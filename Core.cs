using System;
using System.Collections;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using ExileCore;
using ExileCore.PoEMemory;
using ExileCore.PoEMemory.Components;
using ExileCore.PoEMemory.Elements.Village;
using ExileCore.PoEMemory.Models;
using ExileCore.Shared;
using ExileCore.Shared.Helpers;
using ExileCore.Shared.Nodes;
using Microsoft.VisualBasic.Devices;
using Newtonsoft.Json;
using SharpDX;
using NumVector2 = System.Numerics.Vector2;

namespace SellMyShit
{
    // a copy of one picker row, taken while the row was known to show this currency; the
    // picker reuses its row elements when its search filters the list, so a stored element can
    // later show a different currency
    public sealed class OwnedCurrency
    {
        public string Name { get; init; } = string.Empty;
        public int Owned { get; set; }
        public BaseItemType ItemType { get; set; }
    }

    public class Core : BaseSettingsPlugin<Settings>
    {
        private const string WantedCurrencyName = "Chaos Orb";
        private const int SortByName = 0;
        private const int SortByValue = 1;
        private const int SortByOwned = 2;
        private const int SortByEach = 3;

        // the exchange window holds a static 10 offers; selection and queueing both stop there
        private const int MaxTradeOffers = 10;

        private const int ColumnSelect = 0;
        private const int ColumnName = 1;
        private const int ColumnEach = 2;
        private const int ColumnOwned = 3;
        private const int ColumnValue = 4;

        private readonly List<string> _selectedCurrencies = new();
        private readonly List<OwnedCurrency> _bulkSellQueue = new();

        private bool _collectRunning;
        private DateTime _collectStartedUtc;
        private int _collectClicks;
        private readonly HashSet<long> _collectClickedAddresses = new();

        private Func<BaseItemType, double> _getNinjaBaseItemTypeValue;

        private string _filterText = string.Empty;

        private int _inputInProgress;
        private DateTime _hideOverlayUntilUtc = DateTime.MinValue;

        private SellSequenceStep _sellSequenceStep = SellSequenceStep.Idle;
        private DateTime _sellSequenceStepStartedUtc;
        private CurrencyExchangeCurrencyPickerCurrencyOption _pendingSellItem;
        private CurrencyExchangeCurrencyPickerCurrencyOption _pendingWantedItem;
        private MarketRatio _pendingMarketRatio;

        private string _pendingSellItemName = string.Empty;
        private int _pendingSellOwnedAmount;

        private static readonly TimeSpan CurrencyItemsRefreshInterval =
            TimeSpan.FromMilliseconds(500);

        private List<OwnedCurrency>
            _currencyExchangeItemsCache = [];

        private bool _currencyExchangeItemsCacheInitialized;

        private readonly Dictionary<string, OwnedCurrency> _ownedCurrencies =
            new(StringComparer.OrdinalIgnoreCase);
        private DateTime _nextCurrencyItemsRefreshUtc = DateTime.MinValue;
        private int _currencyItemsVersion;

        private readonly List<OwnedCurrency>
            _displayItemsCache = [];

        private int _displayItemsSourceVersion = -1;
        private string _displayItemsFilter = string.Empty;
        private int _displayItemsSortColumn = -1;
        private bool _displayItemsSortAscending;
        private bool _isAltKeyDown = false;
        private Point storedMousePosition;


        private List<string> debugMessages = new List<string>();


        public override bool Initialise()
        {
            // these two came later than the settings file, so an older save can still hold nulls
            if (Settings != null)
            {
                Settings.AttachToExchangeWindow ??= new ToggleNode(true);
                Settings.AttachDirection ??= new TextNode("Left");

                if (Array.IndexOf(AttachDirections, Settings.AttachDirection.Value) < 0)
                    Settings.AttachDirection.Value = "Left";
            }

            return true;
        }

        public override void Render()
        {
            if (!Settings.Enable.Value)
                return;

            try
            {
                var currencyExchangePanel = GetCurrencyExchangePanel();
                if (Settings.Debug)
                {
                    DebugImGuiWindow();

                    // a missing element here used to throw, and the catch below then cancelled the
                    // running sell sequence on every frame
                    try
                    {
                        DrawDebugElementFrames(currencyExchangePanel);
                    }
                    catch (Exception ex)
                    {
                        AddDebugMessage($"Debug overlay: {ex.Message}");
                    }
                }

                if (currencyExchangePanel?.IsVisible != true)
                    return;

                ProcessSellSequence(currencyExchangePanel);

                var ownedItems =
                    GetCurrencyExchangeItems(currencyExchangePanel);

                ProcessBulkQueue(ownedItems);

                ProcessCollectCompleted(currencyExchangePanel);

                if (SellSequenceStep.Idle == _sellSequenceStep) DrawOwnedItemsUi(ownedItems);
            }
            catch (Exception ex)
            {
                LogError($"SellMyShit error: {ex}");
                StopSellSequence();
            }
        }

        private void DrawDebugElementFrames(CurrencyExchangePanel currencyExchangePanel)
        {
            if (currencyExchangePanel?.IsVisible != true)
                return;

            void Mark(Element element)
            {
                if (element == null)
                    return;

                var rect = element.GetClientRect();
                Graphics.DrawFrame(rect.BottomLeft, rect.TopRight, Color.Red, 2);
                Graphics.DrawCircleFilled(rect.Center.ToVector2Num(), 5, Color.Red, 5);
            }

            var currencyPicker = currencyExchangePanel.CurrencyPicker;

            if (currencyPicker?.IsVisible == true)
            {
                Mark(currencyPicker.GetChildAtIndex(
                    Settings.CurrencyPickerSearchInputChildIndex.Value));
                return;
            }

            if (storedMousePosition.X > 0 && storedMousePosition.Y > 0)
                Graphics.DrawCircleFilled(storedMousePosition.ToVector2(), 5, Color.Red, 5);

            Mark(currencyExchangePanel.GetChildAtIndex(Settings.IHaveButtonChildIndex.Value));
            Mark(currencyExchangePanel.GetChildAtIndex(Settings.IWantButtonChildIndex.Value));
            Mark(currencyExchangePanel.OfferedItemCountInput);
            Mark(currencyExchangePanel.WantedItemCountInput);
            Mark(currencyExchangePanel.GetChildAtIndex(Settings.SellButtonChildIndex.Value));
        }

        private CurrencyExchangePanel GetCurrencyExchangePanel()
        {

            return GameController?
                .IngameState?
                .IngameUi?
                .CurrencyExchangePanel;
        }

        private List<OwnedCurrency>
            GetCurrencyExchangeItems(
                CurrencyExchangePanel currencyExchangePanel)
        {
            if (currencyExchangePanel == null)
                return [];

            var now = DateTime.UtcNow;

            if (_currencyExchangeItemsCacheInitialized &&
                now < _nextCurrencyItemsRefreshUtc)
            {
                return _currencyExchangeItemsCache;
            }

            _nextCurrencyItemsRefreshUtc =
                now.Add(CurrencyItemsRefreshInterval);

            try
            {
                var currencyPicker = currencyExchangePanel.CurrencyPicker;
                var options = currencyPicker?.Options;

                if (options == null)
                    return _currencyExchangeItemsCache;

                // the game keeps the last search text in the picker, so after selling e.g. Abyss
                // Thread the picker only lists that; a filtered list may only update the rows it
                // shows, a full rebuild needs an empty search box
                var searchText = currencyPicker
                    .GetChildAtIndex(Settings.CurrencyPickerSearchInputChildIndex.Value)?
                    .GetChildAtIndex(0)?
                    .Text?
                    .Trim();

                var isFiltered =
                    !string.IsNullOrEmpty(searchText) ||
                    _sellSequenceStep != SellSequenceStep.Idle;

                var seen = new Dictionary<string, OwnedCurrency>(
                    StringComparer.OrdinalIgnoreCase);

                foreach (var option in options)
                {
                    if (option?.Children == null || option.Children.Count == 0)
                        continue;

                    var name = GetItemName(option)?.Trim();

                    if (string.IsNullOrEmpty(name) ||
                        LooksLikeAddress(name) ||
                        seen.ContainsKey(name))
                    {
                        continue;
                    }

                    seen[name] = new OwnedCurrency
                    {
                        Name = name,
                        Owned = option.Owned,
                        ItemType = ResolveBaseItemType(option)
                    };
                }

                if (!isFiltered)
                    _ownedCurrencies.Clear();

                foreach (var currency in seen.Values)
                {
                    if (currency.Owned > 0)
                        _ownedCurrencies[currency.Name] = currency;
                    else
                        _ownedCurrencies.Remove(currency.Name);
                }

                _currencyExchangeItemsCache = _ownedCurrencies.Values
                    .Where(currency => !Settings.IsCurrencyExcluded(currency.Name))
                    .ToList();

                _currencyExchangeItemsCacheInitialized = true;
                _currencyItemsVersion++;

                return _currencyExchangeItemsCache;
            }
            catch (Exception ex)
            {
                LogError(
                    $"SellMyShit error while extracting items: {ex}");

                return _currencyExchangeItemsCache;
            }
        }

        private static bool LooksLikeAddress(string name) =>
            name.Length >= 8 && name.All(Uri.IsHexDigit);

        private bool IsSelected(string name) =>
            _selectedCurrencies.Any(selected =>
                string.Equals(selected, name, StringComparison.OrdinalIgnoreCase));

        private void SetSelected(string name, bool selected)
        {
            if (selected)
            {
                if (_selectedCurrencies.Count >= MaxTradeOffers ||
                    IsSelected(name))
                {
                    return;
                }

                _selectedCurrencies.Add(name);
                return;
            }

            _selectedCurrencies.RemoveAll(selectedName =>
                string.Equals(selectedName, name, StringComparison.OrdinalIgnoreCase));
        }

        // every order still on the board takes one of the 10 slots, including completed ones that
        // have not been collected; only cancelled orders free a slot
        private int GetListedOfferCount()
        {
            var orders = GetCurrencyExchangePanel()?.Orders;

            if (orders == null)
                return MaxTradeOffers;

            return orders.Count(order =>
                order != null && !order.IsCanceled);
        }

        private int GetRemainingOfferCapacity() =>
            Math.Max(0, MaxTradeOffers - GetListedOfferCount());

        private void StartBulkSell()
        {
            if (_sellSequenceStep != SellSequenceStep.Idle)
                return;

            var capacity = Math.Min(
                GetRemainingOfferCapacity(),
                MaxTradeOffers);

            if (capacity <= 0)
                return;

            _bulkSellQueue.Clear();

            foreach (var name in _selectedCurrencies)
            {
                if (_bulkSellQueue.Count >= capacity)
                    break;

                // keep the option itself: the picker is empty while no list is open, so a name
                // lookup at start time would fail
                var item = _currencyExchangeItemsCache.FirstOrDefault(option =>
                    string.Equals(
                        GetItemName(option),
                        name,
                        StringComparison.OrdinalIgnoreCase));

                if (item != null)
                    _bulkSellQueue.Add(item);
            }

            _selectedCurrencies.Clear();

            LogMessage(
                $"Bulk: queued {_bulkSellQueue.Count} item(s), " +
                $"{GetListedOfferCount()} already listed.");
        }

        private void ProcessBulkQueue(
            List<OwnedCurrency> ownedItems)
        {
            if (_sellSequenceStep != SellSequenceStep.Idle ||
                _bulkSellQueue.Count == 0)
            {
                return;
            }

            if (GetRemainingOfferCapacity() <= 0)
            {
                LogMessage(
                    $"Bulk: offer slots full ({GetListedOfferCount()}/" +
                    $"{MaxTradeOffers}), stopping with " +
                    $"{_bulkSellQueue.Count} item(s) queued.");

                _bulkSellQueue.Clear();
                return;
            }

            var item = _bulkSellQueue[0];
            _bulkSellQueue.RemoveAt(0);

            // use the latest owned count for this name if the list has one
            var current = ownedItems?.FirstOrDefault(option =>
                string.Equals(
                    option.Name,
                    item.Name,
                    StringComparison.OrdinalIgnoreCase)) ?? item;

            LogMessage(
                $"Bulk: starting {current.Name} " +
                $"({_bulkSellQueue.Count} left).");

            StartSellSequence(current);
        }

        private void StartCollect()
        {
            _collectRunning = true;
            _collectStartedUtc = DateTime.UtcNow;
            _collectClicks = 0;
            _collectClickedAddresses.Clear();

            var panel = GetCurrencyExchangePanel();

            LogMessage(
                "Collect: " +
                $"{panel?.Orders?.Count(order => order != null && order.IsCompleted && !order.IsCanceled) ?? 0} " +
                $"completed of {panel?.Orders?.Count ?? 0} order(s), " +
                $"{panel?.OrderElements?.Count ?? 0} row element(s).");

            var rows = CompletedOrderRows(panel);

            if (rows == null)
                return;

            // keep the press cheap; the tree is dumped on failure from ProcessCollectCompleted
        }

        private void LogRowTree(Element element, int depth)
        {
            if (element == null || depth > 2)
                return;

            var rect = element.GetClientRect();
            var text = element.TextNoTags?.Trim();

            LogMessage(
                $"Collect: {(depth == 0 ? "row" : "child")} " +
                $"d{depth} addr={element.Address} " +
                $"rect={rect.Left},{rect.Top},{rect.Width},{rect.Height} " +
                $"tex='{element.TextureName}' " +
                $"entity='{element.Entity?.Path}' " +
                $"text='{text}'.");

            var children = element.Children;

            if (children == null)
                return;

            foreach (var child in children)
                LogRowTree(child, depth + 1);
        }

        private void ProcessCollectCompleted(CurrencyExchangePanel currencyExchangePanel)
        {
            if (!_collectRunning)
                return;

            if (_sellSequenceStep != SellSequenceStep.Idle ||
                currencyExchangePanel?.IsVisible != true)
            {
                _collectRunning = false;
                return;
            }

            if (IsGameInputBusy())
                return;

            if ((DateTime.UtcNow - _collectStartedUtc).TotalSeconds > 15 ||
                _collectClicks > 60)
            {
                _collectRunning = false;
                return;
            }

            var target = FindNextCollectTarget(
                currencyExchangePanel,
                _collectClickedAddresses);

            if (target == null)
            {
                if (_collectClicks == 0)
                {
                    LogError(
                        "Collect: no item slot found in the completed rows.");

                    var rows = CompletedOrderRows(currencyExchangePanel);

                    if (rows != null)
                    {
                        foreach (var row in rows.Take(2))
                            LogRowTree(row, 0);
                    }
                }

                _collectRunning = false;
                return;
            }

            if (QueueGameCtrlShiftRightClick(target.GetClientRect().Center))
            {
                var rect = target.GetClientRect();

                _collectClickedAddresses.Add(target.Address);
                _collectClicks++;

                LogMessage(
                    $"Collect: ctrl+shift+right-clicked slot " +
                    $"{rect.Left},{rect.Top} {rect.Width}x{rect.Height} " +
                    $"({target.Address}).");
            }
        }

        private static Element FindNextCollectTarget(
            CurrencyExchangePanel currencyExchangePanel,
            HashSet<long> clicked)
        {
            var rows = CompletedOrderRows(currencyExchangePanel);

            if (rows == null)
                return null;

            foreach (var row in rows)
            {
                var item = FindItemElement(row, clicked);

                if (item != null)
                    return item;
            }

            return null;
        }

        private static List<Element> CompletedOrderRows(
            CurrencyExchangePanel currencyExchangePanel)
        {
            var elements = currencyExchangePanel?.OrderElements;

            if (elements == null || elements.Count == 0)
                return null;

            // the order ids do not line up with PlayerOrderId, but every finished row carries an
            // "Order Completed" label; rows without it are still listed and must not be touched
            var rows = elements
                .Where(element => element != null &&
                                  HasCompletedLabel(element) &&
                                  element.GetClientRect().Width > 0)
                .Select(element => (Element)element)
                .ToList();

            return rows.Count > 0 ? rows : null;
        }

        private static bool HasCompletedLabel(Element row, int depth = 0)
        {
            var children = row?.Children;

            if (children == null || depth > 2)
                return false;

            foreach (var child in children)
            {
                var text = child?.TextNoTags;

                if (!string.IsNullOrWhiteSpace(text) &&
                    text.Replace(" ", string.Empty)
                        .Contains("completed", StringComparison.OrdinalIgnoreCase))
                {
                    return true;
                }

                if (HasCompletedLabel(child, depth + 1))
                    return true;
            }

            return false;
        }

        // completed orders draw the two currencies as plain 72x72 icon slots; nothing is attached
        // to them (no Entity, no text), so the slot size is what identifies them
        private static bool IsItemSlot(Element element)
        {
            if (element == null)
                return false;

            var rect = element.GetClientRect();

            return rect.Width >= 60 &&
                   rect.Width <= 100 &&
                   rect.Height >= 60 &&
                   rect.Height <= 100 &&
                   Math.Abs(rect.Width - rect.Height) <= 6;
        }

        private static Element FindItemElement(Element element, HashSet<long> clicked, int depth = 0)
        {
            if (element == null || depth > 3)
                return null;

            if (!clicked.Contains(element.Address) && IsItemSlot(element))
                return element;

            var children = element.Children;

            if (children == null)
                return null;

            foreach (var child in children)
            {
                var found = FindItemElement(child, clicked, depth + 1);

                if (found != null)
                    return found;
            }

            return null;
        }

        private IReadOnlyList<OwnedCurrency>
            GetDisplayItems(
                IReadOnlyList<
                    OwnedCurrency> ownedItems)
        {
            var sortColumn =
                GetConfiguredSortColumn();

            var sortAscending =
                Settings.SortAscending.Value;

            var filter =
                _filterText?.Trim() ?? string.Empty;

            var cacheIsCurrent =
                _displayItemsSourceVersion == _currencyItemsVersion &&
                _displayItemsSortColumn == sortColumn &&
                _displayItemsSortAscending == sortAscending &&
                string.Equals(
                    _displayItemsFilter,
                    filter,
                    StringComparison.Ordinal);

            if (cacheIsCurrent)
                return _displayItemsCache;

            _displayItemsCache.Clear();

            foreach (var item in ownedItems)
            {
                if (item == null)
                    continue;

                if (!string.IsNullOrWhiteSpace(filter) &&
                    GetItemSearchText(item).IndexOf(
                        filter,
                        StringComparison.OrdinalIgnoreCase) < 0)
                {
                    continue;
                }

                _displayItemsCache.Add(item);
            }

            _displayItemsCache.Sort(
                (left, right) =>
                    CompareItems(
                        left,
                        right,
                        sortColumn,
                        sortAscending));

            _displayItemsSourceVersion =
                _currencyItemsVersion;

            _displayItemsFilter =
                filter;

            _displayItemsSortColumn =
                sortColumn;

            _displayItemsSortAscending =
                sortAscending;

            return _displayItemsCache;
        }

        private void DrawOwnedItemsUi(
            List<OwnedCurrency> ownedItems)
        {
            ownedItems ??= [];

            if (DateTime.UtcNow < _hideOverlayUntilUtc)
                return;

            if (Settings.AttachToExchangeWindow.Value &&
                TryGetExchangePanelRect(out var panelRect))
            {
                PrepareAttach(panelRect, ImGui.GetIO().DisplaySize);
            }

            if (!ImGui.Begin(
                    "Owned Currency Items",
                    ImGuiWindowFlags.AlwaysAutoResize))
            {
                ImGui.End();
                return;
            }

            _lastWindowSize = ImGui.GetWindowSize();

            if (Settings.AttachToExchangeWindow.Value &&
                TryGetExchangePanelRect(out panelRect))
            {
                ApplyAttachPosition(panelRect, _lastWindowSize);
            }

            // width of the list itself, not the window: reading the window's content width here
            // makes an auto-resizing window keep whatever width it happened to have last frame
            var available = Settings.AttachToExchangeWindow.Value
                ? _attachedChildWidth
                : Settings.WindowWidth.Value;
            var attached = Settings.AttachToExchangeWindow.Value;
            var style = ImGui.GetStyle();

            var buttonsWidth =
                ImGui.CalcTextSize(attached ? "Detach" : "Attach").X +
                style.FramePadding.X * 2 +
                (attached
                    ? ImGui.CalcTextSize($"Dir: {Settings.AttachDirection.Value}").X +
                      style.FramePadding.X * 2 + style.ItemSpacing.X
                    : 0f);

            // when the window is squeezed the buttons drop to their own row instead of clipping
            var narrow = available - buttonsWidth < 120f;

            ImGui.SetNextItemWidth(
                narrow
                    ? available
                    : Math.Max(120f, available - buttonsWidth - style.ItemSpacing.X));

            DrawFilterControls();

            if (!narrow)
                ImGui.SameLine();

            if (ImGui.SmallButton(attached ? "Detach" : "Attach"))
            {
                Settings.AttachToExchangeWindow.Value = !attached;
            }

            if (attached)
            {
                ImGui.SameLine();

                if (ImGui.SmallButton($"Dir: {Settings.AttachDirection.Value}"))
                {
                    var index = Array.IndexOf(
                        AttachDirections,
                        Settings.AttachDirection.Value);

                    Settings.AttachDirection.Value =
                        AttachDirections[(index + 1) % AttachDirections.Length];
                }
            }

            var filteredItems =
                GetDisplayItems(ownedItems);

            ImGui.Text(
                $"Owned Items: {filteredItems.Count} / {ownedItems.Count}");

            var capacity = GetRemainingOfferCapacity();
            var selectedCount = Math.Min(_selectedCurrencies.Count, capacity);
            var offersText =
                $"offers {GetListedOfferCount()}/{MaxTradeOffers}";

            var controlsWidth =
                ImGui.CalcTextSize($"Sell selected ({selectedCount})").X +
                ImGui.CalcTextSize("Clear").X +
                ImGui.CalcTextSize(offersText).X +
                ImGui.CalcTextSize("Collect").X +
                style.FramePadding.X * 8 +
                style.ItemSpacing.X * 4;

            if (ImGui.GetContentRegionAvail().X >= controlsWidth)
                ImGui.SameLine();

            ImGui.BeginDisabled(_selectedCurrencies.Count == 0 || capacity <= 0);

            if (ImGui.SmallButton($"Sell selected ({selectedCount})"))
                StartBulkSell();

            ImGui.EndDisabled();

            ImGui.SameLine();

            if (ImGui.SmallButton("Clear"))
                _selectedCurrencies.Clear();

            ImGui.SameLine();

            ImGui.TextDisabled(offersText);

            ImGui.SameLine();

            ImGui.BeginDisabled(_collectRunning);

            if (ImGui.SmallButton("Collect"))
                StartCollect();

            ImGui.EndDisabled();

            ImGui.Separator();

            var childSize = new NumVector2(
                Settings.AttachToExchangeWindow.Value
                    ? _attachedChildWidth
                    : Settings.WindowWidth.Value,
                Settings.AttachToExchangeWindow.Value
                    ? _attachedChildHeight
                    : Settings.WindowHeight.Value);

            if (ImGui.BeginChild(
                    "CurrencyOwnedItemsChild",
                    childSize,
                    ImGuiChildFlags.None,
                    ImGuiWindowFlags.None))
            {
                DrawOwnedItemsTable(filteredItems);
            }

            ImGui.EndChild();
            ImGui.End();
        }

        private static readonly string[] AttachDirections =
            ["Right", "Bottom", "Left", "Top"];

        private NumVector2 _lastWindowSize;
        private int _attachedChildWidth = 400;
        private int _attachedChildHeight = 300;

        private bool TryGetExchangePanelRect(out RectangleF rect)
        {
            rect = GetCurrencyExchangePanel()?.GetClientRect() ?? default;
            return rect.Width > 0 && rect.Height > 0;
        }

        // Shrinks the window to the free strip beside the panel, so it can never sit on top of the
        // panel itself: the child gets the smaller content size and the window is capped to the strip.
        private void PrepareAttach(RectangleF panelRect, NumVector2 display)
        {
            const float gap = 10f;
            const float chromeWidth = 24f;   // window padding
            const float chromeHeight = 96f;  // title bar, filter row, count line, separator, padding

            var direction = Settings.AttachDirection.Value;

            var (sideWidth, sideHeight) = direction switch
            {
                "Left" => (panelRect.Left - gap, display.Y),
                "Bottom" => (display.X - panelRect.Left, display.Y - panelRect.Bottom - gap),
                "Top" => (display.X - panelRect.Left, panelRect.Top - gap),
                _ => (display.X - panelRect.Right - gap, display.Y - panelRect.Top),
            };

            var maxWidth = Math.Max(sideWidth, 160f);
            var maxHeight = Math.Max(sideHeight, 140f);

            _attachedChildWidth = Math.Clamp(
                Settings.WindowWidth.Value,
                100,
                (int)Math.Max(maxWidth - chromeWidth, 100f));

            _attachedChildHeight = Math.Clamp(
                Settings.WindowHeight.Value,
                80,
                (int)Math.Max(maxHeight - chromeHeight, 80f));

            ImGui.SetNextWindowSizeConstraints(
                new NumVector2(140, 120),
                new NumVector2(maxWidth, maxHeight));
        }

        private void ApplyAttachPosition(RectangleF panelRect, NumVector2 size)
        {
            const float gap = 10f;

            var x = Settings.AttachDirection.Value switch
            {
                "Left" => panelRect.Left - size.X - gap,
                "Bottom" => panelRect.Left,
                "Top" => panelRect.Left,
                _ => panelRect.Right + gap,
            };

            var y = Settings.AttachDirection.Value switch
            {
                "Left" => panelRect.Top,
                "Bottom" => panelRect.Bottom + gap,
                "Top" => panelRect.Top - size.Y - gap,
                _ => panelRect.Top,
            };

            ImGui.SetWindowPos(
                new NumVector2(Math.Max(x, 0f), Math.Max(y, 0f)),
                ImGuiCond.Always);
        }

        private void DrawFilterControls()
        {
            ImGui.InputText(
                "##Filter",
                ref _filterText,
                256);
        }

        private void HandleSortHeaderClick(int column)
        {
            var configuredColumn =
                GetConfiguredSortColumn();

            if (configuredColumn == column)
            {
                Settings.SortAscending.Value =
                    !Settings.SortAscending.Value;

                return;
            }

            Settings.SortBy.Value =
                GetSortOption(column);

            Settings.SortAscending.Value = true;
        }

        private void DrawSortHeader(
            string label,
            int column)
        {
            var isCurrentColumn =
                GetConfiguredSortColumn() == column;

            var indicator = isCurrentColumn
                ? Settings.SortAscending.Value
                    ? " ^"
                    : " v"
                : string.Empty;

            var buttonLabel =
                $"{label}{indicator}##SortHeader{column}";

            if (ImGui.Button(
                    buttonLabel,
                    new NumVector2(
                        ImGui.GetContentRegionAvail().X,
                        0)))
            {
                HandleSortHeaderClick(column);
            }
        }

        private unsafe void DrawOwnedItemsTable(
            IReadOnlyList<OwnedCurrency> items)
        {
            const ImGuiTableFlags tableFlags =
                ImGuiTableFlags.Borders |
                ImGuiTableFlags.RowBg |
                ImGuiTableFlags.Resizable |
                ImGuiTableFlags.Sortable |
                ImGuiTableFlags.SizingStretchProp |
                ImGuiTableFlags.NoSavedSettings;

            if (!ImGui.BeginTable(
                    "CurrencyOwnedItemsTable",
                    6,
                    tableFlags))
            {
                return;
            }

            ImGui.TableSetupColumn(
                "##select",
                ImGuiTableColumnFlags.WidthFixed |
                ImGuiTableColumnFlags.NoSort,
                26f);

            var defaultSortByColum = Settings.SortBy.Value;


            var nameTableFlags = ImGuiTableColumnFlags.WidthStretch |
                ImGuiTableColumnFlags.PreferSortAscending;
            if (defaultSortByColum == "Name") nameTableFlags |= ImGuiTableColumnFlags.DefaultSort;
            ImGui.TableSetupColumn(
                "Name",
                nameTableFlags,
                3f);

            var eachTableFlags = ImGuiTableColumnFlags.WidthStretch |
                ImGuiTableColumnFlags.PreferSortDescending;
            if (defaultSortByColum == SortOptions.Each) eachTableFlags |= ImGuiTableColumnFlags.DefaultSort;
            ImGui.TableSetupColumn(
                "Each (c)",
                eachTableFlags,
                1.6f);

            var ownedTableFlags = ImGuiTableColumnFlags.WidthStretch |
                ImGuiTableColumnFlags.PreferSortDescending;
            if (defaultSortByColum == "Owned") ownedTableFlags |= ImGuiTableColumnFlags.DefaultSort;
            ImGui.TableSetupColumn(
                "Owned",
                ownedTableFlags,
                1.4f);

            // "Value" in settings has always meant the total for the whole stack
            var valueTableFlags = ImGuiTableColumnFlags.WidthStretch |
                ImGuiTableColumnFlags.PreferSortDescending;
            if (defaultSortByColum == "Value") valueTableFlags |= ImGuiTableColumnFlags.DefaultSort;
            ImGui.TableSetupColumn(
                "Total (c)",
                valueTableFlags,
                1.8f);

            ImGui.TableSetupColumn(
                "Action",
                ImGuiTableColumnFlags.WidthFixed |
                ImGuiTableColumnFlags.NoSort,
                120f);

            // ImGui erzeugt die klickbaren Header und Sortierpfeile.
            ImGui.TableHeadersRow();

            ApplyImGuiTableSorting();

            var clipper = ImGui.ImGuiListClipper();

            try
            {
                clipper.Begin(items.Count);

                while (clipper.Step())
                {
                    for (var index = clipper.DisplayStart;
                         index < clipper.DisplayEnd;
                         index++)
                    {
                        DrawOwnedItemRow(
                            items[index],
                            index);
                    }
                }
            }
            finally
            {
                clipper.Destroy();
            }

            ImGui.EndTable();
        }

        private unsafe void ApplyImGuiTableSorting()
        {
            var sortSpecs =
                ImGui.TableGetSortSpecs();

            if (sortSpecs.IsNull ||
                !sortSpecs.SpecsDirty ||
                sortSpecs.SpecsCount <= 0)
            {
                return;
            }

            var columnSortSpec =
                sortSpecs.Specs;

            Settings.SortBy.Value =
                GetSortOption(columnSortSpec.ColumnIndex);

            Settings.SortAscending.Value =
                columnSortSpec.SortDirection ==
                ImGuiSortDirection.Ascending;

            _displayItemsSourceVersion = -1;

            sortSpecs.SpecsDirty = false;
        }
        private static float GetSortHeaderWidth(string label)
        {
            var textWidth =
                ImGui.CalcTextSize($"{label} v").X;

            var style =
                ImGui.GetStyle();

            return textWidth +
                   style.FramePadding.X * 2 +
                   style.CellPadding.X * 2;
        }

        private void DrawOwnedItemRow(
            OwnedCurrency item,
            int index)
        {
            ImGui.TableNextRow();

            ImGui.TableNextColumn();

            var name = GetItemName(item);
            var selected = IsSelected(name);

            // a plain PushID(index) made row 0's "##select" checkbox share its ID with the
            // "##select" column header, which ImGui also pushes under ID 0
            ImGui.PushID($"row_{index}");

            ImGui.BeginDisabled(
                !selected &&
                _selectedCurrencies.Count >= MaxTradeOffers);

            if (ImGui.Checkbox("##select", ref selected))
                SetSelected(name, selected);

            ImGui.EndDisabled();

            ImGui.PopID();

            ImGui.TableNextColumn();

            ImGui.TextUnformatted(name);

            ImGui.TableNextColumn();

            var unitValue = GetUnitNinjaValue(item);

            ImGui.TextUnformatted(
                unitValue.ToString(
                    unitValue >= 100 ? "0" : "0.##",
                    CultureInfo.InvariantCulture));

            ImGui.TableNextColumn();

            ImGui.TextUnformatted(
                item.Owned.ToString(
                    CultureInfo.InvariantCulture));

            ImGui.TableNextColumn();

            var totalValue =
                GetTotalNinjaValue(item);

            ImGui.TextUnformatted(
                totalValue.ToString(
                    CultureInfo.InvariantCulture));

            ImGui.TableNextColumn();

            if (ImGui.SmallButton($"Sell##{index}"))
                StartSellSequence(item);

            ImGui.SameLine();

            if (ImGui.SmallButton($"Ignore##{index}"))
            {
                Settings.AddExcludedCurrency(name);

                _selectedCurrencies.RemoveAll(selected =>
                    string.Equals(
                        selected,
                        name,
                        StringComparison.OrdinalIgnoreCase));

                _currencyExchangeItemsCacheInitialized = false;

                AddDebugMessage($"Excluded {name}.");
            }
        }

        private int CompareItems(
            OwnedCurrency left,
            OwnedCurrency right,
            int column,
            bool ascending)
        {
            if (left == null && right == null)
                return 0;

            if (left == null)
                return ascending ? -1 : 1;

            if (right == null)
                return ascending ? 1 : -1;

            switch (column)
            {
                case SortByValue:
                    {
                        var leftValue =
                            GetTotalNinjaValue(left);

                        var rightValue =
                            GetTotalNinjaValue(right);

                        return ascending
                            ? leftValue.CompareTo(rightValue)
                            : rightValue.CompareTo(leftValue);
                    }

                case SortByOwned:
                    return ascending
                        ? left.Owned.CompareTo(right.Owned)
                        : right.Owned.CompareTo(left.Owned);

                case SortByEach:
                    {
                        var leftEach = GetUnitNinjaValue(left);
                        var rightEach = GetUnitNinjaValue(right);

                        return ascending
                            ? leftEach.CompareTo(rightEach)
                            : rightEach.CompareTo(leftEach);
                    }

                case SortByName:
                default:
                    {
                        var leftName =
                            GetItemName(left);

                        var rightName =
                            GetItemName(right);

                        return ascending
                            ? string.Compare(
                                leftName,
                                rightName,
                                StringComparison.OrdinalIgnoreCase)
                            : string.Compare(
                                rightName,
                                leftName,
                                StringComparison.OrdinalIgnoreCase);
                    }
            }
        }

        private int GetConfiguredSortColumn()
        {
            return Settings.SortBy.Value switch
            {
                SortOptions.Name => SortByName,
                SortOptions.Owned => SortByOwned,
                SortOptions.Each => SortByEach,
                _ => SortByValue
            };
        }

        private static string GetSortOption(int column)
        {
            return column switch
            {
                ColumnName => SortOptions.Name,
                ColumnOwned => SortOptions.Owned,
                ColumnEach => SortOptions.Each,
                _ => SortOptions.Value
            };
        }

        private void ProcessSellSequence(
            CurrencyExchangePanel currencyExchangePanel)
        {
            if (_sellSequenceStep == SellSequenceStep.Idle)
                return;

            if (currencyExchangePanel == null ||
                !currencyExchangePanel.IsVisible)
            {
                LogError(
                    "Currency exchange panel is no longer visible.");

                StopSellSequence();
                return;
            }

            if (string.IsNullOrEmpty(_pendingSellItemName))
            {
                LogError("No pending sell item.");
                StopSellSequence();
                return;
            }

            if (TimeInCurrentStep() >
                TimeSpan.FromSeconds(
                    Settings.SequenceTimeoutSeconds.Value))
            {
                LogError(
                    $"Sell sequence timed out at step " +
                    $"{_sellSequenceStep}.");

                StopSellSequence();
                return;
            }

            var itemName = _pendingSellItemName;
            var ownedAmount = _pendingSellOwnedAmount;

            var currencyPicker =
                currencyExchangePanel.CurrencyPicker;

            var isCurrencyPickerVisible =
                currencyPicker?.IsVisible == true;

            var offeredItemCountInput =
                currencyExchangePanel.OfferedItemCountInput;

            var wantedItemCountInput =
                currencyExchangePanel.WantedItemCountInput;

            switch (_sellSequenceStep)
            {
                case SellSequenceStep.Start:
                    storedMousePosition = MouseInput.Mouse.GetCursorPosition();
                    AddDebugMessage($"Stored Mouse Position {storedMousePosition}");
                    {
                        SetSellSequenceStep(
                            isCurrencyPickerVisible
                                ? SellSequenceStep
                                    .ClickCurrencyPickerOfferedSearchInput
                                : SellSequenceStep.ClickIHave);

                        break;
                    }

                case SellSequenceStep.ClickIHave:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.WaitForOfferedCurrencyPicker);

                            break;
                        }

                        var iHaveButtonChildIndex =
                            Settings.IHaveButtonChildIndex.Value;

                        if (currencyExchangePanel.Children == null ||
                            currencyExchangePanel.Children.Count <=
                            iHaveButtonChildIndex)
                        {
                            LogError("I Have button was not found.");
                            StopSellSequence();
                            break;
                        }

                        var iHaveButtonPosition =
                            currencyExchangePanel
                                .Children[iHaveButtonChildIndex]
                                .GetClientRect()
                                .Center;

                        // Graphics.DrawCircleFilled(iHaveButtonPosition.ToVector2Num(), 20, Color.Red, 5);

                        if (QueueGameClick(iHaveButtonPosition))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.WaitForOfferedCurrencyPicker);
                        }

                        break;
                    }

                case SellSequenceStep.WaitForOfferedCurrencyPicker:
                    {
                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .ClickCurrencyPickerOfferedSearchInput);
                        }

                        break;
                    }

                case SellSequenceStep
                    .ClickCurrencyPickerOfferedSearchInput:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIHave);

                            break;
                        }

                        var searchInputChildIndex =
                            Settings
                                .CurrencyPickerSearchInputChildIndex
                                .Value;

                        if (currencyPicker.Children == null ||
                            currencyPicker.Children.Count <=
                            searchInputChildIndex)
                        {
                            LogError(
                                "Currency picker search input " +
                                "was not found.");

                            StopSellSequence();
                            break;
                        }

                        var searchInputPosition =
                            currencyPicker
                                .Children[searchInputChildIndex]
                                .GetClientRect()
                                .Center;

                        if (QueueGameClick(searchInputPosition))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .TypeCurrencyPickerOfferedSearchQuery);
                        }

                        break;
                    }

                case SellSequenceStep
                    .TypeCurrencyPickerOfferedSearchQuery:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIHave);

                            break;
                        }

                        if (QueueGameTextReplacement(itemName))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .ValidateOfferedSearchQuery);
                        }

                        break;
                    }

                case SellSequenceStep.ValidateOfferedSearchQuery:
                    {

                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIHave);

                            break;
                        }

                        var searchInputChildIndex =
                               Settings
                                   .CurrencyPickerSearchInputChildIndex
                                   .Value;

                        if (currencyPicker.Children == null ||
                            currencyPicker.Children.Count <=
                            searchInputChildIndex)
                        {
                            LogError(
                                "Currency picker search input " +
                                "was not found.");

                            StopSellSequence();
                            break;
                        }

                        var searchText =
                            currencyPicker
                                .GetChildAtIndex(searchInputChildIndex)?
                                .GetChildAtIndex(0)?
                                .Text?
                                .Trim();

                        if (string.Equals(
                                searchText,
                                itemName?.Trim(),
                                StringComparison.OrdinalIgnoreCase))
                        {
                            SetSellSequenceStep(SellSequenceStep.WaitForCurrencyPickerOfferedSearchResults);
                        }

                        break;
                    }

                case SellSequenceStep
                    .WaitForCurrencyPickerOfferedSearchResults:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIHave);

                            break;
                        }

                        if (TimeInCurrentStep() <
                            TimeSpan.FromMilliseconds(
                                Settings
                                    .CurrencySearchDelayMilliseconds
                                    .Value))
                        {
                            break;
                        }

                        // the element stored when the sale started belongs to the unfiltered
                        // list; after searching, the picker lays its rows out again (and some
                        // currencies, such as threads, sit in a separate section whose positions
                        // are relative to that section), so look the item up afresh by name and
                        // check it against the visible list area on screen
                        var freshItem = FindVisiblePickerOption(
                            currencyPicker.Options,
                            currencyPicker.OptionContainer,
                            itemName);

                        if (freshItem == null)
                        {
                            AddDebugMessage($"Waiting for {itemName} to appear in the search results.");
                            break;
                        }

                        _pendingSellItem = freshItem;

                        SetSellSequenceStep(
                            SellSequenceStep.ClickOwnedItem);

                        break;
                    }

                case SellSequenceStep.ClickOwnedItem:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickOfferedItemInput);

                            break;
                        }

                        if (_pendingSellItem == null)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.WaitForCurrencyPickerOfferedSearchResults);

                            break;
                        }

                        var ownedItemRect =
                            _pendingSellItem.GetClientRect();

                        if (ownedItemRect.Width <= 0 ||
                            ownedItemRect.Height <= 0)
                        {
                            break;
                        }

                        if (QueueGameClick(
                                ownedItemRect.Center))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .WaitForOfferedCurrencyPickerToClose);
                        }

                        break;
                    }

                case SellSequenceStep
                    .WaitForOfferedCurrencyPickerToClose:
                    {
                        if (IsGameInputBusy() ||
                            isCurrencyPickerVisible)
                        {
                            break;
                        }


                        SetSellSequenceStep(SellSequenceStep.CheckIfChaosIsWanted);

                        break;
                    }


                case SellSequenceStep.CheckIfChaosIsWanted:
                    {
                        if (IsGameInputBusy())
                            break;


                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickCurrencyPickerWantedSearchInput);

                            break;
                        }


                        var iWantButtonChildIndex = Settings.IWantButtonChildIndex.Value;

                        if (currencyExchangePanel?.Children == null ||
                            currencyExchangePanel.Children.Count <=
                            iWantButtonChildIndex)
                        {
                            LogError("I Want button not found, aborting...");
                            StopSellSequence();
                            break;
                        }

                        var iWantButton = currencyExchangePanel.GetChildAtIndex(iWantButtonChildIndex);
                        var selectedWantedItemName = iWantButton?.GetChildAtIndex(0)?.Text?.Trim();

                        if (selectedWantedItemName == WantedCurrencyName)
                        {
                            AddDebugMessage($"{WantedCurrencyName} is already selected as wanted currency.");


                            if (Settings.ListPriceBasedOnHighestCompetingTrade)
                            {
                                SetSellSequenceStep(SellSequenceStep.ShowMarketRatioTooltip);
                            }
                            else
                            {
                                SetSellSequenceStep(
                                    SellSequenceStep.WaitForMarketRatio);
                            }

                            break;
                        }

                        SetSellSequenceStep(
                            SellSequenceStep.ClickIWant);

                        break;
                    }

                case SellSequenceStep.ClickIWant:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.WaitForWantedCurrencyPicker);

                            break;
                        }

                        var iWantButtonChildIndex = Settings.IWantButtonChildIndex.Value;

                        if (currencyExchangePanel.Children == null ||
                            currencyExchangePanel.Children.Count <=
                            iWantButtonChildIndex)
                        {
                            LogError("I Want button was not found.");
                            StopSellSequence();
                            break;
                        }

                        var iWantButtonPosition =
                            currencyExchangePanel
                                .GetChildAtIndex(iWantButtonChildIndex)
                                .GetClientRect()
                                .Center;

                        if (QueueGameClick(iWantButtonPosition))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.WaitForWantedCurrencyPicker);
                        }

                        break;
                    }

                case SellSequenceStep.WaitForWantedCurrencyPicker:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickCurrencyPickerWantedSearchInput);
                        }

                        break;
                    }

                case SellSequenceStep.ClickCurrencyPickerWantedSearchInput:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIWant);

                            break;
                        }

                        var searchInputChildIndex = Settings.CurrencyPickerSearchInputChildIndex.Value;

                        if (currencyPicker.Children == null ||
                            currencyPicker.Children.Count <=
                            searchInputChildIndex)
                        {
                            LogError(
                                "Wanted currency picker search input was not found.");

                            StopSellSequence();
                            break;
                        }

                        var searchInputPosition =
                            currencyPicker
                                .GetChildAtIndex(searchInputChildIndex)
                                .GetClientRect()
                                .Center;

                        if (QueueGameClick(searchInputPosition))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.TypeCurrencyPickerWantedSearchQuery);
                        }

                        break;
                    }

                case SellSequenceStep.TypeCurrencyPickerWantedSearchQuery:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIWant);

                            break;
                        }

                        if (QueueGameTextReplacement(WantedCurrencyName))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ValidatedWantedSearchQuery);
                        }

                        break;
                    }

                case SellSequenceStep.ValidatedWantedSearchQuery:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIWant);

                            break;
                        }

                        var searchInputChildIndex = Settings.CurrencyPickerSearchInputChildIndex.Value;

                        if (currencyPicker.Children == null ||
                            currencyPicker.Children.Count <= searchInputChildIndex)
                        {
                            LogError(
                                "Wanted currency picker search input was not found.");

                            StopSellSequence();
                            break;
                        }

                        var searchInput =
                            currencyPicker.GetChildAtIndex(searchInputChildIndex);

                        if (searchInput.Children == null ||
                            searchInput.Children.Count == 0)
                        {
                            break;
                        }

                        var searchText = searchInput.GetChildAtIndex(0).Text?.Trim();

                        if (string.Equals(
                                searchText,
                                WantedCurrencyName,
                                StringComparison.OrdinalIgnoreCase))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .WaitForCurrencyPickerWantedSearchResults);
                        }

                        break;
                    }

                case SellSequenceStep.WaitForCurrencyPickerWantedSearchResults:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (!isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ClickIWant);

                            break;
                        }

                        if (TimeInCurrentStep() <
                            TimeSpan.FromMilliseconds(
                                Settings.CurrencySearchDelayMilliseconds.Value))
                        {
                            break;
                        }


                        _pendingWantedItem = currencyPicker.Options?
                            .FirstOrDefault(option =>
                                option?.Children != null &&
                                option.Children.Any(child =>
                                    string.Equals(
                                        child?.Text?.Trim(),
                                        WantedCurrencyName,
                                        StringComparison.OrdinalIgnoreCase)));

                        if (_pendingWantedItem == null)
                            break;

                        var wantedItemRect = _pendingWantedItem.GetClientRect();

                        if (wantedItemRect.Width <= 0 ||
                            wantedItemRect.Height <= 0)
                        {
                            break;
                        }

                        var optionContainer =
                            currencyPicker.OptionContainer;

                        if (optionContainer != null)
                        {
                            var optionContainerRect =
                                optionContainer.GetClientRect();

                            if (!optionContainerRect.Intersects(wantedItemRect))
                                break;
                        }

                        SetSellSequenceStep(
                            SellSequenceStep.ClickWantedItem);

                        break;
                    }

                case SellSequenceStep.ClickWantedItem:
                    {
                        if (IsGameInputBusy())
                            break;


                        if (_pendingWantedItem == null)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .WaitForCurrencyPickerWantedSearchResults);

                            break;
                        }

                        var wantedItemRect = _pendingWantedItem.GetClientRect();

                        if (wantedItemRect.Width <= 0 ||
                            wantedItemRect.Height <= 0)
                        {
                            break;
                        }

                        if (QueueGameClick(
                                wantedItemRect.Center))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .WaitForWantedCurrencyPickerToClose);
                        }

                        break;
                    }

                case SellSequenceStep.WaitForWantedCurrencyPickerToClose:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (isCurrencyPickerVisible)
                            break;

                        _pendingWantedItem = null;


                        if (Settings.ListPriceBasedOnHighestCompetingTrade)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.ShowMarketRatioTooltip);
                        }
                        else
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.WaitForMarketRatio);
                        }

                        break;
                    }


                case SellSequenceStep.ShowMarketRatioTooltip:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (TimeInCurrentStep() <
                            TimeSpan.FromMilliseconds(
                                Settings
                                    .MarketRatioDelayMilliseconds
                                    .Value))
                        {
                            break;
                        }

                        var apiRatio = GetMarketRatiosFromSearchResults()
                            .FirstOrDefault();

                        if (apiRatio != null)
                        {
                            _pendingMarketRatio = apiRatio;

                            AddDebugMessage(
                                $"Market search API ratio for " +
                                $"{ownedAmount} of {itemName}: " +
                                $"{apiRatio.MarketGetRate}:{apiRatio.MarketGiveRate}");

                            SetSellSequenceStep(
                                SellSequenceStep.ClickOfferedItemInput);

                            break;
                        }

                        AddDebugMessage(
                            $"Showing market ratio tooltip for " +
                            $"{ownedAmount} of {itemName}...");

                        var marketRatioPanelChildIndex = Settings.MarketRatioPanelIndex.Value;
                        var marketRatioPanel = currencyExchangePanel.GetChildAtIndex(marketRatioPanelChildIndex);

                        if (marketRatioPanel.Text.Contains("Retrieving"))
                        {
                            AddDebugMessage("Market ratio panel not loaded yet, retrying...");

                            // a stockless item can leave this on "Retrieving" forever
                            if (TimeInCurrentStep() > TimeSpan.FromSeconds(5))
                            {
                                SkipSellSequence(
                                    "market ratio stayed on Retrieving");
                            }

                            break;
                        }

                        if (QueueGameMove(marketRatioPanel.GetClientRect().Center))
                        {
                            {
                                Thread.Sleep(
                                    Settings.MouseSettleDelayMilliseconds.Value);

                                SetSellSequenceStep(
                                    SellSequenceStep.ShowDetailedMarketRatioTooltip);
                                break;
                            }
                        }

                        break;
                    }

                case SellSequenceStep.ShowDetailedMarketRatioTooltip:
                    {
                        if (IsGameInputBusy())
                            break;

                        AddDebugMessage(
                            $"Showing detailed market ratio tooltip for " +
                            $"{ownedAmount} of {itemName}...");

                        var marketRatioPanelChildIndex = Settings.MarketRatioPanelIndex.Value;
                        var marketRatioPanel = currencyExchangePanel.GetChildAtIndex(marketRatioPanelChildIndex);
                        var marketRatioPanelTooltip = marketRatioPanel?.Tooltip;

                        if (marketRatioPanelTooltip == null)
                        {
                            // no tooltip at all usually means no stock; don't wait for the step
                            // timeout to notice
                            if (TimeInCurrentStep() > TimeSpan.FromSeconds(5))
                            {
                                SkipSellSequence(
                                    "no market ratio tooltip (item has no stock)");
                            }

                            break;
                        }

                        if (!_isAltKeyDown)
                        {
                            KeyboardInput.Keyboard.AltKeyDown();
                            AddDebugMessage($"Pressing Alt to show detailed market ratio info");

                            _isAltKeyDown = true;
                        }

                        SetSellSequenceStep(
                            SellSequenceStep.WaitForDetailedMarketRatioInfo);
                        break;
                    }

                case SellSequenceStep.WaitForDetailedMarketRatioInfo:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (TimeInCurrentStep() <
                            TimeSpan.FromMilliseconds(
                                Settings.MarketRatioDelayMilliseconds.Value))
                        {
                            break;
                        }

                        AddDebugMessage(
                            $"Waiting for detailed market ratio info for " +
                            $"{ownedAmount} of {itemName}...");

                        var marketRatioPanelChildIndex = Settings.MarketRatioPanelIndex.Value;
                        var marketRatioPanel = currencyExchangePanel.GetChildAtIndex(marketRatioPanelChildIndex);
                        var marketRatioPanelTooltip = marketRatioPanel?.Tooltip;


                        if (marketRatioPanelTooltip == null ||
                            !marketRatioPanelTooltip.Children.Any(child => child.Text == "Competing Trades"))
                        {
                            // no competing trades appears when the item has no stock; do not sit
                            // here until the whole sequence times out
                            if (TimeInCurrentStep() > TimeSpan.FromSeconds(5))
                            {
                                SkipSellSequence(
                                    "no competing trades (item has no stock)");
                            }

                            break;
                        }

                        AddDebugMessage("Found competing trades window...");


                        _pendingMarketRatio = GetMarketRatioForPendingExchange(currencyExchangePanel);

                        if (_pendingMarketRatio == null)
                        {
                            AddDebugMessage("Competing trade for pending item not found...");
                            break;
                        }

                        if (_isAltKeyDown)
                        {
                            KeyboardInput.Keyboard.AltKeyUp();
                            _isAltKeyDown = false;
                        }

                        if (_pendingMarketRatio == null || _pendingMarketRatio.MarketGetRate <= 0 || _pendingMarketRatio.MarketGiveRate <= 0)
                        {
                            SkipSellSequence(
                                "no usable market ratio for this item");
                        }

                        AddDebugMessage(
                            $"Market ratio for {ownedAmount} of {itemName}: " +
                            $"{_pendingMarketRatio.MarketGetRate}:{_pendingMarketRatio.MarketGiveRate}");

                        SetSellSequenceStep(
                            SellSequenceStep.ClickOfferedItemInput);
                        break;
                    }

                case SellSequenceStep.WaitForMarketRatio:
                    {

                        if (IsGameInputBusy())
                            break;

                        if (TimeInCurrentStep() <
                            TimeSpan.FromMilliseconds(
                                Settings
                                    .MarketRatioDelayMilliseconds
                                    .Value))
                        {
                            break;
                        }

                        var marketRatio = GetMarketRatioForPendingExchange(currencyExchangePanel);

                        var marketRateGive = currencyExchangePanel.MarketRateGive;

                        if (marketRatio == null ||
                            marketRatio.MarketGetRate <= 0 ||
                            marketRatio.MarketGiveRate <= 0)
                        {
                            var ratioPanel = currencyExchangePanel.GetChildAtIndex(
                                Settings.MarketRatioPanelIndex.Value);

                            if (ratioPanel?.Text?.Contains("Retrieving") == true)
                                break; // still loading; the step timeout guards this

                            SkipSellSequence(
                                "no usable market ratio for this item");
                        }

                        AddDebugMessage(
                            $"Market ratio for {ownedAmount} of {itemName}: " +
                            $"{marketRatio.MarketGetRate}:{marketRatio.MarketGiveRate}");

                        _pendingMarketRatio = marketRatio;


                        SetSellSequenceStep(
                            SellSequenceStep.ClickOfferedItemInput);

                        break;
                    }

                case SellSequenceStep.ClickOfferedItemInput:
                    {
                        if (IsGameInputBusy())
                            break;


                        if (offeredItemCountInput == null)
                        {
                            LogError(
                                "Offered item count input was not found.");

                            StopSellSequence();
                            break;
                        }

                        var offeredInputPosition = offeredItemCountInput.GetClientRect().Center;

                        if (QueueGameClick(offeredInputPosition))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .TypeOfferedItemValue);
                        }

                        break;
                    }

                case SellSequenceStep.TypeOfferedItemValue:
                    {
                        if (IsGameInputBusy())
                            break;

                        var offeredValue =
                            ownedAmount.ToString(
                                CultureInfo.InvariantCulture);

                        if (QueueGameTextReplacement(offeredValue))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .ClickWantedItemInput);
                        }

                        break;
                    }



                case SellSequenceStep.ClickWantedItemInput:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.Start);

                            break;
                        }

                        if (wantedItemCountInput == null)
                        {
                            LogError(
                                "Wanted item count input was not found.");

                            StopSellSequence();
                            break;
                        }

                        var wantedInputPosition =
                            wantedItemCountInput
                                .GetClientRect()
                                .Center;

                        if (QueueGameClick(wantedInputPosition))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep
                                    .TypeWantedItemValue);
                        }

                        break;
                    }

                case SellSequenceStep.TypeWantedItemValue:
                    {
                        if (IsGameInputBusy())
                            break;


                        AddDebugMessage(
                            $"Calculating wanted value for " +
                            $"{ownedAmount} of {itemName}...");

                        AddDebugMessage(
                            $"Market ratio: " +
                            $"{_pendingMarketRatio.MarketGetRate}:{_pendingMarketRatio.MarketGiveRate}");

                        var wantedValue =
                            CalculateWantedAmount(
                                ownedAmount,
                                _pendingMarketRatio.MarketGetRate,
                                _pendingMarketRatio.MarketGiveRate,
                                Settings.ListingPricePercent.Value);

                        if (wantedValue <= 0)
                        {
                            LogError(
                                $"Invalid market ratio: " +
                                $"{_pendingMarketRatio.MarketGetRate}:{_pendingMarketRatio.MarketGiveRate}");

                            StopSellSequence();
                            break;
                        }

                        AddDebugMessage(
                            $"Pricing {ownedAmount} {itemName}: " +
                            $"market={_pendingMarketRatio.MarketGetRate}:{_pendingMarketRatio.MarketGiveRate}, " +
                            $"wanted={wantedValue}");

                        if (QueueGameTextReplacement(
                                wantedValue.ToString(
                                    CultureInfo.InvariantCulture)))
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.BlurInput);
                        }

                        break;
                    }

                case SellSequenceStep.BlurInput:
                    {
                        if (IsGameInputBusy())
                            break;

                        var villageGold = currencyExchangePanel.GetChildAtIndex(15);
                        var villageGoldPosition = villageGold.GetClientRect().Center;

                        if (QueueGameClick(villageGoldPosition))
                        {
                            AddDebugMessage($"Blurring input to lock in ratio... ");

                            SetSellSequenceStep(
                                SellSequenceStep.CheckIfSellButtonIsActive);
                        }

                        break;
                    }

                case SellSequenceStep.CheckIfSellButtonIsActive:
                    {
                        if (IsGameInputBusy())
                            break;


                        var sellButtonChildIndex =
                            Settings.SellButtonChildIndex.Value;

                        if (currencyExchangePanel.Children == null ||
                            currencyExchangePanel.Children.Count <=
                            sellButtonChildIndex)
                        {
                            LogError("Sell button was not found.");
                            StopSellSequence();
                            break;
                        }

                        var sellButton = currencyExchangePanel.GetChildAtIndex(sellButtonChildIndex);

                        if (sellButton.IsActive)
                        {
                            SetSellSequenceStep(SellSequenceStep.ClickSellButton);
                        }

                        break;
                    }

                case SellSequenceStep.ClickSellButton:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.Start);

                            break;
                        }

                        var sellButtonChildIndex =
                            Settings.SellButtonChildIndex.Value;

                        if (currencyExchangePanel.Children == null ||
                            currencyExchangePanel.Children.Count <=
                            sellButtonChildIndex)
                        {
                            LogError("Sell button was not found.");
                            StopSellSequence();
                            break;
                        }

                        var sellButtonPosition =
                            currencyExchangePanel
                                .Children[sellButtonChildIndex]
                                .GetClientRect()
                                .Center;

                        if (Settings.TestRun)
                        {
                            SetSellSequenceStep(SellSequenceStep.End);
                            break;
                        }
                        if (QueueGameClick(sellButtonPosition))
                        {
                            AddDebugMessage(
                                $"Sell sequence completed for " +
                                $"{ownedAmount} of {itemName}.");

                            SetSellSequenceStep(
                                SellSequenceStep.CheckUnfavorableTrade);
                        }

                        break;
                    }

                case SellSequenceStep.CheckUnfavorableTrade:
                    {
                        //Check unfavorable trade window here...

                        SetSellSequenceStep(
                            SellSequenceStep.ReopenIHave);

                        break;
                    }

                case SellSequenceStep.ReopenIHave:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (isCurrencyPickerVisible)
                        {
                            SetSellSequenceStep(
                                SellSequenceStep.WaitForOfferedCurrencyPicker);

                            break;
                        }

                        var iHaveButtonChildIndex =
                            Settings.IHaveButtonChildIndex.Value;

                        if (currencyExchangePanel.Children == null ||
                            currencyExchangePanel.Children.Count <=
                            iHaveButtonChildIndex)
                        {
                            LogError("I Have button was not found.");
                            StopSellSequence();
                            break;
                        }

                        var iHaveButtonPosition =
                            currencyExchangePanel
                                .Children[iHaveButtonChildIndex]
                                .GetClientRect()
                                .Center;

                        if (QueueGameClick(iHaveButtonPosition))
                            SetSellSequenceStep(SellSequenceStep.End);

                        break;
                    }
                case SellSequenceStep.End:
                    {
                        if (IsGameInputBusy())
                            break;

                        if (Settings.RestoreMousePosition && storedMousePosition.X > 0)
                        {
                            var windowLocation =
                                GameController.Window
                                    .GetWindowRectangle()
                                    .TopLeft;

                            QueueGameMove(
                                new Vector2(
                                    storedMousePosition.X - windowLocation.X,
                                    storedMousePosition.Y - windowLocation.Y));

                            storedMousePosition = new Point();
                        }
                        StopSellSequence();
                        break;
                    }
            }
        }

        private void StartSellSequence(
            OwnedCurrency item)
        {
            if (item == null)
                return;



            if (_sellSequenceStep != SellSequenceStep.Idle)
            {
                AddDebugMessage("A sell sequence is already running.");
                return;
            }

            if (!GameController.Window.IsForeground())
            {
                var focused =
                    WinApi.SetForegroundWindow(
                        GameController.Window.Process.MainWindowHandle);
                AddDebugMessage($"Focused PoE: {focused}");
            }

            // the picker row is looked up by name once the search results are showing
            _pendingSellItem = null;
            _pendingSellItemName = item.Name;
            _pendingSellOwnedAmount = item.Owned;

            AddDebugMessage(
                $"Started sell sequence for {_pendingSellItemName}, " +
                $"owned amount: {_pendingSellOwnedAmount}.");

            SetSellSequenceStep(SellSequenceStep.Start);
        }

        private static string GetItemName(
            CurrencyExchangeCurrencyPickerCurrencyOption item)
        {
            return item?
                       .Children?
                       .FirstOrDefault()?
                       .Text
                   ?? item?.ToString()
                   ?? "Unknown";
        }

        private static string GetItemName(OwnedCurrency item) =>
            item?.Name ?? "Unknown";

        private static string GetItemSearchText(OwnedCurrency item) =>
            item?.Name ?? string.Empty;

        private static string GetItemSearchText(
            CurrencyExchangeCurrencyPickerCurrencyOption item)
        {
            return item?
                       .Children?
                       .FirstOrDefault()?
                       .Text
                   ?? item?.ToString()
                   ?? string.Empty;
        }

        private void SetSellSequenceStep(
            SellSequenceStep step)
        {
            _sellSequenceStep = step;
            _sellSequenceStepStartedUtc = DateTime.UtcNow;

            AddDebugMessage(
                $"Sell sequence step: {step}");
        }

        private void SkipSellSequence(string reason)
        {
            LogError(
                $"SellMyShit: skipping {_pendingSellItemName}: {reason}.");

            if (_bulkSellQueue.Count > 0)
                LogMessage($"Bulk: {_bulkSellQueue.Count} item(s) left in the queue.");

            StopSellSequence();
        }

        private void StopSellSequence()
        {
            _sellSequenceStep = SellSequenceStep.Idle;

            // the picker only fills its owned counts when it opens, so drop the cached list and
            // let the next frame read the current one
            _currencyExchangeItemsCacheInitialized = false;

            _pendingSellItem = null;
            _pendingWantedItem = null;

            _pendingSellItemName = string.Empty;
            _pendingSellOwnedAmount = 0;
            _pendingMarketRatio = null;

            if (_isAltKeyDown) KeyboardInput.Keyboard.AltKeyUp();

            _isAltKeyDown = false;

        }

        private TimeSpan TimeInCurrentStep()
        {
            return DateTime.UtcNow -
                   _sellSequenceStepStartedUtc;
        }

        private bool IsGameInputBusy()
        {
            return Volatile.Read(
                ref _inputInProgress) != 0;
        }

        private bool QueueGameTextReplacement(
            string text)
        {
            if (text == null)
                return false;

            var overlayHideMilliseconds =
                Settings.TextOverlayHideMilliseconds.Value;

            var releaseDelayMilliseconds =
                Settings.TextReleaseDelayMilliseconds.Value;

            var preFocusDelayMilliseconds =
                Settings.TextPreFocusDelayMilliseconds.Value;

            var postFocusDelayMilliseconds =
                Settings.TextPostFocusDelayMilliseconds.Value;

            return QueueGameInput(
                overlayHideMilliseconds,
                releaseDelayMilliseconds,
                "Game keyboard input failed",
                gameWindowHandle =>
                {
                    Thread.Sleep(
                        preFocusDelayMilliseconds);




                    Thread.Sleep(
                        postFocusDelayMilliseconds);

                    var typed =
                        KeyboardInput.Keyboard
                            .ReplaceText(text);

                    AddDebugMessage(
                        $"Replaced input text with " +
                        $"\"{text}\": {typed}");
                });
        }

        private bool QueueGameClick(
            Vector2 screenPosition)
        {
            // element rects are relative to the game window; the cursor needs screen coordinates
            var targetPosition = ToScreenPosition(screenPosition);

            var overlayHideMilliseconds =
                Settings.ClickOverlayHideMilliseconds.Value;

            var releaseDelayMilliseconds =
                Settings.ClickReleaseDelayMilliseconds.Value;

            var preFocusDelayMilliseconds =
                Settings.ClickPreFocusDelayMilliseconds.Value;

            var postFocusDelayMilliseconds =
                Settings.ClickPostFocusDelayMilliseconds.Value;

            var mouseSettleDelayMilliseconds =
                Settings.MouseSettleDelayMilliseconds.Value;

            return QueueGameInput(
                overlayHideMilliseconds,
                releaseDelayMilliseconds,
                "Game click failed",
                gameWindowHandle =>
                {
                    Thread.Sleep(preFocusDelayMilliseconds);
                    Thread.Sleep(postFocusDelayMilliseconds);

                    MoveCursorTo(targetPosition);
                    Thread.Sleep(mouseSettleDelayMilliseconds);
                    ClickMouse(MouseButtons.Left);
                });
        }

        private bool QueueGameCtrlShiftRightClick(
            Vector2 screenPosition)
        {
            // element rects are relative to the game window; the cursor needs screen coordinates
            var targetPosition = ToScreenPosition(screenPosition);

            var overlayHideMilliseconds =
                Settings.ClickOverlayHideMilliseconds.Value;

            var releaseDelayMilliseconds =
                Settings.ClickReleaseDelayMilliseconds.Value;

            var preFocusDelayMilliseconds =
                Settings.ClickPreFocusDelayMilliseconds.Value;

            var postFocusDelayMilliseconds =
                Settings.ClickPostFocusDelayMilliseconds.Value;

            var mouseSettleDelayMilliseconds =
                Settings.MouseSettleDelayMilliseconds.Value;

            return QueueGameInput(
                overlayHideMilliseconds,
                releaseDelayMilliseconds,
                "Game ctrl+shift right click failed",
                gameWindowHandle =>
                {
                    Thread.Sleep(preFocusDelayMilliseconds);
                    Thread.Sleep(postFocusDelayMilliseconds);

                    Input.KeyDown(Keys.LControlKey);
                    Input.KeyDown(Keys.LShiftKey);

                    try
                    {
                        MoveCursorTo(targetPosition);
                        Thread.Sleep(mouseSettleDelayMilliseconds);
                        ClickMouse(MouseButtons.Right);
                    }
                    finally
                    {
                        Input.KeyUp(Keys.LShiftKey);
                        Input.KeyUp(Keys.LControlKey);
                    }
                });
        }

        // the option with this name that is drawn and can be clicked inside the list area
        private static CurrencyExchangeCurrencyPickerCurrencyOption FindVisiblePickerOption(
            IEnumerable<CurrencyExchangeCurrencyPickerCurrencyOption> options,
            Element optionContainer,
            string name)
        {
            if (options == null || string.IsNullOrWhiteSpace(name))
                return null;

            var listRect = optionContainer?.GetClientRect();

            return options
                .Where(option =>
                    option != null &&
                    option.IsVisible &&
                    string.Equals(
                        GetItemName(option)?.Trim(),
                        name.Trim(),
                        StringComparison.OrdinalIgnoreCase))
                .Where(option =>
                {
                    var rect = option.GetClientRect();

                    if (rect.Width <= 0 || rect.Height <= 0)
                        return false;

                    return listRect == null ||
                           listRect.Value.Width <= 0 ||
                           listRect.Value.Contains(rect.Center);
                })
                .OrderByDescending(option => option.Owned)
                .FirstOrDefault();
        }

        private Vector2 ToScreenPosition(Vector2 windowPosition)
        {
            var window = GameController?.Window;

            if (window == null)
                return windowPosition;

            return windowPosition + window.GetWindowRectangle().TopLeft;
        }

        // moves with Win32 directly and reports where the cursor actually ended up, so a blocked
        // move (e.g. the game running as admin while ExileApi is not) shows in the debug window
        private void MoveCursorTo(Vector2 target)
        {
            var moved = MouseInput.Mouse.MoveMouse(target);
            var actual = MouseInput.Mouse.GetCursorPosition();

            AddDebugMessage(
                $"Move cursor to ({target.X:0},{target.Y:0}): " +
                $"{(moved ? "ok" : "FAILED")}, cursor now ({actual.X},{actual.Y})");

            if (!moved ||
                Math.Abs(actual.X - target.X) > 2 ||
                Math.Abs(actual.Y - target.Y) > 2)
            {
                // fall back to ExileApi's own input
                Input.SetCursorPos(target);
            }
        }

        private void ClickMouse(MouseButtons button)
        {
            var hold = Settings.MouseButtonHoldMilliseconds.Value;

            var sent = button == MouseButtons.Right
                ? MouseInput.Mouse.RightClick(hold)
                : MouseInput.Mouse.LeftClick(hold);

            AddDebugMessage($"{button} click: {(sent ? "sent" : "BLOCKED by Windows")}");
        }

        private static void RunHumanizedInput(IEnumerator enumerator)
        {
            if (enumerator == null)
                return;

            var guard = 0;

            while (enumerator.MoveNext() && guard++ < 5000)
                Thread.Sleep(1);
        }

        private bool QueueGameMove(
            Vector2 screenPosition)
        {
            // element rects are relative to the game window; the cursor needs screen coordinates
            var targetPosition = ToScreenPosition(screenPosition);

            var overlayHideMilliseconds =
                Settings.ClickOverlayHideMilliseconds.Value;

            var releaseDelayMilliseconds =
                Settings.ClickReleaseDelayMilliseconds.Value;

            var preFocusDelayMilliseconds =
                Settings.ClickPreFocusDelayMilliseconds.Value;

            var postFocusDelayMilliseconds =
                Settings.ClickPostFocusDelayMilliseconds.Value;

            return QueueGameInput(
                overlayHideMilliseconds,
                releaseDelayMilliseconds,
                "Game click failed",
                gameWindowHandle =>
                {
                    Thread.Sleep(preFocusDelayMilliseconds);
                    Thread.Sleep(postFocusDelayMilliseconds);

                    MoveCursorTo(targetPosition);
                });
        }

        private bool QueueGameInput(
            int overlayHideMilliseconds,
            int releaseDelayMilliseconds,
            string errorMessage,
            Action<IntPtr> inputAction)
        {
            if (Interlocked.CompareExchange(
                    ref _inputInProgress,
                    1,
                    0) != 0)
            {
                return false;
            }

            var gameWindowHandle =
                GameController?
                    .Window?
                    .Process?
                    .MainWindowHandle
                ?? IntPtr.Zero;

            if (gameWindowHandle == IntPtr.Zero)
            {
                Interlocked.Exchange(
                    ref _inputInProgress,
                    0);

                LogError(
                    "Path of Exile window handle is unavailable.");

                return false;
            }

            _hideOverlayUntilUtc =
                DateTime.UtcNow.AddMilliseconds(
                    overlayHideMilliseconds);

            _ = Task.Run(() =>
            {
                try
                {
                    inputAction(gameWindowHandle);
                }
                catch (Exception ex)
                {
                    LogError(
                        $"{errorMessage}: {ex}");

                    AddDebugMessage($"{errorMessage}: {ex.Message}");
                }
                finally
                {
                    Thread.Sleep(
                        releaseDelayMilliseconds);

                    Interlocked.Exchange(
                        ref _inputInProgress,
                        0);
                }
            });

            return true;
        }

        private static int CalculateWantedAmount(
            int offeredAmount,
            float marketRateGet,
            float marketRateGive,
            int listingPricePercent)
        {
            if (offeredAmount <= 0 ||
                marketRateGet <= 0 ||
                marketRateGive <= 0 ||
                listingPricePercent <= 0)
            {
                return 0;
            }

            var priceMultiplier =
                listingPricePercent / 100d;

            var exactWantedAmount =
                offeredAmount *
                (marketRateGet * priceMultiplier) /
                marketRateGive;

            return Math.Max(
                1,
                (int)Math.Floor(exactWantedAmount));
        }

        private bool TryGetNinjaValue(
            OwnedCurrency option,
            out double chaosValue)
        {
            chaosValue = 0;

            var itemType = option?.ItemType;

            _getNinjaBaseItemTypeValue ??=
                GameController.PluginBridge
                    .GetMethod<Func<BaseItemType, double>>(
                        "NinjaPrice.GetBaseItemTypeValue");

            if (_getNinjaBaseItemTypeValue == null)
            {
                if (!_ninjaBridgeWarningLogged)
                {
                    _ninjaBridgeWarningLogged = true;
                    LogError(
                        "NinjaPrice.GetBaseItemTypeValue is unavailable; " +
                        "currency values will show as 0.");
                }

                return false;
            }

            if (itemType == null)
            {
                // one line per name, so a currency the game files cannot resolve stays visible
                // instead of turning into a silent 0
                var name = GetItemName(option);

                if (_unresolvedCurrencyNames.Add(name))
                {
                    LogError(
                        $"No BaseItemType found for currency '{name}'; " +
                        "its value will show as 0.");
                }

                return false;
            }

            try
            {
                chaosValue =
                    _getNinjaBaseItemTypeValue(itemType);

                return true;
            }
            catch (Exception ex)
            {
                LogError(
                    $"Failed to retrieve Ninja Price for " +
                    $"{GetItemName(option)}: {ex}");

                return false;
            }
        }

        private readonly HashSet<string> _unresolvedCurrencyNames =
            new(StringComparer.OrdinalIgnoreCase);

        private bool _ninjaBridgeWarningLogged;

        private Dictionary<string, BaseItemType> _baseItemTypesByName;
        private int _baseItemTypesSourceCount = -1;

        // This ExileCore hands the currency picker options over without a BaseItemType, so look the
        // type up by the name the picker shows. The map is built once (a few thousand entries) and
        // rebuilt if the game files reload with a different size.
        private BaseItemType ResolveBaseItemType(
            CurrencyExchangeCurrencyPickerCurrencyOption option)
        {
            var itemType = option?.ItemType;

            if (!string.IsNullOrEmpty(itemType?.BaseName))
                return itemType;

            var types =
                GameController?
                    .Files?
                    .BaseItemTypes?
                    .Contents;

            if (types == null || types.Count == 0)
                return itemType;

            if (_baseItemTypesByName == null ||
                _baseItemTypesSourceCount != types.Count)
            {
                var byName =
                    new Dictionary<string, BaseItemType>(
                        StringComparer.OrdinalIgnoreCase);

                foreach (var candidate in types.Values)
                {
                    if (string.IsNullOrEmpty(candidate?.BaseName))
                        continue;

                    // a name can exist in more than one class; the picker lists currencies, so
                    // never let a non-currency entry replace one
                    if (!byName.TryGetValue(candidate.BaseName, out var existing) ||
                        existing.ClassName != "StackableCurrency")
                    {
                        byName[candidate.BaseName] = candidate;
                    }
                }

                _baseItemTypesByName = byName;
                _baseItemTypesSourceCount = types.Count;
            }

            return _baseItemTypesByName.GetValueOrDefault(GetItemName(option))
                   ?? itemType;
        }

        private double GetUnitNinjaValue(OwnedCurrency item) =>
            item != null && TryGetNinjaValue(item, out var unitValue)
                ? unitValue
                : 0;

        private double GetTotalNinjaValue(
            OwnedCurrency item)
        {
            if (item == null)
                return 0;

            return TryGetNinjaValue(
                item,
                out var unitValue)
                ? Math.Floor(unitValue * item.Owned)
                : 0;
        }

        private MarketRatio GetMarketRatioForPendingExchange(CurrencyExchangePanel currencyExchangePanel, int neededAmount = 100)
        {
            if (currencyExchangePanel == null)
            {
                return null;
            }

            if (Settings.ListPriceBasedOnHighestCompetingTrade)
            {
                var apiRatios = GetMarketRatiosFromSearchResults();

                if (apiRatios.Count > 0)
                {
                    AddDebugMessage(
                        $"Market search API returned {apiRatios.Count} competing ratios.");

                    return apiRatios.First();
                }

                AddDebugMessage(
                    "Market search API returned no listings, falling back to the ratio tooltip.");

                var marketRatioPanelChildIndex = Settings.MarketRatioPanelIndex.Value;
                var marketRatioPanel = currencyExchangePanel.GetChildAtIndex(marketRatioPanelChildIndex);
                var marketRatioPanelTooltip = marketRatioPanel?.Tooltip;

                var allMarketRatioLinesGroupedByHeight = marketRatioPanelTooltip?.Children?
                    .GroupBy(child => child.Y)
                    .Select(group => group
                        .Select(child => child.TextNoTags)
                        .ToList())
                    .ToList();

                // AddDebugMessage($"Json Formated competing trade lines: {JsonConvert.SerializeObject(allMarketRatioLinesGroupedByHeight, Formatting.Indented)}");

                var availableMarketRatios = new List<MarketRatio>();
                foreach (var marketRatioLine in allMarketRatioLinesGroupedByHeight)
                {
                    var ratioParts = marketRatioLine[0].Split(" : ");

                    var marketRatio = new MarketRatio
                    {
                        MarketGetRate = float.TryParse(
                            ratioParts.FirstOrDefault()?.Replace(">", "").Replace("<", "").Trim(),
                            NumberStyles.Float,
                            CultureInfo.InvariantCulture,
                            out float giveRate)
                                ? giveRate
                                : 0,

                        MarketGiveRate = float.TryParse(
                            ratioParts.LastOrDefault()?.Replace(">", "").Replace("<", "").Trim(),
                            NumberStyles.Float,
                            CultureInfo.InvariantCulture,
                            out float getRate)
                                ? getRate
                                : 0,
                    };

                    if (marketRatio.MarketGetRate <= 0 || marketRatio.MarketGiveRate <= 0)
                    {
                        CustomDebugImGuiWindow($"Skipping market ratio line due to invalid rates: {marketRatioLine[0]}");
                        continue;
                    }

                    marketRatio.AvailableTrades = int.TryParse(marketRatioLine[1].Replace(".", ""), out int trades) ? trades : 0;

                    CustomDebugImGuiWindow($"Found market ratio: {marketRatio.MarketGetRate}:{marketRatio.MarketGiveRate} with {marketRatio.AvailableTrades} available trades.");


                    if (marketRatio.MarketGetRate > 0 && marketRatio.MarketGiveRate > 0 && marketRatio.AvailableTrades > 0)
                    {
                        availableMarketRatios.Add(marketRatio);
                    }
                }

                availableMarketRatios = availableMarketRatios.OrderByDescending(ratio => ratio.MarketGetRate).ToList();

                if (Settings.OnlyPickRatiosWithSufficientStock)
                {
                    availableMarketRatios = availableMarketRatios.Where(ratio => ratio.AvailableTrades >= neededAmount).ToList();
                }

                AddDebugMessage($"Json Formated Ratios: {JsonConvert.SerializeObject(availableMarketRatios, Formatting.Indented)}");

                return availableMarketRatios.FirstOrDefault();
            }
            else
            {
                return new MarketRatio
                {
                    MarketGetRate = currencyExchangePanel.MarketRateGet,
                    MarketGiveRate = currencyExchangePanel.MarketRateGive,
                    AvailableTrades = 0 // Not available in this mode
                };
            }
        }

        private List<MarketRatio> GetMarketRatiosFromSearchResults()
        {
            var ratios = new List<MarketRatio>();

            var results =
                GameController?
                    .IngameState?
                    .IngameUi?
                    .MarketSearchResultsPanel?
                    .Results;

            if (results == null || results.Count == 0)
                return ratios;

            var offeredName = _pendingSellItemName?.Trim();

            foreach (var result in results)
            {
                if (result == null)
                    continue;

                var price = result.PriceAmount;

                if (price <= 0)
                    continue;

                var currency = result.PriceCurrencyString?.Trim();

                float getRate;
                float giveRate;

                if (string.Equals(currency, WantedCurrencyName, StringComparison.OrdinalIgnoreCase))
                {
                    getRate = price;
                    giveRate = 1;
                }
                else if (!string.IsNullOrEmpty(offeredName) &&
                         string.Equals(currency, offeredName, StringComparison.OrdinalIgnoreCase))
                {
                    getRate = 1;
                    giveRate = price;
                }
                else
                {
                    continue;
                }

                var existing = ratios.FirstOrDefault(ratio =>
                    ratio.MarketGetRate == getRate &&
                    ratio.MarketGiveRate == giveRate);

                if (existing != null)
                {
                    existing.AvailableTrades++;
                }
                else
                {
                    ratios.Add(new MarketRatio
                    {
                        MarketGetRate = getRate,
                        MarketGiveRate = giveRate,
                        AvailableTrades = 1,
                    });
                }
            }

            return ratios
                .OrderByDescending(ratio =>
                    ratio.MarketGetRate / ratio.MarketGiveRate)
                .ToList();
        }

        private void MyLogMessage(string message)
        {
            if (Settings.Debug)
            {
                LogMessage(message);
            }
        }

        private void DebugImGuiWindow()
        {
            try
            {
                if (!Settings.Debug)
                    return;

                ImGui.Separator();

                ImGui.Text($"Sell sequence step: {_sellSequenceStep}");
                ImGui.Text($"Pending sell item: {_pendingSellItemName}");
                ImGui.Text($"Pending sell owned amount: {_pendingSellOwnedAmount}");
                ImGui.Text($"Pending wanted item: {_pendingWantedItem?.Text}");
                ImGui.Text($"Input in progress: {(_inputInProgress != 0)}");

                ImGui.Separator();

                string[] messages;

                lock (debugMessages)
                    messages = debugMessages.ToArray();

                foreach (var message in messages)
                {
                    ImGui.NewLine();
                    ImGui.TextWrapped(message);
                }
            }
            catch (Exception)
            {
            }
        }

        private void CustomDebugImGuiWindow(string message)
        {
            if (!Settings.Debug)
                return;

            ImGui.TextWrapped(message);
        }

        // clicks run on a background thread and log from there, so guard the list
        private void AddDebugMessage(string message)
        {
            lock (debugMessages)
                AddDebugMessageUnsafe(message);
        }

        private void AddDebugMessageUnsafe(string message)
        {
            if (debugMessages.Count == 0)
            {
                debugMessages.Add(message);
                return;
            }

            int lastIndex = debugMessages.Count - 1;
            string lastMessage = debugMessages[lastIndex];

            string lastMessageWithoutCounter =
                Regex.Replace(lastMessage, @"\s*\(\d+\)$", "");

            if (lastMessageWithoutCounter == message)
            {
                Match match = Regex.Match(lastMessage, @"\((\d+)\)$");

                if (match.Success)
                {
                    int count = int.Parse(match.Groups[1].Value);

                    debugMessages[lastIndex] =
                        Regex.Replace(lastMessage, @"\(\d+\)$", $"({count + 1})");
                }
                else
                {
                    debugMessages[lastIndex] = $"{message} (2)";
                }
            }
            else
            {
                debugMessages.Add(message);
            }
        }
    }
}
