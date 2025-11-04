import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
import json
import math
import uuid
from typing import List, Tuple, Dict, Optional, Set


class Node:
    """Reprezentuje węzeł w grafie (punkt na mapie)"""
    def __init__(self, x: float, y: float, node_id: int, label: str = ""):
        self.x = x
        self.y = y
        self.id = node_id
        self.label = label or f"N{node_id}"
        
    def distance_to(self, other: 'Node') -> float:
        """Oblicza dystans do innego węzła"""
        return math.sqrt((self.x - other.x)**2 + (self.y - other.y)**2)
    
    def to_dict(self) -> dict:
        return {"x": self.x, "y": self.y, "id": self.id, "label": self.label}
    
    @staticmethod
    def from_dict(data: dict) -> 'Node':
        return Node(data["x"], data["y"], data["id"], data.get("label", ""))


class Edge:
    """Reprezentuje krawędź w grafie (połączenie między punktami)"""
    def __init__(self, node1_id: int, node2_id: int, weight: Optional[float] = None):
        self.node1_id = node1_id
        self.node2_id = node2_id
        self.weight = weight
        
    def to_dict(self) -> dict:
        return {"node1_id": self.node1_id, "node2_id": self.node2_id, "weight": self.weight}
    
    @staticmethod
    def from_dict(data: dict) -> 'Edge':
        return Edge(data["node1_id"], data["node2_id"], data.get("weight"))


class Graph:
    """Reprezentuje graf (mapa budynku)"""
    def __init__(self, name: str = "Graf"):
        self.name = name
        self.nodes: Dict[int, Node] = {}
        self.edges: List[Edge] = []
        self.next_node_id = 1
        
    def add_node(self, x: float, y: float, label: str = "") -> Node:
        """Dodaje nowy węzeł do grafu"""
        node = Node(x, y, self.next_node_id, label)
        self.nodes[node.id] = node
        self.next_node_id += 1
        return node
    
    def add_edge(self, node1_id: int, node2_id: int, weight: Optional[float] = None) -> Edge:
        """Dodaje nową krawędź między węzłami"""
        if node1_id not in self.nodes or node2_id not in self.nodes:
            raise ValueError("Jeden z węzłów nie istnieje")
        
        # Sprawdź czy krawędź już istnieje
        for edge in self.edges:
            if (edge.node1_id == node1_id and edge.node2_id == node2_id) or \
               (edge.node1_id == node2_id and edge.node2_id == node1_id):
                return edge
        
        if weight is None:
            weight = self.nodes[node1_id].distance_to(self.nodes[node2_id])
        
        edge = Edge(node1_id, node2_id, weight)
        self.edges.append(edge)
        return edge
    
    def remove_node(self, node_id: int):
        """Usuwa węzeł i wszystkie połączone z nim krawędzie"""
        if node_id in self.nodes:
            del self.nodes[node_id]
            self.edges = [e for e in self.edges if e.node1_id != node_id and e.node2_id != node_id]
    
    def remove_edge(self, node1_id: int, node2_id: int):
        """Usuwa krawędź między węzłami"""
        self.edges = [e for e in self.edges if not (
            (e.node1_id == node1_id and e.node2_id == node2_id) or
            (e.node1_id == node2_id and e.node2_id == node1_id)
        )]
    
    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "nodes": [node.to_dict() for node in self.nodes.values()],
            "edges": [edge.to_dict() for edge in self.edges],
            "next_node_id": self.next_node_id
        }
    
    @staticmethod
    def from_dict(data: dict) -> 'Graph':
        graph = Graph(data.get("name", "Graf"))
        graph.next_node_id = data.get("next_node_id", 1)
        for node_data in data.get("nodes", []):
            node = Node.from_dict(node_data)
            graph.nodes[node.id] = node
        for edge_data in data.get("edges", []):
            graph.edges.append(Edge.from_dict(edge_data))
        return graph
    
    def merge_with(self, other: 'Graph', offset_x: float = 0, offset_y: float = 0):
        """Łączy ten graf z innym grafem"""
        # Mapowanie starych ID na nowe ID
        id_mapping = {}
        
        # Dodaj węzły z drugiego grafu
        for node in other.nodes.values():
            new_node = self.add_node(node.x + offset_x, node.y + offset_y, node.label)
            id_mapping[node.id] = new_node.id
        
        # Dodaj krawędzie z drugiego grafu
        for edge in other.edges:
            new_node1_id = id_mapping[edge.node1_id]
            new_node2_id = id_mapping[edge.node2_id]
            self.add_edge(new_node1_id, new_node2_id, edge.weight)


class GraphEditorApp:
    """Główna aplikacja do edycji grafów"""
    
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Edytor Grafów - Mapy Budynków")
        self.root.geometry("1600x900")
        
        # System pięter - każde piętro ma własny graf, sale i windy/schody
        self.floors = {}  # {floor_number: {"graph": Graph, "rooms": [], "elevators": [], "room_counter": 1, "elevator_counter": 1}}
        self.current_floor = 0  # Numer aktualnie wyświetlanego piętra
        self.floor_counter = 0  # Licznik do tworzenia nowych pięter
        
        # Inicjalizuj pierwsze piętro (parter)
        self.add_floor(0, "Parter")
        
        self.mode = "add_node"  # add_node, add_edge, move, delete, simulate_path
        self.selected_node = None
        self.edge_start_node = None
        self.canvas_objects = {}  # Mapowanie ID węzłów na obiekty canvas
        self.edge_objects = []  # Lista obiektów krawędzi
        
        # Symulacja ścieżki użytkownika
        self.path_points = []  # Lista punktów ścieżki
        self.path_line = None  # Linia ścieżki
        self.is_simulating = False
        self.last_path_node = None
        self.path_threshold = 30  # Próg odległości do tworzenia nowego węzła
        self.merge_radius = 40  # Promień do wykrywania pobliskich węzłów do połączenia
        self.corridor_detection_radius = 50  # Promień wykrywania równoległych korytarzy
        
        # Przesuwanie canvas
        self.pan_start_x = 0
        self.pan_start_y = 0
        self.is_panning = False
        
        # Siatka
        self.show_grid = True
        self.grid_size = 50
        
        # Workspace
        self.current_workspace = "graph_editor"  # graph_editor, map_editor, navigation
        
        # Preview
        self.room_preview = None  # Preview sali/windy przy dodawaniu
        
        # Navigation workspace
        self.nav_start_point = None  # {"floor": int, "type": "node"/"room"/"elevator", "id": ...}
        self.nav_end_point = None
        self.nav_path = None  # Lista kroków w trasie
        
        self.setup_ui()
        self.update_status()
    
    def add_floor(self, floor_number: int, name: str = None):
        """Dodaje nowe piętro"""
        if name is None:
            name = f"Piętro {floor_number}"
        
        self.floors[floor_number] = {
            "graph": Graph(name),
            "rooms": [],
            "elevators": [],
            "room_counter": 1,
            "elevator_counter": 1
        }
    
    @property
    def graph(self):
        """Zwraca graf aktualnego piętra"""
        return self.floors[self.current_floor]["graph"]
    
    @graph.setter
    def graph(self, value):
        """Ustawia graf aktualnego piętra"""
        self.floors[self.current_floor]["graph"] = value
    
    @property
    def rooms(self):
        """Zwraca sale aktualnego piętra"""
        return self.floors[self.current_floor]["rooms"]
    
    @rooms.setter
    def rooms(self, value):
        """Ustawia sale aktualnego piętra"""
        self.floors[self.current_floor]["rooms"] = value
    
    @property
    def elevators(self):
        """Zwraca windy/schody aktualnego piętra"""
        return self.floors[self.current_floor]["elevators"]
    
    @elevators.setter
    def elevators(self, value):
        """Ustawia windy/schody aktualnego piętra"""
        self.floors[self.current_floor]["elevators"] = value
    
    @property
    def room_counter(self):
        """Zwraca licznik sal aktualnego piętra"""
        return self.floors[self.current_floor]["room_counter"]
    
    @room_counter.setter
    def room_counter(self, value):
        """Ustawia licznik sal aktualnego piętra"""
        self.floors[self.current_floor]["room_counter"] = value
    
    @property
    def elevator_counter(self):
        """Zwraca licznik wind/schodów aktualnego piętra"""
        return self.floors[self.current_floor]["elevator_counter"]
    
    @elevator_counter.setter
    def elevator_counter(self, value):
        """Ustawia licznik wind/schodów aktualnego piętra"""
        self.floors[self.current_floor]["elevator_counter"] = value
        
    def setup_ui(self):
        """Tworzy interfejs użytkownika"""
        # Menu bar
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        
        # Menu Workspace - przełączanie między trybami
        workspace_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Workspace", menu=workspace_menu)
        workspace_menu.add_radiobutton(label="Graph Editor", command=lambda: self.switch_workspace("graph_editor"))
        workspace_menu.add_radiobutton(label="Map Editor", command=lambda: self.switch_workspace("map_editor"))
        workspace_menu.add_radiobutton(label="Navigation", command=lambda: self.switch_workspace("navigation"))
        
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Plik", menu=file_menu)
        file_menu.add_command(label="Nowy", command=self.new_graph)
        file_menu.add_command(label="Otwórz", command=self.load_graph)
        file_menu.add_command(label="Zapisz", command=self.save_graph)
        file_menu.add_separator()
        file_menu.add_command(label="Wyjście", command=self.root.quit)
        
        # Menu Piętra - zarządzanie piętrami
        floors_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Piętra", menu=floors_menu)
        floors_menu.add_command(label="Dodaj nowe piętro", command=self.add_new_floor)
        floors_menu.add_command(label="Lista wszystkich pięter", command=self.show_floors_list)
        
        # Menu Graf Edit - wszystkie funkcje edycji grafu
        self.graph_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Graph Editor", menu=self.graph_menu)
        self.graph_menu.add_command(label="Połącz z innym grafem", command=self.merge_graphs)
        self.graph_menu.add_command(label="Zmień nazwę", command=self.rename_graph)
        self.graph_menu.add_command(label="Wyczyść", command=self.clear_graph)
        self.graph_menu.add_separator()
        self.graph_menu.add_command(label="Generuj siatkę węzłów", command=self.generate_grid)
        self.graph_menu.add_command(label="Auto-połącz węzły", command=self.auto_connect)
        self.graph_menu.add_separator()
        self.graph_menu.add_command(label="Usuń węzły ścieżki", command=self.remove_path_nodes)
        self.graph_menu.add_command(label="Optymalizuj skrzyżowania", command=self.optimize_crossings)
        self.graph_menu.add_command(label="Uprość ścieżki (usuń zbędne węzły)", command=self.simplify_paths)
        self.graph_menu.add_separator()
        self.graph_menu.add_command(label="Wyrównaj wszystkie węzły do siatki", command=self.align_all_to_grid)
        
        # Menu Map Editor - funkcje edycji mapy
        self.map_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Map Editor", menu=self.map_menu)
        self.map_menu.add_command(label="Usuń wszystkie sale", command=self.remove_all_rooms)
        self.map_menu.add_command(label="Usuń wszystkie windy/schody", command=self.remove_all_elevators)
        
        # Toolbar - tryby edycji dla Graph Editor
        self.toolbar = ttk.Frame(self.root, padding="5")
        self.toolbar.pack(side=tk.TOP, fill=tk.X)
        
        ttk.Label(self.toolbar, text="Tryb:").pack(side=tk.LEFT, padx=5)
        
        self.mode_var = tk.StringVar(value="add_node")
        modes = [
            ("Dodaj węzeł", "add_node"),
            ("Dodaj krawędź", "add_edge"),
            ("Przesuń węzeł", "move"),
            ("Usuń", "delete"),
            ("Symuluj przejście", "simulate_path")
        ]
        
        for text, mode in modes:
            ttk.Radiobutton(self.toolbar, text=text, variable=self.mode_var, 
                           value=mode, command=self.change_mode).pack(side=tk.LEFT, padx=2)
        
        # Canvas
        canvas_frame = ttk.Frame(self.root)
        canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Scrollbars
        v_scroll = ttk.Scrollbar(canvas_frame, orient=tk.VERTICAL)
        h_scroll = ttk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL)
        
        self.canvas = tk.Canvas(canvas_frame, bg="white", cursor="cross", 
                               scrollregion=(0, 0, 3000, 3000),
                               yscrollcommand=v_scroll.set,
                               xscrollcommand=h_scroll.set)
        
        v_scroll.config(command=self.canvas.yview)
        h_scroll.config(command=self.canvas.xview)
        
        # Grid layout dla canvas i scrollbarów
        self.canvas.grid(row=0, column=0, sticky="nsew")
        v_scroll.grid(row=0, column=1, sticky="ns")
        h_scroll.grid(row=1, column=0, sticky="ew")
        
        canvas_frame.grid_rowconfigure(0, weight=1)
        canvas_frame.grid_columnconfigure(0, weight=1)
        
        # Panel pięter po prawej stronie (jak warstwy w Photoshopie)
        self.floors_panel = ttk.Frame(self.root, padding="5", relief=tk.RAISED, width=280)
        self.floors_panel.pack(side=tk.RIGHT, fill=tk.BOTH, padx=5, pady=5)
        self.floors_panel.pack_propagate(False)  # Zachowaj stałą szerokość
        
        # Nagłówek panelu pięter
        header_frame = ttk.Frame(self.floors_panel)
        header_frame.pack(side=tk.TOP, fill=tk.X, pady=(0, 5))
        
        ttk.Label(header_frame, text="Piętra", font=("Arial", 11, "bold")).pack(side=tk.LEFT)
        ttk.Button(header_frame, text="+", width=3, command=self.add_new_floor).pack(side=tk.RIGHT)
        
        # Informacje o aktualnym piętrze
        info_frame = ttk.LabelFrame(self.floors_panel, text="Aktualne piętro", padding="5")
        info_frame.pack(side=tk.TOP, fill=tk.X, pady=(0, 10))
        
        self.floor_info_label = ttk.Label(info_frame, text="", font=("Arial", 9), justify=tk.LEFT)
        self.floor_info_label.pack(fill=tk.X)
        
        # Opcje widoczności
        visibility_frame = ttk.LabelFrame(self.floors_panel, text="Podgląd sąsiednich", padding="5")
        visibility_frame.pack(side=tk.TOP, fill=tk.X, pady=(0, 10))
        
        self.show_floor_above_var = tk.BooleanVar(value=False)
        self.show_floor_below_var = tk.BooleanVar(value=False)
        
        ttk.Checkbutton(visibility_frame, text="Piętro wyżej", 
                       variable=self.show_floor_above_var, 
                       command=self.redraw).pack(anchor=tk.W)
        ttk.Checkbutton(visibility_frame, text="Piętro niżej", 
                       variable=self.show_floor_below_var, 
                       command=self.redraw).pack(anchor=tk.W)
        
        # Lista pięter (scrollable)
        list_frame = ttk.Frame(self.floors_panel)
        list_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        list_scroll = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        list_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.floors_listbox = tk.Listbox(list_frame, yscrollcommand=list_scroll.set, 
                                         font=("Arial", 10), activestyle='none')
        self.floors_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        list_scroll.config(command=self.floors_listbox.yview)
        
        self.floors_listbox.bind('<<ListboxSelect>>', self.on_floor_select)
        self.floors_listbox.bind('<Button-3>', self.show_floor_context_menu)
        
        # Przyciski akcji
        actions_frame = ttk.Frame(self.floors_panel)
        actions_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 0))
        
        ttk.Button(actions_frame, text="Zmień nazwę", command=self.rename_current_floor).pack(fill=tk.X, pady=2)
        ttk.Button(actions_frame, text="Usuń piętro", command=self.delete_current_floor).pack(fill=tk.X, pady=2)
        
        # Rysuj siatkę
        self.draw_grid()
        
        # Bind events
        self.canvas.bind("<Button-1>", self.canvas_click)
        self.canvas.bind("<B1-Motion>", self.canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.canvas_release)
        self.canvas.bind("<Button-3>", self.canvas_right_click)
        
        # Przesuwanie canvas środkowym przyciskiem lub Ctrl+lewy
        self.canvas.bind("<Button-2>", self.start_pan)
        self.canvas.bind("<B2-Motion>", self.pan_canvas)
        self.canvas.bind("<ButtonRelease-2>", self.end_pan)
        self.canvas.bind("<Control-Button-1>", self.start_pan)
        self.canvas.bind("<Control-B1-Motion>", self.pan_canvas)
        self.canvas.bind("<Control-ButtonRelease-1>", self.end_pan)
        
        # Tooltip na hover
        self.canvas.bind("<Motion>", self.on_mouse_move)
        self.tooltip = None
        
        # Side panel - usunięty
        # Status bar
        self.status_var = tk.StringVar(value="Gotowy")
        status_bar = ttk.Label(self.root, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Inicjalizuj domyślny workspace
        self.switch_workspace("graph_editor")
        
    def switch_workspace(self, workspace_name: str):
        """Przełącza między workspace'ami (Graph Editor / Map Editor)"""
        self.current_workspace = workspace_name
        
        # Wyczyść preview sali
        if self.room_preview:
            for item_id in self.room_preview:
                self.canvas.delete(item_id)
            self.room_preview = None
        
        # Ukryj/pokaż odpowiednie toolbary
        for widget in self.toolbar.winfo_children():
            widget.destroy()
        
        if workspace_name == "graph_editor":
            # Toolbar dla Graph Editor - tryby edycji grafu
            ttk.Label(self.toolbar, text="Graph Editor - Tryb:").pack(side=tk.LEFT, padx=5)
            
            self.mode_var = tk.StringVar(value="add_node")
            modes = [
                ("Dodaj węzeł", "add_node"),
                ("Dodaj krawędź", "add_edge"),
                ("Przesuń węzeł", "move"),
                ("Usuń", "delete"),
                ("Symuluj przejście", "simulate_path")
            ]
            
            for text, mode in modes:
                ttk.Radiobutton(self.toolbar, text=text, variable=self.mode_var, 
                               value=mode, command=self.change_mode).pack(side=tk.LEFT, padx=2)
            
            self.mode = "add_node"
            
        elif workspace_name == "map_editor":
            # Toolbar dla Map Editor - dodawanie sal
            ttk.Label(self.toolbar, text="Map Editor - Tryb:", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=10)
            
            self.map_mode_var = tk.StringVar(value="add_room")
            ttk.Radiobutton(self.toolbar, text="Dodaj salę", variable=self.map_mode_var, 
                           value="add_room", command=self.change_map_mode).pack(side=tk.LEFT, padx=2)
            ttk.Radiobutton(self.toolbar, text="Dodaj windę", variable=self.map_mode_var, 
                           value="add_elevator", command=self.change_map_mode).pack(side=tk.LEFT, padx=2)
            ttk.Radiobutton(self.toolbar, text="Dodaj schody", variable=self.map_mode_var, 
                           value="add_stairs", command=self.change_map_mode).pack(side=tk.LEFT, padx=2)
            ttk.Radiobutton(self.toolbar, text="Usuń", variable=self.map_mode_var, 
                           value="delete_room", command=self.change_map_mode).pack(side=tk.LEFT, padx=2)
            
            ttk.Separator(self.toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=10)
            ttk.Button(self.toolbar, text="🔗 Grupuj windy", 
                      command=self.open_elevator_grouping_dialog).pack(side=tk.LEFT, padx=5)
            
            self.mode = "add_room"
        
        elif workspace_name == "navigation":
            # Toolbar dla Navigation - wyznaczanie trasy
            ttk.Label(self.toolbar, text="Navigation - Nawigacja:", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=10)
            
            ttk.Button(self.toolbar, text="Wybierz punkt startowy (A)", 
                      command=self.set_nav_start_mode).pack(side=tk.LEFT, padx=5)
            ttk.Button(self.toolbar, text="Wybierz punkt docelowy (B)", 
                      command=self.set_nav_end_mode).pack(side=tk.LEFT, padx=5)
            
            ttk.Separator(self.toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=10)
            
            ttk.Button(self.toolbar, text="🔍 Znajdź trasę", 
                      command=self.find_path).pack(side=tk.LEFT, padx=5)
            ttk.Button(self.toolbar, text="✖ Wyczyść", 
                      command=self.clear_navigation).pack(side=tk.LEFT, padx=5)
            
            self.mode = "nav_idle"
        
        self.update_status()
        self.redraw()
    
    def change_map_mode(self):
        """Zmienia tryb edycji w Map Editor"""
        self.mode = self.map_mode_var.get()
        # Wyczyść preview sali
        if self.room_preview:
            for item_id in self.room_preview:
                self.canvas.delete(item_id)
            self.room_preview = None
        self.update_status()
        
    def change_mode(self):
        """Zmienia tryb edycji"""
        self.mode = self.mode_var.get()
        self.edge_start_node = None
        self.selected_node = None
        
        # Wyczyść ścieżkę jeśli zmieniamy tryb
        if self.mode != "simulate_path":
            self.clear_path()
        
        self.update_status()
        self.redraw()
        
    def update_status(self):
        """Aktualizuje pasek statusu i informacje w panelu pięter"""
        workspace_names = {
            "graph_editor": "Graph Editor",
            "map_editor": "Map Editor"
        }
        
        mode_names = {
            "add_node": "Dodawanie węzłów",
            "add_edge": "Dodawanie krawędzi",
            "move": "Przesuwanie węzłów",
            "delete": "Usuwanie",
            "simulate_path": "Symulacja przejścia",
            "add_room": "Dodawanie sal",
            "add_elevator": "Dodawanie wind",
            "add_stairs": "Dodawanie schodów",
            "delete_room": "Usuwanie elementów",
            "nav_idle": "Wybierz punkt startowy lub docelowy",
            "nav_select_start": "Kliknij, aby wybrać punkt startowy (A)",
            "nav_select_end": "Kliknij, aby wybrać punkt docelowy (B)"
        }
        
        workspace = workspace_names.get(self.current_workspace, "Unknown")
        mode_desc = mode_names.get(self.mode, self.mode)
        
        # Status bar - tylko tryb (krótki)
        status = f"{workspace} | {mode_desc}"
        self.status_var.set(status)
        
        # Szczegółowe informacje w panelu pięter
        floor_info = f"{self.graph.name}\n"
        floor_info += f"Piętro: {self.current_floor}\n"
        floor_info += f"─────────────────\n"
        floor_info += f"Węzłów: {len(self.graph.nodes)}\n"
        floor_info += f"Krawędzi: {len(self.graph.edges)}\n"
        floor_info += f"Sal: {len(self.rooms)}\n"
        floor_info += f"Wind/Schodów: {len(self.elevators)}"
        
        self.floor_info_label.config(text=floor_info)
        
        # Aktualizuj listę pięter
        self.update_floors_list()
    
    def update_floors_list(self):
        """Aktualizuje listę pięter w panelu"""
        self.floors_listbox.delete(0, tk.END)
        
        sorted_floors = sorted(self.floors.keys(), reverse=True)  # Od góry do dołu
        
        for floor_num in sorted_floors:
            floor_data = self.floors[floor_num]
            floor_name = floor_data['graph'].name
            
            # Formatowanie z ikonami i statystykami
            nodes_count = len(floor_data['graph'].nodes)
            rooms_count = len(floor_data['rooms'])
            elevators_count = len(floor_data['elevators'])
            
            display_text = f"{'★ ' if floor_num == self.current_floor else '   '}{floor_name} ({floor_num})"
            if nodes_count > 0 or rooms_count > 0:
                display_text += f" [{nodes_count}n {rooms_count}s {elevators_count}w]"
            
            self.floors_listbox.insert(tk.END, display_text)
        
        # Zaznacz aktualne piętro
        try:
            current_idx = sorted_floors.index(self.current_floor)
            self.floors_listbox.selection_clear(0, tk.END)
            self.floors_listbox.selection_set(current_idx)
            self.floors_listbox.see(current_idx)
            
            # Zmień kolor tła aktualnego piętra
            self.floors_listbox.itemconfig(current_idx, bg='lightblue')
        except ValueError:
            pass
    
    def on_floor_select(self, event):
        """Obsługuje wybór piętra z listy"""
        selection = self.floors_listbox.curselection()
        if selection:
            idx = selection[0]
            sorted_floors = sorted(self.floors.keys(), reverse=True)
            selected_floor = sorted_floors[idx]
            
            if selected_floor != self.current_floor:
                self.current_floor = selected_floor
                self.redraw()
                self.update_status()
    
    def show_floor_context_menu(self, event):
        """Pokazuje menu kontekstowe dla piętra"""
        # Znajdź które piętro zostało kliknięte
        idx = self.floors_listbox.nearest(event.y)
        self.floors_listbox.selection_clear(0, tk.END)
        self.floors_listbox.selection_set(idx)
        
        sorted_floors = sorted(self.floors.keys(), reverse=True)
        clicked_floor = sorted_floors[idx]
        
        # Menu kontekstowe
        context_menu = tk.Menu(self.root, tearoff=0)
        context_menu.add_command(label="Przejdź do tego piętra", 
                                command=lambda: self.switch_to_floor(clicked_floor))
        context_menu.add_command(label="Zmień nazwę", 
                                command=lambda: self.rename_floor(clicked_floor))
        context_menu.add_separator()
        context_menu.add_command(label="Usuń piętro", 
                                command=lambda: self.delete_floor(clicked_floor))
        
        context_menu.post(event.x_root, event.y_root)
    
    def switch_to_floor(self, floor_num):
        """Przełącza na wybrane piętro"""
        self.current_floor = floor_num
        self.redraw()
        self.update_status()
    
    def rename_floor(self, floor_num):
        """Zmienia nazwę wybranego piętra"""
        old_name = self.floors[floor_num]['graph'].name
        new_name = simpledialog.askstring("Zmień nazwę piętra", 
                                         "Nowa nazwa piętra:", 
                                         initialvalue=old_name,
                                         parent=self.root)
        if new_name:
            self.floors[floor_num]['graph'].name = new_name
            self.update_floors_list()
    
    def delete_floor(self, floor_num):
        """Usuwa wybrane piętro"""
        if len(self.floors) == 1:
            messagebox.showwarning("Nie można usunąć", "Nie można usunąć ostatniego piętra!")
            return
        
        floor_name = self.floors[floor_num]['graph'].name
        if not messagebox.askyesno("Usuń piętro", 
                                   f"Czy na pewno chcesz usunąć piętro '{floor_name}'?"):
            return
        
        # Usuń piętro
        del self.floors[floor_num]
        
        # Przejdź do innego piętra jeśli usunięto aktualne
        if self.current_floor == floor_num:
            self.current_floor = sorted(self.floors.keys())[0]
        
        self.redraw()
        self.update_status()
    
    def add_new_floor(self):
        """Dodaje nowe piętro"""
        # Zapytaj o numer piętra
        floor_number = simpledialog.askinteger("Nowe piętro", 
                                              "Podaj numer piętra (np. 1, 2, -1 dla piwnicy):",
                                              parent=self.root)
        if floor_number is None:
            return
        
        if floor_number in self.floors:
            messagebox.showwarning("Piętro istnieje", f"Piętro {floor_number} już istnieje!")
            return
        
        # Zapytaj o nazwę
        floor_name = simpledialog.askstring("Nazwa piętra", 
                                           f"Podaj nazwę dla piętra {floor_number}:",
                                           initialvalue=f"Piętro {floor_number}",
                                           parent=self.root)
        if not floor_name:
            floor_name = f"Piętro {floor_number}"
        
        # Dodaj piętro
        self.add_floor(floor_number, floor_name)
        self.current_floor = floor_number
        self.redraw()
        self.update_status()
        messagebox.showinfo("Dodano piętro", f"Dodano piętro: {floor_name}")
    
    def delete_current_floor(self):
        """Usuwa aktualne piętro"""
        if len(self.floors) == 1:
            messagebox.showwarning("Nie można usunąć", "Nie można usunąć ostatniego piętra!")
            return
        
        if not messagebox.askyesno("Usuń piętro", 
                                   f"Czy na pewno chcesz usunąć piętro '{self.graph.name}'?"):
            return
        
        # Usuń piętro
        del self.floors[self.current_floor]
        
        # Przejdź do innego piętra
        self.current_floor = sorted(self.floors.keys())[0]
        self.redraw()
        self.update_status()
    
    def rename_current_floor(self):
        """Zmienia nazwę aktualnego piętra"""
        new_name = simpledialog.askstring("Zmień nazwę piętra", 
                                         "Nowa nazwa piętra:", 
                                         initialvalue=self.graph.name,
                                         parent=self.root)
        if new_name:
            self.graph.name = new_name
            self.update_status()
    
    def open_elevator_grouping_dialog(self):
        """Otwiera okno do grupowania wind/schodów"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Grupowanie wind i schodów")
        dialog.geometry("900x600")
        dialog.transient(self.root)
        
        # Główny frame
        main_frame = ttk.Frame(dialog, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Instrukcje
        instructions = ttk.Label(main_frame, 
                                text="Zaznacz windy/schody z różnych pięter, które powinny być połączone w jedną grupę, następnie kliknij 'Połącz w grupę'.",
                                wraplength=850)
        instructions.pack(side=tk.TOP, pady=(0, 10))
        
        # Frame z listami (podzielony na kolumny dla każdego piętra)
        lists_frame = ttk.Frame(main_frame)
        lists_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        # Przechowujemy listboxy i ich dane
        listboxes = {}
        
        # Stwórz kolumnę dla każdego piętra
        for floor_num in sorted(self.floors.keys()):
            floor_data = self.floors[floor_num]
            floor_name = floor_data["graph"].name
            
            # Frame dla piętra
            floor_frame = ttk.LabelFrame(lists_frame, text=f"{floor_name} (Piętro {floor_num})", padding="5")
            floor_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
            
            # Listbox ze scrollbarem
            scroll = ttk.Scrollbar(floor_frame, orient=tk.VERTICAL)
            scroll.pack(side=tk.RIGHT, fill=tk.Y)
            
            listbox = tk.Listbox(floor_frame, selectmode=tk.MULTIPLE, yscrollcommand=scroll.set, 
                               exportselection=False)
            listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            scroll.config(command=listbox.yview)
            
            # Wypełnij listę windami/schodami z tego piętra
            for elevator in floor_data["elevators"]:
                elev_type = "🛗" if elevator["type"] == "elevator" else "🚶"
                group_info = ""
                if elevator.get("group_id"):
                    # Policz ile wind ma ten sam group_id
                    count = sum(1 for f in self.floors.values() 
                              for e in f["elevators"] 
                              if e.get("group_id") == elevator["group_id"])
                    group_info = f" [Grupa: {count} pięter]"
                
                listbox.insert(tk.END, f"{elev_type} {elevator['name']}{group_info}")
            
            listboxes[floor_num] = listbox
        
        # Przyciski akcji
        buttons_frame = ttk.Frame(main_frame)
        buttons_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 0))
        
        def connect_selected():
            """Łączy zaznaczone windy w jedną grupę"""
            selected_elevators = []
            
            # Zbierz zaznaczone windy ze wszystkich pięter
            for floor_num, listbox in listboxes.items():
                selected_indices = listbox.curselection()
                floor_elevators = self.floors[floor_num]["elevators"]
                
                for idx in selected_indices:
                    if idx < len(floor_elevators):
                        selected_elevators.append((floor_num, floor_elevators[idx]))
            
            if len(selected_elevators) < 2:
                messagebox.showwarning("Za mało wind", 
                                     "Zaznacz co najmniej 2 windy/schody z różnych pięter!",
                                     parent=dialog)
                return
            
            # Sprawdź czy są z różnych pięter
            floors_involved = set(floor_num for floor_num, _ in selected_elevators)
            if len(floors_involved) < 2:
                messagebox.showwarning("Te same piętro", 
                                     "Zaznaczone windy muszą być z różnych pięter!",
                                     parent=dialog)
                return
            
            # Utwórz nową grupę (UUID) lub użyj istniejącej jeśli któraś winda już ma group_id
            existing_group_id = None
            for floor_num, elevator in selected_elevators:
                if elevator.get("group_id"):
                    existing_group_id = elevator["group_id"]
                    break
            
            group_id = existing_group_id or str(uuid.uuid4())
            
            # Przypisz group_id do wszystkich zaznaczonych wind
            for floor_num, elevator in selected_elevators:
                elevator["group_id"] = group_id
            
            messagebox.showinfo("Połączono", 
                              f"Połączono {len(selected_elevators)} wind/schodów z {len(floors_involved)} pięter w jedną grupę!",
                              parent=dialog)
            
            # Odśwież dialog
            dialog.destroy()
            self.open_elevator_grouping_dialog()
        
        def ungroup_selected():
            """Usuwa grupowanie z zaznaczonych wind"""
            selected_count = 0
            
            # Usuń group_id z zaznaczonych wind
            for floor_num, listbox in listboxes.items():
                selected_indices = listbox.curselection()
                floor_elevators = self.floors[floor_num]["elevators"]
                
                for idx in selected_indices:
                    if idx < len(floor_elevators):
                        if floor_elevators[idx].get("group_id"):
                            del floor_elevators[idx]["group_id"]
                            selected_count += 1
            
            if selected_count == 0:
                messagebox.showinfo("Brak zmian", "Zaznaczone windy nie należały do żadnej grupy.", parent=dialog)
            else:
                messagebox.showinfo("Rozgrupowano", f"Usunięto grupowanie z {selected_count} wind/schodów.", parent=dialog)
                # Odśwież dialog
                dialog.destroy()
                self.open_elevator_grouping_dialog()
        
        ttk.Button(buttons_frame, text="🔗 Połącz w grupę", 
                  command=connect_selected).pack(side=tk.LEFT, padx=5)
        ttk.Button(buttons_frame, text="✂️ Rozgrupuj", 
                  command=ungroup_selected).pack(side=tk.LEFT, padx=5)
        ttk.Button(buttons_frame, text="Zamknij", 
                  command=dialog.destroy).pack(side=tk.RIGHT, padx=5)
        
        # Informacja o istniejących grupach
        info_frame = ttk.LabelFrame(main_frame, text="Istniejące grupy", padding="5")
        info_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 10))
        
        # Znajdź wszystkie grupy
        groups = {}
        for floor_num, floor_data in self.floors.items():
            for elevator in floor_data["elevators"]:
                group_id = elevator.get("group_id")
                if group_id:
                    if group_id not in groups:
                        groups[group_id] = []
                    groups[group_id].append((floor_num, elevator))
        
        if groups:
            info_text = f"Znaleziono {len(groups)} grup połączeń:\n"
            for i, (group_id, elevators) in enumerate(groups.items(), 1):
                floors_in_group = sorted(set(floor_num for floor_num, _ in elevators))
                names = [e['name'] for _, e in elevators]
                info_text += f"  Grupa {i}: {len(elevators)} wind/schodów ({', '.join(names)}) na piętrach {floors_in_group}\n"
        else:
            info_text = "Brak zdefiniowanych grup. Zaznacz windy i kliknij 'Połącz w grupę'."
        
        ttk.Label(info_frame, text=info_text, justify=tk.LEFT).pack(anchor=tk.W)
    
    def set_nav_start_mode(self):
        """Ustawia tryb wybierania punktu startowego"""
        self.mode = "nav_select_start"
        self.update_status()
    
    def set_nav_end_mode(self):
        """Ustawia tryb wybierania punktu docelowego"""
        self.mode = "nav_select_end"
        self.update_status()
    
    def clear_navigation(self):
        """Czyści wszystkie punkty nawigacji i trasę"""
        self.nav_start_point = None
        self.nav_end_point = None
        self.nav_path = None
        self.mode = "nav_idle"
        self.redraw()
        self.update_status()
    
    def select_navigation_point(self, x: float, y: float):
        """Wybiera punkt nawigacji (salę lub windę/schody)"""
        # Sprawdź sale
        for room in self.rooms:
            room_size = 15
            if (room["x"] - room_size <= x <= room["x"] + room_size and 
                room["y"] - room_size <= y <= room["y"] + room_size):
                point = {
                    "floor": self.current_floor,
                    "type": "room",
                    "data": room,
                    "name": room["name"]
                }
                return point
        
        # Sprawdź windy/schody
        for elevator in self.elevators:
            size = 15
            if (elevator["x"] - size <= x <= elevator["x"] + size and 
                elevator["y"] - size <= y <= elevator["y"] + size):
                point = {
                    "floor": self.current_floor,
                    "type": "elevator",
                    "data": elevator,
                    "name": elevator["name"]
                }
                return point
        
        # Nie akceptujemy węzłów jako punktów nawigacji
        return None
    
    def find_path(self):
        """Znajduje najkrótszą trasę między punktami A i B"""
        if not self.nav_start_point:
            messagebox.showwarning("Brak punktu startowego", "Wybierz punkt startowy (A)")
            return
        
        if not self.nav_end_point:
            messagebox.showwarning("Brak punktu docelowego", "Wybierz punkt docelowy (B)")
            return
        
        # AUTOMATYCZNE ODŚWIEŻENIE WAG - przelicz wagi wszystkich krawędzi na wszystkich piętrach
        self.recalculate_all_edge_weights()
        
        # Znajdź trasę używając algorytmu Dijkstry z uwzględnieniem pięter
        path = self.find_shortest_path_multi_floor(self.nav_start_point, self.nav_end_point)
        
        if path:
            self.nav_path = path
            self.redraw()
            
            # Pokaż szczegóły trasy
            self.show_path_details(path)
        else:
            messagebox.showerror("Brak trasy", "Nie można znaleźć trasy między wybranymi punktami!")
    
    def recalculate_all_edge_weights(self):
        """Automatycznie przelicza wagi wszystkich krawędzi na wszystkich piętrach"""
        updated_count = 0
        
        for floor_num, floor_data in self.floors.items():
            graph = floor_data["graph"]
            
            for edge in graph.edges:
                node1 = graph.nodes.get(edge.node1_id)
                node2 = graph.nodes.get(edge.node2_id)
                
                if node1 and node2:
                    # Oblicz rzeczywistą odległość euklidesową
                    distance = math.sqrt((node1.x - node2.x)**2 + (node1.y - node2.y)**2)
                    
                    # Aktualizuj wagę tylko jeśli się zmieniła
                    if edge.weight != distance:
                        edge.weight = distance
                        updated_count += 1
        
        # Opcjonalnie: wyświetl info o aktualizacji (tylko dla debugowania)
        # if updated_count > 0:
        #     print(f"Zaktualizowano {updated_count} wag krawędzi")
    
    def find_shortest_path_multi_floor(self, start_point, end_point):
        """Znajduje najkrótszą trasę między dwoma punktami przez graf"""
        import heapq
        
        # Krok 1: Znajdź najbliższe węzły dla punktów start i end
        start_floor = start_point["floor"]
        end_floor = end_point["floor"]
        
        start_nodes = self.get_nodes_near_point(start_point)
        end_nodes = self.get_nodes_near_point(end_point)
        
        if not start_nodes:
            messagebox.showerror("Błąd", f"Nie znaleziono węzłów grafu w pobliżu punktu startowego.\nUpewnij się że {start_point['name']} jest przy grafie.")
            return None
        
        if not end_nodes:
            messagebox.showerror("Błąd", f"Nie znaleziono węzłów grafu w pobliżu punktu docelowego.\nUpewnij się że {end_point['name']} jest przy grafie.")
            return None
        
        # Krok 2: Zbuduj mapę połączeń wind
        elevator_connections = self.build_elevator_connections()
        
        # Krok 3: Dijkstra - znajdź najkrótszą trasę
        queue = []
        visited = set()
        came_from = {}
        cost_so_far = {}
        
        # Inicjalizuj kolejkę od węzłów startowych
        for node_id, dist_from_start in start_nodes:
            state = (start_floor, node_id)
            heapq.heappush(queue, (dist_from_start, start_floor, node_id))
            cost_so_far[state] = dist_from_start
            came_from[state] = None
        
        # Stwórz specjalny stan końcowy (poza grafem)
        goal_state = ("END", -1)
        found_goal = None
        best_cost = float('inf')
        best_end_node = None
        
        while queue:
            current_cost, current_floor, current_node_id = heapq.heappop(queue)
            
            state = (current_floor, current_node_id)
            
            if state in visited:
                continue
            visited.add(state)
            
            # Sprawdź czy to jest stan końcowy
            if state == goal_state:
                if current_cost < best_cost:
                    best_cost = current_cost
                    found_goal = state
                continue
            
            # Pobierz obecny węzeł
            floor_data = self.floors[current_floor]
            graph = floor_data["graph"]
            current_node = graph.nodes.get(current_node_id)
            
            if not current_node:
                continue
            
            # Jeśli jesteśmy na piętrze docelowym, sprawdź czy możemy dojść do celu
            if current_floor == end_floor:
                for end_node_id, dist_to_end in end_nodes:
                    if current_node_id == end_node_id:
                        # Możemy dojść do celu z tego węzła
                        total_cost = current_cost + dist_to_end
                        
                        if goal_state not in visited and total_cost < cost_so_far.get(goal_state, float('inf')):
                            cost_so_far[goal_state] = total_cost
                            came_from[goal_state] = state
                            heapq.heappush(queue, (total_cost, "END", -1))
            
            if not current_node:
                continue
            
            # Eksploruj sąsiednie węzły
            for edge in graph.edges:
                next_node_id = None
                if edge.node1_id == current_node_id:
                    next_node_id = edge.node2_id
                elif edge.node2_id == current_node_id:
                    next_node_id = edge.node1_id
                
                if next_node_id:
                    next_node = graph.nodes.get(next_node_id)
                    if next_node:
                        next_state = (current_floor, next_node_id)
                        if next_state not in visited:
                            edge_cost = edge.weight if edge.weight else current_node.distance_to(next_node)
                            new_cost = current_cost + edge_cost
                            
                            if new_cost < cost_so_far.get(next_state, float('inf')):
                                cost_so_far[next_state] = new_cost
                                # Zapisz state + krawędź którą przeszliśmy
                                came_from[next_state] = (state, edge)
                                heapq.heappush(queue, (new_cost, current_floor, next_node_id))
            
            # Sprawdź windy/schody (przejścia między piętrami)
            for elevator in floor_data["elevators"]:
                elev_dist = math.sqrt((current_node.x - elevator["connection_x"])**2 + 
                                     (current_node.y - elevator["connection_y"])**2)
                
                if elev_dist < 500:  # Bardzo duży zasięg dla wind
                    group_id = elevator.get("group_id")
                    if not group_id:
                        continue
                    
                    # Znajdź tę samą windę na innych piętrach
                    for other_floor in elevator_connections.get(group_id, {}).keys():
                        if other_floor == current_floor:
                            continue
                        
                        other_elevators = elevator_connections[group_id][other_floor]
                        for other_elev in other_elevators:
                            # Znajdź węzły w pobliżu wyjścia z windy
                            other_graph = self.floors[other_floor]["graph"]
                            
                            for other_node in other_graph.nodes.values():
                                exit_dist = math.sqrt((other_node.x - other_elev["connection_x"])**2 + 
                                                     (other_node.y - other_elev["connection_y"])**2)
                                
                                if exit_dist < 500:  # Bardzo duży zasięg
                                    next_state = (other_floor, other_node.id)
                                    if next_state not in visited:
                                        floor_cost = 50 if elevator["type"] == "elevator" else 80
                                        new_cost = current_cost + elev_dist + floor_cost + exit_dist
                                        
                                        if new_cost < cost_so_far.get(next_state, float('inf')):
                                            cost_so_far[next_state] = new_cost
                                            came_from[next_state] = (state, elevator, other_elev)
                                            heapq.heappush(queue, (new_cost, other_floor, other_node.id))
        
        # Zrekonstruuj ścieżkę
        if found_goal:
            return self.reconstruct_path(came_from, found_goal, start_point, end_point)
        
        return None
    
    def get_nodes_near_point(self, point):
        """Zwraca listę węzłów w pobliżu punktu (jako [(node_id, distance), ...])"""
        floor_data = self.floors[point["floor"]]
        graph = floor_data["graph"]
        data = point["data"]
        
        # Pobierz współrzędne punktu połączenia (najpierw connection, potem x/y)
        if "connection_x" in data and "connection_y" in data:
            px, py = data["connection_x"], data["connection_y"]
        else:
            px, py = data["x"], data["y"]
        
        # Znajdź węzły w promieniu (zwiększony zasięg)
        nearby_nodes = []
        max_distance = 500  # Bardzo duży zasięg
        
        for node in graph.nodes.values():
            dist = math.sqrt((node.x - px)**2 + (node.y - py)**2)
            if dist < max_distance:
                nearby_nodes.append((node.id, dist))
        
        # Sortuj po odległości
        nearby_nodes.sort(key=lambda x: x[1])
        
        # Jeśli nie znaleziono żadnych węzłów w zasięgu, znajdź najbliższy bez limitu
        if not nearby_nodes and graph.nodes:
            closest_node = None
            min_dist = float('inf')
            for node in graph.nodes.values():
                dist = math.sqrt((node.x - px)**2 + (node.y - py)**2)
                if dist < min_dist:
                    min_dist = dist
                    closest_node = node
            if closest_node:
                nearby_nodes.append((closest_node.id, min_dist))
        
        return nearby_nodes
    
    def reconstruct_path(self, came_from, goal_state, start_point, end_point):
        """Rekonstruuje ścieżkę z mapy came_from"""
        # Idź wstecz od celu do startu, budując listę kroków
        path_items = []
        
        # Jeśli goal_state to ("END", -1), zacznij od came_from[goal_state]
        if goal_state == ("END", -1):
            current = came_from.get(goal_state)
        else:
            current = goal_state
        
        # Zbierz wszystkie kroki od celu do startu
        iteration = 0
        while current is not None and iteration < 100:
            iteration += 1
            
            # Dodaj obecny stan do ścieżki
            if current != ("END", -1):
                path_items.append(("node", current, None))
            
            # Pobierz poprzedni stan
            value = came_from.get(current)
            
            if value is None:
                # Dotarliśmy do startu
                break
            elif isinstance(value, tuple):
                if len(value) == 4:
                    # Przejście przez windę: (prev_state, "elevator", enter_elev, exit_elev)
                    prev_state, marker, enter_elev, exit_elev = value
                    # Wstaw informację o windzie PRZED obecnym statem
                    path_items[-1] = ("elevator", current, enter_elev, exit_elev)
                    current = prev_state
                elif len(value) == 3:
                    # Może to stary format windy: (prev_state, enter_elev, exit_elev)
                    prev_state, enter_elev, exit_elev = value
                    path_items[-1] = ("elevator", current, enter_elev, exit_elev)
                    current = prev_state
                elif len(value) == 2:
                    # Zwykła krawędź: (prev_state, edge)
                    prev_state, edge = value
                    # Zaktualizuj ostatni item o edge
                    if path_items:
                        path_items[-1] = ("node", current, edge)
                    current = prev_state
                else:
                    current = value[0] if value else None
            else:
                # Pojedyncza wartość - poprzedni stan
                current = value
        
        # Odwróć kolejność (od startu do celu)
        path_items.reverse()
        
        # Buduj finalną ścieżkę
        path = []
        
        # Dodaj punkt startowy
        path.append({
            "floor": start_point["floor"],
            "type": "start",
            "point": start_point
        })
        
        # Przetwórz wszystkie kroki
        for i, item in enumerate(path_items):
            if item[0] == "node":
                # Węzeł grafu
                state = item[1]
                edge = item[2] if len(item) > 2 else None
                
                if state == ("END", -1):
                    continue
                
                floor_num, node_id = state
                node = self.floors[floor_num]["graph"].nodes.get(node_id)
                
                if node:
                    path.append({
                        "floor": floor_num,
                        "type": "node",
                        "node": node,
                        "edge": edge
                    })
            
            elif item[0] == "elevator":
                # Przejście przez windę
                current_state, enter_elev, exit_elev = item[1], item[2], item[3]
                
                if current_state == ("END", -1):
                    continue
                
                floor_num, node_id = current_state
                
                # Dodaj wejście do windy na poprzednim piętrze
                if len(path) > 0:
                    prev_floor = path[-1]["floor"]
                    path.append({
                        "floor": prev_floor,
                        "type": "elevator_enter",
                        "elevator": enter_elev
                    })
                
                # Dodaj wyjście z windy na nowym piętrze
                path.append({
                    "floor": floor_num,
                    "type": "elevator_exit",
                    "elevator": exit_elev
                })
        
        # Dodaj punkt końcowy
        path.append({
            "floor": end_point["floor"],
            "type": "end",
            "point": end_point
        })
        
        return path
    
    def build_elevator_connections(self):
        """Buduje mapę połączeń wind między piętrami na podstawie group_id"""
        connections = {}
        
        for floor_num, floor_data in self.floors.items():
            for elevator in floor_data["elevators"]:
                group_id = elevator.get("group_id")
                
                # Pomiń windy bez group_id (niezgrupowane)
                if not group_id:
                    continue
                
                if group_id not in connections:
                    connections[group_id] = {}
                
                if floor_num not in connections[group_id]:
                    connections[group_id][floor_num] = []
                
                connections[group_id][floor_num].append(elevator)
        
        return connections
    
    def get_nearest_node_to_point(self, point):
        """Zwraca najbliższy węzeł do punktu (sala lub winda)"""
        floor_data = self.floors[point["floor"]]
        graph = floor_data["graph"]
        
        if point["type"] == "room":
            room = point["data"]
            x, y = room["x"], room["y"]
        elif point["type"] == "elevator":
            elevator = point["data"]
            x, y = elevator["x"], elevator["y"]
        else:
            return None
        
        # Znajdź najbliższy węzeł
        closest_node = None
        min_distance = float('inf')
        
        for node in graph.nodes.values():
            dist = math.sqrt((node.x - x)**2 + (node.y - y)**2)
            if dist < min_distance:
                min_distance = dist
                closest_node = node
        
        return closest_node
    
    def show_path_details(self, path):
        """Pokazuje szczegóły znalezionej trasy"""
        details = ["╔═══ TRASA NAWIGACJI ═══╗\n"]
        start_name = self.nav_start_point['name']
        end_name = self.nav_end_point['name']
        
        details.append(f"📍 START: {start_name}")
        details.append(f"   (Piętro {self.nav_start_point['floor']})\n")
        details.append(f"🎯 CEL: {end_name}")
        details.append(f"   (Piętro {self.nav_end_point['floor']})\n")
        
        # Sprawdź czy zmiana piętra jest konieczna
        has_floor_change = any(step.get("type") == "elevator_enter" for step in path)
        if has_floor_change:
            details.append("⚠️  Trasa wymaga zmiany piętra\n")
        
        details.append("━━━━━━━━━━━━━━━━━━━━━━")
        details.append("INSTRUKCJE:\n")
        
        step_num = 1
        current_floor = self.nav_start_point['floor']
        shown_nodes = set()
        
        for i, step in enumerate(path):
            step_type = step.get("type", "")
            
            if step_type == "start":
                details.append(f"1️⃣  Wyjdź z: {start_name}")
                step_num += 1
                
            elif step_type == "node":
                # Pokaż tylko ważne węzły (z etykietami lub przed windami)
                node = step["node"]
                
                # Sprawdź czy następny krok to winda
                next_is_elevator = (i + 1 < len(path) and 
                                  path[i + 1].get("type") == "elevator_enter")
                
                # Pokaż węzeł jeśli ma etykietę lub jest przed windą
                if node.label and node.label != f"N{node.id}":
                    if node.id not in shown_nodes:
                        details.append(f"   ↓ Idź przez: {node.label}")
                        shown_nodes.add(node.id)
                elif next_is_elevator and node.id not in shown_nodes:
                    details.append(f"   ↓ Dojdź do punktu przejścia")
                    shown_nodes.add(node.id)
                
            elif step_type == "elevator_enter":
                elevator = step["elevator"]
                elev_type = "windą" if elevator["type"] == "elevator" else "schodami"
                elev_icon = "🛗" if elevator["type"] == "elevator" else "🚶"
                
                # Znajdź docelowe piętro
                target_floor = None
                for j in range(i + 1, len(path)):
                    if path[j].get("type") == "elevator_exit":
                        target_floor = path[j]["floor"]
                        break
                
                if target_floor is not None:
                    direction = "w górę ⬆️" if target_floor > step["floor"] else "w dół ⬇️"
                    floor_diff = abs(target_floor - step["floor"])
                    details.append(f"\n{step_num}️⃣  {elev_icon} Użyj: {elevator['name']}")
                    details.append(f"   Jedź {elev_type} {direction}")
                    details.append(f"   Zmiana: {step['floor']} → {target_floor} ({floor_diff} piętro/a)")
                    current_floor = target_floor
                else:
                    details.append(f"\n{step_num}️⃣  {elev_icon} Użyj: {elevator['name']} ({elev_type})")
                
                step_num += 1
                shown_nodes.clear()  # Reset dla nowego piętra
                
            elif step_type == "end":
                details.append(f"\n{step_num}️⃣  Dotarłeś do celu: {end_name}")
                details.append("\n✅ META OSIĄGNIĘTA!")
        
        details.append("\n╚═══════════════════════╝")
        
        messagebox.showinfo("🗺️ Znaleziona trasa", "\n".join(details))
    
    def show_floors_list(self):
        """Pokazuje listę wszystkich pięter"""
        sorted_floors = sorted(self.floors.keys())
        
        info_lines = ["Lista wszystkich pięter:\n"]
        for num in sorted_floors:
            floor_data = self.floors[num]
            graph = floor_data['graph']
            current_marker = " ◄ AKTUALNE" if num == self.current_floor else ""
            info_lines.append(f"Piętro {num}: {graph.name}{current_marker}")
            info_lines.append(f"  • Węzłów: {len(graph.nodes)}, Krawędzi: {len(graph.edges)}")
            info_lines.append(f"  • Sal: {len(floor_data['rooms'])}, Wind/Schodów: {len(floor_data['elevators'])}\n")
        
        messagebox.showinfo("Lista pięter", "\n".join(info_lines))
        
    def canvas_click(self, event):
        """Obsługuje kliknięcie na canvas"""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        
        if self.mode == "nav_select_start":
            # Wybierz punkt startowy (A) w trybie nawigacji
            point = self.select_navigation_point(x, y)
            if point:
                self.nav_start_point = point
                self.mode = "nav_idle"
                self.redraw()
                self.update_status()
                messagebox.showinfo("Punkt startowy", 
                                  f"Wybrano punkt startowy (A):\n{point['name']}\nPiętro {point['floor']}")
            else:
                messagebox.showwarning("Błąd", "Nie znaleziono sali lub windy/schodów w tym miejscu.\nKliknij na salę lub windę/schody.")
        
        elif self.mode == "nav_select_end":
            # Wybierz punkt docelowy (B) w trybie nawigacji
            point = self.select_navigation_point(x, y)
            if point:
                self.nav_end_point = point
                self.mode = "nav_idle"
                self.redraw()
                self.update_status()
                messagebox.showinfo("Punkt docelowy", 
                                  f"Wybrano punkt docelowy (B):\n{point['name']}\nPiętro {point['floor']}")
            else:
                messagebox.showwarning("Błąd", "Nie znaleziono sali lub windy/schodów w tym miejscu.\nKliknij na salę lub windę/schody.")
        
        elif self.mode == "add_room":
            # Dodaj salę w Map Editor
            self.add_room_at(x, y)
        
        elif self.mode == "add_elevator":
            # Dodaj windę w Map Editor
            self.add_elevator_at(x, y, "elevator")
        
        elif self.mode == "add_stairs":
            # Dodaj schody w Map Editor
            self.add_elevator_at(x, y, "stairs")
            
        elif self.mode == "delete_room":
            # Usuń salę lub windę/schody w Map Editor
            if not self.delete_room_at(x, y):
                self.delete_elevator_at(x, y)
            
        elif self.mode == "add_node":
            label = simpledialog.askstring("Etykieta węzła", "Podaj etykietę (opcjonalnie):", parent=self.root)
            node = self.graph.add_node(x, y, label or "")
            self.draw_node(node)
            self.update_status()
            
        elif self.mode == "add_edge":
            clicked_node = self.find_node_at(x, y)
            if clicked_node:
                if self.edge_start_node is None:
                    self.edge_start_node = clicked_node
                    self.canvas.itemconfig(self.canvas_objects[clicked_node.id], fill="yellow")
                else:
                    if self.edge_start_node.id != clicked_node.id:
                        self.graph.add_edge(self.edge_start_node.id, clicked_node.id)
                        self.redraw()
                        self.update_status()
                    self.edge_start_node = None
                    
        elif self.mode == "move":
            self.selected_node = self.find_node_at(x, y)
            
        elif self.mode == "delete":
            clicked_node = self.find_node_at(x, y)
            if clicked_node:
                self.graph.remove_node(clicked_node.id)
                self.redraw()
                self.update_status()
            else:
                # Sprawdź czy kliknięto na krawędź
                clicked_edge = self.find_edge_at(x, y)
                if clicked_edge:
                    self.graph.remove_edge(clicked_edge.node1_id, clicked_edge.node2_id)
                    self.redraw()
                    self.update_status()
                    
        elif self.mode == "simulate_path":
            # Rozpocznij symulację ścieżki
            self.is_simulating = True
            self.path_points = [(x, y)]
            self.last_path_node = None
    
    def canvas_drag(self, event):
        """Obsługuje przeciąganie"""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        
        if self.mode == "move" and self.selected_node:
            self.selected_node.x = x
            self.selected_node.y = y
            self.redraw()
            
        elif self.mode == "simulate_path" and self.is_simulating:
            # Dodaj punkt do ścieżki
            self.path_points.append((x, y))
            
            # Rysuj ścieżkę na bieżąco
            if len(self.path_points) > 1:
                if self.path_line:
                    self.canvas.delete(self.path_line)
                self.path_line = self.canvas.create_line(self.path_points, 
                                                         fill="green", 
                                                         width=3, 
                                                         smooth=True,
                                                         tags="path_preview")
            
            # Twórz węzły w prosty sposób
            if self.last_path_node is None:
                # Pierwszy węzeł - sprawdź czy blisko istniejącego węzła (mniejszy promień dla bezpieczeństwa)
                nearby_node = self.find_nearby_existing_node(x, y, self.merge_radius * 0.7, exclude_path_nodes=True)
                
                if nearby_node:
                    # Połącz się z istniejącym węzłem
                    self.last_path_node = nearby_node
                    # Podświetl węzeł
                    if nearby_node.id in self.canvas_objects:
                        self.canvas.itemconfig(self.canvas_objects[nearby_node.id], fill="yellow", width=3)
                else:
                    # Utwórz nowy węzeł
                    node = self.graph.add_node(x, y, f"P{len(self.graph.nodes)}")
                    self.last_path_node = node
                    self.draw_node(node)
            else:
                # Sprawdź odległość od ostatniego węzła
                distance = math.sqrt((x - self.last_path_node.x)**2 + (y - self.last_path_node.y)**2)
                if distance >= self.path_threshold:
                    # Najpierw sprawdź czy nie jesteśmy blisko istniejącego węzła (mniejszy promień)
                    nearby_node = self.find_nearby_existing_node(x, y, self.merge_radius * 0.7, exclude_path_nodes=True)
                    
                    if nearby_node:
                        # Połącz z istniejącym węzłem zamiast tworzyć nowy
                        if not self.edge_exists(self.last_path_node.id, nearby_node.id):
                            self.graph.add_edge(self.last_path_node.id, nearby_node.id)
                            self.draw_edge(self.graph.edges[-1])
                        self.last_path_node = nearby_node
                        # Podświetl węzeł
                        if nearby_node.id in self.canvas_objects:
                            self.canvas.itemconfig(self.canvas_objects[nearby_node.id], fill="yellow", width=3)
                    else:
                        # Sprawdź czy nowy segment przecina istniejącą krawędź
                        crossing_info = self.find_edge_crossing(self.last_path_node.x, self.last_path_node.y, x, y)
                        
                        if crossing_info:
                            edge, intersection_point = crossing_info
                            ix, iy = intersection_point
                            
                            # Utwórz węzeł skrzyżowania
                            crossing_node = self.graph.add_node(ix, iy, f"X{len([n for n in self.graph.nodes.values() if n.label.startswith('X')])+1}")
                            
                            # Podziel istniejącą krawędź
                            node1 = self.graph.nodes.get(edge.node1_id)
                            node2 = self.graph.nodes.get(edge.node2_id)
                            
                            if node1 and node2:
                                self.graph.remove_edge(edge.node1_id, edge.node2_id)
                                self.graph.add_edge(edge.node1_id, crossing_node.id)
                                self.graph.add_edge(crossing_node.id, edge.node2_id)
                            
                            # Połącz z naszą ścieżką
                            self.graph.add_edge(self.last_path_node.id, crossing_node.id)
                            
                            # Przerysuj wszystko
                            self.redraw()
                            # Narysuj ścieżkę z powrotem
                            if len(self.path_points) > 1:
                                self.path_line = self.canvas.create_line(self.path_points, 
                                                                         fill="green", 
                                                                         width=3, 
                                                                         smooth=True,
                                                                         tags="path_preview")
                            
                            self.last_path_node = crossing_node
                        else:
                            # Utwórz nowy węzeł i połącz z poprzednim
                            node = self.graph.add_node(x, y, f"P{len(self.graph.nodes)}")
                            self.graph.add_edge(self.last_path_node.id, node.id)
                            self.draw_node(node)
                            self.draw_edge(self.graph.edges[-1])
                            self.last_path_node = node
            
    def canvas_release(self, event):
        """Obsługuje puszczenie przycisku myszy"""
        if self.mode == "move":
            self.selected_node = None
            
        elif self.mode == "simulate_path" and self.is_simulating:
            # Zakończ symulację ścieżki
            x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            
            # Sprawdź czy ostatni węzeł powinien połączyć się z istniejącym grafem (mniejszy promień)
            if self.last_path_node:
                nearby_end_node = self.find_nearby_existing_node(x, y, self.merge_radius * 0.7, exclude_path_nodes=True)
                
                if nearby_end_node and nearby_end_node.id != self.last_path_node.id:
                    # Połącz koniec ścieżki z najbliższym węzłem istniejącego grafu
                    if not self.edge_exists(self.last_path_node.id, nearby_end_node.id):
                        self.graph.add_edge(self.last_path_node.id, nearby_end_node.id)
            
            self.is_simulating = False
            self.clear_path_preview()
            self.last_path_node = None
            
            # AUTOMATYCZNE MERGOWANIE BLISKICH WĘZŁÓW (bardzo konserwatywne - tylko bardzo blisko)
            # Tylko proste mergowanie węzłów które są bardzo blisko siebie
            merged = self.auto_merge_nearby_nodes(self.merge_radius * 0.3)  # Jeszcze mniejszy promień
            
            self.redraw()
            self.update_status()
            
    def canvas_right_click(self, event):
        """Obsługuje prawy przycisk myszy"""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        clicked_node = self.find_node_at(x, y)
        if clicked_node:
            menu = tk.Menu(self.root, tearoff=0)
            menu.add_command(label=f"Węzeł: {clicked_node.label}", state=tk.DISABLED)
            menu.add_separator()
            menu.add_command(label="Zmień etykietę", 
                           command=lambda: self.rename_node(clicked_node))
            menu.add_command(label="Usuń węzeł", 
                           command=lambda: self.delete_node(clicked_node))
            menu.post(event.x_root, event.y_root)
    
    def on_mouse_move(self, event):
        """Obsługuje ruch myszy - pokazuje tooltip z informacją o węźle lub preview sali"""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        
        # Usuń poprzedni tooltip
        if self.tooltip:
            if isinstance(self.tooltip, tuple):
                for item_id in self.tooltip:
                    self.canvas.delete(item_id)
            else:
                self.canvas.delete(self.tooltip)
            self.tooltip = None
        
        # Usuń poprzedni preview sali
        if self.room_preview:
            for item_id in self.room_preview:
                self.canvas.delete(item_id)
            self.room_preview = None
        
        # Tryb dodawania sali - pokaż preview
        if self.mode == "add_room":
            self.show_room_preview(x, y)
            return
        
        # Tryb dodawania windy - pokaż preview
        if self.mode == "add_elevator":
            self.show_elevator_preview(x, y, "elevator")
            return
        
        # Tryb dodawania schodów - pokaż preview
        if self.mode == "add_stairs":
            self.show_elevator_preview(x, y, "stairs")
            return
        
        # Znajdź węzeł pod kursorem (tylko w Graph Editor)
        if self.current_workspace == "graph_editor":
            node = self.find_node_at(x, y)
            if node:
                # Policz połączenia
                connections = len([e for e in self.graph.edges 
                                 if e.node1_id == node.id or e.node2_id == node.id])
                
                # Utwórz tekst tooltipa
                tooltip_text = f"{node.label} (ID: {node.id})\n[{node.x:.0f}, {node.y:.0f}]\nPołączenia: {connections}"
                
                # Pozycja tooltipa - nad węzłem
                tooltip_x = node.x
                tooltip_y = node.y - 40
                
                # Rysuj tło tooltipa
                lines = tooltip_text.split('\n')
                max_width = max(len(line) for line in lines) * 7
                height = len(lines) * 14
                
                bg_id = self.canvas.create_rectangle(
                    tooltip_x - max_width//2 - 5, tooltip_y - height//2 - 5,
                    tooltip_x + max_width//2 + 5, tooltip_y + height//2 + 5,
                    fill="lightyellow", outline="black", width=1
                )
                
                # Rysuj tekst
                text_id = self.canvas.create_text(
                    tooltip_x, tooltip_y,
                    text=tooltip_text,
                    font=("Arial", 9),
                    fill="black",
                    justify=tk.CENTER
                )
                
                # Zapamiętaj ID tooltipa (aby móc usunąć)
                self.tooltip = (bg_id, text_id)
    
    def show_room_preview(self, x: float, y: float):
        """Pokazuje preview sali przy dodawaniu"""
        # Usuń stary preview
        self.canvas.delete("preview")
        
        if len(self.graph.edges) == 0:
            return
        
        # Znajdź najbliższą krawędź
        closest_edge = None
        min_distance = float('inf')
        closest_point = None
        
        for edge in self.graph.edges:
            node1 = self.graph.nodes.get(edge.node1_id)
            node2 = self.graph.nodes.get(edge.node2_id)
            
            if node1 and node2:
                # Znajdź najbliższy punkt na krawędzi
                point_x, point_y, distance = self.closest_point_on_line(
                    x, y, node1.x, node1.y, node2.x, node2.y
                )
                
                if distance < min_distance:
                    min_distance = distance
                    closest_edge = edge
                    closest_point = (point_x, point_y)
        
        if closest_edge is None or closest_point is None:
            return
        
        # Oblicz pozycję preview sali - 30px prostopadle od krawędzi
        node1 = self.graph.nodes.get(closest_edge.node1_id)
        node2 = self.graph.nodes.get(closest_edge.node2_id)
        
        # Wektor krawędzi
        dx = node2.x - node1.x
        dy = node2.y - node1.y
        length = (dx**2 + dy**2)**0.5
        
        if length > 0:
            # Wektor prostopadły (obrócony o 90 stopni)
            perp_x = -dy / length
            perp_y = dx / length
            
            # Określ którą stronę wybrać (bliższą do kursora)
            offset_dist = 30
            test_x1 = closest_point[0] + perp_x * offset_dist
            test_y1 = closest_point[1] + perp_y * offset_dist
            test_x2 = closest_point[0] - perp_x * offset_dist
            test_y2 = closest_point[1] - perp_y * offset_dist
            
            dist1 = ((x - test_x1)**2 + (y - test_y1)**2)**0.5
            dist2 = ((x - test_x2)**2 + (y - test_y2)**2)**0.5
            
            if dist1 < dist2:
                room_x = test_x1
                room_y = test_y1
            else:
                room_x = test_x2
                room_y = test_y2
            
            room_size = 15
            
            # Rysuj preview z półprzezroczystością (używając stipple)
            # Linia połączenia
            self.canvas.create_line(
                closest_point[0], closest_point[1], 
                room_x, room_y,
                fill="orange", width=2, dash=(5, 3), 
                stipple="gray50", tags="preview"
            )
            
            # Kwadrat sali
            self.canvas.create_rectangle(
                room_x - room_size, room_y - room_size,
                room_x + room_size, room_y + room_size,
                fill="yellow", outline="orange", width=2, 
                stipple="gray50", tags="preview"
            )
            
            # Tekst preview
            self.canvas.create_text(
                room_x, room_y, 
                text=f"Sala {self.room_counter}",
                font=("Arial", 9, "bold"), 
                fill="gray", tags="preview"
            )
            
            # Punkt na krawędzi (czerwona kropka)
            self.canvas.create_oval(
                closest_point[0] - 3, closest_point[1] - 3,
                closest_point[0] + 3, closest_point[1] + 3,
                fill="red", outline="darkred", tags="preview"
            )
    
    def start_pan(self, event):
        """Rozpoczyna przesuwanie canvas"""
        self.is_panning = True
        self.pan_start_x = event.x
        self.pan_start_y = event.y
        self.canvas.config(cursor="fleur")
    
    def pan_canvas(self, event):
        """Przesuwa canvas"""
        if self.is_panning:
            dx = event.x - self.pan_start_x
            dy = event.y - self.pan_start_y
            
            self.canvas.xview_scroll(-dx, "units")
            self.canvas.yview_scroll(-dy, "units")
            
            self.pan_start_x = event.x
            self.pan_start_y = event.y
    
    def end_pan(self, event):
        """Kończy przesuwanie canvas"""
        self.is_panning = False
        self.canvas.config(cursor="cross")
    
    def draw_grid(self):
        """Rysuje siatkę na canvas"""
        if not self.show_grid:
            return
        
        # Usuń starą siatkę
        self.canvas.delete("grid")
        
        # Pobierz rozmiar widocznego obszaru
        scroll_region = self.canvas.cget("scrollregion").split()
        if len(scroll_region) == 4:
            max_x = int(scroll_region[2])
            max_y = int(scroll_region[3])
        else:
            max_x = 3000
            max_y = 3000
        
        # Rysuj linie pionowe
        for x in range(0, max_x, self.grid_size):
            self.canvas.create_line(x, 0, x, max_y, fill="#e0e0e0", tags="grid")
        
        # Rysuj linie poziome
        for y in range(0, max_y, self.grid_size):
            self.canvas.create_line(0, y, max_x, y, fill="#e0e0e0", tags="grid")
        
        # Przesuń siatkę na spód
        self.canvas.tag_lower("grid")
    
    def toggle_grid(self):
        """Przełącza widoczność siatki"""
        self.show_grid = not self.show_grid
        if self.show_grid:
            self.draw_grid()
        else:
            self.canvas.delete("grid")
    
    def align_all_to_grid(self):
        """Wyrównuje wszystkie węzły do najbliższych punktów siatki"""
        if len(self.graph.nodes) == 0:
            messagebox.showwarning("Brak węzłów", "Nie ma węzłów do wyrównania")
            return
        
        for node in self.graph.nodes.values():
            node.x = round(node.x / self.grid_size) * self.grid_size
            node.y = round(node.y / self.grid_size) * self.grid_size
        
        self.redraw()
        self.update_info()
        messagebox.showinfo("Wyrównano", f"Wyrównano {len(self.graph.nodes)} węzłów do siatki {self.grid_size}px")
    
    def find_node_at(self, x: float, y: float, radius: float = 10) -> Optional[Node]:
        """Znajduje węzeł w pobliżu punktu (x, y)"""
        for node in self.graph.nodes.values():
            if math.sqrt((node.x - x)**2 + (node.y - y)**2) <= radius:
                return node
        return None
    
    def find_nearby_node(self, x: float, y: float, radius: float, exclude_id: Optional[int] = None) -> Optional[Node]:
        """Znajduje najbliższy węzeł w określonym promieniu"""
        closest_node = None
        min_distance = radius
        
        for node in self.graph.nodes.values():
            if exclude_id is not None and node.id == exclude_id:
                continue
            distance = math.sqrt((node.x - x)**2 + (node.y - y)**2)
            if distance <= min_distance:
                min_distance = distance
                closest_node = node
        
        return closest_node
    
    def find_nearby_existing_node(self, x: float, y: float, radius: float, exclude_path_nodes: bool = False) -> Optional[Node]:
        """
        Znajduje najbliższy istniejący węzeł w promieniu.
        Jeśli exclude_path_nodes=True, ignoruje węzły które są częścią aktualnie rysowanej ścieżki (P* nodes).
        """
        closest_node = None
        min_distance = radius
        
        # Zbierz wszystkie węzły z aktualnej ścieżki aby ich unikać
        path_node_ids = set()
        if exclude_path_nodes and self.last_path_node:
            # Znajdź wszystkie węzły połączone w aktualnej ścieżce
            current = self.last_path_node
            visited = {current.id}
            
            # Śledź wstecz przez krawędzie oznaczone jako P
            for edge in self.graph.edges:
                n1 = self.graph.nodes.get(edge.node1_id)
                n2 = self.graph.nodes.get(edge.node2_id)
                if n1 and n2:
                    if n1.label.startswith("P") or n2.label.startswith("P"):
                        path_node_ids.add(edge.node1_id)
                        path_node_ids.add(edge.node2_id)
        
        for node in self.graph.nodes.values():
            # Pomiń węzły ścieżki jeśli exclude_path_nodes=True
            if exclude_path_nodes and (node.label.startswith("P") or node.id in path_node_ids):
                continue
            
            # Pomiń ostatni węzeł ścieżki
            if self.last_path_node and node.id == self.last_path_node.id:
                continue
            
            distance = math.sqrt((node.x - x)**2 + (node.y - y)**2)
            if distance < min_distance:  # Zmienione z <= na < dla jednoznaczności
                min_distance = distance
                closest_node = node
        
        return closest_node
    
    def edge_exists(self, node1_id: int, node2_id: int) -> bool:
        """Sprawdza czy krawędź między węzłami już istnieje"""
        for edge in self.graph.edges:
            if (edge.node1_id == node1_id and edge.node2_id == node2_id) or \
               (edge.node1_id == node2_id and edge.node2_id == node1_id):
                return True
        return False
    
    def find_crossing_corridor(self, x1: float, y1: float, x2: float, y2: float) -> Optional[Edge]:
        """Znajduje korytarz (krawędź) który przecina aktualny segment ścieżki"""
        for edge in self.graph.edges:
            node1 = self.graph.nodes[edge.node1_id]
            node2 = self.graph.nodes[edge.node2_id]
            
            # Sprawdź czy linie się przecinają
            if self.lines_intersect(x1, y1, x2, y2, node1.x, node1.y, node2.x, node2.y):
                return edge
        
        return None
    
    def lines_intersect(self, x1: float, y1: float, x2: float, y2: float,
                       x3: float, y3: float, x4: float, y4: float) -> bool:
        """Sprawdza czy dwa odcinki się przecinają"""
        def ccw(ax, ay, bx, by, cx, cy):
            return (cy - ay) * (bx - ax) > (by - ay) * (cx - ax)
        
        # Sprawdź czy odcinki się przecinają
        if ccw(x1, y1, x3, y3, x4, y4) != ccw(x2, y2, x3, y3, x4, y4) and \
           ccw(x1, y1, x2, y2, x3, y3) != ccw(x1, y1, x2, y2, x4, y4):
            return True
        return False
    
    def get_intersection_point(self, x1: float, y1: float, x2: float, y2: float,
                              x3: float, y3: float, x4: float, y4: float) -> Optional[Tuple[float, float]]:
        """Oblicza punkt przecięcia dwóch odcinków"""
        denom = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4)
        
        if abs(denom) < 1e-10:
            return None
        
        t = ((x1 - x3) * (y3 - y4) - (y1 - y3) * (x3 - x4)) / denom
        u = -((x1 - x2) * (y1 - y3) - (y1 - y2) * (x1 - x3)) / denom
        
        if 0 <= t <= 1 and 0 <= u <= 1:
            ix = x1 + t * (x2 - x1)
            iy = y1 + t * (y2 - y1)
            return (ix, iy)
        
        return None
    
    def find_edge_at(self, x: float, y: float, threshold: float = 5) -> Optional[Edge]:
        """Znajduje krawędź w pobliżu punktu (x, y)"""
        for edge in self.graph.edges:
            node1 = self.graph.nodes[edge.node1_id]
            node2 = self.graph.nodes[edge.node2_id]
            
            # Oblicz odległość punktu od linii
            dist = self.point_to_line_distance(x, y, node1.x, node1.y, node2.x, node2.y)
            if dist <= threshold:
                return edge
        return None
    
    def find_edge_crossing(self, x1: float, y1: float, x2: float, y2: float, 
                          min_edge_length: float = 50) -> Optional[Tuple[Edge, Tuple[float, float]]]:
        """Znajduje krawędź którą przecina segment (x1,y1)-(x2,y2)
        Zwraca (edge, punkt_przecięcia) lub None
        min_edge_length - minimalna długość krawędzi aby utworzyć skrzyżowanie
        """
        for edge in self.graph.edges:
            node1 = self.graph.nodes.get(edge.node1_id)
            node2 = self.graph.nodes.get(edge.node2_id)
            
            if not node1 or not node2:
                continue
            
            # Sprawdź długość krawędzi - tylko długie krawędzie
            edge_length = math.sqrt((node2.x - node1.x)**2 + (node2.y - node1.y)**2)
            if edge_length < min_edge_length:
                continue
            
            # Nie sprawdzaj krawędzi które mają wspólny węzeł z naszym segmentem
            if edge.node1_id == self.last_path_node.id or edge.node2_id == self.last_path_node.id:
                continue
            
            # Sprawdź czy linie się przecinają
            if self.lines_intersect(x1, y1, x2, y2, node1.x, node1.y, node2.x, node2.y):
                # Oblicz punkt przecięcia
                intersection = self.get_intersection_point(x1, y1, x2, y2, 
                                                          node1.x, node1.y, node2.x, node2.y)
                if intersection:
                    # Sprawdź czy punkt przecięcia nie jest za blisko istniejących węzłów
                    ix, iy = intersection
                    too_close = False
                    for node in [node1, node2]:
                        dist = math.sqrt((ix - node.x)**2 + (iy - node.y)**2)
                        if dist < 20:  # Minimum 20 pikseli od węzłów krawędzi
                            too_close = True
                            break
                    
                    if not too_close:
                        return (edge, intersection)
        
        return None
    
    def point_to_line_distance(self, px, py, x1, y1, x2, y2) -> float:
        """Oblicza odległość punktu od odcinka"""
        dx = x2 - x1
        dy = y2 - y1
        if dx == 0 and dy == 0:
            return math.sqrt((px - x1)**2 + (py - y1)**2)
        
        t = max(0, min(1, ((px - x1) * dx + (py - y1) * dy) / (dx * dx + dy * dy)))
        closest_x = x1 + t * dx
        closest_y = y1 + t * dy
        
        return math.sqrt((px - closest_x)**2 + (py - closest_y)**2)
    
    def closest_point_on_line(self, px, py, x1, y1, x2, y2):
        """Znajduje najbliższy punkt na odcinku i zwraca (point_x, point_y, distance)"""
        dx = x2 - x1
        dy = y2 - y1
        
        if dx == 0 and dy == 0:
            # Linia jest punktem
            distance = math.sqrt((px - x1)**2 + (py - y1)**2)
            return x1, y1, distance
        
        # Parametr t określa pozycję na linii (0 = początek, 1 = koniec)
        t = max(0, min(1, ((px - x1) * dx + (py - y1) * dy) / (dx * dx + dy * dy)))
        
        # Najbliższy punkt na linii
        closest_x = x1 + t * dx
        closest_y = y1 + t * dy
        
        # Odległość od punktu do najbliższego punktu na linii
        distance = math.sqrt((px - closest_x)**2 + (py - closest_y)**2)
        
        return closest_x, closest_y, distance
    
    def draw_node(self, node: Node):
        """Rysuje węzeł na canvas"""
        r = 8
        # Węzły ze ścieżki w innym kolorze
        if node.label.startswith("P"):
            fill_color = "lightgreen"
            outline_color = "darkgreen"
        elif node.label.startswith("X"):
            # Skrzyżowania w kolorze czerwonym
            fill_color = "salmon"
            outline_color = "darkred"
            r = 10  # Większy promień dla skrzyżowań
        else:
            fill_color = "lightblue"
            outline_color = "blue"
            
        oval = self.canvas.create_oval(node.x - r, node.y - r, node.x + r, node.y + r, 
                                       fill=fill_color, outline=outline_color, width=2)
        text = self.canvas.create_text(node.x, node.y - 15, text=node.label, 
                                       font=("Arial", 9), fill="black")
        self.canvas_objects[node.id] = oval
        
    def draw_edge(self, edge: Edge):
        """Rysuje krawędź na canvas"""
        node1 = self.graph.nodes[edge.node1_id]
        node2 = self.graph.nodes[edge.node2_id]
        
        line = self.canvas.create_line(node1.x, node1.y, node2.x, node2.y, 
                                       fill="gray", width=2, arrow=tk.BOTH)
        self.edge_objects.append(line)
        
        # Rysuj wagę w środku krawędzi
        mid_x = (node1.x + node2.x) / 2
        mid_y = (node1.y + node2.y) / 2
        if edge.weight:
            self.canvas.create_text(mid_x, mid_y, text=f"{edge.weight:.1f}", 
                                   font=("Arial", 8), fill="red")
    
    def add_room_at(self, x: float, y: float):
        """Dodaje salę w pobliżu kliknięcia"""
        if len(self.graph.edges) == 0:
            messagebox.showwarning("Brak krawędzi", "Dodaj najpierw krawędzie do grafu, aby móc umieścić sale")
            return
        
        # Znajdź najbliższą krawędź
        closest_edge = None
        min_distance = float('inf')
        closest_point = None
        
        for edge in self.graph.edges:
            node1 = self.graph.nodes.get(edge.node1_id)
            node2 = self.graph.nodes.get(edge.node2_id)
            
            if node1 and node2:
                # Znajdź najbliższy punkt na krawędzi
                point_x, point_y, distance = self.closest_point_on_line(
                    x, y, node1.x, node1.y, node2.x, node2.y
                )
                
                if distance < min_distance:
                    min_distance = distance
                    closest_edge = edge
                    closest_point = (point_x, point_y)
        
        if closest_edge is None or closest_point is None:
            messagebox.showwarning("Brak ścieżek", "Nie znaleziono odpowiedniej krawędzi!")
            return
        
        # Oblicz pozycję sali - 30px prostopadle od krawędzi
        node1 = self.graph.nodes.get(closest_edge.node1_id)
        node2 = self.graph.nodes.get(closest_edge.node2_id)
        
        # Wektor krawędzi
        dx = node2.x - node1.x
        dy = node2.y - node1.y
        length = (dx**2 + dy**2)**0.5
        
        if length > 0:
            # Wektor prostopadły (obrócony o 90 stopni)
            perp_x = -dy / length
            perp_y = dx / length
            
            # Określ którą stronę wybrać (bliższą do kliknięcia)
            offset_dist = 30
            test_x1 = closest_point[0] + perp_x * offset_dist
            test_y1 = closest_point[1] + perp_y * offset_dist
            test_x2 = closest_point[0] - perp_x * offset_dist
            test_y2 = closest_point[1] - perp_y * offset_dist
            
            dist1 = ((x - test_x1)**2 + (y - test_y1)**2)**0.5
            dist2 = ((x - test_x2)**2 + (y - test_y2)**2)**0.5
            
            if dist1 < dist2:
                room_x = test_x1
                room_y = test_y1
            else:
                room_x = test_x2
                room_y = test_y2
            
            # Dodaj salę do listy
            room = {
                "id": f"room_{self.current_floor}_{self.room_counter}",  # Unikalny ID
                "floor": self.current_floor,  # Numer piętra
                "name": f"Sala {self.room_counter}",
                "x": room_x,
                "y": room_y,
                "connection_x": closest_point[0],
                "connection_y": closest_point[1],
                "edge": closest_edge
            }
            self.rooms.append(room)
            self.room_counter += 1
            
            self.redraw()
            self.update_status()
    
    def delete_room_at(self, x: float, y: float) -> bool:
        """Usuwa salę klikniętą myszką"""
        room_size = 15  # Połowa rozmiaru kwadratu sali
        
        for i, room in enumerate(self.rooms):
            # Sprawdź czy kliknięcie jest wewnątrz kwadratu sali
            if (room["x"] - room_size <= x <= room["x"] + room_size and 
                room["y"] - room_size <= y <= room["y"] + room_size):
                self.rooms.pop(i)
                self.redraw()
                self.update_status()
                return True
        return False
    
    def remove_all_rooms(self):
        """Usuwa wszystkie sale"""
        if len(self.rooms) == 0:
            messagebox.showinfo("Brak sal", "Nie ma sal do usunięcia")
            return
            
        if messagebox.askyesno("Usuń sale", f"Czy na pewno chcesz usunąć wszystkie {len(self.rooms)} sal?"):
            self.rooms.clear()
            self.room_counter = 1
            self.redraw()
            self.update_status()
    
    def add_elevator_at(self, x: float, y: float, elevator_type: str):
        """Dodaje windę lub schody w podanym miejscu"""
        if len(self.graph.edges) == 0:
            messagebox.showwarning("Brak krawędzi", "Dodaj najpierw krawędzie do grafu, aby móc umieścić windy/schody")
            return
        
        # Znajdź najbliższą krawędź
        closest_edge = None
        min_distance = float('inf')
        closest_point = None
        
        for edge in self.graph.edges:
            node1 = self.graph.nodes.get(edge.node1_id)
            node2 = self.graph.nodes.get(edge.node2_id)
            
            if node1 and node2:
                # Znajdź najbliższy punkt na krawędzi
                point_x, point_y, distance = self.closest_point_on_line(
                    x, y, node1.x, node1.y, node2.x, node2.y
                )
                
                if distance < min_distance:
                    min_distance = distance
                    closest_edge = edge
                    closest_point = (point_x, point_y)
        
        if closest_edge and closest_point:
            # Oblicz pozycję windy/schodów - 30px prostopadle od krawędzi
            node1 = self.graph.nodes.get(closest_edge.node1_id)
            node2 = self.graph.nodes.get(closest_edge.node2_id)
            
            # Wektor krawędzi
            dx = node2.x - node1.x
            dy = node2.y - node1.y
            length = (dx**2 + dy**2)**0.5
            
            if length > 0:
                # Wektor prostopadły (obrócony o 90 stopni)
                perp_x = -dy / length
                perp_y = dx / length
                
                # Określ którą stronę wybrać (bliższą do kliknięcia)
                offset_dist = 30
                test_x1 = closest_point[0] + perp_x * offset_dist
                test_y1 = closest_point[1] + perp_y * offset_dist
                test_x2 = closest_point[0] - perp_x * offset_dist
                test_y2 = closest_point[1] - perp_y * offset_dist
                
                dist1 = ((x - test_x1)**2 + (y - test_y1)**2)**0.5
                dist2 = ((x - test_x2)**2 + (y - test_y2)**2)**0.5
                
                if dist1 < dist2:
                    elevator_x = test_x1
                    elevator_y = test_y1
                else:
                    elevator_x = test_x2
                    elevator_y = test_y2
                
                # Dodaj windę/schody
                name = f"{'W' if elevator_type == 'elevator' else 'S'}{self.elevator_counter}"
                
                # Sprawdź czy w podobnym miejscu istnieje winda na innym piętrze
                # Jeśli tak, użyj tego samego group_id
                group_id = None
                tolerance = 30
                
                for floor_num, floor_data in self.floors.items():
                    if floor_num == self.current_floor:
                        continue
                    for other_elev in floor_data["elevators"]:
                        if (abs(other_elev["x"] - elevator_x) < tolerance and 
                            abs(other_elev["y"] - elevator_y) < tolerance):
                            group_id = other_elev["group_id"]
                            break
                    if group_id:
                        break
                
                # Jeśli nie znaleziono powiązanej windy, utwórz nowy group_id
                if group_id is None:
                    group_id = str(uuid.uuid4())
                
                elevator = {
                    "id": f"elevator_{self.current_floor}_{self.elevator_counter}",  # Unikalny ID
                    "floor": self.current_floor,  # Numer piętra
                    "group_id": group_id,  # Unikalny ID grupy wind na różnych piętrach
                    "name": name,
                    "type": elevator_type,
                    "x": elevator_x,
                    "y": elevator_y,
                    "connection_x": closest_point[0],
                    "connection_y": closest_point[1],
                    "edge": closest_edge
                }
                
                self.elevators.append(elevator)
                self.elevator_counter += 1
                self.redraw()
                self.update_status()
    
    def delete_elevator_at(self, x: float, y: float) -> bool:
        """Usuwa windę/schody w danym miejscu. Zwraca True jeśli usunięto."""
        click_radius = 20
        for elevator in self.elevators:
            distance = ((x - elevator["x"])**2 + (y - elevator["y"])**2)**0.5
            if distance <= click_radius:
                self.elevators.remove(elevator)
                self.redraw()
                self.update_status()
                return True
        return False
    
    def remove_all_elevators(self):
        """Usuwa wszystkie windy i schody"""
        if len(self.elevators) == 0:
            messagebox.showinfo("Brak wind/schodów", "Nie ma wind ani schodów do usunięcia")
            return
            
        if messagebox.askyesno("Usuń windy/schody", f"Czy na pewno chcesz usunąć wszystkie {len(self.elevators)} wind/schodów?"):
            self.elevators.clear()
            self.elevator_counter = 1
            self.redraw()
            self.update_status()
    
    def show_elevator_preview(self, x: float, y: float, elevator_type: str):
        """Pokazuje podgląd miejsca gdzie zostanie umieszczona winda/schody"""
        # Usuń stary podgląd
        self.canvas.delete("elevator_preview")
        
        if len(self.graph.edges) == 0:
            return
        
        # Znajdź najbliższą krawędź
        closest_edge = None
        min_distance = float('inf')
        closest_point = None
        
        for edge in self.graph.edges:
            node1 = self.graph.nodes.get(edge.node1_id)
            node2 = self.graph.nodes.get(edge.node2_id)
            
            if node1 and node2:
                point_x, point_y, distance = self.closest_point_on_line(
                    x, y, node1.x, node1.y, node2.x, node2.y
                )
                
                if distance < min_distance:
                    min_distance = distance
                    closest_edge = edge
                    closest_point = (point_x, point_y)
        
        if closest_edge and closest_point:
            # Oblicz pozycję podglądu
            node1 = self.graph.nodes.get(closest_edge.node1_id)
            node2 = self.graph.nodes.get(closest_edge.node2_id)
            
            dx = node2.x - node1.x
            dy = node2.y - node1.y
            length = (dx**2 + dy**2)**0.5
            
            if length > 0:
                perp_x = -dy / length
                perp_y = dx / length
                
                offset_dist = 30
                test_x1 = closest_point[0] + perp_x * offset_dist
                test_y1 = closest_point[1] + perp_y * offset_dist
                test_x2 = closest_point[0] - perp_x * offset_dist
                test_y2 = closest_point[1] - perp_y * offset_dist
                
                dist1 = ((x - test_x1)**2 + (y - test_y1)**2)**0.5
                dist2 = ((x - test_x2)**2 + (y - test_y2)**2)**0.5
                
                if dist1 < dist2:
                    preview_x = test_x1
                    preview_y = test_y1
                else:
                    preview_x = test_x2
                    preview_y = test_y2
                
                # Rysuj podgląd
                size = 15
                
                # Linia połączenia (szara przerywana)
                self.canvas.create_line(closest_point[0], closest_point[1],
                                       preview_x, preview_y,
                                       fill="gray", width=2, dash=(5, 3), 
                                       tags="elevator_preview")
                
                # Prostokąt windy/schodów (szary półprzezroczysty)
                color = "lightblue" if elevator_type == "elevator" else "lightgreen"
                self.canvas.create_rectangle(preview_x - size, preview_y - size,
                                            preview_x + size, preview_y + size,
                                            fill=color, outline="gray", width=2,
                                            stipple="gray50", tags="elevator_preview")
                
                # Tekst w środku
                text = "W" if elevator_type == "elevator" else "S"
                self.canvas.create_text(preview_x, preview_y,
                                       text=text,
                                       font=("Arial", 12, "bold"),
                                       fill="black", stipple="gray50",
                                       tags="elevator_preview")
                
                # Czerwona kropka w miejscu połączenia
                self.canvas.create_oval(closest_point[0] - 3, closest_point[1] - 3,
                                       closest_point[0] + 3, closest_point[1] + 3,
                                       fill="red", outline="darkred",
                                       tags="elevator_preview")
    
    def draw_elevator(self, elevator: dict):
        """Rysuje windę lub schody na canvas"""
        size = 15  # Połowa rozmiaru prostokąta
        
        # Rysuj linię połączenia z krawędzią
        self.canvas.create_line(elevator["connection_x"], elevator["connection_y"], 
                               elevator["x"], elevator["y"],
                               fill="purple", width=2, dash=(5, 3), tags="elevator")
        
        # Kolor w zależności od typu
        if elevator["type"] == "elevator":
            fill_color = "lightblue"
            outline_color = "blue"
        else:  # stairs
            fill_color = "lightgreen"
            outline_color = "green"
        
        # Rysuj prostokąt windy/schodów
        self.canvas.create_rectangle(elevator["x"] - size, elevator["y"] - size,
                                     elevator["x"] + size, elevator["y"] + size,
                                     fill=fill_color, outline=outline_color, width=2, tags="elevator")
        
        # Rysuj literę w środku (W dla windy, S dla schodów)
        text = "W" if elevator["type"] == "elevator" else "S"
        self.canvas.create_text(elevator["x"], elevator["y"], 
                               text=text,
                               font=("Arial", 12, "bold"), 
                               fill="black", tags="elevator")
    
    def draw_room(self, room: dict):
        """Rysuje salę na canvas"""
        room_size = 15  # Połowa rozmiaru kwadratu
        
        # Rysuj linię połączenia z krawędzią (ścieżką)
        self.canvas.create_line(room["connection_x"], room["connection_y"], 
                               room["x"], room["y"],
                               fill="orange", width=2, dash=(5, 3), tags="room")
        
        # Rysuj żółty kwadrat sali
        self.canvas.create_rectangle(room["x"] - room_size, room["y"] - room_size,
                                     room["x"] + room_size, room["y"] + room_size,
                                     fill="yellow", outline="orange", width=2, tags="room")
        
        # Rysuj nazwę sali
        self.canvas.create_text(room["x"], room["y"], 
                               text=room["name"],
                               font=("Arial", 9, "bold"), 
                               fill="black", tags="room")
    
    def redraw(self):
        """Przerysowuje cały graf"""
        self.canvas.delete("all")
        self.canvas_objects.clear()
        self.edge_objects.clear()
        
        # Narysuj siatkę najpierw
        self.draw_grid()
        
        # Rysuj sąsiednie piętra z przezroczystością (jako podgląd, bez możliwości edycji)
        sorted_floors = sorted(self.floors.keys())
        current_idx = sorted_floors.index(self.current_floor)
        
        # Piętro niżej
        if self.show_floor_below_var.get() and current_idx > 0:
            floor_below = sorted_floors[current_idx - 1]
            self.draw_floor_ghost(floor_below, "below")
        
        # Piętro wyżej
        if self.show_floor_above_var.get() and current_idx < len(sorted_floors) - 1:
            floor_above = sorted_floors[current_idx + 1]
            self.draw_floor_ghost(floor_above, "above")
        
        # Rysuj aktualne piętro (normalnie, z możliwością edycji)
        # Najpierw rysuj krawędzie
        for edge in self.graph.edges:
            self.draw_edge(edge)
        
        # Potem węzły
        for node in self.graph.nodes.values():
            self.draw_node(node)
        
        # Rysuj sale (Map Editor)
        for room in self.rooms:
            self.draw_room(room)
        
        # Rysuj windy i schody (Map Editor)
        for elevator in self.elevators:
            self.draw_elevator(elevator)
        
        # Podświetl wybrany węzeł
        if self.edge_start_node and self.edge_start_node.id in self.canvas_objects:
            self.canvas.itemconfig(self.canvas_objects[self.edge_start_node.id], fill="yellow")
        
        # Rysuj punkty nawigacji (A i B) oraz trasę
        self.draw_navigation_markers()
    
    def draw_navigation_markers(self):
        """Rysuje markery punktów A, B oraz trasę nawigacji"""
        # Rysuj punkt startowy (A) - zielony
        if self.nav_start_point:
            self.draw_nav_point(self.nav_start_point, "A", "#00FF00")
        
        # Rysuj punkt docelowy (B) - czerwony
        if self.nav_end_point:
            self.draw_nav_point(self.nav_end_point, "B", "#FF0000")
        
        # Rysuj trasę jeśli istnieje
        if self.nav_path:
            self.draw_navigation_path(self.nav_path)
    
    def draw_nav_point(self, point, label, color):
        """Rysuje marker punktu nawigacji (A lub B)"""
        # Tylko jeśli punkt jest na obecnym piętrze
        if point["floor"] != self.current_floor:
            return
        
        # Pobierz współrzędne punktu (tylko sale i windy)
        if point["type"] == "room":
            x, y = point["data"]["x"], point["data"]["y"]
        elif point["type"] == "elevator":
            x, y = point["data"]["x"], point["data"]["y"]
        else:
            return
        
        # Rysuj dużą obwódkę
        r = 25
        self.canvas.create_oval(x - r, y - r, x + r, y + r, 
                               outline=color, width=4, tags="navigation")
        
        # Rysuj etykietę (A lub B)
        self.canvas.create_text(x, y - 35, text=label,
                               font=("Arial", 20, "bold"),
                               fill=color, tags="navigation")
        
        # Rysuj nazwę punktu
        self.canvas.create_text(x, y + 35, text=point["name"],
                               font=("Arial", 10),
                               fill=color, tags="navigation")
    
    def draw_navigation_path(self, path):
        """Rysuje trasę nawigacji przez graf"""
        if not path:
            return
        
        prev_pos = None
        
        for i, step in enumerate(path):
            if step["floor"] != self.current_floor:
                continue
            
            step_type = step.get("type", "")
            
            if step_type == "start":
                # Punkt startowy
                point = step["point"]
                data = point["data"]
                edge = step.get("edge")  # Krawędź do której podłączony jest punkt startowy
                
                if "connection_x" in data and "connection_y" in data:
                    start_pos = (data["connection_x"], data["connection_y"])
                else:
                    start_pos = (data["x"], data["y"])
                
                # Jeśli mamy krawędź, narysuj linię od punktu startowego do najbliższego węzła tej krawędzi
                if edge and i + 1 < len(path):
                    floor_data = self.floors[step["floor"]]
                    graph = floor_data["graph"]
                    
                    # Znajdź węzły krawędzi
                    node1 = graph.nodes.get(edge.node1_id)
                    node2 = graph.nodes.get(edge.node2_id)
                    
                    if node1 and node2:
                        # Znajdź który węzeł jest bliżej punktu startowego
                        dist1 = math.sqrt((node1.x - start_pos[0])**2 + (node1.y - start_pos[1])**2)
                        dist2 = math.sqrt((node2.x - start_pos[0])**2 + (node2.y - start_pos[1])**2)
                        
                        if dist1 < dist2:
                            closest_node_pos = (node1.x, node1.y)
                        else:
                            closest_node_pos = (node2.x, node2.y)
                        
                        # Linia od startu do najbliższego węzła krawędzi (kreskowana)
                        self.canvas.create_line(start_pos[0], start_pos[1],
                                              closest_node_pos[0], closest_node_pos[1],
                                              fill="#00DD00", width=4, 
                                              dash=(8, 4), tags="navigation")
                
                # Mały punkt startowy
                r = 6
                self.canvas.create_oval(start_pos[0] - r, start_pos[1] - r,
                                      start_pos[0] + r, start_pos[1] + r,
                                      fill="#00FF00", outline="#008800",
                                      width=2, tags="navigation")
                
                prev_pos = start_pos
                    
            elif step_type == "node":
                # Węzeł grafu
                node = step["node"]
                edge = step.get("edge")  # Krawędź którą doszliśmy do tego węzła
                current_pos = (node.x, node.y)
                
                # Rysuj linię od poprzedniego punktu wzdłuż krawędzi
                if prev_pos and edge:
                    # Mamy krawędź - rysuj wzdłuż niej
                    floor_data = self.floors[step["floor"]]
                    graph = floor_data["graph"]
                    
                    # Znajdź węzły krawędzi
                    node1 = graph.nodes.get(edge.node1_id)
                    node2 = graph.nodes.get(edge.node2_id)
                    
                    if node1 and node2:
                        # Rysuj linię wzdłuż krawędzi
                        self.canvas.create_line(node1.x, node1.y, node2.x, node2.y,
                                              fill="#00DD00", width=6, tags="navigation",
                                              capstyle=tk.ROUND, smooth=True)
                elif prev_pos:
                    # Brak krawędzi - rysuj prostą linię (fallback)
                    self.canvas.create_line(prev_pos[0], prev_pos[1],
                                          current_pos[0], current_pos[1],
                                          fill="#00DD00", width=6, tags="navigation",
                                          capstyle=tk.ROUND, smooth=True)
                
                # Podświetl węzeł
                r = 7
                self.canvas.create_oval(node.x - r, node.y - r, 
                                      node.x + r, node.y + r,
                                      fill="#00FF00", outline="#008800", 
                                      width=2, tags="navigation")
                
                prev_pos = current_pos
                
            elif step_type == "elevator_enter":
                # Wejście do windy
                elevator = step["elevator"]
                
                if "connection_x" in elevator and "connection_y" in elevator:
                    elev_conn = (elevator["connection_x"], elevator["connection_y"])
                else:
                    elev_conn = (elevator["x"], elevator["y"])
                
                # Linia do punktu połączenia windy
                if prev_pos:
                    self.canvas.create_line(prev_pos[0], prev_pos[1],
                                          elev_conn[0], elev_conn[1],
                                          fill="#00DD00", width=6, tags="navigation",
                                          capstyle=tk.ROUND)
                
                # Linia do samej windy (jeśli connection != pozycja windy)
                if elev_conn != (elevator["x"], elevator["y"]):
                    self.canvas.create_line(elev_conn[0], elev_conn[1],
                                          elevator["x"], elevator["y"],
                                          fill="#00DD00", width=4, dash=(8, 4),
                                          tags="navigation")
                
                # Podświetl windę
                size = 22
                elev_color = "#FF8800" if elevator["type"] == "elevator" else "#8800FF"
                self.canvas.create_rectangle(elevator["x"] - size, elevator["y"] - size,
                                            elevator["x"] + size, elevator["y"] + size,
                                            outline=elev_color, width=6, 
                                            tags="navigation")
                
                # Duża ikona
                icon = "�" if elevator["type"] == "elevator" else "🚶"
                self.canvas.create_text(elevator["x"], elevator["y"],
                                      text=icon, font=("Arial", 20),
                                      tags="navigation")
                
                prev_pos = None  # Reset dla nowego piętra
                
            elif step_type == "elevator_exit":
                # Wyjście z windy na nowym piętrze
                elevator = step["elevator"]
                
                if "connection_x" in elevator and "connection_y" in elevator:
                    prev_pos = (elevator["connection_x"], elevator["connection_y"])
                else:
                    prev_pos = (elevator["x"], elevator["y"])
                
            elif step_type == "end":
                # Punkt końcowy
                point = step["point"]
                data = point["data"]
                edge = step.get("edge")  # Krawędź do której podłączony jest punkt końcowy
                
                if "connection_x" in data and "connection_y" in data:
                    end_pos = (data["connection_x"], data["connection_y"])
                else:
                    end_pos = (data["x"], data["y"])
                
                # Linia do punktu końcowego - wzdłuż krawędzi jeśli dostępna
                if prev_pos and edge:
                    # Mamy krawędź - rysuj wzdłuż niej
                    floor_data = self.floors[step["floor"]]
                    graph = floor_data["graph"]
                    
                    # Znajdź węzły krawędzi
                    node1 = graph.nodes.get(edge.node1_id)
                    node2 = graph.nodes.get(edge.node2_id)
                    
                    if node1 and node2:
                        # Rysuj linię wzdłuż krawędzi ze strzałką
                        self.canvas.create_line(node1.x, node1.y, node2.x, node2.y,
                                              fill="#00DD00", width=6, 
                                              tags="navigation", capstyle=tk.ROUND, smooth=True)
                        
                        # Dodaj strzałkę od ostatniego węzła do punktu końcowego
                        # Znajdź który węzeł jest bliżej punktu końcowego
                        dist1 = math.sqrt((node1.x - end_pos[0])**2 + (node1.y - end_pos[1])**2)
                        dist2 = math.sqrt((node2.x - end_pos[0])**2 + (node2.y - end_pos[1])**2)
                        
                        if dist1 < dist2:
                            closest_node_pos = (node1.x, node1.y)
                        else:
                            closest_node_pos = (node2.x, node2.y)
                        
                        # Linia ze strzałką od węzła do punktu końcowego
                        self.canvas.create_line(closest_node_pos[0], closest_node_pos[1],
                                              end_pos[0], end_pos[1],
                                              fill="#00DD00", width=4, 
                                              arrow=tk.LAST, arrowshape=(16, 20, 6),
                                              dash=(8, 4), tags="navigation")
                elif prev_pos:
                    # Brak krawędzi - rysuj prostą linię (fallback)
                    self.canvas.create_line(prev_pos[0], prev_pos[1],
                                          end_pos[0], end_pos[1],
                                          fill="#00DD00", width=6, 
                                          arrow=tk.LAST, arrowshape=(16, 20, 6),
                                          tags="navigation", capstyle=tk.ROUND)
                
                # Punkt końcowy
                r = 6
                self.canvas.create_oval(end_pos[0] - r, end_pos[1] - r,
                                      end_pos[0] + r, end_pos[1] + r,
                                      fill="#FF0000", outline="#880000",
                                      width=2, tags="navigation")
    
    def get_point_coordinates(self, point):
        """Pobiera współrzędne punktu (tylko sale i windy)"""
        if point["type"] == "room":
            return point["data"]["x"], point["data"]["y"]
        elif point["type"] == "elevator":
            return point["data"]["x"], point["data"]["y"]
        return 0, 0
    
    def draw_floor_ghost(self, floor_num: int, position: str):
        """Rysuje piętro jako podgląd (ghost) z przezroczystością"""
        floor_data = self.floors[floor_num]
        graph = floor_data['graph']
        
        # Kolor w zależności od pozycji
        if position == "below":
            color = "#FFB6C1"  # Jasny różowy dla piętra niżej
            stipple = "gray50"
        else:  # above
            color = "#ADD8E6"  # Jasny niebieski dla piętra wyżej
            stipple = "gray50"
        
        # Rysuj krawędzie
        for edge in graph.edges:
            node1 = graph.nodes.get(edge.node1_id)
            node2 = graph.nodes.get(edge.node2_id)
            if node1 and node2:
                self.canvas.create_line(node1.x, node1.y, node2.x, node2.y, 
                                       fill=color, width=1, dash=(3, 3), 
                                       stipple=stipple, tags="ghost")
        
        # Rysuj węzły
        for node in graph.nodes.values():
            r = 5
            self.canvas.create_oval(node.x - r, node.y - r, node.x + r, node.y + r, 
                                   fill=color, outline=color, 
                                   stipple=stipple, tags="ghost")
        
        # Rysuj sale jako małe kwadraty
        for room in floor_data['rooms']:
            room_size = 10
            self.canvas.create_rectangle(room["x"] - room_size, room["y"] - room_size,
                                         room["x"] + room_size, room["y"] + room_size,
                                         fill=color, outline=color, 
                                         stipple=stipple, tags="ghost")
        
        # Rysuj windy/schody - ważne dla połączeń między piętrami!
        for elevator in floor_data['elevators']:
            size = 12
            elev_color = "#FF69B4" if position == "below" else "#4169E1"  # Wyraźniejsze kolory dla wind
            self.canvas.create_rectangle(elevator["x"] - size, elevator["y"] - size,
                                         elevator["x"] + size, elevator["y"] + size,
                                         fill=elev_color, outline=elev_color, width=2,
                                         stipple=stipple, tags="ghost")
            
            # Dodaj etykietę windy/schodów
            text = "W" if elevator["type"] == "elevator" else "S"
            self.canvas.create_text(elevator["x"], elevator["y"], 
                                   text=text,
                                   font=("Arial", 8, "bold"), 
                                   fill="black", stipple=stipple,
                                   tags="ghost")
    
    def update_info(self):
        """Aktualizuje panel informacji (usunięty - teraz używamy tooltipów)"""
        pass
    
    
    def rename_node(self, node: Node):
        """Zmienia etykietę węzła"""
        new_label = simpledialog.askstring("Zmień etykietę", 
                                          f"Nowa etykieta dla {node.label}:", 
                                          initialvalue=node.label,
                                          parent=self.root)
        if new_label:
            node.label = new_label
            self.redraw()
            self.update_info()
    
    def delete_node(self, node: Node):
        """Usuwa węzeł"""
        self.graph.remove_node(node.id)
        self.redraw()
        self.update_status()
        self.update_info()
    
    def new_graph(self):
        """Tworzy nowy graf"""
        if len(self.graph.nodes) > 0:
            if not messagebox.askyesno("Nowy graf", "Czy na pewno chcesz utworzyć nowy graf? Niezapisane zmiany zostaną utracone."):
                return
        
        name = simpledialog.askstring("Nowy graf", "Nazwa nowego grafu:", parent=self.root)
        if name:
            self.graph = Graph(name)
            self.redraw()
            self.update_status()
            self.update_info()
    
    def save_graph(self):
        """Zapisuje całą mapę budynku (wszystkie piętra) do pliku JSON"""
        filename = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if filename:
            try:
                # Przygotuj dane wszystkich pięter
                floors_data = {}
                
                for floor_num, floor_data in self.floors.items():
                    # Skopiuj rooms i elevators, konwertując obiekty Edge na słowniki
                    rooms_data = []
                    for room in floor_data["rooms"]:
                        room_dict = room.copy()
                        # Konwertuj obiekt Edge na słownik
                        if "edge" in room_dict and hasattr(room_dict["edge"], 'to_dict'):
                            room_dict["edge"] = room_dict["edge"].to_dict()
                        elif "edge" in room_dict and room_dict["edge"] is None:
                            room_dict["edge"] = None
                        rooms_data.append(room_dict)
                    
                    elevators_data = []
                    for elevator in floor_data["elevators"]:
                        elevator_dict = elevator.copy()
                        # Konwertuj obiekt Edge na słownik
                        if "edge" in elevator_dict and hasattr(elevator_dict["edge"], 'to_dict'):
                            elevator_dict["edge"] = elevator_dict["edge"].to_dict()
                        elif "edge" in elevator_dict and elevator_dict["edge"] is None:
                            elevator_dict["edge"] = None
                        elevators_data.append(elevator_dict)
                    
                    floors_data[str(floor_num)] = {
                        "graph": floor_data["graph"].to_dict(),
                        "rooms": rooms_data,
                        "elevators": elevators_data,
                        "room_counter": floor_data["room_counter"],
                        "elevator_counter": floor_data["elevator_counter"]
                    }
                
                data = {
                    "version": "2.0",  # Wersja z obsługą wielu pięter
                    "current_floor": self.current_floor,
                    "floors": floors_data
                }
                
                with open(filename, 'w', encoding='utf-8') as f:
                    json.dump(data, f, indent=2, ensure_ascii=False)
                messagebox.showinfo("Zapisano", f"Zapisano mapę budynku ({len(self.floors)} pięter) do {filename}")
            except Exception as e:
                messagebox.showerror("Błąd", f"Nie udało się zapisać mapy: {e}")
    
    def load_graph(self):
        """Wczytuje mapę budynku z pliku JSON"""
        filename = filedialog.askopenfilename(
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if filename:
            try:
                with open(filename, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                
                # Sprawdź wersję formatu
                if "version" in data and data["version"] == "2.0":
                    # Nowy format z wieloma piętrami
                    self.floors = {}
                    
                    for floor_num_str, floor_data in data["floors"].items():
                        floor_num = int(floor_num_str)
                        
                        # Wczytaj graf
                        graph = Graph.from_dict(floor_data["graph"])
                        
                        # Wczytaj rooms i przywróć obiekty Edge
                        rooms = []
                        for room_data in floor_data.get("rooms", []):
                            room = room_data.copy()
                            # Dodaj id i floor jeśli nie istnieją (stare pliki)
                            if "id" not in room:
                                room["id"] = f"room_{floor_num}_{len(rooms) + 1}"
                            if "floor" not in room:
                                room["floor"] = floor_num
                            # Migruj connected_edge na edge
                            if "connected_edge" in room:
                                room["edge"] = Edge.from_dict(room["connected_edge"]) if room["connected_edge"] else None
                                del room["connected_edge"]
                            elif "edge" in room and room["edge"]:
                                room["edge"] = Edge.from_dict(room["edge"])
                            rooms.append(room)
                        
                        # Wczytaj elevators i przywróć obiekty Edge
                        elevators = []
                        for elevator_data in floor_data.get("elevators", []):
                            elevator = elevator_data.copy()
                            # Dodaj id i floor jeśli nie istnieją (stare pliki)
                            if "id" not in elevator or not isinstance(elevator["id"], str):
                                elevator["id"] = f"elevator_{floor_num}_{len(elevators) + 1}"
                            if "floor" not in elevator:
                                elevator["floor"] = floor_num
                            if "edge" in elevator and elevator["edge"]:
                                elevator["edge"] = Edge.from_dict(elevator["edge"])
                            # Dodaj group_id jeśli nie istnieje (stare pliki)
                            if "group_id" not in elevator:
                                elevator["group_id"] = str(uuid.uuid4())
                            elevators.append(elevator)
                        
                        self.floors[floor_num] = {
                            "graph": graph,
                            "rooms": rooms,
                            "elevators": elevators,
                            "room_counter": floor_data.get("room_counter", 1),
                            "elevator_counter": floor_data.get("elevator_counter", 1)
                        }
                    
                    self.current_floor = data.get("current_floor", 0)
                    
                    # Jeśli brak aktualnego piętra w danych, użyj pierwszego dostępnego
                    if self.current_floor not in self.floors:
                        self.current_floor = sorted(self.floors.keys())[0]
                    
                    messagebox.showinfo("Wczytano", f"Wczytano mapę budynku ({len(self.floors)} pięter)")
                    
                elif "graph" in data:
                    # Stary format v1.0 - jedno piętro z roomami i elevators
                    self.floors = {}
                    self.current_floor = 0
                    
                    graph = Graph.from_dict(data["graph"])
                    
                    # Wczytaj rooms i przywróć obiekty Edge
                    rooms = []
                    for room_data in data.get("rooms", []):
                        room = room_data.copy()
                        # Dodaj id i floor jeśli nie istnieją (stare pliki)
                        if "id" not in room:
                            room["id"] = f"room_0_{len(rooms) + 1}"
                        if "floor" not in room:
                            room["floor"] = 0
                        # Migruj connected_edge na edge
                        if "connected_edge" in room:
                            room["edge"] = Edge.from_dict(room["connected_edge"]) if room["connected_edge"] else None
                            del room["connected_edge"]
                        elif "edge" in room and room["edge"]:
                            room["edge"] = Edge.from_dict(room["edge"])
                        rooms.append(room)
                    
                    # Wczytaj elevators i przywróć obiekty Edge
                    elevators = []
                    for elevator_data in data.get("elevators", []):
                        elevator = elevator_data.copy()
                        # Dodaj id i floor jeśli nie istnieją (stare pliki)
                        if "id" not in elevator or not isinstance(elevator["id"], str):
                            elevator["id"] = f"elevator_0_{len(elevators) + 1}"
                        if "floor" not in elevator:
                            elevator["floor"] = 0
                        if "edge" in elevator and elevator["edge"]:
                            elevator["edge"] = Edge.from_dict(elevator["edge"])
                        # Dodaj group_id jeśli nie istnieje (stare pliki)
                        if "group_id" not in elevator:
                            elevator["group_id"] = str(uuid.uuid4())
                        elevators.append(elevator)
                    
                    self.floors[0] = {
                        "graph": graph,
                        "rooms": rooms,
                        "elevators": elevators,
                        "room_counter": data.get("room_counter", 1),
                        "elevator_counter": data.get("elevator_counter", 1)
                    }
                    
                    messagebox.showinfo("Wczytano", f"Wczytano starszy format mapy (1 piętro)")
                    
                else:
                    # Najstarszy format - tylko graf
                    self.floors = {}
                    self.current_floor = 0
                    
                    self.floors[0] = {
                        "graph": Graph.from_dict(data),
                        "rooms": [],
                        "elevators": [],
                        "room_counter": 1,
                        "elevator_counter": 1
                    }
                    
                    messagebox.showinfo("Wczytano", f"Wczytano starszy format grafu")
                
                self.redraw()
                self.update_status()
                self.update_info()
                
            except Exception as e:
                messagebox.showerror("Błąd", f"Nie udało się wczytać mapy: {e}")
    
    def merge_graphs(self):
        """Łączy aktualny graf z innym grafem"""
        filename = filedialog.askopenfilename(
            title="Wybierz graf do połączenia",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        if filename:
            try:
                with open(filename, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                other_graph = Graph.from_dict(data)
                
                # Przesuń drugi graf w prawo
                offset_x = 200
                offset_y = 0
                
                self.graph.merge_with(other_graph, offset_x, offset_y)
                self.redraw()
                self.update_status()
                self.update_info()
                messagebox.showinfo("Połączono", f"Graf połączono z {other_graph.name}")
            except Exception as e:
                messagebox.showerror("Błąd", f"Nie udało się połączyć grafów: {e}")
    
    def rename_graph(self):
        """Zmienia nazwę grafu"""
        new_name = simpledialog.askstring("Zmień nazwę", 
                                         "Nowa nazwa grafu:", 
                                         initialvalue=self.graph.name,
                                         parent=self.root)
        if new_name:
            self.graph.name = new_name
            self.update_info()
    
    def clear_graph(self):
        """Czyści graf"""
        if messagebox.askyesno("Wyczyść graf", "Czy na pewno chcesz usunąć wszystkie węzły i krawędzie?"):
            self.graph.nodes.clear()
            self.graph.edges.clear()
            self.redraw()
            self.update_status()
            self.update_info()
    
    def generate_grid(self):
        """Generuje siatkę węzłów"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Generuj siatkę")
        dialog.geometry("300x200")
        
        ttk.Label(dialog, text="Liczba kolumn:").pack(pady=5)
        cols_var = tk.IntVar(value=5)
        ttk.Spinbox(dialog, from_=2, to=20, textvariable=cols_var).pack()
        
        ttk.Label(dialog, text="Liczba wierszy:").pack(pady=5)
        rows_var = tk.IntVar(value=5)
        ttk.Spinbox(dialog, from_=2, to=20, textvariable=rows_var).pack()
        
        ttk.Label(dialog, text="Odstęp:").pack(pady=5)
        spacing_var = tk.IntVar(value=50)
        ttk.Spinbox(dialog, from_=20, to=100, textvariable=spacing_var).pack()
        
        def create_grid():
            cols = cols_var.get()
            rows = rows_var.get()
            spacing = spacing_var.get()
            
            start_x = 50
            start_y = 50
            
            for row in range(rows):
                for col in range(cols):
                    x = start_x + col * spacing
                    y = start_y + row * spacing
                    self.graph.add_node(x, y, f"R{row}C{col}")
            
            self.redraw()
            self.update_status()
            self.update_info()
            dialog.destroy()
        
        ttk.Button(dialog, text="Generuj", command=create_grid).pack(pady=20)
    
    def auto_connect(self):
        """Automatycznie łączy najbliższe węzły"""
        max_distance = simpledialog.askfloat("Auto-połącz", 
                                            "Maksymalna odległość połączenia:", 
                                            initialvalue=100,
                                            parent=self.root)
        if max_distance:
            nodes_list = list(self.graph.nodes.values())
            for i, node1 in enumerate(nodes_list):
                for node2 in nodes_list[i+1:]:
                    distance = node1.distance_to(node2)
                    if distance <= max_distance:
                        self.graph.add_edge(node1.id, node2.id)
            
            self.redraw()
            self.update_status()
            self.update_info()
            messagebox.showinfo("Auto-połączenie", f"Dodano połączenia dla węzłów w odległości do {max_distance}")
    
    def update_path_threshold(self):
        """Aktualizuje próg odległości dla symulacji ścieżki"""
        self.path_threshold = self.path_threshold_var.get()
    
    def update_merge_radius(self):
        """Aktualizuje promień łączenia węzłów"""
        self.merge_radius = self.merge_radius_var.get()
    
    def set_grid_size(self):
        """Ustawia rozmiar siatki przez okno dialogowe"""
        new_size = simpledialog.askinteger("Rozmiar siatki", 
                                          "Podaj rozmiar siatki (10-100 px):",
                                          initialvalue=self.grid_size,
                                          minvalue=10,
                                          maxvalue=100,
                                          parent=self.root)
        if new_size:
            self.grid_size = new_size
            if self.show_grid:
                self.draw_grid()
    
    def set_path_threshold(self):
        """Ustawia próg ścieżki przez okno dialogowe"""
        new_threshold = simpledialog.askinteger("Próg ścieżki",
                                               "Podaj próg odległości dla tworzenia nowego węzła (10-100 px):",
                                               initialvalue=self.path_threshold,
                                               minvalue=10,
                                               maxvalue=100,
                                               parent=self.root)
        if new_threshold:
            self.path_threshold = new_threshold
            messagebox.showinfo("Próg ścieżki", f"Próg ścieżki ustawiony na {new_threshold} px")
    
    def set_merge_radius(self):
        """Ustawia promień łączenia przez okno dialogowe"""
        new_radius = simpledialog.askinteger("Promień łączenia",
                                            "Podaj promień do wykrywania pobliskich węzłów (20-100 px):",
                                            initialvalue=self.merge_radius,
                                            minvalue=20,
                                            maxvalue=100,
                                            parent=self.root)
        if new_radius:
            self.merge_radius = new_radius
            messagebox.showinfo("Promień łączenia", f"Promień łączenia ustawiony na {new_radius} px")
    
    def clear_path(self):
        """Czyści dane ścieżki"""
        self.path_points = []
        self.is_simulating = False
        self.last_path_node = None
        self.clear_path_preview()
    
    def clear_path_preview(self):
        """Czyści podgląd ścieżki z canvas"""
        if self.path_line:
            self.canvas.delete(self.path_line)
            self.path_line = None
        self.canvas.delete("path_preview")
    
    def remove_path_nodes(self):
        """Usuwa wszystkie węzły utworzone przez symulację ścieżki"""
        if messagebox.askyesno("Usuń węzły ścieżki", 
                              "Czy na pewno chcesz usunąć wszystkie węzły utworzone przez symulację przejścia?"):
            path_nodes = [node_id for node_id, node in self.graph.nodes.items() 
                         if node.label.startswith("P")]
            for node_id in path_nodes:
                self.graph.remove_node(node_id)
            
            self.redraw()
            self.update_status()
            self.update_info()
            messagebox.showinfo("Usunięto", f"Usunięto {len(path_nodes)} węzłów ścieżki")
    
    def optimize_crossings(self):
        """Optymalizuje skrzyżowania - łączy bardzo bliskie węzły"""
        merged_count = self.auto_merge_nearby_nodes(self.merge_radius)
        
        self.redraw()
        self.update_status()
        self.update_info()
        messagebox.showinfo("Optymalizacja", f"Scalono {merged_count} par bliskich węzłów")
    
    def merge_parallel_edges(self) -> int:
        """
        Znajduje i merguje równoległe krawędzie - jeśli nowa ścieżka jest bardzo bliska istniejącej,
        merguje węzły zamiast tworzyć duplikaty.
        """
        merged_count = 0
        
        # Przejdź przez wszystkie krawędzie z węzłami ścieżki (P*)
        path_edges = [e for e in self.graph.edges 
                      if any(self.graph.nodes[nid].label.startswith("P") 
                            for nid in [e.node1_id, e.node2_id])]
        
        for path_edge in path_edges:
            path_node1 = self.graph.nodes.get(path_edge.node1_id)
            path_node2 = self.graph.nodes.get(path_edge.node2_id)
            
            if not path_node1 or not path_node2:
                continue
            
            # Szukaj istniejących krawędzi które są równoległe
            for existing_edge in self.graph.edges:
                if existing_edge == path_edge:
                    continue
                
                exist_node1 = self.graph.nodes.get(existing_edge.node1_id)
                exist_node2 = self.graph.nodes.get(existing_edge.node2_id)
                
                if not exist_node1 or not exist_node2:
                    continue
                
                # Sprawdź czy krawędzie są równoległe i blisko siebie
                if self.are_edges_parallel(path_node1, path_node2, exist_node1, exist_node2):
                    # Merguj węzły path_edge do exist_edge
                    # Znajdź najbliższe pary
                    pairs = [
                        (path_node1, exist_node1, path_node1.distance_to(exist_node1)),
                        (path_node1, exist_node2, path_node1.distance_to(exist_node2)),
                        (path_node2, exist_node1, path_node2.distance_to(exist_node1)),
                        (path_node2, exist_node2, path_node2.distance_to(exist_node2))
                    ]
                    pairs.sort(key=lambda p: p[2])
                    
                    # Merguj najbliższe pary
                    first_pair = pairs[0]
                    if first_pair[2] < self.merge_radius:
                        self.merge_two_nodes(first_pair[1], first_pair[0])  # Zachowaj istniejący
                        merged_count += 1
                        
                        # Spróbuj zmergować drugi koniec
                        remaining_pairs = [p for p in pairs if p[0] != first_pair[0] and p[1] != first_pair[1]]
                        if remaining_pairs:
                            second_pair = min(remaining_pairs, key=lambda p: p[2])
                            if second_pair[2] < self.merge_radius:
                                # Sprawdź czy węzły nadal istnieją
                                if (second_pair[0].id in self.graph.nodes and 
                                    second_pair[1].id in self.graph.nodes):
                                    self.merge_two_nodes(second_pair[1], second_pair[0])
                                    merged_count += 1
                        
                        break
        
        return merged_count
    
    def are_edges_parallel(self, p1: Node, p2: Node, e1: Node, e2: Node, 
                          max_distance: float = None, max_angle_diff: float = 20) -> bool:
        """
        Sprawdza czy dwie krawędzie są równoległe (lub prawie równoległe) i blisko siebie.
        
        Args:
            p1, p2: Węzły pierwszej krawędzi (path)
            e1, e2: Węzły drugiej krawędzi (existing)
            max_distance: Maksymalna odległość między krawędziami (domyślnie merge_radius)
            max_angle_diff: Maksymalna różnica kąta w stopniach
        """
        if max_distance is None:
            max_distance = self.merge_radius
        
        # Oblicz wektory kierunkowe
        dx1 = p2.x - p1.x
        dy1 = p2.y - p1.y
        dx2 = e2.x - e1.x
        dy2 = e2.y - e1.y
        
        len1 = math.sqrt(dx1**2 + dy1**2)
        len2 = math.sqrt(dx2**2 + dy2**2)
        
        if len1 < 1 or len2 < 1:
            return False
        
        # Znormalizuj wektory
        dx1, dy1 = dx1/len1, dy1/len1
        dx2, dy2 = dx2/len2, dy2/len2
        
        # Oblicz kąt między wektorami (iloczyn skalarny)
        dot_product = abs(dx1*dx2 + dy1*dy2)  # abs() bo kierunek nie ma znaczenia
        
        # Kąt w stopniach
        angle = math.degrees(math.acos(max(-1, min(1, dot_product))))
        
        # Jeśli kąt > 90°, użyj kąta uzupełniającego
        if angle > 90:
            angle = 180 - angle
        
        if angle > max_angle_diff:
            return False
        
        # Sprawdź odległość między krawędziami
        # Użyj odległości punktu od linii dla obu końców
        dist1 = self.point_to_line_distance(p1.x, p1.y, e1.x, e1.y, e2.x, e2.y)
        dist2 = self.point_to_line_distance(p2.x, p2.y, e1.x, e1.y, e2.x, e2.y)
        dist3 = self.point_to_line_distance(e1.x, e1.y, p1.x, p1.y, p2.x, p2.y)
        dist4 = self.point_to_line_distance(e2.x, e2.y, p1.x, p1.y, p2.x, p2.y)
        
        avg_distance = (dist1 + dist2 + dist3 + dist4) / 4
        
        return avg_distance < max_distance
    
    def auto_merge_nearby_nodes(self, merge_radius: float) -> int:
        """Automatycznie scala węzły które są blisko siebie"""
        merged_count = 0
        
        # Powtarzaj dopóki są węzły do scalenia
        while True:
            nodes_list = list(self.graph.nodes.values())
            merged_this_round = False
            
            for i, node1 in enumerate(nodes_list):
                if node1.id not in self.graph.nodes:
                    continue
                
                for j in range(i + 1, len(nodes_list)):
                    node2 = nodes_list[j]
                    if node2.id not in self.graph.nodes:
                        continue
                    
                    # Sprawdź odległość
                    distance = node1.distance_to(node2)
                    
                    if distance < merge_radius:
                        # Scal te węzły
                        self.merge_two_nodes(node1, node2)
                        merged_count += 1
                        merged_this_round = True
                        break
                
                if merged_this_round:
                    break
            
            if not merged_this_round:
                break
        
        return merged_count
    
    def merge_two_nodes(self, keep_node: Node, remove_node: Node):
        """Scala dwa węzły - zachowuje keep_node, usuwa remove_node"""
        if keep_node.id == remove_node.id:
            return  # Nie merguj tego samego węzła
        
        # Sprawdź czy oba węzły nadal istnieją
        if keep_node.id not in self.graph.nodes or remove_node.id not in self.graph.nodes:
            return
        
        # Przenieś keep_node do średniej pozycji
        keep_node.x = (keep_node.x + remove_node.x) / 2
        keep_node.y = (keep_node.y + remove_node.y) / 2
        
        # Zbierz wszystkie krawędzie do aktualizacji (kopiujemy listę aby bezpiecznie modyfikować)
        edges_to_remove = []
        edges_to_add = []
        
        for edge in list(self.graph.edges):  # list() tworzy kopię
            if edge.node1_id == remove_node.id or edge.node2_id == remove_node.id:
                # Ta krawędź jest połączona z usuwanym węzłem
                other_id = edge.node2_id if edge.node1_id == remove_node.id else edge.node1_id
                
                # Nie twórz krawędzi do samego siebie
                if other_id == keep_node.id:
                    edges_to_remove.append(edge)
                    continue
                
                # Sprawdź czy już nie ma takiej krawędzi między keep_node a other_id
                if not self.edge_exists(keep_node.id, other_id):
                    edges_to_add.append((keep_node.id, other_id))
                
                edges_to_remove.append(edge)
        
        # Usuń stare krawędzie
        for edge in edges_to_remove:
            if edge in self.graph.edges:
                self.graph.edges.remove(edge)
        
        # Dodaj nowe krawędzie
        for node1_id, node2_id in edges_to_add:
            self.graph.add_edge(node1_id, node2_id)
        
        # Zmień etykietę jeśli to skrzyżowanie
        if not keep_node.label.startswith("X"):
            keep_connections = len([e for e in self.graph.edges 
                                  if e.node1_id == keep_node.id or e.node2_id == keep_node.id])
            
            if keep_connections > 2:
                # To prawdopodobnie skrzyżowanie
                x_count = len([n for n in self.graph.nodes.values() if n.label.startswith('X')])
                keep_node.label = f"X{x_count + 1}"
        
        # Usuń węzeł
        if remove_node.id in self.graph.nodes:
            del self.graph.nodes[remove_node.id]
    
    def simplify_paths(self):
        """Upraszcza ścieżki - usuwa węzły które leżą prawie na prostej między sąsiadami"""
        
        # KROK 1: Oznacz ważne węzły (zakręty i skrzyżowania)
        important_nodes = set()
        max_distance_from_line = 15  # Piksele - maksymalna odległość od linii prostej
        
        for node in self.graph.nodes.values():
            # Znajdź sąsiadów
            connected_edges = [e for e in self.graph.edges 
                             if e.node1_id == node.id or e.node2_id == node.id]
            
            # Skrzyżowanie lub punkt końcowy = zawsze ważne
            if len(connected_edges) != 2:
                important_nodes.add(node.id)
                continue
            
            # Sprawdź czy węzeł leży na prostej między sąsiadami
            edge1, edge2 = connected_edges
            neighbor1_id = edge1.node2_id if edge1.node1_id == node.id else edge1.node1_id
            neighbor2_id = edge2.node2_id if edge2.node1_id == node.id else edge2.node1_id
            
            neighbor1 = self.graph.nodes.get(neighbor1_id)
            neighbor2 = self.graph.nodes.get(neighbor2_id)
            
            if neighbor1 and neighbor2:
                # Oblicz odległość węzła od linii między sąsiadami
                distance = self.point_to_line_distance(
                    node.x, node.y,
                    neighbor1.x, neighbor1.y,
                    neighbor2.x, neighbor2.y
                )
                
                # Jeśli węzeł jest daleko od linii prostej = to zakręt
                if distance > max_distance_from_line:
                    important_nodes.add(node.id)
        
        # KROK 2: Usuń wszystkie węzły które NIE są ważne
        nodes_to_remove = []
        for node in self.graph.nodes.values():
            if node.id not in important_nodes:
                # Sprawdź czy ma dokładnie 2 połączenia
                connected_edges = [e for e in self.graph.edges 
                                 if e.node1_id == node.id or e.node2_id == node.id]
                
                if len(connected_edges) == 2:
                    nodes_to_remove.append(node)
        
        # KROK 3: Usuń nieważne węzły i połącz ich sąsiadów
        removed_count = 0
        for node in nodes_to_remove:
            # Znajdź sąsiadów
            connected_edges = [e for e in self.graph.edges 
                             if e.node1_id == node.id or e.node2_id == node.id]
            
            if len(connected_edges) == 2:
                edge1, edge2 = connected_edges
                neighbor1_id = edge1.node2_id if edge1.node1_id == node.id else edge1.node1_id
                neighbor2_id = edge2.node2_id if edge2.node1_id == node.id else edge2.node1_id
                
                # Usuń węzeł
                self.graph.remove_node(node.id)
                
                # Połącz sąsiadów jeśli oba istnieją
                if neighbor1_id in self.graph.nodes and neighbor2_id in self.graph.nodes:
                    if not self.edge_exists(neighbor1_id, neighbor2_id):
                        self.graph.add_edge(neighbor1_id, neighbor2_id)
                
                removed_count += 1
        
        self.redraw()
        self.update_status()
        self.update_info()
        messagebox.showinfo("Uproszczono", 
                          f"Znaleziono {len(important_nodes)} kluczowych węzłów\n"
                          f"(zakręty i skrzyżowania)\n\n"
                          f"Usunięto {removed_count} węzłów na prostych\n"
                          f"Pozostało {len(self.graph.nodes)} węzłów")


def main():
    root = tk.Tk()
    app = GraphEditorApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
