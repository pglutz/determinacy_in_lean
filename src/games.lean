import tactic
import prefixes

class game (α : Type*):=
(players : Type*)
(turn : (list α) → players)

variables {α : Type*}

class quasi_strategy (G : game α) :=
(player : G.players)
(positions : set (list α))
(is_quasi_strategy : ∀ t : list α, t ∈ positions →
  (G.turn(t) = player → ∃ a, t.concat a ∈ positions) ∧
  (G.turn(t) ≠ player → ∀ a, t.concat a ∈ positions))

variables {G : game α} (σ : quasi_strategy G) (X : (ℕ → α) → G.players) 
  (s : list α) (f : ℕ → α)

def s_quasi_strategy :=
  s ∈ σ.positions ∧ ∀ t ∈ σ.positions, s <+: t

lemma s_in_s_quasi_strategy (h : s_quasi_strategy σ s) : s ∈ σ.positions := h.left

def is_strategy :=
  ∀ t : list α, t ∈ σ.positions → 
  (G.turn(t) = σ.player → ∃! a, t.concat a ∈ σ.positions)

def is_play := ∃ N, ∀ n ≥ N, stream_prefix f n ∈ σ.positions

def is_winning := ∀ f : ℕ → α, is_play σ f → X f = σ.player

def is_s_winning := s_quasi_strategy σ s ∧ is_winning σ X

def quasi_determined := ∃ σ : quasi_strategy G, is_s_winning σ X s 

def determined := ∃ σ : quasi_strategy G, 
  is_s_winning σ X s ∧ is_strategy σ

variables (p : G.players)

def winning_position := ∃ σ : quasi_strategy G, 
  is_s_winning σ X s ∧ σ.player = p

variables {γ : Type*}

instance union_of_quasi_strategies (g : γ → quasi_strategy G)
  (hg : ∀ x, (g x).player = p) : quasi_strategy G :=
⟨p, ⋃ (x : γ), (g x).positions, sorry⟩

instance extension_of_quasi_strategy (a : α) (h : G.turn(s) = σ.player) 
  (h' : s.concat a ∈ σ.positions) : quasi_strategy G :=
⟨σ.player, {s} ∪ σ.positions, sorry⟩

instance extension_of_quasi_strategy' (a : α)
  (h : ∀ a, s.concat a ∈ σ.positions) : quasi_strategy G :=
⟨σ.player, {s} ∪ σ.positions, sorry⟩

lemma s_quasi_strategy_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) :
  s_quasi_strategy (union_of_quasi_strategies p g hg) s := sorry

lemma s_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s_quasi_strategy σ (s.concat a)) :
  s_quasi_strategy (extension_of_quasi_strategy σ s a h (s_in_s_quasi_strategy σ _ h')) s := sorry

lemma s_quasi_strategy_extension' (a : α) (h : ∀ a, s.concat a ∈ σ.positions)
  (h' : ∀ t, t ∈ σ.positions → s <+: t) :
  s_quasi_strategy (extension_of_quasi_strategy' σ s a h) s := sorry

lemma is_winning_quasi_strategy_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) (hg'' : ∀ a, is_winning (g a) X) :
  is_winning (union_of_quasi_strategies p g hg) X := sorry

lemma is_winning_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s.concat a ∈ σ.positions) (h'' : is_winning σ X) :
  is_winning (extension_of_quasi_strategy σ s a h h') X := sorry

lemma is_winning_quasi_strategy_extension' (a : α) (h : ∀ a, s.concat a ∈ σ.positions)
  (h' : is_winning σ X) : is_winning (extension_of_quasi_strategy' σ s a h) X := sorry

lemma is_s_winning_quasi_strategy_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) (hg'' : ∀ a, is_winning (g a) X) :
  is_s_winning (union_of_quasi_strategies p g hg) X s :=
  ⟨s_quasi_strategy_union _ _ _ _ hg', is_winning_quasi_strategy_union _ s _ _ _ hg' hg''⟩

lemma is_s_winning_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s_quasi_strategy σ (s.concat a)) (h'' : is_winning σ X) :
  is_s_winning (extension_of_quasi_strategy σ s a h (s_in_s_quasi_strategy σ _ h')) X s :=
  ⟨s_quasi_strategy_extension _ _ _ _ _, is_winning_quasi_strategy_extension _ _ _ _ _ _ h''⟩

lemma is_s_winning_quasi_strategy_extension' (a : α) (h : ∀ a, s.concat a ∈ σ.positions)
  (h' : ∀ t, t ∈ σ.positions → s <+: t) (h'' : is_winning σ X) :
  is_s_winning (extension_of_quasi_strategy' σ s a h) X s :=
  ⟨s_quasi_strategy_extension' _ _ _ _ h', is_winning_quasi_strategy_extension' _ _ _ _ _ h''⟩

instance above_s_quasi_strategy [hα : nonempty α] : quasi_strategy G :=
⟨p, {t | s <+: t}, sorry⟩

lemma above_s_is_s_quasi_strategy [hα : nonempty α] :
  s_quasi_strategy (above_s_quasi_strategy s p) s := sorry

lemma above_s_winning_iff [hα : nonempty α] :
  is_winning (above_s_quasi_strategy s p) X ↔ ∀ f, is_prefix s f → X f = p :=
  sorry

-- TODO:
-- union of winning quasi strategies is winning (with appropriate extra hypothesis)
-- extension of winning quasi strategy is winning
-- extension' of winning quasi strategies is winning
-- quasi strategy above s
-- quasi strategy above s is winning iff
-- idea: prove determinacy for games where players = Prop?
-- define non-winning quasi-strategy
-- prove non-winning quasi-strategy is winning for player 2
-- prove quasi-determinacy
-- strategy from quasi-strategy (instance of quasi-strategy)
-- strategy is winning if quasi-strategy is winning
-- prove determinacy