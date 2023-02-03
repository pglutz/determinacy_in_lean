import tactic
import prefixes

class game (α β : Type*):=
(turn : (list α) → β)

variables {α β : Type*}

class quasi_strategy (G : game α β) :=
(player : β)
(positions : set (list α))
(is_quasi_strategy : ∀ t : list α, t ∈ positions →
  (G.turn(t) = player → ∃ a, t.concat a ∈ positions) ∧
  (G.turn(t) ≠ player → ∀ a, t.concat a ∈ positions))

variables {G : game α β} (σ : quasi_strategy G) (X : (ℕ → α) → β) 
  (s : list α) (f : ℕ → α)

def s_quasi_strategy :=
  s ∈ σ.positions ∧ ∀ t ∈ σ.positions, s <+: t

lemma s_in_s_quasi_strategy (h : s_quasi_strategy σ s) : s ∈ σ.positions := h.left

def is_strategy :=
  ∀ t : list α, t ∈ σ.positions → 
  (G.turn(t) = σ.player → ∃! a, t.concat a ∈ σ.positions)

def is_play := ∃ N, ∀ n ≥ N, stream_prefix f n ∈ σ.positions

def winning := ∀ f : ℕ → α, is_play σ f → X f = σ.player

def s_winning := s_quasi_strategy σ s ∧ winning σ X

def quasi_determined := ∃ σ : quasi_strategy G, s_winning σ X s 

def determined := ∃ σ : quasi_strategy G, 
  s_winning σ X s ∧ is_strategy σ

variables (p : β) {γ : Type*}

instance union_of_quasi_strategies (g : γ → quasi_strategy G)
  (hg : ∀ x, (g x).player = p) : quasi_strategy G :=
⟨p, ⋃ (x : γ), (g x).positions, sorry⟩

lemma mem_union_of_mem (g : γ → quasi_strategy G) (hg : ∀ x, (g x).player = p)
  (x : γ) (hs : s ∈ (g x).positions) : s ∈ (union_of_quasi_strategies p g hg).positions :=
  set.mem_Union_of_mem x hs

instance extension_of_quasi_strategy (a : α) (h : G.turn(s) = σ.player) 
  (h' : s.concat a ∈ σ.positions) : quasi_strategy G :=
⟨σ.player, {s} ∪ σ.positions, sorry⟩

-- instance extension_of_quasi_strategy'
--   (h : ∀ a, s.concat a ∈ σ.positions) : quasi_strategy G :=
-- ⟨σ.player, {s} ∪ σ.positions, sorry⟩

lemma s_quasi_strategy_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) :
  s_quasi_strategy (union_of_quasi_strategies p g hg) s := sorry

lemma s_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s_quasi_strategy σ (s.concat a)) :
  s_quasi_strategy (extension_of_quasi_strategy σ s a h (s_in_s_quasi_strategy σ _ h')) s := sorry

lemma winning_quasi_strategy_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) (hg'' : ∀ a, winning (g a) X) :
  winning (union_of_quasi_strategies p g hg) X := sorry

lemma winning_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s.concat a ∈ σ.positions) (h'' : winning σ X) :
  winning (extension_of_quasi_strategy σ s a h h') X := sorry

lemma s_winning_quasi_strategy_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) (hg'' : ∀ a, winning (g a) X) :
  s_winning (union_of_quasi_strategies p g hg) X s :=
  ⟨s_quasi_strategy_union _ _ _ _ hg', winning_quasi_strategy_union _ s _ _ _ hg' hg''⟩

lemma s_winning_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s_quasi_strategy σ (s.concat a)) (h'' : winning σ X) :
  s_winning (extension_of_quasi_strategy σ s a h (s_in_s_quasi_strategy σ _ h')) X s :=
  ⟨s_quasi_strategy_extension _ _ _ _ _, winning_quasi_strategy_extension _ _ _ _ _ _ h''⟩

instance above_s_quasi_strategy (G : game α β) (s : list α) (p : β) [hα : nonempty α] : quasi_strategy G :=
⟨p, {t | s <+: t}, sorry⟩

lemma above_s_is_s_quasi_strategy [hα : nonempty α] :
  s_quasi_strategy (above_s_quasi_strategy G s p) s := sorry

lemma above_s_winning_iff [hα : nonempty α] :
  winning (above_s_quasi_strategy G s p) X ↔ ∀ f, is_prefix s f → X f = p :=
  sorry

instance quasi_strategy_restriction : quasi_strategy G :=
⟨σ.player, {t ∈ σ.positions | s <+: t}, sorry⟩

lemma s_quasi_strategy_restriction (h : s ∈ σ.positions) : s_quasi_strategy (quasi_strategy_restriction σ s) s :=
  sorry

lemma winning_restriction (h : winning σ X) : winning (quasi_strategy_restriction σ s) X :=
  sorry

lemma s_winning_restriction (h : s ∈ σ.positions) (h' : winning σ X) : 
  s_winning (quasi_strategy_restriction σ s) X s :=
  ⟨s_quasi_strategy_restriction _ _ h, winning_restriction _ _ _ h'⟩

-- TODO:
-- union of winning quasi strategies is winning (with appropriate extra hypothesis)
-- extension of winning quasi strategy is winning
-- restriction of quasi strategy to above s
-- quasi strategy above s
-- quasi strategy above s is winning iff
-- strategy from quasi-strategy (instance of quasi-strategy)
-- strategy is winning if quasi-strategy is winning
-- prove determinacy
-- prove open → is_prefix_open