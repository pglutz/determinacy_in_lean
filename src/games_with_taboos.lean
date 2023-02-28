import tactic
import data.list.infix
import data.pfun
import prefixes

open set list

noncomputable theory
open_locale classical

-- Basic definitions and lemmas about game trees

-- A game tree is just a set theoretic tree, i.e., a set of finite sequences closed under taking subsequences
class game_tree {α : Type*} (T : set (list α)) :=
(nonempty : nil ∈ T)
(prefix_closed : ∀ s t : list α, s <+: t → t ∈ T → s ∈ T)

def game_tree_of_nonempty_of_prefix_closed {α : Type*} (T : set (list α)) :
  nil ∈ T → (∀ s t : list α, s <+: t → t ∈ T → s ∈ T) → game_tree T :=
λ h₁ h₂, ⟨h₁, h₂⟩

section game_tree

variables {α β : Type*} (T : set (list α)) [game_tree T] (T' : set (list β)) [game_tree T']

-- The localized subtree of T at t is the subtrees of T consisting of sequences compatible with t
def localized_subtree (t : list α) := {s | s ∈ T ∧ (s <+: t ∨ t <+: s)}

instance localized_game_tree {α : Type*} {T : set (list α)} [game_tree T] {t : list α} :
  game_tree (localized_subtree T t) :=
{ nonempty := ⟨game_tree.nonempty, or.inl (nil_prefix _)⟩,
  prefix_closed := λ s u psu uinT,
    ⟨game_tree.prefix_closed _ _ psu uinT.1,
      or.elim uinT.2
        (assume put, or.inl (psu.trans put))
        (assume ptu, prefix_or_prefix_of_prefix psu ptu)⟩ }

lemma localized_subtree_subset (t : list α) : (localized_subtree T t) ⊆ T :=
  inter_subset_left _ _

def is_legal_move (t : list α) (a : α) := t.concat a ∈ T

def has_legal_move (t : list α) := ∃ a, is_legal_move T t a

lemma in_tree_of_has_legal_move (t : list α) : has_legal_move T t → t ∈ T :=
λ ⟨a, hta⟩, game_tree.prefix_closed _ (t.concat a) (by simp) hta

lemma has_legal_move_of_prefix_of_ne_of_in_tree {s t : list α} :
  s <+: t → s ≠ t → t ∈ T → has_legal_move T s :=
begin
  sorry
end

lemma has_legal_move_of_has_legal_move_of_prefix {s t : list α} :
  has_legal_move T t → s <+: t → has_legal_move T s :=
begin
  rintros hlt hst,
  by_cases h : s.length < t.length,
  { use nth_le t s.length h,
    have : s.concat (nth_le t s.length h) <+: t := concat_prefix_of_length_lt_of_prefix h hst,
    refine game_tree.prefix_closed _ _ this _,
    exact in_tree_of_has_legal_move _ _ hlt, },
  have : s.length = t.length,
  { linarith [hst.length_le], },
  rwa [eq_of_prefix_of_length_eq hst this],
end

lemma has_legal_move_localized_of_has_legal_move (p t : list α) : p ∈ T →
  t ∈ localized_subtree T p → has_legal_move T t → has_legal_move (localized_subtree T p) t :=
begin
  rintros hpT ⟨ht, htp | hpt⟩ ⟨a, hta⟩,
  { by_cases h : t.length < p.length,
    { use nth_le p t.length h,
      have : t.concat (nth_le p t.length h) <+: p := concat_prefix_of_length_lt_of_prefix h htp,
      refine game_tree.prefix_closed _ _ this _,
      exact ⟨hpT, or.inl prefix_rfl⟩, },
    have : t.length = p.length,
    { linarith [htp.length_le], },
    rw [eq_of_prefix_of_length_eq htp this] at *,
    use a,
    refine ⟨hta, or.inr (prefix_concat _ _)⟩, },
  use [a, hta],
  right,
  exact hpt.trans (prefix_concat _ _),
end

lemma has_legal_move_localized_of_has_legal_move_localized_of_prefix (p q t : list α):
  has_legal_move (localized_subtree T q) t → p <+: q → has_legal_move (localized_subtree T p) t :=
sorry

@[simp] def is_terminal (t : list α) := t ∈ T ∧ ¬ has_legal_move T t

@[simp] def finite_plays := {p  | is_terminal T p}

def is_infinite_play (f : ℕ → α) := ∀ n : ℕ, stream_prefix f n ∈ T

@[simp] def infinite_plays := {f | is_infinite_play T f}

end game_tree

-- Strategies for a game tree

section strategies

variables {α β : Type*} (T : set (list α)) [game_tree T] (T' : set (list β)) [game_tree T']

def is_strategy (σ : list α → α) := ∀ t ∈ T, has_legal_move T t → is_legal_move T t (σ t)

@[simp] def strategies := {σ | is_strategy T σ}

def consistent_position₁ (σ ∈ strategies T) (p : list α) :=
  p ∈ T ∧ ∀ k < p.length, even k → nth_le p k (by assumption) = σ (take k p)

@[simp] def consistent_finite_play₁ (σ ∈ strategies T) (p : list α) :=
  p ∈ finite_plays T ∧ consistent_position₁ T σ (by assumption) p

@[simp] def consistent_infinite_play₁ (σ ∈ strategies T) (f : ℕ → α) :=
  f ∈ infinite_plays T ∧ ∀ n, even n → f n = σ (stream_prefix f n)

def consistent_position₂ (τ ∈ strategies T) (p : list α) :=
  p ∈ T ∧ ∀ k < p.length, odd k → nth_le p k (by assumption) = τ (take k p)

@[simp] def consistent_finite_play₂ (τ ∈ strategies T) (p : list α) :=
  p ∈ finite_plays T ∧ consistent_position₂ T τ (by assumption) p

@[simp] def consistent_infinite_play₂ (τ ∈ strategies T) (f : ℕ → α) :=
  f ∈ infinite_plays T ∧ ∀ n, odd n → f n = τ (stream_prefix f n)

lemma prefix_of_consistent_is_consistent₁ (σ ∈ strategies T) (f : ℕ → α) :
  consistent_infinite_play₁ _ σ (by assumption) f →
    ∀ n, consistent_position₁ _ σ (by assumption) (stream_prefix f n) :=
sorry

lemma prefix_of_consistent_is_consistent₂ (τ ∈ strategies T) (f : ℕ → α) :
  consistent_infinite_play₂ _ τ (by assumption) f →
    ∀ n, consistent_position₂ _ τ (by assumption) (stream_prefix f n) :=
sorry

end strategies

-- Maps between trees

section tree_maps

variables {α β : Type*} (T : set (list α)) [game_tree T] (T' : set (list β)) [game_tree T']

class tree_map (f : list α → list β) :=
(image_subset : f '' T ⊆ T')
(monotone : ∀ p q ∈ T, p <+: q → f p <+: f q)
(lipschitz : ∀ p ∈ T, length p = length (f p))
(induced_map : (ℕ → α) → (ℕ → β))
(induced_map_def : ∀ (g ∈ infinite_plays T) (n : ℕ),
                      stream_prefix (induced_map g) n = f (stream_prefix g n))

lemma image_subset_of_induced_map {f : list α → list β} (hf : tree_map T T' f):
  hf.induced_map '' infinite_plays T ⊆ infinite_plays T' :=
begin
  intros x hx n,
  rcases hx with ⟨g, ⟨hg, hgx⟩⟩,
  rw [← hgx, hf.induced_map_def g hg],
  apply mem_of_subset_of_mem hf.image_subset,
  apply mem_image_of_mem,
  apply hg,
end

end tree_maps

-- Every monotone lipschitz map between trees induces a tree map

-- section induced_tree_maps

-- variables {α β : Type*} {T : set (list α)} [game_tree T] {T' : set (list β)} [game_tree T']
--           (f : list α → list β) (Hfis : f '' T ⊆ T') (Hfm : ∀ p q ∈ T, p <+: q → f p <+: f q)
--           (Hfl : ∀ p ∈ T, length p = length (f p))

-- def induced_tree_maps.induced_map : (ℕ → α) → (ℕ → β) :=
-- sorry

-- lemma induced_tree_maps.induced_map_def :
--   ∀ (g ∈ infinite_plays T) (n : ℕ),
--     stream_prefix (induced_tree_maps.induced_map g) n = f (stream_prefix g n) :=
-- sorry

-- instance induced_tree_map : tree_map T T' f :=
-- { image_subset := Hfis,
--   monotone := Hfm,
--   lipschitz := Hfl,
--   induced_map := induced_tree_maps.induced_map,
--   induced_map_def := induced_tree_maps.induced_map_def f }

-- end induced_tree_maps

-- Topology on the space of infinite plays through a tree

section topology

variables {α : Type*} (T : set (list α)) [game_tree T]

@[simp] def plays_of_subtree (A : set (ℕ → α)) (T' : set (list α)) [game_tree T'] :=
  T' ⊆ T ∧ A = infinite_plays T'

def closed_set (A : set (ℕ → α)) := ∃ T' (h : game_tree T'), @plays_of_subtree _ T _ A T' h

lemma subset_plays_of_closed_set (A : set (ℕ → α)) : closed_set T A → A ⊆ infinite_plays T :=
begin
  unfold closed_set,
  rintros ⟨T', ⟨hT', ⟨T'subT, AT'⟩⟩⟩,
  have : A ⊆ @infinite_plays _ T' hT' := subset_of_eq AT',
  refine subset_trans this _,
  exact λ g hg n, mem_of_mem_of_subset (hg n) T'subT,
end

@[simp] def open_set (A : set (ℕ → α)) := A ⊆ infinite_plays T ∧ closed_set T (infinite_plays T \ A)

@[simp] def clopen_set (A : set (ℕ → α)) := closed_set T A ∧ open_set T A

variables {β : Type*} (T' : set (list β)) [game_tree T'] (f : list α → list β) (hf : tree_map T T' f)

lemma preimage_closed_of_induced_map_of_closed (A : set (ℕ → β)) :
  closed_set T' A → closed_set T (hf.induced_map ⁻¹' A ∩ infinite_plays T) :=
begin
  unfold closed_set,
  rintros ⟨S, ⟨hS, ⟨hST, hSA⟩⟩⟩,
  rw hSA,
  use f ⁻¹' S ∩ T,
  have nonempty : nil ∈ f ⁻¹' S ∩ T,
  { refine mem_inter _ game_tree.nonempty,
    simp,
    have : length (f nil) = 0,
    { rw ← hf.lipschitz nil game_tree.nonempty, simp, },
    have : f nil = nil := length_eq_zero.mp this,
    rw this,
    exact hS.nonempty, },
  have prefix_closed : ∀ s t, s <+: t → t ∈ f ⁻¹' S ∩ T → s ∈ f ⁻¹' S ∩ T,
  { intros s t hst ht,
    have : s ∈ T := game_tree.prefix_closed s t hst ht.2,
    split,
    { refine hS.prefix_closed (f s) (f t) _ ht.1,
      refine hf.monotone _ this _ ht.2 hst, },
    exact this, },
  use game_tree_of_nonempty_of_prefix_closed _ nonempty prefix_closed,
  simp, ext, split,
  { intros hx n,
    simp,
    have hxt : x ∈ infinite_plays T := mem_of_mem_inter_right hx,
    refine ⟨_, hxt n⟩,
    have := (mem_of_mem_inter_left hx) n,
    rwa ← hf.induced_map_def x hxt n, },
  simp, intros hx,
  have hxt : x ∈ infinite_plays T := λ n,  mem_of_mem_inter_right (hx n),
  split,
  { intros n,
    rw hf.induced_map_def x hxt n,
    apply mem_of_mem_inter_left (hx n), },
  exact hxt,
end

end topology

-- Games with taboos

-- A game tree with taboos is a game tree with a partition of its terminal notes into two pieces
class game_tree_with_taboos {α : Type*} (T : set (list α)) extends (game_tree T) :=
(taboos₁ : set (list α))
(taboos₂ : set (list α))
(taboos_disjoint : taboos₁ ∩ taboos₂ = ∅)
(taboos_terminal : taboos₁ ∪ taboos₂ = finite_plays T)

lemma taboos_subset_finite_plays₁ {α : Type*} (T : set (list α)) [game_tree_with_taboos T] :
  game_tree_with_taboos.taboos₁ T ⊆ finite_plays T :=
begin
  rw ← game_tree_with_taboos.taboos_terminal,
  apply subset_union_left,
end

lemma taboos_subset_tree₁ {α : Type*} (T : set (list α)) [game_tree_with_taboos T] :
  game_tree_with_taboos.taboos₁ T ⊆ T :=
begin
  refine subset_trans (taboos_subset_finite_plays₁ T) _,
  intros x hx,
  exact hx.1,
end

lemma taboos_subset_finite_plays₂ {α : Type*} (T : set (list α)) [game_tree_with_taboos T] :
  game_tree_with_taboos.taboos₂ T ⊆ finite_plays T :=
begin
  rw ← game_tree_with_taboos.taboos_terminal,
  apply subset_union_right,
end

lemma taboos_subset_tree₂ {α : Type*} (T : set (list α)) [game_tree_with_taboos T] :
  game_tree_with_taboos.taboos₂ T ⊆ T :=
begin
  refine subset_trans (taboos_subset_finite_plays₂ T) _,
  intros x hx,
  exact hx.1,
end

-- We define the sub-game-tree with taboos starting at position p of a game G
-- View this as the players being forced to play following p at the start of the game
instance localized_game_tree_with_taboos {α : Type*} (T : set (list α)) [game_tree_with_taboos T] (p ∈ T) :
  game_tree_with_taboos (localized_subtree T p) :=
{ taboos₁ := game_tree_with_taboos.taboos₁ T ∩ (localized_subtree T p),
  taboos₂ := game_tree_with_taboos.taboos₂ T ∩ (localized_subtree T p),
  taboos_disjoint :=
    by { rw [← inter_assoc, inter_assoc _ (localized_subtree _ _) _,
         inter_comm (localized_subtree _ _) _, ← inter_assoc,
         game_tree_with_taboos.taboos_disjoint, empty_inter, empty_inter], },
  taboos_terminal := 
    begin
      rw[← union_inter_distrib_right, game_tree_with_taboos.taboos_terminal],
      ext, split,
      { intros hx,
        split,
        { exact mem_of_mem_inter_right hx, },
        rintros ⟨a, hxa⟩,
        suffices : ¬ is_terminal T x,
        { apply this, apply (mem_of_mem_inter_left hx), },
        suffices : has_legal_move T x,
        { exact λ ⟨_, hxt⟩, hxt this, },
        use [a, mem_of_mem_of_subset hxa (localized_subtree_subset _ _)], },
      rintros ⟨hx, hxt⟩,
      split,
      { split,
        { exact mem_of_mem_of_subset hx (localized_subtree_subset _ _) },
        contrapose! hxt,
        exact has_legal_move_localized_of_has_legal_move _ _ _ H hx hxt, },
      exact hx,
    end }

-- Here we define coverings of games with taboos

section game_maps

variables {α β : Type*} (T : set (list α)) [game_tree_with_taboos T] (T' : set (list β))
          [game_tree_with_taboos T']

class position_map (f : list α → list β) extends (tree_map T T' f) :=
(taboos_lift₁ : game_tree_with_taboos.taboos₁ T ⊆ f⁻¹' game_tree_with_taboos.taboos₁ T')
(taboos_lift₂ : game_tree_with_taboos.taboos₂ T ⊆ f⁻¹' game_tree_with_taboos.taboos₂ T')

def depends_only_on_initial_segments (f : (list α → α) → (list β → β)) :=
  ∀ (n : ℕ) (σ τ : list α → α), (∀ p : list α, p.length < n → σ p = τ p)
    → (∀ p : list β, p.length < n → f σ p = f τ p)

class strategies_map (f : (list α → α) → (list β → β)) :=
(preserve_strategies : f '' strategies T ⊆ strategies T')
(finite_dep : depends_only_on_initial_segments f)

end game_maps

section coverings

variables {α β : Type*} (T : set (list α)) [game_tree_with_taboos T] (T' : set (list β))
          [game_tree_with_taboos T'] (π : list α → list β) [position_map T T' π]
          (φ : (list α → α) → (list β → β)) [strategies_map T T' φ]


lemma strategy_of_strategy_map (σ ∈ strategies T) :
  (φ σ ∈ strategies T') :=
strategies_map.preserve_strategies (mem_image_of_mem φ (by assumption))

@[simp] def lifting_condition_finite_play₁ :=
  ∀ (σ ∈ strategies T) x,
    consistent_finite_play₁ T' (φ σ) (strategy_of_strategy_map T T' φ σ (by assumption)) x
      → ∃ x', consistent_finite_play₁ T σ (by assumption) x' ∧ π x' <+: x
              ∧ (π x' = x ∨ x' ∈ game_tree_with_taboos.taboos₁ T)

@[simp] def lifting_condition_infinite_play₁ :=
  ∀ (σ ∈ strategies T) f,
    consistent_infinite_play₁ T' (φ σ) (strategy_of_strategy_map T T' φ σ (by assumption)) f
    → (∃ x', consistent_finite_play₁ T σ (by assumption) x' ∧ is_prefix (π x') f
              ∧ x' ∈ game_tree_with_taboos.taboos₁ T)
      ∨ (∃ f', consistent_infinite_play₁ T σ (by assumption) f'
              ∧ (tree_map.induced_map T T' π) f' = f)

@[simp] def lifting_condition_finite_play₂ :=
  ∀ (τ ∈ strategies T) x,
    consistent_finite_play₂ T' (φ τ) (strategy_of_strategy_map T T' φ τ (by assumption)) x
      → ∃ x', consistent_finite_play₂ T τ (by assumption) x' ∧ π x' <+: x
              ∧ (π x' = x ∨ x' ∈ game_tree_with_taboos.taboos₂ T)

@[simp] def lifting_condition_infinite_play₂ :=
  ∀ (τ ∈ strategies T) f,
    consistent_infinite_play₂ T' (φ τ) (strategy_of_strategy_map T T' φ τ (by assumption)) f
    → (∃ x', consistent_finite_play₂ T τ (by assumption) x' ∧ is_prefix (π x') f
              ∧ x' ∈ game_tree_with_taboos.taboos₂ T)
      ∨ (∃ f', consistent_infinite_play₂ T τ (by assumption) f'
                ∧ (tree_map.induced_map T T' π) f' = f)

class covering (T : set (list α)) [game_tree_with_taboos T] (T' : set (list β))
          [game_tree_with_taboos T'] (π : list α → list β) (φ : (list α → α) → (list β → β))
            extends (position_map T T' π), (strategies_map T T' φ) :=
(finite_lifting₁ : lifting_condition_finite_play₁ T T' π φ)
(infinite_lifting₁ : lifting_condition_infinite_play₁ T T' π φ)
(finite_lifting₂ : lifting_condition_finite_play₂ T T' π φ)
(infinite_lifting₂ : lifting_condition_infinite_play₂ T T' π φ)

end coverings

-- We now define games, unravellings, winning strategies and determinacy

-- A game is a game tree with a payoff set
class game {α : Type*} (T : set (list α)) (A : set (ℕ → α)) extends (game_tree_with_taboos T) :=
(payoff_subset : A ⊆ infinite_plays T)

@[simp] def eq_game {α : Type*} {T T' : set (list α)} {A B : set (ℕ → α)}
            (G : game T A) (G' : game T' B) :=
  T = T' ∧ A = B ∧ G.taboos₁ = G'.taboos₁ ∧ G.taboos₂ = G'.taboos₂

@[simp] def closed_game {α : Type*} {T : set (list α)} {A : set (ℕ → α)} (h : game T A) := closed_set T A
@[simp] def open_game {α : Type*} {T : set (list α)} {A : set (ℕ → α)} (h : game T A) := open_set T A
@[simp] def clopen_game {α : Type*} {T : set (list α)} {A : set (ℕ → α)} (h : game T A) := clopen_set T A

-- We define the subgame starting at position p of a game G
-- View this as the players being forced to play following p at the start of the game

instance localized_game {α : Type*} {T : set (list α)} {A : set (ℕ → α)} (G : game T A) (p ∈ T) :
  game (localized_subtree T p) (A ∩ infinite_plays (localized_subtree T p)) :=
{ taboos₁ := _,
  taboos₂ := _,
  taboos_disjoint := (localized_game_tree_with_taboos T p (by assumption)).taboos_disjoint,
  taboos_terminal := (localized_game_tree_with_taboos T p (by assumption)).taboos_terminal,
  payoff_subset := λ f hf, hf.2}

-- Localizing at the empty sequence gives the same game
lemma eq_game_trivial_localization {α : Type*} {T : set (list α)} {A : set (ℕ → α)} (G : game T A) :
  eq_game (localized_game G nil G.nonempty) G :=
begin
  split,
  { apply eq_of_subset_of_subset,
    { exact λ x hx, hx.1 },
    exact λ x hx, ⟨hx, or.inr (nil_prefix _)⟩, },
  split,
  { rw inter_eq_left_iff_subset,
    refine subset_trans G.payoff_subset _,
    exact λ f hf n, ⟨hf n, or.inr (nil_prefix _)⟩, },
  split,
  { simp [game_tree_with_taboos.taboos₁],
    have : T ⊆ localized_subtree T nil := λ x hx, ⟨hx, or.inr (nil_prefix _)⟩,
    exact subset_trans (taboos_subset_tree₁ T) this, },
  simp [game_tree_with_taboos.taboos₂],
  have : T ⊆ localized_subtree T nil := λ x hx, ⟨hx, or.inr (nil_prefix _)⟩,
  exact subset_trans (taboos_subset_tree₂ T) this,
end

section unravellings

variables {α β : Type*} (T : set (list α)) [game_tree_with_taboos T] {T' : set (list β)}
          {B : set (ℕ → β)}

instance lifted_game (G : game T' B) {π : list α → list β} {φ : (list α → α) → (list β → β)}
  (hc: covering T T' π φ) :
  game T ((tree_map.induced_map T T' π) ⁻¹' B ∩ infinite_plays T) :=
⟨inter_subset_right _ _⟩

end unravellings

section covers

variables {α β : Type*} {T : set (list α)} {T' : set (list β)} {A : set (ℕ → α)} {B : set (ℕ → β)} 

def covers (G : game T A) (G' : game T' B) :=
  ∃ π φ (hc : covering T T' π φ), eq_game G (lifted_game T G' hc)

def unravels (G : game T A) (G' : game T' B) :=
  ∃ π φ (hc : covering T T' π φ), eq_game G (lifted_game T G' hc) ∧ clopen_game (lifted_game T G' hc)

lemma covers_of_unravels {G : game T A} {G' : game T' B} : unravels G G' → covers G G' :=
begin
  unfold covers unravels,
  rintros ⟨π, ⟨φ, ⟨hc, ⟨heq, _⟩⟩⟩⟩,
  use [π, φ, hc, heq],
end

end covers

section determinacy

variables {α : Type*} {T : set (list α)} {A : set (ℕ → α)}

def winning_strategy₁ (G : game T A) (σ ∈ strategies T) :=
  (∀ p, consistent_finite_play₁ T σ (by assumption) p → p ∈ G.taboos₂)
  ∧ (∀ f, consistent_infinite_play₁ T σ (by assumption) f → f ∈ A)

def winning_strategy₂ (G : game T A) (τ ∈ strategies T) :=
  (∀ p, consistent_finite_play₂ T τ (by assumption) p → p ∈ G.taboos₁)
  ∧ (∀ f, consistent_infinite_play₂ T τ (by assumption) f → f ∉ A)

def determined₁ (G : game T A) := ∃ σ ∈ strategies T, winning_strategy₁ G σ (by assumption)

def determined₂ (G : game T A) := ∃ τ ∈ strategies T, winning_strategy₂ G τ (by assumption)

def determined (G : game T A) := determined₁ G ∨ determined₂ G

end determinacy