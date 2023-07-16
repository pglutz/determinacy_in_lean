import sequences

open finseq seq set

universes u v

class game_tree (E : ℕ → Type u) :=
(moves : Π {{n}}, finseq E n → set (E n))

namespace game_tree

variables {E : ℕ → Type u} (T : game_tree E) (T' : game_tree E)

@[simp] def is_subtree (T' : game_tree E) := ∀ {{n}} (σ : finseq E n), T.moves σ ⊆ T'.moves σ

@[refl] lemma is_subtree_refl : is_subtree T T := λ n σ, subset_rfl

@[trans] lemma is_subtree.trans {T₀ T₁ T₂ : game_tree E} :
  is_subtree T₀ T₁ → is_subtree T₁ T₂ → is_subtree T₀ T₂ :=
λ h₀ h₁ n σ, subset.trans (h₀ σ) (h₁ σ)

lemma is_subtree_rfl {T : game_tree E} : is_subtree T T := is_subtree_refl T

def subtrees := { T' | is_subtree T' T }

@[refl, simp] lemma subtrees_refl : T ∈ T.subtrees := is_subtree_rfl

@[simp] def is_play (α : seq E) := ∀ n, α n ∈ T.moves (α.restrict n)

def plays := { α | T.is_play α }

lemma play_of_subtree_play (T' ∈ T.subtrees) {α : seq E} : α ∈ T'.plays → α ∈ T.plays :=
begin
  intros h n,
  simp [h n, set.mem_of_subset_of_mem (H (α.restrict n))]
end

@[simp] def is_position {n} (σ : finseq E n) :=
  ∀ {{k}} (h : k < n), σ.nth k h ∈ T.moves (σ.restrict k (le_of_lt h))

-- Reachable positions in the game tree T
def positions (n : ℕ) := { σ : finseq E n | T.is_position σ }

@[simp] def position.is_prefix {T : game_tree E} {n k : ℕ}
  (σ : T.positions n) (τ : T.positions k) :=
(σ : finseq E n) << (τ : finseq E k)

infix (name := game_tree.position.prefix) ` << `:50 := position.is_prefix

lemma move_of_position_cat {n} {σ : finseq E n} {x : E n} :
  σ ⌢ x ∈ T.positions (n+1) → x ∈ T.moves σ :=
begin
  intros h,
  unfold positions at h,
  have := h (nat.lt_succ_self n),
  simp at this,
  assumption
end

lemma positions_prefix_closed {k n} {σ : finseq E k} {τ : finseq E n} :
  σ << τ → τ ∈ T.positions n → σ ∈ T.positions k :=
begin
  rintros ⟨hkn, hστ⟩ hplay l hlk,
  rw ← hστ,
  simp [le_trans (le_of_lt hlk) hkn],
  apply hplay
end

lemma position_of_position_cat {n} {σ : finseq E n} {x : E n} :
  σ ⌢ x ∈ T.positions (n+1) → σ ∈ T.positions n :=
begin
  apply positions_prefix_closed,
  simp
end

lemma position_cat_of_position_of_move {n} {σ : finseq E n} {x : E n} :
  σ ∈ T.positions n → x ∈ T.moves σ → σ ⌢ x ∈ T.positions (n+1) :=
begin
  intros hσ hx,
  unfold positions is_position,
  intros k hk,
  by_cases k = n,
  { cases h, simp* },
  have : k < n := lt_of_le_of_ne (nat.le_of_lt_succ hk) h,
  simp [*, ne_of_lt hk],
  apply hσ
end

lemma position_of_prefix_play {n} (σ : finseq E n) (α ∈ T.plays) : σ << α → σ ∈ T.positions n :=
begin
  intros h k hkn,
  unfold seq.is_prefix at h,
  rw ← h,
  simp,
  apply H
end

lemma position_of_subtree_position (T' ∈ T.subtrees) {n} {σ : finseq E n} :
  σ ∈ T'.positions n → σ ∈ T.positions n :=
begin
  intros h₁ k h₂,
  simp [h₁ h₂, set.mem_of_subset_of_mem (H (σ.restrict k (le_of_lt h₂)))]
end

@[simp] def is_leaf {n} (σ : finseq E n) := T.moves σ = ∅

def leaves (n : ℕ) := { σ : finseq E n | T.is_leaf σ }

def finite_plays (n : ℕ) := T.positions n ∩ T.leaves n

end game_tree

open game_tree

class game (E : ℕ → Type u) (β : Type v) extends (game_tree E) :=
(turn : Π {{n}}, finseq E n → β)
(taboo : Π {{n}}, finseq E n → β)
(payoff : seq E → β)

namespace game

variables {E : ℕ → Type u} {β : Type v} (G : game E β)

-- nowhere in this definition do we require T to be a subtree of G
-- TODO: should we add this in this definition?
-- otherwise we need to mention it elsewhere that this is used (eg winning_quasi_strategy defs)
def subgame (T : game_tree E) : game E β :=
{ moves := T.moves, ..G }

@[simp] def is_quasi_strategy (P : β) (T : game_tree E) :=
  (T ∈ G.subtrees) ∧ ∀ {{n}} (σ : finseq E n), σ ∈ T.positions n →
    (G.turn σ = P → (G.moves σ).nonempty → (T.moves σ).nonempty)
    ∧ (G.turn σ ≠ P → T.moves σ = G.moves σ)

@[refl] lemma is_quasi_strategy_refl (P : β) : G.is_quasi_strategy P G.to_game_tree := by simp

lemma is_quasi_strategy_rfl {G : game E β} {P : β} : G.is_quasi_strategy P G.to_game_tree :=
  G.is_quasi_strategy_refl P

@[simp] def is_strategy (P : β) (T : game_tree E) := G.is_quasi_strategy P T ∧
  ∀ {{n}} (σ : finseq E n), σ ∈ T.positions n → G.turn σ = P → (T.moves σ).subsingleton

def quasi_strategies (P : β) := { T | G.is_quasi_strategy P T }

@[refl, simp] lemma quasi_strategies_refl (P : β) : G.to_game_tree ∈ G.quasi_strategies P :=
  is_quasi_strategy_rfl

@[simp] def is_winning_play (P : β) (α) := α ∈ G.plays ∧ G.payoff α = P

def winning_plays (P : β) := { α | G.is_winning_play P α }

-- if σ is a finite play and taboo for P, then P WINS if we reach σ
-- this is because we are allowing a general set β of players, so it doesn't make
-- sense to say that it loses for P, since in this case we don't know who wins
-- TODO: maybe we should rename taboo to something else because of this? eg finite_payoff?
@[simp] def is_winning_finite_play (P : β) {n} (σ : finseq E n) := σ ∈ G.finite_plays n ∧ G.taboo σ = P

def winning_finite_plays (P : β) (n) := { σ : finseq E n | G.is_winning_finite_play P σ }

-- A "winning position" for P is a _reachable_ position where P wins no matter what she plays
@[simp] def is_winning_position (P : β) {n} (σ : finseq E n) := σ ∈ G.positions n
  ∧ (∀ α ∈ G.plays, σ << α → α ∈ G.winning_plays P)
  ∧ (∀ {{m}} (τ ∈ G.finite_plays m), σ << τ → τ ∈ G.winning_finite_plays P m)

def winning_positions (P : β) (n : ℕ) := { σ : finseq E n | G.is_winning_position P σ }

lemma winning_move_of_winning_prefix (P : β) {k} (σ : finseq E k) {n} (τ : finseq E n) :
  σ << τ → τ ∈ G.positions n → σ ∈ G.winning_positions P k → τ ∈ G.winning_positions P n :=
begin
  unfold winning_positions is_winning_position,
  rintros hστ hτpos ⟨_, ⟨hσwin₁, hσwin₂⟩⟩,
  split,
  { exact hτpos },
  split,
  { intros α hα hτα,
    exact hσwin₁ _ hα (is_prefix.trans hστ hτα) },
  intros m μ hμ hτμ,
  exact hσwin₂ μ hμ (hστ.trans hτμ)
end

lemma winning_position_of_finite_play_of_taboo (P : β) {n} (σ : finseq E n) :
  σ ∈ G.finite_plays n → G.taboo σ = P → σ ∈ G.winning_positions P n :=
begin
  rintros ⟨σpos, σleaf⟩ σtab,
  split,
  { exact σpos },
  split,
  { intros α αplay hσα,
    have h : α n ∈ G.moves σ := by {
      cases hσα,
      exact αplay n
    },
    simp [leaves] at σleaf,
    rw σleaf at h,
    cases h },
  rintros k τ ⟨τplay, τleaf⟩ hστ,
  have : n = k := by {
    contrapose! σleaf with h,
    have h' : n < k := lt_of_le_of_ne hστ.fst h,
    apply nonempty.ne_empty,
    use τ.nth n h',
    rw ← hστ.snd,
    apply τplay
  },
  cases this,
  cases (eq_of_prefix_of_length_eq hστ),
  split; try { split }; assumption
end

@[simp] def is_winning_quasi_strategy_at_position (T : game_tree E) (P : β) {n} (σ : finseq E n) :=
  T ∈ G.quasi_strategies P ∧ σ ∈ (G.subgame T).winning_positions P n

def winning_quasi_strategies_at_position (P : β) {n} (σ : finseq E n) :=
  { T | G.is_winning_quasi_strategy_at_position T P σ }

@[simp] def is_winnable_position (P : β) {n} (σ : finseq E n) :=
  (G.winning_quasi_strategies_at_position P σ).nonempty

def winnable_positions (P : β) (n : ℕ) := { σ : finseq E n | G.is_winnable_position P σ }

lemma winnable_position_of_winning_position (P : β) :
  ∀ n, G.winning_positions P n ⊆ G.winnable_positions P n :=
begin
  intros n σ h,
  simp [winnable_positions],
  rw set.nonempty_def,
  use G.to_game_tree,
  simp [winning_quasi_strategies_at_position],
  exact h
end

lemma winnable_move_of_not_turn_of_winnable_position (P : β) {n} (σ : finseq E n) : G.turn σ ≠ P →
  σ ∈ G.winnable_positions P n → ∀ x : E n, (x ∈ G.moves σ → (σ ⌢ x) ∈ G.winnable_positions P (n+1)) :=
begin
  simp [winnable_positions],
  rintros turn ⟨T, ⟨Tstrat, Twin⟩⟩ x xmove,
  use T,
  simp [winning_quasi_strategies_at_position, Tstrat],
  apply winning_move_of_winning_prefix _ P σ _ (prefix_cat _ _) _ Twin,
  apply position_cat_of_position_of_move,
  { change σ ∈ T.positions n,
    exact Twin.1 },
  simp [quasi_strategies] at Tstrat,
  have := (Tstrat.2 σ Twin.1).2 turn,
  change x ∈ T.moves σ,
  rw this,
  assumption
end

def winning_quasi_strategies (P : β) := G.winning_quasi_strategies_at_position P null

def is_winnable (P : β) := null ∈ G.winnable_positions P 0

def is_quasi_determined := ∃ P : β, G.is_winnable P

def is_determined := ∃ P : β,
  { T ∈ G.winning_quasi_strategies_at_position P null | G.is_strategy P T }.nonempty

section determined_of_quasi_determined

noncomputable theory
open_locale classical

theorem determined_of_quasi_determined : G.is_quasi_determined → G.is_determined :=
begin
  rintros ⟨P, ⟨T, Twin⟩⟩,
  let moves : Π {{k}} (τ : finseq E k), set (E k) :=
    λ n σ,
      if h : G.turn σ = P ∧ (T.moves σ).nonempty
        then { h.2.some }
        else T.moves σ,
  let S : game_tree E := ⟨moves⟩,
  have Ssub : S ∈ T.subtrees := by {
    intros n σ,
    by_cases h : G.turn σ = P ∧ (T.moves σ).nonempty,
    { simp [moves, h, nonempty.some_mem] },
    simp [moves, h]
  },
  have Sstrat : S ∈ G.quasi_strategies P := by {
    split,
    { exact is_subtree.trans Ssub Twin.1.1 },
    intros n σ σpos,
    split,
    { intros σturn σmove,
      have h : (T.moves σ).nonempty :=
        (Twin.1.2 σ (position_of_subtree_position _ _ Ssub σpos)).1 σturn σmove,
      simp [moves, σturn, h] },
    intros σturn,
    have h : T.moves σ = G.moves σ :=
      (Twin.1.2 σ (position_of_subtree_position _ _ Ssub σpos)).2 σturn,
    simp [moves, σturn, h]
  },
  use [P, S],
  split,
  { split,
    { exact Sstrat },
    split,
    { intros k hk,
      cases hk },
    split,
    { intros α αplay h,
      split,
      { exact αplay },
      apply (Twin.2.2.1 α _ h).2,
      exact play_of_subtree_play _ _ Ssub αplay },
    intros n σ σplay h,
    split,
    { exact σplay },
    apply (Twin.2.2.2 σ _ h).2,
    split,
    { exact position_of_subtree_position _ _ Ssub σplay.1 },
    have h₀ : S.moves σ = ∅ := σplay.2,
    by_cases h : G.turn σ = P,
    { contrapose h₀,
      change T.moves σ ≠ ∅ at h₀,
      rw ← nonempty_iff_ne_empty at h₀,
      simp [moves, h, h₀] },
    simp [leaves, moves, h] at h₀,
    exact h₀ },
  split,
  { exact Sstrat },
  intros n σ σpos σturn,
  by_cases h : (T.moves σ).nonempty,
  { simp [moves, σturn, h] },
  have : T.moves σ = ∅ := by {
    rw eq_empty_iff_forall_not_mem,
    contrapose! h,
    exact h
  },
  simp [moves, h, this]
end

end determined_of_quasi_determined

end game
