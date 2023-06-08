import sequences
import games

open finseq

noncomputable theory
open_locale classical

variables {E : ℕ → Type} (G : game E bool)

def canonical_quasi_strategy (P : bool) : game_tree E :=
⟨λ {{n}} (σ : finseq E n), { x ∈ G.moves σ | G.turn σ = P → ¬ G.is_winnable_position (¬ P) (σ ⌢ x) }⟩

lemma not_losing_move_of_not_losing : ∀ (P : bool) {n} (σ : finseq E n), G.turn σ = P →
  (G.moves σ).nonempty → ¬ G.is_winnable_position (¬ P) σ → ∃ x, x ∈ G.moves σ ∧ ¬ G.is_winnable_position (¬ P) (σ ⌢ x) :=
begin
  intros P n σ σturn σmove σ_not_losing,
  contrapose! σ_not_losing,
  sorry
end

lemma winnable_of_winnable_move : ∀ (P : bool) {n} (σ : finseq E n), G.turn σ = P →
  (∃ x, x ∈ G.moves σ ∧ G.is_winnable_position P (σ ⌢ x)) → G.is_winnable_position P σ :=
begin
  rintros P n σ σturn ⟨x, ⟨xmove, ⟨T, ⟨Tstrat, ⟨Tplay, Twinning⟩⟩⟩⟩⟩,
  sorry
end

lemma canonical_quasi_strategy_not_losing : ∀ (P : bool) {n} (σ : finseq E n),
  ¬ G.is_winnable_position (¬ P) null → (canonical_quasi_strategy G P).is_finite_play σ
    → ¬ G.is_winnable_position (¬ P) σ :=
begin
  intros P n σ null_not_losing σplay,
  induction σ with n σ x ihσ,
  { assumption },
  by_cases G.turn σ = P,
  { exact ((canonical_quasi_strategy G P).move_of_finite_play_cat σplay).2 h },
  have := ihσ ((canonical_quasi_strategy G P).finite_play_of_finite_play_cat σplay),
  contrapose! this,
  apply winnable_of_winnable_move,
  { rw ← (bool.bnot_eq_iff.mpr h),
    simp },
  use x,
  split,
  { have := ((canonical_quasi_strategy G P).move_of_finite_play_cat σplay),
    exact set.mem_of_mem_of_subset this (set.sep_subset _ _) },
  assumption
end

lemma canonical_quasi_strategy_is_quasi_strategy_of_not_losing (P : bool) :
  ¬ G.is_winnable_position (¬ P) null → G.is_quasi_strategy P (canonical_quasi_strategy G P) :=
begin
  intros null_not_losing,
  split,
  { intros n σ x hx,
    exact set.mem_of_mem_of_subset hx (set.sep_subset _ _) },
  intros n σ σplay,
  split,
  { intros σturn σmoves,
    have σ_not_losing := canonical_quasi_strategy_not_losing _ _ _ null_not_losing σplay,
    rcases (not_losing_move_of_not_losing _ _ _ σturn σmoves σ_not_losing) with ⟨x, ⟨xmove, x_not_losing⟩⟩,
    use x,
    apply set.mem_sep xmove,
    intros _,
    assumption },
  intros σturn,
  apply set.sep_eq_self_iff_mem_true.mpr,
  intros x hx σturn',
  contradiction
end
