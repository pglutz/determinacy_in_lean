import tactic.interactive
import games_with_taboos

open set list

noncomputable theory
open_locale classical

-- Define the trivial covering of two equal games

section trivial_covering

variables {α : Type*} {T T' : set (list α)} {A A' : set (ℕ → α)} {G : game T A} {G' : game T' A'}

instance position_map_eq_game (heq : eq_game G G') : position_map T T' id :=
{ image_subset := by { rw heq.1, exact subset_of_eq (image_id _) },
  monotone := λ p hp q hq hpq, hpq,
  lipschitz := λ p hp, rfl,
  induced_map := id,
  induced_map_def := λ g hg n, rfl,
  taboos_lift₁ := by { rw heq.2.2.1, simp, },
  taboos_lift₂ := by { rw heq.2.2.2, simp, } }

instance strategies_map_eq_game (heq : eq_game G G') : strategies_map T T' id :=
{ preserve_strategies :=
  begin
    unfold strategies is_strategy,
    simp [has_legal_move, is_legal_move, heq.1],
  end,
  finite_dep := by simp [depends_only_on_initial_segments] }

def covering_eq_game (heq : eq_game G G') :
  covering T T' id id :=
{ finite_lifting₁ :=
  begin
    have := heq.1,
    unfreezingI {subst this},
    intros σ hσ x hσxc,
    use [x, hσxc, prefix_rfl, or.inl rfl],
  end,
  infinite_lifting₁ :=
  begin
    have := heq.1,
    unfreezingI {subst this},
    intros σ hσ f hσfc,
    right,
    use f,
    change consistent_infinite_play₁ T (id σ) hσ f ∧ f = f,
    use [hσfc, rfl],
  end,
  finite_lifting₂ :=
  begin
    have := heq.1,
    unfreezingI {subst this},
    intros σ hσ x hσxc,
    use [x, hσxc, prefix_rfl, or.inl rfl],
  end,
  infinite_lifting₂ :=
  begin
    have := heq.1,
    unfreezingI {subst this},
    intros σ hσ f hσfc,
    right,
    use f,
    change consistent_infinite_play₂ T (id σ) hσ f ∧ f = f,
    use [hσfc, rfl],
  end,
  .. (position_map_eq_game heq),
  .. (strategies_map_eq_game heq) }

lemma covers_of_eq_game {T' : set (list α)} {B : set (ℕ → α)} {G : game T A} {G' : game T' B} :
  eq_game G G' → covers G G' :=
begin
  intros heq,
  unfold covers,
  use [id, id, covering_eq_game heq],
  unfold eq_game,
  rcases heq with ⟨_, ⟨_, _⟩⟩,
  unfreezingI {subst_vars},
  refine ⟨rfl, ⟨_, ⟨rfl, rfl⟩⟩⟩,
  change B = B ∩ _,
  symmetry,
  rw inter_eq_left_iff_subset,
  exact G'.payoff_subset,
end

end trivial_covering