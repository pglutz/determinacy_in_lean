import games

noncomputable theory
open_locale classical

variables {α β : Type*} [nonempty α]

def winning_position (G : game α β) (X : (ℕ → α) → β) (s : list α) (p : β):=
  ∃ σ : quasi_strategy G, s_winning σ X s ∧ σ.player = p

variables (G : game α Prop) (X : (ℕ → α) → Prop) (s : list α) (p : Prop)

lemma winning_position_of_prefix_prefix_open (t : list α) (C : set (list α)) 
  (h : prefix_open X C) (hs : s ∈ C) (ht : s <+: t) : winning_position G X t true :=
begin
  use above_s_quasi_strategy G t true,
  split,
  { split,
    { exact above_s_is_s_quasi_strategy t true, },
    { intros f hf,
      apply eq_true_intro,
      apply (h f).mpr,
      use s,
      use hs,
      cases hf with n hn,
      specialize hn n rfl.ge,
      change t <+: stream_prefix f n at hn,
      apply is_prefix_of_prefix s f n,
      calc s <+: t : ht 
      ... <+: stream_prefix f n : hn, }, },
  { refl, },
end

instance non_winning : quasi_strategy G :=
⟨ p, 
  {s | ¬ winning_position G X s (¬ p)}, 
  begin
    intros t ht,
    split,
    { intros ht',
      by_contra' h,
      apply ht,
      change ∀ a, ¬¬ winning_position G X (t.concat a) (¬ p) at h,
      conv at h in (¬¬ winning_position G X (t.concat _) (¬ p))
        { rw not_not, rw winning_position, },
      choose g hg using h,
      have hg₁ : ∀ a, (g a).player = ¬ p := λ a, (hg a).right,
      have hg₂ : ∀ a, s_quasi_strategy (g a) (t.concat a) := λ a, (hg a).left.left,
      have hg₃ : ∀ a, winning (g a) X := λ a, (hg a).left.right,
      let σ := union_of_quasi_strategies (¬ p) g hg₁,
      let τ := extension_of_quasi_strategy' σ t (λ a, mem_union_of_mem _ _ g hg₁ a (hg₂ a).left), 
      use τ,
      split,
      { apply s_winning_quasi_strategy_extension' σ X t,
        { intros r hr,
          cases set.mem_Union.mp hr with a ha,
          calc t <+: t.concat a : list.prefix_concat a t
          ... <+: r : (hg₂ a).right r ha, },
        { exact winning_quasi_strategy_union _ _ _ g hg₁ hg₂ hg₃, },  },
      { refl, }, },
    { intros ht' a,
      by_contra' h,
      apply ht,
      change ¬¬ winning_position G X (t.concat a) (¬ p) at h,
      rw not_not at h,
      rcases h with ⟨σ, ⟨⟨hσ₁, hσ₂⟩, hσ₃⟩⟩,
      have hp : G.turn t = σ.player,
      { change ¬ (G.turn t = p) at ht',
        rw hσ₃,
        by_contra',
        tauto, },
      let τ := extension_of_quasi_strategy σ t a hp hσ₁.left,
      exact ⟨τ, s_winning_quasi_strategy_extension _ _ _ _ hp hσ₁ hσ₂, hσ₃⟩, },
  end⟩

lemma non_winning_is_winning (h : is_prefix_open X) : winning (non_winning G X false) X :=
begin
  intros f,
  contrapose!,
  intros hf hf',
  change ¬ (X f) = false at hf,
  simp only [eq_iff_iff, iff_false, not_not] at hf,
  cases h with C hC,
  rcases (hC f).mp hf with ⟨s, ⟨hs, hs'⟩⟩,
  cases hf' with N h,
  let n := max N s.length,
  specialize h n (le_max_left _ _),
  have key : winning_position G X (stream_prefix f n) true,
  { apply winning_position_of_prefix_prefix_open G X s (stream_prefix f n) C hC hs,
    apply prefix_of_is_prefix s f n hs' (le_max_right _ _), },
  rw ← not_false_iff at key,
  exact h key,
end

theorem open_quasi_determinacy (h : is_prefix_open X) : @quasi_determined _ _ G X s :=
begin
  by_cases h' : winning_position G X s true,
  { cases h' with σ hσ,
    exact ⟨σ, hσ.left⟩, },
  { let σ := quasi_strategy_restriction (non_winning G X false) s,
    use σ,
    apply s_winning_restriction,
    { rw ← not_false_iff at h',
      exact h', },
    { exact non_winning_is_winning _ _ h, }, },
end 
