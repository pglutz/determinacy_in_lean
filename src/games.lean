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
⟨ p, 
  ⋃ (x : γ), (g x).positions,
  begin
    intros t ht,
    cases set.mem_Union.mp ht with x hx,
    have key := (g x).is_quasi_strategy t hx,
    split,
    { intros ht',
      cases key.left ((rfl.congr (eq.symm (hg x))).mp ht') with a ha,
      use a,
      exact set.mem_Union_of_mem x ha, },
    { intros ht' a,
      have := key.right (ne_of_ne_of_eq ht' (eq.symm (hg x))) a,
      exact set.mem_Union_of_mem x this, },
  end ⟩

lemma mem_union_of_mem (g : γ → quasi_strategy G) (hg : ∀ x, (g x).player = p)
  (x : γ) (hs : s ∈ (g x).positions) : s ∈ (union_of_quasi_strategies p g hg).positions :=
  set.mem_Union_of_mem x hs

instance extension_of_quasi_strategy (a : α) (h : G.turn(s) = σ.player) 
  (h' : s.concat a ∈ σ.positions) : quasi_strategy G :=
⟨ σ.player,
  {s} ∪ σ.positions,
  begin
    intros t ht,
    cases ht,
    { change t = s at ht,
      rw ht,
      split,
      { intros _,
        exact ⟨a, set.mem_union_right _ h'⟩, },
      { intros ht',
        exfalso,
        exact ht' h, },
    },
    { cases σ.is_quasi_strategy t ht with hσ₁ hσ₂,
      split,
      { intros ht',
        cases hσ₁ ht' with b hb,
        use b,
        exact set.mem_union_right _ hb, },
      { intros ht' b,
        exact set.mem_union_right _ (hσ₂ ht' b), }, },
  end ⟩

instance extension_of_quasi_strategy' [hα : nonempty α] (h : ∀ a, s.concat a ∈ σ.positions) :
  quasi_strategy G :=
⟨ σ.player,
  {s} ∪ σ.positions,
  begin
    intros t ht,
    cases ht,
    { change t = s at ht,
      rw ht,
      split,
      { intros _,
        use hα.some,
        exact set.mem_union_right _ (h _), },
      { intros _ a,
        exact set.mem_union_right _ (h a), }, },
    { cases σ.is_quasi_strategy t ht with hσ₁ hσ₂,
      split,
      { intros ht',
        cases hσ₁ ht' with b hb,
        use b,
        exact set.mem_union_right _ hb, },
      { intros ht' b,
        exact set.mem_union_right _ (hσ₂ ht' b), }, },
  end ⟩

lemma s_quasi_strategy_extension' [hα : nonempty α] (h : ∀ a, s.concat a ∈ σ.positions)
  (h' : ∀ t ∈ σ.positions, s <+: t) :
  s_quasi_strategy (extension_of_quasi_strategy' σ s h) s :=
begin
  split,
  { left,
    exact set.mem_singleton s, },
  { intros t ht,
    cases ht,
    { change t = s at ht,
      rw ht, },
    { exact h' t ht }, },
end

lemma s_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s_quasi_strategy σ (s.concat a)) :
  s_quasi_strategy (extension_of_quasi_strategy σ s a h (s_in_s_quasi_strategy σ _ h')) s :=
begin
  split,
  { exact (quasi_strategy.positions G).mem_union_left (set.mem_singleton s), },
  { intros t ht,
    cases ht,
    { change t = s at ht,
      rw ht, },
    { calc s <+: s.concat a : list.prefix_concat a s
      ... <+: t : h'.right t ht, }, },
end

lemma is_play_of_is_play_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) (hf : is_play (union_of_quasi_strategies p g hg) f) :
  ∃ a, is_play (g a) f :=
begin
  cases hf with N' hf,
  let N := max N' (s.length + 1),
  let a := f (s.length),
  use a,
  use N,
  intros n hn,
  specialize hf n (le_of_max_le_left hn),
  cases set.mem_Union.mp hf with b hb,
  have key : a = b,
  { have h₁ := (hg' b).right (stream_prefix f n) hb,
    have h₂ : s.concat b = stream_prefix f (s.length + 1),
    { apply list.eq_of_prefix_of_length_eq,
      { apply list.prefix_of_prefix_length_le h₁ (stream_prefix_prefix f (s.length + 1) n (le_of_max_le_right hn)),
        rw list.length_concat,
        rw stream_prefix_length, },
      { rw stream_prefix_length,
        rw list.length_concat, },
    },
    have h₃ : (s.concat b).nth s.length = b,
    { simp only [list.concat_eq_append, list.nth_concat_length],
      refl, },
    rw h₂ at h₃,
    rw stream_prefix_nth at h₃,
    exact with_bot.coe_inj.mp h₃,
  },
  rw key,
  exact hb,
end

lemma winning_quasi_strategy_union (g : α → quasi_strategy G) (hg : ∀ a, (g a).player = p)
  (hg' : ∀ a, s_quasi_strategy (g a) (s.concat a)) (hg'' : ∀ a, winning (g a) X) :
  winning (union_of_quasi_strategies p g hg) X :=
begin
  intros f hf,
  cases is_play_of_is_play_union _ _ _ _ hg hg' hf with a hf,
  simp only [hg'' a f hf, hg a],
  refl,
end

lemma is_play_of_is_play_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s.concat a ∈ σ.positions) (hf : is_play (extension_of_quasi_strategy σ s a h h') f) :
  is_play σ f :=
begin
  cases hf with N' hf,
  let N := max N' (s.length + 1),
  use N,
  intros n hn,
  cases hf n (le_of_max_le_left hn) with hf₁ hf₂,
  { exfalso,
    change stream_prefix f n = s at hf₁,
    have h₁ : n ≥ s.length + 1 := le_of_max_le_right hn,
    have h₂ : (stream_prefix f n).length = n := stream_prefix_length f n,
    have h₃ : (stream_prefix f n).length = s.length := by rw hf₁,
    linarith, },
  { exact hf₂, },
end

lemma is_play_of_is_play_extension' [hα : nonempty α] (h : ∀ a, s.concat a ∈ σ.positions)
  (h' : ∀ t ∈ σ.positions, s <+: t) (hf : is_play (extension_of_quasi_strategy' σ s h) f) :
  is_play σ f :=
begin
  cases hf with N' hf,
  let N := max N' (s.length + 1),
  use N,
  intros n hn,
  cases hf n (le_of_max_le_left hn) with hf₁ hf₂,
  { exfalso,
    change stream_prefix f n = s at hf₁,
    have h₁ : n ≥ s.length + 1 := le_of_max_le_right hn,
    have h₂ : (stream_prefix f n).length = n := stream_prefix_length f n,
    have h₃ : (stream_prefix f n).length = s.length := by rw hf₁,
    linarith, },
  { exact hf₂, },
end

lemma winning_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s.concat a ∈ σ.positions) (h'' : winning σ X) :
  winning (extension_of_quasi_strategy σ s a h h') X :=
λ f hf, h'' f (is_play_of_is_play_extension _ _ _ _ h h' hf)

lemma winning_quasi_strategy_extension' [hα : nonempty α] (h : ∀ a, s.concat a ∈ σ.positions)
  (h' : ∀ t ∈ σ.positions, s <+: t) (h'' : winning σ X) :
  winning (extension_of_quasi_strategy' σ s h) X :=
λ f hf, h'' f (is_play_of_is_play_extension' _ _ _ h h' hf)

lemma s_winning_quasi_strategy_extension (a : α) (h : G.turn(s) = σ.player)
  (h' : s_quasi_strategy σ (s.concat a)) (h'' : winning σ X) :
  s_winning (extension_of_quasi_strategy σ s a h (s_in_s_quasi_strategy σ _ h')) X s :=
  ⟨s_quasi_strategy_extension _ _ _ _ _, winning_quasi_strategy_extension _ _ _ _ _ _ h''⟩

lemma s_winning_quasi_strategy_extension' [hα : nonempty α] (h : ∀ a, s.concat a ∈ σ.positions)
  (h' : ∀ t ∈ σ.positions, s <+: t) (h'' : winning σ X) :
  s_winning (extension_of_quasi_strategy' σ s h) X s :=
⟨s_quasi_strategy_extension' σ s h h', winning_quasi_strategy_extension' σ X s h h' h''⟩

instance above_s_quasi_strategy (G : game α β) (s : list α) (p : β) [hα : nonempty α] : quasi_strategy G :=
⟨ p,
  {t | s <+: t},
  begin
    intros t ht,
    split,
    { intros _, 
      use hα.some,
      calc s <+: t : ht
      ... <+: t.concat _ : list.prefix_concat _ _, },
    { intros _ a,
      calc s <+: t : ht
      ... <+: t.concat _ : list.prefix_concat _ _, },
  end ⟩

lemma above_s_is_s_quasi_strategy [hα : nonempty α] :
  s_quasi_strategy (above_s_quasi_strategy G s p) s :=
⟨(refl s : s <+: s), λ t ht, ht⟩

lemma above_s_winning_iff [hα : nonempty α] :
  winning (above_s_quasi_strategy G s p) X ↔ ∀ f, is_prefix s f → X f = p :=
begin
  split,
  { intros h f hf,
    apply h,
    use s.length,
    intros n hn,
    exact prefix_of_is_prefix s f n hf hn, },
  { intros h f hf,
    apply h,
    cases hf with n hf,
    specialize hf n rfl.ge,
    exact is_prefix_of_prefix s f n hf, },
end

instance quasi_strategy_restriction : quasi_strategy G :=
⟨ σ.player, 
  {t ∈ σ.positions | s <+: t},
  begin
    intros t ht,
    cases ht with ht₁ ht₂,
    split,
    { intros h,
      cases (σ.is_quasi_strategy t ht₁).left h with a ha,
      use a,
      split,
      { exact ha, },
      { calc s <+: t : ht₂
        ... <+: t.concat a : list.prefix_concat _ _, }, },
    { intros h a,
      obtain ha := (σ.is_quasi_strategy t ht₁).right h a,
      split,
      { exact ha, },
      { calc s <+: t : ht₂
        ... <+: t.concat a : list.prefix_concat _ _ , }, },
  end ⟩

lemma s_quasi_strategy_restriction (h : s ∈ σ.positions) :
  s_quasi_strategy (quasi_strategy_restriction σ s) s :=
⟨⟨h, refl s⟩, λ t ht, ht.right⟩

lemma is_play_restriction_of_is_play (hf : is_play σ f) (hf' : is_prefix s f):
  is_play (quasi_strategy_restriction σ s) f :=
begin
  cases hf with N' hf,
  let N := max N' s.length,
  use N,
  intros n hn,
  split,
  { exact hf n (le_of_max_le_left hn), },
  { exact prefix_of_is_prefix s f n hf' (le_of_max_le_right hn), },
end

lemma is_play_of_is_play_restriction (hf : is_play (quasi_strategy_restriction σ s) f) :
  is_play σ f :=
begin
  cases hf with N hf,
  use N,
  intros n hn,
  exact (hf n hn).left,
end

lemma winning_restriction (h : winning σ X) : winning (quasi_strategy_restriction σ s) X :=
begin
  intros f hf,
  apply h f (is_play_of_is_play_restriction σ s f hf),
end

lemma s_winning_restriction (h : s ∈ σ.positions) (h' : winning σ X) : 
  s_winning (quasi_strategy_restriction σ s) X s :=
  ⟨s_quasi_strategy_restriction _ _ h, winning_restriction _ _ _ h'⟩

-- TODO:
-- strategy from quasi-strategy (instance of quasi-strategy)
-- strategy is winning if quasi-strategy is winning
-- prove determinacy
-- prove open → is_prefix_open