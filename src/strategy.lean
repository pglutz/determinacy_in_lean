import tactic
import prefixes
import games

open list set

noncomputable theory
open_locale classical

-- We need to assume α is nonempty to construct the strategy
variables {α β : Type*} [inhabited α] {G : game α β} (σ : quasi_strategy G)

def choice_map (f : β → set α) : β → α :=
λ b, if h : (f b).nonempty then h.some else inhabited.default

lemma choice_map_def (f : β → set α) : ∀ b, (f  b).nonempty → choice_map f b ∈ f b :=
begin
  intros b hfb,
  simp [choice_map, hfb],
  exact hfb.some_mem,
end

def strategy_map_of_quasi_strategy : list α → α :=
  choice_map (λ t, {a | t.concat a ∈ σ.positions})

lemma strategy_map_of_quasi_strategy_def :
  ∀ t ∈ σ.positions, concat t (strategy_map_of_quasi_strategy σ t) ∈ σ.positions :=
begin
  intros t tpos,
  change strategy_map_of_quasi_strategy σ t ∈ {a | t.concat a ∈ σ.positions},
  unfold strategy_map_of_quasi_strategy,
  apply choice_map_def,
  by_cases G.turn t = σ.player,
  { exact (σ.is_quasi_strategy t tpos).1 h, },
  use inhabited.default,
  exact (σ.is_quasi_strategy t tpos).2 h inhabited.default,
end

def level_by_level_subtree_of_quasi_strategy :
  ℕ → set (list α)
| 0     := λ t, t ∈ σ.positions ∧ t = nil
| (n+1) := λ t, t ∈ σ.positions
                ∧ (t.init ∈ σ.positions
                    → t.init ∈ level_by_level_subtree_of_quasi_strategy n)
                ∧ (t.init ∈ σ.positions → G.turn t.init = σ.player
                    → t.ilast = strategy_map_of_quasi_strategy σ t.init)

def subtree_of_quasi_strategy : set (list α) :=
  ⋃ n, level_by_level_subtree_of_quasi_strategy σ n

lemma subtree_of_quasi_strategy_def {G : game α β} {σ : quasi_strategy G} {t : list α} :
  t ∈ subtree_of_quasi_strategy σ ↔ t ∈ level_by_level_subtree_of_quasi_strategy σ t.length :=
begin
  unfold subtree_of_quasi_strategy,
  rw mem_Union,
  refine ⟨_, λ h, ⟨t.length, h⟩⟩,
  induction h : t.length generalizing t,
  { rw eq_nil_of_length_eq_zero h,
    rintros ⟨k, hk⟩,
    cases k,
    exact hk,
    use [hk.1, rfl], },
  rintros ⟨k, hk⟩,
  cases k,
  { rw hk.2 at h, contradiction, },
  by_cases hinit : t.init ∈ σ.positions,
  { have : t.init.length = n,
    { change t.init.length = n.succ - 1,
      rw ← h,
      apply length_init, },
    use hk.1,
    split,
    { intros _, exact ih this ⟨k, (hk.2.1 hinit)⟩, },
    intros _ h, exact hk.2.2 hinit h, },
  use hk.1,
  split; intros contra; contradiction,
end

lemma position_of_position_subtree {t : list α} :
  t ∈ subtree_of_quasi_strategy σ → t ∈ σ.positions :=
begin
  rw subtree_of_quasi_strategy_def,
  cases t with h t,
  { exact λ h, h.1, },
  exact λ h, h.1,
end

lemma list.init_concat : ∀ (l : list α) (a : α), (l.concat a).init = l
| [] a := rfl
| [x] a := rfl
| (x :: y :: l) a := by simp [init]

lemma list.ilast_concat : ∀ (l : list α) (a : α), (l.concat a).ilast = a
| [] a := rfl
| [x] a := rfl
| [x, y] a := rfl
| [x, y, z] a := rfl
| (x :: y :: z :: l) a := by {  simp [ilast],
                                rw [← cons_append, ← concat_append, append_nil],
                                apply list.ilast_concat, }

lemma list.nil_of_prefix_init {l : list α} : l <+: l.init → l = nil :=
begin
  intros h,
  apply eq_nil_of_length_eq_zero,
  have := h.length_le,
  rw l.length_init at this,
  linarith,
end

instance strategy_of_quasi_strategy : quasi_strategy G :=
{ player := σ.player,
  positions := subtree_of_quasi_strategy σ,
  is_quasi_strategy :=
  begin
    intros t ht,
    rw subtree_of_quasi_strategy_def at ht,
    -- Didn't need induction, just two cases
    cases h : t,
    { rw h at ht,
      split,
      { intros turn,
        use strategy_map_of_quasi_strategy σ nil,
        rw subtree_of_quasi_strategy_def,
        use strategy_map_of_quasi_strategy_def σ nil ht.1,
        split,
        { intros _,
          change nil ∈ level_by_level_subtree_of_quasi_strategy σ 0,
          use [ht.1, rfl], },
        intros _ _,
        exact rfl, },
      intros turn a,
      rw subtree_of_quasi_strategy_def,
      use [(σ.is_quasi_strategy nil ht.1).2 turn a],
      split,
      { intros _,
        change nil ∈ level_by_level_subtree_of_quasi_strategy σ 0,
        use [ht.1, rfl], },
      intros _ contra,
      exfalso,
      change game.turn nil = _ at contra,
      exact turn contra, },
    have hn : t.length = tl.length + 1,
    { rw h, simp, },
    rw ← h,
    rw hn at ht,
    rcases ht with ⟨ht, ⟨tinit, tplay⟩⟩,
    split,
    { intros turn,
      use strategy_map_of_quasi_strategy σ t,
      rw subtree_of_quasi_strategy_def,
      simp only [length_concat],
      use strategy_map_of_quasi_strategy_def σ t ht,
      rw list.init_concat,
      split,
      { intros _,
        rw hn,
        unfold level_by_level_subtree_of_quasi_strategy,
        use [ht, tinit, tplay], },
      intros _ _,
      rw list.ilast_concat, },
    intros turn a,
    rw subtree_of_quasi_strategy_def,
    simp only [length_concat],
    unfold level_by_level_subtree_of_quasi_strategy,
    use [(σ.is_quasi_strategy t ht).2 turn a],
    rw list.init_concat,
    split,
    { intros _,
      rw hn,
      unfold level_by_level_subtree_of_quasi_strategy,
      use [ht, tinit, tplay], },
    intros _ contra,
    exfalso,
    exact turn contra,
  end }

theorem is_strategy_of_quasi_strategy :
  is_strategy (strategy_of_quasi_strategy σ) :=
begin
  intros t tpos tturn,
  use strategy_map_of_quasi_strategy σ t,
  split,
  { change t.concat (strategy_map_of_quasi_strategy σ t) ∈ (subtree_of_quasi_strategy σ),
    rw subtree_of_quasi_strategy_def,
    simp only [length_concat],
    split,
    { apply strategy_map_of_quasi_strategy_def,
      apply position_of_position_subtree,
      exact tpos, },
    split,
    { intros _,
      rw list.init_concat,
      rw ← subtree_of_quasi_strategy_def,
      exact tpos, },
    intros _ _,
    rw [list.ilast_concat, list.init_concat], },
  intros a tapos,
  change t.concat a ∈ subtree_of_quasi_strategy σ at tapos,
  rw [subtree_of_quasi_strategy_def, length_concat] at tapos,
  rcases tapos with ⟨_, ⟨_, h⟩⟩,
  rw [list.init_concat, list.ilast_concat] at h,
  exact h (position_of_position_subtree σ tpos) tturn,
end

lemma in_subtree_of_quasi_strategy (s : list α) :
  s ∈ σ.positions ∧ (s ≠ nil → s.init ∉ σ.positions) → s ∈ subtree_of_quasi_strategy σ :=
begin
  rintros ⟨hs, hsinit⟩,
  rw subtree_of_quasi_strategy_def,
  cases s,
  { use hs, },
  use hs,
  have : s_hd :: s_tl ≠ nil,
  { simp, },
  have hsinit := hsinit this,
  split,
  { intros contra, contradiction, },
  intros contra, contradiction,
end

lemma s_strategy_of_s_quasi_strategy (s : list α) :
  s_quasi_strategy σ s → s_quasi_strategy (strategy_of_quasi_strategy σ) s :=
begin
  intros hs,
  split,
  { apply in_subtree_of_quasi_strategy,
    use hs.1,
    contrapose!,
    intros hsinit,
    exact list.nil_of_prefix_init (hs.2 s.init hsinit), },
  intros t tpos,
  have : t ∈ σ.positions,
  { apply position_of_position_subtree σ tpos, },
  exact hs.2 t this,
end

variables (X : (ℕ → α) → β)

theorem winning_strategy_of_winning_quasi_strategy :
  winning σ X → winning (strategy_of_quasi_strategy σ) X :=
begin
  intros winning,
  intros f fplay,
  change X f = σ.player,
  apply winning f,
  cases fplay with N hN,
  use N,
  intros n hn,
  apply position_of_position_subtree,
  exact hN n hn,
end