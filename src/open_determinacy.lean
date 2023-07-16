import sequences
import games

open finseq nat set game_tree game

noncomputable theory
open_locale classical

universes u

section open_determinacy

parameters {E : ℕ → Type u} (G : game E bool) (P : bool)

def is_open := ∀ α ∈ G.plays, G.payoff α = P → ∃ n, α.restrict n ∈ G.winning_positions P n

lemma winnable_position_of_turn_of_exists_winnable_move {n} (σ : finseq E n) :
  G.turn σ = P → (∃ x ∈ G.moves σ, σ ⌢ x ∈ G.winnable_positions P (n+1)) →
    σ ∈ G.winnable_positions P n :=
begin
  rintros turn ⟨x, ⟨xmove, ⟨T, ⟨⟨Tsubtree, Tstrat⟩, Twinning⟩⟩⟩⟩,
  let moves : Π {{k}} (τ : finseq E k), set (E k) :=
    λ k τ,
      if h : k = n
        then if (cast (congr_arg (finseq E) h.symm) σ) = τ
          then { cast (congr_arg E h.symm) x }
          else T.moves τ
        else T.moves τ,
  let S : game_tree E := ⟨moves⟩,
  have SsubT : S ∈ T.subtrees := by {
    intros k τ,
    by_cases h : k = n,
    { by_cases h' : (cast (congr_arg (finseq E) h.symm) σ) = τ,
      { cases h,
        cases h',
        simp [moves],
        apply move_of_position_cat,
        exact Twinning.1 },
      simp [moves, h, h'] },
    simp [moves, h]
  },
  have Sstrat : S ∈ G.quasi_strategies P := by {
    split,
    { exact is_subtree.trans SsubT Tsubtree },
    intros k τ τpos,
    have τposT := T.position_of_subtree_position S SsubT τpos,
    by_cases h : k = n,
    { by_cases h' : (cast (congr_arg (finseq E) h.symm) σ) = τ,
      { cases h,
        cases h',
        split,
        { simp [moves] },
        contradiction },
      simp [moves, h, h'],
      exact Tstrat τ τposT },
    simp [moves, h],
    exact Tstrat τ τposT
  },
  have Swinning : σ ∈ (G.subgame S).winning_positions P n := by {
    split,
    { intros k hkn,
      change σ.nth k hkn ∈ moves (σ.restrict k _),
      simp [moves, ne_of_lt hkn],
      have := Twinning.1 (lt_succ_of_lt hkn),
      simp [ne_of_lt hkn, ne_of_lt (lt_succ_of_lt hkn)] at this,
      exact this },
    split,
    { intros α αplay hσα,
      split,
      { exact αplay },
      have : σ ⌢ x << α := by {
        change α.restrict n = σ at hσα,
        simp [hσα],
        have h₁ : α n ∈ S.moves (α.restrict n) := αplay n,
        have h₂ : S.moves σ = { x } := by simp [moves],
        rw [hσα, h₂] at h₁,
        exact h₁
      },
      apply (Twinning.2.1 _ _ this).2,
      exact play_of_subtree_play _ _ SsubT αplay },
    intros k τ τplay hστ,
    split,
    { exact τplay },
    have h₀ : k ≠ n := by {
      have := τplay.2,
      contrapose! this,
      apply nonempty.ne_empty,
      cases this,
      cases (eq_of_prefix_of_length_eq hστ),
      use x,
      change x ∈ moves σ,
      simp [moves]
    },
    have : σ ⌢ x << τ := by {
      cases hστ with h' h,
      have : n < k := lt_of_le_of_ne h' h₀.symm,
      use this,
      rw ← (cat_restrict (τ.restrict (n+1) this)),
      simp,
      split,
      { exact h },
      have h₁ : τ.nth n this ∈ S.moves σ := by {
        rw ← h,
        apply τplay.1
      },
      have h₂ : S.moves σ = { x } := by simp [moves],
      rw h₂ at h₁,
      exact h₁
    },
    apply (Twinning.2.2 _ _ this).2,
    split,
    { exact T.position_of_subtree_position S SsubT τplay.1 },
    have h₁ : S.moves τ = T.moves τ := by simp [h₀],
    change T.moves τ = ∅,
    rw ← h₁,
    exact τplay.2
  },
  use [S, Sstrat, Swinning]
end

lemma winnable_position_of_not_turn_of_no_losing_move {n} (σ : finseq E n) :
  G.turn σ ≠ P → σ ∈ G.positions n → (G.moves σ = ∅ → G.taboo σ = P) →
    (∀ x ∈ G.moves σ, σ ⌢ x ∈ G.winnable_positions P (n+1)) → σ ∈ G.winnable_positions P n :=
begin
  rintros turn σpos σtaboo hσ,
  have : ∀ x : E n, ∃ T ∈ G.quasi_strategies P,
    x ∈ G.moves σ → G.is_winning_quasi_strategy_at_position T P (σ ⌢ x) := by {
    intros x,
    by_cases h : x ∈ G.moves σ,
    { cases hσ x h with T hT,
      use [T, hT.1],
      intros _,
      exact hT },
    use G.to_game_tree,
    split,
    { reflexivity },
    intros h',
    contradiction
  },
  cases (classical.axiom_of_choice this) with T hT,
  let moves : Π {{k}} (τ : finseq E k), set (E k) :=
    λ k τ,
      if h : n < k ∧ σ << τ
        then let x := τ.nth n h.1 in (T x).moves τ
        else G.moves τ,
  let S : game_tree E := ⟨moves⟩,
  have SsubT₀ : ∀ {{k}} {τ : finseq E k} {h : n < k},
    σ << τ → τ ∈ S.positions k → τ ∈ (T (τ.nth n h)).positions k :=
  begin
    intros k τ hk hστ τpos,
    generalize hx : τ.nth n hk = x,
    intros l hlk,
    by_cases h : n < l,
    { have h₀ : σ << τ.restrict l (le_of_lt hlk) := by {
        apply prefix_of_prefix_length_le hστ _ (le_of_lt h),
        simp
      },
      have h₁ : (τ.restrict l (le_of_lt hlk)).nth n h = x := by simp [hx],
      have := τpos hlk,
      simp [moves, h, h₀] at this,
      rw h₁ at this,
      exact this },
    have h : l ≤ n := le_of_not_lt h,
    have h₀ : x ∈ G.moves σ := by {
      have := τpos hk,
      simp [moves] at this,
      rw [hx, hστ.snd] at this,
      exact this
    },
    have h₁ : (σ ⌢ x) ∈ (T x).positions (n+1) := ((hT x).snd h₀).2.1,
    have h₂ : σ ⌢ x = τ.restrict (n+1) hk := by {
      have h' : τ.nth n hk = (τ.restrict (n+1) hk).nth n (lt_succ_self _) := by simp,
      have h'' : τ.restrict n (le_of_lt hk) =
                  (τ.restrict (n+1) hk).restrict n (le_succ _) := by {
        symmetry,
        apply restrict_restrict
      },
      rw [← hστ.snd, ← hx, h', h''],
      apply cat_restrict
    },
    have h₃ : τ.nth l hlk = (σ ⌢ x).nth l (lt_succ_of_le h) := by simp [h₂],
    have h₄ : τ.restrict l (le_of_lt hlk) = (σ ⌢ x).restrict l (le_succ_of_le h) := by {
      rw h₂,
      symmetry,
      apply restrict_restrict
    },
    rw [h₃, h₄],
    exact h₁ (lt_succ_of_le h)
  end,
  have SsubT₁ : ∀ {α : seq E}, σ << α → α ∈ S.plays → α ∈ (T (α n)).plays :=
  begin
    intros α hσα αplay k,
    let m := max n k + 1,
    have h₀ : n < m := by {
      simp [m],
      apply lt_succ_of_le,
      apply le_max_left
    },
    have h₁ : k < m := by {
      simp [m],
      apply lt_succ_of_le,
      apply le_max_right
    },
    have h₂ : σ << α.restrict m :=
      seq.prefix_of_prefix_length_le hσα (seq.restrict_prefix _ _) (le_of_lt h₀),
    have h₃ : α.restrict m ∈ S.positions m :=
      position_of_prefix_play _ _ _ αplay (seq.restrict_prefix _ _),
    have h₄ : (α.restrict m).nth k h₁ = α k := seq.nth_restrict _ _,
    have h₅ : (α.restrict m).nth n h₀ = α n := seq.nth_restrict _ _,
    have h₆ : (α.restrict m).restrict k (le_of_lt h₁) = α.restrict k :=
      seq.restrict_restrict _,
    have h₇ := (SsubT₀ h₂ h₃) h₁,
    rw [h₄, h₅, h₆] at h₇,
    exact h₇
  end,
  have Sstrat : S ∈ G.quasi_strategies P := by {
    split; intros k τ,
    { by_cases h : n < k ∧ σ << τ; simp [moves, h],
      exact ((hT (τ.nth n h.1)).fst).1 τ },
    intros τpos,
    by_cases h : n < k ∧ σ << τ; simp [moves, h],
    apply ((hT (τ.nth n h.1)).fst).2 τ,
    exact SsubT₀ h.2 τpos
  },
  have Swinning : σ ∈ (G.subgame S).winning_positions P n := by {
    split,
    { intros k hk,
      have h : ¬ (n < k ∧ σ << (σ.restrict k (le_of_lt hk))) := by {
        rw not_and_distrib,
        left,
        exact has_lt.lt.asymm hk
      },
      change σ.nth k hk ∈ moves (σ.restrict k _),
      simp [moves, h, σpos hk] },
    split,
    { intros α αplay hσα,
      split,
      { exact αplay },
      have h₀ : α n ∈ G.moves σ := by {
        cases hσα,
        exact mem_of_mem_of_subset (αplay n) (Sstrat.1 _)
      },
      have h₁ : σ ⌢ (α n) << α := by {
        simp,
        exact hσα
      },
      have h₂ : α ∈ (T (α n)).plays := SsubT₁ hσα αplay,
      exact ((((hT (α n))).snd h₀).2.2.1 _ h₂ h₁).2
    },
    intros k τ τplay hστ,
    split,
    { exact τplay },
    by_cases h₀ : n = k,
    { cases h₀,
      cases (eq_of_prefix_of_length_eq hστ),
      apply σtaboo,
      rw ← (Sstrat.2 σ τplay.1).2 turn,
      exact τplay.2
    },
    have h₁ : n < k := lt_of_le_of_ne hστ.fst h₀,
    let x := τ.nth n h₁,
    have h₂ : x ∈ G.moves σ := by {
      apply mem_of_mem_of_subset _ (Sstrat.1 _),
      rw ← hστ.snd,
      exact τplay.1 h₁
    },
    have h₃ : σ ⌢ x << τ := by {
      cases hστ with h' h,
      use h₁,
      rw ← (cat_restrict (τ.restrict (n+1) h₁)),
      simp,
      exact h
    },
    have h₄ : τ ∈ (T x).finite_plays k := by {
      split,
      { exact SsubT₀ hστ τplay.1 },
      show (T x).moves τ = ∅,
      have : (T x).moves τ = moves τ := by simp [moves, h₁, hστ],
      rw this,
      exact τplay.2
    },
    exact ((((hT x)).snd h₂).2.2.2 τ h₄ h₃).2
  },
  use [S, Sstrat, Swinning]
end

-- TODO : should we extract from this proof the contruction of the non-losing quasi-strategy?
-- It may be useful elsewhere

theorem open_quasi_determinacy : is_open → G.is_quasi_determined :=
begin
  intros hopen,
  by_cases G.is_winnable P,
  { exact ⟨P, h⟩ },
  have fact₁ : ∀ {{n}} (σ : finseq E n), G.turn σ ≠ P → σ ∈ G.positions n →
    σ ∉ G.winnable_positions P n → (σ ∈ G.finite_plays n ∧ G.taboo σ ≠ P)
      ∨ ∃ x ∈ G.moves σ, σ ⌢ x ∉ G.winnable_positions P (n+1) :=
  begin
    intros n σ σturn σpos,
    contrapose!,
    rintros ⟨h₀, h₁⟩,
    by_cases h₂ : G.moves σ = ∅,
    { simp [winnable_positions],
      use G.to_game_tree,
      split,
      { reflexivity },
      have h₃ : σ ∈ G.finite_plays n := ⟨σpos, h₂⟩,
      exact winning_position_of_finite_play_of_taboo _ _ _ h₃ (h₀ h₃) },
    apply winnable_position_of_not_turn_of_no_losing_move _ σturn σpos _ h₁,
    intros,
    contradiction
  end,
  have fact₂ : ∀ {{n}} (σ : finseq E n), G.turn σ = P → σ ∉ G.winnable_positions P n →
    ∀ x ∈ G.moves σ, σ ⌢ x ∉ G.winnable_positions P (n+1) :=
  begin
    intros n σ σturn,
    contrapose!,
    intros H,
    apply winnable_position_of_turn_of_exists_winnable_move,
      exact σturn,
    rcases H with ⟨x, ⟨h₀, h₁⟩⟩,
    use [x, h₀, h₁]
  end,
  let moves : Π {{k}} (τ : finseq E k), set (E k) :=
    λ n σ,
      if h : G.turn σ ≠ P ∧ σ ∉ G.winnable_positions P n
        then { x ∈ G.moves σ | σ ⌢ x ∉ G.winnable_positions P (n+1) }
        else G.moves σ,
  let S : game_tree E := ⟨moves⟩,
  have Ssub : S ∈ G.subtrees :=
  begin
    intros n σ,
    by_cases h : turn σ ≠ P ∧ σ ∉ G.winnable_positions P n,
    { have : S.moves σ = {x ∈ game_tree.moves σ | σ ⌢ x ∉ G.winnable_positions P (n + 1)} :=
        by simp [moves, h],
      rw this,
      simp },
    have : S.moves σ = G.moves σ := by simp [moves, h],
    rw this
  end,
  have Sprop : ∀ {{n}} (σ : finseq E n), σ ∈ S.positions n →
    σ ∉ G.winnable_positions P n :=
  begin
    intros n σ,
    induction σ with n σ x ih,
    { intros _,
      exact h },
    intros h₀,
    have h₁ : σ ∈ S.positions n := position_of_position_cat _ h₀,
    have h₂ : σ ∉ G.winnable_positions P n := ih h₁,
    have h₃ : x ∈ S.moves σ := by {
      have := h₀ (lt_succ_self _),
      simp at this,
      exact this
    },
    by_cases h : G.turn σ = P,
    { apply fact₂ _ h h₂,
      apply Ssub σ,
      exact h₃ },
    have h₄ : S.moves σ = {x ∈ game_tree.moves σ | σ ⌢ x ∉ G.winnable_positions P (n + 1)} :=
    begin
      simp [moves],
      intros h',
      exfalso,
      exact h₂ (h' h)
    end,
    rw h₄ at h₃,
    exact h₃.2
  end,
  have Sstrat : S ∈ G.quasi_strategies (!P) :=
  begin
    split,
    { exact Ssub },
    intros n σ σpos,
    split; intros σturn,
    { have h₀ : G.turn σ ≠ P :=  by cases G.turn σ; cases P; simp at σturn; contradiction,
      have h₁ : σ ∉ G.winnable_positions P n := Sprop _ σpos,
      have h₂ := fact₁ _ h₀ (position_of_subtree_position _ _ Ssub σpos) h₁,
      cases h₂,
      { intros h,
        have : G.moves σ = ∅ := h₂.1.2,
        exfalso,
        exact (nonempty.ne_empty h) this },
      rcases h₂ with ⟨x, ⟨xmove, hx⟩⟩,
      intros _,
      have h₂ : S.moves σ = {x ∈ G.moves σ | σ ⌢ x ∉ G.winnable_positions P (n + 1)} :=
      begin
        simp [moves],
        intros h,
        exfalso,
        exact h₁ (h h₀)
      end,
      rw h₂,
      use [x, ⟨xmove, hx⟩] },
    have h₀ : G.turn σ = P := by cases G.turn σ; cases P; simp at σturn; contradiction,
    simp [moves, h₀]
  end,
  have Swinning : null ∈ (G.subgame S).winning_positions (!P) 0 :=
  begin
    split,
    { simp [positions] },
    split,
    { intros α αplay _,
      split,
      { exact αplay },
      have h₀ : ¬ G.payoff α = P → G.payoff α = !P := by cases G.payoff α; cases P; simp,
      apply h₀,
      intros αpayoff,
      cases hopen α (play_of_subtree_play _ _ Ssub αplay) αpayoff with n h,
      have h₁ : α.restrict n ∈ S.positions n := by {
        apply S.position_of_prefix_play _ _ αplay,
        simp
      },
      have h₂ : α.restrict n ∈ G.winnable_positions P n := by {
        use G.to_game_tree,
        split,
        { reflexivity },
        exact h
      },
      exact (Sprop (α.restrict n) h₁) h₂ },
    intros n σ σplay _,
    split,
    { exact σplay },
    have h₀ : ¬ G.taboo σ = P → G.taboo σ = !P := by cases G.taboo σ; cases P; simp,
    apply h₀,
    intros σtaboo,
    have : σ ∈ G.winnable_positions P n := by {
      apply winnable_position_of_winning_position,
      apply winning_position_of_finite_play_of_taboo,
      { split,
        { exact position_of_subtree_position _ _ Ssub σplay.1 },
        have : S.moves σ = ∅ → G.moves σ = ∅ := by {
          contrapose!,
          by_cases h : G.turn σ = !P,
          { rw [← nonempty_iff_ne_empty, ← nonempty_iff_ne_empty],
            exact (Sstrat.2 σ σplay.1).1 h },
          rw ← (Sstrat.2 σ σplay.1).2 h,
          simp
        },
        exact this σplay.2 },
      exact σtaboo
    },
    exact (Sprop σ σplay.1) this
  end,
  use [!P, S, Sstrat, Swinning]
end

theorem open_determinacy : is_open → G.is_determined :=
G.determined_of_quasi_determined ∘ open_quasi_determinacy

end open_determinacy
