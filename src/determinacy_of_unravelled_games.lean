import tactic
import games_with_taboos
import data.nat.parity
import unravellings
import prefixes

open set list

noncomputable theory
open_locale classical

-- If G covers G' and G is determined, then so is G'

section determined_of_unravelling_of_determined

variables {α β : Type*} {T : set (list α)} {A : set (ℕ → α)}
          (G : game T A) {T' : set (list β)} {B : set (ℕ → β)}
          (G' : game T' B) {π : list α → list β} {φ : (list α → α) → (list β → β)}

lemma winning_of_image_of_winning₁ (hc : covering T T' π φ) :
  ∀ σ ∈ @strategies _ T G.to_game_tree, winning_strategy₁ (lifted_game T G' hc) σ (by assumption)
    → winning_strategy₁ G' (φ σ) (strategy_of_strategy_map T T' φ σ (by assumption)) :=
begin
  rintros σ hσ ⟨hσwf, hσwi⟩,
  split,
  { intros p hpφσ,
    rcases hc.finite_lifting₁ σ hσ p hpφσ with ⟨p', ⟨hp'c, ⟨hp'p, hp't | hp't⟩⟩⟩,
    { have : p' ∈ game_tree_with_taboos.taboos₂ T := hσwf p' hp'c,
      have : π p' ∈ game_tree_with_taboos.taboos₂ T' :=
        mem_of_mem_of_subset (mem_image_of_mem _ this) (image_subset_iff.mpr hc.taboos_lift₂),
      rwa ← hp't, },
    exfalso,
    have : p' ∈ game_tree_with_taboos.taboos₂ T := hσwf p' hp'c,
    have : (game_tree_with_taboos.taboos₁ T ∩ game_tree_with_taboos.taboos₂ T).nonempty :=
      nonempty_of_mem (mem_inter hp't this),
    apply this.ne_empty game_tree_with_taboos.taboos_disjoint, },
  intros f hfφσ,
  rcases hc.infinite_lifting₁ σ hσ f hfφσ with ⟨f', ⟨hf'c, ⟨hf'p, hf't⟩⟩⟩ | ⟨f', ⟨hf'c, hf'f⟩⟩,
  { exfalso,
    have : f' ∈ game_tree_with_taboos.taboos₂ T := hσwf f' hf'c,
    have : (game_tree_with_taboos.taboos₁ T ∩ game_tree_with_taboos.taboos₂ T).nonempty :=
      nonempty_of_mem (mem_inter hf't this),
    apply this.ne_empty game_tree_with_taboos.taboos_disjoint, },
  rw ← hf'f,
  exact mem_preimage.mp (mem_of_mem_inter_left (hσwi f' hf'c)),
end

lemma winning_of_image_of_winning₂ (hc : covering T T' π φ) :
  ∀ τ ∈ @strategies _ T G.to_game_tree, winning_strategy₂ (lifted_game T G' hc) τ (by assumption)
    → winning_strategy₂ G' (φ τ) (strategy_of_strategy_map T T' φ τ (by assumption)) :=
begin
  rintros τ hτ ⟨hτwf, hτwi⟩,
  split,
  { intros p hpφτ,
    rcases hc.finite_lifting₂ τ hτ p hpφτ with ⟨p', ⟨hp'c, ⟨hp'p, hp't | hp't⟩⟩⟩,
    { have : p' ∈ game_tree_with_taboos.taboos₁ T := hτwf p' hp'c,
      have : π p' ∈ game_tree_with_taboos.taboos₁ T' :=
        mem_of_mem_of_subset (mem_image_of_mem _ this) (image_subset_iff.mpr hc.taboos_lift₁),
      rwa ← hp't, },
    exfalso,
    have : p' ∈ game_tree_with_taboos.taboos₁ T := hτwf p' hp'c,
    have : (game_tree_with_taboos.taboos₁ T ∩ game_tree_with_taboos.taboos₂ T).nonempty :=
      nonempty_of_mem (mem_inter this hp't),
    apply this.ne_empty game_tree_with_taboos.taboos_disjoint, },
  intros f hfφτ,
  rcases hc.infinite_lifting₂ τ hτ f hfφτ with ⟨f', ⟨hf'c, ⟨hf'p, hf't⟩⟩⟩ | ⟨f', ⟨hf'c, hf'f⟩⟩,
  { exfalso,
    have : f' ∈ game_tree_with_taboos.taboos₁ T := hτwf f' hf'c,
    have : (game_tree_with_taboos.taboos₁ T ∩ game_tree_with_taboos.taboos₂ T).nonempty :=
      nonempty_of_mem (mem_inter this hf't),
    apply this.ne_empty game_tree_with_taboos.taboos_disjoint, },
  rw ← hf'f,
  intros h,
  have : f' ∈ hc.induced_map ⁻¹' B ∩ infinite_plays T := mem_inter h hf'c.1,
  exact (hτwi f' hf'c) this,
end

theorem determined_of_unravelling_of_determined₁ : covers G G' → determined₁ G → determined₁ G' :=
begin
  intros hu hd,
  rcases hu with ⟨π, ⟨φ, ⟨hc, heq⟩⟩⟩,
  rcases hd with ⟨σ, ⟨hσ, hσw⟩⟩,
  use [φ σ, @strategy_of_strategy_map _ _ T _ T' _ φ hc.to_strategies_map σ hσ],
  apply winning_of_image_of_winning₁ G G' hc,
  unfold winning_strategy₁,
  unfold eq_game at heq,
  conv in (_ ∩ infinite_plays T) { rw ← heq.2.1 },
  exact hσw,
end

theorem determined_of_unravelling_of_determined₂ : covers G G' → determined₂ G → determined₂ G' :=
begin
  intros hu hd,
  rcases hu with ⟨π, ⟨φ, ⟨hc, heq⟩⟩⟩,
  rcases hd with ⟨τ, ⟨hτ, hτw⟩⟩,
  use [φ τ, @strategy_of_strategy_map _ _ T _ T' _ φ hc.to_strategies_map τ hτ],
  apply winning_of_image_of_winning₂ G G' hc,
  unfold winning_strategy₂,
  unfold eq_game at heq,
  conv in (_ ∩ infinite_plays T) { rw ← heq.2.1 },
  exact hτw,
end

theorem determined_of_unravelling_of_determined : covers G G' → determined G → determined G' :=
begin
  intros hu hd,
  rcases hd with hd₁ | hd₂,
  { left,
    exact determined_of_unravelling_of_determined₁ _ _ hu hd₁, },
  right,
  exact determined_of_unravelling_of_determined₂ _ _ hu hd₂,
end

end determined_of_unravelling_of_determined

-- We now show that closed (and in particular clopen) games are determined

section clopen_determinacy

variables {α : Type*} {T : set (list α)} {A : set (ℕ → α)} (G : game T A) [nonempty α]

def follow_p_strategy (p ∈ T) : list α → α :=
λ t, if h : t <+: p ∧ t.length < p.length
     then nth_le p t.length h.2
     else let legal_moves := {a : α | @is_legal_move _ T G.to_game_tree t a} in
          if h' : legal_moves.nonempty
          then set.nonempty.some h'
          else classical.arbitrary α

lemma follow_p_strategy_is_strategy (p ∈ T) :
  follow_p_strategy G p (by assumption) ∈ strategies (localized_subtree T p) :=
begin
  simp [is_strategy],
  intros t ht hlt,
  by_cases h : t <+: p ∧ t.length < p.length,
  { have : follow_p_strategy G p H t = nth_le p t.length h.2,
    { unfold follow_p_strategy, simp [h], },
    rw this,
    have : t.concat (nth_le p t.length h.2) <+: p := concat_prefix_of_length_lt_of_prefix h.2 h.1,
    refine game_tree.prefix_closed _ _ this _,
    exact ⟨H, or.inl prefix_rfl⟩, },
  let legal_moves := {a : α | @is_legal_move _ T G.to_game_tree t a},
  have h' : legal_moves.nonempty,
  { change ∃ a, is_legal_move T t a,
    cases hlt with a ha,
    use a,
    exact ha.1, },
  have : follow_p_strategy G p H t = set.nonempty.some h',
  { unfold follow_p_strategy, simp [h, h'], },
  rw this,
  have : h'.some ∈ {a : α | @is_legal_move _ T G.to_game_tree t a} := h'.some_mem,
  refine ⟨this, _⟩,
  right,
  have : p <+: t,
  { cases ht.2 with htp,
    { have : t = p,
      { apply eq_of_prefix_of_length_eq htp,
        push_neg at h,
        linarith [h htp, htp.length_le], },
      rw this, },
    assumption, },
  apply this.trans (prefix_concat _ _),
end

lemma p_consistent_with_follow_p_strategy₁ (p ∈ T) :
  consistent_position₂ (localized_subtree T p) (follow_p_strategy G p (by assumption))
    (follow_p_strategy_is_strategy G p (by assumption)) p :=
begin
  unfold consistent_position₂,
  refine ⟨⟨H, or.inl prefix_rfl⟩, _⟩,
  intros k hk hko,
  have : take k p <+: p ∧ (take k p).length < p.length,
  { split,
    apply take_prefix,
    linarith [length_take_le k p], },
  unfold follow_p_strategy, simp [this],
  have : min k p.length = k := min_eq_left_of_lt hk,
  apply option.some_inj.mp,
  rw ← nth_le_nth hk,
  rw ← nth_le_nth _,
  rw this,
end

-- def winning_position₁ (p : list α) := p ∈ T → determined₁ (localized_game G p (by assumption))

def losing_position₁ (p : list α) := p ∈ T → determined₂ (localized_game G p (by assumption))

lemma losing_position_def₁ (p : list α) : losing_position₁ G p ↔
  ∃ τ ∈ strategies (localized_subtree T p), p ∈ T →
    winning_strategy₂ (localized_game G p (by assumption)) τ (by assumption) :=
sorry

lemma losing_of_taboo₁ (p ∈ G.taboos₁) :
  losing_position₁ G p :=
begin
  unfold losing_position₁ determined₂,
  intros hpinT,
  use follow_p_strategy G p hpinT,
  use follow_p_strategy_is_strategy G p hpinT,
  split,
  { intros q hτqc,
    simp at hτqc,
    change q ∈ game_tree_with_taboos.taboos₁ T ∧ q ∈ (localized_subtree T p),
    refine ⟨_, hτqc.1.1⟩,
    have hp : ¬ has_legal_move (localized_subtree T p) p,
    { have : ¬ has_legal_move T p := (mem_of_mem_of_subset H (taboos_subset_finite_plays₁ T)).2,
      contrapose! this,
      cases this with a ha,
      use a,
      apply mem_of_mem_of_subset ha (localized_subtree_subset T p), },
    have : p = q,
    { by_contradiction,
      cases hτqc.1.1.2 with h₂ h₂,
      { apply hτqc.1.2,
        refine has_legal_move_of_prefix_of_ne_of_in_tree (localized_subtree T p) h₂ _ _,
        { intros he, apply h he.symm, },
        split,
        { apply hpinT, },
        left, apply prefix_rfl, },
      apply hp (has_legal_move_of_prefix_of_ne_of_in_tree (localized_subtree T p) h₂ h hτqc.1.1), },
    rwa ← this, },
  intros f hτfc,
  exfalso,
  have hpt : p ∈ finite_plays T,
  { apply mem_of_mem_of_subset H (taboos_subset_finite_plays₁ T), },
  apply hpt.2,
  have : p = stream_prefix f p.length,
  { have : stream_prefix f p.length ∈ (localized_subtree T p) := hτfc.1 _,
    cases this.2,
    apply (eq_of_prefix_of_length_eq h (stream_prefix_length f p.length)).symm,
    apply eq_of_prefix_of_length_eq h (stream_prefix_length f p.length).symm, },
  rw this,
  use f p.length,
  change stream_prefix f (p.length + 1) ∈ T,
  apply mem_of_mem_of_subset (hτfc.1 _) (localized_subtree_subset T p),
end

-- lemma winning_of_taboo₂ (p ∈ G.taboos₂) :
--   winning_position₁ G p :=
-- begin
--   unfold winning_position₁ determined₁,
--   intros hpinT,
--   use follow_p_strategy G p hpinT,
--   use follow_p_strategy_is_strategy G p hpinT,
--   split,
--   { intros q hτqc,
--     simp at hτqc,
--     change q ∈ game_tree_with_taboos.taboos₂ T ∧ q ∈ (localized_subtree T p),
--     refine ⟨_, hτqc.1.1⟩,
--     have hp : ¬ has_legal_move (localized_subtree T p) p,
--     { have : ¬ has_legal_move T p := (mem_of_mem_of_subset H (taboos_subset_finite_plays₂ T)).2,
--       contrapose! this,
--       cases this with a ha,
--       use a,
--       apply mem_of_mem_of_subset ha (localized_subtree_subset T p), },
--     have : p = q,
--     { by_contradiction,
--       cases hτqc.1.1.2 with h₂ h₂,
--       { apply hτqc.1.2,
--         refine has_legal_move_of_prefix_of_ne_of_in_tree (localized_subtree T p) h₂ _ _,
--         { intros he, apply h he.symm, },
--         split,
--         { apply hpinT, },
--         left, apply prefix_rfl, },
--       apply hp (has_legal_move_of_prefix_of_ne_of_in_tree (localized_subtree T p) h₂ h hτqc.1.1), },
--     rwa ← this, },
--   intros f hσfc,
--   exfalso,
--   have hpt : p ∈ finite_plays T,
--   { apply mem_of_mem_of_subset H (taboos_subset_finite_plays₂ T), },
--   apply hpt.2,
--   have : p = stream_prefix f p.length,
--   { have : stream_prefix f p.length ∈ (localized_subtree T p) := hσfc.1 _,
--     cases this.2,
--     apply (eq_of_prefix_of_length_eq h (stream_prefix_length f p.length)).symm,
--     apply eq_of_prefix_of_length_eq h (stream_prefix_length f p.length).symm, },
--   rw this,
--   use f p.length,
--   change stream_prefix f (p.length + 1) ∈ T,
--   apply mem_of_mem_of_subset (hσfc.1 _) (localized_subtree_subset T p),
-- end

def never_lose_strategy₁ : list α → α :=
λ t, let P := {a : α | is_legal_move T t a ∧ ¬ losing_position₁ G (t.concat a)} in
     if h : P.nonempty
     then set.nonempty.some h
     else classical.arbitrary α

-- TODO: this proof is terrible...
-- TODO: create lemmas for the following:
   -- stream_prefix f n nth k = f k
   -- if τ is a strategy for the localized tree at p, and t <+ p and t ≠ p,
   -- then τ (t) = p.nth t.length
lemma extension_of_not_losing₁ (p : list α) : p ∈ T → even p.length → p ∉ G.taboos₂ →
  ¬ losing_position₁ G p → ∃ a : α, ¬ losing_position₁ G (p.concat a) :=
begin
  sorry
  -- intros hpT hevenp hpnt₂,
  -- contrapose!,
  -- intros halosing,
  -- conv at halosing in (losing_position₁ _ _) { rw losing_position_def₁ _, },
  -- choose τa τastrat τawinning₂ using halosing,
  -- let τ : list α → α :=
  --   λ t, if h : p <+: t ∧ p.length < t.length
  --        then τa (t.nth_le p.length h.2) t
  --        else if h : t <+: p ∧ t.length < p.length
  --             then p.nth_le t.length h.2
  --             else let legal_moves := {a : α | @is_legal_move _ T G.to_game_tree t a} in
  --                  if h : legal_moves.nonempty
  --                  then set.nonempty.some h
  --                  else classical.arbitrary α,
  -- unfold losing_position₁,
  -- intros _,
  -- use τ,
  -- have : τ ∈ strategies (localized_subtree T p),
  -- { simp [is_strategy],
  --   rintros t ⟨htT, ht⟩ htl,
  --   by_cases h : p <+: t ∧ p.length < t.length,
  --   { simp [*, is_legal_move],
  --     split,
  --     { apply mem_of_mem_of_subset _ (localized_subtree_subset T (p.concat (t.nth_le p.length h.2))),
  --       rw ← concat_eq_append,
  --       have := concat_prefix_of_length_lt_of_prefix h.2 h.1,
  --       apply τastrat (t.nth_le p.length h.2),
  --       { split,
  --         exact htT,
  --         right,
  --         exact this, },
  --       cases htl with x hx,
  --       use x,
  --       split,
  --       { exact hx.1 },
  --       right,
  --       exact this.trans (prefix_concat _ _), },
  --     right,
  --     exact h.1.trans (prefix_append _ _), },
  --   by_cases h' : t <+: p ∧ t.length < p.length,
  --   { simp [*, is_legal_move],
  --     rw ← concat_eq_append,
  --     have := concat_prefix_of_length_lt_of_prefix h'.2 h'.1,
  --     split,
  --     { apply game_tree.prefix_closed _ _ this hpT, },
  --     left,
  --     exact this, },
  --   have : p = t,
  --   { push_neg at h h',
  --     cases ht,
  --     { symmetry,
  --       apply eq_of_prefix_of_length_eq ht _,
  --       linarith [ht.length_le, h' ht], },
  --     apply eq_of_prefix_of_length_eq ht _,
  --     linarith [ht.length_le, h ht], },
  --   rw this at *,
  --   have : {a : α | @is_legal_move _ T G.to_game_tree t a}.nonempty,
  --   { cases htl with a ha,
  --     have : a ∈ { a | is_legal_move T t a} := ha.1,
  --     apply nonempty_of_mem this, },
  --   simp [*],
  --   change t.concat this.some ∈ localized_subtree T t,
  --   split,
  --   exact this.some_mem,
  --   right,
  --   exact prefix_concat _ _, },
  -- use this,
  -- unfold winning_strategy₂,
  -- split,
  -- { intros t hτtc,
  --   change t ∈ game_tree_with_taboos.taboos₁ T ∩ (localized_subtree T p),
  --   rcases hτtc with ⟨⟨⟨htT, htp | hpt⟩, h₂⟩, ⟨htTp, hτtc⟩⟩,
  --   { split,
  --     { have : t.length = p.length,
  --       { by_contradiction,
  --         apply h₂,
  --         refine has_legal_move_of_prefix_of_ne_of_in_tree _ htp _ ⟨hpT, or.inl prefix_rfl⟩,
  --         contrapose! h,
  --         rw h, },
  --       have teqp : t = p := eq_of_prefix_of_length_eq htp this,
  --       rw ← teqp at *,
  --       have : t ∈ finite_plays T,
  --       { split,
  --         exact htT,
  --         contrapose! h₂,
  --         cases h₂ with a ha,
  --         use a,
  --         split,
  --         exact ha,
  --         right,
  --         rw teqp,
  --         exact prefix_concat _ _, },
  --       rw ← game_tree_with_taboos.taboos_terminal at this,
  --       cases mem_or_mem_of_mem_union this,
  --       { apply h, },
  --       contradiction, },
  --     exact htTp, },
  --   split,
  --   { have : t ∈ finite_plays T,
  --     { sorry },
  --     rw ← game_tree_with_taboos.taboos_terminal at this,
  --     cases mem_or_mem_of_mem_union this,
  --     { apply h, },
  --     have : p <+: t ∧ p.length < t.length,
  --     { sorry },
  --     have : p = t,
  --     { by_contradiction httaboo₂,
  --       have hptlt: p.length < t.length,
  --       { sorry },
  --       have : t ∈ (localized_game G (p.concat (t.nth_le p.length hptlt)) _).taboos₁,
  --       { have := concat_prefix_of_length_lt_of_prefix hptlt hpt,
  --         have := τawinning₂ (t.nth_le p.length _) (game_tree.prefix_closed _ _ this htT),
  --         apply this.1,
  --         simp,
  --         split,
  --         { split,
  --           { use htT,
  --             right,
  --             rwa ← concat_eq_append _ _, },
  --           contrapose! h₂,
  --           apply has_legal_move_localized_of_has_legal_move_localized_of_prefix _ _ _ _ h₂,
  --           apply prefix_concat _ _, },
  --         split,
  --         { use htT, right, assumption, },
  --         intros k hk hkodd,
  --         rw hτtc k hk hkodd,
  --         by_cases p.length < k,
  --         { have : p <+: take k t ∧ p.length < (take k t).length,
  --           { split,
  --             { rw [prefix_iff_eq_take, take_take, min_eq_left (le_of_lt h), ← prefix_iff_eq_take],
  --               assumption, },
  --             rw length_take,
  --             apply lt_min h,
  --             contrapose! httaboo₂,
  --             apply eq_of_prefix_of_length_eq hpt,
  --             linarith [hpt.length_le], },
  --           simp [*],
  --           have : (take k t).nth_le p.length this.2 = t.nth_le p.length hptlt,
  --           { symmetry,
  --             apply nth_le_take,
  --             assumption, },
  --           rw this, },
  --         sorry },
  --       { have : t ∈ game_tree_with_taboos.taboos₁ T,
  --         { exact this.1, },
  --         have : (game_tree_with_taboos.taboos₁ T ∩ game_tree_with_taboos.taboos₂ T).nonempty,
  --         { apply nonempty_of_mem (mem_inter this h), },
  --         apply this.ne_empty game_tree_with_taboos.taboos_disjoint, },
  --       apply game_tree.prefix_closed _ _ (concat_prefix_of_length_lt_of_prefix _ hpt) htT, },
  --     rw this at *,
  --     contradiction, },
  --   exact htTp, },
  -- intros f hτfc,
  -- suffices : f ∉ A ∩ infinite_plays (localized_subtree T (p.concat (f p.length))),
  -- { contrapose! this,
  --   split,
  --   exact this.1,
  --   intros n,
  --   split,
  --   exact (this.2 n).1,
  --   cases (this.2 n).2,
  --   { left,
  --     exact h.trans (prefix_concat _ _), },
  --   by_cases h' : p.length < n,
  --   { right,
  --     have : p.length < (stream_prefix f n).length,
  --     { rwa stream_prefix_length f n, },
  --     -- This should become a lemma...
  --     have : f p.length = (stream_prefix f n).nth_le p.length this,
  --     { apply option.some_inj.mp,
  --       rw ← nth_le_nth this,
  --       rw ← nth_take (lt_add_one p.length),
  --       have : stream_prefix f (p.length + 1) = take (p.length + 1) (stream_prefix f n),
  --       { nth_rewrite 1 ← stream_prefix_length f (p.length + 1),
  --         apply prefix_iff_eq_take.mp,
  --         apply stream_prefix_prefix,
  --         linarith, },
  --       rw ← this,
  --       symmetry,
  --       apply stream_prefix_nth f _, },
  --     rw this,
  --     exact concat_prefix_of_length_lt_of_prefix _ h, },
  --   have : p = stream_prefix f n,
  --   { have : p.length = n,
  --     { linarith [h.length_le, stream_prefix_length f n], },
  --     rw ← stream_prefix_length f n at this,
  --     exact eq_of_prefix_of_length_eq h this, },
  --   left,
  --   rw ← this,
  --   exact prefix_concat _ _, },
  -- refine (τawinning₂ _ _).2 f _,
  -- { have : p.concat (f p.length) = stream_prefix f (p.length + 1),
  --   { have : p = stream_prefix f p.length,
  --     { cases (hτfc.1 p.length).2,
  --       exact (eq_of_prefix_of_length_eq h (stream_prefix_length f _)).symm,
  --       exact eq_of_prefix_of_length_eq h (stream_prefix_length f _).symm, },
  --     nth_rewrite 0 this,
  --     simp [stream_prefix], },
  --   rw this,
  --   apply (hτfc.1 (p.length + 1)).1, },
  -- split,
  -- { sorry },
  -- intros n nodd,
  -- rw hτfc.2 n nodd,
  -- cases (hτfc.1 n).2,
  -- { have : stream_prefix f n <+: p ∧ (stream_prefix f n).length < p.length,
  --   { sorry },
  --   have : ¬ (p <+: stream_prefix f n ∧ p.length < (stream_prefix f n).length),
  --   { sorry },
  --   simp [*],
  --   sorry, },
  -- have : p <+: stream_prefix f n ∧ p.length < (stream_prefix f n).length,
  -- { split, exact h, apply lt_of_le_of_ne, exact h.length_le,
  --   rw stream_prefix_length f n, intros hc, rw hc at hevenp,
  --   apply nat.even_iff_not_odd.mp hevenp nodd, },
  -- simp [*],
  -- have : f p.length = (stream_prefix f n).nth_le p.length this.2,
  -- { apply option.some_inj.mp,
  --   rw ← nth_le_nth this.2,
  --   rw ← nth_take (lt_add_one p.length),
  --   have : stream_prefix f (p.length + 1) = take (p.length + 1) (stream_prefix f n),
  --   { nth_rewrite 1 ← stream_prefix_length f (p.length + 1),
  --     apply prefix_iff_eq_take.mp,
  --     apply stream_prefix_prefix,
  --     linarith [h.length_le, stream_prefix_length f n], },
  --   rw ← this,
  --   symmetry,
  --   apply stream_prefix_nth f _, },
  -- rw this,
end

lemma never_lose_strategy_is_strategy₁ :
  never_lose_strategy₁ G ∈ strategies T :=
sorry

lemma never_lose_strategy_never_loses (p : list α) :
  consistent_position₁ T (never_lose_strategy₁ G) (never_lose_strategy_is_strategy₁ G) p →
    ¬losing_position₁ G p :=
sorry

lemma plays_of_subtree_not_in_tree_losing₁ {S : set (list α)} [game_tree S] (p : list α) :
  plays_of_subtree T A S → p ∉ S → losing_position₁ G p :=
begin
  sorry
end

theorem closed_determinacy : closed_game G → determined G :=
begin
  intros hclosed,
  by_cases determined₂ G,
  { right, by assumption, },
  left,
  have : ¬ losing_position₁ G nil,
  { contrapose! h,
    unfold losing_position₁ at h,
    have h' := h G.nonempty,
    apply determined_of_unravelling_of_determined₂ _ _ _ h',
    apply covers_of_eq_game,
    apply eq_game_trivial_localization, },
  use never_lose_strategy₁ G,
  use never_lose_strategy_is_strategy₁ G,
  have hσnl := never_lose_strategy_never_loses G,
  split,
  { intros p hpc,
    have : p ∉ G.taboos₁ := λ h, hσnl _ hpc.2 (losing_of_taboo₁ _ _ h),
    have : p ∈ G.taboos₁ ∪ G.taboos₂,
    { rw G.taboos_terminal, apply hpc.1, },
    cases mem_or_mem_of_mem_union this,
    contradiction,
    assumption, },
  intros f hfc,
  rcases hclosed with ⟨S, ⟨hS, hTAS⟩⟩,
  rw hTAS.2,
  intros n,
  by_contradiction,
  apply hσnl _ ((prefix_of_consistent_is_consistent₁ _ _ _ _ hfc) n),
  apply @plays_of_subtree_not_in_tree_losing₁ _ _ _ G _ _ hS (stream_prefix f n) hTAS h,
end

theorem clopen_determinacy : clopen_game G → determined G :=
λ h, closed_determinacy G h.1

end clopen_determinacy

