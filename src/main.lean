-- This file contains a mostly-complete but flawed proof of 
-- determinacy for open games. To complete it, a definition has
-- to be changed. However, I decided the definitions were very bad
-- and it would be better to start over with cleaner definitions.
-- The other files in this project are my attempt to do that

import topology.metric_space.pi_nat
import data.seq.seq
import data.list.infix
import tactic.suggest

noncomputable theory
open_locale classical

variable {α : Type*}

def stream_prefix : (ℕ → α) → ℕ → list α
| f 0 := list.nil 
| f (n + 1) := list.concat (stream_prefix f n) (f n)

lemma stream_prefix_length (f : ℕ → α) (n : ℕ) :
  (stream_prefix f n).length = n :=
begin
  induction n with n ih,
  { refl, },
  { rw [stream_prefix, list.length_concat, ih], },
end

def is_prefix (s : list α) (f : ℕ → α) := stream_prefix f (s.length) = s

def prefix_open (X : set (ℕ → α)) (C : set (list α)):= ∀ f : ℕ → α,
  f ∈ X ↔ ∃ s ∈ C, is_prefix s f 

def is_prefix_open (X : set (ℕ → α)) := ∃ C, prefix_open X C

def is_p1_quasi_strategy (σ : set (list α)) (s : list α) :=
  s ∈ σ ∧ ∀ t : list α, (t ∈ σ → 
    (even t.length → ∃ a : α, (list.concat t a) ∈ σ) ∧
    (odd t.length → ∀ a : α, (list.concat t a) ∈ σ))

def is_p2_quasi_strategy (σ : set (list α)) (s : list α) :=
  s ∈ σ ∧ ∀ t : list α, (t ∈ σ → 
    (odd t.length → ∃ a : α, (list.concat t a) ∈ σ) ∧
    (even t.length → ∀ a : α, (list.concat t a) ∈ σ))

def is_winning_p1_quasi_strategy (σ : set (list α)) (s : list α) 
  (X : set (ℕ → α)):= 
  ∀ f : ℕ → α, (∀ n ≥ s.length, stream_prefix f n ∈ σ) → f ∈ X

def is_winning_p2_quasi_strategy (σ : set (list α)) (s : list α) 
  (X : set (ℕ → α)) := 
  ∀ f : ℕ → α, (∀ n ≥ s.length, stream_prefix f n ∈ σ) → f ∉ X

def is_p1_winning (s : list α) (X : set (ℕ → α)) :=
  ∃ σ, (is_p1_quasi_strategy σ s ∧ is_winning_p1_quasi_strategy σ s X)

def is_p2_winning (s : list α) (X : set (ℕ → α)) :=
  ∃ σ, (is_p2_quasi_strategy σ s ∧ is_winning_p2_quasi_strategy σ s X)

def quasi_determined (s : list α) (X : set (ℕ → α)) :=
  is_p1_winning s X ∨ is_p2_winning s X

def non_winning (X : set (ℕ → α)) := {s | ¬ is_p1_winning s X}

lemma extension_of_quasi_strategy (X : set (ℕ → α)) (s : list α) (a : α) (σ : set (list α))
  (h : is_p1_quasi_strategy σ (s.concat a)) (hs : even s.length) : is_p1_quasi_strategy ({s} ∪ σ) s :=
begin
  split,
  { simp only [set.singleton_union, set.mem_insert_iff, eq_self_iff_true, true_or], },
  { intros t ht,
    cases ht,
    { change t = s at ht,
      rw ht,
      split,
      { intros _,
        use a,
        right,
        exact h.left, },
      { intros hs',
        exfalso,
        exact nat.even_iff_not_odd.mp hs hs',}, },
    { split,
      { intros ht',
        cases (h.right t ht).left ht' with b hb,
        use b,
        right,
          exact hb, },
      { intros ht' b,
        right,
        exact (h.right t ht).right ht' b, }, },
  },
end

lemma extension_of_winning_quasi_strategy (X : set (ℕ → α)) (s : list α) (a : α) (σ : set (list α))
  (h : is_winning_p1_quasi_strategy σ (s.concat a) X) : is_winning_p1_quasi_strategy ({s} ∪ σ) s X :=
begin
  intros f hf,
  apply h f,
  intros n hn,
  rw list.length_concat at hn,
  have key : n > s.length := nat.succ_le_iff.mp hn,
  specialize hf n (by linarith),
  cases hf,
  { exfalso,
    change stream_prefix f n = s at hf,
    rw [← hf, stream_prefix_length] at key,
    exact nat.lt_asymm key key, },
  { exact hf, },
end

lemma union_of_quasi_strategies [hα : nonempty α] (X : set (ℕ → α)) (s : list α) 
  (g : α → (set (list α))) (h : ∀ a, is_p1_quasi_strategy (g a) (s.concat a)) : 
  is_p1_quasi_strategy ({s} ∪ (⋃ (a : α), g a)) s :=
begin
  split,
  { simp only [set.singleton_union, set.mem_insert_iff, eq_self_iff_true, true_or], },
  intros t ht,
  cases ht,
  { change t = s at ht,
    rw ht,
    have key : ∀ a : α, s.concat a ∈ {s} ∪ ⋃ (a : α), g a,
    { intros a,
      right,
      exact set.mem_Union_of_mem a (h a).left,  },
    split,
    { intros _,
      exact ⟨hα.some, key _⟩, },
    { intros _,
      exact key,  },  },
  { cases set.mem_Union.mp ht with a ha,
    clear ht,
    have h' := (h a).right t ha,
    split,
    { intros ht,
      cases h'.left ht with b hb,
      use b,
      right,
      exact set.mem_Union_of_mem a hb,  },
    { intros ht b,
      right,
      exact set.mem_Union_of_mem a (h'.right ht b), },  },
end

lemma union_of_winning_quasi_strategies [hα : nonempty α] (X : set (ℕ → α)) (s : list α) 
  (g : α → (set (list α))) (h : ∀ a, is_winning_p1_quasi_strategy (g a) (s.concat a) X) : 
  is_winning_p1_quasi_strategy ({s} ∪ (⋃ (a : α), g a)) s X :=
begin
  intros f hf,
  sorry,
  -- let a := f s.length,
  -- apply h a f,
  -- intros n hn,
  -- rw list.length_concat at hn,
  -- have key : n > s.length := nat.succ_le_iff.mp hn,
  -- specialize hf n (by linarith),
  -- cases hf,
  -- { exfalso,
  --   change stream_prefix f n = s at hf,
  --   rw [← hf, stream_prefix_length] at key,
  --   exact nat.lt_asymm key key, },
  -- { cases set.mem_Union.mp hf with b hb,

  -- },
end

theorem non_winning_is_quasi_strategy [nonempty α] (X : set (ℕ → α)) (s : list α) 
  (h : ¬ is_p1_winning s X) : is_p2_quasi_strategy (non_winning X) s :=
begin
  split,
  { exact h, },
  { intros t ht₁,
    split,
    { intros ht₂,
      by_contra' h',
      have key : ∃ g : α → (set (list α)), ∀ a, is_p1_quasi_strategy (g a) (t.concat a) 
        ∧ is_winning_p1_quasi_strategy (g a) (t.concat a) X := sorry,
      cases key with g hg,
      have key : is_p1_quasi_strategy ({t} ∪ ⋃ (a : α), g a) t := union_of_quasi_strategies X t g (λ a, (hg a).left),
      have key' : is_winning_p1_quasi_strategy ({t} ∪ ⋃ (a : α), g a) t X := union_of_winning_quasi_strategies X t g (λ a, (hg a).right),
      exact ht₁ ⟨{t} ∪ ⋃ (a : α), g a, key, key'⟩,  },
    { intros ht₂,
      by_contra' h',
      cases h' with a ha,
      simp only [non_winning, set.mem_set_of_eq, not_not] at ha,
      cases ha with σ hσ,
      have key : is_p1_quasi_strategy ({t} ∪ σ) t := extension_of_quasi_strategy X t a σ hσ.left ht₂,
      have key' : is_winning_p1_quasi_strategy ({t} ∪ σ) t X := extension_of_winning_quasi_strategy X t a σ hσ.right,
      exact ht₁ ⟨{t} ∪ σ, key, key'⟩, }, },
end

theorem prefix_winning [hα : nonempty α] (X : set (ℕ → α)) (C : set (list α)) (s : list α) 
  (h₁ : s ∈ C) (h₂ : prefix_open X C) : is_p1_winning s X :=
begin
  use {t | list.is_prefix s t},
  split,
  { split,
    { exact set.mem_set_of.mpr (list.prefix_rfl)  },
    { intros t ht,
      split,
      { intros _,
        have a : α := nonempty.some hα,
        use a,
        have key : list.is_prefix s (t.concat a),
        { calc s <+: t : ht
        ... <+: t.concat a : list.prefix_concat a t, },
        exact set.mem_set_of.mpr key, },
      { intros _ a,
        have key : list.is_prefix s (t.concat a),
        { calc s <+: t : ht
          ... <+: t.concat a : list.prefix_concat a t, },
        exact set.mem_set_of.mpr key, }, }, },
  { intros f hf,
    have key : stream_prefix f (s.length) = s,
    { specialize hf s.length rfl.ge,
      simp only [set.mem_set_of_eq] at *,
      exact eq.symm (list.eq_of_prefix_of_length_eq hf (eq.symm (stream_prefix_length _ _))), },
    exact (h₂ f).mpr ⟨s, h₁, key⟩, },
end

theorem quasi_determined_if_prefix_open [nonempty α] (X : set (ℕ → α)) (h : is_prefix_open X) : quasi_determined list.nil X :=
begin
  by_cases h' : is_p1_winning _ X,
  { left,
    exact h', },
  { right,
    use non_winning X,
    split,
    { exact non_winning_is_quasi_strategy X _ h', },
    intros f hf hf',
    rcases h with ⟨C, hC⟩,
    rcases (hC f).mp hf' with ⟨s, ⟨hs₁, hs₂⟩⟩,
    have hs₃ : s.length ≥ list.nil.length,
    { simp only [list.length, ge_iff_le, zero_le']},
    specialize hf s.length hs₃,
    unfold is_prefix at hs₂,
    rw hs₂ at hf,
    have key := prefix_winning X C s hs₁ hC,
    exact h' (false.rec (is_p1_winning list.nil X) (hf (prefix_winning X C s hs₁ hC))), },
end


