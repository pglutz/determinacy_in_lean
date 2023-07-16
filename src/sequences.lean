import tactic

universe u

inductive finseq (E : ℕ → Type u) : ℕ → Type u
| null : finseq 0
| cat {n : ℕ} (σ : finseq n) (x : E n) : finseq (n + 1)

infixl (name := finseq.cat) ` ⌢ `:67 := finseq.cat

def seq (E : ℕ → Type u) : Type u := Π n, E n

variables {E : ℕ → Type u}

namespace finseq

@[simp] def length {n : ℕ} (σ : finseq E n) := n

@[simp] def parent : Π {n : ℕ}, finseq E n → finseq E n.pred
| 0 null := null
| (n + 1) (σ ⌢ x) := σ

@[simp] def last : Π {n : ℕ}, finseq E n → 0 < n → E n.pred
| 0 null h := absurd h (nat.not_lt_zero _)
| (n + 1) (σ ⌢ x) _ := x

@[simp] def nth : Π {n : ℕ} (σ : finseq E n) (k), k < n → E k
| 0 null k h := absurd h k.not_lt_zero
| (n+1) (σ ⌢ x) k h₁ :=
    if h₂ : k = n
      then cast (congr_arg E h₂.symm) x
      else nth σ k (nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂)

@[simp] lemma nth_cat_of_length {n : ℕ} (σ : finseq E n) (x : E n) {h : n < n + 1} :
  (σ ⌢ x).nth n h = x := by simp

@[simp] lemma nth_cat_of_length_lt {n : ℕ} (σ : finseq E n) (x : E n) {k} {h : k < n} :
  (σ ⌢ x).nth k (nat.lt_succ_of_lt h) = σ.nth k h := by simp [ne_of_lt h]

@[simp] def restrict : Π {n : ℕ} (σ : finseq E n) (k : ℕ), k ≤ n → finseq E k
| 0 null k h := cast (congr_arg (finseq E) (nat.eq_zero_of_le_zero h).symm) null
| (n + 1) (σ ⌢ x) k h₁ :=
    if h₂ : k = n + 1
      then cast (congr_arg (finseq E) h₂.symm) (σ ⌢ x)
      else restrict σ k (nat.le_of_lt_succ (nat.lt_of_le_and_ne h₁ h₂))

@[simp] lemma restrict_length {n : ℕ} (σ : finseq E n) {h : n ≤ n} :
  restrict σ n h = σ :=
by induction σ; simp

@[simp] lemma restrict_cat_of_length {n} (σ : finseq E n) (x : E n) :
  restrict (σ ⌢ x) n (nat.le_succ n) = σ := by simp

@[simp] lemma restrict_cat_of_length_le {n} (σ : finseq E n) (x : E n) {k} {h : k ≤ n} :
  restrict (σ ⌢ x) k (nat.le_succ_of_le h) = restrict σ k h :=
by simp [ne_of_lt (nat.lt_succ_of_le h)]

@[simp] lemma cat_restrict : Π {n} (σ : finseq E (n+1)),
  σ.restrict n (by simp) ⌢ σ.nth n (by simp) = σ
| n (σ ⌢ x) := by simp

@[simp] lemma restrict_zero : Π {n : ℕ} (σ : finseq E n),
  σ.restrict 0 (nat.zero_le _) = null
| 0 null := rfl
| (n+1) (σ ⌢ x) := restrict_zero σ

@[simp] lemma nth_restrict {n k l : ℕ} (σ : finseq E n) {hlk : l < k} {hkn : k ≤ n} :
  (σ.restrict k hkn).nth l hlk = σ.nth l (lt_of_lt_of_le hlk hkn) :=
begin
  induction hkn with n hkn,
  { simp },
  change k ≤ n at hkn,
  cases σ with _ σ x,
  have h₁ : k ≠ n + 1 := by linarith,
  have h₂ : l ≠ n := by linarith,
  simp [h₁, h₂],
  apply hkn_ih
end

@[simp] lemma restrict_restrict {n k l : ℕ} (σ : finseq E n) {h₁ : l ≤ k} {h₂ : k ≤ n} :
  (σ.restrict k h₂).restrict l h₁ = σ.restrict l (le_trans h₁ h₂) :=
begin
  induction h₂ with n h₂,
  { rw restrict_length },
  change k ≤ n at h₂,
  cases σ with _ σ x,
  have hkn : k ≠ n + 1 := by linarith,
  have hln : l ≠ n + 1 := by linarith,
  simp [hkn, hln],
  apply h₂_ih,
end

def is_prefix {k : ℕ} {n : ℕ} (σ : finseq E k) (τ : finseq E n) : Prop :=
  ∃ (h : k ≤ n), restrict τ k h = σ

infix (name := finseq.prefix) ` << `:50 := is_prefix

@[simp] lemma null_prefix {n : ℕ} (σ : finseq E n) : null << σ :=
⟨nat.zero_le _, restrict_zero _⟩

@[refl] lemma prefix_refl {n : ℕ} (σ : finseq E n) : σ << σ :=
⟨le_rfl, restrict_length _⟩

lemma prefix_rfl {n : ℕ} {σ : finseq E n} : σ << σ := prefix_refl _

@[simp] lemma prefix_cat {n : ℕ} (σ : finseq E n) (x : E n) : σ << σ ⌢ x :=
⟨le_of_lt (nat.lt_succ_self _), by simp⟩

@[trans] lemma is_prefix.trans {k m n} :
  ∀ {σ₁ : finseq E k} {σ₂ : finseq E m} {σ₃ : finseq E n},
    σ₁ << σ₂ → σ₂ << σ₃ → σ₁ << σ₃
| _ _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ := ⟨le_trans h₁ h₂, (restrict_restrict _).symm⟩

@[simp] lemma restrict_prefix {n k} (σ : finseq E n) (h : k ≤ n) : σ.restrict k h << σ := ⟨h, rfl⟩

lemma prefix_of_prefix_length_le {k m n} :
  ∀ {σ₁ : finseq E k} {σ₂ : finseq E m} {σ₃ : finseq E n},
    σ₁ << σ₃ → σ₂ << σ₃ → k ≤ m → σ₁ << σ₂
| _ _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ h₃ := ⟨h₃, restrict_restrict _⟩

lemma prefix_cat_of_prefix_of_length_lt {m n} :
  ∀ {σ : finseq E m} {τ : finseq E n} (h : m < n),
    σ << τ → σ ⌢ (τ.nth m h) << τ
| _ τ h ⟨h₁, rfl⟩ :=
  calc τ.restrict m h₁ ⌢ τ.nth m h
        = τ.restrict m h₁ ⌢ (τ.restrict (m+1) h).nth m (nat.lt_succ_self _) : by simp
    ... = (τ.restrict (m+1) h).restrict m (nat.le_succ m) ⌢ (τ.restrict (m+1) h).nth m (nat.lt_succ_self _)
            : by rw ← restrict_restrict
    ... = τ.restrict (m+1) h : cat_restrict _
    ... << τ.restrict (m+1) h : prefix_rfl
    ... << τ : by simp

lemma prefix_or_prefix_of_prefix {k m n} {σ₁ : finseq E k} {σ₂ : finseq E m} {σ₃ : finseq E n}
  (h₁ : σ₁ << σ₃) (h₂ : σ₂ << σ₃) : σ₁ << σ₂ ∨ σ₂ << σ₁ :=
(le_total (length σ₁) (length σ₂)).imp
  (prefix_of_prefix_length_le h₁ h₂)
  (prefix_of_prefix_length_le h₂ h₁)

lemma eq_of_prefix_of_length_eq {n} {σ : finseq E n} {τ : finseq E n} :
  σ << τ → σ = τ
| ⟨_, h⟩ := by { rw ← h, simp }

end finseq

open finseq

namespace seq

@[simp] def restrict (α : seq E) : Π k, finseq E k
| 0 := null
| (k + 1) := (restrict k) ⌢ (α k)

@[simp] lemma restrict_restrict (α : seq E) {m k : ℕ} {h : k ≤ m} :
  (α.restrict m).restrict k h = α.restrict k :=
begin
  induction h with m h,
  { induction k; simp },
  change k ≤ m at h,
  have : k ≠ m + 1 := by linarith,
  simp [this],
  assumption
end

@[simp] lemma nth_restrict {n k : ℕ} (α : seq E) :
  ∀ (hkn : k < n), (α.restrict n).nth k hkn = α k :=
begin
  induction n with n ih; intros hkn,
  { cases hkn },
  simp *,
  intros h,
  cases h,
  reflexivity
end

@[simp] def is_prefix {n : ℕ} (σ : finseq E n) (α : seq E) : Prop :=
  α.restrict n = σ

infix (name := seq.prefix) ` << `:50 := is_prefix

@[simp] lemma null_prefix (α : seq E) : null << α := by simp

@[simp] lemma restrict_prefix (α : seq E) (k) : α.restrict k << α := by simp

lemma is_prefix.trans {m n} :
  ∀ {σ : finseq E m} {τ : finseq E n} {α : seq E}, σ << τ → τ << α → σ << α
| _ _ _ ⟨h₁, rfl⟩ rfl := (restrict_restrict _).symm

lemma prefix_of_prefix_length_le {k n} :
  ∀ {σ : finseq E k} {τ : finseq E n} {α : seq E},
    σ << α → τ << α → k ≤ n → σ << τ
| _ _ α rfl rfl h := by {
  rw ← (restrict_restrict α),
  exact finseq.restrict_prefix _ h
}

lemma is_prefix_iff_nth_equal {n} (σ : finseq E n) (α : seq E) :
  σ << α ↔ ∀ k (h : k < n), α k = σ.nth k h :=
begin
  split,
  { intros h,
    induction σ with n σ x σ_ih,
    { intros k hk,
      cases hk, },
    intros k hk,
    cases hk with k hk',
    { simp,
      simp at h,
      exact h.2, },
    change k < n at hk',
    simp [ne_of_lt hk'],
    apply σ_ih,
    simp at h,
    exact h.1 },
  induction σ with n σ x σ_ih,
  { intros, apply null_prefix },
  intros h,
  simp,
  split,
  { apply σ_ih,
    intros k hk,
    rw h k (nat.lt_succ_of_lt hk),
    simp [ne_of_lt hk], },
  rw h n (nat.lt_succ_self n),
  simp,
end

end seq
