import tactic

inductive finseq (E : ℕ → Type) : ℕ → Type
| null : finseq 0
| cat {n : ℕ} (σ : finseq n) (x : E n) : finseq (n + 1)

infixl ` ⌢ `:67 := finseq.cat

def seq (E : ℕ → Type) : Type := Π n, E n

@[simp] def shift (E : ℕ → Type) (n : ℕ) (k : ℕ) := E (n + k)

variables {E : ℕ → Type}

namespace finseq

@[simp] def length {n : ℕ} (σ : finseq E n) := n

@[simp] def append {n : ℕ} :
  Π {k : ℕ}, finseq E n → finseq (shift E n) k → finseq E (n + k)
| 0 σ null := σ
| (k + 1) σ (τ ⌢ x) := (append σ τ) ⌢ x

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
      then by rw h₂; exact x
      else nth σ k (nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂)

@[simp] def restrict : Π {n : ℕ} (σ : finseq E n) (k : ℕ), k ≤ n → finseq E k
| 0 null k h := by rw (nat.eq_zero_of_le_zero h); exact null
| (n + 1) (σ ⌢ x) k h₁ :=
    if h₂ : k = n + 1
      then by rw h₂; exact σ ⌢ x
      else restrict σ k (nat.le_of_lt_succ (nat.lt_of_le_and_ne h₁ h₂))

@[simp] lemma restrict_length {n : ℕ} (σ : finseq E n) {h : n ≤ n} :
  restrict σ n h = σ :=
by induction σ; simp

@[simp] lemma restrict_append {n k : ℕ} (σ : finseq E n) (τ : finseq (shift E n) k) {h : n ≤ n + k} :
  restrict (σ.append τ) n h  = σ :=
begin
  induction τ with k τ x τ_ih,
  { simp, apply restrict_length, },
  have : ¬ (n = n + k + 1) := by linarith,
  simp [this],
  apply τ_ih,
end

@[simp] lemma restrict_zero {n : ℕ} (σ : finseq E n) {h : 0 ≤ n} : σ.restrict 0 h = null :=
begin
  induction σ with n σ x σ_ih,
  { simp, },
  have : 0 ≠ n + 1 := by linarith,
  simp [this],
  apply σ_ih,
end

@[simp] lemma restrict_restrict {n k l : ℕ} (σ : finseq E n) {h₁ : l ≤ k} {h₂ : k ≤ n} {h₃ : l ≤ n} :
  (σ.restrict k h₂).restrict l h₁ = σ.restrict l h₃ :=
begin
  induction h₂ with n h₂,
  { rw restrict_length, },
  change k ≤ n at h₂,
  cases σ with _ σ x,
  have hkn : k ≠ n + 1 := by linarith,
  have hln : l ≠ n + 1 := by linarith,
  simp [hkn, hln],
  apply h₂_ih,
end

def is_prefix {k : ℕ} {n : ℕ} (σ : finseq E k) (τ : finseq E n) : Prop :=
  ∃ (h : k ≤ n), restrict τ k h = σ

infix ` << `:50 := is_prefix

lemma prefix_append {n k : ℕ} (σ : finseq E n) (τ : finseq (shift E n) k) : σ << σ.append τ :=
⟨nat.le_add_right _ _, restrict_append _ _⟩

lemma null_prefix {n : ℕ} (σ : finseq E n) : null << σ :=
⟨nat.zero_le _, restrict_zero _⟩

@[refl] lemma prefix_refl {n : ℕ} (σ : finseq E n) : σ << σ :=
⟨le_rfl, restrict_length _⟩

lemma prefix_rfl {n : ℕ} {σ : finseq E n} : σ << σ := prefix_refl _

lemma prefix_cat {n : ℕ} {σ : finseq E n} {x : E n} : σ << σ ⌢ x :=
⟨le_of_lt (nat.lt_succ_self _), by simp⟩

@[trans] lemma is_prefix.trans {k m n} :
  ∀ {σ₁ : finseq E k} {σ₂ : finseq E m} {σ₃ : finseq E n},
    σ₁ << σ₂ → σ₂ << σ₃ → σ₁ << σ₃
| _ _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ := ⟨le_trans h₁ h₂, (restrict_restrict _).symm⟩

lemma prefix_of_prefix_length_le {k m n} :
  ∀ {σ₁ : finseq E k} {σ₂ : finseq E m} {σ₃ : finseq E n},
    σ₁ << σ₃ → σ₂ << σ₃ → k ≤ m → σ₁ << σ₂
| _ _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ h₃ := ⟨h₃, restrict_restrict _⟩

lemma prefix_or_prefix_of_prefix {k m n} {σ₁ : finseq E k} {σ₂ : finseq E m} {σ₃ : finseq E n}
  (h₁ : σ₁ << σ₃) (h₂ : σ₂ << σ₃) : σ₁ << σ₂ ∨ σ₂ << σ₁ :=
(le_total (length σ₁) (length σ₂)).imp
  (prefix_of_prefix_length_le h₁ h₂)
  (prefix_of_prefix_length_le h₂ h₁)

lemma restrict_prefix {n} (k) (σ : finseq E n) {h : k ≤ n} : σ.restrict k h << σ := ⟨h, rfl⟩

end finseq

open finseq

namespace seq

@[simp] def restrict (α : seq E) : Π k, finseq E k
| 0 := null
| (k + 1) := (restrict k) ⌢ (α k)

lemma restrict_restrict (α : seq E) {m k : ℕ} {h : k ≤ m} :
  (α.restrict m).restrict k h = α.restrict k :=
begin
  induction h with m h,
  { induction k; simp },
  change k ≤ m at h,
  have : k ≠ m + 1 := by linarith,
  simp [this],
  assumption
end

@[simp] def is_prefix {n : ℕ} (σ : finseq E n) (α : seq E) : Prop :=
  α.restrict n = σ

infix ` <<< `:50 := is_prefix

lemma null_prefix (α : seq E) : null <<< α := by simp

lemma restrict_prefix (α : seq E) (k) : α.restrict k <<< α := by simp

lemma is_prefix.trans {m n} :
  ∀ {σ : finseq E m} {τ : finseq E n} {α : seq E}, σ << τ → τ <<< α → σ <<< α
| _ _ _ ⟨h₁, rfl⟩ rfl := (restrict_restrict _).symm

lemma is_prefix_iff_nth_equal {n} (σ : finseq E n) (α : seq E) :
  σ <<< α ↔ ∀ k (h : k < n), α k = σ.nth k h :=
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
