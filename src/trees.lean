import tactic

inductive finseq (E : ℕ → Type) : ℕ → Type
| empty {} : finseq 0
| cat {n : ℕ} (s : finseq n) (a : E n) : finseq (n + 1)

infixl ` ⌢ `:67 := finseq.cat

def seq (E : ℕ → Type) : Type := Π n, E n

@[simp] def shift (E : ℕ → Type) (n : ℕ) (k : ℕ) := E (n + k)

variables {E : ℕ → Type}

namespace finseq

@[simp] def length {n : ℕ} (s : finseq E n) := n

@[simp] def append {n : ℕ} :
  Π {k : ℕ}, finseq E n → finseq (shift E n) k → finseq E (n + k)
| 0 s empty := s
| (k + 1) s (t ⌢ a) := (append s t) ⌢ a

@[simp] def parent : Π {n : ℕ}, finseq E n → finseq E n.pred
| 0 empty := empty
| (n + 1) (s ⌢ a) := s

@[simp] def last : Π {n : ℕ}, finseq E n → 0 < n → E n.pred
| 0 empty h := absurd h (nat.not_lt_zero _)
| (n + 1) (s ⌢ a) _ := a

@[simp] def nth : Π {n : ℕ} (s : finseq E n) {k}, k < n → E k
| 0 empty k h := absurd h k.not_lt_zero
| (n+1) (s ⌢ a) k h₁ :=
    if h₂ : k = n
      then by rw h₂; exact a
      else nth s (nat.lt_of_le_and_ne (nat.le_of_lt_succ h₁) h₂)

@[simp] def restrict : Π {n : ℕ} (s : finseq E n) (k : ℕ), k ≤ n → finseq E k
| 0 empty k h := by rw (nat.eq_zero_of_le_zero h); exact empty
| (n + 1) (s ⌢ a) k h₁ :=
    if h₂ : k = n + 1
      then by rw h₂; exact s ⌢ a
      else restrict s k (nat.le_of_lt_succ (nat.lt_of_le_and_ne h₁ h₂))

@[simp] lemma restrict_length {n : ℕ} (s : finseq E n) {h : n ≤ n} :
  restrict s n h = s :=
by induction s; simp

@[simp] lemma restrict_append {n k : ℕ} (s : finseq E n) (t : finseq (shift E n) k) {h : n ≤ n + k} :
  restrict (s.append t) n h  = s :=
begin
  induction t,
  { simp, apply restrict_length, },
  have : ¬ (n = n + t_n + 1) := by linarith,
  simp [this],
  apply t_ih,
end

@[simp] lemma restrict_zero {n : ℕ} (s : finseq E n) {h : 0 ≤ n} : s.restrict 0 h = empty :=
begin
  induction s,
  { simp, },
  have : 0 ≠ s_n + 1 := by linarith,
  simp [this],
  apply s_ih,
end

@[simp] lemma restrict_restrict {n k l : ℕ} (s : finseq E n) {h₁ : l ≤ k} {h₂ : k ≤ n} {h₃ : l ≤ n} :
  (s.restrict k h₂).restrict l h₁ = s.restrict l h₃ :=
begin
  induction h₂ with n h₂,
  { rw restrict_length, },
  change k ≤ n at h₂,
  cases s with _ s a,
  have hkn : k ≠ n + 1 := by linarith,
  have hln : l ≠ n + 1 := by linarith,
  simp [hkn, hln],
  apply h₂_ih,
end

def is_prefix {k : ℕ} {n : ℕ} (s : finseq E k) (t : finseq E n) : Prop :=
  ∃ (h : k ≤ n), restrict t k h = s

infix ` << `:50 := is_prefix

lemma prefix_append {n k : ℕ} (s : finseq E n) (t : finseq (shift E n) k) : s << s.append t :=
⟨nat.le_add_right _ _, restrict_append _ _⟩

lemma empty_prefix {n : ℕ} (s : finseq E n) : empty << s :=
⟨nat.zero_le _, restrict_zero _⟩

@[refl] lemma prefix_refl {n : ℕ} (s : finseq E n) : s << s :=
⟨le_rfl, restrict_length _⟩

lemma prefix_rfl {n : ℕ} {s : finseq E n} : s << s := prefix_refl _

@[trans] lemma is_prefix.trans {k m n} :
  ∀ {s₁ : finseq E k} {s₂ : finseq E m} {s₃ : finseq E n},
    s₁ << s₂ → s₂ << s₃ → s₁ << s₃
| _ _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ := ⟨le_trans h₁ h₂, (restrict_restrict _).symm⟩

lemma prefix_of_prefix_length_le {k m n} :
  ∀ {s₁ : finseq E k} {s₂ : finseq E m} {s₃ : finseq E n},
    s₁ << s₃ → s₂ << s₃ → k ≤ m → s₁ << s₂
| _ _ _ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩ h₃ := ⟨h₃, restrict_restrict _⟩

lemma prefix_or_prefix_of_prefix {k m n} {s₁ : finseq E k} {s₂ : finseq E m} {s₃ : finseq E n}
  (h₁ : s₁ << s₃) (h₂ : s₂ << s₃) : s₁ << s₂ ∨ s₂ << s₁ :=
(le_total (length s₁) (length s₂)).imp
  (prefix_of_prefix_length_le h₁ h₂)
  (prefix_of_prefix_length_le h₂ h₁)

lemma restrict_prefix {n} (k) (s : finseq E n) {h : k ≤ n} : s.restrict k h << s := ⟨h, rfl⟩

end finseq

namespace seq

@[simp] def restrict (x : seq E) : Π k, finseq E k
| 0 := finseq.empty
| (k + 1) := (restrict k) ⌢ (x k)

lemma restrict_restrict (x : seq E) {m k : ℕ} {h : k ≤ m} :
  (x.restrict m).restrict k h = x.restrict k :=
begin
  induction h with m h,
  { induction k; simp },
  change k ≤ m at h,
  have : k ≠ m + 1 := by linarith,
  simp [this],
  assumption
end

@[simp] def is_prefix {n : ℕ} (s : finseq E n) (x : seq E) : Prop :=
  x.restrict n = s

infix ` <<< `:50 := is_prefix

lemma empty_prefix (x : seq E) : finseq.empty <<< x := by simp

lemma restrict_prefix (x : seq E) (k) : x.restrict k <<< x := by simp

end seq
