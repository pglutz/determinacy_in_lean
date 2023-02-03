import data.seq.seq
import data.list.infix

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

lemma stream_prefix_prefix (f : ℕ → α) (n m : ℕ) (h : n ≤ m) :
  stream_prefix f n <+: stream_prefix f m :=
begin
  induction m with m ih,
  { rw nonpos_iff_eq_zero.mp h, },
  { rw le_iff_eq_or_lt at h,
    cases h,
    { rw h, },
    { rw nat.lt_succ_iff at h,
       calc stream_prefix f n <+: stream_prefix f m : ih h 
       ... <+: stream_prefix f m.succ : list.prefix_concat (f m) (stream_prefix f m), }, },
end

def is_prefix (s : list α) (f : ℕ → α) := stream_prefix f (s.length) = s

lemma prefix_of_is_prefix (s : list α) (f : ℕ → α) (n : ℕ) (h : is_prefix s f)
  (h' : n ≥ s.length) : s <+: stream_prefix f n :=
begin
  rw is_prefix at h,
  rw ← h,
  exact stream_prefix_prefix f s.length n h',
end

lemma is_prefix_of_prefix (s : list α) (f : ℕ → α) (n : ℕ)
  (h : s <+: stream_prefix f n) : is_prefix s f :=
begin
  have hn : n ≥ s.length,
  { rw ← (stream_prefix_length f n),
    exact list.is_prefix.length_le h, },
  have hf : (stream_prefix f s.length).length = s.length :=
    stream_prefix_length f s.length,
  apply list.eq_of_prefix_of_length_eq,
  { apply list.prefix_of_prefix_length_le (stream_prefix_prefix f s.length n hn) h,
    rw stream_prefix_length, },
  { exact hf, },
end

def prefix_open (X : set (ℕ → α)) (C : set (list α)):= ∀ f : ℕ → α,
  f ∈ X ↔ ∃ s ∈ C, is_prefix s f 

def is_prefix_open (X : set (ℕ → α)) := ∃ C, prefix_open X C
