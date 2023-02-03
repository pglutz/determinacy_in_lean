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

def is_prefix (s : list α) (f : ℕ → α) := stream_prefix f (s.length) = s

def prefix_open (X : set (ℕ → α)) (C : set (list α)):= ∀ f : ℕ → α,
  f ∈ X ↔ ∃ s ∈ C, is_prefix s f 

def is_prefix_open (X : set (ℕ → α)) := ∃ C, prefix_open X C
