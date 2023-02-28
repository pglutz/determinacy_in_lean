import prefixes
import topology.metric_space.pi_nat

noncomputable theory
open_locale classical topology filter
open topological_space 

variables {α : Type*} [topological_space α] [discrete_topology α]

lemma prefix_open_of_open (A : set (ℕ → α)) : is_open A → is_prefix_open A :=
begin
  intros hA,
  use {s : list α | ∀ f, is_prefix s f → f ∈ A},
  intros f,
  split,
  { intros hf,
    have key := (is_topological_basis.is_open_iff (pi_nat.is_topological_basis_cylinders _)).mp hA,
    rcases key f hf with ⟨B, B_cylinder, hB₁, hB₂⟩,
    rcases B_cylinder with ⟨g, n, hn⟩,
    use stream_prefix g n,
    rw hn at *,
    clear key hn,
    split,
    { clear hf hB₁ f,
      intros f hf,
      apply hB₂,
      intros i hi,
      unfold is_prefix at hf,
      rw stream_prefix_length at hf,
      have key : (f i : option α) = (g i : option α) :=
      by calc ↑(f i) = (stream_prefix f n).nth i : (stream_prefix_nth' f n i hi).symm
      ... = (stream_prefix g n).nth i : by rw hf
      ... = ↑(g i) : stream_prefix_nth' g n i hi,
      injections_and_clear,
      assumption, },
    { unfold is_prefix,
      rw stream_prefix_length,
      ext1 i,
      by_cases hi : i < n,
      { calc (stream_prefix f n).nth i = f i : stream_prefix_nth' f n i hi
        ... = g i : congr_arg coe (hB₁ i hi)
        ... = (stream_prefix g n).nth i : (stream_prefix_nth' g n i hi).symm, },
      { calc (stream_prefix f n).nth i = none : list.nth_len_le (by linarith [stream_prefix_length f n])
        ... = (stream_prefix g n).nth i : (list.nth_len_le (by linarith [stream_prefix_length g n])).symm, }, }, },
  { rintros ⟨s, hs₁, hs₂⟩,
    exact hs₁ f hs₂, },
end