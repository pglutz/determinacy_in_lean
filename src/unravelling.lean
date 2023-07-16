import sequences
import games

open finseq nat set game_tree game

universes u₀ u₁ v

class game_map {E₀ : ℕ → Type u₀} {E₁ : ℕ → Type u₁} {β : Type v}
  (G₀ : game E₀ β) (G₁ : game E₁ β) :=
(map : Π {{n}}, G₀.positions n → G₁.positions n)
(monotone : ∀ {{n k}} {σ : G₀.positions n} {τ : G₀.positions k}, σ << τ → map σ << map τ)
(leaf_lift : ∀ {{n}} {σ : G₀.positions n}, ↑(map σ) ∈ G₁.leaves n → ↑σ ∈ G₀.leaves n)
(taboo_lift : ∀ {{n}} {σ : G₀.positions n}, ↑(map σ) ∈ G₁.leaves n →
  G₀.taboo (σ : finseq E₀ n) = G₁.taboo (map σ : finseq E₁ n))

instance game_map_to_position_fun {E₀ : ℕ → Type u₀} {E₁ : ℕ → Type u₁} {β : Type v}
    (G₀ : game E₀ β) (G₁ : game E₁ β) :
  has_coe_to_fun (game_map G₀ G₁) (λ _, Π {{n}}, G₀.positions n → G₁.positions n) :=
{ coe := λ F, F.map }

instance game_map_to_move_fun {E₀ : ℕ → Type u₀} {E₁ : ℕ → Type u₁} {β : Type v}
    (G₀ : game E₀ β) (G₁ : game E₁ β) :
  has_coe_to_fun (game_map G₀ G₁)
    (λ F, Π {{n}} {σ : G₀.positions n},
      G₀.moves (σ : finseq E₀ n) → G₁.moves (F σ : finseq E₁ n)) :=
{ coe := λ F n σ x, let τ : G₀.positions (n+1) := ⟨(σ : finseq E₀ n) ⌢ x,
                                        by simp [position_cat_of_position_of_move]⟩
          in ⟨(F τ : finseq E₁ (n+1)).nth n (le_refl (n+1)),
              begin
                have h₀ : ↑(F τ) ∈ G₁.positions (n+1) := (F τ).mem,
                apply move_of_position_cat,
                have h₁ : ↑(F σ) ⌢ (F τ : finseq E₁ (n+1)).nth n (le_refl (n+1)) = ↑(F τ) := by {
                  apply eq_of_prefix_of_length_eq,
                  apply prefix_cat_of_prefix_of_length_lt,
                  apply F.monotone,
                  simp
                },
                rw h₁,
                exact h₀
              end⟩ }

namespace game_map

variables {E₀ : ℕ → Type u₀} {E₁ : ℕ → Type u₁} {β : Type v}
  {G₀ : game E₀ β} {G₁ : game E₁ β}

notation (name := game_map) G₀ `⇒` G₁ := game_map G₀ G₁

variables (F : G₀ ⇒ G₁)

end game_map