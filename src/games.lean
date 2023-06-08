import sequences

class game_tree (E : ℕ → Type) :=
(moves : Π {{n}}, finseq E n → set (E n))

namespace game_tree

variables {E : ℕ → Type} (f : game_tree E)

def is_subtree (g : game_tree E) := ∀ n (σ : finseq E n), f.moves σ ⊆ g.moves σ

def is_play (α : seq E) := ∀ n, α n ∈ f.moves (α.restrict n)

def is_finite_play {n} (σ : finseq E n) := ∀ k (h : k < n), σ.nth k h ∈ f.moves (σ.restrict k (le_of_lt h))

def is_leaf {n} (σ : finseq E n) := f.moves σ = ∅

end game_tree

class game (E : ℕ → Type) (β : Type) extends (game_tree E) :=
(turn : Π {{n}}, finseq E n → β)
(taboo : Π {{n}}, finseq E n → β)
(payoff : seq E → β)

namespace game

variables {E : ℕ → Type} {β : Type} (G : game E β)

def induced_subgame (f : game_tree E) : game E β :=
{ moves := f.moves,
  turn := G.turn,
  taboo := G.taboo,
  payoff := G.payoff }

def is_quasi_strategy (P : β) (f : game_tree E) :=
  (f.is_subtree G.to_game_tree) ∧ ∀ {n} (σ : finseq E n),
    (G.turn σ = P → G.moves σ ≠ ∅ → f.moves σ ≠ ∅)
    ∧ (G.turn σ ≠ P → f.moves σ = G.moves σ)

def is_winning_position (P : β) {n} (σ : finseq E n) := ∀ α, G.is_play α → σ <<< α → G.payoff α = P

def is_winnable_position (P : β) {n} (σ : finseq E n) :=
  ∃ (f : game_tree E), G.is_quasi_strategy P f ∧ f.is_finite_play σ
                      ∧ (G.induced_subgame f).is_winning_position P σ

end game