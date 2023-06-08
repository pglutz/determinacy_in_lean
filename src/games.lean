import sequences

class game_tree (E : ℕ → Type) :=
(moves : Π {{n}}, finseq E n → set (E n))

namespace game_tree

variables {E : ℕ → Type} (T : game_tree E)

def is_subtree (T' : game_tree E) := ∀ n (σ : finseq E n), T.moves σ ⊆ T'.moves σ

def is_play (α : seq E) := ∀ n, α n ∈ T.moves (α.restrict n)

def is_finite_play {n} (σ : finseq E n) := ∀ k (h : k < n), σ.nth k h ∈ T.moves (σ.restrict k (le_of_lt h))

def is_leaf {n} (σ : finseq E n) := T.moves σ = ∅

end game_tree

class game (E : ℕ → Type) (β : Type) extends (game_tree E) :=
(turn : Π {{n}}, finseq E n → β)
(taboo : Π {{n}}, finseq E n → β)
(payoff : seq E → β)

namespace game

variables {E : ℕ → Type} {β : Type} (G : game E β)

-- nowhere in this definition do we require f to be a subgame of G
-- TODO: should we add this in this definition?
-- otherwise we need to mention it elsewhere that this is used (eg in is_quasi_strategy)
-- OR we could let moves := G.moves ∩ T.moves
def induced_game (T : game_tree E) : game E β :=
{ moves := T.moves,
  turn := G.turn,
  taboo := G.taboo,
  payoff := G.payoff }

def is_quasi_strategy (P : β) (T : game_tree E) :=
  (T.is_subtree G.to_game_tree) ∧ ∀ {n} (σ : finseq E n),
    (G.turn σ = P → G.moves σ ≠ ∅ → T.moves σ ≠ ∅)
    ∧ (G.turn σ ≠ P → T.moves σ = G.moves σ)

-- if σ is a leaf and taboo for P, then P WINS if we reach σ
-- this is because we are allowing a general set β of players, so it doesn't make
-- sense to say that it loses for P
-- TODO: maybe we should rename taboo to something else because of this?
def is_winning_position (P : β) {n} (σ : finseq E n) := ∀ α, G.is_play α → σ <<< α → G.payoff α = P
  ∧ ∀ {k} (τ : finseq E k), G.is_finite_play τ → G.is_leaf τ → σ <<< τ → G.taboo τ = P

def is_winnable_position (P : β) {n} (σ : finseq E n) :=
  ∃ (T : game_tree E), G.is_quasi_strategy P T ∧ T.is_finite_play σ
                      ∧ (G.induced_game T).is_winning_position P σ

end game