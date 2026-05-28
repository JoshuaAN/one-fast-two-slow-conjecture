import Mathlib.Data.Real.Basic

/-!
# Definitions for the one-fast / two-slow server model

This file defines the state space, model parameters, holding cost, the event operator `P`,
and the invariant cone `InCone`.

## Main definitions

* `State` - the post-decision state `(x, y) : ℕ × Fin 3`, where `x` is the number of
  customers either waiting in the queue or in the fast server, and `y` is the number of
  busy slow servers.
* `ValueFn` - a real-valued function on the states
* `QueueParams` - the model parameters
* `P` - the event operator
* `c` - the one-step holding cost
* `InCone` - the cone `𝒦` of value functions satisfying all seven invariant equalities
  (K1)-(K7).
-/

/-- The state of the queueing system.

The first component is the number of customers in the queue plus the one in the fast
server (if any). The second component is the number of busy slow servers, ranging over
`{0, 1, 2}`.
-/
abbrev State := ℕ × Fin 3

/-- A real-valued function on the states. -/
abbrev ValueFn := State → ℝ

/-- Parameters of the queueing model.

* `μ₁` - fast server service rate
* `μ₂` - slow server service rate (both slow servers have rate `μ₂`)
* `Λ` - Poisson arrival rate

The constraints are from the paper's assumptions in (1.1) -/
structure QueueParams where
  μ₁ : ℝ
  μ₂ : ℝ
  Λ : ℝ
  hμ_ord : μ₁ > μ₂
  hμ₂_pos : μ₂ > 0
  hΛ_nn : Λ ≥ 0

variable (p : QueueParams)

/-- The event operator, equations (1.13)-(1.15) of the paper. -/
def P (f : ValueFn) : ValueFn := fun (x, y) =>
  match y with
  | 0 => p.Λ * f (x+1, 0) + p.μ₁ * f (x-1, 0) + 2 * p.μ₂ * f (x, 0)
  | 1 => p.Λ * f (x+1, 1) + p.μ₁ * f (x-1, 1) + p.μ₂ * f (x, 0) + p.μ₂ * f (x, 1)
  | 2 => p.Λ * f (x+1, 2) + p.μ₁ * f (x-1, 2) + 2 * p.μ₂ * f (x, 1)

/-- The relaxed tail-minimum assignment operator, equation (1.19).

Note this is explicitly defined through casing to make the closure proof easier. Maybe
this should be proven to be equivalent to the min definition in the paper? Or maybe this
is obvious enough where it doesn't matter? -/
def Q (f : ValueFn) : ValueFn := fun (x, y) =>
  match y, x with
  | 0, 0       => f (0, 0)
  | 0, 1       => min (f (1, 0)) (f (0, 1))
  | 0, x + 2   => min (f (x + 2, 0)) (min (f (x + 1, 1)) (f (x, 2)))
  | 1, 0       => f (0, 1)
  | 1, x + 1   => min (f (x + 1, 1)) (f (x, 2))
  | 2, _       => f (x, 2)

/-- One-step holding cost, `c(x, y) = x + y`, equation (1.3) of the paper. This is the
    total number of customers in the system. -/
def c : ValueFn := fun (x, y) => (x : ℝ) + (y : ℝ)

/-- The invariant cone `𝒦` from §2 of the paper. -/
structure InCone (f : ValueFn) : Prop where
  K1 : ∀ (y : Fin 3) (x : ℕ), f (x + 1, y) - f (x, y) ≥ 0
  K2 : ∀ (y : Fin 3) (x : ℕ), f (x + 2, y) - 2 * f (x + 1, y) + f (x, y) ≥ 0
  K3 : ∀ (y : Fin 2) (x : ℕ),
    f (x + 2, y.castSucc) + f (x, y.succ) - f (x + 1, y.castSucc) - f (x + 1, y.succ) ≥ 0
  K4 : ∀ (y : Fin 2) (x : ℕ),
    f (x, y.castSucc) + f (x + 1, y.succ) - f (x + 1, y.castSucc) - f (x, y.succ) ≥ 0
  K5 : ∀ (y : Fin 2) (x : ℕ), f (x, y.succ) - f (x, y.castSucc) ≥ 0
  K6 : ∀ x : ℕ, f (x, 0) + f (x, 2) - 2 * f (x, 1) ≥ 0
  K7 : ∀ x : ℕ, f (x + 2, 0) + f (x, 2) - 2 * f (x + 1, 1) ≥ 0
