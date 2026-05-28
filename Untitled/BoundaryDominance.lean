import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Untitled.Defs
import Untitled.AssignmentClosure

/-!
# Boundary feasibility of the relaxed assignment operator (Lemma 4)

This file proves Lemma 4 of the paper (§5): one step of the relaxed value iteration
preserves the two boundary comparisons

* `V(1, 0) ≤ V(0, 1)`   (5.1)
* `V(1, 1) ≤ V(0, 2)`   (5.2)
-/

variable (p : QueueParams)

/-- Tail-order: `Q f (2,0) ≤ Q f (1,1)`, equation (5.3). -/
lemma tail_20_le_11 (f : ValueFn) : Q f (2, 0) ≤ Q f (1, 1) := by
  simp only [Q]; exact min_le_right _ _

/-- Tail-order: `Q f (1,0) ≤ Q f (0,1)`, equation (5.3). -/
lemma tail_10_le_01 (f : ValueFn) : Q f (1, 0) ≤ Q f (0, 1) := by
  simp only [Q]; exact min_le_right _ _

/-- Tail-order: `Q f (1,1) ≤ Q f (0,2)`, equation (5.3). -/
lemma tail_11_le_02 (f : ValueFn) : Q f (1, 1) ≤ Q f (0, 2) := by
  simp only [Q]; exact min_le_right _ _

/-- Tail-order: `Q f (2,1) ≤ Q f (1,2)`, needed for equation (5.5). -/
lemma tail_21_le_12 (f : ValueFn) : Q f (2, 1) ≤ Q f (1, 2) := by
  simp only [Q]; exact min_le_right _ _

private theorem step_b1 (ρ : ℝ) (hρ : 0 < ρ) (f : ValueFn) (hf : InCone f) :
    valueStep p ρ f (1, 0) ≤ valueStep p ρ f (0, 1) := by
  have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
  have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
  have hμsum  : 0 ≤ p.μ₁ + p.μ₂ := by linarith [p.hμ₂_pos, p.hμ_ord]
  have hμdiff : 0 ≤ p.μ₁ - p.μ₂ := by linarith [p.hμ_ord]
  -- W = Q f is in the cone (Lemma 2); monotonicity in x is its K1.
  have hW : InCone (Q f) := Q_preserves_cone f hf
  have hWmono : Q f (0, 0) ≤ Q f (1, 0) := by have := hW.K1 0 0; linarith
  -- The difference equals ρ · D, with D a nonnegative combination (paper eq 5.4).
  have key :
      valueStep p ρ f (0, 1) - valueStep p ρ f (1, 0)
        = ρ * ( p.Λ * (Q f (1, 1) - Q f (2, 0))
              + (p.μ₁ - p.μ₂) * (Q f (1, 0) - Q f (0, 0))
              + (p.μ₁ + p.μ₂) * (Q f (0, 1) - Q f (1, 0)) ) := by
    simp only [valueStep, c, P, Fin.isValue]   -- unfold first → exposes (1-1), (0-1)
    norm_num                                    -- reduce nat-sub and Fin casts
    ring
  -- D ≥ 0, using the tail-order lemmas and the x-monotonicity of Q f.
  have hD : 0 ≤ p.Λ * (Q f (1, 1) - Q f (2, 0))
              + (p.μ₁ - p.μ₂) * (Q f (1, 0) - Q f (0, 0))
              + (p.μ₁ + p.μ₂) * (Q f (0, 1) - Q f (1, 0)) := by
    have t1 : 0 ≤ p.Λ * (Q f (1, 1) - Q f (2, 0)) :=
      mul_nonneg hΛ_nn (by linarith [tail_20_le_11 f])
    have t2 : 0 ≤ (p.μ₁ - p.μ₂) * (Q f (1, 0) - Q f (0, 0)) :=
      mul_nonneg hμdiff (by linarith)
    have t3 : 0 ≤ (p.μ₁ + p.μ₂) * (Q f (0, 1) - Q f (1, 0)) :=
      mul_nonneg hμsum (by linarith [tail_10_le_01 f])
    linarith
  -- ρ · D ≥ 0, hence the difference ≥ 0.
  have : 0 ≤ valueStep p ρ f (0, 1) - valueStep p ρ f (1, 0) := by
    rw [key]; exact mul_nonneg hρ.le hD
  linarith

private theorem step_b2 (ρ : ℝ) (hρ : 0 < ρ) (f : ValueFn) (hf : InCone f) :
    valueStep p ρ f (1, 1) ≤ valueStep p ρ f (0, 2) := by
  have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
  have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
  have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
  have hμdiff : 0 ≤ p.μ₁ - p.μ₂ := by linarith [p.hμ_ord]
  -- W = Q f is in the cone (Lemma 2); monotonicity in x is its K1.
  have hW : InCone (Q f) := Q_preserves_cone f hf
  have hWmono : Q f (0, 1) ≤ Q f (1, 1) := by have := hW.K1 1 0; linarith
  -- The difference equals ρ · D, with D a nonnegative combination (paper eq 5.5).
  have key :
      valueStep p ρ f (0, 2) - valueStep p ρ f (1, 1)
        = ρ * ( p.Λ * (Q f (1, 2) - Q f (2, 1))
              + (p.μ₁ - p.μ₂) * (Q f (1, 1) - Q f (0, 1))
              + p.μ₁ * (Q f (0, 2) - Q f (1, 1))
              + p.μ₂ * (Q f (0, 1) - Q f (1, 0)) ) := by
    simp only [valueStep, c, P, Fin.isValue]
    norm_num
    ring
  -- D ≥ 0, using the tail-order lemmas and the x-monotonicity of Q f.
  have hD : 0 ≤ p.Λ * (Q f (1, 2) - Q f (2, 1))
              + (p.μ₁ - p.μ₂) * (Q f (1, 1) - Q f (0, 1))
              + p.μ₁ * (Q f (0, 2) - Q f (1, 1))
              + p.μ₂ * (Q f (0, 1) - Q f (1, 0)) := by
    have t1 : 0 ≤ p.Λ * (Q f (1, 2) - Q f (2, 1)) :=
      mul_nonneg hΛ_nn (by linarith [tail_21_le_12 f])
    have t2 : 0 ≤ (p.μ₁ - p.μ₂) * (Q f (1, 1) - Q f (0, 1)) :=
      mul_nonneg hμdiff (by linarith)
    have t3 : 0 ≤ p.μ₁ * (Q f (0, 2) - Q f (1, 1)) :=
      mul_nonneg hμ₁_nn (by linarith [tail_11_le_02 f])
    have t4 : 0 ≤ p.μ₂ * (Q f (0, 1) - Q f (1, 0)) :=
      mul_nonneg hμ₂_nn (by linarith [tail_10_le_01 f])
    linarith
  -- ρ · D ≥ 0, hence the difference ≥ 0.
  have : 0 ≤ valueStep p ρ f (0, 2) - valueStep p ρ f (1, 1) := by
    rw [key]; exact mul_nonneg hρ.le hD
  linarith

theorem boundary_dominance (ρ : ℝ) (hρ : 0 < ρ) (V : ValueFn) (hV : InCone V) :
    BoundaryComp (valueStep p ρ V) where
  b1 := step_b1 p ρ hρ V hV
  b2 := step_b2 p ρ hρ V hV
