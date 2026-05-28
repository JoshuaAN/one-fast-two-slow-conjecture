import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Untitled.Defs

/-!
# Closure of the cone 𝒦 under the event operator (Lemma 3)
-/

variable (p : QueueParams)

-- K closure under P
private theorem P_preserves_K1 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 3) (x : ℕ), P p f (x + 1, y) - P p f (x, y) ≥ 0 := by
  intro y x
  have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
  have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
  have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
  have h2μ₂_nn : (0 : ℝ) ≤ 2 * p.μ₂ := by linarith
  have hfast : ∀ z : Fin 3, 0 ≤ f (x, z) - f (x - 1, z) := by
    intro z
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · have hsub : x - 1 + 1 = x := Nat.sub_add_cancel hx
      have h := hf.K1 z (x - 1)
      rwa [hsub] at h
  fin_cases y
  -- y = 0
  · simp [P]
    have h1 : 0 ≤ f (x + 1 + 1, 0) - f (x + 1, 0) := hf.K1 0 (x + 1)
    have h2 : 0 ≤ f (x + 1, 0) - f (x, 0)         := hf.K1 0 x
    have h3 : 0 ≤ f (x, 0) - f (x - 1, 0)         := hfast 0
    nlinarith [mul_nonneg hΛ_nn h1, mul_nonneg hμ₁_nn h3,
               mul_nonneg h2μ₂_nn h2]
  -- y = 1
  · simp [P]
    have h1 : 0 ≤ f (x + 1 + 1, 1) - f (x + 1, 1) := hf.K1 1 (x + 1)
    have h2a : 0 ≤ f (x + 1, 1) - f (x, 1)         := hf.K1 1 x
    have h2b : 0 ≤ f (x + 1, 0) - f (x, 0)         := hf.K1 0 x
    have h3  : 0 ≤ f (x, 1) - f (x - 1, 1)         := hfast 1
    nlinarith [mul_nonneg hΛ_nn h1, mul_nonneg hμ₁_nn h3,
               mul_nonneg hμ₂_nn h2a, mul_nonneg hμ₂_nn h2b]
  -- y = 1
  · simp [P]
    have h1 : 0 ≤ f (x + 1 + 1, 2) - f (x + 1, 2) := hf.K1 2 (x + 1)
    have h2 : 0 ≤ f (x + 1, 1) - f (x, 1)         := hf.K1 1 x
    have h3 : 0 ≤ f (x, 2) - f (x - 1, 2)         := hfast 2
    nlinarith [mul_nonneg hΛ_nn h1, mul_nonneg hμ₁_nn h3,
               mul_nonneg h2μ₂_nn h2]

private theorem P_preserves_K2 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 3) (x : ℕ), P p f (x + 2, y) - 2 * P p f (x + 1, y) + P p f (x, y) ≥ 0 := by
    intro y x
    -- Coefficient nonnegativity
    have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
    have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
    have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
    have h2μ₂_nn : (0 : ℝ) ≤ 2 * p.μ₂ := by linarith
    -- Boundary-extended convexity: 0 ≤ f(x+1, z) - 2 f(x, z) + f(x-1, z) for all z.
    have hatC : ∀ z : Fin 3, 0 ≤ f (x + 1, z) - 2 * f (x, z) + f (x - 1, z) := by
      intro z
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · have h := hf.K1 z 0; simp at h ⊢; linarith
      · have hsub1 : x - 1 + 1 = x := Nat.sub_add_cancel hx
        have hsub2 : x - 1 + 2 = x + 1 := by omega
        have h := hf.K2 z (x - 1)
        rw [hsub1, hsub2] at h
        linarith
    -- Normalize (x+2)-1 ↦ x+1, (x+1)-1 ↦ x in the goal.
    have e1 : (x + 2 : ℕ) - 1 = x + 1 := by omega
    have e2 : (x + 1 : ℕ) - 1 = x     := by omega
    fin_cases y
    -- y = 0
    · simp only [P]; rw [e1, e2]
      have h_lam  : 0 ≤ f (x + 1 + 2, 0) - 2 * f (x + 1 + 1, 0) + f (x + 1, 0) := hf.K2 0 (x + 1)
      have h_slow : 0 ≤ f (x + 2, 0)     - 2 * f (x + 1, 0)     + f (x, 0)     := hf.K2 0 x
      have h_bdry : 0 ≤ f (x + 1, 0)     - 2 * f (x, 0)         + f (x - 1, 0) := hatC 0
      nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
                mul_nonneg h2μ₂_nn h_slow]
    -- y = 1
    · simp only [P]; rw [e1, e2]
      have h_lam   : 0 ≤ f (x + 1 + 2, 1) - 2 * f (x + 1 + 1, 1) + f (x + 1, 1) := hf.K2 1 (x + 1)
      have h_slow0 : 0 ≤ f (x + 2, 0)     - 2 * f (x + 1, 0)     + f (x, 0)     := hf.K2 0 x
      have h_slow1 : 0 ≤ f (x + 2, 1)     - 2 * f (x + 1, 1)     + f (x, 1)     := hf.K2 1 x
      have h_bdry  : 0 ≤ f (x + 1, 1)     - 2 * f (x, 1)         + f (x - 1, 1) := hatC 1
      nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
                mul_nonneg hμ₂_nn h_slow0, mul_nonneg hμ₂_nn h_slow1]
    -- y = 2
    · simp only [P]; rw [e1, e2]
      have h_lam  : 0 ≤ f (x + 1 + 2, 2) - 2 * f (x + 1 + 1, 2) + f (x + 1, 2) := hf.K2 2 (x + 1)
      have h_slow : 0 ≤ f (x + 2, 1)     - 2 * f (x + 1, 1)     + f (x, 1)     := hf.K2 1 x
      have h_bdry : 0 ≤ f (x + 1, 2)     - 2 * f (x, 2)         + f (x - 1, 2) := hatC 2
      nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
                mul_nonneg h2μ₂_nn h_slow]

private theorem P_preserves_K3 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 2) (x : ℕ),
      P p f (x + 2, y.castSucc) + P p f (x, y.succ)
        - P p f (x + 1, y.castSucc) - P p f (x + 1, y.succ) ≥ 0 := by
  intro y x
  -- Coefficient nonnegativity
  have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
  have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
  have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
  -- Boundary-extended diagonal-difference M̂^f_y(x-1):
  -- at x = 0 it's K1 of f at 0 (in row z.castSucc);
  -- at x ≥ 1 it's K3 of f at x - 1.
  have hatM : ∀ z : Fin 2,
      0 ≤ f (x + 1, z.castSucc) + f (x - 1, z.succ)
            - f (x, z.castSucc) - f (x, z.succ) := by
    intro z
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · -- x = 0
      have h := hf.K1 z.castSucc 0
      simp; linarith
    · have hsub1 : x - 1 + 1 = x     := Nat.sub_add_cancel hx
      have hsub2 : x - 1 + 2 = x + 1 := by omega
      have h := hf.K3 z (x - 1)
      rw [hsub1, hsub2] at h
      linarith
  fin_cases y
  -- y = 0
  · simp [P]
    -- λ term
    have h_lam : 0 ≤ f (x + 1 + 2, 0) + f (x + 1, 1)
                       - f (x + 1 + 1, 0) - f (x + 1 + 1, 1) := hf.K3 0 (x + 1)
    -- μ₁ term
    have h_bdry : 0 ≤ f (x + 1, 0) + f (x - 1, 1) - f (x, 0) - f (x, 1) := hatM 0
    -- μ₂ terms
    have h_k2 : 0 ≤ f (x + 2, 0) - 2 * f (x + 1, 0) + f (x, 0)         := hf.K2 0 x
    have h_k3 : 0 ≤ f (x + 2, 0) + f (x, 1) - f (x + 1, 0) - f (x + 1, 1) := hf.K3 0 x
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
               mul_nonneg hμ₂_nn h_k2, mul_nonneg hμ₂_nn h_k3]
  -- y = 1
  · simp [P]
    -- λ term
    have h_lam : 0 ≤ f (x + 1 + 2, 1) + f (x + 1, 2)
                       - f (x + 1 + 1, 1) - f (x + 1 + 1, 2) := hf.K3 1 (x + 1)
    -- μ₁ term
    have h_bdry : 0 ≤ f (x + 1, 1) + f (x - 1, 2) - f (x, 1) - f (x, 2) := hatM 1
    -- μ₂ terms
    have h_k2 : 0 ≤ f (x + 2, 1) - 2 * f (x + 1, 1) + f (x, 1)         := hf.K2 1 x
    have h_k3 : 0 ≤ f (x + 2, 0) + f (x, 1) - f (x + 1, 0) - f (x + 1, 1) := hf.K3 0 x
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
               mul_nonneg hμ₂_nn h_k2, mul_nonneg hμ₂_nn h_k3]

private theorem P_preserves_K4 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 2) (x : ℕ),
      P p f (x, y.castSucc) + P p f (x + 1, y.succ)
        - P p f (x + 1, y.castSucc) - P p f (x, y.succ) ≥ 0 := by
  intro y x
  -- Coefficient nonnegativity
  have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
  have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
  have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
  have hatS : ∀ z : Fin 2,
      0 ≤ f (x - 1, z.castSucc) + f (x, z.succ)
            - f (x, z.castSucc) - f (x - 1, z.succ) := by
    intro z
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · -- x = 0
      simp
    · have hsub : x - 1 + 1 = x := Nat.sub_add_cancel hx
      have h := hf.K4 z (x - 1)
      rw [hsub] at h
      linarith
  -- Normalize (x+1) - 1 ↦ x in the goal (K4 doesn't touch (x+2) - 1).
  have e1 : (x + 1 : ℕ) - 1 = x := by omega
  fin_cases y
  -- y = 0
  · show P p f (x, 0) + P p f (x + 1, 1)
          - P p f (x + 1, 0) - P p f (x, 1) ≥ 0
    simp only [P]
    rw [e1]
    -- λ-term: K4 at x+1, row 0
    have h_lam  : 0 ≤ f (x + 1, 0) + f (x + 1 + 1, 1)
                       - f (x + 1 + 1, 0) - f (x + 1, 1) := hf.K4 0 (x + 1)
    -- μ₁-term: boundary Ŝ at x, row 0
    have h_bdry : 0 ≤ f (x - 1, 0) + f (x, 1) - f (x, 0) - f (x - 1, 1) := hatS 0
    -- μ₂-term: K4 at x, row 0
    have h_slow : 0 ≤ f (x, 0) + f (x + 1, 1) - f (x + 1, 0) - f (x, 1) := hf.K4 0 x
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
               mul_nonneg hμ₂_nn h_slow]
  -- y = 1
  · show P p f (x, 1) + P p f (x + 1, 2)
          - P p f (x + 1, 1) - P p f (x, 2) ≥ 0
    simp only [P]
    rw [e1]
    -- λ-term
    have h_lam  : 0 ≤ f (x + 1, 1) + f (x + 1 + 1, 2)
                       - f (x + 1 + 1, 1) - f (x + 1, 2) := hf.K4 1 (x + 1)
    -- μ₁-term
    have h_bdry : 0 ≤ f (x - 1, 1) + f (x, 2) - f (x, 1) - f (x - 1, 2) := hatS 1
    -- μ₂-term
    have h_slow : 0 ≤ f (x, 0) + f (x + 1, 1) - f (x + 1, 0) - f (x, 1) := hf.K4 0 x
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
               mul_nonneg hμ₂_nn h_slow]

private theorem P_preserves_K5 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 2) (x : ℕ), P p f (x, y.succ) - P p f (x, y.castSucc) ≥ 0 := by
  intro y x
  have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
  have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
  have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
  fin_cases y
  -- y = 0
  · show P p f (x, 1) - P p f (x, 0) ≥ 0
    simp only [P]
    -- λ-term
    have h_lam  : 0 ≤ f (x + 1, 1) - f (x + 1, 0) := hf.K5 0 (x + 1)
    -- μ₁-term
    have h_bdry : 0 ≤ f (x - 1, 1) - f (x - 1, 0) := hf.K5 0 (x - 1)
    -- μ₂-term
    have h_slow : 0 ≤ f (x, 1)     - f (x, 0)     := hf.K5 0 x
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
               mul_nonneg hμ₂_nn h_slow]
  -- y = 1
  · show P p f (x, 2) - P p f (x, 1) ≥ 0
    simp only [P]
    -- λ-term
    have h_lam  : 0 ≤ f (x + 1, 2) - f (x + 1, 1) := hf.K5 1 (x + 1)
    -- μ₁-term
    have h_bdry : 0 ≤ f (x - 1, 2) - f (x - 1, 1) := hf.K5 1 (x - 1)
    -- μ₂-term
    have h_slow : 0 ≤ f (x, 1)     - f (x, 0)     := hf.K5 0 x
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
               mul_nonneg hμ₂_nn h_slow]

private theorem P_preserves_K6 (f : ValueFn) (hf : InCone f) :
    ∀ x : ℕ, P p f (x, 0) + P p f (x, 2) - 2 * P p f (x, 1) ≥ 0 := by
    intro x
    have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
    have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
    simp only [P]
    -- λ-term: K6 of f at x+1
    have h_lam  : 0 ≤ f (x + 1, 0) + f (x + 1, 2) - 2 * f (x + 1, 1) := hf.K6 (x + 1)
    -- μ₁-term: K6 of f at x-1 (truncated subtraction — K6 holds at every ℕ)
    have h_bdry : 0 ≤ f (x - 1, 0) + f (x - 1, 2) - 2 * f (x - 1, 1) := hf.K6 (x - 1)
    -- μ₂ contribution is identically zero (slow-completion terms cancel)
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry]

private theorem P_preserves_K7 (f : ValueFn) (hf : InCone f) :
    ∀ x : ℕ, P p f (x + 2, 0) + P p f (x, 2) - 2 * P p f (x + 1, 1) ≥ 0 := by
    intro x
    -- Coefficient nonnegativity
    have hμ₁_nn : 0 ≤ p.μ₁ := (p.hμ₂_pos.trans p.hμ_ord).le
    have hμ₂_nn : 0 ≤ p.μ₂ := p.hμ₂_pos.le
    have hΛ_nn  : 0 ≤ p.Λ  := p.hΛ_nn
    have h2μ₂_nn : (0 : ℝ) ≤ 2 * p.μ₂ := by linarith
    have hatR : 0 ≤ f (x + 1, 0) + f (x - 1, 2) - 2 * f (x, 1) := by
      rcases Nat.eq_zero_or_pos x with rfl | hx
      · -- x = 0
        have hK1 := hf.K1 0 0
        have hK6 := hf.K6 0
        simp at hK1 ⊢
        linarith
      · -- x ≥ 1
        have hsub1 : x - 1 + 1 = x     := Nat.sub_add_cancel hx
        have hsub2 : x - 1 + 2 = x + 1 := by omega
        have h := hf.K7 (x - 1)
        rw [hsub1, hsub2] at h
        linarith
    have e1 : (x + 2 : ℕ) - 1 = x + 1 := by omega
    have e2 : (x + 1 : ℕ) - 1 = x     := by omega
    simp only [P]
    rw [e1, e2]
    -- λ-term
    have h_lam  : 0 ≤ f (x + 1 + 2, 0) + f (x + 1, 2) - 2 * f (x + 1 + 1, 1) := hf.K7 (x + 1)
    -- μ₁-term
    have h_bdry : 0 ≤ f (x + 1, 0) + f (x - 1, 2) - 2 * f (x, 1) := hatR
    -- 2μ₂-term
    have h_slow : 0 ≤ f (x + 2, 0) + f (x, 1) - f (x + 1, 0) - f (x + 1, 1) := hf.K3 0 x
    nlinarith [mul_nonneg hΛ_nn h_lam, mul_nonneg hμ₁_nn h_bdry,
              mul_nonneg h2μ₂_nn h_slow]

/-- Lemma 3 (Event closure). For every value function in the cone,
    applying the event operator keeps it in the cone. -/
theorem P_preserves_cone (f : ValueFn) (hf : InCone f) : InCone (P p f) where
  K1 := P_preserves_K1 p f hf
  K2 := P_preserves_K2 p f hf
  K3 := P_preserves_K3 p f hf
  K4 := P_preserves_K4 p f hf
  K5 := P_preserves_K5 p f hf
  K6 := P_preserves_K6 p f hf
  K7 := P_preserves_K7 p f hf
