import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Untitled.Defs

/-!
# Basic properties of the cone

This file proves the simple properties of the cone:

* `zero_mem_cone` — the zero function lies in `𝒦`.
* `c_mem_cone` — the holding cost `c` lies in `𝒦`.
* `cone_add` — `𝒦` is closed under addition.
* `cone_smul_nonneg` — `𝒦` is closed under multiplication by a nonnegative scalar.
-/

/-- The zero function lies in the cone. -/
theorem zero_mem_cone : InCone (fun _ : State => (0 : ℝ)) where
  K1 := by intro y x; simp
  K2 := by intro y x; simp
  K3 := by intro y x; simp
  K4 := by intro y x; simp
  K5 := by intro x; simp
  K6 := by intro x; simp

/-- The holding cost `c(x,y) = x + y` lies in the cone. -/
theorem c_mem_cone : InCone c where
  K1 := by
    intro y x
    have h : c (x + 1, y) - c (x, y) = 1 := by simp only [c]; push_cast; ring
    linarith
  K2 := by
    intro y x
    have h : c (x + 2, y.castSucc) + c (x, y.succ)
              - c (x + 1, y.castSucc) - c (x + 1, y.succ) = 0 := by
      simp only [c]; push_cast; ring
    linarith
  K3 := by
    intro y x
    have h : c (x, y.castSucc) + c (x + 1, y.succ)
              - c (x + 1, y.castSucc) - c (x, y.succ) = 0 := by
      simp only [c]; push_cast; ring
    linarith
  K4 := by
    intro y x
    fin_cases y <;>
      (simp only [c, Fin.val_castSucc, Fin.val_succ]; push_cast; linarith)
  K5 := by
    intro x
    have h : c (x, 0) + c (x, 2) - 2 * c (x, 1) = 0 := by
      simp only [c, Fin.val_zero, Fin.val_one, Fin.val_two]; push_cast; ring
    linarith
  K6 := by
    intro x
    have h : c (x + 2, 0) + c (x, 2) - 2 * c (x + 1, 1) = 0 := by
      simp only [c, Fin.val_zero, Fin.val_one, Fin.val_two]; push_cast; ring
    linarith

/-- The cone is closed under addition. -/
theorem cone_add {f g : ValueFn} (hf : InCone f) (hg : InCone g) :
    InCone (fun s => f s + g s) where
  K1 := by intro y x; have := hf.K1 y x; have := hg.K1 y x; linarith
  K2 := by intro y x; have := hf.K2 y x; have := hg.K2 y x; linarith
  K3 := by intro y x; have := hf.K3 y x; have := hg.K3 y x; linarith
  K4 := by intro y x; have := hf.K4 y x; have := hg.K4 y x; linarith
  K5 := by intro x; have := hf.K5 x; have := hg.K5 x; linarith
  K6 := by intro x; have := hf.K6 x; have := hg.K6 x; linarith

/-- The cone is closed under multiplication by a nonnegative scalar. -/
theorem cone_smul_nonneg {a : ℝ} (ha : 0 ≤ a) {f : ValueFn} (hf : InCone f) :
    InCone (fun s => a * f s) where
  K1 := by intro y x; have h := hf.K1 y x; nlinarith [mul_nonneg ha h]
  K2 := by intro y x; have h := hf.K2 y x; nlinarith [mul_nonneg ha h]
  K3 := by intro y x; have h := hf.K3 y x; nlinarith [mul_nonneg ha h]
  K4 := by intro y x; have h := hf.K4 y x; nlinarith [mul_nonneg ha h]
  K5 := by intro x; have h := hf.K5 x; nlinarith [mul_nonneg ha h]
  K6 := by intro x; have h := hf.K6 x; nlinarith [mul_nonneg ha h]

theorem convex_x (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 3) (x : ℕ), f (x + 2, y) - 2 * f (x + 1, y) + f (x, y) ≥ 0 := by
  intro y x
  -- Diagonal condition (K2), both rows, Fin indices reduced to numerals.
  have K2_0 : ∀ a : ℕ,
      f (a + 2, 0) + f (a, 1) - f (a + 1, 0) - f (a + 1, 1) ≥ 0 := by
    intro a; have h := hf.K2 0 a
    have ec : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have es : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [ec, es] at h; linarith
  have K2_1 : ∀ a : ℕ,
      f (a + 2, 1) + f (a, 2) - f (a + 1, 1) - f (a + 1, 2) ≥ 0 := by
    intro a; have h := hf.K2 1 a
    have ec : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have es : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [ec, es] at h; linarith
  -- Multimodularity condition (K3), both rows.
  have K3_0 : ∀ a : ℕ,
      f (a, 0) + f (a + 1, 1) - f (a + 1, 0) - f (a, 1) ≥ 0 := by
    intro a; have h := hf.K3 0 a
    have ec : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have es : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [ec, es] at h; linarith
  have K3_1 : ∀ a : ℕ,
      f (a, 1) + f (a + 1, 2) - f (a + 1, 1) - f (a, 2) ≥ 0 := by
    intro a; have h := hf.K3 1 a
    have ec : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have es : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [ec, es] at h; linarith
  fin_cases y
  · show f (x + 2, 0) - 2 * f (x + 1, 0) + f (x, 0) ≥ 0
    linarith [K2_0 x, K3_0 x]
  · show f (x + 2, 1) - 2 * f (x + 1, 1) + f (x, 1) ≥ 0
    linarith [K2_1 x, K3_1 x]
  · show f (x + 2, 2) - 2 * f (x + 1, 2) + f (x, 2) ≥ 0
    linarith [K2_1 x, K3_1 (x + 1)]
