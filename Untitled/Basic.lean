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
  K5 := by intro y x; simp
  K6 := by intro x; simp
  K7 := by intro x; simp

/-- The holding cost `c(x,y) = x + y` lies in the cone. -/
theorem c_mem_cone : InCone c where
  K1 := by
    intro y x
    have h : c (x + 1, y) - c (x, y) = 1 := by simp only [c]; push_cast; ring
    linarith
  K2 := by
    intro y x
    have h : c (x + 2, y) - 2 * c (x + 1, y) + c (x, y) = 0 := by
      simp only [c]; push_cast; ring
    linarith
  K3 := by
    intro y x
    have h : c (x + 2, y.castSucc) + c (x, y.succ)
              - c (x + 1, y.castSucc) - c (x + 1, y.succ) = 0 := by
      simp only [c]; push_cast; ring
    linarith
  K4 := by
    intro y x
    have h : c (x, y.castSucc) + c (x + 1, y.succ)
              - c (x + 1, y.castSucc) - c (x, y.succ) = 0 := by
      simp only [c]; push_cast; ring
    linarith
  K5 := by
    intro y x
    fin_cases y <;>
      (simp only [c, Fin.val_castSucc, Fin.val_succ]; push_cast; linarith)
  K6 := by
    intro x
    have h : c (x, 0) + c (x, 2) - 2 * c (x, 1) = 0 := by
      simp only [c, Fin.val_zero, Fin.val_one, Fin.val_two]; push_cast; ring
    linarith
  K7 := by
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
  K5 := by intro y x; have := hf.K5 y x; have := hg.K5 y x; linarith
  K6 := by intro x; have := hf.K6 x; have := hg.K6 x; linarith
  K7 := by intro x; have := hf.K7 x; have := hg.K7 x; linarith

/-- The cone is closed under multiplication by a nonnegative scalar. -/
theorem cone_smul_nonneg {a : ℝ} (ha : 0 ≤ a) {f : ValueFn} (hf : InCone f) :
    InCone (fun s => a * f s) where
  K1 := by intro y x; have h := hf.K1 y x; nlinarith [mul_nonneg ha h]
  K2 := by intro y x; have h := hf.K2 y x; nlinarith [mul_nonneg ha h]
  K3 := by intro y x; have h := hf.K3 y x; nlinarith [mul_nonneg ha h]
  K4 := by intro y x; have h := hf.K4 y x; nlinarith [mul_nonneg ha h]
  K5 := by intro y x; have h := hf.K5 y x; nlinarith [mul_nonneg ha h]
  K6 := by intro x; have h := hf.K6 x; nlinarith [mul_nonneg ha h]
  K7 := by intro x; have h := hf.K7 x; nlinarith [mul_nonneg ha h]
