import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

import OneFastTwoSlow.Defs
import OneFastTwoSlow.Basic

/-!
# Closure of the cone 𝒦 under the relaxed assignment operator (Lemma 2)
-/

private abbrev Q : ValueFn → ValueFn := Q_modified

-- Row 0, position ≥ 2: three-way min.
private lemma Q0_eq (f : ValueFn) (k : ℕ) :
    Q f (k + 2, 0) = f (k + 2, 0) ∨ Q f (k + 2, 0) = f (k + 1, 1)
      ∨ Q f (k + 2, 0) = f (k, 2) := by
  simp only [Q_modified]
  rcases min_cases (f (k + 1, 1)) (f (k, 2)) with ⟨e, _⟩ | ⟨e, _⟩ <;>
  rcases min_cases (f (k + 2, 0)) (min (f (k + 1, 1)) (f (k, 2))) with ⟨E, _⟩ | ⟨E, _⟩
  · left; exact E
  · right; left; rw [E]; exact e
  · left; exact E
  · right; right; rw [E]; exact e

private lemma Q0_le (f : ValueFn) (k : ℕ) :
    Q f (k + 2, 0) ≤ f (k + 2, 0) ∧ Q f (k + 2, 0) ≤ f (k + 1, 1)
      ∧ Q f (k + 2, 0) ≤ f (k, 2) := by
  simp only [Q]
  exact ⟨min_le_left _ _,
         le_trans (min_le_right _ _) (min_le_left _ _),
         le_trans (min_le_right _ _) (min_le_right _ _)⟩

-- Row 0, position 1: two-way min.
private lemma Q0_pos1_eq (f : ValueFn) :
    Q f (1, 0) = f (1, 0) ∨ Q f (1, 0) = f (0, 1) := by
  simp only [Q]
  rcases min_cases (f (1, 0)) (f (0, 1)) with ⟨e, _⟩ | ⟨e, _⟩
  · left; exact e
  · right; exact e

private lemma Q0_pos1_le (f : ValueFn) :
    Q f (1, 0) ≤ f (1, 0) ∧ Q f (1, 0) ≤ f (0, 1) := by
  simp only [Q]; exact ⟨min_le_left _ _, min_le_right _ _⟩

-- Row 1, position ≥ 1: two-way min.
private lemma Q1_eq (f : ValueFn) (k : ℕ) :
    Q f (k + 1, 1) = f (k + 1, 1) ∨ Q f (k + 1, 1) = f (k, 2) := by
  simp only [Q]
  rcases min_cases (f (k + 1, 1)) (f (k, 2)) with ⟨e, _⟩ | ⟨e, _⟩
  · left; exact e
  · right; exact e

private lemma Q1_le (f : ValueFn) (k : ℕ) :
    Q f (k + 1, 1) ≤ f (k + 1, 1) ∧ Q f (k + 1, 1) ≤ f (k, 2) := by
  simp only [Q]; exact ⟨min_le_left _ _, min_le_right _ _⟩

/-- (K1) Monotonicity in `x` at fixed `y` for `Q f`. Paper page 8 table. -/
private theorem Q_preserves_K1 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 3) (x : ℕ), Q f (x + 1, y) - Q f (x, y) ≥ 0 := by
  intro y x
  -- Reduce `_ - _ ≥ 0` to `Q f (x, y) ≤ Q f (x + 1, y)`.
  rw [ge_iff_le, sub_nonneg]
  -- K1 fact for f, as a plain `≤` statement.
  have K1 : ∀ (z : Fin 3) (a : ℕ), f (a, z) ≤ f (a + 1, z) := by
    intro z a; have := hf.K1 z a; linarith
  -- K4 facts for f, with the Fin 2 → Fin 3 indices reduced to numerals.
  have K4_01 : ∀ (a : ℕ), f (a, 0) ≤ f (a, 1) := by
    intro a
    have h := hf.K4 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h
    linarith
  have K4_12 : ∀ (a : ℕ), f (a, 1) ≤ f (a, 2) := by
    intro a
    have h := hf.K4 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h
    linarith
  fin_cases y
  -- ── y = 0 ──────────────────────────────────────────────────────────
  · match x with
    | 0 =>
      show Q f (0, 0) ≤ Q f (1, 0)
      simp only [Q]
      exact le_min (K1 0 0) (K4_01 0)
    | 1 =>
      show Q f (1, 0) ≤ Q f (2, 0)
      simp only [Q]
      apply le_min
      · exact le_trans (min_le_left _ _) (K1 0 1)
      · apply le_min
        · exact le_trans (min_le_right _ _) (K1 1 0)
        · exact le_trans (min_le_right _ _) (K4_12 0)
    | k + 2 =>
      show Q f (k + 2, 0) ≤ Q f (k + 3, 0)
      simp only [Q]
      exact min_le_min (K1 0 (k + 2)) (min_le_min (K1 1 (k + 1)) (K1 2 k))
  -- ── y = 1 ──────────────────────────────────────────────────────────
  · match x with
    | 0 =>
      show Q f (0, 1) ≤ Q f (1, 1)
      simp only [Q]
      exact le_min (K1 1 0) (K4_12 0)
    | k + 1 =>
      show Q f (k + 1, 1) ≤ Q f (k + 2, 1)
      simp only [Q]
      exact min_le_min (K1 1 (k + 1)) (K1 2 k)
  -- ── y = 2 ──────────────────────────────────────────────────────────
  · show Q f (x, 2) ≤ Q f (x + 1, 2)
    simp only [Q]
    exact K1 2 x

/-- (K2) Diagonal increasing differences for `Q f`. Follows from
`A_mono`, `B_mono` via `Ā = min(A, 0)`, `B̄ = min(B, 0)`. Paper page 7. -/
private theorem Q_preserves_K2 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 2) (x : ℕ),
      Q f (x + 2, y.castSucc) + Q f (x, y.succ)
        - Q f (x + 1, y.castSucc) - Q f (x + 1, y.succ) ≥ 0 := by
  intro y x
  -- Cone-fact menu for f (same helpers as K2).
  have K1 : ∀ (z : Fin 3) (a : ℕ), f (a, z) ≤ f (a + 1, z) := by
    intro z a; have := hf.K1 z a; linarith
  have K2_0 : ∀ (a : ℕ),
      f (a + 2, 0) + f (a, 1) - f (a + 1, 0) - f (a + 1, 1) ≥ 0 := by
    intro a; have h := hf.K2 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K2_1 : ∀ (a : ℕ),
      f (a + 2, 1) + f (a, 2) - f (a + 1, 1) - f (a + 1, 2) ≥ 0 := by
    intro a; have h := hf.K2 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K3_0 : ∀ (a : ℕ),
      f (a, 0) + f (a + 1, 1) - f (a + 1, 0) - f (a, 1) ≥ 0 := by
    intro a; have h := hf.K3 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K3_1 : ∀ (a : ℕ),
      f (a, 1) + f (a + 1, 2) - f (a + 1, 1) - f (a, 2) ≥ 0 := by
    intro a; have h := hf.K3 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K4_01 : ∀ (a : ℕ), f (a, 0) ≤ f (a, 1) := by
    intro a; have h := hf.K4 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K4_12 : ∀ (a : ℕ), f (a, 1) ≤ f (a, 2) := by
    intro a; have h := hf.K4 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K5 : ∀ (a : ℕ), f (a, 0) + f (a, 2) - 2 * f (a, 1) ≥ 0 := by
    intro a; have := hf.K5 a; linarith
  have K6 : ∀ (a : ℕ), f (a + 2, 0) + f (a, 2) - 2 * f (a + 1, 1) ≥ 0 := by
    intro a; have := hf.K6 a; linarith
  fin_cases y
  -- ════════════════ y = 0 :  Ā nondecreasing ════════════════
  · match x with
    | 0 =>
      show Q f (2, 0) + Q f (0, 1) - Q f (1, 0) - Q f (1, 1) ≥ 0
      -- "+" points get exact values; "−" points get upper bounds.
      have hP1 := Q0_eq f 0                      -- Q f (2,0)
      have hP1' := Q0_le f 0
      have hP2 : Q f (0, 1) = f (0, 1) := by simp only [Q_modified]
      have hM1 := Q0_pos1_le f                   -- Q f (1,0) ≤ branches
      have hM2 := Q1_le f 0                       -- Q f (1,1) ≤ branches
      rcases hP1 with e | e | e <;> rw [e, hP2] <;>
      linarith [K1 0 0, K1 0 1, K1 1 0, K2_0 0, K2_1 0, K3_0 0, K3_1 0,
                K4_01 0, K4_12 0, K5 0, K6 0,
                hM1.1, hM1.2, hM2.1, hM2.2,
                hP1'.1, hP1'.2.1, hP1'.2.2]
    | k + 1 =>
      show Q f (k + 3, 0) + Q f (k + 1, 1) - Q f (k + 2, 0) - Q f (k + 2, 1) ≥ 0
      have hP1 := Q0_eq f (k + 1)                 -- Q f (k+3,0)
      have hP1' := Q0_le f (k + 1)
      have hP2 := Q1_eq f k                       -- Q f (k+1,1)
      have hP2' := Q1_le f k
      have hM1 := Q0_le f k                        -- Q f (k+2,0) ≤ branches
      have hM2 := Q1_le f (k + 1)                  -- Q f (k+2,1) ≤ branches
      rcases hP1 with e1 | e1 | e1 <;> rcases hP2 with e2 | e2 <;>
      rw [e1, e2] <;>
      linarith [K1 0 k, K1 0 (k+1), K1 0 (k+2), K1 1 k, K1 1 (k+1), K1 2 k,
                K2_0 k, K2_0 (k+1), K2_1 k, K2_1 (k+1),
                K3_0 k, K3_0 (k+1), K3_1 k, K3_1 (k+1),
                K4_01 k, K4_01 (k+1), K4_12 k, K4_12 (k+1),
                K5 k, K5 (k+1), K5 (k+2), K6 k, K6 (k+1),
                hM1.1, hM1.2.1, hM1.2.2, hM2.1, hM2.2,
                hP1'.1, hP1'.2.1, hP1'.2.2, hP2'.1, hP2'.2]
  -- ════════════════ y = 1 :  B̄ nondecreasing (no boundary split) ════════════════
  · show Q f (x + 2, 1) + Q f (x, 2) - Q f (x + 1, 1) - Q f (x + 1, 2) ≥ 0
    -- Row 2 is exact everywhere; row 1 is the two-way min everywhere.
    have hP1 := Q1_eq f (x + 1)                   -- Q f (x+2,1)
    have hP1' := Q1_le f (x + 1)
    have hP2 : Q f (x, 2) = f (x, 2) := by simp only [Q_modified]
    have hM1 := Q1_le f x                          -- Q f (x+1,1) ≤ branches
    have hM2 : Q f (x + 1, 2) = f (x + 1, 2) := by simp only [Q_modified]
    rcases hP1 with e | e <;> rw [e, hP2, hM2] <;>
    linarith [K1 1 x, K1 2 x, K2_1 x, K2_1 (x+1), K3_1 x, K3_1 (x+1),
              K4_12 x, K4_12 (x+1), K5 x, K5 (x+1), K6 x,
              hM1.1, hM1.2, hP1'.1, hP1'.2]

/-- (K3) Right multimodularity for `Q f`. Paper pages 9–11. -/
private theorem Q_preserves_K3 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 2) (x : ℕ),
      Q f (x, y.castSucc) + Q f (x + 1, y.succ)
        - Q f (x + 1, y.castSucc) - Q f (x, y.succ) ≥ 0 := by
  intro y x
  -- Cone-fact menu for f (same helpers as K2/K2).
  have K1 : ∀ (z : Fin 3) (a : ℕ), f (a, z) ≤ f (a + 1, z) := by
    intro z a; have := hf.K1 z a; linarith
  have K2 : ∀ (z : Fin 3) (a : ℕ),
      f (a, z) + f (a + 2, z) - 2 * f (a + 1, z) ≥ 0 := by
    intro z a; have := convex_x f hf z a; linarith
  have K2_0 : ∀ (a : ℕ),
      f (a + 2, 0) + f (a, 1) - f (a + 1, 0) - f (a + 1, 1) ≥ 0 := by
    intro a; have h := hf.K2 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K2_1 : ∀ (a : ℕ),
      f (a + 2, 1) + f (a, 2) - f (a + 1, 1) - f (a + 1, 2) ≥ 0 := by
    intro a; have h := hf.K2 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K3_0 : ∀ (a : ℕ),
      f (a, 0) + f (a + 1, 1) - f (a + 1, 0) - f (a, 1) ≥ 0 := by
    intro a; have h := hf.K3 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K3_1 : ∀ (a : ℕ),
      f (a, 1) + f (a + 1, 2) - f (a + 1, 1) - f (a, 2) ≥ 0 := by
    intro a; have h := hf.K3 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K4_01 : ∀ (a : ℕ), f (a, 0) ≤ f (a, 1) := by
    intro a; have h := hf.K4 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K4_12 : ∀ (a : ℕ), f (a, 1) ≤ f (a, 2) := by
    intro a; have h := hf.K4 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K5 : ∀ (a : ℕ), f (a, 0) + f (a, 2) - 2 * f (a, 1) ≥ 0 := by
    intro a; have := hf.K5 a; linarith
  have K6 : ∀ (a : ℕ), f (a + 2, 0) + f (a, 2) - 2 * f (a + 1, 1) ≥ 0 := by
    intro a; have := hf.K6 a; linarith
  fin_cases y
  -- ════════════════ y = 0 ════════════════
  · match x with
    | 0 =>
      show Q f (0, 0) + Q f (1, 1) - Q f (1, 0) - Q f (0, 1) ≥ 0
      have hP0 : Q f (0, 0) = f (0, 0) := by simp only [Q_modified]   -- "+", exact
      have hP1 := Q1_eq f 0                                   -- "+", Q f (1,1)
      have hP1' := Q1_le f 0
      have hM1 := Q0_pos1_le f                                -- "−", Q f (1,0)
      have hM2 : Q f (0, 1) = f (0, 1) := by simp only [Q_modified]    -- "−", exact
      rcases hP1 with e | e <;> rw [hP0, e, hM2] <;>
      linarith [K1 0 0, K1 1 0, K2_0 0, K3_0 0, K3_1 0,
                K4_01 0, K4_12 0, K5 0, K6 0,
                hM1.1, hM1.2, hP1'.1, hP1'.2]
    | 1 =>
      show Q f (1, 0) + Q f (2, 1) - Q f (2, 0) - Q f (1, 1) ≥ 0
      have hP1 := Q0_pos1_eq f                                -- "+", Q f (1,0)
      have hP1' := Q0_pos1_le f
      have hP2 := Q1_eq f 1                                   -- "+", Q f (2,1)
      have hP2' := Q1_le f 1
      have hM1 := Q0_le f 0                                   -- "−", Q f (2,0)
      have hM2 := Q1_le f 0                                   -- "−", Q f (1,1)
      rcases hP1 with e1 | e1 <;> rcases hP2 with e2 | e2 <;>
      rw [e1, e2] <;>
      linarith [K1 0 0, K1 0 1, K1 1 0, K1 1 1, K1 2 0,
                K2 0 0, K2 1 0, K2_0 0, K2_0 1, K2_1 0, K2_1 1,
                K3_0 0, K3_0 1, K3_1 0, K3_1 1,
                K4_01 0, K4_01 1, K4_12 0, K4_12 1, K5 0, K5 1, K6 0, K6 1,
                hM1.1, hM1.2.1, hM1.2.2, hM2.1, hM2.2,
                hP1'.1, hP1'.2, hP2'.1, hP2'.2]
    | k + 2 =>
      show Q f (k + 2, 0) + Q f (k + 3, 1) - Q f (k + 3, 0) - Q f (k + 2, 1) ≥ 0
      have hP1 := Q0_eq f k                                   -- "+", Q f (k+2,0)
      have hP1' := Q0_le f k
      have hP2 := Q1_eq f (k + 2)                             -- "+", Q f (k+3,1)
      have hP2' := Q1_le f (k + 2)
      have hM1 := Q0_le f (k + 1)                             -- "−", Q f (k+3,0)
      have hM2 := Q1_le f (k + 1)                             -- "−", Q f (k+2,1)
      rcases hP1 with e1 | e1 | e1 <;> rcases hP2 with e2 | e2 <;>
      rw [e1, e2] <;>
      linarith [K1 0 k, K1 0 (k+1), K1 0 (k+2), K1 1 k, K1 1 (k+1), K1 1 (k+2),
                K1 2 k, K1 2 (k+1), K2 0 k, K2 0 (k+1), K2 1 k, K2 1 (k+1),
                K2 2 k, K2 2 (k+1),
                K2_0 k, K2_0 (k+1), K2_0 (k+2), K2_1 k, K2_1 (k+1), K2_1 (k+2),
                K3_0 k, K3_0 (k+1), K3_0 (k+2), K3_1 k, K3_1 (k+1), K3_1 (k+2),
                K4_01 k, K4_01 (k+1), K4_01 (k+2), K4_12 k, K4_12 (k+1), K4_12 (k+2),
                K5 k, K5 (k+1), K5 (k+2), K6 k, K6 (k+1),
                hM1.1, hM1.2.1, hM1.2.2, hM2.1, hM2.2,
                hP1'.1, hP1'.2.1, hP1'.2.2, hP2'.1, hP2'.2]
  -- ════════════════ y = 1 ════════════════
  · match x with
    | 0 =>
      show Q f (0, 1) + Q f (1, 2) - Q f (1, 1) - Q f (0, 2) ≥ 0
      have hP1 : Q f (0, 1) = f (0, 1) := by simp only [Q_modified]    -- "+", exact
      have hP2 : Q f (1, 2) = f (1, 2) := by simp only [Q_modified]    -- "+", exact
      have hM1 := Q1_le f 0                                   -- "−", Q f (1,1)
      have hM2 : Q f (0, 2) = f (0, 2) := by simp only [Q_modified]    -- "−", exact
      rw [hP1, hP2, hM2]
      linarith [K1 1 0, K2 2 0, K2_1 0, K3_1 0, K4_12 0, K5 0, K6 0,
                hM1.1, hM1.2]
    | k + 1 =>
      show Q f (k + 1, 1) + Q f (k + 2, 2) - Q f (k + 2, 1) - Q f (k + 1, 2) ≥ 0
      have hP1 := Q1_eq f k                                   -- "+", Q f (k+1,1)
      have hP1' := Q1_le f k
      have hP2 : Q f (k + 2, 2) = f (k + 2, 2) := by simp only [Q_modified]  -- "+", exact
      have hM1 := Q1_le f (k + 1)                             -- "−", Q f (k+2,1)
      have hM2 : Q f (k + 1, 2) = f (k + 1, 2) := by simp only [Q_modified]  -- "−", exact
      rcases hP1 with e | e <;> rw [e, hP2, hM2] <;>
      linarith [K1 1 k, K1 1 (k+1), K1 2 k, K1 2 (k+1),
                K2 1 k, K2 2 k, K2_1 k, K2_1 (k+1), K3_1 k, K3_1 (k+1),
                K4_12 k, K4_12 (k+1), K5 k, K5 (k+1), K6 k,
                hM1.1, hM1.2, hP1'.1, hP1'.2]

/-- (K4) Monotonicity in `y` at fixed `x` for `Q f`. Paper page 11. -/
private theorem Q_preserves_K4 (f : ValueFn) (hf : InCone f) :
    ∀ (y : Fin 2) (x : ℕ), Q f (x, y.succ) - Q f (x, y.castSucc) ≥ 0 := by
  intro y x
  -- The only cone facts K4 needs are (K1) and (K4) of f.
  have K1 : ∀ (z : Fin 3) (a : ℕ), f (a, z) ≤ f (a + 1, z) := by
    intro z a; have := hf.K1 z a; linarith
  have K4_01 : ∀ (a : ℕ), f (a, 0) ≤ f (a, 1) := by
    intro a; have h := hf.K4 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K4_12 : ∀ (a : ℕ), f (a, 1) ≤ f (a, 2) := by
    intro a; have h := hf.K4 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  fin_cases y
  -- ════════════════ y = 0 :  Q f (x,1) ≥ Q f (x,0) ════════════════
  · match x with
    | 0 =>
      show Q f (0, 1) - Q f (0, 0) ≥ 0
      have h1 : Q f (0, 1) = f (0, 1) := by simp only [Q_modified]
      have h0 : Q f (0, 0) = f (0, 0) := by simp only [Q_modified]
      rw [h1, h0]; linarith [K4_01 0]
    | 1 =>
      show Q f (1, 1) - Q f (1, 0) ≥ 0
      -- Q f (1,1) = min (f(1,1)) (f(0,2));  Q f (1,0) = min (f(1,0)) (f(0,1))
      have hP := Q1_eq f 0          -- exact value of the upper point Q f (1,1)
      have hM := Q0_pos1_le f       -- upper bounds on Q f (1,0)
      rcases hP with e | e <;> rw [e] <;>
      linarith [K1 1 0, K4_01 1, K4_12 0, hM.1, hM.2]
    | k + 2 =>
      show Q f (k + 2, 1) - Q f (k + 2, 0) ≥ 0
      have hP := Q1_eq f (k + 1)    -- exact value of Q f (k+2,1)
      have hM := Q0_le f k          -- upper bounds on Q f (k+2,0)
      rcases hP with e | e <;> rw [e] <;>
      linarith [K1 1 (k + 1), K1 2 k, hM.1, hM.2.1, hM.2.2]
  -- ════════════════ y = 1 :  Q f (x,2) ≥ Q f (x,1) ════════════════
  · match x with
    | 0 =>
      show Q f (0, 2) - Q f (0, 1) ≥ 0
      have h2 : Q f (0, 2) = f (0, 2) := by simp only [Q_modified]
      have h1 : Q f (0, 1) = f (0, 1) := by simp only [Q_modified]
      rw [h2, h1]; linarith [K4_12 0]
    | k + 1 =>
      show Q f (k + 1, 2) - Q f (k + 1, 1) ≥ 0
      -- Q f (k+1,2) = f(k+1,2) (exact);  Q f (k+1,1) bounded above
      have h2 : Q f (k + 1, 2) = f (k + 1, 2) := by simp only [Q_modified]
      have hM := Q1_le f k          -- upper bounds on Q f (k+1,1)
      rw [h2]
      linarith [K1 2 k, K4_12 (k + 1), hM.1, hM.2]

/-- (K5) Convexity in `y` at fixed `x` for `Q f`. Paper pages 11–12. -/
private theorem Q_preserves_K5 (f : ValueFn) (hf : InCone f) :
    ∀ x : ℕ, Q f (x, 0) + Q f (x, 2) - 2 * Q f (x, 1) ≥ 0 := by
  intro x
  -- Cone-fact menu for f (same helpers as K2/K2/K3).
  have K1 : ∀ (z : Fin 3) (a : ℕ), f (a, z) ≤ f (a + 1, z) := by
    intro z a; have := hf.K1 z a; linarith
  have K2 : ∀ (z : Fin 3) (a : ℕ),
      f (a, z) + f (a + 2, z) - 2 * f (a + 1, z) ≥ 0 := by
    intro z a; have := convex_x f hf z a; linarith
  have K3_0 : ∀ (a : ℕ),
      f (a, 0) + f (a + 1, 1) - f (a + 1, 0) - f (a, 1) ≥ 0 := by
    intro a; have h := hf.K3 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K3_1 : ∀ (a : ℕ),
      f (a, 1) + f (a + 1, 2) - f (a + 1, 1) - f (a, 2) ≥ 0 := by
    intro a; have h := hf.K3 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K4_01 : ∀ (a : ℕ), f (a, 0) ≤ f (a, 1) := by
    intro a; have h := hf.K4 0 a
    have e0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have e1 : ((0 : Fin 2).succ : Fin 3) = 1 := rfl
    rw [e0, e1] at h; linarith
  have K4_12 : ∀ (a : ℕ), f (a, 1) ≤ f (a, 2) := by
    intro a; have h := hf.K4 1 a
    have e1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have e2 : ((1 : Fin 2).succ : Fin 3) = 2 := rfl
    rw [e1, e2] at h; linarith
  have K5 : ∀ (a : ℕ), f (a, 0) + f (a, 2) - 2 * f (a, 1) ≥ 0 := by
    intro a; have := hf.K5 a; linarith
  match x with
  | 0 =>
    -- All three points exact: Q f(0,0)=f(0,0), Q f(0,1)=f(0,1), Q f(0,2)=f(0,2).
    show Q f (0, 0) + Q f (0, 2) - 2 * Q f (0, 1) ≥ 0
    have h0 : Q f (0, 0) = f (0, 0) := by simp only [Q_modified]
    have h1 : Q f (0, 1) = f (0, 1) := by simp only [Q_modified]
    have h2 : Q f (0, 2) = f (0, 2) := by simp only [Q_modified]
    rw [h0, h1, h2]; linarith [K5 0]
  | 1 =>
    show Q f (1, 0) + Q f (1, 2) - 2 * Q f (1, 1) ≥ 0
    have hP0 := Q0_pos1_eq f          -- "+", Q f (1,0)
    have hP0' := Q0_pos1_le f
    have hP2 : Q f (1, 2) = f (1, 2) := by simp only [Q_modified]   -- "+", exact
    have hM := Q1_le f 0              -- "−", Q f (1,1): both upper bounds
    rcases hP0 with e | e <;> rw [e, hP2] <;>
    linarith [K1 1 0, K3_1 0, K4_01 0, K4_01 1, K4_12 0, K5 0, K5 1,
              hM.1, hM.2]
  | k + 2 =>
    show Q f (k + 2, 0) + Q f (k + 2, 2) - 2 * Q f (k + 2, 1) ≥ 0
    have hP0 := Q0_eq f k             -- "+", Q f (k+2,0)
    have hP0' := Q0_le f k
    have hP2 : Q f (k + 2, 2) = f (k + 2, 2) := by simp only [Q_modified]  -- "+", exact
    have hM := Q1_le f (k + 1)        -- "−", Q f (k+2,1): both upper bounds
    rcases hP0 with e | e | e <;> rw [e, hP2] <;>
    linarith [K1 0 (k+1), K1 1 (k+1), K1 2 k, K2 1 k, K2 2 k,
              K3_0 (k+1), K3_1 (k+1), K4_01 (k+1), K4_12 k, K4_12 (k+1),
              K5 (k+1), K5 (k+2),
              hM.1, hM.2]

/-- (K6) Convexity in slow-server count at fixed total population for
`Q f`. Follows from `A_ge_B` via `Ā ≥ B̄`. Paper page 7. -/
private theorem Q_preserves_K6 (f : ValueFn) (hf : InCone f) :
    ∀ x : ℕ, Q f (x + 2, 0) + Q f (x, 2) - 2 * Q f (x + 1, 1) ≥ 0 := by
  intro x
  have K6 : ∀ (a : ℕ), f (a + 2, 0) + f (a, 2) - 2 * f (a + 1, 1) ≥ 0 := by
    intro a; have := hf.K6 a; linarith
  -- Q f (x+2,0) exact (3-way); Q f (x,2) exact; Q f (x+1,1) bounded above (both).
  have hP0 := Q0_eq f x                         -- Q f (x+2,0)
  have hP2 : Q f (x, 2) = f (x, 2) := by simp only [Q_modified]
  have hM := Q1_le f x                          -- Q f (x+1,1) ≤ f(x+1,1), ≤ f(x,2)
  rcases hP0 with e | e | e <;> rw [e, hP2] <;>
  linarith [K6 x, hM.1, hM.2]

theorem Q_preserves_cone (f : ValueFn) (hf : InCone f) : InCone (Q f) where
  K1 := Q_preserves_K1 f hf
  K2 := Q_preserves_K2 f hf
  K3 := Q_preserves_K3 f hf
  K4 := Q_preserves_K4 f hf
  K5 := Q_preserves_K5 f hf
  K6 := Q_preserves_K6 f hf
