import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import OneFastTwoSlow.Defs
import OneFastTwoSlow.AssignmentClosure
import OneFastTwoSlow.EventClosure
import OneFastTwoSlow.BoundaryDominance
import OneFastTwoSlow.Basic

/-!
# The relaxed and true value recursions coincide (Proposition 1)
-/

variable (p : QueueParams)

private abbrev Q : ValueFn → ValueFn := Q_modified

def iterate (ρ : ℝ) : ℕ → ValueFn :=
  fun m => (T_modified p ρ)^[m] (fun _ => 0)

theorem iterate_mem_cone (ρ : ℝ) (hρ : 0 < ρ) : ∀ m, InCone (iterate p ρ m) := by
  intro m
  induction m with
  | zero =>
    have h0 : iterate p ρ 0 = (fun _ => 0) := by
      simp only [iterate, Function.iterate_zero_apply]
    rw [h0]; exact zero_mem_cone
  | succ k ih =>
    have hstep : iterate p ρ (k + 1) = T_modified p ρ (iterate p ρ k) := by
      simp only [iterate, Function.iterate_succ_apply']
    rw [hstep]
    unfold T_modified
    exact cone_add c_mem_cone
      (cone_smul_nonneg hρ.le
        (P_preserves_cone p (Q (iterate p ρ k)) (Q_preserves_cone (iterate p ρ k) ih)))

theorem relaxed_eq_true (f : ValueFn) (hb : BoundaryComp f) :
    Q f = Q_true f := by
  funext s
  obtain ⟨x, y⟩ := s
  fin_cases y
  · -- y = 0
    rcases x with _ | _ | _ | k
    · show Q f (0, 0) = Q_true f (0, 0)
      simp only [Q, Q_modified, Q_true]
    · show Q f (1, 0) = Q_true f (1, 0)
      simp only [Q, Q_modified, Q_true]; exact min_eq_left hb.b1
    · show Q f (2, 0) = Q_true f (2, 0)
      simp only [Q, Q_modified, Q_true]; rw [min_eq_left hb.b2]
    · show Q f (k + 3, 0) = Q_true f (k + 3, 0)
      simp only [Q, Q_modified, Q_true]
  · -- y = 1
    rcases x with _ | _ | k
    · show Q f (0, 1) = Q_true f (0, 1)
      simp only [Q, Q_modified, Q_true]
    · show Q f (1, 1) = Q_true f (1, 1)
      simp only [Q, Q_modified, Q_true]; exact min_eq_left hb.b2
    · show Q f (k + 2, 1) = Q_true f (k + 2, 1)
      simp only [Q, Q_modified, Q_true]
  · -- y = 2
    simp only [Q, Q_modified, Q_true]

/-- Every iterate satisifes the boundary comparisons, proposition (1a). -/
theorem iterate_boundary (ρ : ℝ) (hρ : 0 < ρ) : ∀ m, BoundaryComp (iterate p ρ m) := by
  intro m
  cases m with
  | zero =>
    have h0 : iterate p ρ 0 = (fun _ => 0) := by
      simp only [iterate, Function.iterate_zero_apply]
    rw [h0]
    exact ⟨le_refl _, le_refl _⟩
  | succ k =>
    have hstep : iterate p ρ (k + 1) = T_modified p ρ (iterate p ρ k) := by
      simp only [iterate, Function.iterate_succ_apply']
    rw [hstep]
    exact boundary_dominance p ρ hρ (iterate p ρ k) (iterate_mem_cone p ρ hρ k)

theorem relaxed_eq_true_iterate (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ m, Q (iterate p ρ m) = Q_true (iterate p ρ m) := by
  intro m
  exact relaxed_eq_true (iterate p ρ m) (iterate_boundary p ρ hρ m)
