import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import OneFastTwoSlow.Defs
import OneFastTwoSlow.AssignmentClosure
import OneFastTwoSlow.EventClosure
import OneFastTwoSlow.BoundaryDominance
import OneFastTwoSlow.RelaxedEqualsTrue
import OneFastTwoSlow.Basic

lemma step_boundary (ρ : ℝ) (hρ : 0 < ρ) (f : ValueFn) (hf : InCone f) :
    BoundaryComp (T_modified p ρ f) :=
  boundary_dominance p ρ hρ f hf

lemma step_assign (g : ValueFn) (hb : BoundaryComp g) :
    Q_modified g = Q_true g :=
  relaxed_eq_true g hb

lemma step_bellman (ρ : ℝ) (f : ValueFn) (hQ : Q_modified f = Q_true f) :
    T_modified p ρ f = T p ρ f := by
  unfold T_modified T; rw [hQ]

theorem value_consistency (ρ : ℝ) (hρ : 0 < ρ) (f : ValueFn) (hf : InCone f) :
    T_modified p ρ (T_modified p ρ f) = T p ρ (T_modified p ρ f) := by
  set g := T_modified p ρ f with hg
  have hb : BoundaryComp g := by rw [hg]; exact step_boundary ρ hρ f hf
  have hQ : Q_modified g = Q_true g := step_assign g hb
  exact step_bellman ρ g hQ
