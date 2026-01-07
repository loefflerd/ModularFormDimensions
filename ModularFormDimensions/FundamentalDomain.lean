import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Measure

open MeasureTheory

section basic

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {s t : Set X} {μ : Measure X}

lemma hasNullFrontier_inter (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s ∩ t)) = 0 := by
  refine measure_mono_null (frontier_inter_subset s t) (measure_union_null ?_ ?_)
  · exact measure_mono_null Set.inter_subset_left hs
  · exact measure_mono_null Set.inter_subset_right ht

lemma hasNullFrontier_union (hs : μ (frontier s) = 0) (ht : μ (frontier t) = 0) :
    μ (frontier (s ∪ t)) = 0 := by
  refine measure_mono_null (frontier_union_subset s t) (measure_union_null ?_ ?_)
  · exact measure_mono_null Set.inter_subset_left hs
  · exact measure_mono_null Set.inter_subset_right ht

lemma hasNullFrontier_compl :
    μ (frontier sᶜ) = 0 ↔ μ (frontier sᶜ) = 0 := by
  rw [frontier_compl]

end basic

section fundDomain

private def openFundDomainSet : Set ℂ := {z | 0 < z.im ∧ 1 < ‖z‖ ∧ |z.re| < 1/2}

lemma isOpen_openFundDomainSet : IsOpen openFundDomainSet := by
  apply IsOpen.inter
  · exact UpperHalfPlane.isOpen_upperHalfPlaneSet
  · apply IsOpen.inter
    · exact isOpen_lt continuous_const continuous_norm
    · exact isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

private lemma hasNullFrontier_fundDomainSet : volume (frontier openFundDomainSet) = 0 := by
  apply hasNullFrontier_inter
  · exact (convex_halfSpace_im_gt 0).addHaar_frontier volume
  · apply hasNullFrontier_inter (s := {z | 1 < ‖z‖}) (t := {z : ℂ | |z.re| < 1/2})
    · rw [← frontier_compl]
      convert (convex_closedBall (0 : ℂ) 1).addHaar_frontier volume
      ext
      simp
    · simp only [abs_lt]
      apply hasNullFrontier_inter
      · exact (convex_halfSpace_re_gt _).addHaar_frontier _
      · exact (convex_halfSpace_re_lt _).addHaar_frontier _

end fundDomain
