import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

open MeasureTheory

noncomputable section

namespace UpperHalfPlane

instance : MeasurableSpace ℍ := Subtype.instMeasurableSpace

instance : BorelSpace ℍ := Subtype.borelSpace _

lemma measurableEmbedding_coe : MeasurableEmbedding UpperHalfPlane.coe :=
  isOpenEmbedding_coe.measurableEmbedding

/-- The invariant measure on the upper half-plane, defined by `dx dy / y ^ 2`. -/
instance : MeasureSpace ℍ :=
  ⟨(volume.comap UpperHalfPlane.coe).withDensity fun z ↦ (1 / ⟨z.im, z.im_pos.le⟩ : NNReal) ^ 2⟩

/-- Express the volume of a measurable set as a lintegral over the corresponding subset of `ℂ`. -/
lemma volume_eq_lintegral {s : Set ℍ} (hs : MeasurableSet s) :
    volume s = ∫⁻ z : ℂ in (↑) '' s, (1 / ‖z.im‖₊) ^ 2 := by
  simp only [volume, one_div]
  -- This proof is annoying because `setLIntegral_subtype` only works on a literal subtype,
  -- while `UpperHalfPlane` is a _type alias_ for a subtype, so we need to do some annoying
  -- defeq abuse.
  rw [show UpperHalfPlane.coe = Subtype.val from rfl,
    ← setLIntegral_subtype (by exact isOpen_upperHalfPlaneSet.measurableSet),
    withDensity_apply _ hs]
  congr 1 with z
  rw [ENNReal.coe_inv (mod_cast NNReal.coe_ne_zero.mp z.im_pos.ne')]
  congr
  rw [Real.norm_of_nonneg (by simpa using z.im_pos.le), ← z.coe_im,
    show UpperHalfPlane.coe = Subtype.val from rfl]

instance : SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume := by
  refine ((smulInvariantMeasure_tfae _ _).out 2 0).mp fun g s hs ↦ ?_
  rw [volume_eq_lintegral hs, volume_eq_lintegral (hs.const_smul _)]

  have aux1a (x : ℂ) (hx : x ∈ UpperHalfPlane.coe '' s) :
        HasFDerivWithinAt (𝕜 := ℂ) (smulAux' g) (17) (UpperHalfPlane.coe '' s) x := by
      sorry

  have aux1b (x : ℂ) (hx : x ∈ UpperHalfPlane.coe '' s) :
      HasFDerivWithinAt (𝕜 := ℝ) (smulAux' g) (
        ContinuousLinearMap.restrictScalars ℝ (17 : ℂ →L[ℂ] ℂ)) (UpperHalfPlane.coe '' s) x :=
    (aux1a x hx).restrictScalars ℝ

  have aux2 : ((↑) '' s).InjOn (smulAux' g) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← UpperHalfPlane.ext_iff]
      change (↑(g • x) : ℂ) = ↑(g • y) → x = y
      simp only [ext_iff', smul_left_cancel_iff, imp_self]

  convert MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      volume (measurableEmbedding_coe.measurableSet_image.mpr hs)
      (fun a ha ↦ (aux1a a ha).restrictScalars ℝ) aux2
      (fun z ↦ (1 / ‖z.im‖₊) ^ 2)
  · have : smulAux' g ∘ ((↑) : ℍ → ℂ) = (↑) ∘ (fun x ↦ g • x) := by rfl
    rw [← Set.image_comp, this, Set.image_comp, Set.image_smul]
  · sorry


end UpperHalfPlane

end
