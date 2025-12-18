/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

import ModularFormDimensions.MathlibPRs.MeromorphicOrder


open UpperHalfPlane Filter Topology

open scoped ModularForm

private lemma UpperHalfPlane.analyticAt_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    AnalyticAt ℂ (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) τ := by
  refine DifferentiableOn.analyticAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.property)
  -- surely the following must be proved in mathlib somewhere?
  suffices DifferentiableOn ℂ (num g / denom g) _ by
    refine this.congr fun z (hz : 0 < z.im) ↦ ?_
    simp_all [σ, coe_smul, ofComplex_apply_of_im_pos]
  unfold num denom
  exact .div (by fun_prop) (by fun_prop) fun _ hz ↦ denom_ne_zero_of_im g hz.ne'

private lemma UpperHalfPlane.deriv_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) τ = g.val.det / denom g τ ^ 2 := by
  have : (fun z ↦ ↑(g • ofComplex z)) =ᶠ[𝓝 ↑τ] (num g / denom g) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simp [coe_smul, ofComplex_apply_of_im_pos hz, σ, if_pos hg]
  rw [EventuallyEq.deriv_eq this,
    deriv_div (by unfold num; fun_prop) (by unfold denom; fun_prop) (denom_ne_zero g τ)]
  congr 1
  unfold num denom
  simp only [deriv_add_const, Matrix.det_fin_two]
  -- why does `rw` work here but `simp` does not?
  rw [deriv_const_mul_field, deriv_id'', deriv_const_mul_field, deriv_id'']
  push_cast
  ring

private lemma UpperHalfPlane.deriv_smul_ne_zero {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) τ ≠ 0 := by
  rw [deriv_smul hg]
  apply div_ne_zero
  · exact_mod_cast hg.ne'
  · exact pow_ne_zero _ (denom_ne_zero g τ)

private lemma order_comp_smul {f : ℍ → ℂ} {τ : ℍ} {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) :
    meromorphicOrderAt (fun z ↦ f (g • ofComplex z)) τ =
      meromorphicOrderAt (fun z ↦ f (ofComplex z)) ↑(g • τ) := by
  let G z : ℂ := ↑(g • ofComplex z)
  let F z := f (ofComplex z)
  have : (fun z : ℂ ↦ f (g • ofComplex z)) = F ∘ G := by ext; simp [F, G]
  rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero]
  · simp [F, G]
  · exact τ.analyticAt_smul hg
  · exact τ.deriv_smul_ne_zero hg

open scoped ModularForm in
private lemma order_slash {k : ℤ} {f : ℍ → ℂ} {τ : ℍ} {g : GL (Fin 2) ℝ}
    (hg : 0 < g.val.det) :
    meromorphicOrderAt (fun z : ℂ ↦ (f ∣[k] g) (ofComplex z)) ↑τ =
      meromorphicOrderAt (fun z ↦ f (ofComplex z)) ↑(g • τ) := by
  simp only [ModularForm.slash_def, σ, Matrix.GeneralLinearGroup.val_det_apply, hg, ↓reduceIte,
    RingHom.id_apply, zpow_neg, mul_assoc, ← order_comp_smul hg]
  rw [← Pi.mul_def, mul_comm, meromorphicOrderAt_mul_of_ne_zero]
  · refine .const_smul (.inv ?_ ?_)
    · refine .fun_zpow ?_ (denom_ne_zero g _)
      refine (analyticAt_id.congr ?_).const_smul.add analyticAt_const
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      simp [ofComplex_apply_of_im_pos hz]
    · exact zpow_ne_zero _ <| denom_ne_zero g _
  · apply mul_ne_zero
    · norm_cast
      positivity
    · rw [Ne, inv_eq_zero]
      exact zpow_ne_zero _ <| denom_ne_zero g _

variable (𝒢 : Subgroup (GL (Fin 2) ℝ))

/-- The quotient `𝒢 \ ℍ`, where `𝒢` is a subgroup of `GL(2, ℝ)`. -/
def OpenModularCurve : Type := MulAction.orbitRel.Quotient 𝒢 ℍ

local notation "Y(" 𝒢 ")" => OpenModularCurve 𝒢

/-- Order of vanishing of a meromorphic `SlashInvariantForm`.

TODO: Is this the morally right definition? Do we want to `weight` it by
the order of the stabilizer (at a cost of being `ℚ∞`-valued)? -/
noncomputable def meromorphicOrderQuotient {k : ℤ} (f : SlashInvariantForm 𝒢 k)
    [𝒢.HasDetOne] : Y(𝒢) → WithTop ℤ :=
  Quotient.lift (meromorphicOrderAt (f ∘ ofComplex) ·) (by
    rintro _ b ⟨⟨g, hg⟩, rfl⟩
    dsimp only [Subgroup.smul_def, Function.comp_def]
    rw [← order_slash, SlashInvariantFormClass.slash_action_eq f g hg]
    have := Units.val_eq_one.mpr <| Subgroup.HasDetOne.det_eq hg
    simp_all)

@[simp]
lemma meromorphicOrderQuotient_mk [𝒢.HasDetOne] {k : ℤ} (f : SlashInvariantForm 𝒢 k) (τ : ℍ) :
    meromorphicOrderQuotient 𝒢 f ⟦τ⟧ = meromorphicOrderAt (fun z ↦ f (ofComplex z)) ↑τ := by
  rfl

/-- The quotient `𝒢 \ ℍ⋆`, where `𝒢` is a subgroup of `GL(2, ℝ)` and `ℍ⋆` denotes the union of
`ℍ` and the cusps of `𝒢`. -/
def CompletedModularCurve : Type := (OpenModularCurve 𝒢) ⊕ CuspOrbits 𝒢
