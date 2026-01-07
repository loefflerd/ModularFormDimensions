import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Modular MatrixGroups Real

open UpperHalfPlane ModularGroup

noncomputable def ρ : ℍ := ⟨Complex.exp (2 * π * I / 3), by
  rw [Complex.exp_im]
  refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_mem_Ioo ?_)
  simp
  grind [Real.pi_pos]⟩

open Matrix Matrix.SpecialLinearGroup

variable {τ : ℍ} {g : SL(2, ℤ)}

instance {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R] [DecidableEq R] :
  DecidableEq (Matrix.SpecialLinearGroup n R) := Subtype.instDecidableEq

lemma smul_I_eq_iff : g • I = I ↔ g ∈ ({1, -1, S, -S} : Finset SL(2, ℤ)) where
  mp hg := by
    obtain ⟨hb, ha⟩ : g 0 1 = -g 1 0 ∧ g 0 0 = g 1 1 := by
      have := congr_arg UpperHalfPlane.coe hg
      rw [sl_moeb, coe_smul_of_det_pos (by simp), div_eq_iff (denom_ne_zero g I)] at this
      simp [num, denom, mul_add, mul_comm _ (Complex.I), ← mul_assoc, Complex.ext_iff] at this
      norm_cast at this
    have := g.det_coe
    rw [Matrix.det_fin_two, hb, ha, ← sq, neg_mul, ← sq, sub_neg_eq_add] at this
    have hd : g 1 1 ^ 2 ≤ 1 := by nlinarith
    have hc : g 1 0 ^ 2 ≤ 1 := by nlinarith
    rw [sq_le_one_iff_abs_le_one, Int.abs_le_one_iff] at hc hd
    -- do as much `simp` as possible before the `rcases` split
    simp only [S, Int.reduceNeg, Finset.mem_insert, SpecialLinearGroup.ext_iff,
      SpecialLinearGroup.coe_one, Fin.forall_fin_two, Fin.isValue, one_apply_eq, ne_eq, zero_ne_one,
      not_false_eq_true, one_apply_ne, one_ne_zero, coe_neg, neg_apply, neg_zero, of_apply,
      cons_val', cons_val_fin_one, cons_val_zero, cons_val_one, Finset.mem_singleton, neg_neg]
    rcases hc with hc | hc | hc <;> grind
  mpr := by
    simp only [Finset.mem_insert, Finset.mem_singleton, UpperHalfPlane.ext_iff, S]
    rintro (rfl | rfl | rfl | rfl) <;> simp [coe_smul, σ, num, denom]

/-- No element of `SL(2, ℤ)` except `±1` acts trivially on `ℍ`. -/
lemma forall_smul_eq_iff : (∀ τ : ℍ, g • τ = τ) ↔ g = 1 ∨ g = -1 where
  mp hg := by
    have hI := smul_I_eq_iff.mp (hg I)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hI
    rcases hI with (rfl | rfl | rfl | rfl) <;>
    [tauto; tauto; skip; skip] <;>
    · have : -1 / (2 * Complex.I) = 2 * Complex.I := by
        simpa [S, UpperHalfPlane.coe_smul, σ, num, denom]
          using congr_arg UpperHalfPlane.coe <| hg (.mk (2 * I) (by simp))
      rw [div_eq_iff (by simp)] at this
      contrapose! this
      simp [Ne, Complex.ext_iff]
      norm_num
  mpr := by rintro (rfl | rfl) <;> simp

/-- If `τ` is in the open fundamental domain, its stabilizer is `±1`. -/
lemma eq_one_or_neg_one_of_mem_fdo (hg : g • τ = τ) (hτ : τ ∈ 𝒟ᵒ) : g = 1 ∨ g = -1 := by
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hτ (hg ▸ hτ))
  have : n = 0 := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hτ ((hg ▸ hn τ) ▸ hτ)
  exact forall_smul_eq_iff.mp (by simpa [this] using hn)
