import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Mathlib PR #33000: analytic order of a composition
-/
open Filter Topology

@[simp]
protected lemma ENat.map_mul {R : Type*} [NonAssocSemiring R] [DecidableEq R] [CharZero R]
    (a b : ℕ∞) :
    (map Nat.cast (a * b) : WithTop R) = map Nat.cast a * map Nat.cast b :=
  map_mul ((Nat.castRingHom R : ℕ →*₀ R).ENatMap Nat.cast_injective) a b

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] {f : 𝕜 → E}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hf' : deriv f x ≠ 0) : analyticOrderAt (f · - f x) x = 1 := by
  generalize h : analyticOrderAt (f · - f x) x = r
  cases r with
  | top =>
    simp_rw [analyticOrderAt_eq_top, sub_eq_zero] at h
    refine (hf' ?_).elim
    rw [EventuallyEq.deriv_eq h, deriv_const]
  | coe r =>
    norm_cast
    obtain ⟨F, hFa, hFne, hfF⟩ := (analyticOrderAt_eq_natCast (by fun_prop)).mp h
    apply eq_of_ge_of_le
    · by_contra! hr
      have := hfF.self_of_nhds
      simp_all
    · contrapose! hf'
      simp_rw [sub_eq_iff_eq_add] at hfF
      rw [EventuallyEq.deriv_eq hfF, deriv_add_const, deriv_fun_smul (by fun_prop) (by fun_prop),
        deriv_fun_pow (by fun_prop), sub_self, zero_pow (by omega), zero_pow (by omega),
        mul_zero, zero_mul, zero_smul, zero_smul, add_zero]

section comp
/-!
## Vanishing order of a composition of functions
-/
variable {x : 𝕜} {f : 𝕜 → E} {g : 𝕜 → 𝕜}

lemma eventuallyConst_iff_analyticOrderAt_sub_eq_top :
    EventuallyConst f (𝓝 x) ↔ analyticOrderAt (f · - f x) x = ⊤ := by
  simpa [eventuallyConst_iff_exists_eventuallyEq, analyticOrderAt_eq_top, sub_eq_zero]
    using ⟨fun ⟨c, hc⟩ ↦ (show f x = c from hc.self_of_nhds) ▸ hc, fun h ↦ ⟨_, h⟩⟩

/-- If `g` is analytic at `x`, `f` is meromorphic at `g x`, and `g` is not locally constant near
`x`, the order of `f ∘ g` is the product of the orders of `f` and `g`. -/
lemma MeromorphicAt.meromorphicOrderAt_comp (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
    (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicOrderAt (f ∘ g) x =
      (meromorphicOrderAt f (g x)) * (analyticOrderAt (g · - g x) x).map Nat.cast := by
  -- First deal with the silly case that `f` is identically zero around `g x`.
  rcases eq_or_ne (meromorphicOrderAt f (g x)) ⊤ with hf' | hf'
  · rw [hf', WithTop.top_mul]
    · rw [meromorphicOrderAt_eq_top_iff] at hf' ⊢
      rw [Function.comp_def, ← eventually_map (P := fun x ↦ f x = 0)]
      exact EventuallyEq.filter_mono hf' (hg.map_nhdsNE hg_nc)
    · simp [(show AnalyticAt 𝕜 (g · - g x) x by fun_prop).analyticOrderAt_eq_zero]
  -- Now the interesting case. First unpack the data
  have hr := (WithTop.coe_untop₀_of_ne_top hf').symm
  rw [meromorphicOrderAt_ne_top_iff hf] at hf'
  set r := (meromorphicOrderAt f (g x)).untop₀
  rw [hr]
  -- Now write `F = (· - g x) ^ r • G` for `G` analytic and nonzero at `g x`
  obtain ⟨F, hFan, hFne, hFev⟩ := hf'
  have aux1 : f ∘ g =ᶠ[𝓝[≠] x] (g · - g x) ^ r • (F ∘ g) :=
    hFev.comp_tendsto (hg.map_nhdsNE hg_nc)
  have aux2 : meromorphicOrderAt (F ∘ g) x = 0 := by
    rw [AnalyticAt.meromorphicOrderAt_eq (by fun_prop),
      analyticOrderAt_eq_zero.mpr (by exact .inr hFne), ENat.map_zero, CharP.cast_eq_zero,
      WithTop.coe_zero]
  rw [meromorphicOrderAt_congr aux1,
    meromorphicOrderAt_smul ?_ (AnalyticAt.meromorphicAt <| ?_), aux2, add_zero,
    meromorphicOrderAt_zpow, AnalyticAt.meromorphicOrderAt_eq] <;>
  fun_prop

/-- Analytic order of a composition of analytic functions. -/
lemma AnalyticAt.analyticOrderAt_comp (hf : AnalyticAt 𝕜 f (g x)) (hg : AnalyticAt 𝕜 g x) :
    analyticOrderAt (f ∘ g) x = analyticOrderAt f (g x) * analyticOrderAt (g · - g x) x := by
  -- For most cases we can use the `meromorphicOrderAt` lemma, but this version is also true
  -- if `g` is locally constant (unlike the meromorphic version) so we must prove this case.
  by_cases hg_nc : EventuallyConst g (𝓝 x)
  · have := hg_nc.comp f
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hg_nc this
    rw [hg_nc]
    by_cases hf' : f (g x) = 0
    · simpa [hf', show analyticOrderAt f (g x) ≠ 0 by grind [analyticOrderAt_ne_zero]]
    · rw [show analyticOrderAt f (g x) = 0 from ?_, zero_mul] <;>
      grind [hf.comp hg, AnalyticAt.analyticOrderAt_eq_zero]
  simpa [hf.meromorphicOrderAt_eq, (hf.comp hg).meromorphicOrderAt_eq, ← ENat.map_mul]
    using hf.meromorphicAt.meromorphicOrderAt_comp hg hg_nc

/-- If `g` is analytic at `x`, `f` is meromorphic at `g x`, and `g' x ≠ 0`, then the order of
`f ∘ g` at `x` is the order of `f` at `g x`. -/
lemma MeromorphicAt.meromorphicOrderAt_comp_of_deriv_ne_zero
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
    meromorphicOrderAt (f ∘ g) x = meromorphicOrderAt f (g x) := by
  have hgo : analyticOrderAt _ x = 1 := hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
  rw [hf.meromorphicOrderAt_comp hg, hgo] <;>
  simp [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hgo]

/-- If `g` is analytic at `x`, `f` is meromorphic at `g x`, and `g' x ≠ 0`, then the order of
`f ∘ g` at `x` is the order of `f` at `g x`. -/
lemma AnalyticAt.analyticOrderAt_comp_of_deriv_ne_zero {g : 𝕜 → 𝕜}
    (hf : AnalyticAt 𝕜 f (g x)) (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
    analyticOrderAt (f ∘ g) x = analyticOrderAt f (g x) := by
  simp [hf.analyticOrderAt_comp hg, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg']

end comp
