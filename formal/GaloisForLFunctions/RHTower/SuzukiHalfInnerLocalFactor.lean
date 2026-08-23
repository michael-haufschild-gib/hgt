import GaloisForLFunctions.RHTower.SuzukiHalfInnerHalfPlane
import GaloisForLFunctions.HTGeometry.EntireMultiplicityFactor
import GaloisForLFunctions.HTGeometry.DslopeLocalFactor
import Mathlib.Analysis.Calculus.DSlope

/-!
# Removing the zeros of `A/E` at Xi zeros

Suzuki's family `F_γ` divides the inner half `A/E` by `z - γ` at a zero `γ` of `A`.  Written
naively that quotient carries the wrong value at `γ` itself, so this module works with the
divided slope `dslope (A/E) γ`, which is the analytic continuation.

The engine is a local factorization: peeling `A = (z-γ)^m h` gives `E = (z-γ)^{m-1} P` with
`P(γ) = i m h(γ) ≠ 0`, hence `A/E = (z-γ) · (h/P)` on a whole neighbourhood of `γ` — below the
axis as well as above it.  That factorization is exactly the hypothesis of
`dslope_eventuallyEq_of_localFactor`, so the divided slope is differentiable at `γ`; away from
`γ` differentiability transfers from `A/E` itself.

Iterating once more removes a second zero, giving a function holomorphic on the whole closed
upper half-plane that agrees with `(A/E) / ((z-γ)(z-δ))` off the two points.
-/

open Complex Filter Topology
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-- **Local linear factorization of `A/E` at a zero of `A`.**  With `A = (z-γ)^m h` and
`E = (z-γ)^{m-1} P`, `P(γ) = i m h(γ) ≠ 0`, the quotient is `(z-γ)` times `h/P`. -/
theorem exists_localFactor_suzukiHalfInner {γ : ℂ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC γ = (m : ℕ∞)) :
    ∃ g : ℂ → ℂ, DifferentiableAt ℂ g γ ∧ g γ = -I / (m : ℂ) ∧
      (suzukiHalfInner =ᶠ[𝓝 γ] fun z => (z - γ) * g z) ∧
      ∀ᶠ z in 𝓝 γ, DifferentiableAt ℂ suzukiHalfInner z := by
  obtain ⟨h, hh, hhγ, hfac⟩ :=
    exists_entire_factor_of_analyticOrderAt_eq (fun z => XiC_analytic z (Set.mem_univ z)) γ m hord
  have hmC : ((m : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hfun : XiC = fun z => (z - γ) ^ m * h z := funext hfac
  have hderiv : ∀ z, HasDerivAt XiC
      ((m : ℂ) * (z - γ) ^ (m - 1) * h z + (z - γ) ^ m * deriv h z) z := by
    intro z
    rw [hfun]
    have h1 : HasDerivAt (fun w : ℂ => (w - γ) ^ m) ((m : ℂ) * (z - γ) ^ (m - 1)) z := by
      have hb : HasDerivAt (fun w : ℂ => w - γ) 1 z := (hasDerivAt_id z).sub_const γ
      simpa [Pi.pow_def] using hb.pow m
    exact h1.mul ((hh z).differentiableAt.hasDerivAt)
  have hderivEq : ∀ z, deriv XiC z
      = (m : ℂ) * (z - γ) ^ (m - 1) * h z + (z - γ) ^ m * deriv h z :=
    fun z => (hderiv z).deriv
  set P : ℂ → ℂ := fun z => (z - γ) * h z + I * ((m : ℂ) * h z + (z - γ) * deriv h z) with hP
  have hPγ : P γ = I * (m : ℂ) * h γ := by
    rw [hP]
    simp
    ring
  have hPne : P γ ≠ 0 := by
    rw [hPγ]
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hmC) hhγ
  have hEfac : ∀ z, xiHedenmalmDeBrangesE z = (z - γ) ^ (m - 1) * P z := by
    intro z
    rw [xiHedenmalmDeBrangesE, hfac z, hderivEq z, hP]
    have hpow : (z - γ) ^ m = (z - γ) ^ (m - 1) * (z - γ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    ring
  have hPan : AnalyticAt ℂ P γ := by
    have hd : AnalyticAt ℂ (deriv h) γ := (hh γ).deriv
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - γ) γ := (analyticAt_id).sub analyticAt_const
    exact (h1.mul (hh γ)).add (analyticAt_const.mul
      ((analyticAt_const.mul (hh γ)).add (h1.mul hd)))
  have hhdiff : Differentiable ℂ h := fun z => (hh z).differentiableAt
  have hdhdiff : Differentiable ℂ (deriv h) := fun z => ((hh z).deriv).differentiableAt
  have hPdiff : Differentiable ℂ P := by
    rw [hP]
    exact ((differentiable_id.sub_const γ).mul hhdiff).add
      ((differentiable_const I).mul (((differentiable_const ((m : ℂ))).mul hhdiff).add
        ((differentiable_id.sub_const γ).mul hdhdiff)))
  have hVopen : IsOpen {w : ℂ | P w ≠ 0} := isOpen_ne_fun hPdiff.continuous continuous_const
  have hVmem : γ ∈ {w : ℂ | P w ≠ 0} := hPne
  have hEqOnV : ∀ z ∈ {w : ℂ | P w ≠ 0}, suzukiHalfInner z = (z - γ) * (h z / P z) := by
    intro z hz
    rw [suzukiHalfInner, hfac z, hEfac z]
    rcases eq_or_ne z γ with rfl | hzγ
    · simp [zero_pow (show m ≠ 0 by omega)]
    · have hsub : (z - γ) ≠ 0 := sub_ne_zero.mpr hzγ
      have hpowne : (z - γ) ^ (m - 1) ≠ 0 := pow_ne_zero _ hsub
      have hpow : (z - γ) ^ m = (z - γ) ^ (m - 1) * (z - γ) := by
        rw [← pow_succ]
        congr 1
        omega
      have hPz : P z ≠ 0 := hz
      rw [hpow]
      field_simp
  refine ⟨fun z => h z / P z, (hh γ).differentiableAt.div hPan.differentiableAt hPne, ?_, ?_, ?_⟩
  · show h γ / P γ = -I / (m : ℂ)
    rw [hPγ]
    field_simp
    rw [Complex.I_sq]
    norm_num
  · filter_upwards [hVopen.mem_nhds hVmem] with z hz using hEqOnV z hz
  · filter_upwards [hVopen.mem_nhds hVmem] with z hzV
    have heq : suzukiHalfInner =ᶠ[𝓝 z] fun w => (w - γ) * (h w / P w) := by
      filter_upwards [hVopen.mem_nhds hzV] with w hw using hEqOnV w hw
    refine (Filter.EventuallyEq.differentiableAt_iff heq).mpr ?_
    exact ((differentiable_id.sub_const γ) z).mul ((hhdiff z).div (hPdiff z) hzV)

theorem exists_localFactor_suzukiHalfInner_of_XiC_zero {γ : ℂ} (hγ : XiC γ = 0) :
    ∃ g : ℂ → ℂ, DifferentiableAt ℂ g γ ∧
      (suzukiHalfInner =ᶠ[𝓝 γ] fun z => (z - γ) * g z) ∧
      ∀ᶠ z in 𝓝 γ, DifferentiableAt ℂ suzukiHalfInner z := by
  set m : ℕ := (analyticOrderAt XiC γ).toNat with hm
  have hord : analyticOrderAt XiC γ = (m : ℕ∞) := (ENat.coe_toNat (XiC_order_ne_top γ)).symm
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h
    · exfalso
      rw [h0] at hord
      exact ((XiC_analytic γ (Set.mem_univ γ)).analyticOrderAt_eq_zero.mp
        (by exact_mod_cast hord)) hγ
    · exact h
  obtain ⟨g, hg, _, hfac, hnbhd⟩ := exists_localFactor_suzukiHalfInner hmpos hord
  exact ⟨g, hg, hfac, hnbhd⟩

/-- `A/E` is holomorphic on a whole neighbourhood of any zero of `A` — below the axis as well
as above it. -/
theorem eventually_differentiableAt_suzukiHalfInner {γ : ℂ} (hγ : XiC γ = 0) :
    ∀ᶠ z in 𝓝 γ, DifferentiableAt ℂ suzukiHalfInner z :=
  (exists_localFactor_suzukiHalfInner_of_XiC_zero hγ).choose_spec.2.2

@[simp] theorem suzukiHalfInner_eq_zero_of_XiC_zero {γ : ℂ} (hγ : XiC γ = 0) :
    suzukiHalfInner γ = 0 := by
  rw [suzukiHalfInner, hγ, zero_div]

theorem dslope_suzukiHalfInner_apply {γ z : ℂ} (hγ : XiC γ = 0) (hz : z ≠ γ) :
    dslope suzukiHalfInner γ z = suzukiHalfInner z / (z - γ) := by
  rw [dslope_of_ne _ hz, slope_def_field, suzukiHalfInner_eq_zero_of_XiC_zero hγ, sub_zero]

theorem differentiableAt_dslope_suzukiHalfInner_of_rh (hRH : RiemannHypothesis) {γ : ℂ}
    (hγ : XiC γ = 0) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (dslope suzukiHalfInner γ) z := by
  rcases eq_or_ne z γ with rfl | hne
  · obtain ⟨g, hg, hfac, _⟩ := exists_localFactor_suzukiHalfInner_of_XiC_zero hγ
    exact GaloisForLFunctions.HTGeometry.differentiableAt_dslope_of_localFactor hg hfac
  · exact (differentiableAt_dslope_of_ne hne).mpr
      (differentiableAt_suzukiHalfInner_of_rh hRH hz)

theorem exists_localFactor_dslope_suzukiHalfInner {γ δ : ℂ} (hγ : XiC γ = 0) (hδ : XiC δ = 0)
    (hne : δ ≠ γ) :
    ∃ g : ℂ → ℂ, DifferentiableAt ℂ g δ ∧
      dslope suzukiHalfInner γ =ᶠ[𝓝 δ] fun z => (z - δ) * g z := by
  obtain ⟨gδ, hgδ, hfac, _⟩ := exists_localFactor_suzukiHalfInner_of_XiC_zero hδ
  refine ⟨fun z => gδ z / (z - γ),
    hgδ.div ((differentiableAt_id).sub_const γ) (sub_ne_zero.mpr hne), ?_⟩
  filter_upwards [hfac, eventually_ne_nhds hne] with z hz hzγ
  rw [dslope_suzukiHalfInner_apply hγ hzγ, hz, mul_comm ((z : ℂ) - δ) (gδ z)]
  rw [mul_div_assoc, mul_comm]
  ring

theorem differentiableAt_dslope2_suzukiHalfInner_of_rh (hRH : RiemannHypothesis) {γ δ : ℂ}
    (hγ : XiC γ = 0) (hδ : XiC δ = 0) (hne : δ ≠ γ) {z : ℂ} (hz : 0 ≤ z.im) :
    DifferentiableAt ℂ (dslope (dslope suzukiHalfInner γ) δ) z := by
  rcases eq_or_ne z δ with rfl | hzδ
  · obtain ⟨g, hg, hfac⟩ := exists_localFactor_dslope_suzukiHalfInner hγ hδ hne
    exact GaloisForLFunctions.HTGeometry.differentiableAt_dslope_of_localFactor hg hfac
  · exact (differentiableAt_dslope_of_ne hzδ).mpr
      (differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ hz)

theorem dslope2_suzukiHalfInner_apply {γ δ z : ℂ} (hγ : XiC γ = 0) (hδ : XiC δ = 0)
    (hne : δ ≠ γ) (hzγ : z ≠ γ) (hzδ : z ≠ δ) :
    dslope (dslope suzukiHalfInner γ) δ z = suzukiHalfInner z / ((z - γ) * (z - δ)) := by
  rw [dslope_of_ne _ hzδ, slope_def_field, dslope_suzukiHalfInner_apply hγ hzγ,
    dslope_suzukiHalfInner_apply hγ hne, suzukiHalfInner_eq_zero_of_XiC_zero hδ,
    zero_div, sub_zero, div_div]

end
end RHTower
