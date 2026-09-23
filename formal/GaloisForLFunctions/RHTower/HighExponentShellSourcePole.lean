import GaloisForLFunctions.RHTower.HighExponentShellCriticalClock
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The pole structure of the high-exponent shell source

The analytic shell source `S_m(z) = ζ(z)·H_m(z)` has, for `m ≥ 12`, a simple pole at `z = 1` with
nonzero residue.  Writing `U_m(z) = G(z)·H_m(z)` with `G = (z-1)ζ(z)` the analytic zeta residue
unit, one has `S_m = U_m·(z-1)⁻¹` off the pole with `U_m` analytic at `1` and `U_m(1) = H_m(1) ≠ 0`.

Consequently the two normalised derivative ratios of the source converge:

* `RHTower.tendsto_shellSource_logDeriv` — `-(z-1)·S_m'/S_m → 1`;
* `RHTower.tendsto_shellSource_secondDeriv` — `(z-1)²·S_m''/S_m → 2`.

These are the first and second unit-rate exponential moments; they are the analytic input to the
critical clock variance of a high-exponent shell.
-/

noncomputable section

namespace RHTower

open Complex Filter
open scoped Topology

/-- The analytic shell source `S_m(z) = ζ(z)·H_m(z)`. -/
def shellSource (m : ℕ) (z : ℂ) : ℂ := riemannZeta z * shellMultiplier m z

/-- The analytic unit of the shell source at its pole: `(z-1)·S_m(z)` continued across `z = 1`. -/
def shellResidueUnit (m : ℕ) (z : ℂ) : ℂ := zetaResidueUnit z * shellMultiplier m z

@[simp] theorem shellResidueUnit_one (m : ℕ) : shellResidueUnit m 1 = shellMultiplier m 1 := by
  rw [shellResidueUnit, zetaResidueUnit_one, one_mul]

theorem analyticAt_shellResidueUnit {m : ℕ} (hm : 12 ≤ m) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (shellResidueUnit m) s :=
  (analyticAt_zetaResidueUnit s).mul (analyticAt_shellMultiplier hm hs)

theorem shellResidueUnit_one_ne_zero {m : ℕ} (hm : 2 ≤ m) : shellResidueUnit m 1 ≠ 0 := by
  rw [shellResidueUnit_one]
  intro h
  have hpos := shellResidue_pos hm
  rw [h] at hpos
  simp at hpos

/-- Off the pole the shell source factors through its analytic unit. -/
theorem shellSource_eq_of_ne_one {m : ℕ} {z : ℂ} (hz : z ≠ 1) :
    shellSource m z = shellResidueUnit m z * (z - 1)⁻¹ := by
  have h : zetaResidueUnit z = (z - 1) * riemannZeta z := by
    simp [zetaResidueUnit, Function.update_of_ne hz]
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hrearrange : (z - 1) * riemannZeta z * shellMultiplier m z * (z - 1)⁻¹
      = riemannZeta z * shellMultiplier m z * ((z - 1) * (z - 1)⁻¹) := by ring
  rw [shellSource, shellResidueUnit, h, hrearrange, mul_inv_cancel₀ hz1, mul_one]

/-- On the punctured plane the shell source agrees with the explicit factored model. -/
private theorem shellSource_eventuallyEq_model {m : ℕ} {s : ℂ} (hs : s ≠ 1) :
    shellSource m =ᶠ[𝓝 s] fun z => shellResidueUnit m z * (z - 1)⁻¹ := by
  filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1}ᶜ : Set ℂ) by simpa using hs)]
    with z hz
  exact shellSource_eq_of_ne_one (by simpa using hz)

/-! ## First and second derivative ratios -/

private theorem hasDerivAt_inv_sub_one {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun w : ℂ => (w - 1)⁻¹) (-((z - 1) ^ (2 : ℕ))⁻¹) z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hbase : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
  have h := hbase.inv hz1
  simpa only [Pi.inv_apply] using! h.congr_deriv (by
    simp only [div_eq_mul_inv, neg_one_mul])

private theorem hasDerivAt_neg_inv_sq_sub_one {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun w : ℂ => -((w - 1) ^ (2 : ℕ))⁻¹) (2 * ((z - 1) ^ (3 : ℕ))⁻¹) z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hbase : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
  have hsq : HasDerivAt (fun w : ℂ => (w - 1) ^ (2 : ℕ)) (2 * (z - 1) ^ (1 : ℕ) * 1) z := hbase.pow 2
  have hneg := (hsq.inv (pow_ne_zero 2 hz1)).neg
  simpa only [Pi.neg_apply, Pi.inv_apply] using! hneg.congr_deriv (by
    field_simp [hz1])

/-- The derivative of the shell source off its pole. -/
theorem deriv_shellSource {m : ℕ} (hm : 12 ≤ m) {z : ℂ} (hz : z ≠ 1) (hre : 1 / 2 < z.re) :
    deriv (shellSource m) z
      = deriv (shellResidueUnit m) z * (z - 1)⁻¹
        + shellResidueUnit m z * (-((z - 1) ^ (2 : ℕ))⁻¹) := by
  rw [(shellSource_eventuallyEq_model (m := m) hz).deriv_eq]
  exact ((analyticAt_shellResidueUnit hm hre).differentiableAt.hasDerivAt.mul
    (hasDerivAt_inv_sub_one hz)).deriv

/-- The shell source is nonzero in a punctured neighbourhood of the pole. -/
theorem shellSource_ne_zero_eventually {m : ℕ} (hm : 12 ≤ m) :
    ∀ᶠ z in 𝓝[≠] (1 : ℂ), shellSource m z ≠ 0 := by
  have hhalf : (1 : ℝ) / 2 < ((1 : ℂ)).re := by norm_num
  have hUne : ∀ᶠ z in 𝓝 (1 : ℂ), shellResidueUnit m z ≠ 0 :=
    (analyticAt_shellResidueUnit hm hhalf).continuousAt.eventually_ne
      (shellResidueUnit_one_ne_zero (by omega))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hUne] with z hz hU
  have hz1 : z ≠ 1 := by simpa using hz
  rw [shellSource_eq_of_ne_one hz1]
  exact mul_ne_zero hU (inv_ne_zero (sub_ne_zero.mpr hz1))

/-- **First critical moment of the shell source.**  `-(z-1)·S_m'/S_m → 1` as `z → 1`. -/
theorem tendsto_shellSource_logDeriv {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (fun z : ℂ => -((z - 1) * (deriv (shellSource m) z / shellSource m z)))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
  have hhalf : (1 : ℝ) / 2 < ((1 : ℂ)).re := by norm_num
  have hUana := analyticAt_shellResidueUnit hm hhalf
  have hU1 := shellResidueUnit_one_ne_zero (m := m) (by omega)
  have hUne : ∀ᶠ z in 𝓝 (1 : ℂ), shellResidueUnit m z ≠ 0 :=
    hUana.continuousAt.eventually_ne hU1
  have hre : ∀ᶠ z in 𝓝 (1 : ℂ), (1 : ℝ) / 2 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hhalf
  -- the model limit
  have hsub : Tendsto (fun z : ℂ => z - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => z - 1) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)) :=
      tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun z : ℂ => deriv (shellResidueUnit m) z / shellResidueUnit m z)
      (𝓝[≠] (1 : ℂ)) (𝓝 (deriv (shellResidueUnit m) 1 / shellResidueUnit m 1)) := by
    have h : ContinuousAt (fun z : ℂ => deriv (shellResidueUnit m) z / shellResidueUnit m z) 1 :=
      (hUana.deriv.continuousAt).div hUana.continuousAt hU1
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have hmodel : Tendsto (fun z : ℂ =>
      1 - (z - 1) * (deriv (shellResidueUnit m) z / shellResidueUnit m z))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℂ))
      (f := 𝓝[≠] (1 : ℂ))).sub (hsub.mul hlog)
    rw [zero_mul, sub_zero] at h
    exact h
  refine hmodel.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hUne, nhdsWithin_le_nhds hre]
    with z hz hU hzre
  have hz1 : z ≠ 1 := by simpa using hz
  have hz10 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [deriv_shellSource hm hz1 hzre, shellSource_eq_of_ne_one hz1]
  field_simp
  ring

/-- The second derivative of the shell source off its pole. -/
theorem deriv_deriv_shellSource {m : ℕ} (hm : 12 ≤ m) {z : ℂ} (hz : z ≠ 1) (hre : 1 / 2 < z.re) :
    deriv (deriv (shellSource m)) z
      = deriv (deriv (shellResidueUnit m)) z * (z - 1)⁻¹
        + 2 * deriv (shellResidueUnit m) z * (-((z - 1) ^ (2 : ℕ))⁻¹)
        + shellResidueUnit m z * (2 * ((z - 1) ^ (3 : ℕ))⁻¹) := by
  have hopen : ({1}ᶜ : Set ℂ) ∈ 𝓝 z :=
    isOpen_compl_singleton.mem_nhds (by simpa using hz)
  have hreOpen : {w : ℂ | (1 : ℝ) / 2 < w.re} ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre
  have hEq : deriv (shellSource m) =ᶠ[𝓝 z] fun w : ℂ =>
      deriv (shellResidueUnit m) w * (w - 1)⁻¹
        + shellResidueUnit m w * (-((w - 1) ^ (2 : ℕ))⁻¹) := by
    filter_upwards [hopen, hreOpen] with w hw hwre
    exact deriv_shellSource hm (by simpa using hw) hwre
  rw [hEq.deriv_eq]
  have hU := analyticAt_shellResidueUnit hm hre
  have hUderiv : AnalyticAt ℂ (deriv (shellResidueUnit m)) z := hU.deriv
  have h1 : HasDerivAt (fun w : ℂ => deriv (shellResidueUnit m) w * (w - 1)⁻¹)
      (deriv (deriv (shellResidueUnit m)) z * (z - 1)⁻¹
        + deriv (shellResidueUnit m) z * (-((z - 1) ^ (2 : ℕ))⁻¹)) z :=
    hUderiv.differentiableAt.hasDerivAt.mul (hasDerivAt_inv_sub_one hz)
  have h2 : HasDerivAt (fun w : ℂ => shellResidueUnit m w * (-((w - 1) ^ (2 : ℕ))⁻¹))
      (deriv (shellResidueUnit m) z * (-((z - 1) ^ (2 : ℕ))⁻¹)
        + shellResidueUnit m z * (2 * ((z - 1) ^ (3 : ℕ))⁻¹)) z :=
    hU.differentiableAt.hasDerivAt.mul (hasDerivAt_neg_inv_sq_sub_one hz)
  have h3 : HasDerivAt (fun w : ℂ =>
      deriv (shellResidueUnit m) w * (w - 1)⁻¹ + shellResidueUnit m w * (-((w - 1) ^ (2 : ℕ))⁻¹))
      ((deriv (deriv (shellResidueUnit m)) z * (z - 1)⁻¹
          + deriv (shellResidueUnit m) z * (-((z - 1) ^ (2 : ℕ))⁻¹))
        + (deriv (shellResidueUnit m) z * (-((z - 1) ^ (2 : ℕ))⁻¹)
          + shellResidueUnit m z * (2 * ((z - 1) ^ (3 : ℕ))⁻¹))) z := h1.add h2
  rw [h3.deriv]
  ring

/-- **Second critical moment of the shell source.**  `(z-1)²·S_m''/S_m → 2` as `z → 1`. -/
theorem tendsto_shellSource_secondDeriv {m : ℕ} (hm : 12 ≤ m) :
    Tendsto (fun z : ℂ => (z - 1) ^ (2 : ℕ) * (deriv (deriv (shellSource m)) z / shellSource m z))
      (𝓝[≠] (1 : ℂ)) (𝓝 2) := by
  have hhalf : (1 : ℝ) / 2 < ((1 : ℂ)).re := by norm_num
  have hUana := analyticAt_shellResidueUnit hm hhalf
  have hU1 := shellResidueUnit_one_ne_zero (m := m) (by omega)
  have hUne : ∀ᶠ z in 𝓝 (1 : ℂ), shellResidueUnit m z ≠ 0 :=
    hUana.continuousAt.eventually_ne hU1
  have hre : ∀ᶠ z in 𝓝 (1 : ℂ), (1 : ℝ) / 2 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hhalf
  have hsub : Tendsto (fun z : ℂ => z - 1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => z - 1) (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ) - 1)) :=
      tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hratio1 : Tendsto (fun z : ℂ => deriv (shellResidueUnit m) z / shellResidueUnit m z)
      (𝓝[≠] (1 : ℂ)) (𝓝 (deriv (shellResidueUnit m) 1 / shellResidueUnit m 1)) := by
    have h : ContinuousAt (fun z : ℂ => deriv (shellResidueUnit m) z / shellResidueUnit m z) 1 :=
      (hUana.deriv.continuousAt).div hUana.continuousAt hU1
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have hratio2 : Tendsto
      (fun z : ℂ => deriv (deriv (shellResidueUnit m)) z / shellResidueUnit m z)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (deriv (deriv (shellResidueUnit m)) 1 / shellResidueUnit m 1)) := by
    have h : ContinuousAt
        (fun z : ℂ => deriv (deriv (shellResidueUnit m)) z / shellResidueUnit m z) 1 :=
      (hUana.deriv.deriv.continuousAt).div hUana.continuousAt hU1
    exact h.tendsto.mono_left nhdsWithin_le_nhds
  have hmodel : Tendsto (fun z : ℂ =>
      (z - 1) ^ (2 : ℕ) * (deriv (deriv (shellResidueUnit m)) z / shellResidueUnit m z)
        - 2 * ((z - 1) * (deriv (shellResidueUnit m) z / shellResidueUnit m z)) + 2)
      (𝓝[≠] (1 : ℂ)) (𝓝 2) := by
    have hA : Tendsto (fun z : ℂ =>
        (z - 1) ^ (2 : ℕ) * (deriv (deriv (shellResidueUnit m)) z / shellResidueUnit m z))
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
      have h := (hsub.pow 2).mul hratio2
      rw [show (0 : ℂ) ^ (2 : ℕ) = 0 by ring, zero_mul] at h
      exact h
    have hB : Tendsto (fun z : ℂ =>
        2 * ((z - 1) * (deriv (shellResidueUnit m) z / shellResidueUnit m z)))
        (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
      have h := (hsub.mul hratio1).const_mul (2 : ℂ)
      rw [zero_mul, mul_zero] at h
      exact h
    have h := (hA.sub hB).add (tendsto_const_nhds (x := (2 : ℂ)) (f := 𝓝[≠] (1 : ℂ)))
    rw [sub_zero, zero_add] at h
    exact h
  refine hmodel.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hUne, nhdsWithin_le_nhds hre]
    with z hz hU hzre
  have hz1 : z ≠ 1 := by simpa using hz
  have hz10 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [deriv_deriv_shellSource hm hz1 hzre, shellSource_eq_of_ne_one hz1]
  field_simp
  ring

end RHTower
