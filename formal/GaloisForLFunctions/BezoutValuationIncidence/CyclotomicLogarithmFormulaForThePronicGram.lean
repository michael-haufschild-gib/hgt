import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.BezoutValuationIncidence.MeanCenteredPronicGramRecurrenceAndCenteringDiscrepancyBridge
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanQuadratic

/-!
# A cyclotomic-logarithm formula for the pronic Gram

On the primitive roots of order `q ≥ 2` the Ramanujan primitive is a pure exponential sum:

`R_q(M) = Σ_ζ a_ζ (ζ^M - 1)`,  `a_ζ = ζ/(ζ - 1)`,  and  `Σ_ζ a_ζ = φ(q)/2`

because `a_ζ + a_{ζ⁻¹} = 1`. Hence the mean-centered primitive `R_q(M) + φ(q)/2` is exactly
`Σ_ζ a_ζ ζ^M`, with no constant term.

The pronic weight sums against characters in closed form: for `|z| ≤ 1`, `z ≠ 0, 1`,

`Σ_{M ≥ 1} z^M / (M(M+1)) = 1 + Q(z)`,  `Q(z) = (1 - z) log(1 - z) / z`,

where `Q(1) = 0` matches the total pronic mass. Inside the disk this is the logarithmic series. On
the circle it follows by continuity, since the series converges uniformly on the closed disk.

**Theorem.** For `p, q ≥ 2` the mean-centered pronic Gram is a finite cyclotomic sum:

`G^{mc}(p, q) = φ(p) φ(q)/4 + Σ_{ζ prim p} Σ_{ξ prim q} a_ζ a_ξ Q(ζ ξ)`.

The infinite pronic series is replaced by values of `log(1 - η)` at the roots of unity
`η = ζξ` of order dividing `lcm(p, q)`. These are logarithms of cyclotomic numbers: real parts
`log |2 sin π x|`, imaginary parts sawtooth values. The uncentered and energy-centered Grams differ
from `G^{mc}` by the rank-one von Mangoldt terms.
-/

open Finset Filter Topology Complex GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The pronic character term `z^M/(M(M+1))`. -/
def pronicTerm (z : ℂ) (M : ℕ) : ℂ := z ^ M / ((M : ℂ) * ((M : ℂ) + 1))

/-- The cyclotomic logarithm kernel `Q(z) = (1 - z) log(1 - z)/z`, with `Q(1) = 0`. -/
def cyclotomicLogKernel (z : ℂ) : ℂ := if z = 1 then 0 else (1 - z) * log (1 - z) / z

/-! ## §1. The pronic generating function -/

theorem norm_pronicTerm_le {z : ℂ} (hz : ‖z‖ ≤ 1) (M : ℕ) :
    ‖pronicTerm z M‖ ≤ 1 / ((M : ℝ) * ((M : ℝ) + 1)) := by
  unfold pronicTerm
  have hc : ((M : ℂ) * ((M : ℂ) + 1)) = (((M : ℝ) * ((M : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
  rw [norm_div, norm_pow, hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hz) (by positivity)

theorem summable_pronicTerm {z : ℂ} (hz : ‖z‖ ≤ 1) : Summable (pronicTerm z) :=
  Summable.of_norm_bounded RHTower.hasSum_pm_reciprocal_weight.summable (norm_pronicTerm_le hz)

/-- Inside the unit disk the pronic series is the logarithmic series. -/
theorem hasSum_pronicTerm_of_norm_lt {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (pronicTerm z) (1 + cyclotomicLogKernel z) := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have h1 := Complex.hasSum_taylorSeries_neg_log hz
  have h2 : HasSum (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1)) (-log (1 - z)) := by
    have := (hasSum_nat_add_iff' 1).mpr h1
    simpa [Finset.sum_range_one] using this
  have h3 : HasSum (fun n : ℕ => z ^ n / ((n : ℂ) + 1)) (-log (1 - z) / z) := by
    have he : (fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) / z) =
        fun n : ℕ => z ^ n / ((n : ℂ) + 1) := by
      funext n
      rw [pow_succ]
      field_simp
    exact he ▸ h2.div_const z
  have hdecomp : pronicTerm z = fun M : ℕ =>
      (z ^ M / (M : ℂ) - z ^ M / ((M : ℂ) + 1)) + (if M = 0 then 1 else 0) := by
    funext M
    unfold pronicTerm
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
      have hM1 : (M : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
      rw [if_neg hM.ne']
      field_simp
      ring
  have hval : 1 + cyclotomicLogKernel z = (-log (1 - z) - -log (1 - z) / z) + 1 := by
    unfold cyclotomicLogKernel
    rw [if_neg hz1]
    field_simp
    ring
  rw [hdecomp, hval]
  exact (h1.sub h3).add (hasSum_ite_eq 0 (1 : ℂ))

theorem one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) : 1 - z ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [sub_re, one_re]
  by_contra hre
  have hle : z.re ≤ 1 := (re_le_norm z).trans hz
  have hre1 : z.re = 1 := by linarith
  have hsq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm z
    rw [normSq_apply] at h
    nlinarith [norm_nonneg z]
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact hz1 (Complex.ext (by simpa using hre1) (by simpa using him))

/-- **The pronic series on the closed disk.** For `|z| ≤ 1`, `z ≠ 0, 1`,
`Σ z^M/(M(M+1)) = 1 + (1 - z) log(1 - z)/z`. -/
theorem hasSum_pronicTerm {z : ℂ} (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    HasSum (pronicTerm z) (1 + cyclotomicLogKernel z) := by
  refine (summable_pronicTerm hz).hasSum_iff.mpr ?_
  have hcont : ContinuousOn (fun w => ∑' M, pronicTerm w M) (Metric.closedBall 0 1) :=
    continuousOn_tsum (fun M => by unfold pronicTerm; fun_prop)
      RHTower.hasSum_pm_reciprocal_weight.summable
      fun M w hw => norm_pronicTerm_le (by simpa using hw) M
  -- approach `z` radially from inside the disk
  set w : ℕ → ℂ := fun n => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) * z
  have hfac : ∀ n : ℕ, 0 < 1 - 1 / ((n : ℝ) + 2) ∧ 1 - 1 / ((n : ℝ) + 2) < 1 := fun n => by
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    constructor
    · rw [sub_pos, div_lt_one h2]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
  have hwn : ∀ n, ‖w n‖ = (1 - 1 / ((n : ℝ) + 2)) * ‖z‖ := fun n => by
    simp only [w, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hfac n).1]
  have hwlt : ∀ n, ‖w n‖ < 1 := fun n => by
    rw [hwn]
    calc (1 - 1 / ((n : ℝ) + 2)) * ‖z‖ ≤ (1 - 1 / ((n : ℝ) + 2)) * 1 :=
          mul_le_mul_of_nonneg_left hz (hfac n).1.le
      _ < 1 := by linarith [(hfac n).2]
  have hw0 : ∀ n, w n ≠ 0 := fun n => mul_ne_zero (by exact_mod_cast (hfac n).1.ne') hz0
  have hwlim : Tendsto w atTop (𝓝 z) := by
    have h : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
    have hc := (Complex.continuous_ofReal.tendsto 1).comp h
    simpa [w] using hc.mul_const z
  have hF : Tendsto (fun n => ∑' M, pronicTerm (w n) M) atTop (𝓝 (∑' M, pronicTerm z M)) :=
    (hcont z (by simpa using hz)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hwlim, Eventually.of_forall fun n => by
        simpa using (hwlt n).le⟩)
  -- the closed form is continuous at `z`
  have hG : ContinuousAt (fun u : ℂ => (1 - u) * log (1 - u) / u) z :=
    ((continuousAt_const.sub continuousAt_id).mul
      ((continuousAt_clog (one_sub_mem_slitPlane hz hz1)).comp
        (continuousAt_const.sub continuousAt_id))).div continuousAt_id hz0
  have hval : ∀ n, ∑' M, pronicTerm (w n) M = 1 + (1 - w n) * log (1 - w n) / w n := fun n => by
    have hw1 : w n ≠ 1 := by rintro h; have := hwlt n; rw [h] at this; simp at this
    rw [(hasSum_pronicTerm_of_norm_lt (hwlt n) (hw0 n)).tsum_eq, cyclotomicLogKernel, if_neg hw1]
  have hlim := tendsto_nhds_unique (hF.congr hval)
    ((tendsto_const_nhds (x := (1 : ℂ))).add (hG.tendsto.comp hwlim))
  rw [hlim, cyclotomicLogKernel, if_neg hz1]

/-- On the unit circle, including `z = 1` where the series is the total pronic mass. -/
theorem hasSum_pronicTerm_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    HasSum (pronicTerm z) (1 + cyclotomicLogKernel z) := by
  by_cases h1 : z = 1
  · subst h1
    rw [cyclotomicLogKernel, if_pos rfl, add_zero]
    have h := (Complex.hasSum_ofReal).mpr RHTower.hasSum_pm_reciprocal_weight
    convert h using 1
    · funext M
      simp [pronicTerm]
    · norm_num
  · exact hasSum_pronicTerm hz.le (by rintro rfl; simp at hz) h1

/-! ## §2. Spectral form of the Ramanujan primitive -/

theorem d4BMRamanujanNaturalCoefficient_eq_sum_primitiveRoots {n q : ℕ} (hn : 0 < n)
    (hq : 0 < q) :
    RHTower.d4BMRamanujanNaturalCoefficient n q = ∑ ζ ∈ primitiveRoots q ℂ, ζ ^ n := by
  rw [sum_primitiveRoots_pow n hq, RHTower.pm_ramanujan_eq_antidiagonal hn,
    ramanujanLagWeight_eq_sum_divisors,
    Nat.sum_divisorsAntidiagonal (f := fun a b =>
      (if a ∣ n then (a : ℂ) else 0) * (ArithmeticFunction.moebius b : ℂ))]
  push_cast
  refine sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem mul_sum_Icc_pow (ζ : ℂ) (M : ℕ) :
    (ζ - 1) * ∑ n ∈ Icc 1 M, ζ ^ n = ζ * (ζ ^ M - 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

/-- **The Ramanujan primitive on the primitive roots.** `R_q(M) = Σ_ζ ζ/(ζ - 1) (ζ^M - 1)`. -/
theorem pmRamanujanPrimitive_eq_spectral {q : ℕ} (hq : 2 ≤ q) (M : ℕ) :
    RHTower.pmRamanujanPrimitive q M =
      ∑ ζ ∈ primitiveRoots q ℂ, ζ / (ζ - 1) * (ζ ^ M - 1) := by
  unfold RHTower.pmRamanujanPrimitive
  rw [sum_congr rfl fun n hn => d4BMRamanujanNaturalCoefficient_eq_sum_primitiveRoots
    (mem_Icc.mp hn).1 (by omega : 0 < q), sum_comm]
  refine sum_congr rfl fun ζ hζ => ?_
  have hζ1 : ζ ≠ 1 := ((mem_primitiveRoots (by omega)).mp hζ).ne_one (by omega)
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have key := mul_sum_Icc_pow ζ M
  field_simp
  linear_combination key

/-- **Inversion pairing.** `Σ_{ζ prim q} ζ/(ζ - 1) = φ(q)/2`, since `a_ζ + a_{ζ⁻¹} = 1`. -/
theorem sum_primitiveRoots_div_sub_one {q : ℕ} (hq : 2 ≤ q) :
    ∑ ζ ∈ primitiveRoots q ℂ, ζ / (ζ - 1) = (q.totient : ℂ) / 2 := by
  have hq0 : 0 < q := by omega
  have hmem : ∀ ζ ∈ primitiveRoots q ℂ, ζ⁻¹ ∈ primitiveRoots q ℂ := fun ζ hζ =>
    (mem_primitiveRoots hq0).mpr ((mem_primitiveRoots hq0).mp hζ).inv
  have hinv : ∑ ζ ∈ primitiveRoots q ℂ, ζ / (ζ - 1) =
      ∑ ζ ∈ primitiveRoots q ℂ, ζ⁻¹ / (ζ⁻¹ - 1) :=
    sum_nbij' (·⁻¹) (·⁻¹) hmem hmem (fun ζ _ => inv_inv ζ) (fun ζ _ => inv_inv ζ)
      fun ζ _ => by rw [inv_inv]
  have hpair : ∀ ζ ∈ primitiveRoots q ℂ, ζ / (ζ - 1) + ζ⁻¹ / (ζ⁻¹ - 1) = 1 := by
    intro ζ hζ
    have hp := (mem_primitiveRoots hq0).mp hζ
    have h1 : ζ ≠ 1 := hp.ne_one (by omega)
    have h0 : ζ ≠ 0 := hp.ne_zero hq0.ne'
    have hs : ζ - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hs' : ζ⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (by rwa [Ne, inv_eq_one])
    field_simp
    ring
  have hcard : ((primitiveRoots q ℂ).card : ℂ) = q.totient := by
    rw [(Complex.isPrimitiveRoot_exp q hq0.ne').card_primitiveRoots]
  have h2 : 2 * ∑ ζ ∈ primitiveRoots q ℂ, ζ / (ζ - 1) = q.totient := by
    rw [two_mul]
    nth_rewrite 2 [hinv]
    rw [← sum_add_distrib, sum_congr rfl hpair, sum_const, nsmul_eq_mul, mul_one, hcard]
  linear_combination h2 / 2

/-- **The mean-centered primitive is a pure exponential sum.** -/
theorem pmRamanujanMeanCenteredPrimitive_eq_spectral {q : ℕ} (hq : 2 ≤ q) (M : ℕ) :
    (RHTower.pmRamanujanMeanCenteredPrimitive q M : ℂ) =
      ∑ ζ ∈ primitiveRoots q ℂ, ζ / (ζ - 1) * ζ ^ M := by
  have hre : ((RHTower.pmRamanujanPrimitive q M).re : ℂ) = RHTower.pmRamanujanPrimitive q M :=
    Complex.ext (by simp) (by simp [RHTower.pmRamanujanPrimitive_im])
  unfold RHTower.pmRamanujanMeanCenteredPrimitive
  push_cast
  rw [hre, pmRamanujanPrimitive_eq_spectral hq, ← sum_primitiveRoots_div_sub_one hq,
    ← sum_add_distrib]
  exact sum_congr rfl fun ζ _ => by ring

/-! ## §3. The Gram -/

/-- **Cyclotomic-logarithm formula for the mean-centered pronic Gram.** -/
theorem pmRamanujanMeanCenteredGram_eq_cyclotomicLog {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (RHTower.pmRamanujanMeanCenteredGram p q : ℂ) =
      (p.totient : ℂ) * q.totient / 4 + ∑ ζ ∈ primitiveRoots p ℂ, ∑ ξ ∈ primitiveRoots q ℂ,
        ζ / (ζ - 1) * (ξ / (ξ - 1)) * cyclotomicLogKernel (ζ * ξ) := by
  set t : ℕ → ℝ := fun N => RHTower.pmRamanujanMeanCenteredPrimitive p N *
    RHTower.pmRamanujanMeanCenteredPrimitive q N / ((N : ℝ) * ((N : ℝ) + 1))
  set V : ℂ := ∑ ζ ∈ primitiveRoots p ℂ, ∑ ξ ∈ primitiveRoots q ℂ,
    ζ / (ζ - 1) * (ξ / (ξ - 1)) * (1 + cyclotomicLogKernel (ζ * ξ))
  have hnorm : ∀ {r : ℕ}, 2 ≤ r → ∀ ζ ∈ primitiveRoots r ℂ, ‖ζ‖ = 1 := fun hr ζ hζ =>
    Complex.norm_eq_one_of_pow_eq_one ((mem_primitiveRoots (by omega)).mp hζ).pow_eq_one
      (by omega)
  -- the complex terms are a finite combination of pronic character series
  have hterm : ∀ N : ℕ, ((t N : ℝ) : ℂ) = ∑ ζ ∈ primitiveRoots p ℂ, ∑ ξ ∈ primitiveRoots q ℂ,
      ζ / (ζ - 1) * (ξ / (ξ - 1)) * pronicTerm (ζ * ξ) N := by
    intro N
    simp only [t]
    push_cast
    rw [pmRamanujanMeanCenteredPrimitive_eq_spectral hp, pmRamanujanMeanCenteredPrimitive_eq_spectral hq,
      sum_mul_sum, sum_div]
    refine sum_congr rfl fun ζ _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun ξ _ => ?_
    unfold pronicTerm
    rw [mul_pow]
    ring
  have hV : HasSum (fun N => ((t N : ℝ) : ℂ)) V := by
    simp only [hterm]
    refine hasSum_sum fun ζ hζ => hasSum_sum fun ξ hξ => ?_
    refine (hasSum_pronicTerm_of_norm_eq_one ?_).mul_left _
    rw [norm_mul, hnorm hp ζ hζ, hnorm hq ξ hξ, one_mul]
  have hVim : V.im = 0 := by
    have h := (Complex.imCLM.hasSum hV)
    simp only [Complex.imCLM_apply, Complex.ofReal_im] at h
    exact h.unique hasSum_zero
  have hG : RHTower.pmRamanujanMeanCenteredGram p q = V.re := by
    have h := (Complex.reCLM.hasSum hV)
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h
    exact h.tsum_eq
  rw [show (RHTower.pmRamanujanMeanCenteredGram p q : ℂ) = V from
    Complex.ext (by simp [hG]) (by simp [hVim])]
  simp only [V, mul_add, mul_one, sum_add_distrib, ← sum_mul_sum,
    sum_primitiveRoots_div_sub_one hp, sum_primitiveRoots_div_sub_one hq]
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
