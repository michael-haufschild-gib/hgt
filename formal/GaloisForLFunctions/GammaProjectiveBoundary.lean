import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.MeromorphicPoleOrbitBoundary
import GaloisForLFunctions.OrbitBalanceAdditive
import GaloisForLFunctions.RHTower.DigammaAsymptotic
import GaloisForLFunctions.RHTower.TrigammaVertical
import GaloisForLFunctions.RHTower.WindingAmplitude

open Filter Finset

namespace GaloisForLFunctions

/-!
# Gamma projective-boundary infrastructure

This file starts the unconditional formalization of the Gamma projective-boundary theorem.
It records two load-bearing pieces without replacing the analytic theorem by an assumption:

* the order-two pole datum in the differentiated digamma shift equation has nonzero orbit mass,
  hence cannot be a finite shift coboundary;
* a finite relation whose normalized coefficients and jet monomials converge has the corresponding
  constant-coefficient limiting relation.

The remaining card work is the actual Gamma-field valuation and the holomorphic Bohr recurrence
theory needed to instantiate the second theorem.
-/

noncomputable section

/-- The order-two principal-part datum of
`ψ'(s + 1) - ψ'(s) = -1 / s²` on the integer translation orbit of `0`.

The coefficient is `-1` at the unique pole and zero elsewhere. -/
def digammaShiftDerivativePoleDatum : ℤ →₀ ℂ :=
  Finsupp.single 0 (-1)

/-- The differentiated digamma shift has nonzero total order-two pole mass. -/
@[simp]
theorem additiveOrbitSum_digammaShiftDerivativePoleDatum :
    additiveOrbitSum digammaShiftDerivativePoleDatum = -1 := by
  unfold digammaShiftDerivativePoleDatum
  exact additiveOrbitSum_single 0 (-1)

/-- The differentiated digamma shift datum is not the finite coboundary of any order-two
principal-part datum.  This is the orbit-mass obstruction behind the non-rationality step in the
Gamma projective-boundary proof. -/
theorem digammaShiftDerivativePoleDatum_ne_shiftCoboundary
    (E : ℤ →₀ ℂ) :
    digammaShiftDerivativePoleDatum ≠ additiveIntShiftCoboundary E := by
  exact single_ne_additiveIntShiftCoboundary 0 (by norm_num) E

/-- There is no meromorphic solution with finite pole support on the integer orbit to the
differentiated digamma shift equation
`g(z + 1) - g(z) = -1 / z²`.

Every rational function satisfies the two meromorphicity and finite-pole hypotheses, so this is
the analytic pole-orbit obstruction used to exclude the rational branch in the Gamma
projective-boundary proof. -/
theorem no_finitePole_solution_digammaShiftDerivative
    (g : ℂ → ℂ)
    (hg : ∀ n : ℤ, MeromorphicAt g (additiveOrbitPoint 0 1 n))
    (hfinite : (poleIndexSet g 0 1).Finite)
    (hshift : ∀ z : ℂ, -(z ^ 2)⁻¹ = g (z + 1) - g z) : False := by
  apply shiftCoboundary_not_singleton_poleOrbit g (fun z : ℂ => -(z ^ 2)⁻¹) 0 1 hg hshift
    hfinite
  · rw [← meromorphicOrderAt_fun_neg (f := (fun z : ℂ => (z ^ 2)⁻¹))]
    change meromorphicOrderAt ((fun z : ℂ => z ^ 2)⁻¹) 0 < 0
    rw [meromorphicOrderAt_inv]
    have hpow : meromorphicOrderAt (fun z : ℂ => z ^ 2) 0 = 2 := by
      simpa only [sub_zero] using
        (meromorphicOrderAt_pow_id_sub_const (𝕜 := ℂ) (x := 0) (n := 2))
    rw [hpow]
    change (-(2 : WithTop ℤ)) < 0
    have hneg : ((-2 : ℤ) : WithTop ℤ) < (0 : ℤ) :=
      WithTop.coe_lt_coe.mpr (by norm_num)
    simpa using hneg
  · intro n hn
    by_contra hn0
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hana : AnalyticAt ℂ (fun z : ℂ => -(z ^ 2)⁻¹) (n : ℂ) := by
      exact ((analyticAt_id.pow 2).inv (pow_ne_zero 2 hnC)).neg
    have hval : -(((n : ℂ) ^ 2)⁻¹) ≠ 0 := by
      simp [hnC]
    have horder : meromorphicOrderAt (fun z : ℂ => -(z ^ 2)⁻¹) (n : ℂ) = 0 := by
      rw [hana.meromorphicOrderAt_eq]
      rw [hana.analyticOrderAt_eq_zero.mpr hval]
      simp
    rw [show additiveOrbitPoint 0 1 n = (n : ℂ) by simp [additiveOrbitPoint], horder] at hn
    exact (not_lt_of_ge (le_refl 0)) hn

/-- The real part of digamma tends to `+∞` on every upper vertical line in the closed right
half-plane.  This is the first asymptotic boundary coordinate of the Gamma field. -/
theorem re_digamma_vertical_tendsto_atTop {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re) atTop atTop := by
  have h1 : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (nhds 0) := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    simpa [one_div, inv_pow] using hinv.pow 2
  have h2 : Tendsto (fun t : ℝ => Real.pi / (2 * t)) atTop (nhds 0) := by
    have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    convert hinv.const_mul (Real.pi / 2) using 1
    · funext t
      ring
    · simp
  have herr : Tendsto (fun t : ℝ => 1 / t ^ 2 + Real.pi / (2 * t))
      atTop (nhds 0) := by simpa using h1.add h2
  have hlower : Tendsto
      (fun t : ℝ => Real.log t - (1 / t ^ 2 + Real.pi / (2 * t))) atTop atTop := by
    convert herr.neg.add_atTop Real.tendsto_log_atTop using 1
    funext t
    ring
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact RHTower.re_digamma_ge hσ ht

/-- The reciprocal digamma coordinate tends to zero on every upper vertical line in the closed
right half-plane. -/
theorem inv_digamma_vertical_tendsto_zero {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹) atTop (nhds 0) := by
  have hre := re_digamma_vertical_tendsto_atTop hσ
  have hnorm : Tendsto (fun t : ℝ =>
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hre
    exact Filter.Eventually.of_forall (fun _ => Complex.re_le_norm _)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_inv] using hnorm.inv_tendsto_atTop

/-- A fixed constant for the logarithmic upper bound on vertical digamma growth. -/
def digammaVerticalLogConstant : ℝ := 2 + 2 * Real.pi + Real.log 2

/-- Digamma has at most logarithmic norm growth on every upper vertical line in the open right
half-plane.  The real-part asymptotic and imaginary-part bound are both unconditional. -/
theorem norm_digamma_vertical_le_log {σ t : ℝ}
    (hσ : 0 < σ) (ht1 : 1 ≤ t) (hσt : σ ≤ t) :
    ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log t + digammaVerticalLogConstant := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  let ψ := Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
  let L : ℝ := (1 / 2) * Real.log (σ ^ 2 + t ^ 2)
  let E : ℝ := 1 / t ^ 2 + Real.pi / (2 * t)
  have hre := RHTower.re_digamma_vertical_bound_uncond hσ.le ht
  have him := RHTower.im_digamma_vertical_bound hσ.le ht
  have ht_inv : 1 / t ≤ 1 := by
    exact (div_le_one ht).2 ht1
  have ht_sq : 1 ≤ t ^ 2 := one_le_pow₀ ht1
  have hE : E ≤ 1 + Real.pi := by
    dsimp [E]
    have h1 : 1 / t ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos ht)).2 ht_sq
    have h2 : Real.pi / (2 * t) ≤ Real.pi := by
      apply (div_le_iff₀ (mul_pos (by norm_num) ht)).2
      nlinarith [Real.pi_pos]
    linarith
  have hbase : 1 ≤ σ ^ 2 + t ^ 2 := by nlinarith [sq_nonneg σ, ht_sq]
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (by norm_num) (Real.log_nonneg hbase)
  have hquad : σ ^ 2 + t ^ 2 ≤ 2 * t ^ 2 := by nlinarith
  have hlogquad : Real.log (σ ^ 2 + t ^ 2) ≤ Real.log 2 + 2 * Real.log t := by
    calc
      Real.log (σ ^ 2 + t ^ 2) ≤ Real.log (2 * t ^ 2) :=
        Real.log_le_log (by positivity) hquad
      _ = Real.log 2 + 2 * Real.log t := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 ht.ne'), Real.log_pow]
        norm_num
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : L ≤ Real.log t + Real.log 2 := by
    dsimp [L]
    nlinarith [Real.log_nonneg ht1, hlog2]
  have hreabs : |ψ.re| ≤ L + E := by
    have hdiff : |ψ.re - L| ≤ E := by simpa [ψ, L, E] using hre
    calc
      |ψ.re| = |(ψ.re - L) + L| := by congr 1; ring
      _ ≤ |ψ.re - L| + |L| := abs_add_le _ _
      _ ≤ E + L := by rw [abs_of_nonneg hL0]; linarith
      _ = L + E := by ring
  have himabs : |ψ.im| ≤ 1 + Real.pi := by
    rw [abs_of_nonneg him.1]
    linarith [him.2, Real.pi_pos]
  calc
    ‖ψ‖ ≤ |ψ.re| + |ψ.im| := Complex.norm_le_abs_re_add_abs_im ψ
    _ ≤ (L + E) + (1 + Real.pi) := add_le_add hreabs himabs
    _ ≤ Real.log t + digammaVerticalLogConstant := by
      dsimp [digammaVerticalLogConstant]
      linarith

/-- Every fixed power of a shifted logarithm is negligible compared with the vertical height. -/
theorem tendsto_log_add_const_pow_div (C : ℝ) (k : ℕ) :
    Tendsto (fun t : ℝ => (Real.log t + C) ^ k / t) atTop (nhds 0) := by
  have hi : ∀ i ∈ Finset.range (k + 1), Tendsto
      (fun t : ℝ => (k.choose i * C ^ (k - i)) * Real.log t ^ i / t)
      atTop (nhds 0) := by
    intro i hi
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 i one_ne_zero
    have hc := h.const_mul (k.choose i * C ^ (k - i))
    convert hc using 1
    · funext t
      ring
    · simp
  have hsum := tendsto_finsetSum (Finset.range (k + 1)) hi
  have hsum0 : Tendsto
      (fun t : ℝ => ∑ i ∈ Finset.range (k + 1),
        (k.choose i * C ^ (k - i)) * Real.log t ^ i / t) atTop (nhds 0) := by
    simpa using hsum
  apply hsum0.congr'
  filter_upwards [] with t
  rw [← Finset.sum_div, add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every fixed logarithmic power kills the universal vertical polygamma error. -/
theorem tendsto_log_add_const_pow_mul_verticalError (C : ℝ) (k : ℕ) :
    Tendsto (fun t : ℝ => (Real.log t + C) ^ k *
      (1 / t ^ 2 + Real.pi / (2 * t))) atTop (nhds 0) := by
  have h := tendsto_log_add_const_pow_div C k
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have h1 := h.mul hinv
  have h2 := h.const_mul (Real.pi / 2)
  have hsum := h1.add h2
  convert hsum using 1
  · funext t
    field_simp
  · simp

/-- The two-coordinate Gamma jet has the projective upper-vertical boundary `[0 : 1]`:
`Γ(σ+it) / Γ'(σ+it) → 0` for every `σ > 0`.

The proof is unconditional: the logarithmic derivative is digamma, its real part tends to
`+∞`, and Gamma has no zeros in the right half-plane. -/
theorem Gamma_div_deriv_vertical_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
      Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
  have hinv := inv_digamma_vertical_tendsto_zero hσ.le
  have hre := re_digamma_vertical_tendsto_atTop hσ.le
  apply hinv.congr'
  filter_upwards [hre.eventually_gt_atTop 0] with t ht
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hzre : z.re = σ := by simp [z]
  have hpsi : Complex.digamma z ≠ 0 := by
    intro hzero
    rw [hzero] at ht
    simp at ht
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa [hzre])
  have hd : deriv Complex.Gamma z ≠ 0 := by
    intro hzero
    apply hpsi
    rw [Complex.digamma_def, logDeriv_apply, hzero, zero_div]
  change (Complex.digamma z)⁻¹ = Complex.Gamma z / deriv Complex.Gamma z
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp

/-- Trigamma tends to zero on every upper vertical line in the open right half-plane. -/
theorem deriv_digamma_vertical_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
      deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact RHTower.norm_deriv_digamma_vertical_le hσ ht
  · have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have h1 : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (nhds 0) := by
      simpa [one_div, inv_pow] using hinv.pow 2
    have h2 : Tendsto (fun t : ℝ => Real.pi / (2 * t)) atTop (nhds 0) := by
      convert hinv.const_mul (Real.pi / 2) using 1
      · funext t
        ring
      · simp
    simpa using h1.add h2

/-- Every positive-order polygamma tends to zero after large positive translation:
`ψ⁽ᵐ⁺¹⁾(z+N) → 0` as `N → ∞`.

The proof applies the all-orders Cauchy estimate on a fixed radius-`1/2` disk to the existing
uniform `O(1/N)` digamma shift bound.  It upgrades the previously available trigamma-only
far-field theorem to every derivative order. -/
theorem iteratedDeriv_digamma_add_nat_tendsto (m : ℕ) (z : ℂ) :
    Tendsto (fun N : ℕ => iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ)))
      atTop (nhds 0) := by
  set K : ℝ := ‖z - 1‖ + 1 / 2 with hK_def
  have hK0 : 0 < K := by
    rw [hK_def]
    positivity
  let B : ℝ := (m + 1).factorial * (2 * K) / (1 / 2 : ℝ) ^ (m + 1)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat B)
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * K),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (-z.re + 1)]
    with N hN1 hthr hre
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hclosed_re : ∀ ζ ∈ Metric.closedBall (z + (N : ℂ)) (1 / 2), 0 < ζ.re := by
    intro ζ hζ
    have hd : ‖ζ - (z + (N : ℂ))‖ ≤ 1 / 2 := by
      rw [← dist_eq_norm]
      exact hζ
    have h1 := abs_le.mp (le_trans (Complex.abs_re_le_norm (ζ - (z + (N : ℂ)))) hd)
    have h2 : (ζ - (z + (N : ℂ))).re = ζ.re - (z.re + N) := by
      simp [Complex.sub_re, Complex.add_re]
    rw [h2] at h1
    linarith [h1.1]
  have hsup : ∀ ζ ∈ Metric.closedBall (z + (N : ℂ)) (1 / 2),
      ‖Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1)‖ ≤ 2 * K / N := by
    intro ζ hζ
    have hd : ‖ζ - (z + (N : ℂ))‖ ≤ 1 / 2 := by
      rw [← dist_eq_norm]
      exact hζ
    have hwz : ‖(ζ - (N : ℂ)) - z‖ ≤ 1 / 2 := by
      rw [show (ζ - (N : ℂ)) - z = ζ - (z + (N : ℂ)) from by ring]
      exact hd
    have hw1 : ‖(ζ - (N : ℂ)) - 1‖ ≤ K := by
      rw [hK_def]
      calc ‖(ζ - (N : ℂ)) - 1‖ = ‖((ζ - (N : ℂ)) - z) + (z - 1)‖ := by ring_nf
        _ ≤ ‖(ζ - (N : ℂ)) - z‖ + ‖z - 1‖ := norm_add_le _ _
        _ ≤ ‖z - 1‖ + 1 / 2 := by linarith
    have hwre : 0 < ((ζ - (N : ℂ)) + (N : ℂ)).re := by
      rw [sub_add_cancel]
      exact hclosed_re ζ hζ
    have hthr' : 2 * ‖(ζ - (N : ℂ)) - 1‖ ≤ (N : ℝ) := by linarith
    have happ := RHTower.digamma_shift_diff_bound hN1 hwre hthr'
    rw [sub_add_cancel] at happ
    exact le_trans happ (div_le_div₀ (by linarith) (by linarith) hN0 le_rfl)
  have hdiff : DifferentiableOn ℂ
      (fun ζ => Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1))
      {ζ : ℂ | 0 < ζ.re} := fun ζ hζ =>
    ((RHTower.digamma_analyticOnNhd_re_pos ζ hζ).differentiableAt.sub_const
      _).differentiableWithinAt
  have hsubset : Metric.closedBall (z + (N : ℂ)) (1 / 2) ⊆ {ζ : ℂ | 0 < ζ.re} :=
    fun ζ hζ => hclosed_re ζ hζ
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (m + 1) (show (0 : ℝ) < 1 / 2 by norm_num) (hdiff.diffContOnCl_ball hsubset)
    (fun ζ hζ => hsup ζ (Metric.sphere_subset_closedBall hζ))
  rw [show (fun ζ => Complex.digamma ζ - Complex.digamma ((N : ℂ) + 1)) =
      (fun ζ => -Complex.digamma ((N : ℂ) + 1) + Complex.digamma ζ) by
        funext ζ
        ring,
    iteratedDeriv_const_add (Nat.succ_pos m)] at hcauchy
  calc
    ‖iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ))‖
        ≤ (m + 1).factorial * (2 * K / N) / (1 / 2 : ℝ) ^ (m + 1) := hcauchy
    _ = B / N := by
      dsimp [B]
      field_simp

/-- Iterating the general polygamma recurrence over a positive integer shift. -/
theorem polygamma_apply_add_nat (r N : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv r Complex.digamma (z + (N : ℂ)) =
      iteratedDeriv r Complex.digamma z +
        (-1 : ℂ) ^ r * r.factorial *
          ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (r + 1))⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hzN : 0 < (z + (N : ℂ)).re := by simp; positivity
      have hpoles : ∀ p : ℕ, z + (N : ℂ) ≠ -(p : ℂ) := by
        intro p heq
        have hre := congrArg Complex.re heq
        simp at hre
        linarith [Nat.cast_nonneg (α := ℝ) p]
      have hrec := polygamma_recurrence r (z + (N : ℂ)) hpoles
      rw [show (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma by
        funext w
        rw [Complex.digamma_def, logDeriv_apply]] at hrec
      rw [show z + (↑(N + 1) : ℂ) = (z + (N : ℂ)) + 1 by push_cast; ring]
      rw [sub_eq_iff_eq_add] at hrec
      rw [hrec, ih, Finset.sum_range_succ]
      rw [div_eq_mul_inv]
      ring

/-- Uniform finite-sum bound for every positive-order polygamma kernel on an upper vertical line.
For height at least one, every exponent `m+2` is dominated by the already-established quadratic
kernel. -/
theorem norm_polygammaKernel_sum_le (m N : ℕ) {σ t : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    ‖∑ n ∈ Finset.range N,
        ((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)‖ ≤
      1 / t ^ 2 + Real.pi / (2 * t) := by
  calc
    ‖∑ n ∈ Finset.range N,
        ((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)‖
        ≤ ∑ n ∈ Finset.range N,
          ‖((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)‖ :=
            norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, 1 / ((σ + n) ^ 2 + t ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      let w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)
      have hw : w = ((σ + n : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
        dsimp [w]
        push_cast
        ring
      have him : w.im = t := by simp [hw]
      have htq : t ≤ ‖w‖ := by
        have := Complex.abs_im_le_norm w
        simpa [him, abs_of_pos ht] using this
      have hq : 1 ≤ ‖w‖ := ht1.trans htq
      have hpow : ‖w‖ ^ 2 ≤ ‖w‖ ^ (m + 2) := by
        rw [show m + 2 = 2 + m by omega, pow_add]
        exact le_mul_of_one_le_right (sq_nonneg ‖w‖) (one_le_pow₀ hq)
      have hnormsq : ‖w‖ ^ 2 = (σ + n) ^ 2 + t ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, hw, Complex.normSq_add_mul_I]
      change ‖(w ^ (m + 2))⁻¹‖ ≤ _
      rw [norm_inv, norm_pow, inv_eq_one_div]
      calc
        1 / ‖w‖ ^ (m + 2) ≤ 1 / ‖w‖ ^ 2 :=
          one_div_le_one_div_of_le (by positivity) hpow
        _ = 1 / ((σ + n) ^ 2 + t ^ 2) := by rw [hnormsq]
    _ ≤ 1 / t ^ 2 + Real.pi / (2 * t) :=
      RHTower.sum_inv_sq_add_le hσ.le ht N

/-- Explicit all-orders vertical polygamma bound. -/
theorem norm_iteratedDeriv_digamma_vertical_le (m : ℕ) {σ t : ℝ}
    (hσ : 0 < σ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    ‖iteratedDeriv (m + 1) Complex.digamma
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (m + 1).factorial * (1 / t ^ 2 + Real.pi / (2 * t)) := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]; exact hσ
  let C : ℂ := (-1 : ℂ) ^ (m + 1) * (m + 1).factorial
  let E : ℝ := 1 / t ^ 2 + Real.pi / (2 * t)
  have hCnorm : ‖C‖ = (m + 1).factorial := by simp [C]
  have hineq : ∀ N : ℕ,
      ‖iteratedDeriv (m + 1) Complex.digamma z‖ ≤
        ‖iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ))‖ +
          (m + 1).factorial * E := by
    intro N
    have hrec := polygamma_apply_add_nat (m + 1) N hz
    have hsum := norm_polygammaKernel_sum_le m N hσ ht ht1
    have hsum' : ‖∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (m + 2))⁻¹‖ ≤ E := by
      simpa [z, E, add_assoc] using hsum
    have heq : iteratedDeriv (m + 1) Complex.digamma z =
        iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ)) -
          C * ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (m + 2))⁻¹ := by
      rw [show m + 1 + 1 = m + 2 by omega] at hrec
      apply eq_sub_of_add_eq
      simpa [C] using hrec.symm
    rw [heq]
    calc
      ‖iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ)) -
          C * ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (m + 2))⁻¹‖
          ≤ ‖iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ))‖ +
            ‖C * ∑ n ∈ Finset.range N, ((z + (n : ℂ)) ^ (m + 2))⁻¹‖ := norm_sub_le _ _
      _ ≤ ‖iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ))‖ +
            (m + 1).factorial * E := by
          gcongr
          rw [norm_mul, hCnorm]
          exact mul_le_mul_of_nonneg_left hsum' (Nat.cast_nonneg _)
  have hfar := iteratedDeriv_digamma_add_nat_tendsto m z
  have hc : Tendsto (fun _ : ℕ => (m + 1).factorial * E) atTop
      (nhds ((m + 1).factorial * E)) := tendsto_const_nhds
  have hlim : Tendsto (fun N : ℕ =>
      ‖iteratedDeriv (m + 1) Complex.digamma (z + (N : ℂ))‖ +
        (m + 1).factorial * E) atTop
      (nhds (0 + (m + 1).factorial * E)) := by
    simpa using hfar.norm.add hc
  simpa [z, E] using ge_of_tendsto hlim (Filter.Eventually.of_forall hineq)

/-- Every positive-order polygamma tends to zero on every upper vertical line in the open right
half-plane. -/
theorem iteratedDeriv_digamma_vertical_tendsto_zero (m : ℕ) {σ : ℝ}
    (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => iteratedDeriv (m + 1) Complex.digamma
      ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact norm_iteratedDeriv_digamma_vertical_le m hσ (lt_of_lt_of_le zero_lt_one ht) ht
  · have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have h1 : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (nhds 0) := by
      simpa [one_div, inv_pow] using hinv.pow 2
    have h2 : Tendsto (fun t : ℝ => Real.pi / (2 * t)) atTop (nhds 0) := by
      convert hinv.const_mul (Real.pi / 2) using 1
      · funext t
        ring
      · simp
    simpa using (h1.add h2).const_mul ((m + 1).factorial : ℝ)

/-- The canonical complete Bell polynomial expressing `Γ⁽ⁿ⁾/Γ` in the digamma jet. -/
def gammaBell : (n : ℕ) → MvPolynomial (Fin n) ℂ
  | 0 => 1
  | n + 1 =>
      MvPolynomial.X 0 * MvPolynomial.rename Fin.castSucc (gammaBell n) +
        ∑ j : Fin n, MvPolynomial.rename Fin.castSucc (MvPolynomial.pderiv j (gammaBell n)) *
          MvPolynomial.X j.succ

/-- The canonical Bell polynomial evaluates to the normalized `n`-th Gamma derivative off the
poles.  Unlike `exists_gamma_bell`, this theorem exposes one recursive polynomial whose algebraic
invariants can be used by the projective-boundary proof. -/
theorem gamma_iteratedDeriv_eq_gamma_mul_eval_gammaBell (n : ℕ) (s : ℂ)
    (hs : ∀ p : ℕ, s ≠ -(p : ℂ)) :
    iteratedDeriv n Complex.Gamma s = Complex.Gamma s *
      MvPolynomial.eval
        (fun j : Fin n => iteratedDeriv (j : ℕ) Complex.digamma s) (gammaBell n) := by
  induction n generalizing s with
  | zero => simp [gammaBell, iteratedDeriv_zero]
  | succ n ih =>
      set ψ : ℂ → ℂ := Complex.digamma with hψdef
      have hev : (iteratedDeriv n Complex.Gamma) =ᶠ[nhds s]
          (fun w => Complex.Gamma w * MvPolynomial.eval
            (fun j : Fin n => iteratedDeriv (j : ℕ) ψ w) (gammaBell n)) := by
        filter_upwards [offPoles_isOpen.mem_nhds hs] with w hw
        rw [hψdef]
        exact ih w hw
      have hg : ∀ j : Fin n, HasDerivAt (fun w => iteratedDeriv (j : ℕ) ψ w)
          (iteratedDeriv ((j : ℕ) + 1) ψ s) s := by
        intro j
        have hj := (analyticAt_iteratedDeriv_logDeriv (j : ℕ) s hs).differentiableAt.hasDerivAt
        rw [hψdef, Complex.digamma_def]
        rw [iteratedDeriv_succ]
        exact hj
      have hchain := hasDerivAt_mvEval_jet (gammaBell n)
        (fun j => fun w => iteratedDeriv (j : ℕ) ψ w)
        (fun j => iteratedDeriv ((j : ℕ) + 1) ψ s) s hg
      have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
        (analyticAt_Gamma s hs).differentiableAt.hasDerivAt
      have hRHS := hΓ.mul hchain
      have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
      have hgpsi : deriv Complex.Gamma s = Complex.Gamma s * ψ s := by
        rw [hψdef, Complex.digamma_def, logDeriv_apply]
        field_simp
      rw [iteratedDeriv_succ, hev.deriv_eq.trans hRHS.deriv, hgpsi]
      simp only [gammaBell, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_succ,
        Fin.val_castSucc, iteratedDeriv_zero, Fin.val_zero]
      ring

/-- On the pure digamma axis, the order-`n` Bell polynomial is exactly its leading monomial `xⁿ`.
All terms containing a positive-order polygamma vanish. -/
theorem gammaBell_eval_axis (n : ℕ) (x : ℂ) :
    MvPolynomial.eval (fun j : Fin n => if (j : ℕ) = 0 then x else 0) (gammaBell n) = x ^ n := by
  induction n with
  | zero => simp [gammaBell]
  | succ n ih =>
      simp only [gammaBell, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.eval_rename, MvPolynomial.eval_sum, Function.comp_def, Fin.val_zero,
        if_pos, Fin.val_castSucc, Fin.val_succ, Nat.succ_ne_zero, if_false, mul_zero,
        Finset.sum_const_zero, add_zero]
      calc
        x * (MvPolynomial.eval (fun j : Fin n => if (j : ℕ) = 0 then x else 0)
            (gammaBell n)) = x * x ^ n := congrArg (fun y => x * y) ih
        _ = x ^ (n + 1) := by rw [pow_succ']

/-- The order-two Gamma jet has the next projective boundary relation:
`Γ'(σ+it) / Γ''(σ+it) → 0` for `σ > 0`.

This combines the order-two Bell identity `Γ'' = Γ(ψ² + ψ')`, reciprocal-digamma decay, and
vertical trigamma decay. -/
theorem deriv_Gamma_div_second_vertical_tendsto_zero {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
      deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
        iteratedDeriv 2 Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  let z : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * Complex.I
  let ψ : ℝ → ℂ := fun t => Complex.digamma (z t)
  let ψ' : ℝ → ℂ := fun t => deriv Complex.digamma (z t)
  have hinv : Tendsto (fun t => (ψ t)⁻¹) atTop (nhds 0) := by
    simpa [ψ, z] using inv_digamma_vertical_tendsto_zero hσ.le
  have hderiv : Tendsto ψ' atTop (nhds 0) := by
    simpa [ψ', z] using deriv_digamma_vertical_tendsto_zero hσ
  have hcorr : Tendsto (fun t => ψ' t * (ψ t)⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hderiv.mul (hinv.pow 2)
  have hden : Tendsto (fun t => 1 + ψ' t * (ψ t)⁻¹ ^ 2) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hcorr
  have hmodel : Tendsto (fun t => (ψ t)⁻¹ / (1 + ψ' t * (ψ t)⁻¹ ^ 2))
      atTop (nhds 0) := by
    simpa using hinv.div hden (by norm_num : (1 : ℂ) ≠ 0)
  apply hmodel.congr'
  have hre := re_digamma_vertical_tendsto_atTop hσ.le
  filter_upwards [hre.eventually_gt_atTop 0,
    hden.eventually_ne (by norm_num : (1 : ℂ) ≠ 0)] with t ht hdenne
  have hzre : (z t).re = σ := by simp [z]
  have hpoles : ∀ p : ℕ, z t ≠ -(p : ℂ) := by
    intro p heq
    have hreEq := congrArg Complex.re heq
    simp [hzre] at hreEq
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hG : Complex.Gamma (z t) ≠ 0 := Complex.Gamma_ne_zero hpoles
  have hpsi : ψ t ≠ 0 := by
    intro hzero
    have : (Complex.digamma (z t)).re = 0 := by simp [ψ, hzero]
    rw [this] at ht
    linarith
  have hBell := iteratedDeriv_two_Gamma_eq_logDeriv (z t) hpoles
  have hlog : deriv Complex.Gamma (z t) / Complex.Gamma (z t) = ψ t := by
    simp [ψ, Complex.digamma_def, logDeriv_apply]
  have hlog' : deriv (fun w => deriv Complex.Gamma w / Complex.Gamma w) (z t) = ψ' t := by
    rw [show (fun w => deriv Complex.Gamma w / Complex.Gamma w) = Complex.digamma by
      funext w
      rw [Complex.digamma_def, logDeriv_apply]]
  rw [hlog, hlog'] at hBell
  have hderivG : deriv Complex.Gamma (z t) = ψ t * Complex.Gamma (z t) :=
    (div_eq_iff hG).mp hlog
  change (ψ t)⁻¹ / (1 + ψ' t * (ψ t)⁻¹ ^ 2) =
    deriv Complex.Gamma (z t) / iteratedDeriv 2 Complex.Gamma (z t)
  rw [hBell, hderivG]
  field_simp [hG, hpsi, hdenne]

/-- Finite projective coefficient limits turn translated finite relations into
constant-coefficient limiting relations.

Here `a n i` is the normalized coefficient of the `i`-th differential monomial after the `n`-th
vertical return, and `x n i` is that monomial evaluated on the returned jet.  The hypotheses are
the two genuine convergence statements; the conclusion is the autonomous relation used in the
Gamma boundary argument. -/
theorem finiteProjectiveRelationCollapse
    {ι : Type*} (S : Finset ι)
    (a x : ℕ → ι → ℂ) (da dx : ι → ℂ)
    (ha : ∀ i ∈ S, Tendsto (fun n => a n i) atTop (nhds (da i)))
    (hx : ∀ i ∈ S, Tendsto (fun n => x n i) atTop (nhds (dx i)))
    (hzero : ∀ n, ∑ i ∈ S, a n i * x n i = 0) :
    ∑ i ∈ S, da i * dx i = 0 := by
  have hlim :
      Tendsto (fun n => ∑ i ∈ S, a n i * x n i) atTop
        (nhds (∑ i ∈ S, da i * dx i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact (ha i hi).mul (hx i hi)
  have hzeroLim :
      Tendsto (fun n => ∑ i ∈ S, a n i * x n i) atTop (nhds 0) := by
    rw [show (fun n => ∑ i ∈ S, a n i * x n i) = (fun _ => 0) by
      funext n
      exact hzero n]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzeroLim

end

end GaloisForLFunctions
