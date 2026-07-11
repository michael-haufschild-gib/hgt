import GaloisForLFunctions.GammaDifferentialFE
import GaloisForLFunctions.MeromorphicPoleOrbitBoundary
import GaloisForLFunctions.OrbitBalanceAdditive
import GaloisForLFunctions.RHTower.DigammaAsymptotic
import GaloisForLFunctions.RHTower.TrigammaVertical

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
