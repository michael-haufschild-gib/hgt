import GaloisForLFunctions.ZeroConfigurationGeometry.HighDerivativesRecoverARightmostZero
import GaloisForLFunctions.RHTower.ZetaWeakRecurrenceLadderCollapse
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg
import GaloisForLFunctions.RHTower.XiPrimeLogHigherValuationHalfPlane
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros
import GaloisForLFunctions.ZeroConfigurationGeometry.VonMangoldtMomentDiagonalsVanish

/-!
# A finite exceptional layer forces persistent low-height jets

Failure of the asymptotic abscissa law selects an actual rightmost zeta zero.
For the entire residue unit `(s-1)ζ(s)`, normalized logarithmic-derivative jets at
every centre horizontally to its right converge to its positive multiplicity.
The cofactor and its analytic remainder are constructed from the actual function.
At the unit horizontal shift the pole correction vanishes. The raw von Mangoldt
moments then tend to a negative multiplicity while their coefficient-square
diagonals vanish, leaving the squared multiplicity in the off-diagonal sum.
-/

open Complex Filter Metric Set Topology RHTower
open ComplexConjugate

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Removing the pole at `1` adds its explicit derivative to every zeta jet. -/
theorem iteratedDeriv_logDeriv_zetaResidueUnit {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    iteratedDeriv k (logDeriv zetaResidueUnit) s =
      iteratedDeriv k (logDeriv riemannZeta) s +
        (-1 : ℂ) ^ k * (k.factorial : ℂ) / (s - 1) ^ (k + 1) := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hlocal : logDeriv zetaResidueUnit =ᶠ[𝓝 s]
      fun z => logDeriv riemannZeta z + (z - 1)⁻¹ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; norm_num at hz
    have hunit : zetaResidueUnit z ≠ 0 := by
      rw [(zetaResidueUnit_eventuallyEq hz1).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_le_re hz.le)
    exact (eq_sub_iff_add_eq.mp (logDeriv_zeta_eq hz1 hunit)).symm
  have hlog : AnalyticAt ℂ (logDeriv riemannZeta) s :=
    (analyticOn_riemannZeta s hs1).deriv.div (analyticOn_riemannZeta s hs1)
      (riemannZeta_ne_zero_of_one_le_re hs.le)
  have hinv : ContDiffAt ℂ k (fun z : ℂ => (z - 1)⁻¹) s := by
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    fun_prop
  rw [hlocal.iteratedDeriv_eq, iteratedDeriv_fun_add hlog.contDiffAt hinv,
    iteratedDeriv_inv_sub 1 k s (sub_ne_zero.mpr hs1)]

/-- Failure of the abscissa law produces an actual zero whose multiplicity is recovered
by all sufficiently high logarithmic-derivative jets of the entire residue unit. -/
theorem not_asymptoticAbscissaLaw_has_persistent_low_jets :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧ analyticOrderAt zetaResidueUnit ρ = m ∧
        ∀ d : ℝ, 0 < d →
          Tendsto (fun k : ℕ => (d : ℂ) ^ (k + 1) *
            iteratedDeriv k (logDeriv zetaResidueUnit) (ρ + (d : ℂ)) /
            ((-1 : ℂ) ^ k * (k.factorial : ℂ))) atTop (𝓝 (m : ℂ)) := by
  intro hnot
  unfold AsymptoticAbscissaLaw at hnot
  push Not at hnot
  obtain ⟨h, hh, hfin, q, hq⟩ := hnot
  obtain ⟨q₀, hq₀, hqmax⟩ := hfin.exists_maximalFor
    (fun q : XiZeroCopy => (q.1 : ℂ).re)
    {q : XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re} ⟨q, hq⟩
  change 1 / 2 + h < (q₀.1 : ℂ).re at hq₀
  have hmax : ∀ q' : XiZeroCopy, (q'.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    intro q'
    by_cases hmem : 1 / 2 + h < (q'.1 : ℂ).re
    · by_contra hgt
      exact (not_le.mpr (lt_of_not_ge hgt)) (hqmax hmem (lt_of_not_ge hgt).le)
    · exact (le_of_not_gt hmem).trans (le_of_lt hq₀)
  let ρ : ℂ := (q₀.1 : ℂ)
  have hρhalf : 1 / 2 < ρ.re := by dsimp [ρ]; linarith only [hh, hq₀]
  have hρone : ρ.re < 1 := (xi_divisor_support_re_mem_open_unit q₀.1).2
  have hζ : riemannZeta ρ = 0 := riemannZeta_eq_zero_of_xiZeroCopy q₀
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hρone; norm_num at hρone
  have hunit : zetaResidueUnit ρ = 0 := by
    rw [(zetaResidueUnit_eventuallyEq hρ1).eq_of_nhds, hζ, mul_zero]
  have hunitmax : ∀ z : ℂ, zetaResidueUnit z = 0 → z.re ≤ ρ.re := by
    intro z hz
    by_contra hgt
    have hzre : ρ.re < z.re := lt_of_not_ge hgt
    have hz1 : z ≠ 1 := by intro h; rw [h, zetaResidueUnit_one] at hz; norm_num at hz
    have hζz : riemannZeta z = 0 := by
      rw [(zetaResidueUnit_eventuallyEq hz1).eq_of_nhds] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hz1)
    have hzlt : z.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h) hζz
    obtain ⟨q', hq'⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζz (by linarith) hzlt
    have hle := hmax q'
    rw [hq'] at hle
    exact (not_le.mpr hzre) hle
  have han : AnalyticOnNhd ℂ zetaResidueUnit univ := fun z _ => analyticAt_zetaResidueUnit z
  have hord : analyticOrderAt zetaResidueUnit ρ ≠ ⊤ := by
    refine han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 1) trivial trivial ?_
    rw [(analyticAt_zetaResidueUnit 1).analyticOrderAt_eq_zero.mpr (by simp)]
    exact ENat.zero_ne_top
  let m : ℕ := (analyticOrderAt zetaResidueUnit ρ).toNat
  have hm : analyticOrderAt zetaResidueUnit ρ = m := (ENat.coe_toNat hord).symm
  have hmpos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm0
    have hzero : analyticOrderAt zetaResidueUnit ρ = 0 := by rw [hm, hm0]; rfl
    exact ((analyticAt_zetaResidueUnit ρ).analyticOrderAt_eq_zero.mp hzero) hunit
  exact ⟨ρ, m, hρhalf, hρone, hζ, hmpos, hm,
    fun d hd => tendsto_logDeriv_jets_at_rightmost_zero analyticAt_zetaResidueUnit hm hunitmax hd⟩

/-- The persistent jets expressed through the actual zeta logarithmic derivative,
with the pole at `1` retained as an explicit geometric term. -/
theorem not_asymptoticAbscissaLaw_has_corrected_zeta_jet_limit :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧ ∀ d : ℝ, 1 - ρ.re < d →
          Tendsto (fun k : ℕ =>
            (d : ℂ) ^ (k + 1) * iteratedDeriv k (logDeriv riemannZeta) (ρ + (d : ℂ)) /
              ((-1 : ℂ) ^ k * (k.factorial : ℂ)) +
            ((d : ℂ) / (ρ + (d : ℂ) - 1)) ^ (k + 1)) atTop (𝓝 (m : ℂ)) := by
  intro hnot
  obtain ⟨ρ, m, hρhalf, hρone, hζ, hm, _, hlim⟩ :=
    not_asymptoticAbscissaLaw_has_persistent_low_jets hnot
  refine ⟨ρ, m, hρhalf, hρone, hζ, hm, ?_⟩
  intro d hd
  have hdpos : 0 < d := by linarith
  have hs : 1 < (ρ + (d : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  refine (hlim d hdpos).congr' (Filter.Eventually.of_forall fun k => ?_)
  dsimp only
  rw [iteratedDeriv_logDeriv_zetaResidueUnit hs k, div_pow]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hs1 : ρ + (d : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    rw [h] at hs
    norm_num at hs
  field_simp

#print axioms not_asymptoticAbscissaLaw_has_persistent_low_jets
#print axioms not_asymptoticAbscissaLaw_has_corrected_zeta_jet_limit

/-- The same residue is isolated by logarithmic moments of the actual von Mangoldt series.
The geometric correction is exactly the pole at `1`. -/
theorem not_asymptoticAbscissaLaw_has_prime_moment_limit :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧ ∀ d : ℝ, 1 - ρ.re < d →
          Tendsto (fun k : ℕ =>
            (d : ℂ) ^ (k + 1) *
              LSeries (LSeries.logMul^[k] (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
                (ρ + (d : ℂ)) / (k.factorial : ℂ) -
            ((d : ℂ) / (ρ + (d : ℂ) - 1)) ^ (k + 1)) atTop (𝓝 (-(m : ℂ))) := by
  intro hnot
  obtain ⟨ρ, m, hρhalf, hρone, hζ, hm, hlim⟩ :=
    not_asymptoticAbscissaLaw_has_corrected_zeta_jet_limit hnot
  refine ⟨ρ, m, hρhalf, hρone, hζ, hm, ?_⟩
  intro d hd
  have hs : 1 < (ρ + (d : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  refine (hlim d hd).neg.congr' (Filter.Eventually.of_forall fun k => ?_)
  dsimp only
  have hderiv := iteratedDeriv_zetaLogDeriv_eq_LSeries k hs
  change iteratedDeriv k (logDeriv riemannZeta) (ρ + (d : ℂ)) = _ at hderiv
  rw [hderiv, pow_succ (-1 : ℂ)]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  ring

#print axioms not_asymptoticAbscissaLaw_has_prime_moment_limit

/-- Proper prime powers have no normalized jet mass at any radius strictly inside
the half-plane of absolute convergence `Re s > 1/2`. -/
theorem tendsto_normalized_higher_prime_power_jets {s a : ℂ}
    (ha : ‖a‖ < s.re - 1 / 2) :
    Tendsto (fun k : ℕ => a ^ (k + 1) *
      iteratedDeriv k xiPrimeLogHigherValuation s /
      ((-1 : ℂ) ^ k * (k.factorial : ℂ))) atTop (𝓝 0) := by
  let R : ℝ := (‖a‖ + s.re - 1 / 2) / 2
  have hR : ‖a‖ < R := by dsimp [R]; linarith only [ha]
  have hRhalf : R < s.re - 1 / 2 := by dsimp [R]; linarith only [ha]
  have han : AnalyticOnNhd ℂ xiPrimeLogHigherValuation {z : ℂ | 1 / 2 < z.re} :=
    differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  apply tendsto_normalized_analytic_jets (R := R) ?_ hR
  intro z hz
  have hn : ‖z - s‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hn)).1
  simp only [Complex.sub_re] at hre
  exact han z (by dsimp only [mem_setOf_eq]; linarith only [hre, hRhalf])

/-- The nonzero limit survives removal of every proper prime power: it is already
present in the corrected prime-only logarithmic series. -/
theorem not_asymptoticAbscissaLaw_has_prime_only_jet_limit :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧ ∀ d : ℝ, 1 - ρ.re < d →
          Tendsto (fun k : ℕ => (d : ℂ) ^ (k + 1) *
            iteratedDeriv k (fun z => xiPrimeLogDirichlet z - (z - 1)⁻¹)
              (ρ + (d : ℂ)) / ((-1 : ℂ) ^ k * (k.factorial : ℂ)))
            atTop (𝓝 (-(m : ℂ))) := by
  intro hnot
  obtain ⟨ρ, m, hρhalf, hρone, hζ, hm, _, hlim⟩ :=
    not_asymptoticAbscissaLaw_has_persistent_low_jets hnot
  refine ⟨ρ, m, hρhalf, hρone, hζ, hm, ?_⟩
  intro d hd
  have hdpos : 0 < d := by linarith only [hd, hρone]
  have hs : 1 < (ρ + (d : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hd]
  have hscale : ‖(d : ℂ)‖ < (ρ + (d : ℂ)).re - 1 / 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos,
      Complex.add_re, Complex.ofReal_re]
    linarith only [hρhalf]
  have hhigh := tendsto_normalized_higher_prime_power_jets hscale
  have hlocal : (fun z => xiPrimeLogDirichlet z - (z - 1)⁻¹) =ᶠ[𝓝 (ρ + (d : ℂ))]
      fun z => (-1 : ℂ) * (logDeriv zetaResidueUnit z + xiPrimeLogHigherValuation z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    rw [xiPrimeLogDirichlet_eq_pole_add_regular_sub_higherValuation hz,
      RHTower.Sieve.zetaLogDerivReg]
    ring
  have hs1 : ρ + (d : ℂ) ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hunit : zetaResidueUnit (ρ + (d : ℂ)) ≠ 0 := by
    rw [(zetaResidueUnit_eventuallyEq hs1).eq_of_nhds]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs.le)
  have hlog : AnalyticAt ℂ (logDeriv zetaResidueUnit) (ρ + (d : ℂ)) :=
    (analyticAt_zetaResidueUnit _).deriv.div (analyticAt_zetaResidueUnit _) hunit
  have hH : AnalyticAt ℂ xiPrimeLogHigherValuation (ρ + (d : ℂ)) :=
    differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re) _ (by
        change 1 / 2 < (ρ + (d : ℂ)).re
        linarith only [hs])
  have ht := ((hlim d hdpos).add hhigh).neg
  rw [add_zero] at ht
  refine ht.congr' (Filter.Eventually.of_forall fun k => ?_)
  dsimp only
  rw [hlocal.iteratedDeriv_eq, _root_.iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add hlog.contDiffAt hH.contDiffAt]
  ring

#print axioms tendsto_normalized_higher_prime_power_jets
#print axioms not_asymptoticAbscissaLaw_has_prime_only_jet_limit

/-- At the unit horizontal shift the pole correction vanishes: the uncorrected
von Mangoldt moments themselves tend to a negative integer. -/
theorem not_asymptoticAbscissaLaw_has_raw_prime_moment_limit :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧ Tendsto (fun k : ℕ =>
          LSeries (LSeries.logMul^[k]
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (ρ + 1) /
            (k.factorial : ℂ)) atTop (𝓝 (-(m : ℂ))) := by
  intro hnot
  obtain ⟨ρ, m, hρhalf, hρone, hζ, hm, hlim⟩ :=
    not_asymptoticAbscissaLaw_has_prime_moment_limit hnot
  refine ⟨ρ, m, hρhalf, hρone, hζ, hm, ?_⟩
  have hγ := four_le_abs_im_of_zeta_zero (by linarith only [hρhalf]) hρone hζ
  have hnorm : 1 < ‖ρ‖ := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 4)
    (hγ.trans (Complex.abs_im_le_norm ρ))
  have hinv : ‖ρ⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hnorm
  have hpowers : Tendsto (fun k : ℕ => (ρ⁻¹) ^ (k + 1)) atTop (𝓝 0) := by
    simpa only [pow_succ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hinv).mul_const (ρ⁻¹)
  have ht := hlim 1 (by linarith only [hρhalf])
  simp only [Complex.ofReal_one, one_pow, one_mul, add_sub_cancel_right, one_div] at ht
  simpa only [sub_add_cancel, add_zero] using ht.add hpowers

#print axioms not_asymptoticAbscissaLaw_has_raw_prime_moment_limit

/-- Failure of AAL forces a nonzero raw moment limit at a point where the
complete coefficient-square diagonal vanishes unconditionally. -/
theorem not_asymptoticAbscissaLaw_has_nonzero_moment_and_vanishing_diagonal :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧
        Tendsto (fun k : ℕ =>
          LSeries (LSeries.logMul^[k]
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (ρ + 1) /
            (k.factorial : ℂ)) atTop (𝓝 (-(m : ℂ))) ∧
        Tendsto (fun k : ℕ => ∑' n : ℕ,
          ‖LSeries.term (LSeries.logMul^[k]
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (ρ + 1) n /
            (k.factorial : ℂ)‖ ^ 2) atTop (𝓝 0) := by
  intro hnot
  obtain ⟨ρ, m, hρhalf, hρone, hζ, hm, hlim⟩ :=
    not_asymptoticAbscissaLaw_has_raw_prime_moment_limit hnot
  refine ⟨ρ, m, hρhalf, hρone, hζ, hm, hlim, ?_⟩
  apply tendsto_normalizedMangoldtTermDiagonal_zero
  simp only [Complex.add_re, Complex.one_re]
  linarith only [hρhalf]

#print axioms not_asymptoticAbscissaLaw_has_nonzero_moment_and_vanishing_diagonal

/-- Removing equal indices from an absolutely convergent correlation sum subtracts
exactly the coefficient-square diagonal. -/
theorem tsum_offDiagonal_re {a : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖)) :
    (∑' n : ℕ, ∑' j : ℕ, if j = n then 0 else a n * conj (a j)).re =
      ‖∑' n : ℕ, a n‖ ^ 2 - ∑' n : ℕ, ‖a n‖ ^ 2 := by
  have ha' : Summable a := ha.of_norm
  have hconj : Summable (fun n => conj (a n)) := Complex.summable_conj.mpr ha'
  have hconjNorm : Summable (fun n => ‖conj (a n)‖) := by
    simpa only [Complex.norm_conj] using ha
  have hprod := summable_mul_of_summable_norm ha hconjNorm
  have hdiag : Summable (fun n => a n * conj (a n)) :=
    hprod.comp_injective (i := fun n : ℕ => (n, n))
      (fun _ _ h => congrArg Prod.fst h)
  have hrow (n : ℕ) : (∑' j : ℕ, if j = n then 0 else a n * conj (a j)) =
      a n * conj (∑' j : ℕ, a j) - a n * conj (a n) := by
    have hsingle : Summable (fun j : ℕ => if j = n then a n * conj (a n) else 0) := by
      apply (ha.mul_left ‖a n‖).of_norm_bounded
      intro j
      by_cases h : j = n
      · subst j
        simp only [ite_true, norm_mul, Complex.norm_conj, le_refl]
      · simp only [if_neg h, norm_zero]
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have heq : (fun j : ℕ => if j = n then 0 else a n * conj (a j)) =
        fun j => a n * conj (a j) - if j = n then a n * conj (a n) else 0 := by
      funext j
      by_cases h : j = n <;> simp [h]
    rw [heq, (hconj.mul_left (a n)).tsum_sub hsingle, tsum_mul_left,
      ← Complex.conj_tsum, tsum_ite_eq]
  simp_rw [hrow]
  rw [(ha'.mul_right _).tsum_sub hdiag, tsum_mul_right]
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_tsum,
    Complex.sub_re, Complex.ofReal_re]

/-- The entire surviving squared moment is an explicit off-diagonal arithmetic
correlation, whose limit is the square of the selected zero's multiplicity. -/
theorem not_asymptoticAbscissaLaw_has_positive_offDiagonal_limit :
    ¬ AsymptoticAbscissaLaw →
      ∃ (ρ : ℂ) (m : ℕ), 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧
        0 < m ∧
        let a : ℕ → ℕ → ℂ := fun k n =>
          LSeries.term (LSeries.logMul^[k]
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (ρ + 1) n /
            (k.factorial : ℂ)
        Tendsto (fun k : ℕ =>
          (∑' n : ℕ, ∑' j : ℕ, if j = n then 0 else a k n * conj (a k j)).re)
          atTop (𝓝 ((m : ℝ) ^ 2)) := by
  intro hnot
  obtain ⟨ρ, m, hρhalf, hρone, hζ, hm, hlim, hdiag⟩ :=
    not_asymptoticAbscissaLaw_has_nonzero_moment_and_vanishing_diagonal hnot
  refine ⟨ρ, m, hρhalf, hρone, hζ, hm, ?_⟩
  dsimp only
  have hs : 1 < (ρ + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hρhalf]
  have htotal := (hlim.norm.pow 2).sub hdiag
  simp only [norm_neg, Complex.norm_natCast, sub_zero] at htotal
  refine htotal.congr' (Filter.Eventually.of_forall fun k => ?_)
  have hslog : LSeriesSummable (LSeries.logMul^[k]
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (ρ + 1) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt abscissaOfAbsConv_vonMangoldt_le (by exact_mod_cast hs)
  have hsum : Summable (fun n =>
      ‖LSeries.term (LSeries.logMul^[k]
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) (ρ + 1) n /
        (k.factorial : ℂ)‖) :=
    summable_norm_iff.mpr (hslog.div_const (k.factorial : ℂ))
  dsimp only
  simpa only [tsum_div_const, LSeries] using (tsum_offDiagonal_re hsum).symm

#print axioms not_asymptoticAbscissaLaw_has_positive_offDiagonal_limit

end GaloisForLFunctions.ZeroConfigurationGeometry
