import GaloisForLFunctions.RHTower.JointAncestryArithmeticCapstone
import GaloisForLFunctions.HTGeometry.PrimePoissonSuperselectionScreen
import GaloisForLFunctions.HTGeometry.InfiniteTorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.TorusPoissonConvolutionSemigroup

/-!
# JAS positivity below `½` lives on Haar-null sets

A *JAS certificate* at dressing `σ` is a finite positive measure `ν` on the prime torus
`Nat.Primes → UnitAddCircle` whose Fourier coefficients are the dressed aggregate:
`∫ χ_n dν = jasDressedLagAggregate σ n` for every finite character `n`.  A certificate forces
`JasDressedPSD σ` (`jasDressedPSD_of_integral_infiniteTorusFourier_eq`).

* **Below `½` every certificate is singular to Haar measure**
  (`mutuallySingular_torusHaar_of_jas_fourier`): for `0 < σ < ½`, a certificate forces RH by the
  abscissa gap, and under RH the only certificate is `Σ_ρ w_ρ μ_{σ,−γ_ρ}`, a countable sum of
  prime-Poisson laws, each singular to Haar by Kakutani's criterion `Σ_p p^{−2σ} = ∞`.
* **Above `½` the certificate is Haar-absolutely continuous** under RH
  (`jasCertificate_absolutelyContinuous_torusHaar`).

So the dressings that decide RH are exactly those whose positivity certificates are Haar-singular:
the threshold `½` of the abscissa gap is the Kakutani threshold of the prime-Poisson laws.  In
particular no vector of `L²(Haar)` (and no density in `L¹(Haar)`) certifies JAS positivity below `½`.
-/

open Complex MeasureTheory
open scoped ComplexConjugate

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **A certificate forces positivity.** -/
theorem jasDressedPSD_of_integral_infiniteTorusFourier_eq {σ : ℝ}
    (ν : Measure (Nat.Primes → UnitAddCircle)) [IsFiniteMeasure ν]
    (hν : ∀ n, ∫ x, infiniteTorusFourier n x ∂ν = jasDressedLagAggregate σ n) :
    JasDressedPSD σ := by
  intro ι t c n _
  have hint : ∀ m : Nat.Primes →₀ ℤ, Integrable (fun x => infiniteTorusFourier m x) ν :=
    integrable_infiniteTorusFourier ν
  have hpt : ∀ x, ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * infiniteTorusFourier (n i - n j) x =
      ((Complex.normSq (∑ i ∈ t, c i * infiniteTorusFourier (n i) x) : ℝ) : ℂ) := by
    intro x
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sub_eq_add_neg, infiniteTorusFourier_add, infiniteTorusFourier_neg, map_mul]
    ring
  have heq : ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * jasDressedLagAggregate σ (n i - n j) =
      ∫ x, ∑ i ∈ t, ∑ j ∈ t, c i * conj (c j) * infiniteTorusFourier (n i - n j) x ∂ν := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul, hν]
      · intro j _; exact (hint _).const_mul _
    · intro i _; exact integrable_finsetSum _ fun j _ => (hint _).const_mul _
  rw [heq]
  simp_rw [hpt]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun x => Complex.normSq_nonneg _

/-- Finite measures on the prime torus are determined by their Fourier coefficients. -/
theorem finiteMeasure_ext_of_infiniteTorusFourier {μ ν : Measure (Nat.Primes → UnitAddCircle)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n, ∫ x, infiniteTorusFourier n x ∂μ = ∫ x, infiniteTorusFourier n x ∂ν) : μ = ν := by
  have hmass : (μ Set.univ).toReal = (ν Set.univ).toReal := by
    have h0 := h 0
    rw [infiniteTorusFourier_zero] at h0
    simp only [ContinuousMap.one_apply, integral_const] at h0
    have h1 := congrArg Complex.re h0
    simpa [measureReal_def] using h1
  have hmass' : μ Set.univ = ν Set.univ :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hmass
  rcases eq_or_ne μ 0 with hμ | hμ
  · rw [hμ, Measure.coe_zero, Pi.zero_apply] at hmass'
    rw [hμ, eq_comm, ← Measure.measure_univ_eq_zero, ← hmass']
  · haveI : NeZero μ := ⟨hμ⟩
    have hν : ν ≠ 0 := by
      intro h0; apply hμ
      rw [← Measure.measure_univ_eq_zero, hmass', h0, Measure.coe_zero, Pi.zero_apply]
    haveI : NeZero ν := ⟨hν⟩
    have hp := probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq
      ⟨(μ Set.univ)⁻¹ • μ, isProbabilityMeasureSMul⟩ ⟨(ν Set.univ)⁻¹ • ν, isProbabilityMeasureSMul⟩
      fun n => by
        simp only [ProbabilityMeasure.coe_mk, integral_smul_measure, h n, hmass']
    have hc : (μ Set.univ)⁻¹ • μ = (μ Set.univ)⁻¹ • ν := by
      have := congrArg (fun m : ProbabilityMeasure (Nat.Primes → UnitAddCircle) =>
        (m : Measure (Nat.Primes → UnitAddCircle))) hp
      simpa only [ProbabilityMeasure.coe_mk, hmass'] using this
    have hne : (μ Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
    have hnt : (μ Set.univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (NeZero.ne _)
    ext s _
    have := congrArg (fun m : Measure (Nat.Primes → UnitAddCircle) => m s) hc
    simp only [Measure.smul_apply, smul_eq_mul] at this
    exact (ENNReal.mul_right_inj hne hnt).mp this

/-- The Fourier coefficients of a prime-Poisson law:
`μ̂_{σ,t}(n) = e^{−σ‖n‖} e^{i t (log u − log v)}` for `n = u/v`. -/
theorem integral_infiniteTorusFourier_primePoissonMeasure_eq {σ : ℝ} (t : ℝ) (hσ : 0 < σ)
    (n : Nat.Primes →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(primePoissonMeasure σ t hσ) =
      (Real.exp (-σ * jasLogSize n) : ℂ) *
        cexp ((t : ℂ) * I * ((jasLogPos n - jasLogNeg n : ℝ) : ℂ)) := by
  rw [integral_infiniteTorusFourier_primePoissonMeasure]
  have hloc : ∀ p : Nat.Primes, ∀ k : ℤ,
      circlePoissonFourierMoment (primePoissonParameter σ t hσ p) k =
        cexp (((-σ * ((|k| : ℝ) * Real.log p) : ℝ) : ℂ) +
          (t : ℂ) * I * (((k : ℝ) * Real.log p : ℝ) : ℂ)) := by
    intro p k
    rcases k with m | m
    · simp only [circlePoissonFourierMoment, coe_primePoissonParameter,
        primePoissonParameterValue, ← Complex.exp_nat_mul]
      congr 1
      have hm : |((Int.ofNat m : ℤ) : ℝ)| = (m : ℝ) := by simp
      rw [hm, Int.ofNat_eq_natCast]
      push_cast
      ring
    · simp only [circlePoissonFourierMoment, coe_primePoissonParameter,
        primePoissonParameterValue, ← Complex.exp_conj, ← Complex.exp_nat_mul]
      congr 1
      have hm : |((Int.negSucc m : ℤ) : ℝ)| = ((m + 1 : ℕ) : ℝ) := by
        rw [Int.cast_negSucc, abs_neg]; push_cast; rw [abs_of_nonneg (by positivity)]
      rw [hm, Int.cast_negSucc]
      simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
  rw [Finsupp.prod, Finset.prod_congr rfl fun p _ => hloc p (n p), ← Complex.exp_sum,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have h1 : jasLogSize n = n.sum fun p k => (|k| : ℝ) * Real.log p := jasLogSize_eq n
  have h2 : jasLogPos n - jasLogNeg n = n.sum fun p k => (k : ℝ) * Real.log p := by
    unfold jasLogPos jasLogNeg Finsupp.sum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← sub_mul]
    congr 1
    exact_mod_cast Int.toNat_sub_toNat_neg (n p)
  rw [h1, h2, Finsupp.sum, Finsupp.sum, Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]

/-- The canonical certificate `Σ_ρ w_ρ μ_{σ,−γ_ρ}` (a certificate under RH). -/
def jasCertificate (σ : ℝ) (hσ : 0 < σ) : Measure (Nat.Primes → UnitAddCircle) :=
  Measure.sum fun q : XiZeroCopy =>
    ENNReal.ofReal (lagWeight q).re • primePoissonMeasure σ (-(q.1 : ℂ).im) hσ

theorem summable_lagWeight_re : Summable fun q : XiZeroCopy => (lagWeight q).re :=
  summable_norm_lagWeight.of_norm_bounded fun q => by
    rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _

instance (σ : ℝ) (hσ : 0 < σ) : IsFiniteMeasure (jasCertificate σ hσ) := by
  refine ⟨?_⟩
  rw [jasCertificate, Measure.sum_apply _ MeasurableSet.univ]
  have h : ∀ q : XiZeroCopy, (ENNReal.ofReal (lagWeight q).re •
      primePoissonMeasure σ (-(q.1 : ℂ).im) hσ) Set.univ = ENNReal.ofReal (lagWeight q).re :=
    fun q => by rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  simp_rw [h]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => (lagWeight_re_pos q).le) summable_lagWeight_re]
  exact ENNReal.ofReal_lt_top

/-- Fourier coefficients of the canonical certificate. -/
theorem integral_infiniteTorusFourier_jasCertificate {σ : ℝ} (hσ : 0 < σ) (n : Nat.Primes →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(jasCertificate σ hσ) =
      ∑' q : XiZeroCopy, ((lagWeight q).re : ℂ) *
        ∫ x, infiniteTorusFourier n x ∂(primePoissonMeasure σ (-(q.1 : ℂ).im) hσ) := by
  have hint : Integrable (fun x => infiniteTorusFourier n x) (jasCertificate σ hσ) :=
    integrable_infiniteTorusFourier _ n
  unfold jasCertificate at hint ⊢
  rw [integral_sum_measure hint]
  refine tsum_congr fun q => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (lagWeight_re_pos q).le, Complex.real_smul]

/-- **Under RH the canonical measure is a certificate.** -/
theorem integral_infiniteTorusFourier_jasCertificate_of_rh (hRH : RiemannHypothesis) {σ : ℝ}
    (hσ : 0 < σ) (n : Nat.Primes →₀ ℤ) :
    ∫ x, infiniteTorusFourier n x ∂(jasCertificate σ hσ) = jasDressedLagAggregate σ n := by
  rw [integral_infiniteTorusFourier_jasCertificate, jasDressedLagAggregate, weilLagFunction,
    ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  have hre : (q.1 : ℂ).re = 1 / 2 :=
    xi_zero_re_eq_half_of_RH hRH (xi_xiZeroCopy_eq_zero q)
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (q.1 : ℂ).im := ⟨_, rfl⟩
  have hq : (q.1 : ℂ) = 1 / 2 + (γ : ℂ) * I := by
    apply Complex.ext <;> simp [hre, hγ]
  have hreal : (q.1 : ℂ) * (1 - (q.1 : ℂ)) = ((1 / 4 + γ ^ 2 : ℝ) : ℂ) := by
    rw [hq]; push_cast; linear_combination (-(γ : ℂ) ^ 2) * Complex.I_sq
  have hw : lagWeight q = ((lagWeight q).re : ℂ) := by
    unfold lagWeight
    rw [hreal, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hwq : 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) = ((lagWeight q).re : ℂ) := hw
  rw [integral_infiniteTorusFourier_primePoissonMeasure_eq, ← hγ, div_eq_mul_one_div _ (_ * _),
    hwq, show (q.1 : ℂ) - 1 / 2 = (γ : ℂ) * I by rw [hq]; ring]
  have hexp : cexp (((jasLogNeg n - jasLogPos n : ℝ) : ℂ) * ((γ : ℂ) * I)) =
      cexp (((-γ : ℝ) : ℂ) * I * ((jasLogPos n - jasLogNeg n : ℝ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [hexp]
  ring

/-- Each summand of the certificate is singular to Haar below the Kakutani threshold. -/
theorem jasCertificate_mutuallySingular {σ : ℝ} (hσ : 0 < σ) (hσh : σ ≤ 1 / 2) :
    jasCertificate σ hσ ⟂ₘ torusHaar Nat.Primes := by
  rw [jasCertificate, Measure.MutuallySingular.sum_left]
  exact fun q => (primePoissonMeasure_mutuallySingular_torusHaar_of_le_half σ _ hσ hσh).smul _

/-- Above the threshold the certificate is Haar-absolutely continuous. -/
theorem jasCertificate_absolutelyContinuous_torusHaar {σ : ℝ} (hσ : 0 < σ) (hσh : 1 / 2 < σ) :
    jasCertificate σ hσ ≪ torusHaar Nat.Primes :=
  Measure.absolutelyContinuous_sum_left fun _ =>
    ((primePoissonMeasure_absolutelyContinuous_torusHaar_iff σ _ hσ).mpr hσh).smul_left _

/-- **Certificates below `½` are Haar-singular.**  For `0 < σ < ½`, every finite measure on the
prime torus whose Fourier coefficients are the dressed JAS aggregate is singular to Haar measure. -/
theorem mutuallySingular_torusHaar_of_jas_fourier {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1 / 2)
    (ν : Measure (Nat.Primes → UnitAddCircle)) [IsFiniteMeasure ν]
    (hν : ∀ n, ∫ x, infiniteTorusFourier n x ∂ν = jasDressedLagAggregate σ n) :
    ν ⟂ₘ torusHaar Nat.Primes := by
  have hRH := riemannHypothesis_iff_exists_lt_half.mpr
    ⟨σ, hσ, jasDressedPSD_of_integral_infiniteTorusFourier_eq ν hν⟩
  have heq : ν = jasCertificate σ hσ0 := finiteMeasure_ext_of_infiniteTorusFourier fun n => by
    rw [hν, integral_infiniteTorusFourier_jasCertificate_of_rh hRH]
  rw [heq]
  exact jasCertificate_mutuallySingular hσ0 hσ.le

/-- **No Haar density certifies positivity below `½`.**  For `0 < σ < ½` there is no finite
measure absolutely continuous with respect to Haar measure whose Fourier coefficients are the
dressed aggregate. -/
theorem not_exists_haar_absolutelyContinuous_jas_fourier {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1 / 2) :
    ¬ ∃ ν : Measure (Nat.Primes → UnitAddCircle), IsFiniteMeasure ν ∧
      ν ≪ torusHaar Nat.Primes ∧
      ∀ n, ∫ x, infiniteTorusFourier n x ∂ν = jasDressedLagAggregate σ n := by
  rintro ⟨ν, hfin, hac, hν⟩
  have hsing := mutuallySingular_torusHaar_of_jas_fourier hσ0 hσ ν hν
  have hzero : ν = 0 := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hac hsing
  have h0 := hν 0
  rw [hzero, integral_zero_measure, jasDressedLagAggregate_zero] at h0
  have h1 := congrArg Complex.re h0
  rw [Complex.zero_re, Complex.ofReal_re] at h1
  linarith [poleSharpConstant_pos]

end

end RHTower
