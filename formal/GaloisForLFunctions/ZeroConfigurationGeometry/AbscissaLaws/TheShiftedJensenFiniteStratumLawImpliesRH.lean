import GaloisForLFunctions.RHTower.Jensen.EveryFixedDegreeIsEventuallyRealRooted
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RigidArithmeticOfCuts.TheZeroOfMaximalAngle
import GaloisForLFunctions.HTGeometry.LaguerrePolyaJensenConverse

/-!
# The finite-stratum law for shifted Jensen polynomials

At each fixed degree, only finitely many shifts can fail real-rootedness.
A law excluding finite nonempty exceptional strata therefore forces every
unshifted Jensen polynomial to split. Their locally uniform limit is the
squared Xi function with its argument negated, with the exact Pólya
coefficient normalization. Hurwitz then gives RH.
-/

open Complex Filter Topology RHTower
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RigidArithmeticOfCuts

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws

/-- Even Cauchy coefficients of Xi are its signed theta moments. -/
theorem evenEntireBaseSeries_XiC_coeff (n : ℕ) :
    (evenEntireBaseSeries XiC).coeff (2 * n) =
      ((-1 : ℂ) ^ n * (thetaCuspRawEvenMoment n : ℂ)) / ((2 * n).factorial : ℂ) := by
  have hp := XiC_differentiable.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) (by norm_num)
  have hfac := hp.factorial_smul 1 (2 * n)
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul, iteratedDeriv_XiC_zero_eq_rawEvenMoment] at hfac
  apply (eq_div_iff (by exact_mod_cast (2 * n).factorial_ne_zero :
    ((2 * n).factorial : ℂ) ≠ 0)).mpr
  simpa only [evenEntireBaseSeries, FormalMultilinearSeries.coeff,
    nsmul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, mul_comm] using! hfac

/-- The exponential generating series of the Pólya coefficients is `Q(-w)`. -/
theorem hasSum_xiJensenCoeff_squaredXi (w : ℂ) :
    HasSum (fun n : ℕ => ((xiJensenCoeff n / (n.factorial : ℝ) : ℝ) : ℂ) * w ^ n)
      (squaredXi (-w)) := by
  let p := evenEntireSquareFactorSeries XiC
  have hr : p.radius = ⊤ := evenEntireSquareFactorSeries_radius_eq_top XiC_differentiable
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have hsum : HasSum (fun n => p n (fun _ => -w)) (p.sum (-w)) := by
    simpa only [zero_add] using hp.hasSum (y := -w) (by rw [hr]; simp)
  have hc : ∀ n : ℕ, ((xiJensenCoeff n / (n.factorial : ℝ) : ℝ) : ℂ) =
      (thetaCuspRawEvenMoment n : ℂ) / ((2 * n).factorial : ℂ) := by
    intro n
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [show xiJensenCoeff n / (n.factorial : ℝ) =
        thetaCuspRawEvenMoment n / ((2 * n).factorial : ℝ) by
      unfold xiJensenCoeff
      field_simp [hn]
      <;> ring]
    push_cast
  change HasSum _ (p.sum (-w))
  convert hsum using 1
  funext n
  symm
  rw [show p n (fun _ => -w) = (evenEntireBaseSeries XiC).coeff (2 * n) * (-w) ^ n by
    exact FormalMultilinearSeries.ofScalars_apply_eq _ _ _]
  rw [hc, evenEntireBaseSeries_XiC_coeff, neg_pow]
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  calc ((-1 : ℂ) ^ n * (thetaCuspRawEvenMoment n : ℂ)) /
        ((2 * n).factorial : ℂ) * ((-1 : ℂ) ^ n * w ^ n) =
      ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
        ((thetaCuspRawEvenMoment n : ℂ) / ((2 * n).factorial : ℂ) * w ^ n) := by ring
    _ = _ := by rw [hsign, one_mul]

/-- Real-rootedness of all unshifted Pólya Jensen polynomials implies RH. -/
theorem riemannHypothesis_of_splits_xiJensenPoly
    (hsplit : ∀ d : ℕ, (SignAlternation.jensenPoly xiJensenCoeff d 0).Splits) :
    RiemannHypothesis := by
  have hLP : LaguerrePolya (fun w : ℂ => squaredXi (-w)) :=
    laguerrePolya_of_splits_jensenPoly hasSum_xiJensenCoeff_squaredXi (fun d => by
      rw [jensenPoly_div_factorial]
      simpa only [SignAlternation.jensenPoly, zero_add] using hsplit d)
  have hzero : squaredXi (-(0 : ℂ)) ≠ 0 := by
    have hQ0 : squaredXi 0 = XiC 0 := by
      simpa only [zero_pow (by decide)] using squaredXi_sq (0 : ℂ)
    simpa only [neg_zero, hQ0] using XiC_zero_ne
  apply riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero.mpr
  intro q
  have hq : squaredXi (-(-zeroSq q)) = 0 := by
    rw [neg_neg, zeroSq, squaredXi_sq]
    exact XiC_xiSpectralPoint_eq_zero q
  have him := im_eq_zero_of_laguerrePolya hLP hzero hq
  have hreal : (zeroSq q).im = 0 := by simpa only [neg_im, neg_eq_zero] using him
  rw [zeroSq_im] at hreal
  exact (mul_eq_zero.mp hreal).resolve_left (mul_ne_zero two_ne_zero (spectral_re_ne_zero q))

/-- Every fixed-degree exceptional shift set is finite, unconditionally. -/
theorem finite_nonreal_xiJensen_shifts (d : ℕ) :
    {n : ℕ | ¬ (SignAlternation.jensenPoly xiJensenCoeff d n).Splits}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_splits_xiJensenPoly d)
  apply (Finset.range N).finite_toSet.subset
  intro n hn
  exact Finset.mem_range.mpr (lt_of_not_ge (fun h => hn (hN n h)))

/-- A finite-stratum exclusion law for every shifted Jensen degree implies RH. -/
theorem riemannHypothesis_of_shifted_jensen_finite_stratum_law
    (hlaw : ∀ d : ℕ,
      {n : ℕ | ¬ (SignAlternation.jensenPoly xiJensenCoeff d n).Splits}.Finite →
      ∀ n : ℕ, (SignAlternation.jensenPoly xiJensenCoeff d n).Splits) :
    RiemannHypothesis :=
  riemannHypothesis_of_splits_xiJensenPoly fun d => hlaw d (finite_nonreal_xiJensen_shifts d) 0

#print axioms hasSum_xiJensenCoeff_squaredXi
#print axioms riemannHypothesis_of_splits_xiJensenPoly
#print axioms finite_nonreal_xiJensen_shifts
#print axioms riemannHypothesis_of_shifted_jensen_finite_stratum_law

end GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws
