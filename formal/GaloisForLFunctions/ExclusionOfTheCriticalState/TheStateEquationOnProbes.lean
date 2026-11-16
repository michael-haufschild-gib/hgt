import GaloisForLFunctions.ExclusionOfTheCriticalState.WeilsFormOnProbesIsTheCaratheodoryKernelOfXi
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ExponentialBarrierPrimeEdges

/-!
# The critical state's equation on probes, in prime coordinates

Testing the weak equation of the critical state `F` on the probe `e_p` (`p > 4`) gives, with
`L F(c) = ∫ F(u) e^{cu} du`,

`a L F(p-8) + (1/2π) ∫ Re(F̂(r)/(p - ir)) γ(r) dr - L F(p) Σ Λ(n) n^{-½-p} - T F(p)
  + C(F)(1/(p+½) + 1/(p-½)) - S(F)(1/(p+½) - 1/(p-½)) = 0`,

where `T F(p) = Σ Λ(n) n^{-½} n^{p} ∫_{u<-log n} F(u) e^{pu} du` collects the backward prime
translates. Every term is an explicit transform of `F`; the Euler factor enters only through
`Σ Λ(n) n^{-½-p} = -ζ'/ζ(½+p)` multiplying `L F(p)`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-- The backward prime tail of a profile seen by the probe `e_p`. -/
def primeTail (F : ℝ → ℝ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    (Real.exp (p * Real.log n) * ∫ u in Iio (-Real.log n), F u * Real.exp (p * u))

/-- Forward prime translate of a probe against a half-line profile. -/
theorem integral_mul_probe_sub {F : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0) (p : ℝ) {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ t, F t * probe p (t - L)) = Real.exp (-(p * L)) * ∫ t, F t * Real.exp (p * t) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  rcases lt_or_ge t 0 with ht | ht
  · simp only [probe_of_neg (by linarith : t - L < 0)]
    rw [show p * (t - L) = -(p * L) + p * t by ring, Real.exp_add]
    ring
  · simp only [hF t ht, zero_mul, mul_zero]

/-- Backward prime translate of a probe against a half-line profile. -/
theorem integral_mul_probe_add (F : ℝ → ℝ) (p L : ℝ) :
    (∫ t, F t * probe p (t + L)) =
      Real.exp (p * L) * ∫ t in Iio (-L), F t * Real.exp (p * t) := by
  rw [← integral_const_mul, ← integral_indicator measurableSet_Iio]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rcases lt_or_ge t (-L) with ht | ht
  · rw [indicator_of_mem (Set.mem_Iio.mpr ht), probe_of_neg (by linarith : t + L < 0),
      show p * (t + L) = p * L + p * t by ring, Real.exp_add]
    ring
  · rw [indicator_of_notMem (fun h => (not_lt.mpr ht) (Set.mem_Iio.mp h)),
      probe_of_nonneg (by linarith : 0 ≤ t + L), mul_zero]

/-- One prime term of a half-line profile against a probe. -/
theorem primePairTerm_probe_right {F : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0) (p : ℝ) (n : ℕ) :
    primePairTerm F (probe p) n = vonMangoldtAtom n *
      (Real.exp (-(p * Real.log n)) * (∫ t, F t * Real.exp (p * t))) +
      vonMangoldtAtom n * (Real.exp (p * Real.log n) *
        ∫ t in Iio (-Real.log n), F t * Real.exp (p * t)) := by
  unfold primePairTerm
  rw [integral_mul_probe_sub hF p (Real.log_natCast_nonneg n), integral_mul_probe_add]
  ring

/-- The prime part against a probe: the Euler term `L F(p) Σ Λ(n) n^{-½-p}` plus the prime tail. -/
theorem primeMixedForm_probe_right {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℝ}
    (hp : 4 < p) :
    primeMixedForm F (probe p) = (∫ t, F t * Real.exp (p * t)) *
      (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p)) +
      primeTail F p := by
  have hsum := summable_primePairTerm hF.weighted (criticalHalfLineEnergyDomain_probe hp).weighted
  have hfirst : Summable fun n : ℕ => vonMangoldtAtom n *
      (Real.exp (-(p * Real.log n)) * (∫ t, F t * Real.exp (p * t))) := by
    have h := (summable_vonMangoldt_div_rpow (σ := 1 / 2 + p) (by linarith)).mul_right
      (∫ t, F t * Real.exp (p * t))
    refine h.congr fun n => ?_
    rw [← vonMangoldtAtom_mul_exp_eq]
    ring
  have htail : Summable fun n : ℕ => vonMangoldtAtom n * (Real.exp (p * Real.log n) *
      ∫ t in Iio (-Real.log n), F t * Real.exp (p * t)) := by
    refine (hsum.sub hfirst).congr fun n => ?_
    rw [primePairTerm_probe_right hF.support]
    ring
  unfold primeMixedForm primeTail
  simp_rw [primePairTerm_probe_right hF.support]
  rw [hfirst.tsum_add htail]
  congr 1
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [← vonMangoldtAtom_mul_exp_eq]
  ring

/-- The Gamma pairing against a probe is the real part of `F̂(r)/(p - ir)`. -/
theorem gammaFourierPair_probe_right (F : ℝ → ℝ) {p : ℝ} (hp : 0 < p) (r : ℝ) :
    gammaFourierPair F (probe p) r = (paperFT (cx F) r / ((p : ℂ) - I * r)).re := by
  unfold gammaFourierPair
  rw [paperFT_probe (z := (r : ℂ)) (by simpa using hp), re_one_div_probe, im_one_div_probe,
    Complex.div_re]
  have hN : Complex.normSq ((p : ℂ) - I * r) = p ^ 2 + r ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hre : ((p : ℂ) - I * r).re = p := by simp
  have him : ((p : ℂ) - I * r).im = -r := by simp
  rw [hN, hre, him]
  ring

/-- The pole part against a probe. -/
theorem polePart_probe_right (F : ℝ → ℝ) {p : ℝ} (hp : 1 / 2 < p) :
    2 * coshHalfMoment F * coshHalfMoment (probe p) -
        2 * sinhHalfMoment F * sinhHalfMoment (probe p) =
      coshHalfMoment F * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
        sinhHalfMoment F * (1 / (p + 1 / 2) - 1 / (p - 1 / 2)) := by
  rw [coshHalfMoment_probe hp, sinhHalfMoment_probe hp]
  ring

/-- **The state equation on probes.** At the window threshold the critical state satisfies, for
every `p > 4`, the closed-form identity of the module docstring. -/
theorem criticalState_probeEquation {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {p : ℝ} (hp : 4 < p) :
    criticalAliasCoefficient W₀ * (∫ u, F u * Real.exp ((p - 8) * u)) +
      1 / (2 * Real.pi) *
        (∫ r : ℝ, (paperFT (cx F) (r : ℂ) / ((p : ℂ) - I * r)).re * EF.gammaBracket r) -
      ((∫ t, F t * Real.exp (p * t)) *
        (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p)) +
        primeTail F p) +
      (coshHalfMoment F * (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) -
        sinhHalfMoment F * (1 / (p + 1 / 2) - 1 / (p - 1 / 2))) = 0 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have he := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF
    (criticalHalfLineEnergyDomain_probe hp)
  rw [criticalHalfLineMixedEnergy_eq_bare_add, confinement_probe_right hd.support] at he
  unfold bareMixedEnergy gammaMixedForm at he
  rw [primeMixedForm_symm (probe p) F, polePart_probe_right F (by linarith),
    primeMixedForm_probe_right hd hp] at he
  simp_rw [gammaFourierPair_probe_right F (by linarith : (0 : ℝ) < p)] at he
  linarith only [he]

end GaloisForLFunctions.ExclusionOfTheCriticalState
