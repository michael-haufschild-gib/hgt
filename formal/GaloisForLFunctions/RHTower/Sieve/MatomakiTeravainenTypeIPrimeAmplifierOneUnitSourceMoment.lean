import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierOneUnitMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSourceScale

/-!
# Source schedule for the one-unit Type-I prime-amplifier receiver

This inserts equation (5.4) into the coefficient-energy-faithful one-unit receiver and constructs
the prime scale, raising degree, block-height comparison, and energy estimate uniformly on the
paper's source ranges.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Source-energy form of one powered-prime block in the one-unit receiver. -/
noncomputable def mtTypeIPrimeOneUnitSourceBlockMomentBound
    (C epsilon alpha : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (C * T ^ epsilon *
        (T + ((((2 * B) * N' : ℕ) : ℝ))) *
        (1 / (B : ℝ) ^ 2) *
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha) *
        (1 / (N : ℝ)) *
        (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Equation (5.4) removes the literal powered-prime block energy from the one-unit bound. -/
theorem mtTypeIPrimeOneUnitBlockMomentBound_le_source
    {C epsilon alpha T V : ℝ} {A P ell N N' : ℕ}
    (a : ℕ → ℂ) (r : Fin ell)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hV : 0 < V)
    (henergy : ∑ m ∈ Finset.Ioc (mtTypeIPrimeBlockLength P ell r)
          (2 * mtTypeIPrimeBlockLength P ell r),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 ≤
        (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha)) :
    mtTypeIPrimeOneUnitBlockMomentBound
        C epsilon a A P ell N N' T V r ≤
      mtTypeIPrimeOneUnitSourceBlockMomentBound
        C epsilon alpha a A P ell N N' T V r := by
  let B := mtTypeIPrimeBlockLength P ell r
  let Q : ℝ := C * T ^ epsilon * (T + ((((2 * B) * N' : ℕ) : ℝ))) *
    (1 / (B : ℝ) ^ 2)
  let R : ℝ := (1 / (N : ℝ)) *
    (Real.sqrt T / (N : ℝ) + 1 / Real.sqrt T) ^ 2
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hinside :
      Q * (∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) * R ≤
        Q * (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / alpha) * R := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by simpa only [B] using henergy) hQ) hR
  have hsqrt := Real.sqrt_le_sqrt hinside
  rw [mtTypeIPrimeOneUnitBlockMomentBound, mtTypeIPrimeOneUnitSourceBlockMomentBound]
  dsimp only [B, Q, R] at hsqrt ⊢
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hsqrt) (by positivity))
    (Real.sqrt_nonneg _)

/-- Complete source-scale sub-height one-unit receiver.  Prime scale, degree, every block height,
and every powered-prime energy bound are discharged internally. -/
theorem exists_eventually_setIntegral_mtTypeI_primeAmplifier_oneUnit_sourceScale
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (V : ℝ),
        (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
        1 ≤ A → 1 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N → 0 < V →
        let P := mtTypeIPrimeScale X alpha
        let ell := mtTypeIPrimeDegree P T
        (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
            ‖mtWattCoefficientBlock a A t‖ ^ 2 *
              ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
          ∑ r : Fin ell,
            mtTypeIPrimeOneUnitSourceBlockMomentBound
              C epsilon alpha a A P ell N N' T V r := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_setIntegral_mtTypeI_primeAmplifier_oneUnit hepsilon
  refine ⟨C, hC, ?_⟩
  have hquarter :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 2
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 2)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards [eventually_mtTypeIPrimeScale_two_le,
      eventually_mtTypeIPrimeScale_le_height_two_fifths,
      hquarter, hlog, hXlarge] with X hPsource hPTsource hquarterX hlogX hX
  intro alpha T a A N N' V halpha halpha2 hXT hTX hA hN hNT hNN' hN' hV
  dsimp only
  have halphaPos : 0 < alpha := by norm_num at halpha ⊢; linarith
  have halphaOne : (1 : ℝ) ≤ alpha := by norm_num at halpha ⊢; linarith
  have hlogOne : (1 : ℝ) ≤ Real.log X :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX
  have hscale : Real.exp 2 ≤ (Real.log X) ^ alpha := by
    calc
      Real.exp 2 ≤ Real.log X := hlogX
      _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log X) ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hlogOne halphaOne
  have hP : 2 ≤ mtTypeIPrimeScale X alpha := hPsource alpha halphaOne
  have hT : 2 ≤ T := hquarterX.trans hXT
  have hTgt : 1 < T := by linarith
  have hell : 0 < mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T :=
    mtTypeIPrimeDegree_pos hP hTgt
  have hfull := mtTypeIPrimeDegree_fullSupport_le_height hP
    (one_le_two.trans hT) (hPTsource alpha T halphaOne halpha2 hXT)
  have hblocks : ∀ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
      (mtTypeIPrimeBlockLength (mtTypeIPrimeScale X alpha)
        (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r : ℝ) ≤ T := by
    intro r
    have htwoNat :
        2 * mtTypeIPrimeBlockLength (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r ≤
          (2 * mtTypeIPrimeScale X alpha) ^
            mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T := by
      simpa only [mtTypeIPrimeBlockLength, mtTypeIPrimeHeathBrownBlockLength] using
        (two_mul_mtTypeIPrimeHeathBrownBlockLength_le
          (P := mtTypeIPrimeScale X alpha)
          (ell := mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r)
    have htwo :
        ((2 * mtTypeIPrimeBlockLength (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r : ℕ) : ℝ) ≤ T := by
      exact (by exact_mod_cast htwoNat :
        ((2 * mtTypeIPrimeBlockLength (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r : ℕ) : ℝ) ≤
          ((((2 * mtTypeIPrimeScale X alpha) ^
            mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ))).trans hfull
    have htwo' : 2 * (mtTypeIPrimeBlockLength (mtTypeIPrimeScale X alpha)
        (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r : ℝ) ≤ T := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using htwo
    nlinarith [show 0 ≤ (mtTypeIPrimeBlockLength (mtTypeIPrimeScale X alpha)
      (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r : ℝ) by positivity]
  have hraw := hbase a A (mtTypeIPrimeScale X alpha)
    (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V
    hA (one_le_two.trans hP) hell hN hNN' hN' hT hV hNT hblocks
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeOneUnitBlockMomentBound C epsilon a A
          (mtTypeIPrimeScale X alpha)
          (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T V r := hraw
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeOneUnitBlockMomentBound_le_source a r hC.le
        (zero_le_two.trans hT) hV
        (sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_source_schedule
          (mtTypeIPrimeBlockLength (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) r)
          halphaPos hX hscale hTgt hTX)

end

end RHTower.Sieve
