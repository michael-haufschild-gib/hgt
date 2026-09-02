import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownLayerSourceScalar
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierSourceLargeSet
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSourceScale

/-!
# Source-scale Type-I receiver with exact layer sparsity saving

This module inserts the source-saving layer roots into the restricted Type-I receiver, then
constructs the paper's base, degree, threshold, support height, and source-large-set identity.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One Type-I block after exposing the exact source layer powers. -/
noncomputable def mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound
    (eta rho : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) *
    (mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound
        P ell N' (N * N) T eta rho +
      mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound
        P ell N' (2 * (N * N)) T eta rho) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Exact layer receiver bounded by its source-saving scalar form. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_source
    (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V eta rho : ℝ)
    (hP : 1 ≤ P) (hell : 0 < ell)
    (hdegree : (ell : ℝ) ≤ (P : ℝ) ^ rho)
    (hN : 2 ≤ N) (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hV : 0 < V) (heta : 0 < eta)
    (hfull : ((((2 * P) ^ ell : ℕ) : ℝ)) ≤ T) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ 2 *
          ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound
          eta rho a A P ell N N' T V r := by
  have hbase :=
    setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_of_fullSupport_le
      a A P ell N N' T V eta hP hell hN hNN' hN'le hT hV heta hfull
  let T' : Set.Ioi (0 : ℝ) := ⟨T, zero_lt_two.trans_le hT⟩
  calc
    _ ≤ ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownLayerBlockMomentBound
          eta a A P ell N N' T V r := hbase
    _ ≤ ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound
          eta rho a A P ell N N' T V r := by
      apply Finset.sum_le_sum
      intro r hr
      have hlow := mtTypeIPrimeRaisedHeathBrownLayerRootBound_le_source
        hP hdegree (by nlinarith : 1 ≤ N * N) N' T' heta r
      have hhigh := mtTypeIPrimeRaisedHeathBrownLayerRootBound_le_source
        hP hdegree (by nlinarith : 1 ≤ 2 * (N * N)) N' T' heta r
      have hsum := add_le_add hlow hhigh
      rw [mtTypeIPrimeHeathBrownLayerBlockMomentBound,
        mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound]
      dsimp only [T'] at hsum ⊢
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (by positivity)) (Real.sqrt_nonneg _)

/-- Literal Section-5.1 source receiver.  Base, degree, threshold, full support, and source-set
identity are all constructed internally. -/
theorem eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceScale :
    ∀ᶠ X : ℝ in atTop,
      ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (epsilon eta : ℝ),
      (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
      2 ≤ N → N < N' → N' ≤ 2 * N → 0 < eta →
      let P := mtTypeIPrimeScale X alpha
      let ell := mtTypeIPrimeDegree P T
      let V := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
      (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound
            eta (1 / alpha) a A P ell N N' T V r := by
  have hquarter :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 2
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 2)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards [eventually_mtTypeIPrimeScale_le_height_two_fifths,
    eventually_mtTypeIPrimeAmplifierLargeSet_sourceScale_eq,
    hquarter, hlog, hXlarge] with X hPT hset hquarterX hlogX hX
  intro alpha T a A N N' epsilon eta halpha halpha2 hXT hTX hN hNN' hN'le heta
  dsimp only
  let P := mtTypeIPrimeScale X alpha
  let ell := mtTypeIPrimeDegree P T
  let V : ℝ := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
  have halpha0 : 0 < alpha := by norm_num at halpha ⊢; linarith
  have halpha1 : (1 : ℝ) ≤ alpha := by norm_num at halpha ⊢; linarith
  have hlogOne : (1 : ℝ) ≤ Real.log X :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX
  have hscaleReal : Real.exp 2 ≤ (Real.log X) ^ alpha := by
    calc
      Real.exp 2 ≤ Real.log X := hlogX
      _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log X) ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hlogOne halpha1
  have hP : 2 ≤ P := by
    dsimp only [P]
    exact mtTypeIPrimeScale_two_le hscaleReal
  have hT : 2 ≤ T := hquarterX.trans hXT
  have hschedule := mtTypeIPrimeDegree_source_schedule
    halpha0 hX hscaleReal (by linarith : 1 < T) hTX
  have hell : 0 < ell := by simpa only [P, ell] using hschedule.1
  have hdegree : (ell : ℝ) ≤ (P : ℝ) ^ (1 / alpha) := by
    simpa only [P, ell] using hschedule.2.2.2
  have hheightScale : (P : ℝ) ≤ T ^ (2 / 5 : ℝ) := by
    dsimp only [P]
    exact hPT alpha T halpha1 halpha2 hXT
  have hfull : ((((2 * P) ^ ell : ℕ) : ℝ)) ≤ T := by
    simpa only [ell] using
      mtTypeIPrimeDegree_fullSupport_le_height hP (one_le_two.trans hT) hheightScale
  have hV : 0 < V := by
    dsimp only [V]
    have hpow : 0 < P ^ ell := pow_pos (by omega) _
    exact Real.rpow_pos_of_pos (by exact_mod_cast hpow) _
  have hbound := setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_source
    a A P ell N N' T V eta (1 / alpha) (one_le_two.trans hP) hell hdegree
      hN hNN' hN'le hT hV heta hfull
  have hsetEq := hset alpha T epsilon halpha hXT
  dsimp only [P, ell] at hsetEq
  rw [hsetEq.2.2] at hbound
  simpa only [P, ell, V] using hbound

end

end RHTower.Sieve
