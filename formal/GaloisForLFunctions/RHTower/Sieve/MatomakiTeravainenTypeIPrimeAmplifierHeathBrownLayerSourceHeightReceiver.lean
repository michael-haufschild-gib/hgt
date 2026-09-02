import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownLayerSourceHeight

/-!
# Sub-height source receiver for the sharp Heath--Brown layers

This is the receiver-level substitution of the uniform source-height root.  It retains the exact
amplifier threshold and both negative source powers.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- One source Type-I block after both square-product roots are paid by height. -/
noncomputable def mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound
    (eta rho : ℝ) (a : ℕ → ℂ) (A P ell N : ℕ) (T V : ℝ)
    (_r : Fin ell) : ℝ :=
  ((ell : ℝ) / V) *
    (2 * mtTypeIPrimeRaisedHeathBrownLayerSourceHeightRootBound
      P ell N T eta rho) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- One exact source layer block is bounded by its sub-height form. -/
theorem mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound_le_height
    {P ell N N' : ℕ} (T : Set.Ioi (0 : ℝ)) {eta rho : ℝ}
    (a : ℕ → ℂ) (A : ℕ) (V : ℝ) (r : Fin ell)
    (hN : 2 ≤ N) (hN'le : N' ≤ 2 * N)
    (hNT : (N : ℝ) ≤ (T : ℝ)) (hT : 2 ≤ (T : ℝ))
    (hV : 0 < V) (heta : 0 < eta) :
    mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound
        eta rho a A P ell N N' (T : ℝ) V r ≤
      mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound
        eta rho a A P ell N (T : ℝ) V r := by
  have hroot := add_mtTypeIPrimeRaisedHeathBrownLayerSourceRootBound_le_height
    (P := P) (ell := ell) (eta := eta) (rho := rho) T hN hN'le hNT hT heta
  rw [mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound,
    mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hroot (div_nonneg (by positivity) hV.le))
    (Real.sqrt_nonneg _)

/-- Literal source-scale sub-height receiver with sharp layer sparsity and all source schedules
constructed internally. -/
theorem eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceHeight :
    ∀ᶠ X : ℝ in atTop,
      ∀ (alpha T : ℝ) (a : ℕ → ℂ) (A N N' : ℕ) (epsilon eta : ℝ),
      (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T → T ≤ X →
      2 ≤ N → (N : ℝ) ≤ T → N < N' → N' ≤ 2 * N → 0 < eta →
      let P := mtTypeIPrimeScale X alpha
      let ell := mtTypeIPrimeDegree P T
      let V := (((P ^ ell : ℕ) : ℝ)) ^ (-epsilon / 10)
      (∫ t in mtTypeIPrimeSourceLargeSet P T epsilon,
          ‖mtWattCoefficientBlock a A t‖ ^ 2 *
            ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
        ∑ r : Fin ell,
          mtTypeIPrimeHeathBrownLayerSourceHeightBlockMomentBound
            eta (1 / alpha) a A P ell N T V r := by
  filter_upwards
    [eventually_setIntegral_mtTypeI_primeAmplifier_heathBrown_layer_sourceScale,
      eventually_mtTypeIPrimeAmplifierLargeSet_sourceScale_eq]
      with X hsource hset
  intro alpha T a A N N' epsilon eta halpha halpha2 hXT hTX
    hN hNT hNN' hN'le heta
  dsimp only
  have hbase := hsource alpha T a A N N' epsilon eta
    halpha halpha2 hXT hTX hN hNN' hN'le heta
  have hT : 2 ≤ T := by
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    exact hNreal.trans hNT
  let T' : Set.Ioi (0 : ℝ) := ⟨T, zero_lt_two.trans_le hT⟩
  have hready := hset alpha T epsilon halpha hXT
  have hV : 0 < ((((mtTypeIPrimeScale X alpha ^
      mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
        (-epsilon / 10)) := by
    have hpow : 0 < mtTypeIPrimeScale X alpha ^
        mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T := pow_pos (by omega) _
    exact Real.rpow_pos_of_pos (by exact_mod_cast hpow) _
  calc
    _ ≤ ∑ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T),
        mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound
          eta (1 / alpha) a A (mtTypeIPrimeScale X alpha)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T) N N' T
            ((((mtTypeIPrimeScale X alpha ^
              mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
                (-epsilon / 10)) r := hbase
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownLayerSourceBlockMomentBound_le_height
        (P := mtTypeIPrimeScale X alpha)
        (ell := mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T)
        (N' := N') (eta := eta) (rho := 1 / alpha) T' a A
          ((((mtTypeIPrimeScale X alpha ^
            mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ^
              (-epsilon / 10)) r hN hN'le hNT hT hV heta

end

end RHTower.Sieve
