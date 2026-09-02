import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierLayerCake
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattUnitSquareHeathBrown
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownMoment
import GaloisForLFunctions.HTGeometry.WeightedHolder

/-!
# Coefficient-faithful Heath--Brown layer moment

The powered-prime coefficient is decomposed into unit threshold layers before Heath--Brown's
Lemma 3.4 is applied.  Finite `L²` Minkowski then recombines the layers.  This retains the exact
powered-block denominator and replaces the false global factorial normalization by controlled
sums of layer cardinalities.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- Lemma 3.4 divisor envelope for one unit threshold layer and one dense dyadic piece. -/
def mtTypeIPrimeRaisedHeathBrownLayerPieceBound
    (P ell B N' K j : ℕ) (T eta : ℝ) : ℝ :=
  heathBrownLemma34Coefficient eta *
    (heathBrownSquareDivisorScale N' eta) ^ 2 *
    ((((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) / (B : ℝ)) ^ 2 +
      (((K : ℝ) * T) ^ eta) *
        (((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) * T /
            ((B : ℝ) ^ 2 * (K : ℝ)) +
          ((mtTypeIPrimeRaisedBlockLayer P ell B j).card : ℝ) ^ (7 / 4 : ℝ) *
            T ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))))

/-- One unit threshold layer satisfies Lemma 3.4 with the closed divisor coefficient scale. -/
theorem integral_Icc_normSq_mtTypeIPrimeRaised_blockLayer_heathBrownDyadic_le
    (P ell j : ℕ) {B K : ℕ} (hB : 1 ≤ B) (hK : 2 ≤ K)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    (N N' : ℕ) (hN' : 1 ≤ N') {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseOneLineFactor
            (mtTypeIPrimeRaisedBlockLayer P ell B j) (fun _ => (1 : ℂ)) t *
          heathBrownDenseOneLineFactor
            (mtWattPositiveDyadicInterval K)
            (mtWattUnitSquareRawCoeff N N') t‖ ^ 2) ≤
      mtTypeIPrimeRaisedHeathBrownLayerPieceBound
        P ell B N' K j (T : ℝ) eta := by
  let A := mtTypeIPrimeRaisedBlockLayer P ell B j
  have hBreal : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hAM : ∀ m ∈ A, (B : ℝ) ≤ ((m : ℕ) : ℝ) := by
    intro m hm
    exact_mod_cast mtTypeIPrimeRaisedBlockSupportPNat_lower
      (mtTypeIPrimeRaisedBlockLayer_subset P ell B j hm) |>.le
  have heps : ∀ m ∈ A, ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hMT : (B : ℝ) ≤ (T : ℝ) := by
    have hB0 : (0 : ℝ) ≤ (B : ℝ) := by positivity
    norm_num at hBT ⊢
    linarith
  have hAT : ∀ m ∈ A, ((m : ℕ) : ℝ) ≤ (T : ℝ) := by
    intro m hm
    have hmupper := mtTypeIPrimeRaisedBlockLayer_upper hm
    exact (by exact_mod_cast hmupper : ((m : ℕ) : ℝ) ≤ ((2 * B : ℕ) : ℝ)).trans hBT
  have hBN : ∀ n ∈ mtWattPositiveDyadicInterval K, K < (n : ℕ) := by
    intro n hn
    exact (mem_mtWattPositiveDyadicInterval (by omega)).mp hn |>.1
  have hB2N : ∀ n ∈ mtWattPositiveDyadicInterval K, (n : ℕ) ≤ 2 * K := by
    intro n hn
    exact (mem_mtWattPositiveDyadicInterval (by omega)).mp hn |>.2
  have hbase := integral_Icc_normSq_heathBrown_oneLine_le_lemma34
    A (mtWattPositiveDyadicInterval K) (fun _ => (1 : ℂ))
      (mtWattUnitSquareRawCoeff N N') hBreal hAM heps T hMT hAT hK hBN hB2N heta
  have hmax :=
    heathBrownDenseCoefficientMax_mtWattUnitSquareRawCoeff_le_divisorScale_of_finset
      (mtWattPositiveDyadicInterval K) N hN' heta
  have hmax0 := heathBrownDenseCoefficientMax_nonneg
    (mtWattPositiveDyadicInterval K) (mtWattUnitSquareRawCoeff N N')
  have hC : 0 ≤ heathBrownLemma34Coefficient eta := by
    have hdiv : 0 < divisorBoundConst (eta / 4) :=
      divisorBoundConst_pos (by linarith)
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  have hscalar : 0 ≤
      ((((A.card : ℝ) / (B : ℝ)) ^ 2 + (((K : ℝ) * (T : ℝ)) ^ eta) *
        ((A.card : ℝ) * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
          (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
            ((B : ℝ) ^ 2 * (K : ℝ))))) := by
    have hden : 0 ≤ (B : ℝ) ^ 2 * (K : ℝ) := by positivity
    have hcard : 0 ≤ (A.card : ℝ) := by positivity
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) T.property.le) _)
        (add_nonneg
          (div_nonneg (mul_nonneg hcard T.property.le) hden)
          (div_nonneg
            (mul_nonneg (Real.rpow_nonneg hcard _)
              (Real.rpow_nonneg T.property.le _)) hden)))
  have hsquare :
      (heathBrownDenseCoefficientMax
        (mtWattPositiveDyadicInterval K) (mtWattUnitSquareRawCoeff N N')) ^ 2 ≤
        (heathBrownSquareDivisorScale N' eta) ^ 2 :=
    pow_le_pow_left₀ hmax0 hmax 2
  change _ ≤ heathBrownLemma34Coefficient eta *
    (heathBrownSquareDivisorScale N' eta) ^ 2 *
      ((((A.card : ℝ) / (B : ℝ)) ^ 2 + (((K : ℝ) * (T : ℝ)) ^ eta) *
        ((A.card : ℝ) * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) +
          (A.card : ℝ) ^ (7 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) /
            ((B : ℝ) ^ 2 * (K : ℝ)))))
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsquare hC) hscalar)

/-- Minkowski recombination of all coefficient layers for one dense dyadic piece. -/
theorem sqrt_integral_Icc_normSq_mtTypeIPrimeRaised_heathBrownDyadic_le_layerSum
    (P ell : ℕ) {B K : ℕ} (hB : 1 ≤ B) (hK : 2 ≤ K)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    (N N' : ℕ) (hN' : 1 ≤ N') {eta : ℝ} (heta : 0 < eta) :
    Real.sqrt (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          heathBrownDenseOneLineFactor
            (mtWattPositiveDyadicInterval K)
            (mtWattUnitSquareRawCoeff N N') t‖ ^ 2) ≤
      ∑ j ∈ Finset.range ell.factorial,
        Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
          P ell B N' K j (T : ℝ) eta) := by
  classical
  let g : ℕ → ℝ → ℂ := fun j t =>
    heathBrownSparseOneLineFactor
        (mtTypeIPrimeRaisedBlockLayer P ell B j) (fun _ => (1 : ℂ)) t *
      heathBrownDenseOneLineFactor
        (mtWattPositiveDyadicInterval K) (mtWattUnitSquareRawCoeff N N') t
  have hcont : ∀ j : ℕ, Continuous (g j) := by
    intro j
    exact (continuous_heathBrownSparseOneLineFactor _ _).mul
      (continuous_heathBrownDenseOneLineFactor _ _)
  have hmg : ∀ j ∈ Finset.range ell.factorial,
      AEStronglyMeasurable (g j)
        (volume.restrict (Set.Icc (-(T : ℝ)) (T : ℝ))) :=
    fun j _ => (hcont j).aestronglyMeasurable.restrict
  have hig : ∀ j ∈ Finset.range ell.factorial,
      Integrable (fun t => ‖g j t‖ ^ 2)
        (volume.restrict (Set.Icc (-(T : ℝ)) (T : ℝ))) :=
    fun j _ => ((hcont j).norm.pow 2).integrableOn_Icc
  have hpoint : ∀ t : ℝ,
      mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          heathBrownDenseOneLineFactor
            (mtWattPositiveDyadicInterval K)
            (mtWattUnitSquareRawCoeff N N') t =
        ∑ j ∈ Finset.range ell.factorial, g j t := by
    intro t
    rw [← heathBrownSparseOneLineFactor_mtTypeIPrimeRaised_unnormalized_eq]
    rw [← sum_heathBrownSparseOneLineFactor_blockLayer_eq]
    rw [Finset.sum_mul]
  have hminkowski :=
    GaloisForLFunctions.HTGeometry.sqrt_integral_normSq_sum_le_measure
      (Finset.range ell.factorial) g hmg hig
  rw [setIntegral_congr_fun measurableSet_Icc
    (fun t _ht => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpoint t))]
  refine hminkowski.trans (Finset.sum_le_sum fun j hj => ?_)
  exact Real.sqrt_le_sqrt
    (integral_Icc_normSq_mtTypeIPrimeRaised_blockLayer_heathBrownDyadic_le
      P ell j hB hK T hBT N N' hN' heta)

/-- Full squared-unit-block root moment with exact layer sums for both dyadic pieces. -/
theorem sqrt_integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_layerSums
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    Real.sqrt (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      (∑ j ∈ Finset.range ell.factorial,
        Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
          P ell B N' (N * N) j (T : ℝ) eta)) +
      ∑ j ∈ Finset.range ell.factorial,
        Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
          P ell B N' (2 * (N * N)) j (T : ℝ) eta) := by
  classical
  let S : ℝ → ℂ := fun t =>
    mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t
  let Dlow : ℝ → ℂ := fun t => heathBrownDenseOneLineFactor
    (mtWattPositiveDyadicInterval (N * N)) (mtWattUnitSquareRawCoeff N N') t
  let Dhigh : ℝ → ℂ := fun t => heathBrownDenseOneLineFactor
    (mtWattPositiveDyadicInterval (2 * (N * N))) (mtWattUnitSquareRawCoeff N N') t
  let F : ℝ → ℂ := fun t => S t * Dlow t
  let G : ℝ → ℂ := fun t => S t * Dhigh t
  have hNN : 2 ≤ N * N := by nlinarith
  have htwoNN : 2 ≤ 2 * (N * N) := by omega
  have hS : Continuous S := by
    have hSeq : S = heathBrownSparseOneLineFactor
        (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
        (mtTypeIPrimeRaisedCoeff P ell) := by
      funext t
      exact (heathBrownSparseOneLineFactor_mtTypeIPrimeRaised_unnormalized_eq
        P ell B t).symm
    rw [hSeq]
    exact continuous_heathBrownSparseOneLineFactor _ _
  have hDlow : Continuous Dlow := continuous_heathBrownDenseOneLineFactor _ _
  have hDhigh : Continuous Dhigh := continuous_heathBrownDenseOneLineFactor _ _
  have hF : Continuous F := hS.mul hDlow
  have hG : Continuous G := hS.mul hDhigh
  have hpoint : ∀ t : ℝ,
      S t * (mtWattUnitBlock N N' t) ^ 2 = F t + G t := by
    intro t
    rw [← heathBrownDenseOneLineFactor_mtWattUnitSquareRawCoeff_eq N hN' t,
      heathBrownDenseOneLineFactor_mtWattUnitSquareRawCoeff_eq_twoDyadic
        (by omega) hN' hN'le]
    dsimp only [F, G, Dlow, Dhigh]
    ring
  have hmeasF : AEStronglyMeasurable F
      (volume.restrict (Set.Icc (-(T : ℝ)) (T : ℝ))) :=
    hF.aestronglyMeasurable.restrict
  have hmeasG : AEStronglyMeasurable G
      (volume.restrict (Set.Icc (-(T : ℝ)) (T : ℝ))) :=
    hG.aestronglyMeasurable.restrict
  have hintF : Integrable (fun t => ‖F t‖ ^ 2)
      (volume.restrict (Set.Icc (-(T : ℝ)) (T : ℝ))) :=
    (hF.norm.pow 2).integrableOn_Icc
  have hintG : Integrable (fun t => ‖G t‖ ^ 2)
      (volume.restrict (Set.Icc (-(T : ℝ)) (T : ℝ))) :=
    (hG.norm.pow 2).integrableOn_Icc
  have hminkowski := GaloisForLFunctions.HTGeometry.sqrt_integral_normSq_add_le_measure
    hmeasF hmeasG hintF hintG
  have hlow :=
    sqrt_integral_Icc_normSq_mtTypeIPrimeRaised_heathBrownDyadic_le_layerSum
      P ell hB hNN T hBT N N' hN' heta
  have hhigh :=
    sqrt_integral_Icc_normSq_mtTypeIPrimeRaised_heathBrownDyadic_le_layerSum
      P ell hB htwoNN T hBT N N' hN' heta
  change Real.sqrt (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
      ‖S t * (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤ _
  rw [setIntegral_congr_fun measurableSet_Icc
    (fun t _ht => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpoint t))]
  dsimp only [F, G, S, Dlow, Dhigh] at hminkowski hlow hhigh ⊢
  linarith

/-- Squared form of the exact layer-sum moment. -/
theorem integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_layerSums_sq
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      ((∑ j ∈ Finset.range ell.factorial,
          Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
            P ell B N' (N * N) j (T : ℝ) eta)) +
        ∑ j ∈ Finset.range ell.factorial,
          Real.sqrt (mtTypeIPrimeRaisedHeathBrownLayerPieceBound
            P ell B N' (2 * (N * N)) j (T : ℝ) eta)) ^ 2 := by
  have hroot :=
    sqrt_integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_layerSums
      P ell hB hN hN' hN'le T hBT heta
  have hint0 : 0 ≤ (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
      ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
        (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) :=
    integral_nonneg fun _ => sq_nonneg _
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rw [Real.sq_sqrt hint0] at hsquare
  exact hsquare

end

end RHTower.Sieve
