import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattUnitSquareHeathBrown
import GaloisForLFunctions.RHTower.Sieve.SetIntegralBlockSplit

/-!
# Heath--Brown moment for the Matomäki--Teräväinen prime amplifier

This file applies the closed one-line form of Heath--Brown's Lemma 3.4 to the literal powered
prime amplifier and to each of the two dyadic pieces of the squared reciprocal unit block.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Exact right-hand side of Lemma 3.4 for one dyadic piece of the squared unit block. -/
def mtTypeIPrimeRaisedHeathBrownPieceBound
    (P ell B N N' K : ℕ) (T eta : ℝ) : ℝ :=
  heathBrownLemma34Coefficient eta *
    (heathBrownDenseCoefficientMax
      (mtWattPositiveDyadicInterval K)
      (mtWattUnitSquareRawCoeff N N')) ^ 2 *
    ((((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) / (B : ℝ)) ^ 2 +
      (((K : ℝ) * T) ^ eta) *
        (((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) * T /
            ((B : ℝ) ^ 2 * (K : ℝ)) +
          ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) ^ (7 / 4 : ℝ) *
            T ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))))

/-- Every restricted dense support inherits the complete divisor-scale coefficient bound. -/
theorem heathBrownDenseCoefficientMax_mtWattUnitSquareRawCoeff_le_divisorScale_of_finset
    (C : Finset PNat) (N : ℕ) {N' : ℕ} (hN' : 1 ≤ N')
    {eta : ℝ} (heta : 0 < eta) :
    heathBrownDenseCoefficientMax C (mtWattUnitSquareRawCoeff N N') ≤
      heathBrownSquareDivisorScale N' eta := by
  classical
  rw [heathBrownDenseCoefficientMax]
  split
  next hC =>
    apply Finset.sup'_le hC
    intro m hm
    exact abs_mtWattUnitSquareRawCoeff_le_divisorScale N hN' heta (m : ℕ)
  next =>
    exact zero_le_one.trans (one_le_heathBrownSquareDivisorScale hN' heta)

/-- One-piece Lemma 3.4 envelope with its dense maximum replaced by the closed divisor scale. -/
def mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
    (P ell B _N N' K : ℕ) (T eta : ℝ) : ℝ :=
  heathBrownLemma34Coefficient eta *
    (heathBrownSquareDivisorScale N' eta) ^ 2 *
    ((((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) / (B : ℝ)) ^ 2 +
      (((K : ℝ) * T) ^ eta) *
        (((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) * T /
            ((B : ℝ) ^ 2 * (K : ℝ)) +
          ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) ^ (7 / 4 : ℝ) *
            T ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ))))

theorem mtTypeIPrimeRaisedHeathBrownPieceBound_le_divisorPieceBound
    (P ell : ℕ) {B N N' K : ℕ} (hB : 1 ≤ B) (hN' : 1 ≤ N') (hK : 1 ≤ K)
    (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownPieceBound P ell B N N' K (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownDivisorPieceBound P ell B N N' K (T : ℝ) eta := by
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
      ((((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) / (B : ℝ)) ^ 2 +
        (((K : ℝ) * (T : ℝ)) ^ eta) *
          (((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) * (T : ℝ) /
              ((B : ℝ) ^ 2 * (K : ℝ)) +
            ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) ^ (7 / 4 : ℝ) *
              (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)))) := by
    have hden : 0 ≤ (B : ℝ) ^ 2 * (K : ℝ) := by positivity
    have hcard : 0 ≤ ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) := by
      positivity
    have hT0 : 0 ≤ (T : ℝ) := T.property.le
    have hfirst : 0 ≤
        ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) * (T : ℝ) /
          ((B : ℝ) ^ 2 * (K : ℝ)) := by
      exact div_nonneg (mul_nonneg (by positivity) T.property.le) hden
    have hsecond : 0 ≤
        ((mtTypeIPrimeRaisedBlockSupportPNat P ell B).card : ℝ) ^ (7 / 4 : ℝ) *
          (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) := by
      exact div_nonneg
        (mul_nonneg (Real.rpow_nonneg hcard _) (Real.rpow_nonneg hT0 _)) hden
    exact add_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) hT0) _)
        (add_nonneg hfirst hsecond))
  have hsquare :
      (heathBrownDenseCoefficientMax
        (mtWattPositiveDyadicInterval K) (mtWattUnitSquareRawCoeff N N')) ^ 2 ≤
        (heathBrownSquareDivisorScale N' eta) ^ 2 :=
    pow_le_pow_left₀ hmax0 hmax 2
  rw [mtTypeIPrimeRaisedHeathBrownPieceBound,
    mtTypeIPrimeRaisedHeathBrownDivisorPieceBound]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hsquare hscalar) hC

/-- Lemma 3.4 specialized to one literal prime-amplifier block and one dyadic product block. -/
theorem integral_Icc_normSq_mtTypeIPrimeRaised_heathBrownDyadic_le
    (P ell : ℕ) {B K : ℕ} (hB : 1 ≤ B) (hK : 2 ≤ K)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    (N N' : ℕ) {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseOneLineFactor
            (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
            (mtTypeIPrimeRaisedNormalizedCoeff P ell) t *
          heathBrownDenseOneLineFactor
            (mtWattPositiveDyadicInterval K)
            (mtWattUnitSquareRawCoeff N N') t‖ ^ 2) ≤
      mtTypeIPrimeRaisedHeathBrownPieceBound P ell B N N' K (T : ℝ) eta := by
  have hBreal : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hAM : ∀ m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B,
      (B : ℝ) ≤ ((m : ℕ) : ℝ) := by
    intro m hm
    exact_mod_cast (mtTypeIPrimeRaisedBlockSupportPNat_lower hm).le
  have heps : ∀ m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B,
      ‖mtTypeIPrimeRaisedNormalizedCoeff P ell (m : ℕ)‖ ≤ 1 := by
    intro m hm
    exact norm_mtTypeIPrimeRaisedNormalizedCoeff_le_one P ell (m : ℕ)
  have hMT : (B : ℝ) ≤ (T : ℝ) := by
    have hBnonneg : (0 : ℝ) ≤ (B : ℝ) := by positivity
    norm_num at hBT ⊢
    linarith
  have hAT : ∀ m ∈ mtTypeIPrimeRaisedBlockSupportPNat P ell B,
      ((m : ℕ) : ℝ) ≤ (T : ℝ) := by
    intro m hm
    have hmupper := mtTypeIPrimeRaisedBlockSupportPNat_upper hm
    exact (by exact_mod_cast hmupper : ((m : ℕ) : ℝ) ≤ ((2 * B : ℕ) : ℝ)).trans hBT
  have hBN : ∀ n ∈ mtWattPositiveDyadicInterval K, K < (n : ℕ) := by
    intro n hn
    exact (mem_mtWattPositiveDyadicInterval (by omega)).mp hn |>.1
  have hB2N : ∀ n ∈ mtWattPositiveDyadicInterval K, (n : ℕ) ≤ 2 * K := by
    intro n hn
    exact (mem_mtWattPositiveDyadicInterval (by omega)).mp hn |>.2
  simpa only [mtTypeIPrimeRaisedHeathBrownPieceBound] using
    integral_Icc_normSq_heathBrown_oneLine_le_lemma34
      (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
      (mtWattPositiveDyadicInterval K)
      (mtTypeIPrimeRaisedNormalizedCoeff P ell)
      (mtWattUnitSquareRawCoeff N N')
      hBreal hAM heps T hMT hAT hK hBN hB2N heta

/-- Exact two-piece Heath--Brown bound for the normalized powered-prime amplifier against the
square of the reciprocal unit block. -/
theorem integral_Icc_normSq_mtTypeIPrimeRaisedNormalized_mul_mtWattUnitBlock_sq_le
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseOneLineFactor
            (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
            (mtTypeIPrimeRaisedNormalizedCoeff P ell) t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      2 * mtTypeIPrimeRaisedHeathBrownPieceBound
          P ell B N N' (N * N) (T : ℝ) eta +
        2 * mtTypeIPrimeRaisedHeathBrownPieceBound
          P ell B N N' (2 * (N * N)) (T : ℝ) eta := by
  let A := mtTypeIPrimeRaisedBlockSupportPNat P ell B
  let eps := mtTypeIPrimeRaisedNormalizedCoeff P ell
  let a := mtWattUnitSquareRawCoeff N N'
  let low := mtWattPositiveDyadicInterval (N * N)
  let high := mtWattPositiveDyadicInterval (2 * (N * N))
  let S : ℝ → ℂ := fun t => heathBrownSparseOneLineFactor A eps t
  let Dlow : ℝ → ℂ := fun t => heathBrownDenseOneLineFactor low a t
  let Dhigh : ℝ → ℂ := fun t => heathBrownDenseOneLineFactor high a t
  let F : ℝ → ℂ := fun t => S t * Dlow t
  let G : ℝ → ℂ := fun t => S t * Dhigh t
  have hNN : 2 ≤ N * N := by
    have hmul := Nat.mul_le_mul hN (show 1 ≤ N by omega)
    simpa using hmul
  have htwoNN : 2 ≤ 2 * (N * N) := by omega
  have hS : Continuous S := continuous_heathBrownSparseOneLineFactor A eps
  have hDlow : Continuous Dlow := continuous_heathBrownDenseOneLineFactor low a
  have hDhigh : Continuous Dhigh := continuous_heathBrownDenseOneLineFactor high a
  have hF : Continuous F := hS.mul hDlow
  have hG : Continuous G := hS.mul hDhigh
  have hpoint : ∀ t : ℝ,
      S t * (mtWattUnitBlock N N' t) ^ 2 = F t + G t := by
    intro t
    rw [← heathBrownDenseOneLineFactor_mtWattUnitSquareRawCoeff_eq N hN' t,
      heathBrownDenseOneLineFactor_mtWattUnitSquareRawCoeff_eq_twoDyadic
        (by omega) hN' hN'le]
    dsimp only [F, G, S, Dlow, Dhigh, A, eps, a, low, high]
    ring
  have hsplit := setIntegral_normSq_add_le hF hG
    (E := Set.Icc (-(T : ℝ)) (T : ℝ)) measurableSet_Icc
    (W := (T : ℝ)) (by intro t ht; exact ht)
  have hlow := integral_Icc_normSq_mtTypeIPrimeRaised_heathBrownDyadic_le
    P ell hB hNN T hBT N N' heta
  have hhigh := integral_Icc_normSq_mtTypeIPrimeRaised_heathBrownDyadic_le
    P ell hB htwoNN T hBT N N' heta
  change (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
      ‖S t * (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤ _
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖S t * (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) =
        ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖F t + G t‖ ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpoint t)
    _ ≤ 2 * (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖F t‖ ^ 2) +
          2 * ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖G t‖ ^ 2 := hsplit
    _ ≤ 2 * mtTypeIPrimeRaisedHeathBrownPieceBound
          P ell B N N' (N * N) (T : ℝ) eta +
        2 * mtTypeIPrimeRaisedHeathBrownPieceBound
          P ell B N N' (2 * (N * N)) (T : ℝ) eta := by
      dsimp only [F, G, S, Dlow, Dhigh, A, eps, a, low, high] at hlow hhigh ⊢
      gcongr

/-- Literal unnormalized Watt moment.  The only normalization loss is the sharp `ell!` coefficient
bound, squared after taking the mean square. -/
theorem integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      (ell.factorial : ℝ) ^ 2 *
        (2 * mtTypeIPrimeRaisedHeathBrownPieceBound
            P ell B N N' (N * N) (T : ℝ) eta +
          2 * mtTypeIPrimeRaisedHeathBrownPieceBound
            P ell B N N' (2 * (N * N)) (T : ℝ) eta) := by
  let S : ℝ → ℂ := fun t => heathBrownSparseOneLineFactor
    (mtTypeIPrimeRaisedBlockSupportPNat P ell B)
    (mtTypeIPrimeRaisedNormalizedCoeff P ell) t
  let U : ℝ → ℂ := fun t => (mtWattUnitBlock N N' t) ^ 2
  let D : ℝ → ℂ := fun t =>
    mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t
  have hfac : (ell.factorial : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos ell).ne'
  have hpoint : ∀ t : ℝ, D t * U t = (ell.factorial : ℂ) * (S t * U t) := by
    intro t
    have hs := heathBrownSparseOneLineFactor_mtTypeIPrimeRaised_eq P ell B t
    dsimp only [S, U, D]
    rw [hs]
    calc
      mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          mtWattUnitBlock N N' t ^ 2 =
          (((ell.factorial : ℂ) * (ell.factorial : ℂ)⁻¹) *
            mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t) *
              mtWattUnitBlock N N' t ^ 2 := by
        rw [mul_inv_cancel₀ hfac, one_mul]
      _ = (ell.factorial : ℂ) *
          (((ell.factorial : ℂ)⁻¹ *
            mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t) *
              mtWattUnitBlock N N' t ^ 2) := by ring
  have hnormalized :=
    integral_Icc_normSq_mtTypeIPrimeRaisedNormalized_mul_mtWattUnitBlock_sq_le
      P ell hB hN hN' hN'le T hBT heta
  change (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖D t * U t‖ ^ 2) ≤ _
  change (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖S t * U t‖ ^ 2) ≤ _ at hnormalized
  calc
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖D t * U t‖ ^ 2) =
        (ell.factorial : ℝ) ^ 2 *
          ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖S t * U t‖ ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro t ht
      change ‖D t * U t‖ ^ 2 = (ell.factorial : ℝ) ^ 2 * ‖S t * U t‖ ^ 2
      rw [hpoint, norm_mul]
      norm_num
      ring
    _ ≤ (ell.factorial : ℝ) ^ 2 *
        (2 * mtTypeIPrimeRaisedHeathBrownPieceBound
            P ell B N N' (N * N) (T : ℝ) eta +
          2 * mtTypeIPrimeRaisedHeathBrownPieceBound
            P ell B N N' (2 * (N * N)) (T : ℝ) eta) :=
      mul_le_mul_of_nonneg_left hnormalized (sq_nonneg _)

/-- Source-facing moment bound with every dense coefficient maximum discharged by the divisor
estimate. -/
theorem integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_divisorScale
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      (ell.factorial : ℝ) ^ 2 *
        (2 * mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
            P ell B N N' (N * N) (T : ℝ) eta +
          2 * mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
            P ell B N N' (2 * (N * N)) (T : ℝ) eta) := by
  have hbase := integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le
    P ell hB hN hN' hN'le T hBT heta
  have hNNone : 1 ≤ N * N := by
    have hmul := Nat.mul_le_mul (show 1 ≤ N by omega) (show 1 ≤ N by omega)
    simpa using hmul
  have hlow := mtTypeIPrimeRaisedHeathBrownPieceBound_le_divisorPieceBound
    P ell (B := B) (N := N) (N' := N') (K := N * N) hB hN' hNNone T heta
  have hhigh := mtTypeIPrimeRaisedHeathBrownPieceBound_le_divisorPieceBound
    P ell (B := B) (N := N) (N' := N') (K := 2 * (N * N))
      hB hN' (by omega : 1 ≤ 2 * (N * N)) T heta
  calc
    _ ≤ (ell.factorial : ℝ) ^ 2 *
        (2 * mtTypeIPrimeRaisedHeathBrownPieceBound
            P ell B N N' (N * N) (T : ℝ) eta +
          2 * mtTypeIPrimeRaisedHeathBrownPieceBound
            P ell B N N' (2 * (N * N)) (T : ℝ) eta) := hbase
    _ ≤ (ell.factorial : ℝ) ^ 2 *
        (2 * mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
            P ell B N N' (N * N) (T : ℝ) eta +
          2 * mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
            P ell B N N' (2 * (N * N)) (T : ℝ) eta) := by
      gcongr

/-- Literal positive-height interval form consumed by the Type-I argument. -/
theorem intervalIntegral_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_divisorScale
    (P ell : ℕ) {B N N' : ℕ} (hB : 1 ≤ B) (hN : 2 ≤ N)
    (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N)
    (T : Set.Ioi (0 : ℝ)) (hBT : ((2 * B : ℕ) : ℝ) ≤ (T : ℝ))
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in ((T : ℝ) / 2)..(T : ℝ),
        ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
          (mtWattUnitBlock N N' t) ^ 2‖ ^ 2) ≤
      (ell.factorial : ℝ) ^ 2 *
        (2 * mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
            P ell B N N' (N * N) (T : ℝ) eta +
          2 * mtTypeIPrimeRaisedHeathBrownDivisorPieceBound
            P ell B N N' (2 * (N * N)) (T : ℝ) eta) := by
  let f : ℝ → ℝ := fun t =>
    ‖mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t *
      (mtWattUnitBlock N N' t) ^ 2‖ ^ 2
  have hcoeff : Continuous fun t : ℝ =>
      mtWattCoefficientBlock (mtTypeIPrimeRaisedCoeff P ell) B t := by
    have h := (continuous_dirPoly (2 * B)
      (mtWattDataCoeff (mtTypeIPrimeRaisedCoeff P ell) B)).comp continuous_neg
    convert h using 1
    funext t
    exact mtWattCoefficientBlock_eq_dirPoly
      (mtTypeIPrimeRaisedCoeff P ell) B t
  have hunit : Continuous fun t : ℝ => mtWattUnitBlock N N' t := by
    have h := (continuous_dirPoly N' (mtWattUnitCoeff N N')).comp continuous_neg
    convert h using 1
    funext t
    exact mtWattUnitBlock_eq_dirPoly N N' t
  have hf : Continuous f := ((hcoeff.mul (hunit.pow 2)).norm).pow 2
  have hsub : Set.Icc ((T : ℝ) / 2) (T : ℝ) ⊆
      Set.Icc (-(T : ℝ)) (T : ℝ) := by
    intro t ht
    constructor
    · have hT0 : 0 < (T : ℝ) := T.property
      linarith [ht.1]
    · exact ht.2
  have hmono :
      (∫ t in Set.Icc ((T : ℝ) / 2) (T : ℝ), f t) ≤
        ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), f t := by
    exact MeasureTheory.setIntegral_mono_set
      (hf.integrableOn_Icc (a := -(T : ℝ)) (b := (T : ℝ)))
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (Filter.Eventually.of_forall hsub)
  have hinterval :
      (∫ t in Set.Icc ((T : ℝ) / 2) (T : ℝ), f t) =
        ∫ t in ((T : ℝ) / 2)..(T : ℝ), f t := by
    rw [intervalIntegral.integral_of_le (by linarith [T.property]),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hsym :=
    integral_Icc_normSq_mtTypeIPrimeRaised_mul_mtWattUnitBlock_sq_le_divisorScale
      P ell hB hN hN' hN'le T hBT heta
  change (∫ t in ((T : ℝ) / 2)..(T : ℝ), f t) ≤ _
  rw [← hinterval]
  exact hmono.trans hsym

end

end RHTower.Sieve
