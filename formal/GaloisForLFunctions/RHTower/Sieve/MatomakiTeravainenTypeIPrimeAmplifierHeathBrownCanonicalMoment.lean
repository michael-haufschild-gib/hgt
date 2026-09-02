import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownSqrtBTMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSchedule

/-!
# Canonical Type-I receiver from the powered-prime Heath--Brown moment

This module links the Type-I receiver to the square-root Brun--Titchmarsh coefficient.  It removes
the last exact support statistic from the receiver by monotonicity, without repeating its analytic
proof.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory

noncomputable section

/-- Exact energy coefficient is bounded by the canonical square-root Brun--Titchmarsh one. -/
theorem mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient_le_sqrt_bt
    (P ell : ℕ) {B N N' : ℕ} (hP : 2 ≤ P) (hB : 1 ≤ B) (hN : 2 ≤ N)
    (T : Set.Ioi (0 : ℝ)) {eta : ℝ} (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient
        P ell B N N' (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient
        P ell B N N' (T : ℝ) eta := by
  have hPR : (1 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hsqrt : (1 : ℝ) < Real.sqrt (P : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hPR
  exact (mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient_le_bt
    P ell (N' := N') hB hN T heta hsqrt).trans
      (mtTypeIPrimeRaisedHeathBrownBTMomentCoefficient_sqrt_le
        P ell (N' := N') hP hB hN T heta)

/-- Canonical support-free Type-I bound charged to one powered-prime block. -/
noncomputable def mtTypeIPrimeHeathBrownCanonicalBlockMomentBound
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient
          P ell B N N' T eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2)) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- The exact-support block bound is dominated by the canonical support-free block bound. -/
theorem mtTypeIPrimeHeathBrownBlockMomentBound_le_canonical
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) (hP : 2 ≤ P) (hN : 2 ≤ N) (hT : 0 < T)
    (hV : 0 < V) (heta : 0 < eta) :
    mtTypeIPrimeHeathBrownBlockMomentBound eta a A P ell N N' T V r ≤
      mtTypeIPrimeHeathBrownCanonicalBlockMomentBound eta a A P ell N N' T V r := by
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  have hB : 1 ≤ B := by
    have hBpos : 0 < B := by
      dsimp only [B, mtTypeIPrimeHeathBrownBlockLength]
      positivity
    omega
  let T' : Set.Ioi (0 : ℝ) := ⟨T, hT⟩
  have hcoeff := mtTypeIPrimeRaisedHeathBrownEnergyMomentCoefficient_le_sqrt_bt
    P ell (N' := N') hP hB hN T' heta
  have henergy : 0 ≤ ∑ m ∈ Finset.Ioc B (2 * B),
      ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hinside := mul_le_mul_of_nonneg_right hcoeff henergy
  have hsqrt := Real.sqrt_le_sqrt hinside
  rw [mtTypeIPrimeHeathBrownBlockMomentBound,
    mtTypeIPrimeHeathBrownCanonicalBlockMomentBound]
  dsimp only [B, T'] at hsqrt ⊢
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (Real.sqrt_nonneg _)

/-- Type-I receiver with all analytic and support-statistic hypotheses discharged. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_canonical
    (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V eta : ℝ)
    (hP : 2 ≤ P) (hell : 0 < ell) (hN : 2 ≤ N)
    (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hV : 0 < V) (heta : 0 < eta)
    (hfull : ((((2 * P) ^ ell : ℕ) : ℝ)) ≤ T) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ 2 *
          ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownCanonicalBlockMomentBound
          eta a A P ell N N' T V r := by
  calc
    _ ≤ ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownBlockMomentBound eta a A P ell N N' T V r :=
      setIntegral_mtTypeI_primeAmplifier_heathBrown_of_fullSupport_le
        a A P ell N N' T V eta (one_le_two.trans hP) hell hN hNN' hN'le
          hT hV heta hfull
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownBlockMomentBound_le_canonical
        eta a A P ell N N' T V r hP hN (by linarith) hV heta

/-- Canonical source-degree receiver, with block height discharged by the Section 5.1 schedule. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_canonical_sourceDegree
    (a : ℕ → ℂ) (A P N N' : ℕ) (T V eta : ℝ)
    (hP : 2 ≤ P) (hN : 2 ≤ N) (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hPT : (P : ℝ) ≤ T ^ (2 / 5 : ℝ))
    (hV : 0 < V) (heta : 0 < eta) :
    let ell := mtTypeIPrimeDegree P T
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ 2 *
          ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownCanonicalBlockMomentBound
          eta a A P ell N N' T V r := by
  dsimp only
  apply setIntegral_mtTypeI_primeAmplifier_heathBrown_canonical
    a A P (mtTypeIPrimeDegree P T) N N' T V eta hP
      (mtTypeIPrimeDegree_pos hP (by linarith)) hN hNN' hN'le hT hV heta
  exact mtTypeIPrimeDegree_fullSupport_le_height hP (one_le_two.trans hT) hPT

/-- Elementary upper bound for a natural factorial. -/
theorem nat_factorial_le_self_pow (n : ℕ) : n.factorial ≤ n ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (n + 1).factorial = (n + 1) * n.factorial := by rw [Nat.factorial_succ]
        _ ≤ (n + 1) * n ^ n := Nat.mul_le_mul_left _ ih
        _ ≤ (n + 1) * (n + 1) ^ n :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ n) n)
        _ = (n + 1) ^ (n + 1) := by rw [pow_succ]; ring

/-- Named canonical Brun--Titchmarsh base. -/
def mtTypeIPrimeSqrtBTBase (P ell : ℕ) : ℝ :=
  292 * (P : ℝ) / Real.log P + 1 + ell

/-- Once `log P ≥ 1` and the degree is at most `P`, the canonical base is at most `294P`. -/
theorem mtTypeIPrimeSqrtBTBase_le_mul
    {P ell : ℕ} (hP : 1 ≤ P) (hlogP : 1 ≤ Real.log (P : ℝ))
    (hellP : ell ≤ P) :
    mtTypeIPrimeSqrtBTBase P ell ≤ 294 * (P : ℝ) := by
  have hPR : (0 : ℝ) ≤ P := by positivity
  have hPone : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hlogPos : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlogP
  have hdiv : (P : ℝ) / Real.log P ≤ (P : ℝ) := by
    rw [div_le_iff₀ hlogPos]
    nlinarith
  have hdiv292 : (292 : ℝ) * ((P : ℝ) / Real.log P) ≤ 292 * (P : ℝ) :=
    mul_le_mul_of_nonneg_left hdiv (by norm_num)
  have hellR : (ell : ℝ) ≤ (P : ℝ) := by exact_mod_cast hellP
  rw [mtTypeIPrimeSqrtBTBase]
  calc
    292 * (P : ℝ) / Real.log P + 1 + ell ≤
        292 * (P : ℝ) + 1 + ell := by
          rw [mul_div_assoc]
          linarith
    _ ≤ 294 * (P : ℝ) := by nlinarith

/-- The factorial-weighted canonical support numerator is at most `B²` once the source degree has
the fixed linear deficit `294 ell ≤ P`. -/
theorem factorial_mul_mtTypeIPrimeSqrtBTBase_pow_le_sq
    {P ell B : ℕ} (hP : 1 ≤ P) (hlogP : 1 ≤ Real.log (P : ℝ))
    (hdegree : 294 * ell ≤ P) (hB : P ^ ell ≤ B) :
    (ell.factorial : ℝ) * mtTypeIPrimeSqrtBTBase P ell ^ ell ≤ (B : ℝ) ^ 2 := by
  have hellP : ell ≤ P := by omega
  have hQ := mtTypeIPrimeSqrtBTBase_le_mul hP hlogP hellP
  have hQ0 : 0 ≤ mtTypeIPrimeSqrtBTBase P ell := by
    rw [mtTypeIPrimeSqrtBTBase]
    have hlogPos : 0 < Real.log (P : ℝ) := zero_lt_one.trans_le hlogP
    positivity
  have hfacNat := nat_factorial_le_self_pow ell
  have hfac : (ell.factorial : ℝ) ≤ (ell : ℝ) ^ ell := by exact_mod_cast hfacNat
  have hdegreeR : (294 : ℝ) * ell ≤ P := by exact_mod_cast hdegree
  have hlin : (ell : ℝ) * mtTypeIPrimeSqrtBTBase P ell ≤ (P : ℝ) ^ 2 := by
    calc
      (ell : ℝ) * mtTypeIPrimeSqrtBTBase P ell ≤
          (ell : ℝ) * (294 * (P : ℝ)) := by gcongr
      _ ≤ (P : ℝ) * (P : ℝ) := by nlinarith
      _ = (P : ℝ) ^ 2 := by ring
  have hpow : ((ell : ℝ) * mtTypeIPrimeSqrtBTBase P ell) ^ ell ≤
      ((P : ℝ) ^ 2) ^ ell := pow_le_pow_left₀ (by positivity) hlin ell
  have hBreal : (((P ^ ell : ℕ) : ℝ)) ≤ (B : ℝ) := by exact_mod_cast hB
  calc
    (ell.factorial : ℝ) * mtTypeIPrimeSqrtBTBase P ell ^ ell ≤
        (ell : ℝ) ^ ell * mtTypeIPrimeSqrtBTBase P ell ^ ell := by gcongr
    _ = ((ell : ℝ) * mtTypeIPrimeSqrtBTBase P ell) ^ ell := by rw [mul_pow]
    _ ≤ ((P : ℝ) ^ 2) ^ ell := hpow
    _ = (((P ^ ell : ℕ) : ℝ)) ^ 2 := by
      push_cast
      ring
    _ ≤ (B : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hBreal 2

/-- Divided form of the canonical numerator absorption. -/
theorem factorial_mul_mtTypeIPrimeSqrtBTBase_pow_div_sq_le_one
    {P ell B : ℕ} (hP : 1 ≤ P) (hlogP : 1 ≤ Real.log (P : ℝ))
    (hdegree : 294 * ell ≤ P) (hB : P ^ ell ≤ B) :
    (ell.factorial : ℝ) * mtTypeIPrimeSqrtBTBase P ell ^ ell / (B : ℝ) ^ 2 ≤ 1 := by
  have hBpos : (0 : ℝ) < B := by
    have hPpos : 0 < P := lt_of_lt_of_le Nat.zero_lt_one hP
    have : 0 < P ^ ell := pow_pos hPpos ell
    exact_mod_cast this.trans_le hB
  rw [div_le_one (by positivity)]
  exact factorial_mul_mtTypeIPrimeSqrtBTBase_pow_le_sq hP hlogP hdegree hB

/-- The squared factorial normalization is at most one on every powered-prime block. -/
theorem factorial_sq_div_block_sq_le_one
    {P ell B : ℕ} (hP : 1 ≤ P) (hellP : ell ≤ P) (hB : P ^ ell ≤ B) :
    (ell.factorial : ℝ) ^ 2 / (B : ℝ) ^ 2 ≤ 1 := by
  have hfacNat := nat_factorial_le_self_pow ell
  have hellPow : ell ^ ell ≤ P ^ ell := Nat.pow_le_pow_left hellP ell
  have hfacB : ell.factorial ≤ B := hfacNat.trans (hellPow.trans hB)
  have hBpos : (0 : ℝ) < B := by
    have hPpos : 0 < P := lt_of_lt_of_le Nat.zero_lt_one hP
    have : 0 < P ^ ell := pow_pos hPpos ell
    exact_mod_cast this.trans_le hB
  rw [div_le_one (by positivity)]
  exact_mod_cast (Nat.pow_le_pow_left hfacB 2)

/-- One-piece coefficient after all factorial and Brun--Titchmarsh numerators are absorbed. -/
def mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient
    (N' K B : ℕ) (T eta : ℝ) : ℝ :=
  heathBrownLemma34Coefficient eta *
    (heathBrownSquareDivisorScale N' eta) ^ 2 *
    (1 + (((K : ℝ) * T) ^ eta) *
      (T / (K : ℝ) + (B : ℝ) ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) / (K : ℝ)))

/-- Source degree reserve removes every factorial and canonical-base quotient from one piece. -/
theorem mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient_le_absorbed
    {P ell B N' K : ℕ} (T : Set.Ioi (0 : ℝ)) {eta : ℝ}
    (hP : 1 ≤ P) (hlogP : 1 ≤ Real.log (P : ℝ))
    (hdegree : 294 * ell ≤ P) (hB : P ^ ell ≤ B) (hK : 1 ≤ K)
    (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient
        P ell B N' K (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient
        N' K B (T : ℝ) eta := by
  have hellP : ell ≤ P := by omega
  have hfirst := factorial_mul_mtTypeIPrimeSqrtBTBase_pow_div_sq_le_one
    hP hlogP hdegree hB
  have hfac := factorial_sq_div_block_sq_le_one hP hellP hB
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hT0 : (0 : ℝ) ≤ T := T.property.le
  have hterm1 : (ell.factorial : ℝ) ^ 2 * (T : ℝ) /
      ((B : ℝ) ^ 2 * (K : ℝ)) ≤ (T : ℝ) / (K : ℝ) := by
    calc
      (ell.factorial : ℝ) ^ 2 * (T : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) =
          ((ell.factorial : ℝ) ^ 2 / (B : ℝ) ^ 2) * ((T : ℝ) / K) := by ring
      _ ≤ 1 * ((T : ℝ) / K) := by gcongr
      _ = (T : ℝ) / K := one_mul _
  have hterm2 : (ell.factorial : ℝ) ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) *
      (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) ≤
      (B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / (K : ℝ) := by
    calc
      (ell.factorial : ℝ) ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) *
          (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)) =
          ((ell.factorial : ℝ) ^ 2 / (B : ℝ) ^ 2) *
            ((B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / K) := by ring
      _ ≤ 1 * ((B : ℝ) ^ (3 / 4 : ℝ) * (T : ℝ) ^ (3 / 4 : ℝ) / K) := by
        gcongr
      _ = _ := one_mul _
  have hpowKT : 0 ≤ ((K : ℝ) * (T : ℝ)) ^ eta :=
    Real.rpow_nonneg (mul_nonneg (by positivity) hT0) _
  have hC : 0 ≤ heathBrownLemma34Coefficient eta := by
    have hdiv : 0 < divisorBoundConst (eta / 4) :=
      divisorBoundConst_pos (by linarith)
    rw [heathBrownLemma34Coefficient, heathBrownLemma34PositiveCoefficient,
      heathBrownTheoremFourCoefficient, heathBrownTheoremFourUniversalCoefficient,
      heathBrownMeanSquareCoefficient]
    positivity
  rw [mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient,
    mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient]
  change heathBrownLemma34Coefficient eta *
      (heathBrownSquareDivisorScale N' eta) ^ 2 *
        ((ell.factorial : ℝ) * mtTypeIPrimeSqrtBTBase P ell ^ ell / (B : ℝ) ^ 2 +
          (((K : ℝ) * (T : ℝ)) ^ eta) *
            ((ell.factorial : ℝ) ^ 2 * (T : ℝ) /
                ((B : ℝ) ^ 2 * (K : ℝ)) +
              (ell.factorial : ℝ) ^ 2 * (B : ℝ) ^ (3 / 4 : ℝ) *
                (T : ℝ) ^ (3 / 4 : ℝ) / ((B : ℝ) ^ 2 * (K : ℝ)))) ≤ _
  gcongr

/-- Combined factorial-free coefficient for both unit-square dyadic pieces. -/
def mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient
    (N N' B : ℕ) (T eta : ℝ) : ℝ :=
  2 * mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient N' (N * N) B T eta +
    2 * mtTypeIPrimeRaisedHeathBrownAbsorbedPieceCoefficient
      N' (2 * (N * N)) B T eta

/-- Canonical two-piece coefficient is bounded by its factorial-free form. -/
theorem mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient_le_absorbed
    {P ell B N N' : ℕ} (T : Set.Ioi (0 : ℝ)) {eta : ℝ}
    (hP : 1 ≤ P) (hlogP : 1 ≤ Real.log (P : ℝ))
    (hdegree : 294 * ell ≤ P) (hB : P ^ ell ≤ B) (hN : 1 ≤ N)
    (heta : 0 < eta) :
    mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient P ell B N N' (T : ℝ) eta ≤
      mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient N N' B (T : ℝ) eta := by
  have hKlow : 1 ≤ N * N := Nat.mul_le_mul hN hN
  have hKhigh : 1 ≤ 2 * (N * N) := by omega
  have hlow := mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient_le_absorbed
    (N' := N') T hP hlogP hdegree hB hKlow heta
  have hhigh := mtTypeIPrimeRaisedHeathBrownSqrtBTPieceCoefficient_le_absorbed
    (N' := N') T hP hlogP hdegree hB hKhigh heta
  rw [mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient,
    mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient]
  gcongr

/-- Factorial-free Type-I bound charged to one powered-prime block. -/
noncomputable def mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) : ℝ :=
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  ((ell : ℝ) / V) * Real.sqrt
      (mtTypeIPrimeRaisedHeathBrownAbsorbedMomentCoefficient N N' B T eta *
        (∑ m ∈ Finset.Ioc B (2 * B),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2)) *
    Real.sqrt
      (generalMeanSquareConst (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 +
        generalMeanSquareRate (fun n => mtTypeILongSquareAF a A n)
          (Finset.Icc 1 ((2 * A) * (2 * A))) 1 * T)

/-- Canonical block bound is dominated by its factorial-free form. -/
theorem mtTypeIPrimeHeathBrownCanonicalBlockMomentBound_le_absorbed
    (eta : ℝ) (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V : ℝ)
    (r : Fin ell) (hP : 1 ≤ P) (hlogP : 1 ≤ Real.log (P : ℝ))
    (hdegree : 294 * ell ≤ P) (hN : 1 ≤ N) (hT : 0 < T)
    (hV : 0 < V) (heta : 0 < eta) :
    mtTypeIPrimeHeathBrownCanonicalBlockMomentBound eta a A P ell N N' T V r ≤
      mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound eta a A P ell N N' T V r := by
  let B := mtTypeIPrimeHeathBrownBlockLength P ell r
  have hB : P ^ ell ≤ B := by
    dsimp only [B, mtTypeIPrimeHeathBrownBlockLength]
    have hr : 1 ≤ 2 ^ (r : ℕ) := one_le_pow₀ (by norm_num)
    simpa using Nat.mul_le_mul_left (P ^ ell) hr
  let T' : Set.Ioi (0 : ℝ) := ⟨T, hT⟩
  have hcoeff := mtTypeIPrimeRaisedHeathBrownSqrtBTMomentCoefficient_le_absorbed
    (N' := N') T' hP hlogP hdegree hB hN heta
  have henergy : 0 ≤ ∑ m ∈ Finset.Ioc B (2 * B),
      ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hinside := mul_le_mul_of_nonneg_right hcoeff henergy
  have hsqrt := Real.sqrt_le_sqrt hinside
  rw [mtTypeIPrimeHeathBrownCanonicalBlockMomentBound,
    mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound]
  dsimp only [B, T'] at hsqrt ⊢
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (Real.sqrt_nonneg _)

/-- Type-I receiver after complete factorial and canonical-base absorption. -/
theorem setIntegral_mtTypeI_primeAmplifier_heathBrown_absorbed
    (a : ℕ → ℂ) (A P ell N N' : ℕ) (T V eta : ℝ)
    (hP : 2 ≤ P) (hlogP : 1 ≤ Real.log (P : ℝ))
    (hdegree : 294 * ell ≤ P) (hell : 0 < ell) (hN : 2 ≤ N)
    (hNN' : N < N') (hN'le : N' ≤ 2 * N)
    (hT : 2 ≤ T) (hV : 0 < V) (heta : 0 < eta)
    (hfull : ((((2 * P) ^ ell : ℕ) : ℝ)) ≤ T) :
    (∫ t in mtTypeIPrimeAmplifierLargeSet P ell T V,
        ‖mtWattCoefficientBlock a A t‖ ^ 2 *
          ‖mtWattUnitBlock N N' t‖ ^ 2) ≤
      ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownAbsorbedBlockMomentBound
          eta a A P ell N N' T V r := by
  calc
    _ ≤ ∑ r : Fin ell,
        mtTypeIPrimeHeathBrownCanonicalBlockMomentBound eta a A P ell N N' T V r :=
      setIntegral_mtTypeI_primeAmplifier_heathBrown_canonical
        a A P ell N N' T V eta hP hell hN hNN' hN'le hT hV heta hfull
    _ ≤ _ := Finset.sum_le_sum fun r _ =>
      mtTypeIPrimeHeathBrownCanonicalBlockMomentBound_le_absorbed
        eta a A P ell N N' T V r (one_le_two.trans hP) hlogP hdegree
          (one_le_two.trans hN) (by linarith) hV heta

end

end RHTower.Sieve
