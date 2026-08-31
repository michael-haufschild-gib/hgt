import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueTwoScale
import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.ProdIdxFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# Heath--Brown sparse mean value: divisor square lift

This leaf formalizes the Cauchy/divisor step in Heath--Brown's proof of Theorem 4(iii).  A full
unit interval is squared, its convolution coefficients are normalized by the explicit divisor
bound, and collision comparison replaces the resulting `[0,1]` coefficients by unit coefficients
on the squared interval.  The sparse-factor mean square is proved with support height and
integration height kept separate, so the result applies after the two-scale recurrence halves the
integration height.
-/

open Finset MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

def heathBrownSparseNatSupport (A : Finset PNat) : Finset ℕ :=
  A.image fun n : PNat => (n : ℕ)

def heathBrownSparseNatCoeff (A : Finset PNat) (eps : ℕ → Circle) (n : ℕ) : ℂ :=
  if n ∈ heathBrownSparseNatSupport A then (eps n : ℂ) else 0

@[simp] theorem heathBrownSparseNatCoeff_coe_of_mem
    (A : Finset PNat) (eps : ℕ → Circle) {n : PNat} (hn : n ∈ A) :
    heathBrownSparseNatCoeff A eps (n : ℕ) = (eps (n : ℕ) : ℂ) := by
  rw [heathBrownSparseNatCoeff, if_pos]
  rw [heathBrownSparseNatSupport]
  exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

@[simp] theorem norm_heathBrownSparseNatCoeff_coe_of_mem
    (A : Finset PNat) (eps : ℕ → Circle) {n : PNat} (hn : n ∈ A) :
    ‖heathBrownSparseNatCoeff A eps (n : ℕ)‖ = 1 := by
  rw [heathBrownSparseNatCoeff_coe_of_mem A eps hn, Circle.norm_coe]

@[simp] theorem zero_not_mem_heathBrownSparseNatSupport (A : Finset PNat) :
    0 ∉ heathBrownSparseNatSupport A := by
  intro h
  rw [heathBrownSparseNatSupport, Finset.mem_image] at h
  obtain ⟨n, hn, hn0⟩ := h
  have hn0' : (n : ℕ) = 0 := hn0
  exact (Nat.ne_of_gt n.pos) hn0'

theorem heathBrownSparseNatCoeff_support (A : Finset PNat) (eps : ℕ → Circle) (n : ℕ)
    (hn : heathBrownSparseNatCoeff A eps n ≠ 0) :
    n ∈ heathBrownSparseNatSupport A := by
  by_contra h
  simp [heathBrownSparseNatCoeff, h] at hn

@[simp] theorem norm_mul_natCast_rpow_zero (z : ℂ) (n : ℕ) :
    ‖z * ((((n : ℝ) ^ (-(0 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 := by
  norm_num

theorem LSeries_heathBrownSparseNatCoeff_eq
    (A : Finset PNat) (eps : ℕ → Circle) (t : ℝ) :
    LSeries (heathBrownSparseNatCoeff A eps) (((0 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      heathBrownSparseFactor A eps t := by
  rw [LSeries_eq_logPoly_of_support (zero_not_mem_heathBrownSparseNatSupport A)
    (heathBrownSparseNatCoeff_support A eps) 0 t]
  rw [logPoly, heathBrownSparseFactor, heathBrownSparseNatSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [heathBrownSparseNatCoeff_coe_of_mem A eps hn]
    let z : ℂ := (eps (n : ℕ) : ℂ)
    change z * ((((n : ℕ) : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (-t / (2 * Real.pi) *
          Real.log ((n : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) =
      z * heathBrownDirichletPhase n t
    have hpow : (((((n : ℕ) : ℝ) ^ (-(0 : ℝ)) : ℝ)) : ℂ) = 1 := by norm_num
    rw [hpow, mul_one, heathBrownDirichletPhase]
    congr 2
    push_cast
    field_simp [Real.pi_ne_zero]
  · intro n hn m hm hnm
    exact PNat.eq hnm

theorem sum_normSq_heathBrownSparseNatCoeff_eq_card
    (A : Finset PNat) (eps : ℕ → Circle) :
    (∑ n ∈ heathBrownSparseNatSupport A, ‖heathBrownSparseNatCoeff A eps n‖ ^ 2) =
      (A.card : ℝ) := by
  rw [heathBrownSparseNatSupport, Finset.sum_image]
  · calc
      (∑ n ∈ A, ‖heathBrownSparseNatCoeff A eps (n : ℕ)‖ ^ 2) =
          ∑ _n ∈ A, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_heathBrownSparseNatCoeff_coe_of_mem A eps hn, one_pow]
      _ = (A.card : ℝ) := by simp
  · intro n hn m hm hnm
    exact PNat.eq hnm

theorem sum_mul_normSq_heathBrownSparseNatCoeff_le
    (A : Finset PNat) (eps : ℕ → Circle) {X : ℝ}
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X) :
    (∑ n ∈ heathBrownSparseNatSupport A,
        (n : ℝ) * ‖heathBrownSparseNatCoeff A eps n‖ ^ 2) ≤ X * (A.card : ℝ) := by
  rw [heathBrownSparseNatSupport, Finset.sum_image]
  · calc
      (∑ n ∈ A, ((n : ℕ) : ℝ) *
          ‖heathBrownSparseNatCoeff A eps (n : ℕ)‖ ^ 2) ≤
          ∑ _n ∈ A, X := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_heathBrownSparseNatCoeff_coe_of_mem A eps hn, one_pow, mul_one]
        exact hA n hn
      _ = X * (A.card : ℝ) := by simp [mul_comm]
  · intro n hn m hm hnm
    exact PNat.eq hnm

/-- Ordinary mean square for the sparse factor, with support height and integration height separate. -/
theorem integral_Icc_normSq_heathBrownSparseFactor_le
    (A : Finset PNat) (eps : ℕ → Circle) {X W : ℝ}
    (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X) (hW : 1 ≤ W) :
    (∫ t in Set.Icc (-W) W, ‖heathBrownSparseFactor A eps t‖ ^ 2) ≤
      (5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * W) * (A.card : ℝ) := by
  have hbase := integral_Icc_normSq_LSeries_le_general_affine
    (zero_not_mem_heathBrownSparseNatSupport A)
    (heathBrownSparseNatCoeff_support A eps) 0 hW
  simp_rw [LSeries_heathBrownSparseNatCoeff_eq] at hbase
  rw [generalMeanSquareConst, generalMeanSquareRate] at hbase
  simp_rw [norm_mul_natCast_rpow_zero] at hbase
  have hweighted := sum_mul_normSq_heathBrownSparseNatCoeff_le A eps hA
  have hplain := sum_normSq_heathBrownSparseNatCoeff_eq_card A eps
  rw [hplain] at hbase
  calc
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (∑ n ∈ heathBrownSparseNatSupport A,
            (n : ℝ) * ‖heathBrownSparseNatCoeff A eps n‖ ^ 2) +
        (5 * Real.pi / 2) * (A.card : ℝ) * W := hbase
    _ ≤ 5 * Real.pi * Real.exp 1 * (X * (A.card : ℝ)) +
        (5 * Real.pi / 2) * (A.card : ℝ) * W := by
      gcongr
    _ = (5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * W) *
        (A.card : ℝ) := by ring

def heathBrownFinSucc (N : ℕ) : Fin N ↪ PNat where
  toFun n := ⟨(n : ℕ) + 1, by omega⟩
  inj' _ _ h := Fin.ext (by simpa using congrArg (fun n : PNat => (n : ℕ)) h)

theorem map_univ_heathBrownFinSucc_eq_positiveInterval {N : ℕ} (hN : 1 ≤ N) :
    (Finset.univ : Finset (Fin N)).map (heathBrownFinSucc N) =
      heathBrownPositiveInterval N hN := by
  ext n
  rw [Finset.mem_map, heathBrownPositiveInterval, Finset.mem_Icc]
  constructor
  · rintro ⟨m, -, rfl⟩
    constructor
    · change 1 ≤ (m : ℕ) + 1
      omega
    · change (m : ℕ) + 1 ≤ N
      exact m.isLt
  · intro hn
    have hn' : 1 ≤ (n : ℕ) ∧ (n : ℕ) ≤ N := hn
    let m : Fin N := ⟨(n : ℕ) - 1, by omega⟩
    refine ⟨m, Finset.mem_univ _, ?_⟩
    apply PNat.eq
    dsimp [m, heathBrownFinSucc]
    omega

theorem sum_fin_heathBrownFinSucc_eq_positiveInterval
    {N : ℕ} (hN : 1 ≤ N) (f : PNat → ℂ) :
    (∑ n : Fin N, f (heathBrownFinSucc N n)) =
      ∑ n ∈ heathBrownPositiveInterval N hN, f n := by
  rw [← map_univ_heathBrownFinSucc_eq_positiveInterval hN, Finset.sum_map]

/-- Full dense factor is a standard finite Dirichlet polynomial at reflected height. -/
theorem heathBrownDenseFactor_positiveInterval_eq_dirPoly
    {N : ℕ} (hN : 1 ≤ N) (q : ℕ → Set.Icc (0 : ℝ) 1) (t : ℝ) :
    heathBrownDenseFactor (heathBrownPositiveInterval N hN) q t =
      dirPoly N (fun n => (((q ((n : ℕ) + 1) : ℝ) : ℂ))) (-t) := by
  rw [heathBrownDenseFactor, dirPoly]
  rw [← sum_fin_heathBrownFinSucc_eq_positiveInterval hN]
  apply Finset.sum_congr rfl
  intro n hn
  rw [heathBrownDirichletPhase]
  congr 2
  simp [heathBrownFinSucc]

/-- Full unit dense factor is the standard finite Dirichlet polynomial at reflected height. -/
theorem heathBrownDenseFactor_positiveInterval_unit_eq_dirPoly
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    heathBrownDenseFactor (heathBrownPositiveInterval N hN) heathBrownDenseUnitWeight t =
      dirPoly N (fun _ => (1 : ℂ)) (-t) := by
  rw [heathBrownDenseFactor_positiveInterval_eq_dirPoly hN]
  apply Finset.sum_congr rfl
  intro n hn
  simp [heathBrownDenseUnitWeight]

/-- Ordered factor-pair multiplicity of one coefficient of the squared full interval. -/
def heathBrownSquareFibreCard (N : ℕ) (r : Fin (N * N)) : ℕ :=
  #((Finset.univ : Finset (Fin N × Fin N)).filter fun q => prodIdx q = r)

theorem dirConv_unit_eq_heathBrownSquareFibreCard (N : ℕ) (r : Fin (N * N)) :
    dirConv N N (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) r =
      (heathBrownSquareFibreCard N r : ℂ) := by
  rw [dirConv, filter_prodIdx_eq, heathBrownSquareFibreCard]
  simp

def heathBrownSquareDivisorScale (N : ℕ) (eta : ℝ) : ℝ :=
  divisorBoundConst eta * ((N * N : ℕ) : ℝ) ^ eta

def heathBrownSquareNormalizer (N : ℕ) (eta : ℝ) : ℝ :=
  max 1 (heathBrownSquareDivisorScale N eta)

theorem one_le_heathBrownSquareDivisorScale {N : ℕ} (hN : 1 ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    1 ≤ heathBrownSquareDivisorScale N eta := by
  have hC : 1 ≤ divisorBoundConst eta := by
    rw [divisorBoundConst]
    exact one_le_pow₀ (one_le_divisorBoundFactor heta)
  have hNNnat : 1 ≤ N * N := by simpa using Nat.mul_le_mul hN hN
  have hNN : (1 : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast hNNnat
  have hpow : 1 ≤ ((N * N : ℕ) : ℝ) ^ eta := Real.one_le_rpow hNN heta.le
  rw [heathBrownSquareDivisorScale]
  nlinarith [hC, hpow]

theorem cast_heathBrownSquareFibreCard_le_divisorScale
    {N : ℕ} {eta : ℝ} (heta : 0 < eta) (r : Fin (N * N)) :
    (heathBrownSquareFibreCard N r : ℝ) ≤ heathBrownSquareDivisorScale N eta := by
  have hfib : (heathBrownSquareFibreCard N r : ℝ) ≤
      ((Nat.divisors ((r : ℕ) + 1)).card : ℝ) := by
    exact_mod_cast prodIdx_fibre_card_le_divisors N N r
  have hdiv := card_divisors_le_rpow heta (n := (r : ℕ) + 1) (by omega)
  have hr : (((r : ℕ) + 1 : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) := by
    exact_mod_cast r.isLt
  have hrpow : (((r : ℕ) + 1 : ℕ) : ℝ) ^ eta ≤ ((N * N : ℕ) : ℝ) ^ eta :=
    Real.rpow_le_rpow (by positivity) hr heta.le
  calc
    (heathBrownSquareFibreCard N r : ℝ) ≤
        ((Nat.divisors ((r : ℕ) + 1)).card : ℝ) := hfib
    _ ≤ divisorBoundConst eta * (((r : ℕ) + 1 : ℕ) : ℝ) ^ eta := hdiv
    _ ≤ divisorBoundConst eta * ((N * N : ℕ) : ℝ) ^ eta := by
      gcongr
      exact (divisorBoundConst_pos heta).le
    _ = heathBrownSquareDivisorScale N eta := rfl

/-- Divisor-normalized coefficients of the square of the full unit interval. -/
def heathBrownNormalizedSquareWeight (N : ℕ) (eta : ℝ) (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  if h : 1 ≤ n ∧ n ≤ N * N then
    let r : Fin (N * N) := ⟨n - 1, by omega⟩
    ⟨min 1 ((heathBrownSquareFibreCard N r : ℝ) /
        heathBrownSquareNormalizer N eta), by
      constructor
      · apply le_min (by norm_num)
        exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (lt_of_lt_of_le zero_lt_one
          (le_max_left 1 (heathBrownSquareDivisorScale N eta))))
      · exact min_le_left _ _⟩
  else ⟨0, by constructor <;> norm_num⟩

theorem coe_heathBrownNormalizedSquareWeight_succ
    {N : ℕ} (hN : 1 ≤ N) {eta : ℝ} (heta : 0 < eta) (r : Fin (N * N)) :
    (heathBrownNormalizedSquareWeight N eta ((r : ℕ) + 1) : ℝ) =
      (heathBrownSquareFibreCard N r : ℝ) / heathBrownSquareDivisorScale N eta := by
  have hrange : 1 ≤ (r : ℕ) + 1 ∧ (r : ℕ) + 1 ≤ N * N := ⟨by omega, r.isLt⟩
  rw [heathBrownNormalizedSquareWeight, dif_pos hrange]
  let r' : Fin (N * N) := ⟨(r : ℕ) + 1 - 1, by omega⟩
  change min 1 ((heathBrownSquareFibreCard N r' : ℝ) /
      heathBrownSquareNormalizer N eta) = _
  have hr' : r' = r := by
    apply Fin.ext
    simp [r']
  rw [hr']
  have hscale1 := one_le_heathBrownSquareDivisorScale hN heta
  have hnorm : heathBrownSquareNormalizer N eta = heathBrownSquareDivisorScale N eta := by
    rw [heathBrownSquareNormalizer, max_eq_right hscale1]
  rw [hnorm]
  have hscale0 : 0 < heathBrownSquareDivisorScale N eta := lt_of_lt_of_le zero_lt_one hscale1
  have hcard := cast_heathBrownSquareFibreCard_le_divisorScale heta r
  have hratio : (heathBrownSquareFibreCard N r : ℝ) /
      heathBrownSquareDivisorScale N eta ≤ 1 := (div_le_one hscale0).mpr hcard
  exact min_eq_right hratio

/-- The normalized divisor coefficients reconstruct the square of the full unit interval. -/
theorem heathBrownDenseFactor_normalizedSquare_eq
    {N : ℕ} (hN : 1 ≤ N) {eta : ℝ} (heta : 0 < eta) (t : ℝ) :
    heathBrownDenseFactor (heathBrownPositiveInterval (N * N)
      (by simpa using Nat.mul_le_mul hN hN))
        (heathBrownNormalizedSquareWeight N eta) t =
      ((heathBrownSquareDivisorScale N eta : ℂ)⁻¹) *
        (heathBrownDenseFactor (heathBrownPositiveInterval N hN)
          heathBrownDenseUnitWeight t) ^ 2 := by
  rw [heathBrownDenseFactor_positiveInterval_eq_dirPoly
    (by simpa using Nat.mul_le_mul hN hN : 1 ≤ N * N)]
  have hcoeff : ∀ r : Fin (N * N),
      (((heathBrownNormalizedSquareWeight N eta ((r : ℕ) + 1) : ℝ) : ℂ)) =
        ((heathBrownSquareDivisorScale N eta : ℂ)⁻¹) *
          dirConv N N (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) r := by
    intro r
    rw [coe_heathBrownNormalizedSquareWeight_succ hN heta r,
      dirConv_unit_eq_heathBrownSquareFibreCard]
    push_cast
    rw [div_eq_mul_inv]
    ring
  rw [heathBrownDenseFactor_positiveInterval_unit_eq_dirPoly hN, pow_two,
    dirPoly_mul_eq_dirPoly]
  simp only [dirPoly]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hcoeff r]
  ring

/-- Any `[0,1]` dense coefficients are dominated by unit dense coefficients on the same support. -/
theorem integral_Icc_normSq_heathBrown_factors_le_unit
    (A B : Finset PNat) (eps : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t * heathBrownDenseFactor B q t‖ ^ 2) ≤
      (25 * Real.pi / 8) *
        ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A (fun _ => 1) t *
            heathBrownDenseFactor B heathBrownDenseUnitWeight t‖ ^ 2 := by
  let J : ℝ := (#(heathBrownPositiveStrictCollisionFinset A B ((T : ℝ)⁻¹)) : ℝ)
  have hforward := integral_Icc_normSq_heathBrown_factors_le_weightedCollision
    A B eps q T
  have hqJ : heathBrownPositiveWeightedCollision A B q T ≤ J := by
    exact heathBrownPositiveWeightedCollision_le_card_strictCollision A B q T
  have hunit : J ≤ (5 / (4 * (T : ℝ))) *
      ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor B heathBrownDenseUnitWeight t‖ ^ 2 := by
    dsimp only [J]
    rw [← heathBrownPositiveWeightedCollision_unit_eq_card A B T]
    exact heathBrownPositiveWeightedCollision_le_integral_Icc_factors
      A B heathBrownDenseUnitWeight T
  have hfac : 0 ≤ (5 * Real.pi / 2) * (T : ℝ) :=
    mul_nonneg (by positivity) T.property.le
  calc
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) * heathBrownPositiveWeightedCollision A B q T :=
      hforward
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) * J :=
      mul_le_mul_of_nonneg_left hqJ hfac
    _ ≤ (5 * Real.pi / 2) * (T : ℝ) *
        ((5 / (4 * (T : ℝ))) *
          ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
            ‖heathBrownSparseFactor A (fun _ => 1) t *
              heathBrownDenseFactor B heathBrownDenseUnitWeight t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hunit hfac
    _ = (25 * Real.pi / 8) *
        ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A (fun _ => 1) t *
            heathBrownDenseFactor B heathBrownDenseUnitWeight t‖ ^ 2 := by
      have hT0 : (T : ℝ) ≠ 0 := ne_of_gt T.property
      field_simp
      ring

/-- Cauchy--Schwarz in the square-lift form used by Heath--Brown. -/
theorem integral_Icc_normSq_mul_sq_le_mul
    (M Z : ℝ → ℂ) (hM : Continuous M) (hZ : Continuous Z) (W : ℝ) :
    (∫ t in Set.Icc (-W) W, ‖M t * Z t‖ ^ 2) ^ 2 ≤
      (∫ t in Set.Icc (-W) W, ‖M t‖ ^ 2) *
        ∫ t in Set.Icc (-W) W, ‖M t * Z t ^ 2‖ ^ 2 := by
  let E : Set ℝ := Set.Icc (-W) W
  have hMc : Continuous fun t => ‖M t‖ ^ 2 := hM.norm.pow 2
  have hGc : Continuous fun t => ‖M t * Z t ^ 2‖ ^ 2 :=
    (hM.mul (hZ.pow 2)).norm.pow 2
  have hMint : Integrable (fun t => ‖M t‖ ^ 2) (volume.restrict E) :=
    hMc.integrableOn_Icc
  have hGint : Integrable (fun t => ‖M t * Z t ^ 2‖ ^ 2) (volume.restrict E) :=
    hGc.integrableOn_Icc
  have hcs := GaloisForLFunctions.HTGeometry.integral_mul_le_sqrt_mul_sqrt_measure
    (μ := volume.restrict E) (g₁ := M) (g₂ := fun t => M t * Z t ^ 2)
    hM.aestronglyMeasurable.restrict
    (hM.mul (hZ.pow 2)).aestronglyMeasurable.restrict hMint hGint
  have hid : ∀ t : ℝ, ‖M t * Z t‖ ^ 2 = ‖M t‖ * ‖M t * Z t ^ 2‖ := by
    intro t
    rw [norm_mul, norm_mul, norm_pow]
    ring
  have hcs' : (∫ t in E, ‖M t * Z t‖ ^ 2) ≤
      Real.sqrt (∫ t in E, ‖M t‖ ^ 2) *
        Real.sqrt (∫ t in E, ‖M t * Z t ^ 2‖ ^ 2) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => hid t]
    exact hcs
  have hI0 : 0 ≤ ∫ t in E, ‖M t * Z t‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hM0 : 0 ≤ ∫ t in E, ‖M t‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hG0 : 0 ≤ ∫ t in E, ‖M t * Z t ^ 2‖ ^ 2 := integral_nonneg fun _ => by positivity
  calc
    (∫ t in E, ‖M t * Z t‖ ^ 2) ^ 2 ≤
        (Real.sqrt (∫ t in E, ‖M t‖ ^ 2) *
          Real.sqrt (∫ t in E, ‖M t * Z t ^ 2‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ hI0 hcs' 2
    _ = (∫ t in E, ‖M t‖ ^ 2) *
        ∫ t in E, ‖M t * Z t ^ 2‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hM0, Real.sq_sqrt hG0]

theorem continuous_heathBrownSparseFactor (A : Finset PNat) (eps : ℕ → Circle) :
    Continuous (heathBrownSparseFactor A eps) := by
  unfold heathBrownSparseFactor
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  unfold heathBrownDirichletPhase
  fun_prop

theorem continuous_heathBrownDenseFactor
    (B : Finset PNat) (q : ℕ → Set.Icc (0 : ℝ) 1) :
    Continuous (heathBrownDenseFactor B q) := by
  unfold heathBrownDenseFactor
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  unfold heathBrownDirichletPhase
  fun_prop

/-- Heath--Brown's Cauchy/divisor square lift, with every coefficient and analytic premise closed. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_sq_le_squareLift
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {X : ℝ} (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X)
    {N : ℕ} (hN : 1 ≤ N) {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor (heathBrownPositiveInterval N hN)
            heathBrownDenseUnitWeight t‖ ^ 2) ^ 2 ≤
      ((5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * (T : ℝ)) *
        (A.card : ℝ)) *
      (heathBrownSquareDivisorScale N eta ^ 2 * (25 * Real.pi / 8) *
        ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A (fun _ => 1) t *
            heathBrownDenseFactor
              (heathBrownPositiveInterval (N * N)
                (by simpa using Nat.mul_le_mul hN hN))
              heathBrownDenseUnitWeight t‖ ^ 2) := by
  let M : ℝ → ℂ := heathBrownSparseFactor A (fun _ => 1)
  let Z : ℝ → ℂ := heathBrownDenseFactor (heathBrownPositiveInterval N hN)
    heathBrownDenseUnitWeight
  let Z₂ : ℝ → ℂ := heathBrownDenseFactor
    (heathBrownPositiveInterval (N * N) (by simpa using Nat.mul_le_mul hN hN))
    (heathBrownNormalizedSquareWeight N eta)
  let I₂ : ℝ := ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
    ‖M t * heathBrownDenseFactor
      (heathBrownPositiveInterval (N * N) (by simpa using Nat.mul_le_mul hN hN))
      heathBrownDenseUnitWeight t‖ ^ 2
  have hM : Continuous M := continuous_heathBrownSparseFactor A (fun _ => 1)
  have hZ : Continuous Z :=
    continuous_heathBrownDenseFactor (heathBrownPositiveInterval N hN)
      heathBrownDenseUnitWeight
  have hZ₂ : Continuous Z₂ :=
    continuous_heathBrownDenseFactor
      (heathBrownPositiveInterval (N * N) (by simpa using Nat.mul_le_mul hN hN))
      (heathBrownNormalizedSquareWeight N eta)
  have hcs := integral_Icc_normSq_mul_sq_le_mul M Z hM hZ (T : ℝ)
  have hMbound : (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖M t‖ ^ 2) ≤
      (5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * (T : ℝ)) *
        (A.card : ℝ) := by
    exact integral_Icc_normSq_heathBrownSparseFactor_le A (fun _ => 1) hA hT
  have hscale1 := one_le_heathBrownSquareDivisorScale hN heta
  have hscale0 : 0 < heathBrownSquareDivisorScale N eta :=
    lt_of_lt_of_le zero_lt_one hscale1
  have hrecover : ∀ t : ℝ, Z t ^ 2 =
      (heathBrownSquareDivisorScale N eta : ℂ) * Z₂ t := by
    intro t
    have hz := heathBrownDenseFactor_normalizedSquare_eq hN heta t
    change Z₂ t = (heathBrownSquareDivisorScale N eta : ℂ)⁻¹ * Z t ^ 2 at hz
    rw [hz]
    field_simp [ne_of_gt hscale0]
  have hGpoint : ∀ t : ℝ, ‖M t * Z t ^ 2‖ ^ 2 =
      heathBrownSquareDivisorScale N eta ^ 2 * ‖M t * Z₂ t‖ ^ 2 := by
    intro t
    rw [hrecover t]
    have hnorm : ‖(heathBrownSquareDivisorScale N eta : ℂ)‖ =
        heathBrownSquareDivisorScale N eta := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale0]
    rw [show M t * ((heathBrownSquareDivisorScale N eta : ℂ) * Z₂ t) =
        (heathBrownSquareDivisorScale N eta : ℂ) * (M t * Z₂ t) by ring,
      norm_mul, hnorm]
    ring
  have hGidentity : (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖M t * Z t ^ 2‖ ^ 2) =
      heathBrownSquareDivisorScale N eta ^ 2 *
        ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖M t * Z₂ t‖ ^ 2 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ => hGpoint t]
    rw [MeasureTheory.integral_const_mul]
  have hZ₂bound : (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖M t * Z₂ t‖ ^ 2) ≤
      (25 * Real.pi / 8) * I₂ := by
    exact integral_Icc_normSq_heathBrown_factors_le_unit A
      (heathBrownPositiveInterval (N * N) (by simpa using Nat.mul_le_mul hN hN))
      (fun _ => 1) (heathBrownNormalizedSquareWeight N eta) T
  have hGbound : (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖M t * Z t ^ 2‖ ^ 2) ≤
      heathBrownSquareDivisorScale N eta ^ 2 * (25 * Real.pi / 8) * I₂ := by
    rw [hGidentity]
    have hs0 : 0 ≤ heathBrownSquareDivisorScale N eta ^ 2 := sq_nonneg _
    calc
      _ ≤ heathBrownSquareDivisorScale N eta ^ 2 * ((25 * Real.pi / 8) * I₂) :=
        mul_le_mul_of_nonneg_left hZ₂bound hs0
      _ = _ := by ring
  have hMbound0 : 0 ≤
      (5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * (T : ℝ)) *
        (A.card : ℝ) := le_trans (integral_nonneg fun _ => by positivity) hMbound
  have hG0 : 0 ≤ ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖M t * Z t ^ 2‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  change (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ), ‖M t * Z t‖ ^ 2) ^ 2 ≤ _
  exact hcs.trans (mul_le_mul hMbound hGbound hG0 hMbound0)

end

end RHTower.Sieve
