import GaloisForLFunctions.RHTower.XiTransversePrimeSourceProjectiveTangent
import GaloisForLFunctions.HTGeometry.CayleySchur
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The valuation--Szego true-aperture metric of the transverse Xi source

At a fixed prime, raw transverse valuation layers converge to the same projective ray.  Their
successive differences do not collapse.  If `q_a = exp (-a log p)`, then the normalized layer is
`1 - q_a^(e+1)` and its valuation difference is

`(1 - q_a) q_a^e`.

Thus one prime and its complete valuation tower already place the aperture axis in the Hardy
coherent-state geometry.  The completed Gram is the diagonally weighted Szego kernel

`(1-q_a)(1-q_b)/(1-q_a q_b)`.

After unit normalization, its two-point defect is exactly the real disk pseudohyperbolic metric.
This is a positive replacement for the raw projective-collapse no-go.  It is a source metric and
does not assert the missing contractive comparison with the Xi Hardy leakage operator.
-/

namespace RHTower

noncomputable section

open scoped BigOperators ComplexOrder InnerProduct
open Matrix

/-- The real disk node attached to aperture `a` at the fixed prime `p`. -/
def xiTransversePrimeApertureDiskNode (a : ℕ) (p : Nat.Primes) : ℝ :=
  Real.exp (-(a : ℝ) * Real.log (p : ℕ))

theorem xiTransversePrimeApertureDiskNode_pos (a : ℕ) (p : Nat.Primes) :
    0 < xiTransversePrimeApertureDiskNode a p := by
  exact Real.exp_pos _

theorem xiTransversePrimeApertureDiskNode_lt_one
    {a : ℕ} (ha : 0 < a) (p : Nat.Primes) :
    xiTransversePrimeApertureDiskNode a p < 1 := by
  rw [xiTransversePrimeApertureDiskNode, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog := Real.log_pos hp
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  nlinarith

theorem xiTransversePrimeApertureDiskNode_injective (p : Nat.Primes) :
    Function.Injective (fun a : ℕ => xiTransversePrimeApertureDiskNode a p) := by
  intro a b hab
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℕ) := Real.log_pos hp
  have hexp := Real.exp_injective hab
  have hcast : (a : ℝ) = (b : ℝ) := by
    nlinarith
  exact_mod_cast hcast

/-- Multiplying an aperture by a valuation depth raises its disk node to that depth. -/
theorem xiTransversePrimeApertureDiskNode_mul
    (a r : ℕ) (p : Nat.Primes) :
    xiTransversePrimeApertureDiskNode (r * a) p =
      xiTransversePrimeApertureDiskNode a p ^ r := by
  rw [xiTransversePrimeApertureDiskNode, xiTransversePrimeApertureDiskNode,
    ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The disk node is the actual prime shift factor, not an auxiliary parametrization. -/
theorem primeShiftFactor_nat_eq_xiTransversePrimeApertureDiskNode
    (a : ℕ) (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.primeShiftFactor (a : ℂ) p =
      (xiTransversePrimeApertureDiskNode a p : ℂ) := by
  rw [GaloisForLFunctions.HTGeometry.primeShiftFactor,
    GaloisForLFunctions.HTGeometry.primeLogClock,
    xiTransversePrimeApertureDiskNode, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The actual prime-power transverse coefficient after removing its common prime-log clock. -/
def xiTransversePrimeValuationDefect
    (a e : ℕ) (p : Nat.Primes) : ℂ :=
  xiTransverseShiftArithmetic a ((p : ℕ) ^ (e + 1)) /
    (Real.log (p : ℕ) : ℂ)

/-- Exact disk form of every normalized valuation layer. -/
theorem xiTransversePrimeValuationDefect_eq
    (a e : ℕ) (p : Nat.Primes) :
    xiTransversePrimeValuationDefect a e p =
      1 - (xiTransversePrimeApertureDiskNode a p : ℂ) ^ (e + 1) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : (Real.log (p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hp).ne'
  rw [xiTransversePrimeValuationDefect, xiTransverseShiftArithmetic_apply,
    ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero e),
    ArithmeticFunction.vonMangoldt_apply_prime p.2,
    xiTransverse_cpowWeight_primePow]
  have hshift :
      GaloisForLFunctions.HTGeometry.primeShiftFactor
          (((e + 1 : ℕ) : ℂ) * (a : ℂ)) p =
        (xiTransversePrimeApertureDiskNode a p : ℂ) ^ (e + 1) := by
    rw [show (((e + 1 : ℕ) : ℂ) * (a : ℂ)) = (((e + 1) * a : ℕ) : ℂ) by
      push_cast
      ring,
      primeShiftFactor_nat_eq_xiTransversePrimeApertureDiskNode,
      xiTransversePrimeApertureDiskNode_mul]
    norm_cast
  rw [hshift]
  field_simp

/-- The non-collapsing coordinate: the successive valuation difference at one prime. -/
def xiTransversePrimeValuationIncrement
    (a e : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - xiTransversePrimeApertureDiskNode a p) *
    xiTransversePrimeApertureDiskNode a p ^ e

/-- The first valuation increment is the first normalized transverse layer. -/
theorem xiTransversePrimeValuationIncrement_zero_eq_defect
    (a : ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationIncrement a 0 p : ℂ) =
      xiTransversePrimeValuationDefect a 0 p := by
  rw [xiTransversePrimeValuationDefect_eq]
  simp [xiTransversePrimeValuationIncrement]

/-- Every later valuation increment is the successive difference of two actual normalized
prime-power layers. -/
theorem xiTransversePrimeValuationIncrement_succ_eq_defect_sub
    (a e : ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationIncrement a (e + 1) p : ℂ) =
      xiTransversePrimeValuationDefect a (e + 1) p -
        xiTransversePrimeValuationDefect a e p := by
  rw [xiTransversePrimeValuationDefect_eq,
    xiTransversePrimeValuationDefect_eq]
  simp only [xiTransversePrimeValuationIncrement,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_pow, pow_succ]
  ring

/-- The first `N` valuation increments of one aperture at one prime. -/
def xiTransversePrimeValuationFeature
    (N a : ℕ) (p : Nat.Primes) : Fin N → ℂ :=
  fun e => (xiTransversePrimeValuationIncrement a e p : ℂ)

/-- Square one-prime observation matrix: rows are valuation increments and columns are apertures. -/
def xiTransversePrimeValuationSamplingMatrix
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) : Matrix (Fin N) (Fin N) ℂ :=
  fun e j => xiTransversePrimeValuationFeature N (shift j) p e

theorem xiTransversePrimeValuationSamplingMatrix_factorization
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    xiTransversePrimeValuationSamplingMatrix shift p =
      (Matrix.vandermonde
        (fun j => (xiTransversePrimeApertureDiskNode (shift j) p : ℂ)))ᵀ *
      Matrix.diagonal
        (fun j => 1 - (xiTransversePrimeApertureDiskNode (shift j) p : ℂ)) := by
  classical
  ext e j
  rw [Matrix.mul_diagonal]
  simp [xiTransversePrimeValuationSamplingMatrix,
    xiTransversePrimeValuationFeature, xiTransversePrimeValuationIncrement,
    Matrix.vandermonde]
  ring

/-- One fixed prime and the first `N` valuation differences separate every injective packet of
`N` positive integral apertures. -/
theorem xiTransversePrimeValuationSamplingMatrix_det_ne_zero
    {N : ℕ} {shift : Fin N → ℕ} (hshift : Function.Injective shift)
    (hpos : ∀ j, 0 < shift j)
    (p : Nat.Primes) :
    (xiTransversePrimeValuationSamplingMatrix shift p).det ≠ 0 := by
  let q : Fin N → ℂ :=
    fun j => (xiTransversePrimeApertureDiskNode (shift j) p : ℂ)
  let d : Fin N → ℂ := fun j => 1 - q j
  have hq : Function.Injective q :=
    Complex.ofReal_injective.comp
      ((xiTransversePrimeApertureDiskNode_injective p).comp hshift)
  have hd : ∀ j, d j ≠ 0 := by
    intro j
    have hlt := xiTransversePrimeApertureDiskNode_lt_one (hpos j) p
    dsimp [d, q]
    intro hzero
    have hzeroR : (1 : ℝ) - xiTransversePrimeApertureDiskNode (shift j) p = 0 := by
      exact_mod_cast hzero
    linarith
  rw [xiTransversePrimeValuationSamplingMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hq
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun j _ => hd j

/-- The finite true-aperture metric at one prime. -/
def xiTransversePrimeValuationGramMatrix
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) : Matrix (Fin N) (Fin N) ℂ :=
  (xiTransversePrimeValuationSamplingMatrix shift p)ᴴ *
    xiTransversePrimeValuationSamplingMatrix shift p

/-- Every injective `N`-aperture packet has a positive-definite Gram using only one prime and its
first `N` valuation differences. -/
theorem xiTransversePrimeValuationGramMatrix_posDef
    {N : ℕ} {shift : Fin N → ℕ} (hshift : Function.Injective shift)
    (hpos : ∀ j, 0 < shift j)
    (p : Nat.Primes) :
    (xiTransversePrimeValuationGramMatrix shift p).PosDef := by
  rw [xiTransversePrimeValuationGramMatrix]
  apply Matrix.PosDef.conjTranspose_mul_self
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  exact xiTransversePrimeValuationSamplingMatrix_det_ne_zero hshift hpos p

/-- **Exact fixed-prime aperture classification.** At any chosen prime, the first `N` valuation
increments give a strictly positive `N`-aperture Gram exactly when the integral shifts have no
zero or collision. Thus one prime detects both literal defects, not only collision-free packets. -/
theorem xiTransversePrimeValuationGramMatrix_posDef_iff_injective_ne_zero
    {N : ℕ} (shift : Fin N → ℕ) (p : Nat.Primes) :
    (xiTransversePrimeValuationGramMatrix shift p).PosDef ↔
      Function.Injective shift ∧ ∀ j, shift j ≠ 0 := by
  constructor
  · intro hgram
    have hgramDet : (xiTransversePrimeValuationGramMatrix shift p).det ≠ 0 :=
      hgram.det_pos.ne'
    have hsampling : (xiTransversePrimeValuationSamplingMatrix shift p).det ≠ 0 := by
      intro hzero
      apply hgramDet
      rw [xiTransversePrimeValuationGramMatrix, Matrix.det_mul, hzero, mul_zero]
    rw [xiTransversePrimeValuationSamplingMatrix_factorization,
      Matrix.det_mul, Matrix.det_transpose] at hsampling
    obtain ⟨hvandermonde, hdiagonal⟩ := mul_ne_zero_iff.mp hsampling
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdiagonal
    constructor
    · intro i j hij
      have hnodes : Function.Injective
          (fun k : Fin N =>
            (xiTransversePrimeApertureDiskNode (shift k) p : ℂ)) :=
        Matrix.det_vandermonde_ne_zero_iff.mp hvandermonde
      exact hnodes (congrArg
        (fun a : ℕ => (xiTransversePrimeApertureDiskNode a p : ℂ)) hij)
    · intro j hzero
      have hj := hdiagonal j (Finset.mem_univ j)
      simp [hzero, xiTransversePrimeApertureDiskNode] at hj
  · rintro ⟨hinjective, hnonzero⟩
    exact xiTransversePrimeValuationGramMatrix_posDef hinjective
      (fun j => Nat.pos_of_ne_zero (hnonzero j)) p

/-- The completed one-prime valuation Gram: a diagonally weighted Szego kernel. -/
def xiTransversePrimeValuationSzegoMetric
    (a b : ℕ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode a p
  let r := xiTransversePrimeApertureDiskNode b p
  (1 - q) * (1 - r) / (1 - q * r)

/-- The completed metric is exactly the sum of all valuation-increment Gram coordinates. -/
theorem tsum_xiTransversePrimeValuationIncrement_mul_eq_szegoMetric
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    (∑' e : ℕ, xiTransversePrimeValuationIncrement a e p *
      xiTransversePrimeValuationIncrement b e p) =
      xiTransversePrimeValuationSzegoMetric a b p := by
  let q := xiTransversePrimeApertureDiskNode a p
  let r := xiTransversePrimeApertureDiskNode b p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos a p).le
  have hr0 : 0 ≤ r := (xiTransversePrimeApertureDiskNode_pos b p).le
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one ha p
  have hr1 : r < 1 := xiTransversePrimeApertureDiskNode_lt_one hb p
  have hqr0 : 0 ≤ q * r := mul_nonneg hq0 hr0
  have hqr1 : q * r < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hq0 hq1 hr1.le
  calc
    (∑' e : ℕ, xiTransversePrimeValuationIncrement a e p *
        xiTransversePrimeValuationIncrement b e p) =
        ∑' e : ℕ, ((1 - q) * (1 - r)) * (q * r) ^ e := by
      apply tsum_congr
      intro e
      simp only [xiTransversePrimeValuationIncrement, q, r, mul_pow]
      ring
    _ = ((1 - q) * (1 - r)) * ∑' e : ℕ, (q * r) ^ e := by
      rw [tsum_mul_left]
    _ = ((1 - q) * (1 - r)) * (1 - q * r)⁻¹ := by
      rw [tsum_geometric_of_lt_one hqr0 hqr1]
    _ = xiTransversePrimeValuationSzegoMetric a b p := by
      simp only [xiTransversePrimeValuationSzegoMetric, q, r, div_eq_mul_inv]

/-- Diagonal mass of one completed aperture ray. -/
theorem xiTransversePrimeValuationSzegoMetric_self
    {a : ℕ} (ha : 0 < a) (p : Nat.Primes) :
    xiTransversePrimeValuationSzegoMetric a a p =
      (1 - xiTransversePrimeApertureDiskNode a p) /
        (1 + xiTransversePrimeApertureDiskNode a p) := by
  let q := xiTransversePrimeApertureDiskNode a p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos a p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one ha p
  have hden :
      1 + q ≠ 0 := by nlinarith
  have hother :
      1 - q ≠ 0 := by linarith
  have hsq : 1 - q ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (q - 1)]
  simp only [xiTransversePrimeValuationSzegoMetric]
  rw [show xiTransversePrimeApertureDiskNode a p = q by rfl,
    show q * q = q ^ 2 by ring]
  field_simp [hden, hother, hsq]
  ring

/-- Squared correlation of the unit-normalized valuation features. -/
def xiTransversePrimeValuationNormalizedCorrelationSq
    (a b : ℕ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode a p
  let r := xiTransversePrimeApertureDiskNode b p
  (1 - q ^ 2) * (1 - r ^ 2) / (1 - q * r) ^ 2

/-- The normalized Hilbert defect is exactly the disk pseudohyperbolic distance squared. -/
theorem one_sub_xiTransversePrimeValuationNormalizedCorrelationSq
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    1 - xiTransversePrimeValuationNormalizedCorrelationSq a b p =
      ((xiTransversePrimeApertureDiskNode a p -
          xiTransversePrimeApertureDiskNode b p) /
        (1 - xiTransversePrimeApertureDiskNode a p *
          xiTransversePrimeApertureDiskNode b p)) ^ 2 := by
  let q := xiTransversePrimeApertureDiskNode a p
  let r := xiTransversePrimeApertureDiskNode b p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos a p).le
  have hr0 : 0 ≤ r := (xiTransversePrimeApertureDiskNode_pos b p).le
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one ha p
  have hr1 : r < 1 := xiTransversePrimeApertureDiskNode_lt_one hb p
  have hden : 1 - q * r ≠ 0 := by
    have : q * r < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hq0 hq1 hr1.le
    linarith
  change 1 - (1 - q ^ 2) * (1 - r ^ 2) / (1 - q * r) ^ 2 =
    ((q - r) / (1 - q * r)) ^ 2
  field_simp [hden]
  ring

/-- Distinct positive apertures have strictly positive completed Hilbert separation already at
one fixed prime. -/
theorem one_sub_xiTransversePrimeValuationNormalizedCorrelationSq_pos
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (p : Nat.Primes) :
    0 < 1 - xiTransversePrimeValuationNormalizedCorrelationSq a b p := by
  rw [one_sub_xiTransversePrimeValuationNormalizedCorrelationSq ha hb p]
  have hnode : xiTransversePrimeApertureDiskNode a p ≠
      xiTransversePrimeApertureDiskNode b p :=
    fun h => hab ((xiTransversePrimeApertureDiskNode_injective p) h)
  have hq0 := (xiTransversePrimeApertureDiskNode_pos a p).le
  have hr0 := (xiTransversePrimeApertureDiskNode_pos b p).le
  have hq1 := xiTransversePrimeApertureDiskNode_lt_one ha p
  have hr1 := xiTransversePrimeApertureDiskNode_lt_one hb p
  have hden : 0 < 1 - xiTransversePrimeApertureDiskNode a p *
      xiTransversePrimeApertureDiskNode b p := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hq0 hq1 hr1.le
    linarith
  exact sq_pos_of_ne_zero (div_ne_zero (sub_ne_zero.mpr hnode) hden.ne')

end

end RHTower
