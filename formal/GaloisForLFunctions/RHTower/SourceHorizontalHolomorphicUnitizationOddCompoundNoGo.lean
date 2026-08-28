import GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicMatrixEquivalenceNoGo
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Odd-compound obstruction to holomorphic SC identity unitization

Identity unitization is the first additive escape from the scalar and matrix-equivalence
obstructions: `det (I + M_m(0)) = 1`, and the moving zeros of `det M_m` disappear.  This file
computes that genuinely nonlinear candidate rather than its tangent approximation.

For the universal reservoir `R = I - 𝟙𝟙ᵀ` and any real diagonal vector `b`, every principal
minor of `R diag(b)` indexed by `S` is

`(1 - |S|) ∏_{i∈S} b_i`.

Consequently `det(I + R diag(b))` has an exact Boolean-cube expansion.  If all `b_i < 0`, its
odd part is termwise nonnegative; the first three coordinates give a fixed strictly positive
cubic witness.  At real inputs `z = ±1`, coefficient faithfulness identifies this real matrix
with the actual entire prime Gamma-Bockstein reservoir.  Its unitized determinants therefore
retain a uniform sign asymmetry, whereas normalized centered Xi is even.  Compact-open
convergence is impossible.

The surviving SC landing must cancel the source-derived third exterior compound cofinally and
then every higher odd compound, for example through a nontrivial additive counterterm or a
symmetrized determinant.  No RH assumption or zero-location input is used.
-/

open Complex Filter Topology Set
open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- All-one real matrix on an arbitrary finite coordinate type. -/
def realReservoirOnesMatrix {ι : Type*} : Matrix ι ι ℝ := fun _ _ => 1

/-- Universal real reservoir `I - 𝟙𝟙ᵀ`. -/
def realReservoirBaseMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] : Matrix ι ι ℝ :=
  (1 : Matrix ι ι ℝ) - realReservoirOnesMatrix

/-- Universal reservoir with column `i` weighted by `b i`. -/
def realReservoirDiagonalMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) : Matrix ι ι ℝ :=
  realReservoirBaseMatrix * Matrix.diagonal b

/-- The reservoir determinant depends only on coordinate cardinality. -/
theorem realReservoirBaseMatrix_det {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (realReservoirBaseMatrix : Matrix ι ι ℝ).det =
      1 - (Fintype.card ι : ℝ) := by
  let c : Matrix ι (Fin 1) ℝ := fun _ _ => 1
  let r : Matrix (Fin 1) ι ℝ := fun _ _ => 1
  have hbase : (realReservoirBaseMatrix : Matrix ι ι ℝ) = 1 - c * r := by
    ext i j
    simp [realReservoirBaseMatrix, realReservoirOnesMatrix, c, r, Matrix.mul_apply]
  rw [hbase, Matrix.det_one_sub_mul_comm]
  have hsmall :
      (1 - r * c : Matrix (Fin 1) (Fin 1) ℝ) =
        !![(1 - (Fintype.card ι : ℝ))] := by
    ext i j
    fin_cases i
    fin_cases j
    simp [c, r, Matrix.mul_apply]
  rw [hsmall]
  simp

/-- Entrywise form of the column-weighted reservoir. -/
theorem realReservoirDiagonalMatrix_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (i j : ι) :
    realReservoirDiagonalMatrix b i j = realReservoirBaseMatrix i j * b j := by
  rw [realReservoirDiagonalMatrix, Matrix.mul_diagonal]

/-- Every principal minor is `(1 - |S|)` times its diagonal weight product. -/
theorem realReservoirDiagonalMatrix_submatrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (s : Finset ι) :
    ((realReservoirDiagonalMatrix b).submatrix
      (Subtype.val : s → ι) (Subtype.val : s → ι)).det =
      (1 - (s.card : ℝ)) * ∏ i : s, b i := by
  have hsub :
      (realReservoirDiagonalMatrix b).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι) =
        (realReservoirBaseMatrix : Matrix s s ℝ) *
          Matrix.diagonal (fun i : s => b i) := by
    ext i j
    rw [Matrix.submatrix_apply, realReservoirDiagonalMatrix_apply,
      Matrix.mul_diagonal]
    simp [realReservoirBaseMatrix, realReservoirOnesMatrix, Matrix.one_apply]
  rw [hsub, Matrix.det_mul, realReservoirBaseMatrix_det, Matrix.det_diagonal]
  rw [Fintype.card_coe]

/-- Canonical real identity-unitized reservoir determinant. -/
def unitizedRealReservoirDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) : ℝ :=
  (1 + realReservoirDiagonalMatrix b).det

/-- Exact Boolean-cube expansion of the nonlinear unitized determinant. -/
theorem unitizedRealReservoirDeterminant_eq_sum_powerset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) :
    unitizedRealReservoirDeterminant b =
      ∑ s ∈ (Finset.univ : Finset ι).powerset,
        (1 - (s.card : ℝ)) * ∏ i ∈ s, b i := by
  classical
  let P : Polynomial ℝ :=
    (1 + (Polynomial.X : Polynomial ℝ) •
      (realReservoirDiagonalMatrix b).map Polynomial.C).det
  have hP : P =
      ∑ s ∈ (Finset.univ : Finset ι).powerset,
        Polynomial.monomial s.card
          ((1 - (s.card : ℝ)) * ∏ i ∈ s, b i) := by
    ext k
    rw [show P.coeff k =
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
          ((realReservoirDiagonalMatrix b).submatrix
            (Subtype.val : s → ι) (Subtype.val : s → ι)).det by
      exact Matrix.coeff_det_one_add_X_smul_eq_sum_minors
        (realReservoirDiagonalMatrix b) k]
    simp_rw [realReservoirDiagonalMatrix_submatrix_det]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [← Finset.sum_filter]
    rw [← Finset.powersetCard_eq_filter]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.prod_coe_sort]
  have heval := congrArg (Polynomial.eval 1) hP
  have hevalDet : Polynomial.eval 1 P =
      unitizedRealReservoirDeterminant b := by
    change Polynomial.eval 1
        ((1 + (Polynomial.X : Polynomial ℝ) •
          (realReservoirDiagonalMatrix b).map Polynomial.C).det) = _
    have hmap := RingHom.map_det (Polynomial.evalRingHom (1 : ℝ))
      (1 + (Polynomial.X : Polynomial ℝ) •
        (realReservoirDiagonalMatrix b).map Polynomial.C)
    simp only [Polynomial.coe_evalRingHom] at hmap
    rw [hmap]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Matrix.add_apply, Matrix.add_apply,
      Matrix.smul_apply]
    simp only [map_add]
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hevalDet] at heval
  simpa [Polynomial.eval_finsetSum] using heval

/-- Exact odd-compound expansion: all even principal compounds cancel under `b ↦ -b`. -/
theorem unitizedRealReservoirDeterminant_sub_neg_eq_odd_powerset
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) :
    unitizedRealReservoirDeterminant b -
        unitizedRealReservoirDeterminant (-b) =
      2 * ∑ s ∈ (Finset.univ : Finset ι).powerset with Odd s.card,
        (1 - (s.card : ℝ)) * ∏ i ∈ s, b i := by
  classical
  rw [unitizedRealReservoirDeterminant_eq_sum_powerset,
    unitizedRealReservoirDeterminant_eq_sum_powerset,
    ← Finset.sum_sub_distrib]
  have hterm (s : Finset ι) :
      (1 - (s.card : ℝ)) * ∏ i ∈ s, b i -
          (1 - (s.card : ℝ)) * ∏ i ∈ s, (-b) i =
        (1 - (-1 : ℝ) ^ s.card) *
          ((1 - (s.card : ℝ)) * ∏ i ∈ s, b i) := by
    rw [show (∏ i ∈ s, (-b) i) =
        (-1 : ℝ) ^ s.card * ∏ i ∈ s, b i by
      simpa only [Pi.neg_apply] using (Finset.prod_neg (s := s) b)]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset ι).powerset (fun s => Odd s.card)
    (fun s => (1 - (-1 : ℝ) ^ s.card) *
      ((1 - (s.card : ℝ)) * ∏ i ∈ s, b i))]
  have hodd :
      (∑ s ∈ (Finset.univ : Finset ι).powerset with Odd s.card,
          (1 - (-1 : ℝ) ^ s.card) *
            ((1 - (s.card : ℝ)) * ∏ i ∈ s, b i)) =
        2 * ∑ s ∈ (Finset.univ : Finset ι).powerset with Odd s.card,
          (1 - (s.card : ℝ)) * ∏ i ∈ s, b i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hsodd : Odd s.card := (Finset.mem_filter.mp hs).2
    rw [hsodd.neg_one_pow]
    ring
  have heven :
      (∑ s ∈ (Finset.univ : Finset ι).powerset with ¬Odd s.card,
          (1 - (-1 : ℝ) ^ s.card) *
            ((1 - (s.card : ℝ)) * ∏ i ∈ s, b i)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hsnot : ¬Odd s.card := (Finset.mem_filter.mp hs).2
    have hseven : Even s.card := (Nat.even_or_odd s.card).resolve_right hsnot
    rw [hseven.neg_one_pow]
    ring
  rw [hodd, heven, add_zero]

/-- For a strictly negative diagonal, every odd principal-compound summand is nonnegative. -/
theorem realReservoirOddSummand_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hb : ∀ i, b i < 0)
    (s : Finset ι) (hs : Odd s.card) :
    0 ≤ (1 - (s.card : ℝ)) * ∏ i ∈ s, b i := by
  have hcard : 1 ≤ s.card := by
    obtain ⟨k, hk⟩ := hs
    omega
  have hnegprod : ∏ i ∈ s, b i < 0 := by
    have hpos : 0 < ∏ i ∈ s, -b i := by
      exact Finset.prod_pos fun i hi => neg_pos.mpr (hb i)
    calc
      ∏ i ∈ s, b i = (-1 : ℝ) ^ s.card * ∏ i ∈ s, -b i := by
        have h := Finset.prod_neg (s := s) (fun i => -b i)
        simpa using h
      _ = -(∏ i ∈ s, -b i) := by rw [hs.neg_one_pow]; ring
      _ < 0 := neg_neg_of_pos hpos
  have hcoeff : 1 - (s.card : ℝ) ≤ 0 := by
    exact sub_nonpos.mpr (by exact_mod_cast hcard)
  exact mul_nonneg_of_nonpos_of_nonpos hcoeff hnegprod.le

/-- Distinguished cubic compound carried by any embedded first triple of coordinates. -/
def realReservoirTripleWitness
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (e : Fin 3 ↪ ι) : ℝ :=
  -4 * ∏ j : Fin 3, b (e j)

/-- A strictly negative diagonal makes the distinguished cubic compound strictly positive. -/
theorem realReservoirTripleWitness_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hb : ∀ i, b i < 0) (e : Fin 3 ↪ ι) :
    0 < realReservoirTripleWitness b e := by
  have hprod : ∏ j : Fin 3, b (e j) < 0 := by
    have hpos : 0 < ∏ j : Fin 3, -b (e j) :=
      Finset.prod_pos fun j _ => neg_pos.mpr (hb (e j))
    calc
      ∏ j : Fin 3, b (e j) =
          (-1 : ℝ) ^ Fintype.card (Fin 3) * ∏ j : Fin 3, -b (e j) := by
        have h := Finset.prod_neg (s := (Finset.univ : Finset (Fin 3)))
          (fun j => -b (e j))
        simpa using h
      _ = -(∏ j : Fin 3, -b (e j)) := by norm_num
      _ < 0 := neg_neg_of_pos hpos
  unfold realReservoirTripleWitness
  nlinarith

/-- The fixed cubic compound is a lower witness for the complete odd determinant gap. -/
theorem realReservoirTripleWitness_le_odd_gap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : ι → ℝ} (hb : ∀ i, b i < 0) (e : Fin 3 ↪ ι) :
    realReservoirTripleWitness b e ≤
      unitizedRealReservoirDeterminant b -
        unitizedRealReservoirDeterminant (-b) := by
  rw [unitizedRealReservoirDeterminant_sub_neg_eq_odd_powerset]
  let S : Finset ι := Finset.univ.map e
  have hS : S ∈ (Finset.univ : Finset ι).powerset.filter
      (fun s => Odd s.card) := by
    simp [S]
    decide
  have hnonneg : ∀ s ∈ (Finset.univ : Finset ι).powerset.filter
      (fun s => Odd s.card),
      0 ≤ (1 - (s.card : ℝ)) * ∏ i ∈ s, b i := by
    intro s hs
    exact realReservoirOddSummand_nonneg hb s (Finset.mem_filter.mp hs).2
  have hsingle :
      (1 - (S.card : ℝ)) * ∏ i ∈ S, b i ≤
        ∑ s ∈ (Finset.univ : Finset ι).powerset with Odd s.card,
          (1 - (s.card : ℝ)) * ∏ i ∈ s, b i :=
    Finset.single_le_sum hnonneg hS
  have hterm :
      2 * ((1 - (S.card : ℝ)) * ∏ i ∈ S, b i) =
        realReservoirTripleWitness b e := by
    simp [S, realReservoirTripleWitness]
    ring
  rw [← hterm]
  nlinarith

/-- Canonical full-rank identity unitization of the first `m + 3` prime reservoir. -/
def preDivisorRiggedPrimeHolomorphicUnitizedDeterminant (m : ℕ) (z : ℂ) : ℂ :=
  (1 + preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) z).det

/-- The identity-unitized holomorphic determinant is centrally normalized to one. -/
theorem preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_zero (m : ℕ) :
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m 0 = 1 := by
  rw [preDivisorRiggedPrimeHolomorphicUnitizedDeterminant]
  have hmatrix :
      preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) 0 = 0 := by
    ext i j
    rw [preDivisorRiggedPrimeHolomorphicReservoirMatrix, Matrix.mul_diagonal]
    simp [preDivisorHolomorphicPrimeBockstein]
  rw [hmatrix]
  simp

/-- Every finite identity-unitized prime reservoir determinant is entire. -/
theorem differentiable_preDivisorRiggedPrimeHolomorphicUnitizedDeterminant (m : ℕ) :
    Differentiable ℂ (preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m) := by
  unfold preDivisorRiggedPrimeHolomorphicUnitizedDeterminant
  unfold preDivisorRiggedPrimeHolomorphicReservoirMatrix
  unfold preDivisorHolomorphicPrimeBockstein
  simp only [Matrix.det_apply', Matrix.add_apply, Matrix.mul_diagonal]
  fun_prop

/-- Real coefficient vector of the prime Bocksteins at positive transverse input `t = 1`. -/
def preDivisorRiggedPrimeRealBocksteinVector (m : ℕ) : Fin (m + 3) → ℝ :=
  fun i => primeGammaCofinalBocksteinCoefficient 1 (nthPrimePoint i)

/-- Every coordinate of the positive-input real Bockstein vector is strictly negative. -/
theorem preDivisorRiggedPrimeRealBocksteinVector_neg (m : ℕ) (i : Fin (m + 3)) :
    preDivisorRiggedPrimeRealBocksteinVector m i < 0 := by
  exact primeGammaCofinalBocksteinCoefficient_neg_of_pos (by norm_num) _

/-- The first three prime coordinates embedded into every cofinal packet. -/
def preDivisorRiggedPrimeFirstThreeEmbedding (m : ℕ) : Fin 3 ↪ Fin (m + 3) :=
  Fin.castLEEmb (by omega)

/-- Packet-independent cubic odd-compound witness carried by the first three primes. -/
def preDivisorRiggedPrimeUnitizedOddWitness : ℝ :=
  -4 * ∏ j : Fin 3,
    primeGammaCofinalBocksteinCoefficient 1 (nthPrimePoint j)

/-- The fixed first-three-prime odd-compound witness is strictly positive. -/
theorem preDivisorRiggedPrimeUnitizedOddWitness_pos : 0 < preDivisorRiggedPrimeUnitizedOddWitness := by
  have h := realReservoirTripleWitness_pos
    (b := preDivisorRiggedPrimeRealBocksteinVector 0)
    (preDivisorRiggedPrimeRealBocksteinVector_neg 0)
    (Function.Embedding.refl (Fin 3))
  simpa [realReservoirTripleWitness, preDivisorRiggedPrimeRealBocksteinVector,
    preDivisorRiggedPrimeUnitizedOddWitness] using h

/-- Coefficient faithfulness lifts from entries to the complete finite reservoir matrix. -/
theorem preDivisorRiggedPrimeHolomorphicReservoirMatrix_ofReal (m : ℕ) (t : ℝ) :
    preDivisorRiggedPrimeHolomorphicReservoirMatrix (m + 1) (t : ℂ) =
      (realReservoirDiagonalMatrix
        (fun i : Fin (m + 3) =>
          primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i))).map
        Complex.ofRealHom := by
  ext i j
  rw [preDivisorRiggedPrimeHolomorphicReservoirMatrix,
    Matrix.mul_diagonal, Matrix.map_apply, realReservoirDiagonalMatrix_apply,
    preDivisorHolomorphicPrimeBockstein_ofReal]
  by_cases hij : i = j
  · subst j
    simp [holomorphicReservoirBaseMatrix, holomorphicReservoirColumn,
      holomorphicReservoirRow, realReservoirBaseMatrix, realReservoirOnesMatrix,
      Matrix.mul_apply]
  · simp [holomorphicReservoirBaseMatrix, holomorphicReservoirColumn,
      holomorphicReservoirRow, realReservoirBaseMatrix, realReservoirOnesMatrix,
      Matrix.mul_apply, hij]

/-- Real restriction of the actual holomorphic unitized determinant. -/
theorem preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal (m : ℕ) (t : ℝ) :
    preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m (t : ℂ) =
      (unitizedRealReservoirDeterminant
        (fun i : Fin (m + 3) =>
          primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i)) : ℂ) := by
  rw [preDivisorRiggedPrimeHolomorphicUnitizedDeterminant,
    preDivisorRiggedPrimeHolomorphicReservoirMatrix_ofReal]
  let M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
    realReservoirDiagonalMatrix
      (fun i => primeGammaCofinalBocksteinCoefficient t (nthPrimePoint i))
  calc
    (1 + M.map Complex.ofRealHom).det =
        ((1 + M).map Complex.ofRealHom).det := by
      congr 1
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, map_add]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    _ = ((1 + M).det : ℂ) :=
      (RingHom.map_det Complex.ofRealHom (1 + M)).symm
    _ = _ := rfl

/-- Sign reversal at `t = -1` is pointwise negation of the positive-input vector. -/
theorem preDivisorRiggedPrimeRealBocksteinVector_neg_one (m : ℕ) :
    (fun i : Fin (m + 3) =>
      primeGammaCofinalBocksteinCoefficient (-1) (nthPrimePoint i)) =
      -(preDivisorRiggedPrimeRealBocksteinVector m) := by
  funext i
  rw [primeGammaCofinalBocksteinCoefficient_neg]
  rfl

/-- Every cofinal prime packet retains the same positive odd determinant gap witness. -/
theorem preDivisorRiggedPrimeUnitizedOddWitness_le_unitized_real_gap (m : ℕ) :
    preDivisorRiggedPrimeUnitizedOddWitness ≤
      (preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m 1 -
        preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m (-1)).re := by
  have hone := preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal m (1 : ℝ)
  have hnegone := preDivisorRiggedPrimeHolomorphicUnitizedDeterminant_ofReal m (-1 : ℝ)
  norm_num at hone hnegone
  rw [hone, hnegone]
  change preDivisorRiggedPrimeUnitizedOddWitness ≤
    unitizedRealReservoirDeterminant (preDivisorRiggedPrimeRealBocksteinVector m) -
      unitizedRealReservoirDeterminant (-(preDivisorRiggedPrimeRealBocksteinVector m))
  have h := realReservoirTripleWitness_le_odd_gap
    (b := preDivisorRiggedPrimeRealBocksteinVector m)
    (preDivisorRiggedPrimeRealBocksteinVector_neg m)
    (preDivisorRiggedPrimeFirstThreeEmbedding m)
  have hwitness :
      realReservoirTripleWitness (preDivisorRiggedPrimeRealBocksteinVector m)
          (preDivisorRiggedPrimeFirstThreeEmbedding m) = preDivisorRiggedPrimeUnitizedOddWitness := by
    simp [realReservoirTripleWitness, preDivisorRiggedPrimeRealBocksteinVector,
      preDivisorRiggedPrimeFirstThreeEmbedding, preDivisorRiggedPrimeUnitizedOddWitness, Fin.castLEEmb]
  rwa [hwitness] at h

/-- **Holomorphic identity-unitization no-go.**  The exact coefficient-faithful prime reservoir,
after canonical additive identity unitization, cannot converge compact-open to normalized
centered Xi.  The source has a fixed positive `z = ±1` odd-compound gap, while Xi is even. -/
theorem not_tendstoLocallyUniformly_normalizedXiC_of_holomorphicUnitization :
    ¬ TendstoLocallyUniformly preDivisorRiggedPrimeHolomorphicUnitizedDeterminant
      (fun z => XiC z / XiC 0) atTop := by
  intro hconv
  have hconvOn : TendstoLocallyUniformlyOn
      preDivisorRiggedPrimeHolomorphicUnitizedDeterminant
      (fun z => XiC z / XiC 0) atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr hconv
  have hplus := hconvOn.tendsto_at (Set.mem_univ (1 : ℂ))
  have hminus := hconvOn.tendsto_at (Set.mem_univ (-1 : ℂ))
  have hgapComplex := hplus.sub hminus
  have htarget :
      XiC (1 : ℂ) / XiC 0 - XiC (-1 : ℂ) / XiC 0 = 0 := by
    rw [show (-1 : ℂ) = -(1 : ℂ) by norm_num, XiC_even]
    ring
  have hgapReal : Tendsto
      (fun m => (preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m 1 -
        preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m (-1)).re)
      atTop (nhds 0) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hgapComplex
    have hre' : Tendsto
        (fun m => (preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m 1 -
          preDivisorRiggedPrimeHolomorphicUnitizedDeterminant m (-1)).re)
        atTop
        (nhds ((XiC (1 : ℂ) / XiC 0 - XiC (-1 : ℂ) / XiC 0).re)) :=
      hre.congr' (Filter.Eventually.of_forall fun _ => rfl)
    simpa only [htarget, Complex.zero_re] using hre'
  have hle : preDivisorRiggedPrimeUnitizedOddWitness ≤ 0 :=
    ge_of_tendsto' hgapReal preDivisorRiggedPrimeUnitizedOddWitness_le_unitized_real_gap
  exact (not_lt_of_ge hle) preDivisorRiggedPrimeUnitizedOddWitness_pos

end
end RHTower
