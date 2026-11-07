import GaloisForLFunctions.RHTower.Representation.EndpointAlternatingPositivity
import GaloisForLFunctions.RHTower.Representation.EndpointSectorPositivity

/-!
# Young projections of the arithmetic character at rank at most four

For a tableau `T` with row group `R` and column group `C`, the Young symmetrizer value of a class
function `χ` on `S_n` is `χ(c_T) = Σ_{p ∈ R} Σ_{q ∈ C} sgn(q) χ(pq)` (`youngValue`); the
multiplicity of the irreducible `λ` in `χ` is `(f^λ/n!) χ(c_T)`.

Let `χ_p(σ) = Π_{cycles of σ of length k ≥ 2} p_{k−1}` be multiplicative (`cycleMomentCharacter`), and
`e_k = (1/k!) Σ_{σ ∈ S_k} sgn(σ) χ_p(σ)` its elementary sequence (`eSeq`). For every shape `λ` with
`|λ| ≤ 4` (`youngValue_*_eq`),

`χ_p(c_T) = (n!/f^λ) · det (e_{λ'_r − r + c})_{r,c < λ₁}`,

a Toeplitz minor of `e`: the dual Jacobi–Trudi determinant. The proof evaluates both sides: the
signed cycle types of `R × C` and of `S_k` are computed by the kernel (`decide`).

For the arithmetic character, `e_k` is the `k`-th Taylor coefficient of the endpoint exterior series
(`eSeq_xiEndpoint`), whose Toeplitz minors of order `≤ 200` are nonnegative. So every Young
projection of the arithmetic character at rank `≤ 4` is nonnegative (`youngValue_*_nonneg`): the
arithmetic cycle class function is positive definite on `S_2`, `S_3`, `S_4`. The mixed shapes are
`(2,1)`, `(3,1)`, `(2,2)`, `(2,1,1)`.
-/

set_option autoImplicit false

open Equiv Finset
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.YoungProjections

open GaloisForLFunctions.SymmetricCharacters GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Young symmetrizer values -/

/-- The permutations preserving every class of a labelling. -/
def stabilizer {n : ℕ} (row : Fin n → ℕ) : Finset (Perm (Fin n)) :=
  univ.filter fun σ => ∀ i, row (σ i) = row i

/-- The Young symmetrizer value `χ(c_T) = Σ_{p ∈ R} Σ_{q ∈ C} sgn(q) χ(pq)` for the tableau with row
labels `row` and column labels `col`. -/
def youngValue {n : ℕ} (row col : Fin n → ℕ) (χ : Perm (Fin n) → ℝ) : ℝ :=
  ∑ p ∈ stabilizer row, ∑ q ∈ stabilizer col, ((Perm.sign q : ℤ) : ℝ) * χ (p * q)

/-- A signed multiset of cycle types, evaluated at the cycle values `p`. -/
def evalCT (p : ℕ → ℝ) (M : Multiset (ℤ × Multiset ℕ)) : ℝ :=
  (M.map fun x => (x.1 : ℝ) * (x.2.map fun k => p (k - 1)).prod).sum

theorem evalCT_add (p : ℕ → ℝ) (M N : Multiset (ℤ × Multiset ℕ)) :
    evalCT p (M + N) = evalCT p M + evalCT p N := by
  simp [evalCT]

theorem youngValue_eq_evalCT {n : ℕ} (row col : Fin n → ℕ) (p : ℕ → ℝ) :
    youngValue row col (cycleMomentCharacter p) =
      evalCT p ((stabilizer row ×ˢ stabilizer col).val.map fun pq =>
        (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) := by
  unfold youngValue evalCT
  rw [← Finset.sum_product', Finset.sum_eq_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => ?_)
  simp only [Function.comp, cycleMomentCharacter]
  congr

/-- The signed sum `Σ_{σ ∈ S_n} sgn(σ) χ_p(σ)`. -/
def altSum (n : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : ℝ) * cycleMomentCharacter p σ

theorem altSum_eq_evalCT (n : ℕ) (p : ℕ → ℝ) :
    altSum n p = evalCT p ((univ : Finset (Perm (Fin n))).val.map fun σ =>
      (((Perm.sign σ : ℤˣ) : ℤ), σ.cycleType)) := by
  unfold altSum evalCT
  rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => ?_)
  simp only [Function.comp, cycleMomentCharacter]
  congr

/-- The elementary sequence `e_k = (1/k!) Σ_{σ ∈ S_k} sgn(σ) χ_p(σ)`. -/
def eSeq (p : ℕ → ℝ) (k : ℕ) : ℝ := altSum k p / k.factorial

/-! ### The signed cycle types, by the kernel -/

theorem cycles_S0 : ((univ : Finset (Perm (Fin 0))).val.map fun σ =>
    (((Perm.sign σ : ℤˣ) : ℤ), σ.cycleType)) = {(1, 0)} := by decide

theorem cycles_S1 : ((univ : Finset (Perm (Fin 1))).val.map fun σ =>
    (((Perm.sign σ : ℤˣ) : ℤ), σ.cycleType)) = {(1, 0)} := by decide

theorem cycles_S2 : ((univ : Finset (Perm (Fin 2))).val.map fun σ =>
    (((Perm.sign σ : ℤˣ) : ℤ), σ.cycleType)) = {(1, 0), (-1, {2})} := by decide

theorem cycles_S3 : ((univ : Finset (Perm (Fin 3))).val.map fun σ =>
    (((Perm.sign σ : ℤˣ) : ℤ), σ.cycleType)) =
      {(1, 0), (-1, {2}), (-1, {2}), (-1, {2}), (1, {3}), (1, {3})} := by decide

theorem cycles_S4 : ((univ : Finset (Perm (Fin 4))).val.map fun σ =>
    (((Perm.sign σ : ℤˣ) : ℤ), σ.cycleType)) =
      {(1, 0), (-1, {2}), (-1, {2}), (-1, {2}), (-1, {2}), (-1, {2}), (-1, {2}),
        (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}),
        (1, {2, 2}), (1, {2, 2}), (1, {2, 2}),
        (-1, {4}), (-1, {4}), (-1, {4}), (-1, {4}), (-1, {4}), (-1, {4})} := by decide

theorem eSeq_zero (p : ℕ → ℝ) : eSeq p 0 = 1 := by
  rw [eSeq, altSum_eq_evalCT, cycles_S0]
  simp [evalCT]

theorem eSeq_one (p : ℕ → ℝ) : eSeq p 1 = 1 := by
  rw [eSeq, altSum_eq_evalCT, cycles_S1]
  simp [evalCT]

theorem eSeq_two (p : ℕ → ℝ) : eSeq p 2 = (1 - p 1) / 2 := by
  rw [eSeq, altSum_eq_evalCT, cycles_S2]
  simp [evalCT, Nat.factorial]
  ring

theorem eSeq_three (p : ℕ → ℝ) : eSeq p 3 = (1 - 3 * p 1 + 2 * p 2) / 6 := by
  rw [eSeq, altSum_eq_evalCT, cycles_S3]
  simp [evalCT, Nat.factorial]
  ring

theorem eSeq_four (p : ℕ → ℝ) :
    eSeq p 4 = (1 - 6 * p 1 + 8 * p 2 + 3 * p 1 ^ 2 - 6 * p 3) / 24 := by
  rw [eSeq, altSum_eq_evalCT, cycles_S4]
  simp [evalCT, Nat.factorial]
  ring

/-! ### Young symmetrizer values by shape -/

/-- Shape `(2,1)`: rows `{0,1},{2}`, columns `{0,2},{1}`. -/
theorem cycles_21 : ((stabilizer ![0, 0, 1] ×ˢ stabilizer ![0, 1, 0]).val.map fun pq =>
    (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) =
      {(1, 0), (-1, {2}), (1, {2}), (-1, {3})} := by decide

/-- Shape `(3,1)`: rows `{0,1,2},{3}`, columns `{0,3},{1},{2}`. -/
theorem cycles_31 : ((stabilizer ![0, 0, 0, 1] ×ˢ stabilizer ![0, 1, 2, 0]).val.map fun pq =>
    (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) =
      {(1, 0), (1, {2}), (1, {2}), (1, {2}), (1, {3}), (1, {3}),
        (-1, {2}), (-1, {3}), (-1, {3}), (-1, {2, 2}), (-1, {4}), (-1, {4})} := by decide

/-- Shape `(2,2)`: rows `{0,1},{2,3}`, columns `{0,2},{1,3}`. -/
theorem cycles_22 : ((stabilizer ![0, 0, 1, 1] ×ˢ stabilizer ![0, 1, 0, 1]).val.map fun pq =>
    (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) =
      {(1, 0), (-1, {2}), (-1, {2}), (1, {2}), (1, {2}), (1, {2, 2}), (1, {2, 2}), (1, {2, 2}),
        (-1, {3}), (-1, {3}), (-1, {3}), (-1, {3}), (1, {4}), (1, {4}), (-1, {4}), (-1, {4})} := by
  decide

/-- Shape `(2,1,1)`: rows `{0,1},{2},{3}`, columns `{0,2,3},{1}`. -/
theorem cycles_211 : ((stabilizer ![0, 0, 1, 2] ×ˢ stabilizer ![0, 1, 0, 0]).val.map fun pq =>
    (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) =
      {(1, 0), (-1, {2}), (-1, {2}), (-1, {2}), (1, {3}), (1, {3}),
        (1, {2}), (-1, {3}), (-1, {3}), (-1, {2, 2}), (1, {4}), (1, {4})} := by decide

/-- Shape `(2)`. -/
theorem cycles_2 : ((stabilizer ![0, 0] ×ˢ stabilizer ![0, 1]).val.map fun pq =>
    (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) = {(1, 0), (1, {2})} := by decide

/-- Shape `(3)`. -/
theorem cycles_3 : ((stabilizer ![0, 0, 0] ×ˢ stabilizer ![0, 1, 2]).val.map fun pq =>
    (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) =
      {(1, 0), (1, {2}), (1, {2}), (1, {2}), (1, {3}), (1, {3})} := by decide

/-- Shape `(4)`. -/
theorem cycles_4 : ((stabilizer ![0, 0, 0, 0] ×ˢ stabilizer ![0, 1, 2, 3]).val.map fun pq =>
    (((Perm.sign pq.2 : ℤˣ) : ℤ), (pq.1 * pq.2).cycleType)) =
      {(1, 0), (1, {2}), (1, {2}), (1, {2}), (1, {2}), (1, {2}), (1, {2}),
        (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}), (1, {3}),
        (1, {2, 2}), (1, {2, 2}), (1, {2, 2}),
        (1, {4}), (1, {4}), (1, {4}), (1, {4}), (1, {4}), (1, {4})} := by decide

/-! ### Toeplitz minors -/

theorem toeplitzMinor_two (a : ℕ → ℝ) (i j : Fin 2 → ℕ) :
    toeplitzMinor a 2 i j =
      zext a ((j 0 : ℤ) - i 0) * zext a ((j 1 : ℤ) - i 1) -
        zext a ((j 1 : ℤ) - i 0) * zext a ((j 0 : ℤ) - i 1) := by
  rw [toeplitzMinor, Matrix.det_fin_two]
  simp [Matrix.of_apply]

theorem toeplitzMinor_three (a : ℕ → ℝ) (i j : Fin 3 → ℕ) :
    toeplitzMinor a 3 i j = Matrix.det (Matrix.of fun r c => zext a ((j c : ℤ) - i r)) := rfl

theorem zext_of_nonneg (a : ℕ → ℝ) (n : ℕ) : zext a (n : ℤ) = a n := zext_natCast a n

theorem zext_neg_one (a : ℕ → ℝ) : zext a (-1) = 0 := by
  simp [zext]

/-! ### The dual Jacobi–Trudi identities at rank at most four -/

theorem youngValue_21_eq (p : ℕ → ℝ) :
    youngValue ![0, 0, 1] ![0, 1, 0] (cycleMomentCharacter p) =
      3 * toeplitzMinor (eSeq p) 2 ![0, 2] ![2, 3] := by
  rw [youngValue_eq_evalCT, cycles_21, toeplitzMinor_two]
  simp [evalCT, zext, eSeq_zero, eSeq_one, eSeq_two, eSeq_three]
  ring

theorem youngValue_22_eq (p : ℕ → ℝ) :
    youngValue ![0, 0, 1, 1] ![0, 1, 0, 1] (cycleMomentCharacter p) =
      12 * toeplitzMinor (eSeq p) 2 ![0, 1] ![2, 3] := by
  rw [youngValue_eq_evalCT, cycles_22, toeplitzMinor_two]
  simp [evalCT, zext, eSeq_one, eSeq_two, eSeq_three]
  ring

theorem youngValue_211_eq (p : ℕ → ℝ) :
    youngValue ![0, 0, 1, 2] ![0, 1, 0, 0] (cycleMomentCharacter p) =
      8 * toeplitzMinor (eSeq p) 2 ![0, 3] ![3, 4] := by
  rw [youngValue_eq_evalCT, cycles_211, toeplitzMinor_two]
  simp [evalCT, zext, eSeq_zero, eSeq_one, eSeq_three, eSeq_four]
  ring

theorem youngValue_31_eq (p : ℕ → ℝ) :
    youngValue ![0, 0, 0, 1] ![0, 1, 2, 0] (cycleMomentCharacter p) =
      8 * toeplitzMinor (eSeq p) 3 ![0, 2, 3] ![2, 3, 4] := by
  rw [youngValue_eq_evalCT, cycles_31, toeplitzMinor_three, Matrix.det_fin_three]
  simp [evalCT, zext, eSeq_zero, eSeq_one, eSeq_two, eSeq_three, eSeq_four]
  ring

theorem youngValue_2_eq (p : ℕ → ℝ) :
    youngValue ![0, 0] ![0, 1] (cycleMomentCharacter p) =
      2 * toeplitzMinor (eSeq p) 2 ![0, 1] ![1, 2] := by
  rw [youngValue_eq_evalCT, cycles_2, toeplitzMinor_two]
  simp [evalCT, zext, eSeq_zero, eSeq_one, eSeq_two]
  ring

theorem youngValue_3_eq (p : ℕ → ℝ) :
    youngValue ![0, 0, 0] ![0, 1, 2] (cycleMomentCharacter p) =
      6 * toeplitzMinor (eSeq p) 3 ![0, 1, 2] ![1, 2, 3] := by
  rw [youngValue_eq_evalCT, cycles_3, toeplitzMinor_three, Matrix.det_fin_three]
  simp [evalCT, zext, eSeq_zero, eSeq_one, eSeq_two, eSeq_three]
  ring

theorem youngValue_4_eq (p : ℕ → ℝ) :
    youngValue ![0, 0, 0, 0] ![0, 1, 2, 3] (cycleMomentCharacter p) =
      24 * toeplitzMinor (eSeq p) 4 ![0, 1, 2, 3] ![1, 2, 3, 4] := by
  rw [youngValue_eq_evalCT, cycles_4, toeplitzMinor, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, evalCT, zext, eSeq_zero,
    eSeq_one, eSeq_two, eSeq_three, eSeq_four, Fin.succAbove]
  ring

/-! ### The arithmetic character -/

theorem realSign_eq {k : ℕ} (σ : Perm (Fin k)) : realSign σ = ((Perm.sign σ : ℤ) : ℝ) := by
  unfold realSign
  congr
  exact Subsingleton.elim _ _

/-- **The elementary sequence of the arithmetic character is the exterior series.** -/
theorem eSeq_xiEndpoint (k : ℕ) :
    eSeq xiEndpointArithmeticCycle k = (xiEndpointExteriorCoefficient k).re := by
  have h1 := xiEndpointArithmeticCharacter_alternating_eq k
  have h2 := xiEndpointExteriorCoefficient_eq_deriv k
  rw [← h1] at h2
  have hsum : (∑ σ : Perm (Fin k), (realSign σ : ℂ) * xiEndpointArithmeticCharacter σ) =
      ((altSum k xiEndpointArithmeticCycle : ℝ) : ℂ) := by
    rw [altSum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [xiEndpointArithmeticCharacter, realSign_eq]
    push_cast
    ring
  have hA : complexAlternatingMass (X := Fin k) xiEndpointArithmeticCharacter =
      ((altSum k xiEndpointArithmeticCycle : ℝ) : ℂ) := by
    rw [complexAlternatingMass]
    convert hsum using 2
    exact congrArg (fun i => @Finset.univ (Perm (Fin k)) i) (Subsingleton.elim _ _)
  rw [h2, hA, eSeq, show ((k.factorial : ℕ) : ℂ) = ((k.factorial : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_div, Complex.ofReal_re]

theorem toeplitzMinor_xiEndpoint_nonneg {m : ℕ} (hm : m ≤ 200) {i j : Fin m → ℕ}
    (hi : StrictMono i) (hj : StrictMono j) :
    0 ≤ toeplitzMinor (eSeq xiEndpointArithmeticCycle) m i j := by
  have h := xiEndpointExteriorCoefficient_pfSeq_twoHundred m hm i j hi hj
  rwa [show eSeq xiEndpointArithmeticCycle = fun k => (xiEndpointExteriorCoefficient k).re from
    funext eSeq_xiEndpoint]

/-- **Shape `(2,1)` of the arithmetic character is nonnegative.** -/
theorem youngValue_21_nonneg :
    0 ≤ youngValue ![0, 0, 1] ![0, 1, 0] (cycleMomentCharacter xiEndpointArithmeticCycle) := by
  rw [youngValue_21_eq]
  exact mul_nonneg (by norm_num) (toeplitzMinor_xiEndpoint_nonneg (by norm_num) (by decide)
    (by decide))

/-- **Shape `(3,1)` of the arithmetic character is nonnegative.** -/
theorem youngValue_31_nonneg :
    0 ≤ youngValue ![0, 0, 0, 1] ![0, 1, 2, 0] (cycleMomentCharacter xiEndpointArithmeticCycle) := by
  rw [youngValue_31_eq]
  exact mul_nonneg (by norm_num) (toeplitzMinor_xiEndpoint_nonneg (by norm_num) (by decide)
    (by decide))

/-- **Shape `(2,2)` of the arithmetic character is nonnegative.** -/
theorem youngValue_22_nonneg :
    0 ≤ youngValue ![0, 0, 1, 1] ![0, 1, 0, 1] (cycleMomentCharacter xiEndpointArithmeticCycle) := by
  rw [youngValue_22_eq]
  exact mul_nonneg (by norm_num) (toeplitzMinor_xiEndpoint_nonneg (by norm_num) (by decide)
    (by decide))

/-- **Shape `(2,1,1)` of the arithmetic character is nonnegative.** -/
theorem youngValue_211_nonneg :
    0 ≤ youngValue ![0, 0, 1, 2] ![0, 1, 0, 0] (cycleMomentCharacter xiEndpointArithmeticCycle) := by
  rw [youngValue_211_eq]
  exact mul_nonneg (by norm_num) (toeplitzMinor_xiEndpoint_nonneg (by norm_num) (by decide)
    (by decide))

/-- **The row shapes `(2)`, `(3)`, `(4)` of the arithmetic character are nonnegative.** -/
theorem youngValue_rows_nonneg :
    0 ≤ youngValue ![0, 0] ![0, 1] (cycleMomentCharacter xiEndpointArithmeticCycle) ∧
      0 ≤ youngValue ![0, 0, 0] ![0, 1, 2] (cycleMomentCharacter xiEndpointArithmeticCycle) ∧
      0 ≤ youngValue ![0, 0, 0, 0] ![0, 1, 2, 3]
        (cycleMomentCharacter xiEndpointArithmeticCycle) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [youngValue_2_eq]
    exact mul_nonneg (by norm_num) (toeplitzMinor_xiEndpoint_nonneg (by norm_num) (by decide)
      (by decide))
  · rw [youngValue_3_eq]
    exact mul_nonneg (by norm_num) (toeplitzMinor_xiEndpoint_nonneg (by norm_num) (by decide)
      (by decide))
  · rw [youngValue_4_eq]
    exact mul_nonneg (by norm_num) (toeplitzMinor_xiEndpoint_nonneg (by norm_num) (by decide)
      (by decide))

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.YoungProjections
