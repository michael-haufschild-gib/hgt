import GaloisForLFunctions.HTGeometry.SignCouplingDeterminant
import GaloisForLFunctions.HTGeometry.PairCoupledImaginaryKyFan
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# A matrix realization of the real part of a product of shifted factors

Data: `m` quadratic factors `(z − x_j)(z − v_j) + R_j + i c_j (z − v_j)` (`R_j` real, `c_j ≥ 0`)
and `l` linear factors `z − s_k + i t_k` (`t_k ≥ 0`).  Every complex monic quadratic is of this
form; `x_j = v_j` is the vertically aligned case.  Let `E_±` be the product with `i` replaced by
`±i` (`realPartFactorGen`; `realPartFactor` is the case `v = x`).  The matrix
(`realPartMatrixGen`)

`T = [[diag(x, s) + K, B], [C, diag v]]`

on `Fin (m + l) ⊕ Fin m`, with the sign coupling `K` of weights `g = √(c, t)`, `B_{j j} = β_j`,
`C_{j j} = γ_j`, `β_j = √R_j⁺ + √R_j⁻`, `γ_j = −√R_j⁺ + √R_j⁻` (so `β_j γ_j = −R_j`), has

* characteristic polynomial `(E₊ + E₋)/2` (`charpoly_realPartMatrix`), and
* quadratic form with `Im ⟨x, T x⟩ = Σ_j 2 √R_j Im(conj x_{p_j} x_{q_j})`
  (`im_star_dotProduct_realPartMatrix`), `p_j`, `q_j` the two coordinates of factor `j`;

with the pair-coupled Ky Fan bound this gives, for every `σ ≥ 0`,
`Σ_λ (Im λ − σ)_+ ≤ Σ_j (√R_j − σ)_+` over the roots `λ` of `(E₊ + E₋)/2`
(`sum_roots_realPart_im_sub_pos_le`).

**Characteristic polynomial.**  At `z ∉ {v_j}` eliminate the lower block:
`det(z − T) = ∏(z − v_j) · det(diag(e) − K)` with `e_j = z − x_j + R_j/(z − v_j)`, `e_k = z − s_k`,
and the sign-coupling determinant gives `(∏(e + i g²) + ∏(e − i g²))/2`.
-/

open Matrix Complex Finset Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m l : ℕ}

/-- Upper coupling amplitude `β_j = √R_j⁺ + √R_j⁻`. -/
def pairUpper (R : Fin m → ℝ) (j : Fin m) : ℝ := Real.sqrt (R j) + Real.sqrt (-R j)

/-- Lower coupling amplitude `γ_j = −√R_j⁺ + √R_j⁻`. -/
def pairLower (R : Fin m → ℝ) (j : Fin m) : ℝ := -Real.sqrt (R j) + Real.sqrt (-R j)

theorem pairUpper_mul_pairLower (R : Fin m → ℝ) (j : Fin m) :
    pairUpper R j * pairLower R j = -R j := by
  unfold pairUpper pairLower
  rcases le_total 0 (R j) with h | h
  · rw [Real.sqrt_eq_zero'.mpr (show -R j ≤ 0 by linarith)]; nlinarith [Real.sq_sqrt h]
  · rw [Real.sqrt_eq_zero'.mpr h]; nlinarith [Real.sq_sqrt (neg_nonneg.mpr h)]

theorem pairUpper_sub_pairLower (R : Fin m → ℝ) (j : Fin m) :
    pairUpper R j - pairLower R j = 2 * Real.sqrt (R j) := by
  unfold pairUpper pairLower; ring

/-- The upper-right block `B`. -/
def realPartUpper (R : Fin m → ℝ) (l : ℕ) : Matrix (Fin (m + l)) (Fin m) ℂ :=
  of fun u j => if u = Fin.castAdd l j then ((pairUpper R j : ℝ) : ℂ) else 0

/-- The lower-left block `C`. -/
def realPartLower (R : Fin m → ℝ) (l : ℕ) : Matrix (Fin m) (Fin (m + l)) ℂ :=
  of fun j u => if u = Fin.castAdd l j then ((pairLower R j : ℝ) : ℂ) else 0

/-- The positive diagonal block `diag(x, s) + K`. -/
def realPartPos (x c : Fin m → ℝ) (s t : Fin l → ℝ) : Matrix (Fin (m + l)) (Fin (m + l)) ℂ :=
  diagonal (fun u => ((Fin.append x s u : ℝ) : ℂ)) +
    signCoupling fun u => ((Real.sqrt (Fin.append c t u) : ℝ) : ℂ)

/-- **The realization matrix.** -/
def realPartMatrixGen (x v R c : Fin m → ℝ) (s t : Fin l → ℝ) :
    Matrix (Fin (m + l) ⊕ Fin m) (Fin (m + l) ⊕ Fin m) ℂ :=
  fromBlocks (realPartPos x c s t) (realPartUpper R l) (realPartLower R l)
    (diagonal fun j => ((v j : ℝ) : ℂ))

/-- The vertically aligned realization `v = x`. -/
def realPartMatrix (x R c : Fin m → ℝ) (s t : Fin l → ℝ) :
    Matrix (Fin (m + l) ⊕ Fin m) (Fin (m + l) ⊕ Fin m) ℂ :=
  realPartMatrixGen x x R c s t

/-- The product `E_ε = ∏ ((X − x_j)(X − v_j) + R_j + ε c_j (X − v_j)) · ∏ (X − s_k + ε t_k)`. -/
def realPartFactorGen (x v R c : Fin m → ℝ) (s t : Fin l → ℝ) (ε : ℂ) : ℂ[X] :=
  (∏ j, ((X - C ((x j : ℝ) : ℂ)) * (X - C ((v j : ℝ) : ℂ)) + C ((R j : ℝ) : ℂ) +
      C (ε * ((c j : ℝ) : ℂ)) * (X - C ((v j : ℝ) : ℂ)))) *
    ∏ k, (X - C ((s k : ℝ) : ℂ) + C (ε * ((t k : ℝ) : ℂ)))

theorem eval_realPartFactorGen (x v R c : Fin m → ℝ) (s t : Fin l → ℝ) (ε z : ℂ) :
    (realPartFactorGen x v R c s t ε).eval z =
      (∏ j, ((z - x j) * (z - v j) + R j + ε * c j * (z - v j))) * ∏ k, (z - s k + ε * t k) := by
  simp [realPartFactorGen, eval_prod, mul_assoc]

/-- The product `E_ε = ∏ ((X − x_j)² + R_j + ε c_j (X − x_j)) · ∏ (X − s_k + ε t_k)`. -/
def realPartFactor (x R c : Fin m → ℝ) (s t : Fin l → ℝ) (ε : ℂ) : ℂ[X] :=
  (∏ j, ((X - C ((x j : ℝ) : ℂ)) ^ 2 + C ((R j : ℝ) : ℂ) +
      C (ε * ((c j : ℝ) : ℂ)) * (X - C ((x j : ℝ) : ℂ)))) *
    ∏ k, (X - C ((s k : ℝ) : ℂ) + C (ε * ((t k : ℝ) : ℂ)))

theorem eval_realPartFactor (x R c : Fin m → ℝ) (s t : Fin l → ℝ) (ε z : ℂ) :
    (realPartFactor x R c s t ε).eval z =
      (∏ j, ((z - x j) ^ 2 + R j + ε * c j * (z - x j))) * ∏ k, (z - s k + ε * t k) := by
  simp [realPartFactor, eval_prod, mul_assoc]

theorem realPartFactor_eq_gen (x R c : Fin m → ℝ) (s t : Fin l → ℝ) (ε : ℂ) :
    realPartFactor x R c s t ε = realPartFactorGen x x R c s t ε := by
  simp only [realPartFactor, realPartFactorGen, sq]

theorem castAdd_ne_natAdd (j : Fin m) (k : Fin l) : Fin.castAdd l j ≠ Fin.natAdd m k := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- The Schur correction `B · diag(w) · C` is diagonal. -/
theorem realPartUpper_mul_diagonal_mul_lower (R : Fin m → ℝ) (w : Fin m → ℂ) :
    realPartUpper R l * diagonal w * realPartLower R l =
      diagonal (Fin.append (fun j => ((pairUpper R j : ℝ) : ℂ) * w j * (pairLower R j : ℝ))
        (fun _ : Fin l => (0 : ℂ))) := by
  ext u v
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, realPartUpper, realPartLower, of_apply]
  induction u using Fin.addCases with
  | left j =>
    rw [Finset.sum_eq_single j]
    · simp only [if_true, Fin.append_left, diagonal_apply]
      by_cases hv : v = Fin.castAdd l j
      · subst hv; simp
      · simp [hv, Ne.symm hv]
    · intro i _ hij
      have : Fin.castAdd l j ≠ Fin.castAdd l i := fun h => hij (Fin.castAdd_injective _ _ h).symm
      simp [this]
    · simp
  | right k =>
    have h0 : ∀ i : Fin m, Fin.natAdd m k ≠ Fin.castAdd l i := fun i h => castAdd_ne_natAdd i k h.symm
    simp [h0, diagonal_apply]

/-- The positive diagonal block is `diag(x, s) + K` with real diagonal. -/
theorem realPartPos_apply (x c : Fin m → ℝ) (s t : Fin l → ℝ) (u v : Fin (m + l)) :
    realPartPos x c s t u v = diagonal (fun u => ((Fin.append x s u : ℝ) : ℂ)) u v +
      signCoupling (fun u => ((Real.sqrt (Fin.append c t u) : ℝ) : ℂ)) u v := rfl

/-- `√(c, t)²` recovers the weights. -/
theorem sq_sqrt_append (c : Fin m → ℝ) (t : Fin l → ℝ) (hc : ∀ j, 0 ≤ c j) (ht : ∀ k, 0 ≤ t k)
    (u : Fin (m + l)) :
    (((Real.sqrt (Fin.append c t u) : ℝ) : ℂ)) ^ 2 = ((Fin.append c t u : ℝ) : ℂ) := by
  have h0 : 0 ≤ Fin.append c t u := by
    induction u using Fin.addCases with
    | left j => simpa using hc j
    | right k => simpa using ht k
  rw [← ofReal_pow, Real.sq_sqrt h0]

/-- **Determinant of the realization at a point off the lower diagonal.** -/
theorem det_scalar_sub_realPartMatrixGen (x v R c : Fin m → ℝ) (s t : Fin l → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ht : ∀ k, 0 ≤ t k) {z : ℂ} (hz : ∀ j, z ≠ v j) :
    (scalar (Fin (m + l) ⊕ Fin m) z - realPartMatrixGen x v R c s t).det =
      ((realPartFactorGen x v R c s t I).eval z +
        (realPartFactorGen x v R c s t (-I)).eval z) / 2 := by
  set D : Matrix (Fin m) (Fin m) ℂ := diagonal fun j => z - v j with hD
  have hdz : ∀ j, z - (v j : ℂ) ≠ 0 := fun j => sub_ne_zero.mpr (hz j)
  have hDinv : D * diagonal (fun j => (z - v j)⁻¹) = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j; exact mul_inv_cancel₀ (hdz j)
  haveI : Invertible D := ⟨diagonal (fun j => (z - v j)⁻¹),
    by rw [hD, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext j
       exact inv_mul_cancel₀ (hdz j), hDinv⟩
  have hinv : ⅟D = diagonal (fun j => (z - v j)⁻¹) := invOf_eq_right_inv hDinv
  have hblocks : scalar (Fin (m + l) ⊕ Fin m) z - realPartMatrixGen x v R c s t =
      fromBlocks (scalar (Fin (m + l)) z - realPartPos x c s t) (-realPartUpper R l)
        (-realPartLower R l) D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [realPartMatrixGen, hD, scalar_apply, diagonal_apply, sub_eq_add_neg]
    all_goals (split_ifs <;> simp_all)
  rw [hblocks, det_fromBlocks₂₂, hinv]
  have hschur : scalar (Fin (m + l)) z - realPartPos x c s t -
      -realPartUpper R l * diagonal (fun j => (z - v j)⁻¹) * -realPartLower R l =
      diagonal (Fin.append (fun j => z - x j + R j / (z - v j)) (fun k => z - s k)) -
        signCoupling fun u => ((Real.sqrt (Fin.append c t u) : ℝ) : ℂ) := by
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [realPartUpper_mul_diagonal_mul_lower]
    ext u v
    simp only [Matrix.sub_apply, realPartPos_apply, scalar_apply, diagonal_apply]
    by_cases huv : u = v
    · subst huv
      simp only [if_true]
      induction u using Fin.addCases with
      | left j =>
        simp only [Fin.append_left]
        have hc : ((pairUpper R j : ℝ) : ℂ) * (pairLower R j : ℝ) = -(R j : ℂ) := by
          exact_mod_cast pairUpper_mul_pairLower R j
        linear_combination (-(z - v j)⁻¹) * hc
      | right k => simp only [Fin.append_right]; ring
    · simp [huv]
  rw [hschur, det_diagonal_sub_signCoupling, hD, det_diagonal]
  simp only [sq_sqrt_append c t hc ht, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    eval_realPartFactorGen]
  have hpair : ∀ (ε : ℂ) (j : Fin m), (z - v j) * (z - x j + R j / (z - v j) + ε * c j) =
      (z - x j) * (z - v j) + R j + ε * c j * (z - v j) := by
    intro ε j; field_simp [hdz j]
  have e1 : ∏ j, ((z - x j) * (z - v j) + R j + I * c j * (z - v j)) =
      (∏ j, (z - v j)) * ∏ j, (z - x j + R j / (z - v j) + I * c j) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun j _ => (hpair I j).symm
  have e2 : ∏ j, ((z - x j) * (z - v j) + R j + -I * c j * (z - v j)) =
      (∏ j, (z - v j)) * ∏ j, (z - x j + R j / (z - v j) - I * c j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hpair (-I) j]; ring
  have e3 : ∏ k, (z - s k + -I * t k) = ∏ k, (z - s k - I * t k) :=
    Finset.prod_congr rfl fun k _ => by ring
  rw [e1, e2, e3]; ring

/-- **The characteristic polynomial of the realization.** -/
theorem charpoly_realPartMatrixGen (x v R c : Fin m → ℝ) (s t : Fin l → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ht : ∀ k, 0 ≤ t k) :
    (realPartMatrixGen x v R c s t).charpoly =
      C (1 / 2 : ℂ) * (realPartFactorGen x v R c s t I + realPartFactorGen x v R c s t (-I)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hfin : ({z : ℂ | ∃ j, z = v j}).Finite := by
    have : {z : ℂ | ∃ j, z = v j} = Set.range (fun j => ((v j : ℝ) : ℂ)) := by
      ext z; simp [eq_comm]
    rw [this]; exact Set.finite_range _
  refine (hfin.infinite_compl.mono ?_)
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists] at hz
  simp only [Set.mem_setOf_eq, eval_charpoly, eval_mul, eval_C, eval_add]
  rw [det_scalar_sub_realPartMatrixGen x v R c s t hc ht hz]
  ring

theorem charpoly_realPartMatrix (x R c : Fin m → ℝ) (s t : Fin l → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ht : ∀ k, 0 ≤ t k) :
    (realPartMatrix x R c s t).charpoly =
      C (1 / 2 : ℂ) * (realPartFactor x R c s t I + realPartFactor x R c s t (-I)) := by
  rw [realPartMatrix, charpoly_realPartMatrixGen x x R c s t hc ht, realPartFactor_eq_gen,
    realPartFactor_eq_gen]

/-- A Hermitian quadratic form is real. -/
theorem im_star_dotProduct_mulVec_of_conj {ι : Type*} [Fintype ι] (P : Matrix ι ι ℂ)
    (hP : ∀ u w, (starRingEnd ℂ) (P u w) = P w u) (a : ι → ℂ) :
    (star a ⬝ᵥ P *ᵥ a).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, map_sum, map_mul,
    Complex.conj_conj, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [hP]; ring

/-- The positive block is Hermitian. -/
theorem realPartPos_conj (x c : Fin m → ℝ) (s t : Fin l → ℝ) (u w : Fin (m + l)) :
    (starRingEnd ℂ) (realPartPos x c s t u w) = realPartPos x c s t w u := by
  simp only [realPartPos_apply, map_add, diagonal_apply, signCoupling, of_apply]
  rcases lt_trichotomy u w with h | h | h
  · simp [h, h.ne, h.ne', not_lt.mpr h.le]; ring
  · subst h; simp
  · simp [h, h.ne, h.ne', not_lt.mpr h.le]; ring

/-- **The imaginary part of the quadratic form.** -/
theorem im_star_dotProduct_realPartMatrixGen (x w R c : Fin m → ℝ) (s t : Fin l → ℝ)
    (v : Fin (m + l) ⊕ Fin m → ℂ) :
    (star v ⬝ᵥ realPartMatrixGen x w R c s t *ᵥ v).im =
      ∑ j, 2 * Real.sqrt (R j) *
        ((starRingEnd ℂ) (v (Sum.inl (Fin.castAdd l j))) * v (Sum.inr j)).im := by
  set a : Fin (m + l) → ℂ := v ∘ Sum.inl with ha
  set b : Fin m → ℂ := v ∘ Sum.inr with hb
  have hsplit : star v ⬝ᵥ realPartMatrixGen x w R c s t *ᵥ v =
      star a ⬝ᵥ realPartPos x c s t *ᵥ a + star a ⬝ᵥ realPartUpper R l *ᵥ b +
        (star b ⬝ᵥ realPartLower R l *ᵥ a +
          star b ⬝ᵥ (diagonal fun j => ((w j : ℝ) : ℂ)) *ᵥ b) := by
    rw [realPartMatrixGen, fromBlocks_mulVec]
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      mul_add, Finset.sum_add_distrib, Pi.star_apply, ha, hb, Function.comp_apply]
  have hAB : star a ⬝ᵥ realPartUpper R l *ᵥ b =
      ∑ j, ((pairUpper R j : ℝ) : ℂ) * ((starRingEnd ℂ) (a (Fin.castAdd l j)) * b j) := by
    simp only [dotProduct, mulVec, realPartUpper, of_apply, Pi.star_apply, RCLike.star_def,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]; ring
  have hBA : star b ⬝ᵥ realPartLower R l *ᵥ a =
      ∑ j, ((pairLower R j : ℝ) : ℂ) * ((starRingEnd ℂ) (b j) * a (Fin.castAdd l j)) := by
    simp only [dotProduct, mulVec, realPartLower, of_apply, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]; ring
  have hAA : (star a ⬝ᵥ realPartPos x c s t *ᵥ a).im = 0 :=
    im_star_dotProduct_mulVec_of_conj _ (realPartPos_conj x c s t) a
  have hDD : (star b ⬝ᵥ (diagonal fun j => ((w j : ℝ) : ℂ)) *ᵥ b).im = 0 := by
    refine im_star_dotProduct_mulVec_of_conj _ (fun u w => ?_) b
    by_cases h : u = w
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [hsplit, Complex.add_im, Complex.add_im, Complex.add_im, hAA, hDD, hAB, hBA,
    Complex.im_sum, Complex.im_sum, zero_add, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := pairUpper_sub_pairLower R j
  have hswap : ((starRingEnd ℂ) (b j) * a (Fin.castAdd l j)).im =
      -((starRingEnd ℂ) (a (Fin.castAdd l j)) * b j).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  rw [Complex.im_ofReal_mul, Complex.im_ofReal_mul, hswap]
  simp only [ha, hb, Function.comp_apply]
  linear_combination ((starRingEnd ℂ) (v (Sum.inl (Fin.castAdd l j))) * v (Sum.inr j)).im * h

/-- **Pair-coupled Ky Fan bound for the real part of a shifted product.**  For every `σ ≥ 0`, the
roots `λ` of `(E₊ + E₋)/2` satisfy `Σ_λ (Im λ − σ)_+ ≤ Σ_j (√R_j − σ)_+`. -/
theorem sum_roots_realPartGen_im_sub_pos_le (x v R c : Fin m → ℝ) (s t : Fin l → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ht : ∀ k, 0 ≤ t k) {σ : ℝ} (hσ : 0 ≤ σ) :
    ((C (1 / 2 : ℂ) * (realPartFactorGen x v R c s t I +
        realPartFactorGen x v R c s t (-I))).roots.map
        fun z => max (z.im - σ) 0).sum ≤ ∑ j, max (Real.sqrt (R j) - σ) 0 := by
  classical
  set e : Fin (m + l) ⊕ Fin m ≃ Fin (m + l + m) := finSumFinEquiv
  set T := realPartMatrixGen x v R c s t
  set T' : Matrix (Fin (m + l + m)) (Fin (m + l + m)) ℂ := reindex e e T with hT'
  have hcp : T'.charpoly = C (1 / 2 : ℂ) *
      (realPartFactorGen x v R c s t I + realPartFactorGen x v R c s t (-I)) := by
    rw [hT', charpoly_reindex, charpoly_realPartMatrixGen x v R c s t hc ht]
  rw [← hcp]
  refine sum_roots_charpoly_im_sub_pos_le T' (fun j => e (Sum.inl (Fin.castAdd l j)))
    (fun j => e (Sum.inr j)) ?_ ?_ ?_ (fun j => Real.sqrt (R j)) (fun j => Real.sqrt_nonneg _)
    ?_ hσ
  · intro j k h
    have := e.injective h
    exact Fin.castAdd_injective _ _ (Sum.inl_injective this)
  · intro j k h
    exact Sum.inr_injective (e.injective h)
  · intro j k h
    exact Sum.inl_ne_inr (e.injective h)
  · intro w
    have hq : star w ⬝ᵥ T' *ᵥ w = star (w ∘ e) ⬝ᵥ T *ᵥ (w ∘ e) := by
      simp only [hT', dotProduct, mulVec, reindex_apply, submatrix_apply, Pi.star_apply,
        Function.comp_apply]
      rw [← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← e.sum_comp]
      simp
    rw [hq, im_star_dotProduct_realPartMatrixGen]
    rfl

/-- The vertically aligned case. -/
theorem sum_roots_realPart_im_sub_pos_le (x R c : Fin m → ℝ) (s t : Fin l → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ht : ∀ k, 0 ≤ t k) {σ : ℝ} (hσ : 0 ≤ σ) :
    ((C (1 / 2 : ℂ) * (realPartFactor x R c s t I + realPartFactor x R c s t (-I))).roots.map
        fun z => max (z.im - σ) 0).sum ≤ ∑ j, max (Real.sqrt (R j) - σ) 0 := by
  rw [realPartFactor_eq_gen, realPartFactor_eq_gen]
  exact sum_roots_realPartGen_im_sub_pos_le x x R c s t hc ht hσ

end

end GaloisForLFunctions.HTGeometry
