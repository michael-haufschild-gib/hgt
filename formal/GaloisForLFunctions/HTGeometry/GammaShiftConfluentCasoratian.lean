import GaloisForLFunctions.HTGeometry.GammaDifferentialFE
import GaloisForLFunctions.HTGeometry.GammaShiftConfluentAnnihilator
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sigma.Order
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Exact confluent Gamma-shift Casoratians

This module proves the arbitrary-multiplicity determinant in equation (5) of the finite
Gamma-shift Dirichlet residual law.  The proof builds the missing confluent Vandermonde
infrastructure rather than postulating it:

* derivative-evaluation determinants are invariant under a unitriangular change between monic
  successive-degree polynomial families;
* a canonically ordered Newton--Hermite basis has a triangular jet matrix, whose diagonal gives
  the factorials and exact pairwise powers;
* the differentiated Gamma functional equation is an upper-triangular column change with one
  copy of `Gamma` on every jet-slot diagonal.

The principal result is `det_confluentGammaShiftMatrix`; its nonvanishing corollary is
`det_confluentGammaShiftMatrix_ne_zero`.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open Matrix Polynomial Filter Topology

noncomputable section

variable {K : Type*} [CommRing K]

/-- Matrix of polynomial derivative jets: rows are functionals and columns are polynomials. -/
def polynomialJetEvalMatrix {n : ℕ} (x : Fin n → K) (ord : Fin n → ℕ)
    (p : Fin n → K[X]) : Matrix (Fin n) (Fin n) K :=
  fun j k ↦ ((derivative^[ord j]) (p k)).eval (x j)

/-- Coefficient matrix of a finite polynomial family. -/
def polynomialCoeffMatrix {n : ℕ} (p : Fin n → K[X]) : Matrix (Fin n) (Fin n) K :=
  fun i k ↦ (p k).coeff (i : ℕ)

theorem polynomialJetEvalMatrix_eq_mul_coeff {n : ℕ}
    (x : Fin n → K) (ord : Fin n → ℕ) (p : Fin n → K[X])
    (hdeg : ∀ k, (p k).natDegree ≤ (k : ℕ)) :
    polynomialJetEvalMatrix x ord p =
      polynomialJetEvalMatrix x ord (fun k ↦ X ^ (k : ℕ)) * polynomialCoeffMatrix p := by
  ext j k
  rw [polynomialJetEvalMatrix, Matrix.mul_apply]
  have hp : (p k).natDegree < n := hdeg k |>.trans_lt k.isLt
  rw [(p k).as_sum_range' n hp, iterate_derivative_sum, eval_finsetSum,
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, iterate_derivative_C_mul, eval_mul, eval_C]
  simp only [polynomialJetEvalMatrix, polynomialCoeffMatrix]
  ring

theorem det_polynomialCoeffMatrix_eq_one {n : ℕ} (p : Fin n → K[X])
    (hdeg : ∀ k, (p k).natDegree = (k : ℕ)) (hmonic : ∀ k, (p k).Monic) :
    (polynomialCoeffMatrix p).det = 1 := by
  exact Matrix.det_matrixOfPolynomials p hdeg hmonic

theorem det_polynomialJetEvalMatrix_eq_monomial {n : ℕ}
    (x : Fin n → K) (ord : Fin n → ℕ) (p : Fin n → K[X])
    (hdeg : ∀ k, (p k).natDegree = (k : ℕ)) (hmonic : ∀ k, (p k).Monic) :
    (polynomialJetEvalMatrix x ord p).det =
      (polynomialJetEvalMatrix x ord (fun k ↦ X ^ (k : ℕ))).det := by
  rw [polynomialJetEvalMatrix_eq_mul_coeff x ord p (fun k ↦ (hdeg k).le),
    Matrix.det_mul, det_polynomialCoeffMatrix_eq_one p hdeg hmonic, mul_one]

theorem det_polynomialJetEvalMatrix_eq_of_monic_successive {n : ℕ}
    (x : Fin n → K) (ord : Fin n → ℕ) (p q : Fin n → K[X])
    (hpdeg : ∀ k, (p k).natDegree = (k : ℕ)) (hpmonic : ∀ k, (p k).Monic)
    (hqdeg : ∀ k, (q k).natDegree = (k : ℕ)) (hqmonic : ∀ k, (q k).Monic) :
    (polynomialJetEvalMatrix x ord p).det = (polynomialJetEvalMatrix x ord q).det := by
  rw [det_polynomialJetEvalMatrix_eq_monomial x ord p hpdeg hpmonic,
    det_polynomialJetEvalMatrix_eq_monomial x ord q hqdeg hqmonic]

/-! Canonically ordered confluent jet slots. -/

abbrev GammaJetSlot {r : ℕ} (mult : Fin r → ℕ) :=
  Σₗ i : Fin r, Fin (mult i)

def gammaJetSlotOrderIso {r : ℕ} (mult : Fin r → ℕ) :
    Fin (∑ i, mult i) ≃o GammaJetSlot mult :=
  Fintype.orderIsoFinOfCardEq (GammaJetSlot mult) (by
    simp [GammaJetSlot])

def gammaJetSlotNode {r : ℕ} (mult : Fin r → ℕ) (k : Fin (∑ i, mult i)) : Fin r :=
  (gammaJetSlotOrderIso mult k).1

def gammaJetSlotOrder {r : ℕ} (mult : Fin r → ℕ) (k : Fin (∑ i, mult i)) : ℕ :=
  ((gammaJetSlotOrderIso mult k).2 : ℕ)

def gammaJetNewtonPolynomial {r : ℕ} (x : Fin r → K) (mult : Fin r → ℕ)
    (k : Fin (∑ i, mult i)) : K[X] :=
  ∏ j ∈ Finset.Iio k, (X - C (x (gammaJetSlotNode mult j)))

theorem gammaJetNewtonPolynomial_monic {r : ℕ} (x : Fin r → K) (mult : Fin r → ℕ)
    (k : Fin (∑ i, mult i)) : (gammaJetNewtonPolynomial x mult k).Monic := by
  apply monic_prod_of_monic
  intro j _
  exact monic_X_sub_C _

theorem gammaJetNewtonPolynomial_natDegree {r : ℕ} [Nontrivial K]
    (x : Fin r → K) (mult : Fin r → ℕ) (k : Fin (∑ i, mult i)) :
    (gammaJetNewtonPolynomial x mult k).natDegree = (k : ℕ) := by
  rw [gammaJetNewtonPolynomial, natDegree_prod_of_monic]
  · simp [Fin.card_Iio]
  · intro j _
    exact monic_X_sub_C _

variable {M : Type*} [CommMonoid M]

theorem prod_fin_ite_lt (n : ℕ) (a : Fin n) (c : M) :
    (∏ q : Fin n, if q < a then c else 1) = c ^ (a : ℕ) := by
  rw [← Finset.prod_filter]
  rw [show Finset.filter (fun q : Fin n => q < a) Finset.univ = Finset.Iio a by ext; simp,
    Finset.prod_const, Fin.card_Iio]

theorem prod_gammaJetSlot_Iio {r : ℕ} (mult : Fin r → ℕ)
    (a : GammaJetSlot mult) (f : Fin r → M) :
    (∏ z ∈ Finset.univ.filter (fun z : GammaJetSlot mult => z < a), f z.1) =
      (∏ i ∈ Finset.Iio a.1, f i ^ mult i) * f a.1 ^ (a.2 : ℕ) := by
  classical
  induction a using Lex.rec with
  | _ a =>
  rcases a with ⟨a, m⟩
  calc
    (∏ z ∈ Finset.univ.filter (fun z : GammaJetSlot mult => z < toLex ⟨a, m⟩), f z.1) =
        ∏ z : GammaJetSlot mult, if z < toLex ⟨a, m⟩ then f z.1 else 1 :=
          Finset.prod_filter _ _
    _ = ∏ i : Fin r, ∏ q : Fin (mult i),
        if (toLex ⟨i, q⟩ : GammaJetSlot mult) < toLex ⟨a, m⟩ then f i else 1 := by
          exact Fintype.prod_sigma _
    _ = ∏ i : Fin r,
        if i < a then f i ^ mult i else if i = a then f i ^ (m : ℕ) else 1 := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i < a
          · have hcond : ∀ q : Fin (mult i),
                (toLex ⟨i, q⟩ : GammaJetSlot mult) < toLex ⟨a, m⟩ := by
                intro q
                exact Sigma.Lex.lt_def.mpr (Or.inl hi)
            simp only [if_pos hi, hcond, if_true, Finset.prod_const, Finset.card_univ,
              Fintype.card_fin]
          · by_cases hieq : i = a
            · subst i
              have hcond : ∀ q : Fin (mult a),
                  ((toLex ⟨a, q⟩ : GammaJetSlot mult) < toLex ⟨a, m⟩ ↔ q < m) := by
                intro q
                rw [Sigma.Lex.lt_def]
                constructor
                · rintro (ha | ⟨heq, hq⟩)
                  · exact (lt_irrefl a ha).elim
                  · simpa using hq
                · intro hq
                  exact Or.inr ⟨rfl, hq⟩
              simp only [lt_self_iff_false, ↓reduceIte, hcond]
              exact prod_fin_ite_lt (mult a) m (f a)
            · have hgt : a < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hieq)
              have hcond : ∀ q : Fin (mult i),
                  ¬(toLex ⟨i, q⟩ : GammaJetSlot mult) < toLex ⟨a, m⟩ := by
                intro q hq
                exact (Sigma.Lex.lt_def.mp hq).elim hgt.not_gt (fun heq ↦ hieq heq.1)
              simp only [hi, ↓reduceIte, hieq, hcond, Finset.prod_const_one]
    _ = (∏ i ∈ Finset.Iio a, f i ^ mult i) * f a ^ (m : ℕ) := by
          rw [Finset.prod_ite]
          rw [show Finset.filter (fun i : Fin r => i < a) Finset.univ = Finset.Iio a by
            ext; simp]
          congr 1
          rw [Finset.prod_ite]
          have hfilterEq :
              (Finset.filter (fun i : Fin r => ¬i < a) Finset.univ).filter
                (fun i => i = a) = {a} := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · exact And.right
            · intro h
              exact ⟨h ▸ lt_irrefl a, h⟩
          rw [hfilterEq]
          simp

theorem prod_Iio_orderIso {n : ℕ} {α : Type*} [Fintype α] [LinearOrder α]
    (e : Fin n ≃o α) (k : Fin n) (f : α → M) :
    (∏ j ∈ Finset.Iio k, f (e j)) =
      ∏ a ∈ Finset.univ.filter (fun a => a < e k), f a := by
  classical
  calc
    (∏ j ∈ Finset.Iio k, f (e j)) =
        ∏ a ∈ (Finset.Iio k).map e.toEmbedding, f a :=
          (Finset.prod_map (Finset.Iio k) e.toEmbedding f).symm
    _ = ∏ a ∈ Finset.univ.filter (fun a => a < e k), f a := by
      congr 1
      ext a
      simp only [Finset.mem_map, Finset.mem_Iio, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact e.lt_iff_lt.mpr hj
      · intro ha
        refine ⟨e.symm a, e.lt_iff_lt.mp ?_, e.apply_symm_apply a⟩
        simpa using ha

theorem gammaJetNewtonPolynomial_eq_blockProduct {r : ℕ}
    (x : Fin r → K) (mult : Fin r → ℕ) (k : Fin (∑ i, mult i)) :
    gammaJetNewtonPolynomial x mult k =
      (∏ i ∈ Finset.Iio (gammaJetSlotNode mult k),
          (X - C (x i)) ^ mult i) *
        (X - C (x (gammaJetSlotNode mult k))) ^ gammaJetSlotOrder mult k := by
  unfold gammaJetNewtonPolynomial gammaJetSlotNode gammaJetSlotOrder
  rw [prod_Iio_orderIso (gammaJetSlotOrderIso mult) k
      (fun z : GammaJetSlot mult => X - C (x z.1))]
  exact prod_gammaJetSlot_Iio mult ((gammaJetSlotOrderIso mult) k)
    (fun i => X - C (x i))

theorem iterate_derivative_eval_eq_zero_of_pow_succ_dvd
    {P : K[X]} {c : K} {m : ℕ} (hdvd : (X - C c) ^ (m + 1) ∣ P) :
    ((derivative^[m]) P).eval c = 0 := by
  have hpow : (X - C c) ^ ((m + 1) - m) ∣ (derivative^[m]) P :=
    pow_sub_dvd_iterate_derivative_of_pow_dvd m hdvd
  have hlin : X - C c ∣ (derivative^[m]) P := by
    simpa using hpow
  exact Polynomial.dvd_iff_isRoot.mp hlin

theorem transport_fin_val {ι : Type*} (d : ι → ℕ) {i j : ι} (h : i = j)
    (q : Fin (d i)) :
    (((h ▸ q) : Fin (d j)) : ℕ) = (q : ℕ) := by
  subst j
  rfl

theorem eval_iterate_derivative_pow_X_sub_C_mul (c : K) (m : ℕ) (Q : K[X]) :
    ((derivative^[m]) ((X - C c) ^ m * Q)).eval c =
      (m.factorial : K) * Q.eval c := by
  rw [iterate_derivative_mul, eval_finsetSum,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, m.sub_zero,
      iterate_derivative_X_sub_pow_self, Function.iterate_zero_apply,
      eval_mul, eval_natCast]
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow, eval_smul, eval_mul, eval_smul, eval_pow,
      Nat.sub_sub_self (Finset.mem_range_succ_iff.mp hb), eval_sub, eval_X, eval_C,
      sub_self, zero_pow hb0, smul_zero, zero_mul, smul_zero]

theorem gammaJetNewtonPolynomial_jetEval_eq_zero_of_lt {r : ℕ}
    (x : Fin r → K) (mult : Fin r → ℕ) {j k : Fin (∑ i, mult i)} (hjk : j < k) :
    ((derivative^[gammaJetSlotOrder mult j])
      (gammaJetNewtonPolynomial x mult k)).eval
        (x (gammaJetSlotNode mult j)) = 0 := by
  apply iterate_derivative_eval_eq_zero_of_pow_succ_dvd
  rw [gammaJetNewtonPolynomial_eq_blockProduct]
  have hslot : (gammaJetSlotOrderIso mult j) < gammaJetSlotOrderIso mult k :=
    (gammaJetSlotOrderIso mult).lt_iff_lt.mpr hjk
  rcases Sigma.Lex.lt_def.mp hslot with hnode | ⟨hnode, horder⟩
  · have hlocal :
        (X - C (x (gammaJetSlotNode mult j))) ^ mult (gammaJetSlotNode mult j) ∣
          ∏ i ∈ Finset.Iio (gammaJetSlotNode mult k), (X - C (x i)) ^ mult i := by
      apply Finset.dvd_prod_of_mem
      exact Finset.mem_Iio.mpr hnode
    have hpow :
        (X - C (x (gammaJetSlotNode mult j))) ^
            (gammaJetSlotOrder mult j + 1) ∣
          (X - C (x (gammaJetSlotNode mult j))) ^ mult (gammaJetSlotNode mult j) := by
      apply pow_dvd_pow
      exact Nat.succ_le_iff.mpr ((gammaJetSlotOrderIso mult j).2.isLt)
    exact dvd_mul_of_dvd_left (hpow.trans hlocal) _
  · have hnode' : gammaJetSlotNode mult j = gammaJetSlotNode mult k := hnode
    have horder' : gammaJetSlotOrder mult j < gammaJetSlotOrder mult k := by
      have hval :
          (((hnode ▸ (gammaJetSlotOrderIso mult j).2) :
              Fin (mult (gammaJetSlotOrderIso mult k).1)) : ℕ) =
            ((gammaJetSlotOrderIso mult j).2 : ℕ) :=
        transport_fin_val mult hnode (gammaJetSlotOrderIso mult j).2
      change (((hnode ▸ (gammaJetSlotOrderIso mult j).2) :
          Fin (mult (gammaJetSlotOrderIso mult k).1)) : ℕ) <
        ((gammaJetSlotOrderIso mult k).2 : ℕ) at horder
      simpa [gammaJetSlotOrder, hval] using horder
    rw [hnode']
    exact dvd_mul_of_dvd_right
      (pow_dvd_pow _ (Nat.succ_le_iff.mpr horder')) _

theorem gammaJetNewtonPolynomial_jetEval_diagonal {r : ℕ}
    (x : Fin r → K) (mult : Fin r → ℕ) (k : Fin (∑ i, mult i)) :
    ((derivative^[gammaJetSlotOrder mult k])
      (gammaJetNewtonPolynomial x mult k)).eval
        (x (gammaJetSlotNode mult k)) =
      ((gammaJetSlotOrder mult k).factorial : K) *
        ∏ i ∈ Finset.Iio (gammaJetSlotNode mult k),
          (x (gammaJetSlotNode mult k) - x i) ^ mult i := by
  rw [gammaJetNewtonPolynomial_eq_blockProduct, mul_comm,
    eval_iterate_derivative_pow_X_sub_C_mul]
  congr 1
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_pow, eval_sub, eval_X, eval_C]

def confluentPolynomialJetMatrix {r : ℕ} (x : Fin r → K) (mult : Fin r → ℕ)
    (p : Fin (∑ i, mult i) → K[X]) :
    Matrix (Fin (∑ i, mult i)) (Fin (∑ i, mult i)) K :=
  polynomialJetEvalMatrix
    (fun k => x (gammaJetSlotNode mult k))
    (gammaJetSlotOrder mult) p

theorem det_confluentPolynomialJetMatrix_newton {r : ℕ}
    (x : Fin r → K) (mult : Fin r → ℕ) :
    (confluentPolynomialJetMatrix x mult
      (gammaJetNewtonPolynomial x mult)).det =
      ∏ k : Fin (∑ i, mult i),
        ((gammaJetSlotOrder mult k).factorial : K) *
          ∏ i ∈ Finset.Iio (gammaJetSlotNode mult k),
            (x (gammaJetSlotNode mult k) - x i) ^ mult i := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_congr rfl
    intro k _
    exact gammaJetNewtonPolynomial_jetEval_diagonal x mult k
  · intro i j hij
    apply gammaJetNewtonPolynomial_jetEval_eq_zero_of_lt x mult
    exact hij

theorem det_confluentPolynomialJetMatrix_eq_newton {r : ℕ} [Nontrivial K]
    (x : Fin r → K) (mult : Fin r → ℕ)
    (p : Fin (∑ i, mult i) → K[X])
    (hdeg : ∀ k, (p k).natDegree = (k : ℕ)) (hmonic : ∀ k, (p k).Monic) :
    (confluentPolynomialJetMatrix x mult p).det =
      (confluentPolynomialJetMatrix x mult
        (gammaJetNewtonPolynomial x mult)).det := by
  exact det_polynomialJetEvalMatrix_eq_of_monic_successive
    (fun k => x (gammaJetSlotNode mult k)) (gammaJetSlotOrder mult)
    p (gammaJetNewtonPolynomial x mult) hdeg hmonic
    (gammaJetNewtonPolynomial_natDegree x mult)
    (gammaJetNewtonPolynomial_monic x mult)

theorem prod_gammaJetSlotOrderIso {r : ℕ} (mult : Fin r → ℕ)
    (F : (i : Fin r) → Fin (mult i) → M) :
    (∏ k : Fin (∑ i, mult i),
      F (gammaJetSlotNode mult k)
        ⟨gammaJetSlotOrder mult k,
          (gammaJetSlotOrderIso mult k).2.isLt⟩) =
      ∏ i : Fin r, ∏ m : Fin (mult i), F i m := by
  calc
    _ = ∏ z : GammaJetSlot mult, F z.1 z.2 := by
      apply Fintype.prod_equiv (gammaJetSlotOrderIso mult).toEquiv
      intro k
      rfl
    _ = _ := Fintype.prod_sigma _

theorem prod_Iio_eq_prod_Ioi {r : ℕ} (F : Fin r → Fin r → M) :
    (∏ i : Fin r, ∏ j ∈ Finset.Iio i, F j i) =
      ∏ j : Fin r, ∏ i ∈ Finset.Ioi j, F j i := by
  classical
  calc
    (∏ i : Fin r, ∏ j ∈ Finset.Iio i, F j i) =
        ∏ i : Fin r, ∏ j : Fin r, if j < i then F j i else 1 := by
          apply Finset.prod_congr rfl
          intro i _
          rw [← Finset.prod_filter]
          congr 1
          ext j
          simp
    _ = ∏ j : Fin r, ∏ i : Fin r, if j < i then F j i else 1 :=
      Finset.prod_comm
    _ = ∏ j : Fin r, ∏ i ∈ Finset.Ioi j, F j i := by
          apply Finset.prod_congr rfl
          intro j _
          rw [← Finset.prod_filter]
          congr 1
          ext i
          simp

theorem prod_gammaJetNewtonDiagonal_eq {r : ℕ}
    (x : Fin r → K) (mult : Fin r → ℕ) :
    (∏ k : Fin (∑ i, mult i),
        ((gammaJetSlotOrder mult k).factorial : K) *
          ∏ i ∈ Finset.Iio (gammaJetSlotNode mult k),
            (x (gammaJetSlotNode mult k) - x i) ^ mult i) =
      (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : K)) *
        ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
          (x j - x i) ^ (mult i * mult j) := by
  classical
  calc
    _ = ∏ i : Fin r, ∏ m : Fin (mult i),
        ((m : ℕ).factorial : K) *
          ∏ j ∈ Finset.Iio i, (x i - x j) ^ mult j := by
      exact prod_gammaJetSlotOrderIso mult (fun i m =>
        ((m : ℕ).factorial : K) *
          ∏ j ∈ Finset.Iio i, (x i - x j) ^ mult j)
    _ = ∏ i : Fin r,
        (∏ m : Fin (mult i), ((m : ℕ).factorial : K)) *
          (∏ j ∈ Finset.Iio i, (x i - x j) ^ mult j) ^ mult i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.prod_mul_distrib]
      congr 1
      simp
    _ = (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : K)) *
        ∏ i : Fin r,
          (∏ j ∈ Finset.Iio i, (x i - x j) ^ mult j) ^ mult i := by
      exact Finset.prod_mul_distrib
    _ = (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : K)) *
        ∏ i : Fin r, ∏ j ∈ Finset.Iio i,
          (x i - x j) ^ (mult j * mult i) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp_rw [pow_mul]
      exact (Finset.prod_pow (Finset.Iio i) (mult i)
        (fun j => (x i - x j) ^ mult j)).symm
    _ = (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : K)) *
        ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
          (x j - x i) ^ (mult i * mult j) := by
      congr 1
      exact prod_Iio_eq_prod_Ioi (fun j i =>
        (x i - x j) ^ (mult j * mult i))

theorem det_confluentPolynomialJetMatrix {r : ℕ} [Nontrivial K]
    (x : Fin r → K) (mult : Fin r → ℕ)
    (p : Fin (∑ i, mult i) → K[X])
    (hdeg : ∀ k, (p k).natDegree = (k : ℕ)) (hmonic : ∀ k, (p k).Monic) :
    (confluentPolynomialJetMatrix x mult p).det =
      (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : K)) *
        ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
          (x j - x i) ^ (mult i * mult j) := by
  rw [det_confluentPolynomialJetMatrix_eq_newton x mult p hdeg hmonic,
    det_confluentPolynomialJetMatrix_newton,
    prod_gammaJetNewtonDiagonal_eq]

theorem iteratedDeriv_Gamma_add_nat_eq_sum (z : ℂ) (n m : ℕ)
    (hz : ∀ p : ℕ, z ≠ -(p : ℂ)) :
    iteratedDeriv m Complex.Gamma (z + n) =
      ∑ a ∈ Finset.range (m + 1),
        m.choose a * ((derivative^[a]) (ascPochhammer ℂ n)).eval z *
          iteratedDeriv (m - a) Complex.Gamma z := by
  have hzn : ∀ k < n, z + k ≠ 0 := by
    intro k _ hk
    apply hz k
    linear_combination hk
  have hev : ∀ᶠ w : ℂ in 𝓝 z, ∀ k ∈ Finset.range n, w + (k : ℂ) ≠ 0 := by
    rw [Finset.eventually_all]
    intro k hk
    exact (continuousAt_id.add continuousAt_const).eventually_ne
      (hzn k (Finset.mem_range.mp hk))
  have hEq : (fun w : ℂ => Complex.Gamma (w + n)) =ᶠ[𝓝 z]
      (fun w => (ascPochhammer ℂ n).eval w) * Complex.Gamma := by
    filter_upwards [hev] with w hw
    exact Complex.Gamma_add_nat_eq_ascPochhammer_mul w n
      (fun k hk => hw k (Finset.mem_range.mpr hk))
  have hshift : iteratedDeriv m Complex.Gamma (z + n) =
      iteratedDeriv m (fun w : ℂ => Complex.Gamma (w + n)) z :=
    (congrFun (iteratedDeriv_comp_add_const m Complex.Gamma n) z).symm
  have hpoly : ContDiffAt ℂ m (fun w : ℂ => (ascPochhammer ℂ n).eval w) z := by
    simpa [Polynomial.aeval_def] using
      ((Polynomial.contDiff_aeval (ascPochhammer ℂ n) (m : WithTop ℕ∞)).contDiffAt)
  rw [hshift, hEq.iteratedDeriv_eq,
    iteratedDeriv_mul (𝕜 := ℂ) hpoly (contDiffAt_Gamma z hz m)]
  apply Finset.sum_congr rfl
  intro a _
  rw [iteratedDeriv_complexPolynomial_eval]

def confluentAscPochhammerMatrix {r : ℕ} (x : Fin r → K) (mult : Fin r → ℕ) :
    Matrix (Fin (∑ i, mult i)) (Fin (∑ i, mult i)) K :=
  fun k a => ((derivative^[gammaJetSlotOrder mult a])
    (ascPochhammer K (k : ℕ))).eval (x (gammaJetSlotNode mult a))

theorem det_confluentAscPochhammerMatrix {r : ℕ} [Nontrivial K] [NoZeroDivisors K]
    (x : Fin r → K) (mult : Fin r → ℕ) :
    (confluentAscPochhammerMatrix x mult).det =
      (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : K)) *
        ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
          (x j - x i) ^ (mult i * mult j) := by
  rw [← Matrix.det_transpose]
  change (confluentPolynomialJetMatrix x mult
    (fun k => ascPochhammer K (k : ℕ))).det = _
  apply det_confluentPolynomialJetMatrix
  · intro k
    exact ascPochhammer_natDegree K (k : ℕ)
  · intro k
    exact monic_ascPochhammer K (k : ℕ)

def gammaJetColumnChange {r : ℕ} (x : Fin r → ℂ) (mult : Fin r → ℕ) :
    Matrix (Fin (∑ i, mult i)) (Fin (∑ i, mult i)) ℂ :=
  fun a b =>
    if gammaJetSlotNode mult a = gammaJetSlotNode mult b ∧
        gammaJetSlotOrder mult a ≤ gammaJetSlotOrder mult b then
      (gammaJetSlotOrder mult b).choose (gammaJetSlotOrder mult a) *
        iteratedDeriv (gammaJetSlotOrder mult b - gammaJetSlotOrder mult a)
          Complex.Gamma (x (gammaJetSlotNode mult b))
    else 0

@[simp] theorem gammaJetColumnChange_diagonal {r : ℕ}
    (x : Fin r → ℂ) (mult : Fin r → ℕ) (a : Fin (∑ i, mult i)) :
    gammaJetColumnChange x mult a a = Complex.Gamma (x (gammaJetSlotNode mult a)) := by
  simp [gammaJetColumnChange]

theorem gammaJetColumnChange_blockTriangular {r : ℕ}
    (x : Fin r → ℂ) (mult : Fin r → ℕ) :
    Matrix.BlockTriangular (gammaJetColumnChange x mult) id := by
  intro a b hba
  have hslot : gammaJetSlotOrderIso mult b < gammaJetSlotOrderIso mult a :=
    (gammaJetSlotOrderIso mult).lt_iff_lt.mpr hba
  rcases Sigma.Lex.lt_def.mp hslot with hnode | ⟨hnode, horder⟩
  · rw [gammaJetColumnChange, if_neg]
    intro h
    exact (ne_of_gt hnode) h.1
  · have horder' : gammaJetSlotOrder mult b < gammaJetSlotOrder mult a := by
      have hval :
          (((hnode ▸ (gammaJetSlotOrderIso mult b).2) :
              Fin (mult (gammaJetSlotOrderIso mult a).1)) : ℕ) =
            ((gammaJetSlotOrderIso mult b).2 : ℕ) :=
        transport_fin_val mult hnode (gammaJetSlotOrderIso mult b).2
      change (((hnode ▸ (gammaJetSlotOrderIso mult b).2) :
          Fin (mult (gammaJetSlotOrderIso mult a).1)) : ℕ) <
        ((gammaJetSlotOrderIso mult a).2 : ℕ) at horder
      simpa [gammaJetSlotOrder, hval] using horder
    rw [gammaJetColumnChange, if_neg]
    intro h
    exact (Nat.not_le_of_lt horder') h.2

theorem det_gammaJetColumnChange {r : ℕ}
    (x : Fin r → ℂ) (mult : Fin r → ℕ) :
    (gammaJetColumnChange x mult).det =
      ∏ i : Fin r, Complex.Gamma (x i) ^ mult i := by
  rw [Matrix.det_of_upperTriangular (gammaJetColumnChange_blockTriangular x mult)]
  simp_rw [gammaJetColumnChange_diagonal]
  calc
    (∏ a : Fin (∑ i, mult i), Complex.Gamma (x (gammaJetSlotNode mult a))) =
        ∏ i : Fin r, ∏ _m : Fin (mult i), Complex.Gamma (x i) := by
      exact prod_gammaJetSlotOrderIso mult (fun i _ => Complex.Gamma (x i))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      simp

theorem sum_mul_gammaJetColumnChange {r : ℕ}
    (x : Fin r → ℂ) (mult : Fin r → ℕ)
    (F : Fin r → ℕ → ℂ) (b : Fin (∑ i, mult i)) :
    (∑ a : Fin (∑ i, mult i),
        F (gammaJetSlotNode mult a) (gammaJetSlotOrder mult a) *
          gammaJetColumnChange x mult a b) =
      ∑ p ∈ Finset.range (gammaJetSlotOrder mult b + 1),
        F (gammaJetSlotNode mult b) p *
          ((gammaJetSlotOrder mult b).choose p *
            iteratedDeriv (gammaJetSlotOrder mult b - p) Complex.Gamma
              (x (gammaJetSlotNode mult b))) := by
  classical
  let eb := gammaJetSlotOrderIso mult b
  calc
    _ = ∑ z : GammaJetSlot mult,
        F z.1 (z.2 : ℕ) *
          (if z.1 = eb.1 ∧ (z.2 : ℕ) ≤ (eb.2 : ℕ) then
            (eb.2 : ℕ).choose (z.2 : ℕ) *
              iteratedDeriv ((eb.2 : ℕ) - (z.2 : ℕ)) Complex.Gamma (x eb.1)
          else 0) := by
      apply Fintype.sum_equiv (gammaJetSlotOrderIso mult).toEquiv
      intro a
      simp [gammaJetColumnChange, gammaJetSlotNode, gammaJetSlotOrder, eb]
    _ = ∑ i : Fin r, ∑ q : Fin (mult i),
        F i (q : ℕ) *
          (if i = eb.1 ∧ (q : ℕ) ≤ (eb.2 : ℕ) then
            (eb.2 : ℕ).choose (q : ℕ) *
              iteratedDeriv ((eb.2 : ℕ) - (q : ℕ)) Complex.Gamma (x eb.1)
          else 0) := Fintype.sum_sigma _
    _ = ∑ q : Fin (mult eb.1),
        F eb.1 (q : ℕ) *
          (if (q : ℕ) ≤ (eb.2 : ℕ) then
            (eb.2 : ℕ).choose (q : ℕ) *
              iteratedDeriv ((eb.2 : ℕ) - (q : ℕ)) Complex.Gamma (x eb.1)
          else 0) := by
      rw [Fintype.sum_eq_single eb.1]
      · apply Finset.sum_congr rfl
        intro q _
        simp
      · intro i hi
        apply Finset.sum_eq_zero
        intro q _
        simp [hi]
    _ = ∑ p ∈ Finset.range ((eb.2 : ℕ) + 1),
        F eb.1 p * ((eb.2 : ℕ).choose p *
          iteratedDeriv ((eb.2 : ℕ) - p) Complex.Gamma (x eb.1)) := by
      rw [Fin.sum_univ_eq_sum_range (fun q : ℕ =>
        F eb.1 q *
          (if q ≤ (eb.2 : ℕ) then
            (eb.2 : ℕ).choose q *
              iteratedDeriv ((eb.2 : ℕ) - q) Complex.Gamma (x eb.1)
          else 0)) (mult eb.1)]
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    _ = _ := rfl

def confluentGammaShiftMatrix {r : ℕ} (s : ℂ) (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) :
    Matrix (Fin (∑ i, mult i)) (Fin (∑ i, mult i)) ℂ :=
  fun k a => iteratedDeriv (gammaJetSlotOrder mult a) Complex.Gamma
    (s + shift (gammaJetSlotNode mult a) + (k : ℕ))

theorem confluentGammaShiftMatrix_eq_mul {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ)) :
    confluentGammaShiftMatrix s shift mult =
      confluentAscPochhammerMatrix (fun i => s + shift i) mult *
        gammaJetColumnChange (fun i => s + shift i) mult := by
  ext k b
  rw [confluentGammaShiftMatrix, Matrix.mul_apply]
  simp only [confluentAscPochhammerMatrix]
  rw [sum_mul_gammaJetColumnChange (fun i => s + shift i) mult
      (fun i p => ((derivative^[p]) (ascPochhammer ℂ (k : ℕ))).eval (s + shift i)) b]
  have hGamma := iteratedDeriv_Gamma_add_nat_eq_sum
    (s + shift (gammaJetSlotNode mult b)) (k : ℕ)
    (gammaJetSlotOrder mult b) (hpole (gammaJetSlotNode mult b))
  rw [hGamma]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Equation (5): exact confluent Gamma Casoratian for arbitrary positive or zero multiplicities. -/
theorem det_confluentGammaShiftMatrix {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ)) :
    (confluentGammaShiftMatrix s shift mult).det =
      (∏ i : Fin r, Complex.Gamma (s + shift i) ^ mult i) *
        (∏ i : Fin r, ∏ m : Fin (mult i), ((m : ℕ).factorial : ℂ)) *
          ∏ i : Fin r, ∏ j ∈ Finset.Ioi i,
            (shift j - shift i) ^ (mult i * mult j) := by
  rw [confluentGammaShiftMatrix_eq_mul s shift mult hpole, Matrix.det_mul,
    det_confluentAscPochhammerMatrix, det_gammaJetColumnChange]
  simp only [add_sub_add_left_eq_sub]
  ring

theorem det_confluentGammaShiftMatrix_ne_zero {r : ℕ}
    (s : ℂ) (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift)
    (hpole : ∀ i (p : ℕ), s + shift i ≠ -(p : ℂ)) :
    (confluentGammaShiftMatrix s shift mult).det ≠ 0 := by
  rw [det_confluentGammaShiftMatrix s shift mult hpole]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact pow_ne_zero _ (Complex.Gamma_ne_zero (hpole i))
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro m _
      exact_mod_cast Nat.factorial_ne_zero m
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact pow_ne_zero _ (sub_ne_zero.mpr
      (hshift.ne (ne_of_gt (Finset.mem_Ioi.mp hj))))

end
end GaloisForLFunctions
