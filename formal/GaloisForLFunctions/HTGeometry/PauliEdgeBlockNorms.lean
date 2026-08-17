import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The two norms of a two-site Pauli interaction

The nine genuinely coupling two-site Pauli words are Hilbert--Schmidt orthogonal with squared
Hilbert--Schmidt norm four, so an interaction with coefficient vector `J` has squared
Hilbert--Schmidt norm `4‖J‖²`.  Each word is a Hermitian involution, hence has operator norm one,
so the triangle inequality and Cauchy--Schwarz over the nine words bound the operator norm by
`3‖J‖`.  In the other direction the edge space has dimension four, so the squared Hilbert--Schmidt
norm never exceeds four times the squared operator norm, and the operator norm is at least `‖J‖`.

Both comparisons are exact in the exponent: the operator norm of a two-site interaction is
equivalent to the Euclidean norm of its nine coefficients, with the explicit constants one and
three.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section HilbertSchmidt

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Hilbert--Schmidt norm of a finite matrix. -/
def hsNormSq (A : Matrix n n ℂ) : ℝ := ∑ y, ∑ x, ‖A x y‖ ^ 2

theorem hsNormSq_nonneg (A : Matrix n n ℂ) : 0 ≤ hsNormSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

/-- The complex form of the squared Hilbert--Schmidt norm. -/
theorem hsNormSq_eq_sum_star (A : Matrix n n ℂ) :
    ((hsNormSq A : ℝ) : ℂ) = ∑ y, ∑ x, star (A x y) * A x y := by
  rw [hsNormSq]
  push_cast
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- **One column of a matrix is shorter than its operator norm.** -/
theorem sum_sq_column_le (A : Matrix n n ℂ) (y : n) :
    (∑ x, ‖A x y‖ ^ 2) ≤ ‖A‖ ^ 2 := by
  have hsingle : ‖(EuclideanSpace.single y (1 : ℂ))‖ = 1 := by simp
  have hbound := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single y (1 : ℂ))
  rw [hsingle, mul_one] at hbound
  have hvec : (A *ᵥ (EuclideanSpace.single y (1 : ℂ)).ofLp) = fun x => A x y := by
    funext x
    simp [Matrix.mulVec_apply]
  rw [hvec] at hbound
  have hnorm : ‖(EuclideanSpace.equiv n ℂ).symm (fun x => A x y)‖
      = Real.sqrt (∑ x, ‖A x y‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    rfl
  rw [hnorm] at hbound
  have hsqrt := Real.sq_sqrt
    (Finset.sum_nonneg fun x _ => by positivity : (0:ℝ) ≤ ∑ x, ‖A x y‖ ^ 2)
  nlinarith [Real.sqrt_nonneg (∑ x, ‖A x y‖ ^ 2), norm_nonneg A]

/-- **The Hilbert--Schmidt norm is at most the dimension times the operator norm.** -/
theorem hsNormSq_le_card_mul_sq (A : Matrix n n ℂ) :
    hsNormSq A ≤ (Fintype.card n : ℝ) * ‖A‖ ^ 2 := by
  calc hsNormSq A = ∑ y, ∑ x, ‖A x y‖ ^ 2 := rfl
    _ ≤ ∑ _y : n, ‖A‖ ^ 2 := Finset.sum_le_sum fun y _ => sum_sq_column_le A y
    _ = (Fintype.card n : ℝ) * ‖A‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end HilbertSchmidt

section PauliNorm

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **Every Pauli string has operator norm one.** -/
theorem l2_opNorm_finitePauliMatrix (P : σ → Option (Fin 3)) :
    ‖finitePauliMatrix P‖ = 1 := by
  have hherm : (finitePauliMatrix P)ᴴ = finitePauliMatrix P := finitePauliMatrix_isHermitian P
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (finitePauliMatrix P)
  rw [hherm, finitePauliMatrix_mul_self] at h
  have hone : ‖(1 : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)‖ = 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    simp
  rw [hone] at h
  nlinarith [norm_nonneg (finitePauliMatrix P)]

/-- **The Hilbert--Schmidt pairing of two Pauli strings in matrix form.** -/
theorem sum_star_finitePauliMatrix (P Q : σ → Option (Fin 3)) :
    (∑ y, ∑ x, star (finitePauliMatrix P x y) * finitePauliMatrix Q x y)
      = finitePauliHilbertSchmidt P Q := by
  classical
  have hpt : ∀ x y : FiniteQubitConfiguration σ,
      star (finitePauliMatrix P x y) * finitePauliMatrix Q x y
        = ∏ s, star (boolPauliOptionEntry (P s) (x s, y s)) *
            boolPauliOptionEntry (Q s) (x s, y s) := by
    intro x y
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [finitePauliMatrix]
    exact map_prod (starRingEnd ℂ) _ Finset.univ
  calc (∑ y, ∑ x, star (finitePauliMatrix P x y) * finitePauliMatrix Q x y)
      = ∑ y : FiniteQubitConfiguration σ, ∑ x : FiniteQubitConfiguration σ, ∏ s,
          star (boolPauliOptionEntry (P s) (x s, y s)) *
            boolPauliOptionEntry (Q s) (x s, y s) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => hpt x y
    _ = ∑ p : (σ → Bool) × (σ → Bool), ∏ s,
          star (boolPauliOptionEntry (P s) (p.2 s, p.1 s)) *
            boolPauliOptionEntry (Q s) (p.2 s, p.1 s) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ xy : σ → Bool × Bool, ∏ s,
          star (boolPauliOptionEntry (P s) (xy s)) *
            boolPauliOptionEntry (Q s) (xy s) := by
        refine (Fintype.sum_equiv
          (((Equiv.arrowProdEquivProdArrow σ (fun _ => Bool) (fun _ => Bool)).trans
            (Equiv.prodComm _ _))) _ _ ?_).symm
        intro xy
        rfl
    _ = finitePauliHilbertSchmidt P Q := rfl

/-- **A Pauli combination is bounded by the Cauchy--Schwarz norm of its coefficients.**  Each Pauli
string has operator norm one, so a real combination of `N` of them has operator norm at most
`√N` times the Euclidean norm of the coefficients. -/
theorem l2_opNorm_pauliCombination_le {κ : Type*} [Fintype κ]
    (P : κ → σ → Option (Fin 3)) (J : κ → ℝ) :
    ‖∑ k, ((J k : ℝ) : ℂ) • finitePauliMatrix (P k)‖
      ≤ Real.sqrt (Fintype.card κ) * Real.sqrt (∑ k, J k ^ 2) := by
  classical
  have hsum : ‖∑ k, ((J k : ℝ) : ℂ) • finitePauliMatrix (P k)‖ ≤ ∑ k, |J k| := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, l2_opNorm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hsq : (∑ k, |J k|) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, J k ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset κ)) (f := fun k => |J k|)
    rw [Finset.card_univ] at h
    calc (∑ k, |J k|) ^ 2 ≤ (Fintype.card κ : ℝ) * ∑ k, |J k| ^ 2 := h
      _ = (Fintype.card κ : ℝ) * ∑ k, J k ^ 2 := by
          refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
          rw [sq_abs]
  have hnn : 0 ≤ ∑ k, |J k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hprod : Real.sqrt (Fintype.card κ) * Real.sqrt (∑ k, J k ^ 2)
      = Real.sqrt ((Fintype.card κ : ℝ) * ∑ k, J k ^ 2) :=
    (Real.sqrt_mul (by positivity) _).symm
  rw [hprod]
  refine le_trans hsum ?_
  rw [show (∑ k, |J k|) = Real.sqrt ((∑ k, |J k|) ^ 2) from (Real.sqrt_sq hnn).symm]
  exact Real.sqrt_le_sqrt hsq

end PauliNorm

/-- Swapping the outer and inner pair of a fourfold finite sum. -/
theorem sum_comm_four {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc (∑ a, ∑ b, ∑ c, ∑ d, f a b c d)
      = ∑ p : α × β, ∑ q : γ × δ, f p.1 p.2 q.1 q.2 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Fintype.sum_prod_type]
    _ = ∑ q : γ × δ, ∑ p : α × β, f p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Fintype.sum_prod_type]

section Edge

/-- The nine genuinely coupling two-site Pauli words. -/
def edgeWord (ab : Fin 3 × Fin 3) : Bool → Option (Fin 3) :=
  fun s => if s then some ab.2 else some ab.1

theorem edgeWord_injective : Function.Injective edgeWord := by
  intro ab cd h
  have h1 := congrFun h false
  have h2 := congrFun h true
  simp only [edgeWord, if_pos, Bool.false_eq_true] at h1 h2
  exact Prod.ext (by simpa using h1) (by simpa using h2)

/-- The interaction across one edge with the given nine coefficients. -/
def edgeInteraction (J : Fin 3 × Fin 3 → ℝ) :
    Matrix (FiniteQubitConfiguration Bool) (FiniteQubitConfiguration Bool) ℂ :=
  ∑ ab, ((J ab : ℝ) : ℂ) • finitePauliMatrix (edgeWord ab)

/-- The Euclidean norm of the nine edge coefficients. -/
def edgeRho (J : Fin 3 × Fin 3 → ℝ) : ℝ := Real.sqrt (∑ ab, J ab ^ 2)

theorem edgeRho_nonneg (J : Fin 3 × Fin 3 → ℝ) : 0 ≤ edgeRho J := Real.sqrt_nonneg _

theorem edgeRho_sq (J : Fin 3 × Fin 3 → ℝ) : edgeRho J ^ 2 = ∑ ab, J ab ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)

/-- **`(21)`, the Hilbert--Schmidt half.**  The squared Hilbert--Schmidt norm of the edge
interaction is four times the squared coefficient norm. -/
theorem hsNormSq_edgeInteraction (J : Fin 3 × Fin 3 → ℝ) :
    hsNormSq (edgeInteraction J) = 4 * edgeRho J ^ 2 := by
  classical
  have hcomplex : ((hsNormSq (edgeInteraction J) : ℝ) : ℂ) = ((4 * edgeRho J ^ 2 : ℝ) : ℂ) := by
    rw [hsNormSq_eq_sum_star]
    have hexp : ∀ x y : FiniteQubitConfiguration Bool,
        star (edgeInteraction J x y) * edgeInteraction J x y
          = ∑ ab, ∑ cd, ((J ab : ℝ) : ℂ) * ((J cd : ℝ) : ℂ) *
              (star (finitePauliMatrix (edgeWord ab) x y) *
                finitePauliMatrix (edgeWord cd) x y) := by
      intro x y
      have hval : edgeInteraction J x y
          = ∑ ab, ((J ab : ℝ) : ℂ) * finitePauliMatrix (edgeWord ab) x y := by
        rw [edgeInteraction]
        simp [Matrix.sum_apply, Matrix.smul_apply]
      rw [hval, show star (∑ ab, ((J ab : ℝ) : ℂ) * finitePauliMatrix (edgeWord ab) x y)
            = ∑ ab, star (((J ab : ℝ) : ℂ) * finitePauliMatrix (edgeWord ab) x y) from
          map_sum (starRingEnd ℂ) _ Finset.univ, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl fun cd _ => ?_
      rw [star_mul', RCLike.star_def, Complex.conj_ofReal]
      ring
    calc (∑ y, ∑ x, star (edgeInteraction J x y) * edgeInteraction J x y)
        = ∑ y, ∑ x, ∑ ab, ∑ cd, ((J ab : ℝ) : ℂ) * ((J cd : ℝ) : ℂ) *
            (star (finitePauliMatrix (edgeWord ab) x y) *
              finitePauliMatrix (edgeWord cd) x y) :=
          Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => hexp x y
      _ = ∑ ab, ∑ cd, ∑ y : FiniteQubitConfiguration Bool, ∑ x : FiniteQubitConfiguration Bool,
            ((J ab : ℝ) : ℂ) * ((J cd : ℝ) : ℂ) *
              (star (finitePauliMatrix (edgeWord ab) x y) *
                finitePauliMatrix (edgeWord cd) x y) := sum_comm_four _
      _ = ∑ ab, ∑ cd, ((J ab : ℝ) : ℂ) * ((J cd : ℝ) : ℂ) *
            (∑ y, ∑ x, star (finitePauliMatrix (edgeWord ab) x y) *
              finitePauliMatrix (edgeWord cd) x y) := by
          refine Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl fun cd _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ ab, ∑ cd, ((J ab : ℝ) : ℂ) * ((J cd : ℝ) : ℂ) *
            (if edgeWord ab = edgeWord cd then (2 : ℂ) ^ Fintype.card Bool else 0) := by
          refine Finset.sum_congr rfl fun ab _ => Finset.sum_congr rfl fun cd _ => ?_
          rw [sum_star_finitePauliMatrix, finitePauliHilbertSchmidt_eq]
      _ = ((4 * edgeRho J ^ 2 : ℝ) : ℂ) := by
          have hcard : Fintype.card Bool = 2 := rfl
          simp only [hcard]
          have hinner : ∀ ab : Fin 3 × Fin 3,
              (∑ cd, ((J ab : ℝ) : ℂ) * ((J cd : ℝ) : ℂ) *
                (if edgeWord ab = edgeWord cd then (2 : ℂ) ^ 2 else 0))
                = 4 * ((J ab : ℝ) : ℂ) * ((J ab : ℝ) : ℂ) := by
            intro ab
            rw [Finset.sum_eq_single ab]
            · rw [if_pos rfl]
              ring
            · intro cd _ hcd
              rw [if_neg fun h => hcd (edgeWord_injective h).symm]
              ring
            · intro hab
              exact absurd (Finset.mem_univ ab) hab
          rw [Finset.sum_congr rfl fun ab _ => hinner ab, edgeRho_sq]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ab _ => ?_
          ring
  exact_mod_cast hcomplex

/-- **`(19)`.**  The operator norm of the edge interaction is at most three times the coefficient
norm. -/
theorem l2_opNorm_edgeInteraction_le (J : Fin 3 × Fin 3 → ℝ) :
    ‖edgeInteraction J‖ ≤ 3 * edgeRho J := by
  classical
  have hsum : ‖edgeInteraction J‖ ≤ ∑ ab, |J ab| := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ab _ => ?_)
    rw [norm_smul, l2_opNorm_finitePauliMatrix, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hcs : (∑ ab, |J ab|) ≤ 3 * edgeRho J := by
    have hsq : (∑ ab, |J ab|) ^ 2 ≤ 9 * ∑ ab, J ab ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
        (f := fun ab => |J ab|)
      have hcard : (((Finset.univ : Finset (Fin 3 × Fin 3)).card : ℕ) : ℝ) = 9 := by simp
      rw [hcard] at h
      calc (∑ ab, |J ab|) ^ 2 ≤ 9 * ∑ ab, |J ab| ^ 2 := h
        _ = 9 * ∑ ab, J ab ^ 2 := by
            refine congrArg _ (Finset.sum_congr rfl fun ab _ => ?_)
            rw [sq_abs]
    have hnn : 0 ≤ ∑ ab, |J ab| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith [edgeRho_sq J, edgeRho_nonneg J]
  linarith

/-- **`(21)`, the lower half.**  The operator norm of the edge interaction is at least the
coefficient norm. -/
theorem le_l2_opNorm_edgeInteraction (J : Fin 3 × Fin 3 → ℝ) :
    edgeRho J ≤ ‖edgeInteraction J‖ := by
  have hcard : (Fintype.card (FiniteQubitConfiguration Bool) : ℝ) = 4 := by
    simp [FiniteQubitConfiguration]
  have hle := hsNormSq_le_card_mul_sq (edgeInteraction J)
  rw [hcard, hsNormSq_edgeInteraction] at hle
  nlinarith [edgeRho_nonneg J, norm_nonneg (edgeInteraction J)]

end Edge

end

end GaloisForLFunctions.HTGeometry
