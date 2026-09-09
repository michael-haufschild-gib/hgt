import GaloisForLFunctions.HTGeometry.GomesFockTaylorGauge
import GaloisForLFunctions.HTGeometry.GomesExponentialInvariantForms
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# Complete invariant-form classification for the finite Taylor gauge action

Applying the real/complex representation distinction in Gomes, arXiv:2607.24901,
to the Gamma-factorial Fock derivative clock yields an exact positive survivor:
all complex-translation invariant sesquilinear forms are uniquely supported on the
highest jet coordinate. Their radicals are classified explicitly. Even restricting
to real translations excludes every positive metric in dimension at least two.
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Existing jet coordinates coincide with the standard matrix basis vectors. -/
theorem fockCoordVec_eq_single {N : ℕ} (k : Fin N) :
    coordVec k.val = Pi.single k (1 : ℂ) := by
  funext j
  simp [coordVec,Pi.single_apply,Fin.ext_iff,eq_comm]

/-- Matrix action on an existing coordinate jet reads exactly one matrix column. -/
theorem fockMatrix_mulVec_coord {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (k : Fin N) (i : Fin N) : (M *ᵥ coordVec k.val) i = M i k := by
  rw [fockCoordVec_eq_single,Matrix.mulVec_single_one]
  rfl

/-- The derivative clock kills the constant jet. -/
theorem fockShiftMatrix_mulVec_constant (n : ℕ) :
    fockShiftMatrix (n+1) *ᵥ coordVec 0 = 0 := by
  rw [fockShiftMatrix_mulVec]
  funext i
  change jetExt (coordVec (N := n+1) 0) (i.val+1) = 0
  rw [jetExt_coordVec (by omega)]
  simp

/-- Every nonconstant coordinate jet differentiates to its predecessor. -/
theorem fockShiftMatrix_mulVec_successor (n : ℕ) (j : Fin n) :
    fockShiftMatrix (n+1) *ᵥ coordVec j.succ.val = coordVec j.castSucc.val := by
  rw [fockShiftMatrix_mulVec]
  funext i
  change jetExt (coordVec (N := n+1) j.succ.val) (i.val+1) = _
  rw [jetExt_coordVec j.succ.isLt]
  simp [coordVec]

/-- Right annihilation by the derivative clock means that all columns except the final one
vanish, in every positive jet dimension. -/
theorem fockShiftMatrix_right_annihilator (n : ℕ) (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    H * fockShiftMatrix (n+1) = 0 ↔ ∀ j : Fin n, ∀ i : Fin (n+1), H i j.castSucc = 0 := by
  constructor
  · intro h j i
    have hc := congrArg (fun M => (M *ᵥ coordVec j.succ.val) i) h
    rw [← Matrix.mulVec_mulVec,fockShiftMatrix_mulVec_successor,
      fockMatrix_mulVec_coord,Matrix.zero_mulVec] at hc
    exact hc
  · intro h
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← fockCoordVec_eq_single]
    induction j using Fin.cases with
    | zero => rw [Fin.val_zero,← Matrix.mulVec_mulVec,fockShiftMatrix_mulVec_constant,
        Matrix.mulVec_zero,Matrix.zero_mulVec]
    | succ j =>
      rw [← Matrix.mulVec_mulVec,fockShiftMatrix_mulVec_successor,Matrix.zero_mulVec]
      funext i
      rw [fockMatrix_mulVec_coord]
      exact h j i

/-- Left annihilation by the adjoint derivative means that all rows except the final one vanish. -/
theorem fockShiftMatrix_left_annihilator (n : ℕ) (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    star (fockShiftMatrix (n+1)) * H = 0 ↔
      ∀ i : Fin n, ∀ j : Fin (n+1), H i.castSucc j = 0 := by
  constructor
  · intro h
    have hs : star H * fockShiftMatrix (n+1) = 0 := by
      simpa only [star_mul,star_star,star_zero] using congrArg star h
    have hc := (fockShiftMatrix_right_annihilator n (star H)).mp hs
    intro i j
    have hij := hc i j
    change star (H i.castSucc j) = 0 at hij
    exact star_eq_zero.mp hij
  · intro h
    have hs : star H * fockShiftMatrix (n+1) = 0 := by
      apply (fockShiftMatrix_right_annihilator n (star H)).mpr
      intro i j
      change star (H i.castSucc j) = 0
      rw [h i j,star_zero]
    simpa only [star_mul,star_star,star_zero] using congrArg star hs

/-- The sesquilinear form supported only on the highest derivative coordinate. -/
def fockTopJetForm (n : ℕ) (c : ℂ) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => if i = Fin.last n ∧ j = Fin.last n then c else 0

/-- Exact positive survivor of complex-parameter invariant-form rigidity: the complete space
of invariant forms is the one-dimensional space supported on the highest jet coordinate. -/
theorem fockTaylorMatrix_invariant_forms (n : ℕ)
    (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (∀ z : ℂ, star (fockTaylorMatrix (n+1) z) * H * fockTaylorMatrix (n+1) z = H) ↔
      H = fockTopJetForm n (H (Fin.last n) (Fin.last n)) := by
  simp only [fockTaylorMatrix]
  rw [complex_exponential_sesquilinear_invariants,
    fockShiftMatrix_left_annihilator,fockShiftMatrix_right_annihilator]
  constructor
  · rintro ⟨hl,hr⟩
    ext i j
    by_cases hi : i = Fin.last n
    · by_cases hj : j = Fin.last n
      · simp [fockTopJetForm,hi,hj]
      · have hjlt : j.val < n := by
          have hjv : j.val ≠ n := by simpa only [Fin.ext_iff,Fin.val_last] using hj
          omega
        have hzero := hr ⟨j.val,hjlt⟩ i
        change H i j = 0 at hzero
        simp [fockTopJetForm,hj,hzero]
    · have hilt : i.val < n := by
        have hiv : i.val ≠ n := by simpa only [Fin.ext_iff,Fin.val_last] using hi
        omega
      have hzero := hl ⟨i.val,hilt⟩ j
      change H i j = 0 at hzero
      simp [fockTopJetForm,hi,hzero]
  · intro h
    constructor
    · intro i j
      rw [h]
      simp [fockTopJetForm]
    · intro j i
      rw [h]
      simp [fockTopJetForm]

/-- The derivative clock has ones precisely on its first superdiagonal. -/
theorem fockShiftMatrix_apply {N : ℕ} (i j : Fin N) :
    fockShiftMatrix N i j = if i.val+1 = j.val then 1 else 0 := by
  rw [← fockMatrix_mulVec_coord (fockShiftMatrix N) j i,fockShiftMatrix_mulVec]
  exact jetExt_coordVec j.isLt (i.val+1)

/-- Even restricting translation parameters to the real axis rules out every positive
sesquilinear metric on a nontrivial finite jet space. -/
theorem fockTaylorMatrix_no_positive_metric (n : ℕ) :
    ¬ ∃ H : Matrix (Fin (n+2)) (Fin (n+2)) ℂ, H.PosDef ∧
      ∀ t : ℝ, star (fockTaylorMatrix (n+2) (t : ℂ)) * H *
        fockTaylorMatrix (n+2) (t : ℂ) = H := by
  rintro ⟨H,hpos,h⟩
  have hr : star (fockShiftMatrix (n+2)) * H + H * fockShiftMatrix (n+2) = 0 := by
    apply (real_exponential_sesquilinear_invariants (fockShiftMatrix (n+2)) H).mp
    intro t
    simpa only [fockTaylorMatrix,Complex.coe_smul] using h t
  have hl : (star (fockShiftMatrix (n+2)) * H) 0 1 = 0 := by
    simp [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,
      fockShiftMatrix_apply]
  have hd : (H * fockShiftMatrix (n+2)) 0 1 = H 0 0 := by
    rw [← fockMatrix_mulVec_coord (H * fockShiftMatrix (n+2)) 1 0,
      ← Matrix.mulVec_mulVec]
    have hs : fockShiftMatrix (n+2) *ᵥ coordVec 1 = coordVec 0 :=
      fockShiftMatrix_mulVec_successor (n+1) 0
    simp only [Fin.val_one]
    rw [hs]
    exact fockMatrix_mulVec_coord H 0 0
  have he := congrFun (congrFun hr 0) 1
  simp only [Matrix.add_apply,Matrix.zero_apply,hl,hd,zero_add] at he
  have hp : 0 < H 0 0 := hpos.diag_pos
  rw [he] at hp
  exact lt_irrefl _ hp

/-- The surviving form acts only on the highest derivative coordinate. -/
theorem fockTopJetForm_mulVec (n : ℕ) (c : ℂ) (x : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    (fockTopJetForm n c *ᵥ x) i = if i = Fin.last n then c * x (Fin.last n) else 0 := by
  by_cases hi : i = Fin.last n <;>
    simp [Matrix.mulVec,dotProduct,fockTopJetForm,hi]

/-- The radical of the surviving form is exact: either its coefficient is zero or the highest
jet coordinate vanishes. -/
theorem fockTopJetForm_kernel (n : ℕ) (c : ℂ) (x : Fin (n+1) → ℂ) :
    fockTopJetForm n c *ᵥ x = 0 ↔ c = 0 ∨ x (Fin.last n) = 0 := by
  constructor
  · intro h
    have hc := congrFun h (Fin.last n)
    rw [fockTopJetForm_mulVec,if_pos rfl] at hc
    exact mul_eq_zero.mp hc
  · intro h
    funext i
    rw [fockTopJetForm_mulVec]
    rcases h with h | h <;> simp [h]

/-- Invariant forms have a unique complex coordinate; the classification is a complete
one-dimensional parameterization, including the zero form. -/
theorem fockTaylorMatrix_invariant_form_unique (n : ℕ)
    (H : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (∀ z : ℂ, star (fockTaylorMatrix (n+1) z) * H * fockTaylorMatrix (n+1) z = H) ↔
      ∃! c : ℂ, H = fockTopJetForm n c := by
  rw [fockTaylorMatrix_invariant_forms]
  constructor
  · intro h
    refine ⟨H (Fin.last n) (Fin.last n),h,?_⟩
    intro c hc
    have he := congrFun (congrFun hc (Fin.last n)) (Fin.last n)
    simpa only [fockTopJetForm,ite_true,and_self,eq_self] using he.symm
  · rintro ⟨c,rfl,_⟩
    simp [fockTopJetForm]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
