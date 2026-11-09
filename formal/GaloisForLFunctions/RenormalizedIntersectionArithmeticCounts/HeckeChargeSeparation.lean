import GaloisForLFunctions.RHTower.MobiusCoprimeMatrixFactorization

/-!
# Integral separation by conductor dilations

All multiplicative translates of the Möbius charge separate the squarefree
coordinates of an integer probe. Tests through the original cutoff suffice.
The squarefree multiplication matrix is unimodular: divisor incidence
factors its coprimality part, and every remaining Möbius diagonal is a unit.
-/

noncomputable section
open Finset Matrix ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts

/-- Positive integer conductors in a finite window. -/
abbrev ConductorWindow := RHTower.finiteMobiusCoprimeCoordinate

/-- Squarefree arithmetic labels in an integer conductor window. -/
abbrev SquarefreeConductor (N : ℕ) := {i : ConductorWindow N // Squarefree i.val}

/-- Divisor incidence on the squarefree down-set. -/
def squarefreeDivisorMatrix (N : ℕ) :
    Matrix (SquarefreeConductor N) (SquarefreeConductor N) ℤ :=
  fun a d => if d.val.val ∣ a.val.val then 1 else 0

/-- The integral orientation on squarefree arithmetic labels. -/
def squarefreeOrientationMatrix (N : ℕ) :
    Matrix (SquarefreeConductor N) (SquarefreeConductor N) ℤ :=
  diagonal fun a => moebius a.val.val

/-- Multiplication is performed on the original integer conductors. -/
def squarefreeHeckeMatrix (N : ℕ) :
    Matrix (SquarefreeConductor N) (SquarefreeConductor N) ℤ :=
  fun a b => moebius (a.val.val * b.val.val)

private theorem moebius_mul_indicator (a b : ℕ) :
    moebius (a*b) = moebius a * (if a.Coprime b then 1 else 0) * moebius b := by
  by_cases h : a.Coprime b
  · rw [if_pos h, mul_one, isMultiplicative_moebius.map_mul_of_coprime h]
  · rw [if_neg h, mul_zero, zero_mul]
    exact moebius_eq_zero_of_not_squarefree (fun hs => h (Nat.coprime_of_squarefree_mul hs))

private theorem sum_squarefree_moebius (N : ℕ) (f : ConductorWindow N → ℤ) :
    (∑ d : SquarefreeConductor N, moebius d.val.val * f d.val) =
      ∑ d : ConductorWindow N, moebius d.val * f d := by
  rw [← sum_subtype (univ.filter fun d : ConductorWindow N => Squarefree d.val)
    (by intro d; simp only [mem_filter, mem_univ, true_and])
    (fun d => moebius d.val * f d)]
  apply sum_subset (filter_subset _ _)
  intro d _ hd
  have hsf : ¬ Squarefree d.val := by simpa only [mem_filter, mem_univ, true_and] using hd
  rw [moebius_eq_zero_of_not_squarefree hsf, zero_mul]

/-- The coprimality factorization restricts without loss to squarefree divisors. -/
theorem squarefreeCoprimeMatrix_factorization (N : ℕ) :
    (fun a b : SquarefreeConductor N => if a.val.val.Coprime b.val.val then (1 : ℤ) else 0) =
      squarefreeDivisorMatrix N * squarefreeOrientationMatrix N *
        (squarefreeDivisorMatrix N).transpose := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [squarefreeOrientationMatrix, squarefreeDivisorMatrix,
    Matrix.mul_diagonal, Matrix.transpose_apply]
  have he := RHTower.finiteMobiusCoprimeIncidenceEntry_eq_coprimeIndicator N a.val b.val.val
  rw [← he, RHTower.finiteMobiusCoprimeIncidenceEntry]
  rw [sum_subtype (Icc 1 N) (by intro x; rfl)]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (sum_squarefree_moebius N
      (fun d => (if d.val ∣ a.val.val then 1 else 0) *
        (if d.val ∣ b.val.val then 1 else 0))).symm

/-- Restricting divisor incidence to its squarefree down-set preserves determinant one. -/
theorem squarefreeDivisorMatrix_det (N : ℕ) : (squarefreeDivisorMatrix N).det = 1 := by
  have htri : (squarefreeDivisorMatrix N).BlockTriangular
      (fun a : SquarefreeConductor N => OrderDual.toDual a.val.val) := by
    intro a d hlt
    apply if_neg
    intro hd
    exact (Nat.not_le_of_gt hlt)
      (Nat.le_of_dvd (mem_Icc.mp a.val.property).1 hd)
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp only [squarefreeDivisorMatrix, dvd_refl, if_true, prod_const_one]

/-- Every squarefree orientation is its own integral inverse. -/
theorem squarefreeOrientationMatrix_mul_self (N : ℕ) :
    squarefreeOrientationMatrix N * squarefreeOrientationMatrix N = 1 := by
  rw [squarefreeOrientationMatrix, Matrix.diagonal_mul_diagonal]
  ext a b
  by_cases h : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, ← pow_two]
    exact moebius_sq_eq_one_of_squarefree a.property
  · simp [Matrix.diagonal, h]

/-- The full conductor-multiplication matrix has an integral incidence factorization. -/
theorem squarefreeHeckeMatrix_factorization (N : ℕ) :
    squarefreeHeckeMatrix N =
      squarefreeOrientationMatrix N *
        (squarefreeDivisorMatrix N * squarefreeOrientationMatrix N *
          (squarefreeDivisorMatrix N).transpose) * squarefreeOrientationMatrix N := by
  rw [← squarefreeCoprimeMatrix_factorization]
  ext a b
  simp only [squarefreeHeckeMatrix, squarefreeOrientationMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact moebius_mul_indicator _ _

/-- Dilated charges on a squarefree conductor window have an integral inverse. -/
theorem squarefreeHeckeMatrix_isUnit (N : ℕ) : IsUnit (squarefreeHeckeMatrix N) := by
  have hE : IsUnit (squarefreeDivisorMatrix N) := by
    rw [Matrix.isUnit_iff_isUnit_det, squarefreeDivisorMatrix_det]
    exact isUnit_one
  have hJ : IsUnit (squarefreeOrientationMatrix N) :=
    ⟨⟨_, _, squarefreeOrientationMatrix_mul_self N,
      squarefreeOrientationMatrix_mul_self N⟩, rfl⟩
  rw [squarefreeHeckeMatrix_factorization]
  exact (hJ.mul ((hE.mul hJ).mul ((Matrix.isUnit_transpose _).mpr hE))).mul hJ

/-- Charge after multiplying every conductor by `a`. -/
def conductorDilatedCharge (N a : ℕ) (v : ConductorWindow N → ℤ) : ℤ :=
  ∑ n, moebius (a*n.val) * v n

private theorem moebius_mul_zero_of_not_squarefree (a n : ℕ) (hn : ¬ Squarefree n) :
    moebius (a*n) = 0 := by
  apply moebius_eq_zero_of_not_squarefree
  intro h
  apply hn
  intro p hp
  exact h p (dvd_mul_of_dvd_right hp a)

/-- Nonsquarefree coordinates contribute to no multiplicatively translated charge. -/
theorem conductorDilatedCharge_squarefree (N a : ℕ) (v : ConductorWindow N → ℤ) :
    conductorDilatedCharge N a v =
      ∑ n : SquarefreeConductor N, moebius (a*n.val.val) * v n.val := by
  rw [← sum_subtype (univ.filter fun n : ConductorWindow N => Squarefree n.val)
    (by intro n; simp only [mem_filter, mem_univ, true_and])
    (fun n => moebius (a*n.val) * v n)]
  symm
  apply sum_subset (filter_subset _ _)
  intro n _ hn
  have hsf : ¬ Squarefree n.val := by simpa only [mem_filter, mem_univ, true_and] using hn
  rw [moebius_mul_zero_of_not_squarefree _ _ hsf, zero_mul]

/-- Tests through the original cutoff recover every squarefree integer coefficient. -/
theorem conductorDilatedCharge_vanish_iff (N : ℕ) (v : ConductorWindow N → ℤ) :
    (∀ a : ConductorWindow N, conductorDilatedCharge N a.val v = 0) ↔
      ∀ n : ConductorWindow N, Squarefree n.val → v n = 0 := by
  constructor
  · intro h
    have hv : squarefreeHeckeMatrix N *ᵥ (fun n : SquarefreeConductor N => v n.val) = 0 := by
      funext a
      have ha := h a.val
      rw [conductorDilatedCharge_squarefree] at ha
      exact ha
    have hz := Matrix.mulVec_injective_of_isUnit (squarefreeHeckeMatrix_isUnit N)
      (hv.trans (Matrix.mulVec_zero _).symm)
    intro n hn
    exact congrFun hz ⟨n,hn⟩
  · intro h a
    rw [conductorDilatedCharge_squarefree]
    exact sum_eq_zero fun n _ => by rw [h n.val n.property, mul_zero]

#print axioms squarefreeCoprimeMatrix_factorization
#print axioms squarefreeHeckeMatrix_isUnit
#print axioms conductorDilatedCharge_vanish_iff

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
