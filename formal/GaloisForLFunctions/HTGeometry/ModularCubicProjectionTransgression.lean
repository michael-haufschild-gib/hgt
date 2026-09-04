import Mathlib

/-!
# Modular cubic projection transgression

Ordinary trace kills the nuclear associator of three projection polarizations.  A source modular
weight need not: its sigma-trace law converts every commutator into an exact modular displacement.
This file proves the resulting cubic transgression in an arbitrary noncommutative ring and gives a
closed two-dimensional witness whose ordinary trace is zero while its modular cubic anomaly is
nonzero.
-/

namespace GaloisForLFunctions.HTGeometry

section Generic

variable {A G : Type*} [Ring A] [AddCommGroup G]

/-- Noncommutative commutator, named locally to avoid choosing a topological operator category. -/
def modularCommutator (x y : A) : A := x * y - y * x

/-- Failure of cubic projection displacement to add through an intermediate polarization. -/
def cubicProjectionAssociatorAlgebra (r q p : A) : A :=
  (r - p) ^ 3 - (r - q) ^ 3 - (q - p) ^ 3

/-- A sigma-trace: cyclic rotation is accompanied by the source modular automorphism. -/
def IsSigmaTrace (sigma : A →+* A) (tau : A →+ G) : Prop :=
  ∀ x y, tau (x * y) = tau (sigma y * x)

/-- Exact operator-valued modular correction to cubic projection additivity. -/
def cubicProjectionModularAnomaly (sigma : A →+* A) (r q p : A) : A :=
  let a := r - q
  let b := q - p
  3 • ((sigma q - q) * (a * b)) +
    (sigma a - a) * (a * b) +
    (sigma (a ^ 2) - a ^ 2) * b +
    (sigma (a * b) - a * b) * b +
    (sigma a - a) * b ^ 2

/-- The cubic associator is a sum of five commutator channels.  Projection algebra collapses the
distinguished mixed pair to the commutator with the intermediate projection. -/
theorem cubicProjectionAssociatorAlgebra_eq_commutators
    (r q p : A) (hr : r * r = r) (hq : q * q = q) (hp : p * p = p) :
    cubicProjectionAssociatorAlgebra r q p =
      let a := r - q
      let b := q - p
      3 • modularCommutator (a * b) q +
        modularCommutator (a * b) a +
        modularCommutator b (a ^ 2) +
        modularCommutator b (a * b) +
        modularCommutator (b ^ 2) a := by
  let a := r - q
  let b := q - p
  have hlong : r - p = a + b := by
    simp only [a, b]
    noncomm_ring
  have hqqp : q * (q * p) = q * p := by rw [← mul_assoc, hq]
  have hcross : a ^ 2 * b + a * b ^ 2 = modularCommutator (a * b) q := by
    simp only [a, b, modularCommutator]
    noncomm_ring [hr, hq, hp, hqqp]
  rw [cubicProjectionAssociatorAlgebra, hlong]
  change (a + b) ^ 3 - a ^ 3 - b ^ 3 = _
  rw [show (a + b) ^ 3 - a ^ 3 - b ^ 3 =
      3 • (a ^ 2 * b + a * b ^ 2) +
        modularCommutator (a * b) a +
        modularCommutator b (a ^ 2) +
        modularCommutator b (a * b) +
        modularCommutator (b ^ 2) a by
      simp only [modularCommutator]
      noncomm_ring]
  rw [hcross]

/-- A sigma-trace sends an ordinary commutator to the modular displacement of its rotated
factor.  This is the basic mechanism by which source time survives ordinary trace
abelianization. -/
theorem IsSigmaTrace.map_modularCommutator
    {sigma : A →+* A} {tau : A →+ G} (h : IsSigmaTrace sigma tau)
    (x y : A) :
    tau (modularCommutator x y) = tau ((sigma y - y) * x) := by
  rw [modularCommutator, map_sub, h]
  rw [sub_mul, map_sub]

/-- **Modular cubic projection transgression.**  Under a sigma-trace, the entire cubic projection
associator is exactly the source modular anomaly. -/
theorem IsSigmaTrace.map_cubicProjectionAssociatorAlgebra
    {sigma : A →+* A} {tau : A →+ G} (h : IsSigmaTrace sigma tau)
    (r q p : A) (hr : r * r = r) (hq : q * q = q) (hp : p * p = p) :
    tau (cubicProjectionAssociatorAlgebra r q p) =
      tau (cubicProjectionModularAnomaly sigma r q p) := by
  rw [cubicProjectionAssociatorAlgebra_eq_commutators r q p hr hq hp]
  simp only [cubicProjectionModularAnomaly, map_add, map_nsmul]
  rw [h.map_modularCommutator, h.map_modularCommutator,
    h.map_modularCommutator, h.map_modularCommutator,
    h.map_modularCommutator]

/-- The new term vanishes in the tracial centralizer.  It detects failure of modular invariance,
not a new ordinary trace or a choice of phase. -/
theorem cubicProjectionModularAnomaly_eq_zero_of_fixed
    (sigma : A →+* A) (r q p : A)
    (hr : sigma r = r) (hq : sigma q = q) (hp : sigma p = p) :
    cubicProjectionModularAnomaly sigma r q p = 0 := by
  simp [cubicProjectionModularAnomaly, hr, hq, hp]

end Generic

/-! ## Exact two-block modular compression law -/

section TwoBlock

variable {K : Type*} [Field K]

/-- Scalar two-block model for a source density split into retained and discarded sectors. -/
abbrev ModularTwoBlockMatrix (K : Type*) := Matrix (Fin 2) (Fin 2) K

/-- Projection onto the retained source sector. -/
def modularTwoBlockCornerProjection : ModularTwoBlockMatrix K := !![1, 0; 0, 0]

/-- A prime-mixed source density.  The off-diagonal entries are the source couplings. -/
def modularTwoBlockDensity (a b c d : K) : ModularTwoBlockMatrix K :=
  !![a, b; c, d]

/-- Explicit inverse of the two-block density. -/
def modularTwoBlockDensityInv (a b c d : K) : ModularTwoBlockMatrix K :=
  let det := a * d - b * c
  !![d / det, -b / det; -c / det, a / det]

theorem modularTwoBlockDensity_mul_inv
    (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    modularTwoBlockDensity a b c d * modularTwoBlockDensityInv a b c d =
      (1 : ModularTwoBlockMatrix K) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hdet]
    ring
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hdet]
    ring
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hdet]
    ring
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    calc
      c * (-b / (a * d - b * c)) + d * (a / (a * d - b * c)) =
          (a * d - b * c) / (a * d - b * c) := by ring
      _ = 1 := div_self hdet

theorem modularTwoBlockDensityInv_mul
    (a b c d : K) (hdet : a * d - b * c ≠ 0) :
    modularTwoBlockDensityInv a b c d * modularTwoBlockDensity a b c d =
      (1 : ModularTwoBlockMatrix K) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    calc
      d / (a * d - b * c) * a + -b / (a * d - b * c) * c =
          (a * d - b * c) / (a * d - b * c) := by ring
      _ = 1 := div_self hdet
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hdet]
    ring
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [hdet]
    ring
  · simp [modularTwoBlockDensity, modularTwoBlockDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]
    calc
      -c / (a * d - b * c) * b + a / (a * d - b * c) * d =
          (a * d - b * c) / (a * d - b * c) := by ring
      _ = 1 := div_self hdet

/-- **Schur modular compression formula.**  Compression fails to commute with inner modular
transport by exactly the normalized product of the two cross-sector couplings.  This is a source
term: it exists before any divisor or zero data. -/
theorem modularTwoBlockCompressionDefect
    (a b c d x : K) (hdet : a * d - b * c ≠ 0) :
    modularTwoBlockCornerProjection *
          (modularTwoBlockDensityInv a b c d *
              (x • modularTwoBlockCornerProjection) *
            modularTwoBlockDensity a b c d) *
        modularTwoBlockCornerProjection -
      x • modularTwoBlockCornerProjection =
        ((b * c / (a * d - b * c)) * x) •
          modularTwoBlockCornerProjection := by
  have hdet' : d * a - b * c ≠ 0 := by
    rw [mul_comm d a]
    exact hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modularTwoBlockCornerProjection, modularTwoBlockDensity,
      modularTwoBlockDensityInv]
  all_goals field_simp [hdet, hdet']
  all_goals ring_nf

/-- Prime-separable (zero cross-block product) modular density cannot produce a compression
extension class. -/
theorem modularTwoBlockCompressionDefect_eq_zero_of_crossProduct_eq_zero
    (a b c d x : K) (hdet : a * d - b * c ≠ 0) (hcross : b * c = 0) :
    modularTwoBlockCornerProjection *
          (modularTwoBlockDensityInv a b c d *
              (x • modularTwoBlockCornerProjection) *
            modularTwoBlockDensity a b c d) *
        modularTwoBlockCornerProjection -
      x • modularTwoBlockCornerProjection = 0 := by
  rw [modularTwoBlockCompressionDefect a b c d x hdet, hcross]
  simp

end TwoBlock

/-! ## A closed nontrivial sigma-trace witness -/

abbrev ModularCubicWitnessMatrix := Matrix (Fin 2) (Fin 2) ℚ

def modularCubicWitnessP : ModularCubicWitnessMatrix := !![1, 0; 0, 0]

def modularCubicWitnessQ : ModularCubicWitnessMatrix :=
  !![(1 : ℚ) / 2, (1 : ℚ) / 2; (1 : ℚ) / 2, (1 : ℚ) / 2]

def modularCubicWitnessR : ModularCubicWitnessMatrix := !![0, 0; 0, 1]

def modularCubicWitnessDensity : ModularCubicWitnessMatrix :=
  !![(1 : ℚ) / 2, (1 : ℚ) / 4; (1 : ℚ) / 4, (1 : ℚ) / 4]

def modularCubicWitnessDensityInv : ModularCubicWitnessMatrix :=
  !![4, -4; -4, 8]

theorem modularCubicWitnessDensity_mul_inv :
    modularCubicWitnessDensity * modularCubicWitnessDensityInv =
      (1 : ModularCubicWitnessMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularCubicWitnessDensity, modularCubicWitnessDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modularCubicWitnessDensityInv_mul :
    modularCubicWitnessDensityInv * modularCubicWitnessDensity =
      (1 : ModularCubicWitnessMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularCubicWitnessDensity, modularCubicWitnessDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem modularCubicWitnessP_idempotent :
    modularCubicWitnessP * modularCubicWitnessP = modularCubicWitnessP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularCubicWitnessP, Matrix.mul_apply, Fin.sum_univ_two]

theorem modularCubicWitnessQ_idempotent :
    modularCubicWitnessQ * modularCubicWitnessQ = modularCubicWitnessQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularCubicWitnessQ, Matrix.mul_apply, Fin.sum_univ_two]

theorem modularCubicWitnessR_idempotent :
    modularCubicWitnessR * modularCubicWitnessR = modularCubicWitnessR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularCubicWitnessR, Matrix.mul_apply, Fin.sum_univ_two]

/-- The prime-mixed density has strict sub-unit total mass. -/
theorem trace_modularCubicWitnessDensity_eq :
    Matrix.trace modularCubicWitnessDensity = (3 : ℚ) / 4 := by
  norm_num [modularCubicWitnessDensity, Matrix.trace, Fin.sum_univ_two]

theorem trace_modularCubicWitnessDensity_lt_one :
    Matrix.trace modularCubicWitnessDensity < 1 := by
  norm_num [modularCubicWitnessDensity, Matrix.trace, Fin.sum_univ_two]

/-- Algebraic modular automorphism implemented by the prime-mixed witness density. -/
def modularCubicWitnessSigma :
    ModularCubicWitnessMatrix →+* ModularCubicWitnessMatrix where
  toFun x :=
    modularCubicWitnessDensityInv * x * modularCubicWitnessDensity
  map_one' := by simp [modularCubicWitnessDensityInv_mul]
  map_mul' x y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc modularCubicWitnessDensity
      modularCubicWitnessDensityInv, modularCubicWitnessDensity_mul_inv,
      Matrix.one_mul]
  map_zero' := by simp
  map_add' x y := by simp [mul_add, add_mul]

/-- Weighted source trace associated with the witness density. -/
def modularCubicWitnessTrace : ModularCubicWitnessMatrix →+ ℚ where
  toFun x := Matrix.trace (modularCubicWitnessDensity * x)
  map_zero' := by simp
  map_add' x y := by simp [mul_add, Matrix.trace_add]

/-- The weighted trace is exactly a sigma-trace for the inner modular automorphism. -/
theorem modularCubicWitnessTrace_isSigmaTrace :
    IsSigmaTrace modularCubicWitnessSigma modularCubicWitnessTrace := by
  intro x y
  change Matrix.trace (modularCubicWitnessDensity * (x * y)) =
    Matrix.trace
      (modularCubicWitnessDensity *
        ((modularCubicWitnessDensityInv * y * modularCubicWitnessDensity) * x))
  simp only [← Matrix.mul_assoc, modularCubicWitnessDensity_mul_inv, Matrix.one_mul]
  exact Matrix.trace_mul_cycle modularCubicWitnessDensity x y

/-- Compression does not intertwine the prime-mixed modular automorphism: its exact defect is one
rank-one corner.  Scalar rescaling of the density changes its mass but not this projective
modular defect. -/
theorem modularCubicWitness_compressionDefect_eq_projection :
    modularCubicWitnessP *
          modularCubicWitnessSigma modularCubicWitnessP *
        modularCubicWitnessP -
      modularCubicWitnessP =
        modularCubicWitnessP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularCubicWitnessP, modularCubicWitnessSigma,
      modularCubicWitnessDensity, modularCubicWitnessDensityInv,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Ordinary trace erases the cubic associator in the witness. -/
theorem trace_modularCubicWitness_associator_eq_zero :
    Matrix.trace
      (cubicProjectionAssociatorAlgebra modularCubicWitnessR
        modularCubicWitnessQ modularCubicWitnessP) = 0 := by
  norm_num [cubicProjectionAssociatorAlgebra, modularCubicWitnessR,
    modularCubicWitnessQ, modularCubicWitnessP, Matrix.trace,
    Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- The strict-subunit source modular weight sees the same cubic associator as a nonzero
eighth-unit. -/
theorem modularCubicWitnessTrace_associator_eq_neg_eighth :
    modularCubicWitnessTrace
      (cubicProjectionAssociatorAlgebra modularCubicWitnessR
        modularCubicWitnessQ modularCubicWitnessP) = -(1 : ℚ) / 8 := by
  norm_num [modularCubicWitnessTrace, cubicProjectionAssociatorAlgebra,
    modularCubicWitnessDensity, modularCubicWitnessR, modularCubicWitnessQ,
    modularCubicWitnessP, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    pow_succ]

/-- The exact modular anomaly, not an arbitrary nontracial remainder, carries the eighth-unit. -/
theorem modularCubicWitnessTrace_anomaly_eq_neg_eighth :
    modularCubicWitnessTrace
      (cubicProjectionModularAnomaly modularCubicWitnessSigma
        modularCubicWitnessR modularCubicWitnessQ modularCubicWitnessP) =
      -(1 : ℚ) / 8 := by
  rw [← modularCubicWitnessTrace_isSigmaTrace.map_cubicProjectionAssociatorAlgebra
    modularCubicWitnessR modularCubicWitnessQ modularCubicWitnessP
    modularCubicWitnessR_idempotent modularCubicWitnessQ_idempotent
    modularCubicWitnessP_idempotent]
  exact modularCubicWitnessTrace_associator_eq_neg_eighth

/-- Closed certificate: ordinary trace loses a nonzero source-modular cubic transgression. -/
theorem modularCubicProjectionTransgression_closed :
    Matrix.trace
        (cubicProjectionAssociatorAlgebra modularCubicWitnessR
          modularCubicWitnessQ modularCubicWitnessP) = 0 ∧
      modularCubicWitnessTrace
        (cubicProjectionModularAnomaly modularCubicWitnessSigma
          modularCubicWitnessR modularCubicWitnessQ modularCubicWitnessP) =
        -(1 : ℚ) / 8 ∧
      Matrix.trace modularCubicWitnessDensity < 1 ∧
      modularCubicWitnessP *
            modularCubicWitnessSigma modularCubicWitnessP *
          modularCubicWitnessP -
        modularCubicWitnessP =
          modularCubicWitnessP :=
  ⟨trace_modularCubicWitness_associator_eq_zero,
    modularCubicWitnessTrace_anomaly_eq_neg_eighth,
    trace_modularCubicWitnessDensity_lt_one,
    modularCubicWitness_compressionDefect_eq_projection⟩

end GaloisForLFunctions.HTGeometry
