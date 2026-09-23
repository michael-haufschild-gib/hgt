import GaloisForLFunctions.HTGeometry.ConstraintRelativity.BipartiteMatrixDecomposition
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Core.DynamicalLieAlgebra

/-!
# Hermitian passive-relation interaction cross-fibre

Exact real-form completion of the passive relation card's joint-system theorems:

* `Herm₀(A ⊗ B) = L ⊕⊥ C` for Hilbert--Schmidt pairing;
* `C = ker (Tr_B / dim B, Tr_A / dim A)`;
* `C = Herm₀(A) ⊗ℝ Herm₀(B)` under Kronecker realization;
* `dimℝ C = (dim(A)^(2 : ℕ) - 1)(dim(B)^(2 : ℕ) - 1)`;
* first-order Hermitian locality iff the Hamiltonian is local plus a real scalar.
-/

namespace HTGeometry.ConstraintRelativity

noncomputable section

open Matrix
open scoped Kronecker

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem finrank_matrix_generic (m : Type*) [Fintype m] :
    Module.finrank ℂ (Matrix m m ℂ) = Fintype.card m * Fintype.card m := by
  change Module.finrank ℂ (m → m → ℂ) = _
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fintype_fun_eq_card, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id]

theorem finrank_tracelessMatrices_generic
    (m : Type*) [Fintype m] [DecidableEq m] [Nonempty m] :
    Module.finrank ℂ (tracelessMatrices m) =
      Fintype.card m * Fintype.card m - 1 := by
  have hsurj : Function.Surjective (Matrix.traceLinearMap m ℂ ℂ) := by
    intro c
    refine ⟨(c / (Fintype.card m : ℂ)) • 1, ?_⟩
    rw [Matrix.traceLinearMap_apply, Matrix.trace_smul, Matrix.trace_one,
      smul_eq_mul, div_mul_cancel₀]
    exact_mod_cast Fintype.card_ne_zero
  have hrange : Module.finrank ℂ (LinearMap.range (Matrix.traceLinearMap m ℂ ℂ)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hrn := (Matrix.traceLinearMap m ℂ ℂ).finrank_range_add_finrank_ker
  rw [hrange, finrank_matrix_generic] at hrn
  change Module.finrank ℂ (LinearMap.ker (Matrix.traceLinearMap m ℂ ℂ)) = _
  omega

section LocalDimension

variable [Nonempty m] [Nonempty n]

/-- Canonical sum of the two traceless factor reporters. -/
def localReporterPairLinear :
    (tracelessMatrices m × tracelessMatrices n) →ₗ[ℂ]
      Matrix (m × n) (m × n) ℂ where
  toFun p := (p.1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ) +
    (1 : Matrix m m ℂ) ⊗ₖ (p.2 : Matrix n n ℂ)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_kronecker,
      Matrix.kronecker_add]
    abel
  map_smul' c p := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [Matrix.kroneckerMap_apply, smul_eq_mul, mul_add]
    ring

/-- The two factor reporters parametrize the local reporter sector without redundancy. -/
noncomputable def localReporterPairEquiv :
    (tracelessMatrices m × tracelessMatrices n) ≃ₗ[ℂ]
      matrixLocalReporter (m := m) (n := n) := by
  let f : (tracelessMatrices m × tracelessMatrices n) →ₗ[ℂ]
      matrixLocalReporter (m := m) (n := n) :=
    LinearMap.codRestrict _ localReporterPairLinear fun p => by
      rw [mem_matrixLocalReporter_iff]
      exact ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩
  apply LinearEquiv.ofBijective f
  constructor
  · intro p q hpq
    have hmatrix :
        localReporterPairLinear p = localReporterPairLinear q :=
      congrArg Subtype.val hpq
    have hR := congrArg (partialTraceRight (m := m) (n := n)) hmatrix
    have hL := congrArg (partialTraceLeft (m := m) (n := n)) hmatrix
    have hn : (Fintype.card n : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hm : (Fintype.card m : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hfirst : (p.1 : Matrix m m ℂ) = q.1 := by
      have hp2 : (p.2 : Matrix n n ℂ).trace = 0 := p.2.property
      have hq2 : (q.2 : Matrix n n ℂ).trace = 0 := q.2.property
      have hR' : (Fintype.card n : ℂ) • (p.1 : Matrix m m ℂ) =
          (Fintype.card n : ℂ) • (q.1 : Matrix m m ℂ) := by
        simpa [localReporterPairLinear, partialTraceRight_add,
          partialTraceRight_kronecker, hp2, hq2] using hR
      have hdiff : (Fintype.card n : ℂ) •
          ((p.1 : Matrix m m ℂ) - (q.1 : Matrix m m ℂ)) = 0 := by
        rw [smul_sub, hR', sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hdiff).resolve_left hn)
    have hsecond : (p.2 : Matrix n n ℂ) = q.2 := by
      have hp1 : (p.1 : Matrix m m ℂ).trace = 0 := p.1.property
      have hq1 : (q.1 : Matrix m m ℂ).trace = 0 := q.1.property
      have hL' : (Fintype.card m : ℂ) • (p.2 : Matrix n n ℂ) =
          (Fintype.card m : ℂ) • (q.2 : Matrix n n ℂ) := by
        simpa [localReporterPairLinear, partialTraceLeft_add,
          partialTraceLeft_kronecker, hp1, hq1] using hL
      have hdiff : (Fintype.card m : ℂ) •
          ((p.2 : Matrix n n ℂ) - (q.2 : Matrix n n ℂ)) = 0 := by
        rw [smul_sub, hL', sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hdiff).resolve_left hm)
    exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)
  · intro X
    have hmem := X.property
    rw [mem_matrixLocalReporter_iff] at hmem
    obtain ⟨A, hA, B, hB, hX⟩ := hmem
    refine ⟨(⟨A, hA⟩, ⟨B, hB⟩), ?_⟩
    apply Subtype.ext
    exact hX.symm

theorem finrank_matrixLocalReporter :
    Module.finrank ℂ (matrixLocalReporter (m := m) (n := n)) =
      (Fintype.card m * Fintype.card m - 1) +
        (Fintype.card n * Fintype.card n - 1) := by
  rw [← (localReporterPairEquiv (m := m) (n := n)).finrank_eq,
    Module.finrank_prod, finrank_tracelessMatrices_generic,
    finrank_tracelessMatrices_generic]

private theorem cross_dimension_arithmetic {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a * b * (a * b) - 1) - ((a * a - 1) + (b * b - 1)) =
      (a * a - 1) * (b * b - 1) := by
  have hA : 1 ≤ a * a := by nlinarith
  have hB : 1 ≤ b * b := by nlinarith
  have hAB : 1 ≤ a * b * (a * b) := by nlinarith
  have hid : a * b * (a * b) - 1 =
      (a * a - 1) + (b * b - 1) + (a * a - 1) * (b * b - 1) := by
    apply Nat.cast_injective (R := ℤ)
    push_cast [Nat.cast_sub hA, Nat.cast_sub hB, Nat.cast_sub hAB]
    ring
  rw [hid]
  omega

theorem finrank_matrixCrossFibre :
    Module.finrank ℂ (matrixCrossFibre (m := m) (n := n)) =
      (Fintype.card m * Fintype.card m - 1) *
        (Fintype.card n * Fintype.card n - 1) := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (matrixLocalReporter (m := m) (n := n))
    (matrixCrossFibre (m := m) (n := n))
  rw [← jointTracelessMatrices_eq_local_sup_cross,
    matrixLocalReporter_inf_matrixCrossFibre_eq_bot,
    finrank_tracelessMatrices_generic, finrank_matrixLocalReporter] at hsum
  simp only [Fintype.card_prod, finrank_bot, add_zero] at hsum
  let T := Fintype.card m * Fintype.card n *
    (Fintype.card m * Fintype.card n) - 1
  let L := (Fintype.card m * Fintype.card m - 1) +
    (Fintype.card n * Fintype.card n - 1)
  let C := Module.finrank ℂ (matrixCrossFibre (m := m) (n := n))
  have hsum' : T = L + C := by
    simpa [T, L, C] using hsum
  have hcross : Module.finrank ℂ (matrixCrossFibre (m := m) (n := n)) =
      (Fintype.card m * Fintype.card n * (Fintype.card m * Fintype.card n) - 1) -
        ((Fintype.card m * Fintype.card m - 1) +
          (Fintype.card n * Fintype.card n - 1)) := by
    change C = T - L
    omega
  rw [hcross]
  exact cross_dimension_arithmetic Fintype.card_pos Fintype.card_pos

end LocalDimension

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem partialTraceRight_conjTranspose (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceRight Xᴴ = (partialTraceRight X)ᴴ := by
  ext i j
  simp [partialTraceRight, Matrix.conjTranspose_apply]

omit [DecidableEq m] [Fintype n] [DecidableEq n] in
theorem partialTraceLeft_conjTranspose (X : Matrix (m × n) (m × n) ℂ) :
    partialTraceLeft Xᴴ = (partialTraceLeft X)ᴴ := by
  ext i j
  simp [partialTraceLeft, Matrix.conjTranspose_apply]

theorem star_mem_matrixCrossFibre {X : Matrix (m × n) (m × n) ℂ}
    (hX : X ∈ matrixCrossFibre (m := m) (n := n)) :
    star X ∈ matrixCrossFibre (m := m) (n := n) := by
  rw [mem_matrixCrossFibre] at hX ⊢
  constructor
  · change partialTraceRight Xᴴ = 0
    rw [partialTraceRight_conjTranspose, hX.1, conjTranspose_zero]
  · change partialTraceLeft Xᴴ = 0
    rw [partialTraceLeft_conjTranspose, hX.2, conjTranspose_zero]

section StarLocal

variable [Nonempty m] [Nonempty n]

theorem star_mem_matrixLocalReporter {X : Matrix (m × n) (m × n) ℂ}
    (hX : X ∈ matrixLocalReporter (m := m) (n := n)) :
    star X ∈ matrixLocalReporter (m := m) (n := n) := by
  rw [mem_matrixLocalReporter_iff] at hX ⊢
  obtain ⟨A, hA, B, hB, rfl⟩ := hX
  refine ⟨Aᴴ, ?_, Bᴴ, ?_, ?_⟩
  · rw [Matrix.trace_conjTranspose, hA, star_zero]
  · rw [Matrix.trace_conjTranspose, hB, star_zero]
  · simp only [star_eq_conjTranspose, conjTranspose_add, conjTranspose_kronecker,
      conjTranspose_one]

/-- Cross and local sectors are Hilbert--Schmidt orthogonal already over `ℂ`. -/
theorem hsInner_eq_zero_of_mem_cross_of_mem_local
    {X L : Matrix (m × n) (m × n) ℂ}
    (hX : X ∈ matrixCrossFibre (m := m) (n := n))
    (hL : L ∈ matrixLocalReporter (m := m) (n := n)) :
    QuantumAlg.hsInner X L = 0 := by
  have hXstar := star_mem_matrixCrossFibre hX
  rw [mem_matrixCrossFibre] at hXstar
  have hXR : partialTraceRight Xᴴ = 0 := by
    simpa only [star_eq_conjTranspose] using hXstar.1
  have hXL : partialTraceLeft Xᴴ = 0 := by
    simpa only [star_eq_conjTranspose] using hXstar.2
  rw [mem_matrixLocalReporter_iff] at hL
  obtain ⟨A, hA, B, hB, rfl⟩ := hL
  rw [QuantumAlg.hsInner_add_right]
  have hleft : QuantumAlg.hsInner X
      (A ⊗ₖ (1 : Matrix n n ℂ)) = 0 := by
    rw [QuantumAlg.hsInner_def, ← trace_partialTraceRight,
      partialTraceRight_mul_leftLocal, hXR]
    simp
  have hright : QuantumAlg.hsInner X
      ((1 : Matrix m m ℂ) ⊗ₖ B) = 0 := by
    rw [QuantumAlg.hsInner_def, ← trace_partialTraceLeft,
      partialTraceLeft_mul_rightLocal, hXL]
    simp
  rw [hleft, hright, add_zero]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] in
theorem isSelfAdjoint_partialTraceRight {X : Matrix (m × n) (m × n) ℂ}
    (hX : IsSelfAdjoint X) : IsSelfAdjoint (partialTraceRight X) := by
  change Xᴴ = X at hX
  change (partialTraceRight X)ᴴ = partialTraceRight X
  rw [← partialTraceRight_conjTranspose, hX]

omit [DecidableEq m] [Fintype n] [DecidableEq n] [Nonempty m] [Nonempty n] in
theorem isSelfAdjoint_partialTraceLeft {X : Matrix (m × n) (m × n) ℂ}
    (hX : IsSelfAdjoint X) : IsSelfAdjoint (partialTraceLeft X) := by
  change Xᴴ = X at hX
  change (partialTraceLeft X)ᴴ = partialTraceLeft X
  rw [← partialTraceLeft_conjTranspose, hX]

omit [Nonempty m] in
theorem IsSelfAdjoint.traceCenter {A : Matrix m m ℂ} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (HTGeometry.ConstraintRelativity.traceCenter A) := by
  change Aᴴ = A at hA
  have htrace : star A.trace = A.trace := by
    rw [← Matrix.trace_conjTranspose]
    exact congrArg Matrix.trace hA
  change (HTGeometry.ConstraintRelativity.traceCenter A)ᴴ =
    HTGeometry.ConstraintRelativity.traceCenter A
  simp [HTGeometry.ConstraintRelativity.traceCenter, hA, htrace]

omit [DecidableEq n] [Nonempty m] [Nonempty n] in
theorem IsSelfAdjoint.leftReducedComponent {X : Matrix (m × n) (m × n) ℂ}
    (hX : IsSelfAdjoint X) : IsSelfAdjoint (leftReducedComponent X) := by
  apply IsSelfAdjoint.traceCenter
  have hpartial := isSelfAdjoint_partialTraceRight hX
  change (partialTraceRight X)ᴴ = partialTraceRight X at hpartial
  change ((((Fintype.card n : ℂ)⁻¹) • partialTraceRight X)ᴴ) =
    ((Fintype.card n : ℂ)⁻¹) • partialTraceRight X
  simp [hpartial]

omit [DecidableEq m] [Nonempty m] [Nonempty n] in
theorem IsSelfAdjoint.rightReducedComponent {X : Matrix (m × n) (m × n) ℂ}
    (hX : IsSelfAdjoint X) : IsSelfAdjoint (rightReducedComponent X) := by
  apply IsSelfAdjoint.traceCenter
  have hpartial := isSelfAdjoint_partialTraceLeft hX
  change (partialTraceLeft X)ᴴ = partialTraceLeft X at hpartial
  change ((((Fintype.card m : ℂ)⁻¹) • partialTraceLeft X)ᴴ) =
    ((Fintype.card m : ℂ)⁻¹) • partialTraceLeft X
  simp [hpartial]

omit [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] in
theorem star_bipartiteScalarCoeff {X : Matrix (m × n) (m × n) ℂ}
    (hX : IsSelfAdjoint X) :
    star (bipartiteScalarCoeff X) = bipartiteScalarCoeff X := by
  have htrace : star X.trace = X.trace := by
    rw [← Matrix.trace_conjTranspose]
    exact congrArg Matrix.trace hX
  simp [bipartiteScalarCoeff, htrace]

omit [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] in
theorem ofReal_re_bipartiteScalarCoeff {X : Matrix (m × n) (m × n) ℂ}
    (hX : IsSelfAdjoint X) :
    ((bipartiteScalarCoeff X).re : ℂ) = bipartiteScalarCoeff X := by
  have hc := star_bipartiteScalarCoeff hX
  have him := congrArg Complex.im hc
  apply Complex.ext
  · simp
  · simp at him ⊢
    linarith

end StarLocal

section HermitianCrossFibre

variable [Nonempty m] [Nonempty n]

/-- Traceless Hermitian matrices on one factor. -/
abbrev hermitianTracelessMatrices (m : Type*) [Fintype m] [DecidableEq m] :
    Submodule ℝ (Matrix m m ℂ) :=
  selfAdjoint.submodule ℝ (Matrix m m ℂ) ⊓
    (tracelessMatrices m).restrictScalars ℝ

/-- Real span of pure tensors with traceless Hermitian factors. This is the concrete
Kronecker realization of `Herm₀(A) ⊗ℝ Herm₀(B)`. -/
def hermitianTracelessKroneckerSpan :
    Submodule ℝ (Matrix (m × n) (m × n) ℂ) :=
  Submodule.map₂
    (Matrix.kroneckerBilinear (R := ℝ) (α := ℂ)
      (l := m) (m := m) (n := n) (p := n))
    (hermitianTracelessMatrices m) (hermitianTracelessMatrices n)

/-- Real Hermitian operators invisible to both boundary partial traces. -/
abbrev hermitianMatrixCrossFibre : Submodule ℝ (Matrix (m × n) (m × n) ℂ) :=
  selfAdjoint.submodule ℝ (Matrix (m × n) (m × n) ℂ) ⊓
    (matrixCrossFibre (m := m) (n := n)).restrictScalars ℝ

/-- Real traceless Hermitian joint reporter sector. -/
abbrev hermitianJointTraceless : Submodule ℝ (Matrix (m × n) (m × n) ℂ) :=
  selfAdjoint.submodule ℝ (Matrix (m × n) (m × n) ℂ) ⊓
    (jointTracelessMatrices (m := m) (n := n)).restrictScalars ℝ

/-- Real traceless Hermitian local reporter sector. -/
abbrev hermitianMatrixLocalReporter : Submodule ℝ (Matrix (m × n) (m × n) ℂ) :=
  selfAdjoint.submodule ℝ (Matrix (m × n) (m × n) ℂ) ⊓
    (matrixLocalReporter (m := m) (n := n)).restrictScalars ℝ

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Nonempty m] [Nonempty n] in
theorem IsSelfAdjoint.kronecker
    {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A ⊗ₖ B) := by
  change Aᴴ = A at hA
  change Bᴴ = B at hB
  change (A ⊗ₖ B)ᴴ = A ⊗ₖ B
  rw [conjTranspose_kronecker, hA, hB]

omit [Nonempty m] in
theorem realPart_mem_hermitianTracelessMatrices
    {A : Matrix m m ℂ} (hA : A ∈ tracelessMatrices m) :
    (realPart A : Matrix m m ℂ) ∈ hermitianTracelessMatrices m := by
  constructor
  · exact (realPart A).property
  · rw [realPart_apply_coe]
    exact (tracelessMatrices m).smul_of_tower_mem _
      ((tracelessMatrices m).add_mem hA (by
        have hstar : star A ∈ tracelessMatrices m := by
          change Aᴴ ∈ tracelessMatrices m
          change A.trace = 0 at hA
          change Aᴴ.trace = 0
          rw [Matrix.trace_conjTranspose, hA, star_zero]
        exact hstar))

omit [Nonempty m] in
theorem imaginaryPart_mem_hermitianTracelessMatrices
    {A : Matrix m m ℂ} (hA : A ∈ tracelessMatrices m) :
    (imaginaryPart A : Matrix m m ℂ) ∈ hermitianTracelessMatrices m := by
  constructor
  · exact (imaginaryPart A).property
  · rw [imaginaryPart_apply_coe]
    exact (tracelessMatrices m).smul_mem _
      ((tracelessMatrices m).smul_of_tower_mem _
        ((tracelessMatrices m).sub_mem hA (by
          change Aᴴ ∈ tracelessMatrices m
          change A.trace = 0 at hA
          change Aᴴ.trace = 0
          rw [Matrix.trace_conjTranspose, hA, star_zero])))

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Nonempty m] [Nonempty n] in
private theorem kronecker_eq_real_imag_expansion
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    A ⊗ₖ B =
      ((realPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ) -
        (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ)) +
      Complex.I •
        ((realPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ) +
          (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ)) := by
  conv_lhs =>
    rw [← realPart_add_I_smul_imaginaryPart A,
      ← realPart_add_I_smul_imaginaryPart B]
  simp only [Matrix.add_kronecker, Matrix.kronecker_add, Matrix.smul_kronecker,
    Matrix.kronecker_smul]
  simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
  module

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Nonempty m] [Nonempty n] in
private theorem realPart_kronecker
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (realPart (A ⊗ₖ B) : Matrix (m × n) (m × n) ℂ) =
      (realPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ) -
        (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ) := by
  let R := (realPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ) -
    (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ)
  let S := (realPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ) +
    (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ)
  have hR : IsSelfAdjoint R :=
    (selfAdjoint.submodule ℝ _).sub_mem
      (IsSelfAdjoint.kronecker (realPart A).property (realPart B).property)
      (IsSelfAdjoint.kronecker (imaginaryPart A).property (imaginaryPart B).property)
  have hS : IsSelfAdjoint S :=
    (selfAdjoint.submodule ℝ _).add_mem
      (IsSelfAdjoint.kronecker (realPart A).property (imaginaryPart B).property)
      (IsSelfAdjoint.kronecker (imaginaryPart A).property (realPart B).property)
  rw [kronecker_eq_real_imag_expansion]
  change (realPart (R + Complex.I • S) : Matrix (m × n) (m × n) ℂ) = R
  rw [map_add, realPart_I_smul]
  simp [hR.coe_realPart, hS.imaginaryPart]

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Nonempty m] [Nonempty n] in
private theorem imaginaryPart_kronecker
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (imaginaryPart (A ⊗ₖ B) : Matrix (m × n) (m × n) ℂ) =
      (realPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ) +
        (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ) := by
  let R := (realPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ) -
    (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ)
  let S := (realPart A : Matrix m m ℂ) ⊗ₖ (imaginaryPart B : Matrix n n ℂ) +
    (imaginaryPart A : Matrix m m ℂ) ⊗ₖ (realPart B : Matrix n n ℂ)
  have hR : IsSelfAdjoint R :=
    (selfAdjoint.submodule ℝ _).sub_mem
      (IsSelfAdjoint.kronecker (realPart A).property (realPart B).property)
      (IsSelfAdjoint.kronecker (imaginaryPart A).property (imaginaryPart B).property)
  have hS : IsSelfAdjoint S :=
    (selfAdjoint.submodule ℝ _).add_mem
      (IsSelfAdjoint.kronecker (realPart A).property (imaginaryPart B).property)
      (IsSelfAdjoint.kronecker (imaginaryPart A).property (realPart B).property)
  rw [kronecker_eq_real_imag_expansion]
  change (imaginaryPart (R + Complex.I • S) : Matrix (m × n) (m × n) ℂ) = S
  rw [map_add, imaginaryPart_I_smul]
  simp [hS.coe_realPart, hR.imaginaryPart]

/-- Complex subspace whose Hermitian and skew-Hermitian coordinates both lie in the
real Hermitian pure-tensor span. -/
private def realImagInHermitianKroneckerSpan :
    Submodule ℂ (Matrix (m × n) (m × n) ℂ) where
  carrier := {X | (realPart X : Matrix (m × n) (m × n) ℂ) ∈
      hermitianTracelessKroneckerSpan (m := m) (n := n) ∧
    (imaginaryPart X : Matrix (m × n) (m × n) ℂ) ∈
      hermitianTracelessKroneckerSpan (m := m) (n := n)}
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    constructor
    · rw [map_add]
      exact (hermitianTracelessKroneckerSpan (m := m) (n := n)).add_mem hX.1 hY.1
    · rw [map_add]
      exact (hermitianTracelessKroneckerSpan (m := m) (n := n)).add_mem hX.2 hY.2
  smul_mem' c X hX := by
    constructor
    · rw [realPart_smul]
      exact (hermitianTracelessKroneckerSpan (m := m) (n := n)).sub_mem
        ((hermitianTracelessKroneckerSpan (m := m) (n := n)).smul_mem c.re hX.1)
        ((hermitianTracelessKroneckerSpan (m := m) (n := n)).smul_mem c.im hX.2)
    · rw [imaginaryPart_smul]
      exact (hermitianTracelessKroneckerSpan (m := m) (n := n)).add_mem
        ((hermitianTracelessKroneckerSpan (m := m) (n := n)).smul_mem c.re hX.2)
        ((hermitianTracelessKroneckerSpan (m := m) (n := n)).smul_mem c.im hX.1)

omit [Nonempty m] [Nonempty n] in
private theorem tracelessKroneckerSpan_le_realImagInHermitianKroneckerSpan :
    tracelessKroneckerSpan (m := m) (n := n) ≤
      realImagInHermitianKroneckerSpan (m := m) (n := n) := by
  rw [tracelessKroneckerSpan, Submodule.map₂_le]
  intro A hA B hB
  constructor
  · change (realPart (A ⊗ₖ B) : Matrix (m × n) (m × n) ℂ) ∈
      hermitianTracelessKroneckerSpan
    rw [realPart_kronecker]
    exact (hermitianTracelessKroneckerSpan (m := m) (n := n)).sub_mem
      (Submodule.apply_mem_map₂ _
        (realPart_mem_hermitianTracelessMatrices hA)
        (realPart_mem_hermitianTracelessMatrices hB))
      (Submodule.apply_mem_map₂ _
        (imaginaryPart_mem_hermitianTracelessMatrices hA)
        (imaginaryPart_mem_hermitianTracelessMatrices hB))
  · change (imaginaryPart (A ⊗ₖ B) : Matrix (m × n) (m × n) ℂ) ∈
      hermitianTracelessKroneckerSpan
    rw [imaginaryPart_kronecker]
    exact (hermitianTracelessKroneckerSpan (m := m) (n := n)).add_mem
      (Submodule.apply_mem_map₂ _
        (realPart_mem_hermitianTracelessMatrices hA)
        (imaginaryPart_mem_hermitianTracelessMatrices hB))
      (Submodule.apply_mem_map₂ _
        (imaginaryPart_mem_hermitianTracelessMatrices hA)
        (realPart_mem_hermitianTracelessMatrices hB))

/-- Exact identification `C = Herm₀(A) ⊗ℝ Herm₀(B)` under Kronecker realization. -/
theorem hermitianMatrixCrossFibre_eq_hermitianTracelessKroneckerSpan :
    hermitianMatrixCrossFibre (m := m) (n := n) =
      hermitianTracelessKroneckerSpan := by
  apply le_antisymm
  · intro X hX
    have hComplex : (X : Matrix (m × n) (m × n) ℂ) ∈
        tracelessKroneckerSpan (m := m) (n := n) := by
      rw [← matrixCrossFibre_eq_tracelessKroneckerSpan]
      exact hX.2
    have hRI := tracelessKroneckerSpan_le_realImagInHermitianKroneckerSpan hComplex
    simpa [hX.1.coe_realPart] using hRI.1
  · rw [hermitianTracelessKroneckerSpan, Submodule.map₂_le]
    intro A hA B hB
    constructor
    · exact IsSelfAdjoint.kronecker hA.1 hB.1
    · exact kronecker_mem_matrixCrossFibre hA.2 hB.2

/-- Normalized boundary map `(Tr_B / dim B, Tr_A / dim A)` on the traceless
Hermitian joint sector. -/
noncomputable def normalizedHermitianBoundaryMap :
    hermitianJointTraceless (m := m) (n := n) →ₗ[ℝ]
      (Matrix m m ℂ × Matrix n n ℂ) :=
  LinearMap.prod
    (LinearMap.domRestrict
      (LinearMap.restrictScalars ℝ
        (((Fintype.card n : ℂ)⁻¹) • partialTraceRightLinear (m := m) (n := n)))
      hermitianJointTraceless)
    (LinearMap.domRestrict
      (LinearMap.restrictScalars ℝ
        (((Fintype.card m : ℂ)⁻¹) • partialTraceLeftLinear (m := m) (n := n)))
      hermitianJointTraceless)

omit [Nonempty m] [Nonempty n] in
@[simp] theorem normalizedHermitianBoundaryMap_apply
    (X : hermitianJointTraceless (m := m) (n := n)) :
    normalizedHermitianBoundaryMap X =
      (((Fintype.card n : ℂ)⁻¹) • partialTraceRight (X : Matrix (m × n) (m × n) ℂ),
        ((Fintype.card m : ℂ)⁻¹) • partialTraceLeft (X : Matrix (m × n) (m × n) ℂ)) :=
  rfl

omit [Nonempty m] [Nonempty n] in
/-- The normalized boundary reports land in the exact Hermitian traceless factor spaces
`Herm₀(A) × Herm₀(B)`. -/
theorem normalizedHermitianBoundaryMap_mem_hermitianTracelessMatrices
    (X : hermitianJointTraceless (m := m) (n := n)) :
    (normalizedHermitianBoundaryMap X).1 ∈ hermitianTracelessMatrices m ∧
      (normalizedHermitianBoundaryMap X).2 ∈ hermitianTracelessMatrices n := by
  rw [normalizedHermitianBoundaryMap_apply]
  constructor
  · constructor
    · have hpartial := isSelfAdjoint_partialTraceRight X.property.1
      change
        ((((Fintype.card n : ℂ)⁻¹) •
          partialTraceRight (X : Matrix (m × n) (m × n) ℂ))ᴴ) =
            ((Fintype.card n : ℂ)⁻¹) •
              partialTraceRight (X : Matrix (m × n) (m × n) ℂ)
      change
        (partialTraceRight (X : Matrix (m × n) (m × n) ℂ))ᴴ =
          partialTraceRight (X : Matrix (m × n) (m × n) ℂ) at hpartial
      simp [hpartial]
    · change
        Matrix.trace (((Fintype.card n : ℂ)⁻¹) •
          partialTraceRight (X : Matrix (m × n) (m × n) ℂ)) = 0
      rw [Matrix.trace_smul, trace_partialTraceRight]
      have htrace : (X : Matrix (m × n) (m × n) ℂ).trace = 0 := X.property.2
      simp [htrace]
  · constructor
    · have hpartial := isSelfAdjoint_partialTraceLeft X.property.1
      change
        ((((Fintype.card m : ℂ)⁻¹) •
          partialTraceLeft (X : Matrix (m × n) (m × n) ℂ))ᴴ) =
            ((Fintype.card m : ℂ)⁻¹) •
              partialTraceLeft (X : Matrix (m × n) (m × n) ℂ)
      change
        (partialTraceLeft (X : Matrix (m × n) (m × n) ℂ))ᴴ =
          partialTraceLeft (X : Matrix (m × n) (m × n) ℂ) at hpartial
      simp [hpartial]
    · change
        Matrix.trace (((Fintype.card m : ℂ)⁻¹) •
          partialTraceLeft (X : Matrix (m × n) (m × n) ℂ)) = 0
      rw [Matrix.trace_smul, trace_partialTraceLeft]
      have htrace : (X : Matrix (m × n) (m × n) ℂ).trace = 0 := X.property.2
      simp [htrace]

/-- Card equation `(5.2)`: kernel of normalized boundary reporting is exactly the
Hermitian interaction cross-fibre, viewed inside the joint traceless sector. -/
theorem ker_normalizedHermitianBoundaryMap :
    LinearMap.ker (normalizedHermitianBoundaryMap (m := m) (n := n)) =
      (hermitianMatrixCrossFibre (m := m) (n := n)).comap
        (hermitianJointTraceless (m := m) (n := n)).subtype := by
  ext X
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  have hm : ((Fintype.card m : ℂ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have hn : ((Fintype.card n : ℂ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  simp only [normalizedHermitianBoundaryMap_apply, Prod.mk_eq_zero,
    smul_eq_zero, hm, hn, false_or]
  constructor
  · intro h
    exact ⟨X.property.1, h⟩
  · intro h
    exact h.2

/-- Exact Hermitian boundary/cross decomposition. -/
theorem hermitianJointTraceless_eq_local_sup_cross :
    hermitianJointTraceless (m := m) (n := n) =
      hermitianMatrixLocalReporter ⊔ hermitianMatrixCrossFibre := by
  apply le_antisymm
  · intro X hX
    have hJoint : (X : Matrix (m × n) (m × n) ℂ) ∈
        jointTracelessMatrices (m := m) (n := n) := hX.2
    rw [jointTracelessMatrices_eq_local_sup_cross, Submodule.mem_sup] at hJoint
    obtain ⟨L, hL, C, hC, hLC⟩ := hJoint
    have hstarSum : star L + star C = L + C := by
      calc
        star L + star C = star (L + C) := (star_add L C).symm
        _ = star (X : Matrix (m × n) (m × n) ℂ) := by rw [hLC]
        _ = X := hX.1
        _ = L + C := hLC.symm
    have hdLlocal : star L - L ∈ matrixLocalReporter (m := m) (n := n) :=
      (matrixLocalReporter (m := m) (n := n)).sub_mem
        (star_mem_matrixLocalReporter hL) hL
    have hdCcross : star C - C ∈ matrixCrossFibre (m := m) (n := n) :=
      (matrixCrossFibre (m := m) (n := n)).sub_mem
        (star_mem_matrixCrossFibre hC) hC
    have hdiff : star L - L = -(star C - C) := by
      calc
        star L - L = (star L + star C) - (L + star C) := by abel
        _ = (L + C) - (L + star C) := by rw [hstarSum]
        _ = -(star C - C) := by abel
    have hdLcross : star L - L ∈ matrixCrossFibre (m := m) (n := n) := by
      rw [hdiff]
      exact (matrixCrossFibre (m := m) (n := n)).neg_mem hdCcross
    have hdLzero : star L - L = 0 := by
      have hmem : star L - L ∈
          matrixLocalReporter (m := m) (n := n) ⊓ matrixCrossFibre :=
        ⟨hdLlocal, hdLcross⟩
      rw [matrixLocalReporter_inf_matrixCrossFibre_eq_bot] at hmem
      simpa using hmem
    have hLself : IsSelfAdjoint L := sub_eq_zero.mp hdLzero
    have hCself : IsSelfAdjoint C := by
      change star C = C
      rw [← sub_eq_zero]
      rw [← neg_eq_zero]
      rw [← hdiff, hdLzero]
    rw [Submodule.mem_sup]
    exact ⟨L, ⟨hLself, hL⟩, C, ⟨hCself, hC⟩, hLC⟩
  · intro X hX
    rw [Submodule.mem_sup] at hX
    obtain ⟨L, hL, C, hC, hLC⟩ := hX
    rw [← hLC]
    constructor
    · exact (selfAdjoint.submodule ℝ _).add_mem hL.1 hC.1
    · exact (jointTracelessMatrices (m := m) (n := n)).add_mem
        (matrixLocalReporter_le_jointTraceless hL.2)
        (matrixCrossFibre_le_jointTraceless hC.2)

/-- Local and cross Hermitian sectors have trivial intersection. -/
theorem hermitianMatrixLocalReporter_inf_hermitianMatrixCrossFibre_eq_bot :
    hermitianMatrixLocalReporter (m := m) (n := n) ⊓
      hermitianMatrixCrossFibre = ⊥ := by
  rw [eq_bot_iff]
  intro X hX
  have hComplex : (X : Matrix (m × n) (m × n) ℂ) ∈
      matrixLocalReporter (m := m) (n := n) ⊓ matrixCrossFibre :=
    ⟨hX.1.2, hX.2.2⟩
  rw [matrixLocalReporter_inf_matrixCrossFibre_eq_bot] at hComplex
  simpa using hComplex

/-- Hilbert--Schmidt orthogonality of exact Hermitian local and cross sectors. -/
theorem hsInner_eq_zero_of_mem_hermitianCross_of_mem_hermitianLocal
    {X L : Matrix (m × n) (m × n) ℂ}
    (hX : X ∈ hermitianMatrixCrossFibre (m := m) (n := n))
    (hL : L ∈ hermitianMatrixLocalReporter (m := m) (n := n)) :
    QuantumAlg.hsInner X L = 0 :=
  hsInner_eq_zero_of_mem_cross_of_mem_local hX.2 hL.2

omit [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] in
@[simp] theorem matrixCommutator_add_right
    (H X Y : Matrix (m × n) (m × n) ℂ) :
    matrixCommutator H (X + Y) = matrixCommutator H X + matrixCommutator H Y := by
  simp only [matrixCommutator, Matrix.mul_add, Matrix.add_mul]
  abel

omit [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] in
@[simp] theorem matrixCommutator_smul_right
    (H X : Matrix (m × n) (m × n) ℂ) (c : ℂ) :
    matrixCommutator H (c • X) = c • matrixCommutator H X := by
  simp only [matrixCommutator, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

omit [DecidableEq m] [DecidableEq n] [Nonempty m] [Nonempty n] in
theorem I_smul_matrixCommutator_isSelfAdjoint
    {H L : Matrix (m × n) (m × n) ℂ}
    (hH : IsSelfAdjoint H) (hL : IsSelfAdjoint L) :
    IsSelfAdjoint (Complex.I • matrixCommutator H L) := by
  change Hᴴ = H at hH
  change Lᴴ = L at hL
  change (Complex.I • matrixCommutator H L)ᴴ =
    Complex.I • matrixCommutator H L
  simp only [matrixCommutator, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_mul, hH, hL]
  simp
  module

/-- Exact Hermitian version of Card Theorem 5.2: first-order preservation of every
Hermitian local reporter is equivalent to a Hermitian local-plus-real-scalar Hamiltonian. -/
theorem preserves_hermitianMatrixLocalReporter_iff_localForm
    (H : selfAdjoint (Matrix (m × n) (m × n) ℂ)) :
    (∀ L : Matrix (m × n) (m × n) ℂ,
        L ∈ hermitianMatrixLocalReporter (m := m) (n := n) →
          Complex.I • matrixCommutator (H : Matrix (m × n) (m × n) ℂ) L ∈
            hermitianMatrixLocalReporter) ↔
      ∃ H₀ : selfAdjoint (Matrix m m ℂ),
        ∃ H₁ : selfAdjoint (Matrix n n ℂ),
          ∃ c : ℝ,
            (H : Matrix (m × n) (m × n) ℂ) =
              (H₀ : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ) +
                (1 : Matrix m m ℂ) ⊗ₖ (H₁ : Matrix n n ℂ) +
                  (c : ℂ) • ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ)) := by
  constructor
  · intro hpres
    have hpresComplex : ∀ L : Matrix (m × n) (m × n) ℂ,
        L ∈ matrixLocalReporter (m := m) (n := n) →
          matrixCommutator (H : Matrix (m × n) (m × n) ℂ) L ∈
            matrixLocalReporter := by
      intro L hL
      let LR : selfAdjoint (Matrix (m × n) (m × n) ℂ) := realPart L
      let LI : selfAdjoint (Matrix (m × n) (m × n) ℂ) := imaginaryPart L
      have hLRmem : (LR : Matrix (m × n) (m × n) ℂ) ∈
          matrixLocalReporter (m := m) (n := n) := by
        change (realPart L : Matrix (m × n) (m × n) ℂ) ∈ matrixLocalReporter
        rw [realPart_apply_coe]
        exact (matrixLocalReporter (m := m) (n := n)).smul_of_tower_mem _
          ((matrixLocalReporter (m := m) (n := n)).add_mem hL
            (star_mem_matrixLocalReporter hL))
      have hLImem : (LI : Matrix (m × n) (m × n) ℂ) ∈
          matrixLocalReporter (m := m) (n := n) := by
        change (imaginaryPart L : Matrix (m × n) (m × n) ℂ) ∈ matrixLocalReporter
        rw [imaginaryPart_apply_coe]
        exact (matrixLocalReporter (m := m) (n := n)).smul_mem _
          ((matrixLocalReporter (m := m) (n := n)).smul_of_tower_mem _
            ((matrixLocalReporter (m := m) (n := n)).sub_mem hL
              (star_mem_matrixLocalReporter hL)))
      have hcommRscaled := hpres (LR : Matrix (m × n) (m × n) ℂ)
        ⟨LR.property, hLRmem⟩
      have hcommIscaled := hpres (LI : Matrix (m × n) (m × n) ℂ)
        ⟨LI.property, hLImem⟩
      have hcommR : matrixCommutator (H : Matrix (m × n) (m × n) ℂ) LR ∈
          matrixLocalReporter (m := m) (n := n) := by
        have h := (matrixLocalReporter (m := m) (n := n)).smul_mem
          (-Complex.I) hcommRscaled.2
        simpa [smul_smul] using h
      have hcommI : matrixCommutator (H : Matrix (m × n) (m × n) ℂ) LI ∈
          matrixLocalReporter (m := m) (n := n) := by
        have h := (matrixLocalReporter (m := m) (n := n)).smul_mem
          (-Complex.I) hcommIscaled.2
        simpa [smul_smul] using h
      have hsplit := realPart_add_I_smul_imaginaryPart L
      rw [← hsplit, matrixCommutator_add_right, matrixCommutator_smul_right]
      exact (matrixLocalReporter (m := m) (n := n)).add_mem hcommR
        ((matrixLocalReporter (m := m) (n := n)).smul_mem Complex.I hcommI)
    have hcross : crossMatrixPart (H : Matrix (m × n) (m × n) ℂ) = 0 :=
      (crossMatrixPart_eq_zero_iff_preserves_local _).2 hpresComplex
    let Hmat : Matrix (m × n) (m × n) ℂ := H
    have hHmat : IsSelfAdjoint Hmat := H.property
    let H₀ : selfAdjoint (Matrix m m ℂ) :=
      ⟨leftReducedComponent Hmat,
        IsSelfAdjoint.leftReducedComponent (X := Hmat) hHmat⟩
    let H₁ : selfAdjoint (Matrix n n ℂ) :=
      ⟨rightReducedComponent Hmat,
        IsSelfAdjoint.rightReducedComponent (X := Hmat) hHmat⟩
    let c : ℝ := (bipartiteScalarCoeff Hmat).re
    refine ⟨H₀, H₁, c, ?_⟩
    have hc : (c : ℂ) = bipartiteScalarCoeff Hmat := by
      exact ofReal_re_bipartiteScalarCoeff hHmat
    have hdecomp := bipartite_decomposition Hmat
    rw [hcross, add_zero] at hdecomp
    simpa only [Hmat, H₀, H₁, c, leftLocalPart, rightLocalPart,
      scalarMatrixPart, hc] using hdecomp
  · rintro ⟨H₀, H₁, c, hform⟩
    intro L hL
    constructor
    · exact I_smul_matrixCommutator_isSelfAdjoint H.property hL.1
    · have hcomm := matrixCommutator_localForm_mem
        (H₀ : Matrix m m ℂ) (H₁ : Matrix n n ℂ) (c : ℂ) hL.2
      rw [← hform] at hcomm
      exact (matrixLocalReporter (m := m) (n := n)).smul_mem Complex.I hcomm

/-- Exact real dimension of the Hermitian interaction cross-fibre. -/
theorem finrank_hermitianMatrixCrossFibre :
    Module.finrank ℝ (hermitianMatrixCrossFibre (m := m) (n := n)) =
      (Fintype.card m * Fintype.card m - 1) *
        (Fintype.card n * Fintype.card n - 1) := by
  rw [QuantumAlg.finrank_selfAdjoint_inf_restrictScalars_eq
    (matrixCrossFibre (m := m) (n := n))
    (fun X hX => star_mem_matrixCrossFibre hX)]
  exact finrank_matrixCrossFibre

end HermitianCrossFibre

end

end HTGeometry.ConstraintRelativity
