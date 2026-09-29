import GaloisForLFunctions.HTGeometry.CubicApertureGaugedSynthesis
import GaloisForLFunctions.HTGeometry.GradedRowSynthesis

/-!
# The matrix-complete graded Euler–continuum carrier

On the direct sum `ℓ²(n ≥ 2) ⊕ L²(ds)` the row synthesis `A = [A_E A₀]` into the Burnol carrier
`H_B` is Hilbert–Schmidt.  Its range covariances `K_E = A_E A_E*` and `K₀ = A₀ A₀*` are
Schatten-one, and for the grading `J = diag(+1, -1)`

`K_rel = A J A* = K_E - K₀ ∈ S₁`,  `tr K_rel = ‖A_E‖²_HS - ‖A₀‖²_HS`.

The label Gram `A* A` keeps all blocks: its atomic block has kernel `2 a_n a_m/(log n + log m)³`
and its atomic–continuum block has kernel `2 a_n √(h_x(s)) d_c(s)^{3/2}/(log n + s)³`, both nonzero
on prime labels and positive continuum labels.  Doubling by complex conjugation (the features are
real, so the conjugate legs coincide with the originals) gives the four-leg carrier with grading
`diag(+, -, +, -)`, which is Hilbert–Schmidt with supertrace `Str K_four = 2 (tr K_E - tr K₀)`.
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance factTwoNeTopGradedCarrier : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## Conjugate kernels -/

namespace SqIntKernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- The complex-conjugate kernel `(y, x) ↦ conj k(y, x)`. -/
def conjKernel (k : SqIntKernel ν μ) : SqIntKernel ν μ where
  toFun y x := starRingEnd ℂ (k.toFun y x)
  measurable := Complex.continuous_conj.measurable.comp k.measurable
  energy_lt_top := by
    simp only [RCLike.enorm_conj]
    exact k.energy_lt_top

/-- A real kernel equals its conjugate, so its conjugate synthesis is the same operator. -/
theorem conj_op_of_real [SFinite μ] (k : SqIntKernel ν μ)
    (h : ∀ y x, starRingEnd ℂ (k.toFun y x) = k.toFun y x) : k.conjKernel.op = k.op :=
  op_congr _ (Eventually.of_forall fun y => Eventually.of_forall fun x => h y x)

end SqIntKernel

/-! ## The carrier -/

/-- The atomic label space `ℓ²(n ≥ 2)`. -/
abbrev AtomicLabelSpace := Lp ℂ 2 (Measure.count : Measure AtomLabel)

/-- The Burnol carrier `H_B = L²((0, ∞), dr)`. -/
abbrev BurnolCarrier := Lp ℂ 2 halfLineMeasure

theorem atomicCoefficient_pos {x c : ℝ} (hc : 0 < c) {n : AtomLabel}
    (hn : 0 < ArithmeticFunction.vonMangoldt (n : ℕ)) :
    0 < atomicCoefficient x c n := by
  have hn1 : (1 : ℝ) < (n : ℕ) := by exact_mod_cast (show 1 < (n : ℕ) by have := n.2; omega)
  have hd : 0 < 1 - ((n : ℕ) : ℝ) ^ (-(2 * c)) := by
    have : ((n : ℕ) : ℝ) ^ (-(2 * c)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hn1 (by linarith)
    linarith
  unfold atomicCoefficient
  have : 0 < ArithmeticFunction.vonMangoldt (n : ℕ) / ((n : ℕ) : ℝ) := div_pos hn (by linarith)
  have := Real.sqrt_pos.mpr this
  positivity

theorem cubicGaugeWeight_pos {x c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 < s) :
    0 < cubicGaugeWeight x c s := by
  have hd : 0 < apertureDefect c s := by
    rw [apertureDefect, sub_pos, Real.exp_lt_one_iff]
    have : 0 < 2 * c * s := by positivity
    linarith
  unfold cubicGaugeWeight
  have := Real.sqrt_pos.mpr (thetaDamping_pos x s)
  positivity

variable {x c : ℝ} (hx : 0 < x) (hc : 0 < c)

/-- **(CAGC.7).**  The row synthesis `A = [A_E A₀]`. -/
def eulerContinuumSynthesis :
    WithLp 2 (AtomicLabelSpace × BurnolCarrier) →L[ℂ] BurnolCarrier :=
  rowSynthesis (atomicSynthesis hx.le hc.le) (continuumSynthesis hx hc)

theorem isHilbertSchmidt_eulerContinuumSynthesis :
    IsHilbertSchmidt (eulerContinuumSynthesis hx hc) :=
  isHilbertSchmidt_rowSynthesis (isHilbertSchmidt_atomicSynthesis hx.le hc.le)
    (isHilbertSchmidt_continuumSynthesis hx hc)

/-- `K_E = A_E A_E*`. -/
def atomicCovariance : BurnolCarrier →L[ℂ] BurnolCarrier :=
  atomicSynthesis hx.le hc.le ∘L adjoint (atomicSynthesis hx.le hc.le)

/-- `K₀ = A₀ A₀*`. -/
def continuumCovariance : BurnolCarrier →L[ℂ] BurnolCarrier :=
  continuumSynthesis hx hc ∘L adjoint (continuumSynthesis hx hc)

/-- `K_rel = A J A*` with `J = diag(+1, -1)`. -/
def relativeCovariance : BurnolCarrier →L[ℂ] BurnolCarrier :=
  eulerContinuumSynthesis hx hc ∘L gradingOp 1 (-1) ∘L adjoint (eulerContinuumSynthesis hx hc)

/-- **(CAGC.8).**  Both range covariances are nuclear. -/
theorem memSchattenClass_one_covariances :
    RHTower.MemSchattenClass 1 (atomicCovariance hx hc) ∧
      RHTower.MemSchattenClass 1 (continuumCovariance hx hc) :=
  ⟨memSchattenClass_one_comp_adjoint (isHilbertSchmidt_atomicSynthesis hx.le hc.le),
    memSchattenClass_one_comp_adjoint (isHilbertSchmidt_continuumSynthesis hx hc)⟩

/-- **(CAGC.8).**  `K_rel = K_E - K₀`. -/
theorem relativeCovariance_eq :
    relativeCovariance hx hc = atomicCovariance hx hc - continuumCovariance hx hc := by
  rw [relativeCovariance, eulerContinuumSynthesis, rowSynthesis_grading_adjoint, one_smul,
    neg_one_smul, ← sub_eq_add_neg]
  rfl

/-- **(CAGC.8).**  `K_rel ∈ S₁` with `tr K_rel = tr K_E - tr K₀`. -/
theorem relativeCovariance_traceClass :
    RHTower.MemSchattenClass 1 (relativeCovariance hx hc) ∧
      opTrace (relativeCovariance hx hc)
        = opTrace (atomicCovariance hx hc) - opTrace (continuumCovariance hx hc) := by
  have h := gradedCovariance_traceClass (isHilbertSchmidt_atomicSynthesis hx.le hc.le)
    (isHilbertSchmidt_continuumSynthesis hx hc) 1 (-1)
  have hrel : relativeCovariance hx hc = (1 : ℂ) • (atomicSynthesis hx.le hc.le ∘L
      adjoint (atomicSynthesis hx.le hc.le)) + (-1 : ℂ) • (continuumSynthesis hx hc ∘L
      adjoint (continuumSynthesis hx hc)) := by
    rw [relativeCovariance, eulerContinuumSynthesis, rowSynthesis_grading_adjoint]
  refine ⟨hrel ▸ h.1, ?_⟩
  rw [hrel, h.2, atomicCovariance, continuumCovariance,
    opTrace_comp_adjoint (isHilbertSchmidt_atomicSynthesis hx.le hc.le),
    opTrace_comp_adjoint (isHilbertSchmidt_continuumSynthesis hx hc)]
  ring

/-- The label Gram `A* A` is Schatten-one. -/
theorem memSchattenClass_one_labelGram :
    RHTower.MemSchattenClass 1
      (adjoint (eulerContinuumSynthesis hx hc) ∘L eulerContinuumSynthesis hx hc) :=
  RHTower.memSchattenClass_one_comp (isHilbertSchmidt_eulerContinuumSynthesis hx hc).adjoint
    (isHilbertSchmidt_eulerContinuumSynthesis hx hc)

/-! ## The label Gram blocks -/

/-- **(CAGC.9).**  The atomic block of the label Gram is the kernel operator with kernel
`2 a_n a_m/(log n + log m)³`. -/
theorem atomicGram_eq :
    adjoint (atomicSynthesis hx.le hc.le) ∘L atomicSynthesis hx.le hc.le
      = ((atomicKernel hx.le hc.le).adjoint.comp (atomicKernel hx.le hc.le)).op := by
  rw [SqIntKernel.op_comp, atomicSynthesis, SqIntKernel.adjoint_op]

theorem atomicGram_toFun (n m : AtomLabel) :
    ((atomicKernel hx.le hc.le).adjoint.comp (atomicKernel hx.le hc.le)).toFun n m
      = ((2 * atomicCoefficient x c n * atomicCoefficient x c m
          / (Real.log (n : ℕ) + Real.log (m : ℕ)) ^ 3 : ℝ) : ℂ) := by
  change ∫ r, starRingEnd ℂ (((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r :
      ℝ) : ℂ)) * ((atomicCoefficient x c m * burnolRadial (Real.log (m : ℕ)) r : ℝ) : ℂ)
      ∂halfLineMeasure = _
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  have h : ∀ r, atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r *
      (atomicCoefficient x c m * burnolRadial (Real.log (m : ℕ)) r)
      = atomicCoefficient x c n * atomicCoefficient x c m *
        (burnolRadial (Real.log (n : ℕ)) r * burnolRadial (Real.log (m : ℕ)) r) := fun r => by
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_burnolRadial_mul (by
    linarith [log_pos_of_atomLabel n, log_pos_of_atomLabel m])]
  ring

/-- **(CAGC.10).**  The atomic–continuum block is the kernel operator with kernel
`2 a_n √(h_x(s)) d_c(s)^{3/2}/(log n + s)³`. -/
theorem mixedGram_eq :
    adjoint (atomicSynthesis hx.le hc.le) ∘L continuumSynthesis hx hc
      = ((atomicKernel hx.le hc.le).adjoint.comp (continuumKernel hx hc)).op := by
  rw [SqIntKernel.op_comp, atomicSynthesis, SqIntKernel.adjoint_op]
  rfl

theorem mixedGram_toFun (n : AtomLabel) {s : ℝ} (hs : 0 ≤ s) :
    ((atomicKernel hx.le hc.le).adjoint.comp (continuumKernel hx hc)).toFun n s
      = ((2 * atomicCoefficient x c n * cubicGaugeWeight x c s
          / (Real.log (n : ℕ) + s) ^ 3 : ℝ) : ℂ) := by
  change ∫ r, starRingEnd ℂ (((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r :
      ℝ) : ℂ)) * ((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ) ∂halfLineMeasure = _
  simp_rw [Complex.conj_ofReal, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  have h : ∀ r, atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r *
      (cubicGaugeWeight x c s * burnolRadial s r)
      = atomicCoefficient x c n * cubicGaugeWeight x c s *
        (burnolRadial (Real.log (n : ℕ)) r * burnolRadial s r) := fun r => by ring
  simp_rw [h]
  rw [integral_const_mul, integral_burnolRadial_mul (by linarith [log_pos_of_atomLabel n])]
  ring

/-- **(CAGC.9)–(CAGC.10).**  Distinct-prime and atomic–continuum Gram entries are nonzero. -/
theorem labelGram_entries_ne_zero {n m : AtomLabel}
    (hn : 0 < ArithmeticFunction.vonMangoldt (n : ℕ))
    (hm : 0 < ArithmeticFunction.vonMangoldt (m : ℕ)) {s : ℝ} (hs : 0 < s) :
    ((atomicKernel hx.le hc.le).adjoint.comp (atomicKernel hx.le hc.le)).toFun n m ≠ 0 ∧
      ((atomicKernel hx.le hc.le).adjoint.comp (continuumKernel hx hc)).toFun n s ≠ 0 := by
  have hln := log_pos_of_atomLabel n
  have hlm := log_pos_of_atomLabel m
  have ha := atomicCoefficient_pos (x := x) hc hn
  have hb := atomicCoefficient_pos (x := x) hc hm
  have hw := cubicGaugeWeight_pos (x := x) hc hs
  rw [atomicGram_toFun hx hc, mixedGram_toFun hx hc n hs.le, Ne, Ne, Complex.ofReal_eq_zero,
    Complex.ofReal_eq_zero]
  constructor <;> positivity

/-! ## The four-leg carrier -/

/-- The conjugate atomic synthesis. -/
def conjAtomicSynthesis : AtomicLabelSpace →L[ℂ] BurnolCarrier :=
  (atomicKernel hx.le hc.le).conjKernel.op

/-- The conjugate continuum synthesis. -/
def conjContinuumSynthesis : BurnolCarrier →L[ℂ] BurnolCarrier :=
  (continuumKernel hx hc).conjKernel.op

theorem conjAtomicSynthesis_eq : conjAtomicSynthesis hx hc = atomicSynthesis hx.le hc.le :=
  SqIntKernel.conj_op_of_real _ fun _ _ => Complex.conj_ofReal _

theorem conjContinuumSynthesis_eq : conjContinuumSynthesis hx hc = continuumSynthesis hx hc :=
  SqIntKernel.conj_op_of_real _ fun _ _ => Complex.conj_ofReal _

/-- The four-leg synthesis `[A_E A₀ Ā_E Ā₀]`. -/
def fourLegSynthesis :
    WithLp 2 (WithLp 2 (AtomicLabelSpace × BurnolCarrier) ×
      WithLp 2 (AtomicLabelSpace × BurnolCarrier)) →L[ℂ] BurnolCarrier :=
  rowSynthesis (eulerContinuumSynthesis hx hc)
    (rowSynthesis (conjAtomicSynthesis hx hc) (conjContinuumSynthesis hx hc))

/-- The four-leg supercovariance with grading `diag(+, -, +, -)`. -/
def fourLegSupercovariance : BurnolCarrier →L[ℂ] BurnolCarrier :=
  fourLegSynthesis hx hc ∘L blockDiag (gradingOp 1 (-1)) (gradingOp 1 (-1)) ∘L
    adjoint (fourLegSynthesis hx hc)

/-- **Theorem CAGC-C.**  The four-leg synthesis is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_fourLegSynthesis : IsHilbertSchmidt (fourLegSynthesis hx hc) := by
  unfold fourLegSynthesis
  rw [conjAtomicSynthesis_eq, conjContinuumSynthesis_eq]
  exact isHilbertSchmidt_rowSynthesis (isHilbertSchmidt_eulerContinuumSynthesis hx hc)
    (isHilbertSchmidt_eulerContinuumSynthesis hx hc)

theorem fourLegSupercovariance_eq :
    fourLegSupercovariance hx hc = (2 : ℂ) • relativeCovariance hx hc := by
  rw [fourLegSupercovariance, fourLegSynthesis, rowSynthesis_blockDiag_adjoint,
    conjAtomicSynthesis_eq, conjContinuumSynthesis_eq]
  change relativeCovariance hx hc + relativeCovariance hx hc = _
  rw [two_smul]

/-- **(CAGC.11).**  `Str K_four = 2 (tr K_E - tr K₀)`, with every term finite. -/
theorem fourLegSupertrace :
    RHTower.MemSchattenClass 1 (fourLegSupercovariance hx hc) ∧
      opTrace (fourLegSupercovariance hx hc)
        = 2 * (opTrace (atomicCovariance hx hc) - opTrace (continuumCovariance hx hc)) := by
  rw [fourLegSupercovariance_eq]
  refine ⟨RHTower.memSchattenClass_one_smul (relativeCovariance_traceClass hx hc).1 2, ?_⟩
  rw [RHTower.opTrace_smul, (relativeCovariance_traceClass hx hc).2]

end GaloisForLFunctions.HTGeometry
