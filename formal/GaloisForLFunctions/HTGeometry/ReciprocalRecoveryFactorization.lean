import GaloisForLFunctions.HTGeometry.ReciprocalWorkWeightedCompactness
import GaloisForLFunctions.HTGeometry.BoundedDiagonalOperatorLp
import GaloisForLFunctions.HTGeometry.LpDiagonalOperator
import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionOperatorLaw
import GaloisForLFunctions.RHTower.MertensClockRelativeDeterminant
import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass

/-!
# Exact reciprocal recovery factorization

On `H = ℓ²(ℕ; ℂ)`, a bounded real sequence `y` defines the positive diagonal
`E_y e_j = e^{y_j} e_j`.  For a finite-work sequence `x` put `Q_x = E_{x/2}` and
`B_x = Q_x⁻¹ = E_{-x/2}`.

* **Theorem 4.1, `(RFT.16)`–`(RFT.21)`**: `B_x Q_x = Q_x B_x = I`; `Q_x* Q_x = E_x`,
  `B_x B_x* = E_{-x}`, the Grams multiply to `I`, reversal swaps them; `Q_x - B_x` maps `H` into
  the natural domain of the complexity diagonal `A_a`, and `A_a(Q_x - B_x)` is the
  Hilbert–Schmidt diagonal with `‖A_a(Q_x - B_x)‖²_HS = 𝒲_a(x)`; `E_{x+y} = E_x E_y`.
* **Theorem 6.1, `(RFT.29)`**: for summable `x`, `S_x - I` and `S_x⁻¹ - I` are trace class and
  the Fredholm determinant is `det(S_x) = exp(½ ∑ x_j)`; `x = (t, -t, 0, …)` has determinant `1`
  and positive work.
* **`(RFT.30)`**: the Gram `Q_x* Q_x` reconstructs `x` (`x_j = log ⟨e_j, Q_x* Q_x e_j⟩`).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open Filter Topology ContinuousLinearMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ReciprocalFusion

/-- The Hilbert space `ℓ²(ℕ; ℂ)`. -/
abbrev H2 := lp (fun _ : ℕ => ℂ) 2

theorem exp_le_of_abs_le {y : ℕ → ℝ} {B : ℝ} (hB : ∀ j, |y j| ≤ B) (j : ℕ) :
    ‖((Real.exp (y j) : ℝ) : ℂ)‖ ≤ Real.exp B := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (hB j))

/-- The positive diagonal `E_y e_j = e^{y_j} e_j` of a bounded real sequence. -/
def expDiag (y : ℕ → ℝ) (hy : ∃ B, ∀ j, |y j| ≤ B) : H2 →L[ℂ] H2 :=
  LpDiagonal.lpDiag (fun j => ((Real.exp (y j) : ℝ) : ℂ)) (Real.exp hy.choose)
    (Real.exp_pos _).le (exp_le_of_abs_le hy.choose_spec)

@[simp] theorem expDiag_apply (y : ℕ → ℝ) (hy : ∃ B, ∀ j, |y j| ≤ B) (v : H2) (j : ℕ) :
    (expDiag y hy v : ℕ → ℂ) j = ((Real.exp (y j) : ℝ) : ℂ) * (v : ℕ → ℂ) j := rfl

theorem bounded_neg {y : ℕ → ℝ} (hy : ∃ B, ∀ j, |y j| ≤ B) : ∃ B, ∀ j, |(-y) j| ≤ B :=
  let ⟨B, hB⟩ := hy; ⟨B, fun j => by simpa using hB j⟩

theorem bounded_add {y z : ℕ → ℝ} (hy : ∃ B, ∀ j, |y j| ≤ B) (hz : ∃ B, ∀ j, |z j| ≤ B) :
    ∃ B, ∀ j, |(y + z) j| ≤ B :=
  let ⟨B, hB⟩ := hy; let ⟨C, hC⟩ := hz
  ⟨B + C, fun j => (abs_add_le _ _).trans (add_le_add (hB j) (hC j))⟩

theorem bounded_smul {y : ℕ → ℝ} (hy : ∃ B, ∀ j, |y j| ≤ B) (c : ℝ) :
    ∃ B, ∀ j, |(c • y) j| ≤ B :=
  let ⟨B, hB⟩ := hy
  ⟨|c| * B, fun j => by
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg c)⟩

/-- `E_{y+z} = E_y E_z`. -/
theorem expDiag_add {y z : ℕ → ℝ} (hy : ∃ B, ∀ j, |y j| ≤ B) (hz : ∃ B, ∀ j, |z j| ≤ B) :
    expDiag (y + z) (bounded_add hy hz) = expDiag y hy ∘L expDiag z hz := by
  ext v j
  simp only [expDiag_apply, comp_apply, Pi.add_apply, Real.exp_add, Complex.ofReal_mul]
  ring

theorem expDiag_zero (h : ∃ B, ∀ j, |(0 : ℕ → ℝ) j| ≤ B) : expDiag 0 h = 1 := by
  ext v j
  simp

/-- A real positive diagonal is self-adjoint. -/
theorem adjoint_expDiag (y : ℕ → ℝ) (hy : ∃ B, ∀ j, |y j| ≤ B) :
    adjoint (expDiag y hy) = expDiag y hy := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v w => ?_).symm
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  simp only [expDiag_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- A finite-work sequence is bounded. -/
theorem bounded_of_summable_workTerm {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ a j) {x : ℕ → ℝ}
    (hx : Summable (workTerm a x)) : ∃ B, ∀ j, |x j| ≤ B :=
  ⟨_, (sq_summable_and_le ha hx).2.2.2.2⟩

section Recovery

variable {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ a j) {x : ℕ → ℝ} (hx : Summable (workTerm a x))

/-- **`(RFT.16)`–`(RFT.17)`** the recovery leg `Q_x = S_x`, `S_x e_j = e^{x_j/2} e_j`. -/
def recoveryQ : H2 →L[ℂ] H2 :=
  expDiag ((1 / 2 : ℝ) • x) (bounded_smul (bounded_of_summable_workTerm ha hx) _)

/-- **`(RFT.17)`** the reflected leg `B_x = S_x⁻¹ = S_{-x}`. -/
def recoveryB : H2 →L[ℂ] H2 :=
  expDiag (-((1 / 2 : ℝ) • x))
    (bounded_neg (bounded_smul (bounded_of_summable_workTerm ha hx) _))

@[simp] theorem recoveryQ_apply (v : H2) (j : ℕ) :
    (recoveryQ ha hx v : ℕ → ℂ) j = ((Real.exp (x j / 2) : ℝ) : ℂ) * (v : ℕ → ℂ) j := by
  simp [recoveryQ, div_eq_inv_mul]

@[simp] theorem recoveryB_apply (v : H2) (j : ℕ) :
    (recoveryB ha hx v : ℕ → ℂ) j = ((Real.exp (-(x j / 2)) : ℝ) : ℂ) * (v : ℕ → ℂ) j := by
  simp [recoveryB, div_eq_inv_mul]

/-- **Theorem 4.1, `(RFT.18)`**: `B_x Q_x = Q_x B_x = I`. -/
theorem recovery_inverse :
    recoveryB ha hx ∘L recoveryQ ha hx = 1 ∧ recoveryQ ha hx ∘L recoveryB ha hx = 1 := by
  constructor <;>
  · ext v j
    simp only [comp_apply, recoveryQ_apply, recoveryB_apply, one_apply_eq_self]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp

/-- **Theorem 4.1, `(RFT.19)`**: `Q_x* Q_x = E_x`, `B_x B_x* = E_{-x}`, the Grams multiply to the
identity, and reversal `x ↦ -x` exchanges them. -/
theorem recovery_grams :
    adjoint (recoveryQ ha hx) ∘L recoveryQ ha hx =
        expDiag x (bounded_of_summable_workTerm ha hx) ∧
      recoveryB ha hx ∘L adjoint (recoveryB ha hx) =
        expDiag (-x) (bounded_neg (bounded_of_summable_workTerm ha hx)) ∧
      (adjoint (recoveryQ ha hx) ∘L recoveryQ ha hx) ∘L
          (recoveryB ha hx ∘L adjoint (recoveryB ha hx)) = 1 ∧
      (∀ hx' : Summable (workTerm a (-x)),
        adjoint (recoveryQ ha hx') ∘L recoveryQ ha hx' =
          recoveryB ha hx ∘L adjoint (recoveryB ha hx)) := by
  have hQ : adjoint (recoveryQ ha hx) = recoveryQ ha hx := adjoint_expDiag _ _
  have hB : adjoint (recoveryB ha hx) = recoveryB ha hx := adjoint_expDiag _ _
  have hGQ : adjoint (recoveryQ ha hx) ∘L recoveryQ ha hx =
      expDiag x (bounded_of_summable_workTerm ha hx) := by
    rw [hQ]
    ext v j
    simp only [comp_apply, recoveryQ_apply, expDiag_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_halves]
  have hGB : recoveryB ha hx ∘L adjoint (recoveryB ha hx) =
      expDiag (-x) (bounded_neg (bounded_of_summable_workTerm ha hx)) := by
    rw [hB]
    ext v j
    simp only [comp_apply, recoveryB_apply, expDiag_apply, Pi.neg_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  refine ⟨hGQ, hGB, ?_, fun hx' => ?_⟩
  · rw [hGQ, hGB]
    ext v j
    simp only [comp_apply, expDiag_apply, one_apply_eq_self, Pi.neg_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  · rw [hGB, show adjoint (recoveryQ ha hx') = recoveryQ ha hx' from adjoint_expDiag _ _]
    ext v j
    simp only [comp_apply, recoveryQ_apply, expDiag_apply, Pi.neg_apply]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_halves]

/-- **Theorem 4.1, `(RFT.21)`**: formation composition is exact, `S_{x+y} = S_x S_y`. -/
theorem recoveryQ_add {y : ℕ → ℝ} (hy : Summable (workTerm a y))
    (hxy : Summable (workTerm a (x + y))) :
    recoveryQ ha hxy = recoveryQ ha hx ∘L recoveryQ ha hy := by
  ext v j
  simp only [comp_apply, recoveryQ_apply, Pi.add_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-! ### The complexity diagonal and the Hilbert–Schmidt work identity -/

/-- The natural domain `{v : (a_j v_j) ∈ ℓ²}` of the complexity diagonal. -/
def complexityDomain (a : ℕ → ℝ) : Submodule ℂ H2 where
  carrier := {v | Memℓp (fun j => (a j : ℂ) * (v : ℕ → ℂ) j) 2}
  zero_mem' := by
    show Memℓp (fun j => (a j : ℂ) * ((0 : H2) : ℕ → ℂ) j) 2
    simp only [lp.coeFn_zero, Pi.zero_apply, mul_zero]
    exact zero_memℓp
  add_mem' {v w} hv hw := by
    show Memℓp (fun j => (a j : ℂ) * ((v + w : H2) : ℕ → ℂ) j) 2
    have := hv.add hw
    convert this using 1
    funext j
    simp [mul_add]
  smul_mem' c v hv := by
    show Memℓp (fun j => (a j : ℂ) * ((c • v : H2) : ℕ → ℂ) j) 2
    have := hv.const_smul c
    convert this using 1
    funext j
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- **`A_a`**, the source-complexity diagonal `A_a e_j = a_j e_j` on its natural domain. -/
def complexityOp (a : ℕ → ℝ) : H2 →ₗ.[ℂ] H2 where
  domain := complexityDomain a
  toFun :=
    { toFun := fun v => ⟨fun j => (a j : ℂ) * ((v : H2) : ℕ → ℂ) j, v.2⟩
      map_add' := fun v w => by
        refine lp.ext (funext fun j => ?_)
        simp [mul_add]
      map_smul' := fun c v => by
        refine lp.ext (funext fun j => ?_)
        simp only [Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }

theorem complexityOp_apply (v : complexityDomain a) (j : ℕ) :
    (complexityOp a v : ℕ → ℂ) j = (a j : ℂ) * ((v : H2) : ℕ → ℂ) j := rfl

/-- The diagonal coefficients `a_j (e^{x_j/2} - e^{-x_j/2})` of `A_a(Q_x - B_x)`. -/
def defectWeight (a x : ℕ → ℝ) (j : ℕ) : ℂ :=
  ((a j * (Real.exp (x j / 2) - Real.exp (-(x j / 2))) : ℝ) : ℂ)

theorem norm_defectWeight_sq (j : ℕ) : ‖defectWeight a x j‖ ^ 2 = workTerm a x j := by
  rw [defectWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs, workTerm, mul_pow,
    reciprocalWork]
  congr 1
  have h1 : Real.exp (x j / 2) ^ 2 = Real.exp (x j) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : Real.exp (-(x j / 2)) ^ 2 = Real.exp (-x j) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : Real.exp (x j / 2) * Real.exp (-(x j / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [h1, h2, h3]

theorem summable_defectWeight (hx : Summable (workTerm a x)) :
    Summable fun j => ‖defectWeight a x j‖ ^ (2 : ℕ) :=
  hx.congr fun j => (norm_defectWeight_sq j).symm

/-- **Theorem 4.1, `(RFT.20)`**: `Q_x - B_x` maps `H` into the domain of `A_a`, the composition
`A_a(Q_x - B_x)` is the Hilbert–Schmidt diagonal with coefficients `a_j(e^{x_j/2} - e^{-x_j/2})`,
and `‖A_a(Q_x - B_x)‖²_HS = 𝒲_a(x)`. -/
theorem complexity_defect_hilbertSchmidt :
    ∃ hdom : ∀ v : H2, (recoveryQ ha hx - recoveryB ha hx) v ∈ complexityDomain a,
      (∀ v : H2, complexityOp a ⟨_, hdom v⟩ =
        HilbertSchmidt.diagOp (defectWeight a x) (summable_defectWeight hx) v) ∧
      (HilbertSchmidt.diagOp (defectWeight a x) (summable_defectWeight hx)).IsHilbertSchmidt ∧
      hsNormSq (HilbertSchmidt.diagOp (defectWeight a x) (summable_defectWeight hx)) =
        work a x := by
  have hcoord : ∀ (v : H2) (j : ℕ), (a j : ℂ) * (((recoveryQ ha hx - recoveryB ha hx) v :
      H2) : ℕ → ℂ) j = defectWeight a x j * (v : ℕ → ℂ) j := fun v j => by
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, recoveryQ_apply, recoveryB_apply,
      defectWeight, Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  have hbound : ∀ j, ‖defectWeight a x j‖ ≤ Real.sqrt (work a x) := fun j => by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_defectWeight_sq]
    exact Real.sqrt_le_sqrt (workTerm_le_work hx j)
  have hdom : ∀ v : H2, (recoveryQ ha hx - recoveryB ha hx) v ∈ complexityDomain a :=
    fun v => by
      show Memℓp (fun j => (a j : ℂ) * (((recoveryQ ha hx - recoveryB ha hx) v : H2) :
        ℕ → ℂ) j) 2
      have := LpDiagonal.memℓp_diag hbound v
      convert this using 1
      funext j
      exact hcoord v j
  refine ⟨hdom, fun v => ?_, HilbertSchmidt.isHilbertSchmidt_diagOp _ _, ?_⟩
  · refine lp.ext (funext fun j => ?_)
    rw [complexityOp_apply, HilbertSchmidt.diagOp_apply]
    exact hcoord v j
  · rw [HilbertSchmidt.hsNormSq_diagOp, work]
    exact tsum_congr fun j => norm_defectWeight_sq j

/-- **`(RFT.30)`**: the Gram `Q_x* Q_x` reconstructs every radial coordinate,
`x_j = log ⟨e_j, Q_x* Q_x e_j⟩`. -/
theorem gram_reconstructs (j : ℕ) :
    x j = Real.log (⟪lp.single 2 j (1 : ℂ),
      (adjoint (recoveryQ ha hx) ∘L recoveryQ ha hx) (lp.single 2 j (1 : ℂ))⟫_ℂ).re := by
  rw [(recovery_grams ha hx).1, lp.inner_single_left, expDiag_apply, lp.single_apply,
    Pi.single_eq_same, RCLike.inner_apply, map_one, mul_one, mul_one, Complex.ofReal_re,
    Real.log_exp]

end Recovery

/-- **`(RFT.30)`**: equal Grams force equal sequences. -/
theorem gram_injective {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ a j) {x y : ℕ → ℝ}
    (hx : Summable (workTerm a x)) (hy : Summable (workTerm a y))
    (h : adjoint (recoveryQ ha hx) ∘L recoveryQ ha hx =
      adjoint (recoveryQ ha hy) ∘L recoveryQ ha hy) : x = y := by
  funext j
  rw [gram_reconstructs ha hx j, gram_reconstructs ha hy j, h]

/-! ### Theorem 6.1: the Fredholm determinant -/

section Determinant

open HilbertSchmidt

theorem abs_exp_sub_one_le (u : ℝ) : |Real.exp u - 1| ≤ |u| * Real.exp |u| := by
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu, abs_of_nonneg (by linarith [Real.add_one_le_exp u])]
    have h := Real.add_one_le_exp (-u)
    have he := Real.exp_pos u
    have : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  · rw [abs_of_nonpos hu, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 hu])]
    have h := Real.add_one_le_exp u
    have h1 : 1 ≤ Real.exp (-u) := Real.one_le_exp (by linarith)
    nlinarith

/-- The entries `e^{c x_j} - 1` of `E_{c x} - I` are absolutely summable for summable `x`. -/
theorem summable_abs_exp_sub_one {x : ℕ → ℝ} (hx : Summable fun j => |x j|) (c : ℝ) :
    Summable fun j => |Real.exp (c * x j) - 1| := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ j, |x j| ≤ B :=
    ⟨∑' j, |x j|, fun j => hx.le_tsum j fun k _ => abs_nonneg _⟩
  refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_)
    (hx.mul_left (|c| * Real.exp (|c| * B)))
  calc |Real.exp (c * x j) - 1| ≤ |c * x j| * Real.exp |c * x j| := abs_exp_sub_one_le _
    _ ≤ (|c| * |x j|) * Real.exp (|c| * B) := by
        rw [abs_mul]
        gcongr
        exact hB j
    _ = |c| * Real.exp (|c| * B) * |x j| := by ring

/-- `E_{c x} - I` is the real summable diagonal with entries `e^{c x_j} - 1`. -/
theorem expDiag_sub_one {x : ℕ → ℝ} (hx : Summable fun j => |x j|) (c : ℝ)
    (h : ∃ B, ∀ j, |(c • x) j| ≤ B) :
    expDiag (c • x) h - 1 =
      realSummableDiagonalOperator (fun j => Real.exp (c * x j) - 1)
        (summable_abs_exp_sub_one hx c) := by
  ext v j
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, expDiag_apply, one_apply_eq_self,
    realSummableDiagonalOperator_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
    Complex.ofReal_one]
  ring

/-- The coordinate matrix of a diagonal operator in the standard basis is the diagonal kernel. -/
theorem coordMatrix_realSummableDiagonalOperator (w : ℕ → ℝ) (hw : Summable fun j => |w j|) :
    RHTower.coordMatrix (lpBasis ℕ) (realSummableDiagonalOperator w hw) =
      diagMul fun j => (w j : ℂ) := by
  funext p
  rcases p with ⟨i, j⟩
  rw [RHTower.coordMatrix_apply, lpBasis_apply, lpBasis_apply, lp.inner_single_left,
    realSummableDiagonalOperator_apply, lp.coeFn_single]
  by_cases h : i = j
  · subst h
    simp [diagMul, RCLike.inner_apply]
  · simp [diagMul, h, RCLike.inner_apply]

/-- The entire regularized determinant of a summable diagonal at `z = -1`:
`det₂(I + diag g) = ∏ (1 + g_j) e^{-g_j}`. -/
theorem entireDet2_diagMul_neg_one {g : ℕ → ℂ} (hs2 : Summable fun j => ‖g j‖ ^ (2 : ℕ))
    {P : ℂ} (hP : HasProd (fun j => (1 + g j) * Complex.exp (-g j)) P) :
    GaloisForLFunctions.HTGeometry.entireDet2 (diagMul g) (-1) = P := by
  have hHS : IsHS (diagMul g) := isHS_diagMul_infinite g hs2
  have hdet := GaloisForLFunctions.HTGeometry.tendsto_finiteDet2_entireDet2 hHS (-1 : ℂ)
  have hfin : (fun s : Finset ℕ => GaloisForLFunctions.HTGeometry.finiteDet2
      (-(blockMatrix (diagMul g) s)) (-1)) =
      fun s : Finset ℕ => ∏ i ∈ s, (1 + g i) * Complex.exp (-g i) := by
    funext s
    let M : Matrix s s ℂ := -(blockMatrix (diagMul g) s)
    have htri : M.BlockTriangular id := by
      intro i k hik
      have hne : (i : ℕ) ≠ k := fun h => (ne_of_lt hik) (Subtype.ext h.symm)
      simp [M, blockMatrix, diagMul, hne]
    have hdet := GaloisForLFunctions.HTGeometry.finiteDet2_eq_prod
      (M := M) (U := (1 : Matrix s s ℂ)) (T := M) (by simp) (by simp) htri (by simp) (-1 : ℂ)
    rw [hdet, Finset.prod_subtype s (fun _ => Iff.rfl)
      (fun i => (1 + g i) * Complex.exp (-g i))]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [M, blockMatrix, diagMul]
  rw [hfin] at hdet
  exact tendsto_nhds_unique hdet hP

/-- **Theorem 6.1, `(RFT.29)`**: for summable `x`, `S_x - I` and `S_x⁻¹ - I` are trace class and
the Fredholm determinant of `S_x = E_{x/2}` is `exp(½ ∑ x_j)`. -/
theorem fredholmDet_recovery {x : ℕ → ℝ} (hx : Summable fun j => |x j|)
    (h : ∃ B, ∀ j, |((1 / 2 : ℝ) • x) j| ≤ B) (h' : ∃ B, ∀ j, |((-(1 / 2) : ℝ) • x) j| ≤ B) :
    RHTower.MemSchattenClass 1 (expDiag ((1 / 2 : ℝ) • x) h - 1) ∧
      RHTower.MemSchattenClass 1 (expDiag ((-(1 / 2) : ℝ) • x) h' - 1) ∧
      RHTower.fredholmDetOp (lpBasis ℕ) (expDiag ((1 / 2 : ℝ) • x) h - 1) =
        Complex.exp ((1 / 2 : ℂ) * ((∑' j, x j : ℝ) : ℂ)) := by
  set g : ℕ → ℝ := fun j => Real.exp ((1 / 2 : ℝ) * x j) - 1
  have hg := summable_abs_exp_sub_one hx (1 / 2)
  rw [expDiag_sub_one hx _ h, expDiag_sub_one hx _ h']
  refine ⟨realSummableDiagonalOperator_memSchattenClass_one _ _,
    realSummableDiagonalOperator_memSchattenClass_one _ _, ?_⟩
  have hS1 := realSummableDiagonalOperator_memSchattenClass_one g hg
  -- the trace is `∑ g_j`
  have htr : opTrace (realSummableDiagonalOperator g hg) = ((∑' j, g j : ℝ) : ℂ) := by
    rw [RHTower.opTrace_eq_tsum_basis_of_memSchattenClass_one hS1 (lpBasis ℕ),
      Complex.ofReal_tsum]
    refine tsum_congr fun j => ?_
    rw [lpBasis_apply, lp.inner_single_left, realSummableDiagonalOperator_apply,
      lp.single_apply, Pi.single_eq_same]
    simp
  -- the regularized determinant is `exp(∑ (x_j/2 - g_j))`
  have hgs : Summable g := hg.of_abs
  have hxs : Summable x := hx.of_abs
  have hsum : HasSum (fun j => (((1 / 2 : ℝ) * x j - g j : ℝ) : ℂ))
      ((((1 / 2 : ℝ) * ∑' j, x j - ∑' j, g j : ℝ)) : ℂ) := by
    have := ((hxs.hasSum.mul_left (1 / 2 : ℝ)).sub hgs.hasSum)
    exact (Complex.ofRealCLM.hasSum this)
  have hprod : HasProd (fun j => (1 + (g j : ℂ)) * Complex.exp (-(g j : ℂ)))
      (Complex.exp (((1 / 2 : ℝ) * ∑' j, x j - ∑' j, g j : ℝ))) := by
    have := hsum.cexp
    refine this.congr_fun fun j => ?_
    have hL : (1 + ((g j : ℝ) : ℂ)) * Complex.exp (-((g j : ℝ) : ℂ)) =
        ((Real.exp ((1 / 2 : ℝ) * x j) * Real.exp (-g j) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_one,
        ← Complex.ofReal_add, ← Complex.ofReal_mul]
      congr 2
      simp only [g]
      ring
    have hR : (Complex.exp ∘ fun j => (((1 / 2 : ℝ) * x j - g j : ℝ) : ℂ)) j =
        ((Real.exp ((1 / 2 : ℝ) * x j) * Real.exp (-g j) : ℝ) : ℂ) := by
      simp only [Function.comp_apply]
      rw [← Complex.ofReal_exp, sub_eq_add_neg, Real.exp_add]
    rw [hL, hR]
  have hs2 : Summable fun j => ‖((g j : ℝ) : ℂ)‖ ^ (2 : ℕ) := by
    have hb : ∀ j, |g j| ≤ ∑' k, |g k| := fun j => hg.le_tsum j fun k _ => abs_nonneg _
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (hg.mul_left (∑' k, |g k|))
    rw [Complex.norm_real, Real.norm_eq_abs, sq]
    exact mul_le_mul_of_nonneg_right (hb j) (abs_nonneg _)
  have hdet2 := entireDet2_diagMul_neg_one hs2 hprod
  rw [RHTower.fredholmDetOp, RHTower.det2Op, coordMatrix_realSummableDiagonalOperator, hdet2,
    htr, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Theorem 6.1, `(RFT.29)`, under `(RFT.23)`**: a finite-work sequence is summable, so
`S_x - I` and `S_x⁻¹ - I` are trace class and `det(S_x) = exp(½ ∑ x_j)`. -/
theorem fredholmDet_recovery_of_threshold {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ a j)
    (hsum : Summable fun j => (a j ^ 2)⁻¹) {x : ℕ → ℝ} (hx : Summable (workTerm a x)) :
    ∃ (h : ∃ B, ∀ j, |((1 / 2 : ℝ) • x) j| ≤ B) (h' : ∃ B, ∀ j, |((-(1 / 2) : ℝ) • x) j| ≤ B),
      RHTower.MemSchattenClass 1 (expDiag ((1 / 2 : ℝ) • x) h - 1) ∧
        RHTower.MemSchattenClass 1 (expDiag ((-(1 / 2) : ℝ) • x) h' - 1) ∧
        RHTower.fredholmDetOp (lpBasis ℕ) (expDiag ((1 / 2 : ℝ) • x) h - 1) =
          Complex.exp ((1 / 2 : ℂ) * ((∑' j, x j : ℝ) : ℂ)) := by
  have hb := bounded_of_summable_workTerm ha hx
  exact ⟨bounded_smul hb _, bounded_smul hb _,
    fredholmDet_recovery (tail_bound ha hsum hx 0).1 _ _⟩

/-- **Theorem 6.1, determinant boundary**: `x = (t, -t, 0, …)`, `t ≠ 0`, has `∑ x_j = 0`, so
`det(S_x) = 1`, but positive work. -/
theorem determinant_neutral_not_work_neutral {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ a j) {t : ℝ}
    (ht : t ≠ 0) :
    let x : ℕ → ℝ := fun j => if j = 0 then t else if j = 1 then -t else 0
    (Summable fun j => |x j|) ∧ ∃ h : ∃ B, ∀ j, |((1 / 2 : ℝ) • x) j| ≤ B,
      RHTower.fredholmDetOp (lpBasis ℕ) (expDiag ((1 / 2 : ℝ) • x) h - 1) = 1 ∧
        Summable (workTerm a x) ∧ 0 < work a x := by
  intro x
  have hsupp : ∀ j ∉ ({0, 1} : Finset ℕ), x j = 0 := fun j hj => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [x, hj.1, hj.2]
  have hx : Summable fun j => |x j| :=
    summable_of_ne_finset_zero fun j hj => by rw [hsupp j hj, abs_zero]
  have hb : ∃ B, ∀ j, |((1 / 2 : ℝ) • x) j| ≤ B :=
    bounded_smul ⟨∑' j, |x j|, fun j => hx.le_tsum j fun k _ => abs_nonneg _⟩ _
  have hb' : ∃ B, ∀ j, |((-(1 / 2) : ℝ) • x) j| ≤ B :=
    bounded_smul ⟨∑' j, |x j|, fun j => hx.le_tsum j fun k _ => abs_nonneg _⟩ _
  have hsum : ∑' j, x j = 0 := by
    rw [tsum_eq_sum (s := {0, 1}) hsupp]
    simp [x]
  have hwsupp : ∀ j ∉ ({0, 1} : Finset ℕ), workTerm a x j = 0 := fun j hj => by
    simp [workTerm, hsupp j hj, reciprocalWork_zero]
  have hws : Summable (workTerm a x) := summable_of_ne_finset_zero hwsupp
  refine ⟨hx, hb, ?_, hws, ?_⟩
  · rw [(fredholmDet_recovery hx hb hb').2.2, hsum]
    simp
  · rw [work, tsum_eq_sum hwsupp]
    have h0 : 0 < workTerm a x 0 := by
      simp only [workTerm, x, if_pos rfl]
      have h1 : 0 < a 0 ^ 2 := by have := ha 0; positivity
      have h2 : 0 < reciprocalWork t := lt_of_le_of_ne (reciprocalWork_nonneg t)
        (fun h => ht ((reciprocalWork_eq_zero_iff t).1 h.symm))
      positivity
    have h1 := workTerm_nonneg a x 1
    simp only [Finset.sum_insert (by simp : (0 : ℕ) ∉ ({1} : Finset ℕ)), Finset.sum_singleton]
    linarith

end Determinant

end GaloisForLFunctions.HTGeometry.ReciprocalFusion
