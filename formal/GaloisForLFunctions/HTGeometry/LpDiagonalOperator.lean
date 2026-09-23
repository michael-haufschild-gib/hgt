import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.FredholmDeterminantExamples

/-!
# Diagonal Hilbert--Schmidt operators on `ℓ²(ι)`

A square-summable weight family `w : ι → ℂ` defines a diagonal kernel, hence a
Hilbert--Schmidt operator on `ℓ²(ι)` acting coordinatewise by multiplication.
Composition of diagonals is pointwise multiplication of weights, so powers of a
diagonal are the diagonals of the pointwise powers, and the trace of a product of
two diagonals is the sum of the pointwise products of the weights.  The
Hilbert--Schmidt norm is the weight energy.

These are the computations that turn a diagonal operator into an explicit
Hilbert--Carleman exponent germ: every power trace is a weight sum.
-/

open ContinuousLinearMap
open scoped BigOperators

namespace HilbertSchmidt

variable {ι : Type*} [DecidableEq ι]

@[simp] theorem diagMul_diag (w : ι → ℂ) (i : ι) : diagMul w (i, i) = w i := by
  simp [diagMul]

theorem diagMul_of_ne {w : ι → ℂ} {i j : ι} (h : i ≠ j) : diagMul w (i, j) = 0 := by
  simp [diagMul, h]

omit [DecidableEq ι] in
theorem injective_diag : Function.Injective fun i : ι => (i, i) := by
  intro a b h
  exact congrArg Prod.fst h

theorem support_diagMul_normSq (w : ι → ℂ) :
    Function.support (fun p : ι × ι => ‖diagMul w p‖ ^ (2 : ℕ))
      ⊆ Set.range fun i : ι => (i, i) := by
  rintro ⟨a, b⟩ hp
  by_cases h : a = b
  · exact ⟨a, by rw [h]⟩
  · refine absurd ?_ hp
    show ‖diagMul w (a, b)‖ ^ (2 : ℕ) = 0
    rw [diagMul_of_ne h, norm_zero]
    norm_num

/-- Diagonal weight energy: the kernel energy of a diagonal kernel is the weight
energy. -/
theorem tsum_diagMul_normSq (w : ι → ℂ) :
    ∑' p : ι × ι, ‖diagMul w p‖ ^ (2 : ℕ) = ∑' i, ‖w i‖ ^ (2 : ℕ) := by
  rw [← injective_diag.tsum_eq (support_diagMul_normSq w)]
  refine tsum_congr fun i => ?_
  show ‖diagMul w (i, i)‖ ^ (2 : ℕ) = ‖w i‖ ^ (2 : ℕ)
  rw [diagMul_diag]

/-- A square-summable weight family gives a Hilbert--Schmidt kernel. -/
theorem isHS_diagMul_of_summable {w : ι → ℂ} (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ)) :
    IsHS (diagMul w) := by
  refine (Function.Injective.summable_iff (f := fun p : ι × ι => ‖diagMul w p‖ ^ (2 : ℕ))
    injective_diag ?_).mp ?_
  · rintro ⟨a, b⟩ hb
    by_cases h : a = b
    · exact absurd ⟨a, by rw [h]⟩ hb
    · show ‖diagMul w (a, b)‖ ^ (2 : ℕ) = 0
      rw [diagMul_of_ne h, norm_zero]
      norm_num
  · refine hw.congr fun i => ?_
    show ‖w i‖ ^ (2 : ℕ) = ‖diagMul w (i, i)‖ ^ (2 : ℕ)
    rw [diagMul_diag]

/-- The diagonal operator of a square-summable weight family. -/
noncomputable def diagOp (w : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ)) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  toOperator (isHS_diagMul_of_summable hw)

theorem diagOp_apply (w : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) : diagOp w hw f i = w i * f i := by
  rw [diagOp, toOperator_apply,
    tsum_eq_single i fun j hj => by rw [diagMul_of_ne (Ne.symm hj), zero_mul],
    diagMul_diag]

theorem diagOp_congr {w v : ι → ℂ} (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (hv : Summable fun i => ‖v i‖ ^ (2 : ℕ)) (h : w = v) : diagOp w hw = diagOp v hv := by
  subst h
  rfl

theorem isHilbertSchmidt_diagOp (w : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ)) :
    (diagOp w hw).IsHilbertSchmidt :=
  isHilbertSchmidt_toOperator _

/-- The Hilbert--Schmidt norm of a diagonal is the weight energy. -/
theorem hsNormSq_diagOp (w : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ)) :
    ContinuousLinearMap.hsNormSq (diagOp w hw) = ∑' i, ‖w i‖ ^ (2 : ℕ) := by
  rw [diagOp, hsNormSq_toOperator, hsNormSq, tsum_diagMul_normSq]

/-- Composition of diagonals is pointwise multiplication of weights. -/
theorem diagOp_comp (w v : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (hv : Summable fun i => ‖v i‖ ^ (2 : ℕ))
    (hwv : Summable fun i => ‖w i * v i‖ ^ (2 : ℕ)) :
    diagOp w hw ∘L diagOp v hv = diagOp (fun i => w i * v i) hwv := by
  ext f i
  rw [ContinuousLinearMap.comp_apply, diagOp_apply, diagOp_apply, diagOp_apply,
    mul_assoc]

/-- Differences of diagonals are diagonals. -/
theorem diagOp_sub (w v : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (hv : Summable fun i => ‖v i‖ ^ (2 : ℕ))
    (hwv : Summable fun i => ‖w i - v i‖ ^ (2 : ℕ)) :
    diagOp w hw - diagOp v hv = diagOp (fun i => w i - v i) hwv := by
  ext f i
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, diagOp_apply,
    diagOp_apply, diagOp_apply, sub_mul]

omit [DecidableEq ι] in
/-- Weights bounded by one keep every power square-summable. -/
theorem summable_pow_normSq {w : ι → ℂ} (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (hb : ∀ i, ‖w i‖ ≤ 1) (k : ℕ) :
    Summable fun i => ‖w i ^ (k + 1)‖ ^ (2 : ℕ) := by
  refine hw.of_nonneg_of_le (fun i => by positivity) fun i => ?_
  rw [norm_pow, ← pow_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) (hb i) (by omega)

/-- Powers of a diagonal are the diagonals of the pointwise powers. -/
theorem diagOp_pow (w : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (hb : ∀ i, ‖w i‖ ≤ 1) (k : ℕ) :
    (diagOp w hw) ^ (k + 1)
      = diagOp (fun i => w i ^ (k + 1)) (summable_pow_normSq hw hb k) := by
  induction k with
  | zero =>
      rw [pow_one]
      exact diagOp_congr hw _ (funext fun i => (pow_one (w i)).symm)
  | succ k ih =>
      have hmul : Summable fun i => ‖w i ^ (k + 1) * w i‖ ^ (2 : ℕ) := by
        refine (summable_pow_normSq hw hb (k + 1)).congr fun i => ?_
        rw [← pow_succ]
      calc (diagOp w hw) ^ (k + 2)
          = ((diagOp w hw) ^ (k + 1)) ∘L diagOp w hw := by
            rw [pow_succ, ContinuousLinearMap.mul_def]
        _ = diagOp (fun i => w i ^ (k + 1)) (summable_pow_normSq hw hb k)
              ∘L diagOp w hw := by rw [ih]
        _ = diagOp (fun i => w i ^ (k + 1) * w i) hmul :=
              diagOp_comp _ _ _ _ hmul
        _ = diagOp (fun i => w i ^ (k + 2)) (summable_pow_normSq hw hb (k + 1)) :=
              diagOp_congr _ _ (funext fun i => (pow_succ (w i) (k + 1)).symm)

/-- The trace of a product of two diagonals is the weight pairing. -/
theorem opTrace_diagOp_comp (w v : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (hv : Summable fun i => ‖v i‖ ^ (2 : ℕ)) :
    ContinuousLinearMap.opTrace (diagOp w hw ∘L diagOp v hv) = ∑' i, w i * v i := by
  rw [diagOp, diagOp, opTrace_toOperator_comp]
  refine tsum_congr fun i => ?_
  rw [show hsComp (diagMul w) (diagMul v) = diagMul fun i => w i * v i from
    hsComp_diagMul w v, diagMul_diag]

/-- **Power traces of a diagonal.**  Every power trace from degree two onward is
the sum of that power of the weights. -/
theorem opTrace_diagOp_pow (w : ι → ℂ) (hw : Summable fun i => ‖w i‖ ^ (2 : ℕ))
    (hb : ∀ i, ‖w i‖ ≤ 1) (n : ℕ) :
    ContinuousLinearMap.opTrace ((diagOp w hw) ^ (n + 2)) = ∑' i, w i ^ (n + 2) := by
  have hsplit : (diagOp w hw) ^ (n + 2)
      = diagOp (fun i => w i ^ (n + 1)) (summable_pow_normSq hw hb n) ∘L diagOp w hw := by
    rw [← diagOp_pow w hw hb n, pow_succ, ContinuousLinearMap.mul_def]
  rw [hsplit, opTrace_diagOp_comp]
  exact tsum_congr fun i => (pow_succ (w i) (n + 1)).symm

end HilbertSchmidt
