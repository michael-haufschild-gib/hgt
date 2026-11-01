import GaloisForLFunctions.HTGeometry.HilbertBlockOperator
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.RHTower.NuclearRankOneTrace
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Local `p`-adic Valuation-Shell Wiener–Hopf Operator and Logarithmic Trace Law

On the unramified `p`-adic valuation-shell Hilbert space `ℓ²(ℤ) = lp (fun _ : ℤ => ℂ) 2`, let `U`
be the unitary valuation shift `(U^k x)_n = x_{n - k}` and `P_{ℤ_p}` the orthogonal projection onto
nonnegative valuation shells `{n : ℤ | 0 ≤ n}`. For every prime `p` and `m : ℕ`, the Wiener–Hopf
valuation-shell defect

`K_p(m) := (log p) • (P_{ℤ_p} - U^m P_{ℤ_p} U^{-m}) = (log p) • ∑_{k = 0}^{m - 1} |e_k⟩⟨e_k|`

is self-adjoint, positive (`IsPositive`), Schatten-1 (`MemSchattenClass 1`), and trace-class
(`IsTraceClass`) of rank at most `m`, with exact logarithmic trace

`opTrace (K_p(m)) = m * log p`,   `(opTrace (K_p(m))).re = log (p ^ m)`.

Paired with the unsquared logarithmic Euler coefficient `c_p(m + 1) = p^{-(m + 1)/2} / (m + 1)`
(`soninSemilocalLogPrimePowerCoefficient`), this reproduces the exact von Mangoldt prime-power
flux `Λ(p^{m + 1}) / √(p^{m + 1})`, supplying the logarithmically growing local trace response
isolated by `SoninSemilocalTraceObstruction`.
-/

noncomputable section

open Complex Filter Topology BigOperators
open scoped ENNReal InnerProductSpace
open ContinuousLinearMap _root_.RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

/-- Unramified `p`-adic valuation-shell Hilbert space `ℓ²(ℤ)`. -/
abbrev ValuationShellL2 : Type := lp (fun _ : ℤ => ℂ) 2

/-- Standard orthonormal basis vector `e_n` supported on valuation shell `n ∈ ℤ`. -/
def valuationShellBasis (n : ℤ) : ValuationShellL2 :=
  lp.single 2 n (1 : ℂ)

@[simp] theorem valuationShellBasis_apply (n m : ℤ) :
    valuationShellBasis n m = if m = n then 1 else 0 := by
  unfold valuationShellBasis
  rw [lp.single_apply]
  by_cases h : m = n
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg h]

theorem inner_valuationShellBasis_left (n : ℤ) (x : ValuationShellL2) :
    ⟪valuationShellBasis n, x⟫_ℂ = x n := by
  rw [lp.inner_eq_tsum, tsum_eq_single n]
  · simp [valuationShellBasis_apply]
  · intro m hm
    simp [valuationShellBasis_apply, hm]

theorem inner_valuationShellBasis_self (n : ℤ) :
    ⟪valuationShellBasis n, valuationShellBasis n⟫_ℂ = 1 := by
  rw [inner_valuationShellBasis_left, valuationShellBasis_apply, if_pos rfl]

/-- Coordinate shift `n ↦ x (n - k)` preserves `ℓ²(ℤ)`. -/
theorem valuationShift_memℓp (k : ℤ) (x : ValuationShellL2) :
    Memℓp (fun n : ℤ => x (n - k)) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable (fun n : ℤ => ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ)) :=
    (lp.memℓp x).summable (by norm_num)
  exact (Equiv.subRight k).summable_iff.mpr hsum

/-- Linear valuation shift `(U^k x)_n = x_{n - k}` on `ℓ²(ℤ)`. -/
def valuationShiftLinear (k : ℤ) : ValuationShellL2 →ₗ[ℂ] ValuationShellL2 where
  toFun x := ⟨fun n => x (n - k), valuationShift_memℓp k x⟩
  map_add' x y := by ext n; simp
  map_smul' c x := by ext n; simp

@[simp] theorem valuationShiftLinear_apply (k : ℤ) (x : ValuationShellL2) (n : ℤ) :
    valuationShiftLinear k x n = x (n - k) := rfl

theorem norm_valuationShiftLinear (k : ℤ) (x : ValuationShellL2) :
    ‖valuationShiftLinear k x‖ = ‖x‖ := by
  have hleft : 0 ≤ ‖valuationShiftLinear k x‖ := norm_nonneg _
  have hright : 0 ≤ ‖x‖ := norm_nonneg _
  have h1 : ‖valuationShiftLinear k x‖ ^ (2 : ℝ) =
      ∑' n : ℤ, ‖(valuationShiftLinear k x : ℤ → ℂ) n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num)
      (valuationShiftLinear k x)
  have h2 : ‖x‖ ^ (2 : ℝ) = ∑' n : ℤ, ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num) x
  have heq : ∑' n : ℤ, ‖(valuationShiftLinear k x : ℤ → ℂ) n‖ ^ (2 : ℝ) =
      ∑' n : ℤ, ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) :=
    (Equiv.subRight k).tsum_eq (fun n : ℤ => ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ))
  have hrpow : ‖valuationShiftLinear k x‖ ^ (2 : ℝ) = ‖x‖ ^ (2 : ℝ) := by
    rw [h1, heq, ← h2]
  have hleft2 : ‖valuationShiftLinear k x‖ ^ (2 : ℝ) =
      ‖valuationShiftLinear k x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : ‖x‖ ^ (2 : ℝ) = ‖x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hrpow
  have hsqrt := congrArg Real.sqrt hrpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- Bounded unitary valuation shift `(U^k x)_n = x_{n - k}` on `ℓ²(ℤ)`. -/
def valuationShiftCLM (k : ℤ) : ValuationShellL2 →L[ℂ] ValuationShellL2 :=
  LinearMap.mkContinuous (valuationShiftLinear k) 1 fun x => by
    rw [norm_valuationShiftLinear, one_mul]

@[simp] theorem valuationShiftCLM_apply (k : ℤ) (x : ValuationShellL2) (n : ℤ) :
    valuationShiftCLM k x n = x (n - k) := rfl

theorem valuationShiftCLM_zero :
    valuationShiftCLM 0 = ContinuousLinearMap.id ℂ ValuationShellL2 := by
  ext x n
  simp

theorem valuationShiftCLM_comp (j k : ℤ) :
    valuationShiftCLM j ∘L valuationShiftCLM k = valuationShiftCLM (j + k) := by
  ext x n
  simp [sub_sub]

theorem inner_valuationShiftCLM (k : ℤ) (x y : ValuationShellL2) :
    ⟪valuationShiftCLM k x, y⟫_ℂ = ⟪x, valuationShiftCLM (-k) y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simpa [sub_neg_eq_add] using
    (Equiv.subRight k).tsum_eq (fun m : ℤ => ⟪(x : ℤ → ℂ) m, (y : ℤ → ℂ) (m + k)⟫_ℂ)

theorem adjoint_valuationShiftCLM (k : ℤ) :
    ContinuousLinearMap.adjoint (valuationShiftCLM k) = valuationShiftCLM (-k) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, inner_valuationShiftCLM]

/-- Orthogonal projection `P_{ℤ_p}` onto the integral valuation shells `{n : ℤ | 0 ≤ n}`. -/
def integralValuationProj : ValuationShellL2 →L[ℂ] ValuationShellL2 :=
  blockOperator (fun n : ℤ => if 0 ≤ n then ContinuousLinearMap.id ℂ ℂ else 0) zero_le_one
    fun n => by
      split_ifs
      · exact ContinuousLinearMap.norm_id_le
      · simp

@[simp] theorem integralValuationProj_apply (x : ValuationShellL2) (n : ℤ) :
    integralValuationProj x n = if 0 ≤ n then x n else 0 := by
  unfold integralValuationProj
  rw [blockOperator_apply]
  split_ifs <;> simp

theorem integralValuationProj_idem :
    integralValuationProj ∘L integralValuationProj = integralValuationProj := by
  ext x n
  simp only [comp_apply, integralValuationProj_apply]
  split_ifs <;> rfl

theorem integralValuationProj_isSelfAdjoint : IsSelfAdjoint integralValuationProj := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  change ⟪integralValuationProj x n, y n⟫_ℂ = ⟪x n, integralValuationProj y n⟫_ℂ
  rw [integralValuationProj_apply, integralValuationProj_apply]
  split_ifs
  · rfl
  · simp only [inner_zero_left, inner_zero_right]

/-- Wiener–Hopf valuation-shell defect `P_{ℤ_p} - U^m P_{ℤ_p} U^{-m}` for `m : ℕ`. -/
def valuationShellDefect (m : ℕ) : ValuationShellL2 →L[ℂ] ValuationShellL2 :=
  integralValuationProj -
    valuationShiftCLM (m : ℤ) ∘L integralValuationProj ∘L valuationShiftCLM (-(m : ℤ))

@[simp] theorem valuationShellDefect_apply (m : ℕ) (x : ValuationShellL2) (n : ℤ) :
    valuationShellDefect m x n = if 0 ≤ n ∧ n < (m : ℤ) then x n else 0 := by
  change integralValuationProj x n -
      valuationShiftCLM (m : ℤ) (integralValuationProj (valuationShiftCLM (-(m : ℤ)) x)) n = _
  rw [integralValuationProj_apply, valuationShiftCLM_apply, integralValuationProj_apply,
    valuationShiftCLM_apply]
  have hcancel : n - (m : ℤ) - -(m : ℤ) = n := by omega
  rw [hcancel]
  by_cases h0 : 0 ≤ n
  · by_cases hm : n < (m : ℤ)
    · have hnm : ¬ 0 ≤ n - (m : ℤ) := by omega
      rw [if_pos h0, if_neg hnm, if_pos ⟨h0, hm⟩, sub_zero]
    · have hnm : 0 ≤ n - (m : ℤ) := by omega
      rw [if_pos h0, if_pos hnm, if_neg (fun h => hm h.2), sub_self]
  · have hnm : ¬ 0 ≤ n - (m : ℤ) := by omega
    rw [if_neg h0, if_neg hnm, if_neg (fun h => h0 h.1), sub_zero]

/-- Exact finite rank-one basis expansion of the valuation-shell Wiener–Hopf defect. -/
theorem valuationShellDefect_eq_sum_rankOne (m : ℕ) :
    valuationShellDefect m =
      ∑ k ∈ Finset.range m,
        InnerProductSpace.rankOne ℂ (valuationShellBasis (k : ℤ)) (valuationShellBasis (k : ℤ)) := by
  ext x n
  rw [valuationShellDefect_apply, sum_apply, lp.coeFn_sum]
  simp only [Finset.sum_apply, InnerProductSpace.rankOne_apply, inner_valuationShellBasis_left,
    lp.coeFn_smul, Pi.smul_apply, valuationShellBasis_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  by_cases hn : 0 ≤ n ∧ n < (m : ℤ)
  · rw [if_pos hn]
    lift n to ℕ using hn.1
    have hmem : n ∈ Finset.range m := Finset.mem_range.mpr (by exact_mod_cast hn.2)
    rw [Finset.sum_eq_single n]
    · simp
    · intro k _ hkn
      have hne : (n : ℤ) ≠ (k : ℤ) := fun h => hkn (Int.ofNat.inj h.symm)
      rw [if_neg hne]
    · intro hnot
      exact absurd hmem hnot
  · rw [if_neg hn]
    symm
    refine Finset.sum_eq_zero fun k hk => ?_
    have hklt : (k : ℤ) < (m : ℤ) := by exact_mod_cast Finset.mem_range.mp hk
    have hne : n ≠ (k : ℤ) := by
      intro h
      subst h
      exact hn ⟨Int.natCast_nonneg k, hklt⟩
    rw [if_neg hne]

theorem rankOne_self_isSelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : H) :
    IsSelfAdjoint (InnerProductSpace.rankOne ℂ v v) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', InnerProductSpace.adjoint_rankOne]

theorem rankOne_self_isPositive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : H) :
    ContinuousLinearMap.IsPositive (InnerProductSpace.rankOne ℂ v v) := by
  refine ⟨(rankOne_self_isSelfAdjoint v).isSymmetric, fun x => ?_⟩
  rw [reApplyInnerSelf, InnerProductSpace.rankOne_apply, inner_smul_left]
  set z : ℂ := ⟪v, x⟫_ℂ
  change 0 ≤ (starRingEnd ℂ z * z).re
  have hz : starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [hz, Complex.ofReal_re]
  exact sq_nonneg ‖z‖

theorem valuationShellDefect_isSelfAdjoint (m : ℕ) :
    IsSelfAdjoint (valuationShellDefect m) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', valuationShellDefect_eq_sum_rankOne]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ContinuousLinearMap.adjoint.map_add, ih,
        InnerProductSpace.adjoint_rankOne]

theorem valuationShellDefect_isPositive (m : ℕ) :
    ContinuousLinearMap.IsPositive (valuationShellDefect m) := by
  rw [valuationShellDefect_eq_sum_rankOne]
  induction m with
  | zero => exact ContinuousLinearMap.isPositive_zero
  | succ m ih =>
      rw [Finset.sum_range_succ]
      exact ih.add (rankOne_self_isPositive _)

theorem valuationShellDefect_hasRankLE (m : ℕ) :
    HasRankLE (valuationShellDefect m) m := by
  rw [valuationShellDefect_eq_sum_rankOne]
  exact hasRankLE_sum_range_rankOne (fun k => valuationShellBasis (k : ℤ))
    (fun k => valuationShellBasis (k : ℤ)) m

theorem valuationShellDefect_memSchattenClass_one (m : ℕ) :
    MemSchattenClass 1 (valuationShellDefect m) :=
  memSchattenClass_of_hasRankLE one_pos (valuationShellDefect_hasRankLE m)

theorem valuationShellDefect_isTraceClass (m : ℕ) :
    ContinuousLinearMap.IsTraceClass (valuationShellDefect m) :=
  (valuationShellDefect_memSchattenClass_one m).one_isTraceClass

theorem opTrace_valuationShellDefect (m : ℕ) :
    opTrace (valuationShellDefect m) = (m : ℂ) := by
  induction m with
  | zero =>
      have h0 : valuationShellDefect 0 = 0 := by
        rw [valuationShellDefect_eq_sum_rankOne, Finset.range_zero, Finset.sum_empty]
      rw [h0, RHTower.opTrace_zero, Nat.cast_zero]
  | succ m ih =>
      have hsucc : valuationShellDefect (m + 1) =
          valuationShellDefect m +
            InnerProductSpace.rankOne ℂ (valuationShellBasis (m : ℤ))
              (valuationShellBasis (m : ℤ)) := by
        rw [valuationShellDefect_eq_sum_rankOne, Finset.sum_range_succ,
          ← valuationShellDefect_eq_sum_rankOne]
      have hrank1 : HasRankLE
          (InnerProductSpace.rankOne ℂ (valuationShellBasis (m : ℤ))
            (valuationShellBasis (m : ℤ))) 1 := by
        simpa using hasRankLE_sum_range_rankOne (fun _ => valuationShellBasis (m : ℤ))
          (fun _ => valuationShellBasis (m : ℤ)) 1
      rw [hsucc, opTrace_add_of_memSchattenClass_one (valuationShellDefect_memSchattenClass_one m)
        (memSchattenClass_of_hasRankLE one_pos hrank1), ih, opTrace_rankOne,
        inner_valuationShellBasis_self, Nat.cast_add, Nat.cast_one]

/-- Local `p`-adic logarithmic shell operator `K_p(m) = (log p) • (P_{ℤ_p} - U^m P_{ℤ_p} U^{-m})`. -/
def primeValuationLogOperator (p m : ℕ) : ValuationShellL2 →L[ℂ] ValuationShellL2 :=
  (Real.log p : ℂ) • valuationShellDefect m

/-- The distinguished local `2`-adic operator `K_2(m)` of Candidate A / Question Q6. -/
abbrev primeTwoLogOperator (m : ℕ) : ValuationShellL2 →L[ℂ] ValuationShellL2 :=
  primeValuationLogOperator 2 m

theorem primeValuationLogOperator_isSelfAdjoint (p m : ℕ) :
    IsSelfAdjoint (primeValuationLogOperator p m) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', primeValuationLogOperator,
    ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp (valuationShellDefect_isSelfAdjoint m),
    Complex.conj_ofReal]

theorem primeValuationLogOperator_isPositive {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    ContinuousLinearMap.IsPositive (primeValuationLogOperator p m) := by
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  have hpos := valuationShellDefect_isPositive m
  refine ⟨(primeValuationLogOperator_isSelfAdjoint p m).isSymmetric, fun x => ?_⟩
  rw [reApplyInnerSelf, primeValuationLogOperator, smul_apply, inner_smul_left,
    Complex.conj_ofReal]
  change 0 ≤ ((Real.log p : ℂ) * ⟪valuationShellDefect m x, x⟫_ℂ).re
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg hlog (hpos.2 x)

theorem primeTwoLogOperator_isPositive (m : ℕ) :
    ContinuousLinearMap.IsPositive (primeTwoLogOperator m) :=
  primeValuationLogOperator_isPositive (by norm_num) m

theorem primeValuationLogOperator_hasRankLE (p m : ℕ) :
    HasRankLE (primeValuationLogOperator p m) m := by
  obtain ⟨V, hVfd, hVdim, hVmem⟩ := valuationShellDefect_hasRankLE m
  refine ⟨V, hVfd, hVdim, fun x => ?_⟩
  rw [primeValuationLogOperator, smul_apply]
  exact V.smul_mem _ (hVmem x)

theorem primeValuationLogOperator_memSchattenClass_one (p m : ℕ) :
    MemSchattenClass 1 (primeValuationLogOperator p m) :=
  memSchattenClass_of_hasRankLE one_pos (primeValuationLogOperator_hasRankLE p m)

theorem primeValuationLogOperator_isTraceClass (p m : ℕ) :
    ContinuousLinearMap.IsTraceClass (primeValuationLogOperator p m) :=
  (primeValuationLogOperator_memSchattenClass_one p m).one_isTraceClass

theorem primeTwoLogOperator_isTraceClass (m : ℕ) :
    ContinuousLinearMap.IsTraceClass (primeTwoLogOperator m) :=
  primeValuationLogOperator_isTraceClass 2 m

/-- **Exact logarithmic trace growth law.** For every `p` and `m`, `opTrace(K_p(m)) = m log p`. -/
theorem opTrace_primeValuationLogOperator (p m : ℕ) :
    opTrace (primeValuationLogOperator p m) = (m : ℂ) * (Real.log p : ℂ) := by
  rw [primeValuationLogOperator, RHTower.opTrace_smul, opTrace_valuationShellDefect, mul_comm]

theorem opTrace_primeValuationLogOperator_re (p m : ℕ) :
    (opTrace (primeValuationLogOperator p m)).re = Real.log ((p : ℝ) ^ m) := by
  rw [opTrace_primeValuationLogOperator, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    Complex.ofReal_re, Real.log_pow]

/-- **Exact `2`-adic logarithmic trace law:** `opTrace(K_2(m)) = m log 2 = log(2^m)`. -/
theorem opTrace_primeTwoLogOperator (m : ℕ) :
    opTrace (primeTwoLogOperator m) = (m : ℂ) * (Real.log 2 : ℂ) :=
  opTrace_primeValuationLogOperator 2 m

theorem opTrace_primeTwoLogOperator_re (m : ℕ) :
    (opTrace (primeTwoLogOperator m)).re = Real.log ((2 : ℝ) ^ m) :=
  opTrace_primeValuationLogOperator_re 2 m

/-- **Exact compatibility with `SoninSemilocalRelativeTrace`:** the trace of `K_p(k + 1)` equals
the static logarithmic scale length `soninSemilocalLogScaleLength pk`, so multiplying by the
unsquared Euler coefficient produces the exact von Mangoldt prime-power flux. -/
theorem opTrace_primeValuationLogOperator_eq_soninLogScaleLength (pk : Nat.Primes × ℕ) :
    opTrace (primeValuationLogOperator pk.1.1 (pk.2 + 1)) =
      soninSemilocalLogScaleLength pk := by
  rw [opTrace_primeValuationLogOperator, soninSemilocalLogScaleLength]
  push_cast
  ring

private theorem real_sqrt_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Real.sqrt_mul hx, ih]

theorem soninEulerCoeff_mul_opTrace_primeValuationLogOperator (pk : Nat.Primes × ℕ) :
    soninSemilocalLogPrimePowerCoefficient pk *
        opTrace (primeValuationLogOperator pk.1.1 (pk.2 + 1)) =
      (((ArithmeticFunction.vonMangoldt (pk.1.1 ^ (pk.2 + 1)) : ℝ) /
        Real.sqrt ((pk.1.1 ^ (pk.2 + 1) : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hp : pk.1.1.Prime := pk.1.2
  have hppos : (0 : ℝ) ≤ (pk.1.1 : ℝ) := Nat.cast_nonneg _
  have hvm : ArithmeticFunction.vonMangoldt (pk.1.1 ^ (pk.2 + 1)) = Real.log (pk.1.1 : ℝ) :=
    (ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero pk.2)).trans
      (ArithmeticFunction.vonMangoldt_apply_prime hp)
  have hflx : soninSemilocalPrimeFluxCoefficient pk =
      (((Real.sqrt (pk.1.1 : ℝ))⁻¹ ^ (pk.2 + 1) * Real.log (pk.1.1 : ℝ) : ℝ) : ℂ) :=
    soninSemilocalPrimeFluxCoefficient_eq pk
  rw [opTrace_primeValuationLogOperator_eq_soninLogScaleLength,
    ← soninSemilocalPrimeFluxCoefficient, hflx, hvm, Nat.cast_pow, real_sqrt_pow hppos (pk.2 + 1)]
  congr 1
  rw [inv_pow, div_eq_mul_inv, mul_comm]

/-- The prime `2` bundled as `Nat.Primes`. -/
def twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- Specialized Euler-to-von-Mangoldt trace identity at the prime `2`. -/
theorem soninEulerCoeff_mul_opTrace_primeTwoLogOperator (k : ℕ) :
    soninSemilocalLogPrimePowerCoefficient (twoPrime, k) *
        opTrace (primeTwoLogOperator (k + 1)) =
      (((ArithmeticFunction.vonMangoldt (2 ^ (k + 1)) : ℝ) /
        Real.sqrt ((2 ^ (k + 1) : ℕ) : ℝ) : ℝ) : ℂ) :=
  soninEulerCoeff_mul_opTrace_primeValuationLogOperator (twoPrime, k)

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

end
