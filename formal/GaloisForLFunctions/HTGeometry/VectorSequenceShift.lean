import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Shifts and weak nullness on vector-valued `ℓ²(ℕ; E)`

Reusable infrastructure for operator-weighted sequence operators on the Hilbert direct sum
`ℓ²(ℕ; E)` of a Hilbert space `E`:

* the backward shift `(B x)_n = x_{n+1}` and forward shift `(S x)_0 = 0`, `(S x)_{n+1} = x_n`,
  both of norm at most one, with `B^* = S` and `B S = 1`;
* coordinatewise-null bounded sequences are weakly null.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology
open scoped InnerProductSpace ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hilbert direct sum `ℓ²(ℕ; E)`. -/
abbrev VecSeq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :=
  lp (fun _ : ℕ => E) 2

theorem vecSeq_summable_sq (x : VecSeq E) : Summable fun n => ‖(x : ℕ → E) n‖ ^ 2 := by
  have := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using this

theorem vecSeq_norm_sq (x : VecSeq E) : ‖x‖ ^ 2 = ∑' n, ‖(x : ℕ → E) n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  simpa using this

omit [InnerProductSpace ℂ E] in
theorem memℓp_of_summable_sq {f : ℕ → E} (h : Summable fun n => ‖f n‖ ^ 2) : Memℓp f 2 :=
  memℓp_gen (by simpa using h)

theorem vecSeq_norm_le_of_tsum_le (x : VecSeq E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' n, ‖(x : ℕ → E) n‖ ^ 2 ≤ C ^ 2) : ‖x‖ ≤ C := by
  rw [← vecSeq_norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).mp h

/-! ## The backward shift -/

/-- The backward shift `(B x)_n = x_{n+1}` as a linear map. -/
def vecBackLinear : VecSeq E →ₗ[ℂ] VecSeq E where
  toFun x := ⟨fun n => (x : ℕ → E) (n + 1),
    memℓp_of_summable_sq ((summable_nat_add_iff 1).mpr (vecSeq_summable_sq x))⟩
  map_add' x y := by ext n; simp
  map_smul' c x := by ext n; simp

theorem norm_vecBackLinear_le (x : VecSeq E) : ‖vecBackLinear x‖ ≤ ‖x‖ := by
  apply vecSeq_norm_le_of_tsum_le _ (norm_nonneg _)
  rw [vecSeq_norm_sq]
  have hs := vecSeq_summable_sq x
  have h := hs.tsum_eq_zero_add
  change ∑' n, ‖(x : ℕ → E) (n + 1)‖ ^ 2 ≤ _
  rw [h]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The backward shift on `ℓ²(ℕ; E)`. -/
def vecBack : VecSeq E →L[ℂ] VecSeq E :=
  vecBackLinear.mkContinuous 1 fun x => by rw [one_mul]; exact norm_vecBackLinear_le x

@[simp] theorem vecBack_apply (x : VecSeq E) (n : ℕ) :
    (vecBack x : ℕ → E) n = (x : ℕ → E) (n + 1) := rfl

theorem norm_vecBack_le : ‖(vecBack : VecSeq E →L[ℂ] VecSeq E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## The forward shift -/

/-- Coordinates of the forward shift. -/
def vecForwardFun (x : ℕ → E) : ℕ → E := fun n => Nat.casesOn n 0 fun m => x m

omit [InnerProductSpace ℂ E] in
@[simp] theorem vecForwardFun_zero (x : ℕ → E) : vecForwardFun x 0 = 0 := rfl

omit [InnerProductSpace ℂ E] in
@[simp] theorem vecForwardFun_succ (x : ℕ → E) (n : ℕ) : vecForwardFun x (n + 1) = x n := rfl

theorem summable_vecForwardFun (x : VecSeq E) :
    Summable fun n => ‖vecForwardFun (x : ℕ → E) n‖ ^ 2 :=
  (summable_nat_add_iff 1).mp (by simpa using vecSeq_summable_sq x)

/-- The forward shift `(S x)_0 = 0`, `(S x)_{n+1} = x_n` as a linear map. -/
def vecForwardLinear : VecSeq E →ₗ[ℂ] VecSeq E where
  toFun x := ⟨vecForwardFun (x : ℕ → E), memℓp_of_summable_sq (summable_vecForwardFun x)⟩
  map_add' x y := by ext n; cases n <;> simp
  map_smul' c x := by ext n; cases n <;> simp

theorem norm_vecForwardLinear (x : VecSeq E) : ‖vecForwardLinear x‖ = ‖x‖ := by
  have h1 : ‖vecForwardLinear x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [vecSeq_norm_sq, vecSeq_norm_sq]
    change ∑' n, ‖vecForwardFun (x : ℕ → E) n‖ ^ 2 = _
    rw [(summable_vecForwardFun x).tsum_eq_zero_add]
    simp
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- The forward shift on `ℓ²(ℕ; E)` (an isometry). -/
def vecForward : VecSeq E →L[ℂ] VecSeq E :=
  vecForwardLinear.mkContinuous 1 fun x => by rw [one_mul, norm_vecForwardLinear]

@[simp] theorem vecForward_apply_zero (x : VecSeq E) : (vecForward x : ℕ → E) 0 = 0 := rfl

@[simp] theorem vecForward_apply_succ (x : VecSeq E) (n : ℕ) :
    (vecForward x : ℕ → E) (n + 1) = (x : ℕ → E) n := rfl

theorem norm_vecForward_apply (x : VecSeq E) : ‖vecForward x‖ = ‖x‖ := norm_vecForwardLinear x

theorem norm_vecForward_le : ‖(vecForward : VecSeq E →L[ℂ] VecSeq E)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem vecBack_comp_vecForward :
    (vecBack : VecSeq E →L[ℂ] VecSeq E) ∘L vecForward = ContinuousLinearMap.id ℂ _ := by
  ext x n; rfl

variable [CompleteSpace E]

/-- `B^* = S`. -/
theorem adjoint_vecBack :
    ContinuousLinearMap.adjoint (vecBack : VecSeq E →L[ℂ] VecSeq E) = vecForward := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hs : Summable fun n => ⟪(vecForward x : ℕ → E) n, (y : ℕ → E) n⟫_ℂ :=
    lp.summable_inner _ _
  rw [hs.tsum_eq_zero_add]
  simp

theorem adjoint_vecForward :
    ContinuousLinearMap.adjoint (vecForward : VecSeq E →L[ℂ] VecSeq E) = vecBack := by
  rw [← adjoint_vecBack, ContinuousLinearMap.adjoint_adjoint]

/-! ## Weak nullness from coordinates -/

omit [CompleteSpace E] in
/-- A bounded sequence in `ℓ²(ℕ; E)` whose coordinates all tend to zero is weakly null. -/
theorem tendsto_inner_vecSeq_of_coord (u : ℕ → VecSeq E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ N, ‖u N‖ ≤ C) (hcoord : ∀ n, Tendsto (fun N => (u N : ℕ → E) n) atTop (𝓝 0))
    (z : VecSeq E) : Tendsto (fun N => ⟪z, u N⟫_ℂ) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsum := lp.hasSum_single (E := fun _ : ℕ => E) (p := 2) (by norm_num) z
  have hδ : 0 < ε / (2 * (C + 1)) := by positivity
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp hsum (ε / (2 * (C + 1))) hδ).exists
  set zs := ∑ i ∈ s, lp.single 2 i ((z : ℕ → E) i)
  have hfin : Tendsto (fun N => ⟪zs, u N⟫_ℂ) atTop (𝓝 0) := by
    have : ∀ N, ⟪zs, u N⟫_ℂ = ∑ i ∈ s, ⟪(z : ℕ → E) i, (u N : ℕ → E) i⟫_ℂ := by
      intro N; rw [sum_inner]
      exact Finset.sum_congr rfl fun i _ => lp.inner_single_left _ _ _
    simp_rw [this]
    rw [show (0 : ℂ) = ∑ i ∈ s, (0 : ℂ) by simp]
    refine tendsto_finsetSum _ fun i _ => ?_
    have := ((innerSL ℂ ((z : ℕ → E) i)).continuous.tendsto (0 : E)).comp (hcoord i)
    rw [map_zero] at this
    exact this
  filter_upwards [Metric.tendsto_nhds.mp hfin (ε / 2) (by positivity)] with N hN
  rw [dist_zero_right] at hN ⊢
  have hsplit : ⟪z, u N⟫_ℂ = ⟪zs, u N⟫_ℂ + ⟪z - zs, u N⟫_ℂ := by
    rw [← inner_add_left, add_sub_cancel]
  have htail : ‖⟪z - zs, u N⟫_ℂ‖ ≤ ε / (2 * (C + 1)) * C := by
    calc ‖⟪z - zs, u N⟫_ℂ‖ ≤ ‖z - zs‖ * ‖u N‖ := norm_inner_le_norm _ _
      _ ≤ ε / (2 * (C + 1)) * C := by
          apply mul_le_mul _ (hb N) (norm_nonneg _) hδ.le
          rw [dist_comm, dist_eq_norm] at hs
          exact hs.le
  have hsmall : ε / (2 * (C + 1)) * C < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [hsplit]
  calc ‖⟪zs, u N⟫_ℂ + ⟪z - zs, u N⟫_ℂ‖ ≤ ‖⟪zs, u N⟫_ℂ‖ + ‖⟪z - zs, u N⟫_ℂ‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end

end GaloisForLFunctions.HTGeometry
