import GaloisForLFunctions.RHTower.SuzukiLatticePolynomialGroupEstimate
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The weighted evolution group on all of `ℓ²`

The polynomial group estimate is first proved for finitely supported fields, where every coordinate
moment is manifestly square summable.  Truncation upgrades it to arbitrary fields: the truncations
of a field converge to it, the evolution is continuous, and evaluation at a label is continuous, so
each finite partial sum of the weighted evolution is a limit of finite partial sums obeying the
bound.

Duality then reverses the direction of the conjugation.  Pairing the reciprocal weight against the
weighted estimate for the reversed time exhibits `⟨X⟩^{-m} e^{-ixA} ⟨X⟩^{m}` as a bounded operator
with the same polynomial bound, and since the reciprocal weight has dense range this operator is the
continuous extension of the conjugated evolution.
-/

open Finset
open scoped ENNReal

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

/-! ## Square-summability by finite partial sums -/

theorem rpow_two_toReal (z : ℝ) : z ^ ((2 : ℝ≥0∞).toReal) = z ^ 2 := by norm_num

omit [Fintype P] [DecidableEq P] in
/-- A finite partial sum of squared coordinates never exceeds the squared norm. -/
theorem sum_sq_le_norm_sq (f : H) (T : Finset (P → ℤ)) :
    ∑ r ∈ T, ‖((f : H) : (P → ℤ) → ℂ) r‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (E := fun _ : (P → ℤ) => ℂ) (p := 2)
    (by norm_num) f T
  simpa only [rpow_two_toReal] using h

omit [Fintype P] [DecidableEq P] in
/-- A field with uniformly bounded finite partial sums of squares lies in `ℓ²`. -/
theorem memℓp_of_forall_finset_sum_sq_le {g : (P → ℤ) → ℂ} {K : ℝ}
    (h : ∀ T : Finset (P → ℤ), ∑ r ∈ T, ‖g r‖ ^ 2 ≤ K) : Memℓp g 2 := by
  refine memℓp_gen ?_
  simp only [rpow_two_toReal]
  exact summable_of_sum_le (c := K) (fun r => by positivity) h

omit [Fintype P] [DecidableEq P] in
/-- The `ℓ²` norm is determined by the finite partial sums of squares. -/
theorem norm_le_of_forall_finset_sum_sq_le {f : H} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ T : Finset (P → ℤ), ∑ r ∈ T, ‖((f : H) : (P → ℤ) → ℂ) r‖ ^ 2 ≤ K ^ 2) :
    ‖f‖ ≤ K := by
  refine lp.norm_le_of_forall_sum_le (E := fun _ : (P → ℤ) => ℂ) (p := 2) (by norm_num) hK ?_
  intro T
  simpa only [rpow_two_toReal] using h T

/-! ## Truncation to finitely many labels -/

omit [Fintype P] [DecidableEq P] in
/-- The truncation of a field to a finite set of labels. -/
def truncField (S : Finset (P → ℤ)) (f : (P → ℤ) → ℂ) : (P → ℤ) → ℂ :=
  Set.indicator (↑S : Set (P → ℤ)) f

omit [Fintype P] [DecidableEq P] in
theorem support_truncField_finite (S : Finset (P → ℤ)) (f : (P → ℤ) → ℂ) :
    (Function.support (truncField S f)).Finite :=
  Set.Finite.subset S.finite_toSet Set.support_indicator_subset

omit [Fintype P] [DecidableEq P] in
theorem norm_truncField_le (S : Finset (P → ℤ)) (f : (P → ℤ) → ℂ) (r : P → ℤ) :
    ‖truncField S f r‖ ≤ ‖f r‖ := by
  by_cases hr : r ∈ (↑S : Set (P → ℤ))
  · rw [truncField, Set.indicator_of_mem hr]
  · rw [truncField, Set.indicator_of_notMem hr, norm_zero]
    exact norm_nonneg _

omit [Fintype P] [DecidableEq P] in
/-- The truncation of an `ℓ²` field, as an `ℓ²` field. -/
def truncL2 (S : Finset (P → ℤ)) (v : H) : H :=
  l2OfFinSupp (truncField S ((v : H) : (P → ℤ) → ℂ)) (support_truncField_finite S _)

omit [Fintype P] [DecidableEq P] in
@[simp]
theorem coe_truncL2 (S : Finset (P → ℤ)) (v : H) :
    ((truncL2 S v : H) : (P → ℤ) → ℂ) = truncField S ((v : H) : (P → ℤ) → ℂ) := rfl

omit [DecidableEq P] in
/-- **Truncations converge.**  Every `ℓ²` field is the limit of its finite truncations. -/
theorem tendsto_truncL2 (v : H) :
    Filter.Tendsto (fun S : Finset (P → ℤ) => (truncL2 S v : H)) Filter.atTop (nhds v) := by
  have h := lp.hasSum_single (E := fun _ : (P → ℤ) => ℂ) (p := 2) (by norm_num) v
  rw [HasSum, SummationFilter.unconditional_filter] at h
  refine Filter.Tendsto.congr (fun S => ?_) h
  refine lp.ext ?_
  funext r
  rw [lp.coeFn_sum, Finset.sum_apply, coe_truncL2]
  simp only [lp.single_apply, Pi.single_apply, Finset.sum_ite_eq, truncField]
  by_cases hr : r ∈ S
  · rw [if_pos hr, Set.indicator_of_mem (by simpa using hr)]
  · rw [if_neg hr, Set.indicator_of_notMem (by simpa using hr)]

/-! ## The reciprocal shell weight -/

/-- Multiplication by the reciprocal shell weight. -/
def invShellField (m : ℕ) (ψ : (P → ℤ) → ℂ) : (P → ℤ) → ℂ :=
  fun r => ((shellWeight m r : ℝ) : ℂ)⁻¹ * ψ r

omit [DecidableEq P] in
theorem ofReal_shellWeight_ne_zero (m : ℕ) (r : P → ℤ) :
    ((shellWeight m r : ℝ) : ℂ) ≠ 0 := by
  simpa using (shellWeight_pos m r).ne'

omit [DecidableEq P] in
/-- The reciprocal shell weight is a contraction. -/
theorem norm_invShellField_le (m : ℕ) (ψ : (P → ℤ) → ℂ) (r : P → ℤ) :
    ‖invShellField m ψ r‖ ≤ ‖ψ r‖ := by
  simp only [invShellField, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (shellWeight_pos m r).le]
  have hs : 0 < shellWeight m r := shellWeight_pos m r
  have hone : (shellWeight m r)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hs]
    exact one_le_shellWeight m r
  nlinarith [norm_nonneg (ψ r)]

omit [DecidableEq P] in
/-- The shell weight undoes the reciprocal shell weight. -/
theorem shellWeightField_invShellField (m : ℕ) (ψ : (P → ℤ) → ℂ) :
    shellWeightField m (invShellField m ψ) = ψ := by
  funext r
  simp only [shellWeightField, invShellField, ← mul_assoc,
    mul_inv_cancel₀ (ofReal_shellWeight_ne_zero (P := P) m r), one_mul]

omit [DecidableEq P] in
/-- The reciprocal shell weight undoes the shell weight. -/
theorem invShellField_shellWeightField (m : ℕ) (ψ : (P → ℤ) → ℂ) :
    invShellField m (shellWeightField m ψ) = ψ := by
  funext r
  simp only [shellWeightField, invShellField, ← mul_assoc,
    inv_mul_cancel₀ (ofReal_shellWeight_ne_zero (P := P) m r), one_mul]

omit [DecidableEq P] in
/-- The reciprocal shell weight of an `ℓ²` field. -/
def invShellL2 (m : ℕ) (ψ : H) : H :=
  ⟨invShellField m ((ψ : H) : (P → ℤ) → ℂ),
    memℓp_of_norm_le (u := ψ) fun r => norm_invShellField_le m _ r⟩

omit [DecidableEq P] in
@[simp]
theorem coe_invShellL2 (m : ℕ) (ψ : H) :
    ((invShellL2 m ψ : H) : (P → ℤ) → ℂ) = invShellField m ((ψ : H) : (P → ℤ) → ℂ) := rfl

omit [DecidableEq P] in
/-- **The reciprocal shell weight as a diagonal operator.** -/
def invShellLM (m : ℕ) : H →ₗ[ℂ] H where
  toFun := invShellL2 m
  map_add' a b := by
    refine lp.ext ?_
    funext r
    simp only [coe_invShellL2, invShellField, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' a b := by
    refine lp.ext ?_
    funext r
    simp only [coe_invShellL2, invShellField, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

omit [DecidableEq P] in
@[simp]
theorem coe_invShellLM (m : ℕ) (ψ : H) :
    ((invShellLM m ψ : H) : (P → ℤ) → ℂ) = invShellField m ((ψ : H) : (P → ℤ) → ℂ) := rfl

omit [DecidableEq P] in
/-- **The reciprocal shell weight has dense range.**  Its range contains every finitely supported
field, and those are dense. -/
theorem denseRange_invShellLM (m : ℕ) :
    DenseRange (invShellLM (P := P) m : H → H) := by
  intro v
  refine mem_closure_of_tendsto (tendsto_truncL2 v) (Filter.Eventually.of_forall fun S => ?_)
  refine ⟨l2OfFinSupp (shellWeightField m (truncField S ((v : H) : (P → ℤ) → ℂ)))
    ((support_truncField_finite S _).subset (support_shellWeightField_subset m _)), ?_⟩
  refine lp.ext ?_
  rw [coe_invShellLM, coe_l2OfFinSupp, coe_truncL2, invShellField_shellWeightField]

/-! ## The polynomial estimate on all of `ℓ²` -/

set_option maxHeartbeats 1000000 in
omit [DecidableEq P] in
/-- **The polynomial group estimate on all of `ℓ²`.**  If the shell-weighted field of `v` is square
summable, then so is the shell-weighted field of its evolution, with the polynomial bound. -/
theorem exists_shellWeighted_exp {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (v u : H),
      ((u : H) : (P → ℤ) → ℂ) = shellWeightField m ((v : H) : (P → ℤ) → ℂ) →
      ∃ w : H, ((w : H) : (P → ℤ) → ℂ)
          = shellWeightField m
              ((NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) v : H)
                : (P → ℤ) → ℂ)
        ∧ ‖w‖ ≤ C * (1 + |x|) ^ m * ‖u‖ := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_norm_shellWeighted_exp_le hsa m
  refine ⟨C, hC, fun x v u hu => ?_⟩
  set E : H →L[ℂ] H := NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) with hEdef
  set K : ℝ := C * (1 + |x|) ^ m * ‖u‖ with hKdef
  have hK0 : 0 ≤ K := by
    refine mul_nonneg (mul_nonneg hC ?_) (norm_nonneg u)
    positivity
  have hev : ∀ r : P → ℤ, Filter.Tendsto
      (fun S : Finset (P → ℤ) => ((E (truncL2 S v) : H) : (P → ℤ) → ℂ) r)
      Filter.atTop (nhds (((E v : H) : (P → ℤ) → ℂ) r)) := by
    intro r
    have hE : Filter.Tendsto (fun S : Finset (P → ℤ) => (E (truncL2 S v) : H))
        Filter.atTop (nhds (E v)) :=
      (E.continuous.tendsto v).comp (tendsto_truncL2 v)
    exact ((lp.lipschitzWith_one_eval (E := fun _ : (P → ℤ) => ℂ) 2 r).continuous.tendsto
      (E v)).comp hE
  have hkey : ∀ T : Finset (P → ℤ),
      ∑ r ∈ T, ‖shellWeightField m ((E v : H) : (P → ℤ) → ℂ) r‖ ^ 2 ≤ K ^ 2 := by
    intro T
    have hlim : Filter.Tendsto
        (fun S : Finset (P → ℤ) =>
          ∑ r ∈ T, ‖shellWeightField m ((E (truncL2 S v) : H) : (P → ℤ) → ℂ) r‖ ^ 2)
        Filter.atTop
        (nhds (∑ r ∈ T, ‖shellWeightField m ((E v : H) : (P → ℤ) → ℂ) r‖ ^ 2)) := by
      simp only [shellWeightField]
      refine tendsto_finsetSum T fun r _ => ?_
      have hc : Continuous fun z : ℂ => ‖((shellWeight m r : ℝ) : ℂ) * z‖ ^ 2 := by fun_prop
      exact (hc.tendsto _).comp (hev r)
    refine le_of_tendsto hlim (Filter.Eventually.of_forall fun S => ?_)
    obtain ⟨wS, hwS, hwSn⟩ := hb x (truncField S ((v : H) : (P → ℤ) → ℂ))
      (support_truncField_finite S _)
    have hsub : ‖(l2OfFinSupp (shellWeightField m (truncField S ((v : H) : (P → ℤ) → ℂ)))
        ((support_truncField_finite S _).subset
          (support_shellWeightField_subset m _)) : H)‖ ≤ ‖u‖ := by
      refine lp.norm_mono (by norm_num) fun r => ?_
      rw [coe_l2OfFinSupp, hu]
      simp only [shellWeightField, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_truncField_le S _ r) (norm_nonneg _)
    have hwSK : ‖wS‖ ≤ K := by
      refine le_trans hwSn ?_
      rw [hKdef]
      refine mul_le_mul_of_nonneg_left hsub ?_
      exact mul_nonneg hC (by positivity)
    have hsum := sum_sq_le_norm_sq wS T
    rw [hwS] at hsum
    refine le_trans hsum ?_
    exact pow_le_pow_left₀ (norm_nonneg _) hwSK 2
  refine ⟨⟨shellWeightField m ((E v : H) : (P → ℤ) → ℂ),
    memℓp_of_forall_finset_sum_sq_le (K := K ^ 2) hkey⟩, rfl,
    norm_le_of_forall_finset_sum_sq_le hK0 hkey⟩

/-! ## Time reversal -/

omit [Fintype P] [DecidableEq P] in
/-- The evolution as a linear isometry. -/
def expIsometry {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (x : ℝ) : H →ₗᵢ[ℂ] H where
  toLinearMap :=
    (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) : H →L[ℂ] H).toLinearMap
  norm_map' := norm_exp_latticeAdjacency_apply hsa x

omit [Fintype P] [DecidableEq P] in
/-- The evolution preserves inner products. -/
theorem inner_exp_latticeAdjacency {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (x : ℝ) (a b : H) :
    (inner ℂ (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) a)
        (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) b) : ℂ)
      = inner ℂ a b :=
  (expIsometry hsa x).inner_map_map a b

omit [Fintype P] [DecidableEq P] in
/-- **Time reversal.**  The evolutions at opposite times are mutually inverse. -/
theorem exp_latticeAdjacency_neg_apply (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (x : ℝ) (ζ : H) :
    NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
        (NormedSpace.exp ((-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c) ζ) = ζ := by
  letI : NormedAlgebra ℚ (lp (fun _ : (P → ℤ) => ℂ) 2 →L[ℂ] lp (fun _ : (P → ℤ) => ℂ) 2) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have hcomm : Commute ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
      ((-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c) :=
    ((Commute.refl (latticeAdjacency Q c)).smul_left _).smul_right _
  have hzero : (-(x : ℂ) * Complex.I) • latticeAdjacency Q c
      + (-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c = 0 := by
    rw [← add_smul, show (-(x : ℂ) * Complex.I + -((-x : ℝ) : ℂ) * Complex.I) = 0 by
      push_cast
      ring, zero_smul]
  have hmul : NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
      * NormedSpace.exp ((-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c) = 1 := by
    rw [← NormedSpace.exp_add_of_commute hcomm, hzero, NormedSpace.exp_zero]
  have happ := congrArg (fun T : H →L[ℂ] H => T ζ) hmul
  simpa [mul_apply_eq_comp] using happ

/-! ## `(17)` and `(9)`: the weighted conjugation -/

set_option maxHeartbeats 1000000 in
omit [DecidableEq P] in
/-- **`(17)`.**  Conjugating the evolution by the polynomial weight `⟨X⟩^{-m}` costs exactly `m`
powers of the time. -/
theorem exists_norm_invShell_exp_le {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (η : H),
      ‖invShellLM m (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) η)‖
        ≤ C * (1 + |x|) ^ m * ‖invShellLM m η‖ := by
  obtain ⟨C, hC, hb⟩ := exists_shellWeighted_exp hsa m
  refine ⟨C, hC, fun x η => ?_⟩
  obtain ⟨w, hwdef⟩ : ∃ w : H,
      w = invShellLM m (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) η) :=
    ⟨_, rfl⟩
  obtain ⟨ζ, hζdef⟩ : ∃ z : H, z = invShellLM m w := ⟨_, rfl⟩
  rw [← hwdef]
  have hζw : ((w : H) : (P → ℤ) → ℂ) = shellWeightField m ((ζ : H) : (P → ℤ) → ℂ) := by
    rw [hζdef, coe_invShellLM, shellWeightField_invShellField]
  obtain ⟨w', hw'coe, hw'n⟩ := hb (-x) ζ w hζw
  rw [abs_neg] at hw'n
  have hinner1 : (inner ℂ ζ
      (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) η) : ℂ)
      = inner ℂ w w := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun r => ?_
    simp only [hζdef, hwdef, coe_invShellLM, RCLike.inner_apply, invShellField, map_mul,
      map_inv₀, Complex.conj_ofReal]
    ring
  have hinner2 : (inner ℂ ζ
      (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) η) : ℂ)
      = inner ℂ (NormedSpace.exp ((-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c) ζ) η := by
    have hUU : NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
        (NormedSpace.exp ((-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c) ζ)
        = ζ := exp_latticeAdjacency_neg_apply Q c x ζ
    calc (inner ℂ ζ
          (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) η) : ℂ)
        = inner ℂ (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c)
            (NormedSpace.exp ((-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c) ζ))
            (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) η) := by rw [hUU]
      _ = inner ℂ (NormedSpace.exp ((-((-x : ℝ) : ℂ) * Complex.I)
            • latticeAdjacency Q c) ζ) η := inner_exp_latticeAdjacency hsa x _ _
  have hinner3 :
      (inner ℂ (NormedSpace.exp ((-((-x : ℝ) : ℂ) * Complex.I) • latticeAdjacency Q c) ζ) η : ℂ)
        = inner ℂ w' (invShellLM m η) := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun r => ?_
    have hne := ofReal_shellWeight_ne_zero (P := P) m r
    simp only [RCLike.inner_apply, coe_invShellLM, congrFun hw'coe r, invShellField,
      shellWeightField, map_mul, Complex.conj_ofReal]
    field_simp
  have hDη : (0 : ℝ) ≤ ‖invShellLM (P := P) m η‖ := norm_nonneg _
  have hcoef : (0 : ℝ) ≤ C * (1 + |x|) ^ m := mul_nonneg hC (by positivity)
  have hnormsq : ‖w‖ ^ 2 = ‖(inner ℂ w w : ℂ)‖ := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow]
    simp
  have hfinal : ‖w‖ ^ 2 ≤ (C * (1 + |x|) ^ m * ‖invShellLM (P := P) m η‖) * ‖w‖ := by
    rw [hnormsq, ← hinner1, hinner2, hinner3]
    refine le_trans (norm_inner_le_norm _ _) ?_
    have h1 : ‖w'‖ * ‖invShellLM (P := P) m η‖
        ≤ (C * (1 + |x|) ^ m * ‖w‖) * ‖invShellLM (P := P) m η‖ :=
      mul_le_mul_of_nonneg_right hw'n hDη
    refine le_trans h1 (le_of_eq ?_)
    ring
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | h0
  · rw [← h0]
    exact mul_nonneg hcoef hDη
  · nlinarith [hfinal, h0]

omit [DecidableEq P] in
/-- **`(18)`: the weighted evolution.**  The continuous extension of `D_w e^{-ixA} D_w^{-1}`, where
`D_w` is multiplication by `⟨X⟩^{-m}`. -/
def weightedEvolution (Q : Finset (P → ℤ)) (c : (P → ℤ) → ℂ) (m : ℕ) (x : ℝ) : H →L[ℂ] H :=
  LinearMap.extendOfNorm
    ((invShellLM m).comp
      (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) : H →L[ℂ] H).toLinearMap)
    (invShellLM m)

omit [DecidableEq P] in
/-- The weighted evolution conjugates the evolution by the polynomial weight. -/
theorem weightedEvolution_apply {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (m : ℕ) (x : ℝ) (η : H) :
    weightedEvolution Q c m x (invShellLM m η)
      = invShellLM m (NormedSpace.exp ((-(x : ℂ) * Complex.I) • latticeAdjacency Q c) η) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_invShell_exp_le hsa m
  exact LinearMap.extendOfNorm_eq (denseRange_invShellLM m)
    ⟨C * (1 + |x|) ^ m, fun ψ => hb x ψ⟩ η

omit [DecidableEq P] in
/-- **`(9)`: the weighted prime group grows at most polynomially.** -/
theorem exists_norm_weightedEvolution_le {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖weightedEvolution Q c m x‖ ≤ C * (1 + |x|) ^ m := by
  obtain ⟨C, hC, hb⟩ := exists_norm_invShell_exp_le hsa m
  refine ⟨C, hC, fun x => ?_⟩
  exact LinearMap.opNorm_extendOfNorm_le (denseRange_invShellLM m)
    (mul_nonneg hC (by positivity)) fun ψ => hb x ψ

omit [DecidableEq P] in
/-- **`(9)` in the two-sided form of the card.** -/
theorem exists_norm_weightedEvolution_add_le {Q : Finset (P → ℤ)} {c : (P → ℤ) → ℂ}
    (hsa : IsSelfAdjoint (latticeAdjacency Q c)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖weightedEvolution Q c m (x / 2)‖ + ‖weightedEvolution Q c m (-x / 2)‖
        ≤ C * (1 + |x|) ^ m := by
  obtain ⟨C, hC, hb⟩ := exists_norm_weightedEvolution_le hsa m
  refine ⟨2 * C, by linarith, fun x => ?_⟩
  have hhalf : ∀ y : ℝ, |y / 2| ≤ |x| → (1 + |y / 2|) ^ m ≤ (1 + |x|) ^ m := by
    intro y hy
    exact pow_le_pow_left₀ (by positivity) (by linarith) m
  have habs2 : |(2 : ℝ)| = 2 := by norm_num
  have h1 : ‖weightedEvolution Q c m (x / 2)‖ ≤ C * (1 + |x|) ^ m := by
    refine le_trans (hb (x / 2)) (mul_le_mul_of_nonneg_left (hhalf x ?_) hC)
    rw [abs_div, habs2]
    linarith [abs_nonneg x]
  have h2 : ‖weightedEvolution Q c m (-x / 2)‖ ≤ C * (1 + |x|) ^ m := by
    refine le_trans (hb (-x / 2)) (mul_le_mul_of_nonneg_left (hhalf (-x) ?_) hC)
    rw [abs_div, abs_neg, habs2]
    linarith [abs_nonneg x]
  linarith

end RHTower
