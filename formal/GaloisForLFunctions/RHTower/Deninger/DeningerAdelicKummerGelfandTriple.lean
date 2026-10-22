import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# The mixed `L¹/L²` rigged Hilbert triple

A test space continuously and densely embedded in a Hilbert space produces a rigged Hilbert
triple `E ↪ H ↪ E'`, the second map sending `h` to the functional `e ↦ ⟪i e, h⟫`.

This file proves the abstract construction and then builds the mixed `L¹/L²` test space over an
arbitrary measure space and shows it is such an `E`.

* `deningerRiggedDual` is the distribution map `H → E'`, with `deningerRiggedDual_apply`,
  `deningerRiggedDual_norm_le` and `deningerRiggedDual_injective` (injective as soon as the test
  embedding has dense range).
* `deningerMixedL12` is the mixed carrier: pairs of an `L¹` class and an `L²` class that agree
  almost everywhere, normed by `‖f‖₁ + ‖f‖₂`.
* `deningerMixedToL2` is the canonical map into `L²`; it is norm-decreasing, injective, and has
  dense range, so `deningerMixedGelfandTriple` is an unconditional rigged Hilbert triple.
* `deningerMixedIntegral` is the product-formula functional; it satisfies
  `|I f| ≤ ‖f‖₁ ≤ ‖f‖_E`, so its kernel is closed and it vanishes on the closure of any set on
  which it vanishes.
-/

namespace RHTower

open MeasureTheory

section RiggedTriple

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The distribution map `H → E'` attached to a test embedding `i : E → H`. -/
noncomputable def deningerRiggedDual (i : E →L[ℝ] H) : H →L[ℝ] (E →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ E H ℝ).flip i).comp (innerSL ℝ)

@[simp] theorem deningerRiggedDual_apply (i : E →L[ℝ] H) (h : H) (e : E) :
    deningerRiggedDual i h e = inner ℝ h (i e) := rfl

theorem deningerRiggedDual_apply' (i : E →L[ℝ] H) (h : H) (e : E) :
    deningerRiggedDual i h e = inner ℝ (i e) h := by
  rw [deningerRiggedDual_apply, real_inner_comm]

theorem deningerRiggedDual_norm_le (i : E →L[ℝ] H) (h : H) :
    ‖deningerRiggedDual i h‖ ≤ ‖h‖ * ‖i‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
  calc ‖deningerRiggedDual i h e‖ = ‖inner ℝ h (i e)‖ := rfl
    _ ≤ ‖h‖ * ‖i e‖ := by
        rw [Real.norm_eq_abs]
        exact abs_real_inner_le_norm h (i e)
    _ ≤ ‖h‖ * (‖i‖ * ‖e‖) := by
        gcongr
        exact i.le_opNorm e
    _ = ‖h‖ * ‖i‖ * ‖e‖ := by ring

/-- **Rigged triple.**  If the test embedding has dense range, the distribution map is
injective. -/
theorem deningerRiggedDual_injective (i : E →L[ℝ] H) (hd : DenseRange i) :
    Function.Injective (deningerRiggedDual i) := by
  refine (injective_iff_map_eq_zero (deningerRiggedDual i).toLinearMap).mpr fun h hh => ?_
  have hzero : ∀ y : H, inner ℝ h y = (0 : ℝ) := by
    have hcont : Continuous fun y : H => inner ℝ h y :=
      (innerSL ℝ h).continuous
    have heq : ∀ e : E, inner ℝ h (i e) = (0 : ℝ) := by
      intro e
      have := congrArg (fun φ : E →L[ℝ] ℝ => φ e) hh
      simpa using this
    have hEq : Set.EqOn (fun y : H => inner ℝ h y) (fun _ : H => (0 : ℝ)) (Set.range i) := by
      rintro _ ⟨e, rfl⟩
      exact heq e
    have hfun : (fun y : H => inner ℝ h y) = fun _ : H => (0 : ℝ) :=
      Continuous.ext_on hd hcont continuous_const hEq
    intro y
    exact congrFun hfun y
  have := hzero h
  rwa [real_inner_self_eq_norm_sq, pow_eq_zero_iff (by norm_num), norm_eq_zero] at this

end RiggedTriple

section MixedL12

variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

/-- The mixed `L¹/L²` carrier: pairs of an `L¹` class and an `L²` class agreeing almost
everywhere.  The ambient norm is `‖f‖₁ + ‖f‖₂`. -/
def deningerMixedL12 : Submodule ℝ (WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)) where
  carrier := {x | (x.fst : Y → ℝ) =ᵐ[μ] (x.snd : Y → ℝ)}
  zero_mem' := by
    show ((0 : Lp ℝ 1 μ) : Y → ℝ) =ᵐ[μ] ((0 : Lp ℝ 2 μ) : Y → ℝ)
    filter_upwards [Lp.coeFn_zero ℝ 1 μ, Lp.coeFn_zero ℝ 2 μ] with t h1 h2
    rw [h1, h2]
  add_mem' := by
    intro x y hx hy
    show ((x.fst + y.fst : Lp ℝ 1 μ) : Y → ℝ) =ᵐ[μ] ((x.snd + y.snd : Lp ℝ 2 μ) : Y → ℝ)
    filter_upwards [hx, hy, Lp.coeFn_add x.fst y.fst, Lp.coeFn_add x.snd y.snd]
      with t hxt hyt h1 h2
    rw [h1, h2]
    simp only [Pi.add_apply]
    rw [hxt, hyt]
  smul_mem' := by
    intro c x hx
    show ((c • x.fst : Lp ℝ 1 μ) : Y → ℝ) =ᵐ[μ] ((c • x.snd : Lp ℝ 2 μ) : Y → ℝ)
    filter_upwards [hx, Lp.coeFn_smul c x.fst, Lp.coeFn_smul c x.snd] with t hxt h1 h2
    rw [h1, h2]
    simp only [Pi.smul_apply]
    rw [hxt]

/-- The `L¹` projection of the ambient mixed product. -/
noncomputable def deningerAmbFst :
    WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ) →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.fst
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
      intro x
      rw [one_mul, WithLp.prod_norm_eq_of_L1]
      exact le_add_of_nonneg_right (norm_nonneg _))

/-- The `L²` projection of the ambient mixed product. -/
noncomputable def deningerAmbSnd :
    WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ) →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.snd
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
      intro x
      rw [one_mul, WithLp.prod_norm_eq_of_L1]
      exact le_add_of_nonneg_left (norm_nonneg _))

/-- **The mixed carrier is closed.**  Convergence in `L¹` and in `L²` both imply convergence in
measure, and the limit in measure is almost everywhere unique. -/
theorem deningerMixedL12_isClosed :
    IsClosed ((deningerMixedL12 μ : Submodule ℝ (WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ))) :
      Set (WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ))) := by
  refine IsSeqClosed.isClosed ?_
  intro u v hu huv
  have hu' : ∀ n, ((u n).fst : Y → ℝ) =ᵐ[μ] ((u n).snd : Y → ℝ) := fun n => hu n
  have h1 : Filter.Tendsto (fun n => (u n).fst) Filter.atTop (nhds v.fst) :=
    ((deningerAmbFst μ).continuous.tendsto v).comp huv
  have h2 : Filter.Tendsto (fun n => (u n).snd) Filter.atTop (nhds v.snd) :=
    ((deningerAmbSnd μ).continuous.tendsto v).comp huv
  have m1 : MeasureTheory.TendstoInMeasure μ (fun n => ((u n).fst : Y → ℝ)) Filter.atTop
      ((v.fst : Y → ℝ)) := MeasureTheory.tendstoInMeasure_of_tendsto_Lp h1
  have m2 : MeasureTheory.TendstoInMeasure μ (fun n => ((u n).snd : Y → ℝ)) Filter.atTop
      ((v.snd : Y → ℝ)) := MeasureTheory.tendstoInMeasure_of_tendsto_Lp h2
  have m1' : MeasureTheory.TendstoInMeasure μ (fun n => ((u n).fst : Y → ℝ)) Filter.atTop
      ((v.snd : Y → ℝ)) := m2.congr_left fun n => (hu' n).symm
  exact MeasureTheory.tendstoInMeasure_ae_unique m1 m1'

/-- The mixed `L¹/L²` test space. -/
abbrev DeningerMixed := ↥(deningerMixedL12 μ)

/-- The mixed test space is a Banach space. -/
instance : CompleteSpace (DeningerMixed μ) :=
  (deningerMixedL12_isClosed μ).completeSpace_coe

theorem deningerMixed_norm (x : DeningerMixed μ) :
    ‖x‖ = ‖(x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).fst‖
      + ‖(x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).snd‖ :=
  WithLp.prod_norm_eq_of_L1 _

/-- The `L¹` component of the mixed test space. -/
noncomputable def deningerMixedToL1 : DeningerMixed μ →L[ℝ] Lp ℝ 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun x => (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).fst
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
      intro x
      rw [one_mul, deningerMixed_norm]
      exact le_add_of_nonneg_right (norm_nonneg _))

/-- The `L²` component of the mixed test space: the canonical test embedding. -/
noncomputable def deningerMixedToL2 : DeningerMixed μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun x => (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).snd
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (by
      intro x
      rw [one_mul, deningerMixed_norm]
      exact le_add_of_nonneg_left (norm_nonneg _))

@[simp] theorem deningerMixedToL1_apply (x : DeningerMixed μ) :
    deningerMixedToL1 μ x = (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).fst := rfl

@[simp] theorem deningerMixedToL2_apply (x : DeningerMixed μ) :
    deningerMixedToL2 μ x = (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).snd := rfl

/-- The test embedding is injective. -/
theorem deningerMixedToL2_injective : Function.Injective (deningerMixedToL2 μ) := by
  refine (injective_iff_map_eq_zero (deningerMixedToL2 μ).toLinearMap).mpr fun x hx => ?_
  have hsnd : (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).snd = 0 := hx
  have hfst : (x : WithLp 1 (Lp ℝ 1 μ × Lp ℝ 2 μ)).fst = 0 := by
    refine Lp.ext ?_
    filter_upwards [x.2, Lp.coeFn_zero ℝ 1 μ, Lp.coeFn_zero ℝ 2 μ] with t ht h1 h2
    rw [ht, hsnd, h1, h2]
  refine Subtype.ext (WithLp.ofLp_injective 1 (Prod.ext hfst hsnd))

/-- An `L²` class represented by a simple function lies in the range of the test embedding. -/
theorem deningerMixedToL2_range_simpleFunc (s : Lp.simpleFunc ℝ 2 μ) :
    (s : Lp ℝ 2 μ) ∈ Set.range (deningerMixedToL2 μ) := by
  have hs2 : MemLp (Lp.simpleFunc.toSimpleFunc s) 2 μ :=
    (Lp.memLp (s : Lp ℝ 2 μ)).ae_eq (Lp.simpleFunc.toSimpleFunc_eq_toFun s).symm
  have hfin := (SimpleFunc.memLp_iff_finMeasSupp (by norm_num) (by norm_num)).mp hs2
  have hs1 : MemLp (Lp.simpleFunc.toSimpleFunc s) 1 μ :=
    (SimpleFunc.memLp_iff_finMeasSupp (by norm_num) (by norm_num)).mpr hfin
  have hcoe1 : MemLp ((s : Lp ℝ 2 μ) : Y → ℝ) 1 μ :=
    hs1.ae_eq (Lp.simpleFunc.toSimpleFunc_eq_toFun s)
  refine ⟨⟨WithLp.toLp 1 (hcoe1.toLp _, (s : Lp ℝ 2 μ)), ?_⟩, rfl⟩
  exact hcoe1.coeFn_toLp

/-- **Density.**  The test embedding has dense range: the mixed space is dense in `L²`. -/
theorem deningerMixedToL2_denseRange : DenseRange (deningerMixedToL2 μ) := by
  have hbasis : DenseRange ((↑) : Lp.simpleFunc ℝ 2 μ → Lp ℝ 2 μ) :=
    Lp.simpleFunc.denseRange (by norm_num)
  refine hbasis.mono ?_
  rintro _ ⟨s, rfl⟩
  exact deningerMixedToL2_range_simpleFunc μ s

/-- **The rigged Hilbert triple.**  The mixed `L¹/L²` space embeds continuously, injectively and
densely in `L²`, and the induced distribution map into its dual is injective. -/
theorem deningerMixedGelfandTriple :
    Function.Injective (deningerMixedToL2 μ) ∧ DenseRange (deningerMixedToL2 μ)
      ∧ Function.Injective (deningerRiggedDual (deningerMixedToL2 μ)) :=
  ⟨deningerMixedToL2_injective μ, deningerMixedToL2_denseRange μ,
    deningerRiggedDual_injective _ (deningerMixedToL2_denseRange μ)⟩

/-- The product-formula functional on the mixed test space. -/
noncomputable def deningerMixedIntegral : DeningerMixed μ →L[ℝ] ℝ :=
  (MeasureTheory.L1.integralCLM (α := Y) (E := ℝ) (μ := μ)).comp (deningerMixedToL1 μ)

/-- **Continuity of the product formula.**  `|I f| ≤ ‖f‖₁ ≤ ‖f‖_E`. -/
theorem deningerMixedIntegral_norm_le (x : DeningerMixed μ) :
    |deningerMixedIntegral μ x| ≤ ‖x‖ := by
  have hop : ‖MeasureTheory.L1.integralCLM (α := Y) (E := ℝ) (μ := μ)‖ ≤ 1 :=
    MeasureTheory.L1.norm_Integral_le_one
  have hle := (MeasureTheory.L1.integralCLM (α := Y) (E := ℝ) (μ := μ)).le_opNorm
    (deningerMixedToL1 μ x)
  have h1 : |deningerMixedIntegral μ x| ≤ ‖deningerMixedToL1 μ x‖ := by
    rw [← Real.norm_eq_abs]
    refine hle.trans ?_
    calc ‖MeasureTheory.L1.integralCLM (α := Y) (E := ℝ) (μ := μ)‖ * ‖deningerMixedToL1 μ x‖
        ≤ 1 * ‖deningerMixedToL1 μ x‖ := by gcongr
      _ = ‖deningerMixedToL1 μ x‖ := one_mul _
  refine h1.trans ?_
  rw [deningerMixedToL1_apply, deningerMixed_norm]
  exact le_add_of_nonneg_right (norm_nonneg _)

/-- The product-formula kernel is closed. -/
theorem deningerMixedIntegral_isClosed_ker :
    IsClosed {x : DeningerMixed μ | deningerMixedIntegral μ x = 0} :=
  (deningerMixedIntegral μ).isClosed_ker

/-- **Closure stability.**  A functional vanishing on a set vanishes on its closure. -/
theorem deningerMixedIntegral_eq_zero_of_mem_closure {S : Set (DeningerMixed μ)}
    (hS : ∀ x ∈ S, deningerMixedIntegral μ x = 0) {x : DeningerMixed μ}
    (hx : x ∈ closure S) : deningerMixedIntegral μ x = 0 :=
  (deningerMixedIntegral_isClosed_ker μ).closure_subset_iff.mpr hS hx

end MixedL12

end RHTower
