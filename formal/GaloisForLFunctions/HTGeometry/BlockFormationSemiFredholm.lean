import GaloisForLFunctions.HTGeometry.GlobalGramResidualCoverage
import GaloisForLFunctions.HTGeometry.RectangularVectorDiagonal

/-!
# Block-formation semi-Fredholm classification

For uniformly bounded blocks `T_n : H_n → Y_n` the block formation `𝐓 = ⊕_n T_n` is bounded and,
with the reduced minimum modulus `γ(T) = inf {‖T x‖ : x ⊥ ker T, ‖x‖ = 1}` (`+∞` on a trivial
complement):

* `(5.12)` `ker 𝐓 = ⊕_n ker T_n`;
* `(5.13)` `ran 𝐓` is closed iff `inf_n γ(T_n) > 0`;
* `(5.14)` `𝐓` has closed range and finite-dimensional kernel iff `inf_n γ(T_n) > 0` and
  `Σ_n dim ker T_n < ∞` (the dimension of the algebraic direct sum of the kernels);
* `(5.15)` for injective blocks with closed range the Moore–Penrose inverses satisfy
  `‖T_n†‖ = γ(T_n)⁻¹`, so they assemble to a bounded decoder of `𝐓` iff
  `sup_n ‖T_n†‖ = (inf_n γ(T_n))⁻¹ < ∞`.

Both conditions are invariant under unitary conjugation and permutation of the blocks.
-/

open Filter Topology
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TightFormation

universe uH uY

/-! ### The reduced minimum modulus -/

section ReducedMinModulus

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The reduced minimum modulus `γ(T) = inf {‖T x‖ : x ∈ (ker T)ᗮ, ‖x‖ = 1}`, valued in `[0, ∞]`,
with `γ(T) = ∞` when `(ker T)ᗮ = 0`. -/
def reducedMinModulus (T : E →L[ℂ] F) : ℝ≥0∞ :=
  ⨅ (x : E) (_ : x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ) (_ : ‖x‖ = 1), (‖T x‖₊ : ℝ≥0∞)

theorem le_reducedMinModulus_iff (T : E →L[ℂ] F) (c : ℝ≥0) :
    (c : ℝ≥0∞) ≤ reducedMinModulus T ↔
      ∀ x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ, (c : ℝ) * ‖x‖ ≤ ‖T x‖ := by
  constructor
  · intro h x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    set u : E := ((‖x‖ : ℂ)⁻¹) • x with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hxpos.le,
        inv_mul_cancel₀ hxpos.ne']
    have humem : u ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ := Submodule.smul_mem _ _ hx
    have hle : (c : ℝ≥0∞) ≤ ‖T u‖₊ := (h.trans (iInf₂_le u humem)).trans (iInf_le _ hu1)
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at hle
    have hTu : ‖T u‖ = ‖x‖⁻¹ * ‖T x‖ := by
      rw [hu, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hxpos.le]
    rw [hTu] at hle
    calc (c : ℝ) * ‖x‖ ≤ ‖x‖⁻¹ * ‖T x‖ * ‖x‖ := mul_le_mul_of_nonneg_right hle hxpos.le
      _ = ‖T x‖ := by field_simp
  · intro h
    refine le_iInf₂ fun x hx => le_iInf fun hx1 => ?_
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
    simpa [hx1] using h x hx

/-- `inf_n γ(T_n) > 0` is a uniform lower bound on the kernel complements. -/
theorem pos_iInf_reducedMinModulus_iff {ι : Type*} {E' F' : ι → Type*}
    [∀ n, NormedAddCommGroup (E' n)] [∀ n, InnerProductSpace ℂ (E' n)]
    [∀ n, NormedAddCommGroup (F' n)] [∀ n, InnerProductSpace ℂ (F' n)]
    (T : ∀ n, E' n →L[ℂ] F' n) :
    0 < ⨅ n, reducedMinModulus (T n) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ n, ∀ x ∈ (LinearMap.ker (T n : E' n →ₗ[ℂ] F' n))ᗮ,
        c * ‖x‖ ≤ ‖T n x‖ := by
  constructor
  · intro h
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
    refine ⟨(r : ℝ), NNReal.coe_pos.2 (ENNReal.coe_pos.1 hr0), fun n => ?_⟩
    exact (le_reducedMinModulus_iff (T n) r).1 (hr.le.trans (iInf_le _ n))
  · rintro ⟨c, hc, h⟩
    set r : ℝ≥0 := ⟨c, hc.le⟩ with hr
    have hle : (r : ℝ≥0∞) ≤ ⨅ n, reducedMinModulus (T n) :=
      le_iInf fun n => (le_reducedMinModulus_iff (T n) r).2 (h n)
    have hr0 : (0 : ℝ≥0) < r := hc
    exact lt_of_lt_of_le (ENNReal.coe_pos.2 hr0) hle

end ReducedMinModulus

/-! ### The Moore–Penrose inverse and `(5.15)` -/

section MoorePenrose

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
theorem completeSpace_range {T : E →L[ℂ] F} (hcl : IsClosed (Set.range T)) :
    CompleteSpace (LinearMap.range (T : E →ₗ[ℂ] F)) := by
  have h : IsClosed ((LinearMap.range (T : E →ₗ[ℂ] F) : Set F)) := by
    rw [LinearMap.coe_range]
    exact hcl
  exact h.completeSpace_coe

/-- The corestriction of `T` onto its range. -/
def rangeCorestrict (T : E →L[ℂ] F) : E →L[ℂ] LinearMap.range (T : E →ₗ[ℂ] F) :=
  T.codRestrict _ fun x => LinearMap.mem_range_self _ x

omit [CompleteSpace E] [CompleteSpace F] in
theorem rangeCorestrict_ker {T : E →L[ℂ] F} (hinj : Function.Injective T) :
    LinearMap.ker (rangeCorestrict T : E →ₗ[ℂ] LinearMap.range (T : E →ₗ[ℂ] F)) = ⊥ :=
  LinearMap.ker_eq_bot.2 fun _ _ h => hinj (congrArg Subtype.val h)

omit [CompleteSpace E] [CompleteSpace F] in
theorem rangeCorestrict_range (T : E →L[ℂ] F) :
    LinearMap.range (rangeCorestrict T : E →ₗ[ℂ] LinearMap.range (T : E →ₗ[ℂ] F)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨_, x, rfl⟩ -
  exact ⟨x, rfl⟩

/-- The Moore–Penrose inverse `T† = (T|_{ran})⁻¹ ∘ P_{ran T}` of an injective operator with closed
range. -/
def moorePenrose (T : E →L[ℂ] F) (hinj : Function.Injective T) (hcl : IsClosed (Set.range T)) :
    F →L[ℂ] E :=
  haveI := completeSpace_range hcl
  ((ContinuousLinearEquiv.ofBijective (rangeCorestrict T) (rangeCorestrict_ker hinj)
      (rangeCorestrict_range T)).symm : LinearMap.range (T : E →ₗ[ℂ] F) →L[ℂ] E) ∘L
    (LinearMap.range (T : E →ₗ[ℂ] F)).orthogonalProjectionOnto

variable {T : E →L[ℂ] F} (hinj : Function.Injective T) (hcl : IsClosed (Set.range T))

/-- `T† T = I`. -/
theorem moorePenrose_apply_self (x : E) : moorePenrose T hinj hcl (T x) = x := by
  haveI := completeSpace_range hcl
  have hP : (LinearMap.range (T : E →ₗ[ℂ] F)).orthogonalProjectionOnto (T x) =
      rangeCorestrict T x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨T x, x, rfl⟩ :
      LinearMap.range (T : E →ₗ[ℂ] F))
  simp only [moorePenrose, ContinuousLinearMap.comp_apply]
  rw [hP]
  exact ContinuousLinearEquiv.ofBijective_symm_apply_apply _ _ _ x

/-- `‖T T† y‖ ≤ ‖y‖`: `T T†` is the orthogonal projection onto `ran T`. -/
theorem norm_apply_moorePenrose_le (y : F) : ‖T (moorePenrose T hinj hcl y)‖ ≤ ‖y‖ := by
  haveI := completeSpace_range hcl
  have h : T (moorePenrose T hinj hcl y) =
      ((LinearMap.range (T : E →ₗ[ℂ] F)).orthogonalProjectionOnto y : F) := by
    have := ContinuousLinearEquiv.ofBijective_apply_symm_apply (rangeCorestrict T)
      (rangeCorestrict_ker hinj) (rangeCorestrict_range T)
      ((LinearMap.range (T : E →ₗ[ℂ] F)).orthogonalProjectionOnto y)
    exact congrArg Subtype.val this
  rw [h, ← Submodule.coe_norm]
  calc ‖(LinearMap.range (T : E →ₗ[ℂ] F)).orthogonalProjectionOnto y‖
      ≤ ‖(LinearMap.range (T : E →ₗ[ℂ] F)).orthogonalProjectionOnto‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right
        (Submodule.orthogonalProjectionOnto_norm_le _) (norm_nonneg _)
    _ = ‖y‖ := one_mul _

/-- A lower bound `c‖x‖ ≤ ‖T x‖` gives `‖T†‖ ≤ c⁻¹`. -/
theorem norm_moorePenrose_le {c : ℝ} (hc : 0 < c) (h : ∀ x, c * ‖x‖ ≤ ‖T x‖) :
    ‖moorePenrose T hinj hcl‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => by
    have h1 := (h (moorePenrose T hinj hcl y)).trans (norm_apply_moorePenrose_le hinj hcl y)
    rw [le_inv_mul_iff₀ hc]
    exact h1

theorem norm_le_norm_moorePenrose_mul (x : E) : ‖x‖ ≤ ‖moorePenrose T hinj hcl‖ * ‖T x‖ := by
  conv_lhs => rw [← moorePenrose_apply_self hinj hcl x]
  exact ContinuousLinearMap.le_opNorm _ _

include hinj in
omit [CompleteSpace E] [CompleteSpace F] in
theorem mem_ker_orthogonal_of_injective (x : E) :
    x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ := by
  rw [LinearMap.ker_eq_bot.2 hinj, Submodule.bot_orthogonal_eq_top]
  exact Submodule.mem_top

/-- **`(5.15)`, one block**: `‖T†‖ = γ(T)⁻¹`. -/
theorem nnnorm_moorePenrose_eq :
    (‖moorePenrose T hinj hcl‖₊ : ℝ≥0∞) = (reducedMinModulus T)⁻¹ := by
  suffices hγ : reducedMinModulus T = (‖moorePenrose T hinj hcl‖₊ : ℝ≥0∞)⁻¹ by
    rw [hγ, inv_inv]
  apply le_antisymm
  · -- `γ ≤ ‖T†‖⁻¹`
    rcases eq_or_ne ‖moorePenrose T hinj hcl‖₊ 0 with h0 | h0
    · rw [h0, ENNReal.coe_zero, ENNReal.inv_zero]
      exact le_top
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hb := (le_reducedMinModulus_iff T r).1 hr.le
    have hn := norm_moorePenrose_le hinj hcl (c := r) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr0))
      fun x => hb x (mem_ker_orthogonal_of_injective hinj x)
    rw [← ENNReal.coe_inv h0, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_inv,
      coe_nnnorm]
    rw [le_inv_comm₀ (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr0)) (norm_pos_iff.2 (by
      intro h; exact h0 (by rw [← nnnorm_eq_zero] at h; exact h)))]
    exact hn
  · -- `‖T†‖⁻¹ ≤ γ`
    refine le_iInf₂ fun x _ => le_iInf fun hx1 => ?_
    have h := norm_le_norm_moorePenrose_mul hinj hcl x
    rw [hx1] at h
    have h0 : ‖moorePenrose T hinj hcl‖₊ ≠ 0 := by
      intro h0
      rw [← coe_nnnorm, h0, NNReal.coe_zero, zero_mul] at h
      linarith
    rw [← ENNReal.coe_inv h0, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_inv,
      coe_nnnorm, coe_nnnorm, inv_le_iff_one_le_mul₀ (norm_pos_iff.2 (by
        intro h'; exact h0 (by rw [← nnnorm_eq_zero] at h'; exact h')))]
    linarith [mul_comm ‖T x‖ ‖moorePenrose T hinj hcl‖]

end MoorePenrose

/-! ### Theorem 5.3: the block formation -/

section Block

variable {ι : Type} [DecidableEq ι] {H : ι → Type uH} {Y : ι → Type uY}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]
  [∀ n, NormedAddCommGroup (Y n)] [∀ n, InnerProductSpace ℂ (Y n)] [∀ n, CompleteSpace (Y n)]
  (T : ∀ n, H n →L[ℂ] Y n) {M : ℝ} (hM : 0 ≤ M) (hT : ∀ n, ‖T n‖ ≤ M)

/-- **`(5.10)`**: the block formation `𝐓 = ⊕_n T_n`. -/
def blockFormation : lp H 2 →L[ℂ] lp Y 2 := RHTower.rectangularBlockOperator T hM hT

omit [DecidableEq ι] [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
theorem blockFormation_apply (x : lp H 2) (n : ι) :
    (blockFormation T hM hT x : ∀ n, Y n) n = T n ((x : ∀ n, H n) n) := rfl

omit [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
theorem blockFormation_single (n : ι) (v : H n) :
    blockFormation T hM hT (lp.single 2 n v) = lp.single 2 n (T n v) :=
  RHTower.rectangularBlockOperator_single T hM hT n v

omit [DecidableEq ι] [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
/-- **`(5.12)`**: `ker 𝐓 = ⊕_n ker T_n`. -/
theorem mem_ker_blockFormation (x : lp H 2) :
    x ∈ LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2) ↔
      ∀ n, (x : ∀ n, H n) n ∈ LinearMap.ker (T n : H n →ₗ[ℂ] Y n) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h n
    have := congrArg (fun z : lp Y 2 => (z : ∀ n, Y n) n) h
    simpa [blockFormation_apply] using this
  · intro h
    exact lp.ext (funext fun n => h n)

omit [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
theorem single_mem_ker_orthogonal {n : ι} {v : H n}
    (hv : v ∈ (LinearMap.ker (T n : H n →ₗ[ℂ] Y n))ᗮ) :
    lp.single 2 n v ∈ (LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro k hk
  rw [lp.inner_single_right]
  exact inner_eq_zero_symm.1
    ((Submodule.mem_orthogonal' _ _).1 hv _ ((mem_ker_blockFormation T hM hT k).1 hk n))

omit [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
theorem coord_mem_ker_orthogonal {x : lp H 2}
    (hx : x ∈ (LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2))ᗮ) (n : ι) :
    (x : ∀ n, H n) n ∈ (LinearMap.ker (T n : H n →ₗ[ℂ] Y n))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hmem : lp.single 2 n w ∈ LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2) := by
    rw [mem_ker_blockFormation]
    intro m
    rcases eq_or_ne m n with rfl | h
    · rwa [lp.single_apply_self]
    · rw [lp.single_apply_ne _ _ _ h]
      exact Submodule.zero_mem _
  have := (Submodule.mem_orthogonal _ _).1 hx _ hmem
  rwa [lp.inner_single_left] at this

/-- **`(5.13)`**: `ran 𝐓` is closed iff `inf_n γ(T_n) > 0`. -/
theorem isClosed_range_blockFormation_iff :
    IsClosed (Set.range (blockFormation T hM hT)) ↔ 0 < ⨅ n, reducedMinModulus (T n) := by
  rw [← ContinuousLinearMap.hasTransverseLowerBound_iff_isClosed_range,
    pos_iInf_reducedMinModulus_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun n v hv => ?_⟩
    have := h _ (single_mem_ker_orthogonal T hM hT hv)
    rwa [blockFormation_single, lp.norm_single (by norm_num), lp.norm_single (by norm_num)] at this
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, fun x hx => ?_⟩
    have hsq : (c * ‖x‖) ^ 2 ≤ ‖blockFormation T hM hT x‖ ^ 2 := by
      rw [mul_pow, norm_sq_lp, norm_sq_lp, ← tsum_mul_left]
      have hxs : Summable fun n => ‖(x : ∀ n, H n) n‖ ^ 2 := by
        simpa using (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      have hys : Summable fun n => ‖(blockFormation T hM hT x : ∀ n, Y n) n‖ ^ 2 := by
        simpa using (lp.memℓp (blockFormation T hM hT x)).summable
          (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      refine (hxs.mul_left _).tsum_le_tsum (fun n => ?_) hys
      rw [blockFormation_apply, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (h n _ (coord_mem_ker_orthogonal T hM hT hx n)) 2
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq

/-- The kernel components assemble into the kernel of `𝐓`. -/
def kernelAssembly : (DirectSum ι fun n => LinearMap.ker (T n : H n →ₗ[ℂ] Y n)) →ₗ[ℂ]
    LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2) :=
  DirectSum.toModule ℂ ι _ fun n =>
    { toFun := fun w => ⟨lp.single 2 n (w : H n), by
        rw [mem_ker_blockFormation]
        intro m
        rcases eq_or_ne m n with rfl | h
        · rw [lp.single_apply_self]
          exact w.2
        · rw [lp.single_apply_ne _ _ _ h]
          exact Submodule.zero_mem _⟩
      map_add' := fun a b => Subtype.ext (by
        simp only [Submodule.coe_add]
        exact lp.single_add 2 n (a : H n) b)
      map_smul' := fun a b => Subtype.ext (by
        simp only [Submodule.coe_smul, RingHom.id_apply]
        exact lp.single_smul 2 n a (b : H n)) }

omit [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
theorem kernelAssembly_lof (n : ι) (w : LinearMap.ker (T n : H n →ₗ[ℂ] Y n)) :
    (kernelAssembly T hM hT (DirectSum.lof ℂ ι _ n w) : lp H 2) = lp.single 2 n (w : H n) := by
  rw [kernelAssembly, DirectSum.toModule_lof]
  rfl

omit [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
theorem kernelAssembly_apply (z : DirectSum ι fun n => LinearMap.ker (T n : H n →ₗ[ℂ] Y n))
    (m : ι) :
    ((kernelAssembly T hM hT z : lp H 2) : ∀ n, H n) m = (z m : H m) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of n w =>
    rw [← DirectSum.lof_eq_of ℂ, kernelAssembly_lof]
    rcases eq_or_ne m n with rfl | h
    · rw [lp.single_apply_self, DirectSum.lof_eq_of, DirectSum.of_eq_same]
    · rw [lp.single_apply_ne _ _ _ h, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ h,
        Submodule.coe_zero]
  | add a b ha hb =>
    rw [map_add, Submodule.coe_add, lp.coeFn_add, Pi.add_apply, ha, hb, DirectSum.add_apply,
      Submodule.coe_add]

omit [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
theorem kernelAssembly_injective : Function.Injective (kernelAssembly T hM hT) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  refine DirectSum.ext _ fun m => Subtype.ext ?_
  have := kernelAssembly_apply T hM hT z m
  rw [hz] at this
  simpa using this.symm

omit [DecidableEq ι] in
theorem sum_lof_apply {K : ι → Type*} [∀ n, AddCommGroup (K n)] [∀ n, Module ℂ (K n)]
    [DecidableEq ι] (s : Finset ι) (v : ∀ n, K n) (m : ι) :
    (∑ n ∈ s, DirectSum.lof ℂ ι K n (v n)) m = if m ∈ s then v m else 0 := by
  rw [DirectSum.sum_apply]
  split_ifs with hm
  · rw [Finset.sum_eq_single m]
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
    · intro n _ hnm
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hnm)]
    · exact fun h => absurd hm h
  · refine Finset.sum_eq_zero fun n hn => ?_
    have hmn : m ≠ n := fun h => hm (h ▸ hn)
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hmn]

omit [∀ (n : ι), CompleteSpace (H n)] [∀ (n : ι), CompleteSpace (Y n)] in
/-- **`(5.12)`–`(5.14)`**: the kernel of `𝐓` is finite-dimensional iff `Σ_n dim ker T_n < ∞`. -/
theorem finiteDimensional_ker_blockFormation_iff :
    FiniteDimensional ℂ (LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2)) ↔
      Cardinal.sum (fun n => Module.rank ℂ (LinearMap.ker (T n : H n →ₗ[ℂ] Y n))) <
        Cardinal.aleph0 := by
  rw [← rank_directSum, Module.rank_lt_aleph0_iff]
  constructor
  · intro hfin
    exact Module.Finite.of_injective (kernelAssembly T hM hT) (kernelAssembly_injective T hM hT)
  · intro hfin
    refine Module.Finite.of_surjective (kernelAssembly T hM hT) fun x => ?_
    -- the support of a kernel vector is finite
    have hsupp : Set.Finite {n | (x : lp H 2) n ≠ 0} := by
      by_contra hinf
      let s := {n | (x : lp H 2) n ≠ 0}
      have hmem : ∀ n : s, (x : lp H 2) n ∈ LinearMap.ker (T n : H n →ₗ[ℂ] Y n) := fun n =>
        (mem_ker_blockFormation T hM hT x).1 x.2 n
      let f : s → DirectSum ι fun n => LinearMap.ker (T n : H n →ₗ[ℂ] Y n) := fun n =>
        DirectSum.lof ℂ ι (fun n => LinearMap.ker (T n : H n →ₗ[ℂ] Y n)) n ⟨(x : lp H 2) n, hmem n⟩
      have hli : LinearIndependent ℂ f := by
        apply LinearIndependent.of_comp
          ((LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2)).subtype.comp
            (kernelAssembly T hM hT))
        have hg : ⇑((LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2)).subtype.comp
            (kernelAssembly T hM hT)) ∘ f = fun n : s => lp.single 2 (n : ι) ((x : lp H 2) n) :=
          funext fun n => kernelAssembly_lof T hM hT n _
        rw [hg]
        refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun n => ?_) fun m n hmn => ?_
        · intro h0
          apply n.2
          have := congrArg (fun z : lp H 2 => (z : ∀ n, H n) n) h0
          simpa [lp.single_apply_self] using this
        · dsimp only
          rw [lp.inner_single_left, lp.single_apply_ne _ _ _ (fun h => hmn (Subtype.ext h)),
            inner_zero_right]
      haveI : Finite s := hli.finite
      exact hinf (Set.toFinite s)
    refine ⟨∑ n ∈ hsupp.toFinset, DirectSum.lof ℂ ι
      (fun n => LinearMap.ker (T n : H n →ₗ[ℂ] Y n)) n
      ⟨(x : lp H 2) n, (mem_ker_blockFormation T hM hT x).1 x.2 n⟩, ?_⟩
    refine Subtype.ext (lp.ext (funext fun m => ?_))
    rw [kernelAssembly_apply, sum_lof_apply]
    split_ifs with hm
    · rfl
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hm
      rw [Submodule.coe_zero, hm]

/-- **`(5.14)`**: `𝐓` has closed range and finite-dimensional kernel iff `inf_n γ(T_n) > 0` and
`Σ_n dim ker T_n < ∞`. -/
theorem blockFormation_upperSemiFredholm_iff :
    (IsClosed (Set.range (blockFormation T hM hT)) ∧
        FiniteDimensional ℂ (LinearMap.ker (blockFormation T hM hT : lp H 2 →ₗ[ℂ] lp Y 2))) ↔
      0 < ⨅ n, reducedMinModulus (T n) ∧
        Cardinal.sum (fun n => Module.rank ℂ (LinearMap.ker (T n : H n →ₗ[ℂ] Y n))) <
          Cardinal.aleph0 := by
  rw [isClosed_range_blockFormation_iff, finiteDimensional_ker_blockFormation_iff]

/-- **`(5.15)`**: for injective blocks with closed range, `sup_n ‖T_n†‖ = (inf_n γ(T_n))⁻¹`, and the
Moore–Penrose inverses assemble to a bounded operator on `⊕_n Y_n` iff `inf_n γ(T_n) > 0`. -/
theorem blockDecoder_iff (hinj : ∀ n, Function.Injective (T n))
    (hcl : ∀ n, IsClosed (Set.range (T n))) :
    (⨆ n, (‖moorePenrose (T n) (hinj n) (hcl n)‖₊ : ℝ≥0∞)) =
        (⨅ n, reducedMinModulus (T n))⁻¹ ∧
      ((∃ L : lp Y 2 →L[ℂ] lp H 2, ∀ y n,
          (L y : ∀ n, H n) n = moorePenrose (T n) (hinj n) (hcl n) ((y : ∀ n, Y n) n)) ↔
        0 < ⨅ n, reducedMinModulus (T n)) := by
  have hsup : (⨆ n, (‖moorePenrose (T n) (hinj n) (hcl n)‖₊ : ℝ≥0∞)) =
      (⨅ n, reducedMinModulus (T n))⁻¹ := by
    rw [ENNReal.inv_iInf]
    exact iSup_congr fun n => nnnorm_moorePenrose_eq (hinj n) (hcl n)
  refine ⟨hsup, ⟨fun ⟨L, hL⟩ => ?_, fun h => ?_⟩⟩
  · have hb : ∀ n, (‖moorePenrose (T n) (hinj n) (hcl n)‖₊ : ℝ≥0∞) ≤ ‖L‖₊ := fun n => by
      rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
      have h1 := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (L (lp.single 2 n w)) n
      rw [hL, lp.single_apply_self] at h1
      refine h1.trans ((L.le_opNorm _).trans ?_)
      rw [lp.norm_single (by norm_num)]
    have h1 : (⨅ n, reducedMinModulus (T n))⁻¹ ≤ ‖L‖₊ := hsup ▸ iSup_le hb
    rw [ENNReal.inv_le_iff_inv_le] at h1
    exact lt_of_lt_of_le (ENNReal.inv_pos.2 ENNReal.coe_ne_top) h1
  · obtain ⟨c, hc, hb⟩ := (pos_iInf_reducedMinModulus_iff T).1 h
    have hn : ∀ n, ‖moorePenrose (T n) (hinj n) (hcl n)‖ ≤ c⁻¹ := fun n =>
      norm_moorePenrose_le (hinj n) (hcl n) hc fun x =>
        hb n x (mem_ker_orthogonal_of_injective (hinj n) x)
    exact ⟨RHTower.rectangularBlockOperator (fun n => moorePenrose (T n) (hinj n) (hcl n))
      (by positivity) hn, fun y n => rfl⟩

omit [DecidableEq ι] in
/-- **`(5.15)`**: the assembled Moore–Penrose decoder inverts the block formation. -/
theorem blockDecoder_comp (hinj : ∀ n, Function.Injective (T n))
    (hcl : ∀ n, IsClosed (Set.range (T n))) (L : lp Y 2 →L[ℂ] lp H 2)
    (hL : ∀ y n, (L y : ∀ n, H n) n = moorePenrose (T n) (hinj n) (hcl n) ((y : ∀ n, Y n) n))
    (x : lp H 2) : L (blockFormation T hM hT x) = x :=
  lp.ext (funext fun n => by rw [hL, blockFormation_apply, moorePenrose_apply_self])

end Block

/-! ### Unitary and permutation covariance of the block conditions -/

section Covariance

theorem cardinal_sum_comp_equiv {ι : Type*} (σ : ι ≃ ι) (f : ι → Cardinal) :
    Cardinal.sum (fun n => f (σ n)) = Cardinal.sum f := by
  simp only [Cardinal.sum]
  exact Cardinal.mk_congr (Equiv.sigmaCongrLeft (β := fun i => Quotient.out (f i)) σ)

variable {E E' : Type uH} {F F' : Type uY} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- Unitary conjugation preserves the reduced minimum modulus and the kernel dimension. -/
theorem reducedMinModulus_conj (T : E →L[ℂ] F) (T' : E' →L[ℂ] F') (V : E ≃ₗᵢ[ℂ] E')
    (U : F ≃ₗᵢ[ℂ] F') (h : ∀ x, T' (V x) = U (T x)) :
    reducedMinModulus T' = reducedMinModulus T ∧
      Module.rank ℂ (LinearMap.ker (T' : E' →ₗ[ℂ] F')) =
        Module.rank ℂ (LinearMap.ker (T : E →ₗ[ℂ] F)) := by
  have hker : ∀ x', x' ∈ LinearMap.ker (T' : E' →ₗ[ℂ] F') ↔
      V.symm x' ∈ LinearMap.ker (T : E →ₗ[ℂ] F) := fun x' => by
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    change T' x' = 0 ↔ T (V.symm x') = 0
    rw [← V.apply_symm_apply x', h, V.symm_apply_apply, LinearIsometryEquiv.map_eq_zero_iff]
  have horth : ∀ x, V x ∈ (LinearMap.ker (T' : E' →ₗ[ℂ] F'))ᗮ ↔
      x ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ := fun x => by
    rw [Submodule.mem_orthogonal, Submodule.mem_orthogonal]
    constructor
    · intro hx k hk
      have := hx (V k) ((hker _).2 (by rwa [V.symm_apply_apply]))
      rwa [LinearIsometryEquiv.inner_map_map] at this
    · intro hx k' hk'
      have := hx _ ((hker k').1 hk')
      rwa [← LinearIsometryEquiv.inner_map_map V, V.apply_symm_apply] at this
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine le_iInf₂ fun x hx => le_iInf fun hx1 => ?_
    refine (iInf₂_le (V x) ((horth x).2 hx)).trans (iInf_le_of_le (by rw [V.norm_map, hx1]) ?_)
    rw [h, LinearIsometryEquiv.nnnorm_map]
  · refine le_iInf₂ fun x' hx' => le_iInf fun hx1 => ?_
    have hx : V.symm x' ∈ (LinearMap.ker (T : E →ₗ[ℂ] F))ᗮ := by
      rw [← horth, V.apply_symm_apply]
      exact hx'
    refine (iInf₂_le (V.symm x') hx).trans (iInf_le_of_le (by rw [V.symm.norm_map, hx1]) ?_)
    rw [← LinearIsometryEquiv.nnnorm_map U, ← h, V.apply_symm_apply]
  · have hmap : (LinearMap.ker (T : E →ₗ[ℂ] F)).map (V.toLinearEquiv : E →ₗ[ℂ] E') =
        LinearMap.ker (T' : E' →ₗ[ℂ] F') := by
      ext x'
      rw [Submodule.mem_map_equiv, hker]
      rfl
    exact (LinearEquiv.ofSubmodules V.toLinearEquiv _ _ hmap).rank_eq.symm

/-- **§5–§7 covariance**: unitarily conjugating and permuting the blocks preserves both the uniform
gap `inf_n γ(T_n) > 0` and the finite exceptional multiplicity `Σ_n dim ker T_n < ∞`. -/
theorem blockConditions_conj {ι : Type*} (σ : ι ≃ ι) {H H' : ι → Type uH} {Y Y' : ι → Type uY}
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, NormedAddCommGroup (H' n)] [∀ n, InnerProductSpace ℂ (H' n)]
    [∀ n, NormedAddCommGroup (Y n)] [∀ n, InnerProductSpace ℂ (Y n)]
    [∀ n, NormedAddCommGroup (Y' n)] [∀ n, InnerProductSpace ℂ (Y' n)]
    (T : ∀ n, H n →L[ℂ] Y n) (T' : ∀ n, H' n →L[ℂ] Y' n) (V : ∀ n, H n ≃ₗᵢ[ℂ] H' (σ n))
    (U : ∀ n, Y n ≃ₗᵢ[ℂ] Y' (σ n)) (h : ∀ n x, T' (σ n) (V n x) = U n (T n x)) :
    (0 < ⨅ m, reducedMinModulus (T' m) ∧
        Cardinal.sum (fun m => Module.rank ℂ (LinearMap.ker (T' m : H' m →ₗ[ℂ] Y' m))) <
          Cardinal.aleph0) ↔
      (0 < ⨅ n, reducedMinModulus (T n) ∧
        Cardinal.sum (fun n => Module.rank ℂ (LinearMap.ker (T n : H n →ₗ[ℂ] Y n))) <
          Cardinal.aleph0) := by
  have hγ : ⨅ m, reducedMinModulus (T' m) = ⨅ n, reducedMinModulus (T n) := by
    rw [← σ.iInf_comp (g := fun m => reducedMinModulus (T' m))]
    exact iInf_congr fun n => (reducedMinModulus_conj (T n) (T' (σ n)) (V n) (U n) (h n)).1
  have hd : Cardinal.sum (fun m => Module.rank ℂ (LinearMap.ker (T' m : H' m →ₗ[ℂ] Y' m))) =
      Cardinal.sum (fun n => Module.rank ℂ (LinearMap.ker (T n : H n →ₗ[ℂ] Y n))) := by
    rw [← cardinal_sum_comp_equiv σ]
    exact congrArg Cardinal.sum (funext fun n =>
      (reducedMinModulus_conj (T n) (T' (σ n)) (V n) (U n) (h n)).2)
  rw [hγ, hd]

end Covariance

end GaloisForLFunctions.HTGeometry.TightFormation
