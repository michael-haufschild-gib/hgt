import GaloisForLFunctions.HTGeometry.KSGNSPositiveKernel
import Mathlib.Analysis.CStarAlgebra.Module.Constructions

open scoped CStarAlgebra

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {A B : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The canonical B-valued KSGNS sesquilinear form on the algebraic free module. -/
def ksgnsPreInner (phi : A →CP B) (x y : A →₀ B) : B :=
  x.sum fun a b => y.sum fun c d => star b * phi (star a * c) * d

@[simp]
theorem ksgnsPreInner_single_single (phi : A →CP B) (a c : A) (b d : B) :
    ksgnsPreInner phi (Finsupp.single a b) (Finsupp.single c d) =
      star b * phi (star a * c) * d := by
  classical
  simp [ksgnsPreInner]

theorem ksgnsPreInner_self_eq_cpGramQuadratic (phi : A →CP B) (x : A →₀ B) :
    ksgnsPreInner phi x x =
      cpGramQuadratic phi (fun i : x.support => (i : A)) (fun i : x.support => x i) := by
  classical
  change (∑ a ∈ x.support, ∑ c ∈ x.support,
      star (x a) * phi (star a * c) * x c) =
    ∑ i : x.support, ∑ j : x.support,
      star (x i) * phi (star (i : A) * (j : A)) * x j
  rw [Finset.sum_subtype x.support (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_subtype x.support (fun _ => Iff.rfl)]

theorem ksgnsPreInner_self_nonneg (phi : A →CP B) (x : A →₀ B) :
    0 ≤ ksgnsPreInner phi x x := by
  rw [ksgnsPreInner_self_eq_cpGramQuadratic]
  exact cpGramQuadratic_nonneg phi _ _

/-- Pointwise right multiplication on the free KSGNS module. -/
def ksgnsPreRmul (x : A →₀ B) (b : B) : A →₀ B :=
  x.mapRange (fun c => c * b) (zero_mul b)

@[simp]
theorem ksgnsPreRmul_apply (x : A →₀ B) (b : B) (a : A) :
    ksgnsPreRmul x b a = x a * b := by
  classical
  simp [ksgnsPreRmul]

@[simp]
theorem ksgnsPreRmul_single (a : A) (b c : B) :
    ksgnsPreRmul (Finsupp.single a b) c = Finsupp.single a (b * c) := by
  classical
  ext q
  by_cases h : a = q
  · subst q
    simp [ksgnsPreRmul_apply]
  · simp [ksgnsPreRmul_apply, h]

theorem ksgnsPreInner_add_right (phi : A →CP B) (x y z : A →₀ B) :
    ksgnsPreInner phi x (y + z) = ksgnsPreInner phi x y + ksgnsPreInner phi x z := by
  classical
  change (∑ a ∈ x.support, (y + z).sum fun c d =>
      star (x a) * phi (star a * c) * d) =
    (∑ a ∈ x.support, y.sum fun c d => star (x a) * phi (star a * c) * d) +
    ∑ a ∈ x.support, z.sum fun c d => star (x a) * phi (star a * c) * d
  have hinner : ∀ a : A,
      (y + z).sum (fun c d => star (x a) * phi (star a * c) * d) =
        y.sum (fun c d => star (x a) * phi (star a * c) * d) +
        z.sum (fun c d => star (x a) * phi (star a * c) * d) := by
    intro a
    rw [Finsupp.sum_add_index]
    · intro c _
      simp
    · intro c _ d e
      simp [mul_add]
  simp_rw [hinner]
  exact Finset.sum_add_distrib

theorem ksgnsPreInner_smul_right (phi : A →CP B) (c : ℂ) (x y : A →₀ B) :
    ksgnsPreInner phi x (c • y) = c • ksgnsPreInner phi x y := by
  classical
  change (∑ a ∈ x.support, (c • y).sum fun q d =>
      star (x a) * phi (star a * q) * d) =
    c • ∑ a ∈ x.support, y.sum fun q d =>
      star (x a) * phi (star a * q) * d
  have hinner : ∀ a : A,
      (c • y).sum (fun q d => star (x a) * phi (star a * q) * d) =
        c • y.sum (fun q d => star (x a) * phi (star a * q) * d) := by
    intro a
    let kernel : A → B → B := fun q d => star (x a) * phi (star a * q) * d
    have hadd (u v : A →₀ B) :
        (u + v).sum kernel = u.sum kernel + v.sum kernel := by
      rw [Finsupp.sum_add_index]
      · intro q _
        simp [kernel]
      · intro q _ d e
        simp [kernel, mul_add]
    induction y using Finsupp.induction_linear with
    | zero => simp [kernel]
    | add u v hu hv =>
        rw [smul_add, hadd, hadd, hu, hv, smul_add]
    | single q d =>
        rw [Finsupp.smul_single]
        simp [kernel, mul_smul_comm]
  simp_rw [hinner]
  exact Finset.smul_sum.symm

theorem ksgnsPreInner_rmul_right (phi : A →CP B) (x y : A →₀ B) (b : B) :
    ksgnsPreInner phi x (ksgnsPreRmul y b) = ksgnsPreInner phi x y * b := by
  classical
  change (∑ a ∈ x.support, (ksgnsPreRmul y b).sum fun c d =>
      star (x a) * phi (star a * c) * d) =
    (∑ a ∈ x.support, y.sum fun c d =>
      star (x a) * phi (star a * c) * d) * b
  have hinner : ∀ a : A,
      (ksgnsPreRmul y b).sum (fun c d => star (x a) * phi (star a * c) * d) =
        y.sum (fun c d => star (x a) * phi (star a * c) * d) * b := by
    intro a
    unfold ksgnsPreRmul
    rw [Finsupp.sum_mapRange_index]
    rw [Finsupp.sum_mul]
    apply Finsupp.sum_congr
    intro c hc
    simp [mul_assoc]
    · intro q
      simp
  simp_rw [hinner]
  rw [Finset.sum_mul]

theorem ksgnsPreInner_star (phi : A →CP B) (x y : A →₀ B) :
    star (ksgnsPreInner phi x y) = ksgnsPreInner phi y x := by
  classical
  change star (∑ a ∈ x.support, ∑ c ∈ y.support,
      star (x a) * phi (star a * c) * y c) =
    ∑ c ∈ y.support, ∑ a ∈ x.support,
      star (y c) * phi (star c * a) * x a
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [← map_star phi]
  simp [mul_assoc]

/-- Exact algebraic right-inner-module structure on the KSGNS free module. -/
def ksgnsPreModuleData (phi : A →CP B) : RightInnerModuleData B (A →₀ B) where
  inner := ksgnsPreInner phi
  rmul := ksgnsPreRmul
  inner_add_right := ksgnsPreInner_add_right phi
  inner_smul_right := ksgnsPreInner_smul_right phi
  inner_rmul_right := ksgnsPreInner_rmul_right phi
  star_inner := ksgnsPreInner_star phi
  rmul_one := by
    intro x
    ext a
    simp [ksgnsPreRmul_apply]
  rmul_mul := by
    intro x b c
    ext a
    simp [ksgnsPreRmul_apply, mul_assoc]
  rmul_add_left := by
    intro x y b
    ext a
    simp [ksgnsPreRmul_apply, add_mul]
  rmul_add_right := by
    intro x b c
    ext a
    simp [ksgnsPreRmul_apply, mul_add]
  rmul_smul := by
    intro c x b
    ext a
    simp [ksgnsPreRmul_apply, smul_mul_assoc]

theorem ksgnsPreInner_null_left (phi : A →CP B) {x : A →₀ B}
    (hxx : ksgnsPreInner phi x x = 0) (y : A →₀ B) :
    ksgnsPreInner phi x y = 0 := by
  let M := ksgnsPreModuleData phi
  let d : B := M.inner x y
  let c : B := M.inner y y
  change M.inner x x = 0 at hxx
  by_contra hd
  have hdpos : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  let r : ℝ := ‖d‖ ^ 2 / (‖c‖ + 1)
  have hr : 0 < r := div_pos hdpos (by positivity)
  let z : A →₀ B := M.rmul x d - (r : ℂ) • y
  have hzpos : 0 ≤ M.inner z z := ksgnsPreInner_self_nonneg phi z
  have inner_smul_left (q : ℂ) (u v : A →₀ B) :
      M.inner (q • u) v = star q • M.inner u v := by
    rw [← M.star_inner, M.inner_smul_right, star_smul, M.star_inner]
  have hform : M.inner z z =
      (r ^ 2 : ℝ) • c - (2 * r : ℝ) • (star d * d) := by
    dsimp only [z]
    rw [M.inner_sub_left, M.inner_sub_right, M.inner_sub_right]
    simp_rw [M.inner_rmul_left, M.inner_rmul_right,
      inner_smul_left, M.inner_smul_right]
    rw [hxx]
    have hyx : M.inner y x = star d := by
      exact (M.star_inner x y).symm
    rw [hyx]
    have hdxy : M.inner x y = d := rfl
    have hcyy : M.inner y y = c := rfl
    rw [hdxy, hcyy]
    have hsr : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    rw [hsr]
    simp only [zero_mul, smul_smul]
    push_cast
    simp only [mul_zero, mul_smul_comm, smul_mul_assoc]
    push_cast
    module
  have hle : (2 * r : ℝ) • (star d * d) ≤ (r ^ 2 : ℝ) • c := by
    rw [hform] at hzpos
    exact sub_nonneg.mp hzpos
  have hleft : 0 ≤ (2 * r : ℝ) • (star d * d) :=
    smul_nonneg (by positivity) (star_mul_self_nonneg d)
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le hleft hle
  have hstar : ‖star d * d‖ = ‖d‖ ^ 2 := by
    rw [CStarRing.norm_star_mul_self]
    ring
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * r), abs_of_pos (sq_pos_of_pos hr), hstar] at hnorm
  have hrv : r * ‖c‖ < ‖d‖ ^ 2 := by
    dsimp [r]
    have hv : ‖c‖ / (‖c‖ + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    rw [div_mul_eq_mul_div]
    calc
      ‖d‖ ^ 2 * ‖c‖ / (‖c‖ + 1) = ‖d‖ ^ 2 * (‖c‖ / (‖c‖ + 1)) := by ring
      _ < ‖d‖ ^ 2 * 1 := mul_lt_mul_of_pos_left hv hdpos
      _ = ‖d‖ ^ 2 := mul_one _
  have hbound : 2 * ‖d‖ ^ 2 ≤ r * ‖c‖ := by
    nlinarith [hnorm]
  nlinarith

theorem ksgnsPreInner_add_left (phi : A →CP B) (x y z : A →₀ B) :
    ksgnsPreInner phi (x + y) z =
      ksgnsPreInner phi x z + ksgnsPreInner phi y z :=
  (ksgnsPreModuleData phi).inner_add_left x y z

theorem ksgnsPreInner_sub_left (phi : A →CP B) (x y z : A →₀ B) :
    ksgnsPreInner phi (x - y) z =
      ksgnsPreInner phi x z - ksgnsPreInner phi y z :=
  (ksgnsPreModuleData phi).inner_sub_left x y z

theorem ksgnsPreInner_sub_right (phi : A →CP B) (x y z : A →₀ B) :
    ksgnsPreInner phi x (y - z) =
      ksgnsPreInner phi x y - ksgnsPreInner phi x z :=
  (ksgnsPreModuleData phi).inner_sub_right x y z

theorem ksgnsPreInner_smul_left (phi : A →CP B) (q : ℂ) (x y : A →₀ B) :
    ksgnsPreInner phi (q • x) y = star q • ksgnsPreInner phi x y := by
  rw [← ksgnsPreInner_star, ksgnsPreInner_smul_right, star_smul,
    ksgnsPreInner_star]

theorem ksgnsPreInner_rmul_left (phi : A →CP B) (x y : A →₀ B) (b : B) :
    ksgnsPreInner phi (ksgnsPreRmul x b) y =
      star b * ksgnsPreInner phi x y :=
  (ksgnsPreModuleData phi).inner_rmul_left x y b

/-- Null radical of the positive KSGNS form. -/
def ksgnsPreRadical (phi : A →CP B) : Submodule ℂ (A →₀ B) where
  carrier := {x | ∀ y, ksgnsPreInner phi x y = 0}
  zero_mem' := by
    intro y
    exact (ksgnsPreModuleData phi).inner_zero_left y
  add_mem' := by
    intro x y hx hy z
    rw [ksgnsPreInner_add_left, hx z, hy z, add_zero]
  smul_mem' := by
    intro q x hx y
    rw [ksgnsPreInner_smul_left, hx y]
    simp

theorem mem_ksgnsPreRadical_iff_inner_self_eq_zero (phi : A →CP B) (x : A →₀ B) :
    x ∈ ksgnsPreRadical phi ↔ ksgnsPreInner phi x x = 0 := by
  constructor
  · intro hx
    exact hx x
  · intro hx y
    exact ksgnsPreInner_null_left phi hx y

/-- Separated algebraic KSGNS module, before Hilbert-module completion. -/
abbrev KSGNSSeparated (phi : A →CP B) := (A →₀ B) ⧸ ksgnsPreRadical phi

/-- The B-valued inner product descended to the separated KSGNS quotient. -/
def ksgnsSeparatedInner (phi : A →CP B) (u v : KSGNSSeparated phi) : B :=
  Quotient.liftOn₂ u v (ksgnsPreInner phi) (by
    intro x y x' y' hx hy
    have hxeq : Submodule.Quotient.mk x =
        (Submodule.Quotient.mk x' : KSGNSSeparated phi) := by
      exact Quotient.sound hx
    have hyeq : Submodule.Quotient.mk y =
        (Submodule.Quotient.mk y' : KSGNSSeparated phi) := by
      exact Quotient.sound hy
    have hxmem : x - x' ∈ ksgnsPreRadical phi :=
      (Submodule.Quotient.eq (ksgnsPreRadical phi)).mp hxeq
    have hymem : y - y' ∈ ksgnsPreRadical phi :=
      (Submodule.Quotient.eq (ksgnsPreRadical phi)).mp hyeq
    have hx0 : ksgnsPreInner phi (x - x') y = 0 := hxmem y
    have hy0left : ksgnsPreInner phi (y - y') x' = 0 := hymem x'
    have hy0 : ksgnsPreInner phi x' (y - y') = 0 := by
      rw [← star_eq_zero, ksgnsPreInner_star]
      exact hy0left
    have hxEq : ksgnsPreInner phi x y = ksgnsPreInner phi x' y := by
      rw [ksgnsPreInner_sub_left] at hx0
      exact sub_eq_zero.mp hx0
    have hyEq : ksgnsPreInner phi x' y = ksgnsPreInner phi x' y' := by
      rw [ksgnsPreInner_sub_right] at hy0
      exact sub_eq_zero.mp hy0
    exact hxEq.trans hyEq)

@[simp]
theorem ksgnsSeparatedInner_mk (phi : A →CP B) (x y : A →₀ B) :
    ksgnsSeparatedInner phi (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      ksgnsPreInner phi x y := rfl

/-- Right multiplication as a complex-linear map on the free KSGNS module. -/
def ksgnsPreRmulLinear (b : B) : (A →₀ B) →ₗ[ℂ] (A →₀ B) where
  toFun x := ksgnsPreRmul x b
  map_add' := by
    intro x y
    ext a
    simp [ksgnsPreRmul_apply, add_mul]
  map_smul' := by
    intro q x
    ext a
    simp [ksgnsPreRmul_apply]

theorem ksgnsPreRmul_mem_radical (phi : A →CP B) (b : B) {x : A →₀ B}
    (hx : x ∈ ksgnsPreRadical phi) :
    ksgnsPreRmul x b ∈ ksgnsPreRadical phi := by
  intro y
  rw [ksgnsPreInner_rmul_left, hx y, mul_zero]

/-- Right multiplication descended to the separated quotient. -/
def ksgnsSeparatedRmul (phi : A →CP B) (b : B) :
    KSGNSSeparated phi →ₗ[ℂ] KSGNSSeparated phi :=
  (ksgnsPreRadical phi).mapQ (ksgnsPreRadical phi) (ksgnsPreRmulLinear b) (by
    intro x hx
    exact ksgnsPreRmul_mem_radical phi b hx)

@[simp]
theorem ksgnsSeparatedRmul_mk (phi : A →CP B) (b : B) (x : A →₀ B) :
    ksgnsSeparatedRmul phi b (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ksgnsPreRmul x b) := by
  exact Submodule.mapQ_apply _ _ _ _

instance ksgnsSeparatedSMul (phi : A →CP B) :
    SMul Bᵐᵒᵖ (KSGNSSeparated phi) where
  smul b x := ksgnsSeparatedRmul phi (MulOpposite.unop b) x

@[simp]
theorem ksgnsSeparated_op_smul_mk (phi : A →CP B) (b : B) (x : A →₀ B) :
    MulOpposite.op b • (Submodule.Quotient.mk x : KSGNSSeparated phi) =
      Submodule.Quotient.mk (ksgnsPreRmul x b) := by
  exact ksgnsSeparatedRmul_mk phi b x

instance ksgnsSeparatedInnerInstance (phi : A →CP B) :
    Inner Bᵐᵒᵖ (KSGNSSeparated phi) where
  inner x y := MulOpposite.op (ksgnsSeparatedInner phi x y)

open scoped InnerProductSpace

@[simp]
theorem ksgnsSeparated_inner_mk (phi : A →CP B) (x y : A →₀ B) :
    ⟪(Submodule.Quotient.mk x : KSGNSSeparated phi), Submodule.Quotient.mk y⟫_Bᵐᵒᵖ =
      MulOpposite.op (ksgnsPreInner phi x y) := rfl

instance ksgnsSeparatedNorm (phi : A →CP B) : Norm (KSGNSSeparated phi) where
  norm x := Real.sqrt ‖ksgnsSeparatedInner phi x x‖

/-- The separated algebraic KSGNS quotient is a genuine (not yet complete) Hilbert C⋆-module over
the opposite coefficient algebra, which is the standard encoding of its right `B`-action. -/
instance ksgnsSeparatedCStarModule (phi : A →CP B) :
    CStarModule Bᵐᵒᵖ (KSGNSSeparated phi) where
  inner_add_right := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ x y z =>
      change MulOpposite.op (ksgnsPreInner phi x (y + z)) =
        MulOpposite.op (ksgnsPreInner phi x y) + MulOpposite.op (ksgnsPreInner phi x z)
      rw [ksgnsPreInner_add_right]
      rfl
  inner_self_nonneg := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      change 0 ≤ MulOpposite.op (ksgnsPreInner phi x x)
      rw [MulOpposite.op_nonneg]
      exact ksgnsPreInner_self_nonneg phi x
  inner_self := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      constructor
      · intro hx
        have hx0 : ksgnsPreInner phi x x = 0 := by
          change MulOpposite.op (ksgnsPreInner phi x x) = 0 at hx
          have hu := congrArg MulOpposite.unop hx
          change ksgnsPreInner phi x x = 0 at hu
          exact hu
        change Submodule.Quotient.mk x = Submodule.Quotient.mk 0
        rw [Submodule.Quotient.eq]
        rw [sub_zero]
        exact (mem_ksgnsPreRadical_iff_inner_self_eq_zero phi x).2 hx0
      · intro hx
        rw [hx]
        change MulOpposite.op (ksgnsPreInner phi 0 0) = 0
        change MulOpposite.op (0 : B) = 0
        rfl
  inner_op_smul_right := by
    intro b x y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op
          (ksgnsPreInner phi x (ksgnsPreRmul y (MulOpposite.unop b))) =
        b * MulOpposite.op (ksgnsPreInner phi x y)
      rw [ksgnsPreInner_rmul_right]
      rfl
  inner_smul_right_complex := by
    intro q x y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op (ksgnsPreInner phi x (q • y)) =
        q • MulOpposite.op (ksgnsPreInner phi x y)
      rw [ksgnsPreInner_smul_right]
      rfl
  star_inner := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op (star (ksgnsPreInner phi x y)) =
        MulOpposite.op (ksgnsPreInner phi y x)
      rw [ksgnsPreInner_star]
  norm_eq_sqrt_norm_inner_self := by
    intro x
    change Real.sqrt ‖ksgnsSeparatedInner phi x x‖ =
      Real.sqrt ‖MulOpposite.op (ksgnsSeparatedInner phi x x)‖
    rw [MulOpposite.norm_op]

noncomputable instance ksgnsSeparatedNormedAddCommGroup (phi : A →CP B) :
    NormedAddCommGroup (KSGNSSeparated phi) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore Bᵐᵒᵖ)

noncomputable instance ksgnsSeparatedNormedSpace (phi : A →CP B) :
    NormedSpace ℂ (KSGNSSeparated phi) :=
  NormedSpace.ofCore (CStarModule.normedSpaceCore Bᵐᵒᵖ)

/-- Completed canonical Paschke--KSGNS Hilbert-module carrier. -/
abbrev KSGNS (phi : A →CP B) := UniformSpace.Completion (KSGNSSeparated phi)

section CompletionExtension

open UniformSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {σ : ℂ →+* ℂ} [RingHomIsometric σ]

/-- Continuous semilinear extension from a normed space to its completion. -/
noncomputable def completionExtendSL (f : E →SL[σ] F) : Completion E →SL[σ] F where
  toFun := Completion.extension (f : E → F)
  map_add' := by
    intro x y
    refine Completion.induction_on₂ x y ?_ ?_
    · refine isClosed_eq ?_ ?_
      · exact Completion.continuous_extension.comp continuous_add
      · exact (Completion.continuous_extension.comp continuous_fst).add
          (Completion.continuous_extension.comp continuous_snd)
    · intro a b
      rw [← Completion.coe_add,
        Completion.extension_coe f.uniformContinuous,
        Completion.extension_coe f.uniformContinuous,
        Completion.extension_coe f.uniformContinuous, map_add]
  map_smul' := by
    intro q x
    refine Completion.induction_on x ?_ ?_
    · refine isClosed_eq ?_ ?_
      · exact Completion.continuous_extension.comp (continuous_const_smul q)
      · exact (continuous_const_smul (σ q)).comp Completion.continuous_extension
    · intro a
      rw [← Completion.coe_smul,
        Completion.extension_coe f.uniformContinuous,
        Completion.extension_coe f.uniformContinuous, f.map_smulₛₗ]
  cont := Completion.continuous_extension

@[simp]
theorem completionExtendSL_coe (f : E →SL[σ] F) (x : E) :
    completionExtendSL f (x : Completion E) = f x :=
  Completion.extension_coe f.uniformContinuous x

/-- Canonical complex-linear isometry into the uniform completion. -/
noncomputable def completionCoeLinearIsometry : E →ₗᵢ[ℂ] Completion E where
  toLinearMap :=
    { toFun := fun x => (x : Completion E)
      map_add' := fun x y => Completion.coe_add x y
      map_smul' := fun q x => Completion.coe_smul q x }
  norm_map' := Completion.norm_coe

end CompletionExtension

section KSGNSCompletion

open UniformSpace

variable (phi : A →CP B)

/-- Algebraic sesquilinear inner-product map on the separated KSGNS module. -/
def ksgnsSeparatedInnerLM :
    KSGNSSeparated phi →ₗ⋆[ℂ] KSGNSSeparated phi →ₗ[ℂ] Bᵐᵒᵖ where
  toFun x :=
    { toFun := fun y => MulOpposite.op (ksgnsSeparatedInner phi x y)
      map_add' := by
        intro y z
        induction x, y, z using Quotient.inductionOn₃ with
        | _ x y z =>
          change MulOpposite.op (ksgnsPreInner phi x (y + z)) =
            MulOpposite.op (ksgnsPreInner phi x y) +
              MulOpposite.op (ksgnsPreInner phi x z)
          rw [ksgnsPreInner_add_right]
          rfl
      map_smul' := by
        intro q y
        induction x, y using Quotient.inductionOn₂ with
        | _ x y =>
          change MulOpposite.op (ksgnsPreInner phi x (q • y)) =
            q • MulOpposite.op (ksgnsPreInner phi x y)
          rw [ksgnsPreInner_smul_right]
          rfl }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ x y z =>
      change MulOpposite.op (ksgnsPreInner phi (x + y) z) =
        MulOpposite.op (ksgnsPreInner phi x z) +
          MulOpposite.op (ksgnsPreInner phi y z)
      rw [ksgnsPreInner_add_left]
      rfl
  map_smul' := by
    intro q x
    apply LinearMap.ext
    intro y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op (ksgnsPreInner phi (q • x) y) =
        starRingEnd ℂ q • MulOpposite.op (ksgnsPreInner phi x y)
      rw [ksgnsPreInner_smul_left]
      rfl

/-- Inner product continuous in its second variable. -/
noncomputable def ksgnsSeparatedInnerRightCLM (x : KSGNSSeparated phi) :
    KSGNSSeparated phi →L[ℂ] Bᵐᵒᵖ :=
  (ksgnsSeparatedInnerLM phi x).mkContinuous ‖x‖ (by
    intro y
    exact CStarModule.norm_inner_le (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi))

/-- Algebraic conjugate-linear dependence of the continuous second-variable map. -/
def ksgnsSeparatedInnerRightLM :
    KSGNSSeparated phi →ₛₗ[starRingEnd ℂ]
      (KSGNSSeparated phi →L[ℂ] Bᵐᵒᵖ) where
  toFun := ksgnsSeparatedInnerRightCLM phi
  map_add' := by
    intro x y
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun (map_add (ksgnsSeparatedInnerLM phi) x y) z
  map_smul' := by
    intro q x
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun ((ksgnsSeparatedInnerLM phi).map_smulₛₗ q x) y

set_option maxHeartbeats 1000000 in
theorem norm_ksgnsSeparated_inner_le (x y : KSGNSSeparated phi) :
    ‖MulOpposite.op (ksgnsSeparatedInner phi x y)‖ ≤ ‖x‖ * ‖y‖ := by
  exact CStarModule.norm_inner_le (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi)

noncomputable def ksgnsSeparatedInnerSLM :
    KSGNSSeparated phi →SL[starRingEnd ℂ]
      KSGNSSeparated phi →L[ℂ] Bᵐᵒᵖ :=
  CStarModule.innerSL (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi)

@[simp]
theorem ksgnsSeparatedInnerSLM_apply (x y : KSGNSSeparated phi) :
    ksgnsSeparatedInnerSLM phi x y = ⟪x, y⟫_Bᵐᵒᵖ := rfl

/-- Extend the second variable of the KSGNS inner product to the completion. -/
noncomputable def ksgnsInnerRightCompletion (x : KSGNSSeparated phi) :
    KSGNS phi →L[ℂ] Bᵐᵒᵖ :=
  completionExtendSL (ksgnsSeparatedInnerSLM phi x)

@[simp]
theorem ksgnsInnerRightCompletion_coe (x y : KSGNSSeparated phi) :
    ksgnsInnerRightCompletion phi x (y : KSGNS phi) = ⟪x, y⟫_Bᵐᵒᵖ := by
  rw [ksgnsInnerRightCompletion, completionExtendSL_coe]
  rfl

theorem norm_ksgnsInnerRightCompletion_le (x : KSGNSSeparated phi) :
    ‖ksgnsInnerRightCompletion phi x‖ ≤ ‖x‖ := by
  apply (ksgnsInnerRightCompletion phi x).opNorm_le_bound
    (CStarModule.norm_nonneg Bᵐᵒᵖ)
  intro y
  refine Completion.induction_on y ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp (ksgnsInnerRightCompletion phi x).continuous)
      (continuous_const.mul continuous_norm)
  · intro y
    rw [ksgnsInnerRightCompletion_coe, Completion.norm_coe]
    exact CStarModule.norm_inner_le (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi)

/-- Conjugate-linear dependence of the completed second-variable inner map. -/
noncomputable def ksgnsInnerLeftLM :
    KSGNSSeparated phi →ₛₗ[starRingEnd ℂ]
      (KSGNS phi →L[ℂ] Bᵐᵒᵖ) where
  toFun := ksgnsInnerRightCompletion phi
  map_add' := by
    intro x y
    apply ContinuousLinearMap.ext
    intro z
    refine Completion.induction_on z ?_ ?_
    · exact isClosed_eq (ksgnsInnerRightCompletion phi (x + y)).continuous
        ((ksgnsInnerRightCompletion phi x).continuous.add
          (ksgnsInnerRightCompletion phi y).continuous)
    · intro z
      change ksgnsInnerRightCompletion phi (x + y) (z : KSGNS phi) =
        ksgnsInnerRightCompletion phi x (z : KSGNS phi) +
          ksgnsInnerRightCompletion phi y (z : KSGNS phi)
      rw [ksgnsInnerRightCompletion_coe, ksgnsInnerRightCompletion_coe,
        ksgnsInnerRightCompletion_coe]
      change ⟪x + y, z⟫_Bᵐᵒᵖ = ⟪x, z⟫_Bᵐᵒᵖ + ⟪y, z⟫_Bᵐᵒᵖ
      exact CStarModule.inner_add_left (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi)
        (x := x) (y := y) (z := z)
  map_smul' := by
    intro q x
    apply ContinuousLinearMap.ext
    intro y
    refine Completion.induction_on y ?_ ?_
    · exact isClosed_eq (ksgnsInnerRightCompletion phi (q • x)).continuous
        ((continuous_const_smul (starRingEnd ℂ q)).comp
          (ksgnsInnerRightCompletion phi x).continuous)
    · intro y
      change ksgnsInnerRightCompletion phi (q • x) (y : KSGNS phi) =
        starRingEnd ℂ q • ksgnsInnerRightCompletion phi x (y : KSGNS phi)
      rw [ksgnsInnerRightCompletion_coe, ksgnsInnerRightCompletion_coe]
      change ⟪q • x, y⟫_Bᵐᵒᵖ =
        starRingEnd ℂ q • ⟪x, y⟫_Bᵐᵒᵖ
      exact CStarModule.inner_smul_left_complex (A := Bᵐᵒᵖ)
        (E := KSGNSSeparated phi) (z := q) (x := x) (y := y)

/-- Continuous first-variable map after completing the second variable. -/
noncomputable def ksgnsInnerLeftSLM :
    KSGNSSeparated phi →SL[starRingEnd ℂ]
      (KSGNS phi →L[ℂ] Bᵐᵒᵖ) :=
  (ksgnsInnerLeftLM phi).mkContinuous 1 (by
    intro x
    change ‖ksgnsInnerRightCompletion phi x‖ ≤ 1 * ‖x‖
    simpa using norm_ksgnsInnerRightCompletion_le phi x)

/-- Completed B-valued KSGNS inner product, continuous in both variables. -/
noncomputable def ksgnsCompletedInnerSLM :
    KSGNS phi →SL[starRingEnd ℂ] (KSGNS phi →L[ℂ] Bᵐᵒᵖ) :=
  completionExtendSL (ksgnsInnerLeftSLM phi)

@[simp]
theorem ksgnsCompletedInnerSLM_coe (x : KSGNSSeparated phi) :
    ksgnsCompletedInnerSLM phi (x : KSGNS phi) = ksgnsInnerRightCompletion phi x := by
  rw [ksgnsCompletedInnerSLM, completionExtendSL_coe]
  rfl

@[simp]
theorem ksgnsCompletedInnerSLM_coe_coe (x y : KSGNSSeparated phi) :
    ksgnsCompletedInnerSLM phi (x : KSGNS phi) (y : KSGNS phi) =
      ⟪x, y⟫_Bᵐᵒᵖ := by
  rw [ksgnsCompletedInnerSLM_coe, ksgnsInnerRightCompletion_coe]

theorem norm_ksgnsSeparated_op_smul_le (b : Bᵐᵒᵖ) (x : KSGNSSeparated phi) :
    ‖b • x‖ ≤ ‖b‖ * ‖x‖ := by
  rw [← sq_le_sq₀ (CStarModule.norm_nonneg Bᵐᵒᵖ) (mul_nonneg (norm_nonneg b) (norm_nonneg x))]
  rw [CStarModule.norm_sq_eq (A := Bᵐᵒᵖ), mul_pow]
  calc
    ‖⟪b • x, b • x⟫_Bᵐᵒᵖ‖ =
        ‖b * ⟪x, x⟫_Bᵐᵒᵖ * star b‖ := by
          rw [CStarModule.inner_op_smul_left
                (A := Bᵐᵒᵖ) (a := b) (x := x) (y := b • x),
              CStarModule.inner_op_smul_right
                (A := Bᵐᵒᵖ) (a := b) (x := x) (y := x)]
    _ ≤ ‖b‖ * ‖⟪x, x⟫_Bᵐᵒᵖ‖ * ‖star b‖ := by
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖b‖ ^ 2 * ‖x‖ ^ 2 := by
          have hxnorm : ‖⟪x, x⟫_Bᵐᵒᵖ‖ = ‖x‖ ^ 2 :=
            (CStarModule.norm_sq_eq (A := Bᵐᵒᵖ) (x := x)).symm
          rw [norm_star, hxnorm]
          ring

/-- Bounded coefficient action on the separated module. -/
noncomputable def ksgnsSeparatedActionCLM (b : Bᵐᵒᵖ) :
    KSGNSSeparated phi →L[ℂ] KSGNSSeparated phi :=
  (ksgnsSeparatedRmul phi (MulOpposite.unop b)).mkContinuous ‖b‖ (by
    intro x
    change ‖b • x‖ ≤ ‖b‖ * ‖x‖
    exact norm_ksgnsSeparated_op_smul_le phi b x)

@[simp]
theorem ksgnsSeparatedActionCLM_apply (b : Bᵐᵒᵖ) (x : KSGNSSeparated phi) :
    ksgnsSeparatedActionCLM phi b x = b • x := rfl

/-- Coefficient action extended to the Hilbert-module completion. -/
noncomputable def ksgnsCompletedActionCLM (b : Bᵐᵒᵖ) :
    KSGNS phi →L[ℂ] KSGNS phi :=
  completionExtendSL
    ((completionCoeLinearIsometry (E := KSGNSSeparated phi)).toContinuousLinearMap.comp
      (ksgnsSeparatedActionCLM phi b))

@[simp]
theorem ksgnsCompletedActionCLM_coe (b : Bᵐᵒᵖ) (x : KSGNSSeparated phi) :
    ksgnsCompletedActionCLM phi b (x : KSGNS phi) =
      ((b • x : KSGNSSeparated phi) : KSGNS phi) := by
  rw [ksgnsCompletedActionCLM, completionExtendSL_coe]
  rfl

noncomputable instance ksgnsCompletedSMul : SMul Bᵐᵒᵖ (KSGNS phi) :=
  ⟨fun b x => ksgnsCompletedActionCLM phi b x⟩

noncomputable instance ksgnsCompletedInner : Inner Bᵐᵒᵖ (KSGNS phi) :=
  ⟨fun x y => ksgnsCompletedInnerSLM phi x y⟩

@[simp]
theorem ksgnsCompleted_inner_apply (x y : KSGNS phi) :
    ⟪x, y⟫_Bᵐᵒᵖ = ksgnsCompletedInnerSLM phi x y := rfl

theorem continuous_ksgnsCompleted_inner_pair :
    Continuous (fun p : KSGNS phi × KSGNS phi => ⟪p.1, p.2⟫_Bᵐᵒᵖ) := by
  exact ((ksgnsCompletedInnerSLM phi).continuous.comp continuous_fst).clm_apply
    continuous_snd

theorem continuous_ksgnsCompleted_inner_self :
    Continuous (fun x : KSGNS phi => ⟪x, x⟫_Bᵐᵒᵖ) := by
  exact (continuous_ksgnsCompleted_inner_pair phi).comp
    (continuous_id.prodMk continuous_id)

theorem ksgnsCompleted_inner_add_right (x y z : KSGNS phi) :
    ⟪x, y + z⟫_Bᵐᵒᵖ = ⟪x, y⟫_Bᵐᵒᵖ + ⟪x, z⟫_Bᵐᵒᵖ := by
  exact map_add (ksgnsCompletedInnerSLM phi x) y z

theorem ksgnsCompleted_inner_smul_right_complex (q : ℂ) (x y : KSGNS phi) :
    ⟪x, q • y⟫_Bᵐᵒᵖ = q • ⟪x, y⟫_Bᵐᵒᵖ := by
  exact map_smul (ksgnsCompletedInnerSLM phi x) q y

theorem ksgnsCompleted_star_inner (x y : KSGNS phi) :
    star ⟪x, y⟫_Bᵐᵒᵖ = ⟪y, x⟫_Bᵐᵒᵖ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      (continuous_star.comp (continuous_ksgnsCompleted_inner_pair phi))
      ((continuous_ksgnsCompleted_inner_pair phi).comp
        (continuous_snd.prodMk continuous_fst))
  · intro x y
    rw [ksgnsCompleted_inner_apply, ksgnsCompleted_inner_apply,
      ksgnsCompletedInnerSLM_coe_coe, ksgnsCompletedInnerSLM_coe_coe]
    exact CStarModule.star_inner (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi) x y

theorem ksgnsCompleted_inner_self_nonneg (x : KSGNS phi) :
    0 ≤ ⟪x, x⟫_Bᵐᵒᵖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_le continuous_const (continuous_ksgnsCompleted_inner_self phi)
  · intro x
    rw [ksgnsCompleted_inner_apply, ksgnsCompletedInnerSLM_coe_coe]
    exact CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi)

theorem ksgnsCompleted_norm_eq_sqrt_norm_inner_self (x : KSGNS phi) :
    ‖x‖ = Real.sqrt ‖⟪x, x⟫_Bᵐᵒᵖ‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq continuous_norm
      (Real.continuous_sqrt.comp
        (continuous_norm.comp (continuous_ksgnsCompleted_inner_self phi)))
  · intro x
    rw [Completion.norm_coe, ksgnsCompleted_inner_apply,
      ksgnsCompletedInnerSLM_coe_coe]
    exact CStarModule.norm_eq_sqrt_norm_inner_self
      (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi) x

theorem ksgnsCompleted_inner_self (x : KSGNS phi) :
    ⟪x, x⟫_Bᵐᵒᵖ = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply norm_eq_zero.mp
    rw [ksgnsCompleted_norm_eq_sqrt_norm_inner_self phi x, hx, norm_zero,
      Real.sqrt_zero]
  · rintro rfl
    simp only [ksgnsCompleted_inner_apply, map_zero]

theorem ksgnsCompleted_inner_op_smul_right (b : Bᵐᵒᵖ) (x y : KSGNS phi) :
    ⟪x, b • y⟫_Bᵐᵒᵖ = b * ⟪x, y⟫_Bᵐᵒᵖ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      ((continuous_ksgnsCompleted_inner_pair phi).comp
        (continuous_fst.prodMk
          ((ksgnsCompletedActionCLM phi b).continuous.comp continuous_snd)))
      (continuous_const.mul (continuous_ksgnsCompleted_inner_pair phi))
  · intro x y
    change ksgnsCompletedInnerSLM phi (x : KSGNS phi)
        (ksgnsCompletedActionCLM phi b (y : KSGNS phi)) =
      b * ksgnsCompletedInnerSLM phi (x : KSGNS phi) (y : KSGNS phi)
    rw [ksgnsCompletedActionCLM_coe, ksgnsCompletedInnerSLM_coe_coe,
      ksgnsCompletedInnerSLM_coe_coe]
    exact CStarModule.inner_op_smul_right
      (A := Bᵐᵒᵖ) (E := KSGNSSeparated phi)

noncomputable instance ksgnsCompletedCStarModule : CStarModule Bᵐᵒᵖ (KSGNS phi) where
  inner_add_right := ksgnsCompleted_inner_add_right phi _ _ _
  inner_self_nonneg := ksgnsCompleted_inner_self_nonneg phi _
  inner_self := ksgnsCompleted_inner_self phi _
  inner_op_smul_right := ksgnsCompleted_inner_op_smul_right phi _ _ _
  inner_smul_right_complex := ksgnsCompleted_inner_smul_right_complex phi _ _ _
  star_inner := ksgnsCompleted_star_inner phi
  norm_eq_sqrt_norm_inner_self := ksgnsCompleted_norm_eq_sqrt_norm_inner_self phi

/-! ## Canonical left representation -/

/-- Left multiplication of algebra labels on the algebraic KSGNS free module. -/
def ksgnsPreLmul (a : A) (x : A →₀ B) : A →₀ B :=
  x.sum fun c d => Finsupp.single (a * c) d

@[simp]
theorem ksgnsPreLmul_single (a c : A) (d : B) :
    ksgnsPreLmul a (Finsupp.single c d) = Finsupp.single (a * c) d := by
  classical
  simp [ksgnsPreLmul]

theorem ksgnsPreLmul_add (a : A) (x y : A →₀ B) :
    ksgnsPreLmul a (x + y) = ksgnsPreLmul a x + ksgnsPreLmul a y := by
  classical
  unfold ksgnsPreLmul
  rw [Finsupp.sum_add_index]
  · intro c
    simp
  · intro c _ d e
    simpa using (Finsupp.single_add (a * c) d e)

theorem ksgnsPreLmul_smul (a : A) (q : ℂ) (x : A →₀ B) :
    ksgnsPreLmul a (q • x) = q • ksgnsPreLmul a x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreLmul]
  | add x y hx hy => rw [smul_add, ksgnsPreLmul_add, ksgnsPreLmul_add, hx, hy, smul_add]
  | single c d => simp [ksgnsPreLmul]

/-- Left multiplication as a complex-linear map on the free module. -/
def ksgnsPreLmulLinear (a : A) : (A →₀ B) →ₗ[ℂ] (A →₀ B) where
  toFun := ksgnsPreLmul a
  map_add' := ksgnsPreLmul_add a
  map_smul' := ksgnsPreLmul_smul a

@[simp]
theorem ksgnsPreLmulLinear_apply (a : A) (x : A →₀ B) :
    ksgnsPreLmulLinear a x = ksgnsPreLmul a x := rfl

theorem ksgnsPreLmul_one (x : A →₀ B) : ksgnsPreLmul 1 x = x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreLmul]
  | add x y hx hy => rw [ksgnsPreLmul_add, hx, hy]
  | single c d => simp

theorem ksgnsPreLmul_mul (a c : A) (x : A →₀ B) :
    ksgnsPreLmul (a * c) x = ksgnsPreLmul a (ksgnsPreLmul c x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreLmul]
  | add x y hx hy => rw [ksgnsPreLmul_add, ksgnsPreLmul_add, ksgnsPreLmul_add, hx, hy]
  | single d e => simp [mul_assoc]

theorem ksgnsPreInner_lmul_adjoint (phi : A →CP B) (a : A) (x y : A →₀ B) :
    ksgnsPreInner phi (ksgnsPreLmul a x) y =
      ksgnsPreInner phi x (ksgnsPreLmul (star a) y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreLmul, ksgnsPreInner]
  | add x z hx hz =>
      rw [ksgnsPreLmul_add, ksgnsPreInner_add_left, hx, hz,
        ksgnsPreInner_add_left]
  | single c d =>
      induction y using Finsupp.induction_linear with
      | zero => simp [ksgnsPreLmul, ksgnsPreInner]
      | add y z hy hz =>
          rw [ksgnsPreLmul_add, ksgnsPreInner_add_right,
            ksgnsPreInner_add_right, hy, hz]
      | single e f => simp [mul_assoc]

theorem ksgnsPreInner_lmul_both (phi : A →CP B) (a c : A) (x y : A →₀ B) :
    ksgnsPreInner phi (ksgnsPreLmul a x) (ksgnsPreLmul c y) =
      ksgnsPreInner phi x (ksgnsPreLmul (star a * c) y) := by
  rw [ksgnsPreInner_lmul_adjoint, ← ksgnsPreLmul_mul]

theorem ksgnsPreInner_lmul_add_label (phi : A →CP B) (a c : A) (x y : A →₀ B) :
    ksgnsPreInner phi x (ksgnsPreLmul (a + c) y) =
      ksgnsPreInner phi x (ksgnsPreLmul a y) +
        ksgnsPreInner phi x (ksgnsPreLmul c y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreInner]
  | add x z hx hz =>
      simp only [ksgnsPreInner_add_left, hx, hz]
      abel
  | single d e =>
      induction y using Finsupp.induction_linear with
      | zero => simp [ksgnsPreLmul, ksgnsPreInner]
      | add y z hy hz =>
          rw [ksgnsPreLmul_add, ksgnsPreLmul_add, ksgnsPreLmul_add,
            ksgnsPreInner_add_right, ksgnsPreInner_add_right,
            ksgnsPreInner_add_right, hy, hz]
          abel
      | single f g => simp [add_mul, mul_add]

theorem ksgnsPreInner_lmul_smul_label (phi : A →CP B) (q : ℂ) (a : A)
    (x y : A →₀ B) :
    ksgnsPreInner phi x (ksgnsPreLmul (q • a) y) =
      q • ksgnsPreInner phi x (ksgnsPreLmul a y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp [ksgnsPreInner]
  | add x z hx hz =>
      simp only [ksgnsPreInner_add_left, hx, hz, smul_add]
  | single d e =>
      induction y using Finsupp.induction_linear with
      | zero => simp [ksgnsPreLmul, ksgnsPreInner]
      | add y z hy hz =>
          rw [ksgnsPreLmul_add, ksgnsPreLmul_add,
            ksgnsPreInner_add_right, ksgnsPreInner_add_right,
            hy, hz, smul_add]
      | single f g => simp [smul_mul_assoc, mul_smul_comm]

theorem ksgnsPreInner_lmul_add_label_left (phi : A →CP B) (a c : A)
    (x y : A →₀ B) :
    ksgnsPreInner phi (ksgnsPreLmul (a + c) x) y =
      ksgnsPreInner phi (ksgnsPreLmul a x) y +
        ksgnsPreInner phi (ksgnsPreLmul c x) y := by
  rw [ksgnsPreInner_lmul_adjoint, star_add, ksgnsPreInner_lmul_add_label,
    ← ksgnsPreInner_lmul_adjoint, ← ksgnsPreInner_lmul_adjoint]

theorem ksgnsPreInner_lmul_smul_label_left (phi : A →CP B) (q : ℂ) (a : A)
    (x y : A →₀ B) :
    ksgnsPreInner phi (ksgnsPreLmul (q • a) x) y =
      star q • ksgnsPreInner phi (ksgnsPreLmul a x) y := by
  rw [ksgnsPreInner_lmul_adjoint, star_smul,
    ksgnsPreInner_lmul_smul_label, ← ksgnsPreInner_lmul_adjoint]

theorem ksgnsPreInner_lmul_sub_label (phi : A →CP B) (a c : A) (x y : A →₀ B) :
    ksgnsPreInner phi x (ksgnsPreLmul (a - c) y) =
      ksgnsPreInner phi x (ksgnsPreLmul a y) -
        ksgnsPreInner phi x (ksgnsPreLmul c y) := by
  rw [sub_eq_add_neg, ksgnsPreInner_lmul_add_label]
  have hneg := ksgnsPreInner_lmul_smul_label phi (-1 : ℂ) c x y
  simp only [neg_one_smul] at hneg
  rw [hneg]
  rw [sub_eq_add_neg]

theorem ksgnsPreInner_lmul_norm_gap (phi : A →CP B) (a : A) (x : A →₀ B) :
    (‖a‖ ^ 2 : ℝ) • ksgnsPreInner phi x x -
        ksgnsPreInner phi (ksgnsPreLmul a x) (ksgnsPreLmul a x) =
      ksgnsPreInner phi
        (ksgnsPreLmul (CFC.sqrt ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a)) x)
        (ksgnsPreLmul (CFC.sqrt ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a)) x) := by
  let h : A := (‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a
  have hh : 0 ≤ h := by
    dsimp [h]
    rw [sub_nonneg]
    have ha := (IsSelfAdjoint.star_mul_self a).le_algebraMap_norm_self
    rw [CStarRing.norm_star_mul_self, Algebra.algebraMap_eq_smul_one] at ha
    simpa [pow_two] using ha
  let p : A := CFC.sqrt h
  have hpstar : star p = p := (CFC.sqrt_nonneg h).star_eq
  have hp2 : star p * p = h := by
    rw [hpstar]
    simpa [pow_two] using CFC.sq_sqrt h hh
  have hrlabel : ((‖a‖ ^ 2 : ℝ) • (1 : A)) =
      ((‖a‖ ^ 2 : ℂ) • (1 : A)) := by
    norm_cast
  change (‖a‖ ^ 2 : ℝ) • ksgnsPreInner phi x x -
      ksgnsPreInner phi (ksgnsPreLmul a x) (ksgnsPreLmul a x) =
    ksgnsPreInner phi (ksgnsPreLmul p x) (ksgnsPreLmul p x)
  rw [ksgnsPreInner_lmul_both, ksgnsPreInner_lmul_both, hp2]
  change (‖a‖ ^ 2 : ℝ) • ksgnsPreInner phi x x -
      ksgnsPreInner phi x (ksgnsPreLmul (star a * a) x) =
    ksgnsPreInner phi x (ksgnsPreLmul h x)
  rw [show h = (‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a by rfl,
    ksgnsPreInner_lmul_sub_label, hrlabel,
    ksgnsPreInner_lmul_smul_label, ksgnsPreLmul_one]
  norm_cast

theorem ksgnsPreInner_lmul_self_le (phi : A →CP B) (a : A) (x : A →₀ B) :
    ksgnsPreInner phi (ksgnsPreLmul a x) (ksgnsPreLmul a x) ≤
      (‖a‖ ^ 2 : ℝ) • ksgnsPreInner phi x x := by
  apply sub_nonneg.mp
  rw [ksgnsPreInner_lmul_norm_gap]
  exact ksgnsPreInner_self_nonneg phi _

theorem norm_ksgnsPreInner_lmul_self_le (phi : A →CP B) (a : A) (x : A →₀ B) :
    ‖ksgnsPreInner phi (ksgnsPreLmul a x) (ksgnsPreLmul a x)‖ ≤
      ‖a‖ ^ 2 * ‖ksgnsPreInner phi x x‖ := by
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (ksgnsPreInner_self_nonneg phi (ksgnsPreLmul a x))
    (ksgnsPreInner_lmul_self_le phi a x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a‖)] at hnorm
  exact hnorm

theorem ksgnsPreLmul_mem_radical (phi : A →CP B) (a : A) {x : A →₀ B}
    (hx : x ∈ ksgnsPreRadical phi) :
    ksgnsPreLmul a x ∈ ksgnsPreRadical phi := by
  intro y
  rw [ksgnsPreInner_lmul_adjoint]
  exact hx _

/-- Canonical left multiplication descended to the separated KSGNS quotient. -/
def ksgnsSeparatedLmul (phi : A →CP B) (a : A) :
    KSGNSSeparated phi →ₗ[ℂ] KSGNSSeparated phi :=
  (ksgnsPreRadical phi).mapQ (ksgnsPreRadical phi) (ksgnsPreLmulLinear a) (by
    intro x hx
    exact ksgnsPreLmul_mem_radical phi a hx)

@[simp]
theorem ksgnsSeparatedLmul_mk (phi : A →CP B) (a : A) (x : A →₀ B) :
    ksgnsSeparatedLmul phi a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ksgnsPreLmul a x) := by
  exact Submodule.mapQ_apply _ _ _ _

theorem norm_ksgnsSeparatedLmul_le (phi : A →CP B) (a : A)
    (x : KSGNSSeparated phi) :
    ‖ksgnsSeparatedLmul phi a x‖ ≤ ‖a‖ * ‖x‖ := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change ‖(Submodule.Quotient.mk (ksgnsPreLmul a x) : KSGNSSeparated phi)‖ ≤
      ‖a‖ * ‖(Submodule.Quotient.mk x : KSGNSSeparated phi)‖
    rw [← sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg a) (norm_nonneg (Submodule.Quotient.mk x : KSGNSSeparated phi)))]
    rw [CStarModule.norm_sq_eq (A := Bᵐᵒᵖ)
        (x := (Submodule.Quotient.mk (ksgnsPreLmul a x) : KSGNSSeparated phi)),
      mul_pow,
      CStarModule.norm_sq_eq (A := Bᵐᵒᵖ)
        (x := (Submodule.Quotient.mk x : KSGNSSeparated phi))]
    change ‖MulOpposite.op
        (ksgnsPreInner phi (ksgnsPreLmul a x) (ksgnsPreLmul a x))‖ ≤
      ‖a‖ ^ 2 * ‖MulOpposite.op (ksgnsPreInner phi x x)‖
    rw [MulOpposite.norm_op, MulOpposite.norm_op]
    exact norm_ksgnsPreInner_lmul_self_le phi a x

/-- Bounded canonical left multiplication on the separated quotient. -/
noncomputable def ksgnsSeparatedLmulCLM (phi : A →CP B) (a : A) :
    KSGNSSeparated phi →L[ℂ] KSGNSSeparated phi :=
  (ksgnsSeparatedLmul phi a).mkContinuous ‖a‖ (by
    intro x
    exact norm_ksgnsSeparatedLmul_le phi a x)

@[simp]
theorem ksgnsSeparatedLmulCLM_apply (phi : A →CP B) (a : A)
    (x : KSGNSSeparated phi) :
    ksgnsSeparatedLmulCLM phi a x = ksgnsSeparatedLmul phi a x := rfl

/-- Canonical left action extended to the complete KSGNS module. -/
noncomputable def ksgnsRepresentation (phi : A →CP B) (a : A) :
    KSGNS phi →L[ℂ] KSGNS phi :=
  completionExtendSL
    ((completionCoeLinearIsometry (E := KSGNSSeparated phi)).toContinuousLinearMap.comp
      (ksgnsSeparatedLmulCLM phi a))

@[simp]
theorem ksgnsRepresentation_coe (phi : A →CP B) (a : A) (x : KSGNSSeparated phi) :
    ksgnsRepresentation phi a (x : KSGNS phi) =
      ((ksgnsSeparatedLmul phi a x : KSGNSSeparated phi) : KSGNS phi) := by
  rw [ksgnsRepresentation, completionExtendSL_coe]
  rfl

theorem ksgnsSeparatedLmul_add_label (phi : A →CP B) (a c : A)
    (x : KSGNSSeparated phi) :
    ksgnsSeparatedLmul phi (a + c) x =
      ksgnsSeparatedLmul phi a x + ksgnsSeparatedLmul phi c x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsPreLmul (a + c) x) =
      Submodule.Quotient.mk (ksgnsPreLmul a x + ksgnsPreLmul c x)
    rw [Submodule.Quotient.eq]
    intro y
    rw [ksgnsPreInner_sub_left, ksgnsPreInner_lmul_add_label_left,
      ksgnsPreInner_add_left]
    abel

theorem ksgnsSeparatedLmul_smul_label (phi : A →CP B) (q : ℂ) (a : A)
    (x : KSGNSSeparated phi) :
    ksgnsSeparatedLmul phi (q • a) x = q • ksgnsSeparatedLmul phi a x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsPreLmul (q • a) x) =
      Submodule.Quotient.mk (q • ksgnsPreLmul a x)
    rw [Submodule.Quotient.eq]
    intro y
    rw [ksgnsPreInner_sub_left, ksgnsPreInner_lmul_smul_label_left,
      ksgnsPreInner_smul_left]
    simp

theorem ksgnsSeparatedLmul_one (phi : A →CP B) (x : KSGNSSeparated phi) :
    ksgnsSeparatedLmul phi 1 x = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsPreLmul 1 x) = Submodule.Quotient.mk x
    rw [ksgnsPreLmul_one]

theorem ksgnsSeparatedLmul_mul (phi : A →CP B) (a c : A)
    (x : KSGNSSeparated phi) :
    ksgnsSeparatedLmul phi (a * c) x =
      ksgnsSeparatedLmul phi a (ksgnsSeparatedLmul phi c x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsPreLmul (a * c) x) =
      Submodule.Quotient.mk (ksgnsPreLmul a (ksgnsPreLmul c x))
    rw [ksgnsPreLmul_mul]

theorem ksgnsSeparatedLmul_adjoint (phi : A →CP B) (a : A)
    (x y : KSGNSSeparated phi) :
    ⟪ksgnsSeparatedLmul phi a x, y⟫_Bᵐᵒᵖ =
      ⟪x, ksgnsSeparatedLmul phi (star a) y⟫_Bᵐᵒᵖ := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y =>
    change MulOpposite.op (ksgnsPreInner phi (ksgnsPreLmul a x) y) =
      MulOpposite.op (ksgnsPreInner phi x (ksgnsPreLmul (star a) y))
    rw [ksgnsPreInner_lmul_adjoint]

theorem ksgnsSeparatedLmul_rmul (phi : A →CP B) (a : A) (b : B)
    (x : KSGNSSeparated phi) :
    ksgnsSeparatedLmul phi a (MulOpposite.op b • x) =
      MulOpposite.op b • ksgnsSeparatedLmul phi a x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsPreLmul a (ksgnsPreRmul x b)) =
      Submodule.Quotient.mk (ksgnsPreRmul (ksgnsPreLmul a x) b)
    congr 1
    classical
    have rmul_add (u v : A →₀ B) :
        ksgnsPreRmul (u + v) b = ksgnsPreRmul u b + ksgnsPreRmul v b := by
      ext q
      simp [ksgnsPreRmul_apply, add_mul]
    induction x using Finsupp.induction_linear with
    | zero => simp [ksgnsPreLmul, ksgnsPreRmul]
    | add x y hx hy =>
        rw [rmul_add, ksgnsPreLmul_add, ksgnsPreLmul_add, rmul_add, hx, hy]
    | single c d => simp [mul_assoc]

theorem ksgnsRepresentation_add (phi : A →CP B) (a c : A) :
    ksgnsRepresentation phi (a + c) =
      ksgnsRepresentation phi a + ksgnsRepresentation phi c := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsRepresentation phi (a + c)).continuous
      ((ksgnsRepresentation phi a).continuous.add
        (ksgnsRepresentation phi c).continuous)
  · intro x
    rw [ksgnsRepresentation_coe]
    change ((ksgnsSeparatedLmul phi (a + c) x : KSGNSSeparated phi) : KSGNS phi) =
      ksgnsRepresentation phi a (x : KSGNS phi) +
        ksgnsRepresentation phi c (x : KSGNS phi)
    rw [ksgnsRepresentation_coe, ksgnsRepresentation_coe,
      ← Completion.coe_add,
      ksgnsSeparatedLmul_add_label]

theorem ksgnsRepresentation_smul (phi : A →CP B) (q : ℂ) (a : A) :
    ksgnsRepresentation phi (q • a) = q • ksgnsRepresentation phi a := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsRepresentation phi (q • a)).continuous
      ((continuous_const_smul q).comp (ksgnsRepresentation phi a).continuous)
  · intro x
    rw [ksgnsRepresentation_coe]
    change ((ksgnsSeparatedLmul phi (q • a) x : KSGNSSeparated phi) : KSGNS phi) =
      q • ksgnsRepresentation phi a (x : KSGNS phi)
    rw [ksgnsRepresentation_coe,
      ← Completion.coe_smul, ksgnsSeparatedLmul_smul_label]

theorem ksgnsRepresentation_one (phi : A →CP B) :
    ksgnsRepresentation phi 1 = ContinuousLinearMap.id ℂ (KSGNS phi) := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsRepresentation phi 1).continuous continuous_id
  · intro x
    rw [ksgnsRepresentation_coe, ksgnsSeparatedLmul_one]
    rfl

theorem ksgnsRepresentation_mul (phi : A →CP B) (a c : A) :
    ksgnsRepresentation phi (a * c) =
      (ksgnsRepresentation phi a).comp (ksgnsRepresentation phi c) := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsRepresentation phi (a * c)).continuous
      ((ksgnsRepresentation phi a).continuous.comp
        (ksgnsRepresentation phi c).continuous)
  · intro x
    rw [ksgnsRepresentation_coe]
    change ((ksgnsSeparatedLmul phi (a * c) x : KSGNSSeparated phi) : KSGNS phi) =
      ksgnsRepresentation phi a (ksgnsRepresentation phi c (x : KSGNS phi))
    rw [ksgnsRepresentation_coe,
      ksgnsRepresentation_coe, ksgnsSeparatedLmul_mul]

theorem ksgnsRepresentation_adjoint (phi : A →CP B) (a : A)
    (x y : KSGNS phi) :
    ⟪ksgnsRepresentation phi a x, y⟫_Bᵐᵒᵖ =
      ⟪x, ksgnsRepresentation phi (star a) y⟫_Bᵐᵒᵖ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      ((continuous_ksgnsCompleted_inner_pair phi).comp
        (((ksgnsRepresentation phi a).continuous.comp continuous_fst).prodMk
          continuous_snd))
      ((continuous_ksgnsCompleted_inner_pair phi).comp
        (continuous_fst.prodMk
          ((ksgnsRepresentation phi (star a)).continuous.comp continuous_snd)))
  · intro x y
    rw [ksgnsRepresentation_coe, ksgnsRepresentation_coe,
      ksgnsCompleted_inner_apply, ksgnsCompleted_inner_apply,
      ksgnsCompletedInnerSLM_coe_coe, ksgnsCompletedInnerSLM_coe_coe]
    exact ksgnsSeparatedLmul_adjoint phi a x y

theorem ksgnsRepresentation_rmul (phi : A →CP B) (a : A) (b : B)
    (x : KSGNS phi) :
    ksgnsRepresentation phi a (MulOpposite.op b • x) =
      MulOpposite.op b • ksgnsRepresentation phi a x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq
      ((ksgnsRepresentation phi a).continuous.comp
        (ksgnsCompletedActionCLM phi (MulOpposite.op b)).continuous)
      ((ksgnsCompletedActionCLM phi (MulOpposite.op b)).continuous.comp
        (ksgnsRepresentation phi a).continuous)
  · intro x
    change ksgnsRepresentation phi a
        (ksgnsCompletedActionCLM phi (MulOpposite.op b) (x : KSGNS phi)) =
      ksgnsCompletedActionCLM phi (MulOpposite.op b)
        (ksgnsRepresentation phi a (x : KSGNS phi))
    rw [ksgnsCompletedActionCLM_coe, ksgnsRepresentation_coe,
      ksgnsRepresentation_coe, ksgnsCompletedActionCLM_coe,
      ksgnsSeparatedLmul_rmul]

theorem ksgnsRepresentation_zero (phi : A →CP B) :
    ksgnsRepresentation phi 0 = 0 := by
  have h := ksgnsRepresentation_smul phi (0 : ℂ) (0 : A)
  simpa using h

/-- Algebra-homomorphic part of the canonical KSGNS representation. -/
noncomputable def ksgnsRepresentationAlgHom (phi : A →CP B) :
    A →ₐ[ℂ] (KSGNS phi →L[ℂ] KSGNS phi) where
  toFun := ksgnsRepresentation phi
  map_one' := ksgnsRepresentation_one phi
  map_mul' a c := by
    rw [ksgnsRepresentation_mul]
    rfl
  map_zero' := ksgnsRepresentation_zero phi
  map_add' := ksgnsRepresentation_add phi
  commutes' q := by
    rw [Algebra.algebraMap_eq_smul_one, ksgnsRepresentation_smul,
      ksgnsRepresentation_one, Algebra.algebraMap_eq_smul_one]
    congr 1

/-- A bounded left representation on a Hilbert C⋆-module, including adjoint and right-module
compatibility. This packages the operator notion needed for C⋆-correspondences without assuming
that every bounded module operator has an adjoint. -/
structure CStarModuleRepresentation (A B E : Type*)
    [CStarAlgebra A] [CStarAlgebra B]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [PartialOrder B] [StarOrderedRing B] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] where
  toAlgHom : A →ₐ[ℂ] (E →L[ℂ] E)
  adjoint_inner : ∀ (a : A) (x y : E),
    ⟪toAlgHom a x, y⟫_Bᵐᵒᵖ = ⟪x, toAlgHom (star a) y⟫_Bᵐᵒᵖ
  map_op_smul : ∀ (a : A) (b : B) (x : E),
    toAlgHom a (MulOpposite.op b • x) = MulOpposite.op b • toAlgHom a x

instance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] :
    CoeFun (CStarModuleRepresentation A B E) (fun _ => A → E → E) :=
  ⟨fun π a x => π.toAlgHom a x⟩

/-- Canonical adjointable, right-module-linear KSGNS representation. -/
noncomputable def canonicalKSGNSRepresentation (phi : A →CP B) :
    CStarModuleRepresentation A B (KSGNS phi) where
  toAlgHom := ksgnsRepresentationAlgHom phi
  adjoint_inner := ksgnsRepresentation_adjoint phi
  map_op_smul := ksgnsRepresentation_rmul phi

/-- Algebraic cyclic vector before separation. -/
def ksgnsPreCyclic : A →₀ B := Finsupp.single 1 1

/-- Cyclic vector in the separated KSGNS module. -/
def ksgnsSeparatedCyclic (phi : A →CP B) : KSGNSSeparated phi :=
  Submodule.Quotient.mk ksgnsPreCyclic

/-- Canonical cyclic vector in the complete KSGNS module. -/
def ksgnsCyclic (phi : A →CP B) : KSGNS phi :=
  (ksgnsSeparatedCyclic phi : KSGNS phi)

@[simp]
theorem ksgnsSeparatedLmul_cyclic (phi : A →CP B) (a : A) :
    ksgnsSeparatedLmul phi a (ksgnsSeparatedCyclic phi) =
      Submodule.Quotient.mk (Finsupp.single a 1) := by
  rw [ksgnsSeparatedCyclic, ksgnsSeparatedLmul_mk]
  simp [ksgnsPreCyclic]

@[simp]
theorem ksgnsRepresentation_cyclic (phi : A →CP B) (a : A) :
    ksgnsRepresentation phi a (ksgnsCyclic phi) =
      ((Submodule.Quotient.mk (Finsupp.single a 1) : KSGNSSeparated phi) : KSGNS phi) := by
  rw [ksgnsCyclic, ksgnsRepresentation_coe, ksgnsSeparatedLmul_cyclic]

/-- Exact recovery of the CP map from its canonical cyclic vector. -/
@[simp]
theorem ksgns_inner_cyclic_representation_cyclic (phi : A →CP B) (a : A) :
    ⟪ksgnsCyclic phi, ksgnsRepresentation phi a (ksgnsCyclic phi)⟫_Bᵐᵒᵖ =
      MulOpposite.op (phi a) := by
  rw [ksgnsRepresentation_cyclic, ksgnsCyclic,
    ksgnsCompleted_inner_apply, ksgnsCompletedInnerSLM_coe_coe]
  change MulOpposite.op
      (ksgnsPreInner phi (Finsupp.single 1 1) (Finsupp.single a 1)) = _
  simp

/-- Exact cyclic-square identity `⟨ξ,ξ⟩ = Φ(1)`. -/
@[simp]
theorem ksgns_inner_cyclic (phi : A →CP B) :
    ⟪ksgnsCyclic phi, ksgnsCyclic phi⟫_Bᵐᵒᵖ = MulOpposite.op (phi 1) := by
  have h := ksgns_inner_cyclic_representation_cyclic phi 1
  rw [ksgnsRepresentation_one] at h
  exact h

/-- Complex cyclic span generated by `π(A)ξ B`; taking closure gives the minimal KSGNS
correspondence. -/
def ksgnsCyclicSpan (phi : A →CP B) : Submodule ℂ (KSGNS phi) :=
  Submodule.span ℂ {z | ∃ (a : A) (b : B),
    z = MulOpposite.op b • ksgnsRepresentation phi a (ksgnsCyclic phi)}

theorem coe_mem_ksgnsCyclicSpan (phi : A →CP B) (x : KSGNSSeparated phi) :
    (x : KSGNS phi) ∈ ksgnsCyclicSpan phi := by
  induction x using Quotient.inductionOn with
  | _ x =>
    induction x using Finsupp.induction_linear with
    | zero =>
        change ((0 : KSGNSSeparated phi) : KSGNS phi) ∈ ksgnsCyclicSpan phi
        rw [Completion.coe_zero]
        exact (ksgnsCyclicSpan phi).zero_mem
    | add x y hx hy =>
        change (((Submodule.Quotient.mk x : KSGNSSeparated phi) +
          Submodule.Quotient.mk y : KSGNSSeparated phi) : KSGNS phi) ∈
            ksgnsCyclicSpan phi
        rw [Completion.coe_add]
        exact (ksgnsCyclicSpan phi).add_mem hx hy
    | single a b =>
        apply Submodule.subset_span
        refine ⟨a, b, ?_⟩
        rw [ksgnsRepresentation_cyclic]
        change ((Submodule.Quotient.mk (Finsupp.single a b) : KSGNSSeparated phi) : KSGNS phi) =
          ksgnsCompletedActionCLM phi (MulOpposite.op b)
            ((Submodule.Quotient.mk (Finsupp.single a 1) : KSGNSSeparated phi) : KSGNS phi)
        rw [ksgnsCompletedActionCLM_coe]
        congr 1
        simp

/-- Minimality: the canonical cyclic span is dense in the complete KSGNS module. -/
theorem dense_ksgnsCyclicSpan (phi : A →CP B) :
    Dense (ksgnsCyclicSpan phi : Set (KSGNS phi)) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_closure
  · intro x
    exact subset_closure (coe_mem_ksgnsCyclicSpan phi x)

/-! ## Genuine right-module laws and pointed KSGNS presentation -/

theorem ksgnsSeparated_one_op_smul (phi : A →CP B) (x : KSGNSSeparated phi) :
    (1 : Bᵐᵒᵖ) • x = x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk (ksgnsPreRmul x 1) = Submodule.Quotient.mk x
    congr 1
    ext q
    simp [ksgnsPreRmul_apply]

theorem ksgnsSeparated_mul_op_smul (phi : A →CP B) (b c : Bᵐᵒᵖ)
    (x : KSGNSSeparated phi) :
    (b * c) • x = b • c • x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk
        (ksgnsPreRmul x (MulOpposite.unop (b * c))) =
      Submodule.Quotient.mk
        (ksgnsPreRmul (ksgnsPreRmul x (MulOpposite.unop c))
          (MulOpposite.unop b))
    rw [MulOpposite.unop_mul]
    congr 1
    ext q
    simp [ksgnsPreRmul_apply, mul_assoc]

theorem ksgnsSeparated_add_op_smul (phi : A →CP B) (b c : Bᵐᵒᵖ)
    (x : KSGNSSeparated phi) :
    (b + c) • x = b • x + c • x := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk
        (ksgnsPreRmul x (MulOpposite.unop (b + c))) =
      Submodule.Quotient.mk
        (ksgnsPreRmul x (MulOpposite.unop b) +
          ksgnsPreRmul x (MulOpposite.unop c))
    congr 1
    ext q
    simp [ksgnsPreRmul_apply, mul_add]

theorem ksgnsSeparated_op_smul_add (phi : A →CP B) (b : Bᵐᵒᵖ)
    (x y : KSGNSSeparated phi) :
    b • (x + y) = b • x + b • y := by
  exact map_add (ksgnsSeparatedRmul phi (MulOpposite.unop b)) x y

noncomputable instance ksgnsSeparatedModule (phi : A →CP B) :
    Module Bᵐᵒᵖ (KSGNSSeparated phi) :=
  Module.ofMinimalAxioms
    (ksgnsSeparated_op_smul_add phi)
    (ksgnsSeparated_add_op_smul phi)
    (ksgnsSeparated_mul_op_smul phi)
    (ksgnsSeparated_one_op_smul phi)

theorem ksgnsCompleted_one_op_smul (phi : A →CP B) (x : KSGNS phi) :
    (1 : Bᵐᵒᵖ) • x = x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsCompletedActionCLM phi 1).continuous continuous_id
  · intro x
    change ksgnsCompletedActionCLM phi 1 (x : KSGNS phi) = (x : KSGNS phi)
    rw [ksgnsCompletedActionCLM_coe, ksgnsSeparated_one_op_smul]

theorem ksgnsCompleted_mul_op_smul (phi : A →CP B) (b c : Bᵐᵒᵖ)
    (x : KSGNS phi) :
    (b * c) • x = b • c • x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsCompletedActionCLM phi (b * c)).continuous
      ((ksgnsCompletedActionCLM phi b).continuous.comp
        (ksgnsCompletedActionCLM phi c).continuous)
  · intro x
    change ksgnsCompletedActionCLM phi (b * c) (x : KSGNS phi) =
      ksgnsCompletedActionCLM phi b
        (ksgnsCompletedActionCLM phi c (x : KSGNS phi))
    rw [ksgnsCompletedActionCLM_coe, ksgnsCompletedActionCLM_coe,
      ksgnsCompletedActionCLM_coe, ksgnsSeparated_mul_op_smul]

theorem ksgnsCompleted_add_op_smul (phi : A →CP B) (b c : Bᵐᵒᵖ)
    (x : KSGNS phi) :
    (b + c) • x = b • x + c • x := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsCompletedActionCLM phi (b + c)).continuous
      ((ksgnsCompletedActionCLM phi b).continuous.add
        (ksgnsCompletedActionCLM phi c).continuous)
  · intro x
    change ksgnsCompletedActionCLM phi (b + c) (x : KSGNS phi) =
      ksgnsCompletedActionCLM phi b (x : KSGNS phi) +
        ksgnsCompletedActionCLM phi c (x : KSGNS phi)
    rw [ksgnsCompletedActionCLM_coe, ksgnsCompletedActionCLM_coe,
      ksgnsCompletedActionCLM_coe, ← Completion.coe_add,
      ksgnsSeparated_add_op_smul]

theorem ksgnsCompleted_op_smul_add (phi : A →CP B) (b : Bᵐᵒᵖ)
    (x y : KSGNS phi) :
    b • (x + y) = b • x + b • y := by
  exact map_add (ksgnsCompletedActionCLM phi b) x y

noncomputable instance ksgnsCompletedModule (phi : A →CP B) :
    Module Bᵐᵒᵖ (KSGNS phi) :=
  Module.ofMinimalAxioms
    (ksgnsCompleted_op_smul_add phi)
    (ksgnsCompleted_add_op_smul phi)
    (ksgnsCompleted_mul_op_smul phi)
    (ksgnsCompleted_one_op_smul phi)

theorem ksgnsSeparated_smul_op_smul (phi : A →CP B) (q : ℂ) (b : Bᵐᵒᵖ)
    (x : KSGNSSeparated phi) :
    (q • b) • x = q • (b • x) := by
  induction x using Quotient.inductionOn with
  | _ x =>
    change Submodule.Quotient.mk
        (ksgnsPreRmul x (q • MulOpposite.unop b)) =
      Submodule.Quotient.mk (q • ksgnsPreRmul x (MulOpposite.unop b))
    congr 1
    ext a
    simp [ksgnsPreRmul_apply]

theorem ksgnsCompleted_smul_op_smul (phi : A →CP B) (q : ℂ) (b : Bᵐᵒᵖ)
    (x : KSGNS phi) :
    (q • b) • x = q • (b • x) := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq (ksgnsCompletedActionCLM phi (q • b)).continuous
      ((continuous_const_smul q).comp (ksgnsCompletedActionCLM phi b).continuous)
  · intro x
    change ksgnsCompletedActionCLM phi (q • b) (x : KSGNS phi) =
      q • ksgnsCompletedActionCLM phi b (x : KSGNS phi)
    rw [ksgnsCompletedActionCLM_coe, ksgnsCompletedActionCLM_coe,
      ← Completion.coe_smul, ksgnsSeparated_smul_op_smul]

/-- Standard `B`-valued right Hilbert-module operations extracted from the opposite-algebra
encoding used by `CStarModule`. -/
noncomputable def ksgnsRightInnerModuleData (phi : A →CP B) :
    RightInnerModuleData B (KSGNS phi) where
  inner x y := MulOpposite.unop ⟪x, y⟫_Bᵐᵒᵖ
  rmul x b := MulOpposite.op b • x
  inner_add_right := by
    intro x y z
    rw [CStarModule.inner_add_right (A := Bᵐᵒᵖ) (E := KSGNS phi)]
    rfl
  inner_smul_right := by
    intro q x y
    rw [CStarModule.inner_smul_right_complex
      (A := Bᵐᵒᵖ) (E := KSGNS phi)]
    rfl
  inner_rmul_right := by
    intro x y b
    rw [CStarModule.inner_op_smul_right
      (A := Bᵐᵒᵖ) (E := KSGNS phi)]
    rfl
  star_inner := by
    intro x y
    have h := CStarModule.star_inner (A := Bᵐᵒᵖ) x y
    exact congrArg MulOpposite.unop h
  rmul_one := by
    intro x
    exact ksgnsCompleted_one_op_smul phi x
  rmul_mul := by
    intro x b c
    have h := ksgnsCompleted_mul_op_smul phi (MulOpposite.op c)
      (MulOpposite.op b) x
    simpa using h.symm
  rmul_add_left := by
    intro x y b
    exact ksgnsCompleted_op_smul_add phi (MulOpposite.op b) x y
  rmul_add_right := by
    intro x b c
    exact ksgnsCompleted_add_op_smul phi (MulOpposite.op b)
      (MulOpposite.op c) x
  rmul_smul := by
    intro q x b
    exact map_smul (ksgnsCompletedActionCLM phi (MulOpposite.op b)) q x

/-- Actual minimal pointed KSGNS presentation for a unital completely positive map. -/
noncomputable def canonicalUnitalPointedKSGNS (phi : A →CP B) (hphi : phi 1 = 1) :
    UnitalPointedKSGNSData A B (KSGNS phi) phi where
  moduleData := ksgnsRightInnerModuleData phi
  act a x := ksgnsRepresentation phi a x
  xi := ksgnsCyclic phi
  act_one := by
    intro x
    rw [ksgnsRepresentation_one]
    rfl
  act_mul := by
    intro a c x
    exact congrArg (fun T : KSGNS phi →L[ℂ] KSGNS phi => T x)
      (ksgnsRepresentation_mul phi a c)
  act_add_ring := by
    intro a c x
    exact congrArg (fun T : KSGNS phi →L[ℂ] KSGNS phi => T x)
      (ksgnsRepresentation_add phi a c)
  act_add_module := by
    intro a x y
    exact map_add (ksgnsRepresentation phi a) x y
  act_smul := by
    intro q a x
    exact map_smul (ksgnsRepresentation phi a) q x
  act_rmul := by
    intro a x b
    exact ksgnsRepresentation_rmul phi a b x
  act_adjoint := by
    intro a x y
    exact congrArg MulOpposite.unop (ksgnsRepresentation_adjoint phi a x y)
  recover := by
    intro a
    exact congrArg MulOpposite.unop
      (ksgns_inner_cyclic_representation_cyclic phi a)
  map_one := hphi

/-- Equation (4) on the actual minimal complete KSGNS module. -/
theorem canonicalKSGNS_inner_centered_centered (phi : A →CP B)
    (hphi : phi 1 = 1) (x y : A) :
    (ksgnsRightInnerModuleData phi).inner
        ((canonicalUnitalPointedKSGNS phi hphi).centered x)
        ((canonicalUnitalPointedKSGNS phi hphi).centered y) =
      phi (star x * y) - star (phi x) * phi y :=
  (canonicalUnitalPointedKSGNS phi hphi).inner_centered_centered x y

/-! ## Weighted centered complement -/

theorem ksgnsRight_inner_rep_cyclic_rep_cyclic (phi : A →CP B) (x y : A) :
    (ksgnsRightInnerModuleData phi).inner
        (ksgnsRepresentation phi x (ksgnsCyclic phi))
        (ksgnsRepresentation phi y (ksgnsCyclic phi)) =
      phi (star x * y) := by
  apply MulOpposite.op_injective
  change ⟪ksgnsRepresentation phi x (ksgnsCyclic phi),
      ksgnsRepresentation phi y (ksgnsCyclic phi)⟫_Bᵐᵒᵖ =
    MulOpposite.op (phi (star x * y))
  rw [ksgnsRepresentation_adjoint]
  have hmul :
      ksgnsRepresentation phi (star x * y) (ksgnsCyclic phi) =
        ksgnsRepresentation phi (star x)
          (ksgnsRepresentation phi y (ksgnsCyclic phi)) := by
    simpa using congrArg
      (fun T : KSGNS phi →L[ℂ] KSGNS phi => T (ksgnsCyclic phi))
      (ksgnsRepresentation_mul phi (star x) y)
  rw [← hmul, ksgns_inner_cyclic_representation_cyclic]

theorem ksgnsRight_inner_rep_cyclic_cyclic (phi : A →CP B) (x : A) :
    (ksgnsRightInnerModuleData phi).inner
        (ksgnsRepresentation phi x (ksgnsCyclic phi)) (ksgnsCyclic phi) =
      star (phi x) := by
  rw [← (ksgnsRightInnerModuleData phi).star_inner]
  change star (MulOpposite.unop
      ⟪ksgnsCyclic phi, ksgnsRepresentation phi x (ksgnsCyclic phi)⟫_Bᵐᵒᵖ) = _
  rw [ksgns_inner_cyclic_representation_cyclic]
  rfl

theorem ksgnsRight_inner_cyclic_rep_cyclic (phi : A →CP B) (x : A) :
    (ksgnsRightInnerModuleData phi).inner (ksgnsCyclic phi)
        (ksgnsRepresentation phi x (ksgnsCyclic phi)) = phi x := by
  exact congrArg MulOpposite.unop
    (ksgns_inner_cyclic_representation_cyclic phi x)

theorem ksgnsRight_inner_cyclic_cyclic (phi : A →CP B) :
    (ksgnsRightInnerModuleData phi).inner (ksgnsCyclic phi) (ksgnsCyclic phi) =
      phi 1 := by
  exact congrArg MulOpposite.unop (ksgns_inner_cyclic phi)

/-- Inverse of the positive order unit `Φ(1)`, represented through the unit certified by
invertibility. -/
def ksgnsOrderUnitInv (phi : A →CP B) (hunit : IsUnit (phi 1)) : B :=
  ↑(hunit.unit⁻¹)

theorem ksgnsOrderUnitInv_mul (phi : A →CP B) (hunit : IsUnit (phi 1)) :
    ksgnsOrderUnitInv phi hunit * phi 1 = 1 := by
  simpa only [ksgnsOrderUnitInv, hunit.unit_spec] using Units.inv_mul hunit.unit

theorem mul_ksgnsOrderUnitInv (phi : A →CP B) (hunit : IsUnit (phi 1)) :
    phi 1 * ksgnsOrderUnitInv phi hunit = 1 := by
  simpa only [ksgnsOrderUnitInv, hunit.unit_spec] using Units.mul_inv hunit.unit

theorem star_ksgnsOrderUnitInv (phi : A →CP B) (hunit : IsUnit (phi 1)) :
    star (ksgnsOrderUnitInv phi hunit) = ksgnsOrderUnitInv phi hunit := by
  let g := ksgnsOrderUnitInv phi hunit
  let h := phi 1
  have hhstar : star h = h := by
    dsimp [h]
    rw [← map_star phi]
    simp
  have hhg : h * g = 1 := mul_ksgnsOrderUnitInv phi hunit
  have hgh : g * h = 1 := ksgnsOrderUnitInv_mul phi hunit
  have hstargh : star g * h = 1 := by
    have hs := congrArg star hhg
    rw [star_mul, star_one, hhstar] at hs
    exact hs
  calc
    star g = star g * 1 := by rw [mul_one]
    _ = star g * (h * g) := by rw [hhg]
    _ = (star g * h) * g := by rw [mul_assoc]
    _ = g := by rw [hstargh, one_mul]

/-- Weighted centered KSGNS vector from Equation (1). -/
def ksgnsWeightedCentered (phi : A →CP B) (hunit : IsUnit (phi 1)) (x : A) :
    KSGNS phi :=
  ksgnsRepresentation phi x (ksgnsCyclic phi) -
    MulOpposite.op (ksgnsOrderUnitInv phi hunit * phi x) • ksgnsCyclic phi

/-- Equation (2): exact weighted covariance Gram kernel on the actual complete minimal KSGNS
module. -/
theorem ksgnsWeightedCentered_inner (phi : A →CP B)
    (hunit : IsUnit (phi 1)) (x y : A) :
    (ksgnsRightInnerModuleData phi).inner
        (ksgnsWeightedCentered phi hunit x)
        (ksgnsWeightedCentered phi hunit y) =
      phi (star x * y) -
        star (phi x) * ksgnsOrderUnitInv phi hunit * phi y := by
  let M := ksgnsRightInnerModuleData phi
  let g := ksgnsOrderUnitInv phi hunit
  have hgstar : star g = g := star_ksgnsOrderUnitInv phi hunit
  have hgh : g * phi 1 = 1 := ksgnsOrderUnitInv_mul phi hunit
  have hcyc : M.inner (ksgnsCyclic phi) (ksgnsCyclic phi) = phi 1 := by
    exact ksgnsRight_inner_cyclic_cyclic phi
  change M.inner
      (ksgnsRepresentation phi x (ksgnsCyclic phi) -
        M.rmul (ksgnsCyclic phi) (g * phi x))
      (ksgnsRepresentation phi y (ksgnsCyclic phi) -
        M.rmul (ksgnsCyclic phi) (g * phi y)) = _
  rw [M.inner_sub_left, M.inner_sub_right, M.inner_sub_right,
    M.inner_rmul_right, M.inner_rmul_left,
    ksgnsRight_inner_rep_cyclic_rep_cyclic,
    ksgnsRight_inner_rep_cyclic_cyclic,
    ksgnsRight_inner_cyclic_rep_cyclic]
  rw [M.inner_rmul_right]
  rw [M.inner_rmul_left]
  rw [hcyc]
  change phi (star x * y) - star (phi x) * (g * phi y) -
      (star (g * phi x) * phi y -
        star (g * phi x) * phi 1 * (g * phi y)) =
    phi (star x * y) - star (phi x) * g * phi y
  rw [star_mul, hgstar]
  simp only [mul_assoc]
  have hcollapse : g * (phi 1 * (g * phi y)) = g * phi y := by
    rw [← mul_assoc, hgh, one_mul]
  rw [hcollapse]
  noncomm_ring

theorem norm_ksgnsCompleted_op_smul_le (phi : A →CP B) (b : Bᵐᵒᵖ)
    (x : KSGNS phi) :
    ‖b • x‖ ≤ ‖b‖ * ‖x‖ := by
  change ‖ksgnsCompletedActionCLM phi b x‖ ≤ ‖b‖ * ‖x‖
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp (ksgnsCompletedActionCLM phi b).continuous)
      (continuous_const.mul continuous_norm)
  · intro x
    rw [ksgnsCompletedActionCLM_coe]
    calc
      ‖((b • x : KSGNSSeparated phi) : KSGNS phi)‖ =
          ‖(b • x : KSGNSSeparated phi)‖ := Completion.norm_coe _
      _ ≤ ‖b‖ * ‖x‖ := norm_ksgnsSeparated_op_smul_le phi b x
      _ = ‖b‖ * ‖(x : KSGNS phi)‖ := by rw [Completion.norm_coe]

/-- Continuous coefficient-to-vector map `b ↦ v b`, encoded over the opposite algebra. -/
noncomputable def ksgnsCoefficientToVector (phi : A →CP B) (v : KSGNS phi) :
    Bᵐᵒᵖ →L[ℂ] KSGNS phi :=
  ({ toFun := fun b => b • v
     map_add' := fun b c => ksgnsCompleted_add_op_smul phi b c v
     map_smul' := fun q b => ksgnsCompleted_smul_op_smul phi q b v } :
      Bᵐᵒᵖ →ₗ[ℂ] KSGNS phi).mkContinuous ‖v‖ (by
        intro b
        simpa [mul_comm] using norm_ksgnsCompleted_op_smul_le phi b v)

@[simp]
theorem ksgnsCoefficientToVector_apply (phi : A →CP B) (v : KSGNS phi) (b : Bᵐᵒᵖ) :
    ksgnsCoefficientToVector phi v b = b • v := rfl

/-- Weighted cyclic-line projection `z ↦ ξ Φ(1)⁻¹⟨ξ,z⟩`. -/
noncomputable def ksgnsWeightedProjection (phi : A →CP B)
    (hunit : IsUnit (phi 1)) : KSGNS phi →L[ℂ] KSGNS phi :=
  (ksgnsCoefficientToVector phi
      (MulOpposite.op (ksgnsOrderUnitInv phi hunit) • ksgnsCyclic phi)).comp
    (ksgnsCompletedInnerSLM phi (ksgnsCyclic phi))

@[simp]
theorem ksgnsWeightedProjection_apply (phi : A →CP B)
    (hunit : IsUnit (phi 1)) (z : KSGNS phi) :
    ksgnsWeightedProjection phi hunit z =
      MulOpposite.op
          (ksgnsOrderUnitInv phi hunit *
            (ksgnsRightInnerModuleData phi).inner (ksgnsCyclic phi) z) •
        ksgnsCyclic phi := by
  change (MulOpposite.op
      ((ksgnsRightInnerModuleData phi).inner (ksgnsCyclic phi) z)) •
        (MulOpposite.op (ksgnsOrderUnitInv phi hunit) • ksgnsCyclic phi) = _
  rw [← ksgnsCompleted_mul_op_smul]
  rfl

theorem ksgnsWeightedProjection_rep_cyclic (phi : A →CP B)
    (hunit : IsUnit (phi 1)) (x : A) :
    ksgnsWeightedProjection phi hunit
        (ksgnsRepresentation phi x (ksgnsCyclic phi)) =
      MulOpposite.op (ksgnsOrderUnitInv phi hunit * phi x) •
        ksgnsCyclic phi := by
  rw [ksgnsWeightedProjection_apply,
    ksgnsRight_inner_cyclic_rep_cyclic]

theorem ksgnsWeightedCentered_eq_one_sub_projection (phi : A →CP B)
    (hunit : IsUnit (phi 1)) (x : A) :
    ksgnsWeightedCentered phi hunit x =
      ksgnsRepresentation phi x (ksgnsCyclic phi) -
        ksgnsWeightedProjection phi hunit
          (ksgnsRepresentation phi x (ksgnsCyclic phi)) := by
  rw [ksgnsWeightedCentered, ksgnsWeightedProjection_rep_cyclic]

theorem ksgnsWeightedProjection_idempotent (phi : A →CP B)
    (hunit : IsUnit (phi 1)) (z : KSGNS phi) :
    ksgnsWeightedProjection phi hunit (ksgnsWeightedProjection phi hunit z) =
      ksgnsWeightedProjection phi hunit z := by
  let M := ksgnsRightInnerModuleData phi
  let g := ksgnsOrderUnitInv phi hunit
  have hcyc : M.inner (ksgnsCyclic phi) (ksgnsCyclic phi) = phi 1 :=
    ksgnsRight_inner_cyclic_cyclic phi
  have hgh : g * phi 1 = 1 := ksgnsOrderUnitInv_mul phi hunit
  rw [ksgnsWeightedProjection_apply, ksgnsWeightedProjection_apply]
  change M.rmul (ksgnsCyclic phi)
      (g * M.inner (ksgnsCyclic phi)
        (M.rmul (ksgnsCyclic phi) (g * M.inner (ksgnsCyclic phi) z))) =
    M.rmul (ksgnsCyclic phi) (g * M.inner (ksgnsCyclic phi) z)
  rw [M.inner_rmul_right, hcyc]
  congr 1
  rw [← mul_assoc, hgh, one_mul]

theorem ksgnsWeightedProjection_selfAdjoint (phi : A →CP B)
    (hunit : IsUnit (phi 1)) (x y : KSGNS phi) :
    (ksgnsRightInnerModuleData phi).inner
        (ksgnsWeightedProjection phi hunit x) y =
      (ksgnsRightInnerModuleData phi).inner x
        (ksgnsWeightedProjection phi hunit y) := by
  let M := ksgnsRightInnerModuleData phi
  let g := ksgnsOrderUnitInv phi hunit
  have hgstar : star g = g := star_ksgnsOrderUnitInv phi hunit
  rw [ksgnsWeightedProjection_apply, ksgnsWeightedProjection_apply]
  change M.inner (M.rmul (ksgnsCyclic phi) (g * M.inner (ksgnsCyclic phi) x)) y =
    M.inner x (M.rmul (ksgnsCyclic phi) (g * M.inner (ksgnsCyclic phi) y))
  rw [M.inner_rmul_left, M.inner_rmul_right, star_mul, hgstar,
    M.star_inner]
  simp [mul_assoc]

end KSGNSCompletion

end GaloisForLFunctions.HTGeometry
