import GaloisForLFunctions.HTGeometry.KSGNSConstruction

open scoped CStarAlgebra

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {I B : Type*}
    [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A positive-definite B-valued kernel, stated directly through all finite Finsupp quadratic
forms. This is the exact Kolmogorov input for a Hilbert C-star module completion. -/
structure PositiveKernelData (I B : Type*) [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] where
  kernel : I → I → B
  kernel_star : ∀ i j, star (kernel i j) = kernel j i
  quadratic_nonneg : ∀ x : I →₀ B,
    0 ≤ x.sum fun i b => x.sum fun j c => star b * kernel i j * c

/-- Canonical B-valued sesquilinear form of a positive kernel. -/
def positiveKernelPreInner (K : PositiveKernelData I B) (x y : I →₀ B) : B :=
  x.sum fun i b => y.sum fun j c => star b * K.kernel i j * c

@[simp]
theorem positiveKernelPreInner_single_single (K : PositiveKernelData I B)
    (i j : I) (b c : B) :
    positiveKernelPreInner K (Finsupp.single i b) (Finsupp.single j c) =
      star b * K.kernel i j * c := by
  classical
  simp [positiveKernelPreInner]

theorem positiveKernelPreInner_self_nonneg (K : PositiveKernelData I B) (x : I →₀ B) :
    0 ≤ positiveKernelPreInner K x x := K.quadratic_nonneg x

/-- Pointwise right multiplication on the free positive-kernel module. -/
def positiveKernelPreRmul (x : I →₀ B) (b : B) : I →₀ B :=
  x.mapRange (fun c => c * b) (zero_mul b)

@[simp]
theorem positiveKernelPreRmul_apply (x : I →₀ B) (b : B) (i : I) :
    positiveKernelPreRmul x b i = x i * b := by
  classical
  simp [positiveKernelPreRmul]

@[simp]
theorem positiveKernelPreRmul_single (i : I) (b c : B) :
    positiveKernelPreRmul (Finsupp.single i b) c = Finsupp.single i (b * c) := by
  classical
  ext j
  by_cases h : i = j
  · subst j
    simp [positiveKernelPreRmul_apply]
  · simp [positiveKernelPreRmul_apply, h]

theorem positiveKernelPreInner_add_right (K : PositiveKernelData I B) (x y z : I →₀ B) :
    positiveKernelPreInner K x (y + z) =
      positiveKernelPreInner K x y + positiveKernelPreInner K x z := by
  classical
  change (∑ i ∈ x.support, (y + z).sum fun j c =>
      star (x i) * K.kernel i j * c) =
    (∑ i ∈ x.support, y.sum fun j c => star (x i) * K.kernel i j * c) +
    ∑ i ∈ x.support, z.sum fun j c => star (x i) * K.kernel i j * c
  have hinner : ∀ i : I,
      (y + z).sum (fun j c => star (x i) * K.kernel i j * c) =
        y.sum (fun j c => star (x i) * K.kernel i j * c) +
        z.sum (fun j c => star (x i) * K.kernel i j * c) := by
    intro i
    rw [Finsupp.sum_add_index]
    · intro j _
      simp
    · intro j _ b c
      simp [mul_add]
  simp_rw [hinner]
  exact Finset.sum_add_distrib

theorem positiveKernelPreInner_smul_right (K : PositiveKernelData I B)
    (q : ℂ) (x y : I →₀ B) :
    positiveKernelPreInner K x (q • y) = q • positiveKernelPreInner K x y := by
  classical
  change (∑ i ∈ x.support, (q • y).sum fun j c =>
      star (x i) * K.kernel i j * c) =
    q • ∑ i ∈ x.support, y.sum fun j c => star (x i) * K.kernel i j * c
  have hinner : ∀ i : I,
      (q • y).sum (fun j c => star (x i) * K.kernel i j * c) =
        q • y.sum (fun j c => star (x i) * K.kernel i j * c) := by
    intro i
    let kernel : I → B → B := fun j c => star (x i) * K.kernel i j * c
    have hadd (u v : I →₀ B) :
        (u + v).sum kernel = u.sum kernel + v.sum kernel := by
      rw [Finsupp.sum_add_index]
      · intro j _
        simp [kernel]
      · intro j _ b c
        simp [kernel, mul_add]
    induction y using Finsupp.induction_linear with
    | zero => simp [kernel]
    | add u v hu hv => rw [smul_add, hadd, hadd, hu, hv, smul_add]
    | single j c =>
        rw [Finsupp.smul_single]
        simp [kernel, mul_smul_comm]
  simp_rw [hinner]
  exact Finset.smul_sum.symm

theorem positiveKernelPreInner_rmul_right (K : PositiveKernelData I B)
    (x y : I →₀ B) (b : B) :
    positiveKernelPreInner K x (positiveKernelPreRmul y b) =
      positiveKernelPreInner K x y * b := by
  classical
  change (∑ i ∈ x.support, (positiveKernelPreRmul y b).sum fun j c =>
      star (x i) * K.kernel i j * c) =
    (∑ i ∈ x.support, y.sum fun j c => star (x i) * K.kernel i j * c) * b
  have hinner : ∀ i : I,
      (positiveKernelPreRmul y b).sum
        (fun j c => star (x i) * K.kernel i j * c) =
        y.sum (fun j c => star (x i) * K.kernel i j * c) * b := by
    intro i
    unfold positiveKernelPreRmul
    rw [Finsupp.sum_mapRange_index, Finsupp.sum_mul]
    apply Finsupp.sum_congr
    intro j hj
    simp [mul_assoc]
    · intro q
      simp
  simp_rw [hinner]
  rw [Finset.sum_mul]

theorem positiveKernelPreInner_star (K : PositiveKernelData I B) (x y : I →₀ B) :
    star (positiveKernelPreInner K x y) = positiveKernelPreInner K y x := by
  classical
  change star (∑ i ∈ x.support, ∑ j ∈ y.support,
      star (x i) * K.kernel i j * y j) =
    ∑ j ∈ y.support, ∑ i ∈ x.support,
      star (y j) * K.kernel j i * x i
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [K.kernel_star]
  simp [mul_assoc]

/-- Exact algebraic right-inner-module structure on the KSGNS free module. -/
def positiveKernelPreModuleData (K : PositiveKernelData I B) : RightInnerModuleData B (I →₀ B) where
  inner := positiveKernelPreInner K
  rmul := positiveKernelPreRmul
  inner_add_right := positiveKernelPreInner_add_right K
  inner_smul_right := positiveKernelPreInner_smul_right K
  inner_rmul_right := positiveKernelPreInner_rmul_right K
  star_inner := positiveKernelPreInner_star K
  rmul_one := by
    intro x
    ext a
    simp [positiveKernelPreRmul_apply]
  rmul_mul := by
    intro x b c
    ext a
    simp [positiveKernelPreRmul_apply, mul_assoc]
  rmul_add_left := by
    intro x y b
    ext a
    simp [positiveKernelPreRmul_apply, add_mul]
  rmul_add_right := by
    intro x b c
    ext a
    simp [positiveKernelPreRmul_apply, mul_add]
  rmul_smul := by
    intro c x b
    ext a
    simp [positiveKernelPreRmul_apply, smul_mul_assoc]

theorem positiveKernelPreInner_null_left (K : PositiveKernelData I B) {x : I →₀ B}
    (hxx : positiveKernelPreInner K x x = 0) (y : I →₀ B) :
    positiveKernelPreInner K x y = 0 := by
  let M := positiveKernelPreModuleData K
  let d : B := M.inner x y
  let c : B := M.inner y y
  change M.inner x x = 0 at hxx
  by_contra hd
  have hdpos : 0 < ‖d‖ ^ (2 : ℕ) := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg c
  let r : ℝ := ‖d‖ ^ (2 : ℕ) / (‖c‖ + 1)
  have hr : 0 < r := div_pos hdpos (by positivity)
  let z : I →₀ B := M.rmul x d - (r : ℂ) • y
  have hzpos : 0 ≤ M.inner z z := positiveKernelPreInner_self_nonneg K z
  have inner_smul_left (q : ℂ) (u v : I →₀ B) :
      M.inner (q • u) v = star q • M.inner u v := by
    rw [← M.star_inner, M.inner_smul_right, star_smul, M.star_inner]
  have hform : M.inner z z =
      (r ^ (2 : ℕ) : ℝ) • c - (2 * r : ℝ) • (star d * d) := by
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
  have hle : (2 * r : ℝ) • (star d * d) ≤ (r ^ (2 : ℕ) : ℝ) • c := by
    rw [hform] at hzpos
    exact sub_nonneg.mp hzpos
  have hleft : 0 ≤ (2 * r : ℝ) • (star d * d) :=
    smul_nonneg (by positivity) (star_mul_self_nonneg d)
  have hnorm := CStarAlgebra.norm_le_norm_of_nonneg_of_le hleft hle
  have hstar : ‖star d * d‖ = ‖d‖ ^ (2 : ℕ) := by
    rw [CStarRing.norm_star_mul_self]
    ring
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * r), abs_of_pos (sq_pos_of_pos hr), hstar] at hnorm
  have hrv : r * ‖c‖ < ‖d‖ ^ (2 : ℕ) := by
    dsimp [r]
    have hv : ‖c‖ / (‖c‖ + 1) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    rw [div_mul_eq_mul_div]
    calc
      ‖d‖ ^ (2 : ℕ) * ‖c‖ / (‖c‖ + 1) = ‖d‖ ^ (2 : ℕ) * (‖c‖ / (‖c‖ + 1)) := by ring
      _ < ‖d‖ ^ (2 : ℕ) * 1 := mul_lt_mul_of_pos_left hv hdpos
      _ = ‖d‖ ^ (2 : ℕ) := mul_one _
  have hbound : 2 * ‖d‖ ^ (2 : ℕ) ≤ r * ‖c‖ := by
    nlinarith [hnorm]
  nlinarith

theorem positiveKernelPreInner_add_left (K : PositiveKernelData I B) (x y z : I →₀ B) :
    positiveKernelPreInner K (x + y) z =
      positiveKernelPreInner K x z + positiveKernelPreInner K y z :=
  (positiveKernelPreModuleData K).inner_add_left x y z

theorem positiveKernelPreInner_sub_left (K : PositiveKernelData I B) (x y z : I →₀ B) :
    positiveKernelPreInner K (x - y) z =
      positiveKernelPreInner K x z - positiveKernelPreInner K y z :=
  (positiveKernelPreModuleData K).inner_sub_left x y z

theorem positiveKernelPreInner_sub_right (K : PositiveKernelData I B) (x y z : I →₀ B) :
    positiveKernelPreInner K x (y - z) =
      positiveKernelPreInner K x y - positiveKernelPreInner K x z :=
  (positiveKernelPreModuleData K).inner_sub_right x y z

theorem positiveKernelPreInner_smul_left (K : PositiveKernelData I B) (q : ℂ) (x y : I →₀ B) :
    positiveKernelPreInner K (q • x) y = star q • positiveKernelPreInner K x y := by
  rw [← positiveKernelPreInner_star, positiveKernelPreInner_smul_right, star_smul,
    positiveKernelPreInner_star]

theorem positiveKernelPreInner_rmul_left (K : PositiveKernelData I B) (x y : I →₀ B) (b : B) :
    positiveKernelPreInner K (positiveKernelPreRmul x b) y =
      star b * positiveKernelPreInner K x y :=
  (positiveKernelPreModuleData K).inner_rmul_left x y b

/-- Null radical of the positive KSGNS form. -/
def positiveKernelPreRadical (K : PositiveKernelData I B) : Submodule ℂ (I →₀ B) where
  carrier := {x | ∀ y, positiveKernelPreInner K x y = 0}
  zero_mem' := by
    intro y
    exact (positiveKernelPreModuleData K).inner_zero_left y
  add_mem' := by
    intro x y hx hy z
    rw [positiveKernelPreInner_add_left, hx z, hy z, add_zero]
  smul_mem' := by
    intro q x hx y
    rw [positiveKernelPreInner_smul_left, hx y]
    simp

theorem mem_positiveKernelPreRadical_iff_inner_self_eq_zero (K : PositiveKernelData I B) (x : I →₀ B) :
    x ∈ positiveKernelPreRadical K ↔ positiveKernelPreInner K x x = 0 := by
  constructor
  · intro hx
    exact hx x
  · intro hx y
    exact positiveKernelPreInner_null_left K hx y

/-- Separated algebraic KSGNS module, before Hilbert-module completion. -/
abbrev PositiveKernelSeparated (K : PositiveKernelData I B) :=
  (I →₀ B) ⧸ positiveKernelPreRadical K

/-- The B-valued inner product descended to the separated KSGNS quotient. -/
def positiveKernelSeparatedInner (K : PositiveKernelData I B) (u v : PositiveKernelSeparated K) : B :=
  Quotient.liftOn₂ u v (positiveKernelPreInner K) (by
    intro x y x' y' hx hy
    have hxeq : Submodule.Quotient.mk x =
        (Submodule.Quotient.mk x' : PositiveKernelSeparated K) := by
      exact Quotient.sound hx
    have hyeq : Submodule.Quotient.mk y =
        (Submodule.Quotient.mk y' : PositiveKernelSeparated K) := by
      exact Quotient.sound hy
    have hxmem : x - x' ∈ positiveKernelPreRadical K :=
      (Submodule.Quotient.eq (positiveKernelPreRadical K)).mp hxeq
    have hymem : y - y' ∈ positiveKernelPreRadical K :=
      (Submodule.Quotient.eq (positiveKernelPreRadical K)).mp hyeq
    have hx0 : positiveKernelPreInner K (x - x') y = 0 := hxmem y
    have hy0left : positiveKernelPreInner K (y - y') x' = 0 := hymem x'
    have hy0 : positiveKernelPreInner K x' (y - y') = 0 := by
      rw [← star_eq_zero, positiveKernelPreInner_star]
      exact hy0left
    have hxEq : positiveKernelPreInner K x y = positiveKernelPreInner K x' y := by
      rw [positiveKernelPreInner_sub_left] at hx0
      exact sub_eq_zero.mp hx0
    have hyEq : positiveKernelPreInner K x' y = positiveKernelPreInner K x' y' := by
      rw [positiveKernelPreInner_sub_right] at hy0
      exact sub_eq_zero.mp hy0
    exact hxEq.trans hyEq)

@[simp]
theorem positiveKernelSeparatedInner_mk (K : PositiveKernelData I B) (x y : I →₀ B) :
    positiveKernelSeparatedInner K (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      positiveKernelPreInner K x y := rfl

/-- Right multiplication as a complex-linear map on the free KSGNS module. -/
def positiveKernelPreRmulLinear (b : B) : (I →₀ B) →ₗ[ℂ] (I →₀ B) where
  toFun x := positiveKernelPreRmul x b
  map_add' := by
    intro x y
    ext a
    simp [positiveKernelPreRmul_apply, add_mul]
  map_smul' := by
    intro q x
    ext a
    simp [positiveKernelPreRmul_apply]

theorem positiveKernelPreRmul_mem_radical (K : PositiveKernelData I B) (b : B) {x : I →₀ B}
    (hx : x ∈ positiveKernelPreRadical K) :
    positiveKernelPreRmul x b ∈ positiveKernelPreRadical K := by
  intro y
  rw [positiveKernelPreInner_rmul_left, hx y, mul_zero]

/-- Right multiplication descended to the separated quotient. -/
def positiveKernelSeparatedRmul (K : PositiveKernelData I B) (b : B) :
    PositiveKernelSeparated K →ₗ[ℂ] PositiveKernelSeparated K :=
  (positiveKernelPreRadical K).mapQ (positiveKernelPreRadical K) (positiveKernelPreRmulLinear b) (by
    intro x hx
    exact positiveKernelPreRmul_mem_radical K b hx)

@[simp]
theorem positiveKernelSeparatedRmul_mk (K : PositiveKernelData I B) (b : B) (x : I →₀ B) :
    positiveKernelSeparatedRmul K b (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (positiveKernelPreRmul x b) := by
  exact Submodule.mapQ_apply _ _ _ _

instance positiveKernelSeparatedSMul (K : PositiveKernelData I B) :
    SMul Bᵐᵒᵖ (PositiveKernelSeparated K) where
  smul b x := positiveKernelSeparatedRmul K (MulOpposite.unop b) x

@[simp]
theorem positiveKernelSeparated_op_smul_mk (K : PositiveKernelData I B) (b : B) (x : I →₀ B) :
    MulOpposite.op b • (Submodule.Quotient.mk x : PositiveKernelSeparated K) =
      Submodule.Quotient.mk (positiveKernelPreRmul x b) := by
  exact positiveKernelSeparatedRmul_mk K b x

instance positiveKernelSeparatedInnerInstance (K : PositiveKernelData I B) :
    Inner Bᵐᵒᵖ (PositiveKernelSeparated K) where
  inner x y := MulOpposite.op (positiveKernelSeparatedInner K x y)

open scoped InnerProductSpace

@[simp]
theorem positiveKernelSeparated_inner_mk (K : PositiveKernelData I B) (x y : I →₀ B) :
    ⟪(Submodule.Quotient.mk x : PositiveKernelSeparated K), Submodule.Quotient.mk y⟫_Bᵐᵒᵖ =
      MulOpposite.op (positiveKernelPreInner K x y) := rfl

instance positiveKernelSeparatedNorm (K : PositiveKernelData I B) : Norm (PositiveKernelSeparated K) where
  norm x := Real.sqrt ‖positiveKernelSeparatedInner K x x‖

/-- The separated algebraic KSGNS quotient is a genuine (not yet complete) Hilbert C⋆-module over
the opposite coefficient algebra, which is the standard encoding of its right `B`-action. -/
instance positiveKernelSeparatedCStarModule (K : PositiveKernelData I B) :
    CStarModule Bᵐᵒᵖ (PositiveKernelSeparated K) where
  inner_add_right := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ x y z =>
      change MulOpposite.op (positiveKernelPreInner K x (y + z)) =
        MulOpposite.op (positiveKernelPreInner K x y) + MulOpposite.op (positiveKernelPreInner K x z)
      rw [positiveKernelPreInner_add_right]
      rfl
  inner_self_nonneg := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      change 0 ≤ MulOpposite.op (positiveKernelPreInner K x x)
      rw [MulOpposite.op_nonneg]
      exact positiveKernelPreInner_self_nonneg K x
  inner_self := by
    intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      constructor
      · intro hx
        have hx0 : positiveKernelPreInner K x x = 0 := by
          change MulOpposite.op (positiveKernelPreInner K x x) = 0 at hx
          have hu := congrArg MulOpposite.unop hx
          change positiveKernelPreInner K x x = 0 at hu
          exact hu
        change Submodule.Quotient.mk x = Submodule.Quotient.mk 0
        rw [Submodule.Quotient.eq]
        rw [sub_zero]
        exact (mem_positiveKernelPreRadical_iff_inner_self_eq_zero K x).2 hx0
      · intro hx
        rw [hx]
        change MulOpposite.op (positiveKernelPreInner K 0 0) = 0
        change MulOpposite.op (0 : B) = 0
        rfl
  inner_op_smul_right := by
    intro b x y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op
          (positiveKernelPreInner K x (positiveKernelPreRmul y (MulOpposite.unop b))) =
        b * MulOpposite.op (positiveKernelPreInner K x y)
      rw [positiveKernelPreInner_rmul_right]
      rfl
  inner_smul_right_complex := by
    intro q x y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op (positiveKernelPreInner K x (q • y)) =
        q • MulOpposite.op (positiveKernelPreInner K x y)
      rw [positiveKernelPreInner_smul_right]
      rfl
  star_inner := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op (star (positiveKernelPreInner K x y)) =
        MulOpposite.op (positiveKernelPreInner K y x)
      rw [positiveKernelPreInner_star]
  norm_eq_sqrt_norm_inner_self := by
    intro x
    change Real.sqrt ‖positiveKernelSeparatedInner K x x‖ =
      Real.sqrt ‖MulOpposite.op (positiveKernelSeparatedInner K x x)‖
    rw [MulOpposite.norm_op]

noncomputable instance positiveKernelSeparatedNormedAddCommGroup (K : PositiveKernelData I B) :
    NormedAddCommGroup (PositiveKernelSeparated K) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore Bᵐᵒᵖ)

noncomputable instance positiveKernelSeparatedNormedSpace (K : PositiveKernelData I B) :
    NormedSpace ℂ (PositiveKernelSeparated K) :=
  NormedSpace.ofCore (CStarModule.normedSpaceCore Bᵐᵒᵖ)

/-- Completed canonical Paschke--KSGNS Hilbert-module carrier. -/
abbrev PositiveKernelCompletion (K : PositiveKernelData I B) :=
  UniformSpace.Completion (PositiveKernelSeparated K)

section KSGNSCompletion

open UniformSpace

variable (K : PositiveKernelData I B)

/-- Algebraic sesquilinear inner-product map on the separated KSGNS module. -/
def positiveKernelSeparatedInnerLM :
    PositiveKernelSeparated K →ₗ⋆[ℂ] PositiveKernelSeparated K →ₗ[ℂ] Bᵐᵒᵖ where
  toFun x :=
    { toFun := fun y => MulOpposite.op (positiveKernelSeparatedInner K x y)
      map_add' := by
        intro y z
        induction x, y, z using Quotient.inductionOn₃ with
        | _ x y z =>
          change MulOpposite.op (positiveKernelPreInner K x (y + z)) =
            MulOpposite.op (positiveKernelPreInner K x y) +
              MulOpposite.op (positiveKernelPreInner K x z)
          rw [positiveKernelPreInner_add_right]
          rfl
      map_smul' := by
        intro q y
        induction x, y using Quotient.inductionOn₂ with
        | _ x y =>
          change MulOpposite.op (positiveKernelPreInner K x (q • y)) =
            q • MulOpposite.op (positiveKernelPreInner K x y)
          rw [positiveKernelPreInner_smul_right]
          rfl }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ x y z =>
      change MulOpposite.op (positiveKernelPreInner K (x + y) z) =
        MulOpposite.op (positiveKernelPreInner K x z) +
          MulOpposite.op (positiveKernelPreInner K y z)
      rw [positiveKernelPreInner_add_left]
      rfl
  map_smul' := by
    intro q x
    apply LinearMap.ext
    intro y
    induction x, y using Quotient.inductionOn₂ with
    | _ x y =>
      change MulOpposite.op (positiveKernelPreInner K (q • x) y) =
        starRingEnd ℂ q • MulOpposite.op (positiveKernelPreInner K x y)
      rw [positiveKernelPreInner_smul_left]
      rfl

/-- Inner product continuous in its second variable. -/
noncomputable def positiveKernelSeparatedInnerRightCLM (x : PositiveKernelSeparated K) :
    PositiveKernelSeparated K →L[ℂ] Bᵐᵒᵖ :=
  (positiveKernelSeparatedInnerLM K x).mkContinuous ‖x‖ (by
    intro y
    exact CStarModule.norm_inner_le (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K))

/-- Algebraic conjugate-linear dependence of the continuous second-variable map. -/
def positiveKernelSeparatedInnerRightLM :
    PositiveKernelSeparated K →ₛₗ[starRingEnd ℂ]
      (PositiveKernelSeparated K →L[ℂ] Bᵐᵒᵖ) where
  toFun := positiveKernelSeparatedInnerRightCLM K
  map_add' := by
    intro x y
    apply ContinuousLinearMap.ext
    intro z
    exact LinearMap.congr_fun (map_add (positiveKernelSeparatedInnerLM K) x y) z
  map_smul' := by
    intro q x
    apply ContinuousLinearMap.ext
    intro y
    exact LinearMap.congr_fun ((positiveKernelSeparatedInnerLM K).map_smulₛₗ q x) y

set_option maxHeartbeats 1000000 in
theorem norm_positiveKernelSeparated_inner_le (x y : PositiveKernelSeparated K) :
    ‖MulOpposite.op (positiveKernelSeparatedInner K x y)‖ ≤ ‖x‖ * ‖y‖ := by
  exact CStarModule.norm_inner_le (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K)

noncomputable def positiveKernelSeparatedInnerSLM :
    PositiveKernelSeparated K →SL[starRingEnd ℂ]
      PositiveKernelSeparated K →L[ℂ] Bᵐᵒᵖ :=
  CStarModule.innerSL (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K)

@[simp]
theorem positiveKernelSeparatedInnerSLM_apply (x y : PositiveKernelSeparated K) :
    positiveKernelSeparatedInnerSLM K x y = ⟪x, y⟫_Bᵐᵒᵖ := rfl

/-- Extend the second variable of the KSGNS inner product to the completion. -/
noncomputable def positiveKernelInnerRightCompletion (x : PositiveKernelSeparated K) :
    PositiveKernelCompletion K →L[ℂ] Bᵐᵒᵖ :=
  completionExtendSL (positiveKernelSeparatedInnerSLM K x)

@[simp]
theorem positiveKernelInnerRightCompletion_coe (x y : PositiveKernelSeparated K) :
    positiveKernelInnerRightCompletion K x (y : PositiveKernelCompletion K) = ⟪x, y⟫_Bᵐᵒᵖ := by
  rw [positiveKernelInnerRightCompletion, completionExtendSL_coe]
  rfl

theorem norm_positiveKernelInnerRightCompletion_le (x : PositiveKernelSeparated K) :
    ‖positiveKernelInnerRightCompletion K x‖ ≤ ‖x‖ := by
  apply (positiveKernelInnerRightCompletion K x).opNorm_le_bound
    (CStarModule.norm_nonneg Bᵐᵒᵖ)
  intro y
  refine Completion.induction_on y ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp (positiveKernelInnerRightCompletion K x).continuous)
      (continuous_const.mul continuous_norm)
  · intro y
    rw [positiveKernelInnerRightCompletion_coe, Completion.norm_coe]
    exact CStarModule.norm_inner_le (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K)

/-- Conjugate-linear dependence of the completed second-variable inner map. -/
noncomputable def positiveKernelInnerLeftLM :
    PositiveKernelSeparated K →ₛₗ[starRingEnd ℂ]
      (PositiveKernelCompletion K →L[ℂ] Bᵐᵒᵖ) where
  toFun := positiveKernelInnerRightCompletion K
  map_add' := by
    intro x y
    apply ContinuousLinearMap.ext
    intro z
    refine Completion.induction_on z ?_ ?_
    · exact isClosed_eq (positiveKernelInnerRightCompletion K (x + y)).continuous
        ((positiveKernelInnerRightCompletion K x).continuous.add
          (positiveKernelInnerRightCompletion K y).continuous)
    · intro z
      change positiveKernelInnerRightCompletion K (x + y) (z : PositiveKernelCompletion K) =
        positiveKernelInnerRightCompletion K x (z : PositiveKernelCompletion K) +
          positiveKernelInnerRightCompletion K y (z : PositiveKernelCompletion K)
      rw [positiveKernelInnerRightCompletion_coe, positiveKernelInnerRightCompletion_coe,
        positiveKernelInnerRightCompletion_coe]
      change ⟪x + y, z⟫_Bᵐᵒᵖ = ⟪x, z⟫_Bᵐᵒᵖ + ⟪y, z⟫_Bᵐᵒᵖ
      exact CStarModule.inner_add_left (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K)
        (x := x) (y := y) (z := z)
  map_smul' := by
    intro q x
    apply ContinuousLinearMap.ext
    intro y
    refine Completion.induction_on y ?_ ?_
    · exact isClosed_eq (positiveKernelInnerRightCompletion K (q • x)).continuous
        ((continuous_const_smul (starRingEnd ℂ q)).comp
          (positiveKernelInnerRightCompletion K x).continuous)
    · intro y
      change positiveKernelInnerRightCompletion K (q • x) (y : PositiveKernelCompletion K) =
        starRingEnd ℂ q • positiveKernelInnerRightCompletion K x (y : PositiveKernelCompletion K)
      rw [positiveKernelInnerRightCompletion_coe, positiveKernelInnerRightCompletion_coe]
      change ⟪q • x, y⟫_Bᵐᵒᵖ =
        starRingEnd ℂ q • ⟪x, y⟫_Bᵐᵒᵖ
      exact CStarModule.inner_smul_left_complex (A := Bᵐᵒᵖ)
        (E := PositiveKernelSeparated K) (z := q) (x := x) (y := y)

/-- Continuous first-variable map after completing the second variable. -/
noncomputable def positiveKernelInnerLeftSLM :
    PositiveKernelSeparated K →SL[starRingEnd ℂ]
      (PositiveKernelCompletion K →L[ℂ] Bᵐᵒᵖ) :=
  (positiveKernelInnerLeftLM K).mkContinuous 1 (by
    intro x
    change ‖positiveKernelInnerRightCompletion K x‖ ≤ 1 * ‖x‖
    simpa using norm_positiveKernelInnerRightCompletion_le K x)

/-- Completed B-valued KSGNS inner product, continuous in both variables. -/
noncomputable def positiveKernelCompletedInnerSLM :
    PositiveKernelCompletion K →SL[starRingEnd ℂ] (PositiveKernelCompletion K →L[ℂ] Bᵐᵒᵖ) :=
  completionExtendSL (positiveKernelInnerLeftSLM K)

@[simp]
theorem positiveKernelCompletedInnerSLM_coe (x : PositiveKernelSeparated K) :
    positiveKernelCompletedInnerSLM K (x : PositiveKernelCompletion K) = positiveKernelInnerRightCompletion K x := by
  rw [positiveKernelCompletedInnerSLM, completionExtendSL_coe]
  rfl

@[simp]
theorem positiveKernelCompletedInnerSLM_coe_coe (x y : PositiveKernelSeparated K) :
    positiveKernelCompletedInnerSLM K (x : PositiveKernelCompletion K) (y : PositiveKernelCompletion K) =
      ⟪x, y⟫_Bᵐᵒᵖ := by
  rw [positiveKernelCompletedInnerSLM_coe, positiveKernelInnerRightCompletion_coe]

theorem norm_positiveKernelSeparated_op_smul_le (b : Bᵐᵒᵖ) (x : PositiveKernelSeparated K) :
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
    _ = ‖b‖ ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) := by
          have hxnorm : ‖⟪x, x⟫_Bᵐᵒᵖ‖ = ‖x‖ ^ (2 : ℕ) :=
            (CStarModule.norm_sq_eq (A := Bᵐᵒᵖ) (x := x)).symm
          rw [norm_star, hxnorm]
          ring

/-- Bounded coefficient action on the separated module. -/
noncomputable def positiveKernelSeparatedActionCLM (b : Bᵐᵒᵖ) :
    PositiveKernelSeparated K →L[ℂ] PositiveKernelSeparated K :=
  (positiveKernelSeparatedRmul K (MulOpposite.unop b)).mkContinuous ‖b‖ (by
    intro x
    change ‖b • x‖ ≤ ‖b‖ * ‖x‖
    exact norm_positiveKernelSeparated_op_smul_le K b x)

@[simp]
theorem positiveKernelSeparatedActionCLM_apply (b : Bᵐᵒᵖ) (x : PositiveKernelSeparated K) :
    positiveKernelSeparatedActionCLM K b x = b • x := rfl

/-- Coefficient action extended to the Hilbert-module completion. -/
noncomputable def positiveKernelCompletedActionCLM (b : Bᵐᵒᵖ) :
    PositiveKernelCompletion K →L[ℂ] PositiveKernelCompletion K :=
  completionExtendSL
    ((completionCoeLinearIsometry (E := PositiveKernelSeparated K)).toContinuousLinearMap.comp
      (positiveKernelSeparatedActionCLM K b))

@[simp]
theorem positiveKernelCompletedActionCLM_coe (b : Bᵐᵒᵖ) (x : PositiveKernelSeparated K) :
    positiveKernelCompletedActionCLM K b (x : PositiveKernelCompletion K) =
      ((b • x : PositiveKernelSeparated K) : PositiveKernelCompletion K) := by
  rw [positiveKernelCompletedActionCLM, completionExtendSL_coe]
  rfl

noncomputable instance positiveKernelCompletedSMul : SMul Bᵐᵒᵖ (PositiveKernelCompletion K) :=
  ⟨fun b x => positiveKernelCompletedActionCLM K b x⟩

noncomputable instance positiveKernelCompletedInner : Inner Bᵐᵒᵖ (PositiveKernelCompletion K) :=
  ⟨fun x y => positiveKernelCompletedInnerSLM K x y⟩

@[simp]
theorem positiveKernelCompleted_inner_apply (x y : PositiveKernelCompletion K) :
    ⟪x, y⟫_Bᵐᵒᵖ = positiveKernelCompletedInnerSLM K x y := rfl

theorem continuous_positiveKernelCompleted_inner_pair :
    Continuous (fun p : PositiveKernelCompletion K × PositiveKernelCompletion K => ⟪p.1, p.2⟫_Bᵐᵒᵖ) := by
  exact ((positiveKernelCompletedInnerSLM K).continuous.comp continuous_fst).clm_apply
    continuous_snd

theorem continuous_positiveKernelCompleted_inner_self :
    Continuous (fun x : PositiveKernelCompletion K => ⟪x, x⟫_Bᵐᵒᵖ) := by
  exact (continuous_positiveKernelCompleted_inner_pair K).comp
    (continuous_id.prodMk continuous_id)

theorem positiveKernelCompleted_inner_add_right (x y z : PositiveKernelCompletion K) :
    ⟪x, y + z⟫_Bᵐᵒᵖ = ⟪x, y⟫_Bᵐᵒᵖ + ⟪x, z⟫_Bᵐᵒᵖ := by
  exact map_add (positiveKernelCompletedInnerSLM K x) y z

theorem positiveKernelCompleted_inner_smul_right_complex (q : ℂ) (x y : PositiveKernelCompletion K) :
    ⟪x, q • y⟫_Bᵐᵒᵖ = q • ⟪x, y⟫_Bᵐᵒᵖ := by
  exact map_smul (positiveKernelCompletedInnerSLM K x) q y

theorem positiveKernelCompleted_star_inner (x y : PositiveKernelCompletion K) :
    star ⟪x, y⟫_Bᵐᵒᵖ = ⟪y, x⟫_Bᵐᵒᵖ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      (continuous_star.comp (continuous_positiveKernelCompleted_inner_pair K))
      ((continuous_positiveKernelCompleted_inner_pair K).comp
        (continuous_snd.prodMk continuous_fst))
  · intro x y
    rw [positiveKernelCompleted_inner_apply, positiveKernelCompleted_inner_apply,
      positiveKernelCompletedInnerSLM_coe_coe, positiveKernelCompletedInnerSLM_coe_coe]
    exact CStarModule.star_inner (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K) x y

theorem positiveKernelCompleted_inner_self_nonneg (x : PositiveKernelCompletion K) :
    0 ≤ ⟪x, x⟫_Bᵐᵒᵖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_le continuous_const (continuous_positiveKernelCompleted_inner_self K)
  · intro x
    rw [positiveKernelCompleted_inner_apply, positiveKernelCompletedInnerSLM_coe_coe]
    exact CStarModule.inner_self_nonneg (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K)

theorem positiveKernelCompleted_norm_eq_sqrt_norm_inner_self (x : PositiveKernelCompletion K) :
    ‖x‖ = Real.sqrt ‖⟪x, x⟫_Bᵐᵒᵖ‖ := by
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq continuous_norm
      (Real.continuous_sqrt.comp
        (continuous_norm.comp (continuous_positiveKernelCompleted_inner_self K)))
  · intro x
    rw [Completion.norm_coe, positiveKernelCompleted_inner_apply,
      positiveKernelCompletedInnerSLM_coe_coe]
    exact CStarModule.norm_eq_sqrt_norm_inner_self
      (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K) x

theorem positiveKernelCompleted_inner_self (x : PositiveKernelCompletion K) :
    ⟪x, x⟫_Bᵐᵒᵖ = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply norm_eq_zero.mp
    rw [positiveKernelCompleted_norm_eq_sqrt_norm_inner_self K x, hx, norm_zero,
      Real.sqrt_zero]
  · rintro rfl
    simp only [positiveKernelCompleted_inner_apply, map_zero]

theorem positiveKernelCompleted_inner_op_smul_right (b : Bᵐᵒᵖ) (x y : PositiveKernelCompletion K) :
    ⟪x, b • y⟫_Bᵐᵒᵖ = b * ⟪x, y⟫_Bᵐᵒᵖ := by
  refine Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq
      ((continuous_positiveKernelCompleted_inner_pair K).comp
        (continuous_fst.prodMk
          ((positiveKernelCompletedActionCLM K b).continuous.comp continuous_snd)))
      (continuous_const.mul (continuous_positiveKernelCompleted_inner_pair K))
  · intro x y
    change positiveKernelCompletedInnerSLM K (x : PositiveKernelCompletion K)
        (positiveKernelCompletedActionCLM K b (y : PositiveKernelCompletion K)) =
      b * positiveKernelCompletedInnerSLM K (x : PositiveKernelCompletion K) (y : PositiveKernelCompletion K)
    rw [positiveKernelCompletedActionCLM_coe, positiveKernelCompletedInnerSLM_coe_coe,
      positiveKernelCompletedInnerSLM_coe_coe]
    exact CStarModule.inner_op_smul_right
      (A := Bᵐᵒᵖ) (E := PositiveKernelSeparated K)

noncomputable instance positiveKernelCompletedCStarModule : CStarModule Bᵐᵒᵖ (PositiveKernelCompletion K) where
  inner_add_right := positiveKernelCompleted_inner_add_right K _ _ _
  inner_self_nonneg := positiveKernelCompleted_inner_self_nonneg K _
  inner_self := positiveKernelCompleted_inner_self K _
  inner_op_smul_right := positiveKernelCompleted_inner_op_smul_right K _ _ _
  inner_smul_right_complex := positiveKernelCompleted_inner_smul_right_complex K _ _ _
  star_inner := positiveKernelCompleted_star_inner K
  norm_eq_sqrt_norm_inner_self := positiveKernelCompleted_norm_eq_sqrt_norm_inner_self K

end KSGNSCompletion

end GaloisForLFunctions.HTGeometry
