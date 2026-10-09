import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.Circle

/-!
# Full crossed products by discrete abelian groups and their graded modular flows

For a C⋆-algebra `A` and an action `α` of a discrete abelian group `Γ` by `*`-automorphisms:

* the **algebraic crossed product** `A ⋊_alg Γ` is the finitely supported `∑ f_γ U_γ` with the
  twisted convolution `(a U_γ)(b U_δ) = a α_γ(b) U_{γ+δ}` and the involution
  `(a U_γ)* = α_{-γ}(a*) U_{-γ}`; it is a non-unital `*`-algebra and `a ↦ a U_0` embeds `A`;
* every Hilbert `*`-representation is contractive on monomials, `‖π(a U_γ)‖ ≤ ‖a‖` (C⋆-identity and
  contractivity of `*`-homomorphisms of C⋆-algebras), hence bounded by the `ℓ¹` norm;
* the **full crossed product** is the norm closure of the universal representation
  `x ↦ (π(x))_π` in `ℓ^∞(B(H_π))`: a C⋆-algebra whose norm is the supremum over all
  representations;
* **every `*`-automorphism of the algebraic crossed product extends** to an isometric
  `*`-automorphism of the full one (precomposition permutes the representations);
* a circle character `χ` of `Γ` gives the dual `*`-automorphism `a U_γ ↦ χ(γ) a U_γ`; for a real
  grading `ℓ : Γ → ℝ` and a grade `a ∈ ℝ` the **modular flow**
  `β^a_t(f U_γ) = exp(i t a ℓ(γ)) f U_γ` is a strongly continuous one-parameter group of
  `*`-automorphisms of the full crossed product;
* an action-reversing coefficient automorphism `R` (`R α_γ = α_{-γ} R`) induces the reflection
  `f U_γ ↦ R(f) U_{-γ}`, which conjugates `β^a` to `β^{-a}`;
* the complex-time scalings `f U_γ ↦ exp(i z a ℓ(γ)) f U_γ` are algebra automorphisms; at real
  time they are `β^a_t`, at `z = -i` they are the nonunitary scalings by `exp(a ℓ(γ))`.
-/

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

universe u

section Algebraic

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  (α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A))

/-- The action of `γ ∈ Γ` on the coefficient algebra. -/
def crossedAct (γ : Γ) : A ≃⋆ₐ[ℂ] A := α (Multiplicative.ofAdd γ)

theorem crossedAct_zero (a : A) : crossedAct α 0 a = a := by
  simp [crossedAct]

theorem crossedAct_add (γ δ : Γ) (a : A) :
    crossedAct α (γ + δ) a = crossedAct α γ (crossedAct α δ a) := by
  simp [crossedAct, ofAdd_add, map_mul, StarAlgEquiv.aut_mul]

theorem crossedAct_neg_cancel (γ : Γ) (a : A) : crossedAct α (-γ) (crossedAct α γ a) = a := by
  rw [← crossedAct_add, neg_add_cancel, crossedAct_zero]

theorem crossedAct_cancel_neg (γ : Γ) (a : A) : crossedAct α γ (crossedAct α (-γ) a) = a := by
  rw [← crossedAct_add, add_neg_cancel, crossedAct_zero]

/-- The algebraic crossed product `A ⋊_alg Γ`: finitely supported families `∑ f_γ U_γ`, for the
action `α`. -/
@[nolint unusedArguments]
def AlgCrossed (_α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A)) : Type u := Γ →₀ A

instance : AddCommGroup (AlgCrossed α) := inferInstanceAs (AddCommGroup (Γ →₀ A))
instance : Module ℂ (AlgCrossed α) := inferInstanceAs (Module ℂ (Γ →₀ A))

/-- The monomial `a U_γ`. -/
def AlgCrossed.single (γ : Γ) (a : A) : AlgCrossed α := Finsupp.single γ a

/-- The bilinear twisted convolution `(a U_γ)(b U_δ) = a α_γ(b) U_{γ+δ}`. -/
def crossedMulHom : (Γ →₀ A) →+ (Γ →₀ A) →+ (Γ →₀ A) :=
  Finsupp.liftAddHom fun γ =>
    (Finsupp.liftAddHom fun δ =>
      ((AddMonoidHom.mul.compr₂ (Finsupp.singleAddHom (γ + δ))).compl₂
        (crossedAct α γ : A →+ A)).flip).flip

instance : Mul (AlgCrossed α) := ⟨fun x y => crossedMulHom α x y⟩

/-- The involution `(a U_γ)* = α_{-γ}(a*) U_{-γ}`. -/
def crossedStarHom : (Γ →₀ A) →+ (Γ →₀ A) :=
  Finsupp.liftAddHom fun γ =>
    (Finsupp.singleAddHom (-γ)).comp
      ((crossedAct α (-γ) : A →+ A).comp (starAddEquiv : A ≃+ A).toAddMonoidHom)

instance : Star (AlgCrossed α) := ⟨fun x => crossedStarHom α x⟩

namespace AlgCrossed

theorem mul_def (x y : AlgCrossed α) : x * y = crossedMulHom α x y := rfl

theorem star_def (x : AlgCrossed α) : star x = crossedStarHom α x := rfl

theorem single_mul_single (γ δ : Γ) (a b : A) :
    single α γ a * single α δ b = single α (γ + δ) (a * crossedAct α γ b) := by
  simp [mul_def, single, crossedMulHom]

theorem star_single (γ : Γ) (a : A) :
    star (single α γ a) = single α (-γ) (crossedAct α (-γ) (star a)) := by
  simp [star_def, single, crossedStarHom]

theorem single_add (γ : Γ) (a b : A) : single α γ (a + b) = single α γ a + single α γ b :=
  Finsupp.single_add γ a b

theorem single_zero (γ : Γ) : single α γ (0 : A) = 0 := Finsupp.single_zero γ

theorem smul_single (c : ℂ) (γ : Γ) (a : A) : c • single α γ a = single α γ (c • a) :=
  Finsupp.smul_single c γ a

theorem mul_add (x y z : AlgCrossed α) : x * (y + z) = x * y + x * z := by
  rw [mul_def, mul_def, mul_def]
  exact map_add _ _ _

theorem add_mul (x y z : AlgCrossed α) : (x + y) * z = x * z + y * z := by
  rw [mul_def, mul_def, mul_def]
  exact DFunLike.congr_fun (map_add (crossedMulHom α) x y) z

theorem zero_mul (x : AlgCrossed α) : (0 : AlgCrossed α) * x = 0 := by
  rw [mul_def]
  exact DFunLike.congr_fun (map_zero (crossedMulHom α)) x

theorem mul_zero (x : AlgCrossed α) : x * 0 = 0 := by
  rw [mul_def]
  exact map_zero _

theorem star_add (x y : AlgCrossed α) : star (x + y) = star x + star y := by
  rw [star_def, star_def, star_def]
  exact map_add _ _ _

theorem star_zero : star (0 : AlgCrossed α) = 0 := by
  rw [star_def]
  exact map_zero _

/-- Induction over sums of monomials. -/
theorem induction {motive : AlgCrossed α → Prop} (x : AlgCrossed α) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (single : ∀ γ a, motive (single α γ a)) : motive x :=
  Finsupp.induction_linear (motive := motive) x zero add single

theorem mul_assoc (x y z : AlgCrossed α) : x * y * z = x * (y * z) := by
  induction x using induction α with
  | zero => simp only [zero_mul]
  | add x x' hx hx' => simp only [add_mul, hx, hx']
  | single γ a =>
    induction y using induction α with
    | zero => simp only [mul_zero, zero_mul]
    | add y y' hy hy' => simp only [mul_add, add_mul, hy, hy']
    | single δ b =>
      induction z using induction α with
      | zero => simp only [mul_zero]
      | add z z' hz hz' => simp only [mul_add, hz, hz']
      | single ε c =>
        rw [single_mul_single, single_mul_single, single_mul_single, single_mul_single,
          add_assoc, map_mul, crossedAct_add, _root_.mul_assoc]

theorem star_star (x : AlgCrossed α) : star (star x) = x := by
  induction x using induction α with
  | zero => simp only [star_zero]
  | add x x' hx hx' => simp only [star_add, hx, hx']
  | single γ a =>
    rw [star_single, star_single, neg_neg, ← map_star (crossedAct α (-γ)), _root_.star_star,
      crossedAct_cancel_neg]

theorem star_mul (x y : AlgCrossed α) : star (x * y) = star y * star x := by
  induction x using induction α with
  | zero => simp only [zero_mul, mul_zero, star_zero]
  | add x x' hx hx' => simp only [add_mul, mul_add, star_add, hx, hx']
  | single γ a =>
    induction y using induction α with
    | zero => simp only [mul_zero, zero_mul, star_zero]
    | add y y' hy hy' => simp only [mul_add, add_mul, star_add, hy, hy']
    | single δ b =>
      rw [single_mul_single, star_single, star_single, star_single, single_mul_single,
        StarMul.star_mul, map_mul, neg_add_rev]
      simp only [map_star, crossedAct_add, crossedAct_neg_cancel]

theorem smul_mul (c : ℂ) (x y : AlgCrossed α) : (c • x) * y = c • (x * y) := by
  induction x using induction α with
  | zero => simp only [smul_zero, zero_mul]
  | add x x' hx hx' => simp only [smul_add, add_mul, hx, hx']
  | single γ a =>
    induction y using induction α with
    | zero => simp only [mul_zero, smul_zero]
    | add y y' hy hy' => simp only [mul_add, smul_add, hy, hy']
    | single δ b =>
      rw [smul_single, single_mul_single, single_mul_single, smul_single, smul_mul_assoc]

theorem mul_smul (c : ℂ) (x y : AlgCrossed α) : x * (c • y) = c • (x * y) := by
  induction x using induction α with
  | zero => simp only [smul_zero, zero_mul]
  | add x x' hx hx' => simp only [smul_add, add_mul, hx, hx']
  | single γ a =>
    induction y using induction α with
    | zero => simp only [smul_zero, mul_zero]
    | add y y' hy hy' => simp only [mul_add, smul_add, hy, hy']
    | single δ b =>
      rw [smul_single, single_mul_single, single_mul_single, smul_single, map_smul,
        mul_smul_comm]

theorem star_smul (c : ℂ) (x : AlgCrossed α) : star (c • x) = star c • star x := by
  induction x using induction α with
  | zero => simp only [smul_zero, star_zero]
  | add x x' hx hx' => simp only [smul_add, star_add, hx, hx']
  | single γ a =>
    rw [smul_single, star_single, star_single, smul_single, StarModule.star_smul, map_smul]

end AlgCrossed

instance : NonUnitalRing (AlgCrossed α) where
  left_distrib := AlgCrossed.mul_add α
  right_distrib := AlgCrossed.add_mul α
  zero_mul := AlgCrossed.zero_mul α
  mul_zero := AlgCrossed.mul_zero α
  mul_assoc := AlgCrossed.mul_assoc α

instance : StarRing (AlgCrossed α) where
  star_involutive := AlgCrossed.star_star α
  star_mul := AlgCrossed.star_mul α
  star_add := AlgCrossed.star_add α

instance : IsScalarTower ℂ (AlgCrossed α) (AlgCrossed α) :=
  ⟨fun c x y => AlgCrossed.smul_mul α c x y⟩

instance : SMulCommClass ℂ (AlgCrossed α) (AlgCrossed α) :=
  ⟨fun c x y => (AlgCrossed.mul_smul α c x y).symm⟩

instance : StarModule ℂ (AlgCrossed α) := ⟨fun c x => AlgCrossed.star_smul α c x⟩

/-- The coefficient algebra embeds as the degree-zero part. -/
def crossedCoeff : A →⋆ₙₐ[ℂ] AlgCrossed α where
  toFun a := AlgCrossed.single α 0 a
  map_smul' c a := (AlgCrossed.smul_single α c 0 a).symm
  map_zero' := AlgCrossed.single_zero α 0
  map_add' a b := AlgCrossed.single_add α 0 a b
  map_mul' a b := by
    rw [AlgCrossed.single_mul_single, add_zero, crossedAct_zero]
  map_star' a := by
    rw [AlgCrossed.star_single, neg_zero, crossedAct_zero]

end Algebraic

/-! ## Hilbert representations and the universal norm -/

section Representations

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  (α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A))

/-- A `*`-representation of the algebraic crossed product on a Hilbert space. -/
structure CrossedRep where
  /-- The Hilbert space. -/
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  /-- The representation. -/
  π : AlgCrossed α →⋆ₙₐ[ℂ] (H →L[ℂ] H)

attribute [instance] CrossedRep.normed CrossedRep.inner CrossedRep.complete

variable {α}

/-- A `*`-automorphism of the coefficients is isometric. -/
theorem norm_starAlgEquiv_apply (e : A ≃⋆ₐ[ℂ] A) (a : A) : ‖e a‖ = ‖a‖ :=
  le_antisymm (NonUnitalStarAlgHom.norm_apply_le e a) (by
    simpa using NonUnitalStarAlgHom.norm_apply_le e.symm (e a))

/-- Every representation is contractive on monomials: `‖π(a U_γ)‖ ≤ ‖a‖`. -/
theorem CrossedRep.norm_single_le (ρ : CrossedRep α) (γ : Γ) (a : A) :
    ‖ρ.π (AlgCrossed.single α γ a)‖ ≤ ‖a‖ := by
  have hss : star (AlgCrossed.single α γ a) * AlgCrossed.single α γ a =
      crossedCoeff α (crossedAct α (-γ) (star a * a)) := by
    rw [AlgCrossed.star_single, AlgCrossed.single_mul_single, neg_add_cancel, map_mul]
    rfl
  have h2 : ‖ρ.π (AlgCrossed.single α γ a)‖ ^ 2 ≤ ‖a‖ ^ 2 := by
    rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul, hss, sq,
      ← CStarRing.norm_star_mul_self]
    calc ‖ρ.π (crossedCoeff α (crossedAct α (-γ) (star a * a)))‖
        ≤ ‖crossedAct α (-γ) (star a * a)‖ :=
          NonUnitalStarAlgHom.norm_apply_le (ρ.π.comp (crossedCoeff α)) _
      _ = ‖star a * a‖ := norm_starAlgEquiv_apply _ _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The `ℓ¹` norm `∑_γ ‖f_γ‖` of the algebraic crossed product. -/
def AlgCrossed.l1Norm (x : AlgCrossed α) : ℝ := (x : Γ →₀ A).sum fun _ a => ‖a‖

/-- Every representation is bounded by the `ℓ¹` norm. -/
theorem CrossedRep.norm_le_l1Norm (ρ : CrossedRep α) (x : AlgCrossed α) :
    ‖ρ.π x‖ ≤ AlgCrossed.l1Norm x := by
  have hx : x = (x : Γ →₀ A).sum fun γ a => AlgCrossed.single α γ a :=
    (Finsupp.sum_single (x : Γ →₀ A)).symm
  conv_lhs => rw [hx]
  unfold Finsupp.sum
  rw [map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun γ _ => ρ.norm_single_le γ _)

end Representations

/-! ## The full crossed product -/

section Full

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  (α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A))

/-- Bounded families `(T_ρ)_ρ` of operators indexed by all representations: `ℓ^∞(B(H_ρ))`. -/
def RepFamily : Type (u + 1) := lp (fun ρ : CrossedRep α => ρ.H →L[ℂ] ρ.H) ∞

instance : NonUnitalCStarAlgebra (RepFamily α) :=
  inferInstanceAs (NonUnitalCStarAlgebra (lp (fun ρ : CrossedRep α => ρ.H →L[ℂ] ρ.H) ∞))

variable {α} in
/-- The `ρ`-component of a bounded family. -/
def RepFamily.apply (y : RepFamily α) (ρ : CrossedRep α) : ρ.H →L[ℂ] ρ.H :=
  (show lp (fun ρ : CrossedRep α => ρ.H →L[ℂ] ρ.H) ∞ from y) ρ

variable {α} in
/-- A bounded family from a uniformly bounded choice of operators. -/
def RepFamily.ofBounded (f : ∀ ρ : CrossedRep α, ρ.H →L[ℂ] ρ.H) (C : ℝ) (hf : ∀ ρ, ‖f ρ‖ ≤ C) :
    RepFamily α :=
  (⟨f, memℓp_infty ⟨C, by rintro _ ⟨ρ, rfl⟩; exact hf ρ⟩⟩ :
    lp (fun ρ : CrossedRep α => ρ.H →L[ℂ] ρ.H) ∞)

namespace RepFamily

variable {α}

@[simp] theorem apply_ofBounded (f : ∀ ρ : CrossedRep α, ρ.H →L[ℂ] ρ.H) (C : ℝ)
    (hf : ∀ ρ, ‖f ρ‖ ≤ C) (ρ : CrossedRep α) : (ofBounded f C hf).apply ρ = f ρ := rfl

theorem ext {y z : RepFamily α} (h : ∀ ρ, y.apply ρ = z.apply ρ) : y = z :=
  lp.ext (funext h)

@[simp] theorem apply_add (y z : RepFamily α) (ρ : CrossedRep α) :
    (y + z).apply ρ = y.apply ρ + z.apply ρ := rfl
@[simp] theorem apply_zero (ρ : CrossedRep α) : (0 : RepFamily α).apply ρ = 0 := rfl
@[simp] theorem apply_mul (y z : RepFamily α) (ρ : CrossedRep α) :
    (y * z).apply ρ = y.apply ρ * z.apply ρ := rfl
@[simp] theorem apply_smul (c : ℂ) (y : RepFamily α) (ρ : CrossedRep α) :
    (c • y).apply ρ = c • y.apply ρ := rfl
@[simp] theorem apply_star (y : RepFamily α) (ρ : CrossedRep α) :
    (star y).apply ρ = star (y.apply ρ) := rfl

theorem norm_apply_le (y : RepFamily α) (ρ : CrossedRep α) : ‖y.apply ρ‖ ≤ ‖y‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero
    (show lp (fun ρ : CrossedRep α => ρ.H →L[ℂ] ρ.H) ∞ from y) ρ

theorem norm_le_of_forall_le {y : RepFamily α} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ρ, ‖y.apply ρ‖ ≤ C) : ‖y‖ ≤ C :=
  lp.norm_le_of_forall_le (f := (show lp (fun ρ : CrossedRep α => ρ.H →L[ℂ] ρ.H) ∞ from y)) hC h

end RepFamily

/-- The **universal representation** `x ↦ (ρ(x))_ρ`, bounded by the `ℓ¹` norm. -/
def universalRep : AlgCrossed α →⋆ₙₐ[ℂ] RepFamily α where
  toFun x := RepFamily.ofBounded (fun ρ => ρ.π x) (AlgCrossed.l1Norm x) fun ρ =>
    ρ.norm_le_l1Norm x
  map_smul' c x := RepFamily.ext fun ρ => by simp
  map_zero' := RepFamily.ext fun ρ => by simp
  map_add' x y := RepFamily.ext fun ρ => by simp
  map_mul' x y := RepFamily.ext fun ρ => by simp
  map_star' x := RepFamily.ext fun ρ => by
    rw [RepFamily.apply_star, RepFamily.apply_ofBounded, RepFamily.apply_ofBounded]
    exact map_star ρ.π x

@[simp]
theorem universalRep_apply (x : AlgCrossed α) (ρ : CrossedRep α) :
    (universalRep α x).apply ρ = ρ.π x := rfl

/-- The closure of the universal representation, as a closed `*`-subalgebra. -/
def fullCrossedSub : NonUnitalStarSubalgebra ℂ (RepFamily α) :=
  (NonUnitalStarAlgHom.range (universalRep α)).topologicalClosure

instance : IsClosed (fullCrossedSub α : Set (RepFamily α)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

theorem mem_fullCrossedSub_iff {y : RepFamily α} :
    y ∈ fullCrossedSub α ↔ y ∈ closure (Set.range (universalRep α)) := by
  rw [← NonUnitalStarAlgHom.coe_range]
  rfl

/-- **The full crossed product** `A ⋊ Γ`: the norm closure of the universal representation of the
algebraic crossed product.  Its norm is `‖x‖ = sup_ρ ‖ρ(x)‖` over all Hilbert representations. -/
def FullCrossed : Type (u + 1) := fullCrossedSub α

/-- The full crossed product is a C⋆-algebra. -/
noncomputable instance : NonUnitalCStarAlgebra (FullCrossed α) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (fullCrossedSub α)

variable {α}

/-- The underlying bounded family of an element of the full crossed product. -/
def FullCrossed.val (y : FullCrossed α) : RepFamily α := Subtype.val (p := (· ∈ fullCrossedSub α)) y

theorem FullCrossed.val_mem (y : FullCrossed α) : y.val ∈ fullCrossedSub α :=
  Subtype.property (p := (· ∈ fullCrossedSub α)) y

/-- An element of the full crossed product from a family in the closure. -/
def FullCrossed.mk (y : RepFamily α) (hy : y ∈ fullCrossedSub α) : FullCrossed α :=
  (⟨y, hy⟩ : fullCrossedSub α)

@[simp] theorem FullCrossed.val_mk (y : RepFamily α) (hy : y ∈ fullCrossedSub α) :
    (FullCrossed.mk y hy).val = y := rfl

theorem FullCrossed.val_injective : Function.Injective (FullCrossed.val (α := α)) :=
  Subtype.val_injective (p := (· ∈ fullCrossedSub α))

theorem FullCrossed.ext {y z : FullCrossed α} (h : y.val = z.val) : y = z :=
  FullCrossed.val_injective h

@[simp] theorem FullCrossed.val_add (y z : FullCrossed α) : (y + z).val = y.val + z.val := rfl
@[simp] theorem FullCrossed.val_zero : (0 : FullCrossed α).val = 0 := rfl
@[simp] theorem FullCrossed.val_mul (y z : FullCrossed α) : (y * z).val = y.val * z.val := rfl
@[simp] theorem FullCrossed.val_smul (c : ℂ) (y : FullCrossed α) : (c • y).val = c • y.val := rfl
@[simp] theorem FullCrossed.val_star (y : FullCrossed α) : (star y).val = star y.val := rfl
theorem FullCrossed.norm_val (y : FullCrossed α) : ‖y.val‖ = ‖y‖ := rfl

theorem FullCrossed.isInducing_val : Topology.IsInducing (FullCrossed.val (α := α)) :=
  Topology.IsInducing.subtypeVal

theorem FullCrossed.continuous_val : Continuous (FullCrossed.val (α := α)) :=
  FullCrossed.isInducing_val.continuous

variable (α)

theorem universalRep_mem (x : AlgCrossed α) : universalRep α x ∈ fullCrossedSub α :=
  NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨x, rfl⟩

/-- The canonical map of the algebraic crossed product into the full one. -/
def toFullCrossed : AlgCrossed α →⋆ₙₐ[ℂ] FullCrossed α where
  toFun x := FullCrossed.mk (universalRep α x) (universalRep_mem α x)
  map_smul' c x := FullCrossed.ext (map_smul (universalRep α) c x)
  map_zero' := FullCrossed.ext (map_zero (universalRep α))
  map_add' x y := FullCrossed.ext (map_add (universalRep α) x y)
  map_mul' x y := FullCrossed.ext (map_mul (universalRep α) x y)
  map_star' x := FullCrossed.ext (map_star (universalRep α) x)

@[simp] theorem toFullCrossed_val (x : AlgCrossed α) :
    (toFullCrossed α x).val = universalRep α x := rfl

theorem toFullCrossed_dense : DenseRange (toFullCrossed α) := by
  intro y
  rw [FullCrossed.isInducing_val.closure_eq_preimage_closure_image]
  have himg : FullCrossed.val '' Set.range (toFullCrossed α) = Set.range (universalRep α) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
  rw [Set.mem_preimage, himg, ← mem_fullCrossedSub_iff]
  exact y.val_mem

/-- The norm of the full crossed product is the supremum over all representations. -/
theorem norm_toFullCrossed (x : AlgCrossed α) :
    ‖toFullCrossed α x‖ = ‖universalRep α x‖ := rfl

theorem CrossedRep.norm_le_full (ρ : CrossedRep α) (x : AlgCrossed α) :
    ‖ρ.π x‖ ≤ ‖toFullCrossed α x‖ :=
  (universalRep α x).norm_apply_le ρ

end Full

/-! ## Dual actions: scaling the monomials by a character -/

section Scaling

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  (α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A))

/-- Scaling of the monomials by a character `ψ : Γ → ℂ`: `a U_γ ↦ ψ(γ) a U_γ`. -/
def charScaleHom (ψ : AddChar Γ ℂ) : (Γ →₀ A) →+ (Γ →₀ A) :=
  Finsupp.liftAddHom fun γ =>
    (Finsupp.singleAddHom γ).comp (DistribSMul.toAddMonoidHom A (ψ γ))

/-- The scaling as a map of the algebraic crossed product. -/
def charScale (ψ : AddChar Γ ℂ) (x : AlgCrossed α) : AlgCrossed α := charScaleHom ψ x

namespace AlgCrossed

theorem charScale_single (ψ : AddChar Γ ℂ) (γ : Γ) (a : A) :
    charScale α ψ (single α γ a) = single α γ (ψ γ • a) := by
  simp [charScale, charScaleHom, single]

theorem charScale_add (ψ : AddChar Γ ℂ) (x y : AlgCrossed α) :
    charScale α ψ (x + y) = charScale α ψ x + charScale α ψ y :=
  map_add (charScaleHom ψ) x y

theorem charScale_zero (ψ : AddChar Γ ℂ) : charScale α ψ (0 : AlgCrossed α) = 0 :=
  map_zero (charScaleHom (A := A) ψ)

theorem charScale_mul (ψ : AddChar Γ ℂ) (x y : AlgCrossed α) :
    charScale α ψ (x * y) = charScale α ψ x * charScale α ψ y := by
  induction x using induction α with
  | zero => simp only [zero_mul, charScale_zero]
  | add x x' hx hx' => simp only [add_mul, charScale_add, hx, hx']
  | single γ a =>
    induction y using induction α with
    | zero => simp only [mul_zero, charScale_zero]
    | add y y' hy hy' => simp only [mul_add, charScale_add, hy, hy']
    | single δ b =>
      rw [single_mul_single, charScale_single, charScale_single, charScale_single,
        single_mul_single, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
        AddChar.map_add_eq_mul]

theorem charScale_smul (ψ : AddChar Γ ℂ) (c : ℂ) (x : AlgCrossed α) :
    charScale α ψ (c • x) = c • charScale α ψ x := by
  induction x using induction α with
  | zero => simp only [smul_zero, charScale_zero]
  | add x x' hx hx' => simp only [smul_add, charScale_add, hx, hx']
  | single γ a =>
    rw [smul_single, charScale_single, charScale_single, smul_single, smul_comm]

theorem charScale_charScale (ψ φ : AddChar Γ ℂ) (x : AlgCrossed α) :
    charScale α ψ (charScale α φ x) = charScale α (ψ * φ) x := by
  induction x using induction α with
  | zero => simp only [charScale_zero]
  | add x x' hx hx' => simp only [charScale_add, hx, hx']
  | single γ a =>
    rw [charScale_single, charScale_single, charScale_single, smul_smul, AddChar.mul_apply]

theorem charScale_one (x : AlgCrossed α) : charScale α (1 : AddChar Γ ℂ) x = x := by
  induction x using induction α with
  | zero => simp only [charScale_zero]
  | add x x' hx hx' => simp only [charScale_add, hx, hx']
  | single γ a => rw [charScale_single, AddChar.one_apply, one_smul]

/-- A unitary character scales compatibly with the involution. -/
theorem charScale_star (ψ : AddChar Γ ℂ) (hψ : ∀ γ, ψ (-γ) = star (ψ γ))
    (x : AlgCrossed α) : charScale α ψ (star x) = star (charScale α ψ x) := by
  induction x using induction α with
  | zero => simp only [star_zero, charScale_zero]
  | add x x' hx hx' => simp only [star_add, charScale_add, hx, hx']
  | single γ a =>
    rw [star_single, charScale_single, charScale_single, star_single, StarModule.star_smul,
      map_smul, hψ]

end AlgCrossed

/-- The character `γ ↦ (χ(γ) : ℂ)` of a circle-valued character. -/
def circleCharToComplex (χ : AddChar Γ Circle) : AddChar Γ ℂ where
  toFun γ := (χ γ : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' γ δ := by simp [AddChar.map_add_eq_mul]

theorem circleCharToComplex_neg (χ : AddChar Γ Circle) (γ : Γ) :
    circleCharToComplex χ (-γ) = star (circleCharToComplex χ γ) := by
  change ((χ (-γ) : Circle) : ℂ) = star ((χ γ : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

theorem circleCharToComplex_mul (χ φ : AddChar Γ Circle) :
    circleCharToComplex (χ * φ) = circleCharToComplex χ * circleCharToComplex φ := by
  ext γ
  simp [circleCharToComplex, AddChar.mul_apply]

/-- **The dual action** of a circle character: the `*`-automorphism `a U_γ ↦ χ(γ) a U_γ`. -/
def dualTwist (χ : AddChar Γ Circle) : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α where
  toFun := charScale α (circleCharToComplex χ)
  invFun := charScale α (circleCharToComplex χ⁻¹)
  left_inv x := by
    rw [AlgCrossed.charScale_charScale, ← circleCharToComplex_mul, inv_mul_cancel]
    exact (congrArg (fun ψ => charScale α ψ x) (by ext γ; simp [circleCharToComplex])).trans
      (AlgCrossed.charScale_one α x)
  right_inv x := by
    rw [AlgCrossed.charScale_charScale, ← circleCharToComplex_mul, mul_inv_cancel]
    exact (congrArg (fun ψ => charScale α ψ x) (by ext γ; simp [circleCharToComplex])).trans
      (AlgCrossed.charScale_one α x)
  map_add' := AlgCrossed.charScale_add α _
  map_mul' := AlgCrossed.charScale_mul α _
  map_smul' := AlgCrossed.charScale_smul α _
  map_star' := AlgCrossed.charScale_star α _ (circleCharToComplex_neg χ)

theorem dualTwist_single (χ : AddChar Γ Circle) (γ : Γ) (a : A) :
    dualTwist α χ (AlgCrossed.single α γ a) = AlgCrossed.single α γ ((χ γ : ℂ) • a) :=
  AlgCrossed.charScale_single α _ γ a

theorem dualTwist_mul (χ φ : AddChar Γ Circle) (x : AlgCrossed α) :
    dualTwist α (χ * φ) x = dualTwist α χ (dualTwist α φ x) := by
  change charScale α _ x = charScale α _ (charScale α _ x)
  rw [AlgCrossed.charScale_charScale, circleCharToComplex_mul]

end Scaling

/-! ## Automorphisms extend to the full crossed product -/

section Extension

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  {α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A)}

/-- Precomposition of a representation with a `*`-automorphism. -/
def CrossedRep.precomp (ρ : CrossedRep α) (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) :
    CrossedRep α where
  H := ρ.H
  π := ρ.π.comp (θ : AlgCrossed α →⋆ₙₐ[ℂ] AlgCrossed α)

variable (α) in
/-- The permutation `(T_ρ)_ρ ↦ (T_{ρ ∘ θ})_ρ` of bounded families. -/
def repPermute (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) : RepFamily α →⋆ₙₐ[ℂ] RepFamily α where
  toFun y := RepFamily.ofBounded (fun ρ => y.apply (ρ.precomp θ)) ‖y‖ fun ρ =>
    y.norm_apply_le (ρ.precomp θ)
  map_smul' _ _ := RepFamily.ext fun _ => rfl
  map_zero' := RepFamily.ext fun _ => rfl
  map_add' _ _ := RepFamily.ext fun _ => rfl
  map_mul' _ _ := RepFamily.ext fun _ => rfl
  map_star' _ := RepFamily.ext fun _ => rfl

theorem repPermute_apply (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (y : RepFamily α)
    (ρ : CrossedRep α) : (repPermute α θ y).apply ρ = y.apply (ρ.precomp θ) := rfl

theorem norm_repPermute_le (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (y : RepFamily α) :
    ‖repPermute α θ y‖ ≤ ‖y‖ :=
  RepFamily.norm_le_of_forall_le (norm_nonneg y) fun ρ => y.norm_apply_le (ρ.precomp θ)

theorem continuous_repPermute (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) :
    Continuous (repPermute α θ) :=
  AddMonoidHomClass.continuous_of_bound (repPermute α θ) 1 fun y => by
    rw [one_mul]
    exact norm_repPermute_le θ y

theorem repPermute_universalRep (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (x : AlgCrossed α) :
    repPermute α θ (universalRep α x) = universalRep α (θ x) := rfl

theorem repPermute_mem (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) {y : RepFamily α}
    (hy : y ∈ fullCrossedSub α) : repPermute α θ y ∈ fullCrossedSub α := by
  rw [mem_fullCrossedSub_iff] at hy ⊢
  exact map_mem_closure (t := Set.range (universalRep α)) (continuous_repPermute θ) hy (by
    rintro _ ⟨x, rfl⟩
    exact ⟨θ x, rfl⟩)

variable (α) in
/-- The extension of a `*`-automorphism of the algebraic crossed product to the full one. -/
def fullExtend (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) :
    FullCrossed α →⋆ₙₐ[ℂ] FullCrossed α where
  toFun y := FullCrossed.mk (repPermute α θ y.val) (repPermute_mem θ y.val_mem)
  map_smul' c y := FullCrossed.ext (map_smul (repPermute α θ) c y.val)
  map_zero' := FullCrossed.ext (map_zero (repPermute α θ))
  map_add' y z := FullCrossed.ext (map_add (repPermute α θ) y.val z.val)
  map_mul' y z := FullCrossed.ext (map_mul (repPermute α θ) y.val z.val)
  map_star' y := FullCrossed.ext (map_star (repPermute α θ) y.val)

theorem fullExtend_toFullCrossed (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (x : AlgCrossed α) :
    fullExtend α θ (toFullCrossed α x) = toFullCrossed α (θ x) :=
  FullCrossed.ext (repPermute_universalRep θ x)

theorem continuous_fullExtend (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) :
    Continuous (fullExtend α θ) :=
  FullCrossed.isInducing_val.continuous_iff.mpr
    ((continuous_repPermute θ).comp FullCrossed.continuous_val)

/-- Two continuous maps out of the full crossed product agreeing on the algebraic crossed product
agree. -/
theorem fullCrossed_ext {X : Type*} [TopologicalSpace X] [T2Space X] {f g : FullCrossed α → X}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f (toFullCrossed α x) = g (toFullCrossed α x)) :
    f = g :=
  (toFullCrossed_dense α).equalizer hf hg (funext h)

theorem fullExtend_comp (θ θ' : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (y : FullCrossed α) :
    fullExtend α θ (fullExtend α θ' y) = fullExtend α (θ'.trans θ) y := by
  have := fullCrossed_ext ((continuous_fullExtend θ).comp (continuous_fullExtend θ'))
    (continuous_fullExtend (θ'.trans θ)) fun x => by
      simp only [Function.comp_apply, fullExtend_toFullCrossed]
      rfl
  exact congrFun this y

theorem fullExtend_of_forall_eq (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (hθ : ∀ x, θ x = x)
    (y : FullCrossed α) : fullExtend α θ y = y := by
  have := fullCrossed_ext (continuous_fullExtend θ) continuous_id fun x => by
    rw [fullExtend_toFullCrossed, hθ]
    rfl
  exact congrFun this y

variable (α) in
/-- **Every `*`-automorphism of the algebraic crossed product extends to a `*`-automorphism of the
full crossed product.** -/
def fullCrossedAut (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) : FullCrossed α ≃⋆ₐ[ℂ] FullCrossed α where
  toFun := fullExtend α θ
  invFun := fullExtend α θ.symm
  left_inv y := by
    rw [fullExtend_comp]
    exact fullExtend_of_forall_eq _ (fun x => θ.symm_apply_apply x) y
  right_inv y := by
    rw [fullExtend_comp]
    exact fullExtend_of_forall_eq _ (fun x => θ.apply_symm_apply x) y
  map_add' := map_add _
  map_mul' := map_mul _
  map_smul' := map_smul _
  map_star' := map_star _

theorem fullCrossedAut_toFullCrossed (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (x : AlgCrossed α) :
    fullCrossedAut α θ (toFullCrossed α x) = toFullCrossed α (θ x) :=
  fullExtend_toFullCrossed θ x

theorem fullCrossedAut_apply (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (y : FullCrossed α) :
    fullCrossedAut α θ y = fullExtend α θ y := rfl

theorem fullCrossedAut_trans (θ θ' : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (y : FullCrossed α) :
    fullCrossedAut α (θ'.trans θ) y = fullCrossedAut α θ (fullCrossedAut α θ' y) := by
  rw [fullCrossedAut_apply, fullCrossedAut_apply, fullCrossedAut_apply]
  exact (fullExtend_comp θ θ' y).symm

/-- The extended automorphisms are isometric. -/
theorem norm_fullCrossedAut (θ : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α) (y : FullCrossed α) :
    ‖fullCrossedAut α θ y‖ = ‖y‖ :=
  norm_starAlgEquiv_apply (fullCrossedAut α θ) y

end Extension

/-! ## Graded modular flows -/

section Flow

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  (α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A)) (ℓ : Γ →+ ℝ)

/-- The circle character `γ ↦ exp(i s ℓ(γ))` of a real grading `ℓ`. -/
def gradeChar (s : ℝ) : AddChar Γ Circle where
  toFun γ := Circle.exp (s * ℓ γ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' γ δ := by simp [mul_add, Circle.exp_add]

theorem gradeChar_apply (s : ℝ) (γ : Γ) :
    ((gradeChar ℓ s γ : Circle) : ℂ) = Complex.exp (↑(s * ℓ γ) * Complex.I) := rfl

theorem gradeChar_add (s s' : ℝ) : gradeChar ℓ (s + s') = gradeChar ℓ s * gradeChar ℓ s' := by
  ext γ
  simp [gradeChar, add_mul, Circle.exp_add, AddChar.mul_apply]

theorem gradeChar_zero : gradeChar ℓ 0 = 1 := by
  ext γ
  simp [gradeChar]

theorem gradeChar_neg (s : ℝ) : gradeChar ℓ (-s) = (gradeChar ℓ s)⁻¹ := by
  ext γ
  simp [gradeChar, AddChar.inv_apply]

/-- **The modular flow** `β^a_t(f U_γ) = exp(i t a ℓ(γ)) f U_γ` on the algebraic crossed product,
for a real grade `a`. -/
def modularFlow (a t : ℝ) : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α :=
  dualTwist α (gradeChar ℓ (t * a))

theorem modularFlow_single (a t : ℝ) (γ : Γ) (f : A) :
    modularFlow α ℓ a t (AlgCrossed.single α γ f) =
      AlgCrossed.single α γ (Complex.exp (↑(t * a * ℓ γ) * Complex.I) • f) :=
  dualTwist_single α _ γ f

theorem modularFlow_add (a s t : ℝ) (x : AlgCrossed α) :
    modularFlow α ℓ a (s + t) x = modularFlow α ℓ a s (modularFlow α ℓ a t x) := by
  rw [modularFlow, modularFlow, modularFlow, ← dualTwist_mul, add_mul, gradeChar_add]

theorem modularFlow_zero (a : ℝ) (x : AlgCrossed α) : modularFlow α ℓ a 0 x = x := by
  rw [modularFlow, zero_mul, gradeChar_zero]
  change charScale α _ x = x
  rw [show circleCharToComplex (1 : AddChar Γ Circle) = 1 by ext γ; simp [circleCharToComplex]]
  exact AlgCrossed.charScale_one α x

/-- The modular flow on the full crossed product. -/
def fullModularFlow (a t : ℝ) : FullCrossed α ≃⋆ₐ[ℂ] FullCrossed α :=
  fullCrossedAut α (modularFlow α ℓ a t)

theorem fullModularFlow_toFullCrossed (a t : ℝ) (x : AlgCrossed α) :
    fullModularFlow α ℓ a t (toFullCrossed α x) = toFullCrossed α (modularFlow α ℓ a t x) :=
  fullCrossedAut_toFullCrossed _ x

theorem continuous_fullModularFlow (a t : ℝ) : Continuous (fullModularFlow α ℓ a t) :=
  continuous_fullExtend _

/-- **Group law** of the modular flow on the full crossed product. -/
theorem fullModularFlow_add (a s t : ℝ) (y : FullCrossed α) :
    fullModularFlow α ℓ a (s + t) y = fullModularFlow α ℓ a s (fullModularFlow α ℓ a t y) := by
  have := fullCrossed_ext (continuous_fullModularFlow α ℓ a (s + t))
    ((continuous_fullModularFlow α ℓ a s).comp (continuous_fullModularFlow α ℓ a t)) fun x => by
      simp only [Function.comp_apply, fullModularFlow_toFullCrossed, modularFlow_add]
  exact congrFun this y

theorem fullModularFlow_zero (a : ℝ) (y : FullCrossed α) : fullModularFlow α ℓ a 0 y = y := by
  have := fullCrossed_ext (continuous_fullModularFlow α ℓ a 0) continuous_id fun x => by
    rw [fullModularFlow_toFullCrossed, modularFlow_zero]
    rfl
  exact congrFun this y

/-- The modular flow is isometric. -/
theorem dist_fullModularFlow (a t : ℝ) (y z : FullCrossed α) :
    dist (fullModularFlow α ℓ a t y) (fullModularFlow α ℓ a t z) = dist y z := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact norm_starAlgEquiv_apply _ _

theorem continuous_modularFlow_toFullCrossed (a : ℝ) (x : AlgCrossed α) :
    Continuous fun t => toFullCrossed α (modularFlow α ℓ a t x) := by
  induction x using AlgCrossed.induction α with
  | zero => simp only [map_zero]; exact continuous_const
  | add x x' hx hx' => simp only [map_add]; exact hx.add hx'
  | single γ f =>
    simp only [modularFlow_single, ← AlgCrossed.smul_single, map_smul]
    exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      ((continuous_id.mul continuous_const).mul continuous_const)).mul continuous_const)).smul
        continuous_const

/-- **Strong continuity**: `t ↦ β^a_t(y)` is norm continuous for every `y` of the full crossed
product, so `(FullCrossed α, β^a)` is a C⋆-dynamical system. -/
theorem continuous_fullModularFlow_apply (a : ℝ) (y : FullCrossed α) :
    Continuous fun t => fullModularFlow α ℓ a t y := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨x, hx⟩ := (toFullCrossed_dense α).exists_dist_lt y hε
  refine ⟨fun t => fullModularFlow α ℓ a t (toFullCrossed α x), ?_, fun t => hεu ?_⟩
  · simp only [fullModularFlow_toFullCrossed]
    exact continuous_modularFlow_toFullCrossed α ℓ a x
  · rw [dist_fullModularFlow]
    exact hx

end Flow

/-! ## Reflections conjugate the flow to the opposite grade -/

section Reflection

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  (α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A))

/-- A coefficient automorphism `R` reversing the action: `R ∘ α_γ = α_{-γ} ∘ R`. -/
def IsActionReversing (R : A ≃⋆ₐ[ℂ] A) : Prop :=
  ∀ γ a, R (crossedAct α γ a) = crossedAct α (-γ) (R a)

theorem IsActionReversing.symm {R : A ≃⋆ₐ[ℂ] A} (hR : IsActionReversing α R) :
    IsActionReversing α R.symm := by
  intro γ a
  have h := hR (-γ) (R.symm a)
  rw [neg_neg, StarAlgEquiv.apply_symm_apply] at h
  rw [← h, StarAlgEquiv.symm_apply_apply]

/-- The map `a U_γ ↦ R(a) U_{-γ}` on monomials, extended additively. -/
def reflectHom (R : A ≃⋆ₐ[ℂ] A) : (Γ →₀ A) →+ (Γ →₀ A) :=
  Finsupp.liftAddHom fun γ => (Finsupp.singleAddHom (-γ)).comp (R : A →+ A)

/-- The reflection as a map of the algebraic crossed product. -/
def reflectMap (R : A ≃⋆ₐ[ℂ] A) (x : AlgCrossed α) : AlgCrossed α := reflectHom R x

namespace AlgCrossed

theorem reflectMap_single (R : A ≃⋆ₐ[ℂ] A) (γ : Γ) (a : A) :
    reflectMap α R (single α γ a) = single α (-γ) (R a) := by
  simp [reflectMap, reflectHom, single]

theorem reflectMap_add (R : A ≃⋆ₐ[ℂ] A) (x y : AlgCrossed α) :
    reflectMap α R (x + y) = reflectMap α R x + reflectMap α R y := map_add (reflectHom R) x y

theorem reflectMap_zero (R : A ≃⋆ₐ[ℂ] A) : reflectMap α R (0 : AlgCrossed α) = 0 :=
  map_zero (reflectHom R)

variable {α}

theorem reflectMap_mul {R : A ≃⋆ₐ[ℂ] A} (hR : IsActionReversing α R) (x y : AlgCrossed α) :
    reflectMap α R (x * y) = reflectMap α R x * reflectMap α R y := by
  induction x using induction α with
  | zero => simp only [zero_mul, reflectMap_zero]
  | add x x' hx hx' => simp only [add_mul, reflectMap_add, hx, hx']
  | single γ a =>
    induction y using induction α with
    | zero => simp only [mul_zero, reflectMap_zero]
    | add y y' hy hy' => simp only [mul_add, reflectMap_add, hy, hy']
    | single δ b =>
      rw [single_mul_single, reflectMap_single, reflectMap_single, reflectMap_single,
        single_mul_single, map_mul, hR, neg_add]

theorem reflectMap_star {R : A ≃⋆ₐ[ℂ] A} (hR : IsActionReversing α R) (x : AlgCrossed α) :
    reflectMap α R (star x) = star (reflectMap α R x) := by
  induction x using induction α with
  | zero => simp only [star_zero, reflectMap_zero]
  | add x x' hx hx' => simp only [star_add, reflectMap_add, hx, hx']
  | single γ a =>
    rw [star_single, reflectMap_single, reflectMap_single, star_single, hR, map_star, neg_neg]

theorem reflectMap_smul (R : A ≃⋆ₐ[ℂ] A) (c : ℂ) (x : AlgCrossed α) :
    reflectMap α R (c • x) = c • reflectMap α R x := by
  induction x using induction α with
  | zero => simp only [smul_zero, reflectMap_zero]
  | add x x' hx hx' => simp only [smul_add, reflectMap_add, hx, hx']
  | single γ a => rw [smul_single, reflectMap_single, reflectMap_single, smul_single, map_smul]

theorem reflectMap_symm (R : A ≃⋆ₐ[ℂ] A) (x : AlgCrossed α) :
    reflectMap α R.symm (reflectMap α R x) = x := by
  induction x using induction α with
  | zero => simp only [reflectMap_zero]
  | add x x' hx hx' => simp only [reflectMap_add, hx, hx']
  | single γ a =>
    rw [reflectMap_single, reflectMap_single, neg_neg, StarAlgEquiv.symm_apply_apply]

end AlgCrossed

variable {α}

/-- **The reflection automorphism** `a U_γ ↦ R(a) U_{-γ}` of the algebraic crossed product, for an
action-reversing coefficient automorphism `R`. -/
def reflectAut {R : A ≃⋆ₐ[ℂ] A} (hR : IsActionReversing α R) : AlgCrossed α ≃⋆ₐ[ℂ] AlgCrossed α where
  toFun := reflectMap α R
  invFun := reflectMap α R.symm
  left_inv := AlgCrossed.reflectMap_symm R
  right_inv x := by
    simpa using AlgCrossed.reflectMap_symm R.symm x
  map_add' := AlgCrossed.reflectMap_add α R
  map_mul' := AlgCrossed.reflectMap_mul hR
  map_smul' := AlgCrossed.reflectMap_smul R
  map_star' := AlgCrossed.reflectMap_star hR

theorem reflectAut_single {R : A ≃⋆ₐ[ℂ] A} (hR : IsActionReversing α R) (γ : Γ) (a : A) :
    reflectAut hR (AlgCrossed.single α γ a) = AlgCrossed.single α (-γ) (R a) :=
  AlgCrossed.reflectMap_single α R γ a

/-- **The reflection conjugates the modular flow of grade `a` to the flow of grade `-a`**:
`R̃ ∘ β^a_t = β^{-a}_t ∘ R̃`. -/
theorem reflectAut_modularFlow {R : A ≃⋆ₐ[ℂ] A} (hR : IsActionReversing α R) (ℓ : Γ →+ ℝ)
    (a t : ℝ) (x : AlgCrossed α) :
    reflectAut hR (modularFlow α ℓ a t x) = modularFlow α ℓ (-a) t (reflectAut hR x) := by
  induction x using AlgCrossed.induction α with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | single γ f =>
    rw [modularFlow_single, reflectAut_single, reflectAut_single, modularFlow_single, map_smul,
      map_neg]
    congr 2
    push_cast
    ring_nf

/-- The reflection of the full crossed product conjugates the full flow of grade `a` to grade
`-a`. -/
theorem fullReflect_fullModularFlow {R : A ≃⋆ₐ[ℂ] A} (hR : IsActionReversing α R)
    (ℓ : Γ →+ ℝ) (a t : ℝ) (y : FullCrossed α) :
    fullCrossedAut α (reflectAut hR) (fullModularFlow α ℓ a t y) =
      fullModularFlow α ℓ (-a) t (fullCrossedAut α (reflectAut hR) y) := by
  have := fullCrossed_ext
    ((continuous_fullExtend (reflectAut hR)).comp (continuous_fullModularFlow α ℓ a t))
    ((continuous_fullModularFlow α ℓ (-a) t).comp (continuous_fullExtend (reflectAut hR)))
    fun x => by
      simp only [Function.comp_apply]
      rw [← fullCrossedAut_apply, ← fullCrossedAut_apply, fullModularFlow_toFullCrossed,
        fullCrossedAut_toFullCrossed, fullCrossedAut_toFullCrossed, fullModularFlow_toFullCrossed,
        reflectAut_modularFlow]
  exact congrFun this y

end Reflection

/-! ## Imaginary time: the nonunitary Euler scaling -/

section ImaginaryTime

variable {A : Type u} [NonUnitalCStarAlgebra A] {Γ : Type u} [AddCommGroup Γ]
  (α : Multiplicative Γ →* (A ≃⋆ₐ[ℂ] A)) (ℓ : Γ →+ ℝ)

/-- The complex-time character `γ ↦ exp(i z a ℓ(γ))`, `z ∈ ℂ`. -/
def complexTimeChar (a : ℝ) (z : ℂ) : AddChar Γ ℂ where
  toFun γ := Complex.exp (Complex.I * z * a * ℓ γ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' γ δ := by
    rw [map_add, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- At real time the complex-time character is the unitary character of the modular flow. -/
theorem complexTimeChar_real (a t : ℝ) :
    complexTimeChar ℓ a t = circleCharToComplex (gradeChar ℓ (t * a)) := by
  ext γ
  rw [show (circleCharToComplex (gradeChar ℓ (t * a))) γ = ((gradeChar ℓ (t * a) γ : Circle) : ℂ)
    from rfl, gradeChar_apply]
  simp only [complexTimeChar, AddChar.coe_mk]
  congr 1
  push_cast
  ring

/-- **At imaginary time `z = -i` the flow is the Euler scaling** `f U_γ ↦ exp(a ℓ(γ)) f U_γ`. -/
theorem complexTimeChar_neg_I (a : ℝ) (γ : Γ) :
    complexTimeChar ℓ a (-Complex.I) γ = ((Real.exp (a * ℓ γ) : ℝ) : ℂ) := by
  simp only [complexTimeChar, AddChar.coe_mk]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The complex-time scaling is a multiplicative `ℂ`-linear bijection of the algebraic crossed
product for every complex time (an algebra automorphism, not a `*`-automorphism in general). -/
theorem complexTime_mul (a : ℝ) (z : ℂ) (x y : AlgCrossed α) :
    charScale α (complexTimeChar ℓ a z) (x * y) =
      charScale α (complexTimeChar ℓ a z) x * charScale α (complexTimeChar ℓ a z) y :=
  AlgCrossed.charScale_mul α _ x y

theorem complexTime_bijective (a : ℝ) (z : ℂ) :
    Function.Bijective (charScale α (complexTimeChar ℓ a z)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨charScale α (complexTimeChar ℓ a z)⁻¹, ?_, ?_⟩
  · intro x
    rw [AlgCrossed.charScale_charScale, inv_mul_cancel, AlgCrossed.charScale_one]
  · intro x
    rw [AlgCrossed.charScale_charScale, mul_inv_cancel, AlgCrossed.charScale_one]

end ImaginaryTime

end GaloisForLFunctions.HTGeometry
