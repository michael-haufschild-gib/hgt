import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Projection

/-!
# Fitting decomposition for semilinear Frobenius

The kernel and image of every iterate of a semilinear endomorphism are
submodules when the scalar twist is an automorphism. On a finite-length
module both chains stabilize, and the stable kernel complements the stable
image. This gives the nilpotent/invertible splitting used for Frobenius in
§1 of Yang's *Finite torsion in Hodge--Witt cohomology groups*.

The argument works over the original scalar ring; restriction to integers
would not preserve finite length over an infinite residue field.
-/

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
variable (σ : R ≃+* R) (f : M →ₛₗ[σ.toRingHom] M)

/-- The integral linear map underlying a semilinear endomorphism. -/
def integralEnd : Module.End ℤ M := f.toAddMonoidHom.toIntLinearMap

/-- Iteration twists scalars by the same number of Frobenius iterates. -/
theorem integralEnd_pow_smul (n : ℕ) (a : R) (x : M) :
    (integralEnd σ f ^ n) (a • x) = (σ : R → R)^[n] a • (integralEnd σ f ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih,
        Function.iterate_succ_apply']
      exact f.map_smulₛₗ _ _

/-- Kernel of an iterate, with its original scalar structure retained. -/
def semilinearKerPow (n : ℕ) : Submodule R M where
  carrier := {x | (integralEnd σ f ^ n) x = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro x y hx hy
    change (integralEnd σ f ^ n) (x + y) = 0
    rw [map_add, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx
    change (integralEnd σ f ^ n) (a • x) = 0
    rw [integralEnd_pow_smul, hx, smul_zero]

/-- Image of an iterate; surjectivity of the scalar twist gives scalar closure. -/
def semilinearRangePow (n : ℕ) : Submodule R M where
  carrier := {x | ∃ y, (integralEnd σ f ^ n) y = x}
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, map_add _ _ _⟩
  smul_mem' := by
    rintro a x ⟨y, rfl⟩
    obtain ⟨b, hb⟩ := σ.surjective.iterate n a
    exact ⟨b • y, (integralEnd_pow_smul σ f n b y).trans (by rw [hb])⟩

theorem semilinearKerPow_monotone : Monotone (semilinearKerPow σ f) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  change (integralEnd σ f ^ (n + 1)) x = 0
  change (integralEnd σ f ^ n) x = 0 at hx
  rw [pow_succ', Module.End.mul_apply, hx, map_zero]

theorem semilinearRangePow_antitone : Antitone (semilinearRangePow σ f) := by
  apply antitone_nat_of_succ_le
  intro n x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨integralEnd σ f y, by rw [pow_succ, Module.End.mul_apply]⟩

/-- Both chains stabilize for a semilinear endomorphism of a finite-length module. -/
theorem semilinear_stabilization [IsNoetherian R M] [IsArtinian R M] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      semilinearKerPow σ f n = semilinearKerPow σ f m ∧
      semilinearRangePow σ f n = semilinearRangePow σ f m := by
  obtain ⟨a, ha⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R M) ⟨_, semilinearKerPow_monotone σ f⟩
  obtain ⟨b, hb⟩ := IsArtinian.monotone_stabilizes
    ⟨_, semilinearRangePow_antitone σ f⟩
  refine ⟨max a b, fun m hm => ⟨?_, ?_⟩⟩
  · exact (ha _ (le_max_left _ _)).symm.trans (ha m ((le_max_left _ _).trans hm))
  · exact (hb _ (le_max_right _ _)).symm.trans (hb m ((le_max_right _ _).trans hm))

/-- Sufficiently high iterates have complementary kernel and image over the original ring. -/
theorem semilinear_eventually_isCompl [IsNoetherian R M] [IsArtinian R M] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      IsCompl (semilinearKerPow σ f m) (semilinearRangePow σ f m) := by
  obtain ⟨n, hn⟩ := semilinear_stabilization σ f
  refine ⟨n, fun m hm => ?_⟩
  have hdouble := hn (m + m) (hm.trans (Nat.le_add_right m m))
  have hk : semilinearKerPow σ f m = semilinearKerPow σ f (m + m) :=
    (hn m hm).1.symm.trans hdouble.1
  have hr : semilinearRangePow σ f m = semilinearRangePow σ f (m + m) :=
    (hn m hm).2.symm.trans hdouble.2
  apply isCompl_iff.mpr
  constructor
  · apply Submodule.disjoint_def.mpr
    intro x hx hx'
    obtain ⟨y, hy⟩ := hx'
    have hyy : y ∈ semilinearKerPow σ f (m + m) := by
      change (integralEnd σ f ^ (m + m)) y = 0
      rw [pow_add, Module.End.mul_apply, hy]
      exact hx
    rw [← hk] at hyy
    exact hy.symm.trans hyy
  · apply codisjoint_iff.mpr
    apply Submodule.eq_top_iff'.mpr
    intro x
    have him : (integralEnd σ f ^ m) x ∈ semilinearRangePow σ f (m + m) := by
      rw [← hr]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := him
    apply Submodule.mem_sup.mpr
    refine ⟨x - (integralEnd σ f ^ m) y, ?_, (integralEnd σ f ^ m) y, ⟨y, rfl⟩,
      sub_add_cancel _ _⟩
    change (integralEnd σ f ^ m) (x - (integralEnd σ f ^ m) y) = 0
    rw [map_sub, ← Module.End.mul_apply, ← pow_add, hy, sub_self]

/-- Elements killed by some Frobenius iterate. -/
def semilinearNilpotentPart : Submodule R M := ⨆ n : ℕ, semilinearKerPow σ f n

/-- Elements lying in every Frobenius image. -/
def semilinearStablePart : Submodule R M := ⨅ n : ℕ, semilinearRangePow σ f n

/-- The stabilized kernel and image are independent of the stabilization exponent. -/
theorem semilinear_parts_eq_stabilized [IsNoetherian R M] [IsArtinian R M] :
    ∃ n : ℕ, semilinearNilpotentPart σ f = semilinearKerPow σ f n ∧
      semilinearStablePart σ f = semilinearRangePow σ f n := by
  obtain ⟨n, hn⟩ := semilinear_stabilization σ f
  refine ⟨n, le_antisymm (iSup_le fun m => ?_) (le_iSup _ n),
    le_antisymm (iInf_le _ n) (le_iInf fun m => ?_)⟩
  · by_cases h : m ≤ n
    · exact semilinearKerPow_monotone σ f h
    · exact le_of_eq ((hn m (Nat.le_of_not_ge h)).1.symm)
  · by_cases h : m ≤ n
    · exact semilinearRangePow_antitone σ f h
    · exact le_of_eq ((hn m (Nat.le_of_not_ge h)).2)

/-- Canonical semilinear Fitting decomposition, without linearizing the scalar twist. -/
theorem semilinear_isCompl [IsNoetherian R M] [IsArtinian R M] :
    IsCompl (semilinearNilpotentPart σ f) (semilinearStablePart σ f) := by
  obtain ⟨a, ha, ha'⟩ := semilinear_parts_eq_stabilized σ f
  obtain ⟨b, hb⟩ := semilinear_eventually_isCompl σ f
  have hka : semilinearKerPow σ f (max a b) = semilinearNilpotentPart σ f :=
    le_antisymm (le_iSup _ _) (ha ▸ semilinearKerPow_monotone σ f (le_max_left _ _))
  have hra : semilinearRangePow σ f (max a b) = semilinearStablePart σ f :=
    le_antisymm (ha' ▸ semilinearRangePow_antitone σ f (le_max_left _ _)) (iInf_le _ _)
  simpa only [hka, hra] using hb (max a b) (le_max_right _ _)

/-- The original module is the direct product of its Frobenius-nilpotent and stable parts. -/
noncomputable def semilinearFittingEquiv [IsNoetherian R M] [IsArtinian R M] :
    (semilinearNilpotentPart σ f × semilinearStablePart σ f) ≃ₗ[R] M :=
  Submodule.prodEquivOfIsCompl _ _ (semilinear_isCompl σ f)

/-- A single Frobenius power kills the entire nilpotent summand. -/
theorem semilinearNilpotentPart_nilpotent [IsNoetherian R M] [IsArtinian R M] :
    ∃ n : ℕ, ∀ x : semilinearNilpotentPart σ f, (integralEnd σ f ^ n) x.1 = 0 := by
  obtain ⟨n, hn, _⟩ := semilinear_parts_eq_stabilized σ f
  refine ⟨n, fun x => ?_⟩
  exact (le_of_eq hn) x.2

/-- Frobenius restricts to the stable-image summand, with its original scalar twist. -/
def semilinearStableEnd :
    semilinearStablePart σ f →ₛₗ[σ.toRingHom] semilinearStablePart σ f where
  toFun x := ⟨f x.1, by
    apply (Submodule.mem_iInf _).mpr
    intro n
    obtain ⟨y, hy⟩ := (Submodule.mem_iInf _).mp x.2 n
    refine ⟨f y, ?_⟩
    change (integralEnd σ f ^ n) (integralEnd σ f y) = integralEnd σ f x.1
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hy]⟩
  map_add' x y := Subtype.ext (f.map_add x.1 y.1)
  map_smul' a x := Subtype.ext (f.map_smulₛₗ a x.1)

/-- Frobenius is bijective on the stable summand. -/
theorem semilinearStableEnd_bijective [IsNoetherian R M] [IsArtinian R M] :
    Function.Bijective (semilinearStableEnd σ f) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    change f x.1 = f y.1 at he
    have hnil : x.1 - y.1 ∈ semilinearNilpotentPart σ f := by
      apply (le_iSup (semilinearKerPow σ f) 1)
      change f (x.1 - y.1) = 0
      rw [map_sub, he, sub_self]
    have hstable : x.1 - y.1 ∈ semilinearStablePart σ f :=
      (semilinearStablePart σ f).sub_mem x.2 y.2
    have hzero := Submodule.disjoint_def.mp
      (isCompl_iff.mp (semilinear_isCompl σ f)).1 (x.1 - y.1) hnil hstable
    exact Subtype.ext (sub_eq_zero.mp hzero)
  · intro x
    obtain ⟨n, _, hn⟩ := semilinear_parts_eq_stabilized σ f
    obtain ⟨y, hy⟩ := (Submodule.mem_iInf _).mp x.2 (n + 1)
    have hz : (integralEnd σ f ^ n) y ∈ semilinearStablePart σ f := by
      rw [hn]
      exact ⟨y, rfl⟩
    refine ⟨⟨(integralEnd σ f ^ n) y, hz⟩, Subtype.ext ?_⟩
    change integralEnd σ f ((integralEnd σ f ^ n) y) = x.1
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hy

private instance scalarTwistInvPair : RingHomInvPair σ.toRingHom σ.symm.toRingHom where
  comp_eq := by ext a; exact σ.symm_apply_apply a
  comp_eq₂ := by ext a; exact σ.apply_symm_apply a

private instance scalarTwistInvPairSymm : RingHomInvPair σ.symm.toRingHom σ.toRingHom where
  comp_eq := by ext a; exact σ.apply_symm_apply a
  comp_eq₂ := by ext a; exact σ.symm_apply_apply a

/-- The stable Frobenius summand carries a semilinear automorphism. -/
noncomputable def semilinearStableEquiv [IsNoetherian R M] [IsArtinian R M] :
    LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom)
      (semilinearStablePart σ f) (semilinearStablePart σ f) :=
  LinearEquiv.ofBijective (σ₂₁ := σ.symm.toRingHom)
    (semilinearStableEnd σ f) (semilinearStableEnd_bijective σ f)

#print axioms semilinear_eventually_isCompl
#print axioms semilinearFittingEquiv
#print axioms semilinearNilpotentPart_nilpotent
#print axioms semilinearStableEquiv

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt
