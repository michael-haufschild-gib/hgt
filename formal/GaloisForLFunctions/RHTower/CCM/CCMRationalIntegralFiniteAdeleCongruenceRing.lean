import GaloisForLFunctions.RHTower.CCM.CCMRationalProfiniteUnitCongruenceLift
import GaloisForLFunctions.RHTower.CCM.CCMRationalIntegralFiniteAdeleCyclicHaarAverage

/-!
# Multiplicative stability of congruence in integral finite adeles

The compact open `Z-hat` was originally bundled only as an additive subgroup,
because its Haar quotient was the first use.  Tate radialization also needs
the elementary but literal ring fact that congruence modulo `N Z-hat` is
preserved by multiplication by integral adeles, especially profinite units.

This file proves that fact directly in the restricted product, without
replacing the actual adelic subgroup by an abstract quotient ring.
-/

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct algebraMap Classical

namespace GaloisForLFunctions.RHTower

private abbrev IntegralFiniteAdeles :=
  ccmRationalIntegralFiniteAdelesAddSubgroup

/-- Product of two actual integral finite adeles, retained in the additive
subgroup carrier used by Haar theory. -/
def ccmRationalIntegralFiniteAdeleMul
    (x y : IntegralFiniteAdeles) : IntegralFiniteAdeles :=
  ⟨x.1 * y.1, fun v => mul_mem (x.2 v) (y.2 v)⟩

@[simp]
theorem ccmRationalIntegralFiniteAdeleMul_coe
    (x y : IntegralFiniteAdeles) :
    (ccmRationalIntegralFiniteAdeleMul x y : CCMRationalFiniteAdele) =
      x.1 * y.1 :=
  rfl

/-- Multiplication by a literal profinite unit on integral finite adeles. -/
def ccmRationalIntegralFiniteAdeleMulProfiniteUnit
    (x : IntegralFiniteAdeles) (u : CCMRationalProfiniteUnit) :
    IntegralFiniteAdeles :=
  ccmRationalIntegralFiniteAdeleMul x
    (ccmRationalProfiniteUnitIntegralVal u)

/-- Additive congruence modulo `N Z-hat` on the actual integral finite-adele
carrier. -/
def CCMRationalIntegralFiniteAdeleCongruent
    (N : ℕ) (x y : IntegralFiniteAdeles) : Prop :=
  ∃ z : IntegralFiniteAdeles, x - y = N • z

theorem ccmRationalIntegralFiniteAdeleCongruent_refl
    (N : ℕ) (x : IntegralFiniteAdeles) :
    CCMRationalIntegralFiniteAdeleCongruent N x x := by
  refine ⟨0, by simp⟩

theorem CCMRationalIntegralFiniteAdeleCongruent.symm
    {N : ℕ} {x y : IntegralFiniteAdeles}
    (h : CCMRationalIntegralFiniteAdeleCongruent N x y) :
    CCMRationalIntegralFiniteAdeleCongruent N y x := by
  obtain ⟨z, hz⟩ := h
  refine ⟨-z, ?_⟩
  rw [smul_neg, ← hz]
  abel

theorem CCMRationalIntegralFiniteAdeleCongruent.trans
    {N : ℕ} {x y z : IntegralFiniteAdeles}
    (hxy : CCMRationalIntegralFiniteAdeleCongruent N x y)
    (hyz : CCMRationalIntegralFiniteAdeleCongruent N y z) :
    CCMRationalIntegralFiniteAdeleCongruent N x z := by
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyz
  refine ⟨a + b, ?_⟩
  rw [smul_add, ← ha, ← hb]
  abel

/-- Congruence is stable under right multiplication by an integral finite
adele. -/
theorem CCMRationalIntegralFiniteAdeleCongruent.mul_right
    {N : ℕ} {x y : IntegralFiniteAdeles}
    (hxy : CCMRationalIntegralFiniteAdeleCongruent N x y)
    (b : IntegralFiniteAdeles) :
    CCMRationalIntegralFiniteAdeleCongruent N
      (ccmRationalIntegralFiniteAdeleMul x b)
      (ccmRationalIntegralFiniteAdeleMul y b) := by
  obtain ⟨z, hz⟩ := hxy
  refine ⟨ccmRationalIntegralFiniteAdeleMul z b, ?_⟩
  apply Subtype.ext
  change x.1 * b.1 - y.1 * b.1 = N • (z.1 * b.1)
  have hz' := congrArg Subtype.val hz
  change x.1 - y.1 = N • z.1 at hz'
  rw [← sub_mul, hz']
  simp only [nsmul_eq_mul]
  ring

/-- Congruence is stable under left multiplication by an integral finite
adele. -/
theorem CCMRationalIntegralFiniteAdeleCongruent.mul_left
    {N : ℕ} {x y : IntegralFiniteAdeles}
    (hxy : CCMRationalIntegralFiniteAdeleCongruent N x y)
    (b : IntegralFiniteAdeles) :
    CCMRationalIntegralFiniteAdeleCongruent N
      (ccmRationalIntegralFiniteAdeleMul b x)
      (ccmRationalIntegralFiniteAdeleMul b y) := by
  obtain ⟨z, hz⟩ := hxy
  refine ⟨ccmRationalIntegralFiniteAdeleMul b z, ?_⟩
  apply Subtype.ext
  change b.1 * x.1 - b.1 * y.1 = N • (b.1 * z.1)
  have hz' := congrArg Subtype.val hz
  change x.1 - y.1 = N • z.1 at hz'
  rw [← mul_sub, hz']
  simp only [nsmul_eq_mul]
  ring

/-- Canonical residue representatives equal in `ZMod N` are congruent as
literal diagonal integral finite adeles. -/
theorem ccmRationalIntegralFiniteAdeleDiagonal_congruent_of_intCast_eq
    {N : ℕ} {m n : ℤ} (hmn : (m : ZMod N) = (n : ZMod N)) :
    CCMRationalIntegralFiniteAdeleCongruent N
      (ccmRationalIntegralFiniteAdeleDiagonal m)
      (ccmRationalIntegralFiniteAdeleDiagonal n) := by
  let q := QuotientAddGroup.mk'
    (nsmulAddMonoidHom (α := IntegralFiniteAdeles) N).range
  have hq :
      q (ccmRationalIntegralFiniteAdeleDiagonal m) =
        q (ccmRationalIntegralFiniteAdeleDiagonal n) := by
    rw [← ccmRationalZModToIntegralFiniteAdeleQuotient_intCast,
      ← ccmRationalZModToIntegralFiniteAdeleQuotient_intCast, hmn]
  obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_iff_sub_mem).mp hq
  exact ⟨z, hz.symm⟩

/-- Canonical residue representatives equal in `ZMod N` are congruent as
literal diagonal integral finite adeles. -/
theorem ccmRationalIntegralFiniteAdeleDiagonal_congruent_of_zmod_eq
    {N : ℕ} {r s : ZMod N} (hrs : r = s) :
    CCMRationalIntegralFiniteAdeleCongruent N
      (ccmRationalIntegralFiniteAdeleDiagonal (r.val : ℤ))
      (ccmRationalIntegralFiniteAdeleDiagonal (s.val : ℤ)) := by
  subst s
  exact ccmRationalIntegralFiniteAdeleCongruent_refl N _

/-- The profinite lift of a finite unit is congruent to its canonical
diagonal representative in the multiplicatively stable relation. -/
theorem ccmRationalZModUnit_exists_profiniteUnit_integralCongruent
    (N : ℕ) (hN : N ≠ 0) (u : (ZMod N)ˣ) :
    ∃ v : CCMRationalProfiniteUnit,
      CCMRationalIntegralFiniteAdeleCongruent N
        (ccmRationalProfiniteUnitIntegralVal v)
        (ccmRationalIntegralFiniteAdeleDiagonal
          ((u : ZMod N).val : ℤ)) := by
  obtain ⟨v, z, hz⟩ :=
    ccmRationalZModUnit_exists_profiniteUnit_congruent N hN u
  exact ⟨v, z, hz⟩

end GaloisForLFunctions.RHTower
