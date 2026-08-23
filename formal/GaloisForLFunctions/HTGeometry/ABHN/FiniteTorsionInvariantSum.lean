/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsion

/-!
# Finite-level invariant sums

For each positive or zero denominator `n`, finitely supported `ℚ/ℤ[n]` profiles have their own
additive sum and exact zero-sum presentation.  This is the finite-level target of ABHN.  It does
not identify any profile with a family of local Brauer classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Sum a finite profile with values already restricted to `ℚ/ℤ[n]`. -/
noncomputable def finsuppRatModIntNTorsionSumAddHom (ι : Type u) (n : ℕ) :
    (ι →₀ ratModIntNTorsion n) →+ ratModIntNTorsion n := by
  classical
  exact
    { toFun := fun f ↦ f.sum fun _ q ↦ q
      map_zero' := Finsupp.sum_zero_index
      map_add' := fun f g ↦ Finsupp.sum_add_index (by intros; rfl) (by intros; rfl) }

/-- A singleton finite-level profile sums to its one local value. -/
theorem finsuppRatModIntNTorsionSumAddHom_apply_single
    (ι : Type u) (n : ℕ) (i : ι) (q : ratModIntNTorsion n) :
    finsuppRatModIntNTorsionSumAddHom ι n (Finsupp.single i q) = q := by
  change (Finsupp.single i q).sum (fun _ q ↦ q) = q
  exact Finsupp.sum_single_index rfl

/-- A finite-level invariant sum is surjective as soon as the index type has one place. -/
theorem finsuppRatModIntNTorsionSumAddHom_surjective
    (ι : Type u) [Nonempty ι] (n : ℕ) :
    Function.Surjective (finsuppRatModIntNTorsionSumAddHom ι n) := by
  intro q
  let i : ι := Classical.choice inferInstance
  exact ⟨Finsupp.single i q, finsuppRatModIntNTorsionSumAddHom_apply_single ι n i q⟩

/-- Modulo finite-level zero-sum profiles, the `ℚ/ℤ[n]` profile group is canonically
`ℚ/ℤ[n]`. -/
noncomputable def finsuppRatModIntNTorsionSumQuotientAddEquiv
    (ι : Type u) [Nonempty ι] (n : ℕ) :
    ((ι →₀ ratModIntNTorsion n) ⧸
      (finsuppRatModIntNTorsionSumAddHom ι n).ker) ≃+ ratModIntNTorsion n :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (finsuppRatModIntNTorsionSumAddHom ι n)
    (finsuppRatModIntNTorsionSumAddHom_surjective ι n)

/-- The finite-level profile sum is exact after including its zero-sum subgroup. -/
theorem finsuppRatModIntNTorsionSum_zeroSum_exact
    (ι : Type u) (n : ℕ) :
    Function.Exact (finsuppRatModIntNTorsionSumAddHom ι n).ker.subtype
      (finsuppRatModIntNTorsionSumAddHom ι n) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact y.property

/-- The finite-level global additive character: first sum all local invariant values, then
apply the faithful standard character of `ℚ/ℤ[n]`. -/
noncomputable def finsuppRatModIntNTorsionStdAddChar
    (ι : Type u) (n : ℕ) (hn : n ≠ 0) :
    AddChar (ι →₀ ratModIntNTorsion n) ℂ :=
  (ratModIntNTorsionStdAddChar n hn).compAddMonoidHom
    (finsuppRatModIntNTorsionSumAddHom ι n)

/-- Finite-level additive reciprocity is exactly the product-one condition for the global
character.  This is target-side ABHN reciprocity; it does not identify the finite profile with
local Brauer classes. -/
theorem finsuppRatModIntNTorsionStdAddChar_eq_one_iff_sum_eq_zero
    (ι : Type u) (n : ℕ) (hn : n ≠ 0) (f : ι →₀ ratModIntNTorsion n) :
    finsuppRatModIntNTorsionStdAddChar ι n hn f = 1 ↔
      finsuppRatModIntNTorsionSumAddHom ι n f = 0 := by
  constructor
  · intro hf
    apply ratModIntNTorsionStdAddChar_injective n hn
    simpa [finsuppRatModIntNTorsionStdAddChar] using hf
  · intro hf
    rw [finsuppRatModIntNTorsionStdAddChar, AddChar.compAddMonoidHom_apply, hf]
    exact (ratModIntNTorsionStdAddChar n hn).map_zero_eq_one

/-- The global finite-level character is the product of its local character values. -/
theorem finsuppRatModIntNTorsionStdAddChar_eq_finsupp_prod
    (ι : Type u) (n : ℕ) (hn : n ≠ 0) (f : ι →₀ ratModIntNTorsion n) :
    finsuppRatModIntNTorsionStdAddChar ι n hn f =
      f.prod fun _ x ↦ ratModIntNTorsionStdAddChar n hn x := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [finsuppRatModIntNTorsionStdAddChar,
        finsuppRatModIntNTorsionSumAddHom]
  | single_add i x f hif hx ih =>
      rw [(finsuppRatModIntNTorsionStdAddChar ι n hn).map_add_eq_mul, ih,
        Finsupp.prod_add_index']
      · rw [finsuppRatModIntNTorsionStdAddChar,
          AddChar.compAddMonoidHom_apply,
          finsuppRatModIntNTorsionSumAddHom_apply_single,
          Finsupp.prod_single_index]
        exact (ratModIntNTorsionStdAddChar n hn).map_zero_eq_one
      · intro _
        exact (ratModIntNTorsionStdAddChar n hn).map_zero_eq_one
      · intro _ a b
        exact (ratModIntNTorsionStdAddChar n hn).map_add_eq_mul a b

/-- Finite-level reciprocity in its explicit local product form. -/
theorem finsuppRatModIntNTorsionStdAddChar_product_eq_one_iff_sum_eq_zero
    (ι : Type u) (n : ℕ) (hn : n ≠ 0) (f : ι →₀ ratModIntNTorsion n) :
    f.prod (fun _ x ↦ ratModIntNTorsionStdAddChar n hn x) = 1 ↔
      finsuppRatModIntNTorsionSumAddHom ι n f = 0 := by
  rw [← finsuppRatModIntNTorsionStdAddChar_eq_finsupp_prod,
    finsuppRatModIntNTorsionStdAddChar_eq_one_iff_sum_eq_zero]

/-- The global finite-level reciprocity character still has values among `n`th roots of unity. -/
theorem finsuppRatModIntNTorsionStdAddChar_pow_eq_one
    (ι : Type u) (n : ℕ) (hn : n ≠ 0) (f : ι →₀ ratModIntNTorsion n) :
    (finsuppRatModIntNTorsionStdAddChar ι n hn f) ^ n = 1 := by
  rw [← (finsuppRatModIntNTorsionStdAddChar ι n hn).map_nsmul_eq_pow]
  have hf : n • f = 0 := by
    ext i
    change n • (f i : RatModInt) = 0
    exact (f i).property
  rw [hf]
  exact (finsuppRatModIntNTorsionStdAddChar ι n hn).map_zero_eq_one

/-- Every finite `ℚ/ℤ` invariant profile lifts, with one common nonzero denominator, to a
finite torsion profile. -/
theorem finsupp_exists_finite_level_lift
    {ι : Type u} (x : ι →₀ RatModInt) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ y : ι →₀ ratModIntNTorsion n,
      ∀ i, (y i : RatModInt) = x i := by
  classical
  obtain ⟨n, hn, hxn⟩ := finsupp_exists_nonzero_common_ratModIntTorsion x
  let y : ι →₀ ratModIntNTorsion n :=
    Finsupp.mk x.support (fun i ↦ ⟨x i, hxn i⟩) (by
      intro i
      constructor
      · intro hi hzero
        have hval := congrArg Subtype.val hzero
        change x i = 0 at hval
        exact (Finsupp.mem_support_iff.mp hi) hval
      · intro hi
        apply Finsupp.mem_support_iff.mpr
        intro hzero
        apply hi
        exact Subtype.ext hzero)
  refine ⟨n, hn, y, ?_⟩
  intro i
  simp [y]

/-- Every finite-support reciprocal `ℚ/ℤ` profile has a finite torsion realization whose local
standard character values multiply to one.  This is the denominator-uniform finite target of
global reciprocity; no local Brauer or class-field-theory comparison is asserted. -/
theorem finsupp_reciprocity_exists_finite_level_product_character
    {ι : Type u} (x : ι →₀ RatModInt)
    (hx : x.sum (fun _ q ↦ q) = 0) :
    ∃ n : ℕ, ∃ hn : n ≠ 0, ∃ y : ι →₀ ratModIntNTorsion n,
      (∀ i, (y i : RatModInt) = x i) ∧
      y.prod (fun _ q ↦ ratModIntNTorsionStdAddChar n hn q) = 1 := by
  obtain ⟨n, hn, y, hy⟩ := finsupp_exists_finite_level_lift x
  refine ⟨n, hn, y, hy, ?_⟩
  rw [finsuppRatModIntNTorsionStdAddChar_product_eq_one_iff_sum_eq_zero]
  apply Subtype.ext
  unfold finsuppRatModIntNTorsionSumAddHom
  change ((y.sum (fun _ (q : ratModIntNTorsion n) ↦ q) : ratModIntNTorsion n) : RatModInt) = 0
  let hsub : ratModIntNTorsion n →+ RatModInt := (ratModIntNTorsion n).subtype
  have hsub_zero : hsub 0 = 0 := hsub.map_zero
  have hyval : Finsupp.mapRange hsub hsub_zero y = x := by
    ext i
    simp [hsub, hy i]
  change hsub (y.sum fun _ q ↦ q) = 0
  rw [map_finsuppSum hsub y (fun _ q ↦ q)]
  rw [← Finsupp.sum_mapRange_index (f := hsub) (hf := hsub_zero) (g := y) (h := fun _ q ↦ q)
    (by intro _; rfl), hyval]
  exact hx

end GaloisForLFunctions.HTGeometry.ABHN
