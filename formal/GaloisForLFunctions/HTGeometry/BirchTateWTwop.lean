import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# The p-primary Birch--Tate denominator

For a field `F` and a rational prime `p`, this module constructs
`H⁰(F, ℚ_p/ℤ_p(2))`: the fixed submodule of `ℚ_p/ℤ_p` for the square of the `p`-adic
cyclotomic character. Its order is the `p`-primary contribution to the Birch--Tate integer `w₂(F)`.
-/

namespace GaloisForLFunctions.HTGeometry

variable (p : ℕ) [Fact p.Prime]

/-- The integral lattice `ℤ_p ⊂ ℚ_p`, regarded as an `ℤ_p`-submodule. -/
noncomputable def padicIntegralSubmodule : Submodule ℤ_[p] ℚ_[p] :=
  LinearMap.range (Algebra.linearMap ℤ_[p] ℚ_[p])

theorem mem_padicIntegralSubmodule_iff (x : ℚ_[p]) :
    x ∈ padicIntegralSubmodule p ↔ ‖x‖ ≤ 1 := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The discrete `p`-primary Tate module `ℚ_p/ℤ_p`. -/
abbrev PadicTateQuotient := ℚ_[p] ⧸ padicIntegralSubmodule p

/-- Every element of `ℚ_p` becomes integral after multiplication by a sufficiently large power
of `p`. -/
theorem exists_pow_smul_mem_padicIntegralSubmodule (q : ℚ_[p]) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • q ∈ padicIntegralSubmodule p := by
  by_cases hq : q = 0
  · exact ⟨0, by simp [hq]⟩
  by_cases hv : 0 ≤ q.valuation
  · refine ⟨0, ?_⟩
    simpa using (mem_padicIntegralSubmodule_iff p q).2
      ((Padic.norm_le_one_iff_val_nonneg q).2 hv)
  · let n := Int.toNat (-q.valuation)
    refine ⟨n, (mem_padicIntegralSubmodule_iff p _).2 ?_⟩
    have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    change ‖(p : ℚ_[p]) ^ n * q‖ ≤ 1
    rw [Padic.norm_le_one_iff_val_nonneg,
      Padic.valuation_mul (pow_ne_zero n hp) hq, Padic.valuation_pow, Padic.valuation_p]
    have hneg : 0 ≤ -q.valuation := neg_nonneg.mpr (le_of_not_ge hv)
    rw [show (n : ℤ) = -q.valuation by exact Int.toNat_of_nonneg hneg]
    simp

/-- `ℚ_p/ℤ_p` is `p`-primary torsion: every class is killed by a power of `p`. -/
theorem exists_pow_smul_eq_zero_padicTateQuotient (x : PadicTateQuotient p) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ q =>
      obtain ⟨n, hn⟩ := exists_pow_smul_mem_padicIntegralSubmodule p q
      refine ⟨n, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hn

/-- A nonzero principal quotient of `ℤ_p` is the cyclic group of order `p^v(a)`. -/
noncomputable def padicIntQuotientEquivZModPow (a : ℤ_[p]) (ha : a ≠ 0) :
    ℤ_[p] ⧸ (Ideal.span ({a} : Set ℤ_[p])).toAddSubgroup ≃+
      ZMod (p ^ a.valuation) := by
  let e := a.valuation
  let f := PadicInt.toZModPow (p := p) e
  have hassoc : Associated a ((p : ℤ_[p]) ^ e) := by
    rw [PadicInt.unitCoeff_spec ha]
    exact associated_unit_mul_left _ _ (PadicInt.unitCoeff ha).isUnit
  have hker : (Ideal.span ({a} : Set ℤ_[p])).toAddSubgroup =
      f.toAddMonoidHom.ker := by
    rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc]
    ext x
    change x ∈ Ideal.span {((p : ℤ_[p]) ^ e)} ↔
      x ∈ RingHom.ker (PadicInt.toZModPow e)
    exact (SetLike.ext_iff.mp (PadicInt.ker_toZModPow e) x).symm
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f.toAddMonoidHom
      (ZMod.ringHom_surjective f))

theorem padicIntQuotientSpan_card (a : ℤ_[p]) (ha : a ≠ 0) :
    Nat.card (ℤ_[p] ⧸ (Ideal.span ({a} : Set ℤ_[p])).toAddSubgroup) =
      p ^ a.valuation := by
  rw [Nat.card_congr (padicIntQuotientEquivZModPow p a ha).toEquiv]
  exact Nat.card_zmod _

/-- Parameterization of the `a`-torsion in `ℚ_p/ℤ_p` by integral numerators. -/
noncomputable def padicTateTorsionParam (a : ℤ_[p]) (ha : a ≠ 0) :
    ℤ_[p] →+ Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) a where
  toFun z := ⟨z • Submodule.Quotient.mk ((a : ℚ_[p])⁻¹), by
    rw [Submodule.mem_torsionBy_iff, smul_smul, mul_comm, ← smul_smul]
    suffices a • (Submodule.Quotient.mk ((a : ℚ_[p])⁻¹) : PadicTateQuotient p) = 0 by
      simp [this]
    rw [← Submodule.Quotient.mk_smul, Algebra.smul_def]
    change Submodule.Quotient.mk ((a : ℚ_[p]) * (a : ℚ_[p])⁻¹) = 0
    rw [mul_inv_cancel₀ (PadicInt.coe_ne_zero.mpr ha), Submodule.Quotient.mk_eq_zero,
      mem_padicIntegralSubmodule_iff]
    simp⟩
  map_zero' := by ext; simp
  map_add' z w := by ext; simp [add_smul]

theorem ker_padicTateTorsionParam (a : ℤ_[p]) (ha : a ≠ 0) :
    (padicTateTorsionParam p a ha).ker =
      (Ideal.span ({a} : Set ℤ_[p])).toAddSubgroup := by
  ext z
  rw [AddMonoidHom.mem_ker]
  simp only [padicTateTorsionParam]
  rw [Subtype.ext_iff]
  change (Submodule.Quotient.mk ((z : ℚ_[p]) * (a : ℚ_[p])⁻¹) :
      PadicTateQuotient p) = 0 ↔ z ∈ Ideal.span ({a} : Set ℤ_[p])
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨c, hc⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    apply Subtype.coe_injective
    change (z : ℚ_[p]) = (a : ℚ_[p]) * (c : ℚ_[p])
    change (c : ℚ_[p]) = (z : ℚ_[p]) * (a : ℚ_[p])⁻¹ at hc
    rw [hc]
    field_simp [PadicInt.coe_ne_zero.mpr ha]
  · rw [Ideal.mem_span_singleton]
    rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    change (c : ℚ_[p]) = (a * c : ℤ_[p]) * (a : ℚ_[p])⁻¹
    push_cast
    field_simp [PadicInt.coe_ne_zero.mpr ha]

theorem padicTateTorsionParam_surjective (a : ℤ_[p]) (ha : a ≠ 0) :
    Function.Surjective (padicTateTorsionParam p a ha) := by
  intro x
  obtain ⟨q, hq⟩ := Submodule.Quotient.mk_surjective (padicIntegralSubmodule p) x.1
  have hx : a • x.1 = 0 :=
    (Submodule.mem_torsionBy_iff (R := ℤ_[p]) (M := PadicTateQuotient p)
      (a := a) x.1).mp x.2
  rw [← hq, ← Submodule.Quotient.mk_smul, Algebra.smul_def] at hx
  change (Submodule.Quotient.mk ((a : ℚ_[p]) * q) : PadicTateQuotient p) = 0 at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, Subtype.ext ?_⟩
  simp only [padicTateTorsionParam]
  rw [← hq]
  apply congrArg Submodule.Quotient.mk
  change (z : ℚ_[p]) * (a : ℚ_[p])⁻¹ = q
  change (z : ℚ_[p]) = (a : ℚ_[p]) * q at hz
  rw [hz]
  field_simp [PadicInt.coe_ne_zero.mpr ha]

/-- Exact classification of scalar torsion in `ℚ_p/ℤ_p`. -/
noncomputable def padicIntQuotientEquivPadicTateTorsion (a : ℤ_[p]) (ha : a ≠ 0) :
    ℤ_[p] ⧸ (Ideal.span ({a} : Set ℤ_[p])).toAddSubgroup ≃+
      Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) a := by
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (ker_padicTateTorsionParam p a ha).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (padicTateTorsionParam p a ha)
        (padicTateTorsionParam_surjective p a ha))

theorem padicTateTorsion_card (a : ℤ_[p]) (ha : a ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) a) =
      p ^ a.valuation := by
  calc
    Nat.card (Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) a) =
        Nat.card (ℤ_[p] ⧸ (Ideal.span ({a} : Set ℤ_[p])).toAddSubgroup) :=
      Nat.card_congr (padicIntQuotientEquivPadicTateTorsion p a ha).symm.toEquiv
    _ = p ^ a.valuation := padicIntQuotientSpan_card p a ha

theorem finite_padicTateTorsion (a : ℤ_[p]) (ha : a ≠ 0) :
    Finite (Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) a) :=
  Finite.of_equiv (ZMod (p ^ a.valuation))
    ((padicIntQuotientEquivZModPow p a ha).symm.trans
      (padicIntQuotientEquivPadicTateTorsion p a ha)).toEquiv

variable (F : Type*) [Field F]

/-- The fixed submodule `H⁰(F, ℚ_p/ℤ_p(2))`.

The absolute Galois group acts through the square of the cyclotomic character, which is the
second Tate twist. -/
noncomputable def padicTateTwistTwoInvariants :
    Submodule ℤ_[p] (PadicTateQuotient p) where
  carrier := {x | ∀ g : Field.absoluteGaloisGroup F,
    (((cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv) ^ 2 :
      (ℤ_[p])ˣ) : ℤ_[p]) • x = x}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro x y hx hy g
    rw [smul_add, hx g, hy g]
  smul_mem' := by
    intro c x hx g
    rw [smul_smul, mul_comm, ← smul_smul, hx g]

/-- The fixed part remains `p`-primary torsion. -/
theorem exists_pow_smul_eq_zero_padicTateTwistTwoInvariants
    (x : padicTateTwistTwoInvariants p F) :
    ∃ n : ℕ, (p : ℤ_[p]) ^ n • x = 0 := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_padicTateQuotient p x.1
  exact ⟨n, Subtype.ext hn⟩

theorem mem_padicTateTwistTwoInvariants_iff (x : PadicTateQuotient p) :
    x ∈ padicTateTwistTwoInvariants p F ↔
      ∀ g : Field.absoluteGaloisGroup F,
        (((cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv) ^ 2 :
          (ℤ_[p])ˣ) : ℤ_[p]) • x = x :=
  Iff.rfl

/-- `p`-primary contribution to `w₂(F)`. For number fields, its finiteness is a downstream
arithmetic theorem; `Nat.card` keeps the definition usable before that proof is installed. -/
noncomputable def wTwoPrimary : ℕ :=
  Nat.card (padicTateTwistTwoInvariants p F)

/-- Scalar whose torsion kernel contains every class fixed by one Galois element. -/
noncomputable def cyclotomicSquareMinusOne (g : Field.absoluteGaloisGroup F) : ℤ_[p] :=
  (((cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv) ^ 2 :
    (ℤ_[p])ˣ) : ℤ_[p]) - 1

noncomputable def padicTateTwistTwoInvariantsToTorsion
    (g : Field.absoluteGaloisGroup F) :
    padicTateTwistTwoInvariants p F →
      Submodule.torsionBy ℤ_[p] (PadicTateQuotient p)
        (cyclotomicSquareMinusOne p F g) := fun x =>
  ⟨x.1, by
    rw [Submodule.mem_torsionBy_iff, cyclotomicSquareMinusOne, sub_smul,
      one_smul, x.2 g, sub_self]⟩

theorem padicTateTwistTwoInvariantsToTorsion_injective
    (g : Field.absoluteGaloisGroup F) :
    Function.Injective (padicTateTwistTwoInvariantsToTorsion p F g) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : Submodule.torsionBy ℤ_[p] (PadicTateQuotient p)
      (cyclotomicSquareMinusOne p F g) => z.1) hxy

/-- One Galois element with nontrivial cyclotomic square proves finiteness of
`H⁰(F, ℚ_p/ℤ_p(2))`. -/
theorem finite_padicTateTwistTwoInvariants_of_cyclotomicSquare_ne_one
    (g : Field.absoluteGaloisGroup F)
    (hg : cyclotomicSquareMinusOne p F g ≠ 0) :
    Finite (padicTateTwistTwoInvariants p F) := by
  letI := finite_padicTateTorsion p _ hg
  exact Finite.of_injective (padicTateTwistTwoInvariantsToTorsion p F g)
    (padicTateTwistTwoInvariantsToTorsion_injective p F g)

/-- Valuation bound on the `p`-primary Birch--Tate denominator from one Galois element. -/
theorem wTwoPrimary_le_of_cyclotomicSquare_ne_one
    (g : Field.absoluteGaloisGroup F)
    (hg : cyclotomicSquareMinusOne p F g ≠ 0) :
    wTwoPrimary p F ≤ p ^ (cyclotomicSquareMinusOne p F g).valuation := by
  letI := finite_padicTateTorsion p _ hg
  rw [wTwoPrimary, ← padicTateTorsion_card p _ hg]
  exact Nat.card_le_card_of_injective
    (padicTateTwistTwoInvariantsToTorsion p F g)
    (padicTateTwistTwoInvariantsToTorsion_injective p F g)

/-- Under the same witness, the primary denominator is itself a power of `p`. -/
theorem wTwoPrimary_eq_prime_pow_of_cyclotomicSquare_ne_one
    (g : Field.absoluteGaloisGroup F)
    (hg : cyclotomicSquareMinusOne p F g ≠ 0) :
    ∃ k ≤ (cyclotomicSquareMinusOne p F g).valuation,
      wTwoPrimary p F = p ^ k := by
  let a := cyclotomicSquareMinusOne p F g
  have hle : (padicTateTwistTwoInvariants p F).toAddSubgroup ≤
      (Submodule.torsionBy ℤ_[p] (PadicTateQuotient p) a).toAddSubgroup := by
    intro x hx
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
    dsimp [a]
    rw [cyclotomicSquareMinusOne, sub_smul, one_smul, hx g, sub_self]
  have hdvd : wTwoPrimary p F ∣ p ^ a.valuation := by
    rw [wTwoPrimary, ← padicTateTorsion_card p a hg]
    exact AddSubgroup.card_dvd_of_le hle
  exact (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd

end GaloisForLFunctions.HTGeometry
