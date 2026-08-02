import GaloisForLFunctions.RHTower.DeningerPrimeFiniteCyclotomicReductionSystem
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# Rational-Witt source admission for finite Deninger packets

Deninger's finite-field presentation identifies

`W_rat(AlgebraicClosure (ZMod p))`

with the reduced monoid algebra of the multiplicative group of the algebraic
closure.  After complexification this is

`ℂ[(AlgebraicClosure (ZMod p))ˣ]`.

Galois descent identifies the rational Witt vectors over the prime field with
the arithmetic-Frobenius fixed part.  This module constructs the finite
cyclotomic pieces of that published presentation and proves that their
evaluation on the Deninger packet is already exhaustive.

For every prime-to-`p` modulus `n`:

* a chosen primitive `n`-th root embeds `ℂ[μ_n]` injectively into the full
  complexified rational-Witt presentation;
* finite Frobenius `j ↦ pj` commutes with arithmetic Frobenius `x ↦ x^p`;
* the normalized orbit trace of every root is Frobenius fixed;
* evaluating that orbit trace is exactly the previously constructed
  Frobenius-orbit root evaluation;
* every complex function on `(ZMod n)ˣ / ⟨p⟩` is the evaluation of one such
  Frobenius-fixed element.

Consequently every member of the uniformly dense, hence Haar-`L²`-dense,
finite-stage packet subalgebra has an arithmetic-Frobenius-fixed
rational-Witt witness.  This closes finite rational-Witt source admission; it
does not construct Deninger's conjectural relevant complex or identify its
closed middle boundaries.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- Complexified reduced-monoid-algebra presentation of
`W_rat(AlgebraicClosure (ZMod p))`. -/
abbrev DeningerPrimeComplexifiedRationalWittPresentation (p : Nat.Primes) :=
  MonoidAlgebra ℂ (DeningerPrimeArithmeticClosure p)ˣ

instance deningerFiniteFrobeniusStageNatCastNeZero
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    NeZero (s.modulus : ZMod (p : ℕ)) := by
  constructor
  intro h
  have hdvd : (p : ℕ) ∣ s.modulus :=
    (ZMod.natCast_eq_zero_iff s.modulus (p : ℕ)).mp h
  exact (p.2.coprime_iff_not_dvd.mp s.coprime) hdvd

/-- A chosen primitive root realizing one finite cyclotomic stage inside
the algebraic closure of the prime field. -/
noncomputable def deningerPrimeFiniteWittPrimitiveRoot
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerPrimeArithmeticClosure p :=
  Classical.choose
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (DeningerPrimeArithmeticClosure p) s.modulus)

theorem deningerPrimeFiniteWittPrimitiveRoot_spec
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    IsPrimitiveRoot (deningerPrimeFiniteWittPrimitiveRoot p s) s.modulus :=
  Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (DeningerPrimeArithmeticClosure p) s.modulus)

noncomputable def deningerPrimeFiniteWittPrimitiveRootUnit
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    (DeningerPrimeArithmeticClosure p)ˣ :=
  (deningerPrimeFiniteWittPrimitiveRoot_spec p s).isUnit
    s.modulus_ne_zero |>.unit

theorem deningerPrimeFiniteWittPrimitiveRootUnit_spec
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    IsPrimitiveRoot (deningerPrimeFiniteWittPrimitiveRootUnit p s) s.modulus :=
  IsPrimitiveRoot.isUnit_unit s.modulus_ne_zero
    (deningerPrimeFiniteWittPrimitiveRoot_spec p s)

/-- Embedding of the abstract finite root group into the actual roots of
unity of `AlgebraicClosure (ZMod p)`. -/
noncomputable def deningerPrimeFiniteWittRootEmbedding
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Multiplicative (ZMod s.modulus) →*
      (DeningerPrimeArithmeticClosure p)ˣ :=
  let e :
      Multiplicative (ZMod s.modulus) ≃*
        Subgroup.zpowers (deningerPrimeFiniteWittPrimitiveRootUnit p s) :=
    (deningerPrimeFiniteWittPrimitiveRootUnit_spec p s).zmodEquivZPowers
      |>.toMultiplicative
  (Subgroup.zpowers
      (deningerPrimeFiniteWittPrimitiveRootUnit p s)).subtype.comp
    e.toMonoidHom

theorem deningerPrimeFiniteWittRootEmbedding_injective
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Injective (deningerPrimeFiniteWittRootEmbedding p s) := by
  let e :
      Multiplicative (ZMod s.modulus) ≃*
        Subgroup.zpowers (deningerPrimeFiniteWittPrimitiveRootUnit p s) :=
    (deningerPrimeFiniteWittPrimitiveRootUnit_spec p s).zmodEquivZPowers
      |>.toMultiplicative
  exact (Subgroup.zpowers
      (deningerPrimeFiniteWittPrimitiveRootUnit p s)).subtype_injective.comp
    e.injective

/-- Complex group algebra of one finite cyclotomic root group. -/
abbrev DeningerFiniteCyclotomicWittAlgebra (n : ℕ) :=
  AddMonoidAlgebra ℂ (ZMod n)

/-- Inclusion of a finite cyclotomic group algebra into the published
complexified rational-Witt presentation. -/
noncomputable def deningerPrimeFiniteCyclotomicWittInclusion
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    DeningerFiniteCyclotomicWittAlgebra s.modulus →ₐ[ℂ]
      DeningerPrimeComplexifiedRationalWittPresentation p where
  toFun x :=
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ
      (deningerPrimeFiniteWittRootEmbedding p s)
      ((AddMonoidAlgebra.toMultiplicative ℂ (ZMod s.modulus)) x)
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul]
    exact map_mul
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ
        (deningerPrimeFiniteWittRootEmbedding p s))
      ((AddMonoidAlgebra.toMultiplicative ℂ (ZMod s.modulus)) x)
      ((AddMonoidAlgebra.toMultiplicative ℂ (ZMod s.modulus)) y)
  map_zero' := by simp
  map_add' x y := by
    rw [map_add]
    exact map_add
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ
        (deningerPrimeFiniteWittRootEmbedding p s))
      ((AddMonoidAlgebra.toMultiplicative ℂ (ZMod s.modulus)) x)
      ((AddMonoidAlgebra.toMultiplicative ℂ (ZMod s.modulus)) y)
  commutes' c := by
    simp [AddMonoidAlgebra.toMultiplicative]

theorem deningerPrimeFiniteCyclotomicWittInclusion_injective
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ)) :
    Function.Injective
      (deningerPrimeFiniteCyclotomicWittInclusion p s) := by
  exact
    (MonoidAlgebra.mapDomain_injective
      (deningerPrimeFiniteWittRootEmbedding_injective p s)).comp
      (AddMonoidAlgebra.toMultiplicative ℂ (ZMod s.modulus)).injective

@[simp] theorem deningerPrimeFiniteCyclotomicWittInclusion_single
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (j : ZMod s.modulus) (c : ℂ) :
    deningerPrimeFiniteCyclotomicWittInclusion p s
        (AddMonoidAlgebra.single j c) =
      MonoidAlgebra.single
        (deningerPrimeFiniteWittRootEmbedding p s
          (Multiplicative.ofAdd j)) c := by
  simp [deningerPrimeFiniteCyclotomicWittInclusion,
    AddMonoidAlgebra.toMultiplicative]

/-- Frobenius on the complexified rational-Witt group-algebra
presentation over the algebraic closure of `𝔽_p`. -/
noncomputable def deningerPrimeComplexifiedRationalWittFrobenius
    (p : Nat.Primes) :
    DeningerPrimeComplexifiedRationalWittPresentation p ≃ₐ[ℂ]
      DeningerPrimeComplexifiedRationalWittPresentation p :=
  MonoidAlgebra.domCongr ℂ ℂ
    (deningerPrimeArithmeticFrobeniusMulAut p)

@[simp] theorem deningerPrimeComplexifiedRationalWittFrobenius_single
    (p : Nat.Primes) (x : (DeningerPrimeArithmeticClosure p)ˣ)
    (c : ℂ) :
    deningerPrimeComplexifiedRationalWittFrobenius p
        (MonoidAlgebra.single x c) =
      MonoidAlgebra.single (x ^ (p : ℕ)) c := by
  simp [deningerPrimeComplexifiedRationalWittFrobenius,
    deningerPrimeArithmeticFrobeniusMulAut_apply]

/-- Character evaluation of the finite cyclotomic rational-Witt algebra. -/
def deningerFiniteCyclotomicWittCharacter
    (n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    Multiplicative (ZMod n) →* ℂ where
  toFun j := ZMod.stdAddChar (j.toAdd * (u : ZMod n))
  map_one' := by
    simp
  map_mul' j k := by
    change ZMod.stdAddChar ((j.toAdd + k.toAdd) * (u : ZMod n)) =
      ZMod.stdAddChar (j.toAdd * (u : ZMod n)) *
        ZMod.stdAddChar (k.toAdd * (u : ZMod n))
    rw [add_mul, AddChar.map_add_eq_mul]

/-- Algebra homomorphism evaluating a finite rational-Witt element at a
cyclotomic packet character. -/
def deningerFiniteCyclotomicWittEvaluation
    (n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    DeningerFiniteCyclotomicWittAlgebra n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (ZMod n)
    (deningerFiniteCyclotomicWittCharacter n u)

@[simp] theorem deningerFiniteCyclotomicWittEvaluation_single
    (n : ℕ) [NeZero n] (u : (ZMod n)ˣ)
    (j : ZMod n) (c : ℂ) :
    deningerFiniteCyclotomicWittEvaluation n u
        (AddMonoidAlgebra.single j c) =
      c * deningerFiniteUnitEvaluation n j u := by
  simp [deningerFiniteCyclotomicWittEvaluation,
    deningerFiniteCyclotomicWittCharacter,
    deningerFiniteUnitEvaluation]

/-- Normalized Frobenius orbit trace of one cyclotomic root.  The
normalization is available after complexification. -/
def deningerFiniteCyclotomicWittOrbitTrace
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (j : ZMod n) :
    DeningerFiniteCyclotomicWittAlgebra n := by
  classical
  let H := deningerFiniteFrobeniusSubgroup p n hpn
  letI : Fintype H := Fintype.ofFinite H
  exact
    (Fintype.card H : ℂ)⁻¹ •
      ∑ h : H, AddMonoidAlgebra.single (j * (h.1 : ZMod n)) 1

/-- Evaluation of a rational-Witt orbit trace is exactly the finite
Frobenius-orbit evaluation. -/
theorem deningerFiniteCyclotomicWittEvaluation_orbitTrace
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (j : ZMod n) (u : (ZMod n)ˣ) :
    deningerFiniteCyclotomicWittEvaluation n u
        (deningerFiniteCyclotomicWittOrbitTrace p n hpn j) =
      deningerFiniteOrbitEvaluation n
        (deningerFiniteFrobeniusSubgroup p n hpn) j u := by
  classical
  let H := deningerFiniteFrobeniusSubgroup p n hpn
  letI : Fintype H := Fintype.ofFinite H
  simp only [deningerFiniteCyclotomicWittOrbitTrace,
    deningerFiniteCyclotomicWittEvaluation, map_smul, map_sum,
    AddMonoidAlgebra.lift_single, smul_eq_mul]
  simp only [deningerFiniteCyclotomicWittCharacter,
    deningerFiniteOrbitEvaluation, deningerFiniteUnitEvaluation]
  apply congrArg
  apply Finset.sum_congr rfl
  intro h _
  simp [mul_comm, mul_left_comm]

/-- Rational-Witt element associated to a coefficient vector of orbit
traces. -/
def deningerFiniteCyclotomicWittLinearCombination
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (c : ZMod n → ℂ) :
    DeningerFiniteCyclotomicWittAlgebra n :=
  ∑ j : ZMod n, c j •
    deningerFiniteCyclotomicWittOrbitTrace p n hpn j

/-- Arithmetic Frobenius on the finite cyclotomic part of the rational-Witt
group-algebra presentation. -/
def deningerFiniteCyclotomicWittFrobenius
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n) :
    DeningerFiniteCyclotomicWittAlgebra n ≃ₐ[ℂ]
      DeningerFiniteCyclotomicWittAlgebra n :=
  AddMonoidAlgebra.domCongr ℂ ℂ
    (AddAut.mulRight (ZMod.unitOfCoprime p hpn))

@[simp] theorem deningerFiniteCyclotomicWittFrobenius_single
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (j : ZMod n) (c : ℂ) :
    deningerFiniteCyclotomicWittFrobenius p n hpn
        (AddMonoidAlgebra.single j c) =
      AddMonoidAlgebra.single
        (j * (ZMod.unitOfCoprime p hpn : ZMod n)) c := by
  simp [deningerFiniteCyclotomicWittFrobenius]

/-- The finite inclusion intertwines finite and arithmetic Frobenius. -/
theorem deningerPrimeFiniteCyclotomicWittInclusion_frobenius
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (w : DeningerFiniteCyclotomicWittAlgebra s.modulus) :
    deningerPrimeComplexifiedRationalWittFrobenius p
        (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
      deningerPrimeFiniteCyclotomicWittInclusion p s
        (deningerFiniteCyclotomicWittFrobenius
          (p : ℕ) s.modulus s.coprime w) := by
  induction w using AddMonoidAlgebra.induction with
  | zero =>
      simp
  | single_add j c w _hj _hc ih =>
      simp only [map_add, ih,
        deningerPrimeFiniteCyclotomicWittInclusion_single,
        deningerFiniteCyclotomicWittFrobenius_single,
        deningerPrimeComplexifiedRationalWittFrobenius_single]
      congr 2
      rw [← map_pow]
      congr 1
      apply Multiplicative.ext
      simp [ZMod.unitOfCoprime, nsmul_eq_mul, mul_comm]

/-- Every rational-Witt orbit trace is fixed by finite Frobenius. -/
theorem deningerFiniteCyclotomicWittFrobenius_orbitTrace
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (j : ZMod n) :
    deningerFiniteCyclotomicWittFrobenius p n hpn
        (deningerFiniteCyclotomicWittOrbitTrace p n hpn j) =
      deningerFiniteCyclotomicWittOrbitTrace p n hpn j := by
  classical
  let H := deningerFiniteFrobeniusSubgroup p n hpn
  letI : Fintype H := Fintype.ofFinite H
  let fp : H :=
    ⟨ZMod.unitOfCoprime p hpn, Subgroup.mem_zpowers _⟩
  simp only [deningerFiniteCyclotomicWittOrbitTrace, map_smul, map_sum,
    deningerFiniteCyclotomicWittFrobenius_single]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight fp)
    (fun h : H =>
      AddMonoidAlgebra.single
        (j * (h.1 : ZMod n) *
          (ZMod.unitOfCoprime p hpn : ZMod n)) 1)
    (fun h : H =>
      AddMonoidAlgebra.single (j * (h.1 : ZMod n)) 1) ?_
  intro h
  congr 1
  simp [fp, mul_assoc]

/-- Linear combinations of orbit traces remain Frobenius fixed. -/
theorem deningerFiniteCyclotomicWittFrobenius_linearCombination
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (c : ZMod n → ℂ) :
    deningerFiniteCyclotomicWittFrobenius p n hpn
        (deningerFiniteCyclotomicWittLinearCombination p n hpn c) =
      deningerFiniteCyclotomicWittLinearCombination p n hpn c := by
  classical
  simp [deningerFiniteCyclotomicWittLinearCombination,
    deningerFiniteCyclotomicWittFrobenius_orbitTrace]

theorem deningerPrimeFiniteCyclotomicWittInclusion_orbitTrace_fixed
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (j : ZMod s.modulus) :
    deningerPrimeComplexifiedRationalWittFrobenius p
        (deningerPrimeFiniteCyclotomicWittInclusion p s
          (deningerFiniteCyclotomicWittOrbitTrace
            (p : ℕ) s.modulus s.coprime j)) =
      deningerPrimeFiniteCyclotomicWittInclusion p s
        (deningerFiniteCyclotomicWittOrbitTrace
          (p : ℕ) s.modulus s.coprime j) := by
  rw [deningerPrimeFiniteCyclotomicWittInclusion_frobenius,
    deningerFiniteCyclotomicWittFrobenius_orbitTrace]

theorem deningerPrimeFiniteCyclotomicWittInclusion_linearCombination_fixed
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (c : ZMod s.modulus → ℂ) :
    deningerPrimeComplexifiedRationalWittFrobenius p
        (deningerPrimeFiniteCyclotomicWittInclusion p s
          (deningerFiniteCyclotomicWittLinearCombination
            (p : ℕ) s.modulus s.coprime c)) =
      deningerPrimeFiniteCyclotomicWittInclusion p s
        (deningerFiniteCyclotomicWittLinearCombination
          (p : ℕ) s.modulus s.coprime c) := by
  rw [deningerPrimeFiniteCyclotomicWittInclusion_frobenius,
    deningerFiniteCyclotomicWittFrobenius_linearCombination]

theorem deningerFiniteCyclotomicWittEvaluation_linearCombination
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (c : ZMod n → ℂ) (u : (ZMod n)ˣ) :
    deningerFiniteCyclotomicWittEvaluation n u
        (deningerFiniteCyclotomicWittLinearCombination p n hpn c) =
      ∑ j : ZMod n, c j *
        deningerFiniteOrbitEvaluation n
          (deningerFiniteFrobeniusSubgroup p n hpn) j u := by
  classical
  simp [deningerFiniteCyclotomicWittLinearCombination,
    deningerFiniteCyclotomicWittEvaluation_orbitTrace]

theorem deningerFiniteCyclotomicWittEvaluation_surjective_on_packet
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (F : ((ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn) → ℂ) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra n,
      ∀ u : (ZMod n)ˣ,
        deningerFiniteCyclotomicWittEvaluation n u w =
          F (QuotientGroup.mk u) := by
  obtain ⟨c, hc⟩ :=
    deningerFiniteFrobeniusOrbitEvaluation_span p n hpn F
  refine ⟨deningerFiniteCyclotomicWittLinearCombination p n hpn c, ?_⟩
  intro u
  rw [deningerFiniteCyclotomicWittEvaluation_linearCombination]
  simpa [deningerFiniteFrobeniusOrbitEvaluation,
    deningerFiniteOrbitEvaluationQuotient_mk] using
      (hc (QuotientGroup.mk u)).symm

/-- Every finite packet function is restriction of a Frobenius-fixed
complexified rational-Witt cyclotomic element. -/
theorem deningerFiniteCyclotomicWittEvaluation_surjective_fixed
    (p n : ℕ) [NeZero n] (hpn : p.Coprime n)
    (F : ((ZMod n)ˣ ⧸ deningerFiniteFrobeniusSubgroup p n hpn) → ℂ) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra n,
      deningerFiniteCyclotomicWittFrobenius p n hpn w = w ∧
      ∀ u : (ZMod n)ˣ,
        deningerFiniteCyclotomicWittEvaluation n u w =
          F (QuotientGroup.mk u) := by
  obtain ⟨c, hc⟩ :=
    deningerFiniteFrobeniusOrbitEvaluation_span p n hpn F
  refine
    ⟨deningerFiniteCyclotomicWittLinearCombination p n hpn c,
      deningerFiniteCyclotomicWittFrobenius_linearCombination p n hpn c,
      ?_⟩
  intro u
  rw [deningerFiniteCyclotomicWittEvaluation_linearCombination]
  simpa [deningerFiniteFrobeniusOrbitEvaluation,
    deningerFiniteOrbitEvaluationQuotient_mk] using
      (hc (QuotientGroup.mk u)).symm

/-- **Actual finite rational-Witt admission.** Every function on a finite
Deninger packet is obtained by evaluating a finite cyclotomic element whose
image in the published complexified presentation
`ℂ[(AlgebraicClosure (ZMod p))ˣ]` is fixed by arithmetic Frobenius. -/
theorem deningerPrimeComplexifiedRationalWitt_finiteRestriction_surjective
    (p : Nat.Primes) (s : DeningerFiniteFrobeniusStage (p : ℕ))
    (F : DeningerFiniteFrobeniusStageQuotient (p : ℕ) s → ℂ) :
    ∃ w : DeningerFiniteCyclotomicWittAlgebra s.modulus,
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      ∀ u : (ZMod s.modulus)ˣ,
        deningerFiniteCyclotomicWittEvaluation s.modulus u w =
          F (QuotientGroup.mk u) := by
  obtain ⟨w, hwfixed, hw⟩ :=
    deningerFiniteCyclotomicWittEvaluation_surjective_fixed
      (p : ℕ) s.modulus s.coprime F
  refine ⟨w, ?_, hw⟩
  rw [deningerPrimeFiniteCyclotomicWittInclusion_frobenius, hwfixed]

/-- Every member of the uniformly and Haar-dense finite-stage packet
subalgebra is the literal restriction of an arithmetic-Frobenius-fixed
element in the complexified rational-Witt presentation. -/
theorem deningerPrimeFiniteStageRealSubalgebra_has_rationalWittWitness
    (p : Nat.Primes)
    (g : deningerPrimeFiniteStageRealSubalgebra p) :
    ∃ (s : DeningerFiniteFrobeniusStage (p : ℕ))
      (w : DeningerFiniteCyclotomicWittAlgebra s.modulus),
      deningerPrimeComplexifiedRationalWittFrobenius p
          (deningerPrimeFiniteCyclotomicWittInclusion p s w) =
        deningerPrimeFiniteCyclotomicWittInclusion p s w ∧
      ∀ (x : DeningerPacketFrobeniusQuotient p)
        (u : (ZMod s.modulus)ˣ),
        (QuotientGroup.mk u :
            DeningerFiniteFrobeniusStageQuotient (p : ℕ) s) =
            deningerPrimeFiniteStageQuotientReduction p s x →
          deningerFiniteCyclotomicWittEvaluation s.modulus u w =
            (((g : C(DeningerPacketFrobeniusQuotient p, ℝ)) x : ℝ) : ℂ) := by
  obtain ⟨s, F, hg⟩ := g.property
  obtain ⟨w, hwfixed, hw⟩ :=
    deningerPrimeComplexifiedRationalWitt_finiteRestriction_surjective
      p s (fun q => (F q : ℂ))
  refine ⟨s, w, hwfixed, ?_⟩
  intro x u hu
  rw [hw u, hu]
  rw [show (g : C(DeningerPacketFrobeniusQuotient p, ℝ)) =
      deningerPrimeFiniteStageRealPullback p s F from hg]
  rfl

end

end RHTower
