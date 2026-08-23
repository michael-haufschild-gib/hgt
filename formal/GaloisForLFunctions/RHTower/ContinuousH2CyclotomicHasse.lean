import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanContinuousH2Hasse
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionDirectedSystem
import GaloisForLFunctions.HTGeometry.ABHN.FiniteTorsionInvariantSum
import GaloisForLFunctions.RHTower.DeningerPrimePacketFiniteCyclotomicStage

/-!
# Continuous local H² as a Deninger cyclotomic stage

The standard finite `RatModInt` character realizes its `n`-torsion subgroup as the complex
`n`-th roots of unity.  Since a finite unramified continuous local `H²` layer is already
additively equivalent to that torsion subgroup, it is additively equivalent to the multiplicative
Deninger cyclotomic stage.  The additive wrapper records that cohomological addition becomes
multiplication of roots.

This is a route-neutral finite-stage bridge.  Compatibility with field-tower inflation and
arithmetic Frobenius is a separate transition-law problem.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry.ABHN
open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

/-- Faithful finite torsion phase as an actual complex root of unity. -/
noncomputable def ratModIntNTorsionDeningerPhase (n : ℕ) [NeZero n] :
    ratModIntNTorsion n → DeningerRootsOfUnityStage n := fun x ↦
  ⟨Units.mk0 (ratModIntNTorsionStdAddChar n (NeZero.ne n) x) (by
      intro hz
      have hp := ratModIntNTorsionStdAddChar_pow_eq_one n (NeZero.ne n) x
      rw [hz, zero_pow (NeZero.ne n)] at hp
      exact zero_ne_one hp), by
    apply Units.ext
    exact ratModIntNTorsionStdAddChar_pow_eq_one n (NeZero.ne n) x⟩

@[simp] theorem ratModIntNTorsionDeningerPhase_coe
    (n : ℕ) [NeZero n] (x : ratModIntNTorsion n) :
    (((ratModIntNTorsionDeningerPhase n x : DeningerRootsOfUnityStage n) : ℂˣ) : ℂ) =
      ratModIntNTorsionStdAddChar n (NeZero.ne n) x := rfl

/-- The torsion phase embedding is faithful. -/
theorem ratModIntNTorsionDeningerPhase_injective (n : ℕ) [NeZero n] :
    Function.Injective (ratModIntNTorsionDeningerPhase n) := by
  intro x y h
  apply ratModIntNTorsionStdAddChar_injective n (NeZero.ne n)
  exact congrArg (fun z : DeningerRootsOfUnityStage n ↦ ((z.1 : ℂˣ) : ℂ)) h

/-- Cyclotomic phase respects addition of local invariants and multiplication of roots. -/
noncomputable def ratModIntNTorsionDeningerPhaseAddHom (n : ℕ) [NeZero n] :
    ratModIntNTorsion n →+ Additive (DeningerRootsOfUnityStage n) where
  toFun x := ratModIntNTorsionDeningerPhase n x
  map_zero' := by
    change ratModIntNTorsionDeningerPhase n 0 = 1
    apply Subtype.ext
    apply Units.ext
    exact (ratModIntNTorsionStdAddChar n (NeZero.ne n)).map_zero_eq_one
  map_add' x y := by
    change ratModIntNTorsionDeningerPhase n (x + y) =
      ratModIntNTorsionDeningerPhase n x * ratModIntNTorsionDeningerPhase n y
    apply Subtype.ext
    apply Units.ext
    exact (ratModIntNTorsionStdAddChar n (NeZero.ne n)).map_add_eq_mul x y

/-- The finite torsion subgroup has exactly its denominator many elements. -/
theorem ratModIntNTorsion_natCard (n : ℕ) [NeZero n] :
    Nat.card (ratModIntNTorsion n) = n := by
  calc
    Nat.card (ratModIntNTorsion n) = Nat.card (ZMod n) :=
      Nat.card_congr (zmodRatModIntAddEquivNTorsion n (NeZero.ne n)).toEquiv.symm
    _ = n := Nat.card_zmod n

/-- Additive finite local invariants are exactly the multiplicative Deninger cyclotomic stage. -/
noncomputable def ratModIntNTorsionDeningerPhaseAddEquiv (n : ℕ) [NeZero n] :
    ratModIntNTorsion n ≃+ Additive (DeningerRootsOfUnityStage n) := by
  letI : Finite (ratModIntNTorsion n) :=
    Finite.of_injective (zmodRatModIntAddEquivNTorsion n (NeZero.ne n)).symm
      (zmodRatModIntAddEquivNTorsion n (NeZero.ne n)).symm.injective
  refine AddEquiv.ofBijective (ratModIntNTorsionDeningerPhaseAddHom n) ?_
  exact (Nat.bijective_iff_injective_and_card _).2
    ⟨ratModIntNTorsionDeningerPhase_injective n,
      (ratModIntNTorsion_natCard n).trans (deningerRootsOfUnityStage_card n).symm⟩

@[simp] theorem ratModIntNTorsionDeningerPhaseAddEquiv_apply
    (n : ℕ) [NeZero n] (x : ratModIntNTorsion n) :
    ratModIntNTorsionDeningerPhaseAddEquiv n x = ratModIntNTorsionDeningerPhase n x := rfl

/-- Inclusion of cyclotomic stages when one order divides another. -/
def deningerRootsOfUnityStageInclusion {m n : ℕ} (hmn : m ∣ n) :
    DeningerRootsOfUnityStage m →* DeningerRootsOfUnityStage n :=
  Subgroup.inclusion (by
    intro u hu
    rw [mem_rootsOfUnity] at hu ⊢
    obtain ⟨c, rfl⟩ := hmn
    rw [pow_mul, hu, one_pow])

@[simp] theorem deningerRootsOfUnityStageInclusion_coe {m n : ℕ} (hmn : m ∣ n)
    (z : DeningerRootsOfUnityStage m) :
    ((deningerRootsOfUnityStageInclusion hmn z : DeningerRootsOfUnityStage n) : ℂˣ) = z := rfl

/-- Cyclotomic-stage inclusion is compatible with finite local-invariant transition. -/
theorem ratModIntNTorsionDeningerPhase_inclusion {m n : ℕ}
    [NeZero m] [NeZero n] (hmn : m ∣ n) (x : ratModIntNTorsion m) :
    deningerRootsOfUnityStageInclusion hmn (ratModIntNTorsionDeningerPhase m x) =
      ratModIntNTorsionDeningerPhase n (ratModIntNTorsionInclusion hmn x) := by
  apply Subtype.ext
  apply Units.ext
  exact (ratModIntNTorsionStdAddChar_inclusion
    (NeZero.ne m) (NeZero.ne n) hmn x).symm

/-- Identity law for cyclotomic-stage inclusion. -/
theorem deningerRootsOfUnityStageInclusion_self (n : ℕ) :
    deningerRootsOfUnityStageInclusion (dvd_refl n) =
      MonoidHom.id (DeningerRootsOfUnityStage n) := by
  ext z
  rfl

/-- Composition law for the cyclotomic-stage directed system. -/
theorem deningerRootsOfUnityStageInclusion_comp {l m n : ℕ}
    (hlm : l ∣ m) (hmn : m ∣ n) :
    (deningerRootsOfUnityStageInclusion hmn).comp
      (deningerRootsOfUnityStageInclusion hlm) =
        deningerRootsOfUnityStageInclusion (dvd_trans hlm hmn) := by
  ext z
  rfl

/-- Coordinatewise finite local invariants as a finite-support cyclotomic profile. -/
noncomputable def ratModIntNTorsionCyclotomicProfileAddEquiv
    (ι : Type*) (n : ℕ) [NeZero n] :
    (ι →₀ ratModIntNTorsion n) ≃+
      (ι →₀ Additive (DeningerRootsOfUnityStage n)) :=
  Finsupp.mapRange.addEquiv (ratModIntNTorsionDeningerPhaseAddEquiv n)

/-- Literal product of a finite-support Deninger cyclotomic profile. -/
noncomputable def deningerCyclotomicProfileProduct
    {ι : Type*} (n : ℕ) [NeZero n]
    (z : ι →₀ Additive (DeningerRootsOfUnityStage n)) :
    DeningerRootsOfUnityStage n :=
  (z.sum fun _ ζ ↦ ζ).toMul

/-- Coordinatewise cyclotomic conversion turns invariant sum into literal root product. -/
theorem deningerCyclotomicProfileProduct_map_invariant
    (ι : Type*) (n : ℕ) [NeZero n] (x : ι →₀ ratModIntNTorsion n) :
    deningerCyclotomicProfileProduct n
        (ratModIntNTorsionCyclotomicProfileAddEquiv ι n x) =
      ratModIntNTorsionDeningerPhase n
        (finsuppRatModIntNTorsionSumAddHom ι n x) := by
  classical
  rw [deningerCyclotomicProfileProduct,
    ratModIntNTorsionCyclotomicProfileAddEquiv]
  change ((Finsupp.mapRange (ratModIntNTorsionDeningerPhaseAddEquiv n)
    (ratModIntNTorsionDeningerPhaseAddEquiv n).map_zero x).sum
      (fun _ ζ ↦ ζ)).toMul = _
  rw [Finsupp.sum_mapRange_index]
  · change (x.sum fun _ b ↦
        ratModIntNTorsionDeningerPhaseAddEquiv n b).toMul =
      (ratModIntNTorsionDeningerPhaseAddEquiv n
        (finsuppRatModIntNTorsionSumAddHom ι n x)).toMul
    apply Additive.toMul.injective
    change (∑ a ∈ x.support, ratModIntNTorsionDeningerPhaseAddEquiv n (x a)) =
      ratModIntNTorsionDeningerPhaseAddEquiv n (∑ a ∈ x.support, x a)
    rw [map_sum]
  · intro i
    rfl

/-- Cyclotomic product-one reciprocity is exactly zero-sum finite-level ABHN reciprocity. -/
theorem deningerCyclotomicProfileProduct_eq_one_hasse_iff
    (ι : Type*) (n : ℕ) [NeZero n] (x : ι →₀ ratModIntNTorsion n) :
    deningerCyclotomicProfileProduct n
        (ratModIntNTorsionCyclotomicProfileAddEquiv ι n x) = 1 ↔
      finsuppRatModIntNTorsionSumAddHom ι n x = 0 := by
  rw [deningerCyclotomicProfileProduct_map_invariant]
  constructor
  · intro h
    apply ratModIntNTorsionDeningerPhase_injective n
    have hzero : ratModIntNTorsionDeningerPhase n 0 = 1 := by
      apply Subtype.ext
      apply Units.ext
      exact (ratModIntNTorsionStdAddChar n (NeZero.ne n)).map_zero_eq_one
    exact h.trans hzero.symm
  · intro h
    rw [h]
    apply Subtype.ext
    apply Units.ext
    exact (ratModIntNTorsionStdAddChar n (NeZero.ne n)).map_zero_eq_one

/-- Continuous unramified local `H²` is additively equivalent to its Deninger cyclotomic stage. -/
noncomputable def nonarchimedeanContinuousH2DeningerPhaseAddEquiv
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : NonarchimedeanFiniteUnramifiedRootLift K) :=
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  D.continuousH2NTorsionInvariant.trans
    (ratModIntNTorsionDeningerPhaseAddEquiv D.polynomial.natDegree)

/-- Deninger Frobenius is multiplication by its exponent on finite local invariant phases. -/
theorem deningerRootsOfUnityStageFrobenius_ratModIntNTorsionPhase
    (n : ℕ) [NeZero n] (p : {p : ℕ // p.Coprime n})
    (x : ratModIntNTorsion n) :
    deningerRootsOfUnityStageFrobenius p.1 n p.2
        (ratModIntNTorsionDeningerPhase n x) =
      ratModIntNTorsionDeningerPhase n (p.1 • x) := by
  apply Subtype.ext
  apply Units.ext
  change (ratModIntNTorsionStdAddChar n (NeZero.ne n) x) ^ p.1 =
    ratModIntNTorsionStdAddChar n (NeZero.ne n) (p.1 • x)
  exact (ratModIntNTorsionStdAddChar n (NeZero.ne n)).map_nsmul_eq_pow p.1 x |>.symm

/-- Under the local-H²/cyclotomic equivalence, Deninger Frobenius is cohomological
multiplication by `p`. -/
theorem nonarchimedeanContinuousH2DeningerFrobenius_conjugacy
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : NonarchimedeanFiniteUnramifiedRootLift K)
    (p : {p : ℕ // p.Coprime D.polynomial.natDegree}) :
    letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
    let e := nonarchimedeanContinuousH2DeningerPhaseAddEquiv D
    ∀ x, deningerRootsOfUnityStageFrobenius p.1 D.polynomial.natDegree p.2 (e x).toMul =
      (e (p.1 • x)).toMul := by
  dsimp only
  intro x
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  change deningerRootsOfUnityStageFrobenius p.1 D.polynomial.natDegree p.2
      (ratModIntNTorsionDeningerPhase D.polynomial.natDegree
        (D.continuousH2NTorsionInvariant x)) =
    ratModIntNTorsionDeningerPhase D.polynomial.natDegree
      (D.continuousH2NTorsionInvariant (p.1 • x))
  rw [map_nsmul]
  exact deningerRootsOfUnityStageFrobenius_ratModIntNTorsionPhase
    D.polynomial.natDegree p (D.continuousH2NTorsionInvariant x)

/-- Cyclotomic Hasse congruence for packaged continuous local `H²`. -/
theorem nonarchimedeanContinuousH2DeningerPhase_congr_hasse_iff
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := nonarchimedeanContinuousH2DeningerPhaseAddEquiv D
    ∀ x y, x = y ↔ e x = e y := by
  dsimp only
  intro x y
  exact (nonarchimedeanContinuousH2DeningerPhaseAddEquiv D).injective.eq_iff.symm

/-- A continuous local `H²` class vanishes exactly when its cyclotomic image is the unit root. -/
theorem nonarchimedeanContinuousH2DeningerPhase_eq_one_hasse_iff
    {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := nonarchimedeanContinuousH2DeningerPhaseAddEquiv D
    ∀ x, x = 0 ↔ e x = 0 := by
  dsimp only
  intro x
  constructor
  · rintro rfl
    exact map_zero _
  · intro hx
    apply (nonarchimedeanContinuousH2DeningerPhaseAddEquiv D).injective
    simpa using hx

end

end RHTower
