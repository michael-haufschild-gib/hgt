import GaloisForLFunctions.HTGeometry.BiprojectiveGradedPiece
import GaloisForLFunctions.HTGeometry.BihomogeneousHilbertIdentity
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Multihomogeneous Bézout via bigraded quotient pieces

This module proves the missing algebraic bridge from a regular sequence of `m+n` bihomogeneous
forms of bidegree `(1,1)` on `P^m × P^n` to its exact Hilbert value `choose (m+n) m`.

No intersection-theory result is assumed.  The proof constructs multiplication and factor maps on
each quotient piece, proves their kernel–range exactness by homogeneous-component extraction, derives
the one-equation Hilbert recurrence by rank–nullity, and iterates it as a forward difference.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable local instance biprojectiveWeightedGradedAlgebra
    (K : Type*) [Field K] (m n : ℕ) :
    GradedAlgebra
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)) :=
  MvPolynomial.weightedGradedAlgebra K biprojectiveWeight

noncomputable local instance finiteBiprojectivePiece
    (K : Type*) [Field K] (m n p q : ℕ) :
    Module.Finite K (BiprojectivePiece K m n p q) :=
  Module.Finite.of_basis (biprojectiveMonomialBasis K m n p q)

abbrev BiprojRing (K : Type*) [Field K] (m n : ℕ) := MvPolynomial (BiprojVar m n) K

noncomputable def biprojectiveIdealPiece (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n)) (p q : ℕ) :
    Submodule K (BiprojectivePiece K m n p q) :=
  (I.restrictScalars K).comap (BiprojectivePiece K m n p q).subtype

abbrev BiprojectiveQuotientPiece (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n)) (p q : ℕ) :=
  (BiprojectivePiece K m n p q) ⧸ biprojectiveIdealPiece K I p q

/-- Dimension of one bigraded piece of a bihomogeneous coordinate-ring quotient. -/
noncomputable def biprojectiveHilbertFunction (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n)) (p q : ℕ) : ℕ :=
  Module.finrank K (BiprojectiveQuotientPiece K I p q)

/-- Multiplication by a bihomogeneous polynomial of bidegree `(a, b)` on bigraded pieces. -/
noncomputable def biprojectiveMul (K : Type*) [Field K] {m n : ℕ}
    (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b)) (p q : ℕ) :
    BiprojectivePiece K m n p q →ₗ[K]
      BiprojectivePiece K m n (a + p) (b + q) where
  toFun g := ⟨f * g.1, by
    exact hf.mul g.2⟩
  map_add' g h := by
    apply Subtype.ext
    exact mul_add f g h
  map_smul' c g := by
    apply Subtype.ext
    simp [Algebra.smul_def, mul_comm, mul_assoc]

@[simp]
theorem biprojectiveMul_apply (K : Type*) [Field K] {m n : ℕ}
    (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b)) (p q : ℕ)
    (g : BiprojectivePiece K m n p q) :
    (biprojectiveMul K f hf p q g : BiprojRing K m n) = f * g := rfl

/-- Multiplication on a bigraded quotient by a bihomogeneous ideal. -/
noncomputable def biprojectiveQuotientMul (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n)) (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b)) (p q : ℕ) :
    BiprojectiveQuotientPiece K I p q →ₗ[K]
      BiprojectiveQuotientPiece K I (a + p) (b + q) :=
  (biprojectiveIdealPiece K I p q).mapQ
    (biprojectiveIdealPiece K I (a + p) (b + q))
    (biprojectiveMul K f hf p q) (by
      intro g hg
      exact I.mul_mem_left f hg)

/-- A polynomial is regular modulo an ideal when multiplication by its residue class is injective. -/
def IsRegularModulo (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n)) (f : BiprojRing K m n) : Prop :=
  ∀ g, f * g ∈ I → g ∈ I

theorem biprojectiveQuotientMul_injective (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n)) (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b))
    (hreg : IsRegularModulo K I f) (p q : ℕ) :
    Function.Injective (biprojectiveQuotientMul K I f hf p q) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | _ g =>
      simp only [biprojectiveQuotientMul, Submodule.mapQ_apply] at hx
      rw [Submodule.Quotient.mk_eq_zero] at hx ⊢
      exact hreg g.1 hx

/-- Homogeneous component of a product whose left factor is homogeneous. -/
theorem weightedHomogeneousComponent_mul_left
    (K : Type*) [Field K] {m n : ℕ}
    (f g : BiprojRing K m n) {a b p q : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b)) :
    weightedHomogeneousComponent biprojectiveWeight (a + p, b + q) (f * g) =
      f * weightedHomogeneousComponent biprojectiveWeight (p, q) g := by
  letI : GradedAlgebra
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)) :=
    MvPolynomial.weightedGradedAlgebra K biprojectiveWeight
  change weightedHomogeneousComponent biprojectiveWeight ((a, b) + (p, q)) (f * g) =
    f * weightedHomogeneousComponent biprojectiveWeight (p, q) g
  rw [← weightedDecomposition.decompose'_apply K biprojectiveWeight,
    ← weightedDecomposition.decompose'_apply K biprojectiveWeight]
  exact DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule K
      (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)) hf

/-- Natural map between bigraded pieces of nested ideal quotients. -/
noncomputable def biprojectiveQuotientFactor (K : Type*) [Field K] {m n : ℕ}
    (I J : Ideal (BiprojRing K m n)) (hIJ : I ≤ J) (p q : ℕ) :
    BiprojectiveQuotientPiece K I p q →ₗ[K]
      BiprojectiveQuotientPiece K J p q :=
  (biprojectiveIdealPiece K I p q).mapQ
    (biprojectiveIdealPiece K J p q) LinearMap.id (by
      intro g hg
      exact hIJ hg)

theorem biprojectiveQuotientFactor_surjective (K : Type*) [Field K] {m n : ℕ}
    (I J : Ideal (BiprojRing K m n)) (hIJ : I ≤ J) (p q : ℕ) :
    Function.Surjective (biprojectiveQuotientFactor K I J hIJ p q) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ g =>
      refine ⟨Submodule.Quotient.mk g, ?_⟩
      rfl

/-- Exactness of adjoining one bihomogeneous equation to a homogeneous ideal. -/
theorem range_biprojectiveQuotientMul_eq_ker_factor
    (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n))
    (hI : I.IsHomogeneous
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)))
    (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b)) (p q : ℕ) :
    LinearMap.range (biprojectiveQuotientMul K I f hf p q) =
      LinearMap.ker (biprojectiveQuotientFactor K I (I ⊔ Ideal.span {f})
        le_sup_left (a + p) (b + q)) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    induction y using Submodule.Quotient.induction_on with
    | _ g =>
        simp only [biprojectiveQuotientMul, biprojectiveQuotientFactor,
          Submodule.mapQ_apply]
        rw [Submodule.Quotient.mk_eq_zero]
        change f * g.1 ∈ I ⊔ Ideal.span {f}
        exact Submodule.mem_sup_right <|
          Ideal.mem_span_singleton'.2 ⟨g.1, by rw [mul_comm]⟩
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    induction x using Submodule.Quotient.induction_on with
    | _ g =>
        simp only [biprojectiveQuotientFactor, Submodule.mapQ_apply] at hx
        rw [Submodule.Quotient.mk_eq_zero] at hx
        change g.1 ∈ I ⊔ Ideal.span {f} at hx
        have hx' : g.1 ∈ Ideal.span {f} ⊔ I := by
          simpa only [sup_comm] using hx
        obtain ⟨c, i, hi, hci⟩ := Ideal.mem_span_singleton_sup.mp hx'
        let cPiece : BiprojectivePiece K m n p q :=
          ⟨weightedHomogeneousComponent biprojectiveWeight (p, q) c,
            weightedHomogeneousComponent_isWeightedHomogeneous (p, q) c⟩
        refine ⟨Submodule.Quotient.mk cPiece, ?_⟩
        simp only [biprojectiveQuotientMul, Submodule.mapQ_apply]
        apply (Submodule.Quotient.eq (biprojectiveIdealPiece K I (a + p) (b + q))).2
        change f * weightedHomogeneousComponent biprojectiveWeight (p, q) c - g.1 ∈ I
        have hciComp := congrArg
          (weightedHomogeneousComponent biprojectiveWeight (a + p, b + q)) hci
        rw [map_add, mul_comm c f,
          weightedHomogeneousComponent_mul_left K f c hf,
          g.2.weightedHomogeneousComponent_same] at hciComp
        have hiComp :
            weightedHomogeneousComponent biprojectiveWeight (a + p, b + q) i ∈ I :=
          weightedHomogeneousComponent_mem_of_mem K biprojectiveWeight hI hi (a + p, b + q)
        have heq :
            f * weightedHomogeneousComponent biprojectiveWeight (p, q) c - g.1 =
              -weightedHomogeneousComponent biprojectiveWeight (a + p, b + q) i := by
          rw [← hciComp]
          abel
        rw [heq]
        exact I.neg_mem hiComp

/-- A singleton ideal generated by a bihomogeneous polynomial is homogeneous. -/
theorem isHomogeneous_span_singleton_biprojective
    (K : Type*) [Field K] {m n : ℕ}
    (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b)) :
    (Ideal.span {f}).IsHomogeneous
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)) := by
  apply Ideal.homogeneous_span
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst g
  exact ⟨(a, b), hf⟩

/-- Adjoining a bihomogeneous generator preserves homogeneity of an ideal. -/
theorem Ideal.IsHomogeneous.sup_span_biprojective
    (K : Type*) [Field K] {m n : ℕ}
    {I : Ideal (BiprojRing K m n)}
    (hI : I.IsHomogeneous
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)))
    (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b)) :
    (I ⊔ Ideal.span {f}).IsHomogeneous
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)) :=
  hI.sup (isHomogeneous_span_singleton_biprojective K f hf)

/-- Bigraded Hilbert-function recurrence after adjoining one regular bihomogeneous equation. -/
theorem finrank_quotient_sup_span_add_finrank
    (K : Type*) [Field K] {m n : ℕ}
    (I : Ideal (BiprojRing K m n))
    (hI : I.IsHomogeneous
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)))
    (f : BiprojRing K m n) {a b : ℕ}
    (hf : f.IsWeightedHomogeneous biprojectiveWeight (a, b))
    (hreg : IsRegularModulo K I f) (p q : ℕ) :
    Module.finrank K
        (BiprojectiveQuotientPiece K (I ⊔ Ideal.span {f}) (a + p) (b + q)) +
      Module.finrank K (BiprojectiveQuotientPiece K I p q) =
        Module.finrank K (BiprojectiveQuotientPiece K I (a + p) (b + q)) := by
  let mulMap := biprojectiveQuotientMul K I f hf p q
  let factorMap := biprojectiveQuotientFactor K I (I ⊔ Ideal.span {f})
    le_sup_left (a + p) (b + q)
  have hMulInj : Function.Injective mulMap :=
    biprojectiveQuotientMul_injective K I f hf hreg p q
  have hFactorSurj : Function.Surjective factorMap :=
    biprojectiveQuotientFactor_surjective K I (I ⊔ Ideal.span {f})
      le_sup_left (a + p) (b + q)
  have hExact : LinearMap.range mulMap = LinearMap.ker factorMap :=
    range_biprojectiveQuotientMul_eq_ker_factor K I hI f hf p q
  calc
    Module.finrank K
          (BiprojectiveQuotientPiece K (I ⊔ Ideal.span {f}) (a + p) (b + q)) +
        Module.finrank K (BiprojectiveQuotientPiece K I p q) =
      Module.finrank K (LinearMap.range factorMap) +
        Module.finrank K (LinearMap.range mulMap) := by
          rw [LinearMap.range_eq_top.mpr hFactorSurj, finrank_top,
            LinearMap.finrank_range_of_inj hMulInj]
    _ = Module.finrank K (LinearMap.range factorMap) +
        Module.finrank K (LinearMap.ker factorMap) := by rw [← hExact]
    _ = Module.finrank K
        (BiprojectiveQuotientPiece K I (a + p) (b + q)) :=
      LinearMap.finrank_range_add_finrank_ker factorMap

/-- A regular sequence of bidegree-`(1,1)` forms, built in ideal-adjoining order. -/
inductive BiprojectiveRegularSequence (K : Type*) [Field K] {m n : ℕ} :
    List (BiprojRing K m n) → Prop
  | nil : BiprojectiveRegularSequence K []
  | snoc {fs : List (BiprojRing K m n)} {f : BiprojRing K m n}
      (hfs : BiprojectiveRegularSequence K fs)
      (hf : f.IsWeightedHomogeneous biprojectiveWeight (1, 1))
      (hreg : IsRegularModulo K (Ideal.ofList fs) f) :
      BiprojectiveRegularSequence K (fs ++ [f])

namespace BiprojectiveRegularSequence

/-- Ideals generated by prefixes of a bihomogeneous regular sequence are homogeneous. -/
theorem isHomogeneous (K : Type*) [Field K] {m n : ℕ}
    {fs : List (BiprojRing K m n)} (hfs : BiprojectiveRegularSequence K fs) :
    (Ideal.ofList fs).IsHomogeneous
      (weightedHomogeneousSubmodule K
        (biprojectiveWeight : BiprojVar m n → ℕ × ℕ)) := by
  induction hfs with
  | nil =>
      rw [Ideal.ofList_nil]
      exact Ideal.IsHomogeneous.bot _
  | @snoc fs f hfs hf hreg ih =>
      rw [Ideal.ofList_append, Ideal.ofList_singleton]
      exact ih.sup (isHomogeneous_span_singleton_biprojective K f hf)

/-- Hilbert function of a regular sequence is its iterated forward difference. -/
theorem finrank_eq_iterate_fwdDiff
    (K : Type*) [Field K] {m n : ℕ}
    {fs : List (BiprojRing K m n)} (hfs : BiprojectiveRegularSequence K fs)
    (j c : ℕ) :
    ((biprojectiveHilbertFunction K (Ideal.ofList fs)
        (j + fs.length) (j + fs.length + c) : ℕ) : ℚ) =
      (fwdDiff (1 : ℚ))^[fs.length]
        (fun x => Polynomial.eval x (bezoutPoly m n c)) (j : ℚ) := by
  induction hfs generalizing j with
  | nil =>
      rw [Ideal.ofList_nil]
      change ((biprojectiveHilbertFunction K
        (⊥ : Ideal (BiprojRing K m n)) j (j + c) : ℕ) : ℚ) =
          Polynomial.eval (j : ℚ) (bezoutPoly m n c)
      have hbot : biprojectiveIdealPiece K (⊥ : Ideal (BiprojRing K m n)) j (j + c) = ⊥ := by
        ext g
        simp [biprojectiveIdealPiece]
      rw [biprojectiveHilbertFunction, LinearEquiv.finrank_eq
        ((biprojectiveIdealPiece K (⊥ : Ideal (BiprojRing K m n)) j (j + c)).quotEquivOfEqBot hbot),
        finrank_biprojectivePiece, eval_bezoutPoly]
      norm_num
  | @snoc fs f hfs hf hreg ih =>
      have hrec := finrank_quotient_sup_span_add_finrank K (Ideal.ofList fs)
        (isHomogeneous K hfs) f hf hreg (j + fs.length) (j + fs.length + c)
      change biprojectiveHilbertFunction K (Ideal.ofList fs ⊔ Ideal.span {f})
          (1 + (j + fs.length)) (1 + (j + fs.length + c)) +
        biprojectiveHilbertFunction K (Ideal.ofList fs)
          (j + fs.length) (j + fs.length + c) =
        biprojectiveHilbertFunction K (Ideal.ofList fs)
          (1 + (j + fs.length)) (1 + (j + fs.length + c)) at hrec
      rw [Ideal.ofList_append, Ideal.ofList_singleton]
      simp only [List.length_append, List.length_singleton]
      have ihj := ih j
      have ihj1 := ih (j + 1)
      rw [← Nat.succ_eq_add_one, Function.iterate_succ_apply', fwdDiff]
      rw [show j + (fs.length + 1) = 1 + (j + fs.length) by omega,
        show 1 + (j + fs.length) + c = 1 + (j + fs.length + c) by omega]
      have hrecQ :
          (biprojectiveHilbertFunction K (Ideal.ofList fs ⊔ Ideal.span {f})
              (1 + (j + fs.length)) (1 + (j + fs.length + c)) : ℚ) +
            (biprojectiveHilbertFunction K (Ideal.ofList fs)
              (j + fs.length) (j + fs.length + c) : ℚ) =
            (biprojectiveHilbertFunction K (Ideal.ofList fs)
              (1 + (j + fs.length)) (1 + (j + fs.length + c)) : ℚ) := by
        exact_mod_cast hrec
      have hnew :
          (biprojectiveHilbertFunction K (Ideal.ofList fs ⊔ Ideal.span {f})
              (1 + (j + fs.length)) (1 + (j + fs.length + c)) : ℚ) =
            (biprojectiveHilbertFunction K (Ideal.ofList fs)
              (1 + (j + fs.length)) (1 + (j + fs.length + c)) : ℚ) -
            (biprojectiveHilbertFunction K (Ideal.ofList fs)
              (j + fs.length) (j + fs.length + c) : ℚ) := by
        linarith
      have ihj1' :
          (biprojectiveHilbertFunction K (Ideal.ofList fs)
              (1 + (j + fs.length)) (1 + (j + fs.length + c)) : ℚ) =
            (fwdDiff (1 : ℚ))^[fs.length]
              (fun x => Polynomial.eval x (bezoutPoly m n c)) ((j : ℚ) + 1) := by
        simpa only [show j + 1 + fs.length = 1 + (j + fs.length) by omega,
          show 1 + (j + fs.length) + c = 1 + (j + fs.length + c) by omega,
          Nat.cast_add, Nat.cast_one] using ihj1
      rw [hnew, ihj, ihj1']

/-- Multihomogeneous Bézout count for a full regular sequence of `m+n` bilinear forms. -/
theorem hilbertFunction_eq_criticalHorizonMultiplicity
    (K : Type*) [Field K] (m n : ℕ)
    {fs : List (BiprojRing K m n)} (hfs : BiprojectiveRegularSequence K fs)
    (hlen : fs.length = m + n) (j c : ℕ) :
    biprojectiveHilbertFunction K (Ideal.ofList fs)
      (j + (m + n)) (j + (m + n) + c) = criticalHorizonMultiplicity m n := by
  have h := finrank_eq_iterate_fwdDiff K hfs j c
  rw [hlen, fwdDiff_iter_bezoutPoly] at h
  rw [criticalHorizonMultiplicity]
  exact_mod_cast h

/-- Dimension form of `hilbertFunction_eq_criticalHorizonMultiplicity`. -/
theorem finrank_quotientPiece_eq_criticalHorizonMultiplicity
    (K : Type*) [Field K] (m n : ℕ)
    {fs : List (BiprojRing K m n)} (hfs : BiprojectiveRegularSequence K fs)
    (hlen : fs.length = m + n) (j c : ℕ) :
    Module.finrank K
      (BiprojectiveQuotientPiece K (Ideal.ofList fs)
        (j + (m + n)) (j + (m + n) + c)) = criticalHorizonMultiplicity m n := by
  change biprojectiveHilbertFunction K (Ideal.ofList fs)
    (j + (m + n)) (j + (m + n) + c) = criticalHorizonMultiplicity m n
  exact hilbertFunction_eq_criticalHorizonMultiplicity K m n hfs hlen j c

end BiprojectiveRegularSequence

end GaloisForLFunctions.HTGeometry
