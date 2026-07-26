import GaloisForLFunctions.RHTower.DeningerArithmeticCompactDualLocalization
import GaloisForLFunctions.RHTower.DeningerArithmeticGelfandTriple
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Canonical jet Hilbert rigging of Deninger arithmetic cohomology

The compact-open arithmetic middle cohomology is the full product of its multiplicity-bounded
local Xi jets, while its continuous compact-support dual consists exactly of finite-support jet
functionals.  The canonical Hilbert space between these two boundaries is therefore the
square-summable jet carrier

`⊕ J_rho^vee ⊂ ell^2(rho,k) ⊂ ∏ J_rho`.

This file constructs that middle carrier from the source jet equivalence.  It proves an exact
linear equivalence between compact-support cohomology and the finite jet sum and a continuous
injective map from the Hilbert carrier into compact-open ordinary cohomology.

No Frobenius symmetry, Hodge positivity, zero-location statement, or simplicity hypothesis is
used.
-/

open Complex Function Set Topology

namespace RHTower

noncomputable section

/-- One multiplicity-bounded local Xi-jet coordinate. -/
abbrev DeningerArithmeticJetCoordinate :=
  Σ rho : XiDivisorSupport, DeningerArithmeticJetIndex rho

/-- Algebraic finite-support boundary of the source jet product. -/
abbrev DeningerArithmeticJetTest :=
  DeningerArithmeticJetCoordinate →₀ ℂ

/-- Canonical Hilbert middle carrier of square-summable source jets. -/
abbrev DeningerArithmeticJetHilbert :=
  lp (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2

/-- A finite jet family acts on compact-open cohomology by the corresponding finite sum. -/
def deningerArithmeticJetTestToCompact :
    DeningerArithmeticJetTest →ₗ[ℂ]
      DeningerArithmeticTopologicalH1Compact :=
  Finsupp.lsum ℂ fun idx =>
    LinearMap.toSpanSingleton ℂ
      DeningerArithmeticTopologicalH1Compact
      (deningerCompactOpenH1Jet idx.1 idx.2)

@[simp]
theorem deningerArithmeticJetTestToCompact_single
    (idx : DeningerArithmeticJetCoordinate) (c : ℂ) :
    deningerArithmeticJetTestToCompact
        (Finsupp.single idx c) =
      c • deningerCompactOpenH1Jet idx.1 idx.2 := by
  simp [deningerArithmeticJetTestToCompact]

theorem deningerArithmeticJetTestToCompact_apply
    (a : DeningerArithmeticJetTest)
    (x : DeningerArithmeticCompactOpenH1) :
    deningerArithmeticJetTestToCompact a x =
      a.sum fun idx c =>
        c * deningerCompactOpenH1Jet idx.1 idx.2 x := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      change (0 : ℂ) = 0
      rfl
  | single_add idx c a hidx _hc ih =>
      have hadd :
          ((Finsupp.single idx c + a).sum fun j d =>
              d * deningerCompactOpenH1Jet j.1 j.2 x) =
            (Finsupp.single idx c).sum (fun j d =>
              d * deningerCompactOpenH1Jet j.1 j.2 x) +
            a.sum (fun j d =>
              d * deningerCompactOpenH1Jet j.1 j.2 x) :=
        Finsupp.sum_add_index'
          (fun _ => by simp)
          (fun _ _ _ => by ring)
      rw [map_add, deningerArithmeticJetTestToCompact_single,
        ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ih, hadd]
      simp

/-- One product basis vector, written using the flattened jet-coordinate index. -/
def deningerArithmeticJetCoordinateBasis
    (idx : DeningerArithmeticJetCoordinate) :
    DeningerArithmeticJetProduct :=
  deningerArithmeticJetBasisVector idx.1 idx.2

/-- A local jet evaluates the corresponding product basis vector by the Kronecker law. -/
theorem deningerCompactOpenH1Jet_jetCoordinateBasis
    (i j : DeningerArithmeticJetCoordinate) :
    deningerCompactOpenH1Jet i.1 i.2
        (deningerCompactOpenJetProductToH1
          (deningerArithmeticJetCoordinateBasis j)) =
      if i = j then 1 else 0 := by
  rw [← deningerCompactOpenH1AllJets_apply,
    deningerCompactOpenH1AllJets_jetProductToH1]
  by_cases hij : i = j
  · subst j
    simp [deningerArithmeticJetCoordinateBasis,
      deningerArithmeticJetBasisVector, piBasisVector]
  · have hrho :
        i.1 = j.1 → HEq i.2 j.2 → False := by
      intro hrho hk
      apply hij
      exact Sigma.ext hrho hk
    rcases i with ⟨rho, k⟩
    rcases j with ⟨tau, l⟩
    by_cases hrt : rho = tau
    · subst tau
      have hkl : k ≠ l := by
        intro h
        apply hij
        exact Sigma.ext rfl (by simp [h])
      simp [deningerArithmeticJetCoordinateBasis,
        deningerArithmeticJetBasisVector, piBasisVector,
        hij, hkl]
    · simp [deningerArithmeticJetCoordinateBasis,
        deningerArithmeticJetBasisVector, piBasisVector,
        hij, hrt]

/-- Evaluation of a finite jet functional on a product basis vector recovers its coefficient. -/
@[simp]
theorem deningerArithmeticJetTestToCompact_basis
    (a : DeningerArithmeticJetTest)
    (idx : DeningerArithmeticJetCoordinate) :
    deningerArithmeticJetTestToCompact a
        (deningerCompactOpenJetProductToH1
          (deningerArithmeticJetCoordinateBasis idx)) =
      a idx := by
  classical
  rw [deningerArithmeticJetTestToCompact_apply]
  simp_rw [deningerCompactOpenH1Jet_jetCoordinateBasis]
  have hsum :=
    Finsupp.sum_ite_eq' a idx
      (fun (_ : DeningerArithmeticJetCoordinate) (c : ℂ) => c)
  simp only [mul_ite, mul_one, mul_zero] at *
  by_cases hidx : idx ∈ a.support
  · rw [hsum, if_pos hidx]
  · have ha : a idx = 0 := by
      by_contra hne
      exact hidx (Finsupp.mem_support_iff.mpr hne)
    rw [hsum, if_neg hidx, ha]

/-- Distinct finite jet families define distinct continuous compact-support classes. -/
theorem deningerArithmeticJetTestToCompact_injective :
    Function.Injective deningerArithmeticJetTestToCompact := by
  intro a b hab
  ext idx
  have h :=
    congrArg
      (fun ell : DeningerArithmeticTopologicalH1Compact =>
        ell
          (deningerCompactOpenJetProductToH1
            (deningerArithmeticJetCoordinateBasis idx)))
      hab
  simpa using h

/-- Every continuous compact-support class is represented by one finite jet family. -/
theorem deningerArithmeticJetTestToCompact_surjective :
    Function.Surjective deningerArithmeticJetTestToCompact := by
  classical
  intro ell
  obtain ⟨S, T, hEll⟩ :=
    deningerArithmeticTopologicalH1Compact_finiteJetSupport ell
  let a : DeningerArithmeticJetTest :=
    ∑ rho : ↥S,
      ∑ k ∈ T rho.1,
        Finsupp.single
          (⟨rho.1, k⟩ : DeningerArithmeticJetCoordinate)
          (ell
            (deningerCompactOpenJetProductToH1
              (deningerArithmeticJetBasisVector rho.1 k)))
  refine ⟨a, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rw [hEll x]
  simp only [a, map_sum, deningerArithmeticJetTestToCompact_single,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  ring_nf

/--
Exact source identification of continuous compact-support cohomology with the algebraic direct
sum of local Xi-jet duals.
-/
noncomputable def deningerArithmeticJetTestCompactEquiv :
    DeningerArithmeticJetTest ≃ₗ[ℂ]
      DeningerArithmeticTopologicalH1Compact :=
  LinearEquiv.ofBijective deningerArithmeticJetTestToCompact
    ⟨deningerArithmeticJetTestToCompact_injective,
      deningerArithmeticJetTestToCompact_surjective⟩

/-- Continuous inclusion of square-summable jets into the full product jet carrier. -/
def deningerArithmeticJetHilbertToProduct :
    DeningerArithmeticJetHilbert →L[ℂ]
      DeningerArithmeticJetProduct where
  toFun a rho k := a ⟨rho, k⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply continuous_pi
    intro rho
    apply continuous_pi
    intro k
    exact
      (lp.evalCLM ℂ
        (fun _ : DeningerArithmeticJetCoordinate => ℂ)
        2 (⟨rho, k⟩ : DeningerArithmeticJetCoordinate)).continuous

@[simp]
theorem deningerArithmeticJetHilbertToProduct_apply
    (a : DeningerArithmeticJetHilbert)
    (rho : XiDivisorSupport)
    (k : DeningerArithmeticJetIndex rho) :
    deningerArithmeticJetHilbertToProduct a rho k =
      a ⟨rho, k⟩ :=
  rfl

/-- Square-summable source jets determine compact-open arithmetic cohomology classes. -/
def deningerArithmeticJetHilbertToH1 :
    DeningerArithmeticJetHilbert →L[ℂ]
      DeningerArithmeticCompactOpenH1 :=
  deningerCompactOpenJetProductToH1.comp
    deningerArithmeticJetHilbertToProduct

/-- The Hilbert-to-distribution map is injective. -/
theorem deningerArithmeticJetHilbertToH1_injective :
    Function.Injective deningerArithmeticJetHilbertToH1 := by
  intro a b hab
  apply Subtype.ext
  funext idx
  have h :=
    congrArg deningerCompactOpenH1AllJets hab
  have hidx :=
    congrFun (congrFun h idx.1) idx.2
  simpa [deningerArithmeticJetHilbertToH1] using hidx

/-- Algebraic inclusion of finite jet families into the square-summable carrier. -/
def deningerArithmeticJetTestToHilbert :
    DeningerArithmeticJetTest →ₗ[ℂ]
      DeningerArithmeticJetHilbert :=
  Finsupp.lsum ℂ fun idx =>
    lp.lsingle (E := fun _ : DeningerArithmeticJetCoordinate => ℂ)
      2 idx

@[simp]
theorem deningerArithmeticJetTestToHilbert_single
    (idx : DeningerArithmeticJetCoordinate) (c : ℂ) :
    deningerArithmeticJetTestToHilbert
        (Finsupp.single idx c) =
      lp.single 2 idx c := by
  simp [deningerArithmeticJetTestToHilbert]

/-- The algebraic finite-test inclusion preserves every jet coefficient. -/
@[simp]
theorem deningerArithmeticJetTestToHilbert_apply
    (a : DeningerArithmeticJetTest)
    (idx : DeningerArithmeticJetCoordinate) :
    deningerArithmeticJetTestToHilbert a idx = a idx := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      change (0 : ℂ) = 0
      rfl
  | single_add q c a hq _hc ih =>
      rw [map_add, lp.coeFn_add, Pi.add_apply,
        deningerArithmeticJetTestToHilbert_single, ih]
      by_cases hqi : q = idx
      · subst q
        simp
      · simp [lp.single_apply, hqi]

/-- Finite jet families are dense in the canonical jet Hilbert space. -/
theorem deningerArithmeticJetTestToHilbert_dense :
    DenseRange deningerArithmeticJetTestToHilbert := by
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.subset_univ _) isClosed_univ
  · intro x _hx
    have hsum :
        HasSum
          (fun idx : DeningerArithmeticJetCoordinate =>
            lp.single 2 idx (x idx))
          x :=
      lp.hasSum_single ENNReal.ofNat_ne_top x
    apply isClosed_closure.mem_of_tendsto hsum
    filter_upwards [] with S
    apply subset_closure
    let a : DeningerArithmeticJetTest :=
      ∑ idx ∈ S, Finsupp.single idx (x idx)
    refine ⟨a, ?_⟩
    simp [a, deningerArithmeticJetTestToHilbert]

/--
Conjugate-linear finite-test inclusion forced by the variance of the continuous-dual pairing.
-/
def deningerArithmeticJetTestToHilbertConj :
    DeningerArithmeticJetTest →ₛₗ[starRingEnd ℂ]
      DeningerArithmeticJetHilbert where
  toFun a := star (deningerArithmeticJetTestToHilbert a)
  map_add' a b := by
    rw [map_add, star_add]
  map_smul' c a := by
    ext idx
    simp [map_smul]

/-- Conjugate finite-test inclusion is coefficientwise complex conjugation. -/
@[simp]
theorem deningerArithmeticJetTestToHilbertConj_apply
    (a : DeningerArithmeticJetTest)
    (idx : DeningerArithmeticJetCoordinate) :
    deningerArithmeticJetTestToHilbertConj a idx =
      (starRingEnd ℂ) (a idx) := by
  change
    (starRingEnd ℂ)
        (deningerArithmeticJetTestToHilbert a idx) =
      (starRingEnd ℂ) (a idx)
  rw [deningerArithmeticJetTestToHilbert_apply]

@[simp]
theorem deningerArithmeticJetTestToHilbertConj_single
    (idx : DeningerArithmeticJetCoordinate) (c : ℂ) :
    deningerArithmeticJetTestToHilbertConj
        (Finsupp.single idx c) =
      lp.single 2 idx ((starRingEnd ℂ) c) := by
  ext j
  by_cases hji : j = idx
  · subst j
    simp [deningerArithmeticJetTestToHilbertConj]
  · simp [deningerArithmeticJetTestToHilbertConj, hji]

/-- The Hilbert distribution embedding has the expected jet coordinates. -/
@[simp]
theorem deningerCompactOpenH1Jet_jetHilbertToH1
    (idx : DeningerArithmeticJetCoordinate)
    (x : DeningerArithmeticJetHilbert) :
    deningerCompactOpenH1Jet idx.1 idx.2
        (deningerArithmeticJetHilbertToH1 x) =
      x idx := by
  rw [← deningerCompactOpenH1AllJets_apply]
  simp [deningerArithmeticJetHilbertToH1]

/--
The finite-test/`ell^2`/product rigging realizes the original source Poincare evaluation pairing.
-/
theorem deningerArithmeticJetHilbert_pairing
    (a : DeningerArithmeticJetTest)
    (x : DeningerArithmeticJetHilbert) :
    deningerArithmeticJetTestToCompact a
        (deningerArithmeticJetHilbertToH1 x) =
      @inner ℂ DeningerArithmeticJetHilbert _
        (deningerArithmeticJetTestToHilbertConj a) x := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      simp [deningerArithmeticJetTestToHilbertConj]
  | single_add idx c a hidx _hc ih =>
      rw [map_add, deningerArithmeticJetTestToCompact_single,
        ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply,
        deningerCompactOpenH1Jet_jetHilbertToH1,
        map_add, inner_add_left,
        deningerArithmeticJetTestToHilbertConj_single,
        lp.inner_single_left, ih]
      simp [RCLike.inner_apply]
      ring

/-- Conjugate finite jet families are also dense in the canonical Hilbert carrier. -/
theorem deningerArithmeticJetTestToHilbertConj_dense :
    DenseRange deningerArithmeticJetTestToHilbertConj := by
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.subset_univ _) isClosed_univ
  · intro x _hx
    have hsum :
        HasSum
          (fun idx : DeningerArithmeticJetCoordinate =>
            lp.single 2 idx (x idx))
          x :=
      lp.hasSum_single ENNReal.ofNat_ne_top x
    apply isClosed_closure.mem_of_tendsto hsum
    filter_upwards [] with S
    apply subset_closure
    let a : DeningerArithmeticJetTest :=
      ∑ idx ∈ S,
        Finsupp.single idx ((starRingEnd ℂ) (x idx))
    refine ⟨a, ?_⟩
    simp [a, deningerArithmeticJetTestToHilbertConj_single]

/--
Restriction of a compact-support distribution to the canonical square-summable jet carrier.

Continuity uses the strong topology on the source dual: precomposition by the fixed continuous
map from `ell^2` into compact-open cohomology is continuous for bounded convergence.
-/
def deningerArithmeticJetCompactRestrict :
    DeningerArithmeticTopologicalH1Compact →L[ℂ]
      StrongDual ℂ DeningerArithmeticJetHilbert :=
  ContinuousLinearMap.precomp ℂ
    deningerArithmeticJetHilbertToH1

/--
Canonical conjugate-linear embedding of compact-support arithmetic cohomology into the jet
Hilbert carrier, obtained by Fréchet--Riesz representation after restriction.
-/
def deningerArithmeticJetCompactToHilbert :
    DeningerArithmeticTopologicalH1Compact →L⋆[ℂ]
      DeningerArithmeticJetHilbert :=
  ((InnerProductSpace.toDual ℂ
      DeningerArithmeticJetHilbert).symm :
      StrongDual ℂ DeningerArithmeticJetHilbert →L⋆[ℂ]
        DeningerArithmeticJetHilbert).comp
    deningerArithmeticJetCompactRestrict

/-- Fréchet--Riesz realizes the original compact-support/distribution pairing exactly. -/
@[simp]
theorem deningerArithmeticJetCompactToHilbert_pairing
    (ell : DeningerArithmeticTopologicalH1Compact)
    (x : DeningerArithmeticJetHilbert) :
    @inner ℂ DeningerArithmeticJetHilbert _
        (deningerArithmeticJetCompactToHilbert ell) x =
      ell (deningerArithmeticJetHilbertToH1 x) := by
  simp [deningerArithmeticJetCompactToHilbert,
    deningerArithmeticJetCompactRestrict,
    InnerProductSpace.toDual_symm_apply]

/-- On finite source tests, the Fréchet--Riesz embedding is coefficientwise conjugation. -/
@[simp]
theorem deningerArithmeticJetCompactToHilbert_test
    (a : DeningerArithmeticJetTest) :
    deningerArithmeticJetCompactToHilbert
        (deningerArithmeticJetTestToCompact a) =
      deningerArithmeticJetTestToHilbertConj a := by
  apply (InnerProductSpace.toDualMap ℂ
    DeningerArithmeticJetHilbert).injective
  apply ContinuousLinearMap.ext
  intro x
  simp only [InnerProductSpace.toDualMap_apply_apply]
  rw [deningerArithmeticJetCompactToHilbert_pairing,
    deningerArithmeticJetHilbert_pairing]

/-- Compact-support arithmetic cohomology has dense image in the canonical jet Hilbert carrier. -/
theorem deningerArithmeticJetCompactToHilbert_dense :
    DenseRange deningerArithmeticJetCompactToHilbert := by
  apply DenseRange.of_comp
    (f := deningerArithmeticJetCompactToHilbert)
    (g := deningerArithmeticJetTestToCompact)
  have hfun :
      deningerArithmeticJetCompactToHilbert ∘
          deningerArithmeticJetTestToCompact =
        deningerArithmeticJetTestToHilbertConj := by
    funext a
    exact deningerArithmeticJetCompactToHilbert_test a
  rw [hfun]
  exact deningerArithmeticJetTestToHilbertConj_dense

/--
Unconditional source-defined Gelfand triple

`H^1_c = direct sum of jets  ⊂  ell^2(jets)  ⊂  product of jets = H^1`.
-/
def deningerArithmeticJetGelfandTriple :
    DeningerArithmeticGelfandTriple
      DeningerArithmeticJetHilbert where
  testToHilbert := deningerArithmeticJetCompactToHilbert
  hilbertToDistribution := deningerArithmeticJetHilbertToH1
  test_dense := deningerArithmeticJetCompactToHilbert_dense
  hilbertToDistribution_injective :=
    deningerArithmeticJetHilbertToH1_injective
  pairing_compatibility ell x :=
    (deningerArithmeticJetCompactToHilbert_pairing ell x).symm

end

end RHTower
