import GaloisForLFunctions.HTGeometry.AllDepthNormalForm
import GaloisForLFunctions.HTGeometry.AllDepthOperatorCriterion
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetSpanDecomposition
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaHypertranscendence
import GaloisForLFunctions.HTGeometry.DifferentialIndependentPerturbation
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetCompleteDifferentialMatroid

/-!
# From the all-depth class to the labelled deep coordinates

The universal carrier of the full direction set is the multiple elliptic gamma logarithmic
derivative itself, and every element of its jet-translate span is a finite constant-coefficient
differential-translation operator applied to it.  Combined with the coset span decomposition this
expresses every member of the all-depth class as an operator row on the labelled deep coordinates,
modulo a differentially algebraic error.

* `universalCarrierMero_univ`;
* `exists_transOp_of_mem_carrierSpan`;
* `differentialJet_finsetSum`, `differentialJet_smul_complex`.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The carrier of the full direction set is the multiple elliptic gamma coordinate.** -/
theorem universalCarrierMero_univ (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    universalCarrierMero τ hτ (Finset.univ : Finset ι) = multipleEllipticGammaLogDerivMero τ hτ := by
  have hset : (Finset.univ : Finset ι) \ (Finset.univ : Finset ι) = (∅ : Finset ι) := by
    simp
  rw [universalCarrierMero, hset]
  exact multipleEllipticGammaLogDerivFaceMero_empty τ hτ

theorem differentialJet_zero_elem (n : ℕ) :
    differentialJet n (0 : meroField (Set.univ : Set ℂ)) = 0 := by
  induction n with
  | zero => simp
  | succ m ihm =>
      rw [differentialJet_succ, ihm]
      simp

/-- Jets are additive over finite families. -/
theorem differentialJet_finsetSum {κ : Type*} (n : ℕ) (M : Finset κ)
    (y : κ → meroField (Set.univ : Set ℂ)) :
    differentialJet n (∑ m ∈ M, y m) = ∑ m ∈ M, differentialJet n (y m) := by
  classical
  induction M using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact differentialJet_zero_elem n
  | @insert a M' ha ihM =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ihM]
      exact differentialJet_add_apply n _ _

/-- Jets are `ℂ`-linear. -/
theorem differentialJet_smul_complex (n : ℕ) (c : ℂ) (y : meroField (Set.univ : Set ℂ)) :
    differentialJet n (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * y)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) c * differentialJet n y := by
  induction n with
  | zero => simp
  | succ m ihm =>
      rw [differentialJet_succ, differentialJet_succ, ihm]
      have h := differentialJet_algebraMap_apply
        (F := ℂ) (K := meroField (Set.univ : Set ℂ)) 1 c
      simp only [differentialJet_succ, differentialJet_zero] at h
      have hzero : (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ = 0 := by
        rw [h]
        have : (c : ℂ)′ = 0 := rfl
        rw [this, map_zero]
      simp [hzero]

/-- **Every element of the carrier span is a finite differential-translation operator applied to
the carrier.** -/
theorem exists_transOp_of_mem_carrierSpan (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ∈ carrierSpan τ hτ s) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (jj : Fin n → ℕ) (bb : Fin n → ℂ),
      y = transOpMero (Finset.univ : Finset (Fin n)) c jj bb (universalCarrierMero τ hτ s) := by
  classical
  rw [carrierSpan, Submodule.mem_span_set'] at hy
  obtain ⟨n, f, g, hsum⟩ := hy
  have hg : ∀ i : Fin n, ∃ (m : ℕ) (b : ℂ),
      (g i : meroField (Set.univ : Set ℂ))
        = differentialJet m (addTranslationMeroEquiv b (universalCarrierMero τ hτ s)) :=
    fun i => (g i).2
  choose jj bb hgval using hg
  refine ⟨n, f, jj, bb, ?_⟩
  rw [transOpMero, ← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hgval i, Algebra.smul_def]

/-- Jets of a differentially algebraic germ are differentially algebraic. -/
theorem differentialAlgebraicOver_differentialJet
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {y : E} (hy : DifferentialAlgebraicOver F y) (n : ℕ) :
    DifferentialAlgebraicOver F (differentialJet n y) := by
  refine differentialAlgebraicOver_of_mem_differentialAdjoin_singleton hy ?_
  induction n with
  | zero =>
      simpa using subset_differentialAdjoin F ({y} : Set E) rfl
  | succ m ihm =>
      rw [differentialJet_succ]
      exact derivationClosed_differentialAdjoin F ({y} : Set E) ihm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **A jet of a complex translate of the carrier is a finite combination of jets of labelled deep
coordinates, modulo a differentially algebraic error.** -/
theorem exists_deepCombination_of_jet_translate (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) {A : Set ℂ}
    (hcover : ∀ z : ℂ, ∃ a ∈ A, z - a ∈ fullPeriodLattice τ) (j : ℕ) (b : ℂ) :
    ∃ (m : ℕ) (a : Fin m → ℂ) (g : Fin m → meroField (Set.univ : Set ℂ))
      (d : meroField (Set.univ : Set ℂ)),
      (∀ t, g t ∈ cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
      DifferentialAlgebraicOver ℂ d ∧
      differentialJet j (addTranslationMeroEquiv b (multipleEllipticGammaLogDerivMero τ hτ))
        = (∑ t, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a t) * differentialJet j (g t))
          + d := by
  classical
  obtain ⟨y, d0, hyspan, hd0, hsplit⟩ :=
    arbitraryTranslate_eq_deepSpan_add_differentialAlgebraic τ hτ hQ hι hcover b
  rw [Submodule.mem_span_set'] at hyspan
  obtain ⟨m, aa, gg, hgsum⟩ := hyspan
  refine ⟨m, aa, fun t => (gg t : meroField (Set.univ : Set ℂ)), differentialJet j d0,
    fun t => (gg t).2, differentialAlgebraicOver_differentialJet hd0 j, ?_⟩
  rw [hsplit, differentialJet_add_apply, ← hgsum, differentialJet_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Algebra.smul_def, differentialJet_smul_complex]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **Every member of the all-depth class is a finite combination of jets of labelled deep
coordinates, modulo a differentially algebraic error.** -/
theorem exists_deepRow_of_class (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) {A : Set ℂ}
    (hcover : ∀ z : ℂ, ∃ a ∈ A, z - a ∈ fullPeriodLattice τ)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (hper : PeriodicOneGerm f)
    (hmixed : MixedConstGermSet τ (Finset.univ : Finset ι) f Cst) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → ℂ) (jj : κ → ℕ)
      (g : κ → meroField (Set.univ : Set ℂ)),
      (∀ t, g t ∈ cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
      DifferentialAlgebraicOver ℂ
        (x - ∑ t : κ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a t)
          * differentialJet (jj t) (g t)) := by
  classical
  obtain ⟨y, hyspan, hDA⟩ := exists_carrierSpan_normal_form τ hτ hQ
    (Finset.univ : Finset ι).card (Finset.univ : Finset ι) rfl (by simpa using hι) x Cst f
    hx hper hmixed
  obtain ⟨n, c, jj0, bb, hy⟩ := exists_transOp_of_mem_carrierSpan τ hτ (Finset.univ : Finset ι)
    hyspan
  have hterm : ∀ i : Fin n, ∃ (m : ℕ) (aa : Fin m → ℂ) (gg : Fin m → meroField (Set.univ : Set ℂ))
      (d : meroField (Set.univ : Set ℂ)),
      (∀ t, gg t ∈ cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
      DifferentialAlgebraicOver ℂ d ∧
      differentialJet (jj0 i)
          (addTranslationMeroEquiv (bb i) (multipleEllipticGammaLogDerivMero τ hτ))
        = (∑ t, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (aa t)
            * differentialJet (jj0 i) (gg t)) + d :=
    fun i => exists_deepCombination_of_jet_translate τ hτ hQ hι hcover (jj0 i) (bb i)
  choose mm aa gg dd hggmem hddDA hdec using hterm
  refine ⟨Σ i : Fin n, Fin (mm i), inferInstance,
    fun q => c q.1 * aa q.1 q.2, fun q => jj0 q.1, fun q => gg q.1 q.2, ?_, ?_⟩
  · rintro ⟨i, t⟩
    exact hggmem i t
  · have hcarrier : universalCarrierMero τ hτ (Finset.univ : Finset ι)
        = multipleEllipticGammaLogDerivMero τ hτ := universalCarrierMero_univ τ hτ
    have hstep : ∀ i : Fin n,
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i) * differentialJet (jj0 i)
            (addTranslationMeroEquiv (bb i) (multipleEllipticGammaLogDerivMero τ hτ))
          = (∑ t : Fin (mm i), algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i * aa i t)
              * differentialJet (jj0 i) (gg i t))
            + algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i) * dd i := by
      intro i
      rw [hdec i, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul]
      ring
    have hyval : y = (∑ q : Σ i : Fin n, Fin (mm i),
          algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c q.1 * aa q.1 q.2)
            * differentialJet (jj0 q.1) (gg q.1 q.2))
        + ∑ i : Fin n, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i) * dd i := by
      rw [hy, transOpMero, hcarrier, Finset.sum_congr rfl fun i _ => hstep i,
        Finset.sum_add_distrib]
      congr 1
      rw [Fintype.sum_sigma]
    have hsplit : x - ∑ q : Σ i : Fin n, Fin (mm i),
        algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c q.1 * aa q.1 q.2)
          * differentialJet (jj0 q.1) (gg q.1 q.2)
        = (x - y) + ∑ i : Fin n, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (c i) * dd i := by
      rw [hyval]
      ring
    rw [hsplit]
    refine differentialAlgebraicOver_add hDA ?_
    refine differentialAlgebraicOver_finset_sum _ fun i _ => ?_
    exact differentialAlgebraicOver_mul
      (HTGeometry.differentialAlgebraicOver_algebraMap _) (hddDA i)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **Every finite family in the all-depth class is an operator row family on the labelled deep
coordinates, modulo differentially algebraic errors.** -/
theorem exists_operatorRow_of_class_family (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) {A : Set ℂ}
    (hcover : ∀ z : ℂ, ∃ a ∈ A, z - a ∈ fullPeriodLattice τ)
    {ρ : Type} [Fintype ρ] (Fam : ρ → meroField (Set.univ : Set ℂ)) (f : ρ → ℂ → ℂ)
    (Cst : ρ → ℂ) (hreal : ∀ r, RealizesMero (Fam r) (f r))
    (hper : ∀ r, PeriodicOneGerm (f r))
    (hmixed : ∀ r, MixedConstGermSet τ (Finset.univ : Finset ι) (f r) (Cst r)) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
      (xc : κ → meroField (Set.univ : Set ℂ)) (L : ρ → κ → Polynomial ℂ),
      (∀ k, xc k ∈ cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
      Function.Injective xc ∧
      ∀ r, DifferentialAlgebraicOver ℂ (Fam r - differentialOperatorRowApply L xc r) := by
  classical
  have hrow : ∀ r : ρ, ∃ (κ : Type) (_ : Fintype κ) (a : κ → ℂ) (jj : κ → ℕ)
      (g : κ → meroField (Set.univ : Set ℂ)),
      (∀ t, g t ∈ cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
      DifferentialAlgebraicOver ℂ
        (Fam r - ∑ t : κ, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a t)
          * differentialJet (jj t) (g t)) :=
    fun r => exists_deepRow_of_class τ hτ hQ hι hcover (hreal r) (hper r) (hmixed r)
  choose kk inst a jj g hgmem hDA using hrow
  letI : ∀ r, Fintype (kk r) := inst
  set P : Finset (meroField (Set.univ : Set ℂ)) :=
    Finset.image (fun q : Σ r : ρ, kk r => g q.1 q.2) Finset.univ with hP
  have hgP : ∀ (r : ρ) (t : kk r), g r t ∈ P := by
    intro r t
    exact Finset.mem_image.mpr ⟨⟨r, t⟩, Finset.mem_univ _, rfl⟩
  refine ⟨{v : meroField (Set.univ : Set ℂ) // v ∈ P}, inferInstance, inferInstance,
    (fun k : {v : meroField (Set.univ : Set ℂ) // v ∈ P} => (k : meroField (Set.univ : Set ℂ))),
    (fun (r : ρ) (k : {v : meroField (Set.univ : Set ℂ) // v ∈ P}) => ∑ t : kk r,
      if g r t = (k : meroField (Set.univ : Set ℂ))
        then Polynomial.monomial (jj r t) (a r t) else 0), ?_, Subtype.val_injective, ?_⟩
  · rintro ⟨v, hv⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hv
    exact hgmem q.1 q.2
  · intro r
    have hval : differentialOperatorRowApply
        (fun (r : ρ) (k : {v : meroField (Set.univ : Set ℂ) // v ∈ P}) => ∑ t : kk r,
          if g r t = (k : meroField (Set.univ : Set ℂ))
            then Polynomial.monomial (jj r t) (a r t) else 0)
        (fun k : {v : meroField (Set.univ : Set ℂ) // v ∈ P} =>
          (k : meroField (Set.univ : Set ℂ))) r
        = ∑ t : kk r, algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a r t)
            * differentialJet (jj r t) (g r t) := by
      rw [differentialOperatorRowApply]
      have hk : ∀ k : {v : meroField (Set.univ : Set ℂ) // v ∈ P},
          differentialOperatorApply
            (∑ t : kk r, if g r t = (k : meroField (Set.univ : Set ℂ))
              then Polynomial.monomial (jj r t) (a r t) else 0)
            (k : meroField (Set.univ : Set ℂ))
          = ∑ t : kk r, if g r t = (k : meroField (Set.univ : Set ℂ))
              then algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a r t)
                * differentialJet (jj r t) (k : meroField (Set.univ : Set ℂ)) else 0 := by
        intro k
        rw [differentialOperatorApply_finsetSum]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hc : g r t = (k : meroField (Set.univ : Set ℂ))
        · rw [if_pos hc, if_pos hc, differentialOperatorApply_monomial]
        · rw [if_neg hc, if_neg hc, differentialOperatorApply_zero]
      rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hone : (∑ k : {v : meroField (Set.univ : Set ℂ) // v ∈ P},
          if g r t = (k : meroField (Set.univ : Set ℂ))
            then algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a r t)
              * differentialJet (jj r t) (k : meroField (Set.univ : Set ℂ)) else 0)
          = algebraMap ℂ (meroField (Set.univ : Set ℂ)) (a r t)
              * differentialJet (jj r t) (g r t) := by
        rw [Finset.sum_eq_single_of_mem (⟨g r t, hgP r t⟩ :
          {v : meroField (Set.univ : Set ℂ) // v ∈ P}) (Finset.mem_univ _)
          (fun k _ hne => by
            refine if_neg fun hc => hne ?_
            exact Subtype.ext hc.symm), if_pos rfl]
      exact hone
    rw [hval]
    exact hDA r

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The complete all-depth differential matroid.**  Every finite family in the all-depth
mixed-constraint class has the differential matroid of an operator row family on the labelled deep
coordinates, and therefore the ordinary localized row matroid. -/
theorem allDepth_completeDifferentialRank (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) {A : Set ℂ}
    (hA : CosetSeparated τ A)
    (hcover : ∀ z : ℂ, ∃ a ∈ A, z - a ∈ fullPeriodLattice τ)
    {ρ : Type} [Fintype ρ] [DecidableEq ρ] (Fam : ρ → meroField (Set.univ : Set ℂ))
    (f : ρ → ℂ → ℂ) (Cst : ρ → ℂ) (hreal : ∀ r, RealizesMero (Fam r) (f r))
    (hper : ∀ r, PeriodicOneGerm (f r))
    (hmixed : ∀ r, MixedConstGermSet τ (Finset.univ : Finset ι) (f r) (Cst r)) (I : Finset ρ) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
      (xc : κ → meroField (Set.univ : Set ℂ)) (L : ρ → κ → Polynomial ℂ),
      (∀ k, xc k ∈ cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
      Function.Injective xc ∧
      (differentialFamilyMatroid (F := ℂ) Fam).eRk (↑I : Set ρ)
        = (Module.finrank (FractionRing (Polynomial ℂ))
            (Submodule.span (FractionRing (Polynomial ℂ))
              ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ρ))) : ℕ∞) := by
  classical
  obtain ⟨κ, instκ, instDκ, xc, L, hxmem, hxinj, hDA⟩ :=
    exists_operatorRow_of_class_family τ hτ hQ hι hcover Fam f Cst hreal hper hmixed
  letI := instκ
  letI := instDκ
  refine ⟨κ, instκ, instDκ, xc, L, hxmem, hxinj, ?_⟩
  have hmat : differentialFamilyMatroid (F := ℂ) (differentialOperatorRowApply L xc)
      = differentialFamilyMatroid (F := ℂ) Fam :=
    HTGeometry.differentialFamilyMatroid_congr_of_sub_differentialAlgebraic (fun r => hDA r)
  rw [← hmat]
  exact cosetCompleteDifferentialRank τ hτ hQ hι hA xc hxmem hxinj L I

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The complete all-depth differential matroid over the natural rational base `ℂ(z)`.** -/
theorem allDepth_completeDifferentialRank_rationalBase (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) {A : Set ℂ}
    (hA : CosetSeparated τ A)
    (hcover : ∀ z : ℂ, ∃ a ∈ A, z - a ∈ fullPeriodLattice τ)
    {ρ : Type} [Fintype ρ] [DecidableEq ρ] (Fam : ρ → meroField (Set.univ : Set ℂ))
    (f : ρ → ℂ → ℂ) (Cst : ρ → ℂ) (hreal : ∀ r, RealizesMero (Fam r) (f r))
    (hper : ∀ r, PeriodicOneGerm (f r))
    (hmixed : ∀ r, MixedConstGermSet τ (Finset.univ : Finset ι) (f r) (Cst r)) (I : Finset ρ) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
      (xc : κ → meroField (Set.univ : Set ℂ)) (L : ρ → κ → Polynomial ℂ),
      (∀ k, xc k ∈ cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
      Function.Injective xc ∧
      (differentialFamilyMatroid (F := meromorphicRationalCoordinateField) Fam).eRk
          (↑I : Set ρ)
        = (Module.finrank (FractionRing (Polynomial ℂ))
            (Submodule.span (FractionRing (Polynomial ℂ))
              ((fun i => localizeOperatorRow (L i)) '' (↑I : Set ρ))) : ℕ∞) := by
  classical
  obtain ⟨κ, instκ, instDκ, xc, L, hxmem, hxinj, hDA⟩ :=
    exists_operatorRow_of_class_family τ hτ hQ hι hcover Fam f Cst hreal hper hmixed
  letI := instκ
  letI := instDκ
  refine ⟨κ, instκ, instDκ, xc, L, hxmem, hxinj, ?_⟩
  have hbase : differentialFamilyMatroid (F := meromorphicRationalCoordinateField) Fam
      = differentialFamilyMatroid (F := ℂ) Fam := by
    rw [differentialFamilyMatroid, differentialFamilyMatroid,
      differentialMatroid_meromorphicRationalCoordinateField_eq]
  rw [hbase]
  have hmat : differentialFamilyMatroid (F := ℂ) (differentialOperatorRowApply L xc)
      = differentialFamilyMatroid (F := ℂ) Fam :=
    HTGeometry.differentialFamilyMatroid_congr_of_sub_differentialAlgebraic (fun r => hDA r)
  rw [← hmat]
  exact cosetCompleteDifferentialRank τ hτ hQ hι hA xc hxmem hxinj L I

end

end GaloisForLFunctions
