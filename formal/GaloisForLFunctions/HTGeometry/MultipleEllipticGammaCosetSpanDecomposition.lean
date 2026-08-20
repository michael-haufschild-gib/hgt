import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaCosetCompleteDifferentialMatroid
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaStructuralSpanDecomposition
import GaloisForLFunctions.HTGeometry.FacePacketDisplacementFreeness

/-!
# The universal cyclic carrier reduction for arbitrary complex translations

Every complex translate of the top multiple elliptic-gamma logarithmic derivative is, modulo a
differentially algebraic function, a finite `ℂ`-linear combination of the labelled deep
face-packet coordinates.  Together with `cosetProperFacePackets_diffIndepOn` this is the
arbitrary-translation form of the universal cyclic carrier reduction: the whole cyclic module
`ℂ[∂][ℂ] · Ψ` is spanned, modulo differentially algebraic errors, by one jointly free system of
coordinates indexed by external cosets and faces.

* `fullPeriodSubgroup` — the period lattice as an additive subgroup;
* **`exists_cosetTransversal`** — a coset-separated label set meeting every class;
* **`cosetTranslate_mem_span`** — every labelled structural translate lies in the labelled total
  packet span;
* **`cosetTranslate_eq_deepSpan_add_differentialAlgebraic`** — the reduction, modulo a
  differentially algebraic error;
* **`arbitraryTranslate_eq_deepSpan_add_differentialAlgebraic`** — its arbitrary-complex-shift
  form for a transversal label set.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The period lattice as a subgroup, and transversals -/

/-- The period lattice `ℤ + ∑_i ℤ τ_i` as an additive subgroup of `ℂ`. -/
def fullPeriodSubgroup (τ : ι → ℂ) : AddSubgroup ℂ where
  carrier := fullPeriodLattice τ
  zero_mem' := zero_mem_fullPeriodLattice τ
  add_mem' hx hy := add_mem_fullPeriodLattice τ hx hy
  neg_mem' hx := by
    have := sub_mem_fullPeriodLattice τ (zero_mem_fullPeriodLattice τ) hx
    simpa using this

omit [DecidableEq ι] in
theorem mem_fullPeriodSubgroup_iff (τ : ι → ℂ) {z : ℂ} :
    z ∈ fullPeriodSubgroup τ ↔ z ∈ fullPeriodLattice τ := Iff.rfl

/-- **A coset transversal exists.**  Some coset-separated label set meets every class of
`ℂ / (ℤ + ∑_i ℤ τ_i)`. -/
theorem exists_cosetTransversal (τ : ι → ℂ) :
    ∃ A : Set ℂ, CosetSeparated τ A ∧
      ∀ z : ℂ, ∃ a ∈ A, z - a ∈ fullPeriodLattice τ := by
  classical
  refine ⟨Set.range (fun c : ℂ ⧸ fullPeriodSubgroup τ => c.out), ?_, ?_⟩
  · rintro a ⟨c, rfl⟩ b ⟨c', rfl⟩ hab hmem
    have hcc : (c : ℂ ⧸ fullPeriodSubgroup τ) = c' := by
      have hq : ((c.out : ℂ) : ℂ ⧸ fullPeriodSubgroup τ) =
          ((c'.out : ℂ) : ℂ ⧸ fullPeriodSubgroup τ) :=
        QuotientAddGroup.eq_iff_sub_mem.mpr hmem
      rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at hq
    exact hab (by rw [hcc])
  · intro z
    refine ⟨(QuotientAddGroup.mk (s := fullPeriodSubgroup τ) z).out, ⟨_, rfl⟩, ?_⟩
    have hq : ((z : ℂ) : ℂ ⧸ fullPeriodSubgroup τ) =
        (((QuotientAddGroup.mk (s := fullPeriodSubgroup τ) z).out : ℂ) :
          ℂ ⧸ fullPeriodSubgroup τ) := by
      rw [QuotientAddGroup.out_eq']
    exact QuotientAddGroup.eq_iff_sub_mem.mp hq

/-! ## The labelled total packet and its span -/

/-- The union of the labelled external translation packets of every deletion face. -/
def cosetTotalPacket (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) :
    Set (meroField (Set.univ : Set ℂ)) :=
  ⋃ J : Finset ι, cosetFacePacket τ hτ A J

theorem cosetLogDerivMero_mem_cosetTotalPacket (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {A : Set ℂ} {a : ℂ} (ha : a ∈ A) :
    addTranslationMeroEquiv a (multipleEllipticGammaLogDerivMero τ hτ) ∈
      cosetTotalPacket τ hτ A := by
  refine Set.mem_iUnion.mpr ⟨(∅ : Finset ι), ⟨a, ⟨a, ha, 0, ⟨0, fun _ _ => rfl, by simp⟩,
    by ring⟩, ?_⟩⟩
  show addTranslationMeroEquiv a (multipleEllipticGammaLogDerivFaceMero τ hτ ∅) = _
  rw [multipleEllipticGammaLogDerivFaceMero_empty]

set_option maxHeartbeats 1000000 in
/-- A surviving direction moves a labelled packet element inside the labelled total span. -/
theorem cosetFacePacket_zsmul_sub_mem_span (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (J : Finset ι) {p : ι} (hp : p ∉ J) (m : ℤ) {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ cosetFacePacket τ hτ A J) :
    addTranslationMeroEquiv ((m : ℂ) * τ p) y - y ∈
      Submodule.span ℂ (cosetTotalPacket τ hτ A) := by
  classical
  set w : meroField (Set.univ : Set ℂ) := addTranslationMeroEquiv (τ p) y - y with hwdef
  have hw : w ∈ cosetFacePacket τ hτ A (insert p J) :=
    cosetFacePacket_translate_sub_mem τ hτ A J hp hy
  have hmemK : ∀ k : ℤ, addTranslationMeroEquiv ((k : ℂ) * τ p) w ∈
      Submodule.span ℂ (cosetTotalPacket τ hτ A) := by
    intro k
    refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨insert p J, ?_⟩)
    exact cosetFacePacket_zsmul_translate_mem τ hτ A (insert p J)
      (Finset.mem_insert_self p J) k hw
  induction m using Int.induction_on with
  | zero =>
      have hz : addTranslationMeroEquiv (((0 : ℤ) : ℂ) * τ p) y - y = 0 := by
        rw [Int.cast_zero, zero_mul, addTranslationMeroEquiv_zero_apply, sub_self]
      rw [hz]
      exact Submodule.zero_mem _
  | succ k ih =>
      have hcast : ((((k : ℤ) + 1 : ℤ)) : ℂ) * τ p = (((k : ℤ) : ℂ) * τ p) + τ p := by
        push_cast; ring
      have hsplit : addTranslationMeroEquiv ((((k : ℤ) + 1 : ℤ) : ℂ) * τ p) y - y =
          (addTranslationMeroEquiv (((k : ℤ) : ℂ) * τ p) y - y) +
            addTranslationMeroEquiv (((k : ℤ) : ℂ) * τ p) w := by
        rw [hwdef, map_sub, hcast, ← addTranslationMeroEquiv_add]
        ring
      rw [hsplit]
      exact Submodule.add_mem _ ih (hmemK (k : ℤ))
  | pred k ih =>
      have hcast : ((((-(k : ℤ)) - 1 : ℤ)) : ℂ) * τ p + τ p = ((-(k : ℤ) : ℤ) : ℂ) * τ p := by
        push_cast; ring
      have hsplit : addTranslationMeroEquiv (((-(k : ℤ) - 1 : ℤ) : ℂ) * τ p) y - y =
          (addTranslationMeroEquiv (((-(k : ℤ) : ℤ) : ℂ) * τ p) y - y) -
            addTranslationMeroEquiv (((-(k : ℤ) - 1 : ℤ) : ℂ) * τ p) w := by
        rw [hwdef, map_sub, addTranslationMeroEquiv_add, hcast]
        ring
      rw [hsplit]
      exact Submodule.sub_mem _ ih (hmemK (-(k : ℤ) - 1))

set_option maxHeartbeats 1000000 in
/-- **The labelled total packet span is translation stable.** -/
theorem cosetTotalPacket_span_translate_mem (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ)
    (p : ι) (m : ℤ) {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ Submodule.span ℂ (cosetTotalPacket τ hτ A)) :
    addTranslationMeroEquiv ((m : ℂ) * τ p) x ∈
      Submodule.span ℂ (cosetTotalPacket τ hτ A) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨J, hyJ⟩ := Set.mem_iUnion.mp hy
      by_cases hp : p ∈ J
      · exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨J,
          cosetFacePacket_zsmul_translate_mem τ hτ A J hp m hyJ⟩)
      · have hy' : y ∈ Submodule.span ℂ (cosetTotalPacket τ hτ A) :=
          Submodule.subset_span (Set.mem_iUnion.mpr ⟨J, hyJ⟩)
        have hsub := cosetFacePacket_zsmul_sub_mem_span τ hτ A J hp m hyJ
        simpa using Submodule.add_mem _ hsub hy'
  | zero => simp
  | add y z _ _ ihy ihz => simpa [map_add] using Submodule.add_mem _ ihy ihz
  | smul c y _ ih =>
      have hsmul : addTranslationMeroEquiv ((m : ℂ) * τ p) (c • y) =
          c • addTranslationMeroEquiv ((m : ℂ) * τ p) y := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul,
          addTranslationMeroEquiv_algebraMap_complex]
      rw [hsmul]
      exact Submodule.smul_mem _ c ih

set_option maxHeartbeats 1000000 in
/-- **Every labelled structural translate of the top primitive lies in the labelled packet
span.** -/
theorem cosetTranslate_mem_span (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    {A : Set ℂ} {a : ℂ} (ha : a ∈ A) (n : ι → ℤ) (T : Finset ι) :
    addTranslationMeroEquiv (a + ∑ i ∈ T, (n i : ℂ) * τ i)
        (multipleEllipticGammaLogDerivMero τ hτ) ∈
      Submodule.span ℂ (cosetTotalPacket τ hτ A) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simpa using
        Submodule.subset_span (cosetLogDerivMero_mem_cosetTotalPacket τ hτ ha)
  | @insert p T hpT ih =>
      have hsum : a + ∑ i ∈ insert p T, (n i : ℂ) * τ i =
          (n p : ℂ) * τ p + (a + ∑ i ∈ T, (n i : ℂ) * τ i) := by
        rw [Finset.sum_insert hpT]
        ring
      rw [hsum, ← addTranslationMeroEquiv_add]
      exact cosetTotalPacket_span_translate_mem τ hτ A p (n p) ih

theorem cosetTotalPacket_eq_union (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (A : Set ℂ) :
    cosetTotalPacket τ hτ A =
      cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card} ∪
        cosetFacePacketUnion τ hτ A {J : Finset ι | (Jᶜ).card < 2} := by
  ext y
  simp only [cosetTotalPacket, cosetFacePacketUnion, Set.mem_iUnion, Set.mem_union,
    Set.mem_setOf_eq, exists_prop]
  constructor
  · rintro ⟨J, hyJ⟩
    by_cases h2 : 2 ≤ (Jᶜ).card
    · exact Or.inl ⟨J, h2, hyJ⟩
    · refine Or.inr ⟨J, ?_, hyJ⟩
      omega
  · rintro (⟨J, -, hyJ⟩ | ⟨J, -, hyJ⟩) <;> exact ⟨J, hyJ⟩

set_option maxHeartbeats 1000000 in
/-- Every element of the span of the labelled boundary packets is differentially algebraic. -/
theorem differentialAlgebraicOver_mem_span_cosetBoundaryPacket
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι) (A : Set ℂ)
    {x : meroField (Set.univ : Set ℂ)}
    (hx : x ∈ Submodule.span ℂ
      (cosetFacePacketUnion τ hτ A {J : Finset ι | (Jᶜ).card < 2})) :
    DifferentialAlgebraicOver ℂ x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨J, hJ, hyJ⟩ := Set.mem_iUnion₂.mp hy
      exact differentialAlgebraicOver_cosetFacePacket_of_compl_lt_two τ hτ hQ hι A J hJ hyJ
  | zero => exact differentialAlgebraicOver_zero
  | add y z _ _ ihy ihz => exact differentialAlgebraicOver_add ihy ihz
  | smul c y _ ih =>
      rw [Algebra.smul_def]
      exact differentialAlgebraicOver_mul (differentialAlgebraicOver_algebraMap c) ih

set_option maxHeartbeats 1500000 in
/-- **Universal cyclic carrier reduction, arbitrary complex translation.**  Modulo a
differentially algebraic error, every labelled translate of the top primitive is a finite
`ℂ`-linear combination of the jointly independent labelled deep face-packet coordinates. -/
theorem cosetTranslate_eq_deepSpan_add_differentialAlgebraic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {A : Set ℂ} {a : ℂ} (ha : a ∈ A) (n : ι → ℤ) (T : Finset ι) :
    ∃ y d : meroField (Set.univ : Set ℂ),
      y ∈ Submodule.span ℂ
          (cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
        DifferentialAlgebraicOver ℂ d ∧
        addTranslationMeroEquiv (a + ∑ i ∈ T, (n i : ℂ) * τ i)
            (multipleEllipticGammaLogDerivMero τ hτ) = y + d := by
  classical
  have hmem := cosetTranslate_mem_span τ hτ ha n T
  rw [cosetTotalPacket_eq_union, Submodule.span_union] at hmem
  obtain ⟨y, hy, d, hd, hsum⟩ := Submodule.mem_sup.mp hmem
  exact ⟨y, d, hy,
    differentialAlgebraicOver_mem_span_cosetBoundaryPacket τ hτ hQ hι A hd, hsum.symm⟩

/-- **Arbitrary-complex-shift form.**  For a transversal label set every complex translate of the
top primitive reduces, modulo a differentially algebraic error, to the labelled deep span. -/
theorem arbitraryTranslate_eq_deepSpan_add_differentialAlgebraic
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    {A : Set ℂ} (hcover : ∀ z : ℂ, ∃ a ∈ A, z - a ∈ fullPeriodLattice τ) (z : ℂ) :
    ∃ y d : meroField (Set.univ : Set ℂ),
      y ∈ Submodule.span ℂ
          (cosetFacePacketUnion τ hτ A {J : Finset ι | 2 ≤ (Jᶜ).card}) ∧
        DifferentialAlgebraicOver ℂ d ∧
        addTranslationMeroEquiv z (multipleEllipticGammaLogDerivMero τ hτ) = y + d := by
  classical
  obtain ⟨a, ha, hlat⟩ := hcover z
  obtain ⟨m, n, hmn⟩ := hlat
  obtain ⟨y, d, hy, hd, heq⟩ :=
    cosetTranslate_eq_deepSpan_add_differentialAlgebraic τ hτ hQ hι ha n Finset.univ
  refine ⟨y, d, hy, hd, ?_⟩
  have hint : addTranslationMeroEquiv ((m : ℤ) : ℂ) (multipleEllipticGammaLogDerivMero τ hτ) =
      multipleEllipticGammaLogDerivMero τ hτ := by
    rw [← multipleEllipticGammaLogDerivFaceMero_empty τ hτ]
    exact addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero τ hτ ∅ m
  have hz : z = (a + ∑ i, (n i : ℂ) * τ i) + (m : ℂ) := by
    have hd' : z - a = (m : ℂ) + ∑ i, (n i : ℂ) * τ i := hmn
    linear_combination hd'
  rw [hz, ← addTranslationMeroEquiv_add, hint]
  exact heq

end

end GaloisForLFunctions
