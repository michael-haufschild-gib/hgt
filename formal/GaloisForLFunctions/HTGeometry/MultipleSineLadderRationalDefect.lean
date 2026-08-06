import GaloisForLFunctions.HTGeometry.BarnesLadderDefectPolePart
import GaloisForLFunctions.HTGeometry.MultipleSineLadderStep

/-!
# The multiple-sine ladder defect is an explicit rational function

Equation `(2)` was proved modulo the differentially algebraic sector.  The defect it hides is in
fact rational: the Barnes ladder defect is `N_k/(X + ω_k)`, and the reflected transport adds its
reflection at the deleted frame's reflection point.  Hence

```text
(σ_{ω_k} - 1) L_S + L_{S∖k} = R_k + ε_S · R_k(c_{S∖k} - ·),
```

with `R_k` the rational ladder defect and `ε_S` the frame parity.  Everything on the right is a
rational function of the argument, embedded in the meromorphic field.

That exact form is what the multiple-sine normalization consumes: the pole parts of the two
summands sit at `-ω_k` and at `c_{S∖k} + ω_k` with opposite residues, hence along one period orbit,
so a rational correction turns the ladder into the exact difference equation with cotangent
increments.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The embedding of the coordinate field into the meromorphic field. -/
abbrev ratMero : RatFunc ℂ →+* meroField (Set.univ : Set ℂ) :=
  ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ

/-- The rational ladder defect of a subframe in one of its directions. -/
def subframeLadderRat (ω : ι → ℂ) (S : Finset ι) (k : ι) (hk : k ∈ S) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (barnesLadderNumerator (subframe ω S) ⟨k, hk⟩) /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X + Polynomial.C (ω k))

omit [Fintype ι] in
/-- **The subframe ladder defect, exactly.** -/
theorem subframe_ladder_defect_eq (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (k : ι) (hk : k ∈ S) (h2 : 2 ≤ S.card)
    [Nonempty {i : ι // i ∈ S}] [Nonempty {i : ι // i ∈ S.erase k}] :
    addTranslationMeroEquiv (ω k)
          (barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S))
        - barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S)
      + barnesSourceLogDerivMero (subframe ω (S.erase k))
          (subframe_im_pos hω (S.erase k))
      = ratMero (subframeLadderRat ω S k hk) := by
  classical
  haveI hne : Nonempty {i' : {i : ι // i ∈ S} // i' ≠ ⟨k, hk⟩} := by
    have hcard : 1 < Fintype.card {i : ι // i ∈ S} := by
      rw [Fintype.card_coe]
      omega
    obtain ⟨i', hi'⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨k, hk⟩
    exact ⟨⟨i', hi'⟩⟩
  have hstep := barnesSource_ladder_defect_eq (subframe ω S)
    (subframe_im_pos hω S) ⟨k, hk⟩
  have hlower : barnesSourceLogDerivMero (deletedFrame (subframe ω S) ⟨k, hk⟩)
        (deletedFrame_im_pos (subframe_im_pos hω S) ⟨k, hk⟩)
      = barnesSourceLogDerivMero (subframe ω (S.erase k)) (subframe_im_pos hω (S.erase k)) := by
    have hframe := deletedFrame_subframe ω S k hk
    have := barnesSourceLogDerivMero_comp_equiv (eraseSubtypeEquiv S k hk)
      (subframe ω (S.erase k)) (subframe_im_pos hω (S.erase k))
      (fun i' => subframe_im_pos hω (S.erase k) _)
    rw [← this]
    exact barnesSourceLogDerivMero_congr hframe _ _
  rw [hlower] at hstep
  have hω' : subframe ω S ⟨k, hk⟩ = ω k := rfl
  rw [hω'] at hstep
  rw [hstep, subframeLadderRat]

omit [Fintype ι] in
/-- **Equation `(2)` with its exact rational defect.** -/
theorem multipleSine_ladder_defect_eq (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (k : ι) (hk : k ∈ S) (h2 : 2 ≤ S.card)
    [Nonempty {i : ι // i ∈ S}] [Nonempty {i : ι // i ∈ S.erase k}] :
    addTranslationMeroEquiv (ω k) (multipleSineSourceMero ω hω S)
        - multipleSineSourceMero ω hω S
      + multipleSineSourceMero ω hω (S.erase k)
      = ratMero (subframeLadderRat ω S k hk
          + (frameSignZ S : RatFunc ℂ) *
            ratReflectBy (frameReflectionPoint ω (S.erase k)) (subframeLadderRat ω S k hk)) := by
  classical
  set Psi := barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S) with hPsi
  set Phi := barnesSourceLogDerivMero (subframe ω (S.erase k))
    (subframe_im_pos hω (S.erase k)) with hPhi
  set d : meroField (Set.univ : Set ℂ) := ratMero (subframeLadderRat ω S k hk) with hd
  have hladder : addTranslationMeroEquiv (ω k) Psi - Psi = -Phi + d := by
    have hex := subframe_ladder_defect_eq ω hω S k hk h2
    rw [← hPsi, ← hPhi, ← hd] at hex
    linear_combination hex
  have htrans := meroShiftDiff_reflectedSource_of_defect (frameSignZ S)
    (frameReflectionPoint ω S) (ω k) Psi Phi d hladder
  have hpoint : frameReflectionPoint ω S - ω k = frameReflectionPoint ω (S.erase k) :=
    frameReflectionPoint_erase ω hk
  have hsign : -frameSignZ S = frameSignZ (S.erase k) := (frameSignZ_erase hk).symm
  rw [hpoint, hsign] at htrans
  have hreflect : complexReflectionMeroEquiv (frameReflectionPoint ω (S.erase k)) d
      = ratMero (ratReflectBy (frameReflectionPoint ω (S.erase k))
        (subframeLadderRat ω S k hk)) := by
    rw [hd]
    exact complexReflectionMeroEquiv_ratfuncToMero _ _
  have hcast : ((frameSignZ S : ℤ) : meroField (Set.univ : Set ℂ))
      = ratMero ((frameSignZ S : ℤ) : RatFunc ℂ) := by
    rw [map_intCast]
  have hgoal : addTranslationMeroEquiv (ω k) (multipleSineSourceMero ω hω S)
        - multipleSineSourceMero ω hω S
      + multipleSineSourceMero ω hω (S.erase k)
      = d + ((frameSignZ S : ℤ) : meroField (Set.univ : Set ℂ)) *
          complexReflectionMeroEquiv (frameReflectionPoint ω (S.erase k)) d := by
    unfold multipleSineSourceMero
    rw [← hPsi, ← hPhi, htrans]
    abel
  rw [hgoal, hreflect, hcast, map_add, map_mul]

end

end GaloisForLFunctions.HTGeometry
