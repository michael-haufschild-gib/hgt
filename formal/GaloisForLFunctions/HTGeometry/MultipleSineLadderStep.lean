import GaloisForLFunctions.HTGeometry.ReflectionStableDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.BarnesSubframeLadderStep
import GaloisForLFunctions.HTGeometry.MultipleSineReflectedRecurrence
import GaloisForLFunctions.HTGeometry.BankOddExponentDichotomy

/-!
# Equation `(2)` for the reflected Barnes source

Everything the multiple-sine difference equation needs is proved:

* the Barnes ladder `(T_k - 1) Psi_S + Psi_{S∖k}` is differentially algebraic;
* the reflection is an automorphism of the meromorphic differential field, anti-commuting with the
  derivation;
* translating a reflection is a reflection, so the shift difference of a reflected source is the
  shift difference of the source plus its reflected copy at the *deleted* frame's reflection point;
* the differentially algebraic sector is stable under the reflection.

This file assembles them.  Writing `L_S` for the reflected Barnes source of a frame `S`, with its
own reflection point `c_S = ∑_{i ∈ S} omega_i` and parity sign `eps_S = (-1)^{|S|+1}`,

```text
(T_k - 1) L_S + L_{S∖k}   is differentially algebraic,
```

for every direction `k` of a frame with at least two directions.  That is equation `(2)` of the
card, modulo the differentially algebraic sector, for the constructed multiple-sine source.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra

/-! ### The transport with an explicit defect -/

/-- **The transport identity carrying a defect.**  A ladder relation with remainder `d` becomes a
ladder relation for the reflected sources whose remainder is the reflected combination of `d`. -/
theorem meroShiftDiff_reflectedSource_of_defect (ε : ℤ) (c a : ℂ)
    (x y d : meroField (Set.univ : Set ℂ))
    (hladder : addTranslationMeroEquiv a x - x = -y + d) :
    addTranslationMeroEquiv a (meroReflectedSource ε c x) - meroReflectedSource ε c x =
      -(meroReflectedSource (-ε) (c - a) y) +
        (d + (ε : meroField (Set.univ : Set ℂ)) *
          complexReflectionMeroEquiv (c - a) d) := by
  rw [meroShiftDiff_reflectedSource, hladder]
  have hR : complexReflectionMeroEquiv (c - a) (-y + d)
      = -(complexReflectionMeroEquiv (c - a) y) +
        complexReflectionMeroEquiv (c - a) d := by
    rw [RingEquiv.map_add, RingEquiv.map_neg]
  rw [hR]
  unfold meroReflectedSource
  have hneg : ((-ε : ℤ) : meroField (Set.univ : Set ℂ))
      = -((ε : ℤ) : meroField (Set.univ : Set ℂ)) := by
    rw [Int.cast_neg]
  rw [hneg]
  ring

/-! ### The parity sign as an integer -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Integer parity sign of a subframe: `eps_S = (-1)^{|S|+1}`. -/
def frameSignZ (S : Finset ι) : ℤ := (-1) ^ (S.card + 1)

omit [Fintype ι] in
/-- **Deleting a direction flips the parity sign.** -/
theorem frameSignZ_erase {S : Finset ι} {k : ι} (hk : k ∈ S) :
    frameSignZ (S.erase k) = -frameSignZ S := by
  unfold frameSignZ
  rw [Finset.card_erase_of_mem hk]
  have hcard : 1 ≤ S.card := Finset.card_pos.2 ⟨k, hk⟩
  rw [show S.card + 1 = (S.card - 1 + 1) + 1 by omega, pow_succ]
  ring

omit [Fintype ι] in
theorem natCast_frameSignZ_mul_da {S : Finset ι}
    {z : meroField (Set.univ : Set ℂ)}
    (hz : DifferentialAlgebraicOver (RatFunc ℂ) z) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      ((frameSignZ S : meroField (Set.univ : Set ℂ)) * z) := by
  have hcast : ((frameSignZ S : ℤ) : meroField (Set.univ : Set ℂ))
      = (-1 : meroField (Set.univ : Set ℂ)) ^ (S.card + 1) := by
    unfold frameSignZ
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hcast]
  exact differentialAlgebraicOver_neg_one_pow_mul hz

/-! ### The reflected Barnes source of a frame -/

/-- The reflected Barnes source of a subframe: the multiple-sine source of that frame. -/
def multipleSineSourceMero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (S : Finset ι)
    [Nonempty {i : ι // i ∈ S}] : meroField (Set.univ : Set ℂ) :=
  meroReflectedSource (frameSignZ S) (frameReflectionPoint ω S)
    (barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S))

/-- **Equation `(2)` for the reflected Barnes source.**  The multiple-sine difference equation holds
modulo the differentially algebraic sector, for every direction of a frame with at least two
directions. -/
theorem differentialAlgebraicOver_multipleSine_ladder_step
    (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (S : Finset ι) (k : ι) (hk : k ∈ S)
    (h2 : 2 ≤ S.card)
    [Nonempty {i : ι // i ∈ S}] [Nonempty {i : ι // i ∈ S.erase k}] :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (addTranslationMeroEquiv (ω k) (multipleSineSourceMero ω hω S)
          - multipleSineSourceMero ω hω S
        + multipleSineSourceMero ω hω (S.erase k)) := by
  classical
  set Psi := barnesSourceLogDerivMero (subframe ω S) (subframe_im_pos hω S) with hPsi
  set Phi := barnesSourceLogDerivMero (subframe ω (S.erase k))
    (subframe_im_pos hω (S.erase k)) with hPhi
  set d := addTranslationMeroEquiv (ω k) Psi - Psi + Phi with hd
  have hdDA : DifferentialAlgebraicOver (RatFunc ℂ) d :=
    differentialAlgebraicOver_subframe_ladder_step ω hω S k hk h2
  have hladder : addTranslationMeroEquiv (ω k) Psi - Psi = -Phi + d := by
    rw [hd]
    abel
  have htrans := meroShiftDiff_reflectedSource_of_defect (frameSignZ S)
    (frameReflectionPoint ω S) (ω k) Psi Phi d hladder
  have hpoint : frameReflectionPoint ω S - ω k = frameReflectionPoint ω (S.erase k) :=
    frameReflectionPoint_erase ω hk
  have hsign : -frameSignZ S = frameSignZ (S.erase k) := (frameSignZ_erase hk).symm
  rw [hpoint, hsign] at htrans
  have hgoal : addTranslationMeroEquiv (ω k) (multipleSineSourceMero ω hω S)
        - multipleSineSourceMero ω hω S
      + multipleSineSourceMero ω hω (S.erase k)
      = d + (frameSignZ S : meroField (Set.univ : Set ℂ)) *
          complexReflectionMeroEquiv (frameReflectionPoint ω (S.erase k)) d := by
    unfold multipleSineSourceMero
    rw [← hPsi, ← hPhi, htrans]
    abel
  rw [hgoal]
  exact differentialAlgebraicOver_add hdDA
    (natCast_frameSignZ_mul_da
      (differentialAlgebraicOver_complexReflectionMeroEquiv _ hdDA))

end

end GaloisForLFunctions.HTGeometry
