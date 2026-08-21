import GaloisForLFunctions.HTGeometry.AllDepthCompleteness
import GaloisForLFunctions.HTGeometry.TripticMultiplicativeKernel

/-!
# Depth-three face-signature completeness

At depth three the common terminal residue no longer classifies differential algebraicity, but the
three *unpushed* codimension-one residues do.  For a `1`-periodic meromorphic germ whose triple
mixed difference is constant, the three codimension-one differences

```text
Δ_{τ₀} F,   Δ_{τ₁} F,   Δ_{τ₂} F
```

each lie in the depth-two class for the two remaining parameters, and the germ is differentially
algebraic exactly when every orbital residue of every one of them vanishes.

This is the `d = 3` case of `differentialAlgebraicOver_iff_pairFace_univ`: the pair-face witness at
the pair `{i, j}` inside a three-element parameter family is the codimension-one difference in the
remaining direction.

The multiplicative form records the same statement for a source `Y` whose logarithmic derivative
lies in the class: the three face charges are the integral divisors of the multiplicative
coboundaries `Y(z + τ_k)/Y(z)` read along the two surviving orbit directions.
-/

open Filter Set Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

/-! ## The pair-face witness at depth three -/

/-- In a three-element parameter family the complement of a pair is the remaining singleton. -/
theorem fin3_univ_sdiff_pair :
    ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      (Finset.univ : Finset (Fin 3)) \ {i, j} = {k} := by decide

/-- **The depth-three pair-face witness is the codimension-one difference in the third
direction.** -/
theorem pairFaceWitnessFun_fin3 (τ : Fin 3 → ℂ) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (f : ℂ → ℂ) :
    pairFaceWitnessFun τ (Finset.univ : Finset (Fin 3)) i j f = shiftDiffFun (τ k) f := by
  rw [pairFaceWitnessFun, fin3_univ_sdiff_pair i j k hij hik hjk, diffCube_singleton]

/-! ## The depth-three face signature -/

/-- **The depth-three face signature vanishes.**  Each codimension-one difference `Δ_{τ k} F` has
vanishing orbital residue at every order and along both surviving directions. -/
def DepthThreeFaceVanishes (τ : Fin 3 → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      additiveOrbitalDivisorAt (shiftDiffFun (τ k) f) (τ i) p ℓ = 0

set_option synthInstance.maxHeartbeats 800000 in
/-- **Depth-three face-signature completeness.**  A `1`-periodic meromorphic germ with constant
triple mixed difference in three integrally independent directions is differentially algebraic
exactly when its depth-three face signature vanishes. -/
theorem differentialAlgebraicOver_iff_depthThreeFaceVanishes
    (τ : Fin 3 → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (hper : PeriodicOneGerm f)
    (hmixed : MixedConstGermSet τ (Finset.univ : Finset (Fin 3)) f Cst) :
    DifferentialAlgebraicOver ℂ x ↔ DepthThreeFaceVanishes τ f := by
  rw [differentialAlgebraicOver_iff_pairFace_univ τ hτ hQ (by simp) hx hper hmixed]
  constructor
  · intro h i j k hij hik hjk p ℓ hℓ
    have := h i j hij p ℓ hℓ
    rwa [pairFaceWitnessFun_fin3 τ hij hik hjk f] at this
  · intro h i j hij p ℓ hℓ
    obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      revert hij; revert i j; decide
    have := h i j k hij hik hjk p ℓ hℓ
    rwa [pairFaceWitnessFun_fin3 τ hij hik hjk f]

/-! ## Multiplicative form

A source `Y` whose logarithmic derivative lies in the depth-three class carries three integral
face charges, one for each multiplicative coboundary `Y(· + τ k)/Y`, read along each of the two
surviving orbit directions.  Because a logarithmic derivative has only simple poles, the whole
face signature of `logDeriv Y` is carried in order `-1`, where it is exactly that integer charge.
-/

variable {Y : ℂ → ℂ}

/-- The integral face charge of the multiplicative coboundary `Y(· + t)/Y` along the `s`-orbit
through `p`. -/
def multFaceCharge (Y : ℂ → ℂ) (t s p : ℂ) : ℤ :=
  ∑ᶠ m : ℤ, (shiftOrder Y t (p + (m : ℂ) * s + s) - shiftOrder Y t (p + (m : ℂ) * s))

theorem meromorphicOn_shiftDiffFun_logDeriv (hY : MeromorphicOn Y Set.univ) (t : ℂ) :
    MeromorphicOn (shiftDiffFun t (logDeriv Y)) Set.univ := by
  have hlog : MeromorphicOn (logDeriv Y) Set.univ := fun z _ =>
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  intro z _
  exact (meromorphicAt_comp_add.mpr (hlog (z + t) (Set.mem_univ _))).sub
    (hlog z (Set.mem_univ z))

/-- The residue of a double logarithmic shift difference is the difference of shift orders. -/
theorem laurentCoeff_doubleShiftDiff_logDeriv (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (t s w : ℂ) :
    laurentCoeff (fun z => shiftDiffFun t (logDeriv Y) (z + s)
        - shiftDiffFun t (logDeriv Y) z) w (-1)
      = ((shiftOrder Y t (w + s) - shiftOrder Y t w : ℤ) : ℂ) := by
  rw [laurentCoeff_shiftDiff (meromorphicOn_shiftDiffFun_logDeriv hY t) s w (-1)]
  have h₁ : laurentCoeff (shiftDiffFun t (logDeriv Y)) (w + s) (-1)
      = (shiftOrder Y t (w + s) : ℂ) := laurentCoeff_shiftDiff_logDeriv hY hfin t (w + s)
  have h₂ : laurentCoeff (shiftDiffFun t (logDeriv Y)) w (-1)
      = (shiftOrder Y t w : ℂ) := laurentCoeff_shiftDiff_logDeriv hY hfin t w
  rw [h₁, h₂]
  push_cast
  ring

/-- Below the residue order a double logarithmic shift difference has no Laurent coefficient. -/
theorem laurentCoeff_doubleShiftDiff_logDeriv_eq_zero (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (t s w : ℂ) {ℓ : ℤ} (hℓ : ℓ ≤ -2) :
    laurentCoeff (fun z => shiftDiffFun t (logDeriv Y) (z + s)
        - shiftDiffFun t (logDeriv Y) z) w ℓ = 0 := by
  have hvan : ∀ a : ℂ, laurentCoeff (logDeriv Y) a ℓ = 0 := by
    intro a
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfin a)
    exact laurentCoeff_logDeriv_eq_zero_of_le (hY a (Set.mem_univ a)) hn.symm hℓ
  have hlog : MeromorphicOn (logDeriv Y) Set.univ := fun z _ =>
    ((hY z (Set.mem_univ z)).deriv).div (hY z (Set.mem_univ z))
  rw [laurentCoeff_shiftDiff (meromorphicOn_shiftDiffFun_logDeriv hY t) s w ℓ]
  have h₁ : laurentCoeff (shiftDiffFun t (logDeriv Y)) (w + s) ℓ = 0 := by
    rw [show (shiftDiffFun t (logDeriv Y)) = fun z => logDeriv Y (z + t) - logDeriv Y z from rfl,
      laurentCoeff_shiftDiff hlog t (w + s) ℓ, hvan, hvan, sub_zero]
  have h₂ : laurentCoeff (shiftDiffFun t (logDeriv Y)) w ℓ = 0 := by
    rw [show (shiftDiffFun t (logDeriv Y)) = fun z => logDeriv Y (z + t) - logDeriv Y z from rfl,
      laurentCoeff_shiftDiff hlog t w ℓ, hvan, hvan, sub_zero]
  rw [h₁, h₂, sub_zero]

/-- **The face signature of a logarithmic derivative is its integral face charge.** -/
theorem additiveOrbitalDivisorAt_shiftDiffFun_logDeriv (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (t s p : ℂ) :
    additiveOrbitalDivisorAt (shiftDiffFun t (logDeriv Y)) s p (-1)
      = ((multFaceCharge Y t s p : ℤ) : ℂ) := by
  rw [additiveOrbitalDivisorAt]
  have hterm : ∀ m : ℤ,
      laurentCoeff (fun z => shiftDiffFun t (logDeriv Y) (z + s)
          - shiftDiffFun t (logDeriv Y) z) (p + (m : ℂ) * s) (-1)
        = ((shiftOrder Y t (p + (m : ℂ) * s + s) - shiftOrder Y t (p + (m : ℂ) * s) : ℤ) : ℂ) :=
    fun m => laurentCoeff_doubleShiftDiff_logDeriv hY hfin t s _
  rw [finsum_congr hterm, ← intCast_finsum]
  rfl

/-- **The depth-three face signature of a logarithmic derivative vanishes exactly when all three
multiplicative face charges vanish.** -/
theorem depthThreeFaceVanishes_logDeriv_iff (hY : MeromorphicOn Y Set.univ)
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (τ : Fin 3 → ℂ) :
    DepthThreeFaceVanishes τ (logDeriv Y) ↔
      ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ p : ℂ, multFaceCharge Y (τ k) (τ i) p = 0 := by
  constructor
  · intro h i j k hij hik hjk p
    have hz := h i j k hij hik hjk p (-1) (by norm_num)
    rw [additiveOrbitalDivisorAt_shiftDiffFun_logDeriv hY hfin] at hz
    exact_mod_cast hz
  · intro h i j k hij hik hjk p ℓ hℓ
    rcases lt_or_eq_of_le (by omega : ℓ ≤ -1) with hlt | heq
    · rw [additiveOrbitalDivisorAt]
      have hzero : ∀ m : ℤ,
          laurentCoeff (fun z => shiftDiffFun (τ k) (logDeriv Y) (z + τ i)
            - shiftDiffFun (τ k) (logDeriv Y) z) (p + (m : ℂ) * τ i) ℓ = 0 :=
        fun m => laurentCoeff_doubleShiftDiff_logDeriv_eq_zero hY hfin _ _ _ (by omega)
      rw [finsum_congr hzero, finsum_zero]
    · subst heq
      rw [additiveOrbitalDivisorAt_shiftDiffFun_logDeriv hY hfin, h i j k hij hik hjk p]
      norm_num

theorem periodicOneGerm_logDeriv (hYper : ∀ z : ℂ, Y (z + 1) = Y z) :
    PeriodicOneGerm (logDeriv Y) := by
  refine periodicOneGerm_of_forall fun z => ?_
  have hfun : (fun w : ℂ => Y (w + 1)) = Y := funext hYper
  have hd : deriv Y (z + 1) = deriv Y z := by
    have hcomp := deriv_comp_add_const (f := Y) (a := (1 : ℂ)) z
    rw [hfun] at hcomp
    exact hcomp.symm
  rw [logDeriv_apply, logDeriv_apply, hd, hYper z]

set_option synthInstance.maxHeartbeats 800000 in
/-- **Depth-three face-signature completeness, multiplicative form.**  A `1`-periodic source whose
logarithmic derivative has constant triple mixed difference has a differentially algebraic
logarithmic derivative exactly when all three multiplicative face charges vanish. -/
theorem differentialAlgebraicOver_logDeriv_iff_multFaceCharge
    (τ : Fin 3 → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hY : MeromorphicOn Y Set.univ) (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤)
    (hYper : ∀ z : ℂ, Y (z + 1) = Y z)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} (hx : RealizesMero x (logDeriv Y))
    (hmixed : MixedConstGermSet τ (Finset.univ : Finset (Fin 3)) (logDeriv Y) Cst) :
    DifferentialAlgebraicOver ℂ x ↔
      ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ p : ℂ, multFaceCharge Y (τ k) (τ i) p = 0 := by
  rw [differentialAlgebraicOver_iff_depthThreeFaceVanishes τ hτ hQ hx
    (periodicOneGerm_logDeriv hYper) hmixed]
  exact depthThreeFaceVanishes_logDeriv_iff hY hfin τ

end

end GaloisForLFunctions

