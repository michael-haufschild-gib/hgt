import GaloisForLFunctions.HTGeometry.AntiInvariantEvaluationMinor
import GaloisForLFunctions.RHTower.XiWeilSameFiberAtomIsotropy

/-!
# Multiplicity-exact Xi Weil negative-index conservation

The negative index of critical-line reflection is exactly the supply of free multiplicity-copy
orbits.  A finite family of disjoint free orbits gives a negative block through explicit odd
coordinate atoms.  Conversely, every strictly negative finite Hilbert block has independent odd
parts; a nonsingular evaluation minor then extracts the same number of pairwise disjoint free
copy-orbits.  No zero-location hypothesis is used.

This copy-level theorem retains analytic zero multiplicity.  Folding only spectral locations is a
coarser lower bound and must not be mistaken for the exact Hilbert index.
-/

namespace RHTower

open scoped BigOperators ComplexConjugate
open Complex Matrix

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Reflection-odd part of a multiplicity-exact Xi Hilbert vector. -/
def xiWeilAntiPart (v : XiWeilCarrier) : XiWeilCarrier :=
  v - xiWeilLineConjLinearIsometry v

/-- One coordinate readout on the multiplicity-exact Xi Hilbert carrier. -/
def xiWeilCoordinateLinear (q : XiZeroCopy) : XiWeilCarrier →ₗ[ℂ] ℂ where
  toFun v := v q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem xiWeilCoordinateLinear_apply (q : XiZeroCopy) (v : XiWeilCarrier) :
    xiWeilCoordinateLinear q v = v q := rfl

/-- Reflected Hilbert Gram in the row/column convention used by source packets. -/
def xiWeilHilbertGram {k : ℕ} (v : Fin k → XiWeilCarrier) :
    Matrix (Fin k) (Fin k) ℂ := fun j l =>
  inner ℂ (xiWeilLineConjLinearIsometry (v l)) (v j)

/-- Matrix energy equals the Weil quadratic of the conjugated-coefficient synthesis. -/
theorem xiWeilHilbertGram_quadratic
    {k : ℕ} (v : Fin k → XiWeilCarrier) (x : Fin k → ℂ) :
    star x ⬝ᵥ (xiWeilHilbertGram v).mulVec x =
      inner ℂ
        (xiWeilLineConjLinearIsometry (∑ j, star (x j) • v j))
        (∑ j, star (x j) • v j) := by
  let a : XiWeilCarrier := ∑ j, star (x j) • v j
  have hmul : ∀ j, (xiWeilHilbertGram v).mulVec x j =
      inner ℂ (xiWeilLineConjLinearIsometry a) (v j) := by
    intro j
    simp only [xiWeilHilbertGram, Matrix.mulVec, dotProduct]
    dsimp only [a]
    rw [map_sum, sum_inner]
    simp_rw [map_smul, inner_smul_left]
    apply Finset.sum_congr rfl
    intro l _
    rw [starRingEnd_apply, star_star]
    ring
  rw [dotProduct]
  simp_rw [hmul]
  dsimp only [a]
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_right]
  rfl

/-- Negative definiteness of the reflected Gram is exactly strict negativity on every synthesized
coefficient direction. -/
theorem quadratic_neg_of_xiWeilHilbertGram_negDef
    {k : ℕ} (v : Fin k → XiWeilCarrier)
    (hneg : ∀ x : Fin k → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (xiWeilHilbertGram v).mulVec x).re < 0) :
    ∀ c : Fin k → ℂ, c ≠ 0 →
      xiWeilHilbertQuadratic (∑ j, c j • v j) < 0 := by
  intro c hc
  have hstar : star c ≠ 0 := by
    intro hs
    apply hc
    have hs' := congrArg star hs
    simpa using hs'
  have hn := hneg (star c) hstar
  rw [xiWeilHilbertGram_quadratic] at hn
  have hsum : (∑ j, star ((star c) j) • v j) = ∑ j, c j • v j := by
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [hsum] at hn
  simpa [xiWeilHilbertQuadratic] using hn

@[simp]
theorem xiWeilAntiPart_lineConj_apply (v : XiWeilCarrier) (q : XiZeroCopy) :
    xiWeilAntiPart v (xiZeroCopyLineConjEquiv q) = -xiWeilAntiPart v q := by
  simp [xiWeilAntiPart, xiWeilLineConjLinearIsometry_apply,
    xiWeilLineConjLp_apply,
    DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply]

/-- Pairwise disjoint free copy-orbits produce a strictly negative block of the same dimension. -/
theorem xiWeilHilbertGram_freeOrbitPacket_negDef
    {k : ℕ} (e : Fin k → XiZeroCopy) (he : Function.Injective e)
    (hsep : ∀ r s, xiZeroCopyLineConjEquiv (e r) ≠ e s)
    (x : Fin k → ℂ) (hx : x ≠ 0) :
    (star x ⬝ᵥ
      (xiWeilHilbertGram (fun j =>
        xiWeilAntiPart (xiWeilCoordinateAtom (e j) 1))).mulVec x).re < 0 := by
  let atom : Fin k → XiWeilCarrier := fun j => xiWeilCoordinateAtom (e j) 1
  let w : XiWeilCarrier := ∑ j, star (x j) • atom j
  let a : XiWeilCarrier := ∑ j, star (x j) • xiWeilAntiPart (atom j)
  have ha : a = xiWeilAntiPart w := by
    dsimp only [a, w]
    rw [xiWeilAntiPart, map_sum]
    simp_rw [map_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [xiWeilAntiPart, smul_sub]
  have hstar : star x ≠ 0 := by
    intro hs
    apply hx
    have hs' := congrArg star hs
    simpa using hs'
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hstar
  have hcoord : xiWeilCoordinateLinear (e j0) a = star (x j0) := by
    dsimp only [a]
    rw [map_sum]
    simp_rw [map_smul, xiWeilCoordinateLinear_apply]
    rw [Finset.sum_eq_single j0]
    · simp [atom, xiWeilAntiPart,
        xiWeilCoordinateAtom_apply, hsep j0 j0]
    · intro j _ hj
      have hej : e j0 ≠ e j := fun h => hj (he h.symm)
      simp [atom, xiWeilAntiPart,
        xiWeilCoordinateAtom_apply, hej, hsep j0 j]
    · simp
  have hane : a ≠ 0 := by
    intro haz
    have hz := congrArg (xiWeilCoordinateLinear (e j0)) haz
    rw [hcoord] at hz
    simp only [map_zero] at hz
    exact hj0 hz
  have hanti : xiWeilLineConjLinearIsometry a = -a := by
    rw [ha, xiWeilAntiPart, map_sub,
      xiWeilLineConjLinearIsometry_involutive]
    abel
  rw [xiWeilHilbertGram_quadratic]
  change (inner ℂ (xiWeilLineConjLinearIsometry a) a).re < 0
  have hre : (inner ℂ a a).re = ‖a‖ ^ 2 := by
    exact_mod_cast congrArg Complex.re
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) a)
  rw [hanti, inner_neg_left, Complex.neg_re, hre]
  have hnorm : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hane)
  exact neg_neg_of_pos hnorm

/-- Strict negativity on every nonzero combination makes the reflection-odd parts independent. -/
theorem linearIndependent_xiWeilAntiPart_of_quadratic_neg
    {k : ℕ} (v : Fin k → XiWeilCarrier)
    (hneg : ∀ c : Fin k → ℂ, c ≠ 0 →
      xiWeilHilbertQuadratic (∑ j, c j • v j) < 0) :
    LinearIndependent ℂ (fun j => xiWeilAntiPart (v j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hci
  have hcne : c ≠ 0 := by
    intro hzero
    exact hci (congrFun hzero i)
  let a : XiWeilCarrier := ∑ j, c j • v j
  have ha : a - xiWeilLineConjLinearIsometry a = 0 := by
    dsimp only [a]
    rw [map_sum]
    simp_rw [map_smul]
    rw [← Finset.sum_sub_distrib]
    simpa [xiWeilAntiPart, smul_sub] using hc
  have hfix : xiWeilLineConjLinearIsometry a = a :=
    (sub_eq_zero.mp ha).symm
  have hn := hneg c hcne
  change xiWeilHilbertQuadratic a < 0 at hn
  rw [xiWeilHilbertQuadratic, hfix, inner_self_eq_norm_sq_to_K] at hn
  have hnonneg : 0 ≤ ((↑‖a‖ ^ 2 : ℂ)).re := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_nonneg ‖a‖
  exact (not_lt_of_ge hnonneg) hn

/-- Every `k`-dimensional strictly negative Xi Weil block exposes `k` pairwise disjoint free
multiplicity-copy reflection orbits. -/
theorem exists_xiZeroCopy_freeOrbitPacket_of_quadratic_neg
    {k : ℕ} (v : Fin k → XiWeilCarrier)
    (hneg : ∀ c : Fin k → ℂ, c ≠ 0 →
      xiWeilHilbertQuadratic (∑ j, c j • v j) < 0) :
    ∃ (e : Fin k → XiZeroCopy) (P : Matrix (Fin k) (Fin k) ℂ),
      Function.Injective e ∧
      (∀ r s, xiZeroCopyLineConjEquiv (e r) ≠ e s) ∧
      IsUnit P.det ∧
      ∀ r s, P r s = xiWeilAntiPart (v s) (e r) := by
  have hLI : LinearIndependent ℂ
      (fun j q => xiWeilAntiPart (v j) q) := by
    let coeLinear : XiWeilCarrier →ₗ[ℂ] (XiZeroCopy → ℂ) :=
      { toFun := fun (w : XiWeilCarrier) (q : XiZeroCopy) => w q
        map_add' := by
          intro x y
          funext q
          rfl
        map_smul' := by
          intro c x
          funext q
          rfl }
    have hker : LinearMap.ker coeLinear = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply Subtype.ext
      exact hxy
    have hmap :=
      (linearIndependent_xiWeilAntiPart_of_quadratic_neg v hneg).map'
        coeLinear hker
    change LinearIndependent ℂ
      (coeLinear ∘ fun j => xiWeilAntiPart (v j))
    exact hmap
  exact GaloisForLFunctions.HTGeometry.exists_orbitSeparated_evaluation_minor_of_linearIndependent_antiInvariant
      xiZeroCopyLineConjEquiv (fun j q => xiWeilAntiPart (v j) q)
      hLI
      (fun j q => xiWeilAntiPart_lineConj_apply (v j) q)

/-- Matrix form of multiplicity-exact negative-index conservation. -/
theorem exists_xiZeroCopy_freeOrbitPacket_of_hilbertGram_negDef
    {k : ℕ} (v : Fin k → XiWeilCarrier)
    (hneg : ∀ x : Fin k → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (xiWeilHilbertGram v).mulVec x).re < 0) :
    ∃ (e : Fin k → XiZeroCopy) (P : Matrix (Fin k) (Fin k) ℂ),
      Function.Injective e ∧
      (∀ r s, xiZeroCopyLineConjEquiv (e r) ≠ e s) ∧
      IsUnit P.det ∧
      ∀ r s, P r s = xiWeilAntiPart (v s) (e r) :=
  exists_xiZeroCopy_freeOrbitPacket_of_quadratic_neg v
    (quadratic_neg_of_xiWeilHilbertGram_negDef v hneg)

end

end RHTower
