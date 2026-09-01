import GaloisForLFunctions.RHTower.SeamInertiaCharge
import GaloisForLFunctions.HTGeometry.CarrierExactPositiveInertia
import GaloisForLFunctions.RHTower.BeurlingRHSensitivityThreshold
import GaloisForLFunctions.RHTower.EntireFunctionalEquationOffLine

/-!
# Off-line zeros of the two countermodels are hyperbolic planes of the seam carrier

The FE seam carrier of `k` distinct upper-half-plane poles has negative index exactly `k`
(`seamCarrier_exact_inertia`).  Here the positive index is shown to be exactly `k` as well, so the
carrier is exactly `k` hyperbolic planes: one positive and one negative square per off-line pair.

Both explicit countermodels of the corpus feed this carrier unconditionally.

* The Beurling countermodel `perturbedZeta β γ` vanishes at `β + iγ` with `1/2 < β < 1`.  For every
  tolerance, an adjoined prime density of reciprocal mass below that tolerance produces such a zero,
  and the seam carrier at that zero is one full hyperbolic plane.  The index is therefore a
  discontinuous invariant of the reciprocal mass.
* The entire functional-equation countermodel `offLineQuartet a0 gam` vanishes at the two
  upper-half-plane points `1/2 ± a0 + i gam`; its seam carrier is exactly two hyperbolic planes.
-/

open Complex Matrix GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact inertia `(k, k)` of the FE seam carrier at poles `t` on a node configuration `z`: every
negative-definite subspace has dimension at most `k` and one of dimension `k` exists, and the same
for positive-definite subspaces. -/
def SeamCarrierExactInertia {k : ℕ} (t : Fin k → ℂ) (z : Fin (2 * k) → ℂ) : Prop :=
  ((∀ W : Submodule ℂ (Fin (2 * k) → ℂ),
      (∀ y ∈ W, y ≠ 0 →
        (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re < 0)
      → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin (2 * k) → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 →
          (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re < 0))
  ∧ ((∀ W : Submodule ℂ (Fin (2 * k) → ℂ),
      (∀ y ∈ W, y ≠ 0 →
        0 < (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re)
      → Module.finrank ℂ W ≤ k)
    ∧ (∃ W : Submodule ℂ (Fin (2 * k) → ℂ), Module.finrank ℂ W = k ∧
        ∀ y ∈ W, y ≠ 0 →
          0 < (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re))

/-- **Exact seam positive index `κ₊ = k`, unconditional.**  For `k` distinct off-line poles there is a
node configuration on which every positive-definite subspace of the FE seam Gram has dimension at
most `k`, and one of dimension `k` exists. -/
theorem seamCarrier_exact_pos_inertia {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) :
    ∃ z : Fin (2 * k) → ℂ,
      (∀ W : Submodule ℂ (Fin (2 * k) → ℂ),
          (∀ y ∈ W, y ≠ 0 →
            0 < (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re)
          → Module.finrank ℂ W ≤ k)
      ∧ (∃ W : Submodule ℂ (Fin (2 * k) → ℂ), Module.finrank ℂ W = k ∧
          ∀ y ∈ W, y ≠ 0 →
            0 < (star y ⬝ᵥ (factoredKreinForm (seamW t z) (seamU t z)).mulVec y).re) := by
  obtain ⟨z, Φ, Ψ, hΦ, hΨ, hT⟩ := exists_seamCarrier_surjective t ht htinj
  exact ⟨z, exact_pos_inertia (seamW t z) (seamU t z) Φ Ψ hΦ hΨ hT⟩

/-- **One hyperbolic plane per off-line pair, unconditional.**  For `k` distinct off-line poles there
is a node configuration on which the FE seam Gram has inertia exactly `(k, k)`. -/
theorem seamCarrier_exact_inertia_pair {k : ℕ} (t : Fin k → ℂ)
    (ht : ∀ i, 0 < (t i).im) (htinj : Function.Injective t) :
    ∃ z : Fin (2 * k) → ℂ, SeamCarrierExactInertia t z := by
  obtain ⟨z, Φ, Ψ, hΦ, hΨ, hT⟩ := exists_seamCarrier_surjective t ht htinj
  exact ⟨z, exact_neg_inertia (seamW t z) (seamU t z) Φ Ψ hΦ hΨ hT,
    exact_pos_inertia (seamW t z) (seamU t z) Φ Ψ hΦ hΨ hT⟩

/-! ## The Beurling countermodel -/

/-- The off-line zero of the Beurling countermodel lies in the upper half-plane. -/
theorem beurlingCountermodel_zero_im_pos (β : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    0 < ((β : ℂ) + (γ : ℂ) * I).im := by
  simp [hγ]

/-- **The Beurling countermodel's off-line zero is one hyperbolic plane of the seam carrier.** -/
theorem beurlingCountermodel_seam_hyperbolicPlane (β : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    BeurlingSensitivity.perturbedZeta β γ ((β : ℂ) + (γ : ℂ) * I) = 0 ∧
      ∃ z : Fin (2 * 1) → ℂ, SeamCarrierExactInertia ![(β : ℂ) + (γ : ℂ) * I] z := by
  refine ⟨BeurlingSensitivity.perturbedZeta_eq_zero β hγ.ne', ?_⟩
  apply seamCarrier_exact_inertia_pair
  · intro i
    fin_cases i
    simpa using beurlingCountermodel_zero_im_pos β hγ
  · intro a b _
    exact Subsingleton.elim a b

/-- **Index discontinuity in the reciprocal mass.**  For every `1/2 < β < 1` and every tolerance
`ε > 0`, an adjoined positive prime density of reciprocal mass below `ε` produces a zero at
`β + iγ` whose seam carrier is one full hyperbolic plane. -/
theorem beurling_small_reciprocalMass_seam_hyperbolicPlane
    {β : ℝ} (hβ1 : 1 / 2 < β) (hβ2 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧
      Real.log (1 + γ ^ 2 / (1 - β) ^ 2) < ε ∧
      BeurlingSensitivity.perturbedZeta β γ ((β : ℂ) + (γ : ℂ) * I) = 0 ∧
      1 / 2 < ((β : ℂ) + (γ : ℂ) * I).re ∧
      ∃ z : Fin (2 * 1) → ℂ, SeamCarrierExactInertia ![(β : ℂ) + (γ : ℂ) * I] z := by
  obtain ⟨γ, hγ, hmass, _, hzero, hre⟩ := BeurlingSensitivity.exists_small_reciprocalMass_zero_off_line hβ1 hβ2 hε
  exact ⟨γ, hγ, hmass, hzero, hre, (beurlingCountermodel_seam_hyperbolicPlane β hγ).2⟩

/-! ## The entire functional-equation countermodel -/

/-- The quartet also vanishes at the reflected upper-half-plane point `1/2 - a0 + i gam`. -/
theorem offLineQuartet_eq_zero_reflected (a0 gam : ℝ) :
    offLineQuartet a0 gam (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 := by
  unfold offLineQuartet
  simp

/-- **The entire countermodel's two upper-half-plane zeros are two hyperbolic planes.**  For
`a0 > 0` and `gam > 0`, the quartet factor of the entire, functional-equation-symmetric, `Λ`-positive
countermodel vanishes at the two distinct upper-half-plane points `1/2 ± a0 + i gam`, and the seam
carrier at those two poles has inertia exactly `(2, 2)`. -/
theorem entireCountermodel_seam_two_hyperbolicPlanes {a0 gam : ℝ}
    (ha0 : 0 < a0) (hgam : 0 < gam) :
    offLineQuartet a0 gam (((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 ∧
    offLineQuartet a0 gam (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I) = 0 ∧
    ∃ z : Fin (2 * 2) → ℂ,
      SeamCarrierExactInertia
        ![(((1 / 2 + a0 : ℝ) : ℂ) + (gam : ℂ) * I),
          (((1 / 2 - a0 : ℝ) : ℂ) + (gam : ℂ) * I)] z := by
  refine ⟨offLineQuartet_eq_zero a0 gam, offLineQuartet_eq_zero_reflected a0 gam, ?_⟩
  apply seamCarrier_exact_inertia_pair
  · intro i
    fin_cases i <;> simp [hgam]
  · intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      have h := congrArg Complex.re hab
      simp at h
      linarith
    · exfalso
      have h := congrArg Complex.re hab
      simp at h
      linarith
    · rfl

end

end RHTower
