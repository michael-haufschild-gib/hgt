import GaloisForLFunctions.HTGeometry.TranslatedFourierCoeffAnalytic

/-!
# The scaling law for active coefficients

Multiplicative translation multiplies the `m`-th active coefficient by the
monomial `h^m`.  On the torus this is the invariance of Haar measure.  Off the
torus both sides are holomorphic in each coordinate of the translation — the
left by differentiation under the integral sign, the right visibly — and the
torus is a uniqueness set for the polyannulus, so the identity propagates to
every translation by a point of the polyannulus.

No Laurent expansion is used anywhere.
-/

open Complex Set Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Monomials -/

/-- The monomial `h^m`. -/
def charPow (h : d → ℂ) (m : d → ℤ) : ℂ := ∏ j, (h j) ^ (m j)

theorem fourier_eq_zpow (n : ℤ) (y : UnitAddCircle) :
    fourier n y = (fourier 1 y) ^ n := by
  rw [fourier_apply, fourier_apply, one_smul, AddCircle.toCircle_zsmul,
    Circle.coe_zpow]

omit [DecidableEq d] in
theorem charPow_circleCoords (x : UnitAddTorus d) (m : d → ℤ) :
    charPow (circleCoords x) m = UnitAddTorus.mFourier m x := by
  simp only [charPow, UnitAddTorus.mFourier, ContinuousMap.coe_mk, circleCoords]
  exact Finset.prod_congr rfl fun j _ => (fourier_eq_zpow (m j) (x j)).symm

theorem charPow_update (g : d → ℂ) (i : d) (w : ℂ) (m : d → ℤ) :
    charPow (Function.update g i w) m
      = w ^ (m i) * ∏ j ∈ Finset.univ.erase i, (g j) ^ (m j) := by
  classical
  rw [charPow, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-! ### Analyticity of the monomial slice -/

theorem analyticOnNhd_zpow_of_ne_zero (n : ℤ) {U : Set ℂ}
    (hU : ∀ w ∈ U, w ≠ 0) : AnalyticOnNhd ℂ (fun w : ℂ => w ^ n) U := by
  intro w hw
  cases n with
  | ofNat k =>
      have hfun : (fun w : ℂ => w ^ (Int.ofNat k)) = fun w : ℂ => w ^ k := by
        funext u
        rw [Int.ofNat_eq_natCast, zpow_natCast]
      rw [hfun]
      exact (analyticAt_id (𝕜 := ℂ) (z := w)).pow k
  | negSucc k =>
      have hfun : (fun w : ℂ => w ^ (Int.negSucc k))
          = fun w : ℂ => (w ^ (k + 1))⁻¹ := by
        funext u
        rw [zpow_negSucc]
      rw [hfun]
      exact ((analyticAt_id (𝕜 := ℂ) (z := w)).pow (k + 1)).inv
        (pow_ne_zero _ (hU w hw))

omit [DecidableEq d] in
theorem ne_zero_of_mem_logAnnulus {c : ℝ} {w : ℂ} (hw : w ∈ logAnnulus c) :
    w ≠ 0 := by
  rintro rfl
  have h := hw.1
  rw [norm_zero] at h
  exact absurd h (not_lt.2 (Real.exp_nonneg _))

/-! ### The scaling law -/

/-- **The scaling law for active coefficients.**  Translating a phase
observable by a point of the polyannulus multiplies its `m`-th active
coefficient by the monomial `h^m`. -/
theorem activeCoeff_comp_torusScale_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (m : d → ℤ) :
    ∀ h ∈ polyannulus ρ,
      activeCoeff (fun z => F (torusScale h z)) m = charPow h m * activeCoeff F m := by
  classical
  refine eqOn_polyannulus_of_slice hρ (fun g hg i => ?_) (fun y hy => ?_)
  · -- the two sides are holomorphic in the `i`-th coordinate
    have hleft := analyticOnNhd_slice_activeCoeff_comp_torusScale hF m hg i
    have hne : ∀ w ∈ logAnnulus (ρ i), w ≠ 0 := fun w hw =>
      ne_zero_of_mem_logAnnulus hw
    have hright : AnalyticOnNhd ℂ
        (fun w : ℂ => charPow (Function.update g i w) m * activeCoeff F m)
        (logAnnulus (ρ i)) := by
      have hfun : (fun w : ℂ => charPow (Function.update g i w) m * activeCoeff F m)
          = fun w : ℂ => w ^ (m i) *
            ((∏ j ∈ Finset.univ.erase i, (g j) ^ (m j)) * activeCoeff F m) := by
        funext w
        rw [charPow_update]
        ring
      rw [hfun]
      exact (analyticOnNhd_zpow_of_ne_zero (m i) hne).mul analyticOnNhd_const
    exact hleft.sub hright
  · -- on the torus this is the Haar-invariance computation
    obtain ⟨x, hx⟩ := unitTorus_subset_range_circleCoords hy
    rw [← hx, activeCoeff_comp_torusScale F x m, charPow_circleCoords]

end

end GaloisForLFunctions.HTGeometry
