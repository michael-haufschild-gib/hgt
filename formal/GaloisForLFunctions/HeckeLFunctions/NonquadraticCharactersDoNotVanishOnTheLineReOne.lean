import GaloisForLFunctions.HeckeLFunctions.HeckeEulerLogarithmsGiveTheThreeFourOneInequality
import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.HTGeometry.RemovableSingularity

/-!
# Nonquadratic Hecke L-functions do not vanish on `Re s ≥ 1`

The three-four-one Euler product has norm at least one. A zero at `1 + it` would
make its fourth-power factor vanish to order at least four. The trivial character
contributes only a cubic pole, and the squared character is holomorphic because
`ψ² ≠ 1`. Canceling powers of `σ - 1` makes the product tend to zero, a contradiction.
The Euler product handles the open half-plane.
-/

noncomputable section

open Complex Filter Topology NumberField
open scoped Classical

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- A nontrivial Hecke L-function is holomorphic throughout its continuation half-plane. -/
theorem differentiableAt_heckeLCont {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) {s : ℂ}
    (hs : 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re) :
    DifferentiableAt ℂ (heckeLCont 𝔪 ψ) s :=
  (differentiableOn_heckeLCont hψ).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds hs)

/-- In particular, every nontrivial Hecke L-function is holomorphic at `1`. -/
theorem differentiableAt_heckeLCont_one {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    DifferentiableAt ℂ (heckeLCont 𝔪 ψ) 1 :=
  differentiableAt_heckeLCont hψ (errExp_lt_one (K := K))

/-- Nonquadratic Hecke characters have no zeros on `Re s = 1`. The Euler-product lower bound
contradicts the fourth-order zero after canceling the trivial character's cubic pole. -/
theorem heckeLCont_line_one_ne_zero_of_sq_ne_one {ψ : HeckeCharacter 𝔪}
    (hψ2 : ψ ^ 2 ≠ 1) (t : ℝ) :
    heckeLCont 𝔪 ψ (1 + I * t) ≠ 0 := by
  have hψ : ψ ≠ 1 := fun h => hψ2 (by rw [h]; ext g; simp)
  intro hzero
  have hc : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [ofReal_one] using
      (continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hc' : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    change (σ : ℂ) ≠ 1
    exact_mod_cast (show 1 < σ from hσ).ne'
  have hdiff : DifferentiableAt ℂ (fun s : ℂ => heckeLCont 𝔪 ψ (s + I * t)) 1 := by
    have h := differentiableAt_heckeLCont hψ (s := 1 + I * t)
      (by simpa using errExp_lt_one (K := K))
    exact h.comp 1 (differentiableAt_id.add_const _)
  have hquot : Tendsto (fun σ : ℝ => heckeL 𝔪 ψ (σ + I * t) / ((σ : ℂ) - 1))
      (𝓝[>] (1 : ℝ)) (𝓝 (deriv (fun s : ℂ => heckeLCont 𝔪 ψ (s + I * t)) 1)) := by
    have h := (HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero
      hdiff hzero).comp hc'
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact congrArg (fun z : ℂ => z / ((σ : ℂ) - 1))
      (heckeLCont_eq_heckeL hψ (by simpa using (show 1 < σ from hσ)))
  have hsq : Tendsto (fun σ : ℝ => heckeL 𝔪 (ψ ^ 2) (σ + 2 * I * t))
      (𝓝[>] (1 : ℝ)) (𝓝 (heckeLCont 𝔪 (ψ ^ 2) (1 + 2 * I * t))) := by
    have hd := differentiableAt_heckeLCont hψ2 (s := 1 + 2 * I * t)
      (by simpa using errExp_lt_one (K := K))
    refine (hd.continuousAt.tendsto.comp (hc.add_const (2 * I * t))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact heckeLCont_eq_heckeL hψ2 (by simpa using (show 1 < σ from hσ))
  have hsub : Tendsto (fun σ : ℝ => (σ : ℂ) - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa only [sub_self] using hc.sub_const 1
  have hprod := (((tendsto_sub_one_mul_heckeL_one (𝔪 := 𝔪)).pow 3).mul
    (hquot.pow 4)).mul hsq |>.mul hsub
  simp only [mul_zero] at hprod
  have hlim : Tendsto (fun σ : ℝ =>
      heckeL 𝔪 1 σ ^ 3 * heckeL 𝔪 ψ (σ + I * t) ^ 4 *
        heckeL 𝔪 (ψ ^ 2) (σ + 2 * I * t))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hs : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by
      exact_mod_cast (show 1 < σ from hσ).ne')
    field_simp [hs]
  have hge : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      1 ≤ ‖heckeL 𝔪 1 σ ^ 3 * heckeL 𝔪 ψ (σ + I * t) ^ 4 *
        heckeL 𝔪 (ψ ^ 2) (σ + 2 * I * t)‖ := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact one_le_norm_heckeL_three_four_one 𝔪 ψ (show 1 < σ from hσ) t
  have hcontr : (1 : ℝ) ≤ 0 := by simpa only [norm_zero] using ge_of_tendsto hlim.norm hge
  exact (not_le_of_gt zero_lt_one) hcontr

/-- The open-half-plane Euler product and the boundary argument give the closed half-plane. -/
theorem heckeLCont_ne_zero_of_sq_ne_one {ψ : HeckeCharacter 𝔪} (hψ2 : ψ ^ 2 ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) : heckeLCont 𝔪 ψ s ≠ 0 := by
  rcases hs.eq_or_lt with hs | hs
  · have hsform : s = 1 + I * s.im := by
      apply Complex.ext
      · simpa using hs.symm
      · simp
    rw [hsform]
    exact heckeLCont_line_one_ne_zero_of_sq_ne_one hψ2 s.im
  · have hψ : ψ ≠ 1 := fun h => hψ2 (by rw [h]; ext g; simp)
    rw [heckeLCont_eq_heckeL hψ hs]
    exact heckeL_ne_zero 𝔪 ψ hs

/-- Nonquadratic Hecke characters have nonzero L-value at `1`. -/
theorem heckeLCont_one_ne_zero_of_sq_ne_one {ψ : HeckeCharacter 𝔪} (hψ2 : ψ ^ 2 ≠ 1) :
    heckeLCont 𝔪 ψ 1 ≠ 0 := by
  simpa only [ofReal_zero, mul_zero, add_zero] using
    heckeLCont_line_one_ne_zero_of_sq_ne_one hψ2 0

/-- Any zero at `1` belongs to a character of order at most two. -/
theorem heckeLCont_one_eq_zero_implies_sq_eq_one (ψ : HeckeCharacter 𝔪) :
    heckeLCont 𝔪 ψ 1 = 0 → ψ ^ 2 = 1 := by
  intro hzero
  by_contra hψ2
  exact heckeLCont_one_ne_zero_of_sq_ne_one hψ2 hzero

end GaloisForLFunctions.HeckeLFunctions

