import GaloisForLFunctions.HTGeometry.CompactAbelianStoneWeierstrass
import GaloisForLFunctions.HTGeometry.BohrHullFrequency
import GaloisForLFunctions.HTGeometry.RealCharacterExp

/-!
# The approximation theorem for almost-periodic functions

Every Bohr almost-periodic function is a uniform limit of trigonometric polynomials.

The proof is a transfer along the hull.  The hull of `f` is a compact abelian group, so its
continuous characters separate points (Peter–Weyl) and their linear span is dense in the continuous
functions on it (Stone–Weierstrass).  Approximating the evaluation map and pulling back along the
dense homomorphism `ι : ℝ → BohrHull f` gives an approximation of `f`, and each character composed
with `ι` is a continuous character of the line, hence an exponential `t ↦ e^{iλt}`.
-/

open MeasureTheory TopologicalSpace

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- **The approximation theorem.**  A Bohr almost-periodic function is uniformly approximated by
trigonometric polynomials. -/
theorem exists_trig_approx {f : ℝ →ᵇ ℂ} (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (lam : Fin n → ℝ),
      ∀ t : ℝ, ‖f t - ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)‖ ≤ ε := by
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  borelize (BohrHull f)
  set F : C(BohrHull f, ℂ) := ⟨bohrEval f, continuous_bohrEval f⟩ with hF
  obtain ⟨n, c, χ, hχ, hclose⟩ :=
    CompactAbelian.exists_char_combination_approx F (half_pos hε)
  have hpull : ∀ j : Fin n, ∃ lam : ℝ, ∀ t : ℝ,
      χ j (bohrIota f t) = Complex.exp ((lam * t : ℝ) * Complex.I) := by
    intro j
    refine exists_exp_of_continuous_character ?_ ?_ ?_
    · exact (χ j).continuous.comp (continuous_bohrIota hf)
    · intro s t
      rw [bohrIota_add, (hχ j).map_add]
    · intro t
      exact (hχ j).norm_one _
  choose lam hlam using hpull
  refine ⟨n, c, lam, fun t => ?_⟩
  have hval : (F - ∑ j, c j • χ j) (bohrIota f t)
      = f t - ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I) := by
    rw [ContinuousMap.sub_apply]
    congr 1
    · show bohrEval f (bohrIota f t) = f t
      exact bohrEval_bohrIota f t
    · rw [ContinuousMap.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousMap.smul_apply, smul_eq_mul, hlam j t]
  rw [← hval]
  calc ‖(F - ∑ j, c j • χ j) (bohrIota f t)‖ ≤ ‖F - ∑ j, c j • χ j‖ :=
        ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ε := by linarith [hclose]

end

end GaloisForLFunctions
