import GaloisForLFunctions.RHTower.ProlateLowSeparationMode
import GaloisForLFunctions.RHTower.ProlateRadialNormalization
import GaloisForLFunctions.RHTower.ProlateExactChannel

/-!
# The exterior channel bound, unconditionally

The exact-channel estimate bounds the sum over all dilation channels of the radial primitives of a
prolate profile, given a profile that is endpoint normalized, solves the radial equation, and has
separation ratio in `[0, 1/2]`.  Every one of those inputs is now a theorem: the variational
selection produces an even joint band/prolate eigenfunction with separation ratio below `1/2`, the
endpoint value of such an eigenfunction cannot vanish, and endpoint normalization preserves the
equation.

The result is a bandwidth-uniform bound with no hypotheses beyond `c ≥ 400`.
-/

noncomputable section

open MeasureTheory

namespace RHTower

/-- **Radial data with separation ratio at most one half exists.** -/
theorem exists_radialProlate_data_separation_le_half {c : ℝ} (hc : 400 ≤ c) :
    ∃ (R : ℝ → ℝ) (s : ℝ),
      0 ≤ s ∧ s ≤ 1 / 2 ∧ R 1 = 1 ∧ Function.Even R ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R ∧
        (∀ t : ℝ, HasDerivAt R (deriv R t) t) ∧
        (∀ t : ℝ, HasDerivAt (deriv R) (deriv (deriv R) t) t) ∧
        (∀ t : ℝ, (t ^ 2 - 1) * deriv (deriv R) t + 2 * t * deriv R t
          - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) := by
  have hc0 : (0 : ℝ) < c := by linarith
  obtain ⟨lam, eta, Phi, hlam, hsm, hne, heven, hband, heig, hsep⟩ :=
    exists_even_joint_prolate_eigen_separation_lt_half hc
  have hPhi1 : Phi 1 ≠ 0 :=
    value_one_ne_of_joint_prolate_band_eigen hsm hne hlam hband heig
  have hd1 : Differentiable ℝ Phi := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Phi) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).1
  set R : ℝ → ℝ := prolateEndpointNormalize Phi with hR
  have hRsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R := contDiff_prolateEndpointNormalize hsm
  have hRd1 : Differentiable ℝ R := (contDiff_infty_iff_deriv.mp hRsm).1
  have hRd2 : Differentiable ℝ (deriv R) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hRsm).2).1
  have hReig : ∀ x : ℝ, prolateSLAction c R x = eta * R x :=
    prolateSLAction_endpointNormalize hd1 hd2 heig
  have hchi : eta ≤ 0 :=
    GaloisForLFunctions.RHTower.prolateSeparation_nonpos_of_global_joint hlam hsm hne hband heig
  refine ⟨R, radialSeparationRatio c eta, ?_, ?_,
    prolateEndpointNormalize_one hPhi1, even_prolateEndpointNormalize heven, hRsm,
    fun t => (hRd1 t).hasDerivAt, fun t => (hRd2 t).hasDerivAt, ?_⟩
  · exact div_nonneg (neg_nonneg.mpr hchi) (sq_nonneg c)
  · exact le_of_lt hsep
  · exact radialProlate_ode_of_prolateSLAction_eq hc0.ne' hReig

/-- **The exterior channel bound, with no hypotheses beyond the bandwidth.**  At every bandwidth
`c ≥ 400` there is an endpoint-normalized even radial prolate profile whose radial primitives, summed
over every dilation channel, are bounded uniformly in the endpoint. -/
theorem exists_radialProlate_channel_bound {c : ℝ} (hc : 400 ≤ c) :
    ∃ (R : ℝ → ℝ) (s : ℝ),
      0 ≤ s ∧ s ≤ 1 / 2 ∧ R 1 = 1 ∧ Function.Even R ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R ∧
        (∀ t : ℝ, (t ^ 2 - 1) * deriv (deriv R) t + 2 * t * deriv R t
          - (s * c ^ 2 - c ^ 2 * t ^ 2) * R t = 0) ∧
        ∀ X : ℝ, 1 ≤ X →
          ‖∫ t in (1 : ℝ)..X, ((R t : ℝ) : ℂ)‖
              + ∑' j : ℕ, ‖∫ t in (1 : ℝ)..X, ((R ((2 + (j : ℝ)) * t) : ℝ) : ℂ)‖
            ≤ GaloisForLFunctions.RHTower.prolateEndpointConstant / (c * Real.sqrt c)
              + 6750 * GaloisForLFunctions.RHTower.exactEnergyBudget s c R (deriv R) 2 /
                  (Real.sqrt c * c) := by
  obtain ⟨R, s, hs0, hs1, hR1, hReven, hRsm, hR, hDR, hode⟩ :=
    exists_radialProlate_data_separation_le_half hc
  refine ⟨R, s, hs0, hs1, hR1, hReven, hRsm, hode, fun X hX1 => ?_⟩
  exact GaloisForLFunctions.RHTower.tsum_norm_integral_radialProlate_all_channels_le
    hs0 hs1 (by linarith : (5 : ℝ) ≤ c) hR1 hX1 hR hDR hode

end RHTower
