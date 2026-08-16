import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinHoheiselPrimeSupply

open Complex Filter Topology Set Finset
open MeasureTheory ArithmeticFunction
open GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

noncomputable section

/-- The buffered Ingham detector windows carry a fixed positive proportion of their width in
prime logarithmic mass.  This strengthens the existing eventual nonvanishing theorem: the full
smooth von Mangoldt mass tends to one after width normalization, while the normalized proper
prime-power leakage tends to zero. -/
theorem eventually_one_four_lt_inghamRouteTBuffered_normalized_theta_window :
    ∀ᶠ X : ℕ in atTop,
      (1 / 4 : ℝ) <
        (inghamRouteTMellinBufferedPhysicalWidth X)⁻¹ *
          (Chebyshev.theta
              (inghamRouteTMellinPhysicalCenter X +
                2 * inghamRouteTMellinBufferedPhysicalWidth X) -
            Chebyshev.theta (inghamRouteTMellinPhysicalCenter X)) := by
  have hmassRe := (Complex.continuous_re.tendsto (1 : ℂ)).comp
    tendsto_inghamRouteTBufferedNormalizedVonMangoldtMass_one
  simp only [Complex.one_re] at hmassRe
  have hmassLower := Filter.Tendsto.eventually_lt
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)))
    hmassRe (by norm_num : (1 / 2 : ℝ) < 1)
  have hleakUpper := Filter.Tendsto.eventually_lt
    tendsto_inghamRouteTBufferedPrimePowerLeakage_zero
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop (nhds (1 / 4)))
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hmassLower, hleakUpper, eventually_ge_atTop (2 : ℕ)] with
      X hmass hleak hX
  let N := inghamRouteTMellinPhysicalCenter X
  let H := inghamRouteTMellinBufferedPhysicalWidth X
  have hX1 : 1 ≤ X := by omega
  have hXR1 : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXR2 : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hN : 0 < N := inghamRouteTMellinPhysicalCenter_pos hX1
  have hN1 : 1 ≤ N := inghamRouteTMellinPhysicalCenter_one_le hX1
  have hN2 : 2 ≤ N := by
    dsimp only [N, inghamRouteTMellinPhysicalCenter]
    calc
      (2 : ℝ) ≤ (X : ℝ) := hXR2
      _ = (X : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (X : ℝ) ^ inghamRouteTPhysicalScaleExponent := by
        exact Real.rpow_le_rpow_of_exponent_le hXR1
          (by unfold inghamRouteTPhysicalScaleExponent; norm_num)
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX1
  have hH1 : 1 ≤ H := by
    dsimp only [H]
    rw [inghamRouteTMellinBufferedPhysicalWidth_eq_center_rpow hX1]
    exact Real.one_le_rpow hN1 (by norm_num)
  have hsmoothPsi := routeT_smooth_vonMangoldt_mass_le_chebyshevPsi_window hN.le hH
  have hpsiTheta := chebyshevPsi_window_le_theta_window_add_local_primePower
    hN2 (by linarith : N ≤ N + 2 * H) (by linarith : 1 ≤ (N + 2 * H) - N)
  have hsmoothTheta :
      (∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n) ≤
        Chebyshev.theta (N + 2 * H) - Chebyshev.theta N +
          (Real.log (N + 2 * H) / Real.log 2) *
            (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H) := by
    calc
      (∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n) ≤
          Chebyshev.psi (N + 2 * H) - Chebyshev.psi N := hsmoothPsi
      _ ≤ Chebyshev.theta (N + 2 * H) - Chebyshev.theta N +
          (Real.log (N + 2 * H) / Real.log 2) *
            (Real.sqrt ((N + 2 * H) - N) + 1) * Real.log (N + 2 * H) := hpsiTheta
      _ = _ := by ring_nf
  have hnormle :
      H⁻¹ * (∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n) ≤
        H⁻¹ * (Chebyshev.theta (N + 2 * H) - Chebyshev.theta N) +
          inghamRouteTBufferedPrimePowerLeakage X := by
    calc
      H⁻¹ * (∑' n : ℕ, (vonMangoldt n : ℝ) * routeTSmoothWindowWeight N H n) ≤
          H⁻¹ * (Chebyshev.theta (N + 2 * H) - Chebyshev.theta N +
            (Real.log (N + 2 * H) / Real.log 2) *
              (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H)) :=
        mul_le_mul_of_nonneg_left hsmoothTheta (inv_nonneg.mpr hH.le)
      _ = H⁻¹ * (Chebyshev.theta (N + 2 * H) - Chebyshev.theta N) +
          inghamRouteTBufferedPrimePowerLeakage X := by
        unfold inghamRouteTBufferedPrimePowerLeakage
        dsimp only [N, H]
        field_simp
  have hmassEq := inghamRouteTBufferedNormalizedVonMangoldtMass_re_eq X
  simp only [Function.comp_apply] at hmass
  rw [hmassEq] at hmass
  dsimp only [N, H] at hnormle ⊢
  linarith

/-- Unnormalized form of the quantitative detector-window prime-mass lower bound. -/
theorem eventually_inghamRouteTBuffered_theta_window_gt_quarter_width :
    ∀ᶠ X : ℕ in atTop,
      inghamRouteTMellinBufferedPhysicalWidth X / 4 <
        Chebyshev.theta
            (inghamRouteTMellinPhysicalCenter X +
              2 * inghamRouteTMellinBufferedPhysicalWidth X) -
          Chebyshev.theta (inghamRouteTMellinPhysicalCenter X) := by
  filter_upwards
      [eventually_one_four_lt_inghamRouteTBuffered_normalized_theta_window,
        eventually_ge_atTop (1 : ℕ)] with X htheta hX
  have hH : 0 < inghamRouteTMellinBufferedPhysicalWidth X :=
    inghamRouteTMellinBufferedPhysicalWidth_pos hX
  rw [inv_mul_eq_div] at htheta
  have hmul := (lt_div_iff₀ hH).mp htheta
  linarith

end

end RHTower.Sieve
