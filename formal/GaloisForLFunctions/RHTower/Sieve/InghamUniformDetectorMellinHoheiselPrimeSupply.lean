import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullPhysicalMass
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinPrimePowerLeakage

open Complex Filter Topology Set Finset
open MeasureTheory ArithmeticFunction
open GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

noncomputable section

theorem inghamRouteTBufferedNormalizedVonMangoldtMass_re_eq
    (X : ℕ) :
    (inghamRouteTBufferedNormalizedVonMangoldtMass X).re =
      (inghamRouteTMellinBufferedPhysicalWidth X)⁻¹ *
        ∑' n : ℕ, (vonMangoldt n : ℝ) *
          routeTSmoothWindowWeight
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) (n : ℝ) := by
  rw [inghamRouteTBufferedNormalizedVonMangoldtMass]
  have hsum :
      (∑' n : ℕ, ((vonMangoldt n : ℝ) : ℂ) *
          ((routeTSmoothWindowWeight
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) (n : ℝ) : ℝ) : ℂ)) =
        ∑' n : ℕ, ((
          (vonMangoldt n : ℝ) * routeTSmoothWindowWeight
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinBufferedPhysicalWidth X) (n : ℝ) : ℝ) : ℂ) := by
    apply tsum_congr
    intro n
    exact (Complex.ofReal_mul _ _).symm
  rw [hsum]
  rw [← Complex.ofReal_tsum]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  exact Complex.ofReal_re _

theorem eventually_inghamRouteTBuffered_theta_window_ne_zero :
    ∀ᶠ X : ℕ in atTop,
      Chebyshev.theta
          (inghamRouteTMellinPhysicalCenter X +
            2 * inghamRouteTMellinBufferedPhysicalWidth X) -
        Chebyshev.theta (inghamRouteTMellinPhysicalCenter X) ≠ 0 := by
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
  intro hprimeFree
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
  have hlocal := routeT_primeFree_smooth_vonMangoldt_mass_le_local_primePower
    hN2 hH (by linarith : 1 ≤ 2 * H) hprimeFree
  have hnormle :
      H⁻¹ *
          (∑' n : ℕ, (vonMangoldt n : ℝ) *
            routeTSmoothWindowWeight N H n) ≤
        inghamRouteTBufferedPrimePowerLeakage X := by
    calc
      H⁻¹ *
          (∑' n : ℕ, (vonMangoldt n : ℝ) *
            routeTSmoothWindowWeight N H n) ≤
        H⁻¹ *
          ((Real.log (N + 2 * H) / Real.log 2) *
            (Real.sqrt (2 * H) + 1) * Real.log (N + 2 * H)) :=
              mul_le_mul_of_nonneg_left hlocal (inv_nonneg.mpr hH.le)
      _ = inghamRouteTBufferedPrimePowerLeakage X := by
        unfold inghamRouteTBufferedPrimePowerLeakage
        dsimp only [N, H]
        ring
  have hmassEq := inghamRouteTBufferedNormalizedVonMangoldtMass_re_eq X
  dsimp only [N, H] at hnormle
  simp only [Function.comp_apply] at hmass
  rw [hmassEq] at hmass
  linarith

theorem exists_eventually_inghamRouteTBuffered_prime :
    ∀ᶠ X : ℕ in atTop,
      ∃ p : ℕ, p.Prime ∧
        inghamRouteTMellinPhysicalCenter X < (p : ℝ) ∧
        (p : ℝ) ≤ inghamRouteTMellinPhysicalCenter X +
          2 * inghamRouteTMellinBufferedPhysicalWidth X := by
  filter_upwards [eventually_inghamRouteTBuffered_theta_window_ne_zero,
      eventually_ge_atTop (1 : ℕ)] with X htheta hX
  let N := inghamRouteTMellinPhysicalCenter X
  let H := inghamRouteTMellinBufferedPhysicalWidth X
  let P : Finset ℕ := (Finset.Ioc ⌊N⌋₊ ⌊N + 2 * H⌋₊).filter Nat.Prime
  have hN : 0 ≤ N := (inghamRouteTMellinPhysicalCenter_pos hX).le
  have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX
  have hNB : N ≤ N + 2 * H := by linarith
  have hfloor : ⌊N⌋₊ ≤ ⌊N + 2 * H⌋₊ := Nat.floor_mono hNB
  have hthetaSum : Chebyshev.theta (N + 2 * H) - Chebyshev.theta N =
      ∑ p ∈ P, Real.log p := by
    dsimp only [P]
    simpa only [Chebyshev.theta, Nat.floor_natCast] using
      (RHTower.theta_window_eq hfloor)
  have hP : P.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hthetaSum, hempty, Finset.sum_empty] at htheta
    exact htheta rfl
  obtain ⟨p, hp⟩ := hP
  have hpdata := Finset.mem_filter.mp hp
  have hpIoc := Finset.mem_Ioc.mp hpdata.1
  refine ⟨p, hpdata.2, ?_, ?_⟩
  · exact (Nat.floor_lt hN).mp hpIoc.1
  · exact (by exact_mod_cast hpIoc.2 : (p : ℝ) ≤ (⌊N + 2 * H⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))

end

end RHTower.Sieve
