import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmTwoPrimeBezout

/-!
# Growth obstruction for the two-prime Bezout identity

Prime-2 and prime-3 centered multipliers generate the unit ideal algebraically, but no Bezout pair
can remain uniformly bounded on the real axis. Both centered multipliers decay to zero there, so
bounded coefficients would force their Bezout combination to decay to zero rather than equal one.
This separates entire-ideal generation from the bounded multiplier synthesis needed by the fixed
mass spectral trace.
-/

open Complex Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

theorem tendsto_norm_centeredMultiplierE_atTop (n : ℕ) :
    Tendsto (fun t : ℝ => ‖centeredMultiplierE n (t : ℂ)‖) atTop (𝓝 0) := by
  apply (tendsto_norm_centeredMultiplier_atTop n).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [centeredMultiplierE_eq n (by exact_mod_cast ht.ne')]

theorem no_uniformly_bounded_real_two_prime_bezout
    (b₂ b₃ : ℝ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb₂ : ∀ t : ℝ, ‖b₂ t‖ ≤ C) (hb₃ : ∀ t : ℝ, ‖b₃ t‖ ≤ C) :
    ¬ ∀ t : ℝ,
      b₂ t * centeredMultiplierE 2 (t : ℂ) +
        b₃ t * centeredMultiplierE 3 (t : ℂ) = 1 := by
  intro hbez
  let D : ℝ := C + 1
  have hD : 0 < D := by dsimp [D]; linarith
  let ε : ℝ := 1 / (4 * D)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have h2 := (tendsto_norm_centeredMultiplierE_atTop 2).eventually
    (Iio_mem_nhds hε)
  have h3 := (tendsto_norm_centeredMultiplierE_atTop 3).eventually
    (Iio_mem_nhds hε)
  obtain ⟨t, ht2, ht3⟩ := (h2.and h3).exists
  have hCD : C ≤ D := by dsimp [D]; linarith
  have hprod2 : ‖b₂ t * centeredMultiplierE 2 (t : ℂ)‖ < 1 / 4 := by
    rw [norm_mul]
    calc
      ‖b₂ t‖ * ‖centeredMultiplierE 2 (t : ℂ)‖ ≤
          D * ‖centeredMultiplierE 2 (t : ℂ)‖ :=
        mul_le_mul_of_nonneg_right ((hb₂ t).trans hCD) (norm_nonneg _)
      _ < D * ε := mul_lt_mul_of_pos_left ht2 hD
      _ = 1 / 4 := by dsimp [ε]; field_simp
  have hprod3 : ‖b₃ t * centeredMultiplierE 3 (t : ℂ)‖ < 1 / 4 := by
    rw [norm_mul]
    calc
      ‖b₃ t‖ * ‖centeredMultiplierE 3 (t : ℂ)‖ ≤
          D * ‖centeredMultiplierE 3 (t : ℂ)‖ :=
        mul_le_mul_of_nonneg_right ((hb₃ t).trans hCD) (norm_nonneg _)
      _ < D * ε := mul_lt_mul_of_pos_left ht3 hD
      _ = 1 / 4 := by dsimp [ε]; field_simp
  have hnorm := norm_add_le
    (b₂ t * centeredMultiplierE 2 (t : ℂ))
    (b₃ t * centeredMultiplierE 3 (t : ℂ))
  rw [hbez t, norm_one] at hnorm
  linarith

end

end RHTower.HedenmalmThetaSource
