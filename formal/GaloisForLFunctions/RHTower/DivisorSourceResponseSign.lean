import GaloisForLFunctions.RHTower.DivisorSourceLogPhase

/-!
# Persistent vertical sign obstruction for the literal divisor response

The candidate response `1/s - B'(s)/B(s)` cannot have nonnegative real
part throughout any right half-plane. The source phase, rather than a
numerical sample, gives negative values at unbounded original heights
on every sufficiently right vertical line.
-/

noncomputable section
open Complex Filter Topology
namespace RHTower

/-- Candidate logarithmic response obtained from the exact divisor-source quotient. -/
def divisorSourceLogResponse (s : ℂ) : ℂ :=
  1/s - deriv divisorSourceEntire s / divisorSourceEntire s

private theorem normalized_real_lower :
    ∃ σ₀ : ℝ, 1 < σ₀ ∧ ∀ s : ℂ, σ₀ ≤ s.re →
      divisorSourceLogPhaseCoefficient / 2 <
        ((2 : ℂ)^s * (deriv divisorSourceEntire s / divisorSourceEntire s)).re := by
  have h := Complex.continuous_re.tendsto (divisorSourceLogPhaseCoefficient : ℂ)
    |>.comp divisorSourceEntire_logarithmic_first_mode
  have he : ∀ᶠ s : ℂ in comap Complex.re atTop,
      divisorSourceLogPhaseCoefficient / 2 <
        ((2 : ℂ)^s * (deriv divisorSourceEntire s / divisorSourceEntire s)).re :=
    h.eventually (Ioi_mem_nhds (by
      simp only [Complex.ofReal_re]
      linarith [divisorSourceLogPhaseCoefficient_pos]))
  obtain ⟨σ₀, hσ₀⟩ := eventually_atTop.mp (eventually_comap.mp he)
  refine ⟨max 2 σ₀, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro s hs
  exact hσ₀ s.re ((le_max_right _ _).trans hs) s rfl

private theorem two_cpow_at_period (σ : ℝ) (k : ℕ) :
    (2 : ℂ)^((σ : ℂ) + ((2 * Real.pi / Real.log 2 * (k : ℝ) : ℝ) : ℂ) * I) =
      (((2 : ℝ)^σ : ℝ) : ℂ) := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hp : (((2 : ℝ)^σ : ℝ) : ℂ) = (2 : ℂ)^(σ : ℂ) := by
    exact_mod_cast Complex.ofReal_cpow (x := 2) (by norm_num) σ
  have hlog : (Real.log 2 : ℂ) = Complex.log (2 : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using Complex.ofReal_log (x := 2) (by norm_num)
  rw [Complex.cpow_add _ _ (by norm_num),
    ← hp,
    Complex.cpow_def_of_ne_zero (by norm_num),
    ← hlog]
  have he : (Real.log 2 : ℂ) *
      (((2 * Real.pi / Real.log 2 * (k : ℝ) : ℝ) : ℂ) * I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    push_cast
    field_simp
  rw [he, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- Every sufficiently right vertical line contains negative responses above every height.
The source denominator is nonzero at each witness. -/
theorem divisorSourceLogResponse_negative_cofinally :
    ∃ σ₀ : ℝ, 1 < σ₀ ∧ ∀ σ : ℝ, σ₀ ≤ σ → ∀ T : ℝ,
      ∃ t : ℝ, T < t ∧ divisorSourceEntire ((σ : ℂ) + (t : ℂ)*I) ≠ 0 ∧
        (divisorSourceLogResponse ((σ : ℂ) + (t : ℂ)*I)).re < 0 := by
  obtain ⟨σ₀, hσ₀, hphase⟩ := normalized_real_lower
  refine ⟨σ₀, hσ₀, ?_⟩
  intro σ hσ T
  let r : ℝ := (2 : ℝ)^σ
  let d : ℝ := divisorSourceLogPhaseCoefficient / (2*r)
  let c : ℝ := 2 * Real.pi / Real.log 2
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hd : 0 < d := div_pos divisorSourceLogPhaseCoefficient_pos (by positivity)
  have hc : 0 < c := div_pos (mul_pos (by norm_num) Real.pi_pos)
    (Real.log_pos (by norm_num))
  obtain ⟨k, hk⟩ := exists_nat_gt (max T (1/d) / c)
  let t : ℝ := c * k
  let s : ℂ := (σ : ℂ) + (t : ℂ)*I
  have htmax : max T (1/d) < t := by
    dsimp [t]
    exact (div_lt_iff₀ hc).mp hk |>.trans_eq (mul_comm _ _)
  have htT : T < t := (le_max_left _ _).trans_lt htmax
  have htd : 1/d < t := (le_max_right _ _).trans_lt htmax
  have ht : 0 < t := (one_div_pos.mpr hd).trans htd
  have hsr : s.re = σ := by simp [s]
  have hsi : s.im = t := by simp [s]
  have hp := hphase s (by simpa only [hsr] using hσ)
  have hBn : divisorSourceEntire s ≠ 0 := by
    intro hz
    simp only [hz, div_zero, mul_zero, Complex.zero_re] at hp
    linarith [divisorSourceLogPhaseCoefficient_pos]
  have hpow : (2 : ℂ)^s = (r : ℂ) := two_cpow_at_period σ k
  rw [hpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  have hlog : d < (deriv divisorSourceEntire s / divisorSourceEntire s).re := by
    dsimp [d]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hnorm : t ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    simpa only [hsi, abs_of_pos ht] using h
  have hinv : (1/s).re < d := calc
    (1/s).re ≤ ‖(1 : ℂ)/s‖ := Complex.re_le_norm _
    _ = 1/‖s‖ := by rw [norm_div, norm_one]
    _ ≤ 1/t := one_div_le_one_div_of_le ht hnorm
    _ < d := (one_div_lt ht hd).mpr htd
  refine ⟨t, htT, hBn, ?_⟩
  change (1/s - deriv divisorSourceEntire s / divisorSourceEntire s).re < 0
  rw [Complex.sub_re]
  linarith

end RHTower
