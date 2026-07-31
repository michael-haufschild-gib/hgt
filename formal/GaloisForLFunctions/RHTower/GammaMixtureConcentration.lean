import GaloisForLFunctions.RHTower.SquaredXiChebyshevWindow

/-!
# Chebyshev concentration for the Gamma legs of the radial mixture

Each leg of the reverse-Bessel radial mixture is the unnormalized Gamma density
`t^j exp (-a t)` on `(0, infinity)`, with total mass `j!/a^(j+1)`, mean `(j+1)/a` and variance
`(j+1)/a^2`.  The exact second-moment identity

`∫_0^∞ (t - (j+1)/a)^2 t^j exp (-a t) dt = ((j+1)/a^2) * (j!/a^(j+1))`

gives Chebyshev's inequality for every measurable subset lying at distance at least `R` from the
mean, with a bound uniform in the leg index once `j` is bounded.  This is the conditional step of
the radial concentration law.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Total mass of the unnormalized Gamma leg. -/
theorem integral_gammaLeg {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-(a * t)) = (j.factorial : ℝ) / a ^ (j + 1) :=
  integral_pow_mul_exp_neg_mul_Ioi ha j

theorem integrableOn_sq_sub_mul_gammaLeg {a : ℝ} (ha : 0 < a) (j : ℕ) (c : ℝ) :
    IntegrableOn (fun t : ℝ => (t - c) ^ 2 * (t ^ j * Real.exp (-(a * t)))) (Ioi (0:ℝ)) := by
  have h0 := integrableOn_pow_mul_exp_neg_mul_Ioi ha j
  have h1 := integrableOn_pow_mul_exp_neg_mul_Ioi ha (j + 1)
  have h2 := integrableOn_pow_mul_exp_neg_mul_Ioi ha (j + 2)
  have hsum : IntegrableOn
      (fun t : ℝ => t ^ (j + 2) * Real.exp (-(a * t))
        + ((-(2 * c)) * (t ^ (j + 1) * Real.exp (-(a * t)))
          + (c ^ 2) * (t ^ j * Real.exp (-(a * t))))) (Ioi (0:ℝ)) :=
    h2.add ((h1.const_mul _).add (h0.const_mul _))
  refine MeasureTheory.IntegrableOn.congr_fun hsum ?_ measurableSet_Ioi
  intro t _
  ring

/-- **Exact second moment about the mean.**  The Gamma leg has variance `(j+1)/a^2` times its
total mass. -/
theorem integral_sq_sub_mean_gammaLeg {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ∫ t in Ioi (0:ℝ), (t - ((j : ℝ) + 1) / a) ^ 2 * (t ^ j * Real.exp (-(a * t)))
      = ((j : ℝ) + 1) / a ^ 2 * ((j.factorial : ℝ) / a ^ (j + 1)) := by
  have hane : a ≠ 0 := ne_of_gt ha
  set c : ℝ := ((j : ℝ) + 1) / a with hc
  set F2 : ℝ → ℝ := fun t : ℝ => t ^ (j + 2) * Real.exp (-(a * t)) with hF2
  set F1 : ℝ → ℝ := fun t : ℝ => (-(2 * c)) * (t ^ (j + 1) * Real.exp (-(a * t))) with hF1
  set F0 : ℝ → ℝ := fun t : ℝ => (c ^ 2) * (t ^ j * Real.exp (-(a * t))) with hF0
  have hI2 : IntegrableOn F2 (Ioi (0:ℝ)) := integrableOn_pow_mul_exp_neg_mul_Ioi ha (j + 2)
  have hI1 : IntegrableOn F1 (Ioi (0:ℝ)) :=
    (integrableOn_pow_mul_exp_neg_mul_Ioi ha (j + 1)).const_mul _
  have hI0 : IntegrableOn F0 (Ioi (0:ℝ)) :=
    (integrableOn_pow_mul_exp_neg_mul_Ioi ha j).const_mul _
  have hadd1 : ∫ t in Ioi (0:ℝ), (F1 t + F0 t)
      = (∫ t in Ioi (0:ℝ), F1 t) + ∫ t in Ioi (0:ℝ), F0 t := integral_add hI1 hI0
  have hadd2 : ∫ t in Ioi (0:ℝ), (F2 t + (F1 t + F0 t))
      = (∫ t in Ioi (0:ℝ), F2 t) + ∫ t in Ioi (0:ℝ), (F1 t + F0 t) :=
    integral_add hI2 (hI1.add hI0)
  have hv2 : ∫ t in Ioi (0:ℝ), F2 t = ((j + 2).factorial : ℝ) / a ^ (j + 2 + 1) :=
    integral_pow_mul_exp_neg_mul_Ioi ha (j + 2)
  have hv1 : ∫ t in Ioi (0:ℝ), F1 t
      = (-(2 * c)) * (((j + 1).factorial : ℝ) / a ^ (j + 1 + 1)) := by
    rw [hF1, integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi ha (j + 1)]
  have hv0 : ∫ t in Ioi (0:ℝ), F0 t = (c ^ 2) * ((j.factorial : ℝ) / a ^ (j + 1)) := by
    rw [hF0, integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi ha j]
  have hEq : ∫ t in Ioi (0:ℝ), (t - c) ^ 2 * (t ^ j * Real.exp (-(a * t)))
      = ∫ t in Ioi (0:ℝ), (F2 t + (F1 t + F0 t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [hF2, hF1, hF0]
    ring
  have hfac1 : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hfac2 : ((j + 2).factorial : ℝ) = ((j : ℝ) + 2) * (((j : ℝ) + 1) * (j.factorial : ℝ)) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hEq, hadd2, hadd1, hv2, hv1, hv0, hfac1, hfac2, hc]
  field_simp
  ring

/-- **Chebyshev's inequality for a Gamma leg.**  Any measurable subset of the positive ray lying at
distance at least `R` from the mean `(j+1)/a` carries at most `(j+1)/(a^2 R^2)` of the leg mass. -/
theorem gammaLeg_chebyshev {a : ℝ} (ha : 0 < a) (j : ℕ) {R : ℝ} (hR : 0 < R)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioi (0:ℝ))
    (hSfar : ∀ t ∈ S, R ≤ |t - ((j : ℝ) + 1) / a|) :
    ∫ t in S, t ^ j * Real.exp (-(a * t))
      ≤ ((j : ℝ) + 1) / (a ^ 2 * R ^ 2) * ((j.factorial : ℝ) / a ^ (j + 1)) := by
  set c : ℝ := ((j : ℝ) + 1) / a with hc
  set f : ℝ → ℝ := fun t => t ^ j * Real.exp (-(a * t)) with hf
  have hfnn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ f t := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have : (0:ℝ) ≤ t ^ j := by positivity
    have h2 : (0:ℝ) < Real.exp (-(a * t)) := Real.exp_pos _
    rw [hf]
    positivity
  have hint : IntegrableOn f (Ioi (0:ℝ)) := integrableOn_pow_mul_exp_neg_mul_Ioi ha j
  have hindic : IntegrableOn (S.indicator f) (Ioi (0:ℝ)) := hint.indicator hS
  have hmaj : IntegrableOn (fun t : ℝ => (t - c) ^ 2 / R ^ 2 * f t) (Ioi (0:ℝ)) := by
    have h := integrableOn_sq_sub_mul_gammaLeg ha j c
    have hcm := h.const_mul ((R ^ 2)⁻¹)
    refine MeasureTheory.IntegrableOn.congr_fun hcm ?_ measurableSet_Ioi
    intro t _
    rw [hf]
    field_simp
  have hsplit : ∫ t in S, f t = ∫ t in Ioi (0:ℝ), S.indicator f t := by
    rw [MeasureTheory.setIntegral_indicator hS, Set.inter_eq_self_of_subset_right hSsub]
  have hmono : ∫ t in Ioi (0:ℝ), S.indicator f t
      ≤ ∫ t in Ioi (0:ℝ), (t - c) ^ 2 / R ^ 2 * f t := by
    refine setIntegral_mono_on hindic hmaj measurableSet_Ioi (fun t ht => ?_)
    by_cases hmem : t ∈ S
    · rw [Set.indicator_of_mem hmem]
      have hfar : R ≤ |t - c| := hSfar t hmem
      have hsq : R ^ 2 ≤ (t - c) ^ 2 := by
        have habs : R ^ 2 ≤ |t - c| ^ 2 := by nlinarith [hR.le, abs_nonneg (t - c)]
        rwa [sq_abs] at habs
      have hone : (1:ℝ) ≤ (t - c) ^ 2 / R ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      nlinarith [hfnn t ht, hone]
    · rw [Set.indicator_of_notMem hmem]
      have hnn : (0:ℝ) ≤ (t - c) ^ 2 / R ^ 2 := by positivity
      exact mul_nonneg hnn (hfnn t ht)
  have hval : ∫ t in Ioi (0:ℝ), (t - c) ^ 2 / R ^ 2 * f t
      = ((j : ℝ) + 1) / (a ^ 2 * R ^ 2) * ((j.factorial : ℝ) / a ^ (j + 1)) := by
    have hcongr : ∫ t in Ioi (0:ℝ), (t - c) ^ 2 / R ^ 2 * f t
        = ∫ t in Ioi (0:ℝ), (R ^ 2)⁻¹ * ((t - c) ^ 2 * f t) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      field_simp
    rw [hcongr, integral_const_mul, hf, integral_sq_sub_mean_gammaLeg ha j]
    field_simp
  rw [hsplit]
  exact le_trans hmono (le_of_eq hval)

/-! ### Geometric decay of the mixture weights above the modal index -/

/-- The mixture ratio at relative index `theta`: `r theta = 2(1-theta) w / ((2-theta) a)`. -/
def radialMixtureRatio (s θ : ℝ) : ℝ :=
  2 * (1 - θ) * (s - 1 / 2) / ((2 - θ) * (s - 1))

theorem radialMixtureRatio_nonneg {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1) :
    0 ≤ radialMixtureRatio s θ := by
  have h1 : (0:ℝ) < s - 1 / 2 := by linarith
  have h2 : (0:ℝ) < s - 1 := by linarith
  have h3 : (0:ℝ) < 2 - θ := by linarith
  have h4 : (0:ℝ) ≤ 1 - θ := by linarith
  rw [radialMixtureRatio]
  positivity

/-- Above the modal ratio the fixed mixture ratio is strictly below one. -/
theorem radialMixtureRatio_lt_one {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1) (hθs : 1 < θ * s) :
    radialMixtureRatio s θ < 1 := by
  have h2 : (0:ℝ) < s - 1 := by linarith
  have h3 : (0:ℝ) < 2 - θ := by linarith
  have hden : (0:ℝ) < (2 - θ) * (s - 1) := mul_pos h3 h2
  rw [radialMixtureRatio, div_lt_one hden]
  nlinarith [hθs]

/-- **Uniform geometric ratio above a fixed relative index.**  Beyond `theta n` the adjacent
mixture ratio never exceeds `r theta`. -/
theorem radialMixtureWeight_succ_le {n j : ℕ} {s θ : ℝ} (hs : 1 < s)
    (hj : j < n) (hθ1 : θ ≤ 1) (hjθ : θ * (n : ℝ) ≤ (j : ℝ)) :
    radialMixtureWeight n s (j + 1) ≤ radialMixtureRatio s θ * radialMixtureWeight n s j := by
  have hw : (0:ℝ) < s - 1 / 2 := by linarith
  have ha : (0:ℝ) < s - 1 := by linarith
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  have hD : (0:ℝ) < 2 * (n : ℝ) - (j : ℝ) := by linarith
  have h3 : (0:ℝ) < 2 - θ := by linarith
  have hden : (0:ℝ) < (2 - θ) * (s - 1) := mul_pos h3 ha
  have hcj : 0 < radialMixtureWeight n s j := radialMixtureWeight_pos (le_of_lt hj) hs
  have hkey := radialMixtureWeight_adjacent hj hs
  have hDa : (0:ℝ) < (2 * (n : ℝ) - (j : ℝ)) * (s - 1) := mul_pos hD ha
  have hstep : radialMixtureWeight n s (j + 1) * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))
      = radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ))) * (s - 1 / 2) := by
    rw [← mul_assoc, hkey]
  have hcmp : ((n : ℝ) - (j : ℝ)) * (2 - θ) ≤ (1 - θ) * (2 * (n : ℝ) - (j : ℝ)) := by
    nlinarith [hjθ]
  rw [radialMixtureRatio, div_mul_eq_mul_div, le_div_iff₀ hden]
  refine le_of_mul_le_mul_right ?_ hDa
  have hposc : (0:ℝ) ≤ 2 * radialMixtureWeight n s j * (s - 1 / 2) * (s - 1) := by positivity
  calc radialMixtureWeight n s (j + 1) * ((2 - θ) * (s - 1)) *
        ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))
      = (radialMixtureWeight n s (j + 1) * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))) *
          ((2 - θ) * (s - 1)) := by ring
    _ = (radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ))) * (s - 1 / 2)) *
          ((2 - θ) * (s - 1)) := by rw [hstep]
    _ ≤ 2 * (1 - θ) * (s - 1 / 2) * radialMixtureWeight n s j *
          ((2 * (n : ℝ) - (j : ℝ)) * (s - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hcmp hposc]

/-- Iterated geometric decay above a fixed relative index. -/
theorem radialMixtureWeight_le_pow {n j₀ : ℕ} {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1)
    (hjθ : θ * (n : ℝ) ≤ (j₀ : ℝ)) :
    ∀ k : ℕ, j₀ + k ≤ n →
      radialMixtureWeight n s (j₀ + k)
        ≤ radialMixtureRatio s θ ^ k * radialMixtureWeight n s j₀ := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : j₀ + k ≤ n := by omega
      have hlt : j₀ + k < n := by omega
      have hstep : radialMixtureWeight n s (j₀ + k + 1)
          ≤ radialMixtureRatio s θ * radialMixtureWeight n s (j₀ + k) := by
        refine radialMixtureWeight_succ_le hs hlt hθ1 ?_
        have : (j₀ : ℝ) ≤ ((j₀ + k : ℕ) : ℝ) := by
          push_cast
          have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        linarith [hjθ]
      have hrn : 0 ≤ radialMixtureRatio s θ := radialMixtureRatio_nonneg hs hθ1
      calc radialMixtureWeight n s (j₀ + (k + 1))
          = radialMixtureWeight n s (j₀ + k + 1) := by ring_nf
        _ ≤ radialMixtureRatio s θ * radialMixtureWeight n s (j₀ + k) := hstep
        _ ≤ radialMixtureRatio s θ * (radialMixtureRatio s θ ^ k *
              radialMixtureWeight n s j₀) := by
            exact mul_le_mul_of_nonneg_left (ih hk') hrn
        _ = radialMixtureRatio s θ ^ (k + 1) * radialMixtureWeight n s j₀ := by ring

/-! ### Geometric growth below the modal index, and the tail sums -/

/-- **Uniform geometric ratio below a fixed relative index.**  Below `theta n` the adjacent mixture
ratio is at least `r theta`, which is above one when `theta s < 1`. -/
theorem radialMixtureWeight_le_succ {n j : ℕ} {s θ : ℝ} (hs : 1 < s)
    (hj : j < n) (hθ1 : θ ≤ 1) (hjθ : (j : ℝ) ≤ θ * (n : ℝ)) :
    radialMixtureRatio s θ * radialMixtureWeight n s j ≤ radialMixtureWeight n s (j + 1) := by
  have hw : (0:ℝ) < s - 1 / 2 := by linarith
  have ha : (0:ℝ) < s - 1 := by linarith
  have hjn : (j : ℝ) < (n : ℝ) := by exact_mod_cast hj
  have hD : (0:ℝ) < 2 * (n : ℝ) - (j : ℝ) := by linarith
  have h3 : (0:ℝ) < 2 - θ := by linarith
  have hden : (0:ℝ) < (2 - θ) * (s - 1) := mul_pos h3 ha
  have hcj : 0 < radialMixtureWeight n s j := radialMixtureWeight_pos (le_of_lt hj) hs
  have hkey := radialMixtureWeight_adjacent hj hs
  have hDa : (0:ℝ) < (2 * (n : ℝ) - (j : ℝ)) * (s - 1) := mul_pos hD ha
  have hstep : radialMixtureWeight n s (j + 1) * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))
      = radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ))) * (s - 1 / 2) := by
    rw [← mul_assoc, hkey]
  have hcmp : (1 - θ) * (2 * (n : ℝ) - (j : ℝ)) ≤ ((n : ℝ) - (j : ℝ)) * (2 - θ) := by
    nlinarith [hjθ]
  rw [radialMixtureRatio, div_mul_eq_mul_div, div_le_iff₀ hden]
  refine le_of_mul_le_mul_right ?_ hDa
  have hposc : (0:ℝ) ≤ 2 * radialMixtureWeight n s j * (s - 1 / 2) * (s - 1) := by positivity
  calc 2 * (1 - θ) * (s - 1 / 2) * radialMixtureWeight n s j *
        ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))
      ≤ (radialMixtureWeight n s j * (2 * ((n : ℝ) - (j : ℝ))) * (s - 1 / 2)) *
          ((2 - θ) * (s - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hcmp hposc]
    _ = (radialMixtureWeight n s (j + 1) * ((2 * (n : ℝ) - (j : ℝ)) * (s - 1))) *
          ((2 - θ) * (s - 1)) := by rw [hstep]
    _ = radialMixtureWeight n s (j + 1) * ((2 - θ) * (s - 1)) *
          ((2 * (n : ℝ) - (j : ℝ)) * (s - 1)) := by ring

/-- Iterated geometric growth below a fixed relative index. -/
theorem radialMixtureWeight_pow_le {n j₀ : ℕ} {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1) :
    ∀ k : ℕ, j₀ + k ≤ n → ((j₀ + k : ℕ) : ℝ) ≤ θ * (n : ℝ) →
      radialMixtureRatio s θ ^ k * radialMixtureWeight n s j₀
        ≤ radialMixtureWeight n s (j₀ + k) := by
  intro k
  induction k with
  | zero => intro _ _; simp
  | succ k ih =>
      intro hk hkθ
      have hk' : j₀ + k ≤ n := by omega
      have hlt : j₀ + k < n := by omega
      have hkθ' : ((j₀ + k : ℕ) : ℝ) ≤ θ * (n : ℝ) := by
        refine le_trans ?_ hkθ
        push_cast
        linarith
      have hstep : radialMixtureRatio s θ * radialMixtureWeight n s (j₀ + k)
          ≤ radialMixtureWeight n s (j₀ + k + 1) :=
        radialMixtureWeight_le_succ hs hlt hθ1 hkθ'
      have hrn : 0 ≤ radialMixtureRatio s θ := radialMixtureRatio_nonneg hs hθ1
      calc radialMixtureRatio s θ ^ (k + 1) * radialMixtureWeight n s j₀
          = radialMixtureRatio s θ * (radialMixtureRatio s θ ^ k *
              radialMixtureWeight n s j₀) := by ring
        _ ≤ radialMixtureRatio s θ * radialMixtureWeight n s (j₀ + k) :=
            mul_le_mul_of_nonneg_left (ih hk' hkθ') hrn
        _ ≤ radialMixtureWeight n s (j₀ + k + 1) := hstep
        _ = radialMixtureWeight n s (j₀ + (k + 1)) := by ring_nf

/-! ### The upper tail sum -/

theorem geomSum_range_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (K : ℕ) :
    ∑ k ∈ Finset.range K, ρ ^ k ≤ (1 - ρ)⁻¹ := by
  have hgeo := hasSum_geometric_of_lt_one hρ0 hρ1
  have hle := hgeo.summable.sum_le_tsum (Finset.range K) (fun k _ => pow_nonneg hρ0 k)
  rwa [hgeo.tsum_eq] at hle

/-- **The upper tail of the mixture is geometrically small.**  Above a fixed relative index beyond
the modal ratio, the whole tail sum is at most a fixed multiple of the first weight. -/
theorem sum_Icc_radialMixtureWeight_le {n j₀ : ℕ} {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1)
    (hθs : 1 < θ * s) (hjθ : θ * (n : ℝ) ≤ (j₀ : ℝ)) (hj₀ : j₀ ≤ n) :
    ∑ j ∈ Finset.Icc j₀ n, radialMixtureWeight n s j
      ≤ (1 - radialMixtureRatio s θ)⁻¹ * radialMixtureWeight n s j₀ := by
  have hrn : 0 ≤ radialMixtureRatio s θ := radialMixtureRatio_nonneg hs hθ1
  have hr1 : radialMixtureRatio s θ < 1 := radialMixtureRatio_lt_one hs hθ1 hθs
  have hcj : 0 < radialMixtureWeight n s j₀ := radialMixtureWeight_pos hj₀ hs
  have hIcc : Finset.Icc j₀ n = Finset.Ico j₀ (n + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hbound : ∀ k ∈ Finset.range (n + 1 - j₀),
      radialMixtureWeight n s (j₀ + k)
        ≤ radialMixtureRatio s θ ^ k * radialMixtureWeight n s j₀ := by
    intro k hk
    have hkn : j₀ + k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    exact radialMixtureWeight_le_pow hs hθ1 hjθ k hkn
  calc ∑ k ∈ Finset.range (n + 1 - j₀), radialMixtureWeight n s (j₀ + k)
      ≤ ∑ k ∈ Finset.range (n + 1 - j₀),
          radialMixtureRatio s θ ^ k * radialMixtureWeight n s j₀ :=
        Finset.sum_le_sum hbound
    _ = (∑ k ∈ Finset.range (n + 1 - j₀), radialMixtureRatio s θ ^ k) *
          radialMixtureWeight n s j₀ := by rw [Finset.sum_mul]
    _ ≤ (1 - radialMixtureRatio s θ)⁻¹ * radialMixtureWeight n s j₀ :=
        mul_le_mul_of_nonneg_right (geomSum_range_le hrn hr1 _) hcj.le

/-! ### The lower tail sum -/

theorem radialMixtureRatio_one_lt {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1) (hθs : θ * s < 1) :
    1 < radialMixtureRatio s θ := by
  have h2 : (0:ℝ) < s - 1 := by linarith
  have h3 : (0:ℝ) < 2 - θ := by linarith
  have hden : (0:ℝ) < (2 - θ) * (s - 1) := mul_pos h3 h2
  rw [radialMixtureRatio, lt_div_iff₀ hden]
  nlinarith [hθs]

/-- **The lower tail of the mixture is geometrically small.**  Below a fixed relative index under
the modal ratio, the whole tail sum is at most a fixed multiple of the last weight. -/
theorem sum_range_radialMixtureWeight_le {n j₁ : ℕ} {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1)
    (hθs : θ * s < 1) (hjθ : ((j₁ : ℕ) : ℝ) ≤ θ * (n : ℝ)) (hj₁ : j₁ ≤ n) :
    ∑ j ∈ Finset.range (j₁ + 1), radialMixtureWeight n s j
      ≤ (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ * radialMixtureWeight n s j₁ := by
  have hr1 : 1 < radialMixtureRatio s θ := radialMixtureRatio_one_lt hs hθ1 hθs
  have hrpos : 0 < radialMixtureRatio s θ := lt_trans zero_lt_one hr1
  have hinv0 : 0 ≤ (radialMixtureRatio s θ)⁻¹ := le_of_lt (inv_pos.mpr hrpos)
  have hinv1 : (radialMixtureRatio s θ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hcj : 0 < radialMixtureWeight n s j₁ := radialMixtureWeight_pos hj₁ hs
  have hbound : ∀ i ∈ Finset.range (j₁ + 1),
      radialMixtureWeight n s (j₁ + 1 - 1 - i)
        ≤ (radialMixtureRatio s θ)⁻¹ ^ i * radialMixtureWeight n s j₁ := by
    intro i hi
    have hij : i ≤ j₁ := by
      have := Finset.mem_range.mp hi
      omega
    have hsplit : j₁ - i + i = j₁ := by omega
    have hkey := radialMixtureWeight_pow_le (n := n) (j₀ := j₁ - i) hs hθ1 i
      (by omega) (by rw [hsplit]; exact hjθ)
    rw [hsplit] at hkey
    have hpow : 0 < radialMixtureRatio s θ ^ i := pow_pos hrpos i
    have hidx : j₁ + 1 - 1 - i = j₁ - i := by omega
    rw [hidx, inv_pow, ← div_eq_inv_mul, le_div_iff₀ hpow]
    linarith [hkey]
  calc ∑ j ∈ Finset.range (j₁ + 1), radialMixtureWeight n s j
      = ∑ i ∈ Finset.range (j₁ + 1), radialMixtureWeight n s (j₁ + 1 - 1 - i) :=
        (Finset.sum_range_reflect _ _).symm
    _ ≤ ∑ i ∈ Finset.range (j₁ + 1),
          (radialMixtureRatio s θ)⁻¹ ^ i * radialMixtureWeight n s j₁ :=
        Finset.sum_le_sum hbound
    _ = (∑ i ∈ Finset.range (j₁ + 1), (radialMixtureRatio s θ)⁻¹ ^ i) *
          radialMixtureWeight n s j₁ := by rw [Finset.sum_mul]
    _ ≤ (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ * radialMixtureWeight n s j₁ :=
        mul_le_mul_of_nonneg_right (geomSum_range_le hinv0 hinv1 _) hcj.le

/-! ### Comparison with the total mass -/

theorem radialMixtureWeight_nonneg (n : ℕ) {s : ℝ} (hs : 1 < s) (j : ℕ) :
    0 ≤ radialMixtureWeight n s j := by
  have hb : (0:ℝ) ≤ (squaredRadialJetWeight n j : ℝ) := Nat.cast_nonneg _
  have hf : (0:ℝ) ≤ (j.factorial : ℝ) := Nat.cast_nonneg _
  have hw : (0:ℝ) ≤ (s - 1 / 2) / (s - 1) := by
    apply div_nonneg <;> linarith
  rw [radialMixtureWeight]
  positivity

theorem radialMixtureWeight_le_total {n j : ℕ} {s : ℝ} (hs : 1 < s) (hj : j ≤ n) :
    radialMixtureWeight n s j
      ≤ ∑ i ∈ Finset.range (n + 1), radialMixtureWeight n s i :=
  Finset.single_le_sum (fun i _ => radialMixtureWeight_nonneg n hs i)
    (Finset.mem_range.mpr (by omega))

/-- **Upper index tail against the total mass.**  Above a comparison index `jm` beyond the modal
ratio, the whole upper tail is a geometric fraction of the total mixture mass, with a rate
depending only on `s` and the relative offset. -/
theorem sum_Icc_radialMixtureWeight_le_total {n jm j₀ : ℕ} {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1)
    (hθs : 1 < θ * s) (hjθ : θ * (n : ℝ) ≤ (jm : ℝ)) (hjj : jm ≤ j₀) (hj₀ : j₀ ≤ n) :
    ∑ j ∈ Finset.Icc j₀ n, radialMixtureWeight n s j
      ≤ (1 - radialMixtureRatio s θ)⁻¹ * radialMixtureRatio s θ ^ (j₀ - jm) *
        ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j := by
  have hjmn : jm ≤ n := le_trans hjj hj₀
  have hrn : 0 ≤ radialMixtureRatio s θ := radialMixtureRatio_nonneg hs hθ1
  have hr1 : radialMixtureRatio s θ < 1 := radialMixtureRatio_lt_one hs hθ1 hθs
  have hC : (0:ℝ) ≤ (1 - radialMixtureRatio s θ)⁻¹ := by
    have hpos : (0:ℝ) < 1 - radialMixtureRatio s θ := by linarith
    positivity
  have hjθ0 : θ * (n : ℝ) ≤ (j₀ : ℝ) := by
    refine le_trans hjθ ?_
    exact_mod_cast hjj
  have h1 := sum_Icc_radialMixtureWeight_le hs hθ1 hθs hjθ0 hj₀
  have hk : jm + (j₀ - jm) = j₀ := by omega
  have h2 := radialMixtureWeight_le_pow hs hθ1 hjθ (j₀ - jm) (by omega)
  rw [hk] at h2
  have h3 := radialMixtureWeight_le_total hs hjmn
  have hpow : (0:ℝ) ≤ radialMixtureRatio s θ ^ (j₀ - jm) := pow_nonneg hrn _
  calc ∑ j ∈ Finset.Icc j₀ n, radialMixtureWeight n s j
      ≤ (1 - radialMixtureRatio s θ)⁻¹ * radialMixtureWeight n s j₀ := h1
    _ ≤ (1 - radialMixtureRatio s θ)⁻¹ *
          (radialMixtureRatio s θ ^ (j₀ - jm) * radialMixtureWeight n s jm) :=
        mul_le_mul_of_nonneg_left h2 hC
    _ ≤ (1 - radialMixtureRatio s θ)⁻¹ *
          (radialMixtureRatio s θ ^ (j₀ - jm) *
            ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact mul_le_mul_of_nonneg_left h3 hpow
    _ = (1 - radialMixtureRatio s θ)⁻¹ * radialMixtureRatio s θ ^ (j₀ - jm) *
          ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j := by ring

/-- **Lower index tail against the total mass.**  Below a comparison index `jm` under the modal
ratio, the whole lower tail is a geometric fraction of the total mixture mass. -/
theorem sum_range_radialMixtureWeight_le_total {n j₁ jm : ℕ} {s θ : ℝ} (hs : 1 < s) (hθ1 : θ ≤ 1)
    (hθs : θ * s < 1) (hjθ : (jm : ℝ) ≤ θ * (n : ℝ)) (hjj : j₁ ≤ jm) (hjm : jm ≤ n) :
    ∑ j ∈ Finset.range (j₁ + 1), radialMixtureWeight n s j
      ≤ (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ * (radialMixtureRatio s θ)⁻¹ ^ (jm - j₁) *
        ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j := by
  have hr1 : 1 < radialMixtureRatio s θ := radialMixtureRatio_one_lt hs hθ1 hθs
  have hrpos : 0 < radialMixtureRatio s θ := lt_trans zero_lt_one hr1
  have hinv0 : (0:ℝ) ≤ (radialMixtureRatio s θ)⁻¹ := le_of_lt (inv_pos.mpr hrpos)
  have hinv1 : (radialMixtureRatio s θ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hC : (0:ℝ) ≤ (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ := by
    have hpos : (0:ℝ) < 1 - (radialMixtureRatio s θ)⁻¹ := by linarith
    positivity
  have hj₁n : j₁ ≤ n := le_trans hjj hjm
  have hj₁θ : ((j₁ : ℕ) : ℝ) ≤ θ * (n : ℝ) := by
    refine le_trans ?_ hjθ
    exact_mod_cast hjj
  have h1 := sum_range_radialMixtureWeight_le hs hθ1 hθs hj₁θ hj₁n
  have hk : j₁ + (jm - j₁) = jm := by omega
  have h2 := radialMixtureWeight_pow_le (n := n) (j₀ := j₁) hs hθ1 (jm - j₁)
    (by omega) (by rw [hk]; exact hjθ)
  rw [hk] at h2
  have hpowpos : (0:ℝ) < radialMixtureRatio s θ ^ (jm - j₁) := pow_pos hrpos _
  have h2' : radialMixtureWeight n s j₁
      ≤ (radialMixtureRatio s θ)⁻¹ ^ (jm - j₁) * radialMixtureWeight n s jm := by
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ hpowpos]
    linarith [h2]
  have h3 := radialMixtureWeight_le_total hs hjm
  have hpow : (0:ℝ) ≤ (radialMixtureRatio s θ)⁻¹ ^ (jm - j₁) := pow_nonneg hinv0 _
  calc ∑ j ∈ Finset.range (j₁ + 1), radialMixtureWeight n s j
      ≤ (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ * radialMixtureWeight n s j₁ := h1
    _ ≤ (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ *
          ((radialMixtureRatio s θ)⁻¹ ^ (jm - j₁) * radialMixtureWeight n s jm) :=
        mul_le_mul_of_nonneg_left h2' hC
    _ ≤ (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ *
          ((radialMixtureRatio s θ)⁻¹ ^ (jm - j₁) *
            ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        exact mul_le_mul_of_nonneg_left h3 hpow
    _ = (1 - (radialMixtureRatio s θ)⁻¹)⁻¹ * (radialMixtureRatio s θ)⁻¹ ^ (jm - j₁) *
          ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j := by ring

/-! ### The index tails vanish -/

theorem tendsto_pow_of_tendsto_atTop {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {k : ℕ → ℕ} (hk : Filter.Tendsto k Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n => ρ ^ k n) Filter.atTop (nhds 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp hk

theorem tendsto_ceil_sub_ceil_atTop {θ θ' : ℝ} (hθ'0 : 0 ≤ θ') (hlt : θ' < θ) :
    Filter.Tendsto (fun n : ℕ => ⌈θ * (n : ℝ)⌉₊ - ⌈θ' * (n : ℝ)⌉₊)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr (fun m => ?_)
  have hd : (0:ℝ) < θ - θ' := by linarith
  have hlin : Filter.Tendsto (fun n : ℕ => (θ - θ') * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hd tendsto_natCast_atTop_atTop
  filter_upwards [hlin.eventually_ge_atTop ((m : ℝ) + 1)] with n hn
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hce2 : ((⌈θ' * (n : ℝ)⌉₊ : ℕ) : ℝ) < θ' * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hθ'0 hn0)
  have hce3 : θ * (n : ℝ) ≤ ((⌈θ * (n : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hkey : ((⌈θ' * (n : ℝ)⌉₊ : ℕ) : ℝ) + (m : ℝ) ≤ ((⌈θ * (n : ℝ)⌉₊ : ℕ) : ℝ) := by
    nlinarith [hn, hce2, hce3]
  have hnat : ⌈θ' * (n : ℝ)⌉₊ + m ≤ ⌈θ * (n : ℝ)⌉₊ := by exact_mod_cast hkey
  omega

theorem tendsto_floor_sub_floor_atTop {θ θ' : ℝ} (hθ0 : 0 ≤ θ) (hlt : θ < θ') :
    Filter.Tendsto (fun n : ℕ => ⌊θ' * (n : ℝ)⌋₊ - ⌊θ * (n : ℝ)⌋₊)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.mpr (fun m => ?_)
  have hd : (0:ℝ) < θ' - θ := by linarith
  have hlin : Filter.Tendsto (fun n : ℕ => (θ' - θ) * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hd tendsto_natCast_atTop_atTop
  filter_upwards [hlin.eventually_ge_atTop ((m : ℝ) + 1)] with n hn
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfl1 : ((⌊θ * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ θ * (n : ℝ) := Nat.floor_le (mul_nonneg hθ0 hn0)
  have hfl2 : θ' * (n : ℝ) - 1 < ((⌊θ' * (n : ℝ)⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
  have hkey : ((⌊θ * (n : ℝ)⌋₊ : ℕ) : ℝ) + (m : ℝ) ≤ ((⌊θ' * (n : ℝ)⌋₊ : ℕ) : ℝ) := by
    nlinarith [hn, hfl1, hfl2]
  have hnat : ⌊θ * (n : ℝ)⌋₊ + m ≤ ⌊θ' * (n : ℝ)⌋₊ := by exact_mod_cast hkey
  omega

/-- **The upper index tail is a vanishing fraction of the total mixture mass.** -/
theorem tendsto_upper_tail_fraction {s θ θ' : ℝ} (hs : 1 < s) (hθ'0 : 0 ≤ θ') (hθ'1 : θ' ≤ 1)
    (hθ's : 1 < θ' * s) (hlt : θ' < θ) (hθ1 : θ ≤ 1) :
    Filter.Tendsto (fun n : ℕ =>
        (∑ j ∈ Finset.Icc ⌈θ * (n : ℝ)⌉₊ n, radialMixtureWeight n s j) /
          ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j)
      Filter.atTop (nhds 0) := by
  have hrn : 0 ≤ radialMixtureRatio s θ' := radialMixtureRatio_nonneg hs hθ'1
  have hr1 : radialMixtureRatio s θ' < 1 := radialMixtureRatio_lt_one hs hθ'1 hθ's
  have hCpos : (0:ℝ) < (1 - radialMixtureRatio s θ')⁻¹ := by
    have hpos : (0:ℝ) < 1 - radialMixtureRatio s θ' := by linarith
    positivity
  have hmaj : Filter.Tendsto (fun n : ℕ =>
      (1 - radialMixtureRatio s θ')⁻¹ *
        radialMixtureRatio s θ' ^ (⌈θ * (n : ℝ)⌉₊ - ⌈θ' * (n : ℝ)⌉₊))
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_of_tendsto_atTop hrn hr1 (tendsto_ceil_sub_ceil_atTop hθ'0 hlt)
    simpa using h.const_mul ((1 - radialMixtureRatio s θ')⁻¹)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmaj
  · have hden : 0 < ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j :=
      lt_of_lt_of_le (radialMixtureWeight_pos (Nat.zero_le n) hs)
        (radialMixtureWeight_le_total hs (Nat.zero_le n))
    refine div_nonneg (Finset.sum_nonneg (fun j _ => radialMixtureWeight_nonneg n hs j)) hden.le
  · have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j :=
      lt_of_lt_of_le (radialMixtureWeight_pos (Nat.zero_le n) hs)
        (radialMixtureWeight_le_total hs (Nat.zero_le n))
    have hcn : ⌈θ * (n : ℝ)⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
    have hbound := sum_Icc_radialMixtureWeight_le_total (n := n) (jm := ⌈θ' * (n : ℝ)⌉₊)
      (j₀ := ⌈θ * (n : ℝ)⌉₊) hs hθ'1 hθ's (Nat.le_ceil _)
      (Nat.ceil_le_ceil (by nlinarith)) hcn
    rw [div_le_iff₀ hden]
    exact hbound

/-- **The lower index tail is a vanishing fraction of the total mixture mass.** -/
theorem tendsto_lower_tail_fraction {s θ θ' : ℝ} (hs : 1 < s) (hθ0 : 0 ≤ θ) (hθ'1 : θ' ≤ 1)
    (hθ's : θ' * s < 1) (hlt : θ < θ') :
    Filter.Tendsto (fun n : ℕ =>
        (∑ j ∈ Finset.range (⌊θ * (n : ℝ)⌋₊ + 1), radialMixtureWeight n s j) /
          ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j)
      Filter.atTop (nhds 0) := by
  have hr1 : 1 < radialMixtureRatio s θ' := radialMixtureRatio_one_lt hs hθ'1 hθ's
  have hrpos : 0 < radialMixtureRatio s θ' := lt_trans zero_lt_one hr1
  have hinv0 : (0:ℝ) ≤ (radialMixtureRatio s θ')⁻¹ := le_of_lt (inv_pos.mpr hrpos)
  have hinv1 : (radialMixtureRatio s θ')⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hmaj : Filter.Tendsto (fun n : ℕ =>
      (1 - (radialMixtureRatio s θ')⁻¹)⁻¹ *
        (radialMixtureRatio s θ')⁻¹ ^ (⌊θ' * (n : ℝ)⌋₊ - ⌊θ * (n : ℝ)⌋₊))
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_of_tendsto_atTop hinv0 hinv1 (tendsto_floor_sub_floor_atTop hθ0 hlt)
    simpa using h.const_mul ((1 - (radialMixtureRatio s θ')⁻¹)⁻¹)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hmaj
  · have hden : 0 < ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j :=
      lt_of_lt_of_le (radialMixtureWeight_pos (Nat.zero_le n) hs)
        (radialMixtureWeight_le_total hs (Nat.zero_le n))
    refine div_nonneg (Finset.sum_nonneg (fun j _ => radialMixtureWeight_nonneg n hs j)) hden.le
  · have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : 0 < ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j :=
      lt_of_lt_of_le (radialMixtureWeight_pos (Nat.zero_le n) hs)
        (radialMixtureWeight_le_total hs (Nat.zero_le n))
    have hfn : ⌊θ' * (n : ℝ)⌋₊ ≤ n := by
      have h1 : θ' * (n : ℝ) ≤ (n : ℝ) := by nlinarith
      calc ⌊θ' * (n : ℝ)⌋₊ ≤ ⌊(n : ℝ)⌋₊ := Nat.floor_le_floor h1
        _ = n := Nat.floor_natCast n
    have hbound := sum_range_radialMixtureWeight_le_total (n := n) (j₁ := ⌊θ * (n : ℝ)⌋₊)
      (jm := ⌊θ' * (n : ℝ)⌋₊) hs hθ'1 hθ's (Nat.floor_le (mul_nonneg (by linarith) hn0))
      (Nat.floor_le_floor (by nlinarith)) hfn
    rw [div_le_iff₀ hden]
    exact hbound

/-! ### The radial mixture density and its leg decomposition -/

/-- The unnormalized radial density `e^{-a t} B_n(w t)` of the reverse-Bessel mixture, written as
a finite sum of Gamma legs. -/
def radialMixtureDensity (n : ℕ) (s t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
      (t ^ j * Real.exp (-((s - 1) * t)))

theorem integrableOn_radialMixtureLeg {n : ℕ} {s : ℝ} (hs : 1 < s) (j : ℕ) :
    IntegrableOn (fun t : ℝ =>
        ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          (t ^ j * Real.exp (-((s - 1) * t)))) (Ioi (0:ℝ)) :=
  (integrableOn_pow_mul_exp_neg_mul_Ioi (by linarith : (0:ℝ) < s - 1) j).const_mul _

/-- **Leg decomposition.**  On any measurable subset of the positive ray the mixture integral is the
finite sum of the leg integrals. -/
theorem integral_radialMixtureDensity_eq {n : ℕ} {s : ℝ} (hs : 1 < s)
    {S : Set ℝ} (_hS : MeasurableSet S) (hSsub : S ⊆ Ioi (0:ℝ)) :
    ∫ t in S, radialMixtureDensity n s t
      = ∑ j ∈ Finset.range (n + 1),
          ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
            ∫ t in S, t ^ j * Real.exp (-((s - 1) * t)) := by
  have hleg : ∀ j ∈ Finset.range (n + 1),
      Integrable (fun t : ℝ =>
        ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          (t ^ j * Real.exp (-((s - 1) * t)))) (volume.restrict S) :=
    fun j _ => (integrableOn_radialMixtureLeg hs j).mono_set hSsub
  simp only [radialMixtureDensity]
  rw [MeasureTheory.integral_finsetSum _ hleg]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_const_mul]

/-- **Total mixture mass.**  The mass of the radial density is the mixture-weight sum, scaled by
`1/a`. -/
theorem integral_radialMixtureDensity_Ioi {n : ℕ} {s : ℝ} (hs : 1 < s) :
    ∫ t in Ioi (0:ℝ), radialMixtureDensity n s t
      = (s - 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j := by
  have ha : (0:ℝ) < s - 1 := by linarith
  have hane : (s : ℝ) - 1 ≠ 0 := ne_of_gt ha
  rw [integral_radialMixtureDensity_eq hs measurableSet_Ioi (subset_refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_pow_mul_exp_neg_mul_Ioi ha j, radialMixtureWeight, div_pow]
  field_simp
  ring

theorem radialMixtureDensity_nonneg {n : ℕ} {s : ℝ} (hs : 1 < s) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ radialMixtureDensity n s t := by
  have hw : (0:ℝ) ≤ s - 1 / 2 := by linarith
  rw [radialMixtureDensity]
  refine Finset.sum_nonneg (fun j _ => ?_)
  have hb : (0:ℝ) ≤ (squaredRadialJetWeight n j : ℝ) := Nat.cast_nonneg _
  have h1 : (0:ℝ) ≤ (s - 1 / 2) ^ j := pow_nonneg hw j
  have h2 : (0:ℝ) ≤ t ^ j := pow_nonneg ht j
  have h3 : (0:ℝ) ≤ Real.exp (-((s - 1) * t)) := (Real.exp_pos _).le
  exact mul_nonneg (mul_nonneg hb h1) (mul_nonneg h2 h3)

/-- **Bad-index legs are bounded by their whole mass.**  Over any subset of the positive ray the
mixture integral restricted to a set of leg indices is at most that part of the total mass. -/
theorem integral_radialMixtureLeg_le {n : ℕ} {s : ℝ} (hs : 1 < s) (j : ℕ)
    {S : Set ℝ} (_hS : MeasurableSet S) (hSsub : S ⊆ Ioi (0:ℝ)) :
    ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
        ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ (s - 1)⁻¹ * radialMixtureWeight n s j := by
  have ha : (0:ℝ) < s - 1 := by linarith
  have hane : (s : ℝ) - 1 ≠ 0 := ne_of_gt ha
  have hcoef : (0:ℝ) ≤ (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j := by
    have hb : (0:ℝ) ≤ (squaredRadialJetWeight n j : ℝ) := Nat.cast_nonneg _
    have h1 : (0:ℝ) ≤ (s - 1 / 2) ^ j := pow_nonneg (by linarith) j
    exact mul_nonneg hb h1
  have hnn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ t ^ j * Real.exp (-((s - 1) * t)) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have h1 : (0:ℝ) ≤ t ^ j := pow_nonneg ht0.le j
    have h2 : (0:ℝ) ≤ Real.exp (-((s - 1) * t)) := (Real.exp_pos _).le
    exact mul_nonneg h1 h2
  have hle : ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-((s - 1) * t)) := by
    refine setIntegral_mono_set (integrableOn_pow_mul_exp_neg_mul_Ioi ha j) ?_
      (Filter.Eventually.of_forall hSsub)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht using hnn t ht
  have hval : ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-((s - 1) * t))
      = (j.factorial : ℝ) / (s - 1) ^ (j + 1) := integral_pow_mul_exp_neg_mul_Ioi ha j
  have hfin : ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
      ((j.factorial : ℝ) / (s - 1) ^ (j + 1)) = (s - 1)⁻¹ * radialMixtureWeight n s j := by
    rw [radialMixtureWeight, div_pow]
    field_simp
    ring
  calc ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
        ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          ∫ t in Ioi (0:ℝ), t ^ j * Real.exp (-((s - 1) * t)) :=
        mul_le_mul_of_nonneg_left hle hcoef
    _ = (s - 1)⁻¹ * radialMixtureWeight n s j := by rw [hval, hfin]

/-! ### The good-leg bound and the block split -/

theorem radialMixtureLeg_mass {n : ℕ} {s : ℝ} (hs : 1 < s) (j : ℕ) :
    ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
        ((j.factorial : ℝ) / (s - 1) ^ (j + 1))
      = (s - 1)⁻¹ * radialMixtureWeight n s j := by
  have hane : (s : ℝ) - 1 ≠ 0 := by intro h; linarith
  rw [radialMixtureWeight, div_pow]
  field_simp
  ring

/-- **Good-leg bound.**  A leg whose mean stays at distance `R` from the set contributes at most a
`(n+1)/(a^2 R^2)` fraction of its own mass. -/
theorem integral_radialMixtureLeg_good_le {n : ℕ} {s R : ℝ} (hs : 1 < s) (hR : 0 < R) (j : ℕ)
    (hjn : j ≤ n) {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioi (0:ℝ))
    (hfar : ∀ t ∈ S, R ≤ |t - ((j : ℝ) + 1) / (s - 1)|) :
    ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
        ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) * ((s - 1)⁻¹ * radialMixtureWeight n s j) := by
  have ha : (0:ℝ) < s - 1 := by linarith
  have hcoef : (0:ℝ) ≤ (squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j := by
    have hb : (0:ℝ) ≤ (squaredRadialJetWeight n j : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg hb (pow_nonneg (by linarith) j)
  have hcheb := gammaLeg_chebyshev ha j hR hS hSsub hfar
  have hjr : ((j : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
    have : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    linarith
  have hmass : (0:ℝ) ≤ (j.factorial : ℝ) / (s - 1) ^ (j + 1) := by positivity
  have hden : (0:ℝ) < (s - 1) ^ 2 * R ^ 2 := by positivity
  have hstep : ((j : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) * ((j.factorial : ℝ) / (s - 1) ^ (j + 1))
      ≤ ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) * ((j.factorial : ℝ) / (s - 1) ^ (j + 1)) := by
    refine mul_le_mul_of_nonneg_right ?_ hmass
    gcongr
  calc ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
        ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          (((j : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) *
            ((j.factorial : ℝ) / (s - 1) ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left hcheb hcoef
    _ ≤ ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          (((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) *
            ((j.factorial : ℝ) / (s - 1) ^ (j + 1))) :=
        mul_le_mul_of_nonneg_left hstep hcoef
    _ = ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) *
          (((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
            ((j.factorial : ℝ) / (s - 1) ^ (j + 1))) := by ring
    _ = ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) * ((s - 1)⁻¹ * radialMixtureWeight n s j) := by
        rw [radialMixtureLeg_mass hs j]

/-- **Block split of the radial mixture mass on a far set.**  The two outer index blocks are
bounded by their whole mass, the middle block by Chebyshev. -/
theorem integral_radialMixtureDensity_le_blocks {n : ℕ} {s R : ℝ} (hs : 1 < s) (hR : 0 < R)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioi (0:ℝ))
    {j₁ j₀ : ℕ} (hj₁ : j₁ + 1 ≤ j₀) (hj₀ : j₀ ≤ n + 1) (hj₁n : j₁ + 1 ≤ n + 1)
    (hgood : ∀ j, j₁ < j → j < j₀ → ∀ t ∈ S, R ≤ |t - ((j : ℝ) + 1) / (s - 1)|) :
    ∫ t in S, radialMixtureDensity n s t
      ≤ (s - 1)⁻¹ *
          (∑ j ∈ Finset.range (j₁ + 1), radialMixtureWeight n s j
            + ∑ j ∈ Finset.Icc j₀ n, radialMixtureWeight n s j)
        + ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) *
            ((s - 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j) := by
  have ha : (0:ℝ) < s - 1 := by linarith
  have hainv : (0:ℝ) ≤ (s - 1)⁻¹ := le_of_lt (inv_pos.mpr ha)
  have hIcc : Finset.Icc j₀ n = Finset.Ico j₀ (n + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsplit : ∑ j ∈ Finset.range (n + 1),
        ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      = (∑ j ∈ Finset.range (j₁ + 1),
            ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
              ∫ t in S, t ^ j * Real.exp (-((s - 1) * t)))
        + (∑ j ∈ Finset.Ico (j₁ + 1) j₀,
            ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
              ∫ t in S, t ^ j * Real.exp (-((s - 1) * t)))
        + ∑ j ∈ Finset.Icc j₀ n,
            ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
              ∫ t in S, t ^ j * Real.exp (-((s - 1) * t)) := by
    rw [hIcc, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (j₁ + 1)) hj₁n,
      ← Finset.sum_Ico_consecutive _ hj₁ hj₀]
    ring
  have hlow : ∑ j ∈ Finset.range (j₁ + 1),
        ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ ∑ j ∈ Finset.range (j₁ + 1), (s - 1)⁻¹ * radialMixtureWeight n s j :=
    Finset.sum_le_sum (fun j _ => integral_radialMixtureLeg_le hs j hS hSsub)
  have hhigh : ∑ j ∈ Finset.Icc j₀ n,
        ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ ∑ j ∈ Finset.Icc j₀ n, (s - 1)⁻¹ * radialMixtureWeight n s j :=
    Finset.sum_le_sum (fun j _ => integral_radialMixtureLeg_le hs j hS hSsub)
  have hmid : ∑ j ∈ Finset.Ico (j₁ + 1) j₀,
        ((squaredRadialJetWeight n j : ℝ) * (s - 1 / 2) ^ j) *
          ∫ t in S, t ^ j * Real.exp (-((s - 1) * t))
      ≤ ∑ j ∈ Finset.Ico (j₁ + 1) j₀,
          ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) * ((s - 1)⁻¹ * radialMixtureWeight n s j) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
    refine integral_radialMixtureLeg_good_le hs hR j (by omega) hS hSsub ?_
    exact hgood j (by omega) h2
  have hmid' : ∑ j ∈ Finset.Ico (j₁ + 1) j₀,
        ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) * ((s - 1)⁻¹ * radialMixtureWeight n s j)
      ≤ ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) *
          ((s - 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j) := by
    have hfac : (0:ℝ) ≤ ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) := by positivity
    have hsub : Finset.Ico (j₁ + 1) j₀ ⊆ Finset.range (n + 1) := by
      intro m hm
      obtain ⟨_, h2⟩ := Finset.mem_Ico.mp hm
      exact Finset.mem_range.mpr (by omega)
    have hpart : ∑ j ∈ Finset.Ico (j₁ + 1) j₀, radialMixtureWeight n s j
        ≤ ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i _ _ => radialMixtureWeight_nonneg n hs i)
    calc ∑ j ∈ Finset.Ico (j₁ + 1) j₀,
          ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) * ((s - 1)⁻¹ * radialMixtureWeight n s j)
        = ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) *
            ((s - 1)⁻¹ * ∑ j ∈ Finset.Ico (j₁ + 1) j₀, radialMixtureWeight n s j) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ ((n : ℝ) + 1) / ((s - 1) ^ 2 * R ^ 2) *
            ((s - 1)⁻¹ * ∑ j ∈ Finset.range (n + 1), radialMixtureWeight n s j) := by
          refine mul_le_mul_of_nonneg_left ?_ hfac
          exact mul_le_mul_of_nonneg_left hpart hainv
  rw [integral_radialMixtureDensity_eq hs hS hSsub, hsplit]
  have hcollect : ∑ j ∈ Finset.range (j₁ + 1), (s - 1)⁻¹ * radialMixtureWeight n s j
      + ∑ j ∈ Finset.Icc j₀ n, (s - 1)⁻¹ * radialMixtureWeight n s j
      = (s - 1)⁻¹ * (∑ j ∈ Finset.range (j₁ + 1), radialMixtureWeight n s j
          + ∑ j ∈ Finset.Icc j₀ n, radialMixtureWeight n s j) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  linarith [hlow, hmid, hmid', hhigh, hcollect]

end

end RHTower
