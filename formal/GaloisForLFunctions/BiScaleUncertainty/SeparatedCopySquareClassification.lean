import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarTopology

/-!
# Exact squared-correlation ambiguity of separated copies

Compactness supplies the separation scale. Squared normalized correlations
determine exactly the magnitude of the mixing coefficient; one signed sample
recovers the complete signed profile. The zero source is included explicitly.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty.SeparatedSquare
set_option autoImplicit false

def radius (f : C_c(ℝ, ℝ)) : ℝ :=
  (exists_pos_autocorr_support_radius f.hasCompactSupport).choose

theorem radius_pos (f : C_c(ℝ, ℝ)) : 0 < radius f :=
  (exists_pos_autocorr_support_radius f.hasCompactSupport).choose_spec.1

private theorem outside (f : C_c(ℝ, ℝ)) {x : ℝ} (hx : radius f < |x|) :
    autocorr f x = 0 :=
  (exists_pos_autocorr_support_radius f.hasCompactSupport).choose_spec.2 x hx

def gap (f : C_c(ℝ, ℝ)) : ℝ := 2 * radius f + 1

theorem twice_radius_lt_gap (f : C_c(ℝ, ℝ)) : 2 * radius f < gap f := by
  dsimp [gap]
  linarith

theorem radius_lt_gap (f : C_c(ℝ, ℝ)) : radius f < gap f := by
  linarith only [radius_pos f, twice_radius_lt_gap f]

def source (f : C_c(ℝ, ℝ)) (a : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨subtractCopy f a (gap f), continuous_subtractCopy f.continuous a (gap f)⟩,
    hasCompactSupport_subtractCopy f.hasCompactSupport a (gap f)⟩

theorem source_mass (f : C_c(ℝ, ℝ)) (a : ℝ) :
    autocorr (source f a) 0 = (1 + a ^ 2) * autocorr f 0 :=
  autocorr_subtractCopy_zero f.continuous f.hasCompactSupport
    (fun _ hx => outside f hx) (radius_lt_gap f) a

theorem source_center (f : C_c(ℝ, ℝ)) (a : ℝ) :
    autocorr (source f a) (gap f) = -a * autocorr f 0 := by
  have ht := radius_lt_gap f
  have hD := radius_pos f
  change autocorr (subtractCopy f a (gap f)) (gap f) = _
  rw [autocorr_subtractCopy f.continuous f.hasCompactSupport,
    outside f (ht.trans_le (le_abs_self _)), sub_self,
    outside f (lt_of_lt_of_le (by linarith : radius f < gap f + gap f) (le_abs_self _))]
  ring

private theorem packet_products (f : C_c(ℝ, ℝ)) (x : ℝ) :
    autocorr f x * autocorr f (x - gap f) = 0 ∧
    autocorr f x * autocorr f (x + gap f) = 0 ∧
    autocorr f (x - gap f) * autocorr f (x + gap f) = 0 := by
  have hT := twice_radius_lt_gap f
  have hD := radius_pos f
  have hcentral : autocorr f x = 0 ∨
      (autocorr f (x - gap f) = 0 ∧ autocorr f (x + gap f) = 0) := by
    by_cases hx : radius f < |x|
    · exact Or.inl (outside f hx)
    · have hb := abs_le.mp (le_of_not_gt hx)
      exact Or.inr ⟨outside f (lt_of_lt_of_le (by linarith : radius f < -(x - gap f))
        (neg_le_abs _)), outside f (lt_of_lt_of_le (by linarith : radius f < x + gap f)
        (le_abs_self _))⟩
  have hside : autocorr f (x - gap f) * autocorr f (x + gap f) = 0 := by
    by_cases hx : radius f < |x - gap f|
    · rw [outside f hx, zero_mul]
    · have hb := (abs_le.mp (le_of_not_gt hx)).1
      rw [outside f (lt_of_lt_of_le (by linarith : radius f < x + gap f) (le_abs_self _)), mul_zero]
  rcases hcentral with hz | ⟨hl, hr⟩
  · simp only [hz, zero_mul, true_and]
    exact hside
  · simp only [hl, hr, mul_zero, true_and]

/-- All three correlation packets have disjoint supports, including their nodal boundaries. -/
theorem source_square (f : C_c(ℝ, ℝ)) (a x : ℝ) :
    autocorr (source f a) x ^ 2 = (1 + a ^ 2) ^ 2 * autocorr f x ^ 2 +
      a ^ 2 * (autocorr f (x - gap f) ^ 2 + autocorr f (x + gap f) ^ 2) := by
  change autocorr (subtractCopy f a (gap f)) x ^ 2 = _
  rw [autocorr_subtractCopy f.continuous f.hasCompactSupport]
  obtain ⟨hl, hr, hs⟩ := packet_products f x
  calc
    _ = (1+a^2)^2*autocorr f x^2 +
        a^2*(autocorr f (x-gap f)^2+autocorr f (x+gap f)^2) -
        2*a*(1+a^2)*(autocorr f x*autocorr f (x-gap f)) -
        2*a*(1+a^2)*(autocorr f x*autocorr f (x+gap f)) +
        2*a^2*(autocorr f (x-gap f)*autocorr f (x+gap f)) := by ring
    _ = _ := by rw [hl, hr, hs]; ring

theorem source_square_neg (f : C_c(ℝ, ℝ)) (a x : ℝ) :
    autocorr (source f (-a)) x ^ 2 = autocorr (source f a) x ^ 2 := by
  simp only [source_square, neg_sq]

theorem source_zero_iff_neg (f : C_c(ℝ, ℝ)) (a x : ℝ) :
    autocorr (source f (-a)) x = 0 ↔ autocorr (source f a) x = 0 := by
  rw [← sq_eq_zero_iff, source_square_neg, sq_eq_zero_iff]

def correlation (f : C_c(ℝ, ℝ)) (a : ℝ) : ℝ → ℝ := normalizedSourceCorrelation (source f a)

private theorem correlation_zero_mass (f : C_c(ℝ, ℝ)) (a x : ℝ)
    (hR : autocorr f 0 = 0) : correlation f a x = 0 := by
  simp only [correlation, normalizedSourceCorrelation, source_mass, hR, mul_zero, div_zero]

/-- Exact signed packet decomposition, also valid for zero sources. -/
theorem correlation_formula (f : C_c(ℝ, ℝ)) (a x : ℝ) :
    correlation f a x = normalizedSourceCorrelation f x - copyMixingCoefficient a *
      (normalizedSourceCorrelation f (x - gap f) + normalizedSourceCorrelation f (x + gap f)) := by
  by_cases hR : autocorr f 0 = 0
  · simp only [correlation_zero_mass f a x hR, normalizedSourceCorrelation, hR,
      div_zero, add_zero, mul_zero, sub_zero]
  · have hp := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
    have he := normalizedSourceCorrelation_subtractCopy_sub f.continuous
      f.hasCompactSupport hp (fun _ hx => outside f hx) (radius_lt_gap f) a x
    change correlation f a x - normalizedSourceCorrelation f x = _ at he
    linarith only [he]

/-- The nonlinear transfer retains exactly the square of the scalar mixing parameter. -/
theorem correlation_square (f : C_c(ℝ, ℝ)) (a x : ℝ) :
    correlation f a x ^ 2 = normalizedSourceCorrelation f x ^ 2 + copyMixingCoefficient a ^ 2 *
      (normalizedSourceCorrelation f (x - gap f) ^ 2 +
        normalizedSourceCorrelation f (x + gap f) ^ 2) := by
  by_cases hR : autocorr f 0 = 0
  · simp only [correlation_zero_mass f a x hR, normalizedSourceCorrelation, hR,
      div_zero, zero_pow (by omega : 2 ≠ 0), add_zero, mul_zero]
  · dsimp [correlation, normalizedSourceCorrelation, copyMixingCoefficient]
    rw [div_pow, source_square, source_mass]
    have hd : 1 + a ^ 2 ≠ (0 : ℝ) := by positivity
    field_simp [hR, hd]
    <;> ring

/-- One signed sample repairs all the orientation lost by squaring in this family. -/
theorem correlation_reconstruction (f : C_c(ℝ, ℝ)) (a x : ℝ) :
    correlation f a x = normalizedSourceCorrelation f x + correlation f a (gap f) *
      (normalizedSourceCorrelation f (x - gap f) + normalizedSourceCorrelation f (x + gap f)) := by
  by_cases hR : autocorr f 0 = 0
  · simp only [correlation_zero_mass f a x hR, correlation_zero_mass f a (gap f) hR,
      normalizedSourceCorrelation, hR, div_zero, mul_zero, zero_mul, add_zero]
  · have hp := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
    have hc := normalizedSourceCorrelation_subtractCopy_center f.continuous f.hasCompactSupport
      hp (radius_pos f) (fun _ hx => outside f hx) (radius_lt_gap f) a
    change correlation f a (gap f) = -copyMixingCoefficient a at hc
    rw [correlation_formula, hc]
    ring

/-- Complete classification of the squared normalized profiles, with the degenerate case explicit. -/
theorem square_profiles_eq_iff (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (∀ x, correlation f a x ^ 2 = correlation f b x ^ 2) ↔
      autocorr f 0 = 0 ∨ copyMixingCoefficient a ^ 2 = copyMixingCoefficient b ^ 2 := by
  by_cases hR : autocorr f 0 = 0
  · simp only [hR, correlation_zero_mass f a _ hR, correlation_zero_mass f b _ hR,
      true_or, implies_true]
  · have hp := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
    have hc (c : ℝ) : correlation f c (gap f) = -copyMixingCoefficient c :=
      normalizedSourceCorrelation_subtractCopy_center f.continuous f.hasCompactSupport
        hp (radius_pos f) (fun _ hx => outside f hx) (radius_lt_gap f) c
    constructor
    · intro h
      exact Or.inr (by simpa only [hc, neg_sq] using h (gap f))
    · rintro (hz | he)
      · exact False.elim (hR hz)
      · intro x
        simp only [correlation_square, he]

/-- Signed profiles are classified by the signed mixing coefficient. -/
theorem profiles_eq_iff (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (∀ x, correlation f a x = correlation f b x) ↔
      autocorr f 0 = 0 ∨ copyMixingCoefficient a = copyMixingCoefficient b := by
  by_cases hR : autocorr f 0 = 0
  · simp only [hR, correlation_zero_mass f a _ hR, correlation_zero_mass f b _ hR,
      true_or, implies_true]
  · have hp := lt_of_le_of_ne (autocorr_zero_nonneg f) (Ne.symm hR)
    have hc (c : ℝ) : correlation f c (gap f) = -copyMixingCoefficient c :=
      normalizedSourceCorrelation_subtractCopy_center f.continuous f.hasCompactSupport
        hp (radius_pos f) (fun _ hx => outside f hx) (radius_lt_gap f) c
    constructor
    · intro h
      exact Or.inr (by simpa only [hc, neg_inj] using h (gap f))
    · rintro (hz | he)
      · exact False.elim (hR hz)
      · intro x
        simp only [correlation_formula, he]

end GaloisForLFunctions.BiScaleUncertainty.SeparatedSquare
