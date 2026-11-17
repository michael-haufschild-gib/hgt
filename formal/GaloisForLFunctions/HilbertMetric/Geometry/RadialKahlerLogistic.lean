import GaloisForLFunctions.HilbertMetric.Geometry.RadialKahlerProfile
import GaloisForLFunctions.HTGeometry.CoshFourierTransform

/-!
# The radial Kähler parameter in logistic coordinates

The logistic coordinate used for hyperbolic Fourier transforms also
parametrizes all positive radial Kähler scales. Its flux transforms the
rational parameter map into the sharp polynomial profile. Thus the
critical scale, maximal parameter, and two monotone branches are exact.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.RadialKahler
open Set

/-- Boundary flux associated with the positive radial scale `exp(2t)`. -/
def flux (n : ℕ) (t : ℝ) : ℝ := (n + 2) * _root_.HTGeometry.logisticVar t

/-- The Kähler parameter in logarithmic radial scale. -/
def parameter (n : ℕ) (t : ℝ) : ℝ := profile n (flux n t)

/-- Logarithmic scale of the unique maximal Kähler parameter. -/
def criticalScale (n : ℕ) : ℝ := Real.log (n + 1) / 2

theorem flux_pos (n : ℕ) (t : ℝ) : 0 < flux n t :=
  mul_pos (by positivity) (_root_.HTGeometry.logisticVar_pos t)

theorem flux_lt_endpoint (n : ℕ) (t : ℝ) : flux n t < n + 2 := by
  have h := mul_lt_mul_of_pos_left (_root_.HTGeometry.logisticVar_lt_one t)
    (by positivity : (0 : ℝ) < n + 2)
  simpa only [flux, mul_one] using h

theorem flux_strictMono (n : ℕ) : StrictMono (flux n) := by
  intro x y hxy
  exact mul_lt_mul_of_pos_left (_root_.HTGeometry.logisticVar_strictMono hxy) (by positivity)

/-- Every admissible boundary flux is realized by one logarithmic radial scale. -/
theorem flux_image_univ (n : ℕ) : flux n '' univ = Ioo 0 (n + 2 : ℝ) := by
  ext s
  constructor
  · rintro ⟨t, _, rfl⟩
    exact ⟨flux_pos n t, flux_lt_endpoint n t⟩
  · intro hs
    have hn : (0 : ℝ) < n + 2 := by positivity
    have hv : s / (n + 2) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos hs.1 hn, (div_lt_one hn).mpr hs.2⟩
    rw [← _root_.HTGeometry.logisticVar_image_univ] at hv
    obtain ⟨t, _, ht⟩ := hv
    refine ⟨t, mem_univ _, ?_⟩
    rw [flux, ht]
    field_simp [hn.ne']

theorem flux_exp (n : ℕ) (t : ℝ) :
    flux n t = (n + 2) * Real.exp (2 * t) / (1 + Real.exp (2 * t)) := by
  rw [flux, _root_.HTGeometry.logisticVar_eq_exp]
  ring

/-- The logistic profile is precisely the explicit radial Kähler parameter formula. -/
theorem parameter_exp (n : ℕ) (t : ℝ) :
    parameter n t = (n + 2 : ℝ) ^ (n + 1) * Real.exp (2 * t) ^ (n + 1) /
      (1 + Real.exp (2 * t)) ^ (n + 2) := by
  rw [parameter, profile, flux_exp]
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  have he : 1 + Real.exp (2 * t) ≠ 0 := by positivity
  simp only [div_pow, mul_pow, pow_succ]
  field_simp [hn, he]
  ring

/-- The extremal flux occurs at radial scale `exp(2t) = n + 1`. -/
theorem flux_criticalScale (n : ℕ) : flux n (criticalScale n) = n + 1 := by
  rw [flux_exp, criticalScale]
  rw [show (2 : ℝ) * (Real.log (n + 1) / 2) = Real.log (n + 1) by ring,
    Real.exp_log (by positivity)]
  have hn : (1 + (n + 1 : ℝ)) ≠ 0 := by positivity
  field_simp [hn]
  ring

theorem parameter_pos (n : ℕ) (t : ℝ) : 0 < parameter n t := by
  change 0 < (flux n t) ^ (n + 1) * (1 - flux n t / (n + 2))
  exact mul_pos (pow_pos (flux_pos n t) _)
    (sub_pos.mpr ((div_lt_one (by positivity : (0 : ℝ) < n + 2)).mpr
      (flux_lt_endpoint n t)))

/-- The sharp radial parameter ceiling holds at every real logarithmic scale. -/
theorem parameter_le_peak (n : ℕ) (t : ℝ) : parameter n t ≤ peak n :=
  profile_le_peak n ⟨flux n t, (flux_pos n t).le⟩

/-- The maximal parameter has exactly one logarithmic scale. -/
theorem parameter_eq_peak_iff (n : ℕ) (t : ℝ) :
    parameter n t = peak n ↔ t = criticalScale n := by
  have h : parameter n t = peak n ↔ flux n t = n + 1 :=
    profile_eq_peak_iff n ⟨flux n t, (flux_pos n t).le⟩
  rw [h]
  rw [← flux_criticalScale]
  exact (flux_strictMono n).injective.eq_iff

/-- The small-scale branch is strictly increasing. -/
theorem parameter_strictMonoOn (n : ℕ) :
    StrictMonoOn (parameter n) (Iic (criticalScale n)) := by
  intro x hx y hy hxy
  change profile n (flux n x) < profile n (flux n y)
  apply profile_strictMonoOn n
  · refine ⟨(flux_pos n x).le, ?_⟩
    rw [← flux_criticalScale]
    exact (flux_strictMono n).monotone hx
  · refine ⟨(flux_pos n y).le, ?_⟩
    rw [← flux_criticalScale]
    exact (flux_strictMono n).monotone hy
  · exact flux_strictMono n hxy

/-- The large-scale branch is strictly decreasing. -/
theorem parameter_strictAntiOn (n : ℕ) :
    StrictAntiOn (parameter n) (Ici (criticalScale n)) := by
  intro x hx y hy hxy
  change profile n (flux n y) < profile n (flux n x)
  apply profile_strictAntiOn n
  · change n + 1 ≤ flux n x
    rw [← flux_criticalScale]
    exact (flux_strictMono n).monotone hx
  · change n + 1 ≤ flux n y
    rw [← flux_criticalScale]
    exact (flux_strictMono n).monotone hy
  · exact flux_strictMono n hxy

/-- The positive radial family realizes precisely the interval below its sharp ceiling. -/
theorem parameter_image_univ (n : ℕ) : parameter n '' univ = Ioc 0 (peak n) := by
  ext y
  constructor
  · rintro ⟨t, _, rfl⟩
    exact ⟨parameter_pos n t, parameter_le_peak n t⟩
  · intro hy
    by_cases hmax : y = peak n
    · refine ⟨criticalScale n, mem_univ _, ?_⟩
      rw [hmax]
      exact (parameter_eq_peak_iff n _).mpr rfl
    · have hlt : y < peak n := by
        by_contra h
        exact hmax (le_antisymm hy.2 (le_of_not_gt h))
      obtain ⟨a, b, ha0, hac, _, _, hay, _, _⟩ :=
        (profile_two_branch_classification n y).mp ⟨hy.1, hlt⟩
      have ha : a ∈ Ioo (0 : ℝ) (n + 2) := ⟨ha0, by linarith only [hac]⟩
      rw [← flux_image_univ] at ha
      obtain ⟨t, _, ht⟩ := ha
      exact ⟨t, mem_univ _, by rw [parameter, ht, hay]⟩

/-- Every positive subcritical parameter has exactly two logarithmic radial scales. -/
theorem parameter_two_scale_classification (n : ℕ) (y : ℝ) :
    (0 < y ∧ y < peak n) ↔
      ∃ a b : ℝ, a < criticalScale n ∧ criticalScale n < b ∧
        parameter n a = y ∧ parameter n b = y ∧
        ∀ t : ℝ, parameter n t = y ↔ t = a ∨ t = b := by
  constructor
  · intro hy
    obtain ⟨a, b, ha0, hac, hcb, hb1, hay, hby, hroots⟩ :=
      (profile_two_branch_classification n y).mp hy
    have ha : a ∈ Ioo (0 : ℝ) (n + 2) := ⟨ha0, by linarith only [hac]⟩
    have hb : b ∈ Ioo (0 : ℝ) (n + 2) :=
      ⟨lt_trans (by positivity : (0 : ℝ) < n + 1) hcb, hb1⟩
    rw [← flux_image_univ] at ha hb
    obtain ⟨a', _, ha'⟩ := ha
    obtain ⟨b', _, hb'⟩ := hb
    have hac' : a' < criticalScale n := by
      by_contra h
      have hm := (flux_strictMono n).monotone (le_of_not_gt h)
      rw [flux_criticalScale, ha'] at hm
      linarith only [hac, hm]
    have hcb' : criticalScale n < b' := by
      by_contra h
      have hm := (flux_strictMono n).monotone (le_of_not_gt h)
      rw [flux_criticalScale, hb'] at hm
      linarith only [hcb, hm]
    refine ⟨a', b', hac', hcb', ?_, ?_, ?_⟩
    · rw [parameter, ha', hay]
    · rw [parameter, hb', hby]
    · intro t
      have hr := hroots ⟨flux n t, (flux_pos n t).le⟩
      change profile n (flux n t) = y ↔ flux n t = a ∨ flux n t = b at hr
      rw [← ha', ← hb', (flux_strictMono n).injective.eq_iff,
        (flux_strictMono n).injective.eq_iff] at hr
      exact hr
  · rintro ⟨a, b, ha, _, hay, _, _⟩
    refine ⟨hay ▸ parameter_pos n a, ?_⟩
    have h := parameter_strictMonoOn n ha.le
      (show criticalScale n ≤ criticalScale n from le_rfl) ha
    rw [(parameter_eq_peak_iff n (criticalScale n)).mpr rfl, hay] at h
    exact h

#print axioms parameter_exp
#print axioms parameter_eq_peak_iff
#print axioms parameter_strictMonoOn
#print axioms parameter_strictAntiOn
#print axioms parameter_image_univ
#print axioms parameter_two_scale_classification

end GaloisForLFunctions.HilbertMetric.RadialKahler
