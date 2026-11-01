import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothProfileLogarithmicTransport
import GaloisForLFunctions.ArithmeticIncidencePositivity.LagChebyshevAbelSummation

/-!
# Smooth taper transport in logarithmic stabilizer rows

The standard taper is the autocorrelation of a compact function between zero
and one whose derivative has total variation two. Its Lipschitz constant is
therefore two, independently of length and collar. The logarithmic first
moment then controls its endpoint variation by `O(O(Q)/T)` for fixed smooth
height profiles, retaining the actual taper in the signed pair kernel.
-/

noncomputable section
open MeasureTheory Real Filter Topology Finset
open Zeta23
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- The actual smooth taper has Lipschitz constant two, uniformly in its
length, collar and monotone transition profile. -/
theorem abs_taperAutocorrelation_sub_le {ρ : ℝ → ℝ} {L w : ℝ}
    (hρ : TaperProfile ρ) (hw : 0 < w) (hwL : 2 * w ≤ L) (x y : ℝ) :
    |Taper.g ρ L w x - Taper.g ρ L w y| ≤ 2 * |x - y| := by
  let F : ℝ → ℝ := fun t => Taper.phi ρ L w t ^ 2
  have hF : ContDiff ℝ 1 F :=
    ((Taper.phi_contDiff hρ hw hwL).of_le (by norm_num)).pow 2
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-(L / 2)) (L / 2))
      isCompact_Icc ?_
    intro t ht
    by_contra hn
    have hts : L / 2 ≤ |t| := by
      by_contra hh
      have hh' := abs_lt.mp (lt_of_not_ge hh)
      exact hn ⟨hh'.1.le, hh'.2.le⟩
    exact ht (by dsimp [F]; rw [Taper.phi_eq_zero hρ hw hts]; ring)
  have hF1 (t : ℝ) : |F t| ≤ 1 := by
    dsimp [F]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (Taper.phi_nonneg hρ t) (Taper.phi_le_one hρ t)
  have hcross (t : ℝ) : |ArithmeticIncidencePositivity.crossCorrelation F t| ≤ 2 := by
    have hdc : Continuous (deriv F) := hF.continuous_deriv le_rfl
    have hdint : Integrable (deriv F) := hdc.integrable_of_hasCompactSupport hFc.deriv
    have hip : Integrable (fun u => F u * deriv F (u + t)) :=
      (hF.continuous.mul (hdc.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hFc.mul_right
    change |∫ u : ℝ, F u * deriv F (u + t)| ≤ 2
    calc
      _ ≤ ∫ u : ℝ, |F u * deriv F (u + t)| := abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ, |deriv F (u + t)| := integral_mono hip.abs (hdint.abs.comp_add_right t) (by
        intro u
        dsimp only
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hF1 u))
      _ = ∫ u : ℝ, |deriv F u| :=
        integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun u => |deriv F u|) t
      _ = 2 := Taper.integral_abs_deriv_phi_sq hρ hw hwL
  have hd (t : ℝ) := ArithmeticIncidencePositivity.hasDerivAt_autoCorrelation hF hFc t
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := ArithmeticIncidencePositivity.autoCorrelation F) (s := Set.univ)
    (fun t _ => (hd t).differentiableAt)
    (fun t _ => by rw [(hd t).deriv, Real.norm_eq_abs]; exact hcross t)
    (convex_univ) (Set.mem_univ x) (Set.mem_univ y)
  change |ArithmeticIncidencePositivity.autoCorrelation F x -
    ArithmeticIncidencePositivity.autoCorrelation F y| ≤ _
  simpa only [Real.norm_eq_abs, abs_sub_comm] using h

/-- The change of taper between the two endpoints of a positive even-shift row. -/
def stabilizerTaperVariation (Q : ℕ) (Ω g : ℝ → ℝ) (m : ℝ) (R : ℕ) : ℝ :=
  ∑ n ∈ range R, parityStabilizerWeight Q (2 * (n + 1)) *
    (g (Real.log (m + ((2 * (n + 1) : ℕ) : ℝ))) - g (Real.log m)) *
      cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
        Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ)))

private theorem taper_variation_le_moment {ρ Ω : ℝ → ℝ} {L w m : ℝ}
    (hρ : TaperProfile ρ) (hw : 0 < w) (hwL : 2 * w ≤ L) (hm : 0 < m) (Q R : ℕ) :
    |stabilizerTaperVariation Q Ω (Taper.g ρ L w) m R| ≤
      2 * ∑ n ∈ range R, |parityStabilizerWeight Q (2 * (n + 1)) *
        Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m) *
        cosTransform Ω (Real.log (1 + ((2 * (n + 1) : ℕ) : ℝ) / m)) /
          Real.sqrt (m * (m + ((2 * (n + 1) : ℕ) : ℝ)))| := by
  unfold stabilizerTaperVariation
  apply (abs_sum_le_sum_abs _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro n _
  let h : ℝ := ((2 * (n + 1) : ℕ) : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hlog : Real.log (m + h) - Real.log m = Real.log (1 + h / m) := by
    rw [← Real.log_div (by positivity : m + h ≠ 0) hm.ne']
    congr 1
    field_simp [hm.ne']
  have hg := abs_taperAutocorrelation_sub_le hρ hw hwL (Real.log (m + h)) (Real.log m)
  rw [hlog] at hg
  change |parityStabilizerWeight Q (2 * (n + 1)) *
      (Taper.g ρ L w (Real.log (m + h)) - Taper.g ρ L w (Real.log m)) *
      cosTransform Ω (Real.log (1 + h / m)) / Real.sqrt (m * (m + h))| ≤ _
  rw [abs_div, abs_mul, abs_mul]
  calc
    _ ≤ (|parityStabilizerWeight Q (2 * (n + 1))| * (2 * |Real.log (1 + h / m)|) *
        |cosTransform Ω (Real.log (1 + h / m))|) / |Real.sqrt (m * (m + h))| :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (abs_nonneg _)) (abs_nonneg _))
        (abs_nonneg _)
    _ = _ := by
      change _ = 2 * |parityStabilizerWeight Q (2 * (n + 1)) * Real.log (1 + h / m) *
        cosTransform Ω (Real.log (1 + h / m)) / Real.sqrt (m * (m + h))|
      rw [abs_div, abs_mul, abs_mul]
      ring

/-- The actual smooth taper's endpoint variation is controlled by the decaying
logarithmic first moment, with no factor proportional to taper length. -/
theorem abs_stabilizerTaperVariation_le {ρ Ω : ℝ → ℝ} {L w a b T m : ℝ}
    (hρ : TaperProfile ρ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (Q R : ℕ) (hab : a ≤ b) (hT : 0 < T) (hm : 0 < m)
    (hR : ((2 * R : ℕ) : ℝ) ≤ m) (hΩ : ContDiff ℝ 4 Ω)
    (hsupp : ∀ t ∉ Set.Icc a b, Ω t = 0) :
    |stabilizerTaperVariation Q Ω (Taper.g ρ L w) m R| ≤
      8 * (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) *
        ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
          16 * T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)) / T := by
  have h := (taper_variation_le_moment hρ hw hwL hm Q R).trans
    (mul_le_mul_of_nonneg_left (sum_abs_stabilizerLogarithmicMoment_le Q R hab hT hm hR hΩ hsupp)
      (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ 2 * (4 * (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1),
      RHTower.Sieve.sqfreeTotientInv q) *
        ((∫ t in (a - 1)..(b + 1), |Ω t|) / T +
          16 * T^3 * (∫ t in (a - 1)..(b + 1), |iteratedDeriv 4 Ω t|)) / T) := h
    _ = _ := by ring

/-- Fixed smooth height profiles give an `O(O(Q)/T)` endpoint-variation bound
uniformly over all admissible standard tapers. -/
theorem WindowProfile.exists_stabilizerTaperVariation_le {ε : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε u) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ → ℝ) (L w T m : ℝ) (Q R : ℕ),
      TaperProfile ρ → 0 < w → 2 * w ≤ L → 1 ≤ T → 0 < m → ((2 * R : ℕ) : ℝ) ≤ m →
      |stabilizerTaperVariation Q (profileΩ u T) (Taper.g ρ L w) m R| ≤
        (∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) * C / T := by
  obtain ⟨C, hC, hCb⟩ := hu.exists_stabilizerLogarithmicMoment_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro ρ L w T m Q R hρ hw hwL hT hm hR
  have h := (taper_variation_le_moment hρ hw hwL hm Q R).trans
    (mul_le_mul_of_nonneg_left (hCb T m Q R hT hm hR) (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ 2 * ((∑ q ∈ (Icc 1 Q).filter (fun q => q % 2 = 1),
      RHTower.Sieve.sqfreeTotientInv q) * C / T) := h
    _ = _ := by ring

end GaloisForLFunctions.TransThresholdPairCorrelation
