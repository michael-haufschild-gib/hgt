import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAHorizonBlock
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe

/-!
# Integer differences of splines and aliasing notches

Integer differences increase every harmonic zero of a cardinal spline without
changing its fourth-power Fourier denominator. Poisson summation retains the
whole harmonic sum: near an integer overlap its notch has order seven.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
namespace SplineAliasNotches

open Zeta23 RenormalizedArithmeticPotentialTheory.CompletedShell
open BiScaleUncertainty.ChebyshevGauge
open RHTower.WeilDeletion (upow paperFT_upow paperFT_unif support_upow_subset)

/-- Successive integer differences of the centered cardinal cubic spline. -/
def differenceSpline : ℕ → ℝ → ℝ
  | 0 => upow (1 / 2) 3
  | n + 1 => fun u => differenceSpline n u - differenceSpline n (u - 1)

theorem contDiff_differenceSpline (n : ℕ) : ContDiff ℝ 2 (differenceSpline n) := by
  induction n with
  | zero => exact contDiff_upow (by norm_num) 2
  | succ n ih => exact ih.sub (ih.comp (contDiff_id.sub contDiff_const))

theorem differenceSpline_support (n : ℕ) {u : ℝ}
    (hu : differenceSpline n u ≠ 0) : |u| ≤ (n : ℝ) + 2 := by
  induction n generalizing u with
  | zero =>
      have h := support_upow_subset (by norm_num : (0 : ℝ) < 1 / 2) 3 hu
      norm_num at h ⊢
      exact abs_le.mpr h
  | succ n ih =>
      by_cases h : differenceSpline n u = 0
      · have h' : differenceSpline n (u - 1) ≠ 0 := by
          intro hz
          exact hu (by simp only [differenceSpline, h, hz, sub_self])
        have hb := ih h'
        have ht : |u| ≤ |u - 1| + 1 := by
          simpa only [sub_add_cancel, abs_one] using abs_add_le (u - 1) (1 : ℝ)
        push_cast
        linarith only [hb, ht]
      · have hb := ih h
        push_cast
        linarith only [hb]

theorem hasCompactSupport_differenceSpline (n : ℕ) : HasCompactSupport (differenceSpline n) :=
  hasCompactSupport_of_support_subset_abs fun _ hu => differenceSpline_support n hu

theorem integrable_differenceSpline (n : ℕ) : Integrable (differenceSpline n) :=
  (contDiff_differenceSpline n).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_differenceSpline n)

theorem integral_differenceSpline_succ (n : ℕ) : ∫ u, differenceSpline (n + 1) u = 0 := by
  rw [differenceSpline, integral_sub (integrable_differenceSpline n)
    ((integrable_differenceSpline n).comp_sub_right 1), integral_sub_right_eq_self, sub_self]

/-- Each difference inserts one additional zero at every integer harmonic. -/
theorem paperFT_differenceSpline (n : ℕ) (z : ℂ) :
    paperFT (fun u => (differenceSpline n u : ℂ)) z =
      (1 - Complex.exp (I * z)) ^ n * paperFT (fun u => (upow (1 / 2) 3 u : ℂ)) z := by
  induction n with
  | zero => simp only [differenceSpline, pow_zero, one_mul]
  | succ n ih =>
      have hc : Continuous (fun u => (differenceSpline n u : ℂ)) :=
        Complex.continuous_ofReal.comp (contDiff_differenceSpline n).continuous
      have hs : HasCompactSupport (fun u => (differenceSpline n u : ℂ)) :=
        (hasCompactSupport_differenceSpline n).comp_left Complex.ofReal_zero
      have hi : Integrable (fun u : ℝ => (differenceSpline n u : ℂ) *
          Complex.exp (I * z * u)) :=
        (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right
      have ht : Integrable (fun u : ℝ => (differenceSpline n (u - 1) : ℂ) *
          Complex.exp (I * z * u)) := by
        have hct : Continuous (fun u : ℝ => (differenceSpline n (u - 1) : ℂ) *
            Complex.exp (I * z * u)) :=
          (hc.comp (continuous_id.sub continuous_const)).mul (by fun_prop)
        exact hct.integrable_of_hasCompactSupport
          (hs.comp_homeomorph (Homeomorph.subRight 1)).mul_right
      have he : paperFT (fun u => (differenceSpline (n + 1) u : ℂ)) z =
          paperFT (fun u => (differenceSpline n u : ℂ)) z -
            paperFT (ArithmeticCastelnuovoSeveri.translate 1
              (fun u => (differenceSpline n u : ℂ))) z := by
        simp only [paperFT, differenceSpline, Complex.ofReal_sub,
          ArithmeticCastelnuovoSeveri.translate, sub_mul]
        exact integral_sub hi ht
      rw [he, ArithmeticCastelnuovoSeveri.paperFT_translate, Complex.ofReal_one, mul_one, ih]
      ring

/-- Multiplication by the fourth power of frequency leaves a periodic numerator. -/
theorem scaled_paperFT_differenceSpline (n : ℕ) (z : ℂ) :
    z ^ 4 * paperFT (fun u => (differenceSpline n u : ℂ)) z =
      (1 - Complex.exp (I * z)) ^ n *
        (Complex.exp (I * z) - 1) ^ 4 / Complex.exp (I * z) ^ 2 := by
  have hb : z ^ 4 * paperFT (fun u => (upow (1 / 2) 3 u : ℂ)) z =
      (Complex.exp (I * z) - 1) ^ 4 / Complex.exp (I * z) ^ 2 := by
    by_cases hz : z = 0
    · subst z
      simp
    rw [paperFT_upow, paperFT_unif (by norm_num) hz]
    norm_num only [Nat.reduceAdd, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    have hden : (2 : ℂ) * I * z * (1 / 2) = I * z := by ring
    have hex : I * z * (1 / 2 : ℂ) = I * z / 2 := by ring
    rw [hden, hex, Complex.exp_neg]
    set E := Complex.exp (I * z / 2) with hE
    have hE0 : E ≠ 0 := Complex.exp_ne_zero _
    have hE2 : E ^ 2 = Complex.exp (I * z) := by
      rw [hE, pow_two, ← Complex.exp_add]
      congr 1
      ring
    rw [← hE2]
    field_simp [hz, hE0, I_ne_zero]
    have hI4 : (I : ℂ) ^ 4 = 1 := by
      calc (I : ℂ) ^ 4 = (I ^ 2) ^ 2 := by ring
        _ = 1 := by rw [Complex.I_sq]; norm_num
    rw [hI4]
    ring
  rw [paperFT_differenceSpline]
  calc z ^ 4 * ((1 - Complex.exp (I * z)) ^ n *
        paperFT (fun u => (upow (1 / 2) 3 u : ℂ)) z) =
      (1 - Complex.exp (I * z)) ^ n *
        (z ^ 4 * paperFT (fun u => (upow (1 / 2) 3 u : ℂ)) z) := by ring
    _ = _ := by rw [hb]; ring

theorem paperFT_differenceSpline_I_ne_zero (n : ℕ) :
    paperFT (fun u => (differenceSpline n u : ℂ)) I ≠ 0 := by
  rw [paperFT_differenceSpline, paperFT_upow]
  apply mul_ne_zero
  · apply pow_ne_zero
    intro h
    have he : Complex.exp (I * I) = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm he
    rw [Complex.norm_exp, norm_one] at hn
    have hre : (I * I).re = -1 := by simp
    rw [hre] at hn
    have hlt : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    exact (ne_of_lt hlt) hn
  · exact pow_ne_zero _ (paperFT_unif_ne_zero (by norm_num) (by simp))

theorem integral_differenceSpline_sq_pos (n : ℕ) :
    0 < ∫ u, differenceSpline n u ^ 2 := by
  have hn : ∃ u, differenceSpline n u ≠ 0 := by
    by_contra h
    push Not at h
    apply paperFT_differenceSpline_I_ne_zero n
    simp only [paperFT, h, Complex.ofReal_zero, zero_mul, integral_zero]
  obtain ⟨u, hu⟩ := hn
  have hc : Continuous (fun x : ℝ => differenceSpline n x ^ 2) :=
    (contDiff_differenceSpline n).continuous.pow 2
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((hasCompactSupport_differenceSpline n).comp_left
        (g := fun x : ℝ => x ^ 2) (by norm_num))
    (fun x => sq_nonneg _) (pow_ne_zero 2 hu)

private theorem norm_fourth_mul_sq (t : ℝ) (z : ℂ) :
    ‖(t : ℂ) ^ 4 * z‖ ^ 2 = t ^ 8 * ‖z‖ ^ 2 := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  congr 1
  calc (|t| ^ 4) ^ 2 = (|t| ^ 2) ^ 4 := by ring
    _ = (t ^ 2) ^ 4 := by rw [sq_abs]
    _ = t ^ 8 := by ring

/-- The eighth-power weighted spectrum is periodic, for every difference order. -/
theorem weighted_spectrum_add_int (n : ℕ) (j : ℤ) (x : ℝ) :
    ((j : ℝ) + x) ^ 8 * shellSpectrum (differenceSpline n) ((j : ℝ) + x) =
      x ^ 8 * shellSpectrum (differenceSpline n) x := by
  have hexp : Complex.exp (I * ((2 * Real.pi * ((j : ℝ) + x) : ℝ) : ℂ)) =
      Complex.exp (I * ((2 * Real.pi * x : ℝ) : ℂ)) := by
    have he : I * ((2 * Real.pi * ((j : ℝ) + x) : ℝ) : ℂ) =
        (j : ℂ) * (2 * (Real.pi : ℂ) * I) + I * ((2 * Real.pi * x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  have h₁ := scaled_paperFT_differenceSpline n
    (((2 * Real.pi * ((j : ℝ) + x) : ℝ)) : ℂ)
  have h₀ := scaled_paperFT_differenceSpline n (((2 * Real.pi * x : ℝ)) : ℂ)
  rw [hexp] at h₁
  have hn := congrArg (fun z : ℂ => ‖z‖ ^ 2) (h₁.trans h₀.symm)
  rw [norm_fourth_mul_sq, norm_fourth_mul_sq] at hn
  change (2 * Real.pi * ((j : ℝ) + x)) ^ 8 *
      shellSpectrum (differenceSpline n) ((j : ℝ) + x) =
    (2 * Real.pi * x) ^ 8 * shellSpectrum (differenceSpline n) x at hn
  apply mul_left_cancel₀ (pow_ne_zero 8 (mul_ne_zero two_ne_zero Real.pi_ne_zero))
  convert hn using 1 <;> ring

theorem aliasDensity_add_nat (n j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    aliasDensity (differenceSpline n) ((j : ℝ) + ε) =
      (ε / ((j : ℝ) + ε)) ^ 8 * aliasDensity (differenceSpline n) ε := by
  have hs : 0 < (j : ℝ) + ε := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hε
  have hterm : ∀ k : ℕ,
      shellSpectrum (differenceSpline n) (((k : ℝ) + 1) * ((j : ℝ) + ε)) =
        (ε / ((j : ℝ) + ε)) ^ 8 *
          shellSpectrum (differenceSpline n) (((k : ℝ) + 1) * ε) := by
    intro k
    have hp := weighted_spectrum_add_int n (((k + 1) * j : ℕ) : ℤ) (((k : ℝ) + 1) * ε)
    have ha : ((((k + 1) * j : ℕ) : ℤ) : ℝ) + ((k : ℝ) + 1) * ε =
        ((k : ℝ) + 1) * ((j : ℝ) + ε) := by push_cast; ring
    rw [ha] at hp
    have hk : ((k : ℝ) + 1) ^ 8 ≠ 0 := by positivity
    have he : ((j : ℝ) + ε) ^ 8 *
        shellSpectrum (differenceSpline n) (((k : ℝ) + 1) * ((j : ℝ) + ε)) =
      ε ^ 8 * shellSpectrum (differenceSpline n) (((k : ℝ) + 1) * ε) := by
      apply mul_left_cancel₀ hk
      convert hp using 1 <;> ring
    rw [div_pow]
    field_simp [hs.ne']
    exact he
  unfold aliasDensity
  simp_rw [hterm]
  exact tsum_mul_left

private theorem autocorr_support {f : ℝ → ℝ} {A : ℝ}
    (hs : ∀ u, f u ≠ 0 → |u| ≤ A) {x : ℝ}
    (hx : shellAutocorr f x ≠ 0) : |x| ≤ 2 * A := by
  by_contra h
  apply hx
  unfold shellAutocorr RHTower.ArchimedeanAnomaly.autocorr
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro u
  change f u * f (u + x) = 0
  by_cases hu : f u = 0
  · rw [hu, zero_mul]
  · have hv : f (u + x) = 0 := by
      by_contra hv
      have h₁ := hs u hu
      have h₂ := hs (u + x) hv
      have h₃ : |x| ≤ |u + x| + |u| := by
        have he : u + x + -u = x := by ring
        simpa only [he, abs_neg] using abs_add_le (u + x) (-u)
      exact h (by linarith only [h₁, h₂, h₃])
    rw [hv, mul_zero]

/-- Below the autocorrelation spacing, all nonzero dual-grid samples vanish. -/
theorem aliasDensity_below_spacing {f : ℝ → ℝ} {A ε : ℝ}
    (hf : ContDiff ℝ 2 f) (hs : ∀ u, f u ≠ 0 → |u| ≤ A)
    (hε : 0 < ε) (hgap : 2 * A < 1 / ε) :
    aliasDensity f ε = (∫ u, f u ^ 2) / (2 * ε) - (∫ u, f u) ^ 2 / 2 := by
  have hfc : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hs
  have hgc : ContDiff ℝ 2 (fun u => (shellAutocorr f u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_autocorr hf hfc)
  have hgs : ∀ u, (shellAutocorr f u : ℂ) ≠ 0 → |u| ≤ 2 * A := by
    intro u hu
    exact autocorr_support hs (fun hz => hu (by rw [hz, Complex.ofReal_zero]))
  have hlattice : (∑' m : ℤ, (shellAutocorr f (m * (1 / ε)) : ℂ)) =
      (((∫ u, f u ^ 2) : ℝ) : ℂ) := by
    rw [tsum_eq_single 0]
    · simp only [Int.cast_zero, zero_mul, shellAutocorr_zero]
    · intro m hm
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
      have hx : 2 * A < |(m : ℝ) * (1 / ε)| := by
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hε)]
        exact hgap.trans_le (by nlinarith only [hm1, one_div_pos.mpr hε])
      have hz : shellAutocorr f ((m : ℝ) * (1 / ε)) = 0 := by
        by_contra hz
        exact (not_lt_of_ge (autocorr_support hs hz)) hx
      rw [hz, Complex.ofReal_zero]
  have hp := RHTower.hasSum_paperFT_lattice (one_div_pos.mpr hε) hgc hgs
  rw [hlattice] at hp
  have hterm : ∀ k : ℤ,
      paperFT (fun u => (shellAutocorr f u : ℂ))
          (((k : ℝ) * (2 * Real.pi / (1 / ε)) : ℝ) : ℂ) =
        (shellSpectrum f ((k : ℝ) * ε) : ℂ) := by
    intro k
    have he : (k : ℝ) * (2 * Real.pi / (1 / ε)) = 2 * Real.pi * ((k : ℝ) * ε) := by
      field_simp
    rw [he, paperFT_autocorr hf.continuous hfc, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  simp_rw [hterm] at hp
  have hr := Complex.hasSum_re hp
  simp only [← Complex.ofReal_mul, Complex.ofReal_re] at hr
  have hnat := hr.nat_add_neg
  have hev : ∀ k : ℕ,
      shellSpectrum f ((k : ℤ) * ε) + shellSpectrum f ((-(k : ℤ) : ℤ) * ε) =
        2 * shellSpectrum f ((k : ℝ) * ε) := by
    intro k
    rw [Int.cast_neg, neg_mul, shellSpectrum_neg, Int.cast_natCast]
    ring
  simp_rw [hev] at hnat
  simp only [Int.cast_zero, zero_mul, shellSpectrum_zero] at hnat
  have hhalf := hnat.div_const 2
  simp_rw [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at hhalf
  have hsucc := (hasSum_nat_add_iff' 1).mpr hhalf
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul,
    shellSpectrum_zero, Nat.cast_add, Nat.cast_one] at hsucc
  rw [aliasDensity, hsucc.tsum_eq]
  ring

/-- Every positive-order integer difference has the same exact seventh-order alias notch. -/
theorem aliasDensity_differenceSpline_near_integer (n j : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hgap : 2 * ((n + 1 : ℕ) + (2 : ℝ)) < 1 / ε) :
    aliasDensity (differenceSpline (n + 1)) ((j : ℝ) + ε) =
      (∫ u, differenceSpline (n + 1) u ^ 2) * ε ^ 7 /
        (2 * ((j : ℝ) + ε) ^ 8) := by
  rw [aliasDensity_add_nat _ _ hε,
    aliasDensity_below_spacing (contDiff_differenceSpline (n + 1))
      (fun _ hu => differenceSpline_support (n + 1) hu)
      hε hgap, integral_differenceSpline_succ, zero_pow (by omega), zero_div, sub_zero]
  have hs : 0 < (j : ℝ) + ε := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hε
  field_simp [hε.ne', hs.ne']

/-- Every positive integer is an exact aliasing zero. -/
theorem aliasDensity_differenceSpline_nat (n j : ℕ) :
    aliasDensity (differenceSpline n) (j + 1) = 0 := by
  have hzero : ∀ k : ℕ, 0 < k → shellSpectrum (differenceSpline n) k = 0 := by
    intro k hk
    have h := weighted_spectrum_add_int n (k : ℤ) 0
    simp only [Int.cast_natCast, add_zero, zero_pow (by norm_num : (8 : ℕ) ≠ 0), zero_mul] at h
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 8 hk0)
  unfold aliasDensity
  have ht : ∀ k : ℕ, shellSpectrum (differenceSpline n) (((k : ℝ) + 1) * (j + 1)) = 0 := by
    intro k
    convert hzero ((k + 1) * (j + 1)) (by positivity) using 1 <;> push_cast <;> rfl
  simp only [ht, tsum_zero]

/-- Every difference order has a seventh-order notch with a positive leading coefficient. -/
theorem tendsto_aliasDensity_div_pow_seven (n j : ℕ) :
    Tendsto (fun ε : ℝ => aliasDensity (differenceSpline (n + 1)) ((j + 1 : ℕ) + ε) / ε ^ 7)
      (𝓝[>] 0)
      (𝓝 ((∫ u, differenceSpline (n + 1) u ^ 2) / (2 * ((j + 1 : ℕ) : ℝ) ^ 8))) := by
  let M := ∫ u, differenceSpline (n + 1) u ^ 2
  let J : ℝ := (j + 1 : ℕ)
  let A : ℝ := (n + 1 : ℕ) + 2
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hA : 0 < 2 * A := by dsimp only [A]; positivity
  have hc : ContinuousAt (fun ε : ℝ => M / (2 * (J + ε) ^ 8)) 0 :=
    continuousAt_const.div
      (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).pow 8))
      (by dsimp; positivity)
  have ht : Tendsto (fun ε : ℝ => M / (2 * (J + ε) ^ 8)) (𝓝[>] 0)
      (𝓝 (M / (2 * J ^ 8))) := by
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  change Tendsto _ _ (𝓝 (M / (2 * J ^ 8)))
  apply ht.congr'
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / (2 * A) :=
    (eventually_lt_nhds (one_div_pos.mpr hA)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hsmallε
  have hε0 : 0 < ε := hε
  have hgap : 2 * A < 1 / ε := by
    apply (lt_div_iff₀ hε0).mpr
    have he := (lt_div_iff₀ hA).mp hsmallε
    linarith only [he]
  rw [aliasDensity_differenceSpline_near_integer n (j + 1) hε0 hgap]
  change M / (2 * (J + ε) ^ 8) = M * ε ^ 7 / (2 * (J + ε) ^ 8) / ε ^ 7
  field_simp [hε0.ne', (add_pos hJ hε0).ne']

#print axioms scaled_paperFT_differenceSpline
#print axioms integral_differenceSpline_sq_pos
#print axioms aliasDensity_differenceSpline_near_integer
#print axioms tendsto_aliasDensity_div_pow_seven

end SplineAliasNotches
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
