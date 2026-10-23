import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheReceiverReadsTheZeroDivisorOfZetaOnTheOscillatingSpectrum
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheProbeReceiverEnergyMeasuresTheModulusOfZeta

/-!
# The half-damped receiver is diagonal on the probe spectrum, with weights |ζ|²

For a finite set `J` of positive frequencies and real coefficients `α_t`, the half-damped probe
combination `c(d) = Σ_{t ∈ J} α_t d^{-1/2} cos(t log d)` has receiver energy
`E_T(c)/log T → Σ_{t ∈ J} α_t² |ζ(½ + it)|²/(2|½ + it|²)`
(`tendsto_halfProbeCombination_energy_div_log`). On the span of the half-damped probes the receiver
is asymptotically the diagonal quadratic form with spectral weight `|ζ(½+it)|²/(2|½+it|²)`:
distinct frequencies are orthogonal for the receiver, and each frequency is weighted by `|ζ|²` on
the critical line. In particular a combination is paid iff every frequency with `α_t ≠ 0` is the
ordinate of a critical zero, and otherwise its energy grows like `log T` with the explicit rate.

* **Main term.** The prefix is `√n Re(Σ_t c_t n^{it}) + O(n^{1/4})`, `c_t = α_t ζ(ρ_t)/ρ_t`
  (`halfProbeMain_eq`), so `|√E_T − ‖M‖_T| = O(1)`.
* **Orthogonality.** `Σ_{n ≤ T} Re(Σ_t c_t n^{it})²/(n+1) = (Σ_t |c_t|²/2) log T + O(1)`
  (`abs_sum_oscSum_sq_div_succ_sub_le`): the cross frequencies `t − s ≠ 0` and `t + s > 0` have
  bounded sums `Σ n^{iτ}/(n+1)`, and the diagonal is the harmonic sum.
-/

open Finset Filter Topology Complex
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Probe combinations -/

/-- The half-damped probe combination `Σ_{t ∈ J} α_t d^{-1/2} cos(t log d)`. -/
def halfProbeCombination (J : Finset ℝ) (α : ℝ → ℝ) (d : ℕ) : ℝ :=
  ∑ t ∈ J, α t * oscillatingSmoothPower (1 / 2) t d

theorem hasSum_halfProbeCombination_div (J : Finset ℝ) (α : ℝ → ℝ) :
    HasSum (fun d : ℕ => halfProbeCombination J α d / d)
      (∑ t ∈ J, α t * ∑' d : ℕ, oscillatingSmoothPower (1 / 2) t d / d) := by
  refine (hasSum_sum fun t _ =>
    ((hasSum_oscillatingSmoothPower_div (by norm_num : (0 : ℝ) < 1 / 2) t).summable.hasSum).mul_left
      (α t)).congr_fun fun d => ?_
  rw [halfProbeCombination, sum_div]
  exact sum_congr rfl fun t _ => by ring

/-- The prefix of a combination is the combination of the prefixes. -/
theorem weightCenteredPrefix_halfProbeCombination (J : Finset ℝ) (α : ℝ → ℝ) (n : ℕ) :
    weightCenteredPrefix (halfProbeCombination J α) (∑' d : ℕ, halfProbeCombination J α d / d) n =
      ∑ t ∈ J, α t * weightCenteredPrefix (oscillatingSmoothPower (1 / 2) t)
        (∑' d : ℕ, oscillatingSmoothPower (1 / 2) t d / d) n := by
  rw [(hasSum_halfProbeCombination_div J α).tsum_eq,
    show halfProbeCombination J α = fun d => ∑ t ∈ J, α t * oscillatingSmoothPower (1 / 2) t d
      from rfl,
    weightCenteredPrefix_finset_sum J (fun t d => α t * oscillatingSmoothPower (1 / 2) t d)
      (fun t => α t * ∑' d : ℕ, oscillatingSmoothPower (1 / 2) t d / d) n]
  exact sum_congr rfl fun t _ => weightCenteredPrefix_smul (α t) _ _ n

/-- The main term `Σ_t α_t Re(a_t n^{ρ_t})` of a combination. -/
def halfProbeMain (J : Finset ℝ) (α : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ J, α t * probeMain (1 / 2) t n

/-- The main term is `√n Re(Σ_t c_t n^{it})`, `c_t = α_t a_t`. -/
theorem halfProbeMain_eq (J : Finset ℝ) (α : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    halfProbeMain J α n =
      Real.sqrt n * oscSum J (fun t => (α t : ℂ) * probeAmp (1 / 2) t) n := by
  have hx0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  unfold halfProbeMain oscSum
  rw [Complex.re_sum, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  have hsplit : ((n : ℝ) : ℂ) ^ oscillationExponent (1 / 2) t =
      ((Real.sqrt n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
    rw [oscillationExponent, Complex.cpow_add _ _ hnC, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow hx0.le]
    norm_num
  unfold probeMain
  rw [hsplit,
    show probeAmp (1 / 2) t * (((Real.sqrt n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)) =
      ((Real.sqrt n : ℝ) : ℂ) * (probeAmp (1 / 2) t * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)) by ring,
    Complex.re_ofReal_mul,
    show (α t : ℂ) * probeAmp (1 / 2) t * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) =
      ((α t : ℝ) : ℂ) * (probeAmp (1 / 2) t * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)) by ring,
    Complex.re_ofReal_mul]
  ring

/-! ### Orthogonality of frequencies -/

/-- **Frequencies are orthogonal for the half-damped receiver.** For positive frequencies,
`|Σ_{n ≤ T} Re(Σ_t c_t n^{it})²/(n+1) − (Σ_t |c_t|²/2) log T| ≤ C(J, c)`. -/
theorem abs_sum_oscSum_sq_div_succ_sub_le {J : Finset ℝ} (hJ : ∀ t ∈ J, 0 < t) (c : ℝ → ℂ)
    {T : ℕ} (hT : 1 ≤ T) :
    |∑ n ∈ Icc 1 T, oscSum J c n ^ 2 / ((n : ℝ) + 1) -
        (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * Real.log T| ≤
      (∑ t ∈ J, ‖c t‖ ^ 2) + (∑ t ∈ J, ∑ s ∈ J, ‖c t‖ * ‖c s‖ *
        ((oscHarmonicBound (t - s) + 2) + (oscHarmonicBound (t + s) + 2))) / 2 := by
  set S : ℝ → ℂ := fun τ => ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((τ : ℂ) * I) /
    (((n : ℝ) + 1 : ℝ) : ℂ) with hS
  set H := ∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1) with hH
  have hterm : ∀ n ∈ Icc 1 T, oscSum J c n ^ 2 / ((n : ℝ) + 1) =
      (∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) *
          (((n : ℝ) : ℂ) ^ (((t - s : ℝ) : ℂ) * I) / (((n : ℝ) + 1 : ℝ) : ℂ))).re +
        (c t * c s * (((n : ℝ) : ℂ) ^ (((t + s : ℝ) : ℂ) * I) /
          (((n : ℝ) + 1 : ℝ) : ℂ))).re)) / 2 := by
    intro n hn
    rw [oscSum_sq_eq c (mem_Icc.mp hn).1]
    simp only [← mul_div_assoc, Complex.div_ofReal_re, ← add_div, ← sum_div]
    ring
  have hexp : ∑ n ∈ Icc 1 T, oscSum J c n ^ 2 / ((n : ℝ) + 1) =
      (∑ t ∈ J, ∑ s ∈ J, ((c t * (starRingEnd ℂ) (c s) * S (t - s)).re +
        (c t * c s * S (t + s)).re)) / 2 := by
    rw [sum_congr rfl hterm, ← sum_div, sum_comm]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [sum_add_distrib, ← Complex.re_sum, ← Complex.re_sum, ← mul_sum, ← mul_sum]
  have hpair : ∀ t ∈ J, ∀ s ∈ J,
      |(c t * (starRingEnd ℂ) (c s) * S (t - s)).re + (c t * c s * S (t + s)).re -
          (if t = s then ‖c t‖ ^ 2 * H else 0)| ≤
        ‖c t‖ * ‖c s‖ * ((oscHarmonicBound (t - s) + 2) + (oscHarmonicBound (t + s) + 2)) := by
    intro t ht s hs
    have hts : t + s ≠ 0 := by have := hJ t ht; have := hJ s hs; linarith
    have hB1 := oscHarmonicBound_nonneg (t - s)
    have hS2 : ‖S (t + s)‖ ≤ oscHarmonicBound (t + s) + 2 := norm_sum_cpow_I_div_succ_le hts T
    have h2 : |(c t * c s * S (t + s)).re| ≤ ‖c t‖ * ‖c s‖ * (oscHarmonicBound (t + s) + 2) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left hS2 (by positivity)
    have hnn : 0 ≤ ‖c t‖ * ‖c s‖ := by positivity
    split_ifs with hst
    · rw [← hst] at h2 hB1 hnn ⊢
      have hS0 : S (t - t) = (H : ℂ) := by simp [hS, hH]
      have hcc : c t * (starRingEnd ℂ) (c t) = ((‖c t‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [hS0, hcc, ← Complex.ofReal_mul, Complex.ofReal_re,
        show ‖c t‖ ^ 2 * H + (c t * c t * S (t + t)).re - ‖c t‖ ^ 2 * H =
          (c t * c t * S (t + t)).re by ring]
      have : 0 ≤ ‖c t‖ * ‖c t‖ * (oscHarmonicBound (t - t) + 2) :=
        mul_nonneg hnn (by linarith)
      calc _ ≤ ‖c t‖ * ‖c t‖ * (oscHarmonicBound (t + t) + 2) := h2
        _ ≤ _ := by nlinarith
    · have hne : t - s ≠ 0 := sub_ne_zero.mpr hst
      have hS1 : ‖S (t - s)‖ ≤ oscHarmonicBound (t - s) + 2 := norm_sum_cpow_I_div_succ_le hne T
      have h1 : |(c t * (starRingEnd ℂ) (c s) * S (t - s)).re| ≤
          ‖c t‖ * ‖c s‖ * (oscHarmonicBound (t - s) + 2) := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left hS1 (by positivity)
      rw [sub_zero]
      refine (abs_add_le _ _).trans ?_
      linarith
  have hdiag : ∑ t ∈ J, ∑ s ∈ J, (if t = s then ‖c t‖ ^ 2 * H else 0) =
      (∑ t ∈ J, ‖c t‖ ^ 2) * H := by
    rw [sum_mul]
    exact sum_congr rfl fun t ht => by rw [sum_ite_eq, if_pos ht]
  have hcross : |∑ n ∈ Icc 1 T, oscSum J c n ^ 2 / ((n : ℝ) + 1) -
      (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * H| ≤ (∑ t ∈ J, ∑ s ∈ J, ‖c t‖ * ‖c s‖ *
        ((oscHarmonicBound (t - s) + 2) + (oscHarmonicBound (t + s) + 2))) / 2 := by
    rw [hexp, show (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * H = (∑ t ∈ J, ‖c t‖ ^ 2) * H / 2 by ring, ← hdiag,
      ← sub_div, ← sum_sub_distrib, abs_div, abs_two]
    refine div_le_div_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t ht => ?_))
      (by norm_num)
    rw [← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s hs => hpair t ht s hs)
  have hlog := abs_sum_one_div_succ_sub_log_le hT
  rw [← hH] at hlog
  have hc0 : 0 ≤ (∑ t ∈ J, ‖c t‖ ^ 2) / 2 := by positivity
  calc |∑ n ∈ Icc 1 T, oscSum J c n ^ 2 / ((n : ℝ) + 1) - (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * Real.log T|
      = |(∑ n ∈ Icc 1 T, oscSum J c n ^ 2 / ((n : ℝ) + 1) - (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * H) +
          (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * (H - Real.log T)| := by ring_nf
    _ ≤ (∑ t ∈ J, ∑ s ∈ J, ‖c t‖ * ‖c s‖ *
          ((oscHarmonicBound (t - s) + 2) + (oscHarmonicBound (t + s) + 2))) / 2 +
          (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * 2 := by
        refine (abs_add_le _ _).trans (add_le_add hcross ?_)
        rw [abs_mul, abs_of_nonneg hc0]
        exact mul_le_mul_of_nonneg_left hlog hc0
    _ = _ := by ring

/-! ### The spectral law -/

/-- **The half-damped receiver is diagonal on the probe spectrum.** For a finite set `J` of
positive frequencies and real coefficients `α_t`,
`E_T(Σ_t α_t d^{-1/2} cos(t log d)) / log T → Σ_t α_t² |ζ(½ + it)|²/(2|½ + it|²)`. -/
theorem tendsto_halfProbeCombination_energy_div_log {J : Finset ℝ} (hJ : ∀ t ∈ J, 0 < t)
    (α : ℝ → ℝ) :
    Tendsto (fun T : ℕ => weightPronicEnergy (halfProbeCombination J α)
        (∑' d : ℕ, halfProbeCombination J α d / d) T / Real.log T) atTop
      (𝓝 (∑ t ∈ J, α t ^ 2 * ‖riemannZeta (oscillationExponent (1 / 2) t)‖ ^ 2 /
        (2 * ‖oscillationExponent (1 / 2) t‖ ^ 2))) := by
  set c : ℝ → ℂ := fun t => (α t : ℂ) * probeAmp (1 / 2) t with hc
  have hκ : ∑ t ∈ J, α t ^ 2 * ‖riemannZeta (oscillationExponent (1 / 2) t)‖ ^ 2 /
      (2 * ‖oscillationExponent (1 / 2) t‖ ^ 2) = (∑ t ∈ J, ‖c t‖ ^ 2) / 2 := by
    rw [sum_div]
    refine sum_congr rfl fun t _ => ?_
    rw [hc]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, probeAmp, norm_div]
    rw [mul_pow, sq_abs, div_pow]
    ring
  rw [hκ]
  set K := ∑ t ∈ J, |α t| * floorSumRate (oscillationExponent (1 / 2) t) with hK
  have hK0 : 0 ≤ K := sum_nonneg fun t _ => mul_nonneg (abs_nonneg _)
    (floorSumRate_nonneg (by rw [oscillationExponent_re]; norm_num)
      (by rw [oscillationExponent_re]; norm_num))
  refine tendsto_div_log_of_sqrt_approx (x := fun T => pronicNorm (halfProbeMain J α) T)
    (B := K * Real.sqrt (1 + 1 / (1 / 2 : ℝ)))
    (C := (∑ t ∈ J, ‖c t‖ ^ 2) + (∑ t ∈ J, ∑ s ∈ J, ‖c t‖ * ‖c s‖ *
      ((oscHarmonicBound (t - s) + 2) + (oscHarmonicBound (t + s) + 2))) / 2) (by positivity)
    (fun T => sum_nonneg fun n _ => by positivity) (fun T => pronicNorm_nonneg _ _)
    (fun T _ => ?_) (fun T hT => ?_)
  · -- the receiver is its main term up to a bounded norm
    rw [weightPronicEnergy_eq_sq_pronicNorm, Real.sqrt_sq (pronicNorm_nonneg _ _)]
    refine (abs_pronicNorm_sub_le _ _ T).trans ?_
    have hrem : ∀ n, 1 ≤ n → |weightCenteredPrefix (halfProbeCombination J α)
        (∑' d : ℕ, halfProbeCombination J α d / d) n - halfProbeMain J α n| ≤
          K * Real.sqrt n ^ (1 - 1 / 2 : ℝ) := by
      intro n hn
      rw [weightCenteredPrefix_halfProbeCombination, halfProbeMain, ← sum_sub_distrib, hK,
        sum_mul]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun t _ => ?_)
      have h := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le (ε := 1 / 2)
        (by norm_num) (by norm_num) t hn
      have e : probeMain (1 / 2) t n = (riemannZeta (oscillationExponent (1 / 2) t) *
          ((n : ℝ) : ℂ) ^ oscillationExponent (1 / 2) t / oscillationExponent (1 / 2) t).re := by
        unfold probeMain probeAmp; congr 1; ring
      rw [← mul_sub, abs_mul, e, mul_assoc]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    have h := sum_sq_le_of_abs_le_sqrt_rpow (ε := 1 / 2) (by norm_num)
      (f := fun n => weightCenteredPrefix (halfProbeCombination J α)
        (∑' d : ℕ, halfProbeCombination J α d / d) n - halfProbeMain J α n) hrem T
    rw [pronicNorm]
    calc Real.sqrt _ ≤ Real.sqrt (K ^ 2 * (1 + 1 / (1 / 2 : ℝ))) := Real.sqrt_le_sqrt h
      _ = K * Real.sqrt (1 + 1 / (1 / 2 : ℝ)) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0]
  · -- the main term carries the diagonal energy
    have hM : pronicNorm (halfProbeMain J α) T ^ 2 =
        ∑ n ∈ Icc 1 T, oscSum J c n ^ 2 / ((n : ℝ) + 1) := by
      rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
      refine sum_congr rfl fun n hn => ?_
      have hn1 := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [halfProbeMain_eq J α hn1, mul_pow, Real.sq_sqrt hn0.le, ← hc]
      field_simp
    show |pronicNorm (halfProbeMain J α) T ^ 2 - (∑ t ∈ J, ‖c t‖ ^ 2) / 2 * Real.log T| ≤ _
    rw [hM]
    exact abs_sum_oscSum_sq_div_succ_sub_le hJ c hT

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
