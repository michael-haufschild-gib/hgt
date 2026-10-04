import GaloisForLFunctions.RHTower.LiClockFiniteTopSinePacket
import GaloisForLFunctions.RHTower.LiClockSineImaginaryEnvelope
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockTopFrequency
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineDecay
import GaloisForLFunctions.RHTower.LiEvenCrossActualCurrentClockRegularity
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

/-!
# Top-packet oscillation of the literal reciprocal sine response

Let `F(t) = Σ_q r_q sin(t r_q)` be the literal actual response, `r_q = (xiSpectralPoint q)⁻¹`,
and `S(w) = liEvenCrossActualCurrentClockSeries w`, so that `F(t) = t S(t²/16)`.

For a finite family of complex frequencies `w_j` with common absolute imaginary part `b > 0`
and nonzero real parts `x_j`, the normalized packet `e^{-bt} Σ_j Re(w_j sin(t w_j))` differs from
the trigonometric profile `P(t) = Σ_j (x_j sin(t x_j) - b cos(t x_j))/2` by at most
`e^{-2bt} Σ_j (|x_j| + b)/2`.  The profile has a bounded primitive and the negative value
`P(0) = -b·#/2`; simultaneous phase recurrence returns the primitive to its initial value along
cofinal clocks, so `P` cannot be nonpositive everywhere.  Shifted recurrence then gives cofinal
clocks along which the normalized packet tends to a positive limit, and unshifted recurrence
gives a negative limit.

Applied to the actual source under failure of RH (finite attained top packet with a strict
remainder gap), this gives the exact leading asymptotic `F(t) = e^{bt}P(t) + O(e^{-bt} + t e^{b₂t})`,
cofinal values of `S` above every bound and below every bound, and cofinal zeros of `S`.
Combined with RH-conditional decay this gives the unconditional `liminf_{w→∞} |S(w)| = 0`.
-/

open Complex Filter Topology Set
open scoped BigOperators Classical
namespace RHTower
noncomputable section

section Profile

variable {ι : Type*} [Fintype ι]

/-- The leading trigonometric profile of a finite top sine packet with real parts `x` and common
absolute imaginary part `b`. -/
def liClockTopSineProfile (x : ι → ℝ) (b t : ℝ) : ℝ :=
  ∑ j, (x j * Real.sin (t * x j) - b * Real.cos (t * x j)) / 2

/-- The bounded primitive of the top profile. -/
def liClockTopSinePrimitive (x : ι → ℝ) (b t : ℝ) : ℝ :=
  ∑ j, (-Real.cos (t * x j) - b * Real.sin (t * x j) / x j) / 2

theorem hasDerivAt_liClockTopSinePrimitive (x : ι → ℝ) (b : ℝ) (hx : ∀ j, x j ≠ 0)
    (t : ℝ) :
    HasDerivAt (liClockTopSinePrimitive x b) (liClockTopSineProfile x b t) t := by
  unfold liClockTopSinePrimitive liClockTopSineProfile
  apply HasDerivAt.fun_sum
  intro j _
  have hxj := hx j
  have hl : HasDerivAt (fun u : ℝ => u * x j) (x j) t := hasDerivAt_mul_const (x j)
  have hc : HasDerivAt (fun u : ℝ => Real.cos (u * x j)) (-Real.sin (t * x j) * x j) t :=
    hl.cos
  have hs : HasDerivAt (fun u : ℝ => Real.sin (u * x j)) (Real.cos (t * x j) * x j) t :=
    hl.sin
  have h := ((hc.neg).sub ((hs.const_mul b).div_const (x j))).div_const 2
  have hv : (-(-Real.sin (t * x j) * x j) - b * (Real.cos (t * x j) * x j) / x j) / 2 =
      (x j * Real.sin (t * x j) - b * Real.cos (t * x j)) / 2 := by
    field_simp
  rw [hv] at h
  exact h

theorem continuous_liClockTopSineProfile (x : ι → ℝ) (b : ℝ) :
    Continuous (liClockTopSineProfile x b) := by
  unfold liClockTopSineProfile
  fun_prop

theorem liClockTopSineProfile_zero (x : ι → ℝ) (b : ℝ) :
    liClockTopSineProfile x b 0 = -b * (Fintype.card ι : ℝ) / 2 := by
  unfold liClockTopSineProfile
  simp only [zero_mul, Real.sin_zero, mul_zero, Real.cos_zero, mul_one, zero_sub]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Simultaneous phase recurrence for finitely many real frequencies, in cosine/sine form. -/
theorem exists_liClockPhaseRecurrence (x : ι → ℝ) :
    ∃ τ : ℕ → ℝ, (∀ n : ℕ, (n : ℝ) + 1 ≤ τ n) ∧ Tendsto τ atTop atTop ∧
      (∀ j, Tendsto (fun n => Real.cos (τ n * x j)) atTop (𝓝 1)) ∧
      (∀ j, Tendsto (fun n => Real.sin (τ n * x j)) atTop (𝓝 0)) := by
  classical
  have hrec (n : ℕ) : ∃ t : ℝ, (n : ℝ) + 1 ≤ t ∧
      ∀ j, ‖GaloisForLFunctions.bohrChar (-x j) t - 1‖ ≤ 1 / ((n : ℝ) + 1) :=
    exists_simultaneous_phase_recurrence (fun j => -x j) (by positivity) ((n : ℝ) + 1)
  choose τ hτ hphase using hrec
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat
  have hchar (j : ι) :
      Tendsto (fun n => GaloisForLFunctions.bohrChar (-x j) (τ n)) atTop (𝓝 1) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => by simpa only [dist_eq_norm] using hphase n j) heps
  have hchar_eq (n : ℕ) (j : ι) :
      GaloisForLFunctions.bohrChar (-x j) (τ n) =
        Complex.exp ((τ n * x j : ℝ) * Complex.I) := by
    have ha : - (-x j * τ n) = τ n * x j := by ring
    rw [GaloisForLFunctions.bohrChar, ha]
  refine ⟨τ, hτ, tendsto_atTop_mono hτ hnat, fun j => ?_, fun j => ?_⟩
  · simpa only [Function.comp_def, hchar_eq,
      Complex.exp_ofReal_mul_I_re, Complex.one_re] using
      (Complex.continuous_re.tendsto (1 : ℂ)).comp (hchar j)
  · simpa only [Function.comp_def, hchar_eq,
      Complex.exp_ofReal_mul_I_im, Complex.one_im] using
      (Complex.continuous_im.tendsto (1 : ℂ)).comp (hchar j)

/-- Shifted recurrence: along recurrent clocks translated by `s`, every phase returns to its
value at `s`. -/
theorem tendsto_cos_sin_shift_of_recurrence {τ : ℕ → ℝ} {y : ℝ}
    (hc : Tendsto (fun n => Real.cos (τ n * y)) atTop (𝓝 1))
    (hs : Tendsto (fun n => Real.sin (τ n * y)) atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun n => Real.cos ((τ n + s) * y)) atTop (𝓝 (Real.cos (s * y))) ∧
      Tendsto (fun n => Real.sin ((τ n + s) * y)) atTop (𝓝 (Real.sin (s * y))) := by
  have hcs : ∀ n, Real.cos ((τ n + s) * y) =
      Real.cos (τ n * y) * Real.cos (s * y) - Real.sin (τ n * y) * Real.sin (s * y) := by
    intro n; rw [add_mul, Real.cos_add]
  have hsn : ∀ n, Real.sin ((τ n + s) * y) =
      Real.sin (τ n * y) * Real.cos (s * y) + Real.cos (τ n * y) * Real.sin (s * y) := by
    intro n; rw [add_mul, Real.sin_add]
  constructor
  · simp_rw [hcs]
    simpa using (hc.mul_const (Real.cos (s * y))).sub (hs.mul_const (Real.sin (s * y)))
  · simp_rw [hsn]
    simpa using (hs.mul_const (Real.cos (s * y))).add (hc.mul_const (Real.sin (s * y)))

/-- The top profile returns to its value at any fixed clock along shifted recurrent clocks. -/
theorem tendsto_liClockTopSineProfile_shift {τ : ℕ → ℝ} (x : ι → ℝ) (b s : ℝ)
    (hc : ∀ j, Tendsto (fun n => Real.cos (τ n * x j)) atTop (𝓝 1))
    (hs : ∀ j, Tendsto (fun n => Real.sin (τ n * x j)) atTop (𝓝 0)) :
    Tendsto (fun n => liClockTopSineProfile x b (τ n + s)) atTop
      (𝓝 (liClockTopSineProfile x b s)) := by
  unfold liClockTopSineProfile
  apply tendsto_finsetSum
  intro j _
  obtain ⟨hcj, hsj⟩ := tendsto_cos_sin_shift_of_recurrence (hc j) (hs j) s
  exact (((hsj.const_mul (x j)).sub (hcj.const_mul b))).div_const 2

private theorem tendsto_primitive_recurrence {τ : ℕ → ℝ} (x : ι → ℝ) (b : ℝ)
    (hc : ∀ j, Tendsto (fun n => Real.cos (τ n * x j)) atTop (𝓝 1))
    (hs : ∀ j, Tendsto (fun n => Real.sin (τ n * x j)) atTop (𝓝 0)) :
    Tendsto (fun n => liClockTopSinePrimitive x b (τ n)) atTop
      (𝓝 (liClockTopSinePrimitive x b 0)) := by
  unfold liClockTopSinePrimitive
  apply tendsto_finsetSum
  intro j _
  have h := (((hc j).neg).sub (((hs j).const_mul b).div_const (x j))).div_const 2
  simpa only [zero_mul, Real.cos_zero, Real.sin_zero, mul_zero, zero_div] using h

/-- A top profile with nonzero real frequencies takes a strictly positive value.  Its primitive
is bounded and returns to its initial value along recurrent clocks, while `P(0) < 0`. -/
theorem exists_liClockTopSineProfile_pos [Nonempty ι] (x : ι → ℝ) {b : ℝ} (hb : 0 < b)
    (hx : ∀ j, x j ≠ 0) : ∃ s, 0 < liClockTopSineProfile x b s := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  set P := liClockTopSineProfile x b with hPdef
  set G := liClockTopSinePrimitive x b with hGdef
  have hPc : Continuous P := continuous_liClockTopSineProfile x b
  have hP0 : P 0 < 0 := by
    rw [hPdef, liClockTopSineProfile_zero]
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    nlinarith
  have hG : ∀ t, HasDerivAt G (P t) t := hasDerivAt_liClockTopSinePrimitive x b hx
  have hFTC : ∀ T, ∫ s in (0 : ℝ)..T, P s = G T - G 0 := fun T =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hG s)
      (hPc.intervalIntegrable _ _)
  -- a short initial interval where `-P > 0`
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), P s < 0 := hPc.continuousAt.eventually (gt_mem_nhds hP0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hδ : (0 : ℝ) < ε / 2 := half_pos hε
  have hpos : 0 < ∫ s in (0 : ℝ)..ε / 2, -P s := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (f := fun s => -P s)
      (hPc.neg.intervalIntegrable _ _) _ hδ
    intro s hs
    show 0 < -P s
    have hd : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
      linarith [hs.2]
    linarith [hball hd]
  -- monotonicity of the nonnegative integral
  have hmono : ∀ T, ε / 2 ≤ T →
      (∫ s in (0 : ℝ)..ε / 2, -P s) ≤ ∫ s in (0 : ℝ)..T, -P s := by
    intro T hT
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (f := fun s => -P s)
      (a := 0) (b := ε / 2) (c := T) (μ := MeasureTheory.volume)
      (hPc.neg.intervalIntegrable _ _) (hPc.neg.intervalIntegrable _ _)
    have : 0 ≤ ∫ s in (ε / 2)..T, -P s :=
      intervalIntegral.integral_nonneg hT (fun s _ => by linarith [hcon s])
    linarith
  obtain ⟨τ, -, hτ, hc, hs⟩ := exists_liClockPhaseRecurrence x
  have hGτ : Tendsto (fun n => G (τ n)) atTop (𝓝 (G 0)) :=
    tendsto_primitive_recurrence x b hc hs
  have hint : Tendsto (fun n => ∫ s in (0 : ℝ)..τ n, -P s) atTop (𝓝 0) := by
    have heq : ∀ n, (∫ s in (0 : ℝ)..τ n, -P s) = G 0 - G (τ n) := by
      intro n
      rw [intervalIntegral.integral_neg, hFTC]
      ring
    simp_rw [heq]
    simpa using (tendsto_const_nhds (x := G 0)).sub hGτ
  have hge : ∀ᶠ n in atTop, (∫ s in (0 : ℝ)..ε / 2, -P s) ≤ ∫ s in (0 : ℝ)..τ n, -P s :=
    (hτ.eventually (eventually_ge_atTop (ε / 2))).mono fun n hn => hmono _ hn
  have := ge_of_tendsto hint hge
  linarith

/-- Exact normalized top-packet expansion with its explicit exponentially small error. -/
theorem abs_liClockTopSinePacket_sub_profile_le (w : ι → ℂ) {b : ℝ} (hb : 0 ≤ b)
    (hw : ∀ j, |(w j).im| = b) (t : ℝ) :
    |Real.exp (-b * t) * ∑ j, (w j * Complex.sin ((t : ℂ) * w j)).re -
        liClockTopSineProfile (fun j => (w j).re) b t| ≤
      Real.exp (-2 * b * t) * ∑ j, (|(w j).re| + b) / 2 := by
  have hexp : ∀ j, Real.exp (-b * t) * (w j * Complex.sin ((t : ℂ) * w j)).re -
      ((w j).re * Real.sin (t * (w j).re) - b * Real.cos (t * (w j).re)) / 2 =
      Real.exp (-2 * b * t) *
        ((w j).re * Real.sin (t * (w j).re) + b * Real.cos (t * (w j).re)) / 2 := by
    intro j
    rw [liClockTopSineAtom_normalized_eq (w j) (hw j)]
    ring
  rw [Finset.mul_sum, liClockTopSineProfile, ← Finset.sum_sub_distrib]
  simp_rw [hexp]
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_two, mul_div_assoc]
  gcongr
  calc |(w j).re * Real.sin (t * (w j).re) + b * Real.cos (t * (w j).re)|
      ≤ |(w j).re * Real.sin (t * (w j).re)| + |b * Real.cos (t * (w j).re)| :=
        abs_add_le _ _
    _ ≤ |(w j).re| * 1 + b * 1 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hb]
        gcongr
        · exact Real.abs_sin_le_one _
        · exact Real.abs_cos_le_one _
    _ = |(w j).re| + b := by ring

/-- The normalized top packet is asymptotic to its trigonometric profile. -/
theorem tendsto_liClockTopSinePacket_sub_profile (w : ι → ℂ) {b : ℝ} (hb : 0 < b)
    (hw : ∀ j, |(w j).im| = b) :
    Tendsto (fun t : ℝ => Real.exp (-b * t) * ∑ j, (w j * Complex.sin ((t : ℂ) * w j)).re -
        liClockTopSineProfile (fun j => (w j).re) b t) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-2 * b * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hexp : Tendsto (fun t : ℝ => Real.exp (-2 * b * t) * ∑ j, (|(w j).re| + b) / 2)
      atTop (𝓝 0) := by
    simpa using he.mul_const (∑ j, (|(w j).re| + b) / 2)
  exact squeeze_zero_norm (fun t => by
    rw [Real.norm_eq_abs]; exact abs_liClockTopSinePacket_sub_profile_le w hb.le hw t) hexp

/-- A finite top packet with nonzero real frequencies has cofinal clocks along which its
normalized value tends to a strictly positive limit. -/
theorem exists_liClockFiniteTopSinePacket_positive_limit [Nonempty ι] (w : ι → ℂ) {b : ℝ}
    (hb : 0 < b) (hw : ∀ j, |(w j).im| = b) (hre : ∀ j, (w j).re ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
      Tendsto (fun n => Real.exp (-b * t n) *
        ∑ j, (w j * Complex.sin ((t n : ℂ) * w j)).re) atTop (𝓝 c) := by
  obtain ⟨s, hs⟩ := exists_liClockTopSineProfile_pos (fun j => (w j).re) hb hre
  obtain ⟨τ, -, hτ, hc, hsn⟩ := exists_liClockPhaseRecurrence (fun j => (w j).re)
  have hτs : Tendsto (fun n => τ n + s) atTop atTop := tendsto_atTop_add_const_right _ s hτ
  refine ⟨_, hs, fun n => τ n + s, hτs, ?_⟩
  have hP := tendsto_liClockTopSineProfile_shift (fun j => (w j).re) b s hc hsn
  have hD := (tendsto_liClockTopSinePacket_sub_profile w hb hw).comp hτs
  simpa [Function.comp_def] using hD.add hP

end Profile

section Actual

/-- Actual reciprocal Xi frequencies have nonzero real part: every copy has a nonzero ordinate. -/
theorem re_inv_xiSpectralPoint_ne_zero (q : XiZeroCopy) : ((xiSpectralPoint q)⁻¹).re ≠ 0 := by
  have hre : (xiSpectralPoint q).re ≠ 0 := by
    have h := xiZeroCopy_fortyOne_div_two_lt_im_sq q
    have hreq : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
    rw [hreq]
    intro h0
    rw [h0] at h
    norm_num at h
  rw [Complex.inv_re]
  exact div_ne_zero hre (Complex.normSq_pos.2 (xiSpectralPoint_ne_zero q)).ne'

private theorem summable_actual_sineAtom_ite (P : Set XiZeroCopy) (t : ℝ) :
    Summable (fun q : XiZeroCopy => if q ∈ P then liEvenCrossActualClockSineAtom t q else 0) := by
  classical
  refine Summable.of_norm_bounded (summable_norm_liEvenCrossActualClockSineAtom t) fun q => ?_
  by_cases hq : q ∈ P <;> simp [hq]

private theorem summable_actual_sineAtom_ite' (P : Set XiZeroCopy) (t : ℝ) :
    Summable (fun q : XiZeroCopy => if q ∈ P then 0 else liEvenCrossActualClockSineAtom t q) := by
  classical
  refine Summable.of_norm_bounded (summable_norm_liEvenCrossActualClockSineAtom t) fun q => ?_
  by_cases hq : q ∈ P <;> simp [hq]

/-- Exact finite-packet/complement splitting of the complete multiplicity-copy sine trace. -/
private theorem tsum_sineAtom_split (P : Set XiZeroCopy) (hP : P.Finite) (t : ℝ) :
    (∑' q : XiZeroCopy, liEvenCrossActualClockSineAtom t q) =
      (∑ q : hP.toFinset, liEvenCrossActualClockSineAtom t q) +
        ∑' q : XiZeroCopy, if q ∈ P then 0 else liEvenCrossActualClockSineAtom t q := by
  classical
  have hsplit : (fun q => liEvenCrossActualClockSineAtom t q) = fun q =>
      (if q ∈ P then liEvenCrossActualClockSineAtom t q else 0) +
        (if q ∈ P then 0 else liEvenCrossActualClockSineAtom t q) := by
    funext q
    by_cases hq : q ∈ P <;> simp [hq]
  rw [hsplit, Summable.tsum_add (summable_actual_sineAtom_ite P t)
    (summable_actual_sineAtom_ite' P t)]
  congr 1
  rw [Finset.sum_coe_sort hP.toFinset (fun q => liEvenCrossActualClockSineAtom t q)]
  have hfin : (∑' q : XiZeroCopy, if q ∈ P then liEvenCrossActualClockSineAtom t q else 0) =
      ∑ q ∈ hP.toFinset, (if q ∈ P then liEvenCrossActualClockSineAtom t q else 0) := by
    apply tsum_eq_sum
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    simp [hq]
  rw [hfin]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Set.Finite.mem_toFinset] at hq
  simp [hq]

/-- **Top-packet leading asymptotic under failure of RH.**  There is a finite nonempty packet of
multiplicity copies with maximal reciprocal growth rate `b > 0` and a strict remainder gap `b₂ < b`,
such that the literal response is `e^{bt}P(t)` up to `L e^{-bt} + A t e^{b₂t}`, with `P` the exact
trigonometric profile of the packet and `A` the complete reciprocal-square source mass. -/
theorem liEvenCrossActualClockResponse_topPacket_of_not_rh (hnot : ¬RiemannHypothesis) :
    ∃ b : ℝ, 0 < b ∧ ∃ Q : Finset XiZeroCopy, Q.Nonempty ∧
      (∀ q, q ∈ Q ↔ liEvenCrossActualClockReciprocalGrowthRate q = b) ∧
      ∃ b₂ : ℝ, 0 ≤ b₂ ∧ b₂ < b ∧
        (∀ q, q ∉ Q → liEvenCrossActualClockReciprocalGrowthRate q ≤ b₂) ∧
        (∀ t : ℝ, 0 ≤ t →
          |liEvenCrossActualClockResponse t - Real.exp (b * t) *
              liClockTopSineProfile (fun q : Q => ((xiSpectralPoint q)⁻¹).re) b t| ≤
            (∑ q : Q, (|((xiSpectralPoint q)⁻¹).re| + b) / 2) * Real.exp (-b * t) +
            (∑' q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖ ^ 2) * t * Real.exp (b₂ * t)) ∧
        Tendsto (fun t : ℝ => Real.exp (-b * t) * liEvenCrossActualClockResponse t -
            liClockTopSineProfile (fun q : Q => ((xiSpectralPoint q)⁻¹).re) b t)
          atTop (𝓝 0) := by
  classical
  obtain ⟨b, hb, hfin, hne, -, b₂, hb₂0, hb₂, hgap⟩ :=
    exists_liEvenCrossActualClockTopPacket_of_not_rh hnot
  set P := liEvenCrossActualClockTopPacket b with hPdef
  set Q := hfin.toFinset with hQdef
  have hmem : ∀ q, q ∈ Q ↔ liEvenCrossActualClockReciprocalGrowthRate q = b := by
    intro q
    rw [hQdef, Set.Finite.mem_toFinset]
    rfl
  have hw : ∀ q : Q, |((xiSpectralPoint q)⁻¹).im| = b := fun q => (hmem q).1 q.2
  have hβ : ∀ q, q ∉ P → |((xiSpectralPoint q)⁻¹).im| ≤ b₂ := fun q hq => hgap q hq
  set w : Q → ℂ := fun q => (xiSpectralPoint q)⁻¹
  have hsplitre : ∀ t, liEvenCrossActualClockResponse t =
      (∑ q : Q, (w q * Complex.sin ((t : ℂ) * w q)).re) +
        (∑' q : XiZeroCopy, if q ∈ P then 0 else liEvenCrossActualClockSineAtom t q).re := by
    intro t
    rw [liEvenCrossActualClockResponse_eq_re_tsum_sine, tsum_sineAtom_split P hfin t,
      Complex.add_re, Complex.re_sum]
    rfl
  refine ⟨b, hb, Q, ?_, hmem, b₂, hb₂0, hb₂, fun q hq => hgap q (by
    intro hqP; exact hq ((hmem q).2 hqP)), ?_, ?_⟩
  · obtain ⟨q, hq⟩ := hne
    exact ⟨q, (hmem q).2 hq⟩
  · intro t ht
    have hpk := abs_liClockTopSinePacket_sub_profile_le w hb.le hw t
    have hcomp := liEvenCrossActualClock_norm_complement_le P hb₂0 hβ ht
    have htop : |(∑ q : Q, (w q * Complex.sin ((t : ℂ) * w q)).re) -
        Real.exp (b * t) * liClockTopSineProfile (fun q => (w q).re) b t| ≤
        (∑ q : Q, (|(w q).re| + b) / 2) * Real.exp (-b * t) := by
      have hfac : (∑ q : Q, (w q * Complex.sin ((t : ℂ) * w q)).re) -
          Real.exp (b * t) * liClockTopSineProfile (fun q => (w q).re) b t =
          Real.exp (b * t) * (Real.exp (-b * t) * ∑ q : Q, (w q * Complex.sin ((t : ℂ) * w q)).re -
            liClockTopSineProfile (fun q => (w q).re) b t) := by
        rw [mul_sub, ← mul_assoc, ← Real.exp_add]
        simp
      rw [hfac, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (b * t) * |Real.exp (-b * t) *
              ∑ q : Q, (w q * Complex.sin ((t : ℂ) * w q)).re -
            liClockTopSineProfile (fun q => (w q).re) b t|
          ≤ Real.exp (b * t) * (Real.exp (-2 * b * t) * ∑ q : Q, (|(w q).re| + b) / 2) :=
            mul_le_mul_of_nonneg_left hpk (Real.exp_pos _).le
        _ = (∑ q : Q, (|(w q).re| + b) / 2) * (Real.exp (b * t) * Real.exp (-2 * b * t)) := by
            ring
        _ = _ := by
            have he : Real.exp (b * t) * Real.exp (-2 * b * t) = Real.exp (-b * t) := by
              rw [← Real.exp_add]; ring_nf
            rw [he]
    rw [hsplitre t, show ∀ X Y Z : ℝ, X + Y - Z = (X - Z) + Y from fun X Y Z => by ring]
    exact (abs_add_le _ _).trans (add_le_add htop ((Complex.abs_re_le_norm _).trans hcomp))
  · have hpk := tendsto_liClockTopSinePacket_sub_profile w hb hw
    have hcomp := liEvenCrossActualClock_tendsto_normalized_complement_zero P hb₂0 hβ hb₂
    have hcre : Tendsto (fun t : ℝ => Real.exp (-b * t) *
        (∑' q : XiZeroCopy, if q ∈ P then 0 else liEvenCrossActualClockSineAtom t q).re)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, Complex.re_ofReal_mul, Complex.zero_re] using
        (Complex.continuous_re.tendsto 0).comp hcomp
    have h := hpk.add hcre
    rw [add_zero] at h
    refine h.congr fun t => ?_
    rw [hsplitre t]
    ring

private theorem tendsto_normalized_response_sub_packet (hnot : ¬RiemannHypothesis) :
    ∃ b : ℝ, 0 < b ∧ ∃ Q : Finset XiZeroCopy, Q.Nonempty ∧
      (∀ q : Q, |((xiSpectralPoint q)⁻¹).im| = b) ∧
      Tendsto (fun t : ℝ => Real.exp (-b * t) * liEvenCrossActualClockResponse t -
          Real.exp (-b * t) * ∑ q : Q,
            ((xiSpectralPoint q)⁻¹ * Complex.sin ((t : ℂ) * (xiSpectralPoint q)⁻¹)).re)
        atTop (𝓝 0) := by
  obtain ⟨b, hb, Q, hne, hmem, -, -, -, -, -, hlim⟩ :=
    liEvenCrossActualClockResponse_topPacket_of_not_rh hnot
  have hw : ∀ q : Q, |((xiSpectralPoint q)⁻¹).im| = b := fun q => (hmem q).1 q.2
  refine ⟨b, hb, Q, hne, hw, ?_⟩
  have hpk := tendsto_liClockTopSinePacket_sub_profile (fun q : Q => (xiSpectralPoint q)⁻¹) hb hw
  simpa using hlim.sub hpk

/-- **Signed oscillation under failure of RH.**  At the maximal reciprocal growth rate `b`, the
normalized literal response `e^{-bt}F(t)` has a strictly negative cofinal limit and a strictly
positive cofinal limit. -/
theorem liEvenCrossActualClockResponse_oscillation_of_not_rh (hnot : ¬RiemannHypothesis) :
    ∃ b : ℝ, 0 < b ∧
      (∃ c : ℝ, c < 0 ∧ ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
        Tendsto (fun n => Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n))
          atTop (𝓝 c)) ∧
      (∃ c : ℝ, 0 < c ∧ ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
        Tendsto (fun n => Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n))
          atTop (𝓝 c)) := by
  obtain ⟨b, hb, Q, hne, hw, hlim⟩ := tendsto_normalized_response_sub_packet hnot
  haveI : Nonempty Q := hne.coe_sort
  refine ⟨b, hb, ?_, ?_⟩
  · obtain ⟨t, -, ht, hneg⟩ := exists_liClockFiniteTopSinePacket_negative_limit
      (fun q : Q => (xiSpectralPoint q)⁻¹) hb hw
    have hcard : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
    refine ⟨-b * (Fintype.card Q : ℝ) / 2, by nlinarith, t, ht, ?_⟩
    simpa using (hlim.comp ht).add hneg
  · obtain ⟨c, hc, t, ht, hpos⟩ := exists_liClockFiniteTopSinePacket_positive_limit
      (fun q : Q => (xiSpectralPoint q)⁻¹) hb hw (fun q => re_inv_xiSpectralPoint_ne_zero q)
    refine ⟨c, hc, t, ht, ?_⟩
    simpa using (hlim.comp ht).add hpos

private theorem tendsto_exp_mul_div_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (b * t) / t) atTop atTop := by
  have h := (Real.tendsto_exp_div_pow_atTop 1).comp (tendsto_id.const_mul_atTop hb)
  have h2 := h.const_mul_atTop hb
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply, id, pow_one]
  field_simp

private theorem series_eq_response_div {t : ℝ} (ht : 0 < t) :
    liEvenCrossActualCurrentClockSeries (t ^ 2 / 16) = liEvenCrossActualClockResponse t / t := by
  rw [liEvenCrossActualClockResponse]
  field_simp

private theorem series_frequently_of_normalized_limit {b c : ℝ} (hb : 0 < b) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop)
    (hlim : Tendsto (fun n => Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n))
      atTop (𝓝 c)) (hc : c ≠ 0) :
    Tendsto (fun n => |liEvenCrossActualCurrentClockSeries (t n ^ 2 / 16)|) atTop atTop ∧
      (0 < c → ∀ᶠ n in atTop, 0 < liEvenCrossActualCurrentClockSeries (t n ^ 2 / 16)) ∧
      (c < 0 → ∀ᶠ n in atTop, liEvenCrossActualCurrentClockSeries (t n ^ 2 / 16) < 0) := by
  have hpos : ∀ᶠ n in atTop, 0 < t n := ht.eventually (eventually_gt_atTop 0)
  have hdiv := (tendsto_exp_mul_div_atTop hb).comp ht
  have habs : Tendsto (fun n => |Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n)|)
      atTop (𝓝 |c|) := hlim.abs
  have hprod := hdiv.atTop_mul_pos (abs_pos.2 hc) habs
  have hsign : ∀ n, 0 < t n → (0 < liEvenCrossActualCurrentClockSeries (t n ^ 2 / 16) ↔
      0 < Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n)) := by
    intro n hn
    rw [series_eq_response_div hn, div_pos_iff_of_pos_right hn, mul_pos_iff_of_pos_left
      (Real.exp_pos _)]
  have hsign' : ∀ n, 0 < t n → (liEvenCrossActualCurrentClockSeries (t n ^ 2 / 16) < 0 ↔
      Real.exp (-b * t n) * liEvenCrossActualClockResponse (t n) < 0) := by
    intro n hn
    rw [series_eq_response_div hn, div_neg_iff, mul_neg_iff]
    have he := Real.exp_pos (-b * t n)
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · exact Or.inl ⟨he, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact Or.inr ⟨h, hn⟩
      · linarith
  refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · refine hprod.congr' ?_
    filter_upwards [hpos] with n hn
    simp only [Function.comp_apply]
    rw [series_eq_response_div hn, abs_div, abs_of_pos hn, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (b * t n) * Real.exp (-b * t n) = 1 := by
      rw [← Real.exp_add, show b * t n + -b * t n = 0 by ring, Real.exp_zero]
    calc Real.exp (b * t n) / t n * (Real.exp (-b * t n) * |liEvenCrossActualClockResponse (t n)|)
        = (Real.exp (b * t n) * Real.exp (-b * t n)) * |liEvenCrossActualClockResponse (t n)| /
            t n := by ring
      _ = _ := by rw [he, one_mul]
  · filter_upwards [hlim.eventually (lt_mem_nhds hc), hpos] with n hn htn
    exact (hsign n htn).2 hn
  · filter_upwards [hlim.eventually (gt_mem_nhds hc), hpos] with n hn htn
    exact (hsign' n htn).2 hn

/-- Under failure of RH the literal clock series exceeds every bound at arbitrarily large clocks. -/
theorem liEvenCrossActualCurrentClockSeries_frequently_gt_of_not_rh
    (hnot : ¬RiemannHypothesis) (M : ℝ) :
    ∃ᶠ w in atTop, M < liEvenCrossActualCurrentClockSeries w := by
  obtain ⟨b, hb, -, c, hc, t, ht, hlim⟩ := liEvenCrossActualClockResponse_oscillation_of_not_rh hnot
  obtain ⟨habs, hsgn, -⟩ := series_frequently_of_normalized_limit hb ht hlim hc.ne'
  have hw : Tendsto (fun n => t n ^ 2 / 16) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp ht).atTop_div_const (by norm_num)
  refine hw.frequently (Filter.Eventually.frequently ?_)
  filter_upwards [habs.eventually (eventually_gt_atTop |M|), hsgn hc] with n hn hs
  rw [abs_of_pos hs] at hn
  exact (le_abs_self M).trans_lt hn

/-- Under failure of RH the literal clock series lies below every bound at arbitrarily large
clocks. -/
theorem liEvenCrossActualCurrentClockSeries_frequently_lt_of_not_rh
    (hnot : ¬RiemannHypothesis) (M : ℝ) :
    ∃ᶠ w in atTop, liEvenCrossActualCurrentClockSeries w < M := by
  obtain ⟨b, hb, ⟨c, hc, t, ht, hlim⟩, -⟩ := liEvenCrossActualClockResponse_oscillation_of_not_rh hnot
  obtain ⟨habs, -, hsgn⟩ := series_frequently_of_normalized_limit hb ht hlim hc.ne
  have hw : Tendsto (fun n => t n ^ 2 / 16) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp ht).atTop_div_const (by norm_num)
  refine hw.frequently (Filter.Eventually.frequently ?_)
  filter_upwards [habs.eventually (eventually_gt_atTop |M|), hsgn hc] with n hn hs
  rw [abs_of_neg hs] at hn
  linarith [neg_abs_le M]

/-- Under failure of RH the literal clock series has zeros at arbitrarily large clocks. -/
theorem liEvenCrossActualCurrentClockSeries_frequently_eq_zero_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    ∃ᶠ w in atTop, liEvenCrossActualCurrentClockSeries w = 0 := by
  rw [Filter.frequently_atTop]
  intro W
  obtain ⟨w₁, hw₁, h₁⟩ := Filter.frequently_atTop.1
    (liEvenCrossActualCurrentClockSeries_frequently_gt_of_not_rh hnot 0) W
  obtain ⟨w₂, hw₂, h₂⟩ := Filter.frequently_atTop.1
    (liEvenCrossActualCurrentClockSeries_frequently_lt_of_not_rh hnot 0) W
  have hivt := intermediate_value_uIcc (a := w₁) (b := w₂)
    continuous_liEvenCrossActualCurrentClockSeries.continuousOn
  have h0 : (0 : ℝ) ∈ uIcc (liEvenCrossActualCurrentClockSeries w₁)
      (liEvenCrossActualCurrentClockSeries w₂) := by
    rw [mem_uIcc]; right; exact ⟨h₂.le, h₁.le⟩
  obtain ⟨w, hw, hw0⟩ := hivt h0
  refine ⟨w, ?_, hw0⟩
  rw [mem_uIcc] at hw
  rcases hw with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith

/-- **Unconditional vanishing boundary.**  At arbitrarily large clocks the literal clock series
is arbitrarily small: it tends to zero under RH and has cofinal zeros otherwise. -/
theorem liEvenCrossActualCurrentClockSeries_frequently_abs_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ w in atTop, |liEvenCrossActualCurrentClockSeries w| < ε := by
  by_cases hRH : RiemannHypothesis
  · have h := tendsto_liEvenCrossActualCurrentClockSeries_atTop_zero_of_rh hRH
    have h0 : Tendsto (fun w => |liEvenCrossActualCurrentClockSeries w|) atTop (𝓝 0) := by
      simpa using h.abs
    exact (h0.eventually (gt_mem_nhds hε)).frequently
  · exact (liEvenCrossActualCurrentClockSeries_frequently_eq_zero_of_not_rh hRH).mono
      fun w hw => by rw [hw, abs_zero]; exact hε

/-- **Unconditional vanishing boundary**, as a limit inferior:
`liminf_{w→∞} |S(w)| = 0`. -/
theorem liminf_abs_liEvenCrossActualCurrentClockSeries :
    Filter.liminf (fun w => |liEvenCrossActualCurrentClockSeries w|) atTop = 0 := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun w => |liEvenCrossActualCurrentClockSeries w|) :=
    isBoundedUnder_of ⟨0, fun w => abs_nonneg _⟩
  have hcob : IsCoboundedUnder (· ≥ ·) atTop
      (fun w => |liEvenCrossActualCurrentClockSeries w|) := by
    refine ⟨1, fun a ha => ?_⟩
    have ha' : ∀ᶠ w in atTop, a ≤ |liEvenCrossActualCurrentClockSeries w| := ha
    have hfr := liEvenCrossActualCurrentClockSeries_frequently_abs_lt one_pos
    obtain ⟨w, hw1, hw2⟩ := (ha'.and_frequently hfr).exists
    exact hw1.trans hw2.le
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    exact Filter.liminf_le_of_frequently_le
      ((liEvenCrossActualCurrentClockSeries_frequently_abs_lt hε).mono fun w hw => hw.le) hbdd
  · exact Filter.le_liminf_of_le hcob (Filter.Eventually.of_forall fun w => abs_nonneg _)

end Actual

end
end RHTower
