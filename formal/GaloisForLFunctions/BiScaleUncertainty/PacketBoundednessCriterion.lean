import GaloisForLFunctions.BiScaleUncertainty.ProbeParsevalLaw
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeAbelCompleteness

/-!
# The growth exponent of a compact packet is the depth of the zeros it sees

For a real compact `C²` source `f` the stationary prime–polar packet is, beyond the support,
`P_f(τ) = A_f(τ) − Σ_ρ c_ρ e^{λ_ρ τ}` with `λ_ρ = ρ − 1/2`, `c_ρ = m_ρ f̂(γ_ρ)` and a bounded
archimedean tail `A_f` (`hasSum_packet_explicit_formula`).

**Packet growth law** (`packet_growth_iff`). For `σ ≥ 0`,
`P_f(τ) = O(e^{στ})` **iff** `f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`.

A source is a spectral filter: its packet grows exactly at the largest depth among the zeros it
does not annihilate. Consequences:

* `packet_bounded_iff_blind`: `P_f` is bounded iff `f` is blind to every zero right of the line.
* `riemannHypothesis_iff_forall_packet_bounded`: RH iff every compact packet is bounded.
* `xiZeroHalfPlaneBound_iff_forall_packet_growth`: the zero width `β` is the universal packet
  growth exponent, the packet counterpart of the band rate law.

**Mechanism.** If `|G(τ)| ≤ K e^{στ}` for the zero series `G = Σ_ρ c_ρ e^{λ_ρ τ}`, its Laplace
transform is holomorphic on `Re z > σ`. On `Re z > 1/2` it is the zero resolvent
`R(z) = Σ_ρ c_ρ e^{(λ_ρ − z)b}/(z − λ_ρ)`, holomorphic off the locally finite set `{λ_ρ}`. The
half-plane minus a countable set is preconnected, so the two agree there, and at `λ_ρ` with
`Re λ_ρ > σ` the residue `c_ρ` of `R` must vanish (`coeff_eq_zero_of_growth`). Local finiteness
replaces any choice of a rightmost zero. A normed bump of small support has `f̂(ξ) ≠ 0` at any
prescribed complex point (`exists_bump_paperFT_ne_zero`).
-/

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

noncomputable section
set_option autoImplicit false

/-! ## Shifted zeros of a zero configuration -/

section ZeroResolvent

variable {Z : Zeta23.ZeroConfig}

/-- The shifted zero `λ_ρ = ρ − 1/2`. -/
def zeroShift (ρ : Z.carrier) : ℂ := (ρ : ℂ) - 1 / 2

theorem I_mul_gammaOf (ρ : Z.carrier) : I * Zeta23.gammaOf ρ = zeroShift ρ := by
  unfold Zeta23.gammaOf zeroShift
  field_simp

theorem abs_re_zeroShift_le (ρ : Z.carrier) : |(zeroShift ρ).re| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := Z.strip ρ ρ.2
  simp only [zeroShift, sub_re, div_ofNat_re, one_re]
  rw [abs_le]
  constructor <;> linarith

theorem zeroShift_injective : Function.Injective (zeroShift (Z := Z)) := fun ρ ρ' h =>
  Subtype.ext (by simpa [zeroShift] using h)

theorem countable_carrier (Z : Zeta23.ZeroConfig) : Z.carrier.Countable := by
  refine Set.Countable.mono (fun ρ hρ => ?_) (Set.countable_iUnion fun n : ℕ =>
    (Z.finite_window (-(n + 1 : ℝ)) (n + 1)).countable)
  have h1 := Nat.le_ceil |ρ.im|
  have h2 := neg_abs_le ρ.im
  have h3 := le_abs_self ρ.im
  exact Set.mem_iUnion.mpr ⟨⌈|ρ.im|⌉₊, hρ, by linarith, by linarith⟩

/-- Shifted zeros are locally finite. -/
theorem exists_radius_zeroShift (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ρ : Z.carrier, zeroShift ρ ≠ z → r ≤ ‖z - zeroShift ρ‖ := by
  set W : Set ℂ := (fun s : ℂ => s - 1 / 2) ''
    (Z.carrier ∩ {s : ℂ | z.im - 1 < s.im ∧ s.im ≤ z.im + 1})
  have hWfin : (W \ {z}).Finite := ((Z.finite_window _ _).image _).sdiff
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hWfin.isClosed.isOpen_compl.mem_nhds (show z ∈ (W \ {z})ᶜ by simp))
  refine ⟨min ε 1, lt_min hε one_pos, fun ρ hρ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have him := (abs_im_le_norm (z - zeroShift ρ)).trans_lt (hlt.trans_le (min_le_right _ _))
  simp only [zeroShift, sub_im, div_ofNat_im, one_im, zero_div, sub_zero, abs_lt] at him
  have hmem : zeroShift ρ ∈ W \ {z} :=
    ⟨⟨ρ, ⟨ρ.2, by linarith, by linarith⟩, rfl⟩, hρ⟩
  refine hball ?_ hmem
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
  exact hlt.trans_le (min_le_left _ _)

theorem norm_exp_zeroShift_sub_le (ρ : Z.carrier) (z : ℂ) (T : ℝ) :
    ‖cexp ((zeroShift ρ - z) * T)‖ ≤ Real.exp ((1 / 2 + |z.re|) * |T|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : ((zeroShift ρ - z) * T).re = ((zeroShift ρ).re - z.re) * T := by simp
  rw [hre]
  calc ((zeroShift ρ).re - z.re) * T ≤ |((zeroShift ρ).re - z.re) * T| := le_abs_self _
    _ = |(zeroShift ρ).re - z.re| * |T| := abs_mul _ _
    _ ≤ (1 / 2 + |z.re|) * |T| := by
        refine mul_le_mul_of_nonneg_right ((abs_sub _ _).trans ?_) (abs_nonneg T)
        linarith [abs_re_zeroShift_le ρ]

/-- Uniform size of `e^{(λ_ρ − z)T}` on a ball. -/
theorem norm_exp_zeroShift_sub_le_ball (ρ : Z.carrier) {z₁ z : ℂ} {r : ℝ}
    (hz : z ∈ Metric.ball z₁ r) (T : ℝ) :
    ‖cexp ((zeroShift ρ - z) * T)‖ ≤ Real.exp ((1 / 2 + |z₁.re| + r) * |T|) := by
  refine (norm_exp_zeroShift_sub_le ρ z T).trans (Real.exp_le_exp.mpr ?_)
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg T)
  have h1 := (abs_re_le_norm (z - z₁)).trans (dist_eq_norm z z₁ ▸ (Metric.mem_ball.mp hz).le)
  have h2 := abs_sub_abs_le_abs_sub z.re z₁.re
  simp only [sub_re] at h1
  linarith

/-- The zero resolvent `R(z) = Σ_ρ c_ρ e^{(λ_ρ − z)T}/(z − λ_ρ)`. -/
def zeroResolvent (c : Z.carrier → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∑' ρ, c ρ * cexp ((zeroShift ρ - z) * T) / (z - zeroShift ρ)

/-- The zero resolvent is holomorphic off the shifted zeros. -/
theorem analyticAt_zeroResolvent {c : Z.carrier → ℂ} (hc : Summable fun ρ => ‖c ρ‖) (T : ℝ)
    {z₁ : ℂ} (hz₁ : ∀ ρ : Z.carrier, zeroShift ρ ≠ z₁) : AnalyticAt ℂ (zeroResolvent c T) z₁ := by
  obtain ⟨r, hr, hrad⟩ := exists_radius_zeroShift (Z := Z) z₁
  set E := Real.exp ((1 / 2 + |z₁.re| + r / 2) * |T|)
  have hdist : ∀ ρ : Z.carrier, ∀ z ∈ Metric.ball z₁ (r / 2), r / 2 ≤ ‖z - zeroShift ρ‖ := by
    intro ρ z hz
    have h1 := hrad ρ (hz₁ ρ)
    have h2 : ‖z - z₁‖ < r / 2 := by rw [← dist_eq_norm]; exact hz
    have h3 := norm_sub_le_norm_sub_add_norm_sub z₁ z (zeroShift ρ)
    rw [norm_sub_rev z₁ z] at h3
    linarith
  have hdiff : DifferentiableOn ℂ (zeroResolvent c T) (Metric.ball z₁ (r / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun ρ => ‖c ρ‖ * E * (2 / r)) ((hc.mul_right E).mul_right (2 / r))
      (fun ρ z hz => ?_) Metric.isOpen_ball (fun ρ z hz => ?_)
    · have hne : z - zeroShift ρ ≠ 0 :=
        norm_pos_iff.mp ((half_pos hr).trans_le (hdist ρ z hz))
      exact (((by fun_prop : Differentiable ℂ fun z : ℂ => c ρ * cexp ((zeroShift ρ - z) * T)) z).div
        (differentiableAt_id.sub_const (zeroShift ρ)) hne).differentiableWithinAt
    · have hpos := (half_pos hr).trans_le (hdist ρ z hz)
      rw [norm_div, norm_mul, div_le_iff₀ hpos]
      calc ‖c ρ‖ * ‖cexp ((zeroShift ρ - z) * T)‖ ≤ ‖c ρ‖ * E :=
            mul_le_mul_of_nonneg_left (norm_exp_zeroShift_sub_le_ball ρ hz T) (norm_nonneg _)
        _ = ‖c ρ‖ * E * (2 / r) * (r / 2) := by field_simp
        _ ≤ ‖c ρ‖ * E * (2 / r) * ‖z - zeroShift ρ‖ :=
            mul_le_mul_of_nonneg_left (hdist ρ z hz) (by positivity)
  exact hdiff.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hr)))

/-- **Residue of the zero resolvent.** `(z − λ_{ρ₀}) R(z) → c_{ρ₀}` as `z → λ_{ρ₀}`. -/
theorem tendsto_residue_zeroResolvent {c : Z.carrier → ℂ} (hc : Summable fun ρ => ‖c ρ‖)
    (T : ℝ) (ρ₀ : Z.carrier) :
    Tendsto (fun z => (z - zeroShift ρ₀) * zeroResolvent c T z) (𝓝[≠] (zeroShift ρ₀))
      (𝓝 (c ρ₀)) := by
  classical
  obtain ⟨r, hr, hrad⟩ := exists_radius_zeroShift (Z := Z) (zeroShift ρ₀)
  set z₀ := zeroShift ρ₀
  set B := Metric.ball z₀ (r / 2)
  set E := Real.exp ((1 / 2 + |z₀.re| + r / 2) * |T|)
  -- the resolvent with the pole at `λ_{ρ₀}` multiplied out
  set H : ℂ → ℂ := fun z => ∑' ρ, c ρ * cexp ((zeroShift ρ - z) * T) *
    (if ρ = ρ₀ then 1 else (z - z₀) / (z - zeroShift ρ))
  have hdist : ∀ ρ, ρ ≠ ρ₀ → ∀ z ∈ B, ‖z - z₀‖ ≤ ‖z - zeroShift ρ‖ := by
    intro ρ hρ z hz
    have h1 := hrad ρ fun h => hρ (zeroShift_injective h)
    have h2 : ‖z - z₀‖ < r / 2 := by rw [← dist_eq_norm]; exact hz
    have h3 := norm_sub_le_norm_sub_add_norm_sub z₀ z (zeroShift ρ)
    rw [norm_sub_rev z₀ z] at h3
    linarith
  have hne : ∀ ρ, ρ ≠ ρ₀ → ∀ z ∈ B, z - zeroShift ρ ≠ 0 := by
    intro ρ hρ z hz h
    have h1 := hrad ρ fun h => hρ (zeroShift_injective h)
    have h2 : ‖z - z₀‖ < r / 2 := by rw [← dist_eq_norm]; exact hz
    have h3 := norm_sub_le_norm_sub_add_norm_sub z₀ z (zeroShift ρ)
    rw [norm_sub_rev z₀ z, h, norm_zero, add_zero] at h3
    linarith
  have hcont : ContinuousOn H B := by
    refine continuousOn_tsum (u := fun ρ => ‖c ρ‖ * E) (fun ρ => ?_) (hc.mul_right E)
      (fun ρ z hz => ?_)
    · by_cases hρ : ρ = ρ₀
      · simp only [hρ, if_true, mul_one]
        exact (by fun_prop : Continuous fun z : ℂ => c ρ₀ * cexp ((zeroShift ρ₀ - z) * T)
          ).continuousOn
      · simp only [hρ, if_false]
        intro z hz
        exact ((by fun_prop : Continuous fun z : ℂ => c ρ * cexp ((zeroShift ρ - z) * T)
          ).continuousAt.mul ((continuousAt_id.sub continuousAt_const).div
            (continuousAt_id.sub continuousAt_const) (hne ρ hρ z hz))).continuousWithinAt
    · rw [norm_mul, norm_mul]
      have hfac : ‖(if ρ = ρ₀ then (1 : ℂ) else (z - z₀) / (z - zeroShift ρ))‖ ≤ 1 := by
        split_ifs with hρ
        · simp
        · rw [norm_div]
          exact div_le_one_of_le₀ (hdist ρ hρ z hz) (norm_nonneg _)
      calc ‖c ρ‖ * ‖cexp ((zeroShift ρ - z) * T)‖ *
            ‖(if ρ = ρ₀ then (1 : ℂ) else (z - z₀) / (z - zeroShift ρ))‖
          ≤ ‖c ρ‖ * E * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (norm_exp_zeroShift_sub_le_ball ρ hz T) (norm_nonneg _)) hfac (norm_nonneg _)
              (by positivity)
        _ = ‖c ρ‖ * E := mul_one _
  have hH₀ : H z₀ = c ρ₀ := by
    simp only [H]
    rw [tsum_eq_single ρ₀ fun ρ hρ => by simp [hρ]]
    simp [z₀]
  have hlim : Tendsto H (𝓝[≠] z₀) (𝓝 (c ρ₀)) := by
    rw [← hH₀]
    exact ((hcont.continuousAt (Metric.isOpen_ball.mem_nhds
      (Metric.mem_ball_self (half_pos hr)))).tendsto).mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (half_pos hr)))] with z hz hzB
  have hz0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  simp only [H, zeroResolvent]
  rw [← tsum_mul_left]
  refine tsum_congr fun ρ => ?_
  by_cases hρ : ρ = ρ₀
  · subst hρ
    rw [if_pos rfl, mul_one, ← mul_div_assoc]
    exact (mul_div_cancel_left₀ _ hz0).symm
  · simp only [hρ, if_false]
    field_simp [hne ρ hρ z hzB]

end ZeroResolvent

/-! ## Exponential sums over zeros -/

section ZeroSeries

variable {Z : Zeta23.ZeroConfig}

/-- The zero series `G(τ) = Σ_ρ c_ρ e^{λ_ρ τ}`. -/
def zeroSeries (c : Z.carrier → ℂ) (τ : ℝ) : ℂ := ∑' ρ, c ρ * cexp (zeroShift ρ * τ)

theorem norm_exp_zeroShift_mul_le (ρ : Z.carrier) (τ : ℝ) :
    ‖cexp (zeroShift ρ * τ)‖ ≤ Real.exp (|τ| / 2) := by
  have := norm_exp_zeroShift_sub_le ρ 0 τ
  simp only [sub_zero, zero_re, abs_zero, add_zero] at this
  rwa [show 1 / 2 * |τ| = |τ| / 2 by ring] at this

theorem continuous_zeroSeries {c : Z.carrier → ℂ} (hc : Summable fun ρ => ‖c ρ‖) :
    Continuous (zeroSeries c) := by
  refine continuous_iff_continuousAt.mpr fun τ₀ => ?_
  have hon : ContinuousOn (zeroSeries c) (Ioo (τ₀ - 1) (τ₀ + 1)) := by
    refine continuousOn_tsum (u := fun ρ => ‖c ρ‖ * Real.exp ((|τ₀| + 1) / 2))
      (fun ρ => by fun_prop) (hc.mul_right _) fun ρ τ hτ => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_exp_zeroShift_mul_le ρ τ).trans
      (Real.exp_le_exp.mpr ?_)) (norm_nonneg _)
    have : |τ| ≤ |τ₀| + 1 := by
      have h1 := abs_sub_abs_le_abs_sub τ τ₀
      have h2 : |τ - τ₀| ≤ 1 := abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      linarith
    linarith
  exact hon.continuousAt (Ioo_mem_nhds (by linarith) (by linarith))

/-- **Termwise Laplace transform.** For `b > 0` and `Re z > 1/2`,
`∫_b^∞ e^{−zτ} G(τ) dτ = R(z)`. -/
theorem integral_exp_mul_zeroSeries {c : Z.carrier → ℂ} (hc : Summable fun ρ => ‖c ρ‖) {b : ℝ}
    (hb : 0 < b) {z : ℂ} (hz : 1 / 2 < z.re) :
    ∫ τ in Ioi b, cexp (-z * τ) * zeroSeries c τ = zeroResolvent c b z := by
  haveI : Countable Z.carrier := (countable_carrier Z).to_subtype
  set F : Z.carrier → ℝ → ℂ := fun ρ τ => c ρ * cexp ((zeroShift ρ - z) * τ)
  have hre : ∀ ρ : Z.carrier, (zeroShift ρ - z).re < 0 := fun ρ => by
    have := (abs_le.mp (abs_re_zeroShift_le ρ)).2
    simp only [sub_re]; linarith
  have hint : ∀ ρ, Integrable (F ρ) (volume.restrict (Ioi b)) := fun ρ =>
    (integrableOn_exp_mul_complex_Ioi (hre ρ) b).const_mul (c ρ)
  have hval : ∀ ρ, ∫ τ in Ioi b, F ρ τ =
      c ρ * cexp ((zeroShift ρ - z) * b) / (z - zeroShift ρ) := fun ρ => by
    simp only [F]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hre ρ)]
    have : z - zeroShift ρ ≠ 0 := fun h => by
      have := hre ρ
      rw [← neg_sub, h, neg_zero, zero_re] at this
      exact lt_irrefl _ this
    rw [show zeroShift ρ - z = -(z - zeroShift ρ) by ring]
    field_simp
  have hnorm : ∀ ρ, ∫ τ in Ioi b, ‖F ρ τ‖ ≤ ‖c ρ‖ / (z.re - 1 / 2) := fun ρ => by
    set a := (zeroShift ρ - z).re
    have ha : a < 0 := hre ρ
    have hle : z.re - 1 / 2 ≤ -a := by
      have := (abs_le.mp (abs_re_zeroShift_le ρ)).2
      simp only [a, sub_re]; linarith
    have hpt : ∀ τ : ℝ, ‖F ρ τ‖ = ‖c ρ‖ * Real.exp (a * τ) := fun τ => by
      simp only [F, norm_mul, Complex.norm_exp, a]
      congr 2
      simp
    have hreal : ∫ τ in Ioi b, Real.exp (a * τ) = Real.exp (a * b) / -a := by
      rw [integral_exp_mul_Ioi ha, neg_div, div_neg]
    simp_rw [hpt]
    rw [integral_const_mul, hreal, div_eq_mul_one_div ‖c ρ‖]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc Real.exp (a * b) / -a ≤ 1 / -a := by
          refine div_le_div_of_nonneg_right ?_ (by linarith)
          exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ha.le hb.le)
      _ ≤ 1 / (z.re - 1 / 2) := one_div_le_one_div_of_le (by linarith) hle
  have hsum : Summable fun ρ => ∫ τ in Ioi b, ‖F ρ τ‖ :=
    (hc.div_const (z.re - 1 / 2)).of_nonneg_of_le
      (fun ρ => integral_nonneg fun _ => norm_nonneg _) hnorm
  have hpoint : ∀ τ : ℝ, cexp (-z * τ) * zeroSeries c τ = ∑' ρ, F ρ τ := fun τ => by
    rw [zeroSeries, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    simp only [F]
    rw [mul_left_comm, ← Complex.exp_add]
    ring_nf
  simp_rw [hpoint]
  rw [← integral_tsum_of_summable_integral_norm hint hsum, zeroResolvent]
  exact tsum_congr hval

/-- **Growth beyond the depth kills the coefficient.** If `|G(τ)| ≤ K e^{στ}` for `τ > b` with
`b > 0`, then `c_ρ = 0` at every zero of depth `Re λ_ρ > σ`. -/
theorem coeff_eq_zero_of_growth {c : Z.carrier → ℂ} (hc : Summable fun ρ => ‖c ρ‖) {b σ K : ℝ}
    (hb : 0 < b) (hK : ∀ τ : ℝ, b < τ → ‖zeroSeries c τ‖ ≤ K * Real.exp (σ * τ))
    {ρ₀ : Z.carrier} (hρ₀ : σ < (zeroShift ρ₀).re) : c ρ₀ = 0 := by
  -- the damped series `H(τ) = e^{−στ} G(τ)` is bounded beyond `b`
  set H : ℝ → ℂ := fun τ => cexp (-(σ : ℂ) * τ) * zeroSeries c τ
  have hHc : Continuous H := (by fun_prop : Continuous fun τ : ℝ => cexp (-(σ : ℂ) * τ)).mul
    (continuous_zeroSeries hc)
  have hHb : ∀ τ, b < τ → ‖H τ‖ ≤ K := fun τ hτ => by
    simp only [H, norm_mul]
    rw [show -(σ : ℂ) * τ = ((-σ * τ : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    calc Real.exp (-σ * τ) * ‖zeroSeries c τ‖ ≤ Real.exp (-σ * τ) * (K * Real.exp (σ * τ)) :=
          mul_le_mul_of_nonneg_left (hK τ hτ) (Real.exp_pos _).le
      _ = K := by
          rw [mul_left_comm, ← Real.exp_add, show -σ * τ + σ * τ = 0 by ring, Real.exp_zero,
            mul_one]
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hHb (b + 1) (by linarith))
  -- its Laplace transform, holomorphic on `Re z > σ`
  set Lre := RHTower.ccmAbelLaplaceTail (fun τ => (H τ).re) b
  set Lim := RHTower.ccmAbelLaplaceTail (fun τ => (H τ).im) b
  have hLre := RHTower.analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    (Complex.continuous_re.comp hHc).measurable hb hK0
    fun τ hτ => (abs_re_le_norm _).trans (hHb τ hτ)
  have hLim := RHTower.analyticOnNhd_ccmAbelLaplaceTail_of_bounded
    (Complex.continuous_im.comp hHc).measurable hb hK0
    fun τ hτ => (abs_im_le_norm _).trans (hHb τ hτ)
  set L : ℂ → ℂ := fun z => Lre (z - σ) + I * Lim (z - σ)
  have hLan : AnalyticOnNhd ℂ L {z : ℂ | σ < z.re} := fun z hz => by
    have hz' : (z - σ) ∈ {u : ℂ | 0 < u.re} := by
      change 0 < (z - σ).re
      simp only [sub_re, ofReal_re]
      exact sub_pos.mpr hz
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - σ) z := by fun_prop
    exact (AnalyticAt.comp (f := fun z : ℂ => z - σ) (hLre _ hz') hshift).add
      (analyticAt_const.mul (AnalyticAt.comp (f := fun z : ℂ => z - σ) (hLim _ hz') hshift))
  -- on `Re z > 1/2 + |σ|` it is the zero resolvent
  have hLR : ∀ z : ℂ, 1 / 2 + |σ| < z.re → L z = zeroResolvent c b z := by
    intro z hz
    have hu : 0 < (z - σ).re := by
      simp only [sub_re, ofReal_re]; linarith [le_abs_self σ]
    have hintq : ∀ q : ℝ → ℝ, Continuous q → (∀ τ, b < τ → |q τ| ≤ K) →
        Integrable (fun τ : ℝ => cexp (-(z - σ) * τ) * (q τ : ℂ)) (volume.restrict (Ioi b)) := by
      intro q hq hqK
      refine Integrable.mono' ((exp_neg_integrableOn_Ioi b hu).const_mul K)
        ((by fun_prop : Continuous fun τ : ℝ => cexp (-(z - σ) * τ) * (q τ : ℂ)
          ).aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun τ hτ => ?_)
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      refine mul_le_mul (hqK τ hτ) (le_of_eq ?_) (Real.exp_pos _).le hK0
      congr 1
      simp
    have hre : Integrable (fun τ : ℝ => cexp (-(z - σ) * τ) * ((H τ).re : ℂ))
        (volume.restrict (Ioi b)) :=
      hintq _ (Complex.continuous_re.comp hHc) fun τ hτ => (abs_re_le_norm _).trans (hHb τ hτ)
    have him : Integrable (fun τ : ℝ => I * (cexp (-(z - σ) * τ) * ((H τ).im : ℂ)))
        (volume.restrict (Ioi b)) :=
      (hintq _ (Complex.continuous_im.comp hHc) fun τ hτ =>
        (abs_im_le_norm _).trans (hHb τ hτ)).const_mul I
    rw [← integral_exp_mul_zeroSeries hc hb (by linarith [abs_nonneg σ])]
    simp only [L, Lre, Lim, RHTower.ccmAbelLaplaceTail]
    rw [← integral_const_mul, ← integral_add hre him]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    have hsplit : ((H τ).re : ℂ) + ((H τ).im : ℂ) * I = H τ := Complex.re_add_im (H τ)
    calc cexp (-(z - σ) * τ) * ((H τ).re : ℂ) + I * (cexp (-(z - σ) * τ) * ((H τ).im : ℂ))
        = cexp (-(z - σ) * τ) * (((H τ).re : ℂ) + ((H τ).im : ℂ) * I) := by ring
      _ = cexp (-(z - σ) * τ) * H τ := by rw [hsplit]
      _ = cexp (-z * τ) * zeroSeries c τ := by
          simp only [H]
          rw [← mul_assoc, ← Complex.exp_add]
          ring_nf
  -- identity theorem on the half-plane minus the shifted zeros
  set U : Set ℂ := {z : ℂ | σ < z.re} \ range (zeroShift (Z := Z))
  have hnot : ∀ x : ℝ, 1 / 2 < x → (x : ℂ) ∉ range (zeroShift (Z := Z)) := by
    rintro x hx ⟨ρ, hρ⟩
    have := (abs_le.mp (abs_re_zeroShift_le ρ)).2
    rw [hρ, ofReal_re] at this
    linarith
  have hz₁U : ((2 + |σ| : ℝ) : ℂ) ∈ U :=
    ⟨by simp only [mem_setOf_eq, ofReal_re]; linarith [le_abs_self σ],
      hnot _ (by linarith [abs_nonneg σ])⟩
  have hUpre : IsPreconnected U := by
    haveI : Countable Z.carrier := (countable_carrier Z).to_subtype
    exact GaloisForLFunctions.HTGeometry.isPreconnected_diff_of_countable_of_convex_complex
      (convex_halfSpace_re_gt σ) (isOpen_lt continuous_const Complex.continuous_re)
      (countable_range _) hz₁U
  have hRan : AnalyticOnNhd ℂ (zeroResolvent c b) U := fun z hz =>
    analyticAt_zeroResolvent hc b fun ρ h => hz.2 ⟨ρ, h⟩
  have hEq : EqOn L (zeroResolvent c b) U := by
    refine (hLan.mono sdiff_subset).eqOn_of_preconnected_of_eventuallyEq hRan hUpre hz₁U ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 / 2 + |σ| : ℝ) < (((2 + |σ| : ℝ) : ℂ)).re by simp only [ofReal_re]; linarith)]
      with z hz
    exact hLR z hz
  -- the residue at `λ_{ρ₀}`
  set z₀ := zeroShift ρ₀
  obtain ⟨r, hr, hrad⟩ := exists_radius_zeroShift (Z := Z) z₀
  have hevU : ∀ᶠ z in 𝓝[≠] z₀, z ∈ U := by
    have hball : Metric.ball z₀ (min r (z₀.re - σ)) ∈ 𝓝 z₀ :=
      Metric.ball_mem_nhds _ (lt_min hr (sub_pos.mpr hρ₀))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with z hz hzb
    have hd : ‖z - z₀‖ < min r (z₀.re - σ) := by rw [← dist_eq_norm]; exact hzb
    refine ⟨?_, ?_⟩
    · have := (abs_re_le_norm (z - z₀)).trans_lt (hd.trans_le (min_le_right _ _))
      simp only [sub_re, abs_lt] at this
      change σ < z.re
      linarith
    · rintro ⟨ρ, hρ⟩
      have hρz : zeroShift ρ ≠ z₀ := fun h => hz (hρ.symm.trans h)
      have := hrad ρ hρz
      rw [hρ] at this
      linarith [hd.trans_le (min_le_left _ _), norm_sub_rev z₀ z]
  have hres := tendsto_residue_zeroResolvent hc b ρ₀
  have hzero : Tendsto (fun z => (z - z₀) * zeroResolvent c b z) (𝓝[≠] z₀) (𝓝 0) := by
    have hcont : ContinuousAt L z₀ := (hLan z₀ hρ₀).continuousAt
    have h0 : Tendsto (fun z => (z - z₀) * L z) (𝓝 z₀) (𝓝 ((z₀ - z₀) * L z₀)) :=
      ((continuousAt_id.sub continuousAt_const).mul hcont).tendsto
    rw [sub_self, zero_mul] at h0
    refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hevU] with z hz
    rw [hEq hz]
  exact tendsto_nhds_unique hres hzero

end ZeroSeries

/-! ## A bump that sees a prescribed point -/

/-- For every complex `ξ` some real compact smooth source has `f̂(ξ) ≠ 0`: a normed bump whose
support is so small that `e^{iξu}` stays within `1/2` of `1` on it. -/
theorem exists_bump_paperFT_ne_zero (ξ : ℂ) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      Zeta23.paperFT (fun u => (f u : ℂ)) ξ ≠ 0 := by
  set g : ℝ → ℂ := fun u => cexp (I * ξ * u)
  have hg : Continuous g := by fun_prop
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hg.continuousAt (1 / 2) (by norm_num)
  let φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  set f := φ.normed volume
  have hf0 : ∀ u, 0 ≤ f u := φ.nonneg_normed
  have hfc : HasCompactSupport f := φ.hasCompactSupport_normed
  have hfcont : Continuous f := (φ.contDiff_normed (n := 0)).continuous
  have hsupp : ∀ u, δ ≤ |u| → f u = 0 := fun u hu => by
    have : u ∉ Function.support f := by
      rw [φ.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
      exact not_lt.mpr hu
    simpa using this
  refine ⟨f, φ.contDiff_normed, hfc, ?_⟩
  have hint1 : Integrable fun u => (f u : ℂ) :=
    (Complex.continuous_ofReal.comp hfcont).integrable_of_hasCompactSupport
      (hfc.comp_left Complex.ofReal_zero)
  have hint2 : Integrable fun u => (f u : ℂ) * (g u - 1) :=
    ((Complex.continuous_ofReal.comp hfcont).mul (hg.sub continuous_const)
      ).integrable_of_hasCompactSupport ((hfc.comp_left Complex.ofReal_zero).mul_right)
  have h1 : ∫ u, (f u : ℂ) = 1 := by
    rw [integral_complex_ofReal, φ.integral_normed, Complex.ofReal_one]
  have hsplit : Zeta23.paperFT (fun u => (f u : ℂ)) ξ = 1 + ∫ u, (f u : ℂ) * (g u - 1) := by
    have h := integral_add hint1 hint2
    rw [h1] at h
    rw [← h]
    unfold Zeta23.paperFT
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [g]
    ring
  have hsmall : ‖∫ u, (f u : ℂ) * (g u - 1)‖ ≤ 1 / 2 := by
    calc ‖∫ u, (f u : ℂ) * (g u - 1)‖ ≤ ∫ u, 1 / 2 * f u := by
          refine norm_integral_le_of_norm_le
            ((φ.integrable_normed (μ := volume)).const_mul _)
            (Eventually.of_forall fun u => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 u), mul_comm]
          by_cases hu : |u| < δ
          · refine mul_le_mul_of_nonneg_right ?_ (hf0 u)
            have := hδg (show dist u 0 < δ by rwa [Real.dist_eq, sub_zero])
            rw [dist_eq_norm] at this
            simpa [g] using this.le
          · rw [hsupp u (not_lt.mp hu)]; simp
      _ = 1 / 2 := by rw [integral_const_mul, φ.integral_normed, mul_one]
  rw [hsplit]
  intro h
  have : ‖(1 : ℂ)‖ ≤ 1 / 2 := by
    rw [show (1 : ℂ) = -∫ u, (f u : ℂ) * (g u - 1) by linear_combination h, norm_neg]
    exact hsmall
  norm_num at this

/-! ## The packet growth law -/

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-- The zero coefficients `c_ρ = m_ρ f̂(γ_ρ)` of a source. -/
def packetCoeff (f : ℝ → ℝ) (ρ : 𝒵) : ℂ :=
  (Zeta23.zetaZeroConfig.mult ρ : ℂ) * Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ)

theorem summable_norm_packetCoeff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Summable fun ρ => ‖packetCoeff f ρ‖ :=
  summable_norm_iff.mpr (Zeta23.WeilEF.EF_lit_zetaZeroConfig _
    (Complex.ofRealCLM.contDiff.comp hf) (hfc.comp_left Complex.ofReal_zero)).1

theorem packetCoeff_eq_zero_iff (f : ℝ → ℝ) (ρ : 𝒵) :
    packetCoeff f ρ = 0 ↔ Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  have hm : (Zeta23.zetaZeroConfig.mult ρ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (Zeta23.zetaZeroConfig.one_le_mult ρ ρ.2))
  rw [packetCoeff, mul_eq_zero, or_iff_right hm]

/-- Beyond the support the packet is the archimedean tail minus the zero series. -/
theorem stationaryPacket_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) {τ : ℝ} (hτ : w < τ) :
    (stationaryPacket f τ : ℂ) = packetArchTail f τ - zeroSeries (packetCoeff f) τ := by
  have h := (hasSum_packet_explicit_formula hf hfc hw0 hw hτ).tsum_eq
  have hser : zeroSeries (packetCoeff f) τ = packetArchTail f τ - (stationaryPacket f τ : ℂ) := by
    rw [zeroSeries, ← h]
    refine tsum_congr fun ρ => ?_
    simp only [packetCoeff]
    rw [show I * Zeta23.gammaOf ρ * τ = zeroShift ρ * τ by rw [I_mul_gammaOf]]
    ring
  rw [hser]
  ring

theorem norm_packetArchTail_le (f : ℝ → ℝ) (τ : ℝ) :
    ‖packetArchTail f τ‖ ≤ 1 / (2 * Real.pi) * ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (f u : ℂ)) r *
      (Zeta23.EF.gammaBracket r : ℂ)‖ := by
  unfold packetArchTail
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hc]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
    (le_of_eq (integral_congr_ae (Eventually.of_forall fun r => ?_)))) (by positivity)
  simp only
  rw [mul_assoc, norm_mul, show I * (r : ℂ) * τ = ((r * τ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

private theorem exists_support_bound {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ w : ℝ, 0 ≤ w ∧ ∀ v : ℝ, w < |v| → f v = 0 := by
  obtain ⟨R, hR, hRf⟩ := hfc.exists_pos_le_norm
  exact ⟨R, hR.le, fun v hv => hRf v (by rw [Real.norm_eq_abs]; exact hv.le)⟩

/-- **Packet growth law.** For a real compact `C²` source and `σ ≥ 0`, the packet is
`O(e^{στ})` iff `f̂(γ_ρ) = 0` at every zero of depth `Re ρ − 1/2 > σ`. -/
theorem packet_growth_iff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → |stationaryPacket f τ| ≤ K * Real.exp (σ * τ)) ↔
      ∀ ρ : 𝒵, σ < (ρ : ℂ).re - 1 / 2 →
        Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  obtain ⟨w, hw0, hw⟩ := exists_support_bound hfc
  have hc := summable_norm_packetCoeff hf hfc
  set CA := 1 / (2 * Real.pi) * ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (f u : ℂ)) r *
    (Zeta23.EF.gammaBracket r : ℂ)‖
  have hCA0 : 0 ≤ CA := (norm_nonneg _).trans (norm_packetArchTail_le f 0)
  constructor
  · rintro ⟨T, K, hK⟩ ρ hρ
    rw [← packetCoeff_eq_zero_iff]
    set b := max (max T w) 0 + 1
    have hb : 0 < b := by positivity
    refine coeff_eq_zero_of_growth hc hb (K := CA + |K|) (σ := σ) (fun τ hτ => ?_)
      (by simpa [zeroShift] using hρ)
    have hτw : w < τ := by
      have := le_max_right T w; have := le_max_left (max T w) 0; linarith
    have hτT : T ≤ τ := by
      have := le_max_left T w; have := le_max_left (max T w) 0; linarith
    have hτ0 : 0 ≤ τ := by have := le_max_right (max T w) 0; linarith
    have hG : zeroSeries (packetCoeff f) τ = packetArchTail f τ - (stationaryPacket f τ : ℂ) := by
      rw [stationaryPacket_eq hf hfc hw0 hw hτw]; ring
    have he : 1 ≤ Real.exp (σ * τ) := Real.one_le_exp (mul_nonneg hσ hτ0)
    rw [hG]
    calc ‖packetArchTail f τ - (stationaryPacket f τ : ℂ)‖
        ≤ ‖packetArchTail f τ‖ + ‖(stationaryPacket f τ : ℂ)‖ := norm_sub_le _ _
      _ ≤ CA + |K| * Real.exp (σ * τ) := by
          refine add_le_add (norm_packetArchTail_le f τ) ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (hK τ hτT).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le)
      _ ≤ (CA + |K|) * Real.exp (σ * τ) := by nlinarith [abs_nonneg K]
  · intro hblind
    set S := ∑' ρ, ‖packetCoeff f ρ‖
    refine ⟨w + 1, CA + S, fun τ hτ => ?_⟩
    have hτw : w < τ := by linarith
    have hτ0 : 0 ≤ τ := by linarith
    have he : 1 ≤ Real.exp (σ * τ) := Real.one_le_exp (mul_nonneg hσ hτ0)
    have hterm : ∀ ρ : 𝒵, ‖packetCoeff f ρ * cexp (zeroShift ρ * τ)‖ ≤
        ‖packetCoeff f ρ‖ * Real.exp (σ * τ) := fun ρ => by
      rw [norm_mul]
      by_cases hρ : σ < (ρ : ℂ).re - 1 / 2
      · rw [(packetCoeff_eq_zero_iff f ρ).mpr (hblind ρ hρ)]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ?_
        have : (zeroShift ρ * τ).re = ((ρ : ℂ).re - 1 / 2) * τ := by simp [zeroShift]
        rw [this]
        exact mul_le_mul_of_nonneg_right (not_lt.mp hρ) hτ0
    have hdom : Summable fun ρ => ‖packetCoeff f ρ‖ * Real.exp (σ * τ) := hc.mul_right _
    have hG : ‖zeroSeries (packetCoeff f) τ‖ ≤ S * Real.exp (σ * τ) := by
      rw [zeroSeries, show S * Real.exp (σ * τ) = ∑' ρ, ‖packetCoeff f ρ‖ * Real.exp (σ * τ) from
        (tsum_mul_right).symm]
      exact (norm_tsum_le_tsum_norm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)).trans
        (Summable.tsum_le_tsum hterm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm) hdom)
    rw [← Real.norm_eq_abs, ← Complex.norm_real, stationaryPacket_eq hf hfc hw0 hw hτw]
    calc ‖packetArchTail f τ - zeroSeries (packetCoeff f) τ‖
        ≤ ‖packetArchTail f τ‖ + ‖zeroSeries (packetCoeff f) τ‖ := norm_sub_le _ _
      _ ≤ CA + S * Real.exp (σ * τ) := add_le_add (norm_packetArchTail_le f τ) hG
      _ ≤ (CA + S) * Real.exp (σ * τ) := by nlinarith

/-- **Bounded packets are blind sources.** `P_f` is eventually bounded iff `f̂(γ_ρ) = 0` at every
zero right of the critical line. -/
theorem packet_bounded_iff_blind {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → |stationaryPacket f τ| ≤ K) ↔
      ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
        Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  have h := packet_growth_iff hf hfc le_rfl
  simp only [zero_mul, Real.exp_zero, mul_one, sub_pos] at h
  exact h

/-- A zero right of the critical line exists as soon as RH fails. -/
theorem exists_mem_re_gt_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re := by
  unfold RiemannHypothesis at hRH
  push Not at hRH
  obtain ⟨s, hs, htriv, hs1, hre⟩ := hRH
  have hxi : _root_.RHTower.xi s = 0 :=
    _root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr
      ⟨hs, fun n hn => htriv n (by rw [hn]; ring)⟩
  have hmem : ∀ t : ℂ, _root_.RHTower.xi t = 0 → 1 / 2 < t.re → t ∈ 𝒵 := by
    intro t ht hlt
    refine ⟨(_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp ht).1,
      by linarith, ?_⟩
    by_contra h
    exact _root_.RHTower.xi_ne_zero_of_one_le_re (not_lt.mp h) ht
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · have h1 : _root_.RHTower.xi (1 - s) = 0 := by rw [_root_.RHTower.xi_one_sub]; exact hxi
    have h2 : 1 / 2 < (1 - s).re := by simp only [sub_re, one_re]; linarith
    exact ⟨⟨1 - s, hmem _ h1 h2⟩, h2⟩
  · exact ⟨⟨s, hmem s hxi hgt⟩, hgt⟩

/-- **RH is the boundedness of every compact packet.** -/
theorem riemannHypothesis_iff_forall_packet_bounded :
    RiemannHypothesis ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → |stationaryPacket f τ| ≤ K := by
  constructor
  · intro hRH f hf hfc
    refine (packet_bounded_iff_blind hf hfc).mpr fun ρ hρ => ?_
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  · intro h
    by_contra hRH
    obtain ⟨ρ, hρ⟩ := exists_mem_re_gt_of_not_riemannHypothesis hRH
    obtain ⟨f, hf, hfc, hne⟩ := exists_bump_paperFT_ne_zero (Zeta23.gammaOf ρ)
    exact hne ((packet_bounded_iff_blind hf hfc).mp (h f hf hfc) ρ hρ)

/-- **The zero width is the universal packet growth exponent.** For `β ≥ 0`, every zero has
`Re ρ ≤ 1/2 + β` iff every compact packet is `O(e^{βτ})`. -/
theorem xiZeroHalfPlaneBound_iff_forall_packet_growth {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔ ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → |stationaryPacket f τ| ≤ K * Real.exp (β * τ) := by
  constructor
  · intro hXi f hf hfc
    refine (packet_growth_iff hf hfc hβ).mpr fun ρ hρ => ?_
    have hxi : _root_.RHTower.xi ρ = 0 :=
      _root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr
        ⟨ρ.2.1, fun n hn => by
          have h := congrArg Complex.re hn
          have h0 := ρ.2.2.1
          rw [h] at h0
          simp at h0
          linarith [(Nat.cast_nonneg (α := ℝ) n)]⟩
    have := hXi ρ hxi
    linarith
  · intro h ρ hρ
    by_contra hlt
    push Not at hlt
    have hmem : ρ ∈ 𝒵 := by
      refine ⟨(_root_.RHTower.xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ).1,
        by linarith, ?_⟩
      by_contra h1
      exact _root_.RHTower.xi_ne_zero_of_one_le_re (not_lt.mp h1) hρ
    obtain ⟨f, hf, hfc, hne⟩ := exists_bump_paperFT_ne_zero (Zeta23.gammaOf ρ)
    exact hne ((packet_growth_iff hf hfc hβ).mp (h f hf hfc) ⟨ρ, hmem⟩ (by
      show β < ρ.re - 1 / 2
      linarith))

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
