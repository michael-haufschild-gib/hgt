import GaloisForLFunctions.RHTower.ThetaPrimePacketPorts
import GaloisForLFunctions.RHTower.ThetaCommutatorKernelInertia

/-!
# Harmonic obstructions for positive prime packets

The source cones of `z = X'/X` at the wall heights `2, 4, 6, 8` give phase-aperture thresholds
`8/11, 8/15, 1/2` at the first three heights (36). A two-scale packet has
`|B(2n)|² = cos²(nΔ) + (1 - 2v)² sin²(nΔ) ≥ cos²(nΔ)` (37), and for every real `θ` one of
`|cos θ| ≥ 8/11`, `|cos 2θ| ≥ 8/15`, `|cos 3θ| ≥ 1/2` holds (38). Hence every positive two-scale
packet with separation `o(L)` has a negative strip defect for every real gauge. The balanced
three-scale repair at offsets `-π/4, 0, π/4` has amplitudes `1/3` at heights `2, 4, 6` but
`B(8) = 1`; with the height-8 cone and prime log scales approximating the offsets (prime number
theorem), it fails for every gauge as well.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-! ## Source apertures at the probe heights -/

/-- **(36).** The phase-aperture thresholds at heights `2, 4, 6`:
`2 Re z₂/Im z₂ < 8/11`, `2 Re z₄/Im z₄ < 8/15`, `2 Re z₆/Im z₆ < 1/2`. -/
theorem wall_aperture_thresholds :
    2 * (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).re /
        (thetaPortLogDeriv (1 / 2 + (2 : ℝ) * I)).im < 8 / 11 ∧
      2 * (thetaPortLogDeriv (1 / 2 + (4 : ℝ) * I)).re /
        (thetaPortLogDeriv (1 / 2 + (4 : ℝ) * I)).im < 8 / 15 ∧
      2 * (thetaPortLogDeriv (1 / 2 + (6 : ℝ) * I)).re /
        (thetaPortLogDeriv (1 / 2 + (6 : ℝ) * I)).im < 1 / 2 := by
  obtain ⟨a2, b2⟩ := thetaPortLogDeriv_cone_two
  obtain ⟨a4, b4⟩ := thetaPortLogDeriv_cone_four
  obtain ⟨a6, b6⟩ := thetaPortLogDeriv_cone_six
  refine ⟨?_, ?_, ?_⟩ <;> rw [div_lt_iff₀ (by linarith)] <;> linarith

/-! ## Two-point characteristic values -/

/-- **(37).** `|v e^{-ix} + (1-v) e^{ix}|² = cos² x + (1 - 2v)² sin² x`. -/
theorem sq_norm_two_point_phase (v x : ℝ) :
    ‖(v : ℂ) * cexp ((-x : ℝ) * I) + ((1 - v : ℝ) : ℂ) * cexp (x * I)‖ ^ 2 =
      Real.cos x ^ 2 + (1 - 2 * v) ^ 2 * Real.sin x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
  ring

/-- **(37).** `|B(2n)| ≥ |cos(nΔ)|` for every two-point packet. -/
theorem abs_cos_le_norm_two_point_phase (v x : ℝ) :
    |Real.cos x| ≤ ‖(v : ℂ) * cexp ((-x : ℝ) * I) + ((1 - v : ℝ) : ℂ) * cexp (x * I)‖ := by
  have h : Real.cos x ^ 2 ≤
      ‖(v : ℂ) * cexp ((-x : ℝ) * I) + ((1 - v : ℝ) : ℂ) * cexp (x * I)‖ ^ 2 := by
    rw [sq_norm_two_point_phase]; nlinarith [sq_nonneg ((1 - 2 * v) * Real.sin x)]
  simpa only [abs_norm] using sq_le_sq.mp h

/-- The characteristic value of a two-scale packet at height `2n`, with midpoint reference. -/
theorem packetPhase_two_scale (a pm pp n : ℝ) :
    packetPhase Finset.univ ![a, 1 - a] ![pm, pp] ((Real.log pm + Real.log pp) / 2) (2 * n) =
      (a : ℂ) * cexp ((-(n * (Real.log pp - Real.log pm)) : ℝ) * I) +
        ((1 - a : ℝ) : ℂ) * cexp ((n * (Real.log pp - Real.log pm) : ℝ) * I) := by
  simp only [packetPhase, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [show (Real.log pm - (Real.log pm + Real.log pp) / 2) * (2 * n) =
      -(n * (Real.log pp - Real.log pm)) by ring,
    show (Real.log pp - (Real.log pm + Real.log pp) / 2) * (2 * n) =
      n * (Real.log pp - Real.log pm) by ring]

/-- **(38).** For every real `θ`: `|cos θ| ≥ 8/11`, `|cos 2θ| ≥ 8/15`, or `|cos 3θ| ≥ 1/2`. -/
theorem three_harmonic_cos (θ : ℝ) :
    8 / 11 ≤ |Real.cos θ| ∨ 8 / 15 ≤ |Real.cos (2 * θ)| ∨ 1 / 2 ≤ |Real.cos (3 * θ)| := by
  by_contra H
  push Not at H
  obtain ⟨h1, h2, h3⟩ := H
  rw [Real.cos_two_mul] at h2
  rw [Real.cos_three_mul] at h3
  set c := Real.cos θ
  set y := |c| with hy
  have hy0 : 0 ≤ y := abs_nonneg c
  have hyc : y ^ 2 = c ^ 2 := sq_abs c
  have h2' := (abs_lt.mp h2)
  have hy2 : 7 / 30 < y ^ 2 := by rw [hyc]; linarith
  have hy12 : 12 / 25 < y := by nlinarith
  have hcube : |4 * c ^ 3 - 3 * c| = y * (3 - 4 * y ^ 2) := by
    rw [show 4 * c ^ 3 - 3 * c = c * (4 * c ^ 2 - 3) by ring, abs_mul, ← hy, ← hyc,
      abs_of_neg (by nlinarith)]
    ring
  rw [hcube] at h3
  rcases le_or_gt y (3 / 5) with hy35 | hy35
  · nlinarith
  · nlinarith

/-! ## Every positive two-scale packet fails -/

theorem two_scale_weights_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ (![a, 1 - a] : Fin 2 → ℝ) j := by
  intro j _
  fin_cases j
  · simpa using ha0
  · simpa using ha1

theorem two_scale_weights_sum (a : ℝ) :
    ∑ j ∈ (Finset.univ : Finset (Fin 2)), (![a, 1 - a] : Fin 2 → ℝ) j = 1 := by
  simp [Fin.sum_univ_two]

/-- **The three-harmonic obstruction for two-scale packets (37)–(38).** There are `ε > 0` and
`L₀` such that every positive normalized packet on two scales `p₋, p₊` with midpoint log scale
`L ≥ L₀` and log separation `|Δ| ≤ εL` has, for **every** real gauge `μ`, a negative modulus
defect in the open physical strip. -/
theorem exists_two_scale_packet_threshold :
    ∃ ε > 0, ∃ L₀ > 0, ∀ a pm pp μ : ℝ, 0 ≤ a → a ≤ 1 → 0 < pm → 0 < pp →
      L₀ ≤ (Real.log pm + Real.log pp) / 2 →
      |Real.log pp - Real.log pm| ≤ ε * ((Real.log pm + Real.log pp) / 2) →
      ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧ portImbalance (packetGaugePort Finset.univ ![a, 1 - a]
        ![pm, pp] ((Real.log pm + Real.log pp) / 2) μ) w < 0 := by
  obtain ⟨a2, b2⟩ := thetaPortLogDeriv_cone_two
  obtain ⟨a4, b4⟩ := thetaPortLogDeriv_cone_four
  obtain ⟨a6, b6⟩ := thetaPortLogDeriv_cone_six
  obtain ⟨ε₂, hε₂, L₂, hL₂, H₂⟩ := exists_packet_wall_threshold (ι := Fin 2) (h := 2)
    (c := 8 / 11) (by norm_num) (by linarith) (by linarith)
  obtain ⟨ε₄, hε₄, L₄, hL₄, H₄⟩ := exists_packet_wall_threshold (ι := Fin 2) (h := 4)
    (c := 8 / 15) (by norm_num) (by linarith) (by linarith)
  obtain ⟨ε₆, hε₆, L₆, hL₆, H₆⟩ := exists_packet_wall_threshold (ι := Fin 2) (h := 6)
    (c := 1 / 2) (by norm_num) (by linarith) (by linarith)
  refine ⟨min ε₂ (min ε₄ ε₆), lt_min hε₂ (lt_min hε₄ hε₆), max L₂ (max L₄ L₆),
    lt_max_of_lt_left hL₂, ?_⟩
  intro a pm pp μ ha0 ha1 hpm hpp hL hΔ
  have hL0 : 0 < (Real.log pm + Real.log pp) / 2 := hL₂.trans_le ((le_max_left _ _).trans hL)
  have hp : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 < (![pm, pp] : Fin 2 → ℝ) j := by
    intro j _; fin_cases j
    · simpa using hpm
    · simpa using hpp
  have hdev : ∀ ε', min ε₂ (min ε₄ ε₆) ≤ ε' → ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      |Real.log ((![pm, pp] : Fin 2 → ℝ) j) - (Real.log pm + Real.log pp) / 2| ≤
        ε' * ((Real.log pm + Real.log pp) / 2) := by
    intro ε' hε' j _
    have hmono := mul_le_mul_of_nonneg_right hε' hL0.le
    have hhalf : |Real.log pp - Real.log pm| / 2 ≤ |Real.log pp - Real.log pm| :=
      half_le_self (abs_nonneg _)
    fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [show Real.log pm - (Real.log pm + Real.log pp) / 2 =
        -((Real.log pp - Real.log pm) / 2) by ring, abs_neg, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [show Real.log pp - (Real.log pm + Real.log pp) / 2 =
        (Real.log pp - Real.log pm) / 2 by ring, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
  have hv := two_scale_weights_nonneg ha0 ha1
  have hs := two_scale_weights_sum a
  rcases three_harmonic_cos (Real.log pp - Real.log pm) with h | h | h
  · refine H₂ _ _ _ _ μ hv hs hp ((le_max_left _ _).trans hL)
      (hdev ε₂ (min_le_left _ _)) ?_
    have := packetPhase_two_scale a pm pp 1
    rw [mul_one, one_mul] at this
    rw [this]
    exact h.trans (abs_cos_le_norm_two_point_phase a _)
  · refine H₄ _ _ _ _ μ hv hs hp (((le_max_left _ _).trans (le_max_right _ _)).trans hL)
      (hdev ε₄ ((min_le_right _ _).trans (min_le_left _ _))) ?_
    rw [show (4 : ℝ) = 2 * 2 by norm_num, packetPhase_two_scale]
    exact h.trans (abs_cos_le_norm_two_point_phase a _)
  · refine H₆ _ _ _ _ μ hv hs hp (((le_max_right _ _).trans (le_max_right _ _)).trans hL)
      (hdev ε₆ ((min_le_right _ _).trans (min_le_right _ _))) ?_
    rw [show (6 : ℝ) = 2 * 3 by norm_num, packetPhase_two_scale]
    exact h.trans (abs_cos_le_norm_two_point_phase a _)

/-- **Two-scale packets, sequence form.** For arbitrary weights `v_R ∈ [0,1]`, midpoint scale
`L_R → ∞` and separation `Δ_R = o(L_R)` (tending to zero, to a positive limit, or to infinity
sublinearly), eventually every gauge gives a negative strip defect. -/
theorem eventually_two_scale_packet_defect {a pm pp : ℕ → ℝ} (ha0 : ∀ R, 0 ≤ a R)
    (ha1 : ∀ R, a R ≤ 1) (hpm : ∀ R, 0 < pm R) (hpp : ∀ R, 0 < pp R)
    (hL : Tendsto (fun R => (Real.log (pm R) + Real.log (pp R)) / 2) atTop atTop)
    (hΔ : Tendsto (fun R => (Real.log (pp R) - Real.log (pm R)) /
      ((Real.log (pm R) + Real.log (pp R)) / 2)) atTop (𝓝 0)) :
    ∀ᶠ R in atTop, ∀ μ : ℝ, ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧
      portImbalance (packetGaugePort Finset.univ ![a R, 1 - a R] ![pm R, pp R]
        ((Real.log (pm R) + Real.log (pp R)) / 2) μ) w < 0 := by
  obtain ⟨ε, hε, L₀, hL₀, H⟩ := exists_two_scale_packet_threshold
  have habs := hΔ.abs
  rw [abs_zero] at habs
  filter_upwards [hL.eventually (eventually_ge_atTop L₀), habs.eventually (eventually_lt_nhds hε)]
    with R hR1 hR2 μ
  have hLR : 0 < (Real.log (pm R) + Real.log (pp R)) / 2 := hL₀.trans_le hR1
  rw [abs_div, abs_of_pos hLR, div_lt_iff₀ hLR] at hR2
  exact H _ _ _ μ (ha0 R) (ha1 R) (hpm R) (hpp R) hR1 hR2.le

/-! ## The balanced three-scale repair fails at the fourth harmonic -/

/-- The ideal log offsets `-π/4, 0, π/4`. -/
def threeScaleOffset : Fin 3 → ℝ := ![-(Real.pi / 4), 0, Real.pi / 4]

theorem abs_threeScaleOffset_le (k : Fin 3) : |threeScaleOffset k| ≤ Real.pi / 4 := by
  have := Real.pi_pos
  fin_cases k
  · simp [threeScaleOffset, abs_of_pos (by positivity : 0 < Real.pi / 4)]
  · simp only [threeScaleOffset]; simp; positivity
  · simp [threeScaleOffset, abs_of_pos (by positivity : 0 < Real.pi / 4)]

/-- The ideal equal-weight packet at offsets `-π/4, 0, π/4` has
`B(2n) = (1 + 2 cos(nπ/2))/3`. -/
theorem packetPhase_three_scale_ideal (L : ℝ) (n : ℝ) :
    packetPhase Finset.univ (fun _ => 1 / 3) (fun k => Real.exp (L + threeScaleOffset k)) L
      (2 * n) = ((1 + 2 * Real.cos (n * (Real.pi / 2))) / 3 : ℝ) := by
  simp only [packetPhase, Fin.sum_univ_three, Real.log_exp, threeScaleOffset,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, add_sub_cancel_left, zero_mul, Complex.ofReal_zero, Complex.exp_zero]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Complex.ofReal_re, mul_one]
    rw [show -(Real.pi / 4) * (2 * n) = -(n * (Real.pi / 2)) by ring,
      show Real.pi / 4 * (2 * n) = n * (Real.pi / 2) by ring, Real.cos_neg]
    ring
  · simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_im, Complex.one_im, mul_zero]
    rw [show -(Real.pi / 4) * (2 * n) = -(n * (Real.pi / 2)) by ring,
      show Real.pi / 4 * (2 * n) = n * (Real.pi / 2) by ring, Real.sin_neg]
    ring

/-- The ideal three-scale amplitudes: `1/3, -1/3, 1/3` at heights `2, 4, 6` (so (38) cannot
force a failure there), and `B(8) = 1`. -/
theorem three_scale_ideal_amplitudes (L : ℝ) :
    packetPhase Finset.univ (fun _ => 1 / 3) (fun k => Real.exp (L + threeScaleOffset k)) L 2 =
        1 / 3 ∧
      packetPhase Finset.univ (fun _ => 1 / 3) (fun k => Real.exp (L + threeScaleOffset k)) L 4 =
        -(1 / 3) ∧
      packetPhase Finset.univ (fun _ => 1 / 3) (fun k => Real.exp (L + threeScaleOffset k)) L 6 =
        1 / 3 ∧
      packetPhase Finset.univ (fun _ => 1 / 3) (fun k => Real.exp (L + threeScaleOffset k)) L 8 =
        1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (2 : ℝ) = 2 * 1 by norm_num, packetPhase_three_scale_ideal, one_mul,
      Real.cos_pi_div_two]; push_cast; ring
  · rw [show (4 : ℝ) = 2 * 2 by norm_num, packetPhase_three_scale_ideal,
      show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.cos_pi]; push_cast; ring
  · rw [show (6 : ℝ) = 2 * 3 by norm_num, packetPhase_three_scale_ideal,
      show (3 : ℝ) * (Real.pi / 2) = Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_pi_div_two]; push_cast; ring
  · rw [show (8 : ℝ) = 2 * 4 by norm_num, packetPhase_three_scale_ideal,
      show (4 : ℝ) * (Real.pi / 2) = 2 * Real.pi by ring, Real.cos_two_pi]; push_cast; ring

/-- Characteristic values of two scale families differ by at most `ρ|β|` when every log scale
moves by at most `ρ`. -/
theorem norm_packetPhase_sub_packetPhase_le {ι : Type*} {s : Finset ι} {v : ι → ℝ}
    (hv : ∀ j ∈ s, 0 ≤ v j) (hs : ∑ j ∈ s, v j = 1) {p p' : ι → ℝ} {L β ρ : ℝ}
    (hρ : ∀ j ∈ s, |Real.log (p j) - Real.log (p' j)| ≤ ρ) :
    ‖packetPhase s v p L β - packetPhase s v p' L β‖ ≤ ρ * |β| := by
  rw [packetPhase, packetPhase, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ j ∈ s, v j * (ρ * |β|) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hv j hj)]
        refine mul_le_mul_of_nonneg_left ((norm_cexp_mul_I_sub_le _ _).trans ?_) (hv j hj)
        rw [show (Real.log (p j) - L) * β - (Real.log (p' j) - L) * β =
          (Real.log (p j) - Real.log (p' j)) * β by ring, abs_mul]
        exact mul_le_mul_of_nonneg_right (hρ j hj) (abs_nonneg _)
    _ = ρ * |β| := by rw [← Finset.sum_mul, hs, one_mul]

/-- **The three-scale repair fails at height `8`.** There are `ρ > 0` and `L₁` such that for
every `L ≥ L₁`: prime triples with log scales within `ρ` of `L - π/4, L, L + π/4` exist (prime
number theorem), and every positive triple within `ρ` of these offsets gives an equal-weight packet
port with a negative strip defect for **every** real gauge (`|B(8)| ≈ 1` against the height-8 cone
`Im z₈ > 2 Re z₈ > 0`). -/
theorem exists_three_scale_packet_failure :
    ∃ ρ > 0, ∃ L₁ : ℝ, ∀ L, L₁ ≤ L →
      (∃ q : Fin 3 → ℕ, (∀ k, (q k).Prime) ∧
        ∀ k, |Real.log (q k) - (L + threeScaleOffset k)| ≤ ρ) ∧
      ∀ q : Fin 3 → ℝ, (∀ k, 0 < q k) → (∀ k, |Real.log (q k) - (L + threeScaleOffset k)| ≤ ρ) →
        ∀ μ : ℝ, ∃ w : ℂ, 0 < w.re ∧ w.re < 1 / 2 ∧
          portImbalance (packetGaugePort Finset.univ (fun _ => 1 / 3) q L μ) w < 0 := by
  obtain ⟨a8, b8⟩ := thetaPortLogDeriv_cone_eight
  set z₈ := thetaPortLogDeriv (1 / 2 + (8 : ℝ) * I)
  have hb : 0 < z₈.im := by linarith
  set c := (z₈.im + 2 * z₈.re) / (2 * z₈.im) with hcdef
  have hc0 : 0 < c := by positivity
  have hc : 2 * z₈.re < c * z₈.im := by
    rw [hcdef, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]; nlinarith
  have hc1 : c < 1 := by rw [hcdef, div_lt_one (by positivity)]; linarith
  obtain ⟨ε, hε, L₀, hL₀, H⟩ := exists_packet_wall_threshold (ι := Fin 3) (h := 8) hc0 hb hc
  set ρ := (1 - c) / 8 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  obtain ⟨T₀, hT₀⟩ := exists_prime_log_near (ρ := 2 * ρ) (by positivity)
  have hπ := Real.pi_pos
  refine ⟨ρ, hρ0, max (max L₀ ((Real.pi / 4 + ρ) / ε)) (T₀ / 2 + Real.pi / 4), ?_⟩
  intro L hL
  have hL1 : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hL2 : (Real.pi / 4 + ρ) / ε ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL3 : T₀ / 2 + Real.pi / 4 ≤ L := (le_max_right _ _).trans hL
  constructor
  · have hex : ∀ k : Fin 3, ∃ p : ℕ, p.Prime ∧
        |Real.log p - (L + threeScaleOffset k)| ≤ ρ := by
      intro k
      have hk := (abs_le.mp (abs_threeScaleOffset_le k)).1
      obtain ⟨p, hp, h1, h2⟩ := hT₀ (2 * (L + threeScaleOffset k)) (by linarith)
      exact ⟨p, hp, abs_le.mpr ⟨by linarith, by linarith⟩⟩
    choose q hq1 hq2 using hex
    exact ⟨q, hq1, hq2⟩
  · intro q hq hdev μ
    refine H Finset.univ (fun _ => 1 / 3) q L μ (fun _ _ => by norm_num)
      (by simp) (fun k _ => hq k) hL1 (fun k _ => ?_) ?_
    · have h1 := hdev k
      have h2 := abs_threeScaleOffset_le k
      have h3 : Real.pi / 4 + ρ ≤ ε * L := by rwa [div_le_iff₀ hε, mul_comm] at hL2
      calc |Real.log (q k) - L| = |(Real.log (q k) - (L + threeScaleOffset k)) +
            threeScaleOffset k| := by ring_nf
        _ ≤ |Real.log (q k) - (L + threeScaleOffset k)| + |threeScaleOffset k| := abs_add_le _ _
        _ ≤ ε * L := by linarith
    · have hid := (three_scale_ideal_amplitudes L).2.2.2
      have hcmp := norm_packetPhase_sub_packetPhase_le (s := Finset.univ) (L := L) (β := 8)
        (v := fun _ => 1 / 3) (p := q) (p' := fun k => Real.exp (L + threeScaleOffset k))
        (fun _ _ => by norm_num) (by simp)
        (fun k _ => by rw [Real.log_exp]; exact hdev k)
      rw [hid, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at hcmp
      have h3 := norm_sub_norm_le (1 : ℂ)
        (packetPhase Finset.univ (fun _ => 1 / 3) q L 8)
      rw [norm_one, norm_sub_rev] at h3
      rw [hρ] at hcmp
      linarith

end

end RHTower
