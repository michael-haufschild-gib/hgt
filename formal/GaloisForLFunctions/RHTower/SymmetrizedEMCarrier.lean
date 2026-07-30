/-
The symmetrized Euler–Maclaurin carrier: exact functional equation AND
fixed-annulus accuracy in one finite member.

The Riemann–Siegel carrier `gN` satisfies the exact χ-functional equation but its
accuracy is a classical debt; the Euler–Maclaurin carrier has machine-checked accuracy
but no functional equation.  χ-symmetrizing the EM carrier produces a member with both:
`semCarrier N = emCarrier N + χ·emCarrier N(1−·)` targets `2ζ` — since
`ζ(s) = χ(s)ζ(1−s)`, the two EM errors add — with remainder `O(N^(−σ))` uniformly on any
compact annulus in the strip, while the χ-symmetrization identity gives the exact
asymmetric functional equation for EVERY seed, hence the completed member
`archFactor·semCarrier/2` satisfies the exact EVEN functional equation and its vanishing
orders pair under `s ↦ 1−s` — the mirror certificate is free.  For `N` large the
completed member dominates ξ on the slit charts of an isolating annulus,
unconditionally, so every ladder rung again reduces to the divisibility of a finite
member's hole count — now for a member carrying ξ's own symmetry.
-/
import GaloisForLFunctions.RHTower.EMAnnulusSupply

noncomputable section

namespace RHTower

open Complex Metric Filter

/-! ### §1 A generic domination supply from uniform decay -/

/-- **Domination from uniform decay against a nonvanishing target.**  If a family of
members approximates a continuous nonvanishing target on a compact set with error
`≤ C·N^(−σ)`, then some member dominates: the target's positive floor beats the decaying
error. -/
theorem exists_domination_of_uniform_decay {K : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) {f : ℂ → ℂ} (hf : ContinuousOn f K)
    (hfne : ∀ z ∈ K, f z ≠ 0) {h : ℕ → ℂ → ℂ} {C σ : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N → ∀ z ∈ K, ‖f z - h N z‖ ≤ C * (N : ℝ) ^ (-σ)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z ∈ K, ‖f z - h N z‖ < ‖h N z‖ := by
  obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn hne hf.norm
  have hδ : 0 < ‖f x‖ := norm_pos_iff.mpr (hfne x hxK)
  have hC1 : 0 < C + 1 := by linarith
  have hε' : 0 < ‖f x‖ / 2 / (C + 1) := by positivity
  have htend : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-σ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hσ).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hNε, hN1⟩ :=
    ((htend.eventually (gt_mem_nhds hε')).and (eventually_ge_atTop 1)).exists
  refine ⟨N, hN1, ?_⟩
  intro z hz
  have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have herr : ‖f z - h N z‖ < ‖f x‖ / 2 := by
    have h1 : ‖f z - h N z‖ ≤ C * (N : ℝ) ^ (-σ) := hbound N hN1 z hz
    have h2 : C * (N : ℝ) ^ (-σ) ≤ (C + 1) * (N : ℝ) ^ (-σ) := by nlinarith
    have h3 : (C + 1) * (N : ℝ) ^ (-σ) < (C + 1) * (‖f x‖ / 2 / (C + 1)) :=
      mul_lt_mul_of_pos_left hNε hC1
    have h4 : (C + 1) * (‖f x‖ / 2 / (C + 1)) = ‖f x‖ / 2 := by field_simp
    linarith
  have htri : ‖f z‖ ≤ ‖f z - h N z‖ + ‖h N z‖ := by
    calc ‖f z‖ = ‖f z - h N z + h N z‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hfl : ‖f x‖ ≤ ‖f z‖ := hmin hz
  linarith

/-! ### §2 The symmetrized EM carrier and its exact functional equation -/

/-- The symmetrized Euler–Maclaurin carrier, targeting `2ζ`. -/
def semCarrier (N : ℕ) : ℂ → ℂ := chiSymmetrize zetaChi (emCarrier N)

/-- The exact asymmetric functional equation of the symmetrized EM carrier —
unconditional on the strip. -/
theorem semCarrier_one_sub {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    semCarrier N (1 - s) = zetaChi (1 - s) * semCarrier N s :=
  chiSymmetrize_one_sub_at (zetaChi_mul_one_sub_of_mem_strip h0 h1)

/-- The symmetrized EM carrier is analytic on the open critical strip. -/
theorem semCarrier_analyticAt {N : ℕ} (hN : 1 ≤ N) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < 1) :
    AnalyticAt ℂ (semCarrier N) z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hem : AnalyticAt ℂ (emCarrier N) z := emCarrier_analyticAt_of_ne_one hN hz1
  have haff : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := analyticAt_const.sub analyticAt_id
  have hem1 : AnalyticAt ℂ (fun s : ℂ => emCarrier N (1 - s)) z := by
    have h1z1 : (1 : ℂ) - z ≠ 1 := by
      intro h
      apply hz0
      have := congrArg (fun w => 1 - w) h
      simpa using this
    have h := (emCarrier_analyticAt_of_ne_one hN h1z1).comp haff
    simpa [Function.comp] using! h
  have hχ : AnalyticAt ℂ zetaChi z := by
    apply zetaChi_analyticAt
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact hem.add (hχ.mul hem1)

/-! ### §3 Accuracy: the symmetrized carrier targets 2ζ -/

/-- **Machine-checked accuracy of the symmetrized EM carrier against `2ζ`**: by the
χ-functional equation of ζ the two Euler–Maclaurin remainders add. -/
theorem two_zeta_sub_semCarrier_norm_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖2 * riemannZeta s - semCarrier N s‖
      ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re
        + ‖zetaChi s‖ * (‖1 - s‖ * (N : ℝ) ^ (-(1 - s).re) / (1 - s).re) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have h1s_re : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h1s_ne1 : (1 : ℂ) - s ≠ 1 := by
    intro h
    apply hs0
    have := congrArg (fun w => 1 - w) h
    simpa using this
  have hG1 : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos h1s_re
  have hFE : riemannZeta s = zetaChi s * riemannZeta (1 - s) :=
    zeta_eq_zetaChi_mul hs0 hs1 hG1
  have hid : 2 * riemannZeta s - semCarrier N s
      = (riemannZeta s - emCarrier N s)
        + zetaChi s * (riemannZeta (1 - s) - emCarrier N (1 - s)) := by
    unfold semCarrier chiSymmetrize
    linear_combination hFE
  rw [hid]
  calc ‖(riemannZeta s - emCarrier N s)
        + zetaChi s * (riemannZeta (1 - s) - emCarrier N (1 - s))‖
      ≤ ‖riemannZeta s - emCarrier N s‖
        + ‖zetaChi s * (riemannZeta (1 - s) - emCarrier N (1 - s))‖ := norm_add_le _ _
    _ = ‖riemannZeta s - emCarrier N s‖
        + ‖zetaChi s‖ * ‖riemannZeta (1 - s) - emCarrier N (1 - s)‖ := by rw [norm_mul]
    _ ≤ _ := add_le_add (zeta_sub_emCarrier_norm_le hN h0 hs1)
        (mul_le_mul_of_nonneg_left
          (zeta_sub_emCarrier_norm_le hN h1s_re h1s_ne1) (norm_nonneg _))

/-! ### §4 The completed member: exact EVEN functional equation -/

/-- The completed symmetrized EM member `archFactor·semCarrier/2` — the finite object on
ξ's own layer, carrying ξ's own symmetry. -/
def completedSEM (N : ℕ) : ℂ → ℂ := fun s => archFactor s * semCarrier N s / 2

/-- **The completed symmetrized member satisfies the exact EVEN functional equation on
the strip — unconditionally.** -/
theorem completedSEM_one_sub {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    completedSEM N (1 - s) = completedSEM N s := by
  have h0' : 0 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hG1 : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0'
  unfold completedSEM archFactor
  rw [semCarrier_one_sub h0 h1]
  unfold zetaChi
  rw [show (1 : ℂ) - (1 - s) = s from by ring]
  field_simp
  ring

/-- **The mirror certificate is free**: vanishing orders of the completed symmetrized
member pair exactly under `s ↦ 1−s` on the strip. -/
theorem completedSEM_orderAt_one_sub {N : ℕ} {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt (completedSEM N) (1 - z) = analyticOrderAt (completedSEM N) z := by
  have h0' : 0 < (1 - z).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h1' : (1 - z).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hmem : {w : ℂ | 0 < w.re ∧ w.re < 1} ∈ nhds (1 - z) := hopen.mem_nhds ⟨h0', h1'⟩
  have hev : completedSEM N =ᶠ[nhds (1 - z)] fun w => completedSEM N (1 - w) := by
    filter_upwards [hmem] with w hw
    exact (completedSEM_one_sub hw.1 hw.2).symm
  rw [analyticOrderAt_congr hev, analyticOrderAt_one_sub]

/-- The completed symmetrized member is analytic on the open critical strip. -/
theorem completedSEM_analyticOnNhd_strip {N : ℕ} (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ (completedSEM N) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  intro z hz
  exact ((archFactor_analyticOnNhd_re_pos z hz.1).mul
    (semCarrier_analyticAt hN hz.1 hz.2)).div_const

/-- The archimedean factor divides out: completed-level domination for the symmetrized
member is equivalent to the raw inequality against `2ζ`. -/
theorem completedSEM_domination_iff {N : ℕ} {s : ℂ} (hσ : 0 < s.re) (h1 : s ≠ 1) :
    (‖xi s - completedSEM N s‖ < ‖completedSEM N s‖)
      ↔ (‖2 * riemannZeta s - semCarrier N s‖ < ‖semCarrier N s‖) := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hσ
  unfold completedSEM
  rw [xi_eq_archFactor_mul_zeta h0 h1 hG]
  rw [show archFactor s * riemannZeta s - archFactor s * semCarrier N s / 2
      = (archFactor s / 2) * (2 * riemannZeta s)
        - (archFactor s / 2) * semCarrier N s from by ring]
  rw [show archFactor s * semCarrier N s / 2
      = (archFactor s / 2) * semCarrier N s from by ring]
  exact norm_mul_sub_lt_iff (div_ne_zero (archFactor_ne_zero h0 h1 hG) two_ne_zero)

/-! ### §5 Uniform decay on the compact annulus -/

/-- **Uniform decay of the symmetrized EM error on a compact annulus in the strip**:
constants depending only on the annulus bound the error by `C·N^(−σ)`. -/
theorem sem_uniform_decay_on_annulus {ρ : ℂ} {r₀ R : ℝ} (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hstrip : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1) :
    ∃ (C σ : ℝ), 0 < σ ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ z ∈ closedBall ρ R \ ball ρ r₀,
        ‖2 * riemannZeta z - semCarrier N z‖ ≤ C * (N : ℝ) ^ (-σ) := by
  set K := closedBall ρ R \ ball ρ r₀ with hKdef
  have hKsub : K ⊆ closedBall ρ R := fun z hz => hz.1
  have hKcompact : IsCompact K := (isCompact_closedBall ρ R).diff isOpen_ball
  have hne : K.Nonempty := annulus_closed_nonempty hr₀.le hrR
  obtain ⟨w0, hw0K, hw0min⟩ :=
    hKcompact.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨w1, hw1K, hw1max⟩ :=
    hKcompact.exists_isMaxOn hne Complex.continuous_re.continuousOn
  have hχcont : ContinuousOn zetaChi K := by
    intro z hz
    have h1z : 0 < (1 - z).re := by
      have := (hstrip z (hKsub hz)).2
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact (zetaChi_analyticAt
      (Gammaℝ_ne_zero_of_re_pos h1z)).continuousAt.continuousWithinAt
  obtain ⟨w2, hw2K, hw2max⟩ := hKcompact.exists_isMaxOn hne hχcont.norm
  have hσ₀pos : 0 < w0.re := (hstrip w0 (hKsub hw0K)).1
  have hσ₁pos : 0 < 1 - w1.re := by
    have := (hstrip w1 (hKsub hw1K)).2
    linarith
  have hRpos : 0 < R := lt_trans hr₀ hrR
  have hApos : 0 < ‖ρ‖ + R := add_pos_of_nonneg_of_pos (norm_nonneg ρ) hRpos
  refine ⟨(‖ρ‖ + R) / w0.re + ‖zetaChi w2‖ * ((1 + (‖ρ‖ + R)) / (1 - w1.re)),
    min w0.re (1 - w1.re), lt_min hσ₀pos hσ₁pos,
    add_nonneg (div_nonneg hApos.le hσ₀pos.le)
      (mul_nonneg (norm_nonneg _) (div_nonneg (by linarith) hσ₁pos.le)), ?_⟩
  intro N hN1 z hz
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hzs := hstrip z (hKsub hz)
  have hnormz : ‖z‖ ≤ ‖ρ‖ + R := by
    have h1 : ‖z - ρ‖ ≤ R := by
      have h := hKsub hz
      rwa [mem_closedBall, dist_eq_norm] at h
    calc ‖z‖ = ‖ρ + (z - ρ)‖ := by rw [show ρ + (z - ρ) = z from by ring]
      _ ≤ ‖ρ‖ + ‖z - ρ‖ := norm_add_le _ _
      _ ≤ ‖ρ‖ + R := by linarith
  have hrez : w0.re ≤ z.re := hw0min hz
  have hrez1 : 1 - w1.re ≤ (1 - z).re := by
    have hzle : z.re ≤ w1.re := hw1max hz
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hχz : ‖zetaChi z‖ ≤ ‖zetaChi w2‖ := hw2max hz
  have hx0 : (0 : ℝ) ≤ (N : ℝ) ^ (-min w0.re (1 - w1.re)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hb1 : (N : ℝ) ^ (-z.re) ≤ (N : ℝ) ^ (-min w0.re (1 - w1.re)) :=
    Real.rpow_le_rpow_of_exponent_le hN1'
      (by have := min_le_left w0.re (1 - w1.re); linarith)
  have hb2 : (N : ℝ) ^ (-(1 - z).re) ≤ (N : ℝ) ^ (-min w0.re (1 - w1.re)) :=
    Real.rpow_le_rpow_of_exponent_le hN1'
      (by have := min_le_right w0.re (1 - w1.re); linarith)
  refine le_trans (two_zeta_sub_semCarrier_norm_le hN1 hzs.1 hzs.2) ?_
  have hp1 : ‖z‖ * (N : ℝ) ^ (-z.re) / z.re
      ≤ (‖ρ‖ + R) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / w0.re :=
    div_le_div₀ (mul_nonneg hApos.le hx0)
      (mul_le_mul hnormz hb1 (Real.rpow_nonneg (Nat.cast_nonneg N) _) hApos.le)
      hσ₀pos hrez
  have hn1z : ‖(1 : ℂ) - z‖ ≤ 1 + (‖ρ‖ + R) := by
    calc ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one]
      _ ≤ 1 + (‖ρ‖ + R) := by linarith
  have hp2i : ‖1 - z‖ * (N : ℝ) ^ (-(1 - z).re) / (1 - z).re
      ≤ (1 + (‖ρ‖ + R)) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / (1 - w1.re) :=
    div_le_div₀ (mul_nonneg (by linarith) hx0)
      (mul_le_mul hn1z hb2 (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by linarith))
      hσ₁pos hrez1
  have hp2 : ‖zetaChi z‖ * (‖1 - z‖ * (N : ℝ) ^ (-(1 - z).re) / (1 - z).re)
      ≤ ‖zetaChi w2‖
        * ((1 + (‖ρ‖ + R)) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / (1 - w1.re)) :=
    mul_le_mul hχz hp2i
      (div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
        (lt_of_lt_of_le hσ₁pos hrez1).le)
      (norm_nonneg _)
  calc ‖z‖ * (N : ℝ) ^ (-z.re) / z.re
        + ‖zetaChi z‖ * (‖1 - z‖ * (N : ℝ) ^ (-(1 - z).re) / (1 - z).re)
      ≤ (‖ρ‖ + R) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / w0.re
        + ‖zetaChi w2‖
          * ((1 + (‖ρ‖ + R)) * (N : ℝ) ^ (-min w0.re (1 - w1.re)) / (1 - w1.re)) :=
        add_le_add hp1 hp2
    _ = ((‖ρ‖ + R) / w0.re + ‖zetaChi w2‖ * ((1 + (‖ρ‖ + R)) / (1 - w1.re)))
        * (N : ℝ) ^ (-min w0.re (1 - w1.re)) := by ring

/-! ### §6 Unconditional domination and the isolating supply -/

/-- **Unconditional raw domination for the symmetrized member on an isolating
annulus.** -/
theorem exists_sem_domination_on_annulus {ρ : ℂ} {r₀ R : ℝ} (hr₀ : 0 < r₀)
    (hrR : r₀ < R)
    (hstrip : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z ∈ closedBall ρ R \ ball ρ r₀,
      ‖2 * riemannZeta z - semCarrier N z‖ < ‖semCarrier N z‖ := by
  obtain ⟨C, σ, hσ, hC, hbound⟩ := sem_uniform_decay_on_annulus hr₀ hrR hstrip
  have hKsub : closedBall ρ R \ ball ρ r₀ ⊆ closedBall ρ R := fun z hz => hz.1
  have hz1K : ∀ z ∈ closedBall ρ R \ ball ρ r₀, z ≠ 1 := by
    intro z hz h
    have hlt := (hstrip z (hKsub hz)).2
    rw [h] at hlt
    simp at hlt
  refine exists_domination_of_uniform_decay
    ((isCompact_closedBall ρ R).diff isOpen_ball)
    (annulus_closed_nonempty hr₀.le hrR) ?_ ?_ hσ hC hbound
  · intro z hz
    exact (continuousAt_const.mul
      (differentiableAt_riemannZeta (hz1K z hz)).continuousAt).continuousWithinAt
  · intro z hz
    have hzρ : z ≠ ρ := by
      intro h
      exact hz.2 (by rw [h]; exact mem_ball_self hr₀)
    have hζne : riemannZeta z ≠ 0 := by
      intro hζ0
      exact hiso z (hKsub hz) hzρ
        ((xi_eq_zero_iff (hstrip z (hKsub hz)).1 (hz1K z hz)).mpr hζ0)
    exact mul_ne_zero two_ne_zero hζne

/-- **Isolating annulus with completed symmetrized-member domination —
unconditional.** -/
theorem exists_isolating_sem_domination (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ (r₀ R : ℝ) (N : ℕ), 0 < r₀ ∧ r₀ < R ∧ 1 ≤ N ∧
      (∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        ‖xi z - completedSEM N z‖ < ‖completedSEM N z‖) := by
  obtain ⟨R₁, hR₁, hiso₁⟩ := xi_exists_isolating_radius ρ
  set R := min (R₁ / 2) (min (ρ.re / 2) ((1 - ρ.re) / 2)) with hRdef
  have hRpos : 0 < R := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hRR₁ : R < R₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hRre : R ≤ ρ.re / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hRre1 : R ≤ (1 - ρ.re) / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hstripcb : ∀ z ∈ closedBall ρ R, 0 < z.re ∧ z.re < 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - ρ.re| ≤ R := by
      have h := Complex.abs_re_le_norm (z - ρ)
      rw [Complex.sub_re] at h
      linarith
    rw [abs_le] at hre
    constructor
    · linarith [hre.1]
    · linarith [hre.2]
  have hisocb : ∀ z ∈ closedBall ρ R, z ≠ ρ → xi z ≠ 0 := by
    intro z hz
    apply hiso₁
    rw [mem_ball]
    rw [mem_closedBall] at hz
    linarith
  obtain ⟨N, hN1, hdomK⟩ := exists_sem_domination_on_annulus
    (r₀ := R / 2) (by linarith) (by linarith) hstripcb hisocb
  refine ⟨R / 2, R, N, by linarith, by linarith, hN1,
    fun z hz => hstripcb z (ball_subset_closedBall hz),
    fun z hz => hisocb z (ball_subset_closedBall hz), ?_⟩
  intro z hz
  have hzK : z ∈ closedBall ρ R \ ball ρ (R / 2) := by
    rw [charts_union_eq_annulus ρ (by linarith : (0 : ℝ) ≤ R / 2)] at hz
    exact ⟨ball_subset_closedBall hz.1, fun hb => hz.2 (ball_subset_closedBall hb)⟩
  have hstripz := hstripcb z hzK.1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hstripz
    simp at hstripz
  exact (completedSEM_domination_iff hstripz.1 hz1).mpr (hdomK z hzK)

/-! ### §7 Dominating splits of the symmetric member and the rungs -/

/-- A dominating split of the completed symmetrized EM member on an isolating annulus
at `ρ`. -/
def SEMSplitData (ρ : ℂ) (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ) : Prop :=
  0 ≤ r₀ ∧ r₀ < R ∧
  (∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1) ∧
  (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
  (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) ∧
  AnalyticOnNhd ℂ u (ball ρ R) ∧ (∀ z ∈ ball ρ R, u z ≠ 0) ∧
  (∀ z ∈ ball ρ R, completedSEM N z = ((zs.map (fun w => z - w)).prod) * u z) ∧
  (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
    ‖xi z - completedSEM N z‖ < ‖completedSEM N z‖)

/-- **Dominating splits of the symmetric member exist unconditionally at every strip
point.** -/
theorem semSplitData_exists (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ), SEMSplitData ρ r₀ R N zs u := by
  obtain ⟨r₀, R, N, hr₀, hrR, hN1, hstripb, hiso, hdom⟩ :=
    exists_isolating_sem_domination ρ h0 h1
  have hFan : AnalyticOnNhd ℂ (completedSEM N) (ball ρ R) := fun z hz =>
    completedSEM_analyticOnNhd_strip hN1 z (hstripb z hz)
  obtain ⟨zs, u, hzs, huan, hune, hufact⟩ :=
    exists_split_of_domination hr₀.le hrR hFan hdom
  exact ⟨r₀, R, N, zs, u, hr₀.le, hrR, hstripb, hiso, hzs, huan, hune, hufact, hdom⟩

/-- **The hole count of any dominating symmetric split is the central vanishing
order.** -/
theorem semSplitData_count_eq {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) :
    (analyticOrderAt xi ρ).toNat = zs.length := by
  obtain ⟨h0, hrR, hstripb, hiso, hzs, huan, hune, hufact, hdom⟩ := h
  have hchartsub : ∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R, z ∈ ball ρ R := by
    intro z hz
    rw [charts_union_eq_annulus ρ h0] at hz
    exact hz.1
  exact enclosed_count_eq_of_split_domination h0 hrR hiso huan hune hzs
    (fun z hz => hufact z (hchartsub z hz)) hdom

/-- **Every ladder rung from divisibility of the symmetric member's hole count.** -/
theorem rhLadder_of_sem_split_multiplicity (k : ℕ)
    (hpar : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      SEMSplitData ρ r₀ R N zs u → 2 ^ k ∣ zs.length) :
    RHLadder k := by
  intro ρ hρ h0
  have hρre : 0 < ρ.re := lt_trans (by norm_num) (mem_rightHalf.mp hρ)
  obtain ⟨r₀, R, N, zs, u, hdata⟩ :=
    semSplitData_exists ρ hρre (xi_zero_re_lt_one hρre h0)
  have hdvd : 2 ^ k ∣ (analyticOrderAt xi ρ).toNat := by
    rw [semSplitData_count_eq hdata]
    exact hpar ρ hρ h0 r₀ R N zs u hdata
  have hm : (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) = analyticOrderAt xi ρ :=
    ENat.coe_toNat (xi_orderAt_ne_top ρ)
  obtain ⟨c, hc⟩ := hdvd
  rw [← hm, hc]
  exact ⟨(c : ℕ∞), by push_cast; ring⟩

/-- **The base rung from parity of the symmetric member's hole count alone.** -/
theorem rhLadder_one_of_sem_split_parity
    (hpar : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      SEMSplitData ρ r₀ R N zs u → Even zs.length) :
    RHLadder 1 := by
  refine rhLadder_of_sem_split_multiplicity 1 ?_
  intro ρ hρ h0 r₀ R N zs u hdata
  rw [pow_one]
  exact (hpar ρ hρ h0 r₀ R N zs u hdata).two_dvd

/-- **The Riemann Hypothesis from all-orders divisibility of the symmetric member's
hole counts.** -/
theorem riemannHypothesis_of_sem_split_multiplicity
    (hpar : ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
      SEMSplitData ρ r₀ R N zs u → 2 ^ k ∣ zs.length) :
    RiemannHypothesis :=
  rh_iff_forall_ladder.mpr fun k => rhLadder_of_sem_split_multiplicity k (hpar k)

/-! ### §8 Schwarz reality and the line reflection of the symmetric member -/

/-- Schwarz reality of the Euler–Maclaurin carrier: real Dirichlet coefficients plus a
real-coefficient pole term. -/
theorem emCarrier_conj (N : ℕ) (s : ℂ) :
    emCarrier N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (emCarrier N s) := by
  unfold emCarrier emPole
  rw [dirichletPoly_conj,
    show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) from by
      rw [map_sub, map_one],
    show (starRingEnd ℂ) s - 1 = (starRingEnd ℂ) (s - 1) from by
      rw [map_sub, map_one],
    natCast_cpow_conj, map_add, map_div₀]

/-- Schwarz reality of the symmetrized EM carrier. -/
theorem semCarrier_conj (N : ℕ) (s : ℂ) :
    semCarrier N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (semCarrier N s) := by
  unfold semCarrier chiSymmetrize
  rw [show (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) from by
        rw [map_sub, map_one],
      emCarrier_conj, emCarrier_conj, zetaChi_conj, map_add, map_mul]

/-- Schwarz reality of the completed symmetrized member. -/
theorem completedSEM_conj (N : ℕ) (s : ℂ) :
    completedSEM N ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedSEM N s) := by
  unfold completedSEM archFactor
  rw [Gammaℝ_conj, semCarrier_conj, map_div₀, map_mul, map_mul, map_div₀, map_mul,
    map_sub, map_one, map_ofNat]

/-- **The line reflection of the symmetric member**: across the critical line the
completed symmetrized EM member reflects by conjugation, exactly as ξ does — the finite
member carries both symmetries of ξ at every truncation length. -/
theorem completedSEM_lineReflection {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    completedSEM N (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (completedSEM N s) := by
  have hconj0 : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  have hconj1 : ((starRingEnd ℂ) s).re < 1 := by rwa [Complex.conj_re]
  rw [completedSEM_one_sub hconj0 hconj1, completedSEM_conj]

/-- Reality pairing of orders for the symmetric member on the strip. -/
theorem completedSEM_orderAt_conj {N : ℕ} (hN : 1 ≤ N) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt (completedSEM N) ((starRingEnd ℂ) z)
      = analyticOrderAt (completedSEM N) z :=
  analyticOrderAt_conj_of_conjEquivariant (completedSEM_conj N)
    (completedSEM_analyticOnNhd_strip hN z ⟨h0, h1⟩)
    (completedSEM_analyticOnNhd_strip hN _
      ⟨by rwa [Complex.conj_re], by rwa [Complex.conj_re]⟩)

/-- **The same-height mirror order pairing of the symmetric member**: at the
line-reflected point `1 − conj z` the completed symmetrized EM member vanishes to
exactly the order it has at `z`.  The pooled two-hole count of any mirror argument is
even for free; only a single hole's parity can carry arithmetic. -/
theorem completedSEM_orderAt_lineReflect {N : ℕ} (hN : 1 ≤ N) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt (completedSEM N) (lineReflect z)
      = analyticOrderAt (completedSEM N) z := by
  have hc0 : 0 < ((starRingEnd ℂ) z).re := by rwa [Complex.conj_re]
  have hc1 : ((starRingEnd ℂ) z).re < 1 := by rwa [Complex.conj_re]
  rw [show lineReflect z = 1 - (starRingEnd ℂ) z from rfl,
    completedSEM_orderAt_one_sub hc0 hc1, completedSEM_orderAt_conj hN h0 h1]

end RHTower
