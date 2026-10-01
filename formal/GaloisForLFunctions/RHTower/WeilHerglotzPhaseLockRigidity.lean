import GaloisForLFunctions.RHTower.WeilFractionalMassAtomicRigidity

/-!
# Phase-locked Herglotz producers are `Λ`

Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and let `Φ` be holomorphic on `Re s > ½` with
`Re Φ ≥ 0` there and `Φ(s) = Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s}` on `Re s > 1` (the Herglotz
form of Weil positivity).  Let `G` solve `G' = Φ G` on `Re s > ½`, be continuous on `Re s ≥ ½`, and
agree with `s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{-s}/log n)` at `s = 2`.

**Theorem** (`phase_lock_rigidity`).  If for some `Y ≥ 0` and `κ ≠ 0`
`G(½ − iy) = κ G(½ + iy)` for all `y > Y`, then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann
hypothesis holds.

For real `lam` one has `G(s̄) = conj G(s)`, so the hypothesis says that the phase of `G` on the
critical line is eventually constant modulo `π`.  Nothing is assumed about the boundary measure of
`Φ` (atomic or not) beyond the continuity of `G` up to the line.

**Proof.**
* `G = s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{-s}/log n)` on `Re s > 1` (equal logarithmic derivatives).
* `G` has no zero on `Re s > ½`: on a disc `Φ` has a primitive `F`, so `G = c e^{F}` there, and a
  zero would make `G` vanish identically.
* `Re Φ ≥ 0` makes `|G(σ + iτ)|` increase in `σ`; with Stirling at `σ = 2` and the lower bound for
  `Γ_ℝ` on the critical line this gives the decay and polynomial bounds of the twisted Hamburger
  theorem (`HamburgerTwisted.coeff_eq_of_critical_line_twisted_defect`) with twist parameter `κ`:
  on the lower half-line `G(1 − s) = κ⁻¹ G(s)`.  The coefficients of `exp(Σ lam(n) n^{-s}/log n)` are constant, so it is `ζ`.
* Then `G = s(s−1)Λ(s)` on `Re s > ½`, and `G` has no zero there.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace PhaseLockRigidity

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity

noncomputable section

section General

variable {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}

/-- `G = s(s−1)Γ_ℝ(s) exp(Σ lam(n) n^{-s}/log n)` on `Re s > 1`. -/
theorem G_eq_bigG (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {s : ℂ} (hs : 1 < s.re) : G s = bigG lam s := by
  set V : Set ℂ := {z : ℂ | 1 < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : Convex ℝ V := convex_halfSpace_re_gt 1
  have hne : ∀ z ∈ V, bigG lam z ≠ 0 := fun z hz => bigG_ne_zero lam hz
  have hhalf : ∀ z ∈ V, 1 / 2 < z.re := fun z hz => by
    have : (1 : ℝ) < z.re := hz
    linarith
  set r : ℂ → ℂ := fun z => G z / bigG lam z with hr
  have hrd : DifferentiableOn ℂ r V := fun z hz =>
    ((hGd z (hhalf z hz)).differentiableAt.div (hasDerivAt_bigG hsl hz).differentiableAt
      (hne z hz)).differentiableWithinAt
  have hderiv : Set.EqOn (deriv r) 0 V := by
    intro z hz
    have hd : HasDerivAt r _ z := (hGd z (hhalf z hz)).div (hasDerivAt_bigG hsl hz) (hne z hz)
    rw [hd.deriv, hid z hz]
    have hze : zetaArchimedeanDatum z = 1 / z + gammaRealLogConnection z := by
      unfold zetaArchimedeanDatum gammaRealLogConnection; ring
    rw [hze]
    simp only [Pi.zero_apply]
    ring
  have h2 : (2 : ℂ) ∈ V := by simp [hV]
  have hc := hVo.is_const_of_deriv_eq_zero hVc.isPreconnected hrd hderiv hs h2
  simp only [hr] at hc
  rw [hG2, div_self (hne 2 h2), div_eq_one_iff_eq (hne s hs)] at hc
  exact hc

/-- `G` has no zero on `Re s > ½`. -/
theorem G_ne_zero (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) : G ρ ≠ 0 := by
  intro hzero
  set U : Set ℂ := {s : ℂ | 1 / 2 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set r : ℝ := ρ.re - 1 / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hball : Metric.ball ρ r ⊆ U := fun z hz => by
    have hd : ‖z - ρ‖ < r := mem_ball_iff_norm.mp hz
    have h1 : |z.re - ρ.re| ≤ ‖z - ρ‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 := abs_lt.mp (h1.trans_lt hd)
    show 1 / 2 < z.re
    linarith [h2.1]
  obtain ⟨F, hF⟩ := (hΦd.mono hball).isExactOn_ball
  -- `G e^{-F}` is constant on the disc
  set H : ℂ → ℂ := fun z => G z * Complex.exp (-F z) with hH
  have hHd : ∀ z ∈ Metric.ball ρ r, HasDerivAt H 0 z := by
    intro z hz
    have h1 := hGd z (hball hz)
    have h2 := ((hF z hz).neg).cexp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    ring
  have hconst : ∀ z ∈ Metric.ball ρ r, H z = H ρ := by
    intro z hz
    have hdo : DifferentiableOn ℂ H (Metric.ball ρ r) := fun w hw =>
      (hHd w hw).differentiableAt.differentiableWithinAt
    have hdz : Set.EqOn (deriv H) 0 (Metric.ball ρ r) := fun w hw => (hHd w hw).deriv
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball ρ r).isPreconnected hdo hdz
      hz (Metric.mem_ball_self hr0)
  have hH0 : H ρ = 0 := by simp only [hH, hzero, zero_mul]
  have hGball : ∀ z ∈ Metric.ball ρ r, G z = 0 := by
    intro z hz
    have h := hconst z hz
    rw [hH0] at h
    simp only [hH] at h
    exact (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)
  -- the identity theorem on the half-plane
  have hGa : AnalyticOnNhd ℂ G U := by
    have : DifferentiableOn ℂ G U := fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt
    exact this.analyticOnNhd hUo
  have hev : G =ᶠ[𝓝 ρ] (fun _ => (0 : ℂ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0)] with z hz
    exact hGball z hz
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
  have hglob := hGa.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected hρ hev h2U
  have hG2' : G 2 ≠ 0 := by rw [hG2]; exact bigG_ne_zero lam (by norm_num)
  exact hG2' hglob

end General

section Hamburger

variable {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}

/-- **Horizontal monotonicity.**  `|G(σ + iτ)| ≤ |G(2 + iτ)|` for `½ ≤ σ ≤ 2`. -/
theorem norm_G_le_two (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s)
    {σ : ℝ} (τ : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 2) : ‖G (σ + τ * I)‖ ≤ ‖G (2 + τ * I)‖ := by
  set φ : ℝ → ℝ := fun x => ‖G (x + τ * I)‖ ^ 2 with hφ
  have hcont : ContinuousOn φ (Set.Icc (1 / 2) 2) := by
    intro x hx
    have hre : 1 / 2 ≤ ((x : ℂ) + τ * I).re := by simpa using hx.1
    have h := (hGc _ hre).comp (f := fun y : ℝ => (y : ℂ) + τ * I) (by fun_prop)
    exact (h.norm.pow 2).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt φ
      (2 * inner ℝ (G (x + τ * I)) (Φ (x + τ * I) * G (x + τ * I))) x := by
    intro x hx
    have hre : 1 / 2 < ((x : ℂ) + τ * I).re := by simpa using hx.1
    have hd2 : HasDerivAt (fun y : ℂ => G (y + τ * I)) (Φ (x + τ * I) * G (x + τ * I)) (x : ℂ) :=
      (hGd _ hre).comp_add_const _ _
    exact hd2.comp_ofReal.norm_sq
  have hnonneg : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2,
      0 ≤ 2 * inner ℝ (G (x + τ * I)) (Φ (x + τ * I) * G (x + τ * I)) := by
    intro x hx
    rw [Complex.inner]
    set g := G (x + τ * I)
    set φ' := Φ (x + τ * I)
    have e : φ' * g * (starRingEnd ℂ) g = ((Complex.normSq g : ℝ) : ℂ) * φ' := by
      rw [mul_assoc, Complex.mul_conj]; ring
    rw [e, Complex.re_ofReal_mul]
    have hre : 1 / 2 < ((x : ℂ) + τ * I).re := by simpa using hx.1
    exact mul_nonneg (by norm_num) (mul_nonneg (Complex.normSq_nonneg _) (hΦre _ hre))
  have hmono : MonotoneOn φ (Set.Icc (1 / 2) 2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderiv x hx).deriv]
      exact hnonneg x hx
  have h := hmono ⟨h1, h2⟩ ⟨by norm_num, le_rfl⟩ h2
  simp only [hφ] at h
  push_cast at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- `β = G(1)/2`. -/
def betaG (G : ℂ → ℂ) : ℂ := G 1 / 2

/-- `G − β · s(s−1)Γ_ℝ(s−1)`, which vanishes at `s = 1`. -/
def numG (G : ℂ → ℂ) (s : ℂ) : ℂ := G s - betaG G * mFactor s

/-- `E(s) = G(s)/(s(s−1)) − β Γ_ℝ(s−1)`, continued across `s = 1`. -/
def bigEG (G : ℂ → ℂ) (s : ℂ) : ℂ := dslope (numG G) 1 s / s

theorem numG_one : numG G 1 = 0 := by
  unfold numG betaG; rw [mFactor_one]; ring

theorem bigEG_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    bigEG G s = G s / (s * (s - 1)) - betaG G * Complex.Gammaℝ (s - 1) := by
  unfold bigEG
  rw [dslope_of_ne _ h1, slope_def_module, numG_one, sub_zero, smul_eq_mul]
  unfold numG
  rw [mFactor_eq h1]
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp

theorem differentiableOn_bigEG (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) :
    DifferentiableOn ℂ (bigEG G) {s : ℂ | 1 / 2 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hN : DifferentiableOn ℂ (numG G) {s : ℂ | 1 / 2 < s.re} := fun s hs => by
    have hs' : (1 / 2 : ℝ) < s.re := hs
    exact ((hGd s hs').differentiableAt.sub
      ((differentiableAt_mFactor (by linarith)).const_mul _)).differentiableWithinAt
  have hD : DifferentiableOn ℂ (dslope (numG G) 1) {s : ℂ | 1 / 2 < s.re} :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds (by norm_num))).mpr hN
  intro s hs
  have hs0 : s ≠ 0 := by
    intro h
    have hs' : (1 / 2 : ℝ) < s.re := hs
    rw [h] at hs'; simp at hs'; linarith
  exact ((hD s hs).differentiableAt (hopen.mem_nhds hs)).div differentiableAt_id hs0
    |>.differentiableWithinAt

theorem continuousAt_bigEG (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousAt (bigEG G) s := by
  rcases eq_or_lt_of_le hs with heq | hlt
  · have hs1 : s ≠ 1 := ne_one_of_re_eq_half heq.symm
    have hs0 : s ≠ 0 := ne_zero_of_re_eq_half heq.symm
    have hN : ContinuousAt (numG G) s :=
      (hGc s hs).sub ((differentiableAt_mFactor (by rw [← heq]; norm_num)).continuousAt.const_mul _)
    have hf : ContinuousAt (fun z => (numG G z - numG G 1) / (z - 1) / z) s :=
      ((hN.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hs1)).div continuousAt_id hs0
    refine hf.congr ?_
    filter_upwards [(isClosed_singleton (x := (1 : ℂ))).isOpen_compl.mem_nhds hs1] with z hz
    have hz1 : z ≠ 1 := hz
    unfold bigEG
    rw [dslope_of_ne _ hz1, slope_def_module, smul_eq_mul]
    ring
  · exact ((differentiableOn_bigEG hGd) s hlt).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hlt) |>.continuousAt

/-- **Growth of `G` on the strip `½ ≤ Re s ≤ 2`.** -/
theorem exists_bound_G (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      ‖G (σ + τ * I)‖ ≤ C * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
  obtain ⟨C, N, hC, h⟩ := exists_bound_bigG_two hsl
  refine ⟨C, N, hC, fun σ τ h1 h2 => ?_⟩
  have hre : (1 : ℝ) < (2 + (τ : ℂ) * I).re := by simp
  refine (norm_G_le_two hΦre hGc hGd τ h1 h2).trans ?_
  rw [G_eq_bigG hsl hid hGd hG2 hre]
  exact h τ

/-- **Decay of `E`** on the closed strip `½ ≤ Re s ≤ 3/2`. -/
theorem exists_decay_bigEG (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2) :
    ∃ C : ℝ, ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖bigEG G s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := exists_bound_G hsl hΦre hid hGc hGd hG2
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_bound_pow_mul_exp_neg (N₁ + 2)
  obtain ⟨C₃, hC₃, h₃⟩ := exists_decay_Gammaℝ_sub_one
  have hK : IsCompact (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (bigEG G) (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4) :=
    fun z hz => by
      rw [Complex.mem_reProdIm] at hz
      exact (continuousAt_bigEG hGc hGd hz.1.1).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  set β := betaG G with hβ
  refine ⟨max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0), fun s hs => ?_⟩
  rw [mem_verticalStrip] at hs
  set τ := s.im with hτ
  have hpos : 0 < 1 + τ ^ 2 := by positivity
  rcases le_or_gt 4 |τ| with h4 | h4
  · have hn1 : 4 ≤ ‖s‖ := h4.trans (Complex.abs_im_le_norm s)
    have hn2 : 4 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    have h0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hn1; norm_num at hn1
    have h1 : s ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hn2; norm_num at hn2
    rw [bigEG_eq h0 h1]
    have hs_eq : (s.re : ℂ) + τ * I = s := Complex.re_add_im s
    have hg : ‖G s‖ ≤ C₁ * ((|τ| + 4) ^ N₁ * Real.exp (-(Real.pi * |τ| / 4))) := by
      rw [← hs_eq]
      exact h₁ s.re τ hs.1 (by linarith [hs.2])
    have hdec := pow_mul_exp_neg_le_div hK₁ (abs_nonneg τ)
    rw [sq_abs] at hdec
    have hden : 1 ≤ ‖s * (s - 1)‖ := by
      rw [norm_mul]; nlinarith
    have hΓ := h₃ s hs.1 hs.2 h4
    calc ‖G s / (s * (s - 1)) - β * Complex.Gammaℝ (s - 1)‖
        ≤ ‖G s / (s * (s - 1))‖ + ‖β‖ * ‖Complex.Gammaℝ (s - 1)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖G s‖ + ‖β‖ * (C₃ / (1 + τ ^ 2)) := by
          gcongr
          rw [norm_div]
          exact div_le_self (norm_nonneg _) hden
      _ ≤ C₁ * (K₁ / (1 + τ ^ 2)) + ‖β‖ * (C₃ / (1 + τ ^ 2)) := by
          gcongr
          exact hg.trans (mul_le_mul_of_nonneg_left hdec hC₁)
      _ = (C₁ * K₁ + ‖β‖ * C₃) / (1 + τ ^ 2) := by ring
      _ ≤ max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0) / (1 + τ ^ 2) := by
          gcongr; exact le_max_left _ _
  · have hab := abs_lt.mp h4
    have hmem : s ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4 := by
      rw [Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, ⟨hab.1.le, hab.2.le⟩⟩
    have hb := (hB s hmem).trans (le_max_left B 0)
    have hτ2 : τ ^ 2 ≤ 16 := by nlinarith
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    calc ‖bigEG G s‖ ≤ max B 0 := hb
      _ ≤ 17 * max B 0 / (1 + τ ^ 2) := by
          rw [le_div_iff₀ hpos]; nlinarith
      _ ≤ max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0) / (1 + τ ^ 2) := by
          gcongr; exact le_max_right _ _

/-- The boundary value `Φ_b(τ) = f(½ + 2iτ)`. -/
def phiG (G : ℂ → ℂ) (τ : ℝ) : ℂ :=
  G (lineS τ) / (lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ))

/-- The reflection defect at `½ + 2iτ`. -/
def gG (G : ℂ → ℂ) (τ : ℝ) : ℂ :=
  (G (lineS τ) - G (1 - lineS τ)) / (lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ))

theorem bigEG_add_eq_phiG (τ : ℝ) :
    bigEG G (lineS τ) + betaG G * Complex.Gammaℝ (lineS τ - 1) =
      Complex.Gammaℝ (lineS τ) * phiG G τ := by
  rw [bigEG_eq (lineS_ne_zero τ) (lineS_ne_one τ)]
  unfold phiG
  have h1 : lineS τ - 1 ≠ 0 := sub_ne_zero.mpr (lineS_ne_one τ)
  have h0 := lineS_ne_zero τ
  have hΓ := Gammaℝ_lineS_ne_zero τ
  field_simp
  ring

theorem bigEG_sub_eq_gG {s : ℂ} (hs : s.re = 1 / 2) :
    bigEG G s - bigEG G (1 - s) =
      -(betaG G * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) +
        Complex.Gammaℝ s * gG G (s.im / 2) := by
  have hsl : lineS (s.im / 2) = s := by
    apply Complex.ext
    · rw [lineS_re, hs]
    · simp [lineS]; ring
  have h0 : s ≠ 0 := ne_zero_of_re_eq_half hs
  have h1 : s ≠ 1 := ne_one_of_re_eq_half hs
  have hre' : (1 - s).re = 1 / 2 := by simp [hs]; norm_num
  have h0' : 1 - s ≠ 0 := ne_zero_of_re_eq_half hre'
  have h1' : 1 - s ≠ 1 := ne_one_of_re_eq_half hre'
  rw [bigEG_eq h0 h1, bigEG_eq h0' h1']
  unfold gG
  rw [hsl]
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hden : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
  rw [hden, show (1 : ℂ) - s - 1 = -s by ring]
  field_simp
  ring

theorem continuous_phiG (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) :
    Continuous (phiG G) := by
  have hl : Continuous lineS := by unfold lineS; fun_prop
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  have hG' : ContinuousAt (fun τ => G (lineS τ)) τ :=
    (hGc _ (le_of_eq (lineS_re τ).symm)).comp hl.continuousAt
  have hΓ : ContinuousAt (fun τ => Complex.Gammaℝ (lineS τ)) τ :=
    ((differentiableAt_Gammaℝ (by rw [lineS_re]; norm_num)).continuousAt).comp hl.continuousAt
  have hden : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
      (Gammaℝ_lineS_ne_zero τ)
  exact hG'.div ((hl.continuousAt.mul (hl.continuousAt.sub continuousAt_const)).mul hΓ) hden

theorem continuous_gG (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s) :
    Continuous (gG G) := by
  have hl : Continuous lineS := by unfold lineS; fun_prop
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  have hG' : ContinuousAt (fun τ => G (lineS τ)) τ :=
    (hGc _ (le_of_eq (lineS_re τ).symm)).comp hl.continuousAt
  have hG'' : ContinuousAt (fun τ => G (1 - lineS τ)) τ := by
    have hre : 1 / 2 ≤ (1 - lineS τ).re := by rw [one_sub_lineS, lineS_re]
    exact (hGc _ hre).comp (f := fun τ => 1 - lineS τ) ((continuous_const.sub hl).continuousAt)
  have hΓ : ContinuousAt (fun τ => Complex.Gammaℝ (lineS τ)) τ :=
    ((differentiableAt_Gammaℝ (by rw [lineS_re]; norm_num)).continuousAt).comp hl.continuousAt
  have hden : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
      (Gammaℝ_lineS_ne_zero τ)
  exact (hG'.sub hG'').div ((hl.continuousAt.mul (hl.continuousAt.sub continuousAt_const)).mul hΓ)
    hden

/-- **Polynomial bounds** for the boundary value and the defect. -/
theorem exists_poly_bound_lineG
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2) :
    ∃ CB : ℝ, ∃ N : ℕ, 0 ≤ CB ∧ ∀ τ : ℝ, ‖phiG G τ‖ ≤ CB * (1 + |τ|) ^ N ∧
      ‖gG G τ‖ ≤ CB * (1 + |τ|) ^ N := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := exists_bound_G hsl hΦre hid hGc hGd hG2
  obtain ⟨cl, hcl, M, hlow⟩ := exists_lower_bound_Gammaℝ_half_line
  refine ⟨2 * (4 * C₁ / cl) * 4 ^ N₁ * 2 ^ M, N₁ + M, by positivity, fun τ => ?_⟩
  have hτ := abs_nonneg τ
  set v : ℝ := 2 * τ with hv
  have hav : |v| = 2 * |τ| := by rw [hv, abs_mul, abs_two]
  set e4 := Real.exp (-(Real.pi * |v| / 4)) with he4
  have he40 : 0 < e4 := Real.exp_pos _
  have hg1 : ‖G (lineS τ)‖ ≤ C₁ * ((|v| + 4) ^ N₁ * e4) := by
    rw [lineS_eq, ← hv, he4]
    have h := h₁ (1 / 2) v le_rfl (by norm_num)
    have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    rwa [e] at h
  have hg2 : ‖G (1 - lineS τ)‖ ≤ C₁ * ((|v| + 4) ^ N₁ * e4) := by
    rw [one_sub_lineS, lineS_eq, he4]
    have h := h₁ (1 / 2) (2 * -τ) le_rfl (by norm_num)
    have habs : |2 * -τ| = |v| := by rw [hv, mul_neg, abs_neg]
    rw [habs] at h
    have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    rwa [e] at h
  have hΓl := hlow v
  rw [← lineS_eq] at hΓl
  have hden : cl * e4 / ((1 + |v|) ^ M) * (1 / 4) ≤
      ‖lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)‖ := by
    rw [norm_mul]
    have h1 := norm_lineS_mul_sub_one τ
    have h2 : cl * e4 / ((1 + |v|) ^ M) ≤ ‖Complex.Gammaℝ (lineS τ)‖ := by
      rw [div_le_iff₀ (by positivity)]; linarith
    calc cl * e4 / ((1 + |v|) ^ M) * (1 / 4) = (1 / 4) * (cl * e4 / ((1 + |v|) ^ M)) := by ring
      _ ≤ ‖lineS τ * (lineS τ - 1)‖ * ‖Complex.Gammaℝ (lineS τ)‖ :=
          mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  have hdenpos : 0 < cl * e4 / ((1 + |v|) ^ M) * (1 / 4) := by positivity
  have hp1 : (|v| + 4) ^ N₁ ≤ 4 ^ N₁ * (1 + |τ|) ^ N₁ := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by rw [hav]; linarith) _
  have hp2 : (1 + |v|) ^ M ≤ 2 ^ M * (1 + |τ|) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by rw [hav]; linarith) _
  have key : ∀ X : ℂ, ‖X‖ ≤ 2 * (C₁ * ((|v| + 4) ^ N₁ * e4)) →
      ‖X / (lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ))‖ ≤
        2 * (4 * C₁ / cl) * 4 ^ N₁ * 2 ^ M * (1 + |τ|) ^ (N₁ + M) := by
    intro X hX
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le hdenpos hden)]
    refine hX.trans ?_
    calc 2 * (C₁ * ((|v| + 4) ^ N₁ * e4))
        = 2 * (4 * C₁ / cl) * (|v| + 4) ^ N₁ * (1 + |v|) ^ M *
            (cl * e4 / ((1 + |v|) ^ M) * (1 / 4)) := by
          field_simp
      _ ≤ 2 * (4 * C₁ / cl) * (4 ^ N₁ * (1 + |τ|) ^ N₁) * (2 ^ M * (1 + |τ|) ^ M) *
            ‖lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)‖ := by
          gcongr
      _ = 2 * (4 * C₁ / cl) * 4 ^ N₁ * 2 ^ M * (1 + |τ|) ^ (N₁ + M) *
            ‖lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)‖ := by
          rw [pow_add]; ring
  refine ⟨key _ ?_, key _ ?_⟩
  · have := norm_nonneg (G (lineS τ))
    nlinarith [mul_nonneg hC₁ (mul_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ |v| + 4) N₁)
      he40.le)]
  · exact (norm_sub_le _ _).trans (by linarith)

end Hamburger

/-! ### Phase-locked producers are `Λ` -/

/-- **Approximately phase-locked Herglotz producers are `Λ`, and the Riemann hypothesis
holds.**  Let `Φ` be the Herglotz form of a Weil-positive weight system `lam`
(holomorphic on `Re s > ½`, `Re Φ ≥ 0`, `Φ = Γ̃ + 1/(s−1) − Σ lam(n)n^{-s}` on `Re s > 1`), and `G` a
solution of `G' = ΦG` on `Re s > ½`, continuous on `Re s ≥ ½`, with
`G(2) = 2·Γ_ℝ(2)·exp(Σ lam(n)n^{-2}/log n)`.  Suppose that on the lower critical half-line
`s = ½ + 2iτ`, `τ < -Y`, the reflection `G(1 − s) = κ⁻¹ G(s) + s(s−1)Γ_ℝ(s) e(τ)` holds with
`κ ≠ 0` and an error `e` that is polynomially bounded and Abel-sublinear.  Then `lam(n) = Λ(n)` for
every `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem phase_lock_rigidity_of_defect {lam : ℕ → ℝ} {Φ G : ℂ → ℂ} {e : ℝ → ℂ} {Ce : ℝ} {Nₑ : ℕ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    (hem : Measurable e) (heb : ∀ t, ‖e t‖ ≤ Ce * (1 + |t|) ^ Nₑ)
    (heA : Tendsto (fun δ => δ * HamburgerStability.abelMass e δ) (𝓝[>] 0) (𝓝 0))
    {Y : ℝ} (hY : 0 ≤ Y) {κ : ℂ} (hκ : κ ≠ 0)
    (hlock : ∀ τ : ℝ, τ < -Y → G (1 - lineS τ) =
      κ⁻¹ * G (lineS τ) + lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) * e τ) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hid' : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s := hid
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable (hLa σ (by simpa using hσ)).1
  obtain ⟨C, hC⟩ := exists_decay_bigEG hsl hΦre hid' hGc hGd hG2
  obtain ⟨CB₀, N₀, hCB₀, hB₀⟩ := exists_poly_bound_lineG hsl hΦre hid' hGc hGd hG2
  have hCe : 0 ≤ Ce := by
    have := (norm_nonneg _).trans (heb 0)
    simpa using this
  set CB := max CB₀ Ce with hCB
  set N := N₀ + Nₑ with hN
  have hpow : ∀ t : ℝ, ∀ k : ℕ, k ≤ N → (1 + |t|) ^ k ≤ (1 + |t|) ^ N := fun t k hk =>
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hk
  have hbound : ∀ {h : ℝ → ℂ} {C₀ : ℝ} {k : ℕ}, k ≤ N → C₀ ≤ CB →
      (∀ t, ‖h t‖ ≤ C₀ * (1 + |t|) ^ k) → ∀ t, ‖h t‖ ≤ CB * (1 + |t|) ^ N := by
    intro h C₀ k hk hC h' t
    have h0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (by simpa using h' 0)
    calc ‖h t‖ ≤ C₀ * (1 + |t|) ^ k := h' t
      _ ≤ CB * (1 + |t|) ^ N := mul_le_mul hC (hpow t k hk) (by positivity)
          (le_trans h0 hC)
  have hdE := differentiableOn_bigEG hGd
  set β := betaG G with hβ
  have hlow : ∀ τ : ℝ, τ < -Y → gG G τ = (1 - κ⁻¹) * phiG G τ + (fun t => -e t) τ := by
    intro τ hτ
    have hD : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
        (Gammaℝ_lineS_ne_zero τ)
    unfold gG phiG
    rw [hlock τ hτ]
    set D := lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) with hDdef
    set X := G (lineS τ)
    show (X - (κ⁻¹ * X + D * e τ)) / D = (1 - κ⁻¹) * (X / D) + -e τ
    field_simp
    ring
  have hrA : Tendsto (fun δ => δ * HamburgerStability.abelMass (fun t => -e t) δ) (𝓝[>] 0)
      (𝓝 0) := by
    have : (fun δ => δ * HamburgerStability.abelMass (fun t => -e t) δ) =
        fun δ => δ * HamburgerStability.abelMass e δ := by
      funext δ; simp [HamburgerStability.abelMass]
    rw [this]; exact heA
  have hcoef := HamburgerTwisted.coeff_eq_of_critical_line_twisted_defect
    (a := a) ha (E := bigEG G) (β := β) (C := C) (g := gG G)
    (Φ := phiG G) (r' := fun t => -e t) (CB := CB) (N := N)
    (fun z hz => by
      rw [mem_verticalStrip] at hz
      exact (continuousAt_bigEG hGc hGd hz.1).continuousWithinAt)
    (hdE.mono fun z hz => by show (1 / 2 : ℝ) < z.re; exact hz.1)
    hC
    (fun s hs => by
      have h1 : 1 < s.re := by rw [hs]; norm_num
      have h0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
      have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [coeffDirichlet_eq_LSeries, (hLa s h1).2, bigEG_eq h0 hs1,
        G_eq_bigG hsl hid' hGd hG2 h1]
      unfold bigG
      field_simp
      ring)
    (fun s hs => bigEG_sub_eq_gG hs)
    (fun τ => bigEG_add_eq_phiG τ)
    (continuous_gG hGc).measurable
    (hbound (k := N₀) (by omega) (le_max_left _ _) (fun t => (hB₀ t).2))
    (continuous_phiG hGc).measurable
    (hbound (k := N₀) (by omega) (le_max_left _ _) (fun t => (hB₀ t).1))
    hem.neg
    (hbound (k := Nₑ) (by omega) (le_max_right _ _) (fun t => by rw [norm_neg]; exact heb t))
    hrA hY hκ hlow
  -- all coefficients equal `a 1 = 1`
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have h2β : 2 * κ * β = 1 := by rw [← hcoef 0, ha1]
  have hall : ∀ {n : ℕ}, n ≠ 0 → a n = (1 : ℕ → ℂ) n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hcoef k, h2β]; rfl
  have hζ : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s := by
    intro s hs
    rw [← (hLa s hs).2, LSeries_congr hall s, LSeries_one_eq_riemannZeta hs]
  have hLam : ∀ s : ℂ, 1 < s.re →
      LSeries (lamTwo lam) s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    intro s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : riemannZeta =ᶠ[𝓝 s] zetaOf lam := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact (hζ z hz).symm
    have hd := (hasDerivAt_zetaOf hsl hs).congr_of_eventuallyEq hev
    have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hd.deriv, hζ s hs]
    field_simp
  have habs1 : LSeries.abscissaOfAbsConv (lamTwo lam) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lseriesSummable_of_le (norm_lamTwo_le lam) hsl (by simpa using hy))
      (EReal.coe_lt_top 1)
  have habs2 :
      LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
      (EReal.coe_lt_top 1)
  have hEv : (fun x : ℝ => LSeries (lamTwo lam) x) =ᶠ[atTop]
      fun x : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hLam x (by simpa using hx)
  refine ⟨fun n hn => ?_, ?_⟩
  · have h := LSeries.eq_of_LSeries_eventually_eq habs1 habs2 hEv (n := n) (by omega)
    simp only [lamTwo, if_pos hn] at h
    exact_mod_cast h
  · by_contra hRH
    obtain ⟨ρ, hρ0, hρ1, hρ2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    set Z : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta₀ s + 1 with hZ
    have hZd : Differentiable ℂ Z := by
      have := differentiable_completedZeta₀
      intro s; simp only [hZ]; fun_prop
    set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hZa : AnalyticOnNhd ℂ Z U := hZd.differentiableOn.analyticOnNhd hUo
    have hGa : AnalyticOnNhd ℂ G U := by
      have : DifferentiableOn ℂ G U := fun z hz =>
        (hGd z hz).differentiableAt.differentiableWithinAt
      exact this.analyticOnNhd hUo
    have hZΛ : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Z s = s * (s - 1) * completedRiemannZeta s := by
      intro s h0 h1
      have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
      simp only [hZ]
      rw [completedRiemannZeta_eq]
      field_simp
      ring
    have hΛζ : ∀ s : ℂ, 0 < s.re → completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      intro s hs
      have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
      rw [riemannZeta_def_of_ne_zero h0]
      field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : G =ᶠ[𝓝 (2 : ℂ)] Z := by
      filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      have hz' : 1 < z.re := hz
      have h0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
      have h1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
      rw [hZΛ z h0 h1, hΛζ z (by linarith), ← hζ z hz', G_eq_bigG hsl hid' hGd hG2 hz']
      unfold bigG; ring
    have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
    have hglob := hGa.eqOn_of_preconnected_of_eventuallyEq hZa
      (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected h2U hev hρ1
    have hρne0 : ρ ≠ 0 := by intro h; rw [h] at hρ1; simp at hρ1; linarith
    have hρne1 : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
    have hzero : G ρ = 0 := by
      rw [hglob, hZΛ ρ hρne0 hρne1, hΛζ ρ (by linarith), hρ0, mul_zero, mul_zero]
    exact G_ne_zero hΦd hGd hG2 hρ1 hzero

/-- **Phase-locked Herglotz producers are `Λ`, and the Riemann hypothesis holds.**  As in
`phase_lock_rigidity_of_defect`, with an exact lock: `G(½ − iy) = κ G(½ + iy)` for all `y > Y`.
For real `lam` this says that the critical-line phase of `G` is eventually constant modulo `π`. -/
theorem phase_lock_rigidity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re → Φ s = zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {Y : ℝ} (hY : 0 ≤ Y) {κ : ℂ} (hκ : κ ≠ 0)
    (hlock : ∀ y : ℝ, Y < y → G (1 / 2 - y * I) = κ * G (1 / 2 + y * I)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hzeroA : Tendsto (fun δ : ℝ => δ * HamburgerStability.abelMass (fun _ : ℝ => (0 : ℂ)) δ)
      (𝓝[>] 0) (𝓝 0) := by
    have : (fun δ : ℝ => δ * HamburgerStability.abelMass (fun _ : ℝ => (0 : ℂ)) δ) =
        fun _ => 0 := by
      funext δ; simp [HamburgerStability.abelMass]
    rw [this]; exact tendsto_const_nhds
  refine phase_lock_rigidity_of_defect (e := fun _ => 0) (Ce := 0) (Nₑ := 0) hsl hΦd hΦre hid hGc
    hGd hG2 measurable_const (fun t => by simp) hzeroA (Y := Y / 2) (by linarith) hκ ?_
  intro τ hτ
  have hy : Y < -(2 * τ) := by linarith
  have hl1 : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by rw [lineS_eq]; push_cast; ring
  have hl2 : 1 - lineS τ = 1 / 2 + ((-(2 * τ) : ℝ) : ℂ) * I := by
    rw [one_sub_lineS, lineS_eq]; push_cast; ring
  have hrefl : G (lineS τ) = κ * G (1 - lineS τ) := by
    rw [hl2, hl1]; exact hlock _ hy
  rw [hrefl, mul_zero, add_zero, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]

end

end PhaseLockRigidity

end RHTower
