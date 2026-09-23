/-
The seam-edge parity functional: the mod-2 seam ledger is read off from two endpoint
signs.

For a carrier that is real on the critical line, the sign product of its real values at
the two endpoints of a line segment detects the parity of the enclosed vanishing: on a
zero-free segment the product is positive, and on a segment enclosing a single zero of
multiplicity `m` the product is positive exactly when `m` is even.  Mechanism: the linear
factor is purely imaginary along the line (`linePt τ − linePt τ₀ = i(τ − τ₀)`), so the
rotated cofactor `i^m·h` is real-valued and of constant sign on the segment, leaving the
sign `(−1)^m` of the real factor `(τ − τ₀)^m` across the zero.

Consequently the level-two seam-jump multiplier `exp(2πi·m/2) = (−1)^m` of an on-seam
zero equals `+1` or `−1` according to the endpoint sign product: the seam contribution to
a box ledger is boundary data, computed from two point evaluations with no zero counting
and no argument principle.
-/
import GaloisForLFunctions.RHTower.SeamCocycle
import GaloisForLFunctions.RHTower.ArchEnvelope

namespace RHTower

open Complex Metric

/-- The seam sign of a carrier over a line segment: the product of the real values at
the two endpoints. -/
noncomputable def seamSign (f : ℂ → ℂ) (t₁ t₂ : ℝ) : ℝ :=
  (f (linePt t₁)).re * (f (linePt t₂)).re

/-- A continuous real function without zeros on a segment has positive endpoint
product. -/
theorem endpoint_sign_product_pos {F : ℝ → ℝ} {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hcont : ContinuousOn F (Set.Icc t₁ t₂))
    (hne : ∀ τ ∈ Set.Icc t₁ t₂, F τ ≠ 0) :
    0 < F t₁ * F t₂ := by
  have h₁ := hne t₁ (Set.left_mem_Icc.mpr h12)
  have h₂ := hne t₂ (Set.right_mem_Icc.mpr h12)
  rcases lt_or_gt_of_ne h₁ with h₁n | h₁p <;> rcases lt_or_gt_of_ne h₂ with h₂n | h₂p
  · exact mul_pos_of_neg_of_neg h₁n h₂n
  · obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc h12 hcont
      (Set.mem_Icc.mpr ⟨h₁n.le, h₂p.le⟩)
    exact absurd hFσ (hne σ hσ)
  · obtain ⟨σ, hσ, hFσ⟩ := intermediate_value_Icc' h12 hcont
      (Set.mem_Icc.mpr ⟨h₂n.le, h₁p.le⟩)
    exact absurd hFσ (hne σ hσ)
  · exact mul_pos h₁p h₂p

/-- **Zero-free seam edges have positive seam sign.**  A carrier that is real and
nonvanishing along a line segment keeps one sign there, so its endpoint product is
positive. -/
theorem seamSign_pos_of_ne_zero {f : ℂ → ℂ} {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hcont : ContinuousOn (fun τ : ℝ => (f (linePt τ)).re) (Set.Icc t₁ t₂))
    (hreal : ∀ τ ∈ Set.Icc t₁ t₂, (f (linePt τ)).im = 0)
    (hne : ∀ τ ∈ Set.Icc t₁ t₂, f (linePt τ) ≠ 0) :
    0 < seamSign f t₁ t₂ := by
  have hF : ∀ τ ∈ Set.Icc t₁ t₂, (f (linePt τ)).re ≠ 0 := by
    intro τ hτ h0
    exact hne τ hτ (Complex.ext (by simpa using h0) (by simpa using hreal τ hτ))
  exact endpoint_sign_product_pos h12 hcont hF

/-- **The seam-edge parity law.**  If a carrier that is real on the line factors through
a single on-line zero of multiplicity `m` interior to the segment, with nonvanishing
analytic cofactor on a disc containing the segment, then the seam sign is positive
exactly when `m` is even.  The linear factor is purely imaginary along the line, so the
rotated cofactor `i^m·h` is real-valued of constant sign, and the real factor
`(τ − τ₀)^m` contributes the sign `(−1)^m` across the zero. -/
theorem seamSign_one_zero_iff_even {f h : ℂ → ℂ} {τ₀ t₁ t₂ R : ℝ} {m : ℕ}
    (h1 : t₁ < τ₀) (h2 : τ₀ < t₂)
    (hseg : ∀ τ ∈ Set.Icc t₁ t₂, linePt τ ∈ ball (linePt τ₀) R)
    (hh : AnalyticOnNhd ℂ h (ball (linePt τ₀) R))
    (hh0 : ∀ z ∈ ball (linePt τ₀) R, h z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τ₀) R, f z = (z - linePt τ₀) ^ m * h z)
    (hreal : ∀ τ ∈ Set.Icc t₁ t₂, (f (linePt τ)).im = 0) :
    (0 < seamSign f t₁ t₂ ↔ Even m) := by
  have h12 : t₁ ≤ t₂ := le_of_lt (lt_trans h1 h2)
  have hτ₀mem : τ₀ ∈ Set.Icc t₁ t₂ := ⟨h1.le, h2.le⟩
  set G : ℝ → ℂ := fun τ => Complex.I ^ m * h (linePt τ) with hG_def
  have hlinecont : Continuous fun τ : ℝ => linePt τ := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasDerivAt_linePt u).continuousAt
  have hGcont : ContinuousOn G (Set.Icc t₁ t₂) := by
    apply ContinuousOn.mul continuousOn_const
    exact (hh.continuousOn).comp hlinecont.continuousOn (fun τ hτ => hseg τ hτ)
  have hexpand : ∀ τ ∈ Set.Icc t₁ t₂,
      f (linePt τ) = (((τ - τ₀) ^ m : ℝ) : ℂ) * G τ := by
    intro τ hτ
    have hlin : linePt τ - linePt τ₀ = ((τ - τ₀ : ℝ) : ℂ) * Complex.I := by
      unfold linePt
      push_cast
      ring
    rw [hfact (linePt τ) (hseg τ hτ), hlin, mul_pow]
    simp only [hG_def]
    push_cast
    ring
  have hGim_off : ∀ τ ∈ Set.Icc t₁ t₂, τ ≠ τ₀ → (G τ).im = 0 := by
    intro τ hτ hne'
    have him := hreal τ hτ
    rw [hexpand τ hτ, Complex.im_ofReal_mul] at him
    rcases mul_eq_zero.mp him with hc | hgim
    · exact absurd hc (pow_ne_zero m (sub_ne_zero.mpr hne'))
    · exact hgim
  have hGim : ∀ τ ∈ Set.Icc t₁ t₂, (G τ).im = 0 := by
    intro τ hτ
    by_cases hττ₀ : τ = τ₀
    · rw [hττ₀]
      have hsub : Set.Ioo τ₀ t₂ ⊆ Set.Icc t₁ t₂ := fun x hx =>
        ⟨by linarith [hx.1], hx.2.le⟩
      have hcont_im : ContinuousOn (fun σ => (G σ).im) (Set.Icc t₁ t₂) :=
        Complex.continuous_im.comp_continuousOn hGcont
      have hcw : ContinuousWithinAt (fun σ => (G σ).im) (Set.Ioo τ₀ t₂) τ₀ :=
        (hcont_im τ₀ hτ₀mem).mono hsub
      haveI hnb : (nhdsWithin τ₀ (Set.Ioo τ₀ t₂)).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo h2.ne]
        exact Set.left_mem_Icc.mpr h2.le
      have hlim0 : Filter.Tendsto (fun σ => (G σ).im)
          (nhdsWithin τ₀ (Set.Ioo τ₀ t₂)) (nhds 0) := by
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hGim_off x (hsub hx) (ne_of_gt hx.1)).symm
      exact tendsto_nhds_unique hcw hlim0
    · exact hGim_off τ hτ hττ₀
  have hGre_ne : ∀ τ ∈ Set.Icc t₁ t₂, (G τ).re ≠ 0 := by
    intro τ hτ h0
    have hGz : G τ = 0 := Complex.ext (by simpa using h0) (by simpa using hGim τ hτ)
    have hmul : Complex.I ^ m * h (linePt τ) = 0 := by
      simpa [hG_def] using hGz
    rcases mul_eq_zero.mp hmul with hI | hh'
    · exact pow_ne_zero m Complex.I_ne_zero hI
    · exact hh0 _ (hseg τ hτ) hh'
  have hGre_cont : ContinuousOn (fun τ => (G τ).re) (Set.Icc t₁ t₂) :=
    Complex.continuous_re.comp_continuousOn hGcont
  have hP : 0 < (G t₁).re * (G t₂).re :=
    endpoint_sign_product_pos h12 hGre_cont hGre_ne
  have hend : ∀ τ ∈ Set.Icc t₁ t₂, (f (linePt τ)).re = (τ - τ₀) ^ m * (G τ).re := by
    intro τ hτ
    rw [hexpand τ hτ, Complex.re_ofReal_mul]
  have hsign : seamSign f t₁ t₂ =
      ((t₁ - τ₀) * (t₂ - τ₀)) ^ m * ((G t₁).re * (G t₂).re) := by
    show (f (linePt t₁)).re * (f (linePt t₂)).re = _
    rw [hend t₁ (Set.left_mem_Icc.mpr h12), hend t₂ (Set.right_mem_Icc.mpr h12),
      mul_pow]
    ring
  have hc : (t₁ - τ₀) * (t₂ - τ₀) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) (by linarith)
  constructor
  · intro hpos
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hneg : ((t₁ - τ₀) * (t₂ - τ₀)) ^ m < 0 := hodd.pow_neg hc
    have hlt : seamSign f t₁ t₂ < 0 := by
      rw [hsign]
      exact mul_neg_of_neg_of_pos hneg hP
    linarith
  · intro heven
    rw [hsign]
    exact mul_pos (heven.pow_pos hc.ne) hP

/-- **The seam ledger is boundary data.**  At level two, the seam-jump multiplier of an
on-seam zero is `(−1)^m`, and the parity law reads it off from the endpoint signs: for
any bank roots, the left seam ratio equals the right seam ratio exactly multiplied by
`+1` or `−1` according to the sign of the seam-edge endpoint product.  The mod-2 seam
contribution to a box ledger is computed from two point evaluations of the carrier. -/
theorem seam_jump_sign_readoff {f h GU GD G₁ G₂ : ℂ → ℂ} {τ₀ t₁ t₂ R : ℝ} {m : ℕ}
    (hR : 0 < R) (h1 : t₁ < τ₀) (h2 : τ₀ < t₂)
    (hseg : ∀ τ ∈ Set.Icc t₁ t₂, linePt τ ∈ ball (linePt τ₀) R)
    (hh : AnalyticOnNhd ℂ h (ball (linePt τ₀) R))
    (hh0 : ∀ z ∈ ball (linePt τ₀) R, h z ≠ 0)
    (hfact : ∀ z ∈ ball (linePt τ₀) R, f z = (z - linePt τ₀) ^ m * h z)
    (hreal : ∀ τ ∈ Set.Icc t₁ t₂, (f (linePt τ)).im = 0)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR (linePt τ₀) R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartL (linePt τ₀) R))
    (hpG₁ : ∀ z ∈ chartR (linePt τ₀) R, G₁ z ^ (2 : ℕ) = f z)
    (hpG₂ : ∀ z ∈ chartL (linePt τ₀) R, G₂ z ^ (2 : ℕ) = f z)
    {qP qM : ℂ} (hqP : qP ∈ overlapU (linePt τ₀) R) (hqM : qM ∈ overlapD (linePt τ₀) R)
    (hpGU : GU qP ^ (2 : ℕ) = f qP) (hpGD : GD qM ^ (2 : ℕ) = f qM) :
    (GU qP / G₂ qP) / (GD qM / G₂ qM) =
      (if 0 < seamSign f t₁ t₂ then 1 else -1) *
        ((GU qP / G₁ qP) / (GD qM / G₁ qM)) := by
  classical
  have hsj := seam_jump hR two_pos hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂ hqP hqM hpGU hpGD
  have hexp : exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / ((2 : ℕ) : ℂ)) = (-1 : ℂ) ^ m := by
    have harg : 2 * (Real.pi : ℂ) * I * (m : ℂ) / ((2 : ℕ) : ℂ) =
        (m : ℂ) * ((Real.pi : ℂ) * I) := by
      push_cast
      ring
    rw [harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [hexp] at hsj
  have hiff := seamSign_one_zero_iff_even h1 h2 hseg hh hh0 hfact hreal
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow] at hsj
    rw [if_pos (hiff.mpr he)]
    exact hsj
  · rw [ho.neg_one_pow] at hsj
    rw [if_neg (fun hpos => (Nat.not_even_iff_odd.mpr ho) (hiff.mp hpos))]
    exact hsj

end RHTower
