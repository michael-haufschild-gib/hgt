import GaloisForLFunctions.RHTower.SpeiserExactCount
import GaloisForLFunctions.RHTower.XiLaguerreShadowDensity

/-!
# Speiser's criterion, eventual form

**Theorem** (`eventually_re_eq_half_iff_eventually_deriv_ne_zero`). The following are equivalent:
- every zero of `ξ` above some height lies on the critical line;
- `ζ'` has no zero in `0 < Re s < 1/2` above some height.

**Proof.**
- (⇒) is the local Speiser theorem (`exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero`): a left
  zero of `ζ'` lies in the Speiser disk of an off-line zero at ordinate distance `< 1/2`.
- (⇐) uses the exact Speiser count (`exists_speiser_count_eq`).
  - The Speiser shadows have measure at most `2 Σ m(β − 1/2)⁺ ≤ (42/100)(V + 1/2)`
    (`volume_xiShadow_inter_Icc_le_offLineMoment`, `eventually_offLineMoment_le`).
  - So every long enough interval contains an unshadowed height
    (`exists_speiserUnshadowed_mem_Icc`).
  - A left zero of `ζ` at a large height `γ₀` then sits in a window with unshadowed edges in
    `[γ₀/4, γ₀ − 1]` and `[γ₀ + 1, 3γ₀]`, where `ζ'` must have as many zeros as `ζ`, hence at
    least one.
  - Right zeros are reflected to left zeros by `ρ ↦ 1 − ρ̄`.
-/

open Complex Set Filter MeasureTheory

namespace RHTower

noncomputable section

/-- A height outside the de Bruijn shadow set is unshadowed. -/
theorem speiserUnshadowed_of_not_mem_xiShadow {T : ℝ} (h : T ∉ DeBruijn.xiShadow) :
    SpeiserUnshadowed T := by
  intro ρ hρ
  by_contra hlt
  push Not at hlt
  apply h
  refine ⟨-I * (ρ - 1 / 2), ?_, ?_⟩
  · rw [DeBruijn.riemannHeat_zero]
    have e : (1 / 2 : ℂ) + I * (-I * (ρ - 1 / 2)) = ρ := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [e, hρ]
  · have hre : (-I * (ρ - 1 / 2)).re = ρ.im := by simp
    have him : (-I * (ρ - 1 / 2)).im = 1 / 2 - ρ.re := by simp
    rw [hre, him]
    nlinarith [hlt]

/-- **Unshadowed heights in long intervals, from an off-line moment bound.**  If
`Σ m(ρ)(Re ρ − ½) ≤ μ V` for all large `V`, there is `V₀ ≥ 0` such that every `[a, b]` with
`0 ≤ a`, `V₀ ≤ b` and `2μ(b + 1) < b − a` contains an unshadowed height. -/
theorem exists_speiserUnshadowed_mem_Icc_of_moment {μ : ℝ} (hμ : 0 ≤ μ)
    (hmom : ∀ᶠ V in atTop, offLineMoment V ≤ μ * V) :
    ∃ V₀ : ℝ, 0 ≤ V₀ ∧ ∀ a b : ℝ, 0 ≤ a → V₀ ≤ b → 2 * μ * (b + 1) < b - a →
      ∃ T ∈ Icc a b, SpeiserUnshadowed T := by
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp hmom
  refine ⟨max V₁ 0, le_max_right _ _, fun a b ha hb hlen => ?_⟩
  by_contra hno
  push Not at hno
  have hsub : Icc a b ⊆ DeBruijn.xiShadow ∩ Icc 0 b := by
    intro T hT
    refine ⟨?_, ⟨ha.trans hT.1, hT.2⟩⟩
    by_contra hT'
    exact hno T hT (speiserUnshadowed_of_not_mem_xiShadow hT')
  have hvol := (measure_mono hsub).trans (DeBruijn.volume_xiShadow_inter_Icc_le_offLineMoment b)
  rw [Real.volume_Icc] at hvol
  have hm := hV₁ (b + 1 / 2) (by linarith [le_max_left V₁ 0])
  have hb0 : 0 ≤ b := le_trans (le_max_right V₁ 0) hb
  have hμb : 0 ≤ 2 * μ * (b + 1) := by positivity
  have hle : b - a ≤ 2 * offLineMoment (b + 1 / 2) := by
    have h0 : 0 ≤ 2 * offLineMoment (b + 1 / 2) := by
      by_contra hneg
      push Not at hneg
      rw [ENNReal.ofReal_of_nonpos hneg.le] at hvol
      have := (ENNReal.ofReal_eq_zero.mp (le_antisymm hvol zero_le))
      linarith
    exact (ENNReal.ofReal_le_ofReal_iff h0).mp hvol
  nlinarith

/-- **Unshadowed heights exist in long intervals.** There is `V₀` such that every `[a, b]` with
`0 ≤ a`, `V₀ ≤ b` and `(43/100)(b + 1) < b − a` contains an unshadowed height. -/
theorem exists_speiserUnshadowed_mem_Icc :
    ∃ V₀ : ℝ, ∀ a b : ℝ, 0 ≤ a → V₀ ≤ b → 43 / 100 * (b + 1) < b - a →
      ∃ T ∈ Icc a b, SpeiserUnshadowed T := by
  obtain ⟨V₀, hV₀, h⟩ :=
    exists_speiserUnshadowed_mem_Icc_of_moment (by norm_num)
      ZetaGateProductAFE.eventually_offLineMoment_le
  refine ⟨V₀, fun a b ha hb hlen => h a b ha hb ?_⟩
  have : 0 ≤ b := hV₀.trans hb
  linarith

/-- A zero of `ζ` off the pole has multiplicity at least one. -/
theorem one_le_toNat_analyticOrderAt_riemannZeta {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hρ : riemannZeta ρ = 0) : 1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
  have hA := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hρ1
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    have hR := RHTower.Sieve.zetaResidueUnit_order_ne_top ρ
    rw [analyticOrderAt_congr (zetaResidueUnit_eventuallyEq hρ1)] at hR
    apply hR
    change analyticOrderAt ((fun s : ℂ => s - 1) * riemannZeta) ρ = ⊤
    rw [analyticOrderAt_mul (by fun_prop) hA, htop]
    simp
  have h0 : analyticOrderAt riemannZeta ρ ≠ 0 := fun h =>
    ((analyticOrderAt_eq_zero.mp h).resolve_left (not_not.mpr hA)) hρ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn, ENat.toNat_coe]
  rw [← hn] at h0
  have : n ≠ 0 := fun h => h0 (by rw [h]; rfl)
  omega

/-- **Speiser, eventual direction.** If `ζ'` has no zero in `0 < Re s < 1/2` above a height `H`,
then `ζ` has no zero there above some height. -/
theorem exists_riemannZeta_ne_zero_left_of_deriv_ne_zero {H : ℝ}
    (hS : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → H ≤ s.im → deriv riemannZeta s ≠ 0) :
    ∃ T₀ : ℝ, ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → T₀ ≤ s.im → riemannZeta s ≠ 0 := by
  obtain ⟨V₀, hV₀⟩ := exists_speiserUnshadowed_mem_Icc
  refine ⟨max (max 1000 (V₀ + 1)) (4 * H + 4), fun s h0 h1 hT hζ => ?_⟩
  set γ := s.im with hγ
  have hγ1000 : 1000 ≤ γ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hγV : V₀ + 1 ≤ γ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hγH : 4 * H + 4 ≤ γ := le_trans (le_max_right _ _) hT
  obtain ⟨T₁, hT₁, hu₁⟩ := hV₀ (γ / 4) (γ - 1) (by linarith) (by linarith) (by linarith)
  obtain ⟨T₂, hT₂, hu₂⟩ := hV₀ (γ + 1) (3 * γ) (by linarith) (by linarith) (by linarith)
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, hsum⟩ := exists_speiser_count_eq (T₁ := T₁) (T₂ := T₂)
    (by linarith [hT₁.1]) (by linarith [hT₁.2, hT₂.1]) hu₁ hu₂
  have hZ₁e : Z₁ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
    obtain ⟨hwin, hd⟩ := (hZ₁ w).mp hw
    exact hS w hwin.1 hwin.2.1 (by linarith [hwin.2.2.1, hT₁.1]) hd
  have hsmem : s ∈ Z₀ := (hZ₀ s).mpr
    ⟨⟨h0, h1, by linarith [hT₁.2], by linarith [hT₂.1]⟩, hζ⟩
  have hs1 : s ≠ 1 := fun h => by
    have : s.im = 0 := by rw [h, Complex.one_im]
    linarith
  have hge : 1 ≤ ∑ w ∈ Z₀, (analyticOrderAt riemannZeta w).toNat :=
    le_trans (one_le_toNat_analyticOrderAt_riemannZeta hs1 hζ)
      (Finset.single_le_sum (f := fun w => (analyticOrderAt riemannZeta w).toNat)
        (fun w _ => Nat.zero_le _) hsmem)
  rw [← hsum, hZ₁e, Finset.sum_empty] at hge
  exact absurd hge (by norm_num)

/-- **Speiser's criterion, eventual form.** Eventual RH is equivalent to the absence of zeros of
`ζ'` in `0 < Re s < 1/2` above some height. -/
theorem eventually_re_eq_half_iff_eventually_deriv_ne_zero :
    (∃ T₀ : ℝ, ∀ ρ : ℂ, xi ρ = 0 → T₀ ≤ ρ.im → ρ.re = 1 / 2) ↔
      (∃ T₀ : ℝ, ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → T₀ ≤ s.im → deriv riemannZeta s ≠ 0) := by
  constructor
  · rintro ⟨T₀, hRH⟩
    refine ⟨max 100 (T₀ + 1), fun s h0 h1 hT hd => ?_⟩
    obtain ⟨ρ, hρ, -, -, hdisk⟩ := exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero h0 h1
      (le_trans (le_max_left _ _) hT) hd
    have hq : (s.im - ρ.im) ^ 2 < 1 := by
      have hstrip : (ρ.re - 1 / 2) ^ 2 < 1 / 4 := by
        by_contra hge
        push Not at hge
        have : ρ.re ≥ 1 ∨ ρ.re ≤ 0 := by
          by_contra hc
          push Not at hc
          nlinarith
        rcases this with h | h
        · exact xi_ne_zero_of_one_le_re h hρ
        · apply xi_ne_zero_of_one_le_re (ρ := 1 - ρ) (by simp; linarith)
          rw [xi_one_sub]; exact hρ
      nlinarith [sq_nonneg (s.re - 1 / 2)]
    have hγ : T₀ ≤ ρ.im := by
      have : |s.im - ρ.im| < 1 := by
        rw [← sq_lt_one_iff_abs_lt_one]; exact hq
      have := (abs_lt.mp this).2
      linarith [le_trans (le_max_right 100 (T₀ + 1)) hT]
    rw [hRH ρ hρ hγ, sub_self, zero_pow two_ne_zero] at hdisk
    have : s.re - 1 / 2 ≠ 0 := by linarith
    have := pow_pos (abs_pos.mpr this) 2
    rw [sq_abs] at this
    nlinarith [sq_nonneg (s.im - ρ.im)]
  · rintro ⟨T₀, hS⟩
    obtain ⟨T₁, hT₁⟩ := exists_riemannZeta_ne_zero_left_of_deriv_ne_zero hS
    refine ⟨T₁, fun ρ hρ hT => ?_⟩
    have hlt1 : ρ.re < 1 := by
      by_contra h; push Not at h; exact xi_ne_zero_of_one_le_re h hρ
    have hgt0 : 0 < ρ.re := by
      by_contra h
      push Not at h
      apply xi_ne_zero_of_one_le_re (ρ := 1 - ρ) (by simp; linarith)
      rw [xi_one_sub]; exact hρ
    have hleft : ∀ w : ℂ, xi w = 0 → 0 < w.re → w.re < 1 / 2 → T₁ ≤ w.im → False := by
      intro w hw h0 h1 hwT
      have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; norm_num at h1
      exact hT₁ w h0 h1 hwT ((xi_eq_zero_iff h0 hw1).mp hw)
    rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
    · exact (hleft ρ hρ hgt0 h hT).elim
    · exact h
    · exfalso
      refine hleft (1 - (starRingEnd ℂ) ρ) ?_ (by simp; linarith) (by simp; linarith)
        (by simpa using hT)
      rw [xi_one_sub, xi_conj, hρ, map_zero]

end

end RHTower
