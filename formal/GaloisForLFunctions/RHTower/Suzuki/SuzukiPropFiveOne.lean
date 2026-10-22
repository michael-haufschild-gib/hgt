import GaloisForLFunctions.RHTower.Suzuki.SuzukiV0WeilForm

noncomputable section

/-!
# Suzuki's Proposition 5.1: an unconditional criterion on `V(0)`

The space `V(0) = L²(0,∞) ∩ K L²(0,∞)` is constructed without assuming RH, so it can carry an
equivalent form of the Riemann hypothesis.  Suzuki's Proposition 5.1 states that RH holds if and
only if

1. `‖ψ‖² = π ⟨ψ,ψ⟩_W` for every `ψ ∈ V(0)` (the source's `2⁻¹` becomes `π` because the corpus's
   Fourier transform is unitary), and
2. for every `γ ∈ Γ` and every `ε > 0` there is `ψ ∈ V(0)` with `ψ̂(γ) = 1` and
   `|ψ̂(γ')| ≤ ε |γ - γ'|^{-1-δ}` at every other zero `γ'` of `A`.

The source leaves `δ > 0` unspecified and only uses `Σ_γ m_γ |γ|^{-1-δ} < ∞`; here `δ = 1/2`, the
value the corpus owns through `xiSpectralPoint_inv_three_halves_summable`.

The forward direction is `SuzukiV0WeilForm`: the mass identity is the Makarov--Poltoratski isometry,
and the peaked vectors are the orthonormal family `F_γ`, which vanishes *exactly* at the other
spectral points.  The converse is the source's contradiction argument: if a nonreal `γ₀ ∈ Γ`
existed, the two-peak test vector `ψ = i ψ_{γ₀} - i ψ_{conj γ₀}` would have
`⟨ψ,ψ⟩_W = -1 + O(ε) < 0`, contradicting (1).  The tail of the spectral sum is controlled by the
recentred three-halves weight, which `SuzukiV0WeilForm` proves summable.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

set_option maxHeartbeats 400000

theorem re_peak_term_le {δ : ℝ} {x y : ℂ} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ δ) :
    ((I - I * x) * (starRingEnd ℂ) (I * y - I)).re ≤ -1 + 2 * δ + δ ^ (2 : ℕ) := by
  have hexp : (I - I * x) * (starRingEnd ℂ) (I * y - I)
      = -((1 - x) * (1 - (starRingEnd ℂ) y)) := by
    simp only [map_sub, map_mul, Complex.conj_I]
    linear_combination ((1 - x) * (1 - (starRingEnd ℂ) y)) * Complex.I_sq
  rw [hexp]
  have hxre : |x.re| ≤ δ := le_trans (Complex.abs_re_le_norm x) hx
  have hyre : |((starRingEnd ℂ) y).re| ≤ δ := by
    rw [Complex.conj_re]
    exact le_trans (Complex.abs_re_le_norm y) hy
  have hprod : |(x * (starRingEnd ℂ) y).re| ≤ δ ^ (2 : ℕ) := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    rw [norm_mul, RCLike.norm_conj]
    have hn1 := norm_nonneg x
    have hn2 := norm_nonneg y
    nlinarith
  have hre : ((1 - x) * (1 - (starRingEnd ℂ) y)).re
      = 1 - ((starRingEnd ℂ) y).re - x.re + (x * (starRingEnd ℂ) y).re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  rw [Complex.neg_re, hre]
  cases' abs_le.mp hxre with h1 h2
  cases' abs_le.mp hyre with h3 h4
  cases' abs_le.mp hprod with h5 h6
  linarith

theorem peak_term_swap (u v : ℂ) :
    (I * v - I) * (starRingEnd ℂ) (I - I * u) = (I - I * v) * (starRingEnd ℂ) (I * u - I) := by
  simp only [map_sub, map_mul, Complex.conj_I]
  ring

/-- Suzuki Proposition 5.1, condition (1). -/
def SuzukiV0MassCondition : Prop :=
  ∀ ψ ∈ suzukiV0, ((‖ψ‖ ^ (2 : ℕ) : ℝ) : ℂ) = (Real.pi : ℂ) * suzukiV0WeilForm ψ ψ

/-- Suzuki Proposition 5.1, condition (2), with the source's `δ` taken to be `1/2`. -/
def SuzukiV0PeakCondition : Prop :=
  ∀ γ : ℂ, XiC γ = 0 → ∀ ε : ℝ, 0 < ε → ∃ ψ ∈ suzukiV0,
    suzukiV0Eval ψ γ = 1 ∧
      ∀ w : ℂ, XiC w = 0 → w ≠ γ →
        ‖suzukiV0Eval ψ w‖ ≤ ε / (‖γ - w‖ * Real.sqrt ‖γ - w‖)

theorem suzukiV0MassCondition_of_rh (hRH : RiemannHypothesis) : SuzukiV0MassCondition :=
  fun _ hψ => norm_sq_eq_pi_mul_suzukiV0WeilForm hRH hψ

theorem suzukiV0PeakCondition_of_rh (hRH : RiemannHypothesis) : SuzukiV0PeakCondition :=
  fun _ hγ _ hε => exists_peaked_suzukiV0 hRH hγ hε

/-- **Suzuki Proposition 5.1, converse.**  Conditions (1) and (2) force the Riemann hypothesis. -/
theorem riemannHypothesis_of_suzukiV0_conditions
    (h1 : SuzukiV0MassCondition) (h2 : SuzukiV0PeakCondition) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_XiC_zero_im_eq_zero]
  by_contra hcon
  push Not at hcon
  obtain ⟨g0, hg0, him⟩ := hcon
  set c : ℂ := (starRingEnd ℂ) g0 with hcdef
  have hc : XiC c = 0 := XiC_conj_eq_zero_of_XiC_zero hg0
  have hcg : (starRingEnd ℂ) c = g0 := by rw [hcdef, Complex.conj_conj]
  have hcne : c ≠ g0 := by
    intro h
    refine him ?_
    have h' : (starRingEnd ℂ) g0 = g0 := by rw [← hcdef, h]
    have h'' := congrArg Complex.im h'
    simp only [Complex.conj_im] at h''
    linarith
  have hdpos : 0 < ‖g0 - c‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact fun h => hcne h.symm
  -- the recentred three-halves weights
  set U : XiZeroCopy → ℝ := fun q =>
    1 / (‖g0 - xiSpectralPoint q‖ * Real.sqrt ‖g0 - xiSpectralPoint q‖) with hUdef
  set V : XiZeroCopy → ℝ := fun q =>
    1 / (‖c - xiSpectralPoint q‖ * Real.sqrt ‖c - xiSpectralPoint q‖) with hVdef
  have hUnn : ∀ q, 0 ≤ U q := fun q => div_nonneg zero_le_one (by positivity)
  have hVnn : ∀ q, 0 ≤ V q := fun q => div_nonneg zero_le_one (by positivity)
  have hUs : Summable U := summable_xiSpectralPoint_shift_three_halves g0
  have hVs : Summable V := summable_xiSpectralPoint_shift_three_halves c
  have hW : Summable (fun q => (U q + V q) ^ (2 : ℕ)) :=
    summable_sq_of_summable_nonneg (fun q => by linarith [hUnn q, hVnn q]) (hUs.add hVs)
  set K : ℝ := ∑' q : XiZeroCopy, (U q + V q) ^ (2 : ℕ) with hKdef
  have hK0 : 0 ≤ K := tsum_nonneg fun q => sq_nonneg _
  set L : ℝ := 1 / (‖g0 - c‖ * Real.sqrt ‖g0 - c‖) with hLdef
  have hL0 : 0 < L := by
    have : 0 < Real.sqrt ‖g0 - c‖ := Real.sqrt_pos.mpr hdpos
    rw [hLdef]; positivity
  set M : ℝ := L + L ^ (2 : ℕ) + K + 1 with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; nlinarith [sq_nonneg L]
  have hM0 : (0:ℝ) < M := by linarith
  set ε : ℝ := min 1 (1 / (8 * M)) with hepsdef
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεM : ε ≤ 1 / (8 * M) := min_le_right _ _
  set δ : ℝ := ε * L with hδdef
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδ8 : δ ≤ 1 / 8 := by
    have hstep : ε * L ≤ (1 / (8 * M)) * L := by nlinarith [hL0.le]
    have hstep2 : (1 / (8 * M)) * L ≤ 1 / 8 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith [hMdef, sq_nonneg L, hK0]
    rw [hδdef]; linarith
  have hεK : ε ^ (2 : ℕ) * K ≤ 1 / 8 := by
    have hsq : ε ^ (2 : ℕ) ≤ ε := by nlinarith
    have hstep : ε ^ (2 : ℕ) * K ≤ ε * K := by nlinarith
    have hstep2 : ε * K ≤ (1 / (8 * M)) * K := by nlinarith
    have hstep3 : (1 / (8 * M)) * K ≤ 1 / 8 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      nlinarith [hMdef, sq_nonneg L, hL0.le]
    linarith
  -- the two peaked test vectors
  obtain ⟨ψ₁, hψ₁, he₁, hb₁⟩ := h2 g0 hg0 ε hε0
  obtain ⟨ψ₂, hψ₂, he₂, hb₂⟩ := h2 c hc ε hε0
  set ψ : Lp ℂ 2 (volume : Measure ℝ) := I • ψ₁ - I • ψ₂ with hψdef
  have hψ : ψ ∈ suzukiV0 :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hψ₁) (Submodule.smul_mem _ _ hψ₂)
  have hev : ∀ w : ℂ, suzukiV0Eval ψ w
      = I * suzukiV0Eval ψ₁ w - I * suzukiV0Eval ψ₂ w := by
    intro w
    rw [hψdef, suzukiV0Eval_sub, suzukiV0Eval_smul, suzukiV0Eval_smul]
  have hu : ‖suzukiV0Eval ψ₂ g0‖ ≤ δ := by
    have hb := hb₂ g0 hg0 (fun h => hcne h.symm)
    rw [norm_sub_rev c g0] at hb
    rw [hδdef, hLdef, mul_one_div]
    exact hb
  have hv : ‖suzukiV0Eval ψ₁ c‖ ≤ δ := by
    have hb := hb₁ c hc hcne
    rw [hδdef, hLdef, mul_one_div]
    exact hb
  have hg0ev : suzukiV0Eval ψ g0 = I - I * suzukiV0Eval ψ₂ g0 := by
    rw [hev, he₁, mul_one]
  have hcev : suzukiV0Eval ψ c = I * suzukiV0Eval ψ₁ c - I := by
    rw [hev, he₂, mul_one]
  set t : XiZeroCopy → ℂ := fun q => suzukiV0Eval ψ (xiSpectralPoint q)
      * (starRingEnd ℂ) (suzukiV0Eval ψ ((starRingEnd ℂ) (xiSpectralPoint q))) with htdef
  have hspecial : ∀ q : XiZeroCopy, xiSpectralPoint q = g0 ∨ xiSpectralPoint q = c →
      (t q).re ≤ -1 + 2 * δ + δ ^ (2 : ℕ) := by
    intro q hq
    rcases hq with h | h
    · rw [htdef]
      simp only
      rw [h, ← hcdef, hg0ev, hcev]
      exact re_peak_term_le hu hv
    · rw [htdef]
      simp only
      rw [h, hcg, hg0ev, hcev, peak_term_swap]
      exact re_peak_term_le hv hu
  have hfar : ∀ q : XiZeroCopy, xiSpectralPoint q ≠ g0 → xiSpectralPoint q ≠ c →
      ‖t q‖ ≤ ε ^ (2 : ℕ) * (U q + V q) ^ (2 : ℕ) := by
    intro q hq1 hq2
    have hz : XiC (xiSpectralPoint q) = 0 := XiC_xiSpectralPoint_eq_zero q
    have hzc : XiC ((starRingEnd ℂ) (xiSpectralPoint q)) = 0 := XiC_conj_eq_zero_of_XiC_zero hz
    have hcq1 : (starRingEnd ℂ) (xiSpectralPoint q) ≠ g0 := by
      intro h
      refine hq2 ?_
      rw [hcdef, ← h, Complex.conj_conj]
    have hcq2 : (starRingEnd ℂ) (xiSpectralPoint q) ≠ c := by
      intro h
      refine hq1 ?_
      rw [← hcg, ← h, Complex.conj_conj]
    have hUeq : ‖g0 - (starRingEnd ℂ) (xiSpectralPoint q)‖ = ‖c - xiSpectralPoint q‖ := by
      rw [hcdef, ← Complex.norm_conj, map_sub]
      simp only [Complex.conj_conj]
    have hVeq : ‖c - (starRingEnd ℂ) (xiSpectralPoint q)‖ = ‖g0 - xiSpectralPoint q‖ := by
      rw [hcdef, ← Complex.norm_conj, map_sub]
      simp only [Complex.conj_conj]
    have hA : ‖suzukiV0Eval ψ (xiSpectralPoint q)‖ ≤ ε * (U q + V q) := by
      rw [hev]
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
      have b1 := hb₁ _ hz hq1
      have b2 := hb₂ _ hz hq2
      rw [hUdef, hVdef]
      simp only
      rw [mul_add, ← div_eq_mul_one_div, ← div_eq_mul_one_div]
      linarith
    have hB : ‖suzukiV0Eval ψ ((starRingEnd ℂ) (xiSpectralPoint q))‖ ≤ ε * (U q + V q) := by
      rw [hev]
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
      have b1 := hb₁ _ hzc hcq1
      have b2 := hb₂ _ hzc hcq2
      rw [hUeq] at b1
      rw [hVeq] at b2
      rw [hUdef, hVdef]
      simp only
      rw [mul_add, ← div_eq_mul_one_div, ← div_eq_mul_one_div]
      linarith
    have hnn : 0 ≤ ε * (U q + V q) := by
      have := hUnn q; have := hVnn q; positivity
    rw [htdef]
    simp only
    rw [norm_mul, RCLike.norm_conj]
    calc ‖suzukiV0Eval ψ (xiSpectralPoint q)‖
          * ‖suzukiV0Eval ψ ((starRingEnd ℂ) (xiSpectralPoint q))‖
        ≤ (ε * (U q + V q)) * (ε * (U q + V q)) := by
          exact mul_le_mul hA hB (norm_nonneg _) hnn
      _ = ε ^ (2 : ℕ) * (U q + V q) ^ (2 : ℕ) := by ring
  -- the two peaked zeros form a finite set of copies
  have hSp : {q : XiZeroCopy | xiSpectralPoint q = g0 ∨ xiSpectralPoint q = c}.Finite := by
    refine Set.Finite.subset (finite_xiSpectralPoint_norm_le ‖g0‖) ?_
    rintro q (h | h)
    · show ‖xiSpectralPoint q‖ ≤ ‖g0‖
      rw [h]
    · show ‖xiSpectralPoint q‖ ≤ ‖g0‖
      rw [h, hcdef, Complex.norm_conj]
  have hts : Summable t := by
    rw [← hSp.summable_compl_iff]
    refine Summable.of_norm_bounded
      ((hW.mul_left (ε ^ (2 : ℕ))).subtype
        {q : XiZeroCopy | xiSpectralPoint q = g0 ∨ xiSpectralPoint q = c}ᶜ) ?_
    rintro ⟨q, hq⟩
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or] at hq
    exact hfar q hq.1 hq.2
  have hrs : Summable (fun q => (t q).re) := Complex.reCLM.summable hts
  obtain ⟨ρ₀, hρ₀⟩ := exists_xiSpectralPointSupport_eq hg0
  have hmpos : 0 < xiSupportMult ρ₀ := xiSupportMult_pos ρ₀
  set q₀ : XiZeroCopy := ⟨ρ₀, ⟨0, hmpos⟩⟩ with hq₀def
  have hq₀ : xiSpectralPoint q₀ = g0 := by
    rw [xiSpectralPoint_eq_support]
    exact hρ₀
  have hsmall : -1 + 2 * δ + δ ^ (2 : ℕ) ≤ 0 := by nlinarith
  have hbound : ∀ q, (t q).re ≤ ε ^ (2 : ℕ) * (U q + V q) ^ (2 : ℕ) := by
    intro q
    by_cases hq : xiSpectralPoint q = g0 ∨ xiSpectralPoint q = c
    · have hsp := hspecial q hq
      have hnn : 0 ≤ ε ^ (2 : ℕ) * (U q + V q) ^ (2 : ℕ) := by positivity
      linarith
    · push Not at hq
      exact le_trans (Complex.re_le_norm _) (hfar q hq.1 hq.2)
  set K0 : ℝ := (-1 + 2 * δ + δ ^ (2 : ℕ)) - ε ^ (2 : ℕ) * (U q₀ + V q₀) ^ (2 : ℕ) with hK0def
  set B : XiZeroCopy → ℝ :=
    fun q => ε ^ (2 : ℕ) * (U q + V q) ^ (2 : ℕ) + (if q = q₀ then K0 else 0) with hBdef
  have hBsum : Summable B := (hW.mul_left (ε ^ (2 : ℕ))).add (hasSum_ite_eq q₀ K0).summable
  have hBval : ∑' q, B q = ε ^ (2 : ℕ) * K + K0 := by
    rw [hBdef, Summable.tsum_add (hW.mul_left (ε ^ (2 : ℕ))) (hasSum_ite_eq q₀ K0).summable,
      tsum_ite_eq, Summable.tsum_mul_left]
    exact hW
  have hle : ∑' q, (t q).re ≤ ε ^ (2 : ℕ) * K + K0 := by
    rw [← hBval]
    refine Summable.tsum_le_tsum (fun q => ?_) hrs hBsum
    rw [hBdef]
    simp only
    by_cases hq : q = q₀
    · rw [if_pos hq, hK0def, hq]
      have hsp := hspecial q₀ (Or.inl hq₀)
      linarith
    · rw [if_neg hq, add_zero]
      exact hbound q
  have hneg : ε ^ (2 : ℕ) * K + K0 < 0 := by
    rw [hK0def]
    have hnn : 0 ≤ ε ^ (2 : ℕ) * (U q₀ + V q₀) ^ (2 : ℕ) := by positivity
    nlinarith
  have hmass := h1 ψ hψ
  have hWre : (suzukiV0WeilForm ψ ψ).re = ∑' q, (t q).re := by
    rw [suzukiV0WeilForm]
    exact Complex.re_tsum hts
  have hre : ‖ψ‖ ^ (2 : ℕ) = Real.pi * (suzukiV0WeilForm ψ ψ).re := by
    have hc2 := congrArg Complex.re hmass
    rw [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at hc2
    exact hc2
  have hSle : ∑' q, (t q).re < 0 := lt_of_le_of_lt hle hneg
  have hlt : Real.pi * (∑' q, (t q).re) < 0 := mul_neg_of_pos_of_neg Real.pi_pos hSle
  rw [hWre] at hre
  linarith [sq_nonneg ‖ψ‖, hre, hlt]

/-- **Suzuki, Proposition 5.1.**  The Riemann hypothesis is equivalent to the conjunction of the
mass identity and the peaked-test-vector property on `V(0)`. -/
theorem suzuki_prop_5_1 :
    RiemannHypothesis ↔ (SuzukiV0MassCondition ∧ SuzukiV0PeakCondition) :=
  ⟨fun hRH => ⟨suzukiV0MassCondition_of_rh hRH, suzukiV0PeakCondition_of_rh hRH⟩,
    fun h => riemannHypothesis_of_suzukiV0_conditions h.1 h.2⟩

end RHTower
