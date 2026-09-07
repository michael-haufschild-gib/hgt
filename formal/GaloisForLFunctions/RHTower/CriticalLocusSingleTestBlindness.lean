import GaloisForLFunctions.RHTower.CriticalLocusConeFullness

/-!
# Finite evaluation blindness for a single spectral test

For one admissible test `F` (holomorphic on the strip `|Re s − 1/2| < θ`, symmetric under
`s ↦ 1 − s` and `s ↦ s̄`, decaying in the substrip, with nonzero line restriction) and any
configuration whose support ordinates are unbounded, an off-line quadruple of displacement `t*`
can be placed so that its test value is cancelled exactly by a single further move: the deletion
of one support pair, the insertion of one line pair, or the insertion of a second quadruple at the
same displacement.  Hence one spectral test never separates the configuration from a configuration
with an off-line quadruple at displacement `t*`.

The proof combines the cone fullness of the configuration moves (a strictly negative move exists
in every direction) with the intermediate value theorem along the decaying quadruple value
`γ ↦ 4 Re F(1/2 + t* + iγ)`.
-/

namespace RHTower

noncomputable section

open Complex Set Filter Topology

/-! ## Intermediate values of decaying continuous functions -/

/-- A continuous function tending to `0` at `+∞` attains every value strictly between `0` and a
value it takes. -/
theorem exists_eq_of_tendsto_zero_of_pos {h : ℝ → ℝ} (hc : Continuous h)
    (hlim : Tendsto h atTop (𝓝 0)) {a c : ℝ} (hc0 : 0 < c) (hca : c < h a) :
    ∃ x : ℝ, h x = c := by
  have hev : ∀ᶠ x in atTop, h x < c := hlim.eventually (eventually_lt_nhds hc0)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
  set b : ℝ := max T a with hb
  have hab : a ≤ b := le_max_right _ _
  have hhb : h b < c := hT b (le_max_left _ _)
  have := intermediate_value_Icc' hab hc.continuousOn ⟨hhb.le, hca.le⟩
  obtain ⟨x, _, hx⟩ := this
  exact ⟨x, hx⟩

theorem exists_eq_of_tendsto_zero_of_neg {h : ℝ → ℝ} (hc : Continuous h)
    (hlim : Tendsto h atTop (𝓝 0)) {a c : ℝ} (hc0 : c < 0) (hca : h a < c) :
    ∃ x : ℝ, h x = c := by
  have hlim' : Tendsto (fun x => -h x) atTop (𝓝 0) := by simpa using hlim.neg
  obtain ⟨x, hx⟩ := exists_eq_of_tendsto_zero_of_pos hc.neg hlim' (a := a) (c := -c)
    (by linarith) (by simp; linarith)
  have hx' : -h x = -c := hx
  exact ⟨x, by linarith⟩

/-! ## The quadruple value along a horizontal line -/

/-- The quadruple value `γ ↦ 4 Re F(1/2 + t + iγ)`. -/
def quadValue (F : ℂ → ℂ) (t : ℝ) (γ : ℝ) : ℝ := 4 * (F (1 / 2 + (t : ℂ) + (γ : ℂ) * I)).re

/-- The pair value `β ↦ 2 Re F(1/2 + iβ)`. -/
def pairValue (F : ℂ → ℂ) (β : ℝ) : ℝ := 2 * (F (1 / 2 + (β : ℂ) * I)).re

theorem continuous_quadValue (F : ℂ → ℂ) {θ t : ℝ} (ht : |t| < θ)
    (hhol : DifferentiableOn ℂ F (criticalStrip θ)) : Continuous (quadValue F t) := by
  have hcont : ContinuousOn F (criticalStrip θ) := hhol.continuousOn
  have hmem : ∀ γ : ℝ, (1 / 2 + (t : ℂ) + (γ : ℂ) * I) ∈ criticalStrip θ := by
    intro γ; simp [criticalStrip, ht]
  have h1 : Continuous fun γ : ℝ => F (1 / 2 + (t : ℂ) + (γ : ℂ) * I) := by
    have hpath : Continuous fun γ : ℝ => (1 / 2 + (t : ℂ) + (γ : ℂ) * I) := by fun_prop
    exact (hcont.comp_continuous hpath hmem)
  unfold quadValue
  exact continuous_const.mul (Complex.continuous_re.comp h1)

theorem continuous_pairValue (F : ℂ → ℂ) {θ : ℝ} (hθ : 0 < θ)
    (hhol : DifferentiableOn ℂ F (criticalStrip θ)) : Continuous (pairValue F) := by
  have := continuous_quadValue F (t := 0) (by simpa using hθ) hhol
  unfold quadValue at this
  unfold pairValue
  have e : (fun β : ℝ => 2 * (F (1 / 2 + (β : ℂ) * I)).re)
      = fun β : ℝ => (1 / 2 : ℝ) * (4 * (F (1 / 2 + ((0 : ℝ) : ℂ) + (β : ℂ) * I)).re) := by
    funext β; simp; ring
  rw [e]
  exact continuous_const.mul this

theorem tendsto_quadValue_atTop (F : ℂ → ℂ) {tstar t : ℝ} (ht : |t| ≤ tstar)
    (hdecay : ∀ ε > 0, ∃ T : ℝ, ∀ s : ℂ, |s.re - 1 / 2| ≤ tstar → T ≤ |s.im| → ‖F s‖ ≤ ε) :
    Tendsto (quadValue F t) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨T, hT⟩ := hdecay (ε / 8) (by positivity)
  refine Filter.eventually_atTop.mpr ⟨|T| + 1, fun γ hγ => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hs : ‖F (1 / 2 + (t : ℂ) + (γ : ℂ) * I)‖ ≤ ε / 8 := by
    apply hT
    · simp; exact ht
    · simp; linarith [le_abs_self T, le_abs_self γ]
  unfold quadValue
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have := (Complex.abs_re_le_norm _).trans hs
  linarith

/-! ## Blindness of a single test -/

/-- **A single spectral test is blind to an off-line quadruple.**  For an admissible test with
nonzero line restriction and a configuration with unbounded support ordinates, some placement of
the quadruple at displacement `t*` has its value cancelled by one deletion, one pair insertion,
or one further quadruple at the same displacement (or the value already vanishes). -/
theorem singleTest_blindness (F : ℂ → ℂ) {θ tstar : ℝ} (htpos : 0 < tstar) (hθ : tstar < θ)
    (hhol : DifferentiableOn ℂ F (criticalStrip θ))
    (hκ : ∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s))
    (hσ : ∀ s, F (1 - s) = F s)
    (hdecay : ∀ ε > 0, ∃ T : ℝ, ∀ s : ℂ, |s.re - 1 / 2| ≤ tstar → T ≤ |s.im| → ‖F s‖ ≤ ε)
    (hne : ∃ τ : ℝ, (F (1 / 2 + (τ : ℂ) * I)).re ≠ 0)
    {S : Set ℝ} (hS : ∀ X : ℝ, ∃ α ∈ S, X ≤ |α|) :
    ∃ γ₀ : ℝ,
      quadValue F tstar γ₀ = 0 ∨
      (∃ α ∈ S, quadValue F tstar γ₀ - pairValue F α = 0) ∨
      (∃ β : ℝ, quadValue F tstar γ₀ + pairValue F β = 0) ∨
      (∃ γ : ℝ, quadValue F tstar γ₀ + quadValue F tstar γ = 0) := by
  classical
  have hθpos : 0 < θ := by linarith
  have hqc : Continuous (quadValue F tstar) :=
    continuous_quadValue F (by rw [abs_of_pos htpos]; exact hθ) hhol
  have hpc : Continuous (pairValue F) := continuous_pairValue F hθpos hhol
  have hqlim : Tendsto (quadValue F tstar) atTop (𝓝 0) :=
    tendsto_quadValue_atTop F (by rw [abs_of_pos htpos]) hdecay
  have hplim : Tendsto (pairValue F) atTop (𝓝 0) := by
    have := tendsto_quadValue_atTop F (t := 0) (by simp; exact htpos.le) hdecay
    unfold quadValue at this
    unfold pairValue
    have e : (fun β : ℝ => 2 * (F (1 / 2 + (β : ℂ) * I)).re)
        = fun β : ℝ => (1 / 2 : ℝ) * (4 * (F (1 / 2 + ((0 : ℝ) : ℂ) + (β : ℂ) * I)).re) := by
      funext β; simp; ring
    rw [e]
    simpa using this.const_mul (1 / 2 : ℝ)
  -- the cone-fullness input for the one-test family
  have hcone : ∀ (w : ℝ), w ≠ 0 → ∀ α : ℝ,
      (∃ β : ℝ, w * pairValue F β < 0) ∨ (w * (-pairValue F α) < 0) ∨
      (∃ γ : ℝ, w * quadValue F tstar γ < 0) := by
    intro w hw α
    have hindep : ∀ v : Fin 1 → ℝ,
        (∀ τ : ℝ, ∑ i, v i * ((fun _ : Fin 1 => F) i (1 / 2 + (τ : ℂ) * I)).re = 0) → v = 0 := by
      intro v hv
      obtain ⟨τ, hτ⟩ := hne
      have := hv τ
      rw [Fin.sum_univ_one] at this
      have hv0 : v 0 = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hτ
      funext i
      rw [Fin.eq_zero i]
      exact hv0
    have := criticalLocus_move_cone_fullness (fun _ : Fin 1 => F) htpos hθ (fun _ => hhol)
      (fun _ => hκ) (fun _ => hσ) (fun _ => hdecay) hindep α (fun _ => w)
      (by intro h; apply hw; have := congrFun h 0; simpa using this)
    simp only [Fin.sum_univ_one] at this
    unfold pairValue quadValue
    rcases this with ⟨β, hβ⟩ | h | ⟨γ, hγ⟩
    · left; exact ⟨β, by linarith⟩
    · right; left; linarith
    · right; right; exact ⟨γ, by linarith⟩
  -- pair values are small far out
  have hpsmall : ∀ ε > 0, ∃ T : ℝ, ∀ β : ℝ, T ≤ |β| → |pairValue F β| < ε := by
    intro ε hε
    obtain ⟨T, hT⟩ := hdecay (ε / 4) (by positivity)
    refine ⟨T, fun β hβ => ?_⟩
    have hs : ‖F (1 / 2 + (β : ℂ) * I)‖ ≤ ε / 4 := by
      apply hT
      · simp; exact htpos.le
      · simp; exact hβ
    unfold pairValue
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := (Complex.abs_re_le_norm _).trans hs
    linarith
  -- case split on the sign of the quadruple value
  by_cases hq0 : ∀ γ, quadValue F tstar γ = 0
  · exact ⟨0, Or.inl (hq0 0)⟩
  push Not at hq0
  obtain ⟨γ₁, hγ₁⟩ := hq0
  set q₁ := quadValue F tstar γ₁ with hq₁
  -- a support ordinate with pair value smaller than `|q₁|`
  obtain ⟨T, hT⟩ := hpsmall |q₁| (abs_pos.mpr hγ₁)
  obtain ⟨α, hαS, hαT⟩ := hS T
  have hpα : |pairValue F α| < |q₁| := hT α hαT
  rcases lt_or_gt_of_ne hγ₁ with hneg | hpos
  · -- `q₁ < 0`: use the direction `w = −1`
    have hq₁abs : |q₁| = -q₁ := abs_of_neg hneg
    rcases hcone (-1) (by norm_num) α with ⟨β, hβ⟩ | h | ⟨γ, hγ⟩
    · -- a pair with positive value: shrink it and cancel
      have hpβ : 0 < pairValue F β := by linarith
      set m : ℝ := min (pairValue F β) (-q₁) / 2 with hm
      have hmpos : 0 < m := by rw [hm]; exact half_pos (lt_min hpβ (by linarith))
      have hm1 : m < pairValue F β := by
        rw [hm]; have := min_le_left (pairValue F β) (-q₁); linarith
      have hm2 : m < -q₁ := by
        rw [hm]; have := min_le_right (pairValue F β) (-q₁); linarith
      obtain ⟨β', hβ'⟩ := exists_eq_of_tendsto_zero_of_pos hpc hplim hmpos hm1
      obtain ⟨γ₀, hγ₀⟩ := exists_eq_of_tendsto_zero_of_neg hqc hqlim (a := γ₁) (c := -m)
        (by linarith) (by linarith)
      exact ⟨γ₀, Or.inr (Or.inr (Or.inl ⟨β', by linarith⟩))⟩
    · -- the support pair at `α` has negative pair value, small: delete it
      have hpα' : pairValue F α < 0 := by linarith
      have hlt : q₁ < pairValue F α := by
        have := (abs_lt.mp hpα).1
        linarith
      obtain ⟨γ₀, hγ₀⟩ := exists_eq_of_tendsto_zero_of_neg hqc hqlim (a := γ₁) (c := pairValue F α)
        hpα' hlt
      exact ⟨γ₀, Or.inr (Or.inl ⟨α, hαS, by linarith⟩)⟩
    · -- a quadruple with positive value: shrink both and cancel
      have hqγ : 0 < quadValue F tstar γ := by linarith
      set m : ℝ := min (quadValue F tstar γ) (-q₁) / 2 with hm
      have hmpos : 0 < m := by rw [hm]; exact half_pos (lt_min hqγ (by linarith))
      have hm1 : m < quadValue F tstar γ := by
        rw [hm]; have := min_le_left (quadValue F tstar γ) (-q₁); linarith
      have hm2 : m < -q₁ := by
        rw [hm]; have := min_le_right (quadValue F tstar γ) (-q₁); linarith
      obtain ⟨γ', hγ'⟩ := exists_eq_of_tendsto_zero_of_pos hqc hqlim hmpos hm1
      obtain ⟨γ₀, hγ₀⟩ := exists_eq_of_tendsto_zero_of_neg hqc hqlim (a := γ₁) (c := -m)
        (by linarith) (by linarith)
      exact ⟨γ₀, Or.inr (Or.inr (Or.inr ⟨γ', by linarith⟩))⟩
  · -- `q₁ > 0`: use the direction `w = 1`
    have hq₁abs : |q₁| = q₁ := abs_of_pos hpos
    rcases hcone 1 one_ne_zero α with ⟨β, hβ⟩ | h | ⟨γ, hγ⟩
    · have hpβ : pairValue F β < 0 := by linarith
      set m : ℝ := min (-pairValue F β) q₁ / 2 with hm
      have hmpos : 0 < m := by rw [hm]; exact half_pos (lt_min (by linarith) hpos)
      have hm1 : -m > pairValue F β := by
        rw [hm]; have := min_le_left (-pairValue F β) q₁; linarith
      have hm2 : m < q₁ := by
        rw [hm]; have := min_le_right (-pairValue F β) q₁; linarith
      obtain ⟨β', hβ'⟩ := exists_eq_of_tendsto_zero_of_neg hpc hplim (a := β) (c := -m)
        (by linarith) hm1
      obtain ⟨γ₀, hγ₀⟩ := exists_eq_of_tendsto_zero_of_pos hqc hqlim (a := γ₁) (c := m) hmpos hm2
      exact ⟨γ₀, Or.inr (Or.inr (Or.inl ⟨β', by linarith⟩))⟩
    · have hpα' : 0 < pairValue F α := by linarith
      have hlt : pairValue F α < q₁ := by
        have := (abs_lt.mp hpα).2
        linarith
      obtain ⟨γ₀, hγ₀⟩ := exists_eq_of_tendsto_zero_of_pos hqc hqlim (a := γ₁) (c := pairValue F α)
        hpα' hlt
      exact ⟨γ₀, Or.inr (Or.inl ⟨α, hαS, by linarith⟩)⟩
    · have hqγ : quadValue F tstar γ < 0 := by linarith
      set m : ℝ := min (-quadValue F tstar γ) q₁ / 2 with hm
      have hmpos : 0 < m := by rw [hm]; exact half_pos (lt_min (by linarith) hpos)
      have hm1 : quadValue F tstar γ < -m := by
        rw [hm]; have := min_le_left (-quadValue F tstar γ) q₁; linarith
      have hm2 : m < q₁ := by
        rw [hm]; have := min_le_right (-quadValue F tstar γ) q₁; linarith
      obtain ⟨γ', hγ'⟩ := exists_eq_of_tendsto_zero_of_neg hqc hqlim (a := γ) (c := -m)
        (by linarith) hm1
      obtain ⟨γ₀, hγ₀⟩ := exists_eq_of_tendsto_zero_of_pos hqc hqlim (a := γ₁) (c := m) hmpos hm2
      exact ⟨γ₀, Or.inr (Or.inr (Or.inr ⟨γ', by linarith⟩))⟩

end

end RHTower
