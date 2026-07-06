/-
The Dirichlet-side synthesis: forced band-edge events on a lateral edge, with the phase
budgets supplied rather than hypothesized.

The incidence pencil is anchored at a finite Euler head `Λ₁ = eulerHeadAnchor P` and targets
the completed carrier `Λ₂ = completedGN N = archFactor · gN`.  Its phase rate along a vertical
edge is `Re(logDeriv Λ₂ − logDeriv Λ₁)`, and

  `logDeriv Λ₂ = logDeriv archFactor + logDeriv gN`,

so the rate splits into three parts:

* the archimedean part `Re(logDeriv archFactor) = stripWindingRate`, bounded below by the
  explicit off-line winding floor `stripFloor σ a ≈ ½ log(a/2π)` (grows with the height);
* the Dirichlet part `Re(logDeriv gN)`, bounded in modulus by a constant `B_D` on a zero-free
  edge (the polar engine's budget `C_D`);
* the anchor part `Re(logDeriv Λ₁)`, bounded in modulus by the prime sum `eulerHeadBound P σ`
  (the finite-prime budget `C₁`).

Both Dirichlet-side budgets are height-independent, so on a sufficiently high edge the
archimedean floor overwhelms their sum and the net phase rate is a positive constant
`ρ₀ = stripFloor σ a − eulerHeadBound P σ − B_D`.  The rate floor then supplies a strictly
ordered family of forced band-edge events whose count grows with the edge length: the events
are supplied, and only the pairing on them remains as the band-edge arithmetic input.
-/
import GaloisForLFunctions.RHTower.IncidenceEdgeCount
import GaloisForLFunctions.RHTower.AnchorHead
import GaloisForLFunctions.RHTower.BandEdgePairing

open Complex

namespace RHTower

/-! ### The archimedean logarithmic derivative on the edge -/

/-- On the critical strip the completed archimedean envelope's logarithmic derivative along a
vertical edge is the strip winding datum, so its real part is the off-line winding rate. -/
theorem logDeriv_archFactor_stripPt {σ τ : ℝ} (hσ : 0 < σ) :
    logDeriv archFactor (stripPt σ τ) = stripWinding σ τ := by
  have hre : 0 < (stripPt σ τ).re := by rw [stripPt_re]; exact hσ
  rw [logDeriv_apply, (hasDerivAt_archFactor_of_re_pos hre).deriv, stripWinding]

theorem re_logDeriv_archFactor_stripPt {σ τ : ℝ} (hσ : 0 < σ) :
    (logDeriv archFactor (stripPt σ τ)).re = stripWindingRate σ τ := by
  rw [logDeriv_archFactor_stripPt hσ, stripWindingRate]

/-! ### Analyticity and nonvanishing of the anchor and target -/

/-- The completed archimedean envelope is analytic on the open right half plane. -/
theorem archFactor_analyticOnNhd_re_pos :
    AnalyticOnNhd ℂ archFactor {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
  exact (hasDerivAt_archFactor_of_re_pos hz).differentiableAt.differentiableWithinAt

/-- The concrete carrier is analytic on the open left half of the plane where `Re z < 1`. -/
theorem gN_analyticOnNhd_re_lt_one (N : ℕ) :
    AnalyticOnNhd ℂ (gN N) {z : ℂ | z.re < 1} := by
  intro z hz
  apply gN_analyticAt
  apply Gammaℝ_ne_zero_of_re_pos
  simp only [Complex.sub_re, Complex.one_re]
  have : z.re < 1 := hz
  linarith

/-- On the open critical strip the completed carrier is analytic. -/
theorem completedGN_analyticOnNhd_strip (N : ℕ) :
    AnalyticOnNhd ℂ (completedGN N) {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  have hsub1 : {z : ℂ | 0 < z.re ∧ z.re < 1} ⊆ {z : ℂ | 0 < z.re} := fun z hz => hz.1
  have hsub2 : {z : ℂ | 0 < z.re ∧ z.re < 1} ⊆ {z : ℂ | z.re < 1} := fun z hz => hz.2
  have ha := archFactor_analyticOnNhd_re_pos.mono hsub1
  have hg := (gN_analyticOnNhd_re_lt_one N).mono hsub2
  exact ha.mul hg

/-- The completed archimedean factor is nonvanishing on the open critical strip. -/
theorem archFactor_ne_zero_strip {z : ℂ} (hz : 0 < z.re ∧ z.re < 1) : archFactor z ≠ 0 := by
  refine archFactor_ne_zero ?_ ?_ (Gammaℝ_ne_zero_of_re_pos hz.1)
  · intro h; rw [h, Complex.zero_re] at hz; exact absurd hz.1 (lt_irrefl 0)
  · intro h; rw [h, Complex.one_re] at hz; exact absurd hz.2 (lt_irrefl 1)

/-! ### The incidence phase-rate floor for the completed pencil -/

/-- **The three-part phase-rate floor.**  Along a vertical edge in the strip, the incidence
phase rate of the pencil `(eulerHeadAnchor P, completedGN N)` is bounded below by the
archimedean winding floor `stripFloor σ a` net of the anchor's prime-sum budget
`eulerHeadBound P σ` and the Dirichlet budget `B_D` — provided the carrier `gN` is nonvanishing
along the edge with logarithmic derivative bounded by `B_D`. -/
theorem incidence_rate_floor_completedGN {P : Finset ℕ} {N : ℕ} {σ a b B_D : ℝ}
    (hP : ∀ p ∈ P, 2 ≤ p) (hσ : 0 < σ) (hσ1 : σ < 1) (ha : 0 < a)
    (hgne : ∀ τ ∈ Set.Icc a b, gN N (stripPt σ τ) ≠ 0)
    (hBD : ∀ τ ∈ Set.Icc a b, |(logDeriv (gN N) (stripPt σ τ)).re| ≤ B_D) :
    ∀ τ ∈ Set.Icc a b,
      stripFloor σ a - eulerHeadBound P σ - B_D
        ≤ (logDeriv (completedGN N) (stripPt σ τ)
            - logDeriv (eulerHeadAnchor P) (stripPt σ τ)).re := by
  intro τ hτ
  have hre : 0 < (stripPt σ τ).re := by rw [stripPt_re]; exact hσ
  have hre1 : (stripPt σ τ).re < 1 := by rw [stripPt_re]; exact hσ1
  have haF : archFactor (stripPt σ τ) ≠ 0 := archFactor_ne_zero_strip ⟨hre, hre1⟩
  have hgN : gN N (stripPt σ τ) ≠ 0 := hgne τ hτ
  have hdA : DifferentiableAt ℂ archFactor (stripPt σ τ) :=
    (hasDerivAt_archFactor_of_re_pos hre).differentiableAt
  have hdg : DifferentiableAt ℂ (gN N) (stripPt σ τ) :=
    (gN_analyticAt (Gammaℝ_ne_zero_of_re_pos
      (by simp only [Complex.sub_re, Complex.one_re]; linarith))).differentiableAt
  -- product decomposition of the target's logarithmic derivative
  have hsplit : logDeriv (completedGN N) (stripPt σ τ)
      = logDeriv archFactor (stripPt σ τ) + logDeriv (gN N) (stripPt σ τ) := by
    have : completedGN N = fun s => archFactor s * gN N s := rfl
    rw [this, logDeriv_mul _ haF hgN hdA hdg]
  rw [hsplit, Complex.sub_re, Complex.add_re, re_logDeriv_archFactor_stripPt hσ]
  -- assemble the three bounds
  have harch : stripFloor σ a ≤ stripWindingRate σ τ :=
    le_trans (stripFloor_mono_height hσ1.le ha hτ.1)
      (stripWindingRate_ge hσ hσ1.le (lt_of_lt_of_le ha hτ.1))
  have hgbd : -B_D ≤ (logDeriv (gN N) (stripPt σ τ)).re :=
    neg_le_of_abs_le (hBD τ hτ)
  have hanc : (logDeriv (eulerHeadAnchor P) (stripPt σ τ)).re ≤ eulerHeadBound P σ :=
    le_trans (le_abs_self _) (abs_re_logDeriv_eulerHeadAnchor_le hP hσ τ)
  linarith

/-! ### The forced-event count -/

/-- **Forced band-edge events on a lateral edge of the completed pencil.**  With the anchor a
finite Euler head, the carrier `gN` nonvanishing along a strip edge at height `a > 0` with a
Dirichlet log-derivative budget `B_D`, and the net winding rate
`ρ₀ = stripFloor σ a − eulerHeadBound P σ − B_D` positive, there are `n` strictly ordered points
on any edge long enough to advance the phase by `n·π` where a real-ratio member of the pencil
`(eulerHeadAnchor P, completedGN N)` vanishes.  The count grows with the edge length; the phase
budgets are computed, not assumed. -/
theorem exists_edge_events_completedGN {P : Finset ℕ} {N : ℕ} {σ a b ρ₀ B_D : ℝ} {n : ℕ}
    {U : Set ℂ}
    (hP : ∀ p ∈ P, 2 ≤ p) (hσ : 0 < σ) (hσ1 : σ < 1) (ha : 0 < a) (hab : a ≤ b)
    (hU : IsOpen U) (hUstrip : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hgneU : ∀ z ∈ U, gN N z ≠ 0)
    (hgne : ∀ τ ∈ Set.Icc a b, gN N (stripPt σ τ) ≠ 0)
    (hBD : ∀ τ ∈ Set.Icc a b, |(logDeriv (gN N) (stripPt σ τ)).re| ≤ B_D)
    (hρ : 0 < ρ₀) (hρle : ρ₀ ≤ stripFloor σ a - eulerHeadBound P σ - B_D)
    (hn : (n : ℝ) * Real.pi ≤ (b - a) * ρ₀) :
    ∃ e : Fin n → ℝ, StrictMono e ∧ ∀ i, e i ∈ Set.Icc a b ∧
      pencil (eulerHeadAnchor P) (completedGN N)
        ((incidence (eulerHeadAnchor P) (completedGN N) (stripPt σ (e i))).re : ℂ) 1
        (stripPt σ (e i)) = 0 := by
  have hΛ1an : AnalyticOnNhd ℂ (eulerHeadAnchor P) U :=
    DifferentiableOn.analyticOnNhd
      (fun z _ => (differentiable_eulerHeadAnchor hP z).differentiableWithinAt) hU
  have hΛ1ne : ∀ z ∈ U, eulerHeadAnchor P z ≠ 0 :=
    fun z hz => eulerHeadAnchor_ne_zero hP (hUstrip hz).1
  have hΛ2an : AnalyticOnNhd ℂ (completedGN N) U :=
    (completedGN_analyticOnNhd_strip N).mono hUstrip
  have hΛ2ne : ∀ z ∈ U, completedGN N z ≠ 0 := by
    intro z hz
    have : completedGN N z = archFactor z * gN N z := rfl
    rw [this]
    exact mul_ne_zero (archFactor_ne_zero_strip (hUstrip hz)) (hgneU z hz)
  have hfloor : ∀ τ ∈ Set.Icc a b,
      ρ₀ ≤ (logDeriv (completedGN N) (stripPt σ τ)
          - logDeriv (eulerHeadAnchor P) (stripPt σ τ)).re := by
    intro τ hτ
    exact le_trans hρle (incidence_rate_floor_completedGN hP hσ hσ1 ha hgne hBD τ hτ)
  exact exists_edge_events_of_incidence_rate_floor hab hρ hU hmapU hΛ1an hΛ1ne hΛ2an hΛ2ne
    hfloor hn

/-! ### The unconditional height threshold -/

/-- **The archimedean floor eventually beats every Dirichlet budget.**  Because the off-line
winding floor `stripFloor σ a` grows without bound in the height while the anchor prime sum and
the Dirichlet budget are fixed, for any target net rate `ρ₀` there is a height above which the
net rate exceeds `ρ₀`.  This is the subcriticality of the two Dirichlet budgets against the
archimedean floor made explicit: `C₁ + C_D` grows slower than the archimedean phase. -/
theorem exists_height_net_rate_ge {P : Finset ℕ} {σ B_D ρ₀ : ℝ} (hσ0 : 0 ≤ σ) :
    ∃ A : ℝ, 0 < A ∧ ∀ a, A ≤ a → ρ₀ ≤ stripFloor σ a - eulerHeadBound P σ - B_D := by
  -- `stripFloor σ a ≥ (log(a/2π) − (4/a² + π/a))/2 − (1−σ)/a²`; pick `a` with the log large
  set C : ℝ := eulerHeadBound P σ + B_D + ρ₀ with hC
  -- choose a height where the pure log term already exceeds `C + 2` and the corrections are `≤ 1`
  obtain ⟨A₀, hA₀⟩ := (Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const (by positivity :
        (0 : ℝ) < 2 * Real.pi))).eventually_ge_atTop (2 * C + 4)))
  refine ⟨max A₀ 12, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun a ha => ?_⟩
  have ha12 : (12 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have haA₀ : A₀ ≤ a := le_trans (le_max_left _ _) ha
  have hapos : 0 < a := by linarith
  have hlog : 2 * C + 4 ≤ Real.log (a / (2 * Real.pi)) := hA₀ a haA₀
  -- the correction terms are small at height ≥ 12
  have hcorr1 : 4 / a ^ 2 ≤ 4 / 144 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have hcorrπ : Real.pi / a ≤ Real.pi / 12 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) ha12
  have h1s' : 1 - σ ≤ 1 := by linarith [hσ0]
  have hcorrσ : (1 - σ) / a ^ 2 ≤ 1 / 144 :=
    div_le_div₀ (by norm_num) h1s' (by norm_num) (by nlinarith)
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  unfold stripFloor
  have hbound : (4 / a ^ 2 + Real.pi / a) ≤ 4 / 144 + 3.15 / 12 := by
    nlinarith [hπ, hcorrπ, hcorr1]
  linarith [hlog, hbound, hcorrσ, hC]

end RHTower
