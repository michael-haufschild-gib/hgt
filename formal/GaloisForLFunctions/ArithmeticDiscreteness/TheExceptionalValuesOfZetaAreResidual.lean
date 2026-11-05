import GaloisForLFunctions.ArithmeticDiscreteness.AlmostEveryValueRepelsAtPolynomialScale
import GaloisForLFunctions.HTGeometry.DivisorPairing
import GaloisForLFunctions.RHTower.ZetaVoroninUniversalityOnCompactSets

/-!
# The exceptional values of ζ are residual

Call `a ∈ ℂ` exceptional if `ζ` has distinct `a`-points `s ≠ s'` with `1/2 < Re s < 1` at
arbitrarily large heights and `|s' − s| < e^{−|Im s|}`; then polynomial collide-or-repel fails for
the `a`-points. The exceptional values form a dense `G_δ` set of measure zero
(`exceptional_values_of_riemannZeta`): almost every value repels at polynomial scale
(`ae_riemannZeta_values_collide_or_repel`), a residual set of values does not. B54 asks that the
single value `0` be non-exceptional, a Diophantine-type property of one point, as for Liouville
numbers.

Mechanism.
* **Openness** (`isOpen_exceptionalSet`): the open mapping theorem moves both `a`-points.
* **Density** (`exists_mem_exceptionalSet_near`): Voronin universality
  (`RHTower.exists_pos_density_zetaTargetReturnSet_of_isCompact`) gives a large `τ` with
  `ζ(z + iτ) ≈ a₀ + μ(z − 3/4)²` near `3/4`; Rouché for the derivative
  (`HTGeometry.exists_local_zeroSet`) gives a critical point `c`; with `v = ζ(c + iτ)` the function
  `ζ(· + iτ) − v` has a zero of order `≥ 2` at `c`, and for small `w ≠ 0` its `w`-points near `c`
  are simple, hence at least two, as close as desired. The height is chosen before the distance.
-/

open Complex Metric Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

open HTGeometry

/-- Values with two distinct `a`-points in `1/2 < Re s < 1`, above height `n + 1`, at distance
`< e^{−|Im s|}`. -/
def exceptionalSet (n : ℕ) : Set ℂ :=
  {a | ∃ s s' : ℂ, riemannZeta s = a ∧ riemannZeta s' = a ∧ s ≠ s' ∧ 1 / 2 < s.re ∧ s.re < 1 ∧
    (n : ℝ) + 1 < |s.im| ∧ ‖s' - s‖ < Real.exp (-|s.im|)}

/-! ### Multiplicities -/

/-- A zero with nonzero derivative has multiplicity one. -/
theorem zeroMult_eq_one_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (han : AnalyticAt ℂ f z)
    (hz : f z = 0) (hd : deriv f z ≠ 0) : zeroMult f z = 1 := by
  have hord : analyticOrderAt f z = (1 : ℕ) := by
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han]
    refine ⟨fun k hk => ?_, ?_⟩
    · have : k = 0 := by omega
      subst this
      simpa using hz
    · simpa using hd
  unfold zeroMult
  rw [hord]
  rfl

/-- A zero with vanishing derivative of a function not vanishing near it has multiplicity `≥ 2`. -/
theorem two_le_zeroMult_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (han : AnalyticAt ℂ f z)
    (hne : ¬ ∀ᶠ w in 𝓝 z, f w = 0) (hz : f z = 0) (hd : deriv f z = 0) : 2 ≤ zeroMult f z := by
  have htop : analyticOrderAt f z ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  have hord : analyticOrderAt f z = (zeroMult f z : ℕ) := by
    rw [zeroMult, ENat.coe_toNat htop]
  have hnz := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp hord).2
  by_contra h
  interval_cases hm : zeroMult f z
  · exact hnz (by rw [iteratedDeriv_zero]; exact hz)
  · exact hnz (by rw [iteratedDeriv_one]; exact hd)

/-! ### `ζ` is not locally constant -/

theorem differentiableOn_riemannZeta_compl : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
  fun _ hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  differentiableOn_riemannZeta_compl.analyticAt (isOpen_compl_singleton.mem_nhds hs)

/-- **`ζ` takes no value on a neighbourhood** (identity theorem on `ℂ ∖ {1}`, and
`ζ(0) = −1/2 ≠ π²/6 = ζ(2)`). -/
theorem riemannZeta_not_eventually_eq {p : ℂ} (hp : p ≠ 1) (v : ℂ) :
    ¬ ∀ᶠ z in 𝓝 p, riemannZeta z = v := by
  intro h
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      _).isPreconnected
  have heq := (differentiableOn_riemannZeta_compl.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (g := fun _ => v) analyticOnNhd_const hconn hp h
  have h0 : riemannZeta 0 = v := heq (by norm_num : (0 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ))
  have h2 : riemannZeta 2 = v := heq (by norm_num : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ))
  rw [riemannZeta_zero] at h0
  rw [riemannZeta_two, ← h0] at h2
  have hpi : (0 : ℝ) < Real.pi ^ 2 / 6 := by positivity
  have hr : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by push_cast; exact h2
  have := Complex.ofReal_injective hr
  linarith

/-- The open mapping theorem for `ζ`. -/
theorem image_ball_mem_nhds_riemannZeta {s : ℂ} (hs : s ≠ 1) {ρ : ℝ} (hρ : 0 < ρ) :
    riemannZeta '' ball s ρ ∈ 𝓝 (riemannZeta s) := by
  rcases (analyticAt_riemannZeta hs).eventually_constant_or_nhds_le_map_nhds with h | h
  · exact absurd h (riemannZeta_not_eventually_eq hs _)
  · exact le_map_iff.mp h _ (ball_mem_nhds s hρ)

/-! ### Openness -/

theorem isOpen_exceptionalSet (n : ℕ) : IsOpen (exceptionalSet n) := by
  refine isOpen_iff_mem_nhds.mpr fun a ⟨s, s', hs, hs', hne, hre0, hre1, him, hd⟩ => ?_
  have hd0 : 0 < ‖s' - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE1 : Real.exp (-|s.im|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg s.im])
  have hs1 : s ≠ 1 := by
    intro h; rw [h, one_im, abs_zero] at him; linarith
  have hs'1 : s' ≠ 1 := by
    intro h
    have := (abs_im_le_norm (s' - s)).trans hd.le
    rw [h, sub_im, one_im, zero_sub, abs_neg] at this
    linarith
  -- a radius keeping every condition strict
  set G : ℝ := Real.exp (-|s.im|) - ‖s' - s‖ with hG
  have hG0 : 0 < G := by rw [hG]; linarith
  set ρ : ℝ := min (min ((s.re - 1 / 2) / 2) ((1 - s.re) / 2))
    (min ((|s.im| - (n + 1)) / 2) (min (G / 4) (‖s' - s‖ / 4))) with hρ
  have hρ0 : 0 < ρ := by
    rw [hρ]
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (lt_min (by linarith)
      (by linarith)))
  have hρ1 : ρ ≤ (s.re - 1 / 2) / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ (1 - s.re) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ (|s.im| - (n + 1)) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ G / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ5 : ρ ≤ ‖s' - s‖ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _))
  have h1 := image_ball_mem_nhds_riemannZeta hs1 hρ0
  have h2 := image_ball_mem_nhds_riemannZeta hs'1 hρ0
  rw [hs] at h1
  rw [hs'] at h2
  refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
  rintro b ⟨⟨u, hu, hub⟩, ⟨u', hu', hub'⟩⟩
  rw [mem_ball, dist_eq_norm] at hu hu'
  have hre := (abs_re_le_norm (u - s)).trans hu.le
  have hi := (abs_im_le_norm (u - s)).trans hu.le
  rw [sub_re] at hre
  rw [sub_im] at hi
  have hi1 := abs_sub_abs_le_abs_sub u.im s.im
  have hi2 := abs_sub_abs_le_abs_sub s.im u.im
  rw [abs_sub_comm] at hi2
  have hdist : ‖u' - u‖ ≤ ‖s' - s‖ + 2 * ρ := by
    have : u' - u = (u' - s') + (s' - s) - (u - s) := by ring
    rw [this]
    have t1 := norm_sub_le ((u' - s') + (s' - s)) (u - s)
    have t2 := norm_add_le (u' - s') (s' - s)
    linarith
  refine ⟨u, u', hub, hub', fun huu => ?_, by linarith [(abs_le.mp hre).1],
    by linarith [(abs_le.mp hre).2], by linarith, ?_⟩
  · -- the two discs are disjoint
    have : ‖s' - s‖ ≤ ‖u' - s'‖ + ‖u - s‖ := by
      have e : s' - s = (u - s) - (u' - s') := by rw [huu]; ring
      rw [e]
      have := norm_sub_le (u - s) (u' - s')
      linarith
    linarith
  · -- `|u' − u| < e^{−|Im s|} − ρ ≤ e^{−|Im s| − ρ} ≤ e^{−|Im u|}`
    have hexp : Real.exp (-|s.im|) - ρ ≤ Real.exp (-|u.im|) := by
      have e1 : Real.exp (-|s.im|) * (1 - ρ) ≤ Real.exp (-|s.im|) * Real.exp (-ρ) :=
        mul_le_mul_of_nonneg_left (Real.one_sub_le_exp_neg ρ) (Real.exp_pos _).le
      have e2 : Real.exp (-|s.im|) * Real.exp (-ρ) ≤ Real.exp (-|u.im|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have e3 : Real.exp (-|s.im|) - ρ ≤ Real.exp (-|s.im|) * (1 - ρ) := by
        nlinarith [Real.exp_pos (-|s.im|)]
      linarith
    linarith

/-! ### Density -/

/-- A set of positive lower density is unbounded. -/
theorem exists_ge_of_pos_density {S : Set ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ T in atTop, ENNReal.ofReal (c * T) ≤ volume (S ∩ Icc 0 T)) (N : ℝ) :
    ∃ τ ∈ S, N ≤ τ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT, hTN⟩ := (h.and (eventually_ge_atTop ((|N| + 1) / c))).exists
  have hsub : S ∩ Icc 0 T ⊆ Icc 0 |N| := fun τ ⟨hτS, hτ0, _⟩ =>
    ⟨hτ0, ((hcon τ hτS).le.trans (le_abs_self N))⟩
  have h1 := hT.trans (measure_mono hsub)
  rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_le_ofReal_iff (abs_nonneg N)] at h1
  rw [div_le_iff₀ hc] at hTN
  linarith

/-- **Cauchy estimate for a difference.** -/
theorem norm_deriv_sub_deriv_le {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) {z₀ : ℂ} {r ρ η : ℝ}
    (hρ : 0 < ρ) (hsub : closedBall z₀ (r + ρ) ⊆ U)
    (hη : ∀ z ∈ closedBall z₀ (r + ρ), ‖f z - g z‖ ≤ η) {z : ℂ} (hz : z ∈ closedBall z₀ r) :
    ‖deriv f z - deriv g z‖ ≤ η / ρ := by
  have hball : closedBall z ρ ⊆ closedBall z₀ (r + ρ) :=
    closedBall_subset_closedBall' (by rw [mem_closedBall] at hz; linarith)
  have hzU : U ∈ 𝓝 z := hU.mem_nhds (hsub (hball (mem_closedBall_self hρ.le)))
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
    ((hf.sub hg).diffContOnCl_ball (hball.trans hsub))
    (fun w hw => hη w (hball (sphere_subset_closedBall hw)))
  rwa [deriv_sub (hf.differentiableAt hzU) (hg.differentiableAt hzU)] at hd

/-- A punctured neighbourhood free of zeros, as a ball. -/
theorem exists_ball_ne_zero {f : ℂ → ℂ} {c : ℂ} (han : AnalyticAt ℂ f c)
    (hne : ¬ ∀ᶠ w in 𝓝 c, f w = 0) : ∃ ρ > 0, ∀ w ∈ ball c ρ, w ≠ c → f w ≠ 0 := by
  have h := han.eventually_eq_zero_or_eventually_ne_zero.resolve_left hne
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h
  obtain ⟨ρ, hρ, hball⟩ := h
  exact ⟨ρ, hρ, fun w hw hwc => hball w hw hwc⟩

/-- **Exceptional values near every nonzero value.** -/
theorem exists_mem_exceptionalSet_near (n : ℕ) {a₀ : ℂ} (ha₀ : a₀ ≠ 0) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ a ∈ exceptionalSet n, ‖a - a₀‖ < r₀ := by
  set z₀ : ℂ := ((3 / 4 : ℝ) : ℂ) with hz₀
  set U : Set ℂ := ball z₀ (1 / 16) with hU
  set K : Set ℂ := closedBall z₀ (1 / 32) with hK
  have hUo : IsOpen U := isOpen_ball
  set m : ℝ := min ‖a₀‖ r₀ with hm
  have ha₀n : 0 < ‖a₀‖ := norm_pos_iff.mpr ha₀
  have hm0 : 0 < m := lt_min ha₀n hr₀
  set g : ℂ → ℂ := fun z => a₀ + (m : ℂ) * (z - z₀) ^ 2 with hg
  set G1 : ℂ → ℂ := fun z => 2 * (m : ℂ) * (z - z₀) with hG1
  have hm0' : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hgdiff : Differentiable ℂ g := by rw [hg]; fun_prop
  have hG1diff : Differentiable ℂ G1 := by rw [hG1]; fun_prop
  have hderiv_g : ∀ z, deriv g z = G1 z := by
    intro z
    have h := ((((hasDerivAt_id z).sub_const z₀).pow 2).const_mul (m : ℂ)).const_add a₀
    rw [h.deriv, hG1]
    simp only [id, Nat.cast_ofNat]
    ring
  -- the simple zero of `g'` at `z₀` and its Rouché radius
  have hG1z₀ : G1 z₀ = 0 := by simp [hG1]
  have hG1only : ∀ w ∈ closedBall z₀ (2 * (1 / 128)), G1 w = 0 → w = z₀ := by
    intro w _ hw
    simp only [hG1, mul_eq_zero, two_ne_zero, hm0', false_or, sub_eq_zero] at hw
    exact hw
  have hsubU : closedBall z₀ (2 * (1 / 128)) ⊆ U :=
    closedBall_subset_ball (by norm_num)
  obtain ⟨ε₁, hε₁, hrouche⟩ := exists_local_zeroSet hUo hG1diff.differentiableOn
    (by norm_num : (0 : ℝ) < 1 / 128) hsubU hG1z₀ hG1only
  have hG1mult : zeroMult G1 z₀ = 1 := by
    refine zeroMult_eq_one_of_analyticAt (hG1diff.analyticAt z₀) hG1z₀ ?_
    have h := (((hasDerivAt_id z₀).sub_const z₀).const_mul (2 * (m : ℂ)))
    rw [show G1 = fun z => 2 * (m : ℂ) * (id z - z₀) from rfl, h.deriv]
    simpa using hm0'
  -- the universality target
  set η : ℝ := min (ε₁ / 64) (r₀ / 4) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hg0 : ∀ z ∈ ball z₀ (1 / 16), g z ≠ 0 := by
    intro z hz hgz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖(m : ℂ) * (z - z₀) ^ 2‖ < ‖a₀‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
      have hz2 : ‖z - z₀‖ ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz.le 2
      have : m ≤ ‖a₀‖ := min_le_left _ _
      nlinarith
    have : a₀ = -((m : ℂ) * (z - z₀) ^ 2) := by rw [hg] at hgz; linear_combination hgz
    rw [this, norm_neg] at h1
    exact lt_irrefl _ h1
  have hKstrip : ∀ s ∈ K, 1 / 2 < s.re ∧ s.re < 1 := by
    intro s hs
    rw [hK, mem_closedBall, dist_eq_norm] at hs
    have := (abs_re_le_norm (s - z₀)).trans hs
    rw [sub_re, hz₀, ofReal_re] at this
    exact ⟨by linarith [(abs_le.mp this).1], by linarith [(abs_le.mp this).2]⟩
  obtain ⟨cd, hcd, hdens⟩ := RHTower.exists_pos_density_zetaTargetReturnSet_of_isCompact
    (isCompact_closedBall z₀ (1 / 32)) hKstrip (closedBall_subset_ball (by norm_num))
    (fun z _ => hgdiff.analyticAt z) hg0 hη0
  obtain ⟨τ, hτS, hτN⟩ := exists_ge_of_pos_density hcd hdens ((n : ℝ) + 2)
  have hτ : ∀ z ∈ K, ‖riemannZeta (z + τ * I) - g z‖ < η := hτS
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the shifted zeta function
  set f : ℂ → ℂ := fun z => riemannZeta (z + τ * I) with hf
  have hUim : ∀ z ∈ U, |z.im| < 1 / 16 := by
    intro z hz
    rw [hU, mem_ball, dist_eq_norm] at hz
    have := (abs_im_le_norm (z - z₀)).trans_lt hz
    rwa [sub_im, hz₀, ofReal_im, sub_zero] at this
  have hfU : DifferentiableOn ℂ f U := by
    intro z hz
    have hne : z + τ * I ≠ 1 := by
      intro h1
      have := congrArg Complex.im h1
      simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, zero_add,
        one_im] at this
      have := hUim z hz
      rw [abs_lt] at this
      linarith
    exact ((differentiableAt_riemannZeta hne).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  -- a critical point `c` of `f` near `z₀` (Rouché for `f'` against `g'`)
  have hK1 : closedBall z₀ (1 / 64 + 1 / 64) ⊆ U := closedBall_subset_ball (by norm_num)
  have hfg : ∀ z ∈ closedBall z₀ (1 / 64 + 1 / 64), ‖f z - g z‖ ≤ η := fun z hz =>
    (hτ z (by rw [hK]; convert hz using 2; norm_num)).le
  obtain ⟨Za, hZa_ball, hZa_iff, hZa_sum⟩ := hrouche (deriv f) (hfU.deriv hUo) (by
    intro z hz
    have hz' : z ∈ closedBall z₀ (1 / 64) := by convert hz using 2; norm_num
    have h := norm_deriv_sub_deriv_le hUo hfU hgdiff.differentiableOn (by norm_num) hK1 hfg hz'
    rw [hderiv_g] at h
    calc ‖deriv f z - G1 z‖ ≤ η / (1 / 64) := h
      _ ≤ ε₁ := by rw [hη]; have := min_le_left (ε₁ / 64) (r₀ / 4); linarith)
  rw [hG1mult] at hZa_sum
  obtain ⟨c, hcZ, hcm⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hZa_sum]; norm_num)
  have hc_ball := hZa_ball c hcZ
  have hcU : U ∈ 𝓝 c := hUo.mem_nhds (ball_subset_ball (by norm_num) hc_ball)
  have hfc : deriv f c = 0 := (hZa_iff c hc_ball).mpr hcZ
  have hf'ne : ¬ ∀ᶠ w in 𝓝 c, deriv f w = 0 := fun h =>
    hcm (by rw [zeroMult, analyticOrderAt_eq_top.mpr h]; rfl)
  have hanf : AnalyticAt ℂ f c := hfU.analyticAt hcU
  have hanf' : AnalyticAt ℂ (deriv f) c := (hfU.deriv hUo).analyticAt hcU
  obtain ⟨ρ₁, hρ₁, hcrit⟩ := exists_ball_ne_zero hanf' hf'ne
  -- the critical value `v` and the double zero of `f − v` at `c`
  set v : ℂ := f c with hv
  set F₀ : ℂ → ℂ := fun z => f z - v with hF₀
  have hF₀ne : ¬ ∀ᶠ w in 𝓝 c, F₀ w = 0 := by
    intro h
    have hev : f =ᶠ[𝓝 c] fun _ => v := h.mono fun w hw => sub_eq_zero.mp hw
    exact hf'ne (hev.deriv.mono fun w hw => by rw [hw, deriv_const])
  have hanF₀ : AnalyticAt ℂ F₀ c := hanf.sub analyticAt_const
  obtain ⟨ρ₂, hρ₂, hiso⟩ := exists_ball_ne_zero hanF₀ hF₀ne
  set δ' : ℝ := min (min (ρ₁ / 2) (ρ₂ / 4)) (min (1 / 64) (Real.exp (-(τ + 2)) / 2)) with hδ'
  have hδ'0 : 0 < δ' := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by norm_num) (by positivity))
  have hδ'1 : δ' ≤ ρ₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ'2 : δ' ≤ ρ₂ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ'3 : δ' ≤ 1 / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'4 : δ' ≤ Real.exp (-(τ + 2)) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hcz₀ : ‖c - z₀‖ < 1 / 128 := by rw [← dist_eq_norm]; exact hc_ball
  have hsub' : closedBall c (2 * δ') ⊆ U := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [hU, mem_ball, dist_eq_norm]
    calc ‖w - z₀‖ = ‖(w - c) + (c - z₀)‖ := by ring_nf
      _ ≤ ‖w - c‖ + ‖c - z₀‖ := norm_add_le _ _
      _ < 1 / 16 := by linarith
  have hF₀c : F₀ c = 0 := sub_self _
  have hF₀only : ∀ w ∈ closedBall c (2 * δ'), F₀ w = 0 → w = c := by
    intro w hw hw0
    by_contra hwc
    refine hiso w ?_ hwc hw0
    rw [mem_closedBall] at hw
    rw [mem_ball]; linarith
  obtain ⟨ε₂, hε₂, hrouche₂⟩ := exists_local_zeroSet hUo (hfU.sub_const v) hδ'0 hsub' hF₀c hF₀only
  set w₀ : ℝ := min ε₂ (r₀ / 4) with hw₀
  have hw₀0 : 0 < w₀ := lt_min hε₂ (by positivity)
  set h : ℂ → ℂ := fun z => F₀ z - w₀ with hh
  obtain ⟨Za', hZa'_ball, hZa'_iff, hZa'_sum⟩ := hrouche₂ h ((hfU.sub_const v).sub_const _) (by
    intro z _
    rw [hh, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hw₀0]
    exact min_le_left _ _)
  -- the `w₀`-points near `c` are simple, hence at least two
  have hF₀2 : 2 ≤ zeroMult F₀ c := by
    refine two_le_zeroMult_of_analyticAt hanF₀ hF₀ne hF₀c ?_
    rw [hF₀, deriv_sub_const, hfc]
  have hderiv_h : ∀ z, deriv h z = deriv f z := fun z => by
    rw [hh, deriv_sub_const, hF₀, deriv_sub_const]
  have hsimple : ∀ ρ ∈ Za', zeroMult h ρ = 1 := by
    intro ρ hρ
    have hρb := hZa'_ball ρ hρ
    have hρ0 : h ρ = 0 := (hZa'_iff ρ hρb).mpr hρ
    have hρc : ρ ≠ c := by
      rintro rfl
      rw [hh, hF₀c, zero_sub, neg_eq_zero] at hρ0
      exact hw₀0.ne' (by exact_mod_cast hρ0)
    have hρU : U ∈ 𝓝 ρ := hUo.mem_nhds (hsub' (ball_subset_closedBall
      (ball_subset_ball (by linarith) hρb)))
    refine zeroMult_eq_one_of_analyticAt (((hfU.sub_const v).sub_const _).analyticAt hρU) hρ0 ?_
    rw [hderiv_h]
    exact hcrit ρ (ball_subset_ball (by linarith) hρb) hρc
  have hcard : 2 ≤ Za'.card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_congr rfl hsimple, hZa'_sum]
    exact hF₀2
  obtain ⟨u, hu, u', hu', huu⟩ := Finset.one_lt_card.mp hcard
  -- the two `a`-points at height `τ`
  set a : ℂ := v + w₀ with ha
  have hfa : ∀ z ∈ Za', f z = a := by
    intro z hz
    have := (hZa'_iff z (hZa'_ball z hz)).mpr hz
    rw [hh, hF₀] at this
    rw [ha]; linear_combination this
  have hub := hZa'_ball u hu
  have hub' := hZa'_ball u' hu'
  rw [mem_ball, dist_eq_norm] at hub hub'
  have huz : ‖u - z₀‖ < 1 / 32 := by
    calc ‖u - z₀‖ = ‖(u - c) + (c - z₀)‖ := by ring_nf
      _ ≤ ‖u - c‖ + ‖c - z₀‖ := norm_add_le _ _
      _ < 1 / 32 := by linarith
  have hre := (abs_re_le_norm (u - z₀)).trans huz.le
  have him := (abs_im_le_norm (u - z₀)).trans huz.le
  rw [sub_re, hz₀, ofReal_re] at hre
  rw [sub_im, hz₀, ofReal_im, sub_zero] at him
  have hsim : (u + τ * I).im = u.im + τ := by simp
  have hsre : (u + τ * I).re = u.re := by simp
  have habs : |(u + τ * I).im| = u.im + τ := by
    rw [hsim]; exact abs_of_pos (by linarith [(abs_le.mp him).1])
  refine ⟨a, ⟨u + τ * I, u' + τ * I, hfa u hu, hfa u' hu', fun h' => huu (add_right_cancel h'),
    by rw [hsre]; linarith [(abs_le.mp hre).1], by rw [hsre]; linarith [(abs_le.mp hre).2],
    by rw [habs]; linarith [(abs_le.mp him).1], ?_⟩, ?_⟩
  · rw [add_sub_add_right_eq_sub, habs]
    calc ‖u' - u‖ = ‖(u' - c) - (u - c)‖ := by ring_nf
      _ ≤ ‖u' - c‖ + ‖u - c‖ := norm_sub_le _ _
      _ < 2 * δ' := by linarith
      _ ≤ Real.exp (-(τ + 2)) := by linarith
      _ ≤ Real.exp (-(u.im + τ)) :=
          Real.exp_le_exp.mpr (by linarith [(abs_le.mp him).2])
  · -- `|a − a₀| ≤ |f(c) − g(c)| + m|c − z₀|² + w₀`
    have hcK : c ∈ K := by
      rw [hK, mem_closedBall, dist_eq_norm]; linarith
    have h1 : ‖v - g c‖ < η := hτ c hcK
    have h2 : ‖g c - a₀‖ ≤ r₀ / 4 := by
      rw [hg, add_sub_cancel_left, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hm0]
      have : ‖c - z₀‖ ^ 2 ≤ (1 / 128) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcz₀.le 2
      have hmr : m ≤ r₀ := min_le_right _ _
      nlinarith
    have h3 : ‖((w₀ : ℝ) : ℂ)‖ ≤ r₀ / 4 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw₀0]; exact min_le_right _ _
    have hη4 : η ≤ r₀ / 4 := min_le_right _ _
    calc ‖a - a₀‖ = ‖(v - g c) + (g c - a₀) + ((w₀ : ℝ) : ℂ)‖ := by rw [ha]; ring_nf
      _ ≤ ‖v - g c‖ + ‖g c - a₀‖ + ‖((w₀ : ℝ) : ℂ)‖ := by
          have t1 := norm_add_le ((v - g c) + (g c - a₀)) ((w₀ : ℝ) : ℂ)
          have t2 := norm_add_le (v - g c) (g c - a₀)
          linarith
      _ < r₀ := by linarith

end GaloisForLFunctions.ArithmeticDiscreteness
