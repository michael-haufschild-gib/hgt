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
  fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

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
  have := congrArg Complex.re h2
  simp only [div_re, neg_re, one_re] at this
  norm_num at this
  nlinarith [Real.pi_pos]

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

end GaloisForLFunctions.ArithmeticDiscreteness
