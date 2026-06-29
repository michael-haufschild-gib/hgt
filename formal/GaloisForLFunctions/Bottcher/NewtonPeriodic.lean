import GaloisForLFunctions.Bottcher.CrossRatioSelectorBridge
import GaloisForLFunctions.Bottcher.JuliaExpansion
import GaloisForLFunctions.Bottcher.RepellingPeriodicFrontier
import GaloisForLFunctions.Bottcher.InverseBranchPeriodic
import Mathlib.Analysis.Real.Cardinality

open Set Filter Topology Metric

namespace Bottcher

noncomputable section

/-- A derivative-bounded self-map of a closed ball has a fixed point once the center displacement
fits inside the contraction margin. -/
theorem exists_fixed_point_of_deriv_bound_self_map_closedBall
    {a : ℂ} {r : ℝ} {T : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hcenter : dist (T a) a + (K : ℝ) * r ≤ r)
    (hderivWithin : ∀ z ∈ Metric.closedBall a r,
      HasDerivWithinAt T (deriv T z) (Metric.closedBall a r) z)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r, ‖deriv T z‖ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.closedBall a r, T y = y := by
  have hlip : LipschitzOnWith K T (Metric.closedBall a r) := by
    apply (convex_closedBall a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      hderivWithin
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hderiv_bound z hz
  have ha : a ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_self]
    exact hr
  have hmaps : Set.MapsTo T (Metric.closedBall a r) (Metric.closedBall a r) := by
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have hdist := hlip.dist_le_mul y hy a ha
    have hstep : dist (T y) a ≤ (K : ℝ) * r + dist (T a) a := by
      have hmul : (K : ℝ) * dist y a ≤ (K : ℝ) * r :=
        mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg K)
      calc
        dist (T y) a ≤ dist (T y) (T a) + dist (T a) a := dist_triangle _ _ _
        _ ≤ (K : ℝ) * dist y a + dist (T a) a := by
          simpa using add_le_add_right hdist (dist (T a) a)
        _ ≤ (K : ℝ) * r + dist (T a) a := by
          simpa using add_le_add_right hmul (dist (T a) a)
    linarith [hstep, hcenter]
  have hcontr : ContractingWith K
      (Set.MapsTo.restrict T (Metric.closedBall a r) (Metric.closedBall a r) hmaps) := by
    refine ⟨hK, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hdist := hlip.dist_le_mul x.1 x.2 y.1 y.2
    simpa [Set.MapsTo.restrict, Subtype.dist_eq] using hdist
  have hcomplete : IsComplete (Metric.closedBall a r) := Metric.isClosed_closedBall.isComplete
  obtain ⟨y, hy, hfix, _htend, _hest⟩ :=
    hcontr.exists_fixedPoint' hcomplete hmaps ha (edist_ne_top a (T a))
  exact ⟨y, hy, by simpa [Function.IsFixedPt] using hfix⟩

/-- The Newton correction map for a quadratic iterate is differentiable on every set. -/
theorem hasDerivWithinAt_newton_quadratic_iterate
    (c A : ℂ) (q : ℕ) (s : Set ℂ) (z : ℂ) :
    HasDerivWithinAt
      (fun w => w - A * ((quadratic c)^[q] w - w))
      (deriv (fun w => w - A * ((quadratic c)^[q] w - w)) z) s z := by
  have hdiff : Differentiable ℂ
      (fun w => w - A * ((quadratic c)^[q] w - w)) := by
    have hiter : Differentiable ℂ ((quadratic c)^[q]) :=
      differentiable_quadratic_iterate c q
    fun_prop
  exact (hdiff z).hasDerivAt.hasDerivWithinAt

/-- Derivative of the Newton correction map for `f_c^[q] - id`. -/
theorem deriv_newton_quadratic_iterate (c A : ℂ) (q : ℕ) (z : ℂ) :
    deriv (fun w => w - A * ((quadratic c)^[q] w - w)) z =
      1 - A * (deriv ((quadratic c)^[q]) z - 1) := by
  have hF : HasDerivAt ((quadratic c)^[q]) (deriv ((quadratic c)^[q]) z) z :=
    (differentiable_quadratic_iterate c q z).hasDerivAt
  have hid : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have hdiff : HasDerivAt (fun w => (quadratic c)^[q] w - w)
      (deriv ((quadratic c)^[q]) z - 1) z := hF.sub hid
  have hmul : HasDerivAt (fun w => A * ((quadratic c)^[q] w - w))
      (A * (deriv ((quadratic c)^[q]) z - 1)) z := hdiff.const_mul A
  exact (hid.sub hmul).deriv

/-- With the inverse derivative as coefficient, the Newton correction derivative at the center is
the inverse derivative. -/
theorem deriv_newton_quadratic_iterate_inv_deriv
    {c : ℂ} {q : ℕ} {z : ℂ}
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0) :
    deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ * ((quadratic c)^[q] w - w)) z =
      (deriv ((quadratic c)^[q]) z)⁻¹ := by
  rw [deriv_newton_quadratic_iterate]
  field_simp [hderiv]
  ring

/-- The Newton correction map for a quadratic iterate is analytic at every point. -/
theorem analyticAt_newton_quadratic_iterate (c A : ℂ) (q : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w => w - A * ((quadratic c)^[q] w - w)) z := by
  have hF : AnalyticAt ℂ ((quadratic c)^[q]) z := analyticAt_quadratic_iterate c q z
  have hdiff : AnalyticAt ℂ (fun w => (quadratic c)^[q] w - w) z := by
    simpa using hF.sub analyticAt_id
  have hmul : AnalyticAt ℂ (fun w => A * ((quadratic c)^[q] w - w)) z := by
    simpa using (analyticAt_const (v := A) (x := z)).mul hdiff
  simpa using analyticAt_id.sub hmul

/-- Numeric center-fit estimate for a contraction closed ball. -/
theorem center_add_mul_radius_le_of_le_one_sub_mul
    {d r : ℝ} {K : NNReal} (hK : K < 1)
    (hd : d ≤ (1 - (K : ℝ)) * r) : d + (K : ℝ) * r ≤ r := by
  have hKle : (K : ℝ) ≤ 1 := le_of_lt (by exact_mod_cast hK)
  nlinarith [NNReal.coe_nonneg K]

/-- If `z` hits a fixed anchor after `n` steps, then every later tail remains at that fixed anchor. -/
theorem iterate_add_eq_fixed_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    (quadratic c)^[n + m] z = α := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, hhit, Function.iterate_fixed hfix m]

/-- Orbit-product factorization at a forward hit to a fixed anchor.  The finite preperiodic segment
is separated from the fixed tail, whose multiplier is `(2α)^m`. -/
theorem orbitProduct_fixed_tail_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    (∏ k ∈ Finset.range (n + m), 2 * (quadratic c)^[k] z)
      = (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) * ((2 : ℂ) * α) ^ m := by
  rw [deriv_iterate_quadratic_cocycle]
  congr 1
  calc
    (∏ k ∈ Finset.range m, 2 * (quadratic c)^[k] ((quadratic c)^[n] z))
        = ∏ k ∈ Finset.range m, 2 * (quadratic c)^[k] α := by
          rw [hhit]
    _ = ∏ _k ∈ Finset.range m, (2 : ℂ) * α := by
          apply Finset.prod_congr rfl
          intro k _hk
          rw [Function.iterate_fixed hfix k]
    _ = ((2 : ℂ) * α) ^ m := by
          rw [Finset.prod_const, Finset.card_range]

/-- Derivative factorization at a forward hit to a fixed anchor. -/
theorem deriv_fixed_tail_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    deriv ((quadratic c)^[n + m]) z
      = (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) * ((2 : ℂ) * α) ^ m := by
  rw [deriv_quadratic_iterate_eq_orbitProduct_core]
  exact orbitProduct_fixed_tail_of_iterate_eq_fixed hhit hfix m

/-- The finite initial orbit product is nonzero exactly when the preperiodic segment avoids the
critical point `0`. -/
theorem orbitProduct_ne_zero_iff_no_precritical
    (c z : ℂ) (n : ℕ) :
    (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 ↔
      ∀ k < n, (quadratic c)^[k] z ≠ 0 := by
  constructor
  · intro hprod k hk hcrit
    apply hprod
    rw [Finset.prod_eq_zero_iff]
    exact ⟨k, Finset.mem_range.mpr hk, by simp [hcrit]⟩
  · intro hcrit
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    exact mul_ne_zero (by norm_num) (hcrit k (Finset.mem_range.mp hk))

/-- A forward hit to a value outside the positive critical orbit has a noncritical preimage segment. -/
theorem no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit
    {c z w : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = w)
    (hwcrit : w ∉ positiveCriticalOrbit c) :
    ∀ k < n, (quadratic c)^[k] z ≠ 0 := by
  intro k hk hcrit
  have hpos : 1 ≤ n - k := by omega
  have hdecomp : n = (n - k) + k := by omega
  have hw : w = (quadratic c)^[n - k] 0 := by
    rw [← hhit, hdecomp, Function.iterate_add_apply, hcrit]
    congr 1
    omega
  apply hwcrit
  refine ⟨n - k - 1, ?_⟩
  have hsucc : n - k - 1 + 1 = n - k := by omega
  change (quadratic c)^[n - k - 1 + 1] 0 = w
  rw [hsucc]
  exact hw.symm

/-- Orbit-product nonvanishing from a hit outside the positive critical orbit. -/
theorem orbitProduct_ne_zero_of_iterate_eq_not_mem_positiveCriticalOrbit
    {c z w : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = w)
    (hwcrit : w ∉ positiveCriticalOrbit c) :
    (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 :=
  (orbitProduct_ne_zero_iff_no_precritical c z n).2
    (no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hwcrit)

/-- Derivative nonvanishing from a hit outside the positive critical orbit. -/
theorem deriv_ne_zero_of_iterate_eq_not_mem_positiveCriticalOrbit
    {c z w : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = w)
    (hwcrit : w ∉ positiveCriticalOrbit c) :
    deriv ((quadratic c)^[n]) z ≠ 0 := by
  rw [deriv_quadratic_iterate_eq_orbitProduct_core]
  exact orbitProduct_ne_zero_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hwcrit

/-- A concrete uncountable target set outside the half-radius source ball: a real segment on the
ray starting just past radius `R / 2`. -/
def offBallRealSegment (ζ : ℂ) (R : ℝ) : Set ℂ :=
  (fun t : ℝ => ζ + ((R / 2 + t : ℝ) : ℂ)) '' Set.Ioo (0 : ℝ) 1

/-- The concrete off-ball target is uncountable. -/
theorem not_countable_offBallRealSegment (ζ : ℂ) (R : ℝ) :
    ¬ (offBallRealSegment ζ R).Countable := by
  intro hcount
  let f : ℝ → ℂ := fun t => ζ + ((R / 2 + t : ℝ) : ℂ)
  have hf : Function.Injective f := by
    intro x y hxy
    have hcoe : ((R / 2 + x : ℝ) : ℂ) = ((R / 2 + y : ℝ) : ℂ) := by
      simpa [f] using add_left_cancel hxy
    have hreal : R / 2 + x = R / 2 + y := Complex.ofReal_injective hcoe
    linarith
  have hpre : (f ⁻¹' offBallRealSegment ζ R).Countable := hcount.preimage hf
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ f ⁻¹' offBallRealSegment ζ R := by
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIcount : (Set.Ioo (0 : ℝ) 1).Countable := hpre.mono hsub
  have hle : (1 : ℝ) ≤ 0 :=
    (Cardinal.Real.Ioo_countable_iff (x := (0 : ℝ)) (y := 1)).mp hIcount
  norm_num at hle

/-- The concrete target lies outside the half-radius source ball. -/
theorem offBallRealSegment_offBall {ζ : ℂ} {R : ℝ} (hR : 0 < R) :
    ∀ w ∈ offBallRealSegment ζ R, w ∉ Metric.ball ζ (R / 2) := by
  intro w hw hball
  rcases hw with ⟨t, ht, rfl⟩
  have htpos : 0 < t := ht.1
  have hnonneg : 0 ≤ R / 2 + t := by linarith
  have hdist : dist (ζ + ((R / 2 + t : ℝ) : ℂ)) ζ = R / 2 + t := by
    rw [dist_eq_norm, add_sub_cancel_left]
    calc
      ‖((R / 2 + t : ℝ) : ℂ)‖ = |R / 2 + t| := by
        simpa using (RCLike.norm_ofReal (K := ℂ) (R / 2 + t))
      _ = R / 2 + t := abs_of_nonneg hnonneg
  rw [Metric.mem_ball, hdist] at hball
  linarith

/-- Countable-avoidance selector output in the regular-hit form needed for local inverse branches:
for any non-countable off-ball target set, a frontier ball either already has a positive periodic
point or has a positive-depth hit whose iterate derivative is nonzero. -/
theorem frontier_ball_positive_periodic_or_regular_forward_hit_target_off_ball
    {c z₀ : ℂ} {ρ Rlift : ℝ} {T : Set ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hT : ¬ T.Countable)
    (hToff : ∀ w ∈ T, w ∉ ball z₀ Rlift) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      ∃ w ∈ T, ∃ n z,
        1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = w ∧
          deriv ((quadratic c)^[n]) z ≠ 0 := by
  have hsel := frontier_ball_positive_periodic_or_forward_hit_target_avoiding_criticalOrbit
    (c := c) (z₀ := z₀) (ρ := ρ) (Rlift := Rlift) (T := T)
    hzfront hρ0 hρR hT hToff
  rcases hsel with hper | hhit
  · exact Or.inl hper
  · rcases hhit with ⟨w, hwT, hwcrit, n, z, hn, hz, hval⟩
    exact Or.inr ⟨w, hwT, n, z, hn, hz, hval,
      deriv_ne_zero_of_iterate_eq_not_mem_positiveCriticalOrbit hval hwcrit⟩

/-- Half-radius regular-hit selector bridge.  To prove ordinary positive-periodic density in every
frontier ball, it is enough to convert regular positive-depth hits into any non-countable target set
lying outside the half-radius source ball. -/
theorem forall_frontier_ball_positive_periodic_of_offBall_regular_hit_to_positive_periodic_half
    {c : ℂ}
    (hconvert : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
        ∃ T : Set ℂ,
          ¬ T.Countable ∧
          (∀ w ∈ T, w ∉ Metric.ball z₀ (R / 2)) ∧
          ∀ w ∈ T, ∀ n z,
            1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
            (quadratic c)^[n] z = w →
            deriv ((quadratic c)^[n]) z ≠ 0 →
            ∃ y ∈ Metric.ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ Metric.ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  intro z₀ hzfront R hR
  have hρ0 : 0 < R / 8 := by linarith
  have hρR : R / 8 < (R / 2) / 2 := by linarith
  obtain ⟨T, hT, hToff, hhit_to_periodic⟩ := hconvert hzfront hρ0 hρR
  have hsel := frontier_ball_positive_periodic_or_regular_forward_hit_target_off_ball
    (c := c) (z₀ := z₀) (ρ := R / 8) (Rlift := R / 2) (T := T)
    hzfront hρ0 hρR hT hToff
  rcases hsel with hper | hhit
  · obtain ⟨n, z, hn, hz, hfix⟩ := hper
    have hzR : z ∈ Metric.ball z₀ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨z, hzR, n, hn, hfix⟩
  · obtain ⟨w, hwT, n, z, hn, hz, hval, hderiv⟩ := hhit
    exact hhit_to_periodic w hwT n z hn hz hval hderiv

/-- Half-radius regular-hit selector bridge specialized to the IFT local-inverse route.  The
remaining local input is exactly the quantitative inverse multiplier and trapping/location estimate
for each regular positive-depth hit into a non-countable off-ball target set. -/
theorem forall_frontier_ball_positive_periodic_of_regular_hit_localInverse_half
    {c : ℂ}
    (hconvert : ∀ {ζ : ℂ} {ρ R : ℝ},
      ζ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
        ∃ T : Set ℂ,
          ¬ T.Countable ∧
          (∀ w ∈ T, w ∉ Metric.ball ζ (R / 2)) ∧
          ∀ w ∈ T, ∀ p z,
            1 ≤ p → z ∈ Metric.ball ζ (R / 2) →
            (quadratic c)^[p] z = w →
            deriv ((quadratic c)^[p]) z ≠ 0 →
            ∃ K : NNReal,
              K < 1 ∧
              ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ) ∧
              (∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
                g ((quadratic c)^[p] z) = z →
                (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
                  HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
                    (fun u => (quadratic c)^[p] (g u)) =ᶠ[𝓝 y] id) →
                dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
                  Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R)) :
    ∀ ζ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ Metric.ball ζ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  intro ζ hzfront R hR
  have hρ0 : 0 < R / 8 := by linarith
  have hρR : R / 8 < (R / 2) / 2 := by linarith
  obtain ⟨T, hT, hToff, hhit_to_inverse⟩ := hconvert hzfront hρ0 hρR
  have hsel := frontier_ball_positive_periodic_or_regular_forward_hit_target_off_ball
    (c := c) (z₀ := ζ) (ρ := R / 8) (Rlift := R / 2) (T := T)
    hzfront hρ0 hρR hT hToff
  rcases hsel with hper | hhit
  · obtain ⟨p, z, hp, hz, hfix⟩ := hper
    have hzR : z ∈ Metric.ball ζ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨z, hzR, p, hp, hfix⟩
  · obtain ⟨w, hwT, p, z, hp, hz, hhit, hderiv⟩ := hhit
    obtain ⟨K, hK, hKderiv, hgeom⟩ :=
      hhit_to_inverse w hwT p z hp hz hhit hderiv
    obtain ⟨y, hyball, hper⟩ :=
      exists_periodic_mem_ball_of_localInverse_iterate_near_return
        (c := c) (ζ := ζ) (z := z) (p := p) (R := R) (K := K)
        hK hderiv hKderiv hgeom
    exact ⟨y, hyball, p, hp, hper⟩

/-- Concrete-target form of `forall_frontier_ball_positive_periodic_of_regular_hit_localInverse_half`.
The selector target is the fixed real segment `offBallRealSegment ζ R`, so the caller only has to
convert arbitrary regular hits outside the half-radius source ball. -/
theorem forall_frontier_ball_positive_periodic_of_all_offBall_regular_hit_localInverse_half
    {c : ℂ}
    (hconvert : ∀ {ζ : ℂ} {ρ R : ℝ},
      ζ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
        ∀ w, w ∉ Metric.ball ζ (R / 2) →
          ∀ p z,
            1 ≤ p → z ∈ Metric.ball ζ (R / 2) →
            (quadratic c)^[p] z = w →
            deriv ((quadratic c)^[p]) z ≠ 0 →
            ∃ K : NNReal,
              K < 1 ∧
              ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ) ∧
              (∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
                g ((quadratic c)^[p] z) = z →
                (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
                  HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
                    (fun u => (quadratic c)^[p] (g u)) =ᶠ[𝓝 y] id) →
                dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
                  Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R)) :
    ∀ ζ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ Metric.ball ζ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_regular_hit_localInverse_half
  intro ζ ρ R hzfront hρ0 hρR
  have hR : 0 < R := by linarith
  refine ⟨offBallRealSegment ζ R, not_countable_offBallRealSegment ζ R,
    offBallRealSegment_offBall hR, ?_⟩
  intro w hw p z hp hz hhit hderiv
  exact hconvert hzfront hρ0 hρR w
    (offBallRealSegment_offBall hR w hw) p z hp hz hhit hderiv

/-- A noncritical hit to a repelling fixed anchor has nonzero derivative along every fixed tail. -/
theorem deriv_fixed_tail_ne_zero_of_repelling_hit
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) (m : ℕ) :
    deriv ((quadratic c)^[n + m]) z ≠ 0 := by
  rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m]
  exact mul_ne_zero hinit (pow_ne_zero _ (norm_pos_iff.mp (lt_trans zero_lt_one hrep)))

/-- Recursive coefficient for the second derivative of a fixed tail.  If `α` is fixed and
`λ = 2α`, then `(f_c^[m])''(α)` is `fixedTailSecondCoeff λ m`. -/
def fixedTailSecondCoeff (lam : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 => lam * fixedTailSecondCoeff lam m + 2 * lam ^ (2 * m)

/-- Quantitative growth bound for the fixed-tail second-derivative coefficient.  For repelling
`|λ| > 1`, any constant `C` with `2 ≤ C |λ| (|λ|-1)` bounds the coefficient by
`C |λ|^(2m)`. -/
theorem norm_fixedTailSecondCoeff_le_mul_pow
    {lam : ℂ} {C : ℝ}
    (hCnonneg : 0 ≤ C)
    (hC : 2 ≤ C * ‖lam‖ * (‖lam‖ - 1)) :
    ∀ m : ℕ, ‖fixedTailSecondCoeff lam m‖ ≤ C * ‖lam‖ ^ (2 * m) := by
  intro m
  induction m with
  | zero =>
      simp [fixedTailSecondCoeff, hCnonneg]
  | succ m ih =>
      have hstep : ‖fixedTailSecondCoeff lam (m + 1)‖ ≤
          ‖lam‖ * ‖fixedTailSecondCoeff lam m‖ + 2 * ‖lam‖ ^ (2 * m) := by
        calc
          ‖lam * fixedTailSecondCoeff lam m + 2 * lam ^ (2 * m)‖
              ≤ ‖lam * fixedTailSecondCoeff lam m‖ + ‖2 * lam ^ (2 * m)‖ :=
                norm_add_le _ _
          _ = ‖lam‖ * ‖fixedTailSecondCoeff lam m‖ + 2 * ‖lam‖ ^ (2 * m) := by
              rw [norm_mul, norm_mul, Complex.norm_two, norm_pow]
      have hmain : ‖lam‖ * ‖fixedTailSecondCoeff lam m‖ + 2 * ‖lam‖ ^ (2 * m) ≤
          C * ‖lam‖ ^ (2 * (m + 1)) := by
        calc
          ‖lam‖ * ‖fixedTailSecondCoeff lam m‖ + 2 * ‖lam‖ ^ (2 * m)
              ≤ ‖lam‖ * (C * ‖lam‖ ^ (2 * m)) + 2 * ‖lam‖ ^ (2 * m) := by
                gcongr
          _ = (C * ‖lam‖ + 2) * ‖lam‖ ^ (2 * m) := by ring
          _ ≤ (C * ‖lam‖ ^ 2) * ‖lam‖ ^ (2 * m) := by
                gcongr
                nlinarith [hC]
          _ = C * ‖lam‖ ^ (2 * (m + 1)) := by
                rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
                ring
      exact le_trans hstep hmain

/-- One-step derivative formula for quadratic iterates. -/
theorem deriv_quadratic_iterate_succ_eq (c : ℂ) (m : ℕ) (w : ℂ) :
    deriv ((quadratic c)^[m + 1]) w =
      2 * (quadratic c)^[m] w * deriv ((quadratic c)^[m]) w := by
  rw [deriv_quadratic_iterate_eq_orbitProduct_core,
    deriv_quadratic_iterate_eq_orbitProduct_core]
  rw [Finset.prod_range_succ]
  ring

/-- Second derivative of a fixed tail at the fixed point, in recursive closed form. -/
theorem hasDerivAt_deriv_iterate_fixed
    {c α : ℂ} (hfix : quadratic c α = α) (m : ℕ) :
    HasDerivAt (fun w => deriv ((quadratic c)^[m]) w)
      (fixedTailSecondCoeff ((2 : ℂ) * α) m) α := by
  induction m with
  | zero =>
      simpa [fixedTailSecondCoeff] using (hasDerivAt_const α (1 : ℂ))
  | succ m ih =>
      let lam : ℂ := (2 : ℂ) * α
      have hderiv_succ : (fun w => deriv ((quadratic c)^[m + 1]) w) =
          fun w => 2 * (quadratic c)^[m] w * deriv ((quadratic c)^[m]) w := by
        funext w
        exact deriv_quadratic_iterate_succ_eq c m w
      have hF : HasDerivAt ((quadratic c)^[m]) (lam ^ m) α := by
        have hbase : HasDerivAt ((quadratic c)^[m])
            (deriv ((quadratic c)^[m]) α) α :=
          (differentiable_quadratic_iterate c m α).hasDerivAt
        have hderiv : deriv ((quadratic c)^[m]) α = lam ^ m := by
          dsimp [lam]
          simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
            (n := 0) (by rfl) hfix m)
        simpa [hderiv] using hbase
      have hFval : (quadratic c)^[m] α = α := Function.iterate_fixed hfix m
      have hDval : deriv ((quadratic c)^[m]) α = lam ^ m := by
        dsimp [lam]
        simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
          (n := 0) (by rfl) hfix m)
      have hprod : HasDerivAt
          (fun w => 2 * (quadratic c)^[m] w * deriv ((quadratic c)^[m]) w)
          ((2 * lam ^ m) * deriv ((quadratic c)^[m]) α +
            (2 * (quadratic c)^[m] α) * fixedTailSecondCoeff lam m) α := by
        exact ((hF.const_mul 2).mul ih)
      rw [hderiv_succ]
      convert hprod using 1
      simp [fixedTailSecondCoeff, lam, hDval, hFval]
      ring

/-- The derivative of the derivative along a fixed tail after a preperiodic hit.  This is the exact
second-derivative decomposition behind the fixed-tail Newton window. -/
theorem hasDerivAt_deriv_fixed_tail_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    HasDerivAt (fun w => deriv ((quadratic c)^[n + m]) w)
      (fixedTailSecondCoeff ((2 : ℂ) * α) m * (deriv ((quadratic c)^[n]) z) ^ 2 +
        ((2 : ℂ) * α) ^ m * deriv (fun w => deriv ((quadratic c)^[n]) w) z) z := by
  let lam : ℂ := (2 : ℂ) * α
  let P : ℂ := deriv ((quadratic c)^[n]) z
  let B : ℂ := deriv (fun w => deriv ((quadratic c)^[n]) w) z
  let A : ℂ := fixedTailSecondCoeff lam m
  have hderiv_add : (fun w => deriv ((quadratic c)^[n + m]) w) =
      fun w => deriv ((quadratic c)^[m]) ((quadratic c)^[n] w) *
        deriv ((quadratic c)^[n]) w := by
    funext w
    rw [deriv_quadratic_iterate_eq_orbitProduct_core,
      deriv_quadratic_iterate_eq_orbitProduct_core,
      deriv_quadratic_iterate_eq_orbitProduct_core]
    rw [deriv_iterate_quadratic_cocycle]
    ring
  have hA : HasDerivAt (fun w => deriv ((quadratic c)^[m]) w) A α := by
    simpa [A, lam] using hasDerivAt_deriv_iterate_fixed hfix m
  have hG : HasDerivAt ((quadratic c)^[n]) P z := by
    simpa [P] using (differentiable_quadratic_iterate c n z).hasDerivAt
  have hAat : HasDerivAt (fun w => deriv ((quadratic c)^[m]) w) A ((quadratic c)^[n] z) := by
    rwa [hhit]
  have hcomp : HasDerivAt
      (fun w => deriv ((quadratic c)^[m]) ((quadratic c)^[n] w)) (A * P) z :=
    hAat.comp z hG
  have hB : HasDerivAt (fun w => deriv ((quadratic c)^[n]) w) B z :=
    (analyticAt_quadratic_iterate c n z).deriv.differentiableAt.hasDerivAt
  have hDtail : deriv ((quadratic c)^[m]) α = lam ^ m := by
    dsimp [lam]
    simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
      (n := 0) (by rfl) hfix m)
  rw [hderiv_add]
  have hprod := hcomp.mul hB
  convert hprod using 1
  simp [A, P, B, lam, hhit, hDtail]
  ring

/-- Equality form of `hasDerivAt_deriv_fixed_tail_of_iterate_eq_fixed`. -/
theorem deriv_deriv_fixed_tail_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    deriv (fun w => deriv ((quadratic c)^[n + m]) w) z =
      fixedTailSecondCoeff ((2 : ℂ) * α) m * (deriv ((quadratic c)^[n]) z) ^ 2 +
        ((2 : ℂ) * α) ^ m * deriv (fun w => deriv ((quadratic c)^[n]) w) z :=
  (hasDerivAt_deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m).deriv

/-- Norm bound for the exact second-derivative fixed-tail decomposition.  This is the quantitative
shape of the remaining Newton-window obstruction: the leading term grows like `|2α|^(2m)`, while
the inverse first derivative only decays like `|2α|^(-m)`. -/
theorem norm_deriv_deriv_fixed_tail_of_iterate_eq_fixed_le
    {c z α : ℂ} {n : ℕ} {C : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hCnonneg : 0 ≤ C)
    (hC : 2 ≤ C * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (m : ℕ) :
    ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) z‖ ≤
      C * ‖(2 : ℂ) * α‖ ^ (2 * m) * ‖deriv ((quadratic c)^[n]) z‖ ^ 2 +
        ‖(2 : ℂ) * α‖ ^ m *
          ‖deriv (fun w => deriv ((quadratic c)^[n]) w) z‖ := by
  rw [deriv_deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m]
  have hA := norm_fixedTailSecondCoeff_le_mul_pow
    (lam := (2 : ℂ) * α) hCnonneg hC m
  calc
    ‖fixedTailSecondCoeff ((2 : ℂ) * α) m * (deriv ((quadratic c)^[n]) z) ^ 2 +
        ((2 : ℂ) * α) ^ m * deriv (fun w => deriv ((quadratic c)^[n]) w) z‖
        ≤ ‖fixedTailSecondCoeff ((2 : ℂ) * α) m * (deriv ((quadratic c)^[n]) z) ^ 2‖ +
          ‖((2 : ℂ) * α) ^ m * deriv (fun w => deriv ((quadratic c)^[n]) w) z‖ :=
          norm_add_le _ _
    _ = ‖fixedTailSecondCoeff ((2 : ℂ) * α) m‖ *
          ‖deriv ((quadratic c)^[n]) z‖ ^ 2 +
        ‖(2 : ℂ) * α‖ ^ m *
          ‖deriv (fun w => deriv ((quadratic c)^[n]) w) z‖ := by
          rw [norm_mul, norm_pow, norm_mul, norm_pow]
    _ ≤ C * ‖(2 : ℂ) * α‖ ^ (2 * m) * ‖deriv ((quadratic c)^[n]) z‖ ^ 2 +
        ‖(2 : ℂ) * α‖ ^ m *
          ‖deriv (fun w => deriv ((quadratic c)^[n]) w) z‖ := by
          gcongr

/-- Recursive coefficient for the third derivative of a fixed tail.  If `α` is fixed,
`λ = 2α`, and `(f_c^[m])''(α)` is `fixedTailSecondCoeff λ m`, then this coefficient is
`(f_c^[m])'''(α)`. -/
def fixedTailThirdCoeff (lam : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 =>
      lam * fixedTailThirdCoeff lam m +
        6 * lam ^ m * fixedTailSecondCoeff lam m

/-- Quantitative growth bound for the fixed-tail third-derivative coefficient, assuming a
quadratic growth bound for the second coefficient.

The recurrence is `C₃(m+1) = λ C₃(m) + 6 λ^m C₂(m)`, so a cubic bound closes whenever the
available cubic constant absorbs `6 * C₂` across the multiplier gap `|λ|^3 - |λ|`. -/
theorem norm_fixedTailThirdCoeff_le_mul_pow_of_second_bound
    {lam : ℂ} {C₂ C₃ : ℝ}
    (hL : 1 < ‖lam‖)
    (hsecond : ∀ m : ℕ, ‖fixedTailSecondCoeff lam m‖ ≤ C₂ * ‖lam‖ ^ (2 * m))
    (hC₃nonneg : 0 ≤ C₃)
    (hC₃ : 6 * C₂ ≤ C₃ * ‖lam‖ * (‖lam‖ ^ 2 - 1)) :
    ∀ m : ℕ, ‖fixedTailThirdCoeff lam m‖ ≤ C₃ * ‖lam‖ ^ (3 * m) := by
  intro m
  induction m with
  | zero =>
      simp [fixedTailThirdCoeff, hC₃nonneg]
  | succ m ih =>
      let L : ℝ := ‖lam‖
      have hLpos : 0 < L := by
        dsimp [L]
        exact lt_trans zero_lt_one hL
      have hstep : ‖fixedTailThirdCoeff lam (m + 1)‖ ≤
          L * ‖fixedTailThirdCoeff lam m‖ +
            6 * L ^ m * ‖fixedTailSecondCoeff lam m‖ := by
        calc
          ‖lam * fixedTailThirdCoeff lam m +
              6 * lam ^ m * fixedTailSecondCoeff lam m‖
              ≤ ‖lam * fixedTailThirdCoeff lam m‖ +
                  ‖(6 : ℂ) * lam ^ m * fixedTailSecondCoeff lam m‖ :=
                norm_add_le _ _
          _ = L * ‖fixedTailThirdCoeff lam m‖ +
                6 * L ^ m * ‖fixedTailSecondCoeff lam m‖ := by
              dsimp [L]
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
      have hmain : L * ‖fixedTailThirdCoeff lam m‖ +
            6 * L ^ m * ‖fixedTailSecondCoeff lam m‖ ≤
          C₃ * L ^ (3 * (m + 1)) := by
        have hsecond_m :
            ‖fixedTailSecondCoeff lam m‖ ≤ C₂ * L ^ (2 * m) := by
          simpa [L] using hsecond m
        have hpow_nonneg : 0 ≤ L ^ (3 * m) := pow_nonneg (le_of_lt hLpos) _
        calc
          L * ‖fixedTailThirdCoeff lam m‖ +
              6 * L ^ m * ‖fixedTailSecondCoeff lam m‖
              ≤ L * (C₃ * L ^ (3 * m)) +
                  6 * L ^ m * (C₂ * L ^ (2 * m)) := by
                have hfirst : L * ‖fixedTailThirdCoeff lam m‖ ≤
                    L * (C₃ * L ^ (3 * m)) :=
                  mul_le_mul_of_nonneg_left ih (le_of_lt hLpos)
                have hfactor_nonneg : 0 ≤ 6 * L ^ m := by
                  positivity
                exact add_le_add hfirst
                  (mul_le_mul_of_nonneg_left hsecond_m hfactor_nonneg)
          _ = (C₃ * L + 6 * C₂) * L ^ (3 * m) := by
                ring_nf
          _ ≤ (C₃ * L ^ 3) * L ^ (3 * m) := by
                have hgap : 6 * C₂ ≤ C₃ * L ^ 3 - C₃ * L := by
                  dsimp [L]
                  nlinarith
                have hcoef : C₃ * L + 6 * C₂ ≤ C₃ * L ^ 3 := by nlinarith
                exact mul_le_mul_of_nonneg_right hcoef hpow_nonneg
          _ = C₃ * L ^ (3 * (m + 1)) := by
                rw [show 3 * (m + 1) = 3 * m + 3 by omega, pow_add]
                ring
      exact le_trans hstep hmain

/-- Explicit constant wrapper for `norm_fixedTailThirdCoeff_le_mul_pow_of_second_bound`, using the
existing fixed-tail second-derivative coefficient estimate. -/
theorem norm_fixedTailThirdCoeff_le_mul_pow
    {lam : ℂ} {C₂ C₃ : ℝ}
    (hL : 1 < ‖lam‖)
    (hC₂nonneg : 0 ≤ C₂)
    (hC₂ : 2 ≤ C₂ * ‖lam‖ * (‖lam‖ - 1))
    (hC₃nonneg : 0 ≤ C₃)
    (hC₃ : 6 * C₂ ≤ C₃ * ‖lam‖ * (‖lam‖ ^ 2 - 1)) :
    ∀ m : ℕ, ‖fixedTailThirdCoeff lam m‖ ≤ C₃ * ‖lam‖ ^ (3 * m) :=
  norm_fixedTailThirdCoeff_le_mul_pow_of_second_bound hL
    (norm_fixedTailSecondCoeff_le_mul_pow hC₂nonneg hC₂)
    hC₃nonneg hC₃

/-- Recursive coefficient for the fourth derivative of a fixed tail.  If `α` is fixed,
`λ = 2α`, and the lower derivative coefficients are the preceding fixed-tail coefficients, then
this coefficient is `(f_c^[m])''''(α)`.  The recurrence is the differentiated form of
`(f ∘ F)''' = 6 F' F'' + 2 F F'''`. -/
def fixedTailFourthCoeff (lam : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 =>
      lam * fixedTailFourthCoeff lam m +
        8 * lam ^ m * fixedTailThirdCoeff lam m +
        6 * (fixedTailSecondCoeff lam m) ^ 2

/-- Quantitative growth bound for the fixed-tail fourth-derivative coefficient, assuming quadratic
and cubic bounds for the second and third coefficients.

The recurrence is
`D₄(m+1) = λ D₄(m) + 8 λ^m D₃(m) + 6 D₂(m)^2`, so a quartic bound closes whenever the available
quartic constant absorbs `8*C₃ + 6*C₂^2` across the multiplier gap `|λ|^4 - |λ|`. -/
theorem norm_fixedTailFourthCoeff_le_mul_pow_of_second_third_bound
    {lam : ℂ} {C₂ C₃ C₄ : ℝ}
    (hL : 1 < ‖lam‖)
    (hsecond : ∀ m : ℕ, ‖fixedTailSecondCoeff lam m‖ ≤ C₂ * ‖lam‖ ^ (2 * m))
    (hthird : ∀ m : ℕ, ‖fixedTailThirdCoeff lam m‖ ≤ C₃ * ‖lam‖ ^ (3 * m))
    (hC₄nonneg : 0 ≤ C₄)
    (hC₄ : 8 * C₃ + 6 * C₂ ^ 2 ≤ C₄ * ‖lam‖ * (‖lam‖ ^ 3 - 1)) :
    ∀ m : ℕ, ‖fixedTailFourthCoeff lam m‖ ≤ C₄ * ‖lam‖ ^ (4 * m) := by
  intro m
  induction m with
  | zero =>
      simp [fixedTailFourthCoeff, hC₄nonneg]
  | succ m ih =>
      let L : ℝ := ‖lam‖
      have hLpos : 0 < L := by
        dsimp [L]
        exact lt_trans zero_lt_one hL
      have hstep : ‖fixedTailFourthCoeff lam (m + 1)‖ ≤
          L * ‖fixedTailFourthCoeff lam m‖ +
            8 * L ^ m * ‖fixedTailThirdCoeff lam m‖ +
            6 * ‖fixedTailSecondCoeff lam m‖ ^ 2 := by
        calc
          ‖lam * fixedTailFourthCoeff lam m +
              8 * lam ^ m * fixedTailThirdCoeff lam m +
              6 * (fixedTailSecondCoeff lam m) ^ 2‖
              ≤ (‖lam * fixedTailFourthCoeff lam m‖ +
                    ‖(8 : ℂ) * lam ^ m * fixedTailThirdCoeff lam m‖) +
                  ‖(6 : ℂ) * (fixedTailSecondCoeff lam m) ^ 2‖ := by
                calc
                  ‖lam * fixedTailFourthCoeff lam m +
                      8 * lam ^ m * fixedTailThirdCoeff lam m +
                      6 * (fixedTailSecondCoeff lam m) ^ 2‖
                      ≤ ‖lam * fixedTailFourthCoeff lam m +
                            8 * lam ^ m * fixedTailThirdCoeff lam m‖ +
                          ‖(6 : ℂ) * (fixedTailSecondCoeff lam m) ^ 2‖ :=
                        norm_add_le _ _
                  _ ≤ (‖lam * fixedTailFourthCoeff lam m‖ +
                          ‖(8 : ℂ) * lam ^ m * fixedTailThirdCoeff lam m‖) +
                        ‖(6 : ℂ) * (fixedTailSecondCoeff lam m) ^ 2‖ := by
                        exact add_le_add
                          (norm_add_le _ _)
                          (le_refl ‖(6 : ℂ) * (fixedTailSecondCoeff lam m) ^ 2‖)
          _ = L * ‖fixedTailFourthCoeff lam m‖ +
                8 * L ^ m * ‖fixedTailThirdCoeff lam m‖ +
                6 * ‖fixedTailSecondCoeff lam m‖ ^ 2 := by
              dsimp [L]
              rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, norm_pow,
                norm_mul, Complex.norm_ofNat, norm_pow]
      have hmain : L * ‖fixedTailFourthCoeff lam m‖ +
            8 * L ^ m * ‖fixedTailThirdCoeff lam m‖ +
            6 * ‖fixedTailSecondCoeff lam m‖ ^ 2 ≤
          C₄ * L ^ (4 * (m + 1)) := by
        have hsecond_m :
            ‖fixedTailSecondCoeff lam m‖ ≤ C₂ * L ^ (2 * m) := by
          simpa [L] using hsecond m
        have hthird_m :
            ‖fixedTailThirdCoeff lam m‖ ≤ C₃ * L ^ (3 * m) := by
          simpa [L] using hthird m
        have hsecond_sq :
            ‖fixedTailSecondCoeff lam m‖ ^ 2 ≤ (C₂ * L ^ (2 * m)) ^ 2 := by
          nlinarith [hsecond_m, norm_nonneg (fixedTailSecondCoeff lam m)]
        have hpow_nonneg : 0 ≤ L ^ (4 * m) := pow_nonneg (le_of_lt hLpos) _
        calc
          L * ‖fixedTailFourthCoeff lam m‖ +
              8 * L ^ m * ‖fixedTailThirdCoeff lam m‖ +
              6 * ‖fixedTailSecondCoeff lam m‖ ^ 2
              ≤ L * (C₄ * L ^ (4 * m)) +
                  8 * L ^ m * (C₃ * L ^ (3 * m)) +
                  6 * (C₂ * L ^ (2 * m)) ^ 2 := by
                have hfirst : L * ‖fixedTailFourthCoeff lam m‖ ≤
                    L * (C₄ * L ^ (4 * m)) :=
                  mul_le_mul_of_nonneg_left ih (le_of_lt hLpos)
                have hthird_factor_nonneg : 0 ≤ 8 * L ^ m := by positivity
                have hthird_term : 8 * L ^ m * ‖fixedTailThirdCoeff lam m‖ ≤
                    8 * L ^ m * (C₃ * L ^ (3 * m)) :=
                  mul_le_mul_of_nonneg_left hthird_m hthird_factor_nonneg
                have hsecond_term : 6 * ‖fixedTailSecondCoeff lam m‖ ^ 2 ≤
                    6 * (C₂ * L ^ (2 * m)) ^ 2 :=
                  mul_le_mul_of_nonneg_left hsecond_sq (by norm_num)
                exact add_le_add (add_le_add hfirst hthird_term) hsecond_term
          _ = (C₄ * L + 8 * C₃ + 6 * C₂ ^ 2) * L ^ (4 * m) := by
                ring_nf
          _ ≤ (C₄ * L ^ 4) * L ^ (4 * m) := by
                have hgap : 8 * C₃ + 6 * C₂ ^ 2 ≤ C₄ * L ^ 4 - C₄ * L := by
                  dsimp [L]
                  nlinarith
                have hcoef : C₄ * L + 8 * C₃ + 6 * C₂ ^ 2 ≤ C₄ * L ^ 4 := by
                  nlinarith
                exact mul_le_mul_of_nonneg_right hcoef hpow_nonneg
          _ = C₄ * L ^ (4 * (m + 1)) := by
                rw [show 4 * (m + 1) = 4 * m + 4 by omega, pow_add]
                ring
      exact le_trans hstep hmain

/-- Explicit constant wrapper for `norm_fixedTailFourthCoeff_le_mul_pow_of_second_third_bound`,
using the existing fixed-tail second- and third-derivative coefficient estimates. -/
theorem norm_fixedTailFourthCoeff_le_mul_pow
    {lam : ℂ} {C₂ C₃ C₄ : ℝ}
    (hL : 1 < ‖lam‖)
    (hC₂nonneg : 0 ≤ C₂)
    (hC₂ : 2 ≤ C₂ * ‖lam‖ * (‖lam‖ - 1))
    (hC₃nonneg : 0 ≤ C₃)
    (hC₃ : 6 * C₂ ≤ C₃ * ‖lam‖ * (‖lam‖ ^ 2 - 1))
    (hC₄nonneg : 0 ≤ C₄)
    (hC₄ : 8 * C₃ + 6 * C₂ ^ 2 ≤ C₄ * ‖lam‖ * (‖lam‖ ^ 3 - 1)) :
    ∀ m : ℕ, ‖fixedTailFourthCoeff lam m‖ ≤ C₄ * ‖lam‖ ^ (4 * m) :=
  norm_fixedTailFourthCoeff_le_mul_pow_of_second_third_bound hL
    (norm_fixedTailSecondCoeff_le_mul_pow hC₂nonneg hC₂)
    (norm_fixedTailThirdCoeff_le_mul_pow hL hC₂nonneg hC₂ hC₃nonneg hC₃)
    hC₄nonneg hC₄

/-- Second-derivative formula for the successor quadratic iterate. -/
theorem deriv_deriv_quadratic_iterate_succ_eq (c : ℂ) (m : ℕ) (w : ℂ) :
    deriv (fun v => deriv ((quadratic c)^[m + 1]) v) w =
      2 * (deriv ((quadratic c)^[m]) w) ^ 2 +
        2 * (quadratic c)^[m] w *
          deriv (fun v => deriv ((quadratic c)^[m]) v) w := by
  have hD : HasDerivAt (fun x => deriv ((quadratic c)^[m + 1]) x)
      (2 * (deriv ((quadratic c)^[m]) w) ^ 2 +
        2 * (quadratic c)^[m] w *
          deriv (fun v => deriv ((quadratic c)^[m]) v) w) w := by
    have hderiv_succ : (fun x => deriv ((quadratic c)^[m + 1]) x) =
        fun x => 2 * (quadratic c)^[m] x * deriv ((quadratic c)^[m]) x := by
      funext x
      exact deriv_quadratic_iterate_succ_eq c m x
    have hF : HasDerivAt ((quadratic c)^[m]) (deriv ((quadratic c)^[m]) w) w :=
      (differentiable_quadratic_iterate c m w).hasDerivAt
    have hB : HasDerivAt (fun x => deriv ((quadratic c)^[m]) x)
        (deriv (fun v => deriv ((quadratic c)^[m]) v) w) w :=
      (analyticAt_quadratic_iterate c m w).deriv.differentiableAt.hasDerivAt
    rw [hderiv_succ]
    convert ((hF.const_mul 2).mul hB) using 1
    · ring_nf
  exact hD.deriv

/-- Third-derivative formula for the successor quadratic iterate. -/
theorem deriv_deriv_deriv_quadratic_iterate_succ_eq (c : ℂ) (m : ℕ) (w : ℂ) :
    deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m + 1]) v) x) w =
      6 * deriv ((quadratic c)^[m]) w *
          deriv (fun v => deriv ((quadratic c)^[m]) v) w +
        2 * (quadratic c)^[m] w *
          deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w := by
  have hD : HasDerivAt
      (fun x => deriv (fun v => deriv ((quadratic c)^[m + 1]) v) x)
      (6 * deriv ((quadratic c)^[m]) w *
          deriv (fun v => deriv ((quadratic c)^[m]) v) w +
        2 * (quadratic c)^[m] w *
          deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w) w := by
    have hsecond_succ :
        (fun x => deriv (fun v => deriv ((quadratic c)^[m + 1]) v) x) =
          fun x =>
            2 * (deriv ((quadratic c)^[m]) x) ^ 2 +
              2 * (quadratic c)^[m] x *
                deriv (fun v => deriv ((quadratic c)^[m]) v) x := by
      funext x
      exact deriv_deriv_quadratic_iterate_succ_eq c m x
    have hF : HasDerivAt ((quadratic c)^[m]) (deriv ((quadratic c)^[m]) w) w :=
      (differentiable_quadratic_iterate c m w).hasDerivAt
    have hB : HasDerivAt (fun x => deriv ((quadratic c)^[m]) x)
        (deriv (fun v => deriv ((quadratic c)^[m]) v) w) w :=
      (analyticAt_quadratic_iterate c m w).deriv.differentiableAt.hasDerivAt
    have hC : HasDerivAt (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x)
        (deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w) w :=
      ((analyticAt_quadratic_iterate c m w).deriv).deriv.differentiableAt.hasDerivAt
    have hterm1 : HasDerivAt
        (fun x => 2 * (deriv ((quadratic c)^[m]) x) ^ 2)
        (4 * deriv ((quadratic c)^[m]) w *
          deriv (fun v => deriv ((quadratic c)^[m]) v) w) w := by
      have hsq := hB.mul hB
      convert hsq.const_mul 2 using 1
      · funext y
        simp [Pi.mul_apply, pow_two]
      · ring
    have hterm2 : HasDerivAt
        (fun x =>
          2 * (quadratic c)^[m] x *
            deriv (fun v => deriv ((quadratic c)^[m]) v) x)
        (2 * deriv ((quadratic c)^[m]) w *
            deriv (fun v => deriv ((quadratic c)^[m]) v) w +
          2 * (quadratic c)^[m] w *
            deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w) w := by
      have hprod := (hF.const_mul 2).mul hC
      convert hprod using 1
    rw [hsecond_succ]
    convert hterm1.add hterm2 using 1
    ring
  exact hD.deriv

/-- Third derivative of a fixed tail at the fixed point, in recursive closed form. -/
theorem hasDerivAt_deriv_deriv_iterate_fixed
    {c α : ℂ} (hfix : quadratic c α = α) (m : ℕ) :
    HasDerivAt (fun w => deriv (fun v => deriv ((quadratic c)^[m]) v) w)
      (fixedTailThirdCoeff ((2 : ℂ) * α) m) α := by
  induction m with
  | zero =>
      simpa [fixedTailThirdCoeff] using (hasDerivAt_const α (0 : ℂ))
  | succ m ih =>
      let lam : ℂ := (2 : ℂ) * α
      let B : ℂ := fixedTailSecondCoeff lam m
      let C : ℂ := fixedTailThirdCoeff lam m
      have hF : HasDerivAt ((quadratic c)^[m]) (lam ^ m) α := by
        have hbase : HasDerivAt ((quadratic c)^[m])
            (deriv ((quadratic c)^[m]) α) α :=
          (differentiable_quadratic_iterate c m α).hasDerivAt
        have hderiv : deriv ((quadratic c)^[m]) α = lam ^ m := by
          dsimp [lam]
          simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
            (n := 0) (by rfl) hfix m)
        simpa [hderiv] using hbase
      have hFval : (quadratic c)^[m] α = α := Function.iterate_fixed hfix m
      have hDval : deriv ((quadratic c)^[m]) α = lam ^ m := by
        dsimp [lam]
        simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
          (n := 0) (by rfl) hfix m)
      have hB : HasDerivAt (fun w => deriv ((quadratic c)^[m]) w) B α := by
        simpa [B, lam] using hasDerivAt_deriv_iterate_fixed hfix m
      have hBval : deriv (fun v => deriv ((quadratic c)^[m]) v) α = B := hB.deriv
      have hC : HasDerivAt
          (fun w => deriv (fun v => deriv ((quadratic c)^[m]) v) w) C α := by
        simpa [C, lam] using ih
      have hterm1 : HasDerivAt
          (fun w => 2 * (deriv ((quadratic c)^[m]) w) ^ 2)
          (4 * lam ^ m * B) α := by
        have hsq := hB.mul hB
        convert hsq.const_mul 2 using 1
        · funext y
          simp [Pi.mul_apply, pow_two]
        · rw [hDval]
          ring
      have hterm2 : HasDerivAt
          (fun w => 2 * (quadratic c)^[m] w *
            deriv (fun v => deriv ((quadratic c)^[m]) v) w)
          (2 * lam ^ m * B + lam * C) α := by
        have hprod := (hF.const_mul 2).mul hC
        convert hprod using 1
        · simp [B, C, lam, hFval, hBval]
      have hsum := hterm1.add hterm2
      have hsecond_succ :
          (fun w => deriv (fun v => deriv ((quadratic c)^[m + 1]) v) w) =
            fun w => 2 * (deriv ((quadratic c)^[m]) w) ^ 2 +
              2 * (quadratic c)^[m] w *
                deriv (fun v => deriv ((quadratic c)^[m]) v) w := by
        funext w
        exact deriv_deriv_quadratic_iterate_succ_eq c m w
      rw [hsecond_succ]
      convert hsum using 1
      · simp [fixedTailThirdCoeff, B, C, lam]
        ring

/-- Fourth derivative of a fixed tail at the fixed point, in recursive closed form. -/
theorem hasDerivAt_deriv_deriv_deriv_iterate_fixed
    {c α : ℂ} (hfix : quadratic c α = α) (m : ℕ) :
    HasDerivAt
      (fun w => deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w)
      (fixedTailFourthCoeff ((2 : ℂ) * α) m) α := by
  induction m with
  | zero =>
      simpa [fixedTailFourthCoeff] using (hasDerivAt_const α (0 : ℂ))
  | succ m ih =>
      let lam : ℂ := (2 : ℂ) * α
      let B : ℂ := fixedTailSecondCoeff lam m
      let C : ℂ := fixedTailThirdCoeff lam m
      let Q : ℂ := fixedTailFourthCoeff lam m
      have hF : HasDerivAt ((quadratic c)^[m]) (lam ^ m) α := by
        have hbase : HasDerivAt ((quadratic c)^[m])
            (deriv ((quadratic c)^[m]) α) α :=
          (differentiable_quadratic_iterate c m α).hasDerivAt
        have hderiv : deriv ((quadratic c)^[m]) α = lam ^ m := by
          dsimp [lam]
          simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
            (n := 0) (by rfl) hfix m)
        simpa [hderiv] using hbase
      have hFval : (quadratic c)^[m] α = α := Function.iterate_fixed hfix m
      have hDval : deriv ((quadratic c)^[m]) α = lam ^ m := by
        dsimp [lam]
        simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
          (n := 0) (by rfl) hfix m)
      have hB : HasDerivAt (fun w => deriv ((quadratic c)^[m]) w) B α := by
        simpa [B, lam] using hasDerivAt_deriv_iterate_fixed hfix m
      have hBval : deriv (fun v => deriv ((quadratic c)^[m]) v) α = B := hB.deriv
      have hC : HasDerivAt
          (fun w => deriv (fun v => deriv ((quadratic c)^[m]) v) w) C α := by
        simpa [C, lam] using hasDerivAt_deriv_deriv_iterate_fixed hfix m
      have hCval :
          deriv (fun w => deriv (fun v => deriv ((quadratic c)^[m]) v) w) α = C :=
        hC.deriv
      have hQ : HasDerivAt
          (fun w => deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w)
          Q α := by
        simpa [Q, lam] using ih
      have hterm1 : HasDerivAt
          (fun w =>
            6 * deriv ((quadratic c)^[m]) w *
              deriv (fun v => deriv ((quadratic c)^[m]) v) w)
          (6 * B ^ 2 + 6 * lam ^ m * C) α := by
        have hprod := (hB.const_mul 6).mul hC
        convert hprod using 1
        · rw [hDval, hBval]
          ring
      have hterm2 : HasDerivAt
          (fun w =>
            2 * (quadratic c)^[m] w *
              deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w)
          (2 * lam ^ m * C + lam * Q) α := by
        have hprod := (hF.const_mul 2).mul hQ
        convert hprod using 1
        · rw [hFval, hCval]
      have hsum := hterm1.add hterm2
      have hthird_succ :
          (fun w => deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m + 1]) v) x) w) =
            fun w =>
              6 * deriv ((quadratic c)^[m]) w *
                  deriv (fun v => deriv ((quadratic c)^[m]) v) w +
                2 * (quadratic c)^[m] w *
                  deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w := by
        funext w
        exact deriv_deriv_deriv_quadratic_iterate_succ_eq c m w
      rw [hthird_succ]
      convert hsum using 1
      · simp [fixedTailFourthCoeff, B, C, Q, lam]
        ring

/-- Equality form of `hasDerivAt_deriv_deriv_deriv_iterate_fixed`. -/
theorem deriv_deriv_deriv_deriv_iterate_fixed
    {c α : ℂ} (hfix : quadratic c α = α) (m : ℕ) :
    deriv
      (fun w => deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w) α =
      fixedTailFourthCoeff ((2 : ℂ) * α) m :=
  (hasDerivAt_deriv_deriv_deriv_iterate_fixed hfix m).deriv

/-- Norm bound for the fourth derivative of a fixed tail at the fixed point. -/
theorem norm_deriv_deriv_deriv_deriv_iterate_fixed_le
    {c α : ℂ} {C₂ C₃ C₄ : ℝ}
    (hfix : quadratic c α = α)
    (hL : 1 < ‖(2 : ℂ) * α‖)
    (hC₂nonneg : 0 ≤ C₂)
    (hC₂ : 2 ≤ C₂ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (hC₃nonneg : 0 ≤ C₃)
    (hC₃ : 6 * C₂ ≤ C₃ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ ^ 2 - 1))
    (hC₄nonneg : 0 ≤ C₄)
    (hC₄ : 8 * C₃ + 6 * C₂ ^ 2 ≤
      C₄ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ ^ 3 - 1))
    (m : ℕ) :
    ‖deriv
      (fun w => deriv (fun x => deriv (fun v => deriv ((quadratic c)^[m]) v) x) w) α‖ ≤
      C₄ * ‖(2 : ℂ) * α‖ ^ (4 * m) := by
  rw [deriv_deriv_deriv_deriv_iterate_fixed hfix m]
  exact norm_fixedTailFourthCoeff_le_mul_pow
    (lam := (2 : ℂ) * α) (C₂ := C₂) (C₃ := C₃) (C₄ := C₄)
    hL hC₂nonneg hC₂ hC₃nonneg hC₃ hC₄nonneg hC₄ m

/-- Second-derivative chain rule for an iterate split `n + m`. -/
theorem deriv_deriv_iterate_add_eq (c : ℂ) (n m : ℕ) (w : ℂ) :
    deriv (fun v => deriv ((quadratic c)^[n + m]) v) w =
      deriv (fun a => deriv ((quadratic c)^[m]) a) ((quadratic c)^[n] w) *
          (deriv ((quadratic c)^[n]) w) ^ 2 +
        deriv ((quadratic c)^[m]) ((quadratic c)^[n] w) *
          deriv (fun v => deriv ((quadratic c)^[n]) v) w := by
  have hderiv_add : (fun x => deriv ((quadratic c)^[n + m]) x) =
      fun x => deriv ((quadratic c)^[m]) ((quadratic c)^[n] x) *
        deriv ((quadratic c)^[n]) x := by
    funext x
    rw [deriv_quadratic_iterate_eq_orbitProduct_core,
      deriv_quadratic_iterate_eq_orbitProduct_core,
      deriv_quadratic_iterate_eq_orbitProduct_core]
    rw [deriv_iterate_quadratic_cocycle]
    ring
  have hA : HasDerivAt (fun a => deriv ((quadratic c)^[m]) a)
      (deriv (fun a => deriv ((quadratic c)^[m]) a) ((quadratic c)^[n] w))
      ((quadratic c)^[n] w) :=
    (analyticAt_quadratic_iterate c m ((quadratic c)^[n] w)).deriv.differentiableAt.hasDerivAt
  have hG : HasDerivAt ((quadratic c)^[n])
      (deriv ((quadratic c)^[n]) w) w :=
    (differentiable_quadratic_iterate c n w).hasDerivAt
  have hcomp : HasDerivAt
      (fun x => deriv ((quadratic c)^[m]) ((quadratic c)^[n] x))
      (deriv (fun a => deriv ((quadratic c)^[m]) a) ((quadratic c)^[n] w) *
        deriv ((quadratic c)^[n]) w) w :=
    hA.comp w hG
  have hB : HasDerivAt (fun x => deriv ((quadratic c)^[n]) x)
      (deriv (fun v => deriv ((quadratic c)^[n]) v) w) w :=
    (analyticAt_quadratic_iterate c n w).deriv.differentiableAt.hasDerivAt
  have hprod := hcomp.mul hB
  rw [hderiv_add]
  convert hprod.deriv using 1
  ring

/-- The third derivative of a fixed tail after a preperiodic hit.  This is the exact
chain-rule decomposition
`T'''(α) P^3 + 3 T''(α) P B + T'(α) C` for `T = f_c^[m]` and `P,B,C`
the first three derivative coefficients of the initial segment `f_c^[n]` at `z`. -/
theorem hasDerivAt_deriv_deriv_fixed_tail_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    HasDerivAt (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w)
      (fixedTailThirdCoeff ((2 : ℂ) * α) m * (deriv ((quadratic c)^[n]) z) ^ 3 +
        3 * fixedTailSecondCoeff ((2 : ℂ) * α) m *
          deriv ((quadratic c)^[n]) z *
          deriv (fun w => deriv ((quadratic c)^[n]) w) z +
        ((2 : ℂ) * α) ^ m *
          deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) z) z := by
  let lam : ℂ := (2 : ℂ) * α
  let P : ℂ := deriv ((quadratic c)^[n]) z
  let B : ℂ := deriv (fun w => deriv ((quadratic c)^[n]) w) z
  let C : ℂ := deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) z
  let A₂ : ℂ := fixedTailSecondCoeff lam m
  let A₃ : ℂ := fixedTailThirdCoeff lam m
  have hG : HasDerivAt ((quadratic c)^[n]) P z := by
    simpa [P] using (differentiable_quadratic_iterate c n z).hasDerivAt
  have hP : HasDerivAt (fun w => deriv ((quadratic c)^[n]) w) B z := by
    simpa [B] using (analyticAt_quadratic_iterate c n z).deriv.differentiableAt.hasDerivAt
  have hC : HasDerivAt
      (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) C z := by
    simpa [C] using (((analyticAt_quadratic_iterate c n z).deriv).deriv.differentiableAt.hasDerivAt)
  have hA₂ : HasDerivAt (fun a => deriv ((quadratic c)^[m]) a) A₂ α := by
    simpa [A₂, lam] using hasDerivAt_deriv_iterate_fixed hfix m
  have hA₂at : HasDerivAt (fun a => deriv ((quadratic c)^[m]) a) A₂ ((quadratic c)^[n] z) := by
    rwa [hhit]
  have hA₂val : deriv (fun a => deriv ((quadratic c)^[m]) a) α = A₂ := hA₂.deriv
  have hA₃ : HasDerivAt
      (fun a => deriv (fun v => deriv ((quadratic c)^[m]) v) a) A₃ α := by
    simpa [A₃, lam] using hasDerivAt_deriv_deriv_iterate_fixed hfix m
  have hA₃at : HasDerivAt
      (fun a => deriv (fun v => deriv ((quadratic c)^[m]) v) a) A₃
      ((quadratic c)^[n] z) := by
    rwa [hhit]
  have hTailDerivVal : deriv ((quadratic c)^[m]) α = lam ^ m := by
    dsimp [lam]
    simpa using (deriv_fixed_tail_of_iterate_eq_fixed (c := c) (z := α) (α := α)
      (n := 0) (by rfl) hfix m)
  have hTailDerivVal_at :
      deriv ((quadratic c)^[m]) ((quadratic c)^[n] z) = lam ^ m := by
    rwa [hhit]
  have hcompA₃ : HasDerivAt
      (fun w => deriv (fun v => deriv ((quadratic c)^[m]) v) ((quadratic c)^[n] w))
      (A₃ * P) z :=
    hA₃at.comp z hG
  have hP2 : HasDerivAt (fun w => (deriv ((quadratic c)^[n]) w) ^ 2)
      (2 * P * B) z := by
    have hsq := hP.mul hP
    convert hsq using 1
    · funext y
      simp [Pi.mul_apply, pow_two]
    · simp [P, B]
      ring
  have hterm1 : HasDerivAt
      (fun w =>
        deriv (fun a => deriv ((quadratic c)^[m]) a) ((quadratic c)^[n] w) *
          (deriv ((quadratic c)^[n]) w) ^ 2)
      (A₃ * P ^ 3 + 2 * A₂ * P * B) z := by
    have hprod := hcompA₃.mul hP2
    convert hprod using 1
    · rw [hhit, hA₂val]
      ring
  have hcompA₂ : HasDerivAt
      (fun w => deriv ((quadratic c)^[m]) ((quadratic c)^[n] w))
      (A₂ * P) z :=
    hA₂at.comp z hG
  have hterm2 : HasDerivAt
      (fun w =>
        deriv ((quadratic c)^[m]) ((quadratic c)^[n] w) *
          deriv (fun v => deriv ((quadratic c)^[n]) v) w)
      (A₂ * P * B + lam ^ m * C) z := by
    have hprod := hcompA₂.mul hC
    convert hprod using 1
    · rw [hTailDerivVal_at]
  have hsum := hterm1.add hterm2
  have hsecond_add :
      (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) =
        fun w =>
          deriv (fun a => deriv ((quadratic c)^[m]) a) ((quadratic c)^[n] w) *
              (deriv ((quadratic c)^[n]) w) ^ 2 +
            deriv ((quadratic c)^[m]) ((quadratic c)^[n] w) *
              deriv (fun v => deriv ((quadratic c)^[n]) v) w := by
    funext w
    exact deriv_deriv_iterate_add_eq c n m w
  rw [hsecond_add]
  convert hsum using 1
  · simp [A₂, A₃, P, B, C, lam]
    ring

/-- Equality form of `hasDerivAt_deriv_deriv_fixed_tail_of_iterate_eq_fixed`. -/
theorem deriv_deriv_deriv_fixed_tail_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) z =
      fixedTailThirdCoeff ((2 : ℂ) * α) m * (deriv ((quadratic c)^[n]) z) ^ 3 +
        3 * fixedTailSecondCoeff ((2 : ℂ) * α) m *
          deriv ((quadratic c)^[n]) z *
          deriv (fun w => deriv ((quadratic c)^[n]) w) z +
        ((2 : ℂ) * α) ^ m *
          deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) z :=
  (hasDerivAt_deriv_deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m).deriv

/-- Norm bound for the exact third-derivative fixed-tail decomposition after a preperiodic hit. -/
theorem norm_deriv_deriv_deriv_fixed_tail_of_iterate_eq_fixed_le
    {c z α : ℂ} {n : ℕ} {C₂ C₃ : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hL : 1 < ‖(2 : ℂ) * α‖)
    (hC₂nonneg : 0 ≤ C₂)
    (hC₂ : 2 ≤ C₂ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (hC₃nonneg : 0 ≤ C₃)
    (hC₃ : 6 * C₂ ≤ C₃ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ ^ 2 - 1))
    (m : ℕ) :
    ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) z‖ ≤
      C₃ * ‖(2 : ℂ) * α‖ ^ (3 * m) * ‖deriv ((quadratic c)^[n]) z‖ ^ 3 +
        3 * C₂ * ‖(2 : ℂ) * α‖ ^ (2 * m) *
          ‖deriv ((quadratic c)^[n]) z‖ *
          ‖deriv (fun w => deriv ((quadratic c)^[n]) w) z‖ +
        ‖(2 : ℂ) * α‖ ^ m *
          ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) z‖ := by
  rw [deriv_deriv_deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m]
  let lam : ℂ := (2 : ℂ) * α
  let P : ℂ := deriv ((quadratic c)^[n]) z
  let B : ℂ := deriv (fun w => deriv ((quadratic c)^[n]) w) z
  let C : ℂ := deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) z
  let A₂ : ℂ := fixedTailSecondCoeff lam m
  let A₃ : ℂ := fixedTailThirdCoeff lam m
  have hA₂ := norm_fixedTailSecondCoeff_le_mul_pow
    (lam := lam) (C := C₂) hC₂nonneg (by simpa [lam] using hC₂) m
  have hA₃ := norm_fixedTailThirdCoeff_le_mul_pow
    (lam := lam) (C₂ := C₂) (C₃ := C₃)
    (by simpa [lam] using hL) hC₂nonneg (by simpa [lam] using hC₂)
    hC₃nonneg (by simpa [lam] using hC₃) m
  have htermA : ‖A₃‖ * ‖P‖ ^ 3 ≤
      C₃ * ‖lam‖ ^ (3 * m) * ‖P‖ ^ 3 := by
    exact mul_le_mul_of_nonneg_right hA₃ (pow_nonneg (norm_nonneg _) _)
  have htermB : 3 * ‖A₂‖ * ‖P‖ * ‖B‖ ≤
      3 * C₂ * ‖lam‖ ^ (2 * m) * ‖P‖ * ‖B‖ := by
    calc
      3 * ‖A₂‖ * ‖P‖ * ‖B‖ = ‖A₂‖ * (3 * ‖P‖ * ‖B‖) := by ring
      _ ≤ (C₂ * ‖lam‖ ^ (2 * m)) * (3 * ‖P‖ * ‖B‖) := by
            exact mul_le_mul_of_nonneg_right hA₂ (by positivity)
      _ = 3 * C₂ * ‖lam‖ ^ (2 * m) * ‖P‖ * ‖B‖ := by ring
  calc
    ‖A₃ * P ^ 3 + 3 * A₂ * P * B + lam ^ m * C‖
        ≤ (‖A₃ * P ^ 3‖ + ‖3 * A₂ * P * B‖) + ‖lam ^ m * C‖ := by
          calc
            ‖A₃ * P ^ 3 + 3 * A₂ * P * B + lam ^ m * C‖
                ≤ ‖A₃ * P ^ 3 + 3 * A₂ * P * B‖ + ‖lam ^ m * C‖ :=
                  norm_add_le (A₃ * P ^ 3 + 3 * A₂ * P * B) (lam ^ m * C)
            _ ≤ (‖A₃ * P ^ 3‖ + ‖3 * A₂ * P * B‖) + ‖lam ^ m * C‖ := by
                  simpa only [add_assoc] using
                    add_le_add (norm_add_le (A₃ * P ^ 3) (3 * A₂ * P * B))
                      (le_refl ‖lam ^ m * C‖)
    _ = ‖A₃‖ * ‖P‖ ^ 3 + 3 * ‖A₂‖ * ‖P‖ * ‖B‖ +
          ‖lam‖ ^ m * ‖C‖ := by
          rw [norm_mul, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
            norm_mul, norm_pow]
    _ ≤ C₃ * ‖lam‖ ^ (3 * m) * ‖P‖ ^ 3 +
          3 * C₂ * ‖lam‖ ^ (2 * m) * ‖P‖ * ‖B‖ +
          ‖lam‖ ^ m * ‖C‖ := by
          exact add_le_add (add_le_add htermA htermB) le_rfl
    _ = C₃ * ‖(2 : ℂ) * α‖ ^ (3 * m) * ‖deriv ((quadratic c)^[n]) z‖ ^ 3 +
          3 * C₂ * ‖(2 : ℂ) * α‖ ^ (2 * m) *
            ‖deriv ((quadratic c)^[n]) z‖ *
            ‖deriv (fun w => deriv ((quadratic c)^[n]) w) z‖ +
          ‖(2 : ℂ) * α‖ ^ m *
            ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) z‖ := by
          simp [lam, P, B, C]

/-- A noncritical forward hit to a repelling fixed anchor gives unbounded derivative growth along
the tail iterates `n + m`.  This is the quantitative large-derivative input for the Newton bridge. -/
theorem tendsto_norm_deriv_fixed_tail_atTop
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) :
    Tendsto (fun m : ℕ => ‖deriv ((quadratic c)^[n + m]) z‖) atTop atTop := by
  have hpow : Tendsto (fun m : ℕ => ‖((2 : ℂ) * α) ^ m‖) atTop atTop := by
    simpa [norm_pow] using tendsto_pow_atTop_atTop_of_one_lt hrep
  have hCpos : 0 < ‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ :=
    norm_pos_iff.mpr hinit
  have hmul := Filter.Tendsto.const_mul_atTop hCpos hpow
  refine hmul.congr' ?_
  filter_upwards with m
  rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m, norm_mul]

/-- Tail inverse multipliers become arbitrarily small after a noncritical hit to a repelling fixed
anchor. -/
theorem exists_tail_deriv_inv_norm_lt_of_repelling_hit
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ,
      deriv ((quadratic c)^[n + m]) z ≠ 0 ∧
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ < ε := by
  have htend := tendsto_norm_deriv_fixed_tail_atTop hhit hfix hinit hrep
  have hev : ∀ᶠ m : ℕ in atTop,
      ε⁻¹ < ‖deriv ((quadratic c)^[n + m]) z‖ :=
    htend.eventually_gt_atTop ε⁻¹
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hlarge : ε⁻¹ < ‖deriv ((quadratic c)^[n + N]) z‖ := hN N le_rfl
  have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
  have hnormpos : 0 < ‖deriv ((quadratic c)^[n + N]) z‖ := lt_trans hεinv hlarge
  have hderiv_ne : deriv ((quadratic c)^[n + N]) z ≠ 0 := norm_pos_iff.mp hnormpos
  refine ⟨N, hderiv_ne, ?_⟩
  rw [norm_inv]
  exact (inv_lt_comm₀ hnormpos hε).2 hlarge

/-- For the Newton correction with inverse derivative coefficient, the center displacement after a
noncritical hit to a repelling fixed anchor can be made arbitrarily small along the fixed tail. -/
theorem exists_tail_newton_center_displacement_lt_of_repelling_hit
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) {η : ℝ} (hη : 0 < η) :
    ∃ m : ℕ,
      deriv ((quadratic c)^[n + m]) z ≠ 0 ∧
      dist (z - (deriv ((quadratic c)^[n + m]) z)⁻¹ *
        ((quadratic c)^[n + m] z - z)) z < η := by
  by_cases hαz : α = z
  · obtain ⟨m, hderiv_ne, _hinv⟩ :=
      exists_tail_deriv_inv_norm_lt_of_repelling_hit hhit hfix hinit hrep
        (show (0 : ℝ) < 1 by norm_num)
    refine ⟨m, hderiv_ne, ?_⟩
    rw [iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m, hαz, sub_self, mul_zero,
      sub_zero, dist_self]
    exact hη
  · have hdistpos : 0 < ‖α - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hαz)
    have hε : 0 < η / ‖α - z‖ := div_pos hη hdistpos
    obtain ⟨m, hderiv_ne, hinvlt⟩ :=
      exists_tail_deriv_inv_norm_lt_of_repelling_hit hhit hfix hinit hrep hε
    refine ⟨m, hderiv_ne, ?_⟩
    rw [iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m]
    rw [dist_eq_norm]
    have hnorm : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹ * (α - z)‖ < η := by
      rw [norm_mul]
      have hmul : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖α - z‖ <
          (η / ‖α - z‖) * ‖α - z‖ :=
        mul_lt_mul_of_pos_right hinvlt hdistpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hdistpos)] at hmul
    rw [show z - (deriv ((quadratic c)^[n + m]) z)⁻¹ * (α - z) - z =
        -((deriv ((quadratic c)^[n + m]) z)⁻¹ * (α - z)) by ring, norm_neg]
    exact hnorm

/-- Along a repelling fixed tail, the exact Newton center-size factor
`‖(F_q' z)⁻¹‖ * ‖α - z‖` can be made arbitrarily small.  This is the
quantitative form needed to compare the Newton center displacement with a chosen contraction
radius. -/
theorem exists_tail_inv_deriv_mul_fixed_dist_lt_of_repelling_hit
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) {η : ℝ} (hη : 0 < η) :
    ∃ m : ℕ,
      deriv ((quadratic c)^[n + m]) z ≠ 0 ∧
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖α - z‖ < η := by
  by_cases hαz : α = z
  · obtain ⟨m, hderiv_ne, _hinv⟩ :=
      exists_tail_deriv_inv_norm_lt_of_repelling_hit hhit hfix hinit hrep
        (show (0 : ℝ) < 1 by norm_num)
    refine ⟨m, hderiv_ne, ?_⟩
    rw [hαz, sub_self, norm_zero, mul_zero]
    exact hη
  · have hdistpos : 0 < ‖α - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hαz)
    have hε : 0 < η / ‖α - z‖ := div_pos hη hdistpos
    obtain ⟨m, hderiv_ne, hinvlt⟩ :=
      exists_tail_deriv_inv_norm_lt_of_repelling_hit hhit hfix hinit hrep hε
    refine ⟨m, hderiv_ne, ?_⟩
    have hmul : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖α - z‖ <
        (η / ‖α - z‖) * ‖α - z‖ :=
      mul_lt_mul_of_pos_right hinvlt hdistpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hdistpos)] at hmul

/-- Along a noncritical hit to a repelling fixed anchor, the exact Newton center-size factor is
eventually below any positive threshold.  This is the synchronization form used with eventual
Newton-window estimates. -/
theorem eventually_tail_inv_deriv_mul_fixed_dist_lt_of_repelling_hit
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      deriv ((quadratic c)^[n + m]) z ≠ 0 ∧
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖α - z‖ < η := by
  by_cases hαz : α = z
  · have htend := tendsto_norm_deriv_fixed_tail_atTop hhit hfix hinit hrep
    have hev : ∀ᶠ m : ℕ in atTop,
        (1 : ℝ) < ‖deriv ((quadratic c)^[n + m]) z‖ :=
      htend.eventually_gt_atTop 1
    filter_upwards [hev] with m hm
    have hnormpos : 0 < ‖deriv ((quadratic c)^[n + m]) z‖ :=
      lt_trans zero_lt_one hm
    refine ⟨norm_pos_iff.mp hnormpos, ?_⟩
    rw [hαz, sub_self, norm_zero, mul_zero]
    exact hη
  · have hdistpos : 0 < ‖α - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hαz)
    have hε : 0 < η / ‖α - z‖ := div_pos hη hdistpos
    have htend := tendsto_norm_deriv_fixed_tail_atTop hhit hfix hinit hrep
    have hev : ∀ᶠ m : ℕ in atTop,
        (η / ‖α - z‖)⁻¹ < ‖deriv ((quadratic c)^[n + m]) z‖ :=
      htend.eventually_gt_atTop (η / ‖α - z‖)⁻¹
    filter_upwards [hev] with m hm
    have hεinv : 0 < (η / ‖α - z‖)⁻¹ := inv_pos.mpr hε
    have hnormpos : 0 < ‖deriv ((quadratic c)^[n + m]) z‖ :=
      lt_trans hεinv hm
    have hderiv_ne : deriv ((quadratic c)^[n + m]) z ≠ 0 :=
      norm_pos_iff.mp hnormpos
    have hinvlt : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ < η / ‖α - z‖ := by
      rw [norm_inv]
      exact (inv_lt_comm₀ hnormpos hε).2 hm
    refine ⟨hderiv_ne, ?_⟩
    have hmul : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖α - z‖ <
        (η / ‖α - z‖) * ‖α - z‖ :=
      mul_lt_mul_of_pos_right hinvlt hdistpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hdistpos)] at hmul

/-- Along a noncritical hit to a repelling fixed anchor, one tail iterate makes both the Newton
center displacement and the Newton derivative at the center arbitrarily small. -/
theorem exists_tail_newton_center_deriv_lt_of_repelling_hit
    {c z α : ℂ} {n : ℕ} (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) {η κ : ℝ} (hη : 0 < η) (hκ : 0 < κ) :
    ∃ m : ℕ,
      deriv ((quadratic c)^[n + m]) z ≠ 0 ∧
      dist (z - (deriv ((quadratic c)^[n + m]) z)⁻¹ *
        ((quadratic c)^[n + m] z - z)) z < η ∧
      ‖deriv (fun w => w - (deriv ((quadratic c)^[n + m]) z)⁻¹ *
        ((quadratic c)^[n + m] w - w)) z‖ < κ := by
  by_cases hαz : α = z
  · obtain ⟨m, hderiv_ne, hinvlt⟩ :=
      exists_tail_deriv_inv_norm_lt_of_repelling_hit hhit hfix hinit hrep hκ
    refine ⟨m, hderiv_ne, ?_, ?_⟩
    · rw [iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m, hαz, sub_self, mul_zero,
        sub_zero, dist_self]
      exact hη
    · rw [deriv_newton_quadratic_iterate_inv_deriv hderiv_ne]
      exact hinvlt
  · have hdistpos : 0 < ‖α - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hαz)
    have hηdiv : 0 < η / ‖α - z‖ := div_pos hη hdistpos
    have hε : 0 < min κ (η / ‖α - z‖) := lt_min hκ hηdiv
    obtain ⟨m, hderiv_ne, hinvlt⟩ :=
      exists_tail_deriv_inv_norm_lt_of_repelling_hit hhit hfix hinit hrep hε
    have hinvκ : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ < κ :=
      lt_of_lt_of_le hinvlt (min_le_left _ _)
    have hinvη : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ < η / ‖α - z‖ :=
      lt_of_lt_of_le hinvlt (min_le_right _ _)
    refine ⟨m, hderiv_ne, ?_, ?_⟩
    · rw [iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m]
      rw [dist_eq_norm]
      have hnorm : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹ * (α - z)‖ < η := by
        rw [norm_mul]
        have hmul : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖α - z‖ <
            (η / ‖α - z‖) * ‖α - z‖ :=
          mul_lt_mul_of_pos_right hinvη hdistpos
        rwa [div_mul_cancel₀ _ (ne_of_gt hdistpos)] at hmul
      rw [show z - (deriv ((quadratic c)^[n + m]) z)⁻¹ * (α - z) - z =
          -((deriv ((quadratic c)^[n + m]) z)⁻¹ * (α - z)) by ring, norm_neg]
      exact hnorm
    · rw [deriv_newton_quadratic_iterate_inv_deriv hderiv_ne]
      exact hinvκ

/-- Newton-contraction form of the local periodic-point producer.  If the Newton correction for
`f_c^[q] - id` contracts a closed ball around `a`, then `f_c^[q]` has a fixed point in that ball. -/
theorem exists_positive_periodic_point_of_newton_contraction_closedBall
    {c a A : ℂ} {q : ℕ} {r : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hA : A ≠ 0)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hcenter :
      dist (a - A * ((quadratic c)^[q] a - a)) a + (K : ℝ) * r ≤ r)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r,
      ‖deriv (fun w => w - A * ((quadratic c)^[q] w - w)) z‖ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.closedBall a r, ∃ q' : ℕ,
      1 ≤ q' ∧ (quadratic c)^[q'] y = y := by
  let T : ℂ → ℂ := fun w => w - A * ((quadratic c)^[q] w - w)
  obtain ⟨y, hy, hfix⟩ :=
    exists_fixed_point_of_deriv_bound_self_map_closedBall
      (a := a) (r := r) (T := T) (K := K) hr hK (by simpa [T] using hcenter)
      (fun z hz => by
        simpa [T] using
          hasDerivWithinAt_newton_quadratic_iterate c A q (Metric.closedBall a r) z)
      (by
        intro z hz
        simpa [T] using hderiv_bound z hz)
  refine ⟨y, hy, q, hq, ?_⟩
  have hmul : A * ((quadratic c)^[q] y - y) = 0 := by
    have hsub : y - A * ((quadratic c)^[q] y - y) - y = 0 := sub_eq_zero.mpr hfix
    linear_combination -hsub
  have hdiff : (quadratic c)^[q] y - y = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left hA
  exact sub_eq_zero.mp hdiff

/-- Target-ball version of `exists_positive_periodic_point_of_newton_contraction_closedBall`. -/
theorem exists_positive_periodic_point_mem_ball_of_newton_contraction
    {c ζ a A : ℂ} {q : ℕ} {R r : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hA : A ≠ 0)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hclosed : Metric.closedBall a r ⊆ Metric.ball ζ R)
    (hcenter :
      dist (a - A * ((quadratic c)^[q] a - a)) a + (K : ℝ) * r ≤ r)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r,
      ‖deriv (fun w => w - A * ((quadratic c)^[q] w - w)) z‖ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q' : ℕ,
      1 ≤ q' ∧ (quadratic c)^[q'] y = y := by
  obtain ⟨y, hyclosed, q', hq', hper⟩ :=
    exists_positive_periodic_point_of_newton_contraction_closedBall
      (c := c) (a := a) (A := A) (q := q) (r := r) (K := K)
      hq hA hr hK hcenter hderiv_bound
  exact ⟨y, hclosed hyclosed, q', hq', hper⟩

/-- Analytic radius package for the Newton correction.  If the Newton derivative is already
strictly below `K` at the center, then there is a target-contained closed ball on which the
derivative is bounded by `K`; if the center displacement also fits that radius, the Newton
contraction theorem produces a positive periodic point in the target ball. -/
theorem exists_newton_contraction_radius_package
    {c ζ a A : ℂ} {q : ℕ} {R : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hA : A ≠ 0)
    (haR : a ∈ Metric.ball ζ R)
    (hK : K < 1)
    (hderiv_center :
      ‖deriv (fun w => w - A * ((quadratic c)^[q] w - w)) a‖ < (K : ℝ)) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ Metric.ball ζ R ∧
      (∀ y ∈ Metric.closedBall a r,
        ‖deriv (fun w => w - A * ((quadratic c)^[q] w - w)) y‖ ≤ (K : ℝ)) ∧
      (dist (a - A * ((quadratic c)^[q] a - a)) a ≤ (1 - (K : ℝ)) * r →
        ∃ y ∈ Metric.ball ζ R, ∃ q' : ℕ,
          1 ≤ q' ∧ (quadratic c)^[q'] y = y) := by
  let T : ℂ → ℂ := fun w => w - A * ((quadratic c)^[q] w - w)
  have hTan : AnalyticAt ℂ T a := by
    simpa [T] using analyticAt_newton_quadratic_iterate c A q a
  obtain ⟨rD, hrD, hD⟩ :=
    exists_closedBall_deriv_bound_of_analyticAt hTan (by simpa [T] using hderiv_center)
  obtain ⟨rT, hrT, hTsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball a haR
  let r : ℝ := min rD (rT / 2)
  have hr : 0 < r := lt_min hrD (by linarith)
  have hrDle : r ≤ rD := min_le_left _ _
  have hrTlt : r < rT := by
    have hle : r ≤ rT / 2 := min_le_right _ _
    linarith
  have hclosed : Metric.closedBall a r ⊆ Metric.ball ζ R := by
    intro y hy
    exact hTsub (Metric.closedBall_subset_ball hrTlt hy)
  have hderiv_bound : ∀ y ∈ Metric.closedBall a r, ‖deriv T y‖ ≤ (K : ℝ) := by
    intro y hy
    have hyD : y ∈ Metric.closedBall a rD := by
      rw [Metric.mem_closedBall] at hy ⊢
      exact le_trans hy hrDle
    exact (hD y hyD).2
  refine ⟨r, hr, hclosed, by simpa [T] using hderiv_bound, ?_⟩
  intro hcenter_small
  exact exists_positive_periodic_point_mem_ball_of_newton_contraction
    (c := c) (ζ := ζ) (a := a) (A := A) (q := q) (R := R) (r := r) (K := K)
    hq hA (le_of_lt hr) hK hclosed
    (center_add_mul_radius_le_of_le_one_sub_mul hK hcenter_small)
    (by simpa [T] using hderiv_bound)

/-- Derivative of the Newton correction at an arbitrary point when the coefficient is the inverse
of the iterate derivative at the base point. -/
theorem deriv_newton_quadratic_iterate_inv_deriv_at
    {c : ℂ} {q : ℕ} {z y : ℂ}
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0) :
    deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ *
      ((quadratic c)^[q] w - w)) y =
      (deriv ((quadratic c)^[q]) z)⁻¹ *
        (deriv ((quadratic c)^[q]) z - deriv ((quadratic c)^[q]) y + 1) := by
  rw [deriv_newton_quadratic_iterate]
  field_simp [hderiv]
  ring

/-- Marty blow-up supplies a frontier-ball Newton base point whose center displacement and center
Newton derivative are both quantitatively small.  This is the combined input needed before choosing
a contraction radius. -/
theorem exists_positive_iterate_newton_center_and_deriv_lt_on_frontier_ball
    {c z₀ : ℂ} {R ρ M η κ : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < R)
    (hMone : 1 < M)
    (hfit : ∀ z ∈ ball z₀ R, (‖z‖ + 1) / M < η)
    (hinv : M⁻¹ < κ) :
    ∃ q z, 1 ≤ q ∧ z ∈ ball z₀ R ∧
      deriv ((quadratic c)^[q]) z ≠ 0 ∧
      dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
        ((quadratic c)^[q] z - z)) z < η ∧
      ‖deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ *
        ((quadratic c)^[q] w - w)) z‖ < κ := by
  obtain ⟨q, z, hz, hσ⟩ :=
    exists_sphericalDeriv_gt_iterates_on_frontier_ball
      (c := c) (z₀ := z₀) (R := R) (ρ := ρ) (M := M) hzfront hρ0 hρR
  have hcenter :=
    newton_center_displacement_lt_of_sphericalDeriv_gt
      (F := (quadratic c)^[q]) (z := z) (M := M) (η := η)
      (lt_trans zero_lt_one hMone) hσ (hfit z hz)
  have hnorm_gt : M < ‖deriv ((quadratic c)^[q]) z‖ :=
    lt_of_lt_of_le hσ (sphericalDeriv_le_norm_deriv _ _)
  have hq : 1 ≤ q := by
    cases q with
    | zero =>
        simp at hnorm_gt
        linarith
    | succ q =>
        exact Nat.succ_le_succ (Nat.zero_le q)
  have hMpos : 0 < M := lt_trans zero_lt_one hMone
  have hderiv_norm_pos : 0 < ‖deriv ((quadratic c)^[q]) z‖ := lt_trans hMpos hnorm_gt
  have hinv_norm : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ < κ := by
    rw [norm_inv]
    have hlt : ‖deriv ((quadratic c)^[q]) z‖⁻¹ < M⁻¹ :=
      (inv_lt_inv₀ hderiv_norm_pos hMpos).2 hnorm_gt
    exact lt_trans hlt hinv
  refine ⟨q, z, hq, hz, hcenter.1, hcenter.2, ?_⟩
  rw [deriv_newton_quadratic_iterate_inv_deriv hcenter.1]
  exact hinv_norm

/-- Explicit version of
`exists_positive_iterate_newton_center_and_deriv_lt_on_frontier_ball`: for any requested center scale
and center-Newton-derivative scale, Marty blow-up supplies a positive iterate and base point meeting
both. -/
theorem exists_positive_iterate_newton_center_and_deriv_lt_on_frontier_ball_explicit
    {c z₀ : ℂ} {R ρ η κ : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < R)
    (hη : 0 < η) (hκ : 0 < κ) :
    ∃ q z, 1 ≤ q ∧ z ∈ ball z₀ R ∧
      deriv ((quadratic c)^[q]) z ≠ 0 ∧
      dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
        ((quadratic c)^[q] z - z)) z < η ∧
      ‖deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ *
        ((quadratic c)^[q] w - w)) z‖ < κ := by
  let B : ℝ := ‖z₀‖ + R + 1
  let M : ℝ := (B + 1) / η + κ⁻¹ + 3
  have hRpos : 0 < R := lt_trans hρ0 hρR
  have hBpos : 0 < B + 1 := by
    dsimp [B]
    nlinarith [norm_nonneg z₀]
  have hMpos : 0 < M := by
    dsimp [M]
    have hdivpos : 0 < (B + 1) / η := div_pos hBpos hη
    have hkinvpos : 0 < κ⁻¹ := inv_pos.mpr hκ
    linarith
  have hMone : 1 < M := by
    dsimp [M]
    have hdivpos : 0 < (B + 1) / η := div_pos hBpos hη
    have hkinvpos : 0 < κ⁻¹ := inv_pos.mpr hκ
    linarith
  have hBMlt : (B + 1) / M < η := by
    rw [div_lt_iff₀ hMpos]
    have hgt : (B + 1) / η < M := by
      dsimp [M]
      have hkinvpos : 0 < κ⁻¹ := inv_pos.mpr hκ
      linarith
    have hcleared : B + 1 < M * η := by
      rwa [div_lt_iff₀ hη] at hgt
    linarith
  have hMinv : M⁻¹ < κ := by
    have hgt : κ⁻¹ < M := by
      dsimp [M]
      have hdivpos : 0 < (B + 1) / η := div_pos hBpos hη
      linarith
    exact (inv_lt_comm₀ hMpos hκ).2 hgt
  apply exists_positive_iterate_newton_center_and_deriv_lt_on_frontier_ball
    (c := c) (z₀ := z₀) (R := R) (ρ := ρ) (M := M) (η := η) (κ := κ)
    hzfront hρ0 hρR hMone ?_ hMinv
  intro z hz
  have hzdist : dist z z₀ < R := by
    simpa [Metric.mem_ball] using hz
  have hnorm : ‖z‖ < ‖z₀‖ + R := by
    calc
      ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ = dist z z₀ + ‖z₀‖ := by rw [dist_eq_norm]
      _ < R + ‖z₀‖ := by linarith
      _ = ‖z₀‖ + R := by ring
  have hnum : ‖z‖ + 1 < B + 1 := by
    dsimp [B]
    linarith
  exact lt_trans (div_lt_div_of_pos_right hnum hMpos) hBMlt

/-- Marty blow-up plus the qualitative analytic-radius package.  In every frontier ball, and at
every requested Newton-center scale, there is a positive iterate/base point with center displacement
below that scale and with an analytic contraction-radius package for Newton's map.  The remaining
obligation is the single synchronization inequality comparing that already-small center displacement
to the returned radius. -/
theorem exists_positive_iterate_newton_radius_package_on_frontier_ball
    {c z₀ : ℂ} {R ρ η : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < R)
    (hη : 0 < η) :
    ∃ q z r, 1 ≤ q ∧ z ∈ ball z₀ R ∧
      deriv ((quadratic c)^[q]) z ≠ 0 ∧ 0 < r ∧
      Metric.closedBall z r ⊆ Metric.ball z₀ R ∧
      dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
        ((quadratic c)^[q] z - z)) z < η ∧
      (∀ y ∈ Metric.closedBall z r,
        ‖deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ *
          ((quadratic c)^[q] w - w)) y‖ ≤ ((1 / 2 : NNReal) : ℝ)) ∧
      (dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
          ((quadratic c)^[q] z - z)) z ≤
          (1 - ((1 / 2 : NNReal) : ℝ)) * r →
        ∃ y ∈ Metric.ball z₀ R, ∃ q' : ℕ,
          1 ≤ q' ∧ (quadratic c)^[q'] y = y) := by
  have hhalf_pos : (0 : ℝ) < ((1 / 2 : NNReal) : ℝ) := by norm_num
  obtain ⟨q, z, hq, hz, hderiv_ne, hcenter_lt, hderiv_center⟩ :=
    exists_positive_iterate_newton_center_and_deriv_lt_on_frontier_ball_explicit
      (c := c) (z₀ := z₀) (R := R) (ρ := ρ) (η := η)
      (κ := ((1 / 2 : NNReal) : ℝ))
      hzfront hρ0 hρR hη hhalf_pos
  have hK : (1 / 2 : NNReal) < 1 := by norm_num
  obtain ⟨r, hr, hclosed, hderiv_bound, hperiodic⟩ :=
    exists_newton_contraction_radius_package
      (c := c) (ζ := z₀) (a := z)
      (A := (deriv ((quadratic c)^[q]) z)⁻¹) (q := q) (R := R)
      (K := (1 / 2 : NNReal))
      hq (inv_ne_zero hderiv_ne) hz hK hderiv_center
  exact ⟨q, z, r, hq, hz, hderiv_ne, hr, hclosed, hcenter_lt, hderiv_bound, hperiodic⟩

/-- A derivative-variation bound for the iterate gives a derivative bound for its Newton
correction.  This is the algebraic estimate behind the chosen-radius Newton route. -/
theorem norm_deriv_newton_quadratic_iterate_inv_deriv_at_le
    {c : ℂ} {q : ℕ} {z y : ℂ} {μ : ℝ}
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0)
    (hvar : ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ) :
    ‖deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ *
      ((quadratic c)^[q] w - w)) y‖ ≤
      ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) := by
  rw [deriv_newton_quadratic_iterate_inv_deriv_at hderiv, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc
    ‖deriv ((quadratic c)^[q]) z - deriv ((quadratic c)^[q]) y + 1‖
        ≤ ‖deriv ((quadratic c)^[q]) z - deriv ((quadratic c)^[q]) y‖ + ‖(1 : ℂ)‖ :=
          norm_add_le _ _
    _ = ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ + 1 := by
          rw [norm_one]
          congr 1
          rw [← norm_neg (deriv ((quadratic c)^[q]) z - deriv ((quadratic c)^[q]) y)]
          ring_nf
    _ ≤ μ + 1 := by linarith

/-- Closed-ball form of `norm_deriv_newton_quadratic_iterate_inv_deriv_at_le`. -/
theorem newton_deriv_bound_of_iterate_deriv_variation_closedBall
    {c z : ℂ} {q : ℕ} {r μ : ℝ} {K : NNReal}
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0)
    (hvar : ∀ y ∈ Metric.closedBall z r,
      ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ)
    (hsmall : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) ≤ (K : ℝ)) :
    ∀ y ∈ Metric.closedBall z r,
      ‖deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ *
        ((quadratic c)^[q] w - w)) y‖ ≤ (K : ℝ) := by
  intro y hy
  exact le_trans
    (norm_deriv_newton_quadratic_iterate_inv_deriv_at_le hderiv (hvar y hy)) hsmall

/-- Chosen-radius Newton theorem from an explicit derivative-variation estimate.  Unlike the
qualitative radius package, the radius here is part of the data, so the center-fit comparison is a
real quantitative obligation rather than an all-small-radii hypothesis. -/
theorem exists_positive_periodic_point_mem_ball_of_newton_variation
    {c ζ z : ℂ} {q : ℕ} {R r μ : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hclosed : Metric.closedBall z r ⊆ Metric.ball ζ R)
    (hcenter :
      dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ * ((quadratic c)^[q] z - z)) z ≤
        (1 - (K : ℝ)) * r)
    (hvar : ∀ y ∈ Metric.closedBall z r,
      ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ)
    (hsmall : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q' : ℕ,
      1 ≤ q' ∧ (quadratic c)^[q'] y = y := by
  exact exists_positive_periodic_point_mem_ball_of_newton_contraction
    (c := c) (ζ := ζ) (a := z) (A := (deriv ((quadratic c)^[q]) z)⁻¹)
    (q := q) (R := R) (r := r) (K := K)
    hq (inv_ne_zero hderiv) hr hK hclosed
    (center_add_mul_radius_le_of_le_one_sub_mul hK hcenter)
    (newton_deriv_bound_of_iterate_deriv_variation_closedBall hderiv hvar hsmall)

/-- Exact center displacement for a Newton step based at a forward hit. -/
theorem newton_center_displacement_eq_inv_deriv_mul_fixed_hit
    {c z γ : ℂ} {q : ℕ}
    (hhit : (quadratic c)^[q] z = γ) :
    dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ * ((quadratic c)^[q] z - z)) z =
      ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * ‖γ - z‖ := by
  rw [hhit, dist_eq_norm]
  rw [show z - (deriv ((quadratic c)^[q]) z)⁻¹ * (γ - z) - z =
      -((deriv ((quadratic c)^[q]) z)⁻¹ * (γ - z)) by ring]
  rw [norm_neg, norm_mul]

/-- Exact fixed-tail center scale for the Newton step.  After a hit to a fixed anchor, the Newton
center displacement is the finite preperiodic inverse multiplier times `|2α|^{-m}` times the anchor
distance. -/
theorem newton_center_displacement_fixed_tail_eq
    {c z α : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    dist (z - (deriv ((quadratic c)^[n + m]) z)⁻¹ *
        ((quadratic c)^[n + m] z - z)) z =
      (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
          ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ := by
  rw [newton_center_displacement_eq_inv_deriv_mul_fixed_hit
    (iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m)]
  rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m]
  rw [norm_inv, norm_mul, norm_pow]

/-- Chosen-radius Newton theorem specialized to a forward hit. -/
theorem exists_positive_periodic_point_mem_ball_of_fixed_hit_newton_variation
    {c ζ z γ : ℂ} {q : ℕ} {R r μ : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hhit : (quadratic c)^[q] z = γ)
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hclosed : Metric.closedBall z r ⊆ Metric.ball ζ R)
    (hcenter : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * ‖γ - z‖ ≤
        (1 - (K : ℝ)) * r)
    (hvar : ∀ y ∈ Metric.closedBall z r,
      ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ)
    (hsmall : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q' : ℕ,
      1 ≤ q' ∧ (quadratic c)^[q'] y = y := by
  apply exists_positive_periodic_point_mem_ball_of_newton_variation
    (c := c) (ζ := ζ) (z := z) (q := q) (R := R) (r := r) (μ := μ) (K := K)
    hq hderiv hr hK hclosed _ hvar hsmall
  rwa [newton_center_displacement_eq_inv_deriv_mul_fixed_hit hhit]

/-- Mean-value estimate for derivative variation on a closed ball. -/
theorem deriv_variation_le_of_deriv_bound_closedBall
    {G : ℂ → ℂ} {z : ℂ} {r M : ℝ}
    (hr : 0 ≤ r)
    (hM : 0 ≤ M)
    (hdiff : ∀ y ∈ Metric.closedBall z r, DifferentiableAt ℂ G y)
    (hbound : ∀ y ∈ Metric.closedBall z r, ‖deriv G y‖ ≤ M) :
    ∀ y ∈ Metric.closedBall z r, ‖G y - G z‖ ≤ M * r := by
  intro y hy
  have hz : z ∈ Metric.closedBall z r := by
    rw [Metric.mem_closedBall, dist_self]
    exact hr
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_closedBall z r) hz hy
  have hydist : ‖y - z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  exact le_trans hmv (mul_le_mul_of_nonneg_left hydist hM)

/-- A second-derivative bound for a quadratic iterate gives the derivative-variation bound used by
the Newton contraction estimate. -/
theorem deriv_variation_quadratic_iterate_le_of_second_deriv_bound_closedBall
    {c z : ℂ} {q : ℕ} {r M : ℝ}
    (hr : 0 ≤ r)
    (hM : 0 ≤ M)
    (hbound : ∀ y ∈ Metric.closedBall z r,
      ‖deriv (fun w => deriv ((quadratic c)^[q]) w) y‖ ≤ M) :
    ∀ y ∈ Metric.closedBall z r,
      ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ M * r :=
  deriv_variation_le_of_deriv_bound_closedBall
    (G := fun w => deriv ((quadratic c)^[q]) w) hr hM
    (fun y _hy => (analyticAt_quadratic_iterate c q y).deriv.differentiableAt)
    hbound

/-- Compactness supplies the second-derivative bound on any chosen closed ball.  This removes the
purely analytic-boundedness part of the Newton-window data: after a radius and tail iterate are
chosen, only the scalar contraction inequalities remain. -/
theorem exists_second_deriv_bound_quadratic_iterate_closedBall
    (c z : ℂ) (q : ℕ) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Metric.closedBall z r,
      ‖deriv (fun w => deriv ((quadratic c)^[q]) w) y‖ ≤ M := by
  have hcont : Continuous (fun y => deriv (fun w => deriv ((quadratic c)^[q]) w) y) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (((analyticAt_quadratic_iterate c q y).deriv).deriv.continuousAt)
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall z r).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro y hy
  exact le_trans (hM y hy) (le_max_left _ _)

/-- Newton derivative bound from a second-derivative bound for the underlying iterate. -/
theorem newton_deriv_bound_of_iterate_second_deriv_bound_closedBall
    {c z : ℂ} {q : ℕ} {r M : ℝ} {K : NNReal}
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0)
    (hr : 0 ≤ r)
    (hM : 0 ≤ M)
    (hsecond : ∀ y ∈ Metric.closedBall z r,
      ‖deriv (fun w => deriv ((quadratic c)^[q]) w) y‖ ≤ M)
    (hsmall : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ y ∈ Metric.closedBall z r,
      ‖deriv (fun w => w - (deriv ((quadratic c)^[q]) z)⁻¹ *
        ((quadratic c)^[q] w - w)) y‖ ≤ (K : ℝ) :=
  newton_deriv_bound_of_iterate_deriv_variation_closedBall
    (c := c) (z := z) (q := q) (r := r) (μ := M * r) (K := K)
    hderiv
    (deriv_variation_quadratic_iterate_le_of_second_deriv_bound_closedBall hr hM hsecond)
    hsmall

/-- Chosen-radius Newton theorem using a second-derivative bound for the quadratic iterate. -/
theorem exists_positive_periodic_point_mem_ball_of_newton_second_deriv
    {c ζ z : ℂ} {q : ℕ} {R r M : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hderiv : deriv ((quadratic c)^[q]) z ≠ 0)
    (hr : 0 ≤ r)
    (hM : 0 ≤ M)
    (hK : K < 1)
    (hclosed : Metric.closedBall z r ⊆ Metric.ball ζ R)
    (hcenter :
      dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ * ((quadratic c)^[q] z - z)) z ≤
        (1 - (K : ℝ)) * r)
    (hsecond : ∀ y ∈ Metric.closedBall z r,
      ‖deriv (fun w => deriv ((quadratic c)^[q]) w) y‖ ≤ M)
    (hsmall : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q' : ℕ,
      1 ≤ q' ∧ (quadratic c)^[q'] y = y := by
  exact exists_positive_periodic_point_mem_ball_of_newton_contraction
    (c := c) (ζ := ζ) (a := z) (A := (deriv ((quadratic c)^[q]) z)⁻¹)
    (q := q) (R := R) (r := r) (K := K)
    hq (inv_ne_zero hderiv) hr hK hclosed
    (center_add_mul_radius_le_of_le_one_sub_mul hK hcenter)
    (newton_deriv_bound_of_iterate_second_deriv_bound_closedBall hderiv hr hM hsecond hsmall)

/-- A repelling fixed tail supplies the Newton center-fit at the same tail where an eventual
second-derivative window is available.  The remaining quantitative work is exactly the eventual
window: radius, second-derivative bound, and inverse-multiplier smallness. -/
theorem exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_newton_window
    {c ζ z α : ℂ} {n : ℕ} {R δ : ℝ}
    (hn : 1 ≤ n)
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hδ : 0 < δ)
    (hwindow : ∀ᶠ m : ℕ in atTop,
      ∃ (r M : ℝ) (K : NNReal),
        0 ≤ r ∧ 0 ≤ M ∧ K < 1 ∧
        Metric.closedBall z r ⊆ Metric.ball ζ R ∧
        δ ≤ (1 - (K : ℝ)) * r ∧
        (∀ y ∈ Metric.closedBall z r,
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q : ℕ,
      1 ≤ q ∧ (quadratic c)^[q] y = y := by
  have hcenter_eventually :=
    eventually_tail_inv_deriv_mul_fixed_dist_lt_of_repelling_hit
      hhit hfix hinit hrep hδ
  have hboth := hcenter_eventually.and hwindow
  obtain ⟨m, hm⟩ := eventually_atTop.mp hboth
  rcases hm m le_rfl with
    ⟨⟨hderiv_ne, hcenter_lt⟩, r, M, K, hr, hM, hK, hclosed, hδle, hsecond, hsmall⟩
  have hq : 1 ≤ n + m := by omega
  refine exists_positive_periodic_point_mem_ball_of_newton_second_deriv
    (c := c) (ζ := ζ) (z := z) (q := n + m) (R := R) (r := r) (M := M)
    (K := K) hq hderiv_ne hr hM hK hclosed ?_ hsecond hsmall
  rw [newton_center_displacement_eq_inv_deriv_mul_fixed_hit
    (iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m)]
  exact le_trans (le_of_lt hcenter_lt) hδle

/-- If a point lies in the half-radius ball, every closed ball around it with radius at most half
the target radius stays inside the target ball.  This is the geometric margin needed after shrinking
the selector ball. -/
theorem closedBall_subset_ball_of_mem_ball_half_radius_le
    {z₀ z : ℂ} {R r : ℝ}
    (hz : z ∈ Metric.ball z₀ (R / 2)) (hr : r ≤ R / 2) :
    Metric.closedBall z r ⊆ Metric.ball z₀ R := by
  intro y hy
  rw [Metric.mem_ball] at hz ⊢
  rw [Metric.mem_closedBall] at hy
  calc
    dist y z₀ ≤ dist y z + dist z z₀ := dist_triangle y z z₀
    _ ≤ r + dist z z₀ := by linarith
    _ < R / 2 + R / 2 := add_lt_add_of_le_of_lt hr hz
    _ = R := by ring

/-- Half-radius form of
`exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_newton_window`.
The forward-hit point lies in `ball ζ (R/2)`, and every eventual Newton radius is at most `R/2`,
so the target-ball containment is automatic. -/
theorem exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_newton_window_half
    {c ζ z α : ℂ} {n : ℕ} {R δ : ℝ}
    (hn : 1 ≤ n)
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hz : z ∈ Metric.ball ζ (R / 2))
    (hδ : 0 < δ)
    (hwindow : ∀ᶠ m : ℕ in atTop,
      ∃ (r M : ℝ) (K : NNReal),
        0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
        δ ≤ (1 - (K : ℝ)) * r ∧
        (∀ y ∈ Metric.closedBall z r,
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q : ℕ,
      1 ≤ q ∧ (quadratic c)^[q] y = y := by
  refine exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_newton_window
    (c := c) (ζ := ζ) (z := z) (α := α) (n := n) (R := R) (δ := δ)
    hn hhit hfix hinit hrep hδ ?_
  exact hwindow.mono (by
    intro m hm
    rcases hm with ⟨r, M, K, hr, hrle, hM, hK, hδle, hsecond, hsmall⟩
    exact ⟨r, M, K, hr, hM, hK,
      closedBall_subset_ball_of_mem_ball_half_radius_le hz hrle, hδle, hsecond, hsmall⟩)

/-- Scaled half-radius fixed-tail window.  This is the form for shrinking Newton radii: the caller
supplies a scale `η m` that bounds the fixed-tail center displacement and proves that the Newton
radius beats that same scale. -/
theorem exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_scaled_newton_window_half
    {c ζ z α : ℂ} {n : ℕ} {R : ℝ} (η : ℕ → ℝ)
    (hn : 1 ≤ n)
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hz : z ∈ Metric.ball ζ (R / 2))
    (hcenter : ∀ᶠ m : ℕ in atTop,
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖α - z‖ ≤ η m)
    (hwindow : ∀ᶠ m : ℕ in atTop,
      ∃ (r M : ℝ) (K : NNReal),
        0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
        η m ≤ (1 - (K : ℝ)) * r ∧
        (∀ y ∈ Metric.closedBall z r,
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q : ℕ,
      1 ≤ q ∧ (quadratic c)^[q] y = y := by
  have hderiv_eventually : ∀ᶠ m : ℕ in atTop,
      deriv ((quadratic c)^[n + m]) z ≠ 0 :=
    Eventually.of_forall (deriv_fixed_tail_ne_zero_of_repelling_hit hhit hfix hinit hrep)
  have hboth := hderiv_eventually.and (hcenter.and hwindow)
  obtain ⟨m, hm⟩ := eventually_atTop.mp hboth
  rcases hm m le_rfl with
    ⟨hderiv_ne, hcenter_le, r, M, K, hr, hrle, hM, hK, hηle, hsecond, hsmall⟩
  have hq : 1 ≤ n + m := by omega
  refine exists_positive_periodic_point_mem_ball_of_newton_second_deriv
    (c := c) (ζ := ζ) (z := z) (q := n + m) (R := R) (r := r) (M := M)
    (K := K) hq hderiv_ne hr hM hK
    (closedBall_subset_ball_of_mem_ball_half_radius_le hz hrle) ?_ hsecond hsmall
  rw [newton_center_displacement_eq_inv_deriv_mul_fixed_hit
    (iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m)]
  exact le_trans hcenter_le hηle

/-- Explicit-scale version of the fixed-tail Newton window.  The auxiliary scale is no longer a
separate caller choice: it is exactly the fixed-tail center displacement
`(|P_n| |2α|^m)⁻¹ |α-z|`.  The only remaining quantitative work is the real window inequality against
that explicit scale. -/
theorem exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_explicit_scaled_newton_window_half
    {c ζ z α : ℂ} {n : ℕ} {R : ℝ}
    (hn : 1 ≤ n)
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hz : z ∈ Metric.ball ζ (R / 2))
    (hwindow : ∀ᶠ m : ℕ in atTop,
      ∃ (r M : ℝ) (K : NNReal),
        0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
        (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
            ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
        (∀ y ∈ Metric.closedBall z r,
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q : ℕ,
      1 ≤ q ∧ (quadratic c)^[q] y = y := by
  refine exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_scaled_newton_window_half
    (c := c) (ζ := ζ) (z := z) (α := α) (n := n) (R := R)
    (η := fun m =>
      (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
        ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖)
    hn hhit hfix hinit hrep hz ?_ hwindow
  exact Eventually.of_forall (fun m => by
    rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m]
    rw [norm_inv, norm_mul, norm_pow])

/-- Concrete Newton-data replacement for the abstract forward-hit-to-periodic hypothesis in the
cross-ratio selector bridge. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_newton
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hnewton : ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
      ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ (q : ℕ) (r : ℝ) (A : ℂ) (K : NNReal),
          1 ≤ q ∧ A ≠ 0 ∧ 0 ≤ r ∧ K < 1 ∧
          Metric.closedBall z r ⊆ Metric.ball z₀ Rlift ∧
          dist (z - A * ((quadratic c)^[q] z - z)) z + (K : ℝ) * r ≤ r ∧
          ∀ y ∈ Metric.closedBall z r,
            ‖deriv (fun w => w - A * ((quadratic c)^[q] w - w)) y‖ ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic
    hαfix hβfix hαβ
  intro z₀ ρ Rlift hzfront hρ0 hρR n z hn hz hhit
  obtain ⟨q, r, A, K, hq, hA, hr, hK, hclosed, hcenter, hderiv_bound⟩ :=
    hnewton hzfront hρ0 hρR n z hn hz hhit
  exact exists_positive_periodic_point_mem_ball_of_newton_contraction
    (c := c) (ζ := z₀) (a := z) (A := A) (q := q) (R := Rlift) (r := r) (K := K)
    hq hA hr hK hclosed hcenter hderiv_bound

/-- Derivative-variation replacement for the abstract forward-hit-to-periodic hypothesis in the
cross-ratio selector bridge.  The caller supplies a chosen contraction radius and a bound on the
variation of the iterate derivative on that radius; `exists_positive_periodic_point_mem_ball_of_newton_variation`
turns those into the Newton contraction data. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_newton_variation
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hnewton : ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
      ∀ n z, 1 ≤ n → z ∈ ball z₀ Rlift →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ (q : ℕ) (r μ : ℝ) (K : NNReal),
          1 ≤ q ∧
          deriv ((quadratic c)^[q]) z ≠ 0 ∧
          0 ≤ r ∧ K < 1 ∧
          Metric.closedBall z r ⊆ Metric.ball z₀ Rlift ∧
          dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
            ((quadratic c)^[q] z - z)) z ≤ (1 - (K : ℝ)) * r ∧
          (∀ y ∈ Metric.closedBall z r,
            ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ) ∧
          ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic
    hαfix hβfix hαβ
  intro z₀ ρ Rlift hzfront hρ0 hρR n z hn hz hhit
  obtain ⟨q, r, μ, K, hq, hderiv, hr, hK, hclosed, hcenter, hvar, hsmall⟩ :=
    hnewton hzfront hρ0 hρR n z hn hz hhit
  exact exists_positive_periodic_point_mem_ball_of_newton_variation
    (c := c) (ζ := z₀) (z := z) (q := q) (R := Rlift) (r := r) (μ := μ) (K := K)
    hq hderiv hr hK hclosed hcenter hvar hsmall

/-- Half-radius margin version of the derivative-variation Newton bridge.  The selector supplies a
forward hit in `ball z₀ (R/2)`; the caller only has to choose a Newton radius `r ≤ R/2`, and the
geometric containment in `ball z₀ R` is automatic. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_newton_variation_half
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hnewton : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        ((quadratic c)^[n] z = α ∨ (quadratic c)^[n] z = β) →
        ∃ (q : ℕ) (r μ : ℝ) (K : NNReal),
          1 ≤ q ∧
          deriv ((quadratic c)^[q]) z ≠ 0 ∧
          0 ≤ r ∧ r ≤ R / 2 ∧ K < 1 ∧
          dist (z - (deriv ((quadratic c)^[q]) z)⁻¹ *
            ((quadratic c)^[q] z - z)) z ≤ (1 - (K : ℝ)) * r ∧
          (∀ y ∈ Metric.closedBall z r,
            ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ μ) ∧
          ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (μ + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic_half
    hαfix hβfix hαβ
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  obtain ⟨q, r, μ, K, hq, hderiv, hr, hrle, hK, hcenter, hvar, hsmall⟩ :=
    hnewton hzfront hρ0 hρR n z hn hz hhit
  exact exists_positive_periodic_point_mem_ball_of_newton_variation
    (c := c) (ζ := z₀) (z := z) (q := q) (R := R) (r := r) (μ := μ) (K := K)
    hq hderiv hr hK (closedBall_subset_ball_of_mem_ball_half_radius_le hz hrle)
    hcenter hvar hsmall

/-- Fixed-tail/eventual-window replacement for the abstract forward-hit-to-periodic bridge.  A
selector hit to either repelling fixed anchor is converted to a positive periodic point once the
pre-hit is noncritical and an eventual half-radius Newton window is available. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_repelling_eventual_newton_window_half
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαrep : 1 < ‖(2 : ℂ) * α‖) (hβrep : 1 < ‖(2 : ℂ) * β‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z γ, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) → (γ = α ∨ γ = β) →
        (quadratic c)^[n] z = γ →
        (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ᶠ m : ℕ in atTop,
            ∃ (r M : ℝ) (K : NNReal),
              0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
              δ ≤ (1 - (K : ℝ)) * r ∧
              (∀ y ∈ Metric.closedBall z r,
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic_half
    hαfix hβfix hαβ
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  rcases hhit with hhitα | hhitβ
  · obtain ⟨hinit, δ, hδ, hwin⟩ :=
      hwindow (γ := α) hzfront hρ0 hρR n z hn hz (Or.inl rfl) hhitα
    exact exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_newton_window_half
      (c := c) (ζ := z₀) (z := z) (α := α) (n := n) (R := R) (δ := δ)
      hn hhitα hαfix hinit hαrep hz hδ hwin
  · obtain ⟨hinit, δ, hδ, hwin⟩ :=
      hwindow (γ := β) hzfront hρ0 hρR n z hn hz (Or.inr rfl) hhitβ
    exact exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_newton_window_half
      (c := c) (ζ := z₀) (z := z) (α := β) (n := n) (R := R) (δ := δ)
      hn hhitβ hβfix hinit hβrep hz hδ hwin

/-- No-precritical form of the fixed-tail/eventual-window bridge.  This is the dynamical version of
the previous theorem: the finite orbit product is discharged by proving that the selector pre-hit
does not pass through the critical point before reaching the fixed anchor. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_repelling_eventual_newton_window_half_no_precritical
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαrep : 1 < ‖(2 : ℂ) * α‖) (hβrep : 1 < ‖(2 : ℂ) * β‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z γ, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) → (γ = α ∨ γ = β) →
        (quadratic c)^[n] z = γ →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ᶠ m : ℕ in atTop,
            ∃ (r M : ℝ) (K : NNReal),
              0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
              δ ≤ (1 - (K : ℝ)) * r ∧
              (∀ y ∈ Metric.closedBall z r,
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_repelling_eventual_newton_window_half
    hαfix hβfix hαβ hαrep hβrep
  intro z₀ ρ R hzfront hρ0 hρR n z γ hn hz hγ hhit
  obtain ⟨hprecrit, hwin⟩ := hwindow hzfront hρ0 hρR n z γ hn hz hγ hhit
  exact ⟨(orbitProduct_ne_zero_iff_no_precritical c z n).2 hprecrit, hwin⟩

/-- Scaled no-precritical form of the fixed-tail/eventual-window bridge.  This is the shrinking
radius version: the caller supplies a center scale `η m` and an eventual Newton window whose radius
beats that scale. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_repelling_eventual_scaled_newton_window_half_no_precritical
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαrep : 1 < ‖(2 : ℂ) * α‖) (hβrep : 1 < ‖(2 : ℂ) * β‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z γ, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) → (γ = α ∨ γ = β) →
        (quadratic c)^[n] z = γ →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∃ η : ℕ → ℝ,
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ‖γ - z‖ ≤ η m) ∧
          ∀ᶠ m : ℕ in atTop,
            ∃ (r M : ℝ) (K : NNReal),
              0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
              η m ≤ (1 - (K : ℝ)) * r ∧
              (∀ y ∈ Metric.closedBall z r,
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_pair_to_positive_periodic_half
    hαfix hβfix hαβ
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  rcases hhit with hhitα | hhitβ
  · obtain ⟨hprecrit, η, hcenter, hwin⟩ :=
      hwindow (γ := α) hzfront hρ0 hρR n z hn hz (Or.inl rfl) hhitα
    exact exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_scaled_newton_window_half
      (c := c) (ζ := z₀) (z := z) (α := α) (n := n) (R := R) η
      hn hhitα hαfix ((orbitProduct_ne_zero_iff_no_precritical c z n).2 hprecrit)
      hαrep hz hcenter hwin
  · obtain ⟨hprecrit, η, hcenter, hwin⟩ :=
      hwindow (γ := β) hzfront hρ0 hρR n z hn hz (Or.inr rfl) hhitβ
    exact exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_scaled_newton_window_half
      (c := c) (ζ := z₀) (z := z) (α := β) (n := n) (R := R) η
      hn hhitβ hβfix ((orbitProduct_ne_zero_iff_no_precritical c z n).2 hprecrit)
      hβrep hz hcenter hwin

end

end Bottcher
