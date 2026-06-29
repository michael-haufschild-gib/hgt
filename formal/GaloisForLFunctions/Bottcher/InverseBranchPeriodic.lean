import GaloisForLFunctions.Bottcher.ConnectedRepellingStrongRoots

open Set Filter Topology Metric

namespace Bottcher

/-- A contracting inverse branch of an iterate on a closed ball produces a periodic point in that
ball.  This is the Banach-fixed-point bridge needed after constructing a local inverse branch from
the blowing-up theorem. -/
theorem exists_periodic_point_of_contracting_inverse_branch_on_closedBall
    {c a : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hmaps : Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r))
    (hcontr : ContractingWith K (Set.MapsTo.restrict g (Metric.closedBall a r)
      (Metric.closedBall a r) hmaps))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z) :
    ∃ z ∈ Metric.closedBall a r, (quadratic c)^[p] z = z := by
  have ha : a ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_self]
    exact hr
  have hcomplete : IsComplete (Metric.closedBall a r) := Metric.isClosed_closedBall.isComplete
  obtain ⟨z, hz, hfix, _htend, _hest⟩ :=
    hcontr.exists_fixedPoint' hcomplete hmaps ha (edist_ne_top a (g a))
  have hper := hinv z hz
  rw [hfix] at hper
  exact ⟨z, hz, hper⟩

/-- Lipschitz form of the ordinary inverse-branch fixed-point bridge. -/
theorem exists_periodic_point_of_lipschitz_inverse_branch_on_closedBall
    {c a : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hmaps : Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r))
    (hlip : LipschitzOnWith K g (Metric.closedBall a r))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z) :
    ∃ z ∈ Metric.closedBall a r, (quadratic c)^[p] z = z := by
  have hcontr : ContractingWith K (Set.MapsTo.restrict g (Metric.closedBall a r)
      (Metric.closedBall a r) hmaps) := by
    refine ⟨hK, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hdist := hlip.dist_le_mul x.1 x.2 y.1 y.2
    simpa [Set.MapsTo.restrict, Subtype.dist_eq] using hdist
  exact exists_periodic_point_of_contracting_inverse_branch_on_closedBall
    hr hmaps hcontr hinv

/-- Near-return form of the ordinary inverse-branch bridge.  A Lipschitz inverse branch centered at
`a`, with `g a = x` and displacement `dist x a` fitting the contraction radius, maps the closed ball
into itself and therefore has a fixed point. -/
theorem exists_periodic_point_of_lipschitz_inverse_branch_near_return_closedBall
    {c a x : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hga : g a = x)
    (hclose : dist x a + (K : ℝ) * r ≤ r)
    (hlip : LipschitzOnWith K g (Metric.closedBall a r))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z) :
    ∃ z ∈ Metric.closedBall a r, (quadratic c)^[p] z = z := by
  have hmaps : Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r) := by
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have ha : a ∈ Metric.closedBall a r := by
      rw [Metric.mem_closedBall, dist_self]
      exact hr
    have hdist := hlip.dist_le_mul y hy a ha
    have hstep : dist (g y) a ≤ (K : ℝ) * r + dist x a := by
      have hdist' : dist (g y) x ≤ (K : ℝ) * dist y a := by
        simpa [hga] using hdist
      have hmul : (K : ℝ) * dist y a ≤ (K : ℝ) * r := by
        exact mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg K)
      calc
        dist (g y) a ≤ dist (g y) (g a) + dist (g a) a := dist_triangle _ _ _
        _ = dist (g y) x + dist x a := by rw [hga]
        _ ≤ (K : ℝ) * dist y a + dist x a := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdist' (dist x a)
        _ ≤ (K : ℝ) * r + dist x a := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul (dist x a)
    linarith [hstep, hclose]
  exact exists_periodic_point_of_lipschitz_inverse_branch_on_closedBall
    hr hK hmaps hlip hinv

/-- Derivative-bound form of the ordinary near-return inverse-branch bridge. -/
theorem exists_periodic_point_of_deriv_bound_inverse_branch_near_return_closedBall
    {c a x : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hga : g a = x)
    (hclose : dist x a + (K : ℝ) * r ≤ r)
    (hderivWithin : ∀ z ∈ Metric.closedBall a r,
      HasDerivWithinAt g (deriv g z) (Metric.closedBall a r) z)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r, ‖deriv g z‖ ≤ (K : ℝ))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z) :
    ∃ z ∈ Metric.closedBall a r, (quadratic c)^[p] z = z := by
  have hlip : LipschitzOnWith K g (Metric.closedBall a r) := by
    apply (convex_closedBall a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      hderivWithin
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hderiv_bound z hz
  exact exists_periodic_point_of_lipschitz_inverse_branch_near_return_closedBall
    hr hK hga hclose hlip hinv

/-- Derivative contraction of an inverse branch gives the hRigid strong orbit-product bound for the
forward iterate. -/
theorem strong_orbitProduct_of_inverse_deriv_norm_lt
    {c z η : ℂ} {p : ℕ}
    (hηinv : deriv ((quadratic c)^[p]) z * η = 1)
    (hη : ‖η‖ < ((2 ^ p : ℝ)⁻¹)) :
    (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  have hpow_pos : 0 < (2 ^ p : ℝ) := by positivity
  have hnorm_prod : ‖deriv ((quadratic c)^[p]) z‖ * ‖η‖ = 1 := by
    have h := congrArg norm hηinv
    simpa [norm_mul, norm_one] using h
  by_contra hnot
  have hle : ‖deriv ((quadratic c)^[p]) z‖ ≤ (2 ^ p : ℝ) := by
    rw [deriv_quadratic_iterate_eq_orbitProduct_core]
    exact le_of_not_gt hnot
  have hmul_lt : ‖deriv ((quadratic c)^[p]) z‖ * ‖η‖ < 1 := by
    calc
      ‖deriv ((quadratic c)^[p]) z‖ * ‖η‖ ≤ (2 ^ p : ℝ) * ‖η‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg η)
      _ < (2 ^ p : ℝ) * ((2 ^ p : ℝ)⁻¹) :=
        mul_lt_mul_of_pos_left hη hpow_pos
      _ = 1 := by field_simp [ne_of_gt hpow_pos]
  linarith

/-- Canonical inverse-multiplier form of the hRigid strong orbit-product bound. -/
theorem strong_orbitProduct_of_deriv_inv_norm_lt
    {c z : ℂ} {p : ℕ}
    (hcrit : deriv ((quadratic c)^[p]) z ≠ 0)
    (hη : ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < ((2 ^ p : ℝ)⁻¹)) :
    (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  exact strong_orbitProduct_of_inverse_deriv_norm_lt (η := (deriv ((quadratic c)^[p]) z)⁻¹)
    (mul_inv_cancel₀ hcrit) hη

/-- Exact-return inverse-multiplier form: an exact periodic point whose canonical inverse multiplier
is below `(2^p)⁻¹` is already the strong periodic witness in any target ball containing it. -/
theorem exists_strongly_repelling_periodic_mem_ball_of_periodic_deriv_inv_norm_lt
    {c ζ z : ℂ} {p : ℕ} {R : ℝ}
    (hzball : z ∈ Metric.ball ζ R)
    (hper : (quadratic c)^[p] z = z)
    (hcrit : deriv ((quadratic c)^[p]) z ≠ 0)
    (hη : ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < ((2 ^ p : ℝ)⁻¹)) :
    ∃ y ∈ Metric.ball ζ R,
      (quadratic c)^[p] y = y ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] y‖ := by
  exact ⟨z, hzball, hper, strong_orbitProduct_of_deriv_inv_norm_lt hcrit hη⟩

/-- Dense exact periodic points with small canonical inverse multiplier give the strong-periodic
density required by the hRigid/q62 path. -/
theorem dense_strongly_repelling_periodic_of_forall_frontier_ball_periodic_deriv_inv_norm_lt
    {c : ℂ}
    (hlocal : ∀ ζ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ z ∈ Metric.ball ζ R, ∃ p : ℕ,
        (quadratic c)^[p] z = z ∧
        deriv ((quadratic c)^[p]) z ≠ 0 ∧
        ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < ((2 ^ p : ℝ)⁻¹)) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖} := by
  apply dense_strongly_repelling_periodic_of_forall_frontier_ball
  intro ζ hζ R hR
  obtain ⟨z, hzball, p, hper, hcrit, hη⟩ := hlocal ζ hζ R hR
  obtain ⟨y, hyball, hpery, hstrong⟩ :=
    exists_strongly_repelling_periodic_mem_ball_of_periodic_deriv_inv_norm_lt
      (c := c) (ζ := ζ) (z := z) (p := p) (R := R) hzball hper hcrit hη
  exact ⟨y, hyball, p, hpery, hstrong⟩

/-- A contracting inverse branch of an iterate, with the derivative inverse relation and the
quantitative inverse-derivative bound on the trapping closed ball, produces the strongly-repelling
periodic witness used by the hRigid frontier-density lane. -/
theorem exists_strongly_repelling_periodic_of_contracting_inverse_branch_on_closedBall
    {c a : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hmaps : Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r))
    (hcontr : ContractingWith K (Set.MapsTo.restrict g (Metric.closedBall a r)
      (Metric.closedBall a r) hmaps))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z)
    (hderiv_inv : ∀ z ∈ Metric.closedBall a r,
      deriv ((quadratic c)^[p]) (g z) * deriv g z = 1)
    (hderiv_lt : ∀ z ∈ Metric.closedBall a r, ‖deriv g z‖ < ((2 ^ p : ℝ)⁻¹)) :
    ∃ z ∈ Metric.closedBall a r,
      (quadratic c)^[p] z = z ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  have ha : a ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_self]
    exact hr
  have hcomplete : IsComplete (Metric.closedBall a r) := Metric.isClosed_closedBall.isComplete
  obtain ⟨z, hz, hfix, _htend, _hest⟩ :=
    hcontr.exists_fixedPoint' hcomplete hmaps ha (edist_ne_top a (g a))
  have hfix_val : g z = z := by
    simpa [Function.IsFixedPt] using hfix
  have hper : (quadratic c)^[p] z = z := by
    have h := hinv z hz
    rwa [hfix_val] at h
  have hderiv : deriv ((quadratic c)^[p]) z * deriv g z = 1 := by
    simpa [hfix_val] using hderiv_inv z hz
  have hstrong :
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ :=
    strong_orbitProduct_of_inverse_deriv_norm_lt hderiv (hderiv_lt z hz)
  exact ⟨z, hz, hper, hstrong⟩

/-- Lipschitz form of
`exists_strongly_repelling_periodic_of_contracting_inverse_branch_on_closedBall`.  This is the form
produced by a Cauchy/derivative estimate on a closed ball: a self-map with Lipschitz constant `< 1`
is a `ContractingWith` map on the restricted complete ball. -/
theorem exists_strongly_repelling_periodic_of_lipschitz_inverse_branch_on_closedBall
    {c a : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hmaps : Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r))
    (hlip : LipschitzOnWith K g (Metric.closedBall a r))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z)
    (hderiv_inv : ∀ z ∈ Metric.closedBall a r,
      deriv ((quadratic c)^[p]) (g z) * deriv g z = 1)
    (hderiv_lt : ∀ z ∈ Metric.closedBall a r, ‖deriv g z‖ < ((2 ^ p : ℝ)⁻¹)) :
    ∃ z ∈ Metric.closedBall a r,
      (quadratic c)^[p] z = z ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  have hcontr : ContractingWith K (Set.MapsTo.restrict g (Metric.closedBall a r)
      (Metric.closedBall a r) hmaps) := by
    refine ⟨hK, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hdist := hlip.dist_le_mul x.1 x.2 y.1 y.2
    simpa [Set.MapsTo.restrict, Subtype.dist_eq] using hdist
  exact exists_strongly_repelling_periodic_of_contracting_inverse_branch_on_closedBall
    hr hmaps hcontr hinv hderiv_inv hderiv_lt

/-- Near-return form of the inverse-branch fixed-point bridge.  A Lipschitz inverse branch centered
at `a`, with `g a = x` and displacement `dist x a` small enough relative to the contraction radius,
automatically maps `closedBall a r` into itself.  This is the trapping estimate needed after a
regular approximate return is selected. -/
theorem exists_strongly_repelling_periodic_of_lipschitz_inverse_branch_near_return_closedBall
    {c a x : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hga : g a = x)
    (hclose : dist x a + (K : ℝ) * r ≤ r)
    (hlip : LipschitzOnWith K g (Metric.closedBall a r))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z)
    (hderiv_inv : ∀ z ∈ Metric.closedBall a r,
      deriv ((quadratic c)^[p]) (g z) * deriv g z = 1)
    (hderiv_lt : ∀ z ∈ Metric.closedBall a r, ‖deriv g z‖ < ((2 ^ p : ℝ)⁻¹)) :
    ∃ z ∈ Metric.closedBall a r,
      (quadratic c)^[p] z = z ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  have hmaps : Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r) := by
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have ha : a ∈ Metric.closedBall a r := by
      rw [Metric.mem_closedBall, dist_self]
      exact hr
    have hdist := hlip.dist_le_mul y hy a ha
    have hstep : dist (g y) a ≤ (K : ℝ) * r + dist x a := by
      have hdist' : dist (g y) x ≤ (K : ℝ) * dist y a := by
        simpa [hga] using hdist
      have hmul : (K : ℝ) * dist y a ≤ (K : ℝ) * r := by
        exact mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg K)
      calc
        dist (g y) a ≤ dist (g y) (g a) + dist (g a) a := dist_triangle _ _ _
        _ = dist (g y) x + dist x a := by rw [hga]
        _ ≤ (K : ℝ) * dist y a + dist x a := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hdist' (dist x a)
        _ ≤ (K : ℝ) * r + dist x a := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul (dist x a)
    linarith [hstep, hclose]
  exact exists_strongly_repelling_periodic_of_lipschitz_inverse_branch_on_closedBall
    hr hK hmaps hlip hinv hderiv_inv hderiv_lt

/-- Derivative-bound form of the near-return inverse-branch bridge.  On a convex closed ball, a
uniform bound `‖g'‖ ≤ K` gives the needed Lipschitz estimate; the strict bound
`K < (2^p)⁻¹` supplies the hRigid orbit-product inequality. -/
theorem exists_strongly_repelling_periodic_of_deriv_bound_inverse_branch_near_return_closedBall
    {c a x : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hKstrong : (K : ℝ) < ((2 ^ p : ℝ)⁻¹))
    (hga : g a = x)
    (hclose : dist x a + (K : ℝ) * r ≤ r)
    (hderivWithin : ∀ z ∈ Metric.closedBall a r,
      HasDerivWithinAt g (deriv g z) (Metric.closedBall a r) z)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r, ‖deriv g z‖ ≤ (K : ℝ))
    (hinv : ∀ z ∈ Metric.closedBall a r, (quadratic c)^[p] (g z) = z)
    (hderiv_inv : ∀ z ∈ Metric.closedBall a r,
      deriv ((quadratic c)^[p]) (g z) * deriv g z = 1) :
    ∃ z ∈ Metric.closedBall a r,
      (quadratic c)^[p] z = z ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  have hlip : LipschitzOnWith K g (Metric.closedBall a r) := by
    apply (convex_closedBall a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      hderivWithin
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hderiv_bound z hz
  exact exists_strongly_repelling_periodic_of_lipschitz_inverse_branch_near_return_closedBall
    hr hK hga hclose hlip hinv hderiv_inv
    (fun z hz => lt_of_le_of_lt (hderiv_bound z hz) hKstrong)

/-- If `g` is a local right inverse to `F` near `z`, then differentiating `F ∘ g = id`
gives the inverse-branch derivative identity. -/
theorem deriv_mul_deriv_eq_one_of_eventually_right_inverse
    {F g : ℂ → ℂ} {z : ℂ}
    (hF : HasDerivAt F (deriv F (g z)) (g z))
    (hg : HasDerivAt g (deriv g z) z)
    (hright : (fun y => F (g y)) =ᶠ[𝓝 z] id) :
    deriv F (g z) * deriv g z = 1 := by
  have hcomp : HasDerivAt (fun y => F (g y)) (deriv F (g z) * deriv g z) z :=
    hF.comp z hg
  have hid : HasDerivAt id (1 : ℂ) z := hasDerivAt_id z
  exact hcomp.unique (hid.congr_of_eventuallyEq hright)

/-- Derivative-bound near-return bridge with the inverse derivative identity derived from an
actual local right-inverse relation, rather than assumed independently. -/
theorem exists_strongly_repelling_periodic_of_deriv_bound_inverse_branch_near_return_nhdsRightInverse
    {c a x : ℂ} {p : ℕ} {r : ℝ} {g : ℂ → ℂ} {K : NNReal}
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hKstrong : (K : ℝ) < ((2 ^ p : ℝ)⁻¹))
    (hga : g a = x)
    (hclose : dist x a + (K : ℝ) * r ≤ r)
    (hderivAt : ∀ z ∈ Metric.closedBall a r, HasDerivAt g (deriv g z) z)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r, ‖deriv g z‖ ≤ (K : ℝ))
    (hinv_nhds : ∀ z ∈ Metric.closedBall a r,
      (fun y => (quadratic c)^[p] (g y)) =ᶠ[𝓝 z] id) :
    ∃ z ∈ Metric.closedBall a r,
      (quadratic c)^[p] z = z ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z‖ := by
  apply exists_strongly_repelling_periodic_of_deriv_bound_inverse_branch_near_return_closedBall
    hr hK hKstrong hga hclose
  · intro z hz
    exact (hderivAt z hz).hasDerivWithinAt
  · exact hderiv_bound
  · intro z hz
    exact (hinv_nhds z hz).eq_of_nhds
  · intro z hz
    have hF : HasDerivAt ((quadratic c)^[p])
        (deriv ((quadratic c)^[p]) (g z)) (g z) :=
      (differentiable_quadratic_iterate c p).differentiableAt.hasDerivAt
    exact deriv_mul_deriv_eq_one_of_eventually_right_inverse hF (hderivAt z hz)
      (hinv_nhds z hz)

/-- A `C^1` inverse branch whose derivative is strictly bounded at the center has the same
derivative bound on some closed ball around the center. -/
theorem exists_closedBall_deriv_bound_of_contDiffAt_one
    {g : ℂ → ℂ} {a : ℂ} {K : ℝ}
    (hg : ContDiffAt ℂ 1 g a)
    (hK : ‖deriv g a‖ < K) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.closedBall a r,
      HasDerivAt g (deriv g z) z ∧ ‖deriv g z‖ ≤ K := by
  have hderiv_cd : ContDiffAt ℂ 0 (deriv g) a :=
    ContDiffAt.derivWithin (f := g) (x := a) (m := 0) hg (by norm_num)
  have hcont : ContinuousAt (fun z => ‖deriv g z‖) a := hderiv_cd.continuousAt.norm
  have hdiff_eventually : ∀ᶠ z in 𝓝 a, ContDiffAt ℂ 1 g z :=
    hg.eventually (by norm_num)
  have hbound_eventually : ∀ᶠ z in 𝓝 a, ‖deriv g z‖ < K :=
    hcont.eventually_lt_const hK
  have hgood : {z | ContDiffAt ℂ 1 g z ∧ ‖deriv g z‖ ≤ K} ∈ 𝓝 a := by
    filter_upwards [hdiff_eventually, hbound_eventually] with z hz hzb
    exact ⟨hz, le_of_lt hzb⟩
  obtain ⟨r, hrpos, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgood
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  have hzg : ContDiffAt ℂ 1 g z ∧ ‖deriv g z‖ ≤ K := hrsub hz
  exact ⟨hzg.1.differentiableAt (by norm_num) |>.hasDerivAt, hzg.2⟩

/-- Analytic version of `exists_closedBall_deriv_bound_of_contDiffAt_one`. -/
theorem exists_closedBall_deriv_bound_of_analyticAt
    {g : ℂ → ℂ} {a : ℂ} {K : ℝ}
    (hg : AnalyticAt ℂ g a)
    (hK : ‖deriv g a‖ < K) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.closedBall a r,
      HasDerivAt g (deriv g z) z ∧ ‖deriv g z‖ ≤ K := by
  exact exists_closedBall_deriv_bound_of_contDiffAt_one hg.contDiffAt hK

/-- An analytic local branch with a center right-inverse equation shrinks to a closed ball on which
the derivative bound holds and the right-inverse equation holds in a neighborhood of every point. -/
theorem exists_closedBall_inverse_branch_data_of_analyticAt_eventually_right_inverse
    {F g : ℂ → ℂ} {a : ℂ} {K : ℝ}
    (hg : AnalyticAt ℂ g a)
    (hK : ‖deriv g a‖ < K)
    (hright : (fun y => F (g y)) =ᶠ[𝓝 a] id) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.closedBall a r,
      HasDerivAt g (deriv g z) z ∧ ‖deriv g z‖ ≤ K ∧
        (fun y => F (g y)) =ᶠ[𝓝 z] id := by
  obtain ⟨r₀, hr₀pos, hderiv⟩ :=
    exists_closedBall_deriv_bound_of_analyticAt hg hK
  have hright_mem : {y | F (g y) = y} ∈ 𝓝 a := hright
  obtain ⟨t, htsub, htopen, hat⟩ := _root_.mem_nhds_iff.mp hright_mem
  have hnb : t ∩ Metric.ball a r₀ ∈ 𝓝 a :=
    inter_mem (htopen.mem_nhds hat) (Metric.ball_mem_nhds a hr₀pos)
  obtain ⟨r, hrpos, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnb
  refine ⟨r, hrpos, ?_⟩
  intro z hz
  have hzmem := hrsub hz
  have hzt : z ∈ t := hzmem.1
  have hzball : z ∈ Metric.closedBall a r₀ := Metric.ball_subset_closedBall hzmem.2
  have hright_z : (fun y => F (g y)) =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (htopen.mem_nhds hzt) (fun y hy => htsub hy)
  exact ⟨(hderiv z hzball).1, (hderiv z hzball).2, hright_z⟩

/-- The inverse-function theorem creates the local inverse branch of a quadratic iterate at a
noncritical point, then shrinks to a closed ball with derivative bound and pointwise local
right-inverse data. -/
theorem exists_closedBall_localInverse_iterate_branch_data
    {c z : ℂ} {p : ℕ} {K : ℝ}
    (hcrit : deriv ((quadratic c)^[p]) z ≠ 0)
    (hK : ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < K) :
    ∃ (g : ℂ → ℂ) (r : ℝ), 0 < r ∧
      g ((quadratic c)^[p] z) = z ∧
      ∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
        HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ K ∧
          (fun w => (quadratic c)^[p] (g w)) =ᶠ[𝓝 y] id := by
  set F : ℂ → ℂ := (quadratic c)^[p]
  have hFan : AnalyticAt ℂ F z := by
    simpa [F] using (analyticOnNhd_quadratic_iterate c p) z (mem_univ z)
  have hstrict : HasStrictDerivAt F (deriv F z) z := hFan.hasStrictDerivAt
  have hcritF : deriv F z ≠ 0 := by simpa [F] using hcrit
  set g : ℂ → ℂ := HasStrictDerivAt.localInverse F (deriv F z) z hstrict hcritF
  have hg_an : AnalyticAt ℂ g (F z) := by
    simpa [g] using hFan.analyticAt_localInverse hcritF
  have hright : (fun y => F (g y)) =ᶠ[𝓝 (F z)] id := by
    simpa [g] using hstrict.eventually_right_inverse hcritF
  have hgderiv : HasStrictDerivAt g (deriv F z)⁻¹ (F z) := by
    simpa [g] using hstrict.to_localInverse hcritF
  have hKcenter : ‖deriv g (F z)‖ < K := by
    rw [hgderiv.hasDerivAt.deriv]
    simpa [F] using hK
  obtain ⟨r, hrpos, hdata⟩ :=
    exists_closedBall_inverse_branch_data_of_analyticAt_eventually_right_inverse
      hg_an hKcenter hright
  have hgFz : g (F z) = z := by
    simp [g]
  refine ⟨g, r, hrpos, ?_, ?_⟩
  · simpa [F] using hgFz
  · simpa [F] using hdata

/-- Ordinary local inverse-function-theorem near-return splice.  Once a noncritical approximate
return has inverse multiplier `< K < 1`, it remains only to prove the generated closed ball is
trapping and located inside the target ball.  No strong multiplier bound is needed for the ordinary
periodic-density lane. -/
theorem exists_periodic_mem_ball_of_localInverse_iterate_near_return
    {c ζ z : ℂ} {p : ℕ} {R : ℝ} {K : NNReal}
    (hK : K < 1)
    (hcrit : deriv ((quadratic c)^[p]) z ≠ 0)
    (hKderiv : ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ))
    (hgeom : ∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
      g ((quadratic c)^[p] z) = z →
      (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
        HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
          (fun w => (quadratic c)^[p] (g w)) =ᶠ[𝓝 y] id) →
      dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
        Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R) :
    ∃ y ∈ Metric.ball ζ R, (quadratic c)^[p] y = y := by
  obtain ⟨g, r, hrpos, hgz, hdata⟩ :=
    exists_closedBall_localInverse_iterate_branch_data
      (c := c) (z := z) (p := p) (K := (K : ℝ)) hcrit hKderiv
  have hgeom_r := hgeom g r hrpos hgz hdata
  obtain ⟨y, hyclosed, hper⟩ :=
    exists_periodic_point_of_deriv_bound_inverse_branch_near_return_closedBall
      (c := c) (a := (quadratic c)^[p] z) (x := z) (p := p) (r := r) (g := g)
      (K := K) (le_of_lt hrpos) hK hgz hgeom_r.1
      (fun y hy => (hdata y hy).1.hasDerivWithinAt)
      (fun y hy => (hdata y hy).2.1)
      (fun y hy => (hdata y hy).2.2.eq_of_nhds)
  exact ⟨y, hgeom_r.2 hyclosed, hper⟩

/-- Local inverse-function-theorem near-return splice.  Once a noncritical approximate return has
small inverse multiplier, it remains only to prove that the closed ball generated by the local
inverse branch is both trapping and located inside the target ball. -/
theorem exists_strongly_repelling_periodic_mem_ball_of_localInverse_iterate_near_return
    {c ζ z : ℂ} {p : ℕ} {R : ℝ} {K : NNReal}
    (hK : K < 1)
    (hKstrong : (K : ℝ) < ((2 ^ p : ℝ)⁻¹))
    (hcrit : deriv ((quadratic c)^[p]) z ≠ 0)
    (hKderiv : ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ))
    (hgeom : ∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
      g ((quadratic c)^[p] z) = z →
      (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
        HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
          (fun w => (quadratic c)^[p] (g w)) =ᶠ[𝓝 y] id) →
      dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
        Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R) :
    ∃ y ∈ Metric.ball ζ R,
      (quadratic c)^[p] y = y ∧
      (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] y‖ := by
  obtain ⟨g, r, hrpos, hgz, hdata⟩ :=
    exists_closedBall_localInverse_iterate_branch_data
      (c := c) (z := z) (p := p) (K := (K : ℝ)) hcrit hKderiv
  have hgeom_r := hgeom g r hrpos hgz hdata
  obtain ⟨y, hyclosed, hper, hstrong⟩ :=
    exists_strongly_repelling_periodic_of_deriv_bound_inverse_branch_near_return_nhdsRightInverse
      (c := c) (a := (quadratic c)^[p] z) (x := z) (p := p) (r := r) (g := g)
      (K := K) (le_of_lt hrpos) hK hKstrong hgz hgeom_r.1
      (fun y hy => (hdata y hy).1)
      (fun y hy => (hdata y hy).2.1)
      (fun y hy => (hdata y hy).2.2)
  exact ⟨y, hgeom_r.2 hyclosed, hper, hstrong⟩

/-- Density form of the local inverse-function-theorem near-return splice.  The remaining dynamical
input in each frontier ball is a noncritical approximate return with small inverse multiplier and a
quantitative trapping/location estimate for the IFT-generated inverse-branch ball. -/
theorem dense_strongly_repelling_periodic_of_forall_frontier_ball_localInverse_near_return
    {c : ℂ}
    (hbranch : ∀ ζ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ (z : ℂ) (p : ℕ) (K : NNReal),
        K < 1 ∧
        (K : ℝ) < ((2 ^ p : ℝ)⁻¹) ∧
        deriv ((quadratic c)^[p]) z ≠ 0 ∧
        ‖(deriv ((quadratic c)^[p]) z)⁻¹‖ < (K : ℝ) ∧
        (∀ (g : ℂ → ℂ) (r : ℝ), 0 < r →
          g ((quadratic c)^[p] z) = z →
          (∀ y ∈ Metric.closedBall ((quadratic c)^[p] z) r,
            HasDerivAt g (deriv g y) y ∧ ‖deriv g y‖ ≤ (K : ℝ) ∧
              (fun w => (quadratic c)^[p] (g w)) =ᶠ[𝓝 y] id) →
          dist z ((quadratic c)^[p] z) + (K : ℝ) * r ≤ r ∧
            Metric.closedBall ((quadratic c)^[p] z) r ⊆ Metric.ball ζ R)) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖} := by
  apply dense_strongly_repelling_periodic_of_forall_frontier_ball
  intro ζ hζ R hR
  obtain ⟨z, p, K, hK, hKstrong, hcrit, hKderiv, hgeom⟩ := hbranch ζ hζ R hR
  obtain ⟨y, hyball, hper, hstrong⟩ :=
    exists_strongly_repelling_periodic_mem_ball_of_localInverse_iterate_near_return
      (c := c) (ζ := ζ) (z := z) (p := p) (R := R) (K := K)
      hK hKstrong hcrit hKderiv hgeom
  exact ⟨y, hyball, p, hper, hstrong⟩

/-- Contracting inverse branches in every frontier ball give the natural strong-periodic density
statement.  This is the direct bridge from a future inverse-branch construction theorem into the
existing closed-ball hRigid/q62 machinery. -/
theorem dense_strongly_repelling_periodic_of_forall_frontier_ball_contracting_inverse_branch
    {c : ℂ}
    (hbranch : ∀ z ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ (a : ℂ) (p : ℕ) (r : ℝ) (g : ℂ → ℂ) (K : NNReal),
      ∃ hmaps : Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r),
        0 ≤ r ∧
        Metric.closedBall a r ⊆ Metric.ball z R ∧
        ContractingWith K (Set.MapsTo.restrict g (Metric.closedBall a r)
          (Metric.closedBall a r) hmaps) ∧
        (∀ y ∈ Metric.closedBall a r, (quadratic c)^[p] (g y) = y) ∧
        (∀ y ∈ Metric.closedBall a r,
          deriv ((quadratic c)^[p]) (g y) * deriv g y = 1) ∧
        (∀ y ∈ Metric.closedBall a r, ‖deriv g y‖ < ((2 ^ p : ℝ)⁻¹))) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖} := by
  apply dense_strongly_repelling_periodic_of_forall_frontier_ball
  intro z hzfront R hR
  obtain ⟨a, p, r, g, K, hmaps, hr, hball, hcontr, hinv, hderiv_inv, hderiv_lt⟩ :=
    hbranch z hzfront R hR
  obtain ⟨y, hyclosed, hper, hstrong⟩ :=
    exists_strongly_repelling_periodic_of_contracting_inverse_branch_on_closedBall
      hr hmaps hcontr hinv hderiv_inv hderiv_lt
  exact ⟨y, hball hyclosed, p, hper, hstrong⟩

/-- Lipschitz-estimate version of
`dense_strongly_repelling_periodic_of_forall_frontier_ball_contracting_inverse_branch`. -/
theorem dense_strongly_repelling_periodic_of_forall_frontier_ball_lipschitz_inverse_branch
    {c : ℂ}
    (hbranch : ∀ z ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ (a : ℂ) (p : ℕ) (r : ℝ) (g : ℂ → ℂ) (K : NNReal),
        0 ≤ r ∧
        K < 1 ∧
        Metric.closedBall a r ⊆ Metric.ball z R ∧
        Set.MapsTo g (Metric.closedBall a r) (Metric.closedBall a r) ∧
        LipschitzOnWith K g (Metric.closedBall a r) ∧
        (∀ y ∈ Metric.closedBall a r, (quadratic c)^[p] (g y) = y) ∧
        (∀ y ∈ Metric.closedBall a r,
          deriv ((quadratic c)^[p]) (g y) * deriv g y = 1) ∧
        (∀ y ∈ Metric.closedBall a r, ‖deriv g y‖ < ((2 ^ p : ℝ)⁻¹))) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖} := by
  apply dense_strongly_repelling_periodic_of_forall_frontier_ball
  intro z hzfront R hR
  obtain ⟨a, p, r, g, K, hr, hK, hball, hmaps, hlip, hinv, hderiv_inv, hderiv_lt⟩ :=
    hbranch z hzfront R hR
  obtain ⟨y, hyclosed, hper, hstrong⟩ :=
    exists_strongly_repelling_periodic_of_lipschitz_inverse_branch_on_closedBall
      hr hK hmaps hlip hinv hderiv_inv hderiv_lt
  exact ⟨y, hball hyclosed, p, hper, hstrong⟩

/-- Frontier-density form of the near-return inverse-branch bridge.  It reduces the local dynamical
task to producing, in every frontier ball, a regular approximate return whose inverse branch is
Lipschitz with a quantitative trapping inequality. -/
theorem dense_strongly_repelling_periodic_of_forall_frontier_ball_lipschitz_near_return_branch
    {c : ℂ}
    (hbranch : ∀ z ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ (a x : ℂ) (p : ℕ) (r : ℝ) (g : ℂ → ℂ) (K : NNReal),
        0 ≤ r ∧
        K < 1 ∧
        Metric.closedBall a r ⊆ Metric.ball z R ∧
        g a = x ∧
        dist x a + (K : ℝ) * r ≤ r ∧
        LipschitzOnWith K g (Metric.closedBall a r) ∧
        (∀ y ∈ Metric.closedBall a r, (quadratic c)^[p] (g y) = y) ∧
        (∀ y ∈ Metric.closedBall a r,
          deriv ((quadratic c)^[p]) (g y) * deriv g y = 1) ∧
        (∀ y ∈ Metric.closedBall a r, ‖deriv g y‖ < ((2 ^ p : ℝ)⁻¹))) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c)^[k] z‖} := by
  apply dense_strongly_repelling_periodic_of_forall_frontier_ball
  intro z hzfront R hR
  obtain ⟨a, x, p, r, g, K, hr, hK, hball, hga, hclose, hlip, hinv, hderiv_inv,
    hderiv_lt⟩ := hbranch z hzfront R hR
  obtain ⟨y, hyclosed, hper, hstrong⟩ :=
    exists_strongly_repelling_periodic_of_lipschitz_inverse_branch_near_return_closedBall
      hr hK hga hclose hlip hinv hderiv_inv hderiv_lt
  exact ⟨y, hball hyclosed, p, hper, hstrong⟩

end Bottcher
