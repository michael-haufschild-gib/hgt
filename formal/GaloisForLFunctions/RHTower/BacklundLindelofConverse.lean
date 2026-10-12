import GaloisForLFunctions.RHTower.LindelofCriticalLineConvexity
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.HTGeometry.ThreeCircles
import GaloisForLFunctions.HTGeometry.AveragedRadiusSelection

/-!
# Backlund's converse: sparse off-line zeros give the Lindelöf hypothesis

**Theorem** (`lindelofOpen_of_offLineSparse`). If off-line zeros are sparse in Backlund's sense
(`OffLineSparse`: for every `η, L, c > 0`, eventually every window of length `2L` at height `t`
carries at most `c log t` zeros with `|β − ½| > η`), then for every `σ₀ > ½` and `ε > 0`,
`‖ζ(σ + it)‖ ≤ |t|^ε` for `σ ≥ σ₀` and `|t|` large.

**Backlund's theorem** (`offLineSparse_iff_lindelofOpen`): off-line sparsity ⟺ `μ(σ) = 0` for every
`σ > ½`. The forward direction is `offLineSparse_of_lindelofOpen`, through
`offLineSparse_of_eventual_bound` (Jensen's formula on discs of radius `3/2`).

**Unconditional local form** (`local_estimate`). For `0 < δ ≤ ¼` and `t ≥ 6`, let `N` count, with
multiplicity, the zeros of `ζ` in the disc of radius `7/2 − 9δ/8` about `4 + it` (all of them have
`β > ½ + 9δ/8` and `|γ − t| < 4`). Then for `½ + 2δ ≤ σ ≤ 15/4`,

`log‖ζ(σ + it)‖ ≤ N log 8 + log 2 + B₁^{1−w} B₃^{w}`, with `w ≤ θ < 1`,

where `B₁ = O(N + 1)` and `B₃ = O(log|t| + N + 1)`. So a value `‖ζ(σ₀ + it)‖ ≥ |t|^ε` forces
`N ≫_ε log|t|`: large values off the line force dense off-line clusters.

**Proof.** Factor out the zeros: `ζ(z) = Π(z − u)^{D(u)} g(z)` on the disc, with `g` holomorphic and
zero-free (Mathlib `MeromorphicOn.extract_zeros_poles` plus the identity theorem). Bound `g` on
three discs. At the centre, `‖g(4 + it)‖ ∈ [¼·4^{−N}, 2]`. On the inner disc of radius `½`,
`‖g‖ ≤ 2`. On the outer disc, use the maximum principle on a circle whose radius is chosen by
averaging (`exists_mem_Icc_sum_rpow_le`), giving `‖g‖ ≤ O(|t|)·e^{O(N)}`. Borel–Carathéodory and
Hadamard's three circles for `log g` then give the stated interpolation, because the inner ratio
is `e^{O(N)}` while only the outer ratio sees `log|t|`.
-/

open Complex Filter Topology Set Metric

namespace RHTower.BacklundConverse

open GaloisForLFunctions.HTGeometry RHTower.CosineSparseCluster RHTower.LindelofSparse

noncomputable section

/-! ## Three circles, upper form -/

/-- **Two-radius upper bound.** The companion of `norm_lower_bound_of_two_radii`:
`‖f z‖ ≤ ‖f c‖ exp(B₁^{1−w} B₃^{w})`. -/
theorem norm_upper_bound_of_two_radii {f : ℂ → ℂ} {c : ℂ} {ρ R r₁ r₃ : ℝ} (h1 : 0 < r₁)
    (h1ρ : r₁ < ρ) (hρR : ρ ≤ R) (h13 : r₁ < r₃) (h3R : r₃ < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hne : ∀ z ∈ ball c R, f z ≠ 0) {Mi mi M m : ℝ}
    (hMi : ∀ z ∈ ball c ρ, ‖f z‖ ≤ Mi) (hmi0 : 0 < mi) (hmi : mi ≤ ‖f c‖)
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hm0 : 0 < m) (hm : m ≤ ‖f c‖) {z : ℂ}
    (hz1 : r₁ ≤ ‖z - c‖) (hz3 : ‖z - c‖ ≤ r₃) :
    ‖f z‖ ≤ ‖f c‖ * Real.exp
        ((2 * (Real.log (Mi / mi) + 1) * r₁ / (ρ - r₁)) ^
            (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
          (2 * (Real.log (M / m) + 1) * r₃ / (R - r₃)) ^
            ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁))) := by
  have hR : (0 : ℝ) < R := lt_trans (lt_trans h1 h13) h3R
  obtain ⟨g, hgon, hg0, hgeq⟩ := exists_log_on_ball hR hf hne
  have hsub : ball c ρ ⊆ ball c R := ball_subset_ball hρR
  have hinner : ∀ w : ℂ, ‖w - c‖ = r₁ →
      ‖g w‖ ≤ 2 * (Real.log (Mi / mi) + 1) * r₁ / (ρ - r₁) := fun w hw =>
    norm_log_le_of_ball h1.le h1ρ (hgon.mono hsub) hg0 (fun x hx => hgeq x (hsub hx)) hMi hmi0 hmi
      (le_of_eq hw)
  have houter : ∀ w : ℂ, ‖w - c‖ = r₃ →
      ‖g w‖ ≤ 2 * (Real.log (M / m) + 1) * r₃ / (R - r₃) := fun w hw =>
    norm_log_le_of_ball (le_of_lt (lt_trans h1 h13)) h3R hgon hg0 hgeq hM hm0 hm (le_of_eq hw)
  have hbound := norm_le_of_three_circles_center h1 h13 h3R hgon hinner houter hz1 hz3
  have hzmem : z ∈ ball c R := by
    rw [mem_ball_iff_norm]
    exact lt_of_le_of_lt hz3 h3R
  have hmod : ‖f z‖ = ‖f c‖ * Real.exp ((g z).re) := by
    rw [hgeq z hzmem, norm_mul, Complex.norm_exp]
  rw [hmod]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  exact (Complex.re_le_norm _).trans hbound

/-! ## Factoring out the zeros of `ζ` on a disc -/

/-- On a disc in `Re > 0` avoiding `1`, `ζ` is a finite product of its zeros times a zero-free
holomorphic function. -/
theorem exists_zeta_factor_ball {c : ℂ} {R R₂ : ℝ} (hR : 0 < R) (hRR : R < R₂)
    (hB : ∀ z ∈ ball c R₂, 0 < z.re ∧ z ≠ 1) (hc : riemannZeta c ≠ 0) :
    ∃ (S : Finset ℂ) (D : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ u ∈ S, u ∈ ball c R ∧ riemannZeta u = 0 ∧ 1 ≤ D u ∧
        ((D u : ℕ) : ℤ) = (MeromorphicOn.divisor riemannZeta (ball c R)) u) ∧
      AnalyticOnNhd ℂ g (ball c R) ∧ (∀ z ∈ ball c R, g z ≠ 0) ∧
      ∀ z ∈ ball c R, riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z := by
  classical
  set U := ball c R with hU
  have hana2 : AnalyticOnNhd ℂ riemannZeta (ball c R₂) :=
    analyticOnNhd_riemannZeta_of_ne_one fun z hz => (hB z hz).2
  have hsubU : U ⊆ ball c R₂ := ball_subset_ball hRR.le
  have hana : AnalyticOnNhd ℂ riemannZeta U := hana2.mono hsubU
  have hmero : MeromorphicOn riemannZeta U := hana.meromorphicOn
  have hconn : IsPreconnected U := (convex_ball c R).isPreconnected
  have hcU : c ∈ U := mem_ball_self hR
  have hordc : analyticOrderAt riemannZeta c ≠ ⊤ := by
    rw [(hana c hcU).analyticOrderAt_eq_zero.mpr hc]; exact WithTop.zero_ne_top
  have hord : ∀ u : U, meromorphicOrderAt riemannZeta u ≠ ⊤ := by
    intro ⟨u, hu⟩
    rw [(hana u hu).meromorphicOrderAt_eq]
    have := hana.analyticOrderAt_ne_top_of_isPreconnected hconn hcU hu hordc
    simpa using this
  -- finiteness of the divisor through the closed disc
  have hsubK : closedBall c R ⊆ ball c R₂ := closedBall_subset_ball hRR
  have hanaK : AnalyticOnNhd ℂ riemannZeta (closedBall c R) := hana2.mono hsubK
  have hfinK := (MeromorphicOn.divisor riemannZeta (closedBall c R)).finiteSupport
    (isCompact_closedBall c R)
  have hfin : (MeromorphicOn.divisor riemannZeta U).support.Finite := by
    refine hfinK.subset fun u hu => ?_
    have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain hu
    have huK : u ∈ closedBall c R := ball_subset_closedBall huU
    simp only [Function.mem_support] at hu ⊢
    rwa [MeromorphicOn.divisor_apply hmero huU,
      ← MeromorphicOn.divisor_apply hanaK.meromorphicOn huK] at hu
  obtain ⟨g, hgan, hgne, hgeq⟩ := hmero.extract_zeros_poles hord hfin
  set Dz := MeromorphicOn.divisor riemannZeta U with hDz
  have hDnn : ∀ u, 0 ≤ Dz u := by
    intro u
    by_cases huU : u ∈ U
    · rw [hDz, MeromorphicOn.divisor_apply hmero huU, (hana u huU).meromorphicOrderAt_eq,
        WithTop.untop₀_nonneg]
      cases h : analyticOrderAt riemannZeta u with
      | top => simp
      | coe n => simp
    · have h0 : Dz u = 0 := by
        by_contra hne
        exact huU (Dz.supportWithinDomain hne)
      rw [h0]
  set S := hfin.toFinset with hS
  set D : ℂ → ℕ := fun u => (Dz u).toNat with hD
  have hDcast : ∀ u, ((D u : ℕ) : ℤ) = Dz u := fun u => Int.toNat_of_nonneg (hDnn u)
  -- the finite product
  have hprod : ∀ z, (∏ᶠ u, (fun x => x - u) ^ Dz u) z = ∏ u ∈ S, (z - u) ^ D u := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · rw [Finset.prod_apply]
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [Pi.pow_apply, ← hDcast u, zpow_natCast]
    · intro u hu
      rw [hS, Set.Finite.coe_toFinset, Function.mem_support]
      intro h0
      apply hu
      simp only [h0, zpow_zero]
  refine ⟨S, D, g, fun u hu => ?_, hgan, fun z hz => hgne ⟨z, hz⟩, ?_⟩
  · rw [hS, Set.Finite.mem_toFinset, Function.mem_support] at hu
    have huU : u ∈ U := Dz.supportWithinDomain hu
    refine ⟨huU, ?_, ?_, hDcast u⟩
    · by_contra hne
      apply hu
      rw [hDz, MeromorphicOn.divisor_apply hmero huU, (hana u huU).meromorphicOrderAt_eq,
        (hana u huU).analyticOrderAt_eq_zero.mpr hne]
      rfl
    · have hpos : 0 < Dz u := lt_of_le_of_ne (hDnn u) (Ne.symm hu)
      have : (1 : ℤ) ≤ (D u : ℤ) := by rw [hDcast]; omega
      exact_mod_cast this
  · -- identity theorem from equality off a discrete set
    have hRHS : AnalyticOnNhd ℂ (fun z => (∏ u ∈ S, (z - u) ^ D u) * g z) U := by
      intro z hz
      refine AnalyticAt.mul ?_ (hgan z hz)
      have hd : Differentiable ℂ fun z : ℂ => ∏ u ∈ S, (z - u) ^ D u := by fun_prop
      exact hd.analyticAt z
    have hfreq : ∃ᶠ z in 𝓝[≠] c, riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z := by
      have hmem : {x | riemannZeta x = ((∏ᶠ u, (fun x => x - u) ^ Dz u) • g) x} ∈
          codiscreteWithin U := hgeq
      rw [mem_codiscreteWithin] at hmem
      have hdisj := hmem c hcU
      have hev : ∀ᶠ z in 𝓝[≠] c, z ∉ U \ {x | riemannZeta x =
          ((∏ᶠ u, (fun x => x - u) ^ Dz u) • g) x} :=
        (Filter.disjoint_principal_right.mp hdisj)
      have hevU : ∀ᶠ z in 𝓝[≠] c, z ∈ U :=
        eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds hcU)
      refine (hev.and hevU).frequently.mono fun z ⟨h1, h2⟩ => ?_
      have h3 : riemannZeta z = ((∏ᶠ u, (fun x => x - u) ^ Dz u) • g) z := by
        by_contra h
        exact h1 ⟨h2, h⟩
      rw [h3, Pi.smul_apply', smul_eq_mul, hprod z]
    exact fun z hz => hana.eqOn_of_preconnected_of_frequently_eq hRHS hconn hcU hfreq hz

/-! ## The outer bound by the maximum principle on an averaged circle -/

theorem inv_le_exp_two_rpow {x : ℝ} (hx : 0 < x) : x⁻¹ ≤ Real.exp (2 * x ^ (-(1 / 2) : ℝ)) := by
  set y := x ^ (-(1 / 2) : ℝ) with hy
  have hy0 : 0 < y := Real.rpow_pos_of_pos hx _
  have hy2 : y ^ 2 = x⁻¹ := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    rw [Real.rpow_neg_one]
  rw [← hy2]
  have := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * y)
  nlinarith

/-- **Weighted averaged radius.** For finitely many centres `a u` with multiplicities `D u` there
is a radius in `[ℓ + r/2, ℓ + r]` avoiding every centre with
`Σ D(u)|R* − a u|^{−1/2} ≤ (Σ D u)·3√(r/2)/(r/2)`. -/
theorem exists_radius_weighted (S : Finset ℂ) (D : ℂ → ℕ) (a : ℂ → ℝ) (ℓ : ℝ) {r : ℝ}
    (hr : 0 < r) :
    ∃ R, ℓ + r / 2 ≤ R ∧ R ≤ ℓ + r ∧ (∀ u ∈ S, 1 ≤ D u → R ≠ a u) ∧
      ∑ u ∈ S, (D u : ℝ) * |R - a u| ^ (-(1 / 2) : ℝ) ≤
        (∑ u ∈ S, (D u : ℝ)) * (3 * Real.sqrt (r / 2) / (r / 2)) := by
  classical
  set J : Finset (Σ _u : ℂ, ℕ) := S.sigma fun u => Finset.range (D u) with hJ
  obtain ⟨x, ⟨hx1, hx2⟩, hxa, hsum⟩ :=
    exists_mem_Icc_sum_rpow_le J (fun j => a j.1 - ℓ) hr
  refine ⟨ℓ + x, by linarith, by linarith, fun u hu hD h => ?_, ?_⟩
  · have hmem : (⟨u, 0⟩ : Σ _u : ℂ, ℕ) ∈ J := by
      rw [hJ]; simp only [Finset.mem_sigma, Finset.mem_range]; exact ⟨hu, hD⟩
    exact hxa _ hmem (by simp only; linarith)
  · have hJsum : ∑ j ∈ J, |x - (a j.1 - ℓ)| ^ (-(1 / 2) : ℝ) =
        ∑ u ∈ S, (D u : ℝ) * |ℓ + x - a u| ^ (-(1 / 2) : ℝ) := by
      rw [hJ, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 2
      ring_nf
    have hJcard : (J.card : ℝ) = ∑ u ∈ S, (D u : ℝ) := by
      rw [hJ, Finset.card_sigma]
      push_cast
      simp
    rw [← hJsum, ← hJcard]
    exact hsum

/-- **Outer bound.** If `ζ = Π(z − u)^{D u}·g` on `ball c R_U`, `g` is holomorphic there,
`R < R* < R_U`, the circle of radius `R*` avoids every zero, and `‖ζ‖ ≤ Z₀` on it, then
`‖g‖ ≤ Z₀ exp(2Σ D(u)|R* − |u − c||^{−1/2})` on `ball c R`. -/
theorem norm_le_on_ball_of_factor {c : ℂ} {R Rs RU Z₀ : ℝ} (S : Finset ℂ) (D : ℂ → ℕ)
    {g : ℂ → ℂ} (hR : 0 < R) (hRs : R ≤ Rs) (hRsU : Rs < RU)
    (hg : AnalyticOnNhd ℂ g (ball c RU))
    (hfac : ∀ z ∈ ball c RU, riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z)
    (hsep : ∀ u ∈ S, Rs ≠ ‖u - c‖) (hZ : ∀ w ∈ sphere c Rs, ‖riemannZeta w‖ ≤ Z₀) :
    ∀ z ∈ ball c R, ‖g z‖ ≤
      Z₀ * Real.exp (2 * ∑ u ∈ S, (D u : ℝ) * |Rs - ‖u - c‖| ^ (-(1 / 2) : ℝ)) := by
  intro z hz
  have hRs0 : 0 < Rs := lt_of_lt_of_le hR hRs
  have hsub : closedBall c Rs ⊆ ball c RU := closedBall_subset_ball hRsU
  have hdc : DiffContOnCl ℂ g (ball c Rs) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hRs0.ne']
    exact fun w hw => (hg w (hsub hw)).differentiableAt.differentiableWithinAt
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc ?_ ?_
  · intro w hw
    rw [frontier_ball c hRs0.ne'] at hw
    have hwU : w ∈ ball c RU := hsub (sphere_subset_closedBall hw)
    have hw' : ‖w - c‖ = Rs := by rwa [mem_sphere, dist_eq_norm] at hw
    have hdist : ∀ u ∈ S, |Rs - ‖u - c‖| ≤ ‖w - u‖ := by
      intro u _
      rw [← hw']
      have := abs_norm_sub_norm_le (w - c) (u - c)
      rwa [show w - c - (u - c) = w - u by ring] at this
    have hpos : ∀ u ∈ S, 0 < |Rs - ‖u - c‖| := fun u hu =>
      abs_pos.mpr (sub_ne_zero.mpr (hsep u hu))
    have hprodpos : ∀ u ∈ S, 0 < ‖w - u‖ := fun u hu => lt_of_lt_of_le (hpos u hu) (hdist u hu)
    have hfw := hfac w hwU
    have hP : ‖∏ u ∈ S, (w - u) ^ D u‖ = ∏ u ∈ S, ‖w - u‖ ^ D u := by
      rw [norm_prod]; simp [norm_pow]
    have hPpos : 0 < ∏ u ∈ S, ‖w - u‖ ^ D u :=
      Finset.prod_pos fun u hu => pow_pos (hprodpos u hu) _
    have hgw : ‖g w‖ = ‖riemannZeta w‖ / ∏ u ∈ S, ‖w - u‖ ^ D u := by
      rw [hfw, norm_mul, hP, mul_div_cancel_left₀ _ hPpos.ne']
    rw [hgw, div_eq_mul_inv]
    refine mul_le_mul (hZ w hw) ?_ (inv_nonneg.mpr hPpos.le)
      ((norm_nonneg _).trans (hZ w hw))
    rw [← Finset.prod_inv_distrib, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun u _ => by positivity) fun u hu => ?_
    rw [← inv_pow, show 2 * ((D u : ℝ) * |Rs - ‖u - c‖| ^ (-(1 / 2) : ℝ)) =
      (D u : ℝ) * (2 * |Rs - ‖u - c‖| ^ (-(1 / 2) : ℝ)) by ring, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    calc ‖w - u‖⁻¹ ≤ |Rs - ‖u - c‖|⁻¹ := inv_anti₀ (hpos u hu) (hdist u hu)
      _ ≤ Real.exp (2 * |Rs - ‖u - c‖| ^ (-(1 / 2) : ℝ)) := inv_le_exp_two_rpow (hpos u hu)
  · rw [closure_ball c hRs0.ne']
    exact closedBall_subset_closedBall hRs (ball_subset_closedBall hz)

/-! ## Counting the extracted zeros as zero copies -/

/-- The extracted zeros, with multiplicity, are a finite family of zero copies of `ξ`. -/
theorem exists_copies_of_factor {c : ℂ} {R : ℝ} (S : Finset ℂ) (D : ℂ → ℕ)
    (hB : ∀ z ∈ ball c R, 0 < z.re ∧ z ≠ 1)
    (hS : ∀ u ∈ S, u ∈ ball c R ∧ riemannZeta u = 0 ∧ 1 ≤ D u ∧
      ((D u : ℕ) : ℤ) = (MeromorphicOn.divisor riemannZeta (ball c R)) u) :
    ∃ F : Finset XiZeroCopy, (∀ q ∈ F, ((q.1 : ℂ)) ∈ S) ∧ F.card = ∑ u ∈ S, D u := by
  classical
  have hana : AnalyticOnNhd ℂ riemannZeta (ball c R) :=
    analyticOnNhd_riemannZeta_of_ne_one fun z hz => (hB z hz).2
  have hxi : ∀ u ∈ S, (MeromorphicOn.divisor xi Set.univ) u = (D u : ℤ) := by
    intro u hu
    obtain ⟨huU, -, -, hDu⟩ := hS u hu
    rw [hDu, MeromorphicOn.divisor_apply xi_meromorphicOn_univ (Set.mem_univ u),
      MeromorphicOn.divisor_apply hana.meromorphicOn huU,
      meromorphicOrderAt_xi_eq_zeta (hB u huU).1 (hB u huU).2]
  set p : ℂ → Prop := fun u => u ∈ (MeromorphicOn.divisor xi Set.univ).support with hp
  have hpS : ∀ u ∈ S, p u := by
    intro u hu
    simp only [hp, Function.mem_support, hxi u hu]
    have := (hS u hu).2.2.1
    omega
  set S' : Finset XiDivisorSupport := S.subtype p with hS'
  refine ⟨S'.sigma fun _ => Finset.univ, fun q hq => ?_, ?_⟩
  · rw [Finset.mem_sigma] at hq
    exact (Finset.mem_subtype.mp hq.1)
  · rw [Finset.card_sigma]
    simp only [Finset.card_univ, Fintype.card_fin]
    have hmap : ∑ ρ ∈ S', ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat =
        ∑ u ∈ S'.map (Function.Embedding.subtype p),
          ((MeromorphicOn.divisor xi Set.univ) u).toNat := by
      rw [Finset.sum_map]; rfl
    rw [hmap, hS', Finset.subtype_map, Finset.filter_true_of_mem hpS]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hxi u hu, Int.toNat_natCast]

/-! ## The final asymptotic inequality -/

/-- With `N ≤ κX`, `B₁ ≤ C₁ + 3N`, `B₃ ≤ βX`, `0 ≤ w ≤ θ < 1`, and `κ` small enough, the three-circles
exponent `N log 8 + log 2 + B₁^{1−w}B₃^{w}` is at most `εX` once `X` is large. -/
theorem final_exponent_le {N X κ ε θ w β C₁ B₁ B₃ : ℝ} (hθ1 : θ < 1) (hw0 : 0 ≤ w)
    (hwθ : w ≤ θ) (hβ : 1 ≤ β) (hκ0 : 0 < κ) (hκ6 : 6 * κ ≤ 1)
    (hκa : κ * Real.log 8 ≤ ε / 4) (hκb : (6 * κ) ^ (1 - θ) * β ≤ ε / 4)
    (hX1 : 1 ≤ X) (hXC : C₁ ≤ 3 * κ * X) (hX2 : Real.log 2 ≤ ε / 2 * X)
    (hN : N ≤ κ * X) (hB₁0 : 0 ≤ B₁) (hB₁ : B₁ ≤ C₁ + 3 * N)
    (hB₃0 : 0 ≤ B₃) (hB₃ : B₃ ≤ β * X) :
    N * Real.log 8 + Real.log 2 + B₁ ^ (1 - w) * B₃ ^ w ≤ ε * X := by
  have hX0 : 0 < X := by linarith
  have hB₁' : B₁ ≤ 6 * κ * X := by nlinarith
  have hw1 : w ≤ 1 := by linarith
  have h1 : B₁ ^ (1 - w) ≤ (6 * κ * X) ^ (1 - w) :=
    Real.rpow_le_rpow hB₁0 hB₁' (by linarith)
  have h2 : B₃ ^ w ≤ (β * X) ^ w := Real.rpow_le_rpow hB₃0 hB₃ hw0
  have h3 : (6 * κ * X) ^ (1 - w) * (β * X) ^ w = (6 * κ) ^ (1 - w) * β ^ w * X := by
    rw [Real.mul_rpow (by positivity) hX0.le, Real.mul_rpow (by positivity) hX0.le]
    have : X ^ (1 - w) * X ^ w = X := by
      rw [← Real.rpow_add hX0]; simp
    calc (6 * κ) ^ (1 - w) * X ^ (1 - w) * (β ^ w * X ^ w)
        = (6 * κ) ^ (1 - w) * β ^ w * (X ^ (1 - w) * X ^ w) := by ring
      _ = _ := by rw [this]
  have h4 : (6 * κ) ^ (1 - w) ≤ (6 * κ) ^ (1 - θ) :=
    Real.rpow_le_rpow_of_exponent_ge (by positivity) hκ6 (by linarith)
  have h5 : β ^ w ≤ β := by
    calc β ^ w ≤ β ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hβ hw1
      _ = β := Real.rpow_one β
  have h6 : B₁ ^ (1 - w) * B₃ ^ w ≤ (6 * κ) ^ (1 - θ) * β * X := by
    calc B₁ ^ (1 - w) * B₃ ^ w ≤ (6 * κ * X) ^ (1 - w) * (β * X) ^ w :=
          mul_le_mul h1 h2 (Real.rpow_nonneg hB₃0 _) (Real.rpow_nonneg (by positivity) _)
      _ = (6 * κ) ^ (1 - w) * β ^ w * X := h3
      _ ≤ (6 * κ) ^ (1 - θ) * β * X := by
          apply mul_le_mul_of_nonneg_right _ hX0.le
          exact mul_le_mul h4 h5 (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by positivity) _)
  have h7 : N * Real.log 8 ≤ κ * X * Real.log 8 :=
    mul_le_mul_of_nonneg_right hN (Real.log_nonneg (by norm_num))
  have h8 : κ * X * Real.log 8 ≤ ε / 4 * X := by nlinarith
  have h9 : (6 * κ) ^ (1 - θ) * β * X ≤ ε / 4 * X := mul_le_mul_of_nonneg_right hκb hX0.le
  linarith

/-! ## Small helpers for the factorization -/

theorem norm_eq_div_of_factor {S : Finset ℂ} {D : ℂ → ℕ} {g : ℂ → ℂ} {z : ℂ}
    (hfz : riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z)
    (hP : 0 < ∏ u ∈ S, ‖z - u‖ ^ D u) :
    ‖g z‖ = ‖riemannZeta z‖ / ∏ u ∈ S, ‖z - u‖ ^ D u := by
  have h : ‖riemannZeta z‖ = (∏ u ∈ S, ‖z - u‖ ^ D u) * ‖g z‖ := by
    rw [hfz, norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun u _ => norm_pow _ _
  rw [h, mul_div_cancel_left₀ _ hP.ne']

theorem norm_zeta_eq_of_factor {S : Finset ℂ} {D : ℂ → ℕ} {g : ℂ → ℂ} {z : ℂ}
    (hfz : riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z) :
    ‖riemannZeta z‖ = (∏ u ∈ S, ‖z - u‖ ^ D u) * ‖g z‖ := by
  rw [hfz, norm_mul, norm_prod]
  congr 1
  exact Finset.prod_congr rfl fun u _ => norm_pow _ _

theorem one_le_prod_pow {S : Finset ℂ} {D : ℂ → ℕ} {f : ℂ → ℝ} (h : ∀ u ∈ S, 1 ≤ f u) :
    1 ≤ ∏ u ∈ S, f u ^ D u := by
  calc (1 : ℝ) = ∏ _u ∈ S, (1 : ℝ) := by simp
    _ ≤ ∏ u ∈ S, f u ^ D u :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) fun u hu => one_le_pow₀ (h u hu)

theorem prod_pow_le_pow_sum {S : Finset ℂ} {D : ℂ → ℕ} {f : ℂ → ℝ} {b : ℝ}
    (h0 : ∀ u ∈ S, 0 ≤ f u) (h : ∀ u ∈ S, f u ≤ b) :
    ∏ u ∈ S, f u ^ D u ≤ b ^ (∑ u ∈ S, D u) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun u hu => pow_nonneg (h0 u hu) _) fun u hu =>
    pow_le_pow_left₀ (h0 u hu) (h u hu) _

theorem log_two_div_quarter_div (n : ℕ) :
    Real.log (2 / (1 / 4 / (4 : ℝ) ^ n)) = Real.log 8 + n * Real.log 4 := by
  have h : (2 : ℝ) / (1 / 4 / 4 ^ n) = 8 * 4 ^ n := by field_simp; ring
  rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]

theorem log_div_quarter_div {Z E : ℝ} (hZ : 0 < Z) (n : ℕ) :
    Real.log (Z * Real.exp E / (1 / 4 / (4 : ℝ) ^ n)) =
      Real.log Z + E + Real.log 4 + n * Real.log 4 := by
  have h : Z * Real.exp E / (1 / 4 / (4 : ℝ) ^ n) = Z * Real.exp E * 4 * 4 ^ n := by
    field_simp
  rw [h, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by norm_num),
    Real.log_mul hZ.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]

theorem log_four_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)

theorem log_eight_nonneg : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)

theorem log_four_le : Real.log 4 ≤ 3 / 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / Real.exp 1 by positivity)
  rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp] at h1
  have h2 : (4 : ℝ) / Real.exp 1 ≤ 3 / 2 := by
    rw [div_le_iff₀ (Real.exp_pos 1)]; linarith [Real.exp_one_gt_d9]
  linarith

/-! ## The local estimate at a positive height -/

/-- The centre `4 + it` of the three circles. -/
def centre (t : ℝ) : ℂ := (4 : ℂ) + (t : ℂ) * I

theorem centre_re (t : ℝ) : (centre t).re = 4 := by simp [centre]

theorem centre_im (t : ℝ) : (centre t).im = t := by simp [centre]

/-- **Step 1: factor out the zeros.** On the disc of radius `7/2 − 9δ/8` about `4 + it`, `ζ` is a
finite product of its zeros times a zero-free holomorphic `g`. Every extracted zero has
`½ + 9δ/8 < Re u < 1` and `|Im u − t| < 4`, and the zeros with multiplicity form a family of zero
copies. -/
theorem step_factor {δ t : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (ht : 6 ≤ t) :
    ∃ (S : Finset ℂ) (D : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ z ∈ ball (centre t) (7 / 2 - 9 * δ / 8),
        riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z) ∧
      AnalyticOnNhd ℂ g (ball (centre t) (7 / 2 - 9 * δ / 8)) ∧
      (∀ z ∈ ball (centre t) (7 / 2 - 9 * δ / 8), g z ≠ 0) ∧
      (∀ u ∈ S, 1 / 2 + 9 * δ / 8 < u.re ∧ u.re < 1 ∧
        ‖u - centre t‖ < 7 / 2 - 9 * δ / 8 ∧ |u.im - t| < 4 ∧ 1 ≤ D u) ∧
      ∃ F : Finset XiZeroCopy, (∀ q ∈ F, |(xiSpectralPoint q).re - t| ≤ 4 ∧
        δ < |(xiSpectralPoint q).im|) ∧ F.card = ∑ u ∈ S, D u := by
  classical
  set c := centre t with hc
  have hcre : c.re = 4 := centre_re t
  have hcim : c.im = t := centre_im t
  have hB : ∀ z ∈ ball c (7 / 2 - δ), 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := Complex.abs_re_le_norm (z - c)
    have him := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    have h1 := abs_lt.mp (lt_of_le_of_lt hre hz)
    have h2 := abs_lt.mp (lt_of_le_of_lt him hz)
    refine ⟨by linarith, fun h => ?_⟩
    rw [h] at h2
    simp at h2
    linarith [h2.1]
  have hcz : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; norm_num)
  obtain ⟨S, D, g, hS, hg, hgne, hfac⟩ := exists_zeta_factor_ball
    (R := 7 / 2 - 9 * δ / 8) (R₂ := 7 / 2 - δ) (by linarith) (by linarith) hB hcz
  have hBU : ∀ z ∈ ball c (7 / 2 - 9 * δ / 8), 0 < z.re ∧ z ≠ 1 := fun z hz =>
    hB z (ball_subset_ball (by linarith) hz)
  obtain ⟨F, hF, hFcard⟩ := exists_copies_of_factor S D hBU hS
  have hzero : ∀ u ∈ S, 1 / 2 + 9 * δ / 8 < u.re ∧ u.re < 1 ∧
      ‖u - c‖ < 7 / 2 - 9 * δ / 8 ∧ |u.im - t| < 4 ∧ 1 ≤ D u := by
    intro u hu
    obtain ⟨huU, hu0, hDu, -⟩ := hS u hu
    rw [mem_ball, dist_eq_norm] at huU
    have hre := Complex.abs_re_le_norm (u - c)
    have him := Complex.abs_im_le_norm (u - c)
    rw [Complex.sub_re, hcre] at hre
    rw [Complex.sub_im, hcim] at him
    have h1 := abs_lt.mp (lt_of_le_of_lt hre huU)
    have h2 := abs_lt.mp (lt_of_le_of_lt him huU)
    have hlt1 : u.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hu0
    refine ⟨by linarith, hlt1, huU, ?_, hDu⟩
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨S, D, g, hfac, hg, hgne, hzero, F, fun q hq => ?_, hFcard⟩
  obtain ⟨h1, -, -, h4, -⟩ := hzero _ (hF q hq)
  rw [spectral_re_eq, spectral_im_eq]
  refine ⟨h4.le, ?_⟩
  rw [abs_of_neg (by linarith)]
  linarith

/-- **Step 2: the outer bound.** On the disc of radius `7/2 − 11δ/8`,
`‖g‖ ≤ (18 + 4t) exp(2 N K)`, with `N` the number of extracted zeros and `K = 3√(δ/8)/(δ/8)`. -/
theorem step_outer {δ t : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (ht : 6 ≤ t)
    {S : Finset ℂ} {D : ℂ → ℕ} {g : ℂ → ℂ}
    (hfac : ∀ z ∈ ball (centre t) (7 / 2 - 9 * δ / 8),
      riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z)
    (hg : AnalyticOnNhd ℂ g (ball (centre t) (7 / 2 - 9 * δ / 8)))
    (hzero : ∀ u ∈ S, 1 ≤ D u) :
    ∀ z ∈ ball (centre t) (7 / 2 - 11 * δ / 8), ‖g z‖ ≤
      (18 + 4 * t) * Real.exp (2 * (∑ u ∈ S, (D u : ℝ)) * (3 * Real.sqrt (δ / 8) / (δ / 8))) := by
  set c := centre t with hc
  have hcre : c.re = 4 := centre_re t
  have hcim : c.im = t := centre_im t
  obtain ⟨Rs, hRs1, hRs2, hsep0, hsumR⟩ := exists_radius_weighted S D (fun u => ‖u - c‖)
    (7 / 2 - 9 * δ / 8 - 3 * δ / 8) (r := δ / 4) (by positivity)
  have hsep : ∀ u ∈ S, Rs ≠ ‖u - c‖ := fun u hu => hsep0 u hu (hzero u hu)
  have hZ : ∀ w ∈ sphere c Rs, ‖riemannZeta w‖ ≤ 18 + 4 * t := by
    intro w hw
    rw [mem_sphere, dist_eq_norm] at hw
    have hre := Complex.abs_re_le_norm (w - c)
    have him := Complex.abs_im_le_norm (w - c)
    rw [Complex.sub_re, hcre, hw] at hre
    rw [Complex.sub_im, hcim, hw] at him
    have h1 := abs_le.mp hre
    have h2 := abs_le.mp him
    have himw : 2 ≤ |w.im| := by rw [le_abs]; left; linarith
    rcases le_or_gt w.re 2 with hw2 | hw2
    · have := norm_riemannZeta_le_linear (by linarith) hw2 himw
      have : |w.im| ≤ t + 4 := by rw [abs_le]; constructor <;> linarith
      linarith
    · have := Sieve.norm_riemannZeta_le (s := w) (by linarith)
      have : 1 / (w.re - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
  intro z hz
  refine (norm_le_on_ball_of_factor S D (by linarith) (by linarith) (by linarith) hg hfac hsep hZ
    z hz).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
  have hrK : 3 * Real.sqrt (δ / 4 / 2) / (δ / 4 / 2) = 3 * Real.sqrt (δ / 8) / (δ / 8) := by
    rw [show δ / 4 / 2 = δ / 8 by ring]
  rw [hrK] at hsumR
  linarith

/-- **Step 3: the centre and the inner disc.** `¼·4^{−N} ≤ ‖g(4 + it)‖ ≤ 2`, and `‖g‖ ≤ 2` on the disc
of radius `½`. -/
theorem step_inner {δ t : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {S : Finset ℂ} {D : ℂ → ℕ} {g : ℂ → ℂ}
    (hfac : ∀ z ∈ ball (centre t) (7 / 2 - 9 * δ / 8),
      riemannZeta z = (∏ u ∈ S, (z - u) ^ D u) * g z)
    (hzero : ∀ u ∈ S, u.re < 1 ∧ ‖u - centre t‖ < 7 / 2 - 9 * δ / 8) :
    1 / 4 / 4 ^ (∑ u ∈ S, D u) ≤ ‖g (centre t)‖ ∧ ‖g (centre t)‖ ≤ 2 ∧
      ∀ z ∈ ball (centre t) (1 / 2), ‖g z‖ ≤ 2 := by
  set c := centre t with hc
  have hcre : c.re = 4 := centre_re t
  have hcU : c ∈ ball c (7 / 2 - 9 * δ / 8) := mem_ball_self (by linarith)
  have hdist_cu : ∀ u ∈ S, 3 ≤ ‖c - u‖ ∧ ‖c - u‖ ≤ 4 := by
    intro u hu
    obtain ⟨h2, h3⟩ := hzero u hu
    refine ⟨?_, ?_⟩
    · have := Complex.abs_re_le_norm (c - u)
      rw [Complex.sub_re, hcre, abs_of_pos (by linarith)] at this
      linarith
    · rw [norm_sub_rev]; linarith
  have hPc_le : ∏ u ∈ S, ‖c - u‖ ^ D u ≤ 4 ^ (∑ u ∈ S, D u) :=
    prod_pow_le_pow_sum (fun u _ => norm_nonneg _) fun u hu => (hdist_cu u hu).2
  have hPc_ge : 1 ≤ ∏ u ∈ S, ‖c - u‖ ^ D u :=
    one_le_prod_pow fun u hu => by linarith [(hdist_cu u hu).1]
  have hPc_pos : 0 < ∏ u ∈ S, ‖c - u‖ ^ D u := by linarith
  have hnormgc := norm_eq_div_of_factor (hfac c hcU) hPc_pos
  have hζc1 : 1 / 4 ≤ ‖riemannZeta c‖ := norm_riemannZeta_ge_of_two_le_re (by rw [hcre]; norm_num)
  have hζc2 : ‖riemannZeta c‖ ≤ 2 := by
    have := Sieve.norm_riemannZeta_le (s := c) (by rw [hcre]; norm_num)
    rw [hcre] at this; norm_num at this; linarith
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [hnormgc]
    exact div_le_div₀ (by positivity) hζc1 hPc_pos hPc_le
  · rw [hnormgc]
    exact (div_le_self (norm_nonneg _) hPc_ge).trans hζc2
  · have hzU : z ∈ ball c (7 / 2 - 9 * δ / 8) := ball_subset_ball (by linarith) hz
    rw [mem_ball, dist_eq_norm] at hz
    have hre := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hcre] at hre
    have hzre := abs_lt.mp (lt_of_le_of_lt hre hz)
    have hz35 : 7 / 2 < z.re := by linarith only [hzre.1]
    have hPz : 1 ≤ ∏ u ∈ S, ‖z - u‖ ^ D u := one_le_prod_pow fun u hu => by
      have h1 := Complex.abs_re_le_norm (z - u)
      rw [Complex.sub_re] at h1
      have hur := (hzero u hu).1
      rw [abs_of_pos (by linarith only [hz35, hur])] at h1
      linarith only [h1, hz35, hur]
    have hζz : ‖riemannZeta z‖ ≤ 2 := by
      have h1 := Sieve.norm_riemannZeta_le (s := z) (by linarith only [hz35])
      have h2 : 1 / (z.re - 1) ≤ 1 := by
        rw [div_le_one (by linarith only [hz35])]; linarith only [hz35]
      linarith only [h1, h2]
    rw [norm_eq_div_of_factor (hfac z hzU) (by linarith only [hPz])]
    exact (div_le_self (norm_nonneg _) hPz).trans hζz

/-- **Local Backlund estimate.** For `0 < δ ≤ ¼` and `t ≥ 6`, every `σ` with `½ + 2δ ≤ σ ≤ 15/4`
satisfies `‖ζ(σ + it)‖ ≤ 8^N · 2 · exp(B₁^{1−w} B₃^{w})`. Here `N` is the size of a family of zero
copies with `|γ − t| ≤ 4` and `|β − ½| > δ`, `B₁ ≤ 2(log 8 + 1) + 3N`,
`B₃ ≤ (16r₃/δ)(log(18 + 4t) + (2K + log 4)N + log 4 + 1)` and `0 ≤ w ≤ θ`, where
`r₃ = 7/2 − 3δ/2`, `K = 3√(δ/8)/(δ/8)` and `θ = (log(7/2 − 2δ) + log 4)/(log r₃ + log 4) < 1`. -/
theorem local_estimate {δ t σ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (ht : 6 ≤ t)
    (hσ1 : 1 / 2 + 2 * δ ≤ σ) (hσ2 : σ ≤ 15 / 4) :
    ∃ F : Finset XiZeroCopy, (∀ q ∈ F, |(xiSpectralPoint q).re - t| ≤ 4 ∧
        δ < |(xiSpectralPoint q).im|) ∧
      ∃ B₁ B₃ w : ℝ, 0 ≤ B₁ ∧ B₁ ≤ 2 * (Real.log 8 + 1) + 3 * F.card ∧ 0 ≤ B₃ ∧
        B₃ ≤ 16 * (7 / 2 - 3 * δ / 2) / δ * (Real.log (18 + 4 * t) +
          (2 * (3 * Real.sqrt (δ / 8) / (δ / 8)) + Real.log 4) * F.card + Real.log 4 + 1) ∧
        0 ≤ w ∧ w ≤ (Real.log (7 / 2 - 2 * δ) - Real.log (1 / 4)) /
          (Real.log (7 / 2 - 3 * δ / 2) - Real.log (1 / 4)) ∧
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          8 ^ F.card * 2 * Real.exp (B₁ ^ (1 - w) * B₃ ^ w) := by
  obtain ⟨S, D, g, hfac, hg, hgne, hzero, F, hF, hFcard⟩ := step_factor hδ hδ4 ht
  refine ⟨F, hF, ?_⟩
  have hNcast : (∑ u ∈ S, (D u : ℝ)) = (F.card : ℝ) := by rw [hFcard]; push_cast; rfl
  have hout := step_outer hδ hδ4 ht hfac hg fun u hu => (hzero u hu).2.2.2.2
  rw [hNcast] at hout
  obtain ⟨hm, hgc2, hMi⟩ := step_inner hδ hδ4 hfac fun u hu => ⟨(hzero u hu).2.1, (hzero u hu).2.2.1⟩
  rw [← hFcard] at hm
  set c := centre t with hc
  set K := 3 * Real.sqrt (δ / 8) / (δ / 8) with hK
  clear_value c K
  set m : ℝ := 1 / 4 / 4 ^ F.card with hm_def
  have hm0 : 0 < m := by positivity
  set Z := (18 + 4 * t) * Real.exp (2 * (F.card : ℝ) * K) with hZ
  have hR : ball c (7 / 2 - 11 * δ / 8) ⊆ ball c (7 / 2 - 9 * δ / 8) :=
    ball_subset_ball (by linarith only [hδ])
  have hgdiff : DifferentiableOn ℂ g (ball c (7 / 2 - 11 * δ / 8)) := fun z hz =>
    (hg z (hR hz)).differentiableAt.differentiableWithinAt
  have hgne' : ∀ z ∈ ball c (7 / 2 - 11 * δ / 8), g z ≠ 0 := fun z hz => hgne z (hR hz)
  set z₀ : ℂ := (σ : ℂ) + (t : ℂ) * I with hz₀
  have hz₀c : ‖z₀ - c‖ = 4 - σ := by
    have : z₀ - c = ((σ - 4 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hz₀, hc, centre]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hσ2])]
    ring
  have hupper := norm_upper_bound_of_two_radii (f := g) (c := c) (ρ := 1 / 2)
    (R := 7 / 2 - 11 * δ / 8) (r₁ := 1 / 4) (r₃ := 7 / 2 - 3 * δ / 2) (by norm_num) (by norm_num)
    (by linarith only [hδ4]) (by linarith only [hδ4]) (by linarith only [hδ]) hgdiff hgne' hMi
    hm0 hm hout hm0 hm (z := z₀) (by rw [hz₀c]; linarith only [hσ2])
    (by rw [hz₀c]; linarith only [hσ1, hδ])
  set w : ℝ := (Real.log ‖z₀ - c‖ - Real.log (1 / 4)) /
    (Real.log (7 / 2 - 3 * δ / 2) - Real.log (1 / 4)) with hw
  set B₁ : ℝ := 2 * (Real.log (2 / m) + 1) * (1 / 4) / (1 / 2 - 1 / 4) with hB₁
  set B₃ : ℝ := 2 * (Real.log (Z / m) + 1) * (7 / 2 - 3 * δ / 2) /
    (7 / 2 - 11 * δ / 8 - (7 / 2 - 3 * δ / 2)) with hB₃
  clear_value w B₁ B₃
  have hlog2m : Real.log (2 / m) = Real.log 8 + F.card * Real.log 4 := by
    rw [hm_def]; exact log_two_div_quarter_div F.card
  have hlogZm : Real.log (Z / m) = Real.log (18 + 4 * t) + 2 * F.card * K + Real.log 4 +
      F.card * Real.log 4 := by
    rw [hm_def, hZ]; exact log_div_quarter_div (by linarith only [ht]) F.card
  have hlog4 := log_four_le
  have hlog8 := log_eight_nonneg
  have hlog40 := log_four_nonneg
  have hcard0 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hlogZ0 : 0 ≤ Real.log (18 + 4 * t) := Real.log_nonneg (by linarith only [ht])
  have hden : 7 / 2 - 11 * δ / 8 - (7 / 2 - 3 * δ / 2) = δ / 8 := by ring
  refine ⟨B₁, B₃, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB₁, hlog2m]
    have : 0 ≤ Real.log 8 + F.card * Real.log 4 + 1 := by positivity
    positivity
  · rw [hB₁, hlog2m]
    have e : 2 * (Real.log 8 + F.card * Real.log 4 + 1) * (1 / 4) / (1 / 2 - 1 / 4) =
        2 * (Real.log 8 + 1) + 2 * (F.card * Real.log 4) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hlog4 hcard0
    linarith only [this]
  · rw [hB₃, hlogZm, hden]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg _ (by linarith only [hδ4])
    have : 0 ≤ Real.log (18 + 4 * t) + 2 * F.card * K + Real.log 4 + F.card * Real.log 4 + 1 := by
      positivity
    linarith only [this]
  · rw [hB₃, hlogZm, hden]
    apply le_of_eq
    field_simp
    ring
  · rw [hw]
    apply div_nonneg
    · have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) (show (1 / 4 : ℝ) ≤ ‖z₀ - c‖ by
        rw [hz₀c]; linarith only [hσ2])
      linarith only [this]
    · have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4)
        (show (1 / 4 : ℝ) < 7 / 2 - 3 * δ / 2 by linarith only [hδ4])
      linarith only [this]
  · rw [hw]
    apply div_le_div_of_nonneg_right _ (by
      have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4)
        (show (1 / 4 : ℝ) < 7 / 2 - 3 * δ / 2 by linarith only [hδ4])
      linarith only [this])
    have := Real.log_le_log (show (0 : ℝ) < ‖z₀ - c‖ by rw [hz₀c]; linarith only [hσ2])
      (show ‖z₀ - c‖ ≤ 7 / 2 - 2 * δ by rw [hz₀c]; linarith only [hσ1])
    linarith only [this]
  · have hz₀U : z₀ ∈ ball c (7 / 2 - 9 * δ / 8) := by
      rw [mem_ball, dist_eq_norm, hz₀c]; linarith only [hσ1, hδ]
    have hPs : ∏ u ∈ S, ‖z₀ - u‖ ^ D u ≤ 8 ^ (∑ u ∈ S, D u) := by
      refine prod_pow_le_pow_sum (fun u _ => norm_nonneg _) fun u hu => ?_
      have h1 : ‖z₀ - u‖ ≤ ‖z₀ - c‖ + ‖c - u‖ := by
        have := norm_add_le (z₀ - c) (c - u)
        rwa [show z₀ - c + (c - u) = z₀ - u by ring] at this
      have h2 : ‖c - u‖ ≤ 4 := by
        rw [norm_sub_rev]; linarith only [(hzero u hu).2.2.1, hδ]
      rw [hz₀c] at h1
      linarith only [h1, h2, hσ1, hδ]
    rw [norm_zeta_eq_of_factor (hfac z₀ hz₀U), hFcard]
    calc (∏ u ∈ S, ‖z₀ - u‖ ^ D u) * ‖g z₀‖
        ≤ 8 ^ (∑ u ∈ S, D u) * (2 * Real.exp (B₁ ^ (1 - w) * B₃ ^ w)) := by
          refine mul_le_mul hPs (hupper.trans ?_) (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right hgc2 (Real.exp_pos _).le
      _ = 8 ^ (∑ u ∈ S, D u) * 2 * Real.exp (B₁ ^ (1 - w) * B₃ ^ w) := by ring

/-! ## Backlund's converse -/

/-- The Lindelöf hypothesis on every half-plane `Re s ≥ σ₀ > ½`. -/
def LindelofOpen : Prop :=
  ∀ σ₀ ε : ℝ, 1 / 2 < σ₀ → 0 < ε → ∃ T : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → T ≤ |s.im| →
    ‖riemannZeta s‖ ≤ |s.im| ^ ε

theorem log_le_log_add_of_le {t : ℝ} (ht : 1 ≤ t) : Real.log (18 + 4 * t) ≤ Real.log 22 + Real.log t := by
  rw [← Real.log_mul (by norm_num) (by linarith)]
  exact Real.log_le_log (by linarith) (by linarith)

/-- **Backlund's converse.** Off-line sparsity gives the Lindelöf hypothesis on every half-plane
`Re s ≥ σ₀ > ½`. -/
theorem lindelofOpen_of_offLineSparse (hsp : OffLineSparse) : LindelofOpen := by
  intro σ₀ ε hσ₀ hε
  set σ₁ := min σ₀ 1 with hσ₁
  have hσ₁0 : 1 / 2 < σ₁ := lt_min hσ₀ (by norm_num)
  have hσ₁1 : σ₁ ≤ 1 := min_le_right _ _
  have hσ₁σ₀ : σ₁ ≤ σ₀ := min_le_left _ _
  set δ := (σ₁ - 1 / 2) / 2 with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  have hδ4 : δ ≤ 1 / 4 := by rw [hδ_def]; linarith
  set r₃ := 7 / 2 - 3 * δ / 2 with hr₃
  set θ := (Real.log (7 / 2 - 2 * δ) - Real.log (1 / 4)) /
    (Real.log r₃ - Real.log (1 / 4)) with hθ
  have hden : 0 < Real.log r₃ - Real.log (1 / 4) := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) (show (1 / 4 : ℝ) < r₃ by
      rw [hr₃]; linarith)
    linarith
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hden]
    have := Real.log_lt_log (show (0 : ℝ) < 7 / 2 - 2 * δ by linarith)
      (show 7 / 2 - 2 * δ < r₃ by rw [hr₃]; linarith)
    linarith
  set K := 3 * Real.sqrt (δ / 8) / (δ / 8) with hK
  have hK0 : 0 ≤ K := by positivity
  have hlog22 : 0 ≤ Real.log 22 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr₃0 : 0 < r₃ := by rw [hr₃]; linarith
  set β := 16 * r₃ / δ * (Real.log 22 + 2 * Real.log 4 + 2 + 2 * K) with hβ
  have hβ1 : 1 ≤ β := by
    have h1 : 1 ≤ 16 * r₃ / δ := by
      rw [le_div_iff₀ hδ]; rw [hr₃]; nlinarith
    have h2 : 1 ≤ Real.log 22 + 2 * Real.log 4 + 2 + 2 * K := by linarith
    rw [hβ]; nlinarith
  set C₁ := 2 * (Real.log 8 + 1) with hC₁
  set a := min 1 (ε / (4 * β)) with ha
  have ha0 : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 := min_le_left _ _
  set κ := min (1 / 6) (min (ε / (4 * Real.log 8)) (a ^ (1 / (1 - θ)) / 6)) with hκ
  have hκ0 : 0 < κ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hκ6 : 6 * κ ≤ 1 := by have := min_le_left (1 / 6 : ℝ) (min (ε / (4 * Real.log 8))
    (a ^ (1 / (1 - θ)) / 6)); rw [← hκ] at this; linarith
  have hκa : κ * Real.log 8 ≤ ε / 4 := by
    have h := (min_le_right (1 / 6 : ℝ) _).trans (min_le_left (ε / (4 * Real.log 8))
      (a ^ (1 / (1 - θ)) / 6))
    rw [← hκ] at h
    calc κ * Real.log 8 ≤ ε / (4 * Real.log 8) * Real.log 8 :=
          mul_le_mul_of_nonneg_right h hlog8.le
      _ = ε / 4 := by field_simp
  have hκb : (6 * κ) ^ (1 - θ) * β ≤ ε / 4 := by
    have h := (min_le_right (1 / 6 : ℝ) _).trans (min_le_right (ε / (4 * Real.log 8))
      (a ^ (1 / (1 - θ)) / 6))
    rw [← hκ] at h
    have h6 : 6 * κ ≤ a ^ (1 / (1 - θ)) := by linarith
    have hpow : (6 * κ) ^ (1 - θ) ≤ a := by
      calc (6 * κ) ^ (1 - θ) ≤ (a ^ (1 / (1 - θ))) ^ (1 - θ) :=
            Real.rpow_le_rpow (by positivity) h6 (by linarith)
        _ = a := by
            rw [← Real.rpow_mul ha0.le, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one]
    have ha' : a ≤ ε / (4 * β) := min_le_right _ _
    calc (6 * κ) ^ (1 - θ) * β ≤ ε / (4 * β) * β :=
          mul_le_mul_of_nonneg_right (hpow.trans ha') (by linarith)
      _ = ε / 4 := by field_simp
  obtain ⟨T₀, hT₀⟩ := hsp δ 4 κ hδ (by norm_num) hκ0
  set T := max (max T₀ 6) (max (Real.exp (C₁ / (3 * κ)))
    (max (Real.exp (2 * Real.log 2 / ε)) (Real.exp 1))) with hT
  -- the bound at positive heights
  have hpos : ∀ s : ℂ, σ₀ ≤ s.re → T ≤ s.im → ‖riemannZeta s‖ ≤ s.im ^ ε := by
    intro s hs ht
    set t := s.im with ht_def
    set σ := s.re with hσ_def
    have htT₀ : T₀ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
    have ht6 : 6 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
    have hte1 : Real.exp (C₁ / (3 * κ)) ≤ t :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
    have hte2 : Real.exp (2 * Real.log 2 / ε) ≤ t :=
      le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) ht
    have hte3 : Real.exp 1 ≤ t :=
      le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) ht
    have ht0 : 0 < t := by linarith
    set X := Real.log t with hX
    have hX1 : 1 ≤ X := by rw [hX, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hte3
    have hXC : C₁ ≤ 3 * κ * X := by
      have : C₁ / (3 * κ) ≤ X := by
        rw [hX, ← Real.log_exp (C₁ / (3 * κ))]; exact Real.log_le_log (Real.exp_pos _) hte1
      rw [div_le_iff₀ (by positivity)] at this; linarith
    have hX2 : Real.log 2 ≤ ε / 2 * X := by
      have : 2 * Real.log 2 / ε ≤ X := by
        rw [hX, ← Real.log_exp (2 * Real.log 2 / ε)]; exact Real.log_le_log (Real.exp_pos _) hte2
      rw [div_le_iff₀ hε] at this; linarith
    have htpow : Real.exp (ε * X) = t ^ ε := by
      rw [Real.rpow_def_of_pos ht0, hX, mul_comm]
    have hseq : s = (σ : ℂ) + (t : ℂ) * I := (Complex.re_add_im s).symm
    rcases le_or_gt σ (15 / 4) with hσ2 | hσ2
    · obtain ⟨F, hF, B₁, B₃, w, hB₁0, hB₁, hB₃0, hB₃, hw0, hwθ, hbound⟩ :=
        local_estimate hδ hδ4 ht6 (show 1 / 2 + 2 * δ ≤ σ by rw [hδ_def]; linarith) hσ2
      have hN : (F.card : ℝ) ≤ κ * X := hT₀ t htT₀ F hF
      have hκX : κ * X ≤ X := mul_le_of_le_one_left (by linarith only [hX1])
        (by linarith only [hκ6])
      have hNX : (F.card : ℝ) ≤ X := hN.trans hκX
      have hB₃' : B₃ ≤ β * X := by
        refine hB₃.trans ?_
        have hl : Real.log (18 + 4 * t) ≤ Real.log 22 + X :=
          log_le_log_add_of_le (by linarith only [ht6])
        have h16 : 0 ≤ 16 * (7 / 2 - 3 * δ / 2) / δ := by
          apply div_nonneg _ hδ.le; linarith only [hδ4]
        have h2K : 0 ≤ 2 * K + Real.log 4 := by linarith only [hK0, hlog4]
        have hA := mul_le_mul_of_nonneg_left hNX h2K
        have hB := mul_le_mul_of_nonneg_left hX1 hlog22
        have hC := mul_le_mul_of_nonneg_left hX1 (show 0 ≤ Real.log 4 + 1 by
          linarith only [hlog4])
        have hinner : Real.log (18 + 4 * t) + (2 * K + Real.log 4) * F.card + Real.log 4 + 1 ≤
            (Real.log 22 + 2 * Real.log 4 + 2 + 2 * K) * X := by
          linarith only [hl, hA, hB, hC]
        calc 16 * (7 / 2 - 3 * δ / 2) / δ * (Real.log (18 + 4 * t) +
              (2 * (3 * Real.sqrt (δ / 8) / (δ / 8)) + Real.log 4) * F.card + Real.log 4 + 1)
            = 16 * (7 / 2 - 3 * δ / 2) / δ * (Real.log (18 + 4 * t) +
              (2 * K + Real.log 4) * F.card + Real.log 4 + 1) := rfl
          _ ≤ 16 * (7 / 2 - 3 * δ / 2) / δ *
              ((Real.log 22 + 2 * Real.log 4 + 2 + 2 * K) * X) :=
            mul_le_mul_of_nonneg_left hinner h16
          _ = β * X := by rw [hβ, hr₃]; ring
      have hexp := final_exponent_le (N := F.card) (X := X) (C₁ := C₁) hθ1 hw0
        hwθ hβ1 hκ0 hκ6 hκa hκb hX1 hXC hX2 hN hB₁0 hB₁ hB₃0 hB₃'
      rw [hseq]
      refine hbound.trans ?_
      rw [← htpow]
      calc (8 : ℝ) ^ F.card * 2 * Real.exp (B₁ ^ (1 - w) * B₃ ^ w)
          = Real.exp (F.card * Real.log 8 + Real.log 2 + B₁ ^ (1 - w) * B₃ ^ w) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 8)]
            ring_nf
        _ ≤ Real.exp (ε * X) := Real.exp_le_exp.mpr hexp
    · have h1 := Sieve.norm_riemannZeta_le (s := s) (by linarith only [hσ2])
      have h2 : 1 / (σ - 1) ≤ 1 := by
        rw [div_le_one (by linarith only [hσ2])]; linarith only [hσ2]
      have hεX : ε / 2 * X ≤ ε * X := mul_le_mul_of_nonneg_right
        (by linarith only [hε]) (by linarith only [hX1])
      have h3 : 2 ≤ t ^ ε := by
        rw [← htpow, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact Real.exp_le_exp.mpr (by linarith only [hX2, hεX])
      linarith only [h1, h2, h3]
  refine ⟨T, fun s hs ht => ?_⟩
  rcases le_or_gt 0 s.im with hs0 | hs0
  · rw [abs_of_nonneg hs0] at ht ⊢
    exact hpos s hs ht
  · rw [abs_of_neg hs0] at ht ⊢
    have h := hpos ((starRingEnd ℂ) s) (by rwa [Complex.conj_re]) (by rwa [Complex.conj_im])
    rw [riemannZeta_conj, norm_conj, Complex.conj_im] at h
    exact h

/-- **Backlund's forward direction, open form.** If `μ(σ) = 0` for every `σ > ½`, off-line zeros
are sparse. -/
theorem offLineSparse_of_lindelofOpen (hLO : LindelofOpen) : OffLineSparse :=
  offLineSparse_of_eventual_bound fun η ε hη hε => by
    obtain ⟨T, hT⟩ := hLO (1 / 2 + η / 2) ε (by linarith) hε
    exact ⟨1, T, le_rfl, fun s hs hs' => by rw [one_mul]; exact hT s hs hs'⟩

/-- **Backlund's theorem.** Off-line zeros are sparse (for every `η, L, c > 0`, eventually every
window of length `2L` at height `t` carries at most `c log t` zeros with `|β − ½| > η`) if and only
if `‖ζ(σ + it)‖ ≤ |t|^ε` for all `σ ≥ σ₀` and `|t|` large, for every `σ₀ > ½` and `ε > 0`. -/
theorem offLineSparse_iff_lindelofOpen : OffLineSparse ↔ LindelofOpen :=
  ⟨lindelofOpen_of_offLineSparse, offLineSparse_of_lindelofOpen⟩

end

end RHTower.BacklundConverse
