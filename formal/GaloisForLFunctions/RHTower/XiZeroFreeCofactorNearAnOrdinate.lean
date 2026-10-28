import GaloisForLFunctions.RHTower.XiLocalZeroDensity
import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization

/-!
# The zero-free cofactor of `ξ` near an ordinate

Let `c = 2 + iT`.  On the ball `B(c, 8)` write `ξ = P · g`, with `P(s) = ∏_ρ (s − ρ)^{m_ρ}` over
the zeros of `ξ` in the ball (with multiplicity) and `g` analytic and zero-free.  For large `T`
(`exists_xi_cofactor_near_ordinate`):

* the zeros in the ball have total multiplicity `≤ C log T`;
* the cofactor has `‖g′/g‖ ≤ C log T` on `B(c, 7)`.

**Proof.**  The partial fraction `ξ′/ξ(s) = Σ_q ((q − 1/2)⁻¹ + (s − q)⁻¹)` over the zero copies
(`logDeriv_xi_eq_partialFraction`) and the factorization give
`g′/g(s) − g′/g(c) = Σ_{q ∉ B(c,8)} ((s − q)⁻¹ − (c − q)⁻¹)`.  For `s ∈ B(c, 7)` each term is at
most `57/(1 + (T − Im q)²)`, and the weighted local density
(`exists_tsum_weighted_density_le`) bounds the sum by `C log T`.  At the Euler point,
`‖ξ′/ξ(c)‖ ≤ C log T` (`exists_norm_logDeriv_xi_two_line_le`) and every zero lies at distance
`≥ 1` from `c`.  The zero count is the local density `N(t+1) − N(t) = O(log t)`
(`exists_card_near_xi_zeros_le`) over nine unit windows.
-/

open Complex Metric Filter Topology

namespace RHTower

noncomputable section

/-! ## The logarithmic derivative at abscissa two -/

/-- `‖ξ′/ξ(2 + it)‖ ≤ C log t` for large `t`. -/
theorem exists_norm_logDeriv_xi_two_line_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      ‖logDeriv xi ((2 : ℂ) + (t : ℂ) * I)‖ ≤ C * Real.log t := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_logDeriv_riemannZeta_two_line
  set C : ℝ := 3 / 2 + |Real.log Real.pi| / 2 + C₀ + 2 with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hC0, ?_⟩
  have hdig : ∀ᶠ u : ℝ in atTop,
      ‖Complex.digamma ((1 : ℂ) + (u : ℂ) * I)‖ ≤ 2 * Real.log u :=
    GaloisForLFunctions.norm_digamma_vertical_le_two_log (by norm_num)
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    Filter.tendsto_id.atTop_div_const (by norm_num)
  have hdig' : ∀ᶠ t : ℝ in atTop,
      ‖Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖ ≤ 2 * Real.log (t / 2) :=
    hhalf.eventually hdig
  filter_upwards [hdig', Filter.eventually_ge_atTop (3 : ℝ),
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ))] with t hdt ht3 hlog1
  set s : ℂ := (2 : ℂ) + (t : ℂ) * I with hs
  have hre : s.re = 2 := by rw [hs]; simp
  have hsplit : logDeriv xi s = s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s
      + logDeriv riemannZeta s := logDeriv_xi_split (by rw [hre]; norm_num)
  have hsnorm : (2 : ℝ) ≤ ‖s‖ := by
    have := Complex.abs_re_le_norm s
    rw [hre] at this
    simpa using this
  have hs1norm : (1 : ℝ) ≤ ‖s - 1‖ := by
    have hre1 : (s - 1).re = 1 := by rw [Complex.sub_re, hre]; norm_num
    have := Complex.abs_re_le_norm (s - 1)
    rw [hre1] at this
    simpa using this
  have hinv1 : ‖s⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, one_div]
    gcongr
  have hinv2 : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv, inv_le_one_iff₀]
    right
    exact hs1norm
  have hgamma : ‖logDeriv Complex.Gammaℝ s‖ ≤ |Real.log Real.pi| / 2 + Real.log t := by
    have hsre : (0 : ℝ) < s.re := by rw [hre]; norm_num
    have hhalfs : s / 2 = (1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
      rw [hs]
      push_cast
      ring
    rw [logDeriv_Gammaℝ_eq hsre, hhalfs]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖-((Real.log Real.pi : ℂ) / 2)‖ = |Real.log Real.pi| / 2 := by
      rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    have h2 : ‖Complex.digamma ((1 : ℂ) + ((t / 2 : ℝ) : ℂ) * I) / 2‖ ≤ Real.log t := by
      rw [norm_div]
      have hlog : Real.log (t / 2) ≤ Real.log t := Real.log_le_log (by linarith) (by linarith)
      have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2norm]
      linarith
    linarith
  have hzeta : ‖logDeriv riemannZeta s‖ ≤ C₀ := hC₀ t
  have hfinal : ‖logDeriv xi s‖ ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t := by
    rw [hsplit]
    calc ‖s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s‖
        ≤ ‖s⁻¹‖ + ‖(s - 1)⁻¹‖ + ‖logDeriv Complex.Gammaℝ s‖ + ‖logDeriv riemannZeta s‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t := by linarith
  have hCpos : (0 : ℝ) ≤ 3 / 2 + |Real.log Real.pi| / 2 + C₀ + 1 := by positivity
  have hmul : 3 / 2 + |Real.log Real.pi| / 2 + C₀ + Real.log t ≤ C * Real.log t := by
    rw [hCdef]
    nlinarith [hlog1, hCpos]
  linarith

/-! ## The factorization with divisor multiplicities -/

/-- The finite factorization on a ball, with the multiplicities read off the divisor. -/
theorem exists_divisor_ball_factorization {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hR : 0 < R) (hfc : f c ≠ 0) :
    ∃ (hfin : (MeromorphicOn.divisor f (ball c R)).support.Finite) (g : ℂ → ℂ),
      AnalyticOnNhd ℂ g (ball c R) ∧ (∀ z ∈ ball c R, g z ≠ 0) ∧
      Set.EqOn f (fun z => (∏ ρ ∈ hfin.toFinset,
        (z - ρ) ^ (MeromorphicOn.divisor f (ball c R) ρ).toNat) * g z) (ball c R) := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hfin : (MeromorphicOn.divisor f (ball c R)).support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  have hnn : ∀ u : ℂ, 0 ≤ MeromorphicOn.divisor f (ball c R) u :=
    HTGeometry.divisor_nonneg_of_analytic_ball (fun z hz => hf z (ball_subset_closedBall hz))
  obtain ⟨g, hg, hg0, heq⟩ := HTGeometry.exists_zeroFree_factor hf hc hfc
  refine ⟨hfin, g, hg, hg0, fun z hz => (heq hz).trans ?_⟩
  have hsupp : Function.mulSupport
      (fun u => (z - u) ^ (MeromorphicOn.divisor f (ball c R) u)) ⊆ (hfin.toFinset : Set ℂ) := by
    intro u hu
    rw [Set.Finite.coe_toFinset]
    by_contra hcon
    have hzero : MeromorphicOn.divisor f (ball c R) u = 0 := by
      simpa [Function.mem_support] using hcon
    apply hu
    show (z - u) ^ (MeromorphicOn.divisor f (ball c R) u) = 1
    rw [hzero, zpow_zero]
  show (∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f (ball c R) u)) * g z = _
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [← zpow_natCast (z - ρ) ((MeromorphicOn.divisor f (ball c R) ρ).toNat),
    Int.toNat_of_nonneg (hnn ρ)]

/-! ## The cofactor near an ordinate -/

/-- A zero copy outside `B(c, 8)`, `c = 2 + iT`, and a point of `B(c, 7)`: the difference of the
two partial-fraction terms is at most `57/(1 + (T − Im q)²)`. -/
theorem norm_inv_sub_sub_inv_sub_le {T : ℝ} {s q : ℂ}
    (hs : s ∈ ball ((2 : ℂ) + (T : ℂ) * I) 7) (hq : q ∉ ball ((2 : ℂ) + (T : ℂ) * I) 8) :
    ‖(s - q)⁻¹ - ((2 : ℂ) + (T : ℂ) * I - q)⁻¹‖ ≤ 57 / (1 + (T - q.im) ^ 2) := by
  set c : ℂ := (2 : ℂ) + (T : ℂ) * I with hcdef
  have hsc : ‖s - c‖ < 7 := by simpa [dist_eq_norm] using hs
  have hqc : 8 ≤ ‖q - c‖ := by simpa [dist_eq_norm] using hq
  have hcq : ‖c - q‖ = ‖q - c‖ := norm_sub_rev c q
  have hsq : ‖q - c‖ / 8 ≤ ‖s - q‖ := by
    have := norm_sub_norm_le (q - c) (s - c)
    rw [show q - c - (s - c) = q - s by ring, norm_sub_rev q s] at this
    linarith
  have hqc0 : 0 < ‖q - c‖ := by linarith
  have hsq0 : 0 < ‖s - q‖ := lt_of_lt_of_le (by positivity) hsq
  have hcq0 : 0 < ‖c - q‖ := by rw [hcq]; exact hqc0
  have hdiff : (s - q)⁻¹ - (c - q)⁻¹ = (c - s) / ((s - q) * (c - q)) := by
    rw [inv_sub_inv (norm_pos_iff.mp hsq0) (norm_pos_iff.mp hcq0)]
    ring_nf
  have hcs : ‖c - s‖ ≤ 7 := by rw [norm_sub_rev]; exact hsc.le
  have hbound : ‖(s - q)⁻¹ - (c - q)⁻¹‖ ≤ 56 / ‖q - c‖ ^ 2 := by
    rw [hdiff, norm_div, norm_mul, hcq]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hsq hqc0.le]
  -- `‖q − c‖² ≥ max(64, (T − Im q)²) ≥ (64/65)(1 + (T − Im q)²)`
  have him : (T - q.im) ^ 2 ≤ ‖q - c‖ ^ 2 := by
    have h := Complex.abs_im_le_norm (q - c)
    have him' : (q - c).im = q.im - T := by rw [hcdef]; simp
    rw [him'] at h
    have : |T - q.im| ≤ ‖q - c‖ := by rw [abs_sub_comm]; exact h
    nlinarith [abs_nonneg (T - q.im), sq_abs (T - q.im)]
  have hden : (64 / 65 : ℝ) * (1 + (T - q.im) ^ 2) ≤ ‖q - c‖ ^ 2 := by
    nlinarith [sq_nonneg (T - q.im)]
  calc ‖(s - q)⁻¹ - (c - q)⁻¹‖ ≤ 56 / ‖q - c‖ ^ 2 := hbound
    _ ≤ 56 / ((64 / 65 : ℝ) * (1 + (T - q.im) ^ 2)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ ≤ 57 / (1 + (T - q.im) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg (T - q.im)]

/-! ## Zero copies over a finite set of zeros -/

/-- The zero copies of `ξ` whose zero lies in the finite set `Z`. -/
def xiCopiesOver (Z : Finset ℂ) : Finset XiZeroCopy := by
  classical
  exact (Z.subtype (fun ρ => ρ ∈ (MeromorphicOn.divisor xi Set.univ).support)).sigma
    fun _ => Finset.univ

theorem mem_xiCopiesOver {Z : Finset ℂ} {q : XiZeroCopy} :
    q ∈ xiCopiesOver Z ↔ ((q.1 : ℂ)) ∈ Z := by
  classical
  simp [xiCopiesOver, Finset.mem_sigma, Finset.mem_subtype]

/-- Summing over the copies of the zeros in `Z` weights each zero by its multiplicity. -/
theorem sum_xiCopiesOver (Z : Finset ℂ) (h : ℂ → ℂ) :
    ∑ q ∈ xiCopiesOver Z, h (q.1 : ℂ)
      = ∑ ρ ∈ Z, (((MeromorphicOn.divisor xi Set.univ) ρ).toNat : ℂ) * h ρ := by
  classical
  rw [xiCopiesOver, Finset.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_subtype_eq_sum_filter (f := fun ρ =>
    (((MeromorphicOn.divisor xi Set.univ) ρ).toNat : ℂ) * h ρ)]
  rw [Finset.sum_filter_of_ne]
  intro ρ _ hne
  by_contra hns
  apply hne
  have : (MeromorphicOn.divisor xi Set.univ) ρ = 0 := by
    simpa [Function.mem_support] using hns
  simp [this]

/-- The divisor of `ξ` on a ball agrees with the global divisor inside the ball. -/
theorem divisor_xi_ball_eq {c : ℂ} {R : ℝ} {ρ : ℂ} (hρ : ρ ∈ ball c R) :
    MeromorphicOn.divisor xi (ball c R) ρ = MeromorphicOn.divisor xi Set.univ ρ := by
  have hmer : ∀ U : Set ℂ, MeromorphicOn xi U := fun U z _ =>
    (xi_differentiable.analyticAt z).meromorphicAt
  rw [MeromorphicOn.divisor_apply (hmer _) hρ, MeromorphicOn.divisor_apply (hmer _) (Set.mem_univ ρ)]

/-- **The zero-free cofactor of `ξ` near an ordinate.**  For large `T`, with `c = 2 + iT`, the
zeros of `ξ` in `B(c, 8)` have total multiplicity `≤ C log T`, and the cofactor `g` of
`ξ = ∏ (s − ρ)^{m_ρ} · g` has `‖g′/g‖ ≤ C log T` on `B(c, 7)`. -/
theorem exists_xi_cofactor_near_ordinate :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∃ (Z : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
      (∀ ρ ∈ Z, ρ ∈ ball ((2 : ℂ) + (T : ℂ) * I) 8) ∧
      (∀ z ∈ ball ((2 : ℂ) + (T : ℂ) * I) 8, xi z = 0 ↔ z ∈ Z) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log T ∧
      AnalyticOnNhd ℂ g (ball ((2 : ℂ) + (T : ℂ) * I) 8) ∧
      (∀ z ∈ ball ((2 : ℂ) + (T : ℂ) * I) 8, g z ≠ 0) ∧
      Set.EqOn xi (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z)
        (ball ((2 : ℂ) + (T : ℂ) * I) 8) ∧
      ∀ s ∈ ball ((2 : ℂ) + (T : ℂ) * I) 7, ‖deriv g s / g s‖ ≤ C * Real.log T := by
  classical
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_card_near_xi_zeros_le
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_tsum_weighted_density_le
  obtain ⟨C₃, hC₃0, hC₃⟩ := exists_norm_logDeriv_xi_two_line_le
  refine ⟨36 * C₁ + C₃ + 57 * C₂, by positivity, ?_⟩
  have hwin : ∀ᶠ T : ℝ in atTop, ∀ k : Fin 9, ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, |(q.1 : ℂ).im - (T - 7 + 2 * k)| ≤ 1) →
        (F.card : ℝ) ≤ C₁ * Real.log (T - 7 + 2 * k) := by
    refine Filter.eventually_all.2 fun k => ?_
    have h := (tendsto_atTop_add_const_right atTop ((-7 : ℝ) + 2 * ((k : ℕ) : ℝ))
      tendsto_id).eventually hC₁
    filter_upwards [h] with T hT
    have e : T - 7 + 2 * ((k : ℕ) : ℝ) = id T + ((-7 : ℝ) + 2 * ((k : ℕ) : ℝ)) := by
      simp only [id]; ring
    rw [e]
    exact hT
  filter_upwards [hwin, hC₂, hC₃, Filter.eventually_ge_atTop (16 : ℝ)]
    with T hwinT hC₂T hC₃T hT16
  set c : ℂ := (2 : ℂ) + (T : ℂ) * I with hcdef
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have han8 : AnalyticOnNhd ℂ xi (closedBall c 8) := fun z _ => xi_differentiable.analyticAt z
  have hxic : xi c ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hcdef]; simp)
  obtain ⟨hfin, g, hg, hg0, heq⟩ := exists_divisor_ball_factorization han8 (by norm_num) hxic
  set Z : Finset ℂ := hfin.toFinset with hZdef
  set m : ℂ → ℕ := fun ρ => (MeromorphicOn.divisor xi (ball c 8) ρ).toNat with hmdef
  have hZball : ∀ ρ ∈ Z, ρ ∈ ball c 8 := fun ρ hρ =>
    (MeromorphicOn.divisor xi (ball c 8)).supportWithinDomain (hfin.mem_toFinset.mp hρ)
  have hfb : AnalyticOnNhd ℂ xi (ball c 8) := fun z _ => xi_differentiable.analyticAt z
  have hzeroZ : ∀ z ∈ ball c 8, xi z = 0 ↔ z ∈ Z := by
    intro z hz
    have hzs : z ∈ ball c 8 ∩ xi ⁻¹' {0} ↔ z ∈ Function.support
        (MeromorphicOn.divisor xi (ball c 8)) := by
      rw [hfb.meromorphicNFOn.zero_set_eq_divisor_support
        (HTGeometry.meromorphicOrderAt_ne_top_of_analytic_ball hfb
          (mem_ball_self (by norm_num)) hxic)]
    constructor
    · intro h0
      exact hfin.mem_toFinset.mpr (hzs.mp ⟨hz, h0⟩)
    · intro hmem
      exact (hzs.mpr (hfin.mem_toFinset.mp hmem)).2
  -- the copies of the zeros in the ball
  set F : Finset XiZeroCopy := xiCopiesOver Z with hFdef
  have hmZ : ∀ ρ ∈ Z, (m ρ : ℂ) = (((MeromorphicOn.divisor xi Set.univ) ρ).toNat : ℂ) := by
    intro ρ hρ
    simp only [hmdef, divisor_xi_ball_eq (hZball ρ hρ)]
  have hsumF : ∀ h : ℂ → ℂ, ∑ ρ ∈ Z, (m ρ : ℂ) * h ρ = ∑ q ∈ F, h (q.1 : ℂ) := by
    intro h
    rw [hFdef, sum_xiCopiesOver]
    exact Finset.sum_congr rfl fun ρ hρ => by rw [hmZ ρ hρ]
  have hcardF : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) = (F.card : ℝ) := by
    have h1 := hsumF (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    exact_mod_cast h1
  -- copies outside `F` lie outside the ball
  have hout : ∀ q : XiZeroCopy, q ∉ F → (q.1 : ℂ) ∉ ball c 8 := by
    intro q hq hmem
    apply hq
    rw [hFdef, mem_xiCopiesOver]
    exact (hzeroZ _ hmem).mp (xi_eq_zero_of_mem_divisor_support q.1)
  -- the zero count
  have hcount : (F.card : ℝ) ≤ 36 * C₁ * Real.log T := by
    have hcover : F ⊆ Finset.univ.biUnion (fun k : Fin 9 =>
        F.filter (fun q => |(q.1 : ℂ).im - (T - 7 + 2 * k)| ≤ 1)) := by
      intro q hq
      have hmem : (q.1 : ℂ) ∈ ball c 8 := by
        have := (mem_xiCopiesOver.mp (hFdef ▸ hq))
        exact hZball _ this
      have hlt : |(q.1 : ℂ).im - T| < 8 := by
        have h := Complex.abs_im_le_norm ((q.1 : ℂ) - c)
        have him : ((q.1 : ℂ) - c).im = (q.1 : ℂ).im - T := by rw [hcdef]; simp
        rw [him] at h
        have : ‖(q.1 : ℂ) - c‖ < 8 := by simpa [dist_eq_norm] using hmem
        linarith
      set u : ℝ := (q.1 : ℂ).im - T + 8 with hu
      have hu0 : 0 < u := by rw [hu]; linarith [abs_lt.mp hlt]
      have hu16 : u < 16 := by rw [hu]; linarith [abs_lt.mp hlt]
      have hTk : ∀ k : ℕ, (q.1 : ℂ).im - (T - 7 + 2 * (k : ℝ)) = u - (2 * k + 1) := by
        intro k; rw [hu]; ring
      set k : ℕ := ⌊u / 2⌋₊ with hk
      have hk8 : k < 9 := by
        rw [hk, Nat.floor_lt (by positivity)]
        push_cast
        linarith
      refine Finset.mem_biUnion.mpr ⟨⟨k, hk8⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hq, ?_⟩⟩
      have hfl := Nat.floor_le (show 0 ≤ u / 2 by positivity)
      have hlt2 := Nat.lt_floor_add_one (u / 2)
      rw [← hk] at hfl hlt2
      rw [hTk, abs_le]
      constructor <;> linarith
    have hcard := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have hk : ∀ k : Fin 9, ((F.filter (fun q => |(q.1 : ℂ).im - (T - 7 + 2 * k)| ≤ 1)).card : ℝ)
        ≤ C₁ * (2 * Real.log T) := by
      intro k
      refine (hwinT k _ fun q hq => (Finset.mem_filter.mp hq).2).trans ?_
      gcongr
      have hk9 : (k : ℝ) < 9 := by exact_mod_cast k.2
      have hpos : 0 < T - 7 + 2 * (k : ℝ) := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        linarith
      calc Real.log (T - 7 + 2 * k) ≤ Real.log (T ^ 2) := by
            refine Real.log_le_log hpos ?_
            nlinarith
        _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
    calc (F.card : ℝ) ≤ ∑ k : Fin 9,
          ((F.filter (fun q => |(q.1 : ℂ).im - (T - 7 + 2 * k)| ≤ 1)).card : ℝ) := by
          exact_mod_cast hcard
      _ ≤ ∑ _k : Fin 9, C₁ * (2 * Real.log T) := Finset.sum_le_sum fun k _ => hk k
      _ = 18 * C₁ * Real.log T := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 36 * C₁ * Real.log T := by
          have hp : 0 ≤ C₁ * Real.log T := by positivity
          linarith
  refine ⟨Z, m, g, hZball, hzeroZ, ?_, hg, hg0, heq, ?_⟩
  · rw [hcardF]
    have hp3 : 0 ≤ C₃ * Real.log T := by positivity
    have hp2 : 0 ≤ C₂ * Real.log T := by positivity
    linarith
  -- the logarithmic derivative of the cofactor
  have hPne : ∀ s, (∀ ρ ∈ Z, s ≠ ρ) → (∏ ρ ∈ Z, (s - ρ) ^ m ρ) ≠ 0 :=
    fun s hs => Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hs ρ hρ))
  have hlogsplit : ∀ s ∈ ball c 8, xi s ≠ 0 →
      logDeriv xi s = (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + deriv g s / g s := by
    intro s hs hxs
    have hsZ : ∀ ρ ∈ Z, s ≠ ρ := fun ρ hρ hsρ =>
      hxs ((hzeroZ s hs).mpr (hsρ ▸ hρ))
    have hev : xi =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hs) fun z hz => heq hz
    have hgd : DifferentiableAt ℂ g s := (hg s hs).differentiableAt
    have hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (z - ρ) ^ m ρ) s := by fun_prop
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, ← logDeriv_apply,
      logDeriv_mul (f := fun z => ∏ ρ ∈ Z, (z - ρ) ^ m ρ) (g := g) s (hPne s hsZ) (hg0 s hs)
        hPd hgd, HTGeometry.logDeriv_finset_prod_pow hsZ, logDeriv_apply]
  have hpf : ∀ s ∈ ball c 8, xi s ≠ 0 →
      deriv g s / g s = (∑' q : XiZeroCopy, ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹))
        - ∑ q ∈ F, (s - (q.1 : ℂ))⁻¹ := by
    intro s hs hxs
    have h1 := hlogsplit s hs hxs
    rw [logDeriv_xi_eq_partialFraction hxs] at h1
    have h2 : ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) = ∑ q ∈ F, (s - (q.1 : ℂ))⁻¹ := by
      rw [← hsumF (fun ρ => (s - ρ)⁻¹)]
      exact Finset.sum_congr rfl fun ρ _ => by rw [div_eq_mul_inv]
    rw [h2] at h1
    linear_combination (-1 : ℂ) * h1
  have hcball : c ∈ ball c 8 := mem_ball_self (by norm_num)
  -- the cofactor at the Euler point
  have hgc : ‖deriv g c / g c‖ ≤ C₃ * Real.log T + 36 * C₁ * Real.log T := by
    have h1 := hlogsplit c hcball hxic
    have hc' : deriv g c / g c = logDeriv xi c - ∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ) := by
      rw [h1]; ring
    rw [hc']
    refine (norm_sub_le _ _).trans ?_
    have hfirst : ‖logDeriv xi c‖ ≤ C₃ * Real.log T := hC₃T
    have hsecond : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (c - ρ)‖ ≤ 36 * C₁ * Real.log T := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ ρ ∈ Z, ‖(m ρ : ℂ) / (c - ρ)‖ ≤ (m ρ : ℝ) := by
        intro ρ hρ
        have hre : ρ.re < 1 := by
          by_contra hge
          exact xi_ne_zero_of_one_le_re (not_lt.mp hge)
            ((hzeroZ ρ (hZball ρ hρ)).mpr hρ)
        have hdist : 1 ≤ ‖c - ρ‖ := by
          have h := Complex.abs_re_le_norm (c - ρ)
          have hre' : (c - ρ).re = 2 - ρ.re := by rw [hcdef]; simp
          rw [hre'] at h
          linarith [le_abs_self (2 - ρ.re)]
        rw [norm_div, Complex.norm_natCast]
        exact div_le_self (Nat.cast_nonneg _) hdist
      refine (Finset.sum_le_sum hterm).trans ?_
      have : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) = ∑ ρ ∈ Z, (m ρ : ℝ) := by push_cast; rfl
      rw [← this, hcardF]
      exact hcount
    linarith
  -- the bound away from the zeros
  have hbound_off : ∀ s ∈ ball c 7, xi s ≠ 0 →
      ‖deriv g s / g s‖ ≤ (36 * C₁ + C₃ + 57 * C₂) * Real.log T := by
    intro s hs hxs
    have hs8 : s ∈ ball c 8 := ball_subset_ball (by norm_num) hs
    set D : XiZeroCopy → ℂ := fun q => (s - (q.1 : ℂ))⁻¹ - (c - (q.1 : ℂ))⁻¹ with hD
    have hsumS := summable_xiPartialFractionTerm hxs
    have hsumC := summable_xiPartialFractionTerm hxic
    have hsumD : Summable D := (hsumS.sub hsumC).congr fun q => by simp only [hD]; ring
    have hdiff : deriv g s / g s - deriv g c / g c = ∑' q : ↑((F : Set XiZeroCopy)ᶜ), D q := by
      rw [hpf s hs8 hxs, hpf c hcball hxic]
      have htsum : (∑' q : XiZeroCopy, ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹))
          - (∑' q : XiZeroCopy, ((((q.1 : ℂ)) - 1 / 2)⁻¹ + (c - (q.1 : ℂ))⁻¹))
          = ∑' q, D q := by
        rw [← hsumS.tsum_sub hsumC]
        exact tsum_congr fun q => by simp only [hD]; ring
      have hsplit := hsumD.sum_add_tsum_compl (s := F)
      have hFD : ∑ q ∈ F, D q = ∑ q ∈ F, (s - (q.1 : ℂ))⁻¹ - ∑ q ∈ F, (c - (q.1 : ℂ))⁻¹ := by
        rw [← Finset.sum_sub_distrib]
      linear_combination htsum + hFD - hsplit
    have hweight : Summable (fun q : XiZeroCopy => (1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2)) :=
      hC₂T.1
    have hDbound : ∀ q : ↑((F : Set XiZeroCopy)ᶜ),
        ‖D q‖ ≤ 57 * ((1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)) := by
      intro q
      have hq : (q : XiZeroCopy) ∉ F := q.2
      have := norm_inv_sub_sub_inv_sub_le (T := T) hs (hout q hq)
      rw [hD]
      simp only
      rw [mul_one_div]
      exact this
    have hsub : Summable (fun q : ↑((F : Set XiZeroCopy)ᶜ) =>
        57 * ((1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2))) :=
      (hweight.subtype _).mul_left 57
    have htail : ‖∑' q : ↑((F : Set XiZeroCopy)ᶜ), D q‖ ≤ 57 * C₂ * Real.log T := by
      have hnormsum : Summable (fun q : ↑((F : Set XiZeroCopy)ᶜ) => ‖D q‖) :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hDbound hsub
      have hle : ∑' q : ↑((F : Set XiZeroCopy)ᶜ),
          (1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)
          ≤ ∑' q : XiZeroCopy, (1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2) :=
        Summable.tsum_subtype_le (fun q : XiZeroCopy => (1 : ℝ) / (1 + (T - (q.1 : ℂ).im) ^ 2))
          ((F : Set XiZeroCopy)ᶜ) (fun q => by positivity) hweight
      calc ‖∑' q : ↑((F : Set XiZeroCopy)ᶜ), D q‖ ≤ ∑' q : ↑((F : Set XiZeroCopy)ᶜ), ‖D q‖ :=
            norm_tsum_le_tsum_norm hnormsum
        _ ≤ ∑' q : ↑((F : Set XiZeroCopy)ᶜ),
              57 * ((1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2)) :=
            Summable.tsum_le_tsum hDbound hnormsum hsub
        _ = 57 * ∑' q : ↑((F : Set XiZeroCopy)ᶜ),
              (1 : ℝ) / (1 + (T - ((q : XiZeroCopy).1 : ℂ).im) ^ 2) := tsum_mul_left
        _ ≤ 57 * (C₂ * Real.log T) := by
            gcongr
            exact hle.trans hC₂T.2
        _ = 57 * C₂ * Real.log T := by ring
    calc ‖deriv g s / g s‖ = ‖deriv g c / g c + ∑' q : ↑((F : Set XiZeroCopy)ᶜ), D q‖ := by
          rw [← hdiff]; ring_nf
      _ ≤ ‖deriv g c / g c‖ + ‖∑' q : ↑((F : Set XiZeroCopy)ᶜ), D q‖ := norm_add_le _ _
      _ ≤ (36 * C₁ + C₃ + 57 * C₂) * Real.log T := by nlinarith [hgc, htail]
  -- extend to the zeros by continuity
  intro s hs
  by_cases hxs : xi s ≠ 0
  · exact hbound_off s hs hxs
  · push Not at hxs
    have hs8 : s ∈ ball c 8 := ball_subset_ball (by norm_num) hs
    have hcont : ContinuousAt (fun w => ‖deriv g w / g w‖) s := by
      have hga : AnalyticAt ℂ g s := hg s hs8
      exact (hga.deriv.continuousAt.div hga.continuousAt (hg0 s hs8)).norm
    have hev : ∀ᶠ w in 𝓝[≠] s, ‖deriv g w / g w‖ ≤ (36 * C₁ + C₃ + 57 * C₂) * Real.log T := by
      have hopen : IsOpen ((ball c 7) ∩ (((Z.erase s : Finset ℂ) : Set ℂ)ᶜ)) :=
        isOpen_ball.inter (Finset.finite_toSet _).isClosed.isOpen_compl
      have hmem : s ∈ (ball c 7) ∩ (((Z.erase s : Finset ℂ) : Set ℂ)ᶜ) :=
        ⟨hs, by simp⟩
      filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin]
        with w hw hws
      refine hbound_off w hw.1 fun hxw => ?_
      have hwZ : w ∈ Z := (hzeroZ w (ball_subset_ball (by norm_num) hw.1)).mp hxw
      exact hw.2 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hws, hwZ⟩))
    exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev

end

end RHTower
