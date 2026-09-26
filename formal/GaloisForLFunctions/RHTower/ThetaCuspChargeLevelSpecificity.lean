import GaloisForLFunctions.RHTower.ThetaCuspChargePolynomialRigidity
import GaloisForLFunctions.RHTower.ThetaCuspChargeRenewalIncrement
import GaloisForLFunctions.HTGeometry.EntireLogarithm
import GaloisForLFunctions.RHTower.FiniteZeroHadamardProduct

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ### Level sets of decaying subquadratic entire functions -/

/-- **Level specificity.**  A nonzero entire function of order `< 2` that decays on both real rays
takes every nonzero value infinitely often. -/
theorem levelSet_infinite_of_growth_decay {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C a : ℝ} (ha0 : 0 ≤ a) (ha2 : a < 2) (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ a))
    (hplus : Tendsto (fun r : ℝ => f (r : ℂ)) atTop (𝓝 0))
    (hminus : Tendsto (fun r : ℝ => f ((-r : ℝ) : ℂ)) atTop (𝓝 0))
    (hne : ∃ z, f z ≠ 0) {L : ℂ} (hL : L ≠ 0) :
    {z : ℂ | f z = L}.Infinite := by
  intro hfin
  set g : ℂ → ℂ := fun z => f z - L with hg
  have hgd : Differentiable ℂ g := hf.sub_const L
  have hgfin : {z : ℂ | g z = 0}.Finite := by
    refine hfin.subset (fun z hz => ?_)
    simp only [mem_setOf_eq, hg, sub_eq_zero] at hz ⊢; exact hz
  -- growth of `g`
  set C₂ : ℝ := C + ‖L‖ + 1 with hC₂
  have hggrowa : ∀ z, ‖g z‖ ≤ Real.exp (C₂ * (1 + ‖z‖) ^ a) := by
    intro z
    have h1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hr1 : 1 ≤ (1 + ‖z‖) ^ a := Real.one_le_rpow h1 ha0
    calc ‖g z‖ ≤ ‖f z‖ + ‖L‖ := by simp only [hg]; exact norm_sub_le _ _
      _ ≤ Real.exp (C * (1 + ‖z‖) ^ a) + ‖L‖ := by linarith [hgrow z]
      _ ≤ Real.exp (C * (1 + ‖z‖) ^ a) * Real.exp (‖L‖ + 1) := by
          have e2 : ‖L‖ + 2 ≤ Real.exp (‖L‖ + 1) := by
            have := Real.add_one_le_exp (‖L‖ + 1); linarith
          have e3 : 1 ≤ Real.exp (C * (1 + ‖z‖) ^ a) := Real.one_le_exp (by positivity)
          set X := Real.exp (C * (1 + ‖z‖) ^ a)
          have h4 := mul_le_mul_of_nonneg_left e2 (by linarith : (0:ℝ) ≤ X)
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ X - 1) (norm_nonneg L)]
      _ = Real.exp (C * (1 + ‖z‖) ^ a + (‖L‖ + 1)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (C₂ * (1 + ‖z‖) ^ a) := by
          apply Real.exp_le_exp.mpr; rw [hC₂]
          nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ ‖L‖ + 1) (by linarith : (0:ℝ) ≤ (1 + ‖z‖) ^ a - 1)]
  have hggrow : ∀ z, ‖g z‖ ≤ Real.exp (C₂ * (1 + ‖z‖) ^ (2 : ℕ)) := by
    intro z
    have h1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hra : (1 + ‖z‖) ^ a ≤ (1 + ‖z‖) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)
    exact le_trans (hggrowa z) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hra (by positivity)))
  obtain ⟨p, q, hp, hpq⟩ := exists_polynomial_mul_expPolynomial_of_finite_zeroSet hgd
    (by positivity : (0 : ℝ) ≤ C₂) hggrow hgfin
  obtain ⟨E, hE⟩ : ∃ E : ℂ → ℂ, E = fun z => Complex.exp (q.eval z) := ⟨_, rfl⟩
  have hpqE : ∀ z, g z = p.eval z * E z := by intro z; rw [hpq z, hE]
  have hEd : Differentiable ℂ E := by rw [hE]; exact fun z => (q.differentiable z).cexp
  have hEne : ∀ z, E z ≠ 0 := fun z => by rw [hE]; exact Complex.exp_ne_zero _
  -- a lower bound for `p` outside a ball
  obtain ⟨m, R, hm, hR⟩ : ∃ m R : ℝ, 0 < m ∧ ∀ z : ℂ, R ≤ ‖z‖ → m ≤ ‖p.eval z‖ := by
    rcases le_or_gt p.degree 0 with hdeg | hdeg
    · rw [Polynomial.eq_C_of_degree_le_zero hdeg] at hp ⊢
      have hc : p.coeff 0 ≠ 0 := by intro h; apply hp; rw [h, map_zero]
      exact ⟨‖p.coeff 0‖, 0, norm_pos_iff.mpr hc, fun z _ => by simp⟩
    · have ht := Polynomial.tendsto_norm_atTop p hdeg (tendsto_norm_cocompact_atTop (E := ℂ))
      have hev := ht.eventually (eventually_ge_atTop 1)
      rw [Filter.Eventually, Metric.mem_cocompact_iff_closedBall_compl_subset] at hev
      obtain ⟨R, hR⟩ := hev
      refine ⟨1, R + 1, one_pos, fun z hz => ?_⟩
      have : z ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
        simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]; linarith
      exact hR this
  -- growth of `E`
  have hEcont : Continuous E := hEd.continuous
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hEcont.continuousOn
  set K' : ℝ := max K (1 / m) + 1 with hK'
  have hK'1 : 1 ≤ K' := by
    rw [hK']; have h1 := le_max_right K (1 / m); have h2 : 0 < 1 / m := by positivity
    linarith
  have hEgrow : ∀ z, ‖E z‖ ≤ Real.exp ((Real.log K' + C₂) * (1 + ‖z‖) ^ a) := by
    intro z
    have h1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hr1 : 1 ≤ (1 + ‖z‖) ^ a := Real.one_le_rpow h1 ha0
    have hlog : 0 ≤ Real.log K' := Real.log_nonneg hK'1
    have hbase : ‖E z‖ ≤ K' * Real.exp (C₂ * (1 + ‖z‖) ^ a) := by
      have he1 : 1 ≤ Real.exp (C₂ * (1 + ‖z‖) ^ a) := Real.one_le_exp (by positivity)
      rcases le_or_gt ‖z‖ R with hz | hz
      · have := hK z (by simpa [Metric.mem_closedBall] using hz)
        have : ‖E z‖ ≤ K' := by have := le_max_left K (1 / m); linarith
        nlinarith
      · have hpz := hR z hz.le
        have hgz : g z = p.eval z * E z := hpqE z
        have hnorm : ‖g z‖ = ‖p.eval z‖ * ‖E z‖ := by rw [hgz, norm_mul]
        have hgb := hggrowa z
        have hEle : ‖E z‖ ≤ ‖g z‖ / m := by
          rw [le_div_iff₀ hm, hnorm]; nlinarith [norm_nonneg (E z)]
        have h1m : 1 / m ≤ K' := by have := le_max_right K (1 / m); linarith
        calc ‖E z‖ ≤ ‖g z‖ / m := hEle
          _ = 1 / m * ‖g z‖ := by ring
          _ ≤ K' * Real.exp (C₂ * (1 + ‖z‖) ^ a) :=
              mul_le_mul h1m hgb (norm_nonneg _) (by linarith)
    calc ‖E z‖ ≤ K' * Real.exp (C₂ * (1 + ‖z‖) ^ a) := hbase
      _ = Real.exp (Real.log K' + C₂ * (1 + ‖z‖) ^ a) := by
          rw [Real.exp_add, Real.exp_log (by linarith)]
      _ ≤ Real.exp ((Real.log K' + C₂) * (1 + ‖z‖) ^ a) := by
          apply Real.exp_le_exp.mpr; nlinarith
  obtain ⟨B, hB⟩ := GaloisForLFunctions.HTGeometry.exists_linear_of_ne_zero_of_growth hEd hEne ha0 ha2
    (by have := Real.log_nonneg hK'1; positivity) hEgrow
  have hgform : ∀ z, g z = p.eval z * E 0 * Complex.exp (B * z) := by
    intro z; rw [hpqE z, hB z]; ring
  -- behaviour on the real line
  have hgplus : Tendsto (fun r : ℝ => g (r : ℂ)) atTop (𝓝 (-L)) := by
    have := hplus.sub_const L; simpa [hg] using this
  have hgminus : Tendsto (fun r : ℝ => g ((-r : ℝ) : ℂ)) atTop (𝓝 (-L)) := by
    have := hminus.sub_const L; simpa [hg] using this
  have hE0 : E 0 ≠ 0 := hEne 0
  -- `p` is constant
  have hdeg : p.degree ≤ 0 := by
    by_contra hdeg
    push Not at hdeg
    have hprod : Tendsto (fun r : ℝ => g (r : ℂ) * g ((-r : ℝ) : ℂ)) atTop (𝓝 (-L * -L)) :=
      hgplus.mul hgminus
    have hform : ∀ r : ℝ, g (r : ℂ) * g ((-r : ℝ) : ℂ) =
        p.eval (r : ℂ) * p.eval ((-r : ℝ) : ℂ) * E 0 ^ 2 := by
      intro r
      rw [hgform, hgform]
      have : Complex.exp (B * (r : ℂ)) * Complex.exp (B * ((-r : ℝ) : ℂ)) = 1 := by
        rw [← Complex.exp_add]; push_cast; ring_nf; simp
      linear_combination (p.eval (r : ℂ) * p.eval ((-r : ℝ) : ℂ) * E 0 ^ 2) * this
    have hn1 : Tendsto (fun r : ℝ => ‖p.eval (r : ℂ)‖) atTop atTop :=
      Polynomial.tendsto_norm_atTop p hdeg (by
        simpa [Complex.norm_real, Real.norm_eq_abs] using tendsto_abs_atTop_atTop)
    have hn2 : Tendsto (fun r : ℝ => ‖p.eval ((-r : ℝ) : ℂ)‖) atTop atTop :=
      Polynomial.tendsto_norm_atTop p hdeg (by
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          tendsto_abs_atTop_atTop)
    have hn : Tendsto (fun r : ℝ => ‖g (r : ℂ) * g ((-r : ℝ) : ℂ)‖) atTop atTop := by
      have hE2 : 0 < ‖E 0 ^ 2‖ := norm_pos_iff.mpr (pow_ne_zero 2 hE0)
      have := (hn1.atTop_mul_atTop₀ hn2).atTop_mul_const hE2
      refine this.congr (fun r => ?_)
      rw [hform, norm_mul, norm_mul]
    exact not_tendsto_atTop_of_tendsto_nhds hprod.norm hn
  have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
  set K₀ : ℂ := p.coeff 0 * E 0 with hK₀
  have hgK : ∀ z, g z = K₀ * Complex.exp (B * z) := by
    intro z; rw [hgform, hpc]; simp [hK₀]
  -- `B = 0`
  have hexp1 : ∀ t : ℝ, Complex.exp (B * t) = 1 := by
    intro t
    have h1 : Tendsto (fun r : ℝ => g ((r + t : ℝ) : ℂ)) atTop (𝓝 (-L)) :=
      hgplus.comp (tendsto_atTop_add_const_right _ t tendsto_id)
    have h2 : Tendsto (fun r : ℝ => g ((r + t : ℝ) : ℂ)) atTop (𝓝 (Complex.exp (B * t) * -L)) := by
      refine (hgplus.const_mul (Complex.exp (B * t))).congr (fun r => ?_)
      rw [hgK, hgK]; push_cast; rw [mul_add, Complex.exp_add]; ring
    have := tendsto_nhds_unique h2 h1
    have hL' : -L ≠ 0 := neg_ne_zero.mpr hL
    have := mul_right_cancel₀ hL' (this.trans (one_mul (-L)).symm)
    exact this
  have hB0 : B = 0 := by
    have hd : HasDerivAt (fun t : ℝ => Complex.exp (B * t)) (B * Complex.exp (B * (0 : ℝ))) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul B).cexp
      simpa [mul_comm] using this
    have hc : (fun t : ℝ => Complex.exp (B * t)) = fun _ => 1 := funext hexp1
    rw [hc] at hd
    have := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
    simpa using this
  -- then `f ≡ 0`
  obtain ⟨z₀, hz₀⟩ := hne
  have hgc : ∀ z, g z = K₀ := by intro z; rw [hgK, hB0]; simp
  have hK₀L : K₀ = -L := by
    have : Tendsto (fun r : ℝ => g (r : ℂ)) atTop (𝓝 K₀) := by
      simp only [hgc]; exact tendsto_const_nhds
    exact tendsto_nhds_unique this hgplus
  apply hz₀
  have := hgc z₀
  simp only [hg] at this
  rw [hK₀L] at this
  linear_combination this

/-- **Finitely many real solutions at a nonzero level.** -/
theorem levelSet_real_finite_of_decay {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hplus : Tendsto (fun r : ℝ => f (r : ℂ)) atTop (𝓝 0))
    (hminus : Tendsto (fun r : ℝ => f ((-r : ℝ) : ℂ)) atTop (𝓝 0)) {L : ℂ} (hL : L ≠ 0) :
    {z : ℂ | f z = L ∧ z.im = 0}.Finite := by
  have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp (hplus.norm.eventually (gt_mem_nhds (by
    rw [norm_zero]; exact hLpos)))
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp (hminus.norm.eventually (gt_mem_nhds (by
    rw [norm_zero]; exact hLpos)))
  set U : ℝ := max (max U₁ U₂) 0 with hU
  have hne : ∀ x : ℝ, U ≤ |x| → f (x : ℂ) ≠ L := by
    intro x hx hfx
    rcases le_total 0 x with h0 | h0
    · have := hU₁ x (by rw [abs_of_nonneg h0] at hx; linarith [le_max_left U₁ U₂, le_max_left (max U₁ U₂) 0])
      rw [hfx] at this; linarith
    · have := hU₂ (-x) (by rw [abs_of_nonpos h0] at hx; linarith [le_max_right U₁ U₂, le_max_left (max U₁ U₂) 0])
      rw [neg_neg, hfx] at this; linarith
  set g : ℂ → ℂ := fun z => f z - L with hg
  have hgd : Differentiable ℂ g := hf.sub_const L
  have han := Complex.analyticOnNhd_univ_iff_differentiable.mpr hgd
  have hiso : ∀ z ∈ (univ : Set ℂ), ¬ (∀ᶠ w in 𝓝 z, g w = 0) := by
    intro z _ hz
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ z) hz
    have h1 := hzero (mem_univ ((U : ℝ) : ℂ))
    simp only [Pi.zero_apply, hg, sub_eq_zero] at h1
    exact hne U (by rw [abs_of_nonneg (le_max_right _ _)]) h1
  have hfinite := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact
    isOpen_univ hgd.differentiableOn hiso (isCompact_closedBall (0 : ℂ) (U + 1)) (subset_univ _)
  apply (hfinite.image id).subset
  intro z hz
  refine ⟨z, ⟨?_, ?_⟩, rfl⟩
  · have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hz.2
    have hr : |z.re| < U := by
      by_contra hr
      apply hne z.re (le_of_not_gt hr)
      rw [← hzreal]; exact hz.1
    rw [Metric.mem_closedBall, dist_zero_right, hzreal, Complex.norm_real, Real.norm_eq_abs]
    linarith
  · simp only [mem_setOf_eq, hg, hz.1, sub_self]

/-! ### Route 2, step 4: level specificity of `ξ` -/

theorem tendsto_XiC_ofReal_neg : Tendsto (fun r : ℝ => XiC ((-r : ℝ) : ℂ)) atTop (𝓝 0) := by
  refine tendsto_XiC_ofReal_atTop.congr (fun r => ?_)
  rw [Complex.ofReal_neg, XiC_neg]

/-- **Level specificity (route 2, step 4).**  For every complex `L ≠ 0` the equation `Ξ(z) = L`
has only finitely many real and infinitely many nonreal solutions.  Any winding or counting
argument for `Ξ = 0` must therefore use the level `0` specifically. -/
theorem XiC_level_specificity {L : ℂ} (hL : L ≠ 0) :
    {z : ℂ | XiC z = L ∧ z.im = 0}.Finite ∧ {z : ℂ | XiC z = L ∧ z.im ≠ 0}.Infinite := by
  have hfin := levelSet_real_finite_of_decay XiC_differentiable tendsto_XiC_ofReal_atTop
    tendsto_XiC_ofReal_neg hL
  refine ⟨hfin, fun hnr => ?_⟩
  obtain ⟨C, hC, hg⟩ := norm_XiC_growth_rpow
  have hinf := levelSet_infinite_of_growth_decay XiC_differentiable (by norm_num : (0:ℝ) ≤ 3 / 2)
    (by norm_num : (3 / 2 : ℝ) < 2) hC hg tendsto_XiC_ofReal_atTop tendsto_XiC_ofReal_neg
    ⟨-Complex.I / 2, by rw [XiC_neg_I_half]; norm_num⟩ hL
  apply hinf
  apply (hnr.union hfin).subset
  intro z hz
  by_cases him : z.im = 0
  · exact Or.inr ⟨hz, him⟩
  · exact Or.inl ⟨hz, him⟩

/-! ### Hardy's property in the affine module `θ₃·ℝ[h] ⊕ ℂ` -/

theorem tendsto_formXi_ofReal (P : Polynomial ℝ) :
    Tendsto (fun r : ℝ => formXi P (r : ℂ)) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_formXi_atTop P)

theorem tendsto_formXi_ofReal_neg (P : Polynomial ℝ) :
    Tendsto (fun r : ℝ => formXi P ((-r : ℝ) : ℂ)) atTop (𝓝 0) := by
  refine (tendsto_formXi_ofReal P).congr (fun r => ?_)
  rw [Complex.ofReal_neg, formXi_neg]

/-- **Affine Hardy characterization.**  For `(P, L) ≠ (0, 0)`, the transform of `θ₃P(h)` takes the
value `L` at infinitely many real points iff `L = 0` and `P` is a nonzero constant, i.e. iff the
function is a nonzero multiple of `ξ`. -/
theorem formXi_level_real_infinite_iff (P : Polynomial ℝ) (L : ℂ) (h : P ≠ 0 ∨ L ≠ 0) :
    {z : ℂ | formXi P z = L ∧ z.im = 0}.Infinite ↔ (L = 0 ∧ P.natDegree = 0) := by
  by_cases hL : L = 0
  · subst hL
    have hP : P ≠ 0 := h.resolve_right (by simp)
    simp only [true_and]
    exact formXi_real_zeros_infinite_iff P hP
  · have hfin := levelSet_real_finite_of_decay (differentiable_formXi P) (tendsto_formXi_ofReal P)
      (tendsto_formXi_ofReal_neg P) hL
    constructor
    · intro hinf; exact absurd hfin hinf
    · rintro ⟨h0, -⟩; exact absurd h0 hL



end RHTower
