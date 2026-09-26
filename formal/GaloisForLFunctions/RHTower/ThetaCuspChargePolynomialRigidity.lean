import GaloisForLFunctions.RHTower.ThetaCuspChargePowDominance

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

theorem exists_thetaGroupXi_growth (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖thetaGroupXi j z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [thetaGroupXi_zero_eq_XiC]; exact norm_XiC_growth_rpow
  · exact norm_thetaGroupXi_growth j hj.ne'

theorem tendsto_thetaGroupXi_norm_atTop (j : ℕ) :
    Tendsto (fun r : ℝ => ‖thetaGroupXi j (r : ℂ)‖) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [thetaGroupXi_zero_eq_XiC]; exact tendsto_XiC_norm_atTop
  · exact tendsto_thetaGroupXi_atTop j

theorem thetaGroupXi_neg (j : ℕ) (w : ℂ) : thetaGroupXi j (-w) = thetaGroupXi j w := by
  unfold thetaGroupXi
  exact modXi_neg (differentiableOn_thetaGroupBasis j) (thetaGroupBasis_axis j) w

/-- The transform of `θ₃P(h)` as a function of `z`. -/
def formXi (P : Polynomial ℝ) (z : ℂ) : ℂ := modXi (thetaGroupForm (P.map (algebraMap ℝ ℂ))) z

theorem formXi_eq_sum (P : Polynomial ℝ) (z : ℂ) :
    formXi P z = ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℂ) * thetaGroupXi j z :=
  modXi_thetaGroupForm_map P z

theorem differentiable_formXi (P : Polynomial ℝ) : Differentiable ℂ (formXi P) := by
  have e : formXi P = fun z => ∑ j ∈ Finset.range (P.natDegree + 1),
      (P.coeff j : ℂ) * thetaGroupXi j z := funext (formXi_eq_sum P)
  rw [e]
  exact Differentiable.fun_sum (fun j _ => (differentiable_thetaGroupXi j).const_mul _)

theorem formXi_neg (P : Polynomial ℝ) (z : ℂ) : formXi P (-z) = formXi P z := by
  rw [formXi_eq_sum, formXi_eq_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [thetaGroupXi_neg])

theorem formXi_growth (P : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖formXi P z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  choose Cf hCf0 hCf using exists_thetaGroupXi_growth
  set N := P.natDegree + 1
  set D : ℝ := ∑ j ∈ Finset.range N, (|P.coeff j| + Cf j) with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun j _ => by have := hCf0 j; positivity)
  refine ⟨N + D, by positivity, fun z => ?_⟩
  set R := (1 + ‖z‖) ^ (3 / 2 : ℝ)
  have hR : 1 ≤ R := Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  have hterm : ∀ j ∈ Finset.range N, ‖(P.coeff j : ℂ) * thetaGroupXi j z‖ ≤ Real.exp (D * R) := by
    intro j hj
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hle : |P.coeff j| + Cf j ≤ D :=
      Finset.single_le_sum (f := fun j => |P.coeff j| + Cf j)
        (fun i _ => by have := hCf0 i; positivity) hj
    have h1 : |P.coeff j| ≤ Real.exp (|P.coeff j|) := by
      have := Real.add_one_le_exp |P.coeff j|; linarith
    calc |P.coeff j| * ‖thetaGroupXi j z‖ ≤ Real.exp (|P.coeff j|) * Real.exp (Cf j * R) :=
          mul_le_mul h1 (hCf j z) (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (|P.coeff j| + Cf j * R) := by rw [Real.exp_add]
      _ ≤ Real.exp (D * R) := by
          apply Real.exp_le_exp.mpr
          have := hCf0 j
          nlinarith [abs_nonneg (P.coeff j)]
  rw [formXi_eq_sum]
  calc ‖∑ j ∈ Finset.range N, (P.coeff j : ℂ) * thetaGroupXi j z‖
      ≤ ∑ j ∈ Finset.range N, Real.exp (D * R) := norm_sum_le_of_le _ hterm
    _ = N * Real.exp (D * R) := by simp
    _ ≤ Real.exp N * Real.exp (D * R) := by
        gcongr; have := Real.add_one_le_exp (N : ℝ); linarith
    _ = Real.exp (N + D * R) := by rw [Real.exp_add]
    _ ≤ Real.exp ((N + D) * R) := by
        apply Real.exp_le_exp.mpr
        have : (0 : ℝ) ≤ N := by positivity
        nlinarith

theorem tendsto_formXi_atTop (P : Polynomial ℝ) :
    Tendsto (fun r : ℝ => ‖formXi P (r : ℂ)‖) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => ∑ j ∈ Finset.range (P.natDegree + 1),
      |P.coeff j| * ‖thetaGroupXi j (r : ℂ)‖) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.range (P.natDegree + 1))
      (fun j _ => (tendsto_thetaGroupXi_norm_atTop j).const_mul |P.coeff j|)
    simpa using this
  refine squeeze_zero (fun r => norm_nonneg _) (fun r => ?_) h
  rw [formXi_eq_sum]
  refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **Hardy rigidity of `ξ` in the module `θ₃·ℝ[h]`.**  For every real polynomial `P` of degree
`≥ 1`, the transform of the exactly `Γ_θ`-modular weight-½ form `θ₃P(h)` has only finitely many
real zeros and infinitely many nonreal zeros.  (For constant `P = c ≠ 0` it is `cΞ`, which has
infinitely many real zeros by Hardy's theorem.) -/
theorem thetaGroupForm_hardy_rigidity (P : Polynomial ℝ) (hP : 0 < P.natDegree) :
    {z : ℂ | formXi P z = 0 ∧ z.im = 0}.Finite ∧
      {z : ℂ | formXi P z = 0 ∧ z.im ≠ 0}.Infinite := by
  obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  obtain ⟨U, hU, hne⟩ := thetaGroupForm_eventually_ne_zero P hn
  have hf := differentiable_formXi P
  have hreal : {z : ℂ | formXi P z = 0 ∧ z.im = 0}.Finite := by
    have han := Complex.analyticOnNhd_univ_iff_differentiable.mpr hf
    have hiso : ∀ z ∈ (univ : Set ℂ), ¬ (∀ᶠ w in 𝓝 z, formXi P w = 0) := by
      intro z _ hz
      have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (mem_univ z) hz
      exact hne U le_rfl (hzero (mem_univ (U : ℂ)))
    have hfinite := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact
      isOpen_univ hf.differentiableOn hiso
      (isCompact_closedBall (0 : ℂ) (|U| + 1)) (subset_univ _)
    apply hfinite.subset
    intro z hz
    refine ⟨?_, hz.1⟩
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hz.2
    have habs : formXi P ((|z.re| : ℝ) : ℂ) = formXi P z := by
      conv_rhs => rw [hzreal]
      rcases le_total 0 z.re with hp | hn'
      · rw [abs_of_nonneg hp]
      · rw [abs_of_nonpos hn', Complex.ofReal_neg, formXi_neg]
    have hr : |z.re| < U := by
      by_contra hr
      exact hne |z.re| (le_of_not_gt hr) (habs.trans hz.1)
    rw [Metric.mem_closedBall, dist_zero_right, hzreal, Complex.norm_real, Real.norm_eq_abs]
    linarith [le_abs_self U]
  refine ⟨hreal, fun hfin => ?_⟩
  obtain ⟨C, hC, hg⟩ := formXi_growth P
  have hplus := tendsto_formXi_atTop P
  have hminus : Tendsto (fun r : ℝ => ‖formXi P ((-r : ℝ) : ℂ)‖) atTop (𝓝 0) := by
    refine hplus.congr (fun r => ?_)
    rw [Complex.ofReal_neg, formXi_neg]
  apply zeroSet_infinite_of_subquadratic_twoRayDecay hf (by norm_num : (0:ℝ) ≤ 3 / 2)
    (by norm_num : (3 / 2 : ℝ) < 2) hC hg hplus hminus
  apply (hfin.union hreal).subset
  intro z hz
  by_cases him : z.im = 0
  · exact Or.inr ⟨hz, him⟩
  · exact Or.inl ⟨hz, him⟩

/-- For constant polynomials the transform is a multiple of `Ξ`. -/
theorem formXi_C (c : ℝ) (z : ℂ) : formXi (Polynomial.C c) z = (c : ℂ) * XiC z := by
  rw [formXi_eq_sum]
  simp [thetaGroupXi_zero_eq_XiC]

/-- **Characterization of `ξ` in `θ₃·ℝ[h]` by Hardy's property.**  Among the transforms of the
nonzero exactly modular forms `θ₃P(h)`, `P ∈ ℝ[X]`, exactly the multiples of `ξ` have infinitely
many real zeros. -/
theorem formXi_real_zeros_infinite_iff (P : Polynomial ℝ) (hP0 : P ≠ 0) :
    {z : ℂ | formXi P z = 0 ∧ z.im = 0}.Infinite ↔ P.natDegree = 0 := by
  constructor
  · intro hinf
    by_contra h
    exact hinf (thetaGroupForm_hardy_rigidity P (Nat.pos_of_ne_zero h)).1
  · intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h]
    have hc : P.coeff 0 ≠ 0 := by
      intro hc0; apply hP0
      rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc0, map_zero]
    have e : {z : ℂ | formXi (Polynomial.C (P.coeff 0)) z = 0 ∧ z.im = 0} =
        {z : ℂ | XiC z = 0 ∧ z.im = 0} := by
      ext z; simp only [mem_setOf_eq, formXi_C, mul_eq_zero, Complex.ofReal_eq_zero, hc, false_or]
    rw [e]; exact XiC_real_zeroSet_infinite

end RHTower
