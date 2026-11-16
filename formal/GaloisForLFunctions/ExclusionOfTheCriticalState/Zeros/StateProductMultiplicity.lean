import GaloisForLFunctions.ExclusionOfTheCriticalState.TheProductOfTheStateWithXiIsEntire

/-!
# Multiplicities of the entire state product

Write `E(w) = ξ(w + 17/2) M(w)` for the entire cleared state. At a centred zero `z`
seen by the Laplace transform, the order of `E` at `z - 8` is one less than the order
of `ξ` at `1/2 + z`. Indeed, locally the cleared pairing is `ξ R + L ξ'`: the first
term vanishes to higher order than the second. Every zero on or right of the
critical line is seen by an actual critical state.
-/

noncomputable section
open Complex Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- An analytic unit multiplying the derivative lowers the order of a zero by exactly one;
adding an analytic multiple of the original function cannot cancel its leading term. -/
private theorem analyticOrderAt_mul_add_mul_deriv {f g r : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hr : AnalyticAt ℂ r z)
    (hfz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) (hgz : g z ≠ 0) :
    analyticOrderAt (fun w => f w * r w + g w * deriv f w) z + 1 =
      analyticOrderAt f z := by
  have hd : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa only [hfz, sub_zero] using hf.analyticOrderAt_deriv_add_one
  have hdne : analyticOrderAt (deriv f) z ≠ ⊤ := by
    intro h
    exact hfinite (by rw [← hd, h, top_add])
  have hgd : analyticOrderAt (g * deriv f) z = analyticOrderAt (deriv f) z := by
    rw [analyticOrderAt_mul hg hf.deriv, hg.analyticOrderAt_eq_zero.mpr hgz, zero_add]
  have hlt : analyticOrderAt (g * deriv f) z < analyticOrderAt (f * r) z := by
    rw [hgd, analyticOrderAt_mul hf hr]
    apply lt_of_lt_of_le _ le_self_add
    rw [← hd]
    exact (ENat.add_one_le_iff hdne).mp le_rfl
  change analyticOrderAt (f * r + g * deriv f) z + 1 = _
  rw [analyticOrderAt_add_eq_right_of_lt hlt, hgd, hd]

/-- If the derivative coefficient also vanishes, neither summand can have smaller order
than the original function. -/
private theorem le_analyticOrderAt_mul_add_mul_deriv {f g r : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hr : AnalyticAt ℂ r z)
    (hfz : f z = 0) (hgz : g z = 0) :
    analyticOrderAt f z ≤ analyticOrderAt (fun w => f w * r w + g w * deriv f w) z := by
  have hd : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa only [hfz, sub_zero] using hf.analyticOrderAt_deriv_add_one
  have hgpos : 1 ≤ analyticOrderAt g z :=
    (ENat.add_one_le_iff (by simp : (0 : ℕ∞) ≠ ⊤)).mpr
      (bot_lt_iff_ne_bot.mpr (analyticOrderAt_ne_zero.mpr ⟨hg, hgz⟩))
  change analyticOrderAt f z ≤ analyticOrderAt (f * r + g * deriv f) z
  apply le_trans _ le_analyticOrderAt_add
  apply le_min
  · rw [analyticOrderAt_mul hf hr]
    exact le_self_add
  · rw [analyticOrderAt_mul hg hf.deriv, ← hd, add_comm]
    exact add_le_add_left hgpos _

theorem analyticAt_regularRemainder {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : -2 < p.re) : AnalyticAt ℂ (regularRemainder F) p := by
  have hd : DifferentiableOn ℂ (regularRemainder F) {w : ℂ | -2 < w.re} :=
    fun w hw => (differentiableAt_regularRemainder hF hw).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp)

private theorem analyticAt_energyLaplace {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : -4 < p.re) : AnalyticAt ℂ (negativeHalfLineLaplace (cx F)) p := by
  have hd : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {w : ℂ | -4 < w.re} :=
    fun w hw => (differentiableAt_laplace hF hw).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp)

private theorem analyticOrderAt_xi_half_add (z : ℂ) :
    analyticOrderAt (fun p : ℂ => xi (1 / 2 + p)) z = analyticOrderAt xi (1 / 2 + z) := by
  apply analyticOrderAt_comp_of_deriv_ne_zero (f := xi)
    (g := fun p : ℂ => 1 / 2 + p) (by fun_prop)
  simp

private theorem deriv_xi_half_add :
    deriv (fun p : ℂ => xi (1 / 2 + p)) = fun p => deriv xi (1 / 2 + p) := by
  funext p
  simpa only [Function.comp_def, one_mul, mul_one] using
    ((xi_differentiable (1 / 2 + p)).hasDerivAt.comp p
      ((hasDerivAt_id p).const_add (1 / 2 : ℂ))).deriv

private theorem clearedRemainder_eventually_eq (F : ℝ → ℝ) {z : ℂ} (hz : -2 < z.re) :
    clearedRemainder F =ᶠ[𝓝 z]
      (fun p => xi (1 / 2 + p) * regularRemainder F p +
        negativeHalfLineLaplace (cx F) p * deriv xi (1 / 2 + p)) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with p hp
  exact clearedRemainder_of_gt hp

/-- At any seen zero, the cleared pairing has order exactly one less than `ξ`. -/
theorem analyticOrderAt_clearedRemainder_add_one {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z : ℂ} (hxi : xi (1 / 2 + z) = 0)
    (hL : negativeHalfLineLaplace (cx F) z ≠ 0) :
    analyticOrderAt (clearedRemainder F) z + 1 = analyticOrderAt xi (1 / 2 + z) := by
  have hz : -2 < z.re := by
    have := (abs_lt.mp (abs_re_lt_of_xi_eq_zero hxi)).1
    linarith
  rw [analyticOrderAt_congr (clearedRemainder_eventually_eq F hz)]
  have h := analyticOrderAt_mul_add_mul_deriv
    (differentiable_xi_half_add.analyticAt z) (analyticAt_energyLaplace hF (by linarith))
    (analyticAt_regularRemainder hF hz) hxi
    (by rw [analyticOrderAt_xi_half_add]; exact xi_order_ne_top _) hL
  simpa only [deriv_xi_half_add, analyticOrderAt_xi_half_add] using h

/-- At an unseen zero, clearing the pairing preserves at least the full multiplicity of `ξ`. -/
theorem le_analyticOrderAt_clearedRemainder_of_laplace_eq_zero {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z : ℂ} (hxi : xi (1 / 2 + z) = 0)
    (hL : negativeHalfLineLaplace (cx F) z = 0) :
    analyticOrderAt xi (1 / 2 + z) ≤ analyticOrderAt (clearedRemainder F) z := by
  have hz : -2 < z.re := by
    have := (abs_lt.mp (abs_re_lt_of_xi_eq_zero hxi)).1
    linarith
  rw [analyticOrderAt_congr (clearedRemainder_eventually_eq F hz)]
  have h := le_analyticOrderAt_mul_add_mul_deriv
    (differentiable_xi_half_add.analyticAt z) (analyticAt_energyLaplace hF (by linarith))
    (analyticAt_regularRemainder hF hz) hxi hL
  simpa only [deriv_xi_half_add, analyticOrderAt_xi_half_add] using h

/-- Translation and the nonzero normalization preserve the order of the cleared pairing. -/
theorem analyticOrderAt_stateXiProduct {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (w : ℂ) :
    analyticOrderAt (stateXiProduct W₀ F) w = analyticOrderAt (clearedRemainder F) (w + 8) := by
  have ha : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have heq : stateXiProduct W₀ F =
      (fun _ : ℂ => -(criticalAliasCoefficient W₀ : ℂ)⁻¹) *
        (fun w => clearedRemainder F (w + 8)) := by
    funext w
    simp only [stateXiProduct, Pi.mul_apply, div_eq_mul_inv, neg_mul]
    ring
  have hd : Differentiable ℂ (fun v : ℂ => clearedRemainder F (v + 8)) :=
    (differentiable_clearedRemainder hF).comp (differentiable_id.add (differentiable_const _))
  rw [heq, analyticOrderAt_mul analyticAt_const (hd.analyticAt w),
    (analyticAt_const.analyticOrderAt_eq_zero.mpr (neg_ne_zero.mpr (inv_ne_zero ha))), zero_add]
  apply analyticOrderAt_comp_of_deriv_ne_zero (f := clearedRemainder F)
    (g := fun v : ℂ => v + 8) (by fun_prop)
  simp

/-- At a seen zero of multiplicity `m`, the entire state product has order `m - 1` at the
shifted point, independently of whether the original zero is simple. -/
theorem analyticOrderAt_stateXiProduct_add_one {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z : ℂ} (hxi : xi (1 / 2 + z) = 0)
    (hL : negativeHalfLineLaplace (cx F) z ≠ 0) :
    analyticOrderAt (stateXiProduct W₀ F) (z - 8) + 1 = analyticOrderAt xi (1 / 2 + z) := by
  rw [analyticOrderAt_stateXiProduct hW hF, sub_add_cancel]
  exact analyticOrderAt_clearedRemainder_add_one hF hxi hL

/-- Full multiplicity in the cleared product detects precisely the zeros invisible to the
profile's Laplace transform. -/
theorem le_analyticOrderAt_stateXiProduct_iff {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z : ℂ} (hxi : xi (1 / 2 + z) = 0) :
    analyticOrderAt xi (1 / 2 + z) ≤ analyticOrderAt (stateXiProduct W₀ F) (z - 8) ↔
      negativeHalfLineLaplace (cx F) z = 0 := by
  constructor
  · intro h
    by_contra hL
    have heq := analyticOrderAt_stateXiProduct_add_one hW hF hxi hL
    have hfinite : analyticOrderAt (stateXiProduct W₀ F) (z - 8) ≠ ⊤ := by
      intro htop
      exact xi_order_ne_top _ (by rw [← heq, htop, top_add])
    have hlt := (ENat.add_one_le_iff hfinite).mp heq.le
    exact (not_lt_of_ge h) hlt
  · intro hL
    rw [analyticOrderAt_stateXiProduct hW hF, sub_add_cancel]
    exact le_analyticOrderAt_clearedRemainder_of_laplace_eq_zero hF hxi hL

/-- Every zero on or right of the line loses exactly one unit of multiplicity in the
entire product attached to a critical state. -/
theorem criticalState_stateXiProduct_order {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : XiZeroCopy}
    (hc : 0 ≤ (centredZero c).re) :
    analyticOrderAt (stateXiProduct W₀ F) (centredZero c - 8) + 1 =
      analyticOrderAt xi (1 / 2 + centredZero c) :=
  analyticOrderAt_stateXiProduct_add_one hW (criticalHalfLineEnergyDomain_of_groundState hF)
    (xi_centredZero c)
    (criticalHalfLineGroundState_closedRightHalfPlaneLaplace_ne_zero hW hthreshold hF hc)

/-- Natural-number multiplicities satisfy the same exact drop at every seen zero. -/
theorem analyticOrderNatAt_stateXiProduct_add_one {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z : ℂ} (hxi : xi (1 / 2 + z) = 0)
    (hL : negativeHalfLineLaplace (cx F) z ≠ 0) :
    analyticOrderNatAt (stateXiProduct W₀ F) (z - 8) + 1 =
      analyticOrderNatAt xi (1 / 2 + z) := by
  have heq := analyticOrderAt_stateXiProduct_add_one hW hF hxi hL
  have hfinite : analyticOrderAt (stateXiProduct W₀ F) (z - 8) ≠ ⊤ := by
    intro htop
    exact xi_order_ne_top _ (by rw [← heq, htop, top_add])
  simpa [analyticOrderNatAt, ENat.toNat_add, hfinite] using congrArg ENat.toNat heq

/-- If a seen zero of `ξ` has multiplicity `m`, the first nonzero jet of the entire
state product is precisely its `(m - 1)`-st derivative. -/
theorem stateXiProduct_first_nonzero_jet {W₀ : ℝ} (hW : 0 < W₀) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {z : ℂ} (hxi : xi (1 / 2 + z) = 0)
    (hL : negativeHalfLineLaplace (cx F) z ≠ 0) :
    let m := analyticOrderNatAt xi (1 / 2 + z)
    (∀ j < m - 1, iteratedDeriv j (stateXiProduct W₀ F) (z - 8) = 0) ∧
      iteratedDeriv (m - 1) (stateXiProduct W₀ F) (z - 8) ≠ 0 := by
  have heq := analyticOrderAt_stateXiProduct_add_one hW hF hxi hL
  have hfinite : analyticOrderAt (stateXiProduct W₀ F) (z - 8) ≠ ⊤ := by
    intro htop
    exact xi_order_ne_top _ (by rw [← heq, htop, top_add])
  have hnat := analyticOrderNatAt_stateXiProduct_add_one hW hF hxi hL
  apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    ((differentiable_stateXiProduct hF).analyticAt (z - 8))).mp
  rw [← Nat.cast_analyticOrderNatAt hfinite]
  congr 1
  omega

/-- Either RH holds, or an actual critical state's entire cleared transform has order `m - 1`
at the shifted copy of every `ξ`-zero of multiplicity `m` on or right of the critical line. -/
theorem riemannHypothesis_or_criticalState_exact_multiplicities :
    RiemannHypothesis ∨
      ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
        IsCriticalHalfLineGroundState W₀ F ∧
        Differentiable ℂ (stateXiProduct W₀ F) ∧
        ∀ c : XiZeroCopy, 0 ≤ (centredZero c).re →
          analyticOrderAt (stateXiProduct W₀ F) (centredZero c - 8) + 1 =
            analyticOrderAt xi (1 / 2 + centredZero c) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF,
      differentiable_stateXiProduct (criticalHalfLineEnergyDomain_of_groundState hF),
      fun _ hc => criticalState_stateXiProduct_order hW ht hF hc⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState

#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.riemannHypothesis_or_criticalState_exact_multiplicities
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.le_analyticOrderAt_stateXiProduct_iff
#print axioms GaloisForLFunctions.ExclusionOfTheCriticalState.stateXiProduct_first_nonzero_jet
