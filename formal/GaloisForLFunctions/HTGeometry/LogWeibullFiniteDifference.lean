import GaloisForLFunctions.HTGeometry.StretchedExponentialFiniteDifference

open Filter Finset Set Asymptotics Topology

namespace GaloisForLFunctions

noncomputable section

def logWeibull (γ x : ℝ) : ℝ :=
  stretchedExp γ (Real.log x)

theorem iteratedDeriv_log_of_posOrder (k : ℕ) (hk : 0 < k) (x : ℝ) :
    iteratedDeriv k Real.log x =
      (-1 : ℝ) ^ (k - 1) * (k - 1).factorial * x ^ (-(k : ℤ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [iteratedDeriv_eq_iterate, Function.iterate_succ_apply,
    Real.deriv_log', iter_deriv_inv]
  congr 2
  push_cast
  omega

theorem finset_prod_zpow_eq_zpow_sum_of_ne_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (e : ι → ℤ) {x : ℝ} (hx : x ≠ 0) :
    ∏ i ∈ s, x ^ e i = x ^ ∑ i ∈ s, e i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      exact (zpow_add₀ hx _ _).symm

private def logPartitionCoefficient {k : ℕ}
    (c : OrderedFinpartition k) : ℝ :=
  ∏ j : Fin c.length,
    (-1 : ℝ) ^ (c.partSize j - 1) * (c.partSize j - 1).factorial

theorem prod_iteratedDeriv_log_eq
    {k : ℕ} (c : OrderedFinpartition k) {x : ℝ} (hx : x ≠ 0) :
    ∏ j : Fin c.length, iteratedDeriv (c.partSize j) Real.log x =
      logPartitionCoefficient c * x ^ (-(k : ℤ)) := by
  simp_rw [iteratedDeriv_log_of_posOrder _ (c.partSize_pos _)]
  rw [Finset.prod_mul_distrib]
  change logPartitionCoefficient c *
      (∏ j : Fin c.length, x ^ (-((c.partSize j : ℕ) : ℤ))) = _
  rw [finset_prod_zpow_eq_zpow_sum_of_ne_zero Finset.univ
    (fun j : Fin c.length => -((c.partSize j : ℕ) : ℤ)) hx]
  congr 1
  have hcard : ∑ j : Fin c.length, c.partSize j = k := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using
      Fintype.card_congr c.equivSigma
  have hcardZ : ∑ j : Fin c.length, (c.partSize j : ℤ) = (k : ℤ) := by
    exact_mod_cast hcard
  rw [Finset.sum_neg_distrib, hcardZ]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Exact partition formula for every derivative of the log-Weibull profile. -/
theorem iteratedDeriv_logWeibull_exact
    (γ x : ℝ) (k : ℕ) (hx : 1 < x) :
    iteratedDeriv k (logWeibull γ) x =
      ∑ c : OrderedFinpartition k,
        iteratedDeriv c.length (stretchedExp γ) (Real.log x) *
          (logPartitionCoefficient c * x ^ (-(k : ℤ))) := by
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hout : ContDiffAt ℝ ⊤ (stretchedExp γ) (Real.log x) := by
    exact Real.contDiff_exp.contDiffAt.comp (Real.log x)
      (Real.contDiffAt_rpow_const_of_ne hlogpos.ne')
  have hin : ContDiffAt ℝ ⊤ Real.log x :=
    Real.contDiffAt_log.mpr (by linarith)
  change iteratedDeriv k (stretchedExp γ ∘ Real.log) x = _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hout hin le_top]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prod_iteratedDeriv_log_eq c (by linarith)]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Leading scale of the `k`th log-Weibull derivative. -/
def logWeibullDerivativeLeading (γ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  γ ^ k * stretchedExp γ (Real.log x) *
    (Real.log x) ^ ((k : ℝ) * (γ - 1)) * x ^ (-(k : ℤ))

private def logWeibullPartitionTerm {k : ℕ}
    (γ : ℝ) (c : OrderedFinpartition k) (x : ℝ) : ℝ :=
  iteratedDeriv c.length (stretchedExp γ) (Real.log x) *
    (logPartitionCoefficient c * x ^ (-(k : ℤ)))

private def logWeibullPartitionModel {k : ℕ}
    (γ : ℝ) (c : OrderedFinpartition k) (x : ℝ) : ℝ :=
  stretchedDerivativeLeading γ c.length (Real.log x) *
    (logPartitionCoefficient c * x ^ (-(k : ℤ)))

private theorem logWeibullPartitionTerm_isEquivalent_model
    {γ : ℝ} (hγ : 0 < γ) {k : ℕ} (c : OrderedFinpartition k) :
    logWeibullPartitionTerm γ c ~[atTop] logWeibullPartitionModel γ c := by
  have houter := (iteratedDeriv_stretchedExp_isEquivalent hγ c.length).comp_tendsto
    Real.tendsto_log_atTop
  have hfactor : (fun x : ℝ => logPartitionCoefficient c * x ^ (-(k : ℤ)))
      ~[atTop] fun x : ℝ => logPartitionCoefficient c * x ^ (-(k : ℤ)) :=
    IsEquivalent.refl
  simpa only [logWeibullPartitionTerm, logWeibullPartitionModel,
    Function.comp_apply] using! houter.mul hfactor

private theorem logWeibullPartitionModel_isLittleO_leading
    {γ : ℝ} (hγ : 1 < γ) {k : ℕ}
    (c : OrderedFinpartition k) (hc : c ≠ OrderedFinpartition.atomic k) :
    logWeibullPartitionModel γ c =o[atTop] logWeibullDerivativeLeading γ k := by
  have hlen : c.length < k := c.length_lt_of_ne_atomic hc
  have hlenR : (c.length : ℝ) < (k : ℝ) := by exact_mod_cast hlen
  let δ : ℝ := ((k : ℝ) - (c.length : ℝ)) * (γ - 1)
  have hδ : 0 < δ := mul_pos (sub_pos.mpr hlenR) (sub_pos.mpr hγ)
  refine (isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    intro hzero
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hlead : logWeibullDerivativeLeading γ k x ≠ 0 := by
      dsimp [logWeibullDerivativeLeading, logWeibull]
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (pow_ne_zero _ (by linarith : γ ≠ 0))
            (Real.exp_ne_zero _))
          (ne_of_gt (Real.rpow_pos_of_pos hlogpos _)))
        (zpow_ne_zero _ (by linarith : x ≠ 0))
    exact (hlead hzero).elim
  · let C : ℝ := logPartitionCoefficient c * γ ^ c.length / γ ^ k
    have ht := (tendsto_rpow_neg_atTop hδ).comp Real.tendsto_log_atTop
    have htC : Tendsto (fun x : ℝ => C * (Real.log x) ^ (-δ)) atTop (𝓝 0) := by
      simpa using ht.const_mul C
    refine htC.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hγ0 : γ ≠ 0 := by linarith
    dsimp [logWeibullPartitionModel, logWeibullDerivativeLeading,
      stretchedDerivativeLeading, stretchedExp, logWeibull, C]
    field_simp [pow_ne_zero _ hγ0, Real.exp_ne_zero,
      ne_of_gt (Real.rpow_pos_of_pos hlogpos ((k : ℝ) * (γ - 1))),
      zpow_ne_zero _ hx0]
    rw [mul_assoc, ← Real.rpow_add hlogpos]
    congr 2
    dsimp [δ]
    ring

private theorem logWeibullPartitionTerm_isLittleO_leading
    {γ : ℝ} (hγ : 1 < γ) {k : ℕ}
    (c : OrderedFinpartition k) (hc : c ≠ OrderedFinpartition.atomic k) :
    logWeibullPartitionTerm γ c =o[atTop] logWeibullDerivativeLeading γ k :=
  (logWeibullPartitionTerm_isEquivalent_model (by linarith) c).trans_isLittleO
    (logWeibullPartitionModel_isLittleO_leading hγ c hc)

private theorem logWeibullPartitionTerm_atomic_isEquivalent
    {γ : ℝ} (hγ : 1 < γ) (k : ℕ) :
    logWeibullPartitionTerm γ (OrderedFinpartition.atomic k) ~[atTop]
      logWeibullDerivativeLeading γ k := by
  have houter := (iteratedDeriv_stretchedExp_isEquivalent (by linarith) k).comp_tendsto
    Real.tendsto_log_atTop
  have hxpow : (fun x : ℝ => x ^ (-(k : ℤ))) ~[atTop]
      fun x : ℝ => x ^ (-(k : ℤ)) := IsEquivalent.refl
  have hmul := houter.mul hxpow
  refine hmul.congr_left ?_ |>.congr_right ?_
  · filter_upwards with x
    simp [logWeibullPartitionTerm, logPartitionCoefficient]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    dsimp [stretchedDerivativeLeading, logWeibullDerivativeLeading,
      logWeibull, stretchedExp]
    ring

/-- Every fixed derivative of the log-Weibull profile is asymptotic to the expected Bell-leading
monomial. -/
theorem iteratedDeriv_logWeibull_isEquivalent
    {γ : ℝ} (hγ : 1 < γ) (k : ℕ) :
    (fun x => iteratedDeriv k (logWeibull γ) x) ~[atTop]
      logWeibullDerivativeLeading γ k := by
  let a : OrderedFinpartition k := OrderedFinpartition.atomic k
  let R : ℝ → ℝ := fun x =>
    ∑ c ∈ (Finset.univ : Finset (OrderedFinpartition k)).erase a,
      logWeibullPartitionTerm γ c x
  have hR : R =o[atTop] logWeibullDerivativeLeading γ k := by
    exact IsLittleO.sum fun c hc =>
      logWeibullPartitionTerm_isLittleO_leading hγ c
        (Finset.ne_of_mem_erase hc)
  have heq : (fun x => iteratedDeriv k (logWeibull γ) x) =ᶠ[atTop]
      fun x => logWeibullPartitionTerm γ a x + R x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [iteratedDeriv_logWeibull_exact γ x k hx]
    change (∑ c : OrderedFinpartition k, logWeibullPartitionTerm γ c x) = _
    rw [← Finset.sum_erase_add Finset.univ
      (fun c : OrderedFinpartition k => logWeibullPartitionTerm γ c x)
      (Finset.mem_univ a)]
    simp only [R]
    ring
  have hmain := logWeibullPartitionTerm_atomic_isEquivalent hγ k
  have htotal := hmain.add_isLittleO hR
  exact htotal.congr_left (heq.mono fun x hx => hx.symm)

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

def logWeibullExponent (γ x : ℝ) : ℝ :=
  (Real.log x) ^ γ

lemma hasDerivAt_logWeibullExponent
    (γ : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (logWeibullExponent γ)
      (γ * (Real.log x) ^ (γ - 1) / x) x := by
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hout := Real.hasDerivAt_rpow_const (x := Real.log x) (p := γ)
    (Or.inl hlogpos.ne')
  have hin := Real.hasDerivAt_log (by linarith : x ≠ 0)
  simpa [logWeibullExponent, div_eq_mul_inv, mul_assoc] using! hout.comp x hin

lemma tendsto_logWeibullExponent_deriv_zero
    {γ : ℝ} (hγ : 1 < γ) :
    Tendsto (fun x : ℝ => γ * (Real.log x) ^ (γ - 1) / x)
      atTop (𝓝 0) := by
  have htcore := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (γ - 1) 1 one_pos
  have ht := htcore.comp Real.tendsto_log_atTop
  have htγ : Tendsto (fun x : ℝ =>
      γ * ((Real.log x) ^ (γ - 1) * Real.exp (-(1 * Real.log x))))
      atTop (𝓝 0) := by
    simpa using ht.const_mul γ
  refine htγ.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [one_mul, Real.exp_neg, Real.exp_log hx0]
  field_simp

lemma tendsto_logWeibullExponent_add_sub_zero
    {γ r : ℝ} (hγ : 1 < γ) (hr : 0 ≤ r) :
    Tendsto (fun x : ℝ =>
      logWeibullExponent γ (x + r) - logWeibullExponent γ x)
      atTop (𝓝 0) := by
  have hderiv := tendsto_logWeibullExponent_deriv_zero hγ
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C := ε / (r + 1)
  have hC : 0 < C := div_pos hε (by linarith)
  have hderivNorm : Tendsto
      (fun x : ℝ => ‖γ * (Real.log x) ^ (γ - 1) / x‖) atTop (𝓝 0) := by
    simpa using hderiv.norm
  have hsmall := hderivNorm.eventually_lt_const hC
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨max Y 2, fun x hx => ?_⟩
  have hxY : Y ≤ x := (le_max_left Y 2).trans hx
  have hx2 : 2 ≤ x := (le_max_right Y 2).trans hx
  have hxr : x ≤ x + r := by linarith
  have hdiff : ‖logWeibullExponent γ (x + r) - logWeibullExponent γ x‖ ≤
      C * ‖(x + r) - x‖ := by
    apply (convex_Icc x (x + r)).norm_image_sub_le_of_norm_deriv_le
      (f := logWeibullExponent γ)
    · intro y hy
      exact (hasDerivAt_logWeibullExponent γ (by linarith [hy.1])).differentiableAt
    · intro y hy
      rw [(hasDerivAt_logWeibullExponent γ (by linarith [hy.1])).deriv]
      exact (hY y (hxY.trans hy.1)).le
    · exact left_mem_Icc.mpr hxr
    · exact right_mem_Icc.mpr hxr
  have hrnorm : ‖(x + r) - x‖ = r := by
    rw [show x + r - x = r by ring, Real.norm_eq_abs, abs_of_nonneg hr]
  rw [hrnorm] at hdiff
  have hCr : C * r < ε := by
    dsimp [C]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by linarith : 0 < r + 1)).2 (by nlinarith)
  simpa only [dist_zero_right] using hdiff.trans_lt hCr

lemma tendsto_logWeibull_fixedShift_ratio
    {γ r : ℝ} (hγ : 1 < γ) (hr : 0 ≤ r) :
    Tendsto (fun x : ℝ => logWeibull γ (x + r) / logWeibull γ x)
      atTop (𝓝 1) := by
  have hdiff := tendsto_logWeibullExponent_add_sub_zero hγ hr
  have hexp : Tendsto (fun x : ℝ => Real.exp
      (logWeibullExponent γ (x + r) - logWeibullExponent γ x))
      atTop (𝓝 1) := by
    simpa using! Real.continuous_exp.continuousAt.tendsto.comp hdiff
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp [logWeibull, stretchedExp, logWeibullExponent] at *
  rw [Real.exp_sub]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

lemma tendsto_log_add_div_log (r : ℝ) :
    Tendsto (fun x : ℝ => Real.log (x + r) / Real.log x) atTop (𝓝 1) := by
  have hsmall :=
    (Real.tendsto_log_comp_add_sub_log r).div_atTop Real.tendsto_log_atTop
  have hadd :=
    (tendsto_const_nhds : Tendsto (fun _x : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hsmall
  simpa only [add_zero] using hadd.congr' (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    field_simp
    ring)

lemma tendsto_log_rpow_div_id_zero (p : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ p / x) atTop (𝓝 0) := by
  have htcore := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p 1 one_pos
  have ht := htcore.comp Real.tendsto_log_atTop
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  simp only [Function.comp_apply]
  rw [show -(1 : ℝ) * Real.log x = -Real.log x by ring,
    Real.exp_neg, Real.exp_log hx0]
  field_simp

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

private def logWeibullDerivativeEnvelope
    (γ : ℝ) (k : ℕ) (r x : ℝ) : ℝ :=
  γ ^ k * logWeibull γ (x + r) *
    (Real.log (x + r)) ^ ((k : ℝ) * (γ - 1)) * x ^ (-(k : ℤ))

private theorem logWeibullDerivativeEnvelope_succ_isLittleO_leading
    {γ : ℝ} (hγ : 1 < γ) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    logWeibullDerivativeEnvelope γ (j + 1) r =o[atTop]
      logWeibullDerivativeLeading γ j := by
  refine (isLittleO_iff_tendsto' ?_).2 ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    intro hzero
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    have hγ0 : γ ≠ 0 := by linarith
    have hx0 : x ≠ 0 := by linarith
    have hlead : logWeibullDerivativeLeading γ j x ≠ 0 := by
      dsimp [logWeibullDerivativeLeading, logWeibull, stretchedExp]
      exact mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (pow_ne_zero _ hγ0) (Real.exp_ne_zero _))
          (ne_of_gt (Real.rpow_pos_of_pos hlogpos _)))
        (zpow_ne_zero _ hx0)
    exact (hlead hzero).elim
  · have hB := tendsto_logWeibull_fixedShift_ratio hγ hr
    have hlog := tendsto_log_add_div_log r
    let e : ℝ := ((j + 1 : ℕ) : ℝ) * (γ - 1)
    have hlogPow : Tendsto
        (fun x : ℝ => (Real.log (x + r) / Real.log x) ^ e)
        atTop (𝓝 1) := by
      have hp : ContinuousAt (fun y : ℝ => y ^ e) 1 :=
        continuousAt_id.rpow_const (Or.inl one_ne_zero)
      have hc := hp.tendsto.comp hlog
      simpa [e] using! hc
    have hcore := tendsto_log_rpow_div_id_zero (γ - 1)
    have htotal : Tendsto (fun x : ℝ =>
        γ * (logWeibull γ (x + r) / logWeibull γ x) *
          (Real.log (x + r) / Real.log x) ^ e *
            ((Real.log x) ^ (γ - 1) / x)) atTop (𝓝 0) := by
      simpa using (((tendsto_const_nhds.mul hB).mul hlogPow).mul hcore)
    refine htotal.congr' ?_
    filter_upwards [eventually_gt_atTop (max 1 (-r + 1))] with x hx
    have hx1 : 1 < x := (le_max_left (1 : ℝ) (-r + 1)).trans_lt hx
    have hxr1 : 1 < x + r := by linarith
    have hx0 : x ≠ 0 := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos hx1
    have hlogrpos : 0 < Real.log (x + r) := Real.log_pos hxr1
    have hγ0 : γ ≠ 0 := by linarith
    dsimp [logWeibullDerivativeEnvelope, logWeibullDerivativeLeading, e]
    rw [Real.div_rpow hlogrpos.le hlogpos.le]
    rw [show (((j + 1 : ℕ) : ℝ) * (γ - 1)) =
        (j : ℝ) * (γ - 1) + (γ - 1) by push_cast; ring]
    rw [Real.rpow_add hlogpos]
    dsimp [logWeibull, stretchedExp]
    field_simp [pow_ne_zero _ hγ0, Real.exp_ne_zero,
      ne_of_gt (Real.rpow_pos_of_pos hlogpos ((j : ℝ) * (γ - 1))),
      ne_of_gt (Real.rpow_pos_of_pos hlogrpos
        (((j + 1 : ℕ) : ℝ) * (γ - 1))), zpow_ne_zero _ hx0]
    rw [zpow_neg, zpow_neg]
    simp only [zpow_natCast]
    rw [zpow_add₀ hx0 (j : ℤ) 1]
    simp only [zpow_natCast, zpow_one]
    rw [pow_succ]
    field_simp [pow_ne_zero _ hx0]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

private def logWeibullTaylorShift
    (γ : ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    iteratedDeriv k (logWeibull γ) x * r ^ k / (k.factorial : ℝ)

private lemma taylorWithinEval_logWeibull_add_eq
    {γ x r : ℝ} (hx : 1 < x) (hr : 0 < r) (j : ℕ) :
    taylorWithinEval (logWeibull γ) j (uIcc x (x + r)) x (x + r) =
      logWeibullTaylorShift γ j r x := by
  have hle : x ≤ x + r := by linarith
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (logWeibull γ) x := by
    have hlogpos : 0 < Real.log x := Real.log_pos hx
    exact Real.contDiff_exp.contDiffAt.comp x
      ((Real.contDiffAt_rpow_const_of_ne hlogpos.ne').comp x
        (Real.contDiffAt_log.mpr (by linarith)))
  rw [uIcc_of_le hle]
  induction j with
  | zero => simp [logWeibullTaylorShift, iteratedDeriv_zero]
  | succ j ih =>
      rw [taylorWithinEval_succ, ih]
      simp only [logWeibullTaylorShift, Finset.sum_range_succ]
      have hderiv : iteratedDerivWithin (j + 1) (logWeibull γ)
          (Icc x (x + r)) x = iteratedDeriv (j + 1) (logWeibull γ) x := by
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
          (hf.of_le (WithTop.coe_le_coe.mpr le_top)) (left_mem_Icc.mpr hle)
      rw [hderiv, Nat.factorial_succ]
      push_cast
      ring

private def logWeibullTaylorRemainderBound
    (C γ : ℝ) (j : ℕ) (r x : ℝ) : ℝ :=
  C * logWeibullDerivativeEnvelope γ (j + 1) r x *
    r ^ (j + 1) / (j.factorial : ℝ)

private theorem logWeibullTaylorRemainderBound_isLittleO
    {γ : ℝ} (hγ : 1 < γ) (j : ℕ) {r C : ℝ} (hr : 0 ≤ r) :
    logWeibullTaylorRemainderBound C γ j r =o[atTop]
      logWeibullDerivativeLeading γ j := by
  have h := logWeibullDerivativeEnvelope_succ_isLittleO_leading hγ j hr
  have hconst := h.const_mul_left (C * r ^ (j + 1) / (j.factorial : ℝ))
  exact hconst.congr_left fun x => by
    dsimp [logWeibullTaylorRemainderBound]
    ring

private theorem logWeibull_taylor_remainder_isLittleO
    {γ r : ℝ} (hγ : 1 < γ) (hr : 0 ≤ r) (j : ℕ) :
    (fun x => logWeibull γ (x + r) - logWeibullTaylorShift γ j r x)
      =o[atTop] logWeibullDerivativeLeading γ j := by
  rcases hr.eq_or_lt with rfl | hr
  · have heq : ∀ x, logWeibullTaylorShift γ j 0 x = logWeibull γ x := by
      intro x
      rw [logWeibullTaylorShift, Finset.sum_eq_single 0]
      · simp [iteratedDeriv_zero]
      · intro k hk hne
        simp [zero_pow hne]
      · simp
    simpa only [add_zero, heq, sub_self] using
      (Asymptotics.isLittleO_zero (logWeibullDerivativeLeading γ j) atTop)
  have hderivO := (iteratedDeriv_logWeibull_isEquivalent hγ (j + 1)).isBigO
  obtain ⟨C, hCnonneg, hC⟩ := hderivO.exists_nonneg
  obtain ⟨Y, hCY⟩ := Filter.eventually_atTop.mp hC.bound
  have hremBound : ∀ᶠ x in atTop,
      ‖logWeibull γ (x + r) - logWeibullTaylorShift γ j r x‖ ≤
        logWeibullTaylorRemainderBound C γ j r x := by
    filter_upwards [eventually_ge_atTop (max Y 2)] with x hx
    have hxY : Y ≤ x := (le_max_left Y 2).trans hx
    have hx2 : 2 ≤ x := (le_max_right Y 2).trans hx
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hle : x ≤ x + r := by linarith
    have hlt : x < x + r := by linarith
    have hcont : ContDiffOn ℝ (j + 1 : ℕ) (logWeibull γ) (Icc x (x + r)) := by
      intro y hy
      have hy1 : 1 < y := hx1.trans_le hy.1
      have hlogpos : 0 < Real.log y := Real.log_pos hy1
      exact (Real.contDiff_exp.contDiffAt.comp y
        ((Real.contDiffAt_rpow_const_of_ne hlogpos.ne').comp y
          (Real.contDiffAt_log.mpr (by linarith)))).contDiffWithinAt
    have hiter : ∀ y ∈ Icc x (x + r),
        ‖iteratedDerivWithin (j + 1) (logWeibull γ) (Icc x (x + r)) y‖ ≤
          C * logWeibullDerivativeEnvelope γ (j + 1) r x := by
      intro y hy
      have hy1 : 1 < y := hx1.trans_le hy.1
      have hy0 : 0 < y := by linarith
      have hyY : Y ≤ y := hxY.trans hy.1
      have hlogy : 0 < Real.log y := Real.log_pos hy1
      have hlogxr : 0 < Real.log (x + r) := Real.log_pos (hx1.trans_le hle)
      have hfull : iteratedDerivWithin (j + 1) (logWeibull γ)
          (Icc x (x + r)) y = iteratedDeriv (j + 1) (logWeibull γ) y := by
        have hyCont : ContDiffAt ℝ (j + 1 : ℕ) (logWeibull γ) y := by
          exact Real.contDiff_exp.contDiffAt.comp y
            ((Real.contDiffAt_rpow_const_of_ne hlogy.ne').comp y
              (Real.contDiffAt_log.mpr (by linarith)))
        exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hlt)
          hyCont hy
      rw [hfull]
      have hbase := hCY y hyY
      have hleadPos : 0 < logWeibullDerivativeLeading γ (j + 1) y := by
        dsimp [logWeibullDerivativeLeading, logWeibull, stretchedExp]
        positivity
      rw [show ‖logWeibullDerivativeLeading γ (j + 1) y‖ =
          logWeibullDerivativeLeading γ (j + 1) y by
        rw [Real.norm_eq_abs, abs_of_pos hleadPos]] at hbase
      have hlogle : Real.log y ≤ Real.log (x + r) :=
        Real.log_le_log (by linarith) hy.2
      have hprofile : logWeibull γ y ≤ logWeibull γ (x + r) := by
        dsimp [logWeibull, stretchedExp]
        apply Real.exp_le_exp.mpr
        exact Real.rpow_le_rpow hlogy.le hlogle (by linarith)
      have hexpNonneg : 0 ≤ (((j + 1 : ℕ) : ℝ) * (γ - 1)) :=
        mul_nonneg (by positivity) (by linarith)
      have hlogpow : (Real.log y) ^ (((j + 1 : ℕ) : ℝ) * (γ - 1)) ≤
          (Real.log (x + r)) ^ (((j + 1 : ℕ) : ℝ) * (γ - 1)) :=
        Real.rpow_le_rpow hlogy.le hlogle hexpNonneg
      have hpow : x ^ (j + 1) ≤ y ^ (j + 1) :=
        pow_le_pow_left₀ hx0.le hy.1 _
      have hzpow : y ^ (-((j + 1 : ℕ) : ℤ)) ≤
          x ^ (-((j + 1 : ℕ) : ℤ)) := by
        rw [zpow_neg, zpow_neg]
        simp only [zpow_natCast]
        exact inv_anti₀ (pow_pos hx0 _) hpow
      have hleadEnvelope : logWeibullDerivativeLeading γ (j + 1) y ≤
          logWeibullDerivativeEnvelope γ (j + 1) r x := by
        dsimp [logWeibullDerivativeLeading, logWeibullDerivativeEnvelope]
        have hγpow : 0 ≤ γ ^ (j + 1) := by positivity
        have hprofileNonneg : 0 ≤ logWeibull γ (x + r) := by
          dsimp [logWeibull, stretchedExp]
          positivity
        have hlogpowNonneg : 0 ≤
            (Real.log (x + r)) ^ (((j + 1 : ℕ) : ℝ) * (γ - 1)) :=
          Real.rpow_nonneg hlogxr.le _
        calc
          γ ^ (j + 1) * stretchedExp γ (Real.log y) *
              (Real.log y) ^ (((j + 1 : ℕ) : ℝ) * (γ - 1)) *
                y ^ (-(((j + 1 : ℕ) : ℤ))) ≤
            γ ^ (j + 1) * logWeibull γ (x + r) *
              (Real.log y) ^ (((j + 1 : ℕ) : ℝ) * (γ - 1)) *
                y ^ (-(((j + 1 : ℕ) : ℤ))) := by
                  have hprofile' : stretchedExp γ (Real.log y) ≤
                      logWeibull γ (x + r) := by simpa [logWeibull] using hprofile
                  gcongr
          _ ≤ γ ^ (j + 1) * logWeibull γ (x + r) *
              (Real.log (x + r)) ^ (((j + 1 : ℕ) : ℝ) * (γ - 1)) *
                y ^ (-(((j + 1 : ℕ) : ℤ))) := by
                  gcongr
          _ ≤ γ ^ (j + 1) * logWeibull γ (x + r) *
              (Real.log (x + r)) ^ (((j + 1 : ℕ) : ℝ) * (γ - 1)) *
                x ^ (-(((j + 1 : ℕ) : ℤ))) := by
                  exact mul_le_mul_of_nonneg_left hzpow
                    (mul_nonneg (mul_nonneg hγpow hprofileNonneg) hlogpowNonneg)
      exact hbase.trans (mul_le_mul_of_nonneg_left hleadEnvelope hCnonneg)
    have htaylor := taylor_mean_remainder_bound hle hcont
      (right_mem_Icc.mpr hle) hiter
    have hteq := taylorWithinEval_logWeibull_add_eq
      (γ := γ) hx1 hr j
    rw [uIcc_of_le hle] at hteq
    rw [hteq] at htaylor
    simpa [logWeibullTaylorRemainderBound, sub_eq_add_neg, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using htaylor
  have hboundLittle := logWeibullTaylorRemainderBound_isLittleO
    hγ j hr.le (C := C)
  refine IsLittleO.of_bound fun c hc => ?_
  have hcB := (hboundLittle.forall_isBigOWith hc).bound
  filter_upwards [hremBound, hcB] with x hxrem hxB
  calc
    ‖logWeibull γ (x + r) - logWeibullTaylorShift γ j r x‖
        ≤ logWeibullTaylorRemainderBound C γ j r x := hxrem
    _ ≤ ‖logWeibullTaylorRemainderBound C γ j r x‖ := le_abs_self _
    _ ≤ c * ‖logWeibullDerivativeLeading γ j x‖ := hxB

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Fixed-shift finite difference of a log-Weibull profile. -/
def logWeibullFiniteDifference
    (γ : ℝ) (d : ℕ →₀ ℝ) (x : ℝ) : ℝ :=
  d.sum fun r a => a * logWeibull γ (x + r)

private lemma finsupp_sum_logWeibullTaylorShift_eq
    {γ : ℝ} (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0) (x : ℝ) :
    d.sum (fun r a => a * logWeibullTaylorShift γ j r x) =
      stretchedMoment d j * iteratedDeriv j (logWeibull γ) x /
        (j.factorial : ℝ) := by
  classical
  rw [Finsupp.sum]
  simp_rw [logWeibullTaylorShift, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hjterm :
      (∑ r ∈ d.support,
          d r * (iteratedDeriv j (logWeibull γ) x * (r : ℝ) ^ j /
            (j.factorial : ℝ))) =
        stretchedMoment d j * iteratedDeriv j (logWeibull γ) x /
          (j.factorial : ℝ) := by
    rw [stretchedMoment, Finsupp.sum]
    simp only [div_eq_mul_inv]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [← hjterm]
  apply Finset.sum_eq_single j
  · intro k hk hkj
    have hkle : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkl : k < j := lt_of_le_of_ne hkle hkj
    have hsum : (∑ r ∈ d.support, d r * (r : ℝ) ^ k) = 0 := by
      simpa only [stretchedMoment, Finsupp.sum] using hcancel k hkl
    calc
      (∑ r ∈ d.support,
          d r * (iteratedDeriv k (logWeibull γ) x * (r : ℝ) ^ k /
            (k.factorial : ℝ))) =
          (iteratedDeriv k (logWeibull γ) x / (k.factorial : ℝ)) *
            ∑ r ∈ d.support, d r * (r : ℝ) ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = 0 := by rw [hsum, mul_zero]
  · simp

/-- Leading term of a log-Weibull finite difference whose first surviving moment is `j`. -/
def logWeibullFiniteDifferenceLeading
    (γ : ℝ) (d : ℕ →₀ ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  (stretchedMoment d j / (j.factorial : ℝ)) *
    logWeibullDerivativeLeading γ j x

/-- First-surviving-moment asymptotic for every fixed log-Weibull difference packet. -/
theorem logWeibullFiniteDifference_isEquivalent
    {γ : ℝ} (hγ : 1 < γ) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0) :
    logWeibullFiniteDifference γ d ~[atTop]
      logWeibullFiniteDifferenceLeading γ d j := by
  classical
  let A : ℝ := stretchedMoment d j / (j.factorial : ℝ)
  have hA : A ≠ 0 := div_ne_zero hmoment (by positivity)
  let R : ℝ → ℝ := fun x => d.sum fun r a =>
    a * (logWeibull γ (x + r) - logWeibullTaylorShift γ j r x)
  have hR : R =o[atTop] fun x => A * logWeibullDerivativeLeading γ j x := by
    have hs :
        (fun x => ∑ r ∈ d.support,
          d r * (logWeibull γ (x + r) - logWeibullTaylorShift γ j r x))
          =o[atTop] fun x => A * logWeibullDerivativeLeading γ j x := by
      exact IsLittleO.sum fun r hr =>
        ((logWeibull_taylor_remainder_isLittleO hγ
          (show (0 : ℝ) ≤ (r : ℝ) by positivity) j).const_mul_left (d r)).const_mul_right hA
    simpa only [R, Finsupp.sum] using hs
  have heq : logWeibullFiniteDifference γ d =ᶠ[atTop]
      fun x => A * iteratedDeriv j (logWeibull γ) x + R x := by
    apply Eventually.of_forall
    intro x
    have hTaylor := finsupp_sum_logWeibullTaylorShift_eq (γ := γ) d j hcancel x
    rw [Finsupp.sum] at hTaylor
    rw [logWeibullFiniteDifference, Finsupp.sum]
    have hsplit :
        (∑ r ∈ d.support, d r * logWeibull γ (x + r)) =
          (∑ r ∈ d.support, d r * logWeibullTaylorShift γ j r x) +
            ∑ r ∈ d.support,
              d r * (logWeibull γ (x + r) -
                logWeibullTaylorShift γ j r x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hsplit, hTaylor]
    simp only [A, R, Finsupp.sum]
    ring
  have hconst : (fun _ : ℝ => A) ~[atTop] fun _ : ℝ => A := IsEquivalent.refl
  have hmain := hconst.mul (iteratedDeriv_logWeibull_isEquivalent hγ j)
  have htotal := hmain.add_isLittleO hR
  have hleft := htotal.congr_left (heq.mono fun x hx => hx.symm)
  refine hleft.congr_right (Eventually.of_forall fun x => ?_)
  rfl

/-- A positive first surviving moment fixes the eventual sign of the finite difference. -/
theorem eventually_pos_logWeibullFiniteDifference
    {γ : ℝ} (hγ : 1 < γ) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : 0 < stretchedMoment d j) :
    ∀ᶠ x : ℝ in atTop, 0 < logWeibullFiniteDifference γ d x := by
  apply (logWeibullFiniteDifference_isEquivalent hγ d j hcancel hmoment.ne').eventually_pos
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  dsimp [logWeibullFiniteDifferenceLeading, logWeibullDerivativeLeading,
    logWeibull, stretchedExp]
  positivity

/-- Every fixed forward shift is asymptotically invisible at the derivative-leading scale. -/
theorem tendsto_logWeibullDerivativeLeading_fixedShift_ratio
    {γ : ℝ} (hγ : 1 < γ) (k : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun x : ℝ =>
      logWeibullDerivativeLeading γ k (x + r) /
        logWeibullDerivativeLeading γ k x) atTop (𝓝 1) := by
  let p : ℝ := (k : ℝ) * (γ - 1)
  have hprofile := tendsto_logWeibull_fixedShift_ratio hγ hr
  have hlogRatio : Tendsto
      (fun x : ℝ => (Real.log (x + r) / Real.log x) ^ p) atTop (𝓝 1) := by
    simpa using (tendsto_log_add_div_log r).rpow tendsto_const_nhds
      (Or.inl one_ne_zero)
  have hbase : Tendsto (fun x : ℝ => (x + r) / x) atTop (𝓝 1) := by
    have ht : Tendsto (fun x : ℝ => 1 + r * x⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := r)).mul tendsto_inv_atTop_zero)
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    field_simp
  have hzpow : Tendsto (fun x : ℝ => ((x + r) / x) ^ (-(k : ℤ))) atTop (𝓝 1) := by
    simpa using hbase.zpow₀ (-(k : ℤ)) (Or.inl one_ne_zero)
  have htotal := (hprofile.mul hlogRatio).mul hzpow
  simpa only [one_mul] using htotal.congr' (by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hxr0 : x + r ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hlogr0 : Real.log (x + r) ≠ 0 :=
      (Real.log_pos (by linarith)).ne'
    dsimp [logWeibullDerivativeLeading, p]
    rw [Real.div_rpow (Real.log_nonneg (by linarith)) (Real.log_nonneg hx.le),
      div_zpow]
    dsimp [logWeibull, stretchedExp]
    field_simp [pow_ne_zero _ (by linarith : γ ≠ 0), Real.exp_ne_zero,
      hlog0, hlogr0, zpow_ne_zero _ hx0, zpow_ne_zero _ hxr0])

/-- A finite-difference packet with nonzero leading moment is stable under every fixed shift. -/
theorem tendsto_logWeibullFiniteDifference_fixedShift_ratio
    {γ : ℝ} (hγ : 1 < γ) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0) (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun x : ℝ =>
      logWeibullFiniteDifference γ d (x + r) /
        logWeibullFiniteDifference γ d x) atTop (𝓝 1) := by
  let L := logWeibullFiniteDifferenceLeading γ d j
  have hLne : ∀ᶠ x : ℝ in atTop, L x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    dsimp [L, logWeibullFiniteDifferenceLeading, logWeibullDerivativeLeading,
      logWeibull, stretchedExp]
    positivity
  have hFL : Tendsto (fun x : ℝ => logWeibullFiniteDifference γ d x / L x)
      atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hLne).mp
      (logWeibullFiniteDifference_isEquivalent hγ d j hcancel hmoment)
  have hshift : Tendsto (fun x : ℝ => x + r) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hFLshift : Tendsto
      (fun x : ℝ => logWeibullFiniteDifference γ d (x + r) / L (x + r))
      atTop (𝓝 1) := hFL.comp hshift
  have hLratio : Tendsto (fun x : ℝ => L (x + r) / L x) atTop (𝓝 1) := by
    have hderiv := tendsto_logWeibullDerivativeLeading_fixedShift_ratio hγ j r hr
    simpa only [L, logWeibullFiniteDifferenceLeading] using hderiv.congr' (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hA : stretchedMoment d j / (j.factorial : ℝ) ≠ 0 :=
        div_ne_zero hmoment (by positivity)
      have hlead0 : logWeibullDerivativeLeading γ j x ≠ 0 := by
        have hlog : 0 < Real.log x := Real.log_pos hx
        dsimp [logWeibullDerivativeLeading, logWeibull, stretchedExp]
        positivity
      field_simp)
  have hLF : Tendsto (fun x : ℝ => L x / logWeibullFiniteDifference γ d x)
      atTop (𝓝 1) := by
    have hinv := hFL.inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using hinv
  have htotal := (hFLshift.mul hLratio).mul hLF
  simpa only [one_mul] using htotal.congr' (by
    have hLneShift := hshift.eventually hLne
    have hFne : ∀ᶠ x : ℝ in atTop, logWeibullFiniteDifference γ d x ≠ 0 := by
      exact (hFL.eventually_const_lt (show (0 : ℝ) < 1 by norm_num)).mono fun x hx hzero => by
        rw [hzero, zero_div] at hx
        linarith
    filter_upwards [hLne, hLneShift, hFne] with x hLx hLxr hFx
    field_simp)

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

lemma tendsto_rpow_mul_exp_nat_mul_sub_rpow_zero
    {γ : ℝ} (hγ : 1 < γ) (s : ℝ) (m : ℕ) :
    Tendsto (fun t : ℝ => t ^ s * Real.exp ((m : ℝ) * t - t ^ γ))
      atTop (𝓝 0) := by
  have hγpos : 0 < γ := by linarith
  have hpowTop := tendsto_rpow_atTop (sub_pos.mpr hγ)
  have hdom := hpowTop.eventually_ge_atTop (2 * m)
  have hcore0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (s / γ) (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have hcore := hcore0.comp (tendsto_rpow_atTop hγpos)
  have hcore' : Tendsto
      (fun t : ℝ => t ^ s * Real.exp (-(1 / 2) * t ^ γ))
      atTop (𝓝 0) := by
    refine hcore.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul ht.le]
    congr 2
    field_simp [ne_of_gt hγpos]
  apply squeeze_zero'
    (g := fun t : ℝ => t ^ s * Real.exp (-(1 / 2) * t ^ γ))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    positivity
  · filter_upwards [hdom, eventually_gt_atTop (1 : ℝ)] with t htdom ht
    have htpos : 0 < t := by linarith
    have hpowSplit : t ^ γ = t ^ (γ - 1) * t := by
      calc
        t ^ γ = t ^ ((γ - 1) + 1) := by congr 1 <;> ring
        _ = t ^ (γ - 1) * t ^ (1 : ℝ) := Real.rpow_add htpos _ _
        _ = t ^ (γ - 1) * t := by rw [Real.rpow_one]
    have hexponent : (m : ℝ) * t - t ^ γ ≤ -(1 / 2) * t ^ γ := by
      rw [hpowSplit]
      have htdom' : (2 : ℝ) * (m : ℝ) ≤ t ^ (γ - 1) := by
        simpa using htdom
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
      (Real.rpow_nonneg htpos.le _)
  · exact hcore'

/-- Every nonzero log-Weibull difference packet dominates the logarithm. -/
theorem log_isLittleO_abs_logWeibullFiniteDifference
    {γ : ℝ} (hγ : 1 < γ) (d : ℕ →₀ ℝ) (j : ℕ)
    (hcancel : ∀ k < j, stretchedMoment d k = 0)
    (hmoment : stretchedMoment d j ≠ 0) :
    Real.log =o[atTop] fun x => |logWeibullFiniteDifference γ d x| := by
  let C : ℝ := stretchedMoment d j / (j.factorial : ℝ) * γ ^ j
  have hC : C ≠ 0 := mul_ne_zero
    (div_ne_zero hmoment (by positivity)) (pow_ne_zero _ (by linarith : γ ≠ 0))
  let p : ℝ := (j : ℝ) * (γ - 1)
  have htcore := tendsto_rpow_mul_exp_nat_mul_sub_rpow_zero
    hγ (-p) (j + 1)
  have htcomp := htcore.comp Real.tendsto_log_atTop
  have ht : Tendsto (fun x : ℝ => |C|⁻¹ *
      ((Real.log x) ^ (-p) *
        Real.exp (((j + 1 : ℕ) : ℝ) * Real.log x - (Real.log x) ^ γ)))
      atTop (𝓝 0) := by
    simpa using htcomp.const_mul |C|⁻¹
  have hxlead : (fun x : ℝ => x) =o[atTop]
      fun x => |logWeibullFiniteDifferenceLeading γ d j x| := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      intro hzero
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hx0 : x ≠ 0 := by linarith
      have hlead : logWeibullFiniteDifferenceLeading γ d j x ≠ 0 := by
        have hA : stretchedMoment d j / (j.factorial : ℝ) ≠ 0 :=
          div_ne_zero hmoment (by positivity)
        have hmain : logWeibullDerivativeLeading γ j x ≠ 0 := by
          dsimp [logWeibullDerivativeLeading, logWeibull, stretchedExp]
          exact mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero (pow_ne_zero _ (by linarith : γ ≠ 0))
                (Real.exp_ne_zero _))
              (ne_of_gt (Real.rpow_pos_of_pos hlogpos _)))
            (zpow_ne_zero _ hx0)
        dsimp [logWeibullFiniteDifferenceLeading, logWeibullDerivativeLeading,
          logWeibull, stretchedExp]
        exact mul_ne_zero hA hmain
      exact (abs_ne_zero.mpr hlead hzero).elim
    · refine ht.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hx0 : 0 < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hγ0 : γ ≠ 0 := by linarith
      have hzpos : 0 < x ^ (-(j : ℤ)) := by positivity
      have hlogpowpos : 0 < (Real.log x) ^ ((j : ℝ) * (γ - 1)) :=
        Real.rpow_pos_of_pos hlogpos _
      have habsLead : |logWeibullFiniteDifferenceLeading γ d j x| =
          |C| * Real.exp ((Real.log x) ^ γ) *
            (Real.log x) ^ ((j : ℝ) * (γ - 1)) * x ^ (-(j : ℤ)) := by
        dsimp [logWeibullFiniteDifferenceLeading, logWeibullDerivativeLeading,
          logWeibull, stretchedExp, C]
        rw [abs_mul, abs_mul, abs_mul, abs_mul,
          abs_of_pos (Real.exp_pos _), abs_of_pos hlogpowpos,
          abs_of_pos hzpos]
        rw [abs_mul]
        ring
      rw [habsLead]
      dsimp [p]
      apply (eq_div_iff ?_).2
      · rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hx0]
        rw [zpow_neg, zpow_natCast]
        rw [Real.rpow_neg hlogpos.le]
        field_simp [abs_ne_zero.mpr hC, Real.exp_ne_zero,
          ne_of_gt hlogpowpos, pow_ne_zero _ hx0.ne']
        rw [pow_succ]
      · exact mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero (abs_ne_zero.mpr hC) (Real.exp_ne_zero _))
            (ne_of_gt hlogpowpos))
          (zpow_ne_zero _ hx0.ne')
  have hlogLead : Real.log =o[atTop]
      fun x => |logWeibullFiniteDifferenceLeading γ d j x| := by
    simpa only [id_eq] using Real.isLittleO_log_id_atTop.trans hxlead
  have heq := logWeibullFiniteDifference_isEquivalent hγ d j hcancel hmoment
  have htheta := heq.isTheta.norm_left.norm_right
  simpa only [Real.norm_eq_abs] using hlogLead.trans_isTheta htheta.symm

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

lemma tendsto_rpow_add_sub_atTop
    {γ a : ℝ} (hγ : 1 < γ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => (t + a) ^ γ - t ^ γ) atTop atTop := by
  have hlow : Tendsto (fun t : ℝ => γ * a * t ^ (γ - 1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hγ)).const_mul_atTop (mul_pos (by linarith) ha)
  refine tendsto_atTop_mono' atTop ?_ hlow
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  have htpos : 0 < t := by linarith
  let s := a / t
  have hs0 : 0 ≤ s := by dsimp [s]; exact div_nonneg ha.le htpos.le
  have hs : -1 ≤ s := by linarith
  have hbern := one_add_mul_self_le_rpow_one_add hs hγ.le
  have htpow : 0 < t ^ γ := Real.rpow_pos_of_pos htpos _
  have hmul := mul_le_mul_of_nonneg_left hbern htpow.le
  have hfactor : t + a = t * (1 + s) := by
    dsimp [s]
    field_simp
  have hpowFactor : (t + a) ^ γ = t ^ γ * (1 + s) ^ γ := by
    rw [hfactor, Real.mul_rpow htpos.le (by linarith)]
  rw [← hpowFactor] at hmul
  have hlinear : t ^ γ * (γ * s) = γ * a * t ^ (γ - 1) := by
    dsimp [s]
    rw [show γ = (γ - 1) + 1 by ring, Real.rpow_add htpos, Real.rpow_one]
    field_simp
    ring
  nlinarith

lemma tendsto_logWeibull_mul_div_atTop
    {γ c : ℝ} (hγ : 1 < γ) (hc : 1 < c) :
    Tendsto (fun x : ℝ => logWeibull γ (c * x) / logWeibull γ x)
      atTop atTop := by
  have hlogc : 0 < Real.log c := Real.log_pos hc
  have hlogcx : Tendsto (fun x : ℝ =>
      logWeibullExponent γ (c * x) - logWeibullExponent γ x)
      atTop atTop := by
    have hcore := (tendsto_rpow_add_sub_atTop hγ hlogc).comp Real.tendsto_log_atTop
    refine hcore.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hc0 : c ≠ 0 := by linarith
    dsimp [logWeibullExponent]
    rw [Real.log_mul hc0 hx0]
    ring
  have hexp := Real.tendsto_exp_atTop.comp hlogcx
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp [logWeibull, stretchedExp, logWeibullExponent]
  rw [Real.exp_sub]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- First forward-difference stencil. -/
def logWeibullFirstStencil : ℕ →₀ ℝ :=
  Finsupp.single 1 1 - Finsupp.single 0 1

/-- Second forward-difference stencil. -/
def logWeibullSecondStencil : ℕ →₀ ℝ :=
  Finsupp.single 2 1 - Finsupp.single 1 2 + Finsupp.single 0 1

private theorem logWeibullFirstStencil_sum (g : ℕ → ℝ) :
    logWeibullFirstStencil.sum (fun r a => a * g r) = g 1 - g 0 := by
  rw [logWeibullFirstStencil, Finsupp.sum_sub_index]
  · simp
  · intro a b₁ b₂
    ring

private theorem logWeibullSecondStencil_sum (g : ℕ → ℝ) :
    logWeibullSecondStencil.sum (fun r a => a * g r) =
      g 2 - 2 * g 1 + g 0 := by
  rw [logWeibullSecondStencil,
    Finsupp.sum_add_index (by intros; simp) (by intros; ring),
    Finsupp.sum_sub_index (by intros; ring)]
  simp

theorem logWeibullFirstStencil_moments :
    stretchedMoment logWeibullFirstStencil 0 = 0 ∧
    stretchedMoment logWeibullFirstStencil 1 = 1 := by
  constructor <;> rw [stretchedMoment, logWeibullFirstStencil_sum] <;> norm_num

theorem logWeibullSecondStencil_moments :
    stretchedMoment logWeibullSecondStencil 0 = 0 ∧
    stretchedMoment logWeibullSecondStencil 1 = 0 ∧
    stretchedMoment logWeibullSecondStencil 2 = 2 := by
  constructor
  · rw [stretchedMoment, logWeibullSecondStencil_sum]
    norm_num
  constructor <;>
    rw [stretchedMoment, logWeibullSecondStencil_sum] <;> norm_num

theorem logWeibullFiniteDifference_first (γ x : ℝ) :
    logWeibullFiniteDifference γ logWeibullFirstStencil x =
      logWeibull γ (x + 1) - logWeibull γ x := by
  simpa [logWeibullFiniteDifference] using
    logWeibullFirstStencil_sum (fun r => logWeibull γ (x + (r : ℝ)))

theorem logWeibullFiniteDifference_second (γ x : ℝ) :
    logWeibullFiniteDifference γ logWeibullSecondStencil x =
      logWeibull γ (x + 2) - 2 * logWeibull γ (x + 1) +
        logWeibull γ x := by
  simpa [logWeibullFiniteDifference] using
    logWeibullSecondStencil_sum (fun r => logWeibull γ (x + (r : ℝ)))

end

end GaloisForLFunctions
