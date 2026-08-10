import GaloisForLFunctions.HTGeometry.EulerQGammaTranslation

/-!
# The zeta ladder of the Euler q-Gamma response

Iterating the shift law `D_σ(w) = ζ(w)·D_σ(w+σ)` produces the finite ladder
`D_σ(w) = (∏_{k<N} ζ(w+kσ))·D_σ(w+Nσ)`.  The far-right Dirichlet series tends to one — every term
beyond `m = 1` is `O(m^{-2}·2^{-(Re w − 2)})` — so the partial products of the ladder converge to
`D_σ(w)`.  This is the second form of (EQG.11): the response is `ζ(σ)^s·C_σ` times the zeta ladder
`∏_{k≥0} ζ(σ(1+s+k))`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The far-right tail of the Dirichlet series -/

/-- The comparison summand `m^{-2}` beyond `m = 1`. -/
def eqgTailBase (m : ℕ) : ℝ := if 2 ≤ m then (m : ℝ) ^ (-(2 : ℝ)) else 0

theorem eqgTailBase_nonneg (m : ℕ) : 0 ≤ eqgTailBase m := by
  rw [eqgTailBase]
  split
  · exact Real.rpow_nonneg (Nat.cast_nonneg m) _
  · exact le_rfl

theorem summable_eqgTailBase : Summable eqgTailBase := by
  have h : Summable fun m : ℕ => (((m : ℝ)) ^ (2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have h' : Summable fun m : ℕ => ((m : ℝ)) ^ (-(2 : ℝ)) := by
    refine h.congr fun m => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg m)]
  refine Summable.of_nonneg_of_le eqgTailBase_nonneg (fun m => ?_) h'
  rw [eqgTailBase]
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (Nat.cast_nonneg m) _

/-- The constant `B = ∑_{m ≥ 2} m^{-2}`. -/
def eqgTailConst : ℝ := ∑' m : ℕ, eqgTailBase m

theorem rpow_le_two_rpow {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc : 0 ≤ c) :
    (m : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-c) := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  rw [Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  refine Real.exp_le_exp.mpr ?_
  have hlog : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hm2
  nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

theorem eqgWeightRe_tail_le (σ : EulerSigma) {x : ℝ} (hx : 2 ≤ x) {m : ℕ} (hm : 2 ≤ m) :
    eqgWeightRe σ x m
      ≤ Real.exp (4 * eqgTail σ) * (2 : ℝ) ^ (-(x - 2)) * eqgTailBase m := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hsplit : (m : ℝ) ^ (-x) = (m : ℝ) ^ (-(2 : ℝ)) * (m : ℝ) ^ (-(x - 2)) := by
    rw [← Real.rpow_add hm0]
    congr 1
    ring
  have hstep : (m : ℝ) ^ (-x) ≤ (m : ℝ) ^ (-(2 : ℝ)) * (2 : ℝ) ^ (-(x - 2)) := by
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left (rpow_le_two_rpow hm (by linarith)) ?_
    exact Real.rpow_nonneg hm0.le _
  have hbase := eqgWeightRe_le σ x m
  have htb : eqgTailBase m = (m : ℝ) ^ (-(2 : ℝ)) := if_pos hm
  rw [htb]
  calc eqgWeightRe σ x m ≤ Real.exp (4 * eqgTail σ) * (m : ℝ) ^ (-x) := hbase
    _ ≤ Real.exp (4 * eqgTail σ) * ((m : ℝ) ^ (-(2 : ℝ)) * (2 : ℝ) ^ (-(x - 2))) :=
        mul_le_mul_of_nonneg_left hstep (Real.exp_pos _).le
    _ = Real.exp (4 * eqgTail σ) * (2 : ℝ) ^ (-(x - 2)) * (m : ℝ) ^ (-(2 : ℝ)) := by ring

/-- **The far-right Dirichlet series is close to one.** -/
theorem norm_eqgDirichlet_sub_one_le (σ : EulerSigma) {v : ℂ} (hv : 2 ≤ v.re) :
    ‖eqgDirichlet σ v - 1‖
      ≤ Real.exp (4 * eqgTail σ) * (2 : ℝ) ^ (-(v.re - 2)) * eqgTailConst := by
  have hv1 : 1 < v.re := by linarith
  have h1 : HasSum (eqgTerm σ v) (eqgDirichlet σ v) := (summable_eqgTerm σ hv1).hasSum
  have h2 : HasSum (fun m : ℕ => if m = 1 then (1 : ℂ) else 0) 1 := hasSum_ite_eq 1 1
  have h3 := h1.sub h2
  set E : ℝ := Real.exp (4 * eqgTail σ) * (2 : ℝ) ^ (-(v.re - 2)) with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    positivity
  have hg : HasSum (fun m : ℕ => E * eqgTailBase m) (E * eqgTailConst) :=
    summable_eqgTailBase.hasSum.mul_left E
  refine h3.norm_le_of_bounded hg fun m => ?_
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [eqgTerm_zero]
      simp only [if_neg (by norm_num : (0 : ℕ) ≠ 1), sub_zero, norm_zero]
      exact mul_nonneg hE0 (eqgTailBase_nonneg _)
    · rw [eqgTerm_one]
      have hz : (1 : ℂ) - (if (1 : ℕ) = 1 then (1 : ℂ) else 0) = 0 := by norm_num
      rw [hz, norm_zero]
      exact mul_nonneg hE0 (eqgTailBase_nonneg _)
  · have hne : m ≠ 1 := by omega
    rw [if_neg hne, sub_zero, norm_eqgTerm]
    exact eqgWeightRe_tail_le σ hv hm

/-! ## The tail tends to one -/

theorem tendsto_eqgDirichlet_shift_one (σ : EulerSigma) (w : ℂ) :
    Tendsto (fun N : ℕ => eqgDirichlet σ (w + (N : ℂ) * (σ.val : ℂ))) atTop (nhds 1) := by
  have hσ0 : 0 < σ.val := σ.pos
  have hre : ∀ N : ℕ, (w + (N : ℂ) * (σ.val : ℂ)).re = w.re + (N : ℝ) * σ.val := by
    intro N
    simp
  set B : ℕ → ℝ := fun N =>
    Real.exp (4 * eqgTail σ) * (2 : ℝ) ^ (-((w.re + (N : ℝ) * σ.val) - 2)) * eqgTailConst with hB
  have hdiv : Tendsto (fun N : ℕ => (w.re + (N : ℝ) * σ.val) - 2) atTop atTop := by
    refine Filter.tendsto_atTop_add_const_right _ (-2) ?_
    refine Filter.tendsto_atTop_add_const_left _ w.re ?_
    exact Filter.Tendsto.atTop_mul_const hσ0 tendsto_natCast_atTop_atTop
  have hBlim : Tendsto B atTop (nhds 0) := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlin : Tendsto (fun N : ℕ => -((w.re + (N : ℝ) * σ.val) - 2) * Real.log 2)
        atTop atBot := by
      have hg : Tendsto (fun N : ℕ => ((w.re + (N : ℝ) * σ.val) - 2) * Real.log 2)
          atTop atTop := Filter.Tendsto.atTop_mul_const hlog hdiv
      have h := Filter.tendsto_neg_atTop_atBot.comp hg
      refine h.congr fun N => ?_
      simp only [Function.comp_apply]
      ring
    have hbase : Tendsto (fun N : ℕ =>
        (2 : ℝ) ^ (-((w.re + (N : ℝ) * σ.val) - 2))) atTop (nhds 0) := by
      have hcomp := Real.tendsto_exp_atBot.comp hlin
      refine hcomp.congr fun N => ?_
      rw [Function.comp_apply, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      ring_nf
    have := (hbase.const_mul (Real.exp (4 * eqgTail σ))).mul_const eqgTailConst
    simpa [hB] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hBlim
  have hev : ∀ᶠ N : ℕ in atTop, 2 ≤ (w + (N : ℂ) * (σ.val : ℂ)).re := by
    filter_upwards [hdiv.eventually_ge_atTop 0] with N hN
    rw [hre N]
    linarith
  filter_upwards [hev] with N hN
  have hbnd := norm_eqgDirichlet_sub_one_le σ hN
  rw [hre N] at hbnd
  exact hbnd

/-! ## The ladder -/

theorem eqgDirichlet_ladder_step (σ : EulerSigma) {w : ℂ} (hw : 1 < w.re) (N : ℕ) :
    eqgDirichlet σ w
      = (∏ k ∈ Finset.range N, riemannZeta (w + (k : ℂ) * (σ.val : ℂ)))
        * eqgDirichlet σ (w + (N : ℂ) * (σ.val : ℂ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hre : 1 < (w + (N : ℂ) * (σ.val : ℂ)).re := by
        have h : (w + (N : ℂ) * (σ.val : ℂ)).re = w.re + (N : ℝ) * σ.val := by simp
        rw [h]
        have hnn : (0 : ℝ) ≤ (N : ℝ) * σ.val := mul_nonneg (Nat.cast_nonneg N) σ.pos.le
        linarith
      have hshift := eqgDirichlet_shift σ hre
      have hstep : w + (N : ℂ) * (σ.val : ℂ) + (σ.val : ℂ)
          = w + ((N + 1 : ℕ) : ℂ) * (σ.val : ℂ) := by
        push_cast
        ring
      rw [hstep] at hshift
      rw [ih, hshift, Finset.prod_range_succ]
      ring

/-- **Equation (EQG.11), ladder form.**  The zeta ladder converges to the arithmetic Dirichlet
series. -/
theorem eqgDirichlet_ladder (σ : EulerSigma) {w : ℂ} (hw : 1 < w.re) :
    Tendsto (fun N : ℕ => ∏ k ∈ Finset.range N, riemannZeta (w + (k : ℂ) * (σ.val : ℂ)))
      atTop (nhds (eqgDirichlet σ w)) := by
  have htail := tendsto_eqgDirichlet_shift_one σ w
  have hne : ∀ᶠ N : ℕ in atTop, eqgDirichlet σ (w + (N : ℂ) * (σ.val : ℂ)) ≠ 0 := by
    have hball : ∀ᶠ N : ℕ in atTop,
        eqgDirichlet σ (w + (N : ℂ) * (σ.val : ℂ)) ∈ Metric.ball (1 : ℂ) 1 :=
      htail (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hball] with N hN h0
    rw [h0] at hN
    simp only [Metric.mem_ball, dist_zero_left] at hN
    exact absurd hN (by norm_num)
  have hinv := htail.inv₀ one_ne_zero
  rw [inv_one] at hinv
  have hlim := hinv.const_mul (eqgDirichlet σ w)
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hne] with N hN
  have hstep := eqgDirichlet_ladder_step σ hw N
  rw [hstep, mul_assoc, mul_inv_cancel₀ hN, mul_one]

/-- **Equation (EQG.11), full ladder form of the response.** -/
theorem eqgResponse_ladder (σ : EulerSigma) {s : ℂ} (hs : 1 < (eqgExponent σ s).re) :
    Tendsto (fun N : ℕ => riemannZeta (σ.val : ℂ) ^ s * (((eqgConst σ : ℝ) : ℂ)
        * ∏ k ∈ Finset.range N, riemannZeta (eqgExponent σ s + (k : ℂ) * (σ.val : ℂ))))
      atTop (nhds (eqgResponse σ s)) := by
  have h := (eqgDirichlet_ladder σ hs).const_mul (((eqgConst σ : ℝ) : ℂ))
  have h2 := h.const_mul (riemannZeta (σ.val : ℂ) ^ s)
  exact h2

end

end GaloisForLFunctions.HTGeometry
