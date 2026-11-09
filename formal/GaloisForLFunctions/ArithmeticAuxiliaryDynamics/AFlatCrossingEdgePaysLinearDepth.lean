import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheSlowReturnBoundLivesRightOfTheLine
import Mathlib.Analysis.Complex.AbsMax

/-!
# A flat crossing edge pays linear depth

Reflection gives a uniform gain on a whole vertical edge. An exponential
barrier carries that gain to the Euler anchor, forcing height growth
with exponent proportional to penetration beyond the critical line.
-/

noncomputable section

open Complex Metric Set

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- A height-two rectangle extending a distance `δ` left of the critical line. -/
def flatCrossingBox (δ T : ℝ) : Set ℂ := Icc (1 / 2 - δ) 4 ×ℂ Icc (T - 1) (T + 1)

/-- The uniform value at the Euler anchor of an exponential rectangle barrier. -/
def flatCrossingWeight : ℝ := Real.exp (-(7 * Real.pi / 4)) * (Real.exp (Real.pi / 2) - 1)

theorem flatCrossingWeight_pos : 0 < flatCrossingWeight := by
  unfold flatCrossingWeight
  have hh : 1 < Real.exp (Real.pi / 2) := Real.one_lt_exp_iff.mpr (by positivity)
  positivity

private def flatBarrier (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * ((a : ℂ) - z)) -
    (Real.exp (Real.pi / 2 * (a - 4)) : ℂ)

private theorem flatBarrier_re (a : ℝ) (z : ℂ) :
    (flatBarrier a z).re = Real.exp (Real.pi / 2 * (a - z.re)) *
      Real.cos (Real.pi / 2 * z.im) - Real.exp (Real.pi / 2 * (a - 4)) := by
  simp [flatBarrier, Complex.exp_re, mul_neg, Real.cos_neg]

private theorem flatBarrier_left_le_one {a : ℝ} {z : ℂ} (hz : z.re = a) :
    (flatBarrier a z).re ≤ 1 := by
  rw [flatBarrier_re, hz, sub_self, mul_zero, Real.exp_zero, one_mul]
  linarith [Real.cos_le_one (Real.pi / 2 * z.im), Real.exp_pos (Real.pi / 2 * (a - 4))]

private theorem flatBarrier_other_edges_nonpos {a : ℝ} {z : ℂ}
    (hz : z.re = 4 ∨ z.im = -1 ∨ z.im = 1) : (flatBarrier a z).re ≤ 0 := by
  rw [flatBarrier_re]
  rcases hz with hz | hz | hz
  · rw [hz]
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one (Real.pi / 2 * z.im))
      (Real.exp_pos (Real.pi / 2 * (a - 4))).le
    linarith
  · rw [hz]
    simp only [mul_neg_one, Real.cos_neg, Real.cos_pi_div_two, mul_zero, zero_sub]
    exact neg_nonpos.mpr (Real.exp_pos _).le
  · rw [hz]
    simp only [mul_one, Real.cos_pi_div_two, mul_zero, zero_sub]
    exact neg_nonpos.mpr (Real.exp_pos _).le

private theorem flatCrossingWeight_le_anchor {a : ℝ} (ha : 1 / 2 ≤ a) :
    flatCrossingWeight ≤ (flatBarrier a 3).re := by
  have hlambda : 0 < Real.pi / 2 := by positivity
  have hfactor : 0 ≤ Real.exp (Real.pi / 2) - 1 := by
    have hh := Real.one_lt_exp_iff.mpr hlambda
    linarith
  have hargument : -(7 * Real.pi / 4) ≤ Real.pi / 2 * (a - 4) := by
    nlinarith only [mul_le_mul_of_nonneg_left ha hlambda.le]
  have hexp := Real.exp_le_exp.mpr hargument
  rw [flatBarrier_re]
  simp only [show (3 : ℂ).re = 3 by norm_num, show (3 : ℂ).im = 0 by norm_num,
    mul_zero, Real.cos_zero, mul_one]
  have heq : Real.pi / 2 * (a - 3) = Real.pi / 2 * (a - 4) + Real.pi / 2 := by ring
  rw [heq, Real.exp_add]
  have hh := mul_le_mul_of_nonneg_right hexp hfactor
  unfold flatCrossingWeight
  nlinarith only [hh]

private theorem flatRectangle_frontier_cases {a : ℝ} {z : ℂ}
    (hz : z ∈ frontier (Icc a 4 ×ℂ Icc (-1 : ℝ) 1)) :
    z ∈ (Icc a 4 ×ℂ Icc (-1 : ℝ) 1) ∧
      (z.re = a ∨ z.re = 4 ∨ z.im = -1 ∨ z.im = 1) := by
  have hclosed : IsClosed (Icc a 4 ×ℂ Icc (-1 : ℝ) 1) := isClosed_Icc.reProdIm isClosed_Icc
  have hzK : z ∈ (Icc a 4 ×ℂ Icc (-1 : ℝ) 1) := by
    have hh := frontier_subset_closure hz
    rwa [hclosed.closure_eq] at hh
  refine ⟨hzK, ?_⟩
  by_contra h
  push Not at h
  have hzU : z ∈ (Ioo a 4 ×ℂ Ioo (-1 : ℝ) 1) := by
    exact ⟨⟨lt_of_le_of_ne hzK.1.1 h.1.symm, lt_of_le_of_ne hzK.1.2 h.2.1⟩,
      ⟨lt_of_le_of_ne hzK.2.1 h.2.2.1.symm, lt_of_le_of_ne hzK.2.2 h.2.2.2⟩⟩
  have hsub : (Ioo a 4 ×ℂ Ioo (-1 : ℝ) 1) ⊆ (Icc a 4 ×ℂ Icc (-1 : ℝ) 1) :=
    fun _ hw => ⟨⟨hw.1.1.le, hw.1.2.le⟩, ⟨hw.2.1.le, hw.2.2.le⟩⟩
  have hin := interior_maximal hsub (isOpen_Ioo.reProdIm isOpen_Ioo) hzU
  exact hz.2 hin

/-- An exponential multiplier transfers a full left-edge gain to the Euler anchor. -/
private theorem norm_anchor_mul_exp_le_of_flat_edge {a B M : ℝ} {f : ℂ → ℂ}
    (ha : 1 / 2 ≤ a) (ha₃ : a ≤ 3) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hd : ∀ z ∈ (Icc a 4 ×ℂ Icc (-1 : ℝ) 1), DifferentiableAt ℂ f z)
    (houter : ∀ z ∈ (Icc a 4 ×ℂ Icc (-1 : ℝ) 1), ‖f z‖ ≤ M)
    (hleft : ∀ z ∈ (Icc a 4 ×ℂ Icc (-1 : ℝ) 1), z.re = a → ‖f z‖ ≤ M * Real.exp (-B)) :
    ‖f 3‖ * Real.exp (B * flatCrossingWeight) ≤ M := by
  let g : ℂ → ℂ := fun z => f z * Complex.exp ((B : ℂ) * flatBarrier a z)
  have hnorm : ∀ z, ‖g z‖ = ‖f z‖ * Real.exp (B * (flatBarrier a z).re) := by
    intro z
    simp only [g, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hg : ∀ z ∈ (Icc a 4 ×ℂ Icc (-1 : ℝ) 1), DifferentiableAt ℂ g z := by
    intro z hz
    apply (hd z hz).mul
    dsimp [flatBarrier]
    fun_prop
  have hcompact : IsCompact (Icc a 4 ×ℂ Icc (-1 : ℝ) 1) := isCompact_Icc.reProdIm isCompact_Icc
  have hdc : DiffContOnCl ℂ g (Icc a 4 ×ℂ Icc (-1 : ℝ) 1) := by
    refine ⟨fun z hz => (hg z hz).differentiableWithinAt, ?_⟩
    rw [hcompact.isClosed.closure_eq]
    exact fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hboundary : ∀ z ∈ frontier (Icc a 4 ×ℂ Icc (-1 : ℝ) 1), ‖g z‖ ≤ M := by
    intro z hz
    obtain ⟨hzK, hzedge⟩ := flatRectangle_frontier_cases hz
    rw [hnorm]
    rcases hzedge with hzleft | hzrest
    · have hre := flatBarrier_left_le_one hzleft
      have hexp : Real.exp (B * (flatBarrier a z).re) ≤ Real.exp B := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left hre hB]
      calc ‖f z‖ * Real.exp (B * (flatBarrier a z).re) ≤
          (M * Real.exp (-B)) * Real.exp B :=
            mul_le_mul (hleft z hzK hzleft) hexp (Real.exp_pos _).le (by positivity)
        _ = M := by rw [mul_assoc, ← Real.exp_add]; simp
    · have hre := flatBarrier_other_edges_nonpos (a := a) hzrest
      have hexp : Real.exp (B * (flatBarrier a z).re) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos hB hre)
      calc ‖f z‖ * Real.exp (B * (flatBarrier a z).re) ≤ M * 1 :=
          mul_le_mul (houter z hzK) hexp (Real.exp_pos _).le hM
        _ = M := mul_one _
  have hthree : (3 : ℂ) ∈ closure (Icc a 4 ×ℂ Icc (-1 : ℝ) 1) := by
    apply subset_closure
    constructor <;> norm_num
    exact ha₃
  have hmain := Complex.norm_le_of_forall_mem_frontier_norm_le hcompact.isBounded hdc hboundary hthree
  rw [hnorm] at hmain
  have hα := flatCrossingWeight_le_anchor ha
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hα hB)
  exact (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans hmain

private theorem flat_shift_ne_one {T : ℝ} (hT : 4 ≤ T) {z : ℂ} (hz : -1 ≤ z.im) :
    z + (T : ℂ) * I ≠ 1 := by
  intro hh
  have hi := congrArg Complex.im hh
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, Complex.one_im] at hi
  linarith

/-- A flat reflected edge forces logarithmic growth linear in crossing depth. -/
theorem exists_flat_crossing_logarithmic_cost :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ δ T : ℝ, 0 < δ → δ ≤ 1 / 8 → 4 ≤ T → ∀ M : ℝ,
      (∀ z ∈ flatCrossingBox δ T, ‖riemannZeta z‖ ≤ M) →
      flatCrossingWeight / 2 * δ * Real.log T ≤ Real.log M + K := by
  obtain ⟨C, hC, hreflect⟩ := exists_norm_zeta_le_reflect
  have hCpos : 0 < C := by linarith
  have hα := flatCrossingWeight_pos
  refine ⟨Real.log 2 + flatCrossingWeight * Real.log C,
    add_nonneg (Real.log_nonneg (by norm_num)) (mul_nonneg hα.le (Real.log_nonneg hC)),
    fun δ T hδ hδ₁ hT M hM => ?_⟩
  have hTpos : 0 < T := by linarith
  have hXpos : 0 < T / 2 := by linarith
  let f : ℂ → ℂ := fun z => riemannZeta (z + (T : ℂ) * I)
  have hd : ∀ z ∈ (Icc (1 / 2 + δ) 4 ×ℂ Icc (-1 : ℝ) 1), DifferentiableAt ℂ f z := by
    intro z hz
    exact (differentiableAt_riemannZeta (flat_shift_ne_one hT hz.2.1)).comp z
      (differentiableAt_id.add_const _)
  have houter : ∀ z ∈ (Icc (1 / 2 + δ) 4 ×ℂ Icc (-1 : ℝ) 1), ‖f z‖ ≤ M := by
    intro z hz
    refine hM _ ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;>
      linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hthree : (3 : ℂ) ∈ (Icc (1 / 2 + δ) 4 ×ℂ Icc (-1 : ℝ) 1) := by
    constructor <;> norm_num
    linarith
  have hanchor : (1 / 2 : ℝ) ≤ ‖f 3‖ := half_le_norm_zeta (by norm_num)
  have hMhalf : (1 / 2 : ℝ) ≤ M := hanchor.trans (houter _ hthree)
  have hMpos : 0 < M := by linarith
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = δ * Real.log (T / 2) - Real.log C := ⟨_, rfl⟩
  have hleft : ∀ z ∈ (Icc (1 / 2 + δ) 4 ×ℂ Icc (-1 : ℝ) 1), z.re = 1 / 2 + δ →
      ‖f z‖ ≤ M * Real.exp (-B) := by
    intro z hz hzleft
    have ht : T / 2 ≤ z.im + T := by linarith [hz.2.1]
    have ht₁ : 1 ≤ z.im + T := by linarith
    have href := hreflect (1 / 2 + δ) (z.im + T) (by linarith) (by linarith) ht₁
    have hrefmem : (((1 - (1 / 2 + δ) : ℝ) : ℂ) + ((z.im + T : ℝ) : ℂ) * I) ∈
        flatCrossingBox δ T := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith [hz.2.1, hz.2.2]
    have hpow : (z.im + T) ^ (1 / 2 - (1 / 2 + δ)) ≤ (T / 2) ^ (-δ) := by
      rw [show (1 / 2 : ℝ) - (1 / 2 + δ) = -δ by ring,
        Real.rpow_neg (by linarith : 0 ≤ z.im + T), Real.rpow_neg hXpos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hXpos _)
        (Real.rpow_le_rpow hXpos.le ht hδ.le)
    have hnorm := href.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow hCpos.le)
      (hM _ hrefmem) (norm_nonneg _) (by positivity))
    have heq : z + (T : ℂ) * I = ((1 / 2 + δ : ℝ) : ℂ) + ((z.im + T : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hzleft]
    have hexp : C * (T / 2) ^ (-δ) = Real.exp (-B) := by
      rw [Real.rpow_def_of_pos hXpos,
        show -B = Real.log C + Real.log (T / 2) * (-δ) by rw [hBdef]; ring,
        Real.exp_add, Real.exp_log hCpos]
    rw [hexp] at hnorm
    change ‖riemannZeta (z + (T : ℂ) * I)‖ ≤ _
    rw [heq]
    nlinarith only [hnorm]
  have hpay : flatCrossingWeight * δ * Real.log (T / 2) ≤
      Real.log M + (Real.log 2 + flatCrossingWeight * Real.log C) := by
    by_cases hB : 0 ≤ B
    · have hh := norm_anchor_mul_exp_le_of_flat_edge (by linarith) (by linarith)
        hB hMpos.le hd houter hleft
      have hhalf : (1 / 2 : ℝ) * Real.exp (B * flatCrossingWeight) ≤ M :=
        (mul_le_mul_of_nonneg_right hanchor (Real.exp_pos _).le).trans hh
      have hl := Real.log_le_log (by positivity : 0 < (1 / 2 : ℝ) * Real.exp (B * flatCrossingWeight)) hhalf
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
        one_div, Real.log_inv, hBdef] at hl
      nlinarith only [hl]
    · have hBneg : B < 0 := lt_of_not_ge hB
      have hb := mul_nonpos_of_nonneg_of_nonpos hα.le hBneg.le
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hMhalf
      rw [one_div, Real.log_inv] at hl
      rw [hBdef] at hb
      nlinarith only [hb, hl]
  have hlogX : Real.log T / 2 ≤ Real.log (T / 2) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hT
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hfour] at hh
    rw [Real.log_div hTpos.ne' (by norm_num)]
    linarith
  have hh := mul_le_mul_of_nonneg_left hlogX (mul_nonneg hα.le hδ.le)
  nlinarith only [hh, hpay]

/-- Every uniform rectangle bound dominates a fixed positive multiple of `T^(bδ)`. -/
theorem exists_flat_crossing_rpow_cost :
    ∃ c : ℝ, 0 < c ∧ ∀ δ T : ℝ, 0 < δ → δ ≤ 1 / 8 → 4 ≤ T → ∀ M : ℝ,
      (∀ z ∈ flatCrossingBox δ T, ‖riemannZeta z‖ ≤ M) →
      c * T ^ (flatCrossingWeight / 2 * δ) ≤ M := by
  obtain ⟨K, _, hK⟩ := exists_flat_crossing_logarithmic_cost
  refine ⟨Real.exp (-K), Real.exp_pos _, fun δ T hδ hδ₁ hT M hM => ?_⟩
  have hTpos : 0 < T := by linarith
  have hcentre : (3 : ℂ) + (T : ℂ) * I ∈ flatCrossingBox δ T := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  have hMpos : 0 < M := by
    have hh := (half_le_norm_zeta (s := (3 : ℂ) + (T : ℂ) * I) (by norm_num)).trans
      (hM _ hcentre)
    linarith
  have hlog := hK δ T hδ hδ₁ hT M hM
  have hh := Real.exp_le_exp.mpr
    (show -K + Real.log T * (flatCrossingWeight / 2 * δ) ≤ Real.log M by nlinarith only [hlog])
  rwa [Real.exp_add, Real.exp_log hMpos, ← Real.rpow_def_of_pos hTpos] at hh

/-- A rectangle with a flat crossing edge contains an actual zeta value of size `cT^(bδ)`. -/
theorem exists_large_zeta_value_on_flat_crossing_box :
    ∃ c : ℝ, 0 < c ∧ ∀ δ T : ℝ, 0 < δ → δ ≤ 1 / 8 → 4 ≤ T →
      ∃ z ∈ flatCrossingBox δ T, c * T ^ (flatCrossingWeight / 2 * δ) ≤ ‖riemannZeta z‖ := by
  obtain ⟨c, hc, hcost⟩ := exists_flat_crossing_rpow_cost
  refine ⟨c, hc, fun δ T hδ hδ₁ hT => ?_⟩
  have hcompact : IsCompact (flatCrossingBox δ T) := isCompact_Icc.reProdIm isCompact_Icc
  have hcentre : (3 : ℂ) + (T : ℂ) * I ∈ flatCrossingBox δ T := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  have hcont : ContinuousOn (fun z : ℂ => ‖riemannZeta z‖) (flatCrossingBox δ T) := by
    intro z hz
    have hne : z ≠ 1 := by
      intro hh
      have hi := congrArg Complex.im hh
      norm_num at hi
      linarith [hz.2.1]
    exact (differentiableAt_riemannZeta hne).continuousAt.norm.continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn ⟨_, hcentre⟩ hcont
  exact ⟨z, hz, hcost δ T hδ hδ₁ hT _ (fun w hw => hmax hw)⟩

/-- Slow bounds on a flat crossing rectangle force a linear penetration budget at aligned returns. -/
theorem exists_aligned_flat_crossing_linear_budget :
    ∃ K H : ℝ, 0 ≤ K ∧ 4 ≤ H ∧ ∀ τ : ℝ, H ≤ τ → ∀ N : ℕ, 1 ≤ N →
      IsHeadReturn N τ → ∀ A δ γ : ℝ, 0 ≤ A → 0 < δ → δ ≤ 1 / 8 → 0 ≤ γ →
      (∀ z ∈ flatCrossingBox δ γ, ‖riemannZeta (z + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A) →
      flatCrossingWeight * δ * Real.log (γ + τ) ≤
        2 * (A * (Real.log 1024 + 6 * Real.log (Real.log τ)) + K) := by
  obtain ⟨K, hK, hcost⟩ := exists_flat_crossing_logarithmic_cost
  obtain ⟨H, _, hlength⟩ := length_le_pow_log_of_isHeadReturn
  refine ⟨K, max 4 H, hK, le_max_left _ _, fun τ hτ N hN hhead A δ γ hA hδ hδ₁ hγ hM => ?_⟩
  have hτ₄ : 4 ≤ τ := (le_max_left _ _).trans hτ
  have hτH : H ≤ τ := (le_max_right _ _).trans hτ
  obtain ⟨hlog, hlen⟩ := hlength τ hτH N hhead
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlogpos : 0 < Real.log τ := by linarith
  have hlogN := Real.log_le_log hNpos hlen
  rw [Real.log_mul (by norm_num) (pow_pos hlogpos _).ne', Real.log_pow] at hlogN
  have hMactual : ∀ z ∈ flatCrossingBox δ (γ + τ), ‖riemannZeta z‖ ≤ (N : ℝ) ^ A := by
    intro z hz
    have hmem : z - (τ : ℂ) * I ∈ flatCrossingBox δ γ := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;>
        linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    simpa only [sub_add_cancel] using hM _ hmem
  have hbound := hcost δ (γ + τ) hδ hδ₁ (by linarith) _ hMactual
  rw [Real.log_rpow hNpos] at hbound
  have hh := mul_le_mul_of_nonneg_left hlogN hA
  norm_num at hh
  nlinarith only [hbound, hh]

#print axioms exists_flat_crossing_logarithmic_cost
#print axioms exists_large_zeta_value_on_flat_crossing_box
#print axioms exists_aligned_flat_crossing_linear_budget

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
