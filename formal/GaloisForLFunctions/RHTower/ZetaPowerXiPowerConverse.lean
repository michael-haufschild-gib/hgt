import GaloisForLFunctions.RHTower.DegreeThreeOddFiniteDeficit

/-!
# Degree-`k` data containing `k − 2` copies of the `ξ` divisor are multiples of `ζᵏ`

Let `ZetaPowerDatum (j + 3) g E` with `E(1) ≠ 0`.  If `ξʲ` divides `E` (order by order), the
quotient `H = E/ξʲ` is a cubic datum for the coefficients `2ʲ · (g ⋆ μ ⋆ ⋯ ⋆ μ)` (`j` Möbius
factors) (`zetaPowerDatum_three_of_xi_pow_dvd`).  Hence:

* if `ξ^{j+1}` divides `E`, then the sign is `+1` and `L(g) = g(1) ζ^{j+3}`
  (`zetaPower_eq_of_xi_pow_le`);
* if `ξʲ` divides `E`, then either `L(g) = g(1) ζ^{j+3}`, or `E` vanishes to order less than
  `(j + 1) · ord ξ` at infinitely many points (`zetaPower_eq_or_infiniteDeficits`).

For `k = j + 3` this says that a degree-`k` conductor-one datum containing `k − 2` copies of the
zeta divisor, up to finitely many points, is `g(1) ζᵏ`.  The `k = 2` case is the `ζ²` converse
theorem.
-/

noncomputable section

open Set Complex Filter Topology

namespace RHTower.WeilHigherDenominator

open MaassZetaSquaredConverse

/-! ## Iterated division by `ζ` -/

/-- The coefficients of `L(g)/ζʲ`. -/
def zetaQuotientIter (j : ℕ) (g : ℕ → ℂ) : ℕ → ℂ := degreeTwoQuotientCoeff^[j] g

theorem zetaQuotientIter_one (j : ℕ) (g : ℕ → ℂ) : zetaQuotientIter j g 1 = g 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [zetaQuotientIter, Function.iterate_succ_apply', degreeTwoQuotientCoeff_one]
    exact ih

theorem zetaQuotientIter_summable (j : ℕ) {g : ℕ → ℂ} {s : ℂ} (hg : LSeriesSummable g s)
    (hs : 1 < s.re) : LSeriesSummable (zetaQuotientIter j g) s := by
  induction j with
  | zero => exact hg
  | succ j ih =>
    rw [zetaQuotientIter, Function.iterate_succ_apply']
    exact degreeTwoQuotientCoeff_summable ih hs

theorem LSeries_zetaQuotientIter (j : ℕ) {g : ℕ → ℂ} {s : ℂ} (hg : LSeriesSummable g s)
    (hs : 1 < s.re) :
    LSeries (zetaQuotientIter j g) s = LSeries g s / riemannZeta s ^ j := by
  induction j with
  | zero => simp [zetaQuotientIter]
  | succ j ih =>
    have hsum := zetaQuotientIter_summable j hg hs
    rw [show zetaQuotientIter (j + 1) g = degreeTwoQuotientCoeff (zetaQuotientIter j g) from
      Function.iterate_succ_apply' _ _ _, LSeries_degreeTwoQuotientCoeff hsum hs, ih, pow_succ,
      div_div]

/-! ## Growth bookkeeping -/

private theorem finiteOrderEnvelope_of_logBound {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    GaloisForLFunctions.HTGeometry.FiniteOrderEnvelope f := by
  refine ⟨C, 2, hC, fun z => (hf z).trans (Real.exp_le_exp.mpr ?_)⟩
  have hl : Real.log (2 + ‖z‖) ≤ 1 + ‖z‖ := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + ‖z‖)
    linarith
  calc C * (1 + ‖z‖) * Real.log (2 + ‖z‖) ≤ C * (1 + ‖z‖) * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
    _ = C * (1 + ‖z‖) ^ 2 := by ring

private theorem finiteOrderEnvelope_xi_pow (j : ℕ) :
    GaloisForLFunctions.HTGeometry.FiniteOrderEnvelope (fun z => xi z ^ j) := by
  induction j with
  | zero => exact ⟨0, 0, le_rfl, fun z => by simp⟩
  | succ j ih =>
    obtain ⟨C, hC, hb⟩ := orderOneEnvelope_xi
    have hxi := finiteOrderEnvelope_of_logBound hC.le hb
    simpa only [pow_succ] using ih.mul hxi

private theorem exists_finiteOrder_bound {f : ℂ → ℂ}
    (hf : GaloisForLFunctions.HTGeometry.FiniteOrderEnvelope f) :
    ∃ ρ C₀ : ℝ, ∀ z, ‖f z‖ ≤ C₀ * Real.exp (‖z‖ ^ ρ) := by
  obtain ⟨C, d, hC, hb⟩ := hf
  let A : ℝ := max 1 (C * 2 ^ d)
  let B : ℝ := C * (1 + A) ^ d
  have hA : 1 ≤ A := le_max_left _ _
  have hCA : C * 2 ^ d ≤ A := le_max_right _ _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(d + 1 : ℕ), Real.exp B, fun z => ?_⟩
  have he : C * (1 + ‖z‖) ^ d ≤ B + ‖z‖ ^ (d + 1) := by
    rcases le_or_gt ‖z‖ A with hz | hz
    · have ht : C * (1 + ‖z‖) ^ d ≤ B := by dsimp [B]; gcongr
      exact ht.trans (le_add_of_nonneg_right (by positivity))
    · have h1 : 1 ≤ ‖z‖ := hA.trans hz.le
      calc C * (1 + ‖z‖) ^ d ≤ C * (2 * ‖z‖) ^ d := by gcongr; linarith
        _ = (C * 2 ^ d) * ‖z‖ ^ d := by rw [mul_pow]; ring
        _ ≤ ‖z‖ * ‖z‖ ^ d := mul_le_mul_of_nonneg_right (hCA.trans hz.le) (by positivity)
        _ = ‖z‖ ^ (d + 1) := by ring
        _ ≤ B + ‖z‖ ^ (d + 1) := le_add_of_nonneg_left hB
  calc ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d) := hb z
    _ ≤ Real.exp (B + ‖z‖ ^ (d + 1)) := Real.exp_le_exp.mpr he
    _ = Real.exp B * Real.exp (‖z‖ ^ ((d + 1 : ℕ) : ℝ)) := by
      rw [Real.exp_add, Real.rpow_natCast]

private theorem xi_one_ne_zero' : xi 1 ≠ 0 := by rw [xi_one]; norm_num

private theorem analyticOrderAt_ne_top_of_one {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf1 : f 1 ≠ 0) (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro ht
  have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
    (fun w => hf.differentiableOn.analyticAt Filter.univ_mem)).mp ht
  exact hf1 (congrFun hz 1)

/-- An entire function vanishing on `Re s > 2` vanishes identically. -/
private theorem eq_zero_of_zero_right {K : ℂ → ℂ} (hK : Differentiable ℂ K)
    (h : ∀ s : ℂ, 2 < s.re → K s = 0) (s : ℂ) : K s = 0 := by
  have hA : AnalyticOnNhd ℂ K univ := fun z _ => hK.analyticAt z
  have hev : K =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    exact h z hz
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ _) hev
    (mem_univ s)

/-! ## The cubic quotient -/

/-- **Dividing out `ξʲ` leaves a cubic datum.** -/
theorem zetaPowerDatum_three_of_xi_pow_dvd {j : ℕ} {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum (j + 3) g E) (hE1 : E 1 ≠ 0)
    (hdiv : ∀ s, j * analyticOrderNatAt xi s ≤ analyticOrderNatAt E s) :
    ∃ H : ℂ → ℂ, (∀ z, E z = H z * xi z ^ j) ∧ H 1 ≠ 0 ∧
      WeilZetaPower.ZetaPowerDatum 3 ((2 : ℂ) ^ j • zetaQuotientIter j g) H := by
  have hxiA : ∀ z, AnalyticAt ℂ xi z := fun z => xi_differentiable.analyticAt z
  have hEA : ∀ z, AnalyticAt ℂ E z := fun z => hD.entire.analyticAt z
  have hxitop := analyticOrderAt_ne_top_of_one xi_differentiable xi_one_ne_zero'
  have hEtop := analyticOrderAt_ne_top_of_one hD.entire hE1
  have hord : ∀ z, analyticOrderAt (fun w => xi w ^ j) z ≤ analyticOrderAt E z := by
    intro z
    change analyticOrderAt (xi ^ j) z ≤ analyticOrderAt E z
    rw [analyticOrderAt_pow (hxiA z) j, ← Nat.cast_analyticOrderNatAt (hxitop z),
      ← Nat.cast_analyticOrderNatAt (hEtop z), nsmul_eq_mul]
    exact_mod_cast hdiv z
  obtain ⟨H, hH, hfac₀⟩ := GaloisForLFunctions.HTGeometry.exists_entire_quotient hD.entire
    (xi_differentiable.pow j) ⟨1, pow_ne_zero j xi_one_ne_zero'⟩ hord
  have hfac : ∀ z, E z = H z * xi z ^ j := fun z => by simpa using hfac₀ z
  have hH1 : H 1 ≠ 0 := by
    intro h
    exact hE1 (by rw [hfac 1, h, zero_mul])
  -- growth
  obtain ⟨CE, hCE, hbE⟩ := hD.orderOne
  have hHfin := finiteOrderEnvelope_entire_quotient
    (fun z _ => (xi_differentiable.pow j).analyticAt z) (fun z _ => hEA z)
    (fun z _ => hH.analyticAt z) ⟨1, pow_ne_zero j xi_one_ne_zero'⟩ ⟨1, hE1⟩ hfac
    (finiteOrderEnvelope_xi_pow j) (finiteOrderEnvelope_of_logBound hCE hbE)
  refine ⟨H, hfac, hH1, ?_⟩
  refine ⟨fun s hs => ((zetaQuotientIter_summable j (hD.summable s hs) hs).smul _), hH,
    fun s hs => ?_, ?_, exists_finiteOrder_bound hHfin⟩
  · -- the completion identity
    have hspos : 0 < s.re := by linarith
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
    have hΓ := Complex.Gammaℝ_ne_zero_of_re_pos hspos
    have hζ := riemannZeta_ne_zero_of_one_lt_re hs
    set A := s * (s - 1) * Complex.Gammaℝ s with hAdef
    have hA : A ≠ 0 := mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hΓ
    have hxi : xi s = A * riemannZeta s / 2 := by
      have := two_xi_eq hspos hs1
      rw [← hAdef] at this
      linear_combination this / 2
    have hxi0 : xi s ≠ 0 := by rw [hxi]; exact div_ne_zero (mul_ne_zero hA hζ) two_ne_zero
    rw [LSeries_smul, LSeries_zetaQuotientIter j (hD.summable s hs) hs]
    apply mul_right_cancel₀ (pow_ne_zero j hxi0)
    rw [← hfac s, hD.completion s hs, ← hAdef, hxi]
    clear_value A
    rw [div_pow, mul_pow]
    have h2 : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j two_ne_zero
    have hz : riemannZeta s ^ j ≠ 0 := pow_ne_zero j hζ
    field_simp
    ring
  · -- the functional equation
    obtain ⟨ε, _, hsym⟩ := hD.exists_sign
    have hHsym : ∀ s, H (1 - s) = ε * H s := by
      intro s
      have hK : Differentiable ℂ fun z => H (1 - z) - ε * H z :=
        (hH.comp ((differentiable_const 1).sub differentiable_id)).sub (hH.const_mul ε)
      have h := eq_zero_of_zero_right hK (fun z hz => by
        have hxi : xi z ≠ 0 := xi_ne_zero_right hz.le
        have he : H (1 - z) * xi z ^ j = ε * H z * xi z ^ j := by
          calc H (1 - z) * xi z ^ j = H (1 - z) * xi (1 - z) ^ j := by rw [xi_one_sub]
            _ = E (1 - z) := (hfac (1 - z)).symm
            _ = ε * E z := hsym z
            _ = ε * H z * xi z ^ j := by rw [hfac z]; ring
        have := mul_right_cancel₀ (pow_ne_zero j hxi) he
        simp [this]) s
      exact sub_eq_zero.mp h
    rcases hD.functional_equation with heven | hodd
    · left
      intro s
      have hε : ε = 1 := by
        apply mul_right_cancel₀ hE1
        rw [one_mul, ← hsym 1, heven 1]
      simpa [hε] using hHsym s
    · right
      intro s
      have hε : ε = -1 := by
        apply mul_right_cancel₀ hE1
        rw [← hsym 1, hodd 1]
        ring
      simpa [hε] using hHsym s

/-- Orders add along the quotient. -/
private theorem order_quotient {j : ℕ} {E H : ℂ → ℂ} (hE : Differentiable ℂ E) (hE1 : E 1 ≠ 0)
    (hH : Differentiable ℂ H) (hH1 : H 1 ≠ 0) (hfac : ∀ z, E z = H z * xi z ^ j) (z : ℂ) :
    analyticOrderNatAt E z = analyticOrderNatAt H z + j * analyticOrderNatAt xi z := by
  have hxitop := analyticOrderAt_ne_top_of_one xi_differentiable xi_one_ne_zero' z
  have hEtop := analyticOrderAt_ne_top_of_one hE hE1 z
  have hHtop := analyticOrderAt_ne_top_of_one hH hH1 z
  have hfun : E = H * xi ^ j := funext fun w => by simp [hfac w]
  have h := analyticOrderAt_mul (hH.analyticAt z) ((xi_differentiable.pow j).analyticAt z)
  have h' : analyticOrderAt E z = analyticOrderAt H z + j • analyticOrderAt xi z := by
    rw [hfun, h, analyticOrderAt_pow (xi_differentiable.analyticAt z) j]
  rw [← Nat.cast_analyticOrderNatAt hEtop, ← Nat.cast_analyticOrderNatAt hHtop,
    ← Nat.cast_analyticOrderNatAt hxitop, nsmul_eq_mul] at h'
  exact_mod_cast h'

/-! ## The degree-`k` rungs -/

/-- **`k − 2` copies of the `ξ` divisor force `ζᵏ`** (`k = j + 3`). -/
theorem zetaPower_eq_of_xi_pow_le {j : ℕ} {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum (j + 3) g E) (hE1 : E 1 ≠ 0)
    (hdiv : ∀ s, (j + 1) * analyticOrderNatAt xi s ≤ analyticOrderNatAt E s) :
    (∀ s, E (1 - s) = E s) ∧
      ∀ s : ℂ, 1 < s.re → LSeries g s = g 1 * riemannZeta s ^ (j + 3) := by
  obtain ⟨H, hfac, hH1, hH⟩ := zetaPowerDatum_three_of_xi_pow_dvd hD hE1
    (fun s => le_trans (Nat.mul_le_mul_right _ (Nat.le_succ j)) (hdiv s))
  have hordH : ∀ s, analyticOrderNatAt xi s ≤ analyticOrderNatAt H s := fun s => by
    have h := order_quotient hD.entire hE1 hH.entire hH1 hfac s
    have := hdiv s
    nlinarith
  obtain ⟨heven, hL⟩ := degreeThree_eq_zetaCube_of_xi_le hH hH1 hordH
  refine ⟨fun s => by rw [hfac, hfac, heven, xi_one_sub], fun s hs => ?_⟩
  have h := hL s hs
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  rw [LSeries_smul, LSeries_zetaQuotientIter j (hD.summable s hs) hs] at h
  simp only [Pi.smul_apply, smul_eq_mul, zetaQuotientIter_one] at h
  have h2 : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j two_ne_zero
  rw [mul_assoc, mul_right_inj' h2, div_eq_iff (pow_ne_zero j hζ)] at h
  rw [h]
  ring

/-- **Degree `k = j + 3`: `ζᵏ`, or infinitely many points below `k − 2` copies of `ξ`.** -/
theorem zetaPower_eq_or_infiniteDeficits {j : ℕ} {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum (j + 3) g E) (hE1 : E 1 ≠ 0)
    (hdiv : ∀ s, j * analyticOrderNatAt xi s ≤ analyticOrderNatAt E s) :
    (∀ s : ℂ, 1 < s.re → LSeries g s = g 1 * riemannZeta s ^ (j + 3)) ∨
      {z | analyticOrderNatAt E z < (j + 1) * analyticOrderNatAt xi z}.Infinite := by
  obtain ⟨H, hfac, hH1, hH⟩ := zetaPowerDatum_three_of_xi_pow_dvd hD hE1 hdiv
  rcases degreeThree_eq_zetaCube_or_infiniteDeficits hH hH1 with hL | hinf
  · left
    intro s hs
    have h := hL s hs
    have hζ := riemannZeta_ne_zero_of_one_lt_re hs
    rw [LSeries_smul, LSeries_zetaQuotientIter j (hD.summable s hs) hs] at h
    simp only [Pi.smul_apply, smul_eq_mul, zetaQuotientIter_one] at h
    have h2 : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j two_ne_zero
    rw [mul_assoc, mul_right_inj' h2, div_eq_iff (pow_ne_zero j hζ)] at h
    rw [h]
    ring
  · right
    refine hinf.mono fun z hz => ?_
    simp only [xiDeficitSupport, mem_setOf_eq] at hz ⊢
    have h := order_quotient hD.entire hE1 hH.entire hH1 hfac z
    rw [h]
    nlinarith

end RHTower.WeilHigherDenominator
