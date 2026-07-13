import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowContinuation

open Complex Filter Function Set

noncomputable section

namespace RHTower

/-- Pole-cancelled sharp source.  Multiplication by the shifted pole-filled zeta has already been
performed algebraically, so the logarithmic derivative is replaced by an ordinary derivative. -/
def dyadicSharpPrimeCancelledSource (s : ℂ) : ℂ :=
  regularizedRiemannZeta (s - 1 / 2) *
      dslope dyadicSharpPrimePoleNumerator (3 / 2) s +
    2 * sharpPrimeWindowMellin (Real.log 2) s *
      deriv regularizedRiemannZeta (s - 1 / 2) -
    2 * regularizedRiemannZeta (s - 1 / 2) *
      dyadicSharpPrimeWindowErrorSeries s

/-- The cancelled sharp source is holomorphic on the full quadrature half-plane. -/
theorem differentiableOn_dyadicSharpPrimeCancelledSource_rightHalf :
    DifferentiableOn ℂ dyadicSharpPrimeCancelledSource
      {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  have hRbase : AnalyticAt ℂ regularizedRiemannZeta (s - 1 / 2) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) _ (Set.mem_univ _)
  have hR : AnalyticAt ℂ
      (fun z : ℂ => regularizedRiemannZeta (z - 1 / 2)) s :=
    AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s) hRbase hshift
  have hRd : AnalyticAt ℂ
      (fun z : ℂ => deriv regularizedRiemannZeta (z - 1 / 2)) s :=
    AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s) hRbase.deriv hshift
  have hD : AnalyticAt ℂ
      (dslope dyadicSharpPrimePoleNumerator (3 / 2)) s :=
    (differentiable_dyadicSharpPrimePoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ (sharpPrimeWindowMellin (Real.log 2)) s :=
    (differentiable_sharpPrimeWindowMellin_logTwo.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hE : AnalyticAt ℂ dyadicSharpPrimeWindowErrorSeries s :=
    (differentiableOn_dyadicSharpPrimeWindowErrorSeries_rightHalf.analyticOnNhd
      hUopen) s hs
  exact ((hR.mul hD).add
    (((analyticAt_const.mul hM).mul hRd))).sub
      ((analyticAt_const.mul hR).mul hE) |>.differentiableWithinAt

/-- Away from a shifted zeta zero, cancellation is literal multiplication of the meromorphic
continued source by the pole-filled zeta. -/
theorem dyadicSharpPrimeCancelledSource_eq_mul_continuedSource
    {s : ℂ} (hR : regularizedRiemannZeta (s - 1 / 2) ≠ 0) :
    dyadicSharpPrimeCancelledSource s =
      regularizedRiemannZeta (s - 1 / 2) *
        dyadicSharpPrimeContinuedSource s := by
  rw [dyadicSharpPrimeCancelledSource, dyadicSharpPrimeContinuedSource,
    dyadicSharpPrimePoleFilledMain, logDeriv_apply]
  have hc : regularizedRiemannZeta (s - 1 / 2) *
      (regularizedRiemannZeta (s - 1 / 2))⁻¹ = 1 :=
    mul_inv_cancel₀ hR
  rw [mul_sub, mul_add]
  rw [show regularizedRiemannZeta (s - 1 / 2) *
      (2 * sharpPrimeWindowMellin (Real.log 2) s *
        (deriv regularizedRiemannZeta (s - 1 / 2) /
          regularizedRiemannZeta (s - 1 / 2))) =
      2 * sharpPrimeWindowMellin (Real.log 2) s *
        deriv regularizedRiemannZeta (s - 1 / 2) by
    rw [div_eq_mul_inv]
    calc
      regularizedRiemannZeta (s - 1 / 2) *
          (2 * sharpPrimeWindowMellin (Real.log 2) s *
            (deriv regularizedRiemannZeta (s - 1 / 2) *
              (regularizedRiemannZeta (s - 1 / 2))⁻¹)) =
        (regularizedRiemannZeta (s - 1 / 2) *
          (regularizedRiemannZeta (s - 1 / 2))⁻¹) *
          (2 * sharpPrimeWindowMellin (Real.log 2) s *
            deriv regularizedRiemannZeta (s - 1 / 2)) := by ring
      _ = _ := by rw [hc, one_mul]; norm_num]
  ring

theorem regularizedRiemannZeta_shift_eq_zero_at_xiRightPole
    (q : XiRightZeroCopy) :
    regularizedRiemannZeta (xiRightShiftedPole q - 1 / 2) = 0 := by
  rw [xiRightShiftedPole_sub_half]
  let ρ : ℂ := (q.1.1 : ℂ)
  have hcenterRe := congrArg Complex.re
    (xiRightCenteredZero_eq_support_sub_half q)
  simp only [Complex.sub_re] at hcenterRe
  norm_num at hcenterRe
  have hcenterBounds := abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)
  have hρpos : 0 < ρ.re := by
    dsimp only [ρ]
    linarith
  have hρlt : ρ.re < 1 := by
    dsimp only [ρ]
    linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hρlt
    exact (lt_irrefl 1 hρlt).elim
  have hxi : xi ρ = 0 := by
    dsimp only [ρ]
    exact xi_eq_zero_of_mem_divisor_support q.1.1
  have hζ : riemannZeta ρ = 0 := (xi_eq_zero_iff hρpos hρ1).mp hxi
  rw [show (q.1.1 : ℂ) = ρ by rfl,
    regularizedRiemannZeta_of_ne_one hρ1, hζ, mul_zero]

/-- Exact loss of one vanishing order in the cancelled source at every right Xi zero. -/
theorem analyticOrderAt_dyadicSharpPrimeCancelledSource_eq_pred
    (q : XiRightZeroCopy) :
    ∃ m : ℕ,
      analyticOrderAt
          (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2))
          (xiRightShiftedPole q) = (m + 1 : ℕ) ∧
      analyticOrderAt dyadicSharpPrimeCancelledSource
          (xiRightShiftedPole q) = m := by
  let p : ℂ := xiRightShiftedPole q
  let ρ : ℂ := (q.1.1 : ℂ)
  have hpρ : p - 1 / 2 = ρ := by
    simpa only [p, ρ] using xiRightShiftedPole_sub_half q
  have hregZero : regularizedRiemannZeta ρ = 0 := by
    simpa only [p, hpρ] using
      regularizedRiemannZeta_shift_eq_zero_at_xiRightPole q
  have hreg : AnalyticAt ℂ regularizedRiemannZeta ρ :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) ρ (Set.mem_univ ρ)
  have hmne : (analyticOrderAt regularizedRiemannZeta ρ).toNat ≠ 0 := by
    intro h0
    have horder0 : analyticOrderAt regularizedRiemannZeta ρ = 0 := by
      rw [(ENat.coe_toNat
        (analyticOrderAt_regularizedRiemannZeta_ne_top ρ)).symm, h0]
      rfl
    rcases analyticOrderAt_eq_zero.mp horder0 with h | h
    · exact h hreg
    · exact h hregZero
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have hregOrder : analyticOrderAt regularizedRiemannZeta ρ = (m + 1 : ℕ) := by
    calc
      analyticOrderAt regularizedRiemannZeta ρ =
          ((analyticOrderAt regularizedRiemannZeta ρ).toNat : ℕ∞) :=
        (ENat.coe_toNat
          (analyticOrderAt_regularizedRiemannZeta_ne_top ρ)).symm
      _ = (m + 1 : ℕ) := by rw [hm, Nat.succ_eq_add_one]
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAn : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hshiftOrder := analyticOrderAt_comp_of_deriv_ne_zero
    (f := regularizedRiemannZeta) hshiftAn hshiftDeriv
  have hRorder : analyticOrderAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p =
        (m + 1 : ℕ) := by
    rw [show shift p = ρ by simpa only [shift] using hpρ,
      hregOrder] at hshiftOrder
    simpa only [shift, Function.comp_apply] using hshiftOrder
  have hpHalf : 1 / 2 < p.re := by
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hcancelAn : AnalyticAt ℂ dyadicSharpPrimeCancelledSource p :=
    (differentiableOn_dyadicSharpPrimeCancelledSource_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) p hpHalf
  have hRshiftAn : AnalyticAt ℂ
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p :=
    have hregp : AnalyticAt ℂ regularizedRiemannZeta (p - 1 / 2) := by
      rw [hpρ]
      exact hreg
    AnalyticAt.comp (f := fun s : ℂ => s - 1 / 2) (x := p) hregp hshiftAn
  have hRne : ∀ᶠ s in nhdsWithin p ({p}ᶜ),
      regularizedRiemannZeta (s - 1 / 2) ≠ 0 := by
    rcases hRshiftAn.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
    · exfalso
      have htop := analyticOrderAt_eq_top.mpr hz
      rw [hRorder] at htop
      exact ENat.coe_ne_top _ htop
    · exact hnz
  have hcongr : dyadicSharpPrimeCancelledSource =ᶠ[nhdsWithin p ({p}ᶜ)]
      fun s => regularizedRiemannZeta (s - 1 / 2) *
        dyadicSharpPrimeContinuedSource s := by
    filter_upwards [hRne] with s hs
    exact dyadicSharpPrimeCancelledSource_eq_mul_continuedSource hs
  have hRmero : MeromorphicAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p :=
    hRshiftAn.meromorphicAt
  have hSmero : MeromorphicAt dyadicSharpPrimeContinuedSource p :=
    meromorphicOn_dyadicSharpPrimeContinuedSource_rightHalf p hpHalf
  have horderCongr := meromorphicOrderAt_congr hcongr
  have hRmeroOrder : meromorphicOrderAt
      (fun s : ℂ => regularizedRiemannZeta (s - 1 / 2)) p =
        ((m + 1 : ℕ) : WithTop ℤ) := by
    rw [hRshiftAn.meromorphicOrderAt_eq, hRorder, ENat.map_coe]
    norm_num
  have hprodOrder : meromorphicOrderAt
      (fun s => regularizedRiemannZeta (s - 1 / 2) *
        dyadicSharpPrimeContinuedSource s) p =
      (m : WithTop ℤ) := by
    rw [fun_meromorphicOrderAt_mul hRmero hSmero, hRmeroOrder,
      meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one q]
    exact_mod_cast (show ((m + 1 : ℕ) : ℤ) + (-1 : ℤ) = m by omega)
  refine ⟨m, hRorder, ?_⟩
  have hcancelMeroOrder : meromorphicOrderAt dyadicSharpPrimeCancelledSource p =
      (m : WithTop ℤ) := by
    rw [horderCongr, hprodOrder]
  rw [hcancelAn.meromorphicOrderAt_eq] at hcancelMeroOrder
  generalize horder : analyticOrderAt dyadicSharpPrimeCancelledSource p = o at hcancelMeroOrder ⊢
  induction o using ENat.recTopCoe with
  | top => simp at hcancelMeroOrder
  | coe n =>
      simp only [ENat.map_coe] at hcancelMeroOrder
      have hnm : n = m := by exact_mod_cast hcancelMeroOrder
      simpa [hnm]

end RHTower
