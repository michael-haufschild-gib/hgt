import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# A common Kummer cover of Xi and its derivative forces RH

At a zero of positive finite order `m`, the derivative has order exactly `m - 1`.  Therefore Xi
and its derivative cannot both admit analytic roots of one common degree `d > 1` across a domain
containing that zero: root existence would make both consecutive orders divisible by `d`.

Applied on the right half-plane, this local Kummer collision excludes every off-critical Xi zero.
The degree-two specialization needs only `RHLadder 1` and an analytic square root of `deriv xi`.
Neither root condition alone is a zero-free statement.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- A common degree-`d` analytic Kummer cover of Xi and its derivative on the right half-plane. -/
def XiDerivativeCommonKummerRootRightHalf (d : ℕ) : Prop :=
  ∃ g h : ℂ → ℂ,
    AnalyticOnNhd ℂ g rightHalf ∧
    AnalyticOnNhd ℂ h rightHalf ∧
    (∀ s ∈ rightHalf, g s ^ d = xi s) ∧
    (∀ s ∈ rightHalf, h s ^ d = deriv xi s)

/-- An analytic square root of the differentiated Xi source on the right half-plane. -/
def XiDerivativeSquareRootRightHalf : Prop :=
  ∃ h : ℂ → ℂ,
    AnalyticOnNhd ℂ h rightHalf ∧
      ∀ s ∈ rightHalf, h s ^ 2 = deriv xi s

/-- **Common Kummer-root collision.**  If Xi and its derivative both have analytic `d`-th roots
on the right half-plane for one `d > 1`, then no right-half Xi zero can exist and RH follows. -/
theorem riemannHypothesis_of_xiDerivativeCommonKummerRootRightHalf
    {d : ℕ} (hd : 1 < d)
    (hroot : XiDerivativeCommonKummerRootRightHalf d) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨g, h, hg, hh, hgpow, hhpow⟩ := hroot
  have hdne : d ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd)
  have hdxi : (d : ℕ∞) ∣ analyticOrderAt xi rho :=
    root_orders_dvd isOpen_rightHalf hg hgpow hrho
  have hdderiv : (d : ℕ∞) ∣ analyticOrderAt (deriv xi) rho :=
    root_orders_dvd isOpen_rightHalf hh hhpow hrho
  let m : ℕ := (analyticOrderAt xi rho).toNat
  have hmne : m ≠ 0 := xi_order_toNat_ne_zero hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have hxiOrder : analyticOrderAt xi rho = (k + 1 : ℕ) := by
    calc
      analyticOrderAt xi rho = (m : ℕ∞) :=
        (ENat.coe_toNat (xi_order_ne_top rho)).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderivOrder : analyticOrderAt (deriv xi) rho = (k : ℕ) := by
    have horder := analyticOrderAt_deriv_of_pos
      (xi_analyticOnNhd_univ rho (Set.mem_univ rho))
      (n := k) (by simpa [Nat.cast_add, Nat.cast_one] using hxiOrder)
    simpa using horder
  rw [hxiOrder] at hdxi
  rw [hderivOrder] at hdderiv
  have hdxiNat : d ∣ k + 1 :=
    natCast_dvd_natCast_of_enat hdne hdxi
  have hdderivNat : d ∣ k :=
    natCast_dvd_natCast_of_enat hdne hdderiv
  have hdOne : d ∣ 1 := by
    simpa using Nat.dvd_sub hdxiNat hdderivNat
  have : d = 1 := Nat.eq_one_of_dvd_one hdOne
  omega

/-- **Square-root specialization.**  The first Xi multiplicity rung, together with an analytic
square root of `deriv xi` on the same right half-plane, forces RH. -/
theorem riemannHypothesis_of_rhLadder_one_of_xiDerivativeSquareRootRightHalf
    (hxi : RHLadder 1)
    (hderiv : XiDerivativeSquareRootRightHalf) :
    RiemannHypothesis := by
  obtain ⟨g, hg, hgpow⟩ := rhLadder_one_iff_sqrt_rightHalf.mp hxi
  obtain ⟨h, hh, hhpow⟩ := hderiv
  apply riemannHypothesis_of_xiDerivativeCommonKummerRootRightHalf
    (d := 2) (by norm_num)
  exact ⟨g, h, hg, hh, hgpow, hhpow⟩

end

end RHTower
