import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam

/-!
# A common Kummer cover of XiC and the Hedenmalm E-function forces RH

The source-defined Hermite--Biehler candidate is `E_Xi = XiC + I * XiC'`.  At every XiC zero of
positive order `m`, its derivative term has the strictly smaller order `m - 1`, so `E_Xi` has
exactly that order.  Consequently XiC and `E_Xi` cannot both have analytic roots of one common
degree `d > 1` across a half-plane containing the zero.

Failure of RH produces an XiC zero in the centered upper half-plane by functional-equation
reflection.  Hence a common Kummer cover there forces RH.  For degree two, `RHLadder 1` supplies
the XiC cover after the same reflection, leaving only a square root of the existing Hedenmalm
source function.  This is weaker than Hermite--Biehler zero-freeness: even-multiplicity `E_Xi`
zeros are allowed.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The centered upper half-plane used by the Hedenmalm orientation coordinate. -/
def xiCenteredUpperHalfPlane : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_xiCenteredUpperHalfPlane : IsOpen xiCenteredUpperHalfPlane := by
  exact isOpen_lt continuous_const Complex.continuous_im

/-- A common degree-`d` analytic Kummer cover of XiC and the Hedenmalm `E_Xi` function on the
centered upper half-plane. -/
def XiHedenmalmCommonKummerRootUpperHalf (d : ℕ) : Prop :=
  ∃ g h : ℂ → ℂ,
    AnalyticOnNhd ℂ g xiCenteredUpperHalfPlane ∧
    AnalyticOnNhd ℂ h xiCenteredUpperHalfPlane ∧
    (∀ z ∈ xiCenteredUpperHalfPlane, g z ^ d = XiC z) ∧
    (∀ z ∈ xiCenteredUpperHalfPlane, h z ^ d = xiHedenmalmDeBrangesE z)

/-- The remaining degree-two source condition after `RHLadder 1` supplies the XiC square root. -/
def XiHedenmalmESquareRootUpperHalf : Prop :=
  ∃ h : ℂ → ℂ,
    AnalyticOnNhd ℂ h xiCenteredUpperHalfPlane ∧
      ∀ z ∈ xiCenteredUpperHalfPlane, h z ^ 2 = xiHedenmalmDeBrangesE z

/-- At an XiC zero of order `k+1`, the Hedenmalm function `XiC + I*XiC'` has exact order `k`.
The derivative term cannot cancel against XiC because their local orders are different. -/
theorem analyticOrderAt_xiHedenmalmDeBrangesE_eq_pred_of_XiC_zero
    {z : ℂ} (hz : XiC z = 0) :
    ∃ k : ℕ,
      analyticOrderAt XiC z = (k + 1 : ℕ) ∧
      analyticOrderAt xiHedenmalmDeBrangesE z = (k : ℕ) := by
  let m : ℕ := (analyticOrderAt XiC z).toNat
  have hmne : m ≠ 0 := by
    have hne : analyticOrderAt XiC z ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨XiC_analytic z (Set.mem_univ z), hz⟩
    intro hm
    rcases ENat.toNat_eq_zero.mp hm with hzero | htop
    · exact hne hzero
    · exact XiC_order_ne_top z htop
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have hXiOrder : analyticOrderAt XiC z = (k + 1 : ℕ) := by
    calc
      analyticOrderAt XiC z = (m : ℕ∞) :=
        (ENat.coe_toNat (XiC_order_ne_top z)).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  have hderivOrder : analyticOrderAt (deriv XiC) z = (k : ℕ) := by
    have horder := analyticOrderAt_deriv_of_pos
      (XiC_analytic z (Set.mem_univ z))
      (n := k) (by simpa [Nat.cast_add, Nat.cast_one] using hXiOrder)
    simpa using horder
  let D : ℂ → ℂ := fun w => I * deriv XiC w
  have hDOrder : analyticOrderAt D z = (k : ℕ) := by
    dsimp only [D]
    change analyticOrderAt ((fun _ : ℂ => I) * deriv XiC) z = (k : ℕ)
    have hIOrder : analyticOrderAt (fun _ : ℂ => I) z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr I_ne_zero)
    rw [analyticOrderAt_mul analyticAt_const
      (XiC_analytic z (Set.mem_univ z)).deriv,
      hIOrder, zero_add, hderivOrder]
  have hlt : analyticOrderAt D z < analyticOrderAt XiC z := by
    rw [hDOrder, hXiOrder]
    exact_mod_cast Nat.lt_succ_self k
  have hEfun : xiHedenmalmDeBrangesE = D + XiC := by
    funext w
    simp only [xiHedenmalmDeBrangesE, D, Pi.add_apply]
    ring
  refine ⟨k, hXiOrder, ?_⟩
  rw [hEfun, analyticOrderAt_add_eq_left_of_lt hlt, hDOrder]

/-- **Hedenmalm Kummer collision.**  A common degree-`d` analytic root of XiC and `E_Xi` on the
centered upper half-plane, for one `d > 1`, excludes every off-critical Xi zero and proves RH. -/
theorem riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf
    {d : ℕ} (hd : 1 < d)
    (hroot : XiHedenmalmCommonKummerRootUpperHalf d) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨g, h, hg, hh, hgpow, hhpow⟩ := hroot
  let z : ℂ := ((1 - rho) - 1 / 2) * (-I)
  have hzUpper : z ∈ xiCenteredUpperHalfPlane := by
    rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq]
    dsimp only [z]
    simp
    have hr := mem_rightHalf.mp hrho
    linarith
  have hcoord : 1 / 2 + z * I = 1 - rho := by
    dsimp only [z]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hXiZero : XiC z = 0 := by
    rw [XiC, hcoord, xi_one_sub, hzero]
  obtain ⟨k, hXiOrder, hEOrder⟩ :=
    analyticOrderAt_xiHedenmalmDeBrangesE_eq_pred_of_XiC_zero hXiZero
  have hdne : d ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd)
  have hdXi : (d : ℕ∞) ∣ analyticOrderAt XiC z :=
    root_orders_dvd isOpen_xiCenteredUpperHalfPlane hg hgpow hzUpper
  have hdE : (d : ℕ∞) ∣ analyticOrderAt xiHedenmalmDeBrangesE z :=
    root_orders_dvd isOpen_xiCenteredUpperHalfPlane hh hhpow hzUpper
  rw [hXiOrder] at hdXi
  rw [hEOrder] at hdE
  have hdXiNat : d ∣ k + 1 := natCast_dvd_natCast_of_enat hdne hdXi
  have hdENat : d ∣ k := natCast_dvd_natCast_of_enat hdne hdE
  have hdOne : d ∣ 1 := by simpa using Nat.dvd_sub hdXiNat hdENat
  have : d = 1 := Nat.eq_one_of_dvd_one hdOne
  omega

/-- `RHLadder 1` transports its analytic Xi square root through functional-equation reflection to
an XiC square root on the centered upper half-plane.  A square root of `E_Xi` there then closes the
common Kummer collision. -/
theorem riemannHypothesis_of_rhLadder_one_of_xiHedenmalmESquareRootUpperHalf
    (hxi : RHLadder 1)
    (hE : XiHedenmalmESquareRootUpperHalf) :
    RiemannHypothesis := by
  obtain ⟨g, hg, hgpow⟩ := rhLadder_one_iff_sqrt_rightHalf.mp hxi
  obtain ⟨h, hh, hhpow⟩ := hE
  let pull : ℂ → ℂ := fun z => 1 / 2 - z * I
  let G : ℂ → ℂ := fun z => g (pull z)
  have hpull_mem : ∀ z ∈ xiCenteredUpperHalfPlane, pull z ∈ rightHalf := by
    intro z hz
    rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq] at hz
    rw [mem_rightHalf]
    dsimp only [pull]
    simp
    linarith
  have hG : AnalyticOnNhd ℂ G xiCenteredUpperHalfPlane := by
    intro z hz
    dsimp only [G]
    exact AnalyticAt.comp (f := pull) (x := z)
      (hg (pull z) (hpull_mem z hz)) (by dsimp only [pull]; fun_prop)
  have hGpow : ∀ z ∈ xiCenteredUpperHalfPlane, G z ^ 2 = XiC z := by
    intro z hz
    rw [show G z ^ 2 = xi (pull z) by
      exact hgpow (pull z) (hpull_mem z hz)]
    rw [XiC]
    have hreflect : pull z = 1 - (1 / 2 + z * I) := by
      dsimp only [pull]
      ring
    rw [hreflect, xi_one_sub]
  apply riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf
    (d := 2) (by norm_num)
  exact ⟨G, h, hG, hh, hGpow, hhpow⟩

end

end RHTower
