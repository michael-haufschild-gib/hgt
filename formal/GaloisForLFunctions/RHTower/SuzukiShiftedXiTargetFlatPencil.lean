import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Suzuki's shifted Xi target is one flat affine pencil

The boundary-free Fourier symbol suggested by Suzuki's shifted continuous kernel is, up to a
fixed nonzero scalar,

`R_eta(z) = z^2 * XiC(z) / (XiC'(z) - eta * XiC(z))`.

This module proves the exact unconditional structure of that pencil.  Distinct shift fibres recover
`XiC` by an affine secant, targets are related by a flat Mobius transport, and every Xi zero of
arbitrary multiplicity becomes a simple zero whose trailing coefficient records the original
multiplicity.  The shift parameter itself obeys an exact Riccati equation.

No finite-aperture convergence, RH, or simplicity of Xi zeros is assumed here.
-/

open Complex Set Filter Topology

namespace RHTower

noncomputable section

/-- The affine denominator in Suzuki's boundary-free shifted Xi target.  Suzuki's real form shift
`lambda` corresponds to `eta = -I * lambda`, up to a fixed nonzero scalar in the target. -/
def suzukiShiftedXiDenominator (eta z : ℂ) : ℂ :=
  deriv XiC z - eta * XiC z

/-- The centered, scalar-normalized shifted reciprocal-logarithmic Xi target. -/
def suzukiShiftedXiTarget (eta z : ℂ) : ℂ :=
  z ^ 2 * XiC z / suzukiShiftedXiDenominator eta z

/-- Flat transport between two denominator fibres. -/
def suzukiXiShiftTransport (alpha beta z : ℂ) : ℂ :=
  suzukiShiftedXiDenominator alpha z / suzukiShiftedXiDenominator beta z

/-- Denominator fibres form an affine pencil with direction `-XiC`. -/
theorem suzukiShiftedXiDenominator_sub (alpha beta z : ℂ) :
    suzukiShiftedXiDenominator alpha z - suzukiShiftedXiDenominator beta z =
      (beta - alpha) * XiC z := by
  simp only [suzukiShiftedXiDenominator]
  ring

/-- Two distinct normalized denominator fibres recover centered Xi exactly. -/
theorem XiC_eq_suzukiShiftedXiDenominator_secant {alpha beta z : ℂ}
    (h : alpha ≠ beta) :
    XiC z =
      (suzukiShiftedXiDenominator alpha z - suzukiShiftedXiDenominator beta z) /
        (beta - alpha) := by
  rw [suzukiShiftedXiDenominator_sub]
  have hba : beta - alpha ≠ 0 := sub_ne_zero.mpr h.symm
  field_simp [hba]

/-- Flat denominator transport carries the complete shifted target. -/
theorem suzukiXiShiftTransport_target {alpha beta z : ℂ}
    (ha : suzukiShiftedXiDenominator alpha z ≠ 0)
    (hb : suzukiShiftedXiDenominator beta z ≠ 0) :
    suzukiXiShiftTransport alpha beta z * suzukiShiftedXiTarget alpha z =
      suzukiShiftedXiTarget beta z := by
  simp only [suzukiXiShiftTransport, suzukiShiftedXiTarget]
  field_simp

/-- The shift transport is a flat cocycle. -/
theorem suzukiXiShiftTransport_cocycle {alpha beta gamma z : ℂ}
    (hb : suzukiShiftedXiDenominator beta z ≠ 0)
    (hg : suzukiShiftedXiDenominator gamma z ≠ 0) :
    suzukiXiShiftTransport alpha beta z * suzukiXiShiftTransport beta gamma z =
      suzukiXiShiftTransport alpha gamma z := by
  simp only [suzukiXiShiftTransport]
  field_simp

/-- Division-free Mobius shift law for the target pencil. -/
theorem suzukiShiftedXiTarget_mobius_cross {alpha beta z : ℂ}
    (ha : suzukiShiftedXiDenominator alpha z ≠ 0)
    (hb : suzukiShiftedXiDenominator beta z ≠ 0) :
    (z ^ 2 - (beta - alpha) * suzukiShiftedXiTarget alpha z) *
        suzukiShiftedXiTarget beta z =
      z ^ 2 * suzukiShiftedXiTarget alpha z := by
  simp only [suzukiShiftedXiTarget]
  field_simp [ha, hb]
  simp only [suzukiShiftedXiDenominator]
  ring

/-- Reciprocal target coordinates translate by the shift difference.  Denominator nonvanishing is
not needed: the identity remains valid in the totalized field once the numerator is nonzero. -/
theorem suzukiShiftedXiTarget_reciprocal_translation {alpha beta z : ℂ}
    (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    z ^ 2 / suzukiShiftedXiTarget beta z -
        z ^ 2 / suzukiShiftedXiTarget alpha z = alpha - beta := by
  simp only [suzukiShiftedXiTarget]
  field_simp [hz, hXi]
  simp only [suzukiShiftedXiDenominator]
  ring

/-- At an arbitrary Xi zero of order `k+1`, every shifted denominator has exact order `k`.
The shift term cannot cancel the derivative because it has strictly larger local order. -/
theorem analyticOrderAt_suzukiShiftedXiDenominator_eq_pred_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    ∃ k : ℕ,
      analyticOrderAt XiC z = (k + 1 : ℕ) ∧
      analyticOrderAt (suzukiShiftedXiDenominator eta) z = (k : ℕ) := by
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
  refine ⟨k, hXiOrder, ?_⟩
  by_cases heta : eta = 0
  · subst eta
    have hfun : suzukiShiftedXiDenominator 0 = deriv XiC := by
      funext w
      simp [suzukiShiftedXiDenominator]
    rw [hfun]
    exact hderivOrder
  · let G : ℂ → ℂ := fun w => (-eta) * XiC w
    have hGOrder : analyticOrderAt G z = (k + 1 : ℕ) := by
      dsimp only [G]
      change analyticOrderAt ((fun _ : ℂ => -eta) * XiC) z = (k + 1 : ℕ)
      have hcOrder : analyticOrderAt (fun _ : ℂ => -eta) z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (neg_ne_zero.mpr heta))
      rw [analyticOrderAt_mul analyticAt_const
        (XiC_analytic z (Set.mem_univ z)), hcOrder, zero_add, hXiOrder]
    have hlt : analyticOrderAt (deriv XiC) z < analyticOrderAt G z := by
      rw [hderivOrder, hGOrder]
      exact_mod_cast Nat.lt_succ_self k
    have hfun : suzukiShiftedXiDenominator eta = deriv XiC + G := by
      funext w
      simp only [suzukiShiftedXiDenominator, G, Pi.add_apply]
      ring
    rw [hfun, analyticOrderAt_add_eq_left_of_lt hlt, hderivOrder]

private theorem XiC_zero_point_ne_zero {z : ℂ} (hz : XiC z = 0) : z ≠ 0 := by
  intro hz0
  subst z
  exact XiC_zero_ne hz

/-- Every Xi zero becomes a simple zero of the meromorphic normal form of every finite shifted
target, independently of its original Xi multiplicity. -/
theorem meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    meromorphicOrderAt (suzukiShiftedXiTarget eta) z = 1 := by
  have hz0 : z ≠ 0 := XiC_zero_point_ne_zero hz
  obtain ⟨k, hXi, hden⟩ :=
    analyticOrderAt_suzukiShiftedXiDenominator_eq_pred_of_XiC_zero
      (eta := eta) hz
  have hnum : AnalyticAt ℂ (fun w : ℂ => w ^ 2 * XiC w) z := by
    have hpow : AnalyticAt ℂ (fun w : ℂ => w ^ 2) z := by fun_prop
    exact hpow.mul (XiC_analytic z (Set.mem_univ z))
  have hdenAn : AnalyticAt ℂ (suzukiShiftedXiDenominator eta) z := by
    apply (XiC_analytic z (Set.mem_univ z)).deriv.sub
    exact analyticAt_const.mul (XiC_analytic z (Set.mem_univ z))
  have hnumOrder :
      analyticOrderAt (fun w : ℂ => w ^ 2 * XiC w) z = (k + 1 : ℕ) := by
    let Q : ℂ → ℂ := fun w => w ^ 2
    have hQ : AnalyticAt ℂ Q z := by fun_prop
    have hQOrder : analyticOrderAt Q z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (pow_ne_zero 2 hz0))
    change analyticOrderAt (Q * XiC) z = (k + 1 : ℕ)
    rw [analyticOrderAt_mul hQ (XiC_analytic z (Set.mem_univ z)),
      hQOrder, zero_add, hXi]
  change meromorphicOrderAt
    ((fun w : ℂ => w ^ 2 * XiC w) / suzukiShiftedXiDenominator eta) z = 1
  rw [meromorphicOrderAt_div hnum.meromorphicAt hdenAn.meromorphicAt,
    hnum.meromorphicOrderAt_eq, hdenAn.meromorphicOrderAt_eq, hnumOrder, hden]
  change ENat.map Nat.cast ((k + 1 : ℕ) : ℕ∞) - (k : WithTop ℤ) = 1
  rw [ENat.map_coe]
  exact_mod_cast (by omega : (k : ℤ) + 1 - k = 1)

/-- Exact multiplicity fingerprint.  At an Xi zero of multiplicity `m`, the shifted target's
simple-zero trailing coefficient is `z^2 / m`, independent of the shift. -/
theorem exists_multiplicity_meromorphicTrailingCoeffAt_suzukiShiftedXiTarget
    {eta z : ℂ} (hz : XiC z = 0) :
    ∃ m : ℕ, 0 < m ∧ analyticOrderAt XiC z = (m : ℕ) ∧
      meromorphicTrailingCoeffAt (suzukiShiftedXiTarget eta) z = z ^ 2 / (m : ℂ) := by
  have hz0 : z ≠ 0 := XiC_zero_point_ne_zero hz
  obtain ⟨k, hXiOrder, _⟩ :=
    analyticOrderAt_suzukiShiftedXiDenominator_eq_pred_of_XiC_zero
      (eta := eta) hz
  let m : ℕ := k + 1
  have hm : 0 < m := by simp [m]
  have hXiOrder' : analyticOrderAt XiC z = (m : ℕ) := by
    simpa [m] using hXiOrder
  have hXiAn : AnalyticAt ℂ XiC z := XiC_analytic z (Set.mem_univ z)
  obtain ⟨g, hg, hg0, hfg⟩ :=
    hXiAn.analyticOrderAt_eq_natCast.mp hXiOrder'
  have hfgMul : XiC =ᶠ[𝓝 z] fun w => (w - z) ^ m * g w := by
    filter_upwards [hfg] with w hw
    simpa [smul_eq_mul] using hw
  let H : ℂ → ℂ := fun w =>
    (m : ℂ) * g w + (w - z) * (deriv g w - eta * g w)
  have hH : AnalyticAt ℂ H z := by
    dsimp only [H]
    exact (analyticAt_const.mul hg).add
      ((analyticAt_id.sub analyticAt_const).mul
        (hg.deriv.sub (analyticAt_const.mul hg)))
  have hHz : H z = (m : ℂ) * g z := by simp [H]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hH0 : H z ≠ 0 := by rw [hHz]; exact mul_ne_zero hmC hg0
  have hfactorDeriv :
      deriv (fun w : ℂ => (w - z) ^ m * g w) =ᶠ[𝓝 z]
        fun w => (w - z) ^ k * ((m : ℂ) * g w + (w - z) * deriv g w) := by
    filter_upwards [hg.eventually_analyticAt] with w hgw
    have hp : HasDerivAt (fun u : ℂ => (u - z) ^ m)
        ((m : ℂ) * (w - z) ^ k) w := by
      have hbase : HasDerivAt (fun u : ℂ => u - z) 1 w :=
        (hasDerivAt_id w).sub_const z
      convert hbase.pow m using 1
      simp [m]
    change deriv (((fun u : ℂ => (u - z) ^ m) * g)) w = _
    rw [(hp.mul hgw.differentiableAt.hasDerivAt).deriv]
    simp only [m, pow_succ]
    ring
  have hderivEq : deriv XiC =ᶠ[𝓝 z]
      fun w => (w - z) ^ k * ((m : ℂ) * g w + (w - z) * deriv g w) :=
    hfgMul.deriv.trans hfactorDeriv
  have hdenEq : suzukiShiftedXiDenominator eta =ᶠ[𝓝 z]
      fun w => (w - z) ^ k * H w := by
    filter_upwards [hderivEq, hfgMul] with w hd hf
    rw [suzukiShiftedXiDenominator, hd, hf]
    simp only [H, m, pow_succ]
    ring
  have hnumEq : (fun w : ℂ => w ^ 2 * XiC w) =ᶠ[𝓝 z]
      fun w => (w - z) ^ m * (w ^ 2 * g w) := by
    filter_upwards [hfgMul] with w hf
    rw [hf]
    ring
  let Q : ℂ → ℂ := fun w => w ^ 2 * g w / H w
  have hQ : AnalyticAt ℂ Q z := by
    dsimp only [Q]
    exact ((by fun_prop : AnalyticAt ℂ (fun w : ℂ => w ^ 2) z).mul hg).div hH hH0
  have hQz : Q z = z ^ 2 / (m : ℂ) := by
    simp only [Q, hHz]
    field_simp [hmC, hg0]
  have hQ0 : Q z ≠ 0 := by
    rw [hQz]
    exact div_ne_zero (pow_ne_zero 2 hz0) hmC
  have hHne : ∀ᶠ w in 𝓝 z, H w ≠ 0 := hH.continuousAt.eventually_ne hH0
  have htargetEq : suzukiShiftedXiTarget eta =ᶠ[𝓝[≠] z]
      fun w => (w - z) * Q w := by
    filter_upwards [hnumEq.filter_mono nhdsWithin_le_nhds,
      hdenEq.filter_mono nhdsWithin_le_nhds,
      hHne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with w hnum hden hHw hwz
    rw [suzukiShiftedXiTarget, hnum, hden]
    simp only [Q]
    have hw0 : w - z ≠ 0 := sub_ne_zero.mpr hwz
    field_simp [pow_ne_zero k hw0, hHw]
    simp only [m, pow_succ]
    ring
  refine ⟨m, hm, hXiOrder', ?_⟩
  rw [hQ.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (f := suzukiShiftedXiTarget eta) (n := 1) hQ0 ?_, hQz]
  filter_upwards [htargetEq] with w hw
  simpa using hw

/-- The multiplicity fingerprint expressed directly through Xi's analytic order. -/
theorem meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) :
    meromorphicTrailingCoeffAt (suzukiShiftedXiTarget eta) z =
      z ^ 2 / ((analyticOrderAt XiC z).toNat : ℂ) := by
  obtain ⟨m, _, hm, htrail⟩ :=
    exists_multiplicity_meromorphicTrailingCoeffAt_suzukiShiftedXiTarget
      (eta := eta) hz
  have htoNat : (analyticOrderAt XiC z).toNat = m := by rw [hm]; simp
  simpa [htoNat] using htrail

/-- Raw shift-parameter derivative of the target pencil. -/
theorem hasDerivAt_suzukiShiftedXiTarget_parameter {eta z : ℂ}
    (hden : suzukiShiftedXiDenominator eta z ≠ 0) :
    HasDerivAt (fun tau => suzukiShiftedXiTarget tau z)
      (z ^ 2 * XiC z ^ 2 / suzukiShiftedXiDenominator eta z ^ 2) eta := by
  have hnum : HasDerivAt (fun _ : ℂ => z ^ 2 * XiC z) 0 eta :=
    hasDerivAt_const _ _
  have hden' : HasDerivAt (fun tau : ℂ => suzukiShiftedXiDenominator tau z)
      (-XiC z) eta := by
    simpa [suzukiShiftedXiDenominator] using
      (hasDerivAt_const (x := eta) (c := deriv XiC z)).sub
        ((hasDerivAt_id eta).mul_const (XiC z))
  have hquot := hnum.div hden' hden
  change HasDerivAt
    (fun tau : ℂ => z ^ 2 * XiC z / suzukiShiftedXiDenominator tau z)
      (z ^ 2 * XiC z ^ 2 / suzukiShiftedXiDenominator eta z ^ 2) eta
  convert hquot using 1
  ring

/-- At every nonzero spectral point, the shift parameter evolves by an exact Riccati law. -/
theorem hasDerivAt_suzukiShiftedXiTarget_parameter_riccati {eta z : ℂ}
    (hz : z ≠ 0) (hden : suzukiShiftedXiDenominator eta z ≠ 0) :
    HasDerivAt (fun tau => suzukiShiftedXiTarget tau z)
      (suzukiShiftedXiTarget eta z ^ 2 / z ^ 2) eta := by
  convert hasDerivAt_suzukiShiftedXiTarget_parameter hden using 1
  simp only [suzukiShiftedXiTarget]
  field_simp

/-- At a simple Xi zero, every shifted target has the same first jet `z^2`. -/
theorem hasDerivAt_suzukiShiftedXiTarget_of_simple_XiC_zero
    {eta z : ℂ} (hz : XiC z = 0) (hsimple : deriv XiC z ≠ 0) :
    HasDerivAt (suzukiShiftedXiTarget eta) (z ^ 2) z := by
  have hXi : HasDerivAt XiC (deriv XiC z) z :=
    (XiC_analytic z (Set.mem_univ z)).differentiableAt.hasDerivAt
  have hXi' : HasDerivAt (deriv XiC) (deriv (deriv XiC) z) z :=
    ((XiC_analytic z (Set.mem_univ z)).deriv).differentiableAt.hasDerivAt
  have hsq : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
    simpa [id, mul_comm] using (hasDerivAt_id z).pow 2
  have hnum := hsq.mul hXi
  have hden : HasDerivAt (suzukiShiftedXiDenominator eta)
      (deriv (deriv XiC) z - eta * deriv XiC z) z := by
    simpa [suzukiShiftedXiDenominator] using
      hXi'.sub ((hasDerivAt_const (x := z) (c := eta)).mul hXi)
  have hdenne : suzukiShiftedXiDenominator eta z ≠ 0 := by
    simpa [suzukiShiftedXiDenominator, hz] using hsimple
  have hquot := hnum.div hden hdenne
  change HasDerivAt
    (fun w : ℂ => w ^ 2 * XiC w / suzukiShiftedXiDenominator eta w) (z ^ 2) z
  convert hquot using 1
  simp only [hz, mul_zero, suzukiShiftedXiDenominator, Pi.mul_apply]
  field_simp [hsimple]
  ring

end

end RHTower
