import GaloisForLFunctions.RHTower.XiHeatCassiniWoldRelativeOrbitLeakage

/-!
# Quantized orbit-charge floor for reflected Wold compensators

The reflected physical Wold pole head has two quotient-orbit atoms away from the critical line and
no charge on the line.  This module computes the exact squared coefficient energy of that charge.
Every finite shift-two coboundary completion transports the same charge into its compensator, so
an off-critical completion pays the scale-free floor `2 * m^2`, where `m` is pole multiplicity.

Consequently no norm-small, subexponential, or limiting-zero compensator can close the Route-T
handoff in a coefficient-faithful orbit topology.  The surviving producer must force literal
orbit neutrality before divisor selection.  No RH assumption, zero enumeration, numerical
certificate, or new axiom occurs here.
-/

open Complex

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Squared coefficient energy of a finitely supported principal-part vector on any orbit space. -/
def principalPartOrbitChargeEnergy
    {α : Type*} [DecidableEq α] (v : α →₀ (ℕ →₀ ℂ)) : ℝ :=
  v.sum fun _ c => c.sum fun _ z => Complex.normSq z

theorem principalPartOrbitChargeEnergy_neg
    {α : Type*} [DecidableEq α] (v : α →₀ (ℕ →₀ ℂ)) :
    principalPartOrbitChargeEnergy (-v) = principalPartOrbitChargeEnergy v := by
  classical
  unfold principalPartOrbitChargeEnergy
  simp only [Finsupp.sum, Finsupp.support_neg]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finsupp.neg_apply]
  rw [Finsupp.support_neg]
  apply Finset.sum_congr rfl
  intro n hn
  exact Complex.normSq_neg ((v x) n)

/-- Two distinct quotient atoms with common nonzero multiplicity coefficient have exact energy
`2 * m^2`. -/
theorem principalPartOrbitChargeEnergy_two_single
    {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y)
    {m : ℕ} (hm : 1 ≤ m) :
    principalPartOrbitChargeEnergy
        (Finsupp.single x (Finsupp.single 1 (-(m : ℂ))) -
          Finsupp.single y (Finsupp.single 1 (-(m : ℂ)))) =
      2 * (m : ℝ) ^ 2 := by
  classical
  have hm0 : m ≠ 0 := Nat.ne_zero_of_lt hm
  let a : ℕ →₀ ℂ := Finsupp.single 1 (-(m : ℂ))
  have hsupp :
      (Finsupp.single x a - Finsupp.single y a).support = {x, y} := by
    ext z
    by_cases hzx : z = x
    · subst z
      simp [hxy, a, hm0]
    · by_cases hzy : z = y
      · subst z
        simp [hzx, a, hm0]
      · simp [hzx, hzy]
  unfold principalPartOrbitChargeEnergy
  change (Finsupp.single x a - Finsupp.single y a).sum
      (fun _ c => c.sum fun _ z => Complex.normSq z) = _
  simp only [Finsupp.sum, hsupp]
  simp [hxy, a, hm0, Complex.normSq_neg, Complex.normSq_natCast]
  ring

/-- In the open critical strip, the two reflected physical pole positions occupy distinct
`2ℤ`-orbit classes whenever the divisor is off the critical line. -/
theorem reflectedWoldPhysicalOrbitClass_ne_of_re_ne_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) :
    ((rho - 1 : ℂ) : ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ)) ≠
      ((-(starRingEnd ℂ rho) : ℂ) :
        ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ)) := by
  intro horbit
  rw [QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_zmultiples_iff] at horbit
  rcases horbit with ⟨n, hn⟩
  have hnre : 2 * (n : ℝ) = 2 * rho.re - 1 := by
    have hre := congrArg Complex.re hn
    norm_num at hre
    linarith
  have hnlowR : (-1 : ℝ) < (n : ℝ) := by
    linarith [hstrip.1]
  have hnhighR : (n : ℝ) < 1 := by
    linarith [hstrip.2]
  have hnlow : (-1 : ℤ) < n := by exact_mod_cast hnlowR
  have hnhigh : n < (1 : ℤ) := by exact_mod_cast hnhighR
  have hn0 : n = 0 := by omega
  subst n
  norm_num at hnre
  exact hoff (by linarith)

/-- Quotient-orbit charge of the anti-reflected physical Wold pole head. -/
def xiHeatCassiniReflectedWoldPhysicalOrbitCharge
    (rho : ℂ) (m : ℕ) :
    (ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ)) →₀ (ℕ →₀ ℂ) :=
  Finsupp.single
      ((rho - 1 : ℂ) : ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ))
      (simplePoleDifferentialOperator 1 (-(m : ℂ))) -
    Finsupp.single
      ((-(starRingEnd ℂ rho) : ℂ) :
        ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ))
      (simplePoleDifferentialOperator 1 (-(m : ℂ)))

/-- Off the critical line, the reflected physical orbit charge has exact energy `2 * m^2`. -/
theorem xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) {m : ℕ} (hm : 1 ≤ m) :
    principalPartOrbitChargeEnergy
        (xiHeatCassiniReflectedWoldPhysicalOrbitCharge rho m) =
      2 * (m : ℝ) ^ 2 := by
  rw [xiHeatCassiniReflectedWoldPhysicalOrbitCharge,
    simplePoleDifferentialOperator_one_eq_single]
  exact principalPartOrbitChargeEnergy_two_single
    (reflectedWoldPhysicalOrbitClass_ne_of_re_ne_half hstrip hoff) hm

/-- On the critical line, the two reflected orbit atoms coincide and their charge energy is zero. -/
theorem xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq_zero
    {rho : ℂ} (hhalf : rho.re = 1 / 2) (m : ℕ) :
    principalPartOrbitChargeEnergy
        (xiHeatCassiniReflectedWoldPhysicalOrbitCharge rho m) = 0 := by
  have hs : rho - 1 = -(starRingEnd ℂ rho) := by
    apply Complex.ext
    · simp
      linarith
    · simp
  simp [xiHeatCassiniReflectedWoldPhysicalOrbitCharge, hs,
    principalPartOrbitChargeEnergy]

/-- Exact phase transition: reflected Wold orbit-charge energy is zero precisely on the critical
line and `2 * m^2` everywhere else in the open strip. -/
theorem xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq_ite
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    principalPartOrbitChargeEnergy
        (xiHeatCassiniReflectedWoldPhysicalOrbitCharge rho m) =
      if rho.re = 1 / 2 then 0 else 2 * (m : ℝ) ^ 2 := by
  by_cases hhalf : rho.re = 1 / 2
  · rw [if_pos hhalf]
    exact xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq_zero hhalf m
  · rw [if_neg hhalf]
    exact xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq hstrip hhalf hm

/-- Every shift-two coboundary completion transports the full quantized off-critical charge into
its compensator. -/
theorem xiHeatCassiniReflectedWoldPhysicalPoleHead_compensator_chargeEnergy_eq
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) {m : ℕ} (hm : 1 ≤ m)
    (R E : ℂ →₀ (ℕ →₀ ℂ))
    (h : xiHeatCassiniReflectedWoldPhysicalPoleHead rho m + R =
      finiteOrbitCoboundary (2 : ℂ) E) :
    principalPartOrbitChargeEnergy (orbitResidueVector (2 : ℂ) R) =
      2 * (m : ℝ) ^ 2 := by
  rw [xiHeatCassiniReflectedWoldPhysicalPoleHead_compensator_orbitLeakage
    rho m R E h]
  rw [principalPartOrbitChargeEnergy_neg]
  exact xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq hstrip hoff hm

/-- Scale-free no-go: every off-critical completion has compensator orbit-charge energy at least
`2`, independently of its distance from the critical line. -/
theorem two_le_xiHeatCassiniReflectedWoldPhysicalPoleHead_compensator_chargeEnergy
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) {m : ℕ} (hm : 1 ≤ m)
    (R E : ℂ →₀ (ℕ →₀ ℂ))
    (h : xiHeatCassiniReflectedWoldPhysicalPoleHead rho m + R =
      finiteOrbitCoboundary (2 : ℂ) E) :
    2 ≤ principalPartOrbitChargeEnergy (orbitResidueVector (2 : ℂ) R) := by
  rw [xiHeatCassiniReflectedWoldPhysicalPoleHead_compensator_chargeEnergy_eq
    hstrip hoff hm R E h]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

end

end RHTower
