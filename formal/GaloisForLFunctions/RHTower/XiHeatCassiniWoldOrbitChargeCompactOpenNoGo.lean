import GaloisForLFunctions.RHTower.XiHeatCassiniWoldOrbitChargeQuantization
import GaloisForLFunctions.RHTower.XiSourceChargeCompactOpenDescent

/-!
# Compact-open no-go for reflected Wold orbit charge

Attach the exact quotient-orbit charge energy of the reflected Wold physical pole head to every
Xi divisor point with its analytic multiplicity.  The energy is zero on the critical line and at
least two off it.

The corpus's canonical multiplicity-matched bubbles converge locally uniformly back to Xi while
retaining any off-line source charge.  Therefore no compact-open sequentially continuous scalar
reporter can preserve the reflected Wold energy along these bubbles.  Globally, existence of such
a reporter is equivalent to RH.  This rules out ordinary compact-open scalar tightness as the
missing Route-T2 bridge; a viable bridge must retain source marking or noncompact boundary mass.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Reflected Wold quotient-orbit charge energy attached to an actual Xi divisor point with its
analytic multiplicity. -/
def xiReflectedWoldOrbitChargeEnergy (rho : XiDivisorSupport) : ℝ :=
  principalPartOrbitChargeEnergy
    (xiHeatCassiniReflectedWoldPhysicalOrbitCharge (rho : ℂ)
      (analyticOrderAt xi (rho : ℂ)).toNat)

/-- Exact wall law for multiplicity-labelled Xi divisor points. -/
theorem xiReflectedWoldOrbitChargeEnergy_eq_ite (rho : XiDivisorSupport) :
    xiReflectedWoldOrbitChargeEnergy rho =
      if (rho : ℂ).re = 1 / 2 then 0
      else 2 * ((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) ^ 2 := by
  unfold xiReflectedWoldOrbitChargeEnergy
  exact xiHeatCassiniReflectedWoldPhysicalOrbitCharge_energy_eq_ite
    (xi_divisor_support_re_mem_open_unit rho)
    (Nat.pos_of_ne_zero
      (xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho)))

/-- Critical-line divisor points have zero reflected Wold orbit-charge energy. -/
theorem xiReflectedWoldOrbitChargeEnergy_eq_zero_of_re_eq_half
    (rho : XiDivisorSupport) (hhalf : (rho : ℂ).re = 1 / 2) :
    xiReflectedWoldOrbitChargeEnergy rho = 0 := by
  rw [xiReflectedWoldOrbitChargeEnergy_eq_ite, if_pos hhalf]

/-- Every off-line Xi divisor point has reflected Wold orbit-charge energy at least two. -/
theorem two_le_xiReflectedWoldOrbitChargeEnergy_of_re_ne_half
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    2 ≤ xiReflectedWoldOrbitChargeEnergy rho := by
  rw [xiReflectedWoldOrbitChargeEnergy_eq_ite, if_neg hoff]
  have hm : 1 ≤ (analyticOrderAt xi (rho : ℂ)).toNat :=
    Nat.one_le_iff_ne_zero.mpr
      (xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support rho))
  have hmR : (1 : ℝ) ≤ (analyticOrderAt xi (rho : ℂ)).toNat := by
    exact_mod_cast hm
  nlinarith

/-- Exact reflected-Wold charge energy is represented by one compact-open scalar reporter on all
canonical multiplicity-matched bubbles. -/
def XiWoldOrbitChargeEnergyCompactOpenDescent : Prop :=
  ∃ Q : (ℂ → ℂ) → ℝ,
    CompactOpenSequentialReporter Q ∧
      Q xi = 0 ∧
      ∀ (rho : XiDivisorSupport) (n : ℕ),
        Q (xiSourceMatchedBubble rho n) =
          xiReflectedWoldOrbitChargeEnergy rho

/-- At an off-line Xi divisor, compact-open scalar continuity cannot retain quantized reflected
Wold charge along the canonical escaping bubbles. -/
theorem offLineXiDivisor_no_compactOpen_woldOrbitChargeEnergyReporter
    (Q : (ℂ → ℂ) → ℝ) (hQ : CompactOpenSequentialReporter Q)
    (hXi : Q xi = 0) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ¬ ∀ n : ℕ, Q (xiSourceMatchedBubble rho n) =
      xiReflectedWoldOrbitChargeEnergy rho := by
  intro hfaithful
  have htoXi : Tendsto (fun n => Q (xiSourceMatchedBubble rho n)) atTop
      (nhds (Q xi)) :=
    hQ _ _ (xiSourceMatchedBubble_tendstoLocallyUniformly rho hoff)
  have htoZero : Tendsto (fun n => Q (xiSourceMatchedBubble rho n)) atTop
      (nhds 0) := by
    simpa [hXi] using htoXi
  have htoEnergy : Tendsto (fun n => Q (xiSourceMatchedBubble rho n)) atTop
      (nhds (xiReflectedWoldOrbitChargeEnergy rho)) := by
    simpa only [hfaithful] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => xiReflectedWoldOrbitChargeEnergy rho) atTop
        (nhds (xiReflectedWoldOrbitChargeEnergy rho)))
  have hzero : xiReflectedWoldOrbitChargeEnergy rho = 0 :=
    tendsto_nhds_unique htoEnergy htoZero
  linarith [two_le_xiReflectedWoldOrbitChargeEnergy_of_re_ne_half rho hoff]

/-- Compact-open scalar descent of exact reflected-Wold charge exists exactly under RH. -/
theorem xiWoldOrbitChargeEnergyCompactOpenDescent_iff_riemannHypothesis :
    XiWoldOrbitChargeEnergyCompactOpenDescent ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨Q, hQ, hXi, hfaithful⟩
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    by_contra hoff
    exact offLineXiDivisor_no_compactOpen_woldOrbitChargeEnergyReporter
      Q hQ hXi rho hoff (hfaithful rho)
  · intro hRH
    refine ⟨fun _ => 0, ?_, rfl, ?_⟩
    · intro F f hF
      exact tendsto_const_nhds
    · intro rho n
      simp only
      exact (xiReflectedWoldOrbitChargeEnergy_eq_zero_of_re_eq_half rho
        (xi_divisor_support_re_eq_half_of_rh hRH rho)).symm

end

end RHTower
