import GaloisForLFunctions.RHTower.XiHeatCassiniWoldOrbitChargeCompactOpenNoGo

/-!
# Upper-semicontinuous no-go for reflected Wold orbit charge

The canonical source-matched bubbles converge locally uniformly back to `xi` while preserving the
complete multiplicity-labelled reflected Wold orbit charge. Previous compact-open no-go results
required exact charge representation and two-sided sequential continuity. Neither is necessary.

If a scalar reporter is only sequentially upper semicontinuous, is nonpositive at `xi`, and merely
majorizes the Wold charge on every canonical bubble, then an off-line divisor already gives a
contradiction: every bubble value is at least the exact two-unit charge quantum, whereas upper
semicontinuity forces those values eventually below one. Such a majorant exists exactly under RH.

The positive survivor is quantitative. Under false RH, every anchored lower-faithful reporter has
one canonical source-matched bubble sequence on which its values remain at least two above its
value at `xi`. Thus any viable T2 scalar selector must have a downward compact-open singularity of
at least one full Wold quantum; ordinary one-sided regularity is already too strong.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- A scalar reporter that is sequentially upper semicontinuous for locally uniform convergence. -/
def CompactOpenSequentialUpperReporter (Q : (ℂ → ℂ) → ℝ) : Prop :=
  ∀ (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    TendstoLocallyUniformly F f atTop →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop, Q (F n) ≤ Q f + ε

/-- **Exact jump survivor.** Every anchored lower-faithful reporter has a two-unit compact-open
jump along the canonical bubble sequence of an off-line Xi divisor. -/
theorem offLineXiDivisor_woldOrbitChargeEnergy_two_le_upperJump
    (Q : (ℂ → ℂ) → ℝ) (hXi : Q xi ≤ 0)
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2)
    (hfaithful : ∀ n : ℕ,
      xiReflectedWoldOrbitChargeEnergy rho ≤ Q (xiSourceMatchedBubble rho n)) :
    ∀ n : ℕ, Q xi + 2 ≤ Q (xiSourceMatchedBubble rho n) := by
  intro n
  have hcharge := two_le_xiReflectedWoldOrbitChargeEnergy_of_re_ne_half rho hoff
  have hmajor := hfaithful n
  linarith

/-- Upper semicontinuity cannot retain even a lower majorant for off-line Wold charge. -/
theorem offLineXiDivisor_no_compactOpenUpper_woldOrbitChargeEnergyMajorant
    (Q : (ℂ → ℂ) → ℝ) (hXi : Q xi ≤ 0)
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2)
    (hfaithful : ∀ n : ℕ,
      xiReflectedWoldOrbitChargeEnergy rho ≤ Q (xiSourceMatchedBubble rho n)) :
    ¬ CompactOpenSequentialUpperReporter Q := by
  intro hupper
  have heventual := hupper (xiSourceMatchedBubble rho) xi
    (xiSourceMatchedBubble_tendstoLocallyUniformly rho hoff) 1 (by norm_num)
  obtain ⟨n, hn⟩ := heventual.exists
  have hjump := offLineXiDivisor_woldOrbitChargeEnergy_two_le_upperJump
    Q hXi rho hoff hfaithful n
  linarith

/-- Existence of one compact-open upper-semicontinuous scalar majorizing every canonical Wold
charge bubble and anchored nonpositively at `xi`. -/
def XiWoldOrbitChargeEnergyCompactOpenUpperDescent : Prop :=
  ∃ Q : (ℂ → ℂ) → ℝ,
    CompactOpenSequentialUpperReporter Q ∧
      Q xi ≤ 0 ∧
      ∀ (rho : XiDivisorSupport) (n : ℕ),
        xiReflectedWoldOrbitChargeEnergy rho ≤ Q (xiSourceMatchedBubble rho n)

/-- **T2 upper-semicontinuous route kill.** A compact-open sequentially upper-semicontinuous
lower-faithful Wold-charge descent exists exactly under RH. -/
theorem xiWoldOrbitChargeEnergyCompactOpenUpperDescent_iff_riemannHypothesis :
    XiWoldOrbitChargeEnergyCompactOpenUpperDescent ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨Q, hupper, hXi, hfaithful⟩
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    by_contra hoff
    exact offLineXiDivisor_no_compactOpenUpper_woldOrbitChargeEnergyMajorant
      Q hXi rho hoff (hfaithful rho) hupper
  · intro hRH
    refine ⟨fun _ => 0, ?_, by norm_num, ?_⟩
    · intro F f hF ε hε
      exact Filter.Eventually.of_forall (fun _ => by linarith)
    · intro rho n
      rw [xiReflectedWoldOrbitChargeEnergy_eq_zero_of_re_eq_half rho
        (xi_divisor_support_re_eq_half_of_rh hRH rho)]

end

end RHTower
