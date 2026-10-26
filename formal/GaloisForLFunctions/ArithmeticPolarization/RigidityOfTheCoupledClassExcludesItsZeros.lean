import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ExteriorAndHeightCoupledQuartetContractions
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.KernelCountsAreBlindToComplexQuartets
import GaloisForLFunctions.StripBochnerWeilForcing.CollectivePoleRepulsion
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Rigidity of the coupled class excludes its zeros

The positive completion of the elliptic sector at ordinate `γ` is the height-coupled lift
`ζ_γ(s) = ζ(s)² ζ(s + iγ) ζ(s − iγ)`, a member of `HeightCoupledSystem 2 1 1 γ`
(`zeta_mem_heightCoupledClass`). The `κ = 1` class `CompletedPositiveSystem 1 d` is `ℝ^× · ζ`
(StripBochnerWeilForcing); is the coupled class at `γ` equally rigid?

* **Rigidity at `γ` excludes every off-line zero at ordinate `γ`** (`xi_ne_zero_of_rigid`). A
  zero `½ + a + iγ` of `ξ` (`0 < a < ½`) contracts inside the coupled class at zero pole cost (ACP
  `contractComplexQuartet_heightCoupled`) and produces a member whose completion vanishes at `½`
  to order four more than that of `ζ_γ`; a proportional member would have the same order.
* **Rigidity at every ordinate is RH** (`riemannHypothesis_of_forall_rigid`).

So the rigidity question for the coupled class is a forcing statement: a Hamburger-type theorem
for `HeightCoupledSystem 2 1 1 γ` whose proof does not use the zeros of `ζ` at ordinate `γ` would
exclude them.
-/

open Complex Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing

/-- **Rigidity of the coupled class at `γ`**: every member of `HeightCoupledSystem 2 1 1 γ` is a
nonzero real multiple of `ζ_γ` on `Re s > 1`. -/
def CoupledRigid (γ : ℝ) : Prop :=
  ∀ F Λ : ℂ → ℂ, HeightCoupledSystem 2 1 1 γ F Λ →
    ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s

/-- `ζ_γ` belongs to the coupled class at every ordinate. -/
theorem zeta_mem_heightCoupledClass (γ : ℝ) :
    HeightCoupledSystem 2 1 1 γ (heightCoupledF riemannZeta γ)
      (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) :=
  ArithmeticCorrespondencePositivity.CompletedPositiveSystem.heightCouple
    completedPositiveSystem_riemannZeta γ

/-- **Rigidity at `γ` excludes the off-line zeros at ordinate `γ`.** -/
theorem xi_ne_zero_of_rigid {γ a : ℝ} (hrig : CoupledRigid γ) (hγ : γ ≠ 0) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) : RHTower.xi (1 / 2 + a + γ * I) ≠ 0 := by
  intro hxi
  have hS := completedPositiveSystem_riemannZeta
  have hq : (fun s => 2 * RHTower.xi s) (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 := by
    simp only [hxi, mul_zero]
  obtain ⟨Λc, hHCc, hord⟩ :=
    ArithmeticCorrespondencePositivity.CompletedPositiveSystem.contractComplexQuartet_heightCoupled
      hS ha0 ha1 hγ hq
  obtain ⟨K, hK0, hK⟩ := hrig _ _ hHCc
  have hHC0 := zeta_mem_heightCoupledClass γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ
  -- the two completions agree up to `K` on `Re s > 1`
  have hagree : ∀ s : ℂ, 1 < s.re → Λc s = (K : ℂ) * Λγ s := by
    intro s hs
    rw [hHCc.completed_eq s hs, hHC0.completed_eq s hs, hK s hs]
    ring
  -- hence everywhere
  have heq : EqOn Λc (fun s => (K : ℂ) * Λγ s) univ := by
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact hHCc.analyticOnNhd_univ.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const.mul hHC0.analyticOnNhd_univ)
      isPreconnected_univ (mem_univ (2 : ℂ))
      (Filter.eventually_of_mem (hU.mem_nhds (by norm_num)) fun s hs => hagree s hs)
  have hfun : Λc = fun s => (K : ℂ) * Λγ s := funext fun s => heq (mem_univ s)
  -- compare vanishing orders at `½`
  have hconst : analyticOrderAt (fun _ : ℂ => (K : ℂ)) (1 / 2 : ℂ) = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by exact_mod_cast hK0)
  have hordK : analyticOrderAt Λc (1 / 2) = analyticOrderAt Λγ (1 / 2) := by
    rw [hfun, show (fun s => (K : ℂ) * Λγ s) = (fun _ : ℂ => (K : ℂ)) * Λγ from rfl,
      analyticOrderAt_mul analyticAt_const (hHC0.entire_Λ.analyticAt _), hconst, zero_add]
  have h0 :=
    ArithmeticCorrespondencePositivity.CompletedPositiveSystem.orderAt_heightCoupledΛ_real hS γ (1 / 2)
  have hhalf : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
  rw [hhalf] at h0
  rw [hordK] at hord
  have : (analyticOrderAt Λγ (1 / 2)).toNat = (analyticOrderAt Λγ (1 / 2)).toNat + 4 := by
    rw [h0] at hord ⊢; omega
  omega

/-- **Rigidity at every ordinate is RH.** -/
theorem riemannHypothesis_of_forall_rigid (h : ∀ γ : ℝ, γ ≠ 0 → CoupledRigid γ) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs1 hs2 hz
  have him : s.im ≠ 0 := zeta_strip_zero_im_ne_zero hz (by linarith) hs2
  have hs : s = 1 / 2 + ((s.re - 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hne1 : s ≠ 1 := by
    intro h1; rw [h1] at hs2; simp at hs2
  have hxi : RHTower.xi s = 0 :=
    (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith) hne1).mpr hz
  rw [hs] at hxi
  exact xi_ne_zero_of_rigid (h _ him) him (by linarith) (by linarith) hxi

end GaloisForLFunctions.ArithmeticPolarization
