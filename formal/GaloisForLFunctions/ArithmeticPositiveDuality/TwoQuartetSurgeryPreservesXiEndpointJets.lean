import GaloisForLFunctions.ArithmeticPositiveDuality.TwoQuartetsPreserveTheEndpointJet
import GaloisForLFunctions.RHTower.Reflection
import Mathlib.Analysis.Calculus.DSlope

/-!
# Entire two-quartet surgery with unchanged xi endpoint jets

Distinct critical-line donor zeros remove the poles of the two-quartet
multiplier. The resulting entire function retains reflection, reality, and
both first endpoint jets of `xi`, while acquiring two off-line quartets.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Distinct zeros can each be divided out once while retaining an entire quotient. -/
theorem entire_divide_finite_zeros (S : Finset ℂ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hz : ∀ a ∈ S, f a = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s, f s = g s * ∏ a ∈ S, (s - a) := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨f, hf, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨g, hg, he⟩ := ih (fun b hb => hz b (Finset.mem_insert_of_mem hb))
    have hp : (∏ b ∈ S, (a - b)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (by
      intro b hb
      exact sub_ne_zero.mpr (fun hab => ha (hab.symm ▸ hb)))
    have hga : g a = 0 := by
      have h := he a
      rw [hz a (Finset.mem_insert_self _ _)] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hp
    refine ⟨dslope g a, differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hg.differentiableOn), ?_⟩
    intro s
    have hd := sub_smul_dslope g a s
    rw [hga, sub_zero, smul_eq_mul] at hd
    rw [he, Finset.prod_insert ha, ← hd]
    ring

private def donorRoot (γ : Fin 4 → ℝ) (i : Fin 4 × Bool) : ℂ :=
  if i.2 then 1 / 2 + (γ i.1 : ℂ) * I else 1 / 2 - (γ i.1 : ℂ) * I

private theorem donorRoot_injective {γ : Fin 4 → ℝ}
    (hp : ∀ i, 0 < γ i) (hi : Function.Injective γ) : Function.Injective (donorRoot γ) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ he
  have him := congrArg Complex.im he
  cases b <;> cases c <;> norm_num [donorRoot] at him
  · exact Prod.ext (hi (by linarith only [him])) rfl
  · linarith only [hp i, hp j, him]
  · linarith only [hp i, hp j, him]
  · exact Prod.ext (hi him) rfl

private theorem donorRoot_zero {γ : Fin 4 → ℝ}
    (hz : ∀ i, riemannZeta (1 / 2 + (γ i : ℂ) * I) = 0) (i : Fin 4 × Bool) :
    RHTower.xi (donorRoot γ i) = 0 := by
  have hxi : RHTower.xi (1 / 2 + (γ i.1 : ℂ) * I) = 0 :=
    (RHTower.xi_eq_zero_iff (by norm_num) (by
      intro he
      have hre := congrArg Complex.re he
      norm_num at hre)).mpr (hz i.1)
  rcases i with ⟨i, b⟩
  cases b
  · have he : (1 / 2 - (γ i : ℂ) * I : ℂ) =
        starRingEnd ℂ (1 / 2 + (γ i : ℂ) * I) := by
      simp only [map_add, map_div₀, map_one, map_ofNat, map_mul,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    change RHTower.xi (1 / 2 - (γ i : ℂ) * I) = 0
    rw [he, RHTower.xi_conj, hxi, map_zero]
  · exact hxi

/-- Entire functions agreeing off the critical line agree everywhere. -/
theorem entire_eq_of_off_line {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (he : ∀ s : ℂ, s.re ≠ 1 / 2 → f s = g s) : f = g := by
  have hev : f =ᶠ[𝓝 (2 : ℂ)] g := by
    filter_upwards [RHTower.isOpen_rightHalf.mem_nhds RHTower.two_mem_rightHalf] with s hs
    exact he s (ne_of_gt hs)
  have h := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hg.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ 2) hev
  exact funext (fun s => h (Set.mem_univ s))

private theorem exists_entire_donor_quotient {γ₁ γ₂ γ₃ γ₄ : ℝ}
    (h₁ : 1 < γ₁) (h₁₂ : γ₁ < γ₂) (h₂₃ : γ₂ < γ₃) (h₃₄ : γ₃ < γ₄)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0)
    (hz₃ : riemannZeta (1 / 2 + (γ₃ : ℂ) * I) = 0)
    (hz₄ : riemannZeta (1 / 2 + (γ₄ : ℂ) * I) = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s,
      RHTower.xi s = g s * (zeroRelocationDen γ₁ γ₂ s * zeroRelocationDen γ₃ γ₄ s) := by
  classical
  let γ : Fin 4 → ℝ := ![γ₁, γ₂, γ₃, γ₄]
  have hp : ∀ i, 0 < γ i := by
    intro i
    fin_cases i <;> dsimp [γ] <;> linarith only [h₁, h₁₂, h₂₃, h₃₄]
  have hi : Function.Injective γ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [γ] at hij ⊢ <;>
      linarith only [h₁₂, h₂₃, h₃₄, hij]
  have hz : ∀ i, riemannZeta (1 / 2 + (γ i : ℂ) * I) = 0 := by
    intro i
    fin_cases i
    · exact hz₁
    · exact hz₂
    · exact hz₃
    · exact hz₄
  let S := Finset.univ.image (donorRoot γ)
  obtain ⟨g, hg, he⟩ := entire_divide_finite_zeros S RHTower.xi_differentiable (by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact donorRoot_zero hz i)
  refine ⟨g, hg, fun s => ?_⟩
  have hD : (∏ a ∈ S, (s - a)) =
      zeroRelocationDen γ₁ γ₂ s * zeroRelocationDen γ₃ γ₄ s := by
    dsimp only [S]
    rw [Finset.prod_image (donorRoot_injective hp hi).injOn, Fintype.prod_prod_type,
      Fin.prod_univ_four]
    simp [donorRoot, γ, zeroRelocationDen]
    ring
  simpa only [hD] using he s

/-- Cancelling eight distinct actual donor zeros gives an entire two-quartet surgery. -/
theorem exists_entire_two_quartet_surgery {γ₁ γ₂ γ₃ γ₄ : ℝ}
    (h₁ : 1 < γ₁) (h₁₂ : γ₁ < γ₂) (h₂₃ : γ₂ < γ₃) (h₃₄ : γ₃ < γ₄)
    (hz₁ : riemannZeta (1 / 2 + (γ₁ : ℂ) * I) = 0)
    (hz₂ : riemannZeta (1 / 2 + (γ₂ : ℂ) * I) = 0)
    (hz₃ : riemannZeta (1 / 2 + (γ₃ : ℂ) * I) = 0)
    (hz₄ : riemannZeta (1 / 2 + (γ₄ : ℂ) * I) = 0) (u v : ℝ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, s.re ≠ 1 / 2 →
        F s = RHTower.xi s * twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)) := by
  obtain ⟨g, hg, he⟩ := exists_entire_donor_quotient h₁ h₁₂ h₂₃ h₃₄ hz₁ hz₂ hz₃ hz₄
  let F := fun s => g s * (zeroRelocationNum (quartetParameterTarget u) s *
    zeroRelocationNum (quartetParameterTarget v) s)
  have hF : Differentiable ℂ F := by
    apply hg.mul
    unfold zeroRelocationNum
    fun_prop
  have hEq (s : ℂ) (hs : s.re ≠ 1 / 2) :
      F s = RHTower.xi s * twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s := by
    have hd₁ := zeroRelocationDen_ne_zero_of_re_ne_half γ₁ γ₂ hs
    have hd₂ := zeroRelocationDen_ne_zero_of_re_ne_half γ₃ γ₄ hs
    rw [he s]
    dsimp only [F, twoQuartetFactor, zeroRelocationFactor]
    field_simp [hd₁, hd₂]
  refine ⟨F, hF, hEq, ?_, ?_⟩
  · have hsym : (fun s => F (1 - s)) = F := entire_eq_of_off_line
        (hF.comp (show Differentiable ℂ (fun s : ℂ => 1 - s) by fun_prop)) hF (by
      intro s hs
      have hs' : (1 - s).re ≠ 1 / 2 := by
        simp only [Complex.sub_re, Complex.one_re]
        intro h
        apply hs
        linarith only [h]
      rw [hEq (1 - s) hs', hEq s hs, RHTower.xi_one_sub, twoQuartetFactor_one_sub])
    exact congrFun hsym
  · have hsym : (fun s => starRingEnd ℂ (F (starRingEnd ℂ s))) = F :=
        entire_eq_of_off_line (RHTower.differentiable_conj_reflect hF) hF (by
      intro s hs
      rw [hEq (starRingEnd ℂ s) (by simpa only [Complex.conj_re] using hs),
        hEq s hs, RHTower.xi_conj, twoQuartetFactor_conj, map_mul,
        Complex.conj_conj, Complex.conj_conj])
    intro s
    have h := congrFun hsym (starRingEnd ℂ s)
    simpa only [Complex.conj_conj] using h.symm

private theorem surgery_endpoint_jet {F : ℂ → ℂ} {u v γ₁ γ₂ γ₃ γ₄ : ℝ}
    (he : ∀ s : ℂ, s.re ≠ 1 / 2 →
      F s = RHTower.xi s * twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s)
    {z : ℂ} (hz : z.re ≠ 1 / 2)
    (hval : twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ z = 1)
    (hjet : HasDerivAt (twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄) 0 z) :
    F z = RHTower.xi z ∧ deriv F z = deriv RHTower.xi z := by
  have hev : F =ᶠ[𝓝 z] fun s => RHTower.xi s * twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s := by
    filter_upwards [(isOpen_ne_fun Complex.continuous_re continuous_const).mem_nhds hz] with s hs
    exact he s hs
  constructor
  · simpa only [hval, mul_one] using hev.self_of_nhds
  · have h := ((RHTower.xi_differentiable z).hasDerivAt.mul hjet).congr_of_eventuallyEq hev
    simpa only [hval, mul_one, mul_zero, add_zero] using h.deriv

/-- Entire finite surgery preserves both endpoint jets of xi and plants two off-line quartets. -/
theorem exists_entire_xi_surgery_preserving_endpoint_jets :
    ∃ (F : ℂ → ℂ) (u v : ℝ), Differentiable ℂ F ∧ 5 / 16 < v ∧ v < u ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)) ∧
      F 0 = RHTower.xi 0 ∧ F 1 = RHTower.xi 1 ∧
      deriv F 0 = deriv RHTower.xi 0 ∧ deriv F 1 = deriv RHTower.xi 1 ∧
      F (quartetParameterTarget u) = 0 ∧ F (quartetParameterTarget v) = 0 ∧
      ∃ γ₁ γ₂ γ₃ γ₄ : ℝ, ∀ s : ℂ, s.re ≠ 1 / 2 →
        F s = RHTower.xi s * twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ s := by
  obtain ⟨γ₁, γ₂, γ₃, γ₄, u, v, h₁, h₁₂, h₂₃, h₃₄, hz₁, hz₂, hz₃, hz₄,
    hv, hvu, hval0, hval1, hjet0, hjet1⟩ := exists_actual_two_quartet_endpoint_jet
  obtain ⟨F, hF, he, hreflect, hconj⟩ :=
    exists_entire_two_quartet_surgery h₁ h₁₂ h₂₃ h₃₄ hz₁ hz₂ hz₃ hz₄ u v
  obtain ⟨hF0, hD0⟩ := surgery_endpoint_jet he (z := 0) (by norm_num) hval0 hjet0
  obtain ⟨hF1, hD1⟩ := surgery_endpoint_jet he (z := 1) (by norm_num) hval1 hjet1
  have hzu : twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ (quartetParameterTarget u) = 0 :=
    (twoQuartetFactor_eq_zero_iff (by norm_num) u v γ₁ γ₂ γ₃ γ₄).mpr (Or.inl rfl)
  have hzv : twoQuartetFactor u v γ₁ γ₂ γ₃ γ₄ (quartetParameterTarget v) = 0 :=
    (twoQuartetFactor_eq_zero_iff (by norm_num) u v γ₁ γ₂ γ₃ γ₄).mpr
      (Or.inr (Or.inr (Or.inl rfl)))
  refine ⟨F, u, v, hF, hv, hvu, hreflect, hconj, hF0, hF1, hD0, hD1, ?_, ?_,
    γ₁, γ₂, γ₃, γ₄, he⟩
  · rw [he _ (by norm_num), hzu, mul_zero]
  · rw [he _ (by norm_num), hzv, mul_zero]

end GaloisForLFunctions.ArithmeticPositiveDuality

#print axioms GaloisForLFunctions.ArithmeticPositiveDuality.exists_entire_xi_surgery_preserving_endpoint_jets
