import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import GaloisForLFunctions.RHTower.DirichletLUniformPartialFraction
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LocalZeroCount

/-! The fibers of the primitive and principal zero-copy maps have the analytic multiplicities. -/

open Complex Set
open RHTower GaloisForLFunctions.EntireZeroDivisor
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

private theorem zeroCopy_count_eq_order {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f univ)
    {a : ℂ} (ha : f a ≠ 0) (w : ℂ) :
    {q : ZeroCopy f | zeroCopyPoint f q = w}.ncard = analyticOrderNatAt f w := by
  have htop : analyticOrderAt f w ≠ ⊤ := fun h =>
    ha (congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero w
      (fun v => hf v (mem_univ v))).mp h) a)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [ncard_zeroCopy_fiber, divisor_univ_eq_analyticOrder hf, analyticOrderNatAt, ← hn]
  simp

theorem primitive_zero_copy_count {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {ρ : ℂ} (hρ : 0 < ρ.re) :
    {q : LZero χ | q.point = ρ}.ncard = analyticOrderNatAt χ.LFunction ρ := by
  have hs : (ρ - 2 + 2 : ℂ) = ρ := sub_add_cancel _ _
  have htranslate : AnalyticAt ℂ (fun z : ℂ => z + 2) (ρ - 2) := analyticAt_id.add analyticAt_const
  have hderiv : deriv (fun z : ℂ => z + 2) (ρ - 2) ≠ 0 := by simp
  have hord : analyticOrderAt (shiftedL χ) (ρ - 2) = analyticOrderAt χ.LFunction ρ := by
    rw [analyticOrderAt_shiftedL_eq hχ (by rwa [hs])]
    change analyticOrderAt (χ.LFunction ∘ fun z : ℂ => z + 2) (ρ - 2) = _
    rw [analyticOrderAt_comp_of_deriv_ne_zero htranslate hderiv, hs]
  have hset : {q : LZero χ | q.point = ρ} =
      {q : LZero χ | zeroCopyPoint (shiftedL χ) q = ρ - 2} := by
    ext q
    exact eq_sub_iff_add_eq.symm
  rw [hset, zeroCopy_count_eq_order (analyticOnNhd_shiftedL hχ) (shiftedL_zero_ne_zero hχ)]
  simp only [analyticOrderNatAt, hord]

theorem primitive_zero_copy_exists {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {ρ : ℂ} (hρ : 0 < ρ.re) (hz : χ.LFunction ρ = 0) :
    ∃ q : LZero χ, q.point = ρ := by
  have hn := RHTower.one_le_analyticOrderNatAt_LFunction hχ hz
  rw [← primitive_zero_copy_count hχ hρ] at hn
  exact Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hn)

theorem finite_primitive_height {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (T : ℝ) : {q : LZero χ | |q.point.im| ≤ T}.Finite := by
  refine (locallyFinite_zeroCopyPoint (analyticOnNhd_shiftedL hχ) (2 + T)).subset ?_
  intro q hq
  let ρ := LZero.point (χ := χ) q
  change |ρ.im| ≤ T at hq
  let w := zeroCopyPoint (shiftedL χ) q
  have hw : w = ρ - 2 := by simp [w, ρ, LZero.point]
  have hρ : 0 < ρ.re ∧ ρ.re < 1 := zero_re_mem hχ hp q
  have hreal : |w.re| ≤ 2 := by
    rw [hw, sub_re, show (2 : ℂ).re = 2 by norm_num, abs_le]
    exact ⟨by linarith only [hρ.1], by linarith only [hρ.2]⟩
  have him : w.im = ρ.im := by simp [hw]
  exact (norm_le_abs_re_add_abs_im w).trans (add_le_add hreal (by rwa [him]))

theorem xi_zero_copy_count {ρ : ℂ} (hρ : ρ.re ∈ Ioo 0 1) :
    {q : XiZeroCopy | (q.1 : ℂ) = ρ}.ncard = analyticOrderNatAt riemannZeta ρ := by
  change {q : ZeroCopy xi | zeroCopyPoint xi q = ρ}.ncard = _
  rw [zeroCopy_count_eq_order xi_analyticOnNhd_univ xi_two_ne_zero]
  simp only [analyticOrderNatAt, xi_analyticOrderAt_eq_riemannZeta_of_mem_strip hρ]

theorem xi_zero_copy_exists {ρ : ℂ} (hρ : ρ.re ∈ Ioo 0 1) (hz : riemannZeta ρ = 0) :
    ∃ q : XiZeroCopy, (q.1 : ℂ) = ρ := by
  have h₁ : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ; exact (lt_irrefl 1 hρ.2)
  have hx := (xi_eq_zero_iff hρ.1 h₁).mpr hz
  have htop : analyticOrderAt xi ρ ≠ ⊤ := fun h => xi_two_ne_zero
    (congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
      (fun v => xi_analyticOnNhd_univ v (mem_univ v))).mp h) 2)
  have hn : analyticOrderNatAt xi ρ ≠ 0 := fun h =>
    ((xi_differentiable.analyticAt ρ).analyticOrderAt_ne_zero.mpr hx) (by
      have hc := Nat.cast_analyticOrderNatAt htop
      rw [h, Nat.cast_zero] at hc
      exact hc.symm)
  change {q : ZeroCopy xi | zeroCopyPoint xi q = ρ}.Nonempty
  apply Set.nonempty_of_ncard_ne_zero
  rwa [zeroCopy_count_eq_order xi_analyticOnNhd_univ xi_two_ne_zero]

end QH.PrimeProgressions
