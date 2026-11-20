import GaloisForLFunctions.goldbach.LiLiu.Boundary.KernelSymmetry

/-! # Continuity of the boundary kernel and holomorphy of its columns -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Set Finset
open scoped ComplexConjugate Classical
noncomputable section

theorem odd_ne_principal {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.Odd) : χ ≠ 1 := by
  rintro rfl
  apply h.not_even
  change (1 : DirichletCharacter ℂ N) (-1) = 1
  exact MulChar.one_apply (isUnit_neg.mpr isUnit_one)

private theorem gamma_differentiable_pos {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Gamma z :=
  differentiableAt_Gamma z (fun k he => by
    rw [he,Complex.neg_re,Complex.natCast_re] at hz
    linarith only [hz,Nat.cast_nonneg (α := ℝ) k])

theorem signedBetaGammaFactor_differentiableAt {s : ℂ} (hs : s.re ∈ Ioo (0:ℝ) (3/2)) :
    DifferentiableAt ℂ signedBetaGammaFactor s := by
  have hu : 0 < ((3/2-s)/2 : ℂ).re := by norm_num; linarith only [hs.2]
  have hv : 0 < ((3/2+s)/2 : ℂ).re := by norm_num; linarith only [hs.1]
  exact ((gamma_differentiable_pos hu).comp s (by fun_prop)).div
    ((gamma_differentiable_pos hv).comp s (by fun_prop)) (Gamma_ne_zero_of_re_pos hv)

theorem betaModel_differentiableAt {N : ℕ} (hN : 0 < N) {p : ℂ × ℂ}
    (hs : p.1.re ∈ Ioo (0:ℝ) (3/2)) (hz : p.2.re ∈ Ioo (0:ℝ) (3/2)) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ => betaModel N q.1 q.2) p := by
  have hW : DifferentiableAt ℂ (fun q : ℂ × ℂ => q.1+q.2) p := by fun_prop
  have hw : 0 < (p.1+p.2).re := add_pos hs.1 hz.1
  have hp : ((Real.pi/N:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (div_pos Real.pi_pos (Nat.cast_pos.mpr hN)).ne'
  have hne : 1-(p.1+p.2) ≠ 1 := fun he => by
    have he' := congrArg Complex.re he
    simp only [sub_re,one_re] at he'
    linarith only [hw,he']
  exact ((((((differentiableAt_const _).mul (hW.const_cpow (Or.inl hp))).mul
    ((densityEuler_differentiableAt N hw).comp p hW)).mul
    ((differentiableAt_riemannZeta hne).comp p ((differentiableAt_const _).sub hW))).mul
    ((signedBetaGammaFactor_differentiableAt hs).comp p (by fun_prop))).mul
    ((signedBetaGammaFactor_differentiableAt hz).comp p (by fun_prop))

private theorem denom_ne {s : ℂ} (hs : 0 < s.re) : 1+s ≠ 0 := by
  intro he
  have H := congrArg Complex.re he
  simp only [add_re,one_re,zero_re] at H
  linarith only [hs,H]

/-- Conjugating the input coordinate preserves joint continuity. -/
theorem boundaryKernel_continuousAt {n : ℕ} (h : modulusGRH (n+1)) {p : ℂ × ℂ}
    (hs : p.1.re ∈ Ioo (0:ℝ) (3/2)) (hz : p.2.re ∈ Ioo (0:ℝ) (3/2)) :
    ContinuousAt (fun q : ℂ × ℂ => boundaryKernel (n+1) q.1 q.2) p := by
  let f (q : ℂ × ℂ) := (q.1,conj q.2)
  have hf : Continuous f := continuous_fst.prodMk (continuous_conj.comp continuous_snd)
  have hW : Continuous (fun q : ℂ × ℂ => q.1+conj q.2) := continuous_fst.add (continuous_conj.comp continuous_snd)
  have hw : 0 < (p.1+conj p.2).re := add_pos hs.1 hz.1
  have hK := (betaModel_differentiableAt (N := n+1) (Nat.succ_pos n)
    (p := f p) hs hz).continuousAt.comp hf.continuousAt
  have hP : ContinuousAt (fun q : ℂ × ℂ => characterKernel (n+1) q.1 q.2) p := by
    apply continuousAt_const.mul
    apply continuousAt_finsetSum
    intro χ hχ
    have hn := odd_ne_principal (mem_filter.mp hχ).2
    exact (((characterFeature_analyticAt h hn hs.1).continuousAt.comp continuous_fst.continuousAt).mul
      (continuous_conj.continuousAt.comp ((characterFeature_analyticAt h hn hz.1).continuousAt.comp
        continuous_snd.continuousAt)))
  exact ((hP.sub ((diagonalSeries_differentiableAt (n+1) hw).continuousAt.comp hW.continuousAt)).sub hK).div
    (by fun_prop) (mul_ne_zero (denom_ne hs.1) (denom_ne (s := conj p.2) hz.1))

theorem boundaryKernel_column_differentiableAt {n : ℕ} (h : modulusGRH (n+1)) {s z : ℂ}
    (hs : s.re ∈ Ioo (0:ℝ) (3/2)) (hz : z.re ∈ Ioo (0:ℝ) (3/2)) :
    DifferentiableAt ℂ (fun u => boundaryKernel (n+1) u z) s := by
  have hP : DifferentiableAt ℂ (fun u => characterKernel (n+1) u z) s := by
    apply (differentiableAt_const _).mul
    apply DifferentiableAt.fun_sum
    intro χ hχ
    exact (characterFeature_analyticAt h (odd_ne_principal (mem_filter.mp hχ).2) hs.1).differentiableAt.mul_const _
  have hw : 0 < (s+conj z).re := add_pos hs.1 hz.1
  have hK := (betaModel_differentiableAt (Nat.succ_pos n) (p := (s,conj z)) hs hz).comp s
    (f := fun u : ℂ => (u,conj z)) (by fun_prop)
  exact ((hP.sub ((diagonalSeries_differentiableAt (n+1) hw).comp s (by fun_prop))).sub hK).div
    (by fun_prop) (mul_ne_zero (denom_ne hs.1) (denom_ne (s := conj z) hz.1))

#print axioms boundaryKernel_column_differentiableAt
end
end GaloisForLFunctions.Goldbach.LiLiu
