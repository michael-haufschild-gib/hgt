import GaloisForLFunctions.HTGeometry.EllipticGammaLogNormalConvergence
import GaloisForLFunctions.HTGeometry.EllipticGammaSourceFaceFracture

/-!
# Normally convergent zero-nome boundary of the elliptic-Gamma log kernel

Finite zero-nome rectangles collapse to one trigonometric Pochhammer row.  Normal convergence of
the full logarithmic double kernel lets this collapse pass to the infinite source: every positive
column and the entire forward face vanish, leaving one normally convergent boundary series.  Its
multiplicative source increment is exactly the surviving Pochhammer logarithmic atom.
-/

open Complex Set Filter

namespace GaloisForLFunctions

noncomputable section

/-- Infinite logarithmic kernel of the one-dimensional trigonometric boundary source. -/
def trigonometricBoundaryLogKernel (p x : ℂ) : ℂ :=
  ∑' j : ℕ, ellipticGammaLogAtom (p ^ j * x)

/-- **Infinite zero-nome face law.**  The elliptic-Gamma logarithmic double kernel collapses
exactly to the trigonometric boundary kernel when either second nome is zero. -/
theorem ellipticGammaLogKernel_zero_nome_eq_trigonometricBoundary
    {p : ℂ} (hp : ‖p‖ < 1) (x : ℂ) :
    ellipticGammaLogKernel p 0 x = trigonometricBoundaryLogKernel p x := by
  rw [ellipticGammaLogKernel_eq_tsum_fibers hp (by norm_num)]
  rw [tsum_eq_single 0]
  · unfold trigonometricBoundaryLogKernel
    apply tsum_congr
    intro j
    simp [ellipticGammaLogSummand, ellipticGammaForwardArgument_zero_nome,
      ellipticGammaBackwardArgument_zero_nome_zero, ellipticGammaLogAtom]
  · intro k hk
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp [ellipticGammaLogSummand, ellipticGammaForwardArgument_zero_nome,
      ellipticGammaBackwardArgument_zero_nome_succ, ellipticGammaLogAtom]

/-- The zero-nome double summands converge uniformly on every closed annulus to the surviving
trigonometric boundary kernel. -/
theorem hasSumUniformlyOn_ellipticGammaLogKernel_zero_nome_boundary
    {p : ℂ} {r R : ℝ} (hp : ‖p‖ < 1) (hr : 0 < r) :
    HasSumUniformlyOn
      (fun jk : ℕ × ℕ => fun x : ℂ => ellipticGammaLogSummand p 0 x jk.1 jk.2)
      (trigonometricBoundaryLogKernel p)
      {x : ℂ | r ≤ ‖x‖ ∧ ‖x‖ ≤ R} := by
  have h := hasSumUniformlyOn_ellipticGammaLogKernel_annulus
    (p := p) (q := (0 : ℂ)) (R := R) hp (by norm_num) hr
  convert h using 1
  funext x
  exact (ellipticGammaLogKernel_zero_nome_eq_trigonometricBoundary hp x).symm

/-- At zero nome the theta boundary is the negative first Pochhammer atom. -/
theorem ellipticThetaLogKernel_zero_nome (x : ℂ) :
    ellipticThetaLogKernel 0 x = -ellipticGammaLogAtom x := by
  rw [ellipticThetaLogKernel, tsum_eq_single 0]
  · simp [ellipticThetaLogSummand, ellipticGammaLogAtom]
  · intro k hk
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp [ellipticThetaLogSummand, ellipticGammaLogAtom]

/-- **Surviving infinite source law.**  Multiplication by the remaining nome changes the normal
boundary kernel by exactly the logarithmic atom of the first trigonometric factor. -/
theorem trigonometricBoundaryLogKernel_mul_sub
    {p x : ℂ} (hp0 : p ≠ 0) (hx : x ≠ 0) (hp : ‖p‖ < 1) :
    trigonometricBoundaryLogKernel p (p * x) -
        trigonometricBoundaryLogKernel p x =
      -ellipticGammaLogAtom x := by
  rw [← ellipticGammaLogKernel_zero_nome_eq_trigonometricBoundary hp,
    ← ellipticGammaLogKernel_zero_nome_eq_trigonometricBoundary hp,
    ← ellipticThetaLogKernel_zero_nome]
  exact ellipticGammaLogKernel_mul_p_sub hp0 hx hp (by norm_num)

end

end GaloisForLFunctions
