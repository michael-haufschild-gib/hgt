import GaloisForLFunctions.HTGeometry.EllipticGammaLogKernel
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Normal convergence of the elliptic-gamma logarithmic kernel

The double logarithmic kernel has an explicit geometric Weierstrass majorant on every closed
annulus in the multiplicative variable.  Consequently its defining series converges uniformly on
each such annulus.  This is the normal-convergence input required to realize the pointwise kernel
as a meromorphic function after the explicit finite-term polar divisor is removed.
-/

open Complex Set Filter

namespace GaloisForLFunctions

noncomputable section

/-- Geometric annular majorant for the numerator-side arguments. -/
def ellipticGammaForwardMajorant (p q : ℂ) (r : ℝ) (jk : ℕ × ℕ) : ℝ :=
  ‖p‖ ^ (jk.1 + 1) * ‖q‖ ^ (jk.2 + 1) / r

/-- Geometric annular majorant for the denominator-side arguments. -/
def ellipticGammaBackwardMajorant (p q : ℂ) (R : ℝ) (jk : ℕ × ℕ) : ℝ :=
  ‖p‖ ^ jk.1 * ‖q‖ ^ jk.2 * R

theorem summable_ellipticGammaForwardMajorant {p q : ℂ} {r : ℝ}
    (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Summable (ellipticGammaForwardMajorant p q r) := by
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hpGeom : Summable (fun j : ℕ => ‖p‖ ^ (j + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hp0 hp).mul_left ‖p‖
  have hqGeom : Summable (fun k : ℕ => ‖q‖ ^ (k + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hq0 hq).mul_left ‖q‖
  exact (hpGeom.mul_of_nonneg hqGeom (fun _ => pow_nonneg hp0 _)
    (fun _ => pow_nonneg hq0 _)).mul_right r⁻¹ |>.congr (fun jk => by
      simp [ellipticGammaForwardMajorant, div_eq_mul_inv])

theorem summable_ellipticGammaBackwardMajorant {p q : ℂ} {R : ℝ}
    (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    Summable (ellipticGammaBackwardMajorant p q R) := by
  have hp0 : 0 ≤ ‖p‖ := norm_nonneg p
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  exact ((summable_geometric_of_lt_one hp0 hp).mul_of_nonneg
    (summable_geometric_of_lt_one hq0 hq) (fun _ => pow_nonneg hp0 _)
      (fun _ => pow_nonneg hq0 _)).mul_right R

theorem norm_ellipticGammaForwardArgument_le_majorant
    {p q x : ℂ} {r : ℝ} (hr : 0 < r) (hx : r ≤ ‖x‖) (j k : ℕ) :
    ‖ellipticGammaForwardArgument p q x j k‖ ≤
      ellipticGammaForwardMajorant p q r (j, k) := by
  rw [ellipticGammaForwardArgument, norm_div]
  simp only [norm_mul, norm_pow, ellipticGammaForwardMajorant]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact hr
  · exact hx

theorem norm_ellipticGammaBackwardArgument_le_majorant
    {p q x : ℂ} {R : ℝ} (hx : ‖x‖ ≤ R) (j k : ℕ) :
    ‖ellipticGammaBackwardArgument p q x j k‖ ≤
      ellipticGammaBackwardMajorant p q R (j, k) := by
  simp only [ellipticGammaBackwardArgument, norm_mul, norm_pow,
    ellipticGammaBackwardMajorant]
  gcongr

/-- **Uniform annular convergence.** For nomes in the open unit disc, the double logarithmic
kernel converges uniformly on every closed annulus `r ≤ ‖x‖ ≤ R` with `r > 0`. -/
theorem hasSumUniformlyOn_ellipticGammaLogKernel_annulus
    {p q : ℂ} {r R : ℝ} (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) (hr : 0 < r) :
    HasSumUniformlyOn
      (fun jk : ℕ × ℕ => fun x : ℂ => ellipticGammaLogSummand p q x jk.1 jk.2)
      (ellipticGammaLogKernel p q) {x : ℂ | r ≤ ‖x‖ ∧ ‖x‖ ≤ R} := by
  let fM := ellipticGammaForwardMajorant p q r
  let bM := ellipticGammaBackwardMajorant p q R
  let u : ℕ × ℕ → ℝ := fun jk => 2 * (fM jk + bM jk)
  have hfM : Summable fM := summable_ellipticGammaForwardMajorant hp hq
  have hbM : Summable bM := summable_ellipticGammaBackwardMajorant hp hq
  have hu : Summable u := (hfM.add hbM).mul_left 2
  apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
  filter_upwards [hfM.tendsto_cofinite_zero.eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2),
    hbM.tendsto_cofinite_zero.eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2)] with jk hfs hbs x hx
  have hf : ‖ellipticGammaForwardArgument p q x jk.1 jk.2‖ ≤ fM jk :=
    norm_ellipticGammaForwardArgument_le_majorant hr hx.1 jk.1 jk.2
  have hb : ‖ellipticGammaBackwardArgument p q x jk.1 jk.2‖ ≤ bM jk :=
    norm_ellipticGammaBackwardArgument_le_majorant hx.2 jk.1 jk.2
  rw [ellipticGammaLogSummand]
  calc
    ‖ellipticGammaLogAtom (ellipticGammaForwardArgument p q x jk.1 jk.2) +
        ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x jk.1 jk.2)‖ ≤
      ‖ellipticGammaLogAtom (ellipticGammaForwardArgument p q x jk.1 jk.2)‖ +
        ‖ellipticGammaLogAtom (ellipticGammaBackwardArgument p q x jk.1 jk.2)‖ :=
      norm_add_le _ _
    _ ≤ 2 * ‖ellipticGammaForwardArgument p q x jk.1 jk.2‖ +
        2 * ‖ellipticGammaBackwardArgument p q x jk.1 jk.2‖ := by
      gcongr
      · exact norm_ellipticGammaLogAtom_le_two_mul (hf.trans hfs)
      · exact norm_ellipticGammaLogAtom_le_two_mul (hb.trans hbs)
    _ ≤ u jk := by
      dsimp [u]
      nlinarith

end

end GaloisForLFunctions
