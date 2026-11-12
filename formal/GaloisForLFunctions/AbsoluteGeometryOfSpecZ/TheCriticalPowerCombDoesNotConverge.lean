import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.CriticalPowerContactContinuation
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The critical power comb diverges

Convergence would remove every nonreal boundary residue of the restored
critical contact transform and every interior pole. A nontrivial zeta
zero, reflected to the right half-strip, supplies a nonzero residue in
one of those two places. The zero-free line at one keeps its multiplier
from vanishing.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity

private theorem critical_contact_residue_vanishes
    (hc : PowerCombTailConverges (1 / 2)) {ρ : ℂ}
    (hre : 1 / 2 ≤ ρ.re) (hτ : ρ.im ≠ 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      criticalPowerContactMellin (ρ - (1 / 2 : ℝ) + (ε : ℂ))) (𝓝[>] 0) (𝓝 0) := by
  rcases lt_or_eq_of_le hre with hgt | heq
  · have heps : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hpath : Tendsto (fun ε : ℝ => ρ - (1 / 2 : ℝ) + (ε : ℂ))
        (𝓝[>] 0) (𝓝 (ρ - (1 / 2 : ℝ))) := by
      simpa only [add_zero] using heps.const_add (ρ - (1 / 2 : ℝ))
    have hmem : ρ - (1 / 2 : ℝ) ∈ {s : ℂ | 0 < s.re} := by
      change 0 < (ρ - (1 / 2 : ℝ)).re
      simp only [sub_re, ofReal_re]
      linarith only [hgt]
    have hcont := ((differentiableOn_criticalPowerContactMellin hc).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).continuousAt
    simpa only [zero_mul, Function.comp_apply] using heps.mul (hcont.tendsto.comp hpath)
  · apply (tendsto_mul_criticalPowerContactMellin_at_nonreal_boundary hc hτ).congr
    intro ε
    have he : (ε : ℂ) + (ρ.im : ℂ) * I = ρ - (1 / 2 : ℝ) + (ε : ℂ) := by
      apply Complex.ext
      · simp only [add_re, sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        linarith only [heq]
      · simp only [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
          mul_one, zero_mul, add_zero, zero_add, sub_zero]
    rw [he]

/-- Any nontrivial zero on or right of the critical line prevents
convergence of the critical comb. -/
theorem not_criticalPowerCombTailConverges_of_zero
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hre : 1 / 2 ≤ ρ.re) :
    ¬ PowerCombTailConverges (1 / 2) := by
  intro hc
  have hρ1 : ρ ≠ 1 := by
    intro he
    exact riemannZeta_ne_zero_of_one_le_re (by rw [he, one_re]) hzero
  have hre1 : ρ.re < 1 := lt_of_not_ge fun h =>
    riemannZeta_ne_zero_of_one_le_re h hzero
  have hre0 : 0 < ρ.re := by linarith only [hre]
  have hρ0 : ρ ≠ 0 := by
    intro he
    rw [he, zero_re] at hre0
    exact lt_irrefl 0 hre0
  have hτ : ρ.im ≠ 0 := by
    intro hi
    have he : ρ = (ρ.re : ℂ) := by
      apply Complex.ext
      · simp only [ofReal_re]
      · simpa only [ofReal_im] using hi
    exact (_root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo hre0 hre1) (he ▸ hzero)
  have hz1 : ρ + (1 / 2 : ℝ) ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [add_im, ofReal_im, add_zero, one_im] at hi
    exact hτ hi
  have hzne : riemannZeta (ρ + (1 / 2 : ℝ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp only [add_re, ofReal_re]; linarith only [hre])
  have hvan := critical_contact_residue_vanishes hc hre hτ
  have heps : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hpath : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    simpa only [add_zero] using heps.const_add ρ
  have hpathNE : Tendsto (fun ε : ℝ => ρ + (ε : ℂ)) (𝓝[>] 0) (𝓝[≠] ρ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hpath, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change ρ + (ε : ℂ) ≠ ρ
    intro he
    have hz : (ε : ℂ) = 0 := add_left_cancel (he.trans (add_zero ρ).symm)
    exact (ne_of_gt (show 0 < ε from hε)) (Complex.ofReal_eq_zero.mp hz)
  obtain ⟨m, hm, hres⟩ := _root_.RHTower.neg_logDeriv_zeta_zero_residue hzero
  have hlog : Tendsto (fun ε : ℝ => (ε : ℂ) *
      (-deriv riemannZeta (ρ + ε) / riemannZeta (ρ + ε)))
      (𝓝[>] 0) (𝓝 (-(m : ℂ))) := by
    apply (hres.comp hpathNE).congr
    intro ε
    change (ρ + (ε : ℂ) - ρ) *
      (-deriv riemannZeta (ρ + ε) / riemannZeta (ρ + ε)) = _
    rw [add_sub_cancel_left]
  have hsmall := heps.mul ((differentiableAt_riemannZeta hρ1).continuousAt.tendsto.comp hpath)
  rw [zero_mul] at hsmall
  have hprime : Tendsto (fun ε : ℝ => (ε : ℂ) *
      (-deriv riemannZeta (ρ + ε) / riemannZeta (ρ + ε) - riemannZeta (ρ + ε)))
      (𝓝[>] 0) (𝓝 (-(m : ℂ))) := by
    have hh := hlog.sub hsmall
    rw [sub_zero] at hh
    exact hh.congr fun ε => (mul_sub _ _ _).symm
  have hmult := ((differentiableAt_riemannZeta hz1).continuousAt.tendsto.comp
    (hpath.add_const ((1 / 2 : ℝ) : ℂ))).mul hprime
  have hnonzero : riemannZeta (ρ + (1 / 2 : ℝ)) * -(m : ℂ) ≠ 0 :=
    mul_ne_zero hzne (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  obtain ⟨η, hη, M, hpole⟩ := exists_logDeriv_symbol_pole_bound hzero hρ1 hρ0
  have hactual : Tendsto (fun ε : ℝ => (ε : ℂ) *
      criticalPowerContactMellin (ρ - (1 / 2 : ℝ) + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 (riemannZeta (ρ + (1 / 2 : ℝ)) * -(m : ℂ))) := by
    apply hmult.congr'
    filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    let s : ℂ := ρ - (1 / 2 : ℝ) + (ε : ℂ)
    have he : s + (1 / 2 : ℝ) = ρ + (ε : ℂ) := by dsimp only [s]; ring
    have he1 : s + 1 = ρ + (ε : ℂ) + (1 / 2 : ℝ) := by
      dsimp only [s]
      push_cast
      ring
    have hdist : ‖ρ + (ε : ℂ) - ρ‖ < η := by
      simpa only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hε.1] using hε.2
    have hpne : ρ + (ε : ℂ) ≠ ρ := by
      intro hh
      have hz : (ε : ℂ) = 0 := add_left_cancel (hh.trans (add_zero ρ).symm)
      exact hε.1.ne' (Complex.ofReal_eq_zero.mp hz)
    obtain ⟨hzeta, hone, _⟩ := hpole (ρ + ε) hdist hpne
    have hs : 0 < s.re := by
      simp only [s, add_re, sub_re, ofReal_re]
      linarith only [hre, hε.1]
    have heq := criticalPowerContactMellin_eq hc hs (by rwa [he]) (by rwa [he])
    rw [he, he1] at heq
    change riemannZeta (ρ + (ε : ℂ) + (1 / 2 : ℝ)) *
      ((ε : ℂ) * (-deriv riemannZeta (ρ + ε) / riemannZeta (ρ + ε) -
        riemannZeta (ρ + ε))) = (ε : ℂ) * criticalPowerContactMellin s
    rw [heq]
    ring
  exact hnonzero (tendsto_nhds_unique hactual hvan)

/-- The critical parameter is always excluded: a nontrivial zero and its
functional-equation reflection supply a zero in the right half-strip. -/
theorem not_powerCombTailConverges_half : ¬ PowerCombTailConverges (1 / 2) := by
  obtain ⟨ρ, hρ0, hρ1, hzero⟩ := _root_.RHTower.exists_riemannZeta_zero_mem_openStrip
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
  · exact not_criticalPowerCombTailConverges_of_zero hzero hre
  · have hzero' := _root_.RHTower.riemannZeta_one_sub_eq_zero_of_mem_openStrip hzero hρ0 hρ1
    apply not_criticalPowerCombTailConverges_of_zero hzero'
    simp only [sub_re, one_re]
    linarith only [hre]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
