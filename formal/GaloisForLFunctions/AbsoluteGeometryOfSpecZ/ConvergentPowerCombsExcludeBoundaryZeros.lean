import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactMellinContinuation
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# A convergent power comb excludes every zero on its boundary

The summatory contact symbol has zero nonreal boundary residue if the
literal comb converges. At a zeta zero on that boundary its actual residue
is a nonzero multiple of `ζ(1+iγ)`. Thus convergence excludes boundary
zeros, even though it need not move the supremum of their real parts.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- A zero on the power boundary forces divergence of the literal power comb. -/
theorem not_powerCombTailConverges_of_boundary_zero
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hre : ρ.re = 1 - a) :
    ¬ PowerCombTailConverges a := by
  intro hc
  have hρ1 : ρ ≠ 1 := by
    intro he
    exact riemannZeta_ne_zero_of_one_le_re (by rw [he, one_re]) hzero
  have hρ0 : ρ ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    rw [hre, zero_re] at hh
    linarith only [ha2, hh]
  have hτ : ρ.im ≠ 0 := by
    intro hi
    have he : ρ = ((1 - a : ℝ) : ℂ) := by
      apply Complex.ext
      · simpa only [ofReal_re] using hre
      · simpa only [ofReal_im] using hi
    exact (_root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
      (by linarith only [ha2] : 0 < 1 - a)
      (by linarith only [ha] : 1 - a < 1)) (he ▸ hzero)
  have hza1 : ρ + (a : ℂ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [add_im, ofReal_im, add_zero, one_im] at hh
    exact hτ hh
  have hzne : riemannZeta (ρ + (a : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp only [add_re, ofReal_re, hre]; linarith)
  obtain ⟨L, hL⟩ :=
    (powerCombTailConverges_iff_normalizedPowerContacts_converges ha ha2).mp hc
  have hnorm : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - 2 * a)) * powerContactPrefix a N)
      atTop (𝓝 L) := by
    apply hL.congr
    intro N
    change (N : ℝ) ^ (2 * a - 1) * powerContactPrefix a N =
      (N : ℝ) ^ (-(1 - 2 * a)) * powerContactPrefix a N
    rw [show -(1 - 2 * a) = 2 * a - 1 by ring]
  obtain ⟨C, hC, hb⟩ := exists_power_bound_of_normalized_tendsto
    (show powerContactPrefix a 0 = 0 by simp [powerContactPrefix]) hnorm
  have hvan := tendsto_mul_powerContactMellin_of_powerCombTailConverges ha ha2 hτ hc
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
  have hshift : Tendsto (fun ε : ℝ => ρ + (ε : ℂ) + a) (𝓝[>] 0) (𝓝 (ρ + a)) :=
    hpath.add_const _
  have hmult := ((differentiableAt_riemannZeta hza1).continuousAt.tendsto.comp hshift).mul hprime
  have hnonzero : riemannZeta (ρ + a) * -(m : ℂ) ≠ 0 :=
    mul_ne_zero hzne (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  obtain ⟨η, hη, M, hpole⟩ := exists_logDeriv_symbol_pole_bound hzero hρ1 hρ0
  have hcontact : Tendsto (fun ε : ℝ => (ε : ℂ) *
      complexMellinPairing (powerContactPrefix a)
        (((1 - 2 * a + ε : ℝ) : ℂ) + (ρ.im : ℂ) * I))
      (𝓝[>] 0) (𝓝 (riemannZeta (ρ + a) * -(m : ℂ))) := by
    apply hmult.congr'
    filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    let s : ℂ := ((1 - 2 * a + ε : ℝ) : ℂ) + (ρ.im : ℂ) * I
    have he : s + a = ρ + (ε : ℂ) := by
      apply Complex.ext <;> simp only [s, add_re, add_im, ofReal_re, ofReal_im,
        mul_re, mul_im, I_re, I_im, hre] <;> ring
    have he2 : s + ((2 * a : ℝ) : ℂ) = ρ + (ε : ℂ) + a := by
      calc
        _ = (s + a) + a := by push_cast; ring
        _ = _ := by rw [he]
    have hdist : ‖ρ + (ε : ℂ) - ρ‖ < η := by
      simpa only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hε.1] using hε.2
    have hpne : ρ + (ε : ℂ) ≠ ρ := by
      intro hh
      have hz : (ε : ℂ) = 0 := add_left_cancel (hh.trans (add_zero ρ).symm)
      exact hε.1.ne' (Complex.ofReal_eq_zero.mp hz)
    obtain ⟨hzeta, hone, _⟩ := hpole (ρ + ε) hdist hpne
    have hs : 1 - 2 * a < s.re := by
      simp only [s, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
      linarith only [hε.1]
    have heq := complexMellinPairing_powerContacts_eq ha ha2 hC hb hs
      (by rwa [he]) (by rwa [he])
    rw [he, he2] at heq
    change riemannZeta (ρ + (ε : ℂ) + a) *
      ((ε : ℂ) * (-deriv riemannZeta (ρ + ε) / riemannZeta (ρ + ε) -
        riemannZeta (ρ + ε))) = (ε : ℂ) * complexMellinPairing (powerContactPrefix a) s
    rw [heq]
    ring
  exact hnonzero (tendsto_nhds_unique hcontact hvan)

/-- Convergence excludes every zeta zero on its contact boundary. -/
theorem powerCombTailConverges_excludes_boundary_zeros
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hc : PowerCombTailConverges a) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re ≠ 1 - a := by
  intro ρ hρ hre
  exact not_powerCombTailConverges_of_boundary_zero ha ha2 hρ hre hc

/-- Attainment of a positive right zero width makes its boundary comb
diverge. The zero-free line at one supplies positivity of the parameter. -/
theorem not_powerCombTailConverges_at_attained_zeroWidth
    (hw : 0 < SquareRootThreshold.zetaZeroWidth)
    (hatt : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧
      ρ.re = 1 / 2 + SquareRootThreshold.zetaZeroWidth) :
    ¬ PowerCombTailConverges (1 / 2 - SquareRootThreshold.zetaZeroWidth) := by
  obtain ⟨ρ, hzero, hre⟩ := hatt
  have hρ1 : ρ.re < 1 := lt_of_not_ge fun h =>
    riemannZeta_ne_zero_of_one_le_re h hzero
  apply not_powerCombTailConverges_of_boundary_zero
    (by linarith only [hre, hρ1]) (by linarith only [hw]) hzero
  linarith only [hre]

/-- If a positive right zero width is attained, the positive subcritical
convergence interval is exactly open at its known radius. -/
theorem powerCombTailConverges_iff_strict_width_of_attained_zeroWidth
    (hw : 0 < SquareRootThreshold.zetaZeroWidth)
    (hatt : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧
      ρ.re = 1 / 2 + SquareRootThreshold.zetaZeroWidth)
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    PowerCombTailConverges a ↔ a + SquareRootThreshold.zetaZeroWidth < 1 / 2 := by
  constructor
  · intro hc
    have hb := add_zeroWidth_le_half_of_powerCombTailConverges ha ha2 hc
    apply lt_of_le_of_ne hb
    intro he
    have haeq : a = 1 / 2 - SquareRootThreshold.zetaZeroWidth := by linarith only [he]
    exact not_powerCombTailConverges_at_attained_zeroWidth hw hatt (haeq ▸ hc)
  · intro haw
    exact ⟨powerTailCombMellinIntegral a, tendsto_powerCombTail_of_add_width_lt_half ha haw⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
