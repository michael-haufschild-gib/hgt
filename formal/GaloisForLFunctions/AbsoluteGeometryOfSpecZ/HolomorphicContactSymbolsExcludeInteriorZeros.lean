import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ContactSymbolsContinueAcrossZeros
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Holomorphic contact symbols exclude interior zeta zeros

The actual contact Dirichlet symbol has a nonzero residue at every zeta
zero strictly beyond its power boundary. Its zeta multiplier lies to the
right of one, so a holomorphic continuation cannot contain that pole.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity

/-- A zero beyond the power boundary contradicts holomorphy of any
continuation of the actual contact Dirichlet symbol. -/
theorem holomorphic_contact_symbol_excludes_interior_zero
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s : ℂ | 1 - 2 * a < s.re})
    (hinitial : ∀ s : ℂ, 2 < s.re → F s =
      riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (-deriv riemannZeta (s + (a : ℂ)) / riemannZeta (s + (a : ℂ)) -
          riemannZeta (s + (a : ℂ))))
    {ρ : ℂ} (hzero : riemannZeta ρ = 0) (hre : 1 - a < ρ.re) : False := by
  have hρ1 : ρ ≠ 1 := by
    intro he
    exact riemannZeta_ne_zero_of_one_le_re (by rw [he, one_re]) hzero
  have hρ0 : ρ ≠ 0 := by
    intro he
    rw [he, zero_re] at hre
    linarith only [ha1, hre]
  have hza : 1 < (ρ + (a : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith only [hre]
  have hza1 : ρ + (a : ℂ) ≠ 1 := by
    intro he
    rw [he, one_re] at hza
    exact lt_irrefl 1 hza
  have hzne := riemannZeta_ne_zero_of_one_lt_re hza
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
  have hpathF : Tendsto (fun ε : ℝ => ρ - (a : ℂ) + (ε : ℂ))
      (𝓝[>] 0) (𝓝 (ρ - (a : ℂ))) := by
    simpa only [add_zero] using heps.const_add (ρ - (a : ℂ))
  have hmem : ρ - (a : ℂ) ∈ {s : ℂ | 1 - 2 * a < s.re} := by
    change 1 - 2 * a < (ρ - (a : ℂ)).re
    simp only [sub_re, ofReal_re]
    linarith only [hre]
  have hcont := ((hF).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).continuousAt
  have hvan : Tendsto (fun ε : ℝ => (ε : ℂ) *
      F (ρ - (a : ℂ) + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using heps.mul (hcont.tendsto.comp hpathF)
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
  have hmult := ((differentiableAt_riemannZeta hza1).continuousAt.tendsto.comp
    (hpath.add_const (a : ℂ))).mul hprime
  have hnonzero : riemannZeta (ρ + a) * -(m : ℂ) ≠ 0 :=
    mul_ne_zero hzne (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))
  obtain ⟨η, hη, M, hpole⟩ := exists_logDeriv_symbol_pole_bound hzero hρ1 hρ0
  have hactual : Tendsto (fun ε : ℝ => (ε : ℂ) *
      F (ρ - (a : ℂ) + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 (riemannZeta (ρ + a) * -(m : ℂ))) := by
    apply hmult.congr'
    filter_upwards [Ioo_mem_nhdsGT hη] with ε hε
    let s : ℂ := ρ - (a : ℂ) + (ε : ℂ)
    have he : s + a = ρ + (ε : ℂ) := by dsimp only [s]; ring
    have he2 : s + ((2 * a : ℝ) : ℂ) = ρ + (ε : ℂ) + a := by
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
    have hs : 1 - 2 * a < s.re := by
      simp only [s, add_re, sub_re, ofReal_re]
      linarith only [hre, hε.1]
    have heq := contactSymbol_eq_of_holomorphic ha hF hinitial hs
      (by rwa [he]) (by rwa [he])
    rw [he, he2] at heq
    change riemannZeta (ρ + (ε : ℂ) + a) *
      ((ε : ℂ) * (-deriv riemannZeta (ρ + ε) / riemannZeta (ρ + ε) -
        riemannZeta (ρ + ε))) = (ε : ℂ) * F s
    rw [heq]
    ring
  exact hnonzero (tendsto_nhds_unique hactual hvan)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
