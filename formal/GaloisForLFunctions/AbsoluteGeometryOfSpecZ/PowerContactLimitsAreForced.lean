import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactMellinContinuation
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.PowerAsymptoticsDetermineRealBoundaryResidues
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# The leading contact coefficient is forced by zeta's real residue

Whenever normalized weighted prime contacts converge, the resonant Abel
limit identifies their coefficient with the real-boundary residue of the
continued contact symbol. No strict gap from the actual zero width is used.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open ArithmeticCorrespondencePositivity TransHorizonIncidenceMechanics

/-- The real-boundary pole fixes every convergent normalized contact limit. -/
theorem normalizedPowerContacts_limit_coefficient
    {a L : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (hL : Tendsto (normalizedPowerContacts a) atTop (𝓝 L)) :
    (1 - 2 * (a : ℂ)) * (L : ℂ) =
      -deriv riemannZeta (1 - (a : ℂ)) / riemannZeta (1 - (a : ℂ)) -
        riemannZeta (1 - (a : ℂ)) := by
  have hnorm : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - 2 * a)) * powerContactPrefix a N)
      atTop (𝓝 L) := by
    apply hL.congr
    intro N
    change (N : ℝ) ^ (2 * a - 1) * powerContactPrefix a N =
      (N : ℝ) ^ (-(1 - 2 * a)) * powerContactPrefix a N
    rw [show -(1 - 2 * a) = 2 * a - 1 by ring]
  have hf0 : powerContactPrefix a 0 = 0 := by simp [powerContactPrefix]
  obtain ⟨C, hC, hb⟩ := exists_power_bound_of_normalized_tendsto hf0 hnorm
  have hres := tendsto_mul_complexMellinPairing_at_real_boundary hf0
    (show 0 ≤ 1 - 2 * a by linarith only [ha2]) hnorm
  have hζ : riemannZeta (1 - (a : ℂ)) ≠ 0 := by
    simpa only [ofReal_sub, ofReal_one] using
      _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
        (by linarith only [ha2] : 0 < 1 - a)
        (by linarith only [ha] : 1 - a < 1)
  have hσ1 : 1 - (a : ℂ) ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [sub_re, one_re, ofReal_re] at hh
    linarith only [ha, hh]
  have hζan : AnalyticAt ℂ riemannZeta (1 - (a : ℂ)) := by
    have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ) := fun z hz =>
      (differentiableAt_riemannZeta (by simpa only [mem_compl_iff, mem_singleton_iff] using hz)).differentiableWithinAt
    exact (hd.analyticOnNhd isOpen_compl_singleton) _
      (by simpa only [mem_compl_iff, mem_singleton_iff] using hσ1)
  have hB : ContinuousAt (fun z : ℂ => -deriv riemannZeta z / riemannZeta z - riemannZeta z)
      (1 - (a : ℂ)) :=
    ((hζan.deriv.continuousAt.neg).div hζan.continuousAt hζ).sub hζan.continuousAt
  have heps : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hpath : Tendsto (fun ε : ℝ => 1 - (a : ℂ) + (ε : ℂ))
      (𝓝[>] 0) (𝓝 (1 - (a : ℂ))) := by
    simpa only [add_zero] using heps.const_add (1 - (a : ℂ))
  have hunit : Tendsto (fun ε : ℝ => (ε : ℂ) * riemannZeta (1 + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 1) := by
    have hpath1 : Tendsto (fun ε : ℝ => 1 + (ε : ℂ)) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
      simpa only [add_zero] using heps.const_add 1
    have hh := _root_.RHTower.zetaResidueUnit_analyticAt.continuousAt.tendsto.comp
      hpath1
    rw [_root_.RHTower.zetaResidueUnit_one] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (show 0 < ε from hε))
    have hne : 1 + (ε : ℂ) ≠ 1 := by
      intro he
      exact hε0 (add_left_cancel (he.trans (add_zero 1).symm))
    change _root_.RHTower.zetaResidueUnit (1 + (ε : ℂ)) = _
    rw [ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hne]
    ring
  have hprod := hunit.mul (hB.tendsto.comp hpath)
  rw [one_mul] at hprod
  have hactual : Tendsto (fun ε : ℝ => (ε : ℂ) *
      complexMellinPairing (powerContactPrefix a) ((1 - 2 * a + ε : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (-deriv riemannZeta (1 - (a : ℂ)) /
        riemannZeta (1 - (a : ℂ)) - riemannZeta (1 - (a : ℂ)))) := by
    apply hprod.congr'
    filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    let s : ℂ := ((1 - 2 * a + ε : ℝ) : ℂ)
    have he : s + (a : ℂ) = 1 - (a : ℂ) + (ε : ℂ) := by
      dsimp only [s]
      push_cast
      ring
    have he2 : s + ((2 * a : ℝ) : ℂ) = 1 + (ε : ℂ) := by
      dsimp only [s]
      push_cast
      ring
    have hp0 : 0 < 1 - a + ε := by linarith only [ha2, hε.1]
    have hp1 : 1 - a + ε < 1 := by linarith only [hε.2]
    have hzne : riemannZeta (1 - (a : ℂ) + (ε : ℂ)) ≠ 0 := by
      simpa only [ofReal_add, ofReal_sub, ofReal_one] using
        _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo hp0 hp1
    have hone : 1 - (a : ℂ) + (ε : ℂ) ≠ 1 := by
      intro hz
      have hh := congrArg Complex.re hz
      simp only [add_re, sub_re, one_re, ofReal_re] at hh
      exact (ne_of_lt hp1) hh
    have hs : 1 - 2 * a < s.re := by
      change 1 - 2 * a < 1 - 2 * a + ε
      linarith only [hε.1]
    have heq := complexMellinPairing_powerContacts_eq ha ha2 hC hb hs
      (by rwa [he]) (by rwa [he])
    rw [he, he2] at heq
    change ((ε : ℂ) * riemannZeta (1 + (ε : ℂ))) *
      (-deriv riemannZeta (1 - (a : ℂ) + (ε : ℂ)) /
        riemannZeta (1 - (a : ℂ) + (ε : ℂ)) - riemannZeta (1 - (a : ℂ) + (ε : ℂ))) =
      (ε : ℂ) * complexMellinPairing (powerContactPrefix a) s
    rw [heq]
    ring
  have heq := tendsto_nhds_unique hres hactual
  simpa only [ofReal_sub, ofReal_one, ofReal_mul, ofReal_ofNat] using heq

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
