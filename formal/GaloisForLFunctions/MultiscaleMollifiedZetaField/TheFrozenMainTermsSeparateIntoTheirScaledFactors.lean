import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFrozenGcdJetsHaveTheirProfileLimits
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZetaPoleHasItsScaledJetLimits
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTwistedMainTermsHavePolynomialDerivatives

/-!
# Exact normalized factors of the frozen main terms

The arithmetic factors carry `log N`, the zeta pole carries its reciprocal,
and the reflected chi integral remains separate. These factors reproduce
the actual main term with frozen coefficients. Dividing each physical
displacement jet by `(log N)^j` gives its literal normalized derivative.
-/

open Complex Filter MeasureTheory Metric Set Topology
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Real tapered reflected weight. -/
def realChiTaperIntegral (p q η d : ℝ) : ℝ :=
  ∫ t, blockWindow p q η t * (chiPairWeight d t).re

theorem chiPairWeight_eq_ofReal_re (d t : ℝ) :
    chiPairWeight d t = ((chiPairWeight d t).re : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [chiPairWeight, displacedLinePt_neg_eq_conj, zetaChi_conj]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

theorem integral_chiPairWeight_eq_ofReal (p q η d : ℝ) :
    (∫ t, blockWindowC p q η t * chiPairWeight d t) =
      (realChiTaperIntegral p q η d : ℂ) := by
  calc
    _ = ∫ t, ((blockWindow p q η t * (chiPairWeight d t).re : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with t
      simpa only [blockWindowC, Complex.ofReal_mul] using
        congrArg (fun w : ℂ => (blockWindow p q η t : ℂ) * w)
          (chiPairWeight_eq_ofReal_re d t)
    _ = _ := integral_ofReal

/-- Physical main jets expressed in the normalized displacement coordinate. -/
def normalizedFrozenMainJet (P : ℝ → ℝ) (N : ℕ) (u p q η : ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  realTwistedMomentMainJet p q η N (moebiusProfileWeights P N (-u)) j
    ((u + z) / Real.log N) / (Real.log N) ^ j

/-- Exact separation into the two normalized arithmetic factors, their poles, and the reflected weight. -/
theorem normalizedFrozenMainJet_zero_eq {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (u p q η z : ℝ) :
    normalizedFrozenMainJet P N u p q η 0 z =
      frozenDirectGcd P N u z * scaledZetaPoleValue (Real.log N) (-2) (u + z) *
        (∫ t, blockWindow p q η t) +
      frozenReflectedGcd P N u z * scaledZetaPoleValue (Real.log N) 2 (u + z) *
        realChiTaperIntegral p q η ((u + z) / Real.log N) := by
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold normalizedFrozenMainJet
  rw [pow_zero, div_one, realTwistedMomentMainJet_zero]
  unfold twistedMomentMain
  rw [integral_chiPairWeight_eq_ofReal]
  have hW : (∫ t, blockWindowC p q η t) = ((∫ t, blockWindow p q η t) : ℂ) := integral_ofReal
  rw [hW]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero]
  unfold frozenDirectGcd frozenReflectedGcd scaledZetaPoleValue
  have hm : ((2 * (1 / 2 - (u + z) / Real.log N) : ℝ) : ℂ) =
      1 + (((-2) * (u + z) / Real.log N : ℝ) : ℂ) := by push_cast; ring
  have hp : ((1 + 2 * ((u + z) / Real.log N) : ℝ) : ℂ) =
      1 + ((2 * (u + z) / Real.log N : ℝ) : ℂ) := by push_cast; ring
  rw [hm, hp]
  field_simp [hL] <;> ring

/-- Normalized adjacent main jets are exact successive real derivatives. -/
theorem hasDerivAt_normalizedFrozenMainJet {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (u : ℝ) {p q η : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    (j : ℕ) {z : ℝ} (hz : 0 < (u + z) / Real.log N)
    (hz20 : (u + z) / Real.log N ≤ 1 / 20) :
    HasDerivAt (normalizedFrozenMainJet P N u p q η j)
      (normalizedFrozenMainJet P N u p q η (j + 1) z) z := by
  have hL : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hg := (((hasDerivAt_id z).const_add u).div_const (Real.log N))
  have hh := ((hasDerivAt_realTwistedMomentMainJet hη hp N
    (moebiusProfileWeights P N (-u)) hz hz20 j).comp z hg).div_const ((Real.log N) ^ j)
  apply hh.congr_deriv
  simp only [normalizedFrozenMainJet, id_eq, one_div]
  rw [pow_succ]
  field_simp [hL] <;> ring

/-- The first two normalized main jets are the literal derivatives at the frozen centre. -/
theorem normalizedFrozenMainJet_derivatives {N : ℕ} (hN : 1 < N)
    (P : ℝ → ℝ) (u : ℝ) {p q η : ℝ} (hη : 0 < η) (hp : 4 ≤ p - η)
    (hu : 0 < u / Real.log N) (hu20 : u / Real.log N < 1 / 20) :
    deriv (normalizedFrozenMainJet P N u p q η 0) 0 =
      normalizedFrozenMainJet P N u p q η 1 0 ∧
    iteratedDeriv 2 (normalizedFrozenMainJet P N u p q η 0) 0 =
      normalizedFrozenMainJet P N u p q η 2 0 := by
  have h0 : 0 < (u + 0) / Real.log N := by simpa only [add_zero] using hu
  have h020 : (u + 0) / Real.log N ≤ 1 / 20 := by simpa only [add_zero] using hu20.le
  constructor
  · exact (hasDerivAt_normalizedFrozenMainJet hN P u hη hp 0 h0 h020).deriv
  · have hc : ContinuousAt (fun z : ℝ => (u + z) / Real.log N) 0 := by fun_prop
    have hnear : ∀ᶠ z in 𝓝 (0 : ℝ), (u + z) / Real.log N ∈ Ioo 0 (1 / 20) :=
      hc.eventually (isOpen_Ioo.mem_nhds (by simpa only [add_zero] using And.intro hu hu20))
    have he : deriv (normalizedFrozenMainJet P N u p q η 0) =ᶠ[𝓝 (0 : ℝ)]
        normalizedFrozenMainJet P N u p q η 1 := by
      filter_upwards [hnear] with z hz
      exact (hasDerivAt_normalizedFrozenMainJet hN P u hη hp 0 hz.1 hz.2.le).deriv
    rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
    exact (hasDerivAt_normalizedFrozenMainJet hN P u hη hp 1 h0 h020).deriv

end GaloisForLFunctions.MultiscaleMollifiedZetaField
