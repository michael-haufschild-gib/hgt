import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.SurvivingPartition
import GaloisForLFunctions.HTGeometry.OrderedPositiveMomentDetermination
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-! # Spectral reconstruction from a holomorphic relative germ

Continuation gives every even thermal moment. The squared occupations are
decreasing summable sequences, so their positive moments retain multiplicity.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

theorem relativePartition_eq_of_levels {r q : ℕ} {b : SpectralBand r} {c : SpectralBand q}
    (he : ∀ n, (b n).val = (c n).val) : relativePartition b = relativePartition c := by
  funext z
  apply tsum_congr
  intro n
  simp only [complexDrop,he n]

private theorem even_level_moment {r : ℕ} (b : SpectralBand r) (k : ℕ) :
    survivingPartition b ((2*(k+1) : ℕ) : ℂ) = ((∑' n, ((b n).val^2)^(k+1) : ℝ) : ℂ) := by
  have hz : 1 < (((2*(k+1) : ℕ) : ℂ)).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (show 1 < 2*(k+1) by omega)
  rw [survivingPartition_eq_tsum b hz,Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [Complex.cpow_natCast,Complex.ofReal_pow,pow_mul]

private theorem summable_squared_levels {r : ℕ} (b : SpectralBand r) : Summable (fun n => (b n).val^2) := by
  simpa only [Real.rpow_two] using (summable_band_rpow_iff b 2).mpr (by norm_num)

theorem levels_of_accumulating_agreement {r q : ℕ} (b : SpectralBand r) (c : SpectralBand q)
    (hb : Antitone (fun n => (b n).val)) (hc : Antitone (fun n => (c n).val))
    {z : ℂ} (hz : 0 < z.re) (h : ∃ᶠ w in 𝓝[≠] z, relativePartition b w = relativePartition c w) :
    ∀ n, (b n).val = (c n).val := by
  have hab : AnalyticOnNhd ℂ (relativePartition b) {w : ℂ | 0 < w.re} := fun _ hw => analyticAt_relativePartition b hw
  have hac : AnalyticOnNhd ℂ (relativePartition c) {w : ℂ | 0 < w.re} := fun _ hw => analyticAt_relativePartition c hw
  have he := hab.eqOn_of_preconnected_of_frequently_eq hac (convex_halfSpace_re_gt 0).isPreconnected hz h
  have hm (k : ℕ) : (∑' n, ((b n).val^2)^(k+1)) = ∑' n, ((c n).val^2)^(k+1) := by
    apply Complex.ofReal_inj.mp
    rw [← even_level_moment b k,← even_level_moment c k]
    exact congrArg (fun u => riemannZeta ((2*(k+1) : ℕ) : ℂ) - u)
      (he (show ((2*(k+1) : ℕ) : ℂ) ∈ {w : ℂ | 0 < w.re} by
        change 0 < (((2*(k+1) : ℕ) : ℂ)).re
        rw [Complex.natCast_re]
        positivity))
  have hs := HTGeometry.antitone_nonneg_eq_of_powerSums_eq (summable_squared_levels b) (summable_squared_levels c)
    (fun n => sq_nonneg _) (fun n => sq_nonneg _)
    (fun i j hij => pow_le_pow_left₀ (band_pos b j).le (hb hij) 2)
    (fun i j hij => pow_le_pow_left₀ (band_pos c j).le (hc hij) 2) hm
  exact fun n => (sq_eq_sq₀ (band_pos b n).le (band_pos c n).le).mp (congrFun hs n)

/-- A local partition germ determines all ordered levels, even at the pole of the absolute Gibbs sum. -/
theorem ordered_germ_iff_levels {r q : ℕ} (b : SpectralBand r) (c : SpectralBand q)
    (hb : Antitone (fun n => (b n).val)) (hc : Antitone (fun n => (c n).val)) {z : ℂ} (hz : 0 < z.re) :
    relativePartition b =ᶠ[𝓝 z] relativePartition c ↔ ∀ n, (b n).val = (c n).val := by
  constructor
  · intro h
    exact levels_of_accumulating_agreement b c hb hc hz ((h.filter_mono nhdsWithin_le_nhds).frequently)
  · intro h
    rw [relativePartition_eq_of_levels h]

#print axioms relativePartition_eq_of_levels
#print axioms levels_of_accumulating_agreement
#print axioms ordered_germ_iff_levels

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
