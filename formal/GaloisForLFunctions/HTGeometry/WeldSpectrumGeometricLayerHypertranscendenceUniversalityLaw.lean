import GaloisForLFunctions.HTGeometry.FiniteGeometricLayerDAResonance
import GaloisForLFunctions.RHTower.SeamSpectrumTranscendence

/-!
# Weld-spectrum geometric-layer hypertranscendence universality

Every nonzero rate in the prime-log weld spectrum is transcendental.  A finite geometric tower in
the negative log-magnitudes of a differentially algebraic Taylor series can contain only algebraic
layer ratios.  Therefore the appearance of any nonzero weld rate at any visible or hidden geometric
depth forces hypertranscendence.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter PowerSeries Topology

noncomputable section

/-- **Weld-spectrum geometric-layer hypertranscendence universality law.**  If any layer ratio of a
finite geometric Taylor-magnitude tower lies nontrivially in the prime-log weld spectrum, then every
phase realization of those magnitudes is hypertranscendental.  The layer may be arbitrarily deep and
need not be visible to the ordinary successive-ratio limit. -/
theorem hypertranscendental_of_finiteGeometricLayer_weldSpectrum_ratio
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {A lam : ℝ} {layers : List (ℝ × ℝ)} {b h : ℕ → ℝ}
    (htower : FiniteGeometricLayerTower ((A, lam) :: layers) b h)
    (hb : ∀ᶠ i in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ = Real.exp (-b i))
    {layer : ℝ × ℝ} (hlayer : layer ∈ (A, lam) :: layers)
    (hspectrum : layer.2 ∈ GaloisForLFunctions.RHTower.primeLogLattice)
    (hnonzero : layer.2 ≠ 0) :
    Hypertranscendental f := by
  exact hypertranscendental_of_finiteGeometricLayer_transcendental_ratio
    hf htower hb hlayer
      (GaloisForLFunctions.RHTower.weld_spectrum_transcendental
        layer.2 hspectrum hnonzero)

end

end GaloisForLFunctions.HTGeometry
