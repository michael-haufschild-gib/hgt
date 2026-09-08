import GaloisForLFunctions.RHTower.UnitModulusL2Multiplier
import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Tactic

/-!
# Singular scattering-phase evolution on the existing L² carrier

The time factor `exp(-i t/(2z))` from Section 5 of Yan–Zhang–Zhu,
arXiv:2607.19649, defines a unitary group on the real-line L² space. At the
single spectral point `z = 0` the phase is set to one, which does not change
Lebesgue L² classes. Every weighted Lp seminorm is preserved.

The construction applies to all existing Hermite profiles. The existing
nonzero Gaussian also refutes the literal converse asserted in Proposition 3.7:
boundedness and higher-exponent integrability do not exclude lower-exponent integrability.
These statements do not assert Sobolev preservation for arbitrary initial data.
-/

open MeasureTheory Complex
open scoped ENNReal SchwartzMap
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def phase (t z : ℝ) : ℂ := Complex.exp (-(↑(t / (2*z)) * I))

@[simp] theorem norm_phase (t z : ℝ) : ‖phase t z‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, neg_zero, Real.exp_zero]

theorem measurable_phase (t : ℝ) : Measurable (phase t) := by
  unfold phase
  fun_prop

@[simp] theorem phase_zero (z : ℝ) : phase 0 z = 1 := by simp [phase]

theorem phase_add (s t z : ℝ) : phase (s+t) z = phase s z * phase t z := by
  simp only [phase, add_div, Complex.ofReal_add, add_mul, neg_add_rev, Complex.exp_add]
  ring

theorem phase_neg_mul (t z : ℝ) : phase (-t) z * phase t z = 1 := by
  rw [← phase_add]
  simp

def timePhase (t : ℝ) : RHTower.UnitModulusL2Phase ℝ volume where
  toFun := phase t
  aestronglyMeasurable := (measurable_phase t).aestronglyMeasurable
  norm_eq_one := Filter.Eventually.of_forall (norm_phase t)

def evolution (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
    Lp ℂ 2 (volume : Measure ℝ) := (timePhase t).mulUnitary

theorem evolution_ae (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    evolution t f =ᵐ[volume] fun z => phase t z * f z :=
  (timePhase t).mulUnitary_ae f

@[simp] theorem norm_evolution (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖evolution t f‖ = ‖f‖ := (evolution t).norm_map f

theorem evolution_add (s t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    evolution (s+t) f = evolution s (evolution t f) := by
  apply Lp.ext
  filter_upwards [evolution_ae (s+t) f, evolution_ae s (evolution t f),
    evolution_ae t f] with z hst hs ht
  rw [hst, hs, ht, phase_add, mul_assoc]

@[simp] theorem evolution_zero (f : Lp ℂ 2 (volume : Measure ℝ)) :
    evolution 0 f = f := by
  apply Lp.ext
  filter_upwards [evolution_ae 0 f] with z hz
  simpa using hz

theorem evolution_neg (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    evolution (-t) (evolution t f) = f := by
  rw [← evolution_add]
  simp

/-- Every weighted Lp seminorm is unchanged, including exponents zero and infinity. -/
theorem weighted_eLpNorm_evolution (t : ℝ) (p : ℝ≥0∞) (w f : ℝ → ℂ) :
    eLpNorm (fun z => w z * (phase t z * f z)) p volume =
      eLpNorm (fun z => w z * f z) p volume := by
  apply eLpNorm_congr_norm_ae
  exact Filter.Eventually.of_forall fun z => by simp

theorem memLp_phase_iff (t : ℝ) (p : ℝ≥0∞) (f : ℝ → ℂ) :
    MemLp (fun z => phase t z * f z) p volume ↔ MemLp f p volume := by
  have forward (t : ℝ) (g : ℝ → ℂ) (hg : MemLp g p volume) :
      MemLp (fun z => phase t z * g z) p volume := by
    apply hg.congr_norm ((measurable_phase t).aestronglyMeasurable.mul hg.1)
    exact Filter.Eventually.of_forall fun z => by simp
  constructor
  · intro h
    have h' := forward (-t) _ h
    simpa only [← mul_assoc, phase_neg_mul, one_mul] using h'
  · exact forward t f

/-- The existing Gaussian is a nonzero bounded function in both L1 and L2,
contradicting the literal converse in Proposition 3.7. -/
theorem gaussian_counterexample :
    MemLp (gaussianSchwartz : ℝ → ℂ) 1 volume ∧
    MemLp (gaussianSchwartz : ℝ → ℂ) 2 volume ∧
    MemLp (gaussianSchwartz : ℝ → ℂ) ⊤ volume ∧
    gaussianSchwartz (0 : ℝ) ≠ 0 := by
  refine ⟨gaussianSchwartz.memLp 1 volume, gaussianSchwartz.memLp 2 volume,
    gaussianSchwartz.memLp ⊤ volume, ?_⟩
  simp [gaussianSchwartz_apply, gaussReal]

/-- Singular-phase evolution preserves every Hermite profile's complete Lp range. -/
theorem hermite_evolution_memLp (n : ℕ) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (fun z => phase t z * hermiteSchwartz n z) p volume :=
  (memLp_phase_iff t p _).mpr ((hermiteSchwartz n).memLp p volume)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
