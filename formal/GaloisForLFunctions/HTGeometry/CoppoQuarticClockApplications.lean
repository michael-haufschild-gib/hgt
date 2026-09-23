import GaloisForLFunctions.HTGeometry.CoppoKerrPhaseGeometry
import GaloisForLFunctions.HTGeometry.CoppoJosephsonPotential
import GaloisForLFunctions.HTGeometry.SourcePairSymmetricGradedQuarticClassification
import GaloisForLFunctions.HTGeometry.ClockDatumExample

/-!
# Quartic moment and clock realizations of the Coppo potentials

The collective polynomial of arXiv:2606.25061 is a linear combination of
second and fourth moments of the existing symmetric real source block.
The pure Josephson harmonic of arXiv:2405.03454 is the real transverse
restriction of the corpus's coupled cosine clock potential.
-/

open Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The collective potential is exactly a second/fourth-moment combination. -/
theorem coppoCollectivePotential_sourcePair_moments (alpha beta k a b : ℝ) :
    _root_.HTGeometry.coppoCollectivePotential alpha beta a (k * b) =
      -alpha / 4 * (sourcePairSymmetricRealEvenMoment 2 k a b).re +
        beta / 8 * (sourcePairSymmetricRealEvenMoment 4 k a b).re := by
  simp only [sourcePairSymmetricRealEvenMoment, ← Complex.ofReal_pow, ← Complex.ofReal_add,
    Complex.ofReal_re, _root_.HTGeometry.coppoCollectivePotential]
  ring

/-- The same identity holds on the literal matrix power traces of the corpus source block. -/
theorem coppoCollectivePotential_sourcePair_matrix (alpha beta k a b : ℝ) :
    _root_.HTGeometry.coppoCollectivePotential alpha beta a (k * b) =
      -alpha / 4 * ((sourcePairSymmetricRealEvenBlock k a b ^ (2 : ℕ)).trace).re +
        beta / 8 * ((sourcePairSymmetricRealEvenBlock k a b ^ (4 : ℕ)).trace).re := by
  rw [sourcePairSymmetricRealEvenBlock_trace_pow, sourcePairSymmetricRealEvenBlock_trace_pow]
  exact coppoCollectivePotential_sourcePair_moments alpha beta k a b

/-- The source block's quartic-minus-quadratic energy has the critical collective minimum bound. -/
theorem coppoSourcePair_quartic_energy_lower (g k a b : ℝ) :
    -g ^ (4 : ℕ) ≤ -g ^ (2 : ℕ) * (sourcePairSymmetricRealEvenMoment 2 k a b).re +
      (sourcePairSymmetricRealEvenMoment 4 k a b).re / 2 := by
  have h := _root_.HTGeometry.coppoKerrEnergy_density_global_min g (Real.sqrt 2) a (k * b)
  have hs : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) := Real.sq_sqrt (by positivity)
  rw [hs] at h
  have heq : _root_.HTGeometry.coppoKerrEnergy (g ^ (2 : ℕ)) (1 + 2) a (k * b) =
      -g ^ (2 : ℕ) * (sourcePairSymmetricRealEvenMoment 2 k a b).re +
        (sourcePairSymmetricRealEvenMoment 4 k a b).re / 2 := by
    simp only [sourcePairSymmetricRealEvenMoment, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Complex.ofReal_re, _root_.HTGeometry.coppoKerrEnergy]
    ring
  rw [heq] at h
  have hmin : _root_.HTGeometry.coppoKerrEnergy (g ^ (2 : ℕ)) (1 + 2) g 0 = -g ^ (4 : ℕ) := by
    dsimp [_root_.HTGeometry.coppoKerrEnergy]; ring
  rwa [hmin] at h

/-- The existing coupled clock is a pure Josephson first harmonic on the real axis. -/
theorem cosPotential_real_eq_coppoJosephson (s t x : ℝ) :
    (cosPotential s t (x : ℂ)).re =
      _root_.HTGeometry.coppoJosephsonPotential (-Real.sin s * Real.cos t) 0 x := by
  simp [cosPotential, ← Complex.ofReal_cos, -Complex.ofReal_sin, _root_.HTGeometry.coppoJosephsonPotential]

/-- A half-period shift reverses the real clock potential exactly. -/
theorem cosPotential_real_halfTurn (s t x : ℝ) :
    (cosPotential s t ((x + Real.pi : ℝ) : ℂ)).re = -(cosPotential s t (x : ℂ)).re := by
  rw [cosPotential_real_eq_coppoJosephson, cosPotential_real_eq_coppoJosephson]
  simp [_root_.HTGeometry.coppoJosephsonPotential]

/-- The circuit's explicit zero mode is the exponential tilt of this actual clock restriction. -/
theorem coppoJosephsonGroundState_eq_exp_cosPotential (s t x : ℝ) :
    _root_.HTGeometry.coppoJosephsonGroundState (Real.sin s * Real.cos t) x =
      Real.exp ((cosPotential s t (x : ℂ)).re) := by
  simp [cosPotential, ← Complex.ofReal_cos, -Complex.ofReal_sin, _root_.HTGeometry.coppoJosephsonGroundState]

end GaloisForLFunctions.HTGeometry
