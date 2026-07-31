import GaloisForLFunctions.RHTower.XiWaveTraceCofinalQuadrature
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Cofinal sign change of the curvature-centered Suzuki screw primitive

Counted with analytic multiplicity, the Xi zero ordinates again form an admissible wave
spectrum. Its constant-weight wave trace is exactly the curvature-centered primitive
`h(A) = ∑ sin (gamma A) / gamma ^ 3` of Suzuki's screw profile.

The Landau recurrence therefore applies: `h` is neither eventually nonnegative nor eventually
nonpositive, so the initial screw average crosses the central Xi curvature strictly in both
directions at arbitrarily large apertures.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The Xi zero ordinates with analytic multiplicity as an admissible wave spectrum. -/
def xiCopyWaveSpectrum : WaveSpectrum XiZeroCopy where
  gamma := xiSpectralPoint
  invol := xiZeroCopyLineConjEquiv
  gamma_invol := xiSpectralPoint_lineConj
  lower := xiHeightLowerBound
  lower_pos := xiHeightLowerBound_pos
  lower_le := fun q => by
    rw [xiSpectralPoint_eq_support]
    exact xiWaveSpectrum.lower_le q.1
  width := 1 / 2
  width_nonneg := by norm_num
  im_le := fun q => by
    rw [xiSpectralPoint_eq_support]
    exact xiWaveSpectrum.im_le q.1
  summable_inv_sq := by
    refine xiSpectralPoint_inv_sq_summable.congr (fun q => ?_)
    rw [one_div, ← inv_pow]

theorem xiCopyWaveSpectrum_locallyFinite : xiCopyWaveSpectrum.IsLocallyFiniteSpectrum := by
  intro R
  have hbase : {ρ : XiDivisorSupport | ‖xiSpectralPointSupport ρ‖ ≤ R}.Finite :=
    xiWaveSpectrum_locallyFinite R
  have hcover : {q : XiZeroCopy | ‖xiCopyWaveSpectrum.gamma q‖ ≤ R} ⊆
      ⋃ ρ ∈ {ρ : XiDivisorSupport | ‖xiSpectralPointSupport ρ‖ ≤ R},
        (Set.range (Sigma.mk ρ) : Set XiZeroCopy) := by
    intro q hq
    refine Set.mem_biUnion (show q.1 ∈ {ρ : XiDivisorSupport |
      ‖xiSpectralPointSupport ρ‖ ≤ R} from hq) ?_
    exact ⟨q.2, rfl⟩
  exact Set.Finite.subset (hbase.biUnion (fun ρ _ => Set.finite_range _)) hcover

theorem xiCopyWaveSpectrum_re_ne_zero (q : XiZeroCopy) :
    (xiCopyWaveSpectrum.gamma q).re ≠ 0 := by
  show (xiSpectralPoint q).re ≠ 0
  rw [xiSpectralPoint_eq_support]
  exact xiWaveSpectrum_re_ne_zero q.1

theorem xiCopyWaveSpectrum_squares_infinite :
    (Set.range fun q : XiZeroCopy => xiCopyWaveSpectrum.gamma q ^ 2).Infinite := by
  refine xiWaveSpectrum_squares_infinite.mono ?_
  rintro _ ⟨ρ, rfl⟩
  have hmult : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    have := xi_divisor_pos_on_support ρ
    omega
  exact ⟨⟨ρ, ⟨0, hmult⟩⟩, rfl⟩

/-- The constant-weight wave trace of the multiplicity divisor is the curvature-centered
screw primitive. -/
theorem xiCopyWaveSpectrum_waveTrace_one (A : ℝ) :
    xiCopyWaveSpectrum.waveTrace 1 A =
      ∑' q : XiZeroCopy,
        Complex.sin (xiSpectralPoint q * A) / xiSpectralPoint q ^ 3 := by
  refine tsum_congr fun q => ?_
  show Complex.sin (xiSpectralPoint q * A) *
      Polynomial.aeval ((xiSpectralPoint q ^ 2)⁻¹) (1 : Polynomial ℝ) /
      xiSpectralPoint q ^ 3 = _
  simp

/-- **Cofinal two-sided sign change of the curvature-centered screw primitive.** For every
aperture bound there are strictly larger apertures at which the primitive is negative and at
which it is positive. No Riemann hypothesis, simplicity, or rational-independence premise is
used. -/
theorem xiScrewPrimitive_cofinal_sign_change (A0 : ℝ) :
    (∃ A, A0 < A ∧ xiCopyWaveSpectrum.realWaveTrace 1 A < 0) ∧
      ∃ A, A0 < A ∧ 0 < xiCopyWaveSpectrum.realWaveTrace 1 A :=
  ⟨cofinalWaveSignEscape xiCopyWaveSpectrum xiCopyWaveSpectrum_locallyFinite
      xiCopyWaveSpectrum_re_ne_zero xiCopyWaveSpectrum_squares_infinite 1 one_ne_zero A0,
    exists_pos_realWaveTrace xiCopyWaveSpectrum xiCopyWaveSpectrum_locallyFinite
      xiCopyWaveSpectrum_re_ne_zero xiCopyWaveSpectrum_squares_infinite one_ne_zero A0⟩

end

end RHTower
