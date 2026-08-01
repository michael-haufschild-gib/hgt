import GaloisForLFunctions.RHTower.SoninOrthonormalCompactVanishing
import GaloisForLFunctions.RHTower.SoninEulerTripleShellOverlap

/-!
# High shell modes leave every fixed frequency band

A mode of a fixed shell is fixed by the physical cutoff at the shell's outer radius, so a frequency
cutoff sees it only through the physical-then-Fourier block — and that block is a finite
time--frequency rectangle, hence compact.  Compact operators die on orthonormal sequences, so the
mode's mass inside any fixed frequency band vanishes as the mode number grows.

This is the band term of a mode estimate, and it needed no new analysis: the rectangle is already
in the corpus's relative ideal.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology

/-- **Band escape for shell modes.**  The mass of a high shell mode inside a fixed frequency band
vanishes. -/
theorem tendsto_norm_evenFourierCutoff_evenShellVectorEven
    (t s u : ℝ) (ht : 0 < t) (hs : 0 < s) (hsu : s < u) :
    Tendsto (fun n => ‖evenFourierCutoff t (evenShellVectorEven s u hsu n)‖) atTop (𝓝 0) := by
  have hblock : IsCompactOperator (evenFourierCutoff t * evenIndicatorCutoff u) :=
    (IsSoninPrincipalRelativeIdeal.fourierIndicator t u ht).isCompactOperator
  have hdie := tendsto_norm_compactOperator_apply_orthonormal hblock
    (evenShellVectorEven_orthonormal s u hs hsu)
  refine hdie.congr fun n => ?_
  have hfix : evenIndicatorCutoff u (evenShellVectorEven s u hsu n) =
      evenShellVectorEven s u hsu n :=
    evenIndicatorCutoff_evenShellVectorEven_of_le s u u hsu le_rfl n
  have happly : (evenFourierCutoff t * evenIndicatorCutoff u) (evenShellVectorEven s u hsu n) =
      evenFourierCutoff t (evenShellVectorEven s u hsu n) := by
    rw [mul_apply_eq_comp]
    show evenFourierCutoff t (evenIndicatorCutoff u (evenShellVectorEven s u hsu n)) =
      evenFourierCutoff t (evenShellVectorEven s u hsu n)
    rw [hfix]
  rw [happly]

/-- The complementary reading: a high shell mode is essentially untouched by the frequency cutoff's
complement, in the sense that the cutoff part vanishes. -/
theorem tendsto_norm_sub_evenFourierCutoff_evenShellVectorEven
    (t s u : ℝ) (ht : 0 < t) (hs : 0 < s) (hsu : s < u) :
    Tendsto (fun n => ‖evenShellVectorEven s u hsu n -
        (evenShellVectorEven s u hsu n - evenFourierCutoff t (evenShellVectorEven s u hsu n))‖)
      atTop (𝓝 0) := by
  refine (tendsto_norm_evenFourierCutoff_evenShellVectorEven t s u ht hs hsu).congr fun n => ?_
  congr 1
  abel

end RHTower
