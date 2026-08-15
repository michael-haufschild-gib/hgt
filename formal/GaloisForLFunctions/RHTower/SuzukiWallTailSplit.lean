import GaloisForLFunctions.RHTower.SuzukiWallWindowEstimate
import GaloisForLFunctions.RHTower.SuzukiRootRetainedJumpSource

/-!
# Splitting the forced profile at the frequency threshold

The variation-of-constants profile on the shifted line is the propagated datum plus the accumulated
forcing.  Splitting the accumulation at a threshold `W` separates the two mechanisms that control it:
everything gathered below the threshold is a *fixed* vector propagated by the Gamma transport, whose
square integrability is the decay `(1+|x|)^{-p}` with `2p > 1`; only the part gathered above the
threshold still depends on the evaluation point through its integration range, and that is the part
the integrations by parts act on.

Together with the observation that finitely many square-integrable pieces sum to a square-integrable
profile, this is the skeleton on which the one-block estimate is assembled: the threshold is chosen
so that the generator has a numerical floor above it, and each of the resulting terms is then
estimated by a mechanism of its own.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Finitely many square-integrable pieces -/

variable {Y : Type*} [NormedAddCommGroup Y]

/-- **A finite sum of square-integrable profiles is square integrable.** -/
theorem lintegral_sq_finsum_ne_top {ι : Type*} (s : Finset ι) {u : ι → ℝ → Y} {A : Set ℝ}
    (hm : ∀ i ∈ s, AEStronglyMeasurable (u i) (volume.restrict A))
    (hfin : ∀ i ∈ s, (∫⁻ L in A, ‖u i L‖ₑ ^ 2) ≠ ⊤) :
    (∫⁻ L in A, ‖∑ i ∈ s, u i L‖ₑ ^ 2) ≠ ⊤ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hmem : a ∈ insert a s := Finset.mem_insert_self a s
    have hsub : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have hrest := ih (fun i hi => hm i (hsub i hi)) (fun i hi => hfin i (hsub i hi))
    have hrw : ∀ L : ℝ, (∑ i ∈ insert a s, u i L) = u a L + ∑ i ∈ s, u i L := by
      intro L
      rw [Finset.sum_insert ha]
    rw [lintegral_congr fun L => by rw [hrw L]]
    exact lintegral_sq_add_ne_top (hm a hmem) (hfin a hmem) hrest

/-! ## The split at the frequency threshold -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

/-- The variation-of-constants profile on the shifted line: the propagated datum plus the forced
part. -/
def forcedProfile (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℝ → X) (c : X) (σ x : ℝ) : X :=
  stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c + forcedWindowPart E T b σ x

omit [Nontrivial X] in
/-- **The profile splits at any frequency threshold.**  Everything accumulated below the threshold
is a fixed vector propagated by the Gamma transport; only the part accumulated above it still
depends on the evaluation point through its integration range. -/
theorem forcedProfile_split (b : ℝ → X) (c : X) {σ W x : ℝ}
    (h₁ : IntervalIntegrable
      (fun t => stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)) volume 0 W)
    (h₂ : IntervalIntegrable
      (fun t => stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)) volume W x) :
    forcedProfile E T b c σ x
      = stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (c + ∫ t in (0 : ℝ)..W, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t))
        + stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
          (∫ t in W..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (b t)) := by
  rw [forcedProfile, forcedWindowPart,
    ← intervalIntegral.integral_add_adjacent_intervals h₁ h₂, map_add, map_add]
  abel

end GaloisForLFunctions.RHTower
