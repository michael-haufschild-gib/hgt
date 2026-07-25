/-
Capstone: the three quantitative statements behind the method-ceiling map.

Three separately-proved facts are bundled here as one theorem, because together they are the content
of the map:

1. **The model floor is `1/8`, identically in `k`.**  The independent-signs model for
   divisor-correlation errors predicts moment-error exponent `k/4`, whose resolution floor
   `(k/4)/(2k)` equals `1/8` for every `k` — so every method confined to what that model sees is
   capped at `1/8`.  The model is exactly correct at `k = 1, 2`, the only indices where the moment of
   `ζ` has a known asymptotic (`E(T) ≍ T^{1/4}`, `E₂(T) ≍ T^{1/2}`, both matched by `Ω`-results).

2. **The neutrality threshold.**  Given an established pointwise exponent `θ` and a perfect `2j`-th
   moment, the whole moment hierarchy delivers exactly `min(1/(2j), θ)`; so the `2j`-th moment
   improves on `θ` iff `j > 1/(2θ)`.  At `θ = 13/84` the threshold is `42/13`, placing the sixth
   moment strictly below it.

3. **The transfer separates.**  The additive-divisor input splits into a pointwise size and a
   shift-cancellation.  Either half alone yields `1/8`; both together yield `m(k) = 1` for every `k`,
   which is the Lindelöf hypothesis.

The module is source-independent: every statement is arithmetic of exponents.
-/
import GaloisForLFunctions.HTGeometry.MomentNeutralityLaw
import GaloisForLFunctions.HTGeometry.MomentChordPivot
import GaloisForLFunctions.HTGeometry.MomentResolutionFloor
import GaloisForLFunctions.HTGeometry.ShiftAverageTransfer

namespace HTGeometry

/-- **Capstone.**  The three quantitative statements of the method-ceiling map, in one place.

`(i)` the independent-signs model has resolution floor `1/8` at every index, and agrees with the
conjectured truth exactly on `[1,2]`;
`(ii)` a perfect `2j`-th moment beats an established exponent `θ` iff `j > 1/(2θ)`, and at
`θ = 13/84` the sixth moment (`j = 3`) fails while the eighth (`j = 4`) succeeds;
`(iii)` the transfer's two halves are each worth `1/8` alone and jointly worth `m(k) = 1`. -/
theorem lindelof_method_ceilings :
    -- (i) the model floor is `1/8` at every index, and the model is exact exactly on `[1,2]`
    (∀ k : ℝ, 0 < k → modelErrorExponent k / (2*k) = 1/8) ∧
    (∀ k : ℝ, 0 < k → (modelErrorExponent k ≤ momentErrorExponent k ↔ 1 ≤ k ∧ k ≤ 2)) ∧
    -- (ii) the neutrality threshold, and its two instances against Bourgain's exponent
    (∀ j θ : ℝ, 0 < j → 0 < θ → (min (1/(2*j)) θ < θ ↔ 1/(2*θ) < j)) ∧
    (min (1 / (2 * (3:ℝ))) bourgainExponent = bourgainExponent) ∧
    (min (1 / (2 * (4:ℝ))) bourgainExponent = 1/8) ∧
    -- (iii) the transfer separates: each half gives `1/8`, both give `m(k) = 1`
    (∀ k : ℝ, 4 ≤ k → transferBound k (1/2) (1 - 1/k) / (2*k) = 1/8) ∧
    (∀ k : ℝ, 4 ≤ k → transferBound k 1 (1/2) / (2*k) = 1/8) ∧
    (∀ k : ℝ, transferBound k (1/2) (1/2) = 1) := by
  refine ⟨fun k hk => model_floor_is_eighth hk,
    fun k hk => model_le_conjecture_iff hk,
    fun j θ hj hθ => momentBound_improves_iff hj hθ,
    sixth_moment_neutral, eighth_moment_improves.1,
    fun k hk => vinogradov_cap hk,
    fun k hk => (conreyGonek_separation hk).1,
    transferBound_conreyGonek⟩

/-- The chord is the image of the single input `(a,b) = (1/2,1)`, and the pivot gain is constant on
it — the two facts that make `1/8` the plateau value rather than a coincidence at one index. -/
theorem chord_is_one_input :
    (∀ k : ℝ, 2 ≤ k → transferBound k (1/2) 1 = momentChord (2*k)) ∧
    (∀ A : ℝ, pivotGain momentChord A = 1/2) :=
  ⟨fun _ hk => transferBound_half_one hk, pivotGain_momentChord⟩

/-- The break criterion, and the fact that `(1/2,1)` fails it with equality on both sides
simultaneously for every `k` — the exact sense in which the chord is critical rather than merely
best-available. -/
theorem chord_criticality :
    (∀ k a b : ℝ, 2 < k →
      (transferBound k a b < momentChord (2*k) ↔ k * (2*a + 2*b - 3) < 4*a - 2)) ∧
    (∀ k : ℝ, k * (2*(1/2 : ℝ) + 2*1 - 3) = 0 ∧ 4*(1/2 : ℝ) - 2 = 0) :=
  ⟨fun _ _ _ hk => transferBound_lt_chord_iff hk, critical_input_equality⟩

end HTGeometry
