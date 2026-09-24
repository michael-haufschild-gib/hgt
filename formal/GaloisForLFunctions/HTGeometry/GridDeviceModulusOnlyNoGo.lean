import GaloisForLFunctions.HTGeometry.GridDeviceGainScaleInvariance

/-!
# No modulus-only bound closes the grid cancellation device

The device counts zeros of `f` on a window from the surplus `∫|f| − ∑_j |∫_{I_j} f|`.  Write `m j`
for the absolute mass of `f` on cell `j`; the signed cell integrals satisfy `|∫_{I_j} f| ≤ m j`, and
a bound for the summed cancellation that depends only on `|f|` is one valid for **every** sign
pattern compatible with those masses.

Any such bound is at least `∑_j m j = ∫|f|`, because the pattern with no sign changes — realised by
`|f|` itself — attains it.  So the surplus it yields is never positive.

This covers Cauchy–Schwarz, Hölder at every exponent, and every moment estimate at once: they all
factor through `|f|`.  Closing the device requires an estimate that uses where `f` changes sign, not
how large it is.
-/

open Finset

namespace HTGeometry

/-- **No modulus-only bound can close the grid device.**  Let `m i` be the absolute mass of `f` on
cell `i`, so that the signed cell integrals `c i` satisfy `|c i| ≤ m i`, and let `Φ` be any bound
for the summed cancellation that is valid for **every** sign pattern compatible with those masses —
which is exactly what a bound depending only on `|f|` is.  Applying it to the pattern `c = m`,
realised by `|f|` itself, forces `Φ` to be at least the total absolute mass.

Since the grid device needs `Bsum < ∫|f| = ∑ m i`, no such bound can ever produce a positive
surplus: Cauchy–Schwarz, Hölder at any exponent, and every moment estimate are of this kind. -/
theorem no_modulus_only_cell_bound {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) {Φ : ℝ}
    (hΦ : ∀ c : ι → ℝ, (∀ i ∈ s, |c i| ≤ m i) → ∑ i ∈ s, |c i| ≤ Φ) :
    ∑ i ∈ s, m i ≤ Φ := by
  have h := hΦ m (fun i hi => by rw [abs_of_nonneg (hm i hi)])
  calc ∑ i ∈ s, m i = ∑ i ∈ s, |m i| :=
        Finset.sum_congr rfl fun i hi => (abs_of_nonneg (hm i hi)).symm
    _ ≤ Φ := h

/-- The grid surplus is nonpositive for every modulus-only cancellation bound. -/
theorem grid_surplus_nonpos_of_modulus_only {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) {Φ L : ℝ} (hL : L ≤ ∑ i ∈ s, m i)
    (hΦ : ∀ c : ι → ℝ, (∀ i ∈ s, |c i| ≤ m i) → ∑ i ∈ s, |c i| ≤ Φ) :
    L - Φ ≤ 0 := by
  have h := no_modulus_only_cell_bound s m hm hΦ
  linarith

end HTGeometry
