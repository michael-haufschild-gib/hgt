/-
Completed-carrier analytic charge on the reflected saddle/grid carrier.

This instantiates the analytic reflected-grid charge package with the concrete completed
finite carrier `completedGN N`.  The remaining geometric data is now explicit:

* centers are paired by the reflection `s ↦ 1-s` under factor swap;
* centers lie in the open critical strip;
* diagonal fixed collisions have center `1/2`;
* local orders are finite.

Under those hypotheses, the completed-carrier reflected charge is even and hence invisible
to the level-two deck reduction.
-/
import GaloisForLFunctions.RHTower.ReflectedGridAnalyticCharge
import GaloisForLFunctions.RHTower.ZetaCarrier

open Complex Real Filter Topology
open scoped BigOperators

namespace RHTower

/-- The reflected grid charge instantiated with the concrete completed finite carrier
`completedGN N`. -/
noncomputable def reflectedGridCompletedCharge (C N : ℕ) (center : ℕ × ℕ → ℂ) : ℕ :=
  reflectedGridAnalyticCharge C (fun _ => completedGN N) center

/-- The completed finite carrier is locally reflection-symmetric at the FE fixed point. -/
theorem completedGN_eventually_reflection_half (N : ℕ) :
    ∀ᶠ s in 𝓝 (1 / 2 : ℂ), completedGN N (2 * (1 / 2 : ℂ) - s) = completedGN N s := by
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hhalf : (1 / 2 : ℂ) ∈ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    norm_num [Complex.div_re]
  filter_upwards [hopen.mem_nhds hhalf] with s hs
  have h := completedGN_one_sub (N := N) hs.1 hs.2
  simpa [show (2 * (1 / 2 : ℂ) - s) = 1 - s by ring] using h

/-- **Completed-carrier reflected-grid charge parity.**  If factor swap sends centers to
`1-center`, all centers lie in the strip, diagonal centers are the FE fixed point `1/2`, and
the local orders are finite, then the completed-carrier analytic charge is even. -/
theorem reflectedGridCompletedCharge_even_of_center_swap {C N : ℕ} {center : ℕ × ℕ → ℂ}
    (hcenter : ∀ x ∈ reflectedGridCollisions C,
      center (reflectedGridSwap x) = 1 - center x)
    (hstrip : ∀ x ∈ reflectedGridCollisions C, 0 < (center x).re ∧ (center x).re < 1)
    (hdiag_center : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 → center x = (1 / 2 : ℂ))
    (hfinite : ∀ x ∈ reflectedGridCollisions C,
      analyticOrderAt (completedGN N) (center x) ≠ ⊤) :
    Even (reflectedGridCompletedCharge C N center) := by
  unfold reflectedGridCompletedCharge reflectedGridAnalyticCharge
  apply reflectedGridWeightedCharge_even_of_swap_invariant_even_fixed
  · intro x hx
    rw [hcenter x hx]
    exact congrArg ENat.toNat
      (completedGN_orderAt_one_sub (N := N) (hstrip x hx).1 (hstrip x hx).2)
  · intro x hx hdiag
    have hc := hdiag_center x hx hdiag
    exact analyticOrderAt_even_of_reflection_eventually
      (by
        rw [hc]
        exact completedGN_analyticAt (N := N) (by norm_num) (by norm_num))
      (by
        rw [hc]
        exact completedGN_eventually_reflection_half N)
      (hfinite x hx)

/-- Deck form of `reflectedGridCompletedCharge_even_of_center_swap`. -/
theorem reflectedGridCompletedCharge_deckRed_two_eq_one_of_center_swap {C N : ℕ}
    {center : ℕ × ℕ → ℂ}
    (hcenter : ∀ x ∈ reflectedGridCollisions C,
      center (reflectedGridSwap x) = 1 - center x)
    (hstrip : ∀ x ∈ reflectedGridCollisions C, 0 < (center x).re ∧ (center x).re < 1)
    (hdiag_center : ∀ x ∈ reflectedGridCollisions C, x.1 = x.2 → center x = (1 / 2 : ℂ))
    (hfinite : ∀ x ∈ reflectedGridCollisions C,
      analyticOrderAt (completedGN N) (center x) ≠ ⊤) :
    deckRed 2 (↑(reflectedGridCompletedCharge C N center)) = 1 := by
  rw [deckRed_two_eq_one_iff]
  exact_mod_cast reflectedGridCompletedCharge_even_of_center_swap
    hcenter hstrip hdiag_center hfinite

end RHTower
