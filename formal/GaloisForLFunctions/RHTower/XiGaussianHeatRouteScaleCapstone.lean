import GaloisForLFunctions.RHTower.XiGaussianHeatHankelSincLevelWitness
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLargeTimeInertia
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelLinearWindow

/-!
# Route HCF across heat-time scales

The heat Hankel ladder `Δ_k(a) = det(M_{i+j}(a))_{i,j<k}` at rank `n + 1` and time `a`
(`hcf_scale_capstone`):

1. **Small time, unconditional.**  `Δ_N(a) > 0` whenever `aN ≤ κ`, an explicit constant.
2. **Small time, sharp.**  RH holds iff for every `K > 0`, eventually all `Δ_k(K/n)` with
   `k ≤ n + 1` are positive.  Without RH some `K` has `Δ_k(K/n) ≤ 0` for all large `n`: the window
   has order exactly `1/N`, and the RH content of the ladder is the unboundedness of its constant.
3. **No intermediate growth.**  For any `f → ∞`, RH holds iff the window `a ≤ f(n)/n` is eventually
   admissible.
4. **Large time, exact.**  For every level `L`, eventually in `a` the negative index of the
   rank-`|S_L|` section is the number of upper off-line heat frequencies of real part `≤ L`.  Hence
   RH holds iff every level is eventually positive definite.

So the producer of the route is one statement: the window constant is unbounded, which is
all-aperture Weil positivity.
-/

open Filter
open GaloisForLFunctions.HTGeometry (leadingMatrix hermNegIndex)

namespace RHTower

theorem hcf_scale_capstone :
    (∀ (N : ℕ) (a : ℝ), 0 < a → a * N ≤ routeUCompletedPrimeGammaAperture →
        0 < (leadingMatrix (heatMomentArray a) N).det) ∧
    (RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ n : ℕ in atTop,
        ∀ k ≤ n + 1, 0 < (leadingMatrix (heatMomentArray (K / n)) k).det) ∧
    (¬ RiemannHypothesis → ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
        ∃ k ≤ n + 1, (leadingMatrix (heatMomentArray (K / n)) k).det ≤ 0) ∧
    (∀ f : ℕ → ℝ, Tendsto f atTop atTop → (RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
        0 < a → a ≤ f n / n → ∀ k ≤ n + 1, 0 < (leadingMatrix (heatMomentArray a) k).det)) ∧
    (∀ L : ℝ, ∀ᶠ a in atTop, hermNegIndex (heatMomentSection a (heatFrequenciesBelow L).card) =
        (lowUpperHeatFrequencies L).card) ∧
    (RiemannHypothesis ↔ ∀ L : ℝ, ∀ᶠ a in atTop,
        hermNegIndex (heatMomentSection a (heatFrequenciesBelow L).card) = 0) :=
  ⟨fun _ _ ha hwin => heatMomentDet_pos_of_mul_le ha hwin,
    riemannHypothesis_iff_forall_eventually_heatMomentDet_pos_scaled,
    exists_pos_eventually_exists_heatMomentDet_nonpos_of_not_riemannHypothesis,
    fun _ hf => riemannHypothesis_iff_eventually_growing_window hf,
    eventually_hermNegIndex_heatMomentSection_eq,
    riemannHypothesis_iff_forall_eventually_hermNegIndex_eq_zero⟩

end RHTower
