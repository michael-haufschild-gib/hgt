import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawOnAStripSurvivesSummablePoles

/-!
# The jump law on a strip survives finitely many poles on the line

The case of finitely many poles of `TheJumpLawOnAStripSurvivesSummablePoles`: `Φ` has simple
poles at the points of a finite set `P` on the critical line, and `Φ − Σ_{p ∈ P} r_p/(s − p)` is
holomorphic on the strip and bounded near the line.

* `fractSeries_sub_eq_polarPart_of_strip`: the two series of fractional parts differ by the polar
  part `Σ_{p ∈ P} r_p u^p`.
* `eq_of_strip_of_poles`: two families over the same injective scales are equal.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*} {κ : Type*}

/-- Over a finite set the polar series is the polar part. -/
theorem polarSeries_coe_finset (P : Finset ℂ) (r : ℂ → ℂ) (u : ℝ) :
    polarSeries (↑P : Set ℂ) r u = polarPart P r u := by
  unfold polarSeries polarPart
  exact Finset.tsum_subtype' P fun p => r p * (u : ℂ) ^ p

/-- **The two series differ by the polar part, on any strip about the line.** -/
theorem fractSeries_sub_eq_polarPart_of_strip [Countable ι] [Countable κ] {b : ι → ℂ}
    {a : ι → ℝ} {c : κ → ℂ} {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ}
    (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' j, c j * (q j : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    {u : ℝ} (hu : 0 < u) : fractSeries b a u - fractSeries c q u = polarPart P r u := by
  haveI : Countable (↑P : Set ℂ) := P.finite_toSet.countable.to_subtype
  rw [← polarSeries_coe_finset]
  exact fractSeries_sub_eq_polarSeries_of_strip ha hq hη0 hη hR hL (E := (↑P : Set ℂ))
    (fun p hp => hP p (Finset.mem_coe.mp hp)) (P.finite_toSet.summable fun p => ‖r p‖) hFd hFb
    (fun s h1 h2 => by rw [hFR s h1 h2, Finset.tsum_subtype' P fun p => r p / (s - p)])
    (fun s h1 h2 => by rw [hFL s h1 h2, Finset.tsum_subtype' P fun p => r p / (s - p)]) hu

/-- **The zeros of `ζ` cancel no pole of a two-sided expansion, up to finitely many.** Two
families over the same injective positive scales that represent, on the two sides of the line, a
function `−(ζ/s) G − Σ_{p ∈ P} r_p/(s − p)` holomorphic on the strip and bounded near the line
are equal. The index set may be uncountable. -/
theorem eq_of_strip_of_poles {b c : ι → ℂ} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hinj : Function.Injective a) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun i => ‖c i‖ * a i ^ σ)
    {P : Finset ℂ} {r : ℂ → ℂ} (hP : ∀ p ∈ P, p.re = 1 / 2)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * (∑' i, b i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p))
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * (∑' i, c i * (a i : ℂ) ^ s) - ∑ p ∈ P, r p / (s - p)) :
    b = c := by
  haveI : Countable (↑P : Set ℂ) := P.finite_toSet.countable.to_subtype
  exact eq_of_strip_of_summable_poles ha hinj hη0 hη hR hL (E := (↑P : Set ℂ))
    (fun p hp => hP p (Finset.mem_coe.mp hp)) (P.finite_toSet.summable fun p => ‖r p‖) hFd hFb
    (fun s h1 h2 => by rw [hFR s h1 h2, Finset.tsum_subtype' P fun p => r p / (s - p)])
    (fun s h1 h2 => by rw [hFL s h1 h2, Finset.tsum_subtype' P fun p => r p / (s - p)])

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
