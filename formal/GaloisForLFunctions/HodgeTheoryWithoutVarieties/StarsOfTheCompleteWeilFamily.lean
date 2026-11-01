import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeOfTheCompleteWeilFamily
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsAreLowerHorizons

/-!
# Stars of the complete Weil family

At resolution `(c, N)` the complete Weil family places atoms of width `w = c/N` at `log n`,
`n ≤ N`. The atoms on the star of `d` sit at `log d + log m`, `m ≤ ⌊N/d⌋`. They are the atoms of
horizon `⌊N/d⌋` translated by `log d`, with the same width. That width is the width at horizon
`⌊N/d⌋` and overlap `c' = c⌊N/d⌋/N`. Weil's form is translation invariant, for every weight
(`weilQuadTw_comp_sub`), so:

* **star law for every weight** (`weilQuadTw_atomicTest_starRestrict`): the twisted Weil form of a
  test supported on the star is the form of the lower-horizon test. Geometric self-similarity is
  blind to the weight; only the counterterm selects (`TheDivisorIdentitySelects`).
* **star law of the complete family** (`completeWeilEnergy_starEmbed`): the star embedding
  `starEmbed d N` is an isometry from the complete Weil family at `(c', ⌊N/d⌋)` to the family at
  `(c, N)`.
* **renormalization-group monotonicity** (`positiveAt_div`, `twinPositiveAt_div`,
  `hyperplanePositiveAt_div`): positivity at `(c, N)` descends to every star `(c⌊N/d⌋/N, ⌊N/d⌋)`.
  Negative directions can only appear first at the top of the divisor lattice and propagate
  upwards.
* **local Hodge–Riemann on deep stars** (`exists_star_positive_tiltedUnitSpline`): for the tilted
  spline there is a horizon `M₀` such that at every resolution `(c, N)` the star of every `d` with
  `⌊N/d⌋ ≥ M₀` and `1 ≤ c⌊N/d⌋/N < (log⌊N/d⌋)^α`, `α < α*`, is positive. The stars of `d` beyond
  a polylogarithm of the overlap sink into the universal regime.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace
open GaloisForLFunctions.EdgeHodgeTheory GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- **Atoms on a star are translated lower-horizon atoms.** -/
theorem atomicTest_starRestrict {d : ℕ} (hd : 0 < d) (N : ℕ) (G : ℕ → ℝ) (g : ℝ → ℝ) (u : ℝ) :
    atomicTest N (starRestrict d G) g u =
      atomicTest (N / d) (starPullback d G) g (u - Real.log d) := by
  unfold atomicTest
  rw [sum_Icc_star hd N]
  · refine sum_congr rfl fun a ha => ?_
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (mem_Icc.mp ha).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    simp only [starRestrict, starPullback, if_pos (dvd_mul_right d a), Nat.cast_mul,
      Real.log_mul hd0.ne' ha0.ne']
    ring_nf
  · intro n hn
    simp [starRestrict, if_neg hn]

/-- **The star law for every weight.** -/
theorem weilQuadTw_atomicTest_starRestrict (lam : ℕ → ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ)
    (G : ℕ → ℝ) (g : ℝ → ℝ) :
    weilQuadTw lam (atomicTest N (starRestrict d G) g) =
      weilQuadTw lam (atomicTest (N / d) (starPullback d G) g) := by
  have : atomicTest N (starRestrict d G) g =
      fun u => atomicTest (N / d) (starPullback d G) g (u - Real.log d) :=
    funext (atomicTest_starRestrict hd N G g)
  rw [this, weilQuadTw_comp_sub]

/-- The overlap of the star of `d`: `c' = c⌊N/d⌋/N`. -/
def starOverlap (c : ℝ) (N d : ℕ) : ℝ := c * (N / d : ℕ) / N

theorem starOverlap_div {c : ℝ} {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    starOverlap c N d / (N / d : ℕ) = c / N := by
  have hM : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast Nat.div_pos hdN hd
  have hN : (0 : ℝ) < N := by exact_mod_cast (hd.trans_le hdN)
  rw [starOverlap]
  field_simp

theorem starOverlap_pos {c : ℝ} (hc : 0 < c) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    0 < starOverlap c N d := by
  have hM : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast Nat.div_pos hdN hd
  have hN : (0 : ℝ) < N := by exact_mod_cast (hd.trans_le hdN)
  rw [starOverlap]
  positivity

/-- **Twisted positivity descends to stars**, for every weight. -/
theorem twinPositiveAt_div (lam : ℕ → ℝ) {φ : ℝ → ℝ} {c : ℝ} {N d : ℕ} (hd : 0 < d)
    (hdN : d ≤ N) (h : TwinPositiveAt lam φ c N) :
    TwinPositiveAt lam φ (starOverlap c N d) (N / d) := by
  intro y
  rw [starOverlap_div hd hdN]
  have hy : starPullback d (fun n => y (n / d)) = y := by
    funext a
    simp only [starPullback, Nat.mul_div_cancel_left a hd]
  rw [← hy, ← weilQuadTw_atomicTest_starRestrict lam hd]
  exact h _

/-- The **star embedding**: a vector at horizon `⌊N/d⌋` placed on the multiples of `d`. -/
def starEmbed (d N : ℕ) (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d))) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 fun n => if d ∣ (n : ℕ) then primeHorizonExtension y ((n : ℕ) / d) else 0

theorem primeHorizonExtension_starEmbed {d : ℕ} (hd : 0 < d) (N : ℕ)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d))) :
    primeHorizonExtension (starEmbed d N y) =
      starRestrict d fun n => primeHorizonExtension y (n / d) := by
  funext n
  by_cases hn : n ∈ Icc 1 N
  · simp only [primeHorizonExtension, dif_pos hn, starEmbed, starRestrict]
  · simp only [primeHorizonExtension, dif_neg hn, starRestrict]
    split_ifs with hdn h2
    · obtain ⟨a, rfl⟩ := hdn
      exfalso
      refine hn (mem_Icc.mpr ⟨Nat.mul_pos hd ?_, ?_⟩)
      · rw [Nat.mul_div_cancel_left a hd] at h2
        exact (mem_Icc.mp h2).1
      · rw [Nat.mul_div_cancel_left a hd] at h2
        have := (Nat.le_div_iff_mul_le hd).mp (mem_Icc.mp h2).2
        rw [mul_comm]; exact this
    · rfl
    · rfl

/-- **The star law of the complete Weil family.** The star embedding is an isometry from the
family at `(c⌊N/d⌋/N, ⌊N/d⌋)` to the family at `(c, N)`. -/
theorem completeWeilEnergy_starEmbed {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c) {N d : ℕ} (hd : 0 < d)
    (hdN : d ≤ N) (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d))) :
    completeWeilEnergy φ c N (starEmbed d N y) =
      completeWeilEnergy φ (starOverlap c N d) (N / d) y := by
  have hN : 1 ≤ N := hd.trans_le hdN
  have hM : 1 ≤ N / d := Nat.div_pos hdN hd
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN, completeWeilEnergy,
    completeWeilMatrix_inner_eq_weilQuad hφ hsupp (starOverlap_pos hc hd hdN) hM,
    starOverlap_div hd hdN, primeHorizonExtension_starEmbed hd]
  congr 1
  have hpull : starPullback d (fun n => primeHorizonExtension y (n / d)) =
      primeHorizonExtension y := by
    funext a
    simp only [starPullback, Nat.mul_div_cancel_left a hd]
  exact (weilQuadTw_atomicTest_starRestrict _ hd N _ _).trans (by rw [hpull]; rfl)

/-- **Positivity descends to stars.** -/
theorem positiveAt_div {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) (h : PositiveAt φ c N) :
    PositiveAt φ (starOverlap c N d) (N / d) := fun y => by
  rw [← completeWeilEnergy_starEmbed hφ hsupp hc hd hdN]
  exact h _

/-- The pole pairing of a star embedding is the pole pairing at the lower horizon, divided by
`√d`. -/
theorem sum_starEmbed_div_sqrt {d : ℕ} (hd : 0 < d) (N : ℕ)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d))) :
    ∑ n ∈ Icc 1 N, primeHorizonExtension (starEmbed d N y) n / Real.sqrt n =
      (Real.sqrt d)⁻¹ * ∑ a ∈ Icc 1 (N / d), primeHorizonExtension y a / Real.sqrt a := by
  rw [primeHorizonExtension_starEmbed hd, sum_Icc_star hd N, mul_sum]
  · refine sum_congr rfl fun a _ => ?_
    simp only [starRestrict, if_pos (dvd_mul_right d a), Nat.mul_div_cancel_left a hd,
      Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg d)]
    field_simp
  · intro n hn
    simp [starRestrict, if_neg hn]

/-- **Hyperplane positivity descends to stars.** A primitive vector of the lower horizon (zero
harmonic pole pairing) embeds as a primitive vector of the star. -/
theorem hyperplanePositiveAt_div {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c) {N d : ℕ} (hd : 0 < d)
    (hdN : d ≤ N) (h : HyperplanePositiveAt φ c N)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d)))
    (hy : ∑ a ∈ Icc 1 (N / d), primeHorizonExtension y a / Real.sqrt a = 0) :
    0 ≤ completeWeilEnergy φ (starOverlap c N d) (N / d) y := by
  rw [← completeWeilEnergy_starEmbed hφ hsupp hc hd hdN]
  refine h _ ?_
  rw [RenormalizedIntersectionTheory.inner_normalizedRamanujanHorizonVector_one,
    sum_starEmbed_div_sqrt hd, hy, mul_zero, mul_zero]

/-- **Local Hodge–Riemann on deep stars.** For the tilted spline and every `α < α*` there is a
horizon `M₀` such that, at every resolution `(c, N)`, the complete Weil form is nonnegative on the
star of every `d` with `⌊N/d⌋ ≥ M₀` and `1 ≤ c⌊N/d⌋/N < (log ⌊N/d⌋)^α`. -/
theorem exists_star_positive_tiltedUnitSpline {α : ℝ} (hα : 0 < α)
    (hα' : α < CriticalArithmeticCorrelationTheory.powerLogPositivityExponent) :
    ∃ M₀ : ℕ, ∀ (c : ℝ) (N d : ℕ), 0 < c → 0 < d → d ≤ N → M₀ ≤ N / d →
      1 ≤ starOverlap c N d → starOverlap c N d < Real.log (N / d : ℕ) ^ α →
      ∀ y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d)),
        0 ≤ completeWeilEnergy tiltedUnitSpline c N (starEmbed d N y) := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (eventually_ofReal_rpow_log_le_edge_tiltedUnitSpline hα hα')
  refine ⟨M₀, fun c N d hc hd hdN hM h1 hlt y => ?_⟩
  rw [completeWeilEnergy_starEmbed admissible_tiltedUnitSpline.contDiff
    admissible_tiltedUnitSpline.supp hc hd hdN]
  have hedge := hM₀ (N / d) hM
  have hpos : PositiveAt tiltedUnitSpline (starOverlap c N d) (N / d) :=
    of_ofReal_lt_firstFailure h1
      (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by
        have : 0 < starOverlap c N d := by linarith
        linarith)).mpr hlt) hedge)
  exact hpos y

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
