import GaloisForLFunctions.RHTower.Sieve.SharedSectorTail
import GaloisForLFunctions.RHTower.Sieve.PrimeRangeSplit
import GaloisForLFunctions.RHTower.MobiusCoprimeEulerMargin

/-!
# The noncoprime pairs have density at most `D²A`

Splitting the union bound at a cut-off `P`, the small primes contribute
`∑_{p ≤ P} D²/(p+1)²` by `(9)` and the large ones are uniformly negligible by `(11)`.  Since every
partial sum of the shared-prime weights is at most `A`, this gives the card's `(12)`:

    B(x,h) / (h√x log 2)  ≤  D²·A + ε   eventually, for every `ε > 0`.

The only input beyond what is already proved is `(9)`, i.e. the bilinear theorem at each rescaled
parameter pair.
-/

namespace RHTower.Sieve

open Finset Filter Topology

/-- The partial sums of the sector densities are bounded by `D²A`. -/
theorem sum_sector_density_le (P : ℕ) :
    ∑ p ∈ Nat.primesLE P, squarefreeDensity ^ (2 : ℕ) / ((p : ℝ) + 1) ^ (2 : ℕ)
      ≤ squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity := by
  have hD : (0 : ℝ) ≤ squarefreeDensity ^ (2 : ℕ) := by positivity
  have hcongr : ∑ p ∈ Nat.primesLE P, squarefreeDensity ^ (2 : ℕ) / ((p : ℝ) + 1) ^ (2 : ℕ)
      = squarefreeDensity ^ (2 : ℕ) * ∑ p ∈ Nat.primesLE P, RHTower.primeSuccInvSq p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [RHTower.primeSuccInvSq, if_pos hp.2]
    ring
  rw [hcongr]
  refine mul_le_mul_of_nonneg_left ?_ hD
  exact RHTower.summable_primeSuccInvSq.sum_le_tsum _
    (fun p _ => RHTower.primeSuccInvSq_nonneg p)

/-- **Card equation (12).**  The noncoprime balanced pairs have density at most `D²A`. -/
theorem eventually_noncoprime_le {hh : ℝ → ℝ}
    (hgrow : Tendsto (fun x => hh x / Real.log (Real.log (3 * x))) atTop atTop)
    (hMR : ∀ p : ℕ, p.Prime → MRBilinearAt (coprimeSquarefreeWeight p)
      (fun x => x / (p : ℝ) ^ (2 : ℕ)) (fun x => hh x / (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop, noncoprimePairCount x (hh x) / (hh x * Real.sqrt x * Real.log 2)
      ≤ squarefreeDensity ^ (2 : ℕ) * RHTower.coprimeSharedPrimeDensity + ε := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hhtop : Tendsto hh atTop atTop := tendsto_of_growth hgrow
  obtain ⟨P, hP1, htail⟩ :=
    exists_sharedSector_tail_small hgrow (ε := ε * Real.log 2 / 2) (by positivity)
  -- the finite part converges
  have hfin : Tendsto (fun x => ∑ p ∈ Nat.primesLE P,
      sharedSectorCount x (hh x) p / (hh x * Real.sqrt x * Real.log 2))
      atTop (𝓝 (∑ p ∈ Nat.primesLE P, squarefreeDensity ^ (2 : ℕ) / ((p : ℝ) + 1) ^ (2 : ℕ))) := by
    refine tendsto_finsetSum _ ?_
    intro p hp
    rw [Nat.mem_primesLE] at hp
    exact tendsto_sharedSector_of_MR hp.2 (hMR p hp.2)
  have hfinev := hfin.eventually (eventually_lt_nhds
    (by linarith : ∑ p ∈ Nat.primesLE P, squarefreeDensity ^ (2 : ℕ) / ((p : ℝ) + 1) ^ (2 : ℕ)
      < ∑ p ∈ Nat.primesLE P, squarefreeDensity ^ (2 : ℕ) / ((p : ℝ) + 1) ^ (2 : ℕ) + ε / 2))
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ((P : ℝ) ^ (2 : ℕ)),
    hhtop.eventually_gt_atTop (0 : ℝ), htail, hfinev] with x hx0 hxP hhx htx hfx
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hden : (0 : ℝ) < hh x * Real.sqrt x * Real.log 2 := by positivity
  -- the cut-off sits inside the range
  have hPle : P ≤ ⌊2 * Real.sqrt x⌋₊ := by
    refine Nat.le_floor ?_
    have hPs : ((P : ℕ) : ℝ) ≤ Real.sqrt x := by
      have h1 : Real.sqrt (((P : ℕ) : ℝ) ^ (2 : ℕ)) ≤ Real.sqrt x := Real.sqrt_le_sqrt hxP
      rwa [Real.sqrt_sq (by positivity)] at h1
    linarith
  have hsplit := noncoprimePairCount_le_split (h := hh x) hx0 hPle
  -- normalise
  have hnorm : noncoprimePairCount x (hh x) / (hh x * Real.sqrt x * Real.log 2)
      ≤ (∑ p ∈ Nat.primesLE P,
          sharedSectorCount x (hh x) p / (hh x * Real.sqrt x * Real.log 2))
        + (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x (hh x) p)
          / (hh x * Real.sqrt x * Real.log 2) := by
    rw [← Finset.sum_div, ← add_div]
    gcongr
  -- the tail, renormalised
  have htail2 : (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x (hh x) p)
      / (hh x * Real.sqrt x * Real.log 2) ≤ ε / 2 := by
    rw [show hh x * Real.sqrt x * Real.log 2 = (hh x * Real.sqrt x) * Real.log 2 from rfl,
      ← div_div]
    rw [div_le_iff₀ hlog2]
    calc (∑ p ∈ bigPrimeSet P ⌊2 * Real.sqrt x⌋₊, sharedSectorCount x (hh x) p)
          / (hh x * Real.sqrt x)
        ≤ ε * Real.log 2 / 2 := htx
      _ = ε / 2 * Real.log 2 := by ring
  have hfinle := hfx.le
  have hsum := sum_sector_density_le P
  linarith

end RHTower.Sieve
