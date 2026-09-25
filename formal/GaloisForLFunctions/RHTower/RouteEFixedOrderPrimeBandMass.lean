import GaloisForLFunctions.RHTower.RouteEFixedOrderSelectedFibreBoundary
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

open Set Finset Filter Real
namespace RHTower
noncomputable section

/-- Primes in a natural-number window, represented as prime subtypes. -/
def routeEPrimeWindow (a b : ℕ) : Finset Nat.Primes :=
  (GaloisForLFunctions.HTGeometry.primesInIoc a b).attach.image
    (fun p => (⟨p.1,
      (GaloisForLFunctions.HTGeometry.mem_primesInIoc p.2).1⟩ : Nat.Primes))

theorem routeEPrimeWindow_card (a b : ℕ) :
    (routeEPrimeWindow a b).card =
      (GaloisForLFunctions.HTGeometry.primesInIoc a b).card := by
  unfold routeEPrimeWindow
  rw [Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro x y h
    apply Subtype.ext
    exact congrArg (fun z : Nat.Primes => (z : ℕ)) h

theorem routeEPrimeWindow_mem {a b : ℕ} {p : Nat.Primes}
    (hp : p ∈ routeEPrimeWindow a b) : a < (p : ℕ) ∧ (p : ℕ) ≤ b := by
  unfold routeEPrimeWindow at hp
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hp
  have hm := (GaloisForLFunctions.HTGeometry.mem_primesInIoc x.2).2
  have hv : (p : ℕ) = x.1 := congrArg Subtype.val hx.symm
  simpa [hv] using hm

/-- Every pair in the two source windows lies in the fixed far-cone ratio band. -/
theorem routeEPrimePairBand_ratio {N : ℕ} {p q : Nat.Primes}
    (hp : p ∈ routeEPrimeWindow N (2 * N))
    (hq : q ∈ routeEPrimeWindow (512 * N) (1024 * N)) :
    (1 / 1024 : ℝ) ≤ ((p : ℝ) / (q : ℝ)) ∧
      ((p : ℝ) / (q : ℝ)) ≤ (1 / 256 : ℝ) := by
  obtain ⟨hqlo,hqhi⟩ := routeEPrimeWindow_mem hq
  obtain ⟨hplo,hphi⟩ := routeEPrimeWindow_mem hp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have hqhi' : (q : ℝ) ≤ 1024 * (N : ℝ) := by exact_mod_cast hqhi
  have hqlo' : (512 : ℝ) * N < (q : ℝ) := by exact_mod_cast hqlo
  have hplo' : (N : ℝ) < (p : ℝ) := by exact_mod_cast hplo
  have hphi' : (p : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hphi
  constructor
  · apply (le_div_iff₀ hq0).2
    nlinarith
  · apply (div_le_iff₀ hq0).2
    nlinarith

/-- Literal full-cofactor prime-numerator source restricted to two disjoint
proportional prime windows. -/
def routeEPrimePairBandMass (r : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ routeEPrimeWindow (512 * N) (1024 * N),
    ∑ p ∈ routeEPrimeWindow N (2 * N),
      routeEFixedOrderPrimeFibre r p q

/-- Uniform finite-block lower bound; one constant works for every cutoff. -/
theorem routeEPrimePairBandMass_ge
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      C * ((routeEPrimeWindow N (2 * N)).card : ℝ) *
          ((routeEPrimeWindow (512 * N) (1024 * N)).card : ℝ) *
          ((1024 * N : ℕ) : ℝ) ^ (-r) ≤ routeEPrimePairBandMass r N := by
  obtain ⟨C, hC, hband⟩ := exists_routeEPrimeBandFloor hr
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hterm (q : Nat.Primes) (hq : q ∈ routeEPrimeWindow (512 * N) (1024 * N))
      (p : Nat.Primes) (hp : p ∈ routeEPrimeWindow N (2 * N)) :
      C * ((1024 * N : ℕ) : ℝ) ^ (-r) ≤ routeEFixedOrderPrimeFibre r p q := by
    obtain ⟨_,hqhi⟩ := routeEPrimeWindow_mem hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
    obtain ⟨hlo,hhi⟩ := routeEPrimePairBand_ratio hp hq
    have hfloor := hband p q hlo hhi
    have hpower : ((1024 * N : ℕ) : ℝ) ^ (-r) ≤ (q : ℝ) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos hq0 (by exact_mod_cast hqhi) (by linarith)
    exact (mul_le_mul_of_nonneg_left hpower hC.le).trans hfloor
  unfold routeEPrimePairBandMass
  calc
    C * ((routeEPrimeWindow N (2 * N)).card : ℝ) *
        ((routeEPrimeWindow (512 * N) (1024 * N)).card : ℝ) *
        ((1024 * N : ℕ) : ℝ) ^ (-r) =
      ∑ q ∈ routeEPrimeWindow (512 * N) (1024 * N),
        ∑ p ∈ routeEPrimeWindow N (2 * N),
          C * ((1024 * N : ℕ) : ℝ) ^ (-r) := by
            simp only [Finset.sum_const,
              nsmul_eq_mul]
            ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro p hp
      exact hterm q hq p hp

/-- The disjoint adjacent composite-numerator source on the same two windows. -/
def routeECompositePairBandMass (r : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ routeEPrimeWindow (512 * N) (1024 * N),
    ∑ p ∈ routeEPrimeWindow N (2 * N),
      routeEFixedOrderIntegerNumeratorFibre r (2 * (p : ℕ)) q

/-- Uniform negative composite block.  It is not an assertion about the sum of
prime and composite blocks, or about the complete Gamma--Hankel covariance. -/
theorem routeECompositePairBandMass_le
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      routeECompositePairBandMass r N ≤
        -C * ((routeEPrimeWindow N (2 * N)).card : ℝ) *
          ((routeEPrimeWindow (512 * N) (1024 * N)).card : ℝ) *
          ((1024 * N : ℕ) : ℝ) ^ (-r) := by
  obtain ⟨C, hC, hband⟩ := exists_routeECompositeBandFloor hr
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hterm (q : Nat.Primes) (hq : q ∈ routeEPrimeWindow (512 * N) (1024 * N))
      (p : Nat.Primes) (hp : p ∈ routeEPrimeWindow N (2 * N)) :
      routeEFixedOrderIntegerNumeratorFibre r (2 * (p : ℕ)) q ≤
        -C * ((1024 * N : ℕ) : ℝ) ^ (-r) := by
    obtain ⟨_,hqhi⟩ := routeEPrimeWindow_mem hq
    obtain ⟨hplo,_⟩ := routeEPrimeWindow_mem hp
    have hp3 : 3 ≤ (p : ℕ) := by omega
    obtain ⟨hlo,hhi⟩ := routeEPrimePairBand_ratio hp hq
    have hfloor := hband p q hp3 hlo hhi
    have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
    have hpower : ((1024 * N : ℕ) : ℝ) ^ (-r) ≤ (q : ℝ) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos hq0 (by exact_mod_cast hqhi) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hpower hC.le]
  unfold routeECompositePairBandMass
  calc
    (∑ q ∈ routeEPrimeWindow (512 * N) (1024 * N),
        ∑ p ∈ routeEPrimeWindow N (2 * N),
          routeEFixedOrderIntegerNumeratorFibre r (2 * (p : ℕ)) q) ≤
      ∑ q ∈ routeEPrimeWindow (512 * N) (1024 * N),
        ∑ p ∈ routeEPrimeWindow N (2 * N),
          -C * ((1024 * N : ℕ) : ℝ) ^ (-r) := by
            apply Finset.sum_le_sum
            intro q hq
            apply Finset.sum_le_sum
            intro p hp
            exact hterm q hq p hp
    _ = -C * ((routeEPrimeWindow N (2 * N)).card : ℝ) *
        ((routeEPrimeWindow (512 * N) (1024 * N)).card : ℝ) *
        ((1024 * N : ℕ) : ℝ) ^ (-r) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring

end
end RHTower
