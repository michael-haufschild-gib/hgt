import GaloisForLFunctions.RHTower.HeatAperturePrimeSeamReflection
import GaloisForLFunctions.HTGeometry.ArbitraryLabelEndReconstruction

/-!
# One-ended cofinal collapse of the canonical prime seam

The canonical FE--Schwarz seam charge is an arbitrary complex label on the primes.  On an infinite
preconnected graph with the finite-boundary one-ended property, finiteness of the set of edges
across which the seam changes forces the seam to be constant away from a finite set of primes.
Cofinal decay of the seam kills that constant, and a single vanishing seam pins the critical line.

The prime ray is the sparsest instance: eventual equality of consecutive seam values along the
increasing enumeration of the primes already forces `Re rho = 1/2`.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Cofinal equality of the canonical prime seam with a fixed value forces that value to vanish.
Only decay of the seam and the existence of arbitrarily large primes are used. -/
theorem common_eq_zero_of_cofinal_primeSeamCharge_eq
    {rho c : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hcof : ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧
      orbitwiseNatPrimeSeamCharge p rho = c) :
    c = 0 := by
  have hlim := tendsto_orbitwiseNatPrimeSeamCharge hstrip
  by_contra hne
  have hc0 : 0 < dist c 0 := dist_pos.mpr hne
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) (dist c 0) hc0
  obtain ⟨p, hNp, _, hp⟩ := hcof N
  have hlt := hN p hNp
  rw [hp] at hlt
  exact (lt_irrefl _ hlt).elim

/-- A seam value attained outside a finite set of primes is attained cofinally. -/
theorem cofinal_of_finite_exceptional_primes
    {rho c : ℂ} {E : Set ℕ} (hE : E.Finite)
    (hout : ∀ p : ℕ, p.Prime → p ∉ E → orbitwiseNatPrimeSeamCharge p rho = c)
    (N : ℕ) :
    ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ orbitwiseNatPrimeSeamCharge p rho = c := by
  classical
  obtain ⟨B, hB⟩ := hE.bddAbove
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max N (B + 1))
  refine ⟨p, le_trans (le_max_left _ _) hple, hp, hout p hp ?_⟩
  intro hmem
  have : p ≤ B := hB hmem
  have : B + 1 ≤ p := le_trans (le_max_right _ _) hple
  omega

/-- **Prime-seam one-ended collapse.**  On an infinite preconnected one-ended prime graph,
finitely many seam-varying edges force the critical line at that divisor point. -/
theorem re_eq_half_of_finite_seam_edgeVariation
    {G : SimpleGraph Nat.Primes} (hconn : G.Preconnected)
    (hG : GaloisForLFunctions.HTGeometry.FiniteBoundaryOneEnded G)
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hvar : (GaloisForLFunctions.HTGeometry.edgeVariation G
      (fun p : Nat.Primes => orbitwiseNatPrimeSeamCharge (p : ℕ) rho)).Finite) :
    rho.re = 1 / 2 := by
  classical
  obtain ⟨c, hc⟩ :=
    GaloisForLFunctions.HTGeometry.eventuallyConstant_of_finite_edgeVariation_of_preconnected
      hconn hG _ hvar
  set E : Set ℕ := Subtype.val '' {v : Nat.Primes | orbitwiseNatPrimeSeamCharge (v : ℕ) rho ≠ c}
    with hEdef
  have hEfin : E.Finite := hc.image _
  have hout : ∀ p : ℕ, p.Prime → p ∉ E → orbitwiseNatPrimeSeamCharge p rho = c := by
    intro p hp hpE
    by_contra hne
    exact hpE ⟨⟨p, hp⟩, hne, rfl⟩
  have hcof := cofinal_of_finite_exceptional_primes (rho := rho) (c := c) hEfin hout
  have hczero : c = 0 := common_eq_zero_of_cofinal_primeSeamCharge_eq hstrip hcof
  obtain ⟨p, _, hp, hpc⟩ := hcof 0
  rw [hczero] at hpc
  exact (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half rho p hp).mp hpc

/-- The increasing enumeration of the primes. -/
def primeRay (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem primeRay_prime (n : ℕ) : (primeRay n).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

theorem primeRay_strictMono : StrictMono primeRay :=
  fun _ _ h => (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr h

theorem le_primeRay (n : ℕ) : n ≤ primeRay n :=
  primeRay_strictMono.le_apply

/-- **Prime-ray form.**  Eventual equality of consecutive seam values along the increasing prime
enumeration already forces the critical line. -/
theorem re_eq_half_of_eventually_const_primeRay_seam
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hray : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      orbitwiseNatPrimeSeamCharge (primeRay n) rho =
        orbitwiseNatPrimeSeamCharge (primeRay (n + 1)) rho) :
    rho.re = 1 / 2 := by
  obtain ⟨N, hN⟩ := hray
  set c : ℂ := orbitwiseNatPrimeSeamCharge (primeRay N) rho with hcdef
  have hconst : ∀ n : ℕ, N ≤ n → orbitwiseNatPrimeSeamCharge (primeRay n) rho = c := by
    intro n hn
    induction n with
    | zero => simpa using (Nat.le_zero.mp hn) ▸ rfl
    | succ m ih =>
        rcases Nat.lt_or_ge N (m + 1) with hlt | hge
        · have hm : N ≤ m := Nat.lt_succ_iff.mp hlt
          exact ((hN m hm).symm).trans (ih hm)
        · have : N = m + 1 := le_antisymm hn hge
          rw [← this]
  have hcof : ∀ M : ℕ, ∃ p : ℕ, M ≤ p ∧ p.Prime ∧
      orbitwiseNatPrimeSeamCharge p rho = c := by
    intro M
    refine ⟨primeRay (max N M), le_trans (le_max_right N M) (le_primeRay _),
      primeRay_prime _, hconst _ (le_max_left N M)⟩
  have hczero : c = 0 := common_eq_zero_of_cofinal_primeSeamCharge_eq hstrip hcof
  have hzero : orbitwiseNatPrimeSeamCharge (primeRay N) rho = 0 := by
    rw [← hcdef, hczero]
  exact (GaloisForLFunctions.orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half rho _ (primeRay_prime N)).mp hzero

end

end RHTower
