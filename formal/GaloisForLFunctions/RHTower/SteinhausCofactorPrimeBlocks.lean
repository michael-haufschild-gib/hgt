import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
import GaloisForLFunctions.RHTower.SteinhausLargestPrimeDecomposition

/-!
# Actual prime blocks reciprocal to coherent cofactor blocks

The primes in `(N/(2*M), N/M]` have cofactor cutoff in `[M, 2*M)`. The proved PNT window
bound gives at least `N/(4*M*log N)` such primes eventually, retaining the factor required
by the coherent mode energy budget. Separated cofactor blocks give disjoint prime sets.

One common moving conditioning threshold `N/(2*K)` contains all constructed cofactors and
lies below all selected prime blocks when `M <= K`. It eventually satisfies the exact
largest-prime decomposition seam `N < (N/(2*K))^2`.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower
open GaloisForLFunctions.HTGeometry

/-- Actual primes whose reciprocal cofactor scale lies in one constructed block. -/
def cofactorPrimeBlock (M N : ℕ) : Finset ℕ := primesInIoc (N / (2 * M)) (N / M)

/-- Every prime in the reciprocal interval has its cofactor cutoff in the prescribed block. -/
theorem cofactorPrimeBlock_mem_bounds {M N p : ℕ} (hM : 0 < M)
    (hp : p ∈ cofactorPrimeBlock M N) : p.Prime ∧ M ≤ N / p ∧ N / p < 2 * M := by
  obtain ⟨hpp, hlo, hhi⟩ := mem_primesInIoc hp
  refine ⟨hpp, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le hpp.pos).mpr
    have h := (Nat.le_div_iff_mul_le hM).mp hhi
    simpa only [Nat.mul_comm] using h
  · apply (Nat.div_lt_iff_lt_mul hpp.pos).mpr
    have h := (Nat.div_lt_iff_lt_mul (show 0 < 2 * M by omega)).mp hlo
    simpa only [Nat.mul_comm] using h

/-- Separated cofactor blocks yield disjoint actual prime sets. -/
theorem cofactorPrimeBlock_disjoint {M K N : ℕ} (hM : 0 < M) (hK : 0 < K)
    (hsep : 2 * M < K) : Disjoint (cofactorPrimeBlock M N) (cofactorPrimeBlock K N) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := cofactorPrimeBlock_mem_bounds hM hp
  have hq' := cofactorPrimeBlock_mem_bounds hK hq
  omega

/-- The exact reciprocal prime block retains a uniform `1/M` counting factor. -/
theorem eventually_cofactorPrimeBlock_card_lower {M : ℕ} (hM : 0 < M) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (4 * M * Real.log N) ≤ ((cofactorPrimeBlock M N).card : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx : Tendsto (fun N : ℕ => (N : ℝ) / (2 * M)) atTop atTop :=
    hcast.atTop_div_const (by positivity)
  have hcount := hx.eventually (eventually_primeCount_window_ge (K := (2 : ℝ)) (by norm_num))
  filter_upwards [hcount, hx.eventually_gt_atTop 1] with N hc hx1
  have hNR : (0 : ℝ) < N := by
    have hpos := lt_trans zero_lt_one hx1
    exact (div_pos_iff.mp hpos).elim (fun h => h.1) (fun h => by linarith)
  have hxN : (N : ℝ) / (2 * M) ≤ N := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hlogx : 0 < Real.log ((N : ℝ) / (2 * M)) := Real.log_pos hx1
  have hlog : Real.log ((N : ℝ) / (2 * M)) ≤ Real.log N :=
    Real.log_le_log (by positivity) hxN
  have hlogN : 0 < Real.log (N : ℝ) := hlogx.trans_le hlog
  have hfloor₁ : ⌊(N : ℝ) / (2 * M)⌋₊ = N / (2 * M) := by
    rw [show (2 : ℝ) * M = ((2 * M : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_div_natCast, Nat.floor_natCast]
  have hfloor₂ : ⌊2 * ((N : ℝ) / (2 * M))⌋₊ = N / M := by
    have heq : 2 * ((N : ℝ) / (2 * M)) = (N : ℝ) / M := by field_simp
    rw [heq, Nat.floor_div_natCast, Nat.floor_natCast]
  rw [hfloor₁, hfloor₂] at hc
  have horder : N / (2 * M) ≤ N / M := Nat.div_le_div_left (by omega) hM
  rw [cofactorPrimeBlock, card_primesInIoc horder]
  calc
    (N : ℝ) / (4 * M * Real.log N) =
        (1 / 2 : ℝ) * (((N : ℝ) / (2 * M)) / Real.log N) := by ring
    _ ≤ (1 / 2 : ℝ) * (((N : ℝ) / (2 * M)) /
        Real.log ((N : ℝ) / (2 * M))) := by gcongr
    _ ≤ _ := by simpa only [show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num] using hc


/-- All selected reciprocal blocks lie above one common moving conditioning cutoff. -/
theorem cofactorPrimeBlock_subset_largePrimes {M K N : ℕ} (hM : 0 < M) (hMK : M ≤ K) :
    cofactorPrimeBlock M N ⊆ largePrimes N (N / (2 * K)) := by
  intro p hp
  obtain ⟨hpp, hlo, hhi⟩ := mem_primesInIoc hp
  apply mem_largePrimes.mpr
  refine ⟨⟨hhi.trans (Nat.div_le_self N M), hpp⟩, ?_⟩
  have hdiv : N / (2 * K) ≤ N / (2 * M) :=
    Nat.div_le_div_left (Nat.mul_le_mul_left 2 hMK) (by omega)
  omega

/-- The common conditioning cutoff eventually satisfies the exact largest-prime seam
and contains every cofactor in the fixed constructed blocks. -/
theorem eventually_cofactorPrimeBlock_conditioning_seam {K : ℕ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, N < (N / (2 * K)) * (N / (2 * K)) ∧ 2 * K < N / (2 * K) := by
  filter_upwards [eventually_ge_atTop ((2 * K) * (2 * K + 2))] with N hN
  have hD : 0 < 2 * K := by omega
  have hY : 2 * K + 2 ≤ N / (2 * K) := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa only [Nat.mul_comm] using hN
  have hrem := Nat.lt_mul_div_succ N hD
  constructor
  · nlinarith
  · omega

end RHTower
