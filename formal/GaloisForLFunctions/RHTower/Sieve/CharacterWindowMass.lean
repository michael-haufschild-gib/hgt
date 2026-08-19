import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRayleighFloor
import GaloisForLFunctions.RHTower.Sieve.MaynardLocalPrimePowerLeakage
import GaloisForLFunctions.HTGeometry.CharacterSource

/-!
# The forced mass of a window

Inside a window the values of the source at proper prime powers are already determined by earlier
windows.  Their total mass is the prime-power leakage `ψ - θ`, which the corpus bounds by
`O(√(width) · log(bound)²)` — negligible against the window's own length `x^θ`.
-/

noncomputable section

open ArithmeticFunction GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

/-- The Chebyshev `ψ` increment counts the von Mangoldt mass of the window. -/
theorem psi_sub_eq_sum_Ioc {u v : ℝ} (huv : u ≤ v) :
    Chebyshev.psi v - Chebyshev.psi u = ∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊, Λ n := by
  have hfl : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_le_floor huv
  have hsplit := Finset.sum_Ioc_consecutive (fun n : ℕ => (Λ n : ℝ)) (Nat.zero_le ⌊u⌋₊) hfl
  rw [Chebyshev.psi, Chebyshev.psi, ← hsplit]
  ring

/-- **The forced mass of a window.**  What the window's proper prime powers contribute is the
prime-power leakage. -/
theorem sum_vonMangoldt_window_sdiff_primes_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y)
    (hd : 1 ≤ y - x) :
    ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ windowPrimes x y, Λ n
      ≤ (Real.log y / Real.log 2) * (Real.sqrt (y - x) + 1) * Real.log y := by
  classical
  have hsub : windowPrimes x y ⊆ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ := by
    intro q hq
    exact (mem_windowPrimes.1 hq).1
  have hsplit : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ windowPrimes x y, Λ n)
      + ∑ n ∈ windowPrimes x y, Λ n = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, Λ n :=
    Finset.sum_sdiff hsub
  have hprimes : (∑ n ∈ windowPrimes x y, Λ n)
      = ∑ p ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ with Nat.Prime p, Real.log p := by
    rw [windowPrimes]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact vonMangoldt_apply_prime (Finset.mem_filter.1 hp).2
  have hpsi := psi_sub_eq_sum_Ioc hxy
  have htheta := theta_sub_eq_sum_Ioc hxy
  have hleak := chebyshevPsi_window_le_theta_window_add_local_primePower hx hxy hd
  have : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊ \ windowPrimes x y, Λ n)
      = (Chebyshev.psi y - Chebyshev.psi x) - (Chebyshev.theta y - Chebyshev.theta x) := by
    rw [hpsi, htheta, ← hsplit, hprimes]
    ring
  rw [this]
  linarith

/-- Updating the phases is updating the source, as far as the window's right endpoint. -/
theorem arithProfile_characterSource_update {u c : ℕ → ℂ} {S : Finset ℕ} {y : ℝ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hSy : ∀ q ∈ S, y < (q : ℝ) ^ 2) (j : ℕ) {t : ℝ} (ht : t ≤ y)
    (ht0 : 0 ≤ t) :
    arithProfile (characterSource (fun m => if m ∈ S then c m else u m)) j t
      = arithProfile (updateWindow (characterSource u) S
          (fun n => c n * ((Real.log n : ℝ) : ℂ))) j t := by
  classical
  rw [arithProfile, arithProfile]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : (n : ℝ) ≤ y := by
    have h1 : n ≤ ⌊t⌋₊ := (Finset.mem_Icc.1 hn).2
    have h2 : (n : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
    exact le_trans (le_trans h2 (Nat.floor_le ht0)) ht
  rw [characterSource_update hS hSy hle]
  by_cases hmem : n ∈ S
  · rw [if_pos hmem, updateWindow, if_pos hmem]
  · rw [if_neg hmem, updateWindow, if_neg hmem]

/-- The phase read off a window assignment. -/
def phaseAssign {N : ℕ} (p : Fin N → ℕ) (b : Fin N → ℂ) : ℕ → ℂ :=
  fun n => if h : ∃ r, p r = n then b h.choose else 1

theorem windowAssign_eq_phaseAssign {N : ℕ} {p : Fin N → ℕ} {b : Fin N → ℂ} {w : Fin N → ℝ}
    (hw : ∀ r, w r = Real.log (p r)) (n : ℕ) :
    windowAssign p b w n
      = if ∃ r, p r = n then phaseAssign p b n * ((Real.log n : ℝ) : ℂ) else 0 := by
  classical
  by_cases h : ∃ r, p r = n
  · rw [if_pos h, windowAssign, dif_pos h, phaseAssign, dif_pos h, hw h.choose, h.choose_spec]
  · rw [if_neg h, windowAssign, dif_neg h]

/-- The bound on the forced mass of the window `(x, x+L]`. -/
def forcedMassBoundL (x L : ℝ) : ℝ :=
  (Real.log (x + L) / Real.log 2) * (Real.sqrt L + 1) * Real.log (x + L)

/-- The bound on the forced mass of the window based at `x` with length `x^θ`. -/
def forcedMassBound (θ x : ℝ) : ℝ := forcedMassBoundL x (x ^ θ)

theorem forcedMassBoundL_nonneg {x L : ℝ} (hx : 1 ≤ x) (hL : 0 ≤ L) :
    0 ≤ forcedMassBoundL x L := by
  have hlog : 0 ≤ Real.log (x + L) := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  rw [forcedMassBoundL]
  positivity

/-- The window's forced source mass is bounded, for a window of any length. -/
theorem sum_norm_characterSource_forced_le_L {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {x L : ℝ} (hx : 2 ≤ x) (hL : 1 ≤ L) :
    ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + L⌋₊ \ windowPrimes x (x + L), ‖characterSource u n‖
      ≤ forcedMassBoundL x L := by
  have hxy : x ≤ x + L := by linarith
  have hd : 1 ≤ (x + L) - x := by linarith
  have heq : ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + L⌋₊ \ windowPrimes x (x + L), ‖characterSource u n‖
      = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + L⌋₊ \ windowPrimes x (x + L), Λ n :=
    Finset.sum_congr rfl fun n _ => norm_characterSource_eq hu n
  rw [heq, forcedMassBoundL]
  have hbound := sum_vonMangoldt_window_sdiff_primes_le hx hxy hd
  have hsq : Real.sqrt ((x + L) - x) = Real.sqrt L := by
    congr 1
    ring
  rw [hsq] at hbound
  exact hbound

theorem forcedMassBound_nonneg {θ x : ℝ} (hx : 1 ≤ x) : 0 ≤ forcedMassBound θ x := by
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hΔ : (0:ℝ) < x ^ θ := Real.rpow_pos_of_pos hxpos θ
  exact forcedMassBoundL_nonneg hx (le_of_lt hΔ)

/-- The window's forced source mass is bounded. -/
theorem sum_norm_characterSource_forced_le {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {θ x : ℝ} (hx : 2 ≤ x) (hΔ1 : 1 ≤ x ^ θ) :
    ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + x ^ θ⌋₊ \ windowPrimes x (x + x ^ θ),
        ‖characterSource u n‖
      ≤ forcedMassBound θ x :=
  sum_norm_characterSource_forced_le_L hu hx hΔ1

/-- The jump mass of a window is at most its integer count times the largest logarithm. -/
theorem sum_norm_characterSource_window_le {u : ℕ → ℂ}
    (hu : ∀ p : ℕ, Nat.Prime p → ‖u p‖ = 1) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖characterSource u n‖
      ≤ (y - x + 1) * Real.log y := by
  have hx0 : (0:ℝ) ≤ x := le_trans zero_le_one hx
  have hy0 : (0:ℝ) ≤ y := le_trans hx0 hxy
  have hy1 : (1:ℝ) ≤ y := le_trans hx hxy
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hterm : ∀ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, ‖characterSource u n‖ ≤ Real.log y := by
    intro n hn
    have hmem := Finset.mem_Ioc.1 hn
    have hny : (n : ℝ) ≤ y := by
      have h1 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hmem.2
      exact le_trans h1 (Nat.floor_le hy0)
    rw [norm_characterSource_eq hu n, vonMangoldt_apply]
    by_cases h : IsPrimePow n
    · rw [if_pos h]
      have hn1 : 1 < n := h.one_lt
      have hle : ((n.minFac : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.minFac_le (by omega : 0 < n)
      refine Real.log_le_log ?_ (le_trans hle hny)
      have : 0 < n.minFac := Nat.minFac_pos n
      exact_mod_cast this
    · rw [if_neg h]
      exact hlogy
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  have hcard : ((⌊y⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ y - x + 1 := by
    rw [Nat.cast_sub hfl]
    have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
    have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  exact mul_le_mul_of_nonneg_right hcard hlogy

/-- The same bridge for the full chain: the continuous datum is untouched by a phase change. -/
theorem arithJumpProfile_characterSource_update {dq : ℝ → ℂ} {u c : ℕ → ℂ} {S : Finset ℕ} {y : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hSy : ∀ p ∈ S, y < (p : ℝ) ^ 2) (j : ℕ) {t : ℝ} (ht : t ≤ y)
    (ht0 : 0 ≤ t) :
    arithJumpProfile dq (characterSource (fun m => if m ∈ S then c m else u m)) j t
      = arithJumpProfile dq (updateWindow (characterSource u) S
          (fun n => c n * ((Real.log n : ℝ) : ℂ))) j t := by
  rw [arithJumpProfile, arithJumpProfile, arithProfile_characterSource_update hS hSy j ht ht0]

end RHTower.Sieve

end
