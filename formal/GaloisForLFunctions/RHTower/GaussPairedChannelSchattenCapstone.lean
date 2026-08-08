import GaloisForLFunctions.HTGeometry.GaussPairedChannelSchattenDepth
import GaloisForLFunctions.RHTower.WeakSchattenResidue

/-!
# Exact Schatten depth of a Gauss-paired channel system

The endpoint information produced by the Gauss-component residue calculation is assembled here:
weak membership at exponent `2m` and the positive arithmetic logarithmic residue force exact
critical depth `2m`.  The prime-counting corollary excludes one fixed Schatten class along every
cofinal cutoff family carrying these endpoint certificates.
-/

namespace RHTower

open GaloisForLFunctions.RHTower

noncomputable section

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Exact direct-sum endpoint.**  Once the channel-resolved defect has the inherited weak
`S_{2m,∞}` bound and the additive Gauss residue, its ordinary Schatten threshold is exactly
`2m`: every positive exponent at or below the endpoint is excluded and every larger exponent is
admitted. -/
theorem gaussPairedChannel_exact_schattenDepth
    {J : Type*} [Fintype J] [Nonempty J] {m : ℕ} (hm : 1 ≤ m)
    (prime : J → Nat.Primes) {T : H →L[ℂ] H}
    (hweak : MemWeakSchattenClass ((2 * m : ℕ) : ℝ) T)
    (hres : HasSchattenLogResidue ((2 * m : ℕ) : ℝ) T
      (gaussPairedChannelResidue m prime)) :
    (∀ q : ℝ, 0 < q → q ≤ (2 * m : ℕ) → ¬ MemSchattenClass q T) ∧
      (∀ q : ℝ, (2 * m : ℕ) < q → MemSchattenClass q T) := by
  have hdepth : (0 : ℝ) < (2 * m : ℕ) := by exact_mod_cast (show 0 < 2 * m by omega)
  exact exact_schattenDepth_of_weak_of_positive_logResidue hdepth
    (gaussPairedChannelResidue_pos hm prime) hweak hres

/-- Card-specialized form with exactly `m` labeled prime channels. Prime labels may repeat: exact
Schatten depth uses positivity of each component residue, not label injectivity. -/
theorem gaussPairedFinChannel_exact_schattenDepth
    {m : ℕ} (hm : 1 ≤ m) (prime : Fin m → Nat.Primes)
    {T : H →L[ℂ] H} (hweak : MemWeakSchattenClass ((2 * m : ℕ) : ℝ) T)
    (hres : HasSchattenLogResidue ((2 * m : ℕ) : ℝ) T
      (gaussPairedChannelResidue m prime)) :
    (∀ q : ℝ, 0 < q → q ≤ (2 * m : ℕ) → ¬ MemSchattenClass q T) ∧
      (∀ q : ℝ, (2 * m : ℕ) < q → MemSchattenClass q T) := by
  letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  exact gaussPairedChannel_exact_schattenDepth hm prime hweak hres

/-- **Cofinal exclusion law.**  A cutoff family with the exact Gauss endpoint certificate at every
nonempty prime aperture cannot lie in any one fixed positive Schatten class. -/
theorem exists_cutoff_not_memSchattenClass
    (T : ℕ → H →L[ℂ] H)
    (prime : ∀ N, Fin (Nat.primeCounting N) → Nat.Primes)
    (hweak : ∀ N, Nat.primeCounting N ≠ 0 →
      MemWeakSchattenClass ((gaussPairedCriticalDepth N : ℕ) : ℝ) (T N))
    (hres : ∀ N, Nat.primeCounting N ≠ 0 →
      HasSchattenLogResidue ((gaussPairedCriticalDepth N : ℕ) : ℝ) (T N)
        (gaussPairedChannelResidue (Nat.primeCounting N) (prime N)))
    (q : ℝ) (hq : 0 < q) :
    ∃ N : ℕ, ¬ MemSchattenClass q (T N) := by
  obtain ⟨N, hN⟩ := exists_gaussPairedCriticalDepth_gt q
  have hm : 1 ≤ Nat.primeCounting N := by
    by_contra hzero
    have hpi : Nat.primeCounting N = 0 := by omega
    rw [gaussPairedCriticalDepth, hpi] at hN
    norm_num at hN
    linarith
  have hm0 : Nat.primeCounting N ≠ 0 := by omega
  letI : Nonempty (Fin (Nat.primeCounting N)) := ⟨⟨0, by omega⟩⟩
  refine ⟨N, ?_⟩
  have hexact := gaussPairedChannel_exact_schattenDepth hm (prime N)
    (hweak N hm0) (hres N hm0)
  exact hexact.1 q hq (le_of_lt hN)

end

end
end RHTower
