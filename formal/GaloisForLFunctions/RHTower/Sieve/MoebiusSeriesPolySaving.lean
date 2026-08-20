import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothPolySaving
import GaloisForLFunctions.RHTower.Sieve.DistanceAbscissaBridge

/-!
# The Halász bound for the Möbius Dirichlet series at every frequency below the square of the cutoff

At the abscissa `σ = 1 + 1/log z` a bounded multiplicative Dirichlet series is at most its trivial
size `1 + 1/(σ − 1) = 1 + log z` times `e^{7/2 + 2(σ−1)(log z + log 4)}·e^{−D²}`, where `D²` is its
squared pretentious distance from the character `n^{it}`
(`Sieve/DistanceAbscissaBridge.norm_tsum_twistedSummand_le_of_mulDistSqPair`).  For `μ` the distance
is at least `(1/100)·log log z − C₀` uniformly over `|t| ≤ z²`
(`Sieve/MoebiusSmoothPolySaving.eventually_mulDistSqPair_ge_allFreq`), so the whole series is at most
`C·(log z)^{99/100}`: an unconditional Halász saving of `(log z)^{−1/100}` over the trivial size, at
every frequency of the range.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A frequency below the square of the cutoff has logarithm below twice the logarithm. -/
theorem log_abs_le_two_mul_log_of_le_sq {z : ℕ} {t : ℝ} (hz : 0 < Real.log (z : ℝ))
    (ht : |t| ≤ (z : ℝ) ^ 2) : Real.log |t| ≤ 2 * Real.log (z : ℝ) := by
  rcases le_or_gt |t| 1 with h1 | h1
  · have : Real.log |t| ≤ 0 := Real.log_nonpos (abs_nonneg t) h1
    linarith
  · have h2 : Real.log |t| ≤ Real.log ((z : ℝ) ^ 2) := Real.log_le_log (by linarith) ht
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith

/-- **The Halász bound for `μ`, uniformly over `|t| ≤ z²`.**  At the abscissa `1 + 1/log z` the
Möbius Dirichlet series is at most `C·(log z)^{99/100}`, against the trivial size `1 + log z`. -/
theorem exists_norm_tsum_moebius_le_polySaving :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ z : ℕ in atTop, ∀ t : ℝ, |t| ≤ (z : ℝ) ^ 2 →
      ‖∑' n : ℕ, twistedSummand moebiusC
          (⟨1 + 1 / Real.log (z : ℝ), t⟩ : ℂ) n‖
        ≤ C₁ * (Real.log (z : ℝ)) ^ (0.99 : ℝ) := by
  obtain ⟨C₀, hdist⟩ := eventually_mulDistSqPair_ge_allFreq
  refine ⟨2 * Real.exp (7 / 2 + 2 + 2 * Real.log 4 + C₀), by positivity, ?_⟩
  filter_upwards [hdist, eventually_ge_atTop 2,
    log_tendsto_atTop_nat.eventually_ge_atTop (1 : ℝ)] with z hdz hz2 hL1
  intro t ht
  set L := Real.log (z : ℝ) with hLdef
  have hLz0 : (0 : ℝ) < L := by linarith
  have hLL : Real.exp (Real.log L) = L := Real.exp_log hLz0
  have hpow : L ^ (0.99 : ℝ) = Real.exp (Real.log L * 0.99) := Real.rpow_def_of_pos hLz0 _
  have hthi : Real.log |t| ≤ 2 * L := log_abs_le_two_mul_log_of_le_sq hLz0 ht
  have hf : ∀ p ∈ Nat.primesLE z, moebiusC p = -1 :=
    fun p hp => moebiusC_prime (Nat.mem_primesLE.1 hp).2
  have hD := hdz t moebiusC hthi hf
  have hs : (1 : ℝ) < (⟨1 + 1 / L, t⟩ : ℂ).re := by
    show (1 : ℝ) < 1 + 1 / L
    have : (0 : ℝ) < 1 / L := by positivity
    linarith
  have hbnd := norm_tsum_twistedSummand_le_of_mulDistSqPair (f := moebiusC)
    moebiusC_one (fun {a b} h => moebiusC_mul_of_coprime h) norm_moebiusC_le_one hs
    (z := z) (by omega)
  refine le_trans hbnd ?_
  have hre : (⟨1 + 1 / L, t⟩ : ℂ).re = 1 + 1 / L := rfl
  have him : (⟨1 + 1 / L, t⟩ : ℂ).im = t := rfl
  rw [hre, him]
  have hsub : (1 + 1 / L) - 1 = 1 / L := by ring
  rw [hsub]
  have hone : (1 : ℝ) + 1 / (1 / L) = 1 + L := by field_simp
  rw [hone]
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hshape : 2 * (1 / L) * (L + Real.log 4) = 2 + 2 * (Real.log 4 / L) := by
    field_simp
  have hdiv : Real.log 4 / L ≤ Real.log 4 := by
    rw [div_le_iff₀ hLz0]
    nlinarith
  have hExp : 7 / 2 + 2 * (1 / L) * (L + Real.log 4)
        - mulDistSqPair moebiusC (charFn t) (Nat.primesLE z)
      ≤ (7 / 2 + 2 + 2 * Real.log 4 + C₀) - 0.01 * Real.log L := by
    rw [hshape]
    linarith
  have hL' : (1 : ℝ) + L ≤ 2 * Real.exp (Real.log L) := by rw [hLL]; linarith
  calc (1 + L) * Real.exp (7 / 2 + 2 * (1 / L) * (L + Real.log 4)
          - mulDistSqPair moebiusC (charFn t) (Nat.primesLE z))
      ≤ (2 * Real.exp (Real.log L))
          * Real.exp ((7 / 2 + 2 + 2 * Real.log 4 + C₀) - 0.01 * Real.log L) :=
        mul_le_mul hL' (Real.exp_le_exp.2 hExp) (Real.exp_pos _).le (by positivity)
    _ = 2 * Real.exp (Real.log L + ((7 / 2 + 2 + 2 * Real.log 4 + C₀) - 0.01 * Real.log L)) := by
        rw [Real.exp_add]; ring
    _ = 2 * Real.exp ((7 / 2 + 2 + 2 * Real.log 4 + C₀) + Real.log L * 0.99) := by
        congr 1
        congr 1
        ring
    _ = 2 * (Real.exp (7 / 2 + 2 + 2 * Real.log 4 + C₀) * Real.exp (Real.log L * 0.99)) := by
        rw [Real.exp_add]
    _ = 2 * Real.exp (7 / 2 + 2 + 2 * Real.log 4 + C₀) * L ^ (0.99 : ℝ) := by
        rw [hpow]; ring

end

end RHTower.Sieve
