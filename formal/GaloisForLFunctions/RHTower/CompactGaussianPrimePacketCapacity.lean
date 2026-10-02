import GaloisForLFunctions.RHTower.CompactGaussianNormalizedChannelUpper
import GaloisForLFunctions.PNTPlus.BrunTitchmarsh

open Complex Finset
noncomputable section
namespace RHTower

-- Elementary sieve-error absorption, kept independent of Gallagher mean-value imports.
private theorem bagPacket_cube_mul_le_exp_half {u : ℝ} (hu : 0 ≤ u) :
    6 * (1 + u / 2) ^ 3 * u ≤ 288 * Real.exp (u / 2) := by
  have hu2 : (0 : ℝ) ≤ u / 2 := by linarith
  have h := Real.sum_le_exp_of_nonneg hu2 6
  simp [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [h, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5, hu]

/-- **The Brun--Titchmarsh error term is a bounded multiple of the main term.**  For every
`H > 1`, `6√H (1 + log √H)³ ≤ 288 H / log H`. -/
private theorem bagPacket_bt_error_le_main {H : ℝ} (hH : 1 < H) :
    6 * Real.sqrt H * (1 + Real.log (Real.sqrt H)) ^ 3 ≤ 288 * H / Real.log H := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hu : (0 : ℝ) < Real.log H := Real.log_pos hH
  have hs : Real.sqrt H = Real.exp (Real.log H / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hH0]
    congr 1
    ring
  have hls : Real.log (Real.sqrt H) = Real.log H / 2 := by
    rw [hs, Real.log_exp]
  have hstep := bagPacket_cube_mul_le_exp_half (u := Real.log H) hu.le
  rw [← hs] at hstep
  rw [hls]
  rw [le_div_iff₀ hu]
  have hsq : Real.sqrt H * Real.sqrt H = H := Real.mul_self_sqrt hH0.le
  have hspos : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hH0
  nlinarith [hstep, hspos, hu, hsq]

/-- **Brun--Titchmarsh in `H/log H` form.**  The sieve level `√H` makes the error term a bounded
multiple of the main term. -/
theorem bagPacket_primesBetween_le_div_log {a H : ℝ} (ha : 0 < a) (hH : 1 < H) :
    (BrunTitchmarsh.primesBetween a (a + H) : ℝ) ≤ 292 * H / Real.log H := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hu : (0 : ℝ) < Real.log H := Real.log_pos hH
  have hZ : (1 : ℝ) < Real.sqrt H := by
    have h1 : Real.sqrt 1 < Real.sqrt H := by
      refine Real.sqrt_lt_sqrt (by norm_num) hH
    simpa using h1
  have hbt := BrunTitchmarsh.primesBetween_le a H (Real.sqrt H) ha hH0 hZ
  have hls : Real.log (Real.sqrt H) = Real.log H / 2 := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hH0]
    ring
  rw [hls] at hbt
  have hmain : 2 * H / (Real.log H / 2) = 4 * H / Real.log H := by
    field_simp
    ring
  rw [hmain] at hbt
  have herr := bagPacket_bt_error_le_main hH
  rw [hls] at herr
  have hsum : 4 * H / Real.log H + 288 * H / Real.log H = 292 * H / Real.log H := by
    field_simp
    ring
  linarith [hbt, herr, hsum.le, hsum.ge]



/-- Every square-root-width prime packet has logarithmically vanishing
capacity in the actual normalized channels, uniformly in its location,
height, cutoff, retained phases, and unit phase multipliers. -/
theorem exists_compactGaussian_prime_packet_capacity (b D : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N a : ℝ, 1 < N → 0 < a →
      ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) ≤ a + Real.sqrt N ∧
        1 ≤ N / p ∧ N / p ≤ D) →
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ b → ∀ tau : ℝ, ∀ K : ℕ → ℕ,
      ∀ ω : SteinhausModel.Omega, ∀ v : ℕ → ℂ, (∀ p ∈ S, ‖v p‖ ≤ 1) →
      ‖∑ p ∈ S, v p * compactGaussianNormalizedPrimeChannel s N p tau (K p) ω‖ ≤
        C / Real.log N := by
  obtain ⟨C, hC, hcol⟩ := exists_compactGaussianNormalizedPrimeChannel_uniform_bound b D
  refine ⟨584 * C, by positivity, ?_⟩
  intro N a hN ha S hS s hs0 hsb tau K ω v hv
  have hN0 : 0 < N := by linarith
  have hroot : 1 < Real.sqrt N := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hN
    simpa using h
  have hsqrt : 0 < Real.sqrt N := by linarith
  have hcard : (S.card : ℝ) ≤ 292 * Real.sqrt N / Real.log (Real.sqrt N) := by
    have hsub : S ⊆ (Finset.Icc (Nat.ceil a) (Nat.floor (a + Real.sqrt N))).filter Nat.Prime := by
      intro p hp
      obtain ⟨hprime, hlo, hhi, _, _⟩ := hS p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩, hprime⟩
    exact (show (S.card : ℝ) ≤ (BrunTitchmarsh.primesBetween a (a + Real.sqrt N) : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans (bagPacket_primesBetween_le_div_log ha hroot)
  have hlog : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
  calc
    _ ≤ ∑ p ∈ S, ‖v p * compactGaussianNormalizedPrimeChannel s N p tau (K p) ω‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, C / Real.sqrt N := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hprime, _, _, hlo, hhi⟩ := hS p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hv p hp)).trans
        (hcol N p hN0 hpR hlo hhi s hs0 hsb tau (K p) ω)
    _ = (S.card : ℝ) * (C / Real.sqrt N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (292 * Real.sqrt N / Real.log (Real.sqrt N)) * (C / Real.sqrt N) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [hlog]; field_simp; ring

end RHTower
