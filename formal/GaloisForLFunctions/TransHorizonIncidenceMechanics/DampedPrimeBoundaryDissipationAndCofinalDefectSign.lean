import GaloisForLFunctions.TransHorizonIncidenceMechanics.IntegerJumpEnergyAndBeyondEnvelopeDefect
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusGradientCoercivityAndRenormalizedDefect
import GaloisForLFunctions.BezoutValuationIncidence.PostStepInactivePrefixAndSixDivisibilityPronicDefect
import GaloisForLFunctions.RHTower.PrimeLogSeparationAperture

/-!
# Prime-boundary dissipation and the cofinal sign of the damped defect

For the damped weight `c_ε(d) = μ(d) d^(-ε)` the sieve below its horizon is the complete
multiplicative coefficient `τ_ε(n) = ∏_{p ∣ n} (1 - p^(-ε))`. At an odd prime `p < N` the path
steps from `τ_ε(p) = 1 - p^(-ε)` to an even argument, where `τ_ε ≤ 1 - 2^(-ε)`. Each such
prime boundary therefore dissipates at least `(2^(-ε) - p^(-ε))²` of jump energy, for every
horizon and every prefix reaching it. At `ε = 0` the dissipation vanishes: the literal Möbius
path is constant below its horizon and must wait for the first trans-horizon octave.

Polarization turns the dissipation into a defect bound in which only the endpoint divisor
square remains. Chebyshev's prime count makes the dissipation of order `N / log N` at fixed
`ε > 0`, while the endpoint divisor square is a small power. Hence at every fixed positive
damping the renormalized defect is eventually below `-κ_ε N / log N` on every polynomial
trans-horizon prefix window, with no shrinking damping radius. Radical-state reduction then
gives nonpositive defects at every prefix, of any size, whose horizon radical state is at most
a fixed power of the horizon; the same transport applies to the literal Möbius weight.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence RHTower
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Damped coefficients at primes and even arguments -/

/-- The damped divisor coefficient of a prime. -/
theorem pmPowerDampedDivisorCoeff_prime (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    pmPowerDampedDivisorCoeff ε p = 1 - (p : ℝ) ^ (-ε) := by
  simpa using pmPowerDampedDivisorCoeff_prime_pow ε hp one_ne_zero

/-- Every even argument carries the factor `1 - 2^(-ε)`. -/
theorem pmPowerDampedDivisorCoeff_le_of_two_dvd {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ}
    (h2 : 2 ∣ n) (hn : n ≠ 0) :
    pmPowerDampedDivisorCoeff ε n ≤ 1 - (2 : ℝ) ^ (-ε) := by
  have h := pmPowerDampedDivisorCoeff_le_of_dvd hε h2 hn
  rwa [pmPowerDampedDivisorCoeff_prime ε Nat.prime_two, Nat.cast_ofNat] at h

/-- The damped response is bounded by the divisor count of its argument. -/
theorem abs_sieveSeq_pmPowerDampedRealWeight_le_divisor_card {ε : ℝ} (hε : 0 ≤ ε)
    (N n : ℕ) :
    |sieveSeq N (pmPowerDampedRealWeight ε) (n + 1)| ≤ ((n + 1).divisors.card : ℝ) := by
  classical
  unfold sieveSeq
  rw [filter_dvd_Icc_eq_divisors_filter_le N (by omega)]
  calc
    _ ≤ ∑ d ∈ (n + 1).divisors.filter (fun d => d ≤ N), |pmPowerDampedRealWeight ε d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (n + 1).divisors.filter (fun d => d ≤ N), (1 : ℝ) :=
      Finset.sum_le_sum fun d _ => abs_pmPowerDampedRealWeight_le_one hε d
    _ = (((n + 1).divisors.filter (fun d => d ≤ N)).card : ℝ) := by simp
    _ ≤ ((n + 1).divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun d => d ≤ N) _)

/-! ### The exact dissipation law -/

/-- One odd prime boundary below the horizon pays `(2^(-ε) - p^(-ε))²` of jump energy. -/
theorem sub_rpow_sq_le_pmPowerDamped_prime_jump {ε : ℝ} (hε : 0 ≤ ε) {N p : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hpN : p + 1 ≤ N) :
    ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 ≤
      (sieveSeq N (pmPowerDampedRealWeight ε) (p + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) p) ^ 2 := by
  have hs : sieveSeq N (pmPowerDampedRealWeight ε) p = 1 - (p : ℝ) ^ (-ε) := by
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hp.one_lt.le (by omega),
      pmPowerDampedDivisorCoeff_prime ε hp]
  have heven : 2 ∣ p + 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨k + 1, by omega⟩
  have hs1 : sieveSeq N (pmPowerDampedRealWeight ε) (p + 1) ≤ 1 - (2 : ℝ) ^ (-ε) := by
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega) hpN]
    exact pmPowerDampedDivisorCoeff_le_of_two_dvd hε heven (by omega)
  have hmono : (p : ℝ) ^ (-ε) ≤ (2 : ℝ) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have h0 : 0 ≤ (2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε) := by linarith
  have hle : (2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε) ≤
      sieveSeq N (pmPowerDampedRealWeight ε) p -
        sieveSeq N (pmPowerDampedRealWeight ε) (p + 1) := by
    rw [hs]; linarith
  calc
    _ ≤ (sieveSeq N (pmPowerDampedRealWeight ε) p -
          sieveSeq N (pmPowerDampedRealWeight ε) (p + 1)) ^ 2 := pow_le_pow_left₀ h0 hle 2
    _ = _ := by ring

/-- **Prime-boundary dissipation.** Every prefix reaching the horizon carries at least the
summed odd-prime boundary energy below the horizon, at every damping `ε ≥ 0`. -/
theorem sum_prime_boundary_le_pmPowerDamped_gradient {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ}
    (hNM : N ≤ M + 1) :
    ∑ p ∈ (Icc 3 (N - 1)).filter Nat.Prime, ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 ≤
      ∑ k ∈ Icc 1 M, (sieveSeq N (pmPowerDampedRealWeight ε) (k + 1) -
        sieveSeq N (pmPowerDampedRealWeight ε) k) ^ 2 := by
  have hsub : (Icc 3 (N - 1)).filter Nat.Prime ⊆ Icc 1 M := by
    intro p hp
    obtain ⟨hpI, -⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_Icc.mp hpI
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  calc
    _ ≤ ∑ p ∈ (Icc 3 (N - 1)).filter Nat.Prime,
          (sieveSeq N (pmPowerDampedRealWeight ε) (p + 1) -
            sieveSeq N (pmPowerDampedRealWeight ε) p) ^ 2 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
      obtain ⟨h1, h2⟩ := mem_Icc.mp hpI
      exact sub_rpow_sq_le_pmPowerDamped_prime_jump hε hpp h1 (by omega)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-- **Damped defect budget.** For `1 ≤ N ≤ M + 1`, twice the renormalized defect plus the
prime-boundary dissipation is bounded by the endpoint divisor square minus one. -/
theorem two_mul_pmPowerDamped_defect_add_prime_boundary_le {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M + 1) :
    2 * sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) +
        ∑ p ∈ (Icc 3 (N - 1)).filter Nat.Prime, ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 ≤
      ((M + 1).divisors.card : ℝ) ^ 2 - 1 := by
  have hid := two_mul_sieveRenormalizedPrefixDefect_add_gradient_eq_boundary N M
    (pmPowerDampedRealWeight ε)
  have h1 : sieveSeq N (pmPowerDampedRealWeight ε) 1 = 1 := by
    rw [sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff le_rfl hN,
      pmPowerDampedDivisorCoeff_one]
  rw [h1, one_pow] at hid
  have hs : sieveSeq N (pmPowerDampedRealWeight ε) (M + 1) ^ 2 ≤
      ((M + 1).divisors.card : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
      (abs_sieveSeq_pmPowerDampedRealWeight_le_divisor_card hε N M) 2
  have hE := sum_prime_boundary_le_pmPowerDamped_gradient hε hNM
  linarith

/-! ### Counting dissipating primes -/

/-- Beyond `2^(1 + 1/ε)` every prime boundary pays at least `(2^(-ε)/2)²`. -/
theorem half_two_rpow_sq_le_prime_boundary {ε : ℝ} (hε : 0 < ε) {p : ℝ}
    (hp : (2 : ℝ) ^ (1 + 1 / ε) ≤ p) :
    ((2 : ℝ) ^ (-ε) / 2) ^ 2 ≤ ((2 : ℝ) ^ (-ε) - p ^ (-ε)) ^ 2 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (1 + 1 / ε) := by positivity
  have hle : p ^ (-ε) ≤ ((2 : ℝ) ^ (1 + 1 / ε)) ^ (-ε) :=
    Real.rpow_le_rpow_of_nonpos hpos hp (by linarith)
  have hval : ((2 : ℝ) ^ (1 + 1 / ε)) ^ (-ε) = (2 : ℝ) ^ (-ε) / 2 := by
    rw [← Real.rpow_mul (by norm_num), show (1 + 1 / ε) * -ε = -ε + -1 by
      field_simp; ring, Real.rpow_add (by norm_num), Real.rpow_neg_one]
    ring
  have hp0 : 0 ≤ p ^ (-ε) := Real.rpow_nonneg (le_trans hpos.le hp) _
  have h2 : 0 < (2 : ℝ) ^ (-ε) := by positivity
  rw [hval] at hle
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- The dissipating primes below the horizon number at least the Chebyshev count minus a
damping-dependent constant. -/
theorem prime_boundary_sum_ge_card_windowPrimes {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ((2 : ℝ) ^ (-ε) / 2) ^ 2 *
        (((RHTower.windowPrimes 1 ((N : ℝ) - 1)).card : ℝ) -
          ((⌈(2 : ℝ) ^ (1 + 1 / ε)⌉₊ + 3 : ℕ) : ℝ)) ≤
      ∑ p ∈ (Icc 3 (N - 1)).filter Nat.Prime, ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 := by
  classical
  set X : ℝ := (2 : ℝ) ^ (1 + 1 / ε)
  set K : ℕ := ⌈X⌉₊ + 3
  set G := ((Icc 3 (N - 1)).filter Nat.Prime).filter (fun p : ℕ => X ≤ (p : ℝ))
  have hcover : RHTower.windowPrimes 1 ((N : ℝ) - 1) ⊆ G ∪ range K := by
    intro p hp
    by_cases hN1 : (N : ℝ) - 1 < 0
    · exfalso
      unfold RHTower.windowPrimes at hp
      have hfl : ⌊(N : ℝ) - 1⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      rw [hfl] at hp
      simp at hp
    rw [RHTower.mem_windowPrimes (by norm_num) (by linarith)] at hp
    obtain ⟨hpp, h1p, hpN⟩ := hp
    by_cases hgood : 3 ≤ p ∧ X ≤ (p : ℝ)
    · refine mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hgood.1, ?_⟩,
        hpp⟩, hgood.2⟩)
      have : (p : ℝ) + 1 ≤ N := by linarith
      have : p + 1 ≤ N := by exact_mod_cast this
      omega
    · refine mem_union_right _ (mem_range.mpr ?_)
      rcases not_and_or.mp hgood with h | h
      · omega
      · have := Nat.lt_ceil.mpr (not_le.mp h)
        omega
  have hcard : ((RHTower.windowPrimes 1 ((N : ℝ) - 1)).card : ℝ) ≤ G.card + K := by
    have := (card_le_card hcover).trans (card_union_le G (range K))
    rw [card_range] at this
    exact_mod_cast this
  have hterm : ∀ p ∈ G, ((2 : ℝ) ^ (-ε) / 2) ^ 2 ≤ ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 :=
    fun p hp => half_two_rpow_sq_le_prime_boundary hε (mem_filter.mp hp).2
  have hG : ((2 : ℝ) ^ (-ε) / 2) ^ 2 * G.card ≤
      ∑ p ∈ G, ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 := by
    have := sum_le_sum hterm
    simpa [mul_comm] using this
  have hGsub : ∑ p ∈ G, ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 ≤
      ∑ p ∈ (Icc 3 (N - 1)).filter Nat.Prime, ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
  have hδ : 0 ≤ ((2 : ℝ) ^ (-ε) / 2) ^ 2 := sq_nonneg _
  nlinarith

/-! ### Cofinal sign at fixed damping -/

/-- Chebyshev's count eventually exceeds `N / (4 log N)` plus any fixed surplus. -/
theorem eventually_card_windowPrimes_ge (K : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (4 * Real.log N) + K ≤ ((RHTower.windowPrimes 1 ((N : ℝ) - 1)).card : ℝ) := by
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp
    (tendsto_chebyshevPrimeLower_div_id.eventually
      (eventually_ge_nhds (show (1 / 2 : ℝ) < Real.log 2 by
        have := Real.log_two_gt_d9; linarith)))
  have hlog : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (1 / (8 * (|K| + 1))) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by positivity)
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp hlog
  filter_upwards [eventually_ge_atTop (⌈max X₁ X₂⌉₊ + 4)] with N hN
  have hNX : max X₁ X₂ + 4 ≤ (N : ℝ) := by
    have h1 := Nat.le_ceil (max X₁ X₂)
    have h2 : ((⌈max X₁ X₂⌉₊ + 4 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2
    linarith
  have hx1 : X₁ ≤ (N : ℝ) - 1 := by linarith [le_max_left X₁ X₂]
  have hx2 : X₂ ≤ (N : ℝ) := by linarith [le_max_right X₁ X₂]
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast (show 4 ≤ N by omega)
  have hcheb := hX₁ ((N : ℝ) - 1) hx1
  have hpos1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hcard := chebyshevPrimeLower_div_log_le_card (x := (N : ℝ) - 1) (by linarith)
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlog1 : 0 < Real.log ((N : ℝ) - 1) := Real.log_pos (by linarith)
  have hlogle : Real.log ((N : ℝ) - 1) ≤ Real.log N := Real.log_le_log hpos1 (by linarith)
  have hlowx : ((N : ℝ) - 1) / 2 ≤ chebyshevPrimeLower ((N : ℝ) - 1) := by
    have := (le_div_iff₀ hpos1).mp hcheb
    linarith
  have hstep1 : ((N : ℝ) - 1) / 2 / Real.log N ≤
      chebyshevPrimeLower ((N : ℝ) - 1) / Real.log ((N : ℝ) - 1) :=
    calc ((N : ℝ) - 1) / 2 / Real.log N ≤ ((N : ℝ) - 1) / 2 / Real.log ((N : ℝ) - 1) :=
          div_le_div_of_nonneg_left (by linarith) hlog1 hlogle
      _ ≤ _ := div_le_div_of_nonneg_right hlowx hlog1.le
  have hsmall := hX₂ N hx2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogN,
    abs_of_pos (by linarith : (0 : ℝ) < N)] at hsmall
  have hK : K ≤ ((N : ℝ) - 2) / (4 * Real.log N) := by
    rw [le_div_iff₀ (by positivity)]
    have hKa : K ≤ |K| := le_abs_self K
    have h8 : 8 * (|K| + 1) * Real.log N ≤ N := by
      have := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 8 * (|K| + 1))
      rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
    nlinarith [abs_nonneg K]
  have hsplit : (N : ℝ) / (4 * Real.log N) + ((N : ℝ) - 2) / (4 * Real.log N) =
      ((N : ℝ) - 1) / 2 / Real.log N := by
    field_simp; ring
  linarith

/-- **Cofinal coercivity at fixed damping.** For every `ε > 0` and every polynomial window,
eventually in the horizon the damped renormalized defect is at most `-(2^(-ε)/2)² N / (16 log N)`
at every prefix `N ≤ M + 1 ≤ N^(r+2) + 1`. -/
theorem eventually_pmPowerDamped_renormalizedDefect_polynomial_cofinal_bound {ε : ℝ}
    (hε : 0 < ε) (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, N ≤ M + 1 → M ≤ N ^ (r + 2) →
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤
        -(((2 : ℝ) ^ (-ε) / 2) ^ 2 * N / (16 * Real.log N)) := by
  set δ : ℝ := ((2 : ℝ) ^ (-ε) / 2) ^ 2
  have hδ : 0 < δ := by positivity
  set K : ℕ := ⌈(2 : ℝ) ^ (1 + 1 / ε)⌉₊ + 3
  obtain ⟨C, hC, hbound⟩ := exists_uniform_divisor_square_subpower_bound (2 * r + 3)
  set a : ℝ := 1 / (((2 * r + 3 : ℕ) : ℝ) + 1)
  have ha : 0 < a := by positivity
  set D : ℝ := C * (2 : ℝ) ^ a
  have hD : 0 < D := by positivity
  have hlog : ∀ᶠ x : ℝ in atTop,
      ‖Real.log x‖ ≤ (δ / (8 * D)) * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num)).bound (by positivity)
  filter_upwards [eventually_card_windowPrimes_ge (K : ℝ),
    tendsto_natCast_atTop_atTop.eventually hlog, eventually_ge_atTop 2] with N hcard hsmall hN
  intro M hNM hMN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hn1
  have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
    rw [← Real.rpow_add hn]; norm_num
  have hsqpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogN, abs_of_pos hsqpos] at hsmall
  -- the endpoint divisor square is at most `D √N`
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ (r + 2) := one_le_pow₀ hn1.le
  have hMN' : (M : ℝ) + 1 ≤ 2 * (N : ℝ) ^ (r + 2) := by
    have hc : (M : ℝ) ≤ (N : ℝ) ^ (r + 2) := by exact_mod_cast hMN
    linarith
  have hpow : ((M : ℝ) + 1) ^ a ≤ (2 : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 * (N : ℝ) ^ (r + 2)) ^ a :=
        Real.rpow_le_rpow (by positivity) hMN' ha.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          ← Real.rpow_natCast (N : ℝ) (r + 2), ← Real.rpow_mul hn.le]
        congr 2
        dsimp [a]
        push_cast
        field_simp
        ring
  have hend : ((M + 1).divisors.card : ℝ) ^ 2 - 1 ≤ D * (N : ℝ) ^ (1 / 2 : ℝ) := by
    have h := hbound M
    have : C * ((M : ℝ) + 1) ^ a ≤ C * ((2 : ℝ) ^ a * (N : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow hC.le
    dsimp [D]
    nlinarith
  -- the dissipation is at least `δ N / (4 log N)`
  have hdiss : δ * ((N : ℝ) / (4 * Real.log N)) ≤
      ∑ p ∈ (Icc 3 (N - 1)).filter Nat.Prime, ((2 : ℝ) ^ (-ε) - (p : ℝ) ^ (-ε)) ^ 2 := by
    have h := prime_boundary_sum_ge_card_windowPrimes hε N
    have hc : (N : ℝ) / (4 * Real.log N) ≤
        ((RHTower.windowPrimes 1 ((N : ℝ) - 1)).card : ℝ) - (K : ℝ) := by linarith
    calc δ * ((N : ℝ) / (4 * Real.log N)) ≤ δ * (((RHTower.windowPrimes 1 ((N : ℝ) - 1)).card
          : ℝ) - (K : ℝ)) := mul_le_mul_of_nonneg_left hc hδ.le
      _ ≤ _ := by simpa [K] using h
  -- the divisor square is dominated by half the dissipation
  have hdom : D * (N : ℝ) ^ (1 / 2 : ℝ) ≤ δ * ((N : ℝ) / (8 * Real.log N)) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have h1 := mul_le_mul_of_nonneg_left hsmall
      (by positivity : (0 : ℝ) ≤ 8 * D * (N : ℝ) ^ (1 / 2 : ℝ))
    have h2 : 8 * D * (N : ℝ) ^ (1 / 2 : ℝ) * (δ / (8 * D) * (N : ℝ) ^ (1 / 2 : ℝ)) =
        δ * ((N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) := by
      field_simp
    rw [hsq] at h2
    nlinarith
  have hbudget := two_mul_pmPowerDamped_defect_add_prime_boundary_le hε.le
    (by omega : 1 ≤ N) hNM
  have hsplit : δ * ((N : ℝ) / (4 * Real.log N)) =
      2 * (δ * ((N : ℝ) / (8 * Real.log N))) := by field_simp; ring
  have hgoal : -(δ * N / (16 * Real.log N)) = -(δ * ((N : ℝ) / (8 * Real.log N))) / 2 := by
    field_simp; ring
  rw [hgoal]
  linarith

/-! ### Radical-state transport to arbitrary scales -/

/-- At every fixed positive damping, eventually in the horizon, every prefix whose horizon
radical state is at most `N^(r+2)` has nonpositive damped defect, however large the prefix. -/
theorem eventually_pmPowerDamped_defect_nonpos_of_radicalState_le {ε : ℝ} (hε : 0 < ε)
    (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, horizonRadicalState N (M + 1) ≤ N ^ (r + 2) →
      sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ 0 := by
  filter_upwards [eventually_pmPowerDamped_renormalizedDefect_polynomial_cofinal_bound hε r,
    eventually_ge_atTop 2] with N hmain hN
  intro M hg
  have hg1 : 1 ≤ horizonRadicalState N (M + 1) := horizonRadicalState_pos N (M + 1)
  have hred := sieveRenormalizedPrefixDefect_le_horizonRadicalState N (k := M + 1)
    (by omega) (pmPowerDampedRealWeight_eq_zero_of_not_squarefree ε)
  rw [Nat.add_sub_cancel] at hred
  generalize horizonRadicalState N (M + 1) = g at hred hg hg1
  refine hred.trans ?_
  by_cases hbig : N ≤ g
  · have h := hmain (g - 1) (by omega) (by omega)
    have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have : 0 ≤ ((2 : ℝ) ^ (-ε) / 2) ^ 2 * N / (16 * Real.log N) := by positivity
    linarith
  · by_cases hg2 : g = 1
    · rw [hg2]
      simp [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff]
    · exact (sieveRenormalizedPrefixDefect_pmPowerDampedRealWeight_nonpos hε.le
        (by omega : 1 ≤ g - 1) (by omega)).2

/-- The same transport for the literal Möbius weight: eventually in the horizon, every prefix
whose horizon radical state is at most `N^(r+2)` has nonpositive renormalized defect. -/
theorem eventually_moebius_defect_nonpos_of_radicalState_le (r : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, horizonRadicalState N (M + 1) ≤ N ^ (r + 2) →
      sieveRenormalizedPrefixDefect N M moebiusReal ≤ 0 := by
  filter_upwards [eventually_moebiusRenormalizedDefect_polynomial_cofinal_bound r]
    with N hmain
  intro M hg
  have hg1 : 1 ≤ horizonRadicalState N (M + 1) := horizonRadicalState_pos N (M + 1)
  have hred := sieveRenormalizedPrefixDefect_le_horizonRadicalState N (k := M + 1)
    (by omega) (moebiusReal_eq_zero_of_not_squarefree)
  rw [Nat.add_sub_cancel] at hred
  generalize horizonRadicalState N (M + 1) = g at hred hg hg1
  refine hred.trans ?_
  by_cases hbig : 2 * N ≤ g - 1
  · have h := hmain (g - 1) (mem_Icc.mpr ⟨hbig, by omega⟩)
    have : -(N : ℝ) / (2 * Real.pi ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N)) (by positivity)
    linarith
  · exact moebius_prefix_defect_nonpos_of_lt_six_succ (by omega)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
