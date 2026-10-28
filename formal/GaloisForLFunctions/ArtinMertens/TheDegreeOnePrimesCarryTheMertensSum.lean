import GaloisForLFunctions.ArtinMertens.TheSoftMertensTheoremForPrimeIdeals

/-!
# The degree-one primes carry the Mertens sum

Let `n_K(p) = #{𝔭 ⊂ 𝓞_K : N𝔭 = p}` be the number of degree-one primes of `K` over `p`. Then
`Σ_{p ≤ x} n_K(p) log p/p = log x + o(log x)` (`tendsto_degreeOneMertens_div_log`).

* **Grouping by norm** (`primeMertens_eq_sum_fiberMertens`): `A_K(x) = Σ_{q ≤ x} F_q(x)` where
  `F_q(x)` collects the prime powers `𝔭^k` of norm exactly `q`.
* **Prime norms** (`fiberMertens_prime`): for a rational prime `q` the fibre is the set of
  degree-one primes over `q`, so `F_q = n_K(q) log q/q`.
* **Composite norms** (`fiberMertens_le`): otherwise `q = p^m` with `m ≥ 2`, the fibre has at
  most `d` members and each contributes at most `d Λ(q)/q`; the tail `Σ_{q not prime} Λ(q)/q`
  converges, so `0 ≤ A_K(x) − Σ_{p ≤ x} n_K(p) log p/p ≤ d² (8 + C)`
  (`primeMertens_sub_degreeOneMertens_le`).
-/

noncomputable section

open Finset NumberField Ideal Filter Topology
open scoped Classical ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArtinMertens

variable {K : Type*} [Field K] [NumberField K]

local notation "d" => Module.finrank ℤ (𝓞 K)

/-- The number of **degree-one primes** over `p`: `n_K(p) = #{𝔭 : N𝔭 = p}`. -/
def degreeOneCount (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  ((idealsLe K p).filter fun P => P.IsPrime ∧ absNorm P = p).card

/-- The **degree-one Mertens sum** `Σ_{p ≤ x} n_K(p) log p/p`. -/
def degreeOneMertens (K : Type*) [Field K] [NumberField K] (x : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 x).filter Nat.Prime, (degreeOneCount K p : ℝ) * (Real.log p / p)

/-- The part of `A_K(x)` coming from the prime powers of norm exactly `q`. -/
def fiberMertens (K : Type*) [Field K] [NumberField K] (x q : ℕ) : ℝ :=
  ∑ pk ∈ (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q),
    Real.log (absNorm pk.1) / q

theorem fiberMertens_nonneg (x q : ℕ) : 0 ≤ fiberMertens K x q :=
  sum_nonneg fun _ _ => div_nonneg (log_absNorm_nonneg _) (Nat.cast_nonneg _)

/-- `A_K(x) = Σ_{q ≤ x} F_q(x)`. -/
theorem primeMertens_eq_sum_fiberMertens (x : ℕ) :
    primeMertens K x = ∑ q ∈ Icc 1 x, fiberMertens K x q := by
  have hmaps : ∀ pk ∈ primePowersLe K x, absNorm pk.1 ^ pk.2 ∈ Icc 1 x := by
    intro ⟨P, k⟩ hpk
    rw [mem_primePowersLe] at hpk
    have h2 := two_le_absNorm_of_isPrime hpk.1 hpk.2.1
    have hpos : 0 < absNorm P ^ k := pow_pos (by omega) k
    exact mem_Icc.mpr ⟨hpos, hpk.2.2.2⟩
  rw [primeMertens, ← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun q _ => sum_congr rfl fun pk hpk => ?_
  rw [(mem_filter.mp hpk).2]

/-- Over a rational prime `q ≤ x` the prime powers of norm `q` are the degree-one primes. -/
theorem card_fiber_prime {x q : ℕ} (hq : q.Prime) (hqx : q ≤ x) :
    ((primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q)).card = degreeOneCount K q := by
  rw [degreeOneCount]
  refine card_nbij' (fun pk => pk.1) (fun P => (P, 1)) ?_ ?_ ?_ ?_
  · intro ⟨P, k⟩ h
    simp only [coe_filter, Set.mem_setOf_eq, mem_primePowersLe, mem_idealsLe] at h ⊢
    obtain ⟨⟨hP, hP0, -, -⟩, hPq⟩ := h
    obtain ⟨hNP, rfl⟩ := hq.pow_eq_iff.mp hPq
    exact ⟨⟨hP0, hNP.le⟩, hP, hNP⟩
  · intro P h
    simp only [coe_filter, Set.mem_setOf_eq, mem_primePowersLe, mem_idealsLe] at h ⊢
    obtain ⟨⟨hP0, -⟩, hP, hNP⟩ := h
    exact ⟨⟨hP, hP0, le_rfl, by rw [pow_one, hNP]; exact hqx⟩, by rw [pow_one, hNP]⟩
  · intro ⟨P, k⟩ h
    simp only [coe_filter, Set.mem_setOf_eq] at h
    obtain ⟨-, rfl⟩ := hq.pow_eq_iff.mp h.2
    rfl
  · intro P _
    rfl

/-- **Prime norms**: `F_q(x) = n_K(q) log q/q` for a rational prime `q ≤ x`. -/
theorem fiberMertens_prime {x q : ℕ} (hq : q.Prime) (hqx : q ≤ x) :
    fiberMertens K x q = (degreeOneCount K q : ℝ) * (Real.log q / q) := by
  rw [fiberMertens, ← card_fiber_prime hq hqx, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun pk h => ?_
  rw [(hq.pow_eq_iff.mp (mem_filter.mp h).2).1]

theorem notPrimeVonMangoldt_div_nonneg (q : ℕ) :
    0 ≤ RHTower.Mertens.notPrimeVonMangoldt q / q := by
  rw [RHTower.Mertens.notPrimeVonMangoldt]
  split_ifs
  · simp
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg q)

/-- **Composite norms**: `F_q(x) ≤ d² Λ(q)/q` when `q` is not prime. -/
theorem fiberMertens_le {x q : ℕ} (hq : ¬ q.Prime) :
    fiberMertens K x q ≤ (d : ℝ) ^ 2 * (RHTower.Mertens.notPrimeVonMangoldt q / q) := by
  rw [RHTower.Mertens.notPrimeVonMangoldt, if_neg hq]
  have hΛ : 0 ≤ (d : ℝ) * Λ q / q :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg)
      (Nat.cast_nonneg _)
  calc fiberMertens K x q
      ≤ ∑ _pk ∈ (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q),
          (d : ℝ) * Λ q / q := by
        refine sum_le_sum fun ⟨P, k⟩ hpk => ?_
        rw [mem_filter, mem_primePowersLe] at hpk
        have h := log_absNorm_le_mul_vonMangoldt hpk.1.1 hpk.1.2.1 hpk.1.2.2.1
        rw [hpk.2] at h
        exact div_le_div_of_nonneg_right h (Nat.cast_nonneg q)
    _ = (((primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q)).card : ℝ) *
          ((d : ℝ) * Λ q / q) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * ((d : ℝ) * Λ q / q) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_fiber_le x q) hΛ
    _ = (d : ℝ) ^ 2 * (Λ q / q) := by ring

/-- **Only degree-one primes matter**:
`0 ≤ A_K(x) − Σ_{p ≤ x} n_K(p) log p/p ≤ d² (8 + C)`. -/
theorem primeMertens_sub_degreeOneMertens_le (x : ℕ) :
    0 ≤ primeMertens K x - degreeOneMertens K x ∧
      primeMertens K x - degreeOneMertens K x ≤
        (d : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail) := by
  have hsplit : primeMertens K x = degreeOneMertens K x +
      ∑ q ∈ (Icc 1 x).filter (fun q => ¬ q.Prime), fiberMertens K x q := by
    rw [primeMertens_eq_sum_fiberMertens, ← sum_filter_add_sum_filter_not (Icc 1 x) Nat.Prime,
      degreeOneMertens]
    congr 1
    refine sum_congr rfl fun q hq => ?_
    rw [mem_filter, mem_Icc] at hq
    exact fiberMertens_prime hq.2 hq.1.2
  rw [hsplit, add_sub_cancel_left]
  refine ⟨sum_nonneg fun q _ => fiberMertens_nonneg x q, ?_⟩
  calc ∑ q ∈ (Icc 1 x).filter (fun q => ¬ q.Prime), fiberMertens K x q
      ≤ ∑ q ∈ (Icc 1 x).filter (fun q => ¬ q.Prime),
          (d : ℝ) ^ 2 * (RHTower.Mertens.notPrimeVonMangoldt q / q) :=
        sum_le_sum fun q hq => fiberMertens_le (mem_filter.mp hq).2
    _ ≤ ∑ q ∈ Icc 1 x, (d : ℝ) ^ 2 * (RHTower.Mertens.notPrimeVonMangoldt q / q) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun q _ _ =>
          mul_nonneg (by positivity) (notPrimeVonMangoldt_div_nonneg q)
    _ = (d : ℝ) ^ 2 * ∑ q ∈ Icc 1 x, RHTower.Mertens.notPrimeVonMangoldt q / q :=
        (mul_sum _ _ _).symm
    _ ≤ (d : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail) :=
        mul_le_mul_of_nonneg_left (RHTower.Mertens.tail_bounded x) (by positivity)

/-- **Mertens for degree-one primes**: `Σ_{p ≤ x} n_K(p) log p/p ∼ log x`. -/
theorem tendsto_degreeOneMertens_div_log :
    Tendsto (fun x : ℕ => degreeOneMertens K x / Real.log x) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hC : Tendsto (fun x : ℕ => (d : ℝ) ^ 2 * (8 + RHTower.Mertens.mertensTail) /
      Real.log x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hR : Tendsto (fun x : ℕ => (primeMertens K x - degreeOneMertens K x) / Real.log x)
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hC
    · filter_upwards [hlog.eventually_ge_atTop 0] with x hx
      exact div_nonneg (primeMertens_sub_degreeOneMertens_le x).1 hx
    · filter_upwards [hlog.eventually_ge_atTop 0] with x hx
      exact div_le_div_of_nonneg_right (primeMertens_sub_degreeOneMertens_le x).2 hx
  have h := (tendsto_primeMertens_div_log (K := K)).sub hR
  rw [sub_zero] at h
  refine h.congr fun x => ?_
  ring

end GaloisForLFunctions.ArtinMertens
