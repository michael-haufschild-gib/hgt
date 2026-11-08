import GaloisForLFunctions.InfiniteRankWeilTheory.LongMeanValuesAreCollisionCounts
import GaloisForLFunctions.ArithmeticKreinLangerTheory.ChebyshevsProducerPassesTheIntegerChebyshevCap

/-!
# Prime collisions have collision size

The off-diagonal of the long mean value of the prime polynomial is a count of prime pairs at
multiplicative distance `≲ 1/T`. Its exact asymptotic is the Hardy–Littlewood pair constant, a binary
problem. Its **order of magnitude** is unconditional.

* `sq_sum_div_le_collisionCount`: for nonnegative coefficients on `[1, X]`, the collision count at
  scale `η` is at least `(Σ a)²/K`, `K = ⌊log X/η⌋ + 1`: cut `[0, log X]` into `K` cells of length `η`;
  two integers in one cell collide, and Cauchy–Schwarz over the cells does the rest.
* `fejerMean_vonMangoldt_ge`: hence the Fejér mean value of `Σ_{n≤X} Λ(n) n^{−it}` is at least
  `(2T/π²) ψ(X)²/(⌊T log X/π⌋ + 1)`, of order `X²/log X` by Chebyshev
  (`fejerMean_vonMangoldt_ge_chebyshev`).
* `fejerMean_vonMangoldt_le`: and at most `(log X)²(TX/2 + 6X²)`, since `0 ≤ Λ ≤ log X` and the Fejér
  kernel is nonnegative.
* `diagonal_vonMangoldt_le`: the diagonal `(T/2)Σ_{n≤X}Λ(n)²` is at most `(T/2) ψ(X) log X`.

So for `X ≥ T` the long mean value of the prime polynomial has order `X²` up to logarithms, carried by
prime pairs `p, p'` with `|p − p'| ≲ X/T`, and dominates the diagonal once `X ≫ T log³X`. What remains
is the constant of the prime pair count: the binary content that Type I/II information cannot see.
-/

open Real Finset

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- **Cauchy–Schwarz collisions.** For nonnegative coefficients on positive integers with
`log n < Kη`, the collision count at scale `η` is at least `(Σ a)²/K`. -/
theorem sq_sum_div_le_collisionCount (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) {a : ℕ → ℝ}
    (ha : ∀ n ∈ S, 0 ≤ a n) {η : ℝ} (hη : 0 < η) {K : ℕ} (hK0 : 0 < K)
    (hK : ∀ n ∈ S, Real.log n < K * η) :
    (∑ n ∈ S, a n) ^ 2 / K ≤ collisionCount S a η := by
  classical
  set cell : ℕ → ℕ := fun n => ⌊Real.log n / η⌋₊ with hcell
  have hlog0 : ∀ n ∈ S, 0 ≤ Real.log n := fun n hn =>
    Real.log_nonneg (by exact_mod_cast hS n hn)
  have hcellK : ∀ n ∈ S, cell n ∈ range K := fun n hn => by
    refine mem_range.2 ((Nat.floor_lt (div_nonneg (hlog0 n hn) hη.le)).2 ?_)
    rw [div_lt_iff₀ hη]; exact hK n hn
  -- integers in one cell collide
  have hsame : ∀ m ∈ S, ∀ n ∈ S, cell m = cell n → |Real.log n - Real.log m| ≤ η := by
    intro m hm n hn h
    have bounds : ∀ k ∈ S, (cell k : ℝ) * η ≤ Real.log k ∧ Real.log k < (cell k + 1) * η :=
      fun k hk => by
        have h1 := Nat.floor_le (div_nonneg (hlog0 k hk) hη.le)
        have h2 := Nat.lt_floor_add_one (Real.log k / η)
        constructor
        · rwa [le_div_iff₀ hη] at h1
        · rwa [div_lt_iff₀ hη] at h2
    obtain ⟨hm1, hm2⟩ := bounds m hm
    obtain ⟨hn1, hn2⟩ := bounds n hn
    rw [h] at hm1 hm2
    rw [abs_le]; constructor <;> nlinarith
  set A : ℕ → ℝ := fun b => ∑ n ∈ S with cell n = b, a n with hA
  -- the collision count dominates the sum of squares of the cell masses
  have hdom : ∑ b ∈ range K, A b ^ 2 ≤ collisionCount S a η := by
    have hcells : ∑ b ∈ range K, A b ^ 2 = ∑ m ∈ S, a m * A (cell m) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := cell) (t := range K) hcellK]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [sq, hA]
      simp only
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [(Finset.mem_filter.1 hm).2]
    rw [hcells, collisionCount]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [hA]; simp only
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n hn _ =>
      mul_nonneg (ha m hm) (ha n (Finset.mem_filter.1 hn).1))
    obtain ⟨hnS, hc⟩ := Finset.mem_filter.1 hn
    exact Finset.mem_filter.2 ⟨hnS, hsame m hm n hnS hc.symm⟩
  have htotal : ∑ b ∈ range K, A b = ∑ n ∈ S, a n :=
    Finset.sum_fiberwise_of_maps_to (g := cell) (t := range K) hcellK a
  have hcs := sq_sum_le_card_mul_sum_sq (s := range K) (f := A)
  rw [htotal, card_range] at hcs
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  rw [div_le_iff₀ hKr]
  nlinarith

/-- **The long prime mean value from below.** For `X ≥ 1` and `T > 0`,
`∫_0^T (1 − t/T)|Σ_{n≤X} Λ(n) n^{−it}|² dt ≥ (2T/π²) ψ(X)²/(⌊T log X/π⌋ + 1)`. -/
theorem fejerMean_vonMangoldt_ge (X : ℕ) {T : ℝ} (hT : 0 < T) :
    2 * T / Real.pi ^ 2 * (Chebyshev.psi X ^ 2 / (⌊T * Real.log X / Real.pi⌋₊ + 1 : ℕ)) ≤
      fejerMean (Finset.Icc 1 X) (fun n => ArithmeticFunction.vonMangoldt n) T := by
  have hpi := Real.pi_pos
  have hpsi : Chebyshev.psi X = ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    rfl
  have hK : ∀ n ∈ Finset.Icc 1 X,
      Real.log n < ((⌊T * Real.log X / Real.pi⌋₊ + 1 : ℕ) : ℝ) * (Real.pi / T) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.1 hn).2
    have hlog : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) hnX
    have hfl := Nat.lt_floor_add_one (T * Real.log X / Real.pi)
    push_cast
    rw [div_lt_iff₀ hpi] at hfl
    calc Real.log n ≤ Real.log X := hlog
      _ = T * Real.log X / Real.pi * (Real.pi / T) := by field_simp
      _ < (⌊T * Real.log X / Real.pi⌋₊ + 1) * (Real.pi / T) := by
          refine mul_lt_mul_of_pos_right ?_ (by positivity)
          rw [div_lt_iff₀ hpi]; linarith
  have hcs := sq_sum_div_le_collisionCount (Finset.Icc 1 X) (fun n hn => (Finset.mem_Icc.1 hn).1)
    (a := fun n => ArithmeticFunction.vonMangoldt n) (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
    (by positivity : 0 < Real.pi / T) (Nat.succ_pos _) hK
  rw [← hpsi] at hcs
  exact (mul_le_mul_of_nonneg_left hcs (by positivity)).trans
    (collisionCount_le_fejerMean _ (fun n _ => ArithmeticFunction.vonMangoldt_nonneg) hT)

/-- With Chebyshev's bound `ψ(X) ≥ 0.89X − O(log X)`: the mean value is of order `X²/log X`. -/
theorem fejerMean_vonMangoldt_ge_chebyshev {X : ℕ} (hX : 30 ≤ X) {T : ℝ} (hT : 0 < T)
    (hpos : 0 ≤ (89 / 100 : ℝ) * X - 30 - 3 - Real.log 30 - 3 / 2 * Real.log X) :
    2 * T / Real.pi ^ 2 * (((89 / 100 : ℝ) * X - 30 - 3 - Real.log 30 - 3 / 2 * Real.log X) ^ 2 /
        (⌊T * Real.log X / Real.pi⌋₊ + 1 : ℕ)) ≤
      fejerMean (Finset.Icc 1 X) (fun n => ArithmeticFunction.vonMangoldt n) T := by
  refine le_trans ?_ (fejerMean_vonMangoldt_ge X hT)
  have hcheb := ArithmeticKreinLangerTheory.psi_ge_of_chebyshev (x := X) (by exact_mod_cast hX)
  have hsq : ((89 / 100 : ℝ) * X - 30 - 3 - Real.log 30 - 3 / 2 * Real.log X) ^ 2 ≤
      Chebyshev.psi X ^ 2 := pow_le_pow_left₀ hpos hcheb 2
  gcongr

/-- **The long prime mean value from above.** `≤ (log X)²(TX/2 + 6X²)`. -/
theorem fejerMean_vonMangoldt_le (X : ℕ) {T : ℝ} (hT : 0 < T) :
    fejerMean (Finset.Icc 1 X) (fun n => ArithmeticFunction.vonMangoldt n) T ≤
      Real.log X ^ 2 * (T * X / 2 + 6 * X ^ 2) := by
  have hlogX : ∀ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n ≤ Real.log X := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by linarith) (by exact_mod_cast (Finset.mem_Icc.1 hn).2))
  rw [fejerMean_eq _ _ hT]
  calc ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt m *
        ArithmeticFunction.vonMangoldt n * fejerKernel T (Real.log n - Real.log m)
      ≤ ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          Real.log X ^ 2 * (1 * 1 * fejerKernel T (Real.log n - Real.log m)) := by
        refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => ?_
        have hk := fejerKernel_nonneg hT (Real.log n - Real.log m)
        have h1 := hlogX m hm
        have h2 := hlogX n hn
        have h0m : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
        have h0n : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        have : ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt n ≤
            Real.log X ^ 2 := by nlinarith
        nlinarith
    _ = Real.log X ^ 2 * fejerMean (Finset.Icc 1 X) (fun _ => 1) T := by
        rw [fejerMean_eq _ _ hT, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (fejerMean_one_le X hT) (sq_nonneg _)

/-- The diagonal `(T/2)Σ_{n≤X} Λ(n)²` is at most `(T/2) ψ(X) log X`. -/
theorem diagonal_vonMangoldt_le (X : ℕ) {T : ℝ} (hT : 0 < T) :
    T / 2 * ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n ^ 2 ≤
      T / 2 * (Chebyshev.psi X * Real.log X) := by
  have hpsi : Chebyshev.psi X = ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    rfl
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [hpsi, Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
  have hle : ArithmeticFunction.vonMangoldt n ≤ Real.log X := ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by linarith) (by exact_mod_cast (Finset.mem_Icc.1 hn).2))
  rw [sq]
  exact mul_le_mul_of_nonneg_left hle ArithmeticFunction.vonMangoldt_nonneg

end GaloisForLFunctions.InfiniteRankWeilTheory
