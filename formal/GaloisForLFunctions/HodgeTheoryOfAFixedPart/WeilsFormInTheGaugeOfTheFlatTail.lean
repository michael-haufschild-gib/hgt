import GaloisForLFunctions.HodgeTheoryOfAFixedPart.TheNormalFormOfThePairingOfTheDegreePoints
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheCarryIsTheDefectOfTheWindowCount

/-!
# Weil's form in the gauge of the flat tail

The flat tail `T_N = Σ_{n ≤ N} γ_n` has the coordinates `c ≡ 1`. Its degrees are `d₂ = N` and
`d₁ = H_N`: in the normal form it is the second ruling, cut at `N`. This file computes Weil's form
on the comb in the gauge of this divisor.

* **The gauge** (`combForm_eq_gauge`): on every finite set `S`,
  `2 d₁ d₂ − D·D = Σ c_n² ρ_S(n) + ½ Σ_{m≠n} (Γ_m·Γ_n − 1/m − 1/n)(c_m − c_n)²`, with
  `ρ_S(n)` the pairing of Weil's form of the flat divisor of `S` with `γ_n`
  (`formBilin_one`).
* **The contacts of a graph with the tail** (`sum_contact_erase_Icc`): `Γ_n` meets the graphs
  below it in `log n` and the graphs `Γ_{nk}`, `nk ≤ N`, in `ψ(N/n)`, Chebyshev's function.
* **The potential is the remainder of the prime number theorem** (`tailPotential_Icc`): on
  `S = [1, N]`,
  `ρ(n) = N/n − ψ(N/n) + H_N − ½(H_{N−n} + H_{N+n}) + 3/(4n) − log 2π`.
  Along `N = kn` it tends to `k − ψ(k) − log 2π − ½ log(1 − k⁻²)` (`tendsto_tailRow_mul`), the
  right side of von Mangoldt's formula for `ψ` at `k`. The pairing of the cut ruling with a graph
  is its degree up to the remainder of the prime number theorem at the ratio of the cut to the
  degree point.
* **Chebyshev's identity is the contact energy of the tail** (`sum_chebyshev_div`,
  `sum_sum_contact_Icc`): `Σ_{n ≤ N} ψ(N/n) = log N!`, and the contacts among the first `N`
  graphs sum to `log N!`, the logarithm of their gluing index.
* **The form of the flat tail** (`combForm_flatTail`, `tendsto_combForm_flatTail_div`):
  `2N·H_N − (N + ½)H_{2N} + (5/4)H_N + N − log N! − N log 2π`, and per degree point it tends to
  `2 + γ − log 4π`.
* **The carry cocycle** (`sum_log_Ioc`, `sum_counterterm_Ioc`): the gluing conditions of the
  block `(M, M + N]` are those of its translate `[1, N]` plus `log C(M + N, M)`, the `Λ`-weighted
  number of carries of `M + N`. The counterterm of a block is the counterterm of its translate
  to the origin plus the carry cocycle: the contacts are not invariant under addition, and the
  defect is the carries.
* **The octave above the tail has no primes** (`sum_contact_Icc_of_octave`,
  `sum_chebyshev_octave`): a graph `Γ_n`, `N < n ≤ 2N + 1`, meets the tail in `log n`; summed
  over the lines `n ≤ N`, the prime counts `ψ(2N/n) − ψ(N/n)` of the octaves are
  `log C(2N, N) + log N!`. The line `n = 1` carries the primes of `(N, 2N]`; the lines `n ≥ 2`
  carry the carries and the gluing index of the tail (`sum_chebyshev_octave_lines`).
-/

open Finset Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open AbsoluteGeometryOfSpecZ

/-! ### The bilinear forms -/

/-- The pairing of two real divisors on `S`. -/
def combBilin (S : Finset ℕ) (c e : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, ∑ m ∈ S.erase n, c m * e n * pairKernel m n - ∑ n ∈ S, c n * e n * counterterm n

theorem combBilin_self (S : Finset ℕ) (c : ℕ → ℝ) : combBilin S c c = combPairing S c := by
  rw [combBilin, combPairing]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Weil's form on the comb as a bilinear form: the pole plane minus the pairing. -/
def formBilin (S : Finset ℕ) (c e : ℕ → ℝ) : ℝ :=
  degOne S c * degTwo S e + degTwo S c * degOne S e - combBilin S c e

theorem formBilin_self (S : Finset ℕ) (c : ℕ → ℝ) : formBilin S c c = combForm S c := by
  rw [formBilin, combForm, combBilin_self]
  ring

/-- The potential of Weil's form in the gauge of the flat divisor of `S`: the row of the pole
plane minus the potential of the pairing. -/
def tailPotential (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ m ∈ S, (1 / (m : ℝ) + 1 / (n : ℝ)) - combPotential S n

/-- **The row of the flat divisor.** Weil's form of the flat divisor of `S` and a divisor `e`
is `Σ e_n ρ_S(n)`. -/
theorem formBilin_one (S : Finset ℕ) (e : ℕ → ℝ) :
    formBilin S (fun _ => 1) e = ∑ n ∈ S, e n * tailPotential S n := by
  have h1 : degOne S (fun _ => 1) * degTwo S e = ∑ n ∈ S, e n * ∑ m ∈ S, 1 / (m : ℝ) := by
    rw [degOne, degTwo, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => mul_comm _ _
  have h2 : degTwo S (fun _ => 1) * degOne S e = ∑ n ∈ S, e n * ∑ _m ∈ S, 1 / (n : ℝ) := by
    rw [degOne, degTwo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have h3 : combBilin S (fun _ => 1) e = ∑ n ∈ S, e n * combPotential S n := by
    rw [combBilin, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [combPotential, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun m _ => by ring
    · ring
  rw [formBilin, h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [tailPotential, Finset.sum_add_distrib]
  ring

/-! ### The gauge of the flat divisor -/

/-- The pole plane in Lévy–Khintchine form. -/
theorem two_mul_degOne_mul_degTwo (S : Finset ℕ) (c : ℕ → ℝ) :
    2 * (degOne S c * degTwo S c) =
      ∑ n ∈ S, c n ^ 2 * ∑ m ∈ S, (1 / (m : ℝ) + 1 / (n : ℝ)) -
        (∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 * (1 / (m : ℝ) + 1 / (n : ℝ))) / 2 := by
  have hLK := sum_mul_mul_eq_row_sub_dirichlet S (fun m n : ℕ => 1 / (m : ℝ) + 1 / (n : ℝ))
    (fun m n => add_comm _ _) c
  -- the pole plane as a double sum
  have hdouble : 2 * (degOne S c * degTwo S c) =
      ∑ n ∈ S, ∑ m ∈ S, c m * c n * (1 / (m : ℝ) + 1 / (n : ℝ)) := by
    have ha : degOne S c * degTwo S c = ∑ n ∈ S, ∑ m ∈ S, c m * c n * (1 / (n : ℝ)) := by
      rw [degOne, degTwo, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hb : degOne S c * degTwo S c = ∑ n ∈ S, ∑ m ∈ S, c m * c n * (1 / (m : ℝ)) := by
      rw [ha, Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
    rw [two_mul]
    nth_rewrite 1 [hb]
    rw [ha, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  -- the diagonal and the rest
  have hdiag : ∀ n ∈ S, ∑ m ∈ S, c m * c n * (1 / (m : ℝ) + 1 / (n : ℝ)) =
      c n ^ 2 * (1 / (n : ℝ) + 1 / (n : ℝ)) +
        ∑ m ∈ S.erase n, c m * c n * (1 / (m : ℝ) + 1 / (n : ℝ)) := fun n hn => by
    rw [← Finset.add_sum_erase S _ hn]
    ring
  have hrow : ∀ n ∈ S, ∑ m ∈ S, (1 / (m : ℝ) + 1 / (n : ℝ)) =
      (1 / (n : ℝ) + 1 / (n : ℝ)) + ∑ m ∈ S.erase n, (1 / (m : ℝ) + 1 / (n : ℝ)) :=
    fun n hn => (Finset.add_sum_erase S _ hn).symm
  rw [hdouble, Finset.sum_congr rfl hdiag, Finset.sum_add_distrib, hLK,
    Finset.sum_congr rfl fun n hn => by rw [hrow n hn]]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- **Weil's form in the gauge of the flat divisor.** -/
theorem combForm_eq_gauge (S : Finset ℕ) (c : ℕ → ℝ) :
    combForm S c = ∑ n ∈ S, c n ^ 2 * tailPotential S n +
      (∑ n ∈ S, ∑ m ∈ S.erase n,
        (c m - c n) ^ 2 * (pairKernel m n - (1 / (m : ℝ) + 1 / (n : ℝ)))) / 2 := by
  have hD : ∑ n ∈ S, ∑ m ∈ S.erase n,
        (c m - c n) ^ 2 * (pairKernel m n - (1 / (m : ℝ) + 1 / (n : ℝ))) =
      combDirichlet S c -
        ∑ n ∈ S, ∑ m ∈ S.erase n, (c m - c n) ^ 2 * (1 / (m : ℝ) + 1 / (n : ℝ)) := by
    rw [combDirichlet, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hpot : ∑ n ∈ S, c n ^ 2 * tailPotential S n =
      ∑ n ∈ S, c n ^ 2 * ∑ m ∈ S, (1 / (m : ℝ) + 1 / (n : ℝ)) -
        ∑ n ∈ S, c n ^ 2 * combPotential S n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [tailPotential, mul_sub]
  rw [combForm, two_mul_degOne_mul_degTwo, combPairing_eq_potential_sub_dirichlet, hD, hpot]
  ring

/-! ### The rows of the tail -/

/-- Chebyshev's function at a natural number: `ψ(K) = Σ_{k ≤ K} Λ(k)`. -/
def chebyshev (K : ℕ) : ℝ := ∑ k ∈ Icc 1 K, (Λ k : ℝ)

/-- The contacts of `Γ_n` with the graphs of its proper divisors in `S`. -/
theorem sum_down_erase {S : Finset ℕ} {n : ℕ} (hn : 0 < n) (hS : n.properDivisors ⊆ S) :
    ∑ m ∈ S.erase n, (if m ∣ n then (Λ (n / m) : ℝ) else 0) = Real.log n := by
  rw [← Finset.sum_filter]
  have hfilter : (S.erase n).filter (· ∣ n) = n.properDivisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_properDivisors]
    constructor
    · rintro ⟨⟨hne, -⟩, hd⟩
      exact ⟨hd, lt_of_le_of_ne (Nat.le_of_dvd hn hd) hne⟩
    · rintro ⟨hd, hlt⟩
      exact ⟨⟨hlt.ne, hS (Nat.mem_properDivisors.mpr ⟨hd, hlt⟩)⟩, hd⟩
  rw [hfilter]
  exact sum_vonMangoldt_div_properDivisors hn

theorem properDivisors_subset_Icc {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    n.properDivisors ⊆ Icc 1 N := fun m hm => by
  rw [Nat.mem_properDivisors] at hm
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hm.1 (by omega), by omega⟩

/-- **The contacts above a degree point are Chebyshev's function**: the graphs `Γ_{nk}`,
`nk ≤ N`, meet `Γ_n` in `ψ(N/n)`. -/
theorem sum_vonMangoldt_multiples {N n : ℕ} (hn : 0 < n) :
    ∑ m ∈ ((Icc 1 N).erase n).filter (n ∣ ·), (Λ (m / n) : ℝ) = chebyshev (N / n) := by
  have h1 : ∑ k ∈ (Icc 1 (N / n)).erase 1, (Λ k : ℝ) = chebyshev (N / n) :=
    Finset.sum_erase _ (by simp)
  rw [← h1]
  refine Finset.sum_nbij' (fun m => m / n) (fun k => n * k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hm1, k, rfl⟩ := Finset.mem_filter.mp hm
    obtain ⟨hne, hmS⟩ := Finset.mem_erase.mp hm1
    obtain ⟨hlow, htop⟩ := Finset.mem_Icc.mp hmS
    rw [Nat.mul_div_cancel_left k hn]
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    refine Finset.mem_erase.mpr ⟨fun h => hne (by rw [h, mul_one]), Finset.mem_Icc.mpr ⟨by omega, ?_⟩⟩
    rw [Nat.le_div_iff_mul_le hn, mul_comm]
    exact htop
  · intro k hk
    obtain ⟨hk1, hkS⟩ := Finset.mem_erase.mp hk
    obtain ⟨hlow, htop⟩ := Finset.mem_Icc.mp hkS
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => hk1 ?_, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩,
      dvd_mul_right n k⟩
    · exact Nat.eq_of_mul_eq_mul_left hn (by rw [h, mul_one])
    · exact Nat.mul_pos hn (by omega)
    · exact (Nat.mul_le_mul_left n htop).trans (Nat.mul_div_le N n)
  · intro m hm
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2
  · intro k _
    exact Nat.mul_div_cancel_left k hn
  · intro m _
    rfl

/-- **The contacts of a graph with the tail**: `log n` below and `ψ(N/n)` above. -/
theorem sum_contact_erase_Icc {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    ∑ m ∈ (Icc 1 N).erase n, contact m n = Real.log n + chebyshev (N / n) := by
  have hlow : ∑ m ∈ ((Icc 1 N).erase n).filter (· ∣ n), (Λ (n / m) : ℝ) = Real.log n := by
    rw [Finset.sum_filter]
    exact sum_down_erase (by omega) (properDivisors_subset_Icc hn hN)
  rw [sum_contact_erase, hlow, sum_vonMangoldt_multiples (by omega)]

/-- The row of the jets on the tail. -/
theorem sum_jetKernel_erase_Icc {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    ∑ m ∈ (Icc 1 N).erase n, jetKernel m n =
      (harm (N - n) + harm (N + n)) / 2 - 3 / (4 * (n : ℝ)) := by
  have hsplit : (Icc 1 N).erase n = Ico 1 n ∪ Ioc n N := by
    ext m
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico,
      Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Ico 1 n) (Ioc n N) := Finset.disjoint_left.mpr fun m h1 h2 => by
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj, sum_jetKernel_row hn hN]

/-- **The potential of the pairing on the tail**: the harmonic row of the jets, Chebyshev's
function of the quotient, and `log 2π`. -/
theorem combPotential_Icc {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    combPotential (Icc 1 N) n = (harm (N - n) + harm (N + n)) / 2 - 3 / (4 * (n : ℝ)) +
      chebyshev (N / n) + Real.log (2 * Real.pi) := by
  rw [combPotential_eq_of_properDivisors_subset (by omega) (properDivisors_subset_Icc hn hN),
    sum_jetKernel_erase_Icc hn hN, sum_vonMangoldt_multiples (by omega)]

/-- The row of the tail at the degree point `n`:
`N/n − ψ(N/n) + H_N − ½(H_{N−n} + H_{N+n}) + 3/(4n) − log 2π`. -/
def tailRow (N n : ℕ) : ℝ :=
  (N : ℝ) / n - chebyshev (N / n) + harm N - (harm (N - n) + harm (N + n)) / 2 +
    3 / (4 * (n : ℝ)) - Real.log (2 * Real.pi)

theorem sum_Icc_one_div (N : ℕ) : ∑ m ∈ Icc 1 N, 1 / (m : ℝ) = harm N := by
  rw [sum_Icc_one_eq_sum_range, harm]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring_nf

/-- **The potential is the remainder of the prime number theorem.** In the gauge of the flat
tail the potential of Weil's form at `n ≤ N` is the row `tailRow N n`. -/
theorem tailPotential_Icc {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    tailPotential (Icc 1 N) n = tailRow N n := by
  rw [tailPotential, combPotential_Icc hn hN, Finset.sum_add_distrib, sum_Icc_one_div,
    Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, tailRow]
  simp only [Nat.add_sub_cancel]
  ring

/-- **The cut ruling pairs with a divisor through the remainder of the prime number theorem.** -/
theorem formBilin_flatTail (N : ℕ) (e : ℕ → ℝ) :
    formBilin (Icc 1 N) (fun _ => 1) e = ∑ n ∈ Icc 1 N, e n * tailRow N n := by
  rw [formBilin_one]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [tailPotential_Icc (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]

/-! ### Chebyshev's identity and the form of the flat tail -/

theorem sum_log_Icc (N : ℕ) : ∑ n ∈ Icc 1 N, Real.log n = Real.log (N.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hf : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul hk hf]
    ring

/-- **The contacts among the first `N` graphs sum to `log N!`**, each pair counted twice. -/
theorem sum_sum_contact_Icc (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, contact m n = 2 * Real.log (N.factorial : ℝ) := by
  have hsplit : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, contact m n =
      ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (if m ∣ n then (Λ (n / m) : ℝ) else 0) +
        ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (if n ∣ m then (Λ (m / n) : ℝ) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    rfl
  have hswap : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
        (if n ∣ m then (Λ (m / n) : ℝ) else 0) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).erase m, (if n ∣ m then (Λ (m / n) : ℝ) else 0) :=
    Finset.sum_comm' (s' := fun m => (Icc 1 N).erase m) (t' := Icc 1 N) fun n m => by
      simp only [Finset.mem_erase]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨Ne.symm h2, h1⟩, h3⟩,
        fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h2, Ne.symm h1, h3⟩⟩
  have hrow : ∀ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      (if m ∣ n then (Λ (n / m) : ℝ) else 0) = Real.log n := fun n hn =>
    sum_down_erase (by have := (Finset.mem_Icc.mp hn).1; omega)
      (properDivisors_subset_Icc (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2)
  rw [hsplit, hswap, Finset.sum_congr rfl hrow, sum_log_Icc]
  ring

/-- **Chebyshev's identity**: `Σ_{n ≤ N} ψ(N/n) = log N!`. -/
theorem sum_chebyshev_div (N : ℕ) :
    ∑ n ∈ Icc 1 N, chebyshev (N / n) = Real.log (N.factorial : ℝ) := by
  have h := sum_sum_contact_Icc N
  rw [Finset.sum_congr rfl fun n hn =>
    sum_contact_erase_Icc (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
    Finset.sum_add_distrib, sum_log_Icc] at h
  linarith

theorem jetEnergy_eq_sum_erase (N : ℕ) :
    jetEnergy N = ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, jetKernel m n := by
  unfold jetEnergy
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  rw [sum_jetKernel_erase_Icc hn1 hn2, sum_jetKernel_row hn1 hn2]

/-- **The pairing of the flat tail with itself**: the energy of the jets plus the logarithm of
the gluing index plus `N log 2π`. -/
theorem combPairing_flatTail (N : ℕ) :
    combPairing (Icc 1 N) (fun _ => 1) =
      jetEnergy N + Real.log (N.factorial : ℝ) + N * Real.log (2 * Real.pi) := by
  have hk : ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n, (1 : ℝ) * 1 * pairKernel m n =
      jetEnergy N + 2 * Real.log (N.factorial : ℝ) := by
    rw [jetEnergy_eq_sum_erase, ← sum_sum_contact_Icc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [pairKernel]; ring
  have hc : ∑ n ∈ Icc 1 N, (1 : ℝ) ^ 2 * counterterm n =
      Real.log (N.factorial : ℝ) - N * Real.log (2 * Real.pi) := by
    rw [← sum_log_div_two_pi]
    exact Finset.sum_congr rfl fun n _ => by rw [counterterm]; ring
  rw [combPairing, hk, hc]
  ring

/-- **Weil's form of the flat tail.** -/
theorem combForm_flatTail (N : ℕ) :
    combForm (Icc 1 N) (fun _ => 1) =
      2 * N * harm N - jetEnergy N - Real.log (N.factorial : ℝ) - N * Real.log (2 * Real.pi) := by
  have h1 : degOne (Icc 1 N) (fun _ => 1) = harm N := sum_Icc_one_div N
  have h2 : degTwo (Icc 1 N) (fun _ => (1 : ℝ)) = N := by
    rw [degTwo, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, Nat.add_sub_cancel]
  rw [combForm, h1, h2, combPairing_flatTail]
  ring

/-- **Per degree point the form of the flat tail tends to `2 + γ − log 4π`.** -/
theorem tendsto_combForm_flatTail_div :
    Tendsto (fun N : ℕ => combForm (Icc 1 N) (fun _ => 1) / N) atTop
      (𝓝 (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))) := by
  have ha := tendsto_harm_sub_log
  have hb := tendsto_log_factorial_div_sub
  have hc := tendsto_jetEnergy_sub_counterterm_div
  have h := (((ha.const_mul 2).sub hc).sub (hb.const_mul 2)).add_const 2
  rw [show 2 * Real.eulerMascheroniConstant -
      (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) - 2 * 0 + 2 =
      2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [combForm_flatTail, sum_log_div_two_pi]
  field_simp
  ring

/-- **Along `N = kn` the row of the tail tends to the remainder of the prime number theorem at
`k`**: `k − ψ(k) − log 2π − ½ log(1 − k⁻²)`. -/
theorem tendsto_tailRow_mul {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => tailRow (k * n) n) atTop
      (𝓝 ((k : ℝ) - chebyshev k - Real.log (2 * Real.pi) -
        Real.log (1 - 1 / (k : ℝ) ^ 2) / 2)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsub : ∀ a : ℕ, 0 < a →
      Tendsto (fun n : ℕ => harm (a * n) - Real.log ((a * n : ℕ) : ℝ)) atTop
        (𝓝 Real.eulerMascheroniConstant) := fun a ha =>
    tendsto_harm_sub_log.comp
      (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n ha) tendsto_id)
  have h1 := hsub k (by omega)
  have h2 := hsub (k - 1) (by omega)
  have h3 := hsub (k + 1) (by omega)
  have h4 : Tendsto (fun n : ℕ => 3 / (4 * (n : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 / 4)
    rw [mul_zero] at this
    exact this.congr fun n => by ring
  have h := ((h1.sub ((h2.add h3).div_const 2)).add h4).const_add
    ((k : ℝ) - chebyshev k - Real.log (2 * Real.pi) - Real.log (1 - 1 / (k : ℝ) ^ 2) / 2)
  rw [show (k : ℝ) - chebyshev k - Real.log (2 * Real.pi) - Real.log (1 - 1 / (k : ℝ) ^ 2) / 2 +
      (Real.eulerMascheroniConstant -
        (Real.eulerMascheroniConstant + Real.eulerMascheroniConstant) / 2 + 0) =
      (k : ℝ) - chebyshev k - Real.log (2 * Real.pi) - Real.log (1 - 1 / (k : ℝ) ^ 2) / 2 by
    ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have e1 : k * n - n = (k - 1) * n := by rw [Nat.sub_mul, one_mul]
  have e2 : k * n + n = (k + 1) * n := by ring
  have e3 : k * n / n = k := Nat.mul_div_cancel k (by omega)
  have hc1 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  -- the logarithms
  have hlog : Real.log (1 - 1 / (k : ℝ) ^ 2) =
      Real.log ((k : ℝ) - 1) + Real.log ((k : ℝ) + 1) - 2 * Real.log k := by
    have : 1 - 1 / (k : ℝ) ^ 2 = ((k : ℝ) - 1) * ((k : ℝ) + 1) / (k : ℝ) ^ 2 := by
      field_simp
      ring
    rw [this, Real.log_div (by positivity) (by positivity),
      Real.log_mul hkm.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have l1 : Real.log ((k * n : ℕ) : ℝ) = Real.log k + Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hk0.ne' hn'.ne']
  have l2 : Real.log (((k - 1) * n : ℕ) : ℝ) = Real.log ((k : ℝ) - 1) + Real.log n := by
    rw [Nat.cast_mul, hc1, Real.log_mul hkm.ne' hn'.ne']
  have l3 : Real.log (((k + 1) * n : ℕ) : ℝ) = Real.log ((k : ℝ) + 1) + Real.log n := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) hn'.ne']
    push_cast
    rfl
  have hdiv : ((k * n : ℕ) : ℝ) / n = k := by
    rw [Nat.cast_mul]
    field_simp
  rw [tailRow, e1, e2, e3, hdiv, l1, l2, l3, hlog]
  ring

/-! ### The carry cocycle -/

/-- The carry cocycle: `log C(M + N, M)`. -/
def carryCocycle (M N : ℕ) : ℝ := Real.log (((M + N).choose M : ℕ) : ℝ)

/-- The carry cocycle is the `Λ`-weighted number of carries of `M + N`. -/
theorem carryCocycle_eq_sum_carry (M N : ℕ) :
    carryCocycle M N = ∑ k ∈ Icc 1 (M + N), if k ≤ M % k + N % k then (Λ k : ℝ) else 0 :=
  log_choose_eq_sum_carry M N

/-- **The gluing conditions of a block are those of its translate to the origin plus the carry
cocycle.** -/
theorem sum_log_Ioc (M N : ℕ) :
    ∑ n ∈ Ioc M (M + N), Real.log n = Real.log (N.factorial : ℝ) + carryCocycle M N := by
  have h1 : ∑ n ∈ Ioc M (M + N), Real.log n =
      Real.log ((M + N).factorial : ℝ) - Real.log (M.factorial : ℝ) := by
    rw [← sum_log_Icc, ← sum_log_Icc, Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) (Nat.le_add_right M N)]
    ring
  have hfac : (((M + N).choose M : ℕ) : ℝ) * (M.factorial : ℝ) * (N.factorial : ℝ) =
      ((M + N).factorial : ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial M N
  have hc : (0 : ℝ) < ((M + N).choose M : ℕ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right M N)
  have hM : (0 : ℝ) < (M.factorial : ℝ) := by exact_mod_cast M.factorial_pos
  have hN : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  rw [h1, ← hfac, Real.log_mul (by positivity) hN.ne', Real.log_mul hc.ne' hM.ne', carryCocycle]
  ring

/-- **The counterterm of a block is the counterterm of its translate plus the carry cocycle.** -/
theorem sum_counterterm_Ioc (M N : ℕ) :
    ∑ n ∈ Ioc M (M + N), counterterm n =
      ∑ n ∈ Icc 1 N, counterterm n + carryCocycle M N := by
  have hc : ∀ n : ℕ, 0 < n → counterterm n = Real.log n - Real.log (2 * Real.pi) := fun n hn => by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [counterterm, Real.log_div hn'.ne' (by positivity)]
  rw [Finset.sum_congr rfl fun n hn => hc n (by have := (Finset.mem_Ioc.mp hn).1; omega),
    Finset.sum_congr rfl fun n hn => hc n (by have := (Finset.mem_Icc.mp hn).1; omega),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_log_Ioc, sum_log_Icc, Finset.sum_const,
    Finset.sum_const, Nat.card_Ioc, Nat.card_Icc]
  simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel]
  ring

/-- The contacts of the graphs of a block with the graphs below them. -/
theorem sum_sum_contact_properDivisors_Ioc (M N : ℕ) :
    ∑ n ∈ Ioc M (M + N), ∑ m ∈ n.properDivisors, contact m n =
      Real.log (N.factorial : ℝ) + carryCocycle M N := by
  rw [← sum_log_Ioc]
  exact Finset.sum_congr rfl fun n hn =>
    sum_contact_properDivisors (by have := (Finset.mem_Ioc.mp hn).1; omega)

/-! ### The octave above the tail -/

/-- **The octave above the tail has no primes.** A graph `Γ_n`, `N < n ≤ 2N + 1`, meets the
tail `[1, N]` in `log n`. -/
theorem sum_contact_Icc_of_octave {N n : ℕ} (h1 : N < n) (h2 : n ≤ 2 * N + 1) :
    ∑ m ∈ Icc 1 N, contact m n = Real.log n := by
  have hterm : ∀ m ∈ Icc 1 N, contact m n = if m ∣ n then (Λ (n / m) : ℝ) else 0 := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hnm : ¬ n ∣ m := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
    rw [contact, if_neg hnm, add_zero]
  have hfilter : (Icc 1 N).filter (· ∣ n) = n.properDivisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_properDivisors]
    constructor
    · rintro ⟨⟨-, hm2⟩, hd⟩
      exact ⟨hd, by omega⟩
    · rintro ⟨hd, hlt⟩
      have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hd (by omega)
      obtain ⟨k, rfl⟩ := hd
      have hk : 2 ≤ k := by
        by_contra hk
        interval_cases k <;> omega
      have : m * 2 ≤ m * k := Nat.mul_le_mul_left m hk
      exact ⟨⟨hm0, by omega⟩, dvd_mul_right m k⟩
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, hfilter]
  exact sum_vonMangoldt_div_properDivisors (by omega)

theorem chebyshev_one : chebyshev 1 = 0 := by
  simp [chebyshev]

/-- **The octaves of the lines sum to the central binomial coefficient and the gluing index of
the tail**: `Σ_{n ≤ N} (ψ(2N/n) − ψ(N/n)) = log C(2N, N) + log N!`. -/
theorem sum_chebyshev_octave (N : ℕ) :
    ∑ n ∈ Icc 1 N, (chebyshev (2 * N / n) - chebyshev (N / n)) =
      Real.log ((Nat.centralBinom N : ℕ) : ℝ) + Real.log (N.factorial : ℝ) := by
  have hhigh : ∑ n ∈ Ioc N (2 * N), chebyshev (2 * N / n) = 0 :=
    Finset.sum_eq_zero fun n hn => by
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
      have h : 2 * N / n = 1 := by
        rw [Nat.div_eq_iff (by omega)]
        omega
      rw [h, chebyshev_one]
  have h2 : ∑ n ∈ Icc 1 N, chebyshev (2 * N / n) = Real.log ((2 * N).factorial : ℝ) := by
    have h := sum_chebyshev_div (2 * N)
    rw [Icc_one_eq_Ioc_zero,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) (by omega : N ≤ 2 * N), hhigh, add_zero,
      ← Icc_one_eq_Ioc_zero] at h
    exact h
  have hfac : ((Nat.centralBinom N : ℕ) : ℝ) * (N.factorial : ℝ) * (N.factorial : ℝ) =
      ((2 * N).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial N N
    rw [← two_mul, ← Nat.centralBinom_eq_two_mul_choose] at h
    exact_mod_cast h
  have hc : (0 : ℝ) < (Nat.centralBinom N : ℕ) := by exact_mod_cast Nat.centralBinom_pos N
  have hN : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  rw [Finset.sum_sub_distrib, h2, sum_chebyshev_div, ← hfac,
    Real.log_mul (by positivity) hN.ne', Real.log_mul hc.ne' hN.ne']
  ring

/-- **The line `n = 1` carries the primes of the octave; the lines `n ≥ 2` carry the carries and
the gluing index of the tail.** -/
theorem sum_chebyshev_octave_lines {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 2 N, (chebyshev (2 * N / n) - chebyshev (N / n)) =
      carryTerm N + Real.log (N.factorial : ℝ) := by
  have h := sum_chebyshev_octave N
  have hwin : chebyshev (2 * N) - chebyshev N = windowCount N := by
    rw [chebyshev, chebyshev, windowCount, Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) (by omega : N ≤ 2 * N)]
    ring
  have hsplit : Icc 1 N = insert 1 (Icc 2 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp), Nat.div_one, Nat.div_one, hwin,
    log_centralBinom_eq_carryTerm_add_window] at h
  linarith

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
