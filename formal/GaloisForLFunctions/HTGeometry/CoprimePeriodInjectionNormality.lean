import GaloisForLFunctions.HTGeometry.FourthPowerCycleEscape
import GaloisForLFunctions.HTGeometry.ParityDriftWeylCriterion

/-!
# First-power prime injections with coprime periods are equidistributed under `×4`

Let `q_j` be the `j`-th prime `≥ 5` and `p_j` the least prime factor of the base-4 repunit
`(4^{q_j} − 1)/3`; then `p_j ∤ 6` and `p_j ∣ 4^{q_j} − 1`, so the orbit of every `b/p_j` under `×4`
has period dividing `q_j`, and the periods are pairwise coprime.  For an exponent sequence growing
fast enough the number

`x = Σ_j p_j^{−1} 4^{−e_j}`

— every denominator a prime entering at the first power — has Weyl sums `o(N)` at every nonzero
frequency, hence `{4ⁿx}` is equidistributed and the parity drift of `x` is `o(N)`
(`not_parityDriftHypothesis_injNumber`).

Mechanism.  On the block `e_J ≤ n < e_{J+1}` the phase `e(h4ⁿx)` is, up to a tail error summing to
`O(|h|)`, the product of the periodic phases `e(h 4^{n−e_j}/p_j)`, `j ≤ J`.  By the Chinese
remainder theorem the mean over a common period is the product of the means
(`sum_range_mul_coprime`), and the escape bound `‖Σ_{t<q} e(b4ᵗ/p)‖ ≤ q − 1/72` makes the `j`-th
mean at most `1 − 1/(72 q_j)`; since `Σ 1/q_j = ∞` the product tends to `0`.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.FirstPowerInjection

open StonehamParityDrift BinaryParityDrift

/-! ### Periodic sums -/

/-- A sum of `L` consecutive values of an `L`-periodic sequence does not depend on the start. -/
theorem sum_range_add_of_periodic {L : ℕ} {Ψ : ℕ → ℂ} (hΨ : ∀ n, Ψ (n + L) = Ψ n) (a : ℕ) :
    ∑ n ∈ range L, Ψ (a + n) = ∑ n ∈ range L, Ψ n := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [sum_range_succ, sum_range_succ']
    have h1 : Ψ (a + 1 + L') = Ψ a := by rw [show a + 1 + L' = a + (L' + 1) by ring, hΨ]
    rw [h1, add_zero]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    congr 1; ring

/-- Blocks of an `L`-periodic unimodular sequence: `‖Σ_{n<ℓ} Ψ(a+n)‖ ≤ ℓ · μ + L` with
`μ = ‖Σ_{t<L} Ψ t‖ / L` the norm of the mean over a period. -/
theorem norm_sum_block_le {L : ℕ} (hL : 0 < L) {Ψ : ℕ → ℂ} (hΨ : ∀ n, Ψ (n + L) = Ψ n)
    (hΨ1 : ∀ n, ‖Ψ n‖ ≤ 1) (a ℓ : ℕ) :
    ‖∑ n ∈ range ℓ, Ψ (a + n)‖ ≤ ℓ * (‖∑ t ∈ range L, Ψ t‖ / L) + L := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hsplit : ℓ = L * (ℓ / L) + ℓ % L := (Nat.div_add_mod ℓ L).symm
  rw [hsplit, sum_range_add]
  have hfull : ∑ n ∈ range (L * (ℓ / L)), Ψ (a + n) =
      ((ℓ / L : ℕ) : ℂ) * ∑ t ∈ range L, Ψ t := by
    induction ℓ / L with
    | zero => simp
    | succ k ih =>
      rw [mul_add, mul_one, sum_range_add, ih]
      have := sum_range_add_of_periodic hΨ (a + L * k)
      simp_rw [add_assoc] at this
      rw [this]; push_cast; ring
  rw [hfull]
  calc ‖((ℓ / L : ℕ) : ℂ) * ∑ t ∈ range L, Ψ t + ∑ n ∈ range (ℓ % L), Ψ (a + (L * (ℓ / L) + n))‖
      ≤ (ℓ / L : ℕ) * ‖∑ t ∈ range L, Ψ t‖ + (ℓ % L : ℕ) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_natCast]
        · refine (norm_sum_le _ _).trans ?_
          simpa using sum_le_sum (fun n (_ : n ∈ range (ℓ % L)) => hΨ1 (a + (L * (ℓ / L) + n)))
    _ ≤ ((L * (ℓ / L) + ℓ % L : ℕ) : ℝ) * (‖∑ t ∈ range L, Ψ t‖ / L) + L := by
        have hmod : ((ℓ % L : ℕ) : ℝ) ≤ L := by exact_mod_cast (Nat.mod_lt _ hL).le
        have hS : 0 ≤ ‖∑ t ∈ range L, Ψ t‖ := norm_nonneg _
        have : ((L * (ℓ / L) : ℕ) : ℝ) * (‖∑ t ∈ range L, Ψ t‖ / L) =
            (ℓ / L : ℕ) * ‖∑ t ∈ range L, Ψ t‖ := by
          push_cast; field_simp
        have hnn : 0 ≤ ((ℓ % L : ℕ) : ℝ) * (‖∑ t ∈ range L, Ψ t‖ / L) := by positivity
        push_cast at this ⊢
        nlinarith

/-- **Chinese remainder theorem for means.**  If `f` is `a`-periodic, `g` is `b`-periodic and
`a, b` are coprime, the sum of `f g` over `a b` consecutive integers factors. -/
theorem sum_range_mul_coprime {a b : ℕ} (hab : a.Coprime b) {f g : ℕ → ℂ}
    (hf : ∀ n, f (n + a) = f n) (hg : ∀ n, g (n + b) = g n) :
    ∑ t ∈ range (a * b), f t * g t = (∑ t ∈ range a, f t) * ∑ t ∈ range b, g t := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  have hfk : ∀ k u, f (u + a * k) = f u := by
    intro k; induction k with
    | zero => simp
    | succ k ih => intro u; rw [show u + a * (k + 1) = (u + a * k) + a by ring, hf, ih]
  have hgk : ∀ k u, g (u + b * k) = g u := by
    intro k; induction k with
    | zero => simp
    | succ k ih => intro u; rw [show u + b * (k + 1) = (u + b * k) + b by ring, hg, ih]
  have hgmod : ∀ u, g u = g (u % b) := fun u => by
    conv_lhs => rw [← Nat.mod_add_div u b]
    exact hgk _ _
  rw [ThreeFiveOrbit.sum_range_mul_eq_sum_sum, sum_mul]
  refine sum_congr rfl fun u _ => ?_
  simp_rw [hfk, ← mul_sum]
  congr 1
  refine sum_nbij (fun k => (u + a * k) % b) (fun k _ => mem_range.mpr (Nat.mod_lt _ hb))
    ?_ ?_ (fun k _ => hgmod _)
  · intro k hk k' hk' hkk
    simp only [coe_range, Set.mem_Iio] at hk hk'
    have h1 : u + a * k ≡ u + a * k' [MOD b] := hkk
    have h2 : a * k ≡ a * k' [MOD b] := Nat.ModEq.add_left_cancel' u h1
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime
      (by rw [Nat.gcd_comm]; exact hab) h2) hk hk'
  · refine surjOn_of_injOn_of_card_le _ (fun k _ => by
      simpa using Nat.mod_lt _ hb) ?_ (by simp)
    intro k hk k' hk' hkk
    simp only [coe_range, Set.mem_Iio] at hk hk'
    have h1 : u + a * k ≡ u + a * k' [MOD b] := hkk
    have h2 : a * k ≡ a * k' [MOD b] := Nat.ModEq.add_left_cancel' u h1
    exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.cancel_left_of_coprime
      (by rw [Nat.gcd_comm]; exact hab) h2) hk hk'

/-! ### The injected primes -/

/-- `q_j`, the `j`-th prime `≥ 5`. -/
noncomputable def injPeriod (j : ℕ) : ℕ := Nat.nth Nat.Prime (j + 2)

/-- The base-4 repunit `Σ_{t<q} 4ᵗ = (4^q − 1)/3`. -/
def repunitFour (q : ℕ) : ℕ := ∑ t ∈ range q, 4 ^ t

/-- `p_j`, the least prime factor of the base-4 repunit of length `q_j`. -/
noncomputable def injPrime (j : ℕ) : ℕ := (repunitFour (injPeriod j)).minFac

theorem injPeriod_prime (j : ℕ) : (injPeriod j).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

theorem injPeriod_strictMono : StrictMono injPeriod :=
  fun _ _ h => Nat.nth_strictMono Nat.infinite_setOf_prime (by omega)

theorem five_le_injPeriod (j : ℕ) : 5 ≤ injPeriod j := by
  have h2 : Nat.nth Nat.Prime 2 = 5 := by
    have : Nat.count Nat.Prime 5 = 2 := by decide
    rw [← this, Nat.nth_count (by norm_num)]
  calc 5 = Nat.nth Nat.Prime 2 := h2.symm
    _ ≤ injPeriod j := (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone (by omega)

theorem three_mul_repunitFour (q : ℕ) : 3 * repunitFour q = 4 ^ q - 1 := by
  induction q with
  | zero => simp [repunitFour]
  | succ q ih =>
    simp only [repunitFour, sum_range_succ] at ih ⊢
    have : 1 ≤ 4 ^ q := Nat.one_le_pow _ _ (by norm_num)
    rw [mul_add, ih, pow_succ]
    omega

theorem repunitFour_mod_three (q : ℕ) : repunitFour q % 3 = q % 3 := by
  induction q with
  | zero => simp [repunitFour]
  | succ q ih =>
    simp only [repunitFour, sum_range_succ] at ih ⊢
    rw [Nat.add_mod, ih, Nat.pow_mod]
    norm_num

theorem repunitFour_mod_two {q : ℕ} (hq : 0 < q) : repunitFour q % 2 = 1 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  simp only [repunitFour]
  rw [sum_range_succ', Nat.add_mod, Finset.sum_nat_mod]
  have : ∀ i ∈ range q', 4 ^ (i + 1) % 2 = 0 := fun i _ => by
    rw [Nat.pow_mod]; norm_num
  rw [sum_congr rfl this]
  simp

theorem repunitFour_ne_one {q : ℕ} (hq : 2 ≤ q) : repunitFour q ≠ 1 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  simp only [repunitFour, sum_range_succ]
  have : 0 < 4 ^ (q' + 1) := by positivity
  omega

theorem injPrime_prime (j : ℕ) : (injPrime j).Prime :=
  Nat.minFac_prime (repunitFour_ne_one (by have := five_le_injPeriod j; omega))

theorem injPrime_dvd (j : ℕ) : (injPrime j : ℤ) ∣ 4 ^ injPeriod j - 1 := by
  have h := Nat.minFac_dvd (repunitFour (injPeriod j))
  have h3 := three_mul_repunitFour (injPeriod j)
  have h1 : 1 ≤ 4 ^ injPeriod j := Nat.one_le_pow _ _ (by norm_num)
  have : injPrime j ∣ 4 ^ injPeriod j - 1 := h3 ▸ dvd_mul_of_dvd_right h 3
  have hc : ((4 ^ injPeriod j - 1 : ℕ) : ℤ) = 4 ^ injPeriod j - 1 := by push_cast [h1]; ring
  rw [← hc]
  exact_mod_cast this

theorem injPrime_ne_two (j : ℕ) : injPrime j ≠ 2 := by
  intro h
  have hd := Nat.minFac_dvd (repunitFour (injPeriod j))
  rw [show (repunitFour (injPeriod j)).minFac = injPrime j from rfl, h] at hd
  have := repunitFour_mod_two (show 0 < injPeriod j by have := five_le_injPeriod j; omega)
  omega

theorem injPrime_ne_three (j : ℕ) : injPrime j ≠ 3 := by
  intro h
  have hd := Nat.minFac_dvd (repunitFour (injPeriod j))
  rw [show (repunitFour (injPeriod j)).minFac = injPrime j from rfl, h] at hd
  have hm := repunitFour_mod_three (injPeriod j)
  have hq3 : injPeriod j % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ injPeriod j := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (injPeriod_prime j)).mp h3
    have := five_le_injPeriod j
    omega
  omega

theorem injPeriod_coprime {i j : ℕ} (hij : i ≠ j) : (injPeriod i).Coprime (injPeriod j) :=
  (Nat.coprime_primes (injPeriod_prime i) (injPeriod_prime j)).mpr
    (injPeriod_strictMono.injective.ne hij)

/-- Distinct periods force distinct primes: a common prime factor would divide `4 − 1`. -/
theorem injPrime_injective : Function.Injective injPrime := by
  intro i j hij
  by_contra hne
  set p := injPrime i
  haveI : Fact p.Prime := ⟨injPrime_prime i⟩
  have hi : (4 : ZMod p) ^ injPeriod i = 1 := by
    have := injPrime_dvd i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    push_cast at this
    exact sub_eq_zero.mp this
  have hj : (4 : ZMod p) ^ injPeriod j = 1 := by
    have := injPrime_dvd j
    rw [← hij, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    push_cast at this
    exact sub_eq_zero.mp this
  have hord : orderOf (4 : ZMod p) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hi
    have h2 := orderOf_dvd_of_pow_eq_one hj
    exact Nat.eq_one_of_dvd_coprimes (injPeriod_coprime hne) h1 h2
  rw [orderOf_eq_one_iff] at hord
  have h3 : ((3 : ℤ) : ZMod p) = 0 := by
    push_cast
    linear_combination hord
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
  have h3' : p ∣ 3 := by exact_mod_cast h3
  exact injPrime_ne_three i ((Nat.prime_dvd_prime_iff_eq (injPrime_prime i) Nat.prime_three).mp h3')

/-! ### Phases of the injected terms and their means -/

/-- The phase `e(h 4^{n−e_j}/p_j)` of the `j`-th injected term, written as
`e(h 4^{n+(q_j−1)e_j}/p_j)` so that it is defined for all `n`; the two agree for `n ≥ e_j`. -/
noncomputable def injPhase (h : ℤ) (e : ℕ → ℕ) (j n : ℕ) : ℂ :=
  ephase (injPrime j) (h * 4 ^ (n + (injPeriod j - 1) * e j))

theorem norm_injPhase (h : ℤ) (e : ℕ → ℕ) (j n : ℕ) : ‖injPhase h e j n‖ = 1 := norm_ephase _ _

theorem injPhase_add_period (h : ℤ) (e : ℕ → ℕ) (j n : ℕ) :
    injPhase h e j (n + injPeriod j) = injPhase h e j n := by
  unfold injPhase
  refine ephase_congr (injPrime_prime j).ne_zero ?_
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  have : h * 4 ^ (n + injPeriod j + (injPeriod j - 1) * e j) -
      h * 4 ^ (n + (injPeriod j - 1) * e j) =
      h * 4 ^ (n + (injPeriod j - 1) * e j) * (4 ^ injPeriod j - 1) := by
    rw [show n + injPeriod j + (injPeriod j - 1) * e j =
      (n + (injPeriod j - 1) * e j) + injPeriod j by ring, pow_add]; ring
  rw [this]
  exact dvd_mul_of_dvd_right (injPrime_dvd j) _

theorem periodic_mul_of_periodic {a : ℕ} {f : ℕ → ℂ} (hf : ∀ n, f (n + a) = f n) (k n : ℕ) :
    f (n + a * k) = f n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => rw [show n + a * (k + 1) = (n + a * k) + a by ring, hf, ih]

/-- The escape bound for one injected prime: `‖Σ_{t<q_j} φ_j(t)‖ ≤ q_j − 1/72` when `p_j ∤ h`. -/
theorem norm_sum_injPhase_le {h : ℤ} (e : ℕ → ℕ) {j : ℕ} (hj : ¬ (injPrime j : ℤ) ∣ h) :
    ‖∑ t ∈ range (injPeriod j), injPhase h e j t‖ ≤ injPeriod j - 1 / 72 := by
  have hp := injPrime_prime j
  have hpZ : Prime (injPrime j : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hb : ¬ (injPrime j : ℤ) ∣ h * 4 ^ ((injPeriod j - 1) * e j) := by
    intro hd
    rcases hpZ.dvd_or_dvd hd with h1 | h4
    · exact hj h1
    · have h4' := hpZ.dvd_of_dvd_pow h4
      have h2 : (injPrime j : ℤ) ∣ 2 * 2 := by norm_num at h4' ⊢; exact h4'
      rcases hpZ.dvd_or_dvd h2 with h2' | h2' <;>
      · have : injPrime j ∣ 2 := by exact_mod_cast h2'
        exact injPrime_ne_two j ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have := norm_sum_ephase_orbit_le hp (injPrime_ne_two j) (injPrime_ne_three j)
    (show 0 < injPeriod j by have := five_le_injPeriod j; omega) (injPrime_dvd j) hb
  convert this using 3 with t
  unfold injPhase
  congr 1
  rw [pow_add]; ring

/-- The product phase of the first `J + 1` injected terms. -/
noncomputable def blockPhase (h : ℤ) (e : ℕ → ℕ) (J n : ℕ) : ℂ :=
  ∏ j ∈ range (J + 1), injPhase h e j n

/-- The common period `q_0 ⋯ q_J`. -/
noncomputable def blockPeriod (J : ℕ) : ℕ := ∏ j ∈ range (J + 1), injPeriod j

theorem blockPeriod_pos (J : ℕ) : 0 < blockPeriod J :=
  prod_pos fun j _ => (injPeriod_prime j).pos

theorem norm_blockPhase (h : ℤ) (e : ℕ → ℕ) (J n : ℕ) : ‖blockPhase h e J n‖ = 1 := by
  simp [blockPhase, norm_prod, norm_injPhase]

theorem blockPhase_add_period (h : ℤ) (e : ℕ → ℕ) (J n : ℕ) :
    blockPhase h e J (n + blockPeriod J) = blockPhase h e J n := by
  unfold blockPhase
  refine prod_congr rfl fun j hj => ?_
  obtain ⟨k, hk⟩ := dvd_prod_of_mem injPeriod hj
  rw [show blockPeriod J = injPeriod j * k from hk]
  exact periodic_mul_of_periodic (injPhase_add_period h e j) k n

/-- **Mean over the common period** = product of the individual means (Chinese remainder
theorem). -/
theorem sum_blockPhase (h : ℤ) (e : ℕ → ℕ) (J : ℕ) :
    ∑ t ∈ range (blockPeriod J), blockPhase h e J t =
      ∏ j ∈ range (J + 1), ∑ t ∈ range (injPeriod j), injPhase h e j t := by
  induction J with
  | zero => simp [blockPhase, blockPeriod]
  | succ J ih =>
    have hcop : (blockPeriod J).Coprime (injPeriod (J + 1)) :=
      Nat.Coprime.prod_left fun j hj => injPeriod_coprime (by
        simp only [mem_range] at hj; omega)
    have hper : blockPeriod (J + 1) = blockPeriod J * injPeriod (J + 1) := by
      simp [blockPeriod, prod_range_succ _ (J + 1)]
    have hph : ∀ n, blockPhase h e (J + 1) n = blockPhase h e J n * injPhase h e (J + 1) n := by
      intro n; simp [blockPhase, prod_range_succ _ (J + 1)]
    simp_rw [hper, hph]
    rw [sum_range_mul_coprime hcop (blockPhase_add_period h e J) (injPhase_add_period h e (J + 1)),
      ih, prod_range_succ _ (J + 1)]

/-- The normalised mean of the `j`-th injected phase. -/
noncomputable def meanFactor (h : ℤ) (e : ℕ → ℕ) (j : ℕ) : ℝ :=
  ‖∑ t ∈ range (injPeriod j), injPhase h e j t‖ / injPeriod j

theorem meanFactor_nonneg (h : ℤ) (e : ℕ → ℕ) (j : ℕ) : 0 ≤ meanFactor h e j := by
  unfold meanFactor; positivity

theorem meanFactor_le_one (h : ℤ) (e : ℕ → ℕ) (j : ℕ) : meanFactor h e j ≤ 1 := by
  unfold meanFactor
  have hq : (0 : ℝ) < injPeriod j := by exact_mod_cast (injPeriod_prime j).pos
  rw [div_le_one hq]
  refine (norm_sum_le _ _).trans ?_
  simp [norm_injPhase]

theorem meanFactor_le {h : ℤ} (e : ℕ → ℕ) {j : ℕ} (hj : ¬ (injPrime j : ℤ) ∣ h) :
    meanFactor h e j ≤ 1 - 1 / (72 * injPeriod j) := by
  unfold meanFactor
  have hq : (0 : ℝ) < injPeriod j := by exact_mod_cast (injPeriod_prime j).pos
  rw [div_le_iff₀ hq]
  have := norm_sum_injPhase_le e hj
  have e1 : (1 - 1 / (72 * (injPeriod j : ℝ))) * injPeriod j = injPeriod j - 1 / 72 := by
    field_simp
  linarith

theorem norm_sum_blockPhase_div (h : ℤ) (e : ℕ → ℕ) (J : ℕ) :
    ‖∑ t ∈ range (blockPeriod J), blockPhase h e J t‖ / blockPeriod J =
      ∏ j ∈ range (J + 1), meanFactor h e j := by
  rw [sum_blockPhase, norm_prod]
  unfold meanFactor blockPeriod
  push_cast
  rw [prod_div_distrib]

/-- `Σ_j 1/q_j = ∞`. -/
theorem not_summable_inv_injPeriod : ¬ Summable fun j => (1 : ℝ) / injPeriod j := by
  intro hs
  have hs' : Summable fun n => (1 : ℝ) / Nat.nth Nat.Prime n :=
    (summable_nat_add_iff 2).mp hs
  let enum : ℕ ≃ Nat.Primes := Equiv.ofBijective
    (fun n => ⟨Nat.nth Nat.Prime n, Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n⟩)
    ⟨fun a b hab => (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
        (congrArg Subtype.val hab),
      fun p => ⟨Nat.count Nat.Prime p, Subtype.ext (Nat.nth_count p.2)⟩⟩
  exact Nat.Primes.not_summable_one_div ((Equiv.summable_iff enum).mp hs')

/-- **The product of the means tends to `0`** at every nonzero frequency. -/
theorem tendsto_prod_meanFactor {h : ℤ} (hh : h ≠ 0) (e : ℕ → ℕ) :
    Tendsto (fun J => ∏ j ∈ range (J + 1), meanFactor h e j) atTop (𝓝 0) := by
  classical
  set bad : Set ℕ := {j | (injPrime j : ℤ) ∣ h}
  have hbad : bad.Finite := by
    refine (Set.finite_Iic h.natAbs).preimage (injPrime_injective.injOn) |>.subset ?_
    intro j hj
    simp only [bad, Set.mem_setOf_eq] at hj
    simp only [Set.mem_preimage, Set.mem_Iic]
    have : injPrime j ∣ h.natAbs := Int.natCast_dvd.mp hj
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hh) this
  set a : ℕ → ℝ := fun j => if (injPrime j : ℤ) ∣ h then 0 else 1 / (72 * injPeriod j)
  have ha0 : ∀ j, 0 ≤ a j := fun j => by simp only [a]; split_ifs <;> positivity
  have hle : ∀ j, meanFactor h e j ≤ Real.exp (-a j) := by
    intro j
    simp only [a]
    split_ifs with hj
    · simpa using meanFactor_le_one h e j
    · exact (meanFactor_le e hj).trans
        (by linarith [Real.add_one_le_exp (-(1 / (72 * (injPeriod j : ℝ))))])
  have hna : ¬ Summable a := by
    intro hs
    apply not_summable_inv_injPeriod
    have hc : Summable fun j =>
        if (injPrime j : ℤ) ∣ h then (1 : ℝ) / (72 * injPeriod j) else 0 := by
      refine summable_of_ne_finset_zero (s := hbad.toFinset) fun j hj => ?_
      simp only [Set.Finite.mem_toFinset, bad, Set.mem_setOf_eq] at hj
      simp [hj]
    have h72 : Summable fun j => (1 : ℝ) / (72 * injPeriod j) := by
      refine (hs.add hc).congr fun j => ?_
      simp only [a]; split_ifs <;> simp
    refine (h72.mul_left 72).congr fun j => ?_
    have : (injPeriod j : ℝ) ≠ 0 := by exact_mod_cast (injPeriod_prime j).ne_zero
    field_simp
  have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg ha0).mp hna
  have hexp : Tendsto (fun J => Real.exp (-∑ j ∈ range (J + 1), a j)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hsum.comp (tendsto_add_atTop_nat 1))
  refine squeeze_zero (fun J => prod_nonneg fun j _ => meanFactor_nonneg h e j) (fun J => ?_) hexp
  rw [← sum_neg_distrib, Real.exp_sum]
  exact prod_le_prod (fun j _ => meanFactor_nonneg h e j) fun j _ => hle j

/-! ### The number `x_e` and its orbit -/

/-- The `j`-th injected term `p_j^{−1} 4^{−e_j}`. -/
noncomputable def injTerm (e : ℕ → ℕ) (j : ℕ) : ℝ := (injPrime j : ℝ)⁻¹ * (1 / 4) ^ e j

/-- `x_e = Σ_j p_j^{−1} 4^{−e_j}`. -/
noncomputable def injNumber (e : ℕ → ℕ) : ℝ := ∑' j, injTerm e j

/-- The tail `Σ_{i>J} p_i^{−1} 4^{−e_i}`. -/
noncomputable def injTail (e : ℕ → ℕ) (J : ℕ) : ℝ := ∑' i, injTerm e (i + (J + 1))

theorem injTerm_nonneg (e : ℕ → ℕ) (j : ℕ) : 0 ≤ injTerm e j := by unfold injTerm; positivity

theorem injTerm_le (e : ℕ → ℕ) (j : ℕ) : injTerm e j ≤ (1 / 4) ^ e j := by
  unfold injTerm
  have hp : (1 : ℝ) ≤ injPrime j := by exact_mod_cast (injPrime_prime j).one_lt.le
  have : (injPrime j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  have h0 : (0 : ℝ) ≤ (1 / 4) ^ e j := by positivity
  nlinarith

theorem le_add_of_strictMono {e : ℕ → ℕ} (he : StrictMono e) (a i : ℕ) : e a + i ≤ e (i + a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := he (show i + a < i + 1 + a by omega)
    omega

theorem summable_injTerm {e : ℕ → ℕ} (he : StrictMono e) : Summable (injTerm e) := by
  refine Summable.of_nonneg_of_le (injTerm_nonneg e) (fun j => (injTerm_le e j).trans
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (he.id_le j))) ?_
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem injTail_nonneg (e : ℕ → ℕ) (J : ℕ) : 0 ≤ injTail e J :=
  tsum_nonneg fun _ => injTerm_nonneg e _

theorem injTail_le {e : ℕ → ℕ} (he : StrictMono e) (J : ℕ) :
    injTail e J ≤ 4 / 3 * (1 / 4) ^ e (J + 1) := by
  have hg : Summable fun i : ℕ => (1 / 4 : ℝ) ^ e (J + 1) * (1 / 4) ^ i :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ i, injTerm e (i + (J + 1)) ≤ (1 / 4 : ℝ) ^ e (J + 1) * (1 / 4) ^ i := by
    intro i
    refine (injTerm_le e _).trans ?_
    rw [← pow_add]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_add_of_strictMono he _ _)
  calc injTail e J ≤ ∑' i, (1 / 4 : ℝ) ^ e (J + 1) * (1 / 4) ^ i :=
        Summable.tsum_le_tsum hle ((summable_nat_add_iff (J + 1)).mpr (summable_injTerm he)) hg
    _ = 4 / 3 * (1 / 4) ^ e (J + 1) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num; ring

theorem injNumber_eq {e : ℕ → ℕ} (he : StrictMono e) (J : ℕ) :
    injNumber e = ∑ j ∈ range (J + 1), injTerm e j + injTail e J :=
  ((summable_injTerm he).sum_add_tsum_nat_add (J + 1)).symm

theorem four_pow_mul_injTerm (e : ℕ → ℕ) {j n : ℕ} (hn : e j ≤ n) :
    (4 : ℝ) ^ n * injTerm e j = ((4 ^ (n - e j) : ℕ) : ℝ) / injPrime j := by
  unfold injTerm
  have h4 : (4 : ℝ) ^ n = 4 ^ (n - e j) * 4 ^ e j := by rw [← pow_add, Nat.sub_add_cancel hn]
  rw [h4]
  push_cast
  have : (4 : ℝ) ^ e j * (1 / 4) ^ e j = 1 := by rw [← mul_pow]; norm_num
  rw [div_eq_mul_inv]
  linear_combination (4 : ℝ) ^ (n - e j) * (injPrime j : ℝ)⁻¹ * this

theorem exp_eq_ephase (p : ℕ) (h m : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * h * (((m : ℝ) / p : ℝ) : ℂ)) = ephase p (h * m) := by
  unfold ephase
  congr 1
  push_cast
  ring

theorem ephase_eq_injPhase (h : ℤ) (e : ℕ → ℕ) {j n : ℕ} (hn : e j ≤ n) :
    ephase (injPrime j) (h * ((4 ^ (n - e j) : ℕ) : ℤ)) = injPhase h e j n := by
  unfold injPhase
  refine ephase_congr (injPrime_prime j).ne_zero ?_
  rw [Int.modEq_iff_dvd]
  have hq : 1 ≤ injPeriod j := (injPeriod_prime j).one_lt.le
  have hexp : n + (injPeriod j - 1) * e j = (n - e j) + injPeriod j * e j := by
    have : (injPeriod j - 1) * e j + e j = injPeriod j * e j := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]
    omega
  have : h * (4 : ℤ) ^ (n + (injPeriod j - 1) * e j) - h * ((4 ^ (n - e j) : ℕ) : ℤ) =
      h * 4 ^ (n - e j) * ((4 ^ injPeriod j) ^ e j - 1 ^ e j) := by
    rw [hexp, pow_add, ← pow_mul]; push_cast; ring
  rw [this]
  exact dvd_mul_of_dvd_right ((injPrime_dvd j).trans (sub_dvd_pow_sub_pow _ _ _)) _

/-- The Weyl phase `e(h 4ⁿ x_e)`. -/
noncomputable def weylPhase (h : ℤ) (e : ℕ → ℕ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * h * (((4 : ℝ) ^ n * injNumber e : ℝ) : ℂ))

/-- On the block `n ≥ e_J`, `e(h4ⁿx_e)` is the product phase times the tail phase. -/
theorem weylPhase_eq {e : ℕ → ℕ} (he : StrictMono e) (h : ℤ) {J n : ℕ} (hn : e J ≤ n) :
    weylPhase h e n = blockPhase h e J n *
      Complex.exp (((2 * Real.pi * h * ((4 : ℝ) ^ n * injTail e J) : ℝ) : ℂ) * Complex.I) := by
  unfold weylPhase blockPhase
  rw [injNumber_eq he J, mul_add, Finset.mul_sum]
  have hterm : ∀ j ∈ range (J + 1), (4 : ℝ) ^ n * injTerm e j =
      (((4 ^ (n - e j) : ℕ) : ℤ) : ℝ) / injPrime j := by
    intro j hj
    have hj' : e j ≤ n := (he.monotone (by simp only [mem_range] at hj; omega)).trans hn
    rw [four_pow_mul_injTerm e hj']; push_cast; ring
  rw [sum_congr rfl hterm, Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_sum,
    mul_sum, Complex.exp_sum]
  congr 1
  · refine prod_congr rfl fun j hj => ?_
    have hj' : e j ≤ n := (he.monotone (by simp only [mem_range] at hj; omega)).trans hn
    rw [exp_eq_ephase, ephase_eq_injPhase h e hj']
  · congr 1; push_cast; ring

theorem norm_weylPhase_sub_le {e : ℕ → ℕ} (he : StrictMono e) (h : ℤ) {J n : ℕ} (hn : e J ≤ n) :
    ‖weylPhase h e n - blockPhase h e J n‖ ≤
      2 * Real.pi * |(h : ℝ)| * (4 / 3 * ((4 : ℝ) ^ n * (1 / 4) ^ e (J + 1))) := by
  rw [weylPhase_eq he h hn, ← mul_sub_one, norm_mul, norm_blockPhase, one_mul]
  refine (StonehamPairDrift.norm_exp_mul_I_sub_one_le _).trans ?_
  have ht := injTail_le he J
  have ht0 := injTail_nonneg e J
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ n * injTail e J)]
  have h4 : (0 : ℝ) ≤ 4 ^ n := by positivity
  have := mul_le_mul_of_nonneg_left ht h4
  have hc : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
  calc 2 * Real.pi * |(h : ℝ)| * ((4 : ℝ) ^ n * injTail e J)
      ≤ 2 * Real.pi * |(h : ℝ)| * ((4 : ℝ) ^ n * (4 / 3 * (1 / 4) ^ e (J + 1))) :=
        mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring

/-! ### Weyl sums -/

/-- The Weyl sum `Σ_{n<N} e(h 4ⁿ x_e)`. -/
noncomputable def weylSum (h : ℤ) (e : ℕ → ℕ) (N : ℕ) : ℂ := ∑ n ∈ range N, weylPhase h e n

theorem sum_four_pow_mul_le {a ℓ b : ℕ} (hab : a + ℓ ≤ b) :
    ∑ n ∈ range ℓ, (4 : ℝ) ^ (a + n) * (1 / 4) ^ b ≤ 1 / 3 := by
  have hgeom : ∑ n ∈ range ℓ, (4 : ℝ) ^ (a + n) = 4 ^ a * ((4 ^ ℓ - 1) / 3) := by
    simp_rw [pow_add]
    rw [← mul_sum, geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
    norm_num
  rw [← sum_mul, hgeom]
  have h1 : (4 : ℝ) ^ a * 4 ^ ℓ ≤ 4 ^ b := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hab
  have h2 : (4 : ℝ) ^ b * (1 / 4) ^ b = 1 := by rw [← mul_pow]; norm_num
  have h3 : (0 : ℝ) ≤ (1 / 4) ^ b := by positivity
  have h4 : (0 : ℝ) ≤ 4 ^ a := by positivity
  nlinarith

/-- **One block.**  For `e_J ≤ N ≤ e_{J+1}`,
`‖S(N) − S(e_J)‖ ≤ (N − e_J) Π_{j≤J} μ_j + q_0⋯q_J + 3|h|`. -/
theorem norm_weylSum_sub_le {e : ℕ → ℕ} (he : StrictMono e) (h : ℤ) {J N : ℕ} (h1 : e J ≤ N)
    (h2 : N ≤ e (J + 1)) :
    ‖weylSum h e N - weylSum h e (e J)‖ ≤
      ((N - e J : ℕ) : ℝ) * ∏ j ∈ range (J + 1), meanFactor h e j + blockPeriod J +
        3 * |(h : ℝ)| := by
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, N = e J + ℓ := ⟨N - e J, by omega⟩
  rw [weylSum, weylSum, sum_range_add, add_sub_cancel_left, Nat.add_sub_cancel_left]
  have hB := norm_sum_block_le (blockPeriod_pos J) (blockPhase_add_period h e J)
    (fun n => (norm_blockPhase h e J n).le) (e J) ℓ
  rw [norm_sum_blockPhase_div] at hB
  have herr : ∑ n ∈ range ℓ, ‖weylPhase h e (e J + n) - blockPhase h e J (e J + n)‖ ≤
      3 * |(h : ℝ)| := by
    calc ∑ n ∈ range ℓ, ‖weylPhase h e (e J + n) - blockPhase h e J (e J + n)‖
        ≤ ∑ n ∈ range ℓ, 2 * Real.pi * |(h : ℝ)| *
            (4 / 3 * ((4 : ℝ) ^ (e J + n) * (1 / 4) ^ e (J + 1))) :=
          sum_le_sum fun n _ => norm_weylPhase_sub_le he h (by omega)
      _ = 2 * Real.pi * |(h : ℝ)| * (4 / 3) *
            ∑ n ∈ range ℓ, (4 : ℝ) ^ (e J + n) * (1 / 4) ^ e (J + 1) := by
          rw [mul_sum]; refine sum_congr rfl fun n _ => by ring
      _ ≤ 2 * Real.pi * |(h : ℝ)| * (4 / 3) * (1 / 3) := by
          gcongr; exact sum_four_pow_mul_le h2
      _ ≤ 3 * |(h : ℝ)| := by
          have := Real.pi_lt_d2
          have : 0 ≤ |(h : ℝ)| := abs_nonneg _
          nlinarith
  have hsplit : ∑ n ∈ range ℓ, weylPhase h e (e J + n) =
      ∑ n ∈ range ℓ, blockPhase h e J (e J + n) +
        ∑ n ∈ range ℓ, (weylPhase h e (e J + n) - blockPhase h e J (e J + n)) := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add hB ((norm_sum_le _ _).trans herr)).trans ?_
  linarith

theorem norm_weylSum_le_card (h : ℤ) (e : ℕ → ℕ) (N : ℕ) : ‖weylSum h e N‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n ∈ range N, ‖weylPhase h e n‖ ≤ 1 := fun n _ => by
    unfold weylPhase
    rw [show 2 * Real.pi * Complex.I * h * (((4 : ℝ) ^ n * injNumber e : ℝ) : ℂ) =
      ((2 * Real.pi * h * ((4 : ℝ) ^ n * injNumber e) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  simpa using sum_le_sum this

/-- **Two blocks.**  For `e_{J+1} ≤ N ≤ e_{J+2}`,
`‖S(N)‖ ≤ N (Π_{j≤J} μ_j + (1 + 6|h|)/(J+1))`, given the growth condition on `e`. -/
theorem norm_weylSum_le {e : ℕ → ℕ} (he : StrictMono e)
    (hgrow : ∀ J, (J + 1) * (e J + 2 * blockPeriod (J + 1)) ≤ e (J + 1)) (h : ℤ) {J N : ℕ}
    (h1 : e (J + 1) ≤ N) (h2 : N ≤ e (J + 2)) :
    ‖weylSum h e N‖ ≤
      N * (∏ j ∈ range (J + 1), meanFactor h e j + (1 + 6 * |(h : ℝ)|) / (J + 1)) := by
  set P := ∏ j ∈ range (J + 1), meanFactor h e j
  have hP0 : 0 ≤ P := prod_nonneg fun j _ => meanFactor_nonneg h e j
  have hP1 : ∏ j ∈ range (J + 1 + 1), meanFactor h e j ≤ P := by
    rw [prod_range_succ]
    exact mul_le_of_le_one_right hP0 (meanFactor_le_one h e _)
  have hA := norm_weylSum_sub_le he h h1 h2
  have hB := norm_weylSum_sub_le he h (he.monotone (show J ≤ J + 1 by omega)) le_rfl
  have hC := norm_weylSum_le_card h e (e J)
  have hL : (blockPeriod J : ℝ) ≤ blockPeriod (J + 1) := by
    have : blockPeriod (J + 1) = blockPeriod J * injPeriod (J + 1) := by
      simp [blockPeriod, prod_range_succ _ (J + 1)]
    rw [this]; push_cast
    have : (1 : ℝ) ≤ injPeriod (J + 1) := by exact_mod_cast (injPeriod_prime _).one_lt.le
    have : (0 : ℝ) ≤ blockPeriod J := by positivity
    nlinarith
  have hg := hgrow J
  have hJN : J + 1 ≤ N := (he.id_le (J + 1)).trans h1
  have heJ : e J ≤ e (J + 1) := he.monotone (by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hJ1 : (0 : ℝ) < J + 1 := by positivity
  have hgR : ((J : ℝ) + 1) * (e J + 2 * blockPeriod (J + 1)) ≤ N := by
    have : (((J + 1) * (e J + 2 * blockPeriod (J + 1)) : ℕ) : ℝ) ≤ N := by
      exact_mod_cast hg.trans h1
    push_cast at this; linarith
  have hhN : 6 * |(h : ℝ)| * (J + 1) ≤ 6 * |(h : ℝ)| * N := by
    have : ((J : ℝ) + 1) ≤ N := by exact_mod_cast hJN
    have := abs_nonneg (h : ℝ)
    nlinarith
  have hsub1 : ((N - e (J + 1) : ℕ) : ℝ) = N - e (J + 1) := by push_cast [h1]; ring
  have hsub2 : ((e (J + 1) - e J : ℕ) : ℝ) = e (J + 1) - e J := by push_cast [heJ]; ring
  rw [hsub1] at hA
  rw [hsub2] at hB
  have htri : ‖weylSum h e N‖ ≤ ‖weylSum h e N - weylSum h e (e (J + 1))‖ +
      ‖weylSum h e (e (J + 1)) - weylSum h e (e J)‖ + ‖weylSum h e (e J)‖ := by
    have hdec : weylSum h e N = (weylSum h e N - weylSum h e (e (J + 1))) +
        (weylSum h e (e (J + 1)) - weylSum h e (e J)) + weylSum h e (e J) := by ring
    calc ‖weylSum h e N‖ = ‖(weylSum h e N - weylSum h e (e (J + 1))) +
        (weylSum h e (e (J + 1)) - weylSum h e (e J)) + weylSum h e (e J)‖ := by
          rw [← hdec]
      _ ≤ _ := norm_add₃_le
  have hN1 : (e (J + 1) : ℝ) ≤ N := by exact_mod_cast h1
  have heJ' : (e J : ℝ) ≤ e (J + 1) := by exact_mod_cast heJ
  have hmain : ‖weylSum h e N‖ ≤ N * P + (e J + 2 * blockPeriod (J + 1)) + 6 * |(h : ℝ)| := by
    have hPP : ((N : ℝ) - e (J + 1)) * ∏ j ∈ range (J + 1 + 1), meanFactor h e j ≤
        ((N : ℝ) - e (J + 1)) * P := mul_le_mul_of_nonneg_left hP1 (by linarith)
    have hPN : ((N : ℝ) - e (J + 1)) * P + ((e (J + 1) : ℝ) - e J) * P ≤ N * P := by
      have : (0 : ℝ) ≤ e J := by positivity
      nlinarith
    linarith
  have hfin : (e J + 2 * blockPeriod (J + 1) : ℝ) + 6 * |(h : ℝ)| ≤
      N * ((1 + 6 * |(h : ℝ)|) / (J + 1)) := by
    rw [mul_div_assoc', le_div_iff₀ hJ1]
    nlinarith
  calc ‖weylSum h e N‖ ≤ N * P + ((e J + 2 * blockPeriod (J + 1) : ℝ) + 6 * |(h : ℝ)|) := by
        linarith
    _ ≤ N * P + N * ((1 + 6 * |(h : ℝ)|) / (J + 1)) := by linarith
    _ = N * (P + (1 + 6 * |(h : ℝ)|) / (J + 1)) := by ring

/-- **Weyl sums of `x_e` are `o(N)`** at every nonzero frequency. -/
theorem tendsto_weylSum_injNumber {e : ℕ → ℕ} (he : StrictMono e)
    (hgrow : ∀ J, (J + 1) * (e J + 2 * blockPeriod (J + 1)) ≤ e (J + 1)) {h : ℤ} (hh : h ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * h * (((4 : ℝ) ^ n * injNumber e : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun J : ℕ => ∏ j ∈ range (J + 1), meanFactor h e j +
      (1 + 6 * |(h : ℝ)|) / ((J : ℝ) + 1)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun J : ℕ => (1 + 6 * |(h : ℝ)|) / ((J : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 + 6 * |(h : ℝ)|)
      rw [mul_zero] at this
      refine this.congr fun J => ?_
      rw [mul_one_div]
    have := (tendsto_prod_meanFactor hh e).add h2
    rwa [add_zero] at this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J₀, hJ₀⟩ := Metric.tendsto_atTop.mp hu ε hε
  refine ⟨e (J₀ + 1), fun N hN => ?_⟩
  have hex : ∃ J, N < e (J + 2) := ⟨N, lt_of_lt_of_le (show N < N + 2 by omega) (he.id_le (N + 2))⟩
  set J := Nat.find hex with hJdef
  have hJ2 : N < e (J + 2) := Nat.find_spec hex
  have hJ1 : e (J + 1) ≤ N := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · rw [h0]; exact (he.monotone (by omega)).trans hN
    · have := Nat.find_min hex (show J - 1 < J by omega)
      rw [show J - 1 + 2 = J + 1 by omega] at this
      omega
  have hJJ : J₀ ≤ J := by
    by_contra hlt
    have : e (J + 2) ≤ e (J₀ + 1) := he.monotone (by omega)
    omega
  have hbound := norm_weylSum_le he hgrow h hJ1 hJ2.le
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (Nat.zero_lt_succ _) ((he.id_le (J + 1)).trans hJ1)
    exact_mod_cast this
  have hu' := hJ₀ J hJJ
  rw [Real.dist_eq, sub_zero] at hu'
  rw [dist_zero_right, norm_mul, norm_inv, Complex.norm_natCast]
  have hw : ‖∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * h *
      (((4 : ℝ) ^ n * injNumber e : ℝ) : ℂ))‖ = ‖weylSum h e N‖ := rfl
  rw [hw]
  calc (N : ℝ)⁻¹ * ‖weylSum h e N‖ ≤ (N : ℝ)⁻¹ * (N * (∏ j ∈ range (J + 1), meanFactor h e j +
        (1 + 6 * |(h : ℝ)|) / (J + 1))) := by gcongr
    _ = ∏ j ∈ range (J + 1), meanFactor h e j + (1 + 6 * |(h : ℝ)|) / (J + 1) := by
        field_simp
    _ ≤ |∏ j ∈ range (J + 1), meanFactor h e j + (1 + 6 * |(h : ℝ)|) / (J + 1)| := le_abs_self _
    _ < ε := hu'

/-- **The parity drift of `x_e` is `o(N)`.** -/
theorem not_parityDriftHypothesis_injNumber {e : ℕ → ℕ} (he : StrictMono e)
    (hgrow : ∀ J, (J + 1) * (e J + 2 * blockPeriod (J + 1)) ≤ e (J + 1)) :
    ¬ ParityDriftHypothesis (injNumber e) :=
  not_parityDriftHypothesis_of_weylSums fun _ hk => tendsto_weylSum_injNumber he hgrow hk

/-- An admissible exponent sequence: `e_0 = 0`, `e_{J+1} = (J+1)(e_J + 2 q_0⋯q_{J+1}) + 1`. -/
noncomputable def injExp : ℕ → ℕ
  | 0 => 0
  | J + 1 => (J + 1) * (injExp J + 2 * blockPeriod (J + 1)) + 1

theorem injExp_strictMono : StrictMono injExp := by
  refine strictMono_nat_of_lt_succ fun J => ?_
  show injExp J < (J + 1) * (injExp J + 2 * blockPeriod (J + 1)) + 1
  have : injExp J ≤ (J + 1) * (injExp J + 2 * blockPeriod (J + 1)) :=
    (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  omega

theorem injExp_grow (J : ℕ) : (J + 1) * (injExp J + 2 * blockPeriod (J + 1)) ≤ injExp (J + 1) :=
  Nat.le_succ _

/-- **Unconditional instance.**  `Σ_j p_j^{−1} 4^{−e_j}` with the exponents `injExp` — infinitely
many distinct prime denominators, each at the first power — has parity drift `o(N)`. -/
theorem not_parityDriftHypothesis_injNumber_injExp : ¬ ParityDriftHypothesis (injNumber injExp) :=
  not_parityDriftHypothesis_injNumber injExp_strictMono injExp_grow

end GaloisForLFunctions.HTGeometry.FirstPowerInjection
