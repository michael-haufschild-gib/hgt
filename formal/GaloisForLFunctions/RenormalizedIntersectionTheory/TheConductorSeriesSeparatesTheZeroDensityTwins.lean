import GaloisForLFunctions.RenormalizedIntersectionTheory.TheResidueClassTwinsAreSeparated
import GaloisForLFunctions.ArithmeticCountingPositivity.EveryPrimePatternInheritsFiniteCutoffUpperBounds

/-!
# The conductor series separates the zero-density twins

For a set of primes `P` the twin `ω_P` carries conductor weights `w_P(m) = (μ * ω_P)(m)²/φ(m)` at the
Ramanujan energies `E_m = γ + log m + Σ_{p ∣ m} log p/(p − 1)`. A hyperplane gap above `s` bounds every
finite packet `Σ_{m ∈ S} w_P(m)/(E_m − γ − s)` by `1/s`, at any Euler density
(`ArithmeticCountingPositivity.primeSet_partial_secular_le_of_gap`). So:

* **Packet criterion** (`hodgeSeparates_primeSetFlip_of_packet`): a packet above `1/s` for some
  `0 < s < 2 log 2` separates the twin from `ζ`. At positive Euler density this is exact:
  separation is a positive value of the secular function (`hodgeSeparates_primeSetFlip_iff_secular_pos`).
* **Divergence at lower density `1/4`** (`exists_packet_gt_of_lowerLogDensity`): if
  `Σ_{p ∈ P, p ≤ n} log p/p ≥ (1/4) log n − C`, the squarefree packets are unbounded. On the
  conductors `∏_{p ∈ T} p` the weight is `∏ 4/(p − 1)` and the energy `Σ p log p/(p − 1)`; the bound
  `1/e ≥ Σ_j 2^{−j−1} e^{−2^{−j} e}` turns the packet into Euler products
  `∏_{p ∈ P, p ≤ X}(1 + (4/(p − 1)) e^{−σ p log p/(p − 1)}) ≥ e^{−K} σ^{−1}`, by Abel summation of the
  density hypothesis; the dyadic sum of `σ · σ^{−1}` diverges.
* **Separation** (`hodgeSeparates_primeSetFlip_of_lowerLogDensity`): every twin whose flipped primes
  have lower logarithmic density at least `1/4` is separated; in particular every residue-class twin
  with `φ(q) ≤ 4` (`hodgeSeparates_residueClassFlip_of_totient_le_four`), e.g. the primes
  `≡ 1 (mod 5)`.
-/

open Finset Filter
open GaloisForLFunctions.ArithmeticCountingPositivity (primeSetFlip primeSetCutoff primeSetMobius
  primeSetSpectralWeight primeSet_partial_secular_le_of_gap primeSetMobius_eq_finiteCutoff
  finiteFlipMobius_isMultiplicative finiteFlipMobius_prime_pow primeSetSecular
  primeSetHarmonicDensity primeSetFlip_hasHyperplaneGap_iff_secular)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (ramanujanAdjunctionEnergy)
open GaloisForLFunctions.ArithmeticIntersectionTheory (tameDifferent)

local notation "γ" => Real.eulerMascheroniConstant

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- **A conductor packet above `1/s` separates a prime-set twin**, at any Euler density. -/
theorem hodgeSeparates_primeSetFlip_of_packet (P : Set ℕ) {s : ℝ} (hs : 0 < s)
    (hs2 : s < 2 * Real.log 2) (S : Finset ℕ) (hS : ∀ m ∈ S, 2 ≤ m)
    (h : 1 / s < ∑ m ∈ S, primeSetSpectralWeight P m / (ramanujanAdjunctionEnergy m - γ - s)) :
    HodgeSeparates (primeSetFlip P) := by
  rw [hodgeSeparates_iff_not_hasHyperplaneGap (primeSetFlip_mul_self P)]
  intro hgap
  exact (not_le.mpr h) (primeSet_partial_secular_le_of_gap P hgap hs hs2 S hS)

/-- **At positive Euler density the secular sign is the exact separation criterion.** -/
theorem hodgeSeparates_primeSetFlip_iff_secular_pos (P : Set ℕ)
    (hc : 0 < primeSetHarmonicDensity P) :
    HodgeSeparates (primeSetFlip P) ↔
      ∃ s : ℝ, 0 < s ∧ s < 2 * Real.log 2 ∧ 0 < primeSetSecular P s := by
  rw [hodgeSeparates_iff_not_hasHyperplaneGap (primeSetFlip_mul_self P),
    primeSetFlip_hasHyperplaneGap_iff_secular P hc]
  constructor
  · intro h
    by_contra hne
    exact h ⟨le_rfl, fun s hs hs2 => not_lt.mp fun hpos => hne ⟨s, hs, hs2, hpos⟩⟩
  · rintro ⟨s, hs, hs2, hpos⟩ ⟨-, h⟩
    exact (not_le.mpr hpos) (h s hs hs2)

section SquarefreeConductors

/-- `φ(∏_{p ∈ T} p) = ∏_{p ∈ T} (p − 1)` for a finite set of primes. -/
theorem totient_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    (((∏ p ∈ T, p).totient : ℕ) : ℝ) = ∏ p ∈ T, ((p : ℝ) - 1) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
    have hTa : ∀ p ∈ T, p.Prime := fun p hp => hT p (mem_insert_of_mem hp)
    have hap : a.Prime := hT a (mem_insert_self a T)
    have hcop : a.Coprime (∏ p ∈ T, p) := Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hap (hTa p hp)).mpr fun h => ha (h ▸ hp)
    rw [prod_insert ha, prod_insert ha, Nat.totient_mul hcop, Nat.cast_mul, ih hTa,
      Nat.totient_prime hap, Nat.cast_sub hap.one_lt.le, Nat.cast_one]

/-- On a squarefree conductor of flipped primes the Möbius transform is `(−2)^{ω(m)}`. -/
theorem primeSetMobius_prod_primes (P : Set ℕ) {T : Finset ℕ}
    (hT : ∀ p ∈ T, p.Prime ∧ p ∈ P) : primeSetMobius P (∏ p ∈ T, p) = ∏ _p ∈ T, (-2 : ℝ) := by
  classical
  have hpos : 0 < ∏ p ∈ T, p := prod_pos fun p hp => (hT p hp).1.pos
  rw [primeSetMobius_eq_finiteCutoff P (le_refl (∏ p ∈ T, p)),
    (finiteFlipMobius_isMultiplicative _).map_prod_of_prime T fun p hp => (hT p hp).1]
  refine prod_congr rfl fun p hp => ?_
  have hmem : p ∈ primeSetCutoff P (∏ p ∈ T, p) := by
    simp only [primeSetCutoff, mem_filter, Nat.mem_primesLE]
    exact ⟨⟨Nat.le_of_dvd hpos (dvd_prod_of_mem _ hp), (hT p hp).1⟩, (hT p hp).2⟩
  have h := finiteFlipMobius_prime_pow (primeSetCutoff P (∏ p ∈ T, p)) (hT p hp).1 0
  simp only [zero_add, pow_one] at h
  rw [h, if_pos hmem]
  norm_num

/-- The conductor weight of `∏_{p ∈ T} p` is `∏_{p ∈ T} 4/(p − 1)`. -/
theorem primeSetSpectralWeight_prod_primes (P : Set ℕ) {T : Finset ℕ}
    (hT : ∀ p ∈ T, p.Prime ∧ p ∈ P) :
    primeSetSpectralWeight P (∏ p ∈ T, p) = ∏ p ∈ T, 4 / ((p : ℝ) - 1) := by
  rw [primeSetSpectralWeight, primeSetMobius_prod_primes P hT,
    totient_prod_primes fun p hp => (hT p hp).1, ← prod_pow, prod_div_distrib]
  norm_num

/-- The conductor energy of `∏_{p ∈ T} p` is `Σ_{p ∈ T} (log p + log p/(p − 1))`. -/
theorem ramanujanAdjunctionEnergy_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    ramanujanAdjunctionEnergy (∏ p ∈ T, p) - γ =
      ∑ p ∈ T, (Real.log p + Real.log p / ((p : ℝ) - 1)) := by
  rw [ramanujanAdjunctionEnergy, Nat.cast_prod,
    Real.log_prod fun p hp => (Nat.cast_pos.mpr (hT p hp).pos).ne', tameDifferent,
    Nat.primeFactors_prod hT, sum_add_distrib]
  ring

end SquarefreeConductors

section Laplace

/-- `1/e ≥ Σ_{j < J} 2^{−j−1} e^{−2^{−j} e}`: a lower Riemann sum of `∫₀¹ e^{−σe} dσ`. -/
theorem sum_dyadic_exp_le_inv {e : ℝ} (he : 0 < e) (J : ℕ) :
    ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-((1 / 2 : ℝ) ^ j * e)) ≤ 1 / e := by
  have hterm : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) * Real.exp (-((1 / 2 : ℝ) ^ j * e)) ≤
      (Real.exp (-((1 / 2 : ℝ) ^ (j + 1) * e)) - Real.exp (-((1 / 2 : ℝ) ^ j * e))) / e := by
    intro j
    set a := (1 / 2 : ℝ) ^ (j + 1)
    have hb : (1 / 2 : ℝ) ^ j = 2 * a := by simp only [a, pow_succ]; ring
    rw [hb, le_div_iff₀ he]
    have h1 := Real.add_one_le_exp (a * e)
    have h2 : Real.exp (-(a * e)) = Real.exp (-(2 * a * e)) * Real.exp (a * e) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-(2 * a * e))).le
    linarith
  calc _ ≤ ∑ j ∈ range J, (Real.exp (-((1 / 2 : ℝ) ^ (j + 1) * e)) -
        Real.exp (-((1 / 2 : ℝ) ^ j * e))) / e := sum_le_sum fun j _ => hterm j
    _ = (Real.exp (-((1 / 2 : ℝ) ^ J * e)) - Real.exp (-((1 / 2 : ℝ) ^ 0 * e))) / e := by
        rw [← sum_div, sum_range_sub (fun j => Real.exp (-((1 / 2 : ℝ) ^ j * e)))]
    _ ≤ 1 / e := by
        refine div_le_div_of_nonneg_right ?_ he.le
        have h1 : Real.exp (-((1 / 2 : ℝ) ^ J * e)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by have : 0 ≤ (1 / 2 : ℝ) ^ J * e := by positivity
                                      linarith)
        linarith [Real.exp_pos (-((1 / 2 : ℝ) ^ 0 * e))]

/-- **Laplace transform of a squarefree packet.** -/
theorem sum_dyadic_euler_le_packet (F : Finset ℕ) (a b : ℕ → ℝ) (ha : ∀ p ∈ F, 0 ≤ a p)
    (hb : ∀ p ∈ F, 0 < b p) (J : ℕ) :
    ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) *
        (∏ p ∈ F, (1 + a p * Real.exp (-((1 / 2 : ℝ) ^ j * b p))) - 1) ≤
      ∑ T ∈ F.powerset.erase ∅, (∏ p ∈ T, a p) / (∑ p ∈ T, b p) := by
  have hT : ∀ T ∈ F.powerset.erase ∅, ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) *
      ((∏ p ∈ T, a p) * Real.exp (-((1 / 2 : ℝ) ^ j * ∑ p ∈ T, b p))) ≤
        (∏ p ∈ T, a p) / (∑ p ∈ T, b p) := by
    intro T hT
    obtain ⟨hne, hsub⟩ := mem_erase.mp hT
    have hsub' := mem_powerset.mp hsub
    have hpos : 0 < ∑ p ∈ T, b p :=
      sum_pos (fun p hp => hb p (hsub' hp)) (nonempty_iff_ne_empty.mpr hne)
    have hA : 0 ≤ ∏ p ∈ T, a p := prod_nonneg fun p hp => ha p (hsub' hp)
    calc _ = (∏ p ∈ T, a p) * ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) *
          Real.exp (-((1 / 2 : ℝ) ^ j * ∑ p ∈ T, b p)) := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      _ ≤ (∏ p ∈ T, a p) * (1 / ∑ p ∈ T, b p) :=
          mul_le_mul_of_nonneg_left (sum_dyadic_exp_le_inv hpos J) hA
      _ = _ := by rw [mul_one_div]
  refine le_trans (le_of_eq ?_) (sum_le_sum hT)
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum]
  congr 1
  have hfac : ∀ T : Finset ℕ, (∏ p ∈ T, a p) * Real.exp (-((1 / 2 : ℝ) ^ j * ∑ p ∈ T, b p)) =
      ∏ p ∈ T, (a p * Real.exp (-((1 / 2 : ℝ) ^ j * b p))) := by
    intro T
    rw [prod_mul_distrib, mul_sum, ← sum_neg_distrib, Real.exp_sum]
  simp_rw [hfac]
  rw [prod_one_add, ← sum_erase_add _ _ (empty_mem_powerset F), prod_empty]
  ring

/-- `e^{x − x²} ≤ 1 + x` for `x ≥ 0`. -/
theorem exp_sub_sq_le_one_add {x : ℝ} (hx : 0 ≤ x) : Real.exp (x - x ^ 2) ≤ 1 + x := by
  have h1 : 0 < 1 + x := by linarith
  rw [← Real.exp_log h1]
  apply Real.exp_le_exp.mpr
  have h := Real.one_sub_inv_le_log_of_pos h1
  have h2 : x - x ^ 2 ≤ 1 - (1 + x)⁻¹ := by
    rw [show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring, le_div_iff₀ h1]
    nlinarith [pow_nonneg hx 3]
  linarith

theorem exp_sub_le_prod_one_add (F : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ p ∈ F, 0 ≤ x p) :
    Real.exp (∑ p ∈ F, x p - ∑ p ∈ F, x p ^ 2) ≤ ∏ p ∈ F, (1 + x p) := by
  rw [← sum_sub_distrib, Real.exp_sum]
  exact prod_le_prod (fun p _ => (Real.exp_pos _).le) fun p hp => exp_sub_sq_le_one_add (hx p hp)

end Laplace

section Abel

/-- Abel summation from `2`: `Σ_{k=2}^X a_k g_k = A(X) g(X) + Σ_{2 ≤ k < X} A(k)(g_k − g_{k+1})`. -/
theorem sum_Icc_two_mul_eq_abel (a g : ℕ → ℝ) (ha1 : a 1 = 0) {X : ℕ} (hX : 2 ≤ X) :
    ∑ k ∈ Icc 2 X, a k * g k = (∑ i ∈ Icc 1 X, a i) * g X +
      ∑ k ∈ Ico 2 X, (∑ i ∈ Icc 1 k, a i) * (g k - g (k + 1)) := by
  induction X, hX using Nat.le_induction with
  | base =>
    have h12 : Icc 1 2 = {1, 2} := by ext x; simp only [mem_Icc, mem_insert, mem_singleton]; omega
    rw [Icc_self, sum_singleton, Ico_self, sum_empty, add_zero, h12,
      sum_pair (by norm_num), ha1, zero_add]
  | succ X hX ih =>
    rw [sum_Icc_succ_top (show 2 ≤ X + 1 by omega), ih,
      sum_Icc_succ_top (show 1 ≤ X + 1 by omega), sum_Ico_succ_top hX]
    ring

theorem sum_Ico_sub_eq {f : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, (f (k + 1) - f k) = f n - f m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [sum_Ico_succ_top hn, ih]; ring

/-- `(v − u)/v ≥ log(v/u) − (v − u)²/(uv)` for `0 < u ≤ v`. -/
theorem sub_div_ge_log_sub {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    Real.log v - Real.log u - (v - u) ^ 2 / (u * v) ≤ (v - u) / v := by
  have hv : 0 < v := hu.trans_le huv
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at h
  have e : v / u - 1 = (v - u) / v + (v - u) ^ 2 / (u * v) := by field_simp; ring
  linarith

/-- **Reciprocal sums from a lower logarithmic density.** If
`Σ_{p ∈ P, p ≤ n} log p/p ≥ (1/4) log n − C`, then `Σ_{p ∈ P, p ≤ X} 1/p ≥ (1/4) log log X − K`. -/
theorem exists_sum_inv_primeSetCutoff_ge (P : Set ℕ) {C : ℝ}
    (hP : ∀ n : ℕ, 1 ≤ n → (1 / 4) * Real.log n - C ≤ primeSetLogMass P n) :
    ∃ K : ℝ, ∀ X : ℕ, 2 ≤ X →
      (1 / 4) * Real.log (Real.log X) - K ≤ ∑ p ∈ primeSetCutoff P X, (1 : ℝ) / p := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨(1 / 4) * (1 / Real.log 2 ^ 2 + Real.log (Real.log 2)) + C / Real.log 2,
    fun X hX => ?_⟩
  set a : ℕ → ℝ := fun k => if k.Prime ∧ k ∈ P then Real.log k / k else 0
  set g : ℕ → ℝ := fun k => 1 / Real.log k
  have ha1 : a 1 = 0 := by simp [a, Nat.not_prime_one]
  have hA : ∀ n, ∑ i ∈ Icc 1 n, a i = primeSetLogMass P n := fun n => by
    rw [primeSetLogMass, primeSetCutoff_eq_filter, filter_filter, sum_filter]
  have hlogk : ∀ k : ℕ, 2 ≤ k → Real.log 2 ≤ Real.log k := fun k hk =>
    Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  -- the reciprocal sum is the Abel sum of `a` against `1/log`
  have hrecip : ∑ p ∈ primeSetCutoff P X, (1 : ℝ) / p = ∑ k ∈ Icc 2 X, a k * g k := by
    have h1 : ∑ k ∈ Icc 2 X, a k * g k = ∑ k ∈ Icc 1 X, a k * g k := by
      rw [show Icc 1 X = insert 1 (Icc 2 X) by ext x; simp only [mem_Icc, mem_insert]; omega,
        sum_insert (by simp), ha1, zero_mul, zero_add]
    rw [h1, primeSetCutoff_eq_filter, filter_filter, sum_filter]
    refine sum_congr rfl fun k hk => ?_
    simp only [a, g]
    split_ifs with h
    · have hk2 : (0 : ℝ) < Real.log k := Real.log_pos (by exact_mod_cast h.1.one_lt)
      field_simp
    · simp only [zero_mul]
  rw [hrecip, sum_Icc_two_mul_eq_abel a g ha1 hX]
  have hg : ∀ k : ℕ, 2 ≤ k → g (k + 1) ≤ g k := fun k hk => by
    simp only [g]
    exact one_div_le_one_div_of_le (hl2.trans_le (hlogk k hk))
      (Real.log_le_log (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                           linarith) (by push_cast; linarith))
  have hgX : 0 ≤ g X := one_div_nonneg.mpr (hl2.le.trans (hlogk X hX))
  -- lower bound through the density hypothesis
  have hlow : ((1 / 4) * Real.log X - C) * g X +
      ∑ k ∈ Ico 2 X, ((1 / 4) * Real.log k - C) * (g k - g (k + 1)) ≤
        (∑ i ∈ Icc 1 X, a i) * g X + ∑ k ∈ Ico 2 X, (∑ i ∈ Icc 1 k, a i) * (g k - g (k + 1)) := by
    refine add_le_add (mul_le_mul_of_nonneg_right (by rw [hA]; exact hP X (by omega)) hgX)
      (sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (hg k ?_)))
    · rw [hA]; exact hP k (by have := (mem_Ico.mp hk).1; omega)
    · exact (mem_Ico.mp hk).1
  refine le_trans ?_ hlow
  -- evaluate the lower bound
  have htel : ∑ k ∈ Ico 2 X, (g k - g (k + 1)) = g 2 - g X := by
    have := sum_Ico_sub_eq (f := fun k => -g k) hX
    simp only [sub_neg_eq_add, neg_add_eq_sub] at this
    exact this
  have hgXlog : Real.log X * g X = 1 := by
    simp only [g]; field_simp [(hl2.trans_le (hlogk X hX)).ne']
  have hstep : ∀ k ∈ Ico 2 X, Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k) -
      1 / ((k : ℝ) ^ 2 * Real.log 2 ^ 2) ≤ Real.log k * (g k - g (k + 1)) := by
    intro k hk
    have hk2 := (mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hu := hl2.trans_le (hlogk k hk2)
    have huv : Real.log k ≤ Real.log (k + 1 : ℕ) :=
      Real.log_le_log hk0 (by push_cast; linarith)
    have hv := hu.trans_le huv
    have h := sub_div_ge_log_sub hu huv
    have hd : Real.log (k + 1 : ℕ) - Real.log k ≤ 1 / k := by
      rw [← Real.log_div (by positivity) hk0.ne']
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
      push_cast; field_simp; ring
    have hd0 : 0 ≤ Real.log (k + 1 : ℕ) - Real.log k := sub_nonneg.mpr huv
    have herr : (Real.log (k + 1 : ℕ) - Real.log k) ^ 2 / (Real.log k * Real.log (k + 1 : ℕ)) ≤
        1 / ((k : ℝ) ^ 2 * Real.log 2 ^ 2) := by
      have hden : Real.log 2 ^ 2 ≤ Real.log k * Real.log (k + 1 : ℕ) := by
        rw [sq]; exact mul_le_mul (hlogk k hk2) (hlogk k hk2 |>.trans huv) hl2.le hu.le
      calc _ ≤ (1 / k) ^ 2 / (Real.log 2 ^ 2) :=
            div_le_div₀ (by positivity) (pow_le_pow_left₀ hd0 hd 2) (by positivity) hden
        _ = 1 / ((k : ℝ) ^ 2 * Real.log 2 ^ 2) := by field_simp
    have heq : Real.log k * (g k - g (k + 1)) =
        (Real.log (k + 1 : ℕ) - Real.log k) / Real.log (k + 1 : ℕ) := by
      simp only [g]
      rw [mul_sub, mul_one_div_cancel hu.ne', mul_one_div, one_sub_div hv.ne']
    rw [heq]
    linarith
  have hsq : ∑ k ∈ Ico 2 X, 1 / ((k : ℝ) ^ 2 * Real.log 2 ^ 2) ≤ 1 / Real.log 2 ^ 2 := by
    have hIoo : Ico 2 X = Ioo 1 X := by ext x; simp only [mem_Ico, mem_Ioo]; omega
    rw [hIoo]
    calc _ = (∑ k ∈ Ioo 1 X, ((k : ℝ) ^ 2)⁻¹) * (1 / Real.log 2 ^ 2) := by
          rw [sum_mul]; exact sum_congr rfl fun k _ => by rw [one_div, mul_inv, one_div]
      _ ≤ 1 * (1 / Real.log 2 ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have := sum_Ioo_inv_sq_le (α := ℝ) 1 X
          norm_num at this ⊢
          exact this
      _ = _ := one_mul _
  have hloglog : ∑ k ∈ Ico 2 X, (Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k)) =
      Real.log (Real.log X) - Real.log (Real.log 2) := by
    have := sum_Ico_sub_eq (f := fun k : ℕ => Real.log (Real.log k)) hX
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using this
  have hmain : Real.log (Real.log X) - Real.log (Real.log 2) - 1 / Real.log 2 ^ 2 ≤
      ∑ k ∈ Ico 2 X, Real.log k * (g k - g (k + 1)) := by
    have := sum_le_sum hstep
    rw [sum_sub_distrib, hloglog] at this
    linarith
  have hsplit : ∑ k ∈ Ico 2 X, ((1 / 4) * Real.log k - C) * (g k - g (k + 1)) =
      (1 / 4) * ∑ k ∈ Ico 2 X, Real.log k * (g k - g (k + 1)) -
        C * ∑ k ∈ Ico 2 X, (g k - g (k + 1)) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => by ring
  have hg2 : g 2 = 1 / Real.log 2 := by simp [g]
  rw [hsplit, htel, hg2]
  have hX1 : ((1 / 4) * Real.log X - C) * g X = (1 / 4) * (Real.log X * g X) - C * g X := by ring
  rw [hX1, hgXlog]
  have e1 : C * (1 / Real.log 2 - g X) = C / Real.log 2 - C * g X := by ring
  linarith [hmain, e1]

end Abel

section Divergence

/-- The weight `4/(p − 1)` of a flipped prime. -/
def flipPrimeWeight (p : ℕ) : ℝ := 4 / ((p : ℝ) - 1)

/-- The energy `log p + log p/(p − 1)` of a flipped prime. -/
def flipPrimeEnergy (p : ℕ) : ℝ := Real.log p + Real.log p / ((p : ℝ) - 1)

theorem mem_primeSetCutoff {P : Set ℕ} {X p : ℕ} :
    p ∈ primeSetCutoff P X ↔ (p ≤ X ∧ p.Prime) ∧ p ∈ P := by
  classical
  simp only [primeSetCutoff, mem_filter, Nat.mem_primesLE]

theorem flipPrimeWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ flipPrimeWeight p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold flipPrimeWeight; exact div_nonneg (by norm_num) (by linarith)

theorem flipPrimeWeight_le {p : ℕ} (hp : p.Prime) : flipPrimeWeight p ≤ 8 / p := by
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold flipPrimeWeight
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

theorem log_two_lt_flipPrimeEnergy {p : ℕ} (hp : p.Prime) : Real.log 2 < flipPrimeEnergy p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) h2
  have hpos : 0 < Real.log p / ((p : ℝ) - 1) :=
    div_pos (Real.log_pos (by linarith)) (by linarith)
  unfold flipPrimeEnergy; linarith

theorem flipPrimeEnergy_le {p : ℕ} (hp : p.Prime) : flipPrimeEnergy p ≤ 2 * Real.log p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have : Real.log p / ((p : ℝ) - 1) ≤ Real.log p := div_le_self hl (by linarith)
  unfold flipPrimeEnergy; linarith

/-- The Laplace factor of a flipped prime is at least `4/p − 8σ log p/p`. -/
theorem sub_le_flipPrimeFactor {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ) :
    4 / p - 8 * σ * (Real.log p / p) ≤
      flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hE := flipPrimeEnergy_le hp
  have hexp : 1 - 2 * σ * Real.log p ≤ Real.exp (-(σ * flipPrimeEnergy p)) := by
    have := Real.add_one_le_exp (-(σ * flipPrimeEnergy p))
    nlinarith [mul_le_mul_of_nonneg_left hE hσ]
  have hw : 4 / (p : ℝ) ≤ flipPrimeWeight p := by
    unfold flipPrimeWeight
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hlhs : 4 / p - 8 * σ * (Real.log p / p) = 4 / (p : ℝ) * (1 - 2 * σ * Real.log p) := by
    field_simp; ring
  rw [hlhs]
  by_cases h0 : 0 ≤ 1 - 2 * σ * Real.log p
  · calc 4 / (p : ℝ) * (1 - 2 * σ * Real.log p) ≤ flipPrimeWeight p * (1 - 2 * σ * Real.log p) :=
          mul_le_mul_of_nonneg_right hw h0
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (flipPrimeWeight_nonneg hp)
  · have : 4 / (p : ℝ) * (1 - 2 * σ * Real.log p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_lt (not_le.mp h0))
    exact this.trans (mul_nonneg (flipPrimeWeight_nonneg hp) (Real.exp_pos _).le)

/-- The squares of the Laplace factors of any set of primes up to `X` sum to at most `64`. -/
theorem sum_sq_flipPrimeFactor_le (P : Set ℕ) (X : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑ p ∈ primeSetCutoff P X, (flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p))) ^ 2 ≤
      64 := by
  have hsub : primeSetCutoff P X ⊆ Ioo 1 (X + 1) := fun p hp => by
    obtain ⟨⟨hpX, hpp⟩, -⟩ := mem_primeSetCutoff.mp hp
    exact mem_Ioo.mpr ⟨hpp.one_lt, by omega⟩
  have hterm : ∀ p ∈ primeSetCutoff P X,
      (flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p))) ^ 2 ≤ 64 * ((p : ℝ) ^ 2)⁻¹ := by
    intro p hp
    have hpp := (mem_primeSetCutoff.mp hp).1.2
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hE : 0 ≤ σ * flipPrimeEnergy p :=
      mul_nonneg hσ ((Real.log_pos one_lt_two).le.trans (log_two_lt_flipPrimeEnergy hpp).le)
    have hx0 : 0 ≤ flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p)) :=
      mul_nonneg (flipPrimeWeight_nonneg hpp) (Real.exp_pos _).le
    have hx1 : flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p)) ≤ 8 / p := by
      refine (mul_le_of_le_one_right (flipPrimeWeight_nonneg hpp)
        (Real.exp_le_one_iff.mpr (by linarith))).trans (flipPrimeWeight_le hpp)
    calc _ ≤ (8 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ hx0 hx1 2
      _ = 64 * ((p : ℝ) ^ 2)⁻¹ := by field_simp; norm_num
  calc _ ≤ ∑ p ∈ primeSetCutoff P X, 64 * ((p : ℝ) ^ 2)⁻¹ := sum_le_sum hterm
    _ = 64 * ∑ p ∈ primeSetCutoff P X, ((p : ℝ) ^ 2)⁻¹ := by rw [mul_sum]
    _ ≤ 64 * ∑ n ∈ Ioo 1 (X + 1), ((n : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
          fun _ _ _ => by positivity) (by norm_num)
    _ ≤ 64 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h := sum_Ioo_inv_sq_le (α := ℝ) 1 (X + 1)
        norm_num at h
        exact h
    _ = 64 := by norm_num

/-- **The Euler factor at scale `σ = 2^{−j}` is at least `e^{−K} 2^{j−1}`.** -/
theorem exists_flipPrime_euler_ge (P : Set ℕ) {C : ℝ}
    (hP : ∀ n : ℕ, 1 ≤ n → (1 / 4) * Real.log n - C ≤ primeSetLogMass P n) :
    ∃ K : ℝ, ∀ j : ℕ, 1 ≤ j → ∀ X : ℕ, 2 ^ 2 ^ (j - 1) ≤ X →
      (j - 1 : ℝ) * Real.log 2 - K ≤
        ∑ p ∈ primeSetCutoff P X,
            flipPrimeWeight p * Real.exp (-((1 / 2 : ℝ) ^ j * flipPrimeEnergy p)) -
          ∑ p ∈ primeSetCutoff P X,
            (flipPrimeWeight p * Real.exp (-((1 / 2 : ℝ) ^ j * flipPrimeEnergy p))) ^ 2 := by
  obtain ⟨K, hK⟩ := exists_sum_inv_primeSetCutoff_ge P hP
  set CM := (Real.log 4 + 4) + (8 + RHTower.Mertens.mertensTail)
  have hCM : 0 ≤ CM := (abs_nonneg _).trans (RHTower.Mertens.mertens_first_prime 1 le_rfl)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨4 * K + 4 * Real.log 2 + 4 * CM + 64 - Real.log (Real.log 2), fun j hj X hX => ?_⟩
  classical
  set Y := 2 ^ 2 ^ (j - 1)
  set σ := (1 / 2 : ℝ) ^ j
  have hσ0 : 0 ≤ σ := by positivity
  have hY2 : 2 ≤ Y := by
    have : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ Y := Nat.pow_le_pow_right (by norm_num) this
  have hlogY : Real.log Y = 2 ^ (j - 1) * Real.log 2 := by
    simp only [Y]; push_cast; rw [Real.log_pow]; push_cast; ring
  have hσY : σ * Real.log Y = Real.log 2 / 2 := by
    rw [hlogY]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [σ, Nat.add_sub_cancel]
    rw [pow_succ]; field_simp
    rw [← mul_pow]; norm_num
  -- the reciprocal sum and the Mertens sum over the flipped primes up to `Y`
  have hrec := hK Y hY2
  have hmass : ∑ p ∈ primeSetCutoff P Y, Real.log p / p ≤ Real.log Y + CM := by
    have hsub : primeSetCutoff P Y ⊆ (Icc 1 Y).filter Nat.Prime := fun p hp => by
      obtain ⟨⟨hpY, hpp⟩, -⟩ := mem_primeSetCutoff.mp hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpp.one_lt.le, hpY⟩, hpp⟩
    refine (sum_le_sum_of_subset_of_nonneg hsub fun k _ _ =>
      div_nonneg (Real.log_natCast_nonneg k) (Nat.cast_nonneg k)).trans ?_
    have h := RHTower.Mertens.mertens_first_prime Y (by omega)
    rw [abs_le] at h
    linarith [h.2]
  have hloglogY : Real.log (Real.log Y) = (j - 1 : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
    rw [hlogY, Real.log_mul (by positivity) hl2.ne', Real.log_pow]
    push_cast [Nat.cast_sub hj]; ring
  have hlin : ∑ p ∈ primeSetCutoff P Y, (4 / (p : ℝ) - 8 * σ * (Real.log p / p)) ≤
      ∑ p ∈ primeSetCutoff P Y, flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p)) :=
    sum_le_sum fun p hp => sub_le_flipPrimeFactor (mem_primeSetCutoff.mp hp).1.2 hσ0
  have hsplit : ∑ p ∈ primeSetCutoff P Y, (4 / (p : ℝ) - 8 * σ * (Real.log p / p)) =
      4 * ∑ p ∈ primeSetCutoff P Y, (1 : ℝ) / p -
        8 * σ * ∑ p ∈ primeSetCutoff P Y, Real.log p / p := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun p _ => by ring
  have hYX : primeSetCutoff P Y ⊆ primeSetCutoff P X := fun p hp => by
    obtain ⟨⟨hpY, hpp⟩, hpP⟩ := mem_primeSetCutoff.mp hp
    exact mem_primeSetCutoff.mpr ⟨⟨hpY.trans hX, hpp⟩, hpP⟩
  have hmono : ∑ p ∈ primeSetCutoff P Y, flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p)) ≤
      ∑ p ∈ primeSetCutoff P X, flipPrimeWeight p * Real.exp (-(σ * flipPrimeEnergy p)) :=
    sum_le_sum_of_subset_of_nonneg hYX fun p hp _ =>
      mul_nonneg (flipPrimeWeight_nonneg (mem_primeSetCutoff.mp hp).1.2) (Real.exp_pos _).le
  have hsq := sum_sq_flipPrimeFactor_le P X hσ0
  have hσ1 : σ ≤ 1 / 2 := by
    simp only [σ]
    calc (1 / 2 : ℝ) ^ j ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
      _ = 1 / 2 := pow_one _
  have hσCM : σ * CM ≤ CM / 2 := by nlinarith
  rw [hsplit] at hlin
  have hmass' : σ * ∑ p ∈ primeSetCutoff P Y, Real.log p / p ≤ Real.log 2 / 2 + CM / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hmass hσ0]
  nlinarith [hrec, hloglogY, hmass', hlin, hmono, hsq]

theorem sum_range_half_pow_succ (J : ℕ) : ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) = 1 - (1 / 2) ^ J := by
  induction J with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Lower logarithmic density `1/4` makes the squarefree conductor packets unbounded.** -/
theorem exists_packet_gt_of_lowerLogDensity (P : Set ℕ) {C : ℝ}
    (hP : ∀ n : ℕ, 1 ≤ n → (1 / 4) * Real.log n - C ≤ primeSetLogMass P n) (B : ℝ) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 2 ≤ m) ∧
      B < ∑ m ∈ S, primeSetSpectralWeight P m / (ramanujanAdjunctionEnergy m - γ - Real.log 2) := by
  classical
  obtain ⟨K, hK⟩ := exists_flipPrime_euler_ge P hP
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c := Real.exp (-K) / 4 with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, B + 1 < (J - 1 : ℝ) * c := by
    obtain ⟨J, hJ⟩ := exists_nat_gt ((B + 1) / c + 1)
    have h1 : (B + 1) / c < (J : ℝ) - 1 := by linarith
    rw [div_lt_iff₀ hc0] at h1
    exact ⟨J, h1⟩
  set F := primeSetCutoff P (2 ^ 2 ^ J)
  have hF : ∀ p ∈ F, p.Prime ∧ p ∈ P := fun p hp =>
    ⟨(mem_primeSetCutoff.mp hp).1.2, (mem_primeSetCutoff.mp hp).2⟩
  have hTF : ∀ T ∈ F.powerset.erase ∅, ∀ p ∈ T, p.Prime ∧ p ∈ P := fun T hT p hp =>
    hF p (mem_powerset.mp (mem_of_mem_erase hT) hp)
  refine ⟨(F.powerset.erase ∅).image (fun T => ∏ p ∈ T, p), ?_, ?_⟩
  · intro m hm
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hm
    obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr (mem_erase.mp hT).1
    have hpos : 0 < ∏ q ∈ T, q := prod_pos fun q hq => (hTF T hT q hq).1.pos
    exact (hTF T hT p hp).1.two_le.trans (Nat.le_of_dvd hpos (dvd_prod_of_mem _ hp))
  rw [sum_image fun T₁ h₁ T₂ h₂ h => by
    rw [← Nat.primeFactors_prod fun p hp => (hTF T₁ h₁ p hp).1,
      ← Nat.primeFactors_prod fun p hp => (hTF T₂ h₂ p hp).1]
    exact congrArg Nat.primeFactors h]
  -- compare with the Laplace packet
  have hcmp : ∀ T ∈ F.powerset.erase ∅,
      (∏ p ∈ T, flipPrimeWeight p) / (∑ p ∈ T, flipPrimeEnergy p) ≤
        primeSetSpectralWeight P (∏ p ∈ T, p) /
          (ramanujanAdjunctionEnergy (∏ p ∈ T, p) - γ - Real.log 2) := by
    intro T hT
    have hTp := hTF T hT
    simp only [flipPrimeWeight, flipPrimeEnergy]
    rw [primeSetSpectralWeight_prod_primes P hTp,
      show ramanujanAdjunctionEnergy (∏ p ∈ T, p) - γ - Real.log 2 =
        (ramanujanAdjunctionEnergy (∏ p ∈ T, p) - γ) - Real.log 2 by ring,
      ramanujanAdjunctionEnergy_prod_primes fun p hp => (hTp p hp).1]
    obtain ⟨p₀, hp₀⟩ := nonempty_iff_ne_empty.mpr (mem_erase.mp hT).1
    have hE : Real.log 2 < ∑ p ∈ T, flipPrimeEnergy p :=
      (log_two_lt_flipPrimeEnergy (hTp p₀ hp₀).1).trans_le
        (single_le_sum (fun p hp => hl2.le.trans (log_two_lt_flipPrimeEnergy (hTp p hp).1).le) hp₀)
    have hW : 0 ≤ ∏ p ∈ T, flipPrimeWeight p :=
      prod_nonneg fun p hp => flipPrimeWeight_nonneg (hTp p hp).1
    simp only [flipPrimeWeight, flipPrimeEnergy] at hE hW
    exact div_le_div_of_nonneg_left hW (by linarith) (by linarith)
  refine lt_of_lt_of_le ?_ (sum_le_sum hcmp)
  refine lt_of_lt_of_le ?_ (sum_dyadic_euler_le_packet F flipPrimeWeight flipPrimeEnergy
    (fun p hp => flipPrimeWeight_nonneg (hF p hp).1)
    (fun p hp => hl2.trans (log_two_lt_flipPrimeEnergy (hF p hp).1)) J)
  -- each dyadic scale `j ≥ 1` contributes at least `c`
  have hscale : ∀ j ∈ range J, (if 1 ≤ j then c else 0) - (1 / 2 : ℝ) ^ (j + 1) ≤
      (1 / 2 : ℝ) ^ (j + 1) *
        (∏ p ∈ F, (1 + flipPrimeWeight p * Real.exp (-((1 / 2 : ℝ) ^ j * flipPrimeEnergy p))) - 1) := by
    intro j hj
    have hx : ∀ p ∈ F, 0 ≤ flipPrimeWeight p * Real.exp (-((1 / 2 : ℝ) ^ j * flipPrimeEnergy p)) :=
      fun p hp => mul_nonneg (flipPrimeWeight_nonneg (hF p hp).1) (Real.exp_pos _).le
    have hprod := exp_sub_le_prod_one_add F _ hx
    have hhalf : 0 < (1 / 2 : ℝ) ^ (j + 1) := by positivity
    split_ifs with hj1
    · have hjJ := mem_range.mp hj
      have hXJ : 2 ^ 2 ^ (j - 1) ≤ 2 ^ 2 ^ J :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h := hK j hj1 _ hXJ
      have hexp : Real.exp ((j - 1 : ℝ) * Real.log 2 - K) = 2 ^ (j - 1) * Real.exp (-K) := by
        rw [show ((j : ℝ) - 1) * Real.log 2 - K = ((j - 1 : ℕ) : ℝ) * Real.log 2 + -K by
          push_cast [Nat.cast_sub hj1]; ring, Real.exp_add, Real.exp_nat_mul, Real.exp_log two_pos]
      have hZ : 2 ^ (j - 1) * Real.exp (-K) ≤
          ∏ p ∈ F, (1 + flipPrimeWeight p * Real.exp (-((1 / 2 : ℝ) ^ j * flipPrimeEnergy p))) := by
        rw [← hexp]; exact (Real.exp_le_exp.mpr h).trans hprod
      have hpow : (1 / 2 : ℝ) ^ (j + 1) * 2 ^ (j - 1) = 1 / 4 := by
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [show i + 1 + 1 = i + 2 by ring, pow_add, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
      have := mul_le_mul_of_nonneg_left hZ hhalf.le
      rw [← mul_assoc, hpow] at this
      simp only [c]
      nlinarith
    · have h1 : 1 ≤ ∏ p ∈ F, (1 + flipPrimeWeight p *
          Real.exp (-((1 / 2 : ℝ) ^ j * flipPrimeEnergy p))) := by
        have := prod_le_prod (s := F) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
          fun p hp => le_add_of_nonneg_right (hx p hp)
        simpa only [prod_const_one] using this
      nlinarith
  refine lt_of_lt_of_le ?_ (sum_le_sum hscale)
  rw [sum_sub_distrib]
  have hgeom : ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := by
    rw [sum_range_half_pow_succ]
    have : 0 ≤ (1 / 2 : ℝ) ^ J := by positivity
    linarith
  have hcount : (J - 1 : ℝ) * c ≤ ∑ j ∈ range J, (if 1 ≤ j then c else 0) := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    have : (range J).filter (fun j => 1 ≤ j) = Ico 1 J := by
      ext x; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [this, Nat.card_Ico]
    rcases Nat.eq_zero_or_pos J with h | h
    · subst h; simp; nlinarith
    · rw [Nat.cast_sub h]; push_cast; nlinarith
  linarith

/-- **Lower logarithmic density at least `1/4` separates the twin.** -/
theorem hodgeSeparates_primeSetFlip_of_lowerLogDensity (P : Set ℕ) {C : ℝ}
    (hP : ∀ n : ℕ, 1 ≤ n → (1 / 4) * Real.log n - C ≤ primeSetLogMass P n) :
    HodgeSeparates (primeSetFlip P) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨S, hS, hB⟩ := exists_packet_gt_of_lowerLogDensity P hP (1 / Real.log 2)
  exact hodgeSeparates_primeSetFlip_of_packet P hl2 (by linarith) S hS hB

/-- **Residue-class twins with `φ(q) ≤ 4` are separated**, `φ(q) = 4` (`q = 5, 8, 10, 12`) included. -/
theorem hodgeSeparates_residueClassFlip_of_totient_le_four {q : ℕ} [NeZero q]
    (hq : q.totient ≤ 4) {r : ZMod q} (hr : IsUnit r) :
    HodgeSeparates (primeSetFlip (residueClassPrimes q r)) := by
  obtain ⟨C, hC⟩ := exists_abs_primeSetLogMass_residueClassPrimes_sub_le hr
  have hφ0 : 0 < q.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hφ : (1 / 4 : ℝ) ≤ (q.totient : ℝ)⁻¹ := by
    rw [one_div]; exact inv_anti₀ (by exact_mod_cast hφ0) (by exact_mod_cast hq)
  refine hodgeSeparates_primeSetFlip_of_lowerLogDensity _ (C := C) fun n hn => ?_
  have h := (abs_le.mp (hC n hn)).1
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_right hφ hl]

/-- **The twin flipping the primes `≡ 1 (mod 5)` is separated.** -/
theorem hodgeSeparates_primeSetFlip_one_mod_five :
    HodgeSeparates (primeSetFlip {p | p.Prime ∧ p % 5 = 1}) := by
  have hset : {p | p.Prime ∧ p % 5 = 1} = residueClassPrimes 5 1 := by
    ext p
    simp only [residueClassPrimes, Set.mem_setOf_eq]
    rw [show (1 : ZMod 5) = ((1 : ℕ) : ZMod 5) from Nat.cast_one.symm,
      ZMod.natCast_eq_natCast_iff']
  rw [hset]
  exact hodgeSeparates_residueClassFlip_of_totient_le_four (by decide) isUnit_one

end Divergence

end GaloisForLFunctions.RenormalizedIntersectionTheory
