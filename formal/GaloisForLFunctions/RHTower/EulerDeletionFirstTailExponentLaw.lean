import GaloisForLFunctions.RHTower.EulerDeletionFirstTailMertens
import GaloisForLFunctions.RHTower.MobiusMertensMeanSquareExponentLaw

/-!
# Exponent law for the first EDQ tail

The first complementary EDQ block is the fixed-start Mertens-window energy

`I(N) = Σ_{N < n ≤ 2N} (M(n) - M(N))² / (n(n+1))`.

For `a ≥ 0` off the boundary `a = 2Θ - 1` (`Θ = sup Re ρ`),

`I(N) = O(N^a)`  ⟺  `2Θ < 1 + a`

(`exists_incrementEnergy_le_rpow_iff`).  In particular a subpower bound `I(N) = O(N^ε)` for every
`ε > 0` is exactly RH: the first tail is a receiver and carries no information beyond `Θ`.

* `⇐`: Littlewood's Mertens bound.
* `⇒`: an anchor chain `N_{k+1} ∈ (3N_k/2, 2N_k]` chosen so that the anchor increments are at most
  the block average, `(M(N_{k+1}) - M(N_k))² ≤ 12 C N_k^{a+1}`.  Then `|M(N_k)| ≪ N_k^{(a+1)/2}`,
  every block `(N_k, 2N_k]` has Mertens mean square `≪ N_k^{a+2}`, and the blocks cover the line.
  This gives `Σ_{k ≤ X} M(k)² ≪ X^{a+2}`, and the mean-square exponent law
  (`zetaZeroAbscissa_le_of_sum_sq_shiftedMertens_le`) gives `Θ ≤ (1+a)/2`.
-/

set_option autoImplicit false
open Filter Finset
open scoped BigOperators

noncomputable section

namespace RHTower.DeletionFirstTail

/-- The Mertens function of the EDQ carrier is the shifted Mertens sum. -/
theorem mertensM_eq_shiftedMertensReal (n : ℕ) : Sieve.mertensM n = shiftedMertensReal n := by
  rw [shiftedMertensReal_eq, Sieve.mertensM, Finset.sum_range_succ',
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- The block increments are bounded by the first-tail energy. -/
theorem sum_sq_mertens_increment_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Ioc N (2 * N), (Sieve.mertensM n - Sieve.mertensM N) ^ 2 ≤
      6 * (N : ℝ) ^ 2 * incrementEnergy N := by
  unfold incrementEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hn0 : (0 : ℝ) < n := by
    have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast (by omega : 0 < n)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 0 < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  have hnn : (n : ℝ) * ((n : ℝ) + 1) ≤ 6 * (N : ℝ) ^ 2 := by nlinarith
  rw [mul_div_assoc', le_div_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hnn (sq_nonneg (Sieve.mertensM n - Sieve.mertensM N))]

/-- **Anchor step.**  Some `N' ∈ (3N/2, 2N]` has `(M(N') - M(N))² ≤ 12 C N^{a+1}`. -/
theorem exists_anchor {C a : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hE : incrementEnergy N ≤ C * (N : ℝ) ^ a) :
    ∃ N' : ℕ, 3 * N / 2 < N' ∧ N' ≤ 2 * N ∧
      (Sieve.mertensM N' - Sieve.mertensM N) ^ 2 ≤ 12 * C * (N : ℝ) ^ (a + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set s : Finset ℕ := Ioc (3 * N / 2) (2 * N) with hs
  have hne : s.Nonempty := ⟨2 * N, by simp [hs]; omega⟩
  have hsub : s ⊆ Ioc N (2 * N) := by
    intro n hn; simp only [hs, Finset.mem_Ioc] at hn ⊢; omega
  have hcard : (N : ℝ) ≤ 2 * (s.card : ℝ) := by
    rw [hs, Nat.card_Ioc]
    have : N ≤ 2 * (2 * N - 3 * N / 2) := by omega
    exact_mod_cast this
  have hEnn : 0 ≤ incrementEnergy N := Finset.sum_nonneg fun n _ => by positivity
  have hC : 0 ≤ C * (N : ℝ) ^ a := hEnn.trans hE
  have hsum : ∑ n ∈ s, (Sieve.mertensM n - Sieve.mertensM N) ^ 2 ≤
      ∑ _n ∈ s, 12 * C * (N : ℝ) ^ (a + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ n ∈ s, (Sieve.mertensM n - Sieve.mertensM N) ^ 2
        ≤ ∑ n ∈ Ioc N (2 * N), (Sieve.mertensM n - Sieve.mertensM N) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
      _ ≤ 6 * (N : ℝ) ^ 2 * incrementEnergy N := sum_sq_mertens_increment_le hN
      _ ≤ 6 * (N : ℝ) ^ 2 * (C * (N : ℝ) ^ a) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 3 * (N : ℝ) * (2 * (C * (N : ℝ) ^ a * N)) := by ring
      _ ≤ 3 * (2 * (s.card : ℝ)) * (2 * (C * (N : ℝ) ^ a * N)) := by
          have h0 : 0 ≤ 2 * (C * (N : ℝ) ^ a * N) := by
            have := mul_nonneg hC hN0.le; linarith
          exact mul_le_mul_of_nonneg_right (by linarith) h0
      _ = (s.card : ℝ) * (12 * C * (N : ℝ) ^ (a + 1)) := by
          rw [Real.rpow_add_one hN0.ne']; ring
  obtain ⟨N', hN', hle⟩ := Finset.exists_le_of_sum_le hne hsum
  simp only [hs, Finset.mem_Ioc] at hN'
  exact ⟨N', hN'.1, hN'.2, hle⟩

/-- **First-tail growth bounds the Mertens mean square.**  If `I(N) ≤ C N^a` for all `N ≥ 1`
(`a ≥ 0`), then `Σ_{k ≤ X} M(k)² ≤ C' (X+1)^{a+2}`. -/
theorem exists_sum_sq_mertens_le_of_incrementEnergy_le {C a : ℝ} (ha : 0 ≤ a)
    (hE : ∀ N : ℕ, 1 ≤ N → incrementEnergy N ≤ C * (N : ℝ) ^ a) :
    ∃ C' : ℝ, ∀ X : ℕ,
      ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2 ≤ C' * ((X : ℝ) + 1) ^ (a + 2) := by
  have hC : 0 ≤ C := by
    have h1 := hE 1 le_rfl
    have h0 : 0 ≤ incrementEnergy 1 := Finset.sum_nonneg fun n _ => by positivity
    simpa using h0.trans h1
  have hanchor : ∀ N : ℕ, ∃ N' : ℕ, 1 ≤ N → 3 * N / 2 < N' ∧ N' ≤ 2 * N ∧
      (Sieve.mertensM N' - Sieve.mertensM N) ^ 2 ≤ 12 * C * (N : ℝ) ^ (a + 1) := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨N', h⟩ := exists_anchor hN (hE N hN)
      exact ⟨N', fun _ => h⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose g hg using hanchor
  set A : ℕ → ℕ := fun k => g^[k] 1 with hA
  have hAsucc : ∀ k, A (k + 1) = g (A k) := fun k => by
    simp only [hA]; rw [Function.iterate_succ_apply']
  have hApos : ∀ k, 1 ≤ A k := by
    intro k; induction k with
    | zero => simp [hA]
    | succ k ih => rw [hAsucc]; have := (hg (A k) ih).1; omega
  have hstep : ∀ k, 3 * A k / 2 < A (k + 1) ∧ A (k + 1) ≤ 2 * A k ∧
      (Sieve.mertensM (A (k + 1)) - Sieve.mertensM (A k)) ^ 2 ≤
        12 * C * (A k : ℝ) ^ (a + 1) := fun k => by
    rw [hAsucc]; exact hg (A k) (hApos k)
  have hgrow : ∀ k, (3 / 2 : ℝ) * A k ≤ A (k + 1) := by
    intro k
    have h := (hstep k).1
    have : 3 * A k ≤ 2 * A (k + 1) := by omega
    have : (3 * A k : ℝ) ≤ 2 * A (k + 1) := by exact_mod_cast this
    linarith
  -- Mertens values at the anchors
  set e : ℝ := (a + 1) / 2 with he
  have he0 : 0 < e := by rw [he]; linarith
  set D : ℝ := Real.sqrt (12 * C) with hD
  have hq : 1 < (3 / 2 : ℝ) ^ e := Real.one_lt_rpow (by norm_num) he0
  set K : ℝ := max 1 (D / ((3 / 2 : ℝ) ^ e - 1)) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKD : D ≤ K * ((3 / 2 : ℝ) ^ e - 1) := by
    have := le_max_right 1 (D / ((3 / 2 : ℝ) ^ e - 1))
    rw [← hK] at this
    rwa [div_le_iff₀ (by linarith)] at this
  have hMA : ∀ k, |Sieve.mertensM (A k)| ≤ K * (A k : ℝ) ^ e := by
    intro k
    induction k with
    | zero =>
        simp only [hA, Function.iterate_zero, id_eq, Nat.cast_one, Real.one_rpow, mul_one]
        have : Sieve.mertensM 1 = 1 := by
          rw [mertensM_eq_shiftedMertensReal, shiftedMertensReal_eq]; simp
        rw [this, abs_one]; exact hK1
    | succ k ih =>
        have hAk : (0 : ℝ) < A k := by exact_mod_cast hApos k
        have hdiff : |Sieve.mertensM (A (k + 1)) - Sieve.mertensM (A k)| ≤ D * (A k : ℝ) ^ e := by
          have h2 := (hstep k).2.2
          rw [← Real.sqrt_sq_eq_abs]
          calc Real.sqrt ((Sieve.mertensM (A (k + 1)) - Sieve.mertensM (A k)) ^ 2)
              ≤ Real.sqrt (12 * C * (A k : ℝ) ^ (a + 1)) := Real.sqrt_le_sqrt h2
            _ = D * (A k : ℝ) ^ e := by
                rw [Real.sqrt_mul (by positivity), hD]
                congr 1
                rw [show a + 1 = e * 2 by rw [he]; ring, Real.rpow_mul hAk.le,
                  show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
                  Real.sqrt_sq (Real.rpow_nonneg hAk.le _)]
        have hpow : (3 / 2 : ℝ) ^ e * (A k : ℝ) ^ e ≤ (A (k + 1) : ℝ) ^ e := by
          rw [← Real.mul_rpow (by norm_num) hAk.le]
          exact Real.rpow_le_rpow (by positivity) (hgrow k) he0.le
        calc |Sieve.mertensM (A (k + 1))|
            ≤ |Sieve.mertensM (A k)| + |Sieve.mertensM (A (k + 1)) - Sieve.mertensM (A k)| := by
              have := abs_add_le (Sieve.mertensM (A k))
                (Sieve.mertensM (A (k + 1)) - Sieve.mertensM (A k))
              rwa [add_sub_cancel] at this
          _ ≤ K * (A k : ℝ) ^ e + D * (A k : ℝ) ^ e := add_le_add ih hdiff
          _ ≤ K * ((3 / 2 : ℝ) ^ e * (A k : ℝ) ^ e) := by
              have := mul_le_mul_of_nonneg_right hKD (Real.rpow_nonneg hAk.le e)
              nlinarith
          _ ≤ K * (A (k + 1) : ℝ) ^ e := mul_le_mul_of_nonneg_left hpow (by linarith)
  -- block mean squares
  set L : ℝ := 12 * C + 2 * K ^ 2 with hL
  have hblock : ∀ k, ∑ n ∈ Ioc (A k) (2 * A k), Sieve.mertensM n ^ 2 ≤
      L * (A k : ℝ) ^ (a + 2) := by
    intro k
    have hAk : (0 : ℝ) < A k := by exact_mod_cast hApos k
    have hinc := sum_sq_mertens_increment_le (hApos k)
    have hEk := hE (A k) (hApos k)
    have hcard : ((Ioc (A k) (2 * A k)).card : ℝ) = A k := by
      rw [Nat.card_Ioc]; push_cast [show 2 * A k - A k = A k by omega]; ring
    calc ∑ n ∈ Ioc (A k) (2 * A k), Sieve.mertensM n ^ 2
        ≤ ∑ n ∈ Ioc (A k) (2 * A k),
            (2 * (Sieve.mertensM n - Sieve.mertensM (A k)) ^ 2 +
              2 * Sieve.mertensM (A k) ^ 2) := by
          refine Finset.sum_le_sum fun n _ => ?_
          nlinarith [sq_nonneg (Sieve.mertensM n - 2 * Sieve.mertensM (A k))]
      _ = 2 * ∑ n ∈ Ioc (A k) (2 * A k), (Sieve.mertensM n - Sieve.mertensM (A k)) ^ 2 +
            2 * (A k : ℝ) * Sieve.mertensM (A k) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard]
          ring
      _ ≤ 2 * (6 * (A k : ℝ) ^ 2 * (C * (A k : ℝ) ^ a)) +
            2 * (A k : ℝ) * (K * (A k : ℝ) ^ e) ^ 2 := by
          have h1 := hinc.trans (mul_le_mul_of_nonneg_left hEk (by positivity))
          have h2 : Sieve.mertensM (A k) ^ 2 ≤ (K * (A k : ℝ) ^ e) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hMA k) 2
          have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (A k : ℝ))
          linarith
      _ = L * (A k : ℝ) ^ (a + 2) := by
          have h1 : (A k : ℝ) ^ (a + 2) = (A k : ℝ) ^ 2 * (A k : ℝ) ^ a := by
            rw [Real.rpow_add hAk, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
          have h2 : ((A k : ℝ) ^ e) ^ 2 = (A k : ℝ) * (A k : ℝ) ^ a := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hAk.le, he]
            push_cast
            rw [show (a + 1) / 2 * 2 = a + 1 by ring, Real.rpow_add_one hAk.ne']
            ring
          rw [hL, h1, mul_pow, h2]; ring
  -- covering by the blocks
  have hcover : ∀ K' : ℕ, ∑ n ∈ range (2 * A K' + 1), Sieve.mertensM n ^ 2 ≤
      1 + ∑ k ∈ range (K' + 1), ∑ n ∈ Ioc (A k) (2 * A k), Sieve.mertensM n ^ 2 := by
    intro K'
    induction K' with
    | zero =>
        have hA0 : A 0 = 1 := by simp [hA]
        simp only [zero_add, Finset.sum_range_one]
        rw [hA0, show 2 * 1 + 1 = 3 by rfl]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
        have h0 : Sieve.mertensM 0 = 0 := by rw [mertensM_eq_shiftedMertensReal]; simp [shiftedMertensReal]
        have h1 : Sieve.mertensM 1 = 1 := by
          rw [mertensM_eq_shiftedMertensReal, shiftedMertensReal_eq]; simp
        have hI : Ioc 1 (2 * 1) = {2} := by decide
        rw [hI, Finset.sum_singleton, h0, h1]; norm_num
    | succ K' ih =>
        rw [Finset.sum_range_succ (fun k => ∑ n ∈ Ioc (A k) (2 * A k), Sieve.mertensM n ^ 2) (K' + 1)]
        have hsplit : range (2 * A (K' + 1) + 1) ⊆
            range (2 * A K' + 1) ∪ Ioc (A (K' + 1)) (2 * A (K' + 1)) := by
          intro n hn
          have h := (hstep K').2.1
          simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc] at hn ⊢
          omega
        calc ∑ n ∈ range (2 * A (K' + 1) + 1), Sieve.mertensM n ^ 2
            ≤ ∑ n ∈ range (2 * A K' + 1) ∪ Ioc (A (K' + 1)) (2 * A (K' + 1)),
                Sieve.mertensM n ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsplit fun _ _ _ => sq_nonneg _
          _ ≤ ∑ n ∈ range (2 * A K' + 1), Sieve.mertensM n ^ 2 +
                ∑ n ∈ Ioc (A (K' + 1)) (2 * A (K' + 1)), Sieve.mertensM n ^ 2 := by
              have hui : ∑ n ∈ range (2 * A K' + 1) ∪ Ioc (A (K' + 1)) (2 * A (K' + 1)),
                    Sieve.mertensM n ^ 2 +
                  ∑ n ∈ range (2 * A K' + 1) ∩ Ioc (A (K' + 1)) (2 * A (K' + 1)),
                    Sieve.mertensM n ^ 2 =
                  ∑ n ∈ range (2 * A K' + 1), Sieve.mertensM n ^ 2 +
                  ∑ n ∈ Ioc (A (K' + 1)) (2 * A (K' + 1)), Sieve.mertensM n ^ 2 :=
                Finset.sum_union_inter
              have hnn : 0 ≤ ∑ n ∈ range (2 * A K' + 1) ∩ Ioc (A (K' + 1)) (2 * A (K' + 1)),
                  Sieve.mertensM n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
              linarith
          _ ≤ _ := by linarith
  -- geometric sum of block sizes
  have hgeo : ∀ K' : ℕ, ∑ k ∈ range (K' + 1), (A k : ℝ) ^ (a + 2) ≤ 3 * (A K' : ℝ) ^ (a + 2) := by
    intro K'
    induction K' with
    | zero =>
        rw [Finset.sum_range_one]
        have := Real.rpow_nonneg (Nat.cast_nonneg (A 0) : (0 : ℝ) ≤ A 0) (a + 2)
        linarith
    | succ K' ih =>
        rw [Finset.sum_range_succ]
        have hx0 := Real.rpow_nonneg (Nat.cast_nonneg (A (K' + 1)) : (0 : ℝ) ≤ A (K' + 1)) (a + 2)
        have hAk : (0 : ℝ) < A K' := by exact_mod_cast hApos K'
        have hr : (A K' : ℝ) ≤ (2 / 3) * A (K' + 1) := by linarith [hgrow K']
        have hpow : (A K' : ℝ) ^ (a + 2) ≤ (4 / 9) * (A (K' + 1) : ℝ) ^ (a + 2) := by
          calc (A K' : ℝ) ^ (a + 2) ≤ ((2 / 3) * A (K' + 1)) ^ (a + 2) :=
                Real.rpow_le_rpow hAk.le hr (by linarith)
            _ = (2 / 3 : ℝ) ^ (a + 2) * (A (K' + 1) : ℝ) ^ (a + 2) :=
                Real.mul_rpow (by norm_num) (by positivity)
            _ ≤ (4 / 9) * (A (K' + 1) : ℝ) ^ (a + 2) := by
                apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
                calc (2 / 3 : ℝ) ^ (a + 2) ≤ (2 / 3 : ℝ) ^ (2 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
                  _ = 4 / 9 := by norm_num
        linarith
  -- conclusion
  refine ⟨1 + 3 * L, fun X => ?_⟩
  have hex : ∃ K' : ℕ, X ≤ 2 * A K' := by
    have hlin : ∀ k, k + 1 ≤ A k := by
      intro k; induction k with
      | zero => exact hApos 0
      | succ k ih => have := (hstep k).1; omega
    exact ⟨X, by have := hlin X; omega⟩
  classical
  obtain ⟨K', hXK, hmin'⟩ : ∃ K' : ℕ, X ≤ 2 * A K' ∧ ∀ j < K', ¬ X ≤ 2 * A j :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hAX : (A K' : ℝ) ≤ (X : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos K' with h0 | hpos
    · rw [h0]; simp [hA]
    · have hmin := hmin' (K' - 1) (by omega)
      push Not at hmin
      have h := (hstep (K' - 1)).2.1
      rw [show K' - 1 + 1 = K' by omega] at h
      have : A K' ≤ X := by omega
      exact_mod_cast (show A K' ≤ X + 1 by omega)
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  calc ∑ k ∈ range (X + 1), shiftedMertensReal k ^ 2
      = ∑ k ∈ range (X + 1), Sieve.mertensM k ^ 2 := by
        simp only [mertensM_eq_shiftedMertensReal]
    _ ≤ ∑ k ∈ range (2 * A K' + 1), Sieve.mertensM k ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) fun _ _ _ => sq_nonneg _
    _ ≤ 1 + ∑ k ∈ range (K' + 1), ∑ n ∈ Ioc (A k) (2 * A k), Sieve.mertensM n ^ 2 := hcover K'
    _ ≤ 1 + ∑ k ∈ range (K' + 1), L * (A k : ℝ) ^ (a + 2) := by
        gcongr with k _; exact hblock k
    _ = 1 + L * ∑ k ∈ range (K' + 1), (A k : ℝ) ^ (a + 2) := by rw [Finset.mul_sum]
    _ ≤ 1 + L * (3 * ((X : ℝ) + 1) ^ (a + 2)) := by
        gcongr
        exact (hgeo K').trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) hAX (by linarith)) (by norm_num))
    _ ≤ (1 + 3 * L) * ((X : ℝ) + 1) ^ (a + 2) := by
        have h1 : 1 ≤ ((X : ℝ) + 1) ^ (a + 2) :=
          Real.one_le_rpow (by linarith [(Nat.cast_nonneg X : (0 : ℝ) ≤ X)]) (by linarith)
        nlinarith

/-- **First-tail growth bounds the zero abscissa.** -/
theorem zetaZeroAbscissa_le_of_incrementEnergy_le {C a : ℝ} (ha : 0 ≤ a)
    (hE : ∀ N : ℕ, 1 ≤ N → incrementEnergy N ≤ C * (N : ℝ) ^ a) :
    zetaZeroAbscissa ≤ (1 + a) / 2 := by
  obtain ⟨C', hS⟩ := exists_sum_sq_mertens_le_of_incrementEnergy_le ha hE
  have h := zetaZeroAbscissa_le_of_sum_sq_shiftedMertens_le (by linarith : 1 ≤ a + 2) hS
  linarith

/-- **The zero abscissa bounds the first tail** (Littlewood). -/
theorem exists_incrementEnergy_le_of_lt {a : ℝ} (ha : 2 * zetaZeroAbscissa < 1 + a) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → incrementEnergy N ≤ C * (N : ℝ) ^ a := by
  set ε : ℝ := (1 + a - 2 * zetaZeroAbscissa) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨C₁, hC₁, hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε hε0
  set b : ℝ := zetaZeroAbscissa + ε with hb
  have hb0 : 0 ≤ b := by linarith [half_le_zetaZeroAbscissa]
  have hMb : ∀ n : ℕ, |Sieve.mertensM n| ≤ C₁ * ((n : ℝ) + 1) ^ b := fun n => by
    rw [mertensM_eq_shiftedMertensReal, ← norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal]
    exact hM n
  refine ⟨16 * C₁ ^ 2 * 3 ^ (2 * b), fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold incrementEnergy
  have hterm : ∀ n ∈ Ioc N (2 * N), (Sieve.mertensM n - Sieve.mertensM N) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ 16 * C₁ ^ 2 * 3 ^ (2 * b) * (N : ℝ) ^ (2 * b) / (N : ℝ) ^ 2 := by
    intro n hn
    have hNn : (N : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hbnd : ∀ m : ℕ, (m : ℝ) ≤ 2 * N → |Sieve.mertensM m| ≤ C₁ * (3 * (N : ℝ)) ^ b := by
      intro m hm
      exact (hMb m).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) hb0) hC₁)
    have hd : |Sieve.mertensM n - Sieve.mertensM N| ≤ 2 * (C₁ * (3 * (N : ℝ)) ^ b) := by
      have := abs_sub (Sieve.mertensM n) (Sieve.mertensM N)
      linarith [hbnd n hn2, hbnd N (by linarith)]
    have hsq : (Sieve.mertensM n - Sieve.mertensM N) ^ 2 ≤
        16 * C₁ ^ 2 * 3 ^ (2 * b) * (N : ℝ) ^ (2 * b) / 4 := by
      rw [← sq_abs]
      calc |Sieve.mertensM n - Sieve.mertensM N| ^ 2 ≤ (2 * (C₁ * (3 * (N : ℝ)) ^ b)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hd 2
        _ = 16 * C₁ ^ 2 * 3 ^ (2 * b) * (N : ℝ) ^ (2 * b) / 4 := by
            rw [Real.mul_rpow (by norm_num) hN0.le]
            have e1 : ((3 : ℝ) ^ b) ^ 2 = 3 ^ (2 * b) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
            have e2 : ((N : ℝ) ^ b) ^ 2 = (N : ℝ) ^ (2 * b) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
            rw [show (2 * (C₁ * (3 ^ b * (N : ℝ) ^ b))) ^ 2 =
              4 * C₁ ^ 2 * ((3 : ℝ) ^ b) ^ 2 * ((N : ℝ) ^ b) ^ 2 by ring, e1, e2]
            ring
    have hden : (N : ℝ) ^ 2 / 4 ≤ (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
    rw [div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (pow_pos hN0 2)]
    calc (Sieve.mertensM n - Sieve.mertensM N) ^ 2 * (N : ℝ) ^ 2
        ≤ (16 * C₁ ^ 2 * 3 ^ (2 * b) * (N : ℝ) ^ (2 * b) / 4) * (4 * ((n : ℝ) * ((n : ℝ) + 1))) :=
          mul_le_mul hsq (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  calc ∑ n ∈ Ioc N (2 * N), (Sieve.mertensM n - Sieve.mertensM N) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))
      ≤ ∑ _n ∈ Ioc N (2 * N), 16 * C₁ ^ 2 * 3 ^ (2 * b) * (N : ℝ) ^ (2 * b) / (N : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = 16 * C₁ ^ 2 * 3 ^ (2 * b) * ((N : ℝ) ^ (2 * b) / N) := by
        rw [Finset.sum_const, Nat.card_Ioc, show 2 * N - N = N by omega, nsmul_eq_mul]
        field_simp
    _ ≤ 16 * C₁ ^ 2 * 3 ^ (2 * b) * (N : ℝ) ^ a := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_sub_one hN0.ne']
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by rw [hb, hε]; linarith)

/-- **Exponent law for the first EDQ tail.**  For `a ≥ 0` off the boundary `a = 2Θ - 1`, the
fixed-start Mertens-window energy satisfies `I(N) = O(N^a)` exactly when `2Θ < 1 + a`. -/
theorem exists_incrementEnergy_le_rpow_iff {a : ℝ} (ha : 0 ≤ a)
    (hne : 1 + a ≠ 2 * zetaZeroAbscissa) :
    (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → incrementEnergy N ≤ C * (N : ℝ) ^ a) ↔
      2 * zetaZeroAbscissa < 1 + a := by
  constructor
  · rintro ⟨C, hE⟩
    have h := zetaZeroAbscissa_le_of_incrementEnergy_le ha hE
    exact lt_of_le_of_ne (by linarith) (fun h' => hne h'.symm)
  · exact exists_incrementEnergy_le_of_lt

end RHTower.DeletionFirstTail
