import GaloisForLFunctions.RHTower.Sieve.VinogradovCollisionPairRemoval
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A Chebyshev reservoir for the moment recursion

The Bertrand reservoir of `vinogradov_moment_bertrand_recurrence` doubles at every prime, so its
`R ≈ k³` primes reach `2^R N^{1/k}` and the recursion constants grow like `2^{k⁴}` per step.
Chebyshev's two bounds put many primes in a single window:

* `R ≤ #{p prime : y < p ≤ 4y}` once `y ≥ 2²⁴` and `81R² ≤ y`
  (`le_card_vinogradovQuadruplePrimes`);
* any `R ≥ k(k² - k) + 1` distinct primes above `y`, `N ≤ y^k`, separate every injective
  `k`-tuple below `N` modulo one of them (`exists_separating_prime_of_family`).

Together they give the moment recursion with all reservoir primes in `(y, 4y]`,
`y = ⌈N^{1/k}⌉ + k` (`exists_vinogradov_moment_chebyshev_recurrence`), hence `p^k ≤ 16^k N`.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The primes of the window `(y, 4y]`. -/
def vinogradovQuadruplePrimes (y : ℕ) : Finset ℕ :=
  (Finset.Ioc y (4 * y)).filter Nat.Prime

theorem sum_log_vinogradovQuadruplePrimes (y : ℕ) :
    ∑ p ∈ vinogradovQuadruplePrimes y, Real.log p =
      Chebyshev.theta ((4 * y : ℕ) : ℝ) - Chebyshev.theta (y : ℝ) := by
  have hsplit : Finset.Ioc 0 (4 * y) = Finset.Ioc 0 y ∪ Finset.Ioc y (4 * y) :=
    (Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)).symm
  have hdisj : Disjoint ((Finset.Ioc 0 y).filter Nat.Prime)
      ((Finset.Ioc y (4 * y)).filter Nat.Prime) := by
    have h : Disjoint (Finset.Ioc 0 y) (Finset.Ioc y (4 * y)) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      exact absurd (Finset.mem_Ioc.mp hz').1 (not_lt.mpr (Finset.mem_Ioc.mp hz).2)
    exact h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h4 : Chebyshev.theta ((4 * y : ℕ) : ℝ) =
      ∑ p ∈ (Finset.Ioc 0 y).filter Nat.Prime, Real.log p +
        ∑ p ∈ (Finset.Ioc y (4 * y)).filter Nat.Prime, Real.log p := by
    rw [Chebyshev.theta, Nat.floor_natCast, hsplit, Finset.filter_union,
      Finset.sum_union hdisj]
  have h1 : Chebyshev.theta (y : ℝ) =
      ∑ p ∈ (Finset.Ioc 0 y).filter Nat.Prime, Real.log p := by
    rw [Chebyshev.theta, Nat.floor_natCast]
  rw [h4, h1, vinogradovQuadruplePrimes]
  ring

/-- **Chebyshev window count.** `(y, 4y]` holds at least `R` primes once `y ≥ 2²⁴` and
`81R² ≤ y`. -/
theorem le_card_vinogradovQuadruplePrimes {y R : ℕ} (hy : 2 ^ 24 ≤ y) (hR : 81 * R ^ 2 ≤ y) :
    R ≤ (vinogradovQuadruplePrimes y).card := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  set Y : ℝ := (y : ℝ) with hYdef
  have hY : (2 : ℝ) ^ 24 ≤ Y := by rw [hYdef]; exact_mod_cast hy
  have hY0 : 0 < Y := by linarith [show (0 : ℝ) < 2 ^ 24 by norm_num]
  set L : ℝ := Real.log (4 * Y) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hcard : ((vinogradovQuadruplePrimes y).card : ℝ) ≤ (R : ℝ) - 1 := by
    have : (vinogradovQuadruplePrimes y).card + 1 ≤ R := hlt
    have h' : (((vinogradovQuadruplePrimes y).card + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast this
    push_cast at h'
    linarith
  -- the window mass is at most `card · L`
  have hmass_le : Chebyshev.theta ((4 * y : ℕ) : ℝ) - Chebyshev.theta Y ≤
      ((vinogradovQuadruplePrimes y).card : ℝ) * L := by
    rw [hYdef, ← sum_log_vinogradovQuadruplePrimes]
    have : ∀ p ∈ vinogradovQuadruplePrimes y, Real.log p ≤ L := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpI := Finset.mem_Ioc.mp hp'.1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
      rw [hLdef]
      apply Real.log_le_log hp0
      have : (p : ℝ) ≤ ((4 * y : ℕ) : ℝ) := by exact_mod_cast hpI.2
      push_cast at this
      linarith
    calc ∑ p ∈ vinogradovQuadruplePrimes y, Real.log p
        ≤ ∑ _p ∈ vinogradovQuadruplePrimes y, L := Finset.sum_le_sum this
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Chebyshev's bounds
  have hlow := Chebyshev.theta_ge' (x := 4 * Y) (by linarith)
  have hup := Chebyshev.theta_le_log4_mul_x hY0.le
  have hcast : ((4 * y : ℕ) : ℝ) = 4 * Y := by rw [hYdef]; push_cast; ring
  rw [hcast] at hmass_le
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlog8 : Real.log (4 * Y + 2) ≤ L + Real.log 2 := by
    rw [hLdef, ← Real.log_mul (by linarith) (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hsqrt4 : Real.sqrt (4 * Y) = 2 * Real.sqrt Y := by
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  rw [← hLdef, hsqrt4] at hlow
  -- `(R + 4√Y) L ≥ 2(Y - 1) log 2`
  have hkey : 2 * (Y - 1) * Real.log 2 ≤ ((R : ℝ) + 4 * Real.sqrt Y) * L := by
    nlinarith
  -- `9R ≤ √Y`
  have hRs : 9 * (R : ℝ) ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    have : ((81 * R ^ 2 : ℕ) : ℝ) ≤ Y := by rw [hYdef]; exact_mod_cast hR
    push_cast at this
    nlinarith
  -- `√Y L ≤ 8 Y^{41/64}`
  have hLb : L ≤ 8 * (4 * Y) ^ ((1 : ℝ) / 8) := by
    have h := Real.log_le_rpow_div (x := 4 * Y) (ε := 1 / 8) (by linarith) (by norm_num)
    rw [hLdef]
    calc Real.log (4 * Y) ≤ (4 * Y) ^ ((1 : ℝ) / 8) / (1 / 8) := h
      _ = 8 * (4 * Y) ^ ((1 : ℝ) / 8) := by ring
  have h4Y : 4 * Y ≤ Y ^ ((9 : ℝ) / 8) := by
    have h18 : (4 : ℝ) ≤ Y ^ ((1 : ℝ) / 8) := by
      have : ((2 : ℝ) ^ 24) ^ ((1 : ℝ) / 8) ≤ Y ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow (by norm_num) hY (by norm_num)
      have e : ((2 : ℝ) ^ 24) ^ ((1 : ℝ) / 8) = 8 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith
    have e : Y ^ ((9 : ℝ) / 8) = Y ^ ((1 : ℝ) / 8) * Y := by
      rw [← Real.rpow_add_one hY0.ne']; norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_right h18 hY0.le
  have h4Yr : (4 * Y) ^ ((1 : ℝ) / 8) ≤ Y ^ ((9 : ℝ) / 64) := by
    calc (4 * Y) ^ ((1 : ℝ) / 8) ≤ (Y ^ ((9 : ℝ) / 8)) ^ ((1 : ℝ) / 8) :=
          Real.rpow_le_rpow (by linarith) h4Y (by norm_num)
      _ = Y ^ ((9 : ℝ) / 64) := by rw [← Real.rpow_mul hY0.le]; norm_num
  have hsqrtY : Real.sqrt Y = Y ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow Y
  have hsL : Real.sqrt Y * L ≤ 8 * Y ^ ((41 : ℝ) / 64) := by
    have hs0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
    calc Real.sqrt Y * L ≤ Real.sqrt Y * (8 * Y ^ ((9 : ℝ) / 64)) :=
          mul_le_mul_of_nonneg_left (hLb.trans (by linarith)) hs0
      _ = 8 * Y ^ ((41 : ℝ) / 64) := by
          rw [hsqrtY, show (8 : ℝ) * Y ^ ((41 : ℝ) / 64) =
            8 * (Y ^ ((1 : ℝ) / 2) * Y ^ ((9 : ℝ) / 64)) by
              rw [← Real.rpow_add hY0]; norm_num]
          ring
  -- `256 Y^{41/64} ≤ Y`
  have hY41 : 256 * Y ^ ((41 : ℝ) / 64) ≤ Y := by
    have h23 : (256 : ℝ) ≤ Y ^ ((23 : ℝ) / 64) := by
      have : ((2 : ℝ) ^ 24) ^ ((23 : ℝ) / 64) ≤ Y ^ ((23 : ℝ) / 64) :=
        Real.rpow_le_rpow (by norm_num) hY (by norm_num)
      have e : ((2 : ℝ) ^ 24) ^ ((23 : ℝ) / 64) = (2 : ℝ) ^ ((69 : ℝ) / 8) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num
      have h2 : (256 : ℝ) ≤ (2 : ℝ) ^ ((69 : ℝ) / 8) := by
        have : (2 : ℝ) ^ ((8 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((69 : ℝ) / 8) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        rw [Real.rpow_natCast] at this
        norm_num at this ⊢
        linarith
      linarith
    have e : Y = Y ^ ((41 : ℝ) / 64) * Y ^ ((23 : ℝ) / 64) := by
      rw [← Real.rpow_add hY0]; norm_num
    have h41 : 0 ≤ Y ^ ((41 : ℝ) / 64) := Real.rpow_nonneg hY0.le _
    calc 256 * Y ^ ((41 : ℝ) / 64) ≤ Y ^ ((23 : ℝ) / 64) * Y ^ ((41 : ℝ) / 64) :=
          mul_le_mul_of_nonneg_right h23 h41
      _ = Y := by rw [mul_comm]; exact e.symm
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hRL : ((R : ℝ) + 4 * Real.sqrt Y) * L ≤ (37 / 9) * (Real.sqrt Y * L) := by
    have : (R : ℝ) ≤ Real.sqrt Y / 9 := by linarith
    nlinarith
  nlinarith

/-- A deterministic family of `R` distinct primes in `(y, 4y]`. -/
def vinogradovQuadruplePrime (y R : ℕ) (h : R ≤ (vinogradovQuadruplePrimes y).card)
    (i : Fin R) : ℕ :=
  (vinogradovQuadruplePrimes y).orderEmbOfFin rfl (Fin.castLE h i)

theorem vinogradovQuadruplePrime_mem {y R : ℕ} (h : R ≤ (vinogradovQuadruplePrimes y).card)
    (i : Fin R) : vinogradovQuadruplePrime y R h i ∈ vinogradovQuadruplePrimes y :=
  Finset.orderEmbOfFin_mem _ _ _

theorem vinogradovQuadruplePrime_prime {y R : ℕ} (h : R ≤ (vinogradovQuadruplePrimes y).card)
    (i : Fin R) : (vinogradovQuadruplePrime y R h i).Prime :=
  (Finset.mem_filter.mp (vinogradovQuadruplePrime_mem h i)).2

theorem vinogradovQuadruplePrime_gt {y R : ℕ} (h : R ≤ (vinogradovQuadruplePrimes y).card)
    (i : Fin R) : y < vinogradovQuadruplePrime y R h i :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp (vinogradovQuadruplePrime_mem h i)).1).1

theorem vinogradovQuadruplePrime_le {y R : ℕ} (h : R ≤ (vinogradovQuadruplePrimes y).card)
    (i : Fin R) : vinogradovQuadruplePrime y R h i ≤ 4 * y :=
  (Finset.mem_Ioc.mp (Finset.mem_filter.mp (vinogradovQuadruplePrime_mem h i)).1).2

theorem vinogradovQuadruplePrime_injective {y R : ℕ}
    (h : R ≤ (vinogradovQuadruplePrimes y).card) :
    Function.Injective (vinogradovQuadruplePrime y R h) := by
  intro i j hij
  have := ((vinogradovQuadruplePrimes y).orderEmbOfFin rfl).injective hij
  exact Fin.castLE_injective h this

/-- **Separation by a prime family.** Distinct primes above `y`, at least `k(k²-k)+1` of them,
with `N ≤ y^k`: every injective `k`-tuple below `N` is injective modulo one of them. -/
theorem exists_separating_prime_of_family {N k R y : ℕ} (hy1 : 1 ≤ y) (hNy : N ≤ y ^ k)
    (hR : k * (k * k - k) + 1 ≤ R) (P : Fin R → ℕ) (hP : ∀ i, (P i).Prime)
    (hPy : ∀ i, y < P i) (hinj : Function.Injective P)
    (m : Fin k → Fin N) (hm : Function.Injective m) :
    ∃ i, Function.Injective (fun j => ((m j).val : ZMod (P i))) := by
  classical
  by_contra hnone
  have hdvd : ∀ i, P i ∣ vinogradovDifferenceProduct m := by
    intro i
    have hi : ¬Function.Injective (fun j => ((m j).val : ZMod (P i))) := fun h => hnone ⟨i, h⟩
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hi
    exact dvd_vinogradovDifferenceProduct_of_cast_eq m hne hab
  set S := Finset.univ.image P with hS
  have hprod_dvd : ∏ p ∈ S, p ∣ vinogradovDifferenceProduct m := by
    apply Finset.prod_primes_dvd
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact (hP i).prime
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hdvd i
  have hD0 := vinogradovDifferenceProduct_ne_zero hm
  have hprod_le : ∏ p ∈ S, p ≤ vinogradovDifferenceProduct m :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hprod_dvd
  have hD := vinogradovDifferenceProduct_le m
  have hScard : S.card = R := by
    rw [hS, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hlow : (y + 1) ^ R ≤ ∏ p ∈ S, p := by
    rw [← hScard]
    apply Finset.pow_card_le_prod
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact hPy i
  have hND : N ^ (k * k - k) ≤ y ^ (k * (k * k - k)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hNy _
  have hyR : y ^ (k * (k * k - k)) < (y + 1) ^ R := by
    calc y ^ (k * (k * k - k)) < (y + 1) ^ (k * (k * k - k) + 1) := by
          calc y ^ (k * (k * k - k)) ≤ (y + 1) ^ (k * (k * k - k)) :=
                Nat.pow_le_pow_left (by omega) _
            _ < (y + 1) ^ (k * (k * k - k) + 1) :=
                Nat.pow_lt_pow_right (by omega) (by omega)
      _ ≤ (y + 1) ^ R := Nat.pow_le_pow_right (by omega) hR
  exact absurd (lt_of_lt_of_le hyR (hlow.trans (hprod_le.trans (hD.trans hND)))) (lt_irrefl _)

/-- The reservoir size `k(k² - k) + 1`. -/
abbrev vinogradovChebyshevReservoirSize (k : ℕ) : ℕ := k * (k * k - k) + 1

/-- The window base `⌈N^{1/k}⌉ + k`. -/
abbrev vinogradovChebyshevBase (N k : ℕ) : ℕ := vinogradovCeilRoot k N + k

/-- **Moment recursion with a Chebyshev reservoir.** If the window base `y = ⌈N^{1/k}⌉ + k`
satisfies `y ≥ 2²⁴` and `81 R² ≤ y`, there are `R` distinct primes in `(y, 4y]` such that
`J_{k+b}(N)` is bounded by the reservoir sum and the pair-removal collision term. -/
theorem exists_vinogradov_moment_chebyshev_recurrence {N k b : ℕ} (hk : k ≠ 0) (hb : b ≠ 0)
    (hN : N ≠ 0) (hy : 2 ^ 24 ≤ vinogradovChebyshevBase N k)
    (hRy : 81 * vinogradovChebyshevReservoirSize k ^ 2 ≤ vinogradovChebyshevBase N k) :
    ∃ P : Fin (vinogradovChebyshevReservoirSize k) → ℕ,
      (∀ i, (P i).Prime ∧ vinogradovChebyshevBase N k < P i ∧
        P i ≤ 4 * vinogradovChebyshevBase N k) ∧
      Fintype.card (VinogradovDiagonalSolution N (k + b) k) ≤
        2 * (vinogradovChebyshevReservoirSize k *
            ∑ i, P i ^ (2 * b) *
              (N ^ k * (k.factorial * P i ^ (k * (k - 1) / 2) *
                Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ P i) b k))) +
          (k * k - k) ^ (2 : ℕ) * N ^ (2 : ℕ) *
            Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k)) := by
  classical
  set y := vinogradovChebyshevBase N k with hydef
  set R := vinogradovChebyshevReservoirSize k with hRdef
  have hcardR : R ≤ (vinogradovQuadruplePrimes y).card := le_card_vinogradovQuadruplePrimes hy hRy
  set P := vinogradovQuadruplePrime y R hcardR with hPdef
  have hPprime : ∀ i, (P i).Prime := vinogradovQuadruplePrime_prime hcardR
  have hPgt : ∀ i, y < P i := vinogradovQuadruplePrime_gt hcardR
  have hPle : ∀ i, P i ≤ 4 * y := vinogradovQuadruplePrime_le hcardR
  refine ⟨P, fun i => ⟨hPprime i, hPgt i, hPle i⟩, ?_⟩
  set q := vinogradovBertrandNext (max (2 * (k + b) * N ^ k) (4 * y)) with hqdef
  have hqprime : q.Prime := vinogradovBertrandNext_prime _
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  have hqlarge : 2 * (k + b) * N ^ k < q :=
    (le_max_left _ _).trans_lt (lt_vinogradovBertrandNext _)
  have hqP : ∀ i, P i < q := fun i =>
    (hPle i).trans_lt ((le_max_right _ _).trans_lt (lt_vinogradovBertrandNext _))
  have hyeq : y = vinogradovCeilRoot k N + k := hydef
  have hroot : vinogradovCeilRoot k N ≤ y := by omega
  have hNy : N ≤ y ^ k :=
    (le_vinogradovCeilRoot_pow hk).trans (Nat.pow_le_pow_left hroot k)
  -- the injective part
  have hgood : finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
      (fun z => Function.Injective z.1) ≤
      R * ∑ i, P i ^ (2 * b) * (N ^ k * (k.factorial * P i ^ (k * (k - 1) / 2) *
        Fintype.card (VinogradovDiagonalSolution (N ⌈/⌉ P i) b k))) := by
    have hcover : ∀ z : (Fin k → Fin N) × (Fin b → Fin N), Function.Injective z.1 →
        ∃ i : Fin R, Function.Injective (fun j => ((z.1 j).val : ZMod (P i))) := by
      intro z hz
      exact exists_separating_prime_of_family (by omega) hNy le_rfl P hPprime hPgt
        (vinogradovQuadruplePrime_injective hcardR) z.1 hz
    calc finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1)
        ≤ R * ∑ i : Fin R, finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
            (fun z => Function.Injective z.1 ∧
              Function.Injective (fun j => ((z.1 j).val : ZMod (P i)))) := by
          simpa only [Fintype.card_fin] using
            (finiteFiberEnergyWith_le_cover (ι := Fin R)
              (vinogradovSplitPowerSignature q N k b) (fun z => Function.Injective z.1)
              (fun i z => Function.Injective (fun j => ((z.1 j).val : ZMod (P i)))) hcover)
      _ ≤ _ := by
          gcongr with i
          haveI : NeZero (P i) := ⟨(hPprime i).ne_zero⟩
          have hkp : k < P i := by
            have : k ≤ y := by omega
            exact lt_of_le_of_lt this (hPgt i)
          have hNp : N < P i ^ k :=
            lt_of_le_of_lt hNy (Nat.pow_lt_pow_left (hPgt i) hk)
          have hunit : IsUnit ((P i : ℕ) : ZMod q) := by
            rw [ZMod.isUnit_iff_coprime]
            exact (Nat.coprime_primes (hPprime i) hqprime).2 (ne_of_lt (hqP i))
          have hM : N ⌈/⌉ P i ≠ 0 := ceilDiv_ne_zero_of_ne_zero hN (hPprime i).pos
          have hqtail : 2 * b * (N ⌈/⌉ P i) ^ k < q := by
            calc 2 * b * (N ⌈/⌉ P i) ^ k ≤ 2 * (k + b) * N ^ k :=
                  Nat.mul_le_mul (by omega)
                    (Nat.pow_le_pow_left (ceilDiv_le_self_of_pos (hPprime i).pos) k)
              _ < q := hqlarge
          exact finiteFiberEnergyWith_separated_le hb (hPprime i) hkp hNp hN hqlarge hunit hM
            hqtail
  calc Fintype.card (VinogradovDiagonalSolution N (k + b) k) =
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k : (Fin (k + b) → Fin N) → Fin k → ZMod q) := by
        symm
        exact vinogradovModularMomentAt_eq_card_of_large hN hqlarge
    _ ≤ 2 * (finiteFiberEnergyWith (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) +
        Fintype.card (VinogradovCollidingBlockCompletion q N k b)) :=
      vinogradov_moment_collision_partition
    _ ≤ _ := by
      have hbad := card_vinogradovCollidingBlockCompletion_le_pairRemoval (q := q) (N := N)
        (k := k) (b := b)
      have hJ : finiteFiberEnergy
          (vinogradovPowerSignatureMod q k : (Fin (k - 2 + b) → Fin N) → Fin k → ZMod q) =
          Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) := by
        apply vinogradovModularMomentAt_eq_card_of_large hN
        calc 2 * (k - 2 + b) * N ^ k ≤ 2 * (k + b) * N ^ k := by gcongr; omega
          _ < q := hqlarge
      rw [hJ] at hbad
      exact Nat.mul_le_mul_left 2 (Nat.add_le_add hgood hbad)

end

end RHTower.Sieve
