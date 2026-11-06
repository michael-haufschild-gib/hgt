import GaloisForLFunctions.ArithmeticCouplingTheory.TheMertensPolarization
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The jump energy detects the gcd profiles

The dilation jump energy `J_N(F) = Σ_{kn ≤ N} (Λ(k)/k)(F(kn) − F(n))²/n` separates the `M`-periodic functions:

* If `F` is a function of `gcd(·, M)`, only prime powers of primes dividing `M` move it, and
  `J_N(F) ≤ 4 V² log M (1 + log N)` (`jumpEnergy_le_of_isGcdProfile`).
* Otherwise a residue class of primes moves it by a fixed amount. Those primes have divergent `Σ log p / p`,
  so `J_N(F) / log N → ∞` (`tendsto_jumpEnergy_div_log_atTop`).

So a periodic function has `J_N(F) = O(log N)` exactly when it is a gcd profile
(`isGcdProfile_iff_jumpEnergy_isBigO_log`). A unit-normalized periodic charge `F / √log N` therefore keeps its
jump energy bounded by its conductor exactly on gcd profiles; on every other twist the energy diverges.
-/

open Finset ArithmeticFunction Filter Topology

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- `F` depends only on `gcd(·, M)`. -/
def IsGcdProfile (M : ℕ) (F : ℕ → ℝ) : Prop := ∀ n, F n = F (n.gcd M)

private theorem sum_inv_eq_harmonic (N : ℕ) :
    ∑ n ∈ Icc 1 N, 1 / (n : ℝ) = ((harmonic N : ℚ) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div]

/-- The geometric series of one prime. -/
private theorem sum_log_div_pow_le {p : ℕ} (hp : p.Prime) (A : ℕ) :
    ∑ a ∈ Icc 1 A, Real.log p / (p : ℝ) ^ a ≤ Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hgeom : ∑ a ∈ Icc 1 A, 1 / (p : ℝ) ^ a ≤ 1 - 1 / (p : ℝ) ^ A := by
    induction A with
    | zero => simp
    | succ A ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hpow : 0 < (p : ℝ) ^ A := pow_pos hp0 A
      have hstep : 2 * (1 / (p : ℝ) ^ (A + 1)) ≤ 1 / (p : ℝ) ^ A := by
        rw [pow_succ, mul_one_div, div_le_div_iff₀ (by positivity) hpow]
        nlinarith only [mul_le_mul_of_nonneg_left hp2 hpow.le]
      linarith only [ih, hstep]
  have hpos : 0 ≤ 1 / (p : ℝ) ^ A := by positivity
  calc
    ∑ a ∈ Icc 1 A, Real.log p / (p : ℝ) ^ a
        = Real.log p * ∑ a ∈ Icc 1 A, 1 / (p : ℝ) ^ a := by
          rw [mul_sum]
          exact sum_congr rfl fun a _ => by ring
    _ ≤ Real.log p * 1 := mul_le_mul_of_nonneg_left (by linarith only [hgeom, hpos]) hlog
    _ = Real.log p := mul_one _

/-- The prime powers that can move a gcd profile carry Mangoldt mass at most `log M`. -/
theorem sum_mangoldt_div_not_coprime_le {M : ℕ} (hM : 0 < M) (N : ℕ) :
    ∑ k ∈ (Icc 1 N).filter (fun k => ¬ k.Coprime M), Λ k / k ≤ Real.log M := by
  classical
  have hnn : ∀ k : ℕ, 0 ≤ Λ k / k := fun k => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  -- keep the prime powers
  have hstep1 : ∑ k ∈ (Icc 1 N).filter (fun k => ¬ k.Coprime M), Λ k / k ≤
      ∑ p ∈ M.primeFactors, ∑ a ∈ Icc 1 N, Real.log p / (p : ℝ) ^ a := by
    have hsub : ∀ k ∈ (Icc 1 N).filter (fun k => ¬ k.Coprime M), Λ k / k ≠ 0 →
        k ∈ M.primeFactors.biUnion fun p => (Icc 1 N).image fun a => p ^ a := by
      intro k hk hne
      obtain ⟨hkI, hkc⟩ := mem_filter.mp hk
      have hΛ : Λ k ≠ 0 := fun h => hne (by rw [h, zero_div])
      obtain ⟨p, a, hp, ha, rfl⟩ := (vonMangoldt_ne_zero_iff.mp hΛ)
      have hpp : p.Prime := hp.nat_prime
      have hdvd : p ∣ M := by
        by_contra hnd
        exact hkc (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hnd))
      refine mem_biUnion.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hM.ne'⟩, ?_⟩
      refine mem_image.mpr ⟨a, mem_Icc.mpr ⟨ha, ?_⟩, rfl⟩
      exact (Nat.lt_pow_self hpp.one_lt).le.trans (mem_Icc.mp hkI).2
    calc
      _ ≤ ∑ k ∈ M.primeFactors.biUnion (fun p => (Icc 1 N).image fun a => p ^ a), Λ k / k := by
        rw [← sum_filter_ne_zero]
        refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hnn k
        intro k hk
        obtain ⟨hk1, hk2⟩ := mem_filter.mp hk
        exact hsub k hk1 hk2
      _ = ∑ p ∈ M.primeFactors, ∑ k ∈ (Icc 1 N).image (fun a => p ^ a), Λ k / k := by
        refine sum_biUnion fun p hp p' hp' hne => Finset.disjoint_left.mpr fun k hk hk' => hne ?_
        obtain ⟨a, ha, rfl⟩ := mem_image.mp hk
        obtain ⟨b, -, hab⟩ := mem_image.mp hk'
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpp' := Nat.prime_of_mem_primeFactors hp'
        have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
        have hdvd : p ∣ p' ^ b := by
          rw [hab]
          exact dvd_pow_self p ha0
        exact (Nat.prime_dvd_prime_iff_eq hpp hpp').mp (hpp.dvd_of_dvd_pow hdvd)
      _ ≤ _ := by
        refine sum_le_sum fun p hp => ?_
        have hpp := Nat.prime_of_mem_primeFactors hp
        rw [sum_image fun a _ b _ h => Nat.pow_right_injective hpp.two_le h]
        refine sum_le_sum fun a ha => le_of_eq ?_
        have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
        rw [vonMangoldt_apply_pow ha0, vonMangoldt_apply_prime hpp]
        push_cast
        rfl
  refine hstep1.trans ?_
  calc
    _ ≤ ∑ p ∈ M.primeFactors, Real.log p :=
      sum_le_sum fun p hp => sum_log_div_pow_le (Nat.prime_of_mem_primeFactors hp) N
    _ = ∑ p ∈ M.primeFactors, Λ p :=
      sum_congr rfl fun p hp => (vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors hp)).symm
    _ ≤ ∑ d ∈ M.divisors, Λ d :=
      sum_le_sum_of_subset_of_nonneg
        (fun p hp => Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, hM.ne'⟩)
        fun _ _ _ => vonMangoldt_nonneg
    _ = Real.log M := vonMangoldt_sum

/-- **Gcd profiles have the jump energy of their conductor.** -/
theorem jumpEnergy_le_of_isGcdProfile {M : ℕ} (hM : 0 < M) {F : ℕ → ℝ} (hF : IsGcdProfile M F)
    {V : ℝ} (hV : ∀ n, |F n| ≤ V) (N : ℕ) :
    jumpEnergy N F ≤ 4 * V ^ 2 * Real.log M * (1 + Real.log N) := by
  classical
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0)
  have hnn : ∀ k : ℕ, 0 ≤ Λ k / k := fun k => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun k => if ¬ k.Coprime M then Λ k / k else 0 := ⟨_, rfl⟩
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    rw [hg]
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hnn k
  unfold jumpEnergy
  calc
    _ ≤ ∑ p ∈ dilationPairs N, g p.1 * (4 * V ^ 2 / p.2) := by
      refine sum_le_sum fun p _ => ?_
      by_cases hc : p.1.Coprime M
      · have heq : F (p.1 * p.2) = F p.2 := by
          rw [hF (p.1 * p.2), hc.gcd_mul_left_cancel p.2, ← hF]
        rw [heq, sub_self, hg]
        simp [hc]
      · have hgk : g p.1 = Λ p.1 / p.1 := by
          rw [hg]
          simp [hc]
        rw [hgk]
        refine mul_le_mul_of_nonneg_left ?_ (hnn p.1)
        refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have h1 := abs_le.mp (hV (p.1 * p.2))
        have h2 := abs_le.mp (hV p.2)
        nlinarith only [h1.1, h1.2, h2.1, h2.2, hV0]
    _ ≤ ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, g p.1 * (4 * V ^ 2 / p.2) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ =>
        mul_nonneg (hg0 _) (by positivity)
    _ = (∑ k ∈ Icc 1 N, g k) * ∑ n ∈ Icc 1 N, 4 * V ^ 2 / (n : ℝ) := by
      rw [sum_product, sum_mul_sum]
    _ = (∑ k ∈ (Icc 1 N).filter (fun k => ¬ k.Coprime M), Λ k / k) *
          (4 * V ^ 2 * ∑ n ∈ Icc 1 N, 1 / (n : ℝ)) := by
      rw [sum_filter, hg, mul_sum (a := 4 * V ^ 2)]
      congr 1
      exact sum_congr rfl fun n _ => by ring
    _ ≤ Real.log M * (4 * V ^ 2 * (1 + Real.log N)) := by
      refine mul_le_mul (sum_mangoldt_div_not_coprime_le hM N) ?_ ?_
        (Real.log_natCast_nonneg M)
      · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sum_inv_eq_harmonic]
        exact harmonic_le_one_add_log N
      · refine mul_nonneg (by positivity) (sum_nonneg fun n _ => by positivity)
    _ = _ := by ring

/-- A twist outside the gcd profiles is moved by a fixed amount along a class of primes of divergent
`Σ log p / p`, on a progression of harmonic mass `≈ log N / M`. -/
theorem exists_jumpEnergy_lower_bound {M : ℕ} (hM : 0 < M) {F : ℕ → ℝ}
    (hper : Function.Periodic F M) (hF : ¬ IsGcdProfile M F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ A : ℝ, 0 ≤ A → ∃ X : ℕ, 0 < X ∧ ∀ N : ℕ, 1 ≤ N →
      κ * A * (Real.log N - Real.log ((X * M : ℕ) : ℝ)) ≤ jumpEnergy N F := by
  classical
  obtain ⟨n₀, hne⟩ := not_forall.mp hF
  obtain ⟨d, hd⟩ : ∃ d, d = n₀.gcd M := ⟨_, rfl⟩
  rw [← hd] at hne
  have hdpos : 0 < d := by rw [hd]; exact Nat.gcd_pos_of_pos_right _ hM
  have hdM : d ≤ M := by rw [hd]; exact Nat.gcd_le_right _ hM
  obtain ⟨q, hq⟩ : ∃ q, q = M / d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = n₀ / d := ⟨_, rfl⟩
  have hqd : q * d = M := by
    rw [hq]
    exact Nat.div_mul_cancel (by rw [hd]; exact Nat.gcd_dvd_right _ _)
  have hrd : r * d = n₀ := by
    rw [hr]
    exact Nat.div_mul_cancel (by rw [hd]; exact Nat.gcd_dvd_left _ _)
  have hcop : r.Coprime q := by
    rw [hr, hq, hd]
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hM)
  have hq0 : 0 < q := by
    rw [hq]
    exact Nat.div_pos hdM hdpos
  haveI : NeZero q := ⟨hq0.ne'⟩
  have hunit : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).mpr hcop
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = F n₀ - F d := ⟨_, rfl⟩
  have hδ0 : δ ≠ 0 := by rw [hδ]; exact sub_ne_zero.mpr hne
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨δ ^ 2 / M, by positivity, fun A hA => ?_⟩
  -- a finite family of primes in the class carries Mangoldt mass `A`
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun n : ℕ =>
      (if n.Prime then vonMangoldt.residueClass (r : ZMod q) n else 0) / n := ⟨_, rfl⟩
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    rw [hf]
    dsimp only
    refine div_nonneg ?_ (Nat.cast_nonneg n)
    split_ifs
    · exact vonMangoldt.residueClass_nonneg _ n
    · exact le_rfl
  have hdiv : Tendsto (fun n => ∑ i ∈ range n, f i) atTop atTop := by
    refine not_summable_iff_tendsto_nat_atTop_of_nonneg hf0 |>.mp ?_
    rw [hf]
    exact vonMangoldt.not_summable_residueClass_prime_div hunit
  obtain ⟨X, hXA, hX0⟩ := ((hdiv.eventually_ge_atTop A).and (eventually_gt_atTop 0)).exists
  obtain ⟨P, hPd⟩ : ∃ P, P = (range X).filter fun k : ℕ => k.Prime ∧ (k : ZMod q) = (r : ZMod q) :=
    ⟨_, rfl⟩
  have hsumP : ∑ i ∈ range X, f i = ∑ k ∈ P, Λ k / k := by
    rw [hPd, sum_filter]
    refine sum_congr rfl fun k _ => ?_
    rw [hf]
    dsimp only
    by_cases hp : k.Prime
    · by_cases hk : (k : ZMod q) = (r : ZMod q)
      · simp only [hp, hk, and_self, if_true, vonMangoldt.residueClass, Set.indicator_apply,
          Set.mem_setOf_eq]
      · simp only [hp, hk, and_false, if_true, if_false, vonMangoldt.residueClass,
          Set.indicator_apply, Set.mem_setOf_eq, zero_div]
    · simp only [hp, false_and, if_false, zero_div]
  have hmass : A ≤ ∑ k ∈ P, Λ k / k := hsumP ▸ hXA
  refine ⟨X, hX0, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = N / (X * M) := ⟨_, rfl⟩
  have hXM : 0 < X * M := Nat.mul_pos hX0 hM
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℕ, m = fun i => d + M * (i - 1) := ⟨_, rfl⟩
  have hmle : ∀ i ∈ Icc 1 Y, m i ≤ M * i := fun i hi => by
    have hi1 := (mem_Icc.mp hi).1
    rw [hm]
    dsimp only
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel, mul_add, mul_one]
    omega
  have hm1 : ∀ i, 1 ≤ m i := fun i => by
    rw [hm]
    dsimp only
    omega
  have hmYX : ∀ i ∈ Icc 1 Y, ∀ k ∈ P, k * m i ≤ N := fun i hi k hk => by
    have hkX : k ≤ X := (mem_range.mp (mem_filter.mp (hPd ▸ hk)).1).le
    have hiY := (mem_Icc.mp hi).2
    calc
      k * m i ≤ X * (M * Y) := Nat.mul_le_mul hkX ((hmle i hi).trans (Nat.mul_le_mul_left M hiY))
      _ = (X * M) * Y := by ring
      _ ≤ N := by rw [hY]; exact Nat.mul_div_le N (X * M)
  -- the values of the jump
  have hmF : ∀ i, F (m i) = F d := fun i => by
    rw [← hper.map_mod_nat (m i), ← hper.map_mod_nat d, hm]
    dsimp only
    rw [Nat.add_mul_mod_self_left]
  have hkF : ∀ k ∈ P, ∀ i, F (k * m i) = F n₀ := fun k hk i => by
    have hkq : (k : ZMod q) = (r : ZMod q) := (mem_filter.mp (hPd ▸ hk)).2.2
    have hmod : k ≡ r [MOD q] := (ZMod.natCast_eq_natCast_iff k r q).mp hkq
    have hmod2 : k * d ≡ r * d [MOD q * d] := hmod.mul_right' d
    rw [hqd, hrd] at hmod2
    rw [← hper.map_mod_nat (k * m i), ← hper.map_mod_nat n₀, hm]
    dsimp only
    have hexp : k * (d + M * (i - 1)) = k * d + M * (k * (i - 1)) := by ring
    rw [hexp, Nat.add_mul_mod_self_left]
    exact congrArg F hmod2
  have hminj : Set.InjOn m (Icc 1 Y : Finset ℕ) := fun i hi j hj hij => by
    have hi1 := (mem_Icc.mp (mem_coe.mp hi)).1
    have hj1 := (mem_Icc.mp (mem_coe.mp hj)).1
    rw [hm] at hij
    dsimp only at hij
    have h := Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel hij)
    omega
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ Λ p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2) := fun p =>
    mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  have hΛ0 : ∀ k : ℕ, 0 ≤ Λ k / k := fun k => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
  have hPpos : ∀ k ∈ P, 1 ≤ k := fun k hk =>
    (mem_filter.mp (hPd ▸ hk)).2.1.pos
  -- restrict the energy to the family
  have hrestrict : ∑ k ∈ P, ∑ i ∈ Icc 1 Y, Λ k / k * (δ ^ 2 / (m i : ℝ)) ≤ jumpEnergy N F := by
    unfold jumpEnergy
    have himage : ∑ k ∈ P, ∑ i ∈ Icc 1 Y, Λ k / k * (δ ^ 2 / (m i : ℝ)) =
        ∑ p ∈ P ×ˢ ((Icc 1 Y).image m), Λ p.1 / p.1 * ((F (p.1 * p.2) - F p.2) ^ 2 / p.2) := by
      rw [sum_product]
      refine sum_congr rfl fun k hk => ?_
      rw [sum_image hminj]
      refine sum_congr rfl fun i _ => ?_
      simp only
      rw [hkF k hk i, hmF i, hδ]
    rw [himage]
    refine sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => hnn p
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_product.mp hp
    obtain ⟨i, hi, hpi⟩ := mem_image.mp hp2
    have hprod : p.1 * p.2 ≤ N := hpi ▸ hmYX i hi p.1 hp1
    have hk1 := hPpos p.1 hp1
    have hm1i : 1 ≤ p.2 := hpi ▸ hm1 i
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hk1, (Nat.le_mul_of_pos_right _ hm1i).trans hprod⟩,
      mem_Icc.mpr ⟨hm1i, (Nat.le_mul_of_pos_left _ hk1).trans hprod⟩⟩, hprod⟩
  -- the harmonic mass of the progression
  have hlogY : Real.log N - Real.log ((X * M : ℕ) : ℝ) ≤ ∑ i ∈ Icc 1 Y, 1 / (i : ℝ) := by
    have hlt : N < (X * M) * (Y + 1) := by rw [hY]; exact Nat.lt_mul_div_succ N hXM
    have hltR : (N : ℝ) ≤ ((X * M : ℕ) : ℝ) * ((Y + 1 : ℕ) : ℝ) := by
      exact_mod_cast hlt.le
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hXM0 : (0 : ℝ) < ((X * M : ℕ) : ℝ) := by exact_mod_cast hXM
    have hY0 : (0 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by positivity
    have hl := Real.log_le_log hN0 hltR
    rw [Real.log_mul hXM0.ne' hY0.ne'] at hl
    rw [sum_inv_eq_harmonic]
    have hh := log_add_one_le_harmonic Y
    linarith only [hl, hh]
  have hharm0 : 0 ≤ ∑ i ∈ Icc 1 Y, 1 / (i : ℝ) := sum_nonneg fun i _ => by positivity
  have hbound : δ ^ 2 / M * ((∑ k ∈ P, Λ k / k) * ∑ i ∈ Icc 1 Y, 1 / (i : ℝ)) ≤
      ∑ k ∈ P, ∑ i ∈ Icc 1 Y, Λ k / k * (δ ^ 2 / (m i : ℝ)) := by
    rw [sum_mul_sum, mul_sum]
    refine sum_le_sum fun k _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun i hi => ?_
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.mp hi).1
    have hmi : (m i : ℝ) ≤ M * i := by exact_mod_cast hmle i hi
    have hmi0 : (0 : ℝ) < m i := by exact_mod_cast hm1 i
    have hfrac : δ ^ 2 / (M * i) ≤ δ ^ 2 / (m i : ℝ) :=
      div_le_div_of_nonneg_left hδ2.le hmi0 hmi
    have h := mul_le_mul_of_nonneg_left hfrac (hΛ0 k)
    refine le_trans (le_of_eq ?_) h
    have hi0 : (i : ℝ) ≠ 0 := by positivity
    field_simp
  refine le_trans ?_ (hbound.trans hrestrict)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases hsign : Real.log N - Real.log ((X * M : ℕ) : ℝ) ≤ 0
  · exact (mul_nonpos_of_nonneg_of_nonpos hA hsign).trans
      (mul_nonneg (hA.trans hmass) hharm0)
  · exact mul_le_mul hmass hlogY (not_le.mp hsign).le (hA.trans hmass)

/-- **Outside the gcd profiles the jump energy beats `log N`.** -/
theorem tendsto_jumpEnergy_div_log_atTop {M : ℕ} (hM : 0 < M) {F : ℕ → ℝ}
    (hper : Function.Periodic F M) (hF : ¬ IsGcdProfile M F) :
    Tendsto (fun N : ℕ => jumpEnergy N F / Real.log N) atTop atTop := by
  obtain ⟨κ, hκ, h⟩ := exists_jumpEnergy_lower_bound hM hper hF
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop.mpr fun b => ?_
  obtain ⟨X, -, hX⟩ := h (2 * |b| / κ) (by positivity)
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_ge_atTop 1,
    hlog.eventually_ge_atTop (2 * Real.log ((X * M : ℕ) : ℝ))] with N hN hL1 hL2
  have hL0 : 0 < Real.log (N : ℝ) := by linarith only [hL1]
  rw [le_div_iff₀ hL0]
  have hb := le_abs_self b
  have hk : κ * (2 * |b| / κ) = 2 * |b| := by field_simp
  have hmain := hX N hN
  rw [hk] at hmain
  have habs : 0 ≤ |b| := abs_nonneg b
  nlinarith only [hmain, hb, habs, hL1, hL2, mul_le_mul_of_nonneg_left
    (show Real.log ((X * M : ℕ) : ℝ) ≤ Real.log N / 2 by linarith only [hL2]) habs,
    mul_le_mul_of_nonneg_right hb hL0.le]

/-- **The dichotomy.** A periodic function has jump energy `O(log N)` exactly when it is a gcd profile. -/
theorem isGcdProfile_iff_jumpEnergy_isBigO_log {M : ℕ} (hM : 0 < M) {F : ℕ → ℝ}
    (hper : Function.Periodic F M) :
    IsGcdProfile M F ↔ ∃ C : ℝ, ∀ N : ℕ, 3 ≤ N → jumpEnergy N F ≤ C * Real.log N := by
  constructor
  · intro hF
    obtain ⟨V, hVd⟩ : ∃ V, V = ∑ r ∈ range M, |F r| := ⟨_, rfl⟩
    have hV : ∀ n, |F n| ≤ V := fun n => by
      rw [← hper.map_mod_nat n, hVd]
      exact single_le_sum (f := fun r => |F r|) (fun _ _ => abs_nonneg _)
        (mem_range.mpr (Nat.mod_lt n hM))
    refine ⟨8 * V ^ 2 * Real.log M, fun N hN => ?_⟩
    refine (jumpEnergy_le_of_isGcdProfile hM hF hV N).trans ?_
    have hL1 : 1 ≤ Real.log (N : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
      linarith only [Real.exp_one_lt_d9, h3]
    have hc : 0 ≤ 4 * V ^ 2 * Real.log M :=
      mul_nonneg (by positivity) (Real.log_natCast_nonneg M)
    nlinarith only [mul_le_mul_of_nonneg_left hL1 hc]
  · intro ⟨C, hC⟩
    by_contra hF
    obtain ⟨N, hbig, hN3⟩ := (((tendsto_jumpEnergy_div_log_atTop hM hper hF).eventually_gt_atTop C).and
      (eventually_ge_atTop 3)).exists
    have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by
      have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN3
      linarith only [h3])
    rw [lt_div_iff₀ hL0] at hbig
    exact absurd (hC N hN3) (not_le.mpr hbig)

end GaloisForLFunctions.ArithmeticCouplingTheory
