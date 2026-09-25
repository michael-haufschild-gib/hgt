import GaloisForLFunctions.RHTower.KloostermanZeta

open RHTower.Sieve

/-!
# Kloosterman sums with one frequency fixed: summability uniform in the other

`kmaxU n c = max_{A mod c} kmax(A, n; c) = max_{A, a unit} |S(aA, an; c)|` is submultiplicative on coprime moduli
and obeys Weil's bound `2√p` and the prime-power bound `2p^{⌈k/2⌉}` at primes `p ∤ 2n`, uniformly in `A`.
The summability criterion for such majorants (`gw_summable`, the argument of `KloostermanZeta` for an arbitrary
majorant `g`) gives `Σ_c kmaxU(n; c) c^{-2σ} < ∞` for `n ≠ 0`, `σ > 3/4` (`kmaxU_summable`): the Kloosterman
zeta function converges absolutely, uniformly in the free frequency.
-/

namespace GaloisForLFunctions.RHTower.KloostermanUniform

open GaloisForLFunctions.RHTower.KloostermanZeta

noncomputable section

/-! ### Summability for Weil-type majorants -/

section general

/-- The weighted coefficient `g(c) c^{-2σ}`. -/
def gw (g : ℕ → ℝ) (σ : ℝ) (c : ℕ) : ℝ := g c * (c : ℝ) ^ (-2 * σ)

variable {g : ℕ → ℝ} {σ : ℝ}

theorem gw_nonneg (hg0 : ∀ c, 0 ≤ g c) (c : ℕ) : 0 ≤ gw g σ c :=
  mul_nonneg (hg0 c) (Real.rpow_nonneg (Nat.cast_nonneg c) _)

theorem gw_one (hg1 : g 1 ≤ 1) : gw g σ 1 ≤ 1 := by
  simp only [gw, Nat.cast_one, Real.one_rpow, mul_one]; exact hg1

theorem gw_mul (hmul : ∀ a b, a.Coprime b → g (a * b) ≤ g a * g b) {a b : ℕ} (h : a.Coprime b) :
    gw g σ (a * b) ≤ gw g σ a * gw g σ b := by
  simp only [gw, Nat.cast_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  have ha := Real.rpow_nonneg (Nat.cast_nonneg a) (-2 * σ)
  have hb := Real.rpow_nonneg (Nat.cast_nonneg b) (-2 * σ)
  calc g (a * b) * ((a : ℝ) ^ (-2 * σ) * (b : ℝ) ^ (-2 * σ))
      ≤ g a * g b * ((a : ℝ) ^ (-2 * σ) * (b : ℝ) ^ (-2 * σ)) :=
        mul_le_mul_of_nonneg_right (hmul a b h) (mul_nonneg ha hb)
    _ = _ := by ring

theorem gw_pow_le_geom (hself : ∀ c, g c ≤ c) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    gw g σ (p ^ k) ≤ ((p : ℝ) ^ (1 - 2 * σ)) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [gw]
  calc g (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-2 * σ)
      ≤ ((p ^ k : ℕ) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right (hself _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ((p : ℝ) ^ (1 - 2 * σ)) ^ k := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le,
          ← Real.rpow_add hp0]
        congr 1; ring

theorem gw_prime_le {p : ℕ} (hp : p.Prime) (hgp : g p ≤ 2 * Real.sqrt p) :
    gw g σ p ≤ 2 * (p : ℝ) ^ (1 / 2 - 2 * σ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [gw]
  calc g p * (p : ℝ) ^ (-2 * σ) ≤ 2 * Real.sqrt p * (p : ℝ) ^ (-2 * σ) :=
        mul_le_mul_of_nonneg_right hgp (Real.rpow_nonneg hp0.le _)
    _ = 2 * (p : ℝ) ^ (1 / 2 - 2 * σ) := by
        rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hp0]; ring_nf

theorem gw_prime_pow_le (hσ : 3 / 4 ≤ σ) {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hgk : g (p ^ k) ≤ 2 * (p : ℝ) ^ ((k + 1) / 2)) :
    gw g σ (p ^ k) ≤ 2 * Real.sqrt p * ((p : ℝ)⁻¹) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  simp only [gw]
  have h1 : ((p : ℝ) ^ ((k + 1) / 2 : ℕ)) ≤ (p : ℝ) ^ (((k : ℝ) + 1) / 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have : (((k + 1) / 2 : ℕ) : ℝ) * 2 ≤ (k : ℝ) + 1 := by
      have := Nat.div_mul_le_self (k + 1) 2
      exact_mod_cast this
    linarith
  have h2 : ((p ^ k : ℕ) : ℝ) ^ (-2 * σ) ≤ (p : ℝ) ^ (-(3 / 2) * (k : ℝ)) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  calc g (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-2 * σ)
      ≤ (2 * (p : ℝ) ^ (((k : ℝ) + 1) / 2)) * (p : ℝ) ^ (-(3 / 2) * (k : ℝ)) := by
        apply mul_le_mul _ h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
        exact hgk.trans (by linarith)
    _ = 2 * Real.sqrt p * ((p : ℝ)⁻¹) ^ k := by
        rw [Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hp0.le, mul_assoc, mul_assoc,
          ← Real.rpow_add hp0, ← Real.rpow_add hp0]
        congr 2; ring

theorem gw_hs (hg0 : ∀ c, 0 ≤ g c) (hself : ∀ c, g c ≤ c) (hσ : 1 / 2 < σ) {p : ℕ} (hp : p.Prime) :
    Summable (fun k => gw g σ (p ^ (k + 1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set r := (p : ℝ) ^ (1 - 2 * σ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by linarith) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  refine Summable.of_nonneg_of_le (fun k => gw_nonneg hg0 _) (fun k => gw_pow_le_geom hself hp (k + 1)) ?_
  simp_rw [pow_succ]
  exact (summable_geometric_of_lt_one hr0 hr1).mul_right r

theorem gw_local_le (hg0 : ∀ c, 0 ≤ g c) (hself : ∀ c, g c ≤ c) (hσ : 3 / 4 < σ) {p : ℕ} (hp : p.Prime)
    (hgp : g p ≤ 2 * Real.sqrt p) (hgk : ∀ k, 2 ≤ k → g (p ^ k) ≤ 2 * (p : ℝ) ^ ((k + 1) / 2)) :
    ∑' k, gw g σ (p ^ (k + 1)) ≤ 2 * (p : ℝ) ^ (1 / 2 - 2 * σ) + 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs := gw_hs (σ := σ) hg0 hself (by linarith : 1 / 2 < σ) hp
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add, pow_one]
  apply add_le_add (gw_prime_le hp hgp)
  set q := (p : ℝ)⁻¹
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by simp only [q]; rw [inv_lt_one₀ hp0]; linarith
  have hb : ∀ k, gw g σ (p ^ (k + 1 + 1)) ≤ 2 * Real.sqrt p * q ^ 2 * q ^ k := by
    intro k
    have := gw_prime_pow_le (g := g) hσ.le hp (k := k + 2) (hgk (k + 2) (by omega))
    rw [show k + 1 + 1 = k + 2 by ring]
    refine this.trans (le_of_eq ?_)
    ring
  have hsum : Summable (fun k : ℕ => 2 * Real.sqrt p * q ^ 2 * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∑' k, gw g σ (p ^ (k + 1 + 1)) ≤ ∑' k : ℕ, 2 * Real.sqrt p * q ^ 2 * q ^ k :=
        (hs.comp_injective (add_left_injective 1)).tsum_le_tsum hb hsum
    _ = 2 * Real.sqrt p * q ^ 2 * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    _ ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        have h1q : (1 - q)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          simp only [q]
          rw [le_sub_comm, inv_le_comm₀ hp0 (by norm_num)]; linarith
        have heq : Real.sqrt p * q ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
          simp only [q]
          rw [Real.sqrt_eq_rpow, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0]
          norm_num
        have hpos : 0 ≤ Real.sqrt p * q ^ 2 := by positivity
        calc 2 * Real.sqrt p * q ^ 2 * (1 - q)⁻¹ = 2 * (Real.sqrt p * q ^ 2) * (1 - q)⁻¹ := by ring
          _ ≤ 2 * (Real.sqrt p * q ^ 2) * 2 := by gcongr
          _ = 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [heq]; ring

/-- **Summability of Weil-type majorants.** A nonnegative submultiplicative `g` with `g(1) ≤ 1`, `g(c) ≤ c`, and
`g(p) ≤ 2√p`, `g(p^k) ≤ 2p^{⌈k/2⌉}` at every prime `p ∤ 2n` has `Σ_c g(c) c^{-2σ} < ∞` for `σ > 3/4`. -/
theorem gw_summable {n : ℤ} (hn : n ≠ 0) (hσ : 3 / 4 < σ) (hg0 : ∀ c, 0 ≤ g c) (hg1 : g 1 ≤ 1)
    (hmul : ∀ a b, a.Coprime b → g (a * b) ≤ g a * g b) (hself : ∀ c, g c ≤ c)
    (hprime : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ n → g p ≤ 2 * Real.sqrt p)
    (hppow : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ n → ∀ k, 2 ≤ k → g (p ^ k) ≤ 2 * (p : ℝ) ^ ((k + 1) / 2)) :
    Summable (gw g σ) := by
  classical
  apply summable_of_submult (fun c => gw_nonneg hg0 c) (gw_one hg1) (fun a b h => gw_mul hmul h)
    (fun p hp => gw_hs hg0 hself (by linarith) hp)
  set E : Nat.Primes → ℝ := fun p => ∑' k, gw g σ ((p : ℕ) ^ (k + 1))
  set M : ℕ := max 2 n.natAbs
  set bad : Finset Nat.Primes := (Finset.range (M + 1)).subtype Nat.Prime
  set B : Nat.Primes → ℝ := fun p => 2 * ((p : ℕ) : ℝ) ^ (1 / 2 - 2 * σ) + 4 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
  have hB : Summable B := by
    apply Summable.add
    · exact (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 2
    · exact (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left 4
  have hF : Summable (fun p => if p ∈ bad then E p else 0) :=
    summable_of_ne_finset_zero (s := bad) (fun p hp => if_neg hp)
  have hEnn : ∀ p, 0 ≤ E p := fun p => tsum_nonneg (fun _ => gw_nonneg hg0 _)
  refine Summable.of_nonneg_of_le hEnn (fun p => ?_) (hB.add hF)
  by_cases hp : p ∈ bad
  · simp only [if_pos hp]
    have : 0 ≤ B p := by simp only [B]; positivity
    linarith
  · simp only [if_neg hp, add_zero]
    have hpM : M < (p : ℕ) := by
      by_contra h; push Not at h
      exact hp (Finset.mem_subtype.mpr (Finset.mem_range.mpr (by omega)))
    have hp2 : (p : ℕ) ≠ 2 := by omega
    have hnd : ¬ ((p : ℕ) : ℤ) ∣ n := by
      intro hd
      have := Int.natAbs_dvd_natAbs.mpr hd
      simp only [Int.natAbs_natCast] at this
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) this
      omega
    exact gw_local_le hg0 hself hσ p.2 (hprime p p.2 hp2 hnd) (hppow p p.2 hp2 hnd)

end general

/-! ### The uniform majorant -/

/-- `kmaxU(n; c) = max_{A mod c} max_{a unit} |S(aA, an; c)|` (zero for `c = 0`). -/
def kmaxU (n : ℤ) (c : ℕ) : ℝ :=
  if h : c = 0 then 0 else
    haveI : NeZero c := ⟨h⟩
    ⨆ A : ZMod c, kmax (A.val : ℤ) n c

theorem kmax_val (A n : ℤ) (c : ℕ) [NeZero c] : kmax (((A : ZMod c).val : ℕ) : ℤ) n c = kmax A n c := by
  rw [kmax_eq, kmax_eq]
  congr 1; ext a
  congr 3
  push_cast
  simp

theorem kmaxU_eq (n : ℤ) (c : ℕ) [hc : NeZero c] : kmaxU n c = ⨆ A : ZMod c, kmax (A.val : ℤ) n c := by
  rw [kmaxU, dif_neg hc.ne]

theorem le_kmaxU (A n : ℤ) (c : ℕ) [NeZero c] : kmax A n c ≤ kmaxU n c := by
  rw [kmaxU_eq, ← kmax_val]
  exact le_ciSup (f := fun B : ZMod c => kmax (B.val : ℤ) n c) (Set.finite_range _).bddAbove _

theorem kmaxU_le (n : ℤ) (c : ℕ) [NeZero c] {B : ℝ} (h : ∀ A : ℤ, kmax A n c ≤ B) : kmaxU n c ≤ B := by
  rw [kmaxU_eq]
  exact ciSup_le (fun A => h _)

theorem kmaxU_nonneg (n : ℤ) (c : ℕ) : 0 ≤ kmaxU n c := by
  by_cases hc : c = 0
  · simp [kmaxU, hc]
  · haveI : NeZero c := ⟨hc⟩
    exact (kmax_nonneg 0 n c).trans (le_kmaxU 0 n c)

theorem kmaxU_mul (n : ℤ) {q r : ℕ} (h : q.Coprime r) : kmaxU n (q * r) ≤ kmaxU n q * kmaxU n r := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp [kmaxU]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [kmaxU]
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  haveI : NeZero (q * r) := ⟨(Nat.mul_pos hq hr).ne'⟩
  apply kmaxU_le
  intro A
  exact (kmax_mul A n h).trans (mul_le_mul (le_kmaxU A n q) (le_kmaxU A n r) (kmax_nonneg _ _ _)
    (kmaxU_nonneg n q))

theorem kmaxU_one (n : ℤ) : kmaxU n 1 ≤ 1 := kmaxU_le n 1 (fun A => kmax_one A n)

theorem kmaxU_le_self (n : ℤ) (c : ℕ) : kmaxU n c ≤ c := by
  by_cases hc : c = 0
  · simp [kmaxU, hc]
  haveI : NeZero c := ⟨hc⟩
  exact kmaxU_le n c (fun A => kmax_le_self A n c)

theorem kmaxU_prime_le (n : ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : ¬ (p : ℤ) ∣ n) :
    kmaxU n p ≤ 2 * Real.sqrt p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact kmaxU_le n p (fun A => kmax_prime_le A n hp2 hn)

theorem kmaxU_prime_pow_le (n : ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : ¬ (p : ℤ) ∣ n)
    {k : ℕ} (hk : 2 ≤ k) : kmaxU n (p ^ k) ≤ 2 * (p : ℝ) ^ ((k + 1) / 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact kmaxU_le n _ (fun A => kmax_prime_pow_le A n hp2 hn hk)

/-- **Uniform absolute convergence of the Kloosterman zeta function**: for `n ≠ 0` and `σ > 3/4`,
`Σ_c max_A |S(A, n; c)| c^{-2σ} < ∞`. -/
theorem kmaxU_summable {n : ℤ} (hn : n ≠ 0) {σ : ℝ} (hσ : 3 / 4 < σ) : Summable (gw (kmaxU n) σ) :=
  gw_summable hn hσ (kmaxU_nonneg n) (kmaxU_one n) (fun _ _ h => kmaxU_mul n h) (kmaxU_le_self n)
    (fun _ hp hp2 hnd => kmaxU_prime_le n hp hp2 hnd)
    (fun _ hp hp2 hnd _ hk => kmaxU_prime_pow_le n hp hp2 hnd hk)

/-- Every Kloosterman sum is bounded by the uniform majorant. -/
theorem norm_kloostermanSum_le_kmaxU (A n : ℤ) (c : ℕ) [NeZero c] :
    ‖kloostermanSum c (A : ZMod c) (n : ZMod c)‖ ≤ kmaxU n c := by
  refine le_trans ?_ (le_kmaxU A n c)
  have := le_kmax A n c (x := 1) isUnit_one
  simpa using this

end

end GaloisForLFunctions.RHTower.KloostermanUniform
