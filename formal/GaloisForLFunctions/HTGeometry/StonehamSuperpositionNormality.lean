import GaloisForLFunctions.HTGeometry.OrbitSumKorobovPowerSaving
import GaloisForLFunctions.HTGeometry.StonehamPairNormality

/-!
# Finite superpositions of Stoneham constants are equidistributed under `×4`

Let `S` be a finite nonempty set of odd primes and `x_S = Σ_{p∈S} α_{2,p}`, with
`α_{2,p} = Σ_{j≥1} p^{−j} 2^{−p^j}`.

On the window `p^{a_p} ≤ 2n < p^{a_p+1}` (`p ∈ S`) one has `4ⁿ x_S = R(n)/Q + O(1/n)`, where
`Q = Π_{p∈S} p^{a_p}` and `R(n + i) = 4ⁱ R(n)` (`four_pow_mul_superStoneham`, `windowNum_add`).
The moduli are not nested, and a window has length `L` with `L^{|S|} ≤ (Π_S p) Q`, below the reach
of completion as soon as `|S| ≥ 2`.

* The window is a fiber of the map `n ↦ (⌊log_p 2n⌋)_{p∈S}`, an interval by monotonicity
  (`norm_sum_fiber_le`).
* Korobov's power saving modulo `Q` for the base `4^{Π(p−1)}` (`norm_window_sum_le`) gives
  `C_k Q^{θ}` with `θ = θ_{|S|} = 1/|S| − 2^{−|S|}/(|S|(|S|+1))`.
* Summing over all windows by a product of geometric series gives
  `Σ_{n<N} e(k 4ⁿ x_S) = O_k(N^{|S| θ})` with `|S| θ < 1` (`tendsto_weylSum_superOrbit`).
* Weyl's criterion then gives equidistribution of `{4ⁿ x_S}` in every `[a, b) ⊂ (0, 1)`
  (`tendsto_card_fract_superOrbit`).
* Hence the parity drift is `o(N)` (`not_parityDriftHypothesis_superStoneham`).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.StonehamSuperposition

open StonehamParityDrift StonehamPrimeDrift ThreeFiveOrbit DiscreteWeyl BinaryParityDrift
open OrbitVanishing OrbitPowerSaving

/-- The superposition `x_S = Σ_{p∈S} α_{2,p}` of Stoneham constants. -/
noncomputable def superStoneham (S : Finset ℕ) : ℝ := ∑ p ∈ S, stonehamP p

/-- The modulus `Q_a = Π_{p∈S} p^{a_p}` of the window with exponents `a`. -/
def windowModulus (S : Finset ℕ) (a : ℕ → ℕ) : ℕ := ∏ p ∈ S, p ^ a p

/-- The numerator `R_a(n) = Σ_{p∈S} 2^{2n−p^{a_p}} A_p(a_p) Q_a/p^{a_p}`. -/
def windowNum (S : Finset ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ p ∈ S, 2 ^ (2 * n - p ^ a p) * stonehamPA p (a p) * (windowModulus S a / p ^ a p)

variable {S : Finset ℕ}

theorem windowModulus_eq_mul_erase {a : ℕ → ℕ} {p : ℕ} (hp : p ∈ S) :
    windowModulus S a = p ^ a p * ∏ q ∈ S.erase p, q ^ a q := by
  unfold windowModulus
  rw [mul_prod_erase S (fun q => q ^ a q) hp]

theorem windowModulus_div {a : ℕ → ℕ} {p : ℕ} (hp : p ∈ S) (hp0 : 0 < p) :
    windowModulus S a / p ^ a p = ∏ q ∈ S.erase p, q ^ a q := by
  rw [windowModulus_eq_mul_erase hp, Nat.mul_div_cancel_left _ (pow_pos hp0 _)]

theorem windowNum_add {a : ℕ → ℕ} {n : ℕ} (ha : ∀ p ∈ S, p ^ a p ≤ 2 * n) (i : ℕ) :
    windowNum S a (n + i) = windowNum S a n * 4 ^ i := by
  unfold windowNum
  rw [sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [show 2 * (n + i) - p ^ a p = (2 * n - p ^ a p) + 2 * i by have := ha p hp; omega,
    pow_add, pow_mul]
  norm_num
  ring

theorem windowModulus_pos (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (a : ℕ → ℕ) :
    0 < windowModulus S a :=
  prod_pos fun p hp => pow_pos (hS p hp).1.pos _

/-- **Coprimality.**  If every exponent is at least `1`, `R_a(n)` is prime to `Q_a`. -/
theorem coprime_windowNum (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) {a : ℕ → ℕ}
    (ha : ∀ p ∈ S, 1 ≤ a p) (n : ℕ) : Nat.Coprime (windowNum S a n) (windowModulus S a) := by
  refine Nat.coprime_of_dvd fun q hq hqR hqQ => ?_
  -- `q ∈ S`
  have hqS : q ∈ S := by
    unfold windowModulus at hqQ
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqQ
    have := (Nat.prime_dvd_prime_iff_eq hq (hS p hp).1).mp (hq.dvd_of_dvd_pow hqp)
    exact this ▸ hp
  have hq2 : q ≠ 2 := (hS q hqS).2
  -- every other term is divisible by `q`
  have hother : q ∣ ∑ p ∈ S.erase q,
      2 ^ (2 * n - p ^ a p) * stonehamPA p (a p) * (windowModulus S a / p ^ a p) := by
    refine dvd_sum fun p hp => ?_
    have hpS := mem_of_mem_erase hp
    have hpq := ne_of_mem_erase hp
    refine Dvd.dvd.mul_left ?_ _
    rw [windowModulus_div hpS (hS p hpS).1.pos]
    refine dvd_trans (dvd_pow_self q (Nat.one_le_iff_ne_zero.mp (ha q hqS))) ?_
    exact dvd_prod_of_mem (fun r => r ^ a r) (mem_erase.mpr ⟨fun h => hpq h.symm, hqS⟩)
  have hR : windowNum S a n = 2 ^ (2 * n - q ^ a q) * stonehamPA q (a q) *
      (windowModulus S a / q ^ a q) + ∑ p ∈ S.erase q,
        2 ^ (2 * n - p ^ a p) * stonehamPA p (a p) * (windowModulus S a / p ^ a p) := by
    unfold windowNum
    exact (add_sum_erase S _ hqS).symm
  rw [hR] at hqR
  have hterm := (Nat.dvd_add_left hother).mp hqR
  rcases (Nat.Prime.dvd_mul hq).mp hterm with h | h
  · rcases (Nat.Prime.dvd_mul hq).mp h with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · have hA := stonehamPA_mod (p := q) hq.two_le (ha q hqS)
      have := Nat.mod_eq_zero_of_dvd h
      omega
  · rw [windowModulus_div hqS (hS q hqS).1.pos] at h
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp h
    have hpS := mem_of_mem_erase hp
    have := (Nat.prime_dvd_prime_iff_eq hq (hS p hpS).1).mp (hq.dvd_of_dvd_pow hqp)
    exact ne_of_mem_erase hp this.symm

/-! ### The window identity -/

/-- **The window identity.**  On the window `p^{a_p} ≤ 2n < p^{a_p+1}` (`p ∈ S`),
`4ⁿ x_S = R_a(n)/Q_a + t` with `0 ≤ t ≤ Σ_{p∈S} 1/(4 p^{a_p})`. -/
theorem four_pow_mul_superStoneham (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) {a : ℕ → ℕ} {n : ℕ}
    (ha1 : ∀ p ∈ S, p ^ a p ≤ 2 * n) (ha2 : ∀ p ∈ S, 2 * n < p ^ (a p + 1)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ ∑ p ∈ S, 1 / (4 * (p : ℝ) ^ a p) ∧
      (4 : ℝ) ^ n * superStoneham S = (windowNum S a n : ℝ) / windowModulus S a + t := by
  have hp3 : ∀ p ∈ S, 3 ≤ p := fun p hp => by
    have := (hS p hp).1.two_le; have := (hS p hp).2; omega
  have hodd : ∀ p ∈ S, p % 2 = 1 := fun p hp =>
    ((hS p hp).1.eq_one_or_self_of_dvd 2 |> fun _ => Nat.odd_iff.mp
      ((hS p hp).1.odd_of_ne_two (hS p hp).2))
  set δ : ℕ → ℝ := fun p => (4 : ℝ) ^ n * stonehamP p -
    ((2 ^ (2 * n - p ^ a p) * stonehamPA p (a p) : ℕ) : ℝ) / (p : ℝ) ^ a p with hδ
  have hδb : ∀ p ∈ S, 0 ≤ δ p ∧ δ p ≤ 1 / (4 * (p : ℝ) ^ a p) := by
    intro p hp
    obtain ⟨t, ht0, ht1, ht⟩ := four_pow_mul_stonehamP (hp3 p hp) (hodd p hp) (ha1 p hp)
      (ha2 p hp)
    have hpa : (0 : ℝ) < (p : ℝ) ^ a p := by have := (hS p hp).1.pos; positivity
    simp only [hδ]
    push_cast at ht ht1 ⊢
    rw [ht]
    constructor
    · linarith
    · rw [le_div_iff₀ (by positivity)]; linarith
  refine ⟨∑ p ∈ S, δ p, sum_nonneg fun p hp => (hδb p hp).1, sum_le_sum fun p hp => (hδb p hp).2,
    ?_⟩
  have hQ0 : (0 : ℝ) < windowModulus S a := by exact_mod_cast windowModulus_pos hS a
  have hR : (windowNum S a n : ℝ) / windowModulus S a = ∑ p ∈ S,
      ((2 ^ (2 * n - p ^ a p) * stonehamPA p (a p) : ℕ) : ℝ) / (p : ℝ) ^ a p := by
    unfold windowNum
    push_cast
    rw [sum_div]
    refine sum_congr rfl fun p hp => ?_
    have hdvd : p ^ a p ∣ windowModulus S a := ⟨_, windowModulus_eq_mul_erase hp⟩
    have hpa : (0 : ℝ) < (p : ℝ) ^ a p := by have := (hS p hp).1.pos; positivity
    rw [Nat.cast_div hdvd (by push_cast; exact hpa.ne')]
    push_cast
    field_simp
  rw [hR, ← sum_add_distrib, superStoneham, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  simp only [hδ]
  ring

/-- The exponents `a_p(n) = ⌊log_p 2n⌋` of the window containing `n`. -/
def logs (n : ℕ) : ℕ → ℕ := fun p => Nat.log p (2 * n)

theorem logs_spec {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) :
    p ^ logs n p ≤ 2 * n ∧ 2 * n < p ^ (logs n p + 1) :=
  ⟨Nat.pow_log_le_self p (by omega), Nat.lt_pow_succ_log_self (by omega) _⟩

/-- The rational approximation `e(k R(n)/Q(n))` of `e(k 4ⁿ x_S)`. -/
noncomputable def superPhase (S : Finset ℕ) (k n : ℕ) : ℂ :=
  ephase (windowModulus S (logs n)) ((k : ℤ) * windowNum S (logs n) n)

/-- **The rational approximation is good.**  `‖e(k 4ⁿ x_S) − e(k R(n)/Q(n))‖ ≤ 2π k Σ_S p / n`. -/
theorem norm_exp_sub_superPhase_le (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (k : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    ‖Complex.exp (2 * Real.pi * Complex.I * k * ((4 : ℝ) ^ n * superStoneham S : ℝ)) -
      superPhase S k n‖ ≤ 2 * Real.pi * k * (∑ p ∈ S, (p : ℝ)) / n := by
  have hspec := fun p (hp : p ∈ S) => logs_spec (n := n) (hS p hp).1.two_le hn
  obtain ⟨t, ht0, ht1, ht⟩ := four_pow_mul_superStoneham hS (a := logs n)
    (fun p hp => (hspec p hp).1) (fun p hp => (hspec p hp).2)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have htn : t ≤ (∑ p ∈ S, (p : ℝ)) / n := by
    refine ht1.trans ?_
    rw [sum_div]
    refine sum_le_sum fun p hp => ?_
    have h2 : (2 * n : ℝ) < p * (p : ℝ) ^ logs n p := by
      have := (hspec p hp).2
      rw [pow_succ] at this
      exact_mod_cast (by linarith : 2 * n < p ^ logs n p * p) |>.trans_eq (by ring)
    have hpa : (0 : ℝ) < (p : ℝ) ^ logs n p := by have := (hS p hp).1.pos; positivity
    rw [div_le_div_iff₀ (by positivity) hnr]
    nlinarith
  have hsplit : Complex.exp (2 * Real.pi * Complex.I * k * ((4 : ℝ) ^ n * superStoneham S : ℝ)) =
      superPhase S k n * Complex.exp (((2 * Real.pi * k * t : ℝ)) * Complex.I) := by
    rw [ht, superPhase, ephase, ← Complex.exp_add]
    congr 1
    push_cast
    have : (windowModulus S (logs n) : ℂ) ≠ 0 := by
      exact_mod_cast (windowModulus_pos hS _).ne'
    field_simp
  rw [hsplit, ← mul_sub_one, norm_mul, show ‖superPhase S k n‖ = 1 from norm_ephase _ _, one_mul]
  refine (StonehamPairDrift.norm_exp_mul_I_sub_one_le _).trans ?_
  rw [abs_of_nonneg (by positivity)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc 2 * Real.pi * k * t ≤ 2 * Real.pi * k * ((∑ p ∈ S, (p : ℝ)) / n) := by gcongr
    _ = 2 * Real.pi * k * (∑ p ∈ S, (p : ℝ)) / n := by ring

/-! ### One window -/

/-- The exponent `m = Π_{p∈S}(p − 1)`; the base `g = 4^m` is `≡ 1` modulo every `p ∈ S`. -/
def superBaseExp (S : Finset ℕ) : ℕ := ∏ p ∈ S, (p - 1)

theorem superBaseExp_pos (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) : 0 < superBaseExp S :=
  prod_pos fun p hp => by have := (hS p hp).1.two_le; omega

theorem dvd_four_pow_sub_one (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) {p : ℕ} (hp : p ∈ S) :
    p ∣ 4 ^ superBaseExp S - 1 := by
  have hpr := (hS p hp).1
  have hcop : Nat.Coprime 4 p := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    refine Nat.Coprime.pow_left _ ?_
    exact (Nat.coprime_primes Nat.prime_two hpr).mpr (hS p hp).2.symm
  have hF := Nat.ModEq.pow_card_sub_one_eq_one hpr hcop
  obtain ⟨t, ht⟩ : p - 1 ∣ superBaseExp S := dvd_prod_of_mem (fun q => q - 1) hp
  have h1 : 4 ^ superBaseExp S ≡ 1 [MOD p] := by
    rw [ht, pow_mul]
    simpa using hF.pow t
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h1.symm

theorem savingExponent_pos {r : ℕ} (hr : 1 ≤ r) : 0 < savingExponent r :=
  lt_of_lt_of_le (by positivity) (inv_succ_le_savingExponent hr)

/-- The constant of the window bound. -/
noncomputable def windowConst (S : Finset ℕ) (k : ℕ) : ℝ :=
  superBaseExp S * savingConst S (4 ^ superBaseExp S) S.card ((k * ∏ p ∈ S, p : ℕ) : ℝ) +
    superBaseExp S

/-- **One window.**  For `Q` with prime factors in `S`, `R` prime to `Q`, `k ≥ 1` and
`L^{|S|} ≤ (Π_S p) Q`, `‖Σ_{i<L} e(k R 4ⁱ/Q)‖ ≤ C_k Q^{θ_{|S|}}`. -/
theorem norm_window_sum_le (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty) {Q : ℕ}
    (hQ : Q ≠ 0) (hQS : Q.primeFactors ⊆ S) {R : ℕ} (hR : Nat.Coprime R Q) {k : ℕ} (hk : 0 < k)
    {L : ℕ} (hL : (L : ℝ) ^ S.card ≤ (∏ p ∈ S, p : ℕ) * Q) :
    ‖∑ i ∈ range L, ephase Q ((k : ℤ) * R * 4 ^ i)‖ ≤
      windowConst S k * (Q : ℝ) ^ savingExponent S.card := by
  have hr : 1 ≤ S.card := Finset.card_pos.mpr hne
  set m := superBaseExp S with hm
  have hm0 : 0 < m := superBaseExp_pos hS
  set g := 4 ^ m with hgdef
  have hg : 2 ≤ g := by
    rw [hgdef]; calc 2 ≤ 4 := by norm_num
      _ = 4 ^ 1 := (pow_one 4).symm
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm0
  have hgS : ∀ p ∈ S, p ∣ g - 1 := fun p hp => dvd_four_pow_sub_one hS hp
  set P : ℕ := ∏ p ∈ S, p with hP
  have hP1 : 1 ≤ P := prod_pos fun p hp => (hS p hp).1.pos
  -- reduce by `gcd(k, Q)`
  obtain ⟨G, hG⟩ : ∃ G, G = Nat.gcd k Q := ⟨_, rfl⟩
  have hG0 : 0 < G := hG ▸ Nat.gcd_pos_of_pos_left _ hk
  obtain ⟨k', hk'⟩ : G ∣ k := hG ▸ Nat.gcd_dvd_left _ _
  obtain ⟨Q', hQ'⟩ : G ∣ Q := hG ▸ Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime k' Q' := by
    have := Nat.coprime_div_gcd_div_gcd (m := k) (n := Q) (hG ▸ hG0)
    rwa [← hG, hk', hQ', Nat.mul_div_cancel_left _ hG0, Nat.mul_div_cancel_left _ hG0] at this
  have hQ'0 : Q' ≠ 0 := by rintro rfl; simp at hQ'; exact hQ hQ'
  have hQ'S : Q'.primeFactors ⊆ S :=
    (Nat.primeFactors_mono ⟨G, by rw [hQ', mul_comm]⟩ hQ).trans hQS
  have hGk : G ≤ k := Nat.le_of_dvd hk (hG ▸ Nat.gcd_dvd_left _ _)
  have hred : ∀ i : ℕ, ephase Q ((k : ℤ) * R * 4 ^ i) = ephase Q' ((k' : ℤ) * R * 4 ^ i) := by
    intro i
    have e1 : Q = Q' * G := by rw [hQ', mul_comm]
    have e2 : (k : ℤ) * R * 4 ^ i = (G : ℤ) * ((k' : ℤ) * R * 4 ^ i) := by
      rw [hk']; push_cast; ring
    rw [e1, e2, ephase_mul_left_cancel hG0.ne']
  simp_rw [hred]
  have hodd : Nat.Coprime 4 Q' := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    intro h2
    exact (hS 2 (hQ'S (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hQ'0⟩))).2 rfl
  have hR' : Nat.Coprime R Q' := Nat.Coprime.coprime_dvd_right ⟨G, by rw [hQ', mul_comm]⟩ hR
  -- the Korobov bound for each residue class of the exponent modulo `m`
  set K := savingConst S g S.card ((k * P : ℕ) : ℝ) with hK
  have hθ0 : 0 ≤ savingExponent S.card := (savingExponent_pos hr).le
  have hQr1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have hQ'Q : (Q' : ℝ) ≤ Q := by
    have : Q' ≤ Q := by rw [hQ']; exact Nat.le_mul_of_pos_left _ hG0
    exact_mod_cast this
  have hQθ1 : (1 : ℝ) ≤ (Q : ℝ) ^ savingExponent S.card := Real.one_le_rpow hQr1 hθ0
  have hclass : ∀ ρ < m, ‖∑ l ∈ range (L / m), ephase Q' ((k' : ℤ) * R * 4 ^ (ρ + m * l))‖ ≤
      K * (Q : ℝ) ^ savingExponent S.card := by
    intro ρ _
    have hu : IsCoprime (((k' * R * 4 ^ ρ : ℕ) : ℤ)) ((Q' : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.mul_left (Nat.Coprime.mul_left hcop hR')
        (Nat.Coprime.pow_left _ hodd))
    have hc : (1 : ℝ) ≤ (k * P : ℕ) := by exact_mod_cast Nat.mul_pos hk hP1
    have hLQ : ((L / m : ℕ) : ℝ) ^ S.card ≤ ((k * P : ℕ) : ℝ) * Q' := by
      have h1 : ((L / m : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.div_le_self L m
      calc ((L / m : ℕ) : ℝ) ^ S.card ≤ (L : ℝ) ^ S.card := by gcongr
        _ ≤ (P : ℝ) * Q := by exact_mod_cast hL
        _ = (P : ℝ) * G * Q' := by rw [hQ']; push_cast; ring
        _ ≤ (P : ℝ) * k * Q' := by gcongr
        _ = ((k * P : ℕ) : ℝ) * Q' := by push_cast; ring
    have hKor := norm_sum_orbit_le hS hg hgS hr hc hQ'0 hQ'S hu hLQ
    have e : ∀ l, ephase Q' ((k' : ℤ) * R * 4 ^ (ρ + m * l)) =
        ephase Q' ((((k' * R * 4 ^ ρ : ℕ) : ℤ)) * (g : ℤ) ^ l) := by
      intro l
      congr 1
      rw [hgdef]
      push_cast
      ring
    simp_rw [e]
    refine hKor.trans ?_
    have hK0 : 0 ≤ K := by
      rw [hK]; unfold savingConst; positivity
    gcongr
  -- assemble
  have hsplit : ∑ i ∈ range L, ephase Q' ((k' : ℤ) * R * 4 ^ i) =
      ∑ ρ ∈ range m, ∑ l ∈ range (L / m), ephase Q' ((k' : ℤ) * R * 4 ^ (ρ + m * l)) +
        ∑ i ∈ range (L % m), ephase Q' ((k' : ℤ) * R * 4 ^ (m * (L / m) + i)) := by
    conv_lhs => rw [← Nat.div_add_mod L m, sum_range_add, sum_range_mul_eq_sum_sum]
  rw [hsplit]
  have hrest : ‖∑ i ∈ range (L % m), ephase Q' ((k' : ℤ) * R * 4 ^ (m * (L / m) + i))‖ ≤ m := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_ephase, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (Nat.mod_lt L hm0).le
  calc ‖∑ ρ ∈ range m, ∑ l ∈ range (L / m), ephase Q' ((k' : ℤ) * R * 4 ^ (ρ + m * l)) +
        ∑ i ∈ range (L % m), ephase Q' ((k' : ℤ) * R * 4 ^ (m * (L / m) + i))‖
      ≤ ∑ ρ ∈ range m, K * (Q : ℝ) ^ savingExponent S.card + m :=
        (norm_add_le _ _).trans (add_le_add ((norm_sum_le _ _).trans
          (sum_le_sum fun ρ hρ => hclass ρ (mem_range.mp hρ))) hrest)
    _ = m * K * (Q : ℝ) ^ savingExponent S.card + m := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ m * K * (Q : ℝ) ^ savingExponent S.card + m * (Q : ℝ) ^ savingExponent S.card := by
        gcongr; nlinarith
    _ = windowConst S k * (Q : ℝ) ^ savingExponent S.card := by
        rw [windowConst, ← hm, ← hgdef, ← hP, ← hK]; ring

/-! ### All windows -/

/-- The window key `n ↦ (a_p(n))_{p∈S}`. -/
def windowKey (S : Finset ℕ) (n : ℕ) : S → ℕ := fun p => logs n p

/-- Extension of a key on `S` by zero. -/
def keyExt (S : Finset ℕ) (a : S → ℕ) : ℕ → ℕ := fun p => if h : p ∈ S then a ⟨p, h⟩ else 0

theorem primeFactors_windowModulus_subset (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (a : ℕ → ℕ) :
    (windowModulus S a).primeFactors ⊆ S := by
  intro q hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  obtain ⟨p, hp, hqd⟩ := (Prime.dvd_finsetProd_iff hqp.prime _).mp (Nat.dvd_of_mem_primeFactors hq)
  have := (Nat.prime_dvd_prime_iff_eq hqp (hS p hp).1).mp (hqp.dvd_of_dvd_pow hqd)
  exact this ▸ hp

/-- **One fiber.**  The fiber `{n ∈ [n₀, N) : key n = a}` is an interval on which the
approximations follow one orbit, so its sum is bounded by `C_k Q_a^{θ}`. -/
theorem norm_sum_fiber_le (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty) {k : ℕ}
    (hk : 0 < k) (N : ℕ) (a : S → ℕ) :
    ‖∑ n ∈ Ico (∏ p ∈ S, p) N with windowKey S n = a, superPhase S k n‖ ≤
      windowConst S k * (windowModulus S (keyExt S a) : ℝ) ^ savingExponent S.card := by
  set F := ({n ∈ Ico (∏ p ∈ S, p) N | windowKey S n = a} : Finset ℕ) with hF
  have hC : 0 ≤ windowConst S k * (windowModulus S (keyExt S a) : ℝ) ^ savingExponent S.card := by
    unfold windowConst savingConst; positivity
  rcases F.eq_empty_or_nonempty with hF0 | hFne
  · rw [hF0, sum_empty, norm_zero]; exact hC
  set s := F.min' hFne with hs
  set M := F.max' hFne with hM
  have hsF : s ∈ F := F.min'_mem hFne
  have hMF : M ∈ F := F.max'_mem hFne
  have hP0 : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS p hp).1.pos
  have hpP : ∀ p ∈ S, p ≤ ∏ q ∈ S, q := fun p hp =>
    Nat.le_of_dvd hP0 (dvd_prod_of_mem _ hp)
  have hsmem := mem_filter.mp hsF
  have hMmem := mem_filter.mp hMF
  have hs0 : ∏ p ∈ S, p ≤ s := (mem_Ico.mp hsmem.1).1
  have hn1 : ∀ n, s ≤ n → 1 ≤ n := fun n hn => by
    obtain ⟨p, hp⟩ := hne; have := hpP p hp; have := (hS p hp).1.pos; omega
  -- the fiber is the interval `[s, M]`
  have hkey : ∀ n, s ≤ n → n ≤ M → ∀ p ∈ S, logs n p = logs s p := by
    intro n h1 h2 p hp
    have e1 : logs s p = a ⟨p, hp⟩ := congrFun hsmem.2 ⟨p, hp⟩
    have e2 : logs M p = a ⟨p, hp⟩ := congrFun hMmem.2 ⟨p, hp⟩
    have m1 : logs s p ≤ logs n p := Nat.log_mono_right (by omega)
    have m2 : logs n p ≤ logs M p := Nat.log_mono_right (by omega)
    omega
  have hFI : F = Ico s (M + 1) := by
    ext n
    constructor
    · intro hn
      exact mem_Ico.mpr ⟨F.min'_le n hn, Nat.lt_succ_of_le (F.le_max' n hn)⟩
    · intro hn
      rw [mem_Ico] at hn
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
      · have := (mem_Ico.mp hMmem.1).2; omega
      · funext p
        rw [← hsmem.2]
        exact hkey n hn.1 (by omega) p p.2
  rw [hFI]
  -- the exponents of the window
  set e := logs s with he
  have hspec : ∀ p ∈ S, p ^ e p ≤ 2 * s ∧ 2 * s < p ^ (e p + 1) :=
    fun p hp => logs_spec (hS p hp).1.two_le (hn1 s le_rfl)
  have he1 : ∀ p ∈ S, 1 ≤ e p := fun p hp => by
    have h2 : p ≤ 2 * s := by have := hpP p hp; omega
    exact (Nat.le_log_iff_pow_le (hS p hp).1.one_lt (by omega)).mpr (by simpa using h2)
  have hmod : windowModulus S (keyExt S a) = windowModulus S e := by
    unfold windowModulus
    refine prod_congr rfl fun p hp => ?_
    simp only [keyExt, dif_pos hp, he]
    rw [← congrFun hsmem.2 ⟨p, hp⟩]
    rfl
  rw [hmod]
  have hphase : ∀ i ∈ range (M + 1 - s), superPhase S k (s + i) =
      ephase (windowModulus S e) ((k : ℤ) * (windowNum S e s : ℕ) * 4 ^ i) := by
    intro i hi
    rw [mem_range] at hi
    have hle : ∀ p ∈ S, logs (s + i) p = e p := fun p hp => hkey (s + i) (by omega) (by omega) p hp
    have hW : windowModulus S (logs (s + i)) = windowModulus S e :=
      prod_congr rfl fun p hp => by rw [hle p hp]
    have hN : windowNum S (logs (s + i)) (s + i) = windowNum S e (s + i) := by
      unfold windowNum
      rw [hW]
      exact sum_congr rfl fun p hp => by rw [hle p hp]
    rw [superPhase, hW, hN, windowNum_add (fun p hp => (hspec p hp).1)]
    push_cast
    ring_nf
  rw [sum_Ico_eq_sum_range, sum_congr rfl hphase]
  have hQ0 : windowModulus S e ≠ 0 := (windowModulus_pos hS e).ne'
  refine norm_window_sum_le hS hne hQ0 (primeFactors_windowModulus_subset hS e)
    (coprime_windowNum hS he1 s) hk ?_
  -- `L^{|S|} ≤ P Q`
  have hLp : ∀ p ∈ S, M + 1 - s ≤ p ^ (e p + 1) := by
    intro p hp
    have hMe : logs M p = e p := hkey M (F.min'_le M hMF) le_rfl p hp
    have hMlt : 2 * M < p ^ (logs M p + 1) := (logs_spec (hS p hp).1.two_le (hn1 M
      (F.min'_le M hMF))).2
    rw [hMe] at hMlt
    have : 3 ≤ p ^ (e p + 1) := by
      have h3 : 3 ≤ p := by have := (hS p hp).1.two_le; have := (hS p hp).2; omega
      calc 3 ≤ p := h3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (e p + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hprod : (M + 1 - s) ^ S.card ≤ (∏ p ∈ S, p) * windowModulus S e := by
    rw [← prod_const, windowModulus, ← prod_mul_distrib]
    exact prod_le_prod' fun p hp => by rw [← pow_succ']; exact hLp p hp
  exact_mod_cast hprod

/-- The constant of the global bound. -/
noncomputable def superGlobalConst (S : Finset ℕ) (k : ℕ) : ℝ :=
  windowConst S k * ∏ p ∈ S, ((p : ℝ) ^ savingExponent S.card /
    ((p : ℝ) ^ savingExponent S.card - 1))

theorem superGlobalConst_nonneg (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty) (k : ℕ) :
    0 ≤ superGlobalConst S k := by
  have hr : 1 ≤ S.card := Finset.card_pos.mpr hne
  have hθ0 : 0 < savingExponent S.card := savingExponent_pos hr
  unfold superGlobalConst
  refine mul_nonneg (by unfold windowConst savingConst; positivity) (prod_nonneg fun p hp => ?_)
  have : 1 < (p : ℝ) ^ savingExponent S.card :=
    Real.one_lt_rpow (by exact_mod_cast (hS p hp).1.one_lt) hθ0
  exact div_nonneg (by positivity) (by linarith)

theorem rpow_windowModulus_keyExt (a : S → ℕ) (θ : ℝ) :
    (windowModulus S (keyExt S a) : ℝ) ^ θ = ∏ p : S, ((p : ℝ) ^ θ) ^ a p := by
  unfold windowModulus
  push_cast
  rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity), ← prod_coe_sort S]
  refine prod_congr rfl fun p _ => ?_
  simp only [keyExt, dif_pos p.2]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), mul_comm]

/-- **All windows.**  `‖Σ_{P_S ≤ n < N} e(k R(n)/Q(n))‖ ≤ C_k (2N)^{|S| θ}`. -/
theorem norm_sum_superPhase_le (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty) {k : ℕ}
    (hk : 0 < k) (N : ℕ) :
    ‖∑ n ∈ Ico (∏ p ∈ S, p) N, superPhase S k n‖ ≤
      superGlobalConst S k * ((2 * N : ℕ) : ℝ) ^ (S.card * savingExponent S.card) := by
  have hr : 1 ≤ S.card := Finset.card_pos.mpr hne
  set θ := savingExponent S.card with hθ
  have hθ0 : 0 < θ := savingExponent_pos hr
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : Ico (∏ p ∈ S, p) 0 = ∅ := Ico_eq_empty_of_le (Nat.zero_le _)
    rw [h0, sum_empty, norm_zero]
    exact mul_nonneg (superGlobalConst_nonneg hS hne k) (Real.rpow_nonneg (by positivity) _)
  have hmaps : ∀ n ∈ Ico (∏ p ∈ S, p) N, windowKey S n ∈
      Fintype.piFinset (fun p : S => range (Nat.log p (2 * N) + 1)) := by
    intro n hn
    rw [mem_Ico] at hn
    rw [Fintype.mem_piFinset]
    intro p
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (by omega)))
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hρ : ∀ p : S, 1 < (p : ℝ) ^ θ := fun p =>
    Real.one_lt_rpow (by exact_mod_cast (hS p p.2).1.one_lt) hθ0
  have hW0 : 0 ≤ windowConst S k := by unfold windowConst savingConst; positivity
  have hA : ∀ p : S, ((p : ℝ) ^ θ) ^ Nat.log p (2 * N) ≤ ((2 * N : ℕ) : ℝ) ^ θ := by
    intro p
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul
      (by positivity), Real.rpow_natCast]
    gcongr
    exact_mod_cast Nat.pow_log_le_self p (by omega)
  calc ‖∑ a ∈ Fintype.piFinset (fun p : S => range (Nat.log p (2 * N) + 1)),
        ∑ n ∈ Ico (∏ p ∈ S, p) N with windowKey S n = a, superPhase S k n‖
      ≤ ∑ a ∈ Fintype.piFinset (fun p : S => range (Nat.log p (2 * N) + 1)),
          windowConst S k * (windowModulus S (keyExt S a) : ℝ) ^ θ :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_fiber_le hS hne hk N a)
    _ = windowConst S k * ∏ p : S, ∑ x ∈ range (Nat.log p (2 * N) + 1), ((p : ℝ) ^ θ) ^ x := by
        rw [← mul_sum, prod_univ_sum]
        congr 1
        exact sum_congr rfl fun a _ => rpow_windowModulus_keyExt a θ
    _ ≤ windowConst S k * ∏ p : S, (((p : ℝ) ^ θ) ^ (Nat.log p (2 * N) + 1) /
          ((p : ℝ) ^ θ - 1)) := by
        gcongr with p _
        exact StonehamPairDrift.sum_range_pow_le (hρ p) _
    _ = windowConst S k * ((∏ p : S, ((p : ℝ) ^ θ / ((p : ℝ) ^ θ - 1))) *
          ∏ p : S, ((p : ℝ) ^ θ) ^ Nat.log p (2 * N)) := by
        rw [← prod_mul_distrib]
        congr 1
        refine prod_congr rfl fun p _ => ?_
        rw [pow_succ]
        ring
    _ ≤ windowConst S k * ((∏ p : S, ((p : ℝ) ^ θ / ((p : ℝ) ^ θ - 1))) *
          ∏ _p : S, ((2 * N : ℕ) : ℝ) ^ θ) := by
        have hpos : ∀ p : S, 0 < (p : ℝ) ^ θ - 1 := fun p => by linarith [hρ p]
        gcongr with p _
        · exact prod_nonneg fun p _ => div_nonneg (by positivity) (hpos p).le
        · exact hA p
    _ = superGlobalConst S k * ((2 * N : ℕ) : ℝ) ^ (S.card * θ) := by
        rw [superGlobalConst, ← prod_coe_sort S (fun p => (p : ℝ) ^ θ / ((p : ℝ) ^ θ - 1)),
          prod_const, card_univ, Fintype.card_coe, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity), mul_comm θ]
        ring

/-! ### Weyl sums, equidistribution and the parity drift -/

theorem card_mul_savingExponent_lt_one {r : ℕ} (hr : 1 ≤ r) : (r : ℝ) * savingExponent r < 1 := by
  unfold savingExponent
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have ha : (0 : ℝ) < (1 / 2) ^ r := by positivity
  rw [mul_sub, mul_one_div_cancel hr'.ne']
  have : 0 < (r : ℝ) * ((1 / 2 : ℝ) ^ r / (r * (r + 1))) := by positivity
  linarith

theorem tendsto_inv_mul_rpow_zero {e : ℝ} (he : e < 1) (C₁ C₂ : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (C₁ + C₂ * ((2 * N : ℕ) : ℝ) ^ e)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - e))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (h2.const_mul C₁).add (h1.const_mul (C₂ * 2 ^ e))
  rw [mul_zero, mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e1 : ((2 * N : ℕ) : ℝ) ^ e = 2 ^ e * (N : ℝ) ^ e := by
    push_cast; exact Real.mul_rpow (by norm_num) hN'.le
  have e2 : (N : ℝ) ^ (-(1 - e)) = (N : ℝ) ^ e / N := by
    rw [show -(1 - e) = e - 1 by ring, Real.rpow_sub_one hN'.ne']
  rw [e1, e2]
  field_simp

/-- The orbit `yₙ = 4ⁿ x_S`. -/
noncomputable def superOrbit (S : Finset ℕ) (n : ℕ) : ℝ := 4 ^ n * superStoneham S

theorem tendsto_superPhase_average (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty) {k : ℕ}
    (hk : 0 < k) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, superPhase S k n) atTop (𝓝 0) := by
  have hr : 1 ≤ S.card := Finset.card_pos.mpr hne
  refine squeeze_zero_norm' ?_ (tendsto_inv_mul_rpow_zero (card_mul_savingExponent_lt_one hr)
    (∏ p ∈ S, p : ℕ) (superGlobalConst S k))
  filter_upwards [eventually_ge_atTop (∏ p ∈ S, p)] with N hN
  rw [← sum_range_add_sum_Ico _ hN, norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_superPhase_le hS hne hk N))
  refine (norm_sum_le _ _).trans ?_
  simp [superPhase, norm_ephase]

theorem tendsto_weylSum_superOrbit_nat (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty)
    {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * superOrbit S n)) atTop (𝓝 0) := by
  have herr : Tendsto (fun n : ℕ =>
      ‖Complex.exp (2 * Real.pi * Complex.I * k * superOrbit S n) - superPhase S k n‖) atTop
      (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi * k * ∑ p ∈ S, (p : ℝ)))
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact norm_exp_sub_superPhase_le hS k hn
  have hces := herr.cesaro
  have hE : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      (Complex.exp (2 * Real.pi * Complex.I * k * superOrbit S n) - superPhase S k n)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) hces
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    exact norm_sum_le _ _
  have h := (tendsto_superPhase_average hS hne hk).add hE
  rw [add_zero] at h
  refine h.congr fun N => ?_
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun n _ => by ring

/-- **The Weyl sums of `4ⁿ x_S` vanish on average** for every frequency `k ≠ 0`. -/
theorem tendsto_weylSum_superOrbit (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty) (k : ℤ)
    (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * superOrbit S n)) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨k.natAbs, by omega⟩
    have hm0 : 0 < m := by omega
    have h := (Complex.continuous_conj.tendsto 0).comp (tendsto_weylSum_superOrbit_nat hS hne hm0)
    rw [map_zero] at h
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, map_mul, map_inv₀, Complex.conj_natCast, map_sum]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [← Complex.exp_conj, hm]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.natAbs, by omega⟩
    have hm0 : 0 < m := by omega
    simpa using tendsto_weylSum_superOrbit_nat hS hne hm0

/-- **Equidistribution.**  For every finite nonempty set `S` of odd primes and `0 < a ≤ b < 1`,
the proportion of `n < N` with `{4ⁿ x_S} ∈ [a, b)` tends to `b − a`. -/
theorem tendsto_card_fract_superOrbit (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Tendsto (fun N : ℕ => (#{n ∈ range N | Int.fract (superOrbit S n) ∈ Set.Ico a b} : ℝ) / N)
      atTop (𝓝 (b - a)) :=
  tendsto_card_fract_mem_Ico (superOrbit S) (tendsto_weylSum_superOrbit hS hne) ha hab hb

theorem drift_superStoneham_eq (N : ℕ) :
    (drift (superStoneham S) N : ℝ) =
      (#{n ∈ range N | Int.fract (superOrbit S n) ∈ Set.Ico (1 / 2 : ℝ) (3 / 4)} : ℝ) -
        #{n ∈ range N | Int.fract (superOrbit S n) ∈ Set.Ico (1 / 4 : ℝ) (1 / 2)} := by
  have hpt : ∀ n ∈ range N, ((digitWeight (quatDigit (superStoneham S) (n + 1)) : ℤ) : ℝ) =
      (if Int.fract (superOrbit S n) ∈ Set.Ico (1 / 2 : ℝ) (3 / 4) then 1 else 0) -
        (if Int.fract (superOrbit S n) ∈ Set.Ico (1 / 4 : ℝ) (1 / 2) then 1 else 0) := by
    intro n _
    rw [quatDigit_succ_eq_floor_fract]
    exact StonehamPairDrift.digitWeight_floor_four_mul _
  rw [drift_eq_sum_digitWeight, Int.cast_sum, sum_congr rfl hpt, sum_sub_distrib, card_filter,
    card_filter]
  push_cast
  rfl

/-- **The parity drift of every finite Stoneham superposition is `o(N)`.** -/
theorem tendsto_drift_superStoneham (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hne : S.Nonempty) :
    Tendsto (fun N : ℕ => (drift (superStoneham S) N : ℝ) / N) atTop (𝓝 0) := by
  have h2 := tendsto_card_fract_superOrbit hS hne (a := 1 / 2) (b := 3 / 4) (by norm_num)
    (by norm_num) (by norm_num)
  have h1 := tendsto_card_fract_superOrbit hS hne (a := 1 / 4) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  have h := h2.sub h1
  rw [show (3 / 4 : ℝ) - 1 / 2 - (1 / 2 - 1 / 4) = 0 by norm_num] at h
  refine h.congr fun N => ?_
  rw [drift_superStoneham_eq, sub_div]

/-- **The parity-drift hypothesis fails for `Σ_{p∈S} α_{2,p}`**, for every finite nonempty set `S`
of odd primes. -/
theorem not_parityDriftHypothesis_superStoneham (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (hne : S.Nonempty) : ¬ ParityDriftHypothesis (superStoneham S) :=
  fun h => h (tendsto_drift_superStoneham hS hne)

end GaloisForLFunctions.HTGeometry.StonehamSuperposition
