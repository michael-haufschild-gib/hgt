import GaloisForLFunctions.FamilyContinuationTheory.MoebiusSignedGaussPairingsEndAtThreeFifths

/-!
# The Gauss pairings meet the sign line only at the Euclidean signatures

A Möbius-signed Gauss pairing of period `k` completes a monomial of Gauss sums at the price
`c = Σ_{i ∈ A} (1/2 − 1/m_i) k + d (k/2 − 1)` (`MoebiusGaussPairing.pairingC`). The sign line of the
tensor-power programme prices a period-`k` frame at `k/2`. This module compares the two.

The nonquadratic characters `S` of a Möbius-signed tuple carry the **signature weight**
`Σ_{x ∈ S} (1/2 − 1/ord x)` (`signatureWeight`), and `c ≥ k · weight`. Möbius parity forces
`S.prod = 1` for odd `#S` and `S.prod = ε`, the involution, for even `#S`. Appending `ε` when
`#S` is even makes `S` the signature `(m₁, …, m_n)` of a sphere orbifold with `n` odd; for
`n = 3` the weight is `1/2 + (1 − Σ 1/m_i)`, one half plus the normalized area of the triangle.

* **The dichotomy** (`signatureWeight_dichotomy`): the weight is `1/2` exactly at the Euclidean
  signatures `(3, 3, 3)`, `(2, 3, 6)`, `(2, 4, 4)`, where every order lies in `{3, 4, 6}`, and is
  at least `7/10` otherwise. Two characters with product `ε` have orders `{3, 6}`, `{4, 4}` or
  `1/a + 1/b ≤ 3/10` (`pair_signature`); three with product `1` are `(3, 3, 3)` or have
  `Σ 1/m ≤ 3/4` (`triple_signature`); four with product `ε` are not all cubic. The gap `1/5` is
  attained by `(2, 5, 10)` (`exists_zmod_eleven_pairing`).
* **Never below the sign line** (`half_period_le_pairingC`): `c ≥ k/2` for every pairing over a
  group with one involution, so no Gauss pairing is a better lever than the sign lever of its period
  (`signCentre_le_coupledBarrier`). Over `𝔽_p` this is the Stickelberger bound
  `Stickelberger.half_mul_period_le_pairingC`; here it follows from the signature alone and comes
  with its equality cases.
* **On the sign line only at the crystallographic periods** (`period_mem_of_pairingC_eq_half`):
  `c = k/2` forces `k ∈ {3, 4, 6}`; a pairing priced below `7k/10`, or with coupled barrier below
  `7/10`, has Euclidean signature (`euclidean_of_pairingC_lt`, `euclidean_of_coupledBarrier_lt`).

So a sign lever of period `5` or of period `k ≥ 7` is never a Gauss pairing
(`half_period_lt_pairingC`): the completion N2 of the programme needs a source outside the Gauss
family, and every Gauss completion of a hyperbolic signature pays at least `k/5` above the sign line.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.TensorPowerProgramme

open FamilyContinuationTheory

variable {G : Type*} [CommGroup G]

/-- The signature weight `Σ_{x ∈ S} (1/2 − 1/ord x)`. -/
def signatureWeight (S : List G) : ℝ := (S.map fun x => 1 / 2 - 1 / (orderOf x : ℝ)).sum

theorem signatureWeight_cons (x : G) (S : List G) :
    signatureWeight (x :: S) = (1 / 2 - 1 / (orderOf x : ℝ)) + signatureWeight S := by
  simp only [signatureWeight, List.map_cons, List.sum_cons]

theorem signatureWeight_nil : signatureWeight ([] : List G) = 0 := by
  simp only [signatureWeight, List.map_nil, List.sum_nil]

theorem one_div_natCast_le {m n : ℕ} (hn : 0 < n) (h : n ≤ m) : 1 / (m : ℝ) ≤ 1 / n :=
  one_div_le_one_div_of_le (by exact_mod_cast hn) (by exact_mod_cast h)

/-- Each character of order at least three weighs at least `1/6`. -/
theorem length_div_six_le_signatureWeight {S : List G} (hS : ∀ x ∈ S, 3 ≤ orderOf x) :
    (S.length : ℝ) / 6 ≤ signatureWeight S := by
  induction S with
  | nil => simp [signatureWeight_nil]
  | cons x S ih =>
    rw [signatureWeight_cons, List.length_cons, Nat.cast_succ]
    have h1 := one_div_natCast_le (by norm_num) (hS x List.mem_cons_self)
    have := ih fun y hy => hS y (List.mem_cons_of_mem _ hy)
    push_cast at h1
    linarith

/-- A character of order at least four weighs at least `1/4 = 1/6 + 1/12`. -/
theorem length_div_six_add_le_signatureWeight {S : List G} (hS : ∀ x ∈ S, 3 ≤ orderOf x)
    {y : G} (hy : y ∈ S) (hy4 : 4 ≤ orderOf y) :
    (S.length : ℝ) / 6 + 1 / 12 ≤ signatureWeight S := by
  induction S with
  | nil => simp at hy
  | cons x S ih =>
    rw [signatureWeight_cons, List.length_cons, Nat.cast_succ]
    have hS' : ∀ z ∈ S, 3 ≤ orderOf z := fun z hz => hS z (List.mem_cons_of_mem _ hz)
    rcases List.mem_cons.mp hy with rfl | hyS
    · have h1 := one_div_natCast_le (by norm_num) hy4
      have := length_div_six_le_signatureWeight hS'
      push_cast at h1
      linarith
    · have h1 := one_div_natCast_le (by norm_num) (hS x List.mem_cons_self)
      have := ih hS' hyS
      push_cast at h1
      linarith

/-! ### Two characters with product the involution -/

/-- The arithmetic of the orders `a ≤ 6`, `b` of two characters with product the involution. -/
theorem pair_orders_aux {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (h6 : a ≤ 6)
    (F1 : a ∣ Nat.lcm 2 b) (F2 : b ∣ Nat.lcm 2 a) (F3 : 2 ∣ a ∨ 2 ∣ b) (F4 : a = 6 → b = 3) :
    (a = 3 ∧ b = 6) ∨ (a = 4 ∧ b = 4) ∨ (a = 5 ∧ b = 10) ∨ (a = 6 ∧ b = 3) := by
  have hb12 : b ≤ 12 := by
    have h1 := Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (by omega)) F2
    have h2 := Nat.le_of_dvd (by omega) (Nat.lcm_dvd_mul 2 a)
    omega
  interval_cases a <;> interval_cases b <;> revert F1 F2 F3 F4 <;> norm_num [Nat.lcm]

/-- **Two characters with product the involution.** Their orders are `{3, 6}` or `{4, 4}`, or
`1/a + 1/b ≤ 3/10`. -/
theorem pair_signature (hG : HasUniqueOrderTwo G) {x y : G} (hx : 3 ≤ orderOf x)
    (hy : 3 ≤ orderOf y) (hq : orderOf (x * y) = 2) :
    ((orderOf x = 3 ∧ orderOf y = 6) ∨ (orderOf x = 4 ∧ orderOf y = 4) ∨
        (orderOf x = 6 ∧ orderOf y = 3)) ∨
      1 / (orderOf x : ℝ) + 1 / (orderOf y : ℝ) ≤ 3 / 10 := by
  have F1 : orderOf x ∣ Nat.lcm 2 (orderOf y) := by
    have h := (Commute.all (x * y) y⁻¹).orderOf_mul_dvd_lcm
    rwa [orderOf_inv, hq, mul_inv_cancel_right] at h
  have F2 : orderOf y ∣ Nat.lcm 2 (orderOf x) := by
    have h := (Commute.all x⁻¹ (x * y)).orderOf_mul_dvd_lcm
    rwa [orderOf_inv, hq, Nat.lcm_comm, inv_mul_cancel_left] at h
  have F3 : 2 ∣ orderOf x ∨ 2 ∣ orderOf y := by
    have h := (Commute.all x y).orderOf_mul_dvd_lcm
    rw [hq] at h
    exact (Nat.Prime.dvd_mul Nat.prime_two).mp (h.trans (Nat.lcm_dvd_mul _ _))
  -- an order-6 character squares to the other one, of order 3
  have F4 : ∀ {u v : G}, u * v = x * y → orderOf u = 6 → orderOf v = 3 := by
    intro u v huv hu
    have hu3 : orderOf (u ^ 3) = 2 := by
      rw [orderOf_pow' u (by norm_num), hu]
      norm_num
    have hq3 : u ^ 3 = x * y := hG hu3 hq
    have hv : v = u ^ 2 := by
      have h : u * v = u * u ^ 2 := by
        rw [huv, ← hq3]
        exact pow_succ' u 2
      exact mul_left_cancel h
    rw [hv, orderOf_pow' u (by norm_num), hu]
    norm_num
  by_cases hxs : orderOf x ≤ 6
  · rcases pair_orders_aux hx hy hxs F1 F2 F3 (F4 rfl) with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · right
      rw [h.1, h.2]
      norm_num
    · exact Or.inl (Or.inr (Or.inr h))
  · by_cases hys : orderOf y ≤ 6
    · rcases pair_orders_aux hy hx hys F2 F1 F3.symm (F4 (mul_comm y x)) with h | h | h | h
      · exact Or.inl (Or.inr (Or.inr ⟨h.2, h.1⟩))
      · exact Or.inl (Or.inr (Or.inl ⟨h.2, h.1⟩))
      · right
        rw [h.1, h.2]
        norm_num
      · exact Or.inl (Or.inl ⟨h.2, h.1⟩)
    · right
      have h1 := one_div_natCast_le (by norm_num : 0 < 7) (by omega : 7 ≤ orderOf x)
      have h2 := one_div_natCast_le (by norm_num : 0 < 7) (by omega : 7 ≤ orderOf y)
      push_cast at h1 h2
      linarith

/-! ### Three characters with product one -/

/-- The arithmetic of the orders of three characters with product one. -/
theorem triple_orders_aux {a b c : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (Fa : a ∣ Nat.lcm b c) (Fb : b ∣ Nat.lcm a c) (Fc : c ∣ Nat.lcm a b) :
    (a = 3 ∧ b = 3 ∧ c = 3) ∨ 1 / (a : ℝ) + 1 / b + 1 / c ≤ 3 / 4 := by
  have h3 : ∀ {u v : ℕ}, 3 ∣ Nat.lcm u v → 3 ∣ u ∨ 3 ∣ v := fun h =>
    (Nat.Prime.dvd_mul (by norm_num)).mp (h.trans (Nat.lcm_dvd_mul _ _))
  have r3 : ∀ {n : ℕ}, 3 ≤ n → 1 / (n : ℝ) ≤ 1 / 3 := fun h => by
    have := one_div_natCast_le (by norm_num) h; push_cast at this; exact this
  have r4 : ∀ {n : ℕ}, 4 ≤ n → 1 / (n : ℝ) ≤ 1 / 4 := fun h => by
    have := one_div_natCast_le (by norm_num) h; push_cast at this; exact this
  have r6 : ∀ {n : ℕ}, 6 ≤ n → 1 / (n : ℝ) ≤ 1 / 6 := fun h => by
    have := one_div_natCast_le (by norm_num) h; push_cast at this; exact this
  -- two orders equal to three force the third
  have two3 : ∀ {u v w : ℕ}, u = 3 → v = 3 → 3 ≤ w → w ∣ Nat.lcm u v → w = 3 := by
    intro u v w hu hv hw h
    rw [hu, hv, Nat.lcm_self] at h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  by_cases hA : a = 3 <;> by_cases hB : b = 3 <;> by_cases hC : c = 3
  · exact Or.inl ⟨hA, hB, hC⟩
  · exact absurd (two3 hA hB hc Fc) hC
  · exact absurd (two3 hA hC hb Fb) hB
  · right
    rcases h3 (hA ▸ Fa) with h | h
    · have := r6 (show 6 ≤ b by omega); have := r4 (show 4 ≤ c by omega); have := r3 ha; linarith
    · have := r6 (show 6 ≤ c by omega); have := r4 (show 4 ≤ b by omega); have := r3 ha; linarith
  · exact absurd (two3 hB hC ha Fa) hA
  · right
    rcases h3 (hB ▸ Fb) with h | h
    · have := r6 (show 6 ≤ a by omega); have := r4 (show 4 ≤ c by omega); have := r3 hb; linarith
    · have := r6 (show 6 ≤ c by omega); have := r4 (show 4 ≤ a by omega); have := r3 hb; linarith
  · right
    rcases h3 (hC ▸ Fc) with h | h
    · have := r6 (show 6 ≤ a by omega); have := r4 (show 4 ≤ b by omega); have := r3 hc; linarith
    · have := r6 (show 6 ≤ b by omega); have := r4 (show 4 ≤ a by omega); have := r3 hc; linarith
  · right
    have := r4 (show 4 ≤ a by omega); have := r4 (show 4 ≤ b by omega)
    have := r4 (show 4 ≤ c by omega)
    linarith

theorem orderOf_dvd_lcm_of_mul_mul_eq_one {x y z : G} (h : x * (y * z) = 1) :
    orderOf x ∣ Nat.lcm (orderOf y) (orderOf z) := by
  rw [eq_inv_of_mul_eq_one_left h, orderOf_inv]
  exact (Commute.all y z).orderOf_mul_dvd_lcm

/-- **Three characters with product one** are `(3, 3, 3)` or have `Σ 1/m ≤ 3/4`. -/
theorem triple_signature {x y z : G} (hx : 3 ≤ orderOf x) (hy : 3 ≤ orderOf y)
    (hz : 3 ≤ orderOf z) (h : x * (y * z) = 1) :
    (orderOf x = 3 ∧ orderOf y = 3 ∧ orderOf z = 3) ∨
      1 / (orderOf x : ℝ) + 1 / (orderOf y : ℝ) + 1 / (orderOf z : ℝ) ≤ 3 / 4 := by
  have hy' : y * (x * z) = 1 := by rw [mul_left_comm, h]
  have hz' : z * (x * y) = 1 := by rw [mul_comm, mul_assoc, h]
  exact triple_orders_aux hx hy hz (orderOf_dvd_lcm_of_mul_mul_eq_one h)
    (orderOf_dvd_lcm_of_mul_mul_eq_one hy') (orderOf_dvd_lcm_of_mul_mul_eq_one hz')

/-! ### The dichotomy of signatures -/

/-- **The signature dichotomy.** The nonquadratic part of a Möbius-signed tuple has weight `1/2`
with every order in `{3, 4, 6}` (the Euclidean signatures), or weight at least `7/10`. -/
theorem signatureWeight_dichotomy (hG : HasUniqueOrderTwo G) {L : List G}
    (hL : IsMoebiusSignedTuple L) :
    (signatureWeight (nonQuadraticPart L) = 1 / 2 ∧
        ∀ x ∈ nonQuadraticPart L, orderOf x = 3 ∨ orderOf x = 4 ∨ orderOf x = 6) ∨
      7 / 10 ≤ signatureWeight (nonQuadraticPart L) := by
  obtain ⟨hsq, hpar⟩ := nonQuadraticPart_moebius_parity hG hL
  have hlen := two_le_length_nonQuadraticPart hG hL
  have h3 : ∀ x ∈ nonQuadraticPart L, 3 ≤ orderOf x := fun x hx =>
    three_le_orderOf_mem_nonQuadraticPart hx
  generalize nonQuadraticPart L = S at hsq hpar hlen h3 ⊢
  rcases S with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, _ | ⟨v, T⟩⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · -- two characters: product the involution
    have hne : x * y ≠ 1 := by
      rcases hpar with ⟨_, hodd⟩ | ⟨hne, _⟩
      · exact absurd hodd (by simp only [List.length_cons, List.length_nil]; decide)
      · simpa using hne
    have hq : orderOf (x * y) = 2 := orderOf_eq_prime (by simpa using hsq) hne
    have hx := h3 x (by simp)
    have hy := h3 y (by simp)
    simp only [signatureWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rcases pair_signature hG hx hy hq with (h | h | h) | h
    · left
      refine ⟨by rw [h.1, h.2]; norm_num, fun u hu => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    · left
      refine ⟨by rw [h.1, h.2]; norm_num, fun u hu => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    · left
      refine ⟨by rw [h.1, h.2]; norm_num, fun u hu => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    · right
      linarith
  · -- three characters: product one
    have h1 : x * (y * z) = 1 := by
      rcases hpar with ⟨h1, _⟩ | ⟨_, hev⟩
      · simpa using h1
      · exact absurd hev (by simp only [List.length_cons, List.length_nil]; decide)
    have hx := h3 x (by simp)
    have hy := h3 y (by simp)
    have hz := h3 z (by simp)
    simp only [signatureWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rcases triple_signature hx hy hz h1 with h | h
    · left
      refine ⟨by rw [h.1, h.2.1, h.2.2]; norm_num, fun u hu => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> omega
    · right
      linarith
  · -- four characters: product the involution, so not all of order three
    right
    have hne : x * (y * (z * w)) ≠ 1 := by
      rcases hpar with ⟨_, hodd⟩ | ⟨hne, _⟩
      · exact absurd hodd (by simp only [List.length_cons, List.length_nil]; decide)
      · simpa using hne
    have hsq' : (x * (y * (z * w))) ^ 2 = 1 := by simpa using hsq
    have hex : ∃ u ∈ [x, y, z, w], 4 ≤ orderOf u := by
      by_contra hno
      simp only [not_exists, not_and, not_le] at hno
      have e : ∀ u ∈ [x, y, z, w], u ^ 3 = 1 := fun u hu => by
        have h3u := h3 u hu
        have h4u := hno u hu
        have hu3 : orderOf u = 3 := by omega
        rw [← hu3]
        exact pow_orderOf_eq_one u
      apply hne
      have hcube : (x * (y * (z * w))) ^ 3 = 1 := by
        rw [mul_pow, mul_pow, mul_pow, e x (by simp), e y (by simp), e z (by simp), e w (by simp)]
        simp
      have hp : (x * (y * (z * w))) ^ 3 = (x * (y * (z * w))) ^ 2 * (x * (y * (z * w))) :=
        pow_succ _ 2
      rw [hp, hsq', one_mul] at hcube
      exact hcube
    obtain ⟨u, hu, hu4⟩ := hex
    have := length_div_six_add_le_signatureWeight h3 hu hu4
    simp only [List.length_cons, List.length_nil] at this
    push_cast at this
    linarith
  · -- five or more characters
    right
    have := length_div_six_le_signatureWeight h3
    simp only [List.length_cons] at this
    push_cast at this
    have hT : (0 : ℝ) ≤ T.length := Nat.cast_nonneg _
    linarith

/-! ### Gauss pairings and the sign line -/

/-- The price dominates the period times the signature weight. -/
theorem signatureWeight_mul_period_le_pairingC (hG : HasUniqueOrderTwo G)
    (P : MoebiusGaussPairing G) :
    signatureWeight (nonQuadraticPart (P.compChars ++ P.rowChars)) * (P.period : ℝ) ≤
      P.pairingC :=
  P.alpha_sum_mul_period_le_pairingC hG

/-- **Gauss pairings never go below the sign line**: `c ≥ k/2`. -/
theorem half_period_le_pairingC (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    (P.period : ℝ) / 2 ≤ P.pairingC := by
  have h := signatureWeight_mul_period_le_pairingC hG P
  have hk : (0 : ℝ) ≤ P.period := Nat.cast_nonneg _
  rcases signatureWeight_dichotomy hG P.moebius with ⟨hw, _⟩ | hw
  · rw [hw] at h
    linarith
  · nlinarith

/-- **A pairing priced below `7k/10` has Euclidean signature.** -/
theorem euclidean_of_pairingC_lt (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G)
    (h : P.pairingC < 7 / 10 * (P.period : ℝ)) :
    signatureWeight (nonQuadraticPart (P.compChars ++ P.rowChars)) = 1 / 2 ∧
      ∀ x ∈ nonQuadraticPart (P.compChars ++ P.rowChars),
        orderOf x = 3 ∨ orderOf x = 4 ∨ orderOf x = 6 := by
  rcases signatureWeight_dichotomy hG P.moebius with h1 | hw
  · exact h1
  · have hle := signatureWeight_mul_period_le_pairingC hG P
    have hk : (0 : ℝ) ≤ P.period := Nat.cast_nonneg _
    nlinarith

/-- **On the sign line only at the crystallographic periods**: `c = k/2` forces `k ∈ {3, 4, 6}`. -/
theorem period_mem_of_pairingC_eq_half (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G)
    (h : P.pairingC = (P.period : ℝ) / 2) :
    P.period = 3 ∨ P.period = 4 ∨ P.period = 6 := by
  have hk3 := P.three_le_period hG
  have hk3r : (3 : ℝ) ≤ P.period := by exact_mod_cast hk3
  have h23 := P.two_thirds_mul_period_sub_one_le_pairingC hG
  have hk6 : P.period ≤ 6 := by
    have : (P.period : ℝ) ≤ 6 := by linarith
    exact_mod_cast this
  obtain ⟨_, hord⟩ := euclidean_of_pairingC_lt hG P (by rw [h]; linarith)
  have hlen := two_le_length_nonQuadraticPart hG P.moebius
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (nonQuadraticPart (P.compChars ++ P.rowChars))
    (fun h0 => by rw [h0] at hlen; simp at hlen)
  have hx' : x ∈ P.compChars ++ P.rowChars := by
    simp only [nonQuadraticPart, List.mem_filter] at hx
    exact hx.1
  have hdvd := P.orderOf_dvd_period hx'
  generalize P.period = k at hk3 hk6 hdvd ⊢
  interval_cases k <;> rcases hord x hx with h' | h' | h' <;> rw [h'] at hdvd <;> omega

/-- **No Gauss sign lever off the crystallographic periods**: `c > k/2` unless `k ∈ {3, 4, 6}`;
in particular at period `5` and at every period `k ≥ 7`. -/
theorem half_period_lt_pairingC (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G)
    (hk : P.period ≠ 3 ∧ P.period ≠ 4 ∧ P.period ≠ 6) : (P.period : ℝ) / 2 < P.pairingC := by
  refine lt_of_le_of_ne (half_period_le_pairingC hG P) fun h => ?_
  rcases period_mem_of_pairingC_eq_half hG P h.symm with h' | h' | h'
  · exact hk.1 h'
  · exact hk.2.1 h'
  · exact hk.2.2 h'

/-- **No Gauss pairing beats the sign lever of its period**: the coupled barrier `c/(k − 1)` is at
least the sign centre `k/(2(k − 1))`. -/
theorem signCentre_le_coupledBarrier (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G) :
    (P.period : ℝ) / (2 * ((P.period : ℝ) - 1)) ≤ P.coupledBarrier := by
  have hk : (3 : ℝ) ≤ P.period := by exact_mod_cast P.three_le_period hG
  have hc := half_period_le_pairingC hG P
  rw [MoebiusGaussPairing.coupledBarrier, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **A coupled barrier below `7/10` needs a Euclidean signature.** -/
theorem euclidean_of_coupledBarrier_lt (hG : HasUniqueOrderTwo G) (P : MoebiusGaussPairing G)
    (h : P.coupledBarrier < 7 / 10) :
    signatureWeight (nonQuadraticPart (P.compChars ++ P.rowChars)) = 1 / 2 ∧
      ∀ x ∈ nonQuadraticPart (P.compChars ++ P.rowChars),
        orderOf x = 3 ∨ orderOf x = 4 ∨ orderOf x = 6 := by
  have hk : (3 : ℝ) ≤ P.period := by exact_mod_cast P.three_le_period hG
  rw [MoebiusGaussPairing.coupledBarrier, div_lt_iff₀ (by linarith)] at h
  exact euclidean_of_pairingC_lt hG P (by linarith)

/-- **The gap `1/5` is attained.** On `ZMod 11` the pair `(φ², φ³)`, `φ` of order `10`, has
signature `(2, 5, 10)`, weight `7/10` and price `7 = 7k/10` at period `10`. -/
theorem exists_zmod_eleven_pairing :
    ∃ P : MoebiusGaussPairing (MulChar (ZMod 11) ℂ),
      P.period = 10 ∧ P.pairingC = 7 ∧
        signatureWeight (nonQuadraticPart (P.compChars ++ P.rowChars)) = 7 / 10 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hexp_ne : Monoid.exponent (ZMod 11)ˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod 11)ˣ) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp (Monoid.exponent (ZMod 11)ˣ) hexp_ne⟩,
      rootsOfUnity.isCyclic _ _⟩
  obtain ⟨e⟩ := MulChar.mulEquiv_units (ZMod 11) ℂ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod 11)ˣ)
  have hcard_u : Fintype.card (ZMod 11)ˣ = 10 := by
    rw [Fintype.card_units, ZMod.card 11]
  have hord_g : orderOf g = 10 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_u]
  let φ : MulChar (ZMod 11) ℂ := e.symm g
  have hord_φ : orderOf φ = 10 := by rw [MulEquiv.orderOf_eq, hord_g]
  let χ : MulChar (ZMod 11) ℂ := φ ^ 2
  let ψ : MulChar (ZMod 11) ℂ := φ ^ 3
  have hχ : orderOf χ = 5 := by
    rw [orderOf_pow' φ two_ne_zero, hord_φ]
    norm_num
  have hψ : orderOf ψ = 10 := by
    rw [orderOf_pow' φ (by norm_num), hord_φ]
    norm_num
  have hprod : χ * ψ = φ ^ 5 := by
    change φ ^ 2 * φ ^ 3 = φ ^ 5
    rw [← pow_add]
  have hord_prod : orderOf (χ * ψ) = 2 := by
    rw [hprod, orderOf_pow' φ (by norm_num), hord_φ]
    norm_num
  have hmoeb : IsMoebiusSignedTuple [χ, ψ] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega
    · simp only [List.prod_cons, List.prod_nil, mul_one]
      exact hord_prod ▸ pow_orderOf_eq_one (χ * ψ)
    · right
      refine ⟨?_, ⟨1, rfl⟩⟩
      simp only [List.prod_cons, List.prod_nil, mul_one]
      intro h1
      rw [h1, orderOf_one] at hord_prod
      omega
  have hlcm : tupleOrderLcm [χ, ψ] = 10 := by
    simp only [tupleOrderLcm, List.foldr_cons, List.foldr_nil, hχ, hψ]
    norm_num
  let P : MoebiusGaussPairing (MulChar (ZMod 11) ℂ) :=
    { compChars := [χ, ψ]
      rowChars := []
      moebius := hmoeb
      period := 10
      period_pos := by norm_num
      lcm_dvd_period := by
        show tupleOrderLcm [χ, ψ] ∣ 10
        rw [hlcm]
      period_eq_of_no_rows := fun _ => by
        show 10 = tupleOrderLcm [χ, ψ]
        rw [hlcm] }
  have hnq : nonQuadraticPart (P.compChars ++ P.rowChars) = [χ, ψ] := by
    show nonQuadraticPart [χ, ψ] = [χ, ψ]
    simp [nonQuadraticPart, hχ, hψ]
  refine ⟨P, rfl, ?_, ?_⟩
  · simp only [P, MoebiusGaussPairing.pairingC, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_nil, hχ, hψ]
    norm_num
  · rw [hnq]
    simp only [signatureWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hχ, hψ]
    norm_num

end GaloisForLFunctions.TensorPowerProgramme
