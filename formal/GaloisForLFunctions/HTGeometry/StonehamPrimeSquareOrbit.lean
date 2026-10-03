import GaloisForLFunctions.HTGeometry.StonehamPrimeDriftLaw

/-!
# Stoneham constants `α_{2,p}` with `p ≡ 7 (mod 8)`

If `4` generates the squares modulo `p` (order `(p − 1)/2`) and `p² ∤ 4^{(p−1)/2} − 1`, the orbit of
`4` modulo `pᵏ` is a full square class.  For `p ≡ 3 (mod 4)` the class and its negative exhaust the
units, which again gives

`2 Σ_{i<φ(pᵏ)/2} G(a4ⁱ mod pᵏ) = Σ_{units r} G(r) + χ(a) Σ_{units r} χ(r) G(r)`

(`two_mul_sum_four_orbit_of_order`).  For `p ≡ 7 (mod 8)` the doubling argument gives
`S(1/4) = S(1/2)`, every period carries zero drift, and the parity drift of `α_p` vanishes at every
window end (`drift_stonehamP_windowEnd_of_mod_eight_eq_seven`), e.g. for `p = 7, 23, 47`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.StonehamPrimeDrift

open BinaryParityDrift StonehamParityDrift

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Lifting the exponent for a base of order `m` -/

omit hp in
theorem dvd_pow_sub_one_iff_of_order {b m : ℕ} (hm0 : 0 < m) (hb : p ∣ b ^ m - 1)
    (hmin : ∀ d < m, 0 < d → ¬ p ∣ b ^ d - 1) (hb0 : 0 < b) {d : ℕ} :
    p ∣ b ^ d - 1 ↔ m ∣ d := by
  constructor
  · intro h
    have h1 : b ^ d ≡ 1 [MOD p] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hb0)).mpr h).symm
    have hF' : b ^ m ≡ 1 [MOD p] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hb0)).mpr hb).symm
    have hsplit : b ^ d = (b ^ m) ^ (d / m) * b ^ (d % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h2 : b ^ (d % m) ≡ 1 [MOD p] := by
      have := (hF'.pow (d / m)).mul_right (b ^ (d % m))
      rw [one_pow, one_mul, ← hsplit] at this
      exact this.symm.trans h1
    by_contra hdvd
    have hr : 0 < d % m := Nat.pos_of_ne_zero fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
    exact hmin _ (Nat.mod_lt _ hm0) hr
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hb0)).mp h2.symm)
  · rintro ⟨e, rfl⟩
    rw [pow_mul]
    exact hb.trans (by simpa using Nat.sub_one_dvd_pow_sub_one (b ^ m) e)

theorem padicValNat_pow_sub_one_of_order (hp2 : p ≠ 2) {b m : ℕ} (hb : p ∣ b ^ m - 1)
    (hpb : ¬ p ∣ b) (hw : ¬ p ^ 2 ∣ b ^ m - 1) {e : ℕ} (he : e ≠ 0) :
    padicValNat p (b ^ (m * e) - 1) = 1 + padicValNat p e := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hlt : 1 < b ^ m := by
    by_contra h
    have : b ^ m - 1 = 0 := by omega
    exact hw (this ▸ dvd_zero _)
  have hv1 : padicValNat p (b ^ m - 1) = 1 := by
    have hne : b ^ m - 1 ≠ 0 := by omega
    have h1 := (padicValNat_dvd_iff_le (p := p) (n := 1) hne).mp (by rwa [pow_one])
    have h2 : ¬ 2 ≤ padicValNat p (b ^ m - 1) := fun h => hw ((padicValNat_dvd_iff_le hne).mpr h)
    omega
  have hndvd : ¬ p ∣ b ^ m := fun h => hpb (hp.out.dvd_of_dvd_pow h)
  rw [pow_mul]
  have := padicValNat.pow_sub_pow (p := p) (x := b ^ m) (y := 1) hodd hlt (by simpa using hb)
    hndvd he
  rw [one_pow] at this
  rw [this, hv1]

/-- **Lifting the exponent.**  `pᵏ ∣ bᵈ − 1 ⟺ m p^{k−1} ∣ d`. -/
theorem pow_dvd_pow_sub_one_iff_of_order (hp2 : p ≠ 2) {b m : ℕ} (hm0 : 0 < m)
    (hb : p ∣ b ^ m - 1) (hmin : ∀ d < m, 0 < d → ¬ p ∣ b ^ d - 1) (hpb : ¬ p ∣ b)
    (hw : ¬ p ^ 2 ∣ b ^ m - 1) {k : ℕ} (hk : 1 ≤ k) {d : ℕ} :
    p ^ k ∣ b ^ d - 1 ↔ m * p ^ (k - 1) ∣ d := by
  have hb0 : 0 < b := Nat.pos_of_ne_zero fun h => hpb (h ▸ dvd_zero p)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hne : b ^ d - 1 ≠ 0 := by
    intro h
    have hbd : b ^ d = 1 := by have := Nat.one_le_pow d b hb0; omega
    have hb1 : b = 1 := (Nat.pow_eq_one.mp hbd).resolve_right hd.ne'
    subst hb1
    simp at hb
    exact hw (by simp)
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := (dvd_pow_sub_one_iff_of_order hm0 hb hmin hb0).mp
      ((dvd_pow_self p (by omega)).trans h)
    have he : e ≠ 0 := by rintro rfl; simp at hd
    have hv := (padicValNat_dvd_iff_le hne).mp h
    rw [padicValNat_pow_sub_one_of_order hp2 hb hpb hw he] at hv
    exact mul_dvd_mul_left _ ((pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd)
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; simp at hd
    rw [mul_assoc] at hne ⊢
    rw [padicValNat_dvd_iff_le hne,
      padicValNat_pow_sub_one_of_order hp2 hb hpb hw
        (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hc),
      padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hc, padicValNat.prime_pow]
    omega

/-! ### The square class and its negative -/

/-- If `4` has order `(p − 1)/2` modulo `p` and `p² ∤ 4^{(p−1)/2} − 1`, then `4` has period
`(p − 1)/2 · p^{k−1}` modulo every `pᵏ`. -/
theorem fourPeriod_of_order (hp2 : p ≠ 2)
    (h4min : ∀ d < (p - 1) / 2, 0 < d → ¬ p ∣ 4 ^ d - 1) (h4w : ¬ p ^ 2 ∣ 4 ^ ((p - 1) / 2) - 1) :
    FourPeriod p := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have h4m : p ∣ 4 ^ ((p - 1) / 2) - 1 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by omega]
    exact dvd_two_pow_prime_sub_one_sub_one hp2
  have h4p : ¬ p ∣ 4 := fun h => not_dvd_two_pow hp2 2 (by norm_num; exact h)
  intro k hk
  exact (pow_dvd_pow_sub_one_iff_of_order hp2 (by omega) h4m h4min h4p h4w hk).mpr dvd_rfl

/-- **Splitting the units into the square class of `a` and its negative.** -/
theorem two_mul_sum_four_orbit_of_order (hp4 : p % 4 = 3)
    (h4min : ∀ d < (p - 1) / 2, 0 < d → ¬ p ∣ 4 ^ d - 1) (h4w : ¬ p ^ 2 ∣ 4 ^ ((p - 1) / 2) - 1)
    {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (ha : ¬ p ∣ a) (G : ℕ → ℤ) :
    2 * ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)), G (a * 4 ^ i % p ^ k) =
      ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, G r +
        legendreSym p a * ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, legendreSym p r * G r := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hneg : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp4]
  set q := p ^ k with hqdef
  set P := (p - 1) / 2 * p ^ (k - 1) with hPdef
  have hq1 : 1 < q := one_lt_prime_pow hk
  have hq : 0 < q := by omega
  have hper := fourPeriod_of_order hp2 h4min h4w
  have h4m : p ∣ 4 ^ ((p - 1) / 2) - 1 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by omega]
    exact dvd_two_pow_prime_sub_one_sub_one hp2
  have h4p : ¬ p ∣ 4 := fun h => not_dvd_two_pow hp2 2 (by norm_num; exact h)
  have hLTE := fun {d : ℕ} => pow_dvd_pow_sub_one_iff_of_order hp2 (by omega : 0 < (p - 1) / 2)
    h4m h4min h4p h4w hk (d := d)
  -- the two orbit maps
  set fP : ℕ → ℕ := fun i => a * 4 ^ i % q with hfP
  set fN : ℕ → ℕ := fun i => (q - 1) * a * 4 ^ i % q with hfN
  have hcopq : ∀ c, ¬ p ∣ c → Nat.Coprime q c := fun c hc =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hc)
  have hpq1 : ¬ p ∣ q - 1 := by
    intro h
    have h1 : p ∣ q := dvd_pow_self p (by omega)
    have := Nat.dvd_sub h1 h
    rw [show q - (q - 1) = 1 by omega] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)
  have hpow4 : ∀ i, ¬ p ∣ 4 ^ i := fun i h => h4p (hp.out.dvd_of_dvd_pow h)
  have hndP : ∀ i, ¬ p ∣ a * 4 ^ i := fun i h =>
    (hp.out.dvd_mul.mp h).elim ha (hpow4 i)
  have hndN : ∀ i, ¬ p ∣ (q - 1) * a * 4 ^ i := fun i h => by
    rcases hp.out.dvd_mul.mp h with h' | h'
    · exact (hp.out.dvd_mul.mp h').elim hpq1 ha
    · exact hpow4 i h'
  -- injectivity on one period
  have hinj : ∀ (c : ℕ), ¬ p ∣ c → Set.InjOn (fun i => c * 4 ^ i % q) (range P) := by
    intro c hc
    have key : ∀ i j, i < j → j < P → c * 4 ^ i % q = c * 4 ^ j % q → False := by
      intro i j hlt hj hij
      have hle : c * 4 ^ i ≤ c * 4 ^ j :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlt.le)
      have hdvd := (Nat.modEq_iff_dvd' hle).mp hij
      rw [show c * 4 ^ j - c * 4 ^ i = c * 4 ^ i * (4 ^ (j - i) - 1) by
        rw [Nat.mul_sub_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]] at hdvd
      have hc4 : ¬ p ∣ c * 4 ^ i := fun h => (hp.out.dvd_mul.mp h).elim hc (hpow4 i)
      have h2 := (hcopq _ hc4).dvd_of_dvd_mul_left hdvd
      exact absurd (Nat.le_of_dvd (by omega) (hLTE.mp h2)) (by omega)
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  have hinjP : Set.InjOn fP (range P) := hinj a ha
  have hinjN : Set.InjOn fN (range P) := hinj ((q - 1) * a) (fun h =>
    (hp.out.dvd_mul.mp h).elim hpq1 ha)
  -- values of `χ` on the two orbits
  have hχ4 : legendreSym p 4 = 1 := by
    rw [show (4 : ℤ) = 2 * 2 by norm_num, legendreSym.mul]
    have := legendreSym.sq_one p (a := 2) (by
      intro h; have := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h
      have := Int.le_of_dvd (by norm_num) this; omega)
    rw [← sq]; exact this
  have hχpow : ∀ i : ℕ, legendreSym p ((4 ^ i : ℕ) : ℤ) = 1 := by
    intro i; induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, Nat.cast_mul, legendreSym.mul, ih, one_mul]; exact_mod_cast hχ4
  have hchiP : ∀ i, legendreSym p (fP i : ℤ) = legendreSym p a := by
    intro i
    simp only [hfP]
    rw [legendreSym_natCast_mod hk, Nat.cast_mul, legendreSym.mul, hχpow, mul_one]
  have hχq1 : legendreSym p ((q - 1 : ℕ) : ℤ) = -1 := by
    rw [legendreSym_sub_eq (dvd_pow_self p (by omega)) (by omega), hneg, Nat.cast_one,
      legendreSym.at_one]; ring
  have hchiN : ∀ i, legendreSym p (fN i : ℤ) = -legendreSym p a := by
    intro i
    simp only [hfN]
    rw [legendreSym_natCast_mod hk, Nat.cast_mul, Nat.cast_mul, legendreSym.mul, legendreSym.mul,
      hχpow, hχq1]; ring
  have hχa : legendreSym p a ≠ 0 := by
    rw [Ne, legendreSym.eq_zero_iff, Int.cast_natCast, ZMod.natCast_eq_zero_iff]; exact ha
  -- the two images partition the units
  set U := {r ∈ range q | q.Coprime r} with hU
  set SP := (range P).image fP with hSP
  set SN := (range P).image fN with hSN
  have hsub : ∀ c, ¬ p ∣ c → ∀ i, c * 4 ^ i % q ∈ U := by
    intro c hc i
    rw [hU, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ hq, ?_⟩
    rw [Nat.coprime_comm, ZMod.coprime_mod_iff_coprime, Nat.coprime_comm]
    exact hcopq _ (fun h => (hp.out.dvd_mul.mp h).elim hc (hpow4 i))
  have hdisj : Disjoint SP SN := by
    rw [disjoint_left]
    intro r hrP hrN
    obtain ⟨i, _, rfl⟩ := mem_image.mp hrP
    obtain ⟨j, _, hj⟩ := mem_image.mp hrN
    have e : legendreSym p (fN j : ℤ) = legendreSym p (fP i : ℤ) := by rw [hj]
    have h1 := hchiP i
    have h2 := hchiN j
    exact hχa (by linarith)
  have hunion : SP ∪ SN = U := by
    apply eq_of_subset_of_card_le
    · intro r hr
      rcases mem_union.mp hr with h | h
      · obtain ⟨i, _, rfl⟩ := mem_image.mp h; exact hsub a ha i
      · obtain ⟨i, _, rfl⟩ := mem_image.mp h
        exact hsub ((q - 1) * a) (fun h' => (hp.out.dvd_mul.mp h').elim hpq1 ha) i
    · rw [card_union_of_disjoint hdisj, card_image_of_injOn hinjP, card_image_of_injOn hinjN,
        card_range, hU, ← Nat.totient_eq_card_coprime, hqdef, Nat.totient_prime_pow hp.out
          (by omega), hPdef]
      have hv : 2 * ((p - 1) / 2) = p - 1 := by omega
      refine le_of_eq ?_
      calc p ^ (k - 1) * (p - 1) = (2 * ((p - 1) / 2)) * p ^ (k - 1) := by rw [hv, mul_comm]
        _ = (p - 1) / 2 * p ^ (k - 1) + (p - 1) / 2 * p ^ (k - 1) := by ring
  -- assemble
  have hsumG : ∑ r ∈ U, G r = ∑ i ∈ range P, G (fP i) + ∑ i ∈ range P, G (fN i) := by
    rw [← hunion, sum_union hdisj, sum_image hinjP, sum_image hinjN]
  have hsumχ : ∑ r ∈ U, legendreSym p r * G r =
      legendreSym p a * (∑ i ∈ range P, G (fP i) - ∑ i ∈ range P, G (fN i)) := by
    rw [← hunion, sum_union hdisj, sum_image hinjP, sum_image hinjN]
    simp only [hchiP, hchiN, ← mul_sum, neg_mul]
    rw [sum_neg_distrib, ← mul_sum]
    ring
  rw [hsumG, hsumχ]
  have hsq : legendreSym p a ^ 2 = 1 := legendreSym_sq_eq_one ha
  change 2 * ∑ i ∈ range P, G (fP i) = _
  linear_combination (-(∑ i ∈ range P, G (fP i) - ∑ i ∈ range P, G (fN i))) * hsq

/-! ### The case `p ≡ 7 (mod 8)` -/

/-- **Doubling for `χ(2) = 1`.**  For `p ≡ 7 (mod 8)`: `S(1/4) = S(1/2)`. -/
theorem sum_quarter_eq_half (hp8 : p % 8 = 7) :
    ∑ r ∈ range ((p + 3) / 4), legendreSym p r = ∑ r ∈ range ((p + 1) / 2), legendreSym p r := by
  have hp2 : p ≠ 2 := by omega
  have h2 : legendreSym p 2 = 1 := by
    have hp2' : p % 2 = 1 := by omega
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]; simp [hp8, hp2']
  have hneg : legendreSym p (-1) = -1 := by
    rw [legendreSym.at_neg_one hp2, ZMod.χ₄_nat_three_mod_four (by omega)]
  obtain ⟨u, hu⟩ : ∃ u, p = 8 * u + 7 := ⟨p / 8, by omega⟩
  rw [show (p + 3) / 4 = 2 * u + 2 by omega, show (p + 1) / 2 = 2 * (2 * u + 2) by omega]
  set A := ∑ r ∈ range (2 * u + 2), legendreSym p r with hAdef
  set O := ∑ j ∈ range (2 * u + 2), legendreSym p ((2 * j + 1 : ℕ) : ℤ) with hO
  have hmul : ∀ r : ℕ, legendreSym p ((2 * r : ℕ) : ℤ) = legendreSym p r := by
    intro r; push_cast; rw [legendreSym.mul, h2, one_mul]
  have hE : ∑ r ∈ range (2 * (2 * u + 2)), legendreSym p r = A + O := by
    rw [sum_range_two_mul, sum_add_distrib]
    simp only [hmul]
    rfl
  have hhigh : ∑ i ∈ range (2 * u + 2), legendreSym p ((2 * (2 * u + 2 + i) : ℕ) : ℤ) = -O := by
    calc ∑ i ∈ range (2 * u + 2), legendreSym p ((2 * (2 * u + 2 + i) : ℕ) : ℤ)
        = ∑ i ∈ range (2 * u + 2), -legendreSym p ((2 * (2 * u + 2 - 1 - i) + 1 : ℕ) : ℤ) := by
          refine sum_congr rfl fun i hi => ?_
          rw [mem_range] at hi
          have := legendreSym_sub hneg (dvd_refl p) (show 2 * (2 * u + 2 - 1 - i) + 1 ≤ p by omega)
          rw [show p - (2 * (2 * u + 2 - 1 - i) + 1) = 2 * (2 * u + 2 + i) by omega] at this
          exact this
      _ = -O := by
          rw [sum_neg_distrib, hO,
            sum_range_reflect (fun j => legendreSym p ((2 * j + 1 : ℕ) : ℤ)) (2 * u + 2)]
  have hD : ∑ r ∈ range (2 * (2 * u + 2)), legendreSym p ((2 * r : ℕ) : ℤ) = A - O := by
    rw [show 2 * (2 * u + 2) = (2 * u + 2) + (2 * u + 2) by ring, sum_range_add, hhigh]
    simp only [hmul]
    rw [hAdef]
    ring
  have hD' : ∑ r ∈ range (2 * (2 * u + 2)), legendreSym p ((2 * r : ℕ) : ℤ) =
      ∑ r ∈ range (2 * (2 * u + 2)), legendreSym p r :=
    sum_congr rfl fun r _ => hmul r
  rw [hE] at hD' ⊢
  linarith

/-- For `p ≡ 7 (mod 8)` every period carries zero drift. -/
theorem sum_period_quarterWeight_of_mod_eight_eq_seven (hp8 : p % 8 = 7)
    (h4min : ∀ d < (p - 1) / 2, 0 < d → ¬ p ∣ 4 ^ d - 1) (h4w : ¬ p ^ 2 ∣ 4 ^ ((p - 1) / 2) - 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)),
      quarterWeight (p ^ k) (2 * stonehamPA p k * 4 ^ i % p ^ k) = 0 := by
  have hp2 : p ≠ 2 := by omega
  have h := two_mul_sum_four_orbit_of_order (by omega) h4min h4w hk
    (not_dvd_two_mul_stonehamPA hp2 hk) (quarterWeight (p ^ k))
  rw [sum_units_quarterWeight hp2 hk, sum_units_legendre_quarterWeight_eq hp2 hk,
    sum_Ico_quarter_half_eq_sub (by omega) hk, sum_quarter_eq_half hp8, sub_self, mul_zero,
    mul_zero, add_zero] at h
  linarith

/-- **Zero drift for `p ≡ 7 (mod 8)`.**  If `4` generates the squares modulo `p` and
`p² ∤ 4^{(p−1)/2} − 1`, the parity drift of `α_p` vanishes at every window end. -/
theorem drift_stonehamP_windowEnd_of_mod_eight_eq_seven (hp8 : p % 8 = 7)
    (h4min : ∀ d < (p - 1) / 2, 0 < d → ¬ p ∣ 4 ^ d - 1) (h4w : ¬ p ^ 2 ∣ 4 ^ ((p - 1) / 2) - 1)
    (k : ℕ) : drift (stonehamP p) ((p ^ (k + 1) + 1) / 2) = 0 := by
  rw [drift_stonehamP_windowEnd_of_period (by omega) (fourPeriod_of_order (by omega) h4min h4w)
    (fun _ hk => sum_period_quarterWeight_of_mod_eight_eq_seven hp8 h4min h4w hk) k]
  ring

/-- `D_{α_7}((7^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_seven (k : ℕ) : drift (stonehamP 7) ((7 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_mod_eight_eq_seven (by norm_num) (by decide) (by decide) k

/-- `D_{α_{23}}((23^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_twenty_three (k : ℕ) :
    drift (stonehamP 23) ((23 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_mod_eight_eq_seven (by norm_num) (by decide) (by decide) k

/-- `D_{α_{47}}((47^{k+1} + 1)/2) = 0`. -/
theorem drift_stonehamP_forty_seven (k : ℕ) :
    drift (stonehamP 47) ((47 ^ (k + 1) + 1) / 2) = 0 := by
  haveI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
  exact drift_stonehamP_windowEnd_of_mod_eight_eq_seven (by norm_num) (by decide) (by decide) k

end GaloisForLFunctions.HTGeometry.StonehamPrimeDrift
