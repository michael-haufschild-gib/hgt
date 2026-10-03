import GaloisForLFunctions.HTGeometry.ThreeFiveOrbitKorobovBound

/-!
# Complete orbit sums and Korobov parameters for odd moduli

Let every prime factor of `Q` be odd and divide `g − 1`.

* `dvd_sub_one_mul_of_sum_ne_zero`: if `T` is a period of `j ↦ e(w gʲ/Q)` and the complete orbit sum
  `Σ_{j<T} e(w gʲ/Q)` does not vanish, then `Q ∣ (g − 1) w`.  At each prime `p ∣ Q` a shift of `j`
  multiplies the sum by a nontrivial `p`-th root of unity unless `p^{v_p(Q) − v_p(g−1)} ∣ w`
  (`sum_orbit_eq_zero_of_prime`).  Exact lifting of the exponent
  (`pow_dvd_pow_sub_one_iff`, `factorization_pow_sub_one`) controls the shift.
* `exists_korobov_parameters`: if the prime factors of `Q` lie in a finite set `S`, then for every
  `r ≥ 1` there are `T₀, D` with `X = g^{T₀} − 1`, `D ∣ X`, `Q ∣ X^{r+1}`, the vanishing hypothesis
  of the iterated-differencing bound, `Q ≤ T₀^{r+1} ≤ Q P^r` and
  `Q ≤ (g−1)^{(r+1)²} P^{r²} D^{r+1}`, where `P = Π_{p∈S} p`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.OrbitVanishing

open StonehamParityDrift ThreeFiveOrbit

/-- A number is divisible by `Q` once every prime power `p^{v_p(Q)}` divides it. -/
theorem dvd_of_forall_prime_pow_dvd {Q n : ℕ} (hQ : Q ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ^ Q.factorization p ∣ n) : Q ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  refine (Nat.factorization_le_iff_dvd hQ hn).mp fun p => ?_
  by_cases hp : p.Prime
  · exact (hp.pow_dvd_iff_le_factorization hn).mp (h p hp)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **Lifting the exponent.**  For an odd prime `p ∣ g − 1` with `g ≥ 2` and `k ≥ v_p(g − 1)`,
`pᵏ ∣ gᵈ − 1 ⟺ p^{k − v_p(g−1)} ∣ d`. -/
theorem pow_dvd_pow_sub_one_iff {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 2 ≤ g)
    (hpg : p ∣ g - 1) {k d : ℕ} (hk : padicValNat p (g - 1) ≤ k) :
    p ^ k ∣ g ^ d - 1 ↔ p ^ (k - padicValNat p (g - 1)) ∣ d := by
  haveI := Fact.mk hp
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hpg' : ¬ p ∣ g := by
    intro h
    have : p ∣ g - (g - 1) := Nat.dvd_sub h hpg
    rw [show g - (g - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hne : g ^ d - 1 ≠ 0 := by
    have : 1 < g ^ d := Nat.one_lt_pow hd.ne' (by omega)
    omega
  have hlte := padicValNat.pow_sub_pow (p := p) (x := g) (y := 1) (hp.odd_of_ne_two hp2)
    (by omega) (by simpa using hpg) hpg' hd.ne'
  rw [one_pow] at hlte
  rw [padicValNat_dvd_iff_le hne, hlte, padicValNat_dvd_iff_le hd.ne']
  omega

/-- If every prime factor of `R` is odd and divides `g − 1`, then `R ∣ g^R − 1`. -/
theorem dvd_pow_self_sub_one {R g : ℕ} (hR : R ≠ 0) (hg : 2 ≤ g)
    (hodd : ∀ q ∈ R.primeFactors, q ≠ 2 ∧ q ∣ g - 1) : R ∣ g ^ R - 1 := by
  refine dvd_of_forall_prime_pow_dvd hR fun q hq => ?_
  by_cases hqR : q ∣ R
  · obtain ⟨hq2, hqg⟩ := hodd q (Nat.mem_primeFactors.mpr ⟨hq, hqR, hR⟩)
    haveI := Fact.mk hq
    have hv : 1 ≤ padicValNat q (g - 1) :=
      one_le_padicValNat_of_dvd (by omega) hqg
    rcases le_or_gt (padicValNat q (g - 1)) (R.factorization q) with hle | hlt
    · rw [pow_dvd_pow_sub_one_iff hq hq2 hg hqg hle, Nat.factorization_def R hq]
      exact (pow_dvd_pow q (Nat.sub_le _ _)).trans pow_padicValNat_dvd
    · refine (pow_dvd_pow q hlt.le).trans ?_
      refine (pow_padicValNat_dvd (n := g - 1)).trans ?_
      exact Nat.sub_one_dvd_pow_sub_one g R
  · rw [Nat.factorization_eq_zero_of_not_dvd hqR, pow_zero]
    exact one_dvd _

/-- **Vanishing at one prime.**  Let `Q = pᵅ R` with `p` an odd prime, `p ∤ R`, `p ∣ g − 1`,
`R ∣ g^ρ − 1` and `p ∤ ρ`.  If `T` is a period of `j ↦ e_Q(w gʲ)` and `p^{α − v_p(g−1)} ∤ w`,
then `Σ_{j<T} e_Q(w gʲ) = 0`: the shift by `σ = p^{α−v_p(w)−1−v_p(g−1)} ρ` multiplies the sum by a
nontrivial `p`-th root of unity. -/
theorem sum_orbit_eq_zero_of_prime {p α R ρ T g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 2 ≤ g)
    (hpg : p ∣ g - 1) (hR : R ∣ g ^ ρ - 1) (hρ : ¬ p ∣ ρ) (hpR : p.Coprime R) {w : ℤ}
    (hper : ((p ^ α * R : ℕ) : ℤ) ∣ w * ((g : ℤ) ^ T - 1))
    (hw : ¬ ((p ^ (α - padicValNat p (g - 1)) : ℕ) : ℤ) ∣ w) :
    ∑ j ∈ range T, ephase (p ^ α * R) (w * (g : ℤ) ^ j) = 0 := by
  haveI := Fact.mk hp
  obtain ⟨E, hE⟩ : ∃ E, E = padicValNat p (g - 1) := ⟨_, rfl⟩
  rw [← hE] at hw
  have hE1 : 1 ≤ E := hE ▸ one_le_padicValNat_of_dvd (by omega) hpg
  have hw0 : w ≠ 0 := by rintro rfl; exact hw (dvd_zero _)
  set e := padicValNat p w.natAbs with he
  have hwa : w.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hw0
  have hdvd : p ^ e ∣ w.natAbs := pow_padicValNat_dvd
  have hndvd : ¬ p ^ (e + 1) ∣ w.natAbs := pow_succ_padicValNat_not_dvd hwa
  have heα : e + E + 1 ≤ α := by
    by_contra h
    exact hw (Int.natCast_dvd.mpr ((pow_dvd_pow p (by omega)).trans hdvd))
  obtain ⟨w', hw'⟩ : ((p ^ e : ℕ) : ℤ) ∣ w := Int.natCast_dvd.mpr hdvd
  have hw'p : ¬ (p : ℤ) ∣ w' := by
    rintro ⟨t, rfl⟩
    apply hndvd
    rw [← Int.natCast_dvd, hw', pow_succ]
    push_cast
    exact ⟨t, by ring⟩
  have hlte := fun k (hk : E ≤ k) (d : ℕ) =>
    pow_dvd_pow_sub_one_iff (d := d) hp hp2 hg hpg (hE ▸ hk)
  set sh := p ^ (α - e - 1 - E) * ρ with hsh
  have h16 : 1 ≤ g ^ sh := Nat.one_le_pow _ _ (by omega)
  have hA : p ^ (α - e - 1) ∣ g ^ sh - 1 := by
    rw [hlte _ (by omega), ← hE]
    exact dvd_mul_right _ _
  have hB : ¬ p ^ (α - e) ∣ g ^ sh - 1 := by
    rw [hlte _ (by omega), ← hE, show α - e - E = α - e - 1 - E + 1 by omega, pow_succ, hsh]
    intro h
    exact hρ (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h)
  have hC : R ∣ g ^ sh - 1 := by
    refine hR.trans ?_
    rw [hsh, mul_comm, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (g ^ ρ) (p ^ (α - e - 1 - E))
  obtain ⟨κ, hκ⟩ : p ^ (α - e - 1) * R ∣ g ^ sh - 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ hpR) hA hC
  have hκp : ¬ p ∣ κ := by
    rintro ⟨t, rfl⟩
    apply hB
    have hpow : p ^ (α - e) = p ^ (α - e - 1) * p := by rw [← pow_succ]; congr 1; omega
    rw [hκ, hpow]
    exact ⟨R * t, by ring⟩
  have hκZ : ((g : ℤ) ^ sh - 1) = (p : ℤ) ^ (α - e - 1) * R * κ := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hκ
    simp only [Nat.cast_sub h16, Nat.cast_pow, Nat.cast_mul, Nat.cast_one] at this
    exact this
  have hR0 : R ≠ 0 := by rintro rfl; simp at hpR; exact hp.one_lt.ne' hpR
  have hsplit : p ^ α * R = p * (p ^ (α - 1) * R) := by
    rw [← mul_assoc, ← pow_succ']; congr 2; omega
  have hM0 : p ^ (α - 1) * R ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hR0
  have hQ0 : p ^ α * R ≠ 0 := by rw [hsplit]; exact Nat.mul_ne_zero hp.ne_zero hM0
  have hgp : (g : ℤ) ≡ 1 [ZMOD p] := by
    obtain ⟨t, ht⟩ := hpg
    have : ((g - 1 : ℕ) : ℤ) = p * t := by exact_mod_cast ht
    push_cast [show 1 ≤ g by omega] at this
    exact (Int.modEq_iff_dvd.mpr ⟨-t, by linear_combination -this⟩)
  refine sum_range_eq_zero_of_shift (sh := sh) (ζ := ephase p (w' * κ)) ?_ ?_ ?_
  · intro j
    apply ephase_congr hQ0
    rw [Int.modEq_iff_dvd]
    obtain ⟨t, ht⟩ := hper
    exact ⟨-(t * (g : ℤ) ^ j), by rw [pow_add]; linear_combination (-(g : ℤ) ^ j) * ht⟩
  · intro h
    have hdv : ¬ (p : ℤ) ∣ w' * κ := by
      intro h0
      rcases Int.Prime.dvd_mul' hp h0 with h1 | h1
      · exact hw'p h1
      · exact hκp (Int.natCast_dvd_natCast.mp h1)
    exact ephase_ne_one hp.ne_zero hdv h
  · intro j
    rw [← ephase_mul_left_cancel hM0 p, ← hsplit, ← ephase_add]
    apply ephase_congr hQ0
    have hcong : (w' * κ : ℤ) * (g : ℤ) ^ j ≡ w' * κ [ZMOD p] := by
      simpa using (hgp.pow j).mul_left (w' * κ)
    obtain ⟨s, hs⟩ := (Int.modEq_iff_dvd.mp hcong.symm)
    rw [Int.modEq_iff_dvd]
    refine ⟨-s, ?_⟩
    have hpe : (p : ℤ) ^ (α - 1) = p ^ e * p ^ (α - e - 1) := by
      rw [← pow_add]; congr 1; omega
    have hQZ : ((p ^ α * R : ℕ) : ℤ) = p * ((p : ℤ) ^ (α - 1) * R) := by
      rw [hsplit]; push_cast; ring
    rw [hQZ]
    push_cast at hw' ⊢
    rw [pow_add, hw', hpe]
    have h16σ : (g : ℤ) ^ sh = 1 + (p : ℤ) ^ (α - e - 1) * R * κ := by linarith [hκZ]
    rw [h16σ]
    linear_combination (-(p : ℤ) ^ e * p ^ (α - e - 1) * R) * hs

/-- **Nonvanishing forces divisibility.**  If every prime factor of `Q` is odd and divides
`g − 1`, `T` is a period of `j ↦ e_Q(w gʲ)` and `Σ_{j<T} e_Q(w gʲ) ≠ 0`, then
`Q ∣ (g − 1) w`. -/
theorem dvd_sub_one_mul_of_sum_ne_zero {Q g T : ℕ} (hQ : Q ≠ 0) (hg : 2 ≤ g)
    (hodd : ∀ p ∈ Q.primeFactors, p ≠ 2 ∧ p ∣ g - 1) {w : ℤ}
    (hper : (Q : ℤ) ∣ w * ((g : ℤ) ^ T - 1))
    (hS : ∑ j ∈ range T, ephase Q (w * (g : ℤ) ^ j) ≠ 0) :
    (Q : ℤ) ∣ ((g : ℤ) - 1) * w := by
  have hg1 : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by push_cast [show 1 ≤ g by omega]; ring
  rw [hg1, Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_natCast]
  refine dvd_of_forall_prime_pow_dvd hQ fun p hp => ?_
  by_cases hpQ : p ∣ Q
  · haveI := Fact.mk hp
    obtain ⟨hp2, hpg⟩ := hodd p (Nat.mem_primeFactors.mpr ⟨hp, hpQ, hQ⟩)
    obtain ⟨α, hα⟩ : ∃ α, α = Q.factorization p := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R, R = Q / p ^ α := ⟨_, rfl⟩
    have hQR : Q = p ^ α * R := by rw [hR, hα]; exact (Nat.ordProj_mul_ordCompl_eq_self Q p).symm
    have hpR : p.Coprime R := by rw [hR, hα]; exact Nat.coprime_ordCompl hp hQ
    have hR0 : R ≠ 0 := by rintro rfl; rw [mul_zero] at hQR; exact hQ hQR
    have hRodd : ∀ q ∈ R.primeFactors, q ≠ 2 ∧ q ∣ g - 1 := by
      intro q hq
      refine hodd q (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
        (Nat.dvd_of_mem_primeFactors hq).trans ⟨p ^ α, by rw [hQR]; ring⟩, hQ⟩)
    have hRg := dvd_pow_self_sub_one hR0 hg hRodd
    have hρ : ¬ p ∣ R := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hpR h)
    have hdiv : ((p ^ (α - padicValNat p (g - 1)) : ℕ) : ℤ) ∣ w := by
      by_contra hw
      rw [hQR] at hper hS
      exact hS (sum_orbit_eq_zero_of_prime hp hp2 hg hpg hRg hρ hpR hper hw)
    rw [← hα]
    calc p ^ α ∣ p ^ padicValNat p (g - 1) * p ^ (α - padicValNat p (g - 1)) := by
          rw [← pow_add]; exact pow_dvd_pow p (by omega)
      _ ∣ (g - 1) * w.natAbs :=
          Nat.mul_dvd_mul pow_padicValNat_dvd (Int.natCast_dvd.mp hdiv)
  · rw [Nat.factorization_eq_zero_of_not_dvd hpQ, pow_zero]
    exact one_dvd _

/-! ### Korobov parameters for moduli with prime factors in a finite set -/

theorem factorization_prod_pow {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℕ) (q : ℕ) :
    (∏ p ∈ S, p ^ f p).factorization q = if q ∈ S then f q else 0 := by
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hS p hp).ne_zero),
    Finsupp.finsetSum_apply]
  rw [sum_congr rfl fun p hp => by rw [(hS p hp).factorization_pow]]
  simp only [Finsupp.single_apply]
  rw [sum_ite_eq']

/-- **Exact lifting the exponent.**  `v_p(gᵀ − 1) = v_p(g − 1) + v_p(T)`. -/
theorem factorization_pow_sub_one {p g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hg : 2 ≤ g)
    (hpg : p ∣ g - 1) {T : ℕ} (hT : T ≠ 0) :
    (g ^ T - 1).factorization p = (g - 1).factorization p + T.factorization p := by
  haveI := Fact.mk hp
  have hpg' : ¬ p ∣ g := by
    intro h
    have : p ∣ g - (g - 1) := Nat.dvd_sub h hpg
    rw [show g - (g - 1) = 1 by omega] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hlte := padicValNat.pow_sub_pow (p := p) (x := g) (y := 1) (hp.odd_of_ne_two hp2)
    (by omega) (by simpa using hpg) hpg' hT
  rw [one_pow] at hlte
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp, hlte]

theorem gcd_pow_le (a b r : ℕ) (ha : 0 < a) : Nat.gcd a (b ^ r) ≤ Nat.gcd a b ^ r := by
  have hd : Nat.gcd a (b ^ r) ∣ Nat.gcd a b ^ r := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, pow_succ]
      exact (Nat.gcd_mul_right_dvd_mul_gcd a _ _).trans (Nat.mul_dvd_mul_right ih _)
  exact Nat.le_of_dvd (pow_pos (Nat.gcd_pos_of_pos_left _ ha) _) hd

/-- `a ∣ b v` gives `a / gcd(a, b) ∣ v`. -/
theorem div_gcd_dvd_of_dvd_mul {a b : ℕ} (ha : 0 < a) {v : ℤ} (h : (a : ℤ) ∣ b * v) :
    ((a / Nat.gcd a b : ℕ) : ℤ) ∣ v := by
  obtain ⟨G, hG⟩ : ∃ G, G = Nat.gcd a b := ⟨_, rfl⟩
  have hG0 : 0 < G := hG ▸ Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a', ha'⟩ : G ∣ a := hG ▸ Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : G ∣ b := hG ▸ Nat.gcd_dvd_right a b
  have hcop : Nat.Coprime a' b' := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) (hG ▸ hG0)
    rwa [← hG, ha', hb', Nat.mul_div_cancel_left _ hG0, Nat.mul_div_cancel_left _ hG0] at this
  rw [← hG, ha', Nat.mul_div_cancel_left _ hG0]
  rw [ha', hb'] at h
  push_cast at h
  have hGZ : (G : ℤ) ≠ 0 := by exact_mod_cast hG0.ne'
  rw [mul_assoc] at h
  have h' := (mul_dvd_mul_iff_left hGZ).mp h
  exact IsCoprime.dvd_of_dvd_mul_left (Nat.isCoprime_iff_coprime.mpr hcop) h'

/-- **Korobov parameters.**  Let every prime of the finite set `S` be odd and divide `g − 1`, and
let the prime factors of `Q` lie in `S`.  For `u` prime to `Q` and `r ≥ 1` there are `T₀, D` with
`X = g^{T₀} − 1`: `D ∣ X`, `Q ∣ X^{r+1}`, complete orbit sums `Σ_{j<T₀} e_Q(u X^r v gʲ)` vanish
unless `D ∣ v`, and `Q ≤ T₀^{r+1} ≤ Q P^r`, `Q ≤ (g−1)^{(r+1)²} P^{r²} D^{r+1}` with
`P = Π_{p∈S} p`. -/
theorem exists_korobov_parameters {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) {g : ℕ}
    (hg : 2 ≤ g) (hgS : ∀ p ∈ S, p ∣ g - 1) {Q : ℕ} (hQ : Q ≠ 0) (hQS : Q.primeFactors ⊆ S)
    {r : ℕ} (hr : 1 ≤ r) {u : ℤ} (hu : IsCoprime u (Q : ℤ)) :
    ∃ T₀ D : ℕ, 0 < T₀ ∧ 0 < D ∧ (D : ℤ) ∣ ((g : ℤ) ^ T₀ - 1) ∧
      (Q : ℤ) ∣ ((g : ℤ) ^ T₀ - 1) ^ (r + 1) ∧
      (∀ v : ℤ, ∑ j ∈ range T₀, ephase Q (u * ((g : ℤ) ^ T₀ - 1) ^ r * v * (g : ℤ) ^ j) ≠ 0 →
        (D : ℤ) ∣ v) ∧
      Q ≤ T₀ ^ (r + 1) ∧ T₀ ^ (r + 1) ≤ Q * (∏ p ∈ S, p) ^ r ∧
      Q ≤ (g - 1) ^ ((r + 1) ^ 2) * (∏ p ∈ S, p) ^ (r ^ 2) * D ^ (r + 1) := by
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (hS p hp).1
  set s : ℕ → ℕ := fun p => (Q.factorization p + r) / (r + 1) with hs
  set T₀ := ∏ p ∈ S, p ^ s p with hT₀
  have hT0 : 0 < T₀ := Finset.prod_pos fun p hp => pow_pos (hSp p hp).pos _
  have hT₀f : ∀ p ∈ S, T₀.factorization p = s p := fun p hp => by
    rw [hT₀, factorization_prod_pow hSp, if_pos hp]
  have hg1 : 1 ≤ g ^ T₀ := Nat.one_le_pow _ _ (by omega)
  set Xn := g ^ T₀ - 1 with hXn
  have hXZ : ((Xn : ℕ) : ℤ) = (g : ℤ) ^ T₀ - 1 := by rw [hXn]; push_cast [hg1]; ring
  have hXn0 : Xn ≠ 0 := by
    have : 1 < g ^ T₀ := Nat.one_lt_pow hT0.ne' (by omega)
    omega
  have hXv : ∀ p ∈ S, Xn.factorization p = (g - 1).factorization p + s p := fun p hp => by
    rw [hXn, factorization_pow_sub_one (hSp p hp) (hS p hp).2 hg (hgS p hp) hT0.ne', hT₀f p hp]
  have hP0 : 0 < ∏ p ∈ S, p := Finset.prod_pos fun p hp => (hSp p hp).pos
  have hPf : ∀ p ∈ S, (∏ q ∈ S, q).factorization p = 1 := fun p hp => by
    have := factorization_prod_pow hSp (fun _ => 1) p
    simp only [pow_one] at this
    rw [this, if_pos hp]
  have hmemS : ∀ p, p.Prime → p ∣ Q → p ∈ S := fun p hp hpQ =>
    hQS (Nat.mem_primeFactors.mpr ⟨hp, hpQ, hQ⟩)
  have hceil : ∀ p, Q.factorization p ≤ (r + 1) * s p := fun p => by
    have := Nat.div_add_mod (Q.factorization p + r) (r + 1)
    have := Nat.mod_lt (Q.factorization p + r) (show 0 < r + 1 by omega)
    simp only [hs]
    nlinarith
  have hceil' : ∀ p, (r + 1) * s p ≤ Q.factorization p + r := fun p => by
    simp only [hs]
    exact Nat.mul_div_le _ _
  -- `Q ∣ X^{r+1}`
  have hQX : Q ∣ Xn ^ (r + 1) := by
    refine dvd_of_forall_prime_pow_dvd hQ fun p hp => ?_
    by_cases hpQ : p ∣ Q
    · have hpS := hmemS p hp hpQ
      have h1 : p ^ s p ∣ Xn := by
        rw [hp.pow_dvd_iff_le_factorization hXn0, hXv p hpS]
        omega
      calc p ^ Q.factorization p ∣ p ^ ((r + 1) * s p) := pow_dvd_pow p (hceil p)
        _ = (p ^ s p) ^ (r + 1) := by rw [← pow_mul, mul_comm]
        _ ∣ Xn ^ (r + 1) := pow_dvd_pow_of_dvd h1 _
    · rw [Nat.factorization_eq_zero_of_not_dvd hpQ, pow_zero]
      exact one_dvd _
  -- the gcd and `D`
  set G := Nat.gcd Q ((g - 1) * Xn ^ r) with hG
  have hG0 : 0 < G := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hQ)
  have hGQ : G ∣ Q := Nat.gcd_dvd_left _ _
  set D := Q / G with hD
  have hD0 : 0 < D := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) hGQ) hG0
  have hQGD : Q = G * D := (Nat.mul_div_cancel' hGQ).symm
  have hDX : D ∣ Xn := by
    rw [hD, Nat.div_dvd_iff_dvd_mul hGQ hG0, hG, ← Nat.gcd_mul_right]
    refine Nat.dvd_gcd (dvd_mul_right _ _) ?_
    rw [mul_assoc, ← pow_succ]
    exact hQX.trans (dvd_mul_left _ _)
  -- `gcd(Q, X) ∣ (g − 1) T₀`
  have hgcdX : Nat.gcd Q Xn ∣ (g - 1) * T₀ := by
    refine dvd_of_forall_prime_pow_dvd (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hQ)).ne'
      fun p hp => ?_
    by_cases hpQ : p ∣ Q
    · have hpS := hmemS p hp hpQ
      have hg10 : g - 1 ≠ 0 := by omega
      rw [hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero hg10 hT0.ne'),
        Nat.factorization_mul hg10 hT0.ne', Finsupp.add_apply, hT₀f p hpS, ← hXv p hpS]
      exact (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_left _
        (Nat.pos_of_ne_zero hQ)).ne' hXn0).mpr (Nat.gcd_dvd_right _ _) p
    · have : ¬ p ∣ Nat.gcd Q Xn := fun h => hpQ (h.trans (Nat.gcd_dvd_left _ _))
      rw [Nat.factorization_eq_zero_of_not_dvd this, pow_zero]
      exact one_dvd _
  have hGle : G ≤ (g - 1) ^ (r + 1) * T₀ ^ r := by
    have hQ0 : 0 < Q := Nat.pos_of_ne_zero hQ
    calc G ≤ Nat.gcd Q (g - 1) * Nat.gcd Q (Xn ^ r) :=
          Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hQ0)
            (Nat.gcd_pos_of_pos_left _ hQ0)) (Nat.gcd_mul_right_dvd_mul_gcd _ _ _)
      _ ≤ (g - 1) * Nat.gcd Q Xn ^ r :=
          Nat.mul_le_mul (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) (gcd_pow_le _ _ _ hQ0)
      _ ≤ (g - 1) * ((g - 1) * T₀) ^ r := by
          gcongr
          exact Nat.le_of_dvd (Nat.mul_pos (by omega) hT0) hgcdX
      _ = (g - 1) ^ (r + 1) * T₀ ^ r := by ring
  -- sizes of `T₀`
  have hQT : Q ∣ T₀ ^ (r + 1) := by
    refine dvd_of_forall_prime_pow_dvd hQ fun p hp => ?_
    by_cases hpQ : p ∣ Q
    · have hpS := hmemS p hp hpQ
      rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero _ hT0.ne'), Nat.factorization_pow,
        Finsupp.smul_apply, smul_eq_mul, hT₀f p hpS]
      exact hceil p
    · rw [Nat.factorization_eq_zero_of_not_dvd hpQ, pow_zero]
      exact one_dvd _
  have hTQ : T₀ ^ (r + 1) ∣ Q * (∏ p ∈ S, p) ^ r := by
    refine dvd_of_forall_prime_pow_dvd (pow_ne_zero _ hT0.ne') fun p hp => ?_
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero hQ (pow_ne_zero _ hP0.ne')),
      Nat.factorization_mul hQ (pow_ne_zero _ hP0.ne'), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hpS : p ∈ S
    · rw [hT₀f p hpS, hPf p hpS]
      have := hceil' p
      omega
    · rw [hT₀, factorization_prod_pow hSp, if_neg hpS]
      omega
  refine ⟨T₀, D, hT0, hD0, ?_, ?_, ?_, Nat.le_of_dvd (pow_pos hT0 _) hQT,
    Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hQ) (pow_pos hP0 _)) hTQ, ?_⟩
  · rw [← hXZ]; exact_mod_cast hDX
  · rw [← hXZ]; exact_mod_cast hQX
  · intro v hv
    have hper : (Q : ℤ) ∣ u * ((g : ℤ) ^ T₀ - 1) ^ r * v * ((g : ℤ) ^ T₀ - 1) := by
      rw [← hXZ]
      have : ((Q : ℕ) : ℤ) ∣ ((Xn ^ (r + 1) : ℕ) : ℤ) := by exact_mod_cast hQX
      refine this.trans ⟨u * v, ?_⟩
      push_cast
      ring
    have h1 := dvd_sub_one_mul_of_sum_ne_zero hQ hg
      (fun p hp => ⟨(hS p (hQS hp)).2, hgS p (hQS hp)⟩) hper hv
    have h2 : (Q : ℤ) ∣ u * (((g - 1) * Xn ^ r : ℕ) * v) := by
      rw [← hXZ] at h1
      have hg' : ((g : ℤ) - 1) = ((g - 1 : ℕ) : ℤ) := by push_cast [show 1 ≤ g by omega]; ring
      rw [hg'] at h1
      refine h1.trans ⟨1, ?_⟩
      push_cast
      ring
    have h3 : (Q : ℤ) ∣ ((g - 1) * Xn ^ r : ℕ) * v :=
      IsCoprime.dvd_of_dvd_mul_left hu.symm h2
    exact div_gcd_dvd_of_dvd_mul (Nat.pos_of_ne_zero hQ) h3
  · -- `Q ≤ (g−1)^{(r+1)²} P^{r²} D^{r+1}`
    have hQ0 : 0 < Q := Nat.pos_of_ne_zero hQ
    have h1 : Q ≤ D * ((g - 1) ^ (r + 1) * T₀ ^ r) := by
      rw [hQGD, mul_comm G]; exact Nat.mul_le_mul_left _ hGle
    have h2 : Q ^ (r + 1) ≤ D ^ (r + 1) * (g - 1) ^ ((r + 1) ^ 2) * (T₀ ^ (r + 1)) ^ r := by
      calc Q ^ (r + 1) ≤ (D * ((g - 1) ^ (r + 1) * T₀ ^ r)) ^ (r + 1) := Nat.pow_le_pow_left h1 _
        _ = D ^ (r + 1) * (g - 1) ^ ((r + 1) ^ 2) * (T₀ ^ (r + 1)) ^ r := by ring
    have h3 : (T₀ ^ (r + 1)) ^ r ≤ (Q * (∏ p ∈ S, p) ^ r) ^ r :=
      Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.mul_pos hQ0 (pow_pos hP0 _)) hTQ) _
    have h4 : Q ^ r * Q ≤
        Q ^ r * ((g - 1) ^ ((r + 1) ^ 2) * (∏ p ∈ S, p) ^ (r ^ 2) * D ^ (r + 1)) := by
      calc Q ^ r * Q = Q ^ (r + 1) := by ring
        _ ≤ D ^ (r + 1) * (g - 1) ^ ((r + 1) ^ 2) * (Q * (∏ p ∈ S, p) ^ r) ^ r :=
            h2.trans (Nat.mul_le_mul_left _ h3)
        _ = Q ^ r * ((g - 1) ^ ((r + 1) ^ 2) * (∏ p ∈ S, p) ^ (r ^ 2) * D ^ (r + 1)) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (pow_pos hQ0 _)

end GaloisForLFunctions.HTGeometry.OrbitVanishing
