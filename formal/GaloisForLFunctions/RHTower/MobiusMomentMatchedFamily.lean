import GaloisForLFunctions.RHTower.MobiusMomentMatchedPacket

/-!
# Moment-matched cofactor families in one physical block

A cofactor `q` is *admissible at scale `R`* when it is odd, squarefree, and every prime factor of
`q` is below `R/q`.  In a block `[X, X+L] ⊆ [2R, 4R]` the theta-mass windows at the bases
`(X + t_i L)/q` and `(X + t_i L)/(2q)` supply `m_q = ⌊(R/q)^α/(32768 log 5R)⌋` atoms `qp` and `2qr`
in each window `[X + t_i L, X + (t_i + ε)L]`.  The atoms of Möbius sign `+1` are the `2qr` when
`μ(q) = 1` and the `qp` when `μ(q) = -1`; the atoms of sign `-1` are the others.

Every selected variable prime exceeds all prime factors of its cofactor, so it is the largest prime
factor of the atom; together with parity this makes all candidate atoms of one sign distinct across
cofactors.  The moment-matched selection then picks exactly `Σ_q m_q` atoms of each sign, with the
order-`(d+1)` Taylor bound.
-/

open Finset

noncomputable section

namespace RHTower.CubicGamma

open RHTower.MomentSelector
open scoped ArithmeticFunction.Moebius

/-- The per-cofactor supply `m_q = ⌊(R/q)^α/(32768 log 5R)⌋`. -/
def cofactorSupply (R : ℝ) (q : ℕ) : ℕ :=
  ⌊(R / q) ^ supplyExp / (32768 * Real.log (5 * R))⌋₊

/-! ### Arithmetic of the atoms -/

/-- `μ(2qr) = μ(q)` for odd `q` and a prime `r ∤ q`, `r > 2`. -/
theorem moebius_two_mul_mul_prime_of_not_dvd {q r : ℕ} (hq : Odd q) (hr : r.Prime)
    (hrq : ¬ r ∣ q) (hr2 : 2 < r) : μ (2 * q * r) = μ q := by
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  have hcop1 : Nat.Coprime 2 (q * r) := Nat.coprime_two_left.mpr (hq.mul hrodd)
  have hcop2 : Nat.Coprime q r := ((hr.coprime_iff_not_dvd).mpr hrq).symm
  rw [mul_assoc, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop1,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop2,
    ArithmeticFunction.moebius_apply_prime hr, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

/-- `μ(qp) = -μ(q)` for a prime `p ∤ q`. -/
theorem moebius_mul_prime_of_not_dvd {q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    μ (q * p) = -μ q := by
  have hcop : Nat.Coprime q p := ((hp.coprime_iff_not_dvd).mpr hpq).symm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- The largest prime factor determines the cofactor: `qr = q'r'` with `r, r'` primes above all
prime factors of `q`, `q'` forces `q = q'` and `r = r'`. -/
theorem cofactor_eq_of_largest_prime {q q' r r' : ℕ} (hr : r.Prime) (hr' : r'.Prime)
    (hq : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → ℓ < r) (hq' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q' → ℓ < r')
    (h : q * r = q' * r') : q = q' ∧ r = r' := by
  have hrr : r = r' := by
    by_contra hne
    have h1 : r ∣ q' := by
      have : r ∣ q' * r' := ⟨q, by rw [← h]; ring⟩
      rcases (Nat.Prime.dvd_mul hr).mp this with h1 | h1
      · exact h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hr').mp h1) hne
    have h2 : r' ∣ q := by
      have : r' ∣ q * r := ⟨q', by rw [h]; ring⟩
      rcases (Nat.Prime.dvd_mul hr').mp this with h2 | h2
      · exact h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr' hr).mp h2).symm hne
    have := hq' r hr h1
    have := hq r' hr' h2
    omega
  subst hrr
  exact ⟨Nat.eq_of_mul_eq_mul_right hr.pos h, rfl⟩

/-- The two window tops stay below `5R`. -/
theorem window_tops_le {q : ℕ} (hq : 1 ≤ q) {R Z : ℝ} (hZ0 : 0 ≤ Z) (hZ : Z ≤ 4 * R)
    (hH : (q : ℝ) * (4 * R / q) ^ supplyExp ≤ R) :
    Z / q + (Z / q) ^ supplyExp / 2 ≤ 5 * R ∧
      Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2 ≤ 5 * R := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h2q : (0 : ℝ) < 2 * q := by positivity
  have hzq : Z / q ≤ 4 * R / q := div_le_div_of_nonneg_right hZ hq0.le
  have hzq2 : Z / (2 * q) ≤ 4 * R / q := by
    rw [div_le_div_iff₀ h2q hq0]; nlinarith
  have hH1 := cofactor_rpow_le hq (div_nonneg hZ0 hq0.le) hzq
  have hH2 := cofactor_rpow_le hq (div_nonneg hZ0 h2q.le) hzq2
  have hr1 := Real.rpow_nonneg (div_nonneg hZ0 hq0.le) supplyExp
  have hr2 := Real.rpow_nonneg (div_nonneg hZ0 h2q.le) supplyExp
  constructor
  · have e : q * (Z / q + (Z / q) ^ supplyExp / 2) = Z + q * (Z / q) ^ supplyExp / 2 := by
      field_simp
    have h1 : q * (Z / q + (Z / q) ^ supplyExp / 2) ≤ 5 * R := by rw [e]; nlinarith
    have h2 : 0 ≤ Z / q + (Z / q) ^ supplyExp / 2 := by positivity
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  · have e : 2 * q * (Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2) =
        Z + q * (Z / (2 * q)) ^ supplyExp := by
      field_simp
    have h1 : 2 * q * (Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2) ≤ 5 * R := by
      rw [e]; nlinarith
    have h2 : 0 ≤ Z / (2 * q) + (Z / (2 * q)) ^ supplyExp / 2 := by positivity
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hq1 : (1 : ℝ) ≤ 2 * q := by linarith
    nlinarith


/-- An admissible cofactor at scale `R`: odd, squarefree, all prime factors below `R/q`. -/
def AdmissibleCofactor (R : ℝ) (q : ℕ) : Prop :=
  1 ≤ q ∧ Odd q ∧ Squarefree q ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → (ℓ : ℝ) < R / q

/-- The shape of a selected atom with cofactor `q`: `2qr` or `qr` with a prime `r > max(2, R/q)`
above every prime factor of `q` (and `r > 2R/q` in the second case). -/
def AtomShape (R : ℝ) (q n : ℕ) : Prop :=
  ∃ r : ℕ, r.Prime ∧ 2 < r ∧ R / q < r ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q → ℓ < r) ∧
    (n = 2 * q * r ∨ (n = q * r ∧ 2 * R / q < r))

/-- Two atoms with admissible shapes and odd cofactors are equal only for equal cofactors. -/
theorem cofactor_eq_of_shape {R : ℝ} {q q' n : ℕ} (hq : Odd q) (hq' : Odd q')
    (h : AtomShape R q n) (h' : AtomShape R q' n) : q = q' := by
  obtain ⟨r, hr, hr2, -, hrq, hn⟩ := h
  obtain ⟨r', hr', hr2', -, hrq', hn'⟩ := h'
  rcases hn with rfl | ⟨rfl, -⟩ <;> rcases hn' with he | ⟨he, -⟩
  · have e : q * r = q' * r' := by
      have : 2 * (q * r) = 2 * (q' * r') := by rw [← mul_assoc, ← mul_assoc]; exact he
      omega
    exact (cofactor_eq_of_largest_prime hr hr' hrq hrq' e).1
  · exfalso
    have hodd : Odd (q' * r') := hq'.mul (hr'.odd_of_ne_two (by omega))
    rw [← he] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨q * r, by ring⟩
  · exfalso
    have hodd : Odd (q * r) := hq.mul (hr.odd_of_ne_two (by omega))
    rw [he] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨q' * r', by ring⟩
  · exact (cofactor_eq_of_largest_prime hr hr' hrq hrq' he).1

/-- The oriented atom of sign `σ` for the cofactor `q`: `2qr` when `μ(q) = 1 ↔ σ`, else `qp`. -/
def orientedAtom (σ : Bool) (q r p : ℕ) : ℕ :=
  if (μ q = 1 ↔ σ = true) then 2 * q * r else q * p

theorem moebius_squarefree_cases {q : ℕ} (hq : Squarefree q) : μ q = 1 ∨ μ q = -1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hq]
  rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors q) with h | h <;> simp [h]

/-- The oriented atom has Möbius sign `σ`. -/
theorem moebius_orientedAtom {σ : Bool} {q r p : ℕ} (hq : Odd q) (hqs : Squarefree q)
    (hr : r.Prime) (hr2 : 2 < r) (hrq : ¬ r ∣ q) (hp : p.Prime) (hpq : ¬ p ∣ q) :
    μ (orientedAtom σ q r p) = if σ then 1 else -1 := by
  unfold orientedAtom
  rcases moebius_squarefree_cases hqs with h | h <;> cases σ <;>
    simp [h, moebius_two_mul_mul_prime_of_not_dvd hq hr hrq hr2, moebius_mul_prime_of_not_dvd hp hpq]

/-- An atom in two windows `[X + t_i L, X + t_i L + εL]` with `ε ≤ 1/(2(d+2))` fixes the window. -/
theorem window_index_eq {d : ℕ} {i i' : Fin (d + 1)} {X L ε n : ℝ} (hL : 0 < L)
    (hεw : ε ≤ 1 / (2 * ((d : ℝ) + 2)))
    (h1 : X + layerNodes d i * L < n) (h2 : n ≤ X + layerNodes d i * L + ε * L)
    (h3 : X + layerNodes d i' * L < n) (h4 : n ≤ X + layerNodes d i' * L + ε * L) : i = i' := by
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hlt1 : (layerNodes d i - layerNodes d i') * L < ε * L := by linarith
  have hlt2 : (layerNodes d i' - layerNodes d i) * L < ε * L := by linarith
  have e1 := lt_of_mul_lt_mul_right hlt1 hL.le
  have e2 := lt_of_mul_lt_mul_right hlt2 hL.le
  have hε' : ε < 1 / ((d : ℝ) + 2) := by
    refine hεw.trans_lt ?_
    apply one_div_lt_one_div_of_lt hd2
    linarith
  unfold layerNodes at e1 e2
  rw [div_sub_div_same, div_lt_iff₀ hd2] at e1 e2
  have hε2 : ε * ((d : ℝ) + 2) < 1 := by rwa [lt_div_iff₀ hd2] at hε'
  have a1 : (i : ℝ) - i' < 1 := by linarith
  have a2 : (i' : ℝ) - i < 1 := by linarith
  have b1 : (i : ℕ) < i' + 1 := by exact_mod_cast (by linarith : (i : ℝ) < i' + 1)
  have b2 : (i' : ℕ) < i + 1 := by exact_mod_cast (by linarith : (i' : ℝ) < i + 1)
  exact Fin.ext (by omega)

/-! ### One block -/

/-- **Moment-matched cofactor block.**  In a block `[X, X+L] ⊆ [2R, 4R]` an admissible family of
cofactors with theta windows of length `≤ εL` yields atoms of each Möbius sign, exactly
`Σ_q m_q` selected of each, distinct, of admissible shape, and the order-`(d+1)` Taylor bound. -/
theorem exists_family_block {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε0 : 0 < ε)
    (hεw : ε ≤ 1 / (2 * ((d : ℝ) + 2)))
    (hε : ∀ Q : Fin (d + 1) → Fin d → ℝ,
        (∀ i k, |Q i k - layerNodes d i ^ (k.val + 1)| ≤ d * ε) →
        ∃ w : Fin (d + 1) → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ ∑ i, w i = 1 ∧
          ∀ k : Fin d, ∑ i, w i * Q i k = nominalBarycenter (layerNodes d) k)
    {z₀ : ℝ} (hz₀ : 1 ≤ z₀)
    (hsupply : ∀ z : ℝ, z₀ ≤ z → z ^ supplyExp / 16384 <
      Chebyshev.theta (z + z ^ supplyExp / 2) - Chebyshev.theta z)
    {R L X : ℝ} (hR : 5 ≤ R) (hL : 0 < L) (hLR : L ≤ R) (hX : 2 * R ≤ X) (hXL : X + L ≤ 4 * R)
    (F : Finset ℕ)
    (hF : ∀ q ∈ F, AdmissibleCofactor R q ∧ 2 ≤ R / q ∧ z₀ ≤ R / q ∧
      (q : ℝ) * (4 * R / q) ^ supplyExp ≤ ε * L) :
    ∃ aP aN : (Σ _ : ℕ, Fin (d + 1) × ℕ) → ℕ,
    ∃ TP ⊆ familyLabels (d := d) F (cofactorSupply R),
    ∃ TN ⊆ familyLabels (d := d) F (cofactorSupply R),
      TP.card = ∑ q ∈ F, cofactorSupply R q ∧ TN.card = ∑ q ∈ F, cofactorSupply R q ∧
      Set.InjOn aP ↑(familyLabels (d := d) F (cofactorSupply R)) ∧
      Set.InjOn aN ↑(familyLabels (d := d) F (cofactorSupply R)) ∧
      (∀ x ∈ familyLabels (d := d) F (cofactorSupply R), X < aP x ∧ (aP x : ℝ) < X + L ∧
        μ (aP x) = 1 ∧ x.1 ∈ F ∧ AtomShape R x.1 (aP x)) ∧
      (∀ x ∈ familyLabels (d := d) F (cofactorSupply R), X < aN x ∧ (aN x : ℝ) < X + L ∧
        μ (aN x) = -1 ∧ x.1 ∈ F ∧ AtomShape R x.1 (aN x)) ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
        gammaNorm δ (fun t => ∑ x ∈ TP, atom (aP x) t - ∑ x ∈ TN, atom (aN x) t) ≤
          ∑ j ∈ range d, 2 * L ^ (j + 1) / ((j + 1).factorial : ℝ) *
              (jetConst (j + 1) * X ^ 2 * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (j + 1)) +
            ((2 * ∑ q ∈ F, cofactorSupply R q : ℕ) : ℝ) *
              (L ^ (d + 1) / ((d + 1).factorial : ℝ) *
                (jetConst (d + 1) * (4 * X ^ 2) * (X ^ ((5 + δ) / 2))⁻¹ / X ^ (d + 1))) := by
  classical
  set m := cofactorSupply R with hmdef
  set t := layerNodes d with htdef
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hlog5 : 0 < Real.log (5 * R) := Real.log_pos (by linarith)
  have hε1 : ε ≤ 1 := by
    refine hεw.trans ?_
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hmle : ∀ q ∈ F, (m q : ℝ) ≤ (R / q) ^ supplyExp / (16384 * Real.log (5 * R)) := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hF q hq).1.1
    have hr := Real.rpow_nonneg (div_nonneg hR0.le hq0.le) supplyExp
    have hx : 0 ≤ (R / q) ^ supplyExp / (32768 * Real.log (5 * R)) := by positivity
    refine (Nat.floor_le hx).trans ?_
    gcongr
    norm_num
  have ht : ∀ i, 0 ≤ t i ∧ t i + 1 / ((d : ℝ) + 2) ≤ 1 := layerNodes_bounds d
  have hHle : ∀ q ∈ F, (q : ℝ) * (4 * R / q) ^ supplyExp ≤ ε * L := fun q hq => (hF q hq).2.2.2
  have hHR : ∀ q ∈ F, (q : ℝ) * (4 * R / q) ^ supplyExp ≤ R := fun q hq => by
    have := hHle q hq
    nlinarith
  -- the prime families of each cofactor and window
  have hfam : ∀ q ∈ F, ∀ i : Fin (d + 1), ∃ eE eO : ℕ → ℕ,
      (∀ ℓ < m q, (eE ℓ).Prime ∧ R / q < (eE ℓ : ℝ) ∧ X + t i * L < ((2 * q * eE ℓ : ℕ) : ℝ) ∧
        ((2 * q * eE ℓ : ℕ) : ℝ) ≤ X + t i * L + q * (4 * R / q) ^ supplyExp) ∧
      (∀ ℓ < m q, ∀ ℓ' < m q, eE ℓ = eE ℓ' → ℓ = ℓ') ∧
      (∀ ℓ < m q, (eO ℓ).Prime ∧ 2 * R / q < (eO ℓ : ℝ) ∧ X + t i * L < ((q * eO ℓ : ℕ) : ℝ) ∧
        ((q * eO ℓ : ℕ) : ℝ) ≤ X + t i * L + q * (4 * R / q) ^ supplyExp) ∧
      (∀ ℓ < m q, ∀ ℓ' < m q, eO ℓ = eO ℓ' → ℓ = ℓ') := by
    intro q hq i
    obtain ⟨⟨hq1, -, -, -⟩, -, hz, -⟩ := hF q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hti := ht i
    have htL : 0 ≤ t i * L := mul_nonneg hti.1 hL.le
    have htL1 : t i * L ≤ L := by
      have : t i ≤ 1 := by have : 0 < 1 / ((d : ℝ) + 2) := by positivity
                           linarith [hti.2]
      nlinarith
    have hZ2 : 2 * R ≤ X + t i * L := by linarith
    have hZ4 : X + t i * L ≤ 4 * R := by linarith
    obtain ⟨htop1, htop2⟩ := window_tops_le hq1 (by linarith) hZ4 (hHR q hq)
    have hbase1 : R / q ≤ (X + t i * L) / q := div_le_div_of_nonneg_right (by linarith) hq0.le
    have hbase2 : R / q ≤ (X + t i * L) / (2 * q) := by
      rw [div_le_div_iff₀ hq0 (by positivity)]; nlinarith
    have hbase3 : 2 * R / q ≤ (X + t i * L) / q := div_le_div_of_nonneg_right hZ2 hq0.le
    obtain ⟨eO, hO, hOinj⟩ := exists_window_family hz₀ hsupply hR1 hz (m q) (hmle q hq) hbase1 htop1
    obtain ⟨eE, hE, hEinj⟩ := exists_window_family hz₀ hsupply hR1 hz (m q) (hmle q hq) hbase2 htop2
    refine ⟨eE, eO, fun ℓ hℓ => ?_, hEinj, fun ℓ hℓ => ?_, hOinj⟩
    · obtain ⟨hp, h1, h2⟩ := hE ℓ hℓ
      obtain ⟨a1, a2⟩ := cofactor_doubled_atoms hq1 (by linarith) hZ4 h1 h2
      exact ⟨hp, hbase2.trans_lt h1, a1, a2⟩
    · obtain ⟨hp, h1, h2⟩ := hO ℓ hℓ
      obtain ⟨a1, a2⟩ := cofactor_prime_atoms hq1 (by linarith) hZ4 h1 h2
      exact ⟨hp, hbase3.trans_lt h1, a1, a2⟩
  choose! eE eO hE hEinj hO hOinj using hfam
  set lab := familyLabels (d := d) F m with hlab
  have hlabmem : ∀ x ∈ lab, x.1 ∈ F ∧ x.2.2 < m x.1 := fun x hx => by
    rw [hlab, familyLabels, mem_sigma, mem_product, mem_range] at hx
    exact ⟨hx.1, hx.2.2⟩
  set a : Bool → (Σ _ : ℕ, Fin (d + 1) × ℕ) → ℕ :=
    fun σ x => orientedAtom σ x.1 (eE x.1 x.2.1 x.2.2) (eO x.1 x.2.1 x.2.2) with ha
  -- positions in the window
  have hpos : ∀ σ, ∀ x ∈ lab, X + t x.2.1 * L < (a σ x : ℝ) ∧
      (a σ x : ℝ) ≤ X + t x.2.1 * L + x.1 * (4 * R / x.1) ^ supplyExp := by
    intro σ x hx
    obtain ⟨hq, hℓ⟩ := hlabmem x hx
    simp only [ha, orientedAtom]
    split_ifs
    · exact ⟨(hE x.1 hq x.2.1 x.2.2 hℓ).2.2.1, (hE x.1 hq x.2.1 x.2.2 hℓ).2.2.2⟩
    · exact ⟨(hO x.1 hq x.2.1 x.2.2 hℓ).2.2.1, (hO x.1 hq x.2.1 x.2.2 hℓ).2.2.2⟩
  have hposε : ∀ σ, ∀ x ∈ lab, X + t x.2.1 * L < (a σ x : ℝ) ∧
      (a σ x : ℝ) ≤ X + t x.2.1 * L + ε * L := by
    intro σ x hx
    obtain ⟨h1, h2⟩ := hpos σ x hx
    exact ⟨h1, h2.trans (by linarith [hHle x.1 (hlabmem x hx).1])⟩
  have hbox : ∀ σ, ∀ x ∈ lab, X < (a σ x : ℝ) ∧ (a σ x : ℝ) < X + L := by
    intro σ x hx
    obtain ⟨h1, h2⟩ := hposε σ x hx
    have hti := ht x.2.1
    have htL : 0 ≤ t x.2.1 * L := mul_nonneg hti.1 hL.le
    have hεL : (t x.2.1 + ε) * L < L := by
      have : t x.2.1 + ε < 1 := by
        have : ε < 1 / ((d : ℝ) + 2) := by
          have : 1 / (2 * ((d : ℝ) + 2)) < 1 / ((d : ℝ) + 2) := by
            apply one_div_lt_one_div_of_lt (by positivity); linarith
          linarith
        linarith [hti.2]
      nlinarith
    constructor <;> nlinarith
  -- Möbius signs and shapes
  have harith : ∀ x ∈ lab, (eE x.1 x.2.1 x.2.2).Prime ∧ 2 < eE x.1 x.2.1 x.2.2 ∧
      ¬ eE x.1 x.2.1 x.2.2 ∣ x.1 ∧ (eO x.1 x.2.1 x.2.2).Prime ∧ 2 < eO x.1 x.2.1 x.2.2 ∧
      ¬ eO x.1 x.2.1 x.2.2 ∣ x.1 ∧ AtomShape R x.1 (2 * x.1 * eE x.1 x.2.1 x.2.2) ∧
      AtomShape R x.1 (x.1 * eO x.1 x.2.1 x.2.2) := by
    intro x hx
    obtain ⟨hq, hℓ⟩ := hlabmem x hx
    obtain ⟨⟨hq1, hqodd, hqsq, hqp⟩, hq2, -, -⟩ := hF x.1 hq
    have hq0 : (0 : ℝ) < x.1 := by exact_mod_cast hq1
    obtain ⟨hEp, hE1, -, -⟩ := hE x.1 hq x.2.1 x.2.2 hℓ
    obtain ⟨hOp, hO1, -, -⟩ := hO x.1 hq x.2.1 x.2.2 hℓ
    have hRq2 : R / x.1 ≤ 2 * R / x.1 := div_le_div_of_nonneg_right (by linarith) hq0.le
    have hO1' : R / x.1 < (eO x.1 x.2.1 x.2.2 : ℝ) := hRq2.trans_lt hO1
    have hprimes : ∀ s : ℕ, R / x.1 < (s : ℝ) → ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ x.1 → ℓ < s := by
      intro s hs ℓ hℓp hℓq
      have := hqp ℓ hℓp hℓq
      exact_mod_cast this.trans hs
    have hndvd : ∀ s : ℕ, s.Prime → R / x.1 < (s : ℝ) → ¬ s ∣ x.1 := by
      intro s hs hRs hdvd
      have := hqp s hs hdvd
      linarith
    have h2E : 2 < eE x.1 x.2.1 x.2.2 := by
      have : (2 : ℝ) < eE x.1 x.2.1 x.2.2 := by linarith
      exact_mod_cast this
    have h2O : 2 < eO x.1 x.2.1 x.2.2 := by
      have : (2 : ℝ) < eO x.1 x.2.1 x.2.2 := by linarith
      exact_mod_cast this
    exact ⟨hEp, h2E, hndvd _ hEp hE1, hOp, h2O, hndvd _ hOp hO1',
      ⟨_, hEp, h2E, hE1, hprimes _ hE1, Or.inl rfl⟩,
      ⟨_, hOp, h2O, hO1', hprimes _ hO1', Or.inr ⟨rfl, hO1⟩⟩⟩
  have hμ : ∀ σ, ∀ x ∈ lab, μ (a σ x) = if σ then 1 else -1 := by
    intro σ x hx
    obtain ⟨hq, -⟩ := hlabmem x hx
    obtain ⟨⟨-, hqodd, hqsq, -⟩, -, -, -⟩ := hF x.1 hq
    obtain ⟨hEp, h2E, hEd, hOp, -, hOd, -, -⟩ := harith x hx
    exact moebius_orientedAtom hqodd hqsq hEp h2E hEd hOp hOd
  have hshape : ∀ σ, ∀ x ∈ lab, AtomShape R x.1 (a σ x) := by
    intro σ x hx
    obtain ⟨-, -, -, -, -, -, hsE, hsO⟩ := harith x hx
    simp only [ha, orientedAtom]
    split_ifs
    · exact hsE
    · exact hsO
  -- injectivity
  have hinj : ∀ σ, Set.InjOn (a σ) ↑lab := by
    rintro σ ⟨q, i, ℓ⟩ hx ⟨q', i', ℓ'⟩ hx' he
    have hx0 : (⟨q, i, ℓ⟩ : Σ _ : ℕ, Fin (d + 1) × ℕ) ∈ lab := hx
    have hx0' : (⟨q', i', ℓ'⟩ : Σ _ : ℕ, Fin (d + 1) × ℕ) ∈ lab := hx'
    obtain ⟨hq, hℓ⟩ := hlabmem _ hx0
    obtain ⟨hq', hℓ'⟩ := hlabmem _ hx0'
    have hodd := (hF q hq).1.2.1
    have hodd' := (hF q' hq').1.2.1
    have hsh := hshape σ _ hx0
    have hsh' := hshape σ _ hx0'
    rw [he] at hsh
    have hqq : q = q' := cofactor_eq_of_shape hodd hodd' hsh hsh'
    subst hqq
    have hii : i = i' := by
      obtain ⟨p1, p2⟩ := hposε σ _ hx0
      obtain ⟨p3, p4⟩ := hposε σ _ hx0'
      rw [he] at p1 p2
      exact window_index_eq hL hεw p1 p2 p3 p4
    subst hii
    have hq0 : 0 < q := (hF q hq).1.1
    have hll : ℓ = ℓ' := by
      simp only [ha, orientedAtom] at he
      split_ifs at he
      · have h2q : 0 < 2 * q := by omega
        exact hEinj q hq i ℓ hℓ ℓ' hℓ' (Nat.eq_of_mul_eq_mul_left h2q he)
      · exact hOinj q hq i ℓ hℓ ℓ' hℓ' (Nat.eq_of_mul_eq_mul_left hq0 he)
    subst hll
    rfl
  -- normalized positions and window weights
  set u : Bool → (Σ _ : ℕ, Fin (d + 1) × ℕ) → ℝ := fun σ x => ((a σ x : ℝ) - X) / L with hu
  have hεw' : ε ≤ 1 / ((d : ℝ) + 2) := by
    refine hεw.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have huwin : ∀ σ, ∀ q ∈ F, ∀ i : Fin (d + 1), ∀ ℓ < m q,
      t i ≤ u σ ⟨q, (i, ℓ)⟩ ∧ u σ ⟨q, (i, ℓ)⟩ ≤ t i + ε := by
    intro σ q hq i ℓ hℓ
    have hmem : (⟨q, (i, ℓ)⟩ : Σ _ : ℕ, Fin (d + 1) × ℕ) ∈ lab := by
      rw [hlab, familyLabels, mem_sigma, mem_product, mem_range]
      exact ⟨hq, mem_univ _, hℓ⟩
    obtain ⟨p1, p2⟩ := hposε σ _ hmem
    simp only [hu]
    constructor
    · rw [le_div_iff₀ hL]; linarith
    · rw [div_le_iff₀ hL]; linarith
  have hu01 : ∀ σ, ∀ x ∈ lab, 0 ≤ u σ x ∧ u σ x ≤ 1 := by
    intro σ x hx
    obtain ⟨hq, hℓ⟩ := hlabmem x hx
    obtain ⟨h1, h2⟩ := huwin σ x.1 hq x.2.1 x.2.2 hℓ
    have hti := ht x.2.1
    exact ⟨hti.1.trans h1, h2.trans (by linarith [hti.2])⟩
  obtain ⟨wP, hwP, hmP, hmomP⟩ := exists_window_weights hd hε hε0.le hεw' F m (u true)
    (huwin true)
  obtain ⟨wN, hwN, hmN, hmomN⟩ := exists_window_weights hd hε hε0.le hεw' F m (u false)
    (huwin false)
  obtain ⟨TP, hTP, TN, hTN, hcP, hcN, hsel⟩ := exists_matched_selection lab lab (u true)
    (u false) wP wN d (∑ q ∈ F, m q) (hu01 true) (hu01 false) hwP hwN hmP hmN
    (fun j hj => by
      have e1 := hmomP ⟨j, hj⟩
      have e2 := hmomN ⟨j, hj⟩
      simp only at e1 e2
      rw [e1, e2])
  refine ⟨a true, a false, TP, hTP, TN, hTN, hcP, hcN, hinj true, hinj false,
    fun x hx => ⟨(hbox true x hx).1, (hbox true x hx).2, by rw [hμ true x hx]; rfl,
      (hlabmem x hx).1, hshape true x hx⟩,
    fun x hx => ⟨(hbox false x hx).1, (hbox false x hx).2, by rw [hμ false x hx]; rfl,
      (hlabmem x hx).1, hshape false x hx⟩, fun δ hδ0 hδ1 => ?_⟩
  -- the Taylor bound
  have hX0 : 0 < X := by linarith
  have hLX : L ≤ X := by linarith
  have h := gammaNorm_matched_block_le hδ0 hδ1 TP TN (fun x => (a true x : ℝ))
    (fun x => (a false x : ℝ)) hX0 hLX d
    (fun x hx => ⟨(hbox true x (hTP hx)).1.le, (hbox true x (hTP hx)).2.le⟩)
    (fun x hx => ⟨(hbox false x (hTN hx)).1.le, (hbox false x (hTN hx)).2.le⟩)
    (by rw [hcP, hcN])
    (fun j hj => by
      have hs := hsel j hj
      have e : ∀ T : Finset (Σ _ : ℕ, Fin (d + 1) × ℕ), ∀ σ,
          ∑ x ∈ T, ((a σ x : ℝ) - X) ^ (j + 1) = L ^ (j + 1) * ∑ x ∈ T, u σ x ^ (j + 1) := by
        intro T σ
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        simp only [hu]
        rw [div_pow]
        field_simp
      rw [e TP true, e TN false, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      calc L ^ (j + 1) * |∑ x ∈ TP, u true x ^ (j + 1) - ∑ x ∈ TN, u false x ^ (j + 1)|
          ≤ L ^ (j + 1) * 2 := by gcongr
        _ = 2 * L ^ (j + 1) := by ring)
  rw [hcP, hcN] at h
  convert h using 3
  push_cast
  ring

end RHTower.CubicGamma
