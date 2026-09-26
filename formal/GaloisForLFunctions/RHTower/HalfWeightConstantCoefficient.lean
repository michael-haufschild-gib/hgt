import GaloisForLFunctions.RHTower.HalfWeightCoefficientL
import GaloisForLFunctions.RHTower.HalfWeightConstantKernel

/-!
# The constant-term coefficient of the weight-½ Eisenstein series

For the trivial nebentypus the `n = 0` Fourier coefficient is
`D_0(w) = (i^{1/2}/√2) Σ_{4M ∣ c} (μ * N(0))(c) c^{1/2-2w}` (`Dser_one_eq_LSeries`).

* `sqCount_zero_prime_pow`: `N_{p^a}(0) = p^{⌊a/2⌋}`, since `p^a ∣ m² ↔ p^{⌈a/2⌉} ∣ m`.
* `fN_zero_eq`: `μ * N(0) = phiSq`, the totient of the square root on squares and `0` elsewhere.
* `mZero N`: the least positive `m₀` with `N ∣ m₀²`; `dvd_sq_iff`: `N ∣ m² ↔ m₀ ∣ m` (if `N ∣ a²` and
  `N ∣ b²` then `N ∣ ab`, so these `m` form an ideal); `prime_dvd_mZero_iff`: `m₀` and `N` have the
  same prime divisors.
* `hTot`: `h(k) = φ(k) g/φ(g)`, `g = gcd(m₀, k)`, is multiplicative with `φ(m₀k) = φ(m₀) h(k)`
  (`totient_mul_eq`), and `hTot_mul_chiZ`: `h ⍟ χ₀ = id` for the principal character `χ₀` mod `N`.
* `LSeries_chiZ`, `LSeries_idC`, `LSeries_hTot_mul`: `L(h,u) ζ(u) ∏_{p∣N}(1-p^{-u}) = ζ(u-1)`.
* `LSeries_sN`, `LSeries_gL_zero`: re-indexing `c = m²` and `m = m₀k`.

**`Dser_zero_mul`**: for `Re w > 3/4`,
`D_0(w) · ζ(4w-1) ∏_{p ∣ 2M} (1 - p^{1-4w}) = (i^{1/2}/√2) φ(m₀) m₀^{1-4w} ζ(4w-2)`, `m₀ = m₀(4M)`.

So `D_0` continues meromorphically: a pole at `w = 3/4` from `ζ(4w-2)`, and a zero at `w = 1/2`
from the pole of `ζ(4w-1)`, which cancels the pole of the kernel constant term
`y^{1-w} c_1(w)/(2w(2w-1))` (`HalfWeightConstantKernel`).
-/

open Real Complex ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

/-! ### Square roots of zero modulo prime powers -/

theorem pow_dvd_sq_iff {p : ℕ} (hp : p.Prime) (a m : ℕ) : p ^ a ∣ m ^ 2 ↔ p ^ ((a + 1) / 2) ∣ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero _ hm.ne'),
    hp.pow_dvd_iff_le_factorization hm.ne', Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  omega

/-- `N_{p^a}(0) = p^{⌊a/2⌋}`. -/
theorem sqCount_zero_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    sqCount 0 (p ^ a) = ((p ^ (a / 2) : ℕ) : ℂ) := by
  unfold sqCount
  have h : ∀ m : ℕ, (((p ^ a : ℕ) : ℤ) ∣ (0 : ℤ) - (m : ℤ) ^ 2) ↔ p ^ ((a + 1) / 2) ∣ m := by
    intro m
    rw [zero_sub, Int.dvd_neg, ← pow_dvd_sq_iff hp]
    exact_mod_cast Iff.rfl
  simp_rw [h]
  have he : p ^ ((a + 1) / 2) ∣ p ^ a := pow_dvd_pow p (by omega)
  rw [sum_range_dvd (pow_pos hp.pos _) he (fun _ => (1 : ℂ)), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, Nat.pow_div (by omega) hp.pos]
  congr 2; omega


/-! ### `μ * N(0)` is the totient on squares -/

open Classical in
/-- `φ(√c)` on squares, `0` elsewhere. -/
noncomputable def phiSq : ArithmeticFunction ℂ :=
  ⟨fun c => if IsSquare c then ((Nat.sqrt c).totient : ℂ) else 0, by simp⟩

open Classical in
theorem phiSq_apply (c : ℕ) : phiSq c = if IsSquare c then ((Nat.sqrt c).totient : ℂ) else 0 := rfl

theorem phiSq_sq (m : ℕ) : phiSq (m ^ 2) = (m.totient : ℂ) := by
  classical
  rw [phiSq_apply, if_pos ⟨m, by ring⟩, Nat.sqrt_eq']

theorem isMultiplicative_phiSq : phiSq.IsMultiplicative := by
  classical
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simpa using phiSq_sq 1, fun {a b} _ _ hab => ?_⟩
  by_cases hA : IsSquare a
  · by_cases hB : IsSquare b
    · obtain ⟨x, rfl⟩ := hA
      obtain ⟨y, rfl⟩ := hB
      have hxy : x.Coprime y := by
        have := Nat.Coprime.coprime_dvd_left (dvd_mul_right x x) hab
        exact Nat.Coprime.coprime_dvd_right (dvd_mul_right y y) this
      rw [show x * x * (y * y) = (x * y) ^ 2 by ring, show x * x = x ^ 2 by ring,
        show y * y = y ^ 2 by ring, phiSq_sq, phiSq_sq, phiSq_sq, Nat.totient_mul hxy]
      push_cast; ring
    · have hAB : ¬ IsSquare (a * b) := fun h => hB ((isSquare_mul_of_coprime hab).1 h).2
      rw [phiSq_apply, phiSq_apply b, if_neg hAB, if_neg hB, mul_zero]
  · have hAB : ¬ IsSquare (a * b) := fun h => hA ((isSquare_mul_of_coprime hab).1 h).1
    rw [phiSq_apply, phiSq_apply a, if_neg hAB, if_neg hA, zero_mul]

theorem phiSq_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    phiSq (p ^ a) = if Even a then ((p ^ (a / 2)).totient : ℂ) else 0 := by
  classical
  by_cases ha : Even a
  · obtain ⟨j, rfl⟩ := ha
    rw [if_pos ⟨j, rfl⟩, show p ^ (j + j) = (p ^ j) ^ 2 by ring, phiSq_sq]
    congr 3; omega
  · rw [phiSq_apply, if_neg ha, if_neg (fun h => ha ((isSquare_prime_pow_iff hp a).1 h))]

/-- **`μ * N(0) = φ(√·)`**: the `n = 0` coefficient function is the totient on squares. -/
theorem fN_zero_eq : fN 0 = phiSq := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_fN 0) _
    isMultiplicative_phiSq).2 ?_
  intro p a hp
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [pow_zero, (isMultiplicative_fN 0).map_one, isMultiplicative_phiSq.map_one]
  rw [fN, moebius_mul_prime_pow _ hp ha, Nfun_apply, Nfun_apply, sqCount_zero_prime_pow hp,
    sqCount_zero_prime_pow hp, phiSq_prime_pow hp]
  rcases Nat.even_or_odd a with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [if_pos ⟨j, rfl⟩, show (j + j) / 2 = j by omega, show (j + j - 1) / 2 = j - 1 by omega]
    have hj : 0 < j := by omega
    rw [Nat.totient_prime_pow hp hj]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hp1 : 1 ≤ p := hp.one_lt.le
    push_cast [hp1]
    ring
  · rw [if_neg (Nat.not_even_iff_odd.2 ⟨j, rfl⟩), show (2 * j + 1) / 2 = j by omega,
      show (2 * j + 1 - 1) / 2 = j by omega, sub_self]


/-! ### The least `m₀` with `N ∣ m₀²` -/

section SquareDivisor

variable (N : ℕ) [NeZero N]

theorem exists_dvd_sq : ∃ m, 0 < m ∧ N ∣ m ^ 2 :=
  ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), dvd_pow_self N two_ne_zero⟩

open Classical in
/-- `m₀(N)`: the least positive `m` with `N ∣ m²`. -/
noncomputable def mZero : ℕ := Nat.find (exists_dvd_sq N)

theorem mZero_pos : 0 < mZero N := by
  classical
  exact (Nat.find_spec (exists_dvd_sq N)).1

theorem dvd_mZero_sq : N ∣ mZero N ^ 2 := by
  classical
  exact (Nat.find_spec (exists_dvd_sq N)).2

/-- `N ∣ m² ↔ m₀ ∣ m`: the `m` with `N ∣ m²` form the ideal generated by `m₀`. -/
theorem dvd_sq_iff (m : ℕ) : N ∣ m ^ 2 ↔ mZero N ∣ m := by
  classical
  constructor
  · intro hm
    set m₀ := mZero N
    have hm₀ := dvd_mZero_sq N
    -- `N ∣ m m₀`, since `N² ∣ (m m₀)²`
    have hmm : N ∣ m * m₀ := by
      have h2 : N ^ 2 ∣ (m * m₀) ^ 2 := by rw [mul_pow, sq N]; exact Nat.mul_dvd_mul hm hm₀
      exact (Nat.pow_dvd_pow_iff two_ne_zero).1 h2
    set q := m / m₀
    set r := m % m₀
    have hqr : m = m₀ * q + r := (Nat.div_add_mod m m₀).symm
    have hr : N ∣ r * m₀ := by
      have : m * m₀ = q * m₀ ^ 2 + r * m₀ := by rw [hqr]; ring
      rw [this] at hmm
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_right hm₀ q)).1 hmm
    have hr2 : N ∣ r ^ 2 := by
      have : m ^ 2 = (q ^ 2 * m₀ ^ 2 + 2 * q * (r * m₀)) + r ^ 2 := by rw [hqr]; ring
      rw [this] at hm
      refine (Nat.dvd_add_right (dvd_add (dvd_mul_of_dvd_right hm₀ _)
        (dvd_mul_of_dvd_right hr _))).1 hm
    by_contra hnd
    have hr0 : 0 < r := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
    have hlt : r < m₀ := Nat.mod_lt m (mZero_pos N)
    exact Nat.find_min (exists_dvd_sq N) hlt ⟨hr0, hr2⟩
  · rintro ⟨k, rfl⟩
    rw [mul_pow]
    exact dvd_mul_of_dvd_left (dvd_mZero_sq N) _

theorem mZero_dvd : mZero N ∣ N := (dvd_sq_iff N N).1 (dvd_pow_self N two_ne_zero)

theorem prime_dvd_mZero_iff {p : ℕ} (hp : p.Prime) : p ∣ mZero N ↔ p ∣ N :=
  ⟨fun h => h.trans (mZero_dvd N), fun h => hp.dvd_of_dvd_pow (h.trans (dvd_mZero_sq N))⟩

end SquareDivisor


/-! ### `φ(m₀ k) = φ(m₀) h(k)` with `h` multiplicative -/

section Totient

variable (m₀ : ℕ)

/-- `h(k) = φ(k) g / φ(g)` with `g = gcd(m₀, k)`. -/
noncomputable def hTot : ArithmeticFunction ℂ :=
  ⟨fun k => (k.totient : ℂ) * (Nat.gcd m₀ k : ℂ) / ((Nat.gcd m₀ k).totient : ℂ), by simp⟩

theorem hTot_apply (k : ℕ) :
    hTot m₀ k = (k.totient : ℂ) * (Nat.gcd m₀ k : ℂ) / ((Nat.gcd m₀ k).totient : ℂ) := rfl

variable {m₀}

theorem totient_gcd_ne_zero (hm : 0 < m₀) (k : ℕ) : ((Nat.gcd m₀ k).totient : ℂ) ≠ 0 := by
  have : 0 < (Nat.gcd m₀ k).totient := Nat.totient_pos.2 (Nat.gcd_pos_of_pos_left _ hm)
  exact_mod_cast this.ne'

theorem totient_mul_eq (hm : 0 < m₀) (k : ℕ) :
    ((m₀ * k).totient : ℂ) = (m₀.totient : ℂ) * hTot m₀ k := by
  have h := Nat.totient_gcd_mul_totient_mul m₀ k
  have hC : ((Nat.gcd m₀ k).totient : ℂ) * ((m₀ * k).totient : ℂ) =
      (m₀.totient : ℂ) * (k.totient : ℂ) * (Nat.gcd m₀ k : ℂ) := by exact_mod_cast h
  have hne := totient_gcd_ne_zero hm k
  rw [hTot_apply]
  field_simp
  linear_combination hC

theorem isMultiplicative_hTot (hm : 0 < m₀) : (hTot m₀).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [hTot_apply], fun {a b} _ _ hab => ?_⟩
  have hg : Nat.gcd m₀ (a * b) = Nat.gcd m₀ a * Nat.gcd m₀ b := Nat.Coprime.gcd_mul m₀ hab
  have hcop : (Nat.gcd m₀ a).Coprime (Nat.gcd m₀ b) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) hab)
  have ha := totient_gcd_ne_zero hm a
  have hb := totient_gcd_ne_zero hm b
  simp only [hTot_apply]
  rw [hg, Nat.totient_mul hab, Nat.totient_mul hcop]
  push_cast
  field_simp

end Totient


/-! ### `h ⍟ χ₀ = id` -/

section Principal

variable (N : ℕ)

/-- The principal character modulo `N` as an arithmetic function. -/
noncomputable def chiZ : ArithmeticFunction ℂ :=
  ⟨fun c => if c ≠ 0 ∧ c.Coprime N then 1 else 0, by simp⟩

theorem chiZ_apply (c : ℕ) : chiZ N c = if c ≠ 0 ∧ c.Coprime N then 1 else 0 := rfl

theorem isMultiplicative_chiZ : (chiZ N).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [chiZ_apply], fun {a b} ha hb _ => ?_⟩
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  rw [chiZ_apply, chiZ_apply, chiZ_apply]
  by_cases hA : a.Coprime N <;> by_cases hB : b.Coprime N
  · rw [if_pos ⟨hab0, Nat.Coprime.mul_left hA hB⟩, if_pos ⟨ha, hA⟩, if_pos ⟨hb, hB⟩, mul_one]
  · rw [if_neg (show ¬(a * b ≠ 0 ∧ (a * b).Coprime N) from
      fun h => hB (Nat.Coprime.coprime_dvd_left (dvd_mul_left b a) h.2)),
      if_neg (show ¬(b ≠ 0 ∧ b.Coprime N) from fun h => hB h.2), mul_zero]
  · rw [if_neg (show ¬(a * b ≠ 0 ∧ (a * b).Coprime N) from
      fun h => hA (Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) h.2)),
      if_neg (show ¬(a ≠ 0 ∧ a.Coprime N) from fun h => hA h.2), zero_mul]
  · rw [if_neg (show ¬(a * b ≠ 0 ∧ (a * b).Coprime N) from
      fun h => hA (Nat.Coprime.coprime_dvd_left (dvd_mul_right a b) h.2)),
      if_neg (show ¬(a ≠ 0 ∧ a.Coprime N) from fun h => hA h.2), zero_mul]

/-- The identity as a complex arithmetic function. -/
noncomputable def idC : ArithmeticFunction ℂ := ⟨fun c => (c : ℂ), by simp⟩

theorem idC_apply (c : ℕ) : idC c = (c : ℂ) := rfl

theorem isMultiplicative_idC : idC.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  exact ⟨by simp [idC_apply], fun {a b} _ _ _ => by simp [idC_apply]⟩

variable [NeZero N]

theorem sum_totient_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), ((p ^ i).totient : ℂ) = ((p ^ j : ℕ) : ℂ) := by
  have h := Nat.sum_totient (p ^ j)
  rw [Nat.sum_divisors_prime_pow hp] at h
  exact_mod_cast h

/-- **`h ⍟ χ₀ = id`** for `m₀ = m₀(N)`. -/
theorem hTot_mul_chiZ : hTot (mZero N) * chiZ N = idC := by
  have hm := mZero_pos N
  have hmul := (isMultiplicative_hTot hm).mul (isMultiplicative_chiZ N)
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _ isMultiplicative_idC).2 ?_
  intro p j hp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => hTot (mZero N) a * chiZ N b),
    Nat.sum_divisors_prime_pow hp, idC_apply]
  by_cases hpN : p ∣ N
  · -- only the top term survives, and `h(p^j) = p^j`
    rw [Finset.sum_range_succ]
    have hz : ∀ i ∈ Finset.range j, hTot (mZero N) (p ^ i) * chiZ N (p ^ j / p ^ i) = 0 := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.pow_div hi.le hp.pos, chiZ_apply, if_neg, mul_zero]
      rintro ⟨_, hc⟩
      have := Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by omega)) hc
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 this hpN
    rw [Finset.sum_eq_zero hz, zero_add, Nat.div_self (pow_pos hp.pos j), chiZ_apply,
      if_pos ⟨one_ne_zero, Nat.coprime_one_left N⟩, mul_one, hTot_apply]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    obtain ⟨t, ht, hgt⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right (mZero N) (p ^ j))
    have ht1 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · exfalso
        have hpm : p ∣ mZero N := (prime_dvd_mZero_iff N hp).2 hpN
        have : p ∣ Nat.gcd (mZero N) (p ^ j) :=
          Nat.dvd_gcd hpm (dvd_pow_self p (by omega))
        rw [hgt, pow_zero] at this
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      · exact h
    rw [hgt, Nat.totient_prime_pow hp hj, Nat.totient_prime_pow hp ht1]
    have hp1 : (p : ℂ) - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, t = b + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast [hp.one_lt.le]
    field_simp
    ring
  · -- every term survives, and `h(p^i) = φ(p^i)`
    have hc : ∀ i, (p ^ i).Coprime N := fun i =>
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
    have hcm : ∀ i, Nat.gcd (mZero N) (p ^ i) = 1 := fun i =>
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2
        (fun h => hpN ((prime_dvd_mZero_iff N hp).1 h))).symm
    have hterm : ∀ i ∈ Finset.range (j + 1),
        hTot (mZero N) (p ^ i) * chiZ N (p ^ j / p ^ i) = ((p ^ i).totient : ℂ) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.pow_div (by omega) hp.pos, chiZ_apply,
        if_pos ⟨pow_ne_zero _ hp.ne_zero, hc _⟩, hTot_apply, hcm]
      simp
    rw [Finset.sum_congr rfl hterm, sum_totient_prime_pow hp]

end Principal


/-! ### Dirichlet series -/

section Series

variable (N : ℕ) [NeZero N]

/-- `Σ χ₀(n) n^{-u} = ζ(u) ∏_{p ∣ N} (1 - p^{-u})` for `Re u > 1`. -/
theorem LSeries_chiZ {u : ℂ} (hu : 1 < u.re) :
    LSeries (fun c => chiZ N c) u =
      riemannZeta u * ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-u)) := by
  have h := DirichletCharacter.LSeries_changeLevel (one_dvd N) (1 : DirichletCharacter ℂ 1) hu
  rw [DirichletCharacter.changeLevel_one] at h
  have h1 : ∀ n : ℕ, (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := fun n =>
    MulChar.one_apply (isUnit_of_subsingleton _)
  simp only [h1, one_mul] at h
  have hz : LSeries (fun _ : ℕ => (1 : ℂ)) u = riemannZeta u := by
    rw [← LSeries_zeta_eq_riemannZeta hu]
    exact LSeries_congr (fun {n} hn => by simp [ArithmeticFunction.zeta_apply, hn]) u
  rw [hz] at h
  rw [← h]
  refine LSeries_congr (fun {c} hc => ?_) u
  rw [chiZ_apply]
  by_cases hcop : c.Coprime N
  · rw [if_pos ⟨hc, hcop⟩, MulChar.one_apply ((ZMod.isUnit_iff_coprime c N).2 hcop)]
  · rw [if_neg (fun h => hcop h.2), MulChar.map_nonunit _
      (fun h => hcop ((ZMod.isUnit_iff_coprime c N).1 h))]

/-- `Σ n · n^{-u} = ζ(u-1)` for `Re u > 2`. -/
theorem LSeries_idC {u : ℂ} (hu : 2 < u.re) : LSeries (fun c => idC c) u = riemannZeta (u - 1) := by
  have hshift : 1 < (u - 1).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hshift]
  unfold LSeries
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [LSeries.term_zero]
    have hne : u - 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    simp [Complex.zero_cpow hne]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [LSeries.term_of_ne_zero hn.ne', idC_apply]
    have e : (n : ℂ) ^ u = (n : ℂ) ^ (u - 1) * n := by
      have := Complex.cpow_add (u - 1) 1 hnC
      rw [Complex.cpow_one, sub_add_cancel] at this
      exact this
    rw [e]
    have : (n : ℂ) ^ (u - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hnC h.1
    field_simp

theorem norm_hTot_le (k : ℕ) : ‖hTot (mZero N) k‖ ≤ (mZero N : ℝ) * k := by
  have hm := mZero_pos N
  have h := totient_mul_eq hm k
  have hφ : (1 : ℝ) ≤ (mZero N).totient := by exact_mod_cast Nat.totient_pos.2 hm
  have hφC : ((mZero N).totient : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (mZero N).totient := by linarith
    exact_mod_cast this.ne'
  have e : hTot (mZero N) k = ((mZero N * k).totient : ℂ) / ((mZero N).totient : ℂ) := by
    rw [h]; field_simp
  rw [e, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rw [div_le_iff₀ (by linarith)]
  have : ((mZero N * k).totient : ℝ) ≤ mZero N * k := by exact_mod_cast Nat.totient_le _
  nlinarith [this, (by positivity : (0 : ℝ) ≤ mZero N * k)]

theorem lseriesSummable_hTot {u : ℂ} (hu : 2 < u.re) :
    LSeriesSummable (fun k => hTot (mZero N) k) u := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hu ⟨mZero N, fun k _ => ?_⟩
  refine (norm_hTot_le N k).trans (le_of_eq ?_)
  norm_num

omit [NeZero N] in
theorem lseriesSummable_chiZ {u : ℂ} (hu : 1 < u.re) : LSeriesSummable (fun c => chiZ N c) u := by
  refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hu ⟨1, fun c _ => ?_⟩
  rw [chiZ_apply]
  split_ifs <;> simp

/-- `L(h, u) · ζ(u) ∏_{p∣N}(1 - p^{-u}) = ζ(u-1)` for `Re u > 2`. -/
theorem LSeries_hTot_mul {u : ℂ} (hu : 2 < u.re) :
    LSeries (fun k => hTot (mZero N) k) u *
      (riemannZeta u * ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-u))) = riemannZeta (u - 1) := by
  rw [← LSeries_chiZ N (by linarith), ← LSeries_mul' (lseriesSummable_hTot N hu)
    (lseriesSummable_chiZ N (by linarith)), hTot_mul_chiZ, LSeries_idC hu]

/-- `s_N(m) = φ(m)` if `N ∣ m²`, else `0`. -/
noncomputable def sN (m : ℕ) : ℂ := if N ∣ m ^ 2 then (m.totient : ℂ) else 0

/-- Re-indexing `m = m₀ k`: `L(s_N, u) = φ(m₀) m₀^{-u} L(h, u)`. -/
theorem LSeries_sN (u : ℂ) :
    LSeries (sN N) u = ((mZero N).totient : ℂ) * (mZero N : ℂ) ^ (-u) *
      LSeries (fun k => hTot (mZero N) k) u := by
  have hm := mZero_pos N
  have hinj : Function.Injective (fun k : ℕ => mZero N * k) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hm h
  have hsupp : Function.support (LSeries.term (sN N) u) ⊆ Set.range (fun k : ℕ => mZero N * k) := by
    intro c hc
    rw [Function.mem_support, LSeries.term_def] at hc
    split_ifs at hc with hc0
    · exact absurd rfl hc
    · by_cases hd : N ∣ c ^ 2
      · obtain ⟨k, hk⟩ := (dvd_sq_iff N c).1 hd
        exact ⟨k, hk.symm⟩
      · exact absurd (by simp [sN, hd]) hc
  unfold LSeries
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hmk : mZero N * k ≠ 0 := (Nat.mul_pos hm hk).ne'
  have hd : N ∣ (mZero N * k) ^ 2 := (dvd_sq_iff N _).2 (dvd_mul_right _ _)
  rw [LSeries.term_of_ne_zero hmk, LSeries.term_of_ne_zero hk.ne', sN, if_pos hd,
    totient_mul_eq hm k, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.cpow_neg]
  have h1 : (mZero N : ℂ) ^ u ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => (by exact_mod_cast hm.ne' : (mZero N : ℂ) ≠ 0) h.1
  have h2 : (k : ℂ) ^ u ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => (by exact_mod_cast hk.ne' : (k : ℂ) ≠ 0) h.1
  field_simp

end Series


/-! ### The `n = 0` coefficient of the weight-½ Eisenstein series -/

section ZeroCoefficient

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
/-- Re-indexing `c = m²`: `L(g_L^{(0)}, s) = L(s_{4M}, 2s)`. -/
theorem LSeries_gL_zero (s : ℂ) :
    LSeries (fun c => gL (n := 0) (M := M) c) s = LSeries (sN (4 * M)) (2 * s) := by
  classical
  have hinj : Function.Injective (fun m : ℕ => m ^ 2) := Nat.pow_left_injective two_ne_zero
  have hsupp : Function.support (LSeries.term (fun c => gL (n := 0) (M := M) c) s) ⊆
      Set.range (fun m : ℕ => m ^ 2) := by
    intro c hc
    rw [Function.mem_support, LSeries.term_def] at hc
    split_ifs at hc with hc0
    · exact absurd rfl hc
    · rw [gL_apply, fN_zero_eq] at hc
      by_cases h4 : 4 * M ∣ c
      · rw [if_pos h4, phiSq_apply] at hc
        by_cases hsq : IsSquare c
        · obtain ⟨r, hr⟩ := hsq
          exact ⟨r, by rw [hr]; ring⟩
        · rw [if_neg hsq, zero_div] at hc; exact absurd rfl hc
      · rw [if_neg h4, zero_div] at hc; exact absurd rfl hc
  unfold LSeries
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero _ hm.ne'
  rw [LSeries.term_of_ne_zero hm2, LSeries.term_of_ne_zero hm.ne', gL_apply, fN_zero_eq, sN]
  have hc : ((m ^ 2 : ℕ) : ℂ) ^ s = (m : ℂ) ^ (2 * s) := by
    rw [show (2 : ℂ) * s = ((2 : ℕ) : ℂ) * s by norm_num, Complex.natCast_cpow_natCast_mul]
    push_cast; ring_nf
  by_cases h4 : 4 * M ∣ m ^ 2
  · rw [if_pos h4, if_pos h4, phiSq_sq, hc]
  · rw [if_neg h4, if_neg h4, zero_div, zero_div]

/-- **The constant-term coefficient in closed form.** For `Re w > 3/4`, with `m₀ = m₀(4M)` the
least positive integer with `4M ∣ m₀²`:
`D_0(w) · ζ(4w-1) ∏_{p ∣ 2M} (1 - p^{1-4w}) = (i^{1/2}/√2) φ(m₀) m₀^{1-4w} ζ(4w-2)`. -/
theorem Dser_zero_mul {w : ℂ} (hw : 3 / 4 < w.re) :
    Dser M (1 : DirichletCharacter ℂ (4 * M)) 0 w *
        (riemannZeta (4 * w - 1) * ∏ p ∈ (4 * M).primeFactors, (1 - (p : ℂ) ^ (-(4 * w - 1)))) =
      I ^ (1 / 2 : ℂ) / Real.sqrt 2 * ((mZero (4 * M)).totient : ℂ) *
        (mZero (4 * M) : ℂ) ^ (-(4 * w - 1)) * riemannZeta (4 * w - 2) := by
  have hu : 2 < (4 * w - 1).re := by simp; linarith
  rw [Dser_one_eq_LSeries, LSeries_gL_zero, show 2 * (2 * w - 1 / 2) = 4 * w - 1 by ring,
    LSeries_sN, show (4 : ℂ) * w - 2 = 4 * w - 1 - 1 by ring,
    ← LSeries_hTot_mul (4 * M) hu]
  ring

end ZeroCoefficient
