import GaloisForLFunctions.RHTower.BourgainEisensteinDivisorCount
import Mathlib

/-!
# The norm count of the Eisenstein integers

The family of the continuation lives over `ℚ(√−3)`; its zeta function reaches `ζ` through the
count of Eisenstein integers of a given norm:

`#{z ∈ ℤ[ω] : N(z) = n} = 6 Σ_{d ∣ n} χ₃(d)`  (`card_normSet`),

`χ₃` the quadratic character modulo `3`.

Both `r(n)/6` and `a(n) = Σ_{d ∣ n} χ₃(d)` satisfy `F(1) = 1` and, for a prime `p` and `m ≥ 1`,
`F(pm) = (1 + χ₃(p)) F(m) − χ₃(p) F(m/p)` (the last term only when `p ∣ m`):
* `p ≡ 2 (mod 3)` stays prime, because the norm form `a² − ab + b²` is never `2` modulo `3`; every
  element of norm `pm` is `p` times an element of norm `m/p`;
* `3 = −ω²(1 − ω)²`: every element of norm `3m` is `1 − ω` times an element of norm `m`;
* `p ≡ 1 (mod 3)` divides `n² + n + 1 = (n − ω)(n − ω̄)` for some `n` and neither factor, so it is
  a norm `p = π π̄`; `π` and `π̄` are not associate (otherwise `π` divides its trace, and then
  `p ∣ 4`), and the elements of norm `pm` are the union of `π · r⁻¹(m)` and `π̄ · r⁻¹(m)`, which
  meet in `p · r⁻¹(m/p)`.
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm

open _root_.RHTower

local notation "𝔼" => RHTower.BourgainEisensteinInt
local notation "N" => RHTower.BourgainEisensteinInt.norm
local notation "cj" => RHTower.BourgainEisensteinInt.conj

/-- The Eisenstein integers of norm `n`. -/
noncomputable def normSet (n : ℕ) : Finset 𝔼 :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).image
    fun ab : ℤ × ℤ => (⟨ab.1, ab.2⟩ : 𝔼)).filter fun z => N z = n

theorem abs_le_of_three_mul_sq_le {a : ℤ} {n : ℕ} (h : 3 * a ^ 2 ≤ 4 * n) : |a| ≤ n := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  rw [abs_le]
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ -a - n - 1 by linarith)
      (show (0 : ℤ) ≤ -a + n + 1 by linarith)]
  · by_contra hlt
    rw [not_le] at hlt
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ a - n - 1 by linarith)
      (show (0 : ℤ) ≤ a + n + 1 by linarith)]

theorem mem_normSet {n : ℕ} {z : 𝔼} : z ∈ normSet n ↔ N z = n := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(z.re, z.im), ?_, rfl⟩, h⟩
    rw [BourgainEisensteinInt.norm_def] at h
    have h1 : 3 * z.re ^ 2 ≤ 4 * (n : ℤ) := by nlinarith [sq_nonneg (z.re - 2 * z.im)]
    have h2 : 3 * z.im ^ 2 ≤ 4 * (n : ℤ) := by nlinarith [sq_nonneg (2 * z.re - z.im)]
    obtain ⟨l1, u1⟩ := abs_le.mp (abs_le_of_three_mul_sq_le h1)
    obtain ⟨l2, u2⟩ := abs_le.mp (abs_le_of_three_mul_sq_le h2)
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨l1, u1⟩, ⟨l2, u2⟩⟩

theorem card_normSet_one : (normSet 1).card = 6 := by decide

theorem conj_dvd_of_dvd {x t : 𝔼} (h : x ∣ cj t) : cj x ∣ t := by
  obtain ⟨c, hc⟩ := h
  exact ⟨cj c, by rw [← BourgainEisensteinInt.conj_conj t, hc, BourgainEisensteinInt.conj_mul]⟩

theorem conj_natCast (p : ℕ) : cj (p : 𝔼) = p := by
  ext <;> simp [BourgainEisensteinInt.conj]

theorem norm_conj (x : 𝔼) : N (cj x) = N x := by
  simp only [BourgainEisensteinInt.norm_def, BourgainEisensteinInt.re_conj,
    BourgainEisensteinInt.im_conj]
  ring

theorem natCast_dvd_mul_conj {t : 𝔼} {p m : ℕ} (ht : N t = ((p * m : ℕ) : ℤ)) :
    (p : 𝔼) ∣ t * cj t := by
  rw [BourgainEisensteinInt.mul_conj, ht]
  exact ⟨m, by push_cast; ring⟩

/-- If `w` has norm `q`, multiplication by `w` maps norm `m` to norm `q m`. -/
theorem mul_mem_normSet {w z : 𝔼} {q m : ℕ} (hw : N w = q) (hz : z ∈ normSet m) :
    w * z ∈ normSet (q * m) := by
  rw [mem_normSet] at hz ⊢
  rw [BourgainEisensteinInt.norm_mul, hw, hz]
  push_cast
  ring

/-- If `t = w z` has norm `q m` with `w` of norm `q > 0`, then `z` has norm `m`. -/
theorem mem_normSet_of_mul {w z : 𝔼} {q m : ℕ} (hq : 0 < q) (hw : N w = q)
    (ht : w * z ∈ normSet (q * m)) : z ∈ normSet m := by
  rw [mem_normSet, BourgainEisensteinInt.norm_mul, hw] at ht
  rw [mem_normSet]
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast at ht
  exact mul_left_cancel₀ hq' ht

/-- The norm of `p w` is `p m` iff `p ∣ m` and `w` has norm `m/p`. -/
theorem mem_normSet_natCast_mul {p m : ℕ} (hp : 0 < p) {w : 𝔼} :
    (p : 𝔼) * w ∈ normSet (p * m) ↔ p ∣ m ∧ w ∈ normSet (m / p) := by
  rw [mem_normSet, mem_normSet, BourgainEisensteinInt.norm_mul,
    BourgainEisensteinInt.norm_natCast]
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro h
    have h1 : (p : ℤ) * N w = m := by
      push_cast at h
      exact mul_left_cancel₀ hp' (by linear_combination h)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (BourgainEisensteinInt.norm_nonneg w)
    rw [hk] at h1
    have h2 : p * k = m := by exact_mod_cast h1
    refine ⟨⟨k, h2.symm⟩, ?_⟩
    rw [hk, ← h2, Nat.mul_div_cancel_left k hp]
  · rintro ⟨⟨k, rfl⟩, h⟩
    rw [Nat.mul_div_cancel_left k hp] at h
    rw [h]
    push_cast
    ring

theorem isUnit_iff_norm_eq_one {z : 𝔼} : IsUnit z ↔ N z = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact BourgainEisensteinInt.norm_coe_unit u
  · exact eisenstein_isUnit_of_norm_eq_one

theorem prime_of_norm_prime {π : 𝔼} {p : ℕ} (hp : p.Prime) (hπ : N π = p) : Prime π := by
  refine irreducible_iff_prime.mp ⟨?_, ?_⟩
  · intro hu
    have := isUnit_iff_norm_eq_one.mp hu
    rw [hπ] at this
    exact hp.one_lt.ne' (by exact_mod_cast this)
  · intro x y hxy
    have hn : N x * N y = p := by rw [← BourgainEisensteinInt.norm_mul, ← hxy, hπ]
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (BourgainEisensteinInt.norm_nonneg x)
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (BourgainEisensteinInt.norm_nonneg y)
    rw [ha, hb] at hn
    have hab : a * b = p := by exact_mod_cast hn
    rcases (Nat.prime_mul_iff.mp (hab ▸ hp)) with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact Or.inr (isUnit_iff_norm_eq_one.mpr (by rw [hb, h1]; rfl))
    · exact Or.inl (isUnit_iff_norm_eq_one.mpr (by rw [ha, h1]; rfl))

/-! ### `p ≡ 2 (mod 3)` -/

/-- The norm form is never `2` modulo `3`. -/
theorem norm_emod_three_ne_two (z : 𝔼) : N z % 3 ≠ 2 := by
  intro h
  have key : ∀ a b : ZMod 3, a ^ 2 - a * b + b ^ 2 - 2 ≠ 0 := by decide
  apply key (z.re : ZMod 3) (z.im : ZMod 3)
  have hdvd : (3 : ℤ) ∣ N z - 2 := by omega
  have hz : ((N z - 2 : ℤ) : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hdvd
  rw [BourgainEisensteinInt.norm_def] at hz
  push_cast at hz
  exact hz

theorem prime_natCast_of_mod_three_eq_two {p : ℕ} (hp : p.Prime) (h2 : p % 3 = 2) :
    Prime (p : 𝔼) := by
  refine irreducible_iff_prime.mp ⟨?_, ?_⟩
  · intro hu
    have := isUnit_iff_norm_eq_one.mp hu
    rw [BourgainEisensteinInt.norm_natCast] at this
    have h1 : p ^ 2 = 1 := by exact_mod_cast this
    have := hp.one_lt
    nlinarith
  · intro x y hxy
    have hn : N x * N y = (p : ℤ) ^ 2 := by
      rw [← BourgainEisensteinInt.norm_mul, ← hxy, BourgainEisensteinInt.norm_natCast]
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (BourgainEisensteinInt.norm_nonneg x)
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (BourgainEisensteinInt.norm_nonneg y)
    rw [ha, hb] at hn
    have hab : a * b = p ^ 2 := by exact_mod_cast hn
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨b, hab.symm⟩
    interval_cases k
    · exact Or.inl (isUnit_iff_norm_eq_one.mpr (by rw [ha]; simp))
    · exfalso
      apply norm_emod_three_ne_two x
      rw [ha]
      simp only [pow_one]
      omega
    · have hb1 : b = 1 :=
        Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [hab, mul_one])
      exact Or.inr (isUnit_iff_norm_eq_one.mpr (by rw [hb, hb1]; rfl))

theorem natCast_dvd_of_two {p m : ℕ} (hp : p.Prime) (hp2 : p % 3 = 2) {t : 𝔼}
    (ht : t ∈ normSet (p * m)) : (p : 𝔼) ∣ t := by
  have hprime := prime_natCast_of_mod_three_eq_two hp hp2
  rcases hprime.dvd_or_dvd (natCast_dvd_mul_conj (mem_normSet.mp ht)) with h | h
  · exact h
  · have := conj_dvd_of_dvd h
    rwa [conj_natCast] at this

theorem card_normSet_mul_of_two {p : ℕ} (hp : p.Prime) (hp2 : p % 3 = 2) (m : ℕ) :
    (normSet (p * m)).card = if p ∣ m then (normSet (m / p)).card else 0 := by
  have hp0 : (p : 𝔼) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : normSet (p * m) = if p ∣ m then (normSet (m / p)).image ((p : 𝔼) * ·) else ∅ := by
    ext t
    constructor
    · intro ht
      obtain ⟨w, rfl⟩ := natCast_dvd_of_two hp hp2 ht
      obtain ⟨hdvd, hw⟩ := (mem_normSet_natCast_mul hp.pos).mp ht
      rw [if_pos hdvd]
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    · intro ht
      split_ifs at ht with hdvd
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
        exact (mem_normSet_natCast_mul hp.pos).mpr ⟨hdvd, hw⟩
      · simp at ht
  rw [e]
  split_ifs
  · exact Finset.card_image_of_injective _ (mul_right_injective₀ hp0)
  · rfl

/-! ### `p = 3` -/

/-- The prime `1 − ω` above `3`. -/
def lam : 𝔼 := ⟨1, -1⟩

theorem norm_lam : N lam = ((3 : ℕ) : ℤ) := by decide

theorem lam_dvd_three : lam ∣ ((3 : ℕ) : 𝔼) :=
  ⟨cj lam, by rw [BourgainEisensteinInt.mul_conj, norm_lam]; push_cast; rfl⟩

theorem lam_dvd_conj_lam : lam ∣ cj lam := ⟨⟨1, 1⟩, by decide⟩

theorem lam_dvd {m : ℕ} {t : 𝔼} (ht : t ∈ normSet (3 * m)) : lam ∣ t := by
  have hprime := prime_of_norm_prime Nat.prime_three norm_lam
  rcases hprime.dvd_or_dvd (lam_dvd_three.trans (natCast_dvd_mul_conj (mem_normSet.mp ht)))
    with h | h
  · exact h
  · exact lam_dvd_conj_lam.trans (conj_dvd_of_dvd h)

theorem card_normSet_three_mul (m : ℕ) : (normSet (3 * m)).card = (normSet m).card := by
  have h0 : lam ≠ 0 := by decide
  have e : normSet (3 * m) = (normSet m).image (lam * ·) := by
    ext t
    constructor
    · intro ht
      obtain ⟨z, rfl⟩ := lam_dvd ht
      exact Finset.mem_image.mpr ⟨z, mem_normSet_of_mul three_pos norm_lam ht, rfl⟩
    · intro ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
      exact mul_mem_normSet norm_lam hz
  rw [e, Finset.card_image_of_injective _ (mul_right_injective₀ h0)]

/-! ### `p ≡ 1 (mod 3)` -/

/-- A prime `p ≡ 1 (mod 3)` divides `n² + n + 1` for some integer `n`. -/
theorem exists_dvd_sq_add_self_add_one (p : ℕ) [Fact p.Prime] (h1 : p % 3 = 1) :
    ∃ n : ℤ, (p : ℤ) ∣ n ^ 2 + n + 1 := by
  have hcard : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units]
    omega
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hy3 : ((g : ZMod p)) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have hy1 : (g : ZMod p) ≠ 1 := by
    intro h
    have hg1 : g = 1 := Units.ext h
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hzero : (g : ZMod p) ^ 2 + (g : ZMod p) + 1 = 0 := by
    have hfac : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + (g : ZMod p) + 1) = 0 := by
      have : ((g : ZMod p) - 1) * ((g : ZMod p) ^ 2 + (g : ZMod p) + 1)
          = (g : ZMod p) ^ 3 - 1 := by ring
      rw [this, hy3, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hy1)
  refine ⟨((g : ZMod p).val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hzero

/-- A prime `p ≡ 1 (mod 3)` is a norm. -/
theorem exists_norm_eq_of_mod_three_eq_one {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1) :
    ∃ π : 𝔼, N π = p := by
  haveI := Fact.mk hp
  obtain ⟨n, k, hk⟩ := exists_dvd_sq_add_self_add_one p h1
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  -- `p` divides `(n − ω)(n − ω̄)`
  have hnx : N (⟨n, -1⟩ : 𝔼) = n ^ 2 + n + 1 := by
    rw [BourgainEisensteinInt.norm_def]
    ring
  have hdvd : (p : 𝔼) ∣ (⟨n, -1⟩ : 𝔼) * cj ⟨n, -1⟩ := by
    rw [BourgainEisensteinInt.mul_conj, hnx, hk]
    exact ⟨(k : 𝔼), by push_cast; ring⟩
  -- and neither factor: their `ω`-coordinates are `∓1`
  have hndvd : ∀ w : 𝔼, (w.im = 1 ∨ w.im = -1) → ¬ (p : 𝔼) ∣ w := by
    rintro w hw ⟨c, hc⟩
    have him := congrArg BourgainEisensteinInt.im hc
    simp only [BourgainEisensteinInt.im_mul, BourgainEisensteinInt.re_natCast,
      BourgainEisensteinInt.im_natCast, zero_mul, add_zero, sub_zero] at him
    rcases hw with h | h <;> rw [h] at him
    · exact absurd (Int.le_of_dvd one_pos ⟨c.im, him⟩) (not_le.mpr hp1)
    · exact absurd (Int.le_of_dvd one_pos ⟨-c.im, by linarith⟩) (not_le.mpr hp1)
  have hnotprime : ¬ Prime (p : 𝔼) := by
    intro hprime
    rcases hprime.dvd_or_dvd hdvd with h | h
    · exact hndvd _ (Or.inr rfl) h
    · exact hndvd _ (Or.inl (by simp)) h
  have hnu : ¬ IsUnit (p : 𝔼) := by
    intro hu
    have := isUnit_iff_norm_eq_one.mp hu
    rw [BourgainEisensteinInt.norm_natCast] at this
    nlinarith
  -- so `p` factors into two non-units, each of norm `p`
  have hex : ∃ a b : 𝔼, (p : 𝔼) = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    by_contra hcon
    apply hnotprime
    refine irreducible_iff_prime.mp (irreducible_iff.mpr ⟨hnu, fun a b hab => ?_⟩)
    by_contra hor
    rw [not_or] at hor
    exact hcon ⟨a, b, hab, hor.1, hor.2⟩
  obtain ⟨a, b, hab, hna, hnb⟩ := hex
  have hnorm : N a * N b = (p : ℤ) ^ 2 := by
    rw [← BourgainEisensteinInt.norm_mul, ← hab, BourgainEisensteinInt.norm_natCast]
  obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le (BourgainEisensteinInt.norm_nonneg a)
  obtain ⟨v, hv⟩ := Int.eq_ofNat_of_zero_le (BourgainEisensteinInt.norm_nonneg b)
  rw [hu, hv] at hnorm
  have huv : u * v = p ^ 2 := by exact_mod_cast hnorm
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨v, huv.symm⟩
  interval_cases j
  · exact absurd (isUnit_iff_norm_eq_one.mpr (by rw [hu]; simp)) hna
  · exact ⟨a, by rw [hu]; simp⟩
  · have hv1 : v = 1 := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [huv, mul_one])
    exact absurd (isUnit_iff_norm_eq_one.mpr (by rw [hv, hv1]; rfl)) hnb

/-- An element of prime norm `p ≡ 1 (mod 3)` does not divide its conjugate. -/
theorem not_dvd_conj_of_norm_prime {π : 𝔼} {p : ℕ} (hp : p.Prime) (h1 : p % 3 = 1)
    (hπ : N π = p) : ¬ π ∣ cj π := by
  intro hdvd
  -- `π` divides its trace `2a − b`
  have htr : π + cj π = ((2 * π.re - π.im : ℤ) : 𝔼) := by
    ext
    · simp only [BourgainEisensteinInt.re_add, BourgainEisensteinInt.re_conj,
        BourgainEisensteinInt.re_intCast]
      ring
    · simp only [BourgainEisensteinInt.im_add, BourgainEisensteinInt.im_conj,
        BourgainEisensteinInt.im_intCast]
      ring
  obtain ⟨c, hc⟩ : π ∣ ((2 * π.re - π.im : ℤ) : 𝔼) := by
    rw [← htr]
    exact dvd_add dvd_rfl hdvd
  have hn := congrArg N hc
  rw [BourgainEisensteinInt.norm_intCast, BourgainEisensteinInt.norm_mul, hπ] at hn
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpt2 : (p : ℤ) ∣ (2 * π.re - π.im) ^ 2 := ⟨N c, hn⟩
  have hpt : (p : ℤ) ∣ 2 * π.re - π.im := hpZ.dvd_of_dvd_pow hpt2
  have h4 := BourgainEisensteinInt.four_mul_norm π
  rw [hπ] at h4
  -- `p ∣ 3b²`, hence `p ∣ b`
  have hp3b : (p : ℤ) ∣ 3 * π.im ^ 2 := by
    have : 3 * π.im ^ 2 = 4 * (p : ℤ) - (2 * π.re - π.im) ^ 2 := by linarith
    rw [this]
    exact dvd_sub (Dvd.intro_left 4 rfl) hpt2
  have hpb : (p : ℤ) ∣ π.im := by
    rcases hpZ.dvd_or_dvd hp3b with h | h
    · exfalso
      have h3 : p ∣ 3 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
    · exact hpZ.dvd_of_dvd_pow h
  obtain ⟨t', ht'⟩ := hpt
  obtain ⟨b', hb'⟩ := hpb
  rw [ht', hb'] at h4
  -- `4p = p²(t'² + 3b'²)`, so `p ∣ 4`
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h4' : (4 : ℤ) = p * (t' ^ 2 + 3 * b' ^ 2) :=
    mul_left_cancel₀ hp0 (by linear_combination h4)
  have hp4z : (p : ℤ) ∣ ((4 : ℕ) : ℤ) := ⟨t' ^ 2 + 3 * b' ^ 2, by push_cast; exact h4'⟩
  have hp4 : p ∣ 4 := Int.natCast_dvd_natCast.mp hp4z
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp4
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem card_normSet_mul_of_one {p : ℕ} (hp : p.Prime) (hp1 : p % 3 = 1) (m : ℕ) :
    ((normSet (p * m)).card : ℤ) =
      2 * (normSet m).card - if p ∣ m then ((normSet (m / p)).card : ℤ) else 0 := by
  have hp0 := hp.pos
  obtain ⟨π, hnπ⟩ := exists_norm_eq_of_mod_three_eq_one hp hp1
  have hnπ' : N (cj π) = p := by rw [norm_conj, hnπ]
  have hπ := prime_of_norm_prime hp hnπ
  have hπ' := prime_of_norm_prime hp hnπ'
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπ'0 : cj π ≠ 0 := hπ'.ne_zero
  have hpp : π * cj π = (p : 𝔼) := by
    rw [BourgainEisensteinInt.mul_conj, hnπ]
    push_cast
    rfl
  have hnd : ¬ π ∣ cj π := not_dvd_conj_of_norm_prime hp hp1 hnπ
  have hnd' : ¬ cj π ∣ π := fun h => hnd (by
    have h' : cj π ∣ cj (cj π) := by rwa [BourgainEisensteinInt.conj_conj]
    simpa using conj_dvd_of_dvd h')
  -- the elements of norm `pm` are `π · r⁻¹(m) ∪ π̄ · r⁻¹(m)`
  set A := (normSet m).image (π * ·)
  set B := (normSet m).image (cj π * ·)
  have hU : normSet (p * m) = A ∪ B := by
    ext t
    constructor
    · intro ht
      have hdiv : π ∣ t * cj t :=
        (Dvd.intro _ hpp).trans (natCast_dvd_mul_conj (mem_normSet.mp ht))
      rcases hπ.dvd_or_dvd hdiv with h | h
      · obtain ⟨z, rfl⟩ := h
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨z, mem_normSet_of_mul hp0 hnπ ht, rfl⟩)
      · obtain ⟨z, rfl⟩ := conj_dvd_of_dvd h
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨z, mem_normSet_of_mul hp0 hnπ' ht, rfl⟩)
    · intro ht
      rcases Finset.mem_union.mp ht with h | h
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        exact mul_mem_normSet hnπ hz
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        exact mul_mem_normSet hnπ' hz
  -- and the two parts meet in `p · r⁻¹(m/p)`
  have hI : A ∩ B = if p ∣ m then (normSet (m / p)).image ((p : 𝔼) * ·) else ∅ := by
    ext t
    constructor
    · intro ht
      obtain ⟨hA, hB⟩ := Finset.mem_inter.mp ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨z', _, hz'⟩ := Finset.mem_image.mp hB
      have hdz : cj π ∣ π * z := ⟨z', hz'.symm⟩
      rcases hπ'.dvd_or_dvd hdz with h | h
      · exact absurd h hnd'
      · obtain ⟨w, rfl⟩ := h
        have ht' : (p : 𝔼) * w ∈ normSet (p * m) := by
          rw [← hpp, mul_assoc]
          exact mul_mem_normSet hnπ hz
        obtain ⟨hdvd, hw⟩ := (mem_normSet_natCast_mul hp0).mp ht'
        rw [if_pos hdvd]
        exact Finset.mem_image.mpr ⟨w, hw, by rw [← hpp, mul_assoc]⟩
    · intro ht
      split_ifs at ht with hdvd
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨k, rfl⟩ := hdvd
        rw [Nat.mul_div_cancel_left k hp0] at hw
        refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨cj π * w, ?_, ?_⟩,
          Finset.mem_image.mpr ⟨π * w, ?_, ?_⟩⟩
        · exact mul_mem_normSet hnπ' hw
        · rw [← hpp]; ring
        · exact mul_mem_normSet hnπ hw
        · rw [← hpp]; ring
      · simp at ht
  have hcard := Finset.card_union_add_card_inter A B
  rw [← hU, hI] at hcard
  have hA : A.card = (normSet m).card :=
    Finset.card_image_of_injective _ (mul_right_injective₀ hπ0)
  have hB : B.card = (normSet m).card :=
    Finset.card_image_of_injective _ (mul_right_injective₀ hπ'0)
  have hp0' : (p : 𝔼) ≠ 0 := by exact_mod_cast hp.ne_zero
  split_ifs at hcard ⊢ with hdvd
  · rw [Finset.card_image_of_injective _ (mul_right_injective₀ hp0'), hA, hB] at hcard
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    push_cast at h
    linarith
  · rw [Finset.card_empty, hA, hB] at hcard
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    push_cast at h
    linarith

/-! ### The divisor sums -/

/-- The quadratic character modulo `3` on the natural numbers. -/
def chi3 (n : ℕ) : ℤ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

theorem chi3_mul (a b : ℕ) : chi3 (a * b) = chi3 a * chi3 b := by
  unfold chi3
  have ha : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hb : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [Nat.mul_mod]
  interval_cases a % 3 <;> interval_cases b % 3 <;> simp

/-- `a(n) = Σ_{d ∣ n} χ₃(d)`. -/
def divisorChar (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi3 d

theorem divisorChar_one : divisorChar 1 = 1 := by
  simp [divisorChar, chi3]

theorem divisorChar_prime_mul {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 0 < m) :
    divisorChar (p * m) =
      (1 + chi3 p) * divisorChar m - chi3 p * (if p ∣ m then divisorChar (m / p) else 0) := by
  have hp0 := hp.pos
  have hU : (p * m).divisors = m.divisors ∪ m.divisors.image (p * ·) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, -⟩
      by_cases hpd : p ∣ d
      · obtain ⟨e, rfl⟩ := hpd
        exact Or.inr ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp0 hd, hm.ne'⟩, rfl⟩
      · exact Or.inl ⟨((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd).symm.dvd_of_dvd_mul_left hd,
          hm.ne'⟩
    · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
      · exact ⟨Dvd.dvd.mul_left hd p, (Nat.mul_pos hp0 hm).ne'⟩
      · exact ⟨Nat.mul_dvd_mul_left p he, (Nat.mul_pos hp0 hm).ne'⟩
  have hI : m.divisors ∩ m.divisors.image (p * ·) =
      if p ∣ m then (m / p).divisors.image (p * ·) else ∅ := by
    ext d
    simp only [Finset.mem_inter, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, -⟩, e, -, rfl⟩
      have hpm : p ∣ m := (Dvd.intro e rfl).trans hd
      rw [if_pos hpm]
      obtain ⟨k, rfl⟩ := hpm
      rw [Nat.mul_div_cancel_left k hp0]
      simp only [Finset.mem_image, Nat.mem_divisors]
      exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hp0 hd, by
        rintro rfl; simp at hm⟩, rfl⟩
    · intro h
      split_ifs at h with hpm
      · simp only [Finset.mem_image, Nat.mem_divisors] at h
        obtain ⟨e, ⟨he, -⟩, rfl⟩ := h
        obtain ⟨k, rfl⟩ := hpm
        rw [Nat.mul_div_cancel_left k hp0] at he
        exact ⟨⟨Nat.mul_dvd_mul_left p he, hm.ne'⟩, e,
          ⟨he.trans (Dvd.intro_left p rfl), hm.ne'⟩, rfl⟩
      · simp at h
  have hsum : ∀ D : Finset ℕ, ∑ d ∈ D.image (p * ·), chi3 d = chi3 p * ∑ d ∈ D, chi3 d :=
    fun D => by
      rw [Finset.sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp0 h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => chi3_mul p d
  have h := Finset.sum_union_inter (s₁ := m.divisors) (s₂ := m.divisors.image (p * ·))
    (f := fun d => chi3 d)
  rw [← hU, hI, hsum] at h
  unfold divisorChar
  split_ifs at h ⊢ with hpm
  · rw [hsum] at h
    linarith
  · simp only [Finset.sum_empty, add_zero] at h
    linarith

/-! ### The count -/

theorem card_normSet_prime_mul {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ((normSet (p * m)).card : ℤ) = (1 + chi3 p) * (normSet m).card -
      chi3 p * (if p ∣ m then ((normSet (m / p)).card : ℤ) else 0) := by
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h0 | h1 | h2
  · have hp3 : p = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    subst hp3
    rw [card_normSet_three_mul]
    have : chi3 3 = 0 := by decide
    rw [this]
    ring
  · rw [card_normSet_mul_of_one hp h1]
    have : chi3 p = 1 := by unfold chi3; rw [if_pos h1]
    rw [this]
    ring
  · rw [card_normSet_mul_of_two hp h2]
    have : chi3 p = -1 := by unfold chi3; rw [if_neg (by omega), if_pos h2]
    rw [this]
    split_ifs <;> push_cast <;> ring

/-- **The norm count**: `#{z ∈ ℤ[ω] : N(z) = n} = 6 Σ_{d ∣ n} χ₃(d)` for `n ≥ 1`. -/
theorem card_normSet {n : ℕ} (hn : 0 < n) : ((normSet n).card : ℤ) = 6 * divisorChar n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [card_normSet_one, divisorChar_one]
      norm_num
    set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
    have hmn : m < n := by
      rw [hm]
      exact lt_mul_left hm0 hp.one_lt
    rw [hm, card_normSet_prime_mul hp, divisorChar_prime_mul hp hm0, ih m hmn hm0]
    split_ifs with hpm
    · have hq0 : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm0 hpm) hp.pos
      rw [ih (m / p) ((Nat.div_le_self m p).trans_lt hmn) hq0]
      ring
    · ring

end GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm
