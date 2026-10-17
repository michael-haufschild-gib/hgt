import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Data.Int.Interval

/-!
# Jacobi's two-square count

The number of Gaussian integers of norm `n ≥ 1` is `4 Σ_{d ∣ n} χ₄(d)` (`card_normSet`).

Both `r(n)/4` and `a(n) = Σ_{d ∣ n} χ₄(d)` satisfy `F(1) = 1` and, for every prime `p` and `m ≥ 1`,
`F(pm) = (1 + χ₄(p)) F(m) − χ₄(p) F(m/p)` (the last term only when `p ∣ m`):
* `p ≡ 3 (mod 4)` is a Gaussian prime, so every element of norm `pm` is `p` times an element of norm
  `m/p` (`card_normSet_mul_of_three`);
* `2 = −i(1+i)²`, so every element of norm `2m` is `(1+i)` times an element of norm `m`
  (`card_normSet_two_mul`);
* `p ≡ 1 (mod 4)` splits as `p = π π̄` with non-associate Gaussian primes, and the elements of norm
  `pm` are the union of `π·r⁻¹(m)` and `π̄·r⁻¹(m)`, which meet in `p·r⁻¹(m/p)`
  (`card_normSet_mul_of_one`);
* for the divisor sums the same inclusion–exclusion holds for `divisors(pm) = divisors(m) ∪
  p·divisors(m)` (`divisorChar_prime_mul`).
-/

open GaussianInt

namespace RHTower.GaussianTwoSquares

local notation "ℤ[i]" => GaussianInt

/-- The Gaussian integers of norm `n`. -/
def normSet (n : ℕ) : Finset ℤ[i] :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).image
    fun ab : ℤ × ℤ => (⟨ab.1, ab.2⟩ : ℤ[i])).filter fun z => z.norm = n

theorem norm_eq (z : ℤ[i]) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

theorem abs_le_sq (a : ℤ) : |a| ≤ a ^ 2 := by
  rcases eq_or_ne a 0 with h0 | h0
  · simp [h0]
  · have h1 : 1 ≤ |a| := Int.one_le_abs h0
    nlinarith [sq_abs a]

theorem mem_normSet {n : ℕ} {z : ℤ[i]} : z ∈ normSet n ↔ z.norm = n := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(z.re, z.im), ?_, rfl⟩, h⟩
    rw [norm_eq] at h
    have h1 : z.re ^ 2 ≤ n := by nlinarith [sq_nonneg z.im]
    have h2 : z.im ^ 2 ≤ n := by nlinarith [sq_nonneg z.re]
    obtain ⟨l1, u1⟩ := abs_le.mp ((abs_le_sq z.re).trans h1)
    obtain ⟨l2, u2⟩ := abs_le.mp ((abs_le_sq z.im).trans h2)
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨l1, u1⟩, ⟨l2, u2⟩⟩

theorem card_normSet_one : (normSet 1).card = 4 := by decide

theorem star_dvd_of_dvd {x t : ℤ[i]} (h : x ∣ star t) : star x ∣ t := by
  obtain ⟨c, hc⟩ := h
  exact ⟨star c, by rw [← star_star t, hc, star_mul']⟩

theorem norm_natCast' (p : ℕ) : ((p : ℤ[i])).norm = (p : ℤ) * p := Zsqrtd.norm_natCast p

theorem natCast_dvd_mul_star {t : ℤ[i]} {p m : ℕ} (ht : t.norm = ((p * m : ℕ) : ℤ)) :
    (p : ℤ[i]) ∣ t * star t := by
  rw [← Zsqrtd.norm_eq_mul_conj, ht]
  exact ⟨m, by push_cast; ring⟩

/-- If a nonzero `w` has norm `q`, multiplication by `w` maps norm `m` to norm `q m`. -/
theorem mul_mem_normSet {w z : ℤ[i]} {q m : ℕ} (hw : w.norm = q) (hz : z ∈ normSet m) :
    w * z ∈ normSet (q * m) := by
  rw [mem_normSet] at hz ⊢
  rw [Zsqrtd.norm_mul, hw, hz]
  push_cast
  ring

/-- If `t = w z` has norm `q m` with `w` of norm `q > 0`, then `z` has norm `m`. -/
theorem mem_normSet_of_mul {w z : ℤ[i]} {q m : ℕ} (hq : 0 < q) (hw : w.norm = q)
    (ht : w * z ∈ normSet (q * m)) : z ∈ normSet m := by
  rw [mem_normSet, Zsqrtd.norm_mul, hw] at ht
  rw [mem_normSet]
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast at ht
  exact mul_left_cancel₀ hq' ht

/-- The norm of `p w` is `p m` iff `p ∣ m` and `w` has norm `m/p`. -/
theorem mem_normSet_natCast_mul {p m : ℕ} (hp : 0 < p) {w : ℤ[i]} :
    (p : ℤ[i]) * w ∈ normSet (p * m) ↔ p ∣ m ∧ w ∈ normSet (m / p) := by
  rw [mem_normSet, mem_normSet, Zsqrtd.norm_mul, norm_natCast']
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro h
    have h1 : (p : ℤ) * w.norm = m := by
      push_cast at h
      exact mul_left_cancel₀ hp' (by linarith)
    have hw0 : 0 ≤ w.norm := GaussianInt.norm_nonneg w
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hw0
    rw [hk] at h1
    have h2 : p * k = m := by exact_mod_cast h1
    refine ⟨⟨k, h2.symm⟩, ?_⟩
    rw [hk, ← h2, Nat.mul_div_cancel_left k hp]
  · rintro ⟨⟨k, rfl⟩, h⟩
    rw [Nat.mul_div_cancel_left k hp] at h
    rw [h]
    push_cast
    ring

theorem prime_of_norm_prime {π : ℤ[i]} {p : ℕ} (hp : p.Prime) (hπ : π.norm = p) : Prime π := by
  refine _root_.irreducible_iff_prime.mp ⟨?_, ?_⟩
  · intro hu
    have := Zsqrtd.norm_eq_one_iff.mpr hu
    rw [hπ] at this
    simp only [Int.natAbs_natCast] at this
    exact hp.one_lt.ne' this
  · intro x y hxy
    have hn := congrArg (fun z : ℤ[i] => z.norm.natAbs) hxy
    simp only [Zsqrtd.norm_mul, Int.natAbs_mul, hπ, Int.natAbs_natCast] at hn
    rcases (Nat.prime_mul_iff.mp (hn ▸ hp)) with ⟨_, h1⟩ | ⟨_, h1⟩
    · exact Or.inr (Zsqrtd.norm_eq_one_iff.mp h1)
    · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp h1)

/-! ### `p ≡ 3 (mod 4)` -/

theorem natCast_dvd_of_three {p m : ℕ} [hpf : Fact p.Prime] (hp3 : p % 4 = 3) {t : ℤ[i]}
    (ht : t ∈ normSet (p * m)) : (p : ℤ[i]) ∣ t := by
  have hprime := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hp3
  rcases hprime.dvd_or_dvd (natCast_dvd_mul_star (mem_normSet.mp ht)) with h | h
  · exact h
  · have := star_dvd_of_dvd h
    rwa [star_natCast] at this

theorem normSet_mul_of_three {p : ℕ} [hpf : Fact p.Prime] (hp3 : p % 4 = 3) (m : ℕ) :
    normSet (p * m) = if p ∣ m then (normSet (m / p)).image ((p : ℤ[i]) * ·) else ∅ := by
  have hp := hpf.out.pos
  ext t
  constructor
  · intro ht
    obtain ⟨w, rfl⟩ := natCast_dvd_of_three hp3 ht
    obtain ⟨hdvd, hw⟩ := (mem_normSet_natCast_mul hp).mp ht
    rw [if_pos hdvd]
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  · intro ht
    split_ifs at ht with hdvd
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
      exact (mem_normSet_natCast_mul hp).mpr ⟨hdvd, hw⟩
    · simp at ht

theorem card_normSet_mul_of_three {p : ℕ} [hpf : Fact p.Prime] (hp3 : p % 4 = 3) (m : ℕ) :
    (normSet (p * m)).card = if p ∣ m then (normSet (m / p)).card else 0 := by
  have hp0 : (p : ℤ[i]) ≠ 0 := by exact_mod_cast hpf.out.ne_zero
  rw [normSet_mul_of_three hp3 m]
  split_ifs
  · exact Finset.card_image_of_injective _ (mul_right_injective₀ hp0)
  · rfl

/-! ### `p = 2` -/

/-- The Gaussian prime `1 + i` above `2`. -/
def onePlusI : ℤ[i] := ⟨1, 1⟩

theorem norm_onePlusI : onePlusI.norm = 2 := by decide

theorem onePlusI_dvd_two : onePlusI ∣ (2 : ℤ[i]) := ⟨⟨1, -1⟩, by decide⟩

theorem onePlusI_dvd_star : onePlusI ∣ star onePlusI := ⟨⟨0, -1⟩, by decide⟩

theorem onePlusI_dvd {m : ℕ} {t : ℤ[i]} (ht : t ∈ normSet (2 * m)) : onePlusI ∣ t := by
  have hprime := prime_of_norm_prime Nat.prime_two norm_onePlusI
  have h2 : (2 : ℤ[i]) ∣ t * star t := by
    have := natCast_dvd_mul_star (p := 2) (mem_normSet.mp ht)
    simpa using this
  rcases hprime.dvd_or_dvd (onePlusI_dvd_two.trans h2) with h | h
  · exact h
  · exact onePlusI_dvd_star.trans (star_dvd_of_dvd h)

theorem card_normSet_two_mul (m : ℕ) : (normSet (2 * m)).card = (normSet m).card := by
  have h0 : onePlusI ≠ 0 := by decide
  have e : normSet (2 * m) = (normSet m).image (onePlusI * ·) := by
    ext t
    constructor
    · intro ht
      obtain ⟨z, rfl⟩ := onePlusI_dvd ht
      exact Finset.mem_image.mpr ⟨z, mem_normSet_of_mul two_pos norm_onePlusI ht, rfl⟩
    · intro ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
      exact mul_mem_normSet norm_onePlusI hz
  rw [e, Finset.card_image_of_injective _ (mul_right_injective₀ h0)]

/-! ### `p ≡ 1 (mod 4)` -/

theorem card_normSet_mul_of_one {p : ℕ} [hpf : Fact p.Prime] (hp1 : p % 4 = 1) (m : ℕ) :
    ((normSet (p * m)).card : ℤ) =
      2 * (normSet m).card - if p ∣ m then ((normSet (m / p)).card : ℤ) else 0 := by
  have hp := hpf.out
  have hp0 := hp.pos
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  set π : ℤ[i] := ⟨a, b⟩ with hπdef
  have hnπ : π.norm = p := by
    rw [norm_eq, hπdef]
    show (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = p
    exact_mod_cast hab
  have hnπ' : (star π).norm = p := by rw [Zsqrtd.norm_conj, hnπ]
  have hπ := prime_of_norm_prime hp hnπ
  have hπ' := prime_of_norm_prime hp hnπ'
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπ'0 : star π ≠ 0 := hπ'.ne_zero
  have hpp : π * star π = (p : ℤ[i]) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hnπ]
    rfl
  -- `π` and `π̄` are not associate
  have hnd : ¬ π ∣ star π := by
    rintro ⟨c, hc⟩
    have hn := congrArg Zsqrtd.norm hc
    rw [Zsqrtd.norm_mul, hnπ, hnπ'] at hn
    have hc1 : c.norm = 1 := by
      have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      exact (mul_eq_left₀ hp').mp hn.symm
    rw [norm_eq] at hc1
    have hre := congrArg Zsqrtd.re hc
    have him := congrArg Zsqrtd.im hc
    simp only [Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.re_mul, Zsqrtd.im_mul, hπdef] at hre him
    have hab' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = p := by exact_mod_cast hab
    have hpodd : p % 2 = 1 := by omega
    have hcases : (c.re = 1 ∧ c.im = 0) ∨ (c.re = -1 ∧ c.im = 0) ∨ (c.re = 0 ∧ c.im = 1) ∨
        (c.re = 0 ∧ c.im = -1) := by
      have h1 : c.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg c.im]
      have h2 : c.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg c.re]
      have hr : -1 ≤ c.re ∧ c.re ≤ 1 := by
        constructor <;> nlinarith [abs_le_sq c.re, abs_le.mp ((abs_le_sq c.re).trans h1)]
      have hi : -1 ≤ c.im ∧ c.im ≤ 1 := by
        constructor <;> nlinarith [abs_le_sq c.im, abs_le.mp ((abs_le_sq c.im).trans h2)]
      rcases hr with ⟨hr1, hr2⟩
      rcases hi with ⟨hi1, hi2⟩
      interval_cases hcr : c.re <;> interval_cases hci : c.im <;> first | decide | (norm_num at hc1)
    have hpsq : ∀ x : ℕ, x ^ 2 ≠ p := fun x hx => by
      have hxp : x ∣ p := ⟨x, by rw [← hx]; ring⟩
      rcases hp.eq_one_or_self_of_dvd x hxp with h | h
      · subst h; simp at hx; exact hp.one_lt.ne hx
      · rw [h] at hx
        have : p * p = p * 1 := by rw [← sq, hx, mul_one]
        exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp0 this)
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hre him
    · have hb : (b : ℤ) = 0 := by linarith
      have : b = 0 := by exact_mod_cast hb
      subst this
      exact hpsq a (by simpa using hab)
    · have ha : (a : ℤ) = 0 := by linarith
      have : a = 0 := by exact_mod_cast ha
      subst this
      exact hpsq b (by simpa using hab)
    · have ha : (a : ℤ) = -b := by linarith
      have hb0 : (b : ℤ) = 0 := by have := Int.natCast_nonneg a; have := Int.natCast_nonneg b; linarith
      have ha0 : (a : ℤ) = 0 := by linarith
      have : (p : ℤ) = 0 := by rw [← hab', ha0, hb0]; ring
      exact hp.ne_zero (by exact_mod_cast this)
    · have ha : (a : ℤ) = b := by linarith
      have : (p : ℤ) = 2 * (a : ℤ) ^ 2 := by rw [← hab', ha]; ring
      have h2p : 2 ∣ p := ⟨a ^ 2, by exact_mod_cast this⟩
      omega
  have hnd' : ¬ star π ∣ π := fun h => hnd (by
    have h' : star π ∣ star (star π) := by rwa [star_star]
    simpa using star_dvd_of_dvd h')
  -- the decomposition
  set A := (normSet m).image (π * ·)
  set B := (normSet m).image (star π * ·)
  have hU : normSet (p * m) = A ∪ B := by
    ext t
    constructor
    · intro ht
      have hdiv : π ∣ t * star t :=
        (Dvd.intro _ hpp).trans (natCast_dvd_mul_star (mem_normSet.mp ht))
      rcases hπ.dvd_or_dvd hdiv with h | h
      · obtain ⟨z, rfl⟩ := h
        exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨z, mem_normSet_of_mul hp0 hnπ ht, rfl⟩)
      · obtain ⟨z, rfl⟩ := star_dvd_of_dvd h
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨z, mem_normSet_of_mul hp0 hnπ' ht, rfl⟩)
    · intro ht
      rcases Finset.mem_union.mp ht with h | h
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        exact mul_mem_normSet hnπ hz
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        exact mul_mem_normSet hnπ' hz
  have hI : A ∩ B = if p ∣ m then (normSet (m / p)).image ((p : ℤ[i]) * ·) else ∅ := by
    ext t
    constructor
    · intro ht
      obtain ⟨hA, hB⟩ := Finset.mem_inter.mp ht
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨z', _, hz'⟩ := Finset.mem_image.mp hB
      have hdz : star π ∣ π * z := ⟨z', hz'.symm⟩
      rcases hπ'.dvd_or_dvd hdz with h | h
      · exact absurd h hnd'
      · obtain ⟨w, rfl⟩ := h
        have ht' : (p : ℤ[i]) * w ∈ normSet (p * m) := by
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
        refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨star π * w, ?_, ?_⟩,
          Finset.mem_image.mpr ⟨π * w, ?_, ?_⟩⟩
        · exact mul_mem_normSet hnπ' hw
        · rw [← hpp]; ring
        · exact mul_mem_normSet hnπ hw
        · rw [← hpp]; ring
      · simp at ht
  have hcard := Finset.card_union_add_card_inter A B
  rw [← hU, hI] at hcard
  have hA : A.card = (normSet m).card := Finset.card_image_of_injective _ (mul_right_injective₀ hπ0)
  have hB : B.card = (normSet m).card :=
    Finset.card_image_of_injective _ (mul_right_injective₀ hπ'0)
  have hp0' : (p : ℤ[i]) ≠ 0 := by exact_mod_cast hp.ne_zero
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

/-- `a(n) = Σ_{d ∣ n} χ₄(d)`. -/
def divisorChar (n : ℕ) : ℤ := ∑ d ∈ n.divisors, ZMod.χ₄ d

theorem divisorChar_one : divisorChar 1 = 1 := by
  simp [divisorChar]

theorem divisorChar_prime_mul {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 0 < m) :
    divisorChar (p * m) =
      (1 + ZMod.χ₄ p) * divisorChar m - ZMod.χ₄ p * (if p ∣ m then divisorChar (m / p) else 0) := by
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
  have hsum : ∀ D : Finset ℕ, ∑ d ∈ D.image (p * ·), ZMod.χ₄ d =
      ZMod.χ₄ p * ∑ d ∈ D, ZMod.χ₄ d := fun D => by
    rw [Finset.sum_image fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp0 h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    exact map_mul _ _ _
  have h := Finset.sum_union_inter (s₁ := m.divisors) (s₂ := m.divisors.image (p * ·))
    (f := fun d => ZMod.χ₄ d)
  rw [← hU, hI, hsum] at h
  unfold divisorChar
  split_ifs at h ⊢ with hpm
  · rw [hsum] at h
    linarith
  · simp only [Finset.sum_empty, add_zero] at h
    linarith

/-! ### Jacobi's formula -/

theorem card_normSet_prime_mul {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ((normSet (p * m)).card : ℤ) = (1 + ZMod.χ₄ p) * (normSet m).card -
      ZMod.χ₄ p * (if p ∣ m then ((normSet (m / p)).card : ℤ) else 0) := by
  haveI := Fact.mk hp
  rcases hp.eq_two_or_odd with rfl | hodd
  · rw [card_normSet_two_mul]
    have : ZMod.χ₄ (2 : ℕ) = 0 := by decide
    rw [this]
    ring
  · rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
    · rw [card_normSet_mul_of_one h1, ZMod.χ₄_nat_one_mod_four h1]
      ring
    · rw [card_normSet_mul_of_three h3, ZMod.χ₄_nat_three_mod_four h3]
      split_ifs <;> push_cast <;> ring

/-- **Jacobi's two-square theorem**: `#{z ∈ ℤ[i] : N(z) = n} = 4 Σ_{d ∣ n} χ₄(d)` for `n ≥ 1`. -/
theorem card_normSet {n : ℕ} (hn : 0 < n) : ((normSet n).card : ℤ) = 4 * divisorChar n := by
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

end RHTower.GaussianTwoSquares
