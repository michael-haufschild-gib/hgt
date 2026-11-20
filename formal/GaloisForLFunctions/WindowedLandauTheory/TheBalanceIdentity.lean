import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusClasses
import GaloisForLFunctions.WindowedLandauTheory.WindowedCesaroBoundsForceZeroFreeHalfPlanes

/-!
# The balance identity for inert primes

Frobenius data on the host group `G = (ℤ/2)² × H` assign to each prime `p` a Frobenius class and an
inertia subgroup; in the admissible pattern the primes `2` and `q₁` are split, `d` is ramified with
inertia `{0, ((1,0),0)}` and every other prime is unramified. A prime is *inert* when it is
unramified with non-split Frobenius.

For `a > 0`, a height `t` and weights `w > 0` on the split classes, the weighted inert count
`ASK = Σ_{p inert} 2 log p Σ_i (a/p^i - w(partner(i·Frob_p)))⁺ + log d · (ramified part)` satisfies

```text
ASK - a(log a - 1 - γ + ℓ(sign) - mean_Φ log w) = (1/|Φ|) Σ_{g non-split} Σ_ψ conj ψ(g) w_g G_ψ(a/w_g),
```

where `w_g = w(partner g)` and `G_ψ` is the Cesàro functional of `ψ` (`G_ζ` for `ψ = 0`)
(`inertTotal_sub_mainTotal`). Characters recover the Frobenius classes of prime powers
(`classKernel_prime_pow`), the non-split classes see only the trivial and the sign character, and the
partner map turns the mean over non-split classes into the mean over split ones.
-/

open Finset ArithmeticFunction

namespace WindowedLandauTheory

noncomputable section

/-- Frobenius classes and inertia groups of the primes on the host group. -/
structure FrobeniusData (H : Type) [AddCommGroup H] where
  q₁ : ℕ
  d : ℕ
  inertia : ℕ → AddSubgroup (SignPair × H)
  frob : ℕ → SignPair × H

section Balance

variable {H : Type} [AddCommGroup H]

/-- The admissible ramification pattern: unramified outside `{2, q₁, d}`, split at `2` and `q₁`, and
inertia `{0, ((1,0),0)}` at `d`. -/
structure FrobeniusData.Admissible (D : FrobeniusData H) : Prop where
  q₁_prime : D.q₁.Prime
  d_prime : D.d.Prime
  q₁_ne_two : D.q₁ ≠ 2
  d_ne_two : D.d ≠ 2
  q₁_ne_d : D.q₁ ≠ D.d
  unramified : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ D.q₁ → p ≠ D.d → D.inertia p = ⊥
  split_inertia : ∀ p : ℕ, (p = 2 ∨ p = D.q₁) → ∀ x ∈ D.inertia p, IsSplit x
  split_frob : ∀ p : ℕ, (p = 2 ∨ p = D.q₁) → IsSplit (D.frob p)
  inertia_d : ∀ x, x ∈ D.inertia D.d ↔ x = 0 ∨ x = ramifiedClass

variable [Fintype H] [DecidableEq H]

/-- The value of a character at `n`: the product over `p ∣ n` of its inertia average at
`v_p(n) · Frob_p`. -/
def classValue (D : FrobeniusData H) (ψ : AddChar (SignPair × H) ℂ) (n : ℕ) : ℂ :=
  ∏ p ∈ n.primeFactors, cosetAverage (D.inertia p) (n.factorization p • D.frob p) ψ

omit [DecidableEq H] in
theorem classValue_zero (D : FrobeniusData H) (n : ℕ) : classValue D 0 n = 1 :=
  Finset.prod_eq_one fun _ _ => cosetAverage_zero _ _

omit [DecidableEq H] in
theorem classValue_prime_pow (D : FrobeniusData H) (ψ : AddChar (SignPair × H) ℂ) {p i : ℕ}
    (hp : p.Prime) (hi : i ≠ 0) :
    classValue D ψ (p ^ i) = cosetAverage (D.inertia p) (i • D.frob p) ψ := by
  rw [classValue, Nat.primeFactors_prime_pow hi hp, Finset.prod_singleton, hp.factorization_pow,
    Finsupp.single_eq_same]

/-- The Cesàro functional of a character of the host group; `G_ζ` for the trivial character. -/
def classCesaro (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    (ψ : AddChar (SignPair × H) ℂ) (y : ℝ) : ℂ :=
  if ψ = 0 then (zetaCesaroFunctional y : ℂ) else
    (∑ n ∈ Icc 1 ⌊y⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n * ((y / n - 1 : ℝ) : ℂ)) +
      (y : ℂ) * ℓ ψ

/-- An inert prime: unramified with non-split Frobenius. -/
def IsInertPrime (D : FrobeniusData H) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ≠ D.q₁ ∧ p ≠ D.d ∧ ¬IsSplit (D.frob p)

/-- The contribution of an inert prime `p`: `Σ_i (a/p^i - w(partner(i·Frob_p)))⁺` over non-split
powers. -/
def inertCount (D : FrobeniusData H) (N : ℕ) (a : ℝ) (t : H) (w : SignPair × H → ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ (Icc 1 N).filter (fun i => ¬IsSplit (i • D.frob p)),
    max (a / (p : ℝ) ^ i - w (partnerClass t (i • D.frob p))) 0

open Classical in
/-- The contribution of the ramified prime `d`. -/
def ramifiedCount (D : FrobeniusData H) (N : ℕ) (a : ℝ) (t : H) (w : SignPair × H → ℝ) : ℝ :=
  ∑ i ∈ Icc 1 N, ∑ g ∈ univ.filter (fun g => g - i • D.frob D.d ∈ D.inertia D.d ∧ ¬IsSplit g),
    max (a / (D.d : ℝ) ^ i - w (partnerClass t g)) 0

open Classical in
/-- The weighted count of inert primes. -/
def inertTotal (D : FrobeniusData H) (N : ℕ) (a : ℝ) (t : H) (w : SignPair × H → ℝ) : ℝ :=
  (∑ p ∈ (range (N + 1)).filter (IsInertPrime D), 2 * Real.log p * inertCount D N a t w p) +
    Real.log D.d * ramifiedCount D N a t w

/-- Its main term `a(log a - 1 - γ + ℓ(sign) - mean_Φ log w)`. -/
def mainTotal (ℓ : AddChar (SignPair × H) ℂ → ℂ) (a : ℝ) (w : SignPair × H → ℝ) : ℂ :=
  (a : ℂ) * (((Real.log a - 1 - Real.eulerMascheroniConstant : ℝ) : ℂ) + ℓ splitSign -
    (((1 / ((splitSet H).card : ℝ)) * ∑ ρ ∈ splitSet H, Real.log (w ρ) : ℝ) : ℂ))

/-- The character side `(1/|Φ|) Σ_{g non-split} Σ_ψ conj ψ(g) w_g G_ψ(a/w_g)`. -/
def balanceTotal (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ) (a : ℝ) (t : H)
    (w : SignPair × H → ℝ) : ℂ :=
  (1 / ((splitSet H).card : ℂ)) * ∑ g ∈ nonsplitSet H, ∑ ψ : AddChar (SignPair × H) ℂ,
    starRingEnd ℂ (ψ g) * ((w (partnerClass t g) : ℝ) : ℂ) *
      classCesaro D ℓ ψ (a / w (partnerClass t g))

/-! ## Characters recover Frobenius classes -/

/-- `K(n, g) = (1/|Φ|) Σ_ψ conj ψ(g) · ψ(n)`. -/
def classKernel (D : FrobeniusData H) (n : ℕ) (g : SignPair × H) : ℂ :=
  (1 / ((splitSet H).card : ℂ)) * ∑ ψ : AddChar (SignPair × H) ℂ,
    starRingEnd ℂ (ψ g) * classValue D ψ n

open Classical in
theorem classKernel_prime_pow (D : FrobeniusData H) {p i : ℕ} (hp : p.Prime) (hi : i ≠ 0)
    (g : SignPair × H) : classKernel D (p ^ i) g =
      if g - i • D.frob p ∈ D.inertia p then 2 / ((univ.filter (· ∈ D.inertia p)).card : ℂ)
      else 0 := by
  unfold classKernel
  simp_rw [classValue_prime_pow D _ hp hi]
  exact sum_conj_mul_cosetAverage _ _ _

theorem classKernel_unramified (D : FrobeniusData H) (hD : D.Admissible) {p i : ℕ}
    (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ D.q₁) (hd : p ≠ D.d) (hi : i ≠ 0) (g : SignPair × H) :
    classKernel D (p ^ i) g = if g = i • D.frob p then 2 else 0 := by
  classical
  rw [classKernel_prime_pow D hp hi, hD.unramified p hp h2 hq hd]
  have hc : (univ.filter (· ∈ (⊥ : AddSubgroup (SignPair × H)))).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨0, by ext x; simp⟩
  rw [hc]
  by_cases hg : g = i • D.frob p
  · rw [if_pos (by rw [hg, sub_self]; exact AddSubgroup.zero_mem _), if_pos hg]
    norm_num
  · rw [if_neg (fun h => hg (sub_eq_zero.mp ((AddSubgroup.mem_bot).mp h))), if_neg hg]

theorem classKernel_split (D : FrobeniusData H) (hD : D.Admissible) {p i : ℕ} (hp : p.Prime)
    (h2 : p = 2 ∨ p = D.q₁) (hi : i ≠ 0) {g : SignPair × H} (hg : ¬IsSplit g) :
    classKernel D (p ^ i) g = 0 := by
  classical
  rw [classKernel_prime_pow D hp hi, if_neg]
  intro hm
  apply hg
  have h := (hD.split_inertia p h2 _ hm).add ((hD.split_frob p h2).nsmul i)
  rwa [sub_add_cancel] at h

open Classical in
theorem classKernel_ramified (D : FrobeniusData H) (hD : D.Admissible) {i : ℕ} (hi : i ≠ 0)
    (g : SignPair × H) :
    classKernel D (D.d ^ i) g = if g - i • D.frob D.d ∈ D.inertia D.d then 1 else 0 := by
  classical
  rw [classKernel_prime_pow D hD.d_prime hi]
  have h0 : (0 : SignPair × H) ≠ ramifiedClass := by
    intro h
    have h' : (0 : SignPair × H).1.1 = (ramifiedClass : SignPair × H).1.1 := by rw [h]
    simp [ramifiedClass] at h'
  have hc : (univ.filter (· ∈ D.inertia D.d)).card = 2 := by
    have hs : univ.filter (· ∈ D.inertia D.d) = {0, ramifiedClass} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hD.inertia_d x
    rw [hs, Finset.card_pair h0]
  rw [hc]
  split_ifs <;> norm_num

/-! ## Von Mangoldt sums over prime powers -/

/-- A von Mangoldt sum is a sum over prime powers `p^i ≤ N`. -/
theorem sum_Icc_vonMangoldt_mul (N : ℕ) (X : ℕ → ℂ)
    (hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i → X (p ^ i) = 0) :
    ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * X n =
      ∑ p ∈ (range (N + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * X (p ^ i) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · intro x hx hne
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    have hle : x.1 ^ x.2 ≤ N := by
      by_contra hlt
      exact hne (by rw [hX x.1 x.2 hp hi1 (not_le.1 hlt), mul_zero])
    exact Finset.mem_Icc.2 ⟨Nat.one_le_pow _ _ hp.pos, hle⟩
  · intro x hx _ y hy _ hxy
    have hxy' : x.1 ^ x.2 = y.1 ^ y.2 := hxy
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx hy
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    obtain ⟨⟨_, hq⟩, hj1, _⟩ := hy
    have hpq : x.1 = y.1 := by
      have hd : x.1 ∣ y.1 ^ y.2 := by
        rw [← hxy']
        exact dvd_pow_self _ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd)
    have hij : x.2 = y.2 := by
      rw [hpq] at hxy'
      exact Nat.pow_right_injective hq.two_le hxy'
    exact Prod.ext hpq hij
  · intro n hn hne
    rw [Finset.mem_Icc] at hn
    have hΛ : vonMangoldt n ≠ 0 := by
      intro h0
      apply hne
      rw [h0, Complex.ofReal_zero, zero_mul]
    rw [vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
    have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
    refine ⟨(p, k), ?_, ?_, rfl⟩
    · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨⟨Nat.lt_succ_of_le (h1.trans hn.2), hp⟩, hk, (h2.trans_le hn.2).le⟩
    · intro h0
      apply hne
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
      exact h0
  · intro x hx _
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx
    show (Real.log x.1 : ℂ) * X (x.1 ^ x.2) = (vonMangoldt (x.1 ^ x.2) : ℂ) * X (x.1 ^ x.2)
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hx.1.2]

/-! ## Expansion of the inert count -/

/-- The cut `(a/n - w)⁺` attached to a non-split class through its partner. -/
def cutValue (a : ℝ) (t : H) (w : SignPair × H → ℝ) (n : ℕ) (g : SignPair × H) : ℂ :=
  ((max (a / (n : ℝ) - w (partnerClass t g)) 0 : ℝ) : ℂ)

omit [Fintype H] [DecidableEq H] in
theorem cutValue_eq_zero {N : ℕ} {a : ℝ} {t : H} {w : SignPair × H → ℝ}
    (hw : ∀ ρ, IsSplit ρ → 0 < w ρ) (hN : ∀ ρ, IsSplit ρ → a / w ρ ≤ N) {g : SignPair × H}
    (hg : ¬IsSplit g) {n : ℕ} (hn : N < n) : cutValue a t w n g = 0 := by
  have hρ := isSplit_partnerClass t hg
  have hwρ := hw _ hρ
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg N) (by exact_mod_cast hn)
  have h1 : a / w (partnerClass t g) < n := lt_of_le_of_lt (hN _ hρ) (by exact_mod_cast hn)
  have h2 : a / n < w (partnerClass t g) := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hwρ] at h1
    linarith
  rw [cutValue, max_eq_right (by linarith), Complex.ofReal_zero]

open Classical in
theorem localTerm_unramified (D : FrobeniusData H) (hD : D.Admissible) (N : ℕ) (a : ℝ) (t : H)
    (w : SignPair × H → ℝ) {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ D.q₁) (hd : p ≠ D.d) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ nonsplitSet H, classKernel D (p ^ i) g *
        cutValue a t w (p ^ i) g =
      ((if IsInertPrime D p then 2 * Real.log p * inertCount D N a t w p else 0 : ℝ) : ℂ) := by
  have hin : ∀ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ nonsplitSet H, classKernel D (p ^ i) g *
        cutValue a t w (p ^ i) g =
      (((if ¬IsSplit (i • D.frob p) then
        2 * Real.log p * max (a / (p : ℝ) ^ i - w (partnerClass t (i • D.frob p))) 0 else 0) : ℝ) :
        ℂ) := by
    intro i hi
    have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
    simp_rw [classKernel_unramified D hD hp h2 hq hd hi0, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    by_cases hs : ¬IsSplit (i • D.frob p)
    · rw [if_pos (by simpa [nonsplitSet] using hs), if_pos hs, cutValue]
      push_cast
      ring
    · rw [if_neg (by simpa [nonsplitSet] using hs), if_neg hs]
      simp
  rw [Finset.sum_congr rfl hin, ← Complex.ofReal_sum]
  congr 1
  by_cases hin' : IsInertPrime D p
  · rw [if_pos hin', inertCount, Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
  · rw [if_neg hin']
    have hsp : IsSplit (D.frob p) := by
      by_contra hc
      exact hin' ⟨hp, h2, hq, hd, hc⟩
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (not_not.2 (hsp.nsmul i))]

theorem localTerm_split (D : FrobeniusData H) (hD : D.Admissible) (N : ℕ) (a : ℝ) (t : H)
    (w : SignPair × H → ℝ) {p : ℕ} (hp : p.Prime) (h2 : p = 2 ∨ p = D.q₁) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ nonsplitSet H, classKernel D (p ^ i) g *
        cutValue a t w (p ^ i) g = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
  rw [Finset.sum_eq_zero, mul_zero]
  intro g hg
  have hg' : ¬IsSplit g := by simpa [nonsplitSet] using hg
  rw [classKernel_split D hD hp h2 hi0 hg', zero_mul]

theorem localTerm_ramified (D : FrobeniusData H) (hD : D.Admissible) (N : ℕ) (a : ℝ) (t : H)
    (w : SignPair × H → ℝ) :
    ∑ i ∈ Icc 1 N, (Real.log D.d : ℂ) * ∑ g ∈ nonsplitSet H, classKernel D (D.d ^ i) g *
        cutValue a t w (D.d ^ i) g = ((Real.log D.d * ramifiedCount D N a t w : ℝ) : ℂ) := by
  classical
  unfold ramifiedCount
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi0 : i ≠ 0 := by have := (Finset.mem_Icc.1 hi).1; omega
  congr 1
  simp_rw [classKernel_ramified D hD hi0, ite_mul, one_mul, zero_mul]
  rw [nonsplitSet, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h1 : IsSplit g <;> by_cases h2 : g - i • D.frob D.d ∈ D.inertia D.d <;>
    simp [h1, h2, cutValue]

omit [DecidableEq H] in
/-- With `a/w ≤ N` on split classes, the ramified part vanishes when `d > N`. -/
theorem ramifiedCount_eq_zero (D : FrobeniusData H) {N : ℕ} {a : ℝ} {t : H}
    {w : SignPair × H → ℝ} (hw : ∀ ρ, IsSplit ρ → 0 < w ρ) (hN : ∀ ρ, IsSplit ρ → a / w ρ ≤ N)
    (hdN : N < D.d) : ramifiedCount D N a t w = 0 := by
  classical
  unfold ramifiedCount
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun g hg => ?_
  have hg' : ¬IsSplit g := (Finset.mem_filter.1 hg).2.2
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hlt : N < D.d ^ i := lt_of_lt_of_le hdN (Nat.le_self_pow (by omega) _)
  have h := cutValue_eq_zero (t := t) hw hN hg' hlt
  rw [cutValue, Complex.ofReal_eq_zero, Nat.cast_pow] at h
  exact h

/-- **Character expansion of the inert count.** -/
theorem inertTotal_eq_characterSum (D : FrobeniusData H) (hD : D.Admissible) {a : ℝ} (t : H)
    {w : SignPair × H → ℝ} (hw : ∀ ρ, IsSplit ρ → 0 < w ρ) {N : ℕ}
    (hN : ∀ ρ, IsSplit ρ → a / w ρ ≤ N) :
    (inertTotal D N a t w : ℂ) = (1 / ((splitSet H).card : ℂ)) * ∑ g ∈ nonsplitSet H,
      ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
        (vonMangoldt n : ℂ) * classValue D ψ n * cutValue a t w n g := by
  classical
  have hg : ∀ g : SignPair × H, (1 / ((splitSet H).card : ℂ)) * ∑ ψ : AddChar (SignPair × H) ℂ,
      starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * classValue D ψ n *
        cutValue a t w n g =
      ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * (classKernel D n g * cutValue a t w n g) := by
    intro g
    simp only [classKernel, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun ψ _ => by ring
  have hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i →
      ∑ g ∈ nonsplitSet H, classKernel D (p ^ i) g * cutValue a t w (p ^ i) g = 0 := by
    intro p i _ _ hlt
    refine Finset.sum_eq_zero fun g hg' => ?_
    have hg'' : ¬IsSplit g := by simpa [nonsplitSet] using hg'
    rw [cutValue_eq_zero hw hN hg'' hlt, mul_zero]
  have hloc : ∀ p ∈ (range (N + 1)).filter Nat.Prime,
      ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ nonsplitSet H, classKernel D (p ^ i) g *
        cutValue a t w (p ^ i) g =
      (((if IsInertPrime D p then 2 * Real.log p * inertCount D N a t w p else 0) +
        (if p = D.d then Real.log D.d * ramifiedCount D N a t w else 0) : ℝ) : ℂ) := by
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.1 hp).2
    by_cases hs : p = 2 ∨ p = D.q₁
    · rw [localTerm_split D hD N a t w hp' hs]
      have h1 : ¬IsInertPrime D p := fun h => hs.elim h.2.1 h.2.2.1
      have h2 : p ≠ D.d := fun h => hs.elim (fun h' => hD.d_ne_two (h.symm.trans h'))
        (fun h' => hD.q₁_ne_d (h'.symm.trans h))
      simp [h1, h2]
    · have hs2 : p ≠ 2 := fun h => hs (Or.inl h)
      have hsq : p ≠ D.q₁ := fun h => hs (Or.inr h)
      by_cases hdd : p = D.d
      · subst hdd
        rw [localTerm_ramified D hD N a t w]
        have h1 : ¬IsInertPrime D D.d := fun h => h.2.2.2.1 rfl
        simp [h1]
      · rw [localTerm_unramified D hD N a t w hp' hs2 hsq hdd]
        simp [hdd]
  have e1 : (1 / ((splitSet H).card : ℂ)) * ∑ g ∈ nonsplitSet H,
      ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
        (vonMangoldt n : ℂ) * classValue D ψ n * cutValue a t w n g =
      ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) *
        ∑ g ∈ nonsplitSet H, classKernel D n g * cutValue a t w n g := by
    rw [Finset.mul_sum, Finset.sum_congr rfl fun g _ => hg g, Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [e1, sum_Icc_vonMangoldt_mul N _ hX, Finset.sum_congr rfl hloc, ← Complex.ofReal_sum]
  congr 1
  rw [Finset.sum_add_distrib, inertTotal]
  congr 1
  · rw [← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · rw [Finset.sum_ite_eq']
    split_ifs with hdm
    · rfl
    · have hdN : N < D.d := by
        by_contra hc
        apply hdm
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hD.d_prime⟩
      rw [ramifiedCount_eq_zero D hw hN hdN, mul_zero]

/-! ## The inner sums are Cesàro functionals -/

omit [Fintype H] [DecidableEq H] in
/-- Cutting at `a/n ≥ W`: `Σ_{n ≤ N} c_n (a/n - W)⁺ = Σ_{n ≤ a/W} c_n (a/n - W)`. -/
theorem sum_Icc_max_eq (c : ℕ → ℂ) {N : ℕ} {a W : ℝ} (ha : 0 < a) (hW : 0 < W)
    (hN : a / W ≤ N) :
    ∑ n ∈ Icc 1 N, c n * ((max (a / n - W) 0 : ℝ) : ℂ) =
      ∑ n ∈ Icc 1 ⌊a / W⌋₊, c n * ((a / n - W : ℝ) : ℂ) := by
  have hMN : ⌊a / W⌋₊ ≤ N := by
    have h1 : ((⌊a / W⌋₊ : ℕ) : ℝ) ≤ N := (Nat.floor_le (by positivity)).trans hN
    exact_mod_cast h1
  have hterm : ∀ n ∈ Icc 1 N, c n * ((max (a / n - W) 0 : ℝ) : ℂ) =
      if n ≤ ⌊a / W⌋₊ then c n * ((a / n - W : ℝ) : ℂ) else 0 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast this
    split_ifs with h
    · have h2 : (n : ℝ) ≤ a / W := (Nat.le_floor_iff (by positivity)).1 h
      have h3 : W ≤ a / n := by
        rw [le_div_iff₀ hn0]
        rw [le_div_iff₀ hW] at h2
        linarith
      rw [max_eq_left (by linarith)]
    · have h2 : a / W < n := (Nat.floor_lt (by positivity)).1 (not_le.1 h)
      have h3 : a / n < W := by
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hW] at h2
        linarith
      rw [max_eq_right (by linarith), Complex.ofReal_zero, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hMN⟩, h.2⟩⟩

omit [DecidableEq H] in
/-- The cut sum of a class is `W · G_ψ(a/W)` up to an explicit correction. -/
theorem sum_cut_eq_classCesaro (D : FrobeniusData H) (ℓ : AddChar (SignPair × H) ℂ → ℂ)
    (ψ : AddChar (SignPair × H) ℂ) {N : ℕ} {a W : ℝ} (ha : 0 < a) (hW : 0 < W)
    (hN : a / W ≤ N) :
    ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * classValue D ψ n * ((max (a / n - W) 0 : ℝ) : ℂ) =
      (W : ℂ) * classCesaro D ℓ ψ (a / W) +
        ((if ψ = 0 then ((a * Real.log a - a * Real.log W -
          (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) + a * ℓ ψ else 0) - a * ℓ ψ) := by
  rw [sum_Icc_max_eq _ ha hW hN]
  have hwa : W * (a / W) = a := by field_simp
  have hterm : ∀ n : ℕ, ((a / n - W : ℝ) : ℂ) = (W : ℂ) * ((a / W / n - 1 : ℝ) : ℂ) := by
    intro n
    rw [← Complex.ofReal_mul]
    congr 1
    rw [mul_sub, mul_one, mul_div_assoc', hwa]
  simp_rw [hterm]
  by_cases h0 : ψ = 0
  · subst h0
    rw [if_pos rfl, classCesaro, if_pos rfl, zetaCesaroFunctional]
    simp_rw [classValue_zero, mul_one]
    rw [Real.log_div ha.ne' hW.ne']
    have hs : ∑ n ∈ Icc 1 ⌊a / W⌋₊, (vonMangoldt n : ℂ) * ((W : ℂ) * ((a / W / n - 1 : ℝ) : ℂ)) =
        (W : ℂ) * ((∑ n ∈ Icc 1 ⌊a / W⌋₊, vonMangoldt n * (a / W / n - 1) : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hs]
    generalize (∑ n ∈ Icc 1 ⌊a / W⌋₊, vonMangoldt n * (a / W / n - 1)) = S
    have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
    push_cast
    field_simp
    ring
  · rw [if_neg h0, classCesaro, if_neg h0]
    have hwa' : (W : ℂ) * ((a / W : ℝ) : ℂ) = a := by rw [← Complex.ofReal_mul, hwa]
    rw [mul_add, Finset.mul_sum, ← mul_assoc, hwa']
    have hs : ∀ n ∈ Icc 1 ⌊a / W⌋₊, (vonMangoldt n : ℂ) * classValue D ψ n *
        ((W : ℂ) * ((a / W / n - 1 : ℝ) : ℂ)) =
        (W : ℂ) * ((vonMangoldt n : ℂ) * classValue D ψ n * ((a / W / n - 1 : ℝ) : ℂ)) :=
      fun n _ => by ring
    rw [Finset.sum_congr rfl hs]
    ring

/-! ## The balance identity -/

/-- **The balance identity.** For admissible Frobenius data, `a > 0` and positive weights on the
split classes with `a/w ≤ N`: the weighted inert count minus its main term is the character side. -/
theorem inertTotal_sub_mainTotal (D : FrobeniusData H) (hD : D.Admissible)
    (ℓ : AddChar (SignPair × H) ℂ → ℂ) {a : ℝ} (t : H) {w : SignPair × H → ℝ} (ha : 0 < a)
    (hw : ∀ ρ, IsSplit ρ → 0 < w ρ) {N : ℕ} (hN : ∀ ρ, IsSplit ρ → a / w ρ ≤ N) :
    (inertTotal D N a t w : ℂ) - mainTotal ℓ a w = balanceTotal D ℓ a t w := by
  classical
  have hΦ := splitSet_card_ne_zero (H := H)
  set c : ℂ := 1 / ((splitSet H).card : ℂ) with hc
  -- the correction terms of the inner sums
  set A : SignPair × H → ℂ := fun g => ((a * Real.log a - a * Real.log (w (partnerClass t g)) -
    (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) with hA
  have hinner : ∀ g ∈ nonsplitSet H, ∀ ψ : AddChar (SignPair × H) ℂ,
      ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * classValue D ψ n * cutValue a t w n g =
        ((w (partnerClass t g) : ℝ) : ℂ) * classCesaro D ℓ ψ (a / w (partnerClass t g)) +
          ((if ψ = 0 then A g + a * ℓ ψ else 0) - a * ℓ ψ) := by
    intro g hg ψ
    have hg' : ¬IsSplit g := by simpa [nonsplitSet] using hg
    have hρ := isSplit_partnerClass t hg'
    exact sum_cut_eq_classCesaro D ℓ ψ ha (hw _ hρ) (hN _ hρ)
  rw [inertTotal_eq_characterSum D hD t hw hN]
  have hsplit : ∑ g ∈ nonsplitSet H, ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) *
      ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * classValue D ψ n * cutValue a t w n g =
      ∑ g ∈ nonsplitSet H, ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) *
        ((w (partnerClass t g) : ℝ) : ℂ) * classCesaro D ℓ ψ (a / w (partnerClass t g)) +
      ∑ g ∈ nonsplitSet H, ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) *
        ((if ψ = 0 then A g + a * ℓ ψ else 0) - a * ℓ ψ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g hg => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [hinner g hg ψ]
    ring
  -- the correction sums to the main term
  have hcorr : ∑ g ∈ nonsplitSet H, ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) *
      ((if ψ = 0 then A g + a * ℓ ψ else 0) - a * ℓ ψ) =
      ((splitSet H).card : ℂ) * mainTotal ℓ a w := by
    have h1 : ∀ g : SignPair × H, ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) *
        ((if ψ = 0 then A g + a * ℓ ψ else 0) - a * ℓ ψ) =
        (A g + a * ℓ 0) - a * ∑ ψ : AddChar (SignPair × H) ℂ, ℓ ψ * starRingEnd ℂ (ψ g) := by
      intro g
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, AddChar.zero_apply, map_one, one_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun ψ _ => by ring
    rw [Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_nonsplit_conj]
    have h2 : ∑ ψ : AddChar (SignPair × H) ℂ, ℓ ψ * (((splitSet H).card : ℂ) *
        ((if ψ = 0 then 1 else 0) - (if ψ = splitSign then 1 else 0))) =
        ((splitSet H).card : ℂ) * (ℓ 0 - ℓ splitSign) := by
      simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [h2, Finset.sum_add_distrib, Finset.sum_const, card_nonsplitSet, nsmul_eq_mul]
    have h3 : ∑ g ∈ nonsplitSet H, A g = ((((splitSet H).card : ℝ) *
        (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a) -
        a * ∑ ρ ∈ splitSet H, Real.log (w ρ) : ℝ) : ℂ) := by
      rw [hA]
      simp only []
      rw [← Complex.ofReal_sum]
      congr 1
      have h4 := sum_nonsplit_partnerClass (H := H) t (fun ρ => Real.log (w ρ))
      simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        Finset.sum_const, card_nonsplitSet, nsmul_eq_mul, ← Finset.mul_sum, h4]
      ring
    rw [h3, mainTotal]
    push_cast
    field_simp
    ring
  rw [hsplit, mul_add, hcorr, balanceTotal]
  field_simp
  ring

end Balance

end

end WindowedLandauTheory
