import GaloisForLFunctions.ArtinMertens.ThePrimeIdealsSatisfyChebyshevBounds

/-!
# The soft Mertens theorem for prime ideals

For a number field `K` the Mertens sum of the prime ideals,
`A_K(x) = Σ_{N𝔭^k ≤ x} log N𝔭 / N𝔭^k`, satisfies `A_K(x) = log x + o(log x)`
(`tendsto_primeMertens_div_log`).

* **Counting ideals** (`tendsto_card_idealsLe_div`): `I_K(t)/t → c_K > 0`, the residue of the
  Dedekind zeta function (Mathlib's `tendsto_norm_le_div_atTop₀`).
* **The two sides of the hyperbola identity**: `L(x) = Σ_{N𝔞 ≤ x} log N𝔞` lies between
  `(I(x) − I(⌊x/T⌋)) log(x/T)` and `I(x) log x` (`sum_log_absNorm_idealsLe_le`,
  `sum_log_absNorm_idealsLe_ge`), while `Σ_{N𝔭^k ≤ x} log N𝔭 · I(⌊x/N𝔭^k⌋)` lies between
  `(1 − ε)c x A_K(x) − c t₀ ψ_K(x)` and `(1 + ε)c x A_K(x) + B t₀ ψ_K(x)` once `I(t)` is within
  `εct` of `ct` beyond `t₀` (`primeHyperbola_le`, `primeHyperbola_ge`).
* **The soft Mertens theorem**: with `ψ_K(x) = O(x)` the two estimates squeeze `A_K(x)/log x`
  between `(1 − 2ε)/(1 + ε) − O(1/log x)` and `(1 + ε)/(1 − ε) + O(1/log x)`.

This is the number-field analogue of `Σ_{p ≤ x} log p/p ∼ log x`, with the residue `c_K` cancelling
between the two sides.
-/

noncomputable section

open Finset NumberField Ideal Filter Topology
open scoped Classical nonZeroDivisors

namespace GaloisForLFunctions.ArtinMertens

variable {K : Type*} [Field K] [NumberField K]

local notation "d" => Module.finrank ℤ (𝓞 K)

/-- The **ideal counting function** `I_K(t) = #{𝔞 ≠ 0 : N𝔞 ≤ t}`. -/
def idealCount (K : Type*) [Field K] [NumberField K] (t : ℕ) : ℝ := ((idealsLe K t).card : ℝ)

/-- The **prime Mertens sum** `A_K(x) = Σ_{N𝔭^k ≤ x} log N𝔭 / N𝔭^k`. -/
def primeMertens (K : Type*) [Field K] [NumberField K] (x : ℕ) : ℝ :=
  ∑ pk ∈ primePowersLe K x, Real.log (absNorm pk.1) / (absNorm pk.1 ^ pk.2 : ℕ)

/-- The **prime Chebyshev function** `ψ_K(x) = Σ_{N𝔭^k ≤ x} log N𝔭`. -/
def primeChebyshev (K : Type*) [Field K] [NumberField K] (x : ℕ) : ℝ :=
  ∑ pk ∈ primePowersLe K x, Real.log (absNorm pk.1)

theorem idealCount_nonneg (t : ℕ) : 0 ≤ idealCount K t := Nat.cast_nonneg _

theorem idealCount_zero : idealCount K 0 = 0 := by
  rw [idealCount, Nat.cast_eq_zero, card_eq_zero]
  ext I
  simp only [mem_idealsLe, nonpos_iff_eq_zero, absNorm_eq_zero_iff, Finset.notMem_empty,
    iff_false, not_and]
  exact fun h h' => h h'

theorem idealCount_mono {s t : ℕ} (h : s ≤ t) : idealCount K s ≤ idealCount K t := by
  refine Nat.cast_le.mpr (card_le_card fun I hI => ?_)
  rw [mem_idealsLe] at hI ⊢
  exact ⟨hI.1, hI.2.trans h⟩

theorem log_absNorm_nonneg (I : Ideal (𝓞 K)) : 0 ≤ Real.log (absNorm I) :=
  Real.log_natCast_nonneg _

theorem primeMertens_nonneg (x : ℕ) : 0 ≤ primeMertens K x :=
  sum_nonneg fun _ _ => div_nonneg (log_absNorm_nonneg _) (Nat.cast_nonneg _)

theorem primeChebyshev_le (x : ℕ) : primeChebyshev K x ≤ (d : ℝ) ^ 2 * ((Real.log 4 + 4) * x) :=
  sum_primePowersLe_log_le x

/-- `I_K(t)` agrees with Mathlib's count of non-zero ideals of norm `≤ t`. -/
theorem idealCount_eq (t : ℕ) :
    idealCount K t = Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ (t : ℝ)} := by
  rw [idealCount, ← Nat.card_eq_finsetCard]
  congr 1
  refine Nat.card_congr ⟨fun I => ⟨⟨I.1, ?_⟩, ?_⟩, fun I => ⟨I.1.1, ?_⟩, ?_, ?_⟩
  · exact mem_nonZeroDivisors_of_ne_zero (mem_idealsLe.mp I.2).1
  · exact_mod_cast (mem_idealsLe.mp I.2).2
  · exact mem_idealsLe.mpr ⟨nonZeroDivisors.ne_zero I.1.2, by exact_mod_cast I.2⟩
  · intro I
    rfl
  · intro I
    rfl

/-- **Counting ideals**: `I_K(t)/t → c_K`, the residue of the Dedekind zeta function. -/
theorem tendsto_idealCount_div :
    Tendsto (fun t : ℕ => idealCount K t / t) atTop (𝓝 (dedekindZeta_residue K)) := by
  have h := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  refine h.congr fun t => ?_
  simp only [Function.comp, idealCount_eq]

/-- The ideals of norm `≤ x` have `L(x) ≤ I(x) log x`. -/
theorem sum_log_absNorm_idealsLe_le (x : ℕ) :
    ∑ I ∈ idealsLe K x, Real.log (absNorm I) ≤ idealCount K x * Real.log x := by
  rw [idealCount, ← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun I hI => ?_
  rw [mem_idealsLe] at hI
  have h1 : (1 : ℝ) ≤ absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr fun h => hI.1 (absNorm_eq_zero_iff.mp h)
  exact Real.log_le_log (by linarith) (by exact_mod_cast hI.2)

/-- The ideals of norm in `(⌊x/T⌋, x]` give `L(x) ≥ (I(x) − I(⌊x/T⌋)) log(x/T)`. -/
theorem sum_log_absNorm_idealsLe_ge {x T : ℕ} (hT : 1 ≤ T) (hTx : T ≤ x) :
    (idealCount K x - idealCount K (x / T)) * Real.log ((x : ℝ) / T) ≤
      ∑ I ∈ idealsLe K x, Real.log (absNorm I) := by
  have hsub : idealsLe K (x / T) ⊆ idealsLe K x := fun I hI => by
    rw [mem_idealsLe] at hI ⊢
    exact ⟨hI.1, hI.2.trans (Nat.div_le_self x T)⟩
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hlog0 : 0 ≤ Real.log ((x : ℝ) / T) :=
    Real.log_nonneg (by rw [le_div_iff₀ hT', one_mul]; exact_mod_cast hTx)
  calc (idealCount K x - idealCount K (x / T)) * Real.log ((x : ℝ) / T)
      = ∑ _I ∈ idealsLe K x \ idealsLe K (x / T), Real.log ((x : ℝ) / T) := by
        rw [sum_const, nsmul_eq_mul, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub),
          idealCount, idealCount]
    _ ≤ ∑ I ∈ idealsLe K x \ idealsLe K (x / T), Real.log (absNorm I) := by
        refine sum_le_sum fun I hI => ?_
        rw [Finset.mem_sdiff, mem_idealsLe, mem_idealsLe] at hI
        -- `N𝔞 > ⌊x/T⌋` gives `N𝔞 > x/T`
        have hgt : x / T < absNorm I := by
          by_contra h
          exact hI.2 ⟨hI.1.1, not_lt.mp h⟩
        have hlt := RHTower.Mertens.cast_div_lt x T hT
        have hN : ((x : ℝ) / T) ≤ absNorm I := by
          have : ((x / T : ℕ) : ℝ) + 1 ≤ absNorm I := by exact_mod_cast hgt
          linarith
        exact Real.log_le_log (div_pos (by exact_mod_cast (by omega : 0 < x)) hT') hN
    _ ≤ ∑ I ∈ idealsLe K x, Real.log (absNorm I) :=
        sum_le_sum_of_subset_of_nonneg sdiff_subset fun I _ _ => log_absNorm_nonneg I

/-- **Upper half of the prime side**: if `I(t) ≤ (1 + ε)c t` for `t ≥ t₀` and `I(t) ≤ B t` for all
`t`, then `Σ log N𝔭 · I(⌊x/N𝔭^k⌋) ≤ (1 + ε)c x A_K(x) + B t₀ ψ_K(x)`. -/
theorem primeHyperbola_le {a B : ℝ} {t₀ : ℕ} (ha : 0 ≤ a)
    (hup : ∀ t : ℕ, t₀ ≤ t → idealCount K t ≤ a * t) (hB : ∀ t : ℕ, idealCount K t ≤ B * t)
    (x : ℕ) :
    ∑ pk ∈ primePowersLe K x,
        Real.log (absNorm pk.1) * ((idealsLe K (x / absNorm pk.1 ^ pk.2)).card : ℝ) ≤
      a * x * primeMertens K x + B * t₀ * primeChebyshev K x := by
  rw [primeMertens, primeChebyshev, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun ⟨P, k⟩ hpk => ?_
  rw [mem_primePowersLe] at hpk
  have h2 := two_le_absNorm_of_isPrime hpk.1 hpk.2.1
  have hq : 0 < absNorm P ^ k := pow_pos (by omega) k
  have hq' : (0 : ℝ) < (absNorm P ^ k : ℕ) := by exact_mod_cast hq
  set t := x / absNorm P ^ k
  have hlog := log_absNorm_nonneg P
  have hB0 : 0 ≤ B := by
    have := hB 1
    simp only [Nat.cast_one, mul_one] at this
    exact (idealCount_nonneg 1).trans this
  have htx : (t : ℝ) ≤ (x : ℝ) / (absNorm P ^ k : ℕ) := Nat.cast_div_le
  -- `I(t) ≤ a x/q + B t₀`
  have hterm : idealCount K t ≤ a * ((x : ℝ) / (absNorm P ^ k : ℕ)) + B * t₀ := by
    by_cases ht : t₀ ≤ t
    · have h1 := hup t ht
      have h2' : a * t ≤ a * ((x : ℝ) / (absNorm P ^ k : ℕ)) := mul_le_mul_of_nonneg_left htx ha
      have : 0 ≤ B * (t₀ : ℝ) := by positivity
      linarith
    · have h1 := hB t
      have h2' : B * (t : ℝ) ≤ B * t₀ :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast (not_le.mp ht).le) hB0
      have : 0 ≤ a * ((x : ℝ) / (absNorm P ^ k : ℕ)) := by positivity
      linarith
  have := mul_le_mul_of_nonneg_left hterm hlog
  calc Real.log (absNorm P) * ((idealsLe K t).card : ℝ) = Real.log (absNorm P) * idealCount K t :=
        rfl
    _ ≤ Real.log (absNorm P) * (a * ((x : ℝ) / (absNorm P ^ k : ℕ)) + B * t₀) := this
    _ = a * x * (Real.log (absNorm P) / (absNorm P ^ k : ℕ)) + B * t₀ * Real.log (absNorm P) := by
        field_simp

/-- **Lower half of the prime side**: if `I(t) ≥ a t` for `t ≥ t₀ ≥ 1` with `0 ≤ a ≤ c`, then
`Σ log N𝔭 · I(⌊x/N𝔭^k⌋) ≥ a x A_K(x) − c t₀ ψ_K(x)`. -/
theorem primeHyperbola_ge {a c : ℝ} {t₀ : ℕ} (ha : 0 ≤ a) (hac : a ≤ c) (ht₀ : 1 ≤ t₀)
    (hlow : ∀ t : ℕ, t₀ ≤ t → a * t ≤ idealCount K t) (x : ℕ) :
    a * x * primeMertens K x - c * t₀ * primeChebyshev K x ≤
      ∑ pk ∈ primePowersLe K x,
        Real.log (absNorm pk.1) * ((idealsLe K (x / absNorm pk.1 ^ pk.2)).card : ℝ) := by
  rw [primeMertens, primeChebyshev, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun ⟨P, k⟩ hpk => ?_
  rw [mem_primePowersLe] at hpk
  have h2 := two_le_absNorm_of_isPrime hpk.1 hpk.2.1
  have hq : 0 < absNorm P ^ k := pow_pos (by omega) k
  have hq' : (0 : ℝ) < (absNorm P ^ k : ℕ) := by exact_mod_cast hq
  set t := x / absNorm P ^ k
  have hlog := log_absNorm_nonneg P
  have hlt := RHTower.Mertens.cast_div_lt x (absNorm P ^ k) hq
  have hc0 : 0 ≤ c := ha.trans hac
  have ht₀' : (1 : ℝ) ≤ t₀ := by exact_mod_cast ht₀
  -- `I(t) ≥ a x/q − c t₀`
  have hterm : a * ((x : ℝ) / (absNorm P ^ k : ℕ)) - c * t₀ ≤ idealCount K t := by
    by_cases ht : t₀ ≤ t
    · have h1 := hlow t ht
      have h2' : a * ((x : ℝ) / (absNorm P ^ k : ℕ)) ≤ a * ((t : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hlt.le ha
      nlinarith
    · have htt : (t : ℝ) + 1 ≤ t₀ := by exact_mod_cast (not_le.mp ht)
      have h2' : a * ((x : ℝ) / (absNorm P ^ k : ℕ)) ≤ c * t₀ := by
        calc a * ((x : ℝ) / (absNorm P ^ k : ℕ)) ≤ a * ((t : ℝ) + 1) :=
              mul_le_mul_of_nonneg_left hlt.le ha
          _ ≤ c * t₀ := mul_le_mul hac htt (by positivity) hc0
      linarith [idealCount_nonneg (K := K) t]
  have := mul_le_mul_of_nonneg_left hterm hlog
  calc a * x * (Real.log (absNorm P) / (absNorm P ^ k : ℕ)) - c * t₀ * Real.log (absNorm P)
      = Real.log (absNorm P) * (a * ((x : ℝ) / (absNorm P ^ k : ℕ)) - c * t₀) := by
        field_simp
    _ ≤ Real.log (absNorm P) * idealCount K t := this
    _ = Real.log (absNorm P) * ((idealsLe K t).card : ℝ) := rfl

/-- **The ideal count is pinched**: for every `ε > 0`, `(1 − ε)c_K t ≤ I_K(t) ≤ (1 + ε)c_K t` for
all large `t`. -/
theorem exists_idealCount_band {ε : ℝ} (hε : 0 < ε) : ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
    (1 - ε) * dedekindZeta_residue K * t ≤ idealCount K t ∧
      idealCount K t ≤ (1 + ε) * dedekindZeta_residue K * t := by
  have hc := dedekindZeta_residue_pos K
  obtain ⟨t₁, ht₁⟩ := Metric.tendsto_atTop.mp (tendsto_idealCount_div (K := K))
    (ε * dedekindZeta_residue K) (by positivity)
  refine ⟨max t₁ 1, le_max_right _ _, fun t ht => ?_⟩
  have ht' : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have h := ht₁ t ((le_max_left _ _).trans ht)
  rw [Real.dist_eq, abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  rw [sub_lt_iff_lt_add, div_lt_iff₀ ht'] at h2
  rw [lt_sub_iff_add_lt, lt_div_iff₀ ht'] at h1
  constructor <;> linarith

/-- **A global linear bound** `I_K(t) ≤ B t`. -/
theorem exists_idealCount_le_mul : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℕ, idealCount K t ≤ B * t := by
  obtain ⟨t₀, -, hb⟩ := exists_idealCount_band (K := K) one_pos
  have hc := dedekindZeta_residue_pos K
  have hS : 0 ≤ ∑ s ∈ range t₀, idealCount K s := sum_nonneg fun s _ => idealCount_nonneg s
  refine ⟨2 * dedekindZeta_residue K + ∑ s ∈ range t₀, idealCount K s, by positivity, fun t => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · rw [idealCount_zero, Nat.cast_zero, mul_zero]
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast htpos
  have hct : 0 ≤ dedekindZeta_residue K * t := mul_nonneg hc.le (Nat.cast_nonneg t)
  by_cases ht : t₀ ≤ t
  · have := (hb t ht).2
    linarith [mul_nonneg hS (Nat.cast_nonneg (α := ℝ) t)]
  · have h1 := single_le_sum (f := idealCount K) (fun s _ => idealCount_nonneg s)
      (mem_range.mpr (not_le.mp ht))
    linarith [mul_le_mul_of_nonneg_left ht1 hS]

/-- **Upper Mertens estimate**: if `I(t) ≥ a t` beyond `t₀ ≥ 1` (with `0 ≤ a ≤ c`),
`I(x) ≤ b x` and `ψ_K(x) ≤ D x`, then `a A_K(x) ≤ b log x + c t₀ D`. -/
theorem primeMertens_upper {a b c D : ℝ} {t₀ x : ℕ} (ha : 0 ≤ a) (hac : a ≤ c) (ht₀ : 1 ≤ t₀)
    (hlow : ∀ t : ℕ, t₀ ≤ t → a * t ≤ idealCount K t) (hx : idealCount K x ≤ b * x)
    (hψ : primeChebyshev K x ≤ D * x) (hx0 : 0 < x) :
    a * primeMertens K x ≤ b * Real.log x + c * t₀ * D := by
  have h1 := primeHyperbola_ge ha hac ht₀ hlow x
  rw [← sum_log_absNorm_idealsLe_eq] at h1
  have h2 := sum_log_absNorm_idealsLe_le (K := K) x
  have h3 : idealCount K x * Real.log x ≤ b * x * Real.log x :=
    mul_le_mul_of_nonneg_right hx (Real.log_natCast_nonneg x)
  have h4 : c * t₀ * primeChebyshev K x ≤ c * t₀ * (D * x) :=
    mul_le_mul_of_nonneg_left hψ (mul_nonneg (ha.trans hac) (Nat.cast_nonneg _))
  refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < x by exact_mod_cast hx0)
  linarith

/-- **Lower Mertens estimate**: if `I(t) ≤ b t` beyond `t₀`, `I(t) ≤ B t` always,
`ψ_K(x) ≤ D x` and the ideals of norm in `(⌊x/T⌋, x]` number at least `a x`, then
`a (log x − log T) ≤ b A_K(x) + B t₀ D`. -/
theorem primeMertens_lower {a b B D : ℝ} {t₀ T x : ℕ} (hb : 0 ≤ b) (hB0 : 0 ≤ B)
    (hup : ∀ t : ℕ, t₀ ≤ t → idealCount K t ≤ b * t) (hB : ∀ t : ℕ, idealCount K t ≤ B * t)
    (hψ : primeChebyshev K x ≤ D * x) (hT : 1 ≤ T) (hTx : T ≤ x)
    (hgap : a * x ≤ idealCount K x - idealCount K (x / T)) :
    a * (Real.log x - Real.log T) ≤ b * primeMertens K x + B * t₀ * D := by
  have h1 := primeHyperbola_le hb hup hB x
  rw [← sum_log_absNorm_idealsLe_eq] at h1
  have h2 := sum_log_absNorm_idealsLe_ge (K := K) hT hTx
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hx' : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog : Real.log ((x : ℝ) / T) = Real.log x - Real.log T := Real.log_div hx'.ne' hT'.ne'
  have hlog0 : 0 ≤ Real.log ((x : ℝ) / T) :=
    Real.log_nonneg (by rw [le_div_iff₀ hT', one_mul]; exact_mod_cast hTx)
  have h3 := mul_le_mul_of_nonneg_right hgap hlog0
  have h4 : B * t₀ * primeChebyshev K x ≤ B * t₀ * (D * x) :=
    mul_le_mul_of_nonneg_left hψ (mul_nonneg hB0 (Nat.cast_nonneg _))
  rw [hlog] at h2 h3
  refine le_of_mul_le_mul_right ?_ hx'
  linarith

/-- **The squeeze**: estimates `(1 − ε)c A ≤ (1 + ε)c L + C₁` and
`(1 − 2ε)c (L − l) ≤ (1 + ε)c A + C₂` with `ε ≤ δ/10` and constants below `c δ L/4` force
`|A/L − 1| < δ`. -/
theorem abs_div_sub_one_lt_of_squeeze {A L c ε δ C₁ C₂ l : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) (hεδ : ε ≤ δ / 10) (hL : 0 < L) (hl : 0 ≤ l) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hup : (1 - ε) * c * A ≤ (1 + ε) * c * L + C₁)
    (hlo : (1 - 2 * ε) * c * (L - l) ≤ (1 + ε) * c * A + C₂)
    (hbig : 4 * (C₁ + C₂ + c * l) ≤ c * δ * L) : |A / L - 1| < δ := by
  have hδ : 0 < δ := by linarith
  have k1 : ε * (c * L) ≤ δ / 10 * (c * L) := mul_le_mul_of_nonneg_right hεδ (by positivity)
  have k2 : 0 ≤ ε * (c * l) := by positivity
  have k6 : 0 ≤ c * l := by positivity
  have k3 : 0 ≤ ε * (c * δ * L) := by positivity
  have k4 : 0 < c * δ * L := by positivity
  have k5 : ε * (c * δ * L) ≤ 1 / 10 * (c * δ * L) := mul_le_mul_of_nonneg_right hε1 k4.le
  rw [div_sub_one hL.ne', abs_div, abs_of_pos hL, div_lt_iff₀ hL, abs_lt]
  constructor
  · have key : c * (1 + ε) * (L - A) < c * (1 + ε) * (δ * L) := by linarith
    have := lt_of_mul_lt_mul_left key (by positivity)
    linarith
  · have key : c * (1 - ε) * (A - L) < c * (1 - ε) * (δ * L) := by linarith
    exact lt_of_mul_lt_mul_left key (mul_nonneg hc.le (by linarith))

/-- **The soft Mertens theorem for prime ideals**: `A_K(x)/log x → 1`. -/
theorem tendsto_primeMertens_div_log :
    Tendsto (fun x : ℕ => primeMertens K x / Real.log x) atTop (𝓝 1) := by
  obtain ⟨c, hc, hband⟩ : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ t₀ : ℕ, 1 ≤ t₀ ∧
      ∀ t : ℕ, t₀ ≤ t → (1 - ε) * c * t ≤ idealCount K t ∧ idealCount K t ≤ (1 + ε) * c * t :=
    ⟨_, dedekindZeta_residue_pos K, fun ε hε => exists_idealCount_band hε⟩
  obtain ⟨B, hB0, hB⟩ := exists_idealCount_le_mul (K := K)
  obtain ⟨D, hD, hψ⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℕ, primeChebyshev K x ≤ D * x :=
    ⟨(d : ℝ) ^ 2 * (Real.log 4 + 4),
      mul_nonneg (by positivity) (add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)),
      fun x => (primeChebyshev_le x).trans_eq (by ring)⟩
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨ε, hε, hε1, hεδ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 10 ∧ ε ≤ δ / 10 :=
    ⟨min δ 1 / 10, by positivity, by linarith [min_le_right δ 1], by linarith [min_le_left δ 1]⟩
  obtain ⟨t₀, ht₀, hb⟩ := hband ε hε
  -- a cutoff `T` with `I(⌊x/T⌋) ≤ ε c x`
  obtain ⟨T, hT⟩ := exists_nat_gt (B / (ε * c))
  have hTpos : (0 : ℝ) < T := lt_of_le_of_lt (div_nonneg hB0 (by positivity)) hT
  have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hTpos)
  have hBT : B / T ≤ ε * c := by
    rw [div_lt_iff₀ (by positivity)] at hT
    rw [div_le_iff₀ hTpos]
    linarith
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hlog.eventually_ge_atTop
    (4 * (c * t₀ * D + B * t₀ * D + c * Real.log T) / (c * δ)))
  refine ⟨max X (max (max t₀ T) 2), fun x hx => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxt₀ : t₀ ≤ x :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
  have hxT : T ≤ x :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hx))
  have hx2 : 2 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hlogx : 0 < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hIT : idealCount K (x / T) ≤ ε * c * x :=
    calc idealCount K (x / T) ≤ B * ((x / T : ℕ) : ℝ) := hB _
      _ ≤ B * ((x : ℝ) / T) := mul_le_mul_of_nonneg_left Nat.cast_div_le hB0
      _ = B / T * x := by ring
      _ ≤ ε * c * x := mul_le_mul_of_nonneg_right hBT (Nat.cast_nonneg x)
  have hup := primeMertens_upper (c := c) (mul_nonneg (by linarith) hc.le)
    (by linarith [mul_pos hε hc]) ht₀ (fun t ht => (hb t ht).1) (hb x hxt₀).2 (hψ x)
    (by omega)
  have hlo := primeMertens_lower (a := (1 - 2 * ε) * c) (mul_nonneg (by linarith) hc.le) hB0
    (fun t ht => (hb t ht).2) hB (hψ x) hT1 hxT (by linarith [(hb x hxt₀).1])
  have hbig : 4 * (c * t₀ * D + B * t₀ * D + c * Real.log T) ≤ c * δ * Real.log x := by
    have h := hX x hxX
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  rw [Real.dist_eq]
  exact abs_div_sub_one_lt_of_squeeze hc hε hε1 hεδ hlogx (Real.log_natCast_nonneg T)
    (mul_nonneg (mul_nonneg hc.le (Nat.cast_nonneg _)) hD)
    (mul_nonneg (mul_nonneg hB0 (Nat.cast_nonneg _)) hD) hup hlo hbig

end GaloisForLFunctions.ArtinMertens
