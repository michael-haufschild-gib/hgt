import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import Mathlib

/-!
# The multiplicative energy of a Burgess box

For a prime `p`, `A, N ≥ 1` with `4AN ≤ p` and any `M ∈ ℤ`, the number of solutions of

  `a₂ (M + m₁) ≡ a₁ (M + m₂) (mod p)`,  `a₁, a₂ ∈ (A, 2A]`, `m₁, m₂ ∈ [0, N)`

is at most `A² + 8AN(1 + log 2A)` (`burgessEnergy_le`). For fixed `(a₁, a₂)` the solutions form a
coset of a lattice, so differences put them in the box `|u|, |v| < N` (`card_shift_le`); there
`|a₂u − a₁v| < 4AN ≤ p`, so the congruence is an equation (`eq_of_modEq_of_lt`), whose solutions
are determined by `u`, a multiple of `a₁/gcd(a₁, a₂)` (`card_eq_solutions_le`). Summing,
`Σ gcd(a₁, a₂) ≤ (2A)²(1 + log 2A)` (`sum_gcd_le`).
-/

open Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- Multiples of `k` in `(−N, N)`: at most `2N/k + 1`. -/
theorem card_filter_dvd_Ioo_le {k : ℕ} (hk : 0 < k) (N : ℕ) :
    (((Ioo (-(N : ℤ)) N).filter fun u => (k : ℤ) ∣ u).card : ℝ) ≤ 2 * N / k + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set T : ℤ := (N - 1) / k
  have hsub : (Ioo (-(N : ℤ)) N).filter (fun u => (k : ℤ) ∣ u) ⊆
      (Icc (-T) T).image fun t => (k : ℤ) * t := by
    intro u hu
    obtain ⟨hu, t, rfl⟩ := Finset.mem_filter.mp hu
    obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hu
    refine Finset.mem_image.mpr ⟨t, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have : (k : ℤ) * (-t) ≤ N - 1 := by linarith
      have := Int.le_ediv_of_mul_le (by exact_mod_cast hk) (by linarith : -t * k ≤ N - 1)
      linarith
    · exact Int.le_ediv_of_mul_le (by exact_mod_cast hk) (by linarith)
  have hT0 : 0 ≤ T := Int.ediv_nonneg (by omega) (by positivity)
  have hTk : (T : ℝ) * k ≤ N := by
    have := Int.ediv_mul_le (N - 1 : ℤ) (by exact_mod_cast hk.ne' : (k : ℤ) ≠ 0)
    have h' : (T * k : ℤ) ≤ N := by linarith
    exact_mod_cast h'
  calc (((Ioo (-(N : ℤ)) N).filter fun u => (k : ℤ) ∣ u).card : ℝ)
      ≤ ((Icc (-T) T).image fun t => (k : ℤ) * t).card := by exact_mod_cast card_le_card hsub
    _ ≤ (Icc (-T) T).card := by exact_mod_cast Finset.card_image_le
    _ = 2 * T + 1 := by
        rw [Int.card_Icc]
        have : (T + 1 - -T).toNat = 2 * T + 1 := by omega
        rw [show ((T + 1 - -T).toNat : ℝ) = ((T + 1 - -T).toNat : ℤ) by norm_cast, this]
        push_cast; ring
    _ ≤ 2 * N / k + 1 := by
        have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
        have : (T : ℝ) ≤ N / k := by rw [le_div_iff₀ hkpos]; exact hTk
        have h2 : 2 * (T : ℝ) ≤ 2 * N / k := by rw [mul_div_assoc]; linarith
        linarith

/-- **Exact solutions**: `#{|u|, |v| < N : a₂u = a₁v} ≤ 2N gcd(a₁, a₂)/a₁ + 1`; `u` determines `v`
and is a multiple of `a₁/gcd(a₁, a₂)`. -/
theorem card_eq_solutions_le {a₁ a₂ : ℕ} (h₁ : 0 < a₁) (N : ℕ) :
    ((((Ioo (-(N : ℤ)) N) ×ˢ (Ioo (-(N : ℤ)) N)).filter fun q => (a₂ : ℤ) * q.1 = a₁ * q.2).card
      : ℝ) ≤ 2 * N * Nat.gcd a₁ a₂ / a₁ + 1 := by
  set g := Nat.gcd a₁ a₂
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ h₁
  set k := a₁ / g
  set k₂ := a₂ / g
  have hk : 0 < k := Nat.div_pos (Nat.gcd_le_left _ h₁) hg
  have hcop : Nat.Coprime k k₂ := Nat.coprime_div_gcd_div_gcd hg
  have ha₁ : a₁ = g * k := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a₁ a₂)).symm
  have ha₂ : a₂ = g * k₂ := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ a₂)).symm
  have hinj : Set.InjOn Prod.fst
      ((((Ioo (-(N : ℤ)) N) ×ˢ (Ioo (-(N : ℤ)) N)).filter fun q =>
        (a₂ : ℤ) * q.1 = a₁ * q.2 : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
    intro q hq q' hq' h
    have e := (Finset.mem_filter.mp hq).2
    have e' := (Finset.mem_filter.mp hq').2
    have h1 : (a₁ : ℤ) ≠ 0 := by exact_mod_cast h₁.ne'
    refine Prod.ext h ?_
    have : (a₁ : ℤ) * q.2 = a₁ * q'.2 := by rw [← e, ← e', h]
    exact mul_left_cancel₀ h1 this
  have hmaps : ∀ q ∈ ((Ioo (-(N : ℤ)) N) ×ˢ (Ioo (-(N : ℤ)) N)).filter
      (fun q => (a₂ : ℤ) * q.1 = a₁ * q.2),
      q.1 ∈ (Ioo (-(N : ℤ)) N).filter fun u => (k : ℤ) ∣ u := by
    intro q hq
    obtain ⟨hq, e⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hq).1, ?_⟩
    have e2 : (k₂ : ℤ) * q.1 = k * q.2 := by
      have hg' : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
      rw [ha₁, ha₂] at e
      push_cast at e
      exact mul_left_cancel₀ hg' (by linear_combination e)
    refine Int.dvd_of_dvd_mul_right_of_gcd_one (b := k₂) ⟨q.2, by rw [e2]⟩ ?_
    rw [Int.gcd_natCast_natCast]; exact hcop
  have hcard := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
  calc _ ≤ (((Ioo (-(N : ℤ)) N).filter fun u => (k : ℤ) ∣ u).card : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * N / k + 1 := card_filter_dvd_Ioo_le hk N
    _ = 2 * N * g / a₁ + 1 := by
        rw [ha₁]
        push_cast
        have : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
        field_simp

/-- **A small congruence is an equation**: if `2 max(a₁, a₂) N ≤ p` and `|u|, |v| < N`, then
`a₂u ≡ a₁v (mod p)` forces `a₂u = a₁v`. -/
theorem eq_of_modEq_of_lt {p a₁ a₂ N : ℕ} (h₁ : 0 < a₁) (hp : 2 * max a₁ a₂ * N ≤ p) {u v : ℤ}
    (hu : |u| < N) (hv : |v| < N) (h : ((a₂ * u : ℤ) : ZMod p) = ((a₁ * v : ℤ) : ZMod p)) :
    (a₂ : ℤ) * u = a₁ * v := by
  have hdvd : (p : ℤ) ∣ a₂ * u - a₁ * v := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast at h ⊢; rw [h, sub_self]
  have hpos : (0 : ℤ) < max a₁ a₂ := by
    have : 0 < max a₁ a₂ := lt_of_lt_of_le h₁ (le_max_left _ _)
    exact_mod_cast this
  have h1 : |(a₂ : ℤ) * u| ≤ max a₁ a₂ * |u| := by
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right _ _) (abs_nonneg _)
  have h2 : |(a₁ : ℤ) * v| ≤ max a₁ a₂ * |v| := by
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left _ _) (abs_nonneg _)
  have hp' : (2 * max a₁ a₂ * N : ℤ) ≤ p := by exact_mod_cast hp
  have hlt : |(a₂ : ℤ) * u - a₁ * v| < p :=
    calc |(a₂ : ℤ) * u - a₁ * v| ≤ |(a₂ : ℤ) * u| + |(a₁ : ℤ) * v| := abs_sub _ _
      _ ≤ max a₁ a₂ * |u| + max a₁ a₂ * |v| := add_le_add h1 h2
      _ < max a₁ a₂ * N + max a₁ a₂ * N :=
          add_lt_add (mul_lt_mul_of_pos_left hu hpos) (mul_lt_mul_of_pos_left hv hpos)
      _ ≤ p := by linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  linarith

/-- **The difference trick**: for fixed `(a₁, a₂)` the solutions `m ∈ [0, N)²` of
`a₂(M + m₁) ≡ a₁(M + m₂)` number at most `2N gcd(a₁, a₂)/a₁ + 1`. -/
theorem card_shift_le {p a₁ a₂ N : ℕ} (h₁ : 0 < a₁) (hp : 2 * max a₁ a₂ * N ≤ p) (M : ℤ) :
    ((((range N) ×ˢ (range N)).filter fun m : ℕ × ℕ =>
        ((a₂ * (M + m.1) : ℤ) : ZMod p) = ((a₁ * (M + m.2) : ℤ) : ZMod p)).card : ℝ) ≤
      2 * N * Nat.gcd a₁ a₂ / a₁ + 1 := by
  set Sol := ((range N) ×ˢ (range N)).filter fun m : ℕ × ℕ =>
    ((a₂ * (M + m.1) : ℤ) : ZMod p) = ((a₁ * (M + m.2) : ℤ) : ZMod p)
  rcases Sol.eq_empty_or_nonempty with h | ⟨m₀, hm₀⟩
  · rw [h, card_empty, Nat.cast_zero]; positivity
  set f : ℕ × ℕ → ℤ × ℤ := fun m => ((m.1 : ℤ) - m₀.1, (m.2 : ℤ) - m₀.2)
  have hinj : Set.InjOn f (Sol : Set (ℕ × ℕ)) := by
    intro m _ m' _ h
    simp only [f, Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  obtain ⟨hm₀r, hm₀e⟩ := Finset.mem_filter.mp hm₀
  obtain ⟨hm₀1, hm₀2⟩ := Finset.mem_product.mp hm₀r
  have hmaps : ∀ m ∈ Sol, f m ∈ ((Ioo (-(N : ℤ)) N) ×ˢ (Ioo (-(N : ℤ)) N)).filter
      fun q => (a₂ : ℤ) * q.1 = a₁ * q.2 := by
    intro m hm
    obtain ⟨hmr, hme⟩ := Finset.mem_filter.mp hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_product.mp hmr
    rw [Finset.mem_range] at hm1 hm2 hm₀1 hm₀2
    have hu : |(m.1 : ℤ) - m₀.1| < N := by rw [abs_lt]; constructor <;> omega
    have hv : |(m.2 : ℤ) - m₀.2| < N := by rw [abs_lt]; constructor <;> omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioo.mpr
      ⟨by rw [abs_lt] at hu; exact hu.1, by rw [abs_lt] at hu; exact hu.2⟩, Finset.mem_Ioo.mpr
      ⟨by rw [abs_lt] at hv; exact hv.1, by rw [abs_lt] at hv; exact hv.2⟩⟩, ?_⟩
    refine eq_of_modEq_of_lt h₁ hp hu hv ?_
    simp only [f]
    push_cast at hme hm₀e ⊢
    linear_combination hme - hm₀e
  calc (Sol.card : ℝ) ≤ (((Ioo (-(N : ℤ)) N) ×ˢ (Ioo (-(N : ℤ)) N)).filter
        fun q => (a₂ : ℤ) * q.1 = a₁ * q.2).card := by
        exact_mod_cast Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ _ := card_eq_solutions_le h₁ N

/-- `Σ_{a₁, a₂ ≤ K} gcd(a₁, a₂) ≤ K²(1 + log K)`: `gcd ≤ Σ_{d ∣ a₁, d ∣ a₂} d`, and `d` divides
`⌊K/d⌋²` pairs. -/
theorem sum_gcd_le (K : ℕ) :
    (∑ a₁ ∈ Icc 1 K, ∑ a₂ ∈ Icc 1 K, (Nat.gcd a₁ a₂ : ℝ)) ≤ K ^ 2 * (1 + Real.log K) := by
  have hpt : ∀ a₁ ∈ Icc 1 K, ∀ a₂ ∈ Icc 1 K, (Nat.gcd a₁ a₂ : ℝ) ≤
      ∑ d ∈ Icc 1 K, if d ∣ a₁ ∧ d ∣ a₂ then (d : ℝ) else 0 := by
    intro a₁ ha₁ a₂ ha₂
    have hg : Nat.gcd a₁ a₂ ∈ Icc 1 K := by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha₁
      exact Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_left _ (by omega),
        (Nat.gcd_le_left _ (by omega)).trans h2⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun d => if d ∣ a₁ ∧ d ∣ a₂ then (d : ℝ) else 0)
      (fun d _ => by split_ifs <;> positivity) hg)
    rw [if_pos ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩]
  have hcount : ∀ d ∈ Icc 1 K, (((Icc 1 K).filter fun a => d ∣ a).card : ℝ) ≤ K / d := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by have := (Finset.mem_Icc.mp hd).1; exact_mod_cast this
    have : (Icc 1 K).filter (fun a => d ∣ a) = (Ioc 0 K).filter (fun a => d ∣ a) := by
      congr 1
    rw [this, Nat.Ioc_filter_dvd_card_eq_div, le_div_iff₀ hd0]
    exact_mod_cast Nat.div_mul_le_self K d
  calc (∑ a₁ ∈ Icc 1 K, ∑ a₂ ∈ Icc 1 K, (Nat.gcd a₁ a₂ : ℝ))
      ≤ ∑ a₁ ∈ Icc 1 K, ∑ a₂ ∈ Icc 1 K, ∑ d ∈ Icc 1 K,
          if d ∣ a₁ ∧ d ∣ a₂ then (d : ℝ) else 0 :=
        Finset.sum_le_sum fun a₁ ha₁ => Finset.sum_le_sum fun a₂ ha₂ => hpt a₁ ha₁ a₂ ha₂
    _ = ∑ d ∈ Icc 1 K, (d : ℝ) * (((Icc 1 K).filter fun a => d ∣ a).card : ℝ) ^ 2 := by
        rw [Finset.sum_congr rfl fun a₁ _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        have : ∀ a₁ a₂ : ℕ, (if d ∣ a₁ ∧ d ∣ a₂ then (d : ℝ) else 0) =
            d * ((if d ∣ a₁ then 1 else 0) * (if d ∣ a₂ then 1 else 0)) := by
          intro a₁ a₂
          by_cases h1 : d ∣ a₁ <;> by_cases h2 : d ∣ a₂ <;> simp [h1, h2]
        rw [Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => this a₁ a₂]
        have hfac : ∑ a₁ ∈ Icc 1 K, ∑ a₂ ∈ Icc 1 K,
            (d : ℝ) * ((if d ∣ a₁ then 1 else 0) * (if d ∣ a₂ then 1 else 0)) =
            d * ((∑ a₁ ∈ Icc 1 K, if d ∣ a₁ then (1 : ℝ) else 0) *
              ∑ a₂ ∈ Icc 1 K, if d ∣ a₂ then (1 : ℝ) else 0) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a₁ _ => ?_
          rw [Finset.mul_sum]
        rw [hfac, Finset.sum_boole]
        ring
    _ ≤ ∑ d ∈ Icc 1 K, (K : ℝ) ^ 2 * (1 / d) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd0 : (0 : ℝ) < d := by have := (Finset.mem_Icc.mp hd).1; exact_mod_cast this
        have h := hcount d hd
        have h0 : (0 : ℝ) ≤ ((Icc 1 K).filter fun a => d ∣ a).card := Nat.cast_nonneg _
        calc (d : ℝ) * (((Icc 1 K).filter fun a => d ∣ a).card : ℝ) ^ 2 ≤ d * (K / d) ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 2) hd0.le
          _ = K ^ 2 * (1 / d) := by field_simp
    _ = K ^ 2 * ∑ d ∈ Icc 1 K, 1 / (d : ℝ) := by rw [Finset.mul_sum]
    _ ≤ K ^ 2 * (1 + Real.log K) :=
        mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_Icc_one_div_le_one_add_log K) (by positivity)

/-- The solutions `(a₁, a₂, m₁, m₂) ∈ (A, 2A]² × [0, N)²` of `a₂(M + m₁) ≡ a₁(M + m₂) (mod p)`. -/
noncomputable def burgessEnergy (p A N : ℕ) (M : ℤ) : ℕ :=
  ((((Ioc A (2 * A)) ×ˢ (Ioc A (2 * A))) ×ˢ ((range N) ×ˢ (range N))).filter
    fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      ((q.1.2 * (M + q.2.1) : ℤ) : ZMod p) = ((q.1.1 * (M + q.2.2) : ℤ) : ZMod p)).card

/-- **The Burgess energy**: `4AN ≤ p` gives at most `A² + 8AN(1 + log 2A)` solutions. -/
theorem burgessEnergy_le {p A N : ℕ} (hA : 1 ≤ A) (hp : 4 * A * N ≤ p) (M : ℤ) :
    (burgessEnergy p A N M : ℝ) ≤ A ^ 2 + 8 * A * N * (1 + Real.log (2 * A)) := by
  set I := Ioc A (2 * A)
  have hfib : (burgessEnergy p A N M : ℝ) = ∑ a₁ ∈ I, ∑ a₂ ∈ I,
      ((((range N) ×ˢ (range N)).filter fun m : ℕ × ℕ =>
        ((a₂ * (M + m.1) : ℤ) : ZMod p) = ((a₁ * (M + m.2) : ℤ) : ZMod p)).card : ℝ) := by
    unfold burgessEnergy
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_product]
    push_cast
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
    rw [Finset.card_filter]
    push_cast
    rfl
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hterm : ∀ a₁ ∈ I, ∀ a₂ ∈ I,
      ((((range N) ×ˢ (range N)).filter fun m : ℕ × ℕ =>
        ((a₂ * (M + m.1) : ℤ) : ZMod p) = ((a₁ * (M + m.2) : ℤ) : ZMod p)).card : ℝ) ≤
      2 * N * Nat.gcd a₁ a₂ / A + 1 := by
    intro a₁ ha₁ a₂ ha₂
    obtain ⟨h1l, h1r⟩ := Finset.mem_Ioc.mp ha₁
    obtain ⟨h2l, h2r⟩ := Finset.mem_Ioc.mp ha₂
    have hmax : 2 * max a₁ a₂ * N ≤ p := by
      have : max a₁ a₂ ≤ 2 * A := max_le h1r h2r
      calc 2 * max a₁ a₂ * N ≤ 2 * (2 * A) * N := by gcongr
        _ = 4 * A * N := by ring
        _ ≤ p := hp
    refine (card_shift_le (by omega) hmax M).trans ?_
    have ha₁ : (A : ℝ) ≤ a₁ := by exact_mod_cast h1l.le
    have hnum : (0 : ℝ) ≤ 2 * N * Nat.gcd a₁ a₂ := by positivity
    have := div_le_div_of_nonneg_left hnum hA0 ha₁
    linarith
  have hgcd : ∑ a₁ ∈ I, ∑ a₂ ∈ I, (Nat.gcd a₁ a₂ : ℝ) ≤ (2 * A) ^ 2 * (1 + Real.log (2 * A)) := by
    have hsub : I ⊆ Icc 1 (2 * A) := by
      intro a ha
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp ha
      exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
    have h := sum_gcd_le (2 * A)
    push_cast at h
    refine le_trans ?_ h
    calc ∑ a₁ ∈ I, ∑ a₂ ∈ I, (Nat.gcd a₁ a₂ : ℝ) ≤ ∑ a₁ ∈ I, ∑ a₂ ∈ Icc 1 (2 * A),
          (Nat.gcd a₁ a₂ : ℝ) :=
          Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum_of_subset_of_nonneg hsub
            fun _ _ _ => Nat.cast_nonneg _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hcardI : (I.card : ℝ) = A := by
    rw [Nat.card_Ioc, show 2 * A - A = A by omega]
  rw [hfib]
  calc ∑ a₁ ∈ I, ∑ a₂ ∈ I, ((((range N) ×ˢ (range N)).filter fun m : ℕ × ℕ =>
        ((a₂ * (M + m.1) : ℤ) : ZMod p) = ((a₁ * (M + m.2) : ℤ) : ZMod p)).card : ℝ)
      ≤ ∑ a₁ ∈ I, ∑ a₂ ∈ I, (2 * (N : ℝ) * (Nat.gcd a₁ a₂ : ℝ) / A + 1) :=
        Finset.sum_le_sum fun a₁ ha₁ => Finset.sum_le_sum fun a₂ ha₂ => hterm a₁ ha₁ a₂ ha₂
    _ = 2 * N / A * ∑ a₁ ∈ I, ∑ a₂ ∈ I, (Nat.gcd a₁ a₂ : ℝ) + (I.card : ℝ) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
        rw [sq, mul_one]
        congr 1
        refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
        ring
    _ ≤ 2 * N / A * ((2 * A) ^ 2 * (1 + Real.log (2 * A))) + A ^ 2 := by
        rw [hcardI]
        gcongr
    _ = A ^ 2 + 8 * A * N * (1 + Real.log (2 * A)) := by
        field_simp
        ring

end GaloisForLFunctions.ArithmeticEffectivityTheory
