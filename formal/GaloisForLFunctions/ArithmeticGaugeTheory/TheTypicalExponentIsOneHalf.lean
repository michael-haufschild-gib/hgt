import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentZeroOneLaw
import GaloisForLFunctions.ArithmeticGaugeTheory.TheDivisorCollapse
import GaloisForLFunctions.HTGeometry.FourthMomentEscape
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The typical exponent is one half

The zero–one law gives a constant `θ_typ ≤ 1/2` equal to the Möbius gauge exponent at Haar-almost
every point (`ae_gaugeExponent_moebius_eq_typical`). This module proves `θ_typ = 1/2`, for every
bounded source that is unimodular at the primes.

* **The top primes are independent coordinates** (`partialSum_add_gaugeRestrict`). The integers
  `n ≤ 2M` with a prime factor `p ∈ (M, 2M]` are the primes `p` themselves. Translating a gauge point
  `x` by a point `y` supported on these primes moves only their terms:
  `S_{2M}(x + y) = B(x) + Σ_{M < p ≤ 2M} a(p) χ_x(p) χ_y(p)`.
* **Paley–Zygmund on a block** (`block_paleyZygmund`). For fixed `x` the right side is a constant plus
  a sum of `#T` independent Steinhaus variables. Products of two elements of `{1} ∪ primes` determine the
  pair (`mul_eq_mul_of_one_or_prime`), so its fourth moment is at most twice the squared second moment
  (`integral_normSq_sq_twistSum_le`), and `|S_{2M}(x + y)|² > #T/2` with probability at least `1/8`.
* **Averaging over translations** (`le_measure_of_translates`). Haar measure is translation
  invariant, so the bound for every fibre gives `μ{|S_{2M}|² > #T/2} ≥ 1/8`
  (`measure_partialSum_large_ge`).
* **Many top primes** (`exists_card_topPrimes_gt`). By the prime number theorem `#T ~ M/log M`, which
  beats every power `M^a` with `a < 1`.
* **The typical exponent** (`typicalExponent_eq_half`, `ae_gaugeExponent_eq_half`). For every bounded
  source with `|a(p)| = 1` at the primes, a power bound with exponent `θ < 1/2` would confine `S_{2M}`
  to `|S_{2M}|² ≤ #T/2` for some `M`, an event of measure at most `7/8`; so no level below `1/2` is
  typical. For tail-invariant sources the zero–one law makes the exponent almost surely `1/2`; the
  Möbius source is one (`ae_gaugeExponent_moebius_eq_half`).

So Haar-almost every gauge point has Möbius exponent exactly `1/2`, and RH is the statement that the
trivial point has the typical exponent (`riemannHypothesis_iff_trivialPoint_typical`). The lower
bound uses only the independence of the prime coordinates and the size of one prime block; it says
nothing about the trivial point, whose exponent is `Θ`.
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### Gauge Parseval with repeated indices -/

/-- **Gauge Parseval with repetitions.** For a sum `D = Σ_t d_t χ(m_t)` over positive indices,
`∫ |D|² = Σ_{m_t = m_u} d_t conj(d_u)`. -/
theorem integral_normSq_sum_twist {ι : Type*} (T : Finset ι) (d : ι → ℂ) (m : ι → ℕ)
    (hm : ∀ t ∈ T, m t ≠ 0) :
    ((∫ y, ‖∑ t ∈ T, d t * twist y (m t)‖ ^ 2 ∂gaugeHaar : ℝ) : ℂ) =
      ∑ t ∈ T, ∑ u ∈ T, if m t = m u then d t * conj (d u) else 0 := by
  rw [← integral_complex_ofReal]
  have hpt : ∀ y : GaugeTorus, ((‖∑ t ∈ T, d t * twist y (m t)‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ T, ∑ u ∈ T, d t * conj (d u) * (twist y (m t) * conj (twist y (m u))) := by
    intro y
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, sum_mul_sum]
    refine sum_congr rfl fun t _ => sum_congr rfl fun u _ => ?_
    rw [map_mul]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun u _ =>
    (integrable_twist_mul_conj _ _).const_mul _]
  refine sum_congr rfl fun t ht => ?_
  rw [integral_finsetSum _ fun u _ => (integrable_twist_mul_conj _ _).const_mul _]
  refine sum_congr rfl fun u hu => ?_
  rw [integral_const_mul, integral_twist_mul_conj (hm t ht) (hm u hu)]
  split_ifs <;> simp

/-! ### The fourth moment of a block -/

/-- A prime dividing a product of two elements of `{1} ∪ primes` is one of them. -/
theorem eq_or_eq_of_prime_dvd_mul {p a b : ℕ} (hp : p.Prime) (ha : a = 1 ∨ a.Prime)
    (hb : b = 1 ∨ b.Prime) (h : p ∣ a * b) : p = a ∨ p = b := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
  · left
    rcases ha with rfl | ha
    · exact absurd (Nat.dvd_one.mp h') hp.one_lt.ne'
    · exact (Nat.prime_dvd_prime_iff_eq hp ha).mp h'
  · right
    rcases hb with rfl | hb
    · exact absurd (Nat.dvd_one.mp h') hp.one_lt.ne'
    · exact (Nat.prime_dvd_prime_iff_eq hp hb).mp h'

/-- **Product rigidity.** A product of two elements of `{1} ∪ primes` determines the unordered pair. -/
theorem mul_eq_mul_of_one_or_prime {i j k l : ℕ} (hi : i = 1 ∨ i.Prime) (hj : j = 1 ∨ j.Prime)
    (hk : k = 1 ∨ k.Prime) (hl : l = 1 ∨ l.Prime) (h : i * j = k * l) :
    (k = i ∧ l = j) ∨ (k = j ∧ l = i) := by
  have hk0 : k ≠ 0 := by rcases hk with rfl | hk <;> [omega; exact hk.ne_zero]
  have hl0 : l ≠ 0 := by rcases hl with rfl | hl <;> [omega; exact hl.ne_zero]
  rcases hi with rfl | hi
  · rcases hj with rfl | hj
    · obtain ⟨rfl, rfl⟩ := mul_eq_one.mp h.symm
      exact Or.inl ⟨rfl, rfl⟩
    · rw [one_mul] at h
      rcases eq_or_eq_of_prime_dvd_mul hj hk hl (h ▸ dvd_rfl) with rfl | rfl
      · exact Or.inr ⟨rfl, (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0)
          (by rw [mul_one]; exact h)).symm⟩
      · exact Or.inl ⟨(Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hl0)
          (by rw [one_mul]; exact h)).symm, rfl⟩
  · rcases eq_or_eq_of_prime_dvd_mul hi hk hl (h ▸ dvd_mul_right i j) with rfl | rfl
    · exact Or.inl ⟨rfl, (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) h).symm⟩
    · exact Or.inr ⟨(Nat.eq_of_mul_eq_mul_left hi.pos (by rw [h, mul_comm])).symm, rfl⟩

/-- **The fourth moment of a block.** For a twisted sum supported on `{1} ∪ primes`,
`∫ |Y|⁴ ≤ 2 (∫ |Y|²)²`. -/
theorem integral_normSq_sq_twistSum_le {s : Finset ℕ} (hs : ∀ n ∈ s, n = 1 ∨ n.Prime)
    (c : ℕ → ℂ) :
    ∫ y, (‖twistSum s c y‖ ^ 2) ^ 2 ∂gaugeHaar ≤ 2 * (∑ n ∈ s, ‖c n‖ ^ 2) ^ 2 := by
  have hs0 : ∀ n ∈ s, n ≠ 0 := fun n hn => by
    rcases hs n hn with h | h
    · omega
    · exact h.ne_zero
  set d : ℕ × ℕ → ℂ := fun t => c t.1 * c t.2 with hd
  have hpt : ∀ y : GaugeTorus, (‖twistSum s c y‖ ^ 2) ^ 2 =
      ‖∑ t ∈ s ×ˢ s, d t * twist y (t.1 * t.2)‖ ^ 2 := by
    intro y
    have hsq : twistSum s c y ^ 2 = ∑ t ∈ s ×ˢ s, d t * twist y (t.1 * t.2) := by
      rw [twistSum, sq, sum_mul_sum, sum_product]
      refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
      rw [hd, twist_mul y (hs0 i hi) (hs0 j hj)]
      ring
    rw [← hsq, norm_pow]
  simp_rw [hpt]
  have hP := integral_normSq_sum_twist (s ×ˢ s) d (fun t => t.1 * t.2) fun t ht => by
    obtain ⟨h1, h2⟩ := mem_product.mp ht
    exact mul_ne_zero (hs0 _ h1) (hs0 _ h2)
  set I := ∫ y, ‖∑ t ∈ s ×ˢ s, d t * twist y (t.1 * t.2)‖ ^ 2 ∂gaugeHaar with hI
  have hIle : I ≤ ‖(I : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self I
  -- Each pair `t` meets at most itself and its swap.
  have hrow : ∀ t ∈ s ×ˢ s, ∑ u ∈ s ×ˢ s,
      ‖if t.1 * t.2 = u.1 * u.2 then d t * conj (d u) else 0‖ ≤ 2 * ‖d t‖ ^ 2 := by
    intro t ht
    have hswap : t.swap ∈ s ×ˢ s := mem_product.mpr ⟨(mem_product.mp ht).2, (mem_product.mp ht).1⟩
    have hdswap : ‖d t.swap‖ = ‖d t‖ := by
      simp only [hd, Prod.fst_swap, Prod.snd_swap, norm_mul]
      ring
    calc ∑ u ∈ s ×ˢ s, ‖if t.1 * t.2 = u.1 * u.2 then d t * conj (d u) else 0‖
        ≤ ∑ u ∈ s ×ˢ s, ((if u = t then ‖d t‖ * ‖d u‖ else 0) +
            (if u = t.swap then ‖d t‖ * ‖d u‖ else 0)) := by
          refine sum_le_sum fun u hu => ?_
          split_ifs with h1 h2 h3 h3
          · rw [norm_mul, Complex.norm_conj]; linarith [mul_nonneg (norm_nonneg (d t)) (norm_nonneg (d u))]
          · rw [norm_mul, Complex.norm_conj]; linarith
          · rw [norm_mul, Complex.norm_conj]; linarith
          · exfalso
            obtain ⟨ht1, ht2⟩ := mem_product.mp ht
            obtain ⟨hu1, hu2⟩ := mem_product.mp hu
            rcases mul_eq_mul_of_one_or_prime (hs _ ht1) (hs _ ht2) (hs _ hu1) (hs _ hu2) h1 with
              ⟨e1, e2⟩ | ⟨e1, e2⟩
            · exact h2 (Prod.ext e1 e2)
            · exact h3 (Prod.ext e1 e2)
          all_goals simp only [norm_zero, add_zero, zero_add, le_refl]
          all_goals positivity
      _ = ‖d t‖ * ‖d t‖ + ‖d t‖ * ‖d t.swap‖ := by
          rw [sum_add_distrib, sum_ite_eq', sum_ite_eq', if_pos ht, if_pos hswap]
      _ = 2 * ‖d t‖ ^ 2 := by rw [hdswap]; ring
  have htot : ∑ t ∈ s ×ˢ s, 2 * ‖d t‖ ^ 2 = 2 * (∑ n ∈ s, ‖c n‖ ^ 2) ^ 2 := by
    rw [← mul_sum, sq (∑ n ∈ s, ‖c n‖ ^ 2), sum_mul_sum, sum_product]
    congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hd, norm_mul]
    ring
  calc I ≤ ‖(I : ℂ)‖ := hIle
    _ = ‖∑ t ∈ s ×ˢ s, ∑ u ∈ s ×ˢ s,
          if t.1 * t.2 = u.1 * u.2 then d t * conj (d u) else 0‖ := by rw [hI, hP]
    _ ≤ ∑ t ∈ s ×ˢ s, ∑ u ∈ s ×ˢ s,
          ‖if t.1 * t.2 = u.1 * u.2 then d t * conj (d u) else 0‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun t _ => norm_sum_le _ _)
    _ ≤ ∑ t ∈ s ×ˢ s, 2 * ‖d t‖ ^ 2 := sum_le_sum hrow
    _ = 2 * (∑ n ∈ s, ‖c n‖ ^ 2) ^ 2 := htot

/-! ### Paley–Zygmund on a prime block -/

/-- **Paley–Zygmund on a block.** A constant plus a unimodular combination of the twists at a
nonempty set `P` of primes exceeds `#P/2` in square norm with probability at least `1/8`. -/
theorem block_paleyZygmund {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hne : P.Nonempty) (b : ℂ)
    {w : ℕ → ℂ} (hw : ∀ p ∈ P, ‖w p‖ = 1) :
    ENNReal.ofReal (1 / 8) ≤
      gaugeHaar {y | (#P : ℝ) / 2 < ‖b + ∑ p ∈ P, w p * twist y p‖ ^ 2} := by
  classical
  have h1P : (1 : ℕ) ∉ P := fun h => Nat.not_prime_one (hP 1 h)
  set s := insert 1 P with hsdef
  set c : ℕ → ℂ := fun n => if n = 1 then b else w n with hc
  have hs : ∀ n ∈ s, n = 1 ∨ n.Prime := fun n hn => by
    rcases mem_insert.mp hn with h | h
    · exact Or.inl h
    · exact Or.inr (hP n h)
  have hs0 : ∀ n ∈ s, n ≠ 0 := fun n hn => by
    rcases hs n hn with h | h
    · omega
    · exact h.ne_zero
  have hY : ∀ y, twistSum s c y = b + ∑ p ∈ P, w p * twist y p := by
    intro y
    rw [twistSum, hsdef, sum_insert h1P]
    simp only [hc, ↓reduceIte, twist_one, mul_one]
    congr 1
    refine sum_congr rfl fun p hp => ?_
    rw [if_neg (show p ≠ 1 from fun h => h1P (h ▸ hp))]
  have hmass : ∑ n ∈ s, ‖c n‖ ^ 2 = ‖b‖ ^ 2 + #P := by
    rw [hsdef, sum_insert h1P]
    simp only [hc, ↓reduceIte]
    congr 1
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine sum_congr rfl fun p hp => ?_
    rw [if_neg (show p ≠ 1 from fun h => h1P (h ▸ hp)), hw p hp, one_pow]
  have hcont : Continuous fun y => ‖twistSum s c y‖ := (continuous_twistSum s c).norm
  have hint : ∀ k : ℕ, Integrable (fun y => ‖twistSum s c y‖ ^ k) gaugeHaar := fun k =>
    (hcont.pow k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : ∫ y, ‖twistSum s c y‖ ^ 2 ∂gaugeHaar = ‖b‖ ^ 2 + #P := by
    rw [integral_normSq_twistSum hs0, hmass]
  have hpos : 0 < ∫ y, ‖twistSum s c y‖ ^ 2 ∂gaugeHaar := by
    rw [h2]
    have : (0 : ℝ) < #P := by exact_mod_cast hne.card_pos
    positivity
  have hup : ∫ y, (‖twistSum s c y‖ ^ 2) ^ 2 ∂gaugeHaar ≤
      2 * (∫ y, ‖twistSum s c y‖ ^ 2 ∂gaugeHaar) ^ 2 := by
    rw [integral_normSq_twistSum hs0]
    exact integral_normSq_sq_twistSum_le hs c
  have hpz := HTGeometry.measure_sq_gt_half_ge (μ := gaugeHaar) hcont.measurable (hint 2)
    (by simpa only [← pow_mul] using hint 4) (by norm_num : (0 : ℝ) < 2) hup hpos
  rw [h2, show (1 : ℝ) / (4 * 2) = 1 / 8 by norm_num] at hpz
  refine (ENNReal.ofReal_le_of_le_toReal hpz).trans (measure_mono fun y hy => ?_)
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [← hY]
  have : (0 : ℝ) ≤ ‖b‖ ^ 2 := by positivity
  linarith

/-! ### Splitting off the top primes -/

/-- The primes in `(M, 2M]`. -/
def topPrimes (M : ℕ) : Finset ℕ := (Ioc M (2 * M)).filter Nat.Prime

theorem prime_of_mem_topPrimes {M p : ℕ} (hp : p ∈ topPrimes M) : p.Prime :=
  (mem_filter.mp hp).2

/-- A gauge point restricted to the coordinates in `P`. -/
def gaugeRestrict (P : Finset ℕ) (y : GaugeTorus) : GaugeTorus :=
  fun i => if i ∈ P then y i else 0

theorem continuous_gaugeRestrict (P : Finset ℕ) : Continuous (gaugeRestrict P) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i ∈ P
  · simp only [gaugeRestrict, hi, if_true]
    exact continuous_apply i
  · simp only [gaugeRestrict, hi, if_false]
    exact continuous_const

/-- The integers `n ≤ 2M` with a prime factor in `(M, 2M]` are those primes. -/
theorem eq_of_mem_topPrimes_dvd {M p n : ℕ} (hp : p ∈ topPrimes M) (hn0 : n ≠ 0)
    (hn : n ≤ 2 * M) (hpn : p ∣ n) : n = p := by
  obtain ⟨k, rfl⟩ := hpn
  have hpM := (mem_Ioc.mp (mem_filter.mp hp).1).1
  have hk0 : k ≠ 0 := right_ne_zero_of_mul hn0
  have hk1 : k < 2 := by
    by_contra hk
    push Not at hk
    have : p * 2 ≤ p * k := Nat.mul_le_mul_left p hk
    omega
  have : k = 1 := by omega
  rw [this, mul_one]

/-- **The top primes are independent coordinates.** Translating by a point supported on the primes
of `(M, 2M]` moves only their terms of a twisted sum of length `2M`. -/
theorem partialSum_add_gaugeRestrict (a : ℕ → ℂ) (M : ℕ) (x y : GaugeTorus) :
    ∑ n ∈ range (2 * M + 1), a n * twist (x + gaugeRestrict (topPrimes M) y) n =
      ∑ n ∈ range (2 * M + 1) \ topPrimes M, a n * twist x n +
        ∑ p ∈ topPrimes M, a p * twist x p * twist y p := by
  set T := topPrimes M
  have hT : T ⊆ range (2 * M + 1) := fun p hp => by
    have := (mem_Ioc.mp (mem_filter.mp hp).1).2
    exact mem_range.mpr (by omega)
  rw [← sum_sdiff hT]
  congr 1
  · refine sum_congr rfl fun n hn => ?_
    obtain ⟨hnr, hnT⟩ := mem_sdiff.mp hn
    rw [twist_add]
    by_cases hn0 : n = 0
    · simp only [hn0, twist_at_zero, mul_one]
    · have hr : twist (gaugeRestrict T y) n = twist 0 n := by
        refine twist_eq_of_primes hn0 fun q hq hqn => ?_
        have hqT : q ∉ T := fun hqT => hnT
          ((eq_of_mem_topPrimes_dvd hqT hn0 (by have := mem_range.mp hnr; omega) hqn).symm ▸ hqT)
        rw [twist_prime_apply _ hq, twist_prime_apply _ hq]
        simp [gaugeRestrict, hqT]
      rw [hr, twist_trivialPoint, mul_one]
  · refine sum_congr rfl fun p hp => ?_
    have hpp := prime_of_mem_topPrimes hp
    have hr : twist (gaugeRestrict T y) p = twist y p := by
      rw [twist_prime_apply _ hpp, twist_prime_apply _ hpp]
      simp [gaugeRestrict, hp]
    rw [twist_add, hr]
    ring

/-! ### Averaging over translations -/

/-- **Averaging over translations.** If every translate `x + r(·)` meets `E` with probability at
least `a`, then `E` has Haar measure at least `a`. -/
theorem le_measure_of_translates {E : Set GaugeTorus} (hE : MeasurableSet E)
    {r : GaugeTorus → GaugeTorus} (hr : Measurable r) {a : ℝ≥0∞}
    (h : ∀ x, a ≤ gaugeHaar {y | r y + x ∈ E}) : a ≤ gaugeHaar E := by
  set F : GaugeTorus → GaugeTorus → ℝ≥0∞ := fun y x => E.indicator 1 (r y + x) with hF
  have hmeas : Measurable (Function.uncurry F) :=
    (measurable_one.indicator hE).comp ((hr.comp measurable_fst).add measurable_snd)
  -- Each translate of `E` has the measure of `E`.
  have hrow : ∀ y, ∫⁻ x, F y x ∂gaugeHaar = gaugeHaar E := by
    intro y
    rw [hF, lintegral_add_left_eq_self (fun z => E.indicator 1 z) (r y),
      lintegral_indicator_one hE]
  -- Each fibre over `x` has measure at least `a`.
  have hcol : ∀ x, a ≤ ∫⁻ y, F y x ∂gaugeHaar := by
    intro x
    have hset : MeasurableSet {y | r y + x ∈ E} := (hr.add_const x) hE
    have heq : (fun y => F y x) = {y | r y + x ∈ E}.indicator 1 := by
      ext y
      by_cases hy : r y + x ∈ E <;> simp [hF, hy]
    rw [heq, lintegral_indicator_one hset]
    exact h x
  calc a = ∫⁻ _x, a ∂gaugeHaar := by rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ x, ∫⁻ y, F y x ∂gaugeHaar ∂gaugeHaar := lintegral_mono hcol
    _ = ∫⁻ y, ∫⁻ x, F y x ∂gaugeHaar ∂gaugeHaar :=
        lintegral_lintegral_swap (f := fun x y => F y x)
          (by exact (hmeas.comp measurable_swap).aemeasurable)
    _ = ∫⁻ _y, gaugeHaar E ∂gaugeHaar := by simp_rw [hrow]
    _ = gaugeHaar E := by rw [lintegral_const, measure_univ, mul_one]

variable {a : ℕ → ℂ}

/-- **Large values at every scale.** For a source unimodular at the primes, with probability at
least `1/8`, `|S_{2M}|² > #T/2`. -/
theorem measure_partialSum_large_ge (hap : ∀ p, p.Prime → ‖a p‖ = 1) (M : ℕ)
    (hne : (topPrimes M).Nonempty) :
    ENNReal.ofReal (1 / 8) ≤ gaugeHaar {z : GaugeTorus | (#(topPrimes M) : ℝ) / 2 <
      ‖∑ n ∈ range (2 * M + 1), a n * twist z n‖ ^ 2} := by
  have hE : MeasurableSet {z : GaugeTorus | (#(topPrimes M) : ℝ) / 2 <
      ‖∑ n ∈ range (2 * M + 1), a n * twist z n‖ ^ 2} :=
    (isOpen_lt continuous_const
      ((continuous_partialSum a (2 * M)).norm.pow 2)).measurableSet
  refine le_measure_of_translates hE (continuous_gaugeRestrict (topPrimes M)).measurable
    fun x => ?_
  have hpz := block_paleyZygmund (fun p hp => prime_of_mem_topPrimes hp) hne
    (∑ n ∈ range (2 * M + 1) \ topPrimes M, a n * twist x n)
    (w := fun p => a p * twist x p) fun p hp => by
      rw [norm_mul, hap p (prime_of_mem_topPrimes hp), norm_twist, one_mul]
  refine hpz.trans (le_of_eq ?_)
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [add_comm (gaugeRestrict _ y) x, partialSum_add_gaugeRestrict]

/-! ### Many top primes -/

theorem card_topPrimes_eq (M : ℕ) :
    (#(topPrimes M) : ℝ) = (Nat.primeCounting (2 * M) : ℝ) - Nat.primeCounting M := by
  have hcount : ∀ n, Nat.primeCounting n = #((range (n + 1)).filter Nat.Prime) := by
    intro n
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hU : (range (2 * M + 1)).filter Nat.Prime =
      (range (M + 1)).filter Nat.Prime ∪ topPrimes M := by
    rw [topPrimes, ← filter_union]
    congr 1
    ext n
    simp only [mem_range, mem_union, mem_Ioc]
    omega
  have hD : Disjoint ((range (M + 1)).filter Nat.Prime) (topPrimes M) :=
    disjoint_filter_filter (disjoint_left.mpr fun n h1 h2 => by
      simp only [mem_range, mem_Ioc] at h1 h2
      omega)
  rw [hcount, hcount, hU, card_union_of_disjoint hD]
  push_cast
  ring

/-- **Many top primes.** For `0 ≤ a < 1` the number of primes in `(M, 2M]` eventually exceeds any
multiple of `(2M + 1)^a`. -/
theorem exists_card_topPrimes_gt {K a : ℝ} (hK : 0 ≤ K) (ha0 : 0 ≤ a) (ha : a < 1) :
    ∃ M : ℕ, K * (2 * (M : ℝ) + 1) ^ a < #(topPrimes M) := by
  obtain ⟨c, hc, hπ⟩ := pi_alt
  set b : ℝ := (1 - a) / 2 with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hc.bound (show (0 : ℝ) < 1 / 10 by norm_num))
  have hgrow : Tendsto (fun M : ℕ => (M : ℝ) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb0).comp tendsto_natCast_atTop_atTop
  obtain ⟨M, hMX, hM10, hMb⟩ := ((tendsto_natCast_atTop_atTop.eventually_ge_atTop X).and
    ((eventually_ge_atTop (2 ^ 10 : ℕ)).and (hgrow.eventually_gt_atTop (6 * K / b)))).exists
  refine ⟨M, ?_⟩
  have hM : (2 ^ 10 : ℝ) ≤ M := by exact_mod_cast hM10
  have hM0 : (0 : ℝ) < M := by linarith
  set L := Real.log M with hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL10 : 10 * Real.log 2 ≤ L := by
    have := Real.log_le_log (by norm_num) hM
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hL0 : 0 < L := by linarith
  have hlog2M : Real.log (2 * M) = Real.log 2 + L := Real.log_mul (by norm_num) hM0.ne'
  have hcM : |c M| ≤ 1 / 10 := by
    have := hX M hMX
    rwa [norm_one, mul_one, Real.norm_eq_abs] at this
  have hc2M : |c (2 * M)| ≤ 1 / 10 := by
    have := hX (2 * M) (by linarith)
    rwa [norm_one, mul_one, Real.norm_eq_abs] at this
  have hπM : (Nat.primeCounting M : ℝ) * L = (1 + c M) * M := by
    have := hπ M
    rw [Nat.floor_natCast] at this
    rw [this, ← hL, div_mul_cancel₀ _ hL0.ne']
  have hπ2M : (Nat.primeCounting (2 * M) : ℝ) * Real.log (2 * M) = (1 + c (2 * M)) * (2 * M) := by
    have := hπ ((2 * M : ℕ) : ℝ)
    rw [Nat.floor_natCast] at this
    have hne : Real.log (2 * M) ≠ 0 := by rw [hlog2M]; linarith
    rw [this]
    push_cast
    exact div_mul_cancel₀ _ hne
  -- `#T log M ≥ M/2`.
  have hcount : (M : ℝ) / 2 ≤ #(topPrimes M) * L := by
    rw [card_topPrimes_eq]
    have hπ2 : (0 : ℝ) ≤ Nat.primeCounting (2 * M) := Nat.cast_nonneg _
    have hle : Real.log (2 * M) ≤ 11 / 10 * L := by rw [hlog2M]; linarith
    have h1 : (Nat.primeCounting (2 * M) : ℝ) * Real.log (2 * M) ≤
        Nat.primeCounting (2 * M) * (11 / 10 * L) := mul_le_mul_of_nonneg_left hle hπ2
    have h2 : -(1 / 10) * (2 * (M : ℝ)) ≤ c (2 * M) * (2 * M) :=
      mul_le_mul_of_nonneg_right (by linarith [neg_abs_le (c (2 * M))]) (by positivity)
    have h3 : c M * M ≤ 1 / 10 * M :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self (c M)]) hM0.le
    nlinarith
  -- `log M ≤ M^b / b` and `M = M^a M^b M^b`.
  have hlogb : L ≤ (M : ℝ) ^ b / b := Real.log_le_rpow_div hM0.le hb0
  set A := (M : ℝ) ^ a with hA
  set B := (M : ℝ) ^ b with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos hM0 a
  have hBpos : 0 < B := Real.rpow_pos_of_pos hM0 b
  have hABB : A * B * B = M := by
    rw [hA, hB, ← Real.rpow_add hM0, ← Real.rpow_add hM0, hb]
    rw [show a + (1 - a) / 2 + (1 - a) / 2 = 1 by ring, Real.rpow_one]
  have hT0 : (0 : ℝ) ≤ #(topPrimes M) := Nat.cast_nonneg _
  have hTB : b * (M : ℝ) / 2 ≤ #(topPrimes M) * B := by
    have : b * L ≤ B := by rw [le_div_iff₀ hb0] at hlogb; linarith
    nlinarith
  -- `(2M + 1)^a ≤ 3 M^a`.
  have h3 : (2 * (M : ℝ) + 1) ^ a ≤ 3 * A := by
    have hle : 2 * (M : ℝ) + 1 ≤ 3 * M := by linarith
    calc (2 * (M : ℝ) + 1) ^ a ≤ (3 * M) ^ a := Real.rpow_le_rpow (by positivity) hle ha0
      _ = 3 ^ a * A := Real.mul_rpow (by norm_num) hM0.le
      _ ≤ 3 * A := by
          refine mul_le_mul_of_nonneg_right ?_ hApos.le
          calc (3 : ℝ) ^ a ≤ 3 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) ha.le
            _ = 3 := Real.rpow_one 3
  have hMb' : 6 * K < b * B := by rw [div_lt_iff₀ hb0] at hMb; linarith
  have hTlow : b / 2 * A * B ≤ #(topPrimes M) := by
    have : b / 2 * A * B * B ≤ #(topPrimes M) * B := by
      calc b / 2 * A * B * B = b * (A * B * B) / 2 := by ring
        _ = b * M / 2 := by rw [hABB]
        _ ≤ _ := hTB
    exact le_of_mul_le_mul_right this hBpos
  calc K * (2 * (M : ℝ) + 1) ^ a ≤ K * (3 * A) := mul_le_mul_of_nonneg_left h3 hK
    _ < b / 2 * A * B := by nlinarith
    _ ≤ _ := hTlow

/-! ### The typical exponent -/

/-- **No level below one half is typical** for a bounded source unimodular at the primes. -/
theorem half_le_of_mem_typicalLevels (ha : ∀ n, ‖a n‖ ≤ 1) (hap : ∀ p, p.Prime → ‖a p‖ = 1)
    {θ : ℝ} (hθ : θ ∈ typicalLevels a) : 1 / 2 ≤ θ := by
  by_contra hlt
  push Not at hlt
  have hθ0 := typicalLevels_nonneg ha hθ
  set θ' := (θ + 1 / 2) / 2 with hθ'
  have hθθ' : θ < θ' := by rw [hθ']; linarith
  -- The sublevel set lies in the union of the bounded sets `B_C`.
  set B : ℕ → Set GaugeTorus := fun C => ⋂ N : ℕ, {x : GaugeTorus |
    ‖∑ n ∈ range (N + 1), a n * twist x n‖ ≤ (C : ℝ) * ((N : ℝ) + 1) ^ θ'} with hBdef
  have hsub : {x : GaugeTorus | gaugeExponent a x ≤ θ} ⊆ ⋃ C, B C := by
    intro x hx
    have hb := gaugePowerBound_of_gaugeExponent_lt ha (lt_of_le_of_lt hx hθθ')
    have : x ∈ {x : GaugeTorus | GaugePowerBound a x θ'} := hb
    rwa [setOf_gaugePowerBound_eq] at this
  have hmono : Monotone B := by
    intro C C' hCC' x hx
    simp only [hBdef, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
    intro N
    refine (hx N).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hCC') (by positivity))
  -- Each `B_C` misses an event of measure at least `1/8`.
  have hBC : ∀ C : ℕ, gaugeHaar (B C) ≤ 1 - ENNReal.ofReal (1 / 8) := by
    intro C
    obtain ⟨M, hM⟩ := exists_card_topPrimes_gt (K := 2 * (C : ℝ) ^ 2) (by positivity)
      (a := 2 * θ') (by rw [hθ']; linarith) (by rw [hθ']; linarith)
    have hne : (topPrimes M).Nonempty := by
      rw [← card_pos]
      have : (0 : ℝ) < #(topPrimes M) :=
        lt_of_le_of_lt (by positivity) hM
      exact_mod_cast this
    set E := {z : GaugeTorus | (#(topPrimes M) : ℝ) / 2 <
      ‖∑ n ∈ range (2 * M + 1), a n * twist z n‖ ^ 2} with hE
    have hEm : MeasurableSet E :=
      (isOpen_lt continuous_const
        ((continuous_partialSum a (2 * M)).norm.pow 2)).measurableSet
    have hsubE : B C ⊆ Eᶜ := by
      intro x hx hxE
      simp only [hBdef, Set.mem_iInter, Set.mem_setOf_eq] at hx
      have hxN := hx (2 * M)
      simp only [hE, Set.mem_setOf_eq] at hxE
      have hX : (0 : ℝ) < ((2 * M : ℕ) : ℝ) + 1 := by positivity
      have hpow : (((2 * M : ℕ) : ℝ) + 1) ^ (2 * θ') = ((((2 * M : ℕ) : ℝ) + 1) ^ θ') ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
        congr 1
        push_cast
        ring
      have hsq : ‖∑ n ∈ range (2 * M + 1), a n * twist x n‖ ^ 2 ≤
          (C : ℝ) ^ 2 * ((((2 * M : ℕ) : ℝ) + 1) ^ θ') ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hxN 2
      rw [← hpow] at hsq
      push_cast at hM hsq
      linarith
    calc gaugeHaar (B C) ≤ gaugeHaar Eᶜ := measure_mono hsubE
      _ = 1 - gaugeHaar E := prob_compl_eq_one_sub hEm
      _ ≤ 1 - ENNReal.ofReal (1 / 8) :=
          tsub_le_tsub_left (measure_partialSum_large_ge hap M hne) 1
  have hU : gaugeHaar (⋃ C, B C) ≤ 1 - ENNReal.ofReal (1 / 8) := by
    rw [hmono.measure_iUnion]
    exact iSup_le hBC
  have hlt : 1 - ENNReal.ofReal (1 / 8) < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (by simp)
  have h1 : gaugeHaar {x : GaugeTorus | gaugeExponent a x ≤ θ} = 1 := hθ
  have := (measure_mono hsub).trans hU
  rw [h1] at this
  exact absurd (this.trans_lt hlt) (lt_irrefl 1)

/-- **The typical exponent is one half** for a bounded source unimodular at the primes. -/
theorem typicalExponent_eq_half (ha : ∀ n, ‖a n‖ ≤ 1) (hap : ∀ p, p.Prime → ‖a p‖ = 1) :
    typicalExponent a = 1 / 2 :=
  le_antisymm (typicalExponent_le_half ha)
    (le_csInf ⟨_, half_mem_typicalLevels ha⟩ fun _ hθ => half_le_of_mem_typicalLevels ha hap hθ)

/-- **Haar-almost every gauge point has exponent exactly one half** for a bounded tail-invariant
source unimodular at the primes. -/
theorem ae_gaugeExponent_eq_half (ha : ∀ n, ‖a n‖ ≤ 1) (hap : ∀ p, p.Prime → ‖a p‖ = 1)
    (ht : IsTailInvariant a) : ∀ᵐ x ∂gaugeHaar, gaugeExponent a x = 1 / 2 := by
  filter_upwards [ae_gaugeExponent_eq_typical ha ht] with x hx
  rw [hx, typicalExponent_eq_half ha hap]

theorem norm_moebiusSource_prime (p : ℕ) (hp : p.Prime) : ‖moebiusSource p‖ = 1 := by
  simp [moebiusSource, ArithmeticFunction.moebius_apply_prime hp]

theorem typicalExponent_moebius_eq_half : typicalExponent moebiusSource = 1 / 2 :=
  typicalExponent_eq_half norm_moebiusSource_le norm_moebiusSource_prime

/-- **Haar-almost every gauge point has Möbius exponent exactly one half.** -/
theorem ae_gaugeExponent_moebius_eq_half :
    ∀ᵐ x ∂gaugeHaar, gaugeExponent moebiusSource x = 1 / 2 :=
  ae_gaugeExponent_eq_half norm_moebiusSource_le norm_moebiusSource_prime isTailInvariant_moebius

/-- **RH is the typicality of the trivial point.** -/
theorem riemannHypothesis_iff_trivialPoint_typical :
    RiemannHypothesis ↔ gaugeExponent moebiusSource 0 ≤ typicalExponent moebiusSource := by
  rw [typicalExponent_moebius_eq_half]
  exact riemannHypothesis_iff_gaugeExponent_moebius_trivial_le_half

end GaloisForLFunctions.ArithmeticGaugeTheory
