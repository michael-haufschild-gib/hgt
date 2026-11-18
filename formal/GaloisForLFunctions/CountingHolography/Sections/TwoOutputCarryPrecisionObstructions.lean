import GaloisForLFunctions.CountingHolography.Sections.SubquadraticFibresOfMidpointSectionMaps
import GaloisForLFunctions.CountingHolography.Sections.CommonDenominatorsOfSectionInjections

/-!
# Two-output carry and precision obstructions for midpoint section maps

Exporting `p`-adic or modular rounding remainders from the narrow midpoint
output coordinate to the wide output coordinate obeys four unconditional
quantitative obstructions along `(2mb, 3mb, 4mb)` for any positive background
`b` of degree `d = Q(b) > 0`:

1. **Two-place precision versus two-output collisions:** For any map
   `S(3mb)² → S(4mb) × S(2mb)` with narrow-coordinate precision losses `(i, j)`
   at coprime bases `(p, q)`, either the largest fibre across **both** outputs
   has `log F > δ₁ m²` (`δ₁ < 2d`) or `max(i log p, j log q) > δ₂ m²`
   (`δ₂ < 5d`). Specializing to injections sharpens the two-place precision cost
   from `d` to `5d`. Moreover, every map with `log F ≤ δ₁ m²` (`δ₁ < 2d`) still
   requires double-logarithmic clearing denominator `9d m²`.
2. **Polynomial rounding with arbitrary first-output carry:** If an integer
   bivariate polynomial `P(x₁, x₂)` equals `D · f₂(x) + r(x)` with remainder
   `0 ≤ r(x) < D` and completely unrestricted first output `f₁(x)` (including
   any carry of `r(x)`), then `P` preserves congruences modulo the coprime pair
   `(Ds, Ds + 1)` with values in `[0, Ds)`, forcing either `log F > δ₁ m²`
   (`δ₁ < 2d`) or `log D > δ₂ m²` (`δ₂ < 5d`).
3. **Carry infection of the wide output:** Any Euclidean carry encoding
   `f₁(x₁, x₂) = (x₁ mod M) + M x₂` (`M ≥ 2`) into `S(4mb)` forces two-place
   precision loss `max(i₁ log p, j₁ log q) > δ m²` (`δ < 2d`) in the first
   output itself.
4. **Universal joint inverse loss at a single place:** Even at one base `p > 1`,
   every map `S(3mb)² → S(4mb) × S(2mb)` loses `k log p > δ m²` (`δ < (5/2) d`)
   digits when recovering the input modulo `p^r` jointly from both outputs
   modulo `p^(r + k)`.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology ArithmeticScatteringHolography

/-- Arbitrary two-output maps between section intervals on `(2b, 3b, 4b)`. -/
abbrev rayProductMap {N : ℕ} (b : Fin N → ℤ) (m : ℕ) :=
  (↥(divisorSections (m • (3 • b))) × ↥(divisorSections (m • (3 • b)))) →
    (↥(divisorSections (m • (4 • b))) × ↥(divisorSections (m • (2 • b))))

/-- Express an arbitrary two-output section map in consecutive interval coordinates. -/
def ordinalMap {N : ℕ} (b : Fin N → ℤ) (m : ℕ) (f : rayProductMap b m) :
    Fin (rayCard b 3 m) × Fin (rayCard b 3 m) → Fin (rayCard b 4 m) × Fin (rayCard b 2 m) :=
  fun x => ((rayOrdinal b 4 m).prodCongr (rayOrdinal b 2 m))
    (f (((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm x))

theorem ordinalMap_embedding {N : ℕ} (b : Fin N → ℤ) (m : ℕ) (e : rayProductEmbedding b m) :
    ordinalMap b m e = ordinalEmbedding b m e :=
  rfl

private theorem maxFibre_comp_equiv_le {α α' β β' : Type*} [Fintype α] [Fintype α']
    [Fintype β] [Fintype β'] (e₁ : α' ≃ α) (e₂ : β ≃ β') (f : α → β) :
    maxFibre (fun x => e₂ (f (e₁ x))) ≤ maxFibre f := by
  rw [maxFibre_le_iff]
  intro y' S' hS'
  rw [← Finset.card_map e₁.toEmbedding]
  refine card_le_maxFibre_of_forall_eq f (e₂.symm y') fun x hx => ?_
  obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
  exact e₂.injective (by simpa only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using hS' x' hx')

theorem maxFibre_comp_equiv {α α' β β' : Type*} [Fintype α] [Fintype α'] [Fintype β] [Fintype β']
    (e₁ : α' ≃ α) (e₂ : β ≃ β') (f : α → β) :
    maxFibre (fun x => e₂ (f (e₁ x))) = maxFibre f := by
  refine le_antisymm (maxFibre_comp_equiv_le e₁ e₂ f) ?_
  have hf : f = fun x => e₂.symm ((fun x' => e₂ (f (e₁ x'))) (e₁.symm x)) := by
    funext x; simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  nth_rw 1 [hf]
  exact maxFibre_comp_equiv_le e₁.symm e₂.symm (fun x' => e₂ (f (e₁ x')))

theorem maxFibre_ordinalMap {N : ℕ} (b : Fin N → ℤ) (m : ℕ) (f : rayProductMap b m) :
    maxFibre (ordinalMap b m f) = maxFibre f :=
  maxFibre_comp_equiv ((rayOrdinal b 3 m).prodCongr (rayOrdinal b 3 m)).symm
    ((rayOrdinal b 4 m).prodCongr (rayOrdinal b 2 m)) f

/-- If the second coordinate of `f : Fin n × Fin n → Fin L × Fin s` is constant,
all `n²` inputs collide into a single slice of size `L`, so `n² ≤ maxFibre f * L`. -/
theorem card_sq_le_maxFibre_mul_of_second_const {n L s : ℕ}
    (f : Fin n × Fin n → Fin L × Fin s) (hconst : ∀ x y, (f x).2 = (f y).2) :
    n * n ≤ maxFibre f * L := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  let x₀ : Fin n × Fin n := (⟨0, hn⟩, ⟨0, hn⟩)
  let g : Fin n × Fin n → Fin L := fun x => (f x).1
  have hg : maxFibre g ≤ maxFibre f := by
    rw [maxFibre_le_iff]
    intro y₁ S hS
    exact card_le_maxFibre_of_forall_eq f (y₁, (f x₀).2) fun x hx => Prod.ext (hS x hx) (hconst x x₀)
  have hc := card_le_maxFibre_mul_card g
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  exact hc.trans (Nat.mul_le_mul_right L hg)

/-! ### 1. Two-place precision versus two-output collisions -/

/-- Two coprime periods in the narrow coordinate either force `n² ≤ maxFibre f * L`
across both outputs or have sum exceeding the input side length `n`. -/
theorem fibre_or_sum_of_periods {n L s P Q u v : ℕ} (f : Fin n × Fin n → Fin L × Fin s)
    (hc : P.Coprime Q) (hp : 0 < P) (hu : s ≤ u) (hv : s ≤ v)
    (hP : preservesSecondMod f P u) (hQ : preservesSecondMod f Q v) :
    n * n ≤ maxFibre f * L ∨ n < P + Q := by
  by_cases hn : P + Q ≤ n
  · left
    have eqP (x y : Fin n × Fin n) (hx : x.1.val ≡ y.1.val [MOD P]) (hy : x.2.val ≡ y.2.val [MOD P]) :
        (f x).2 = (f y).2 :=
      Fin.ext ((hP x y hx hy).eq_of_lt_of_lt ((f x).2.isLt.trans_le hu) ((f y).2.isLt.trans_le hu))
    have eqQ (x y : Fin n × Fin n) (hx : x.1.val ≡ y.1.val [MOD Q]) (hy : x.2.val ≡ y.2.val [MOD Q]) :
        (f x).2 = (f y).2 :=
      Fin.ext ((hQ x y hx hy).eq_of_lt_of_lt ((f x).2.isLt.trans_le hv) ((f y).2.isLt.trans_le hv))
    refine card_sq_le_maxFibre_mul_of_second_const f fun x y => ?_
    have row := constant_of_two_periods (fun i => (f (i, x.2)).2) hp hc hn
      (fun i j h => eqP _ _ h .rfl) (fun i j h => eqQ _ _ h .rfl)
    have col := constant_of_two_periods (fun j => (f (y.1, j)).2) hp hc hn
      (fun i j h => eqP _ _ .rfl h) (fun i j h => eqQ _ _ .rfl h)
    exact (row x.1 y.1).trans (col x.2 y.2)
  · exact Or.inr (lt_of_not_ge hn)

/-- For any two-output map (with unrestricted wide output `f₁`), narrow-coordinate
precision losses `(i, j)` at coprime bases `(p, q)` force either `n² ≤ maxFibre f * L`
or `n < p * s * p^i + q * s * q^j`. -/
theorem two_place_fibre_or_precision_loss {n L s p q i j : ℕ}
    (f : Fin n × Fin n → Fin L × Fin s)
    (hp : 1 < p) (hq : 1 < q) (hc : p.Coprime q) (hs : 0 < s)
    (hi : secondPrecisionLoss f p i) (hj : secondPrecisionLoss f q j) :
    n * n ≤ maxFibre f * L ∨ n < p * s * p ^ i + q * s * q ^ j := by
  let r := Nat.log p s + 1
  let t := Nat.log q s + 1
  have hsmall (b : ℕ) : b ^ (Nat.log b s + 1) ≤ b * s := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b hs.ne')
  rcases fibre_or_sum_of_periods f ((hc.pow_left (r + i)).pow_right (t + j))
    (pow_pos (by omega) _) (Nat.lt_pow_succ_log_self hp s).le (Nat.lt_pow_succ_log_self hq s).le
    (hi r) (hj t) with hfib | hsum
  · exact Or.inl hfib
  · right
    refine hsum.trans_le ?_
    rw [pow_add p r i, pow_add q t j]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (hsmall p)) (Nat.mul_le_mul_right _ (hsmall q))

private theorem log_nat_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Real.log ((a * b : ℕ) : ℝ) = Real.log a + Real.log b := by
  rw [Nat.cast_mul, Real.log_mul (Nat.cast_pos.mpr ha).ne' (Nat.cast_pos.mpr hb).ne']

private theorem logRate_const_zero (c : ℕ) :
    Tendsto (fun m : ℕ => Real.log (c : ℝ) / (m : ℝ)^2) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)

/-- Along `(2mb, 3mb, 4mb)` on a positive ray `b`, every two-output map with
narrow-coordinate precision losses `(i, j)` at coprime bases `(p, q)` either has
quadratic logarithmic fibre collisions `> δ₁ m²` (`δ₁ < 2 Q(b)`) across both
outputs or loses `> δ₂ m²` (`δ₂ < 5 Q(b)`) in `max(i log p, j log q)`. -/
theorem eventually_twoPlace_fibre_or_precision_cost {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (hc : p.Coprime q)
    {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ < 2 * integerProbe N b) (hδ₂ : δ₂ < 5 * integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (i j : ℕ),
      secondPrecisionLoss (ordinalMap b m f) p i →
      secondPrecisionLoss (ordinalMap b m f) q j →
      δ₁ * (m : ℝ)^2 < Real.log (maxFibre f) ∨
        δ₂ * (m : ℝ)^2 < max ((i : ℝ) * Real.log p) ((j : ℝ) * Real.log q) := by
  have hfib_lim := ((rayCard_tateLimit hb 3).const_mul 2).sub (rayCard_tateLimit hb 4)
  have hfib_ev := hfib_lim.eventually_const_lt
    (show δ₁ < 2 * ((3 : ℝ)^2 * integerProbe N b) - (4 : ℝ)^2 * integerProbe N b by linarith)
  have hprec_lim := ((rayCard_tateLimit hb 3).sub (rayCard_tateLimit hb 2)).sub
    (logRate_const_zero (p + q))
  have hprec_ev := hprec_lim.eventually_const_lt
    (show δ₂ < (3 : ℝ)^2 * integerProbe N b - (2 : ℝ)^2 * integerProbe N b - 0 by linarith)
  filter_upwards [hfib_ev, hprec_ev, eventually_ge_atTop 1] with m hm₁ hm₂ hm1
  intro f i j hi hj
  let n := rayCard b 3 m
  let L := rayCard b 4 m
  let s := rayCard b 2 m
  have hn : 0 < n := rayCard_pos b 3 m
  have hL : 0 < L := rayCard_pos b 4 m
  have hs : 0 < s := rayCard_pos b 2 m
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  rcases two_place_fibre_or_precision_loss (ordinalMap b m f) hp hq hc hs hi hj with hcard | hlt
  · left
    rw [maxFibre_ordinalMap] at hcard
    haveI := Fin.pos_iff_nonempty.mp hn
    have hfpos : 0 < maxFibre f := by
      rw [← maxFibre_ordinalMap]
      exact maxFibre_pos _
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hn hn)) (Nat.cast_le.mpr hcard)
    rw [log_nat_mul hn hn, log_nat_mul hfpos hL] at hlog
    have hd : δ₁ < (2 * Real.log n - Real.log L) / (m : ℝ)^2 := by
      simpa only [sub_div, mul_div_assoc] using hm₁
    have hm₁' := (lt_div_iff₀ hm2).mp hd
    linarith only [hm₁', hlog]
  · right
    have hpq : 0 < p + q := by omega
    have hd : δ₂ < (Real.log n - Real.log s - Real.log (p + q : ℕ)) / (m : ℝ)^2 := by
      simpa only [sub_div] using hm₂
    have hm₂' := (lt_div_iff₀ hm2).mp hd
    rcases le_total (p ^ i) (q ^ j) with hij | hji
    · have hub : n < (p + q) * s * q ^ j := hlt.trans_le (by
        calc p * s * p ^ i + q * s * q ^ j
            ≤ p * s * q ^ j + q * s * q ^ j :=
              Nat.add_le_add_right (Nat.mul_le_mul_left (p * s) hij) _
          _ = (p + q) * s * q ^ j := by ring)
      have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn) (Nat.cast_lt.mpr hub)
      rw [log_nat_mul (Nat.mul_pos hpq hs) (pow_pos (by omega) j),
        log_nat_mul hpq hs, Nat.cast_pow, Real.log_pow] at hlog
      linarith only [hm₂', hlog, le_max_right ((i : ℝ) * Real.log p) ((j : ℝ) * Real.log q)]
    · have hub : n < (p + q) * s * p ^ i := hlt.trans_le (by
        calc p * s * p ^ i + q * s * q ^ j
            ≤ p * s * p ^ i + q * s * p ^ i :=
              Nat.add_le_add_left (Nat.mul_le_mul_left (q * s) hji) _
          _ = (p + q) * s * p ^ i := by ring)
      have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn) (Nat.cast_lt.mpr hub)
      rw [log_nat_mul (Nat.mul_pos hpq hs) (pow_pos (by omega) i),
        log_nat_mul hpq hs, Nat.cast_pow, Real.log_pow] at hlog
      linarith only [hm₂', hlog, le_max_left ((i : ℝ) * Real.log p) ((j : ℝ) * Real.log q)]

/-- Sharpened two-place precision cost for midpoint section injections: at
coprime bases `(p, q)`, `max(i log p, j log q) > δ m²` eventually for all `δ < 5 Q(b)`. -/
theorem eventually_sharpened_twoPlace_precision_cost {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (hc : p.Coprime q)
    {δ : ℝ} (hδ : δ < 5 * integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, ∀ (e : rayProductEmbedding b m) (i j : ℕ),
      secondPrecisionLoss (ordinalEmbedding b m e) p i →
      secondPrecisionLoss (ordinalEmbedding b m e) q j →
      δ * (m : ℝ)^2 < max ((i : ℝ) * Real.log p) ((j : ℝ) * Real.log q) := by
  filter_upwards [eventually_twoPlace_fibre_or_precision_cost hb hp hq hc
    (show integerProbe N b < 2 * integerProbe N b by linarith) hδ] with m hm
  intro e i j hi hj
  rcases hm e i j hi hj with hfib | hprec
  · exfalso
    have hle : maxFibre (e : rayProductMap b m) ≤ 1 :=
      (maxFibre_le_one_iff_injective _).mpr e.injective
    have hle' : (maxFibre (e : rayProductMap b m) : ℝ) ≤ 1 := by exact_mod_cast hle
    haveI := Fin.pos_iff_nonempty.mp (rayCard_pos b 3 m)
    have hpos : 0 < (maxFibre (e : rayProductMap b m) : ℝ) := by
      rw [← maxFibre_ordinalMap]; exact Nat.cast_pos.mpr (maxFibre_pos _)
    have hlog : Real.log (maxFibre (e : rayProductMap b m)) ≤ 0 := by
      simpa only [Real.log_one] using Real.log_le_log hpos hle'
    linarith only [hfib, hlog, mul_nonneg hb.le (sq_nonneg (m : ℝ))]
  · exact hprec

private theorem primorial_dvd_cleared_of_fibre {n L s D X : ℕ}
    (f : Fin n × Fin n → Fin L × Fin s) (hfib : maxFibre f * L < n * n)
    (hD : clearsSecond f D) (hd : 0 < D) (hX : 0 < X) (hs : s ≤ X) (hn : 4 * X ≤ n) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2 * X ∧ primorial (2 * X) ∣ primorial X * D * q := by
  have hmiss : ∀ {p q : ℕ}, p.Prime → q.Prime → s ≤ p → s ≤ q → p + q ≤ n →
      ¬ p ∣ D → ¬ q ∣ D → p = q := by
    intro p q hp hq hsp hsq hpq hDp hDq
    by_contra hne
    have hpres (t : ℕ) (ht : t.Prime) (hdt : ¬ t ∣ D) : preservesSecondMod f t t :=
      fun x y hx hy => Nat.ModEq.cancel_left_of_coprime (ht.coprime_iff_not_dvd.mpr hdt) (hD t x y hx hy)
    rcases fibre_or_sum_of_periods f ((Nat.coprime_primes hp hq).mpr hne) hp.pos hsp hsq
      (hpres p hp hDp) (hpres q hq hDq) with hc | hlt
    · exact hfib.not_ge hc
    · exact hpq.not_gt hlt
  have hp (p : ℕ) (hpp : p.Prime) (hpx : p ≤ X) : p ∣ primorial X := by
    rw [primorial_eq_prod_primesLE]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨hpx, hpp⟩)
  have assemble (q : ℕ) (hq : 0 < q)
      (hall : ∀ p, p.Prime → p ≤ 2 * X → p ∣ primorial X * D * q) :
      primorial (2 * X) ∣ primorial X * D * q := by
    rw [primorial_eq_prod_primesLE, ← primeFactors_primorial (2 * X)]
    apply (Nat.prod_primeFactors_dvd_iff (Nat.mul_pos (Nat.mul_pos (primorial_pos X) hd) hq).ne').mpr
    intro p h
    rw [primeFactors_primorial, Nat.mem_primesLE] at h
    exact h.2.mem_primeFactors (hall _ h.2 h.1) (Nat.mul_pos (Nat.mul_pos (primorial_pos X) hd) hq).ne'
  by_cases h : ∃ p : ℕ, p.Prime ∧ X < p ∧ p ≤ 2 * X ∧ ¬ p ∣ D
  · obtain ⟨q, hq, hxq, hqx, hqD⟩ := h
    refine ⟨q, hq.pos, hqx, assemble q hq.pos fun p hpp hpx => ?_⟩
    by_cases hx : p ≤ X
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hp _ hpp hx) _) _
    by_cases hpd : p ∣ D
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpd _) _
    rw [hmiss hpp hq (by omega) (by omega) (by omega) hpd hqD]
    exact dvd_mul_left _ _
  · refine ⟨1, by decide, by omega, assemble 1 (by decide) fun p hpp hpx => ?_⟩
    rw [mul_one]
    by_cases hx : p ≤ X
    · exact dvd_mul_of_dvd_left (hp _ hpp hx) _
    exact dvd_mul_of_dvd_right (Classical.byContradiction fun hd' => h ⟨p, hpp, by omega, hpx, hd'⟩) _

/-- Any map on `S(3mb)² → S(4mb) × S(2mb)` whose largest fibre across both outputs
has `log F ≤ δ m²` (`δ < 2 Q(b)`) still requires every clearing scalar `D > 0`
(in particular `leastClearing`) to satisfy `log(log D) / m² > 9 Q(b) - ε`. -/
theorem eventually_loglog_clearing_of_subquadratic_fibre {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {δ ε : ℝ} (hδ : δ < 2 * integerProbe N b) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (D : ℕ),
      Real.log (maxFibre f) ≤ δ * (m : ℝ)^2 → 0 < D → clearsSecond (ordinalMap b m f) D →
      9 * integerProbe N b - ε < Real.log (Real.log D) / (m : ℝ)^2 := by
  obtain ⟨X₀, hθ⟩ := _root_.RHTower.chebyshevTheta_remainder_eventually_le (by norm_num : (0 : ℝ) < 1 / 8)
  let n := rayCard b 3
  have hr : Tendsto (fun m : ℕ => Real.log (n m) / (m : ℝ)^2) atTop (𝓝 (9 * integerProbe N b)) := by
    convert rayCard_tateLimit hb 3 using 1; norm_num
  have hnat : Tendsto n atTop atTop := by
    apply tendsto_atTop.mpr
    intro U
    filter_upwards [(logRate_const_zero (U + 1)).eventually_lt_const
      (show 0 < 9 * integerProbe N b / 2 by positivity),
      hr.eventually_const_lt (show 9 * integerProbe N b / 2 < 9 * integerProbe N b by linarith),
      eventually_ge_atTop 1] with m hc hm hm1
    have h := hc.trans hm
    rw [div_lt_div_iff_of_pos_right (by positivity : 0 < (m : ℝ)^2),
      Real.log_lt_log_iff (by positivity) (Nat.cast_pos.mpr (rayCard_pos b 3 m))] at h
    have ht : U + 1 < n m := by exact_mod_cast h
    omega
  have hfib_lim := ((rayCard_tateLimit hb 3).const_mul 2).sub (rayCard_tateLimit hb 4)
  have hfib_ev := hfib_lim.eventually_const_lt
    (show δ < 2 * ((3 : ℝ)^2 * integerProbe N b) - (4 : ℝ)^2 * integerProbe N b by linarith)
  have hl := (hr.sub ((tendsto_const_nhds (x := Real.log 20)).div_atTop
    ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop))).eventually_const_lt
    (show 9 * integerProbe N b - ε < 9 * integerProbe N b - 0 by linarith)
  filter_upwards [hnat.eventually (eventually_ge_atTop (4 * max 128 X₀)),
    eventually_narrow_mul_lt_middle hb 4 (by decide), hfib_ev, hl, eventually_ge_atTop 1]
    with m hn_big hs hfib_m hl_m hm1
  intro f D hf hD hclear
  have hn_pos : 0 < n m := rayCard_pos b 3 m
  have hL_pos : 0 < rayCard b 4 m := rayCard_pos b 4 m
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  have hcard_lt : maxFibre (ordinalMap b m f) * rayCard b 4 m < n m * n m := by
    rw [maxFibre_ordinalMap]
    haveI := Fin.pos_iff_nonempty.mp hn_pos
    have hfpos : 0 < maxFibre f := by rw [← maxFibre_ordinalMap]; exact maxFibre_pos _
    have hd : δ < (2 * Real.log (n m) - Real.log (rayCard b 4 m)) / (m : ℝ)^2 := by
      simpa only [sub_div, mul_div_assoc] using hfib_m
    have hlt_log : Real.log ((maxFibre f * rayCard b 4 m : ℕ) : ℝ) <
        Real.log ((n m * n m : ℕ) : ℝ) := by
      rw [log_nat_mul hfpos hL_pos, log_nat_mul hn_pos hn_pos]
      linarith only [hf, (lt_div_iff₀ hm2).mp hd]
    exact_mod_cast (Real.log_lt_log_iff
      (Nat.cast_pos.mpr (Nat.mul_pos hfpos hL_pos))
      (Nat.cast_pos.mpr (Nat.mul_pos hn_pos hn_pos))).mp hlt_log
  let X := n m / 4
  have hx : max 128 X₀ ≤ X := by dsimp only [X]; omega
  have hx₀ : X₀ ≤ X := (le_max_right _ _).trans hx
  have hx' : (128 : ℝ) ≤ X := by exact_mod_cast (le_max_left 128 X₀).trans hx
  have hnx' : (n m : ℝ) ≤ 4 * (X : ℝ) + 3 := by
    have : n m ≤ 4 * X + 3 := by dsimp only [X]; omega
    exact_mod_cast this
  obtain ⟨q, hq, hqx, hdiv⟩ := primorial_dvd_cleared_of_fibre (X := X) (ordinalMap b m f)
    hcard_lt hclear hD (by omega) (by dsimp only [X, n] at hs ⊢; omega)
    (by dsimp only [X, n]; omega)
  have hlog_prim (Y : ℕ) : Real.log (primorial Y) = Chebyshev.theta Y := by
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have hp := primorial_pos X
  have hle := Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos hp hD) hq) hdiv
  have hlog_p := Real.log_le_log (Nat.cast_pos.mpr (primorial_pos (2 * X))) (Nat.cast_le.mpr hle)
  rw [Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (mul_ne_zero (Nat.cast_pos.mpr hp).ne' (Nat.cast_pos.mpr hD).ne') (Nat.cast_pos.mpr hq).ne',
    Real.log_mul (Nat.cast_pos.mpr hp).ne' (Nat.cast_pos.mpr hD).ne',
    hlog_prim, hlog_prim] at hlog_p
  have h₁ := (abs_le.mp (hθ X hx₀)).2
  have h₂ := (abs_le.mp (hθ (2 * X) (by omega))).1
  have hlog2X : Real.log (2 * (X : ℝ)) ≤ X / 4 := by
    have he : (2 * (X : ℝ)) = 16 * (X / 8) := by ring
    have hxpos : 0 < (X : ℝ) / 8 := by linarith only [hx']
    rw [he, Real.log_mul (by norm_num) hxpos.ne']
    linarith only [Real.log_le_sub_one_of_pos hxpos, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16), hx']
  have hq_log := Real.log_le_log (Nat.cast_pos.mpr hq) (Nat.cast_le.mpr hqx)
  push_cast at h₂ hq_log
  have hD_lo : (n m : ℝ) / 20 ≤ Real.log D := by
    linarith only [hnx', h₁, h₂, hlog2X, hlog_p, hq_log, hx']
  have hn_real : 0 < (n m : ℝ) := Nat.cast_pos.mpr hn_pos
  have hll := Real.log_le_log (div_pos hn_real (by norm_num : (0 : ℝ) < 20)) hD_lo
  rw [Real.log_div hn_real.ne' (by norm_num)] at hll
  have hdiv_le := div_le_div_of_nonneg_right hll (sq_nonneg (m : ℝ))
  rw [sub_div] at hdiv_le
  exact lt_of_lt_of_le (hl_m : 9 * integerProbe N b - ε < Real.log (n m) / (m : ℝ)^2 - Real.log 20 / (m : ℝ)^2) hdiv_le

/-! ### 2. Retirement of polynomial rounding with arbitrary first-output carry -/

/-- If `D * f₂(x) + r(x) = P(x₁, x₂)` for a bivariate integer polynomial `P` and
remainder `r(x) < D`, while the first output `f₁(x)` is completely unrestricted
(including any carry of `r(x)`), then `P` preserves congruences modulo the coprime
pair `(Ds, Ds + 1)` with values in `[0, Ds)`, forcing either `n² ≤ maxFibre f * L`
or `n < 2 * D * s + 1`. -/
theorem polynomial_rounding_carry_fibre_or_denom {n L s D : ℕ}
    (f : Fin n × Fin n → Fin L × Fin s) (P : MvPolynomial Bool ℤ)
    (r : Fin n × Fin n → ℕ) (hD : 0 < D) (hs : 0 < s)
    (hr : ∀ x, r x < D)
    (hP : ∀ x, ((D * (f x).2.val + r x : ℕ) : ℤ) = MvPolynomial.eval (boxPoint x) P) :
    n * n ≤ maxFibre f * L ∨ n < 2 * D * s + 1 := by
  by_cases hn : 2 * D * s + 1 ≤ n
  · left
    let v : Fin n × Fin n → ℕ := fun x => D * (f x).2.val + r x
    have hv_lt (x : Fin n × Fin n) : v x < D * s := by
      have hf2 : (f x).2.val + 1 ≤ s := (f x).2.isLt
      have hmul : D * ((f x).2.val + 1) ≤ D * s := Nat.mul_le_mul_left D hf2
      dsimp only [v]
      have hr_x := hr x
      linarith
    have hv_mod (u : ℕ) (x y : Fin n × Fin n)
        (hx : x.1.val ≡ y.1.val [MOD u]) (hy : x.2.val ≡ y.2.val [MOD u]) :
        v x ≡ v y [MOD u] := by
      let φ := Int.castRingHom (ZMod u)
      have he : φ ∘ boxPoint x = φ ∘ boxPoint y := by
        funext i
        cases i
        · simpa [φ, boxPoint] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hx
        · simpa [φ, boxPoint] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hy
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      have hx' := congrArg φ (hP x)
      have hy' := congrArg φ (hP y)
      rw [MvPolynomial.map_eval, he] at hx'
      rw [MvPolynomial.map_eval] at hy'
      simpa [φ, v] using hx'.trans hy'.symm
    let u₁ := D * s
    let u₂ := D * s + 1
    have hu₁ : 0 < u₁ := Nat.mul_pos hD hs
    have hcop : u₁.Coprime u₂ := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right u₁)
    have hsum : u₁ + u₂ ≤ n := by
      have : u₁ + u₂ = 2 * D * s + 1 := by dsimp [u₁, u₂]; ring
      omega
    have eq₁ (x y : Fin n × Fin n) (hx : x.1.val ≡ y.1.val [MOD u₁]) (hy : x.2.val ≡ y.2.val [MOD u₁]) :
        v x = v y := (hv_mod u₁ x y hx hy).eq_of_lt_of_lt (hv_lt x) (hv_lt y)
    have eq₂ (x y : Fin n × Fin n) (hx : x.1.val ≡ y.1.val [MOD u₂]) (hy : x.2.val ≡ y.2.val [MOD u₂]) :
        v x = v y :=
      (hv_mod u₂ x y hx hy).eq_of_lt_of_lt ((hv_lt x).trans (Nat.lt_succ_self u₁))
        ((hv_lt y).trans (Nat.lt_succ_self u₁))
    have hv_const (x y : Fin n × Fin n) : v x = v y := by
      have row := constant_of_two_periods (fun i => v (i, x.2)) hu₁ hcop hsum
        (fun i j h => eq₁ _ _ h .rfl) (fun i j h => eq₂ _ _ h .rfl)
      have col := constant_of_two_periods (fun j => v (y.1, j)) hu₁ hcop hsum
        (fun i j h => eq₁ _ _ .rfl h) (fun i j h => eq₂ _ _ .rfl h)
      exact (row x.1 y.1).trans (col x.2 y.2)
    refine card_sq_le_maxFibre_mul_of_second_const f fun x y => ?_
    apply Fin.ext
    have hdiv (z : Fin n × Fin n) : v z / D = (f z).2.val := by
      dsimp only [v]
      rw [Nat.mul_add_div hD, Nat.div_eq_of_lt (hr z), add_zero]
    rw [← hdiv x, ← hdiv y, hv_const x y]
  · exact Or.inr (lt_of_not_ge hn)

/-- Polynomial rounding of the narrow coordinate with **arbitrary** carry in the
first coordinate is obstructed along `(2mb, 3mb, 4mb)`: eventually either
`log F(f) > δ₁ m²` (`δ₁ < 2 Q(b)`) or `log D > δ₂ m²` (`δ₂ < 5 Q(b)`). -/
theorem eventually_polynomial_carry_quadratic_fibre {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {δ₁ δ₂ : ℝ}
    (hδ₁ : δ₁ < 2 * integerProbe N b) (hδ₂ : δ₂ < 5 * integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (D : ℕ)
      (P : MvPolynomial Bool ℤ) (r : Fin (rayCard b 3 m) × Fin (rayCard b 3 m) → ℕ),
      0 < D → (∀ x, r x < D) →
      (∀ x, ((D * (ordinalMap b m f x).2.val + r x : ℕ) : ℤ) = MvPolynomial.eval (boxPoint x) P) →
      δ₁ * (m : ℝ)^2 < Real.log (maxFibre f) ∨ δ₂ * (m : ℝ)^2 < Real.log D := by
  have hfib_lim := ((rayCard_tateLimit hb 3).const_mul 2).sub (rayCard_tateLimit hb 4)
  have hfib_ev := hfib_lim.eventually_const_lt
    (show δ₁ < 2 * ((3 : ℝ)^2 * integerProbe N b) - (4 : ℝ)^2 * integerProbe N b by linarith)
  have hden_lim := ((rayCard_tateLimit hb 3).sub (rayCard_tateLimit hb 2)).sub (logRate_const_zero 3)
  have hden_ev := hden_lim.eventually_const_lt
    (show δ₂ < (3 : ℝ)^2 * integerProbe N b - (2 : ℝ)^2 * integerProbe N b - 0 by linarith)
  filter_upwards [hfib_ev, hden_ev, eventually_ge_atTop 1] with m hm₁ hm₂ hm1
  intro f D P r hD hr hP
  let n := rayCard b 3 m
  let L := rayCard b 4 m
  let s := rayCard b 2 m
  have hn : 0 < n := rayCard_pos b 3 m
  have hL : 0 < L := rayCard_pos b 4 m
  have hs : 0 < s := rayCard_pos b 2 m
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  rcases polynomial_rounding_carry_fibre_or_denom (ordinalMap b m f) P r hD hs hr hP with hcard | hlt
  · left
    rw [maxFibre_ordinalMap] at hcard
    haveI := Fin.pos_iff_nonempty.mp hn
    have hfpos : 0 < maxFibre f := by rw [← maxFibre_ordinalMap]; exact maxFibre_pos _
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (Nat.mul_pos hn hn)) (Nat.cast_le.mpr hcard)
    rw [log_nat_mul hn hn, log_nat_mul hfpos hL] at hlog
    have hd : δ₁ < (2 * Real.log n - Real.log L) / (m : ℝ)^2 := by
      simpa only [sub_div, mul_div_assoc] using hm₁
    linarith only [(lt_div_iff₀ hm2).mp hd, hlog]
  · right
    have hub : n < 3 * D * s := by
      have h1 : 1 ≤ D * s := Nat.mul_pos hD hs
      change n < 2 * D * s + 1 at hlt
      linarith only [hlt, h1]
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn) (Nat.cast_lt.mpr hub)
    rw [log_nat_mul (Nat.mul_pos (by decide) hD) hs, log_nat_mul (by decide) hD] at hlog
    have hd : δ₂ < (Real.log n - Real.log s - Real.log (3 : ℕ)) / (m : ℝ)^2 := by
      simpa only [sub_div] using hm₂
    linarith only [(lt_div_iff₀ hm2).mp hd, hlog]

/-! ### 3. Exported Euclidean carry infects the wide output at two coprime places -/

/-- Congruence of both input indices modulo `P` forces congruence of the wide output modulo `u`. -/
def preservesFirstMod {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) (P u : ℕ) : Prop :=
  ∀ x y, x.1.val ≡ y.1.val [MOD P] → x.2.val ≡ y.2.val [MOD P] →
    (f x).1.val ≡ (f y).1.val [MOD u]

/-- Loss of `i` digits at `p` in the first (wide) output coordinate. -/
def firstPrecisionLoss {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) (p i : ℕ) : Prop :=
  ∀ r : ℕ, preservesFirstMod f (p ^ (r + i)) (p ^ r)

/-- Canonical Euclidean carry map sending `(x₁, x₂)` to `(x₁ % M + M * x₂, x₁ / M)`. -/
def euclideanCarryBoxMap {n L s M : ℕ} (hM : 0 < M) (hL : M * n ≤ L) (hs : n ≤ M * s)
    (x : Fin n × Fin n) : Fin L × Fin s :=
  (⟨x.1.val % M + M * x.2.val, by
      have h1 : x.1.val % M < M := Nat.mod_lt _ hM
      have h2 : M * (x.2.val + 1) ≤ M * n := Nat.mul_le_mul_left M x.2.isLt
      linarith⟩,
   ⟨x.1.val / M, (Nat.div_lt_iff_lt_mul hM).mpr (x.1.isLt.trans_le (mul_comm M s ▸ hs))⟩)

theorem euclideanCarryBoxMap_injective {n L s M : ℕ} (hM : 0 < M) (hL : M * n ≤ L) (hs : n ≤ M * s) :
    Function.Injective (euclideanCarryBoxMap hM hL hs) := by
  intro x y he
  have h1 : x.1.val % M + M * x.2.val = y.1.val % M + M * y.2.val :=
    congrArg (fun z : Fin L × Fin s => z.1.val) he
  have h2 : x.1.val / M = y.1.val / M :=
    congrArg (fun z : Fin L × Fin s => z.2.val) he
  have hmod : x.1.val % M = y.1.val % M := by
    have hm := congrArg (· % M) h1
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_mod] using hm
  have hx2 : x.2.val = y.2.val := by
    rw [hmod] at h1
    exact mul_left_cancel₀ hM.ne' (Nat.add_left_cancel h1)
  refine Prod.ext (Fin.ext ?_) (Fin.ext hx2)
  calc x.1.val = x.1.val % M + M * (x.1.val / M) := (Nat.mod_add_div _ _).symm
    _ = y.1.val % M + M * (y.1.val / M) := by rw [hmod, h2]
    _ = y.1.val := Nat.mod_add_div _ _

/-- Any map whose first output packs the Euclidean remainder as `(x₁ % M) + M * x₂`
(`M ≥ 2`, `n ≥ 2`) satisfies `n * (n - 1) < L * (p * p^i + q * q^j)` for any
first-output precision losses `(i, j)` at coprime bases `(p, q)`. -/
theorem carryMap_firstPrecision_loss {n L s M p q i j : ℕ}
    (f : Fin n × Fin n → Fin L × Fin s) (hn : 2 ≤ n) (hM : 2 ≤ M)
    (hcarry : ∀ x, (f x).1.val = x.1.val % M + M * x.2.val)
    (hp : 1 < p) (hq : 1 < q) (hc : p.Coprime q)
    (hi : firstPrecisionLoss f p i) (hj : firstPrecisionLoss f q j) :
    n * (n - 1) < L * (p * p ^ i + q * q ^ j) := by
  have hMn_lt_L : M * (n - 1) < L := by
    let z : Fin n × Fin n := (⟨0, by omega⟩, ⟨n - 1, by omega⟩)
    have hz := hcarry z
    dsimp only [z] at hz
    rw [Nat.zero_mod, zero_add] at hz
    exact hz ▸ (f z).1.isLt
  let r := Nat.log p M + 1
  let t := Nat.log q M + 1
  have hM_pos : 0 < M := by omega
  have hu : M ≤ p ^ r := (Nat.lt_pow_succ_log_self hp M).le
  have hv : M ≤ q ^ t := (Nat.lt_pow_succ_log_self hq M).le
  have hslice_lt (a : Fin n) : (f (a, ⟨0, by omega⟩)).1.val < M := by
    rw [hcarry]
    simpa only [mul_zero, add_zero] using Nat.mod_lt a.val hM_pos
  have hn_lt : n < p ^ (r + i) + q ^ (t + j) := by
    by_contra! hsum
    have eqP (a b : Fin n) (h : a.val ≡ b.val [MOD p ^ (r + i)]) :
        (f (a, ⟨0, by omega⟩)).1.val = (f (b, ⟨0, by omega⟩)).1.val :=
      (hi r (a, ⟨0, by omega⟩) (b, ⟨0, by omega⟩) h .rfl).eq_of_lt_of_lt
        ((hslice_lt a).trans_le hu) ((hslice_lt b).trans_le hu)
    have eqQ (a b : Fin n) (h : a.val ≡ b.val [MOD q ^ (t + j)]) :
        (f (a, ⟨0, by omega⟩)).1.val = (f (b, ⟨0, by omega⟩)).1.val :=
      (hj t (a, ⟨0, by omega⟩) (b, ⟨0, by omega⟩) h .rfl).eq_of_lt_of_lt
        ((hslice_lt a).trans_le hv) ((hslice_lt b).trans_le hv)
    have hconst := constant_of_two_periods (fun a : Fin n => (f (a, ⟨0, by omega⟩)).1.val)
      (pow_pos (by omega) _) ((hc.pow_left _).pow_right _) hsum eqP eqQ
    have h01 := hconst ⟨0, by omega⟩ ⟨1, by omega⟩
    rw [hcarry, hcarry] at h01
    simp only [mul_zero, add_zero, Nat.zero_mod, Nat.mod_eq_of_lt hM] at h01
    exact zero_ne_one h01
  have hsmall (c : ℕ) : c ^ (Nat.log c M + 1) ≤ M * c := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right c (Nat.pow_log_le_self c hM_pos.ne')
  have hn_ub : n < M * (p * p ^ i + q * q ^ j) := by
    refine hn_lt.trans_le ?_
    rw [pow_add p r i, pow_add q t j]
    calc p ^ r * p ^ i + q ^ t * q ^ j
        ≤ M * p * p ^ i + M * q * q ^ j :=
          Nat.add_le_add (Nat.mul_le_mul_right _ (hsmall p)) (Nat.mul_le_mul_right _ (hsmall q))
      _ = M * (p * p ^ i + q * q ^ j) := by ring
  calc n * (n - 1)
      < M * (p * p ^ i + q * q ^ j) * (n - 1) := Nat.mul_lt_mul_of_pos_right hn_ub (by omega)
    _ = M * (n - 1) * (p * p ^ i + q * q ^ j) := by ring
    _ ≤ L * (p * p ^ i + q * q ^ j) := Nat.mul_le_mul_right _ hMn_lt_L.le

/-- Along `(2mb, 3mb, 4mb)`, exporting the Euclidean remainder `(x₁ % M) + M * x₂`
(`M ≥ 2`) to the first output forces two-place precision loss
`max(i log p, j log q) > δ m²` (`δ < 2 Q(b)`) in the first output coordinate. -/
theorem eventually_carryMap_firstOutput_precision_cost {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (hc : p.Coprime q)
    {δ : ℝ} (hδ : δ < 2 * integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (M i j : ℕ),
      2 ≤ M → (∀ x, (ordinalMap b m f x).1.val = x.1.val % M + M * x.2.val) →
      firstPrecisionLoss (ordinalMap b m f) p i →
      firstPrecisionLoss (ordinalMap b m f) q j →
      δ * (m : ℝ)^2 < max ((i : ℝ) * Real.log p) ((j : ℝ) * Real.log q) := by
  have hlim := (((rayCard_tateLimit hb 3).const_mul 2).sub (rayCard_tateLimit hb 4)).sub
    ((logRate_const_zero 2).add (logRate_const_zero (p + q)))
  have hev := hlim.eventually_const_lt
    (show δ < 2 * ((3 : ℝ)^2 * integerProbe N b) - (4 : ℝ)^2 * integerProbe N b - (0 + 0) by linarith)
  filter_upwards [hev, eventually_narrow_mul_lt_middle hb 2 (by decide), eventually_ge_atTop 1]
    with m hm hn2 hm1
  intro f M i j hM hcarry hi hj
  let n := rayCard b 3 m
  let L := rayCard b 4 m
  have hn_ge2 : 2 ≤ n := by have := rayCard_pos b 2 m; omega
  have hn_pos : 0 < n := by omega
  have hL_pos : 0 < L := rayCard_pos b 4 m
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  have hloss := carryMap_firstPrecision_loss (ordinalMap b m f) hn_ge2 hM hcarry hp hq hc hi hj
  have hn_sq : n * n ≤ 2 * (n * (n - 1)) := by
    have : n ≤ 2 * (n - 1) := by omega
    calc n * n ≤ n * (2 * (n - 1)) := Nat.mul_le_mul_left n this
      _ = 2 * (n * (n - 1)) := by ring
  have hprod : n * n < 2 * L * (p * p ^ i + q * q ^ j) := by
    calc n * n ≤ 2 * (n * (n - 1)) := hn_sq
      _ < 2 * (L * (p * p ^ i + q * q ^ j)) := Nat.mul_lt_mul_of_pos_left hloss (by decide)
      _ = 2 * L * (p * p ^ i + q * q ^ j) := by ring
  have hd : δ < (2 * Real.log n - Real.log L - (Real.log (2 : ℕ) + Real.log (p + q : ℕ))) / (m : ℝ)^2 := by
    simpa only [add_div, sub_div, mul_div_assoc] using hm
  have hm' := (lt_div_iff₀ hm2).mp hd
  have hpq : 0 < p + q := by omega
  rcases le_total (p ^ i) (q ^ j) with hij | hji
  · have hub : n * n < 2 * L * ((p + q) * q ^ j) := hprod.trans_le (Nat.mul_le_mul_left (2 * L) (by
      calc p * p ^ i + q * q ^ j ≤ p * q ^ j + q * q ^ j :=
            Nat.add_le_add_right (Nat.mul_le_mul_left p hij) _
        _ = (p + q) * q ^ j := by ring))
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr (Nat.mul_pos hn_pos hn_pos)) (Nat.cast_lt.mpr hub)
    rw [log_nat_mul hn_pos hn_pos,
      log_nat_mul (Nat.mul_pos (by decide) hL_pos) (Nat.mul_pos hpq (pow_pos (by omega) j)),
      log_nat_mul (by decide) hL_pos, log_nat_mul hpq (pow_pos (by omega) j),
      Nat.cast_pow, Real.log_pow] at hlog
    linarith only [hm', hlog, le_max_right ((i : ℝ) * Real.log p) ((j : ℝ) * Real.log q)]
  · have hub : n * n < 2 * L * ((p + q) * p ^ i) := hprod.trans_le (Nat.mul_le_mul_left (2 * L) (by
      calc p * p ^ i + q * q ^ j ≤ p * p ^ i + q * p ^ i :=
            Nat.add_le_add_left (Nat.mul_le_mul_left q hji) _
        _ = (p + q) * p ^ i := by ring))
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr (Nat.mul_pos hn_pos hn_pos)) (Nat.cast_lt.mpr hub)
    rw [log_nat_mul hn_pos hn_pos,
      log_nat_mul (Nat.mul_pos (by decide) hL_pos) (Nat.mul_pos hpq (pow_pos (by omega) i)),
      log_nat_mul (by decide) hL_pos, log_nat_mul hpq (pow_pos (by omega) i),
      Nat.cast_pow, Real.log_pow] at hlog
    linarith only [hm', hlog, le_max_left ((i : ℝ) * Real.log p) ((j : ℝ) * Real.log q)]

/-! ### 4. Universal joint inverse precision loss at a single place -/

/-- Joint inverse precision loss `k` at base `p`: knowing both outputs modulo
`p^(r + k)` uniquely determines both inputs modulo `p^r`. -/
def jointInversePrecisionLoss {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) (p k : ℕ) : Prop :=
  ∀ (r : ℕ) (x y : Fin n × Fin n),
    (f x).1.val ≡ (f y).1.val [MOD p ^ (r + k)] →
    (f x).2.val ≡ (f y).2.val [MOD p ^ (r + k)] →
    x.1.val ≡ y.1.val [MOD p ^ r] ∧ x.2.val ≡ y.2.val [MOD p ^ r]

/-- Even at a **single** base `p > 1`, any map `f : Fin n × Fin n → Fin L × Fin s`
with `jointInversePrecisionLoss f p k` obeys `n < p * s * p^(2k)`. -/
theorem joint_inverse_precision_loss {n L s p k : ℕ}
    (f : Fin n × Fin n → Fin L × Fin s) (hp : 1 < p) (hn : 0 < n) (hs : 0 < s)
    (hinv : jointInversePrecisionLoss f p k) :
    n < p * s * p ^ (2 * k) := by
  by_contra! hle
  let R := Nat.log p n
  have hp0 : 0 < p := by omega
  have hpR_le : p ^ R ≤ n := Nat.pow_log_le_self p hn.ne'
  have hn_lt : n < p * p ^ R := by
    have h := Nat.lt_pow_succ_log_self hp n
    rwa [pow_succ, mul_comm] at h
  have hs_lt : s * p ^ (2 * k) < p ^ R := by
    have hmul : p * (s * p ^ (2 * k)) < p * p ^ R :=
      calc p * (s * p ^ (2 * k)) = p * s * p ^ (2 * k) := by ring
        _ ≤ n := hle
        _ < p * p ^ R := hn_lt
    exact (mul_lt_mul_iff_right₀ hp0).mp hmul
  have hk_lt_R : 2 * k < R := by
    have h1 : p ^ (2 * k) < p ^ R :=
      (Nat.le_mul_of_pos_left (p ^ (2 * k)) hs).trans_lt hs_lt
    exact (Nat.pow_lt_pow_iff_right hp).mp h1
  let r := R - k
  have hrk : r + k = R := by omega
  have hpR_split : p ^ R = p ^ k * p ^ r := by rw [← hrk, add_comm, pow_add]
  let ι (u : Fin (p ^ R) × Fin (p ^ R)) : Fin n × Fin n :=
    (⟨u.1.val, u.1.isLt.trans_le hpR_le⟩, ⟨u.2.val, u.2.isLt.trans_le hpR_le⟩)
  let Θ (u : Fin (p ^ R) × Fin (p ^ R)) :
      (Fin (p ^ R) × Fin s) × (Fin (p ^ k) × Fin (p ^ k)) :=
    ((⟨(f (ι u)).1.val % p ^ R, Nat.mod_lt _ (pow_pos hp0 R)⟩, (f (ι u)).2),
     (⟨u.1.val / p ^ r, (Nat.div_lt_iff_lt_mul (pow_pos hp0 r)).mpr (hpR_split ▸ u.1.isLt)⟩,
      ⟨u.2.val / p ^ r, (Nat.div_lt_iff_lt_mul (pow_pos hp0 r)).mpr (hpR_split ▸ u.2.isLt)⟩))
  have hΘ : Function.Injective Θ := by
    intro u v huv
    have h1_mod : (f (ι u)).1.val ≡ (f (ι v)).1.val [MOD p ^ (r + k)] := by
      have he := congrArg (fun w => w.1.1.val) huv
      dsimp only [Θ] at he
      rwa [hrk]
    have h2_eq : (f (ι u)).2 = (f (ι v)).2 := congrArg (fun w => w.1.2) huv
    have h2_mod : (f (ι u)).2.val ≡ (f (ι v)).2.val [MOD p ^ (r + k)] := by rw [h2_eq]
    obtain ⟨hm1, hm2⟩ := hinv r (ι u) (ι v) h1_mod h2_mod
    have hq1 : u.1.val / p ^ r = v.1.val / p ^ r := congrArg (fun w => w.2.1.val) huv
    have hq2 : u.2.val / p ^ r = v.2.val / p ^ r := congrArg (fun w => w.2.2.val) huv
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · calc u.1.val = u.1.val % p ^ r + p ^ r * (u.1.val / p ^ r) := (Nat.mod_add_div _ _).symm
        _ = v.1.val % p ^ r + p ^ r * (v.1.val / p ^ r) := by rw [hm1, hq1]
        _ = v.1.val := Nat.mod_add_div _ _
    · calc u.2.val = u.2.val % p ^ r + p ^ r * (u.2.val / p ^ r) := (Nat.mod_add_div _ _).symm
        _ = v.2.val % p ^ r + p ^ r * (v.2.val / p ^ r) := by rw [hm2, hq2]
        _ = v.2.val := Nat.mod_add_div _ _
  have hcard := Fintype.card_le_of_injective Θ hΘ
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  have hrew : p ^ R * s * (p ^ k * p ^ k) = p ^ R * (s * p ^ (2 * k)) := by
    rw [← pow_add, ← two_mul]; ring
  rw [hrew] at hcard
  exact hs_lt.not_ge ((mul_le_mul_iff_right₀ (pow_pos hp0 R)).mp hcard)

/-- Along `(2mb, 3mb, 4mb)` on a positive ray `b`, even at a **single** base `p > 1`,
every map `f` with `jointInversePrecisionLoss (ordinalMap b m f) p k` loses
`k log p > δ m²` eventually for all `δ < (5 / 2) * Q(b)`. -/
theorem eventually_joint_inverse_precision_cost {N : ℕ} {b : Fin N → ℤ}
    (hb : 0 < integerProbe N b) {p : ℕ} (hp : 1 < p)
    {δ : ℝ} (hδ : δ < (5 / 2) * integerProbe N b) :
    ∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (k : ℕ),
      jointInversePrecisionLoss (ordinalMap b m f) p k →
      δ * (m : ℝ)^2 < (k : ℝ) * Real.log p := by
  have hlim := ((rayCard_tateLimit hb 3).sub (rayCard_tateLimit hb 2)).sub (logRate_const_zero p)
  have hev := hlim.eventually_const_lt
    (show 2 * δ < (3 : ℝ)^2 * integerProbe N b - (2 : ℝ)^2 * integerProbe N b - 0 by linarith)
  filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
  intro f k hinv
  let n := rayCard b 3 m
  let s := rayCard b 2 m
  have hn : 0 < n := rayCard_pos b 3 m
  have hs : 0 < s := rayCard_pos b 2 m
  have hm2 : 0 < (m : ℝ)^2 := by positivity
  have hlt := joint_inverse_precision_loss (ordinalMap b m f) hp hn hs hinv
  have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn) (Nat.cast_lt.mpr hlt)
  rw [log_nat_mul (Nat.mul_pos (by omega) hs) (pow_pos (by omega) (2 * k)),
    log_nat_mul (by omega) hs, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] at hlog
  have hd : 2 * δ < (Real.log n - Real.log s - Real.log p) / (m : ℝ)^2 := by
    simpa only [sub_div] using hm
  linarith only [(lt_div_iff₀ hm2).mp hd, hlog]

/-- Unconditional two-atom prime ray exhibiting both the two-place fibre/precision
dichotomy and the polynomial-carry obstruction without assuming RH. -/
theorem exists_prime_ray_twoOutput_carry_obstructions :
    ∃ (p : ℕ) (b : Fin (p + 1) → ℤ), p.Prime ∧ (b = primePair p ∨ b = primeDifference p) ∧
      0 < integerProbe (p + 1) b ∧
      (∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (i j : ℕ),
        secondPrecisionLoss (ordinalMap b m f) 2 i →
        secondPrecisionLoss (ordinalMap b m f) 3 j →
        integerProbe (p + 1) b * (m : ℝ)^2 < Real.log (maxFibre f) ∨
          4 * integerProbe (p + 1) b * (m : ℝ)^2 <
            max ((i : ℝ) * Real.log 2) ((j : ℝ) * Real.log 3)) ∧
      (∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (D : ℕ)
        (P : MvPolynomial Bool ℤ) (r : Fin (rayCard b 3 m) × Fin (rayCard b 3 m) → ℕ),
        0 < D → (∀ x, r x < D) →
        (∀ x, ((D * (ordinalMap b m f x).2.val + r x : ℕ) : ℤ) = MvPolynomial.eval (boxPoint x) P) →
        integerProbe (p + 1) b * (m : ℝ)^2 < Real.log (maxFibre f) ∨
          4 * integerProbe (p + 1) b * (m : ℝ)^2 < Real.log D) ∧
      (∀ᶠ m : ℕ in atTop, ∀ (f : rayProductMap b m) (k : ℕ),
        jointInversePrecisionLoss (ordinalMap b m f) 2 k →
        2 * integerProbe (p + 1) b * (m : ℝ)^2 < (k : ℝ) * Real.log 2) := by
  obtain ⟨p, b, hp, hb_eq, hb_pos, _⟩ := exists_prime_background_midpointTest
  refine ⟨p, b, hp, hb_eq, hb_pos, ?_, ?_, ?_⟩
  · exact eventually_twoPlace_fibre_or_precision_cost hb_pos (by decide) (by decide) (by decide)
      (by linarith) (by linarith)
  · exact eventually_polynomial_carry_quadratic_fibre hb_pos (by linarith) (by linarith)
  · exact eventually_joint_inverse_precision_cost hb_pos (by decide) (by linarith)

#print axioms eventually_twoPlace_fibre_or_precision_cost
#print axioms eventually_sharpened_twoPlace_precision_cost
#print axioms eventually_loglog_clearing_of_subquadratic_fibre
#print axioms eventually_polynomial_carry_quadratic_fibre
#print axioms eventually_carryMap_firstOutput_precision_cost
#print axioms eventually_joint_inverse_precision_cost
#print axioms exists_prime_ray_twoOutput_carry_obstructions

end GaloisForLFunctions.CountingHolography.Sections
