import GaloisForLFunctions.HTGeometry.StrelitzLogJetReduction

/-!
# A second-jet gap for polynomial-coefficient relations

Let `Q ∈ ℂ[z][F, U, V]` be nonzero.  Order its monomials by the exponent of `F`, then of `z`,
then of `U`, and let `s(V)` collect the coefficients of the largest such exponent triple.  At
every zero `(z, F, U, V)` of `Q` with `1 ≤ |z|, |F|, |U|`, `|U| ≤ B` and `|V| ≤ 1`,

`|s(V)| ≤ C ((1 + |z|)^E B^E / |F| + B^E / |z| + 1 / |U|)`.

Because `s ≠ 0`, a small bracket forbids `ρ / 2 < |V| ≤ ρ` for every sufficiently small `ρ`:
the second jet is confined to the disc of half the radius about the origin.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-- Bound for the `z`-degrees of the coefficients of a polynomial-coefficient relation. -/
def strelitzGapCoeffDegree (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) : ℕ :=
  Q.support.sup fun m => (Q.coeff m).natDegree

/-- Bound for the exponents of the first jet variable. -/
def strelitzGapJetDegree (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) : ℕ :=
  Q.support.sup fun m => m 1

/-- Index set of all exponent pairs `(m, k)`: a monomial exponent and a `z`-degree. -/
def strelitzGapIndex (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) :
    Finset ((Fin 3 →₀ ℕ) × ℕ) :=
  Q.support ×ˢ Finset.range (strelitzGapCoeffDegree Q + 1)

/-- The scalar coefficient of `z^k F^(m 0) U^(m 1) V^(m 2)`. -/
def strelitzGapCoeff (Q : MvPolynomial (Fin 3) (Polynomial ℂ))
    (p : (Fin 3 →₀ ℕ) × ℕ) : ℂ :=
  (Q.coeff p.1).coeff p.2

/-- Full expansion of the evaluated relation as a finite sum of scalar monomials. -/
theorem eval₂_eq_sum_strelitzGapIndex (Q : MvPolynomial (Fin 3) (Polynomial ℂ))
    (z F U V : ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q =
      ∑ p ∈ strelitzGapIndex Q,
        strelitzGapCoeff Q p * z ^ p.2 * F ^ p.1 0 * U ^ p.1 1 * V ^ p.1 2 := by
  classical
  rw [MvPolynomial.eval₂_eq, strelitzGapIndex, Finset.sum_product]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : (Q.coeff m).natDegree < strelitzGapCoeffDegree Q + 1 :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun m => (Q.coeff m).natDegree) hm)
  have hprod : (∏ i ∈ m.support, (![F, U, V] : Fin 3 → ℂ) i ^ m i) =
      F ^ m 0 * U ^ m 1 * V ^ m 2 := by
    have h := Finsupp.prod_fintype m (fun i e => (![F, U, V] : Fin 3 → ℂ) i ^ e)
      (by intro i; simp)
    rw [Fin.prod_univ_three] at h
    exact h
  rw [hprod]
  change (Q.coeff m).eval z * _ = _
  rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [strelitzGapCoeff]
  ring

/-- Coefficient polynomial in `V` of one exponent triple `(d, k, i)` for `(F, z, U)`. -/
def strelitzGapSlice (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) (d k i : ℕ) :
    Polynomial ℂ :=
  ∑ p ∈ (strelitzGapIndex Q).filter (fun p => p.1 0 = d ∧ p.2 = k ∧ p.1 1 = i),
    Polynomial.monomial (p.1 2) (strelitzGapCoeff Q p)

theorem eval_strelitzGapSlice (Q : MvPolynomial (Fin 3) (Polynomial ℂ)) (d k i : ℕ)
    (V : ℂ) :
    (strelitzGapSlice Q d k i).eval V =
      ∑ p ∈ (strelitzGapIndex Q).filter (fun p => p.1 0 = d ∧ p.2 = k ∧ p.1 1 = i),
        strelitzGapCoeff Q p * V ^ p.1 2 := by
  rw [strelitzGapSlice, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

/-- A slice through a nonzero scalar coefficient is a nonzero polynomial: distinct monomials of
the slice have distinct `V`-exponents. -/
theorem strelitzGapSlice_ne_zero {Q : MvPolynomial (Fin 3) (Polynomial ℂ)}
    {p₀ : (Fin 3 →₀ ℕ) × ℕ} (hp₀ : p₀ ∈ strelitzGapIndex Q)
    (hc : strelitzGapCoeff Q p₀ ≠ 0) :
    strelitzGapSlice Q (p₀.1 0) p₀.2 (p₀.1 1) ≠ 0 := by
  classical
  intro hzero
  have hcoeff := congrArg (fun s : Polynomial ℂ => s.coeff (p₀.1 2)) hzero
  simp only [strelitzGapSlice, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single p₀] at hcoeff
  · rw [if_pos rfl] at hcoeff
    exact hc hcoeff
  · intro p hp hne
    rw [if_neg]
    intro h2
    apply hne
    obtain ⟨-, h0, hk, h1⟩ := Finset.mem_filter.mp hp
    refine Prod.ext ?_ hk
    ext j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  · intro hnot
    exact absurd (Finset.mem_filter.mpr ⟨hp₀, rfl, rfl, rfl⟩) hnot

/-- Monomial comparison behind the lexicographic isolation: a monomial whose exponent triple
`(d', k', i')` is lexicographically below `(d, k, i)` is bounded by the leading monomial times
the error bracket. -/
theorem pow_mul_pow_mul_pow_le_strelitzGap {x f w B : ℝ} (hx : 1 ≤ x) (hf : 1 ≤ f)
    (hw : 1 ≤ w) (hwB : w ≤ B) {E d k i d' k' i' : ℕ} (hk' : k' ≤ E) (hi' : i' ≤ E)
    (hlt : d' < d ∨ (d' = d ∧ k' < k) ∨ (d' = d ∧ k' = k ∧ i' < i)) :
    x ^ k' * f ^ d' * w ^ i' ≤
      x ^ k * f ^ d * w ^ i * ((1 + x) ^ E * B ^ E / f + B ^ E / x + 1 / w) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hf0 : 0 < f := lt_of_lt_of_le one_pos hf
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  have hB : 1 ≤ B := hw.trans hwB
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  have h1x : 1 ≤ 1 + x := by linarith
  have hxk : 1 ≤ x ^ k := one_le_pow₀ hx
  have hwi : 1 ≤ w ^ i := one_le_pow₀ hw
  have hwiB : w ^ i' ≤ B ^ E * w ^ i :=
    calc w ^ i' ≤ B ^ i' := pow_le_pow_left₀ hw0.le hwB i'
      _ ≤ B ^ E := pow_le_pow_right₀ hB hi'
      _ ≤ B ^ E * w ^ i := le_mul_of_one_le_right (by positivity) hwi
  have hA : 0 ≤ (1 + x) ^ E * B ^ E / f := by positivity
  have hBx : 0 ≤ B ^ E / x := by positivity
  have hw' : 0 ≤ 1 / w := by positivity
  rcases hlt with hd | ⟨hd, hk⟩ | ⟨hd, hk, hi⟩
  · have hxk' : x ^ k' ≤ (1 + x) ^ E * x ^ k :=
      calc x ^ k' ≤ (1 + x) ^ k' := pow_le_pow_left₀ hx0.le (by linarith) k'
        _ ≤ (1 + x) ^ E := pow_le_pow_right₀ h1x hk'
        _ ≤ (1 + x) ^ E * x ^ k := le_mul_of_one_le_right (by positivity) hxk
    have hfd : f ^ d' ≤ f ^ d / f := by
      rw [le_div_iff₀ hf0, ← pow_succ]
      exact pow_le_pow_right₀ hf (by omega)
    calc x ^ k' * f ^ d' * w ^ i'
        ≤ ((1 + x) ^ E * x ^ k) * (f ^ d / f) * (B ^ E * w ^ i) := by
          gcongr
      _ = x ^ k * f ^ d * w ^ i * ((1 + x) ^ E * B ^ E / f) := by
          field_simp
      _ ≤ x ^ k * f ^ d * w ^ i * ((1 + x) ^ E * B ^ E / f + B ^ E / x + 1 / w) := by
          gcongr
          linarith
  · subst hd
    have hxk' : x ^ k' ≤ x ^ k / x := by
      rw [le_div_iff₀ hx0, ← pow_succ]
      exact pow_le_pow_right₀ hx (by omega)
    calc x ^ k' * f ^ d' * w ^ i'
        ≤ (x ^ k / x) * f ^ d' * (B ^ E * w ^ i) := by
          gcongr
      _ = x ^ k * f ^ d' * w ^ i * (B ^ E / x) := by
          field_simp
      _ ≤ x ^ k * f ^ d' * w ^ i * ((1 + x) ^ E * B ^ E / f + B ^ E / x + 1 / w) := by
          gcongr
          linarith
  · subst hd
    subst hk
    have hwi' : w ^ i' ≤ w ^ i / w := by
      rw [le_div_iff₀ hw0, ← pow_succ]
      exact pow_le_pow_right₀ hw (by omega)
    calc x ^ k' * f ^ d' * w ^ i'
        ≤ x ^ k' * f ^ d' * (w ^ i / w) := by
          gcongr
      _ = x ^ k' * f ^ d' * w ^ i * (1 / w) := by
          field_simp
      _ ≤ x ^ k' * f ^ d' * w ^ i * ((1 + x) ^ E * B ^ E / f + B ^ E / x + 1 / w) := by
          gcongr
          linarith

/-- **Lexicographic isolation.**  A nonzero polynomial-coefficient relation has a nonzero
coefficient polynomial `s(V)` bounded, at every zero with large `z`, `F`, `U` and bounded `V`,
by a fixed multiple of the error bracket. -/
theorem exists_strelitzGap_bound {Q : MvPolynomial (Fin 3) (Polynomial ℂ)} (hQ : Q ≠ 0) :
    ∃ (s : Polynomial ℂ) (C : ℝ) (E : ℕ), s ≠ 0 ∧ 0 ≤ C ∧
      ∀ (z F U V : ℂ) (B : ℝ),
        MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q = 0 →
        1 ≤ ‖z‖ → 1 ≤ ‖F‖ → 1 ≤ ‖U‖ → ‖U‖ ≤ B → ‖V‖ ≤ 1 →
        ‖s.eval V‖ ≤ C * ((1 + ‖z‖) ^ E * B ^ E / ‖F‖ + B ^ E / ‖z‖ + 1 / ‖U‖) := by
  classical
  set P := strelitzGapIndex Q with hP
  set A := P.filter (fun p => strelitzGapCoeff Q p ≠ 0) with hA
  have hAne : A.Nonempty := by
    obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hQ
    have hcm : Q.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    refine ⟨(m, (Q.coeff m).natDegree), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_product.mpr ⟨hm, Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Finset.le_sup (f := fun m => (Q.coeff m).natDegree) hm))⟩
    · exact Polynomial.leadingCoeff_ne_zero.mpr hcm
  obtain ⟨p₁, hp₁, hmax₁⟩ := Finset.exists_max_image A (fun p => p.1 0) hAne
  set A₁ := A.filter (fun p => p.1 0 = p₁.1 0) with hA₁
  obtain ⟨p₂, hp₂, hmax₂⟩ :=
    Finset.exists_max_image A₁ (fun p => p.2) ⟨p₁, Finset.mem_filter.mpr ⟨hp₁, rfl⟩⟩
  set A₂ := A₁.filter (fun p => p.2 = p₂.2) with hA₂
  obtain ⟨p₃, hp₃, hmax₃⟩ :=
    Finset.exists_max_image A₂ (fun p => p.1 1) ⟨p₂, Finset.mem_filter.mpr ⟨hp₂, rfl⟩⟩
  obtain ⟨hp₃A₁, hp₃k⟩ := Finset.mem_filter.mp hp₃
  obtain ⟨hp₃A, hp₃d⟩ := Finset.mem_filter.mp hp₃A₁
  obtain ⟨hp₃P, hp₃c⟩ := Finset.mem_filter.mp hp₃A
  set E := strelitzGapCoeffDegree Q + strelitzGapJetDegree Q with hE
  refine ⟨strelitzGapSlice Q (p₃.1 0) p₃.2 (p₃.1 1), ∑ p ∈ P, ‖strelitzGapCoeff Q p‖, E,
    strelitzGapSlice_ne_zero hp₃P hp₃c, Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
  intro z F U V B hrel hz hF hU hUB hV
  set d := p₃.1 0 with hd
  set k := p₃.2 with hk
  set i := p₃.1 1 with hi
  set β := (1 + ‖z‖) ^ E * B ^ E / ‖F‖ + B ^ E / ‖z‖ + 1 / ‖U‖ with hβ
  set W := ‖z‖ ^ k * ‖F‖ ^ d * ‖U‖ ^ i with hW
  have hW0 : 0 < W := by
    have : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz
    have : 0 < ‖F‖ := lt_of_lt_of_le one_pos hF
    have : 0 < ‖U‖ := lt_of_lt_of_le one_pos hU
    positivity
  set term : (Fin 3 →₀ ℕ) × ℕ → ℂ := fun p =>
    strelitzGapCoeff Q p * z ^ p.2 * F ^ p.1 0 * U ^ p.1 1 * V ^ p.1 2 with hterm
  set slice : (Fin 3 →₀ ℕ) × ℕ → Prop := fun p => p.1 0 = d ∧ p.2 = k ∧ p.1 1 = i
    with hslice
  have hsum := Finset.sum_filter_add_sum_filter_not P slice term
  rw [← eval₂_eq_sum_strelitzGapIndex, hrel] at hsum
  have hsliceEq : ∑ p ∈ P.filter slice, term p =
      z ^ k * F ^ d * U ^ i * (strelitzGapSlice Q d k i).eval V := by
    rw [eval_strelitzGapSlice, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨-, h0, h2, h1⟩ := Finset.mem_filter.mp hp
    simp only [hterm, h0, h2, h1]
    ring
  -- every monomial outside the leading slice is controlled by the bracket
  have hrest : ∀ p ∈ P.filter (fun p => ¬ slice p),
      ‖term p‖ ≤ ‖strelitzGapCoeff Q p‖ * (W * β) := by
    intro p hp
    obtain ⟨hpP, hpns⟩ := Finset.mem_filter.mp hp
    have hnorm : ‖term p‖ = ‖strelitzGapCoeff Q p‖ *
        (‖z‖ ^ p.2 * ‖F‖ ^ p.1 0 * ‖U‖ ^ p.1 1 * ‖V‖ ^ p.1 2) := by
      simp only [hterm, norm_mul, norm_pow]
      ring
    rw [hnorm]
    by_cases hc : strelitzGapCoeff Q p = 0
    · rw [hc, norm_zero, zero_mul, zero_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hpA : p ∈ A := Finset.mem_filter.mpr ⟨hpP, hc⟩
    obtain ⟨hpS, hpR⟩ := Finset.mem_product.mp hpP
    have hk' : p.2 ≤ E := by
      have := Finset.mem_range.mp hpR
      omega
    have hi' : p.1 1 ≤ E := by
      have := Finset.le_sup (f := fun m : Fin 3 →₀ ℕ => m 1) hpS
      change p.1 1 ≤ strelitzGapJetDegree Q at this
      omega
    have hlt : p.1 0 < d ∨ (p.1 0 = d ∧ p.2 < k) ∨ (p.1 0 = d ∧ p.2 = k ∧ p.1 1 < i) := by
      have hle0 : p.1 0 ≤ d := by
        rw [hp₃d]
        exact hmax₁ p hpA
      rcases lt_or_eq_of_le hle0 with h0 | h0
      · exact Or.inl h0
      have hpA₁ : p ∈ A₁ := Finset.mem_filter.mpr ⟨hpA, h0.trans hp₃d⟩
      have hle2 : p.2 ≤ k := by
        rw [hp₃k]
        exact hmax₂ p hpA₁
      rcases lt_or_eq_of_le hle2 with h2 | h2
      · exact Or.inr (Or.inl ⟨h0, h2⟩)
      have hpA₂ : p ∈ A₂ := Finset.mem_filter.mpr ⟨hpA₁, h2.trans hp₃k⟩
      have hle1 : p.1 1 ≤ i := hmax₃ p hpA₂
      rcases lt_or_eq_of_le hle1 with h1 | h1
      · exact Or.inr (Or.inr ⟨h0, h2, h1⟩)
      · exact absurd ⟨h0, h2, h1⟩ hpns
    have hVp : ‖V‖ ^ p.1 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hV
    have hmain := pow_mul_pow_mul_pow_le_strelitzGap hz hF hU hUB hk' hi' hlt
    calc ‖z‖ ^ p.2 * ‖F‖ ^ p.1 0 * ‖U‖ ^ p.1 1 * ‖V‖ ^ p.1 2
        ≤ ‖z‖ ^ p.2 * ‖F‖ ^ p.1 0 * ‖U‖ ^ p.1 1 * 1 := by
          gcongr
      _ ≤ W * β := by
          rw [mul_one]
          exact hmain
  have hβ0 : 0 ≤ β := by
    have : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz
    have : 0 < ‖F‖ := lt_of_lt_of_le one_pos hF
    have : 0 < ‖U‖ := lt_of_lt_of_le one_pos hU
    have : 0 ≤ B := (norm_nonneg U).trans hUB
    positivity
  have hlead : W * ‖(strelitzGapSlice Q d k i).eval V‖ ≤
      (∑ p ∈ P, ‖strelitzGapCoeff Q p‖) * (W * β) := by
    have hWeq : W * ‖(strelitzGapSlice Q d k i).eval V‖ =
        ‖∑ p ∈ P.filter (fun p => ¬ slice p), term p‖ := by
      have hneg : ∑ p ∈ P.filter (fun p => ¬ slice p), term p =
          -(z ^ k * F ^ d * U ^ i * (strelitzGapSlice Q d k i).eval V) := by
        rw [← hsliceEq]
        linear_combination hsum
      rw [hneg, norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
    rw [hWeq]
    calc ‖∑ p ∈ P.filter (fun p => ¬ slice p), term p‖
        ≤ ∑ p ∈ P.filter (fun p => ¬ slice p), ‖term p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ P.filter (fun p => ¬ slice p), ‖strelitzGapCoeff Q p‖ * (W * β) :=
          Finset.sum_le_sum hrest
      _ ≤ ∑ p ∈ P, ‖strelitzGapCoeff Q p‖ * (W * β) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun _ _ _ => mul_nonneg (norm_nonneg _) (mul_nonneg hW0.le hβ0)
      _ = (∑ p ∈ P, ‖strelitzGapCoeff Q p‖) * (W * β) := by
          rw [Finset.sum_mul]
  have hfinal : W * ‖(strelitzGapSlice Q d k i).eval V‖ ≤
      W * ((∑ p ∈ P, ‖strelitzGapCoeff Q p‖) * β) := by
    calc W * ‖(strelitzGapSlice Q d k i).eval V‖
        ≤ (∑ p ∈ P, ‖strelitzGapCoeff Q p‖) * (W * β) := hlead
      _ = W * ((∑ p ∈ P, ‖strelitzGapCoeff Q p‖) * β) := by ring
  exact le_of_mul_le_mul_left hfinal hW0

/-- **Second-jet gap.**  For a nonzero polynomial-coefficient relation there are an exponent `E`
and a radius `ρ₀ > 0` such that, for each `0 < ρ ≤ ρ₀`, a small enough error bracket forces every
zero with `|V| ≤ ρ` to satisfy `|V| ≤ ρ / 2`. -/
theorem exists_strelitzSecondJetGap {Q : MvPolynomial (Fin 3) (Polynomial ℂ)} (hQ : Q ≠ 0) :
    ∃ E : ℕ, ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
        ∀ (z F U V : ℂ) (B : ℝ),
          MvPolynomial.eval₂ (Polynomial.evalRingHom z) ![F, U, V] Q = 0 →
          1 ≤ ‖z‖ → 1 ≤ ‖F‖ → 1 ≤ ‖U‖ → ‖U‖ ≤ B → ‖V‖ ≤ ρ →
          (1 + ‖z‖) ^ E * B ^ E / ‖F‖ + B ^ E / ‖z‖ + 1 / ‖U‖ ≤ κ →
          ‖V‖ ≤ ρ / 2 := by
  obtain ⟨s, C, E, hs, hC, hbound⟩ := exists_strelitzGap_bound hQ
  obtain ⟨q, hsq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd s hs 0
  set m := s.rootMultiplicity 0 with hm
  have hq0 : q.eval 0 ≠ 0 := fun h => hndvd (Polynomial.dvd_iff_isRoot.mpr h)
  set c₀ := ‖q.eval 0‖ with hc₀def
  have hc₀ : 0 < c₀ := norm_pos_iff.mpr hq0
  have hcont : ContinuousAt (fun v : ℂ => q.eval v) 0 := q.continuous.continuousAt
  obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.continuousAt_iff.mp hcont (c₀ / 2) (by positivity)
  refine ⟨E, min (ρ₁ / 2) 1, lt_min (by positivity) one_pos, fun ρ hρ hρ₀ => ?_⟩
  set γ := (ρ / 2) ^ m * (c₀ / 2) with hγ
  have hγ0 : 0 < γ := by positivity
  refine ⟨min 1 (γ / (2 * (C + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  intro z F U V B hrel hz hF hU hUB hV hβ
  by_contra hbig
  push Not at hbig
  have hV1 : ‖V‖ ≤ 1 := hV.trans (hρ₀.trans (min_le_right _ _))
  have hVρ₁ : ‖V‖ < ρ₁ := by
    have := hρ₀.trans (min_le_left _ _)
    linarith
  have hqV : c₀ / 2 ≤ ‖q.eval V‖ := by
    have h := hball (x := V) (by simpa [dist_zero_right] using hVρ₁)
    rw [dist_eq_norm] at h
    have htri := norm_sub_norm_le (q.eval 0) (q.eval V)
    rw [norm_sub_rev] at htri
    linarith
  have hsV : ‖s.eval V‖ = ‖V‖ ^ m * ‖q.eval V‖ := by
    rw [hsq]
    simp [Polynomial.eval_mul]
  have hlow : γ ≤ ‖s.eval V‖ := by
    rw [hsV]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbig.le m) hqV (by positivity)
      (by positivity)
  have hup := hbound z F U V B hrel hz hF hU hUB hV1
  have hβκ := hβ.trans (min_le_right _ _)
  have hCβ : C * ((1 + ‖z‖) ^ E * B ^ E / ‖F‖ + B ^ E / ‖z‖ + 1 / ‖U‖) ≤ γ / 2 := by
    calc C * ((1 + ‖z‖) ^ E * B ^ E / ‖F‖ + B ^ E / ‖z‖ + 1 / ‖U‖)
        ≤ C * (γ / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hβκ hC
      _ ≤ γ / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  linarith

end

end GaloisForLFunctions.HTGeometry
