import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Witt integrality is not purity

A curve datum (reciprocal Frobenius eigenvalues `α_i = √q β_i`) has the zeta series
`Z(X) = P(X) / ((1 − X)(1 − qX))` with `P(X) = Π_i (1 − α_i X)` (`CurveDatum.zetaSeries`).

* **Ghost components.** `X Z'(X) = Z(X) · Σ_{j ≥ 1} N_j X^j` (`CurveDatum.zetaSeries_hasGhost`):
  the Lefschetz numbers are the ghost components of `Z` in the big Witt ring, and a series with
  constant term `1` is determined by its ghost components (`eq_of_hasGhost`), so
  `Z = exp(Σ_j N_j X^j / j)`. The ghost map turns products into sums (`hasGhost_mul`): the pole
  plane `⟨H, V⟩` splits off as the factor `Z_{ℙ¹} = 1/((1 − X)(1 − qX))` with ghost components
  `1 + q^j`, and `P` is the `H¹` class with ghost components `−Σ_i α_i^j`.
* **RH is purity** of the `H¹` class, `|α_i| = √q`, which is the Hodge index on the Frobenius span
  (`CurveDatum.hodgeIndexOnSpan_iff_unitary`).
* **Integrality and purity are independent.** The golden datum over `𝔽₅` has `P = 1 − 5X + 5X²`,
  an integral zeta series with constant term `1`, integral point counts and the functional
  equation, and is not pure (`witt_integral_not_pure`). The pure datum `q = 2`, `β = (1, 1)` has
  `N₁ = 3 − 2√2 ∉ ℤ` (`pureDatum_pointCount_one_not_int`).

So the λ-ring structure of the zeta function (integrality, rationality with the pole plane split
off, functional equation) does not carry the positivity of Weil's proof; it enters only through
the Hodge index.
-/

open PowerSeries

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### The ghost relation -/

/-- `F` has ghost components `G`: `X F' = F G`. For `F(0) = 1` this says `F = exp ∫ G/X`. -/
def HasGhost (F G : ℂ⟦X⟧) : Prop := X * d⁄dX ℂ F = F * G

/-- **The ghost map is additive**: ghost components of a product add. -/
theorem hasGhost_mul {F G F' G' : ℂ⟦X⟧} (h : HasGhost F G) (h' : HasGhost F' G') :
    HasGhost (F * F') (G + G') := by
  unfold HasGhost at *
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  linear_combination F' * h + F * h'

theorem hasGhost_one : HasGhost 1 0 := by
  simp [HasGhost]

theorem hasGhost_prod {ι : Type*} (s : Finset ι) (F G : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, HasGhost (F i) (G i)) : HasGhost (∏ i ∈ s, F i) (∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasGhost_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact hasGhost_mul (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The ghost components determine the series.** Two series with the same constant term and the
same ghost components (without constant term) are equal: `n f_n = Σ_{k < n} f_k g_{n−k}`. -/
theorem eq_of_hasGhost {F F' G : ℂ⟦X⟧} (hF : HasGhost F G) (hF' : HasGhost F' G)
    (h0 : constantCoeff F = constantCoeff F') (hG : constantCoeff G = 0) : F = F' := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simpa using h0
    · have e := congrArg (coeff (m + 1)) hF
      have e' := congrArg (coeff (m + 1)) hF'
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mul] at e e'
      have hsum : ∑ p ∈ Finset.antidiagonal (m + 1), coeff p.1 F * coeff p.2 G =
          ∑ p ∈ Finset.antidiagonal (m + 1), coeff p.1 F' * coeff p.2 G := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_antidiagonal] at hp
        rcases Nat.eq_zero_or_pos p.2 with h2 | h2
        · rw [h2, coeff_zero_eq_constantCoeff_apply, hG, mul_zero, mul_zero]
        · rw [ih p.1 (by omega)]
      have hne : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have := e.trans (hsum.trans e'.symm)
      exact mul_right_cancel₀ hne this

/-! ### Geometric series -/

/-- The geometric series `Σ_n a^n X^n = (1 − aX)⁻¹`. -/
def geom (a : ℂ) : ℂ⟦X⟧ := mk fun n => a ^ n

/-- The tail `Σ_{n ≥ 1} a^n X^n = aX/(1 − aX)`. -/
def geomTail (a : ℂ) : ℂ⟦X⟧ := mk fun n => if n = 0 then 0 else a ^ n

theorem C_mul_X_mul_geom (a : ℂ) : C a * X * geom a = geomTail a := by
  ext n
  rcases n with _ | n
  · simp [geomTail, mul_assoc]
  · rw [mul_assoc, coeff_C_mul, coeff_succ_X_mul]
    simp [geom, geomTail, pow_succ]
    ring

theorem one_sub_mul_geom (a : ℂ) : (1 - C a * X) * geom a = 1 := by
  rw [sub_mul, one_mul, C_mul_X_mul_geom]
  ext n
  rcases n with _ | n <;> simp [geom, geomTail, coeff_one]

/-- The linear factor `1 − aX` has ghost components `−Σ_{n≥1} a^n X^n`. -/
theorem hasGhost_one_sub (a : ℂ) : HasGhost (1 - C a * X) (-geomTail a) := by
  unfold HasGhost
  have hd : d⁄dX ℂ (1 - C a * X) = -C a := by
    rw [map_sub, Derivation.map_one_eq_zero, Derivation.leibniz, derivative_C, derivative_X,
      smul_eq_mul, smul_eq_mul]
    ring
  rw [hd, ← C_mul_X_mul_geom]
  linear_combination (C a * X) * one_sub_mul_geom a

/-- The pole factor `(1 − aX)⁻¹` has ghost components `Σ_{n≥1} a^n X^n`. -/
theorem hasGhost_geom (a : ℂ) : HasGhost (geom a) (geomTail a) := by
  unfold HasGhost
  have hL := hasGhost_one_sub a
  unfold HasGhost at hL
  have hprod := one_sub_mul_geom a
  have hd : d⁄dX ℂ ((1 - C a * X) * geom a) = 0 := by
    rw [hprod, Derivation.map_one_eq_zero]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hd
  linear_combination (geom a * X) * hd - geom a ^ 2 * hL -
    (X * d⁄dX ℂ (geom a) - geom a * geomTail a) * hprod

/-! ### The zeta series of a curve datum -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The reciprocal Frobenius eigenvalues `α_i = √q β_i`. -/
def alpha (i : ι) : ℂ := (D.sqrtq : ℂ) * D.β i

/-- The `H¹` polynomial `P(X) = Π_i (1 − α_i X)`. -/
def hOnePoly : ℂ⟦X⟧ := ∏ i, (1 - C (D.alpha i) * X)

/-- The zeta series of the pole plane, `Z_{ℙ¹} = 1/((1 − X)(1 − qX))`. -/
def poleZeta : ℂ⟦X⟧ := geom 1 * geom (D.q : ℂ)

/-- The zeta series `Z(X) = P(X)/((1 − X)(1 − qX))`. -/
def zetaSeries : ℂ⟦X⟧ := D.poleZeta * D.hOnePoly

/-- The ghost series `Σ_{j ≥ 1} N_j X^j` of the Lefschetz numbers. -/
def ghostSeries : ℂ⟦X⟧ := PowerSeries.mk fun j => if j = 0 then 0 else (D.pointCount j : ℂ)

theorem constantCoeff_zetaSeries : constantCoeff D.zetaSeries = 1 := by
  simp [zetaSeries, poleZeta, hOnePoly, geom, map_prod]

/-- **Ghost components of the zeta series are the Lefschetz numbers**: `X Z' = Z · Σ_j N_j X^j`,
the pole plane contributing `1 + q^j` and the `H¹` class `−Σ_i α_i^j`. -/
theorem zetaSeries_hasGhost : HasGhost D.zetaSeries D.ghostSeries := by
  have h := hasGhost_mul (hasGhost_mul (hasGhost_geom 1) (hasGhost_geom (D.q : ℂ)))
    (hasGhost_prod Finset.univ (fun i => 1 - C (D.alpha i) * X) (fun i => -geomTail (D.alpha i))
      fun i _ => hasGhost_one_sub _)
  have hG : D.ghostSeries = geomTail 1 + geomTail (D.q : ℂ) +
      ∑ i, -geomTail (D.alpha i) := by
    ext j
    simp only [ghostSeries, geomTail, coeff_mk, map_add, map_sum, map_neg]
    rcases j with _ | j
    · simp
    · simp only [Nat.succ_ne_zero, if_false, one_pow, pointCount, alpha, mul_pow,
        Finset.sum_neg_distrib, ← Finset.mul_sum]
      rw [← powerSum, D.powerSum_eq_trace]
      push_cast
      ring
  rw [hG]
  exact h

/-- **The zeta series is determined by the point counts.** -/
theorem zetaSeries_eq_of_pointCount {κ : Type*} [Fintype κ] (D' : CurveDatum κ)
    (h : ∀ j, 1 ≤ j → D.pointCount j = D'.pointCount j) : D.zetaSeries = D'.zetaSeries := by
  have hG : D.ghostSeries = D'.ghostSeries := by
    ext j
    simp only [ghostSeries, coeff_mk]
    split_ifs with hj
    · rfl
    · rw [h j (Nat.one_le_iff_ne_zero.mpr hj)]
  refine eq_of_hasGhost D.zetaSeries_hasGhost (hG ▸ D'.zetaSeries_hasGhost) ?_ ?_
  · rw [constantCoeff_zetaSeries, constantCoeff_zetaSeries]
  · simp [ghostSeries]

end CurveDatum

/-! ### Integral but impure, pure but not integral -/

open Real in
theorem goldenDatum_alpha_sum :
    goldenDatum.alpha 0 + goldenDatum.alpha 1 = 5 := by
  have h := sqrt_five_pow_sum 1
  have hs : goldenDatum.sqrtq = √5 := rfl
  simp only [CurveDatum.alpha, hs]
  show (√5 : ℂ) * ((goldenRatio : ℝ) : ℂ) + (√5 : ℂ) * ((goldenRatio⁻¹ : ℝ) : ℂ) = 5
  rw [pow_one, pow_one] at h
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h]
  norm_num [goldenLucas]

open Real in
theorem goldenDatum_alpha_mul :
    goldenDatum.alpha 0 * goldenDatum.alpha 1 = 5 := by
  have hs : goldenDatum.sqrtq = √5 := rfl
  simp only [CurveDatum.alpha, hs]
  show (√5 : ℂ) * ((goldenRatio : ℝ) : ℂ) * ((√5 : ℂ) * ((goldenRatio⁻¹ : ℝ) : ℂ)) = 5
  have h5 : (√5 : ℝ) * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hφ : goldenRatio * goldenRatio⁻¹ = 1 := mul_inv_cancel₀ goldenRatio_ne_zero
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    show √5 * goldenRatio * (√5 * goldenRatio⁻¹) = (√5 * √5) * (goldenRatio * goldenRatio⁻¹)
      by ring, h5, hφ]
  norm_num

/-- The golden datum has `P(X) = 1 − 5X + 5X²`. -/
theorem goldenDatum_hOnePoly : goldenDatum.hOnePoly = 1 - C 5 * X + C 5 * X ^ 2 := by
  rw [CurveDatum.hOnePoly, Fin.prod_univ_two]
  calc (1 - C (goldenDatum.alpha 0) * X) * (1 - C (goldenDatum.alpha 1) * X)
      = 1 - C (goldenDatum.alpha 0 + goldenDatum.alpha 1) * X +
          C (goldenDatum.alpha 0 * goldenDatum.alpha 1) * X ^ 2 := by
        simp only [map_add, map_mul]; ring
    _ = 1 - C 5 * X + C 5 * X ^ 2 := by rw [goldenDatum_alpha_sum, goldenDatum_alpha_mul]

theorem map_mk_pow (a : ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (mk fun n => a ^ n) = geom (a : ℂ) := by
  ext n
  simp [geom]

/-- **The golden zeta series is integral**: it is the image of a series in `1 + Xℤ⟦X⟧`. -/
theorem goldenDatum_zetaSeries_integral :
    ∃ Zℤ : ℤ⟦X⟧, constantCoeff Zℤ = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Zℤ = goldenDatum.zetaSeries := by
  refine ⟨(mk fun n => (1 : ℤ) ^ n) * (mk fun n => (5 : ℤ) ^ n) * (1 - C 5 * X + C 5 * X ^ 2),
    by simp, ?_⟩
  have hq : ((goldenDatum.q : ℝ) : ℂ) = ((5 : ℤ) : ℂ) := by
    show ((5 : ℝ) : ℂ) = ((5 : ℤ) : ℂ)
    norm_num
  rw [CurveDatum.zetaSeries, CurveDatum.poleZeta, goldenDatum_hOnePoly, map_mul, map_mul,
    map_mk_pow, map_mk_pow, Int.cast_one, hq]
  congr 1
  rw [map_add, map_sub, map_one, map_mul, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  simp

/-- **Witt integrality is not purity.** The golden datum has an integral zeta series with constant
term `1`, integral point counts and the functional equation `β ↦ β⁻¹`, and its eigenvalues are off
the circle (equivalently, the Hodge index fails on its Frobenius span). -/
theorem witt_integral_not_pure :
    (∃ Zℤ : ℤ⟦X⟧, constantCoeff Zℤ = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Zℤ = goldenDatum.zetaSeries) ∧
    (∀ j, ∃ n : ℤ, goldenDatum.pointCount j = n) ∧
    (∀ i, goldenDatum.β (goldenDatum.fePerm i) * goldenDatum.β i = 1) ∧
    ¬ ∀ i, ‖goldenDatum.β i‖ = 1 :=
  ⟨goldenDatum_zetaSeries_integral, fun j => ⟨_, goldenDatum_pointCount_eq j⟩,
    goldenDatum.β_fePerm, goldenDatum_not_unitary⟩

/-- The pure datum `q = 2`, `β = (1, 1)`. -/
def pureDatum : CurveDatum (Fin 2) where
  q := 2
  one_lt_q := by norm_num
  β := ![1, 1]
  conjPerm := Equiv.refl _
  β_conjPerm i := by fin_cases i <;> simp
  fePerm := Equiv.refl _
  β_fePerm i := by fin_cases i <;> simp

theorem pureDatum_unitary : ∀ i, ‖pureDatum.β i‖ = 1 := by
  intro i
  fin_cases i <;> simp [pureDatum]

/-- **Purity is not integrality**: the pure datum has `N₁ = 3 − 2√2 ∉ ℤ`. -/
theorem pureDatum_pointCount_one_not_int : ¬ ∃ n : ℤ, pureDatum.pointCount 1 = n := by
  rintro ⟨n, hn⟩
  have htr : pureDatum.trace 1 = 2 := by
    simp [CurveDatum.trace, CurveDatum.powerSum, pureDatum, Fin.sum_univ_two]
    norm_num
  have hs : pureDatum.sqrtq = Real.sqrt 2 := rfl
  have hq : pureDatum.q = 2 := rfl
  rw [CurveDatum.pointCount, htr, hs, hq] at hn
  apply irrational_sqrt_two
  refine ⟨((3 - n) / 2 : ℚ), ?_⟩
  push_cast
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
