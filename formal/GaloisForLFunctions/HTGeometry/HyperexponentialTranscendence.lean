import GaloisForLFunctions.HTGeometry.DerivationAlgebraicDescent

/-!
# Transcendence of a hyperexponential element

An element `t` with `D t = u · t` and `u` in the base field is transcendental over that field as
soon as none of the homogeneous equations `D w = k · u · w`, `k ≥ 1`, has a nonzero solution there.

Differentiating the minimal polynomial produces a second annihilating polynomial of the same degree
whose leading coefficient is `n · u`; subtracting that multiple of the minimal polynomial and using
minimality shows that each remaining coefficient solves one of the excluded homogeneous equations.
The minimal polynomial is therefore a pure power, which forces the element to vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- Shifting a derivative by one variable multiplies each coefficient by its index. -/
theorem coeff_X_mul_derivative (P : L[X]) (j : ℕ) :
    (Polynomial.X * derivative P).coeff j = (j : L) * P.coeff j := by
  cases j with
  | zero => simp
  | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast
      ring

/-- A polynomial with coefficients in a subfield, annihilating an integral element and of degree
below the minimal polynomial, vanishes. -/
theorem eq_zero_of_coeffs_mem_of_natDegree_lt (K : IntermediateField C L) {T : L} {Q : L[X]} (hQcoeff : ∀ i, Q.coeff i ∈ K) (hQeval : aeval T Q = 0)
    (hQdeg : Q.natDegree < (minpoly K T).natDegree) : Q = 0 := by
  obtain ⟨Q₀, hQ₀⟩ : ∃ Q₀ : K[X], Q₀.map (algebraMap K L) = Q := by
    have hrange : ∀ i, Q.coeff i ∈ Set.range (algebraMap K L) := fun i =>
      ⟨⟨Q.coeff i, hQcoeff i⟩, rfl⟩
    obtain ⟨Q₀, hQ₀⟩ := (Polynomial.mem_map_range (algebraMap K L)).2 hrange
    exact ⟨Q₀, by simpa only [Polynomial.coe_mapRingHom] using hQ₀⟩
  by_contra hne
  have hQ₀ne : Q₀ ≠ 0 := by
    intro hzero
    exact hne (by rw [← hQ₀, hzero, Polynomial.map_zero])
  have hQ₀eval : aeval T Q₀ = 0 := by
    have heq := hQeval
    rw [← hQ₀] at heq
    rwa [aeval_map_algebraMap] at heq
  have hle := minpoly.degree_le_of_ne_zero K T hQ₀ne hQ₀eval
  have hQ₀deg : Q₀.natDegree = Q.natDegree := by
    rw [← hQ₀]
    exact (natDegree_map_eq_of_injective (algebraMap K L).injective Q₀).symm
  have hnd : (minpoly K T).natDegree ≤ Q₀.natDegree := Polynomial.natDegree_le_natDegree hle
  omega

/-- **A hyperexponential element is transcendental.**  If `D t = u · t` with `u` in `K` and no
nonzero element of `K` solves `D w = k · u · w` for a positive integer `k`, then `t` is
transcendental over `K`. -/
theorem transcendental_of_hyperexponential (D : Derivation C L L) (K : IntermediateField C L)
    (hDK : ∀ v ∈ K, D v ∈ K) {t u : L} (ht0 : t ≠ 0) (hu : u ∈ K) (htD : D t = u * t)
    (hker : ∀ k : ℕ, 1 ≤ k → ∀ w ∈ K, D w = (k : L) * u * w → w = 0) :
    ¬ IsAlgebraic K t := by
  classical
  intro halg
  have hint : IsIntegral K t := halg.isIntegral
  set p : K[X] := minpoly K t with hp
  have hpmonic : p.Monic := minpoly.monic hint
  have hpdeg : 0 < p.natDegree := (minpoly.irreducible hint).natDegree_pos
  set P : L[X] := p.map (algebraMap K L) with hP
  have hPmonic : P.Monic := hpmonic.map _
  have hPdeg : P.natDegree = p.natDegree := hpmonic.natDegree_map _
  have hPpos : 0 < P.natDegree := by rw [hPdeg]; exact hpdeg
  have hPcoeff : ∀ i, P.coeff i ∈ K := by
    intro i
    rw [hP, coeff_map]
    exact (p.coeff i).2
  have hPeval : aeval t P = 0 := by
    rw [hP, aeval_map_algebraMap]
    exact minpoly.aeval K t
  set n : ℕ := P.natDegree with hn
  set Q : L[X] := derivMapCoeffs D P + Polynomial.C u * (Polynomial.X * derivative P)
      - Polynomial.C (u * (n : L)) * P with hQ
  -- the shifted derivative annihilates `t`
  have hQeval : aeval t Q = 0 := by
    have hchain := derivation_aeval_eq D t P
    rw [hPeval, map_zero, htD] at hchain
    rw [hQ]
    simp only [map_add, map_sub, map_mul, aeval_C, aeval_X,
      show ∀ b : L, algebraMap L L b = b from fun _ => rfl, hPeval, mul_zero, sub_zero]
    linear_combination -hchain
  -- its coefficients stay in `K`
  have hQcoeff : ∀ i, Q.coeff i ∈ K := by
    intro i
    rw [hQ, coeff_sub, coeff_add, coeff_derivMapCoeffs, coeff_C_mul, coeff_C_mul,
      coeff_X_mul_derivative]
    refine sub_mem (add_mem (hDK _ (hPcoeff i)) (mul_mem hu (mul_mem ?_ (hPcoeff i))))
      (mul_mem (mul_mem hu ?_) (hPcoeff i))
    · exact IntermediateField.natCast_mem _ i
    · exact IntermediateField.natCast_mem _ n
  -- it has degree below the minimal polynomial
  have hQtop : ∀ m : ℕ, n ≤ m → Q.coeff m = 0 := by
    intro m hm
    rw [hQ, coeff_sub, coeff_add, coeff_derivMapCoeffs, coeff_C_mul, coeff_C_mul,
      coeff_X_mul_derivative]
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rw [hPmonic.coeff_natDegree, D.map_one_eq_zero]
      ring
    · rw [coeff_eq_zero_of_natDegree_lt hlt, map_zero]
      ring
  have hQdeg : Q.natDegree < p.natDegree := by
    have hle : Q.natDegree ≤ n - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro m hm
      exact hQtop m (by omega)
    omega
  have hQ0 : Q = 0 := eq_zero_of_coeffs_mem_of_natDegree_lt K hQcoeff hQeval hQdeg
  -- every coefficient below the top solves an excluded homogeneous equation
  have hcoeffzero : ∀ j : ℕ, j < n → P.coeff j = 0 := by
    intro j hj
    have hc := congrArg (fun R : L[X] => R.coeff j) hQ0
    simp only [hQ, coeff_sub, coeff_add, coeff_derivMapCoeffs, coeff_C_mul,
      coeff_X_mul_derivative, coeff_zero] at hc
    refine hker (n - j) (by omega) (P.coeff j) (hPcoeff j) ?_
    have hcast : ((n - j : ℕ) : L) = (n : L) - (j : L) := by
      rw [Nat.cast_sub (le_of_lt hj)]
    rw [hcast]
    linear_combination hc
  -- the minimal polynomial is a pure power
  have hPeq : P = Polynomial.X ^ n := by
    ext i
    rw [Polynomial.coeff_X_pow]
    rcases lt_trichotomy i n with hlt | rfl | hgt
    · rw [hcoeffzero i hlt, if_neg (by omega)]
    · rw [hPmonic.coeff_natDegree, if_pos rfl]
    · rw [coeff_eq_zero_of_natDegree_lt hgt, if_neg (by omega)]
  rw [hPeq, map_pow, aeval_X] at hPeval
  exact ht0 (pow_eq_zero_iff (by omega : n ≠ 0) |>.mp hPeval)

end

end GaloisForLFunctions.HTGeometry
