import GaloisForLFunctions.RHTower.StepanovHyperelliptic

/-!
# The cubic Stepanov polynomial is independent

Stepanov's method for a character of order three of a finite field `E`, `|E| = Q = 3N + 1`, uses the
auxiliary polynomial `Σ_j (r_j + s_j h^N + t_j h^{2N}) X^{Qj}`, one level for each value of
`h(x)^N`. It vanishes only for vanishing data of low degree (`cubic_stepanov_independence`).

* **The norm form** (`norm_form_eq_zero`): `A₀ + A₁g + A₂g² = 0` forces
  `A₀³ + A₁³g³ + A₂³g⁶ − 3A₀A₁A₂g³ = 0`, by `x³ + y³ + z³ − 3xyz = (x + y + z)(x² + y² + z² − xy − yz − zx)`.
* With `g = h^N` and `h g³ = h^Q = h(X^Q)` the identity times `h²` is the value at `Y = X^Q` of
  `h(X)²A₀³ + h(X)h(Y)A₁³ + h(Y)²A₂³ − 3h(X)h(Y)A₀A₁A₂`, whose coefficients in `Y` have degree below
  `Q`; so it vanishes in `E[X][Y]`.
* **Cubic descent** (`cubic_descent`): for `h` squarefree and nonconstant this forces
  `A₀ = A₁ = A₂ = 0`. An irreducible factor `π` of `h(X)` divides `A₂`, then `A₁`, then `A₀`, and the
  quotients satisfy the same equation (`cubic_C_pow_dvd_forall`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open RHTower.Stepanov

/-- The norm form of `A₀ + A₁g + A₂g²` vanishes with it. -/
theorem norm_form_eq_zero {R : Type*} [CommRing R] {A₀ A₁ A₂ g : R}
    (h : A₀ + A₁ * g + A₂ * g ^ 2 = 0) :
    A₀ ^ 3 + A₁ ^ 3 * g ^ 3 + A₂ ^ 3 * g ^ 6 - 3 * (A₀ * A₁ * A₂) * g ^ 3 = 0 := by
  have e : A₀ ^ 3 + A₁ ^ 3 * g ^ 3 + A₂ ^ 3 * g ^ 6 - 3 * (A₀ * A₁ * A₂) * g ^ 3 =
      (A₀ + A₁ * g + A₂ * g ^ 2) * (A₀ ^ 2 + A₁ ^ 2 * g ^ 2 + A₂ ^ 2 * g ^ 4 - A₀ * A₁ * g -
        A₁ * A₂ * g ^ 3 - A₀ * A₂ * g ^ 2) := by ring
  rw [e, h, zero_mul]

variable {E : Type*} [Field E]

/-- **One step of cubic descent, iterated.** If `h = πh₁` with `π` prime and `π ∤ h₁`, every solution
of `h(X)²A₀³ + h(X)h(Y)A₁³ + h(Y)²A₂³ = 3h(X)h(Y)A₀A₁A₂` is divisible by every power of `π(X)`. -/
theorem cubic_C_pow_dvd_forall {π h h1 : E[X]} (hπ : Prime π) (hπh : π * h1 = h) (hπh1 : ¬ π ∣ h1)
    (hh : h ≠ 0) :
    ∀ m : ℕ, ∀ A₀ A₁ A₂ : E[X][X],
      C h ^ 2 * A₀ ^ 3 + C h * h.map C * A₁ ^ 3 + h.map C ^ 2 * A₂ ^ 3 -
          3 * (C h * h.map C) * (A₀ * A₁ * A₂) = 0 →
        C π ^ m ∣ A₀ ∧ C π ^ m ∣ A₁ ∧ C π ^ m ∣ A₂ := by
  have hP : Prime (C π : E[X][X]) := Polynomial.prime_C_iff.mpr hπ
  have hP0 : (C π : E[X][X]) ≠ 0 := hP.ne_zero
  have hH : ¬ (C π : E[X][X]) ∣ h.map C := not_C_dvd_map_C hπ.not_unit hh
  have hG : ¬ (C π : E[X][X]) ∣ C h1 := by
    intro hd
    have := (C_dvd_iff_dvd_coeff _ _).mp hd 0
    rw [coeff_C_zero] at this
    exact hπh1 this
  have hF : (C h : E[X][X]) = C π * C h1 := by rw [← C_mul, hπh]
  intro m
  induction m with
  | zero => intro _ _ _ _; simp
  | succ m ih =>
    intro A₀ A₁ A₂ hEq
    rw [hF] at hEq
    obtain ⟨B₂, rfl⟩ : (C π : E[X][X]) ∣ A₂ := by
      have hd : (C π : E[X][X]) ∣ h.map C ^ 2 * A₂ ^ 3 :=
        ⟨-(C π * C h1 ^ 2 * A₀ ^ 3 + C h1 * h.map C * A₁ ^ 3 -
          3 * (C h1 * h.map C) * (A₀ * A₁ * A₂)), by linear_combination hEq⟩
      rcases hP.dvd_or_dvd hd with h' | h'
      · exact absurd (hP.dvd_of_dvd_pow h') hH
      · exact hP.dvd_of_dvd_pow h'
    have e2 : C π * C h1 ^ 2 * A₀ ^ 3 + C h1 * h.map C * A₁ ^ 3 + C π ^ 2 * h.map C ^ 2 * B₂ ^ 3 -
        3 * C π * (C h1 * h.map C) * (A₀ * A₁ * B₂) = 0 := by
      have : C π * (C π * C h1 ^ 2 * A₀ ^ 3 + C h1 * h.map C * A₁ ^ 3 +
          C π ^ 2 * h.map C ^ 2 * B₂ ^ 3 - 3 * C π * (C h1 * h.map C) * (A₀ * A₁ * B₂)) = 0 := by
        linear_combination hEq
      exact (mul_eq_zero.mp this).resolve_left hP0
    obtain ⟨B₁, rfl⟩ : (C π : E[X][X]) ∣ A₁ := by
      have hd : (C π : E[X][X]) ∣ (C h1 * h.map C) * A₁ ^ 3 :=
        ⟨-(C h1 ^ 2 * A₀ ^ 3 + C π * h.map C ^ 2 * B₂ ^ 3 -
          3 * (C h1 * h.map C) * (A₀ * A₁ * B₂)), by linear_combination e2⟩
      rcases hP.dvd_or_dvd hd with h' | h'
      · rcases hP.dvd_or_dvd h' with h'' | h''
        · exact absurd h'' hG
        · exact absurd h'' hH
      · exact hP.dvd_of_dvd_pow h'
    have e3 : C h1 ^ 2 * A₀ ^ 3 + C π ^ 2 * (C h1 * h.map C) * B₁ ^ 3 + C π * h.map C ^ 2 * B₂ ^ 3 -
        3 * C π * (C h1 * h.map C) * (A₀ * B₁ * B₂) = 0 := by
      have : C π * (C h1 ^ 2 * A₀ ^ 3 + C π ^ 2 * (C h1 * h.map C) * B₁ ^ 3 +
          C π * h.map C ^ 2 * B₂ ^ 3 - 3 * C π * (C h1 * h.map C) * (A₀ * B₁ * B₂)) = 0 := by
        linear_combination e2
      exact (mul_eq_zero.mp this).resolve_left hP0
    obtain ⟨B₀, rfl⟩ : (C π : E[X][X]) ∣ A₀ := by
      have hd : (C π : E[X][X]) ∣ C h1 ^ 2 * A₀ ^ 3 :=
        ⟨-(C π * (C h1 * h.map C) * B₁ ^ 3 + h.map C ^ 2 * B₂ ^ 3 -
          3 * (C h1 * h.map C) * (A₀ * B₁ * B₂)), by linear_combination e3⟩
      rcases hP.dvd_or_dvd hd with h' | h'
      · exact absurd (hP.dvd_of_dvd_pow h') hG
      · exact hP.dvd_of_dvd_pow h'
    have e4 : (C π * C h1) ^ 2 * B₀ ^ 3 + C π * C h1 * h.map C * B₁ ^ 3 + h.map C ^ 2 * B₂ ^ 3 -
        3 * (C π * C h1 * h.map C) * (B₀ * B₁ * B₂) = 0 := by
      have : C π * ((C π * C h1) ^ 2 * B₀ ^ 3 + C π * C h1 * h.map C * B₁ ^ 3 +
          h.map C ^ 2 * B₂ ^ 3 - 3 * (C π * C h1 * h.map C) * (B₀ * B₁ * B₂)) = 0 := by
        linear_combination e3
      exact (mul_eq_zero.mp this).resolve_left hP0
    rw [← hF] at e4
    obtain ⟨d₀, d₁, d₂⟩ := ih B₀ B₁ B₂ e4
    rw [pow_succ']
    exact ⟨mul_dvd_mul_left _ d₀, mul_dvd_mul_left _ d₁, mul_dvd_mul_left _ d₂⟩

/-- **Cubic descent.** For squarefree nonconstant `h`,
`h(X)²A₀³ + h(X)h(Y)A₁³ + h(Y)²A₂³ = 3h(X)h(Y)A₀A₁A₂` in `E[X][Y]` forces `A₀ = A₁ = A₂ = 0`. -/
theorem cubic_descent {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree) {A₀ A₁ A₂ : E[X][X]}
    (hA : C h ^ 2 * A₀ ^ 3 + C h * h.map C * A₁ ^ 3 + h.map C ^ 2 * A₂ ^ 3 -
      3 * (C h * h.map C) * (A₀ * A₁ * A₂) = 0) : A₀ = 0 ∧ A₁ = 0 ∧ A₂ = 0 := by
  have hh : h ≠ 0 := by rintro rfl; simp at hdeg
  have hnu : ¬ IsUnit h := by
    intro hu
    rw [Polynomial.isUnit_iff_degree_eq_zero] at hu
    have h0 : h.natDegree = 0 := natDegree_eq_of_degree_eq_some hu
    omega
  obtain ⟨π, hπirr, h1, hh1⟩ := WfDvdMonoid.exists_irreducible_factor hnu hh
  have hπh1 : ¬ π ∣ h1 := by
    rintro ⟨h2, rfl⟩
    exact hπirr.not_isUnit (hsq π ⟨h2, by rw [hh1]; ring⟩)
  have hall := fun m => cubic_C_pow_dvd_forall hπirr.prime hh1.symm hπh1 hh m A₀ A₁ A₂ hA
  exact ⟨eq_zero_of_forall_C_pow_dvd hπirr.not_isUnit hπirr.ne_zero A₀ fun m => (hall m).1,
    eq_zero_of_forall_C_pow_dvd hπirr.not_isUnit hπirr.ne_zero A₁ fun m => (hall m).2.1,
    eq_zero_of_forall_C_pow_dvd hπirr.not_isUnit hπirr.ne_zero A₂ fun m => (hall m).2.2⟩

/-- The bivariate lift `Σ_j u_j(X) Y^j`. -/
noncomputable def bivariate {J : ℕ} (u : Fin J → E[X]) : E[X][X] :=
  ∑ j : Fin J, monomial (j : ℕ) (u j)

theorem bivariate_coeff_natDegree_le {J K : ℕ} (u : Fin J → E[X]) (hu : ∀ j, (u j).natDegree < K)
    (m : ℕ) : ((bivariate u).coeff m).natDegree ≤ K - 1 := by
  simp only [bivariate, finsetSum_coeff, coeff_monomial]
  apply natDegree_sum_le_of_forall_le
  intro j _
  split_ifs
  · have := hu j; omega
  · simp

theorem eval_bivariate {J Q : ℕ} (u : Fin J → E[X]) :
    (bivariate u).eval (X ^ Q) = ∑ j, u j * (X ^ Q) ^ (j : ℕ) := by
  simp [bivariate, eval_finsetSum]

theorem eq_zero_of_bivariate_eq_zero {J : ℕ} {u : Fin J → E[X]} (h : bivariate u = 0) (j : Fin J) :
    u j = 0 := by
  have := congrArg (fun P => P.coeff (j : ℕ)) h
  simpa [bivariate, finsetSum_coeff, coeff_monomial, Fin.val_inj] using this

/-- Coefficient degrees of powers of bivariate polynomials. -/
theorem coeff_pow_natDegree_le {P : E[X][X]} {a : ℕ} (hP : ∀ j, (P.coeff j).natDegree ≤ a) :
    ∀ (n j : ℕ), ((P ^ n).coeff j).natDegree ≤ n * a := by
  intro n
  induction n with
  | zero =>
    intro j
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    intro j
    rw [pow_succ]
    exact (coeff_mul_natDegree_le ih hP j).trans (by rw [Nat.succ_mul])

theorem coeff_C_natDegree_le (g : E[X]) (j : ℕ) : ((C g : E[X][X]).coeff j).natDegree ≤ g.natDegree := by
  rw [coeff_C]
  split_ifs <;> simp

theorem coeff_map_C_natDegree_le (g : E[X]) (j : ℕ) : ((g.map C : E[X][X]).coeff j).natDegree ≤ 0 := by
  rw [coeff_map]
  simp

variable [Fintype E]

/-- **Cubic Stepanov independence.** Over a finite field with `|E| = Q = 3N + 1`, if
`Σ_j (r_j + s_j h^N + t_j h^{2N}) X^{Qj} = 0` with `deg r_j, deg s_j, deg t_j < K`,
`3(K − 1) + 2 deg h < Q` and `h` squarefree nonconstant, then all `r_j, s_j, t_j` vanish. -/
theorem cubic_stepanov_independence {h : E[X]} (hsq : Squarefree h) (hdeg : 1 ≤ h.natDegree)
    {N K J : ℕ} (hQ : Fintype.card E = 3 * N + 1)
    (hK : 3 * (K - 1) + 2 * h.natDegree < Fintype.card E)
    (r s t : Fin J → E[X]) (hr : ∀ j, (r j).natDegree < K) (hs : ∀ j, (s j).natDegree < K)
    (ht : ∀ j, (t j).natDegree < K)
    (hsum : ∑ j, (r j + s j * h ^ N + t j * h ^ (2 * N)) * (X ^ Fintype.card E) ^ (j : ℕ) = 0) :
    ∀ j, r j = 0 ∧ s j = 0 ∧ t j = 0 := by
  set Q := Fintype.card E
  have hrel : (bivariate r).eval (X ^ Q) + (bivariate s).eval (X ^ Q) * h ^ N +
      (bivariate t).eval (X ^ Q) * (h ^ N) ^ 2 = 0 := by
    rw [eval_bivariate, eval_bivariate, eval_bivariate, ← hsum, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hnorm := norm_form_eq_zero hrel
  have hg3 : h * (h ^ N) ^ 3 = h ^ Q := by rw [hQ]; ring
  have hkey : h ^ 2 * (bivariate r).eval (X ^ Q) ^ 3 +
      h * h ^ Q * (bivariate s).eval (X ^ Q) ^ 3 + (h ^ Q) ^ 2 * (bivariate t).eval (X ^ Q) ^ 3 -
      3 * (h * h ^ Q) * ((bivariate r).eval (X ^ Q) * (bivariate s).eval (X ^ Q) *
        (bivariate t).eval (X ^ Q)) = 0 := by
    rw [← hg3]
    linear_combination h ^ 2 * hnorm
  have hmapeval : (h.map (C : E →+* E[X])).eval (X ^ Q) = h ^ Q := by
    rw [eval_map, ← coe_expand, FiniteField.expand_card]
  have hDif : (C h ^ 2 * bivariate r ^ 3 + C h * h.map C * bivariate s ^ 3 +
      h.map C ^ 2 * bivariate t ^ 3 -
      3 * (C h * h.map C) * (bivariate r * bivariate s * bivariate t)).eval (X ^ Q) = 0 := by
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_C, hmapeval, eval_ofNat]
    linear_combination hkey
  have hcr := bivariate_coeff_natDegree_le r hr
  have hcs := bivariate_coeff_natDegree_le s hs
  have hct := bivariate_coeff_natDegree_le t ht
  set D := h.natDegree
  have hdegDif : ∀ m, ((C h ^ 2 * bivariate r ^ 3 + C h * h.map C * bivariate s ^ 3 +
      h.map C ^ 2 * bivariate t ^ 3 -
      3 * (C h * h.map C) * (bivariate r * bivariate s * bivariate t)).coeff m).natDegree < Q := by
    intro m
    have hCh : ∀ j, ((C h : E[X][X]).coeff j).natDegree ≤ D := coeff_C_natDegree_le h
    have hH : ∀ j, ((h.map C : E[X][X]).coeff j).natDegree ≤ 0 := coeff_map_C_natDegree_le h
    have h3 : ∀ j, ((3 : E[X][X]).coeff j).natDegree ≤ 0 := by
      intro j
      rw [← map_ofNat (C : E[X] →+* E[X][X]) 3, coeff_C]
      split_ifs <;> simp
    have t1 : ((C h ^ 2 * bivariate r ^ 3).coeff m).natDegree ≤ 2 * D + 3 * (K - 1) :=
      coeff_mul_natDegree_le (coeff_pow_natDegree_le hCh 2) (coeff_pow_natDegree_le hcr 3) m
    have t2 : ((C h * h.map C * bivariate s ^ 3).coeff m).natDegree ≤ D + 0 + 3 * (K - 1) :=
      coeff_mul_natDegree_le (coeff_mul_natDegree_le hCh hH) (coeff_pow_natDegree_le hcs 3) m
    have t3 : ((h.map C ^ 2 * bivariate t ^ 3).coeff m).natDegree ≤ 2 * 0 + 3 * (K - 1) :=
      coeff_mul_natDegree_le (coeff_pow_natDegree_le hH 2) (coeff_pow_natDegree_le hct 3) m
    have t4 : ((3 * (C h * h.map C) * (bivariate r * bivariate s * bivariate t)).coeff m).natDegree ≤
        0 + (D + 0) + ((K - 1) + (K - 1) + (K - 1)) :=
      coeff_mul_natDegree_le (coeff_mul_natDegree_le h3 (coeff_mul_natDegree_le hCh hH))
        (coeff_mul_natDegree_le (coeff_mul_natDegree_le hcr hcs) hct) m
    simp only [coeff_sub, coeff_add]
    refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
    refine max_lt (lt_of_le_of_lt (natDegree_add_le _ _) (max_lt
      (lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (by omega) (by omega))) (by omega))) (by omega)
  have hDif0 := eq_zero_of_eval_X_pow _ hdegDif hDif
  obtain ⟨h0, h1, h2⟩ := cubic_descent hsq hdeg hDif0
  exact fun j => ⟨eq_zero_of_bivariate_eq_zero h0 j, eq_zero_of_bivariate_eq_zero h1 j,
    eq_zero_of_bivariate_eq_zero h2 j⟩

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
