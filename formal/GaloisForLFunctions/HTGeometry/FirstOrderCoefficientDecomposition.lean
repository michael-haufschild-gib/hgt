import GaloisForLFunctions.HTGeometry.FirstOrderMvPoly
import GaloisForLFunctions.HTGeometry.NewtonWeightPositiveOrder

/-!
# Polynomial-coefficient monomial rows for first-order equations

Every polynomial in the three coordinates `(z, f, f′)` can be regrouped canonically by the
exponents of `(f, f′)`.  The remaining exponent becomes a one-variable polynomial coefficient in
`z`.  This is the exact compiler from `DifferentiallyAlgebraicOfOrder f 1` to the finite row format
consumed by the Newton-face and Wiman--Valiron modules.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exponents of the value and first-derivative coordinates of a three-variable monomial. -/
def firstOrderExponent (m : Fin 3 →₀ ℕ) : ℕ × ℕ := (m 1, m 2)

/-- Finite set of value/derivative exponent pairs occurring in a differential polynomial. -/
def firstOrderSupport (P : MvPolynomial (Fin 3) ℂ) : Finset (ℕ × ℕ) :=
  P.support.image firstOrderExponent

/-- Polynomial in `z` obtained by collecting every monomial with the same `(f,f′)` exponents. -/
def firstOrderCoeff (P : MvPolynomial (Fin 3) ℂ) (p : ℕ × ℕ) : Polynomial ℂ :=
  ∑ m ∈ P.support with firstOrderExponent m = p,
    Polynomial.monomial (m 0) (P.coeff m)

/-- Regrouping preserves evaluation exactly. -/
theorem eval_firstOrderSupport (P : MvPolynomial (Fin 3) ℂ) (z u v : ℂ) :
    ∑ p ∈ firstOrderSupport P,
        (firstOrderCoeff P p).eval z * u ^ p.1 * v ^ p.2 =
      MvPolynomial.eval ![z, u, v] P := by
  classical
  rw [MvPolynomial.eval_eq]
  calc
    ∑ p ∈ firstOrderSupport P,
        (firstOrderCoeff P p).eval z * u ^ p.1 * v ^ p.2 =
        ∑ p ∈ firstOrderSupport P,
          ∑ m ∈ P.support with firstOrderExponent m = p,
            P.coeff m * z ^ m 0 * u ^ m 1 * v ^ m 2 := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [firstOrderCoeff, Polynomial.eval_finsetSum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hmp : firstOrderExponent m = p := (Finset.mem_filter.mp hm).2
      have h1 : m 1 = p.1 := congrArg Prod.fst hmp
      have h2 : m 2 = p.2 := congrArg Prod.snd hmp
      rw [Polynomial.eval_monomial, ← h1, ← h2]
    _ = ∑ m ∈ P.support, P.coeff m * z ^ m 0 * u ^ m 1 * v ^ m 2 := by
      exact Finset.sum_fiberwise_of_maps_to
        (s := P.support) (t := firstOrderSupport P)
        (g := firstOrderExponent)
        (fun m hm => Finset.mem_image.mpr ⟨m, hm, rfl⟩)
        (fun m => P.coeff m * z ^ m 0 * u ^ m 1 * v ^ m 2)
    _ = ∑ d ∈ P.support, P.coeff d * ∏ i ∈ d.support, ![z, u, v] i ^ d i := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hprod : ∏ i ∈ m.support, ![z, u, v] i ^ m i =
          z ^ m 0 * u ^ m 1 * v ^ m 2 := by
        change (m.prod fun i e => ![z, u, v] i ^ e) = _
        rw [Finsupp.prod_fintype m (fun i e => ![z, u, v] i ^ e)
          (by intro i; simp), Fin.prod_univ_three]
        rfl
      rw [hprod]
      ring

/-- Value/derivative total degree is bounded by total degree of original differential polynomial. -/
theorem firstOrderSupport_degree_le (P : MvPolynomial (Fin 3) ℂ) {p : ℕ × ℕ}
    (hp : p ∈ firstOrderSupport P) : p.1 + p.2 ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, hmp⟩ := Finset.mem_image.mp hp
  have htotal := MvPolynomial.le_totalDegree hm
  have hsum : m.sum (fun _ e => e) = m 0 + m 1 + m 2 := by
    rw [Finsupp.sum_fintype m (fun _ e => e) (by intro i; rfl), Fin.sum_univ_three]
  rw [hsum] at htotal
  have hp1 : p.1 = m 1 := by rw [← hmp]; rfl
  have hp2 : p.2 = m 2 := by rw [← hmp]; rfl
  rw [hp1, hp2]
  omega

/-- A nonzero differential polynomial leaves at least one nonzero collected coefficient. -/
theorem exists_nonzero_firstOrderCoeff {P : MvPolynomial (Fin 3) ℂ} (hP : P ≠ 0) :
    ∃ p ∈ firstOrderSupport P, firstOrderCoeff P p ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hP
  apply MvPolynomial.funext
  intro x
  have hx : (![x 0, x 1, x 2] : Fin 3 → ℂ) = x := by
    funext i
    fin_cases i <;> rfl
  rw [← hx, ← eval_firstOrderSupport]
  exact Finset.sum_eq_zero (fun p hp => by rw [hcon p hp]; simp)

open GaloisForLFunctions

/-- **Canonical finite row for an arbitrary order-one ADE.**  No nondegeneracy or Newton-face
hypothesis is introduced: some collected polynomial coefficient is nonzero, all exponent pairs are
bounded by total degree of the original relation, and the row vanishes identically on `(f,f′)`. -/
theorem exists_firstOrderRelation_of_differentiallyAlgebraicOfOrder_one {f : ℂ → ℂ}
    (h : DifferentiallyAlgebraicOfOrder f 1) :
    ∃ (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ),
      (∃ p ∈ S, A p ≠ 0) ∧
      (∀ p ∈ S, p.1 + p.2 ≤ d) ∧
      ∀ z : ℂ, ∑ p ∈ S, (A p).eval z * (f z) ^ p.1 * (deriv f z) ^ p.2 = 0 := by
  classical
  obtain ⟨P, hP, hrel⟩ := h
  refine ⟨firstOrderSupport P, firstOrderCoeff P, P.totalDegree,
    exists_nonzero_firstOrderCoeff hP, ?_, ?_⟩
  · intro p hp
    exact firstOrderSupport_degree_le P hp
  · intro z
    rw [eval_firstOrderSupport]
    have hvec : (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) =
        (![z, f z, deriv f z] : Fin 3 → ℂ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rw [Fin.cons_succ]
        fin_cases j <;> simp [iteratedDeriv_zero, iteratedDeriv_one]
    rw [← hvec]
    exact hrel z

end

end GaloisForLFunctions.HTGeometry

open Filter Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- **Positive central-index order for every first-order ADE.**  Multiplying the canonical row by
`z^d`, where `d` is its maximal value/derivative total degree, makes every nonzero top coefficient
coefficient-heavy.  The general Newton-face theorem then gives a power lower bound for the central
index at arbitrarily large radii. -/
theorem exists_radius_le_centralIndex_pow_of_order_one
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1) :
    ∃ (d : ℕ) (C : ℝ), 0 < C ∧ ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧
      r ≤ C * ((centralIndex a r : ℕ) : ℝ) ^ d := by
  classical
  obtain ⟨S, A, -, hne, -, hrel⟩ :=
    exists_firstOrderRelation_of_differentiallyAlgebraicOfOrder_one hDA
  set S' : Finset (ℕ × ℕ) := S.filter (fun p => A p ≠ 0) with hS'
  have hS'ne : S'.Nonempty := by
    obtain ⟨p, hpS, hpA⟩ := hne
    exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hpA⟩⟩
  obtain ⟨q, hqS', hqmax⟩ := Finset.exists_max_image S' (fun p => p.1 + p.2) hS'ne
  set d : ℕ := q.1 + q.2 with hd
  set A' : ℕ × ℕ → Polynomial ℂ := fun p => Polynomial.X ^ d * A p with hA'
  have hS'sub : S' ⊆ S := by rw [hS']; exact Finset.filter_subset _ _
  have hrelS' : ∀ z : ℂ,
      ∑ p ∈ S', (A p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    rw [Finset.sum_subset hS'sub]
    · exact hrel z
    · intro p hpS hpnot
      have hAp : A p = 0 := by
        by_contra hpA
        exact hpnot (Finset.mem_filter.mpr ⟨hpS, hpA⟩)
      rw [hAp]
      simp
  have hdeg : ∀ p ∈ S', p.1 + p.2 ≤ d := by
    intro p hp
    rw [hd]
    exact hqmax p hp
  have hrel' : ∀ z : ℂ,
      ∑ p ∈ S', (A' p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    rw [hA']
    simp_rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    calc
      ∑ p ∈ S', z ^ d * (A p).eval z * (coeffFun a z) ^ p.1 *
          deriv (coeffFun a) z ^ p.2 =
          z ^ d * ∑ p ∈ S', (A p).eval z * (coeffFun a z) ^ p.1 *
            deriv (coeffFun a) z ^ p.2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p hp
        ring
      _ = 0 := by rw [hrelS' z, mul_zero]
  have hqmem : q ∈ S.filter (fun p => A p ≠ 0) := by simpa [hS'] using hqS'
  have hAq : A q ≠ 0 := (Finset.mem_filter.mp hqmem).2
  have hA'q : A' q ≠ 0 := by
    rw [hA']
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hAq
  have hdegq : q.2 ≤ (A' q).natDegree := by
    rw [hA', Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hAq,
      Polynomial.natDegree_X_pow]
    omega
  obtain ⟨C, hC, hbound⟩ :=
    exists_radius_le_centralIndex_pow_of_top_coefficient_degree ha hn₀ htrans hdeg hrel'
      ⟨q, hqS', hd.symm, hA'q, hdegq⟩
  exact ⟨d, C, hC, hbound⟩

/-- **Sublogarithmic central index excludes every first-order ADE.**  This is the first-order
Valiron growth wall in the exact asymptotic form supplied by an entire heat orbit. -/
theorem not_differentiallyAlgebraicOfOrder_one_of_centralIndex_div_log_zero
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hlim : Tendsto (fun r : ℝ => (centralIndex a r : ℝ) / Real.log r)
      atTop (nhds 0)) :
    ¬ GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1 := by
  intro hDA
  obtain ⟨d, C, hC, hbound⟩ :=
    exists_radius_le_centralIndex_pow_of_order_one ha hn₀ htrans hDA
  have hsmall : ∀ᶠ r : ℝ in atTop,
      (centralIndex a r : ℝ) / Real.log r < 1 :=
    hlim.eventually_lt_const one_pos
  have hpolyBase := eventually_mul_rpow_le_exp_rpow (C + 1)
    (c := (1 : ℝ)) (δ := (1 : ℝ)) (p := (d : ℝ)) one_pos one_pos
  have hpolyComp := Real.tendsto_log_atTop.eventually hpolyBase
  have hpoly : ∀ᶠ r : ℝ in atTop, C * (Real.log r) ^ d < r := by
    filter_upwards [hpolyComp, eventually_gt_atTop (1 : ℝ)] with r hr hr1
    have hlog : 0 < Real.log r := Real.log_pos hr1
    have hr0 : 0 < r := lt_trans one_pos hr1
    rw [Real.rpow_one, one_mul, Real.rpow_natCast, Real.exp_log hr0] at hr
    have hp : 0 < (Real.log r) ^ d := pow_pos hlog d
    nlinarith
  have hlog : ∀ᶠ r : ℝ in atTop, 0 < Real.log r := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    exact Real.log_pos hr
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hsmall.and (hpoly.and hlog))
  obtain ⟨r, hrR, hrbound⟩ := hbound R
  obtain ⟨hrsmall, hrpoly, hrlog⟩ := hR r hrR
  have hνlog : (centralIndex a r : ℝ) < Real.log r := by
    rw [div_lt_iff₀ hrlog] at hrsmall
    simpa using hrsmall
  have hpow : ((centralIndex a r : ℕ) : ℝ) ^ d ≤ (Real.log r) ^ d :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hνlog.le d
  have hmul : C * ((centralIndex a r : ℕ) : ℝ) ^ d ≤ C * (Real.log r) ^ d :=
    mul_le_mul_of_nonneg_left hpow hC.le
  exact (not_lt_of_ge hrbound) (lt_of_le_of_lt hmul hrpoly)

end

end GaloisForLFunctions.HTGeometry
