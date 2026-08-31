import GaloisForLFunctions.HTGeometry.WeightHomogenization

/-!
# The grading of the homogenized family

Give the extra variable weight `-1`.  A polynomial in it is then homogeneous of weight `d` exactly
when its `j`-th coefficient is weighted-homogeneous of weight `d + j`, and the homogenization of a
polynomial is homogeneous of weight its minimal weight:

```text
weightedHomogeneousComponent_mul_right   multiplying by a homogeneous polynomial shifts components
homogenize_coeff                         the coefficients are the weighted components
IsFamHomog, isFamHomog_homogenize        homogenization is homogeneous
weightedHomogeneousComponent_eval_one    ** the components of the dehomogenization are the
                                            coefficients **
eq_X_pow_mul_homogenize                  ** a homogeneous polynomial is a power of the extra
                                            variable times the homogenization of its
                                            dehomogenization **
```

The structure theorem is what makes the family well behaved.  Homogeneity forces the coefficients to
sit in distinct weights, so the dehomogenization remembers all of them; its minimal weight is
reached at the trailing coefficient, and dividing by that power of the extra variable returns the
homogenization exactly.  In particular no homogeneous element is lost when the extra variable is
inverted, which is the shape of the `t`-saturation statement the flat family needs.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

/-- **Multiplying by a weighted-homogeneous polynomial shifts the weighted components.** -/
theorem weightedHomogeneousComponent_mul_right {w : σ → ℤ} {h : MvPolynomial σ K} {e : ℤ}
    (hh : MvPolynomial.IsWeightedHomogeneous w h e) (g : MvPolynomial σ K) (c : ℤ) :
    MvPolynomial.weightedHomogeneousComponent w c (g * h)
      = MvPolynomial.weightedHomogeneousComponent w (c - e) g * h := by
  classical
  ext γ
  rw [MvPolynomial.coeff_weightedHomogeneousComponent, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_mul]
  by_cases hγ : Finsupp.weight w γ = c
  · rw [if_pos hγ]
    refine Finset.sum_congr rfl ?_
    rintro ⟨α, β⟩ hαβ
    have hsum : α + β = γ := Finset.HasAntidiagonal.mem_antidiagonal.mp hαβ
    by_cases hβ : MvPolynomial.coeff β h = 0
    · rw [hβ, mul_zero, mul_zero]
    · have hwβ : Finsupp.weight w β = e := hh hβ
      have hwα : Finsupp.weight w α = c - e := by
        have : Finsupp.weight w α + Finsupp.weight w β = Finsupp.weight w γ := by
          rw [← map_add, hsum]
        omega
      rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hwα]
  · rw [if_neg hγ]
    refine (Finset.sum_eq_zero ?_).symm
    rintro ⟨α, β⟩ hαβ
    have hsum : α + β = γ := Finset.HasAntidiagonal.mem_antidiagonal.mp hαβ
    by_cases hβ : MvPolynomial.coeff β h = 0
    · rw [hβ, mul_zero]
    · have hwβ : Finsupp.weight w β = e := hh hβ
      have hwα : Finsupp.weight w α ≠ c - e := by
        intro hcon
        refine hγ ?_
        have : Finsupp.weight w α + Finsupp.weight w β = Finsupp.weight w γ := by
          rw [← map_add, hsum]
        omega
      rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_neg hwα, zero_mul]

/-- The coefficients of the homogenization are the weighted-homogeneous components, read off from
the lowest weight upwards. -/
theorem homogenize_coeff (w : σ → ℤ) (f : MvPolynomial σ K) (j : ℕ) :
    (homogenize w f).coeff j
      = MvPolynomial.weightedHomogeneousComponent w (minWeight w f + j) f := by
  classical
  rw [homogenize, Polynomial.finsetSum_coeff,
    MvPolynomial.weightedHomogeneousComponent_apply]
  rw [← Finset.sum_filter_add_sum_filter_not f.support
    (fun α => Finsupp.weight w α = minWeight w f + j)]
  rw [show (∑ α ∈ f.support.filter
      (fun α => ¬ Finsupp.weight w α = minWeight w f + j),
      (Polynomial.monomial ((Finsupp.weight w α - minWeight w f).toNat)
        (MvPolynomial.monomial α (MvPolynomial.coeff α f))).coeff j) = 0 from ?_]
  · rw [add_zero]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [Finset.mem_filter] at hα
    have hj : (Finsupp.weight w α - minWeight w f).toNat = j := by
      have := hα.2
      omega
    rw [hj, Polynomial.coeff_monomial, if_pos rfl]
  · refine Finset.sum_eq_zero fun α hα => ?_
    rw [Finset.mem_filter] at hα
    have hle : minWeight w f ≤ Finsupp.weight w α := minWeight_le hα.1
    have hne : (Finsupp.weight w α - minWeight w f).toNat ≠ j := by
      have := hα.2
      omega
    rw [Polynomial.coeff_monomial, if_neg (fun h => hne h)]

/-- A polynomial in the extra variable is homogeneous for the weight in which the extra variable has
weight `-1` when its `j`-th coefficient is weighted-homogeneous of weight `d + j`. -/
def IsFamHomog (w : σ → ℤ) (d : ℤ) (F : Polynomial (MvPolynomial σ K)) : Prop :=
  ∀ j : ℕ, MvPolynomial.IsWeightedHomogeneous w (F.coeff j) (d + j)

theorem isFamHomog_homogenize (w : σ → ℤ) (f : MvPolynomial σ K) :
    IsFamHomog w (minWeight w f) (homogenize w f) := by
  intro j
  rw [homogenize_coeff]
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- The weighted components of the dehomogenization are the coefficients. -/
theorem weightedHomogeneousComponent_eval_one {w : σ → ℤ} {d : ℤ}
    {F : Polynomial (MvPolynomial σ K)} (hF : IsFamHomog w d F) (j : ℕ) :
    MvPolynomial.weightedHomogeneousComponent w (d + j) (Polynomial.eval 1 F)
      = F.coeff j := by
  classical
  have heval : Polynomial.eval 1 F = ∑ i ∈ F.support, F.coeff i := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    simp
  rw [heval, map_sum]
  by_cases hj : j ∈ F.support
  · rw [← Finset.add_sum_erase _ _ hj]
    have hself : MvPolynomial.weightedHomogeneousComponent w (d + j) (F.coeff j) = F.coeff j := by
      ext γ
      rw [MvPolynomial.coeff_weightedHomogeneousComponent]
      by_cases hγ : Finsupp.weight w γ = d + j
      · rw [if_pos hγ]
      · rw [if_neg hγ]
        by_contra hcon
        exact hγ (hF j (Ne.symm hcon))
    rw [hself, show (∑ i ∈ F.support.erase j,
        MvPolynomial.weightedHomogeneousComponent w (d + j) (F.coeff i)) = 0 from ?_, add_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    ext γ
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hγ : Finsupp.weight w γ = d + j
    · rw [if_pos hγ]
      by_contra hcon
      have hnz : MvPolynomial.coeff γ (F.coeff i) ≠ 0 := by simpa using hcon
      have hwi : Finsupp.weight w γ = d + i := hF i hnz
      omega
    · rw [if_neg hγ]
      simp
  · rw [Polynomial.notMem_support_iff] at hj
    rw [hj]
    refine Finset.sum_eq_zero fun i _ => ?_
    ext γ
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hγ : Finsupp.weight w γ = d + j
    · rw [if_pos hγ]
      by_contra hcon
      have hnz : MvPolynomial.coeff γ (F.coeff i) ≠ 0 := by simpa using hcon
      have hwi : Finsupp.weight w γ = d + i := hF i hnz
      have hij : i = j := by omega
      rw [hij, hj] at hnz
      simp at hnz
    · rw [if_neg hγ]
      simp

theorem eval_one_ne_zero_of_isFamHomog {w : σ → ℤ} {d : ℤ} {F : Polynomial (MvPolynomial σ K)}
    (hF : IsFamHomog w d F) (hF0 : F ≠ 0) : Polynomial.eval 1 F ≠ 0 := by
  intro hzero
  refine hF0 (Polynomial.ext fun j => ?_)
  rw [← weightedHomogeneousComponent_eval_one hF j, hzero, map_zero, Polynomial.coeff_zero]

/-- **A homogeneous polynomial in the extra variable is a power of that variable times the
homogenization of its dehomogenization.** -/
theorem eq_X_pow_mul_homogenize {w : σ → ℤ} {d : ℤ} {F : Polynomial (MvPolynomial σ K)}
    (hF : IsFamHomog w d F) (hF0 : F ≠ 0) :
    F = Polynomial.X ^ F.natTrailingDegree * homogenize w (Polynomial.eval 1 F) := by
  classical
  set j₀ := F.natTrailingDegree with hj₀
  set f := Polynomial.eval 1 F with hf
  have hf0 : f ≠ 0 := eval_one_ne_zero_of_isFamHomog hF hF0
  have hcoeff0 : F.coeff j₀ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hF0
  have hmin : minWeight w f = d + j₀ := by
    refine le_antisymm ?_ ?_
    · have hne : MvPolynomial.weightedHomogeneousComponent w (d + j₀) f ≠ 0 := by
        rw [weightedHomogeneousComponent_eval_one hF]
        exact hcoeff0
      obtain ⟨γ, hγ⟩ := MvPolynomial.support_nonempty.mpr hne
      have hwγ : Finsupp.weight w γ = d + j₀ := by
        have := MvPolynomial.mem_support_iff.mp hγ
        rw [MvPolynomial.coeff_weightedHomogeneousComponent] at this
        by_contra hcon
        rw [if_neg hcon] at this
        exact this rfl
      have hγf : γ ∈ f.support := by
        rw [MvPolynomial.mem_support_iff]
        have := MvPolynomial.mem_support_iff.mp hγ
        rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hwγ] at this
        exact this
      calc minWeight w f ≤ Finsupp.weight w γ := minWeight_le hγf
        _ = d + j₀ := hwγ
    · refine le_minWeight (a := d + (j₀ : ℤ)) hf0 fun γ hγ => ?_
      have heval : f = ∑ i ∈ F.support, F.coeff i := by
        rw [hf, Polynomial.eval_eq_sum, Polynomial.sum]
        simp
      have hnz : MvPolynomial.coeff γ f ≠ 0 := MvPolynomial.mem_support_iff.mp hγ
      rw [heval] at hnz
      rw [MvPolynomial.coeff_sum] at hnz
      obtain ⟨i, hi, hine⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
      have hwi : Finsupp.weight w γ = d + i := hF i hine
      have hij : j₀ ≤ i := Polynomial.natTrailingDegree_le_of_ne_zero
        (Polynomial.mem_support_iff.mp hi)
      have hcast : (j₀ : ℤ) ≤ (i : ℤ) := Int.ofNat_le.mpr hij
      rw [hwi]
      omega
  refine Polynomial.ext fun j => ?_
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hle : j₀ ≤ j
  · rw [if_pos hle, homogenize_coeff, hmin]
    have hrw : d + (j₀ : ℤ) + ((j - j₀ : ℕ) : ℤ) = d + (j : ℤ) := by
      have : ((j - j₀ : ℕ) : ℤ) = (j : ℤ) - (j₀ : ℤ) := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [this]; ring
    rw [hrw, weightedHomogeneousComponent_eval_one hF]
  · rw [if_neg hle]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (p := F) (by omega)

end GaloisForLFunctions.HTGeometry
