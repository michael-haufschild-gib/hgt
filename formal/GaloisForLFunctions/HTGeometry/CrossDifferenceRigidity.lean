import GaloisForLFunctions.HTGeometry.DifferentialLurothComponentTransfer

/-!
# Rigidity of the two-block cross-difference

A two-block divisor of the cross-difference of two coprime scalar differential polynomials whose
left-block degrees it dominates differs from the cross-difference by a base scalar only.  The
quotient cannot involve a left-block jet, by degrees; so it is a right-block polynomial, and as such
it divides every left-block coefficient of the cross-difference — which forces it to divide both
entries, hence to be a unit.

The cross-difference is antisymmetric under the block swap, so its two block degrees agree; the
divisor therefore inherits the same symmetry.  That is the block reciprocity Ritt's argument needs.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {F : Type*} [Field F]

/-- Right-block coefficients scale by a left-block factor. -/
theorem differentialPolynomialTwoBlockCoefficient_left_mul
    (a : DifferentialPolynomial Unit F) (X : DifferentialPolynomial (Unit ⊕ Unit) F)
    (m : (Unit × ℕ) →₀ ℕ) :
    differentialPolynomialTwoBlockCoefficient m
        (differentialPolynomialLeft (κ := Unit) a * X) =
      a * differentialPolynomialTwoBlockCoefficient m X := by
  unfold differentialPolynomialTwoBlockCoefficient
  rw [map_mul, differentialPolynomialTwoBlockEquiv_left, MvPolynomial.coeff_C_mul]

/-- The block swap exchanges the two block degrees. -/
theorem degreeOf_twoBlockSwap_inl (k : ℕ) (X : DifferentialPolynomial (Unit ⊕ Unit) F) :
    MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k)
        (differentialPolynomialTwoBlockSwap F X) =
      MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k) X := by
  have hinj : Function.Injective
      (fun p : (Unit ⊕ Unit) × ℕ => (Equiv.sumComm Unit Unit p.1, p.2)) := by
    rintro ⟨a, m⟩ ⟨b, n⟩ h
    have h1 : Equiv.sumComm Unit Unit a = Equiv.sumComm Unit Unit b := congrArg Prod.fst h
    have h2 : m = n := congrArg Prod.snd h
    exact Prod.ext ((Equiv.sumComm Unit Unit).injective h1) h2
  have := MvPolynomial.degreeOf_rename_of_injective (p := X) hinj
    ((Sum.inr () : Unit ⊕ Unit), k)
  simpa [differentialPolynomialTwoBlockSwap] using this

/-- A two-block polynomial with no left-block jet is a right-block polynomial. -/
theorem exists_right_of_degreeOf_inl_eq_zero
    {q : DifferentialPolynomial (Unit ⊕ Unit) F}
    (h : ∀ k : ℕ, MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) q = 0) :
    ∃ q₀ : DifferentialPolynomial Unit F,
      differentialPolynomialRight (ι := Unit) q₀ = q := by
  classical
  have hinj : Function.Injective (fun p : Unit × ℕ => ((Sum.inr p.1 : Unit ⊕ Unit), p.2)) := by
    rintro ⟨a, m⟩ ⟨b, n⟩ hab
    have h2 : m = n := congrArg Prod.snd hab
    exact Prod.ext (Subsingleton.elim _ _) h2
  refine MvPolynomial.exists_rename_eq_of_vars_subset_range q _ hinj ?_
  rintro ⟨j, k⟩ hj
  rw [Finset.mem_coe] at hj
  cases j with
  | inl u =>
      exfalso
      obtain rfl : u = () := Subsingleton.elim _ _
      exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.1 hj) (h k)
  | inr u =>
      obtain rfl : u = () := Subsingleton.elim _ _
      exact ⟨((), k), rfl⟩

/-- A unit has no jets at all. -/
theorem degreeOf_eq_zero_of_isUnit {σ : Type*} {u : MvPolynomial σ F} (hu : IsUnit u) (i : σ) :
    MvPolynomial.degreeOf i u = 0 := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hv
    exact zero_ne_one hv
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hv
    exact zero_ne_one hv
  have hdeg := MvPolynomial.degreeOf_mul_eq (n := i) hu0 hv0
  rw [hv] at hdeg
  simp only [MvPolynomial.degreeOf_one] at hdeg
  omega

/-- **Rigidity.**  A divisor of the cross-difference which dominates its left-block degrees has
exactly the cross-difference's degree in every jet. -/
theorem degreeOf_eq_of_dvd_crossDifference {H K : DifferentialPolynomial Unit F}
    (hcop : ∀ r : DifferentialPolynomial Unit F, r ∣ H → r ∣ K → IsUnit r)
    {μ ν : (Unit × ℕ) →₀ ℕ}
    (hcross : K.coeff ν * H.coeff μ - K.coeff μ * H.coeff ν ≠ 0)
    {C : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hdvd : C ∣ differentialPolynomialCrossDifference H K)
    (hdeg : ∀ k : ℕ, MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k)
        (differentialPolynomialCrossDifference H K) ≤
      MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) C) :
    ∀ v : (Unit ⊕ Unit) × ℕ,
      MvPolynomial.degreeOf v (differentialPolynomialCrossDifference H K) =
        MvPolynomial.degreeOf v C := by
  classical
  set D := differentialPolynomialCrossDifference H K with hD
  -- the two entries are not proportional, so the cross-difference does not vanish
  have hK0 : K ≠ 0 := by
    intro h0
    apply hcross
    rw [h0]
    simp
  have hD0 : D ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := (differentialPolynomialCrossDifference_eq_zero_iff hK0).1 h0
    apply hcross
    rw [hc]
    simp only [MvPolynomial.coeff_C_mul]
    ring
  obtain ⟨q, hq⟩ := hdvd
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hq
    exact hD0 hq
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact hD0 hq
  -- degrees force the quotient into the right block
  have hqdeg : ∀ k : ℕ, MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) q = 0 := by
    intro k
    have hmul := MvPolynomial.degreeOf_mul_eq (n := ((Sum.inl () : Unit ⊕ Unit), k)) hC0 hq0
    rw [← hq] at hmul
    have := hdeg k
    omega
  obtain ⟨q₀, hq₀⟩ := exists_right_of_degreeOf_inl_eq_zero hqdeg
  -- the quotient divides every left-block coefficient of the cross-difference
  have hswap : - D = differentialPolynomialTwoBlockSwap F C *
      differentialPolynomialLeft (κ := Unit) q₀ := by
    have := congrArg (differentialPolynomialTwoBlockSwap F) hq
    rw [differentialPolynomialTwoBlockSwap_crossDifference] at this
    rw [this, map_mul, ← hq₀, differentialPolynomialTwoBlockSwap_right]
  have hdvdcoeff : ∀ m : (Unit × ℕ) →₀ ℕ,
      q₀ ∣ K * MvPolynomial.C (H.coeff m) - H * MvPolynomial.C (K.coeff m) := by
    intro m
    have hcoeff := congrArg (differentialPolynomialTwoBlockCoefficient m) hswap
    rw [mul_comm (differentialPolynomialTwoBlockSwap F C)
      (differentialPolynomialLeft (κ := Unit) q₀),
      differentialPolynomialTwoBlockCoefficient_left_mul] at hcoeff
    have hneg : differentialPolynomialTwoBlockCoefficient m (-D) =
        - (K * MvPolynomial.C (H.coeff m) - H * MvPolynomial.C (K.coeff m)) := by
      unfold differentialPolynomialTwoBlockCoefficient
      rw [map_neg, MvPolynomial.coeff_neg]
      rw [hD]
      have := differentialPolynomialTwoBlockCoefficient_crossDifference m H K
      unfold differentialPolynomialTwoBlockCoefficient at this
      rw [this]
    rw [hneg] at hcoeff
    refine ⟨- differentialPolynomialTwoBlockCoefficient m
      (differentialPolynomialTwoBlockSwap F C), ?_⟩
    rw [mul_neg, ← hcoeff, neg_neg]
  -- hence it divides both entries and is a unit
  set c : F := K.coeff ν * H.coeff μ - K.coeff μ * H.coeff ν with hc
  have hCc : IsUnit (MvPolynomial.C c : DifferentialPolynomial Unit F) := by
    refine ⟨⟨MvPolynomial.C c, MvPolynomial.C c⁻¹, ?_, ?_⟩, rfl⟩
    · rw [← map_mul, mul_inv_cancel₀ hcross, map_one]
    · rw [← map_mul, inv_mul_cancel₀ hcross, map_one]
  have hdvdK : q₀ ∣ K := by
    have h1 := hdvdcoeff μ
    have h2 := hdvdcoeff ν
    have hcomb : q₀ ∣ MvPolynomial.C (K.coeff ν) *
        (K * MvPolynomial.C (H.coeff μ) - H * MvPolynomial.C (K.coeff μ)) -
        MvPolynomial.C (K.coeff μ) *
        (K * MvPolynomial.C (H.coeff ν) - H * MvPolynomial.C (K.coeff ν)) :=
      dvd_sub (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
    have hval : MvPolynomial.C (K.coeff ν) *
        (K * MvPolynomial.C (H.coeff μ) - H * MvPolynomial.C (K.coeff μ)) -
        MvPolynomial.C (K.coeff μ) *
        (K * MvPolynomial.C (H.coeff ν) - H * MvPolynomial.C (K.coeff ν)) =
          MvPolynomial.C c * K := by
      rw [hc, map_sub, map_mul, map_mul]
      ring
    rw [hval] at hcomb
    exact (hCc.dvd_mul_left).1 hcomb
  have hdvdH : q₀ ∣ H := by
    have h1 := hdvdcoeff μ
    have h2 := hdvdcoeff ν
    have hcomb : q₀ ∣ MvPolynomial.C (H.coeff ν) *
        (K * MvPolynomial.C (H.coeff μ) - H * MvPolynomial.C (K.coeff μ)) -
        MvPolynomial.C (H.coeff μ) *
        (K * MvPolynomial.C (H.coeff ν) - H * MvPolynomial.C (K.coeff ν)) :=
      dvd_sub (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
    have hval : MvPolynomial.C (H.coeff ν) *
        (K * MvPolynomial.C (H.coeff μ) - H * MvPolynomial.C (K.coeff μ)) -
        MvPolynomial.C (H.coeff μ) *
        (K * MvPolynomial.C (H.coeff ν) - H * MvPolynomial.C (K.coeff ν)) =
          MvPolynomial.C c * H := by
      rw [hc, map_sub, map_mul, map_mul]
      ring
    rw [hval] at hcomb
    exact (hCc.dvd_mul_left).1 hcomb
  have hunit : IsUnit q₀ := hcop q₀ hdvdH hdvdK
  have hunitq : IsUnit q := by
    rw [← hq₀]
    exact hunit.map (differentialPolynomialRight (ι := Unit) (C := F))
  intro v
  have hmul := MvPolynomial.degreeOf_mul_eq (n := v) hC0 hq0
  rw [← hq, degreeOf_eq_zero_of_isUnit hunitq v] at hmul
  omega

/-- **Block reciprocity.**  Such a divisor has the same degree in the left and the right block at
every jet, because the cross-difference is antisymmetric under the block swap. -/
theorem degreeOf_inl_eq_degreeOf_inr_of_dvd_crossDifference
    {H K : DifferentialPolynomial Unit F}
    (hcop : ∀ r : DifferentialPolynomial Unit F, r ∣ H → r ∣ K → IsUnit r)
    {μ ν : (Unit × ℕ) →₀ ℕ}
    (hcross : K.coeff ν * H.coeff μ - K.coeff μ * H.coeff ν ≠ 0)
    {C : DifferentialPolynomial (Unit ⊕ Unit) F}
    (hdvd : C ∣ differentialPolynomialCrossDifference H K)
    (hdeg : ∀ k : ℕ, MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k)
        (differentialPolynomialCrossDifference H K) ≤
      MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) C) :
    ∀ k : ℕ, MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k) C =
      MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k) C := by
  intro k
  have heq := degreeOf_eq_of_dvd_crossDifference hcop hcross hdvd hdeg
  have hanti : MvPolynomial.degreeOf ((Sum.inl () : Unit ⊕ Unit), k)
      (differentialPolynomialCrossDifference H K) =
      MvPolynomial.degreeOf ((Sum.inr () : Unit ⊕ Unit), k)
      (differentialPolynomialCrossDifference H K) := by
    have hswap := degreeOf_twoBlockSwap_inl (F := F) k
      (differentialPolynomialCrossDifference H K)
    rw [differentialPolynomialTwoBlockSwap_crossDifference,
      MvPolynomial.degreeOf_neg] at hswap
    exact hswap
  rw [← heq, ← heq, hanti]

end

end GaloisForLFunctions
