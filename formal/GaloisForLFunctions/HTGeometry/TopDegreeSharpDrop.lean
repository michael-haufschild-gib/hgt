import GaloisForLFunctions.HTGeometry.TopDegreeValuationRing
import GaloisForLFunctions.HTGeometry.MvPolynomialPDerivDegree
import GaloisForLFunctions.HTGeometry.AffineFactorFamily

/-!
# The sharp drop at order zero, and the derivation at the uniformiser

Differentiating in the coordinate `m` drops the degree in that coordinate by one.  At degree zero it
drops by two, not one: the leading coefficient of the numerator and of the denominator have the same
`m`-degree, and the term that would produce degree `−1` cancels between them.  The cancellation is
visible on one polynomial operation, the reduction

`topRed m P = X_m · ∂_m P − (deg_m P) · P`,

whose coefficient at a monomial `s` is `(s_m − deg_m P) · coeff s P`, hence vanishes at the top.

The consequence is the statement in valuation form: with `u = 1/X_m`, the uniformiser of the
valuation ring `topInt m`, the derivation `∂/∂u = −X_m²·∂/∂X_m` maps the valuation ring into
itself.  That is the unramified shadow of the bound a place of an algebraic extension needs.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## The reduction that kills the top coefficient -/

/-- `X_m · ∂_m P − (deg_m P)·P`, the reduction whose `m`-degree is strictly smaller than `P`'s. -/
noncomputable def topRed (m : ℕ) (P : MvPolynomial ℕ ℂ) : MvPolynomial ℕ ℂ :=
  MvPolynomial.X m * MvPolynomial.pderiv m P
    - MvPolynomial.C ((MvPolynomial.degreeOf m P : ℂ)) * P

theorem coeff_X_mul_pderiv (m : ℕ) (P : MvPolynomial ℕ ℂ) (s : ℕ →₀ ℕ) :
    MvPolynomial.coeff s (MvPolynomial.X m * MvPolynomial.pderiv m P)
      = (s m : ℂ) * MvPolynomial.coeff s P := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  by_cases hs : m ∈ s.support
  · rw [if_pos hs, MvPolynomial.coeff_pderiv]
    have hsm : 1 ≤ s m := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
    have hadd : s - Finsupp.single m 1 + Finsupp.single m 1 = s := by
      ext i
      by_cases hi : i = m
      · subst hi
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · simp [hi]
    have hval : (s - Finsupp.single m 1 : ℕ →₀ ℕ) m + 1 = s m := by
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    have hvalC : ((s - Finsupp.single m 1 : ℕ →₀ ℕ) m : ℂ) + 1 = (s m : ℂ) := by
      rw [← hval]
      push_cast
      ring
    rw [hadd, hvalC]
    ring
  · rw [if_neg hs]
    have hsm : s m = 0 := by
      by_contra hc
      exact hs (Finsupp.mem_support_iff.mpr hc)
    rw [hsm]
    simp

theorem coeff_topRed (m : ℕ) (P : MvPolynomial ℕ ℂ) (s : ℕ →₀ ℕ) :
    MvPolynomial.coeff s (topRed m P)
      = ((s m : ℂ) - (MvPolynomial.degreeOf m P : ℂ)) * MvPolynomial.coeff s P := by
  rw [topRed, MvPolynomial.coeff_sub, coeff_X_mul_pderiv, MvPolynomial.coeff_C_mul]
  ring

/-- **The reduction strictly drops the degree.** -/
theorem degreeOf_topRed_le (m : ℕ) {P : MvPolynomial ℕ ℂ} (hP : 1 ≤ MvPolynomial.degreeOf m P) :
    MvPolynomial.degreeOf m (topRed m P) ≤ MvPolynomial.degreeOf m P - 1 := by
  refine MvPolynomial.degreeOf_le_iff.mpr fun s hs => ?_
  have hne : MvPolynomial.coeff s (topRed m P) ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  rw [coeff_topRed] at hne
  have hPne : MvPolynomial.coeff s P ≠ 0 := fun hc => hne (by rw [hc, mul_zero])
  have hsP : s m ≤ MvPolynomial.degreeOf m P :=
    MvPolynomial.degreeOf_le_iff.mp le_rfl s (MvPolynomial.mem_support_iff.mpr hPne)
  have hsne : (s m : ℂ) - (MvPolynomial.degreeOf m P : ℂ) ≠ 0 := fun hc => hne (by rw [hc, zero_mul])
  have : s m ≠ MvPolynomial.degreeOf m P := by
    intro hc
    exact hsne (by rw [hc, sub_self])
  omega

/-- The two reductions recombine the Wronskian when the degrees agree. -/
theorem X_mul_wronskian_eq (m : ℕ) {N D : MvPolynomial ℕ ℂ}
    (h : MvPolynomial.degreeOf m N = MvPolynomial.degreeOf m D) :
    MvPolynomial.X m * (D * MvPolynomial.pderiv m N - MvPolynomial.pderiv m D * N)
      = D * topRed m N - N * topRed m D := by
  rw [topRed, topRed, h]
  ring

/-! ## The sharp drop -/

theorem degreeOf_wronskian_le (m : ℕ) {N D : MvPolynomial ℕ ℂ}
    (hd : 1 ≤ MvPolynomial.degreeOf m D)
    (hnd : MvPolynomial.degreeOf m N ≤ MvPolynomial.degreeOf m D) :
    MvPolynomial.degreeOf m (D * MvPolynomial.pderiv m N - MvPolynomial.pderiv m D * N)
      ≤ 2 * MvPolynomial.degreeOf m D - 2 := by
  set n := MvPolynomial.degreeOf m N with hn
  set d := MvPolynomial.degreeOf m D with hdd
  rcases lt_or_eq_of_le hnd with hlt | heq
  · have h1 : MvPolynomial.degreeOf m (D * MvPolynomial.pderiv m N) ≤ 2 * d - 2 := by
      rcases eq_or_ne (MvPolynomial.pderiv m N) 0 with h0 | h0
      · rw [h0, mul_zero, MvPolynomial.degreeOf_zero]
        omega
      · have hlt' := degreeOf_pderiv_lt (i := m) (p := N) h0
        have := MvPolynomial.degreeOf_mul_le m D (MvPolynomial.pderiv m N)
        omega
    have h2 : MvPolynomial.degreeOf m (MvPolynomial.pderiv m D * N) ≤ 2 * d - 2 := by
      rcases eq_or_ne (MvPolynomial.pderiv m D) 0 with h0 | h0
      · rw [h0, zero_mul, MvPolynomial.degreeOf_zero]
        omega
      · have hlt' := degreeOf_pderiv_lt (i := m) (p := D) h0
        have := MvPolynomial.degreeOf_mul_le m (MvPolynomial.pderiv m D) N
        omega
    have := MvPolynomial.degreeOf_add_le m (D * MvPolynomial.pderiv m N)
      (-(MvPolynomial.pderiv m D * N))
    rw [MvPolynomial.degreeOf_neg] at this
    rw [sub_eq_add_neg]
    omega
  · set Q := D * MvPolynomial.pderiv m N - MvPolynomial.pderiv m D * N with hQ
    rcases eq_or_ne Q 0 with h0 | h0
    · rw [h0, MvPolynomial.degreeOf_zero]
      omega
    have hXQ : MvPolynomial.degreeOf m (MvPolynomial.X m * Q) = 1 + MvPolynomial.degreeOf m Q := by
      rw [MvPolynomial.degreeOf_mul_eq (MvPolynomial.X_ne_zero m) h0, MvPolynomial.degreeOf_X]
      simp
    have hid : MvPolynomial.X m * Q = D * topRed m N - N * topRed m D :=
      X_mul_wronskian_eq m heq
    have h1 : MvPolynomial.degreeOf m (D * topRed m N) ≤ 2 * d - 1 := by
      rcases eq_or_ne (topRed m N) 0 with hz | hz
      · rw [hz, mul_zero, MvPolynomial.degreeOf_zero]
        omega
      · have hred := degreeOf_topRed_le m (P := N) (by omega)
        have := MvPolynomial.degreeOf_mul_le m D (topRed m N)
        omega
    have h2 : MvPolynomial.degreeOf m (N * topRed m D) ≤ 2 * d - 1 := by
      rcases eq_or_ne (topRed m D) 0 with hz | hz
      · rw [hz, mul_zero, MvPolynomial.degreeOf_zero]
        omega
      · have hred := degreeOf_topRed_le m (P := D) hd
        have := MvPolynomial.degreeOf_mul_le m N (topRed m D)
        omega
    have hsum := MvPolynomial.degreeOf_add_le m (D * topRed m N) (-(N * topRed m D))
    rw [MvPolynomial.degreeOf_neg] at hsum
    rw [sub_eq_add_neg] at hid
    rw [hid] at hXQ
    omega

/-- **At degree zero the coordinate derivation drops the degree by two.** -/
theorem TopDegLE.fpderiv_top_sharp {m : ℕ} {f : CascadeField} (hf : TopDegLE m 0 f) :
    TopDegLE m (-2) (fpderiv m f) := by
  obtain ⟨N, D, hD, hfND, hdeg⟩ := hf
  rcases eq_or_ne (fpderiv m f) 0 with h0 | h0
  · rw [h0]
    exact topDegLE_zero m (-2)
  have hnd : MvPolynomial.degreeOf m N ≤ MvPolynomial.degreeOf m D := by
    have : ((MvPolynomial.degreeOf m N : ℤ)) ≤ (MvPolynomial.degreeOf m D : ℤ) := by
      simpa using hdeg
    exact_mod_cast this
  have hd : 1 ≤ MvPolynomial.degreeOf m D := by
    by_contra hc
    have hD0 : MvPolynomial.degreeOf m D = 0 := by omega
    have hN0 : MvPolynomial.degreeOf m N = 0 := by omega
    exact h0 (TopFree.fpderiv_eq_zero ⟨N, D, hD, hfND, hN0, hD0⟩)
  refine ⟨D * MvPolynomial.pderiv m N - MvPolynomial.pderiv m D * N, D * D,
    mul_ne_zero hD hD, algebraMap_sq_mul_fpderiv hfND, ?_⟩
  have hDD : MvPolynomial.degreeOf m (D * D)
      = MvPolynomial.degreeOf m D + MvPolynomial.degreeOf m D :=
    MvPolynomial.degreeOf_mul_eq hD hD
  have hmain := degreeOf_wronskian_le m hd hnd
  rw [hDD]
  push_cast
  omega

/-! ## The derivation at the uniformiser -/

theorem topOrd_fpderiv_of_mem_topInt {m : ℕ} {f : CascadeField} (h : f ∈ topInt m) :
    ((2 : ℤ) : WithTop ℤ) ≤ topOrd m (fpderiv m f) := by
  have hf : TopDegLE m 0 f := topDegLE_zero_iff_mem_topInt.mpr h
  have := (topDegLE_iff_le_topOrd m (-2) (fpderiv m f)).mp hf.fpderiv_top_sharp
  simpa using this

/-- The derivation `∂/∂u` at the uniformiser `u = 1/X_m` of the valuation ring. -/
noncomputable def uDeriv (m : ℕ) : Derivation ℂ CascadeField CascadeField :=
  -((fx m) ^ (2 : ℕ)) • fpderiv m

theorem uDeriv_apply (m : ℕ) (f : CascadeField) :
    uDeriv m f = -((fx m) ^ (2 : ℕ)) * fpderiv m f := rfl

/-- **The derivation at the uniformiser preserves the valuation ring.** -/
theorem uDeriv_mem_topInt {m : ℕ} {f : CascadeField} (h : f ∈ topInt m) :
    uDeriv m f ∈ topInt m := by
  have hsq : topOrd m (-((fx m) ^ (2 : ℕ))) = ((-2 : ℤ) : WithTop ℤ) := by
    rw [topOrd_neg, sq, topOrd_mul, topOrd_fx, ← WithTop.coe_add]
    norm_num
  rw [mem_topInt, uDeriv_apply, topOrd_mul, hsq]
  rcases eq_or_ne (fpderiv m f) 0 with h0 | h0
  · rw [h0, topOrd_zero]
    simp
  · have hder := topOrd_fpderiv_of_mem_topInt h
    rw [topOrd_of_ne_zero h0, WithTop.coe_le_coe] at hder
    rw [topOrd_of_ne_zero h0, ← WithTop.coe_add,
      show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) by norm_num, WithTop.coe_le_coe]
    omega

end GaloisForLFunctions.HTGeometry
