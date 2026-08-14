import GaloisForLFunctions.HTGeometry.TwistedFreeShiftNonsummability

/-!
# One-slice nonsummability with an additive base term

The multiple-sine coface equation is exact only modulo the rational coordinate field, so the
telescoper to be excluded is a one-slice form shifted by an element of the base.  A constant summand
lives in degree zero while a one-slice form is degree one in the slice-`0` variables, so the support
argument that excludes the form excludes the shifted form as well.

The rational case is separated from the polynomial case: over a field the denominator analysis never
looks at the right-hand side, so it holds for an arbitrary polynomial whose polynomial case is
already known.
-/

open scoped Differential

namespace GaloisForLFunctions

open HTGeometry MvPolynomial

noncomputable section

variable {K α : Type*} [Field K]

/-- A one-slice form shifted by a constant. -/
def freeShiftAffineSlice (b : K) (c : (α × ℕ) →₀ K) : FreeShiftPolynomial K α :=
  MvPolynomial.C b + freeShiftOneSlice c

/-- Every variable of a shifted one-slice form still lies in the slice `0`. -/
theorem vars_freeShiftAffineSlice_slice (b : K) (c : (α × ℕ) →₀ K)
    {x : FreeShiftJetIndex α} (hx : x ∈ (freeShiftAffineSlice b c).vars) : x.2.1 = 0 := by
  classical
  rw [freeShiftAffineSlice] at hx
  rcases Finset.mem_union.mp (vars_add_subset _ _ hx) with hx2 | hx2
  · rw [vars_C] at hx2
    exact absurd hx2 (Finset.notMem_empty _)
  · exact vars_freeShiftOneSlice_slice c hx2

/-- The linear coefficients of a shifted one-slice form are unchanged. -/
theorem coeff_freeShiftAffineSlice (b : K) (c : (α × ℕ) →₀ K) (j : α × ℕ) :
    (freeShiftAffineSlice b c).coeff
        (Finsupp.single ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α) 1) = c j := by
  classical
  have hmono : ¬ ((0 : FreeShiftJetIndex α →₀ ℕ) =
      Finsupp.single ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α) 1) := by
    intro hh
    exact (by simp : (Finsupp.single ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α) 1) ≠ 0) hh.symm
  rw [freeShiftAffineSlice, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_neg hmono,
    zero_add, coeff_freeShiftOneSlice]

theorem twistedShiftPoly_sub_ne_affineSlice (φ : K ≃+* K) (b : K) (c : (α × ℕ) →₀ K)
    (hc : c ≠ 0) (P : FreeShiftPolynomial K α) :
    twistedShiftPolyEquiv φ P - P ≠ freeShiftAffineSlice b c := by
  classical
  intro h
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp hc
  have hj₀' : c j₀ ≠ 0 := by simpa using hj₀
  have hmono : (Finsupp.single ((j₀.1, ((0 : ℤ), j₀.2)) : FreeShiftJetIndex α) 1) ≠ 0 := by
    simp
  have hmono' : ¬ ((0 : FreeShiftJetIndex α →₀ ℕ) =
      Finsupp.single ((j₀.1, ((0 : ℤ), j₀.2)) : FreeShiftJetIndex α) 1) :=
    fun hh => hmono hh.symm
  by_cases hvars : P.vars = ∅
  · have hP : P = MvPolynomial.C (P.coeff 0) := vars_eq_empty_iff_eq_C.mp hvars
    have hT : twistedShiftPolyEquiv φ P = MvPolynomial.C (φ (P.coeff 0)) := by
      conv_lhs => rw [hP]
      rw [twistedShiftPolyEquiv_apply, MvPolynomial.map_C, MvPolynomial.rename_C]
      rfl
    have hPcoeff : P.coeff
        (Finsupp.single ((j₀.1, ((0 : ℤ), j₀.2)) : FreeShiftJetIndex α) 1) = 0 := by
      rw [hP, MvPolynomial.coeff_C, if_neg hmono']
    have hCcoeff : (MvPolynomial.C (φ (P.coeff 0)) : FreeShiftPolynomial K α).coeff
        (Finsupp.single ((j₀.1, ((0 : ℤ), j₀.2)) : FreeShiftJetIndex α) 1) = 0 := by
      rw [MvPolynomial.coeff_C, if_neg hmono']
    have hcoeff := congrArg (fun r : FreeShiftPolynomial K α =>
      r.coeff (Finsupp.single ((j₀.1, ((0 : ℤ), j₀.2)) : FreeShiftJetIndex α) 1)) h
    simp only [MvPolynomial.coeff_sub, hT, hCcoeff, hPcoeff, coeff_freeShiftAffineSlice,
      sub_zero] at hcoeff
    exact hj₀' hcoeff.symm
  · have hPne : P.vars.Nonempty := Finset.nonempty_iff_ne_empty.mpr hvars
    have hsliceNe : (P.vars.image fun x : FreeShiftJetIndex α => x.2.1).Nonempty :=
      hPne.image _
    set S : Finset ℤ := P.vars.image fun x : FreeShiftJetIndex α => x.2.1 with hS
    obtain ⟨x₀, hx₀, hx₀M⟩ := Finset.mem_image.mp (S.max'_mem hsliceNe)
    obtain ⟨y₀, hy₀, hy₀m⟩ := Finset.mem_image.mp (S.min'_mem hsliceNe)
    have hx₀M' : x₀.2.1 = S.max' hsliceNe := hx₀M
    have hy₀m' : y₀.2.1 = S.min' hsliceNe := hy₀m
    have hTP : twistedShiftPolyEquiv φ P = freeShiftAffineSlice b c + P := by
      rw [← h]; ring
    have hPeq : P = twistedShiftPolyEquiv φ P - freeShiftAffineSlice b c := by
      rw [← h]; ring
    have hMax : S.max' hsliceNe = -1 := by
      have hshift : freeShiftJetIndexEquiv (α := α) 1 x₀ ∈ (twistedShiftPolyEquiv φ P).vars :=
        (mem_vars_twistedShiftPolyEquiv φ P).mpr ⟨x₀, hx₀, rfl⟩
      rw [hTP] at hshift
      rcases Finset.mem_union.mp (vars_add_subset _ _ hshift) with hx2 | hx2
      · have hzero := vars_freeShiftAffineSlice_slice b c hx2
        have hval : x₀.2.1 + 1 = 0 := hzero
        omega
      · have hmem : x₀.2.1 + 1 ∈ S := by
          rw [hS]
          exact Finset.mem_image.mpr ⟨freeShiftJetIndexEquiv (α := α) 1 x₀, hx2, rfl⟩
        have hle := Finset.le_max' S _ hmem
        omega
    have hMin : S.min' hsliceNe = 0 := by
      have hy1 : y₀ ∈ (twistedShiftPolyEquiv φ P).vars ∪ (freeShiftAffineSlice b c).vars := by
        have hsubset := vars_sub_subset (p := twistedShiftPolyEquiv φ P)
          (q := freeShiftAffineSlice b c)
        rw [← hPeq] at hsubset
        exact hsubset hy₀
      rcases Finset.mem_union.mp hy1 with hy2 | hy2
      · obtain ⟨z, hz, hzy⟩ := (mem_vars_twistedShiftPolyEquiv φ P).mp hy2
        have hzslice : z.2.1 + 1 = y₀.2.1 := congrArg (fun w : FreeShiftJetIndex α => w.2.1) hzy
        have hmem : z.2.1 ∈ S := by
          rw [hS]
          exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
        have hge := Finset.min'_le S _ hmem
        omega
      · have hzero := vars_freeShiftAffineSlice_slice b c hy2
        omega
    have hle := Finset.min'_le_max' S hsliceNe
    omega


theorem twistedShiftField_sub_ne_algebraMap_of_poly (φ : K ≃+* K)
    (R : FreeShiftPolynomial K α)
    (hR : ∀ P : FreeShiftPolynomial K α, twistedShiftPolyEquiv φ P - P ≠ R)
    (g : FreeShiftField K α) :
    twistedShiftFieldEquiv (K := K) (α := α) φ g - g ≠
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) R := by
  classical
  intro h
  obtain ⟨p, q, hrel, hmk⟩ :=
    IsFractionRing.exists_reduced_fraction (FreeShiftPolynomial K α)
      (K := FreeShiftField K α) g
  have hq0 : (q : FreeShiftPolynomial K α) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp q.2
  have hTq0 : twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α) ≠ 0 := by
    intro hh
    exact hq0 ((twistedShiftPolyEquiv φ).injective (by rw [hh, map_zero]))
  have hAq : algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
      (q : FreeShiftPolynomial K α) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.2
  have hATq : algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
      (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α)) ≠ 0 := by
    intro hh
    exact hTq0 (IsFractionRing.injective (FreeShiftPolynomial K α) (FreeShiftField K α)
      (by rw [hh, map_zero]))
  have hgdiv : g = algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p /
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
        (q : FreeShiftPolynomial K α) := by
    rw [← hmk, IsFractionRing.mk'_eq_div]
  have hTg : twistedShiftFieldEquiv (K := K) (α := α) φ g =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (twistedShiftPolyEquiv φ p) /
        algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
          (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α)) := by
    conv_lhs => rw [hgdiv]
    rw [map_div₀, twistedShiftFieldEquiv_algebraMap, twistedShiftFieldEquiv_algebraMap]
  have hcrossField :
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (twistedShiftPolyEquiv φ p) *
          algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
            (q : FreeShiftPolynomial K α) -
        algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
            (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α)) *
          algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (R) *
        (algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
            (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α)) *
          algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
            (q : FreeShiftPolynomial K α)) := by
    have h' := h
    rw [hTg, hgdiv, div_sub_div _ _ hATq hAq, div_eq_iff (mul_ne_zero hATq hAq)] at h'
    exact h'
  have hcross : twistedShiftPolyEquiv φ p * (q : FreeShiftPolynomial K α) -
      twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α) * p =
      R * (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α) *
        (q : FreeShiftPolynomial K α)) := by
    apply IsFractionRing.injective (FreeShiftPolynomial K α) (FreeShiftField K α)
    simpa only [map_sub, map_mul] using hcrossField
  have hdvdmul : (q : FreeShiftPolynomial K α) ∣
      twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α) * p := by
    refine ⟨twistedShiftPolyEquiv φ p -
      R * twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α), ?_⟩
    linear_combination -hcross
  have hdvd := hrel.symm.dvd_of_dvd_mul_right hdvdmul
  have hvarsub : ∀ x ∈ (q : FreeShiftPolynomial K α).vars,
      x ∈ (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α)).vars := by
    obtain ⟨r, hr⟩ := hdvd
    have hr0 : r ≠ 0 := by
      intro hh
      rw [hh, mul_zero] at hr
      exact hTq0 hr
    intro x hx
    rw [mem_vars_iff_degreeOf_ne_zero] at hx ⊢
    rw [hr, MvPolynomial.degreeOf_mul_eq hq0 hr0]
    omega
  have hqvars : (q : FreeShiftPolynomial K α).vars = ∅ := by
    classical
    by_contra hne
    have hqne : (q : FreeShiftPolynomial K α).vars.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hne
    have hsliceNe :
        ((q : FreeShiftPolynomial K α).vars.image
          fun x : FreeShiftJetIndex α => x.2.1).Nonempty := hqne.image _
    set S : Finset ℤ :=
      (q : FreeShiftPolynomial K α).vars.image fun x : FreeShiftJetIndex α => x.2.1 with hS
    obtain ⟨y₀, hy₀, hy₀m⟩ := Finset.mem_image.mp (S.min'_mem hsliceNe)
    have hy₀m' : y₀.2.1 = S.min' hsliceNe := hy₀m
    obtain ⟨z, hz, hzy⟩ :=
      (mem_vars_twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α)).mp (hvarsub y₀ hy₀)
    have hzslice : z.2.1 + 1 = y₀.2.1 := congrArg (fun w : FreeShiftJetIndex α => w.2.1) hzy
    have hmem : z.2.1 ∈ S := by
      rw [hS]
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hge := Finset.min'_le S _ hmem
    omega
  obtain ⟨b, hb⟩ : ∃ b : K, (q : FreeShiftPolynomial K α) = MvPolynomial.C b :=
    ⟨_, vars_eq_empty_iff_eq_C.mp hqvars⟩
  have hb0 : b ≠ 0 := by
    intro hh
    rw [hh, map_zero] at hb
    exact hq0 hb
  have hunit : algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
      (MvPolynomial.C b) * algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
        (MvPolynomial.C b⁻¹) = 1 := by
    rw [← map_mul, ← MvPolynomial.C_mul, mul_inv_cancel₀ hb0, MvPolynomial.C_1, map_one]
  have hgpoly : g = algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
      (MvPolynomial.C b⁻¹ * p) := by
    rw [hgdiv, hb, map_mul, div_eq_iff (by rw [← hb]; exact hAq)]
    calc algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p
        = (algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (MvPolynomial.C b) *
            algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (MvPolynomial.C b⁻¹)) *
            algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p := by
          rw [hunit, one_mul]
      _ = algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (MvPolynomial.C b⁻¹) *
            algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p *
            algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (MvPolynomial.C b) := by
          ring
  refine hR (MvPolynomial.C b⁻¹ * p) ?_
  apply IsFractionRing.injective (FreeShiftPolynomial K α) (FreeShiftField K α)
  rw [map_sub, ← twistedShiftFieldEquiv_algebraMap, ← hgpoly]
  exact h


/-- **Twisted one-slice nonsummability, modulo the base.**  In the free bilateral rational jet field
no nonzero finite linear form supported on the slice `0` is a coboundary for the twisted shift, even
after adding a constant. -/
theorem twistedShiftAffineSlice_ne_coboundary (φ : K ≃+* K) (b : K) (c : (α × ℕ) →₀ K)
    (hc : c ≠ 0) (g : FreeShiftField K α) :
    twistedShiftFieldEquiv (K := K) (α := α) φ g - g ≠
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (freeShiftAffineSlice b c) :=
  twistedShiftField_sub_ne_algebraMap_of_poly φ (freeShiftAffineSlice b c)
    (twistedShiftPoly_sub_ne_affineSlice φ b c hc) g

end

end GaloisForLFunctions
