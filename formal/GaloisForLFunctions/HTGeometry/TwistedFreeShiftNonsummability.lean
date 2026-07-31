import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import GaloisForLFunctions.HTGeometry.FreeShiftOneSliceNonsummability

/-!
# Twisted free-shift one-slice nonsummability

A shift acting on a free bilateral jet grid need not fix the field of coefficients: in a tower of
translation orbits the deeper layers are themselves moved by the translation.  The obstruction to
one-slice summability survives that twist.  Let `φ` be a ring automorphism of the coefficient field
and let the twisted shift advance the translation slice by one while applying `φ` to the
coefficients.  Then no nonzero finite linear form supported on the single slice `m = 0` is a
coboundary for it, whatever the coefficients of that form.

The proof is a two-sided variable-window argument.  A reduced representation `p / q` of a
hypothetical primitive forces `q ∣ T q`; comparing the slices of the variables of `q` with those of
its shift makes `q` constant, so the primitive is a polynomial.  For a polynomial primitive the
variable of largest slice must reappear one slice higher, and the variable of smallest slice must
have come from one slice lower, which confines the whole variable set to an empty window.  A
constant primitive changes by a constant, not by a nonzero one-slice form.

* **`twistedShiftPolyEquiv`**, **`twistedShiftFieldEquiv`** — the twisted shift;
* **`twistedShiftPoly_sub_ne_oneSlice`** — the polynomial case;
* **`twistedShiftOneSlice_ne_coboundary`** — the rational case;
* `twistedShiftFieldEquiv_refl` — the untwisted specialization is the canonical free shift.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

variable {K α : Type*} [Field K]

/-! ## The twisted shift -/

/-- The `φ`-twisted unit shift of the free bilateral jet grid: it advances the translation slice by
one and applies `φ` to the coefficients. -/
def twistedShiftPolyEquiv (φ : K ≃+* K) :
    FreeShiftPolynomial K α ≃+* FreeShiftPolynomial K α :=
  (MvPolynomial.mapEquiv (FreeShiftJetIndex α) φ).trans
    (MvPolynomial.renameEquiv K (freeShiftJetIndexEquiv (α := α) 1)).toRingEquiv

theorem twistedShiftPolyEquiv_apply (φ : K ≃+* K) (p : FreeShiftPolynomial K α) :
    twistedShiftPolyEquiv φ p =
      MvPolynomial.rename (freeShiftJetIndexEquiv (α := α) 1) (MvPolynomial.map φ p) := rfl

/-- The twisted shift of the free bilateral rational jet field. -/
def twistedShiftFieldEquiv (φ : K ≃+* K) :
    FreeShiftField K α ≃+* FreeShiftField K α :=
  IsFractionRing.ringEquivOfRingEquiv (twistedShiftPolyEquiv (K := K) (α := α) φ)

@[simp] theorem twistedShiftFieldEquiv_algebraMap (φ : K ≃+* K) (p : FreeShiftPolynomial K α) :
    twistedShiftFieldEquiv (K := K) (α := α) φ
        (algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) p) =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (twistedShiftPolyEquiv φ p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ p

@[simp] theorem twistedShiftPolyEquiv_C (φ : K ≃+* K) (a : K) :
    twistedShiftPolyEquiv (K := K) (α := α) φ (MvPolynomial.C a) = MvPolynomial.C (φ a) := by
  rw [twistedShiftPolyEquiv_apply, MvPolynomial.map_C, MvPolynomial.rename_C]
  rfl

@[simp] theorem twistedShiftPolyEquiv_X (φ : K ≃+* K) (i : FreeShiftJetIndex α) :
    twistedShiftPolyEquiv (K := K) (α := α) φ (MvPolynomial.X i) =
      MvPolynomial.X (freeShiftJetIndexEquiv (α := α) 1 i) := by
  rw [twistedShiftPolyEquiv_apply, MvPolynomial.map_X, MvPolynomial.rename_X]

/-- The twisted shift acts on the base field by the twist. -/
theorem twistedShiftFieldEquiv_algebraMap_base (φ : K ≃+* K) (b : K) :
    twistedShiftFieldEquiv (K := K) (α := α) φ (algebraMap K (FreeShiftField K α) b) =
      algebraMap K (FreeShiftField K α) (φ b) := by
  have hb : algebraMap K (FreeShiftField K α) b =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (MvPolynomial.C b) := by
    rw [IsScalarTower.algebraMap_apply K (FreeShiftPolynomial K α) (FreeShiftField K α)]
    rfl
  have hbφ : algebraMap K (FreeShiftField K α) (φ b) =
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (MvPolynomial.C (φ b)) := by
    rw [IsScalarTower.algebraMap_apply K (FreeShiftPolynomial K α) (FreeShiftField K α)]
    rfl
  rw [hb, hbφ, twistedShiftFieldEquiv_algebraMap, twistedShiftPolyEquiv_C]

/-- The variables of a twisted shift are exactly the shifted variables. -/
theorem mem_vars_twistedShiftPolyEquiv (φ : K ≃+* K) (p : FreeShiftPolynomial K α)
    {x : FreeShiftJetIndex α} :
    x ∈ (twistedShiftPolyEquiv φ p).vars ↔
      ∃ y ∈ p.vars, freeShiftJetIndexEquiv (α := α) 1 y = x := by
  classical
  have hinj : Function.Injective ((φ : K →+* K) : K → K) := φ.injective
  have hmap : (MvPolynomial.map (φ : K →+* K) p).vars = p.vars :=
    vars_map_of_injective p hinj
  constructor
  · intro hx
    rw [twistedShiftPolyEquiv_apply] at hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (vars_rename _ _ hx)
    rw [hmap] at hy
    exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, rfl⟩
    rw [twistedShiftPolyEquiv_apply]
    have hy' : y ∈ (MvPolynomial.map (φ : K →+* K) p).vars := by rwa [hmap]
    have hback : MvPolynomial.rename (⇑(freeShiftJetIndexEquiv (α := α) 1).symm)
        (MvPolynomial.rename (⇑(freeShiftJetIndexEquiv (α := α) 1))
          (MvPolynomial.map (φ : K →+* K) p)) = MvPolynomial.map (φ : K →+* K) p := by
      rw [MvPolynomial.rename_rename]
      simp
    have hsub := vars_rename (R := K) (⇑(freeShiftJetIndexEquiv (α := α) 1).symm)
      (MvPolynomial.rename (⇑(freeShiftJetIndexEquiv (α := α) 1))
        (MvPolynomial.map (φ : K →+* K) p))
    rw [hback] at hsub
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp (hsub hy')
    have hzeq : z = freeShiftJetIndexEquiv (α := α) 1 y := by
      rw [← hzy]
      simp
    rwa [← hzeq]

/-! ## The one-slice form -/

theorem oneSliceIndex_injective :
    Function.Injective
      (fun j : α × ℕ => ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α)) := by
  rintro ⟨a, n⟩ ⟨b, m⟩ h
  simp only [Prod.mk.injEq] at h
  simp [h.1, h.2.2]

/-- Every variable of a one-slice form lies in the slice `0`. -/
theorem vars_freeShiftOneSlice_slice (c : (α × ℕ) →₀ K) {x : FreeShiftJetIndex α}
    (hx : x ∈ (freeShiftOneSlice c).vars) : x.2.1 = 0 := by
  classical
  rw [freeShiftOneSlice, Finsupp.sum] at hx
  obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp (vars_sum_subset _ _ hx)
  have hsub := vars_mul (MvPolynomial.C (c j) : FreeShiftPolynomial K α)
    (MvPolynomial.X ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α))
  have hx2 := hsub hxj
  rw [vars_C, vars_X, Finset.empty_union, Finset.mem_singleton] at hx2
  rw [hx2]

/-- The coefficient of a one-slice form at the linear monomial of a grid point. -/
theorem coeff_freeShiftOneSlice (c : (α × ℕ) →₀ K) (j : α × ℕ) :
    (freeShiftOneSlice c).coeff
        (Finsupp.single ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α) 1) = c j := by
  classical
  rw [freeShiftOneSlice, Finsupp.sum, coeff_sum]
  have hterm : ∀ i ∈ c.support,
      MvPolynomial.coeff (Finsupp.single ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α) 1)
          ((MvPolynomial.C (c i) : FreeShiftPolynomial K α) *
            MvPolynomial.X ((i.1, ((0 : ℤ), i.2)) : FreeShiftJetIndex α)) =
        if i = j then c i else 0 := by
    intro i _
    rw [coeff_C_mul, coeff_X]
    have hiff :
        ((Finsupp.single ((i.1, ((0 : ℤ), i.2)) : FreeShiftJetIndex α) 1) =
          Finsupp.single ((j.1, ((0 : ℤ), j.2)) : FreeShiftJetIndex α) 1) ↔ i = j := by
      constructor
      · intro hh
        exact oneSliceIndex_injective
          (Finsupp.single_left_injective (b := (1 : ℕ)) one_ne_zero hh)
      · rintro rfl
        rfl
    rw [if_congr hiff rfl rfl]
    split <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' c.support j c]
  by_cases hj : j ∈ c.support
  · rw [if_pos hj]
  · rw [if_neg hj]
    have hzero : c j = 0 := by simpa using hj
    rw [hzero]

/-! ## The polynomial case -/

/-- **Twisted one-slice nonsummability for a polynomial primitive.**  The variable of largest slice
would have to reappear one slice higher and the variable of smallest slice one slice lower, so the
primitive has no variables at all; a constant primitive changes by a constant. -/
theorem twistedShiftPoly_sub_ne_oneSlice (φ : K ≃+* K) (c : (α × ℕ) →₀ K) (hc : c ≠ 0)
    (P : FreeShiftPolynomial K α) :
    twistedShiftPolyEquiv φ P - P ≠ freeShiftOneSlice c := by
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
    simp only [MvPolynomial.coeff_sub, hT, hCcoeff, hPcoeff, coeff_freeShiftOneSlice,
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
    have hTP : twistedShiftPolyEquiv φ P = freeShiftOneSlice c + P := by
      rw [← h]; ring
    have hPeq : P = twistedShiftPolyEquiv φ P - freeShiftOneSlice c := by
      rw [← h]; ring
    have hMax : S.max' hsliceNe = -1 := by
      have hshift : freeShiftJetIndexEquiv (α := α) 1 x₀ ∈ (twistedShiftPolyEquiv φ P).vars :=
        (mem_vars_twistedShiftPolyEquiv φ P).mpr ⟨x₀, hx₀, rfl⟩
      rw [hTP] at hshift
      rcases Finset.mem_union.mp (vars_add_subset _ _ hshift) with hx2 | hx2
      · have hzero := vars_freeShiftOneSlice_slice c hx2
        have hval : x₀.2.1 + 1 = 0 := hzero
        omega
      · have hmem : x₀.2.1 + 1 ∈ S := by
          rw [hS]
          exact Finset.mem_image.mpr ⟨freeShiftJetIndexEquiv (α := α) 1 x₀, hx2, rfl⟩
        have hle := Finset.le_max' S _ hmem
        omega
    have hMin : S.min' hsliceNe = 0 := by
      have hy1 : y₀ ∈ (twistedShiftPolyEquiv φ P).vars ∪ (freeShiftOneSlice c).vars := by
        have hsubset := vars_sub_subset (p := twistedShiftPolyEquiv φ P)
          (q := freeShiftOneSlice c)
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
      · have hzero := vars_freeShiftOneSlice_slice c hy2
        omega
    have hle := Finset.min'_le_max' S hsliceNe
    omega

/-! ## The rational case -/

/-- **Twisted one-slice nonsummability.**  In the free bilateral rational jet field no nonzero
finite linear form supported on the single slice `0` is a coboundary for the twisted shift. -/
theorem twistedShiftOneSlice_ne_coboundary (φ : K ≃+* K) (c : (α × ℕ) →₀ K) (hc : c ≠ 0)
    (g : FreeShiftField K α) :
    twistedShiftFieldEquiv (K := K) (α := α) φ g - g ≠
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (freeShiftOneSlice c) := by
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
      algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α) (freeShiftOneSlice c) *
        (algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
            (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α)) *
          algebraMap (FreeShiftPolynomial K α) (FreeShiftField K α)
            (q : FreeShiftPolynomial K α)) := by
    have h' := h
    rw [hTg, hgdiv, div_sub_div _ _ hATq hAq, div_eq_iff (mul_ne_zero hATq hAq)] at h'
    exact h'
  have hcross : twistedShiftPolyEquiv φ p * (q : FreeShiftPolynomial K α) -
      twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α) * p =
      freeShiftOneSlice c * (twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α) *
        (q : FreeShiftPolynomial K α)) := by
    apply IsFractionRing.injective (FreeShiftPolynomial K α) (FreeShiftField K α)
    simpa only [map_sub, map_mul] using hcrossField
  have hdvdmul : (q : FreeShiftPolynomial K α) ∣
      twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α) * p := by
    refine ⟨twistedShiftPolyEquiv φ p -
      freeShiftOneSlice c * twistedShiftPolyEquiv φ (q : FreeShiftPolynomial K α), ?_⟩
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
  refine twistedShiftPoly_sub_ne_oneSlice φ c hc (MvPolynomial.C b⁻¹ * p) ?_
  apply IsFractionRing.injective (FreeShiftPolynomial K α) (FreeShiftField K α)
  rw [map_sub, ← twistedShiftFieldEquiv_algebraMap, ← hgpoly]
  exact h

/-! ## The untwisted specialization -/

theorem twistedShiftPolyEquiv_refl (p : FreeShiftPolynomial K α) :
    twistedShiftPolyEquiv (K := K) (α := α) (RingEquiv.refl K) p =
      freeShiftPolynomialEquiv (K := K) (α := α) 1 p := by
  rw [twistedShiftPolyEquiv_apply, freeShiftPolynomialEquiv, MvPolynomial.renameEquiv_apply]
  congr 1
  simpa using MvPolynomial.map_id p

theorem twistedShiftFieldEquiv_refl (g : FreeShiftField K α) :
    twistedShiftFieldEquiv (K := K) (α := α) (RingEquiv.refl K) g =
      freeShiftFieldEquiv (K := K) (α := α) 1 g := by
  obtain ⟨p, q, hq, rfl⟩ :=
    IsFractionRing.div_surjective (A := FreeShiftPolynomial K α) (K := FreeShiftField K α) g
  rw [map_div₀, map_div₀, twistedShiftFieldEquiv_algebraMap, twistedShiftFieldEquiv_algebraMap,
    freeShiftFieldEquiv_algebraMap, freeShiftFieldEquiv_algebraMap, twistedShiftPolyEquiv_refl,
    twistedShiftPolyEquiv_refl]

end

end GaloisForLFunctions.HTGeometry
