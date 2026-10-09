import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The hypersurface `∑ c_m X_m = 1`

Let `S = R[X_0, …, X_{f-1}] / (∑_m c_m X_m - 1)` with `c_m ∈ R`.  Away from `c_n`, the equation
solves for `X_n`: `S[c_n⁻¹] ≅ R[c_n⁻¹][X_m : m ≠ n]`.  The `c_n` generate the unit ideal of `S`
(their combination `∑ c_m X_m` is `1`), so `S` is smooth over any `K` over which `R` is smooth.  If `R`
is a domain and some `c_n ≠ 0`, then `S` is a domain: `c_n` is a nonzerodivisor on `S` (modulo `c_n`
the equation becomes `-1 + (terms without constant)`, a unit in the power series ring), so `S` embeds
in the domain `S[c_n⁻¹]`.

* `HTGeometry.hypersurfaceLocEquiv`.
* `HTGeometry.hypersurface_smooth`.
* `HTGeometry.hypersurface_isDomain`, `HTGeometry.hypersurface_C_injective`.
-/

namespace HTGeometry

open MvPolynomial

universe u

variable {R : Type u} [CommRing R] {f : ℕ} (c : Fin f → R)

/-- The linear form `∑_m c_m X_m`. -/
noncomputable def hypLinForm : MvPolynomial (Fin f) R := ∑ m, C (c m) * X m

/-- **The hypersurface ring** `R[X] / (∑ c_m X_m - 1)`. -/
abbrev LinHypersurface := MvPolynomial (Fin f) R ⧸ Ideal.span {hypLinForm c - 1}

theorem mk_hypLinForm : (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (hypLinForm c)) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem span_hypCoeffs_eq_top :
    Ideal.span (Set.range fun n => (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n)))) = ⊤ := by
  rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff,
    ← mk_hypLinForm c, hypLinForm, map_sum]
  refine Ideal.sum_mem _ fun m _ => ?_
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨m, rfl⟩)

/-! ## Solving for `X_n` away from `c_n` -/

section Solve

variable (n : Fin f)

/-- The polynomial ring `R[c_n⁻¹][X_m : m ≠ n]`. -/
abbrev HypT := MvPolynomial {m : Fin f // m ≠ n} (Localization.Away (c n))

/-- The value of `X_n`: `c_n⁻¹ (1 - ∑_{m ≠ n} c_m X_m)`. -/
noncomputable def hypSolvedVar : HypT c n :=
  C (IsLocalization.Away.invSelf (c n)) *
    (1 - ∑ m : {m : Fin f // m ≠ n}, C (algebraMap R (Localization.Away (c n)) (c m)) * X m)

/-- `X_m ↦ X_m` (`m ≠ n`), `X_n ↦ c_n⁻¹ (1 - ∑_{m ≠ n} c_m X_m)`. -/
noncomputable def hypSolveMap : MvPolynomial (Fin f) R →+* HypT c n :=
  eval₂Hom (C.comp (algebraMap R (Localization.Away (c n))))
    (fun m => if h : m = n then hypSolvedVar c n else X ⟨m, h⟩)

theorem hypSolveMap_linForm : hypSolveMap c n (hypLinForm c) = 1 := by
  classical
  rw [hypLinForm, map_sum, Fintype.sum_eq_add_sum_subtype_ne _ n]
  simp only [map_mul, hypSolveMap, eval₂Hom_C, eval₂Hom_X', RingHom.comp_apply, ↓reduceDIte]
  have hrest : ∀ m : {m : Fin f // m ≠ n},
      C (algebraMap R (Localization.Away (c n)) (c m)) * (if h : (m : Fin f) = n then hypSolvedVar c n
        else X ⟨m, h⟩) = C (algebraMap R (Localization.Away (c n)) (c m)) * X m := fun m => by
    rw [dif_neg m.2]
  try simp only [hrest]
  rw [hypSolvedVar, ← mul_assoc, ← map_mul,
    IsLocalization.Away.mul_invSelf, map_one, one_mul, sub_add_cancel]

/-- The induced map on the hypersurface ring. -/
noncomputable def hypSolveQuot : LinHypersurface c →+* HypT c n :=
  Ideal.Quotient.lift _ (hypSolveMap c n) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_sub, hypSolveMap_linForm, map_one, sub_self, mul_zero]

theorem hypSolveQuot_unit :
    IsUnit (hypSolveQuot c n (Ideal.Quotient.mk _ (C (c n)))) := by
  rw [hypSolveQuot, Ideal.Quotient.lift_mk, hypSolveMap, eval₂Hom_C, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit (c n)).map C

/-- `S[c_n⁻¹] → R[c_n⁻¹][X_m : m ≠ n]`. -/
noncomputable def hypSolveLoc :
    Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n))) →+* HypT c n :=
  IsLocalization.Away.lift _ (hypSolveQuot_unit c n)

/-- The coefficients `R[c_n⁻¹] → S[c_n⁻¹]`. -/
noncomputable def hypBackCoeff :
    Localization.Away (c n) →+* Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n))) :=
  IsLocalization.Away.lift (c n) (S := Localization.Away (c n))
    (g := (algebraMap (LinHypersurface c) (Localization.Away (Ideal.Quotient.mk _ (C (c n))))).comp
      ((Ideal.Quotient.mk _).comp C))
    (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n))))

/-- `R[c_n⁻¹][X_m : m ≠ n] → S[c_n⁻¹]`. -/
noncomputable def hypBackMap :
    HypT c n →+* Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n))) :=
  eval₂Hom (hypBackCoeff c n) fun m => algebraMap (LinHypersurface c) _ (Ideal.Quotient.mk _ (X m.1))

theorem hypBackCoeff_algebraMap (a : R) :
    hypBackCoeff c n (algebraMap R _ a)
      = algebraMap (LinHypersurface c) _ (Ideal.Quotient.mk _ (C a)) :=
  IsLocalization.Away.lift_eq _ _ a

theorem hypBackMap_solveLoc (x : Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n)))) :
    hypBackMap c n (hypSolveLoc c n x) = x := by
  classical
  have h : (hypBackMap c n).comp (hypSolveLoc c n) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n)))) ?_
    refine Ideal.Quotient.ringHom_ext (R := MvPolynomial (Fin f) R) (I := Ideal.span {hypLinForm c - 1}) ?_
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)
    · simp only [RingHom.comp_apply, hypSolveLoc, IsLocalization.Away.lift_eq, hypSolveQuot,
        Ideal.Quotient.lift_mk, hypSolveMap, eval₂Hom_C, hypBackMap, hypBackCoeff_algebraMap, RingHom.id_apply]
    · simp only [RingHom.comp_apply, hypSolveLoc, IsLocalization.Away.lift_eq, hypSolveQuot,
        Ideal.Quotient.lift_mk, hypSolveMap, eval₂Hom_X', RingHom.id_apply]
      by_cases hm : m = n
      · subst hm
        rw [dif_pos rfl, hypSolvedVar, map_mul, map_sub, map_one, map_sum, hypBackMap, eval₂Hom_C]
        simp only [map_mul, eval₂Hom_C, eval₂Hom_X', hypBackCoeff_algebraMap]
        -- in `S`, `c_n X_n = 1 - ∑_{m ≠ n} c_m X_m`
        have e : hypLinForm c = C (c m) * X m + ∑ x : {x : Fin f // x ≠ m}, C (c x) * X x.1 := by
          rw [hypLinForm, Fintype.sum_eq_add_sum_subtype_ne _ m]
        have hlin : Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1})
            (C (c m) * X m + ∑ x : {x : Fin f // x ≠ m}, C (c x) * X x.1) = 1 := by
          rw [← e]
          exact mk_hypLinForm c
        rw [map_add, map_sum] at hlin
        simp only [map_mul] at hlin
        have hsub : (1 : Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c m))))
            - ∑ x : {x : Fin f // x ≠ m}, algebraMap (LinHypersurface c) _ (Ideal.Quotient.mk _ (C (c x)))
              * algebraMap (LinHypersurface c) _ (Ideal.Quotient.mk _ (X x.1))
            = algebraMap (LinHypersurface c) _ (Ideal.Quotient.mk _ (C (c m)))
              * algebraMap (LinHypersurface c) _ (Ideal.Quotient.mk _ (X m)) := by
          have h2 := congrArg (algebraMap (LinHypersurface c)
            (Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c m))))) hlin
          simp only [map_add, map_sum, map_mul, map_one] at h2
          linear_combination -h2
        rw [hsub, ← mul_assoc]
        have hinv : hypBackCoeff c m (IsLocalization.Away.invSelf (c m))
            * algebraMap (LinHypersurface c) _ (Ideal.Quotient.mk _ (C (c m))) = 1 := by
          rw [← hypBackCoeff_algebraMap, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
        rw [hinv, one_mul]
      · rw [dif_neg hm, hypBackMap, eval₂Hom_X']
  exact DFunLike.congr_fun h x

theorem hypSolveLoc_backMap (y : HypT c n) : hypSolveLoc c n (hypBackMap c n y) = y := by
  have h : (hypSolveLoc c n).comp (hypBackMap c n) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun m => ?_)
    · have hc : (hypSolveLoc c n).comp (hypBackCoeff c n) = C := by
        refine IsLocalization.ringHom_ext (Submonoid.powers (c n)) (RingHom.ext fun b => ?_)
        simp only [RingHom.comp_apply, hypBackCoeff_algebraMap, hypSolveLoc, IsLocalization.Away.lift_eq,
          hypSolveQuot, Ideal.Quotient.lift_mk, hypSolveMap, eval₂Hom_C]
      rw [RingHom.comp_apply, hypBackMap, eval₂Hom_C, ← RingHom.comp_apply, hc, RingHom.id_apply]
    · rw [RingHom.comp_apply, hypBackMap, eval₂Hom_X', hypSolveLoc, IsLocalization.Away.lift_eq, hypSolveQuot,
        Ideal.Quotient.lift_mk, hypSolveMap, eval₂Hom_X', dif_neg m.2, RingHom.id_apply]
  exact DFunLike.congr_fun h y

/-- **Solving for `X_n`**: `S[c_n⁻¹] ≃ R[c_n⁻¹][X_m : m ≠ n]`. -/
noncomputable def hypersurfaceLocEquiv :
    Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n))) ≃+* HypT c n :=
  RingEquiv.ofRingHom (hypSolveLoc c n) (hypBackMap c n)
    (RingHom.ext (hypSolveLoc_backMap c n)) (RingHom.ext (hypBackMap_solveLoc c n))

end Solve

/-! ## Smoothness -/

theorem smooth_algebraMap_hypT {K : Type u} [CommRing K] [Algebra K R] (hR : (algebraMap K R).Smooth)
    (n : Fin f) : (algebraMap K (HypT c n)).Smooth := by
  have h1 : (algebraMap R (Localization.Away (c n))).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway _ (c n)
  haveI : Algebra.Smooth (Localization.Away (c n)) (HypT c n) := {}
  have h2 : (algebraMap (Localization.Away (c n)) (HypT c n)).Smooth :=
    RingHom.smooth_algebraMap.mpr inferInstance
  have heq : algebraMap K (HypT c n)
      = (algebraMap (Localization.Away (c n)) (HypT c n)).comp
          ((algebraMap R (Localization.Away (c n))).comp (algebraMap K R)) := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  rw [heq]
  exact RingHom.Smooth.comp (RingHom.Smooth.comp hR h1) h2

/-- **The hypersurface `∑ c_m X_m = 1` is smooth over `K`** whenever `R` is. -/
theorem hypersurface_smooth {K : Type u} [CommRing K] [Algebra K R] (hR : (algebraMap K R).Smooth) :
    (algebraMap K (LinHypersurface c)).Smooth := by
  refine RingHom.Smooth.ofLocalizationSpanTarget (algebraMap K (LinHypersurface c)) _
    (span_hypCoeffs_eq_top c) ?_
  rintro ⟨_, n, rfl⟩
  have heq : (algebraMap (LinHypersurface c) (Localization.Away
        (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n))))).comp (algebraMap K (LinHypersurface c))
      = (hypersurfaceLocEquiv c n).symm.toRingHom.comp (algebraMap K (HypT c n)) := by
    refine RingHom.ext fun k => ?_
    change _ = hypBackMap c n (algebraMap K (HypT c n) k)
    rw [MvPolynomial.algebraMap_apply, hypBackMap, eval₂Hom_C, IsScalarTower.algebraMap_apply K R,
      hypBackCoeff_algebraMap]
    rfl
  rw [heq]
  exact RingHom.Smooth.comp (smooth_algebraMap_hypT c hR n)
    (RingHom.Smooth.of_bijective (hypersurfaceLocEquiv c n).symm.bijective)

/-! ## Integrality -/

theorem constantCoeff_hypLinForm : MvPolynomial.constantCoeff (hypLinForm c) = 0 := by
  simp [hypLinForm]

section Domain

variable [IsDomain R]

/-- **The coefficients are nonzerodivisors on the hypersurface.**  Modulo `c_n` the equation
`∑ c_m X_m - 1` has constant coefficient `-1`, so it is a unit among power series; hence a relation
`h c_n = q (∑ c_m X_m - 1)` forces `c_n ∣ q`. -/
theorem hyp_mk_C_mem_nonZeroDivisors {n : Fin f} (hc : c n ≠ 0) :
    Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n)) ∈ nonZeroDivisors (LinHypersurface c) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hy
  obtain ⟨q, hq⟩ := hy
  set π := MvPolynomial.map (R := R) (σ := Fin f) (Ideal.Quotient.mk (Ideal.span {c n}))
  have h1 : π q * π (hypLinForm c - 1) = 0 := by
    rw [← map_mul, hq, map_mul, MvPolynomial.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self (c n)), map_zero, mul_zero]
  have hunit : IsUnit ((π (hypLinForm c - 1) : MvPowerSeries (Fin f) (R ⧸ Ideal.span {c n}))) := by
    have e : MvPowerSeries.constantCoeff ((π (hypLinForm c - 1) : MvPowerSeries (Fin f) _))
        = MvPolynomial.constantCoeff (π (hypLinForm c - 1)) := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
        MvPolynomial.constantCoeff_eq]
    rw [MvPowerSeries.isUnit_iff_constantCoeff, e, MvPolynomial.constantCoeff_map,
      map_sub, constantCoeff_hypLinForm, map_one, zero_sub, map_neg, map_one]
    exact isUnit_one.neg
  have h2 : π q = 0 := by
    rw [← MvPolynomial.coe_eq_zero_iff]
    refine hunit.mul_left_eq_zero.mp ?_
    rw [← MvPolynomial.coe_mul, h1, MvPolynomial.coe_zero]
  have h3 : q ∈ Ideal.span {(C (c n) : MvPolynomial (Fin f) R)} := by
    have : q ∈ RingHom.ker π := h2
    rwa [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at this
  obtain ⟨q', rfl⟩ := Ideal.mem_span_singleton.mp h3
  have hC : (C (c n) : MvPolynomial (Fin f) R) ≠ 0 := by rwa [Ne, MvPolynomial.C_eq_zero]
  have h4 : h = q' * (hypLinForm c - 1) := by
    refine mul_right_cancel₀ hC ?_
    rw [← hq]
    ring
  rw [h4, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem hypT_isDomain {n : Fin f} (hc : c n ≠ 0) : IsDomain (HypT c n) := by
  haveI : IsDomain (Localization.Away (c n)) := IsLocalization.Away.isDomain (S := Localization.Away (c n)) hc
  infer_instance

/-- **The hypersurface is a domain** when some coefficient is nonzero. -/
theorem hypersurface_isDomain {n : Fin f} (hc : c n ≠ 0) : IsDomain (LinHypersurface c) := by
  haveI := hypT_isDomain c hc
  have hinj : Function.Injective (algebraMap (LinHypersurface c)
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1}) (C (c n))))) :=
    IsLocalization.injective _ (Submonoid.powers_le.mpr (hyp_mk_C_mem_nonZeroDivisors c hc))
  exact Function.Injective.isDomain ((hypersurfaceLocEquiv c n).toRingHom.comp (algebraMap _ _))
    ((hypersurfaceLocEquiv c n).injective.comp hinj)

/-- **The coefficient ring embeds in the hypersurface** when some coefficient is nonzero. -/
theorem hypersurface_C_injective {n : Fin f} (hc : c n ≠ 0) :
    Function.Injective ((Ideal.Quotient.mk (Ideal.span {hypLinForm c - 1})).comp (C : R →+* _)) := by
  have hloc : Function.Injective (algebraMap R (Localization.Away (c n))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
  intro a b hab
  have := congrArg (fun x => hypersurfaceLocEquiv c n (algebraMap _ _ x)) hab
  simp only [RingHom.comp_apply, hypersurfaceLocEquiv, RingEquiv.ofRingHom_apply, hypSolveLoc,
    IsLocalization.Away.lift_eq, hypSolveQuot, Ideal.Quotient.lift_mk, hypSolveMap, eval₂Hom_C] at this
  exact hloc (MvPolynomial.C_injective _ _ this)

end Domain

end HTGeometry
