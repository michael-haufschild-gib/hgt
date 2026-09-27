import GaloisForLFunctions.HTGeometry.FirstOrderWimanRootBaseChange

/-!
# Inverses, strict degree comparison and exponent dilation for boundary coefficients

Complements to the `HasLead` calculus of Laurent series over a field:

* a nonzero series has a boundary coefficient at its order, and the inverse of a series with
  boundary coefficient `c ≠ 0` in degree `d` has boundary coefficient `c⁻¹` in degree `-d`;
* adding a series that vanishes up to degree `d` does not change a boundary coefficient in
  degree `d`;
* the dilation `t ↦ tᵐ` of `F((t))` multiplies degrees by `m` and keeps boundary coefficients.
-/

open HahnSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F]

theorem hasLead_single (d : ℤ) (c : F) : HasLead (single d c : LaurentSeries F) d c :=
  ⟨fun k hk => by rw [coeff_single, if_neg (by omega)], by rw [coeff_single_same]⟩

theorem hasLead_C (c : F) : HasLead (HahnSeries.C c : LaurentSeries F) 0 c := by
  rw [C_apply]
  exact hasLead_single 0 c

theorem HasLead.unique {f : LaurentSeries F} {d : ℤ} {c c' : F} (h : HasLead f d c)
    (h' : HasLead f d c') : c = c' :=
  h.2.symm.trans h'.2

theorem HasLead.ne_zero {f : LaurentSeries F} {d : ℤ} {c : F} (hf : HasLead f d c) (hc : c ≠ 0) :
    f ≠ 0 := by
  rintro rfl
  exact hc (hf.2.symm.trans (HahnSeries.coeff_zero))

/-- Adding a series that vanishes up to degree `d` keeps the boundary coefficient in degree `d`. -/
theorem HasLead.add_of_vanishing {f g : LaurentSeries F} {d : ℤ} {c : F} (hf : HasLead f d c)
    (hg : ∀ k ≤ d, g.coeff k = 0) : HasLead (f + g) d c := by
  have h := hf.add (⟨fun k hk => hg k hk.le, hg d le_rfl⟩ : HasLead g d 0)
  rwa [add_zero] at h

/-- A series with a boundary coefficient in a larger degree vanishes up to any smaller degree. -/
theorem HasLead.vanishing_le {g : LaurentSeries F} {e d : ℤ} {c : F} (hg : HasLead g e c)
    (hde : d < e) : ∀ k ≤ d, g.coeff k = 0 :=
  fun k hk => hg.1 k (by omega)

/-- A nonzero series has its boundary coefficient at its order. -/
theorem hasLead_order (f : LaurentSeries F) :
    HasLead f f.order (f.coeff f.order) :=
  ⟨fun _ hk => coeff_eq_zero_of_lt_order hk, rfl⟩

theorem HasLead.mul_const {f : LaurentSeries F} {d : ℤ} {c : F} (hf : HasLead f d c) (a : F) :
    HasLead (HahnSeries.C a * f) d (a * c) := by
  have h := (hasLead_C a).mul hf
  rwa [zero_add] at h

/-- **Boundary coefficient of an inverse.** -/
theorem HasLead.inv {f : LaurentSeries F} {d : ℤ} {c : F} (hf : HasLead f d c) (hc : c ≠ 0) :
    HasLead f⁻¹ (-d) c⁻¹ := by
  have hf0 := hf.ne_zero hc
  have hi0 : f⁻¹ ≠ 0 := inv_ne_zero hf0
  have hi := hasLead_order f⁻¹
  have hlc : (f⁻¹).coeff (f⁻¹).order ≠ 0 := mt coeff_order_eq_zero.mp hi0
  have hprod := hf.mul hi
  rw [mul_inv_cancel₀ hf0] at hprod
  have hcoeff := hprod.2
  have hd : d + (f⁻¹).order = 0 := by
    by_contra hne
    rw [coeff_one, if_neg hne] at hcoeff
    exact mul_ne_zero hc hlc hcoeff.symm
  rw [hd, coeff_one, if_pos rfl] at hcoeff
  have horder : (f⁻¹).order = -d := by omega
  have hval : (f⁻¹).coeff (f⁻¹).order = c⁻¹ := eq_inv_of_mul_eq_one_right hcoeff.symm
  rw [horder] at hi hval
  rw [hval] at hi
  exact hi

/-- **Boundary coefficient of a quotient of two series of the same degree.** -/
theorem HasLead.mul_inv_of_same {f g : LaurentSeries F} {d : ℤ} {c c' : F} (hg : HasLead g d c')
    (hf : HasLead f d c) (hc : c ≠ 0) : HasLead (g * f⁻¹) 0 (c' * c⁻¹) := by
  have h := hg.mul (hf.inv hc)
  rwa [add_neg_cancel] at h

/-- A power series has its constant term as boundary coefficient in degree zero. -/
theorem hasLead_ofPowerSeries (z : PowerSeries F) :
    HasLead (HahnSeries.ofPowerSeries ℤ F z) 0 (PowerSeries.constantCoeff z) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · change ((z : PowerSeries F) : LaurentSeries F).coeff k = 0
    rw [PowerSeries.coeff_coe, if_pos hk]
  · change ((z : PowerSeries F) : LaurentSeries F).coeff 0 = _
    rw [PowerSeries.coeff_coe, if_neg (lt_irrefl 0), Int.natAbs_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-! ## Exponent dilation -/

/-- The dilation `t ↦ tᵐ` of `F((t))`. -/
def laurentExpand (m : ℕ) (hm : m ≠ 0) : LaurentSeries F →+* LaurentSeries F :=
  embDomainRingHom (mulExponent m) (mulExponent_injective hm) (mulExponent_le_iff hm)

theorem laurentExpand_coeff_mul {m : ℕ} (hm : m ≠ 0) (x : LaurentSeries F) (n : ℤ) :
    (laurentExpand m hm x).coeff ((m : ℤ) * n) = x.coeff n :=
  HahnSeries.embDomain_coeff (a := n)

theorem laurentExpand_coeff_of_not_mem {m : ℕ} (hm : m ≠ 0) (x : LaurentSeries F) (k : ℤ)
    (hk : ∀ n : ℤ, (m : ℤ) * n ≠ k) : (laurentExpand m hm x).coeff k = 0 := by
  change (embDomain _ x).coeff k = 0
  apply embDomain_notin_range
  rintro ⟨n, hn⟩
  exact hk n hn

theorem laurentExpand_C {m : ℕ} (hm : m ≠ 0) (c : F) :
    laurentExpand m hm (HahnSeries.C c) = HahnSeries.C c :=
  embDomainRingHom_C

theorem laurentExpand_single {m : ℕ} (hm : m ≠ 0) (e : ℤ) (c : F) :
    laurentExpand m hm (single e c) = single ((m : ℤ) * e) c := by
  change embDomain _ (single e c) = _
  rw [embDomain_single]
  rfl

theorem laurentExpand_algebraMap [Algebra ℂ F] {m : ℕ} (hm : m ≠ 0) (c : ℂ) :
    laurentExpand m hm (algebraMap ℂ (LaurentSeries F) c) = algebraMap ℂ (LaurentSeries F) c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
  exact laurentExpand_C hm _

theorem HasLead.laurentExpand {m : ℕ} (hm : m ≠ 0) {x : LaurentSeries F} {d : ℤ} {c : F}
    (hx : HasLead x d c) : HasLead (laurentExpand m hm x) ((m : ℤ) * d) c := by
  have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  refine ⟨fun k hk => ?_, by rw [laurentExpand_coeff_mul, hx.2]⟩
  by_cases hkm : ∃ n : ℤ, (m : ℤ) * n = k
  · obtain ⟨n, rfl⟩ := hkm
    rw [laurentExpand_coeff_mul, hx.1 n (lt_of_mul_lt_mul_left hk hmpos.le)]
  · push Not at hkm
    exact laurentExpand_coeff_of_not_mem hm _ _ hkm

end

end GaloisForLFunctions.HTGeometry
