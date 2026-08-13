import GaloisForLFunctions.RHTower.FieldOneFiniteStageIdeleClassSplitting
import GaloisForLFunctions.RHTower.FieldOneLocalHaarModule
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Compactness of finite-stage module-one idele classes

This file proves the compactness assertion used in the Connes--Marcolli
finite-stage decomposition of the rational semilocal idele-class group.
Each local idele is normalized by a unique integral valuation power up to a
norm-one factor.  The matching diagonal rational prime powers lie in the
`S`-unit subgroup, so every module-one idele class has a representative in a
finite product of compact local norm-one groups.  Surjectivity of this compact
torus parametrization proves compactness of the full module-one class group.
-/

open scoped NNReal BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-- Every rational local idele splits into a norm-one unit and an integral
power of the rational prime uniformizer. -/
theorem fieldOneAdic_exists_normOne_decomposition
    (v : HeightOneSpectrum ℤ) (a : (v.adicCompletion ℚ)ˣ) :
    ∃ b : (v.adicCompletion ℚ)ˣ, ∃ n : ℤ,
      ‖(b : v.adicCompletion ℚ)‖ = 1 ∧
        a = b *
          (fieldOneRationalLocalUnit v
            (fieldOneRationalPrimeUnit v)) ^ n := by
  let q : ℕ := Rat.HeightOneSpectrum.primesEquiv v
  letI : Fact q.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let e := Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
  let P : (v.adicCompletion ℚ)ˣ :=
    fieldOneRationalLocalUnit v
      (fieldOneRationalPrimeUnit v)
  let n : ℤ := (e (a : v.adicCompletion ℚ)).valuation
  let b : (v.adicCompletion ℚ)ˣ := a * P ^ (-n)
  have hea0 : e (a : v.adicCompletion ℚ) ≠ 0 := by
    exact (map_ne_zero e).mpr (Units.ne_zero a)
  have hPmap : e (P : v.adicCompletion ℚ) = (q : ℚ_[q]) := by
    change
      e (algebraMap ℚ (v.adicCompletion ℚ)
        (Rat.HeightOneSpectrum.primesEquiv v : ℚ)) =
        (q : ℚ_[q])
    simp [q]
  have hPzpow :
      e ((P : v.adicCompletion ℚ) ^ (-n)) =
        (q : ℚ_[q]) ^ (-n) := by
    have hPmap' :
        e.toAlgEquiv.toRingEquiv (P : v.adicCompletion ℚ) =
          (q : ℚ_[q]) :=
      hPmap
    change
      e.toAlgEquiv.toRingEquiv
          ((P : v.adicCompletion ℚ) ^ (-n)) =
        (q : ℚ_[q]) ^ (-n)
    rw [map_zpow₀, hPmap']
  have heb :
      e (b : v.adicCompletion ℚ) =
        e (a : v.adicCompletion ℚ) *
          (q : ℚ_[q]) ^ (-n) := by
    dsimp [b]
    rw [Units.val_zpow_eq_zpow_val]
    rw [map_mul, hPzpow]
  have hnormea :
      ‖e (a : v.adicCompletion ℚ)‖ =
        (q : ℝ) ^ (-n) := by
    exact Padic.norm_eq_zpow_neg_valuation hea0
  have hnormeb : ‖e (b : v.adicCompletion ℚ)‖ = 1 := by
    rw [heb, norm_mul, hnormea, Padic.norm_p_zpow]
    rw [← zpow_add₀]
    · simp
    · exact_mod_cast
        (Rat.HeightOneSpectrum.primesEquiv v).property.ne_zero
  have hnormb : ‖(b : v.adicCompletion ℚ)‖ = 1 := by
    have hb_le : ‖(b : v.adicCompletion ℚ)‖ ≤ 1 :=
      (fieldOneAdic_padicEquiv_norm_le_one_iff
        v (b : v.adicCompletion ℚ)).mp hnormeb.le
    have hbinv_le :
        ‖((b⁻¹ : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ)‖ ≤ 1 := by
      apply
        (fieldOneAdic_padicEquiv_norm_le_one_iff
          v ((b⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ)).mp
      rw [show
        e (((b⁻¹ : (v.adicCompletion ℚ)ˣ) :
            v.adicCompletion ℚ)) =
          (e (b : v.adicCompletion ℚ))⁻¹ by simp]
      rw [norm_inv, hnormeb]
      simp
    have hb0 : ‖(b : v.adicCompletion ℚ)‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr (Units.ne_zero b)
    have hbinv_le' : ‖(b : v.adicCompletion ℚ)‖⁻¹ ≤ 1 := by
      simpa using hbinv_le
    have hone_le : 1 ≤ ‖(b : v.adicCompletion ℚ)‖ := by
      calc
        1 = ‖(b : v.adicCompletion ℚ)‖ *
              ‖(b : v.adicCompletion ℚ)‖⁻¹ :=
          (mul_inv_cancel₀ hb0).symm
        _ ≤ ‖(b : v.adicCompletion ℚ)‖ * 1 :=
          mul_le_mul_of_nonneg_left hbinv_le'
            (norm_nonneg _)
        _ = ‖(b : v.adicCompletion ℚ)‖ := mul_one _
    exact le_antisymm hb_le hone_le
  have hdecomp : a = b * P ^ n := by
    dsimp [b]
    rw [mul_assoc, ← zpow_add]
    simp
  exact ⟨b, n, hnormb, hdecomp⟩

/-- Chosen norm-one local factor. -/
def fieldOneAdicNormOnePart (v : HeightOneSpectrum ℤ)
    (a : (v.adicCompletion ℚ)ˣ) : (v.adicCompletion ℚ)ˣ :=
  Classical.choose (fieldOneAdic_exists_normOne_decomposition v a)

/-- Chosen integral uniformizer exponent. -/
def fieldOneAdicExponent (v : HeightOneSpectrum ℤ)
    (a : (v.adicCompletion ℚ)ˣ) : ℤ :=
  Classical.choose
    (Classical.choose_spec (fieldOneAdic_exists_normOne_decomposition v a))

theorem fieldOneAdicNormOnePart_norm (v : HeightOneSpectrum ℤ)
    (a : (v.adicCompletion ℚ)ˣ) :
    ‖(fieldOneAdicNormOnePart v a : v.adicCompletion ℚ)‖ = 1 :=
  (Classical.choose_spec
    (Classical.choose_spec
      (fieldOneAdic_exists_normOne_decomposition v a))).1

theorem fieldOneAdic_decomposition (v : HeightOneSpectrum ℤ)
    (a : (v.adicCompletion ℚ)ˣ) :
    a = fieldOneAdicNormOnePart v a *
      (fieldOneRationalLocalUnit v
        (fieldOneRationalPrimeUnit v)) ^
          fieldOneAdicExponent v a :=
  (Classical.choose_spec
    (Classical.choose_spec
      (fieldOneAdic_exists_normOne_decomposition v a))).2

def fieldOneAdicNormOneSubgroup (v : HeightOneSpectrum ℤ) :
    Subgroup (v.adicCompletion ℚ)ˣ where
  carrier := {u | ‖(u : v.adicCompletion ℚ)‖ = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ‖(a : v.adicCompletion ℚ)‖ = 1 at ha
    change ‖(b : v.adicCompletion ℚ)‖ = 1 at hb
    change ‖((a * b : (v.adicCompletion ℚ)ˣ) :
      v.adicCompletion ℚ)‖ = 1
    rw [Units.val_mul, norm_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simpa [norm_inv, ha]

abbrev FieldOneAdicNormOneUnits (v : HeightOneSpectrum ℤ) :=
  fieldOneAdicNormOneSubgroup v

def fieldOneAdicNormOneUnitsSphereHomeomorph (v : HeightOneSpectrum ℤ) :
    FieldOneAdicNormOneUnits v ≃ₜ
      {x : v.adicCompletion ℚ // ‖x‖ = 1} where
  toFun u := ⟨u.1.1, u.2⟩
  invFun x :=
    ⟨Units.mk0 x.1 (by
      intro h
      have hx := x.property
      rw [h, norm_zero] at hx
      norm_num at hx), x.2⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv x := rfl
  continuous_toFun := by
    exact Continuous.subtype_mk
      (Units.continuous_val.comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    · have hconj : Continuous
          (fun x : {x : v.adicCompletion ℚ // ‖x‖ = 1} => x.1⁻¹) := by
        apply continuous_iff_continuousAt.2
        intro x
        have hx0 : x.1 ≠ 0 := by
          intro hx
          have hxnorm := x.property
          rw [hx, norm_zero] at hxnorm
          norm_num at hxnorm
        exact (continuousAt_inv₀ hx0).comp
          continuous_subtype_val.continuousAt
      simpa using hconj

theorem fieldOneAdicNormOneSphere_isCompact (v : HeightOneSpectrum ℤ) :
    IsCompact {x : v.adicCompletion ℚ | ‖x‖ = 1} := by
  have hclosed : IsClosed {x : v.adicCompletion ℚ | ‖x‖ = 1} :=
    isClosed_eq continuous_norm continuous_const
  have hsub :
      {x : v.adicCompletion ℚ | ‖x‖ = 1} ⊆
        Metric.closedBall 0 1 := by
    intro x hx
    simpa [Metric.mem_closedBall] using le_of_eq hx
  exact (isCompact_closedBall 0 1).of_isClosed_subset hclosed hsub

instance fieldOneAdicNormOneUnitsCompactSpace (v : HeightOneSpectrum ℤ) :
    CompactSpace (FieldOneAdicNormOneUnits v) := by
  letI : CompactSpace {x : v.adicCompletion ℚ // ‖x‖ = 1} :=
    isCompact_iff_compactSpace.mp (fieldOneAdicNormOneSphere_isCompact v)
  exact (fieldOneAdicNormOneUnitsSphereHomeomorph v).symm.compactSpace

abbrev FieldOneFiniteStageNormOneTorus (S : Finset (HeightOneSpectrum ℤ)) :=
  (v : ↥S) → FieldOneAdicNormOneUnits v.1

def fieldOneFiniteStageNormOneTorusIdele (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageNormOneTorus S →* FieldOneFiniteStageIdele S where
  toFun k := (1, fun v => (k v).1)
  map_one' := rfl
  map_mul' k l := by
    apply Prod.ext
    · simp
    · funext v
      apply Units.ext
      rfl

def fieldOneFiniteStageNormOneTorusToModuleOne (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageNormOneTorus S →* FieldOneFiniteStageModuleOneClass S where
  toFun k := ⟨QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S k), by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    change fieldOneFiniteStageModule S (fieldOneFiniteStageNormOneTorusIdele S k) = 1
    change ‖(1 : ℝ)‖₊ *
        ∏ v : ↥S,
          ‖(((k v).1 : (v.1.adicCompletion ℚ)ˣ) :
            v.1.adicCompletion ℚ)‖₊ = 1
    simp only [nnnorm_one, one_mul]
    apply Finset.prod_eq_one
    intro v _
    apply NNReal.eq
    exact (k v).2⟩
  map_one' := by
    apply Subtype.ext
    change QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S 1) = 1
    exact QuotientGroup.mk_one (fieldOneFiniteStageSUnitImage S)
  map_mul' k l := by
    apply Subtype.ext
    change QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S (k * l)) =
      QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S k) *
        QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S l)
    rw [map_mul]
    exact QuotientGroup.mk_mul (fieldOneFiniteStageSUnitImage S) _ _

theorem fieldOneFiniteStageNormOneTorusToModuleOne_continuous
    (S : Finset (HeightOneSpectrum ℤ)) :
    Continuous (fieldOneFiniteStageNormOneTorusToModuleOne S) := by
  change Continuous fun k : FieldOneFiniteStageNormOneTorus S =>
    (⟨QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S k), by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      change fieldOneFiniteStageModule S (fieldOneFiniteStageNormOneTorusIdele S k) = 1
      change ‖(1 : ℝ)‖₊ *
          ∏ v : ↥S,
            ‖(((k v).1 : (v.1.adicCompletion ℚ)ˣ) :
              v.1.adicCompletion ℚ)‖₊ = 1
      simp only [nnnorm_one, one_mul]
      apply Finset.prod_eq_one
      intro v _
      apply NNReal.eq
      exact (k v).2⟩ :
      FieldOneFiniteStageModuleOneClass S)
  apply Continuous.subtype_mk
  apply continuous_quotient_mk'.comp
  apply Continuous.prodMk
  · exact continuous_const
  · apply continuous_pi
    intro v
    change Continuous fun k : FieldOneFiniteStageNormOneTorus S =>
      ((k v).1 : (v.1.adicCompletion ℚ)ˣ)
    exact continuous_subtype_val.comp
      (continuous_apply v : Continuous
        (fun k : FieldOneFiniteStageNormOneTorus S => k v))

def fieldOneFiniteStageGlobalNormalizer (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) : FieldOneFiniteStageIdele S :=
  ∏ v : ↥S,
    fieldOneFiniteStageDiagonalUnit S
      (fieldOneRationalPrimeUnit v.1) ^
        (-fieldOneAdicExponent v.1 (u.2 v))

theorem fieldOneFiniteStageGlobalNormalizer_mem_sUnitImage
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    fieldOneFiniteStageGlobalNormalizer S u ∈ fieldOneFiniteStageSUnitImage S := by
  classical
  apply Subgroup.prod_mem
  intro v _
  apply Subgroup.zpow_mem
  exact fieldOneFiniteStageDiagonalUnit_mem_sUnitImage S
    ⟨fieldOneRationalPrimeUnit v.1,
      fieldOne_prime_mem_sUnitSubgroup S v⟩

theorem fieldOneFiniteStageGlobalNormalized_local_norm
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) (v : ↥S) :
    ‖((((fieldOneFiniteStageGlobalNormalizer S u * u).2 v) :
      (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ)‖ = 1 := by
  classical
  dsimp [fieldOneFiniteStageGlobalNormalizer]
  change ‖((((∏ w : ↥S,
      fieldOneFiniteStageDiagonalUnit S
        (fieldOneRationalPrimeUnit w.1) ^
          (-fieldOneAdicExponent w.1 (u.2 w))) :
        FieldOneFiniteStageIdele S).2 v * u.2 v :
          (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ)‖ = 1
  rw [show
    ((∏ w : ↥S,
      fieldOneFiniteStageDiagonalUnit S
        (fieldOneRationalPrimeUnit w.1) ^
          (-fieldOneAdicExponent w.1 (u.2 w))) :
        FieldOneFiniteStageIdele S).2 v =
      ∏ w : ↥S,
        fieldOneRationalLocalUnit v.1
          (fieldOneRationalPrimeUnit w.1) ^
            (-fieldOneAdicExponent w.1 (u.2 w)) by
      change ((MonoidHom.snd ℝˣ
        ((v : ↥S) → (v.1.adicCompletion ℚ)ˣ))
          (∏ w : ↥S,
            fieldOneFiniteStageDiagonalUnit S
              (fieldOneRationalPrimeUnit w.1) ^
                (-fieldOneAdicExponent w.1 (u.2 w)))) v = _
      rw [map_prod, Finset.prod_apply]
      apply Finset.prod_congr rfl
      intro w _
      rfl]
  rw [Units.val_mul, norm_mul]
  rw [show
    (((∏ w : ↥S,
      fieldOneRationalLocalUnit v.1
        (fieldOneRationalPrimeUnit w.1) ^
          (-fieldOneAdicExponent w.1 (u.2 w))) :
        (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) =
      ∏ w : ↥S,
        (((fieldOneRationalLocalUnit v.1
          (fieldOneRationalPrimeUnit w.1) ^
            (-fieldOneAdicExponent w.1 (u.2 w))) :
          (v.1.adicCompletion ℚ)ˣ) : v.1.adicCompletion ℚ) by
    exact map_prod (Units.coeHom (v.1.adicCompletion ℚ)) _ Finset.univ]
  rw [norm_prod]
  rw [Finset.prod_eq_single v]
  · set n : ℤ := fieldOneAdicExponent v.1 (u.2 v)
    have hdec : u.2 v = fieldOneAdicNormOnePart v.1 (u.2 v) *
        (fieldOneRationalLocalUnit v.1
          (fieldOneRationalPrimeUnit v.1)) ^ n := by
      simpa [n] using fieldOneAdic_decomposition v.1 (u.2 v)
    rw [hdec]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul]
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_zpow]
    rw [fieldOneAdicNormOnePart_norm, one_mul]
    rw [← zpow_add₀]
    simp
    exact norm_ne_zero_iff.mpr (Units.ne_zero _)
  · intro w _ hwv
    rw [Units.val_zpow_eq_zpow_val, norm_zpow]
    have hnorm := fieldOneRationalPrimeUnit_localNorm_of_ne
      w.1 v.1 (fun h => hwv (Subtype.ext h.symm))
    change
      ‖algebraMap ℚ (v.1.adicCompletion ℚ)
        (Rat.HeightOneSpectrum.primesEquiv w.1 : ℚ)‖ ^
          (-fieldOneAdicExponent w.1 (u.2 w)) = 1
    rw [hnorm]
    simp
  · simp

def fieldOneFiniteStageDiagonalNegOne (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdele S :=
  fieldOneFiniteStageDiagonalUnit S (-1)

theorem fieldOneFiniteStageDiagonalNegOne_mem_sUnitImage (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageDiagonalNegOne S ∈ fieldOneFiniteStageSUnitImage S :=
  fieldOneFiniteStageDiagonalUnit_mem_sUnitImage S
    ⟨-1, fieldOne_negOne_mem_sUnitSubgroup S⟩

theorem fieldOneFiniteStageNormOneTorusToModuleOne_surjective
    (S : Finset (HeightOneSpectrum ℤ)) :
    Function.Surjective (fieldOneFiniteStageNormOneTorusToModuleOne S) := by
  classical
  intro c
  rcases c with ⟨c, hc⟩
  revert hc
  refine Quotient.inductionOn' c ?_
  intro u hu
  let h : FieldOneFiniteStageIdele S := fieldOneFiniteStageGlobalNormalizer S u
  let w : FieldOneFiniteStageIdele S := h * u
  have hhmem : h ∈ fieldOneFiniteStageSUnitImage S :=
    fieldOneFiniteStageGlobalNormalizer_mem_sUnitImage S u
  have hmodh : fieldOneFiniteStageModule S h = 1 :=
    fieldOneFiniteStageSUnitImage_le_moduleKernel S hhmem
  have hmodu : fieldOneFiniteStageModule S u = 1 := by
    rw [MonoidHom.mem_ker] at hu
    have hval := congrArg Units.val hu
    change fieldOneFiniteStageIdeleClassModule S
      (QuotientGroup.mk'
        (fieldOneFiniteStageSUnitImage S) u) = 1 at hval
    rw [fieldOneFiniteStageIdeleClassModule_mk] at hval
    exact hval
  have hmodw : fieldOneFiniteStageModule S w = 1 := by
    rw [show w = h * u from rfl, map_mul, hmodh, hmodu, one_mul]
  have hlocal (v : ↥S) :
      ‖((w.2 v : (v.1.adicCompletion ℚ)ˣ) :
        v.1.adicCompletion ℚ)‖ = 1 :=
    fieldOneFiniteStageGlobalNormalized_local_norm S u v
  have hprod :
      ∏ v : ↥S,
        ‖((w.2 v : (v.1.adicCompletion ℚ)ˣ) :
          v.1.adicCompletion ℚ)‖₊ = 1 := by
    apply Finset.prod_eq_one
    intro v _
    apply NNReal.eq
    exact hlocal v
  have hrealnn : ‖((w.1 : ℝˣ) : ℝ)‖₊ = 1 := by
    change ‖((w.1 : ℝˣ) : ℝ)‖₊ *
      ∏ v : ↥S,
        ‖((w.2 v : (v.1.adicCompletion ℚ)ˣ) :
          v.1.adicCompletion ℚ)‖₊ = 1 at hmodw
    rw [hprod, mul_one] at hmodw
    exact hmodw
  have hrealnorm : ‖((w.1 : ℝˣ) : ℝ)‖ = 1 :=
    congrArg (fun x : ℝ≥0 => (x : ℝ)) hrealnn
  have hclassw :
      (QuotientGroup.mk w : FieldOneFiniteStageIdeleClassGroup S) =
        QuotientGroup.mk u := by
    rw [show w = h * u from rfl, QuotientGroup.mk_mul]
    have hmk : (QuotientGroup.mk h :
        FieldOneFiniteStageIdeleClassGroup S) = 1 :=
      (QuotientGroup.eq_one_iff h).mpr hhmem
    rw [hmk, one_mul]
  rcases le_total 0 ((w.1 : ℝˣ) : ℝ) with hwpos | hwneg
  · have hwreal : ((w.1 : ℝˣ) : ℝ) = 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hwpos] at hrealnorm
      exact hrealnorm
    let k : FieldOneFiniteStageNormOneTorus S :=
      fun v => ⟨w.2 v, hlocal v⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    change
      (QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S k) :
        FieldOneFiniteStageIdeleClassGroup S) = QuotientGroup.mk u
    rw [← hclassw]
    congr 1
    apply Prod.ext
    · apply Units.ext
      exact hwreal.symm
    · rfl
  · let d : FieldOneFiniteStageIdele S := fieldOneFiniteStageDiagonalNegOne S
    let w' : FieldOneFiniteStageIdele S := d * w
    have hdmem : d ∈ fieldOneFiniteStageSUnitImage S :=
      fieldOneFiniteStageDiagonalNegOne_mem_sUnitImage S
    have hwreal : ((w.1 : ℝˣ) : ℝ) = -1 := by
      rw [Real.norm_eq_abs, abs_of_nonpos hwneg] at hrealnorm
      linarith
    have hdreal : ((d.1 : ℝˣ) : ℝ) = -1 := by
      dsimp [d, fieldOneFiniteStageDiagonalNegOne,
        fieldOneFiniteStageDiagonalUnit,
        fieldOneRationalRealUnit]
      norm_num
    have hw'real : ((w'.1 : ℝˣ) : ℝ) = 1 := by
      change (((d.1 * w.1 : ℝˣ) : ℝ)) = 1
      rw [Units.val_mul]
      rw [hdreal, hwreal]
      norm_num
    have hw'local (v : ↥S) :
        ‖((w'.2 v : (v.1.adicCompletion ℚ)ˣ) :
          v.1.adicCompletion ℚ)‖ = 1 := by
      change
        ‖algebraMap ℚ (v.1.adicCompletion ℚ) (-1) *
          ((w.2 v : (v.1.adicCompletion ℚ)ˣ) :
            v.1.adicCompletion ℚ)‖ = 1
      rw [norm_mul, hlocal]
      simp
    have hclassw' :
        (QuotientGroup.mk w' : FieldOneFiniteStageIdeleClassGroup S) =
          QuotientGroup.mk u := by
      rw [show w' = d * w from rfl, QuotientGroup.mk_mul]
      have hmk : (QuotientGroup.mk d :
          FieldOneFiniteStageIdeleClassGroup S) = 1 :=
        (QuotientGroup.eq_one_iff d).mpr hdmem
      rw [hmk, one_mul, hclassw]
    let k : FieldOneFiniteStageNormOneTorus S :=
      fun v => ⟨w'.2 v, hw'local v⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    change
      (QuotientGroup.mk (fieldOneFiniteStageNormOneTorusIdele S k) :
        FieldOneFiniteStageIdeleClassGroup S) = QuotientGroup.mk u
    rw [← hclassw']
    congr 1
    apply Prod.ext
    · apply Units.ext
      exact hw'real.symm
    · rfl

noncomputable instance fieldOneFiniteStageModuleOneClassCompactSpace
    (S : Finset (HeightOneSpectrum ℤ)) :
    CompactSpace (FieldOneFiniteStageModuleOneClass S) :=
  Function.Surjective.compactSpace
    (fieldOneFiniteStageNormOneTorusToModuleOne_continuous S)
    (fieldOneFiniteStageNormOneTorusToModuleOne_surjective S)

end

end GaloisForLFunctions.RHTower
