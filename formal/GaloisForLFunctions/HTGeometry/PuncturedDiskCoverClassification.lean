import GaloisForLFunctions.HTGeometry.PuncturedDiskCover
import GaloisForLFunctions.HTGeometry.SubgroupCover
import GaloisForLFunctions.HTGeometry.CoveringComparison
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Classification of connected punctured-disk covers

The explicit integer deck action on the logarithmic half-plane presents the
exponential covering. Its subgroups are exactly the nonnegative integer period
subgroups. Positive-period quotients are punctured disks with exact power
projections; the zero-period quotient retains the logarithmic half-plane.
Comparison of based fundamental-group images classifies every connected,
locally path-connected cover into these two models.
-/

open Topology Set Function Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def logDeckPeriod : ℂ := 2 * Real.pi * I

theorem logDeckPeriod_ne_zero : logDeckPeriod ≠ 0 := by
  simp [logDeckPeriod, Real.pi_ne_zero]

/-- One integer turn in logarithmic coordinates. -/
def logDeckTranslate (k : ℤ) : LogHalfPlane ≃ₜ LogHalfPlane where
  toFun z := ⟨(z : ℂ) + k * logDeckPeriod, by simpa [logDeckPeriod] using z.property⟩
  invFun z := ⟨(z : ℂ) - k * logDeckPeriod, by simpa [logDeckPeriod] using z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := (continuous_subtype_val.add_const _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _

instance logDeckMulAction : MulAction (Multiplicative ℤ) LogHalfPlane where
  smul g z := logDeckTranslate g.toAdd z
  one_smul z := by
    apply Subtype.ext
    change (z : ℂ) + ((1 : Multiplicative ℤ).toAdd : ℂ) * logDeckPeriod = (z : ℂ)
    simp
  mul_smul g h z := by
    apply Subtype.ext
    change (z : ℂ) + ((g * h).toAdd : ℂ) * logDeckPeriod =
      ((z : ℂ) + h.toAdd * logDeckPeriod) + g.toAdd * logDeckPeriod
    rw [toAdd_mul, Int.cast_add]
    ring

@[simp] theorem logDeck_smul_val (g : Multiplicative ℤ) (z : LogHalfPlane) :
    ((g • z : LogHalfPlane) : ℂ) = (z : ℂ) + g.toAdd * logDeckPeriod := rfl

instance logDeckContinuousConstSMul : ContinuousConstSMul (Multiplicative ℤ) LogHalfPlane where
  continuous_const_smul g := (logDeckTranslate g.toAdd).continuous

instance logDeckIsCancelSMul : IsCancelSMul (Multiplicative ℤ) LogHalfPlane where
  right_cancel' g h z he := by
    have hval := congrArg Subtype.val he
    simp only [logDeck_smul_val, add_right_inj] at hval
    have hcast : (g.toAdd : ℂ) = h.toAdd := (mul_right_cancel₀ logDeckPeriod_ne_zero hval)
    have hint : g.toAdd = h.toAdd := by exact_mod_cast hcast
    exact congrArg Multiplicative.ofAdd hint

/-- Fibers of the disk exponential are exactly the integer translation orbits. -/
theorem puncturedDiskExp_eq_iff_orbit (z w : LogHalfPlane) :
    puncturedDiskExp z = puncturedDiskExp w ↔ z ∈ MulAction.orbit (Multiplicative ℤ) w := by
  rw [Subtype.ext_iff]
  change Complex.exp (z : ℂ) = Complex.exp (w : ℂ) ↔ _
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨Multiplicative.ofAdd k, Subtype.ext hk.symm⟩
  · rintro ⟨g, hg⟩
    exact ⟨g.toAdd, (congrArg Subtype.val hg).symm⟩

/-- The logarithmic universal cover has its explicit integer deck group. -/
theorem isQuotientCoveringMap_puncturedDiskExp :
    IsQuotientCoveringMap puncturedDiskExp (Multiplicative ℤ) :=
  (isQuotientCoveringMap_iff_isCoveringMap_and puncturedDiskExp (Multiplicative ℤ)).mpr
    ⟨isCoveringMap_puncturedDiskExp, puncturedDiskExp_surjective, inferInstance,
      inferInstance, fun {z w} => puncturedDiskExp_eq_iff_orbit z w⟩

/-- Fibers of the universal cover adapted to an n-th power chart have period 2πin. -/
theorem puncturedDiskRootExp_eq_iff (n : ℕ) (hn : 0 < n) (z w : LogHalfPlane) :
    puncturedDiskRootExp n hn z = puncturedDiskRootExp n hn w ↔
      ∃ k : ℤ, (z : ℂ) = (w : ℂ) + (n : ℂ) * k * logDeckPeriod := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Subtype.ext_iff]
  simp only [puncturedDiskRootExp_val, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h := congrArg (fun t : ℂ => (n : ℂ) * t) hk
    simpa [mul_add, ← mul_assoc, hnC, logDeckPeriod] using h
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk, mul_add]
    simp [← mul_assoc, hnC, logDeckPeriod]

/-- Integer translations by multiples of n. -/
def integerPeriodSubgroup (n : ℕ) : Subgroup (Multiplicative ℤ) :=
  Subgroup.zpowers (Multiplicative.ofAdd (n : ℤ))

theorem mem_integerPeriodSubgroup (n : ℕ) (g : Multiplicative ℤ) :
    g ∈ integerPeriodSubgroup n ↔ ∃ k : ℤ, g.toAdd = (n : ℤ) * k := by
  rw [integerPeriodSubgroup, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp [toAdd_zpow, mul_comm]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : ((Multiplicative.ofAdd (n : ℤ)) ^ k).toAdd = g.toAdd := by
      simp [toAdd_zpow, hk, mul_comm]
    exact congrArg Multiplicative.ofAdd h

/-- Every deck subgroup is generated by a nonnegative number of turns. -/
theorem exists_eq_integerPeriodSubgroup (H : Subgroup (Multiplicative ℤ)) :
    ∃ n : ℕ, H = integerPeriodSubgroup n := by
  obtain ⟨g, hg⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  refine ⟨g.toAdd.natAbs, ?_⟩
  rw [← hg]
  unfold integerPeriodSubgroup
  rcases le_total 0 g.toAdd with hpos | hneg
  · congr 1
    apply Multiplicative.ext
    simp [abs_of_nonneg hpos]
  · rw [← Subgroup.zpowers_inv]
    congr 1
    apply Multiplicative.ext
    simp [abs_of_nonpos hneg]

/-- The adapted exponential has exactly the selected subgroup's orbits as fibers. -/
theorem puncturedDiskRootExp_eq_iff_periodOrbit (n : ℕ) (hn : 0 < n) (z w : LogHalfPlane) :
    puncturedDiskRootExp n hn z = puncturedDiskRootExp n hn w ↔
      z ∈ MulAction.orbit (integerPeriodSubgroup n) w := by
  rw [puncturedDiskRootExp_eq_iff n hn]
  constructor
  · rintro ⟨k, hk⟩
    let g : integerPeriodSubgroup n :=
      ⟨Multiplicative.ofAdd ((n : ℤ) * k), (mem_integerPeriodSubgroup n _).mpr ⟨k, rfl⟩⟩
    refine ⟨g, Subtype.ext ?_⟩
    change (w : ℂ) + (((n : ℤ) * k : ℤ) : ℂ) * logDeckPeriod = (z : ℂ)
    simpa only [Int.cast_mul, Int.cast_natCast, mul_assoc] using hk.symm
  · rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := (mem_integerPeriodSubgroup n g.val).mp g.property
    refine ⟨k, ?_⟩
    have h := (congrArg Subtype.val hg).symm
    change (z : ℂ) = (w : ℂ) + (g.val.toAdd : ℂ) * logDeckPeriod at h
    simpa only [hk, Int.cast_mul, Int.cast_natCast, mul_assoc] using h

/-- Quotient presentation for the adapted exponential. -/
theorem isQuotientCoveringMap_puncturedDiskRootExp (n : ℕ) (hn : 0 < n) :
    IsQuotientCoveringMap (puncturedDiskRootExp n hn) (integerPeriodSubgroup n) := by
  apply (isQuotientCoveringMap_iff_isCoveringMap_and _ _).mpr
  refine ⟨isCoveringMap_puncturedDiskRootExp n hn, puncturedDiskRootExp_surjective n hn,
    ⟨fun g => (logDeckTranslate g.val.toAdd).continuous⟩, ?_,
    fun {z w} => puncturedDiskRootExp_eq_iff_periodOrbit n hn z w⟩
  exact ⟨fun g h z he => Subtype.ext (logDeckIsCancelSMul.right_cancel g.val h.val z he)⟩

/-- The n-period orbit quotient is a punctured disk in its power-chart coordinate. -/
def periodQuotientHomeomorph (n : ℕ) (hn : 0 < n) :
    SubgroupCover (E := LogHalfPlane) (integerPeriodSubgroup n) ≃ₜ PuncturedUnitDisk :=
  (Homeomorph.Quotient.congrRight fun z w =>
    (puncturedDiskRootExp_eq_iff_periodOrbit n hn z w).symm).trans
    (Topology.IsQuotientMap.homeomorph
      (f := (⟨puncturedDiskRootExp n hn, (isCoveringMap_puncturedDiskRootExp n hn).continuous⟩ :
        C(LogHalfPlane, PuncturedUnitDisk)))
      (isQuotientCoveringMap_puncturedDiskRootExp n hn).toIsQuotientMap)

@[simp] theorem periodQuotientHomeomorph_mk (n : ℕ) (hn : 0 < n) (z : LogHalfPlane) :
    periodQuotientHomeomorph n hn (Quotient.mk _ z) = puncturedDiskRootExp n hn z := rfl

/-- The quotient projection is exactly the power map, not merely a map of the same degree. -/
theorem periodQuotient_projection (n : ℕ) (hn : 0 < n)
    (z : SubgroupCover (E := LogHalfPlane) (integerPeriodSubgroup n)) :
    subgroupCoverProjection isQuotientCoveringMap_puncturedDiskExp (integerPeriodSubgroup n) z =
      puncturedDiskPower n hn (periodQuotientHomeomorph n hn z) := by
  induction z using Quotient.inductionOn with | _ w =>
  exact (puncturedDiskPower_rootExp n hn w).symm

@[simp] theorem integerPeriodSubgroup_zero : integerPeriodSubgroup 0 = ⊥ := by
  simp [integerPeriodSubgroup]

theorem zeroPeriod_orbit_iff (z w : LogHalfPlane) :
    z ∈ MulAction.orbit (integerPeriodSubgroup 0) w ↔ z = w := by
  constructor
  · rintro ⟨g, hg⟩
    have hg1 : g.val = 1 := by
      obtain ⟨k, hk⟩ := (mem_integerPeriodSubgroup 0 g.val).mp g.property
      apply Multiplicative.ext
      simpa using hk
    change g.val • w = z at hg
    rw [hg1, one_smul] at hg
    exact hg.symm
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

/-- The zero-period quotient retains the complete logarithmic half-plane. -/
def zeroPeriodQuotientHomeomorph :
    SubgroupCover (E := LogHalfPlane) (integerPeriodSubgroup 0) ≃ₜ LogHalfPlane :=
  (Homeomorph.Quotient.congrRight (r' := ⊥) fun z w => zeroPeriod_orbit_iff z w).trans
    Homeomorph.quotientBot

@[simp] theorem zeroPeriodQuotientHomeomorph_mk (z : LogHalfPlane) :
    zeroPeriodQuotientHomeomorph (Quotient.mk _ z) = z := rfl

theorem zeroPeriodQuotient_projection
    (z : SubgroupCover (E := LogHalfPlane) (integerPeriodSubgroup 0)) :
    subgroupCoverProjection isQuotientCoveringMap_puncturedDiskExp (integerPeriodSubgroup 0) z =
      puncturedDiskExp (zeroPeriodQuotientHomeomorph z) := by
  induction z using Quotient.inductionOn with | _ w => rfl

/-- Every connected disk cover is represented by a subgroup of integer logarithmic translations. -/
theorem exists_puncturedDiskCover_subgroup_model
    {Y : Type*} [TopologicalSpace Y] [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    {q : Y → PuncturedUnitDisk} (hq : IsCoveringMap q)
    (y₀ : Y) (w₀ : LogHalfPlane) (he : q y₀ = puncturedDiskExp w₀) :
    ∃ H : Subgroup (Multiplicative ℤ),
      ∃ d : SubgroupCover (E := LogHalfPlane) H ≃ₜ Y,
      ∀ z, q (d z) = subgroupCoverProjection isQuotientCoveringMap_puncturedDiskExp H z := by
  let hp := isQuotientCoveringMap_puncturedDiskExp
  let e : puncturedDiskExp ⁻¹' {puncturedDiskExp w₀} := ⟨w₀, rfl⟩
  let K := (FundamentalGroup.mapOfEq ⟨q, hq.continuous⟩ he).range
  let H := (K.map (hp.fundamentalGroupToMulOpposite e)).unop
  let qH := subgroupCoverProjection hp H
  let z₀ : SubgroupCover (E := LogHalfPlane) H := Quotient.mk _ w₀
  have hqH : IsCoveringMap qH := isCoveringMap_subgroupCoverProjection hp H
  have hrange : (FundamentalGroup.map ⟨qH, hqH.continuous⟩ z₀).range = K := by
    have h := fundamentalGroup_range_prescribed_subgroup hp e K
    have hm : FundamentalGroup.map ⟨qH, hqH.continuous⟩ z₀ =
        FundamentalGroup.mapOfEq ⟨qH, hqH.continuous⟩ (show qH z₀ = puncturedDiskExp w₀ from rfl) := by
      ext γ
      simp only [FundamentalGroup.map_apply, FundamentalGroup.mapOfEq_apply,
        Path.Homotopic.Quotient.cast_rfl_rfl]
    rw [hm]
    exact h
  obtain ⟨d, ⟨-, hd⟩, -⟩ := existsUnique_covering_homeomorph_of_range_eq
    hqH hq z₀ y₀ he hrange
  exact ⟨H, d, hd⟩

/-- A connected punctured-disk covering is either logarithmic or an exact positive power cover. -/
theorem puncturedDisk_cover_classification
    {Y : Type*} [TopologicalSpace Y] [PathConnectedSpace Y] [LocallyPathConnectedSpace Y]
    {q : Y → PuncturedUnitDisk} (hq : IsCoveringMap q) :
    (∃ D : Y ≃ₜ LogHalfPlane, ∀ y, q y = puncturedDiskExp (D y)) ∨
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ D : Y ≃ₜ PuncturedUnitDisk,
        ∀ y, q y = puncturedDiskPower n hn (D y) := by
  classical
  let y₀ : Y := Classical.choice (inferInstance : Nonempty Y)
  obtain ⟨w₀, hw₀⟩ := puncturedDiskExp_surjective (q y₀)
  obtain ⟨H, d, hd⟩ := exists_puncturedDiskCover_subgroup_model hq y₀ w₀ hw₀.symm
  obtain ⟨n, rfl⟩ := exists_eq_integerPeriodSubgroup H
  cases n with
  | zero =>
      refine Or.inl ⟨d.symm.trans zeroPeriodQuotientHomeomorph, fun y => ?_⟩
      calc
        q y = subgroupCoverProjection isQuotientCoveringMap_puncturedDiskExp
            (integerPeriodSubgroup 0) (d.symm y) := by rw [← hd, d.apply_symm_apply]
        _ = puncturedDiskExp (zeroPeriodQuotientHomeomorph (d.symm y)) :=
          zeroPeriodQuotient_projection _
  | succ n =>
      refine Or.inr ⟨n + 1, Nat.succ_pos n,
        d.symm.trans (periodQuotientHomeomorph (n + 1) (Nat.succ_pos n)), fun y => ?_⟩
      calc
        q y = subgroupCoverProjection isQuotientCoveringMap_puncturedDiskExp
            (integerPeriodSubgroup (n + 1)) (d.symm y) := by rw [← hd, d.apply_symm_apply]
        _ = puncturedDiskPower (n + 1) (Nat.succ_pos n)
            (periodQuotientHomeomorph (n + 1) (Nat.succ_pos n) (d.symm y)) :=
          periodQuotient_projection _ _ _

end
end GaloisForLFunctions.HTGeometry
