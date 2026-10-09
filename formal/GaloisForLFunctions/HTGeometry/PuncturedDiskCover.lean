import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Homotopy.Contractible

/-!
# Explicit universal and power covers of the punctured unit disk

Restrict the corpus exponential and power coverings to the punctured unit disk.
Its exponential preimage is the left half-plane. Positive scaling gives the
universal cover adapted to each finite power chart, with an exact projection
identity used in peripheral ramification classification.
-/

open Topology Set Function Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The standard punctured disk used in local ramification charts. -/
abbrev PuncturedUnitDisk := {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1}
/-- The logarithmic universal-cover domain. -/
abbrev LogHalfPlane := {z : ℂ // z.re < 0}

instance logHalfPlaneContractibleSpace : ContractibleSpace LogHalfPlane :=
  (convex_halfSpace_re_lt 0).contractibleSpace ⟨-1, by simp⟩

instance logHalfPlaneLocallyPathConnectedSpace : LocallyPathConnectedSpace LogHalfPlane :=
  (isOpen_lt Complex.continuous_re continuous_const).locallyPathConnectedSpace

instance puncturedUnitDiskLocallyPathConnectedSpace : LocallyPathConnectedSpace PuncturedUnitDisk :=
  (isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)).locallyPathConnectedSpace

/-- The restricted exponential projection. -/
def puncturedDiskExp (z : LogHalfPlane) : PuncturedUnitDisk :=
  ⟨Complex.exp z, Complex.exp_ne_zero z, by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    exact z.property⟩

@[simp] theorem puncturedDiskExp_val (z : LogHalfPlane) :
    (puncturedDiskExp z : ℂ) = Complex.exp z := rfl

theorem isCoveringMap_puncturedDiskExp : IsCoveringMap puncturedDiskExp := by
  let S : Set ℂ := {z | z ≠ 0 ∧ ‖z‖ < 1}
  have hp : IsCoveringMapOn Complex.exp S :=
    Complex.isCoveringMapOn_exp.mono fun z hz => hz.1
  have heq : {z : ℂ | z.re < 0} = Complex.exp ⁻¹' S := by
    ext z
    simp only [S, mem_preimage, mem_setOf_eq, Complex.norm_exp, Real.exp_lt_one_iff]
    exact ⟨fun hz => ⟨Complex.exp_ne_zero z, hz⟩, fun hz => hz.2⟩
  exact hp.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr heq)

theorem puncturedDiskExp_surjective : Surjective puncturedDiskExp := by
  intro z
  refine ⟨⟨Complex.log z, ?_⟩, ?_⟩
  · rw [Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr z.property.1) z.property.2
  · apply Subtype.ext
    exact Complex.exp_log z.property.1

instance puncturedUnitDiskPathConnectedSpace : PathConnectedSpace PuncturedUnitDisk :=
  puncturedDiskExp_surjective.pathConnectedSpace isCoveringMap_puncturedDiskExp.continuous

/-- The finite power-cover model for a ramified cap. -/
def puncturedDiskPower (n : ℕ) (hn : 0 < n) (z : PuncturedUnitDisk) : PuncturedUnitDisk :=
  ⟨(z : ℂ) ^ n, pow_ne_zero n z.property.1, by
    rw [norm_pow]
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hn.ne').mpr z.property.2⟩

@[simp] theorem puncturedDiskPower_val (n : ℕ) (hn : 0 < n) (z : PuncturedUnitDisk) :
    (puncturedDiskPower n hn z : ℂ) = (z : ℂ) ^ n := rfl

theorem isCoveringMap_puncturedDiskPower (n : ℕ) (hn : 0 < n) :
    IsCoveringMap (puncturedDiskPower n hn) := by
  let S : Set ℂ := {z | z ≠ 0 ∧ ‖z‖ < 1}
  have hp : IsCoveringMapOn (fun z : ℂ => z ^ n) S :=
    (isCoveringMapOn_npow n (by exact_mod_cast hn.ne')).mono fun z hz => hz.1
  have heq : S = (fun z : ℂ => z ^ n) ⁻¹' S := by
    ext z
    simp only [S, mem_preimage, mem_setOf_eq, pow_ne_zero_iff hn.ne', norm_pow,
      pow_lt_one_iff_of_nonneg (norm_nonneg z) hn.ne']
  exact hp.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr heq)

/-- Positive real scaling preserves the logarithmic half-plane. -/
def logHalfPlaneScale (t : ℝ) (ht : 0 < t) : LogHalfPlane ≃ₜ LogHalfPlane where
  toFun z := ⟨(t : ℂ) * z, by simpa using mul_neg_of_pos_of_neg ht z.property⟩
  invFun z := ⟨(t⁻¹ : ℝ) * (z : ℂ), by simpa using mul_neg_of_pos_of_neg (inv_pos.mpr ht) z.property⟩
  left_inv z := by
    apply Subtype.ext
    simp [ht.ne']
  right_inv z := by
    apply Subtype.ext
    simp [ht.ne']
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- The universal cover adapted to an n-th power chart. -/
def puncturedDiskRootExp (n : ℕ) (hn : 0 < n) : LogHalfPlane → PuncturedUnitDisk :=
  puncturedDiskExp ∘ logHalfPlaneScale (n : ℝ)⁻¹ (inv_pos.mpr (Nat.cast_pos.mpr hn))

@[simp] theorem puncturedDiskRootExp_val (n : ℕ) (hn : 0 < n) (z : LogHalfPlane) :
    (puncturedDiskRootExp n hn z : ℂ) = Complex.exp ((n : ℂ)⁻¹ * z) := by
  simp [puncturedDiskRootExp, logHalfPlaneScale, puncturedDiskExp]

theorem isCoveringMap_puncturedDiskRootExp (n : ℕ) (hn : 0 < n) :
    IsCoveringMap (puncturedDiskRootExp n hn) :=
  isCoveringMap_puncturedDiskExp.comp_homeomorph _

theorem puncturedDiskRootExp_surjective (n : ℕ) (hn : 0 < n) :
    Surjective (puncturedDiskRootExp n hn) :=
  puncturedDiskExp_surjective.comp (logHalfPlaneScale _ _).surjective

/-- The model projection identity for attaching an n-fold ramification cap. -/
@[simp] theorem puncturedDiskPower_rootExp (n : ℕ) (hn : 0 < n) (z : LogHalfPlane) :
    puncturedDiskPower n hn (puncturedDiskRootExp n hn z) = puncturedDiskExp z := by
  apply Subtype.ext
  simp only [puncturedDiskPower_val, puncturedDiskRootExp_val, puncturedDiskExp_val]
  rw [← Complex.exp_nat_mul]
  congr 1
  simp [hn.ne']

theorem puncturedDiskPower_surjective (n : ℕ) (hn : 0 < n) :
    Surjective (puncturedDiskPower n hn) := by
  intro w
  obtain ⟨z, rfl⟩ := puncturedDiskExp_surjective w
  exact ⟨puncturedDiskRootExp n hn z, puncturedDiskPower_rootExp n hn z⟩

end
end GaloisForLFunctions.HTGeometry
