import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vector-valued reflexive polarization synchronization

Several channels report residual covectors produced by one source state.  Each channel has its own
symmetric positive definite polarization form and therefore its own locally optimal correction
velocity; the source can execute only the velocity determined by the summed form and the summed
residual.  Independent local correction power then splits exactly into executable fused power plus
synchronization tension, and homogeneous amplification of the residuals separates the three
boundedness laws.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Constitutive data -/

/-- The fused polarization form. -/
def fusedForm (H : ι → V →L[ℝ] V →L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ := ∑ i, H i

@[simp] theorem fusedForm_apply (H : ι → V →L[ℝ] V →L[ℝ] ℝ) (u w : V) :
    fusedForm H u w = ∑ i, H i u w := by
  simp [fusedForm]

/-- Independent local correction power. -/
def localPower (H : ι → V →L[ℝ] V →L[ℝ] ℝ) (vloc : ι → V) : ℝ := ∑ i, H i (vloc i) (vloc i)

/-- Executable fused correction power. -/
def fusedPower (H : ι → V →L[ℝ] V →L[ℝ] ℝ) (v : V) : ℝ := fusedForm H v v

/-- Synchronization tension. -/
def syncTension (H : ι → V →L[ℝ] V →L[ℝ] ℝ) (vloc : ι → V) (v : V) : ℝ :=
  ∑ i, H i (vloc i - v) (vloc i - v)

/-- The constitutive setting: symmetric channel forms, channel residuals, local velocities solving
the channel equations, and the fused velocity solving the summed equation. -/
structure PolarizationPacket (ι : Type*) [Fintype ι] (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- Channel polarization forms. -/
  form : ι → V →L[ℝ] V →L[ℝ] ℝ
  /-- Channel residual covectors. -/
  residual : ι → V →L[ℝ] ℝ
  /-- Local correction velocities. -/
  localVelocity : ι → V
  /-- The executable fused velocity. -/
  fusedVelocity : V
  /-- Every channel form is symmetric. -/
  symm : ∀ i u w, form i u w = form i w u
  /-- The channel constitutive equations. -/
  local_eq : ∀ i, form i (localVelocity i) = residual i
  /-- The fused constitutive equation. -/
  fused_eq : fusedForm form fusedVelocity = ∑ i, residual i

namespace PolarizationPacket

variable (P : PolarizationPacket ι V)

/-- **Balance law.**  The relative velocity packet is annihilated by the summed form. -/
theorem balance : ∑ i, P.form i (P.localVelocity i - P.fusedVelocity) = 0 := by
  have hsum : ∑ i, P.form i (P.localVelocity i - P.fusedVelocity)
      = (∑ i, P.form i (P.localVelocity i)) - ∑ i, P.form i P.fusedVelocity := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub]
  rw [hsum]
  have h1 : ∑ i, P.form i (P.localVelocity i) = ∑ i, P.residual i :=
    Finset.sum_congr rfl fun i _ => P.local_eq i
  have h2 : ∑ i, P.form i P.fusedVelocity = fusedForm P.form P.fusedVelocity := by
    refine ContinuousLinearMap.ext fun w => ?_
    simp [fusedForm]
  rw [h1, h2, P.fused_eq, sub_self]

/-- **Exact synchronization conservation.**  Local power splits into fused power plus tension. -/
theorem localPower_eq_fusedPower_add_syncTension :
    localPower P.form P.localVelocity
      = fusedPower P.form P.fusedVelocity + syncTension P.form P.localVelocity P.fusedVelocity := by
  have hexpand : ∀ i, P.form i (P.localVelocity i - P.fusedVelocity)
        (P.localVelocity i - P.fusedVelocity)
      = P.form i (P.localVelocity i) (P.localVelocity i)
        - 2 * P.form i (P.localVelocity i) P.fusedVelocity
        + P.form i P.fusedVelocity P.fusedVelocity := by
    intro i
    have h1 : P.form i (P.localVelocity i - P.fusedVelocity)
        = P.form i (P.localVelocity i) - P.form i P.fusedVelocity := map_sub _ _ _
    rw [h1]
    simp only [FunLike.coe_sub, Pi.sub_apply, map_sub]
    rw [P.symm i P.fusedVelocity (P.localVelocity i)]
    ring
  have hcross : ∑ i, P.form i (P.localVelocity i) P.fusedVelocity
      = fusedPower P.form P.fusedVelocity := by
    have h1 : ∑ i, P.form i (P.localVelocity i) P.fusedVelocity
        = ∑ i, P.residual i P.fusedVelocity :=
      Finset.sum_congr rfl fun i _ => by rw [P.local_eq i]
    have h2 : ∑ i, P.residual i P.fusedVelocity
        = (∑ i, P.residual i) P.fusedVelocity := by
      simp
    rw [h1, h2, ← P.fused_eq]
    simp [fusedPower, fusedForm]
  rw [syncTension, localPower, Finset.sum_congr rfl fun i _ => hexpand i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hcross]
  have hlast : ∑ _i : ι, P.form _i P.fusedVelocity P.fusedVelocity
      = fusedPower P.form P.fusedVelocity := by
    simp [fusedPower, fusedForm]
  rw [hlast]
  ring

/-- **Reconstruction.**  Residuals are recovered from the fused velocity and the relative packet. -/
theorem residual_eq (i : ι) :
    P.residual i = P.form i (P.fusedVelocity + (P.localVelocity i - P.fusedVelocity)) := by
  rw [add_sub_cancel, P.local_eq i]

end PolarizationPacket

/-! ## Positivity and the zero classification -/

/-- Positive definiteness of every channel form. -/
def IsPosDef (H : ι → V →L[ℝ] V →L[ℝ] ℝ) : Prop := ∀ i u, u ≠ 0 → 0 < H i u u

omit [Fintype ι] in
theorem nonneg_of_isPosDef {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H) (i : ι) (u : V) :
    0 ≤ H i u u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · exact (hpd i u hu).le

theorem localPower_nonneg {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H) (vloc : ι → V) :
    0 ≤ localPower H vloc :=
  Finset.sum_nonneg fun i _ => nonneg_of_isPosDef hpd i _

theorem syncTension_nonneg {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H) (vloc : ι → V) (v : V) :
    0 ≤ syncTension H vloc v :=
  Finset.sum_nonneg fun i _ => nonneg_of_isPosDef hpd i _

theorem syncTension_eq_zero_iff {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H) (vloc : ι → V)
    (v : V) : syncTension H vloc v = 0 ↔ ∀ i, vloc i = v := by
  constructor
  · intro h i
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => nonneg_of_isPosDef hpd j (vloc j - v))).1 h i
      (Finset.mem_univ i)
    by_contra hne
    have hd : vloc i - v ≠ 0 := sub_ne_zero.2 hne
    exact absurd hzero (ne_of_gt (hpd i _ hd))
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h i, sub_self]
    simp

theorem localPower_eq_zero_iff {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H) (vloc : ι → V) :
    localPower H vloc = 0 ↔ ∀ i, vloc i = 0 := by
  constructor
  · intro h i
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => nonneg_of_isPosDef hpd j (vloc j))).1 h i (Finset.mem_univ i)
    by_contra hne
    exact absurd hzero (ne_of_gt (hpd i _ hne))
  · intro h
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h i]
    simp

theorem fusedForm_posDef [Nonempty ι] {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H) :
    ∀ u : V, u ≠ 0 → 0 < fusedForm H u u := by
  intro u hu
  rw [fusedForm_apply]
  exact Finset.sum_pos (fun i _ => hpd i u hu) Finset.univ_nonempty

theorem fusedPower_nonneg [Nonempty ι] {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H) (v : V) :
    0 ≤ fusedPower H v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [fusedPower]
  · exact (fusedForm_posDef hpd v hv).le

theorem fusedPower_eq_zero_iff [Nonempty ι] {H : ι → V →L[ℝ] V →L[ℝ] ℝ} (hpd : IsPosDef H)
    (v : V) : fusedPower H v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact absurd h (ne_of_gt (fusedForm_posDef hpd v hv))
  · rintro rfl
    simp [fusedPower]

namespace PolarizationPacket

variable (P : PolarizationPacket ι V)

theorem localVelocity_eq_zero_iff {hpd : IsPosDef P.form} (i : ι) :
    P.localVelocity i = 0 ↔ P.residual i = 0 := by
  constructor
  · intro h
    rw [← P.local_eq i, h]
    simp
  · intro h
    by_contra hne
    have hpos := hpd i _ hne
    have : P.form i (P.localVelocity i) (P.localVelocity i) = 0 := by
      rw [P.local_eq i, h]
      simp
    exact absurd this (ne_of_gt hpos)

/-- The channel constitutive equation has a unique solution. -/
theorem localVelocity_unique {hpd : IsPosDef P.form} (i : ι) {w : V}
    (hw : P.form i w = P.residual i) : w = P.localVelocity i := by
  have hinj : Function.Injective (fun u : V => P.form i u) := by
    intro a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.2 hne
    have h0 : P.form i (a - b) = 0 := by
      have : P.form i a = P.form i b := hab
      rw [map_sub, this, sub_self]
    have hpos := hpd i (a - b) hd
    rw [h0] at hpos
    simp at hpos
  refine hinj ?_
  show P.form i w = P.form i (P.localVelocity i)
  rw [hw, P.local_eq i]

/-- The fused constitutive equation has a unique solution. -/
theorem fusedVelocity_unique [Nonempty ι] {hpd : IsPosDef P.form} {w : V}
    (hw : fusedForm P.form w = ∑ i, P.residual i) : w = P.fusedVelocity := by
  have hinj : Function.Injective (fun u : V => fusedForm P.form u) := by
    intro a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.2 hne
    have h0 : fusedForm P.form (a - b) = 0 := by
      have : fusedForm P.form a = fusedForm P.form b := hab
      rw [map_sub, this, sub_self]
    have hpos := fusedForm_posDef hpd (a - b) hd
    rw [h0] at hpos
    simp at hpos
  refine hinj ?_
  show fusedForm P.form w = fusedForm P.form P.fusedVelocity
  rw [hw, P.fused_eq]

/-! ## Homogeneous amplification -/

/-- Amplifying every residual by a common factor. -/
def amplify (r : ℝ) (P : PolarizationPacket ι V) : PolarizationPacket ι V where
  form := P.form
  residual := fun i => r • P.residual i
  localVelocity := fun i => r • P.localVelocity i
  fusedVelocity := r • P.fusedVelocity
  symm := P.symm
  local_eq := by
    intro i
    rw [map_smul, P.local_eq i]
  fused_eq := by
    rw [map_smul, P.fused_eq, Finset.smul_sum]

@[simp] theorem amplify_form (r : ℝ) : (amplify r P).form = P.form := rfl

theorem localPower_amplify (r : ℝ) :
    localPower P.form (amplify r P).localVelocity = r ^ 2 * localPower P.form P.localVelocity := by
  rw [localPower, localPower, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show P.form i (r • P.localVelocity i) (r • P.localVelocity i) = _
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem fusedPower_amplify (r : ℝ) :
    fusedPower P.form (amplify r P).fusedVelocity = r ^ 2 * fusedPower P.form P.fusedVelocity := by
  rw [fusedPower, fusedPower]
  show fusedForm P.form (r • P.fusedVelocity) (r • P.fusedVelocity) = _
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem syncTension_amplify (r : ℝ) :
    syncTension P.form (amplify r P).localVelocity (amplify r P).fusedVelocity
      = r ^ 2 * syncTension P.form P.localVelocity P.fusedVelocity := by
  rw [syncTension, syncTension, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show P.form i (r • P.localVelocity i - r • P.fusedVelocity)
      (r • P.localVelocity i - r • P.fusedVelocity) = _
  rw [← smul_sub]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end PolarizationPacket

theorem bounded_geometric_iff {p d : ℝ} (hp : 0 ≤ p) (hd : 1 < d) :
    (∃ C : ℝ, ∀ n : ℕ, (d ^ n) ^ 2 * p ≤ C) ↔ p = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hne)
    have hd2 : (1 : ℝ) < d ^ 2 := by nlinarith
    have hdiv : Filter.Tendsto (fun n : ℕ => (d ^ 2) ^ n * p) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_mul_const hppos (tendsto_pow_atTop_atTop_of_one_lt hd2)
    obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop C).exists
    have hrw : (d ^ n) ^ 2 * p = (d ^ 2) ^ n * p := by
      rw [← pow_mul, ← pow_mul, mul_comm n 2]
    exact absurd (hC n) (not_le.2 (by rwa [hrw]))
  · rintro rfl
    exact ⟨0, fun n => by simp⟩

namespace PolarizationPacket

variable (P : PolarizationPacket ι V)

/-- **Homogeneous properness.**  Bounded amplified local power selects the whole residual
packet. -/
theorem bounded_localPower_iff {hpd : IsPosDef P.form} {d : ℝ} (hd : 1 < d) :
    (∃ C : ℝ, ∀ n : ℕ, localPower P.form (amplify (d ^ n) P).localVelocity ≤ C)
      ↔ ∀ i, P.residual i = 0 := by
  have hrw : ∀ n : ℕ, localPower P.form (amplify (d ^ n) P).localVelocity
      = (d ^ n) ^ 2 * localPower P.form P.localVelocity := fun n => P.localPower_amplify (d ^ n)
  constructor
  · rintro ⟨C, hC⟩
    have hzero : localPower P.form P.localVelocity = 0 :=
      (bounded_geometric_iff (localPower_nonneg hpd _) hd).1
        ⟨C, fun n => by rw [← hrw n]; exact hC n⟩
    intro i
    exact (P.localVelocity_eq_zero_iff (hpd := hpd) i).1
      ((localPower_eq_zero_iff hpd _).1 hzero i)
  · intro h
    have hv : ∀ i, P.localVelocity i = 0 := fun i =>
      (P.localVelocity_eq_zero_iff (hpd := hpd) i).2 (h i)
    refine ⟨0, fun n => ?_⟩
    rw [hrw n, (localPower_eq_zero_iff hpd _).2 hv, mul_zero]

/-- **Homogeneous properness for the tension.**  Bounded amplified tension is synchronization. -/
theorem bounded_syncTension_iff {hpd : IsPosDef P.form} {d : ℝ} (hd : 1 < d) :
    (∃ C : ℝ, ∀ n : ℕ,
        syncTension P.form (amplify (d ^ n) P).localVelocity (amplify (d ^ n) P).fusedVelocity ≤ C)
      ↔ ∀ i, P.localVelocity i = P.fusedVelocity := by
  have hrw : ∀ n : ℕ,
      syncTension P.form (amplify (d ^ n) P).localVelocity (amplify (d ^ n) P).fusedVelocity
        = (d ^ n) ^ 2 * syncTension P.form P.localVelocity P.fusedVelocity :=
    fun n => P.syncTension_amplify (d ^ n)
  constructor
  · rintro ⟨C, hC⟩
    have hzero : syncTension P.form P.localVelocity P.fusedVelocity = 0 :=
      (bounded_geometric_iff (syncTension_nonneg hpd _ _) hd).1
        ⟨C, fun n => by rw [← hrw n]; exact hC n⟩
    exact (syncTension_eq_zero_iff hpd _ _).1 hzero
  · intro h
    refine ⟨0, fun n => ?_⟩
    rw [hrw n, (syncTension_eq_zero_iff hpd _ _).2 h, mul_zero]

/-- **Homogeneous properness for the fused power.**  Bounded amplified fused power is exactly
total residual neutrality. -/
theorem bounded_fusedPower_iff [Nonempty ι] {hpd : IsPosDef P.form} {d : ℝ} (hd : 1 < d) :
    (∃ C : ℝ, ∀ n : ℕ, fusedPower P.form (amplify (d ^ n) P).fusedVelocity ≤ C)
      ↔ ∑ i, P.residual i = 0 := by
  have hrw : ∀ n : ℕ, fusedPower P.form (amplify (d ^ n) P).fusedVelocity
      = (d ^ n) ^ 2 * fusedPower P.form P.fusedVelocity := fun n => P.fusedPower_amplify (d ^ n)
  constructor
  · rintro ⟨C, hC⟩
    have hzero : fusedPower P.form P.fusedVelocity = 0 :=
      (bounded_geometric_iff (fusedPower_nonneg hpd _) hd).1
        ⟨C, fun n => by rw [← hrw n]; exact hC n⟩
    have hv : P.fusedVelocity = 0 := (fusedPower_eq_zero_iff hpd _).1 hzero
    rw [← P.fused_eq, hv]
    simp
  · intro h
    have hv : P.fusedVelocity = 0 := by
      refine (fusedPower_eq_zero_iff hpd _).1 ?_
      have hz : fusedForm P.form P.fusedVelocity = 0 := by rw [P.fused_eq, h]
      rw [fusedPower, hz]
      simp
    refine ⟨0, fun n => ?_⟩
    rw [hrw n, fusedPower, hv]
    simp

end PolarizationPacket

end

end GaloisForLFunctions.HTGeometry
