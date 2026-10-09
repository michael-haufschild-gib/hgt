import GaloisForLFunctions.HTGeometry.FiniteNormalPackets
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Order.Filter.Cofinite
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Logic.Equiv.Option
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Finite monodromy tests do not determine a nonnormal subgroup

A free group on two generators acts on one distinguished sheet and an integer line.
The first generator fixes the distinguished sheet and translates the line; the second
swaps the distinguished sheet with integer zero. The stabilizer is proper with this
explicit infinite coset space, but contains the first generator, has full integer winding,
normally generates the free group, and has full image under every map to a finite group.
Every finite packet of the winding kernel admits a common conjugator into the stabilizer.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry.InfinitePacketObstruction

abbrev Words := FreeGroup Bool

def x : Words := FreeGroup.of false

def y : Words := FreeGroup.of true

def shifts : Multiplicative ℤ →* Equiv.Perm (Option ℤ) where
  toFun k := Equiv.optionCongr (Equiv.addRight k.toAdd)
  map_one' := by ext j; cases j <;> simp [Equiv.optionCongr]
  map_mul' a b := by ext j; cases j <;> simp [Equiv.optionCongr, add_comm, add_left_comm]

def action : Words →* Equiv.Perm (Option ℤ) :=
  FreeGroup.lift fun b => if b then Equiv.swap none (some 0) else shifts (Multiplicative.ofAdd 1)

def winding : Words →* Multiplicative ℤ :=
  FreeGroup.lift fun b => if b then 1 else Multiplicative.ofAdd 1

instance : MulAction Words (Option ℤ) := MulAction.compHom (Option ℤ) action

def stabilizer : Subgroup Words := MulAction.stabilizer Words (none : Option ℤ)

def kernel : Subgroup Words := winding.ker

instance : kernel.Normal := by unfold kernel; infer_instance

@[simp] theorem mem_stabilizer (g : Words) : g ∈ stabilizer ↔ action g none = none := Iff.rfl

@[simp] theorem action_x : action x = shifts (Multiplicative.ofAdd 1) := by
  simp [action, x]

@[simp] theorem action_y : action y = Equiv.swap none (some 0) := by simp [action, y]

@[simp] theorem winding_x : winding x = Multiplicative.ofAdd 1 := by simp [winding, x]

@[simp] theorem winding_y : winding y = 1 := by simp [winding, y]

@[simp] theorem action_x_zpow_some (k j : ℤ) :
    action (x ^ k) (some j) = some (j + k) := by
  rw [map_zpow, action_x, ← map_zpow]
  change some (j + ((Multiplicative.ofAdd 1 : Multiplicative ℤ) ^ k).toAdd) = _
  rw [← ofAdd_zsmul]
  simp

@[simp] theorem action_x_zpow_none (k : ℤ) : action (x ^ k) none = none := by
  rw [map_zpow, action_x, ← map_zpow]
  rfl

@[simp] theorem winding_x_zpow (k : ℤ) : winding (x ^ k) = Multiplicative.ofAdd k := by
  rw [map_zpow, winding_x, ← ofAdd_zsmul]
  simp

/-- Away from finitely many integer sheets, each word translates by its winding. -/
theorem eventually_action_eq_translation (g : Words) :
    ∀ᶠ j in cofinite, action g (some j) = some (j + (winding g).toAdd) := by
  induction g using FreeGroup.induction_on with
  | C1 => simp
  | of b =>
    cases b with
    | false => exact Filter.Eventually.of_forall (fun _ => by
        simp [action, winding, shifts, Equiv.optionCongr])
    | true =>
      filter_upwards [eventually_cofinite_ne (0 : ℤ)] with j hj
      simp [action, winding, Equiv.swap_apply_of_ne_of_ne, hj]
  | inv_of b _ =>
    cases b with
    | false => exact Filter.Eventually.of_forall (fun _ => by
        simp [action, winding, shifts, Equiv.optionCongr, Equiv.Perm.inv_def])
    | true =>
      filter_upwards [eventually_cofinite_ne (0 : ℤ)] with j hj
      simp [action, winding, Equiv.swap_apply_of_ne_of_ne, hj]
  | mul g h hg hh =>
    have hi : Function.Injective (fun j : ℤ => j + (winding h).toAdd) :=
      fun _ _ e => add_right_cancel e
    have hcomp := hi.tendsto_cofinite.eventually hg
    filter_upwards [hcomp, hh] with j hjg hjh
    simp only [map_mul, Equiv.Perm.mul_apply, toAdd_mul]
    rw [hjh, hjg]
    rw [add_assoc, add_comm (winding h).toAdd (winding g).toAdd]

/-- Every finite kernel packet has one common conjugator into the point stabilizer. -/
theorem common_conjugate_packet (T : Finset Words) (hT : ∀ g ∈ T, g ∈ kernel) :
    ∃ c : Words, ∀ g ∈ T, c * g * c⁻¹ ∈ stabilizer := by
  have he (g : T) : ∀ᶠ j in cofinite, action g.val (some j) = some j := by
    have hg : winding g.val = 1 := hT g.val g.property
    simpa only [hg, toAdd_one, add_zero] using eventually_action_eq_translation g.val
  obtain ⟨j, hj⟩ := (Filter.eventually_all.mpr he).exists
  let c := y * x ^ (-j)
  have hc : action c (some j) = none := by
    simp only [c, map_mul, Equiv.Perm.mul_apply, action_x_zpow_some]
    simp
  have hi : (action c)⁻¹ none = some j := by
    apply (action c).injective
    exact ((action c).apply_symm_apply none).trans hc.symm
  refine ⟨c, fun g hg => ?_⟩
  rw [mem_stabilizer]
  simp only [map_mul, Equiv.Perm.mul_apply, map_inv]
  rw [hi, hj ⟨g, hg⟩, hc]

/-- A stabilizing word has winding one. -/
theorem winding_one_in_stabilizer : x ∈ stabilizer ∧ winding x = Multiplicative.ofAdd 1 := by
  constructor
  · simp [mem_stabilizer, shifts, Equiv.optionCongr]
  · simp

/-- The full integer winding is already attained inside the proper stabilizer. -/
theorem winding_stabilizer_surjective : Function.Surjective (winding.comp stabilizer.subtype) := by
  intro k
  refine ⟨⟨x ^ k.toAdd, stabilizer.zpow_mem winding_one_in_stabilizer.1 _⟩, ?_⟩
  change winding (x ^ k.toAdd) = k
  rw [map_zpow, winding_one_in_stabilizer.2, ← ofAdd_zsmul]
  simp

/-- The subgroup is proper, witnessed by the generator joining the distinguished sheet. -/
theorem stabilizer_ne_top : stabilizer ≠ ⊤ := by
  intro h
  have hy : y ∈ stabilizer := h.symm ▸ Subgroup.mem_top y
  change action y none = none at hy
  simp at hy

/-- The cosets consist of one distinguished sheet and an integer line. -/
noncomputable def cosetEquivSheets : (Words ⧸ stabilizer) ≃ Option ℤ :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer Words (none : Option ℤ))
    ⟨MulAction.injective_ofQuotientStabilizer Words none, by
      intro z
      cases z with
      | none => exact ⟨QuotientGroup.mk 1, rfl⟩
      | some j =>
        refine ⟨QuotientGroup.mk (x ^ j * y), ?_⟩
        change action (x ^ j * y) none = some j
        rw [map_mul, Equiv.Perm.mul_apply, action_y, Equiv.swap_apply_left,
          action_x_zpow_some, zero_add]⟩

@[simp] theorem cosetEquivSheets_mk (g : Words) :
    cosetEquivSheets (QuotientGroup.mk g) = action g none := rfl

/-- The zero meridian fixes the distinguished sheet and translates all other sheets. -/
theorem cosetEquivSheets_x (q : Words ⧸ stabilizer) :
    cosetEquivSheets (x • q) = Option.map (fun j => j + 1) (cosetEquivSheets q) := by
  induction q using Quotient.inductionOn' with
  | h g =>
    change action (x * g) none = Option.map (fun j => j + 1) (action g none)
    rw [map_mul, Equiv.Perm.mul_apply, action_x]
    rfl

/-- The other meridian swaps the distinguished sheet with integer sheet zero. -/
theorem cosetEquivSheets_y (q : Words ⧸ stabilizer) :
    cosetEquivSheets (y • q) = Equiv.swap none (some 0) (cosetEquivSheets q) := by
  induction q using Quotient.inductionOn' with
  | h g =>
    change action (y * g) none = Equiv.swap none (some 0) (action g none)
    simp [Equiv.Perm.mul_apply]

/-- Every finite quotient sees the whole group, although the stabilizer has infinitely many cosets. -/
theorem finite_image_stabilizer_eq_range {G : Type*} [Group G] [Finite G] (q : Words →* G) :
    stabilizer.map q = q.range := by
  have hkernel : kernel.map q ≤ stabilizer.map q :=
    map_le_of_finite_normal_packets kernel stabilizer common_conjugate_packet q
  apply le_antisymm
  · rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨u, hu⟩ := winding_stabilizer_surjective (winding g)
    have hu' : winding (u : Words) = winding g := hu
    have hn : g * (u : Words)⁻¹ ∈ kernel := by
      change winding (g * (u : Words)⁻¹) = 1
      rw [map_mul, map_inv, hu', mul_inv_cancel]
    have hqn : q (g * (u : Words)⁻¹) ∈ stabilizer.map q := hkernel ⟨_, hn, rfl⟩
    have hqu : q (u : Words) ∈ stabilizer.map q := ⟨_, u.property, rfl⟩
    have hprod := (stabilizer.map q).mul_mem hqn hqu
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using hprod

/-- The proper subgroup nevertheless normally generates the entire free group. -/
theorem normalClosure_stabilizer_eq_top :
    Subgroup.normalClosure (stabilizer : Set Words) = ⊤ := by
  apply top_unique
  intro g _
  let C := Subgroup.normalClosure (stabilizer : Set Words)
  have hkernel : kernel ≤ C := by
    intro n hn
    obtain ⟨c, hc⟩ := common_conjugate_packet {n} (by simpa using hn)
    have hmem : c * n * c⁻¹ ∈ C := Subgroup.le_normalClosure (hc n (by simp))
    have hconj := (inferInstance : C.Normal).conj_mem _ hmem c⁻¹
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hconj
  obtain ⟨u, hu⟩ := winding_stabilizer_surjective (winding g)
  have hu' : winding (u : Words) = winding g := hu
  have hn : g * (u : Words)⁻¹ ∈ kernel := by
    change winding (g * (u : Words)⁻¹) = 1
    rw [map_mul, map_inv, hu', mul_inv_cancel]
  have hprod := C.mul_mem (hkernel hn) (Subgroup.le_normalClosure u.property)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hprod

/-- Finite packet realization, full winding, normal generation and every finite image
can all hold for a proper subgroup with the explicit infinite coset geometry above. -/
theorem packet_data_do_not_force_equality :
    ∃ H : Subgroup Words, H ≠ ⊤ ∧ x ∈ H ∧ Nonempty (Words ⧸ H ≃ Option ℤ) ∧
      Function.Surjective (winding.comp H.subtype) ∧
      (∀ T : Finset Words, (∀ g ∈ T, g ∈ kernel) →
        ∃ c : Words, ∀ g ∈ T, c * g * c⁻¹ ∈ H) ∧
      Subgroup.normalClosure (H : Set Words) = ⊤ ∧
      (∀ (G : Type) [Group G] [Finite G] (q : Words →* G), H.map q = q.range) :=
  ⟨stabilizer, stabilizer_ne_top, winding_one_in_stabilizer.1, ⟨cosetEquivSheets⟩,
    winding_stabilizer_surjective,
    common_conjugate_packet, normalClosure_stabilizer_eq_top,
    fun _ _ _ q => finite_image_stabilizer_eq_range q⟩

end GaloisForLFunctions.HTGeometry.InfinitePacketObstruction
