import Mathlib

/-!
# The translation gauge of a derivative horizon

Two structures control what a positive derivative horizon can forget.

The first is geometric: the translation stabilizer of a set splits it as a product of that
stabilizer and a transverse slice, and the slice has trivial stabilizer.  So the only directions
along which a set is a cylinder are the ones its stabilizer already names, and after removing them
nothing is left.

The second is differential: a map commuting with the derivation and fixing the `n`-th derivative of
an element moves that element by something killed by `δ^n`; conversely translation by a constant
fixes every positive derivative.  Together these say that the gauge group of a depth-`n` horizon is
exactly the translations by stabilizer elements annihilated by `δ^n`.
-/

namespace GaloisForLFunctions.HTGeometry

/-! ### The translation stabilizer and the cylinder splitting -/

variable {V : Type*} [AddCommGroup V]

/-- The translation stabilizer of a subset: the translations that preserve it. -/
def transStab (Y : Set V) : AddSubgroup V where
  carrier := {a | ∀ y : V, y + a ∈ Y ↔ y ∈ Y}
  zero_mem' := by intro y; simp
  add_mem' := by
    intro a b ha hb y
    rw [show y + (a + b) = y + a + b by abel, hb, ha]
  neg_mem' := by
    intro a ha y
    have h := ha (y + -a)
    rw [show y + -a + a = y by abel] at h
    exact h.symm

theorem mem_transStab {Y : Set V} {a : V} :
    a ∈ transStab Y ↔ ∀ y : V, y + a ∈ Y ↔ y ∈ Y := Iff.rfl

theorem add_mem_of_mem_transStab {Y : Set V} {a y : V} (ha : a ∈ transStab Y) (hy : y ∈ Y) :
    y + a ∈ Y := (mem_transStab.mp ha y).mpr hy

/-- **The cylinder splitting.**  Relative to a complement of the translation stabilizer, every point
of the set is the sum of a stabilizer element and a point of the transverse slice. -/
theorem mem_iff_exists_add_slice {Y : Set V} {B : AddSubgroup V}
    (hAB : IsCompl (transStab Y) B) (y : V) :
    y ∈ Y ↔ ∃ a ∈ transStab Y, ∃ z ∈ Y ∩ (B : Set V), y = a + z := by
  constructor
  · intro hy
    have htop : y ∈ (⊤ : AddSubgroup V) := AddSubgroup.mem_top y
    rw [← hAB.sup_eq_top] at htop
    obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp htop
    refine ⟨a, ha, b, ⟨?_, hb⟩, hab.symm⟩
    have hneg : -a ∈ transStab Y := AddSubgroup.neg_mem _ ha
    have := add_mem_of_mem_transStab hneg hy
    rw [show y + -a = b by rw [← hab]; abel] at this
    exact this
  · rintro ⟨a, ha, z, ⟨hzY, -⟩, rfl⟩
    rw [show a + z = z + a by abel]
    exact add_mem_of_mem_transStab ha hzY

/-- The splitting is unique. -/
theorem add_slice_unique {Y : Set V} {B : AddSubgroup V} (hAB : IsCompl (transStab Y) B)
    {a a' z z' : V} (ha : a ∈ transStab Y) (ha' : a' ∈ transStab Y)
    (hz : z ∈ B) (hz' : z' ∈ B) (h : a + z = a' + z') : a = a' ∧ z = z' := by
  have hmemA : a - a' ∈ transStab Y := AddSubgroup.sub_mem _ ha ha'
  have hmemB : a - a' ∈ B := by
    have h2 : a - a' = z' - z := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [h2]
    exact AddSubgroup.sub_mem _ hz' hz
  have hzero : a - a' = 0 := by
    have hdisj := hAB.disjoint
    have : a - a' ∈ transStab Y ⊓ B := ⟨hmemA, hmemB⟩
    rw [disjoint_iff] at hdisj
    rw [hdisj] at this
    simpa using this
  have haa : a = a' := sub_eq_zero.mp hzero
  refine ⟨haa, ?_⟩
  rw [haa] at h
  exact add_left_cancel h

/-- **The transverse slice is translation rigid.**  After removing the cylinder directions no
translation preserves what is left. -/
theorem transStab_slice_eq_bot {Y : Set V} {B : AddSubgroup V} (hAB : IsCompl (transStab Y) B)
    (hne : (Y ∩ (B : Set V)).Nonempty) : transStab (Y ∩ (B : Set V)) = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  obtain ⟨z₀, hz₀Y, hz₀B⟩ := hne
  -- `c` lies in `B`
  have hcB : c ∈ B := by
    have hz : z₀ + c ∈ Y ∩ (B : Set V) := (mem_transStab.mp hc z₀).mpr ⟨hz₀Y, hz₀B⟩
    have : c = (z₀ + c) - z₀ := by abel
    rw [this]
    exact AddSubgroup.sub_mem _ hz.2 hz₀B
  -- `c` stabilizes `Y`
  have hstep : ∀ {c' : V}, c' ∈ transStab (Y ∩ (B : Set V)) → ∀ y ∈ Y, y + c' ∈ Y := by
    intro c' hc' y hy
    obtain ⟨a, ha, z, ⟨hzY, hzB⟩, rfl⟩ := (mem_iff_exists_add_slice hAB y).mp hy
    have hzc : z + c' ∈ Y ∩ (B : Set V) := (mem_transStab.mp hc' z).mpr ⟨hzY, hzB⟩
    have hrw : a + z + c' = z + c' + a := by abel
    rw [hrw]
    exact add_mem_of_mem_transStab ha hzc.1
  have hcA : c ∈ transStab Y := by
    refine mem_transStab.mpr fun y => ⟨fun hy => ?_, fun hy => hstep hc y hy⟩
    have hneg : -c ∈ transStab (Y ∩ (B : Set V)) := AddSubgroup.neg_mem _ hc
    have := hstep hneg (y + c) hy
    rwa [show y + c + -c = y by abel] at this
  have hdisj := hAB.disjoint
  rw [disjoint_iff] at hdisj
  have : c ∈ transStab Y ⊓ B := ⟨hcA, hcB⟩
  rw [hdisj] at this
  simpa using this

/-! ### The differential gauge of a horizon -/

variable {R : Type*} [AddCommGroup R]

/-- A map commuting with the derivation commutes with all its iterates. -/
theorem pow_comp_apply {d σ : AddMonoid.End R} (hcomm : Commute d σ) (n : ℕ) (y : R) :
    (d ^ n) (σ y) = σ ((d ^ n) y) := by
  have h : (d ^ n) * σ = σ * (d ^ n) := (hcomm.pow_left n)
  exact congrArg (fun f : AddMonoid.End R => f y) h

/-- **Horizon rigidity.**  A map commuting with the derivation and fixing the `n`-th derivative of an
element displaces it by something annihilated by `δ^n`. -/
theorem pow_apply_sub_eq_zero {d σ : AddMonoid.End R} (hcomm : Commute d σ) {n : ℕ} {y : R}
    (hfix : σ ((d ^ n) y) = (d ^ n) y) : (d ^ n) (σ y - y) = 0 := by
  rw [map_sub, pow_comp_apply hcomm n y, hfix, sub_self]

/-- **Constant translations preserve every positive derivative.**  This is the converse half: a
nonzero constant in the stabilizer produces a nontrivial gauge transformation of the horizon. -/
theorem pow_apply_add_of_apply_eq_zero {d : AddMonoid.End R} {n : ℕ} (hn : 0 < n) {y c : R}
    (hc : d c = 0) : (d ^ n) (y + c) = (d ^ n) y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hcm : (d ^ (m + 1)) c = 0 := by
    rw [pow_succ]
    simp [hc]
  rw [map_add, hcm, add_zero]

/-- The displacement of the identity is zero, and displacements of the derivation-commuting maps
fixing the `n`-th derivative all lie in the kernel of `δ^n`; the two statements together say that
the horizon gauge group is the group of translations by `ker (δ^n)` elements that stabilize the
constraint. -/
theorem mem_ker_pow_of_fix {d σ : AddMonoid.End R} (hcomm : Commute d σ) {n : ℕ} {y : R}
    (hfix : σ ((d ^ n) y) = (d ^ n) y) : σ y - y ∈ AddMonoidHom.ker (d ^ n : AddMonoid.End R) :=
  pow_apply_sub_eq_zero hcomm hfix

end GaloisForLFunctions.HTGeometry
