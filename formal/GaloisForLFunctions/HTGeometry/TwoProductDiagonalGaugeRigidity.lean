import Mathlib.Data.PNat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.FibreDichotomy

/-!
# Two-product diagonal-gauge rigidity

Positive integers carry two distinct formation products: addition and multiplication. A diagonal
gauge with values in a group that respects both products is necessarily trivial.

This is the unconditional algebraic theorem proved in the Stage-2 universal-law-field card
`two-product-formation-mechanics/positive-integer-two-product-diagonal-gauge-rigidity-law.md`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A group-valued diagonal weight on positive-integer packets which respects both ordinary
additive fusion and multiplicative/Dirichlet fusion. The two products remain distinct. -/
structure TwoProductDiagonalGauge (G : Type*) [Group G] where
  weight : ℕ+ → G
  map_add : ∀ m n, weight (m + n) = weight m * weight n
  map_mul : ∀ m n, weight (m * n) = weight m * weight n

namespace TwoProductDiagonalGauge

variable {G : Type*} [Group G]

/-- Identity weight: canonical simultaneous diagonal gauge. -/
def trivial : TwoProductDiagonalGauge G where
  weight := fun _ => 1
  map_add := by simp
  map_mul := by simp

@[simp]
theorem trivial_weight (n : ℕ+) : (trivial : TwoProductDiagonalGauge G).weight n = 1 := rfl

/-- Multiplicative preservation at unit kills additive generator. -/
theorem weight_one_eq_one (g : TwoProductDiagonalGauge G) : g.weight 1 = 1 := by
  have h := g.map_mul 1 1
  have h' : g.weight 1 = g.weight 1 * g.weight 1 := by simpa using h
  calc
    g.weight 1 = (g.weight 1)⁻¹ * (g.weight 1 * g.weight 1) := by simp
    _ = (g.weight 1)⁻¹ * g.weight 1 := by rw [← h']
    _ = 1 := by simp

/-- **Two-product rigidity.** Every simultaneous additive/multiplicative diagonal weight on
positive integers is identity weight. -/
theorem weight_eq_one (g : TwoProductDiagonalGauge G) (n : ℕ+) : g.weight n = 1 := by
  induction n using PNat.recOn with
  | one => exact weight_one_eq_one g
  | succ n ih =>
      rw [g.map_add n 1, ih, weight_one_eq_one, mul_one]

/-- Two simultaneous diagonal gauges are equal; their moduli space is a point. -/
@[ext]
theorem ext (g h : TwoProductDiagonalGauge G) : g = h := by
  cases g with
  | mk gw ga gm =>
      cases h with
      | mk hw ha hm =>
          have hwh : gw = hw := by
            funext n
            calc
              gw n = 1 := weight_eq_one ⟨gw, ga, gm⟩ n
              _ = hw n := (weight_eq_one ⟨hw, ha, hm⟩ n).symm
          subst hwh
          rfl

/-- Common diagonal-gauge space of two packet products is contractible. -/
instance instUnique : Unique (TwoProductDiagonalGauge G) where
  default := trivial
  uniq g := ext g trivial

/-- Real radial weight on positive integers. -/
noncomputable def positiveRadialWeight (a : ℝ) (n : ℕ+) : ℝ := ((n : ℕ) : ℝ) ^ a

/-- Radial weights always respect multiplicative/Dirichlet fusion. -/
theorem positiveRadialWeight_mul (a : ℝ) (m n : ℕ+) :
    positiveRadialWeight a (m * n) =
      positiveRadialWeight a m * positiveRadialWeight a n := by
  have hm : 0 ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
  simpa [positiveRadialWeight] using Real.mul_rpow (z := a) hm hn

/-- Real radial weight respects ordinary additive packet fusion exactly at neutral grade. -/
theorem positiveRadialWeight_map_add_iff (a : ℝ) :
    (∀ m n : ℕ+, positiveRadialWeight a (m + n) =
      positiveRadialWeight a m * positiveRadialWeight a n) ↔ a = 0 := by
  constructor
  · intro h
    have h11 := h 1 1
    have htwo : (2 : ℝ) ^ a = 1 := by
      simpa [positiveRadialWeight] using h11
    exact (DerivedSelection.rpow_eq_one_iff_of_one_lt (by norm_num : (1 : ℝ) < 2)).mp htwo
  · rintro rfl
    intro m n
    simp [positiveRadialWeight]

/-! ## Atom-level packet formulation -/

/-- Positive-integer packet atom with invertible amplitude. -/
@[ext]
structure PacketAtom (G : Type*) where
  index : ℕ+
  amplitude : G

/-- Ordinary additive/Cauchy fusion of packet atoms. -/
def PacketAtom.addFuse {G : Type*} [Mul G]
    (x y : PacketAtom G) : PacketAtom G :=
  ⟨x.index + y.index, x.amplitude * y.amplitude⟩

/-- Multiplicative/Dirichlet fusion of packet atoms. -/
def PacketAtom.mulFuse {G : Type*} [Mul G]
    (x y : PacketAtom G) : PacketAtom G :=
  ⟨x.index * y.index, x.amplitude * y.amplitude⟩

/-- Diagonal action of a weight on packet atoms. -/
def PacketAtom.diagonalAction {G : Type*} [Mul G]
    (w : ℕ+ → G) (x : PacketAtom G) : PacketAtom G :=
  ⟨x.index, w x.index * x.amplitude⟩

/-- A diagonal action preserves ordinary additive atom fusion. -/
def PreservesAdditiveAtomFusion {G : Type*} [Mul G] (w : ℕ+ → G) : Prop :=
  ∀ x y : PacketAtom G,
    PacketAtom.diagonalAction w (PacketAtom.addFuse x y) =
      PacketAtom.addFuse (PacketAtom.diagonalAction w x)
        (PacketAtom.diagonalAction w y)

/-- A diagonal action preserves multiplicative/Dirichlet atom fusion. -/
def PreservesMultiplicativeAtomFusion {G : Type*} [Mul G] (w : ℕ+ → G) : Prop :=
  ∀ x y : PacketAtom G,
    PacketAtom.diagonalAction w (PacketAtom.mulFuse x y) =
      PacketAtom.mulFuse (PacketAtom.diagonalAction w x)
        (PacketAtom.diagonalAction w y)

theorem preservesAdditiveAtomFusion_of_gauge {H : Type*} [CommGroup H]
    (g : TwoProductDiagonalGauge H) : PreservesAdditiveAtomFusion g.weight := by
  intro x y
  ext <;> simp [PacketAtom.diagonalAction, PacketAtom.addFuse, g.map_add]
  ac_rfl

theorem preservesMultiplicativeAtomFusion_of_gauge {H : Type*} [CommGroup H]
    (g : TwoProductDiagonalGauge H) : PreservesMultiplicativeAtomFusion g.weight := by
  intro x y
  ext <;> simp [PacketAtom.diagonalAction, PacketAtom.mulFuse, g.map_mul]
  ac_rfl

/-- Atomwise preservation of both packet products is exactly two-product diagonal-gauge data. -/
theorem preservesBothAtomFusions_iff_exists_gauge {H : Type*} [CommGroup H] (w : ℕ+ → H) :
    PreservesAdditiveAtomFusion w ∧ PreservesMultiplicativeAtomFusion w ↔
      ∃ g : TwoProductDiagonalGauge H, g.weight = w := by
  constructor
  · rintro ⟨hadd, hmul⟩
    let g : TwoProductDiagonalGauge H :=
      { weight := w
        map_add := by
          intro m n
          have h := hadd ⟨m, 1⟩ ⟨n, 1⟩
          simpa [PacketAtom.diagonalAction, PacketAtom.addFuse] using
            congrArg PacketAtom.amplitude h
        map_mul := by
          intro m n
          have h := hmul ⟨m, 1⟩ ⟨n, 1⟩
          simpa [PacketAtom.diagonalAction, PacketAtom.mulFuse] using
            congrArg PacketAtom.amplitude h }
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨preservesAdditiveAtomFusion_of_gauge g,
      preservesMultiplicativeAtomFusion_of_gauge g⟩

/-- **Packet form of two-product rigidity.** A diagonal atom action preserving both source
formation products has identity weight. -/
theorem weight_eq_one_of_preservesBothAtomFusions {H : Type*} [CommGroup H]
    (w : ℕ+ → H) (hadd : PreservesAdditiveAtomFusion w)
    (hmul : PreservesMultiplicativeAtomFusion w) (n : ℕ+) : w n = 1 := by
  obtain ⟨g, hg⟩ := (preservesBothAtomFusions_iff_exists_gauge w).mp ⟨hadd, hmul⟩
  rw [← hg]
  exact weight_eq_one g n

end TwoProductDiagonalGauge

end GaloisForLFunctions.HTGeometry
