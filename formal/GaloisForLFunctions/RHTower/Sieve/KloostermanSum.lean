import GaloisForLFunctions.RHTower.ChenGuptaLiRamanujanFourier

/-!
# Complete Kloosterman sums

This file supplies the finite arithmetic kernel used by the Deshouillers--Iwaniec spectral
estimate: the classical complete Kloosterman sum over units modulo a positive modulus.  It proves
its unit-modulus phase law, exact zero-frequency value, inversion symmetry, unit-frequency
transport, conjugation law, and elementary totient bound.  Sharper Weil and spectral estimates
build on this layer.
-/

open scoped BigOperators

noncomputable section

namespace RHTower.Sieve

/-- Complete classical Kloosterman phase over one unit residue. -/
def kloostermanPhase (q : ℕ) [NeZero q] (m n : ZMod q)
    (x : (ZMod q)ˣ) : ℂ :=
  ZMod.stdAddChar
    (m * (x : ZMod q) + n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q))

/-- Classical complete Kloosterman sum `S(m,n;q)`. -/
def kloostermanSum (q : ℕ) [NeZero q] (m n : ZMod q) : ℂ :=
  ∑ x : (ZMod q)ˣ, kloostermanPhase q m n x

/-- Inversion is an equivalence of the reduced residue classes. -/
def kloostermanUnitInvEquiv (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ (ZMod q)ˣ where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := by simp
  right_inv x := by simp

/-- Left multiplication by a unit permutes the reduced residue classes. -/
def kloostermanUnitMulEquiv (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    (ZMod q)ˣ ≃ (ZMod q)ˣ where
  toFun x := a * x
  invFun x := a⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

@[simp] theorem norm_kloostermanPhase
    (q : ℕ) [NeZero q] (m n : ZMod q) (x : (ZMod q)ˣ) :
    ‖kloostermanPhase q m n x‖ = 1 := by
  simp [kloostermanPhase]

/-- The elementary cardinality bound `|S(m,n;q)| ≤ φ(q)`. -/
theorem norm_kloostermanSum_le_totient
    (q : ℕ) [NeZero q] (m n : ZMod q) :
    ‖kloostermanSum q m n‖ ≤ (Nat.totient q : ℝ) := by
  unfold kloostermanSum
  calc
    ‖∑ x : (ZMod q)ˣ, kloostermanPhase q m n x‖ ≤
        ∑ x : (ZMod q)ˣ, ‖kloostermanPhase q m n x‖ := norm_sum_le _ _
    _ = (Fintype.card (ZMod q)ˣ : ℝ) := by simp
    _ = (Nat.totient q : ℝ) := by rw [ZMod.card_units_eq_totient]

/-- At zero frequency every reduced residue contributes one. -/
@[simp] theorem kloostermanSum_zero_zero
    (q : ℕ) [NeZero q] :
    kloostermanSum q 0 0 = (Nat.totient q : ℂ) := by
  simp [kloostermanSum, kloostermanPhase, ZMod.card_units_eq_totient]

/-- Kloosterman symmetry `S(m,n;q) = S(n,m;q)` from unit inversion. -/
theorem kloostermanSum_comm
    (q : ℕ) [NeZero q] (m n : ZMod q) :
    kloostermanSum q m n = kloostermanSum q n m := by
  let e := kloostermanUnitInvEquiv q
  calc
    kloostermanSum q m n =
        ∑ x : (ZMod q)ˣ, kloostermanPhase q m n (e x) := by
          rw [kloostermanSum]
          exact (e.sum_comp (kloostermanPhase q m n)).symm
    _ = ∑ x : (ZMod q)ˣ, kloostermanPhase q n m x := by
          apply Fintype.sum_congr
          intro x
          simp [e, kloostermanUnitInvEquiv, kloostermanPhase, add_comm]
    _ = kloostermanSum q n m := rfl

/-- Moving a unit factor between frequencies leaves the complete sum unchanged. -/
theorem kloostermanSum_unit_mul_left
    (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (m n : ZMod q) :
    kloostermanSum q ((a : ZMod q) * m) n =
      kloostermanSum q m ((a : ZMod q) * n) := by
  let e := kloostermanUnitMulEquiv q a
  calc
    kloostermanSum q ((a : ZMod q) * m) n =
        ∑ x : (ZMod q)ˣ, kloostermanPhase q m ((a : ZMod q) * n) (e x) := by
          rw [kloostermanSum]
          apply Fintype.sum_congr
          intro x
          simp [e, kloostermanUnitMulEquiv, kloostermanPhase]
          have ha : (a : ZMod q) * ((a⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv a
          have hcancel :
              (a : ZMod q) * n * (x⁻¹ : (ZMod q)ˣ) *
                  ((a⁻¹ : (ZMod q)ˣ) : ZMod q) =
                n * (x⁻¹ : (ZMod q)ˣ) := by
            calc
              _ = n * (x⁻¹ : (ZMod q)ˣ) *
                  ((a : ZMod q) * ((a⁻¹ : (ZMod q)ˣ) : ZMod q)) := by ring
              _ = _ := by rw [ha]; ring
          have hcancel' :
              (a : ZMod q) * n *
                  (((x⁻¹ : (ZMod q)ˣ) : ZMod q) *
                    ((a⁻¹ : (ZMod q)ˣ) : ZMod q)) =
                n * (x⁻¹ : (ZMod q)ˣ) := by
            calc
              _ = (a : ZMod q) * n * (x⁻¹ : (ZMod q)ˣ) *
                  ((a⁻¹ : (ZMod q)ˣ) : ZMod q) := by ring
              _ = _ := hcancel
          rw [hcancel']
          congr 1
          ring
    _ = kloostermanSum q m ((a : ZMod q) * n) := by
          rw [kloostermanSum]
          exact e.sum_comp (kloostermanPhase q m ((a : ZMod q) * n))

/-- A unit first frequency reduces to first frequency one. -/
theorem kloostermanSum_unit_left
    (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (n : ZMod q) :
    kloostermanSum q (a : ZMod q) n =
      kloostermanSum q 1 ((a : ZMod q) * n) := by
  simpa using kloostermanSum_unit_mul_left q a 1 n

/-- Complex conjugation negates both Kloosterman frequencies. -/
theorem star_kloostermanSum
    (q : ℕ) [NeZero q] (m n : ZMod q) :
    star (kloostermanSum q m n) = kloostermanSum q (-m) (-n) := by
  unfold kloostermanSum
  change (starRingEnd ℂ) (∑ x : (ZMod q)ˣ, kloostermanPhase q m n x) = _
  rw [map_sum]
  apply Fintype.sum_congr
  intro x
  rw [kloostermanPhase, kloostermanPhase, ← AddChar.map_neg_eq_conj]
  congr 1
  ring

end RHTower.Sieve
