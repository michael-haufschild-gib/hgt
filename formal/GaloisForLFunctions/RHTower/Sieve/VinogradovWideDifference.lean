import GaloisForLFunctions.RHTower.Sieve.VinogradovBoundedDifference

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Symmetric exact-difference box with user-chosen radius.  Route T needs a
radius twice the raw Vinogradov difference bound so every Fejér pair
difference remains inside one injective box. -/
def vinogradovWideDifferenceBoxSize (R : ℕ) : ℕ :=
  2 * R + 1

instance vinogradovWideDifferenceBoxSizeNeZero (R : ℕ) :
    NeZero (vinogradovWideDifferenceBoxSize R) := by
  exact ⟨by unfold vinogradovWideDifferenceBoxSize; omega⟩

def vinogradovWideDifferenceSignature
    {N b k R : ℕ} (hN : N ≠ 0) (hR : b * N ^ k ≤ R)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) :
    Fin k → Fin (vinogradovWideDifferenceBoxSize R) :=
  fun j => ⟨
    (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + R -
      ∑ i : Fin b, (uv.2 i).val ^ (j.val + 1),
    by
      have hx := vinogradovPowerSum_le hN uv.1 j
      have hy := vinogradovPowerSum_le hN uv.2 j
      have hyR : (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) ≤ R :=
        hy.trans hR
      unfold vinogradovWideDifferenceBoxSize
      calc
        (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + R -
            ∑ i : Fin b, (uv.2 i).val ^ (j.val + 1) ≤
            (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + R :=
          Nat.sub_le _ _
        _ ≤ R + R := Nat.add_le_add_right (hx.trans hR) R
        _ = 2 * R := by omega
        _ < 2 * R + 1 := Nat.lt_succ_self _⟩

theorem vinogradovWideDifferenceSignature_cast_sub
    {N b k R : ℕ} (hN : N ≠ 0) (hR : b * N ^ k ≤ R)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) (j : Fin k) :
    ((vinogradovWideDifferenceSignature hN hR uv j).val :
        ZMod (vinogradovWideDifferenceBoxSize R)) -
        (R : ZMod (vinogradovWideDifferenceBoxSize R)) =
      vinogradovPowerDifferenceMod
        (vinogradovWideDifferenceBoxSize R) N b k uv j := by
  have hyR : (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) ≤ R :=
    (vinogradovPowerSum_le hN uv.2 j).trans hR
  have hsub : (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) ≤
      (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + R :=
    hyR.trans (Nat.le_add_left R _)
  change ((
      ((∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + R -
        ∑ i : Fin b, (uv.2 i).val ^ (j.val + 1) : ℕ) :
          ZMod (vinogradovWideDifferenceBoxSize R)) -
      (R : ZMod (vinogradovWideDifferenceBoxSize R))) =
    (∑ i : Fin b,
        ((uv.1 i).val : ZMod (vinogradovWideDifferenceBoxSize R)) ^
          (j.val + 1)) -
      ∑ i : Fin b,
        ((uv.2 i).val : ZMod (vinogradovWideDifferenceBoxSize R)) ^
          (j.val + 1)
  rw [Nat.cast_sub hsub]
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_add]
  ring

def vinogradovWideDifferenceFiberEmbedding
    {N b k R : ℕ} (hN : N ≠ 0) (hR : b * N ^ k ≤ R)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize R)) :
    {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovWideDifferenceSignature hN hR uv = l} ↪
      VinogradovShiftedModSolution
        (vinogradovWideDifferenceBoxSize R) N b k
        (fun j => ((l j).val : ZMod (vinogradovWideDifferenceBoxSize R)) -
          (R : ZMod (vinogradovWideDifferenceBoxSize R))) where
  toFun uv := ⟨uv.1, by
    funext j
    have hj := congrFun uv.2 j
    have hdiff := vinogradovWideDifferenceSignature_cast_sub hN hR uv.1 j
    rw [hj] at hdiff
    dsimp [vinogradovPowerDifferenceMod] at hdiff
    simpa [add_comm] using sub_eq_iff_eq_add.mp hdiff.symm⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun z : VinogradovShiftedModSolution
      (vinogradovWideDifferenceBoxSize R) N b k
      (fun j => ((l j).val : ZMod (vinogradovWideDifferenceBoxSize R)) -
        (R : ZMod (vinogradovWideDifferenceBoxSize R))) => z.1) h

theorem card_vinogradovWideDifferenceFiber_le_moment
    {N b k R : ℕ} (hN : N ≠ 0) (hR : b * N ^ k ≤ R)
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize R)) :
    Fintype.card {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovWideDifferenceSignature hN hR uv = l} ≤
      Fintype.card (VinogradovDiagonalSolution N b k) := by
  calc
    _ ≤ Fintype.card (VinogradovShiftedModSolution
        (vinogradovWideDifferenceBoxSize R) N b k
        (fun j => ((l j).val : ZMod (vinogradovWideDifferenceBoxSize R)) -
          (R : ZMod (vinogradovWideDifferenceBoxSize R)))) :=
      Fintype.card_le_of_embedding
        (vinogradovWideDifferenceFiberEmbedding hN hR l)
    _ ≤ Fintype.card (VinogradovDiagonalSolution N b k) :=
      card_vinogradovShiftedModSolution_le_moment hN (by
        have htwice : 2 * (b * N ^ k) ≤ 2 * R :=
          Nat.mul_le_mul_left 2 hR
        unfold vinogradovWideDifferenceBoxSize
        calc
          2 * b * N ^ k = 2 * (b * N ^ k) := by ring
          _ ≤ 2 * R := htwice
          _ < 2 * R + 1 := Nat.lt_succ_self _) _

theorem sum_weight_vinogradovWideDifference_le
    {N b k R : ℕ} (hN : N ≠ 0) (hR : b * N ^ k ≤ R)
    (w : (Fin k → Fin (vinogradovWideDifferenceBoxSize R)) → ℝ)
    (hw : ∀ l, 0 ≤ w l) :
    (∑ uv : (Fin b → Fin N) × (Fin b → Fin N),
        w (vinogradovWideDifferenceSignature hN hR uv)) ≤
      Fintype.card (VinogradovDiagonalSolution N b k) *
        ∑ l : Fin k → Fin (vinogradovWideDifferenceBoxSize R), w l := by
  exact sum_comp_le_uniform_fiber_mul
    (vinogradovWideDifferenceSignature hN hR) w hw
    (Fintype.card (VinogradovDiagonalSolution N b k))
    (card_vinogradovWideDifferenceFiber_le_moment hN hR)

def vinogradovWideCenteredDifference
    {k R : ℕ}
    (l : Fin k → Fin (vinogradovWideDifferenceBoxSize R)) (j : Fin k) : ℝ :=
  (l j).val - R

theorem vinogradovWideCenteredDifference_signature
    {N b k R : ℕ} (hN : N ≠ 0) (hR : b * N ^ k ≤ R)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) (j : Fin k) :
    vinogradovWideCenteredDifference
        (vinogradovWideDifferenceSignature hN hR uv) j =
      (∑ i : Fin b, ((uv.1 i).val : ℝ) ^ (j.val + 1)) -
        ∑ i : Fin b, ((uv.2 i).val : ℝ) ^ (j.val + 1) := by
  have hyR : (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) ≤ R :=
    (vinogradovPowerSum_le hN uv.2 j).trans hR
  have hsub : (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) ≤
      (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + R :=
    hyR.trans (Nat.le_add_left R _)
  unfold vinogradovWideCenteredDifference vinogradovWideDifferenceSignature
  rw [Nat.cast_sub hsub]
  push_cast
  ring

end

end RHTower.Sieve
