import GaloisForLFunctions.RHTower.Sieve.FinitePhaseMomentExpansion

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem vinogradovPowerSum_le
    {N b k : ℕ} (hN : N ≠ 0) (u : Fin b → Fin N) (j : Fin k) :
    (∑ i : Fin b, (u i).val ^ (j.val + 1)) ≤ b * N ^ k := by
  have hterm : ∀ i : Fin b, (u i).val ^ (j.val + 1) ≤ N ^ k := by
    intro i
    exact (Nat.pow_le_pow_left (Nat.le_of_lt (u i).isLt) _).trans
      (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN) (by omega))
  calc
    _ ≤ ∑ _i : Fin b, N ^ k := Finset.sum_le_sum fun i _ => hterm i
    _ = b * N ^ k := by simp

def vinogradovDifferenceBoxSize (N b k : ℕ) : ℕ :=
  2 * b * N ^ k + 1

instance vinogradovDifferenceBoxSizeNeZero (N b k : ℕ) :
    NeZero (vinogradovDifferenceBoxSize N b k) := by
  exact ⟨by
    unfold vinogradovDifferenceBoxSize
    exact Nat.succ_ne_zero _⟩

def vinogradovBoundedDifferenceSignature
    {N b k : ℕ} (hN : N ≠ 0)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) :
    Fin k → Fin (vinogradovDifferenceBoxSize N b k) :=
  fun j => ⟨
    (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + b * N ^ k -
      ∑ i : Fin b, (uv.2 i).val ^ (j.val + 1),
    by
      have hx := vinogradovPowerSum_le hN uv.1 j
      have hy := vinogradovPowerSum_le hN uv.2 j
      unfold vinogradovDifferenceBoxSize
      calc
        (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + b * N ^ k -
            ∑ i : Fin b, (uv.2 i).val ^ (j.val + 1) ≤
            (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + b * N ^ k :=
          Nat.sub_le _ _
        _ ≤ b * N ^ k + b * N ^ k := Nat.add_le_add_right hx _
        _ = 2 * b * N ^ k := by ring
        _ < 2 * b * N ^ k + 1 := Nat.lt_succ_self _⟩

theorem vinogradovBoundedDifferenceSignature_cast_sub
    {N b k : ℕ} (hN : N ≠ 0)
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) (j : Fin k) :
    ((vinogradovBoundedDifferenceSignature hN uv j).val :
        ZMod (vinogradovDifferenceBoxSize N b k)) -
        (b * N ^ k : ZMod (vinogradovDifferenceBoxSize N b k)) =
      vinogradovPowerDifferenceMod
        (vinogradovDifferenceBoxSize N b k) N b k uv j := by
  have hC : (∑ i : Fin b, (uv.2 i).val ^ (j.val + 1)) ≤
      (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + b * N ^ k :=
    (vinogradovPowerSum_le hN uv.2 j).trans
      (Nat.le_add_left (b * N ^ k) _)
  change (((
      (∑ i : Fin b, (uv.1 i).val ^ (j.val + 1)) + b * N ^ k -
        ∑ i : Fin b, (uv.2 i).val ^ (j.val + 1) : ℕ) :
          ZMod (vinogradovDifferenceBoxSize N b k)) -
      (b * N ^ k : ZMod (vinogradovDifferenceBoxSize N b k))) =
    (∑ i : Fin b,
        ((uv.1 i).val : ZMod (vinogradovDifferenceBoxSize N b k)) ^
          (j.val + 1)) -
      ∑ i : Fin b,
        ((uv.2 i).val : ZMod (vinogradovDifferenceBoxSize N b k)) ^
          (j.val + 1)
  rw [Nat.cast_sub hC]
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_mul]
  ring

def vinogradovBoundedDifferenceFiberEmbedding
    {N b k : ℕ} (hN : N ≠ 0)
    (l : Fin k → Fin (vinogradovDifferenceBoxSize N b k)) :
    {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovBoundedDifferenceSignature hN uv = l} ↪
      VinogradovShiftedModSolution
        (vinogradovDifferenceBoxSize N b k) N b k
        (fun j => ((l j).val : ZMod (vinogradovDifferenceBoxSize N b k)) -
          (b * N ^ k : ZMod (vinogradovDifferenceBoxSize N b k))) where
  toFun uv := ⟨uv.1, by
    funext j
    have hj := congrFun uv.2 j
    have hdiff := vinogradovBoundedDifferenceSignature_cast_sub hN uv.1 j
    rw [hj] at hdiff
    dsimp [vinogradovPowerDifferenceMod] at hdiff
    simpa [add_comm] using sub_eq_iff_eq_add.mp hdiff.symm⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun z : VinogradovShiftedModSolution
      (vinogradovDifferenceBoxSize N b k) N b k
      (fun j => ((l j).val : ZMod (vinogradovDifferenceBoxSize N b k)) -
        (b * N ^ k : ZMod (vinogradovDifferenceBoxSize N b k))) => z.1) h

theorem card_vinogradovBoundedDifferenceFiber_le_moment
    {N b k : ℕ} (hN : N ≠ 0)
    (l : Fin k → Fin (vinogradovDifferenceBoxSize N b k)) :
    Fintype.card {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovBoundedDifferenceSignature hN uv = l} ≤
      Fintype.card (VinogradovDiagonalSolution N b k) := by
  calc
    _ ≤ Fintype.card (VinogradovShiftedModSolution
        (vinogradovDifferenceBoxSize N b k) N b k
        (fun j => ((l j).val : ZMod (vinogradovDifferenceBoxSize N b k)) -
          (b * N ^ k : ZMod (vinogradovDifferenceBoxSize N b k)))) :=
      Fintype.card_le_of_embedding
        (vinogradovBoundedDifferenceFiberEmbedding hN l)
    _ ≤ Fintype.card (VinogradovDiagonalSolution N b k) :=
      card_vinogradovShiftedModSolution_le_moment hN (by
        unfold vinogradovDifferenceBoxSize
        omega) _

/-- Exact-box weighted grouping.  Unlike modular grouping, the weight sees
the actual signed power differences (translated by the fixed midpoint), so
no periodicity hypothesis is needed. -/
theorem sum_weight_vinogradovBoundedDifference_le
    {N b k : ℕ} (hN : N ≠ 0)
    (w : (Fin k → Fin (vinogradovDifferenceBoxSize N b k)) → ℝ)
    (hw : ∀ l, 0 ≤ w l) :
    (∑ uv : (Fin b → Fin N) × (Fin b → Fin N),
        w (vinogradovBoundedDifferenceSignature hN uv)) ≤
      Fintype.card (VinogradovDiagonalSolution N b k) *
        ∑ l : Fin k → Fin (vinogradovDifferenceBoxSize N b k), w l := by
  exact sum_comp_le_uniform_fiber_mul
    (vinogradovBoundedDifferenceSignature hN) w hw
    (Fintype.card (VinogradovDiagonalSolution N b k))
    (card_vinogradovBoundedDifferenceFiber_le_moment hN)

end

end RHTower.Sieve
