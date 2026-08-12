import GaloisForLFunctions.RHTower.Sieve.VinogradovShiftedMoment

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

theorem sum_comp_eq_sum_card_fiber_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (w : β → ℝ) :
    (∑ a : α, w (f a)) =
      ∑ b : β, Fintype.card {a : α // f a = b} * w b := by
  rw [← Fintype.sum_fiberwise f (fun a => w (f a))]
  apply Finset.sum_congr rfl
  intro b _
  have hterm : ∀ i : {a : α // f a = b}, w (f i.1) = w b :=
    fun i => congrArg w i.2
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]

theorem sum_comp_le_uniform_fiber_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) (J : ℕ)
    (hfiber : ∀ b, Fintype.card {a : α // f a = b} ≤ J) :
    (∑ a : α, w (f a)) ≤ J * ∑ b : β, w b := by
  rw [sum_comp_eq_sum_card_fiber_mul]
  calc
    (∑ b : β, (Fintype.card {a : α // f a = b} : ℝ) * w b) ≤
        ∑ b : β, (J : ℝ) * w b := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber b) (hw b)
    _ = J * ∑ b : β, w b := by rw [Finset.mul_sum]

def vinogradovPowerDifferenceMod
    (q N b k : ℕ) [NeZero q]
    (uv : (Fin b → Fin N) × (Fin b → Fin N)) : Fin k → ZMod q :=
  vinogradovPowerSignatureMod q k uv.1 -
    vinogradovPowerSignatureMod q k uv.2

def vinogradovPowerDifferenceFiberEquiv
    {q N b k : ℕ} [NeZero q] (l : Fin k → ZMod q) :
    {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovPowerDifferenceMod q N b k uv = l} ≃
      VinogradovShiftedModSolution q N b k l where
  toFun uv := ⟨uv.1, by
    have h := uv.2
    dsimp [vinogradovPowerDifferenceMod] at h
    simpa [add_comm] using sub_eq_iff_eq_add.mp h⟩
  invFun uv := ⟨uv.1, by
    dsimp [vinogradovPowerDifferenceMod]
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using uv.2)⟩
  left_inv := fun uv => Subtype.ext rfl
  right_inv := fun uv => Subtype.ext rfl

theorem card_vinogradovPowerDifferenceFiber_le_moment
    {q N b k : ℕ} [NeZero q] (hN : N ≠ 0)
    (hq : 2 * b * N ^ k < q) (l : Fin k → ZMod q) :
    Fintype.card {uv : (Fin b → Fin N) × (Fin b → Fin N) //
      vinogradovPowerDifferenceMod q N b k uv = l} ≤
      Fintype.card (VinogradovDiagonalSolution N b k) := by
  rw [Fintype.card_congr (vinogradovPowerDifferenceFiberEquiv l)]
  exact card_vinogradovShiftedModSolution_le_moment hN hq l

/-- Finite weighted grouping form of the Vinogradov moment bound.  It is
the exact combinatorial replacement for grouping an expanded exponential
moment by its vector of power differences. -/
theorem sum_weight_vinogradovPowerDifferenceMod_le
    {q N b k : ℕ} [NeZero q] (hN : N ≠ 0)
    (hq : 2 * b * N ^ k < q)
    (w : (Fin k → ZMod q) → ℝ) (hw : ∀ l, 0 ≤ w l) :
    (∑ uv : (Fin b → Fin N) × (Fin b → Fin N),
        w (vinogradovPowerDifferenceMod q N b k uv)) ≤
      Fintype.card (VinogradovDiagonalSolution N b k) *
        ∑ l : Fin k → ZMod q, w l := by
  exact sum_comp_le_uniform_fiber_mul
    (vinogradovPowerDifferenceMod q N b k) w hw
    (Fintype.card (VinogradovDiagonalSolution N b k))
    (card_vinogradovPowerDifferenceFiber_le_moment hN hq)

theorem sum_weight_vinogradovRouteTPowerDifferenceMod_le
    {q N s : ℕ} [NeZero q] (hs : 1 ≤ s) (hN : N ≠ 0)
    (hq : 2 * (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s) *
      N ^ (vinogradovRouteTOrder s) < q)
    (w : (Fin (vinogradovRouteTOrder s) → ZMod q) → ℝ)
    (hw : ∀ l, 0 ≤ w l) :
    (∑ uv :
        (Fin (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s) → Fin N) ×
          (Fin (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s) → Fin N),
        w (vinogradovPowerDifferenceMod q N
          (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s)
          (vinogradovRouteTOrder s) uv)) ≤
      (vinogradovMeanConstant
          (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) *
        N ^ (2 * vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s -
            vinogradovRouteTOrder s * (vinogradovRouteTOrder s + 1) / 2 +
          (350 * s + 2))) *
        ∑ l : Fin (vinogradovRouteTOrder s) → ZMod q, w l := by
  calc
    _ ≤ Fintype.card (VinogradovDiagonalSolution N
          (vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s)
          (vinogradovRouteTOrder s)) *
        ∑ l : Fin (vinogradovRouteTOrder s) → ZMod q, w l :=
      sum_weight_vinogradovPowerDifferenceMod_le hN hq w hw
    _ ≤ (vinogradovMeanConstant
          (vinogradovRouteTOrder s) (vinogradovRouteTMomentSteps s) *
        N ^ (2 * vinogradovRouteTOrder s * vinogradovRouteTMomentSteps s -
            vinogradovRouteTOrder s * (vinogradovRouteTOrder s + 1) / 2 +
          (350 * s + 2))) *
        ∑ l : Fin (vinogradovRouteTOrder s) → ZMod q, w l := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast vinogradovRouteT_mean_value_bound hs hN
      · exact Finset.sum_nonneg fun l _ => hw l

end

end RHTower.Sieve
