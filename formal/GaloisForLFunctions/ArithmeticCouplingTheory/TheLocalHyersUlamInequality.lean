import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# The local Hyers–Ulam inequality

A map `ψ : ℝ → E` is `M`-approximately additive on the **triangle box**
`T_L = {(x, y) : |x|, |y|, |x + y| ≤ L}` if `‖ψ(x + y) − ψ(x) − ψ(y)‖ ≤ M` there. Hyers–Ulam stability
says such a map is close to an additive one; on a bounded box the additive approximant is linear
and the constant is absolute:

  `‖ψ(x) − (x/L) ψ(L)‖ ≤ 3M` on `[−L, L]` (`norm_sub_linear_le_three_mul`),

for every `ψ` bounded on `[−L, L]` (no regularity, no control of the bound).

Proof. `φ(x) = ψ(x) − (x/L)ψ(L)` is again `M`-approximately additive and vanishes at `L`. If `‖φ‖ ≤ B`
on `[−L, L]`, halving (`x = (x/2) + (x/2)`) gives `‖φ‖ ≤ (B + M)/2` on `[−L/2, L/2]`, and the shifts
`x = (x − L) + L`, `x + L = x + L` carry this to the outer halves at cost `M`. So `B ↦ B/2 + 3M/2`,
whose fixed point is `3M`.

The profile form (`norm_profileCoupling_sub_linear_le`) applies this to `ψ = Φ − Φ(0)`, whose
approximate additivity is the coupling `Φ(x + y) − Φ(x) − Φ(y) + Φ(0)`.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One halving step: an `M`-approximately additive map vanishing at `L` with `‖φ‖ ≤ B` on
`[−L, L]` satisfies `‖φ‖ ≤ B/2 + 3M/2` there. -/
theorem norm_le_half_add_of_approxAdditive {φ : ℝ → E} {L M B : ℝ} (hL : 0 < L)
    (hM : ∀ x y, |x| ≤ L → |y| ≤ L → |x + y| ≤ L → ‖φ (x + y) - φ x - φ y‖ ≤ M)
    (hφL : φ L = 0) (hB : ∀ x, |x| ≤ L → ‖φ x‖ ≤ B) (x : ℝ) (hx : |x| ≤ L) :
    ‖φ x‖ ≤ B / 2 + 3 * M / 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0 (by simp [hL.le]) (by simp [hL.le])
    (by simp [hL.le]))
  have hLL : |L| ≤ L := (abs_of_pos hL).le
  -- the inner half `[−L/2, L/2]`
  have inner : ∀ y, |y| ≤ L / 2 → ‖φ y‖ ≤ (B + M) / 2 := fun y hy => by
    have hy' : |y| ≤ L := hy.trans (by linarith)
    have hyy : |y + y| ≤ L := by
      rw [← two_mul, abs_mul, abs_two]; linarith
    have h1 := hM y y hy' hy' hyy
    have h2 := hB (y + y) hyy
    have h3 : ‖(2 : ℝ) • φ y‖ ≤ ‖φ (y + y)‖ + ‖φ (y + y) - φ y - φ y‖ := by
      have e : (2 : ℝ) • φ y = φ (y + y) - (φ (y + y) - φ y - φ y) := by
        rw [two_smul]; abel
      rw [e]; exact norm_sub_le _ _
    rw [norm_smul, Real.norm_two] at h3
    linarith
  rcases le_or_gt |x| (L / 2) with hx2 | hx2
  · linarith [inner x hx2]
  · rcases le_or_gt 0 x with hx0 | hx0
    · -- `x ∈ (L/2, L]`: `x = (x − L) + L`
      rw [abs_of_nonneg hx0] at hx hx2
      have hy : |x - L| ≤ L / 2 := by rw [abs_le]; constructor <;> linarith
      have hxL : |x - L + L| ≤ L := by
        rw [sub_add_cancel, abs_le]; constructor <;> linarith
      have h1 := hM (x - L) L (hy.trans (by linarith)) hLL hxL
      rw [sub_add_cancel, hφL, sub_zero] at h1
      have h2 : ‖φ x‖ ≤ ‖φ (x - L)‖ + ‖φ x - φ (x - L)‖ :=
        calc ‖φ x‖ = ‖φ (x - L) + (φ x - φ (x - L))‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith [inner (x - L) hy]
    · -- `x ∈ [−L, −L/2)`: `x + L = x + L`
      rw [abs_of_neg hx0] at hx hx2
      have hy : |x + L| ≤ L / 2 := by rw [abs_le]; constructor <;> linarith
      have h1 := hM x L (by rw [abs_of_neg hx0]; linarith) hLL (hy.trans (by linarith))
      rw [hφL, sub_zero] at h1
      have h2 : ‖φ x‖ ≤ ‖φ (x + L)‖ + ‖φ (x + L) - φ x‖ := by
        have := norm_sub_le (φ (x + L)) (φ (x + L) - φ x)
        rwa [sub_sub_cancel] at this
      linarith [inner (x + L) hy]

/-- **The local Hyers–Ulam inequality.** A map bounded on `[−L, L]` and `M`-approximately additive
on the triangle box `T_L` is within `3M` of the linear map `x ↦ (x/L) ψ(L)` on `[−L, L]`. -/
theorem norm_sub_linear_le_three_mul {ψ : ℝ → E} {L M S : ℝ} (hL : 0 < L)
    (hS : ∀ x, |x| ≤ L → ‖ψ x‖ ≤ S)
    (hM : ∀ x y, |x| ≤ L → |y| ≤ L → |x + y| ≤ L → ‖ψ (x + y) - ψ x - ψ y‖ ≤ M)
    (x : ℝ) (hx : |x| ≤ L) : ‖ψ x - (x / L) • ψ L‖ ≤ 3 * M := by
  set φ : ℝ → E := fun x => ψ x - (x / L) • ψ L with hφ
  have hφM : ∀ x y, |x| ≤ L → |y| ≤ L → |x + y| ≤ L → ‖φ (x + y) - φ x - φ y‖ ≤ M :=
    fun x y hx hy hxy => by
      have e : φ (x + y) - φ x - φ y = ψ (x + y) - ψ x - ψ y := by
        simp only [hφ, add_div, add_smul]; abel
      rw [e]; exact hM x y hx hy hxy
  have hφL : φ L = 0 := by simp [hφ, div_self hL.ne']
  have hφS : ∀ x, |x| ≤ L → ‖φ x‖ ≤ 2 * S := fun x hx => by
    have hxL : |x / L| ≤ 1 := by rw [abs_div, abs_of_pos hL, div_le_one hL]; exact hx
    have h3 : |x / L| * ‖ψ L‖ ≤ 1 * S :=
      mul_le_mul hxL (hS L (abs_of_pos hL).le) (norm_nonneg _) zero_le_one
    calc ‖φ x‖ ≤ ‖ψ x‖ + ‖(x / L) • ψ L‖ := norm_sub_le _ _
      _ = ‖ψ x‖ + |x / L| * ‖ψ L‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ S + 1 * S := add_le_add (hS x hx) h3
      _ = 2 * S := by ring
  have hiter : ∀ n : ℕ, ∀ y, |y| ≤ L → ‖φ y‖ ≤ 3 * M + (2 * S - 3 * M) * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hφS y hy
    | succ n ih =>
      intro y hy
      have := norm_le_half_add_of_approxAdditive hL hφM hφL ih y hy
      calc ‖φ y‖ ≤ (3 * M + (2 * S - 3 * M) * (1 / 2) ^ n) / 2 + 3 * M / 2 := this
        _ = 3 * M + (2 * S - 3 * M) * (1 / 2) ^ (n + 1) := by rw [pow_succ]; ring
  have hlim : Tendsto (fun n : ℕ => 3 * M + (2 * S - 3 * M) * (1 / 2 : ℝ) ^ n) atTop
      (𝓝 (3 * M + (2 * S - 3 * M) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim fun n => hiter n x hx

/-- The coupling of a profile `Φ : ℝ → E`: `Φ(x + y) − Φ(x) − Φ(y) + Φ(0)`. -/
def profileCoupling (Φ : ℝ → E) (x y : ℝ) : E := Φ (x + y) - Φ x - Φ y + Φ 0

/-- **Local Hyers–Ulam for a coupling.** A profile bounded on `[−L, L]` whose coupling is at most `M`
on the triangle box is affine up to `3M` there. -/
theorem norm_profileCoupling_sub_linear_le {Φ : ℝ → E} {L M S : ℝ} (hL : 0 < L)
    (hS : ∀ x, |x| ≤ L → ‖Φ x‖ ≤ S)
    (hM : ∀ x y, |x| ≤ L → |y| ≤ L → |x + y| ≤ L → ‖profileCoupling Φ x y‖ ≤ M)
    (x : ℝ) (hx : |x| ≤ L) : ‖Φ x - Φ 0 - (x / L) • (Φ L - Φ 0)‖ ≤ 3 * M := by
  refine norm_sub_linear_le_three_mul (ψ := fun x => Φ x - Φ 0) (S := S + ‖Φ 0‖) hL
    (fun y hy => (norm_sub_le _ _).trans (by linarith [hS y hy])) (fun y z hy hz hyz => ?_) x hx
  have e : Φ (y + z) - Φ 0 - (Φ y - Φ 0) - (Φ z - Φ 0) = profileCoupling Φ y z := by
    simp only [profileCoupling]; abel
  rw [e]; exact hM y z hy hz hyz

end GaloisForLFunctions.ArithmeticCouplingTheory
