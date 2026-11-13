import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartIsWeilsFormOfTheZerosMinusThePoles
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheStepPacketsOfAWindowFormATowerUnderRefinement

/-!
# The functional equation reflects every window at infinite block size

At infinite block size a window is the logarithmic interval `[log R, log ρR]`, and its form is
Weil's form on all packets supported there, not only on step packets. Weil's form of a packet
depends on the packet only through its autocorrelation and through the product of its two
degrees. Both are invariant under the reflection `u ↦ c − u` of the line:

* the autocorrelation does not change (`packetAutocorr_reflect`): `h(x)` is even;
* the two degrees are exchanged, up to the reciprocal factors `e^{∓c/2}`
  (`integral_reflect_mul_exp_neg`, `integral_reflect_mul_exp`), so their product is unchanged.

Hence Weil's form and its neutral part are invariant under reflection (`packetForm_reflect`,
`neutralForm_reflect`). With the translations (AGZ, `packetForm_translate`) the window form at
infinite block size carries the full symmetry group of the line. For the window
`[log R, log ρR]` the reflection about its centre is `x ↦ ρR²/x`: the functional equation
`s ↦ 1 − s` acts as the reflection of every window. The step packets are not preserved — the
reflection of a step function on unit blocks is a step function on the reciprocal blocks — so
the symmetry belongs to the limit of the tower, not to any of its members.

The floor maps of the integers `k` with `log k` at least half the length of the window — the
shallow ones, of depth one — are **selective** (`shallow_contact_selective`): their contribution
`−2 (Λ(k)/√k) h(log k)` is nonnegative on every packet with one node at the centre, because the
autocorrelation of such a packet is nonpositive at every shift beyond half the window
(`packetAutocorr_nonpos_of_node`), and nonpositive on every packet of one sign. With the true
weights the shallow trees lift the odd one-node states and deepen the even one-signed ones; a
negative weight does the opposite.
-/

open MeasureTheory
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- The reflection of a packet about the point `c / 2`. -/
def reflectPacket (c : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := g (c - u)

/-- **The autocorrelation is invariant under reflection.** -/
theorem packetAutocorr_reflect (c : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    packetAutocorr (reflectPacket c g) x = packetAutocorr g x := by
  unfold packetAutocorr reflectPacket
  have h1 : ∫ u, g (c - u) * g (c - (u + x)) = ∫ v, g v * g (v - x) := by
    have := integral_sub_left_eq_self (fun v => g v * g (v - x)) (μ := volume) c
    refine (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)).trans this
    show g (c - u) * g (c - (u + x)) = g (c - u) * g (c - u - x)
    ring_nf
  have h2 : ∫ v, g v * g (v - x) = ∫ w, g w * g (w + x) := by
    have := integral_add_right_eq_self (fun v => g v * g (v - x)) (μ := volume) x
    refine this.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
    show g (w + x) * g (w + x - x) = g w * g (w + x)
    rw [add_sub_cancel_right, mul_comm]
  rw [h1, h2]

/-- The degree against `e^{−u/2}` of a reflected packet is `e^{−c/2}` times the other degree. -/
theorem integral_reflect_mul_exp_neg (c : ℝ) (g : ℝ → ℝ) :
    ∫ u, reflectPacket c g u * Real.exp (-u / 2) =
      Real.exp (-c / 2) * ∫ v, g v * Real.exp (v / 2) := by
  unfold reflectPacket
  have := integral_sub_left_eq_self (fun v => g v * Real.exp (-(c - v) / 2)) (μ := volume) c
  rw [← integral_const_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)).trans
    (this.trans (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)))
  · show g (c - u) * Real.exp (-u / 2) = g (c - u) * Real.exp (-(c - (c - u)) / 2)
    ring_nf
  · show g v * Real.exp (-(c - v) / 2) = Real.exp (-c / 2) * (g v * Real.exp (v / 2))
    rw [show -(c - v) / 2 = -c / 2 + v / 2 by ring, Real.exp_add]
    ring

/-- The degree against `e^{u/2}` of a reflected packet is `e^{c/2}` times the other degree. -/
theorem integral_reflect_mul_exp (c : ℝ) (g : ℝ → ℝ) :
    ∫ u, reflectPacket c g u * Real.exp (u / 2) =
      Real.exp (c / 2) * ∫ v, g v * Real.exp (-v / 2) := by
  unfold reflectPacket
  have := integral_sub_left_eq_self (fun v => g v * Real.exp ((c - v) / 2)) (μ := volume) c
  rw [← integral_const_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)).trans
    (this.trans (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)))
  · show g (c - u) * Real.exp (u / 2) = g (c - u) * Real.exp ((c - (c - u)) / 2)
    ring_nf
  · show g v * Real.exp ((c - v) / 2) = Real.exp (c / 2) * (g v * Real.exp (-v / 2))
    rw [show (c - v) / 2 = c / 2 + -v / 2 by ring, Real.exp_add]
    ring

theorem levyJump_reflect (c : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    levyJump (reflectPacket c g) x = levyJump g x := by
  simp only [levyJump, packetAutocorr_reflect]

/-- **Weil's form of a packet is invariant under reflection**: the functional equation. -/
theorem packetForm_reflect (Q : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    packetForm Q (reflectPacket c g) = packetForm Q g := by
  have he : Real.exp (-c / 2) * Real.exp (c / 2) = 1 := by
    rw [← Real.exp_add, show -c / 2 + c / 2 = 0 by ring, Real.exp_zero]
  unfold packetForm
  simp only [packetAutocorr_reflect, levyJump_reflect]
  rw [integral_reflect_mul_exp_neg, integral_reflect_mul_exp]
  generalize (∫ u, g u * Real.exp (-u / 2)) = A
  generalize (∫ u, g u * Real.exp (u / 2)) = B
  linear_combination (2 * A * B) * he

/-- **The neutral part of a window is invariant under reflection** at infinite block size. -/
theorem neutralForm_reflect (Q : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    neutralForm Q (reflectPacket c g) = neutralForm Q g := by
  have he : Real.exp (-c / 2) * Real.exp (c / 2) = 1 := by
    rw [← Real.exp_add, show -c / 2 + c / 2 = 0 by ring, Real.exp_zero]
  unfold neutralForm
  rw [packetForm_reflect, integral_reflect_mul_exp_neg, integral_reflect_mul_exp]
  generalize (∫ u, g u * Real.exp (-u / 2)) = A
  generalize (∫ u, g u * Real.exp (u / 2)) = B
  linear_combination (2 * A * B) * he

/-- The reflection about the centre of the window `[a, b]` keeps the window. -/
theorem reflectPacket_support {a b : ℝ} {g : ℝ → ℝ} (hg : ∀ u, u < a ∨ b < u → g u = 0) :
    ∀ u, u < a ∨ b < u → reflectPacket (a + b) g u = 0 := by
  intro u hu
  unfold reflectPacket
  refine hg _ ?_
  rcases hu with h | h
  · right; linarith
  · left; linarith

/-! ### The shallow floor maps are selective -/

/-- **A packet with one node at the centre of its window has nonpositive autocorrelation at every
shift of at least half the window**: the two factors lie on opposite halves. -/
theorem packetAutocorr_nonpos_of_node {g : ℝ → ℝ} {a b ℓ : ℝ}
    (hsupp : ∀ u, u < a ∨ b < u → g u = 0) (hleft : ∀ u, u ≤ (a + b) / 2 → 0 ≤ g u)
    (hright : ∀ u, (a + b) / 2 ≤ u → g u ≤ 0) (hℓ : (b - a) / 2 ≤ ℓ) :
    packetAutocorr g ℓ ≤ 0 := by
  refine integral_nonpos fun u => ?_
  show g u * g (u + ℓ) ≤ 0
  by_cases hu : u < a
  · rw [hsupp u (Or.inl hu), zero_mul]
  by_cases hu' : b < u + ℓ
  · rw [hsupp (u + ℓ) (Or.inr hu'), mul_zero]
  push Not at hu hu'
  exact mul_nonpos_of_nonneg_of_nonpos (hleft u (by linarith)) (hright (u + ℓ) (by linarith))

/-- A packet of one sign has nonnegative autocorrelation. -/
theorem packetAutocorr_nonneg_of_nonneg {g : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u) (ℓ : ℝ) :
    0 ≤ packetAutocorr g ℓ :=
  integral_nonneg fun u => mul_nonneg (hg u) (hg (u + ℓ))

theorem contactWeight_nonneg (k : ℕ) : 0 ≤ contactWeight k :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- **The shallow floor maps are selective.** In Weil's form the floor map of `k` contributes
`−2 (Λ(k)/√k) h(log k)`. If `log k` is at least half the length of the window, this contribution
is nonnegative on every packet with one node at the centre and nonpositive on every packet of
one sign: with the true weights the shallow trees lift the one-node states and deepen the
one-signed ones, and a negative weight, as for the Liouville twist, does the opposite. -/
theorem shallow_contact_selective {g₁ g₂ : ℝ → ℝ} {a b : ℝ} {k : ℕ}
    (hk : (b - a) / 2 ≤ Real.log k)
    (hsupp : ∀ u, u < a ∨ b < u → g₁ u = 0) (hleft : ∀ u, u ≤ (a + b) / 2 → 0 ≤ g₁ u)
    (hright : ∀ u, (a + b) / 2 ≤ u → g₁ u ≤ 0) (hg₂ : ∀ u, 0 ≤ g₂ u) :
    0 ≤ -(2 * (contactWeight k * packetAutocorr g₁ (Real.log k))) ∧
      -(2 * (contactWeight k * packetAutocorr g₂ (Real.log k))) ≤ 0 := by
  have h1 := packetAutocorr_nonpos_of_node hsupp hleft hright hk
  have h2 := packetAutocorr_nonneg_of_nonneg hg₂ (Real.log k)
  have hw := contactWeight_nonneg k
  constructor
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hw h1]
  · nlinarith [mul_nonneg hw h2]

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
