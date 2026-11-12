import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheMatrixOfAStepPacketIsTheMixedDifferenceOfItsWindows

/-!
# The step packets of a window form a tower under refinement

Weil's form `𝔚_Q` of a packet depends on the packet through its autocorrelation and the product
of its two degrees, so it is invariant under translation (`packetForm_translate`). Translation
by `log m` carries the window `(R, R + J]` to `(mR, mR + mJ]` and the step packet with the values
`σ_j` on the unit blocks above `R` to the step packet with the values `σ_j/√m` on each of the
`m` unit blocks above `mR` that subdivide the block `j` (`stepPacket_translate`). Hence:

* `𝔚_Q(step packet of σ above R) = 𝔚_Q(step packet of the refinement of σ above mR)`
  (`packetForm_stepPacket_refine`), and the refinement keeps `Σ σ_j²` (`sum_refineStep_sq`);
* the block matrix above `R` is the compression of the block matrix above `mR` by the isometry
  of refinement (`sum_blockMatrix_refine`);
* a margin of `𝔚_Q` on the `mJ` blocks above `mR` is a margin on the `J` blocks above `R`
  (`margin_of_refined_margin`).

So for a fixed window ratio the margins of the block matrices decrease along divisibility of the
scale `R`, and the matrices on unit blocks above `R = 1` are the first members of the tower.
-/

open Finset MeasureTheory

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Weil's form is invariant under translation -/

/-- The first degree of a translate. -/
theorem integral_translate_mul_exp_neg (g : ℝ → ℝ) (τ : ℝ) :
    ∫ u, g (u - τ) * Real.exp (-u / 2) =
      Real.exp (-τ / 2) * ∫ u, g u * Real.exp (-u / 2) := by
  have h : ∫ u, g (u - τ) * Real.exp (-(u - τ + τ) / 2) =
      ∫ v, g v * Real.exp (-(v + τ) / 2) :=
    integral_sub_right_eq_self (fun v => g v * Real.exp (-(v + τ) / 2)) τ
  have h1 : (fun u => g (u - τ) * Real.exp (-u / 2)) =
      fun u => g (u - τ) * Real.exp (-(u - τ + τ) / 2) := by
    funext u
    rw [sub_add_cancel]
  have h2 : (fun v => g v * Real.exp (-(v + τ) / 2)) =
      fun v => Real.exp (-τ / 2) * (g v * Real.exp (-v / 2)) := by
    funext v
    rw [show -(v + τ) / 2 = -τ / 2 + -v / 2 by ring, Real.exp_add]
    ring
  rw [h1, h, h2, integral_const_mul]

/-- The second degree of a translate. -/
theorem integral_translate_mul_exp_pos (g : ℝ → ℝ) (τ : ℝ) :
    ∫ u, g (u - τ) * Real.exp (u / 2) = Real.exp (τ / 2) * ∫ u, g u * Real.exp (u / 2) := by
  have h : ∫ u, g (u - τ) * Real.exp ((u - τ + τ) / 2) = ∫ v, g v * Real.exp ((v + τ) / 2) :=
    integral_sub_right_eq_self (fun v => g v * Real.exp ((v + τ) / 2)) τ
  have h1 : (fun u => g (u - τ) * Real.exp (u / 2)) =
      fun u => g (u - τ) * Real.exp ((u - τ + τ) / 2) := by
    funext u
    rw [sub_add_cancel]
  have h2 : (fun v => g v * Real.exp ((v + τ) / 2)) =
      fun v => Real.exp (τ / 2) * (g v * Real.exp (v / 2)) := by
    funext v
    rw [show (v + τ) / 2 = τ / 2 + v / 2 by ring, Real.exp_add]
    ring
  rw [h1, h, h2, integral_const_mul]

/-- **Weil's form of a packet is invariant under translation**: the two degrees pick up
reciprocal factors and the autocorrelation does not change. -/
theorem packetForm_translate (Q : ℕ) (g : ℝ → ℝ) (τ : ℝ) :
    packetForm Q (fun u => g (u - τ)) = packetForm Q g := by
  have he : Real.exp (-τ / 2) * Real.exp (τ / 2) = 1 := by
    rw [← Real.exp_add, show -τ / 2 + τ / 2 = 0 by ring, Real.exp_zero]
  unfold packetForm
  simp only [packetAutocorr_translate, levyJump_translate]
  rw [integral_translate_mul_exp_neg, integral_translate_mul_exp_pos]
  generalize (∫ u, g u * Real.exp (-u / 2)) = A
  generalize (∫ u, g u * Real.exp (u / 2)) = B
  linear_combination (2 * A * B) * he

/-! ### Translation refines a step packet -/

/-- A flat packet translated by `log m` is the flat packet of the dilated window, divided by
`√m`. -/
theorem flatPacket_translate {a b m : ℝ} (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) (u : ℝ) :
    flatPacket a b (u - Real.log m) = flatPacket (m * a) (m * b) u / Real.sqrt m := by
  have hexp : Real.exp ((u - Real.log m) / 2) = Real.exp (u / 2) / Real.sqrt m := by
    rw [sub_div, Real.exp_sub, Real.exp_half (Real.log m), Real.exp_log hm]
  simp only [flatPacket, Set.indicator_apply, Set.mem_Ioc, Real.log_mul hm.ne' ha.ne',
    Real.log_mul hm.ne' hb.ne']
  by_cases h : Real.log a < u - Real.log m ∧ u - Real.log m ≤ Real.log b
  · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩, hexp]
  · rw [if_neg h, if_neg fun h' => h ⟨by linarith [h'.1], by linarith [h'.2]⟩, zero_div]

/-- Adjacent unit blocks add up to a window. -/
theorem sum_flatPacket_blocks {c : ℕ} (hc : 1 ≤ c) (m : ℕ) (u : ℝ) :
    ∑ i ∈ range m, flatPacket ((c + i : ℕ) : ℝ) ((c + (i + 1) : ℕ) : ℝ) u =
      flatPacket (c : ℝ) ((c + m : ℕ) : ℝ) u := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have h : ∀ i, flatPacket ((c + i : ℕ) : ℝ) ((c + (i + 1) : ℕ) : ℝ) u =
      flatPacket (c : ℝ) ((c + (i + 1) : ℕ) : ℝ) u - flatPacket (c : ℝ) ((c + i : ℕ) : ℝ) u :=
    fun i => (flatPacket_sub_flatPacket hc' (by exact_mod_cast Nat.le_add_right c i)
      (by exact_mod_cast Nat.add_le_add_left (Nat.le_succ i) c) u).symm
  rw [Finset.sum_congr rfl fun i _ => h i,
    Finset.sum_range_sub (fun i => flatPacket (c : ℝ) ((c + i : ℕ) : ℝ) u), Nat.add_zero,
    flatPacket_self, sub_zero]

/-- A sum over `mJ` consecutive indices, by blocks of `m`. -/
theorem sum_range_mul_eq (m J : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range (m * J), f i = ∑ j ∈ range J, ∑ i ∈ range m, f (m * j + i) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- The refinement of a step function: each block is split into `m` blocks and the value is
divided by `√m`. -/
def refineStep (m : ℕ) (σ : ℕ → ℝ) (i : ℕ) : ℝ := σ (i / m) / Real.sqrt m

theorem refineStep_mul_add {m : ℕ} (hm : 1 ≤ m) (σ : ℕ → ℝ) (j : ℕ) {i : ℕ} (hi : i < m) :
    refineStep m σ (m * j + i) = σ j / Real.sqrt m := by
  rw [refineStep, Nat.mul_add_div (by omega : 0 < m), Nat.div_eq_of_lt hi, add_zero]

/-- The refinement keeps the mass. -/
theorem sum_refineStep_sq {m : ℕ} (hm : 1 ≤ m) (J : ℕ) (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), refineStep m σ i ^ 2 = ∑ j ∈ range J, σ j ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [sum_range_mul_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∀ i ∈ range m, refineStep m σ (m * j + i) ^ 2 = σ j ^ 2 / m := fun i hi => by
    rw [refineStep_mul_add hm σ j (Finset.mem_range.mp hi), div_pow, Real.sq_sqrt hm'.le]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- **Translation by `log m` refines a step packet.** -/
theorem stepPacket_translate {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (J : ℕ) (σ : ℕ → ℝ)
    (u : ℝ) :
    stepPacket R J σ (u - Real.log m) = stepPacket (m * R) (m * J) (refineStep m σ) u := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [stepPacket, stepPacket, sum_range_mul_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : 1 ≤ m * R + m * j := by
    have := Nat.mul_le_mul hm hR
    omega
  have c1 : ((m * R + m * j : ℕ) : ℝ) = (m : ℝ) * ((R + j : ℕ) : ℝ) := by
    push_cast
    ring
  have c2 : ((m * R + m * j + m : ℕ) : ℝ) = (m : ℝ) * ((R + (j + 1) : ℕ) : ℝ) := by
    push_cast
    ring
  have hterm : ∀ i ∈ range m,
      refineStep m σ (m * j + i) * flatPacket ((m * R + (m * j + i) : ℕ) : ℝ)
          ((m * R + (m * j + i + 1) : ℕ) : ℝ) u =
        σ j / Real.sqrt m * flatPacket ((m * R + m * j + i : ℕ) : ℝ)
          ((m * R + m * j + (i + 1) : ℕ) : ℝ) u := fun i hi => by
    rw [refineStep_mul_add hm σ j (Finset.mem_range.mp hi),
      show m * R + (m * j + i) = m * R + m * j + i by ring,
      show m * R + (m * j + i + 1) = m * R + m * j + (i + 1) by ring]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_flatPacket_blocks hc m u, c1, c2,
    flatPacket_translate (Nat.cast_pos.mpr (by omega)) (Nat.cast_pos.mpr (by omega)) hm']
  ring

/-! ### The tower -/

/-- **Weil's form of a step packet is that of its refinement.** -/
theorem packetForm_stepPacket_refine {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (Q J : ℕ)
    (σ : ℕ → ℝ) :
    packetForm Q (stepPacket (m * R) (m * J) (refineStep m σ)) =
      packetForm Q (stepPacket R J σ) := by
  have h : stepPacket (m * R) (m * J) (refineStep m σ) =
      fun u => stepPacket R J σ (u - Real.log m) := by
    funext u
    exact (stepPacket_translate hR hm J σ u).symm
  rw [h, packetForm_translate]

/-- **The block matrix above `R` is the compression of the block matrix above `mR`** by the
refinement. -/
theorem sum_blockMatrix_refine {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (Q J : ℕ)
    (σ : ℕ → ℝ) :
    ∑ i ∈ range (m * J), ∑ l ∈ range (m * J),
        refineStep m σ i * refineStep m σ l * blockMatrix Q (m * R + i) (m * R + l) =
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  have hmR : 1 ≤ m * R := by
    have := Nat.mul_le_mul hm hR
    omega
  rw [← packetForm_stepPacket_eq_sum_blockMatrix hmR, ← packetForm_stepPacket_eq_sum_blockMatrix hR,
    packetForm_stepPacket_refine hR hm]

/-- **A margin on finer blocks is a margin on coarser blocks.** -/
theorem margin_of_refined_margin {R : ℕ} (hR : 1 ≤ R) {m : ℕ} (hm : 1 ≤ m) (Q J : ℕ) {μ : ℝ}
    (h : ∀ σ : ℕ → ℝ, μ * ∑ i ∈ range (m * J), σ i ^ 2 ≤
      packetForm Q (stepPacket (m * R) (m * J) σ)) (σ : ℕ → ℝ) :
    μ * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ) := by
  have h1 := h (refineStep m σ)
  rwa [sum_refineStep_sq hm, packetForm_stepPacket_refine hR hm] at h1

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
