import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinEveryBaseThetaMass

/-!
# Proportional Chebyshev mass in every short window

The every-base detector-packing bound gives a fixed proportion of the width in prime logarithmic
mass for the single window `(z, z + z^α/2]`.  Chaining that window along

```text
z_0 = y ,     z_{i+1} = z_i + z_i^α / 2
```

and stopping at the last index still inside `(y, y + L]` upgrades it to *every* window of *every*
length: the telescoping sum of the individual masses is a fixed proportion of the total advance,
and the advance misses the right endpoint by at most one step.

The sub-window form is the short-interval prime supply that Andersson's Lemma 2 consumes: the mass
of `(x + a x^θ, x + b x^θ]` is at least `((b - a) - δ(x)) x^θ / 8192` with `δ(x) = 2 x^{α-θ} → 0`.
-/

noncomputable section

open Filter Topology

namespace RHTower.Sieve

/-- The chained detector bases starting at `y`. -/
def thetaChainSeq (α y : ℝ) : ℕ → ℝ
  | 0 => y
  | (n + 1) => thetaChainSeq α y n + (thetaChainSeq α y n) ^ α / 2

theorem thetaChainSeq_zero (α y : ℝ) : thetaChainSeq α y 0 = y := rfl

theorem thetaChainSeq_succ (α y : ℝ) (n : ℕ) :
    thetaChainSeq α y (n + 1) = thetaChainSeq α y n + (thetaChainSeq α y n) ^ α / 2 := rfl

theorem thetaChainSeq_ge {α y : ℝ} (hy : 0 < y) (n : ℕ) : y ≤ thetaChainSeq α y n := by
  induction n with
  | zero => exact le_of_eq (thetaChainSeq_zero α y).symm
  | succ n ih =>
      rw [thetaChainSeq_succ]
      have hz : (0:ℝ) < thetaChainSeq α y n := lt_of_lt_of_le hy ih
      have hpos : (0:ℝ) ≤ (thetaChainSeq α y n) ^ α / 2 := by positivity
      linarith

theorem thetaChainSeq_mono {α y : ℝ} (hy : 0 < y) (n : ℕ) :
    thetaChainSeq α y n ≤ thetaChainSeq α y (n + 1) := by
  rw [thetaChainSeq_succ]
  have hz : (0:ℝ) < thetaChainSeq α y n := lt_of_lt_of_le hy (thetaChainSeq_ge hy n)
  have hpos : (0:ℝ) ≤ (thetaChainSeq α y n) ^ α / 2 := by positivity
  linarith

theorem thetaChainSeq_lower_linear {α y : ℝ} (hy : 0 < y) (hα : 0 ≤ α) (n : ℕ) :
    y + (n : ℝ) * (y ^ α / 2) ≤ thetaChainSeq α y n := by
  induction n with
  | zero => simp [thetaChainSeq_zero]
  | succ n ih =>
      rw [thetaChainSeq_succ]
      have hpow : y ^ α ≤ (thetaChainSeq α y n) ^ α :=
        Real.rpow_le_rpow hy.le (thetaChainSeq_ge hy n) hα
      push_cast
      linarith

theorem thetaChainSeq_tendsto {α y : ℝ} (hy : 0 < y) (hα : 0 ≤ α) :
    Tendsto (thetaChainSeq α y) atTop atTop := by
  have hstep : (0:ℝ) < y ^ α / 2 := by positivity
  have hlin : Tendsto (fun n : ℕ => y + (n : ℝ) * (y ^ α / 2)) atTop atTop := by
    refine Filter.tendsto_atTop_add_const_left _ y ?_
    exact tendsto_natCast_atTop_atTop.atTop_mul_const hstep
  exact tendsto_atTop_mono (fun n => thetaChainSeq_lower_linear hy hα n) hlin

/-- **Proportional prime mass in every short window.**  Chaining the every-base detector windows. -/
theorem exists_theta_window_lower {α : ℝ}
    (halpha : (701299 / 1000000 : ℝ) < α) (halpha1 : α < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L - (y + L) ^ α) / 8192 ≤ Chebyshev.theta (y + L) - Chebyshev.theta y := by
  classical
  have hα0 : (0:ℝ) ≤ α := by linarith
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    (eventually_routeT_detectorPacking_theta_mass_every_base halpha halpha1)
  refine ⟨max X₀ 1, le_max_right _ _, ?_⟩
  intro y L hy hL
  have hy1 : (1:ℝ) ≤ y := le_trans (le_max_right X₀ 1) hy
  have hy0 : (0:ℝ) < y := by linarith
  have hyX : X₀ ≤ y := le_trans (le_max_left X₀ 1) hy
  -- the chained masses
  have hchain : ∀ n : ℕ,
      (thetaChainSeq α y n - y) / 8192
        ≤ Chebyshev.theta (thetaChainSeq α y n) - Chebyshev.theta y := by
    intro n
    induction n with
    | zero => simp [thetaChainSeq_zero]
    | succ n ih =>
        have hzy : y ≤ thetaChainSeq α y n := thetaChainSeq_ge hy0 n
        have hzX : X₀ ≤ thetaChainSeq α y n := le_trans hyX hzy
        have hstep := hX₀ (thetaChainSeq α y n) hzX
        have heq : thetaChainSeq α y (n + 1)
            = thetaChainSeq α y n + (thetaChainSeq α y n) ^ α / 2 := thetaChainSeq_succ α y n
        rw [heq]
        have hnum : (thetaChainSeq α y n ^ α / 2) / 8192 = thetaChainSeq α y n ^ α / 16384 := by
          ring
        linarith [hstep, ih]
  -- the stopping index
  have hex : ∃ n : ℕ, y + L < thetaChainSeq α y n :=
    ((thetaChainSeq_tendsto hy0 hα0).eventually_gt_atTop (y + L)).exists
  set N := Nat.find hex with hNdef
  have hNspec : y + L < thetaChainSeq α y N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro h
    rw [h, thetaChainSeq_zero] at hNspec
    linarith
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hMle : thetaChainSeq α y M ≤ y + L := by
    by_contra hcon
    have hlt : y + L < thetaChainSeq α y M := lt_of_not_ge hcon
    exact absurd hlt (Nat.find_min hex (by omega))
  have hstepM : thetaChainSeq α y N
      = thetaChainSeq α y M + (thetaChainSeq α y M) ^ α / 2 := by
    rw [hM]
    exact thetaChainSeq_succ α y M
  have hpowM : (thetaChainSeq α y M) ^ α ≤ (y + L) ^ α :=
    Real.rpow_le_rpow (by linarith [thetaChainSeq_ge hy0 (α := α) M]) hMle hα0
  have hMlow : y + L - (y + L) ^ α / 2 ≤ thetaChainSeq α y M := by
    have := hNspec
    rw [hstepM] at this
    linarith
  have hmono : Chebyshev.theta (thetaChainSeq α y M) ≤ Chebyshev.theta (y + L) :=
    Chebyshev.theta_mono hMle
  have hpow0 : (0:ℝ) ≤ (y + L) ^ α := Real.rpow_nonneg (by linarith) α
  have := hchain M
  linarith

/-- **Andersson's Lemma 2, in Chebyshev-mass form.**  Every sub-window
`(x + a x^θ, x + b x^θ]` of a short window carries prime logarithmic mass at least a fixed
proportion of its width, up to the vanishing slack `δ(x) = 2 x^{α-θ}`. -/
theorem exists_theta_subwindow_lower {α θ : ℝ}
    (halpha : (701299 / 1000000 : ℝ) < α) (hαθ : α < θ) (hθ1 : θ < 1) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      ((b - a) - 2 * x ^ (α - θ)) * x ^ θ / 8192
        ≤ Chebyshev.theta (x + b * x ^ θ) - Chebyshev.theta (x + a * x ^ θ) := by
  have halpha1 : α < 1 := lt_trans hαθ hθ1
  have hα0 : (0:ℝ) < α := by linarith
  have hθ0 : (0:ℝ) < θ := by linarith
  obtain ⟨X, hX1, hXspec⟩ := exists_theta_window_lower halpha halpha1
  refine ⟨X, hX1, ?_⟩
  intro x hx a b ha hab hb
  have hx1 : (1:ℝ) ≤ x := le_trans hX1 hx
  have hx0 : (0:ℝ) < x := by linarith
  have hxθ : x ^ θ ≤ x := by
    calc x ^ θ ≤ x ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hθ1)
      _ = x := Real.rpow_one x
  have hxθ0 : (0:ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hy : X ≤ x + a * x ^ θ := by
    have : (0:ℝ) ≤ a * x ^ θ := mul_nonneg ha hxθ0.le
    linarith
  have hL : (0:ℝ) ≤ (b - a) * x ^ θ := mul_nonneg (by linarith) hxθ0.le
  have hsum : x + a * x ^ θ + (b - a) * x ^ θ = x + b * x ^ θ := by ring
  have hmain := hXspec (x + a * x ^ θ) ((b - a) * x ^ θ) hy hL
  rw [hsum] at hmain
  refine le_trans ?_ hmain
  have hupper : x + b * x ^ θ ≤ 2 * x := by
    have hbx : b * x ^ θ ≤ x ^ θ := by
      nlinarith [hxθ0.le]
    linarith
  have hpow : (x + b * x ^ θ) ^ α ≤ (2 * x) ^ α := by
    refine Real.rpow_le_rpow ?_ hupper hα0.le
    have : (0:ℝ) ≤ b * x ^ θ := mul_nonneg (le_trans ha hab) hxθ0.le
    linarith
  have h2 : (2 * x) ^ α = (2:ℝ) ^ α * x ^ α := Real.mul_rpow (by norm_num) hx0.le
  have h2α : (2:ℝ) ^ α ≤ 2 := by
    calc (2:ℝ) ^ α ≤ (2:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt halpha1)
      _ = 2 := Real.rpow_one 2
  have hxsplit : x ^ α = x ^ (α - θ) * x ^ θ := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hxα0 : (0:ℝ) < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hchain : (x + b * x ^ θ) ^ α ≤ 2 * (x ^ (α - θ) * x ^ θ) := by
    calc (x + b * x ^ θ) ^ α ≤ (2 * x) ^ α := hpow
      _ = (2:ℝ) ^ α * x ^ α := h2
      _ ≤ 2 * x ^ α := by nlinarith [hxα0.le]
      _ = 2 * (x ^ (α - θ) * x ^ θ) := by rw [hxsplit]
  have hnum : ((b - a) - 2 * x ^ (α - θ)) * x ^ θ
      ≤ (b - a) * x ^ θ - (x + b * x ^ θ) ^ α := by
    have : ((b - a) - 2 * x ^ (α - θ)) * x ^ θ
        = (b - a) * x ^ θ - 2 * (x ^ (α - θ) * x ^ θ) := by ring
    rw [this]
    linarith
  exact div_le_div_of_nonneg_right hnum (by norm_num) |>.trans (le_refl _)

end RHTower.Sieve

end
