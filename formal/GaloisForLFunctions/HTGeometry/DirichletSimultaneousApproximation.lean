import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Fintype.Pi

/-!
# Dirichlet's simultaneous approximation theorem

For finitely many reals `α_i`, `i ∈ ι`, and `Q ≥ 1`, some integer `1 ≤ k ≤ Q^{|ι|}` puts every
`k α_i` within `1/Q` of an integer.  The `Q^{|ι|} + 1` multiples `j α`, `0 ≤ j ≤ Q^{|ι|}`, fall into
the `Q^{|ι|}` boxes `∏ [b_i/Q, (b_i + 1)/Q)` of the fractional parts, so two of them share a box and
their difference is the required `k`.

The phase form: for frequencies `γ_i` and a step `U > 0`, some `u = kU`, `1 ≤ k ≤ Q^{|ι|}`, has
`cos(γ_i u) ≥ 1 - 2π²/Q²` and `|sin(γ_i u)| ≤ 2π/Q` for every `i`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two nonnegative reals with the same natural floor differ by less than one. -/
theorem abs_sub_lt_one_of_natFloor_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ⌊x⌋₊ = ⌊y⌋₊) : |x - y| < 1 := by
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one x
  have h3 := Nat.floor_le hy
  have h4 := Nat.lt_floor_add_one y
  rw [h] at h1 h2
  rw [abs_lt]; constructor <;> linarith

/-- The box index of the fractional part of `x`, at resolution `1/Q`. -/
def fractBox (Q : ℕ) (hQ : 1 ≤ Q) (x : ℝ) : Fin Q :=
  ⟨⌊(Q : ℝ) * Int.fract x⌋₊, by
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hlt : (Q : ℝ) * Int.fract x < Q := by
      have := Int.fract_lt_one x
      nlinarith
    have h0 : 0 ≤ (Q : ℝ) * Int.fract x := mul_nonneg hQ0.le (Int.fract_nonneg x)
    exact (Nat.floor_lt h0).mpr (by exact_mod_cast hlt)⟩

/-- Equal boxes put the fractional parts within `1/Q`. -/
theorem abs_fract_sub_lt_of_fractBox_eq {Q : ℕ} (hQ : 1 ≤ Q) {x y : ℝ}
    (h : fractBox Q hQ x = fractBox Q hQ y) : |Int.fract x - Int.fract y| < 1 / Q := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hval : ⌊(Q : ℝ) * Int.fract x⌋₊ = ⌊(Q : ℝ) * Int.fract y⌋₊ := congrArg Fin.val h
  have h1 := abs_sub_lt_one_of_natFloor_eq (mul_nonneg hQ0.le (Int.fract_nonneg x))
    (mul_nonneg hQ0.le (Int.fract_nonneg y)) hval
  rw [← mul_sub, abs_mul, abs_of_pos hQ0] at h1
  rw [lt_div_iff₀ hQ0]
  linarith

/-- **Dirichlet's simultaneous approximation theorem.** -/
theorem exists_dirichlet_simultaneous {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Q ^ Fintype.card ι ∧ ∀ i, ∃ m : ℤ, |(k : ℝ) * α i - m| < 1 / Q := by
  classical
  set B : ℕ → ι → Fin Q := fun j i => fractBox Q hQ ((j : ℝ) * α i) with hB
  have hcard : (Finset.univ : Finset (ι → Fin Q)).card
      < (Finset.range (Q ^ Fintype.card ι + 1)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Finset.card_range]
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := B) (fun _ _ => Finset.mem_coe.mpr
      (Finset.mem_univ _))
  have hj₁' : j₁ ≤ Q ^ Fintype.card ι := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
  have hj₂' : j₂ ≤ Q ^ Fintype.card ι := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₂)
  -- the approximation for an ordered pair
  have key : ∀ a b : ℕ, a < b → b ≤ Q ^ Fintype.card ι → B a = B b →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ Q ^ Fintype.card ι ∧ ∀ i, ∃ m : ℤ, |(k : ℝ) * α i - m| < 1 / Q := by
    intro a b hab hb hBab
    refine ⟨b - a, by omega, by omega, fun i => ?_⟩
    have hbox : fractBox Q hQ ((a : ℝ) * α i) = fractBox Q hQ ((b : ℝ) * α i) :=
      congrFun hBab i
    have hfr := abs_fract_sub_lt_of_fractBox_eq hQ hbox
    refine ⟨⌊(b : ℝ) * α i⌋ - ⌊(a : ℝ) * α i⌋, ?_⟩
    have ha := Int.floor_add_fract ((a : ℝ) * α i)
    have hb' := Int.floor_add_fract ((b : ℝ) * α i)
    have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
      rw [Nat.cast_sub hab.le]
    rw [hcast]
    push_cast
    have heq2 : ((b : ℝ) - a) * α i - (⌊(b : ℝ) * α i⌋ - ⌊(a : ℝ) * α i⌋ : ℝ)
        = Int.fract ((b : ℝ) * α i) - Int.fract ((a : ℝ) * α i) := by
      linarith
    rw [heq2, abs_sub_comm]
    exact hfr
  rcases lt_or_gt_of_ne hne with h | h
  · exact key j₁ j₂ h hj₂' heq
  · exact key j₂ j₁ h hj₁' heq.symm

/-- **The phase form.**  For frequencies `γ_i` and a step `U`, some `u = kU`, `1 ≤ k ≤ Q^{|ι|}`,
has `cos(γ_i u) ≥ 1 - 2π²/Q²` and `|sin(γ_i u)| ≤ 2π/Q` for every `i`. -/
theorem exists_dirichlet_phase {ι : Type*} [Fintype ι] [DecidableEq ι] (γ : ι → ℝ) (U : ℝ)
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ Q ^ Fintype.card ι ∧ ∀ i,
      1 - 2 * Real.pi ^ 2 / (Q : ℝ) ^ 2 ≤ Real.cos (γ i * (k * U))
        ∧ |Real.sin (γ i * (k * U))| ≤ 2 * Real.pi / Q := by
  obtain ⟨k, hk1, hkQ, happ⟩ :=
    exists_dirichlet_simultaneous (fun i => γ i * U / (2 * Real.pi)) Q hQ
  refine ⟨k, hk1, hkQ, fun i => ?_⟩
  obtain ⟨m, hm⟩ := happ i
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hπ := Real.pi_pos
  set θ : ℝ := γ i * (k * U) - m * (2 * Real.pi) with hθ
  have hθb : |θ| ≤ 2 * Real.pi / Q := by
    have h1 : θ = 2 * Real.pi * ((k : ℝ) * (γ i * U / (2 * Real.pi)) - m) := by
      rw [hθ]; field_simp
    rw [h1, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h2 := mul_le_mul_of_nonneg_left hm.le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    calc 2 * Real.pi * |(k : ℝ) * (γ i * U / (2 * Real.pi)) - m| ≤ 2 * Real.pi * (1 / Q) := h2
      _ = 2 * Real.pi / Q := by ring
  have hshift : γ i * (k * U) = θ + m * (2 * Real.pi) := by rw [hθ]; ring
  have hcos : Real.cos (γ i * (k * U)) = Real.cos θ := by
    rw [hshift, Real.cos_add_int_mul_two_pi]
  have hsin : Real.sin (γ i * (k * U)) = Real.sin θ := by
    rw [hshift, Real.sin_add_int_mul_two_pi]
  refine ⟨?_, ?_⟩
  · rw [hcos]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 : θ ^ 2 ≤ (2 * Real.pi / Q) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg θ) hθb 2
    have h3 : (2 * Real.pi / Q) ^ 2 / 2 = 2 * Real.pi ^ 2 / (Q : ℝ) ^ 2 := by
      field_simp
    linarith
  · rw [hsin]
    exact le_trans Real.abs_sin_le_abs hθb

end

end GaloisForLFunctions.HTGeometry
