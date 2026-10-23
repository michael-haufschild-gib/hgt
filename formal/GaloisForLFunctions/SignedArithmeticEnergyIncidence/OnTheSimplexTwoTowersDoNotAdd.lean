import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TowerGridCapacitiesAdd

/-!
# On the simplex two towers do not add

A two-tower train carried by the smooth numbers `p^j q^k` with `j + k ≤ n` has its amplitudes on
the simplex `S_n = {(j, k) : j + k ≤ n}` of the exponent lattice, not on a box.  For equal prime
weights its joint first-power charge obeys

`row + column ≤ (cos θ + cos 2θ) · mass`,   `θ = π/(n+3)`   (`simplex_joint_capacity`),

with equality for the simplex gauge (`simplex_joint_capacity_attained`) and no smaller constant
(`simplex_joint_capacity_sharp`).  Each tower alone keeps the full capacity `cos(π/(n+2))` on
`S_n` (`simplex_row_capacity_attained`): the longest row of the simplex is that of the box.  For
`n ≥ 1` the joint capacity is strictly below the sum `2 cos(π/(n+2))` of the single capacities
(`simplex_capacities_do_not_add`): the hyperbola of the smooth numbers forces a cross-prime
saving, `2 − cos θ − cos 2θ ≈ 5π²/(2n²)` against the box deficit `π²/n²`.  On a box the
capacities add exactly (`grid_joint_capacity_attained`), so the saving is a property of the
support alone.

The extremal is `ψ(j, k) = sin x sin y (cos x + cos y)`, `x = (j+1)θ`, `y = (k+1)θ`: the
antisymmetrization of the box sine `sin x sin 2y` across the cut `j + k = n + 1`.  It is positive on
`S_n` (`simplexGauge_pos`), vanishes on the cut (`simplexGauge_cut`) and on the axes, and its four
neighbours sum to `2(cos θ + cos 2θ) ψ` (`simplexPsi_neighbours`).  The capacity follows from the
ground-state inequality `2 f_a f_b ≤ (ψ_b/ψ_a) f_a² + (ψ_a/ψ_b) f_b²` on every edge.
-/

open Finset Real

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### The simplex gauge -/

/-- The simplex angle `θ = π/(n+3)`. -/
def simplexAngle (n : ℕ) : ℝ := π / ((n : ℝ) + 3)

/-- `Ψ(x, y) = sin x sin y (cos x + cos y)`. -/
def simplexPsi (x y : ℝ) : ℝ := Real.sin x * Real.sin y * (Real.cos x + Real.cos y)

/-- The simplex gauge `ψ(j, k) = Ψ((j+1)θ, (k+1)θ)`. -/
def simplexGauge (n j k : ℕ) : ℝ :=
  simplexPsi (((j : ℝ) + 1) * simplexAngle n) (((k : ℝ) + 1) * simplexAngle n)

/-- **The four-neighbour law**: `Ψ(x−t,y) + Ψ(x+t,y) + Ψ(x,y−t) + Ψ(x,y+t) = 2(cos t + cos 2t) Ψ(x,y)`. -/
theorem simplexPsi_neighbours (x y t : ℝ) :
    simplexPsi (x - t) y + simplexPsi (x + t) y + simplexPsi x (y - t) + simplexPsi x (y + t) =
      2 * (Real.cos t + Real.cos (2 * t)) * simplexPsi x y := by
  unfold simplexPsi
  simp only [Real.sin_sub, Real.sin_add, Real.cos_sub, Real.cos_add, Real.cos_two_mul]
  linear_combination (-2 * Real.sin x * Real.sin y * (Real.cos x + Real.cos y)) *
    Real.sin_sq_add_cos_sq t

theorem simplexPsi_zero_left (y : ℝ) : simplexPsi 0 y = 0 := by simp [simplexPsi]

theorem simplexPsi_zero_right (x : ℝ) : simplexPsi x 0 = 0 := by simp [simplexPsi]

theorem simplexAngle_pos (n : ℕ) : 0 < simplexAngle n := by
  unfold simplexAngle; positivity

theorem simplexAngle_mul (n : ℕ) : ((n : ℝ) + 3) * simplexAngle n = π := by
  unfold simplexAngle; exact mul_div_cancel₀ π (by positivity)

/-- `Ψ(x, y) > 0` for `x, y > 0`, `x + y < π`. -/
theorem simplexPsi_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y < π) :
    0 < simplexPsi x y := by
  unfold simplexPsi
  have hsx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith)
  have hsy : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy (by linarith)
  have hc : Real.cos (π - x) < Real.cos y :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hy.le (by linarith) (by linarith)
  rw [Real.cos_pi_sub] at hc
  have : 0 < Real.cos x + Real.cos y := by linarith
  exact mul_pos (mul_pos hsx hsy) this

/-- `Ψ(x, π − x) = 0`. -/
theorem simplexPsi_cut (x : ℝ) : simplexPsi x (π - x) = 0 := by
  simp [simplexPsi, Real.cos_pi_sub]

/-- **Positivity on the simplex**: `ψ(j, k) > 0` for `j + k ≤ n`. -/
theorem simplexGauge_pos {n j k : ℕ} (h : j + k ≤ n) : 0 < simplexGauge n j k := by
  have hθ := simplexAngle_pos n
  have hmul := simplexAngle_mul n
  have hjk : ((j : ℝ) + 1) + ((k : ℝ) + 1) ≤ (n : ℝ) + 2 := by
    have : ((j + k : ℕ) : ℝ) ≤ n := by exact_mod_cast h
    push_cast at this; linarith
  unfold simplexGauge
  refine simplexPsi_pos (mul_pos (by positivity) hθ) (mul_pos (by positivity) hθ) ?_
  have : (((j : ℝ) + 1) + ((k : ℝ) + 1)) * simplexAngle n < ((n : ℝ) + 3) * simplexAngle n :=
    mul_lt_mul_of_pos_right (by linarith) hθ
  linarith

/-- **The gauge vanishes on the cut** `j + k = n + 1`. -/
theorem simplexGauge_cut {n j k : ℕ} (h : j + k = n + 1) : simplexGauge n j k = 0 := by
  have hmul := simplexAngle_mul n
  have hjk : ((j : ℝ) + 1) + ((k : ℝ) + 1) = (n : ℝ) + 3 := by
    have : ((j + k : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  unfold simplexGauge
  have hy : ((k : ℝ) + 1) * simplexAngle n = π - ((j : ℝ) + 1) * simplexAngle n := by
    rw [← hmul, ← hjk]; ring
  rw [hy, simplexPsi_cut]

/-- **The vertex law**: on the simplex the four neighbours of `ψ` sum to `2(cos θ + cos 2θ) ψ`,
with the left and lower neighbours read through `Ψ` (they vanish on the axes). -/
theorem simplexGauge_vertex (n j k : ℕ) :
    simplexGauge n (j + 1) k + simplexPsi ((j : ℝ) * simplexAngle n) (((k : ℝ) + 1) * simplexAngle n) +
        (simplexGauge n j (k + 1) +
          simplexPsi (((j : ℝ) + 1) * simplexAngle n) ((k : ℝ) * simplexAngle n)) =
      2 * (Real.cos (simplexAngle n) + Real.cos (2 * simplexAngle n)) * simplexGauge n j k := by
  have h := simplexPsi_neighbours (((j : ℝ) + 1) * simplexAngle n)
    (((k : ℝ) + 1) * simplexAngle n) (simplexAngle n)
  unfold simplexGauge
  have e1 : ((j : ℝ) + 1) * simplexAngle n - simplexAngle n = (j : ℝ) * simplexAngle n := by ring
  have e2 : ((k : ℝ) + 1) * simplexAngle n - simplexAngle n = (k : ℝ) * simplexAngle n := by ring
  have e3 : (((j + 1 : ℕ) : ℝ) + 1) * simplexAngle n =
      ((j : ℝ) + 1) * simplexAngle n + simplexAngle n := by push_cast; ring
  have e4 : (((k + 1 : ℕ) : ℝ) + 1) * simplexAngle n =
      ((k : ℝ) + 1) * simplexAngle n + simplexAngle n := by push_cast; ring
  rw [e1, e2] at h
  rw [e3, e4]
  linarith

/-! ### The edge inequality and the regrouping -/

/-- **Edge inequality**: `2xy ≤ (b/a) x² + (a/b) y²` when `a, b > 0`, or when `y = 0` and either
`b = 0` or `x = 0`. -/
theorem two_mul_le_ratio {a b x y : ℝ} (h : (0 < a ∧ 0 < b) ∨ (y = 0 ∧ (b = 0 ∨ x = 0))) :
    2 * x * y ≤ b / a * x ^ 2 + a / b * y ^ 2 := by
  rcases h with ⟨ha, hb⟩ | ⟨hy, hb | hx⟩
  · have ha' := ha.ne'
    have hb' := hb.ne'
    have e : b / a * x ^ 2 + a / b * y ^ 2 - 2 * x * y = (b * x - a * y) ^ 2 / (a * b) := by
      first | (field_simp; ring) | field_simp
    have : 0 ≤ (b * x - a * y) ^ 2 / (a * b) := div_nonneg (sq_nonneg _) (mul_pos ha hb).le
    linarith
  · subst hy hb; simp
  · subst hy hx; simp

/-- Equality in the edge inequality on the gauge itself. -/
theorem two_mul_eq_ratio {a b x y : ℝ}
    (h : (0 < a ∧ 0 < b ∧ x = a ∧ y = b) ∨ (y = 0 ∧ (b = 0 ∨ x = 0))) :
    2 * x * y = b / a * x ^ 2 + a / b * y ^ 2 := by
  rcases h with ⟨ha, hb, rfl, rfl⟩ | ⟨hy, hb | hx⟩
  · have ha' := ha.ne'
    have hb' := hb.ne'
    first | (field_simp; ring) | field_simp
  · subst hy hb; simp
  · subst hy hx; simp

/-- **Regrouping a chain**: the edge terms of a chain are vertex terms with the two neighbour
ratios, once the boundary terms vanish. -/
theorem chain_regroup (n : ℕ) (f u uL : ℕ → ℝ) (hL : ∀ j, uL (j + 1) = u j) (hL0 : uL 0 = 0)
    (hend : u (n + 1) / u n * f n ^ 2 = 0) :
    ∑ j ∈ range n, (u (j + 1) / u j * f j ^ 2 + u j / u (j + 1) * f (j + 1) ^ 2) =
      ∑ j ∈ range (n + 1), f j ^ 2 * ((u (j + 1) + uL j) / u j) := by
  rw [sum_add_distrib]
  have h1 : ∑ j ∈ range n, u (j + 1) / u j * f j ^ 2 =
      ∑ j ∈ range (n + 1), u (j + 1) / u j * f j ^ 2 := by
    rw [sum_range_succ, hend, add_zero]
  have h2 : ∑ j ∈ range n, u j / u (j + 1) * f (j + 1) ^ 2 =
      ∑ j ∈ range (n + 1), uL j / u j * f j ^ 2 := by
    rw [sum_range_succ', hL0, zero_div, zero_mul, add_zero]
    exact sum_congr rfl fun j _ => by rw [hL]
  rw [h1, h2, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- `λ_n = 2(cos θ + cos 2θ)`. -/
def simplexEigenvalue (n : ℕ) : ℝ :=
  2 * (Real.cos (simplexAngle n) + Real.cos (2 * simplexAngle n))

/-- The edge terms of the box charges. -/
def simplexEdgeTerms (n : ℕ) (f : ℕ → ℕ → ℝ) : ℝ :=
  (∑ k ∈ range (n + 1), ∑ j ∈ range n,
      (simplexGauge n (j + 1) k / simplexGauge n j k * f j k ^ 2 +
        simplexGauge n j k / simplexGauge n (j + 1) k * f (j + 1) k ^ 2)) +
    ∑ j ∈ range (n + 1), ∑ k ∈ range n,
      (simplexGauge n j (k + 1) / simplexGauge n j k * f j k ^ 2 +
        simplexGauge n j k / simplexGauge n j (k + 1) * f j (k + 1) ^ 2)

/-- **The regrouped edge terms**: for amplitudes supported on the simplex the edge terms are
`λ_n` times the mass. -/
theorem simplexEdgeTerms_eq (n : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ j k, n < j + k → f j k = 0) :
    simplexEdgeTerms n f = simplexEigenvalue n * gridMass n n f := by
  have hrow : ∀ k ∈ range (n + 1), ∑ j ∈ range n,
      (simplexGauge n (j + 1) k / simplexGauge n j k * f j k ^ 2 +
        simplexGauge n j k / simplexGauge n (j + 1) k * f (j + 1) k ^ 2) =
      ∑ j ∈ range (n + 1), f j k ^ 2 * ((simplexGauge n (j + 1) k +
        simplexPsi ((j : ℝ) * simplexAngle n) (((k : ℝ) + 1) * simplexAngle n)) /
          simplexGauge n j k) := by
    intro k _
    have hL : ∀ j, simplexPsi (((j + 1 : ℕ) : ℝ) * simplexAngle n)
        (((k : ℝ) + 1) * simplexAngle n) = simplexGauge n j k := by
      intro j; simp only [simplexGauge, Nat.cast_succ]
    have hL0 : simplexPsi (((0 : ℕ) : ℝ) * simplexAngle n) (((k : ℝ) + 1) * simplexAngle n) = 0 := by
      simp only [Nat.cast_zero, zero_mul, simplexPsi_zero_left]
    have hend : simplexGauge n (n + 1) k / simplexGauge n n k * f n k ^ 2 = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [simplexGauge_cut (by omega), zero_div, zero_mul]
      · rw [hf n k (by omega)]; ring
    exact chain_regroup n (fun j => f j k) (fun j => simplexGauge n j k)
      (fun j => simplexPsi ((j : ℝ) * simplexAngle n) (((k : ℝ) + 1) * simplexAngle n)) hL hL0 hend
  have hcol : ∀ j ∈ range (n + 1), ∑ k ∈ range n,
      (simplexGauge n j (k + 1) / simplexGauge n j k * f j k ^ 2 +
        simplexGauge n j k / simplexGauge n j (k + 1) * f j (k + 1) ^ 2) =
      ∑ k ∈ range (n + 1), f j k ^ 2 * ((simplexGauge n j (k + 1) +
        simplexPsi (((j : ℝ) + 1) * simplexAngle n) ((k : ℝ) * simplexAngle n)) /
          simplexGauge n j k) := by
    intro j _
    have hL : ∀ k, simplexPsi (((j : ℝ) + 1) * simplexAngle n)
        (((k + 1 : ℕ) : ℝ) * simplexAngle n) = simplexGauge n j k := by
      intro k; simp only [simplexGauge, Nat.cast_succ]
    have hL0 : simplexPsi (((j : ℝ) + 1) * simplexAngle n) (((0 : ℕ) : ℝ) * simplexAngle n) = 0 := by
      simp only [Nat.cast_zero, zero_mul, simplexPsi_zero_right]
    have hend : simplexGauge n j (n + 1) / simplexGauge n j n * f j n ^ 2 = 0 := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [simplexGauge_cut (by omega), zero_div, zero_mul]
      · rw [hf j n (by omega)]; ring
    exact chain_regroup n (fun k => f j k) (fun k => simplexGauge n j k)
      (fun k => simplexPsi (((j : ℝ) + 1) * simplexAngle n) ((k : ℝ) * simplexAngle n)) hL hL0 hend
  unfold simplexEdgeTerms gridMass
  rw [sum_congr rfl hrow, sum_congr rfl hcol, sum_comm, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  by_cases hjk : j + k ≤ n
  · have hpos := simplexGauge_pos hjk
    have hv := simplexGauge_vertex n j k
    rw [← mul_add, ← add_div]
    rw [show simplexGauge n (j + 1) k +
          simplexPsi ((j : ℝ) * simplexAngle n) (((k : ℝ) + 1) * simplexAngle n) +
        (simplexGauge n j (k + 1) +
          simplexPsi (((j : ℝ) + 1) * simplexAngle n) ((k : ℝ) * simplexAngle n)) =
        simplexEigenvalue n * simplexGauge n j k by rw [hv]; rfl]
    rw [mul_div_assoc, div_self hpos.ne', mul_one, mul_comm]
  · rw [hf j k (by omega)]; ring

/-! ### The joint capacity on the simplex -/

/-- **The joint capacity on the simplex**: for amplitudes on `S_n`,
`row + column ≤ (cos θ + cos 2θ) · mass`, `θ = π/(n+3)`. -/
theorem simplex_joint_capacity (n : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ j k, n < j + k → f j k = 0) :
    gridRowCharge n n f + gridColCharge n n f ≤
      (Real.cos (simplexAngle n) + Real.cos (2 * simplexAngle n)) * gridMass n n f := by
  have hE := simplexEdgeTerms_eq n f hf
  have hrow : 2 * gridRowCharge n n f ≤ ∑ k ∈ range (n + 1), ∑ j ∈ range n,
      (simplexGauge n (j + 1) k / simplexGauge n j k * f j k ^ 2 +
        simplexGauge n j k / simplexGauge n (j + 1) k * f (j + 1) k ^ 2) := by
    unfold gridRowCharge
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    have hk' := mem_range.mp hk
    have hj' := mem_range.mp hj
    rw [← mul_assoc]
    refine two_mul_le_ratio ?_
    by_cases h : j + 1 + k ≤ n
    · exact Or.inl ⟨simplexGauge_pos (by omega), simplexGauge_pos h⟩
    · refine Or.inr ⟨hf _ _ (by omega), ?_⟩
      by_cases h' : j + k = n
      · exact Or.inl (simplexGauge_cut (by omega))
      · exact Or.inr (hf _ _ (by omega))
  have hcol : 2 * gridColCharge n n f ≤ ∑ j ∈ range (n + 1), ∑ k ∈ range n,
      (simplexGauge n j (k + 1) / simplexGauge n j k * f j k ^ 2 +
        simplexGauge n j k / simplexGauge n j (k + 1) * f j (k + 1) ^ 2) := by
    unfold gridColCharge
    rw [mul_sum]
    refine sum_le_sum fun j hj => ?_
    rw [mul_sum]
    refine sum_le_sum fun k hk => ?_
    have hj' := mem_range.mp hj
    have hk' := mem_range.mp hk
    rw [← mul_assoc]
    refine two_mul_le_ratio ?_
    by_cases h : j + (k + 1) ≤ n
    · exact Or.inl ⟨simplexGauge_pos (by omega), simplexGauge_pos h⟩
    · refine Or.inr ⟨hf _ _ (by omega), ?_⟩
      by_cases h' : j + k = n
      · exact Or.inl (simplexGauge_cut (by omega))
      · exact Or.inr (hf _ _ (by omega))
  unfold simplexEdgeTerms simplexEigenvalue at hE
  linarith

/-- The simplex amplitude: the gauge on `S_n`, zero off it. -/
def simplexAmplitude (n : ℕ) (j k : ℕ) : ℝ := if j + k ≤ n then simplexGauge n j k else 0

theorem simplexAmplitude_support (n : ℕ) : ∀ j k, n < j + k → simplexAmplitude n j k = 0 := by
  intro j k h; simp [simplexAmplitude, not_le.mpr h]

/-- **The simplex gauge attains the joint capacity.** -/
theorem simplex_joint_capacity_attained (n : ℕ) :
    gridRowCharge n n (simplexAmplitude n) + gridColCharge n n (simplexAmplitude n) =
      (Real.cos (simplexAngle n) + Real.cos (2 * simplexAngle n)) *
        gridMass n n (simplexAmplitude n) := by
  have hE := simplexEdgeTerms_eq n _ (simplexAmplitude_support n)
  have hrow : 2 * gridRowCharge n n (simplexAmplitude n) = ∑ k ∈ range (n + 1), ∑ j ∈ range n,
      (simplexGauge n (j + 1) k / simplexGauge n j k * simplexAmplitude n j k ^ 2 +
        simplexGauge n j k / simplexGauge n (j + 1) k * simplexAmplitude n (j + 1) k ^ 2) := by
    unfold gridRowCharge
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hk' := mem_range.mp hk
    have hj' := mem_range.mp hj
    rw [← mul_assoc]
    refine two_mul_eq_ratio ?_
    by_cases h : j + 1 + k ≤ n
    · refine Or.inl ⟨simplexGauge_pos (by omega), simplexGauge_pos h, ?_, ?_⟩
      · simp [simplexAmplitude, show j + k ≤ n by omega]
      · simp [simplexAmplitude, h]
    · refine Or.inr ⟨simplexAmplitude_support n _ _ (by omega), ?_⟩
      by_cases h' : j + k = n
      · exact Or.inl (simplexGauge_cut (by omega))
      · exact Or.inr (simplexAmplitude_support n _ _ (by omega))
  have hcol : 2 * gridColCharge n n (simplexAmplitude n) = ∑ j ∈ range (n + 1), ∑ k ∈ range n,
      (simplexGauge n j (k + 1) / simplexGauge n j k * simplexAmplitude n j k ^ 2 +
        simplexGauge n j k / simplexGauge n j (k + 1) * simplexAmplitude n j (k + 1) ^ 2) := by
    unfold gridColCharge
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hj' := mem_range.mp hj
    have hk' := mem_range.mp hk
    rw [← mul_assoc]
    refine two_mul_eq_ratio ?_
    by_cases h : j + (k + 1) ≤ n
    · refine Or.inl ⟨simplexGauge_pos (by omega), simplexGauge_pos h, ?_, ?_⟩
      · simp [simplexAmplitude, show j + k ≤ n by omega]
      · simp [simplexAmplitude, h]
    · refine Or.inr ⟨simplexAmplitude_support n _ _ (by omega), ?_⟩
      by_cases h' : j + k = n
      · exact Or.inl (simplexGauge_cut (by omega))
      · exact Or.inr (simplexAmplitude_support n _ _ (by omega))
  unfold simplexEdgeTerms simplexEigenvalue at hE
  linarith

theorem gridMass_simplexAmplitude_pos (n : ℕ) : 0 < gridMass n n (simplexAmplitude n) := by
  unfold gridMass
  have h00 : 0 < simplexAmplitude n 0 0 ^ 2 := by
    have := simplexGauge_pos (n := n) (j := 0) (k := 0) (by omega)
    rw [simplexAmplitude, if_pos (by omega)]
    exact pow_pos this 2
  refine lt_of_lt_of_le h00 ?_
  have h1 : simplexAmplitude n 0 0 ^ 2 ≤ ∑ k ∈ range (n + 1), simplexAmplitude n 0 k ^ 2 :=
    single_le_sum (f := fun k => simplexAmplitude n 0 k ^ 2) (fun _ _ => sq_nonneg _)
      (mem_range.mpr (Nat.succ_pos n))
  have h2 : ∑ k ∈ range (n + 1), simplexAmplitude n 0 k ^ 2 ≤
      ∑ j ∈ range (n + 1), ∑ k ∈ range (n + 1), simplexAmplitude n j k ^ 2 :=
    single_le_sum (f := fun j => ∑ k ∈ range (n + 1), simplexAmplitude n j k ^ 2)
      (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_range.mpr (Nat.succ_pos n))
  linarith

/-- No constant below `cos θ + cos 2θ` bounds the joint charge on the simplex. -/
theorem simplex_joint_capacity_sharp (n : ℕ) {c : ℝ}
    (hc : c < Real.cos (simplexAngle n) + Real.cos (2 * simplexAngle n)) :
    ∃ f : ℕ → ℕ → ℝ, (∀ j k, n < j + k → f j k = 0) ∧
      c * gridMass n n f < gridRowCharge n n f + gridColCharge n n f := by
  refine ⟨simplexAmplitude n, simplexAmplitude_support n, ?_⟩
  rw [simplex_joint_capacity_attained]
  exact mul_lt_mul_of_pos_right hc (gridMass_simplexAmplitude_pos n)

/-! ### Each tower alone keeps the box capacity -/

/-- The bottom-row sine train, supported on the longest row of the simplex. -/
def simplexRowSine (n : ℕ) (j k : ℕ) : ℝ := if k = 0 ∧ j ≤ n then trainSine n j else 0

/-- **A single tower keeps the full capacity on the simplex**: the bottom-row sine lies in `S_n`
and carries first-tower charge `cos(π/(n+2))` times its mass (the box bound
`gridRowCharge_le` holds for every amplitude). -/
theorem simplex_row_capacity_attained (n : ℕ) :
    (∀ j k, n < j + k → simplexRowSine n j k = 0) ∧
      gridRowCharge n n (simplexRowSine n) =
        Real.cos (π / (n + 2)) * gridMass n n (simplexRowSine n) ∧
      0 < gridMass n n (simplexRowSine n) := by
  have hrowk : ∀ k, ∑ j ∈ range n, simplexRowSine n j k * simplexRowSine n (j + 1) k =
      if k = 0 then ∑ j ∈ range n, trainSine n j * trainSine n (j + 1) else 0 := by
    intro k
    split_ifs with hk
    · subst hk
      refine sum_congr rfl fun j hj => ?_
      have := mem_range.mp hj
      simp [simplexRowSine, show j ≤ n by omega, show j + 1 ≤ n by omega]
    · exact sum_eq_zero fun j _ => by simp [simplexRowSine, hk]
  have hmassk : ∀ k, ∑ j ∈ range (n + 1), simplexRowSine n j k ^ 2 =
      if k = 0 then ∑ j ∈ range (n + 1), trainSine n j ^ 2 else 0 := by
    intro k
    split_ifs with hk
    · subst hk
      refine sum_congr rfl fun j hj => ?_
      have := mem_range.mp hj
      simp [simplexRowSine, show j ≤ n by omega]
    · exact sum_eq_zero fun j _ => by simp [simplexRowSine, hk]
  have hmass : gridMass n n (simplexRowSine n) = ∑ j ∈ range (n + 1), trainSine n j ^ 2 := by
    unfold gridMass
    rw [sum_comm, sum_congr rfl fun k _ => hmassk k, sum_ite_eq' (range (n + 1)) 0]
    simp
  have hrow : gridRowCharge n n (simplexRowSine n) =
      ∑ j ∈ range n, trainSine n j * trainSine n (j + 1) := by
    unfold gridRowCharge
    rw [sum_congr rfl fun k _ => hrowk k, sum_ite_eq' (range (n + 1)) 0]
    simp
  have hatt := uniformTrain_capacity_attained n
  refine ⟨fun j k h => ?_, ?_, ?_⟩
  · simp only [simplexRowSine]
    split_ifs with h'
    · omega
    · rfl
  · rw [hrow, hmass]; linarith
  · rw [hmass]
    refine sum_pos (fun j hj => ?_) ⟨0, by simp⟩
    exact pow_pos (trainSine_pos n (mem_range.mp hj)) 2

/-! ### The capacities do not add -/

/-- **The hyperbola saves across towers**: for `n ≥ 1`,
`cos(π/(n+3)) + cos(2π/(n+3)) < 2 cos(π/(n+2))`: the joint capacity on `S_n` is strictly below the
sum of the single-tower capacities, which the box attains. -/
theorem simplex_capacities_do_not_add {n : ℕ} (hn : 1 ≤ n) :
    Real.cos (simplexAngle n) + Real.cos (2 * simplexAngle n) < 2 * Real.cos (π / (n + 2)) := by
  set α : ℝ := π / ((n : ℝ) + 2) with hα
  set β : ℝ := simplexAngle n with hβ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  have hβ0 : 0 < β := simplexAngle_pos n
  have hαβ : β < α := by
    rw [hα, hβ, simplexAngle]
    exact div_lt_div_of_pos_left hpi (by positivity) (by linarith)
  have h2 : 2 * α < 3 * β := by
    rw [hα, hβ, simplexAngle, mul_div_assoc', mul_div_assoc',
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hpi (by linarith : (0 : ℝ) < n)]
  have hsum : α + 2 * β ≤ π := by
    rw [hα, hβ, simplexAngle]
    have h2pos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h3pos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
    have e : π / ((n : ℝ) + 2) + 2 * (π / ((n : ℝ) + 3)) =
        π * ((3 * (n : ℝ) + 7) / (((n : ℝ) + 2) * ((n : ℝ) + 3))) := by
      first | (field_simp; ring) | field_simp
    rw [e]
    have : (3 * (n : ℝ) + 7) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    exact (mul_le_mul_of_nonneg_left this hpi.le).trans (le_of_eq (mul_one π))
  -- `2cos α − cos β − cos 2β = 2 sin((α+2β)/2) sin((2β−α)/2) − 2 sin((α+β)/2) sin((α−β)/2)`
  have hA : Real.sin ((α + β) / 2) < Real.sin ((α + 2 * β) / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hB : Real.sin ((α - β) / 2) < Real.sin ((2 * β - α) / 2) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hA0 : 0 < Real.sin ((α + β) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hB0 : 0 < Real.sin ((α - β) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hprod : Real.sin ((α + β) / 2) * Real.sin ((α - β) / 2) <
      Real.sin ((α + 2 * β) / 2) * Real.sin ((2 * β - α) / 2) :=
    mul_lt_mul'' hA hB hA0.le hB0.le
  have e1 := Real.cos_sub_cos β α
  have e2 := Real.cos_sub_cos α (2 * β)
  have e3 : (α - 2 * β) / 2 = -((2 * β - α) / 2) := by ring
  have e4 : (β - α) / 2 = -((α - β) / 2) := by ring
  rw [e4, Real.sin_neg] at e1
  rw [e3, Real.sin_neg] at e2
  rw [show (β + α) / 2 = (α + β) / 2 by ring] at e1
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
