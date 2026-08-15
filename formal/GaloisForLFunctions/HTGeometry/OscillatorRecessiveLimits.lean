import GaloisForLFunctions.HTGeometry.OscillatorProductMonotone

/-!
# Boundary behaviour of a square-integrable oscillator solution

Past the turning point a square-integrable nontrivial solution of `v″ = (ξ² − μ)v` has `v v′ < 0`,
so `v²` is antitone and `v` has no zeros, hence a constant sign.  Three limits follow, each by the
same mechanism: a monotone quantity whose derivative is bounded away from zero would drive a
nonnegative quantity below zero.

`v v′ → 0` ,   `v′ → 0` ,   `ξ² v² → 0` .

The last uses the nonnegativity of the energy, `(ξ² − μ)v² ≤ v′²`.  Together they make the boundary
term `v v′ + ξ v²` of the ladder identity vanish at infinity.
-/

open Set MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A nonnegative function cannot have derivative bounded above by a negative constant on a
half line. -/
theorem not_deriv_le_neg_of_nonneg {f f' : ℝ → ℝ} {b eps : ℝ} (heps : 0 < eps)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hnn : ∀ x ∈ Ici b, 0 ≤ f x)
    (hd : ∀ x ∈ Ici b, f' x ≤ -eps) : False := by
  have hanti : AntitoneOn (fun x => f x + eps * x) (Ici b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici b) ?_ ?_ ?_
    · intro x _
      exact (((hf x).continuousAt).add
        ((continuous_const.mul continuous_id).continuousAt)).continuousWithinAt
    · intro x _
      exact (((hf x).add ((hasDerivAt_id x).const_mul eps)).differentiableAt).differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hxm : x ∈ Ici b := le_of_lt (Set.mem_Ioi.1 hx)
      have hderiv : HasDerivAt (fun y => f y + eps * y) (f' x + eps) x := by
        refine ((hf x).add ((hasDerivAt_id x).const_mul eps)).congr_deriv ?_
        ring
      rw [hderiv.deriv]
      linarith [hd x hxm]
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((f b + eps * b) / eps) |b| + 1)
  set x : ℝ := (N : ℝ) with hxdef
  have hmax1 : (f b + eps * b) / eps ≤ max ((f b + eps * b) / eps) |b| := le_max_left _ _
  have hmax2 : |b| ≤ max ((f b + eps * b) / eps) |b| := le_max_right _ _
  have hbx : b ≤ x := by
    have h3 : b ≤ |b| := le_abs_self b
    linarith
  have hle := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hbx) hbx
  have hfx : 0 ≤ f x := hnn x (Set.mem_Ici.2 hbx)
  have hbig : (f b + eps * b) / eps < x := by linarith
  rw [div_lt_iff₀ heps] at hbig
  nlinarith

/-- A continuous nowhere-zero function on a half line has a constant sign. -/
theorem sign_locally_const_of_ne_zero {v : ℝ → ℝ} {b : ℝ} (hc : Continuous v)
    (hnz : ∀ x ∈ Ici b, v x ≠ 0) :
    (∀ x ∈ Ici b, 0 < v x) ∨ (∀ x ∈ Ici b, v x < 0) := by
  rcases lt_or_gt_of_ne (hnz b (Set.mem_Ici.2 le_rfl)) with hneg | hpos
  · right
    intro x hx
    have hbx : b ≤ x := Set.mem_Ici.1 hx
    by_contra hcon
    have hxpos : 0 < v x := lt_of_le_of_ne (not_lt.1 hcon) (Ne.symm (hnz x hx))
    have hmem : (0 : ℝ) ∈ Icc (v b) (v x) := ⟨le_of_lt hneg, le_of_lt hxpos⟩
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hbx hc.continuousOn hmem
    exact hnz y (Set.mem_Ici.2 (Set.mem_Icc.1 hy).1) hy0
  · left
    intro x hx
    have hbx : b ≤ x := Set.mem_Ici.1 hx
    by_contra hcon
    have hxneg : v x < 0 := lt_of_le_of_ne (not_lt.1 hcon) (hnz x hx)
    have hmem : (0 : ℝ) ∈ Icc (v x) (v b) := ⟨le_of_lt hxneg, le_of_lt hpos⟩
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hbx hc.continuousOn hmem
    exact hnz y (Set.mem_Ici.2 (Set.mem_Icc.1 hy).1) hy0

/-- **The product tends to zero.**  It is nondecreasing and negative, and if it stayed below `−ε`
the square would be driven negative. -/
theorem tendsto_oscProduct_zero {mu : ℝ} {v v' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hmu : mu ≤ a ^ 2) (hab : a ≤ b)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hneg : ∀ x ∈ Ici b, oscProduct v v' x < 0) :
    Tendsto (oscProduct v v') atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hmono := monotoneOn_oscProduct ha hmu hv hv'
  have hex : ∃ x1 ∈ Ici b, -eps < oscProduct v v' x1 := by
    by_contra hcon
    have hall : ∀ x ∈ Ici b, oscProduct v v' x ≤ -eps := by
      intro x hx
      by_contra h
      exact hcon ⟨x, hx, lt_of_not_ge h⟩
    have hsqderiv : ∀ x, HasDerivAt (fun y => v y ^ 2) (2 * oscProduct v v' x) x := by
      intro x
      refine ((hv x).pow 2).congr_deriv ?_
      rw [oscProduct]
      push_cast
      ring
    refine not_deriv_le_neg_of_nonneg (f := fun x => v x ^ 2)
      (f' := fun x => 2 * oscProduct v v' x) (b := b) (eps := 2 * eps) (by linarith)
      hsqderiv (fun x _ => sq_nonneg _) ?_
    intro x hx
    linarith [hall x hx]
  obtain ⟨x1, hx1, hx1lt⟩ := hex
  refine ⟨x1, fun x hx => ?_⟩
  have hbx1 : b ≤ x1 := Set.mem_Ici.1 hx1
  have hbx : b ≤ x := le_trans hbx1 hx
  have hax1 : x1 ∈ Ici a := Set.mem_Ici.2 (le_trans hab hbx1)
  have hax : x ∈ Ici a := Set.mem_Ici.2 (le_trans hab hbx)
  have hge : oscProduct v v' x1 ≤ oscProduct v v' x := hmono hax1 hax hx
  have hlt : oscProduct v v' x < 0 := hneg x (Set.mem_Ici.2 hbx)
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-- **The derivative tends to zero** for a positive solution with negative product: it is
nondecreasing and negative, and if it stayed below `−ε` the solution itself would go negative. -/
theorem tendsto_deriv_zero_of_pos {mu : ℝ} {v v' : ℝ → ℝ} {b : ℝ} (hb : 0 < b) (hmu : mu ≤ b ^ 2)
    (hv : ∀ x, HasDerivAt v (v' x) x)
    (hv' : ∀ x, HasDerivAt v' ((x ^ 2 - mu) * v x) x)
    (hpos : ∀ x ∈ Ici b, 0 < v x)
    (hneg : ∀ x ∈ Ici b, oscProduct v v' x < 0) :
    Tendsto v' atTop (𝓝 0) := by
  have hderivneg : ∀ x ∈ Ici b, v' x < 0 := by
    intro x hx
    have h := hneg x hx
    rw [oscProduct] at h
    nlinarith [hpos x hx]
  have hmono : MonotoneOn v' (Ici b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici b) ?_ ?_ ?_
    · exact fun x _ => ((hv' x).continuousAt).continuousWithinAt
    · intro x _
      exact (hv' x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hxm : x ∈ Ici b := le_of_lt (Set.mem_Ioi.1 hx)
      rw [(hv' x).deriv]
      have hbx : b ≤ x := Set.mem_Ici.1 hxm
      have hxsq : mu ≤ x ^ 2 := by nlinarith
      have := hpos x hxm
      nlinarith
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hex : ∃ x1 ∈ Ici b, -eps < v' x1 := by
    by_contra hcon
    have hall : ∀ x ∈ Ici b, v' x ≤ -eps := by
      intro x hx
      by_contra h
      exact hcon ⟨x, hx, lt_of_not_ge h⟩
    exact not_deriv_le_neg_of_nonneg heps hv (fun x hx => le_of_lt (hpos x hx)) hall
  obtain ⟨x1, hx1, hx1lt⟩ := hex
  refine ⟨x1, fun x hx => ?_⟩
  have hbx1 : b ≤ x1 := Set.mem_Ici.1 hx1
  have hbx : b ≤ x := le_trans hbx1 hx
  have hge : v' x1 ≤ v' x := hmono hx1 (Set.mem_Ici.2 hbx) hx
  have hlt : v' x < 0 := hderivneg x (Set.mem_Ici.2 hbx)
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-- **The weighted square tends to zero.**  Nonnegative energy bounds `(ξ² − μ)v²` by `v′²`. -/
theorem tendsto_weighted_sq_zero {mu : ℝ} {v v' : ℝ → ℝ} {b : ℝ}
    (hE : ∀ x ∈ Ici b, 0 ≤ oscillatorMonotoneEnergy mu v v' x)
    (hmu : ∀ x ∈ Ici b, mu ≤ x ^ 2)
    (hv'0 : Tendsto v' atTop (𝓝 0)) :
    Tendsto (fun x => (x ^ 2 - mu) * v x ^ 2) atTop (𝓝 0) := by
  have hsq : Tendsto (fun x => v' x ^ 2) atTop (𝓝 0) := by
    have := hv'0.pow 2
    simpa using this
  refine squeeze_zero' ?_ ?_ hsq
  · filter_upwards [eventually_ge_atTop b] with x hx
    have h1 := hmu x (Set.mem_Ici.2 hx)
    nlinarith [sq_nonneg (v x)]
  · filter_upwards [eventually_ge_atTop b] with x hx
    have h := hE x (Set.mem_Ici.2 hx)
    rw [oscillatorMonotoneEnergy] at h
    linarith

/-- The linear moment of the square tends to zero. -/
theorem tendsto_mul_sq_zero {mu : ℝ} {v : ℝ → ℝ}
    (hw : Tendsto (fun x => (x ^ 2 - mu) * v x ^ 2) atTop (𝓝 0)) :
    Tendsto (fun x => x * v x ^ 2) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ hw
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (max 1 (|mu| + 1))] with x hx
    have h1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
    have h2 : |mu| + 1 ≤ x := le_trans (le_max_right _ _) hx
    have hmu' : mu ≤ |mu| := le_abs_self mu
    have hstep : x ≤ x ^ 2 - mu := by nlinarith
    nlinarith [sq_nonneg (v x)]

end GaloisForLFunctions.HTGeometry
