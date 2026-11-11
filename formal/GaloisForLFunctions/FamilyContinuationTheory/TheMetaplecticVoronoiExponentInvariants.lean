import GaloisForLFunctions.FamilyContinuationTheory.TheBudgetInTheTwistExponent

/-!
# Metaplectic Voronoi exponent invariants and the `(n − 2)/(n − 1)` floor

Single reflection closes every positive `L²` sieve at `θ ≥ (n − 2)/(n − 1)` (`4/5` at `n = 6`,
`σ₀ = 5/6`) under `2ℓ ≤ lx + ly` (`free_floor_le_probeThetaFree`). Passing to higher-rank `GL(d)`
or metaplectic cover Voronoi involutions, iterated reflection-summation words, or multi-variable
Weyl-group reflections cannot shift `(n − 2)/(n − 1)` downward inside any Cauchy–Schwarz `L²`
row-sieve:

* **`SL₂(ℝ)` Coxeter–Cartan trichotomy** (`det_voronoiCompositeMatrix`,
  `voronoiQuadraticInvariant_reflect`, `voronoiQuadraticInvariant_sum`,
  `parabolic_linear_invariant_iff`, `voronoi_no_linear_invariant_of_ne_four`). Generalized row
  reflections `ρ_{row, κ}(r, l) = (r, κ r − l)` and row-index summations
  `ρ_{sum, κ'}(r, l) = (κ' l − r, l)` have composite `SL₂(ℝ)` matrix `M_{κ, κ'}` (`det = 1`,
  `tr = κ κ' − 2`) preserving `Q_{κ, κ'}(r, l) = κ r² − κ κ' r l + κ' l²`. The dynamics are
  elliptic for `κ κ' < 4` (`M_{1,1}³ = M_{1,2}⁴ = M_{1,3}⁶ = I`), parabolic with unique linear
  invariant `(κ/2) r − l` at `κ κ' = 4` (`r − l` at `(2, 2)`), and hyperbolic without nonzero
  linear invariants for `κ > 2, κ' = 2` (strictly expanding dual excess `(κ − 1)r − l > r − l`).
* **Unitary Plancherel invariance and unconditional hybrid-slot floor**
  (`sum_norm_sq_mulVec_unitary`, `max_zero_sub_div_three_le_slotHybridExcess`,
  `free_floor_le_probeThetaHybridFree`). Every unitary transform `U` (`Uᴴ U = I`) preserves
  `∑_i ‖(U A)_i‖² = ∑_i ‖A_i‖²`. Retaining the hybrid slot excess
  `slotHybridExcess(M, ℓ, v) = max(M, v) − M + ℓ − hybridSaving(v, ℓ) ≥ max(0, (2ℓ − M)/3)` removes
  the hypothesis `2ℓ ≤ lx + ly` completely: for every `n ≥ 3` and every `(lx, ly, ℓ, v) ∈ ℝ⁴`,
  `probeThetaHybridFree n lx ly ℓ v ≥ (n − 2)/(n − 1)`, with equality for `n > 3` iff
  `lx ≤ ly`, `0 ≤ ℓ`, `lx + ly = 2ℓ`, and `v = 2ℓ`.
* **Multi-variable scaling, Weyl-orbit twist circularity, and escape classification**
  (`mul_free_floor_le_probeThetaDesignHybridFree`, `principalRelativeSizeOrder_sub_window`,
  `escape_below_free_floor_bound`). Adding row variables multiplies the free floor by `k`
  (`θ ≥ k(n − 2)/(n − 1)`) and drives the joint reflection-summation trace to `4k − 2 ≥ 6`
  (`k ≥ 2`), while passing through row-index summation injects principal `n`-th-power twists
  returning `β`. Crossing `< (n − 2)/(n − 1)` at `n ≥ 3, k ≥ 1` requires strictly positive
  pre-Cauchy–Schwarz bilinear row-column cancellation `sBilin > 0` (`sBilin ≥ 1/4 − 1/n` for
  `σ₀ = 3/4`, `sBilin ≥ ½ − 1/n` for `σ₀ = ½`).
-/

namespace GaloisForLFunctions.FamilyContinuationTheory.Budget

open Finset ComplexConjugate _root_.RHTower.QuasiRHDetectorScaleBudget

noncomputable section

/-! ### Generalized metaplectic / `GL(d)` Voronoi involutions and `SL₂(ℝ)` trichotomy -/

/-- Row Voronoi reflection of conductor degree `κ`: `(r, l) ↦ (r, κ r − l)`. -/
def reflectScaleKappa (κ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, κ * p.1 - p.2)

/-- Row-index summation of conductor degree `κ'`: `(r, l) ↦ (κ' l − r, l)`. -/
def sumScaleKappa (κ' : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (κ' * p.2 - p.1, p.2)

/-- `2 × 2` matrix of the composite Voronoi-summation step `sumScaleKappa κ' ∘ reflectScaleKappa κ`. -/
def voronoiCompositeMatrix (κ κ' : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![κ * κ' - 1, -κ'; κ, -1]

/-- Universal quadratic form preserved by both `reflectScaleKappa κ` and `sumScaleKappa κ'`. -/
def voronoiQuadraticInvariant (κ κ' r l : ℝ) : ℝ :=
  κ * r ^ 2 - κ * κ' * r * l + κ' * l ^ 2

theorem reflectScaleKappa_two : reflectScaleKappa 2 = reflectScale := rfl

theorem sumScaleKappa_two : sumScaleKappa 2 = sumScale := rfl

theorem reflectScaleKappa_involutive (κ : ℝ) : Function.Involutive (reflectScaleKappa κ) := by
  rintro ⟨r, l⟩
  simp only [reflectScaleKappa, Prod.mk.injEq, true_and]
  ring

theorem sumScaleKappa_involutive (κ' : ℝ) : Function.Involutive (sumScaleKappa κ') := by
  rintro ⟨r, l⟩
  simp only [sumScaleKappa, Prod.mk.injEq, and_true]
  ring

theorem sumScaleKappa_reflectScaleKappa (κ κ' r l : ℝ) :
    sumScaleKappa κ' (reflectScaleKappa κ (r, l)) =
      ((κ * κ' - 1) * r - κ' * l, κ * r - l) := by
  simp only [sumScaleKappa, reflectScaleKappa, Prod.mk.injEq, and_true]
  ring

/-- Every composite Voronoi-summation transformation has determinant `1` (`M_{κ, κ'} ∈ SL₂(ℝ)`). -/
theorem det_voronoiCompositeMatrix (κ κ' : ℝ) :
    (voronoiCompositeMatrix κ κ').det = 1 := by
  rw [voronoiCompositeMatrix, Matrix.det_fin_two_of]
  ring

/-- Trace of `M_{κ, κ'}`: elliptic when `|κ κ' − 2| < 2` (`0 < κ κ' < 4`), parabolic at `κ κ' = 4`,
and hyperbolic for `κ κ' > 4`. -/
theorem trace_voronoiCompositeMatrix (κ κ' : ℝ) :
    (voronoiCompositeMatrix κ κ').trace = κ * κ' - 2 := by
  rw [voronoiCompositeMatrix, Matrix.trace_fin_two_of]
  ring

/-- `Q_{κ, κ'}` is invariant under `reflectScaleKappa κ`. -/
theorem voronoiQuadraticInvariant_reflect (κ κ' : ℝ) (p : ℝ × ℝ) :
    voronoiQuadraticInvariant κ κ' (reflectScaleKappa κ p).1 (reflectScaleKappa κ p).2 =
      voronoiQuadraticInvariant κ κ' p.1 p.2 := by
  unfold voronoiQuadraticInvariant reflectScaleKappa
  ring

/-- `Q_{κ, κ'}` is invariant under `sumScaleKappa κ'`. -/
theorem voronoiQuadraticInvariant_sum (κ κ' : ℝ) (p : ℝ × ℝ) :
    voronoiQuadraticInvariant κ κ' (sumScaleKappa κ' p).1 (sumScaleKappa κ' p).2 =
      voronoiQuadraticInvariant κ κ' p.1 p.2 := by
  unfold voronoiQuadraticInvariant sumScaleKappa
  ring

/-- `Q_{κ, κ'}` is invariant along every iterate `(sumScaleKappa κ' ∘ reflectScaleKappa κ)^[m]`. -/
theorem voronoiQuadraticInvariant_iterate (κ κ' : ℝ) (m : ℕ) (p : ℝ × ℝ) :
    let q := (sumScaleKappa κ' ∘ reflectScaleKappa κ)^[m] p
    voronoiQuadraticInvariant κ κ' q.1 q.2 = voronoiQuadraticInvariant κ κ' p.1 p.2 := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
    simp only [Function.iterate_succ_apply, Function.comp_apply]
    rw [ih, voronoiQuadraticInvariant_sum, voronoiQuadraticInvariant_reflect]

/-- Finite Weyl-group orders in the elliptic crystallographic cases `(1, 1)` (`A₂`, order `3`),
`(1, 2)` (`B₂`, order `4`), and `(1, 3)` (`G₂`, order `6`). -/
theorem voronoiCompositeMatrix_elliptic_orders :
    voronoiCompositeMatrix 1 1 ^ 3 = 1 ∧
      voronoiCompositeMatrix 1 2 ^ 4 = 1 ∧
      voronoiCompositeMatrix 1 3 ^ 6 = 1 := by
  have h11 : voronoiCompositeMatrix 1 1 ^ 3 = 1 := by
    rw [pow_three]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [voronoiCompositeMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  have h12_sq : voronoiCompositeMatrix 1 2 ^ 2 = -1 := by
    rw [sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [voronoiCompositeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have h12 : voronoiCompositeMatrix 1 2 ^ 4 = 1 := by
    calc voronoiCompositeMatrix 1 2 ^ 4 = (voronoiCompositeMatrix 1 2 ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (-1) ^ 2 := by rw [h12_sq]
      _ = 1 := by norm_num
  have h13_cube : voronoiCompositeMatrix 1 3 ^ 3 = -1 := by
    rw [pow_three]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [voronoiCompositeMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have h13 : voronoiCompositeMatrix 1 3 ^ 6 = 1 := by
    calc voronoiCompositeMatrix 1 3 ^ 6 = (voronoiCompositeMatrix 1 3 ^ 3) ^ 2 := by rw [← pow_mul]
      _ = (-1) ^ 2 := by rw [h13_cube]
      _ = 1 := by norm_num
  exact ⟨h11, h12, h13⟩

/-- In the elliptic regime `0 < κ`, `0 < κ'`, `κ κ' < 4`, `Q_{κ, κ'}` is strictly positive definite,
forcing all reflection-summation orbits to remain bounded. -/
theorem voronoiQuadraticInvariant_pos_of_lt_four {κ κ' r l : ℝ}
    (hκ : 0 < κ) (hκ' : 0 < κ') (hprod : κ * κ' < 4) (hne : (r, l) ≠ (0, 0)) :
    0 < voronoiQuadraticInvariant κ κ' r l := by
  have hrew : voronoiQuadraticInvariant κ κ' r l =
      κ * (r - κ' * l / 2) ^ 2 + κ' * (4 - κ * κ') / 4 * l ^ 2 := by
    unfold voronoiQuadraticInvariant
    ring
  rw [hrew]
  by_cases hl : l = 0
  · have hr : r ≠ 0 := fun hr0 => hne (Prod.ext hr0 hl)
    rw [hl]
    simp only [mul_zero, zero_div, sub_zero, zero_pow two_ne_zero, add_zero]
    exact mul_pos hκ (sq_pos_of_ne_zero hr)
  · have ht1 : 0 ≤ κ * (r - κ' * l / 2) ^ 2 := mul_nonneg hκ.le (sq_nonneg _)
    have ht2 : 0 < κ' * (4 - κ * κ') / 4 * l ^ 2 :=
      mul_pos (div_pos (mul_pos hκ' (by linarith)) (by norm_num)) (sq_pos_of_ne_zero hl)
    linarith

/-- On the parabolic locus `κ κ' = 4` (`κ ≠ 0`), `Q_{κ, 4/κ}` degenerates to
`(4/κ)((κ/2) r − l)²`, and `(κ/2) r − l` (`r − l` at `κ = 2`) is the unique linear invariant up to
scalar multiplication. -/
theorem parabolic_quadratic_and_iterate {κ : ℝ} (hκ : κ ≠ 0) (m : ℕ) (r l : ℝ) :
    voronoiQuadraticInvariant κ (4 / κ) r l = 4 / κ * (κ / 2 * r - l) ^ 2 ∧
      (sumScaleKappa (4 / κ) ∘ reflectScaleKappa κ)^[m] (r, l) =
        (r + m * (4 / κ) * (κ / 2 * r - l), l + m * 2 * (κ / 2 * r - l)) := by
  refine ⟨?_, ?_⟩
  · unfold voronoiQuadraticInvariant
    field_simp
    ring
  · induction m generalizing r l with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply, Function.comp_apply, sumScaleKappa_reflectScaleKappa, ih]
      simp only [Prod.mk.injEq]
      push_cast
      constructor <;> (field_simp; ring)

theorem parabolic_linear_invariant_iff {κ : ℝ} (hκ : κ ≠ 0) (a b : ℝ) :
    (∀ r l : ℝ,
      a * (sumScaleKappa (4 / κ) (reflectScaleKappa κ (r, l))).1 +
        b * (sumScaleKappa (4 / κ) (reflectScaleKappa κ (r, l))).2 = a * r + b * l) ↔
      a = -(κ / 2) * b := by
  constructor
  · intro h
    have h01 := h 0 1
    simp only [sumScaleKappa_reflectScaleKappa, mul_zero, zero_sub] at h01
    have hmul : -(4 / κ) * a - 2 * b = 0 := by linarith
    have hmul2 := congrArg (fun x => κ * x) hmul
    simp only [mul_zero] at hmul2
    have hrew : κ * (-(4 / κ) * a - 2 * b) = -4 * a - 2 * κ * b := by field_simp; ring
    rw [hrew] at hmul2
    linarith
  · intro ha r l
    rw [ha, sumScaleKappa_reflectScaleKappa]
    field_simp
    ring

/-- Off the parabolic locus (`κ κ' ≠ 4`, in particular every `GL(d)` Voronoi reflection `κ > 2`
paired with `κ' = 2`), no nonzero linear translation invariant exists. -/
theorem voronoi_no_linear_invariant_of_ne_four {κ κ' : ℝ} (hne : κ * κ' ≠ 4) (a b : ℝ) :
    (∀ r l : ℝ,
      a * (sumScaleKappa κ' (reflectScaleKappa κ (r, l))).1 +
        b * (sumScaleKappa κ' (reflectScaleKappa κ (r, l))).2 = a * r + b * l) ↔
      a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h10 := h 1 0
    have h01 := h 0 1
    simp only [sumScaleKappa_reflectScaleKappa, mul_one, mul_zero, sub_zero, zero_sub,
      add_zero, zero_add] at h10 h01
    have hb : b = -(κ' / 2) * a := by linarith
    have ha_eq : a * (κ * κ' - 4) = 0 := by
      rw [hb] at h10
      linarith
    have ha0 : a = 0 := (mul_eq_zero.mp ha_eq).resolve_right (sub_ne_zero.mpr hne)
    exact ⟨ha0, by rw [hb, ha0, mul_zero]⟩
  · rintro ⟨rfl, rfl⟩ _ _
    simp

/-- Higher-conductor Voronoi reflections (`κ > 2`, e.g. `GL(d)` for `d ≥ 3` or covers `κ = 3, 4`)
strictly worsen both the single-reflection dual excess `(κ − 1)r − l` and the composite excess
along `sumScale ∘ reflectScaleKappa κ` for `0 < r` and `l ≤ r`. -/
theorem hyperbolic_voronoi_excess_strict_growth {κ r l : ℝ} (hκ : 2 < κ) (hr : 0 < r)
    (hlr : l ≤ r) :
    r - l < (reflectScaleKappa κ (r, l)).2 - r ∧
      r - l < (sumScale (reflectScaleKappa κ (r, l))).1 -
        (sumScale (reflectScaleKappa κ (r, l))).2 ∧
      r < (sumScale (reflectScaleKappa κ (r, l))).1 := by
  simp only [reflectScaleKappa, sumScale]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [mul_pos (by linarith : 0 < κ - 2) hr]
  · nlinarith [mul_pos (by linarith : 0 < κ - 2) hr]
  · nlinarith [mul_pos (by linarith : 0 < κ - 2) hr]

/-! ### Unitary Plancherel `L²`-invariance and unconditional hybrid-slot floor -/

/-- **Finite-dimensional Plancherel identity.** Any unitary transformation `U` (`Uᴴ U = I`,
modeling any composition of unitary multi-variable or metaplectic Voronoi transforms) preserves
the `ℓ²` row norm identically. -/
theorem sum_norm_sq_mulVec_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U.conjTranspose * U = 1) (A : I → ℂ) :
    ∑ i : I, ‖(U.mulVec A) i‖ ^ 2 = ∑ i : I, ‖A i‖ ^ 2 := by
  have hc : ∑ i : I, ((‖(U.mulVec A) i‖ ^ 2 : ℝ) : ℂ) = ∑ j : I, ((‖A j‖ ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ i : I, ((‖(U.mulVec A) i‖ ^ 2 : ℝ) : ℂ) =
        ∑ j : I, ∑ k : I, conj (A j) * (U.conjTranspose j i * U i k) * A k := by
      intro i
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm _ (conj _)]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.conjTranspose_apply]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ k : I,
        ∑ i : I, conj (A j) * (U.conjTranspose j i * U i k) * A k =
          conj (A j) * (U.conjTranspose * U) j k * A k := by
      intro k
      have heq : ∀ i : I, conj (A j) * (U.conjTranspose j i * U i k) * A k =
          conj (A j) * A k * (U.conjTranspose j i * U i k) := fun _ => by ring
      simp_rw [heq, ← Finset.mul_sum, Matrix.mul_apply]
      ring
    simp_rw [hinner, hU]
    rw [Finset.sum_eq_single j]
    · simp only [Matrix.one_apply_eq, mul_one]
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · intro k _ hkj
      rw [Matrix.one_apply_ne (Ne.symm hkj), mul_zero, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hre := congrArg Complex.re hc
  simp only [Complex.re_sum, Complex.ofReal_re] at hre
  exact hre

/-- Cauchy–Schwarz between a row vector `A` and column detector `B` is invariant under replacing
`A` by `U A` for any unitary transformation `U`. -/
theorem norm_sq_inner_le_unitary_mul {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U.conjTranspose * U = 1) (A B : I → ℂ) :
    ‖∑ i : I, A i * conj (B i)‖ ^ 2 ≤
      (∑ i : I, ‖(U.mulVec A) i‖ ^ 2) * (∑ i : I, ‖B i‖ ^ 2) := by
  rw [sum_norm_sq_mulVec_unitary U hU A]
  have htri : ‖∑ i : I, A i * conj (B i)‖ ≤ ∑ i : I, ‖A i‖ * ‖B i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
  exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖A i‖) (fun i => ‖B i‖))

/-- **Two-parameter translation invariance of `probeThetaFree`.** Redistributing column scales by
`δ` (`lx + δ ≤ ly − δ`) and translating `(M, ℓ)` along `(2Δ, Δ)` leaves `probeThetaFree`
identically unchanged. -/
theorem probeThetaFree_translation_invariant (n lx ly ℓ δ Δ : ℝ)
    (hle : lx ≤ ly) (hle' : lx + δ ≤ ly - δ) :
    probeThetaFree n (lx + δ + Δ) (ly - δ + Δ) (ℓ + Δ) = probeThetaFree n lx ly ℓ := by
  unfold probeThetaFree
  rw [max_eq_right (by linarith : 0 ≤ (ly - δ + Δ) - (lx + δ + Δ)),
    max_eq_right (by linarith : 0 ≤ ly - lx)]
  congr 1
  ring

/-- Excess over `M` of the fully marked (`d = 0`) reflected energy at an arbitrary dual scale `v`,
retaining the hybrid slot term `ℓ − hybridSaving v ℓ`. -/
def slotHybridExcess (M ℓ v : ℝ) : ℝ := max M v - M + ℓ - hybridSaving v ℓ

theorem reflectedExponent_eq_add_slotHybridExcess (M ℓ v : ℝ) :
    reflectedExponent 0 M 0 0 ℓ v 0 0 v = M + slotHybridExcess M ℓ v := by
  unfold reflectedExponent slotHybridExcess
  simp only [zero_div, zero_add, add_zero, sub_zero, mul_zero, sub_self, max_self]
  ring

/-- **Universal lower bound on `slotHybridExcess`.** Across all `(M, ℓ, v) ∈ ℝ³`, the hybrid slot
excess is at least `max 0 ((2ℓ − M)/3)`, and vanishes iff `0 ≤ ℓ ∧ 2ℓ ≤ v ∧ v ≤ M`. -/
theorem max_zero_sub_div_three_le_slotHybridExcess (M ℓ v : ℝ) :
    max 0 ((2 * ℓ - M) / 3) ≤ slotHybridExcess M ℓ v := by
  unfold slotHybridExcess hybridSaving
  refine max_le ?_ ?_
  · have hM : M ≤ max M v := le_max_left _ _
    have hmin : min v (min ℓ ((v + ℓ) / 3)) ≤ ℓ :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  · have hconv : (v - M) / 3 ≤ max M v - M := by
      have hM : M ≤ max M v := le_max_left _ _
      have hv : v ≤ max M v := le_max_right _ _
      linarith
    have hthird : min v (min ℓ ((v + ℓ) / 3)) ≤ (v + ℓ) / 3 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith

theorem slotHybridExcess_eq_zero_iff (M ℓ v : ℝ) :
    slotHybridExcess M ℓ v = 0 ↔ 0 ≤ ℓ ∧ 2 * ℓ ≤ v ∧ v ≤ M := by
  unfold slotHybridExcess hybridSaving
  constructor
  · intro h
    have h1 : 0 ≤ max M v - M := sub_nonneg.mpr (le_max_left _ _)
    have h2 : min v (min ℓ ((v + ℓ) / 3)) ≤ ℓ := (min_le_right _ _).trans (min_le_left _ _)
    have heq1 : max M v = M := by linarith
    have heq2 : min v (min ℓ ((v + ℓ) / 3)) = ℓ := by linarith
    have hvM : v ≤ M := max_eq_left_iff.mp heq1
    have hℓv : ℓ ≤ v := by rw [← heq2]; exact min_le_left _ _
    have hℓ3 : ℓ ≤ (v + ℓ) / 3 := by
      rw [← heq2]
      exact (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by linarith, by linarith, hvM⟩
  · rintro ⟨hℓ0, h2ℓv, hvM⟩
    rw [max_eq_left hvM]
    have hmin1 : min ℓ ((v + ℓ) / 3) = ℓ := min_eq_left (by linarith)
    rw [hmin1, min_eq_right (by linarith)]
    ring

/-- Effective twist exponent retaining the hybrid slot excess at arbitrary dual scale `v ∈ ℝ`. -/
def probeThetaHybridFree (n lx ly ℓ v : ℝ) : ℝ :=
  positiveFormTheta n (lowBoundaryFreeOrder n lx ly ℓ + slotHybridExcess (lx + ly) ℓ v / 2)

/-- **Unconditional hybrid-slot floor (removing `2ℓ ≤ lx + ly`).** For every order `n ≥ 3` and
every `(lx, ly, ℓ, v) ∈ ℝ⁴`, `probeThetaHybridFree n lx ly ℓ v ≥ (n − 2)/(n − 1)`. -/
theorem free_floor_le_probeThetaHybridFree {n : ℝ} (hn : 3 ≤ n) (lx ly ℓ v : ℝ) :
    (n - 2) / (n - 1) ≤ probeThetaHybridFree n lx ly ℓ v := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) < n := by linarith
  unfold probeThetaHybridFree
  rw [← positiveFormTheta_free_floor hn0.ne' hn1.ne']
  refine (positiveFormTheta_strictMono hn1).monotone ?_
  have hslot := max_zero_sub_div_three_le_slotHybridExcess (lx + ly) ℓ v
  have h0 : 0 ≤ slotHybridExcess (lx + ly) ℓ v := (le_max_left _ _).trans hslot
  have h3 : (2 * ℓ - (lx + ly)) / 3 ≤ slotHybridExcess (lx + ly) ℓ v :=
    (le_max_right _ _).trans hslot
  have hν : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
  have hrew : lowBoundaryFreeOrder n lx ly ℓ - (1 - 1 / n) =
      (lx + ly - 2 * ℓ + (max 0 (ly - lx) - (ly - lx))) / (2 * n) := by
    unfold lowBoundaryFreeOrder
    field_simp
    ring
  rcases le_total (2 * ℓ) (lx + ly) with hle | hgt
  · have hnn : 0 ≤ lowBoundaryFreeOrder n lx ly ℓ - (1 - 1 / n) := by
      rw [hrew]
      exact div_nonneg (by linarith) (by linarith)
    linarith
  · have hinv : 1 / (2 * n) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hmul : (2 * ℓ - (lx + ly)) * (1 / (2 * n)) ≤ (2 * ℓ - (lx + ly)) * (1 / 6) :=
      mul_le_mul_of_nonneg_left hinv (by linarith)
    have hge : -(2 * ℓ - (lx + ly)) * (1 / (2 * n)) ≤
        lowBoundaryFreeOrder n lx ly ℓ - (1 - 1 / n) := by
      rw [hrew]
      have hpos_c : 0 ≤ (max 0 (ly - lx) - (ly - lx)) / (2 * n) :=
        div_nonneg (by linarith) (by linarith)
      have heq : (lx + ly - 2 * ℓ + (max 0 (ly - lx) - (ly - lx))) / (2 * n) =
          -(2 * ℓ - (lx + ly)) * (1 / (2 * n)) +
            (max 0 (ly - lx) - (ly - lx)) / (2 * n) := by ring
      linarith
    linarith

/-- For `n > 3` (in particular `n = 4, 5, 6`), `probeThetaHybridFree` attains `(n − 2)/(n − 1)`
if and only if `lx ≤ ly`, `0 ≤ ℓ`, `lx + ly = 2ℓ`, and `v = 2ℓ`. -/
theorem probeThetaHybridFree_eq_iff {n lx ly ℓ v : ℝ} (hn : 3 < n) :
    probeThetaHybridFree n lx ly ℓ v = (n - 2) / (n - 1) ↔
      lx ≤ ly ∧ 0 ≤ ℓ ∧ lx + ly = 2 * ℓ ∧ v = 2 * ℓ := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) < n := by linarith
  unfold probeThetaHybridFree
  rw [← positiveFormTheta_free_floor hn0.ne' hn1.ne',
    (positiveFormTheta_strictMono hn1).injective.eq_iff]
  constructor
  · intro heq
    have hslot := max_zero_sub_div_three_le_slotHybridExcess (lx + ly) ℓ v
    have h0 : 0 ≤ slotHybridExcess (lx + ly) ℓ v := (le_max_left _ _).trans hslot
    have h3 : (2 * ℓ - (lx + ly)) / 3 ≤ slotHybridExcess (lx + ly) ℓ v :=
      (le_max_right _ _).trans hslot
    have hν : ly - lx ≤ max 0 (ly - lx) := le_max_right _ _
    have hrew : lowBoundaryFreeOrder n lx ly ℓ - (1 - 1 / n) =
        (lx + ly - 2 * ℓ + (max 0 (ly - lx) - (ly - lx))) / (2 * n) := by
      unfold lowBoundaryFreeOrder
      field_simp
      ring
    have hM2ℓ : lx + ly = 2 * ℓ := by
      rcases lt_trichotomy (lx + ly) (2 * ℓ) with hlt | hEq | hgt
      · exfalso
        have hinv : 1 / (2 * n) < 1 / 6 := by
          rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
          linarith
        have hmul : (2 * ℓ - (lx + ly)) * (1 / (2 * n)) < (2 * ℓ - (lx + ly)) * (1 / 6) :=
          mul_lt_mul_of_pos_left hinv (by linarith)
        have hge : -(2 * ℓ - (lx + ly)) * (1 / (2 * n)) ≤
            lowBoundaryFreeOrder n lx ly ℓ - (1 - 1 / n) := by
          rw [hrew]
          have hpos_c : 0 ≤ (max 0 (ly - lx) - (ly - lx)) / (2 * n) :=
            div_nonneg (by linarith) (by linarith)
          have heq2 : (lx + ly - 2 * ℓ + (max 0 (ly - lx) - (ly - lx))) / (2 * n) =
              -(2 * ℓ - (lx + ly)) * (1 / (2 * n)) +
                (max 0 (ly - lx) - (ly - lx)) / (2 * n) := by ring
          linarith
        linarith
      · exact hEq
      · exfalso
        have hpos_low : 0 < lowBoundaryFreeOrder n lx ly ℓ - (1 - 1 / n) := by
          rw [hrew]
          exact div_pos (by linarith) (by linarith)
        linarith
    rw [hM2ℓ] at hrew
    have hsub0 : (2 * ℓ - 2 * ℓ + (max 0 (ly - lx) - (ly - lx))) / (2 * n) +
        slotHybridExcess (lx + ly) ℓ v / 2 = 0 := by linarith
    have hc_nonneg : 0 ≤ (max 0 (ly - lx) - (ly - lx)) / (2 * n) :=
      div_nonneg (by linarith) (by linarith)
    have hslot0 : slotHybridExcess (lx + ly) ℓ v = 0 := by linarith
    have hc0 : max 0 (ly - lx) = ly - lx := by
      have hdiv0 : (max 0 (ly - lx) - (ly - lx)) / (2 * n) = 0 := by linarith
      have hnum0 := (div_eq_zero_iff.mp hdiv0).resolve_right (by linarith)
      linarith
    have hlxly : lx ≤ ly := by
      have : 0 ≤ ly - lx := by rw [← hc0]; exact le_max_left _ _
      linarith
    obtain ⟨hℓ0, h2ℓv, hvM⟩ := (slotHybridExcess_eq_zero_iff (lx + ly) ℓ v).mp hslot0
    exact ⟨hlxly, hℓ0, hM2ℓ, by linarith⟩
  · rintro ⟨hlxly, hℓ0, hM2ℓ, hv⟩
    have hslot0 : slotHybridExcess (lx + ly) ℓ v = 0 :=
      (slotHybridExcess_eq_zero_iff (lx + ly) ℓ v).mpr ⟨hℓ0, by linarith, by linarith⟩
    rw [hslot0]
    unfold lowBoundaryFreeOrder
    rw [max_eq_right (by linarith : 0 ≤ ly - lx)]
    have hnum : 1 - lx - (ly - lx) / 2 + ℓ = 1 := by linarith
    rw [hnum]
    ring

/-! ### Multi-variable designs, Weyl-orbit circularity, and escape classification -/

/-- `2 × 2` matrix induced on `(∑ r_i, l)` by joint reflection `l ↦ 2(∑ r_i) − l` followed by
`k` individual row-variable summations `r_i ↦ 2 l' − r_i`. -/
def multiVarVoronoiMatrix (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4 * k - 1, -2 * k; 2, -1]

theorem multiVarVoronoiMatrix_det_and_trace (k : ℝ) :
    (multiVarVoronoiMatrix k).det = 1 ∧ (multiVarVoronoiMatrix k).trace = 4 * k - 2 := by
  refine ⟨?_, ?_⟩
  · rw [multiVarVoronoiMatrix, Matrix.det_fin_two_of]; ring
  · rw [multiVarVoronoiMatrix, Matrix.trace_fin_two_of]; ring

/-- Slotted, unbalanced, dual-penalty-free low boundary for `k` row variables of order `n` with
total column scales `Lx = ∑ lx_i`, `Ly = ∑ ly_i` and slot length `ℓ`. -/
def lowBoundaryDesignFree (k n Lx Ly ℓ : ℝ) : ℝ :=
  1 / 2 + k * (1 / 2 - 1 / n) + (2 * Lx + max 0 (Ly - Lx) - 2 * ℓ) / (2 * n)

/-- Effective twist exponent of `lowBoundaryDesignFree`. -/
def probeThetaDesignFree (k n Lx Ly ℓ : ℝ) : ℝ :=
  positiveFormTheta n (lowBoundaryDesignFree k n Lx Ly ℓ)

theorem lowBoundaryDesignFree_one (n lx ly ℓ : ℝ) :
    lowBoundaryDesignFree 1 n lx ly ℓ = lowBoundaryFreeOrder n lx ly ℓ := by
  unfold lowBoundaryDesignFree lowBoundaryFreeOrder
  ring

theorem lowBoundaryDesignFree_balanced_unslotted (k n : ℝ) :
    lowBoundaryDesignFree k n (1 / 2) (1 / 2) 0 = lowBoundaryDesign k n := by
  unfold lowBoundaryDesignFree lowBoundaryDesign
  rw [sub_self, max_self]
  ring

theorem probeThetaDesignFree_eq {n : ℝ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (k Lx Ly ℓ : ℝ) :
    probeThetaDesignFree k n Lx Ly ℓ =
      k * ((n - 2) / (n - 1)) + (Lx + Ly - 2 * ℓ + max 0 (Lx - Ly)) / (n - 1) := by
  have hsub : n - 1 ≠ 0 := sub_ne_zero.mpr hn1
  have hmax : 2 * Lx + max 0 (Ly - Lx) = Lx + Ly + max 0 (Lx - Ly) := by
    rcases le_total Lx Ly with h | h
    · rw [max_eq_right (by linarith : 0 ≤ Ly - Lx), max_eq_left (by linarith : Lx - Ly ≤ 0)]
      ring
    · rw [max_eq_left (by linarith : Ly - Lx ≤ 0), max_eq_right (by linarith : 0 ≤ Lx - Ly)]
      ring
  unfold probeThetaDesignFree positiveFormTheta lowBoundaryDesignFree
  rw [hmax]
  field_simp
  ring

/-- **Unconditional `k`-variable hybrid-slot floor.** Retaining `slotHybridExcess`, `k` row
variables of order `n ≥ 3` have effective twist exponent at least `k(n − 2)/(n − 1)` across all
`(Lx, Ly, ℓ, v) ∈ ℝ⁴` (`≥ n/(n − 1)` whenever `k ≥ 2` and `n ≥ 4`, `≥ 1` at `(2, 3)`, and `≥ 3/2`
at `(3, 3)`). -/
theorem mul_free_floor_le_probeThetaDesignHybridFree {n : ℝ} (hn : 3 ≤ n)
    (k Lx Ly ℓ v : ℝ) :
    k * ((n - 2) / (n - 1)) ≤
      positiveFormTheta n (lowBoundaryDesignFree k n Lx Ly ℓ +
        slotHybridExcess (Lx + Ly) ℓ v / 2) := by
  have hn0 : n ≠ 0 := by linarith
  have hsub : n - 1 ≠ 0 := by linarith
  have h1 := free_floor_le_probeThetaHybridFree hn Lx Ly ℓ v
  have hshift : positiveFormTheta n (lowBoundaryDesignFree k n Lx Ly ℓ +
        slotHybridExcess (Lx + Ly) ℓ v / 2) =
      probeThetaHybridFree n Lx Ly ℓ v + (k - 1) * ((n - 2) / (n - 1)) := by
    unfold probeThetaHybridFree positiveFormTheta lowBoundaryDesignFree lowBoundaryFreeOrder
    field_simp
    ring
  rw [hshift]
  linarith

theorem multi_row_hybridFree_outside_strip {k n : ℝ} (hk : 2 ≤ k) (hn : 4 ≤ n)
    (Lx Ly ℓ v : ℝ) :
    n / (n - 1) ≤
      positiveFormTheta n (lowBoundaryDesignFree k n Lx Ly ℓ +
        slotHybridExcess (Lx + Ly) ℓ v / 2) := by
  refine le_trans ?_ (mul_free_floor_le_probeThetaDesignHybridFree (by linarith) k Lx Ly ℓ v)
  have hsub : 0 < n - 1 := by linarith
  have h2 : 2 * ((n - 2) / (n - 1)) ≤ k * ((n - 2) / (n - 1)) :=
    mul_le_mul_of_nonneg_right hk (div_nonneg (by linarith) hsub.le)
  have h4 : n / (n - 1) ≤ 2 * ((n - 2) / (n - 1)) := by
    rw [ ← mul_div_assoc, div_le_div_iff_of_pos_right hsub]
    linarith
  exact h4.trans h2

/-- Iterated reflection-summation description `ρ_{row} ∘ (ρ_{sum} ∘ ρ_{row})^m` of `(M, 1)`:
positive index scale without dual excess holds precisely on `(2m + 1)/(2m + 2) < M ≤ 1`. -/
theorem reflect_iterate_sum_reflect (m : ℕ) (M : ℝ) :
    reflectScale ((sumScale ∘ reflectScale)^[m] (M, 1)) =
      ((2 * m + 1) * M - 2 * m, (2 * m + 2) * M - (2 * m + 1)) := by
  rw [iterate_sumScale_reflectScale]
  simp only [reflectScale, Prod.mk.injEq]
  constructor <;> ring

/-- General-order relative size of the principal `n`-th-power twists up to dual scale `T`,
recovering `principalExcessOrder n M ℓ β` upon subtracting the summation window `M − 1 − ℓ` at
`T = (sumScale (M, 1 + ℓ)).1 = 2 + 2ℓ − M`. -/
def principalRelativeSizeOrder (n T ℓ β : ℝ) : ℝ :=
  2 * β + ℓ - 1 - (1 - 1 / n) * T

theorem principalRelativeSizeOrder_sub_window {n : ℝ} (hn0 : n ≠ 0) (M ℓ β : ℝ) :
    principalRelativeSizeOrder n (sumScale (M, 1 + ℓ)).1 ℓ β - (M - 1 - ℓ) =
      principalExcessOrder n M ℓ β := by
  unfold principalRelativeSizeOrder sumScale principalExcessOrder
  field_simp
  ring

/-- Complete escape model incorporating `k` row variables, arbitrary Voronoi dual scale `v`,
hybrid slot excess, and pre-Cauchy–Schwarz bilinear row-column saving `sBilin`. -/
def probeThetaEscapeModel (k n Lx Ly ℓ v sBilin : ℝ) : ℝ :=
  positiveFormTheta n
    (lowBoundaryDesignFree k n Lx Ly ℓ + slotHybridExcess (Lx + Ly) ℓ v / 2 - sBilin)

/-- **Exact classification of escape below `(n − 2)/(n − 1)`.** For `k ≥ 1` and `n ≥ 3`,
`probeThetaEscapeModel` is bounded below by `(n − 2)/(n − 1) − (2n/(n − 1)) sBilin` across all
`(Lx, Ly, ℓ, v, sBilin) ∈ ℝ⁵`: crossing `< (n − 2)/(n − 1)` forces strictly positive
pre-Cauchy–Schwarz bilinear saving `sBilin > 0`. -/
theorem escape_below_free_floor_bound {k n : ℝ} (hk : 1 ≤ k) (hn : 3 ≤ n)
    (Lx Ly ℓ v sBilin : ℝ) :
    (n - 2) / (n - 1) - 2 * n / (n - 1) * sBilin ≤
      probeThetaEscapeModel k n Lx Ly ℓ v sBilin := by
  have hbase := mul_free_floor_le_probeThetaDesignHybridFree hn k Lx Ly ℓ v
  have hshift : probeThetaEscapeModel k n Lx Ly ℓ v sBilin =
      positiveFormTheta n (lowBoundaryDesignFree k n Lx Ly ℓ +
        slotHybridExcess (Lx + Ly) ℓ v / 2) - 2 * n / (n - 1) * sBilin := by
    unfold probeThetaEscapeModel positiveFormTheta
    ring
  have hk1 : (n - 2) / (n - 1) ≤ k * ((n - 2) / (n - 1)) := by
    simpa using mul_le_mul_of_nonneg_right hk (div_nonneg (by linarith) (by linarith))
  linarith

theorem sBilin_pos_of_lt_free_floor {k n Lx Ly ℓ v sBilin : ℝ} (hk : 1 ≤ k) (hn : 3 ≤ n)
    (hlt : probeThetaEscapeModel k n Lx Ly ℓ v sBilin < (n - 2) / (n - 1)) :
    0 < sBilin := by
  have hbound := escape_below_free_floor_bound hk hn Lx Ly ℓ v sBilin
  have hcoef : 0 < 2 * n / (n - 1) := div_pos (by linarith) (by linarith)
  have hmul : 0 < 2 * n / (n - 1) * sBilin := by linarith
  exact (mul_pos_iff_of_pos_left hcoef).mp hmul

/-- Exact pre-Cauchy–Schwarz bilinear savings required to reach `σ₀ = 3/4`
(`θ = n / (2(n − 1))`, `3/5` at `n = 6`, requiring `sBilin ≥ 1/4 − 1/n`) and the critical line
`σ₀ = 1/2` (`θ = 0`, requiring `sBilin ≥ 1/2 − 1/n`). -/
theorem sBilin_thresholds {k n Lx Ly ℓ v sBilin : ℝ} (hk : 1 ≤ k) (hn : 3 ≤ n) :
    (probeThetaEscapeModel k n Lx Ly ℓ v sBilin ≤ n / (2 * (n - 1)) →
      1 / 4 - 1 / n ≤ sBilin) ∧
    (probeThetaEscapeModel k n Lx Ly ℓ v sBilin ≤ 0 →
      1 / 2 - 1 / n ≤ sBilin) := by
  have hn0 : n ≠ 0 := by linarith
  have hsub : 0 < n - 1 := by linarith
  have hsub_ne : n - 1 ≠ 0 := hsub.ne'
  have hbound := escape_below_free_floor_bound hk hn Lx Ly ℓ v sBilin
  refine ⟨fun h34 => ?_, fun h12 => ?_⟩
  · have hineq : (n - 2) / (n - 1) - n / (2 * (n - 1)) ≤ 2 * n / (n - 1) * sBilin := by linarith
    have hlhs : (n - 2) / (n - 1) - n / (2 * (n - 1)) =
        2 * n / (n - 1) * (1 / 4 - 1 / n) := by
      field_simp
      ring
    rw [hlhs] at hineq
    exact le_of_mul_le_mul_left hineq (div_pos (by linarith) hsub)
  · have hineq : (n - 2) / (n - 1) ≤ 2 * n / (n - 1) * sBilin := by linarith
    have hlhs : (n - 2) / (n - 1) = 2 * n / (n - 1) * (1 / 2 - 1 / n) := by
      field_simp
      ring
    rw [hlhs] at hineq
    exact le_of_mul_le_mul_left hineq (div_pos (by linarith) hsub)

end

end GaloisForLFunctions.FamilyContinuationTheory.Budget
