import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair

/-!
# The degree filtration of a curve is its window filtration

Over `ℚ` no degree certifies the Hodge index for all configurations (`exists_hidden_at_degree`).
On the scaling surface of a curve datum the degree filtration is decided by **one** Frobenius
window: with `L = log q`,

    hodgeDefectAt (curveConfig) a = 0   if the window Gram matrix of size ⌈2a/L⌉ is positive
                                        semidefinite,
                                  = ⊤   otherwise                     (`hodgeDefectAt_curveConfig`).

* **Positivity below the threshold** (`re_W_curveConfig_nonneg_of_window`). By the explicit formula
  (`W_curveConfig`), `W(f, f) = L Σ_m t_{|m|} ∫ f(u) conj f(u − mL) du`. Cutting the line into cells
  of length `L` (`integral_eq_sum_cells`) gives `L ∫_0^L Σ_{j,k} t_{|j−k|} F_j(s) conj F_k(s) ds` with
  samples `F_j(s) = f(s + jL)`; a test supported in `[−a, a]` has its nonzero samples in a window of
  length `⌈2a/L⌉` (`window_of_support`), so the integrand is a value of the window Gram form
  (`re_sum_toeplitzDensity_nonneg`).
* **Infinite defect above it** (`hodgeDefectAt_curveConfig_eq_top`). A negative vector `v` of the
  window gives tests `Σ_b conj(v_b) g(· − x_i − bL)` on a narrow bump `g`; the slack
  `2a − (n − 1)L > 0` holds `r` offsets `x_i` that never meet modulo `L` (`sep_offsets`), so the
  tests are `W`-orthogonal (`W_curveConfig_translate_eq_zero`) and each has square
  `L ‖g‖² v* G v < 0`: the defect exceeds every `r`.

So the Hodge defect of a curve jumps from `0` straight to `∞`, at the degree where the first window
acquires a negative square; it vanishes up to degree `L/2` for every curve
(`hodgeDefectAt_curveConfig_eq_zero_of_le`), and from the window `2g` on it is `0` or `∞` according
as the curve is pure or not (`hodgeDefectAt_curveConfig_of_card_le`). For the golden fake curve the
jump is at `log 5 / 2` (`goldenDatum_hodgeDefectAt`).
-/

open Complex MeasureTheory Finset
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Cells and windows -/

/-- A continuous function with `tsupport ⊆ [−a, a]` vanishes off the open interval. -/
theorem mem_Ioo_of_ne_zero {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ}
    (hfs : tsupport f ⊆ Set.Icc (-a) a) {u : ℝ} (hu : f u ≠ 0) : -a < u ∧ u < a := by
  have hmem : ∀ v, f v ≠ 0 → v ∈ Set.Icc (-a) a := fun v hv => hfs (subset_tsupport _ hv)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne_fun hf continuous_const) u hu
  have h1 := hmem (u + ε / 2) (hball (by
    rw [Metric.mem_ball, Real.dist_eq, show u + ε / 2 - u = ε / 2 by ring,
      abs_of_pos (half_pos hε)]
    linarith))
  have h2 := hmem (u - ε / 2) (hball (by
    rw [Metric.mem_ball, Real.dist_eq, show u - ε / 2 - u = -(ε / 2) by ring, abs_neg,
      abs_of_pos (half_pos hε)]
    linarith))
  exact ⟨by linarith [h2.1], by linarith [h1.2]⟩

/-- **Cell decomposition.** If `h` is continuous and vanishes outside `[−NL, NL]`, then
`∫ h = Σ_{−N ≤ j < N} ∫_0^L h(s + jL) ds`. -/
theorem integral_eq_sum_cells {h : ℝ → ℂ} (hh : Continuous h) {L : ℝ} (hL : 0 < L) (N : ℕ)
    (hsupp : ∀ u, h u ≠ 0 → -(N * L) ≤ u ∧ u ≤ N * L) :
    ∫ u, h u = ∑ j ∈ Ico (-(N : ℤ)) N, ∫ s in (0 : ℝ)..L, h (s + j * L) := by
  have hNL : -(N * L) ≤ N * L := by nlinarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N]
  have h1 : ∫ u, h u = ∫ u in -(N * L)..(N * L), h u := by
    rw [intervalIntegral.integral_of_le hNL, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    by_contra hne
    exact hu ⟨(hsupp u hne).1, (hsupp u hne).2⟩
  have hadj : ∑ k ∈ range (2 * N), ∫ x in ((k : ℝ) - N) * L..(((k + 1 : ℕ) : ℝ) - N) * L, h x =
      ∫ x in (((0 : ℕ) : ℝ) - N) * L..(((2 * N : ℕ) : ℝ) - N) * L, h x :=
    intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => ((k : ℝ) - N) * L)
      (fun k _ => hh.intervalIntegrable _ _)
  rw [show (((2 * N : ℕ) : ℝ) - N) * L = N * L by push_cast; ring,
    show (((0 : ℕ) : ℝ) - N) * L = -(N * L) by push_cast; ring] at hadj
  rw [h1, ← hadj]
  refine Finset.sum_nbij' (fun k => (k : ℤ) - N) (fun j => (j + N).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [coe_range, Set.mem_Iio] at hk
    simp only [coe_Ico, Set.mem_Ico]
    omega
  · intro j hj
    simp only [coe_Ico, Set.mem_Ico] at hj
    simp only [coe_range, Set.mem_Iio]
    omega
  · intro k _
    omega
  · intro j hj
    simp only [coe_Ico, Set.mem_Ico] at hj
    omega
  · intro k _
    rw [intervalIntegral.integral_comp_add_right h]
    congr 1 <;> push_cast <;> ring

/-- **Window of a sampled test.** If `tsupport f ⊆ [−a, a]`, the nonzero samples `f(s + jL)` have
`⌈(−a − s)/L⌉ ≤ j < ⌈(−a − s)/L⌉ + ⌈2a/L⌉`. -/
theorem window_of_support {f : ℝ → ℂ} (hf : Continuous f) {a L : ℝ} (hL : 0 < L)
    (hfs : tsupport f ⊆ Set.Icc (-a) a) (s : ℝ) {j : ℤ} (hj : f (s + j * L) ≠ 0) :
    ⌈(-a - s) / L⌉ ≤ j ∧ j < ⌈(-a - s) / L⌉ + ⌈2 * a / L⌉₊ := by
  obtain ⟨h1, h2⟩ := mem_Ioo_of_ne_zero hf hfs hj
  have hlow : (-a - s) / L < j := by rw [div_lt_iff₀ hL]; linarith
  refine ⟨Int.ceil_le.mpr hlow.le, ?_⟩
  have hup : (j : ℝ) < (a - s) / L := by rw [lt_div_iff₀ hL]; linarith
  have hc1 : (-a - s) / L ≤ ⌈(-a - s) / L⌉ := Int.le_ceil _
  have hc2 : 2 * a / L ≤ ⌈2 * a / L⌉₊ := Nat.le_ceil _
  have hsplit : (a - s) / L = (-a - s) / L + 2 * a / L := by ring
  have : (j : ℝ) < (⌈(-a - s) / L⌉ : ℤ) + ((⌈2 * a / L⌉₊ : ℕ) : ℝ) := by linarith
  exact_mod_cast this

/-- A sum over `S` of terms supported where `F ≠ 0` is a sum over a window `j₀, …, j₀ + n − 1`
containing the support of `F`. -/
theorem sum_eq_sum_window (S : Finset ℤ) (F U : ℤ → ℂ) (j₀ : ℤ) (n : ℕ)
    (hS : ∀ j, F j ≠ 0 → j ∈ S) (hwin : ∀ j, F j ≠ 0 → j₀ ≤ j ∧ j < j₀ + n)
    (hU : ∀ j, U j ≠ 0 → F j ≠ 0) :
    ∑ j ∈ S, U j = ∑ b : Fin n, U (j₀ + b) := by
  symm
  refine Finset.sum_bij_ne_zero (fun b _ _ => j₀ + b) (fun b _ hb => hS _ (hU _ hb))
    (fun b _ _ c _ _ h => Fin.ext (by omega)) (fun j _ hj => ?_) (fun _ _ _ => rfl)
  obtain ⟨h1, h2⟩ := hwin j (hU j hj)
  have hj' : j₀ + (((j - j₀).toNat : ℕ) : ℤ) = j := by omega
  exact ⟨⟨(j - j₀).toNat, by omega⟩, Finset.mem_univ _, by simpa [hj'] using hj, hj'⟩

/-- Two offsets `2iw`, `2jw` (`i ≠ j < r`) stay more than `w` apart modulo `L` when
`(2r − 1) w < L`. -/
theorem sep_offsets {L w : ℝ} (hw : 0 < w) (hL : 0 < L) {r : ℕ} (hrL : (2 * r - 1) * w < L)
    {i j : ℕ} (hi : i < r) (hj : j < r) (hij : i ≠ j) (k : ℤ) :
    w < |k * L - 2 * ((i : ℝ) - j) * w| := by
  have hi' : (i : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hj' : (j : ℝ) + 1 ≤ r := by exact_mod_cast hj
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    rw [lt_abs]; right
    nlinarith [mul_le_mul_of_nonneg_right hk' hL.le]
  · rcases Nat.lt_or_gt_of_ne hij with h | h
    · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [lt_abs]; left
      push_cast; nlinarith
    · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [lt_abs]; right
      push_cast; nlinarith
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    rw [lt_abs]; left
    nlinarith [mul_le_mul_of_nonneg_right hk' hL.le]

/-- A diagonal matrix with a constant entry of negative real part is negative definite. -/
theorem card_le_negIndex_diagonal_const {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℂ}
    (hd : d.re < 0) : Fintype.card κ ≤ hermNegIndex (Matrix.diagonal fun _ : κ => d) := by
  have hpd : IsPosDefOn (-(Matrix.diagonal fun _ : κ => d)) ⊤ := by
    intro x _ hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hq : hermQuad (Matrix.diagonal fun _ : κ => d) x = d.re * ∑ j, Complex.normSq (x j) := by
      simp only [hermQuad, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def,
        Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show conj (x j) * (d * x j) = d * ((Complex.normSq (x j) : ℝ) : ℂ) by
        rw [Complex.normSq_eq_conj_mul_self]; ring, Complex.re_mul_ofReal]
    have hpos : 0 < ∑ j, Complex.normSq (x j) :=
      lt_of_lt_of_le (Complex.normSq_pos.mpr hi)
        (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
    rw [hermQuad_neg, hq]
    nlinarith
  have h := finrank_le_posIndex hpd
  rwa [finrank_top, Module.finrank_fintype_fun_eq_card] at h

/-- **Congruence of a block-diagonal matrix** by one vector placed in each block: the result is the
scalar matrix `κ v* S v`. -/
theorem block_congr {r n : ℕ} (G : Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ)
    (S : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ)
    (hG : ∀ p p', G p p' = if p.1 = p'.1 then κ * S p.2 p'.2 else 0) (v : Fin n → ℂ) :
    Matrix.of (fun (i : Fin r) (p : Fin r × Fin n) => if p.1 = i then star (v p.2) else 0) * G *
        (Matrix.of fun (i : Fin r) (p : Fin r × Fin n) => if p.1 = i then star (v p.2) else 0)ᴴ =
      Matrix.diagonal fun _ => κ * (star v ⬝ᵥ S *ᵥ v) := by
  have hCG : ∀ i p', (Matrix.of (fun (i : Fin r) (p : Fin r × Fin n) =>
      if p.1 = i then star (v p.2) else 0) * G) i p' =
        if p'.1 = i then κ * ∑ b, star (v b) * S b p'.2 else 0 := by
    intro i p'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [Matrix.of_apply, hG]
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    by_cases h : p'.1 = i
    · simp [h, Finset.mul_sum, mul_left_comm]
    · simp [h, Ne.symm h]
  ext i i'
  rw [Matrix.mul_apply]
  simp only [hCG, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  by_cases h : i = i'
  · subst h
    simp only [if_true, star_star, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · simp [h]

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-! ### The Toeplitz form of the samples -/

/-- **The Toeplitz form of a windowed sample vector is a window value.** If the nonzero coordinates
of `F` lie in `S` and in a window of length `n`, and the window Gram matrix of size `n` is positive
semidefinite, then `Re Σ_{j,k ∈ S} t_{|j−k|} F_j conj F_k ≥ 0`. -/
theorem re_toeplitz_nonneg (S : Finset ℤ) (F : ℤ → ℂ) (j₀ : ℤ) {n : ℕ}
    (hS : ∀ j, F j ≠ 0 → j ∈ S) (hwin : ∀ j, F j ≠ 0 → j₀ ≤ j ∧ j < j₀ + n)
    (hpsd : ∀ x : Fin n → ℂ, 0 ≤ hermQuad (D.spanGram n) x) :
    0 ≤ (∑ j ∈ S, ∑ k ∈ S, (D.trace (j - k).natAbs : ℂ) * F j * conj (F k)).re := by
  have hrow : ∀ j, ∑ k ∈ S, (D.trace (j - k).natAbs : ℂ) * F j * conj (F k) =
      ∑ c : Fin n, (D.trace (j - (j₀ + c)).natAbs : ℂ) * F j * conj (F (j₀ + c)) := fun j =>
    sum_eq_sum_window S F _ j₀ n hS hwin fun k hk hFk => hk (by rw [hFk]; simp)
  rw [sum_eq_sum_window S F _ j₀ n hS hwin fun j hj hFj =>
    hj (Finset.sum_eq_zero fun k _ => by rw [hFj]; ring)]
  simp only [hrow]
  convert hpsd (fun b => conj (F (j₀ + b))) using 1
  simp only [hermQuad, dotProduct, Matrix.mulVec, spanGram, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [show j₀ + ((b : ℕ) : ℤ) - (j₀ + ((c : ℕ) : ℤ)) = ((b : ℕ) : ℤ) - ((c : ℕ) : ℤ) by ring,
    natAbs_sub_eq_dist]
  ring

/-- The Toeplitz density `Σ_{m ∈ M} t_{|m|} f(u) conj f(u − m log q)`: the explicit formula with
its lags truncated to `M`, before integration. -/
def toeplitzDensity (M : Finset ℤ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ m ∈ M, (D.trace m.natAbs : ℂ) * (f u * conj (f (u - m * Real.log D.q)))

theorem continuous_toeplitzDensity (M : Finset ℤ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (D.toeplitzDensity M f) := by
  unfold toeplitzDensity
  exact continuous_finsetSum _ fun m _ => continuous_const.mul
    (hf.mul (Complex.continuous_conj.comp (hf.comp (continuous_sub_right _))))

/-- **On a cell the Toeplitz density is a window value.** For `s ∈ [0, log q]` the sum of the
density over the cell translates `s + j log q` is the Toeplitz form of the samples
`f(s + j log q)`, which live in a window of length `⌈2a / log q⌉`. -/
theorem re_sum_toeplitzDensity_nonneg {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ}
    (hfs : tsupport f ⊆ Set.Icc (-a) a) {N : ℕ} (haN : a ≤ N * Real.log D.q)
    (hpsd : ∀ x, 0 ≤ hermQuad (D.spanGram ⌈2 * a / Real.log D.q⌉₊) x) {s : ℝ}
    (hs : s ∈ Set.Icc 0 (Real.log D.q)) :
    0 ≤ (∑ j ∈ Ico (-(N : ℤ)) N,
      D.toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) f (s + j * Real.log D.q)).re := by
  have hL := D.log_q_pos
  -- the samples live in the cells `−N ≤ j < N`
  have hS : ∀ j : ℤ, f (s + j * Real.log D.q) ≠ 0 → j ∈ Ico (-(N : ℤ)) N := by
    intro j hj
    obtain ⟨h1, h2⟩ := mem_Ioo_of_ne_zero hf hfs hj
    have hup : (j : ℝ) * Real.log D.q < N * Real.log D.q := by linarith [hs.1]
    have hlo : (-(N : ℝ) - 1) * Real.log D.q < j * Real.log D.q := by linarith [hs.2]
    have hup' : j < (N : ℤ) := by exact_mod_cast lt_of_mul_lt_mul_right hup hL.le
    have hlo' : -(N : ℤ) - 1 < j := by exact_mod_cast lt_of_mul_lt_mul_right hlo hL.le
    exact Finset.mem_Ico.mpr ⟨by omega, hup'⟩
  have key := D.re_toeplitz_nonneg (Ico (-(N : ℤ)) N) (fun j : ℤ => f (s + j * Real.log D.q))
    ⌈(-a - s) / Real.log D.q⌉ hS (fun j hj => window_of_support hf hL hfs s hj) hpsd
  convert key using 2
  refine Finset.sum_congr rfl fun j hj => ?_
  -- reindex the lags `m = j − k`
  have himg : (Ico (-(N : ℤ)) N).image (fun k => j - k) ⊆ Icc (-(2 * N : ℤ)) (2 * N) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_Ico] at hk hj
    rw [Finset.mem_Icc]
    omega
  have hz : ∀ m ∈ Icc (-(2 * N : ℤ)) (2 * N), m ∉ (Ico (-(N : ℤ)) N).image (fun k => j - k) →
      (D.trace m.natAbs : ℂ) * (f (s + j * Real.log D.q) *
        conj (f (s + j * Real.log D.q - m * Real.log D.q))) = 0 := by
    intro m _ hm
    have h0 : f (s + j * Real.log D.q - m * Real.log D.q) = 0 := by
      by_contra hne
      refine hm (Finset.mem_image.mpr ⟨j - m, hS (j - m) ?_, by ring⟩)
      rwa [show s + ((j - m : ℤ) : ℝ) * Real.log D.q = s + j * Real.log D.q - m * Real.log D.q by
        push_cast; ring]
    rw [h0, map_zero, mul_zero, mul_zero]
  calc D.toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) f (s + j * Real.log D.q)
      = ∑ m ∈ (Ico (-(N : ℤ)) N).image (fun k => j - k), (D.trace m.natAbs : ℂ) *
          (f (s + j * Real.log D.q) * conj (f (s + j * Real.log D.q - m * Real.log D.q))) :=
        (Finset.sum_subset himg hz).symm
    _ = ∑ k ∈ Ico (-(N : ℤ)) N, (D.trace (j - k).natAbs : ℂ) *
          (f (s + j * Real.log D.q) *
            conj (f (s + j * Real.log D.q - ((j - k : ℤ) : ℝ) * Real.log D.q))) :=
        Finset.sum_image fun k _ k' _ h => by simpa using h
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show s + j * Real.log D.q - ((j - k : ℤ) : ℝ) * Real.log D.q =
          s + k * Real.log D.q by push_cast; ring]
        ring

/-! ### Positivity below the threshold -/

/-- **Positivity below the threshold.** If the Frobenius window of size `⌈2a / log q⌉` is positive
semidefinite, Weil's form of the curve is positive on every `C²` test supported in `[−a, a]`. -/
theorem re_W_curveConfig_nonneg_of_window {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ}
    (hfs : tsupport f ⊆ Set.Icc (-a) a)
    (hpsd : ∀ x, 0 ≤ hermQuad (D.spanGram ⌈2 * a / Real.log D.q⌉₊) x) :
    0 ≤ ((D.curveConfig hD).W f f).re := by
  have hL := D.log_q_pos
  have hfc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hfs
  obtain ⟨N, haN⟩ : ∃ N : ℕ, a ≤ N * Real.log D.q :=
    ⟨⌈a / Real.log D.q⌉₊, (div_le_iff₀ hL).mp (Nat.le_ceil _)⟩
  -- the autocorrelation lives in `[−2a, 2a]`, so only the lags `|m| ≤ 2N` occur
  have hfs2 : tsupport f ⊆ Set.Icc (-(2 * a / 2)) (2 * a / 2) := by
    rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have hKz : ∀ m : ℤ, m ∉ Icc (-(2 * N : ℤ)) (2 * N) →
      EF.weilTest f f (m * Real.log D.q) = 0 := by
    intro m hm
    by_contra hne
    have hmem := EF.tsupport_weilTest_subset hfs2 hfs2 (subset_tsupport _ hne)
    simp only [Finset.mem_Icc, not_and_or, not_le] at hm
    rcases hm with h | h
    · have h' : (m : ℝ) ≤ -(2 * N) - 1 := by
        exact_mod_cast (show m ≤ -(2 * (N : ℤ)) - 1 by omega)
      nlinarith [hmem.1, mul_le_mul_of_nonneg_right h' hL.le]
    · have h' : 2 * (N : ℝ) + 1 ≤ m := by
        exact_mod_cast (show 2 * (N : ℤ) + 1 ≤ m by omega)
      nlinarith [hmem.2, mul_le_mul_of_nonneg_right h' hL.le]
  have hfin : ∀ i, ∑' m : ℤ, EF.weilTest f f (m * Real.log D.q) * D.β i ^ m =
      ∑ m ∈ Icc (-(2 * N : ℤ)) (2 * N), EF.weilTest f f (m * Real.log D.q) * D.β i ^ m :=
    fun i => tsum_eq_sum fun m hm => by rw [hKz m hm, zero_mul]
  have hW : (D.curveConfig hD).W f f = (Real.log D.q : ℂ) *
      ∑ m ∈ Icc (-(2 * N : ℤ)) (2 * N),
        (D.trace m.natAbs : ℂ) * EF.weilTest f f (m * Real.log D.q) := by
    rw [D.W_curveConfig hD hf hfc hf.continuous hfc, ← Finset.mul_sum]
    congr 1
    simp only [hfin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, sum_zpow_eq_trace, mul_comm]
  -- the truncated explicit formula is the integral of the Toeplitz density
  have hint : ∀ m : ℤ, Integrable fun u =>
      (D.trace m.natAbs : ℂ) * (f u * conj (f (u - m * Real.log D.q))) := fun m =>
    ((hf.continuous.mul (Complex.continuous_conj.comp
      (hf.continuous.comp (continuous_sub_right _)))).integrable_of_hasCompactSupport
        hfc.mul_right).const_mul _
  have hsum : ∑ m ∈ Icc (-(2 * N : ℤ)) (2 * N),
      (D.trace m.natAbs : ℂ) * EF.weilTest f f (m * Real.log D.q) =
        ∫ u, D.toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) f u := by
    simp only [toeplitzDensity]
    rw [integral_finsetSum _ fun m _ => hint m]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [RHTower.weilTest_apply, integral_const_mul]
  have hsupp : ∀ u, D.toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) f u ≠ 0 →
      -(N * Real.log D.q) ≤ u ∧ u ≤ N * Real.log D.q := by
    intro u hu
    have hfu : f u ≠ 0 := by
      intro h0
      apply hu
      unfold toeplitzDensity
      exact Finset.sum_eq_zero fun m _ => by rw [h0, zero_mul, mul_zero]
    obtain ⟨h1, h2⟩ := mem_Ioo_of_ne_zero hf.continuous hfs hfu
    constructor <;> linarith
  have hcont := D.continuous_toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) hf.continuous
  have hswap : ∑ j ∈ Ico (-(N : ℤ)) N, ∫ s in (0 : ℝ)..Real.log D.q,
      D.toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) f (s + j * Real.log D.q) =
        ∫ s in (0 : ℝ)..Real.log D.q, ∑ j ∈ Ico (-(N : ℤ)) N,
          D.toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) f (s + j * Real.log D.q) :=
    (intervalIntegral.integral_finsetSum fun j _ =>
      (hcont.comp (continuous_add_const _)).intervalIntegrable _ _).symm
  have hII : IntervalIntegrable (fun s => ∑ j ∈ Ico (-(N : ℤ)) N,
      D.toeplitzDensity (Icc (-(2 * N : ℤ)) (2 * N)) f (s + j * Real.log D.q))
        volume 0 (Real.log D.q) :=
    (continuous_finsetSum _ fun j _ =>
      hcont.comp (continuous_add_const _)).intervalIntegrable _ _
  rw [hW, hsum, integral_eq_sum_cells hcont hL N hsupp, hswap, Complex.re_ofReal_mul]
  refine mul_nonneg hL.le ?_
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hII]
  exact intervalIntegral.integral_nonneg hL.le fun s hs => by
    simpa using D.re_sum_toeplitzDensity_nonneg hf.continuous hfs haN hpsd hs

/-! ### Infinite defect above the threshold -/

/-- Weil's form of two translates of one test, by the explicit formula. -/
theorem W_curveConfig_translate {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x y : ℝ) :
    (D.curveConfig hD).W (translate x g) (translate y g) =
      ∑ i, Real.log D.q * ∑' m : ℤ, EF.weilTest g g (m * Real.log D.q - (x - y)) * D.β i ^ m := by
  rw [D.W_curveConfig hD (translate_contDiff hg _) (translate_hasCompactSupport hgc _)
    (translate_contDiff hg _).continuous (translate_hasCompactSupport hgc _)]
  simp only [weilTest_translate]

/-- Translates of a narrow test along a shifted `q`-tower: the Frobenius span Gram entries. -/
theorem W_curveConfig_translate_shift {g : ℝ → ℂ} {A : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(A / 2)) (A / 2)) (hAL : A < Real.log D.q) (x : ℝ) (k l : ℕ) :
    (D.curveConfig hD).W (translate (x + k * Real.log D.q) g)
        (translate (x + l * Real.log D.q) g) =
      ((Real.log D.q * ∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) * (D.trace (Nat.dist k l) : ℂ) := by
  have hgc : HasCompactSupport g := RHTower.hasCompactSupport_of_tsupport_subset_Icc hgs
  rw [D.W_curveConfig_translate hD hg hgc,
    show x + k * Real.log D.q - (x + l * Real.log D.q) = k * Real.log D.q - l * Real.log D.q by
      ring,
    ← D.W_curveConfig_translate hD hg hgc]
  exact D.W_curveConfig_translate_narrow hD hg hgs hAL k l

/-- **Offsets that never meet do not interact.** If the offset difference `x − y` stays more than
`w` away from `log q · ℤ` and `g` lives in `[−w/2, w/2]`, the translates are `W`-orthogonal. -/
theorem W_curveConfig_translate_eq_zero {g : ℝ → ℂ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) {x y : ℝ}
    (hsep : ∀ k : ℤ, w < |k * Real.log D.q - (x - y)|) :
    (D.curveConfig hD).W (translate x g) (translate y g) = 0 := by
  have hgc : HasCompactSupport g := RHTower.hasCompactSupport_of_tsupport_subset_Icc hgs
  rw [D.W_curveConfig_translate hD hg hgc]
  have hz : ∀ m : ℤ, EF.weilTest g g (m * Real.log D.q - (x - y)) = 0 := fun m => by
    by_contra hne
    exact absurd (abs_le.mpr (EF.tsupport_weilTest_subset hgs hgs (subset_tsupport _ hne)))
      (not_le.mpr (hsep m))
  simp [hz]

/-- A narrow bump: a `C²` test supported in `[−w/2, w/2]` with positive energy. -/
theorem exists_narrow_test {w : ℝ} (hw : 0 < w) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2) ∧
      0 < ∫ u, ‖g u‖ ^ 2 := by
  have hw2 : 0 < w / 2 := half_pos hw
  set ψ := smallBump (w / 2) hw2
  refine ⟨bumpTest (w / 2) hw2 0, bumpTest_contDiff hw2 0, ?_, ?_⟩
  · refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hu' : u - 0 ∈ Function.support ψ := fun h => hu (by simp [bumpTest, ψ, h])
    rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, sub_zero] at hu'
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  · have h0 : ψ 0 = 1 := ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)
    exact ((bumpTest_contDiff hw2 0).continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      ((bumpTest_hasCompactSupport hw2 0).comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
      (fun u => sq_nonneg _) (show (fun u => ‖bumpTest (w / 2) hw2 0 u‖ ^ 2) 0 ≠ 0 by
        simp [bumpTest, ψ, h0])

/-- **Infinite defect above the threshold.** If the Frobenius window of size `⌈2a / log q⌉` has a
negative square, the Hodge defect of the curve at degree `a` is infinite. -/
theorem hodgeDefectAt_curveConfig_eq_top {a : ℝ} {v : Fin ⌈2 * a / Real.log D.q⌉₊ → ℂ}
    (hv : hermQuad (D.spanGram ⌈2 * a / Real.log D.q⌉₊) v < 0) :
    hodgeDefectAt (D.curveConfig hD) a = ⊤ := by
  classical
  have hL := D.log_q_pos
  set n := ⌈2 * a / Real.log D.q⌉₊ with hn
  -- the window is nonempty, so `(n − 1) log q < 2a`
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      have : hermQuad (D.spanGram n) v = 0 := by
        haveI : IsEmpty (Fin n) := by rw [h0]; infer_instance
        simp [hermQuad, dotProduct]
      linarith
    · exact h0
  have hpos : 0 < 2 * a / Real.log D.q := by
    by_contra h
    push_neg at h
    have : n = 0 := Nat.ceil_eq_zero.mpr h
    omega
  have hgap : ((n : ℝ) - 1) * Real.log D.q < 2 * a := by
    have h1 := Nat.ceil_lt_add_one hpos.le
    rw [← hn] at h1
    have : (n : ℝ) - 1 < 2 * a / Real.log D.q := by linarith
    rwa [lt_div_iff₀ hL] at this
  refine top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun r _ => ?_)
  -- `r` disjoint copies of the window, offset by multiples of `2w` inside the slack
  obtain ⟨η, hη0, hηg, hηL⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 2 * a - ((n : ℝ) - 1) * Real.log D.q ∧
      η ≤ Real.log D.q :=
    ⟨min _ _, lt_min (by linarith) hL, min_le_left _ _, min_le_right _ _⟩
  have hr0 : (0 : ℝ) < 2 * r + 2 := by positivity
  obtain ⟨w, hw0, hwη⟩ : ∃ w : ℝ, 0 < w ∧ (2 * r + 2) * w ≤ η :=
    ⟨η / (2 * r + 2), div_pos hη0 hr0, le_of_eq (by field_simp)⟩
  have hrw : (0 : ℝ) ≤ r * w := mul_nonneg (Nat.cast_nonneg r) hw0.le
  have hrL : (2 * r - 1) * w < Real.log D.q := by nlinarith
  have hwL : w < Real.log D.q := by nlinarith
  obtain ⟨g, hg, hgs, hg0⟩ := exists_narrow_test hw0
  have hgc : HasCompactSupport g := RHTower.hasCompactSupport_of_tsupport_subset_Icc hgs
  have hκ : 0 < Real.log D.q * ∫ u, ‖g u‖ ^ 2 := mul_pos hL hg0
  obtain ⟨t, ht⟩ : ∃ t : Fin r × Fin n → testSpace, ∀ p, (t p : ℝ → ℂ) =
      translate (-a + w / 2 + 2 * ((p.1 : ℕ) : ℝ) * w + ((p.2 : ℕ) : ℝ) * Real.log D.q) g :=
    ⟨fun p => translateTest hg hgc _, fun _ => rfl⟩
  -- the Gram matrix of the offset translates is block diagonal
  have hG : ∀ p p', zeroGram (D.curveConfig hD) (fun p => (t p : ℝ → ℂ)) p p' =
      if p.1 = p'.1 then ((Real.log D.q * ∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) *
        D.spanGram n p.2 p'.2 else 0 := by
    intro p p'
    simp only [zeroGram, ht, spanGram]
    split_ifs with h
    · rw [h]
      exact D.W_curveConfig_translate_shift hD hg hgs hwL _ _ _
    · refine D.W_curveConfig_translate_eq_zero hD hg hgs fun k => ?_
      have := sep_offsets hw0 hL hrL p.1.2 p'.1.2 (fun h' => h (Fin.ext h'))
        (k - ((p.2 : ℕ) : ℤ) + ((p'.2 : ℕ) : ℤ))
      convert this using 2
      push_cast
      ring
  have hGram := (zeroGram_comb (D.curveConfig hD) (D.temperedConfig_curveConfig hD) t
    (Matrix.of fun (i : Fin r) (p : Fin r × Fin n) => if p.1 = i then star (v p.2) else 0)).trans
      (block_congr _ _ _ hG v)
  have hd : (((Real.log D.q * ∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ D.spanGram n *ᵥ v)).re < 0 := by
    rw [Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg hκ hv
  -- the combined tests live in `[−a, a]`
  have hF : ∀ i, ContDiff ℝ 2 ((∑ p, (Matrix.of fun (i : Fin r) (p : Fin r × Fin n) =>
      if p.1 = i then star (v p.2) else 0) i p • t p : testSpace) : ℝ → ℂ) ∧
        tsupport ((∑ p, (Matrix.of fun (i : Fin r) (p : Fin r × Fin n) =>
          if p.1 = i then star (v p.2) else 0) i p • t p : testSpace) : ℝ → ℂ) ⊆
            Set.Icc (-a) a := by
    intro i
    refine ⟨(∑ p, _ • t p : testSpace).2.1, closure_minimal (fun u hu => ?_) isClosed_Icc⟩
    by_contra hout
    apply hu
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ht, translate]
    refine Finset.sum_eq_zero fun p _ => ?_
    have hz : g (u - (-a + w / 2 + 2 * ((p.1 : ℕ) : ℝ) * w + ((p.2 : ℕ) : ℝ) * Real.log D.q)) =
        0 := by
      by_contra hne
      have hmem := hgs (subset_tsupport _ hne)
      apply hout
      have hi : ((p.1 : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast p.1.2
      have hb : ((p.2 : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast p.2.2
      have hiw : 0 ≤ ((p.1 : ℕ) : ℝ) * w := mul_nonneg (Nat.cast_nonneg _) hw0.le
      have hbL : 0 ≤ ((p.2 : ℕ) : ℝ) * Real.log D.q := mul_nonneg (Nat.cast_nonneg _) hL.le
      have hiw' : ((p.1 : ℕ) : ℝ) * w ≤ ((r : ℝ) - 1) * w :=
        mul_le_mul_of_nonneg_right (by linarith) hw0.le
      have hbL' : ((p.2 : ℕ) : ℝ) * Real.log D.q ≤ ((n : ℝ) - 1) * Real.log D.q :=
        mul_le_mul_of_nonneg_right (by linarith) hL.le
      constructor <;> nlinarith [hmem.1, hmem.2]
    rw [hz, mul_zero]
  calc (r : ℕ∞) = (Fintype.card (Fin r) : ℕ∞) := by simp
    _ ≤ hermNegIndex (zeroGram (D.curveConfig hD) fun i =>
          ((∑ p, (Matrix.of fun (i : Fin r) (p : Fin r × Fin n) =>
            if p.1 = i then star (v p.2) else 0) i p • t p : testSpace) : ℝ → ℂ)) := by
        rw [hGram]
        exact_mod_cast card_le_negIndex_diagonal_const hd
    _ ≤ hodgeDefectAt (D.curveConfig hD) a := le_hodgeDefectAt _ _ hF

/-! ### The window filtration -/

/-- **The degree filtration of a curve is its window filtration.** On the scaling surface of a
curve datum in the strip, the Hodge defect at degree `a` is `0` if the Frobenius window of size
`⌈2a / log q⌉` is positive semidefinite and `∞` otherwise. -/
theorem hodgeDefectAt_curveConfig (a : ℝ) :
    hodgeDefectAt (D.curveConfig hD) a =
      if hermNegIndex (D.spanGram ⌈2 * a / Real.log D.q⌉₊) = 0 then 0 else ⊤ := by
  split_ifs with h
  · exact (hodgeDefectAt_eq_zero_iff _ (D.temperedConfig_curveConfig hD) a).mpr fun f hf hfs =>
      D.re_W_curveConfig_nonneg_of_window hD hf hfs (hermQuad_nonneg_of_negIndex_eq_zero h)
  · obtain ⟨v, hv⟩ : ∃ v, hermQuad (D.spanGram ⌈2 * a / Real.log D.q⌉₊) v < 0 := by
      by_contra hcon
      push_neg at hcon
      exact h (negIndex_eq_zero_of_hermQuad_nonneg hcon)
    exact D.hodgeDefectAt_curveConfig_eq_top hD hv

/-- The first window `G₁ = (t₀)` is positive semidefinite. -/
theorem negIndex_spanGram_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) :
    hermNegIndex (D.spanGram n) = 0 := by
  refine negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
  interval_cases n
  · simp [hermQuad, dotProduct]
  · have ht : D.trace 0 = Fintype.card ι := by simp [trace, powerSum]
    simp only [hermQuad, dotProduct, Fin.sum_univ_one, Matrix.mulVec, spanGram, Pi.star_apply,
      Complex.star_def, Nat.dist_self]
    rw [show conj (x 0) * ((D.trace 0 : ℂ) * x 0) =
        ((D.trace 0 * Complex.normSq (x 0) : ℝ) : ℂ) by
      push_cast; rw [Complex.normSq_eq_conj_mul_self]; ring, Complex.ofReal_re]
    exact mul_nonneg (by rw [ht]; positivity) (Complex.normSq_nonneg _)

/-- **Every curve satisfies the Hodge index up to degree `log q / 2`.** -/
theorem hodgeDefectAt_curveConfig_eq_zero_of_le {a : ℝ} (ha : a ≤ Real.log D.q / 2) :
    hodgeDefectAt (D.curveConfig hD) a = 0 := by
  have hn : ⌈2 * a / Real.log D.q⌉₊ ≤ 1 :=
    Nat.ceil_le.mpr (by rw [Nat.cast_one, div_le_iff₀ D.log_q_pos]; linarith)
  rw [D.hodgeDefectAt_curveConfig hD, if_pos (D.negIndex_spanGram_eq_zero_of_le_one hn)]

/-- **Purity decides the defect from the window `2g` on.** Once `⌈2a / log q⌉` reaches the number of
eigenvalues, the Hodge defect at degree `a` is `0` if no eigenvalue lies outside the unit circle and
`∞` otherwise. -/
theorem hodgeDefectAt_curveConfig_of_card_le {a : ℝ}
    (ha : Fintype.card ι ≤ ⌈2 * a / Real.log D.q⌉₊) :
    hodgeDefectAt (D.curveConfig hD) a = if D.outerSpectrum = ∅ then 0 else ⊤ := by
  rw [D.hodgeDefectAt_curveConfig hD, D.pontryagin_law_curve.2 _ ha]
  simp only [Finset.card_eq_zero]

end CurveDatum

open Real in
/-- **The golden fake curve.** Its Hodge defect vanishes up to degree `log 5 / 2` and is infinite
beyond: the window `G₂` already carries the negative square of `φ`. -/
theorem goldenDatum_hodgeDefectAt (a : ℝ) :
    hodgeDefectAt (goldenDatum.curveConfig goldenDatum_strip) a =
      if a ≤ Real.log 5 / 2 then 0 else ⊤ := by
  have hq : goldenDatum.q = 5 := rfl
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [goldenDatum.hodgeDefectAt_curveConfig goldenDatum_strip, hq]
  by_cases ha : a ≤ Real.log 5 / 2
  · have hn : ⌈2 * a / Real.log 5⌉₊ ≤ 1 :=
      Nat.ceil_le.mpr (by rw [Nat.cast_one, div_le_iff₀ h5]; linarith)
    rw [if_pos (goldenDatum.negIndex_spanGram_eq_zero_of_le_one hn), if_pos ha]
  · have hn : 2 ≤ ⌈2 * a / Real.log 5⌉₊ := by
      have h1 : ((1 : ℕ) : ℝ) < 2 * a / Real.log 5 := by
        rw [Nat.cast_one, lt_div_iff₀ h5]; push_neg at ha; linarith
      have := Nat.lt_ceil.mpr h1
      omega
    rw [if_neg (by rw [goldenDatum_negIndex_spanGram hn]; norm_num), if_neg ha]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
