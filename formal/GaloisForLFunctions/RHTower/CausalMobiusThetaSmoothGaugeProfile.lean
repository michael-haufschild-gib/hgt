import GaloisForLFunctions.RHTower.EulerDeletionPeriodicProjection
import GaloisForLFunctions.RHTower.PoissonArithmeticProgressionBound
import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The smooth-gauge profile of the complete-cell wavelet

Ingredients for the flattened test `q_N^flat`:

* every derivative of the theta seed `g` is `O((1+y²)^{−k})` for every `k`;
* the smooth cutoff `χ(x) = s(4x − 1)` (`0` on `(−∞,1/4]`, `1` on `[1/2,∞)`) and two smooth bumps
  `ψ₁, ψ₂` supported in `[3/10, 7/20]` and `[2/5, 9/20]`;
* the seed difference profile `D_N(x) = N(g(x) − g(x+1/N))` with derivative bounds uniform in `N`;
* the gauge profile `G(x) = χ(x)D_N(x) + c₁ψ₁(x) + c₂ψ₂(x)` and bounds
  `|G^{(n)}(x)| ≤ M (1+x²)^{−k}`, uniform in `N` and in bounded coefficients.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Derivatives of the seed -/

theorem thetaCuspSeed_eq_polyGauss :
    thetaCuspSeed = fun y => Polynomial.eval y thetaCuspSeedPolynomial * GaloisForLFunctions.gaussReal y := by
  funext y
  rw [thetaCuspSeed_eq_polynomial, GaloisForLFunctions.gaussReal]
  ring_nf

theorem contDiff_thetaCuspSeed_all {n : WithTop ℕ∞} : ContDiff ℝ n thetaCuspSeed := by
  rw [thetaCuspSeed_eq_polyGauss]
  exact GaloisForLFunctions.contDiff_polyGauss _

theorem one_add_sq_pow_le (y : ℝ) (k : ℕ) : (1 + y ^ 2) ^ k ≤ 2 ^ k * (1 + |y| ^ (2 * k)) := by
  have hy : |y| ^ (2 * k) = (y ^ 2) ^ k := by rw [pow_mul, sq_abs]
  rw [hy]
  rcases le_total (y ^ 2) 1 with h | h
  · calc (1 + y ^ 2) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (1 + (y ^ 2) ^ k) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + y ^ 2) ^ k ≤ (2 * y ^ 2) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * (y ^ 2) ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + (y ^ 2) ^ k) := by gcongr; linarith

/-- `|g^{(j)}(y)| ≤ C (1+y²)^{−k}`. -/
theorem exists_abs_iteratedDeriv_thetaCuspSeed_le (j k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
    |iteratedDeriv j thetaCuspSeed y| ≤ C * ((1 + y ^ 2) ^ k)⁻¹ := by
  obtain ⟨q, hq⟩ := GaloisForLFunctions.exists_poly_iteratedDeriv_polyGauss thetaCuspSeedPolynomial j
  obtain ⟨C0, hC0⟩ := GaloisForLFunctions.exists_bound_poly_mul_gaussReal q 0
  obtain ⟨C2, hC2⟩ := GaloisForLFunctions.exists_bound_poly_mul_gaussReal q (2 * k)
  refine ⟨2 ^ k * (|C0| + |C2|), by positivity, fun y => ?_⟩
  rw [thetaCuspSeed_eq_polyGauss, hq, le_mul_inv_iff₀ (by positivity)]
  have hg := GaloisForLFunctions.gaussReal_pos y
  have habs : |Polynomial.eval y q * GaloisForLFunctions.gaussReal y| =
      |Polynomial.eval y q| * GaloisForLFunctions.gaussReal y := by rw [abs_mul, abs_of_pos hg]
  have h0 := hC0 y
  have h2 := hC2 y
  rw [pow_zero, one_mul] at h0
  rw [habs]
  set a := |Polynomial.eval y q| * GaloisForLFunctions.gaussReal y
  have ha : 0 ≤ a := by positivity
  calc a * (1 + y ^ 2) ^ k ≤ a * (2 ^ k * (1 + |y| ^ (2 * k))) :=
        mul_le_mul_of_nonneg_left (one_add_sq_pow_le y k) ha
    _ = 2 ^ k * (a + |y| ^ (2 * k) * a) := by ring
    _ ≤ 2 ^ k * (|C0| + |C2|) := by
        gcongr
        · exact h0.trans (le_abs_self _)
        · exact h2.trans (le_abs_self _)

/-! ## Locally constant tails and global derivative bounds -/

theorem iteratedDeriv_eq_zero_of_eventuallyEq_const {f : ℝ → ℝ} {x c : ℝ}
    (h : f =ᶠ[𝓝 x] fun _ => c) {i : ℕ} (hi : i ≠ 0 ∨ c = 0) : iteratedDeriv i f x = 0 := by
  rw [h.iteratedDeriv_eq, iteratedDeriv_const]
  split_ifs with h0
  · rcases hi with hi | hi
    · exact absurd h0 hi
    · exact hi
  · rfl

/-- A continuous derivative that is controlled outside a compact interval is globally bounded. -/
theorem exists_abs_le_of_continuous_of_outside {u : ℝ → ℝ} (hu : Continuous u) {a b B : ℝ}
    (hout : ∀ x, x ∉ Icc a b → |u x| ≤ B) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |u x| ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.continuousOn (s := Icc a b)
  refine ⟨max (max C B) 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc a b
  · have := hC x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hout x hx).trans ((le_max_right _ _).trans (le_max_left _ _))

/-! ## The smooth cutoff -/

/-- `χ(x) = s(4x − 1)`: zero on `(−∞, 1/4]`, one on `[1/2, ∞)`. -/
def gaugeCutoff (x : ℝ) : ℝ := Real.smoothTransition (4 * x - 1)

theorem contDiff_gaugeCutoff {n : ℕ∞} : ContDiff ℝ n gaugeCutoff :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem gaugeCutoff_of_le {x : ℝ} (hx : x ≤ 1 / 4) : gaugeCutoff x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem gaugeCutoff_of_ge {x : ℝ} (hx : 1 / 2 ≤ x) : gaugeCutoff x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem gaugeCutoff_nonneg (x : ℝ) : 0 ≤ gaugeCutoff x := Real.smoothTransition.nonneg _

theorem gaugeCutoff_le_one (x : ℝ) : gaugeCutoff x ≤ 1 := Real.smoothTransition.le_one _

theorem gaugeCutoff_eventually_zero {x : ℝ} (hx : x < 1 / 4) :
    gaugeCutoff =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [Iio_mem_nhds hx] with y hy using gaugeCutoff_of_le (le_of_lt hy)

theorem gaugeCutoff_eventually_one {x : ℝ} (hx : 1 / 2 < x) :
    gaugeCutoff =ᶠ[𝓝 x] fun _ => 1 := by
  filter_upwards [Ioi_mem_nhds hx] with y hy using gaugeCutoff_of_ge (le_of_lt hy)

theorem exists_abs_iteratedDeriv_gaugeCutoff_le (i : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |iteratedDeriv i gaugeCutoff x| ≤ K := by
  refine exists_abs_le_of_continuous_of_outside (a := 1 / 4) (b := 1 / 2) (B := 1)
    (contDiff_gaugeCutoff (n := (i : ℕ∞)).continuous_iteratedDeriv i (by exact_mod_cast le_rfl))
    fun x hx => ?_
  rcases not_and_or.1 hx with hx | hx
  · rw [iteratedDeriv_eq_zero_of_eventuallyEq_const (gaugeCutoff_eventually_zero (not_le.1 hx))
      (Or.inr rfl), abs_zero]
    norm_num
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [iteratedDeriv_zero]
      rw [abs_of_nonneg (gaugeCutoff_nonneg x)]
      exact gaugeCutoff_le_one x
    · rw [iteratedDeriv_eq_zero_of_eventuallyEq_const (gaugeCutoff_eventually_one (not_le.1 hx))
        (Or.inl hi.ne'), abs_zero]
      norm_num

/-! ## Two smooth bumps -/

/-- A smooth bump, positive exactly on `(α, β)`. -/
def gaugeBump (α β x : ℝ) : ℝ := Real.smoothTransition (x - α) * Real.smoothTransition (β - x)

theorem contDiff_gaugeBump (α β : ℝ) {n : ℕ∞} : ContDiff ℝ n (gaugeBump α β) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem gaugeBump_nonneg (α β x : ℝ) : 0 ≤ gaugeBump α β x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem gaugeBump_le_one (α β x : ℝ) : gaugeBump α β x ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem gaugeBump_of_le {α β x : ℝ} (hx : x ≤ α) : gaugeBump α β x = 0 := by
  rw [gaugeBump, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem gaugeBump_of_ge {α β x : ℝ} (hx : β ≤ x) : gaugeBump α β x = 0 := by
  rw [gaugeBump, Real.smoothTransition.zero_of_nonpos (by linarith : β - x ≤ 0), mul_zero]

theorem gaugeBump_pos {α β x : ℝ} (h1 : α < x) (h2 : x < β) : 0 < gaugeBump α β x :=
  mul_pos (Real.smoothTransition.pos_of_pos (by linarith)) (Real.smoothTransition.pos_of_pos (by linarith))

theorem gaugeBump_eq_zero_of_not_mem {α β x : ℝ} (hx : x ∉ Ioo α β) : gaugeBump α β x = 0 := by
  rcases not_and_or.1 hx with h | h
  · exact gaugeBump_of_le (not_lt.1 h)
  · exact gaugeBump_of_ge (not_lt.1 h)

theorem gaugeBump_eventually_zero {α β x : ℝ} (hx : x ∉ Icc α β) :
    gaugeBump α β =ᶠ[𝓝 x] fun _ => 0 := by
  rcases not_and_or.1 hx with h | h
  · filter_upwards [Iio_mem_nhds (not_le.1 h)] with y hy using gaugeBump_of_le (le_of_lt hy)
  · filter_upwards [Ioi_mem_nhds (not_le.1 h)] with y hy using gaugeBump_of_ge (le_of_lt hy)

theorem iteratedDeriv_gaugeBump_eq_zero {α β x : ℝ} (hx : x ∉ Icc α β) (i : ℕ) :
    iteratedDeriv i (gaugeBump α β) x = 0 :=
  iteratedDeriv_eq_zero_of_eventuallyEq_const (gaugeBump_eventually_zero hx) (Or.inr rfl)

theorem exists_abs_iteratedDeriv_gaugeBump_le (α β : ℝ) (i : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |iteratedDeriv i (gaugeBump α β) x| ≤ K :=
  exists_abs_le_of_continuous_of_outside (a := α) (b := β) (B := 0)
    ((contDiff_gaugeBump α β (n := (i : ℕ∞))).continuous_iteratedDeriv i (by exact_mod_cast le_rfl))
    fun x hx => by rw [iteratedDeriv_gaugeBump_eq_zero hx, abs_zero]

/-- The first bump, supported in `[3/10, 7/20]`. -/
def gaugeBumpOne : ℝ → ℝ := gaugeBump (3 / 10) (7 / 20)

/-- The second bump, supported in `[2/5, 9/20]`. -/
def gaugeBumpTwo : ℝ → ℝ := gaugeBump (2 / 5) (9 / 20)

/-! ## The seed difference profile -/

/-- `D_N(x) = N (g(x) − g(x + 1/N))`. -/
def seedDifferenceProfile (N : ℕ) (x : ℝ) : ℝ :=
  N * (thetaCuspSeed x - thetaCuspSeed (x + 1 / N))

theorem contDiff_seedDifferenceProfile (N : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (seedDifferenceProfile N) :=
  contDiff_const.mul (contDiff_thetaCuspSeed_all.sub (contDiff_thetaCuspSeed_all.comp (contDiff_id.add contDiff_const)))

theorem iteratedDeriv_seedDifferenceProfile (N m : ℕ) (x : ℝ) :
    iteratedDeriv m (seedDifferenceProfile N) x =
      N * (iteratedDeriv m thetaCuspSeed x - iteratedDeriv m thetaCuspSeed (x + 1 / N)) := by
  have h1 : ContDiffAt ℝ m (fun x => thetaCuspSeed x - thetaCuspSeed (x + 1 / N)) x :=
    (contDiff_thetaCuspSeed_all.sub (contDiff_thetaCuspSeed_all.comp (contDiff_id.add contDiff_const))).contDiffAt
  have h2 : (fun x => thetaCuspSeed x - thetaCuspSeed (x + 1 / N)) =
      thetaCuspSeed - fun x => thetaCuspSeed (x + 1 / N) := rfl
  show iteratedDeriv m (fun x => (N : ℝ) * (fun x => thetaCuspSeed x - thetaCuspSeed (x + 1 / N)) x) x = _
  have hg2 : ContDiffAt ℝ m (fun x => thetaCuspSeed (x + 1 / N)) x :=
    (contDiff_thetaCuspSeed_all.comp (contDiff_id.add contDiff_const)).contDiffAt
  rw [iteratedDeriv_const_mul _ h1, h2,
    iteratedDeriv_sub (f := thetaCuspSeed) (g := fun x => thetaCuspSeed (x + 1 / N))
      contDiff_thetaCuspSeed_all.contDiffAt hg2, iteratedDeriv_comp_add_const]

/-- Uniformly in `N ≥ 1`: `|D_N^{(m)}(x)| ≤ C (1+x²)^{−k}` for `x ≥ 0`. -/
theorem exists_abs_iteratedDeriv_seedDifferenceProfile_le (m k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 ≤ x →
      |iteratedDeriv m (seedDifferenceProfile N) x| ≤ C * ((1 + x ^ 2) ^ k)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_iteratedDeriv_thetaCuspSeed_le (m + 1) k
  refine ⟨C, hC0, fun N hN x hx => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [iteratedDeriv_seedDifferenceProfile]
  have hd : ∀ y, HasDerivAt (iteratedDeriv m thetaCuspSeed) (iteratedDeriv (m + 1) thetaCuspSeed y) y := by
    intro y
    rw [iteratedDeriv_succ]
    exact ((contDiff_thetaCuspSeed_all (n := ⊤).differentiable_iteratedDeriv m
      (by exact_mod_cast WithTop.coe_lt_top _)) y).hasDerivAt
  have hbound : ∀ y ∈ Ico x (x + 1 / N), ‖iteratedDeriv (m + 1) thetaCuspSeed y‖ ≤
      C * ((1 + x ^ 2) ^ k)⁻¹ := by
    intro y hy
    rw [Real.norm_eq_abs]
    refine (hC y).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    apply inv_anti₀ (by positivity)
    gcongr
    nlinarith [hy.1]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := iteratedDeriv m thetaCuspSeed)
    (fun y _ => (hd y).hasDerivWithinAt) hbound (x + 1 / N)
    ⟨by linarith [show (0 : ℝ) ≤ 1 / N by positivity], le_rfl⟩
  rw [Real.norm_eq_abs, abs_sub_comm, add_sub_cancel_left] at hmvt
  rw [abs_mul, abs_of_pos hNR]
  calc (N : ℝ) * |iteratedDeriv m thetaCuspSeed x - iteratedDeriv m thetaCuspSeed (x + 1 / N)|
      ≤ N * (C * ((1 + x ^ 2) ^ k)⁻¹ * (1 / N)) := mul_le_mul_of_nonneg_left hmvt hNR.le
    _ = C * ((1 + x ^ 2) ^ k)⁻¹ := by field_simp

/-! ## The gauge profile and its uniform derivative bounds -/

/-- `|(χ D_N)^{(n)}(x)| ≤ C (1+x²)^{−k}` uniformly in `N ≥ 1`. -/
theorem exists_abs_iteratedDeriv_cutoff_mul_seedDifference_le (n k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ,
      |iteratedDeriv n (fun y => gaugeCutoff y * seedDifferenceProfile N y) x| ≤
        C * ((1 + x ^ 2) ^ k)⁻¹ := by
  choose K hK0 hK using exists_abs_iteratedDeriv_gaugeCutoff_le
  choose D hD0 hD using fun m => exists_abs_iteratedDeriv_seedDifferenceProfile_le m k
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K i * D (n - i),
    Finset.sum_nonneg fun i _ => by have := hK0 i; have := hD0 (n - i); positivity, fun N hN x => ?_⟩
  rcases lt_or_ge x (1 / 4) with hx | hx
  · have hz : (fun y => gaugeCutoff y * seedDifferenceProfile N y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [gaugeCutoff_eventually_zero hx] with y hy
      rw [hy, zero_mul]
    rw [iteratedDeriv_eq_zero_of_eventuallyEq_const hz (Or.inr rfl), abs_zero]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => by have := hK0 i; have := hD0 (n - i); positivity)
      (by positivity)
  · have hx0 : 0 ≤ x := by linarith
    have hL := norm_iteratedFDeriv_mul_le (N := ((n : ℕ∞) : WithTop ℕ∞))
      (contDiff_gaugeCutoff (n := (n : ℕ∞))) (contDiff_seedDifferenceProfile N) x
      (by exact_mod_cast le_rfl)
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hL
    refine hL.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hK i x
    have h2 := hD (n - i) N hN x hx0
    calc (n.choose i : ℝ) * |iteratedDeriv i gaugeCutoff x| *
          |iteratedDeriv (n - i) (seedDifferenceProfile N) x|
        ≤ n.choose i * K i * (D (n - i) * ((1 + x ^ 2) ^ k)⁻¹) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (hK0 i))
      _ = (n.choose i : ℝ) * K i * D (n - i) * ((1 + x ^ 2) ^ k)⁻¹ := by ring

/-- The gauge profile `G(x) = χ(x) D_N(x) + c₁ ψ₁(x) + c₂ ψ₂(x)`. -/
def gaugeProfile (N : ℕ) (c₁ c₂ : ℝ) (x : ℝ) : ℝ :=
  gaugeCutoff x * seedDifferenceProfile N x + c₁ * gaugeBumpOne x + c₂ * gaugeBumpTwo x

theorem contDiff_gaugeProfile (N : ℕ) (c₁ c₂ : ℝ) {n : ℕ∞} : ContDiff ℝ n (gaugeProfile N c₁ c₂) :=
  ((contDiff_gaugeCutoff.mul (contDiff_seedDifferenceProfile N)).add
    (contDiff_const.mul (contDiff_gaugeBump _ _))).add (contDiff_const.mul (contDiff_gaugeBump _ _))

theorem iteratedDeriv_gaugeProfile (N : ℕ) (c₁ c₂ : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (gaugeProfile N c₁ c₂) x =
      iteratedDeriv n (fun y => gaugeCutoff y * seedDifferenceProfile N y) x +
        c₁ * iteratedDeriv n gaugeBumpOne x + c₂ * iteratedDeriv n gaugeBumpTwo x := by
  have hA : ContDiffAt ℝ n (fun y => gaugeCutoff y * seedDifferenceProfile N y) x :=
    ((contDiff_gaugeCutoff (n := (n : ℕ∞))).mul (contDiff_seedDifferenceProfile N)).contDiffAt
  have hB1 : ContDiffAt ℝ n gaugeBumpOne x := (contDiff_gaugeBump (n := (n : ℕ∞)) _ _).contDiffAt
  have hB2 : ContDiffAt ℝ n gaugeBumpTwo x := (contDiff_gaugeBump (n := (n : ℕ∞)) _ _).contDiffAt
  have hC1 : ContDiffAt ℝ n (fun y => c₁ * gaugeBumpOne y) x := contDiffAt_const.mul hB1
  have hC2 : ContDiffAt ℝ n (fun y => c₂ * gaugeBumpTwo y) x := contDiffAt_const.mul hB2
  show iteratedDeriv n ((fun y => gaugeCutoff y * seedDifferenceProfile N y) +
    (fun y => c₁ * gaugeBumpOne y) + fun y => c₂ * gaugeBumpTwo y) x = _
  rw [iteratedDeriv_add (f := (fun y => gaugeCutoff y * seedDifferenceProfile N y) +
      fun y => c₁ * gaugeBumpOne y) (g := fun y => c₂ * gaugeBumpTwo y) (hA.add hC1) hC2,
    iteratedDeriv_add (f := fun y => gaugeCutoff y * seedDifferenceProfile N y)
      (g := fun y => c₁ * gaugeBumpOne y) hA hC1, iteratedDeriv_const_mul _ hB1,
    iteratedDeriv_const_mul _ hB2]

theorem exists_abs_iteratedDeriv_gaugeBump_le_inv (α β : ℝ) (hα : 0 ≤ α) (hβ : β ≤ 1) (n k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |iteratedDeriv n (gaugeBump α β) x| ≤ K * ((1 + x ^ 2) ^ k)⁻¹ := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_iteratedDeriv_gaugeBump_le α β n
  refine ⟨K * 2 ^ k, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ Icc α β
  · have h1 : (1 + x ^ 2) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity)
      (by nlinarith [hx.1, hx.2]) k
    calc |iteratedDeriv n (gaugeBump α β) x| ≤ K := hK x
      _ = K * 2 ^ k * (2 ^ k)⁻¹ := by field_simp
      _ ≤ K * 2 ^ k * ((1 + x ^ 2) ^ k)⁻¹ := by gcongr
  · rw [iteratedDeriv_gaugeBump_eq_zero hx, abs_zero]; positivity

/-- **Uniform derivative bounds** for the gauge profile: `|G^{(n)}(x)| ≤ M (1+x²)^{−k}`, uniformly
in `N ≥ 1` and in coefficients bounded by `B`. -/
theorem exists_abs_iteratedDeriv_gaugeProfile_le (n k : ℕ) (B : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ N : ℕ, 1 ≤ N → ∀ c₁ c₂ : ℝ, |c₁| ≤ B → |c₂| ≤ B → ∀ x : ℝ,
      |iteratedDeriv n (gaugeProfile N c₁ c₂) x| ≤ M * ((1 + x ^ 2) ^ k)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_iteratedDeriv_cutoff_mul_seedDifference_le n k
  obtain ⟨K1, hK10, hK1⟩ := exists_abs_iteratedDeriv_gaugeBump_le_inv (3 / 10) (7 / 20)
    (by norm_num) (by norm_num) n k
  obtain ⟨K2, hK20, hK2⟩ := exists_abs_iteratedDeriv_gaugeBump_le_inv (2 / 5) (9 / 20)
    (by norm_num) (by norm_num) n k
  refine ⟨C + |B| * K1 + |B| * K2, by positivity, fun N hN c₁ c₂ h1 h2 x => ?_⟩
  rw [iteratedDeriv_gaugeProfile]
  have hi : 0 ≤ ((1 + x ^ 2) ^ k)⁻¹ := by positivity
  have e1 : |c₁ * iteratedDeriv n gaugeBumpOne x| ≤ |B| * K1 * ((1 + x ^ 2) ^ k)⁻¹ := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul (h1.trans (le_abs_self B)) (hK1 x) (abs_nonneg _) (abs_nonneg _)
  have e2 : |c₂ * iteratedDeriv n gaugeBumpTwo x| ≤ |B| * K2 * ((1 + x ^ 2) ^ k)⁻¹ := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul (h2.trans (le_abs_self B)) (hK2 x) (abs_nonneg _) (abs_nonneg _)
  calc _ ≤ |iteratedDeriv n (fun y => gaugeCutoff y * seedDifferenceProfile N y) x| +
        |c₁ * iteratedDeriv n gaugeBumpOne x| + |c₂ * iteratedDeriv n gaugeBumpTwo x| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C * ((1 + x ^ 2) ^ k)⁻¹ + |B| * K1 * ((1 + x ^ 2) ^ k)⁻¹ +
        |B| * K2 * ((1 + x ^ 2) ^ k)⁻¹ := add_le_add (add_le_add (hC N hN x) e1) e2
    _ = (C + |B| * K1 + |B| * K2) * ((1 + x ^ 2) ^ k)⁻¹ := by ring

theorem gaugeProfile_of_le (N : ℕ) (c₁ c₂ : ℝ) {x : ℝ} (hx : x ≤ 1 / 4) : gaugeProfile N c₁ c₂ x = 0 := by
  rw [gaugeProfile, gaugeCutoff_of_le hx, gaugeBumpOne, gaugeBumpTwo,
    gaugeBump_of_le (by linarith), gaugeBump_of_le (by linarith)]
  ring

/-! ## Riemann sums -/

/-- For `φ` continuous and vanishing off `[0,1]`: `N^{−1} Σ_{r=1}^{N} φ(r/N) → ∫ φ`. -/
theorem tendsto_riemannSum_Icc {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ x, x ∉ Icc (0 : ℝ) 1 → φ x = 0) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, φ (r / N)) atTop (𝓝 (∫ x, φ x)) := by
  have hint : ∫ x, φ x = ∫ x in (0 : ℝ)..1, φ x := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hsupp x hx]
  rw [hint, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ.continuousOn (s := Icc (0 : ℝ) 1))
    (ε / 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNδ : (N : ℝ)⁻¹ < δ := by
    have : (N₀ : ℝ) ≤ N := by exact_mod_cast le_of_max_le_left hN
    rw [inv_lt_comm₀ hNR hδ]
    calc δ⁻¹ = 1 / δ := (one_div δ).symm
      _ < N₀ := hN₀
      _ ≤ N := this
  set a : ℕ → ℝ := fun i => (i : ℝ) / N
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (f := φ) (a := a) (n := N)
    (μ := volume) fun i _ => hφ.intervalIntegrable _ _
  have ha0 : a 0 = 0 := by simp [a]
  have haN : a N = 1 := by simp [a, hNR.ne']
  rw [ha0, haN] at hadj
  have hlen : ∀ i : ℕ, a (i + 1) - a i = (N : ℝ)⁻¹ := fun i => by
    simp only [a]; push_cast; field_simp; ring
  have hsum : (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, φ (r / N) =
      ∑ i ∈ Finset.range N, ∫ x in a i..a (i + 1), φ (a (i + 1)) := by
    rw [← DeletionResidueMartingale.sum_range_succ_eq_sum_Icc_one N fun r => φ (r / N),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const, smul_eq_mul, hlen]
  rw [Real.dist_eq, hsum, ← hadj, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range N,
      |(∫ x in a i..a (i + 1), φ (a (i + 1))) - ∫ x in a i..a (i + 1), φ x| ≤ ε / 2 * (N : ℝ)⁻¹ := by
    intro i hi
    have hi' : i < N := Finset.mem_range.1 hi
    have hle : a i ≤ a (i + 1) := by simp only [a]; gcongr; linarith
    have hlen := hlen i
    rw [← intervalIntegral.integral_sub (f := fun _ => φ (a (i + 1))) (g := φ)
      intervalIntegrable_const (hφ.intervalIntegrable _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a i) (b := a (i + 1))
      (f := fun x => φ (a (i + 1)) - φ x) (C := ε / 2) fun x hx => ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ a (i + 1) - a i), hlen] at hb
      exact hb
    · rw [uIoc_of_le hle] at hx
      have hai : 0 ≤ a i := by simp only [a]; positivity
      have hai1 : a (i + 1) ≤ 1 := by
        simp only [a]; rw [div_le_one hNR]; exact_mod_cast hi'
      have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have ha01 : a (i + 1) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hai1⟩
      have hd : dist (a (i + 1)) x < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.2])]
        linarith [hx.1]
      exact (hδφ _ ha01 _ hx01 hd).le
  calc |∑ i ∈ Finset.range N, ((∫ x in a i..a (i + 1), φ (a (i + 1))) - ∫ x in a i..a (i + 1), φ x)|
      ≤ ∑ i ∈ Finset.range N, |(∫ x in a i..a (i + 1), φ (a (i + 1))) - ∫ x in a i..a (i + 1), φ x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, ε / 2 * (N : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = ε / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by linarith

/-! ## The moment matrix and its limit -/

/-- Normalized zeroth moment row `N^{−1} Σ_{r≤N} ψ(r/N)`. -/
def gaugeMomentZero (ψ : ℝ → ℝ) (N : ℕ) : ℝ := (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, ψ (r / N)

/-- Normalized first moment row `N^{−1} Σ_{r≤N} (r/N) ψ(r/N)`. -/
def gaugeMomentOne (ψ : ℝ → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, ((r : ℝ) / N) * ψ (r / N)

theorem gaugeBump_eq_zero_off_unit {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) {x : ℝ}
    (hx : x ∉ Icc (0 : ℝ) 1) : gaugeBump α β x = 0 := by
  refine gaugeBump_eq_zero_of_not_mem fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩

theorem tendsto_gaugeMomentZero {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) :
    Tendsto (gaugeMomentZero (gaugeBump α β)) atTop (𝓝 (∫ x, gaugeBump α β x)) :=
  tendsto_riemannSum_Icc (contDiff_gaugeBump α β (n := 0)).continuous
    fun _ hx => gaugeBump_eq_zero_off_unit hα hβ hx

theorem tendsto_gaugeMomentOne {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) :
    Tendsto (gaugeMomentOne (gaugeBump α β)) atTop (𝓝 (∫ x, x * gaugeBump α β x)) :=
  tendsto_riemannSum_Icc (continuous_id.mul (contDiff_gaugeBump α β (n := 0)).continuous)
    fun _ hx => by rw [gaugeBump_eq_zero_off_unit hα hβ hx, mul_zero]

theorem gaugeMomentZero_mem (α β : ℝ) (N : ℕ) :
    0 ≤ gaugeMomentZero (gaugeBump α β) N ∧ gaugeMomentZero (gaugeBump α β) N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [gaugeMomentZero]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs0 : 0 ≤ ∑ r ∈ Finset.Icc 1 N, gaugeBump α β (r / N) :=
    Finset.sum_nonneg fun _ _ => gaugeBump_nonneg _ _ _
  have hs1 : ∑ r ∈ Finset.Icc 1 N, gaugeBump α β (r / N) ≤ N := by
    calc ∑ r ∈ Finset.Icc 1 N, gaugeBump α β (r / N) ≤ ∑ r ∈ Finset.Icc 1 N, (1 : ℝ) :=
          Finset.sum_le_sum fun _ _ => gaugeBump_le_one _ _ _
      _ = N := by simp
  refine ⟨by unfold gaugeMomentZero; positivity, ?_⟩
  rw [gaugeMomentZero, inv_mul_le_iff₀ hNR, mul_one]
  exact hs1

theorem gaugeMomentOne_mem (α β : ℝ) (N : ℕ) :
    0 ≤ gaugeMomentOne (gaugeBump α β) N ∧ gaugeMomentOne (gaugeBump α β) N ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [gaugeMomentOne]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ r ∈ Finset.Icc 1 N, 0 ≤ ((r : ℝ) / N) * gaugeBump α β (r / N) ∧
      ((r : ℝ) / N) * gaugeBump α β (r / N) ≤ 1 := by
    intro r hr
    have hrN : (r : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hr).2
    have h1 : (r : ℝ) / N ≤ 1 := by rw [div_le_one hNR]; exact hrN
    exact ⟨mul_nonneg (by positivity) (gaugeBump_nonneg _ _ _),
      mul_le_one₀ h1 (gaugeBump_nonneg _ _ _) (gaugeBump_le_one _ _ _)⟩
  have hs0 := Finset.sum_nonneg fun r hr => (hterm r hr).1
  have hs1 : ∑ r ∈ Finset.Icc 1 N, ((r : ℝ) / N) * gaugeBump α β (r / N) ≤ N := by
    calc _ ≤ ∑ r ∈ Finset.Icc 1 N, (1 : ℝ) := Finset.sum_le_sum fun r hr => (hterm r hr).2
      _ = N := by simp
  refine ⟨by unfold gaugeMomentOne; positivity, ?_⟩
  rw [gaugeMomentOne, inv_mul_le_iff₀ hNR, mul_one]
  exact hs1

/-- The determinant of the normalized moment matrix. -/
def gaugeDet (N : ℕ) : ℝ :=
  gaugeMomentZero gaugeBumpOne N * gaugeMomentOne gaugeBumpTwo N -
    gaugeMomentZero gaugeBumpTwo N * gaugeMomentOne gaugeBumpOne N

/-- The limit determinant `∫ψ₁ ∫uψ₂ − ∫ψ₂ ∫uψ₁`. -/
def gaugeLimitDet : ℝ :=
  (∫ x, gaugeBumpOne x) * (∫ x, x * gaugeBumpTwo x) -
    (∫ x, gaugeBumpTwo x) * (∫ x, x * gaugeBumpOne x)

theorem tendsto_gaugeDet : Tendsto gaugeDet atTop (𝓝 gaugeLimitDet) := by
  have h1 := tendsto_gaugeMomentZero (α := 3 / 10) (β := 7 / 20) (by norm_num) (by norm_num)
  have h2 := tendsto_gaugeMomentOne (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
  have h3 := tendsto_gaugeMomentZero (α := 2 / 5) (β := 9 / 20) (by norm_num) (by norm_num)
  have h4 := tendsto_gaugeMomentOne (α := 3 / 10) (β := 7 / 20) (by norm_num) (by norm_num)
  exact (h1.mul h2).sub (h3.mul h4)

/-- With `φᵢ(u) = u² ψᵢ(u)` the limit matrix is that of `∫ φ/u²` and `∫ φ/u`. -/
theorem integral_gaugeBump_eq_moments (α β : ℝ) (hα : 0 < α) :
    (∫ x, gaugeBump α β x) = ∫ x, x ^ 2 * gaugeBump α β x / x ^ 2 ∧
      (∫ x, x * gaugeBump α β x) = ∫ x, x ^ 2 * gaugeBump α β x / x := by
  have h0 : ∀ x : ℝ, x = 0 → gaugeBump α β x = 0 := fun x hx => gaugeBump_of_le (by rw [hx]; exact hα.le)
  constructor
  · congr 1; funext x
    by_cases hx : x = 0
    · rw [h0 x hx]; simp
    · field_simp
  · congr 1; funext x
    by_cases hx : x = 0
    · rw [h0 x hx]; simp
    · field_simp

theorem integrable_gaugeBump (α β : ℝ) : Integrable (gaugeBump α β) :=
  (contDiff_gaugeBump α β (n := 0)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun _ hx =>
      gaugeBump_eq_zero_of_not_mem fun h => hx ⟨h.1.le, h.2.le⟩)

theorem integrable_mul_gaugeBump (α β : ℝ) : Integrable fun x => x * gaugeBump α β x :=
  (continuous_id.mul (contDiff_gaugeBump α β (n := 0)).continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := α) (b := β)) fun x hx => by
      show x * gaugeBump α β x = 0
      rw [gaugeBump_eq_zero_of_not_mem fun h => hx ⟨h.1.le, h.2.le⟩, mul_zero])

theorem integral_gaugeBump_pos {α β : ℝ} (h : α < β) : 0 < ∫ x, gaugeBump α β x := by
  rw [integral_pos_iff_support_of_nonneg (fun x => gaugeBump_nonneg α β x) (integrable_gaugeBump α β)]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo α β) fun x hx => (gaugeBump_pos hx.1 hx.2).ne')
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

theorem gaugeLimitDet_pos : 0 < gaugeLimitDet := by
  have I1 := integral_gaugeBump_pos (α := 3 / 10) (β := 7 / 20) (by norm_num)
  have I2 := integral_gaugeBump_pos (α := 2 / 5) (β := 9 / 20) (by norm_num)
  have J2 : 2 / 5 * ∫ x, gaugeBumpTwo x ≤ ∫ x, x * gaugeBumpTwo x := by
    rw [← integral_const_mul]
    refine integral_mono ((integrable_gaugeBump _ _).const_mul _) (integrable_mul_gaugeBump _ _)
      fun x => ?_
    by_cases hx : x ≤ 2 / 5
    · simp [gaugeBumpTwo, gaugeBump_of_le hx]
    · exact mul_le_mul_of_nonneg_right (by linarith) (gaugeBump_nonneg _ _ _)
  have J1 : ∫ x, x * gaugeBumpOne x ≤ 7 / 20 * ∫ x, gaugeBumpOne x := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_mul_gaugeBump _ _) ((integrable_gaugeBump _ _).const_mul _)
      fun x => ?_
    by_cases hx : 7 / 20 ≤ x
    · simp [gaugeBumpOne, gaugeBump_of_ge hx]
    · exact mul_le_mul_of_nonneg_right (by linarith) (gaugeBump_nonneg _ _ _)
  unfold gaugeLimitDet
  change 0 < (∫ x, gaugeBumpOne x) * (∫ x, x * gaugeBumpTwo x) -
    (∫ x, gaugeBumpTwo x) * (∫ x, x * gaugeBumpOne x)
  simp only [gaugeBumpOne, gaugeBumpTwo] at I1 I2 J1 J2 ⊢
  nlinarith [mul_le_mul_of_nonneg_left J2 I1.le, mul_le_mul_of_nonneg_left J1 I2.le, mul_pos I1 I2]

theorem eventually_gaugeDet_ge : ∀ᶠ N in atTop, gaugeLimitDet / 2 ≤ gaugeDet N :=
  tendsto_gaugeDet.eventually (Ici_mem_nhds (by linarith [gaugeLimitDet_pos]))

/-! ## The right-hand sides and the coefficients -/

/-- `ρ₀ = Σ_{r≤N} (1 − χ(r/N)) (g(r/N) − g((r+1)/N))`. -/
def gaugeRhsZero (N : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 N, (1 - gaugeCutoff (r / N)) *
    (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N))

/-- `ρ₁ = N^{−1} Σ_{r≤N} r (1 − χ(r/N)) (g(r/N) − g((r+1)/N))`. -/
def gaugeRhsOne (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, (r : ℝ) * (1 - gaugeCutoff (r / N)) *
    (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N))

theorem exists_abs_gaugeRhs_le : ∃ R : ℝ, 0 ≤ R ∧ ∀ N : ℕ, 1 ≤ N →
    |gaugeRhsZero N| ≤ R ∧ |gaugeRhsOne N| ≤ R := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_thetaSeed_increment_le_linear
  refine ⟨2 * K, by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hcut : ∀ r : ℕ, |1 - gaugeCutoff (r / N)| ≤ 1 := fun r => by
    rw [abs_le]; constructor <;> linarith [gaugeCutoff_nonneg (r / N), gaugeCutoff_le_one (r / N)]
  have hinc : ∀ r ∈ Finset.Icc 1 N, |thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)| ≤
      2 * K / N := by
    intro r hr
    have hrN : (r : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hr).2
    refine (hK N r hN).trans ?_
    rw [div_le_div_iff₀ (by positivity) hN0]
    calc K * ((r : ℝ) + 1) * N ≤ K * (2 * N) * N := by gcongr; linarith
      _ = 2 * K * (N : ℝ) ^ 2 := by ring
  have hcard : ((Finset.Icc 1 N).card : ℝ) = N := by simp
  constructor
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ r ∈ Finset.Icc 1 N, |(1 - gaugeCutoff (r / N)) *
          (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N))|
        ≤ ∑ r ∈ Finset.Icc 1 N, 2 * K / N := Finset.sum_le_sum fun r hr => by
          rw [abs_mul]
          exact (mul_le_mul (hcut r) (hinc r hr) (abs_nonneg _) zero_le_one).trans (by rw [one_mul])
      _ = 2 * K := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; field_simp
  · rw [gaugeRhsOne, abs_mul, abs_of_pos (inv_pos.2 hN0)]
    refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans ?_
    calc (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, |(r : ℝ) * (1 - gaugeCutoff (r / N)) *
          (thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N))|
        ≤ (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc 1 N, (N : ℝ) * (2 * K / N) := by
          gcongr with r hr
          rw [abs_mul, abs_mul, Nat.abs_cast]
          have hrN : (r : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.1 hr).2
          calc (r : ℝ) * |1 - gaugeCutoff (r / N)| *
                |thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)|
              ≤ N * 1 * (2 * K / N) := by
                gcongr
                · exact hcut r
                · exact hinc r hr
            _ = (N : ℝ) * (2 * K / N) := by ring
      _ = 2 * K := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; field_simp

/-- First correction coefficient (Cramer's rule). -/
def gaugeCoeffOne (N : ℕ) : ℝ :=
  (gaugeRhsZero N * gaugeMomentOne gaugeBumpTwo N - gaugeMomentZero gaugeBumpTwo N * gaugeRhsOne N) /
    gaugeDet N

/-- Second correction coefficient (Cramer's rule). -/
def gaugeCoeffTwo (N : ℕ) : ℝ :=
  (gaugeMomentZero gaugeBumpOne N * gaugeRhsOne N - gaugeRhsZero N * gaugeMomentOne gaugeBumpOne N) /
    gaugeDet N

theorem cramer_two {a1 a2 b1 b2 r0 r1 : ℝ} (h : a1 * b2 - a2 * b1 ≠ 0) :
    (r0 * b2 - a2 * r1) / (a1 * b2 - a2 * b1) * a1 + (a1 * r1 - r0 * b1) / (a1 * b2 - a2 * b1) * a2 = r0 ∧
      (r0 * b2 - a2 * r1) / (a1 * b2 - a2 * b1) * b1 +
        (a1 * r1 - r0 * b1) / (a1 * b2 - a2 * b1) * b2 = r1 := by
  constructor <;>
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff h]
    ring

theorem gaugeCoeff_solve {N : ℕ} (h : gaugeDet N ≠ 0) :
    gaugeCoeffOne N * gaugeMomentZero gaugeBumpOne N + gaugeCoeffTwo N * gaugeMomentZero gaugeBumpTwo N =
        gaugeRhsZero N ∧
      gaugeCoeffOne N * gaugeMomentOne gaugeBumpOne N + gaugeCoeffTwo N * gaugeMomentOne gaugeBumpTwo N =
        gaugeRhsOne N := by
  unfold gaugeCoeffOne gaugeCoeffTwo
  unfold gaugeDet at h ⊢
  exact cramer_two h

/-- The correction coefficients are uniformly bounded where the determinant is controlled. -/
theorem exists_abs_gaugeCoeff_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
    gaugeLimitDet / 2 ≤ gaugeDet N → |gaugeCoeffOne N| ≤ B ∧ |gaugeCoeffTwo N| ≤ B := by
  obtain ⟨R, hR0, hR⟩ := exists_abs_gaugeRhs_le
  have hD := gaugeLimitDet_pos
  refine ⟨2 * R / (gaugeLimitDet / 2), by positivity, fun N hN hdet => ?_⟩
  obtain ⟨h0, h1⟩ := hR N hN
  have hdetpos : 0 < gaugeDet N := lt_of_lt_of_le (by linarith) hdet
  obtain ⟨a1, a1'⟩ := gaugeMomentZero_mem (3 / 10) (7 / 20) N
  obtain ⟨a2, a2'⟩ := gaugeMomentZero_mem (2 / 5) (9 / 20) N
  obtain ⟨b1, b1'⟩ := gaugeMomentOne_mem (3 / 10) (7 / 20) N
  obtain ⟨b2, b2'⟩ := gaugeMomentOne_mem (2 / 5) (9 / 20) N
  have hnum : ∀ x y u v : ℝ, |x| ≤ R → |y| ≤ R → 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
      |x * u - v * y| ≤ 2 * R := by
    intro x y u v hx hy hu hu' hv hv'
    calc |x * u - v * y| ≤ |x * u| + |v * y| := abs_sub _ _
      _ = |x| * u + v * |y| := by rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hv]
      _ ≤ R * 1 + 1 * R := by gcongr
      _ = 2 * R := by ring
  have hdiv : ∀ z : ℝ, |z| ≤ 2 * R → |z / gaugeDet N| ≤ 2 * R / (gaugeLimitDet / 2) := by
    intro z hz
    rw [abs_div, abs_of_pos hdetpos]
    calc |z| / gaugeDet N ≤ 2 * R / gaugeDet N := by gcongr
      _ ≤ 2 * R / (gaugeLimitDet / 2) := by gcongr
  exact ⟨hdiv _ (hnum _ _ _ _ h0 h1 b2 b2' a2 a2'),
    hdiv _ (by rw [abs_sub_comm]; exact hnum _ _ _ _ h0 h1 b1 b1' a1 a1')⟩

end

end RHTower
