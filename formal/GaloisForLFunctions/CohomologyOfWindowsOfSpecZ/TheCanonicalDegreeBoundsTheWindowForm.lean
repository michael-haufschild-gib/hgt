import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.TheCanonicalClassOfAWindow

/-!
# The canonical degree bounds the window form

On a window of length `A` every term of Weil's form but three is a jump count: the archimedean
constant `Ω(0)`, the canonical density `k_A ≤ 2ψ_{1/2}(e^A)`, and the negative pole square
`½⟨2 sinh(u/2), H⟩² ≤ 2A sinh²(A/2)‖H‖²`. Since `2ψ_{1/2}(e^A) − Ω(0)` is the canonical degree:

* **Semiboundedness** (`weilQuad_ge_neg_windowFloor`):
  `Q(H) ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²` on window tests. The window `h¹` is bounded below by
  minus its canonical degree and the pole capacity.
* **The second-order pencil** (`pencil_nonneg`): for `κ > 0`, `p ≥ 0` and `c ≥ κ·(deg K_A +
  2A sinh²(A/2))`, `κQ(H) + c∫e^{−py}H(y)² dy ≥ 0` on window tests. The second-order term of the
  degeneration at the critical curve, `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`, is therefore nonnegative on
  every window as soon as `K ≤ βJ/(κ(deg K_A + 2A sinh²(A/2)))`: the prime-free term — the
  dimension `β` times the Jordan count `J` — pays the whole arithmetic of a window at bounded
  dilation constant. All of RH sits in `K → ∞`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.CohomologyOfWindowsOfSpecZ

open SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {A : ℝ} {H : ℝ → ℝ}

/-- The **window floor** `deg K_A + 2A sinh²(A/2)`. -/
def windowFloor (A : ℝ) : ℝ := canonicalDegree A + 2 * A * Real.sinh (A / 2) ^ 2

theorem levyJump_nonneg (g : ℝ → ℝ) : 0 ≤ levyJump g := ENNReal.toReal_nonneg

theorem halfChebyshev_mono : Monotone halfChebyshev := fun _ _ h =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor h))
    fun n _ _ => primeJumpWeight_nonneg n

/-- On the window the canonical density is at most `2ψ_{1/2}(e^A)`. -/
theorem canonicalDensity_le {u : ℝ} (hu : u ∈ Icc (-A) 0) :
    canonicalDensity A u ≤ 2 * halfChebyshev (Real.exp A) := by
  rw [canonicalDensity_eq_halfChebyshev hu]
  have h1 := halfChebyshev_mono (Real.exp_le_exp.mpr (show -u ≤ A by linarith [hu.1]))
  have h2 := halfChebyshev_mono (Real.exp_le_exp.mpr (show A + u ≤ A by linarith [hu.2]))
  linarith

theorem integrable_canonicalDensity_mul (hc : Continuous H) (hcs : HasCompactSupport H) (A : ℝ) :
    Integrable fun u => canonicalDensity A u * H u ^ 2 := by
  have iH := integrable_sq hc hcs
  simp_rw [canonicalDensity, Finset.sum_mul]
  refine integrable_finsetSum _ fun n _ => ?_
  simp_rw [mul_assoc]
  refine Integrable.const_mul ?_ _
  have hpt : (fun u => inWindowCount A (Real.log n) u * H u ^ 2) = fun u =>
      (Icc (-A) (-Real.log n)).indicator (fun u => H u ^ 2) u +
        (Icc (Real.log n - A) 0).indicator (fun u => H u ^ 2) u :=
    funext fun u => inWindowCount_mul A (Real.log n) u fun u => H u ^ 2
  rw [hpt]
  exact (iH.indicator measurableSet_Icc).add (iH.indicator measurableSet_Icc)

/-- The canonical density costs at most `2ψ_{1/2}(e^A)‖H‖²`. -/
theorem integral_canonicalDensity_mul_le (hH : IsWindowTest A H) :
    ∫ u, canonicalDensity A u * H u ^ 2 ≤ 2 * halfChebyshev (Real.exp A) * ∫ u, H u ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_canonicalDensity_mul hH.continuous hH.hasCompactSupport A)
    ((integrable_sq hH.continuous hH.hasCompactSupport).const_mul _) fun u => ?_
  by_cases hu : u ∈ Icc (-A) 0
  · exact mul_le_mul_of_nonneg_right (canonicalDensity_le hu) (sq_nonneg _)
  · simp [hH.vanish u hu]

/-- On the window `|2 sinh(u/2)|² ≤ 4 sinh²(A/2)`. -/
theorem sq_two_sinh_le {u : ℝ} (hu : u ∈ Icc (-A) 0) :
    (2 * Real.sinh (u / 2)) ^ 2 ≤ 4 * Real.sinh (A / 2) ^ 2 := by
  have h1 : |Real.sinh (u / 2)| ≤ Real.sinh (A / 2) := by
    rw [Real.abs_sinh, Real.sinh_le_sinh, abs_le]
    constructor <;> linarith [hu.1, hu.2]
  have h2 : Real.sinh (u / 2) ^ 2 ≤ Real.sinh (A / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

/-- Pointwise AM–GM integrated: `2t|⟨2 sinh(u/2), H⟩| ≤ t²‖H‖² + 4A sinh²(A/2)` for `t ≥ 0`. -/
theorem two_mul_abs_sinhPairing_le (hH : IsWindowTest A H) (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) :
    2 * t * |sinhPairing H| ≤ t ^ 2 * (∫ u, H u ^ 2) + 4 * A * Real.sinh (A / 2) ^ 2 := by
  have iH := integrable_sq hH.continuous hH.hasCompactSupport
  have iP : Integrable fun u => H u * (2 * Real.sinh (u / 2)) :=
    (hH.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hH.hasCompactSupport.mul_right
  have iI : Integrable ((Icc (-A) 0).indicator fun _ => 4 * Real.sinh (A / 2) ^ 2) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp [Real.volume_Icc]))
  have hpt : ∀ u, 2 * t * |H u * (2 * Real.sinh (u / 2))| ≤
      t ^ 2 * H u ^ 2 + (Icc (-A) 0).indicator (fun _ => 4 * Real.sinh (A / 2) ^ 2) u := fun u => by
    by_cases hu : u ∈ Icc (-A) 0
    · rw [indicator_of_mem hu, abs_mul]
      have hs := sq_two_sinh_le hu
      have hb : |2 * Real.sinh (u / 2)| ^ 2 ≤ 4 * Real.sinh (A / 2) ^ 2 := by rwa [sq_abs]
      nlinarith [sq_nonneg (t * |H u| - |2 * Real.sinh (u / 2)|), abs_nonneg (H u),
        abs_nonneg (2 * Real.sinh (u / 2)), sq_abs (H u)]
    · rw [indicator_of_notMem hu, hH.vanish u hu]; simp
  calc 2 * t * |sinhPairing H| ≤ 2 * t * ∫ u, |H u * (2 * Real.sinh (u / 2))| :=
        mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (by positivity)
    _ = ∫ u, 2 * t * |H u * (2 * Real.sinh (u / 2))| := (integral_const_mul _ _).symm
    _ ≤ ∫ u, (t ^ 2 * H u ^ 2 +
          (Icc (-A) 0).indicator (fun _ => 4 * Real.sinh (A / 2) ^ 2) u) :=
        integral_mono (iP.abs.const_mul _) ((iH.const_mul _).add iI) hpt
    _ = t ^ 2 * (∫ u, H u ^ 2) + 4 * A * Real.sinh (A / 2) ^ 2 := by
        rw [integral_add (iH.const_mul _) iI, integral_const_mul,
          integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
          smul_eq_mul]
        ring

/-- **The pole capacity of a window**: `⟨2 sinh(u/2), H⟩² ≤ 4A sinh²(A/2)‖H‖²`. -/
theorem sinhPairing_sq_le (hH : IsWindowTest A H) (hA : 0 ≤ A) :
    sinhPairing H ^ 2 ≤ 4 * A * Real.sinh (A / 2) ^ 2 * ∫ u, H u ^ 2 := by
  set M := ∫ u, H u ^ 2
  set G := 4 * A * Real.sinh (A / 2) ^ 2
  have hM : 0 ≤ M := integral_nonneg fun u => sq_nonneg _
  have hG : 0 ≤ G := by positivity
  have hq : ∀ t : ℝ, 0 ≤ M * (t * t) + 2 * (-|sinhPairing H|) * t + G := fun t => by
    rcases le_total 0 t with ht | ht
    · have := two_mul_abs_sinhPairing_le hH hA ht
      nlinarith
    · nlinarith [abs_nonneg (sinhPairing H), mul_self_nonneg t]
  have h := abs_le_sqrt_mul_sqrt_of_quadratic_nonneg hM hq
  rw [abs_neg, abs_abs] at h
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow, Real.sq_sqrt hM, Real.sq_sqrt hG] at h2
  linarith

/-- **The window form is bounded below by the canonical degree**:
`Q(H) ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²` on window tests. -/
theorem weilQuad_ge_neg_windowFloor (hH : IsWindowTest A H) (hA : 0 ≤ A) :
    -(windowFloor A * ∫ u, H u ^ 2) ≤ weilQuad H := by
  rw [weilQuad_eq_fold_sub_canonical hH]
  have hJ := levyJump_nonneg H
  have hF : 0 ≤ ∑ n ∈ Finset.Icc 2 (windowLevel A),
      primeJumpWeight n * foldEnergy A (Real.log n) H :=
    Finset.sum_nonneg fun n _ => mul_nonneg (primeJumpWeight_nonneg n) (foldEnergy_nonneg _ _ _)
  have hk := integral_canonicalDensity_mul_le hH
  have hs := sinhPairing_sq_le hH hA
  have hc := sq_nonneg (coshPairing H)
  rw [windowFloor, canonicalDegree_eq_halfChebyshev]
  nlinarith

theorem windowFloor_nonneg (hA : 0 ≤ A) : 0 ≤ windowFloor A :=
  add_nonneg (canonicalDegree_pos A).le (by positivity)

/-- **The second-order pencil is nonnegative at bounded dilation constant**: for `κ > 0`, `p ≥ 0`
and `c ≥ κ(deg K_A + 2A sinh²(A/2))`, `κQ(H) + c∫e^{−py}H(y)² ≥ 0` on window tests. -/
theorem pencil_nonneg (hH : IsWindowTest A H) (hA : 0 ≤ A) {κ c p : ℝ} (hκ : 0 < κ)
    (hp : 0 ≤ p) (hc : κ * windowFloor A ≤ c) :
    0 ≤ κ * weilQuad H + c * ∫ y, Real.exp (-(p * y)) * H y ^ 2 := by
  have iH := integrable_sq hH.continuous hH.hasCompactSupport
  have hHc := hH.continuous
  have hcont : Continuous fun y => Real.exp (-(p * y)) * H y ^ 2 := by fun_prop
  have hcs : HasCompactSupport fun y => Real.exp (-(p * y)) * H y ^ 2 :=
    HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => by
      rw [hH.vanish y hy]; ring
  have iE : Integrable fun y => Real.exp (-(p * y)) * H y ^ 2 :=
    hcont.integrable_of_hasCompactSupport hcs
  have hmono : ∫ y, H y ^ 2 ≤ ∫ y, Real.exp (-(p * y)) * H y ^ 2 :=
    integral_mono iH iE fun y => by
      by_cases hy : y ∈ Icc (-A) 0
      · have : 1 ≤ Real.exp (-(p * y)) := Real.one_le_exp (by nlinarith [hy.2])
        nlinarith [sq_nonneg (H y)]
      · simp [hH.vanish y hy]
  have hQ := mul_le_mul_of_nonneg_left (weilQuad_ge_neg_windowFloor hH hA) hκ.le
  have hW := windowFloor_nonneg hA
  have hM : 0 ≤ ∫ y, H y ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hc0 : 0 ≤ c := (mul_nonneg hκ.le hW).trans hc
  have h1 := mul_le_mul_of_nonneg_left hmono hc0
  have h2 := mul_le_mul_of_nonneg_right hc hM
  linarith

end GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
