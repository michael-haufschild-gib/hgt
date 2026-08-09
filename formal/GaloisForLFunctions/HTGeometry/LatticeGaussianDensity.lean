import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity

/-!
# A fine lattice keeps a fixed share of standard Gaussian mass

Rescaling a full lattice by `1/t` and taking the `δ/t`-neighbourhood of the rescaled points keeps
a share of Gaussian mass bounded below independently of `t`: the number of usable lattice points
grows like `t^r` while each contributes mass of order `(δ/t)^r`.

The one-dimensional input is a shifted small-interval bound — the standard Gaussian density is
bounded below on `|x| ≤ 2`, so an interval of half-width `ρ ≤ 1` centred within distance `1` of the
origin has measure at least `2 c ρ`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Lower bound for the standard Gaussian density on the interval `|x| ≤ 2`. -/
def gaussianFloorTwo : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-2)

theorem gaussianFloorTwo_pos : 0 < gaussianFloorTwo := by
  have h : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussianFloorTwo]
  positivity

theorem gaussianPDFReal_ge_floorTwo {x : ℝ} (hx : |x| ≤ 2) :
    gaussianFloorTwo ≤ gaussianPDFReal 0 1 x := by
  have hsq : x ^ 2 ≤ 4 := by
    have := sq_abs x
    nlinarith [abs_nonneg x, hx]
  have hexp : Real.exp (-2) ≤ Real.exp (-(x - 0) ^ 2 / 2) := by
    apply Real.exp_le_exp.mpr
    have : (x - 0) ^ 2 = x ^ 2 := by ring
    rw [this]
    linarith
  have hpos : (0 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ := by
    have h : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [gaussianPDFReal, gaussianFloorTwo]
  have hcast : (2 : ℝ) * Real.pi * ((1 : ℝ≥0) : ℝ) = 2 * Real.pi := by norm_num
  rw [hcast]
  have hcast2 : (2 : ℝ) * ((1 : ℝ≥0) : ℝ) = 2 := by norm_num
  rw [hcast2]
  exact mul_le_mul_of_nonneg_left hexp hpos.le

/-- A shifted small interval keeps a fixed share of one-dimensional Gaussian mass. -/
theorem gaussianReal_Icc_shifted_lower {a rho : ℝ} (ha : |a| ≤ 1)
    (_hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    ENNReal.ofReal (2 * gaussianFloorTwo * rho) ≤
      gaussianReal 0 1 (Set.Icc (a - rho) (a + rho)) := by
  classical
  rw [gaussianReal_apply 0 (by norm_num) (Set.Icc (a - rho) (a + rho))]
  have hlow : ∀ x ∈ Set.Icc (a - rho) (a + rho),
      ENNReal.ofReal gaussianFloorTwo ≤ gaussianPDF 0 1 x := by
    intro x hx
    have hxabs : |x| ≤ 2 := by
      rw [abs_le]
      have h1 := hx.1
      have h2 := hx.2
      have ha1 : -1 ≤ a := neg_le_of_abs_le ha
      have ha2 : a ≤ 1 := le_of_abs_le ha
      constructor <;> linarith
    rw [gaussianPDF]
    exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_ge_floorTwo hxabs)
  have hmono : ∫⁻ _x in Set.Icc (a - rho) (a + rho), ENNReal.ofReal gaussianFloorTwo ≤
      ∫⁻ x in Set.Icc (a - rho) (a + rho), gaussianPDF 0 1 x := by
    refine setLIntegral_mono_ae (by fun_prop) ?_
    filter_upwards with x hx using hlow x hx
  refine le_trans ?_ hmono
  rw [setLIntegral_const, Real.volume_Icc]
  have hlen : a + rho - (a - rho) = 2 * rho := by ring
  rw [hlen, ← ENNReal.ofReal_mul gaussianFloorTwo_pos.le]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [gaussianFloorTwo_pos]

/-- A shifted small sup-norm ball keeps a fixed share of product-Gaussian mass. -/
theorem measure_pi_gaussian_shifted_ball_lower (r : ℕ) {y : Fin r → ℝ} (hy : ‖y‖ ≤ 1)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * rho) ^ r) ≤
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) (closedBall y rho) := by
  classical
  have hbox : (Set.univ.pi fun i : Fin r => Set.Icc (y i - rho) (y i + rho)) ⊆
      closedBall y rho := by
    intro x hx
    rw [mem_closedBall, dist_pi_le_iff hrho0]
    intro i
    have := hx i (Set.mem_univ i)
    rw [Real.dist_eq, abs_le]
    constructor <;> [linarith [this.1]; linarith [this.2]]
  refine le_trans ?_ (measure_mono hbox)
  rw [Measure.pi_pi]
  have hcoord : ∀ i : Fin r, |y i| ≤ 1 := by
    intro i
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    linarith
  calc ENNReal.ofReal ((2 * gaussianFloorTwo * rho) ^ r)
      = ∏ _i : Fin r, ENNReal.ofReal (2 * gaussianFloorTwo * rho) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow (by positivity [gaussianFloorTwo_pos])]
    _ ≤ ∏ i : Fin r, gaussianReal 0 1 (Set.Icc (y i - rho) (y i + rho)) := by
        refine Finset.prod_le_prod' fun i _ => ?_
        exact gaussianReal_Icc_shifted_lower (hcoord i) hrho0 hrho1


/-! ## Separated centres -/

/-- A finite family of `σ`-separated centres inside the unit ball carries at least its cardinality
times the shifted small-ball mass. -/
theorem measure_pi_gaussian_separatedCenters_lower (r : ℕ) (S : Finset (Fin r → ℝ))
    (hS1 : ∀ y ∈ S, ‖y‖ ≤ 1)
    {sigma rho : ℝ} (hsep : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → sigma ≤ dist y z)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hrhosep : 2 * rho < sigma) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal ((2 * gaussianFloorTwo * rho) ^ r) ≤
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) (⋃ y ∈ S, closedBall y rho) := by
  classical
  have hdisj : (S : Set (Fin r → ℝ)).PairwiseDisjoint fun y => closedBall y rho := by
    intro y hy z hz hyz
    refine Metric.closedBall_disjoint_closedBall ?_
    have := hsep y hy z hz hyz
    linarith
  rw [measure_biUnion_finset hdisj (fun y _ => measurableSet_closedBall)]
  calc (S.card : ℝ≥0∞) * ENNReal.ofReal ((2 * gaussianFloorTwo * rho) ^ r)
      = ∑ _y ∈ S, ENNReal.ofReal ((2 * gaussianFloorTwo * rho) ^ r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ S, (Measure.pi fun _ : Fin r => gaussianReal 0 1) (closedBall y rho) := by
        refine Finset.sum_le_sum fun y hy => ?_
        exact measure_pi_gaussian_shifted_ball_lower r (hS1 y hy) hrho0 hrho1

/-! ## Rescaled full lattices -/

variable {r : ℕ}

/-- The rescaled lattice points inside the unit ball, indexed by an integer box. -/
def scaledLatticeCenters (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (t : ℝ) (N : ℕ) :
    Finset (Fin r → ℝ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin r => Finset.Icc (-(N : ℤ)) (N : ℤ)).image
    fun n => t⁻¹ • A (fun i => ((n i : ℤ) : ℝ))

theorem card_scaledLatticeCenters (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (hAinj : Function.Injective A) {t : ℝ} (ht : t ≠ 0) (N : ℕ) :
    (scaledLatticeCenters A t N).card = (2 * N + 1) ^ r := by
  classical
  have hinj : Set.InjOn
      (fun n : Fin r → ℤ => t⁻¹ • A (fun i => ((n i : ℤ) : ℝ)))
      (Fintype.piFinset fun _ : Fin r => Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
    intro m _ n _ hmn
    have hA : A (fun i => ((m i : ℤ) : ℝ)) = A (fun i => ((n i : ℤ) : ℝ)) := by
      have := congrArg (fun z => t • z) hmn
      simpa [smul_smul, mul_inv_cancel₀ ht] using this
    have hcast : (fun i => ((m i : ℤ) : ℝ)) = fun i => ((n i : ℤ) : ℝ) := hAinj hA
    funext i
    have := congrFun hcast i
    exact_mod_cast this
  rw [scaledLatticeCenters, Finset.card_image_of_injOn hinj]
  have hcard : ∀ _i : Fin r, (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    intro _i
    rw [Int.card_Icc]
    omega
  rw [Fintype.card_piFinset]
  rw [Finset.prod_congr rfl fun i _ => hcard i]
  simp


theorem norm_intVector_le {N : ℕ} {n : Fin r → ℤ}
    (hn : ∀ i, n i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    ‖(fun i => ((n i : ℤ) : ℝ))‖ ≤ (N : ℝ) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have := Finset.mem_Icc.mp (hn i)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact_mod_cast this.1
  · exact_mod_cast this.2

theorem one_le_norm_intVector_sub {m n : Fin r → ℤ} (hmn : m ≠ n) :
    (1 : ℝ) ≤ ‖(fun i => ((m i : ℤ) : ℝ)) - fun i => ((n i : ℤ) : ℝ)‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ n i := Function.ne_iff.mp hmn
  have hle : ‖((fun i => ((m i : ℤ) : ℝ)) - fun i => ((n i : ℤ) : ℝ)) i‖ ≤
      ‖(fun i => ((m i : ℤ) : ℝ)) - fun i => ((n i : ℤ) : ℝ)‖ :=
    norm_le_pi_norm _ i
  refine le_trans ?_ hle
  have hne : m i - n i ≠ 0 := sub_ne_zero.mpr hi
  have hone : (1 : ℤ) ≤ |m i - n i| := by
    rcases lt_or_gt_of_ne hne with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  have hcast : (1 : ℝ) ≤ |((m i : ℝ)) - ((n i : ℝ))| := by
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|m i - n i| : ℤ) : ℝ) := Int.cast_le.mpr hone
    rwa [Int.cast_abs, Int.cast_sub, Int.cast_one] at h2
  simpa [Pi.sub_apply, Real.norm_eq_abs] using hcast

theorem scaledLatticeCenters_norm_le (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    {M t : ℝ} (hM : ∀ x, ‖A x‖ ≤ M * ‖x‖) (hMpos : 0 < M) (ht : 0 < t)
    {N : ℕ} (hN : (N : ℝ) * M ≤ t) :
    ∀ y ∈ scaledLatticeCenters A t N, ‖y‖ ≤ 1 := by
  classical
  intro y hy
  rw [scaledLatticeCenters, Finset.mem_image] at hy
  obtain ⟨n, hn, rfl⟩ := hy
  have hnmem : ∀ i, n i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro i
    exact (Fintype.mem_piFinset.mp hn) i
  have hnorm : ‖(fun i => ((n i : ℤ) : ℝ))‖ ≤ (N : ℝ) := norm_intVector_le hnmem
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < t⁻¹)]
  have hAle : ‖A (fun i => ((n i : ℤ) : ℝ))‖ ≤ M * (N : ℝ) := by
    refine le_trans (hM _) ?_
    exact mul_le_mul_of_nonneg_left hnorm hMpos.le
  have hMN : M * (N : ℝ) ≤ t := by linarith [hN]
  calc t⁻¹ * ‖A (fun i => ((n i : ℤ) : ℝ))‖ ≤ t⁻¹ * t := by
        exact mul_le_mul_of_nonneg_left (le_trans hAle hMN) (by positivity)
    _ = 1 := by field_simp

theorem scaledLatticeCenters_separated (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    {sigma t : ℝ} (hsigpos : 0 < sigma) (hsig : ∀ x, sigma * ‖x‖ ≤ ‖A x‖) (ht : 0 < t) (N : ℕ) :
    ∀ y ∈ scaledLatticeCenters A t N, ∀ z ∈ scaledLatticeCenters A t N, y ≠ z →
      sigma / t ≤ dist y z := by
  classical
  intro y hy z hz hyz
  rw [scaledLatticeCenters, Finset.mem_image] at hy hz
  obtain ⟨m, -, rfl⟩ := hy
  obtain ⟨n, -, rfl⟩ := hz
  have hmn : m ≠ n := by
    intro h
    exact hyz (by rw [h])
  have hdiff : (t⁻¹ • A (fun i => ((m i : ℤ) : ℝ))) - (t⁻¹ • A (fun i => ((n i : ℤ) : ℝ))) =
      t⁻¹ • A ((fun i => ((m i : ℤ) : ℝ)) - fun i => ((n i : ℤ) : ℝ)) := by
    rw [← smul_sub, ← map_sub]
  rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < t⁻¹)]
  have hlow : sigma ≤ ‖A ((fun i => ((m i : ℤ) : ℝ)) - fun i => ((n i : ℤ) : ℝ))‖ := by
    refine le_trans ?_ (hsig _)
    have hge := one_le_norm_intVector_sub hmn
    nlinarith [hsigpos]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **Fine-lattice Gaussian density.**  The `δ/t`-neighbourhood of the `1/t`-rescaled lattice keeps
a share of standard Gaussian mass bounded below independently of `t`. -/
theorem measure_pi_gaussian_scaledLattice_lower
    (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ)) (hAinj : Function.Injective A)
    {sigma M : ℝ} (hsigpos : 0 < sigma) (hMpos : 0 < M)
    (hsig : ∀ x, sigma * ‖x‖ ≤ ‖A x‖) (hM : ∀ x, ‖A x‖ ≤ M * ‖x‖)
    {delta t : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) (h2delta : 2 * delta < sigma)
    (ht1 : 1 ≤ t) (htM : M ≤ t) :
    ENNReal.ofReal ((2 * gaussianFloorTwo * delta / M) ^ r) ≤
      (Measure.pi fun _ : Fin r => gaussianReal 0 1)
        (⋃ y ∈ scaledLatticeCenters A t ⌊t / M⌋₊, closedBall y (delta / t)) := by
  classical
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  set N : ℕ := ⌊t / M⌋₊ with hN
  have hNle : (N : ℝ) * M ≤ t := by
    have hfl : (N : ℝ) ≤ t / M := Nat.floor_le (by positivity)
    calc (N : ℝ) * M ≤ (t / M) * M := mul_le_mul_of_nonneg_right hfl hMpos.le
      _ = t := by field_simp
  have hrho0 : (0 : ℝ) ≤ delta / t := by positivity
  have hrho1 : delta / t ≤ 1 := by
    rw [div_le_one ht0]
    linarith
  have hsepbound : 2 * (delta / t) < sigma / t := by
    rw [show 2 * (delta / t) = (2 * delta) / t by ring]
    gcongr
  have hmain := measure_pi_gaussian_separatedCenters_lower r
    (scaledLatticeCenters A t N)
    (scaledLatticeCenters_norm_le A hM hMpos ht0 hNle)
    (scaledLatticeCenters_separated A hsigpos hsig ht0 N) hrho0 hrho1 hsepbound
  refine le_trans ?_ hmain
  rw [card_scaledLatticeCenters A hAinj ht0.ne' N]
  have hcount : t / M ≤ ((2 * N + 1 : ℕ) : ℝ) := by
    have hfl : t / M - 1 < (N : ℝ) := Nat.sub_one_lt_floor (t / M)
    have hge1 : (1 : ℝ) ≤ t / M := (one_le_div hMpos).mpr htM
    push_cast
    linarith
  have hfloorpos : (0 : ℝ) < 2 * gaussianFloorTwo * delta := by
    have := gaussianFloorTwo_pos
    positivity
  have hposdelta : (0 : ℝ) < 2 * gaussianFloorTwo * (delta / t) := by
    have := gaussianFloorTwo_pos
    positivity
  have hcast : (((2 * N + 1) ^ r : ℕ) : ℝ) = ((2 * N + 1 : ℕ) : ℝ) ^ r := by push_cast; ring
  have hreal : (2 * gaussianFloorTwo * delta / M) ^ r ≤
      (((2 * N + 1) ^ r : ℕ) : ℝ) * (2 * gaussianFloorTwo * (delta / t)) ^ r := by
    have heq : (t / M) * (2 * gaussianFloorTwo * (delta / t)) =
        2 * gaussianFloorTwo * delta / M := by field_simp
    have hstep : (2 * gaussianFloorTwo * delta / M) ^ r =
        (t / M) ^ r * (2 * gaussianFloorTwo * (delta / t)) ^ r := by
      rw [← mul_pow, heq]
    rw [hstep, hcast]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (by positivity) hcount r
  calc ENNReal.ofReal ((2 * gaussianFloorTwo * delta / M) ^ r)
      ≤ ENNReal.ofReal ((((2 * N + 1) ^ r : ℕ) : ℝ) *
          (2 * gaussianFloorTwo * (delta / t)) ^ r) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = (((2 * N + 1) ^ r : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal ((2 * gaussianFloorTwo * (delta / t)) ^ r) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end

end GaloisForLFunctions.HTGeometry


