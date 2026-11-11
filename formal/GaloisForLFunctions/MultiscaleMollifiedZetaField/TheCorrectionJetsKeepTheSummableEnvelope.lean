import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedAmplitudeIsHolomorphic
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergCorrectionKeepsItsSummableEnvelope

/-!
# A summable envelope for normalized correction derivatives

The normalized correction is entire in its shift. On a unit disk, the
original absolute fibre sum bounds this continuation uniformly in the
cutoff. Cauchy's estimate therefore controls every normalized jet by
the same summable envelope, with a factorial constant.
-/

open ArithmeticFunction Complex Filter Metric Set Topology
open RHTower.Sieve
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The entire extension of one localized amplitude. -/
def complexLocalizedSelbergAmplitude (r n : ℕ) (z : ℂ) : ℂ := by
  classical
  exact if primeSupportedOn r n then complexShiftedSelbergAmplitude n z else 0

/-- The entire extension of a squarefree-support correction fibre. -/
def complexSelbergCorrectionWeight (r u v : ℕ) (z : ℂ) : ℂ :=
  (((moebius r : ℤ) : ℂ) / (r : ℂ) ^ 2) *
    complexLocalizedSelbergAmplitude r u z * complexLocalizedSelbergAmplitude r v z

theorem complexLocalizedSelbergAmplitude_ofReal (r n : ℕ) (c : ℝ) :
    complexLocalizedSelbergAmplitude r n (c : ℂ) = (localizedShiftedSelbergAmplitude c r n : ℂ) := by
  classical
  by_cases h : primeSupportedOn r n <;>
    simp [complexLocalizedSelbergAmplitude, localizedShiftedSelbergAmplitude, h,
      complexShiftedSelbergAmplitude_ofReal]

theorem complexSelbergCorrectionWeight_ofReal (r u v : ℕ) (c : ℝ) :
    complexSelbergCorrectionWeight r u v (c : ℂ) = (shiftedSelbergCorrectionWeight c r u v : ℂ) := by
  simp only [complexSelbergCorrectionWeight, complexLocalizedSelbergAmplitude_ofReal,
    shiftedSelbergCorrectionWeight, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_intCast, Complex.ofReal_natCast]

theorem differentiable_complexLocalizedSelbergAmplitude (r n : ℕ) :
    Differentiable ℂ (complexLocalizedSelbergAmplitude r n) := by
  classical
  by_cases h : primeSupportedOn r n
  · simpa only [complexLocalizedSelbergAmplitude, if_pos h] using
      differentiable_complexShiftedSelbergAmplitude n
  · simpa only [complexLocalizedSelbergAmplitude, if_neg h] using
      (differentiable_const : Differentiable ℂ (fun _ : ℂ => (0 : ℂ)))

theorem differentiable_complexSelbergCorrectionWeight (r u v : ℕ) :
    Differentiable ℂ (complexSelbergCorrectionWeight r u v) :=
  ((differentiable_complexLocalizedSelbergAmplitude r u).const_mul _).mul
    (differentiable_complexLocalizedSelbergAmplitude r v)

private theorem norm_complexLocalizedSelbergAmplitude_log_shift_le {N : ℕ} (hN : 1 < N)
    (z : ℂ) (r : ℕ) {n : ℕ} (hn : n ≤ N) :
    ‖complexLocalizedSelbergAmplitude r n (z / (Real.log N : ℂ))‖ ≤
      Real.exp (2 * ‖z‖) * |localizedReciprocalMoebiusAmplitude r n| := by
  classical
  change ‖if primeSupportedOn r n then complexShiftedSelbergAmplitude n (z / (Real.log N : ℂ)) else 0‖ ≤
    Real.exp (2 * ‖z‖) * |if primeSupportedOn r n then reciprocalMoebiusAmplitude n else 0|
  by_cases h : primeSupportedOn r n
  · simpa only [if_pos h] using norm_complexShiftedSelbergAmplitude_log_shift_le hN z hn
  · simp only [if_neg h, norm_zero, abs_zero, mul_zero, le_refl]

/-- The real absolute fibre envelope also bounds the complex normalized continuation. -/
theorem norm_complexSelbergCorrectionWeight_log_shift_le {N : ℕ} (hN : 1 < N)
    (z : ℂ) (r : ℕ) {u v : ℕ} (hu : u ≤ N) (hv : v ≤ N) :
    ‖complexSelbergCorrectionWeight r u v (z / (Real.log N : ℂ))‖ ≤
      Real.exp (4 * ‖z‖) * |selbergCorrectionWeight r u v| := by
  have hu' := norm_complexLocalizedSelbergAmplitude_log_shift_le hN z r hu
  have hv' := norm_complexLocalizedSelbergAmplitude_log_shift_le hN z r hv
  unfold complexSelbergCorrectionWeight
  rw [norm_mul, norm_mul]
  have hscalar : ‖((moebius r : ℤ) : ℂ) / (r : ℂ) ^ 2‖ =
      |((moebius r : ℤ) : ℝ) / (r : ℝ) ^ 2| := by
    rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_intCast, abs_div,
      abs_pow, abs_of_nonneg (Nat.cast_nonneg r)]
    norm_cast
  rw [hscalar]
  calc
    _ ≤ |((moebius r : ℤ) : ℝ) / (r : ℝ) ^ 2| *
      (Real.exp (2 * ‖z‖) * |localizedReciprocalMoebiusAmplitude r u|) *
      (Real.exp (2 * ‖z‖) * |localizedReciprocalMoebiusAmplitude r v|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hu' (abs_nonneg _)) hv'
          (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (2 * ‖z‖) * Real.exp (2 * ‖z‖) = Real.exp (4 * ‖z‖) := by
        rw [← Real.exp_add]
        congr 1
        ring
      unfold selbergCorrectionWeight
      rw [abs_mul, abs_mul, ← he]
      ring

/-- Cauchy's estimate controls every normalized correction jet by one fibre majorant. -/
theorem norm_normalizedCorrectionJet_le {N : ℕ} (hN : 1 < N)
    (C : ℂ) (j r : ℕ) {u v : ℕ} (hu : u ≤ N) (hv : v ≤ N) :
    ‖iteratedDeriv j (fun z => complexSelbergCorrectionWeight r u v
      (z / (Real.log N : ℂ))) C‖ ≤
      (j.factorial : ℝ) * Real.exp (4 * (‖C‖ + 1)) * |selbergCorrectionWeight r u v| := by
  have hf : Differentiable ℂ (fun z => complexSelbergCorrectionWeight r u v
      (z / (Real.log N : ℂ))) :=
    (differentiable_complexSelbergCorrectionWeight r u v).comp
      (differentiable_id.div_const _)
  have hb : ∀ z ∈ sphere C 1,
      ‖complexSelbergCorrectionWeight r u v (z / (Real.log N : ℂ))‖ ≤
        Real.exp (4 * (‖C‖ + 1)) * |selbergCorrectionWeight r u v| := by
    intro z hz
    have hz1 : ‖z - C‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hzn : ‖z‖ ≤ ‖C‖ + 1 := by
      have hh := norm_add_le (z - C) C
      rw [sub_add_cancel, hz1] at hh
      linarith only [hh]
    refine (norm_complexSelbergCorrectionWeight_log_shift_le hN z r hu hv).trans ?_
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzn (by norm_num))
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j zero_lt_one
    hf.diffContOnCl hb
  simpa only [one_pow, div_one, mul_assoc] using hh


private theorem iteratedDeriv_succ_sub_constant (f : ℂ → ℂ) (a : ℂ) (j : ℕ) :
    iteratedDeriv (j + 1) (fun z => f z - a) = iteratedDeriv (j + 1) f := by
  induction j with
  | zero =>
      simp only [Nat.zero_add, iteratedDeriv_one]
      funext z
      exact deriv_sub_const a
  | succ j ih => rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]

/-- Every positive-order jet of an entire function under reciprocal-logarithmic dilation vanishes. -/
theorem tendsto_entire_normalized_jet_succ {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (C : ℂ) (j : ℕ) :
    Tendsto (fun N : ℕ => iteratedDeriv (j + 1)
      (fun z => f (z / (Real.log N : ℂ))) C) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η : ℝ := ε / (2 * ((j + 1).factorial : ℝ))
  have hfact : (0 : ℝ) < (j + 1).factorial := by positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp (hf 0).continuousAt η hη
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, hlog.eventually_gt_atTop ((‖C‖ + 1) / δ)] with N hN hlarge
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hd : Differentiable ℂ (fun z => f (z / (Real.log N : ℂ)) - f 0) :=
    (hf.comp (differentiable_id.div_const _)).sub_const _
  have hb : ∀ z ∈ sphere C 1, ‖f (z / (Real.log N : ℂ)) - f 0‖ ≤ η := by
    intro z hz
    have hz1 : ‖z - C‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hzn : ‖z‖ ≤ ‖C‖ + 1 := by
      have hh := norm_add_le (z - C) C
      rw [sub_add_cancel, hz1] at hh
      linarith only [hh]
    have hsmall : dist (z / (Real.log N : ℂ)) 0 < δ := by
      rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_of_nonneg hl.le]
      refine (div_le_div_of_nonneg_right hzn hl.le).trans_lt ?_
      apply (div_lt_iff₀ hl).2
      simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hlarge
    have hh := hclose hsmall
    simpa only [dist_eq_norm] using hh.le
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (j + 1) zero_lt_one hd.diffContOnCl hb
  rw [iteratedDeriv_succ_sub_constant] at hCauchy
  rw [dist_zero_right]
  refine hCauchy.trans_lt ?_
  simp only [one_pow, div_one]
  have he : ((j + 1).factorial : ℝ) * η = ε / 2 := by
    dsimp only [η]
    field_simp [hfact.ne']
  rw [he]
  exact half_lt_self hε

/-- Retained normalized correction jet, before the fibres are pushed forward. -/
def cutoffNormalizedCorrectionJet (C : ℂ) (j N : ℕ) (x : ℕ × (ℕ × ℕ)) : ℂ :=
  if x.1 * x.2.1 ≤ N ∧ x.1 * x.2.2 ≤ N then
    iteratedDeriv j (fun z => complexSelbergCorrectionWeight x.1 x.2.1 x.2.2
      (z / (Real.log N : ℂ))) C else 0

/-- Every positive-order normalized correction jet has vanishing total fibre mass. -/
theorem tendsto_tsum_cutoffNormalizedCorrectionJet_succ (C : ℂ) (j : ℕ) :
    Tendsto (fun N : ℕ => ∑' x : ℕ × (ℕ × ℕ), cutoffNormalizedCorrectionJet C (j + 1) N x)
      atTop (𝓝 0) := by
  let B : ℝ := ((j + 1).factorial : ℝ) * Real.exp (4 * (‖C‖ + 1))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hs : Summable (fun x : ℕ × (ℕ × ℕ) => B * |selbergCorrectionWeight x.1 x.2.1 x.2.2|) := by
    simpa only [Real.norm_eq_abs] using summable_selbergCorrectionWeight.norm.mul_left B
  have hp (x : ℕ × (ℕ × ℕ)) :
      Tendsto (fun N : ℕ => cutoffNormalizedCorrectionJet C (j + 1) N x) atTop (𝓝 0) := by
    have hh := tendsto_entire_normalized_jet_succ
      (differentiable_complexSelbergCorrectionWeight x.1 x.2.1 x.2.2) C j
    refine hh.congr' ?_
    filter_upwards [eventually_ge_atTop (max (x.1 * x.2.1) (x.1 * x.2.2))] with N hN
    have hx : x.1 * x.2.1 ≤ N ∧ x.1 * x.2.2 ≤ N :=
      ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩
    simp only [cutoffNormalizedCorrectionJet, if_pos hx]
  have hb : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ × (ℕ × ℕ),
      ‖cutoffNormalizedCorrectionJet C (j + 1) N x‖ ≤
        B * |selbergCorrectionWeight x.1 x.2.1 x.2.2| := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rintro ⟨r, u, v⟩
    by_cases hr : r = 0
    · simp [cutoffNormalizedCorrectionJet, hr, complexSelbergCorrectionWeight,
        selbergCorrectionWeight, iteratedDeriv_succ]
    by_cases hx : r * u ≤ N ∧ r * v ≤ N
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
      have hu : u ≤ N := calc
        u = 1 * u := by rw [one_mul]
        _ ≤ r * u := Nat.mul_le_mul_right u hr1
        _ ≤ N := hx.1
      have hv : v ≤ N := calc
        v = 1 * v := by rw [one_mul]
        _ ≤ r * v := Nat.mul_le_mul_right v hr1
        _ ≤ N := hx.2
      simp only [cutoffNormalizedCorrectionJet, if_pos hx]
      exact norm_normalizedCorrectionJet_le (by omega) C (j + 1) r hu hv
    · simp only [cutoffNormalizedCorrectionJet, if_neg hx, norm_zero]
      exact mul_nonneg hB (abs_nonneg _)
  have hh := tendsto_tsum_of_dominated_convergence hs hp hb
  simpa only [tsum_zero] using hh

end GaloisForLFunctions.MultiscaleMollifiedZetaField
