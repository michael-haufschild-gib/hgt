import GaloisForLFunctions.RHTower.BurnolSoninDilationMellin
import GaloisForLFunctions.RHTower.BurnolSoninApertureRieszBound
import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate

/-!
# Cross-aperture growth of the completed Mellin evaluation vector

The normalized dilation carries the extended Sonine space at aperture `a` into the space at the
shrunk aperture `r⁻¹ a`, in both branches, and multiplies the completed Mellin evaluation by the
exact character `r^(w-1/2)`.  Testing the evaluation vector at the shrunk aperture against the
dilate of the evaluation vector at `a` therefore forces

`‖k_{w, r⁻¹ a}‖ ≥ r^(±(Re w - 1/2)) ‖k_{w,a}‖`,

one inequality per branch.  Iterating gives the exact geometric lower bound along the aperture
sequence `a_N = r^(-N) a`, with exponent the horizontal displacement of `w`.  Combined with the
ambient upper bound this pins the aperture type of the evaluation vector from both sides.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

theorem norm_burnolExtendedSoninEvaluationVector_congr
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a = b) :
    ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ =
      ‖burnolExtendedSoninEvaluationVector w b hlo hhi hb‖ := by
  subst hab
  rfl

/-- The common self-testing step: a character bound on the cross-aperture pairing. -/
private theorem cross_aperture_step
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : 0 < b) {c : ℝ}
    (g : soninExtendedSpace b)
    (hgnorm : ‖g‖ = ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖)
    (hpair : ‖soninMellinEvaluation w (((g : evenSubspace) : SoninL2) : ℝ → ℂ)‖ =
      c * ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2) :
    c * ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ≤
      ‖burnolExtendedSoninEvaluationVector w b hlo hhi hb‖ := by
  set k := burnolExtendedSoninEvaluationVector w a hlo hhi ha with hk
  set k' := burnolExtendedSoninEvaluationVector w b hlo hhi hb with hk'
  have hcs : ‖(inner ℂ k' g : ℂ)‖ ≤ ‖k'‖ * ‖g‖ := norm_inner_le_norm _ _
  rw [inner_burnolExtendedSoninEvaluationVector, hpair, hgnorm] at hcs
  rcases eq_or_lt_of_le (norm_nonneg k) with h0 | h0
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · have hmul : c * ‖k‖ * ‖k‖ ≤ ‖k'‖ * ‖k‖ := by
      calc c * ‖k‖ * ‖k‖ = c * ‖k‖ ^ 2 := by ring
        _ ≤ ‖k'‖ * ‖k‖ := hcs
    exact le_of_mul_le_mul_right (by linarith [hmul]) h0

/-- **Forward branch.**  The forward dilation forces the aperture growth exponent `Re w - 1/2`. -/
theorem norm_burnolExtendedSoninEvaluationVector_forward_le
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (ha' : 0 < r⁻¹ * a) :
    r ^ (w.re - 1 / 2) * ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ≤
      ‖burnolExtendedSoninEvaluationVector w (r⁻¹ * a) hlo hhi ha'‖ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  set k := burnolExtendedSoninEvaluationVector w a hlo hhi ha with hk
  refine cross_aperture_step hlo hhi ha ha'
    ⟨evenDilationCLM r hr0 (k : evenSubspace),
      evenDilation_mem_soninExtendedSpace_inv_mul ha hr k.property⟩ ?_ ?_
  · exact norm_evenDilationCLM_apply r hr0 _
  · show ‖soninMellinEvaluation w
      (((evenDilationCLM r hr0 (k : evenSubspace) : evenSubspace) : SoninL2) : ℝ → ℂ)‖ = _
    rw [soninMellinEvaluation_evenDilation, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hr0]
    have hre : (w - 1 / 2).re = w.re - 1 / 2 := by
      simp
    rw [hre, ← inner_burnolExtendedSoninEvaluationVector w a hlo hhi ha k]
    congr 1
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg k)]

/-- **Inverse branch.**  The inverse dilation forces the reflected exponent `1/2 - Re w`. -/
theorem norm_burnolExtendedSoninEvaluationVector_inverse_le
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (ha' : 0 < r⁻¹ * a) :
    r ^ (1 / 2 - w.re) * ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ≤
      ‖burnolExtendedSoninEvaluationVector w (r⁻¹ * a) hlo hhi ha'‖ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hri : 0 < r⁻¹ := inv_pos.mpr hr0
  set k := burnolExtendedSoninEvaluationVector w a hlo hhi ha with hk
  refine cross_aperture_step hlo hhi ha ha'
    ⟨evenDilationCLM r⁻¹ hri (k : evenSubspace),
      evenInverseDilation_mem_soninExtendedSpace_inv_mul ha hr k.property⟩ ?_ ?_
  · exact norm_evenDilationCLM_apply r⁻¹ hri _
  · show ‖soninMellinEvaluation w
      (((evenDilationCLM r⁻¹ hri (k : evenSubspace) : evenSubspace) : SoninL2) : ℝ → ℂ)‖ = _
    rw [soninMellinEvaluation_evenDilation, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hri]
    have hre : (w - 1 / 2).re = w.re - 1 / 2 := by
      simp
    rw [hre, Real.inv_rpow hr0.le, ← Real.rpow_neg hr0.le,
      show -(w.re - 1 / 2) = 1 / 2 - w.re from by ring,
      ← inner_burnolExtendedSoninEvaluationVector w a hlo hhi ha k]
    congr 1
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg k)]

/-- **Two-sided one-step law.**  The shrunk aperture dominates both reflected characters. -/
theorem norm_burnolExtendedSoninEvaluationVector_max_le
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (ha' : 0 < r⁻¹ * a) :
    max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) *
        ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ≤
      ‖burnolExtendedSoninEvaluationVector w (r⁻¹ * a) hlo hhi ha'‖ := by
  rcases max_cases (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    exact norm_burnolExtendedSoninEvaluationVector_forward_le hlo hhi ha hr ha'
  · rw [h]
    exact norm_burnolExtendedSoninEvaluationVector_inverse_le hlo hhi ha hr ha'


/-- **Geometric cross-aperture lower bound.**  Along the aperture sequence `a_N = r^(-N) a` the
evaluation vector grows at least like the `N`-th power of the reflected character, that is with
exponent the horizontal displacement `|Re w - 1/2|`. -/
theorem norm_burnolExtendedSoninEvaluationVector_geometric_le
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (N : ℕ) :
    max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) ^ N *
        ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ≤
      ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hr) N)) ha)‖ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hMnn : (0 : ℝ) ≤ max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) :=
    le_trans (Real.rpow_nonneg hr0.le _) (le_max_left _ _)
  induction N with
  | zero =>
      have hcongr := norm_burnolExtendedSoninEvaluationVector_congr hlo hhi ha
        (mul_pos (inv_pos.mpr (pow_pos hr0 0)) ha)
        (by rw [pow_zero, inv_one, one_mul])
      rw [pow_zero, one_mul, ← hcongr]
  | succ n ih =>
      have hn : 0 < (r ^ n)⁻¹ * a := mul_pos (inv_pos.mpr (pow_pos hr0 n)) ha
      have hn' : 0 < r⁻¹ * ((r ^ n)⁻¹ * a) := mul_pos (inv_pos.mpr hr0) hn
      have hstep := norm_burnolExtendedSoninEvaluationVector_max_le hlo hhi hn hr hn'
      have hcongr := norm_burnolExtendedSoninEvaluationVector_congr hlo hhi hn'
        (mul_pos (inv_pos.mpr (pow_pos hr0 (n + 1))) ha)
        (by field_simp; ring)
      rw [← hcongr]
      calc max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) ^ (n + 1) *
            ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖
          = max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) *
              (max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) ^ n *
                ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖) := by ring
        _ ≤ max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) *
              ‖burnolExtendedSoninEvaluationVector w ((r ^ n)⁻¹ * a) hlo hhi hn‖ :=
            mul_le_mul_of_nonneg_left ih hMnn
        _ ≤ _ := hstep


/-! ## The two-sided aperture-type law -/

theorem max_rpow_neg_eq_rpow_abs {r : ℝ} (hr : 1 ≤ r) (x : ℝ) :
    max (r ^ x) (r ^ (-x)) = r ^ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_left]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  · rw [abs_of_neg hx, max_eq_right]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)

theorem max_character_eq_rpow_abs {w : ℂ} {r : ℝ} (hr : 1 ≤ r) :
    max (r ^ (w.re - 1 / 2)) (r ^ (1 / 2 - w.re)) = r ^ |w.re - 1 / 2| := by
  rw [show (1 : ℝ) / 2 - w.re = -(w.re - 1 / 2) from by ring]
  exact max_rpow_neg_eq_rpow_abs hr _

/-- **Two-sided aperture type, lower half.**  Along `a_N = r^(-N) a` the evaluation vector grows at
least like `r^(N |Re w - 1/2|)`. -/
theorem norm_burnolExtendedSoninEvaluationVector_geometric_lower
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (N : ℕ) :
    ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ *
        r ^ ((N : ℝ) * |w.re - 1 / 2|) ≤
      ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hr) N)) ha)‖ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h := norm_burnolExtendedSoninEvaluationVector_geometric_le hlo hhi ha hr N
  rw [max_character_eq_rpow_abs hr, ← Real.rpow_natCast (r ^ |w.re - 1 / 2|) N,
    ← Real.rpow_mul hr0.le] at h
  calc ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ *
        r ^ ((N : ℝ) * |w.re - 1 / 2|)
      = r ^ (|w.re - 1 / 2| * (N : ℝ)) *
          ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ := by
        rw [mul_comm |w.re - 1 / 2| (N : ℝ)]
        ring
    _ ≤ _ := h

/-- **Two-sided aperture type, upper half.**  The same sequence grows at most like
`r^(N |Re w - 1/2|)`, with the explicit ambient constant. -/
theorem norm_burnolExtendedSoninEvaluationVector_geometric_upper
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r)
    (N : ℕ) :
    ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hr) N)) ha)‖ ≤
      soninApertureConstant w / Real.sqrt 2 * a ^ (-|w.re - 1 / 2|) *
        r ^ ((N : ℝ) * |w.re - 1 / 2|) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpow : (0 : ℝ) < (r ^ N)⁻¹ := inv_pos.mpr (pow_pos hr0 N)
  have h := norm_burnolExtendedSoninEvaluationVector_le_aperture hlo hhi
    (mul_pos hpow ha)
  refine le_trans h (le_of_eq ?_)
  rw [Real.mul_rpow hpow.le ha.le, ← Real.rpow_natCast r N, ← Real.rpow_neg_one (r ^ ((N : ℝ))),
    ← Real.rpow_mul hr0.le, ← Real.rpow_mul hr0.le]
  ring_nf

/-- **Aperture-type limit.**  If the evaluation vector at the base aperture is nonzero, the
logarithmic growth rate along the geometric apertures is exactly the horizontal displacement. -/
theorem tendsto_log_norm_burnolExtendedSoninEvaluationVector
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hk : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.log ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
          (mul_pos (inv_pos.mpr (pow_pos (lt_of_lt_of_le zero_lt_one hr.le) N)) ha)‖ /
          ((N : ℝ) * Real.log r))
      Filter.atTop (nhds |w.re - 1 / 2|) := by
  have hr1 : (1 : ℝ) ≤ r := hr.le
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hlogr : 0 < Real.log r := Real.log_pos hr
  set c := ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ with hc
  have hcpos : 0 < c := norm_pos_iff.mpr hk
  set C := soninApertureConstant w / Real.sqrt 2 * a ^ (-|w.re - 1 / 2|) with hC
  have hCpos : 0 < C := by
    have h0 := norm_burnolExtendedSoninEvaluationVector_geometric_upper hlo hhi ha hr1 0
    have hbase := norm_burnolExtendedSoninEvaluationVector_congr hlo hhi ha
      (mul_pos (inv_pos.mpr (pow_pos hr0 0)) ha) (by rw [pow_zero, inv_one, one_mul])
    rw [← hbase] at h0
    simp only [Nat.cast_zero, zero_mul, Real.rpow_zero, mul_one] at h0
    linarith
  set θ := |w.re - 1 / 2| with hθ
  have hsq : ∀ N : ℕ, 1 ≤ N →
      Real.log c / ((N : ℝ) * Real.log r) + θ ≤
        Real.log ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
          (mul_pos (inv_pos.mpr (pow_pos hr0 N)) ha)‖ / ((N : ℝ) * Real.log r) ∧
      Real.log ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
          (mul_pos (inv_pos.mpr (pow_pos hr0 N)) ha)‖ / ((N : ℝ) * Real.log r) ≤
        Real.log C / ((N : ℝ) * Real.log r) + θ := by
    intro N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hden : (0 : ℝ) < (N : ℝ) * Real.log r := mul_pos hNpos hlogr
    have hlow := norm_burnolExtendedSoninEvaluationVector_geometric_lower hlo hhi ha hr1 N
    have hupp := norm_burnolExtendedSoninEvaluationVector_geometric_upper hlo hhi ha hr1 N
    have hrpow : Real.log (r ^ ((N : ℝ) * θ)) = (N : ℝ) * θ * Real.log r :=
      Real.log_rpow hr0 _
    have hprod : (0 : ℝ) < c * r ^ ((N : ℝ) * θ) :=
      mul_pos hcpos (Real.rpow_pos_of_pos hr0 _)
    have hknpos : (0 : ℝ) < ‖burnolExtendedSoninEvaluationVector w ((r ^ N)⁻¹ * a) hlo hhi
        (mul_pos (inv_pos.mpr (pow_pos hr0 N)) ha)‖ := lt_of_lt_of_le hprod hlow
    constructor
    · rw [div_add' _ _ _ (ne_of_gt hden), div_le_div_iff_of_pos_right hden]
      have := Real.log_le_log hprod hlow
      rw [Real.log_mul (ne_of_gt hcpos) (ne_of_gt (Real.rpow_pos_of_pos hr0 _)), hrpow] at this
      linarith
    · rw [div_add' _ _ _ (ne_of_gt hden), div_le_div_iff_of_pos_right hden]
      have := Real.log_le_log hknpos hupp
      rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt (Real.rpow_pos_of_pos hr0 _)), hrpow] at this
      linarith
  have hzero : ∀ x : ℝ, Filter.Tendsto
      (fun N : ℕ => Real.log x / ((N : ℝ) * Real.log r) + θ) Filter.atTop (nhds θ) := by
    intro x
    have hone : Filter.Tendsto (fun N : ℕ => (Real.log x / Real.log r) * (1 / (N : ℝ)))
        Filter.atTop (nhds ((Real.log x / Real.log r) * 0)) :=
      tendsto_one_div_atTop_nhds_zero_nat.const_mul _
    rw [mul_zero] at hone
    have hmain : Filter.Tendsto (fun N : ℕ => Real.log x / ((N : ℝ) * Real.log r))
        Filter.atTop (nhds 0) := by
      have hcongr : (fun N : ℕ => Real.log x / ((N : ℝ) * Real.log r)) =
          fun N : ℕ => (Real.log x / Real.log r) * (1 / (N : ℝ)) := by
        funext N
        rw [div_mul_eq_div_div, div_right_comm, div_eq_mul_one_div]
      rw [hcongr]
      exact hone
    simpa using hmain.add_const θ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hzero c) (hzero C) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hsq N hN).1
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    exact (hsq N hN).2

end RHTower
