import GaloisForLFunctions.RHTower.VanDerCorputWeighted
import GaloisForLFunctions.RHTower.VanDerCorputWeightedAnti
import GaloisForLFunctions.RHTower.BernoulliFourierBridge
import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder

/-!
# Signed Fourier control of the literal Bernoulli tail

The actual power-weighted logarithmic Fourier modes have phase speed at least five whenever
`|Im(s)| ≤ N` and their integer frequency is nonzero. Both signs of the weighted
first-derivative test give the same half-line bound. The second-Bernoulli coefficients have
nonnegative real mass exactly `1/12`, so summing the modes gives the centered-tail estimate
`N ^ (-Re(s) - 2) / 15`.

Absolute integrability justifies the sum–integral interchange. Every power weight and the
Bernoulli mean are retained. No zero equation or numerical certificate is used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Actual weighted logarithmic Fourier mode. -/
def logarithmicFourierMode (β t ω x : ℝ) : ℂ :=
  (x ^ (-β) : ℝ) * Complex.exp (((ω*x+t*Real.log x : ℝ):ℂ)*Complex.I)

/-- The mode norm is the actual decreasing power amplitude. -/
theorem norm_logarithmicFourierMode (β t ω x : ℝ) (hx : 0 < x) :
    ‖logarithmicFourierMode β t ω x‖ = x ^ (-β) := by
  simp [logarithmicFourierMode, Complex.norm_exp, Real.rpow_nonneg hx.le]

/-- Uniform finite-interval bound for either sign of the logarithmic phase. -/
theorem norm_integral_logarithmicFourierMode_le {a b β t ω : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hβ : 0 < β) (hω : 6 ≤ ω) (ht : |t| ≤ a) :
    ‖∫ x in a..b, logarithmicFourierMode β t ω x‖ ≤ 4 * a ^ (-β) / 5 := by
  have hx (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x :=
    ha.trans_le ((uIcc_of_le hab ▸ hx).1)
  have hw (x : ℝ) (hxx : x ∈ uIcc a b) : HasDerivAt (fun x : ℝ => x ^ (-β))
      (-β * x ^ (-β-1)) x := Real.hasDerivAt_rpow_const (Or.inl (hx x hxx).ne')
  have hp (p : ℝ) : ContinuousOn (fun x : ℝ => x ^ p) (uIcc a b) := by
    intro x hxx
    exact (Real.hasDerivAt_rpow_const (p := p) (Or.inl (hx x hxx).ne')).continuousAt.continuousWithinAt
  have hwc : ContinuousOn (fun x : ℝ => -β * x ^ (-β-1)) (uIcc a b) :=
    continuousOn_const.mul (hp _)
  have hwnn (x : ℝ) (hxx : x ∈ uIcc a b) : 0 ≤ x ^ (-β) := Real.rpow_nonneg (hx x hxx).le _
  have hwanti (x : ℝ) (hxx : x ∈ uIcc a b) : -β*x^(-β-1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (hx x hxx).le _)
  have hg (x : ℝ) (hxx : x ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ => ω*x+t*Real.log x) (ω+t/x) x := by
    convert! ((hasDerivAt_id x).const_mul ω).add ((Real.hasDerivAt_log (hx x hxx).ne').const_mul t) using 1; ring
  have hg' (x : ℝ) (hxx : x ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ => ω+t/x) (-t/x^(2 : ℕ)) x := by
    convert! (((hasDerivAt_id x).inv (hx x hxx).ne').const_mul t).const_add ω using 1
    simp only [id_eq]
    ring
  have hg'' : ContinuousOn (fun x : ℝ => -t/x^(2 : ℕ)) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun x hxx => pow_ne_zero _ (hx x hxx).ne')
  have hlb (x : ℝ) (hxx : x ∈ uIcc a b) : 5 ≤ ω+t/x := by
    have hax : a ≤ x := (uIcc_of_le hab ▸ hxx).1
    have htlo := (abs_le.mp ht).1
    have hd : -1 ≤ t/x := (le_div_iff₀ (hx x hxx)).mpr (by linarith)
    linarith
  by_cases ht0 : 0 ≤ t
  · exact RHTower.norm_integral_weight_cexp_le_anti hab (by norm_num)
      hw hwc hwnn hwanti hg hg' hg'' hlb
      (fun x hxx => div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht0) (sq_nonneg x))
  · exact RHTower.norm_integral_weight_cexp_le hab (by norm_num)
      hw hwc hwnn hwanti hg hg' hg'' hlb
      (fun x hxx => div_nonneg (by linarith) (sq_nonneg x))

/-- Absolute half-line integrability for every mode with integrable power amplitude. -/
theorem integrable_logarithmicFourierMode {a β : ℝ} (ha : 0 < a) (hβ : 1 < β) (t ω : ℝ) :
    IntegrableOn (logarithmicFourierMode β t ω) (Ioi a) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -β < -1) ha
  apply Integrable.mono hi
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hx0 := ha.trans hx
    have hp := (Real.hasDerivAt_rpow_const (p := -β) (Or.inl hx0.ne')).continuousAt
    have hl := (Real.hasDerivAt_log hx0.ne').continuousAt
    exact ((Complex.continuous_ofReal.continuousAt.comp hp).mul
      (Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.continuousAt.comp
          ((continuousAt_const.mul continuousAt_id).add (continuousAt_const.mul hl))).mul continuousAt_const))).continuousWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [norm_logarithmicFourierMode _ _ _ _ (ha.trans hx)]
    exact le_abs_self _

/-- The finite-interval cancellation bound persists at the infinite endpoint. -/
theorem norm_integral_Ioi_logarithmicFourierMode_le {a β t ω : ℝ}
    (ha : 0 < a) (hβ : 1 < β) (hω : 6 ≤ ω) (ht : |t| ≤ a) :
    ‖∫ x in Ioi a, logarithmicFourierMode β t ω x‖ ≤ 4 * a ^ (-β) / 5 := by
  have hlim := (intervalIntegral_tendsto_integral_Ioi a
    (integrable_logarithmicFourierMode ha hβ t ω) tendsto_id).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop a] with b hb
  exact norm_integral_logarithmicFourierMode_le ha hb (by linarith) hω ht

/-- Simultaneous frequency and height reversal is exact complex conjugation. -/
theorem logarithmicFourierMode_neg (β t ω x : ℝ) :
    logarithmicFourierMode β (-t) (-ω) x = star (logarithmicFourierMode β t ω x) := by
  simp only [logarithmicFourierMode, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

/-- Both signed Fourier frequencies satisfy the same complete-tail bound. -/
theorem norm_integral_Ioi_logarithmicFourierMode_le_abs {a β t ω : ℝ}
    (ha : 0 < a) (hβ : 1 < β) (hω : 6 ≤ |ω|) (ht : |t| ≤ a) :
    ‖∫ x in Ioi a, logarithmicFourierMode β t ω x‖ ≤ 4 * a ^ (-β) / 5 := by
  rcases le_or_gt 0 ω with hpos | hneg
  · exact norm_integral_Ioi_logarithmicFourierMode_le ha hβ (by simpa [abs_of_nonneg hpos] using hω) ht
  · have h := norm_integral_Ioi_logarithmicFourierMode_le (t := -t) (ω := -ω) ha hβ
      (by simpa [abs_of_neg hneg] using hω) (by simpa using ht)
    simpa only [logarithmicFourierMode_neg, Complex.star_def, integral_conj, Complex.norm_conj] using h


/-- The actual nonnegative second-Bernoulli Fourier coefficient, zero at frequency zero. -/
def bernoulliModeWeight (k : ℤ) : ℝ := 1 / (4 * Real.pi ^ 2 * (k : ℝ) ^ 2)

/-- Each Fourier coefficient is nonnegative. -/
theorem bernoulliModeWeight_nonneg (k : ℤ) : 0 ≤ bernoulliModeWeight k := by
  unfold bernoulliModeWeight
  positivity

/-- The mean is kept separately from the nonzero Fourier modes. -/
theorem bernoulliModeWeight_zero : bernoulliModeWeight 0 = 0 := by
  simp [bernoulliModeWeight]

/-- The centered periodic arithmetic kernel is exactly its absolutely convergent Fourier series. -/
theorem hasSum_bernoulliModeWeight_fourier (x : ℝ) :
    HasSum (fun k : ℤ => (bernoulliModeWeight k : ℂ) * fourier k (x : AddCircle (1:ℝ)))
      ((RHTower.bernoulliPeriodic x + 1/12 : ℝ) : ℂ) := by
  have h := (RHTower.fourier_hasSum_bernoulli2 x).mul_left (1 / (4 * (Real.pi : ℂ)^(2 : ℕ)))
  convert! h using 1
  · ext k
    dsimp only [bernoulliModeWeight]
    push_cast
    ring
  · simp only [RHTower.bernoulliPeriodic]
    push_cast
    field_simp
    ring

/-- The complete coefficient mass is exactly `1/12`, from the source series at zero. -/
theorem hasSum_bernoulliModeWeight : HasSum bernoulliModeWeight (1/12) := by
  apply Complex.hasSum_ofReal.mp
  simpa [RHTower.bernoulliPeriodic, fourier_coe_apply] using hasSum_bernoulliModeWeight_fourier 0

/-- Every real-line Fourier character has unit norm. -/
theorem norm_fourier_real (k : ℤ) (x : ℝ) :
    ‖fourier k (x : AddCircle (1:ℝ))‖ = 1 := by
  rw [fourier_coe_apply]
  simp [Complex.norm_exp]

/-- The Fourier character times the literal complex power is the logarithmic mode. -/
theorem fourier_mul_cpow_eq_mode (k : ℤ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    fourier k (x : AddCircle (1:ℝ)) * (x : ℂ)^(-s-2) =
      logarithmicFourierMode (s.re+2) (-s.im) (2*Real.pi*k) x := by
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [fourier_coe_apply, Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le,
    logarithmicFourierMode, Real.rpow_def_of_pos hx, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  have hs : s=(s.re:ℂ)+(s.im:ℂ)*Complex.I := by exact (Complex.re_add_im s).symm
  rw [hs]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, Complex.I_im, sub_self, add_zero,
    Complex.add_im, Complex.mul_im, zero_add, mul_one]
  ring

/-- One complete arithmetic Fourier term, with its coefficient and complex power retained. -/
def bernoulliFourierTerm (k : ℤ) (s : ℂ) (x : ℝ) : ℂ :=
  (bernoulliModeWeight k : ℂ) * (fourier k (x : AddCircle (1:ℝ)) * (x : ℂ)^(-s-2))

/-- The exact pointwise norm majorant preserves the real coefficient and power weight. -/
theorem norm_bernoulliFourierTerm (k : ℤ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖bernoulliFourierTerm k s x‖ = bernoulliModeWeight k * x ^ (-s.re-2) := by
  rw [bernoulliFourierTerm, norm_mul, norm_mul, norm_fourier_real,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bernoulliModeWeight_nonneg k)]
  simp

/-- Each complete arithmetic Fourier term is absolutely integrable on the half-line. -/
theorem integrable_bernoulliFourierTerm {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : -1 < s.re) (k : ℤ) :
    IntegrableOn (bernoulliFourierTerm k s) (Ioi a) := by
  have hi := (integrable_logarithmicFourierMode ha (by linarith : 1 < s.re+2)
    (-s.im) (2*Real.pi*k)).const_mul (bernoulliModeWeight k : ℂ)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [bernoulliFourierTerm, fourier_mul_cpow_eq_mode k s (ha.trans hx)]

/-- The integral norm factors into coefficient mass and the common integrable power amplitude. -/
theorem integral_norm_bernoulliFourierTerm {a : ℝ} (ha : 0 < a) (s : ℂ) (k : ℤ) :
    (∫ x in Ioi a, ‖bernoulliFourierTerm k s x‖) =
      bernoulliModeWeight k * (∫ x in Ioi a, x ^ (-s.re-2)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact norm_bernoulliFourierTerm k s (ha.trans hx)

/-- Absolute summability justifies the full source sum–integral interchange. -/
theorem hasSum_integral_bernoulliFourierTerm {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : -1 < s.re) :
    HasSum (fun k : ℤ => ∫ x in Ioi a, bernoulliFourierTerm k s x)
      (∫ x in Ioi a, ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) := by
  have hsum : Summable (fun k : ℤ => ∫ x in Ioi a, ‖bernoulliFourierTerm k s x‖) := by
    simp_rw [integral_norm_bernoulliFourierTerm ha]
    exact hasSum_bernoulliModeWeight.summable.mul_right _
  have h := hasSum_integral_of_summable_integral_norm (integrable_bernoulliFourierTerm ha hs) hsum
  convert! h using 1
  apply integral_congr_ae
  filter_upwards with x
  have hx := (hasSum_bernoulliModeWeight_fourier x).mul_right ((x:ℂ)^(-s-2))
  simpa only [bernoulliFourierTerm, mul_assoc] using hx.tsum_eq.symm

/-- Uniform cancellation bound for every complete signed arithmetic Fourier term. -/
theorem norm_integral_bernoulliFourierTerm_le {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : -1 < s.re) (ht : |s.im| ≤ a) (k : ℤ) :
    ‖∫ x in Ioi a, bernoulliFourierTerm k s x‖ ≤
      bernoulliModeWeight k * (4 * a ^ (-s.re-2) / 5) := by
  by_cases hk : k = 0
  · simp [hk, bernoulliFourierTerm, bernoulliModeWeight_zero]
  have he : (∫ x in Ioi a, bernoulliFourierTerm k s x) =
      (bernoulliModeWeight k : ℂ) * ∫ x in Ioi a,
        logarithmicFourierMode (s.re+2) (-s.im) (2*Real.pi*k) x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [bernoulliFourierTerm, fourier_mul_cpow_eq_mode k s (ha.trans hx)]
  have hk1 : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hω : 6 ≤ |2*Real.pi*(k:ℝ)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hb := norm_integral_Ioi_logarithmicFourierMode_le_abs (t := -s.im) ha
    (by linarith : 1 < s.re+2) hω (by simpa using ht)
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bernoulliModeWeight_nonneg k)]
  simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using
    mul_le_mul_of_nonneg_left hb (bernoulliModeWeight_nonneg k)

/-- Summed signed-frequency cancellation gives a centered-tail bound with one extra inverse power. -/
theorem norm_centeredBernoulliTail_le_linear {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : -1 < s.re) (ht : |s.im| ≤ a) :
    ‖∫ x in Ioi a, ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)‖ ≤
      a^(-s.re-2)/15 := by
  have h := (hasSum_integral_bernoulliFourierTerm ha hs).norm_le_of_bounded
    (hasSum_bernoulliModeWeight.mul_right (4 * a^(-s.re-2)/5))
    (norm_integral_bernoulliFourierTerm_le ha hs ht)
  convert! h using 1; ring

/-- The centered tail is exactly the literal Bernoulli remainder minus its explicit mean. -/
theorem centeredBernoulliTail_eq_sub_mean {s : ℂ} (hs : -1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in Ioi (N:ℝ), ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) =
      RHTower.zetaBernoulliTail N s + (N:ℂ)^(-s-1)/(12*(s+1)) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hre : (-s-2).re < -1 := by simp; linarith
  have hi := RHTower.integrableOn_bernoulli_cpow hs hN
  have hc := (integrableOn_Ioi_cpow_of_lt hre hNp).const_mul (1/12:ℂ)
  have he : (∫ x in Ioi (N:ℝ), ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-s-2)) =
      RHTower.zetaBernoulliTail N s + (1/12:ℂ)*(∫ x in Ioi (N:ℝ), (x:ℂ)^(-s-2)) := by
    rw [RHTower.zetaBernoulliTail, ← integral_const_mul, ← integral_add hi hc]
    apply integral_congr_ae
    filter_upwards with x
    push_cast
    rw [show -s-1-1 = -s-2 by ring]
    ring
  rw [he, integral_Ioi_cpow_of_lt hre hNp,
    show -s-2+1 = -(s+1) by ring, neg_div_neg_eq]
  congr 1
  rw [show -(s+1) = -s-1 by ring]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end RHTower.DeletionMixedRefinement
