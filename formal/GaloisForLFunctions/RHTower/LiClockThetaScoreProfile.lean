import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.RHTower.LiClockThetaScoreMeasure
import GaloisForLFunctions.RHTower.LiClockPositiveEvenSeriesRatio
import GaloisForLFunctions.RHTower.PrimeArchThetaRawMomentRatioVanishing
import GaloisForLFunctions.HTGeometry.EntireSeriesEulerJet
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Full theta score profiles

These profiles use the literal normalized theta source and full score measure. The
factorial series are entire; all fixed derivative orders have compact summable
majorants. The score reserve retains every positive row with its original R0.

The last two results give an all-real uniform coefficient reserve and its sharp
large-clock ratio. They assert no sign for the actual log-history response.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval
namespace RHTower
noncomputable section
local notation "nu" => thetaCuspNormalizedEvenMoment
local notation "R0" => thetaCuspRawEvenMoment 0
local notation "B" => liEvenCrossActualClockBorelKernel
local notation "K1" => deriv (deriv liEvenCrossActualClockBorelKernel)

/-- The full even kernel with two factorial denominators. -/
def liClockThetaFactorialEvenKernel (z : ℂ) : ℂ :=
  ∑' j : ℕ, z^(2*j) / (((2*j).factorial : ℂ)^2)

/-- The exact second derivative kernel, including its constant term. -/
def liClockThetaFactorialSecondKernel (z : ℂ) : ℂ :=
  ∑' j : ℕ, z^(2*j) /
    (((2*j+2).factorial : ℂ)*((2*j).factorial : ℂ))

/-- The full theta moment profile after compact Borel smoothing. -/
def liClockThetaSmoothedBorelProfile (z : ℂ) : ℂ :=
  ∑' j : ℕ, (nu j : ℂ)*z^(2*j) /
    (((2*j+2).factorial : ℂ)*((2*j).factorial : ℂ))

/-- The full cost profile with literal coefficient 32j+17. -/
def liClockThetaScoreCostProfile (z : ℂ) : ℂ :=
  ∑' j : ℕ, ((32*(j:ℝ)+17)*nu j : ℂ)*z^(2*j) /
    (((2*j+2).factorial : ℂ)*((2*j).factorial : ℂ))

/-- The full signed moment gap integrated against the positive score measure. -/
def liClockThetaScoreReserveProfile (z : ℂ) : ℂ :=
  ∑' j : ℕ, (liClockThetaScoreMomentGap j : ℂ)*z^(2*j) /
    (((2*j+2).factorial : ℂ)*((2*j).factorial : ℂ))

private def spPair (j : ℕ) : ℝ :=
  ((2*j+2).factorial : ℝ)*((2*j).factorial : ℝ)
private def spPhi (j : ℕ) : ℝ := 1/((2*j).factorial : ℝ)^2
private def spSecond (j : ℕ) : ℝ := 1/spPair j
private def spSmooth (j : ℕ) : ℝ := nu j/spPair j
private def spCost (j : ℕ) : ℝ := (32*(j:ℝ)+17)*nu j/spPair j
private def spReserve (j : ℕ) : ℝ := liClockThetaScoreMomentGap j/spPair j
private def spBound (a : ℕ → ℝ) : Prop :=
  ∀ j, |a j| ≤ 49*((j:ℝ)+1)/(j.factorial : ℝ)
private def spTerm (a : ℕ → ℝ) (m j : ℕ) (z : ℂ) : ℂ :=
  (a j : ℂ)*((2*j).descFactorial m : ℂ)*z^(2*j-m)
private def spSeries (a : ℕ → ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ∑' j, spTerm a m j z

private theorem sp_envelope_summable (m : ℕ) (T : ℝ) :
    Summable (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
      (49*((j:ℝ)+1)/(j.factorial : ℝ))*T^(2*j)) := by
  have hc (j : ℕ) : ‖(((j.factorial : ℝ))⁻¹ : ℂ)‖ ≤
      ((j.factorial : ℝ))⁻¹ := by
    simp only [Complex.ofReal_natCast,norm_inv,Complex.norm_natCast]
    exact le_rfl
  have hs0 := GaloisForLFunctions.HTGeometry.summable_pow_mul_of_factorial_decay
    hc m (sq_nonneg T)
  have hs1 := GaloisForLFunctions.HTGeometry.summable_pow_mul_of_factorial_decay
    hc (m+1) (sq_nonneg T)
  have heq : (fun j : ℕ => (2:ℝ)^m*(j:ℝ)^m*
      (49*((j:ℝ)+1)/(j.factorial : ℝ))*T^(2*j)) =
      (fun j : ℕ => ((2:ℝ)^m*49)*
        ((j:ℝ)^(m+1)*(‖(((j.factorial:ℝ))⁻¹:ℂ)‖*(T^2)^j)+
         (j:ℝ)^m*(‖(((j.factorial:ℝ))⁻¹:ℂ)‖*(T^2)^j))) := by
    funext j
    simp only [Complex.ofReal_natCast,norm_inv,Complex.norm_natCast]
    rw [←pow_mul]
    rw [pow_succ]
    ring
  rw [heq]
  exact (hs1.add hs0).mul_left _

private theorem sp_term_bound {a : ℕ → ℝ} (ha : spBound a) (m j : ℕ)
    {z : ℂ} {T : ℝ} (hT : 1 ≤ T) (hz : ‖z‖ ≤ T) :
    ‖spTerm a m j z‖ ≤ (2:ℝ)^m*(j:ℝ)^m*
      (49*((j:ℝ)+1)/(j.factorial : ℝ))*T^(2*j) := by
  have hd : ((2*j).descFactorial m : ℝ) ≤ (2:ℝ)^m*(j:ℝ)^m := by
    calc
      ((2*j).descFactorial m : ℝ) ≤ (((2*j : ℕ) : ℝ))^m := by
        exact_mod_cast Nat.descFactorial_le_pow (2*j) m
      _ = _ := by push_cast; rw [mul_pow]
  have hp : ‖z‖^(2*j-m) ≤ T^(2*j) :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans
      (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  rw [spTerm,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_natCast,norm_pow]
  calc
    |a j| *((2*j).descFactorial m : ℝ)*‖z‖^(2*j-m) ≤
      ((49*((j:ℝ)+1)/(j.factorial : ℝ))*((2:ℝ)^m*(j:ℝ)^m))*T^(2*j) :=
      mul_le_mul (mul_le_mul (ha j) hd (by positivity) (by positivity)) hp
        (by positivity) (by positivity)
    _ = _ := by ring

private theorem sp_norm_summable {a : ℕ → ℝ} (ha : spBound a) (m : ℕ) (z : ℂ) :
    Summable (fun j => ‖spTerm a m j z‖) := by
  let T := ‖z‖+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [norm_nonneg z]
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => sp_term_bound ha m j hT (by dsimp [T]; linarith))
    (sp_envelope_summable m T)

private theorem sp_summable {a : ℕ → ℝ} (ha : spBound a) (m : ℕ) (z : ℂ) :
    Summable (fun j => spTerm a m j z) := (sp_norm_summable ha m z).of_norm

private theorem sp_term_hasDerivAt (a : ℕ → ℝ) (m j : ℕ) (z : ℂ) :
    HasDerivAt (spTerm a m j) (spTerm a (m+1) j z) z := by
  have he : 2*j-(m+1)=2*j-m-1 := by omega
  convert (((hasDerivAt_id z).pow (2*j-m)).const_mul
    ((a j:ℂ)*((2*j).descFactorial m : ℂ))) using 1 <;>
    first | rfl | (simp only [spTerm,Nat.descFactorial_succ,Nat.cast_mul,
      id_eq,mul_one,he]; ring)

private theorem sp_series_hasDerivAt {a : ℕ → ℝ} (ha : spBound a) (m : ℕ) (z : ℂ) :
    HasDerivAt (spSeries a m) (spSeries a (m+1) z) z := by
  let T := ‖z‖+1
  have hT : 1 ≤ T := by dsimp [T]; linarith [norm_nonneg z]
  exact hasDerivAt_tsum_of_isPreconnected (sp_envelope_summable (m+1) T)
    Metric.isOpen_ball (convex_ball (0:ℂ) T).isPreconnected
    (fun j y _ => sp_term_hasDerivAt a m j y)
    (fun j y hy => sp_term_bound ha (m+1) j hT
      (le_of_lt (by simpa [Metric.mem_ball,dist_zero_right] using hy)))
    (by simp [Metric.mem_ball,T]; positivity) (sp_summable ha m 0)
    (by simp [Metric.mem_ball,T])

private theorem sp_series_analytic {a : ℕ → ℝ} (ha : spBound a) (m : ℕ) (z : ℂ) :
    AnalyticAt ℂ (spSeries a m) z :=
  (show Differentiable ℂ (spSeries a m) from
    fun y => (sp_series_hasDerivAt ha m y).differentiableAt).analyticAt z

private theorem sp_iteratedDeriv {a : ℕ → ℝ} (ha : spBound a) (m : ℕ) :
    iteratedDeriv m (spSeries a 0) = spSeries a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ,ih]
    funext z
    exact (sp_series_hasDerivAt ha m z).deriv

private theorem sp_series_even (a : ℕ → ℝ) (z : ℂ) :
    spSeries a 0 (-z)=spSeries a 0 z := by
  unfold spSeries
  apply tsum_congr
  intro j
  simp [spTerm]

private theorem sp_series_real (a : ℕ → ℝ) (r : ℝ) :
    spSeries a 0 (r:ℂ) = ((∑' j, a j*r^(2*j) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro j
  simp [spTerm]

private theorem sp_factorial_lower (j : ℕ) :
    0 < (j.factorial : ℝ) ∧
    (j.factorial : ℝ)^2 ≤ ((2*j).factorial : ℝ)^2 ∧
    ((2*j).factorial : ℝ)^2 ≤ spPair j := by
  have h1 : (j.factorial : ℝ) ≤ ((2*j).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : j ≤ 2*j)
  have h2 : ((2*j).factorial : ℝ) ≤ ((2*j+2).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2*j ≤ 2*j+2)
  refine ⟨by positivity,?_,?_⟩
  · exact pow_le_pow_left₀ (by positivity) h1 2
  · dsimp [spPair]
    nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ ((2*j).factorial:ℝ))]

private theorem sp_nu_factorial (j : ℕ) : nu j ≤ (j.factorial : ℝ) := by
  have hp : (32/303 : ℝ)^j ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  exact (thetaCuspNormalizedEvenMoment_le_score_factorial j).trans
    (by simpa using mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ (j.factorial:ℝ)))

private theorem sp_pair_pos (j : ℕ) : 0 < spPair j := by unfold spPair; positivity

private theorem sp_quotient_bound (j : ℕ) {x d : ℝ} (_hx : 0 ≤ x)
    (hxd : x ≤ d*(j.factorial : ℝ)) (hd : 0 ≤ d) :
    x/spPair j ≤ d/(j.factorial : ℝ) := by
  have hf := sp_factorial_lower j
  have hden : (j.factorial : ℝ)^2 ≤ spPair j := hf.2.1.trans hf.2.2
  calc
    x/spPair j ≤ (d*(j.factorial : ℝ))/spPair j :=
      div_le_div_of_nonneg_right hxd (sp_pair_pos j).le
    _ ≤ (d*(j.factorial : ℝ))/(j.factorial : ℝ)^2 :=
      div_le_div_of_nonneg_left (mul_nonneg hd hf.1.le) (by positivity) hden
    _ = _ := by field_simp

private theorem sp_coefficient_bounds :
    spBound spPhi ∧ spBound spSecond ∧ spBound spSmooth ∧
    spBound spCost ∧ spBound spReserve := by
  have hp (j : ℕ) : 0 < spPhi j := by unfold spPhi; positivity
  have hs (j : ℕ) : 0 < spSecond j := by unfold spSecond; exact div_pos one_pos (sp_pair_pos j)
  have ht (j : ℕ) : 0 < spSmooth j := by unfold spSmooth; exact div_pos (thetaCuspNormalizedEvenMoment_pos j) (sp_pair_pos j)
  have hu (j : ℕ) : 0 < spCost j := by unfold spCost; exact div_pos (mul_pos (by positivity) (thetaCuspNormalizedEvenMoment_pos j)) (sp_pair_pos j)
  have hr (j : ℕ) : 0 < spReserve j := by unfold spReserve; exact div_pos (liClockThetaScoreMomentGap_bounds j).1 (sp_pair_pos j)
  have h49 (j : ℕ) : (32*(j:ℝ)+17) ≤ 49*((j:ℝ)+1) := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
  have hunit (j : ℕ) : (1:ℝ)/(j.factorial:ℝ) ≤
      49*((j:ℝ)+1)/(j.factorial:ℝ) :=
    div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg j (α := ℝ)])
      (by positivity)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    rw [abs_of_pos (hp j)]
    have hfac : (j.factorial : ℝ) ≤ ((2*j).factorial : ℝ)^2 := by
      have hf := sp_factorial_lower j
      have hf1 : 1 ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
      nlinarith [hf.2.1]
    apply (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
      (by positivity : 0 < (j.factorial:ℝ)) hfac).trans
    exact hunit j
  · intro j
    rw [abs_of_pos (hs j)]
    exact (sp_quotient_bound j (by norm_num : (0:ℝ)≤1)
      (by simpa using (show (1:ℝ) ≤ (j.factorial:ℝ) from by exact_mod_cast Nat.factorial_pos j)) (by norm_num : (0:ℝ)≤1)).trans
      (hunit j)
  · intro j
    rw [abs_of_pos (ht j)]
    exact (sp_quotient_bound j (thetaCuspNormalizedEvenMoment_pos j).le
      (by simpa using sp_nu_factorial j) (by norm_num : (0:ℝ)≤1)).trans
      (hunit j)
  · intro j
    rw [abs_of_pos (hu j)]
    exact (sp_quotient_bound j (mul_nonneg (by positivity) (thetaCuspNormalizedEvenMoment_pos j).le)
      (mul_le_mul_of_nonneg_left (sp_nu_factorial j) (by positivity)) (by positivity)).trans
      (div_le_div_of_nonneg_right (h49 j) (by positivity))
  · intro j
    rw [abs_of_pos (hr j)]
    apply (sp_quotient_bound j (liClockThetaScoreMomentGap_bounds j).1.le
      ((liClockThetaScoreMomentGap_bounds j).2.trans
        (mul_le_mul_of_nonneg_left (sp_nu_factorial j) (by positivity)))
      (by positivity)).trans
    exact div_le_div_of_nonneg_right (h49 j) (by positivity)

private theorem sp_public_series :
    liClockThetaFactorialEvenKernel=spSeries spPhi 0 ∧
    liClockThetaFactorialSecondKernel=spSeries spSecond 0 ∧
    liClockThetaSmoothedBorelProfile=spSeries spSmooth 0 ∧
    liClockThetaScoreCostProfile=spSeries spCost 0 ∧
    liClockThetaScoreReserveProfile=spSeries spReserve 0 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> funext z <;>
    simp only [liClockThetaFactorialEvenKernel,liClockThetaFactorialSecondKernel,
      liClockThetaSmoothedBorelProfile,liClockThetaScoreCostProfile,
      liClockThetaScoreReserveProfile,spSeries] <;>
    apply tsum_congr <;> intro j <;>
    simp [spTerm,spPhi,spSecond,spSmooth,spCost,spReserve,spPair,div_eq_mul_inv] <;> ring


/-- All five complete complex series are absolutely summable. -/
theorem liClockThetaScoreProfiles_summable_norm (z : ℂ) :
  Summable (fun j : ℕ => ‖z^(2*j)/(((2*j).factorial:ℂ)^2)‖) ∧
  Summable (fun j : ℕ => ‖z^(2*j)/
    (((2*j+2).factorial:ℂ)*((2*j).factorial:ℂ))‖) ∧
  Summable (fun j : ℕ => ‖(nu j:ℂ)*z^(2*j)/
    (((2*j+2).factorial:ℂ)*((2*j).factorial:ℂ))‖) ∧
  Summable (fun j : ℕ => ‖((32*(j:ℝ)+17)*nu j:ℂ)*z^(2*j)/
    (((2*j+2).factorial:ℂ)*((2*j).factorial:ℂ))‖) ∧
  Summable (fun j : ℕ => ‖(liClockThetaScoreMomentGap j:ℂ)*z^(2*j)/
    (((2*j+2).factorial:ℂ)*((2*j).factorial:ℂ))‖) := by
  obtain ⟨hp,hs,ht,hu,hr⟩ := sp_coefficient_bounds
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [spTerm,spPhi,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
      using sp_norm_summable hp 0 z
  · simpa [spTerm,spSecond,spPair,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
      using sp_norm_summable hs 0 z
  · simpa [spTerm,spSmooth,spPair,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
      using sp_norm_summable ht 0 z
  · simpa [spTerm,spCost,spPair,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
      using sp_norm_summable hu 0 z
  · simpa [spTerm,spReserve,spPair,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
      using sp_norm_summable hr 0 z

/-- All five profiles are analytic at every complex point. -/
theorem liClockThetaScoreProfiles_analyticAt (z : ℂ) :
  AnalyticAt ℂ liClockThetaFactorialEvenKernel z ∧
  AnalyticAt ℂ liClockThetaFactorialSecondKernel z ∧
  AnalyticAt ℂ liClockThetaSmoothedBorelProfile z ∧
  AnalyticAt ℂ liClockThetaScoreCostProfile z ∧
  AnalyticAt ℂ liClockThetaScoreReserveProfile z := by
  obtain ⟨hp,hs,ht,hu,hr⟩ := sp_coefficient_bounds
  obtain ⟨hP,hS,hT,hU,hR⟩ := sp_public_series
  rw [hP,hS,hT,hU,hR]
  exact ⟨sp_series_analytic hp 0 z,sp_series_analytic hs 0 z,
    sp_series_analytic ht 0 z,sp_series_analytic hu 0 z,sp_series_analytic hr 0 z⟩

/-- The complete complex profiles are even. -/
theorem liClockThetaScoreProfiles_even (z : ℂ) :
  liClockThetaFactorialEvenKernel (-z)=liClockThetaFactorialEvenKernel z ∧
  liClockThetaFactorialSecondKernel (-z)=liClockThetaFactorialSecondKernel z ∧
  liClockThetaSmoothedBorelProfile (-z)=liClockThetaSmoothedBorelProfile z ∧
  liClockThetaScoreCostProfile (-z)=liClockThetaScoreCostProfile z ∧
  liClockThetaScoreReserveProfile (-z)=liClockThetaScoreReserveProfile z := by
  obtain ⟨hP,hS,hT,hU,hR⟩ := sp_public_series
  rw [hP,hS,hT,hU,hR]
  exact ⟨sp_series_even _ _,sp_series_even _ _,sp_series_even _ _,
    sp_series_even _ _,sp_series_even _ _⟩

/-- Each profile is real on the whole real axis. -/
theorem liClockThetaScoreProfiles_im_ofReal (r : ℝ) :
  (liClockThetaFactorialEvenKernel (r:ℂ)).im=0 ∧
  (liClockThetaFactorialSecondKernel (r:ℂ)).im=0 ∧
  (liClockThetaSmoothedBorelProfile (r:ℂ)).im=0 ∧
  (liClockThetaScoreCostProfile (r:ℂ)).im=0 ∧
  (liClockThetaScoreReserveProfile (r:ℂ)).im=0 := by
  obtain ⟨hP,hS,hT,hU,hR⟩ := sp_public_series
  rw [hP,hS,hT,hU,hR]
  simp only [sp_series_real,Complex.ofReal_im,and_self]


private theorem sp_even_nonneg (r : ℝ) (j : ℕ) : 0 ≤ r^(2*j) := by
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg r) j

private theorem sp_real_summable {a : ℕ → ℝ} (ha : spBound a) (r : ℝ) :
    Summable (fun j => a j*r^(2*j)) := by
  have hn : Summable (fun j => ‖a j*r^(2*j)‖) := by
    simpa [spTerm,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_pow]
      using sp_norm_summable ha 0 (r:ℂ)
  exact hn.of_norm

private theorem sp_series_integrable {μ : Measure ℝ} (f : ℕ → ℝ → ℂ)
    (hm : ∀ j, Measurable (f j)) (hi : ∀ j, Integrable (f j) μ)
    (hs : Summable (fun j => ∫ x, ‖f j x‖ ∂μ)) :
    Integrable (fun x => ∑' j, f j x) μ := by
  have hrow (j : ℕ) : (∫⁻ x, ‖f j x‖ₑ ∂μ) = ‖∫ x, ‖f j x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi j).norm,ENNReal.coe_nnreal_eq,coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (f j x)))]
    simp only [coe_nnnorm]
  have hsum : (∑' j, ∫⁻ x, ‖f j x‖ₑ ∂μ) ≠ ∞ := by
    rw [funext hrow]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun j => (hm j).enorm.aemeasurable)]
  exact hsum.lt_top

private def spRow (z : ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ((x^(2*j) : ℝ) : ℂ)*z^(2*j)/(spPair j : ℂ)

private theorem sp_row_norm (z : ℂ) (j : ℕ) (x : ℝ) :
    ‖spRow z j x‖ = x^(2*j)*‖z‖^(2*j)/spPair j := by
  simp only [spRow,norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (sp_pair_pos j)]
  rw [←abs_pow,abs_of_nonneg (sp_even_nonneg x j)]

private theorem sp_row_tsum (z : ℂ) (x : ℝ) :
    (∑' j, spRow z j x)=liClockThetaFactorialSecondKernel (z*(x:ℂ)) := by
  unfold liClockThetaFactorialSecondKernel
  apply tsum_congr
  intro j
  simp only [spRow,spPair,Complex.ofReal_mul,Complex.ofReal_natCast,
    mul_pow]
  rw [Complex.ofReal_pow]
  ring

private theorem sp_source_profile (μ : Measure ℝ) (d : ℕ → ℝ)
    (hi : ∀ j, Integrable (fun x : ℝ => x^(2*j)) μ)
    (hm : ∀ j, (∫ x : ℝ, x^(2*j) ∂μ)=d j)
    (hb : spBound (fun j => d j/spPair j)) (z : ℂ) :
    Integrable (fun x : ℝ => liClockThetaFactorialSecondKernel (z*(x:ℂ))) μ ∧
    spSeries (fun j => d j/spPair j) 0 z =
      ∫ x : ℝ, liClockThetaFactorialSecondKernel (z*(x:ℂ)) ∂μ := by
  have hri (j : ℕ) : Integrable (spRow z j) μ := by
    exact ((hi j).ofReal.mul_const (z^(2*j))).div_const (spPair j : ℂ)
  have hnorm (j : ℕ) : (∫ x, ‖spRow z j x‖ ∂μ)=
      (d j/spPair j)*‖z‖^(2*j) := by
    simp_rw [sp_row_norm]
    rw [integral_div,integral_mul_const,hm]
    ring
  have hsum : Summable (fun j => ∫ x, ‖spRow z j x‖ ∂μ) := by
    simp_rw [hnorm]
    exact sp_real_summable hb ‖z‖
  refine ⟨?_,?_⟩
  · have hg := sp_series_integrable (spRow z) (fun j => by unfold spRow; fun_prop) hri hsum
    simpa only [sp_row_tsum] using hg
  · calc
      _ = ∑' j, ∫ x, spRow z j x ∂μ := by
        unfold spSeries
        apply tsum_congr
        intro j
        have hcast : (∫ x : ℝ, ((x^(2*j):ℝ):ℂ) ∂μ)=(d j:ℂ) := by
          calc
            _ = (((∫ x : ℝ, x^(2*j) ∂μ) : ℝ) : ℂ) :=
              integral_complex_ofReal (μ := μ) (f := fun x : ℝ => x^(2*j))
            _ = _ := congrArg (fun x : ℝ => (x:ℂ)) (hm j)
        simp only [spTerm,Nat.descFactorial_zero,Nat.cast_one,mul_one,Nat.sub_zero,
          spRow,integral_div,integral_mul_const,Complex.ofReal_div]
        rw [hcast]
        ring
      _ = ∫ x, ∑' j, spRow z j x ∂μ :=
        integral_tsum_of_summable_integral_norm hri hsum
      _ = _ := by simp only [sp_row_tsum]


private theorem sp_phi_second_shift (j : ℕ) (z : ℂ) :
    spTerm spPhi 2 (j+1) z=spTerm spSecond 0 j z := by
  have hn : 2*(j+1)=2*j+2 := by omega
  have hfac : ((2*j+2).factorial : ℂ) =
      (2*(j:ℂ)+2)*(2*(j:ℂ)+1)*((2*j).factorial:ℂ) := by
    rw [show 2*j+2=(2*j+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  have hdesc : ((2*(j+1)).descFactorial 2 : ℂ) =
      (2*(j:ℂ)+2)*(2*(j:ℂ)+1) := by
    rw [show (2:ℕ)=1+1 by rfl,Nat.descFactorial_succ]
    simp only [Nat.descFactorial_one]
    have hminus : 2*(j+1)-1=2*j+1 := by omega
    rw [hminus,hn]
    push_cast
    ring
  have hdesc' : ((2*j+2).descFactorial 2 : ℂ) =
      (2*(j:ℂ)+2)*(2*(j:ℂ)+1) := by simpa only [hn] using hdesc
  simp only [spTerm,spPhi,spSecond,spPair,Complex.ofReal_div,Complex.ofReal_one,
    Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_mul,hn,
    Nat.descFactorial_zero,Nat.cast_one,Nat.sub_zero,mul_one]
  rw [show 2*j+2-2=2*j by omega,hdesc',hfac]
  have hf : ((2*j).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*j)
  have h1 : 2*(j:ℂ)+1 ≠ 0 := by exact_mod_cast (by omega : 2*j+1 ≠ 0)
  have h2 : 2*(j:ℂ)+2 ≠ 0 := by exact_mod_cast (by omega : 2*j+2 ≠ 0)
  field_simp [hf,h1,h2]

/-- The factorial second kernel is the genuine ordinary second derivative. -/
theorem liClockThetaFactorialSecondKernel_eq_iteratedDeriv (z : ℂ) :
    liClockThetaFactorialSecondKernel z =
      iteratedDeriv 2 liClockThetaFactorialEvenKernel z := by
  obtain ⟨hP,hS,hT,hU,hR⟩ := sp_public_series
  rw [hP,hS,sp_iteratedDeriv sp_coefficient_bounds.1]
  have hs := sp_summable sp_coefficient_bounds.1 2 z
  have hshift := hs.sum_add_tsum_nat_add 1
  have hz : spTerm spPhi 2 0 z=0 := by simp [spTerm]
  simpa only [Finset.sum_range_one,hz,zero_add,sp_phi_second_shift,spSeries]
    using hshift

/-- Both actual source integrals are genuinely integrable and equal the full profiles. -/
theorem liClockThetaScoreProfiles_source_integrals (z : ℂ) :
  Integrable (fun x : ℝ => liClockThetaFactorialSecondKernel (z*(x:ℂ)))
    liClockThetaRawSourceMeasure ∧
  Integrable (fun x : ℝ => liClockThetaFactorialSecondKernel (z*(x:ℂ)))
    liClockThetaScoreMeasure ∧
  liClockThetaSmoothedBorelProfile z =
    ∫ x : ℝ, liClockThetaFactorialSecondKernel (z*(x:ℂ))
      ∂liClockThetaRawSourceMeasure ∧
  liClockThetaScoreReserveProfile z =
    ∫ x : ℝ, liClockThetaFactorialSecondKernel (z*(x:ℂ))
      ∂liClockThetaScoreMeasure := by
  have hr := sp_source_profile liClockThetaRawSourceMeasure nu
    (fun j => liClockThetaRawSourceMeasure_admission.2.2.2 (2*j))
    liClockThetaRawSourceMeasure_moment sp_coefficient_bounds.2.2.1 z
  have hs := sp_source_profile liClockThetaScoreMeasure liClockThetaScoreMomentGap
    (fun j => liClockThetaScoreMeasure_admission.2.2.2 (2*j))
    liClockThetaScoreMeasure_moment sp_coefficient_bounds.2.2.2.2 z
  refine ⟨hr.1,hs.1,?_,?_⟩
  · rw [sp_public_series.2.2.1]
    exact hr.2
  · rw [sp_public_series.2.2.2.2]
    exact hs.2


private theorem sp_density_complex_l1 (ρ : ℝ → ℝ)
    (hr : Measurable ρ) (hn : ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ ρ x)
    (f : ℝ → ℂ) (hf : Integrable f
      ((volume.restrict (Ioi 0)).withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    Integrable (fun x => (ρ x:ℂ)*f x) (volume.restrict (Ioi 0)) := by
  have hi := (integrable_withDensity_iff_integrable_smul' hr.ennreal_ofReal
    (by simp : ∀ᵐ x ∂(volume.restrict (Ioi 0)), ENNReal.ofReal (ρ x)<∞)).1 hf
  apply hi.congr
  filter_upwards [hn] with x hx
  simp only [ENNReal.toReal_ofReal hx,Complex.real_smul]

private theorem sp_density_complex_integral (ρ : ℝ → ℝ)
    (hr : Measurable ρ) (hn : ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ ρ x)
    (f : ℝ → ℂ) :
    (∫ x, f x ∂(volume.restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (ρ x))) =
      ∫ x : ℝ in Ioi 0, (ρ x:ℂ)*f x := by
  rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
    (by simp : ∀ᵐ x ∂(volume.restrict (Ioi 0)), ENNReal.ofReal (ρ x)<∞)]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [ENNReal.toReal_ofReal hx,Complex.real_smul]

private theorem sp_density_real_integral (ρ : ℝ → ℝ)
    (hr : Measurable ρ) (hn : ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ ρ x)
    (f : ℝ → ℝ) :
    (∫ x, f x ∂(volume.restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (ρ x))) =
      ∫ x : ℝ in Ioi 0, ρ x*f x := by
  rw [integral_withDensity_eq_integral_toReal_smul hr.ennreal_ofReal
    (by simp : ∀ᵐ x ∂(volume.restrict (Ioi 0)), ENNReal.ofReal (ρ x)<∞)]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [ENNReal.toReal_ofReal hx,smul_eq_mul]

private def spScoreWeight (n : ℕ) (x : ℝ) : ℝ :=
  liClockThetaScoreDefect (n+1) x*thetaCuspBornWittenAmplitude (n+1) x^2

private theorem sp_score_weight_measurable (n : ℕ) : Measurable (spScoreWeight n) := by
  unfold spScoreWeight liClockThetaScoreDefect thetaCuspBornWittenAmplitude
    thetaCuspBornWittenSuperpotential thetaCuspBornWittenWeight
    thetaCuspMorseSuperpotential thetaCuspMorseGroundState thetaCuspMorseZeroMode
    thetaCuspMorseScale
  fun_prop

private theorem sp_score_weight_nonneg (n : ℕ) :
    ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ spScoreWeight n x := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hd : 0 ≤ liClockThetaScoreDefect (n+1) x :=
    (sq_nonneg (x-1)).trans (thetaCuspBornWitten_scoreDefect_ge_square (by omega) hx.le)
  exact mul_nonneg hd (sq_nonneg _)

/-- The entire score reserve retains every row with the same R0 normalizer. -/
theorem liClockThetaScoreReserveProfile_full_rows (z : ℂ) :
  (∀ n : ℕ, IntegrableOn (fun x : ℝ =>
    (liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2 : ℂ) *
      liClockThetaFactorialSecondKernel (z*(x:ℂ))) (Ioi 0)) ∧
  Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0,
    ‖(liClockThetaScoreDefect (n+1) x *
      thetaCuspBornWittenAmplitude (n+1) x ^ 2 : ℂ) *
      liClockThetaFactorialSecondKernel (z*(x:ℂ))‖) ∧
  HasSum (fun n : ℕ => (2*Real.pi/R0 : ℂ) *
    ∫ x : ℝ in Ioi 0,
      (liClockThetaScoreDefect (n+1) x *
        thetaCuspBornWittenAmplitude (n+1) x ^ 2 : ℂ) *
        liClockThetaFactorialSecondKernel (z*(x:ℂ)))
    (liClockThetaScoreReserveProfile z) := by
  let κ : ℝ := 2*Real.pi/R0
  have hk : 0 < κ := by
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) (thetaCuspRawEvenMoment_pos 0)
  have hkc : (κ:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  let f : ℝ → ℂ := fun x => liClockThetaFactorialSecondKernel (z*(x:ℂ))
  have htotal : Integrable f (Measure.sum liClockThetaScoreAtomMeasure) := by
    simpa only [liClockThetaScoreMeasure] using
      (liClockThetaScoreProfiles_source_integrals z).2.1
  have ha (n : ℕ) : Integrable f (liClockThetaScoreAtomMeasure n) :=
    htotal.mono_measure (Measure.le_sum _ n)
  have hm (n : ℕ) : Measurable (fun x => κ*spScoreWeight n x) :=
    (sp_score_weight_measurable n).const_mul κ
  have hn (n : ℕ) : ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ κ*spScoreWeight n x :=
    (sp_score_weight_nonneg n).mono (fun x hx => mul_nonneg hk.le hx)
  have had (n : ℕ) : Integrable f ((volume.restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (κ*spScoreWeight n x))) := by
    simpa only [liClockThetaScoreAtomMeasure,spScoreWeight,κ,mul_assoc] using ha n
  have hrow (n : ℕ) : Integrable (fun x => (spScoreWeight n x:ℂ)*f x)
      (volume.restrict (Ioi 0)) := by
    have h := sp_density_complex_l1 _ (hm n) (hn n) f (had n)
    apply (h.const_mul ((κ:ℂ)⁻¹)).congr
    filter_upwards [] with x
    simp only [Complex.ofReal_mul]
    field_simp [hkc]
  have he (n : ℕ) : (∫ x, f x ∂liClockThetaScoreAtomMeasure n)=
      (κ:ℂ)*(∫ x : ℝ in Ioi 0, (spScoreWeight n x:ℂ)*f x) := by
    rw [show liClockThetaScoreAtomMeasure n=
      (volume.restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (κ*spScoreWeight n x)) by
      simp only [liClockThetaScoreAtomMeasure,spScoreWeight,κ,mul_assoc],
      sp_density_complex_integral _ (hm n) (hn n)]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Complex.ofReal_mul]
    ring
  have heN (n : ℕ) : (∫ x, ‖f x‖ ∂liClockThetaScoreAtomMeasure n)=
      κ*(∫ x : ℝ in Ioi 0, ‖(spScoreWeight n x:ℂ)*f x‖) := by
    rw [show liClockThetaScoreAtomMeasure n=
      (volume.restrict (Ioi 0)).withDensity
        (fun x => ENNReal.ofReal (κ*spScoreWeight n x)) by
      simp only [liClockThetaScoreAtomMeasure,spScoreWeight,κ,mul_assoc],
      sp_density_real_integral _ (hm n) (hn n)]
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [sp_score_weight_nonneg n] with x hx
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx]
    ring
  have hsum := htotal.summable_integral
  have hsumRow : Summable (fun n => ∫ x : ℝ in Ioi 0,
      ‖(spScoreWeight n x:ℂ)*f x‖) := by
    have hh (n : ℕ) : (1/κ)*(∫ x, ‖f x‖ ∂liClockThetaScoreAtomMeasure n)=
        ∫ x : ℝ in Ioi 0, ‖(spScoreWeight n x:ℂ)*f x‖ := by
      rw [heN]
      field_simp [hk.ne']
    exact (hsum.mul_left (1/κ)).congr hh
  have hh := hasSum_integral_measure htotal
  have hval : (∫ x, f x ∂Measure.sum liClockThetaScoreAtomMeasure)=
      liClockThetaScoreReserveProfile z := by
    simpa only [liClockThetaScoreMeasure] using
      (liClockThetaScoreProfiles_source_integrals z).2.2.2.symm
  rw [hval] at hh
  have hfinal := hh.congr_fun (fun n => (he n).symm)
  simpa [spScoreWeight,f,κ,IntegrableOn] using
    (show (∀ n, Integrable (fun x => (spScoreWeight n x:ℂ)*f x)
        (volume.restrict (Ioi 0))) ∧
      Summable (fun n => ∫ x : ℝ in Ioi 0, ‖(spScoreWeight n x:ℂ)*f x‖) ∧
      HasSum (fun n => (κ:ℂ)*(∫ x : ℝ in Ioi 0,
        (spScoreWeight n x:ℂ)*f x)) (liClockThetaScoreReserveProfile z)
      from ⟨hrow,hsumRow,hfinal⟩)


private theorem sp_B_bound : spBound liEvenCrossActualClockBorelCoefficient := by
  intro j
  have hp : (32/303:ℝ)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [abs_of_pos (liEvenCrossActualClockBorelCoefficient_pos j)]
  calc
    liEvenCrossActualClockBorelCoefficient j ≤
        (32/303:ℝ)^j/(j.factorial:ℝ) := liEvenCrossActualClockBorelCoefficient_le j
    _ ≤ 1/(j.factorial:ℝ) := div_le_div_of_nonneg_right hp (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_right
      (by nlinarith [Nat.cast_nonneg j (α := ℝ)]) (by positivity)

private theorem sp_B_real_series :
    B=(fun r : ℝ => (spSeries liEvenCrossActualClockBorelCoefficient 0 (r:ℂ)).re) := by
  funext r
  rw [sp_series_real]
  simp only [Complex.ofReal_re]
  unfold liEvenCrossActualClockBorelKernel
  apply tsum_congr
  intro j
  exact liEvenCrossActualClockBorelTerm_eq_coefficient_mul r j

private theorem sp_B_second (r : ℝ) :
    K1 r=(spSeries liEvenCrossActualClockBorelCoefficient 2 (r:ℂ)).re := by
  have hfirst : deriv B=(fun r : ℝ =>
      (spSeries liEvenCrossActualClockBorelCoefficient 1 (r:ℂ)).re) := by
    rw [sp_B_real_series]
    funext t
    exact (sp_series_hasDerivAt sp_B_bound 0 (t:ℂ)).real_of_complex.deriv
  rw [hfirst]
  exact (sp_series_hasDerivAt sp_B_bound 1 (r:ℂ)).real_of_complex.deriv

private theorem sp_B_shift_term (j : ℕ) (z : ℂ) :
    spTerm liEvenCrossActualClockBorelCoefficient 2 (j+1) z=
      (nu (j+1):ℂ)*spTerm spSecond 0 j z := by
  have h : spTerm liEvenCrossActualClockBorelCoefficient 2 (j+1) z=
      (nu (j+1):ℂ)*spTerm spPhi 2 (j+1) z := by
    simp [spTerm,liEvenCrossActualClockBorelCoefficient,spPhi,div_eq_mul_inv]; ring
  rw [h,sp_phi_second_shift]

private theorem sp_B_shift_hasSum (z : ℂ) :
    HasSum (fun j => (nu (j+1):ℂ)*spTerm spSecond 0 j z)
      (spSeries liEvenCrossActualClockBorelCoefficient 2 z) := by
  have hs := sp_summable sp_B_bound 2 z
  have h := hs.sum_add_tsum_nat_add 1
  have hz : spTerm liEvenCrossActualClockBorelCoefficient 2 0 z=0 := by simp [spTerm]
  simp only [Finset.sum_range_one,hz,zero_add] at h
  unfold spSeries
  rw [←h]
  exact ((summable_nat_add_iff 1).2 hs).hasSum.congr_fun
    (fun j => (sp_B_shift_term j z).symm)

private theorem sp_cost_gap_term (j : ℕ) (z : ℂ) :
    spTerm spCost 0 j z=
      303*((nu (j+1):ℂ)*spTerm spSecond 0 j z)+spTerm spReserve 0 j z := by
  simp [spTerm,spCost,spReserve,spSecond,liClockThetaScoreMomentGap,div_eq_mul_inv]; ring

private theorem sp_cost_gap_complex (z : ℂ) :
    spSeries spCost 0 z=
      303*spSeries liEvenCrossActualClockBorelCoefficient 2 z+spSeries spReserve 0 z := by
  have hh := ((sp_B_shift_hasSum z).mul_left 303).add
    (sp_summable sp_coefficient_bounds.2.2.2.2 0 z).hasSum
  exact (hh.congr_fun (fun j => sp_cost_gap_term j z)).tsum_eq

private theorem sp_euler_term (a : ℕ → ℝ) (j : ℕ) (z : ℂ) :
    z*spTerm a 1 j z=(2*j:ℂ)*spTerm a 0 j z := by
  cases j with
  | zero => simp [spTerm]
  | succ j =>
    have he : 2*(j+1)-1+1=2*(j+1) := by omega
    simp only [spTerm,Nat.descFactorial_one,Nat.descFactorial_zero,
      Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,mul_one,Nat.sub_zero]
    rw [show z*((a (j+1):ℂ)*(2*(j+1):ℂ)*z^(2*(j+1)-1))=
      ((a (j+1):ℂ)*(2*(j+1):ℂ))*(z*z^(2*(j+1)-1)) by ring,
      ←pow_succ',he]
    ring

private theorem sp_cost_euler_term (j : ℕ) (z : ℂ) :
    spTerm spCost 0 j z=17*spTerm spSmooth 0 j z+16*z*spTerm spSmooth 1 j z := by
  rw [show 16*z*spTerm spSmooth 1 j z=16*(z*spTerm spSmooth 1 j z) by ring,
    sp_euler_term]
  simp only [spTerm,Nat.descFactorial_zero,Nat.sub_zero,Nat.cast_one,mul_one,
    spCost,spSmooth,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_natCast,Complex.ofReal_ofNat]
  ring

private theorem sp_cost_euler (z : ℂ) :
    spSeries spCost 0 z=17*spSeries spSmooth 0 z+16*z*spSeries spSmooth 1 z := by
  have ht := sp_coefficient_bounds.2.2.1
  have hh := ((sp_summable ht 0 z).hasSum.mul_left 17).add
    ((sp_summable ht 1 z).hasSum.mul_left (16*z))
  exact (hh.congr_fun (fun j => sp_cost_euler_term j z)).tsum_eq

private theorem sp_second_real_nonneg (r : ℝ) :
    0 ≤ (liClockThetaFactorialSecondKernel (r:ℂ)).re := by
  rw [sp_public_series.2.1,sp_series_real]
  simp only [Complex.ofReal_re]
  exact tsum_nonneg (fun j => mul_nonneg (by unfold spSecond spPair; positivity)
    (sp_even_nonneg r j))

private theorem sp_beta (j : ℕ) :
    (∫ v : ℝ in 0..1, (1-v)*v^(2*j))=
      1/(((2*j+1:ℕ):ℝ)*((2*j+2:ℕ):ℝ)) := by
  have he : (fun v : ℝ => (1-v)*v^(2*j))=
      (fun v : ℝ => v^(2*j)-v^(2*j+1)) := by
    funext v
    rw [pow_succ]
    ring
  have hi : IntervalIntegrable (fun v : ℝ => v^(2*j)) volume 0 1 :=
    (by fun_prop : Continuous (fun v : ℝ => v^(2*j))).intervalIntegrable 0 1
  have hi1 : IntervalIntegrable (fun v : ℝ => v^(2*j+1)) volume 0 1 :=
    (by fun_prop : Continuous (fun v : ℝ => v^(2*j+1))).intervalIntegrable 0 1
  rw [he,intervalIntegral.integral_sub hi hi1,integral_pow,integral_pow]
  simp only [one_pow,zero_pow (by omega : 2*j+1≠0),
    zero_pow (by omega : 2*j+1+1≠0),sub_zero]
  push_cast
  field_simp
  ring

private theorem sp_smoothing_coefficient (j : ℕ) :
    liEvenCrossActualClockBorelCoefficient j/
      (((2*j+1:ℕ):ℝ)*((2*j+2:ℕ):ℝ))=spSmooth j := by
  have he : spPair j=(((2*j+2:ℕ):ℝ)*((2*j+1:ℕ):ℝ))*
      ((2*j).factorial:ℝ)^2 := by
    unfold spPair
    rw [show 2*j+2=(2*j+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  unfold liEvenCrossActualClockBorelCoefficient spSmooth
  rw [he]
  ring

private theorem sp_smoothing_integral (r : ℝ) :
    HasSum (fun j => spSmooth j*r^(2*j))
      (∫ v : ℝ in 0..1, (1-v)*B (v*r)) := by
  let F : ℕ → ℝ → ℝ := fun j v =>
    (1-v)*(liEvenCrossActualClockBorelCoefficient j*(v*r)^(2*j))
  let bound : ℕ → ℝ := fun j => liEvenCrossActualClockBorelCoefficient j*|r|^(2*j)
  have hs : Summable bound := sp_real_summable sp_B_bound |r|
  have hlim (v : ℝ) : HasSum (fun j => F j v) ((1-v)*B (v*r)) := by
    have hh := (sp_real_summable sp_B_bound (v*r)).hasSum.mul_left (1-v)
    convert hh using 1
    · rfl
    · unfold liEvenCrossActualClockBorelKernel
      congr 1
      exact tsum_congr (fun j => liEvenCrossActualClockBorelTerm_eq_coefficient_mul (v*r) j)
  have hc (j : ℕ) : Continuous (F j) := by dsimp [F]; fun_prop
  have hb (j : ℕ) (v : ℝ) (hv : v∈Ι (0:ℝ) 1) : ‖F j v‖ ≤ bound j := by
    simp only [uIoc_of_le (by norm_num : (0:ℝ)≤1),mem_Ioc] at hv
    have hp : 0 ≤ liEvenCrossActualClockBorelCoefficient j :=
      (liEvenCrossActualClockBorelCoefficient_pos j).le
    have hvp : 0 ≤ v^(2*j) := sp_even_nonneg v j
    have hvb : v^(2*j) ≤ 1 := pow_le_one₀ hv.1.le hv.2
    have hwp : 0 ≤ 1-v := by linarith
    have hwb : (1-v)*v^(2*j) ≤ 1 := by nlinarith
    have hn : 0 ≤ bound j := by dsimp [bound]; positivity
    have he : F j v=bound j*((1-v)*v^(2*j)) := by
      dsimp [F,bound]
      rw [mul_pow,←abs_pow,abs_of_nonneg (sp_even_nonneg r j)]
      ring
    rw [he,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg hn,abs_of_nonneg (mul_nonneg hwp hvp)]
    nlinarith
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0:ℝ)) (b := (1:ℝ))
    (fun j (_:ℝ) => bound j) (fun j => (hc j).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall (fun v hv => hb j v hv))
    (Filter.Eventually.of_forall (fun _ _ => hs)) intervalIntegrable_const
    (Filter.Eventually.of_forall (fun v _ => hlim v))
  have he (j : ℕ) : spSmooth j*r^(2*j)=∫ v : ℝ in 0..1, F j v := by
    have hh : F j=(fun v : ℝ =>
      (liEvenCrossActualClockBorelCoefficient j*r^(2*j))*((1-v)*v^(2*j))) := by
      funext v
      dsimp [F]
      rw [mul_pow]
      ring
    rw [hh,intervalIntegral.integral_const_mul,sp_beta]
    rw [←sp_smoothing_coefficient]
    ring
  exact hsum.congr_fun he

private def spAdj (j : ℕ) : ℝ := 303*nu (j+1)/spPair j
private def spRatio (j : ℕ) : ℝ :=
  303*nu (j+1)/((32*(j:ℝ)+17)*nu j)

private theorem sp_coeff_pos (j : ℕ) :
    0 < spSmooth j ∧ 0 < spCost j ∧ 0 < spReserve j ∧ 0 < spAdj j := by
  have hn := thetaCuspNormalizedEvenMoment_pos j
  have hn1 := thetaCuspNormalizedEvenMoment_pos (j+1)
  have hg := (liClockThetaScoreMomentGap_bounds j).1
  have hd : 0 < spPair j := by unfold spPair; positivity
  unfold spSmooth spCost spReserve spAdj
  exact ⟨div_pos hn hd,div_pos (mul_pos (by positivity) hn) hd,
    div_pos hg hd,div_pos (mul_pos (by norm_num) hn1) hd⟩

private theorem sp_reserve_coefficient (j : ℕ) :
    spReserve j=spCost j-spAdj j := by
  unfold spReserve spCost spAdj liClockThetaScoreMomentGap
  ring

private theorem sp_adj_le (j : ℕ) : spAdj j < spCost j := by
  have h := (sp_coeff_pos j).2.2.1
  rw [sp_reserve_coefficient] at h
  linarith

private theorem sp_adj_bound : spBound spAdj := by
  intro j
  rw [abs_of_pos (sp_coeff_pos j).2.2.2]
  exact (sp_adj_le j).le.trans
    (by simpa only [abs_of_pos (sp_coeff_pos j).2.1] using
      sp_coefficient_bounds.2.2.2.1 j)

private theorem sp_ratio_bounds (j : ℕ) : 0 < spRatio j ∧ spRatio j < 1 := by
  have hd : 0 < (32*(j:ℝ)+17)*nu j := by
    exact mul_pos (by positivity) (thetaCuspNormalizedEvenMoment_pos j)
  have hn : 0 < 303*nu (j+1) := by
    exact mul_pos (by norm_num) (thetaCuspNormalizedEvenMoment_pos (j+1))
  refine ⟨div_pos hn hd,?_⟩
  apply (div_lt_one hd).2
  have h := (liClockThetaScoreMomentGap_bounds j).1
  unfold liClockThetaScoreMomentGap at h
  linarith

private theorem sp_ratio_eq (j : ℕ) : spAdj j/spCost j=spRatio j := by
  have hp : spPair j≠0 := by unfold spPair; positivity
  have hn : nu j≠0 := (thetaCuspNormalizedEvenMoment_pos j).ne'
  have hd : 32*(j:ℝ)+17≠0 := by positivity
  unfold spAdj spCost spRatio
  field_simp

private theorem sp_ratio_tendsto : Tendsto spRatio atTop (𝓝 (0:ℝ)) := by
  have hraw := tendsto_thetaCuspRawEvenMoment_oddScaledRatio_zero
  have hupper := hraw.const_mul (303/16:ℝ)
  simp only [mul_zero] at hupper
  have hl (j : ℕ) : 0 ≤ spRatio j := (sp_ratio_bounds j).1.le
  have hu (j : ℕ) : spRatio j ≤ (303/16:ℝ)*
      (thetaCuspRawEvenMoment (j+1)/(((2*j+1:ℕ):ℝ)*thetaCuspRawEvenMoment j)) := by
    have h0 := thetaCuspRawEvenMoment_pos 0
    have hj := thetaCuspRawEvenMoment_pos j
    have hj1 := thetaCuspRawEvenMoment_pos (j+1)
    have hd : 0 < 32*(j:ℝ)+17 := by positivity
    have hd1 : 0 < ((2*j+1:ℕ):ℝ) := by positivity
    unfold spRatio thetaCuspNormalizedEvenMoment
    field_simp
    push_cast
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hl hu

private theorem sp_finite_ratio_ceiling (N : ℕ) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧ ∀ j, j<N → spRatio j ≤ theta := by
  induction N with
  | zero => exact ⟨1/2,by norm_num,by norm_num,by intro j hj; omega⟩
  | succ N ih =>
    obtain ⟨theta,ht0,ht1,ht⟩ := ih
    refine ⟨max theta ((spRatio N+1)/2),lt_max_of_lt_left ht0,
      max_lt_iff.2 ⟨ht1,by linarith [(sp_ratio_bounds N).2]⟩,?_⟩
    intro j hj
    by_cases he : j=N
    · subst j
      exact (by linarith [(sp_ratio_bounds N).2] : spRatio N≤(spRatio N+1)/2).trans
        (le_max_right _ _)
    · exact (ht j (by omega)).trans (le_max_left _ _)

private theorem sp_uniform_ceiling :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧ ∀ j, spRatio j ≤ theta := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (sp_ratio_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/2))
  obtain ⟨theta,ht0,ht1,ht⟩ := sp_finite_ratio_ceiling N
  refine ⟨max theta (1/2),lt_max_of_lt_left ht0,
    max_lt_iff.2 ⟨ht1,by norm_num⟩,?_⟩
  intro j
  by_cases hj : j<N
  · exact (ht j hj).trans (le_max_left _ _)
  · exact (hN j (by omega)).le.trans (le_max_right _ _)

private theorem sp_real_profile (a : ℕ → ℝ) (r : ℝ) :
    (spSeries a 0 (r:ℂ)).re=liClockPositiveEvenSeries a r := by
  rw [sp_series_real]
  rfl

private theorem sp_scaled_second (r : ℝ) :
    303*K1 r=liClockPositiveEvenSeries spAdj r := by
  rw [sp_B_second]
  have hh := (sp_B_shift_hasSum (r:ℂ)).mul_left 303
  have he : (fun j => (303:ℂ)*((nu (j+1):ℂ)*spTerm spSecond 0 j (r:ℂ)))=
      (fun j => ((spAdj j*r^(2*j):ℝ):ℂ)) := by
    funext j
    simp only [spTerm,spSecond,spAdj,Nat.descFactorial_zero,Nat.sub_zero,Nat.cast_one,
      mul_one,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,
      Complex.ofReal_one]
    ring
  rw [he] at hh
  have hv : (liClockPositiveEvenSeries spAdj r:ℂ)=
      303*spSeries liEvenCrossActualClockBorelCoefficient 2 (r:ℂ) := by
    rw [liClockPositiveEvenSeries,Complex.ofReal_tsum]
    exact hh.tsum_eq
  have hr := congrArg Complex.re hv.symm
  norm_num [Complex.mul_re] at hr
  exact hr


/-- Compact interval smoothing recovers the profile at every real clock. -/
theorem liClockThetaSmoothedBorelProfile_smoothing (r : ℝ) :
    (liClockThetaSmoothedBorelProfile (r:ℂ)).re=
      ∫ v in 0..1, (1-v)*B (v*r) := by
  rw [sp_public_series.2.2.1,sp_series_real]
  simp only [Complex.ofReal_re]
  exact (sp_smoothing_integral r).tsum_eq

/-- The exact Euler derivative identity holds on the whole complex plane. -/
theorem liClockThetaScoreCostProfile_eq_derivative (z : ℂ) :
    liClockThetaScoreCostProfile z =
      17*liClockThetaSmoothedBorelProfile z+
        16*z*deriv liClockThetaSmoothedBorelProfile z := by
  rw [sp_public_series.2.2.2.1,sp_public_series.2.2.1,
    (sp_series_hasDerivAt sp_coefficient_bounds.2.2.1 0 z).deriv]
  exact sp_cost_euler z

/-- The ordinary Borel second derivative and reserve sum to the cost profile. -/
theorem liClockThetaScoreProfiles_cost_identity (r : ℝ) :
    303*K1 r + (liClockThetaScoreReserveProfile (r:ℂ)).re =
      (liClockThetaScoreCostProfile (r:ℂ)).re := by
  rw [sp_B_second,sp_public_series.2.2.2.2,sp_public_series.2.2.2.1]
  simpa using congrArg Complex.re (sp_cost_gap_complex (r:ℂ)).symm

/-- The full score profile dominates the square-weighted raw source test. -/
theorem liClockThetaScoreReserveProfile_square (r : ℝ) :
    Integrable (fun x : ℝ => (x-1)^2 *
      (liClockThetaFactorialSecondKernel ((r:ℂ)*(x:ℂ))).re)
      liClockThetaRawSourceMeasure ∧
    (∫ x : ℝ, (x-1)^2 *
      (liClockThetaFactorialSecondKernel ((r:ℂ)*(x:ℂ))).re
        ∂liClockThetaRawSourceMeasure) ≤
      (liClockThetaScoreReserveProfile (r:ℂ)).re := by
  let f : ℝ → ℝ := fun x => (liClockThetaFactorialSecondKernel ((r:ℂ)*(x:ℂ))).re
  have hc : Continuous liClockThetaFactorialSecondKernel :=
    continuous_iff_continuousAt.2 (fun z =>
      (liClockThetaScoreProfiles_analyticAt z).2.1.continuousAt)
  have hf : Measurable f :=
    (Complex.continuous_re.comp (hc.comp
      (continuous_const.mul Complex.continuous_ofReal))).measurable
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x
    dsimp [f]
    simpa only [Complex.ofReal_mul] using sp_second_real_nonneg (r*x)
  have hi := (liClockThetaScoreProfiles_source_integrals (r:ℂ)).2.1
  have hh := liClockThetaScoreMeasure_nonnegative_test f hf hf0 hi.re
  refine ⟨hh.1,?_⟩
  calc
    _ ≤ ∫ x, f x ∂liClockThetaScoreMeasure := hh.2
    _ = _ := by
      dsimp [f]
      have he := integral_re hi
      simp only [RCLike.re_eq_complex_re] at he
      rw [he,(liClockThetaScoreProfiles_source_integrals (r:ℂ)).2.2.2]

private theorem sp_profiles_real (r : ℝ) :
    (liClockThetaSmoothedBorelProfile (r:ℂ)).re=liClockPositiveEvenSeries spSmooth r ∧
    (liClockThetaScoreCostProfile (r:ℂ)).re=liClockPositiveEvenSeries spCost r ∧
    (liClockThetaScoreReserveProfile (r:ℂ)).re=liClockPositiveEvenSeries spReserve r := by
  rw [sp_public_series.2.2.1,sp_public_series.2.2.2.1,sp_public_series.2.2.2.2]
  exact ⟨sp_real_profile _ r,sp_real_profile _ r,sp_real_profile _ r⟩

private theorem sp_profiles_positive (r : ℝ) :
    0 < (liClockThetaSmoothedBorelProfile (r:ℂ)).re ∧
    0 < (liClockThetaScoreCostProfile (r:ℂ)).re ∧
    0 < (liClockThetaScoreReserveProfile (r:ℂ)).re ∧ 0 < 303*K1 r := by
  rw [(sp_profiles_real r).1,(sp_profiles_real r).2.1,(sp_profiles_real r).2.2,
    sp_scaled_second]
  exact ⟨liClockPositiveEvenSeries_pos (fun j => (sp_coeff_pos j).1.le)
      (sp_coeff_pos 0).1 r (sp_real_summable sp_coefficient_bounds.2.2.1 r),
    liClockPositiveEvenSeries_pos (fun j => (sp_coeff_pos j).2.1.le)
      (sp_coeff_pos 0).2.1 r (sp_real_summable sp_coefficient_bounds.2.2.2.1 r),
    liClockPositiveEvenSeries_pos (fun j => (sp_coeff_pos j).2.2.1.le)
      (sp_coeff_pos 0).2.2.1 r (sp_real_summable sp_coefficient_bounds.2.2.2.2 r),
    liClockPositiveEvenSeries_pos (fun j => (sp_coeff_pos j).2.2.2.le)
      (sp_coeff_pos 0).2.2.2 r (sp_real_summable sp_adj_bound r)⟩

private theorem sp_uniform_profiles {theta : ℝ} (ht : ∀ j, spRatio j ≤ theta) (r : ℝ) :
    (1-theta)*(liClockThetaScoreCostProfile (r:ℂ)).re ≤
      (liClockThetaScoreReserveProfile (r:ℂ)).re ∧
    (liClockThetaScoreReserveProfile (r:ℂ)).re <
      (liClockThetaScoreCostProfile (r:ℂ)).re ∧
    303*K1 r ≤ theta*(liClockThetaScoreCostProfile (r:ℂ)).re := by
  have hc (j : ℕ) : spAdj j ≤ theta*spCost j := by
    apply (div_le_iff₀ (sp_coeff_pos j).2.1).1
    rw [sp_ratio_eq]
    exact ht j
  have hs := liClockPositiveEvenSeries_le_ceiling hc r
    (sp_real_summable sp_adj_bound r) (sp_real_summable sp_coefficient_bounds.2.2.2.1 r)
  rw [←sp_scaled_second,←(sp_profiles_real r).2.1] at hs
  have he := liClockThetaScoreProfiles_cost_identity r
  have hp := (sp_profiles_positive r).2.2.2
  exact ⟨by nlinarith,by linarith,hs⟩

/-- One strict coefficient ceiling supplies a positive reserve at every real clock. -/
theorem liClockThetaScoreProfiles_uniform_reserve :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧
      (∀ j : ℕ, (1-theta)*(32*(j:ℝ)+17)*nu j ≤
        liClockThetaScoreMomentGap j) ∧
      ∀ r : ℝ, 0 < (liClockThetaSmoothedBorelProfile (r:ℂ)).re ∧
        0 < (liClockThetaScoreCostProfile (r:ℂ)).re ∧
        0 < (liClockThetaScoreReserveProfile (r:ℂ)).re ∧
        (1-theta)*(liClockThetaScoreCostProfile (r:ℂ)).re ≤
          (liClockThetaScoreReserveProfile (r:ℂ)).re ∧
        (liClockThetaScoreReserveProfile (r:ℂ)).re <
          (liClockThetaScoreCostProfile (r:ℂ)).re ∧
        0 < 303*K1 r ∧
        303*K1 r ≤ theta*(liClockThetaScoreCostProfile (r:ℂ)).re := by
  obtain ⟨theta,ht0,ht1,ht⟩ := sp_uniform_ceiling
  refine ⟨theta,ht0,ht1,?_,?_⟩
  · intro j
    have hd : 0 < (32*(j:ℝ)+17)*nu j :=
      mul_pos (by positivity) (thetaCuspNormalizedEvenMoment_pos j)
    have hh := (div_le_iff₀ hd).1 (ht j)
    unfold liClockThetaScoreMomentGap
    nlinarith
  · intro r
    have hp := sp_profiles_positive r
    have hb := sp_uniform_profiles ht r
    exact ⟨hp.1,hp.2.1,hp.2.2.1,hb.1,hb.2.1,hp.2.2.2,hb.2.2⟩


private theorem sp_second_cost_tendsto :
    Tendsto (fun r : ℝ => 303*K1 r/(liClockThetaScoreCostProfile (r:ℂ)).re)
      atTop (𝓝 (0:ℝ)) := by
  have hq : Tendsto (fun j => spAdj j/spCost j) atTop (𝓝 (0:ℝ)) := by
    simpa only [sp_ratio_eq] using sp_ratio_tendsto
  have hh := liClockPositiveEvenSeries_ratio_tendsto
    (fun j => (sp_coeff_pos j).2.2.2.le) (fun j => (sp_coeff_pos j).2.1)
    (sp_real_summable sp_adj_bound) (sp_real_summable sp_coefficient_bounds.2.2.2.1) hq
  have he : (fun r : ℝ => 303*K1 r/(liClockThetaScoreCostProfile (r:ℂ)).re)=
      (fun r => liClockPositiveEvenSeries spAdj r/liClockPositiveEvenSeries spCost r) := by
    funext r
    rw [sp_scaled_second,(sp_profiles_real r).2.1]
  rw [he]
  exact hh

private theorem sp_reserve_cost_ratio (r : ℝ) :
    (liClockThetaScoreReserveProfile (r:ℂ)).re/(liClockThetaScoreCostProfile (r:ℂ)).re=
      1-303*K1 r/(liClockThetaScoreCostProfile (r:ℂ)).re := by
  have hp := (sp_profiles_positive r).2.1
  have he := liClockThetaScoreProfiles_cost_identity r
  apply (div_eq_iff hp.ne').2
  field_simp
  linarith

private theorem sp_reserve_cost_tendsto :
    Tendsto (fun r : ℝ => (liClockThetaScoreReserveProfile (r:ℂ)).re/
      (liClockThetaScoreCostProfile (r:ℂ)).re) atTop (𝓝 (1:ℝ)) := by
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub sp_second_cost_tendsto
  simpa only [sub_zero,←sp_reserve_cost_ratio] using hh

private theorem sp_reserve_ratio_lt_one (r : ℝ) :
    (liClockThetaScoreReserveProfile (r:ℂ)).re/(liClockThetaScoreCostProfile (r:ℂ)).re < 1 := by
  apply (div_lt_one (sp_profiles_positive r).2.1).2
  have he := liClockThetaScoreProfiles_cost_identity r
  have hp := (sp_profiles_positive r).2.2.2
  linarith

/-- The fixed large-clock reserve ratio tends to its optimal supremum one. -/
theorem liClockThetaScoreProfiles_sharp_reserve :
    Tendsto (fun r : ℝ => 303*K1 r/
      (liClockThetaScoreCostProfile (r:ℂ)).re) atTop (𝓝 (0:ℝ)) ∧
    Tendsto (fun r : ℝ => (liClockThetaScoreReserveProfile (r:ℂ)).re/
      (liClockThetaScoreCostProfile (r:ℂ)).re) atTop (𝓝 (1:ℝ)) ∧
    sSup ((fun r : ℝ => (liClockThetaScoreReserveProfile (r:ℂ)).re/
      (liClockThetaScoreCostProfile (r:ℂ)).re) '' Ici 0) = 1 := by
  refine ⟨sp_second_cost_tendsto,sp_reserve_cost_tendsto,?_⟩
  let f : ℝ → ℝ := fun r => (liClockThetaScoreReserveProfile (r:ℂ)).re/
    (liClockThetaScoreCostProfile (r:ℂ)).re
  have hne : (f '' Ici 0).Nonempty := ⟨f 0,0,by simp,rfl⟩
  have hb : BddAbove (f '' Ici 0) := by
    refine ⟨1,?_⟩
    rintro _ ⟨r,_,rfl⟩
    exact (sp_reserve_ratio_lt_one r).le
  apply le_antisymm
  · exact csSup_le hne (by rintro _ ⟨r,_,rfl⟩; exact (sp_reserve_ratio_lt_one r).le)
  · apply le_of_tendsto sp_reserve_cost_tendsto
    filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    exact le_csSup hb ⟨r,hr,rfl⟩

end
end RHTower
