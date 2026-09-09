import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPositiveMean
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspNonparabolicHeight
import GaloisForLFunctions.RHTower.SelbergScatteringFiniteQuarterPacket
import Mathlib.Analysis.Normed.Algebra.Exponential
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularStripPowerAdmission
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-!
# Locally resummed complete Eisenstein source

Every complete shifted Eisenstein field retains both Weyl terms and all Fourier
modes. Absolute double summability identifies their pointwise Taylor resummation
with the full modular row source of y^s exp(-y). For 2 <= Re(s) <= 3 this source
belongs to the original native L2 space; complete absolute unfolding evaluates
its mean as Gamma(s-1), which is nonzero. All statements specialize without
additional assumptions to s = rho/2 + 2 for every actual Xi copy.

The shared scalar entire-transform value of the summands is proved. No infinite
operator interchange or native entire occurrence follows from this identity.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
namespace RHTower.SelbergResummedSource
open D4BMModularCore D4BMJointSource D4BMGlobalAngularResponse
noncomputable section

/-- A literal exponentially damped height seed; no Fourier mode or modular row is discarded. -/
def profile (s : ℂ) (y : ℝ) : ℂ := (y:ℂ)^s*Complex.exp (-(y:ℂ))

/-- Full projective modular periodization of the resummed height profile. -/
def source (s : ℂ) (z : UpperHalfPlane) : ℂ := periodize (cuspHeightSeed (profile s)) z

/-- Every actual modular height is bounded at a fixed original point. -/
theorem row_height_bound (v : gammaSetHalf) (z : UpperHalfPlane) :
    (gammaSetMatrix v.1 • z).im ≤ max z.im (1/z.im) := by
  by_cases hv : v=cuspIdentityRow
  · rw [hv,cuspIdentityRow_height]
    exact le_max_left _ _
  · exact (cuspRow_nonparabolic_height_le v hv z).trans (le_max_right _ _)

/-- Damping leaves the original absolute-convergence power as a pointwise majorant. -/
theorem profile_norm_le (s : ℂ) {y : ℝ} (hy : 0 < y) : ‖profile s y‖ ≤ y^s.re := by
  rw [profile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.norm_exp]
  apply mul_le_of_le_one_right (Real.rpow_nonneg hy.le _)
  apply Real.exp_le_one_iff.mpr
  simpa using hy.le

/-- The resummed seed has an absolutely convergent complete modular row sum. -/
theorem profile_rows_summable (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun v : gammaSetHalf => profile s (gammaSetMatrix v.1 • z).im) :=
  Summable.of_norm_bounded (positiveCuspRows_summable s.re hs z)
    (fun v => profile_norm_le s (gammaSetMatrix v.1 • z).im_pos)

/-- The actual orbit sum equals its complete row realization. -/
theorem source_eq_rows (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    source s z = ∑' v : gammaSetHalf, profile s (gammaSetMatrix v.1 • z).im :=
  periodize_cuspHeightSeed_eq_rows_of_rows_summable _ z (profile_rows_summable s hs z)

/-- One retained Taylor term before either infinite sum is interchanged. -/
def rowTerm (s : ℂ) (z : UpperHalfPlane) (n : ℕ) (v : gammaSetHalf) : ℂ :=
  ((gammaSetMatrix v.1 • z).im:ℂ)^s *
    ((-((gammaSetMatrix v.1 • z).im:ℂ))^n/(n.factorial:ℂ))

/-- The literal exponential series sums each original row, with its original complex power. -/
theorem rowTerm_hasSum (s : ℂ) (z : UpperHalfPlane) (v : gammaSetHalf) :
    HasSum (fun n => rowTerm s z n v) (profile s (gammaSetMatrix v.1 • z).im) := by
  have he : HasSum (fun n : ℕ => (-((gammaSetMatrix v.1 • z).im:ℂ))^n/(n.factorial:ℂ))
      (Complex.exp (-((gammaSetMatrix v.1 • z).im:ℂ))) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  exact he.mul_left _

/-- A separable summable majorant controls the complete double series. -/
theorem rowTerm_norm_bound (s : ℂ) (z : UpperHalfPlane) (n : ℕ) (v : gammaSetHalf) :
    ‖rowTerm s z n v‖ ≤ (max z.im (1/z.im))^n/(n.factorial:ℝ)*
      (gammaSetMatrix v.1 • z).im^s.re := by
  have hy := (gammaSetMatrix v.1 • z).im_pos
  rw [rowTerm,norm_mul,norm_div,norm_pow,norm_neg,Complex.norm_real,
    Real.norm_of_nonneg hy.le,Complex.norm_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hy]
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy.le _)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hy.le (row_height_bound v z) n)
    (Nat.cast_nonneg _)

/-- Absolute double summability justifies resummation in the actual modular row coordinates. -/
theorem rowTerm_double_summable (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun p : ℕ × gammaSetHalf => rowTerm s z p.1 p.2) := by
  let H := max z.im (1/z.im)
  have hH : 0 ≤ H := z.im_pos.le.trans (le_max_left _ _)
  have hmaj : Summable (fun p : ℕ × gammaSetHalf => H^p.1/(p.1.factorial:ℝ)*
      (gammaSetMatrix p.2.1 • z).im^s.re) := by
    apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
    constructor
    · intro n
      exact (positiveCuspRows_summable s.re hs z).mul_left (H^n/(n.factorial:ℝ))
    · simp_rw [tsum_mul_left]
      exact (Real.summable_pow_div_factorial H).mul_right _
  exact Summable.of_norm_bounded hmaj (fun p => rowTerm_norm_bound s z p.1 p.2)

/-- Resumming the complete Taylor coefficients before taking the native norm recovers the actual source. -/
theorem source_eq_tsum_rows (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    source s z = ∑' n : ℕ, ∑' v : gammaSetHalf, rowTerm s z n v := by
  have he : (∑' v : gammaSetHalf, ∑' n : ℕ, rowTerm s z n v) =
      ∑' n : ℕ, ∑' v : gammaSetHalf, rowTerm s z n v :=
    (rowTerm_double_summable s hs z).tsum_comm
  rw [← he]
  rw [source_eq_rows s hs z]
  exact tsum_congr (fun v => (rowTerm_hasSum s z v).tsum_eq.symm)

/-- Exact completed-field coefficient in the locally resummed packet. -/
def coefficient (s : ℂ) (n : ℕ) : ℂ :=
  (-1:ℂ)^n/((n.factorial:ℂ)*reflectedCompletedLambda (2*(s+(n:ℂ))))

private theorem rowTerm_power (s : ℂ) (z : UpperHalfPlane) (n : ℕ) (v : gammaSetHalf) :
    rowTerm s z n v = ((-1:ℂ)^n/(n.factorial:ℂ))*
      ((gammaSetMatrix v.1 • z).im:ℂ)^(s+(n:ℂ)) := by
  have hy := (gammaSetMatrix v.1 • z).im_pos
  rw [rowTerm,Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'),Complex.cpow_natCast]
  rw [neg_eq_neg_one_mul,mul_pow]
  ring

/-- Every resummed coefficient retains the exact original completion normalization. -/
theorem rowTerm_tsum_eq_complete (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) (n : ℕ) :
    (∑' v : gammaSetHalf, rowTerm s z n v) =
      coefficient s n*scalar (s+(n:ℂ)-1/2) (coordinates z) := by
  have hn : 1 < (s+(n:ℂ)).re := by
    simp only [Complex.add_re,Complex.natCast_re]
    linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]
  let P : D4BMEisensteinAbsoluteConvergenceParameter := ⟨s+(n:ℂ),hn⟩
  have hL := cuspCompletedLambda_ne_zero (s:=2*(s+(n:ℂ))) (by
    have hn0 := hn
    norm_num [Complex.mul_re] at hn0 ⊢
    linarith)
  have hrow := periodize_cuspHeightSeed_eq_rows_of_rows_summable
    (fun y : ℝ => (y:ℂ)^(s+(n:ℂ))) z (cuspHeightPower_rows_summable P z)
  have hfield : reflectedCompletedLambda (2*(s+(n:ℂ)))*
      (∑' v : gammaSetHalf, ((gammaSetMatrix v.1 • z).im:ℂ)^(s+(n:ℂ))) =
        scalar (s+(n:ℂ)-1/2) (coordinates z) :=
    (congrArg (fun r : ℂ => reflectedCompletedLambda (2*(s+(n:ℂ)))*r) hrow).symm.trans
      (cuspHeightPower_periodize_completed P z)
  calc
    _ = ((-1:ℂ)^n/(n.factorial:ℂ))*
        (∑' v : gammaSetHalf, ((gammaSetMatrix v.1 • z).im:ℂ)^(s+(n:ℂ))) := by
      simp_rw [rowTerm_power]
      exact tsum_mul_left
    _ = coefficient s n*(reflectedCompletedLambda (2*(s+(n:ℂ)))*
        (∑' v : gammaSetHalf, ((gammaSetMatrix v.1 • z).im:ℂ)^(s+(n:ℂ)))) := by
      unfold coefficient
      have hL' : reflectedCompletedLambda ((s+(n:ℂ))*2) ≠ 0 := by
        simpa only [mul_comm] using hL
      field_simp [hL,hL']
    _ = _ := congrArg (fun r : ℂ => coefficient s n*r) hfield

/-- Absolute summability of the complete shifted Eisenstein fields at every original point. -/
theorem complete_series_summable (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    Summable (fun n : ℕ => coefficient s n*scalar (s+(n:ℂ)-1/2) (coordinates z)) := by
  have h := (rowTerm_double_summable s hs z).prod
  exact h.congr (fun n => rowTerm_tsum_eq_complete s hs z n)

/-- The actual locally resummed complete Eisenstein packet is the literal damped modular source. -/
theorem source_eq_complete_series (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    source s z = ∑' n : ℕ, coefficient s n*scalar (s+(n:ℂ)-1/2) (coordinates z) := by
  rw [source_eq_tsum_rows s hs z]
  exact tsum_congr (fun n => rowTerm_tsum_eq_complete s hs z n)

/-- The complete resummed source retains the original modular invariance. -/
theorem source_invariant (s : ℂ) (γ : PSL2Z) (z : UpperHalfPlane) :
    source s (γ • z) = source s z := periodize_invariant _ γ z

/-- The actual height profile is continuous before modular summation. -/
theorem profile_continuous (s : ℂ) (hs : 0 < s.re) : Continuous (profile s) :=
  (Complex.continuous_ofReal_cpow_const hs).mul (Complex.continuous_exp.comp (by fun_prop))

/-- The complete locally resummed source is measurable in the original modular coordinates. -/
theorem source_measurable (s : ℂ) (hs : 0 < s.re) : Measurable (source s) :=
  periodize_measurable _ (cuspHeightSeed_measurable _ (profile_continuous s hs).measurable)

/-- In the source's actual parameter strip, one quadratic majorant controls every row. -/
theorem profile_norm_le_sq (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3)
    {y : ℝ} (hy : 0 < y) : ‖profile s y‖ ≤ y^2 := by
  rw [profile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.norm_exp]
  simp only [Complex.neg_re,Complex.ofReal_re]
  by_cases hy1 : y ≤ 1
  · have hp : y^s.re ≤ y^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hy hy1 hs
    exact (mul_le_of_le_one_right (Real.rpow_nonneg hy.le _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans hp
  · have hp : y^s.re ≤ y^3 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hy1) hs'
    have he : y*Real.exp (-y) ≤ 1 := by
      rw [Real.exp_neg,← div_eq_mul_inv]
      exact (div_le_one (Real.exp_pos y)).mpr (by linarith [Real.add_one_le_exp y])
    calc
      _ ≤ y^3*Real.exp (-y) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = y^2*(y*Real.exp (-y)) := by ring
      _ ≤ y^2 := mul_le_of_le_one_right (sq_nonneg _) he

/-- Exponential damping uniformly bounds the original parabolic profile. -/
theorem profile_norm_le_six (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3)
    {y : ℝ} (hy : 0 < y) : ‖profile s y‖ ≤ 6 := by
  by_cases hy1 : y ≤ 1
  · have h := profile_norm_le_sq s hs hs' hy
    nlinarith
  · rw [profile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.norm_exp]
    simp only [Complex.neg_re,Complex.ofReal_re]
    have hp : y^s.re ≤ y^3 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hy1) hs'
    have he := Real.pow_div_factorial_le_exp y hy.le 3
    norm_num only [Nat.factorial] at he
    calc
      _ ≤ y^3*Real.exp (-y) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ ≤ 6 := by
        rw [Real.exp_neg,← div_eq_mul_inv]
        exact (div_le_iff₀ (Real.exp_pos y)).mpr (by linarith)

private theorem positiveRows_two_principal (z : UpperHalfPlane) :
    principal ((2:ℂ)-1/2) (coordinates z) =
      reflectedCompletedLambda 3*(z.im:ℂ)^(-1:ℂ)+reflectedCompletedLambda 4*(z.im:ℂ)^2 := by
  norm_num [D4BMGlobalAngularResponse.principal,coordinates,d4BMCompletedEisensteinCuspConstantPart,
    d4BMCompletedEisensteinCuspConstantTerm,d4BMCompletedEisensteinCuspConstantCoefficient,
    d4BMCompletedEisensteinCuspConstantMaassFactor,d4BMCompletedEisensteinCuspWeylExponent,d4BMCuspSign]

/-- The full nonparabolic quadratic row mass is bounded down to the native cell's lower height. -/
theorem nonparabolic_quadratic_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ z : UpperHalfPlane,
    1/2 ≤ z.im → positiveCuspRows 2 z-z.im^2 ≤ B := by
  obtain ⟨C,hC,hbound⟩ := weighted_tail_bounded ((2:ℂ)-1/2) 0 (1/2) (by norm_num)
  have hL : reflectedCompletedLambda 4 ≠ 0 := cuspCompletedLambda_ne_zero (by norm_num)
  refine ⟨(2*‖reflectedCompletedLambda 3‖+C)/‖reflectedCompletedLambda 4‖,by positivity,?_⟩
  intro z hz
  have he : ((positiveCuspRows 2 z-z.im^2:ℝ):ℂ) =
      (reflectedCompletedLambda 3*(z.im:ℂ)^(-1:ℂ)+tail ((2:ℂ)-1/2) (coordinates z))/
        reflectedCompletedLambda 4 := by
    apply (eq_div_iff hL).mpr
    have hp := positiveCuspRows_completed 2 (by norm_num) z
    change reflectedCompletedLambda (2*(2:ℂ))*(positiveCuspRows 2 z:ℂ) =
      principal ((2:ℂ)-1/2) (coordinates z)+tail ((2:ℂ)-1/2) (coordinates z) at hp
    rw [positiveRows_two_principal] at hp
    norm_num only at hp
    push_cast
    norm_num only
    linear_combination hp
  have ht : ‖tail ((2:ℂ)-1/2) (coordinates z)‖ ≤ C := by
    simpa only [cpow_zero,one_mul] using hbound (coordinates z) hz
  have hy : ‖(z.im:ℂ)^(-1:ℂ)‖ ≤ 2 := by
    rw [Complex.cpow_neg_one,norm_inv,Complex.norm_real,Real.norm_of_nonneg z.im_pos.le]
    exact (inv_le_comm₀ z.im_pos (by norm_num)).mpr (by simpa using hz)
  calc
    _ ≤ |positiveCuspRows 2 z-z.im^2| := le_abs_self _
    _ = ‖((positiveCuspRows 2 z-z.im^2:ℝ):ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := by
      rw [he,norm_div]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact (norm_add_le _ _).trans (by rw [norm_mul]; nlinarith [norm_nonneg (reflectedCompletedLambda 3)])

/-- The complete source's norm is controlled by its damped parabolic row and actual remaining rows. -/
theorem source_norm_le_rows (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3)
    (z : UpperHalfPlane) : ‖source s z‖ ≤ 6+(positiveCuspRows 2 z-z.im^2) := by
  classical
  have hsum := profile_rows_summable s (by linarith) z
  have hquad := positiveCuspRows_summable 2 (by norm_num) z
  have hn : Summable (fun v : gammaSetHalf => if v=cuspIdentityRow then (0:ℝ)
      else ‖profile s (gammaSetMatrix v.1 • z).im‖) :=
    hsum.norm.of_nonneg_of_le (fun v => by split_ifs <;> positivity)
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
  have hq : Summable (fun v : gammaSetHalf => if v=cuspIdentityRow then (0:ℝ)
      else (gammaSetMatrix v.1 • z).im^2) := by
    have hquad' : Summable (fun v : gammaSetHalf => (gammaSetMatrix v.1 • z).im^2) := by
      simpa only [Real.rpow_two] using hquad
    exact hquad'.of_nonneg_of_le (fun v => by split_ifs <;> positivity)
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
  have hle := hn.tsum_le_tsum (fun v => show
      (if v=cuspIdentityRow then (0:ℝ) else ‖profile s (gammaSetMatrix v.1 • z).im‖) ≤
      (if v=cuspIdentityRow then (0:ℝ) else (gammaSetMatrix v.1 • z).im^2) from by
    split_ifs
    · exact le_rfl
    · exact profile_norm_le_sq s hs hs' (gammaSetMatrix v.1 • z).im_pos) hq
  have hsplit := hsum.norm.tsum_eq_add_tsum_ite cuspIdentityRow
  have hquadSplit := hquad.tsum_eq_add_tsum_ite cuspIdentityRow
  rw [cuspIdentityRow_height] at hsplit hquadSplit
  change positiveCuspRows 2 z = _ at hquadSplit
  simp only [Real.rpow_two] at hquadSplit
  rw [source_eq_rows s (by linarith) z]
  have hnorm := norm_tsum_le_tsum_norm hsum.norm
  have hid := profile_norm_le_six s hs hs' z.im_pos
  linarith

/-- The literal resummed complete source is bounded on the original modular cell. -/
theorem source_bounded (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ModularGroup.fd, ‖source s z‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := nonparabolic_quadratic_bound
  refine ⟨6+B,by positivity,?_⟩
  intro z hz
  have hheight : 1/2 ≤ z.im := by
    have hsq := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
    have him := z.im_pos
    nlinarith
  exact (source_norm_le_rows s hs hs' z).trans (by linarith [hbound z hheight])

/-- Resummation gives an admitted source in the original native Hilbert space. -/
theorem source_memLp (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3) :
    MemLp (source s) 2 angularMeasure := by
  obtain ⟨C,_,hC⟩ := source_bounded s hs hs'
  apply MemLp.of_bound (source_measurable s (by linarith)).aestronglyMeasurable C
  exact (ae_restrict_mem ModularGroup.isClosed_fd.measurableSet).mono hC

/-- The actual height seed is admitted on the full unfolded modular strip. -/
theorem profile_strip_integrable (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3) :
    IntegrableOn (fun z : UpperHalfPlane => profile s z.im) modularStrip volume := by
  apply modularStrip_integrable_of_two_bounds _
    ((profile_continuous s (by linarith)).comp continuous_im) 2 1 6 (by norm_num)
  · intro z _ _
    change ‖profile s z.im‖ ≤ 1*z.im^(2:ℝ)
    simpa only [one_mul,Real.rpow_two] using profile_norm_le_sq s hs hs' z.im_pos
  · intro z _ _
    exact profile_norm_le_six s hs hs' z.im_pos

private theorem profile_periodic (s : ℂ) (n : ℤ) (z : UpperHalfPlane) :
    profile s (ModularGroup.T^n • z).im = profile s z.im := by
  rw [ModularGroup.im_T_zpow_smul]

/-- Each literal row remains integrable before the complete source is unfolded. -/
theorem profile_row_integrable (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3)
    (v : gammaSetHalf) :
    Integrable (fun z : UpperHalfPlane => profile s (gammaSetMatrix v.1 • z).im) angularMeasure :=
  (integrableOn_smul_set_iff _ _ _).mp
    (integrableOn_smul_fd_of_periodic (profile_periodic s) (profile_strip_integrable s hs hs') _)

/-- Absolute integral summability makes full-row unfolding legitimate in the native measure. -/
theorem profile_integral_norm_summable (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3) :
    Summable (fun v : gammaSetHalf => ∫ z, ‖profile s (gammaSetMatrix v.1 • z).im‖ ∂angularMeasure) := by
  let φ : UpperHalfPlane → ℂ := fun z => (‖profile s z.im‖:ℂ)
  have hper : ∀ (n : ℤ) (z : UpperHalfPlane), φ (ModularGroup.T^n • z) = φ z := by
    intro n z
    exact congrArg (fun c : ℂ => (‖c‖:ℂ)) (profile_periodic s n z)
  have hi : IntegrableOn φ modularStrip volume :=
    (profile_strip_integrable s hs hs').norm.ofReal
  have h := (Complex.reCLM.hasSum (hasSum_fdUnfoldTerm_half hper hi)).summable
  convert h using 1
  funext v
  change (∫ z, ‖profile s (gammaSetMatrix v.1 • z).im‖ ∂angularMeasure) =
    (∫ z, (‖profile s (gammaSetMatrix v.1 • z).im‖:ℂ) ∂angularMeasure).re
  have he : (∫ z, (‖profile s (gammaSetMatrix v.1 • z).im‖:ℂ) ∂angularMeasure) =
      ((∫ z, ‖profile s (gammaSetMatrix v.1 • z).im‖ ∂angularMeasure : ℝ):ℂ) := integral_ofReal
  rw [he,Complex.ofReal_re]

/-- Exact unfolding of the whole resummed source, with absolute integral interchange discharged. -/
theorem source_integral_eq_strip (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3) :
    (∫ z, source s z ∂angularMeasure) = ∫ z in modularStrip, profile s z.im := by
  have ht := (hasSum_integral_of_summable_integral_norm
    (profile_row_integrable s hs hs') (profile_integral_norm_summable s hs hs')).tsum_eq
  have hu := (hasSum_fdUnfoldTerm_half (profile_periodic s)
    (profile_strip_integrable s hs hs')).tsum_eq
  rw [← isFundamentalDomain_modularStrip.setIntegral_eq isFundamentalDomain_iUnion_halfRep_smul_fd
    (translationSubgroup_invariant_of_periodic (profile_periodic s))] at hu
  calc
    _ = ∫ z, ∑' v : gammaSetHalf, profile s (gammaSetMatrix v.1 • z).im ∂angularMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall (source_eq_rows s (by linarith)))
    _ = _ := ht.symm.trans hu

/-- The full native mean is the nonvanishing Mellin integral of the actual damped seed. -/
theorem source_integral_eq_gamma (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3) :
    (∫ z, source s z ∂angularMeasure) = Complex.Gamma (s-1) := by
  rw [source_integral_eq_strip s hs hs',
    setIntegral_modularStrip_eq_iterated _ (profile_strip_integrable s hs hs'),
    Complex.Gamma_eq_integral (by simp only [Complex.sub_re,Complex.one_re]; linarith),
    Complex.GammaIntegral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have him (x : ℝ) : (ofComplex (⟨x,y⟩:ℂ)).im = y := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  simp only [him,integral_const,Measure.real,Measure.restrict_apply_univ,
    Real.volume_Ico,sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul]
  rw [profile,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
  have hc : (y:ℂ)^s/(y:ℂ)^2 = (y:ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hy))]
    norm_num
  rw [← div_eq_inv_mul,mul_div_right_comm,hc]
  rw [show s-1-1=s-2 by ring]
  simp only [Complex.ofReal_exp,Complex.ofReal_neg]
  ring

/-- Nonvanishing follows from the actual full source integral for every admitted parameter. -/
theorem source_integral_ne_zero (s : ℂ) (hs : 2 ≤ s.re) (hs' : s.re ≤ 3) :
    (∫ z, source s z ∂angularMeasure) ≠ 0 := by
  rw [source_integral_eq_gamma s hs hs']
  exact Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.sub_re,Complex.one_re]; linarith)

/-- The actual Xi parameter used by this complete resummation. -/
def xiParameter (q : XiZeroCopy) : ℂ := (q.1:ℂ)/2+2

theorem xiParameter_strip (q : XiZeroCopy) :
    2 ≤ (xiParameter q).re ∧ (xiParameter q).re ≤ 3 := by
  have h := xi_divisor_support_re_mem_open_unit q.1
  norm_num [xiParameter,Complex.add_re,Complex.div_ofNat_re]
  constructor <;> linarith [h.1,h.2]

/-- Every retained complete field lies in the intended quarter lattice. -/
theorem xiParameter_shift (q : XiZeroCopy) (n : ℕ) :
    xiParameter q+(n:ℂ)-1/2 =
      SelbergScatteringFiniteQuarterPacket.shiftedParameter q (8+4*(n:ℤ)) := by
  simp only [xiParameter,SelbergScatteringFiniteQuarterPacket.shiftedParameter,
    physicalAngularParameter_eq,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
  ring

/-- The whole locally resummed source is admitted for every actual Xi copy. -/
theorem xi_source_memLp (q : XiZeroCopy) : MemLp (source (xiParameter q)) 2 angularMeasure :=
  source_memLp _ (xiParameter_strip q).1 (xiParameter_strip q).2

/-- Absolute pointwise convergence of all complete shifted fields at every actual Xi parameter. -/
theorem xi_complete_series_summable (q : XiZeroCopy) (z : UpperHalfPlane) :
    Summable (fun n : ℕ => coefficient (xiParameter q) n*
      scalar (xiParameter q+(n:ℂ)-1/2) (coordinates z)) :=
  complete_series_summable _ (by linarith [(xiParameter_strip q).1]) z

/-- The admitted actual Xi source is the exact locally resummed complete-field packet. -/
theorem xi_source_eq_complete_series (q : XiZeroCopy) (z : UpperHalfPlane) :
    source (xiParameter q) z = ∑' n : ℕ, coefficient (xiParameter q) n*
      scalar (xiParameter q+(n:ℂ)-1/2) (coordinates z) :=
  source_eq_complete_series _ (by linarith [(xiParameter_strip q).1]) z

/-- All complete terms have the intended full Xi scalar target before resummation. -/
theorem xi_complete_term_same_target (q : XiZeroCopy) (n : ℕ) :
    SelbergScatteringEntireTransform.casimirTransform
      ((xiParameter q+(n:ℂ))*(1-(xiParameter q+(n:ℂ)))) =
        SelbergScatteringEntireXiPackets.xiEntireTarget q := by
  have he : xiParameter q+(n:ℂ) = 1/2+
      SelbergScatteringFiniteQuarterPacket.shiftedParameter q (8+4*(n:ℤ)) := by
    rw [← xiParameter_shift]
    ring
  rw [he]
  exact SelbergScatteringFiniteQuarterPacket.shifted_casimir_same_entire_target q _

/-- Unconditional nonvanishing of the full Xi source's actual native mean. -/
theorem xi_source_integral_ne_zero (q : XiZeroCopy) :
    (∫ z, source (xiParameter q) z ∂angularMeasure) ≠ 0 :=
  source_integral_ne_zero _ (xiParameter_strip q).1 (xiParameter_strip q).2

/-- The admitted original Hilbert vector, obtained after full local resummation. -/
def xiVector (q : XiZeroCopy) : Space := (xi_source_memLp q).toLp (source (xiParameter q))

theorem xiVector_coe (q : XiZeroCopy) : (xiVector q : UpperHalfPlane → ℂ) =ᵐ[angularMeasure]
    source (xiParameter q) := (xi_source_memLp q).coeFn_toLp

/-- Nonzero native mass belongs to the actual resummed vector. -/
theorem xiVector_integral_ne_zero (q : XiZeroCopy) :
    (∫ z, (xiVector q : UpperHalfPlane → ℂ) z ∂angularMeasure) ≠ 0 := by
  rw [integral_congr_ae (xiVector_coe q)]
  exact xi_source_integral_ne_zero q

theorem xiVector_ne_zero (q : XiZeroCopy) : xiVector q ≠ 0 := by
  intro he
  have h := xiVector_integral_ne_zero q
  rw [he,integral_congr_ae (Lp.coeFn_zero ℂ 2 angularMeasure)] at h
  exact h (by simp)

end
end RHTower.SelbergResummedSource
