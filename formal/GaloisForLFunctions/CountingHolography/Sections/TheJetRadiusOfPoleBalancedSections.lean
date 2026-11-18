import GaloisForLFunctions.CountingHolography.Sections.ThreeSquareConductorsWithZeroPoleDegree
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane
import GaloisForLFunctions.RHTower.EvenSectorWeightGrowth

/-!
# The jet radius on pole-balanced divisors

On a divisor of zero positive pole degree the two sampled pole moments
have product of subquadratic size. The ordinary-prime fractional ideal
of the three square conductors can therefore be tested using only the
negative regularized jet pairing at infinity. Its Fourier integral is
bounded by the squared coefficient mass times a single-atom integral.
Thus the prime product alone detects the full zero width.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open MeasureTheory Finset Filter Topology AbsoluteGeometryOfSpecZ ArithmeticScatteringHolography
open BiScaleUncertainty.ChebyshevGauge SquareRootThreshold

private def origin {N : ℕ} (i : Fin N) : ℝ := Real.log 3+5+Real.log ((i : ℝ)+1)

private theorem packet_expansion {N : ℕ} (a : Fin N → ℤ) (u : ℝ) :
    packet a u = ∑ i, (a i : ℝ)*cubicSpline (u-origin i) := by
  unfold packet splineSource
  apply sum_congr rfl
  intro i _
  congr 2
  change u-(Real.log 3+5)-Real.log ((i : ℝ)+1) = u-(Real.log 3+5+Real.log ((i : ℝ)+1))
  ring

private def poleMoment {N : ℕ} (a : Fin N → ℤ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, packet a u * Real.exp (t*u)

private theorem positive_poleMoment {N : ℕ} (a : Fin N → ℤ) (ha : positivePoleDegree a = 0) :
    poleMoment a (1/2) = 0 := by
  unfold poleMoment
  have hi (i : Fin N) : Integrable (fun u : ℝ =>
      (a i : ℝ)*cubicSpline (u-origin i)*Real.exp ((1/2)*u)) := by
    have hc : Continuous (fun u : ℝ => cubicSpline (u-origin i)) :=
      contDiff_cubicSpline.continuous.comp (continuous_id.sub continuous_const)
    apply ((continuous_const.mul hc).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    have hs : HasCompactSupport (fun u : ℝ => (a i : ℝ)*cubicSpline (u-origin i)) :=
      (hasCompactSupport_cubicSpline.comp_homeomorph (Homeomorph.subRight (origin i))).mul_left
    exact hs.mul_right
  simp_rw [packet_expansion,Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => hi i]
  let c := Real.log 3+5
  let M := ∫ u : ℝ, cubicSpline u * Real.exp ((1/2)*u)
  have hterm (i : Fin N) : (∫ u : ℝ, (a i : ℝ)*cubicSpline (u-origin i)*Real.exp ((1/2)*u)) =
      (Real.exp ((1/2)*c)*M)*(Real.sqrt ((i : ℝ)+1)*(a i : ℝ)) := by
    simp_rw [mul_assoc (a i : ℝ)]
    rw [integral_const_mul,SelectiveMultiscaleArithmeticPositivity.integral_shift_mul_exp]
    have hq : 0 < (i : ℝ)+1 := by positivity
    have hs : Real.exp ((1/2)*Real.log ((i : ℝ)+1)) = Real.sqrt ((i : ℝ)+1) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hq, mul_comm]
    change (a i : ℝ)*(Real.exp ((1/2)*(c+Real.log ((i : ℝ)+1)))*M) = _
    rw [mul_add,Real.exp_add,hs]
    ring
  simp only [hterm,← mul_sum]
  change _ * positivePoleDegree a = 0
  rw [ha,mul_zero]

private theorem ray_poleMoment {N : ℕ} (a : Fin N → ℤ) (t : ℝ) :
    Tendsto (fun m : ℕ => sampledDegree (packet (m • a)) (3*windowEnd N) (resolution (m • a)) t / m)
      atTop (𝓝 (poleMoment a t)) := by
  by_cases ha : a = 0
  · subst a
    simp [packet,splineSource,poleMoment,sampledDegree,degreeSample]
  have h := (tendsto_sampledDegree (packet_contDiff a).continuous (packet_window a).1
    (packet_window a).2 t).comp (tendsto_resolution_ray ha)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  change sampledDegree (packet a) _ _ t = _
  rw [packet_smul,sampledDegree_mul,mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt hm)]

/-- The radius retaining only the regularized archimedean jet pairing. -/
def jetRadius {N : ℕ} (a : Fin N → ℤ) : ℝ := -degreeForm (packet a) (3*windowEnd N) (resolution a)

/-- Both sampled moments can be deleted from the radius of a ray with
zero positive pole degree, at subquadratic cost. -/
theorem pole_correction_subquadratic {N : ℕ} (a : Fin N → ℤ) (ha : positivePoleDegree a = 0) :
    Tendsto (fun m : ℕ => (radius (m • a)-jetRadius (m • a))/(m : ℝ)^2) atTop (𝓝 0) := by
  have h := ((ray_poleMoment a (-(1/2))).mul (ray_poleMoment a (1/2))).const_mul 2
  rw [positive_poleMoment a ha,mul_zero,mul_zero] at h
  apply h.congr fun m => ?_
  rw [div_mul_div_comm, ← sq, ← mul_div_assoc]
  unfold radius jetRadius logRadius
  rw [sub_neg_eq_add, sub_add_cancel]

/-- With one negative graph, only ordinary prime contacts on the finite
side and the regularized jets at infinity are needed to read the width. -/
theorem zetaZeroWidth_le_iff_ordinaryTriple_jetRadius {s : ℝ} (hs : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (ordinaryPrimeGenerator (m • balancedPrimeTriple p) : ℝ) ≤ jetRadius (m • balancedPrimeTriple p) +
        (A*(p : ℝ)^(2*s)*(p : ℝ)^2)*(m : ℝ)^2 := by
  rw [zetaZeroWidth_le_iff_ordinaryTriple_sections hs]
  constructor <;> rintro ⟨A,hA⟩ <;> refine ⟨A+1,fun p hp => ?_⟩
  all_goals
    have h := (pole_correction_subquadratic _ (positivePoleDegree_balancedPrimeTriple hp)).abs
    rw [abs_zero] at h
    refine ((hA p hp).and_eventually ((h.eventually_lt_const zero_lt_one).and (eventually_ge_atTop 1))).mono
      fun m ⟨hm,he,hm1⟩ => ?_
    rw [abs_div,abs_of_nonneg (sq_nonneg (m : ℝ))] at he
    have hh := (div_lt_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp he
    rw [one_mul] at hh
    have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have hw := mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le
      (Real.one_le_rpow hp₁ (show 0 ≤ 2*s by linarith)) (one_le_pow₀ hp₁ : 1 ≤ (p : ℝ)^2))
      (sq_nonneg (m : ℝ))
    obtain ⟨hl,hu⟩ := abs_lt.mp hh
    linarith only [hl,hu,hw,hm]

private theorem rh_iff_width_nonpos : RiemannHypothesis ↔ zetaZeroWidth ≤ 0 :=
  riemannHypothesis_iff_zetaZeroWidth_eq_zero.trans
    ⟨fun h => h.le, fun h => le_antisymm h zetaZeroWidth_nonneg⟩

/-- An absolute quadratic allowance in the primitive coefficient p and
multiplicity m suffices on this fixed family of pole-balanced triples. -/
theorem riemannHypothesis_iff_ordinaryTriple_jetRadius :
    RiemannHypothesis ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (ordinaryPrimeGenerator (m • balancedPrimeTriple p) : ℝ) ≤
        jetRadius (m • balancedPrimeTriple p) + A*(p : ℝ)^2*(m : ℝ)^2 := by
  rw [rh_iff_width_nonpos]
  simpa only [mul_zero,Real.rpow_zero,mul_one] using zetaZeroWidth_le_iff_ordinaryTriple_jetRadius
    (s := 0) le_rfl

open Zeta23 _root_.RHTower _root_.RHTower.WeilOneSided
open scoped Real

private def gammaValue (f : ℝ → ℂ) : ℝ :=
  ((1/(2*π) : ℂ) * ∫ r : ℝ, paperFT (EF.weilTest f f) r * (EF.gammaBracket r : ℂ)).re

private def atomGammaMass : ℝ :=
  ∫ r : ℝ, ‖paperFT (EF.weilTest (liftC cubicSpline) (liftC cubicSpline)) r * (mu r : ℂ)‖

private theorem atomGammaMass_nonneg : 0 ≤ atomGammaMass := integral_nonneg fun _ => norm_nonneg _

/-- Translating the atoms changes only their phases on the real Fourier axis. -/
private theorem abs_packet_gammaValue_le {N : ℕ} (a : Fin N → ℤ) :
    |gammaValue (liftC (packet a))| ≤ (∑ i, |(a i : ℝ)|)^2 * atomGammaMass := by
  let M := ∑ i, |(a i : ℝ)|
  have hc := (contDiff_liftC contDiff_cubicSpline).continuous
  have hcs := hasCompactSupport_liftC hasCompactSupport_cubicSpline
  have hpc := (contDiff_liftC (packet_contDiff a)).continuous
  have hpcs := hasCompactSupport_liftC (packet_hasCompactSupport a)
  have hb := (EF.integrable_paperFT_mul_mu
    (EF.weilTest_contDiff (contDiff_liftC contDiff_cubicSpline) hc hcs)
    (EF.weilTest_hasCompactSupport hcs hcs) gammaFacts).norm
  have hex : liftC (packet a) = fun u =>
      ∑ i, ((a i : ℝ) : ℂ)*liftC cubicSpline (u-origin i) := by
    funext u
    simp only [liftC,packet_expansion,Complex.ofReal_sum,Complex.ofReal_mul]
  have hF (r : ℝ) : ‖paperFT (liftC (packet a)) r‖ ≤ M*‖paperFT (liftC cubicSpline) r‖ := by
    rw [hex]
    simpa only [M,Complex.norm_real,Real.norm_eq_abs] using
      EvenSector.norm_paperFT_sum_translate_le univ (fun i => ((a i : ℝ) : ℂ)) origin hc hcs r
  unfold gammaValue atomGammaMass
  rw [EF.gamma_term, ← integral_const_mul]
  refine (Complex.abs_re_le_norm _).trans (norm_integral_le_of_norm_le (hb.const_mul (M^2))
    (Eventually.of_forall fun r => ?_))
  rw [paperFT_weilTest_self_ofReal hpc hpcs,paperFT_weilTest_self_ofReal hc hcs]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_pow,abs_norm]
  have h := pow_le_pow_left₀ (norm_nonneg _) (hF r) 2
  rw [mul_pow] at h
  exact (mul_le_mul_of_nonneg_right h (abs_nonneg (mu r))).trans_eq (mul_assoc _ _ _)

private theorem tendsto_jetRadius {N : ℕ} {a : Fin N → ℤ} (ha : a ≠ 0) :
    Tendsto (fun m : ℕ => jetRadius (m • a)/(m : ℝ)^2) atTop (𝓝 (gammaValue (liftC (packet a)))) := by
  have h := ((tendsto_degreeForm (packet_contDiff a) (packet_hasCompactSupport a)
    (packet_window a).1 (packet_window a).2).comp (tendsto_resolution_ray ha)).neg
  simp only [neg_neg, weilArchRe, weilPoleTerm, Complex.add_re, add_sub_cancel_left] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  change -degreeForm (packet a) _ _ = _
  rw [jetRadius,packet_smul,degreeForm_mul,neg_div,mul_div_cancel_left₀ _ (by positivity : (m : ℝ)^2 ≠ 0)]

private theorem eventually_jetRadius_bound {N : ℕ} (a : Fin N → ℤ) :
    ∀ᶠ m : ℕ in atTop, |jetRadius (m • a)| ≤
      ((∑ i, |(a i : ℝ)|)^2*atomGammaMass+1)*(m : ℝ)^2 := by
  by_cases ha : a = 0
  · subst a
    filter_upwards with m
    simp [jetRadius,packet,splineSource,degreeForm,degreePairing,degreeSample]
  have hlt := (abs_packet_gammaValue_le a).trans_lt (lt_add_one _)
  filter_upwards [(tendsto_jetRadius ha).abs.eventually_lt_const hlt,eventually_ge_atTop 1] with m hm hm1
  rw [abs_div,abs_of_nonneg (sq_nonneg (m : ℝ))] at hm
  exact ((div_lt_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp hm).le

/-- The regularized jets of the balanced triple cost at most one absolute
multiple of the squared coefficient mass, uniformly in its prime. -/
theorem eventually_balanced_jetRadius_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, p.Prime → ∀ᶠ m : ℕ in atTop,
      |jetRadius (m • balancedPrimeTriple p)| ≤ C*(p : ℝ)^2*(m : ℝ)^2 := by
  refine ⟨4*atomGammaMass+1,by linarith only [atomGammaMass_nonneg],fun p hp => ?_⟩
  have hmass := balancedPrimeTriple_mass hp 1
  simp only [one_smul,Nat.cast_one,mul_one] at hmass
  have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hmass 2)
    atomGammaMass_nonneg
  have hp' : (1 : ℝ) ≤ (p : ℝ)^2 := one_le_pow₀ (by exact_mod_cast hp.one_le)
  exact (eventually_jetRadius_bound _).mono fun m hm => hm.trans
    (mul_le_mul_of_nonneg_right (by linarith only [hh,hp']) (sq_nonneg (m : ℝ)))

/-- For any divisor annihilating the positive pole, the discrepancy between
the negative signed degree and its ordinary-prime product is bounded in
terms of total variation alone after passing far enough along its ray. -/
theorem poleBalanced_ordinary_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ), positivePoleDegree a = 0 → ∀ᶠ m : ℕ in atTop,
      |Real.log (ordinaryPrimeGenerator (m • a) : ℝ) + integerProbe N a*(m : ℝ)^2| ≤
        (C*(∑ i, |(a i : ℝ)|)^2+4)*(m : ℝ)^2 := by
  obtain ⟨D,hD,hd⟩ := eventually_signed_prime_error
  refine ⟨D+atomGammaMass,add_nonneg hD atomGammaMass_nonneg,fun N a ha => ?_⟩
  have hp := (pole_correction_subquadratic a ha).abs
  rw [abs_zero] at hp
  have hq := tendsto_splineDegree a
  filter_upwards [hd N a,eventually_jetRadius_bound a,hp.eventually_lt_const zero_lt_one,
    hq.eventually_lt_const (lt_add_one _),hq.eventually_const_lt (sub_one_lt _),eventually_ge_atTop 1]
    with m hm hj hpol hhi hlo hm1
  have hm' : 0 < (m : ℝ)^2 := by positivity
  rw [abs_div,abs_of_pos hm'] at hpol
  have hpol' := (div_lt_iff₀ hm').mp hpol
  rw [one_mul] at hpol'
  obtain ⟨hpl,hpu⟩ := abs_lt.mp hpol'
  obtain ⟨hdl,hdu⟩ := abs_le.mp hm
  obtain ⟨hjl,hju⟩ := abs_le.mp hj
  have h₁ := (div_lt_iff₀ hm').mp hhi
  have h₂ := (lt_div_iff₀ hm').mp hlo
  exact abs_le.mpr ⟨by linarith only [hpl,hdl,hdu,hjl,h₁],
    by linarith only [hpu,hdl,hdu,hju,h₂]⟩

/-- The finite-place test uses only the rational product of ordinary
prime contacts. Its allowable exponent, above p², reads the zero width. -/
theorem zetaZeroWidth_le_iff_ordinaryTriple_generator {s : ℝ} (hs : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (ordinaryPrimeGenerator (m • balancedPrimeTriple p) : ℝ) ≤
        (A*(p : ℝ)^(2*s)*(p : ℝ)^2)*(m : ℝ)^2 := by
  rw [zetaZeroWidth_le_iff_ordinaryTriple_jetRadius hs]
  obtain ⟨C,hC,hjet⟩ := eventually_balanced_jetRadius_bound
  constructor <;> rintro ⟨A,hA⟩ <;> refine ⟨A+C,fun p hp => ?_⟩
  all_goals
    refine ((hA p hp).and_eventually (hjet p hp)).mono fun m ⟨hm,hj⟩ => ?_
    have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hw := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.one_le_rpow hp₁ (show 0 ≤ 2*s by linarith)) hC)
      (sq_nonneg (p : ℝ))) (sq_nonneg (m : ℝ))
    obtain ⟨hl,hu⟩ := abs_le.mp hj
    linarith only [hm,hw,hl,hu]

theorem riemannHypothesis_iff_ordinaryTriple_generator :
    RiemannHypothesis ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (ordinaryPrimeGenerator (m • balancedPrimeTriple p) : ℝ) ≤ A*(p : ℝ)^2*(m : ℝ)^2 := by
  rw [rh_iff_width_nonpos]
  simpa only [mul_zero,Real.rpow_zero,mul_one] using zetaZeroWidth_le_iff_ordinaryTriple_generator
    (s := 0) le_rfl

theorem generator_le_power_iff {N : ℕ} (a : Fin N → ℤ) {B : ℕ} (hB : 0 < B) (p m : ℕ) :
    ordinaryPrimeGenerator a ≤ (B : ℚ)^((p*m)^2) ↔
      Real.log (ordinaryPrimeGenerator a : ℝ) ≤ Real.log B*(p : ℝ)^2*(m : ℝ)^2 := by
  have hg : 0 < ordinaryPrimeGenerator a := Finset.prod_pos fun k _ =>
    zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _
  have hB' : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
  have he : Real.log ((B : ℝ)^((p*m)^2)) = Real.log B*(p : ℝ)^2*(m : ℝ)^2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [← he,Real.log_le_log_iff (by exact_mod_cast hg) (pow_pos hB' _)]
  constructor <;> intro h <;> exact_mod_cast h

/-- One integer base suffices for all finite rational comparisons. -/
theorem riemannHypothesis_iff_ordinaryTriple_power :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      ordinaryPrimeGenerator (m • balancedPrimeTriple p) ≤ (B : ℚ)^((p*m)^2) := by
  rw [riemannHypothesis_iff_ordinaryTriple_generator]
  constructor
  · rintro ⟨A,hA⟩
    let B := ⌈Real.exp A⌉₊
    have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos A)
    have hl : A ≤ Real.log B := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil _)
    refine ⟨B,hB,fun p hp => (hA p hp).mono fun m hm => ?_⟩
    exact (generator_le_power_iff _ hB p m).mpr (hm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hl (sq_nonneg _)) (sq_nonneg _)))
  · rintro ⟨B,hB,h⟩
    exact ⟨Real.log B,fun p hp => (h p hp).mono fun m hm => (generator_le_power_iff _ hB p m).mp hm⟩

#print axioms riemannHypothesis_iff_ordinaryTriple_power
#print axioms poleBalanced_ordinary_error
#print axioms eventually_balanced_jetRadius_bound
#print axioms riemannHypothesis_iff_ordinaryTriple_generator
#print axioms pole_correction_subquadratic
#print axioms riemannHypothesis_iff_ordinaryTriple_jetRadius

end GaloisForLFunctions.CountingHolography.Sections
