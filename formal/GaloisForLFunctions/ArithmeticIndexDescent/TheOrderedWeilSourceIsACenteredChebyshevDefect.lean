import GaloisForLFunctions.ArithmeticIndexDescent.TheOrderedGammaTailRetainsPolarCancellation
import GaloisForLFunctions.ArithmeticIncidencePositivity.LagChebyshevAbelSummation

/-!
# The ordered Weil source as a centered Chebyshev discrepancy

The first Gamma exponential cancels one ordered polar product. The other polar
product and the actual prime comb are compared before taking absolute values.
Lag Abel summation then identifies their difference with the Chebyshev error
against the derivative of the same mixed profile. Its zero boundary value
allows arbitrary constant centering. The remaining Gamma charge is localized
by exponential distance from the cut.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open RHTower RHTower.WeilSpectral Zeta23

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticIncidencePositivity

private theorem sectionCorr_as_crossCorr (f g : ℝ → ℝ) (h : ℝ) :
    sectionCorr f g h = RHTower.crossCorr g f h := by
  unfold sectionCorr RHTower.crossCorr
  rw [← integral_add_right_eq_self (μ := volume) (fun u => g u * f (u - h)) h]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [add_sub_cancel_right, mul_comm]

/-- The oriented correlation is zero on nonpositive lags across an ordered cut. -/
theorem sectionCorr_ordered_nonpos {f g : ℝ → ℝ} {b h : ℝ}
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) (hh : h ≤ 0) :
    sectionCorr f g h = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with u
  change f u * g (u + h) = 0
  by_cases hu : b ≤ u
  · rw [hleft u hu, zero_mul]
  · rw [hright (u + h) (by linarith only [le_of_not_ge hu, hh]), mul_zero]

/-- Differentiation of the literal mixed correlation keeps its orientation. -/
theorem hasDerivAt_sectionCorr {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (t : ℝ) :
    HasDerivAt (sectionCorr f g) (sectionCorr f (deriv g) t) t := by
  have hd : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := hgc.deriv.exists_bound_of_continuous hd
  have hbound : Integrable (fun x => ‖f x‖ * M) :=
    (hf.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport hfc.norm.mul_right
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (u : ℝ) (x : ℝ) => f x * g (x + u))
    (F' := fun (u : ℝ) (x : ℝ) => f x * deriv g (x + u))
    (x₀ := t) (bound := fun x => ‖f x‖ * M) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun u =>
      (hf.continuous.mul (hg.continuous.comp
        (continuous_id.add continuous_const))).aestronglyMeasurable)
    ((hf.continuous.mul (hg.continuous.comp
      (continuous_id.add continuous_const))).integrable_of_hasCompactSupport hfc.mul_right)
    ((hf.continuous.mul (hd.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x u _ => by
      rw [Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM (x + u)) (norm_nonneg _)) hbound
    (Filter.Eventually.of_forall fun x u _ =>
      (HasDerivAt.comp_const_add x u ((hg.differentiable one_ne_zero (x + u)).hasDerivAt)).const_mul
        (f x))
  exact h.2

theorem contDiff_one_sectionCorr {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ContDiff ℝ 1 (sectionCorr f g) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_sectionCorr hf hfc hg hgc t).differentiableAt, ?_⟩
  have hd : deriv (sectionCorr f g) = RHTower.crossCorr (deriv g) f := by
    funext t
    rw [(hasDerivAt_sectionCorr hf hfc hg hgc t).deriv, sectionCorr_as_crossCorr]
  rw [hd]
  exact CHMDStage6.continuous_crossCorr_of_hasCompactSupport
    (hg.continuous_deriv le_rfl) hf.continuous hfc

/-- The actual ordered prime atom reads this half-weighted mixed correlation. -/
def orderedSourceLagWeight (f g : ℝ → ℝ) (h : ℝ) : ℝ :=
  Real.exp (-h / 2) * sectionCorr f g h

theorem contDiff_one_orderedSourceLagWeight {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ContDiff ℝ 1 (orderedSourceLagWeight f g) :=
  ((contDiff_id.neg.div_const 2).exp).mul (contDiff_one_sectionCorr hf hfc hg hgc)

/-- The lag derivative retains both the correlation derivative and the half-density term. -/
theorem deriv_orderedSourceLagWeight {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (h : ℝ) :
    deriv (orderedSourceLagWeight f g) h =
      Real.exp (-h / 2) * (sectionCorr f (deriv g) h - sectionCorr f g h / 2) := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s / 2))
      (Real.exp (-h / 2) * (-1 / 2)) h := by
    simpa only [id_eq] using ((hasDerivAt_id h).neg.div_const 2).exp
  exact ((he.mul (hasDerivAt_sectionCorr hf hfc hg hgc h)).congr_deriv (by ring)).deriv

theorem orderedSourceLagWeight_nonpos {f g : ℝ → ℝ} {b h : ℝ}
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) (hh : h ≤ 0) :
    orderedSourceLagWeight f g h = 0 := by
  rw [orderedSourceLagWeight, sectionCorr_ordered_nonpos hleft hright hh, mul_zero]

/-- Compact profiles supply their own finite Abel horizon. -/
theorem exists_orderedSourceLag_horizon {f g : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ∃ S : ℝ, 0 < S ∧ ∀ h, S ≤ h → orderedSourceLagWeight f g h = 0 := by
  have hc : HasCompactSupport (sectionCorr f g) := by
    have he : sectionCorr f g = RHTower.crossCorr g f := funext (sectionCorr_as_crossCorr f g)
    rw [he]
    exact CHMDStage6.hasCompactSupport_crossCorr_of_hasCompactSupport hgc hfc
  have hq : HasCompactSupport (orderedSourceLagWeight f g) := hc.mul_left
  obtain ⟨r, hr⟩ := ArithmeticIncidencePositivity.exists_radius_of_hasCompactSupport hq
  refine ⟨max r 0 + 1, by positivity, ?_⟩
  intro h hh
  exact hr h (lt_of_lt_of_le (by linarith only [le_max_left r 0, hh]) (le_abs_self h))

/-- The original prime source has one oriented term, with no extra factor of two. -/
theorem primePart_eq_orderedLag_sum {f g : ℝ → ℝ} {b S : ℝ} {N : ℕ}
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0)
    (hvan : ∀ h, S ≤ h → orderedSourceLagWeight f g h = 0)
    (hN : Real.exp S ≤ N) :
    (primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (cx f) (cx g))).re =
      ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n *
        orderedSourceLagWeight f g (Real.log n) := by
  have hterm (n : ℕ) :
      (sourcePrimeCoefficient n : ℂ) *
        (EF.weilTest (cx f) (cx g) (Real.log n) +
          EF.weilTest (cx f) (cx g) (-Real.log n)) =
        ((ArithmeticFunction.vonMangoldt n * orderedSourceLagWeight f g (Real.log n) : ℝ) : ℂ) := by
    by_cases hn : 2 ≤ n
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      rw [sourcePrimeCoefficient, if_pos hn, weilTest_eq_sectionCorr, weilTest_eq_sectionCorr,
        neg_neg, sectionCorr_ordered_nonpos hleft hright (neg_nonpos.mpr hlog),
        Complex.ofReal_zero, zero_add, orderedSourceLagWeight, exp_neg_half_log hnpos]
      push_cast
      ring
    · have hnle : n ≤ 1 := by omega
      interval_cases n <;> simp [sourcePrimeCoefficient]
  have hc : primePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (cx f) (cx g)) =
      ∑ n ∈ Finset.range (N + 1),
        ((ArithmeticFunction.vonMangoldt n * orderedSourceLagWeight f g (Real.log n) : ℝ) : ℂ) := by
    calc
      _ = ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n * orderedSourceLagWeight f g (Real.log n) : ℝ) : ℂ) :=
        tsum_congr hterm
      _ = _ := by
        apply tsum_eq_sum
        intro n hn
        have hlarge : N < n := by
          have hn' : N + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
          omega
        have hpos : 0 < (n : ℝ) := (Real.exp_pos S).trans_le (hN.trans (by exact_mod_cast hlarge.le))
        have hlog : S ≤ Real.log n := (Real.le_log_iff_exp_le hpos).mpr
          (hN.trans (by exact_mod_cast hlarge.le))
        rw [hvan _ hlog, mul_zero, Complex.ofReal_zero]
  rw [hc]
  simp only [map_sum, Complex.ofReal_re]

/-- The surviving polar product is the continuum density for the same ordered lag weight. -/
theorem integral_exp_orderedSourceLagWeight {f g : ℝ → ℝ} {b : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hleft : ∀ u, b ≤ u → f u = 0) (hright : ∀ u, u ≤ b → g u = 0) :
    (∫ h in Ioi (0 : ℝ), Real.exp h * orderedSourceLagWeight f g h) = poleB f * poleA g := by
  have he : (∫ h in Ioi (0 : ℝ), Real.exp h * orderedSourceLagWeight f g h) =
      ∫ h, Real.exp ((1 / 2 : ℝ) * h) * RHTower.crossCorr g f h := by
    calc
      _ = ∫ h in Ioi (0 : ℝ), Real.exp ((1 / 2 : ℝ) * h) * RHTower.crossCorr g f h := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro h _
        dsimp only [orderedSourceLagWeight]
        rw [← mul_assoc, ← Real.exp_add, sectionCorr_as_crossCorr]
        congr 2
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by
        rw [← sectionCorr_as_crossCorr,
          sectionCorr_ordered_nonpos hleft hright (le_of_not_gt hh), mul_zero]
  rw [he, CHMDStage6.integral_exp_mul_crossCorr_eq hg hgc hf hfc (1 / 2)]
  have hA : (∫ t : ℝ, g t * Real.exp ((1 / 2 : ℝ) * t)) = poleA g := by
    unfold poleA
    apply integral_congr_ae
    filter_upwards [] with t
    congr 2
    ring
  have hB : (∫ t : ℝ, f t * Real.exp (-(1 / 2 : ℝ) * t)) = poleB f := by
    unfold poleB
    apply integral_congr_ae
    filter_upwards [] with t
    congr 2
    ring
  rw [hA, hB, mul_comm]

private theorem onePole_sub_prime_eq_centered_error {q : ℝ → ℝ} {S : ℝ} {N : ℕ}
    (hq : ContDiff ℝ 1 q) (hS : 0 < S) (hvan : ∀ h, S ≤ h → q h = 0)
    (hzero : q 0 = 0) (hN : Real.exp S ≤ N) (c : ℝ) :
    (∫ h in Ioi (0 : ℝ), Real.exp h * q h) -
      (∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n * q (Real.log n)) =
      -∫ h in Ioi (0 : ℝ), (chebyshevError h - c) * deriv q h := by
  have hiq := integrableOn_Ioi_of_vanishing hq.continuous hS (fun h hh => hvan h hh.le)
  have hie : IntegrableOn (fun h => Real.exp h * q h) (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_of_vanishing (Real.continuous_exp.mul hq.continuous) hS
      (fun h hh => by rw [hvan h hh.le, mul_zero])
  have hsplit : (∫ h in Ioi (0 : ℝ), (Real.exp h + 1) * q h) =
      (∫ h in Ioi (0 : ℝ), Real.exp h * q h) + ∫ h in Ioi (0 : ℝ), q h := by
    rw [← integral_add hie hiq]
    exact setIntegral_congr_fun measurableSet_Ioi fun h _ => by dsimp only; ring
  have habel := sum_vonMangoldt_sub_polar_eq_chebyshevError hq hS hvan hN
  rw [hsplit, hzero] at habel
  have hderiv : (∫ h in Ioi (0 : ℝ), deriv q h) = 0 := by
    rw [integral_Ioi_eq_intervalIntegral (hq.continuous_deriv le_rfl) hS
      (fun h hh => deriv_eq_zero_of_vanishing hvan hh),
      intervalIntegral.integral_deriv_eq_sub
        (fun h _ => hq.differentiable one_ne_zero h)
        ((hq.continuous_deriv le_rfl).intervalIntegrable _ _), hvan S le_rfl, hzero, sub_self]
  have hcenter : (∫ h in Ioi (0 : ℝ), (chebyshevError h - c) * deriv q h) =
      ∫ h in Ioi (0 : ℝ), chebyshevError h * deriv q h := by
    calc
      _ = (∫ h in Ioi (0 : ℝ), chebyshevError h * deriv q h) -
          ∫ h in Ioi (0 : ℝ), c * deriv q h := by
        rw [← integral_sub (integrableOn_Ioi_chebyshevError_mul_deriv hq hS hvan hN)
          ((integrableOn_Ioi_deriv hq hS hvan).const_mul c)]
        exact setIntegral_congr_fun measurableSet_Ioi fun h _ => by dsimp only; ring
      _ = _ := by rw [integral_const_mul, hderiv, mul_zero, sub_zero]
  rw [hcenter]
  linarith only [habel]

/-- Exact arithmetic cancellation on the original mixed Weil form, with arbitrary centering. -/
theorem realWeilForm_ordered_eq_centered_chebyshev (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) (c : ℝ) :
    realWeilForm f g =
      -(∫ h in Ioi (0 : ℝ), (chebyshevError h - c) *
        deriv (orderedSourceLagWeight f.1 g.1) h) - orderedGammaTail f.1 g.1 := by
  obtain ⟨S, hS, hvan⟩ := exists_orderedSourceLag_horizon f.2.2 g.2.2
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp S)
  have hf1 : ContDiff ℝ 1 f.1 := f.2.1.of_le (by norm_num)
  have hg1 : ContDiff ℝ 1 g.1 := g.2.1.of_le (by norm_num)
  have hq := contDiff_one_orderedSourceLagWeight hf1 f.2.2 hg1 g.2.2
  have hq0 := orderedSourceLagWeight_nonpos hleft hright (le_refl (0 : ℝ))
  have ha := onePole_sub_prime_eq_centered_error hq hS hvan hq0 hN.le c
  rw [integral_exp_orderedSourceLagWeight f.2.1.continuous f.2.2
    g.2.1.continuous g.2.2 hleft hright,
    ← primePart_eq_orderedLag_sum hleft hright hvan hN.le] at ha
  rw [realWeilForm_ordered_pole_cancellation f g hleft hright, ha]

/-- Absolute source payment uses centered Chebyshev variation and localized Gamma mass. -/
theorem abs_realWeilForm_ordered_le_centered_chebyshev (f g : realTests) {b : ℝ}
    (hleft : ∀ u, b ≤ u → f.1 u = 0) (hright : ∀ u, u ≤ b → g.1 u = 0) (c : ℝ) :
    |realWeilForm f g| ≤
      (∫ h in Ioi (0 : ℝ), |chebyshevError h - c| *
        |deriv (orderedSourceLagWeight f.1 g.1) h|) +
          Real.pi * (leftBoundaryMass b f.1 + rightBoundaryMass b g.1) := by
  rw [realWeilForm_ordered_eq_centered_chebyshev f g hleft hright c]
  have hi : |∫ h in Ioi (0 : ℝ), (chebyshevError h - c) *
      deriv (orderedSourceLagWeight f.1 g.1) h| ≤
      ∫ h in Ioi (0 : ℝ), |chebyshevError h - c| *
        |deriv (orderedSourceLagWeight f.1 g.1) h| := by
    refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
    exact setIntegral_congr_fun measurableSet_Ioi fun h _ => abs_mul _ _
  have ht := abs_orderedGammaTail_le_boundaryMass f.2.1.continuous f.2.2
    g.2.1.continuous g.2.2 hleft hright
  have htri := abs_sub (-(∫ h in Ioi (0 : ℝ), (chebyshevError h - c) *
    deriv (orderedSourceLagWeight f.1 g.1) h)) (orderedGammaTail f.1 g.1)
  rw [abs_neg] at htri
  linarith only [hi, ht, htri]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.primePart_eq_orderedLag_sum
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.realWeilForm_ordered_eq_centered_chebyshev
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.abs_realWeilForm_ordered_le_centered_chebyshev
