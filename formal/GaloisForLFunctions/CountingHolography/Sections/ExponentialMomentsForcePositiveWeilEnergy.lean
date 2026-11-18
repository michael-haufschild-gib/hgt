import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.WindowNaiveHeights
import GaloisForLFunctions.HTGeometry.IntervalL2Density
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# Exponential moments force positive Weil energy on fixed intervals

Polynomials in the multiplicative coordinate approximate every bounded-frequency
Fourier character on a compact log interval. A unit-mass sequence annihilating
more and more moments therefore loses all its low frequencies. Bounded Weil
energy would keep its mass in a bounded frequency band.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory Finset Set Zeta23 _root_.RHTower
open ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis

/-- Exponential moments with nonnegative integer exponents below k. -/
def vanishingExpMoments (k : ℕ) (f : ℝ → ℝ) : Prop :=
  ∀ j < k, ∫ u : ℝ, f u * (Real.exp u)^j = 0

private theorem integral_polynomial_zero {k : ℕ} {f : ℝ → ℝ} (hc : Continuous f)
    (hk : HasCompactSupport f) (hm : vanishingExpMoments k f) (p : Polynomial ℝ)
    (hp : p.natDegree < k) : ∫ u : ℝ, f u * p.eval (Real.exp u) = 0 := by
  have hi (j : ℕ) : Integrable fun u => p.coeff j * (f u*(Real.exp u)^j) :=
    ((hc.mul (Real.continuous_exp.pow j)).integrable_of_hasCompactSupport hk.mul_right).const_mul _
  simp_rw [Polynomial.eval_eq_sum_range' hp, Finset.mul_sum,
    show ∀ (u : ℝ) (j : ℕ), f u * (p.coeff j * (Real.exp u)^j) =
      p.coeff j * (f u*(Real.exp u)^j) by intros; ring]
  rw [integral_finsetSum _ fun j _ => hi j]
  exact Finset.sum_eq_zero fun j hj => by rw [integral_const_mul, hm j (Finset.mem_range.mp hj),mul_zero]

private theorem polynomial_pair_zero {k : ℕ} {f : ℝ → ℝ} (hc : Continuous f) (hk : HasCompactSupport f)
    (hm : vanishingExpMoments k f) (p q : Polynomial ℝ) (hp : p.natDegree < k) (hq : q.natDegree < k) :
    ∫ u : ℝ, cx f u * (Complex.ofReal (p.eval (Real.exp u)) + Complex.I*Complex.ofReal (q.eval (Real.exp u))) = 0 := by
  let P (p : Polynomial ℝ) (u : ℝ) := f u * p.eval (Real.exp u)
  have hi (v : Polynomial ℝ) : Integrable (P v) :=
    (hc.mul (v.continuous.comp Real.continuous_exp)).integrable_of_hasCompactSupport hk.mul_right
  have hz (v : Polynomial ℝ) (hv : v.natDegree < k) : (∫ u : ℝ, (P v u : ℂ)) = 0 := by
    rw [integral_complex_ofReal, show (∫ u : ℝ, P v u) = 0 from integral_polynomial_zero hc hk hm v hv,
      Complex.ofReal_zero]
  have he (u : ℝ) : cx f u * (Complex.ofReal (p.eval (Real.exp u)) + Complex.I*Complex.ofReal (q.eval (Real.exp u))) =
      (P p u : ℂ) + Complex.I*(P q u : ℂ) := by
    simp only [cx,P,Complex.ofReal_mul]; ring
  simp_rw [he]
  have hiC (v : Polynomial ℝ) : Integrable (fun u => (P v u : ℂ)) := (hi v).ofReal
  calc _ = (∫ u : ℝ, (P p u : ℂ)) + ∫ u : ℝ, Complex.I * (P q u : ℂ) :=
          integral_add (hiC p) ((hiC q).const_mul Complex.I)
       _ = 0 := by rw [integral_const_mul, hz p hp, hz q hq, mul_zero, zero_add]

/-- Vanishing exponential moments on a fixed window suppress each fixed real frequency. -/
private theorem fourier_tendsto_zero {A C : ℝ} (hC : 0 < C) (U : ℕ → ℝ → ℝ)
    (hc : ∀ n, Continuous (U n)) (hk : ∀ n, HasCompactSupport (U n))
    (hs : ∀ n u, u ∉ Set.Icc (-A) 0 → U n u = 0)
    (hL : ∀ n, (∫ u, ‖U n u‖) ≤ C) (hm : ∀ n, vanishingExpMoments n (U n)) (r : ℝ) :
    Tendsto (fun n => paperFT (cx (U n)) r) atTop (𝓝 0) := by
  let K (u : ℝ) := Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))
  have hK : Continuous K := by dsimp [K]; fun_prop
  let z (v : ℝ) := max (Real.exp (-A)) v
  have hz : Continuous z := continuous_const.max continuous_id
  have hzp v : 0 < z v := (Real.exp_pos _).trans_le (le_max_left _ _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ := ε/(2*C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p,q,hpq⟩ := HTGeometry.exists_complexPolynomial_near 1
    (hK.comp (hz.log fun v => (hzp v).ne')) hδ
  let P (u : ℝ) := Complex.ofReal (p.eval (Real.exp u)) + Complex.I*Complex.ofReal (q.eval (Real.exp u))
  have hP : Continuous P := by dsimp [P]; fun_prop
  refine ⟨max (p.natDegree+1) (q.natDegree+1),fun n hn => ?_⟩
  have hzero : (∫ u : ℝ, cx (U n) u * P u) = 0 := polynomial_pair_zero (hc n) (hk n) (hm n) p q
    (lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans hn))
    (lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right _ _).trans hn))
  have hint (v : ℝ → ℂ) (hv : Continuous v) : Integrable fun u => cx (U n) u * v u :=
    ((Complex.continuous_ofReal.comp (hc n)).mul hv).integrable_of_hasCompactSupport
      (cx_hasCompactSupport (hk n)).mul_right
  have he : paperFT (cx (U n)) r = ∫ u : ℝ, cx (U n) u * (K u-P u) := by
    simp_rw [mul_sub]
    rw [integral_sub (hint K hK) (hint P hP),hzero,sub_zero]
    rfl
  rw [dist_zero_right,he]
  have hd (u : ℝ) : ‖cx (U n) u * (K u-P u)‖ ≤ ‖U n u‖*δ := by
    by_cases hu : u ∈ Set.Icc (-A) 0
    · have hx : Real.exp u ∈ Set.Icc (-1:ℝ) 1 :=
        ⟨by linarith only [Real.exp_pos u],Real.exp_le_one_iff.mpr hu.2⟩
      have hap := hpq _ hx
      change ‖K (Real.log (max (Real.exp (-A)) (Real.exp u))) - P u‖ < δ at hap
      rw [max_eq_right (Real.exp_le_exp.mpr hu.1),Real.log_exp] at hap
      simpa only [norm_mul,cx,Complex.norm_real] using
        mul_le_mul_of_nonneg_left hap.le (norm_nonneg (U n u))
    · simp [cx,hs n u hu]
  refine (norm_integral_le_of_norm_le (((hc n).integrable_of_hasCompactSupport (hk n)).norm.mul_const δ)
    (Eventually.of_forall hd)).trans_lt ?_
  rw [integral_mul_const]
  calc _ ≤ C*δ := mul_le_mul_of_nonneg_right (hL n) hδ.le
       _ = ε/2 := by dsimp [δ]; field_simp [hC.ne']
       _ < ε := half_lt_self hε

private theorem low_mass_tendsto_zero {U : ℕ → ℝ → ℝ} (hU : ∀ n, Integrable (U n))
    {C : ℝ} (hC : ∀ n, (∫ u, ‖U n u‖) ≤ C)
    (ht : ∀ r : ℝ, Tendsto (fun n => paperFT (cx (U n)) r) atTop (𝓝 0)) (T : ℝ) :
    Tendsto (fun n => lowFourierMass (U n) T) atTop (𝓝 0) := by
  let S := (highFrequencies T)ᶜ
  have hvol : volume S ≠ ⊤ :=
    ((measure_mono (compl_highFrequencies_subset T)).trans_lt isCompact_Icc.measure_lt_top).ne
  have h : Tendsto (fun n => ∫ r in S, ‖paperFT (cx (U n)) r‖^2) atTop
      (𝓝 (∫ _r : ℝ in S, (0:ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C^2)
    · exact Eventually.of_forall fun n => ((continuous_paperFT_cx (hU n)).norm.pow 2).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_paperFT_le _ r).trans (hC n)) 2
    · exact integrableOn_const hvol
    · exact Eventually.of_forall fun r => by simpa using (ht r).norm.pow 2
  simpa only [lowFourierMass,S,integral_zero,mul_zero] using h.const_mul (1/(2*Real.pi))

/-- On a fixed log interval the normalized Weil form exceeds any prescribed level
once sufficiently many multiplicative moments vanish. -/
theorem unit_weil_energy_of_vanishing_moments {A : ℝ} (hA : 0 < A) (E : ℝ) :
    ∃ k : ℕ, ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, u ∉ Set.Icc (-A) 0 → f u = 0) →
      (∫ u, f u^2) = 1 → vanishingExpMoments k f → E < weilQuad f := by
  by_contra! hn
  choose U hU hs hmass hm hbad using hn
  have hk (n : ℕ) : HasCompactSupport (U n) := HasCompactSupport.intro isCompact_Icc (hs n)
  have hL (n : ℕ) : (∫ u, ‖U n u‖) ≤ 2*A+1 := by
    have h := sq_integral_norm_le_of_abs_support (Complex.continuous_ofReal.comp (hU n).continuous) hA
      (f := cx (U n)) (fun u hu => by
        have hnot : u ∉ Set.Icc (-A) 0 := fun h => hu.not_ge (abs_le.mpr ⟨h.1,h.2.trans hA.le⟩)
        simp [cx,hs n u hnot])
    simp only [cx,Complex.norm_real,Real.norm_eq_abs,sq_abs,hmass n,mul_one] at h
    simp only [Real.norm_eq_abs]
    nlinarith only [h,sq_nonneg ((∫ u, |U n u|)-1),hA]
  have hw (n : ℕ) : (∫ y, U n y ^ 2 * Real.exp (-(8*y))) ≤ Real.exp (8*A) := by
    have ht : Integrable fun y => U n y^2 := ((hU n).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (K := Set.Icc (-A) 0) isCompact_Icc (fun y hy => by simp [hs n y hy]))
    calc _ ≤ ∫ y, U n y^2 * Real.exp (8*A) := by
           apply integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
             (ht.mul_const _) (Eventually.of_forall fun y => ?_)
           by_cases hy : y ∈ Set.Icc (-A) 0
           · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hy.1])) (sq_nonneg _)
           · simp [hs n y hy]
         _ = _ := by rw [integral_mul_const,hmass n,one_mul]
  have hh := high_tails_of_bounded_weilQuad hU hk (fun n => (hmass n).le) hw
    (l := atTop) (Eventually.of_forall fun n y hy => hs n y (fun h => by linarith only [h.2,hy]))
    (Eventually.of_forall hbad)
  obtain ⟨T,_,hhT⟩ := hh (1/3) (by norm_num)
  have hft := fourier_tendsto_zero (A := A) (C := 2*A+1) (by positivity) U (fun n => (hU n).continuous)
    hk hs hL hm
  have hl := low_mass_tendsto_zero (fun n => (hU n).continuous.integrable_of_hasCompactSupport (hk n)) hL hft T
  obtain ⟨n,hn1,hn2⟩ := (hhT.and (hl.eventually_lt_const (by norm_num : (0:ℝ) < 1/3))).exists
  have he := lowFourierMass_add_highFourierMass (hU n) (hk n) T
  rw [hmass n] at he
  linarith only [hn1,hn2,he]

#print axioms unit_weil_energy_of_vanishing_moments

end GaloisForLFunctions.CountingHolography.Sections
