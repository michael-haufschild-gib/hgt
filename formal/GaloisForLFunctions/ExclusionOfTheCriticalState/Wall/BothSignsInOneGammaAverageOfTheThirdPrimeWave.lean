import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositeExcursionsOfTheThirdConfinedPrimeWave
import GaloisForLFunctions.RHTower.LandauAbscissaRigidity

/-!
# Simultaneous opposite mass in one gamma average

The Poisson generating function of the positive gamma moments is the
damped positive Laplace mass. A divergent positive Laplace mass forces
exponentially large gamma means. The summable signed means make both
signs exponentially large at the very same orders.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
open private neutral_ordinary_gamma_moments from
  GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositeExcursionsOfTheThirdConfinedPrimeWave

/-- The positive mass at a single gamma order. Negating the density
selects its negative mass. -/
def gammaSignMass (v : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ t in Ioi (0:ℝ), primeGammaWeight n t * max (v t) 0

private theorem weight_nonneg (n : ℕ) {t : ℝ} (ht : t ∈ Ioi (0:ℝ)) :
    0 ≤ primeGammaWeight n t := by
  have : 0 ≤ t := (show 0 < t from ht).le
  unfold primeGammaWeight
  positivity

private theorem sign_integrable {v : ℝ → ℝ} (hm : Measurable v) {n : ℕ}
    (hi : IntegrableOn (fun t => primeGammaWeight n t * v t) (Ioi 0)) :
    IntegrableOn (fun t => primeGammaWeight n t * max (v t) 0) (Ioi 0) := by
  apply hi.norm.mono' (by unfold primeGammaWeight; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hn := weight_nonneg n ht
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg hn,abs_of_nonneg (le_max_right _ _)]
  exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) hn

private theorem mass_nonneg (v : ℝ → ℝ) (n : ℕ) : 0 ≤ gammaSignMass v n :=
  integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
    mul_nonneg (weight_nonneg n ht) (le_max_right _ _))

private theorem laplace_of_gamma_series {v : ℝ → ℝ} (hm : Measurable v)
    (hi : ∀ n, IntegrableOn (fun t => primeGammaWeight n t * v t) (Ioi 0))
    {r : ℝ} (hr : 0 ≤ r) (hs : Summable fun n => r^n * gammaSignMass v n) :
    IntegrableOn (fun t => Real.exp (-(1-r)*t)*max (v t) 0) (Ioi 0) := by
  let g := fun n t => r^n * (primeGammaWeight n t * max (v t) 0)
  have hg (n : ℕ) : IntegrableOn (g n) (Ioi 0) := (sign_integrable hm (hi n)).const_mul _
  have integralG (n : ℕ) : (∫ t in Ioi (0:ℝ), g n t) = r^n * gammaSignMass v n := integral_const_mul ..
  let P := fun N t => ∑ n ∈ Finset.range N, g n t
  have hP (N : ℕ) : IntegrableOn (P N) (Ioi 0) := integrable_finsetSum _ fun n _ => hg n
  have hsum (t : ℝ) : HasSum (fun n => g n t) (Real.exp (-(1-r)*t)*max (v t) 0) := by
    have h := (GaloisForLFunctions.RHTower.summable_shift_terms 1 r t).hasSum
    rw [←GaloisForLFunctions.RHTower.exp_shift_tsum] at h
    exact (h.mul_right (max (v t) 0)).congr_fun fun n => by
      dsimp only [g,primeGammaWeight]; rw [neg_one_mul]; ring
  apply integrable_of_tendsto (Eventually.of_forall fun t => (hsum t).tendsto_sum_nat) (fun n => (hP n).1)
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n, r^n * gammaSignMass v n))
  apply liminf_le_of_frequently_le'
  apply Frequently.of_forall
  intro n
  rw [← ofReal_integral_norm_eq_lintegral_enorm (hP n)]
  apply ENNReal.ofReal_le_ofReal
  have eq := setIntegral_congr_fun (μ := volume) measurableSet_Ioi (fun t (ht : t ∈ Ioi (0:ℝ)) =>
    Real.norm_of_nonneg (show 0 ≤ P n t from Finset.sum_nonneg fun j _ =>
      mul_nonneg (pow_nonneg hr _) (mul_nonneg (weight_nonneg j ht) (le_max_right _ _))))
  rw [eq]
  change (∫ t in Ioi (0:ℝ), ∑ j ∈ Finset.range n, g j t) ≤ _
  rw [integral_finsetSum _ (fun j _ => hg j)]
  simp only [integralG]
  exact hs.sum_le_tsum _ fun j _ => mul_nonneg (pow_nonneg hr _) (mass_nonneg _ _)

private theorem paired_gamma_growth {v : ℝ → ℝ} (hm : Measurable v)
    (hi : ∀ n, IntegrableOn (fun t => primeGammaWeight n t*v t) (Ioi 0))
    (hs : Summable fun n => |∫ t in Ioi (0:ℝ), primeGammaWeight n t*v t|)
    {b : ℝ} (hb : 0 < b)
    (hpos : ¬IntegrableOn (fun t => Real.exp (-b*t)*max (v t) 0) (Ioi 0)) :
    ∃ d : ℝ, 1 < d ∧ ∀ M : ℝ, ∃ᶠ n : ℕ in atTop,
      M*d^n < min (gammaSignMass v n) (gammaSignMass (fun t => -v t) n) := by
  let b' := min b (1/2)
  let r := 1-b'
  have bp : 0 < b' := lt_min hb (by norm_num)
  have rp : 0 < r := sub_pos.mpr ((min_le_right b (1/2:ℝ)).trans_lt (by norm_num))
  have ru : r < 1 := sub_lt_self _ bp
  let d := (1+r)/(2*r)
  have dp : 1 < d := (lt_div_iff₀ (by positivity : 0 < 2*r)).mpr (by linarith only [ru])
  have rd : r*d < 1 := by dsimp only [d]; field_simp; linarith only [ru]
  have notSum : ¬Summable (fun n => r^n*gammaSignMass v n) := by
    intro sum
    apply hpos
    apply (laplace_of_gamma_series hm hi rp.le sum).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp := le_max_right (v t) 0
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hp)]
    apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr _) hp
    have he : 1-r=b' := by dsimp [r]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left ..)) (le_of_lt ht)
  let B := ∑' n, |∫ t in Ioi (0:ℝ), primeGammaWeight n t*v t|
  have B0 : 0 ≤ B := tsum_nonneg fun _ => abs_nonneg _
  have diff (n : ℕ) : gammaSignMass v n - gammaSignMass (fun t => -v t) n ≤ B := by
    have hin : IntegrableOn (fun t => primeGammaWeight n t*(-v t)) (Ioi 0) :=
      (hi n).neg.congr (.of_forall fun t => (mul_neg ..).symm)
    have h : gammaSignMass v n-gammaSignMass (fun t => -v t) n =
        ∫ t in Ioi (0:ℝ), primeGammaWeight n t*v t := by
      rw [gammaSignMass,gammaSignMass]
      refine (integral_sub (sign_integrable hm (hi n))
        (sign_integrable (v := fun t => -v t) hm.neg hin)).symm.trans ?_
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      show primeGammaWeight n t * max (v t) 0 - primeGammaWeight n t * max (-v t) 0 =
        primeGammaWeight n t * v t
      rw [←mul_sub]
      congr 1
      rcases le_total 0 (v t) with h | h
      · simp only [max_eq_left h,max_eq_right (neg_nonpos.mpr h),sub_zero]
      · simp only [max_eq_right h,max_eq_left (neg_nonneg.mpr h),zero_sub,neg_neg]
    exact h.le.trans ((le_abs_self _).trans (hs.le_tsum n fun _ _ => abs_nonneg _))
  refine ⟨d,dp,fun M => ?_⟩
  have many : ∃ᶠ n : ℕ in atTop, (|M|+B)*d^n < gammaSignMass v n := by
    by_contra no
    have he := not_frequently.mp no
    have geom := (summable_geometric_of_lt_one (mul_nonneg rp.le (zero_lt_one.trans dp).le) rd).mul_left (|M|+B)
    apply notSum
    apply Summable.of_norm_bounded_eventually geom
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [he] with n hn
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg rp.le _) (mass_nonneg _ _)),mul_pow]
    exact (mul_le_mul_of_nonneg_left (le_of_not_gt hn) (pow_nonneg rp.le _)).trans_eq (by ring)
  apply many.mono
  intro n hn
  have p0 := pow_nonneg (zero_lt_one.trans dp).le n
  have x := mul_le_mul_of_nonneg_right (le_abs_self M) p0
  have y : B ≤ B * d^n := le_mul_of_one_le_right B0 (one_le_pow₀ dp.le)
  exact lt_min (by linarith only [hn,x,y,B0]) (by linarith only [hn,x,y,diff n])

/-- Three actual rungs force positive and negative ordinary-prime mass to
exceed the same exponential target at the same gamma orders. The two
Laplace moments vanish for the same nonzero coefficient vector. -/
theorem IsCriticalLadder.exists_simultaneous_gamma_excursions {R : Fin 3 → ℝ} {Φ : Fin 3 → ℝ → ℝ}
    (hL : IsCriticalLadder 2 R Φ) :
    ∃ (c : Fin 3 → ℝ) (d : ℝ), c ≠ 0 ∧ 1 < d ∧
      let H := fun u => ∑ i, c i*Φ i u
      let v := fun t => (ordinaryPrimeWave H t).re
      negativeHalfLineLaplace (cx H) (-(1/2))=0 ∧ negativeHalfLineLaplace (cx H) 0=0 ∧
      ∀ M : ℝ, ∃ᶠ n : ℕ in atTop,
        M*d^n < min (gammaSignMass v n) (gammaSignMass (fun t => -v t) n) := by
  obtain ⟨c,b,hc,hb,ha,hz,hpos,_⟩ := hL.exists_double_neutral_opposite_prime_mass
  let H := fun u => ∑ i, c i*Φ i u
  have hd : CriticalHalfLineEnergyDomain H := (hL.bare_neg_of_nonzero hc).1
  have hm : Measurable (fun t => (ordinaryPrimeWave H t).re) := by
    apply Complex.continuous_re.measurable.comp
    apply Measurable.tsum
    intro q
    exact measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (hd.meas.comp (measurable_id.sub_const _)))
  obtain ⟨hi,hs⟩ := neutral_ordinary_gamma_moments hd ha hz
  obtain ⟨d,dp,h⟩ := paired_gamma_growth hm hi hs hb hpos
  exact ⟨c,d,hc,dp,ha,hz,h⟩

#print axioms IsCriticalLadder.exists_simultaneous_gamma_excursions
end GaloisForLFunctions.ExclusionOfTheCriticalState
