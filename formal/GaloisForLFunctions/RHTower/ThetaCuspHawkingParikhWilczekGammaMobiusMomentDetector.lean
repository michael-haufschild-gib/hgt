import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaReciprocalMoments
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaGroundBoundary

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section

def pwGammaMobiusReciprocalMomentAtom (z : ℂ) (k n : ℕ) : ℂ :=
  pwGammaMobiusReciprocalCoefficient z n *
    (pwGammaReciprocalMoment ((n:ℝ)+1) k : ℂ)

def pwGammaMobiusReciprocalMoment (z : ℂ) (k : ℕ) : ℂ :=
  ∑' n, pwGammaMobiusReciprocalMomentAtom z k n

def pwGammaMobiusReciprocalNormalizedMomentAtom (z : ℂ) (k n : ℕ) : ℂ :=
  pwGammaMobiusReciprocalCoefficient z n *
    (pwGammaReciprocalMomentRatio ((n:ℝ)+1) k : ℂ)

def pwGammaMobiusReciprocalNormalizedMoment (z : ℂ) (k : ℕ) : ℂ :=
  ∑' n, pwGammaMobiusReciprocalNormalizedMomentAtom z k n

private theorem pwGammaMomentSeries_inv_square_summable :
    Summable (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^2) := by
  have ht := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Nat.succ_injective
  simpa only [Function.comp_def, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using ht

theorem pwGammaMobiusReciprocalMomentAtom_norm_bound {N : ℕ} {z : ℂ}
    (hz : ‖z‖≤(N:ℝ)) (k n : ℕ) :
    ‖pwGammaMobiusReciprocalMomentAtom z k n‖ ≤
      (2^(N+1)*((k+3+N).factorial:ℝ)*(N.factorial:ℝ))*(1/((n:ℝ)+1)^2) := by
  have ha : (0:ℝ)<(n:ℝ)+1 := by positivity
  have ha1 : (1:ℝ)≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  rw [pwGammaMobiusReciprocalMomentAtom, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pwGammaReciprocalMoment_pos k ha).le]
  calc
    _ ≤ ((n+2:ℕ):ℝ)^(N+1)*
        ((((k+3+N).factorial:ℝ)/((n:ℝ)+1)^(k+3+N))*(N.factorial:ℝ)) := by
      apply mul_le_mul (pwGammaMobiusReciprocalCoefficient_norm_le hz n)
        (pwGammaReciprocalMoment_pow_bound k N ha) (pwGammaReciprocalMoment_pos k ha).le
      positivity
    _ ≤ (2*((n:ℝ)+1))^(N+1)*
        ((((k+3+N).factorial:ℝ)/((n:ℝ)+1)^(k+3+N))*(N.factorial:ℝ)) := by
      gcongr
      push_cast
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    _ = (2^(N+1)*((k+3+N).factorial:ℝ)*(N.factorial:ℝ))*(1/((n:ℝ)+1)^(k+2)) := by
      rw [mul_pow, show k+3+N=(N+1)+(k+2) by omega, pow_add]
      field_simp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ ha1 (by omega)

theorem pwGammaMobiusReciprocalMomentAtom_summable (z : ℂ) (k : ℕ) :
    Summable (pwGammaMobiusReciprocalMomentAtom z k) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  exact (pwGammaMomentSeries_inv_square_summable.mul_left
    (2^(N+1)*((k+3+N).factorial:ℝ)*(N.factorial:ℝ))).of_norm_bounded
      (pwGammaMobiusReciprocalMomentAtom_norm_bound hN k)

theorem pwGammaMobiusReciprocalNormalizedMomentAtom_eq (z : ℂ) (k n : ℕ) :
    pwGammaMobiusReciprocalNormalizedMomentAtom z k n =
      pwGammaMobiusReciprocalMomentAtom z k n / ((k+1).factorial:ℂ) := by
  unfold pwGammaMobiusReciprocalNormalizedMomentAtom pwGammaMobiusReciprocalMomentAtom
    pwGammaReciprocalMomentRatio
  rw [Complex.ofReal_div, Complex.ofReal_natCast, mul_div_assoc]

theorem pwGammaMobiusReciprocalNormalizedMoment_eq (z : ℂ) (k : ℕ) :
    pwGammaMobiusReciprocalNormalizedMoment z k =
      pwGammaMobiusReciprocalMoment z k / ((k+1).factorial:ℂ) := by
  unfold pwGammaMobiusReciprocalNormalizedMoment pwGammaMobiusReciprocalMoment
  simp only [pwGammaMobiusReciprocalNormalizedMomentAtom_eq, tsum_div_const]

theorem pwGammaMobiusReciprocalNormalizedMomentAtom_summable (z : ℂ) (k : ℕ) :
    Summable (pwGammaMobiusReciprocalNormalizedMomentAtom z k) := by
  change Summable (fun n => pwGammaMobiusReciprocalNormalizedMomentAtom z k n)
  simp_rw [pwGammaMobiusReciprocalNormalizedMomentAtom_eq]
  exact (pwGammaMobiusReciprocalMomentAtom_summable z k).div_const ((k+1).factorial:ℂ)

/-- One fixed majorant controls the complete signed family at every later order. -/
theorem pwGammaMobiusReciprocalNormalizedMomentAtom_norm_bound {N : ℕ} {z : ℂ}
    (hz : ‖z‖≤(N:ℝ)) {k : ℕ} (hk : N+1≤k) (n : ℕ) :
    ‖pwGammaMobiusReciprocalNormalizedMomentAtom z k n‖ ≤
      2^(N+1)*(1/((n:ℝ)+1)^2) := by
  have ha : (0:ℝ)<(n:ℝ)+1 := by positivity
  have ha1 : (1:ℝ)≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hI := (pwGammaReciprocalMomentRatio_pos k ha).le
  rw [pwGammaMobiusReciprocalNormalizedMomentAtom, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hI]
  calc
    _ ≤ ((n+2:ℕ):ℝ)^(N+1)*(1/((n:ℝ)+1)^(k+2)) := by
      apply mul_le_mul (pwGammaMobiusReciprocalCoefficient_norm_le hz n)
        (pwGammaReciprocalMomentRatio_upper k ha) hI
      positivity
    _ ≤ (2*((n:ℝ)+1))^(N+1)*(1/((n:ℝ)+1)^(N+3)) := by
      apply mul_le_mul
      · gcongr
        push_cast
        linarith [Nat.cast_nonneg (α:=ℝ) n]
      · apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ ha1 (by omega)
      · positivity
      · positivity
    _ = _ := by
      rw [mul_pow, show N+3=(N+1)+2 by omega, pow_add]
      field_simp
      ring

theorem pwGammaMobiusReciprocalCoefficient_zero (z : ℂ) :
    pwGammaMobiusReciprocalCoefficient z 0 =
      -(Real.sqrt (2:ℝ):ℂ)*Complex.exp (-z*(Real.log (2:ℝ):ℂ)) := by
  simp [pwGammaMobiusReciprocalCoefficient, moebius_apply_prime Nat.prime_two]
  ring

theorem pwGammaMobiusReciprocalCoefficient_zero_ne (z : ℂ) :
    pwGammaMobiusReciprocalCoefficient z 0 ≠ 0 := by
  rw [pwGammaMobiusReciprocalCoefficient_zero]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  · exact Complex.exp_ne_zero _

theorem pwGammaMobiusReciprocalNormalizedMomentAtom_tendsto (z : ℂ) (n : ℕ) :
    Tendsto (fun k => pwGammaMobiusReciprocalNormalizedMomentAtom z k n) atTop
      (𝓝 (if n=0 then pwGammaMobiusReciprocalCoefficient z 0 else 0)) := by
  cases n with
  | zero =>
      have ht := ((Complex.continuous_ofReal.tendsto _).comp
        pwGammaReciprocalMomentRatio_one_tendsto).const_mul (pwGammaMobiusReciprocalCoefficient z 0)
      simpa only [pwGammaMobiusReciprocalNormalizedMomentAtom, Nat.cast_zero, zero_add,
        if_pos rfl, ite_true, Complex.ofReal_one, mul_one, Function.comp_def] using ht
  | succ n =>
      have ha : (1:ℝ)<((n+1:ℕ):ℝ)+1 := by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n]
      have ht := ((Complex.continuous_ofReal.tendsto _).comp
        (pwGammaReciprocalMomentRatio_tendsto_zero ha)).const_mul
          (pwGammaMobiusReciprocalCoefficient z (n+1))
      simpa only [pwGammaMobiusReciprocalNormalizedMomentAtom, Nat.succ_eq_add_one,
        Nat.add_one_ne_zero, if_false, Complex.ofReal_zero, mul_zero, Function.comp_def] using ht

/-- High-order moments of the complete signed series recover its nonzero first coefficient. -/
theorem pwGammaMobiusReciprocalNormalizedMoment_tendsto (z : ℂ) :
    Tendsto (pwGammaMobiusReciprocalNormalizedMoment z) atTop
      (𝓝 (pwGammaMobiusReciprocalCoefficient z 0)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ‖z‖
  have ht := tendsto_tsum_of_dominated_convergence
    (pwGammaMomentSeries_inv_square_summable.mul_left (2^(N+1)))
    (pwGammaMobiusReciprocalNormalizedMomentAtom_tendsto z)
    (show ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      ‖pwGammaMobiusReciprocalNormalizedMomentAtom z k n‖≤2^(N+1)*(1/((n:ℝ)+1)^2) from by
        filter_upwards [eventually_ge_atTop (N+1)] with k hk n
        exact pwGammaMobiusReciprocalNormalizedMomentAtom_norm_bound hN hk n)
  change Tendsto (fun k => ∑' n, pwGammaMobiusReciprocalNormalizedMomentAtom z k n) atTop _
  simpa using ht


/-- The original normalized source in reciprocal coordinates, with all signed coefficients. -/
theorem pwGammaMobiusTilt_reciprocal_tail_eq (z : ℂ) {x : ℝ} (hx : 0<x) :
    pwGammaMobiusTilt z (1/x)/pwGammaRaySource (1/x)-1 =
      ∑' n, pwGammaMobiusReciprocalCoefficient z n*(Real.exp (-((n:ℝ)+1)/x):ℂ) := by
  rw [pwGammaMobiusTilt_ground_tail_eq z (by positivity : (0:ℝ)<1/x)]
  apply tsum_congr
  intro n
  have he : ((n+2:ℕ):ℝ)-1=(n:ℝ)+1 := by push_cast; ring
  have hr : pwGammaMobiusGlobalAtom z (n+2) 1/pwGammaRaySource 1 =
      pwGammaMobiusReciprocalCoefficient z n*(Real.exp (-((n:ℝ)+1)):ℂ) := by
    rw [pwGammaMobiusGlobalAtom, mul_div_assoc,
      pwGammaNormalizedRayMode_source_ratio (by omega : 0<n+2) zero_lt_one]
    unfold pwGammaNormalizedRayMode pwGammaMobiusReciprocalCoefficient
    rw [he, mul_one, Complex.ofReal_mul]
    ring
  rw [hr, he, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

def pwGammaMobiusReciprocalMomentIntegrand (z : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (-x)/x^(k+3):ℝ):ℂ)*
    (pwGammaMobiusTilt z (1/x)/pwGammaRaySource (1/x)-1)

theorem pwGammaMobiusReciprocalMomentIntegrand_eq_tsum (z : ℂ) (k : ℕ)
    {x : ℝ} (hx : 0<x) :
    pwGammaMobiusReciprocalMomentIntegrand z k x =
      ∑' n, pwGammaMobiusReciprocalCoefficient z n*
        (pwGammaReciprocalMomentKernel ((n:ℝ)+1) k x:ℂ) := by
  rw [pwGammaMobiusReciprocalMomentIntegrand, pwGammaMobiusTilt_reciprocal_tail_eq z hx,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold pwGammaReciprocalMomentKernel
  rw [sub_eq_add_neg, Real.exp_add, neg_div]
  push_cast
  ring

theorem pwGammaMobiusReciprocalMomentAtom_integrable (z : ℂ) (k n : ℕ) :
    IntegrableOn (fun x : ℝ => pwGammaMobiusReciprocalCoefficient z n*
      (pwGammaReciprocalMomentKernel ((n:ℝ)+1) k x:ℂ)) (Ioi 0) :=
  ((pwGammaReciprocalMomentKernel_integrable k (by positivity : (0:ℝ)<(n:ℝ)+1)).ofReal).const_mul _

theorem pwGammaMobiusReciprocalMomentAtom_norm_integral (z : ℂ) (k n : ℕ) :
    (∫ x in Ioi (0:ℝ), ‖pwGammaMobiusReciprocalCoefficient z n*
      (pwGammaReciprocalMomentKernel ((n:ℝ)+1) k x:ℂ)‖) =
      ‖pwGammaMobiusReciprocalMomentAtom z k n‖ := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (pwGammaReciprocalMomentKernel_pos ((n:ℝ)+1) k hx).le])]
  rw [integral_const_mul, pwGammaMobiusReciprocalMomentAtom, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pwGammaReciprocalMoment_pos k (by positivity : (0:ℝ)<(n:ℝ)+1)).le]
  rfl

theorem pwGammaMobiusReciprocalMomentIntegrand_integrable (z : ℂ) (k : ℕ) :
    IntegrableOn (pwGammaMobiusReciprocalMomentIntegrand z k) (Ioi 0) := by
  have hsum : Summable (fun n : ℕ => ∫ x in Ioi (0:ℝ),
      ‖pwGammaMobiusReciprocalCoefficient z n*
        (pwGammaReciprocalMomentKernel ((n:ℝ)+1) k x:ℂ)‖) := by
    simp only [pwGammaMobiusReciprocalMomentAtom_norm_integral]
    exact (pwGammaMobiusReciprocalMomentAtom_summable z k).norm
  have hi := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusReciprocalMomentAtom_integrable z k) hsum
  exact IntegrableOn.congr_fun hi
    (fun x hx => (pwGammaMobiusReciprocalMomentIntegrand_eq_tsum z k hx).symm)
    measurableSet_Ioi

/-- Actual source integration equals the entire admitted signed moment series. -/
theorem pwGammaMobiusReciprocalMoment_integral_eq (z : ℂ) (k : ℕ) :
    (∫ x in Ioi (0:ℝ), pwGammaMobiusReciprocalMomentIntegrand z k x) =
      pwGammaMobiusReciprocalMoment z k := by
  have hsum : Summable (fun n : ℕ => ∫ x in Ioi (0:ℝ),
      ‖pwGammaMobiusReciprocalCoefficient z n*
        (pwGammaReciprocalMomentKernel ((n:ℝ)+1) k x:ℂ)‖) := by
    simp only [pwGammaMobiusReciprocalMomentAtom_norm_integral]
    exact (pwGammaMobiusReciprocalMomentAtom_summable z k).norm
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => pwGammaMobiusReciprocalMomentIntegrand_eq_tsum z k hx)]
  rw [← integral_tsum_of_summable_integral_norm
    (pwGammaMobiusReciprocalMomentAtom_integrable z k) hsum]
  simp only [integral_const_mul, integral_complex_ofReal]
  rfl

theorem pwGammaMobiusReciprocalMoment_eventually_ne_zero (z : ℂ) :
    ∀ᶠ k : ℕ in atTop, pwGammaMobiusReciprocalMoment z k ≠ 0 := by
  have ht := (pwGammaMobiusReciprocalNormalizedMoment_tendsto z).eventually
    (eventually_ne_nhds (pwGammaMobiusReciprocalCoefficient_zero_ne z))
  filter_upwards [ht] with k hk
  intro hz
  apply hk
  rw [pwGammaMobiusReciprocalNormalizedMoment_eq, hz, zero_div]

/-- Every sufficiently high endpoint moment of the actual source is nonzero, for each z. -/
theorem pwGammaMobiusReciprocalMoment_integral_eventually_ne_zero (z : ℂ) :
    ∀ᶠ k : ℕ in atTop,
      (∫ x in Ioi (0:ℝ), pwGammaMobiusReciprocalMomentIntegrand z k x) ≠ 0 := by
  simpa only [pwGammaMobiusReciprocalMoment_integral_eq] using
    pwGammaMobiusReciprocalMoment_eventually_ne_zero z

end
end RHTower
