import GaloisForLFunctions.RHTower.ThetaTailCauchyAsymptotic
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomAllOrderApproximation
import GaloisForLFunctions.RHTower.LogarithmicCauchyRankBoundary

/-!
# The positive first correction to the theta tail Cauchy limit

The complete source score has constant offset 9/2. L'Hopital then identifies
the first omitted kernel term as a positive squared-Cauchy kernel with coefficient 7.
After Cayley congruence its formal coefficient form is an exact weighted difference
energy. That form is positive and grows quadratically on the adverse alternating
vector, so it is outside every uniform ordinary-energy bound.

The source limit fixes the nodes before translation. No interchange with growing
rank, lower bound for the full remainder, or RH conclusion is asserted.
-/

open Filter Topology Set
noncomputable section
namespace RHTower.ThetaTailFirstCorrection
open ThetaTailCauchy

private theorem scale_eq_morse (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 x = thetaCuspMorseScale 1 x := by
  unfold thetaCuspSingleAtomReflectionScale thetaCuspMorseScale
  rw [show (2 : ℝ)*x = x+x by ring, Real.exp_add]
  norm_num
  ring

private theorem first_score_eq {x : ℝ} (hx : 0 < x) :
    deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x / thetaCuspSourceTerm x 1 +
      2*thetaCuspSingleAtomReflectionScale 1 x =
      9/2+3/(thetaCuspSingleAtomReflectionScale 1 x-3/2) := by
  rw [(hasDerivAt_thetaCuspSourceTerm_eq_bornWittenScore (by norm_num : 0 < 1) hx).deriv,
    mul_div_cancel_right₀ _ (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne',
    scale_eq_morse]
  have hq := thetaCuspMorseScale_pi_le (n := 1) (by norm_num) hx.le
  have hp := Real.pi_gt_three
  have hn : thetaCuspMorseScale 1 x-3/2 ≠ 0 := by linarith
  unfold thetaCuspBornWittenSuperpotential
  rw [thetaCuspBornWittenWeight_eq]
  unfold thetaCuspMorseSuperpotential
  have hn' : 2*thetaCuspMorseScale 1 x-3 ≠ 0 := by linarith
  field_simp [hn, hn']
  ring

private theorem first_score_limit :
    Tendsto (fun x : ℝ => deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x /
      thetaCuspSourceTerm x 1 + 2*thetaCuspSingleAtomReflectionScale 1 x)
      atTop (𝓝 (9/2 : ℝ)) := by
  have hq : Tendsto (fun x : ℝ => thetaCuspSingleAtomReflectionScale 1 x-3/2)
      atTop atTop := by
    simpa only [sub_eq_add_neg, add_comm] using
      tendsto_atTop_add_const_left atTop (-(3/2 : ℝ)) thetaCuspC5FarTail_scale_tendsto_atTop
  have h := ((tendsto_inv_atTop_zero.comp hq).const_mul 3).const_add (9/2)
  apply (show Tendsto _ atTop (𝓝 (9/2 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [div_eq_mul_inv] using (first_score_eq hx).symm

/-- The literal complete source retains the first-atom prefactor in its logarithmic score. -/
theorem source_score_offset_limit :
    Tendsto (fun x : ℝ => deriv thetaCuspFullSource x / thetaCuspFullSource x +
      2*thetaCuspSingleAtomReflectionScale 1 x) atTop (𝓝 (9/2 : ℝ)) := by
  let f : ℝ → ℝ := fun x => thetaCuspSourceTerm x 1
  let e0 : ℝ → ℝ := fun x => (thetaCuspFullSource x-f x)/f x
  let e1 : ℝ → ℝ := fun x => (deriv thetaCuspFullSource x-deriv f x)/f x
  have h0 : Tendsto e0 atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
      thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero 0 0
  have h1 : Tendsto e1 atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using
      thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero 0 1
  have hq0 : Tendsto (fun x => thetaCuspSingleAtomReflectionScale 1 x*e0 x) atTop (𝓝 0) := by
    simpa only [pow_one, iteratedDeriv_zero] using
      thetaCuspFullSource_derivative_relative_error_scaled_tendsto_zero 1 0
  have h := ((h1.add first_score_limit).add (hq0.const_mul 2)).div
    (h0.const_add 1) (by norm_num : (1 : ℝ)+0 ≠ 0)
  apply (show Tendsto _ atTop (𝓝 (9/2 : ℝ)) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hf : f x ≠ 0 := (thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num)).ne'
  have hphi := (HedenmalmThetaSource.thetaCuspFullSource_pos x).ne'
  dsimp [f] at hf
  have hd : 1+(thetaCuspFullSource x-thetaCuspSourceTerm x 1)/thetaCuspSourceTerm x 1 =
      thetaCuspFullSource x/thetaCuspSourceTerm x 1 := by field_simp; ring
  dsimp [e0, e1, f]
  rw [hd]
  field_simp [hf, hphi]
  ring

private theorem shift_atTop (x : ℝ) : Tendsto (fun r : ℝ => x+r) atTop atTop :=
  tendsto_atTop_add_const_left atTop x tendsto_id

private theorem exp_scale (x r : ℝ) :
    Real.exp (-2*r)*thetaCuspSingleAtomReflectionScale 1 (x+r) =
      Real.pi*Real.exp (2*x) := by
  unfold thetaCuspSingleAtomReflectionScale
  norm_num only [Nat.cast_one, one_pow, mul_one]
  rw [show 2*(x+r) = 2*x+2*r by ring, Real.exp_add]
  have he : Real.exp (-2*r)*Real.exp (2*r) = 1 := by
    rw [← Real.exp_add, show -2*r+2*r = 0 by ring, Real.exp_zero]
  linear_combination Real.pi*Real.exp (2*x)*he

/-- Exact constant in the paired logarithmic slope after removing its leading scale. -/
theorem baseSlope_error_div_exp_limit (x y : ℝ) :
    Tendsto (fun r : ℝ => (baseSlope x y r+2*pairScale x y)/Real.exp (-2*r))
      atTop (𝓝 (7 : ℝ)) := by
  have h := ((source_score_offset_limit.comp (shift_atTop x)).add
    (source_score_offset_limit.comp (shift_atTop y))).sub_const 2
  apply (show Tendsto _ atTop (𝓝 (7 : ℝ)) from by convert h using 1; norm_num).congr'
  apply Eventually.of_forall
  intro r
  simp only [Function.comp_apply]
  unfold baseSlope pairScale
  apply (eq_div_iff (Real.exp_ne_zero _)).mpr
  linear_combination 2*(exp_scale x r)+2*(exp_scale y r)

/-- The next literal-kernel term has a strictly positive squared-Cauchy coefficient. -/
theorem kernel_first_correction_limit (x y : ℝ) :
    Tendsto (fun r : ℝ =>
      (thetaTailFirstMomentKernel (x+r) (y+r)/baseNormalizer x y r -
        (2*r+x+y)/(2*pairScale x y))/(r*Real.exp (-2*r)))
      atTop (𝓝 (7/(2*pairScale x y^2))) := by
  let A := pairScale x y
  let E : ℝ → ℝ := fun r => Real.exp (-2*r)
  let P := pairProduct x y
  let D := baseNormalizer x y
  let T := baseSlope x y
  let U : ℝ → ℝ := fun r => normalizedSlope x y r-2*E r
  let B : ℝ → ℝ := fun r => (T r+2*A)/E r
  let L : ℝ → ℝ := fun r => (2*r+x+y)/(2*A)
  let N : ℝ → ℝ := fun r => thetaTailFirstMomentKernel (x+r) (y+r)-D r*L r
  let J : ℝ → ℝ := fun r => -(2*r+x+y)*P r-(P r*T r*L r+D r/A)
  let G : ℝ → ℝ := fun r => E r*normalizer x y r
  let Gjet : ℝ → ℝ := fun r => E r*(normalizerJet x y r-2*normalizer x y r)
  have hA : A ≠ 0 := (pairScale_pos x y).ne'
  have hP : ∀ r, P r ≠ 0 := fun r =>
    mul_ne_zero (HedenmalmThetaSource.thetaCuspFullSource_pos _).ne'
      (HedenmalmThetaSource.thetaCuspFullSource_pos _).ne'
  have hE : ∀ r, E r ≠ 0 := fun r => Real.exp_ne_zero _
  have hD : ∀ r, D r ≠ 0 := fun r => mul_ne_zero (hE r) (hP r)
  have hU : Tendsto U atTop (𝓝 (-2*A)) := by
    have h := (normalizedSlope_limit x y).sub
      ((PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)).const_mul 2)
    simpa only [mul_zero, sub_zero, U, A, pairScale, mul_assoc] using h
  have hU0 : -2*A ≠ 0 := mul_ne_zero (by norm_num) hA
  have hUne : ∀ᶠ r : ℝ in atTop, U r ≠ 0 :=
    hU.eventually (eventually_ne_nhds hU0)
  have hB : Tendsto B atTop (𝓝 (7 : ℝ)) := baseSlope_error_div_exp_limit x y
  have hL : ∀ r, HasDerivAt L (1/A) r := by
    intro r
    have h := (((hasDerivAt_id r).const_mul 2).add_const x |>.add_const y).div_const (2*A)
    refine h.congr_deriv ?_
    field_simp
  have hN : ∀ r, HasDerivAt N (J r) r := by
    intro r
    refine ((hasDerivAt_thetaTailFirstMomentKernel_commonShift r x y).sub
      ((baseNormalizer_hasDerivAt x y r).mul (hL r))).congr_deriv ?_
    dsimp [J, P, pairProduct, thetaTailCommonTranslationGenerator]
    ring
  have hG : ∀ r, HasDerivAt G (Gjet r) r := by
    intro r
    have he := ((hasDerivAt_id r).const_mul (-2)).exp
    refine (he.mul (normalizer_hasDerivAt x y r)).congr_deriv ?_
    dsimp [Gjet, E]
    ring
  have hGjet (r : ℝ) (hr : r ≠ 0) : Gjet r = r*E r*P r*U r := by
    dsimp [Gjet]
    rw [normalizerJet_eq hr]
    dsimp [P, pairProduct, U, normalizer]
    ring
  have hNjet (r : ℝ) : J r =
      -P r*((2*r+x+y)*(T r+2*A)+2*E r)/(2*A) := by
    dsimp [J, L, D, baseNormalizer]
    change -(2*r+x+y)*P r-(P r*T r*((2*r+x+y)/(2*A))+E r*P r/A) = _
    field_simp
    ring
  have hGne : ∀ᶠ r : ℝ in atTop, Gjet r ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hUne] with r hr hu
    rw [hGjet r hr.ne']
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hr.ne' (hE r)) (hP r)) hu
  have hN0 : Tendsto N atTop (𝓝 0) := by
    have h := (baseNormalizer_limit x y).mul (kernel_two_term_limit x y)
    apply (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using h).congr'
    apply Eventually.of_forall
    intro r
    dsimp [N, D, L, A]
    have hd : baseNormalizer x y r ≠ 0 := hD r
    field_simp [hd]
  have hG0 : Tendsto G atTop (𝓝 0) := by
    have h := (PositiveCoshEdge.exp_neg_rate (c := 2) (by norm_num)).mul
      (normalizer_limit x y)
    simpa only [mul_zero] using h
  have hratio : Tendsto (fun r => J r/Gjet r) atTop (𝓝 (7/(2*A^2))) := by
    have ha : Tendsto (fun r : ℝ => 2+(x+y)*r⁻¹) atTop (𝓝 (2 : ℝ)) := by
      simpa using (tendsto_inv_atTop_zero.const_mul (x+y)).const_add 2
    have hnum := ((ha.mul hB).add (tendsto_inv_atTop_zero.const_mul 2)).neg
    have h := hnum.div (hU.const_mul (2*A))
      (mul_ne_zero (mul_ne_zero (by norm_num) hA) hU0)
    have hl : -((2 : ℝ)*7+2*0)/(2*A*(-2*A)) = 7/(2*A^2) := by field_simp; ring
    rw [hl] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ), hUne] with r hr hu
    simp only [Pi.div_apply]
    rw [hGjet r hr.ne', hNjet]
    dsimp [B]
    field_simp [hA, hE r, hP r, hr.ne', hu]
    ring
  have hquot := HasDerivAt.lhopital_zero_atTop
    (Eventually.of_forall hN) (Eventually.of_forall hG) hGne hN0 hG0 hratio
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  dsimp [N, G, L, A]
  have hm : normalizer x y r = r*D r := by dsimp [normalizer, D, baseNormalizer, pairProduct]; ring
  rw [hm]
  change (thetaTailFirstMomentKernel (x+r) (y+r)-D r*((2*r+x+y)/(2*pairScale x y))) /
    (E r*(r*D r)) =
    (thetaTailFirstMomentKernel (x+r) (y+r)/D r-(2*r+x+y)/(2*pairScale x y))/(r*E r)
  field_simp [hD r, hE r, hr.ne']

namespace CauchySquare
open Finset PowerSeries
open scoped BigOperators

def geometric : PowerSeries (PowerSeries ℝ) :=
  PowerSeries.mk (fun i => PowerSeries.mk (fun j => if i=j then 1 else 0))
def diagonalSquare : PowerSeries (PowerSeries ℝ) :=
  PowerSeries.mk (fun i => PowerSeries.mk (fun j => if i=j then (i:ℝ)+1 else 0))
def repairSeries : PowerSeries (PowerSeries ℝ) :=
  (1-PowerSeries.X)*(1-PowerSeries.C PowerSeries.X)*diagonalSquare

theorem geometric_equation :
    (1-PowerSeries.C PowerSeries.X*PowerSeries.X)*geometric = 1 := by
  rw [sub_mul, one_mul, mul_assoc]
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  cases i <;> cases j <;>
    simp [geometric, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]

theorem diagonalSquare_equation :
    (1-PowerSeries.C PowerSeries.X*PowerSeries.X)*diagonalSquare = geometric := by
  rw [sub_mul, one_mul, mul_assoc]
  apply PowerSeries.ext
  intro i
  apply PowerSeries.ext
  intro j
  cases i with
  | zero => cases j <;> simp [diagonalSquare, geometric]
  | succ i =>
    cases j with
    | zero => simp [diagonalSquare, geometric, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]
    | succ j =>
      by_cases h : i=j <;> simp [diagonalSquare, geometric, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, h]

theorem repairSeries_equation :
    (1-PowerSeries.C PowerSeries.X*PowerSeries.X)^2*repairSeries =
      (1-PowerSeries.X)*(1-PowerSeries.C PowerSeries.X) := by
  calc
    _ = (1-PowerSeries.X)*(1-PowerSeries.C PowerSeries.X)*
      ((1-PowerSeries.C PowerSeries.X*PowerSeries.X)*
        ((1-PowerSeries.C PowerSeries.X*PowerSeries.X)*diagonalSquare)) := by
          unfold repairSeries
          ring
    _ = _ := by rw [diagonalSquare_equation, geometric_equation, mul_one]

def entry (i j : ℕ) : ℝ :=
  if i=j then 2*i+1 else if i=j+1 then -(i:ℝ) else if j=i+1 then -(j:ℝ) else 0

theorem repairSeries_coefficient (i j : ℕ) :
    PowerSeries.coeff j (PowerSeries.coeff i repairSeries) = entry i j := by
  have he : repairSeries = diagonalSquare-PowerSeries.C PowerSeries.X*diagonalSquare-
      PowerSeries.X*diagonalSquare+PowerSeries.C PowerSeries.X*(PowerSeries.X*diagonalSquare) := by
    unfold repairSeries
    ring
  rw [he]
  cases i with
  | zero =>
    cases j with
    | zero => simp [diagonalSquare, entry]
    | succ j =>
      cases j <;> simp [diagonalSquare, entry, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]
  | succ i =>
    cases j with
    | zero =>
      cases i <;> simp [diagonalSquare, entry, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul]
    | succ j =>
      by_cases h : i=j
      · subst j
        simp [diagonalSquare, entry, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_succ_X_mul]
        ring
      · by_cases h1 : i=j+1
        · subst i
          simp [diagonalSquare, entry, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_succ_X_mul]
          ring_nf
          simp
        · by_cases h2 : j=i+1
          · subst j
            simp [diagonalSquare, entry, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_succ_X_mul]
            ring_nf
            simp
          · simp [diagonalSquare, entry, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_succ_X_mul, h, h1, h2, Ne.symm h2]

def energy (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range n, ((i:ℝ)+1)*(a i-a (i+1))^2

def form (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ i ∈ range n, (2*(i:ℝ)+1)*a i^2)-
    2*∑ i ∈ range n, ((i:ℝ)+1)*a i*a (i+1)

theorem energy_nonneg (n : ℕ) (a : ℕ → ℝ) : 0 ≤ energy n a := by
  apply sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (sq_nonneg _)

/-- The exact boundary term in the discrete weighted-gradient representation. -/
theorem energy_eq_form_add_boundary (n : ℕ) (a : ℕ → ℝ) :
    energy n a = form n a+(n:ℝ)*a n^2 := by
  induction n with
  | zero => simp [energy, form]
  | succ n ih =>
    simp only [energy, form, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
    linear_combination ih

/-- Finite coefficient forms of the squared-Cauchy repair are positive. -/
theorem form_nonneg {n : ℕ} (a : ℕ → ℝ) (ha : a n=0) : 0 ≤ form n a := by
  have h := energy_nonneg n a
  rw [energy_eq_form_add_boundary, ha, zero_pow (by decide), mul_zero, add_zero] at h
  exact h

def alternatingCutoff (n i : ℕ) : ℝ := if i<n then (-1:ℝ)^i else 0

private theorem sum_indices (n : ℕ) :
    (∑ i ∈ range n, ((i:ℝ)+1)) = (n:ℝ)*((n:ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The positive correction grows quadratically on the model's adverse alternating direction. -/
theorem alternating_energy (n : ℕ) :
    energy n (alternatingCutoff n) = 2*(n:ℝ)^2-n := by
  cases n with
  | zero => simp [energy]
  | succ n =>
    rw [energy, Finset.sum_range_succ]
    have hsum : (∑ i ∈ range n,
        ((i:ℝ)+1)*(alternatingCutoff (n+1) i-alternatingCutoff (n+1) (i+1))^2) =
        4*∑ i ∈ range n, ((i:ℝ)+1) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hi' : i<n+1 := by have := mem_range.mp hi; omega
      have hi'' : i+1<n+1 := by have := mem_range.mp hi; omega
      simp only [alternatingCutoff, if_pos hi', if_pos hi'', pow_succ]
      have hs : ((-1:ℝ)^i)^2 = 1 := by rw [← pow_mul, mul_comm i 2, pow_mul]; norm_num
      nlinarith
    rw [hsum, sum_indices]
    simp only [alternatingCutoff, Nat.lt_succ_self, if_true, lt_self_iff_false, if_false, sub_zero]
    have hs : ((-1:ℝ)^n)^2 = 1 := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
    rw [hs]
    push_cast
    ring

theorem alternating_form (n : ℕ) :
    form n (alternatingCutoff n) = 2*(n:ℝ)^2-n := by
  have h := energy_eq_form_add_boundary n (alternatingCutoff n)
  norm_num [alternatingCutoff] at h
  rw [← h]
  exact alternating_energy n

/-- Exact coefficient-form reading: only the diagonal and adjacent coefficients survive. -/
theorem form_eq_coefficient_lags (n : ℕ) (a : ℕ → ℝ) :
    form n a =
      (∑ i ∈ range n, a i^2*PowerSeries.coeff i (PowerSeries.coeff i repairSeries))+
      2*∑ i ∈ range n, a i*a (i+1)*PowerSeries.coeff (i+1) (PowerSeries.coeff i repairSeries) := by
  rw [form, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [repairSeries_coefficient, repairSeries_coefficient]
  simp only [entry, if_neg (show i ≠ i+1 by omega),
    if_neg (show i ≠ i+1+1 by omega), Nat.cast_add, Nat.cast_one, if_true]
  ring

theorem alternating_l2 (n : ℕ) :
    LogCauchyRank.energy n (alternatingCutoff n) = n := by
  unfold LogCauchyRank.energy
  calc
    _ = ∑ i ∈ range n, (1 : ℝ) := by
      apply sum_congr rfl
      intro i hi
      simp only [alternatingCutoff, if_pos (mem_range.mp hi)]
      rw [← pow_mul, mul_comm i 2, pow_mul]
      norm_num
    _ = _ := by simp

/-- This positive repair is outside every uniform ordinary-energy bound. -/
theorem no_uniform_energy_bound :
    ¬ ∃ C : ℝ, ∀ n : ℕ, ∀ a : ℕ → ℝ, a n=0 →
      energy n a ≤ C*LogCauchyRank.energy n a := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (|C|+1)
  have hz : 0 < (n : ℝ) := by linarith [abs_nonneg C]
  have h := hC n (alternatingCutoff n) (by simp [alternatingCutoff])
  rw [alternating_energy, alternating_l2] at h
  nlinarith [le_abs_self C]

/-- Real Cayley congruence of the squared-Cauchy kernel. -/
theorem cayley_squared {u z w : ℝ} (hu : u ≠ 0) (hz : 1-z ≠ 0)
    (hw : 1-w ≠ 0) (hzw : 1-z*w ≠ 0) :
    (2*u/((1-z)*(1-w)))*(1/(LogCauchyRank.cayley u z+LogCauchyRank.cayley u w)^2) =
      (1/(2*u))*((1-z)*(1-w)/(1-z*w)^2) := by
  have hs : LogCauchyRank.cayley u z+LogCauchyRank.cayley u w =
      2*u*(1-z*w)/((1-z)*(1-w)) := by
    unfold LogCauchyRank.cayley
    field_simp [hz, hw]
    ring
  rw [hs]
  field_simp [hu, hz, hw, hzw]

end CauchySquare

end RHTower.ThetaTailFirstCorrection
