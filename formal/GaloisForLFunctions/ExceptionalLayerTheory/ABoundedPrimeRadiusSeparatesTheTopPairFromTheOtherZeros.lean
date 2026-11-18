import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimeIncrementAcrossAnExtremalWave
import GaloisForLFunctions.RHTower.FiniteOffLineConverse
import GaloisForLFunctions.HTGeometry.OstrowskiRelationCarrier

/-!
# The gap below the extremal pair of a bounded prime radius

Taking a square root of the signed increment estimate and telescoping gives a
power bound for the Chebyshev error after subtracting the extremal zeros.
The finite-wave Landau converse bounds the real part of each remaining zero.
-/

noncomputable section
open Complex Filter Topology RHTower Set
open GaloisForLFunctions.ZeroConfigurationGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Removing the extremal logarithmic trace is exactly the finite-wave
subtraction for the set of all multiplicity copies on the extremal line. -/
theorem mul_exp_boundaryTrace_eq_neg_top_wave {β : ℝ}
    (hf : {q : XiZeroCopy | (q.1 : ℂ).re = β}.Finite) (t : ℝ) :
    Real.exp (β*t)*primeErrorBoundaryTrace β t = -(offLineWave hf.toFinset (Real.exp t)).re := by
  classical
  let f := fun q : XiZeroCopy => if (q.1 : ℂ).re = β then
    Complex.exp (((q.1 : ℂ)-(β:ℂ))*(t:ℂ))/(q.1:ℂ) else 0
  have hc : (Real.exp (β*t) : ℂ) * (∑' q, f q) = offLineWave hf.toFinset (Real.exp t) := by
    rw [tsum_eq_sum (s := hf.toFinset) (fun q hq => if_neg (fun h => hq (hf.mem_toFinset.mpr h))),
      Finset.mul_sum,offLineWave]
    apply Finset.sum_congr rfl
    intro q hq
    rw [show f q = _ from if_pos (hf.mem_toFinset.mp hq),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast Real.exp_ne_zero t),
      ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp, ← mul_div_assoc,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  change Real.exp (β*t)*(-(∑' q, f q).re) = _
  rw [mul_neg,← hc,Complex.ofReal_mul_re]

/-- Telescoping a one-step estimate for a function bounded below on compact
intervals preserves its positive exponential rate. -/
theorem exp_lower_of_step {E : ℝ → ℝ} {h a K : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hK : 0 ≤ K) (hlocal : ∀ b, ∃ B : ℝ, ∀ t, 0 ≤ t → t ≤ b → -B ≤ E t)
    (hinc : ∀ᶠ t : ℝ in atTop, |E (t+h)-E t| ≤ K*Real.exp (a*t)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, 0 ≤ t → -(B*Real.exp (a*t)) ≤ E t := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hinc
  let T := max 0 T₀
  have hT (t : ℝ) (ht : T ≤ t) := hT₀ t ((le_max_right _ _).trans ht)
  obtain ⟨L,hL⟩ := hlocal (T+h)
  let C := K/(Real.exp (a*h)-1)
  have hden : 0 < Real.exp (a*h)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ha hh))
  have hC : 0 ≤ C := div_nonneg hK hden.le
  have hCK : C*(Real.exp (a*h)-1)=K := div_mul_cancel₀ _ hden.ne'
  let G := fun t => E t+C*Real.exp (a*t)
  have hs (t : ℝ) (ht : T ≤ t) : G t ≤ G (t+h) := by
    have he := congrArg (fun b : ℝ => b*Real.exp (a*t)) hCK
    dsimp only [G]
    rw [mul_add,Real.exp_add]
    linarith only [(abs_le.mp (hT t ht)).1,he]
  have hbase (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ T+h) : -|L| ≤ G t := by
    exact (neg_le_neg (le_abs_self _)).trans ((hL t ht0 ht).trans
      (le_add_of_nonneg_right (mul_nonneg hC (Real.exp_pos _).le)))
  have hi (n : ℕ) : ∀ t : ℝ, 0 ≤ t → t ≤ T+n*h → -|L| ≤ G t := by
    induction n with
    | zero =>
      intro t ht0 ht
      have h0 : t ≤ T := by simpa only [Nat.cast_zero,zero_mul,add_zero] using ht
      exact hbase t ht0 (h0.trans (le_add_of_nonneg_right hh.le))
    | succ n ih =>
      intro t hpos ht
      by_cases ht' : t ≤ T+h
      · exact hbase t hpos ht'
      have ht0 : T ≤ t-h := by linarith only [lt_of_not_ge ht']
      rw [Nat.cast_succ,add_mul,one_mul] at ht
      have h := (ih (t-h) ((le_max_left _ _).trans ht0) (by linarith only [ht])).trans (hs (t-h) ht0)
      rwa [sub_add_cancel] at h
  refine ⟨C+|L|,add_nonneg hC (abs_nonneg _),fun t ht => ?_⟩
  obtain ⟨n,hn⟩ := exists_nat_ge ((t-T)/h)
  have h := hi n t ht (by linarith only [(div_le_iff₀ hh).mp hn])
  have hmul := mul_le_mul_of_nonneg_left (Real.one_le_exp (mul_nonneg ha.le ht)) (abs_nonneg L)
  dsimp only [G] at h
  linarith only [h,hmul]

private def subtractedTheta (β t : ℝ) :=
  thetaLogError t-Real.exp (β*t)*primeErrorBoundaryTrace β t

private theorem subtractedTheta_step (β h t : ℝ) :
    subtractedTheta β (t+h)-subtractedTheta β t = Real.exp (β*t)*
      (normalizedPrimeIncrement β h t - boundaryStep β h (primeErrorBoundaryTrace β) t) := by
  simp only [subtractedTheta,normalizedPrimeIncrement,logStepIncrement,boundaryStep,mul_add,Real.exp_add]
  field_simp <;> ring

private theorem subtractedTheta_locally_bddBelow {β : ℝ} (hβ : 1/2 < β) (b : ℝ) :
    ∃ B : ℝ, ∀ t, 0 ≤ t → t ≤ b → -B ≤ subtractedTheta β t := by
  let B := ∑' q, ‖primeErrorBoundaryAmplitude β q‖
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨Real.exp b+Real.exp (β*b)*B,fun t _ ht => ?_⟩
  have htrace : primeErrorBoundaryTrace β t ≤ B := by
    rw [primeErrorBoundaryTrace_eq_re_expSeries]
    exact (Complex.re_le_norm _).trans (GaloisForLFunctions.HTGeometry.norm_expSeriesCarrier_le
      (summable_primeErrorBoundaryAmplitude hβ) t)
  have hf := (mul_le_mul_of_nonneg_left htrace (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht (by linarith only [hβ]))) hB)
  dsimp only [subtractedTheta,thetaLogError]
  linarith only [hf,Real.exp_le_exp.mpr ht,Chebyshev.theta_nonneg (Real.exp t)]

/-- Every nonextremal zero lies at or left of the midpoint between the
critical line and the extremal line of a bounded trial radius. -/
theorem re_le_midpoint_of_bounded_radius_of_not_top {γ : ℝ} {m : ℕ}
    (hΘ : 1/2 < zetaZeroAbscissa) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy zetaZeroAbscissa γ m))
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ zetaZeroAbscissa) :
    (q.1 : ℂ).re ≤ (zetaZeroAbscissa+1/2)/2 := by
  classical
  by_contra! hlarge
  let β := zetaZeroAbscissa
  let r := (q.1 : ℂ).re
  have hrβ : r < β := lt_of_le_of_ne (re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q)) hq
  let σ := ((1/2)+(2*r-β))/2
  let a := (β+σ)/2
  have hσ : 1/2 < σ := by dsimp only [σ,r,β]; linarith only [hlarge]
  have hσβ : σ < β := by dsimp only [σ]; linarith only [hrβ,hΘ]
  have hhalf : 1/2 < a := by dsimp only [a]; linarith only [hσ,hΘ]
  have har : a < r := by dsimp only [a,σ,r,β]; linarith only [hlarge]
  have ha1 : a < 1 := har.trans (xiZeroCopy_re_lt_one q)
  let h := quarterPeriodStep γ
  let D := boundaryStep β h (primeErrorBoundaryTrace β)
  let U := normalizedPrimeIncrement β h
  obtain ⟨M,hM⟩ := signed_prime_increment_on_extremal_wave hσ hσβ hγ hm hb
  have hinc : ∀ᶠ t in atTop, |subtractedTheta β (t+h)-subtractedTheta β t| ≤
      Real.sqrt |M| * Real.exp (a*t) := by
    filter_upwards [hM] with t ht
    have hs : (U t-D t)^2 ≤ |M| * Real.exp (-(β-σ)*t) :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (ht.trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
    have H : |U t-D t| ≤ Real.sqrt |M| * Real.exp (-(β-σ)*t/2) := by
      apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
      rw [sq_abs,mul_pow,Real.sq_sqrt (abs_nonneg _),sq,← Real.exp_add]
      rw [show -(β-σ)*t/2 + -(β-σ)*t/2 = -(β-σ)*t by ring]
      exact hs
    rw [subtractedTheta_step,abs_mul,abs_of_pos (Real.exp_pos _)]
    refine (mul_le_mul_of_nonneg_left H (Real.exp_pos _).le).trans_eq ?_
    rw [mul_left_comm,← Real.exp_add]
    congr 2
    dsimp only [a]
    ring
  obtain ⟨C,hC,hbound⟩ := exp_lower_of_step (quarterPeriodStep_pos hγ)
    (by linarith only [hhalf] : 0 < a) (Real.sqrt_nonneg _) (subtractedTheta_locally_bddBelow hΘ) hinc
  let hf := finite_top_of_bounded_thetaRadial hΘ hγ hb
  let S := hf.toFinset
  have hp (x : ℝ) (hx : 2 ≤ x) : -(C*x^(1/2+(a-1/2))) ≤
      Chebyshev.psi x - x + (offLineWave S x).re := by
    have hpos : 0 < x := by linarith only [hx]
    have he := hbound (Real.log x) (Real.log_nonneg (by linarith only [hx]))
    dsimp only [subtractedTheta,thetaLogError] at he
    rw [mul_exp_boundaryTrace_eq_neg_top_wave hf, Real.exp_log hpos,sub_neg_eq_add] at he
    rw [show (1/2:ℝ)+(a-1/2)=a by ring,Real.rpow_def_of_pos hpos,mul_comm (Real.log x) a]
    exact he.trans (add_le_add (sub_le_sub_right (Chebyshev.theta_le_psi _) _) le_rfl)
  have hnot : lagPole q ∉ offLinePoles S := by
    rintro (⟨p,hp,he⟩ | ⟨p,hp,he⟩)
    all_goals
      have hpβ := hf.mem_toFinset.mp hp
      have hz := congrArg Complex.re he
      simp only [lagPole,Complex.conj_re,Complex.sub_re,Complex.ofReal_re] at hz
      apply hq
      linarith only [hz,hpβ]
  have H := re_le_half_add_of_chebyshevPsi_sub_add_offLineWave_ge S hC (sub_pos.mpr hhalf)
    (by linarith only [ha1]) (by norm_num : (1:ℝ)<2) hp q hnot
  linarith only [har,H]

#print axioms re_le_midpoint_of_bounded_radius_of_not_top

end GaloisForLFunctions.ExceptionalLayerTheory
