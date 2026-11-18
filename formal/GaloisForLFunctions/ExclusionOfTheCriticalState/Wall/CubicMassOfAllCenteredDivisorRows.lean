import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.MoebiusInversionOfTheIntegerQuadrature
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SubcriticalMeanSquareOfTheIntegerQuadrature
import GaloisForLFunctions.RHTower.ZetaFisherVariance
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Algebra.Order.Chebyshev

/-!
# Cubic mass of the centered divisors at every scale

Translation separates the cubic integral into a logarithmic Dirichlet
series and the cubic integral of the integer quadrature. A pointwise growth
bound and the weighted square estimates place the latter below tilt 1/6.
-/

noncomputable section
open MeasureTheory Set Filter Topology Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

private theorem integerReferenceWave_coarse_bound {Φ : ℝ → ℝ} {C σ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (hs : ∀ u, 0 ≤ u → Φ u=0)
    (hσ : 1/2 < σ) (hσ' : σ ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, |integerReferenceWave Φ t| ≤ B*Real.exp (σ*t) := by
  let c := fun n : ℕ => (n:ℝ)^(-(1/2+σ))
  have hsum : Summable c := Real.summable_nat_rpow.2 (by linarith only [hσ])
  have hpos (n : ℕ) : 0 ≤ c n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨C*(∑' n, c n),mul_nonneg hC (tsum_nonneg hpos),fun t => ?_⟩
  have hφ (u : ℝ) : |Φ u| ≤ C*Real.exp (σ*u) := by
    rcases le_total 0 u with hu | hu
    · rw [hs _ hu,abs_zero]; exact mul_nonneg hC (Real.exp_pos _).le
    · exact (hb _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hσ' hu)) hC)
  have ha := summable_continuousIntegerAtom hb t
  rw [← tsum_continuousIntegerAtom hb]
  calc _ ≤ ∑' n : ℕ, |continuousIntegerAtom Φ n t| := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm ha.norm
    _ ≤ ∑' n : ℕ, (C*Real.exp (σ*t))*c n := by
         apply ha.abs.tsum_le_tsum _ (hsum.mul_left _)
         intro n
         rcases Nat.eq_zero_or_pos n with rfl | hn
         · simp only [continuousIntegerAtom,Nat.cast_zero,Real.sqrt_zero,inv_zero,zero_mul,abs_zero]
           exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hpos 0)
         have hx : (0:ℝ) < n := by exact_mod_cast hn
         rw [continuousIntegerAtom,abs_mul,abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
         apply (mul_le_mul_of_nonneg_left (hφ _) (inv_nonneg.2 (Real.sqrt_nonneg _))).trans_eq
         rw [show (Real.sqrt n)⁻¹=Real.exp (-(Real.log n/2)) by rw [Real.exp_neg,Real.exp_half,Real.exp_log hx]]
         dsimp only [c]; rw [Real.rpow_def_of_pos hx]
         calc _ = C*Real.exp (-(Real.log n/2)+σ*(t-Real.log n)) := by rw [Real.exp_add]; ring
           _ = _ := by rw [show -(Real.log n/2)+σ*(t-Real.log n)=σ*t+Real.log n*(-(1/2+σ)) by ring,Real.exp_add]; ring
    _ = _ := by rw [tsum_mul_left]; ring

/-- Cubic integrability of the exponentially tilted integer discrepancy. -/
theorem criticalState_cubic_integer_error {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {b : ℝ} (hb0 : 0 ≤ b) (hb' : b < 1/6) :
    Integrable (fun t : ℝ => |tiltedIntegerError Φ b t|^3) := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let D := fun t : ℝ => integerReferenceWave Φ t-Real.exp (t/2)*A
  obtain ⟨σ,hσ,hσ'⟩ := exists_between (by linarith only [hb'] : 1/2 < 1-3*b)
  obtain ⟨B,hB,hN⟩ := integerReferenceWave_coarse_bound hC hb hs hσ (by linarith only [hσ',hb0])
  have hD (t : ℝ) : |D t| ≤ B*Real.exp (σ*t)+|A| *Real.exp ((1/2)*t) := by
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact add_le_add (hN t) (by rw [one_div_mul_eq_div,mul_comm])
  have hint (a : ℝ) (ha : 0 ≤ a) (ha' : 3*b+a < 1) :
      Integrable (fun t : ℝ => Real.exp ((3*b+a)*t)*D t^2) := by
    have h := criticalState_subcritical_integer_error hW ht hF hc he hC hb
      (show 0 ≤ (3*b+a)/2 by positivity) (by linarith only [ha'] : (3*b+a)/2 < 1/2)
    have h2 := (memLp_two_iff_integrable_sq_norm h.1).1 h
    apply h2.congr (Eventually.of_forall fun t => ?_)
    simp only [tiltedIntegerError,Real.norm_eq_abs,sq_abs,mul_pow,D,A]
    rw [pow_two (Real.exp _),← Real.exp_add]; congr 2; ring
  have hσ0 := (by norm_num : (0:ℝ) < 1/2).trans hσ
  have h1 := (hint σ hσ0.le (by linarith only [hσ'])).const_mul B
  have h2 := (hint (1/2) (by norm_num) (by linarith only [hb'])).const_mul |A|
  have hcN := continuous_integerReferenceWave hc hC hb
  have hm : Measurable (tiltedIntegerError Φ b) := by unfold tiltedIntegerError; fun_prop
  apply (h1.add h2).mono' (by fun_prop)
  refine Eventually.of_forall fun t => ?_
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  change |Real.exp (b*t)*D t|^3 ≤ B*(Real.exp ((3*b+σ)*t)*D t^2)+|A| *(Real.exp ((3*b+1/2)*t)*D t^2)
  have heq : (Real.exp (b*t))^3=Real.exp ((3*b)*t) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [abs_mul,abs_of_pos (Real.exp_pos _),mul_pow,heq,pow_succ |D t| 2,sq_abs]
  calc _ = (Real.exp ((3*b)*t)*D t^2)*|D t| := by ring
    _ ≤ (Real.exp ((3*b)*t)*D t^2)*(B*Real.exp (σ*t)+|A| *Real.exp ((1/2)*t)) :=
        mul_le_mul_of_nonneg_left (hD t) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    _ = _ := by rw [add_mul (3*b) σ,add_mul (3*b) (1/2),Real.exp_add,Real.exp_add]; ring

/-- The logarithmic, exponentially weighted cubic contribution of divisor d. -/
def divisorCubicMass (Φ : ℝ → ℝ) (A b : ℝ) (k d : ℕ) (t : ℝ) : ℝ :=
  (Real.exp (b*t)*(Real.log d)^k*|centredMultipleRow Φ A d t|)^3

private def cubicCost (b : ℝ) (k d : ℕ) : ℝ := (Real.log d)^(3*k)*(d:ℝ)^(-(3*(1/2-b)))

private theorem divisorCubicMass_translate (Φ : ℝ → ℝ) {b : ℝ} (hb : b < 1/6) (k d : ℕ) (t : ℝ) :
    divisorCubicMass Φ (∫ u, Real.exp (-u/2)*Φ u) b k d t =
      cubicCost b k d*|tiltedIntegerError Φ b (t-Real.log d)|^3 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [divisorCubicMass,cubicCost,centredMultipleRow,Real.zero_rpow (by linarith only [hb] : -(3*(1/2-b))≠0)]
  have hx : (0:ℝ) < d := by exact_mod_cast hd
  let L := Real.log (d:ℝ)
  have hroot : (Real.sqrt d)⁻¹=Real.exp (-(L/2)) := by rw [Real.exp_neg,Real.exp_half,Real.exp_log hx]
  have heq : Real.exp (b*t)*Real.exp (-(L/2))=Real.exp (-(1/2-b)*L)*Real.exp (b*(t-L)) := by
    rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  have hcoef : (Real.exp (-(1/2-b)*L))^3=(d:ℝ)^(-(3*(1/2-b))) := by
    rw [← Real.exp_nat_mul,Real.rpow_def_of_pos hx]; congr 1; dsimp only [L]; push_cast; ring
  let D := integerReferenceWave Φ (t-L)-Real.exp ((t-L)/2)*(∫ u, Real.exp (-u/2)*Φ u)
  change (Real.exp (b*t)*L^k*|(Real.sqrt d)⁻¹*D|)^3=
    (L^(3*k)*(d:ℝ)^(-(3*(1/2-b))))*|Real.exp (b*(t-L))*D|^3
  rw [hroot,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
  rw [show Real.exp (b*t)*L^k*(Real.exp (-(L/2))*|D|)=
      (L^k*(Real.exp (b*t)*Real.exp (-(L/2))))*|D| by ring,heq]
  rw [Nat.mul_comm 3 k,pow_mul,← hcoef]
  ring

/-- The total cubic mass over all divisors factors exactly, and is integrable
without a bound on the divisor size. -/
theorem criticalState_all_divisor_cubic_mass {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {b : ℝ} (hb0 : 0 ≤ b) (hb' : b < 1/6) (k : ℕ) :
    let A := ∫ u, Real.exp (-u/2)*Φ u
    let m := divisorCubicMass Φ A b k
    Integrable (fun t => ∑' d, m d t) ∧
      (∫ t, ∑' d, m d t) = (∑' d : ℕ, (Real.log d)^(3*k)*(d:ℝ)^(-(3*(1/2-b))))*
        (∫ t, |tiltedIntegerError Φ b t|^3) ∧
      ∀ᵐ t ∂volume, Summable (fun d => m d t) := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let m := divisorCubicMass Φ A b k
  let g := fun t : ℝ => |tiltedIntegerError Φ b t|^3
  let c := cubicCost b k
  have hg : Integrable g := criticalState_cubic_integer_error hW ht hF hc he hs hC hb hb0 hb'
  have hcost : Summable c := _root_.RHTower.summable_log_natCast_pow_mul_rpow_neg (3*k)
    (by linarith only [hb'] : 1 < 3*(1/2-b))
  have hc0 (d : ℕ) : 0 ≤ c d := mul_nonneg (pow_nonneg (Real.log_natCast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have htrans (d : ℕ) : m d = fun t => c d*g (t-Real.log d) := funext (divisorCubicMass_translate Φ hb' k d)
  have hm (d : ℕ) : Integrable (m d) := by rw [htrans]; exact (hg.comp_sub_right _).const_mul _
  have hp (d : ℕ) (t : ℝ) : 0 ≤ m d t := by rw [htrans]; exact mul_nonneg (hc0 _) (pow_nonneg (abs_nonneg _) _)
  have hint (d : ℕ) : (∫ t, m d t)=c d*∫ t, g t := by rw [htrans,integral_const_mul,integral_sub_right_eq_self]
  have hnorm (d : ℕ) : (∫ t, ‖m d t‖)=c d*∫ t, g t := by simp only [Real.norm_of_nonneg (hp d _),hint]
  have hsum : Summable fun d => ∫ t, ‖m d t‖ := by simp_rw [hnorm]; exact hcost.mul_right _
  have hL (d : ℕ) : eLpNorm (m d) 1 volume=ENNReal.ofReal (c d*∫ t, g t) := by
    rw [eLpNorm_one_eq_lintegral_enorm,← hnorm,ofReal_integral_norm_eq_lintegral_enorm (hm d)]
  have hfin : (∑' d, eLpNorm (m d) 1 volume) ≠ ⊤ := by
    simp_rw [hL]; rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun d => mul_nonneg (hc0 d) (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _)) (hcost.mul_right _)]
    exact ENNReal.ofReal_ne_top
  dsimp only
  refine ⟨HTGeometry.integrable_tsum_of_summable_integral_norm hm hsum,?_,?_⟩
  · rw [integral_tsum_of_summable_integral_norm hm hsum]
    simp_rw [hint]; exact tsum_mul_right
  · filter_upwards [MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
      (fun d => (hm d).1) hfin] with t ht
    exact ht.of_norm

/-- One integrable majorant for every selection of at most exp(κt) divisors,
with no restriction on their sizes or on how the selection depends on t. -/
theorem criticalState_sparse_divisor_envelope {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (k : ℕ) {r κ : ℝ} (hr : 0 ≤ r) (hκ : 0 ≤ κ) (hroom : r+2*κ < 1/2) :
    let A := ∫ u, Real.exp (-u/2)*Φ u
    ∃ B : ℝ → ℝ, Integrable B ∧ ∀ᵐ t ∂halfLineLaplaceMeasure, ∀ S : Finset ℕ,
      (S.card:ℝ) ≤ Real.exp (κ*t) →
      Real.exp (r*t)*(∑ d ∈ S, (Real.log d)^k*|centredMultipleRow Φ A d t|)^3 ≤ B t := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let b := (r+2*κ)/3
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hb' : b < 1/6 := by dsimp only [b]; linarith only [hroom]
  let m := divisorCubicMass Φ A b k
  obtain ⟨hi,_,hsum⟩ := criticalState_all_divisor_cubic_mass hW ht hF hc he hs hC hb hb0 hb' k
  refine ⟨fun t => ∑' d, m d t,hi,?_⟩
  filter_upwards [ae_restrict_of_ae (s := Ioi (0:ℝ)) hsum] with t hconv
  intro S hsize
  let f := fun d : ℕ => (Real.log d)^k*|centredMultipleRow Φ A d t|
  have hpos (d : ℕ) : 0 ≤ f d := mul_nonneg (pow_nonneg (Real.log_natCast_nonneg _) _) (abs_nonneg _)
  have heq (d : ℕ) : m d t=(Real.exp (b*t))^3*(f d)^3 := by
    dsimp only [m,divisorCubicMass,f]; rw [mul_assoc,mul_pow]
  have hweight : Real.exp (r*t)*(S.card:ℝ)^2 ≤ (Real.exp (b*t))^3 := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hsize 2) (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add]; congr 1; dsimp only [b]; push_cast; ring
  change Real.exp (r*t)*(∑ d ∈ S, f d)^3 ≤ ∑' d, m d t
  calc _ ≤ Real.exp (r*t)*((S.card:ℝ)^2*∑ d ∈ S, (f d)^3) :=
           mul_le_mul_of_nonneg_left (pow_sum_le_card_mul_sum_pow (s := S) (fun d _ => hpos d) 2) (Real.exp_pos _).le
    _ ≤ (Real.exp (b*t))^3*∑ d ∈ S, (f d)^3 := by
           rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hweight (sum_nonneg fun d _ => pow_nonneg (hpos d) _)
    _ = ∑ d ∈ S, m d t := by rw [Finset.mul_sum]; exact sum_congr rfl fun d _ => (heq d).symm
    _ ≤ _ := hconv.sum_le_tsum S fun d _ => by rw [heq]; exact mul_nonneg (pow_nonneg (Real.exp_pos _).le 3) (pow_nonneg (hpos d) 3)

/-- Under failure of RH one actual state obeys the simultaneous
all-divisor estimate at every admissible rate and logarithmic order. -/
theorem riemannHypothesis_or_sparse_divisor_envelope : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ (k : ℕ) (r κ : ℝ), 0 ≤ r → 0 ≤ κ → r+2*κ < 1/2 →
        let A := ∫ u, Real.exp (-u/2)*Φ u
        ∃ B : ℝ → ℝ, Integrable B ∧ ∀ᵐ t ∂halfLineLaplaceMeasure, ∀ S : Finset ℕ,
          (S.card:ℝ) ≤ Real.exp (κ*t) →
          Real.exp (r*t)*(∑ d ∈ S, (Real.log d)^k*|centredMultipleRow Φ A d t|)^3 ≤ B t := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun k _ _ =>
    criticalState_sparse_divisor_envelope hW ht hF hc he hs hC hb k⟩

#print axioms riemannHypothesis_or_sparse_divisor_envelope
#print axioms criticalState_all_divisor_cubic_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
