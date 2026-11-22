import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Realization
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Divisor

/-!
# Zeta zeros from coincidence of different clock traces

At a common block the winding factor separates distinct orders throughout
the open right half-plane. Any such pair therefore detects the full scaled
zeta divisor by subtraction. Two clocks calibrated on the prime two already
detect exactly the temperatures at which every continued clock response agrees.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open ZeroForcingCalculus

private theorem factor_as_difference {q : ℂ} (hq : ‖q‖ < 1) (m : ℕ) (hm : 1 < m) :
    factor m q = 2*((1-q)⁻¹-(1-q^m)⁻¹) := by
  have hd : 1-q ≠ 0 := by simpa only [pow_one] using one_sub_pow_ne hq (one_ne_zero : (1:ℕ) ≠ 0)
  have hn := one_sub_pow_ne hq (show m ≠ 0 by omega)
  have hqm : q*q^(m-1) = q^m := by rw [← pow_succ',Nat.sub_add_cancel hm.le]
  have hnum : 2*q*(1-q^(m-1)) = 2*(q-q^m) := by rw [← hqm]; ring
  rw [factor,hnum]
  field_simp [hd,hn]
  ring

private theorem factor_injective {q : ℂ} (hq : ‖q‖ < 1) (hne : q ≠ 0) {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    factor m q = factor n q ↔ m = n := by
  rw [factor_as_difference hq m hm,factor_as_difference hq n hn]
  constructor
  · intro h
    have he := sub_right_inj.mp (inv_inj.mp (sub_right_inj.mp (mul_left_cancel₀ two_ne_zero h)))
    apply pow_right_injective₀ (norm_pos_iff.mpr hne) hq.ne
    simpa only [norm_pow] using congrArg norm he
  · rintro rfl; rfl

private def weight (t : ExceptionalTime) (s : ℂ) := factor (windingOrder t) (heat s (block t))

private theorem weight_analytic (t : ExceptionalTime) (s : {s : ℂ // 0 < s.re}) : AnalyticAt ℂ (weight t) s.val := by
  have ha : AnalyticAt ℂ (fun z => heat z (block t)) s.val := (analyticAt_id.neg.mul analyticAt_const).cexp
  have hq := heat_contraction _ (block_nontrivial t) _ s.property
  have hm := order_nontrivial t
  have h₁ : 1-heat s.val (block t) ≠ 0 := by simpa only [pow_one] using one_sub_pow_ne hq (one_ne_zero : (1:ℕ) ≠ 0)
  exact ((analyticAt_const.mul ha).mul (analyticAt_const.sub (ha.pow (windingOrder t-1)))).div
    ((analyticAt_const.sub ha).mul (analyticAt_const.sub (ha.pow (windingOrder t))))
    (mul_ne_zero h₁ (one_sub_pow_ne hq (by omega)))

private theorem weight_ne {t u : ExceptionalTime} (hb : block t = block u) (hm : windingOrder t ≠ windingOrder u)
    (s : {s : ℂ // 0 < s.re}) : weight t s.val ≠ weight u s.val := by
  unfold weight
  rw [hb]
  exact fun h => hm ((factor_injective (heat_contraction _ (block_nontrivial u) _ s.property)
    (Complex.exp_ne_zero _) (order_nontrivial t) (order_nontrivial u)).mp h)

/-- Distinct winding orders on the same block agree precisely at the scaled zeta zeros. -/
theorem same_block_coincidence {t u : ExceptionalTime} (hb : block t = block u)
    (hm : windingOrder t ≠ windingOrder u) (s : {s : ℂ // 0 < s.re}) :
    response t s.val = response u s.val ↔ riemannZeta (2*s.val) = 0 := by
  change riemannZeta _ * weight t _ = riemannZeta _ * weight u _ ↔ _
  exact ⟨fun h => Classical.byContradiction fun hn => weight_ne hb hm s (mul_left_cancel₀ hn h),
    fun h => by rw [h,zero_mul,zero_mul]⟩

/-- Clock comparison preserves all multiplicities, including the simple pole at one half. -/
theorem same_block_difference_order {t u : ExceptionalTime} (hb : block t = block u)
    (hm : windingOrder t ≠ windingOrder u) (s : {s : ℂ // 0 < s.re}) :
    meromorphicOrderAt (response t-response u) s.val = meromorphicOrderAt riemannZeta (2*s.val) := by
  have hf : response t-response u = (weight t-weight u)*(fun z : ℂ => riemannZeta (2*z)) := by
    funext z
    change riemannZeta _ * weight t z - riemannZeta _ * weight u z = (weight t z-weight u z)*riemannZeta _
    ring
  rw [hf,meromorphicOrderAt_mul_of_ne_zero ((weight_analytic t s).sub (weight_analytic u s)) (sub_ne_zero.mpr (weight_ne hb hm s))]
  exact (meromorphicOrderAt_riemannZeta_const_mul (c := 2) two_ne_zero s.val).2

private def primeTwo : {H : ℕ+ // 1 < H.val ∧ ¬IsSquare H.val} := by
  refine ⟨2,by change 1 < 2; norm_num,?_⟩
  change ¬IsSquare (2:ℕ)
  simpa only [pow_one] using _root_.RHTower.not_isSquare_prime_pow_odd Nat.prime_two (show Odd (1:ℕ) from ⟨0,rfl⟩)

private def primeClock (m : {m : ℕ // 1 < m ∧ ∃ j : ℕ, m = 2^j}) : ExceptionalTime :=
  ⟨calibration primeTwo.val m.val,(calibrated_parameters primeTwo m).choose⟩

private theorem primeClock_spec (m : {m : ℕ // 1 < m ∧ ∃ j : ℕ, m = 2^j}) :
    block (primeClock m) = 2 ∧ windingOrder (primeClock m) = m.val :=
  (calibrated_parameters primeTwo m).choose_spec

def halfTurnClock := primeClock ⟨2,by norm_num,1,by norm_num⟩
def quarterTurnClock := primeClock ⟨4,by norm_num,2,by norm_num⟩

theorem prime_clock_parameters : (block halfTurnClock = 2 ∧ windingOrder halfTurnClock = 2) ∧
    (block quarterTurnClock = 2 ∧ windingOrder quarterTurnClock = 4) := ⟨primeClock_spec _,primeClock_spec _⟩

theorem prime_clock_difference (s : {s : ℂ // 0 < s.re}) :
    response quarterTurnClock s.val-response halfTurnClock s.val =
      riemannZeta (2*s.val)*(2*(heat s.val 2)^2/(1-(heat s.val 2)^4)) := by
  obtain ⟨⟨hb,hm⟩,⟨hb',hm'⟩⟩ := prime_clock_parameters
  let q := heat s.val 2
  have hq : ‖q‖ < 1 := heat_contraction _ (by change 1 < 2; norm_num) _ s.property
  unfold response
  rw [hb,hm,hb',hm',← mul_sub,factor_as_difference hq 2 (by norm_num),factor_as_difference hq 4 (by norm_num)]
  apply congrArg (riemannZeta (2*s.val) * ·)
  change 2*((1-q)⁻¹-(1-q^4)⁻¹)-2*((1-q)⁻¹-(1-q^2)⁻¹) = 2*q^2/(1-q^4)
  have h2 := one_sub_pow_ne hq (show (2:ℕ) ≠ 0 by norm_num)
  have h4 := one_sub_pow_ne hq (show (4:ℕ) ≠ 0 by norm_num)
  rw [show 2*((1-q)⁻¹-(1-q^4)⁻¹)-2*((1-q)⁻¹-(1-q^2)⁻¹) = 2*((1-q^2)⁻¹-(1-q^4)⁻¹) by ring]
  field_simp [h2,h4]
  ring

theorem prime_clock_coincidence (s : {s : ℂ // 0 < s.re}) :
    response quarterTurnClock s.val = response halfTurnClock s.val ↔ riemannZeta (2*s.val) = 0 := by
  obtain ⟨⟨hb,hm⟩,⟨hb',hm'⟩⟩ := prime_clock_parameters
  exact same_block_coincidence (hb'.trans hb.symm) (by rw [hm,hm']; norm_num) s

/-- Two specified physical clocks detect universal agreement of all continued responses. -/
theorem universal_coincidence (s : {s : ℂ // 0 < s.re}) :
    (∀ t u : ExceptionalTime, response t s.val = response u s.val) ↔ riemannZeta (2*s.val) = 0 := by
  refine ⟨fun h => (prime_clock_coincidence s).mp (h _ _),?_⟩
  intro hz t u
  exact ((response_zero_iff t s).mpr hz).trans ((response_zero_iff u s).mpr hz).symm

theorem rh_iff_coincidence_isometric : RiemannHypothesis ↔
    ∀ s : {s : ℂ // 0 < s.re ∧ s.re < 1/2},
      (∀ t u : ExceptionalTime, response t s.val = response u s.val) →
      ∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split (2*s.val) f x := by
  rw [rh_iff_response_zeros_isometric halfTurnClock]
  apply forall_congr'
  intro s
  exact imp_congr ((response_zero_iff halfTurnClock ⟨_,s.property.1⟩).trans
    (universal_coincidence ⟨_,s.property.1⟩).symm) Iff.rfl

#print axioms same_block_coincidence
#print axioms same_block_difference_order
#print axioms prime_clock_parameters
#print axioms prime_clock_difference
#print axioms prime_clock_coincidence
#print axioms universal_coincidence
#print axioms rh_iff_coincidence_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
