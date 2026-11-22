import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.Partition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PrimeParityPartition

/-!
# Zeta zeros and poles in the rejected partition

The geometric winding factor is an analytic unit to the right of the
imaginary axis. Each exceptional clock therefore records the entire scaled
zeta divisor, including the simple pole on the heat boundary.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open HTGeometry ZeroForcingCalculus

private theorem analytic_heat (B : ℕ+) (s : ℂ) : AnalyticAt ℂ (fun z => heat z B) s := by
  unfold heat
  exact (analyticAt_id.neg.mul analyticAt_const).cexp

private def unitFactor (t : ExceptionalTime) (s : ℂ) := factor (windingOrder t) (heat s (block t))

private theorem unit_at (t : ExceptionalTime) (s : {s : ℂ // 0 < s.re}) :
    AnalyticAt ℂ (unitFactor t) s.val ∧ unitFactor t s.val ≠ 0 := by
  let m := windingOrder t
  let q := heat s.val (block t)
  have hq : ‖q‖ < 1 := heat_contraction _ (block_nontrivial t) _ s.property
  have hm : 1 < m := order_nontrivial t
  have h₁ : 1-q ≠ 0 := by simpa only [pow_one] using one_sub_pow_ne hq (one_ne_zero : (1:ℕ) ≠ 0)
  have h₂ : 1-q^m ≠ 0 := one_sub_pow_ne hq (by omega)
  have ha := analytic_heat (block t) s.val
  exact ⟨((analyticAt_const.mul ha).mul (analyticAt_const.sub (ha.pow (m-1)))).div
    ((analyticAt_const.sub ha).mul (analyticAt_const.sub (ha.pow m))) (mul_ne_zero h₁ h₂),
    factor_ne_zero hq (Complex.exp_ne_zero _) hm⟩

/-- The response agreeing with the operator trace is meromorphic at every complex temperature. -/
theorem response_meromorphic (t : ExceptionalTime) (s : ℂ) : MeromorphicAt (response t) s := by
  have hq := (analytic_heat (block t) s).meromorphicAt
  have hz := (meromorphicOrderAt_riemannZeta_const_mul (c := 2) two_ne_zero s).1
  let m := windingOrder t
  exact hz.mul (((analyticAt_const.meromorphicAt.mul hq).mul (analyticAt_const.meromorphicAt.sub (hq.pow (m-1)))).div
    ((analyticAt_const.meromorphicAt.sub hq).mul (analyticAt_const.meromorphicAt.sub (hq.pow m))))

theorem response_zero_iff (t : ExceptionalTime) (s : {s : ℂ // 0 < s.re}) :
    response t s.val = 0 ↔ riemannZeta (2*s.val) = 0 := by
  change riemannZeta (2*s.val)*unitFactor t s.val = 0 ↔ _
  rw [mul_eq_zero,or_iff_left (unit_at t s).2]

theorem response_regular (t : ExceptionalTime) (s : {s : ℂ // 0 < s.re}) (h : 2*s.val ≠ 1) :
    AnalyticAt ℂ (response t) s.val :=
  ((HTGeometry.analyticAt_riemannZeta h).comp (analyticAt_const.mul analyticAt_id)).mul (unit_at t s).1

/-- Zeros and poles retain their full multiplicities under the doubling of inverse temperature. -/
theorem response_order (t : ExceptionalTime) (s : {s : ℂ // 0 < s.re}) :
    meromorphicOrderAt (response t) s.val = meromorphicOrderAt riemannZeta (2*s.val) := by
  obtain ⟨ha,hn⟩ := unit_at t s
  change meromorphicOrderAt ((fun z : ℂ => riemannZeta (2*z)) * unitFactor t) s.val = _
  rw [mul_comm,meromorphicOrderAt_mul_of_ne_zero ha hn]
  exact (meromorphicOrderAt_riemannZeta_const_mul (c := 2) two_ne_zero s.val).2

theorem response_critical_pole (t : ExceptionalTime) : meromorphicOrderAt (response t) (1/2) = ((-1 : ℤ) : WithTop ℤ) := by
  have h := response_order t ⟨1/2,by norm_num⟩
  change meromorphicOrderAt (response t) (1/2) = meromorphicOrderAt riemannZeta (2*(1/2)) at h
  simpa only [show (2*(1/2):ℂ) = 1 by norm_num,meromorphicOrderAt_riemannZeta_one] using h

/-- For each exceptional clock, vanishing of its continued rejection in the half strip
selects an isometric composition at doubled temperature exactly when RH holds. -/
theorem rh_iff_response_zeros_isometric (t : ExceptionalTime) : RiemannHypothesis ↔
    ∀ s : {s : ℂ // 0 < s.re ∧ s.re < 1/2}, response t s.val = 0 →
      ∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split (2*s.val) f x := by
  constructor
  · intro rh s hs
    apply (split_isometric_iff _).mpr
    have hpos : 0 < (2*s.val).re := by rw [two_mul,Complex.add_re]; linarith only [s.property.1]
    have hlt : (2*s.val).re < 1 := by rw [two_mul,Complex.add_re]; linarith only [s.property.2]
    apply rh (2*s.val) ((response_zero_iff t ⟨_,s.property.1⟩).mp hs)
    · rintro ⟨n,hn⟩
      rw [hn] at hpos
      norm_num [Complex.mul_re] at hpos
      linarith only [hpos,Nat.cast_nonneg (α := ℝ) n]
    · rintro h
      rw [h,Complex.one_re] at hlt
      exact hlt.false
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro z hhalf hone hz
    have hu : 0 < (z/2).re ∧ (z/2).re < 1/2 := by
      rw [Complex.div_ofNat_re]; constructor <;> linarith only [hhalf,hone]
    have hd : 2*(z/2) = z := by ring
    have hh : response t (z/2) = 0 := (response_zero_iff t ⟨_,hu.1⟩).mpr (by change riemannZeta (2*(z/2)) = 0; rwa [hd])
    have hi := (split_isometric_iff _).mp (h ⟨_,hu⟩ hh)
    change (2*(z/2)).re = 1/2 at hi
    rw [hd] at hi
    exact hhalf.ne' hi

#print axioms response_meromorphic
#print axioms response_zero_iff
#print axioms response_order
#print axioms response_critical_pole
#print axioms rh_iff_response_zeros_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
