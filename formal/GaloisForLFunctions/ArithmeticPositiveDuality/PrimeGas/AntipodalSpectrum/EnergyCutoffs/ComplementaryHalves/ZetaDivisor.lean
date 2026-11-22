import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.JointPartition
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Divisor of the complementary partition

Interleaving copies adds exactly the simple zeros of the binary return
factor. Away from the imaginary return lattice, the joint partition and
the full zeta partition have identical local orders.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

def factor (s : ℂ) := (2:ℂ)^s-1

def frequency (k : ℤ) : ℂ := (((k:ℝ)*(2*Real.pi)/Real.log 2:ℝ):ℂ)*Complex.I

private theorem log_two : Complex.log 2 = (Real.log 2:ℂ) := by
  rw [Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2),Complex.ofReal_ofNat]

private theorem log_ne : Complex.log 2 ≠ 0 := log_two ▸ Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'

private theorem frequency_scaled (k : ℤ) :
    Complex.log 2*frequency k = (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
  rw [frequency,log_two,← mul_assoc,← Complex.ofReal_mul,mul_comm (Real.log 2),
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
  push_cast
  ring

theorem factor_zero_iff (s : ℂ) : factor s = 0 ↔ ∃ k : ℤ, s = frequency k := by
  rw [factor,sub_eq_zero,Complex.cpow_def_of_ne_zero two_ne_zero,Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k,mul_left_cancel₀ log_ne (hk.trans (frequency_scaled k).symm)⟩
  · rintro ⟨k,rfl⟩
    exact ⟨k,frequency_scaled k⟩

theorem frequency_re (k : ℤ) : (frequency k).re = 0 := by
  simp only [frequency,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero]

private theorem factor_exp : factor = fun s : ℂ => Complex.exp (Complex.log 2*s)-1 := by
  funext s
  rw [factor,Complex.cpow_def_of_ne_zero two_ne_zero]

private theorem factor_analytic (s : ℂ) : AnalyticAt ℂ factor s := by
  rw [factor_exp]
  exact ((analyticAt_const.mul analyticAt_id).cexp).sub analyticAt_const

theorem continued_meromorphic (s : ℂ) : MeromorphicAt continued s :=
  (factor_analytic s).meromorphicAt.mul (HTGeometry.meromorphicOn_riemannZeta s (Set.mem_univ s))

theorem joint_divisor (s : ℂ) :
    meromorphicOrderAt continued s =
      (if factor s = 0 then 1 else 0)+meromorphicOrderAt riemannZeta s := by
  change meromorphicOrderAt (factor*riemannZeta) s = _
  have ha := factor_analytic s
  rw [meromorphicOrderAt_mul ha.meromorphicAt (HTGeometry.meromorphicOn_riemannZeta s (Set.mem_univ s)),
    ha.meromorphicOrderAt_eq]
  by_cases hz : factor s = 0
  · have he : Complex.exp (Complex.log 2*s) = 1 := by rw [factor_exp] at hz; exact sub_eq_zero.mp hz
    have hd : HasDerivAt factor (Complex.log 2) s := by
      rw [factor_exp]
      simpa only [id_eq,mul_one,he,one_mul] using ((((hasDerivAt_id s).const_mul (Complex.log 2)).cexp).sub_const 1)
    rw [ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz (by rw [hd.deriv]; exact log_ne),if_pos hz]
    rfl
  · rw [ha.analyticOrderAt_eq_zero.mpr hz,if_neg hz]
    rfl

/-- The added clock zeros are genuine and simple, including the zero at the origin. -/
theorem simple_clock_zeros (k : ℤ) :
    continued (frequency k) = 0 ∧ meromorphicOrderAt continued (frequency k) = 1 := by
  let w := frequency k
  have hw : w.re = 0 := frequency_re k
  have hz : factor w = 0 := (factor_zero_iff w).mpr ⟨k,rfl⟩
  have hn : riemannZeta w ≠ 0 := _root_.RHTower.riemannZeta_ne_zero_of_re_le_zero hw.le (by
    intro n he
    have h := congrArg Complex.re he
    simp only [hw,Complex.neg_re,Complex.mul_re,Complex.natCast_re,Complex.add_re,Complex.one_re,
      Complex.natCast_im,Complex.add_im,Complex.one_im] at h
    norm_num at h
    linarith only [h,Nat.cast_nonneg (α := ℝ) n])
  have ha := HTGeometry.analyticAt_riemannZeta (s := w) (by intro h; rw [h,Complex.one_re] at hw; norm_num at hw)
  constructor
  · change factor w*riemannZeta w = 0
    rw [hz,zero_mul]
  · change meromorphicOrderAt continued w = 1
    rw [joint_divisor,if_pos hz,ha.meromorphicOrderAt_eq,ha.analyticOrderAt_eq_zero.mpr hn]
    rfl

private theorem factor_nonzero (s : {z : ℂ // 0 < z.re}) : factor s.val ≠ 0 := by
  rintro h
  obtain ⟨k,hk⟩ := (factor_zero_iff _).mp h
  exact s.property.ne' ((congrArg Complex.re hk).trans (frequency_re k))

theorem positive_divisor (s : {z : ℂ // 0 < z.re}) :
    meromorphicOrderAt continued s.val = meromorphicOrderAt riemannZeta s.val := by
  rw [joint_divisor,if_neg (factor_nonzero s),zero_add]

theorem positive_zero_iff (s : {z : ℂ // 0 < z.re}) : continued s.val = 0 ↔ riemannZeta s.val = 0 := by
  change factor s.val*riemannZeta s.val = 0 ↔ _
  rw [mul_eq_zero,or_iff_right (factor_nonzero s)]

/-- The completed two-copy trace is the reflected parity sector of the full prime gas. -/
theorem parity_exchange (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1 < z.re}) :
    Complex.Gammaℝ s.val*ContinuousLinearMap.opTrace (gibbs t j s) = -_root_.RHTower.lambdaParity (1-s.val) := by
  rw [gibbs_trace,partition_eq_zeta,← _root_.RHTower.hzeta_one_half s.property,
    ← _root_.RHTower.lambdaHalfShift_eq_halfLevels s.property,_root_.RHTower.lambdaParity_one_sub,neg_neg]

#print axioms joint_divisor
#print axioms continued_meromorphic
#print axioms simple_clock_zeros
#print axioms positive_divisor
#print axioms parity_exchange

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
