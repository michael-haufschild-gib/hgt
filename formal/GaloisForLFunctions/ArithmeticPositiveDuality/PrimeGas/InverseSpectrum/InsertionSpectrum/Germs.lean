import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Partition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-! # Insertion measured by partition germs, including at zeros -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- First nonzero coefficient in the local expansion of the relative partition. -/
def omissionLead (v : MissingWave) (z : ℂ) := meromorphicTrailingCoeffAt (omissionPartition v) z

theorem omission_finite_order (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (omissionPartition v) z ≠ ⊤ := by
  intro h
  have hzero := (omissionPartition_analytic v).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt 0).isPreconnected hz (meromorphicOrderAt_eq_top_iff.mp h).frequently
  exact omissionPartition_two_ne v (hzero (show (2:ℂ) ∈ {w : ℂ | 0 < w.re} by change 0 < (2:ℂ).re; norm_num))

theorem omissionLead_ne (v : MissingWave) {z : ℂ} (hz : 0 < z.re) : omissionLead v z ≠ 0 :=
  (omissionPartition_analytic v z hz).meromorphicAt.meromorphicTrailingCoeffAt_ne_zero (omission_finite_order v hz)

private theorem insertion_germ (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    omissionPartition (insertMissing a v) =ᶠ[𝓝[≠] z] (fun w => heat w a)*omissionPartition v := by
  have hu : {w : ℂ | 0 < w.re} ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  filter_upwards [mem_nhdsWithin_of_mem_nhds hu] with w hw
  exact omissionPartition_insert a v hw

theorem insertion_preserves_order (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt (omissionPartition (insertMissing a v)) z = meromorphicOrderAt (omissionPartition v) z := by
  rw [meromorphicOrderAt_congr (insertion_germ a v hz)]
  exact meromorphicOrderAt_mul_of_ne_zero (insertion_heat_analytic a z) (Complex.exp_ne_zero _)

theorem omissionLead_insert (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    omissionLead (insertMissing a v) z = heat z a*omissionLead v z := by
  rw [omissionLead,meromorphicTrailingCoeffAt_congr_nhdsNE (insertion_germ a v hz),
    (insertion_heat_analytic a z).meromorphicAt.meromorphicTrailingCoeffAt_mul (omissionPartition_analytic v z hz).meromorphicAt,
    (insertion_heat_analytic a z).meromorphicTrailingCoeffAt_of_ne_zero (Complex.exp_ne_zero _)]
  rfl

/-- The quotient of the leading coefficients removes a common zero at each measurement point. -/
def insertionReading (a : ℕ+) (v : MissingWave) (z : ℂ) := omissionLead (insertMissing a v) z/omissionLead v z

theorem insertionReading_eq_heat (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    insertionReading a v z = heat z a := by
  rw [insertionReading,omissionLead_insert a v hz,mul_div_cancel_right₀ _ (omissionLead_ne v hz)]

/-- The energy increment can also be recovered from the derivative of the normalized germ at a common zero. -/
theorem insertionReading_derivative (a : ℕ+) (v : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    deriv (insertionReading a v) z = -(energy a:ℂ)*insertionReading a v z := by
  have hu : {w : ℂ | 0 < w.re} ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have he : insertionReading a v =ᶠ[𝓝 z] fun w => heat w a := by
    filter_upwards [hu] with w hw
    exact insertionReading_eq_heat a v hw
  rw [he.deriv_eq,insertionReading_eq_heat a v hz]
  have hd := (((hasDerivAt_id z).neg.mul_const (energy a:ℂ)).cexp).deriv
  change deriv (fun w => heat w a) z = heat z a*((-1)*(energy a:ℂ)) at hd
  rw [hd,neg_one_mul,mul_comm]

/-- A single prime compares outgoing and incoming leading intensities at every positive real part. -/
theorem insertion_leading_balance (p : Nat.Primes) (v : MissingWave) {s : ℂ} (hs : 0 < s.re) :
    let a : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
    (a.val:ℝ)*‖omissionLead (insertMissing a v) s‖^2 = ‖omissionLead v s‖^2 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  let a : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
  change (a.val:ℝ)*‖omissionLead (insertMissing a v) s‖^2 = _ ↔ _
  have hn := pow_ne_zero 2 (norm_ne_zero_iff.mpr (omissionLead_ne v hs))
  have he : energy a ≠ 0 := (Real.log_pos (show (1:ℝ) < (a.val:ℝ) by exact_mod_cast p.property.one_lt)).ne'
  rw [omissionLead_insert a v hs,norm_mul,mul_pow,← mul_assoc,← shellMass_eq,split_isometric_iff]
  constructor
  · intro h
    have hm : shellMass s a = 1 := mul_right_cancel₀ hn (h.trans (one_mul _).symm)
    have hhalf := (mul_eq_zero.mp ((Real.exp_eq_one_iff _).mp hm)).resolve_right he
    linarith only [hhalf]
  · intro h
    simp only [shellMass,h]
    norm_num

/-- Two prime insertions determine the real inverse temperature and Hamiltonian time, even at zeros. -/
theorem two_insertion_readings_injective (v w : MissingWave) :
    Function.Injective (fun s : {z : ℂ // 0 < z.re} => (insertionReading 2 v s.val,insertionReading 3 w s.val)) := by
  intro s t h
  apply Subtype.ext
  apply two_prime_heat_injective
  simpa only [insertionReading_eq_heat _ _ s.property,insertionReading_eq_heat _ _ t.property] using h

#print axioms omission_finite_order
#print axioms omissionLead_ne
#print axioms insertion_preserves_order
#print axioms omissionLead_insert
#print axioms insertionReading_eq_heat
#print axioms insertionReading_derivative
#print axioms insertion_leading_balance
#print axioms two_insertion_readings_injective

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
