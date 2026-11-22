import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.HolomorphicContrast
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CompositionRigidity

/-!
# Recovery of the zeta divisor from two prime clock comparisons

The heat amplitudes at two and three return simultaneously to their values
at one only at one. Their divided differences are both nonzero there.
At every point one comparison therefore preserves the full zero order.
Weighting the two finite readings by their conjugate transfers recovers
the complex amplitude of the entire pole-cleared zeta function.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open Filter
open scoped Topology ComplexConjugate

private def primeBase (p : Nat.Primes) : {H : ℕ+ // 1 < H.val ∧ ¬IsSquare H.val} := by
  refine ⟨(⟨p.val,p.property.pos⟩ : ℕ+),p.property.one_lt,?_⟩
  change ¬IsSquare p.val
  simpa only [pow_one] using _root_.RHTower.not_isSquare_prime_pow_odd p.property (show Odd (1:ℕ) from ⟨0,rfl⟩)

private def firstOrder : {m : ℕ // 1 < m ∧ ∃ d : ℕ, m = 2^d} := ⟨2,by norm_num,1,by norm_num⟩

/-- Sampling time π/log(p) against the vacuum. -/
def primeHalfTurnClock (p : Nat.Primes) : ExceptionalTime :=
  ⟨calibration (primeBase p).val 2,(calibrated_parameters (primeBase p) firstOrder).choose⟩

theorem prime_half_turn_radix (p : Nat.Primes) :
    tailRadix (primeHalfTurnClock p) 0 = (⟨p.val,p.property.pos⟩ : ℕ+) := by
  have h := (calibrated_parameters (primeBase p) firstOrder).choose_spec
  change block (primeHalfTurnClock p) = (primeBase p).val ∧ windingOrder (primeHalfTurnClock p) = 2 at h
  calc tailRadix (primeHalfTurnClock p) 0 = (primeBase p).val := by
         rw [tailRadix,show refined (primeHalfTurnClock p) 0 = primeHalfTurnClock p from rfl,h.1,h.2,
           show (2:ℕ)/2 = 1 by norm_num,pow_one]
       _ = _ := rfl

private def threeClock := primeHalfTurnClock ⟨3,Nat.prime_three⟩

private theorem radix_two : tailRadix halfTurnClock 0 = 2 := by
  rw [tailRadix,show refined halfTurnClock 0 = halfTurnClock from rfl,
    prime_clock_parameters.1.1,prime_clock_parameters.1.2,show (2:ℕ)/2 = 1 by norm_num,pow_one]

private theorem radix_three : tailRadix threeClock 0 = 3 := prime_half_turn_radix ⟨3,Nat.prime_three⟩

/-- Ordered pair of finite comparisons with integer multipliers three and four. -/
def twoPrimeCutoff (X : ℕ) (w : ℂ) :=
  (adjacentCutoff halfTurnClock 0 X w, adjacentCutoff threeClock 0 X w)

theorem two_prime_cutoff_limit (w : {z : ℂ // 0 < z.re}) :
    Tendsto (fun X => twoPrimeCutoff X w.val) atTop (𝓝 (contrastResponse 2 w.val,contrastResponse 3 w.val)) := by
  have h₂ := adjacent_cutoff_holomorphic_limit halfTurnClock 0 w
  have h₃ := adjacent_cutoff_holomorphic_limit threeClock 0 w
  rw [radix_two] at h₂
  rw [radix_three] at h₃
  exact h₂.prodMk_nhds h₃

/-- A transfer factor at two or three is nonzero at every point, including the removed pole. -/
theorem two_prime_transfer_cover (w : {z : ℂ // 0 < z.re}) :
    contrastTransfer 2 w.val ≠ 0 ∨ contrastTransfer 3 w.val ≠ 0 := by
  by_contra! h
  have h₂ := (contrastTransfer_zero_iff ⟨2,by change 1 < (2:ℕ); norm_num⟩ w).mp h.1
  have h₃ := (contrastTransfer_zero_iff ⟨3,by change 1 < (3:ℕ); norm_num⟩ w).mp h.2
  exact h₂.1 (two_prime_heat_injective (Prod.ext h₂.2 h₃.2))

theorem two_prime_cutoff_zero_iff (w : {z : ℂ // 0 < z.re}) :
    Tendsto (fun X => twoPrimeCutoff X w.val) atTop (𝓝 (0,0)) ↔ _root_.RHTower.zetaPoleUnit w.val = 0 := by
  have h := two_prime_cutoff_limit w
  constructor
  · intro hz
    have he := tendsto_nhds_unique h hz
    rcases two_prime_transfer_cover w with h₂ | h₃
    · exact (mul_eq_zero.mp (congrArg Prod.fst he)).resolve_right h₂
    · exact (mul_eq_zero.mp (congrArg Prod.snd he)).resolve_right h₃
  · intro hz
    simpa only [contrastResponse,hz,zero_mul] using h

/-- The simultaneous finite readings vanish exactly at genuine partition zeros. -/
theorem two_prime_cutoff_zeta_zeros (w : {z : ℂ // 0 < z.re}) :
    Tendsto (fun X => twoPrimeCutoff X w.val) atTop (𝓝 (0,0)) ↔ w.val ≠ 1 ∧ riemannZeta w.val = 0 := by
  rw [two_prime_cutoff_zero_iff]
  rcases eq_or_ne w.val 1 with he | he
  · simp [he,_root_.RHTower.zetaPoleUnit_one]
  · rw [_root_.RHTower.zetaPoleUnit_of_ne he,mul_eq_zero,or_iff_right (sub_ne_zero.mpr he),and_iff_right he]

/-- RH says that every common vanishing reading in the strip admits an isometric composition. -/
theorem rh_iff_two_prime_cutoffs_isometric :
    RiemannHypothesis ↔ ∀ s : {s : ℂ // 0 < s.re ∧ s.re < 1/2},
      Tendsto (fun X => twoPrimeCutoff X (2*s.val)) atTop (𝓝 (0,0)) →
        ∃ U : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, U f x = split (2*s.val) f x := by
  rw [rh_iff_response_zeros_isometric halfTurnClock]
  apply forall_congr' fun s => ?_
  have hp : 0 < (2*s.val).re := by rw [two_mul,Complex.add_re]; linarith only [s.property.1]
  have hl : (2*s.val).re < 1 := by rw [two_mul,Complex.add_re]; linarith only [s.property.2]
  have he : 2*s.val ≠ 1 := fun h => hl.ne (by rw [h,Complex.one_re])
  rw [response_zero_iff halfTurnClock ⟨s.val,s.property.1⟩,two_prime_cutoff_zeta_zeros ⟨2*s.val,hp⟩,and_iff_right he]

/-- The minimum of the observed zero orders is the exact order of the regularized zeta function. -/
theorem two_prime_cutoff_divisor (w : {z : ℂ // 0 < z.re}) :
    min (analyticOrderAt (contrastResponse 2) w.val) (analyticOrderAt (contrastResponse 3) w.val) =
      analyticOrderAt _root_.RHTower.zetaPoleUnit w.val := by
  have hz := _root_.RHTower.differentiable_zetaPoleUnit.analyticAt w.val
  have h (C : {c : ℕ+ // 1 < c.val}) : analyticOrderAt (contrastResponse C.val) w.val =
      analyticOrderAt _root_.RHTower.zetaPoleUnit w.val + analyticOrderAt (contrastTransfer C.val) w.val :=
    analyticOrderAt_mul hz (contrastTransfer_analytic C w)
  rw [h ⟨2,by change 1 < (2:ℕ); norm_num⟩,h ⟨3,by change 1 < (3:ℕ); norm_num⟩]
  rcases two_prime_transfer_cover w with h₂ | h₃
  · rw [analyticOrderAt_eq_zero.mpr (Or.inr h₂),add_zero,min_eq_left (le_self_add)]
  · rw [analyticOrderAt_eq_zero.mpr (Or.inr h₃),add_zero,min_eq_right (le_self_add)]

/-- Sum of the squared moduli of the two transfer amplitudes. -/
def twoPrimeTransferMass (w : ℂ) := Complex.normSq (contrastTransfer 2 w) + Complex.normSq (contrastTransfer 3 w)

theorem two_prime_transfer_mass_pos (w : {z : ℂ // 0 < z.re}) : 0 < twoPrimeTransferMass w.val := by
  rcases two_prime_transfer_cover w with h₂ | h₃
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h₂) (Complex.normSq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (Complex.normSq_pos.mpr h₃)

/-- Linear reconstruction from the two complex finite measurements. -/
def reconstructedCutoff (X : ℕ) (w : ℂ) : ℂ :=
  (conj (contrastTransfer 2 w)*(twoPrimeCutoff X w).1 +
   conj (contrastTransfer 3 w)*(twoPrimeCutoff X w).2)/(twoPrimeTransferMass w:ℂ)

theorem reconstructed_cutoff_limit (w : {z : ℂ // 0 < z.re}) :
    Tendsto (fun X => reconstructedCutoff X w.val) atTop (𝓝 (_root_.RHTower.zetaPoleUnit w.val)) := by
  let a := contrastTransfer 2 w.val
  let b := contrastTransfer 3 w.val
  let Z := _root_.RHTower.zetaPoleUnit w.val
  have h := two_prime_cutoff_limit w
  have hp := ((h.fst_nhds.const_mul (conj a)).add (h.snd_nhds.const_mul (conj b))).div_const (twoPrimeTransferMass w.val:ℂ)
  change Tendsto (fun X => reconstructedCutoff X w.val) atTop
    (𝓝 ((conj a*(Z*a)+conj b*(Z*b))/(twoPrimeTransferMass w.val:ℂ))) at hp
  have hm : (twoPrimeTransferMass w.val:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (two_prime_transfer_mass_pos w).ne'
  have he : conj a*(Z*a)+conj b*(Z*b) = Z*(twoPrimeTransferMass w.val:ℂ) := by
    change _ = Z*((Complex.normSq a + Complex.normSq b:ℝ):ℂ)
    rw [Complex.ofReal_add,← Complex.mul_conj,← Complex.mul_conj]
    ring
  rwa [he,mul_div_cancel_right₀ Z hm] at hp

#print axioms prime_half_turn_radix
#print axioms two_prime_cutoff_limit
#print axioms two_prime_cutoff_zero_iff
#print axioms two_prime_cutoff_zeta_zeros
#print axioms rh_iff_two_prime_cutoffs_isometric
#print axioms two_prime_cutoff_divisor
#print axioms reconstructed_cutoff_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
