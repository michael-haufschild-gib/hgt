import GaloisForLFunctions.RHTower.DeningerMobiusCriticalWKBSeam

/-!
# Route E all-order source damping and bounded-reporter firewall

This module closes source-side equations `(6)`--`(11)` and operator equations `(37)`--`(40)`
of the terminal-frame minimax law at their exact reusable interfaces.

For every real order `0 < q ≤ 2`, Möbius--Fisher damping is the power weight
`p^(-q/2)` times one explicit likelihood factor.  Its defect is nonnegative and at most
`3 p^(-q/2-1)`.  The comparison is then lifted to arbitrary finite prime packets and arbitrary
nonnegative phase histories; no terminal geometry is discarded.

The reporter result is representation-independent.  An arbitrary bounded operator on an
arbitrary complex Hilbert space can report at most its operator norm times Fisher energy.  Any
reporter faithful to a half-density signal of order `sqrt X / log(X)^(3 : ℕ)` while its source vector
has Fisher energy of order `1 / log(X)^(3 : ℕ)` must therefore have norm of order `sqrt X`.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-! ## Exact all-order source damping -/

/-- Möbius--Fisher damping is exactly the critical prime half-density divided by its local
normalization. -/
theorem xiMobiusPrimeSchurValuationDamping_eq_prime_rpow
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p =
      (p : ℝ) ^ (-(1 / 2 : ℝ)) / (1 + (p : ℝ) ^ (-1 : ℝ)) := by
  rw [xiMobiusPrimeSchurValuationDamping,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp0 : 0 ≤ (p : ℝ) := by exact_mod_cast p.prop.pos.le
  rw [Real.sqrt_eq_rpow, Real.inv_rpow hp0, Real.rpow_neg_one,
    Real.rpow_neg hp0]

/-- Exact real-power law for every source order. -/
theorem xiMobiusPrimeSchurValuationDamping_rpow
    (p : Nat.Primes) (q : ℝ) :
    xiMobiusPrimeSchurValuationDamping p ^ q =
      (p : ℝ) ^ (-q / 2) * (1 + (p : ℝ) ^ (-1 : ℝ)) ^ (-q) := by
  rw [xiMobiusPrimeSchurValuationDamping_eq_prime_rpow]
  have hp0 : 0 ≤ (p : ℝ) := by exact_mod_cast p.prop.pos.le
  have hx0 : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg hp0 _
  have hnum : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp0 _
  have hden : 0 ≤ 1 + (p : ℝ) ^ (-1 : ℝ) :=
    add_nonneg zero_le_one hx0
  rw [Real.div_rpow hnum hden, ← Real.rpow_mul hp0,
    Real.rpow_neg hden, div_eq_mul_inv]
  congr 1
  ring

/-- Uniform scalar likelihood-factor estimate.  The constant three is valid simultaneously for
all orders `0 < q ≤ 2`; no order-dependent compactness argument is used. -/
theorem one_sub_one_add_rpow_neg_le_three_mul
    {x q : ℝ} (hx0 : 0 ≤ x) (hq0 : 0 < q) (hq2 : q ≤ 2) :
    0 ≤ 1 - (1 + x) ^ (-q) ∧
      1 - (1 + x) ^ (-q) ≤ 3 * x := by
  have hb : 1 ≤ 1 + x := by linarith
  have hb0 : 0 ≤ 1 + x := le_trans (by norm_num) hb
  have hbpos : 0 < 1 + x := lt_of_lt_of_le (by norm_num) hb
  have hpowle : (1 + x) ^ (-q) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hb (show -q ≤ 0 by linarith)
    simpa using h
  have hpowge : (1 + x) ^ (-2 : ℝ) ≤ (1 + x) ^ (-q) :=
    Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have halg : 1 - (1 + x) ^ (-2 : ℝ) ≤ 3 * x := by
    rw [Real.rpow_neg hb0, Real.rpow_two]
    have hsq : 0 < (1 + x) ^ 2 := sq_pos_of_pos hbpos
    calc
      1 - ((1 + x) ^ 2)⁻¹ = ((1 + x) ^ 2 - 1) / ((1 + x) ^ 2) := by
        field_simp
      _ ≤ 3 * x := by
        rw [div_le_iff₀ hsq]
        nlinarith [sq_nonneg x]
  constructor <;> linarith

/-- Pointwise all-order source defect, including its sign.  This is the exact Lean form of
`0 ≤ p^(-q/2) - d_p^q ≤ 3 p^(-q/2-1)` for `0 < q ≤ 2`. -/
theorem xiMobiusPrimeSchurValuationDamping_rpow_defect
    (p : Nat.Primes) {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2) :
    0 ≤ (p : ℝ) ^ (-q / 2) - xiMobiusPrimeSchurValuationDamping p ^ q ∧
      (p : ℝ) ^ (-q / 2) - xiMobiusPrimeSchurValuationDamping p ^ q ≤
        3 * (p : ℝ) ^ (-q / 2 - 1) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp0 : 0 ≤ (p : ℝ) := hp.le
  have hx0 : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg hp0 _
  have hfactor := one_sub_one_add_rpow_neg_le_three_mul hx0 hq0 hq2
  have hm0 : 0 ≤ (p : ℝ) ^ (-q / 2) := Real.rpow_nonneg hp0 _
  rw [xiMobiusPrimeSchurValuationDamping_rpow]
  have hrewrite :
      (p : ℝ) ^ (-q / 2) -
          (p : ℝ) ^ (-q / 2) * (1 + (p : ℝ) ^ (-1 : ℝ)) ^ (-q) =
        (p : ℝ) ^ (-q / 2) *
          (1 - (1 + (p : ℝ) ^ (-1 : ℝ)) ^ (-q)) := by ring
  rw [hrewrite]
  constructor
  · exact mul_nonneg hm0 hfactor.1
  · have hmul := mul_le_mul_of_nonneg_left hfactor.2 hm0
    calc
      (p : ℝ) ^ (-q / 2) *
          (1 - (1 + (p : ℝ) ^ (-1 : ℝ)) ^ (-q)) ≤
          (p : ℝ) ^ (-q / 2) * (3 * (p : ℝ) ^ (-1 : ℝ)) := hmul
      _ = 3 * (p : ℝ) ^ (-q / 2 - 1) := by
        rw [show -q / 2 - 1 = -q / 2 + (-1) by ring,
          Real.rpow_add hp]
        ring

/-- Arbitrary finite prime-packet power frame. -/
def routeESourcePowerFrame
    (q : ℝ) (P : Finset Nat.Primes) (phase : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ P, (p : ℝ) ^ (-q / 2) * phase p

/-- Same packet after canonical Möbius--Fisher damping. -/
def routeESourceDampingFrame
    (q : ℝ) (P : Finset Nat.Primes) (phase : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ P, xiMobiusPrimeSchurValuationDamping p ^ q * phase p

/-- Exact packetwise defect identity before any estimate. -/
theorem routeESourcePowerFrame_sub_dampingFrame
    (q : ℝ) (P : Finset Nat.Primes) (phase : Nat.Primes → ℝ) :
    routeESourcePowerFrame q P phase - routeESourceDampingFrame q P phase =
      ∑ p ∈ P,
        ((p : ℝ) ^ (-q / 2) - xiMobiusPrimeSchurValuationDamping p ^ q) * phase p := by
  rw [routeESourcePowerFrame, routeESourceDampingFrame]
  calc
    (∑ p ∈ P, (p : ℝ) ^ (-q / 2) * phase p) -
        ∑ p ∈ P, xiMobiusPrimeSchurValuationDamping p ^ q * phase p =
        ∑ p ∈ P, ((p : ℝ) ^ (-q / 2) * phase p -
          xiMobiusPrimeSchurValuationDamping p ^ q * phase p) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ p ∈ P,
        ((p : ℝ) ^ (-q / 2) - xiMobiusPrimeSchurValuationDamping p ^ q) * phase p := by
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- All-order product-history stability on an arbitrary finite prime packet.  Every nonnegative
phase history retains defect sign and the complete primewise remainder. -/
theorem routeESourcePowerFrame_sub_dampingFrame_nonneg_le
    {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (P : Finset Nat.Primes) (phase : Nat.Primes → ℝ)
    (hphase : ∀ p ∈ P, 0 ≤ phase p) :
    0 ≤ routeESourcePowerFrame q P phase - routeESourceDampingFrame q P phase ∧
      routeESourcePowerFrame q P phase - routeESourceDampingFrame q P phase ≤
        ∑ p ∈ P, 3 * (p : ℝ) ^ (-q / 2 - 1) * phase p := by
  rw [routeESourcePowerFrame_sub_dampingFrame]
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg
      (xiMobiusPrimeSchurValuationDamping_rpow_defect p hq0 hq2).1
      (hphase p hp)
  · apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_right
      (xiMobiusPrimeSchurValuationDamping_rpow_defect p hq0 hq2).2
      (hphase p hp)

/-- Phase energies bounded by four give the literal source-stability majorant used by terminal
prime histories. -/
theorem routeESourcePowerFrame_sub_dampingFrame_le_twelve
    {q : ℝ} (hq0 : 0 < q) (hq2 : q ≤ 2)
    (P : Finset Nat.Primes) (phase : Nat.Primes → ℝ)
    (hphase0 : ∀ p ∈ P, 0 ≤ phase p)
    (hphase4 : ∀ p ∈ P, phase p ≤ 4) :
    routeESourcePowerFrame q P phase - routeESourceDampingFrame q P phase ≤
      ∑ p ∈ P, 12 * (p : ℝ) ^ (-q / 2 - 1) := by
  refine (routeESourcePowerFrame_sub_dampingFrame_nonneg_le
    hq0 hq2 P phase hphase0).2.trans ?_
  apply Finset.sum_le_sum
  intro p hp
  have hpow : 0 ≤ (p : ℝ) ^ (-q / 2 - 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (hphase4 p hp) hpow]

/-! ## Endpoint and recovery scale -/

/-- Half-density endpoint `q = 1`. -/
theorem xiMobiusPrimeSchurValuationDamping_eq_halfDensity_factor
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p =
      (p : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + (p : ℝ) ^ (-1 : ℝ))⁻¹ := by
  rw [xiMobiusPrimeSchurValuationDamping_eq_prime_rpow, div_eq_mul_inv]

/-- Fisher endpoint `q = 2`; squaring changes the prime power from half-density to harmonic. -/
theorem xiMobiusPrimeSchurValuationDamping_sq_eq_harmonic_factor
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p ^ 2 =
      (p : ℝ)⁻¹ / (1 + (p : ℝ)⁻¹) ^ 2 := by
  have hp0 : 0 ≤ (p : ℝ) := by exact_mod_cast p.prop.pos.le
  rw [xiMobiusPrimeSchurValuationDamping_eq_prime_rpow,
    Real.rpow_neg_one, div_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0]
  convert Real.rpow_neg_one (p : ℝ) using 1 <;> ring

/-- Recovery has the matching upper square-root scale, complementing the corpus lower bound
`p ≤ recovery(p)^(2 : ℕ)`. -/
theorem xiMobiusPrimeSchurValuationRecovery_sq_le_four_mul_prime
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationRecovery p ^ 2 ≤ 4 * (p : ℝ) := by
  let x := xiTransversePrimeApertureDiskNode 1 p
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hx : 0 < x := xiTransversePrimeApertureDiskNode_pos 1 p
  have hxle : x ≤ 1 := by
    dsimp [x]
    rw [xiTransversePrimeApertureDiskNode_one_eq_inv]
    exact (inv_le_one₀ hp).2 (by exact_mod_cast p.prop.one_lt.le)
  have hrec : xiMobiusPrimeSchurValuationRecovery p ^ 2 = (1 + x) ^ 2 / x := by
    simp only [xiMobiusPrimeSchurValuationRecovery, x, div_pow]
    rw [Real.sq_sqrt hx.le]
  have hpx : (p : ℝ) * x = 1 := by
    dsimp [x]
    rw [xiTransversePrimeApertureDiskNode_one_eq_inv]
    exact mul_inv_cancel₀ hp.ne'
  rw [hrec, div_le_iff₀ hx]
  nlinarith [sq_nonneg (1 - x)]

/-! ## Representation-independent reporter firewall -/

section Reporter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Equation `(37)` for every bounded operator on every complex Hilbert space. -/
theorem routeEReporter_inner_le_opNorm_mul_sq (B : H →L[ℂ] H) (z : H) :
    ‖inner ℂ z (B z)‖ ≤ ‖B‖ * ‖z‖ ^ 2 := by
  calc
    ‖inner ℂ z (B z)‖ ≤ ‖z‖ * ‖B z‖ := norm_inner_le_norm _ _
    _ ≤ ‖z‖ * (‖B‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm z) (norm_nonneg z)
    _ = ‖B‖ * ‖z‖ ^ 2 := by ring

/-- Abstract coefficient-faithful reporter firewall. -/
theorem routeEReporter_norm_ge_of_faithful
    (B : H →L[ℂ] H) (z : H) {A E H₁ c₀ : ℝ}
    (hc₀ : 0 < c₀) (hE : 0 < E)
    (hphysical : A ≤ H₁)
    (hfisher : ‖z‖ ^ 2 ≤ E)
    (hfaithful : c₀ * H₁ ≤ ‖inner ℂ z (B z)‖) :
    c₀ * A / E ≤ ‖B‖ := by
  have hA : c₀ * A ≤ c₀ * H₁ :=
    mul_le_mul_of_nonneg_left hphysical hc₀.le
  have hinner := routeEReporter_inner_le_opNorm_mul_sq B z
  have hnormE : ‖B‖ * ‖z‖ ^ 2 ≤ ‖B‖ * E :=
    mul_le_mul_of_nonneg_left hfisher (norm_nonneg B)
  rw [div_le_iff₀ hE]
  exact hA.trans (hfaithful.trans (hinner.trans hnormE))

/-- Equations `(38)`--`(40)` with all constants retained: half-density physical power divided by
Fisher energy forces square-root reporter norm. -/
theorem routeEReporter_norm_ge_sqrt_terminal_scale
    (B : H →L[ℂ] H) (z : H) {X L c C H₁ c₀ : ℝ}
    (hL : 0 < L) (hC : 0 < C) (hc₀ : 0 < c₀)
    (hphysical : c * Real.sqrt X / L ^ 3 ≤ H₁)
    (hfisher : ‖z‖ ^ 2 ≤ C / L ^ 3)
    (hfaithful : c₀ * H₁ ≤ ‖inner ℂ z (B z)‖) :
    (c₀ * c / C) * Real.sqrt X ≤ ‖B‖ := by
  have hE : 0 < C / L ^ 3 := div_pos hC (pow_pos hL _)
  have h := routeEReporter_norm_ge_of_faithful
    B z hc₀ hE hphysical hfisher hfaithful
  convert h using 1
  field_simp [hC.ne', hL.ne']

end Reporter

end

end RHTower
