import GaloisForLFunctions.HTGeometry.EulerQGammaLocalRenormBound

/-!
# Normal convergence of the renormalised Euler q-Gamma product

The genus-one renormalisation subtracts the first-activation counterterm, leaving a local factor
that deviates from `1` by `O(q²) + O(q^{2+Re s}) + O(q^{2(1+Re s)})`.  Over the primes with
`q_p = p^{-σ}` all three prime sums converge exactly when `Re s > 1/(2σ) − 1`, so the renormalised
product converges absolutely there.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

noncomputable section

/-! ## Prime power sums -/

theorem summable_prime_rpow_neg {t : ℝ} (ht : 1 < t) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-t)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ t)⁻¹) := Real.summable_nat_rpow_inv.mpr ht
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ (-t)) := by
    refine h.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  exact h2.comp_injective Nat.Primes.coe_nat_injective

theorem eqgNome_rpow (σ : EulerSigma) (p : Nat.Primes) (t : ℝ) :
    (eqgNome σ p).val ^ t = ((p : ℕ) : ℝ) ^ (-(σ.val * t)) := by
  rw [eqgNome_val, eqgQ, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem eqgNome_sq (σ : EulerSigma) (p : Nat.Primes) :
    (eqgNome σ p).val ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * σ.val)) := by
  have hpos : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [eqgNome_val, eqgQ, ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-σ.val)) 2,
    ← Real.rpow_mul hpos]
  congr 1
  push_cast
  ring

theorem eqgNome_le_half (σ : EulerSigma) (p : Nat.Primes) : (eqgNome σ p).val ≤ 1 / 2 :=
  eqgQ_le_half σ p.2.two_le

/-! ## The three exponents -/

/-- The exponent controlling the shifted local scale `q^{1+Re s}`. -/
def eqgShiftExponent (σ : EulerSigma) (s : ℂ) : ℝ := σ.val * (1 + s.re)

theorem half_lt_eqgShiftExponent (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) : 1 / 2 < eqgShiftExponent σ s := by
  have hσ : (0 : ℝ) < σ.val := σ.pos
  have h2σ : (0 : ℝ) < 2 * σ.val := by linarith
  rw [eqgShiftExponent]
  have hlt : 1 / (2 * σ.val) < 1 + s.re := by linarith
  have := mul_lt_mul_of_pos_left hlt hσ
  rw [mul_one_div] at this
  have hcancel : σ.val / (2 * σ.val) = 1 / 2 := by
    field_simp
  rw [hcancel] at this
  exact this

theorem summable_prime_sq (σ : EulerSigma) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * σ.val))) := by
  refine summable_prime_rpow_neg ?_
  have := σ.one_lt
  linarith

theorem summable_prime_shift_sq (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * eqgShiftExponent σ s))) := by
  refine summable_prime_rpow_neg ?_
  have := half_lt_eqgShiftExponent σ hs
  linarith

theorem summable_prime_shift_mul (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) :
    Summable (fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-(eqgShiftExponent σ s + σ.val))) := by
  refine summable_prime_rpow_neg ?_
  have h1 := half_lt_eqgShiftExponent σ hs
  have h2 := σ.one_lt
  linarith

/-! ## The three majorants -/

def eqgPowerMajor (σ : EulerSigma) (s : ℂ) (p : Nat.Primes) : ℝ :=
  Real.exp (‖s‖ / 2) * (2 * ‖s‖ * ((p : ℕ) : ℝ) ^ (-(2 * σ.val)))

def eqgNumerMajor (σ : EulerSigma) (p : Nat.Primes) : ℝ :=
  (3 * Real.exp 2 + genusOneBoundConst) * ((p : ℕ) : ℝ) ^ (-(2 * σ.val))

def eqgDenomMajor (σ : EulerSigma) (s : ℂ) (p : Nat.Primes) : ℝ :=
  3 * Real.exp 2 * ((p : ℕ) : ℝ) ^ (-(eqgShiftExponent σ s + σ.val))
    + genusOneBoundConst * ((p : ℕ) : ℝ) ^ (-(2 * eqgShiftExponent σ s))

theorem eqgPowerMajor_nonneg (σ : EulerSigma) (s : ℂ) (p : Nat.Primes) :
    0 ≤ eqgPowerMajor σ s p := by
  rw [eqgPowerMajor]
  have := Real.rpow_pos_of_pos (show (0 : ℝ) < ((p : ℕ) : ℝ) by exact_mod_cast p.2.pos)
    (-(2 * σ.val))
  positivity

theorem eqgNumerMajor_nonneg (σ : EulerSigma) (p : Nat.Primes) : 0 ≤ eqgNumerMajor σ p := by
  rw [eqgNumerMajor]
  have hr := Real.rpow_pos_of_pos (show (0 : ℝ) < ((p : ℕ) : ℝ) by exact_mod_cast p.2.pos)
    (-(2 * σ.val))
  have hg := genusOneBoundConst_pos
  have he := Real.exp_pos 2
  positivity

theorem eqgDenomMajor_nonneg (σ : EulerSigma) (s : ℂ) (p : Nat.Primes) :
    0 ≤ eqgDenomMajor σ s p := by
  rw [eqgDenomMajor]
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have h1 := Real.rpow_pos_of_pos hp (-(eqgShiftExponent σ s + σ.val))
  have h2 := Real.rpow_pos_of_pos hp (-(2 * eqgShiftExponent σ s))
  have hg := genusOneBoundConst_pos
  have he := Real.exp_pos 2
  positivity

/-! ## The local deviations -/

theorem shift_re (σ : EulerSigma) (s : ℂ) (p : Nat.Primes) :
    (eqgNome σ p).val ^ ((1 + s).re) = ((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s) := by
  have hre : (1 + s).re = 1 + s.re := by simp
  rw [eqgNome_rpow, eqgShiftExponent, hre]

theorem norm_eqgPowerFactor_prime_le (σ : EulerSigma) (s : ℂ) (p : Nat.Primes) :
    ‖eqgPowerFactor (eqgNome σ p) s - 1‖ ≤ eqgPowerMajor σ s p := by
  have hq := eqgNome_le_half σ p
  have hbase := norm_eqgPowerFactor_sub_one_le (eqgNome σ p) hq s
  have hsq : (eqgNome σ p).val ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * σ.val)) := eqgNome_sq σ p
  have hqpos : (0 : ℝ) < (eqgNome σ p).val := (eqgNome σ p).pos
  have hsmall : (eqgNome σ p).val ^ 2 ≤ 1 / 4 := by nlinarith
  have hmono : Real.exp (2 * ‖s‖ * (eqgNome σ p).val ^ 2) ≤ Real.exp (‖s‖ / 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [norm_nonneg s]
  rw [eqgPowerMajor, ← hsq]
  refine le_trans hbase ?_
  refine mul_le_mul_of_nonneg_right hmono ?_
  positivity

theorem norm_eqgNumerFactor_prime_le (σ : EulerSigma) (p : Nat.Primes) :
    ‖eqgNumerFactor (eqgNome σ p) - 1‖ ≤ eqgNumerMajor σ p := by
  have hq := eqgNome_le_half σ p
  have hone : (eqgNome σ p).val ^ ((1 : ℂ).re) = (eqgNome σ p).val := by
    simp [Real.rpow_one]
  have hz : (eqgNome σ p).val ^ ((1 : ℂ).re) ≤ 1 / 2 := by
    rw [hone]
    exact hq
  have h := norm_eqgRenormPochhammer_sub_one_le (eqgNome σ p) hq hz
  rw [eqgNumerFactor_eq]
  refine le_trans h ?_
  rw [hone, eqgNumerMajor, ← eqgNome_sq σ p]
  exact le_of_eq (by ring)

theorem norm_eqgDenomFactorRenorm_prime_le (σ : EulerSigma) (s : ℂ) (p : Nat.Primes)
    (hz : ((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s) ≤ 1 / 2) :
    ‖eqgDenomFactorRenorm (eqgNome σ p) s - 1‖ ≤ eqgDenomMajor σ s p := by
  have hq := eqgNome_le_half σ p
  have hre : (eqgNome σ p).val ^ ((1 + s).re) = ((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s) :=
    shift_re σ s p
  have hz' : (eqgNome σ p).val ^ ((1 + s).re) ≤ 1 / 2 := by
    rw [hre]
    exact hz
  have h := norm_eqgRenormPochhammer_sub_one_le (eqgNome σ p) hq hz'
  rw [eqgDenomFactorRenorm_eq]
  refine le_trans h ?_
  rw [hre, eqgDenomMajor]
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hmul : ((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s) * (eqgNome σ p).val
      = ((p : ℕ) : ℝ) ^ (-(eqgShiftExponent σ s + σ.val)) := by
    rw [eqgNome_val, eqgQ, ← Real.rpow_add hp]
    congr 1
    ring
  have hsq : (((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s)) ^ 2
      = ((p : ℕ) : ℝ) ^ (-(2 * eqgShiftExponent σ s)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp.le]
    congr 1
    push_cast
    ring
  rw [hmul, hsq]

/-! ## Normal convergence over the primes -/

theorem composite_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha1 : a ≤ 1) (_hb1 : b ≤ 1) (hc1 : 2 * c ≤ 1) :
    (a + b + a * b) + 2 * c + (a + b + a * b) * (2 * c) ≤ 4 * (a + b + 2 * c) := by
  have hab : a * b ≤ b := by nlinarith
  have hTnn : 0 ≤ a + b + a * b := by nlinarith
  have hTd : (a + b + a * b) * (2 * c) ≤ (a + b + a * b) * 1 :=
    mul_le_mul_of_nonneg_left hc1 hTnn
  linarith

theorem one_add_mem_qHalfPlane (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) : 1 + s ∈ qHalfPlane := by
  have hσ : (0 : ℝ) < 2 * σ.val := by
    have := σ.pos
    linarith
  have hpos : 0 < 1 / (2 * σ.val) := by positivity
  show 0 < (1 + s).re
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem summable_eqgPowerMajor (σ : EulerSigma) (s : ℂ) : Summable (eqgPowerMajor σ s) := by
  have h := ((summable_prime_sq σ).mul_left (2 * ‖s‖)).mul_left (Real.exp (‖s‖ / 2))
  refine h.congr fun p => ?_
  rw [eqgPowerMajor]

theorem summable_eqgNumerMajor (σ : EulerSigma) : Summable (eqgNumerMajor σ) := by
  have h := (summable_prime_sq σ).mul_left (3 * Real.exp 2 + genusOneBoundConst)
  refine h.congr fun p => ?_
  rw [eqgNumerMajor]

theorem summable_eqgDenomMajor (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) : Summable (eqgDenomMajor σ s) := by
  have h1 := (summable_prime_shift_mul σ hs).mul_left (3 * Real.exp 2)
  have h2 := (summable_prime_shift_sq σ hs).mul_left genusOneBoundConst
  refine (h1.add h2).congr fun p => ?_
  rw [eqgDenomMajor]

theorem eventually_shift_le_half (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) :
    ∀ᶠ p : Nat.Primes in cofinite, ((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s) ≤ 1 / 2 := by
  have h := (summable_prime_shift_sq σ hs).tendsto_cofinite_zero
  have h2 : ∀ᶠ p : Nat.Primes in cofinite,
      ((p : ℕ) : ℝ) ^ (-(2 * eqgShiftExponent σ s)) < 1 / 4 :=
    h.eventually_lt_const (by norm_num)
  filter_upwards [h2] with p hp
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hsq : (((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s)) ^ 2
      = ((p : ℕ) : ℝ) ^ (-(2 * eqgShiftExponent σ s)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hposr : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s) := Real.rpow_pos_of_pos hp0 _
  nlinarith

/-- **Normal convergence.**  The renormalised local factors differ from `1` by an absolutely
summable family on the half plane `Re s > 1/(2σ) − 1`. -/
theorem summable_eqgRenormLocal_sub_one (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) :
    Summable (fun p : Nat.Primes => eqgRenormLocal (eqgNome σ p) s - 1) := by
  have hhalf := one_add_mem_qHalfPlane σ hs
  have hA := summable_eqgPowerMajor σ s
  have hB := summable_eqgNumerMajor σ
  have hC := summable_eqgDenomMajor σ hs
  have hgsum : Summable (fun p : Nat.Primes =>
      4 * (eqgPowerMajor σ s p + eqgNumerMajor σ p + 2 * eqgDenomMajor σ s p)) :=
    ((hA.add hB).add (hC.mul_left 2)).mul_left 4
  refine Summable.of_norm_bounded_eventually hgsum ?_
  have hev1 := eventually_shift_le_half σ hs
  have hev2 : ∀ᶠ p : Nat.Primes in cofinite, eqgPowerMajor σ s p ≤ 1 :=
    (hA.tendsto_cofinite_zero.eventually_lt_const (by norm_num)).mono fun p h => h.le
  have hev3 : ∀ᶠ p : Nat.Primes in cofinite, eqgNumerMajor σ p ≤ 1 :=
    (hB.tendsto_cofinite_zero.eventually_lt_const (by norm_num)).mono fun p h => h.le
  have hev4 : ∀ᶠ p : Nat.Primes in cofinite, 2 * eqgDenomMajor σ s p ≤ 1 := by
    have := (hC.tendsto_cofinite_zero.eventually_lt_const
      (show (0 : ℝ) < 1 / 2 by norm_num))
    exact this.mono fun p h => by linarith
  filter_upwards [hev1, hev2, hev3, hev4] with p h1 h2 h3 h4
  have hc2 : eqgDenomMajor σ s p ≤ 1 / 2 := by linarith
  have hbound := norm_eqgRenormLocal_sub_one_le (eqgNome σ p) hhalf
    (norm_eqgPowerFactor_prime_le σ s p) (norm_eqgNumerFactor_prime_le σ p)
    (norm_eqgDenomFactorRenorm_prime_le σ s p h1) hc2
  refine le_trans hbound ?_
  exact composite_le (eqgPowerMajor_nonneg σ s p) (eqgNumerMajor_nonneg σ p)
    (eqgDenomMajor_nonneg σ s p) h2 h3 h4

/-- **Theorem 9.1, convergence clause.**  The genus-one renormalised Euler q-Gamma product
converges on the half plane `Re s > 1/(2σ) − 1`. -/
theorem multipliable_eqgRenormLocal (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) :
    Multipliable (fun p : Nat.Primes => eqgRenormLocal (eqgNome σ p) s) := by
  have hsum := summable_eqgRenormLocal_sub_one σ hs
  have hmul := Complex.multipliable_one_add_of_summable
    (f := fun p : Nat.Primes => eqgRenormLocal (eqgNome σ p) s - 1) hsum
  refine hmul.congr fun p => ?_
  ring

/-! ## Zero-freeness -/

theorem eqgRenormLocal_ne_zero (q : RealEulerNome) {s : ℂ} (hs : 1 + s ∈ qHalfPlane) :
    eqgRenormLocal q s ≠ 0 := by
  rw [eqgRenormLocal]
  exact mul_ne_zero (qGammaOn_ne_zero q hs) (Complex.exp_ne_zero _)

/-- **Theorem 9.1, zero-free clause.**  The genus-one renormalised Euler q-Gamma product has no
zero on the half plane `Re s > 1/(2σ) − 1`. -/
theorem eqgRenormProduct_ne_zero (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) :
    (∏' p : Nat.Primes, eqgRenormLocal (eqgNome σ p) s) ≠ 0 := by
  have hhalf := one_add_mem_qHalfPlane σ hs
  have hval : (∏' p : Nat.Primes, eqgRenormLocal (eqgNome σ p) s)
      = ∏' p : Nat.Primes, (1 + (eqgRenormLocal (eqgNome σ p) s - 1)) := by
    refine tprod_congr fun p => ?_
    ring
  rw [hval]
  refine tprod_one_add_ne_zero_of_summable ?_ ?_
  · intro p
    have hne : eqgRenormLocal (eqgNome σ p) s ≠ 0 := eqgRenormLocal_ne_zero (eqgNome σ p) hhalf
    intro h0
    apply hne
    have : (1 : ℂ) + (eqgRenormLocal (eqgNome σ p) s - 1) = eqgRenormLocal (eqgNome σ p) s := by
      ring
    rw [this] at h0
    exact h0
  · exact (summable_eqgRenormLocal_sub_one σ hs).norm

/-- **Theorem 9.1, analytic half.**  On the half plane `Re s > 1/(2σ) − 1` the genus-one
renormalised Euler q-Gamma product converges and is zero-free. -/
theorem eqgRenormProduct_multipliable_and_ne_zero (σ : EulerSigma) {s : ℂ}
    (hs : 1 / (2 * σ.val) - 1 < s.re) :
    Multipliable (fun p : Nat.Primes => eqgRenormLocal (eqgNome σ p) s)
      ∧ (∏' p : Nat.Primes, eqgRenormLocal (eqgNome σ p) s) ≠ 0 :=
  ⟨multipliable_eqgRenormLocal σ hs, eqgRenormProduct_ne_zero σ hs⟩

/-! ## Majorants at a fixed shift exponent -/

def eqgDenomMajorAt (σ : EulerSigma) (w : ℝ) (p : Nat.Primes) : ℝ :=
  3 * Real.exp 2 * ((p : ℕ) : ℝ) ^ (-(w + σ.val))
    + genusOneBoundConst * ((p : ℕ) : ℝ) ^ (-(2 * w))

theorem eqgDenomMajor_eq_at (σ : EulerSigma) (s : ℂ) (p : Nat.Primes) :
    eqgDenomMajor σ s p = eqgDenomMajorAt σ (eqgShiftExponent σ s) p := rfl

theorem rpow_neg_le_of_le {p : Nat.Primes} {a b : ℝ} (hab : b ≤ a) :
    ((p : ℕ) : ℝ) ^ (-a) ≤ ((p : ℕ) : ℝ) ^ (-b) := by
  have hp : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    have := p.2.two_le
    exact_mod_cast Nat.one_le_of_lt (by omega : 1 < (p : ℕ))
  exact Real.rpow_le_rpow_of_exponent_le hp (by linarith)

theorem eqgDenomMajorAt_antitone (σ : EulerSigma) {w w' : ℝ} (h : w' ≤ w) (p : Nat.Primes) :
    eqgDenomMajorAt σ w p ≤ eqgDenomMajorAt σ w' p := by
  have h1 : ((p : ℕ) : ℝ) ^ (-(w + σ.val)) ≤ ((p : ℕ) : ℝ) ^ (-(w' + σ.val)) :=
    rpow_neg_le_of_le (by linarith)
  have h2 : ((p : ℕ) : ℝ) ^ (-(2 * w)) ≤ ((p : ℕ) : ℝ) ^ (-(2 * w')) :=
    rpow_neg_le_of_le (by linarith)
  have he : (0 : ℝ) ≤ 3 * Real.exp 2 := by
    have := Real.exp_pos 2
    linarith
  have hg : (0 : ℝ) ≤ genusOneBoundConst := genusOneBoundConst_pos.le
  rw [eqgDenomMajorAt, eqgDenomMajorAt]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 he) (mul_le_mul_of_nonneg_left h2 hg)

def eqgPowerMajorAt (σ : EulerSigma) (M : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (M / 2) * (2 * M * ((p : ℕ) : ℝ) ^ (-(2 * σ.val)))

theorem eqgPowerMajor_le_at (σ : EulerSigma) {s : ℂ} {M : ℝ} (hM : ‖s‖ ≤ M) (p : Nat.Primes) :
    eqgPowerMajor σ s p ≤ eqgPowerMajorAt σ M p := by
  have hr : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-(2 * σ.val)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hs0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  rw [eqgPowerMajor, eqgPowerMajorAt]
  have hexp : Real.exp (‖s‖ / 2) ≤ Real.exp (M / 2) := Real.exp_le_exp.mpr (by linarith)
  have hmul : 2 * ‖s‖ * ((p : ℕ) : ℝ) ^ (-(2 * σ.val))
      ≤ 2 * M * ((p : ℕ) : ℝ) ^ (-(2 * σ.val)) := by
    have : 2 * ‖s‖ ≤ 2 * M := by linarith
    exact mul_le_mul_of_nonneg_right this hr.le
  have hnn : (0 : ℝ) ≤ 2 * ‖s‖ * ((p : ℕ) : ℝ) ^ (-(2 * σ.val)) := by positivity
  exact mul_le_mul hexp hmul hnn (Real.exp_pos _).le

theorem summable_eqgPowerMajorAt (σ : EulerSigma) (M : ℝ) :
    Summable (eqgPowerMajorAt σ M) := by
  have h := ((summable_prime_sq σ).mul_left (2 * M)).mul_left (Real.exp (M / 2))
  refine h.congr fun p => ?_
  rw [eqgPowerMajorAt]

theorem summable_eqgDenomMajorAt (σ : EulerSigma) {w : ℝ} (hw : 1 / 2 < w) :
    Summable (eqgDenomMajorAt σ w) := by
  have hσ := σ.one_lt
  have h1 := ((summable_prime_rpow_neg (t := w + σ.val) (by linarith)).mul_left (3 * Real.exp 2))
  have h2 := ((summable_prime_rpow_neg (t := 2 * w) (by linarith)).mul_left genusOneBoundConst)
  refine (h1.add h2).congr fun p => ?_
  rw [eqgDenomMajorAt]

theorem eventually_prime_rpow_le_half {w : ℝ} (hw : 1 / 2 < w) :
    ∀ᶠ p : Nat.Primes in cofinite, ((p : ℕ) : ℝ) ^ (-w) ≤ 1 / 2 := by
  have hsum : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * w))) :=
    summable_prime_rpow_neg (by linarith)
  have h2 : ∀ᶠ p : Nat.Primes in cofinite, ((p : ℕ) : ℝ) ^ (-(2 * w)) < 1 / 4 :=
    hsum.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  filter_upwards [h2] with p hp
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hsq : (((p : ℕ) : ℝ) ^ (-w)) ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * w)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hposr : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-w) := Real.rpow_pos_of_pos hp0 _
  nlinarith

end

end GaloisForLFunctions.HTGeometry
