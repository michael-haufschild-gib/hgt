import GaloisForLFunctions.RHTower.PMRamanujanBandMellin
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Actual prime factors and analytic correction for the band Mellin transform

The correction is tied to the literal Ramanujan prime coefficient and divisor
symbol. Its prime product converges locally uniformly around both critical
lines, is holomorphic in the scale variable, and stays nonzero near each
critical diagonal point. The infinite arithmetic-series identity and the
complete signed-band energy estimate are not asserted here.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower


/-- Exact local correction after the two zeta factors have been extracted. -/
def pmRamanujanBandEulerFactor (ε : ℝ) (z s : ℂ) (p : ℕ) : ℂ :=
  let a : ℂ := ((p : ℝ)^(-1-ε) : ℝ)
  let b : ℂ := (p : ℂ)^(s-z-1)
  let c : ℂ := (p : ℂ)^(-z)
  1+(b-a)*(c-b)/((1-a)*(1-c))

private theorem pmbe_factor_algebra {a b c : ℂ} (ha : 1-a ≠ 0) (hc : 1-c ≠ 0) :
    1+(b-a)*(c-b)/((1-a)*(1-c)) =
      (1-a+b-c)*(1-b)/((1-a)*(1-c)) := by
  field_simp
  ring

private theorem pmbe_a_bounds {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ (p : ℝ)^(-1-ε) ∧ (p : ℝ)^(-1-ε) ≤ (p : ℝ)^(-1 : ℝ) ∧
      (p : ℝ)^(-1-ε) ≤ 1/2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hpow := Real.rpow_le_rpow_of_exponent_le hp1 (show -1-ε ≤ (-1 : ℝ) by linarith)
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg p) _, hpow, hpow.trans ?_⟩
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ)<2)
    (show (2 : ℝ) ≤ p by exact_mod_cast hp) (by norm_num : (-1 : ℝ) ≤ 0)
  simpa only [Real.rpow_neg_one, inv_eq_one_div] using h

private theorem pmbe_c_bound {z : ℂ} (hz : 3/8 ≤ z.re) {p : ℕ} (hp : 2 ≤ p) :
    ‖(p : ℂ)^(-z)‖ ≤ (p : ℝ)^(-(3/8) : ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < p),
    Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (by omega : 1 ≤ p)) (by linarith)

private theorem pmbe_b_bound {z s : ℂ} (hz : 3/8 ≤ z.re) (hs : s.re ≤ 9/16)
    {p : ℕ} (hp : 2 ≤ p) :
    ‖(p : ℂ)^(s-z-1)‖ ≤ (p : ℝ)^(-(13/16) : ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < p)]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ p))
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- A summable majorant uniform on an open neighborhood of the two critical lines. It controls the Euler correction, not the physical source energy. -/
theorem norm_pmRamanujanBandEulerFactor_sub_one_le {ε : ℝ} (hε : 0 ≤ ε)
    {z s : ℂ} (hz : 3/8 ≤ z.re) (hs : s.re ≤ 9/16) {p : ℕ} (hp : 2 ≤ p) :
    ‖pmRamanujanBandEulerFactor ε z s p - 1‖ ≤
      (8/(1-(2 : ℝ)^(-(3/8) : ℝ))) * (p : ℝ)^(-(19/16) : ℝ) := by
  let a : ℂ := ((p : ℝ)^(-1-ε) : ℝ)
  let b : ℂ := (p : ℂ)^(s-z-1)
  let c : ℂ := (p : ℂ)^(-z)
  let A : ℝ := 1-(2 : ℝ)^(-(3/8) : ℝ)
  have hA : 0 < A := sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ)<2) (by norm_num : (-(3/8) : ℝ)<0))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hba := pmbe_a_bounds hε hp
  have ha : ‖a‖ = (p : ℝ)^(-1-ε) := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hba.1]
  have hab : ‖a‖ ≤ (p : ℝ)^(-(13/16) : ℝ) := by
    rw [ha]
    exact hba.2.1.trans (Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num))
  have hb : ‖b‖ ≤ (p : ℝ)^(-(13/16) : ℝ) := pmbe_b_bound hz hs hp
  have hbc : ‖b‖ ≤ (p : ℝ)^(-(3/8) : ℝ) :=
    hb.trans (Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num))
  have hc : ‖c‖ ≤ (p : ℝ)^(-(3/8) : ℝ) := pmbe_c_bound hz hp
  have hc2 : ‖c‖ ≤ (2 : ℝ)^(-(3/8) : ℝ) := hc.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num)
      (show (2 : ℝ) ≤ p by exact_mod_cast hp) (by norm_num))
  have hdena : (1/2 : ℝ) ≤ ‖1-a‖ := by
    have h := norm_sub_norm_le (1 : ℂ) a
    rw [norm_one, ha] at h
    linarith [hba.2.2]
  have hdenc : A ≤ ‖1-c‖ := by
    have h := norm_sub_norm_le (1 : ℂ) c
    rw [norm_one] at h
    dsimp only [A]
    linarith
  have hden : (1/2)*A ≤ ‖(1-a)*(1-c)‖ := by
    rw [norm_mul]
    exact mul_le_mul hdena hdenc hA.le (norm_nonneg _)
  have hnum : ‖(b-a)*(c-b)‖ ≤ 4*(p : ℝ)^(-(19/16) : ℝ) := by
    rw [norm_mul]
    have h1 : ‖b-a‖ ≤ 2*(p : ℝ)^(-(13/16) : ℝ) := by
      have h := norm_sub_le b a
      linarith
    have h2 : ‖c-b‖ ≤ 2*(p : ℝ)^(-(3/8) : ℝ) := by
      have h := norm_sub_le c b
      linarith
    calc
      _ ≤ (2*(p : ℝ)^(-(13/16) : ℝ))*(2*(p : ℝ)^(-(3/8) : ℝ)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show (2*(p : ℝ)^(-(13/16) : ℝ))*(2*(p : ℝ)^(-(3/8) : ℝ)) =
          4*((p : ℝ)^(-(13/16) : ℝ)*(p : ℝ)^(-(3/8) : ℝ)) by ring,
          ← Real.rpow_add hp0]
        norm_num
  have he : pmRamanujanBandEulerFactor ε z s p-1 =
      (b-a)*(c-b)/((1-a)*(1-c)) := by
    dsimp only [pmRamanujanBandEulerFactor, a, b, c]
    ring
  rw [he, norm_div]
  calc
    _ ≤ (4*(p : ℝ)^(-(19/16) : ℝ))/‖(1-a)*(1-c)‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (4*(p : ℝ)^(-(19/16) : ℝ))/((1/2)*A) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by dsimp only [A]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem summable_norm_pmRamanujanBandEulerFactor_sub_one {ε : ℝ} (hε : 0 ≤ ε)
    {z s : ℂ} (hz : 3/8 ≤ z.re) (hs : s.re ≤ 9/16) :
    Summable (fun p : Nat.Primes => ‖pmRamanujanBandEulerFactor ε z s p - 1‖) := by
  have hpow : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-(19/16) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(19/16) : ℝ) < -1)).subtype Nat.Prime
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_pmRamanujanBandEulerFactor_sub_one_le hε hz hs p.property.two_le)
    (hpow.mul_left (8/(1-(2 : ℝ)^(-(3/8) : ℝ))))

theorem multipliable_pmRamanujanBandEulerFactor {ε : ℝ} (hε : 0 ≤ ε)
    {z s : ℂ} (hz : 3/8 ≤ z.re) (hs : s.re ≤ 9/16) :
    Multipliable (fun p : Nat.Primes => pmRamanujanBandEulerFactor ε z s p) := by
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable
    (summable_norm_pmRamanujanBandEulerFactor_sub_one hε hz hs)

private theorem pmbe_c_lt_one {z : ℂ} (hz : 0 < z.re) {p : ℕ} (hp : 2 ≤ p) :
    ‖(p : ℂ)^(-z)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < p),
    Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (by omega : 1 < p)) (neg_neg_of_pos hz)

theorem pmRamanujanBandEulerFactor_diagonal_ne_zero {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : 0 < z.re) {p : ℕ} (hp : 2 ≤ p) :
    pmRamanujanBandEulerFactor ε z z p ≠ 0 := by
  let a : ℝ := (p : ℝ)^(-1-ε)
  let b : ℝ := (p : ℝ)^(-1 : ℝ)
  let c : ℂ := (p : ℂ)^(-z)
  have ha := pmbe_a_bounds hε hp
  have hb : b ≤ 1/2 := by
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ)<2)
      (show (2 : ℝ) ≤ p by exact_mod_cast hp) (by norm_num : (-1 : ℝ) ≤ 0)
    simpa only [b, Real.rpow_neg_one, inv_eq_one_div] using h
  have hc : ‖c‖ < 1 := pmbe_c_lt_one hz hp
  have hca : (1 : ℂ)-(a : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith [ha.2.2]
  have hcb : (1 : ℂ)-(b : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith
  have hcc : (1 : ℂ)-c ≠ 0 := by
    intro h
    have he : c = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hc
    exact (lt_irrefl _ hc)
  have hn : (1 : ℂ)-(a : ℂ)+(b : ℂ)-c ≠ 0 := by
    intro h
    have he : c = ((1-a+b : ℝ) : ℂ) := by
      rw [← sub_eq_zero] at h
      push_cast
      linear_combination -h
    have hab : 1 ≤ 1-a+b := by linarith [ha.2.1]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hc
    linarith
  have he : (p : ℂ)^(z-z-1) = (b : ℂ) := by
    simp only [sub_self, zero_sub, Complex.cpow_neg_one, b, Real.rpow_neg_one,
      Complex.ofReal_inv, Complex.ofReal_natCast]
  dsimp only [pmRamanujanBandEulerFactor]
  rw [he, pmbe_factor_algebra hca hcc]
  exact div_ne_zero (mul_ne_zero hn hcb) (mul_ne_zero hca hcc)

/-- The normally summable correction to the two zeta factors. -/
def pmRamanujanBandEulerCorrection (ε : ℝ) (z s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, pmRamanujanBandEulerFactor ε z s p

theorem pmRamanujanBandEulerCorrection_diagonal_ne_zero {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : z.re = 1/2) :
    pmRamanujanBandEulerCorrection ε z z ≠ 0 := by
  have hsum := summable_norm_pmRamanujanBandEulerFactor_sub_one hε
    (show 3/8 ≤ z.re by rw [hz]; norm_num)
    (show z.re ≤ 9/16 by rw [hz]; norm_num)
  have hn (p : Nat.Primes) : 1+(pmRamanujanBandEulerFactor ε z z p-1) ≠ 0 := by
    simpa only [add_sub_cancel] using pmRamanujanBandEulerFactor_diagonal_ne_zero hε
      (show 0 < z.re by rw [hz]; norm_num) p.property.two_le
  simpa only [pmRamanujanBandEulerCorrection, add_sub_cancel] using
    tprod_one_add_ne_zero_of_summable hn hsum

/-- The local correction is tied to the literal coefficient and divisor symbol. -/
theorem pmRamanujanBandEulerFactor_prime_identity {ε : ℝ} (hε : 0 < ε)
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : 0 < z.re) (s : ℂ) :
    (pmPowerDampedDivisorDensity ε + pmPowerDampedRamanujanWeight ε p *
      pmRamanujanMellinSymbol p s * (p : ℂ)^((ε : ℂ)+s-z)) *
        (1-(p : ℂ)^(s-z-1)) =
      pmPowerDampedDivisorDensity ε * (1-(p : ℂ)^(-z)) *
        pmRamanujanBandEulerFactor ε z s p := by
  let d : ℂ := ((p : ℝ)^(1+ε) : ℝ)
  let a : ℂ := ((p : ℝ)^(-1-ε) : ℝ)
  let b : ℂ := (p : ℂ)^(s-z-1)
  let c : ℂ := (p : ℂ)^(-z)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd0 : d ≠ 0 := by
    dsimp only [d]
    exact_mod_cast (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.pos : (0 : ℝ) < p) (1+ε)).ne'
  have hd1 : d-1 ≠ 0 := by
    have h : 1 < (p : ℝ)^(1+ε) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    dsimp only [d]
    exact_mod_cast (sub_pos.mpr h).ne'
  have hd : d = (p : ℂ)^(1+(ε : ℂ)) := by
    dsimp only [d]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg p)]
    push_cast
    rfl
  have ha : a = d⁻¹ := by
    dsimp only [a, d]
    rw [show -1-ε = -(1+ε) by ring, Real.rpow_neg (Nat.cast_nonneg p),
      Complex.ofReal_inv]
  have ha0 : 1-a ≠ 0 := by rw [ha]; field_simp; exact div_ne_zero hd1 hd0
  have hc0 : 1-c ≠ 0 := by
    intro h
    have hlt := pmbe_c_lt_one hz hp.two_le
    have he : c = 1 := (sub_eq_zero.mp h).symm
    change ‖c‖ < 1 at hlt
    rw [he, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hv : (p : ℂ)^((ε : ℂ)+s-z) = d*b := by
    rw [hd, ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have huv : ((p : ℂ)^(1-s)-1)*(p : ℂ)^((ε : ℂ)+s-z) = d*(c-b) := by
    rw [sub_mul, ← Complex.cpow_add _ _ hp0, one_mul, hv]
    have he : (p : ℂ)^(1-s+((ε : ℂ)+s-z)) = d*c := by
      rw [hd, ← Complex.cpow_add _ _ hp0]
      congr 1
      ring
    rw [he]
    ring
  have hw := pmPowerDampedRamanujanWeight_prime_mul hε hp hp.not_dvd_one
  rw [mul_one, pmPowerDampedRamanujanWeight_one hε] at hw
  have ht : pmPowerDampedRamanujanWeight ε p * pmRamanujanMellinSymbol p s *
      (p : ℂ)^((ε : ℂ)+s-z) = -pmPowerDampedDivisorDensity ε * (c-b)/(1-a) := by
    rw [hw, pmRamanujanMellinSymbol_prime hp]
    push_cast
    change -pmPowerDampedDivisorDensity ε/(d-1) * _ * _ = _
    rw [show -pmPowerDampedDivisorDensity ε/(d-1) * ((p : ℂ)^(1-s)-1) *
        (p : ℂ)^((ε : ℂ)+s-z) =
      -pmPowerDampedDivisorDensity ε *
        (((p : ℂ)^(1-s)-1)*(p : ℂ)^((ε : ℂ)+s-z))/(d-1) by ring,
      huv, ha]
    field_simp
  rw [ht]
  change (pmPowerDampedDivisorDensity ε + -pmPowerDampedDivisorDensity ε *
    (c-b)/(1-a))*(1-b) = pmPowerDampedDivisorDensity ε*(1-c)*
      (1+(b-a)*(c-b)/((1-a)*(1-c)))
  rw [pmbe_factor_algebra ha0 hc0]
  field_simp
  ring

/-- An open neighborhood of both critical lines. -/
def pmRamanujanBandEulerDomain : Set (ℂ × ℂ) :=
  {w | 3/8 < w.1.re ∧ w.2.re < 9/16}

theorem isOpen_pmRamanujanBandEulerDomain : IsOpen pmRamanujanBandEulerDomain :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
    (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const)

theorem differentiableOn_pmRamanujanBandEulerFactor {ε : ℝ} (hε : 0 ≤ ε)
    {p : ℕ} (hp : 2 ≤ p) :
    DifferentiableOn ℂ (fun w : ℂ × ℂ => pmRamanujanBandEulerFactor ε w.1 w.2 p)
      pmRamanujanBandEulerDomain := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hb : Differentiable ℂ (fun w : ℂ × ℂ => (p : ℂ)^(w.2-w.1-1)) :=
    ((differentiable_snd.sub differentiable_fst).sub_const 1).const_cpow (.inl hp0)
  have hc : Differentiable ℂ (fun w : ℂ × ℂ => (p : ℂ)^(-w.1)) :=
    differentiable_fst.neg.const_cpow (.inl hp0)
  have ha0 : (1 : ℂ)-((p : ℝ)^(-1-ε) : ℝ) ≠ 0 := by
    intro he
    have he' := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at he'
    linarith [(pmbe_a_bounds hε hp).2.2]
  have hc0 (w : ℂ × ℂ) (hw : w ∈ pmRamanujanBandEulerDomain) :
      (1 : ℂ)-(p : ℂ)^(-w.1) ≠ 0 := by
    intro he
    have hnorm := pmbe_c_lt_one (show 0 < w.1.re by have := hw.1; linarith) hp
    rw [← sub_eq_zero.mp he, norm_one] at hnorm
    exact lt_irrefl _ hnorm
  simp only [pmRamanujanBandEulerFactor, div_eq_mul_inv]
  exact (differentiableOn_const _).add
    (((hb.differentiableOn.sub (differentiableOn_const _)).mul
      (hc.differentiableOn.sub hb.differentiableOn)).mul
      (((differentiableOn_const _).mul
        ((differentiableOn_const _).sub hc.differentiableOn)).inv
        (fun w hw => mul_ne_zero ha0 (hc0 w hw))))

theorem hasProdLocallyUniformlyOn_pmRamanujanBandEulerFactor {ε : ℝ} (hε : 0 ≤ ε) :
    HasProdLocallyUniformlyOn
      (fun p : Nat.Primes => fun w : ℂ × ℂ => pmRamanujanBandEulerFactor ε w.1 w.2 p)
      (fun w => pmRamanujanBandEulerCorrection ε w.1 w.2) pmRamanujanBandEulerDomain := by
  have hpow : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-(19/16) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(19/16) : ℝ) < -1)).subtype Nat.Prime
  have h := Summable.hasProdLocallyUniformlyOn_one_add isOpen_pmRamanujanBandEulerDomain
    (hpow.mul_left (8/(1-(2 : ℝ)^(-(3/8) : ℝ))))
    (f := fun p : Nat.Primes => fun w : ℂ × ℂ =>
      pmRamanujanBandEulerFactor ε w.1 w.2 p - 1)
    (.of_forall (fun p w hw =>
      norm_pmRamanujanBandEulerFactor_sub_one_le hε hw.1.le hw.2.le p.property.two_le))
    (fun p => (differentiableOn_pmRamanujanBandEulerFactor hε
      p.property.two_le).continuousOn.sub continuousOn_const)
  simpa only [add_sub_cancel, pmRamanujanBandEulerCorrection] using h

theorem continuousOn_pmRamanujanBandEulerCorrection {ε : ℝ} (hε : 0 ≤ ε) :
    ContinuousOn (fun w : ℂ × ℂ => pmRamanujanBandEulerCorrection ε w.1 w.2)
      pmRamanujanBandEulerDomain := by
  apply (hasProdLocallyUniformlyOn_pmRamanujanBandEulerFactor hε).continuousOn
  exact Filter.Eventually.frequently (.of_forall fun t => by
    simpa only [Finset.prod_fn] using
      continuousOn_finsetProd t (fun p _ =>
        (differentiableOn_pmRamanujanBandEulerFactor hε p.property.two_le).continuousOn))

theorem differentiableOn_pmRamanujanBandEulerCorrection {ε : ℝ} (hε : 0 ≤ ε)
    {s : ℂ} (hs : s.re < 9/16) :
    DifferentiableOn ℂ (fun z : ℂ => pmRamanujanBandEulerCorrection ε z s)
      {z : ℂ | 3/8 < z.re} := by
  have hprod := (hasProdLocallyUniformlyOn_pmRamanujanBandEulerFactor hε).comp
    (fun z : ℂ => (z,s)) (fun z hz => ⟨hz,hs⟩)
    (continuous_id.prodMk continuous_const).continuousOn
  apply hprod.differentiableOn _ (isOpen_lt continuous_const Complex.continuous_re)
  exact .of_forall fun t => by
    simpa [Finset.prod_fn, Function.comp_def] using
      DifferentiableOn.finsetProd (u := t) (fun p _ =>
        (differentiableOn_pmRamanujanBandEulerFactor hε p.property.two_le).comp
          (differentiable_id.prodMk (differentiable_const s)).differentiableOn
          (fun z hz => ⟨hz,hs⟩))

theorem eventually_ne_zero_pmRamanujanBandEulerCorrection {ε : ℝ} (hε : 0 ≤ ε)
    {z : ℂ} (hz : z.re = 1/2) :
    ∀ᶠ w : ℂ × ℂ in 𝓝 (z,z), pmRamanujanBandEulerCorrection ε w.1 w.2 ≠ 0 := by
  have hmem : (z,z) ∈ pmRamanujanBandEulerDomain := by
    constructor <;> simp only [hz] <;> norm_num
  exact ((continuousOn_pmRamanujanBandEulerCorrection hε).continuousAt
    (isOpen_pmRamanujanBandEulerDomain.mem_nhds hmem)).eventually_ne
      (pmRamanujanBandEulerCorrection_diagonal_ne_zero hε hz)

end RHTower
