import GaloisForLFunctions.RHTower.PrimeFirstTraceGammaCofinalNormalizerFrontier

/-!
# Exact all-order Schatten wall of the cofinal Gamma Bockstein

The real representative of the singular all-prime Gamma Bockstein is the reflected Fisher
difference.  Its absolute coefficient has exact prime order `p^(-1 + |t|)`.  Consequently its
`q`-energy is summable exactly when `t = 0` or `q * (1 - |t|) > 1`.

The intersection of every prime `ell^q`, `q > 1`, therefore detects neutral grade exactly.  This
is an unconditional reader theorem.  It does not assert that an Xi landing belongs to that
intersection; constructing a source Stokes/Cartier boundary which proves such membership remains
the producer problem.
-/

namespace RHTower

noncomputable section

/-- Absolute real coefficient of the reflected-minus-forward Fisher Bockstein. -/
def primeGammaCofinalBocksteinMagnitude (t : ℝ) (p : Nat.Primes) : ℝ :=
  |primeActivationOccupancyFisherTwist (-t) p -
    primeActivationOccupancyFisherTwist t p|

/-- `q`th Schatten mass of the cofinal Gamma Bockstein coefficient. -/
def primeGammaCofinalBocksteinSchattenMass
    (q t : ℝ) (p : Nat.Primes) : ℝ :=
  primeGammaCofinalBocksteinMagnitude t p ^ q

private theorem primeActivationOccupancyFisherTwist_mono
    {a b : ℝ} (hab : a ≤ b) (p : Nat.Primes) :
    primeActivationOccupancyFisherTwist a p ≤
      primeActivationOccupancyFisherTwist b p := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hdensity : 0 ≤ primeActivationOccupancyFisherDensity p :=
    le_trans (by positivity)
      (primeActivationOccupancyFisherDensity_bounds p).1
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hp1 hab) hdensity

/-- Reflection reduces the absolute Bockstein coefficient to the positive `|t|` orientation. -/
theorem primeGammaCofinalBocksteinMagnitude_eq
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinMagnitude t p =
      primeActivationOccupancyFisherTwist |t| p -
        primeActivationOccupancyFisherTwist (-|t|) p := by
  by_cases ht : 0 ≤ t
  · have horder :
        primeActivationOccupancyFisherTwist (-t) p ≤
          primeActivationOccupancyFisherTwist t p :=
      primeActivationOccupancyFisherTwist_mono (by linarith) p
    rw [primeGammaCofinalBocksteinMagnitude, abs_of_nonpos (sub_nonpos.mpr horder),
      abs_of_nonneg ht]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have horder :
        primeActivationOccupancyFisherTwist t p ≤
          primeActivationOccupancyFisherTwist (-t) p :=
      primeActivationOccupancyFisherTwist_mono (by linarith) p
    rw [primeGammaCofinalBocksteinMagnitude, abs_of_nonneg (sub_nonneg.mpr horder),
      abs_of_nonpos ht']
    simp only [neg_neg]

/-- Positive-orientation factorization into the dominant Fisher coefficient and its reflected
character defect. -/
theorem primeGammaCofinalBocksteinMagnitude_factor
    (t : ℝ) (p : Nat.Primes) :
    primeGammaCofinalBocksteinMagnitude t p =
      primeActivationOccupancyFisherTwist |t| p *
        (1 - (p : ℝ) ^ (-2 * |t|)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpow : (p : ℝ) ^ (-|t|) =
      (p : ℝ) ^ |t| * (p : ℝ) ^ (-2 * |t|) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  rw [primeGammaCofinalBocksteinMagnitude_eq,
    primeActivationOccupancyFisherTwist,
    primeActivationOccupancyFisherTwist, hpow]
  ring

private theorem primeGammaCofinalBocksteinFactor_bounds
    (t : ℝ) (p : Nat.Primes) :
    1 - (2 : ℝ) ^ (-2 * |t|) ≤ 1 - (p : ℝ) ^ (-2 * |t|) ∧
      1 - (p : ℝ) ^ (-2 * |t|) ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
  have hponent : -2 * |t| ≤ 0 := by nlinarith [abs_nonneg t]
  have hpowle : (p : ℝ) ^ (-2 * |t|) ≤ (2 : ℝ) ^ (-2 * |t|) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 hponent
  have hpow0 : 0 ≤ (p : ℝ) ^ (-2 * |t|) := by positivity
  constructor <;> linarith

/-- Uniform prime-power comparison.  The lower constant depends on the grade but not on the
prime; it is strictly positive whenever `t ≠ 0`. -/
theorem primeGammaCofinalBocksteinMagnitude_bounds
    (t : ℝ) (p : Nat.Primes) :
    (1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|)) *
          (p : ℝ) ^ (|t| - 1) ≤
        primeGammaCofinalBocksteinMagnitude t p ∧
      primeGammaCofinalBocksteinMagnitude t p ≤
        (p : ℝ) ^ (|t| - 1) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hF := primeActivationOccupancyFisherTwist_bounds |t| p
  have hfactor := primeGammaCofinalBocksteinFactor_bounds t p
  have hfactor0 : 0 ≤ 1 - (p : ℝ) ^ (-2 * |t|) := by
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hp1
      (by nlinarith [abs_nonneg t] : -2 * |t| ≤ 0)
    linarith
  have hconst0 : 0 ≤ 1 - (2 : ℝ) ^ (-2 * |t|) := by
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
      (by nlinarith [abs_nonneg t] : -2 * |t| ≤ 0)
    linarith
  rw [primeGammaCofinalBocksteinMagnitude_factor]
  constructor
  · calc
      (1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|)) *
            (p : ℝ) ^ (|t| - 1) =
          ((1 / 4 : ℝ) * (p : ℝ) ^ (|t| - 1)) *
            (1 - (2 : ℝ) ^ (-2 * |t|)) := by ring
      _ ≤ primeActivationOccupancyFisherTwist |t| p *
            (1 - (p : ℝ) ^ (-2 * |t|)) :=
        mul_le_mul hF.1 hfactor.1 hconst0
          (le_trans (by positivity) hF.1)
  · calc
      primeActivationOccupancyFisherTwist |t| p *
            (1 - (p : ℝ) ^ (-2 * |t|)) ≤
          (p : ℝ) ^ (|t| - 1) * 1 :=
        mul_le_mul hF.2 hfactor.2 hfactor0
          (Real.rpow_nonneg hp0.le (|t| - 1))
      _ = (p : ℝ) ^ (|t| - 1) := mul_one _

private theorem primeGammaCofinalBocksteinLowerConstant_pos
    {t : ℝ} (ht : t ≠ 0) :
    0 < (1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|)) := by
  have habs : 0 < |t| := abs_pos.mpr ht
  have hpow : (2 : ℝ) ^ (-2 * |t|) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  positivity

private theorem primeGammaCofinalBocksteinSchattenMass_bounds
    {t q : ℝ} (ht : t ≠ 0) (hq : 0 < q) (p : Nat.Primes) :
    (((1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|))) ^ q) *
          (p : ℝ) ^ (q * (|t| - 1)) ≤
        primeGammaCofinalBocksteinSchattenMass q t p ∧
      primeGammaCofinalBocksteinSchattenMass q t p ≤
        (p : ℝ) ^ (q * (|t| - 1)) := by
  let c : ℝ := (1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|))
  have hc : 0 < c := primeGammaCofinalBocksteinLowerConstant_pos ht
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hmag := primeGammaCofinalBocksteinMagnitude_bounds t p
  have hmag0 : 0 ≤ primeGammaCofinalBocksteinMagnitude t p := abs_nonneg _
  have hmodel0 : 0 ≤ (p : ℝ) ^ (|t| - 1) := Real.rpow_nonneg hp0.le _
  have hpowq : ((p : ℝ) ^ (|t| - 1)) ^ q =
      (p : ℝ) ^ (q * (|t| - 1)) := by
    calc
      ((p : ℝ) ^ (|t| - 1)) ^ q =
          (p : ℝ) ^ ((|t| - 1) * q) :=
        (Real.rpow_mul hp0.le (|t| - 1) q).symm
      _ = (p : ℝ) ^ (q * (|t| - 1)) := by ring_nf
  change
    c ^ q * (p : ℝ) ^ (q * (|t| - 1)) ≤
          primeGammaCofinalBocksteinSchattenMass q t p ∧
      primeGammaCofinalBocksteinSchattenMass q t p ≤
          (p : ℝ) ^ (q * (|t| - 1))
  have hlower : c * (p : ℝ) ^ (|t| - 1) ≤
      primeGammaCofinalBocksteinMagnitude t p := by
    simpa [c, mul_assoc] using hmag.1
  constructor
  · calc
      c ^ q * (p : ℝ) ^ (q * (|t| - 1)) =
          (c * (p : ℝ) ^ (|t| - 1)) ^ q := by
        rw [Real.mul_rpow hc.le hmodel0]
        rw [hpowq]
      _ ≤ primeGammaCofinalBocksteinMagnitude t p ^ q :=
        Real.rpow_le_rpow (mul_nonneg hc.le hmodel0) hlower hq.le
  · calc
      primeGammaCofinalBocksteinMagnitude t p ^ q ≤
          ((p : ℝ) ^ (|t| - 1)) ^ q :=
        Real.rpow_le_rpow hmag0 hmag.2 hq.le
      _ = (p : ℝ) ^ (q * (|t| - 1)) := by
        exact hpowq

/-- Sharp variable-order Schatten classification of the explicit cofinal Gamma Bockstein. -/
theorem summable_primeGammaCofinalBocksteinSchattenMass_iff
    {t q : ℝ} (hq : 0 < q) :
    Summable (primeGammaCofinalBocksteinSchattenMass q t) ↔
      t = 0 ∨ 1 < q * (1 - |t|) := by
  by_cases ht : t = 0
  · subst t
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      change Summable (fun p : Nat.Primes =>
        primeGammaCofinalBocksteinMagnitude 0 p ^ q)
      have hmagzero : primeGammaCofinalBocksteinMagnitude 0 =
          fun _ : Nat.Primes => 0 := by
        funext p
        simp only [primeGammaCofinalBocksteinMagnitude, neg_zero, sub_self,
          abs_zero]
      rw [hmagzero]
      simpa only [Real.zero_rpow hq.ne'] using
        (summable_zero : Summable (fun _ : Nat.Primes => (0 : ℝ)))
  · constructor
    · intro hsum
      have hc : 0 < (1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|)) :=
        primeGammaCofinalBocksteinLowerConstant_pos ht
      have hscaled : Summable (fun p : Nat.Primes =>
          (((1 / 4 : ℝ) * (1 - (2 : ℝ) ^ (-2 * |t|))) ^ q) *
            (p : ℝ) ^ (q * (|t| - 1))) :=
        Summable.of_nonneg_of_le (fun _ => by positivity)
          (fun p => (primeGammaCofinalBocksteinSchattenMass_bounds ht hq p).1)
          hsum
      have hpow : Summable (fun p : Nat.Primes =>
          (p : ℝ) ^ (q * (|t| - 1))) :=
        (summable_mul_left_iff (Real.rpow_pos_of_pos hc q).ne').mp hscaled
      have hexp := (Nat.Primes.summable_rpow).mp hpow
      exact Or.inr (by linarith)
    · rintro (_ | horder)
      · contradiction
      · have hpow : Summable (fun p : Nat.Primes =>
            (p : ℝ) ^ (q * (|t| - 1))) :=
          (Nat.Primes.summable_rpow).2 (by linarith)
        exact Summable.of_nonneg_of_le (fun _ => by
          exact Real.rpow_nonneg (abs_nonneg _) q)
          (fun p => (primeGammaCofinalBocksteinSchattenMass_bounds ht hq p).2)
          hpow

/-- Membership in every prime `ell^q`, `q > 1`, forces and is forced by neutral grade. -/
theorem all_order_summable_primeGammaCofinalBocksteinSchattenMass_iff
    {t : ℝ} :
    (∀ q : ℝ, 1 < q →
      Summable (primeGammaCofinalBocksteinSchattenMass q t)) ↔
      t = 0 := by
  constructor
  · intro hall
    by_contra ht0
    by_cases ht : |t| < 1
    · have hu0 : 0 < 1 - |t| := by linarith
      let q : ℝ := (1 - |t|)⁻¹
      have hq1 : 1 < q := by
        dsimp [q]
        rw [one_lt_inv₀ hu0]
        linarith [abs_pos.mpr ht0]
      have hsum := hall q hq1
      have hclass :=
        (summable_primeGammaCofinalBocksteinSchattenMass_iff
          (show 0 < q by linarith)).mp hsum
      rcases hclass with hzero | hstrict
      · exact ht0 hzero
      · dsimp [q] at hstrict
        rw [inv_mul_cancel₀ hu0.ne'] at hstrict
        linarith
    · have hsum := hall 2 (by norm_num)
      have hclass :=
        (summable_primeGammaCofinalBocksteinSchattenMass_iff
          (show (0 : ℝ) < 2 by norm_num)).mp hsum
      rcases hclass with hzero | hstrict
      · exact ht0 hzero
      · have habs : 1 ≤ |t| := le_of_not_gt ht
        linarith
  · rintro rfl q hq
    exact (summable_primeGammaCofinalBocksteinSchattenMass_iff
      (by linarith)).2 (Or.inl rfl)

end

end RHTower
