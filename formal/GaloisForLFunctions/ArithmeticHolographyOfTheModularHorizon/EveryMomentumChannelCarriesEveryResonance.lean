import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinLineEigenEquation

/-!
# Every momentum channel carries every resonance

The modular image of a seed is read on horocycles in momentum channels: the `n`-th Fourier mode `e^{2πinx}`.
On the constant channel the image sum is the echo train, with Dirichlet series `Σ_c φ(c) c^{−w}`. On the channel
of momentum `n ≠ 0` the images of denominator `c` carry the Ramanujan sums `c_c(n)` (Kloosterman sums at
frequency zero), and the **Rademacher image sum** is

  `Σ_{c ≥ 1} c_c(n) c^{−w} = σ_{1−w}(n)/ζ(w)`,  `σ_{1−w}(n) = Σ_{d | n} d^{1−w}`,

for `Re w > 1` (`RHTower.LSeries_d4BMRamanujanNaturalCoefficient_eq_div_riemannZeta`).

**Theorems.**
* `divisorPowerSum_ne_zero`: `Σ_{d | n} d^w ≠ 0` whenever `Re w ≠ 0`. The divisor sum is multiplicative, and on
  `p^k` it is the geometric sum `Σ_{j ≤ k} p^{jw}`, which vanishes only if `|p^w| = 1`.
* `meromorphicOrderAt_rademacher` (**momentum universality**): for every `n ≥ 1` and every zero `ρ` of `ζ` with
  `Re ρ < 1`, `ρ ≠ 1`, the continued image sum `σ_{1−w}(n)/ζ(w)` has at `ρ` the order `−ord_ρ ζ`: every momentum
  channel carries every resonance with full multiplicity, with no cancellation from the numerator.
* `modeCoefficient_ne_zero_of_resonance`: the Whittaker coefficient `n^u σ_{−2u}(n)` of every mode of the
  completed Eisenstein function is nonzero at every resonance `u = ρ/2 − ½`, so the resonant state excites every
  momentum.

The positions are the same in every channel; the channels differ only in the residues `σ_{1−ρ}(n)`, which are
multiplicative in `n`.
-/

open Complex ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon

/-- The completely multiplicative arithmetic function `d ↦ d^w`. -/
def cpowFn (w : ℂ) : ArithmeticFunction ℂ := ⟨fun d => if d = 0 then 0 else (d : ℂ) ^ w, by simp⟩

theorem cpowFn_apply {w : ℂ} {d : ℕ} (hd : d ≠ 0) : cpowFn w d = (d : ℂ) ^ w := by
  simp [cpowFn, hd]

theorem isMultiplicative_cpowFn (w : ℂ) : (cpowFn w).IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.2 ⟨by simp [cpowFn], fun {m n} hm hn _ => ?_⟩
  rw [cpowFn_apply (mul_ne_zero hm hn), cpowFn_apply hm, cpowFn_apply hn, Nat.cast_mul,
    natCast_mul_natCast_cpow]

theorem cpow_natCast_pow (p j : ℕ) (w : ℂ) : (((p ^ j : ℕ) : ℂ)) ^ w = ((p : ℂ) ^ w) ^ j := by
  rw [Nat.cast_pow, ← natCast_cpow_natCast_mul, cpow_nat_mul]

/-- **The divisor power sum does not vanish off `Re w = 0`.** -/
theorem divisorPowerSum_ne_zero {w : ℂ} (hw : w.re ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, (d : ℂ) ^ w) ≠ 0 := by
  have hmul : ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * cpowFn w).IsMultiplicative :=
    isMultiplicative_zeta.natCast.mul (isMultiplicative_cpowFn w)
  have heq : (∑ d ∈ n.divisors, (d : ℂ) ^ w) = ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * cpowFn w) n := by
    rw [coe_zeta_mul_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [cpowFn_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
  rw [heq, IsMultiplicative.multiplicative_factorization _ hmul hn, Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  set k := n.factorization p
  rw [coe_zeta_mul_apply, Nat.divisors_prime_pow hpp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hterm : ∀ j ∈ Finset.range (k + 1), cpowFn w (p ^ j) = ((p : ℂ) ^ w) ^ j := fun j _ => by
    rw [cpowFn_apply (pow_ne_zero _ hpp.ne_zero), cpow_natCast_pow]
  rw [Finset.sum_congr rfl hterm]
  set r := (p : ℂ) ^ w
  have hnorm : ∀ m : ℕ, 0 < m → ‖r ^ m‖ ≠ 1 := by
    intro m hm h
    rw [norm_pow, Complex.norm_natCast_cpow_of_pos hpp.pos] at h
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have h' : ((p : ℝ) ^ w.re) ^ m = 1 := h
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h'
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · have := Real.rpow_lt_one_of_one_lt_of_neg hp1 (mul_neg_of_neg_of_pos hneg hm')
      linarith
    · have := Real.one_lt_rpow hp1 (mul_pos hpos hm')
      linarith
  have hr1 : r ≠ 1 := fun h => hnorm 1 one_pos (by rw [pow_one, h, norm_one])
  rw [geom_sum_eq hr1]
  refine div_ne_zero (sub_ne_zero.2 fun h => hnorm (k + 1) (Nat.succ_pos k) (by rw [h, norm_one]))
    (sub_ne_zero.2 hr1)

/-- The numerator of the Rademacher image sum is `σ_{1−w}(n)`. -/
theorem ramanujanDivisorPolynomial_eq (n : ℕ) (w : ℂ) :
    RHTower.d4BMRamanujanDivisorPolynomial n w = ∑ d ∈ n.divisors, (d : ℂ) ^ (1 - w) := by
  unfold RHTower.d4BMRamanujanDivisorPolynomial
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
  rw [sub_eq_add_neg, cpow_add _ _ hd0, cpow_one]

/-- The numerator of the momentum-`n` image sum does not vanish at any point with `Re w ≠ 1`. -/
theorem ramanujanDivisorPolynomial_ne_zero {n : ℕ} (hn : n ≠ 0) {w : ℂ} (hw : w.re ≠ 1) :
    RHTower.d4BMRamanujanDivisorPolynomial n w ≠ 0 := by
  rw [ramanujanDivisorPolynomial_eq]
  exact divisorPowerSum_ne_zero (by simp; intro h; exact hw (by linarith)) hn

theorem differentiable_ramanujanDivisorPolynomial (n : ℕ) :
    Differentiable ℂ (fun w => RHTower.d4BMRamanujanDivisorPolynomial n w) := by
  intro w
  unfold RHTower.d4BMRamanujanDivisorPolynomial
  refine DifferentiableAt.fun_sum fun d hd => ?_
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
  exact (differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hd0))

/-- **Momentum universality.** For every momentum `n ≥ 1` and every `ρ` with `Re ρ ≠ 1`, the continued
Rademacher image sum `σ_{1−w}(n)/ζ(w)` has order `−ord_ρ ζ` at `ρ`: every zero of `ζ` off `Re s = 1` is a pole
of every momentum channel with its full multiplicity. -/
theorem meromorphicOrderAt_rademacher {n : ℕ} (hn : n ≠ 0) {ρ : ℂ} (hρ : ρ.re ≠ 1) :
    meromorphicOrderAt (fun w => RHTower.d4BMRamanujanDivisorPolynomial n w / riemannZeta w) ρ =
      -meromorphicOrderAt riemannZeta ρ := by
  have heq : (fun w => RHTower.d4BMRamanujanDivisorPolynomial n w / riemannZeta w) =
      (fun w => RHTower.d4BMRamanujanDivisorPolynomial n w) * riemannZeta⁻¹ := by
    funext w; simp [div_eq_mul_inv]
  rw [heq, meromorphicOrderAt_mul_of_ne_zero ((differentiable_ramanujanDivisorPolynomial n).analyticAt ρ)
    (ramanujanDivisorPolynomial_ne_zero hn hρ), meromorphicOrderAt_inv]

/-- **The Rademacher image sum and its poles.** For `n ≥ 1` the Ramanujan image sum is `σ_{1−w}(n)/ζ(w)` on
`Re w > 1`, and its continuation has the full order of `1/ζ` at every `ρ` with `Re ρ ≠ 1`. -/
theorem rademacher_image_sum {n : ℕ} (hn : 0 < n) :
    (∀ w : ℂ, 1 < w.re → LSeries (RHTower.d4BMRamanujanNaturalCoefficient n) w =
      RHTower.d4BMRamanujanDivisorPolynomial n w / riemannZeta w) ∧
    ∀ ρ : ℂ, ρ.re ≠ 1 →
      meromorphicOrderAt (fun w => RHTower.d4BMRamanujanDivisorPolynomial n w / riemannZeta w) ρ =
        -meromorphicOrderAt riemannZeta ρ :=
  ⟨fun _ hw => RHTower.LSeries_d4BMRamanujanNaturalCoefficient_eq_div_riemannZeta hn hw,
    fun _ hρ => meromorphicOrderAt_rademacher hn.ne' hρ⟩

/-- **Every Whittaker mode of the completed Eisenstein function is excited off `Re u = 0`.** -/
theorem modeCoefficient_ne_zero {u : ℂ} (hu : u.re ≠ 0) (N : ℕ) : RHTower.modeCoefficient u N ≠ 0 := by
  unfold RHTower.modeCoefficient RHTower.d4BMCompletedEisensteinWhittakerCoefficient
  have hN : ((N + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero N)
  refine mul_ne_zero ?_ (divisorPowerSum_ne_zero (by simp [hu]) (Nat.succ_ne_zero N))
  exact (cpow_ne_zero_iff_of_exponent_ne_zero (fun h => hu (by rw [h]; simp))).2 hN

/-- **The resonant state excites every momentum.** At every resonance `u = ρ/2 − ½` (`Re ρ ≠ 1`) every Whittaker
coefficient `n^u σ_{−2u}(n)` of the completed Eisenstein function is nonzero. -/
theorem modeCoefficient_ne_zero_of_resonance {ρ : ℂ} (hρ : ρ.re ≠ 1) (N : ℕ) :
    RHTower.modeCoefficient (ρ / 2 - 1 / 2) N ≠ 0 :=
  modeCoefficient_ne_zero (by simp; intro h; exact hρ (by linarith)) N

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon
