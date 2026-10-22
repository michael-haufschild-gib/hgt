import GaloisForLFunctions.HTGeometry.AutonomousReciprocalAperture
import GaloisForLFunctions.HTGeometry.FiniteStateAutonomousUpperBound
import GaloisForLFunctions.HTGeometry.EulerFactorRankOne
import GaloisForLFunctions.HTGeometry.LinearOdeBohrSpectrum
import GaloisForLFunctions.RHTower.FiniteIndexEulerHeadFredholmResponseUniversalityLaw

/-!
# Autonomous differential order of finite Euler products and their logarithmic derivatives

For a finite set `S` of primes, the finite Euler product and its logarithmic-derivative flux are
quasiperiodic functions of `t` with frequencies `-log p`, `p ∈ S`, obtained by evaluating a rational
observable along the phase flow `z_p = p^(-i t)`. This module shows that the determinant
`Π_(p ∈ S) (1 - p^(-1 - i t))` of the diagonal characteristic matrix has minimal autonomous order `|S|`,
that the orders of finite Euler products are unbounded, and that the flux
`Σ_(p ∈ S) log p · p^(-1-it) / (1 - p^(-1-it))` (the finite-`S` analogue of `-ζ'/ζ(1 + it)`) has
minimal autonomous order exactly `|S|`. The lower bound comes from the Bohr spectrum: the flux has
Bohr coefficient `log p / p` at frequency `-log p`, so its Bohr frequency module has rational rank at
least `|S|`, and the rank bounds the autonomous order from below. The upper bound is an explicit nonzero
autonomous annihilator of order `|S|`.

## Main results

- `autonomousMinimalOrder_finiteEulerCharacteristicDet_eq`: the inverse finite Euler product
  `t ↦ Π_(p ∈ S) (1 - p^(-1 - i t))` has minimal autonomous order `|S|`.
- `finiteEulerAutonomousOrders_cofinal`: for every `n` some finite Euler product phase has minimal
  autonomous order greater than `n`.
- `bohrCoefficient_finiteEulerFluxPhase_prime`: the Bohr coefficient of the flux at frequency `-log p`
  is `log p / p`.
- `cardinal_finitePrimePacket_le_rank_finiteEulerFluxPhase`: the Bohr frequency module of the flux has
  rational rank at least `|S|`.
- `exists_realAutonomousAnnihilator_finiteEulerFluxPhase`: the flux satisfies a nonzero autonomous
  algebraic differential equation of order `|S|` along the real axis.
- `autonomousMinimalOrder_finiteEulerFluxPhase_eq`: the flux has minimal autonomous order exactly `|S|`.

## Hypotheses

All results are unconditional; the only input is the finite set `S` of primes. Linear independence of
the `log p` over `ℚ` is proved, not assumed.
-/

open Complex Set Filter Topology Matrix

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- Bohr coefficients are additive: for continuous Bohr almost periodic `f, g`, the coefficient of
`f - g` at `λ` is the difference of the coefficients. -/
theorem bohrCoefficient_sub_local {f g : ℝ → ℂ}
    (hfc : Continuous f) (hfa : HTGeometry.IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : HTGeometry.IsBohrAlmostPeriodic g) (lam : ℝ) :
    bohrCoefficient (fun t => f t - g t) lam =
      bohrCoefficient f lam - bohrCoefficient g lam := by
  unfold bohrCoefficient
  have hfun : (fun t : ℝ => (f t - g t) * bohrChar lam t) =
      fun t => f t * bohrChar lam t - g t * bohrChar lam t := by
    funext t
    ring
  rw [hfun]
  exact
    (bohrMean_sub (f := fun t => f t * bohrChar lam t)
      (g := fun t => g t * bohrChar lam t)
      (hfc.mul (continuous_bohrChar lam))
      (isBohrAlmostPeriodic_mul_bohrChar hfc hfa lam)
      (hgc.mul (continuous_bohrChar lam))
      (isBohrAlmostPeriodic_mul_bohrChar hgc hga lam))

/-- The Bohr coefficient of a constant `c` is `c` at frequency `0` and `0` elsewhere. -/
theorem bohrCoefficient_const_local (c : ℂ) (lam : ℝ) :
    bohrCoefficient (fun _ : ℝ => c) lam = if lam = 0 then c else 0 := by
  have hfun : (fun _ : ℝ => c) = fun t => c * bohrExp 0 t := by
    funext t
    simp [bohrExp, bohrChar]
  rw [hfun, bohrCoefficient_const_mul c (continuous_bohrExp 0)
    (isBohrAlmostPeriodic_bohrExp 0), bohrCoefficient_bohrExp]
  by_cases h : lam = 0 <;> simp [h]

/-- The diagonal characteristic matrix `diag(1 - p^(-1) z_p)` evaluated along the phase flow
`z_p = e^(-i t log p)` at complex time `t`. -/
def finiteEulerCharacteristicMatrix (S : Finset Nat.Primes) (z : ℂ) :
    Matrix (Fin (Fintype.card ↥S)) (Fin (Fintype.card ↥S)) ℂ :=
  Matrix.diagonal fun i =>
    1 - finitePrimeDamping S i * phasePoint (finitePrimeFrequency S) z i

/-- The characteristic determinant `Π_(p ∈ S) (1 - p^(-1 - i t))`, the inverse finite Euler product. -/
def finiteEulerCharacteristicDet (S : Finset Nat.Primes) (z : ℂ) : ℂ :=
  Matrix.det (finiteEulerCharacteristicMatrix S z)

/-- The characteristic determinant is the phase function of the inverse-anchor polynomial
`Π_p (1 - X_p / p)`. -/
theorem finiteEulerCharacteristicDet_eq_inverseAnchor (S : Finset Nat.Primes) :
    finiteEulerCharacteristicDet S =
      phaseFunction (finitePrimeFrequency S)
        (polynomialPhaseObservable
          (eulerInverseAnchorPolynomial (finitePrimeDamping S))) := by
  funext z
  rw [finiteEulerCharacteristicDet, finiteEulerCharacteristicMatrix,
    Matrix.det_diagonal]
  simp only [phaseFunction, polynomialPhaseObservable,
    eulerInverseAnchorPolynomial, map_prod, map_sub, map_one, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The inverse finite Euler product over `S` has minimal autonomous order `|S|`. -/
theorem autonomousMinimalOrder_finiteEulerCharacteristicDet_eq
    (S : Finset Nat.Primes) :
    autonomousMinimalOrder (finiteEulerCharacteristicDet S) = Fintype.card ↥S := by
  rw [finiteEulerCharacteristicDet_eq_inverseAnchor]
  exact autonomousMinimalOrder_finiteEulerInverseAnchor_eq S

/-- The set of the first `n` primes. -/
def firstPrimePacket (n : ℕ) : Finset Nat.Primes :=
  Finset.univ.image fun i : Fin n =>
    (⟨Nat.nth Nat.Prime (i : ℕ), Nat.prime_nth_prime (i : ℕ)⟩ : Nat.Primes)

/-- The packet of the first `n` primes has exactly `n` elements. -/
theorem card_firstPrimePacket (n : ℕ) : (firstPrimePacket n).card = n := by
  rw [firstPrimePacket, Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    apply Nat.nth_injective Nat.infinite_setOf_prime
    exact congrArg Subtype.val hij

/-- Autonomous orders of finite Euler products are unbounded: for every `n`, the product over the first
`n + 1` primes has minimal autonomous order `n + 1 > n`. -/
theorem finiteEulerAutonomousOrders_cofinal (n : ℕ) :
    ∃ S : Finset Nat.Primes,
      n < autonomousMinimalOrder (finiteEulerProductPhase S) := by
  refine ⟨firstPrimePacket (n + 1), ?_⟩
  rw [autonomousMinimalOrder_finiteEulerProductPhase_eq, Fintype.card_coe,
    card_firstPrimePacket]
  omega

/-- The flux observable `Σ_p log p · (z_p / p) / (1 - z_p / p)` on the polyannulus. -/
def finiteEulerFluxObservable (S : Finset Nat.Primes)
    (z : Fin (Fintype.card ↥S) → ℂ) : ℂ :=
  ∑ i, (-(finitePrimeFrequency S i : ℂ)) *
    (finitePrimeDamping S i * z i) /
      (1 - finitePrimeDamping S i * z i)

/-- The finite Euler flux `t ↦ Σ_(p ∈ S) log p · p^(-1-it) / (1 - p^(-1-it))`, the logarithmic-derivative
analogue `-ζ_S'/ζ_S(1 + it)`, as a phase function. -/
def finiteEulerFluxPhase (S : Finset Nat.Primes) : ℂ → ℂ :=
  phaseFunction (finitePrimeFrequency S) (finiteEulerFluxObservable S)

/-- On the real axis, `p^(-1) · e^(-i t log p) = p^(-(1 + i t))`. -/
theorem finitePrimeDamping_mul_phasePoint_eq_basePowerLine
    (S : Finset Nat.Primes) (i : Fin (Fintype.card ↥S)) (t : ℝ) :
    finitePrimeDamping S i * phasePoint (finitePrimeFrequency S) (t : ℂ) i =
      basePowerLine ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) 1 t := by
  let p : ℝ := (((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast (finitePrimeAt S i).2.pos
  rw [basePowerLine_eq p 1 t hp]
  simp only [Real.rpow_neg_one]
  change ((p : ℂ)⁻¹) *
      Complex.exp
        (Complex.I * ((-Real.log p : ℝ) : ℂ) * (t : ℂ)) =
    ((p⁻¹ : ℝ) : ℂ) * expChar (-Real.log p) t
  rw [Complex.ofReal_inv]
  congr 1
  simp only [expChar]
  congr 1
  push_cast
  ring

/-- On the real axis the flux is `Σ_p log p · ((1 - p^(-1-it))⁻¹ - 1)`. -/
theorem finiteEulerFluxPhase_ofReal_eq_sum_eulerFactorLine
    (S : Finset Nat.Primes) (t : ℝ) :
    finiteEulerFluxPhase S (t : ℂ) =
      ∑ i : Fin (Fintype.card ↥S),
        (-(finitePrimeFrequency S i : ℂ)) *
          (eulerFactorLine
            ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) 1 t - 1) := by
  classical
  unfold finiteEulerFluxPhase phaseFunction finiteEulerFluxObservable
  apply Finset.sum_congr rfl
  intro i _
  rw [finitePrimeDamping_mul_phasePoint_eq_basePowerLine]
  have hp : (1 : ℝ) <
      (((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ) := by
    exact_mod_cast (finitePrimeAt S i).2.one_lt
  have hden := one_sub_basePowerLine_ne_zero hp one_pos t
  rw [eulerFactorLine]
  field_simp
  ring

/-- For distinct primes `p ≠ q` in `S`, the frequency `-log p` is not in the Bohr frequency module of the
Euler factor at `q`, by rational independence of logarithms of primes. -/
theorem finitePrimeFrequency_not_mem_other_eulerFactorModule
    (S : Finset Nat.Primes) {i j : Fin (Fintype.card ↥S)} (hij : i ≠ j) :
    finitePrimeFrequency S i ∉
      bohrFrequencyModule
        (eulerFactorLine
          ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) 1) := by
  intro hmem
  have hp : (1 : ℝ) <
      (((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ) := by
    exact_mod_cast (finitePrimeAt S j).2.one_lt
  have hspan : finitePrimeFrequency S i ∈
      Submodule.span ℚ
        {Real.log ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ))} :=
    (bohrFrequencyModule_eulerFactorLine_le hp one_pos) hmem
  rw [Submodule.mem_span_singleton] at hspan
  obtain ⟨a, ha⟩ := hspan
  have hjlog : Real.log ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) =
      -finitePrimeFrequency S j := by
    simp [finitePrimeFrequency]
  rw [hjlog, smul_neg] at ha
  have hrel : (1 : ℚ) • finitePrimeFrequency S i +
      a • finitePrimeFrequency S j = 0 := by
    rw [one_smul, ← ha]
    simp
  have hindQ : LinearIndependent ℚ (finitePrimeFrequency S) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (finitePrimeFrequency_linearIndependent S)
  have hcoeff := (linearIndependent_iff'.mp hindQ)
    ({i, j} : Finset (Fin (Fintype.card ↥S)))
    (fun k => if k = i then (1 : ℚ) else a) (by
      rw [Finset.sum_insert (by simpa using hij), Finset.sum_singleton]
      rw [if_pos rfl, if_neg (Ne.symm hij), one_smul]
      simpa using hrel) i (by simp)
  simp at hcoeff

/-- The Bohr coefficient of the finite Euler flux at frequency `-log p` is `log p / p`. -/
theorem bohrCoefficient_finiteEulerFluxPhase_prime
    (S : Finset Nat.Primes) (i : Fin (Fintype.card ↥S)) :
    bohrCoefficient (fun t : ℝ => finiteEulerFluxPhase S (t : ℂ))
      (finitePrimeFrequency S i) =
      (-(finitePrimeFrequency S i : ℂ)) *
        (((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℂ))⁻¹) := by
  classical
  let term : Fin (Fintype.card ↥S) → ℝ → ℂ := fun j t =>
    (-(finitePrimeFrequency S j : ℂ)) *
      (eulerFactorLine
        ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) 1 t - 1)
  have hline : (fun t : ℝ => finiteEulerFluxPhase S (t : ℂ)) =
      fun t => ∑ j, term j t := by
    funext t
    simpa [term] using finiteEulerFluxPhase_ofReal_eq_sum_eulerFactorLine S t
  have hcont : ∀ j, Continuous (term j) := by
    intro j
    have hp : (1 : ℝ) <
        (((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ) := by
      exact_mod_cast (finitePrimeAt S j).2.one_lt
    exact continuous_const.mul
      ((continuous_eulerFactorLine hp one_pos).sub continuous_const)
  have hap : ∀ j, HTGeometry.IsBohrAlmostPeriodic (term j) := by
    intro j
    have hp : (1 : ℝ) <
        (((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ) := by
      exact_mod_cast (finitePrimeAt S j).2.one_lt
    exact isBohrAlmostPeriodic_const_mul _
      (isBohrAlmostPeriodic_sub
        (continuous_eulerFactorLine hp one_pos)
        (isBohrAlmostPeriodic_eulerFactorLine hp one_pos)
        continuous_const (isBohrAlmostPeriodic_const 1))
  rw [hline, bohrCoefficient_finsetSum Finset.univ
    (fun j => term j) (fun j _ => hcont j) (fun j _ => hap j)]
  have hi0 : finitePrimeFrequency S i ≠ 0 :=
    (finitePrimeFrequency_linearIndependent S).ne_zero i
  have hterm : ∀ j : Fin (Fintype.card ↥S),
      bohrCoefficient (term j) (finitePrimeFrequency S i) =
        if j = i then
          (-(finitePrimeFrequency S i : ℂ)) *
            (((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℂ))⁻¹)
        else 0 := by
    intro j
    have hp : (1 : ℝ) <
        (((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ) := by
      exact_mod_cast (finitePrimeAt S j).2.one_lt
    have hscale : bohrCoefficient (term j) (finitePrimeFrequency S i) =
        (-(finitePrimeFrequency S j : ℂ)) *
          bohrCoefficient
            (fun t => eulerFactorLine
              ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) 1 t - 1)
            (finitePrimeFrequency S i) := by
      exact bohrCoefficient_const_mul _
        ((continuous_eulerFactorLine hp one_pos).sub continuous_const)
        (isBohrAlmostPeriodic_sub
          (continuous_eulerFactorLine hp one_pos)
          (isBohrAlmostPeriodic_eulerFactorLine hp one_pos)
          continuous_const (isBohrAlmostPeriodic_const 1)) _
    rw [hscale,
      bohrCoefficient_sub_local
        (continuous_eulerFactorLine hp one_pos)
        (isBohrAlmostPeriodic_eulerFactorLine hp one_pos)
        continuous_const (isBohrAlmostPeriodic_const 1),
      bohrCoefficient_const_local]
    rw [if_neg hi0]
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      have hfreq : baseFrequency
          ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) 1 =
          finitePrimeFrequency S i := by
        simp [baseFrequency, finitePrimeFrequency]
      have hcoeff := bohrCoefficient_eulerFactorLine hp one_pos 1
      rw [hfreq] at hcoeff
      rw [hcoeff, sub_zero]
      norm_num [Real.rpow_neg_one, Complex.ofReal_inv]
    · rw [if_neg hji]
      have hzero : bohrCoefficient
          (eulerFactorLine
            ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) 1)
          (finitePrimeFrequency S i) = 0 :=
        bohrCoefficient_eq_zero_of_notMem
          (finitePrimeFrequency_not_mem_other_eulerFactorModule S (Ne.symm hji))
      rw [hzero, sub_zero, mul_zero]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq'
    Finset.univ i]
  simp

/-- Every frequency `-log p`, `p ∈ S`, lies in the Bohr spectrum of the finite Euler flux. -/
theorem finitePrimeFrequency_mem_bohrSpectrum_finiteEulerFluxPhase
    (S : Finset Nat.Primes) (i : Fin (Fintype.card ↥S)) :
    finitePrimeFrequency S i ∈
      bohrSpectrum
        (realPhaseFunction (finitePrimeFrequency S) (finiteEulerFluxObservable S)) := by
  change bohrCoefficient (fun t : ℝ => finiteEulerFluxPhase S (t : ℂ))
    (finitePrimeFrequency S i) ≠ 0
  rw [bohrCoefficient_finiteEulerFluxPhase_prime]
  apply mul_ne_zero
  · exact neg_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr
        ((finitePrimeFrequency_linearIndependent S).ne_zero i))
  · apply inv_ne_zero
    exact_mod_cast (finitePrimeAt S i).2.ne_zero

/-- The Bohr frequency module of the finite Euler flux has rational rank at least `|S|`. -/
theorem cardinal_finitePrimePacket_le_rank_finiteEulerFluxPhase
    (S : Finset Nat.Primes) :
    (Fintype.card ↥S : Cardinal) ≤
      Module.rank ℚ
        (bohrFrequencyModule
          (realPhaseFunction (finitePrimeFrequency S) (finiteEulerFluxObservable S))) := by
  let M := bohrFrequencyModule
    (realPhaseFunction (finitePrimeFrequency S) (finiteEulerFluxObservable S))
  let w : Fin (Fintype.card ↥S) → M := fun i =>
    ⟨finitePrimeFrequency S i,
      Submodule.subset_span
        (finitePrimeFrequency_mem_bohrSpectrum_finiteEulerFluxPhase S i)⟩
  have hcomp : (M.subtype ∘ w) = finitePrimeFrequency S := by
    funext i
    rfl
  have hindQ : LinearIndependent ℚ (finitePrimeFrequency S) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (finitePrimeFrequency_linearIndependent S)
  have hindw : LinearIndependent ℚ w := by
    refine LinearIndependent.of_comp M.subtype ?_
    rw [hcomp]
    exact hindQ
  simpa [M] using hindw.cardinal_le_rank

/-- On the polyannulus `1/p < |z_p| < p` the flux denominators `1 - z_p / p` do not vanish. -/
theorem finiteEulerFluxDenominator_ne_zero (S : Finset Nat.Primes)
    {z : Fin (Fintype.card ↥S) → ℂ}
    (hz : z ∈ polyannulus (finitePrimeRadius S)) (i : Fin (Fintype.card ↥S)) :
    1 - finitePrimeDamping S i * z i ≠ 0 := by
  apply sub_ne_zero.mpr
  intro heq
  have hzlt : ‖z i‖ < Real.exp (finitePrimeRadius S i) := (hz i).2
  have hexp : Real.exp (finitePrimeRadius S i) =
      ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) := by
    rw [finitePrimeRadius, Real.exp_log]
    exact_mod_cast (finitePrimeAt S i).2.pos
  have hp0 : (0 : ℝ) < ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) := by
    exact_mod_cast (finitePrimeAt S i).2.pos
  have hdamp : ‖finitePrimeDamping S i‖ =
      ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ))⁻¹ := by
    simp [finitePrimeDamping]
  have hnorm : ‖finitePrimeDamping S i * z i‖ < 1 := by
    rw [hexp] at hzlt
    rw [norm_mul, hdamp]
    rwa [inv_mul_lt_one₀ hp0]
  rw [← heq, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

/-- The flux observable is analytic on the polyannulus `1/p < |z_p| < p`. -/
theorem analyticOnNhd_finiteEulerFluxObservable (S : Finset Nat.Primes) :
    AnalyticOnNhd ℂ (finiteEulerFluxObservable S)
      (polyannulus (finitePrimeRadius S)) := by
  classical
  let U := polyannulus (finitePrimeRadius S)
  have hcoord : ∀ i : Fin (Fintype.card ↥S),
      AnalyticOnNhd ℂ (fun z : Fin (Fintype.card ↥S) → ℂ => z i) U := by
    intro i
    exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin (Fintype.card ↥S) => ℂ) i).analyticOnNhd U
  have hterm : ∀ i : Fin (Fintype.card ↥S),
      AnalyticOnNhd ℂ
        (fun z : Fin (Fintype.card ↥S) → ℂ =>
          (-(finitePrimeFrequency S i : ℂ)) *
            (finitePrimeDamping S i * z i) /
              (1 - finitePrimeDamping S i * z i)) U := by
    intro i
    have hnum : AnalyticOnNhd ℂ
        (fun z : Fin (Fintype.card ↥S) → ℂ => finitePrimeDamping S i * z i) U :=
      analyticOnNhd_const.mul (hcoord i)
    have hden : AnalyticOnNhd ℂ
        (fun z : Fin (Fintype.card ↥S) → ℂ => 1 - finitePrimeDamping S i * z i) U :=
      analyticOnNhd_const.sub hnum
    have hinv : AnalyticOnNhd ℂ
        (fun z : Fin (Fintype.card ↥S) → ℂ =>
          (1 - finitePrimeDamping S i * z i)⁻¹) U :=
      fun z hz => (hden z hz).inv (finiteEulerFluxDenominator_ne_zero S hz i)
    have hc : AnalyticOnNhd ℂ
        (fun _ : Fin (Fintype.card ↥S) → ℂ =>
          (-(finitePrimeFrequency S i : ℂ))) U := analyticOnNhd_const
    simpa only [Pi.mul_apply, div_eq_mul_inv, mul_assoc] using hc.mul (hnum.mul hinv)
  unfold finiteEulerFluxObservable
  induction (Finset.univ : Finset (Fin (Fintype.card ↥S))) using Finset.induction with
  | empty => simpa using (analyticOnNhd_const : AnalyticOnNhd ℂ
      (fun _ : Fin (Fintype.card ↥S) → ℂ => (0 : ℂ)) U)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      convert (hterm i).add ih using 1
      funext z
      rfl

/-- The finite Euler flux satisfies a nonzero autonomous algebraic differential equation of order `|S|`
along the real axis. -/
theorem exists_realAutonomousAnnihilator_finiteEulerFluxPhase
    (S : Finset Nat.Primes) :
    ∃ P : Polynomial (MvPolynomial (Fin (Fintype.card ↥S)) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (finiteEulerFluxPhase S) (Fintype.card ↥S) P := by
  classical
  let rho := finitePrimeRadius S
  let omega := finitePrimeFrequency S
  let F := finiteEulerFluxObservable S
  let U := phaseStrip rho omega
  have hrho : ∀ i, 0 < rho i := finitePrimeRadius_pos S
  have hUo : IsOpen U := isOpen_phaseStrip rho omega
  have hUc : IsPreconnected U := isPreconnected_phaseStrip rho omega
  have hzero : (0 : ℂ) ∈ U := zero_mem_phaseStrip hrho
  have hreal : ∀ t : ℝ, (t : ℂ) ∈ U := ofReal_mem_phaseStrip hrho
  have hF : AnalyticOnNhd ℂ F (polyannulus rho) :=
    analyticOnNhd_finiteEulerFluxObservable S
  have hf : AnalyticOnNhd ℂ (finiteEulerFluxPhase S) U := by
    simpa [finiteEulerFluxPhase, F, U, omega, rho] using
      (analyticOnNhd_phaseFunction hF)
  let hUne : U.Nonempty := ⟨0, hzero⟩
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI : Algebra ℂ (analyticSubring U) := (constToAnalytic U).toAlgebra
  letI : Algebra ℂ (meroField U) := (constToMero U).toAlgebra
  letI : Differential ℂ := ⟨0⟩
  letI := meroFieldDifferential hUo hUc hUne
  letI : DifferentialAlgebra ℂ (meroField U) :=
    ⟨fun c => by
      rw [meroField_deriv_constToMero_eq_zero hUo hUc hUne]
      change (0 : meroField U) = algebraMap ℂ (meroField U) 0
      rw [map_zero]⟩
  have hphase : AnalyticOnNhd ℂ (phasePoint omega) U :=
    analyticOnNhd_phasePoint omega U
  have hxi : ∀ i : Fin (Fintype.card ↥S),
      AnalyticOnNhd ℂ (fun z => phasePoint omega z i) U :=
    analyticOnNhd_pi_iff.mp hphase
  let state : Fin (Fintype.card ↥S) → meroField U := fun i =>
    analyticMeroElement (fun z => phasePoint omega z i) (hxi i)
  have hstateDeriv : ∀ i : Fin (Fintype.card ↥S), differentialJet 1 (state i) =
      algebraMap ℂ (meroField U) (Complex.I * (omega i : ℂ)) * state i := by
    intro i
    let xi : ℂ → ℂ := fun z => phasePoint omega z i
    have hdxi : deriv xi = fun z =>
        (Complex.I * (omega i : ℂ)) * xi z := by
      funext z
      change deriv (fun w : ℂ => Complex.exp
        (Complex.I * (omega i : ℂ) * w)) z = _
      convert (((hasDerivAt_id z).const_mul
        (Complex.I * (omega i : ℂ))).cexp.deriv) using 1 <;>
        simp [xi, phasePoint]
      all_goals ring
    change differentialJet 1 (analyticMeroElement xi (hxi i)) = _
    rw [differentialJet_analyticMeroElement hUo hUc hUne xi (hxi i) 1]
    change analyticMeroElement (iteratedDeriv 1 xi)
      (analyticOnNhd_iteratedDeriv (hxi i) 1) = _
    have hscalar : AnalyticOnNhd ℂ
        (fun z => (Complex.I * (omega i : ℂ)) * xi z) U :=
      analyticOnNhd_const.mul (hxi i)
    have hcongr : analyticMeroElement (iteratedDeriv 1 xi)
        (analyticOnNhd_iteratedDeriv (hxi i) 1) =
        analyticMeroElement
          (fun z => (Complex.I * (omega i : ℂ)) * xi z) hscalar :=
      analyticMeroElement_congrOn
        (analyticOnNhd_iteratedDeriv (hxi i) 1) hscalar
        (fun z _ => by rw [iteratedDeriv_one]; exact congrFun hdxi z)
    rw [hcongr]
    have hmul := analyticMeroElement_mul
      (analyticOnNhd_const : AnalyticOnNhd ℂ
        (fun _ : ℂ => Complex.I * (omega i : ℂ)) U) (hxi i)
    rw [hmul, analyticMeroElement_const]
    rfl
  have hstate : ∀ i : Fin (Fintype.card ↥S), differentialJet 1 (state i) ∈
      IntermediateField.adjoin ℂ (Set.range state) := by
    intro i
    rw [hstateDeriv i]
    exact IntermediateField.mul_mem _
      (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin ℂ (Set.range state)
        (Set.mem_range_self i))
  let term : Fin (Fintype.card ↥S) → ℂ → ℂ := fun i z =>
    (-(omega i : ℂ)) *
      (finitePrimeDamping S i * phasePoint omega z i) /
        (1 - finitePrimeDamping S i * phasePoint omega z i)
  have hterm : ∀ i, AnalyticOnNhd ℂ (term i) U := by
    intro i
    have hnum : AnalyticOnNhd ℂ
        (fun z => finitePrimeDamping S i * phasePoint omega z i) U :=
      analyticOnNhd_const.mul (hxi i)
    have hden : AnalyticOnNhd ℂ
        (fun z => 1 - finitePrimeDamping S i * phasePoint omega z i) U :=
      analyticOnNhd_const.sub hnum
    have hinv : AnalyticOnNhd ℂ
        (fun z => (1 - finitePrimeDamping S i * phasePoint omega z i)⁻¹) U := by
      intro z hz
      apply (hden z hz).inv
      exact finiteEulerFluxDenominator_ne_zero S
        (phasePoint_mem_polyannulus hz) i
    have hc : AnalyticOnNhd ℂ (fun _ : ℂ => (-(omega i : ℂ))) U :=
      analyticOnNhd_const
    simpa only [term, div_eq_mul_inv, Pi.mul_apply, mul_assoc] using
      hc.mul (hnum.mul hinv)
  have hsumA : ∀ s : Finset (Fin (Fintype.card ↥S)),
      AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, term i z) U := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using (analyticOnNhd_const : AnalyticOnNhd ℂ
        (fun _ : ℂ => (0 : ℂ)) U)
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        convert (hterm i).add ih using 1
        funext z
        rfl
  have hsum : AnalyticOnNhd ℂ (fun z => ∑ i, term i z) U := by
    exact hsumA (Finset.univ : Finset (Fin (Fintype.card ↥S)))
  have hphaseSum : finiteEulerFluxPhase S = fun z => ∑ i, term i z := by
    funext z
    rfl
  have htermMem : ∀ i, analyticMeroElement (term i) (hterm i) ∈
      IntermediateField.adjoin ℂ (Set.range state) := by
    intro i
    let num : ℂ → ℂ := fun z =>
      finitePrimeDamping S i * phasePoint omega z i
    let den : ℂ → ℂ := fun z => 1 - num z
    have hnum : AnalyticOnNhd ℂ num U := analyticOnNhd_const.mul (hxi i)
    have hden : AnalyticOnNhd ℂ den U := analyticOnNhd_const.sub hnum
    have hden0 : ∀ z ∈ U, den z ≠ 0 := by
      intro z hz
      exact finiteEulerFluxDenominator_ne_zero S
        (phasePoint_mem_polyannulus hz) i
    have hnumM : analyticMeroElement num hnum =
        algebraMap ℂ (meroField U) (finitePrimeDamping S i) * state i := by
      rw [analyticMeroElement_mul
        (analyticOnNhd_const : AnalyticOnNhd ℂ
          (fun _ : ℂ => finitePrimeDamping S i) U) (hxi i),
        analyticMeroElement_const]
      rfl
    have hdenM : analyticMeroElement den hden =
        1 - algebraMap ℂ (meroField U) (finitePrimeDamping S i) * state i := by
      rw [analyticMeroElement_sub
        (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U) hnum,
        analyticMeroElement_const, hnumM]
      change algebraMap ℂ (meroField U) 1 - _ = _
      rw [map_one]
    have hinvM : analyticMeroElement (fun z => (den z)⁻¹)
        (fun z hz => (hden z hz).inv (hden0 z hz)) =
        (1 - algebraMap ℂ (meroField U) (finitePrimeDamping S i) * state i)⁻¹ := by
      rw [analyticMeroElement_inv hden hden0, hdenM]
    have htermM : analyticMeroElement (term i) (hterm i) =
        algebraMap ℂ (meroField U) (-(omega i : ℂ)) *
          (algebraMap ℂ (meroField U) (finitePrimeDamping S i) * state i) *
          (1 - algebraMap ℂ (meroField U) (finitePrimeDamping S i) * state i)⁻¹ := by
      have hmul1 := analyticMeroElement_mul
        (analyticOnNhd_const : AnalyticOnNhd ℂ
          (fun _ : ℂ => (-(omega i : ℂ))) U) hnum
      have hinvA : AnalyticOnNhd ℂ (fun z => (den z)⁻¹) U :=
        fun z hz => (hden z hz).inv (hden0 z hz)
      have hrawA : AnalyticOnNhd ℂ
          (fun z => (-(omega i : ℂ)) * num z * (den z)⁻¹) U :=
        ((analyticOnNhd_const : AnalyticOnNhd ℂ
          (fun _ : ℂ => (-(omega i : ℂ))) U).mul hnum).mul hinvA
      have hmul2 := analyticMeroElement_mul
        ((analyticOnNhd_const : AnalyticOnNhd ℂ
          (fun _ : ℂ => (-(omega i : ℂ))) U).mul hnum) hinvA
      have hcongr : analyticMeroElement (term i) (hterm i) =
          analyticMeroElement
            (fun z => (-(omega i : ℂ)) * num z * (den z)⁻¹) hrawA :=
        analyticMeroElement_congrOn (hterm i) hrawA
          (fun z _ => by simp only [term, num, den, div_eq_mul_inv])
      rw [hcongr, hmul2, hmul1, analyticMeroElement_const, hnumM, hinvM]
      rfl
    rw [htermM]
    apply IntermediateField.mul_mem
    · exact IntermediateField.mul_mem _
        (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mul_mem _
          (IntermediateField.algebraMap_mem _ _)
          (IntermediateField.subset_adjoin ℂ (Set.range state)
            (Set.mem_range_self i)))
    · exact IntermediateField.inv_mem _
        (IntermediateField.sub_mem _ (IntermediateField.one_mem _)
          (IntermediateField.mul_mem _
            (IntermediateField.algebraMap_mem _ _)
            (IntermediateField.subset_adjoin ℂ (Set.range state)
              (Set.mem_range_self i))))
  have hsumMeroA : ∀ s : Finset (Fin (Fintype.card ↥S)),
      analyticMeroElement (fun z => ∑ i ∈ s, term i z) (hsumA s) =
        ∑ i ∈ s, analyticMeroElement (term i) (hterm i) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        change analyticMeroElement (fun _ : ℂ => (0 : ℂ)) _ = 0
        rw [analyticMeroElement_const]
        exact map_zero (constToMero U)
    | @insert i s hi ih =>
        have hadd := analyticMeroElement_add (hterm i) (hsumA s)
        have hcongr : analyticMeroElement
            (fun z => ∑ j ∈ insert i s, term j z) (hsumA (insert i s)) =
            analyticMeroElement
              (fun z => term i z + ∑ j ∈ s, term j z)
              ((hterm i).add (hsumA s)) :=
            analyticMeroElement_congrOn (hsumA (insert i s))
            ((hterm i).add (hsumA s))
            (fun z _ => by
              change (∑ j ∈ insert i s, term j z) =
                term i z + ∑ j ∈ s, term j z
              rw [Finset.sum_insert hi])
        rw [hcongr, hadd, ih, Finset.sum_insert hi]
  have hsumMero : analyticMeroElement (fun z => ∑ i, term i z) hsum =
      ∑ i, analyticMeroElement (term i) (hterm i) := by
    simpa using hsumMeroA
      (Finset.univ : Finset (Fin (Fintype.card ↥S)))
  have hfmem : analyticMeroElement (finiteEulerFluxPhase S) hf ∈
      IntermediateField.adjoin ℂ (Set.range state) := by
    have hcongr : analyticMeroElement (finiteEulerFluxPhase S) hf =
        analyticMeroElement (fun z => ∑ i, term i z) hsum :=
      analyticMeroElement_congrOn hf hsum
        (fun z _ => congrFun hphaseSum z)
    rw [hcongr, hsumMero]
    exact IntermediateField.sum_mem _ fun i _ => htermMem i
  have hdep :=
    not_algebraicIndependent_jets_of_mem_finite_derivationClosed_state
      state hstate hfmem
  have hex :=
    exists_realAutonomousAnnihilator_of_not_algebraicIndependent_analyticMero_jets
      hUo hUc hzero hreal hf hdep
  have hcard : Fintype.card (Fin (Fintype.card ↥S)) = Fintype.card ↥S := by
    exact Fintype.card_fin _
  rw [hcard] at hex
  exact hex

/-- Lower bound: the minimal autonomous order of the finite Euler flux is at least `|S|`, since it
dominates the rational rank of the Bohr frequency module. -/
theorem card_finitePrimePacket_le_autonomousMinimalOrder_finiteEulerFluxPhase
    (S : Finset Nat.Primes) :
    Fintype.card ↥S ≤ autonomousMinimalOrder (finiteEulerFluxPhase S) := by
  have hbudget := rank_bohrFrequencyModule_le_autonomousMinimalOrder
    (finitePrimeRadius_pos S)
    (finitePrimeFrequency_rationallyIndependent S)
    (analyticOnNhd_finiteEulerFluxObservable S)
    (exists_realAutonomousAnnihilator_finiteEulerFluxPhase S)
  have hcard : (Fintype.card ↥S : Cardinal) ≤
      (autonomousMinimalOrder (finiteEulerFluxPhase S) : Cardinal) :=
    (cardinal_finitePrimePacket_le_rank_finiteEulerFluxPhase S).trans hbudget
  exact_mod_cast hcard

/-- The finite Euler flux over `S` has minimal autonomous order exactly `|S|`. -/
theorem autonomousMinimalOrder_finiteEulerFluxPhase_eq
    (S : Finset Nat.Primes) :
    autonomousMinimalOrder (finiteEulerFluxPhase S) = Fintype.card ↥S := by
  apply le_antisymm
  · exact autonomousMinimalOrder_le
      (exists_realAutonomousAnnihilator_finiteEulerFluxPhase S)
  · exact card_finitePrimePacket_le_autonomousMinimalOrder_finiteEulerFluxPhase S

end

end GaloisForLFunctions.HTGeometry
