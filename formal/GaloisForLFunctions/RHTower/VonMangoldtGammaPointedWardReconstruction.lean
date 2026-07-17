import GaloisForLFunctions.RHTower.VonMangoldtGammaBivariateGram

/-!
# Pointed Ward reconstruction of the von Mangoldt--Gamma Bianchi current

The unit-interval variable in the bivariate Taylor-remainder measure is not auxiliary.  An exact
integration-by-parts law identifies its upper boundary with the raw logarithmic source jet.  Thus
two adjacent bivariate moments reconstruct every finite Euler source derivative.

After the mixed-moment/anomaly dictionary is substituted, the same law says that the oriented
adjacent-depth Gamma Bianchi current is exactly a positive raw-source Gram.  This integrates the
finite Bianchi correction into a pointed positive moment object, simultaneously for arbitrary
mixed depths.  It remains a finite absolute-Euler source theorem; no positivity-preserving
inverse tilt or critical completion is asserted.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Pointed Ward law for one Taylor-remainder channel.  The right endpoint contributes `1`; the
left endpoint vanishes because the monomial has positive degree. -/
theorem exponentialRemainderMoment_pointedWard (rate : ℝ) (b : ℕ) :
    rate * exponentialRemainderMoment rate (b + 1) +
        (b + 1 : ℝ) * exponentialRemainderMoment rate b = 1 := by
  let F : ℝ → ℝ := fun u ↦ u ^ (b + 1) * Real.exp (-rate * (1 - u))
  let F' : ℝ → ℝ := fun u ↦
    (b + 1 : ℝ) * u ^ b * Real.exp (-rate * (1 - u)) +
      rate * u ^ (b + 1) * Real.exp (-rate * (1 - u))
  have hF (u : ℝ) : HasDerivAt F (F' u) u := by
    have hpow : HasDerivAt (fun v : ℝ ↦ v ^ (b + 1))
        ((b + 1 : ℝ) * u ^ b) u := by
      convert (hasDerivAt_id u).pow (b + 1) using 1 <;> simp [id_eq]
    have hphase : HasDerivAt (fun v : ℝ ↦ -rate * (1 - v)) rate u := by
      convert (hasDerivAt_const u (-rate)).mul
          ((hasDerivAt_const u 1).sub (hasDerivAt_id u)) using 1 <;> ring
    have hexp : HasDerivAt (fun v : ℝ ↦ Real.exp (-rate * (1 - v)))
        (Real.exp (-rate * (1 - u)) * rate) u :=
      (Real.hasDerivAt_exp _).comp u hphase
    dsimp only [F, F']
    convert hpow.mul hexp using 1 <;> ring
  have hderiv : deriv F = F' := by
    funext u
    exact (hF u).deriv
  have hfund := intervalIntegral.integral_deriv_eq_sub'
    F hderiv (fun u _ ↦ (hF u).differentiableAt) (by
      dsimp only [F']
      fun_prop : ContinuousOn F' (Set.uIcc (0 : ℝ) 1))
  have hleft :
      (∫ u in (0 : ℝ)..1, F' u) =
        (b + 1 : ℝ) * exponentialRemainderMoment rate b +
          rate * exponentialRemainderMoment rate (b + 1) := by
    dsimp only [F', exponentialRemainderMoment]
    have hfirst :
        (∫ u in (0 : ℝ)..1,
            (b + 1 : ℝ) * u ^ b * Real.exp (-rate * (1 - u))) =
          (b + 1 : ℝ) *
            ∫ u in (0 : ℝ)..1, u ^ b * Real.exp (-rate * (1 - u)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    have hsecond :
        (∫ u in (0 : ℝ)..1,
            rate * u ^ (b + 1) * Real.exp (-rate * (1 - u))) =
          rate *
            ∫ u in (0 : ℝ)..1, u ^ (b + 1) * Real.exp (-rate * (1 - u)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    rw [intervalIntegral.integral_add]
    · rw [hfirst, hsecond]
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
  rw [hleft] at hfund
  norm_num [F] at hfund
  linarith

/-- Raw positive logarithmic moment of a finite exponential source. -/
def finiteExponentialGammaRawMoment
    {P : Type*} [Fintype P] (weight rate : P → ℝ)
    (x : ℝ) (a : ℕ) : ℝ :=
  ∑ p : P, weight p * Real.exp (-x * rate p) * rate p ^ a

/-- Every raw source jet is reconstructed from two neighboring entries of the fixed bivariate
moment array.  Both summands are nonnegative for a positive source. -/
theorem finiteExponentialGammaRawMoment_eq_pointedWard
    {P : Type*} [Fintype P] (weight rate : P → ℝ)
    (x : ℝ) (a b : ℕ) :
    finiteExponentialGammaRawMoment weight rate x a =
      finiteExponentialGammaBivariateMoment weight rate x (a + 1) (b + 1) +
        (b + 1 : ℝ) *
          finiteExponentialGammaBivariateMoment weight rate x a b := by
  rw [finiteExponentialGammaRawMoment,
    finiteExponentialGammaBivariateMoment,
    finiteExponentialGammaBivariateMoment, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pow_succ]
  have hward := exponentialRemainderMoment_pointedWard (rate p) b
  simp only [exponentialRemainderMoment] at hward
  calc
    weight p * Real.exp (-x * rate p) * rate p ^ a =
        weight p * Real.exp (-x * rate p) * rate p ^ a * 1 := by ring
    _ = weight p * Real.exp (-x * rate p) * rate p ^ a *
          (rate p * (∫ u in (0 : ℝ)..1,
                u ^ (b + 1) * Real.exp (-rate p * (1 - u))) +
            (b + 1 : ℝ) * (∫ u in (0 : ℝ)..1,
                u ^ b * Real.exp (-rate p * (1 - u)))) := by rw [hward]
    _ = _ := by ring

/-- Raw logarithmic moment of the actual finite von Mangoldt source. -/
def finiteVonMangoldtGammaRawMoment (M : ℕ) (x : ℝ) (a : ℕ) : ℝ :=
  finiteExponentialGammaRawMoment
    (fun p : Fin M ↦
      ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
    (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x a

/-- Pointed Ward reconstruction specialized to the finite von Mangoldt source. -/
theorem finiteVonMangoldtGammaRawMoment_eq_pointedWard
    (M : ℕ) (x : ℝ) (a b : ℕ) :
    finiteVonMangoldtGammaRawMoment M x a =
      finiteVonMangoldtGammaBivariateMoment M x (a + 1) (b + 1) +
        (b + 1 : ℝ) * finiteVonMangoldtGammaBivariateMoment M x a b := by
  exact finiteExponentialGammaRawMoment_eq_pointedWard _ _ x a b

theorem finiteVonMangoldtGammaRawMoment_nonneg (M : ℕ) (x : ℝ) (a : ℕ) :
    0 ≤ finiteVonMangoldtGammaRawMoment M x a := by
  rw [finiteVonMangoldtGammaRawMoment, finiteExponentialGammaRawMoment]
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg
    (mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (Real.exp_pos _).le)
    (pow_nonneg (Real.log_pos
      (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))).le a)

/-- Every nonempty finite aperture has a strictly positive raw logarithmic moment at every
order.  The atom `2` supplies the strict term. -/
theorem finiteVonMangoldtGammaRawMoment_pos
    (M : ℕ) (hM : 0 < M) (x : ℝ) (a : ℕ) :
    0 < finiteVonMangoldtGammaRawMoment M x a := by
  rw [finiteVonMangoldtGammaRawMoment, finiteExponentialGammaRawMoment]
  apply Finset.sum_pos'
  · intro p hp
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
        (Real.exp_pos _).le)
      (pow_nonneg (Real.log_pos
        (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))).le a)
  · let p : Fin M := ⟨0, hM⟩
    refine ⟨p, Finset.mem_univ p, ?_⟩
    dsimp only [p]
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    positivity

/-- The raw order-`N` source jet is exactly the factorially normalized oriented difference of
one coordinate at adjacent Gamma depths.  The reverse indices select the same physical jet
coordinate at both depths. -/
theorem finiteVonMangoldtGammaRawMoment_eq_anomalyBianchi
    (M : ℕ) (x : ℝ) (N b : ℕ) (hb : b < N) :
    finiteVonMangoldtGammaRawMoment M x N =
      ((b + 1).factorial : ℝ) * (-1 : ℝ) ^ N *
        ((finiteVonMangoldtGammaAnomaly M (x : ℂ) (N + 1) (fun _ ↦ 1)
            (gammaAnomalyReverseIndex (N + 1) (b + 1) (by omega))).re -
          (finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1)
            (gammaAnomalyReverseIndex N b hb)).re) := by
  rw [finiteVonMangoldtGammaRawMoment_eq_pointedWard]
  rw [← finiteVonMangoldtGammaAnomaly_reverse_eq_bivariateMoment
      M x (N + 1) (b + 1) (by omega),
    ← finiteVonMangoldtGammaAnomaly_reverse_eq_bivariateMoment M x N b hb]
  rw [Nat.factorial_succ]
  push_cast
  have hsign1 : (-1 : ℝ) ^ (N + 1 + 1) = (-1 : ℝ) ^ N := by
    rw [show N + 1 + 1 = N + 2 by omega, pow_add]
    norm_num
  have hsign2 : (-1 : ℝ) ^ (N + 1) = -((-1 : ℝ) ^ N) := by
    rw [pow_succ]
    ring
  rw [hsign1, hsign2]
  ring

/-- Strict adjacent-depth orientation of every finite von Mangoldt--Gamma Bianchi coordinate. -/
theorem finiteVonMangoldtGammaAnomalyBianchi_oriented_re_pos
    (M : ℕ) (hM : 0 < M) (x : ℝ) (N b : ℕ) (hb : b < N) :
    0 < (-1 : ℝ) ^ N *
        ((finiteVonMangoldtGammaAnomaly M (x : ℂ) (N + 1) (fun _ ↦ 1)
            (gammaAnomalyReverseIndex (N + 1) (b + 1) (by omega))).re -
          (finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1)
            (gammaAnomalyReverseIndex N b hb)).re) := by
  have hraw := finiteVonMangoldtGammaRawMoment_pos M hM x N
  rw [finiteVonMangoldtGammaRawMoment_eq_anomalyBianchi M x N b hb] at hraw
  have hfac : 0 < ((b + 1).factorial : ℝ) := by positivity
  nlinarith

/-! ### Mixed Gram form of the integrated Bianchi current -/

def finiteExponentialGammaRawFeature
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a : Fin n → ℕ) (i : Fin n) :
    EuclideanSpace ℝ P :=
  WithLp.toLp 2 fun p ↦
    Real.sqrt (weight p * Real.exp (-x * rate p)) * rate p ^ a i

/-- Literal Gram matrix of arbitrary raw source-rate monomials. -/
def finiteExponentialGammaRawGram
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.gram ℝ (finiteExponentialGammaRawFeature weight rate x a)

theorem finiteExponentialGammaRawGram_apply
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a : Fin n → ℕ)
    (hweight : ∀ p, 0 ≤ weight p) (i j : Fin n) :
    finiteExponentialGammaRawGram weight rate x a i j =
      finiteExponentialGammaRawMoment weight rate x (a i + a j) := by
  rw [finiteExponentialGammaRawGram, Matrix.gram_apply, PiLp.inner_apply]
  simp only [finiteExponentialGammaRawFeature, RCLike.inner_apply, conj_trivial,
    finiteExponentialGammaRawMoment]
  apply Finset.sum_congr rfl
  intro p hp
  rw [pow_add]
  have hmass : 0 ≤ weight p * Real.exp (-x * rate p) :=
    mul_nonneg (hweight p) (Real.exp_pos _).le
  calc
    Real.sqrt (weight p * Real.exp (-x * rate p)) * rate p ^ a j *
          (Real.sqrt (weight p * Real.exp (-x * rate p)) * rate p ^ a i) =
        (Real.sqrt (weight p * Real.exp (-x * rate p)) *
          Real.sqrt (weight p * Real.exp (-x * rate p))) *
            (rate p ^ a i * rate p ^ a j) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hmass]

theorem finiteExponentialGammaRawGram_posSemidef
    {P : Type*} [Fintype P] {n : ℕ}
    (weight rate : P → ℝ) (x : ℝ) (a : Fin n → ℕ) :
    (finiteExponentialGammaRawGram weight rate x a).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

/-- Raw mixed Gram of the finite von Mangoldt source. -/
def finiteVonMangoldtGammaRawGram
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  finiteExponentialGammaRawGram
    (fun p : Fin M ↦
      ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
    (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x a

theorem finiteVonMangoldtGammaRawGram_apply
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) (i j : Fin n) :
    finiteVonMangoldtGammaRawGram M x a i j =
      finiteVonMangoldtGammaRawMoment M x (a i + a j) := by
  apply finiteExponentialGammaRawGram_apply
  intro p
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

theorem finiteVonMangoldtGammaRawGram_posSemidef
    (M : ℕ) {n : ℕ} (x : ℝ) (a : Fin n → ℕ) :
    (finiteVonMangoldtGammaRawGram M x a).PosSemidef :=
  finiteExponentialGammaRawGram_posSemidef _ _ _ _

/-- The factorially normalized adjacent-depth Bianchi current on arbitrary mixed Gamma depths. -/
def finiteVonMangoldtGammaAnomalyBianchiMixedGram
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ)
    (hadm : ∀ i j, b i + b j < a i + a j) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    (((b i + b j + 1).factorial : ℕ) : ℝ) *
      (-1 : ℝ) ^ (a i + a j) *
        ((finiteVonMangoldtGammaAnomaly M (x : ℂ) (a i + a j + 1) (fun _ ↦ 1)
            (gammaAnomalyReverseIndex (a i + a j + 1) (b i + b j + 1)
              (Nat.add_lt_add_right (hadm i j) 1))).re -
          (finiteVonMangoldtGammaAnomaly M (x : ℂ) (a i + a j) (fun _ ↦ 1)
            (gammaAnomalyReverseIndex (a i + a j) (b i + b j) (hadm i j))).re)

/-- The whole mixed Bianchi-current matrix is exactly the raw source Gram. -/
theorem finiteVonMangoldtGammaAnomalyBianchiMixedGram_eq_rawGram
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ)
    (hadm : ∀ i j, b i + b j < a i + a j) :
    finiteVonMangoldtGammaAnomalyBianchiMixedGram M x a b hadm =
      finiteVonMangoldtGammaRawGram M x a := by
  ext i j
  rw [finiteVonMangoldtGammaAnomalyBianchiMixedGram,
    finiteVonMangoldtGammaRawGram_apply]
  exact (finiteVonMangoldtGammaRawMoment_eq_anomalyBianchi
    M x (a i + a j) (b i + b j) (hadm i j)).symm

/-- Unconditional positive-semidefiniteness of the integrated, pointed, all-depth Gamma Bianchi
current. -/
theorem finiteVonMangoldtGammaAnomalyBianchiMixedGram_posSemidef
    (M : ℕ) {n : ℕ} (x : ℝ) (a b : Fin n → ℕ)
    (hadm : ∀ i j, b i + b j < a i + a j) :
    (finiteVonMangoldtGammaAnomalyBianchiMixedGram M x a b hadm).PosSemidef := by
  rw [finiteVonMangoldtGammaAnomalyBianchiMixedGram_eq_rawGram]
  exact finiteVonMangoldtGammaRawGram_posSemidef M x a

end

end RHTower
