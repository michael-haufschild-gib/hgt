import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheSourceIsTheDampedMoebiusResidueSeries
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping

/-!
# Residue-mode coordinates diagonalize the damping chain

The residue modes `v_e(x) = ⌊x/e⌋/x − 1/e` (state `x = n + 1` at index `n`) are the eigenvectors of
the centered damping chain `C_η` (`ArithmeticDampingCenteredSpectrum`). This module constructs their
dual system explicitly and shows that it conjugates the chain to diagonal damping of Dirichlet
coefficients.

For any sequence `b`, put `S_b(x) = x · b(x − 1)` and define the **residue-mode coordinates**
`φ_e(b) = Σ_{d ∣ e} μ(e/d) (S_b(d) − S_b(d − 1))`, a Möbius inversion of the discrete derivative.

* `residueStep_eq_sum_floor` (inverse formula, every sequence):
  `x · b(x − 1) = Σ_{1 ≤ e ≤ x} φ_e(b) ⌊x/e⌋`, with `φ_1(b) = b(0)`.
* `residueModeCoord_normalizedResidueProfile` (biorthogonality): `φ_e(v_f) = δ_{ef}` for `e, f ≥ 2`.
* `residueModeCoord_reciprocal`: the reciprocal `r(x) = 1/x` has coordinates `φ_e(r) = μ(e)`.
* `residueModeCoord_centeredOperator` (**diagonalization**): `φ_e(C_η b) = e^{−η} φ_e(b)` for every
  `b ∈ c₀`, `e ≥ 2`, `η > 0`. In these coordinates the chain is `β_e ↦ e^{−η} β_e`, the vertical shift
  `F(s) ↦ F(s + η)` of the Dirichlet series `F(s) = Σ β_e e^{−s}`; the reciprocal's orbit has
  coordinates `μ(e) e^{−η}`, the coefficients of `1/ζ(s + η)`.
* `residueStep_centeredOperator` (orbit formula): `x · (C_η b)(x − 1) = x (C_η b)(0) +
  Σ_{2 ≤ e ≤ x} e^{−η} φ_e(b) ⌊x/e⌋` — every orbit is a finite floor sum of damped coordinates.
* `residueModeProjection`: `Π_e = φ_e(·) v_e` is a bounded projection onto the `e^{−η}`-eigenline,
  `Π_e Π_f = δ_{ef} Π_e`, and `Π_e C_η = C_η Π_e = e^{−η} Π_e`: the bounded spectral projections of
  the compact chain, all explicit and finitely supported.
* `residueModeCoord_eq_zero_iff`: on `c₀` the coordinates `φ_e`, `e ≥ 2`, determine the vector.

The coordinates are exact, but the expansion `b = Σ φ_e(b) v_e` is only a pointwise floor sum: these
statements give no uniform bound on partial expansions and no estimate in the receiver norm.
-/

open Finset Filter Topology ArithmeticFunction
open scoped ZeroAtInfty ArithmeticFunction.Moebius ArithmeticFunction.zeta
open GaloisForLFunctions.SignedArithmeticEnergyIncidence

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The step primitive `S_b(x) = x · b(x − 1)` of a sequence indexed by predecessor states. -/
def residueStep (b : ℕ → ℝ) (x : ℕ) : ℝ := (x : ℝ) * b (x - 1)

/-- The discrete derivative `S_b(d) − S_b(d − 1)` of the step primitive. -/
def residueIncrement (b : ℕ → ℝ) (d : ℕ) : ℝ := residueStep b d - residueStep b (d - 1)

/-- **Residue-mode coordinates** `φ_e(b) = Σ_{d ∣ e} μ(e/d) ΔS_b(d)`. -/
def residueModeCoord (e : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ d ∈ e.divisors, (μ (e / d) : ℝ) * residueIncrement b d

@[simp] theorem residueStep_zero (b : ℕ → ℝ) : residueStep b 0 = 0 := by
  simp [residueStep]

theorem residueModeCoord_one (b : ℕ → ℝ) : residueModeCoord 1 b = b 0 := by
  simp [residueModeCoord, residueIncrement, residueStep]

/-- Möbius inversion: the increments are the divisor sums of the coordinates. -/
theorem sum_divisors_residueModeCoord (b : ℕ → ℝ) {d : ℕ} (hd : 0 < d) :
    ∑ e ∈ d.divisors, residueModeCoord e b = residueIncrement b d := by
  refine (sum_eq_iff_sum_mul_moebius_eq (f := fun e => residueModeCoord e b)
    (g := residueIncrement b)).mpr (fun n _ => ?_) d hd
  rw [Nat.sum_divisorsAntidiagonal' (fun a c => (μ a : ℝ) * residueIncrement b c)]
  rfl

/-- Uniqueness: increments given by divisor sums of `c` force the coordinates `c`. -/
theorem residueModeCoord_eq_of_increment (b c : ℕ → ℝ)
    (h : ∀ d, 0 < d → residueIncrement b d = ∑ e ∈ d.divisors, c e) {e : ℕ} (he : 0 < e) :
    residueModeCoord e b = c e := by
  have hm := (sum_eq_iff_sum_mul_moebius_eq (f := c) (g := residueIncrement b)).mp
    (fun d hd => (h d hd).symm) e he
  rw [Nat.sum_divisorsAntidiagonal' (fun a c => (μ a : ℝ) * residueIncrement b c)] at hm
  exact hm

/-- **Inverse formula.** Every sequence is the floor sum of its coordinates:
`x · b(x − 1) = Σ_{1 ≤ e ≤ x} φ_e(b) ⌊x/e⌋`. -/
theorem residueStep_eq_sum_floor (b : ℕ → ℝ) (x : ℕ) :
    residueStep b x = ∑ e ∈ Icc 1 x, residueModeCoord e b * ((x / e : ℕ) : ℝ) := by
  have htel : residueStep b x = ∑ d ∈ Icc 1 x, residueIncrement b d := by
    induction x with
    | zero => simp
    | succ x ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ← ih]
      simp only [residueIncrement, Nat.add_sub_cancel]
      ring
  rw [htel]
  calc ∑ d ∈ Icc 1 x, residueIncrement b d
      = ∑ d ∈ Icc 1 x, ∑ e ∈ d.divisors, residueModeCoord e b :=
        sum_congr rfl fun d hd =>
          (sum_divisors_residueModeCoord b (by simp only [mem_Icc] at hd; omega)).symm
    _ = _ := TransHorizonIncidenceMechanics.sum_Icc_sum_divisors_eq_floor _ x

private theorem residueStep_profile (f x : ℕ) :
    residueStep (normalizedResidueProfile f) x = ((x / f : ℕ) : ℝ) - (x : ℝ) / f := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hx' : x - 1 + 1 = x := Nat.sub_add_cancel hx
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [residueStep, normalizedResidueProfile, hx']
  rw [mul_sub, mul_div_cancel₀ _ hx0, mul_one_div]

/-- **Biorthogonality**: `φ_e(v_f) = δ_{ef}` for moduli at least two. -/
theorem residueModeCoord_normalizedResidueProfile {e f : ℕ} (he : 2 ≤ e) (hf : 2 ≤ f) :
    residueModeCoord e (normalizedResidueProfile f) = if e = f then 1 else 0 := by
  have hinc : ∀ d, 0 < d → residueIncrement (normalizedResidueProfile f) d =
      ∑ e ∈ d.divisors, ((if e = f then (1 : ℝ) else 0) - (if e = 1 then 1 / (f : ℝ) else 0)) := by
    intro d hd
    have hsum : ∑ e ∈ d.divisors, ((if e = f then (1 : ℝ) else 0) -
        (if e = 1 then 1 / (f : ℝ) else 0)) = (if f ∣ d then 1 else 0) - 1 / (f : ℝ) := by
      rw [sum_sub_distrib, sum_ite_eq', sum_ite_eq']
      simp only [Nat.mem_divisors, one_dvd, ne_eq, hd.ne', not_false_eq_true, and_true,
        ↓reduceIte]
    have hdiv : ((d / f : ℕ) : ℝ) - (((d - 1) / f : ℕ) : ℝ) = if f ∣ d then 1 else 0 := by
      have h := Nat.succ_div (a := d - 1) (b := f)
      rw [Nat.sub_add_cancel hd] at h
      rw [h]
      split_ifs <;> push_cast <;> ring
    have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
    rw [hsum, residueIncrement, residueStep_profile f, residueStep_profile f, hd1, ← hdiv]
    ring
  rw [residueModeCoord_eq_of_increment _ _ hinc (by omega : 0 < e), if_neg (by omega : e ≠ 1),
    sub_zero]

theorem residueModeCoord_mode {e f : ℕ} (he : 2 ≤ e) (hf : 2 ≤ f) :
    residueModeCoord e (normalizedResidueMode f) = if e = f then 1 else 0 :=
  residueModeCoord_normalizedResidueProfile he hf

/-- The reciprocal `r(x) = 1/x` has the Möbius function as its residue-mode coordinates. -/
theorem residueModeCoord_reciprocal {e : ℕ} (he : 0 < e) :
    residueModeCoord e (fun n => 1 / ((n : ℝ) + 1)) = (μ e : ℝ) := by
  refine residueModeCoord_eq_of_increment _ (fun e => (μ e : ℝ)) (fun d hd => ?_) he
  have hmu : ∑ i ∈ d.divisors, (μ i : ℝ) = if d = 1 then 1 else 0 := by
    have h : ∑ i ∈ d.divisors, (μ i : ℤ) = if d = 1 then 1 else 0 := by
      rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    simpa using h'
  have hstep : ∀ x, 0 < x → residueStep (fun n => 1 / ((n : ℝ) + 1)) x = 1 := by
    intro x hx
    have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
    simp only [residueStep]
    rw [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_one, sub_add_cancel, mul_one_div, div_self hx0]
  rw [hmu, residueIncrement, hstep d hd]
  rcases Nat.lt_or_ge 1 d with h1 | h1
  · rw [hstep (d - 1) (by omega), if_neg (by omega)]; ring
  · rw [show d = 1 by omega]; simp

/-! ### The coordinates as bounded functionals on `c₀` -/

private theorem residueModeCoord_add (e : ℕ) (b c : ℕ → ℝ) :
    residueModeCoord e (b + c) = residueModeCoord e b + residueModeCoord e c := by
  simp only [residueModeCoord, residueIncrement, residueStep, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

private theorem residueModeCoord_smul (e : ℕ) (a : ℝ) (b : ℕ → ℝ) :
    residueModeCoord e (a • b) = a * residueModeCoord e b := by
  simp only [residueModeCoord, residueIncrement, residueStep, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

private theorem rmc_abs_sub_le (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg, ← abs_neg b]
  exact abs_add_le a (-b)

private theorem abs_residueModeCoord_le (e : ℕ) (b : C₀(ℕ, ℝ)) :
    |residueModeCoord e b| ≤ (∑ d ∈ e.divisors, 2 * (d : ℝ)) * ‖b‖ := by
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
  have hmu : |(μ (e / d) : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
  have h1 := abs_c0_apply_le_norm b (d - 1)
  have h2 := abs_c0_apply_le_norm b (d - 1 - 1)
  have hd1 : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hd0 : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb : 0 ≤ ‖b‖ := norm_nonneg b
  simp only [residueIncrement, residueStep]
  rw [abs_mul]
  calc |(μ (e / d) : ℝ)| * |(d : ℝ) * b (d - 1) - ((d - 1 : ℕ) : ℝ) * b (d - 1 - 1)|
      ≤ 1 * ((d : ℝ) * ‖b‖ + (d : ℝ) * ‖b‖) := by
        refine mul_le_mul hmu ((rmc_abs_sub_le _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _) zero_le_one
        · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
          exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg d)
        · rw [abs_mul, abs_of_nonneg hd0]
          exact mul_le_mul hd1 h2 (abs_nonneg _) (Nat.cast_nonneg d)
    _ = 2 * (d : ℝ) * ‖b‖ := by ring

/-- The coordinate `φ_e` as a bounded linear functional on `c₀`. -/
def residueModeCoordCLM (e : ℕ) : C₀(ℕ, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun b => residueModeCoord e b
      map_add' := fun b c => by
        rw [ZeroAtInftyContinuousMap.coe_add]
        exact residueModeCoord_add e b c
      map_smul' := fun a b => by
        rw [ZeroAtInftyContinuousMap.coe_smul, RingHom.id_apply, smul_eq_mul]
        exact residueModeCoord_smul e a b }
    (∑ d ∈ e.divisors, 2 * (d : ℝ)) fun b => by
      rw [Real.norm_eq_abs]
      exact abs_residueModeCoord_le e b

@[simp] theorem residueModeCoordCLM_apply (e : ℕ) (b : C₀(ℕ, ℝ)) :
    residueModeCoordCLM e b = residueModeCoord e b := rfl

/-- Biorthogonality on the `c₀` modes. -/
theorem residueModeCoordCLM_mode {e f : ℕ} (he : 2 ≤ e) (hf : 2 ≤ f) :
    residueModeCoordCLM e (normalizedResidueMode f) = if e = f then 1 else 0 :=
  residueModeCoord_normalizedResidueProfile he hf

/-- **Diagonalization.** In residue-mode coordinates the centered chain is the diagonal damping
`φ_e(C_η b) = e^{−η} φ_e(b)`, for every `b ∈ c₀`. -/
theorem residueModeCoord_centeredOperator {η : ℝ} (hη : 0 < η) {e : ℕ} (he : 2 ≤ e)
    (b : C₀(ℕ, ℝ)) :
    residueModeCoord e (arithmeticDampingCenteredOperator hη b) =
      (e : ℝ) ^ (-η) * residueModeCoord e b := by
  have hdense : Dense (Submodule.span ℝ (normalizedResidueMode '' Set.Ici 2) : Set C₀(ℕ, ℝ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr normalizedResidueMode_dense_span
  have hop : (residueModeCoordCLM e).comp (arithmeticDampingCenteredOperator hη) =
      (e : ℝ) ^ (-η) • residueModeCoordCLM e := by
    refine ContinuousLinearMap.ext_on hdense ?_
    rintro _ ⟨f, hf, rfl⟩
    have hf2 : 2 ≤ f := hf
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, smul_eq_mul,
      centeredOperator_normalizedResidueMode hη (by omega : 0 < f), map_smul,
      residueModeCoordCLM_mode he hf2]
    split_ifs with hef
    · rw [hef]
    · simp
  exact congrArg (fun T : C₀(ℕ, ℝ) →L[ℝ] ℝ => T b) hop

/-- The reciprocal's orbit has the damped Möbius coefficients `μ(e) e^{−η}` as coordinates. -/
theorem residueModeCoord_centeredOperator_reciprocal {η : ℝ} (hη : 0 < η) {e : ℕ} (he : 2 ≤ e) :
    residueModeCoord e (arithmeticDampingCenteredOperator hη reciprocalObservable) =
      (μ e : ℝ) * (e : ℝ) ^ (-η) := by
  rw [residueModeCoord_centeredOperator hη he,
    show residueModeCoord e reciprocalObservable = (μ e : ℝ) from
      residueModeCoord_reciprocal (by omega)]
  ring

/-- **Orbit formula.** Every orbit is a finite floor sum of damped coordinates:
`x · (C_η b)(x − 1) = x (C_η b)(0) + Σ_{2 ≤ e ≤ x} e^{−η} φ_e(b) ⌊x/e⌋`. -/
theorem residueStep_centeredOperator {η : ℝ} (hη : 0 < η) (b : C₀(ℕ, ℝ)) (x : ℕ) :
    residueStep (arithmeticDampingCenteredOperator hη b) x =
      (x : ℝ) * arithmeticDampingCenteredOperator hη b 0 +
        ∑ e ∈ Icc 2 x, (e : ℝ) ^ (-η) * residueModeCoord e b * ((x / e : ℕ) : ℝ) := by
  rw [residueStep_eq_sum_floor]
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  rw [← insert_Icc_add_one_left_eq_Icc (show 1 ≤ x from hx), sum_insert (by simp),
    residueModeCoord_one, Nat.div_one, show (1 : ℕ) + 1 = 2 from rfl]
  refine congrArg₂ (· + ·) (mul_comm _ _) (sum_congr rfl fun e he => ?_)
  rw [residueModeCoord_centeredOperator hη (by simp only [mem_Icc] at he; omega)]

/-! ### Spectral projections -/

/-- The rank-one projection `Π_e b = φ_e(b) v_e` onto the residue line of modulus `e`. -/
def residueModeProjection (e : ℕ) : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  (residueModeCoordCLM e).smulRight (normalizedResidueMode e)

theorem residueModeProjection_apply (e : ℕ) (b : C₀(ℕ, ℝ)) :
    residueModeProjection e b = residueModeCoord e b • normalizedResidueMode e := rfl

/-- The projections are orthogonal idempotents: `Π_e Π_f = δ_{ef} Π_e`. -/
theorem residueModeProjection_comp {e f : ℕ} (he : 2 ≤ e) (hf : 2 ≤ f) :
    (residueModeProjection e).comp (residueModeProjection f) =
      if e = f then residueModeProjection e else 0 := by
  ext1 b
  rw [ContinuousLinearMap.comp_apply, residueModeProjection_apply, residueModeProjection_apply,
    ZeroAtInftyContinuousMap.coe_smul, residueModeCoord_smul, residueModeCoord_mode he hf]
  split_ifs with hef
  · subst hef
    rw [mul_one]
    rfl
  · rw [mul_zero, zero_smul]
    rfl

/-- The projections commute with the chain and carry its eigenvalue:
`Π_e C_η = e^{−η} Π_e = C_η Π_e`. -/
theorem residueModeProjection_comp_centeredOperator {η : ℝ} (hη : 0 < η) {e : ℕ} (he : 2 ≤ e) :
    (residueModeProjection e).comp (arithmeticDampingCenteredOperator hη) =
      (e : ℝ) ^ (-η) • residueModeProjection e ∧
    (arithmeticDampingCenteredOperator hη).comp (residueModeProjection e) =
      (e : ℝ) ^ (-η) • residueModeProjection e := by
  constructor
  · ext1 b
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      residueModeProjection_apply, residueModeCoord_centeredOperator hη he, smul_smul]
  · ext1 b
    simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
      residueModeProjection_apply, map_smul,
      centeredOperator_normalizedResidueMode hη (by omega : 0 < e), smul_smul, mul_comm]

/-- On `c₀` the coordinates `φ_e`, `e ≥ 2`, determine the vector. -/
theorem residueModeCoord_eq_zero_iff (b : C₀(ℕ, ℝ)) :
    (∀ e, 2 ≤ e → residueModeCoord e b = 0) ↔ b = 0 := by
  refine ⟨fun h => ?_, fun h e _ => by
    subst h
    simp [residueModeCoord, residueIncrement, residueStep]⟩
  have hstep : ∀ x, residueStep b x = (x : ℝ) * b 0 := by
    intro x
    rw [residueStep_eq_sum_floor]
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    rw [← insert_Icc_add_one_left_eq_Icc (show 1 ≤ x from hx), sum_insert (by simp),
      residueModeCoord_one, Nat.div_one]
    have hz : ∑ e ∈ Icc (1 + 1) x, residueModeCoord e b * ((x / e : ℕ) : ℝ) = 0 :=
      sum_eq_zero fun e he => by rw [h e (by simp only [mem_Icc] at he; omega), zero_mul]
    rw [hz, add_zero, mul_comm]
  have hconst : ∀ n, b n = b 0 := by
    intro n
    have h1 := hstep (n + 1)
    simp only [residueStep, Nat.add_sub_cancel] at h1
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    exact mul_left_cancel₀ hn h1
  have hz : b 0 = 0 := by
    have ht : Tendsto (fun n => b n) atTop (𝓝 0) := by
      have := b.zero_at_infty'
      rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at this
    exact tendsto_nhds_unique tendsto_const_nhds (ht.congr' (Eventually.of_forall hconst))
  exact ZeroAtInftyContinuousMap.ext fun n => (hconst n).trans hz

end

#print axioms residueStep_eq_sum_floor
#print axioms residueModeCoord_normalizedResidueProfile
#print axioms residueModeCoord_reciprocal
#print axioms residueModeCoord_centeredOperator
#print axioms residueModeCoord_centeredOperator_reciprocal
#print axioms residueStep_centeredOperator
#print axioms residueModeProjection_comp
#print axioms residueModeProjection_comp_centeredOperator
#print axioms residueModeCoord_eq_zero_iff

end GaloisForLFunctions.BezoutValuationIncidence
