import GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.EscortLogit

/-!
# The literal prime Gibbs source of the Boolean--Mass--Hankel--quantum fusion

A finite aperture `F` of primes carries, at inverse temperature `σ`, the fugacity `p^{-σ}`, the
Bernoulli occupation `q_p = p^{-σ}/(1+p^{-σ}) = 1/(1+p^σ)`, the Gibbs weight
`w_p = q_p(1-q_p) = p^σ/(1+p^σ)²` and the clock `lam_p = log p`.  All four fusion organs are
evaluated on that single source:

* the Mass current `j_p = √(w_p)·lam_p`, whose squared `ℓ²` norm is the clock energy `C`, and
  which at `σ = 1` is the primitive Mass coefficient `log p/√p` damped by `p/(p+1)`;
* the first Hankel block `!![M₀, M₁; M₁, M₂]` of the clock moment measure, positive semidefinite,
  with determinant `A C - B²`;
* the parity--clock Schur capacity `D`, with `D · C = π² det H₁`;
* the pure clock orbit of the normalised Boolean state on `ℓ²(𝒫(F))`, a unit vector that returns
  to itself at arbitrarily late times, whose transverse quantum Fisher value is `4 D`.

Every organ is strictly positive as soon as two primes are marked, so a criticality rule asking a
finite transverse organ to vanish is refuted; and one marked Gibbs weight already determines the
inverse temperature.
-/

namespace HTGeometry

noncomputable section

open Finset ConstraintFrameRelativity

/-! ## The Mass current, the moment block, and the three-organ conservation law -/

section Abstract

variable {ι : Type*} [Fintype ι]

/-- The clock Mass current `j_p = √(w_p)·lam_p`. -/
def fusionMassCurrent (w lam : ι → ℝ) (p : ι) : ℝ := Real.sqrt (w p) * lam p

/-- **Mass norm identity.**  The squared `ℓ²` norm of the current is the clock energy `C`. -/
theorem sum_fusionMassCurrent_sq {w : ι → ℝ} (hw : ∀ p, 0 ≤ w p) (lam : ι → ℝ) :
    ∑ p, fusionMassCurrent w lam p ^ 2 = fusionMassEnergy w lam := by
  unfold fusionMassCurrent fusionMassEnergy capC
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_pow, Real.sq_sqrt (hw p)]

/-- The `k`-th moment of the clock measure `∑_p w_p δ_{lam_p}`. -/
def clockMoment (w lam : ι → ℝ) (k : ℕ) : ℝ := ∑ p, w p * lam p ^ k

theorem clockMoment_zero (w lam : ι → ℝ) : clockMoment w lam 0 = capA w := by
  simp [clockMoment, capA]

theorem clockMoment_one (w lam : ι → ℝ) : clockMoment w lam 1 = capB w lam := by
  simp [clockMoment, capB]

theorem clockMoment_two (w lam : ι → ℝ) : clockMoment w lam 2 = capC w lam := rfl

/-- The first Hankel block of the clock moment measure. -/
def fusionHankelMatrix (w lam : ι → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![capA w, capB w lam; capB w lam, capC w lam]

/-- The block is the Hankel matrix of the first three clock moments. -/
theorem fusionHankelMatrix_eq_moments (w lam : ι → ℝ) :
    fusionHankelMatrix w lam
      = Matrix.of fun i j : Fin 2 => clockMoment w lam ((i : ℕ) + (j : ℕ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fusionHankelMatrix, clockMoment_zero, clockMoment_one, clockMoment_two]

theorem det_fusionHankelMatrix (w lam : ι → ℝ) :
    (fusionHankelMatrix w lam).det = fusionHankelDet w lam := by
  rw [fusionHankelMatrix, Matrix.det_fin_two_of, fusionHankelDet]
  ring

/-- The Hankel block is a positive semidefinite quadratic form. -/
theorem fusionHankel_quadratic_nonneg {w : ι → ℝ} (hw : ∀ p, 0 ≤ w p) (lam : ι → ℝ) (x y : ℝ) :
    0 ≤ x ^ 2 * capA w + 2 * x * y * capB w lam + y ^ 2 * capC w lam := by
  have h : x ^ 2 * capA w + 2 * x * y * capB w lam + y ^ 2 * capC w lam
      = ∑ p, w p * (x + y * lam p) ^ 2 := by
    simp only [capA, capB, capC, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (sq_nonneg _)

/-- **Three-organ conserved-volume identity.**  Boolean capacity times Mass energy is `π²` times
the Hankel determinant. -/
theorem schurCapacity_mul_massEnergy {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    schurCapacity w lam * fusionMassEnergy w lam = Real.pi ^ 2 * fusionHankelDet w lam := by
  unfold fusionMassEnergy fusionHankelDet
  rw [schurCapacity_eq_ratio hC]
  field_simp

/-- **Three-organ conservation in clock-gap form.** -/
theorem pairEnergy_eq_schurCapacity_mul_massEnergy [LinearOrder ι] [DecidableEq ι]
    {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    Real.pi ^ 2 *
        ∑ p, ∑ r ∈ Finset.univ.filter (fun r => p < r), w p * w r * (lam p - lam r) ^ 2
      = schurCapacity w lam * fusionMassEnergy w lam := by
  rw [schurCapacity_mul_massEnergy hC, fusionHankelDet, capA_mul_capC_sub_capB_sq_lt]

/-- Pure-state quantum Fisher value along the parity/clock tangent `(a,b)`. -/
def fusionTangentQFI (w lam : ι → ℝ) (a b : ℝ) : ℝ :=
  4 * ((Real.pi * a) ^ 2 * capA w - 2 * (Real.pi * a) * b * capB w lam + b ^ 2 * capC w lam)

/-- The tangent value in the Gram coordinates of the parity--clock pair. -/
theorem fusionTangentQFI_eq (w lam : ι → ℝ) (a b : ℝ) :
    fusionTangentQFI w lam a b
      = 4 * (Real.pi ^ 2 * capA w * a ^ 2 - 2 * Real.pi * capB w lam * a * b
        + capC w lam * b ^ 2) := by
  unfold fusionTangentQFI
  ring

/-- The parity direction of the tangent family is the directional value. -/
theorem fusionTangentQFI_one (w lam : ι → ℝ) (b : ℝ) :
    fusionTangentQFI w lam 1 b = fusionDirectionalQFI w lam b := by
  unfold fusionTangentQFI fusionDirectionalQFI
  ring

/-- **The two-parameter pure-state quantum Fisher value of the Boolean source.**  The tangent
`(a,b)` generates `i(π a N - b E)ψ`, whose projectivised energy is four times the variance of
`π a N - b E`. -/
theorem pureStateQuantumFisherValue_parityClock_tangent [DecidableEq ι]
    (q lam : ι → ℝ) (a b : ℝ) :
    pureStateQuantumFisherValue 1
      (bernoulliExp q (linearStat fun p => Real.pi * a - b * lam p))
      (bernoulliExp q (fun S => (linearStat (fun p => Real.pi * a - b * lam p) S) ^ 2))
      = fusionTangentQFI (bernoulliVar q) lam a b := by
  unfold pureStateQuantumFisherValue projectiveQuantumTangentValue fusionTangentQFI
  simp only [one_pow, div_one]
  have hcov := bernoulliCov_affine_clock q lam (Real.pi * a) b
  rw [quadratic_expand] at hcov
  have hvar :
      bernoulliExp q (fun S => (linearStat (fun p => Real.pi * a - b * lam p) S) ^ 2) -
          bernoulliExp q (linearStat fun p => Real.pi * a - b * lam p) ^ 2 =
        (Real.pi * a) ^ 2 * capA (bernoulliVar q)
          - 2 * (Real.pi * a) * b * capB (bernoulliVar q) lam
          + b ^ 2 * capC (bernoulliVar q) lam := by
    calc
      _ = bernoulliCov q (linearStat fun p => Real.pi * a - b * lam p)
          (linearStat fun p => Real.pi * a - b * lam p) := by
            simp only [bernoulliCov, pow_two]
      _ = _ := hcov
  simpa only [one_mul] using congrArg (fun x : ℝ => 4 * x) hvar

/-- The transverse quantum Fisher value is the least directional value. -/
theorem isLeast_fusionTransverseQFI {w lam : ι → ℝ} (hC : 0 < capC w lam) :
    IsLeast {v : ℝ | ∃ t : ℝ, fusionDirectionalQFI w lam t = v} (fusionTransverseQFI w lam) := by
  constructor
  · exact ⟨Real.pi * capB w lam / capC w lam, fusionDirectionalQFI_canonical hC⟩
  · rintro v ⟨t, rfl⟩
    exact fusionTransverseQFI_le_directional hC t

/-! ### The single-clock degeneration -/

/-- One marked clock kills the Hankel determinant. -/
theorem fusionHankelDet_eq_zero_of_subsingleton [Subsingleton ι] (w lam : ι → ℝ) :
    fusionHankelDet w lam = 0 := by
  unfold fusionHankelDet
  rw [capA_mul_capC_sub_capB_sq]
  have hz : ∀ p : ι, ∑ r, w p * w r * (lam p - lam r) ^ 2 = 0 := by
    intro p
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [Subsingleton.elim r p]
    ring
  rw [Finset.sum_congr rfl fun p _ => hz p]
  simp

/-- One marked clock kills the Boolean capacity. -/
theorem schurCapacity_eq_zero_of_subsingleton [Subsingleton ι] {w lam : ι → ℝ}
    (hC : 0 < capC w lam) : schurCapacity w lam = 0 := by
  rw [schurCapacity_eq_ratio hC]
  have h := fusionHankelDet_eq_zero_of_subsingleton w lam
  unfold fusionHankelDet at h
  rw [h]
  simp

/-- One marked clock kills the transverse quantum Fisher value. -/
theorem fusionTransverseQFI_eq_zero_of_subsingleton [Subsingleton ι] {w lam : ι → ℝ}
    (hC : 0 < capC w lam) : fusionTransverseQFI w lam = 0 := by
  rw [fusionTransverseQFI, schurCapacity_eq_zero_of_subsingleton hC, mul_zero]

end Abstract

/-! ## Recovering the occupation from its variance -/

/-- Two numbers at most `1/2` with equal Bernoulli variance are equal. -/
theorem eq_of_mul_one_sub_eq {q q' : ℝ} (hq : q ≤ 1 / 2) (hq' : q' ≤ 1 / 2)
    (h : q * (1 - q) = q' * (1 - q')) : q = q' := by
  have hfac : (q - q') * (1 - (q + q')) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · linarith
  · have hq2 : q = 1 / 2 := by linarith
    have hq'2 : q' = 1 / 2 := by linarith
    rw [hq2, hq'2]

theorem occVar_le_quarter {x : ℝ} (hx : 0 ≤ x) : occVar x ≤ 1 / 4 := by
  have h : (0 : ℝ) < 1 + x := by linarith
  rw [occVar_eq hx, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (1 - x)]

theorem occProb_le_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : occProb x ≤ 1 / 2 := by
  have h : (0 : ℝ) < 1 + x := by linarith
  rw [occProb, div_le_div_iff₀ h (by norm_num)]
  linarith

theorem probOfVar_le_half (w : ℝ) : probOfVar w ≤ 1 / 2 := by
  have h := Real.sqrt_nonneg (1 - 4 * w)
  rw [probOfVar]
  linarith

/-- **Occupation reconstruction.**  On the physical branch the occupation is the smaller root of
`q(1-q) = w`. -/
theorem occProb_eq_probOfVar_occVar {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    occProb x = probOfVar (occVar x) := by
  refine eq_of_mul_one_sub_eq (occProb_le_half hx0 hx1) (probOfVar_le_half _) ?_
  have h2 : probOfVar (occVar x) * (1 - probOfVar (occVar x)) = occVar x :=
    bernVar_probOfVar (occVar_le_quarter hx0)
  rw [h2]
  rfl

/-- **Fugacity reconstruction.**  The Gibbs variance determines the fugacity on `(0,1]`. -/
theorem eq_of_occVar_eq {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h : occVar x = occVar y) : x = y := by
  have hq : occProb x = occProb y := by
    rw [occProb_eq_probOfVar_occVar hx0.le hx1, occProb_eq_probOfVar_occVar hy0.le hy1, h]
  have hx : probToOdds (occProb x) = x := probToOdds_oddsToProb hx0
  have hy : probToOdds (occProb y) = y := probToOdds_oddsToProb hy0
  rw [← hx, ← hy, hq]

/-- The half-density Mass damping of a single clock. -/
theorem sqrt_div_add_one_sq_mul_log {P : ℝ} (hP : 0 < P) :
    Real.sqrt (P / (P + 1) ^ 2) * Real.log P
      = P / (P + 1) * (Real.log P / Real.sqrt P) := by
  have hP1 : (0 : ℝ) < P + 1 := by linarith
  have hsp : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have hspsq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP.le
  have hL : Real.sqrt (P / (P + 1) ^ 2) = Real.sqrt P / (P + 1) := by
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ (P + 1) ^ 2), Real.sqrt_sq hP1.le]
  rw [hL, div_mul_eq_mul_div, div_mul_div_comm, div_eq_div_iff hP1.ne' (by positivity)]
  linear_combination (Real.log P * (P + 1)) * hspsq

/-! ## The literal prime aperture source -/

section PrimeSource

variable (F : Finset Nat.Primes)

/-- Fugacity `p^{-σ}` of a marked prime. -/
def apertureFug (σ : ℝ) (p : F) : ℝ := ((((p : Nat.Primes) : ℕ) : ℝ)) ^ (-σ)

/-- Bernoulli occupation `q_p = p^{-σ}/(1+p^{-σ})` of a marked prime. -/
def apertureOcc (σ : ℝ) (p : F) : ℝ := occProb (apertureFug F σ p)

/-- Gibbs weight `w_p = q_p(1-q_p)` of a marked prime. -/
def apertureWt (σ : ℝ) (p : F) : ℝ := occVar (apertureFug F σ p)

theorem one_lt_aperturePrime (p : F) : (1 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) := by
  exact_mod_cast (p : Nat.Primes).2.one_lt

theorem aperturePrime_pos (p : F) : (0 : ℝ) < (((p : Nat.Primes) : ℕ) : ℝ) :=
  lt_trans zero_lt_one (one_lt_aperturePrime F p)

theorem apertureFug_pos (σ : ℝ) (p : F) : 0 < apertureFug F σ p :=
  Real.rpow_pos_of_pos (aperturePrime_pos F p) _

theorem apertureFug_le_one {σ : ℝ} (hσ : 0 ≤ σ) (p : F) : apertureFug F σ p ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_lt_aperturePrime F p).le (by linarith)

theorem apertureWt_pos (σ : ℝ) (p : F) : 0 < apertureWt F σ p :=
  occVar_pos (apertureFug_pos F σ p)

/-- The Gibbs weight is the Bernoulli variance of the occupation law. -/
theorem bernoulliVar_apertureOcc (σ : ℝ) : bernoulliVar (apertureOcc F σ) = apertureWt F σ := by
  funext p
  rfl

theorem apertureOcc_pos (σ : ℝ) (p : F) : 0 < apertureOcc F σ p :=
  (oddsToProb_mem (apertureFug_pos F σ p)).1

theorem apertureOcc_lt_one (σ : ℝ) (p : F) : apertureOcc F σ p < 1 :=
  (oddsToProb_mem (apertureFug_pos F σ p)).2

/-- **The occupation in temperature coordinates.**  `q_p = 1/(1+p^σ)`. -/
theorem apertureOcc_eq (σ : ℝ) (p : F) :
    apertureOcc F σ p = 1 / (1 + ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ) := by
  have hp := aperturePrime_pos F p
  have hpow : (0 : ℝ) < ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ := Real.rpow_pos_of_pos hp σ
  have hne : ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ ≠ 0 := hpow.ne'
  have hne' : (1 : ℝ) + ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ ≠ 0 := by positivity
  have hneg : apertureFug F σ p = (((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ)⁻¹ := by
    rw [apertureFug, Real.rpow_neg hp.le]
  rw [apertureOcc, occProb, hneg]
  field_simp
  ring

/-- **The Gibbs weight in temperature coordinates.**  `w_p = p^σ/(1+p^σ)²`. -/
theorem apertureWt_eq (σ : ℝ) (p : F) :
    apertureWt F σ p
      = ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ / (1 + ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ) ^ 2 := by
  have hp := aperturePrime_pos F p
  have hpow : (0 : ℝ) < ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ := Real.rpow_pos_of_pos hp σ
  have hne : ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ ≠ 0 := hpow.ne'
  have hne' : (1 : ℝ) + ((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ ≠ 0 := by positivity
  have hneg : apertureFug F σ p = (((((p : Nat.Primes) : ℕ) : ℝ)) ^ σ)⁻¹ := by
    rw [apertureFug, Real.rpow_neg hp.le]
  rw [apertureWt, occVar_eq (apertureFug_pos F σ p).le, hneg]
  field_simp
  ring

/-- The clock energy moment of the prime source is strictly positive. -/
theorem apertureEnergy_pos (σ : ℝ) (p₀ : F) : 0 < capC (apertureWt F σ) (primeClockVec F) :=
  capC_pos (fun p => apertureWt_pos F σ p) (p₀ := p₀) (primeClockVec_pos p₀).ne'

/-- Distinct marked primes carry distinct clocks. -/
theorem primeClockVec_injective : Function.Injective (primeClockVec F) := by
  intro p r h
  have hp := aperturePrime_pos F p
  have hr := aperturePrime_pos F r
  have hreal : ((((p : Nat.Primes) : ℕ) : ℝ)) = ((((r : Nat.Primes) : ℕ) : ℝ)) := by
    have hex := congrArg Real.exp h
    rwa [primeClockVec, primeClockVec, Real.exp_log hp, Real.exp_log hr] at hex
  have hnat : ((p : Nat.Primes) : ℕ) = ((r : Nat.Primes) : ℕ) := by exact_mod_cast hreal
  exact Subtype.ext (Subtype.ext hnat)

/-! ### The Mass organ of the prime source -/

/-- **Mass norm identity at the prime source.** -/
theorem sum_apertureMassCurrent_sq (σ : ℝ) :
    ∑ p : F, fusionMassCurrent (apertureWt F σ) (primeClockVec F) p ^ 2
      = fusionMassEnergy (apertureWt F σ) (primeClockVec F) :=
  sum_fusionMassCurrent_sq (fun p => (apertureWt_pos F σ p).le) _

/-- **Exact half-density Mass damping.**  At `σ = 1` the source current is the primitive Mass
coefficient `log p/√p` damped by the bounded factor `p/(p+1)`. -/
theorem apertureMassCurrent_one (p : F) :
    fusionMassCurrent (apertureWt F 1) (primeClockVec F) p
      = ((((p : Nat.Primes) : ℕ) : ℝ)) / (((((p : Nat.Primes) : ℕ) : ℝ)) + 1)
        * (Real.log ((((p : Nat.Primes) : ℕ) : ℝ))
          / Real.sqrt ((((p : Nat.Primes) : ℕ) : ℝ))) := by
  have hp := aperturePrime_pos F p
  have hw : apertureWt F 1 p
      = ((((p : Nat.Primes) : ℕ) : ℝ)) / (((((p : Nat.Primes) : ℕ) : ℝ)) + 1) ^ 2 := by
    rw [apertureWt_eq, Real.rpow_one, add_comm (1 : ℝ)]
  rw [fusionMassCurrent, hw, primeClockVec]
  exact sqrt_div_add_one_sq_mul_log hp

/-! ### Strict positivity of every finite organ -/

variable {F}

/-- **Positive Boolean capacity.**  Two marked primes force strictly positive capacity. -/
theorem aperture_schurCapacity_pos (σ : ℝ) {p r : F} (hpr : p ≠ r) :
    0 < schurCapacity (apertureWt F σ) (primeClockVec F) :=
  schurCapacity_pos (fun p => apertureWt_pos F σ p)
    (p₀ := p) (r₀ := r) (fun h => hpr (primeClockVec_injective F h))

/-- **Positive Hankel determinant.** -/
theorem aperture_fusionHankelDet_pos (σ : ℝ) {p r : F} (hpr : p ≠ r) :
    0 < fusionHankelDet (apertureWt F σ) (primeClockVec F) :=
  fusionHankelDet_pos (fun p => apertureWt_pos F σ p)
    (p := p) (r := r) (fun h => hpr (primeClockVec_injective F h))

/-- **Positive transverse quantum Fisher value.** -/
theorem aperture_fusionTransverseQFI_pos (σ : ℝ) {p r : F} (hpr : p ≠ r) :
    0 < fusionTransverseQFI (apertureWt F σ) (primeClockVec F) :=
  fusionTransverseQFI_pos (fun p => apertureWt_pos F σ p)
    (p := p) (r := r) (fun h => hpr (primeClockVec_injective F h))

/-- **Three-organ conservation at the prime source.** -/
theorem aperture_schurCapacity_mul_massEnergy (σ : ℝ) (p₀ : F) :
    schurCapacity (apertureWt F σ) (primeClockVec F)
        * fusionMassEnergy (apertureWt F σ) (primeClockVec F)
      = Real.pi ^ 2 * fusionHankelDet (apertureWt F σ) (primeClockVec F) :=
  schurCapacity_mul_massEnergy (apertureEnergy_pos F σ p₀)

/-- **Four-organ conservation at the prime source.** -/
theorem aperture_fusionTransverseQFI_mul_massEnergy (σ : ℝ) (p₀ : F) :
    fusionTransverseQFI (apertureWt F σ) (primeClockVec F)
        * fusionMassEnergy (apertureWt F σ) (primeClockVec F)
      = 4 * Real.pi ^ 2 * fusionHankelDet (apertureWt F σ) (primeClockVec F) :=
  fusionTransverseQFI_mul_massEnergy (apertureEnergy_pos F σ p₀)

/-! ### Source-parameter reconstruction -/

/-- The marked prime is recovered from its clock. -/
theorem exp_primeClockVec (p : F) :
    Real.exp (primeClockVec F p) = ((((p : Nat.Primes) : ℕ) : ℝ)) :=
  Real.exp_log (aperturePrime_pos F p)

/-- **Inverse-temperature reconstruction.**  One marked Gibbs weight determines `σ`. -/
theorem sigma_eq_of_apertureWt_eq {σ σ' : ℝ} (hσ : 0 ≤ σ) (hσ' : 0 ≤ σ') (p : F)
    (h : apertureWt F σ p = apertureWt F σ' p) : σ = σ' := by
  have hfug : apertureFug F σ p = apertureFug F σ' p :=
    eq_of_occVar_eq (apertureFug_pos F σ p) (apertureFug_le_one F hσ p)
      (apertureFug_pos F σ' p) (apertureFug_le_one F hσ' p) h
  have hP : (1 : ℝ) < ((((p : Nat.Primes) : ℕ) : ℝ)) := one_lt_aperturePrime F p
  have hmono : StrictMono fun y : ℝ => ((((p : Nat.Primes) : ℕ) : ℝ)) ^ y :=
    fun a b hab => (Real.rpow_lt_rpow_left_iff hP).mpr hab
  have hneg : -σ = -σ' := hmono.injective hfug
  linarith

end PrimeSource

/-! ## The Boolean source state and its recurrent clock orbit -/

/-- A product of factors of modulus at most one stays close to `1` when each factor does. -/
theorem norm_prod_sub_one_le {κ : Type*} [DecidableEq κ] (z : κ → ℂ) (hz : ∀ p, ‖z p‖ ≤ 1)
    (S : Finset κ) : ‖(∏ p ∈ S, z p) - 1‖ ≤ ∑ p ∈ S, ‖z p - 1‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hstep : z a * (∏ p ∈ S, z p) - 1
          = z a * ((∏ p ∈ S, z p) - 1) + (z a - 1) := by ring
      have h1 : ‖z a * (∏ p ∈ S, z p) - 1‖
          ≤ ‖z a * ((∏ p ∈ S, z p) - 1)‖ + ‖z a - 1‖ := by
        rw [hstep]
        exact norm_add_le _ _
      have h2 : ‖z a * ((∏ p ∈ S, z p) - 1)‖ ≤ ‖(∏ p ∈ S, z p) - 1‖ := by
        rw [norm_mul]
        nlinarith [hz a, norm_nonneg ((∏ p ∈ S, z p) - 1), norm_nonneg (z a)]
      linarith

section State

variable (F : Finset Nat.Primes)

/-- The normalised Boolean parity/clock source state on `ℓ²(𝒫(F))`. -/
def fusionSourceState (σ α t : ℝ) : EuclideanSpace ℂ (Finset F) :=
  WithLp.toLp 2 fun S =>
    (Real.sqrt (bernoulliWeight (apertureOcc F σ) S) : ℂ) *
      Complex.exp (((Real.pi * α * (S.card : ℝ)
        - t * linearStat (primeClockVec F) S : ℝ) : ℂ) * Complex.I)

theorem fusionSourceState_ofLp (σ α t : ℝ) (S : Finset F) :
    (fusionSourceState F σ α t).ofLp S
      = (Real.sqrt (bernoulliWeight (apertureOcc F σ) S) : ℂ) *
        Complex.exp (((Real.pi * α * (S.card : ℝ)
          - t * linearStat (primeClockVec F) S : ℝ) : ℂ) * Complex.I) := rfl

theorem bernoulliWeight_apertureOcc_pos (σ : ℝ) (S : Finset F) :
    0 < bernoulliWeight (apertureOcc F σ) S := by
  refine mul_pos (Finset.prod_pos fun p _ => apertureOcc_pos F σ p)
    (Finset.prod_pos fun p _ => ?_)
  linarith [apertureOcc_lt_one F σ p]

theorem norm_fusionSourceState_ofLp (σ α t : ℝ) (S : Finset F) :
    ‖(fusionSourceState F σ α t).ofLp S‖
      = Real.sqrt (bernoulliWeight (apertureOcc F σ) S) := by
  rw [fusionSourceState_ofLp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  simp [Complex.norm_exp]

/-- **The source state is a unit vector.** -/
theorem norm_fusionSourceState (σ α t : ℝ) : ‖fusionSourceState F σ α t‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hterm : ∀ S : Finset F, ‖(fusionSourceState F σ α t).ofLp S‖ ^ 2
      = bernoulliWeight (apertureOcc F σ) S := by
    intro S
    rw [norm_fusionSourceState_ofLp, Real.sq_sqrt (bernoulliWeight_apertureOcc_pos F σ S).le]
  rw [Finset.sum_congr rfl fun S _ => hterm S, sum_bernoulliWeight, Real.sqrt_one]

/-- The clock phase of a configuration is the product of its prime phases. -/
theorem exp_clock_eq_prod_shellFlow (t : ℝ) (S : Finset F) :
    Complex.exp (((-(t * linearStat (primeClockVec F) S) : ℝ) : ℂ) * Complex.I)
      = ∏ p ∈ S, shellFlow (F := F) 1 t p := by
  have hfac : ∀ p : F, shellFlow (F := F) 1 t p
      = Complex.exp (((-(t * primeClockVec F p) : ℝ) : ℂ) * Complex.I) := by
    intro p
    simp [shellFlow, shellGenerator]
  rw [Finset.prod_congr rfl fun p _ => hfac p, ← Complex.exp_sum, ← Finset.sum_mul]
  congr 2
  rw [linearStat]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

theorem norm_fusionSourceState_sub_ofLp (σ t : ℝ) (S : Finset F) :
    ‖(fusionSourceState F σ 0 t).ofLp S - (fusionSourceState F σ 0 0).ofLp S‖ ^ 2
      = bernoulliWeight (apertureOcc F σ) S
        * ‖(∏ p ∈ S, shellFlow (F := F) 1 t p) - 1‖ ^ 2 := by
  have hw := (bernoulliWeight_apertureOcc_pos F σ S).le
  have hphase : Complex.exp (((Real.pi * 0 * (S.card : ℝ)
      - t * linearStat (primeClockVec F) S : ℝ) : ℂ) * Complex.I)
      = ∏ p ∈ S, shellFlow (F := F) 1 t p := by
    rw [← exp_clock_eq_prod_shellFlow]
    congr 2
    push_cast
    ring
  have hone : Complex.exp (((Real.pi * 0 * (S.card : ℝ)
      - 0 * linearStat (primeClockVec F) S : ℝ) : ℂ) * Complex.I) = 1 := by
    norm_num
  rw [fusionSourceState_ofLp, fusionSourceState_ofLp, hphase, hone, ← mul_sub, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hw]

/-- **Recurrence of the pure clock orbit.**  The normalised Boolean source state returns to itself
in norm at arbitrarily late times. -/
theorem fusionSourceState_exists_large_return (σ : ℝ) {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) :
    ∃ t : ℝ, T ≤ t ∧ ‖fusionSourceState F σ 0 t - fusionSourceState F σ 0 0‖ < ε := by
  classical
  set d : ℝ := (Fintype.card F : ℝ) with hd
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hden : (0 : ℝ) < d + 1 := by linarith
  set δ : ℝ := ε / (d + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε hden
  obtain ⟨t, hTt, hflow⟩ := exists_large_return 1 F hδ0 hT
  refine ⟨t, hTt, ?_⟩
  have hunit : ∀ p : F, ‖shellFlow (F := F) 1 t p‖ ≤ 1 := by
    intro p
    simp [shellFlow, Complex.norm_exp]
  have hprod : ∀ S : Finset F, ‖(∏ p ∈ S, shellFlow (F := F) 1 t p) - 1‖ ≤ d * δ := by
    intro S
    refine le_trans (norm_prod_sub_one_le _ hunit S) ?_
    refine le_trans (Finset.sum_le_sum fun p _ => (hflow p).le) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((S.card : ℝ)) ≤ d := by
      rw [hd]
      exact_mod_cast Finset.card_le_univ S
    exact mul_le_mul_of_nonneg_right hcard hδ0.le
  have hbound : ∑ S : Finset F,
      ‖(fusionSourceState F σ 0 t - fusionSourceState F σ 0 0).ofLp S‖ ^ 2 ≤ (d * δ) ^ 2 := by
    have hterm : ∀ S : Finset F,
        ‖(fusionSourceState F σ 0 t - fusionSourceState F σ 0 0).ofLp S‖ ^ 2
          ≤ bernoulliWeight (apertureOcc F σ) S * (d * δ) ^ 2 := by
      intro S
      have hsub : (fusionSourceState F σ 0 t - fusionSourceState F σ 0 0).ofLp S
          = (fusionSourceState F σ 0 t).ofLp S - (fusionSourceState F σ 0 0).ofLp S := rfl
      rw [hsub, norm_fusionSourceState_sub_ofLp]
      refine mul_le_mul_of_nonneg_left ?_ (bernoulliWeight_apertureOcc_pos F σ S).le
      exact pow_le_pow_left₀ (norm_nonneg _) (hprod S) 2
    refine le_trans (Finset.sum_le_sum fun S _ => hterm S) ?_
    rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]
  have hnorm : ‖fusionSourceState F σ 0 t - fusionSourceState F σ 0 0‖ ≤ d * δ := by
    rw [EuclideanSpace.norm_eq]
    have hsqrt := Real.sqrt_le_sqrt hbound
    rwa [Real.sqrt_sq (by positivity)] at hsqrt
  have hlt : d * δ < ε := by
    have hval : d * δ = d * ε / (d + 1) := by rw [hδ]; ring
    rw [hval, div_lt_iff₀ hden]
    nlinarith [hε, hd0]
  linarith

/-- The prime `2` as a marked label. -/
def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The prime `3` as a marked label. -/
def primeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

theorem primeTwo_ne_primeThree : primeTwo ≠ primeThree := by
  intro hcon
  have hval := congrArg Subtype.val hcon
  simp [primeTwo, primeThree] at hval

/-- The two-prime aperture `{2,3}`. -/
def twoPrimeAperture : Finset Nat.Primes := {primeTwo, primeThree}

theorem card_twoPrimeAperture : twoPrimeAperture.card = 2 := by
  rw [twoPrimeAperture,
    Finset.card_insert_of_notMem (by simpa using primeTwo_ne_primeThree),
    Finset.card_singleton]

/-- **The transverse organ is nonzero at the physical half-density source.**  No finite aperture
with two marked primes has vanishing transverse quantum Fisher value, so criticality cannot be
"vanishing transverse information". -/
theorem not_forall_apertureTransverseQFI_eq_zero :
    ¬ ∀ (G : Finset Nat.Primes), 2 ≤ G.card →
        fusionTransverseQFI (apertureWt G 1) (primeClockVec G) = 0 := by
  intro h
  have hmem₂ : primeTwo ∈ twoPrimeAperture := by
    rw [twoPrimeAperture]
    exact Finset.mem_insert_self _ _
  have hmem₃ : primeThree ∈ twoPrimeAperture := by
    rw [twoPrimeAperture]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hsub : (⟨primeTwo, hmem₂⟩ : twoPrimeAperture) ≠ ⟨primeThree, hmem₃⟩ := by
    intro hcon
    exact primeTwo_ne_primeThree (congrArg Subtype.val hcon)
  have hpos := aperture_fusionTransverseQFI_pos (F := twoPrimeAperture) 1 hsub
  rw [h twoPrimeAperture (by rw [card_twoPrimeAperture])] at hpos
  exact lt_irrefl 0 hpos

end State

end

end HTGeometry
