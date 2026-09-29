import GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary
import GaloisForLFunctions.RHTower.PoissonScaleHistoryFrame

/-!
# The Gamma coherent-state ladder of the half line

On `H = L²((0,∞), dr)` put, for a degree `k ≥ 1` and a clock `t > 0`,

`ψ_t^{(k)}(r) = √((2t)^k/(k-1)!) r^{(k-1)/2} e^{-tr}`.

* **(A)** every `ψ_t^{(k)}` is a unit vector and `⟨ψ_t^{(k)}, ψ_u^{(k)}⟩ = (2√(tu)/(t+u))^k`;
  degree two is the Poisson scale history, and `ψ_t^{(3)}(r) = √(tr) ψ_t^{(2)}(r)`.
* **(D)** `mellin ψ_t^{(k)} (s) = √(2^k/(k-1)!) Γ(s+(k-1)/2) t^{1/2-s}` for `Re s > -(k-1)/2`; hence
  `mellin ψ_t^{(3)} = a(s) mellin ψ_t^{(2)}` with the clock-free relative creator
  `a(s) = Γ(s+1)/Γ(s+1/2)`, whose modulus on the unitary line is
  `|a(1/2+iτ)|² = (τ²+1/4) tanh(πτ)/τ`, equal to `π/4` at `τ = 0` and asymptotic to `|τ|`.
* **(E)** for `t ≠ u` no contraction of `H` maps `ψ_t^{(2)} ↦ ψ_t^{(3)}` and `ψ_u^{(2)} ↦ ψ_u^{(3)}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The profiles and the Gram law -/

/-- `ψ_t^{(k)}(r) = √((2t)^k/(k-1)!) r^{(k-1)/2} e^{-tr}`. -/
def gammaCoherentProfile (k : ℕ) (t r : ℝ) : ℝ :=
  Real.sqrt ((2 * t) ^ k / ((k - 1).factorial : ℝ)) * r ^ (((k : ℝ) - 1) / 2) *
    Real.exp (-(t * r))

theorem gammaCoherentProfile_mul {k : ℕ} {t u r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    gammaCoherentProfile k t r * gammaCoherentProfile k u r =
      Real.sqrt ((4 * t * u) ^ k) / ((k - 1).factorial : ℝ) *
        (r ^ ((k : ℝ) - 1) * Real.exp (-((t + u) * r))) := by
  have hf : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hsq : Real.sqrt ((2 * t) ^ k / ((k - 1).factorial : ℝ)) *
      Real.sqrt ((2 * u) ^ k / ((k - 1).factorial : ℝ)) =
        Real.sqrt ((4 * t * u) ^ k) / ((k - 1).factorial : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (2 * t) ^ k / ((k - 1).factorial : ℝ) * ((2 * u) ^ k / ((k - 1).factorial : ℝ)) =
        (4 * t * u) ^ k / ((k - 1).factorial : ℝ) ^ 2 by
      rw [div_mul_div_comm, ← mul_pow, sq]
      ring_nf]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hf.le]
  have hrpow : r ^ (((k : ℝ) - 1) / 2) * r ^ (((k : ℝ) - 1) / 2) = r ^ ((k : ℝ) - 1) := by
    rw [← Real.rpow_add hr]
    ring_nf
  have hexp : Real.exp (-(t * r)) * Real.exp (-(u * r)) = Real.exp (-((t + u) * r)) := by
    rw [← Real.exp_add]
    ring_nf
  calc gammaCoherentProfile k t r * gammaCoherentProfile k u r
      = (Real.sqrt ((2 * t) ^ k / ((k - 1).factorial : ℝ)) *
          Real.sqrt ((2 * u) ^ k / ((k - 1).factorial : ℝ))) *
        (r ^ (((k : ℝ) - 1) / 2) * r ^ (((k : ℝ) - 1) / 2)) *
        (Real.exp (-(t * r)) * Real.exp (-(u * r))) := by
          unfold gammaCoherentProfile
          ring
    _ = _ := by rw [hsq, hrpow, hexp]; ring

/-- `Γ(k) = (k-1)!` as a real number. -/
theorem gamma_natCast_eq_factorial_pred {k : ℕ} (hk : k ≠ 0) :
    Real.Gamma (k : ℝ) = ((k - 1).factorial : ℝ) := by
  have h := Real.Gamma_nat_eq_factorial (k - 1)
  rwa [show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk)]
    push_cast
    ring] at h

/-- `∫₀^∞ r^{k-1} e^{-ar} dr = (k-1)!/a^k`. -/
theorem integral_rpow_pred_mul_exp {k : ℕ} (hk : k ≠ 0) {a : ℝ} (ha : 0 < a) :
    ∫ r in Ioi (0 : ℝ), r ^ ((k : ℝ) - 1) * Real.exp (-(a * r)) =
      ((k - 1).factorial : ℝ) / a ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hkpos ha, gamma_natCast_eq_factorial_pred hk,
    Real.rpow_natCast, one_div, inv_pow]
  ring

/-- **(PPTI.3).**  `∫ ψ_t^{(k)} ψ_u^{(k)} = (2√(tu)/(t+u))^k`. -/
theorem integral_gammaCoherentProfile_mul {k : ℕ} (hk : k ≠ 0) {t u : ℝ} (ht : 0 < t)
    (hu : 0 < u) :
    ∫ r in Ioi (0 : ℝ), gammaCoherentProfile k t r * gammaCoherentProfile k u r =
      (2 * Real.sqrt (t * u) / (t + u)) ^ k := by
  have hf : (0 : ℝ) < ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [setIntegral_congr_fun measurableSet_Ioi fun r hr => gammaCoherentProfile_mul (u := u) ht hr,
    integral_const_mul, integral_rpow_pred_mul_exp hk (add_pos ht hu)]
  have hx2 : (2 * Real.sqrt (t * u)) ^ 2 = 4 * t * u := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hroot : Real.sqrt ((4 * t * u) ^ k) = (2 * Real.sqrt (t * u)) ^ k := by
    rw [show (4 * t * u) ^ k = ((2 * Real.sqrt (t * u)) ^ k) ^ 2 by
      rw [← pow_mul, mul_comm k 2, pow_mul, hx2]]
    exact Real.sqrt_sq (by positivity)
  rw [hroot, div_pow]
  field_simp

theorem aestronglyMeasurable_gammaCoherentProfile (k : ℕ) (t : ℝ) (μ : Measure ℝ) :
    AEStronglyMeasurable (gammaCoherentProfile k t) μ := by
  have h : Measurable (gammaCoherentProfile k t) := by
    unfold gammaCoherentProfile
    fun_prop
  exact h.aestronglyMeasurable

theorem memLp_gammaCoherentProfile {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t) :
    MemLp (fun r => (gammaCoherentProfile k t r : ℂ)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  suffices h : MemLp (gammaCoherentProfile k t) 2 (volume.restrict (Ioi (0 : ℝ))) from h.ofReal
  rw [memLp_two_iff_integrable_sq (aestronglyMeasurable_gammaCoherentProfile k t _)]
  have hkpos : (-1 : ℝ) < (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    linarith
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow hkpos le_rfl (by positivity : 0 < 2 * t)
  have hbase' : IntegrableOn (fun r : ℝ => Real.sqrt ((4 * t * t) ^ k) /
      ((k - 1).factorial : ℝ) * (r ^ ((k : ℝ) - 1) * Real.exp (-((t + t) * r)))) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hbase.const_mul (Real.sqrt ((4 * t * t) ^ k) /
      ((k - 1).factorial : ℝ))) (fun r _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    ring_nf
  refine hbase'.congr_fun (fun r hr => ?_) measurableSet_Ioi
  rw [sq, gammaCoherentProfile_mul (u := t) ht hr]

/-- The coherent vector `ψ_t^{(k)} ∈ L²((0,∞), dr)`. -/
def gammaCoherentVector (k : ℕ) [NeZero k] {t : ℝ} (ht : 0 < t) : HalfLineL2 :=
  (memLp_gammaCoherentProfile (NeZero.ne k) ht).toLp _

theorem gammaCoherentVector_ae (k : ℕ) [NeZero k] {t : ℝ} (ht : 0 < t) :
    (gammaCoherentVector k ht : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      fun r => (gammaCoherentProfile k t r : ℂ) :=
  (memLp_gammaCoherentProfile (NeZero.ne k) ht).coeFn_toLp

/-- **Theorem PPTI-A.**  `⟨ψ_t^{(k)}, ψ_u^{(k)}⟩ = (2√(tu)/(t+u))^k`. -/
theorem inner_gammaCoherentVector (k : ℕ) [NeZero k] {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    ⟪gammaCoherentVector k ht, gammaCoherentVector k hu⟫_ℂ =
      (((2 * Real.sqrt (t * u) / (t + u)) ^ k : ℝ) : ℂ) := by
  rw [L2.inner_def, ← integral_gammaCoherentProfile_mul (NeZero.ne k) ht hu,
    ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [gammaCoherentVector_ae k ht, gammaCoherentVector_ae k hu] with r h1 h2
  rw [h1, h2, RCLike.inner_apply, Complex.conj_ofReal]
  push_cast
  ring

theorem norm_gammaCoherentVector (k : ℕ) [NeZero k] {t : ℝ} (ht : 0 < t) :
    ‖gammaCoherentVector k ht‖ = 1 := by
  have h := inner_gammaCoherentVector k ht ht
  rw [Real.sqrt_mul_self ht.le, show 2 * t / (t + t) = 1 by field_simp; ring, one_pow,
    Complex.ofReal_one, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖gammaCoherentVector k ht‖ ^ 2 = 1 := by
    have h'' : ((‖gammaCoherentVector k ht‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      exact h
    exact Complex.ofReal_injective h''
  nlinarith [norm_nonneg (gammaCoherentVector k ht)]

/-- **(PPTI.4).**  Degree two is the Poisson scale history. -/
theorem gammaCoherentProfile_two {t : ℝ} (ht : 0 < t) (r : ℝ) :
    gammaCoherentProfile 2 t r = poissonScaleHistory t r := by
  have h1 : Real.sqrt ((2 * t) ^ 2 / (Nat.factorial (2 - 1) : ℝ)) = 2 * t := by
    rw [show (Nat.factorial (2 - 1) : ℝ) = 1 by norm_num, div_one]
    exact Real.sqrt_sq (by positivity)
  have h2 : r ^ ((((2 : ℕ) : ℝ) - 1) / 2) = Real.sqrt r := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [gammaCoherentProfile, poissonScaleHistory, h1, h2]

/-- **(PPTI.5).**  `poissonScaleHistoryGram t u = (2√(tu)/(t+u))²`. -/
theorem poissonScaleHistoryGram_eq_coherent {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    poissonScaleHistoryGram t u = (2 * Real.sqrt (t * u) / (t + u)) ^ 2 := by
  rw [poissonScaleHistoryGram_eq ht hu, div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- **(PPTI.6).**  `ψ_t^{(3)}(r) = 2 t^{3/2} r e^{-tr}`. -/
theorem gammaCoherentProfile_three {t r : ℝ} (ht : 0 < t) :
    gammaCoherentProfile 3 t r = 2 * t ^ ((3 : ℝ) / 2) * r * Real.exp (-(t * r)) := by
  have ht3 : (t ^ ((3 : ℝ) / 2)) ^ 2 = t ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have h1 : Real.sqrt ((2 * t) ^ 3 / (Nat.factorial (3 - 1) : ℝ)) = 2 * t ^ ((3 : ℝ) / 2) := by
    rw [show (Nat.factorial (3 - 1) : ℝ) = 2 by norm_num,
      show (2 * t) ^ 3 / 2 = (2 * t ^ ((3 : ℝ) / 2)) ^ 2 by
        rw [show (2 * t ^ ((3 : ℝ) / 2)) ^ 2 = 4 * (t ^ ((3 : ℝ) / 2)) ^ 2 by ring, ht3]
        ring]
    exact Real.sqrt_sq (by positivity)
  have h2 : r ^ ((((3 : ℕ) : ℝ) - 1) / 2) = r := by norm_num
  rw [gammaCoherentProfile, h1, h2]

/-- **(PPTI.22).**  `ψ_t^{(3)}(r) = √(tr) ψ_t^{(2)}(r)`. -/
theorem gammaCoherentProfile_three_eq {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    gammaCoherentProfile 3 t r = Real.sqrt (t * r) * gammaCoherentProfile 2 t r := by
  rw [gammaCoherentProfile_three ht, gammaCoherentProfile_two ht r, poissonScaleHistory,
    Real.sqrt_mul ht.le]
  have h1 : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht,
      Real.rpow_one]
  have h2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  rw [h1]
  linear_combination (2 * t * Real.sqrt t * Real.exp (-(t * r))) * h2.symm

/-! ## Mellin transforms and the relative creator -/

theorem mellin_congr_Ioi {f g : ℝ → ℂ} (h : EqOn f g (Ioi 0)) (s : ℂ) :
    mellin f s = mellin g s := by
  unfold mellin
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [h hr]

/-- **(PPTI.24).**  `mellin ψ_t^{(k)} (s) = √(2^k/(k-1)!) Γ(s+(k-1)/2) t^{1/2-s}`. -/
theorem mellin_gammaCoherentProfile {k : ℕ} {t : ℝ} (ht : 0 < t) {s : ℂ}
    (hs : 0 < (s + (((k : ℝ) - 1) / 2 : ℝ)).re) :
    mellin (fun r => (gammaCoherentProfile k t r : ℂ)) s =
      (Real.sqrt (2 ^ k / ((k - 1).factorial : ℝ)) : ℂ) *
        Complex.Gamma (s + (((k : ℝ) - 1) / 2 : ℝ)) * (t : ℂ) ^ ((1 / 2 : ℂ) - s) := by
  set α : ℝ := ((k : ℝ) - 1) / 2
  set C : ℝ := Real.sqrt ((2 * t) ^ k / ((k - 1).factorial : ℝ))
  have hcongr : EqOn (fun r => (gammaCoherentProfile k t r : ℂ))
      (fun r => (C : ℂ) • ((r : ℂ) ^ (α : ℂ) * ((Real.exp (-(t * r)) : ℝ) : ℂ))) (Ioi 0) := by
    intro r hr
    simp only [gammaCoherentProfile, smul_eq_mul]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt hr)]
    ring
  rw [mellin_congr_Ioi hcongr, mellin_const_smul, mellin_cpow_mul_exp_neg_mul ht _ _ hs,
    smul_eq_mul]
  have hsqrt : Real.sqrt (t ^ k) = t ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    ring_nf
  have hC : (C : ℂ) = (Real.sqrt (2 ^ k / ((k - 1).factorial : ℝ)) : ℂ) *
      (t : ℂ) ^ (((k : ℝ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow ht.le, ← Complex.ofReal_mul]
    congr 1
    simp only [C]
    rw [mul_pow, mul_comm (2 ^ k) (t ^ k), mul_div_assoc,
      Real.sqrt_mul (pow_nonneg ht.le k), hsqrt, mul_comm]
  rw [hC]
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ (((k : ℝ) / 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + (α : ℂ))) =
      (t : ℂ) ^ ((1 / 2 : ℂ) - s) := by
    rw [← Complex.cpow_add _ _ ht0]
    congr 1
    simp only [α]
    push_cast
    ring
  rw [← hpow]
  ring

/-- The relative creator `a(s) = Γ(s+1)/Γ(s+1/2)`. -/
def mellinRelativeCreator (s : ℂ) : ℂ := Complex.Gamma (s + 1) / Complex.Gamma (s + 1 / 2)

/-- **(PPTI.25).**  `mellin ψ_t^{(3)} = a · mellin ψ_t^{(2)}` for `Re s > -1/2`. -/
theorem mellin_gammaCoherent_three_eq {t : ℝ} (ht : 0 < t) {s : ℂ} (hs : -(1 / 2) < s.re) :
    mellin (fun r => (gammaCoherentProfile 3 t r : ℂ)) s =
      mellinRelativeCreator s * mellin (fun r => (gammaCoherentProfile 2 t r : ℂ)) s := by
  have h2 : 0 < (s + ((((2 : ℕ) : ℝ) - 1) / 2 : ℝ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num
    linarith
  have h3 : 0 < (s + ((((3 : ℕ) : ℝ) - 1) / 2 : ℝ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num
    linarith
  rw [mellin_gammaCoherentProfile ht h3, mellin_gammaCoherentProfile ht h2, mellinRelativeCreator]
  have hΓ : Complex.Gamma (s + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.add_re]
    norm_num
    linarith)
  norm_num
  rw [div_mul_eq_mul_div, eq_div_iff hΓ]
  ring

/-- **(PPTI.27).**  On the unitary line every prime-clock character has modulus one. -/
theorem norm_clock_character_unitary {t : ℝ} (ht : 0 < t) (τ : ℝ) :
    ‖(t : ℂ) ^ ((1 / 2 : ℂ) - (1 / 2 + τ * Complex.I))‖ = 1 := by
  rw [show (1 / 2 : ℂ) - (1 / 2 + τ * Complex.I) = ((-τ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

theorem Gamma_mul_Gamma_conj_eq (z : ℂ) :
    Complex.Gamma z * Complex.Gamma (conj z) = ((Complex.normSq (Complex.Gamma z) : ℝ) : ℂ) := by
  rw [Complex.Gamma_conj, Complex.mul_conj]

/-- `Γ(1+iτ)Γ(1-iτ) = πτ/sinh(πτ)`. -/
theorem Gamma_one_add_mul_I_mul_conj {τ : ℝ} (hτ : τ ≠ 0) :
    Complex.Gamma (1 + τ * Complex.I) * Complex.Gamma (1 - τ * Complex.I) =
      Real.pi * τ / Real.sinh (Real.pi * τ) := by
  have hz : (τ * Complex.I : ℂ) ≠ 0 := by simp [hτ]
  rw [add_comm, Complex.Gamma_add_one _ hz, mul_assoc, Complex.Gamma_mul_Gamma_one_sub,
    show (Real.pi : ℂ) * (τ * Complex.I) = ((Real.pi * τ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hs : Real.sinh (Real.pi * τ) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hτ
  have hs' : ((Real.sinh (Real.pi * τ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp

/-- `Γ(3/2+iτ)Γ(3/2-iτ) = (τ²+1/4) π/cosh(πτ)`. -/
theorem Gamma_three_halves_add_mul_I_mul_conj (τ : ℝ) :
    Complex.Gamma (3 / 2 + τ * Complex.I) * Complex.Gamma (3 / 2 - τ * Complex.I) =
      (τ ^ 2 + 1 / 4) * Real.pi / Real.cosh (Real.pi * τ) := by
  have h1 : (3 / 2 + τ * Complex.I : ℂ) = (1 / 2 + τ * Complex.I) + 1 := by ring
  have h2 : (3 / 2 - τ * Complex.I : ℂ) = (1 / 2 - τ * Complex.I) + 1 := by ring
  have hz1 : (1 / 2 + τ * Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hz2 : (1 / 2 - τ * Complex.I : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [h1, h2, Complex.Gamma_add_one _ hz1, Complex.Gamma_add_one _ hz2]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + τ * Complex.I)
  rw [show (1 : ℂ) - (1 / 2 + τ * Complex.I) = 1 / 2 - τ * Complex.I by ring,
    show (Real.pi : ℂ) * (1 / 2 + τ * Complex.I) =
      Real.pi / 2 + ((Real.pi * τ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.sin_add, Complex.sin_mul_I, Complex.cos_mul_I,
    show Complex.sin (Real.pi / 2) = 1 by exact_mod_cast Real.sin_pi_div_two,
    show Complex.cos (Real.pi / 2) = 0 by exact_mod_cast Real.cos_pi_div_two,
    ← Complex.ofReal_cosh] at hrefl
  simp only [one_mul, zero_mul, add_zero] at hrefl
  have hc : ((Real.cosh (Real.pi * τ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hprod : (1 / 2 + τ * Complex.I) * (1 / 2 - τ * Complex.I) =
      ((τ ^ 2 + 1 / 4 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  calc (1 / 2 + τ * Complex.I) * Complex.Gamma (1 / 2 + τ * Complex.I) *
        ((1 / 2 - τ * Complex.I) * Complex.Gamma (1 / 2 - τ * Complex.I))
      = ((1 / 2 + τ * Complex.I) * (1 / 2 - τ * Complex.I)) *
        (Complex.Gamma (1 / 2 + τ * Complex.I) * Complex.Gamma (1 / 2 - τ * Complex.I)) := by ring
    _ = _ := by
      rw [hrefl, hprod]
      field_simp
      push_cast
      ring

/-- **(PPTI.28).**  `|a(1/2+iτ)|² = (τ²+1/4) tanh(πτ)/τ` for `τ ≠ 0`. -/
theorem normSq_mellinRelativeCreator {τ : ℝ} (hτ : τ ≠ 0) :
    Complex.normSq (mellinRelativeCreator (1 / 2 + τ * Complex.I)) =
      (τ ^ 2 + 1 / 4) * Real.tanh (Real.pi * τ) / τ := by
  have hnum : ((Complex.normSq (Complex.Gamma (3 / 2 + τ * Complex.I)) : ℝ) : ℂ) =
      (((τ ^ 2 + 1 / 4) * Real.pi / Real.cosh (Real.pi * τ) : ℝ) : ℂ) := by
    rw [← Gamma_mul_Gamma_conj_eq, show conj (3 / 2 + τ * Complex.I : ℂ) =
      3 / 2 - τ * Complex.I by
        rw [map_add, map_div₀, map_ofNat, map_ofNat, map_mul, Complex.conj_ofReal,
          Complex.conj_I]
        ring,
      Gamma_three_halves_add_mul_I_mul_conj]
    push_cast
    ring
  have hden : ((Complex.normSq (Complex.Gamma (1 + τ * Complex.I)) : ℝ) : ℂ) =
      ((Real.pi * τ / Real.sinh (Real.pi * τ) : ℝ) : ℂ) := by
    rw [← Gamma_mul_Gamma_conj_eq, show conj (1 + τ * Complex.I : ℂ) = 1 - τ * Complex.I by
        rw [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring,
      Gamma_one_add_mul_I_mul_conj hτ]
    push_cast
    ring
  have hnum' := Complex.ofReal_injective hnum
  have hden' := Complex.ofReal_injective hden
  rw [mellinRelativeCreator, Complex.normSq_div,
    show (1 / 2 + τ * Complex.I + 1 : ℂ) = 1 + τ * Complex.I + 1 / 2 by ring,
    show (1 / 2 + τ * Complex.I + 1 / 2 : ℂ) = 1 + τ * Complex.I by ring,
    show (1 + τ * Complex.I + 1 / 2 : ℂ) = 3 / 2 + τ * Complex.I by ring, hnum', hden',
    Real.tanh_eq_sinh_div_cosh]
  have hs : Real.sinh (Real.pi * τ) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero hτ
  have hc := (Real.cosh_pos (Real.pi * τ)).ne'
  field_simp

/-- At `τ = 0`: `|a(1/2)|² = π/4`. -/
theorem normSq_mellinRelativeCreator_half :
    Complex.normSq (mellinRelativeCreator (1 / 2)) = Real.pi / 4 := by
  have h1 : Complex.Gamma (1 / 2 + 1) = ((Real.sqrt Real.pi / 2 : ℝ) : ℂ) := by
    rw [show (1 / 2 + 1 : ℂ) = ((1 / 2 + 1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    push_cast
    ring
  rw [mellinRelativeCreator, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.Gamma_one, div_one,
    h1, Complex.normSq_ofReal]
  have := Real.mul_self_sqrt Real.pi_pos.le
  nlinarith

/-- `tanh x → 1` as `x → ∞`. -/
theorem tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  have he : Tendsto (fun x : ℝ => Real.exp (-(2 * x))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop two_pos)
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub he).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add he) (by norm_num)
  rw [sub_zero, add_zero, div_one] at h
  refine h.congr fun x => ?_
  show (1 - Real.exp (-(2 * x))) / (1 + Real.exp (-(2 * x))) = Real.tanh x
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hx := Real.exp_pos x
  have h2 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [h2]
  field_simp
  nlinarith [h3]

/-- The metric anomaly has order `|τ|`: `|a(1/2+iτ)|²/τ → 1` as `τ → ∞`. -/
theorem tendsto_normSq_mellinRelativeCreator_div :
    Tendsto (fun τ : ℝ => Complex.normSq (mellinRelativeCreator (1 / 2 + τ * Complex.I)) / τ)
      atTop (𝓝 1) := by
  have htanh : Tendsto (fun τ : ℝ => Real.tanh (Real.pi * τ)) atTop (𝓝 1) :=
    tendsto_tanh_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)
  have hrat : Tendsto (fun τ : ℝ => 1 + 1 / 4 * (τ ^ 2)⁻¹) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)).const_mul (1 / 4 : ℝ))
    rw [mul_zero, add_zero] at h
    exact h
  have h := hrat.mul htanh
  rw [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with τ hτ
  rw [normSq_mellinRelativeCreator hτ.ne']
  field_simp

/-! ## No contractive two-clock transporter -/

/-- A contraction preserving the norms of two vectors preserves their inner product. -/
theorem inner_map_eq_of_norm_le_one {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (L : E →L[ℂ] F) (hL : ‖L‖ ≤ 1) {x y : E}
    (hx : ‖L x‖ = ‖x‖) (hy : ‖L y‖ = ‖y‖) : ⟪L x, L y⟫_ℂ = ⟪x, y⟫_ℂ := by
  set d := ⟪L x, L y⟫_ℂ - ⟪x, y⟫_ℂ
  have key : ∀ c : ℂ, (c * d).re ≤ 0 := by
    intro c
    have hle : ‖L (x + c • y)‖ ^ 2 ≤ ‖x + c • y‖ ^ 2 := by
      have := L.le_opNorm (x + c • y)
      exact pow_le_pow_left₀ (norm_nonneg _) (this.trans (by nlinarith [norm_nonneg (x + c • y)])) 2
    rw [map_add, map_smul, @norm_add_sq ℂ, @norm_add_sq ℂ, inner_smul_right, inner_smul_right,
      norm_smul, norm_smul, hx, hy] at hle
    have : (c * ⟪L x, L y⟫_ℂ).re ≤ (c * ⟪x, y⟫_ℂ).re := by
      simp only [RCLike.re_to_complex] at hle
      nlinarith
    simp only [d, mul_sub, Complex.sub_re]
    linarith
  have h := key (conj d)
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] at h
  have : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **Theorem PPTI-E.**  For distinct clocks no contraction of `H` sends both degree-two coherent
vectors to the corresponding degree-three ones. -/
theorem not_exists_contraction_gammaCoherent {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (htu : t ≠ u) :
    ¬ ∃ L : HalfLineL2 →L[ℂ] HalfLineL2, ‖L‖ ≤ 1 ∧
      L (gammaCoherentVector 2 ht) = gammaCoherentVector 3 ht ∧
      L (gammaCoherentVector 2 hu) = gammaCoherentVector 3 hu := by
  rintro ⟨L, hL, h1, h2⟩
  have hin := inner_map_eq_of_norm_le_one L hL
    (by rw [h1, norm_gammaCoherentVector, norm_gammaCoherentVector])
    (by rw [h2, norm_gammaCoherentVector, norm_gammaCoherentVector])
  rw [h1, h2, inner_gammaCoherentVector, inner_gammaCoherentVector] at hin
  have hin' := Complex.ofReal_injective hin
  set g := 2 * Real.sqrt (t * u) / (t + u)
  have hg0 : 0 < g := by positivity
  have hg1 : g < 1 := by
    rw [div_lt_one (by positivity)]
    have hsq : (Real.sqrt t - Real.sqrt u) ^ 2 > 0 := by
      have : Real.sqrt t ≠ Real.sqrt u := fun h =>
        htu ((Real.sqrt_inj ht.le hu.le).1 h)
      positivity
    rw [Real.sqrt_mul ht.le]
    nlinarith [Real.sq_sqrt ht.le, Real.sq_sqrt hu.le]
  have : g ^ 3 < g ^ 2 := pow_lt_pow_right_of_lt_one₀ hg0 hg1 (by norm_num)
  linarith

end GaloisForLFunctions.HTGeometry
