import GaloisForLFunctions.BlackHoleRingdown.TheEternalAdSPrimeMarkedDictionary
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateIsTheZeroFreeRegion
import GaloisForLFunctions.RHTower.DirichletLReciprocalRightOfTheOneLine
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.ArithmeticScatteringHolography.ThePhysicalPositivitiesAreBlind
import GaloisForLFunctions.CompactHyperbolicSurfaces.CyclicCovers
import GaloisForLFunctions.CompactHyperbolicSurfaces.SmallEigenvalueZeta

/-!
# Causal Identities Cannot Force Quarter-Rate Modular Ringdown

This module resolves the dynamical half of the eternal-AdS / modular-horizon problem:

1. **Prime-2 Retarded Echo Family (`1/2 < α < 1`)** (`primeTwoFactor`, `xiDeformed`,
   `primeTwoScatteringGate`, `deformedEchoKernel`, `deformedReflectedField`):
   - Replaces the prime-`2` cusp scattering factor by the Schur symbol
     `B_{2,α}(w) = (1 - t_α 2^{-2w} + 2·2^{-4w}) / (2 - t_α 2^{-2w} + 2^{-4w})`
     with `t_α = 2^α + 2^{1-α} ∈ (2√2, 3)`.
   - Realizes `B_{2,α}(w) · Λ(2w)/Λ(2w+1)` on `Re w > 1/2` as the Laplace transform of an explicit
     real retarded echo kernel `deformedEchoKernel α τ` supported strictly on `τ > 0` (`= 0` for
     `τ ≤ 0`), with convergent rational-prime Euler product over `Nat.Primes`.
   - Preserves the completed functional equation `ξ_α(1 - s) = ξ_α(s)`, conjugation symmetry,
     global Lax–Phillips Schur passivity `‖ξ_α(2w)/ξ_α(1+2w)‖ ≤ 1` across `Re w ≥ 0`, positive
     Herglotz boundary admittance, continuous-spectrum unitarity `‖φ_α(it)‖ = 1` on `ℝ`, and the
     complete single- and two-boundary (`G_{R,α}` and `G_{RL,α}`) zero-to-pole multiplicity
     dictionary (including every nontrivial zero of `ζ`).
   - Proves unconditionally that reflected compact pulses decay as `O(e^{-σ τ})` for every
     `0 < σ < min(1/16, (1 - α)/2)` (`deformedReflectedField_decay`), while the smooth compactly
     supported pulse `excitingPulse (((α : ℂ) - 1) / 2)` **violates** `O(e^{-δ τ})` for every
     `δ > (1 - α)/2` (`not_deformedReflectedField_decay_gt`).
   - Consequently (`universal_causal_ringdown_infimum_zero`), for every `δ > 0` (and in particular
     `δ = 1/4` and `δ = 1/16`), there exists `α ∈ (7/8, 1)` obeying all causal, Euler-product,
     Schur-passive, unitary, KMS, functional-equation, and boundary-dictionary laws whose reflected
     pulse fails `O(e^{-δ τ})`.

2. **4D Vacuum Einstein–AdS Bulk + Locally Tempered Geodesic Obstruction**
   (`exists_eternalAdS_compact_blackHole_violating_quarter_decay`):
   - Glues the `SL₂(ℝ)`-equivariant two-boundary Kruskal–Maldacena `AdS₄` spacetime to a cocompact
     torsion-free quaternion cover `Γ_n = coverGroup n ≤ SL₂(ℝ)` (`Odd n`, `3 ≤ n`).
   - Every primitive closed-geodesic Euler factor `1 - e^{-(s+k)ℓ_p}` vanishes only on
     `Re s = -k ≤ 0` (locally tempered), and `logDeriv Z_{Γ_n}` agrees with `lengthSeries` on
     `Re s > 1` while having a simple pole (`meromorphicOrderAt = -1`) at every zero of `Z_{Γ_n}`
     on `Re s > 0`, yet `Z_{Γ_n}` has a real off-line zero `s₀ ∈ (1/2, 1)` violating quarter-rate
     damping `(1 - Re s₀)/2 < 1/4`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups ContDiff FourierTransform

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography (schurNum schurDen schur_bound_iff)
open GaloisForLFunctions.CompactHyperbolicSurfaces
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
  (riemannZeta_zero_mem_quasiRH_strip)

noncomputable section

/-! ## 1. Prime-2 Schur Echo Gate and Deformed Completed Zeta -/

/-- Deformed prime-`2` trace parameter `t_α = 2^α + 2^{1 - α}`. -/
def primeTwoTrace (α : ℝ) : ℝ :=
  (2 : ℝ) ^ α + (2 : ℝ) ^ (1 - α)

/-- For `0 < α < 1`, `0 < primeTwoTrace α` and `|primeTwoTrace α| < 3 = 2 + 1`. -/
theorem primeTwoTrace_pos_and_lt_three {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    0 < primeTwoTrace α ∧ |primeTwoTrace α| < 3 := by
  set u : ℝ := (2 : ℝ) ^ α with hudef
  have hu_pos : 0 < u := Real.rpow_pos_of_pos (by norm_num) α
  have hu1 : 1 < u := Real.one_lt_rpow (by norm_num) h0
  have hu2 : u < 2 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
  have hprod : (2 : ℝ) ^ (1 - α) * u = 2 := by
    rw [hudef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hdiv : (2 : ℝ) ^ (1 - α) = 2 / u := (eq_div_iff hu_pos.ne').mpr hprod
  have htr : primeTwoTrace α = u + 2 / u := by rw [primeTwoTrace, hudef, hdiv]
  have hpos : 0 < primeTwoTrace α := by rw [htr]; positivity
  refine ⟨hpos, ?_⟩
  rw [abs_of_pos hpos, htr]
  have hdiff : 3 - (u + 2 / u) = (u - 1) * (2 - u) / u := by
    field_simp
    ring
  have hpos_diff : 0 < 3 - (u + 2 / u) := by
    rw [hdiff]
    exact div_pos (mul_pos (by linarith) (by linarith)) hu_pos
  linarith

/-- Self-dual entire prime-`2` deformation factor
`E_{2,α}(s) = 2^{s - 1/2} (1 - 2^{α - s}) (1 - 2^{1 - α - s})`. -/
def primeTwoFactor (α : ℝ) (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (s - 1 / 2) * (1 - (2 : ℂ) ^ ((α : ℂ) - s)) *
    (1 - (2 : ℂ) ^ (((1 - α : ℝ) : ℂ) - s))

private theorem two_cpow_eq_exp (z : ℂ) :
    (2 : ℂ) ^ z = Complex.exp (z * ((Real.log 2 : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero two_ne_zero,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2),
    mul_comm]

private theorem differentiable_two_cpow {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun s => (2 : ℂ) ^ f s) := by
  have heq : (fun s => (2 : ℂ) ^ f s) = fun s => Complex.exp (f s * ((Real.log 2 : ℝ) : ℂ)) := by
    funext s; exact two_cpow_eq_exp (f s)
  rw [heq]
  exact (hf.mul_const _).cexp

/-- `primeTwoFactor α` is entire. -/
theorem differentiable_primeTwoFactor (α : ℝ) : Differentiable ℂ (primeTwoFactor α) := by
  unfold primeTwoFactor
  exact ((differentiable_two_cpow (by fun_prop)).mul
    ((differentiable_const 1).sub (differentiable_two_cpow (by fun_prop)))).mul
    ((differentiable_const 1).sub (differentiable_two_cpow (by fun_prop)))

/-- Functional equation `primeTwoFactor α (1 - s) = primeTwoFactor α s`. -/
theorem primeTwoFactor_one_sub (α : ℝ) (s : ℂ) :
    primeTwoFactor α (1 - s) = primeTwoFactor α s := by
  set L : ℂ := ((Real.log 2 : ℝ) : ℂ)
  have hexpand : ∀ z : ℂ, primeTwoFactor α z =
      Complex.exp ((z - 1 / 2) * L) - Complex.exp (((α : ℂ) - 1 / 2) * L) -
        Complex.exp ((1 / 2 - (α : ℂ)) * L) + Complex.exp ((1 / 2 - z) * L) := by
    intro z
    unfold primeTwoFactor
    simp only [two_cpow_eq_exp]
    have h1a : ((1 - α : ℝ) : ℂ) = 1 - (α : ℂ) := by push_cast; ring
    rw [h1a]
    have e1 : Complex.exp ((z - 1 / 2) * L) * Complex.exp (((α : ℂ) - z) * L) =
        Complex.exp (((α : ℂ) - 1 / 2) * L) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e2 : Complex.exp ((z - 1 / 2) * L) * Complex.exp ((1 - (α : ℂ) - z) * L) =
        Complex.exp ((1 / 2 - (α : ℂ)) * L) := by
      rw [← Complex.exp_add]; congr 1; ring
    have e3 : Complex.exp (((α : ℂ) - 1 / 2) * L) * Complex.exp ((1 - (α : ℂ) - z) * L) =
        Complex.exp ((1 / 2 - z) * L) := by
      rw [← Complex.exp_add]; congr 1; ring
    calc Complex.exp ((z - 1 / 2) * L) * (1 - Complex.exp (((α : ℂ) - z) * L)) *
            (1 - Complex.exp ((1 - (α : ℂ) - z) * L))
        = (Complex.exp ((z - 1 / 2) * L) -
            Complex.exp ((z - 1 / 2) * L) * Complex.exp (((α : ℂ) - z) * L)) *
          (1 - Complex.exp ((1 - (α : ℂ) - z) * L)) := by ring
      _ = (Complex.exp ((z - 1 / 2) * L) - Complex.exp (((α : ℂ) - 1 / 2) * L)) *
          (1 - Complex.exp ((1 - (α : ℂ) - z) * L)) := by rw [e1]
      _ = Complex.exp ((z - 1 / 2) * L) -
            Complex.exp ((z - 1 / 2) * L) * Complex.exp ((1 - (α : ℂ) - z) * L) -
            Complex.exp (((α : ℂ) - 1 / 2) * L) +
            Complex.exp (((α : ℂ) - 1 / 2) * L) * Complex.exp ((1 - (α : ℂ) - z) * L) := by ring
      _ = _ := by rw [e2, e3]; ring
  rw [hexpand (1 - s), hexpand s]
  have h1 : (1 - s - 1 / 2) * L = (1 / 2 - s) * L := by ring
  have h2 : (1 / 2 - (1 - s)) * L = (s - 1 / 2) * L := by ring
  rw [h1, h2]
  ring

/-- Conjugation symmetry `primeTwoFactor α (conj s) = conj (primeTwoFactor α s)`. -/
theorem primeTwoFactor_conj (α : ℝ) (s : ℂ) :
    primeTwoFactor α (starRingEnd ℂ s) = starRingEnd ℂ (primeTwoFactor α s) := by
  have hcpow : ∀ z : ℂ, (2 : ℂ) ^ (starRingEnd ℂ z) = starRingEnd ℂ ((2 : ℂ) ^ z) := by
    intro z
    rw [two_cpow_eq_exp, two_cpow_eq_exp, ← Complex.exp_conj]
    simp
  unfold primeTwoFactor
  simp only [map_mul, map_sub, map_one, ← hcpow]
  congr 3
  · simp
  · simp
  · simp

/-- Any zero of `primeTwoFactor α` has real part `α` or `1 - α`. -/
theorem re_eq_of_primeTwoFactor_eq_zero {α : ℝ} {s : ℂ} (hz : primeTwoFactor α s = 0) :
    s.re = α ∨ s.re = 1 - α := by
  have hne0 : (2 : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [two_cpow_eq_exp]; exact Complex.exp_ne_zero _
  unfold primeTwoFactor at hz
  rcases mul_eq_zero.mp hz with h12 | h3
  · have h2 : 1 - (2 : ℂ) ^ ((α : ℂ) - s) = 0 := (mul_eq_zero.mp h12).resolve_left hne0
    have heq1 : (2 : ℂ) ^ ((α : ℂ) - s) = 1 := (sub_eq_zero.mp h2).symm
    have hnorm := congrArg norm heq1
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hnorm
    have hre0 : ((α : ℂ) - s).re = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · linarith [Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hlt]
      · linarith [Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hgt]
    left
    simp at hre0
    linarith
  · have heq1 : (2 : ℂ) ^ (((1 - α : ℝ) : ℂ) - s) = 1 := (sub_eq_zero.mp h3).symm
    have hnorm := congrArg norm heq1
    rw [norm_one, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hnorm
    have hre0 : (((1 - α : ℝ) : ℂ) - s).re = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · linarith [Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) hlt]
      · linarith [Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hgt]
    right
    simp at hre0
    linarith

theorem primeTwoFactor_ne_zero_of_gt {α : ℝ} (h0 : 0 < α) {s : ℂ}
    (hs1 : α < s.re) (hs2 : 1 - α < s.re) : primeTwoFactor α s ≠ 0 := by
  intro hz
  rcases re_eq_of_primeTwoFactor_eq_zero hz with h | h <;> linarith

theorem primeTwoFactor_ne_zero_of_one_le_re {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {s : ℂ}
    (hs : 1 ≤ s.re) : primeTwoFactor α s ≠ 0 :=
  primeTwoFactor_ne_zero_of_gt h0 (by linarith) (by linarith)

theorem primeTwoFactor_eval_self (α : ℝ) : primeTwoFactor α (α : ℂ) = 0 := by
  unfold primeTwoFactor
  simp

/-- Deformed entire completed zeta `ξ_α(s) = primeTwoFactor α s * xi s`. -/
def xiDeformed (α : ℝ) (s : ℂ) : ℂ :=
  primeTwoFactor α s * xi s

theorem differentiable_xiDeformed (α : ℝ) : Differentiable ℂ (xiDeformed α) :=
  (differentiable_primeTwoFactor α).mul xi_differentiable

theorem xiDeformed_one_sub (α : ℝ) (s : ℂ) : xiDeformed α (1 - s) = xiDeformed α s := by
  rw [xiDeformed, xiDeformed, primeTwoFactor_one_sub, xi_one_sub]

theorem xiDeformed_conj (α : ℝ) (s : ℂ) :
    xiDeformed α (starRingEnd ℂ s) = starRingEnd ℂ (xiDeformed α s) := by
  rw [xiDeformed, xiDeformed, map_mul, primeTwoFactor_conj, xi_conj]

theorem xiDeformed_ne_zero_of_one_le_re {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {s : ℂ}
    (hs : 1 ≤ s.re) : xiDeformed α s ≠ 0 :=
  mul_ne_zero (primeTwoFactor_ne_zero_of_one_le_re h0 h1 hs) (xi_ne_zero_of_one_le_re hs)

/-- Prime-`2` Schur scattering gate
`B_{2,α}(w) = schurNum 2 t_α (2^{-2w}) / schurDen 2 t_α (2^{-2w})`. -/
def primeTwoScatteringGate (α : ℝ) (w : ℂ) : ℂ :=
  schurNum 2 (primeTwoTrace α) ((2 : ℂ) ^ (-2 * w)) /
    schurDen 2 (primeTwoTrace α) ((2 : ℂ) ^ (-2 * w))

/-- Exact polynomial factorization of `primeTwoFactor α (2w)` and `primeTwoFactor α (1 + 2w)`. -/
theorem primeTwoFactor_two_mul_eq_schurNum (α : ℝ) (w : ℂ) :
    primeTwoFactor α (2 * w) =
      (2 : ℂ) ^ (2 * w - 1 / 2) * schurNum 2 (primeTwoTrace α) ((2 : ℂ) ^ (-2 * w)) := by
  set L : ℂ := ((Real.log 2 : ℝ) : ℂ)
  have hrpow : ∀ r : ℝ, ((2 : ℝ) ^ r : ℂ) = Complex.exp ((r : ℂ) * L) := by
    intro r
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Complex.ofReal_exp]
    congr 1; push_cast; ring
  have hprod : Complex.exp ((α : ℂ) * L) * Complex.exp (((1 - α : ℝ) : ℂ) * L) = 2 := by
    rw [← hrpow α, ← hrpow (1 - α), ← Complex.ofReal_mul, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  unfold primeTwoFactor schurNum primeTwoTrace
  simp only [two_cpow_eq_exp, Complex.ofReal_add, hrpow]
  have e1 : Complex.exp (((α : ℂ) - 2 * w) * L) =
      Complex.exp ((α : ℂ) * L) * Complex.exp (-2 * w * L) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp ((((1 - α : ℝ) : ℂ) - 2 * w) * L) =
      Complex.exp (((1 - α : ℝ) : ℂ) * L) * Complex.exp (-2 * w * L) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2]
  linear_combination
    (Complex.exp ((2 * w - 1 / 2) * L) * Complex.exp (-2 * w * L) ^ 2) * hprod

theorem primeTwoFactor_one_add_two_mul_eq_schurDen (α : ℝ) (w : ℂ) :
    primeTwoFactor α (1 + 2 * w) =
      (2 : ℂ) ^ (2 * w - 1 / 2) * schurDen 2 (primeTwoTrace α) ((2 : ℂ) ^ (-2 * w)) := by
  set L : ℂ := ((Real.log 2 : ℝ) : ℂ)
  have hrpow : ∀ r : ℝ, ((2 : ℝ) ^ r : ℂ) = Complex.exp ((r : ℂ) * L) := by
    intro r
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Complex.ofReal_exp]
    congr 1; push_cast; ring
  have hexpL : Complex.exp L = 2 := by
    have := hrpow 1
    simpa using this.symm
  have hprod : Complex.exp ((α : ℂ) * L) * Complex.exp (((1 - α : ℝ) : ℂ) * L) = 2 := by
    rw [← hrpow α, ← hrpow (1 - α), ← Complex.ofReal_mul, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  unfold primeTwoFactor schurDen primeTwoTrace
  simp only [two_cpow_eq_exp, Complex.ofReal_add, hrpow]
  have e0 : Complex.exp ((1 + 2 * w - 1 / 2) * L) =
      2 * Complex.exp ((2 * w - 1 / 2) * L) := by
    have : (1 + 2 * w - 1 / 2) * L = L + (2 * w - 1 / 2) * L := by ring
    rw [this, Complex.exp_add, hexpL]
  have e1 : Complex.exp (((α : ℂ) - (1 + 2 * w)) * L) =
      (Complex.exp ((α : ℂ) * L) / 2) * Complex.exp (-2 * w * L) := by
    have h2 : Complex.exp ((α : ℂ) * L) = 2 * (Complex.exp ((α : ℂ) * L) / 2) := by ring
    have hsum : ((α : ℂ) - (1 + 2 * w)) * L + L = (α : ℂ) * L + (-2 * w * L) := by ring
    have hexp := congrArg Complex.exp hsum
    rw [Complex.exp_add, Complex.exp_add, hexpL] at hexp
    apply mul_right_cancel₀ (two_ne_zero' ℂ)
    linear_combination hexp
  have e2 : Complex.exp ((((1 - α : ℝ) : ℂ) - (1 + 2 * w)) * L) =
      (Complex.exp (((1 - α : ℝ) : ℂ) * L) / 2) * Complex.exp (-2 * w * L) := by
    have hsum : (((1 - α : ℝ) : ℂ) - (1 + 2 * w)) * L + L =
        ((1 - α : ℝ) : ℂ) * L + (-2 * w * L) := by ring
    have hexp := congrArg Complex.exp hsum
    rw [Complex.exp_add, Complex.exp_add, hexpL] at hexp
    apply mul_right_cancel₀ (two_ne_zero' ℂ)
    linear_combination hexp
  rw [e0, e1, e2]
  push_cast
  linear_combination
    ((1 / 2 : ℂ) * Complex.exp ((2 * w - 1 / 2) * L) * Complex.exp (-2 * w * L) ^ 2) * hprod

/-- Exact unconditional ratio identity `primeTwoFactor α (2w) / primeTwoFactor α (1 + 2w) =
primeTwoScatteringGate α w` for every `w ∈ ℂ`. -/
theorem primeTwoFactor_div_eq_primeTwoScatteringGate (α : ℝ) (w : ℂ) :
    primeTwoFactor α (2 * w) / primeTwoFactor α (1 + 2 * w) = primeTwoScatteringGate α w := by
  have hne : (2 : ℂ) ^ (2 * w - 1 / 2) ≠ 0 := by
    rw [two_cpow_eq_exp]; exact Complex.exp_ne_zero _
  rw [primeTwoFactor_two_mul_eq_schurNum, primeTwoFactor_one_add_two_mul_eq_schurDen,
    primeTwoScatteringGate, mul_div_mul_left _ _ hne]

/-! ## 2. Global Passivity, Unitarity, Prime Euler Product, and Retarded Echo Kernel -/

/-- Root Factorization of `schurDen 2 (primeTwoTrace α) v`. -/
theorem schurDen_primeTwo_eq_mul (α : ℝ) (v : ℂ) :
    schurDen 2 (primeTwoTrace α) v =
      2 * (1 - ((2 : ℝ) ^ (-α) : ℂ) * v) * (1 - ((2 : ℝ) ^ (α - 1) : ℂ) * v) := by
  have hprod : (2 : ℝ) ^ (-α) * (2 : ℝ) ^ (α - 1) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hsum : 2 * ((2 : ℝ) ^ (-α) + (2 : ℝ) ^ (α - 1)) = primeTwoTrace α := by
    have h1 : (2 : ℝ) * (2 : ℝ) ^ (-α) = (2 : ℝ) ^ (1 - α) := by
      conv_lhs => rw [← Real.rpow_one 2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    have h2 : (2 : ℝ) * (2 : ℝ) ^ (α - 1) = (2 : ℝ) ^ α := by
      conv_lhs => rw [← Real.rpow_one 2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    rw [primeTwoTrace, mul_add, h1, h2, add_comm]
  have hprodC : (((2 : ℝ) ^ (-α) : ℝ) : ℂ) * (((2 : ℝ) ^ (α - 1) : ℝ) : ℂ) = 1 / 2 := by
    exact_mod_cast hprod
  have hsumC : 2 * ((((2 : ℝ) ^ (-α) : ℝ) : ℂ) + (((2 : ℝ) ^ (α - 1) : ℝ) : ℂ)) =
      (primeTwoTrace α : ℂ) := by
    exact_mod_cast hsum
  unfold schurDen
  push_cast
  linear_combination (-(v : ℂ)) * hsumC + (-(2 * v ^ 2)) * hprodC

/-- Nonvanishing of `schurDen 2 (primeTwoTrace α) (2^{-2w})` on `-σ ≤ Re w` when `σ < (1 - α)/2`. -/
theorem schurDen_primeTwo_ne_zero_of_re_gt {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {w : ℂ} (hw1 : α - 1 < 2 * w.re) (hw2 : -α < 2 * w.re) :
    schurDen 2 (primeTwoTrace α) ((2 : ℂ) ^ (-2 * w)) ≠ 0 := by
  have hc0 : (2 : ℂ) ^ (2 * w - 1 / 2) ≠ 0 := by rw [two_cpow_eq_exp]; exact Complex.exp_ne_zero _
  have hfac := primeTwoFactor_one_add_two_mul_eq_schurDen α w
  intro hden
  rw [hden, mul_zero] at hfac
  exact primeTwoFactor_ne_zero_of_gt h0 (by simp; linarith) (by simp; linarith) hfac

/-- Schur contractivity `‖primeTwoScatteringGate α w‖ ≤ 1` across `Re w ≥ 0` (`0 < α < 1`). -/
theorem norm_primeTwoScatteringGate_le_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {w : ℂ} (hw : 0 ≤ w.re) :
    ‖primeTwoScatteringGate α w‖ ≤ 1 := by
  obtain ⟨_, htr⟩ := primeTwoTrace_pos_and_lt_three h0 h1
  set v : ℂ := (2 : ℂ) ^ (-2 * w)
  have hv : ‖v‖ ≤ 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have hre : (-2 * w).re = -2 * w.re := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hschur := (schur_bound_iff (q := 2) (t := primeTwoTrace α) (by norm_num)).mpr
    (by linarith) v hv
  have hden : schurDen 2 (primeTwoTrace α) v ≠ 0 :=
    schurDen_primeTwo_ne_zero_of_re_gt h0 h1 (by linarith) (by linarith)
  rw [primeTwoScatteringGate, norm_div, div_le_one (norm_pos_iff.mpr hden)]
  exact hschur

/-- Unitarity `‖primeTwoScatteringGate α (it)‖ = 1` on `ℝ` (`0 < α < 1`). -/
theorem norm_primeTwoScatteringGate_axis {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (t : ℝ) :
    ‖primeTwoScatteringGate α ((t : ℂ) * I)‖ = 1 := by
  set v : ℂ := (2 : ℂ) ^ (-2 * ((t : ℂ) * I))
  have hv1 : Complex.normSq v = 1 := by
    rw [Complex.normSq_eq_norm_sq, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have hre : (-2 * ((t : ℂ) * I)).re = 0 := by simp
    rw [hre, Real.rpow_zero, one_pow]
  have hdiff := GaloisForLFunctions.ArithmeticScatteringHolography.normSq_schurDen_sub_num
    2 (primeTwoTrace α) v
  rw [hv1, sub_self, mul_zero, zero_mul] at hdiff
  have hnorm_eq : ‖schurNum 2 (primeTwoTrace α) v‖ = ‖schurDen 2 (primeTwoTrace α) v‖ := by
    have hsq : ‖schurNum 2 (primeTwoTrace α) v‖ ^ 2 = ‖schurDen 2 (primeTwoTrace α) v‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      linarith
    nlinarith [norm_nonneg (schurNum 2 (primeTwoTrace α) v),
      norm_nonneg (schurDen 2 (primeTwoTrace α) v)]
  have hden : schurDen 2 (primeTwoTrace α) v ≠ 0 :=
    schurDen_primeTwo_ne_zero_of_re_gt h0 h1 (by simp; linarith) (by simp; linarith)
  rw [primeTwoScatteringGate, norm_div, hnorm_eq, div_self (norm_ne_zero_iff.mpr hden)]

/-- Pole-cleared deformed scattering symbol `S_{red,α}(w) = ξ_α(2w) / ξ_α(1 + 2w)`. -/
def deformedReducedScattering (α : ℝ) (w : ℂ) : ℂ :=
  xiDeformed α (2 * w) / xiDeformed α (1 + 2 * w)

theorem deformedReducedScattering_eq_mul (α : ℝ) (w : ℂ) :
    deformedReducedScattering α w =
      primeTwoScatteringGate α w * modularReducedScattering w := by
  rw [deformedReducedScattering, xiDeformed, xiDeformed, mul_div_mul_comm,
    primeTwoFactor_div_eq_primeTwoScatteringGate, modularReducedScattering]

/-- **Global Schur Passivity of the Deformed Horizon.** For `0 < α < 1` and `Re w ≥ 0`,
`‖ξ_α(2w) / ξ_α(1 + 2w)‖ ≤ 1` and its Herglotz boundary admittance has non-negative real part. -/
theorem norm_deformedReducedScattering_le_one {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {w : ℂ} (hw : 0 ≤ w.re) :
    ‖deformedReducedScattering α w‖ ≤ 1 ∧
      0 ≤ ((1 - deformedReducedScattering α w) / (1 + deformedReducedScattering α w)).re := by
  have hle : ‖deformedReducedScattering α w‖ ≤ 1 := by
    rw [deformedReducedScattering_eq_mul, norm_mul]
    calc ‖primeTwoScatteringGate α w‖ * ‖modularReducedScattering w‖
        ≤ 1 * 1 := mul_le_mul (norm_primeTwoScatteringGate_le_one h0 h1 hw)
            (norm_modularReducedScattering_le_one hw) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  refine ⟨hle, ?_⟩
  set S := deformedReducedScattering α w
  have hS : Complex.normSq S ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg S]
  by_cases hden : 1 + S = 0
  · rw [hden, div_zero, zero_re]
  · rw [Complex.div_re]
    have hnum : (1 - S).re * (1 + S).re + (1 - S).im * (1 + S).im = 1 - Complex.normSq S := by
      rw [Complex.normSq_apply]; simp; ring
    rw [← add_div, hnum]
    exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

/-- Full deformed modular scattering phase
`φ_α(w) = ((1 + 2w)/(2w - 1)) · (ξ_α(2w) / ξ_α(1 + 2w))`. -/
def deformedScatteringPhase (α : ℝ) (w : ℂ) : ℂ :=
  ((1 + 2 * w) / (2 * w - 1)) * (xiDeformed α (2 * w) / xiDeformed α (1 + 2 * w))

theorem deformedScatteringPhase_eq_mul (α : ℝ) (w : ℂ) :
    deformedScatteringPhase α w =
      primeTwoScatteringGate α w * modularScatteringPhase w := by
  rw [deformedScatteringPhase, xiDeformed, xiDeformed, mul_div_mul_comm,
    primeTwoFactor_div_eq_primeTwoScatteringGate, modularScatteringPhase]
  ring

/-- Continuous-spectrum unitarity `‖φ_α(it)‖ = 1` for all `t ∈ ℝ` (`0 < α < 1`). -/
theorem norm_deformedScatteringPhase_axis {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (t : ℝ) :
    ‖deformedScatteringPhase α ((t : ℂ) * I)‖ = 1 := by
  rw [deformedScatteringPhase_eq_mul, norm_mul, norm_primeTwoScatteringGate_axis h0 h1 t,
    norm_modularScatteringPhase_axis t, one_mul]

/-- Deformed prime-marked Euler gates over `Nat.Primes`: modifies only `p = 2` by multiplying by
`primeTwoScatteringGate α w`, leaving all odd primes `p ≠ 2` untouched. -/
def deformedPrimeGate (α : ℝ) (p : Nat.Primes) (w : ℂ) : ℂ :=
  if (p : ℕ) = 2 then primeTwoScatteringGate α w * primeEchoGate p w else primeEchoGate p w

/-- On `Re w > 1/2`, the infinite product of `deformedPrimeGate α p w` over `Nat.Primes` converges
and multiplying by `B(w, 1/2)` equals `deformedScatteringPhase α w`. -/
theorem hasProd_deformedPrimeGate {α : ℝ} {w : ℂ} (hw : 1 / 2 < w.re) :
    HasProd (fun p : Nat.Primes => deformedPrimeGate α p w)
      (primeTwoScatteringGate α w * (riemannZeta (2 * w) / riemannZeta (2 * w + 1))) := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let m : Nat.Primes → ℂ := fun p => if p = p2 then primeTwoScatteringGate α w else 1
  have hm : HasProd m (primeTwoScatteringGate α w) := by
    simpa [m] using hasProd_ite_eq p2 (primeTwoScatteringGate α w)
  have hgate : (fun p : Nat.Primes => deformedPrimeGate α p w) =
      fun p => m p * primeEchoGate p w := by
    funext p
    unfold deformedPrimeGate
    by_cases hp : p = p2
    · subst hp; simp [m, p2]
    · have hp2 : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
      simp [m, hp, hp2]
  rw [hgate]
  exact hm.mul (hasProd_primeEchoGate hw)

/-- Partial-fraction weights for the prime-`2` retarded echo expansion (`1/2 < α < 1`). -/
def echoWeightA1 (α : ℝ) : ℝ :=
  (2 * (2 : ℝ) ^ (2 * α - 1) - 1) / (2 * (1 - (2 : ℝ) ^ (2 * α - 1)))

def echoWeightA2 (α : ℝ) : ℝ :=
  ((2 : ℝ) ^ (2 * α - 1) - 2) / (2 * (1 - (2 : ℝ) ^ (2 * α - 1)))

/-- `k`-th retarded prime-`2` echo amplitude (`k ≥ 0` corresponds to delay `2(k + 1) log 2`). -/
def deformedEchoCoeff (α : ℝ) (k : ℕ) : ℝ :=
  echoWeightA1 α * ((2 : ℝ) ^ (-α)) ^ (k + 1) +
    echoWeightA2 α * ((2 : ℝ) ^ (α - 1)) ^ (k + 1)

/-- Explicit retarded time-domain echo kernel for the prime-`2` deformed horizon:
`K_α(τ) = (1/2) K(τ) + ∑_{k ≥ 0} c_{α,k} K(τ - 2(k + 1) log 2)`. -/
def deformedEchoKernel (α : ℝ) (τ : ℝ) : ℝ :=
  (1 / 2) * echoKernel τ +
    ∑' k : ℕ, deformedEchoCoeff α k * echoKernel (τ - 2 * ((k + 1 : ℕ) : ℝ) * Real.log 2)

/-- **Strict Retarded Causality.** `deformedEchoKernel α τ = 0` for all `τ ≤ 0`. -/
theorem deformedEchoKernel_eq_zero_of_nonpos (α : ℝ) {τ : ℝ} (hτ : τ ≤ 0) :
    deformedEchoKernel α τ = 0 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk : ∀ k : ℕ, echoKernel (τ - 2 * ((k + 1 : ℕ) : ℝ) * Real.log 2) = 0 := fun k =>
    echoKernel_eq_zero_of_nonpos (by
      have : 0 ≤ 2 * ((k + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
      linarith)
  simp [deformedEchoKernel, echoKernel_eq_zero_of_nonpos hτ, hk]

theorem summable_abs_deformedEchoCoeff {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1) :
    Summable fun k : ℕ => |deformedEchoCoeff α k| := by
  have hr1_0 : 0 ≤ (2 : ℝ) ^ (-α) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr1_1 : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr2_0 : 0 ≤ (2 : ℝ) ^ (α - 1) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr2_1 : (2 : ℝ) ^ (α - 1) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs1 : Summable fun k : ℕ => |echoWeightA1 α| * ((2 : ℝ) ^ (-α)) ^ (k + 1) := by
    simp_rw [pow_succ']
    exact ((summable_geometric_of_lt_one hr1_0 hr1_1).mul_left ((2 : ℝ) ^ (-α))).mul_left _
  have hs2 : Summable fun k : ℕ => |echoWeightA2 α| * ((2 : ℝ) ^ (α - 1)) ^ (k + 1) := by
    simp_rw [pow_succ']
    exact ((summable_geometric_of_lt_one hr2_0 hr2_1).mul_left ((2 : ℝ) ^ (α - 1))).mul_left _
  refine (hs1.add hs2).of_nonneg_of_le (fun _ => abs_nonneg _) fun k => ?_
  calc |deformedEchoCoeff α k|
      ≤ |echoWeightA1 α * ((2 : ℝ) ^ (-α)) ^ (k + 1)| +
          |echoWeightA2 α * ((2 : ℝ) ^ (α - 1)) ^ (k + 1)| := abs_add_le _ _
    _ = |echoWeightA1 α| * ((2 : ℝ) ^ (-α)) ^ (k + 1) +
          |echoWeightA2 α| * ((2 : ℝ) ^ (α - 1)) ^ (k + 1) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr1_0 _),
          abs_of_nonneg (pow_nonneg hr2_0 _)]

/-- Causal geometric expansion of `primeTwoScatteringGate α w` on `Re w ≥ 0` (`1/2 < α < 1`). -/
theorem primeTwoScatteringGate_eq_causal_series {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1)
    {w : ℂ} (hw : 0 ≤ w.re) :
    primeTwoScatteringGate α w =
      (1 / 2 : ℂ) + ∑' k : ℕ, ((deformedEchoCoeff α k : ℝ) : ℂ) *
        Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log 2 : ℝ) : ℂ)) := by
  set r₁ : ℝ := (2 : ℝ) ^ (-α)
  set r₂ : ℝ := (2 : ℝ) ^ (α - 1)
  set x : ℝ := (2 : ℝ) ^ (2 * α - 1)
  set v : ℂ := (2 : ℂ) ^ (-2 * w)
  have hx1 : 1 < x := Real.one_lt_rpow (by norm_num) (by linarith)
  have h1x_ne : 1 - x ≠ 0 := by linarith
  have h1xC : (1 - (x : ℂ)) ≠ 0 := by exact_mod_cast h1x_ne
  have hr1_lt : r₁ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr2_lt : r₂ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr1_pos : 0 < r₁ := Real.rpow_pos_of_pos (by norm_num) _
  have hr2_pos : 0 < r₂ := Real.rpow_pos_of_pos (by norm_num) _
  have hv_le : ‖v‖ ≤ 1 := by
    rw [show v = ((2 : ℝ) : ℂ) ^ (-2 * w) by simp [v],
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have hre : (-2 * w).re = -2 * w.re := by simp
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hnr1 : ‖(r₁ : ℂ) * v‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr1_pos.le]
    nlinarith [norm_nonneg v]
  have hnr2 : ‖(r₂ : ℂ) * v‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr2_pos.le]
    nlinarith [norm_nonneg v]
  have h1r1 : 1 - (r₁ : ℂ) * v ≠ 0 := sub_ne_zero.mpr fun h => by
    rw [← h, norm_one] at hnr1; exact lt_irrefl _ hnr1
  have h1r2 : 1 - (r₂ : ℂ) * v ≠ 0 := sub_ne_zero.mpr fun h => by
    rw [← h, norm_one] at hnr2; exact lt_irrefl _ hnr2
  have hexp_pow : ∀ k : ℕ,
      Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log 2 : ℝ) : ℂ)) = v ^ (k + 1) := by
    intro k
    have hv_exp : v = Complex.exp (-2 * w * ((Real.log 2 : ℝ) : ℂ)) := by
      simpa [v] using two_cpow_eq_exp (-2 * w)
    rw [hv_exp, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hexp_pow]
  have hs1 : HasSum (fun k : ℕ => ((echoWeightA1 α : ℂ) * ((r₁ : ℂ) * v)) * ((r₁ : ℂ) * v) ^ k)
      (((echoWeightA1 α : ℂ) * ((r₁ : ℂ) * v)) / (1 - (r₁ : ℂ) * v)) := by
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hnr1).mul_left
      ((echoWeightA1 α : ℂ) * ((r₁ : ℂ) * v))
  have hs2 : HasSum (fun k : ℕ => ((echoWeightA2 α : ℂ) * ((r₂ : ℂ) * v)) * ((r₂ : ℂ) * v) ^ k)
      (((echoWeightA2 α : ℂ) * ((r₂ : ℂ) * v)) / (1 - (r₂ : ℂ) * v)) := by
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hnr2).mul_left
      ((echoWeightA2 α : ℂ) * ((r₂ : ℂ) * v))
  have hterm : ∀ k : ℕ, ((deformedEchoCoeff α k : ℝ) : ℂ) * v ^ (k + 1) =
      ((echoWeightA1 α : ℂ) * ((r₁ : ℂ) * v)) * ((r₁ : ℂ) * v) ^ k +
        ((echoWeightA2 α : ℂ) * ((r₂ : ℂ) * v)) * ((r₂ : ℂ) * v) ^ k := by
    intro k
    unfold deformedEchoCoeff
    push_cast
    rw [mul_pow, mul_pow, pow_succ', pow_succ', pow_succ']
    ring
  simp_rw [hterm]
  rw [(hs1.add hs2).tsum_eq]
  -- Algebraic partial-fraction verification
  have hr12 : (r₁ : ℂ) * (r₂ : ℂ) = 1 / 2 := by
    have : r₁ * r₂ = 1 / 2 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num
    exact_mod_cast this
  have hsum_tr : 2 * ((r₁ : ℂ) + (r₂ : ℂ)) = (primeTwoTrace α : ℂ) := by
    have h1' : (2 : ℝ) * r₁ = (2 : ℝ) ^ (1 - α) := by
      conv_lhs => rw [← Real.rpow_one 2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    have h2' : (2 : ℝ) * r₂ = (2 : ℝ) ^ α := by
      conv_lhs => rw [← Real.rpow_one 2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    have : 2 * (r₁ + r₂) = primeTwoTrace α := by rw [primeTwoTrace, mul_add, h1', h2', add_comm]
    exact_mod_cast this
  have hxr1 : (r₂ : ℂ) = (x : ℂ) * (r₁ : ℂ) := by
    have : r₂ = x * r₁ := by
      dsimp only [r₁, r₂, x]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    exact_mod_cast this
  have hA1 : (echoWeightA1 α : ℂ) = (2 * (x : ℂ) - 1) / (2 * (1 - (x : ℂ))) := by
    unfold echoWeightA1; push_cast; rfl
  have hA2 : (echoWeightA2 α : ℂ) = ((x : ℂ) - 2) / (2 * (1 - (x : ℂ))) := by
    unfold echoWeightA2; push_cast; rfl
  rw [primeTwoScatteringGate, schurDen_primeTwo_eq_mul, schurNum, hA1, hA2]
  have hden_all : 2 * (1 - (r₁ : ℂ) * v) * (1 - (r₂ : ℂ) * v) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero h1r1) h1r2
  field_simp
  linear_combination
    (4 * (1 - (x : ℂ)) * v ^ 2) * hr12 +
    (-(1 - (x : ℂ)) * v) * hsum_tr +
    (-(2 * (2 * (x : ℂ) - 1) * v) + 4 * v ^ 2 * (1 - (x : ℂ)) * (r₁ : ℂ)) * hxr1

private theorem integrable_cexp_mul_echoKernel {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable fun τ : ℝ => Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ) := by
  have hw0 : 0 < w.re := by linarith
  let F : ℕ → ℝ → ℂ := fun c τ => echoCoefficient w c * bounceWave w (τ - echoDelay c)
  have hint : ∀ c, Integrable (F c) := fun c =>
    ((integrable_bounceWave hw0).comp_sub_right (echoDelay c)).const_mul _
  have hnorm : ∀ c, (∫ τ, ‖F c τ‖) = ‖echoCoefficient w c‖ * ∫ v, ‖bounceWave w v‖ := by
    intro c
    simp_rw [F, norm_mul]
    rw [integral_const_mul, integral_sub_right_eq_self (fun v => ‖bounceWave w v‖) (echoDelay c)]
  have hbase : Summable fun c : ℕ => 1 / (c : ℝ) ^ (2 * w.re) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hsum : Summable fun c => ∫ τ, ‖F c τ‖ := by
    simp_rw [hnorm]
    refine Summable.mul_right _ (Summable.of_norm_bounded hbase fun c => ?_)
    rw [norm_norm]
    exact norm_echoCoefficient_le c
  have htsum := HTGeometry.integrable_tsum_of_summable_integral_norm hint hsum
  refine htsum.congr (Eventually.of_forall fun τ => ?_)
  rw [echoKernel, Complex.ofReal_tsum, ← tsum_mul_left]
  exact tsum_congr fun c => (cexp_mul_echoTerm w c τ).symm

/-- **Laplace Transform of the Retarded Deformed Echo Kernel.** On `Re w > 1/2` (`1/2 < α < 1`),
`∫ e^{-wτ} K_α(τ) dτ = primeTwoScatteringGate α w * (Λ(2w) / Λ(2w + 1))`. -/
theorem integral_cexp_mul_deformedEchoKernel {α : ℝ} (h0 : 1 / 2 < α) (h1 : α < 1)
    {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((deformedEchoKernel α τ : ℝ) : ℂ)) =
      primeTwoScatteringGate α w *
        (completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1)) := by
  let Kw : ℝ → ℂ := fun τ => Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ)
  have hKw_int : Integrable Kw := integrable_cexp_mul_echoKernel hw
  have hKw_val : ∫ τ : ℝ, Kw τ =
      completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1) :=
    integral_cexp_mul_echoKernel_eq_completed hw
  let d : ℕ → ℝ := fun k => 2 * ((k + 1 : ℕ) : ℝ) * Real.log 2
  let G : ℕ → ℝ → ℂ := fun k τ =>
    ((deformedEchoCoeff α k : ℝ) : ℂ) * Complex.exp (-w * ((d k : ℝ) : ℂ)) * Kw (τ - d k)
  have hG_eq : ∀ (k : ℕ) (τ : ℝ), G k τ =
      Complex.exp (-w * (τ : ℂ)) *
        ((deformedEchoCoeff α k * echoKernel (τ - d k) : ℝ) : ℂ) := by
    intro k τ
    simp only [G, Kw]
    have hexp : Complex.exp (-w * ((d k : ℝ) : ℂ)) * Complex.exp (-w * ((τ - d k : ℝ) : ℂ)) =
        Complex.exp (-w * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    push_cast
    linear_combination
      (((deformedEchoCoeff α k : ℝ) : ℂ) * ((echoKernel (τ - d k) : ℝ) : ℂ)) * hexp
  have hG_int : ∀ k : ℕ, Integrable (G k) := fun k =>
    (hKw_int.comp_sub_right (d k)).const_mul _
  have hG_norm : Summable fun k : ℕ => ∫ τ : ℝ, ‖G k τ‖ := by
    have hbd : ∀ k : ℕ, ∫ τ : ℝ, ‖G k τ‖ ≤ |deformedEchoCoeff α k| * ∫ v : ℝ, ‖Kw v‖ := by
      intro k
      have hd_nonneg : 0 ≤ d k := by
        dsimp only [d]; exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
      have hexp_le : ‖Complex.exp (-w * ((d k : ℝ) : ℂ))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        have hre : (-w * ((d k : ℝ) : ℂ)).re = -w.re * d k := by simp
        rw [hre]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      have hpt : ∀ τ : ℝ, ‖G k τ‖ =
          ‖((deformedEchoCoeff α k : ℝ) : ℂ) * Complex.exp (-w * ((d k : ℝ) : ℂ))‖ *
            ‖Kw (τ - d k)‖ := fun τ => norm_mul _ _
      simp_rw [hpt]
      rw [integral_const_mul, integral_sub_right_eq_self (fun v => ‖Kw v‖) (d k), norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => norm_nonneg _)
      exact mul_le_of_le_one_right (abs_nonneg _) hexp_le
    exact ((summable_abs_deformedEchoCoeff h0 h1).mul_right _).of_nonneg_of_le
      (fun k => integral_nonneg fun _ => norm_nonneg _) hbd
  have hG_tsum_int : Integrable (fun τ : ℝ => ∑' k : ℕ, G k τ) :=
    HTGeometry.integrable_tsum_of_summable_integral_norm hG_int hG_norm
  have hHS := hasSum_integral_of_summable_integral_norm hG_int hG_norm
  -- Pointwise identity using local finiteness of the retarded echo sum at each `τ`
  have hpoint : ∀ τ : ℝ,
      Complex.exp (-w * (τ : ℂ)) * ((deformedEchoKernel α τ : ℝ) : ℂ) =
        (1 / 2 : ℂ) * Kw τ + ∑' k : ℕ, G k τ := by
    intro τ
    have hfin : {k : ℕ | deformedEchoCoeff α k * echoKernel (τ - d k) ≠ 0}.Finite := by
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      refine (Set.finite_lt_nat (⌈τ / (2 * Real.log 2)⌉₊ + 1)).subset fun k hk => ?_
      simp only [mem_setOf_eq] at hk ⊢
      by_contra hge
      push Not at hge
      have hdk : τ ≤ d k := by
        have h1 : τ / (2 * Real.log 2) ≤ (⌈τ / (2 * Real.log 2)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈τ / (2 * Real.log 2)⌉₊ : ℝ) < (k + 1 : ℕ) := by exact_mod_cast hge
        have h3 : τ / (2 * Real.log 2) < (k + 1 : ℕ) := h1.trans_lt h2
        rw [div_lt_iff₀ (by positivity)] at h3
        dsimp only [d]
        linarith
      exact hk (by rw [echoKernel_eq_zero_of_nonpos (by linarith), mul_zero])
    have hsum_pt : Summable fun k : ℕ => deformedEchoCoeff α k * echoKernel (τ - d k) :=
      summable_of_ne_finset_zero (s := hfin.toFinset) fun k hk => by
        simpa [hfin.mem_toFinset] using hk
    unfold deformedEchoKernel
    push_cast
    rw [mul_add, show Complex.exp (-w * (τ : ℂ)) * ((1 / 2 : ℂ) * ((echoKernel τ : ℝ) : ℂ)) =
      (1 / 2 : ℂ) * Kw τ by simp [Kw]; ring]
    congr 1
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr fun k => (hG_eq k τ).symm
  simp_rw [hpoint]
  rw [integral_add (hKw_int.const_mul _) hG_tsum_int, integral_const_mul, ← hHS.tsum_eq]
  have hG_val : ∀ k : ℕ, ∫ τ : ℝ, G k τ =
      (((deformedEchoCoeff α k : ℝ) : ℂ) * Complex.exp (-w * ((d k : ℝ) : ℂ))) * ∫ v : ℝ, Kw v := by
    intro k
    dsimp only [G]
    rw [integral_const_mul, integral_sub_right_eq_self Kw (d k)]
  simp_rw [hG_val]
  rw [tsum_mul_right, ← add_mul, hKw_val,
    primeTwoScatteringGate_eq_causal_series h0 h1 (by linarith)]

/-! ## 3. Complete Eternal-AdS Boundary Dictionary for the Deformed System -/

/-- Retarded, advanced, and two-boundary Wightman correlators of the deformed horizon. -/
def deformedRetardedCorrelator (α : ℝ) (ω : ℂ) : ℂ :=
  deformedScatteringPhase α (-I * ω)

def deformedAdvancedCorrelator (α : ℝ) (ω : ℂ) : ℂ :=
  deformedScatteringPhase α (I * ω)

def deformedWightmanRL (α : ℝ) (ω : ℂ) : ℂ :=
  (deformedRetardedCorrelator α ω - deformedAdvancedCorrelator α ω) /
    (2 * I * Complex.sinh (Real.pi * ω))

/-- Every zero `ρ` of `xiDeformed α` (including every nontrivial zero of `ζ` and `ρ = α`) produces
an isolated pole of `deformedRetardedCorrelator α` at `ω_ρ = i(ρ - 1)/2` of exact multiplicity
`-ord_ρ (xiDeformed α) < 0`. -/
theorem deformedRetardedCorrelator_order_at_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {ρ : ℂ} (hρ : xiDeformed α ρ = 0) :
    meromorphicOrderAt (deformedRetardedCorrelator α) (I * (ρ - 1) / 2) =
      -meromorphicOrderAt (xiDeformed α) ρ := by
  have hcoord : -I * (I * (ρ - 1) / 2) = (ρ - 1) / 2 := by
    linear_combination (-(ρ - 1) / 2) * I_sq
  have hd : HasDerivAt (fun ω : ℂ => -I * ω) (-I) (I * (ρ - 1) / 2) := hasDerivAt_const_mul (-I)
  have hcomp : meromorphicOrderAt (deformedRetardedCorrelator α) (I * (ρ - 1) / 2) =
      meromorphicOrderAt (deformedScatteringPhase α) ((ρ - 1) / 2) := by
    rw [← hcoord]
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := deformedScatteringPhase α) (g := fun ω : ℂ => -I * ω) (by fun_prop)
      (by rw [hd.deriv]; exact neg_ne_zero.mpr I_ne_zero)
  rw [hcomp]
  exact scatteringPhase_meromorphicOrderAt_at_zero (differentiable_xiDeformed α)
    (fun _ => xiDeformed_ne_zero_of_one_le_re h0 h1) (xiDeformed_one_sub α) hρ

/-- Two-boundary eternal-AdS pole order for `deformedWightmanRL α` in `-1/2 < Im ω < 0`. -/
theorem deformedWightmanRL_order_lower {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {ω : ℂ}
    (hlo : -(1 / 2 : ℝ) < ω.im) (hhi : ω.im < 0) (hz : xiDeformed α (1 - 2 * I * ω) = 0) :
    meromorphicOrderAt (deformedWightmanRL α) ω =
      -meromorphicOrderAt (xiDeformed α) (1 - 2 * I * ω) := by
  have habs0 : 0 < |ω.im| := abs_pos.mpr hhi.ne
  have habs1 : |ω.im| < 1 := by rw [abs_of_neg hhi]; linarith
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ω) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one habs0 habs1)
  have hadv_open : IsOpen {z : ℂ | z ≠ -(I / 2) ∧ xiDeformed α (1 + 2 * I * z) ≠ 0} :=
    isOpen_ne.inter (isOpen_ne.preimage ((differentiable_xiDeformed α).continuous.comp (by fun_prop)))
  have hadv_mem : ω ∈ {z : ℂ | z ≠ -(I / 2) ∧ xiDeformed α (1 + 2 * I * z) ≠ 0} := by
    refine ⟨fun h => by have := congrArg Complex.im h; simp at this; linarith, ?_⟩
    exact xiDeformed_ne_zero_of_one_le_re h0 h1 (by simp; linarith)
  have hadv_an : AnalyticAt ℂ (fun z => -deformedAdvancedCorrelator α z) ω := by
    refine (AnalyticAt.neg ?_)
    refine (DifferentiableOn.analyticOnNhd (fun z hz => ?_) hadv_open) ω hadv_mem
    have h2z : 2 * (I * z) - 1 ≠ 0 := fun he => hz.1 (by linear_combination (-I / 2) * he + z * I_sq)
    exact ((((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) (I * z)).div
      (by fun_prop) h2z).mul
        ((((differentiable_xiDeformed α) _).comp (I * z) (by fun_prop)).div
          (((differentiable_xiDeformed α) _).comp (I * z) (by fun_prop))
          (by simpa [mul_assoc] using hz.2))).comp z (by fun_prop)).differentiableWithinAt
  have hω_eq : ω = I * ((1 - 2 * I * ω) - 1) / 2 := by linear_combination ω * I_sq
  have hret_ord : meromorphicOrderAt (deformedRetardedCorrelator α) ω =
      -meromorphicOrderAt (xiDeformed α) (1 - 2 * I * ω) := by
    nth_rw 1 [hω_eq]
    exact deformedRetardedCorrelator_order_at_zero h0 h1 hz
  obtain ⟨_, hneg, _⟩ := meromorphicOrderAt_pos_of_entire_zero (differentiable_xiDeformed α)
    (fun _ => xiDeformed_ne_zero_of_one_le_re h0 h1) hz
  have hlt : meromorphicOrderAt (deformedRetardedCorrelator α) ω <
      meromorphicOrderAt (fun z => -deformedAdvancedCorrelator α z) ω :=
    lt_of_lt_of_le (by rw [hret_ord]; exact hneg) hadv_an.meromorphicOrderAt_nonneg
  have hden_an : AnalyticAt ℂ (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) ω :=
    AnalyticAt.inv (by fun_prop) hsinh_ne
  have hW : deformedWightmanRL α =
      (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) *
        (deformedRetardedCorrelator α + (fun z => -deformedAdvancedCorrelator α z)) := by
    funext z; simp only [deformedWightmanRL, Pi.mul_apply, Pi.add_apply]; ring
  rw [hW, meromorphicOrderAt_mul_of_ne_zero hden_an (inv_ne_zero hsinh_ne),
    meromorphicOrderAt_add_eq_left_of_lt hadv_an.meromorphicAt hlt, hret_ord]

/-! ## 4. Reflected Wavepacket Ringdown and Exact Decay Collapse to `(1 - α) / 2` -/

/-- Reflected horizon wavepacket for the deformed prime-`2` scattering system. -/
def deformedReflectedField (α : ℝ) (h : CompactPulse) (τ : ℝ) : ℂ :=
  ∫ t : ℝ, pulseAmplitude h (t : ℂ) * deformedScatteringPhase α ((t : ℂ) * I) *
    Complex.exp (I * (t : ℂ) * (τ : ℂ))

/-- Shifted vertical-line integral at `Re u = c`. -/
def deformedLineField (α : ℝ) (h : CompactPulse) (c τ : ℝ) : ℂ :=
  ∫ t : ℝ, pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    deformedScatteringPhase α ((c : ℂ) + (t : ℂ) * I) *
    Complex.exp (((c : ℂ) + (t : ℂ) * I) * (τ : ℂ))

theorem deformedLineField_zero (α : ℝ) (h : CompactPulse) (τ : ℝ) :
    deformedLineField α h 0 τ = deformedReflectedField α h τ := by
  unfold deformedLineField deformedReflectedField
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
  rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
  congr 2; ring

theorem differentiableAt_deformedScatteringPhase {α : ℝ}
    {w : ℂ} (hne : w ≠ 1 / 2) (hxi : xiDeformed α (1 + 2 * w) ≠ 0) :
    DifferentiableAt ℂ (deformedScatteringPhase α) w := by
  have hd : 2 * w - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) w).div (by fun_prop) hd).mul
    ((((differentiable_xiDeformed α) _).comp w (by fun_prop)).div
      (((differentiable_xiDeformed α) _).comp w (by fun_prop)) hxi)

theorem continuous_deformedReflectedField_and_bounded {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) :
    Continuous (deformedReflectedField α h) ∧
      ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ τ : ℝ, ‖deformedReflectedField α h τ‖ ≤ M₀ := by
  have hint_a : Integrable fun t : ℝ => ‖pulseAmplitude h (t : ℂ)‖ := by
    have h_line := (h.integrable_amplitude_line 0).norm
    exact h_line.congr (Eventually.of_forall fun t => by simp)
  have hpt : ∀ τ t : ℝ,
      ‖pulseAmplitude h (t : ℂ) * deformedScatteringPhase α ((t : ℂ) * I) *
        Complex.exp (I * (t : ℂ) * (τ : ℂ))‖ = ‖pulseAmplitude h (t : ℂ)‖ := by
    intro τ t
    rw [norm_mul, norm_mul, norm_deformedScatteringPhase_axis h0 h1 t, mul_one, Complex.norm_exp]
    have hre : (I * (t : ℂ) * (τ : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
  have hcont : Continuous (deformedReflectedField α h) := by
    unfold deformedReflectedField
    refine continuous_of_dominated (bound := fun t : ℝ => ‖pulseAmplitude h (t : ℂ)‖) ?_ ?_ hint_a ?_
    · intro τ
      refine (((h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).mul ?_).mul
        (by fun_prop)).aestronglyMeasurable
      refine continuous_iff_continuousAt.mpr fun t => ?_
      have hne : ((t : ℂ) * I) ≠ 1 / 2 := fun he => by
        have := congrArg Complex.re he; simp at this
      have hxi : xiDeformed α (1 + 2 * ((t : ℂ) * I)) ≠ 0 :=
        xiDeformed_ne_zero_of_one_le_re h0 h1 (by simp)
      exact ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) * I)
        (differentiableAt_deformedScatteringPhase hne hxi).continuousAt (by fun_prop)
    · exact fun τ => ae_of_all _ fun t => (hpt τ t).le
    · exact ae_of_all _ fun t => by fun_prop
  refine ⟨hcont, ∫ t : ℝ, ‖pulseAmplitude h (t : ℂ)‖,
    integral_nonneg fun _ => norm_nonneg _, fun τ => ?_⟩
  exact norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun t => (hpt τ t).le)

private theorem modularScatteringPhase_eq_scatterQ (u : ℂ) :
    modularScatteringPhase u = ((2 : ℂ) / (2 * u - 1)) * scatterQ (u + 1 / 2) := by
  unfold modularScatteringPhase scatterQ
  rw [show 2 * (u + 1 / 2) - 1 = 2 * u by ring, show 2 * (u + 1 / 2) = 1 + 2 * u by ring]
  ring

private theorem exists_norm_modularScatteringPhase_strip_le {a b K₁ : ℝ} {N₁ : ℕ}
    (hK₁ : 0 ≤ K₁)
    (hζ : ∀ u : ℂ, a ≤ u.re → u.re ≤ b → 1 ≤ |u.im| →
      ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ K₁ * |u.im| ^ N₁) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ u : ℂ, a ≤ u.re → u.re ≤ b → 1 ≤ |u.im| →
      ‖modularScatteringPhase u‖ ≤ C * |u.im| ^ M := by
  have hζ_shift : ∀ s : ℂ, a + 1 / 2 ≤ s.re → s.re ≤ b + 1 / 2 → 1 ≤ |s.im| →
      ‖(riemannZeta (2 * s))⁻¹‖ ≤ K₁ * |s.im| ^ N₁ := by
    intro s hs1 hs2 hsim
    have hs_eq : (2 : ℂ) * s = 1 + 2 * (s - 1 / 2) := by ring
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    have him : (s - 1 / 2).im = s.im := by simp
    rw [hs_eq, ← him]
    exact hζ (s - 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hsim)
  obtain ⟨CQ, NQ, hCQ, hQ⟩ := exists_norm_scatterQ_le hK₁ hζ_shift
  refine ⟨CQ, NQ, hCQ, fun u hu1 hu2 hut => ?_⟩
  rw [modularScatteringPhase_eq_scatterQ, norm_mul]
  have h2le : ‖(2 : ℂ) / (2 * u - 1)‖ ≤ 1 := by
    have him2 : (2 : ℝ) ≤ |(2 * u - 1).im| := by simp; linarith
    have hn2 : (2 : ℝ) ≤ ‖2 * u - 1‖ := him2.trans (Complex.abs_im_le_norm _)
    rw [norm_div, Complex.norm_ofNat, div_le_one (by linarith)]
    exact hn2
  have hQb : ‖scatterQ (u + 1 / 2)‖ ≤ CQ * |u.im| ^ NQ := by
    have hre : (u + 1 / 2).re = u.re + 1 / 2 := by simp
    have him : (u + 1 / 2).im = u.im := by simp
    have hb := hQ (u + 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
      (by rw [him]; exact hut)
    rwa [him] at hb
  calc ‖(2 : ℂ) / (2 * u - 1)‖ * ‖scatterQ (u + 1 / 2)‖
      ≤ 1 * (CQ * |u.im| ^ NQ) := mul_le_mul h2le hQb (norm_nonneg _) (by positivity)
    _ = CQ * |u.im| ^ NQ := one_mul _

private theorem exists_amplitude_deformed_right_le {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 8 →
      ‖pulseAmplitude h (-I * u) * deformedScatteringPhase α u‖ ≤ B / (1 + u.im ^ 2) := by
  obtain ⟨C₁, hC₁, hζ_log⟩ := exists_norm_inv_LFunction_le_log_pow (1 : DirichletCharacter ℂ 1)
  set boxR : Set ℂ := {z : ℂ | (1 ≤ z.re ∧ z.re ≤ 2) ∧ 2 ≤ |z.im| ∧ |z.im| ≤ 10}
  have hboxR_c : IsCompact boxR := by
    have heq : boxR = ((Icc (1 : ℝ) 2) ×ℂ (Icc (-10 : ℝ) 10)) ∩ {z : ℂ | 2 ≤ |z.im|} := by
      ext z
      simp only [boxR, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζ : ContinuousOn (fun z : ℂ => (riemannZeta z)⁻¹) boxR := by
    intro z hz
    have hne1 : z ≠ 1 := fun he => by have := hz.2.1; rw [he] at this; simp at this; linarith
    exact ((differentiableAt_riemannZeta hne1).continuousAt.inv₀
      (riemannZeta_ne_zero_of_one_le_re hz.1.1)).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := hboxR_c.exists_bound_of_continuousOn hcont_ζ
  have hζ_strip : ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 8 → 1 ≤ |u.im| →
      ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ (max (max M₁ 0) (C₁ * 2 ^ 7)) * |u.im| ^ 7 := by
    intro u hu1 hu2 hut
    set z : ℂ := 1 + 2 * u with hzdef
    have hzre1 : 1 ≤ z.re := by rw [hzdef]; simp; linarith
    have hzre2 : z.re ≤ 2 := by rw [hzdef]; simp; linarith
    have hzim : |z.im| = 2 * |u.im| := by
      have : z.im = 2 * u.im := by rw [hzdef]; simp
      rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hpow1 : (1 : ℝ) ≤ |u.im| ^ 7 := one_le_pow₀ hut
    rcases le_or_gt |z.im| 10 with hsmall | hbig
    · have hmem : z ∈ boxR := ⟨⟨hzre1, hzre2⟩, by linarith, hsmall⟩
      calc ‖(riemannZeta z)⁻¹‖ ≤ M₁ := hM₁ z hmem
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * 1 := by
            rw [mul_one]; exact (le_max_left M₁ 0).trans (le_max_left _ _)
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |u.im| ^ 7 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have hz_eq : z = (z.re : ℂ) + (z.im : ℂ) * I := by apply Complex.ext <;> simp
      have hb := hζ_log z.re z.im hzre1 hzre2 (by linarith)
      rw [DirichletCharacter.LFunction_modOne_eq, ← hz_eq] at hb
      have hlog_id : Real.log |z.im| ≤ 2 * |u.im| := by
        rw [← hzim]
        exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have hlog : Real.log |z.im| ^ 7 ≤ (2 * |u.im|) ^ 7 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog_id 7
      calc ‖(riemannZeta z)⁻¹‖ ≤ C₁ * Real.log |z.im| ^ 7 := hb
        _ ≤ C₁ * (2 * |u.im|) ^ 7 := mul_le_mul_of_nonneg_left hlog hC₁.le
        _ = (C₁ * 2 ^ 7) * |u.im| ^ 7 := by ring
        _ ≤ max (max M₁ 0) (C₁ * 2 ^ 7) * |u.im| ^ 7 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  obtain ⟨Cφ, Mφ, hCφ, hφ⟩ := exists_norm_modularScatteringPhase_strip_le (by positivity) hζ_strip
  obtain ⟨Ca, hCa, hrap⟩ := h.rapidAmplitude.decay (3 / 8) (Mφ + 2)
  set Kbox : Set ℂ := Icc (0 : ℝ) (3 / 8) ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun u => pulseAmplitude h (-I * u) * deformedScatteringPhase α u)
      Kbox := by
    intro u hu
    have hu' := Complex.mem_reProdIm.1 hu
    have hne : u ≠ 1 / 2 := fun he => by have := hu'.1.2; rw [he] at this; norm_num at this
    have hxi : xiDeformed α (1 + 2 * u) ≠ 0 :=
      xiDeformed_ne_zero_of_one_le_re h0 h1 (by simp; linarith [hu'.1.1])
    exact (((h.differentiable_amplitude _).comp u (by fun_prop)).mul
      (differentiableAt_deformedScatteringPhase hne hxi)).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  refine ⟨max (2 * max B₀ 0) (Cφ * Ca), by positivity, fun u hu1 hu2 => ?_⟩
  by_cases hut : 1 ≤ |u.im|
  · have hφu : ‖deformedScatteringPhase α u‖ ≤ Cφ * |u.im| ^ Mφ := by
      rw [deformedScatteringPhase_eq_mul, norm_mul]
      calc ‖primeTwoScatteringGate α u‖ * ‖modularScatteringPhase u‖
          ≤ 1 * (Cφ * |u.im| ^ Mφ) := mul_le_mul (norm_primeTwoScatteringGate_le_one h0 h1 hu1)
              (hφ u hu1 hu2 hut) (norm_nonneg _) (by positivity)
        _ = Cφ * |u.im| ^ Mφ := one_mul _
    have hw1 : (-I * u).re = u.im := by simp
    have hw2 : (-I * u).im = -u.re := by simp
    have ha := hrap (-I * u) (by rw [hw2, abs_neg, abs_le]; exact ⟨by linarith, hu2⟩)
    rw [hw1] at ha
    have ht1 : |u.im| ^ Mφ ≤ (1 + |u.im|) ^ Mφ :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith) Mφ
    have ht2 : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by nlinarith [abs_nonneg u.im, sq_abs u.im]
    rw [le_div_iff₀ (by positivity), norm_mul]
    calc ‖pulseAmplitude h (-I * u)‖ * ‖deformedScatteringPhase α u‖ * (1 + u.im ^ 2)
        ≤ ‖pulseAmplitude h (-I * u)‖ * (Cφ * (1 + |u.im|) ^ Mφ) * (1 + |u.im|) ^ 2 := by
          gcongr
          exact hφu.trans (mul_le_mul_of_nonneg_left ht1 hCφ)
      _ = Cφ * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ (Mφ + 2)) := by ring
      _ ≤ Cφ * Ca := mul_le_mul_of_nonneg_left ha hCφ
      _ ≤ max (2 * max B₀ 0) (Cφ * Ca) := le_max_right _ _
  · have hut' := abs_le.1 (not_le.1 hut).le
    have hb := hB₀ u (Complex.mem_reProdIm.2 ⟨⟨hu1, hu2⟩, hut'⟩)
    have hsq : u.im ^ 2 ≤ 1 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc ‖pulseAmplitude h (-I * u) * deformedScatteringPhase α u‖ * (1 + u.im ^ 2)
        ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
          (le_max_right _ _)
      _ ≤ max (2 * max B₀ 0) (Cφ * Ca) := by
          linarith [le_max_left (2 * max B₀ 0) (Cφ * Ca)]

private theorem deformedReflectedField_eq_lineField {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 3 / 8) (τ : ℝ) :
    deformedReflectedField α h τ = deformedLineField α h c τ := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_deformed_right_le h0 h1 h
  set Φ : ℂ → ℂ := fun u => pulseAmplitude h (-I * u) * deformedScatteringPhase α u *
    Complex.exp (u * (τ : ℂ)) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c → 0 ≤ s.re ∧ s.re ≤ 3 / 8 := by
    intro s hs; rw [uIcc_of_le hc0] at hs; exact ⟨hs.1, hs.2.trans hc1⟩
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
    have hxi : xiDeformed α (1 + 2 * s) ≠ 0 :=
      xiDeformed_ne_zero_of_one_le_re h0 h1 (by simp; linarith)
    exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
      (differentiableAt_deformedScatteringPhase hne hxi)).mul (by fun_prop))
  have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c →
      ‖Φ s‖ ≤ (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have hexp : ‖Complex.exp (s * (τ : ℂ))‖ ≤ Real.exp ((3 / 8) * |τ|) := by
      rw [Complex.norm_exp]
      have hre : (s * (τ : ℂ)).re = s.re * τ := by simp
      have habs_re : |s.re| ≤ 3 / 8 := by rw [abs_of_nonneg hs1]; exact hs2
      rw [hre]
      refine Real.exp_le_exp.mpr ?_
      calc s.re * τ ≤ |s.re * τ| := le_abs_self _
        _ = |s.re| * |τ| := abs_mul _ _
        _ ≤ (3 / 8) * |τ| := mul_le_mul_of_nonneg_right habs_re (abs_nonneg _)
    simp only [hΦ, norm_mul]
    calc ‖pulseAmplitude h (-I * s) * deformedScatteringPhase α s‖ * ‖Complex.exp (s * (τ : ℂ))‖
        ≤ (B / (1 + s.im ^ 2)) * Real.exp ((3 / 8) * |τ|) :=
          mul_le_mul (hB s hs1 hs2) hexp (norm_nonneg _) (by positivity)
      _ = (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by ring
  rw [← deformedLineField_zero]
  exact integral_vertical_line_shift_of_decay hd hbΦ

private theorem exists_deformedReflectedField_early_decay {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, τ ≤ 0 →
      ‖deformedReflectedField α h τ‖ ≤ C * Real.exp ((3 / 8) * τ) := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_deformed_right_le h0 h1 h
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  rw [deformedReflectedField_eq_lineField h0 h1 h (c := 3 / 8) (by norm_num) le_rfl τ]
  unfold deformedLineField
  have hpt : ∀ t : ℝ,
      ‖pulseAmplitude h (-I * (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)) *
        deformedScatteringPhase α (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
        Complex.exp ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ))‖ ≤
      B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) := by
    intro t
    set u : ℂ := ((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I
    have hre : u.re = 3 / 8 := by simp [u]
    have him : u.im = t := by simp [u]
    rw [norm_mul, Complex.norm_exp]
    have hre_exp : (u * (τ : ℂ)).re = (3 / 8) * τ := by simp [u]
    rw [hre_exp]
    have hb := hB u (by rw [hre]; norm_num) (by rw [hre])
    rw [him, div_eq_mul_inv] at hb
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hint : Integrable fun t : ℝ => B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
    (integrable_inv_one_add_sq.const_mul B).mul_const _
  calc ‖∫ t : ℝ, pulseAmplitude h (-I * (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)) *
          deformedScatteringPhase α (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ))‖
      ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = B * Real.pi * Real.exp ((3 / 8) * τ) := by
        rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

/-- Bilateral Laplace identity on `1/8 < Re w < 5/16` for `deformedReflectedField α h`. -/
theorem deformed_bilateral_laplace_eq {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) {w : ℂ} (hw1 : 1 / 8 < w.re) (hw2 : w.re < 5 / 16) :
    (∫ τ in Ioi (0 : ℝ), Complex.exp (-w * (τ : ℂ)) * deformedReflectedField α h τ) +
      (∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * deformedReflectedField α h (-σ)) =
      2 * Real.pi * pulseAmplitude h (-I * w) * deformedScatteringPhase α w := by
  set c : ℝ := w.re
  set η : ℝ := w.im
  have hc0 : 0 ≤ c := by linarith
  have hc1 : c ≤ 3 / 8 := by linarith
  have hw_eq : w = (c : ℂ) + (η : ℂ) * I := by apply Complex.ext <;> simp [c, η]
  obtain ⟨hGc, M₀, hM₀, hGb⟩ := continuous_deformedReflectedField_and_bounded h0 h1 h
  obtain ⟨Ce, hCe, hGe⟩ := exists_deformedReflectedField_early_decay h0 h1 h
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_deformed_right_le h0 h1 h
  set f : ℝ → ℂ := fun t => pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    deformedScatteringPhase α ((c : ℂ) + (t : ℂ) * I) with hf_def
  have hf_cont : Continuous f := by
    refine (h.differentiable_amplitude.continuous.comp (by fun_prop)).mul ?_
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : ((c : ℂ) + (t : ℂ) * I) ≠ 1 / 2 := fun he => by
      have := congrArg Complex.re he; simp at this; linarith
    have hxi : xiDeformed α (1 + 2 * ((c : ℂ) + (t : ℂ) * I)) ≠ 0 :=
      xiDeformed_ne_zero_of_one_le_re h0 h1 (by simp; linarith)
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
      (differentiableAt_deformedScatteringPhase hne hxi).continuousAt (by fun_prop)
  have hf_int : Integrable f := by
    refine (integrable_inv_one_add_sq.const_mul B).mono' hf_cont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hb := hB ((c : ℂ) + (t : ℂ) * I) (by simp; exact hc0) (by simp; exact hc1)
    simpa [hf_def, div_eq_mul_inv] using hb
  set g : ℝ → ℂ := fun τ => Complex.exp (-(c : ℂ) * (τ : ℂ)) * deformedReflectedField α h τ with hg_def
  have hg_cont : Continuous g := (by fun_prop : Continuous fun τ : ℝ =>
    Complex.exp (-(c : ℂ) * (τ : ℂ))).mul hGc
  have hg_pos : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hdom : IntegrableOn (fun τ : ℝ => M₀ * Real.exp (-c * τ)) (Ioi (0 : ℝ)) :=
      (RingdownRate.integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M₀
    refine hdom.mono' hg_cont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ _ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(c : ℂ) * (τ : ℂ)).re = -c * τ := by simp
    rw [hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hGb τ) (Real.exp_pos _).le
  have hg_neg : IntegrableOn g (Iic (0 : ℝ)) := by
    have hdom_i : IntegrableOn (fun σ : ℝ => Ce * Real.exp (-(3 / 8 - c) * σ)) (Ioi (0 : ℝ)) :=
      (RingdownRate.integrableOn_exp_mul_Ioi (by linarith) 0).const_mul Ce
    have hdom : IntegrableOn (fun τ : ℝ => Ce * Real.exp ((3 / 8 - c) * τ)) (Iic (0 : ℝ)) := by
      rw [← integrable_indicator_iff measurableSet_Iic]
      have h1' := (integrable_indicator_iff measurableSet_Ioi).mpr hdom_i
      refine (h1'.comp_neg).congr ?_
      have hae : ∀ᵐ τ : ℝ, τ ≠ 0 := by
        rw [ae_iff]
        have hset : {τ : ℝ | ¬τ ≠ 0} = ({0} : Set ℝ) := by ext τ; simp
        rw [hset]; exact measure_singleton 0
      refine hae.mono fun τ hτ => ?_
      dsimp only
      rcases lt_or_gt_of_ne hτ with hlt | hgt
      · rw [indicator_of_mem (show -τ ∈ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_mem (show τ ∈ Iic (0 : ℝ) from hlt.le)]
        ring_nf
      · rw [indicator_of_notMem (show -τ ∉ Ioi (0 : ℝ) by simp; linarith),
          indicator_of_notMem (show τ ∉ Iic (0 : ℝ) by simp; linarith)]
    refine hdom.mono' hg_cont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun τ hτ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(c : ℂ) * (τ : ℂ)).re = -c * τ := by simp
    rw [hre]
    calc Real.exp (-c * τ) * ‖deformedReflectedField α h τ‖
        ≤ Real.exp (-c * τ) * (Ce * Real.exp ((3 / 8) * τ)) :=
          mul_le_mul_of_nonneg_left (hGe τ hτ) (Real.exp_pos _).le
      _ = Ce * Real.exp ((3 / 8 - c) * τ) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hg_int : Integrable g := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hg_neg.union hg_pos
  have hpi0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi0
  set F : ℝ → ℂ := fun v => (2 * Real.pi : ℂ) * f (2 * Real.pi * v) with hF_def
  have hF_cont : Continuous F := continuous_const.mul (hf_cont.comp (by fun_prop))
  have hF_int : Integrable F := (hf_int.comp_mul_left' hpi0).const_mul (2 * Real.pi : ℂ)
  have hFinv_eq : 𝓕⁻ F = g := by
    funext τ
    rw [fourierInv_eq_integral_exp]
    have hg_sub := Measure.integral_comp_mul_left
      (fun y : ℝ => f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) (2 * Real.pi)
    have habs : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
    rw [habs, Complex.real_smul] at hg_sub
    have hrw : ∀ v : ℝ, Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) • F v =
        (2 * Real.pi : ℂ) * (f (2 * Real.pi * v) *
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ))) := by
      intro v
      simp only [hF_def, smul_eq_mul]
      have he : Complex.exp (((2 * Real.pi * v * τ : ℝ)) * I) =
          Complex.exp (I * ((2 * Real.pi * v : ℝ) : ℂ) * (τ : ℂ)) := by
        congr 1; push_cast; ring
      rw [he]; ring
    simp_rw [hrw]
    rw [integral_const_mul, hg_sub]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
    simp only [hg_def]
    rw [deformedReflectedField_eq_lineField h0 h1 h hc0 hc1 τ]
    unfold deformedLineField
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hf_def]
    have he : Complex.exp (((c : ℂ) + (y : ℂ) * I) * (τ : ℂ)) =
        Complex.exp ((c : ℂ) * (τ : ℂ)) * Complex.exp (I * (y : ℂ) * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hc_cancel : Complex.exp (-(c : ℂ) * (τ : ℂ)) * Complex.exp ((c : ℂ) * (τ : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      have : -(c : ℂ) * (τ : ℂ) + (c : ℂ) * (τ : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]
    rw [he]
    linear_combination (f y * Complex.exp (I * (y : ℂ) * (τ : ℂ))) * (-hc_cancel)
  have hFF_eq : 𝓕 F = fun x => g (-x) := by
    funext x
    have h1' := Real.fourierInv_eq_fourier_neg F (-x)
    rw [neg_neg, hFinv_eq] at h1'
    exact h1'.symm
  have hFF_int : Integrable (𝓕 F) := by rw [hFF_eq]; exact hg_int.comp_neg
  have hinv := hF_cont.fourier_fourierInv_eq hF_int hFF_int
  rw [hFinv_eq] at hinv
  have hval := congrFun hinv (η / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul] at hval
  have hF_eval : F (η / (2 * Real.pi)) =
      2 * Real.pi * pulseAmplitude h (-I * w) * deformedScatteringPhase α w := by
    simp only [hF_def, hf_def]
    rw [mul_div_cancel₀ _ hpi0, ← hw_eq]; ring
  set H : ℝ → ℂ := fun τ => Complex.exp (-w * (τ : ℂ)) * deformedReflectedField α h τ with hH_def
  have hH_eq : ∀ τ : ℝ,
      Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ = H τ := by
    intro τ
    simp only [smul_eq_mul, hg_def, hH_def]
    have hexp : Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) *
        Complex.exp (-(c : ℂ) * (τ : ℂ)) = Complex.exp (-w * (τ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1
      have hdiv : -2 * Real.pi * τ * (η / (2 * Real.pi)) = -η * τ := by field_simp
      rw [hdiv, hw_eq]; push_cast; ring
    rw [← mul_assoc, hexp]
  have hH_int : Integrable H := by
    refine (hg_int.norm).mono' ((by fun_prop : Continuous fun τ : ℝ =>
      Complex.exp (-w * (τ : ℂ))).mul hGc).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [← hH_eq τ, smul_eq_mul, norm_mul, Complex.norm_exp]
    have hre : (((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) : ℂ) * I).re = 0 := by
      generalize -2 * Real.pi * τ * (η / (2 * Real.pi)) = r; simp
    rw [hre, Real.exp_zero, one_mul]
  have hsplit : (∫ τ in Ioi (0 : ℝ), H τ) + (∫ τ in Iic (0 : ℝ), H τ) = ∫ τ : ℝ, H τ := by
    have h1' := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hH_int
    rwa [compl_Ioi] at h1'
  have hneg_eq : (∫ τ in Iic (0 : ℝ), H τ) =
      ∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * deformedReflectedField α h (-σ) := by
    rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ioi,
      ← integral_neg_eq_self]
    have hae : ∀ᵐ σ : ℝ, σ ≠ 0 := by
      rw [ae_iff]
      have hset : {σ : ℝ | ¬σ ≠ 0} = ({0} : Set ℝ) := by ext σ; simp
      rw [hset]; exact measure_singleton 0
    refine integral_congr_ae (hae.mono fun σ hσ => ?_)
    dsimp only
    rcases lt_or_gt_of_ne hσ with hlt | hgt
    · rw [indicator_of_notMem (show -σ ∉ Iic (0 : ℝ) by simp; linarith),
        indicator_of_notMem (show σ ∉ Ioi (0 : ℝ) by simp; linarith)]
    · rw [indicator_of_mem (show -σ ∈ Iic (0 : ℝ) by simp; linarith),
        indicator_of_mem (show σ ∈ Ioi (0 : ℝ) from hgt)]
      simp only [hH_def]; push_cast; ring_nf
  rw [← hneg_eq, hsplit]
  calc ∫ τ : ℝ, H τ
      = ∫ τ : ℝ, Complex.exp ((-2 * Real.pi * τ * (η / (2 * Real.pi)) : ℝ) * I) • g τ :=
        integral_congr_ae (Eventually.of_forall fun τ => (hH_eq τ).symm)
    _ = F (η / (2 * Real.pi)) := hval
    _ = 2 * Real.pi * pulseAmplitude h (-I * w) * deformedScatteringPhase α w := hF_eval

/-- Uniform bound on `primeTwoScatteringGate α u` across `-σ ≤ Re u ≤ 0` when `σ < (1 - α)/2`. -/
private theorem exists_primeTwoScatteringGate_left_le {α σ : ℝ}
    (h0 : 1 / 2 < α) (h1 : α < 1) (hσ0 : 0 < σ) (hσα : σ < (1 - α) / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 → ‖primeTwoScatteringGate α u‖ ≤ K := by
  set η : ℝ := 1 - (2 : ℝ) ^ (2 * σ + α - 1)
  have hη : 0 < η := by
    have : (2 : ℝ) ^ (2 * σ + α - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  refine ⟨15 / (2 * η ^ 2), by positivity, fun u hu1 hu2 => ?_⟩
  set v : ℂ := (2 : ℂ) ^ (-2 * u)
  have hv_le : ‖v‖ ≤ (2 : ℝ) ^ (2 * σ) := by
    rw [show v = ((2 : ℝ) : ℂ) ^ (-2 * u) by simp [v],
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    have hre : (-2 * u).re = -2 * u.re := by simp
    rw [hre]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hv_two : ‖v‖ ≤ 2 := hv_le.trans (by
    have : (2 : ℝ) ^ (2 * σ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using this)
  have hnum : ‖schurNum 2 (primeTwoTrace α) v‖ ≤ 15 := by
    obtain ⟨htr0, htr3⟩ := primeTwoTrace_pos_and_lt_three (by linarith) h1
    rw [abs_of_pos htr0] at htr3
    unfold schurNum
    calc ‖(1 : ℂ) - (primeTwoTrace α : ℂ) * v + 2 * v ^ 2‖
        ≤ ‖(1 : ℂ) - (primeTwoTrace α : ℂ) * v‖ + ‖(2 : ℂ) * v ^ 2‖ := norm_add_le _ _
      _ ≤ 1 + ‖(primeTwoTrace α : ℂ) * v‖ + ‖(2 : ℂ) * v ^ 2‖ := by
          linarith [norm_sub_le (1 : ℂ) ((primeTwoTrace α : ℂ) * v), norm_one (α := ℂ)]
      _ = 1 + primeTwoTrace α * ‖v‖ + 2 * ‖v‖ ^ 2 := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_real,
            Real.norm_of_nonneg htr0.le]
      _ ≤ 15 := by nlinarith [norm_nonneg v]
  have hden_lb : 2 * η ^ 2 ≤ ‖schurDen 2 (primeTwoTrace α) v‖ := by
    rw [schurDen_primeTwo_eq_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    have hb1 : η ≤ ‖(1 : ℂ) - (((2 : ℝ) ^ (-α) : ℝ) : ℂ) * v‖ := by
      have hn : ‖(((2 : ℝ) ^ (-α) : ℝ) : ℂ) * v‖ ≤ 1 - η := by
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
        calc (2 : ℝ) ^ (-α) * ‖v‖
            ≤ (2 : ℝ) ^ (-α) * (2 : ℝ) ^ (2 * σ) :=
              mul_le_mul_of_nonneg_left hv_le (Real.rpow_pos_of_pos (by norm_num) _).le
          _ = (2 : ℝ) ^ (-α + 2 * σ) := (Real.rpow_add (by norm_num) _ _).symm
          _ ≤ (2 : ℝ) ^ (2 * σ + α - 1) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 1 - η := by simp [η]
      have htri := norm_sub_rev (1 : ℂ) ((((2 : ℝ) ^ (-α) : ℝ) : ℂ) * v)
      have hsub := norm_sub_norm_le (1 : ℂ) ((((2 : ℝ) ^ (-α) : ℝ) : ℂ) * v)
      rw [norm_one] at hsub
      linarith
    have hb2 : η ≤ ‖(1 : ℂ) - (((2 : ℝ) ^ (α - 1) : ℝ) : ℂ) * v‖ := by
      have hn : ‖(((2 : ℝ) ^ (α - 1) : ℝ) : ℂ) * v‖ ≤ 1 - η := by
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
        calc (2 : ℝ) ^ (α - 1) * ‖v‖
            ≤ (2 : ℝ) ^ (α - 1) * (2 : ℝ) ^ (2 * σ) :=
              mul_le_mul_of_nonneg_left hv_le (Real.rpow_pos_of_pos (by norm_num) _).le
          _ = (2 : ℝ) ^ (α - 1 + 2 * σ) := (Real.rpow_add (by norm_num) _ _).symm
          _ = 1 - η := by simp [η]; ring_nf
      have hsub := norm_sub_norm_le (1 : ℂ) ((((2 : ℝ) ^ (α - 1) : ℝ) : ℂ) * v)
      rw [norm_one] at hsub
      linarith
    have hmul : η * η ≤
        ‖(1 : ℂ) - (((2 : ℝ) ^ (-α) : ℝ) : ℂ) * v‖ *
          ‖(1 : ℂ) - (((2 : ℝ) ^ (α - 1) : ℝ) : ℂ) * v‖ :=
      mul_le_mul hb1 hb2 hη.le (by linarith)
    nlinarith
  rw [primeTwoScatteringGate, norm_div]
  exact div_le_div₀ (by norm_num) hnum (by positivity) hden_lb

/-- **Unconditional Sub-Threshold Ringdown.** For `1/2 < α < 1`, every `h : CompactPulse`, and
every `0 < σ < min(1/16, (1 - α)/2)`, `deformedReflectedField α h τ = O(e^{-σ τ})` for `τ ≥ 0`. -/
theorem deformedReflectedField_decay {α σ : ℝ}
    (h0 : 1 / 2 < α) (h1 : α < 1) (hσ0 : 0 < σ)
    (hσ16 : σ < 1 / 16) (hσα : σ < (1 - α) / 2) (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      ‖deformedReflectedField α h τ‖ ≤ C * Real.exp (-σ * τ) := by
  have hzf_ζ : ∀ z : ℂ, (7 / 8 : ℝ) < z.re → riemannZeta z ≠ 0 := by
    intro z hz hζ
    have hmem := riemannZeta_zero_mem_quasiRH_strip (by linarith) hζ
    linarith [hmem.2]
  obtain ⟨κ₁, hκ₁, hζ_lb⟩ := exists_zeta_lower_bound_subpolynomial_of_zeroFree (Θ := 7 / 8)
    (by norm_num) (by norm_num) hzf_ζ (δ := 2 * (1 / 16 - σ)) (by linarith) (by linarith)
    (ε := 1) one_pos
  set boxU : Set ℂ := {u : ℂ | (-σ ≤ u.re ∧ u.re ≤ 0) ∧ 1 ≤ |u.im| ∧ |u.im| ≤ 3}
  have hboxU_c : IsCompact boxU := by
    have heq : boxU = ((Icc (-σ) 0) ×ℂ (Icc (-3 : ℝ) 3)) ∩ {u : ℂ | 1 ≤ |u.im|} := by
      ext u
      simp only [boxU, mem_inter_iff, Complex.mem_reProdIm, mem_Icc, mem_setOf_eq, abs_le]
      tauto
    rw [heq]
    exact (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im))
  have hcont_ζU : ContinuousOn (fun u : ℂ => (riemannZeta (1 + 2 * u))⁻¹) boxU := by
    intro u hu
    have hne1 : 1 + 2 * u ≠ 1 := fun he => by
      have him0 := congrArg Complex.im he; simp at him0
      have := hu.2.1; rw [him0, abs_zero] at this; linarith
    have hz0 : riemannZeta (1 + 2 * u) ≠ 0 := hzf_ζ _ (by simp; linarith [hu.1.1])
    exact ((ContinuousAt.comp (differentiableAt_riemannZeta hne1).continuousAt
      (by fun_prop)).inv₀ hz0).continuousWithinAt
  obtain ⟨Mζ, hMζ⟩ := hboxU_c.exists_bound_of_continuousOn hcont_ζU
  have hζ_strip : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 → 1 ≤ |u.im| →
      ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ (max (max Mζ 0) (4 / κ₁)) * |u.im| ^ 1 := by
    intro u hu1 hu2 hut
    have hpow1 : (1 : ℝ) ≤ |u.im| ^ 1 := by simpa using hut
    rcases le_or_gt |u.im| 3 with hsmall | hbig
    · have hmem : u ∈ boxU := ⟨⟨hu1, hu2⟩, hut, hsmall⟩
      calc ‖(riemannZeta (1 + 2 * u))⁻¹‖ ≤ Mζ := hMζ u hmem
        _ ≤ max (max Mζ 0) (4 / κ₁) * 1 := by
            rw [mul_one]; exact (le_max_left Mζ 0).trans (le_max_left _ _)
        _ ≤ max (max Mζ 0) (4 / κ₁) * |u.im| ^ 1 :=
            mul_le_mul_of_nonneg_left hpow1 (by positivity)
    · have him : |(1 + 2 * u).im| = 2 * |u.im| := by
        have : (1 + 2 * u).im = 2 * u.im := by simp
        rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hb := hζ_lb (1 + 2 * u) (by simp; linarith) (by rw [him]; linarith)
      rw [Real.rpow_neg_one, him] at hb
      have hpos : 0 < ‖riemannZeta (1 + 2 * u)‖ := lt_of_lt_of_le (by positivity) hb
      rw [norm_inv, inv_le_comm₀ hpos (by positivity)]
      have h2t : 2 + 2 * |u.im| ≤ 4 * |u.im| := by linarith
      calc (max (max Mζ 0) (4 / κ₁) * |u.im| ^ 1)⁻¹
          ≤ ((4 / κ₁) * |u.im|)⁻¹ := by
            rw [pow_one]
            exact inv_anti₀ (by positivity)
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
        _ = κ₁ * (4 * |u.im|)⁻¹ := by field_simp
        _ ≤ κ₁ * (2 + 2 * |u.im|)⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2t) hκ₁.le
        _ ≤ ‖riemannZeta (1 + 2 * u)‖ := hb
  obtain ⟨Cφ, Mφ, hCφ, hφ⟩ := exists_norm_modularScatteringPhase_strip_le (by positivity) hζ_strip
  obtain ⟨KG, hKG, hG⟩ := exists_primeTwoScatteringGate_left_le h0 h1 hσ0 hσα
  obtain ⟨Ca, hCa, hrap⟩ := h.rapidAmplitude.decay σ (Mφ + 2)
  have hxi_left : ∀ u : ℂ, -σ ≤ u.re → xiDeformed α (1 + 2 * u) ≠ 0 := by
    intro u hu1
    refine mul_ne_zero
      (primeTwoFactor_ne_zero_of_gt (by linarith) (by simp; linarith) (by simp; linarith)) ?_
    rcases lt_or_ge (1 + 2 * u).re 1 with hlt | hge
    · have hne1 : 1 + 2 * u ≠ 1 := fun he => by rw [he, one_re] at hlt; exact lt_irrefl _ hlt
      have hpos : 0 < (1 + 2 * u).re := by simp; linarith
      rw [Ne, xi_eq_zero_iff hpos hne1]
      exact hzf_ζ _ (by simp; linarith)
    · exact xi_ne_zero_of_one_le_re hge
  set Kbox : Set ℂ := Icc (-σ) 0 ×ℂ Icc (-1 : ℝ) 1
  have hKbox : IsCompact Kbox := isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn (fun u => pulseAmplitude h (-I * u) * deformedScatteringPhase α u)
      Kbox := by
    intro u hu
    have hu' := Complex.mem_reProdIm.1 hu
    have hne : u ≠ 1 / 2 := fun he => by have := hu'.1.2; rw [he] at this; norm_num at this
    exact (((h.differentiable_amplitude _).comp u (by fun_prop)).mul
      (differentiableAt_deformedScatteringPhase hne (hxi_left u hu'.1.1))).continuousAt.continuousWithinAt
  obtain ⟨B₀, hB₀⟩ := hKbox.exists_bound_of_continuousOn hcontK
  set B : ℝ := max (2 * max B₀ 0) ((KG * Cφ) * Ca)
  have hB_left : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 →
      ‖pulseAmplitude h (-I * u) * deformedScatteringPhase α u‖ ≤ B / (1 + u.im ^ 2) := by
    intro u hu1 hu2
    by_cases hut : 1 ≤ |u.im|
    · have hφu : ‖deformedScatteringPhase α u‖ ≤ (KG * Cφ) * |u.im| ^ Mφ := by
        rw [deformedScatteringPhase_eq_mul, norm_mul]
        calc ‖primeTwoScatteringGate α u‖ * ‖modularScatteringPhase u‖
            ≤ KG * (Cφ * |u.im| ^ Mφ) := mul_le_mul (hG u hu1 hu2) (hφ u hu1 hu2 hut)
                (norm_nonneg _) (by positivity)
          _ = (KG * Cφ) * |u.im| ^ Mφ := by ring
      have hw1 : (-I * u).re = u.im := by simp
      have hw2 : (-I * u).im = -u.re := by simp
      have ha := hrap (-I * u) (by rw [hw2, abs_neg, abs_le]; constructor <;> linarith)
      rw [hw1] at ha
      have ht1 : |u.im| ^ Mφ ≤ (1 + |u.im|) ^ Mφ :=
        pow_le_pow_left₀ (abs_nonneg _) (by linarith) Mφ
      have ht2 : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by nlinarith [abs_nonneg u.im, sq_abs u.im]
      rw [le_div_iff₀ (by positivity), norm_mul]
      calc ‖pulseAmplitude h (-I * u)‖ * ‖deformedScatteringPhase α u‖ * (1 + u.im ^ 2)
          ≤ ‖pulseAmplitude h (-I * u)‖ * ((KG * Cφ) * (1 + |u.im|) ^ Mφ) * (1 + |u.im|) ^ 2 := by
            gcongr
            exact hφu.trans (mul_le_mul_of_nonneg_left ht1 (by positivity))
        _ = (KG * Cφ) * (‖pulseAmplitude h (-I * u)‖ * (1 + |u.im|) ^ (Mφ + 2)) := by ring
        _ ≤ (KG * Cφ) * Ca := mul_le_mul_of_nonneg_left ha (by positivity)
        _ ≤ B := le_max_right _ _
    · have hut' := abs_le.1 (not_le.1 hut).le
      have hb := hB₀ u (Complex.mem_reProdIm.2 ⟨⟨hu1, hu2⟩, hut'⟩)
      have hsq : u.im ^ 2 ≤ 1 := by nlinarith
      rw [le_div_iff₀ (by positivity)]
      calc ‖pulseAmplitude h (-I * u) * deformedScatteringPhase α u‖ * (1 + u.im ^ 2)
          ≤ max B₀ 0 * 2 := mul_le_mul (hb.trans (le_max_left _ _)) (by linarith) (by positivity)
            (le_max_right _ _)
        _ ≤ B := by linarith [le_max_left (2 * max B₀ 0) ((KG * Cφ) * Ca)]
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  set Φ : ℂ → ℂ := fun u => pulseAmplitude h (-I * u) * deformedScatteringPhase α u *
    Complex.exp (u * (τ : ℂ)) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → -σ ≤ s.re ∧ s.re ≤ 0 := by
    intro s hs; rw [uIcc_of_ge (by linarith)] at hs; exact hs
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
    exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
      (differentiableAt_deformedScatteringPhase hne (hxi_left s hs1))).mul (by fun_prop))
  have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → ‖Φ s‖ ≤ B / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have he : ‖Complex.exp (s * (τ : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have : (s * (τ : ℂ)).re = s.re * τ := by simp
      rw [this]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hs2 hτ)
    simp only [hΦ, norm_mul]
    calc ‖pulseAmplitude h (-I * s) * deformedScatteringPhase α s‖ * ‖Complex.exp (s * (τ : ℂ))‖
        ≤ B / (1 + s.im ^ 2) * 1 := mul_le_mul (hB_left s hs1 hs2) he (norm_nonneg _) (by positivity)
      _ = B / (1 + s.im ^ 2) := mul_one _
  have hshift := integral_vertical_line_shift_of_decay hd hbΦ
  have hpk : deformedReflectedField α h τ = ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [← deformedLineField_zero]; rfl
  rw [hpk, hshift]
  have hpt : ∀ t : ℝ,
      ‖Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) := by
    intro t
    have hre : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).re = -σ := by simp
    have him : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
    simp only [hΦ, norm_mul, Complex.norm_exp]
    have : ((((-σ : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ)).re = -σ * τ := by simp
    rw [this]
    have hb := hB_left _ (by rw [hre]) (by rw [hre]; linarith)
    rw [him, div_eq_mul_inv] at hb
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hint : Integrable fun t : ℝ => B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) :=
    (integrable_inv_one_add_sq.const_mul B).mul_const _
  calc ‖∫ t : ℝ, Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = B * Real.pi * Real.exp (-σ * τ) := by
        rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

/-- **Strict Failure of Decay Above `(1 - α) / 2`.** For `1/2 < α < 1` and every `δ > (1 - α) / 2`,
the smooth compactly supported pulse `excitingPulse (((α : ℂ) - 1) / 2)` fails `O(e^{-δ τ})`. -/
theorem not_deformedReflectedField_decay_gt {α δ : ℝ}
    (h0 : 1 / 2 < α) (h1 : α < 1) (hδ : (1 - α) / 2 < δ) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖deformedReflectedField α (excitingPulse (((α : ℂ) - 1) / 2)) τ‖ ≤
        C * Real.exp (-δ * τ) := by
  rintro ⟨C₀, hC₀⟩
  have hα0 : 0 < α := by linarith
  set p : ℂ := ((α : ℂ) - 1) / 2 with hpdef
  set h := excitingPulse p
  have hp1 : 1 + 2 * p = (α : ℂ) := by rw [hpdef]; ring
  have hpxi : xiDeformed α (1 + 2 * p) = 0 := by
    rw [hp1, xiDeformed, primeTwoFactor_eval_self, zero_mul]
  have hpre : p.re = (α - 1) / 2 := by rw [hpdef]; simp
  have hp_neg : p.re < 0 := by rw [hpre]; linarith
  have hp_gt : -δ < p.re := by rw [hpre]; linarith
  obtain ⟨hGc, -⟩ := continuous_deformedReflectedField_and_bounded hα0 h1 h
  obtain ⟨Ce, hCe, hGe⟩ := exists_deformedReflectedField_early_decay hα0 h1 h
  set Lpos : ℂ → ℂ := fun w => ∫ τ in Ioi (0 : ℝ),
    Complex.exp (-w * (τ : ℂ)) * deformedReflectedField α h τ with hLpos
  have hC₀' : ∀ τ : ℝ, -0 < τ → ‖deformedReflectedField α h τ‖ ≤ max C₀ 0 * Real.exp (-δ * τ) :=
    fun τ hτ => (hC₀ τ (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hLpos_d : DifferentiableOn ℂ Lpos {w : ℂ | -δ < w.re} := by
    simpa [hLpos] using RingdownRate.differentiableOn_laplace hGc (le_max_right C₀ 0) hC₀'
  set Lneg₀ : ℂ → ℂ := fun z => ∫ σ in Ioi (0 : ℝ),
    Complex.exp (-z * (σ : ℂ)) * deformedReflectedField α h (-σ) with hLneg₀
  have hGe' : ∀ σ : ℝ, -(0 : ℝ) < σ →
      ‖deformedReflectedField α h (-σ)‖ ≤ Ce * Real.exp (-(3 / 8) * σ) := by
    intro σ hσ; simpa [mul_neg, neg_mul] using hGe (-σ) (by linarith)
  have hLneg₀_d : DifferentiableOn ℂ Lneg₀ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by
    simpa [hLneg₀] using RingdownRate.differentiableOn_laplace (hGc.comp continuous_neg) hCe hGe'
  set Lneg : ℂ → ℂ := fun w => Lneg₀ (-w) with hLneg
  have hLneg_d : DifferentiableOn ℂ Lneg {w : ℂ | w.re < 3 / 8} := by
    intro w hw
    have hw' : -w ∈ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by show -(3 / 8 : ℝ) < (-w).re; simp; exact hw
    have hopen : IsOpen {z : ℂ | -(3 / 8 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact ((hLneg₀_d (-w) hw').differentiableAt (hopen.mem_nhds hw')).comp w differentiableAt_id.neg
      |>.differentiableWithinAt
  set S : Set ℂ := {w : ℂ | -δ < w.re ∧ w.re < 3 / 8}
  have hSo : IsOpen S := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hSconn : IsPreconnected S :=
    ((convex_halfSpace_re_gt (-δ)).inter (convex_halfSpace_re_lt (3 / 8))).isPreconnected
  set Φ₁ : ℂ → ℂ := fun w => (2 * w - 1) * xiDeformed α (1 + 2 * w) * (Lpos w + Lneg w) with hΦ₁
  set Φ₂ : ℂ → ℂ := fun w =>
    2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xiDeformed α (2 * w) with hΦ₂
  have hUpos : IsOpen {w : ℂ | -δ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUneg : IsOpen {w : ℂ | w.re < 3 / 8} := isOpen_lt Complex.continuous_re continuous_const
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w hw
    have h1' := (hLpos_d w hw.1).differentiableAt (hUpos.mem_nhds hw.1)
    have h2' := (hLneg_d w hw.2).differentiableAt (hUneg.mem_nhds hw.2)
    have hxi : DifferentiableAt ℂ (fun v : ℂ => xiDeformed α (1 + 2 * v)) w :=
      ((differentiable_xiDeformed α) _).comp w (by fun_prop)
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w).mul hxi).mul
      (h1'.add h2')).differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w _
    have ha : DifferentiableAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) w :=
      (h.differentiable_amplitude _).comp w (by fun_prop)
    have hxi : DifferentiableAt ℂ (fun v : ℂ => xiDeformed α (2 * v)) w :=
      ((differentiable_xiDeformed α) _).comp w (by fun_prop)
    exact ((((differentiableAt_const _).mul ha).mul (by fun_prop)).mul hxi).differentiableWithinAt
  have hagree : ∀ w : ℂ, 1 / 8 < w.re → w.re < 5 / 16 → Φ₁ w = Φ₂ w := by
    intro w hw1 hw2
    have hlap : Lpos w + Lneg w =
        2 * Real.pi * pulseAmplitude h (-I * w) * deformedScatteringPhase α w := by
      have hneg_rw : Lneg w = ∫ σ in Ioi (0 : ℝ),
          Complex.exp (w * (σ : ℂ)) * deformedReflectedField α h (-σ) := by
        simp only [hLneg, hLneg₀, neg_neg]
      rw [hneg_rw]
      exact deformed_bilateral_laplace_eq hα0 h1 h hw1 hw2
    have h2w : 2 * w - 1 ≠ 0 := fun h0' => by
      have := congrArg Complex.re h0'; simp at this; linarith
    have hxi : xiDeformed α (1 + 2 * w) ≠ 0 :=
      xiDeformed_ne_zero_of_one_le_re hα0 h1 (by simp; linarith)
    simp only [hΦ₁, hΦ₂, hlap, deformedScatteringPhase]
    field_simp
  have hEq : EqOn Φ₁ Φ₂ S := by
    refine hΦ₁a.eqOn_of_preconnected_of_eventuallyEq hΦ₂a hSconn
      (show (1 / 4 : ℂ) ∈ S from ⟨by simp; linarith, by norm_num⟩) ?_
    have hV : IsOpen {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hV.mem_nhds (show (1 / 4 : ℂ) ∈ {w : ℂ | 1 / 8 < w.re ∧ w.re < 5 / 16} by
      norm_num)] with w hw
    exact hagree w hw.1 hw.2
  have hpS : p ∈ S := ⟨hp_gt, by linarith⟩
  have hp_eq := hEq hpS
  simp only [hΦ₁, hΦ₂, hpxi, mul_zero, zero_mul] at hp_eq
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have ha_ne : pulseAmplitude h (-I * p) ≠ 0 := pulseAmplitude_excitingPulse_ne_zero p
  have h12p : 1 + 2 * p ≠ 0 := by
    rw [hp1]; exact Complex.ofReal_ne_zero.mpr hα0.ne'
  have hxi2p : xiDeformed α (2 * p) ≠ 0 := by
    rw [← xiDeformed_one_sub α (2 * p)]
    exact xiDeformed_ne_zero_of_one_le_re hα0 h1 (by simp [hpre]; linarith)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi ha_ne) h12p) hxi2p hp_eq.symm

/-- **Universal Causal Decay Infimum is Zero.** For every `δ > 0` (including `δ = 1/4` and
`δ = 1/16`), there exists `α ∈ (7/8, 1)` such that the prime-`2` deformed horizon system satisfies:
1. retarded time-domain echo causality (`deformedEchoKernel α τ = 0` for `τ ≤ 0`) and exact Laplace
   representation on `Re w > 1/2`;
2. convergent Euler product over `Nat.Primes` on `Re w > 1/2`;
3. completed functional equation `ξ_α(1 - s) = ξ_α(s)`, global Schur passivity
   `‖ξ_α(2w)/ξ_α(1+2w)‖ ≤ 1` and non-negative Herglotz admittance on `Re w ≥ 0`, and unitarity
   `‖φ_α(it)‖ = 1` on `ℝ`;
4. exact single- and two-boundary (`G_{R,α}` and `G_{RL,α}`) pole-order dictionary for every
   nontrivial zero of `ζ`;
5. unconditional sub-threshold decay `O(e^{-σ τ})` for all `0 < σ < (1 - α)/2`, yet **strict
   failure** of `O(e^{-δ τ})` for an explicit smooth compactly supported pulse. -/
theorem universal_causal_ringdown_infimum_zero {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 7 / 8 < α ∧ α < 1 ∧
      (∀ τ : ℝ, τ ≤ 0 → deformedEchoKernel α τ = 0) ∧
      (∀ w : ℂ, 1 / 2 < w.re →
        HasProd (fun p : Nat.Primes => deformedPrimeGate α p w)
          (primeTwoScatteringGate α w * (riemannZeta (2 * w) / riemannZeta (2 * w + 1)))) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖deformedReducedScattering α w‖ ≤ 1 ∧
        0 ≤ ((1 - deformedReducedScattering α w) / (1 + deformedReducedScattering α w)).re) ∧
      (∀ t : ℝ, ‖deformedScatteringPhase α ((t : ℂ) * I)‖ = 1) ∧
      (∀ ρ : ℂ, xi ρ = 0 →
        meromorphicOrderAt (deformedWightmanRL α) (I * (ρ - 1) / 2) < 0) ∧
      (∀ σ : ℝ, 0 < σ → σ < (1 - α) / 2 → ∀ h : CompactPulse, ∃ C : ℝ, 0 ≤ C ∧
        ∀ τ : ℝ, 0 ≤ τ → ‖deformedReflectedField α h τ‖ ≤ C * Real.exp (-σ * τ)) ∧
      (∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖deformedReflectedField α h τ‖ ≤ C * Real.exp (-δ * τ)) := by
  set α : ℝ := max (15 / 16) (1 - δ) with hαdef
  have hα78 : 7 / 8 < α := lt_of_lt_of_le (by norm_num : (7 / 8 : ℝ) < 15 / 16) (le_max_left _ _)
  have hα1 : α < 1 := max_lt (by norm_num) (by linarith)
  have hα_half : 1 / 2 < α := by linarith
  have hδ_gt : (1 - α) / 2 < δ := by
    have hle : 1 - δ ≤ α := le_max_right _ _
    linarith
  refine ⟨α, hα78, hα1, fun τ hτ => deformedEchoKernel_eq_zero_of_nonpos α hτ,
    fun w hw => hasProd_deformedPrimeGate hw,
    fun w hw => norm_deformedReducedScattering_le_one (by linarith) hα1 hw,
    fun t => norm_deformedScatteringPhase_axis (by linarith) hα1 t, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨hr0, hr1⟩ := zero_mem_openStrip_of_xi_eq_zero hρ
    set ω : ℂ := I * (ρ - 1) / 2 with hω
    have him : ω.im = (ρ.re - 1) / 2 := by rw [hω]; simp
    have h12 : 1 - 2 * I * ω = ρ := by rw [hω]; linear_combination (1 - ρ) * I_sq
    have hz : xiDeformed α (1 - 2 * I * ω) = 0 := by rw [h12, xiDeformed, hρ, mul_zero]
    rw [deformedWightmanRL_order_lower (by linarith) hα1 (by rw [him]; linarith)
      (by rw [him]; linarith) hz]
    exact (meromorphicOrderAt_pos_of_entire_zero (differentiable_xiDeformed α)
      (fun _ => xiDeformed_ne_zero_of_one_le_re (by linarith) hα1) hz).2.1
  · intro σ hσ0 hσα h
    have hσ16 : σ < 1 / 16 := by linarith
    exact deformedReflectedField_decay hα_half hα1 hσ0 hσ16 hσα h
  · exact ⟨excitingPulse (((α : ℂ) - 1) / 2),
      not_deformedReflectedField_decay_gt hα_half hα1 hδ_gt⟩

/-! ## 5. Smooth 4D Vacuum Einstein–AdS Bulk + Locally Tempered Geodesic Obstruction -/

/-- Simple-pole logarithmic-derivative dictionary for `CompactQuotient.selbergZeta` on `Re s > 0`. -/
theorem CompactQuotient.meromorphicOrderAt_logDeriv_selbergZeta
    {X : CompactQuotient} (hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ|) {a : ℝ} (ha : 1 < a)
    {s₀ : ℂ} (hs₀ : 0 < s₀.re) :
    (meromorphicOrderAt (logDeriv (X.selbergZeta ha)) s₀ < 0 ↔ X.selbergZeta ha s₀ = 0) ∧
      (X.selbergZeta ha s₀ = 0 →
        meromorphicOrderAt (logDeriv (X.selbergZeta ha)) s₀ = ((-1 : ℤ) : WithTop ℤ)) := by
  set U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hanU : AnalyticOnNhd ℂ (X.selbergZeta ha) U :=
    (X.differentiableOn_selbergZeta ha).analyticOnNhd hUo
  have han0 : AnalyticAt ℂ (X.selbergZeta ha) s₀ := hanU s₀ hs₀
  have hord_iff : X.selbergZeta ha s₀ = 0 →
      meromorphicOrderAt (logDeriv (X.selbergZeta ha)) s₀ = ((-1 : ℤ) : WithTop ℤ) := by
    intro hz
    have hntop : analyticOrderAt (X.selbergZeta ha) s₀ ≠ ⊤ := by
      intro htop
      have hev := analyticOrderAt_eq_top.mp htop
      have hp_re : 1 < ((a + 1 : ℝ) : ℂ).re := by simp; linarith
      have hpU : ((a + 1 : ℝ) : ℂ) ∈ U := by show 0 < ((a + 1 : ℝ) : ℂ).re; linarith
      have hzp := hanU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hs₀ hev hpU
      rw [← X.eulerZeta_eq_selbergZeta hhyp ha hp_re] at hzp
      exact X.eulerZeta_ne_zero hhyp hp_re hzp
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hntop
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hp
      · exfalso; exact ((analyticOrderAt_eq_zero.mp hm.symm).resolve_left (not_not.mpr han0)) hz
      · exact hp
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    have horder : analyticOrderAt (X.selbergZeta ha) s₀ = (k + 1 : ℕ) := hm.symm
    have hderiv : analyticOrderAt (deriv (X.selbergZeta ha)) s₀ = k :=
      analyticOrderAt_deriv_of_pos han0 horder
    rw [show logDeriv (X.selbergZeta ha) = deriv (X.selbergZeta ha) / X.selbergZeta ha by
      funext z; rw [logDeriv_apply]; rfl]
    rw [meromorphicOrderAt_div han0.deriv.meromorphicAt han0.meromorphicAt,
      han0.deriv.meromorphicOrderAt_eq, han0.meromorphicOrderAt_eq, hderiv, horder,
      ENat.map_coe, ENat.map_coe]
    exact_mod_cast (show (k : ℤ) - ((k + 1 : ℕ) : ℤ) = -1 by omega)
  refine ⟨⟨?_, fun hz => by rw [hord_iff hz]; norm_num⟩, hord_iff⟩
  intro hpole
  by_contra hnz
  have hlog_an : AnalyticAt ℂ (logDeriv (X.selbergZeta ha)) s₀ := by
    rw [show logDeriv (X.selbergZeta ha) = deriv (X.selbergZeta ha) / X.selbergZeta ha by
      funext z; rw [logDeriv_apply]; rfl]
    exact han0.deriv.div han0 hnz
  exact (not_lt_of_ge hlog_an.meromorphicOrderAt_nonneg) hpole

/-- **4D Vacuum Einstein–AdS Bulk + Locally Tempered Geodesic Obstruction.**
There exist an odd `n ≥ 3`, a cocompact torsion-free subgroup `Γ_n = coverGroup n ≤ SL₂(ℝ)` with
compact quotient `X`, and a real off-line zero `s₀ ∈ (1/2, 1)` (`a = 2`) such that:
1. `Γ_n` acts by `SO(3,2)` isometries on the global two-boundary Kruskal–Maldacena `AdS₄` quadric
   `kruskalEmbedding` and commutes identically with `wedgeReflection`;
2. every primitive closed-geodesic Euler factor `X.eulerFactor x s` is locally tempered, vanishing
   only on `Re s = -k ≤ 0`;
3. `logDeriv (X.selbergZeta _)` agrees with the prime-geodesic `lengthSeries` on `Re s > 1` and has
   a simple pole (`meromorphicOrderAt = -1`) at every Selberg zero on `Re s > 0` (analytic
   elsewhere);
4. yet `X.selbergZeta _ s₀ = 0` with `1/2 < Re s₀ < 1`, violating quarter-rate damping
   `(1 - Re s₀)/2 < 1/4`. -/
theorem exists_eternalAdS_compact_blackHole_violating_quarter_decay :
    let ha : (1 : ℝ) < 2 := by norm_num
    ∃ (n : ℕ) (X : CompactQuotient) (s₀ : ℂ),
      Odd n ∧ 3 ≤ n ∧ X.Γ = coverGroup n ∧
      (∀ (γ : X.Γ) (U V : ℝ) (z : UpperHalfPlane),
        kruskalEmbedding U V ((γ : SL(2, ℝ)) • z).re ((γ : SL(2, ℝ)) • z).im =
          ambientLorentz ((γ : SL(2, ℝ)) 0 0) ((γ : SL(2, ℝ)) 0 1)
            ((γ : SL(2, ℝ)) 1 0) ((γ : SL(2, ℝ)) 1 1)
            (kruskalEmbedding U V z.re z.im) ∧
        wedgeReflection (kruskalEmbedding U V ((γ : SL(2, ℝ)) • z).re ((γ : SL(2, ℝ)) • z).im) =
          kruskalEmbedding (-U) (-V) ((γ : SL(2, ℝ)) • z).re ((γ : SL(2, ℝ)) • z).im) ∧
      (∀ (x : X.PClass × ℕ) (s : ℂ), X.eulerFactor x s = 0 → s.re ≤ 0) ∧
      (∀ s : ℂ, 1 < s.re → logDeriv (X.selbergZeta ha) s = X.lengthSeries s) ∧
      (∀ s : ℂ, 0 < s.re →
        (meromorphicOrderAt (logDeriv (X.selbergZeta ha)) s < 0 ↔ X.selbergZeta ha s = 0)) ∧
      1 / 2 < s₀.re ∧ s₀.re < 1 ∧
      X.selbergZeta ha s₀ = 0 ∧
      meromorphicOrderAt (logDeriv (X.selbergZeta ha)) s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
      (1 - s₀.re) / 2 < 1 / 4 := by
  intro ha
  obtain ⟨n, hn_odd, hn3, hsmall⟩ := exists_coverGroup_small_eigenvalue ha
  obtain ⟨X, hX⟩ := exists_compactQuotient_coverGroup hn_odd
  obtain ⟨j, hj0, hj1⟩ := hsmall X hX
  have hhyp : ∀ γ : X.Γ, γ ≠ 1 → 2 < |trSL γ| := by
    intro γ hγ
    have hmem : (γ : SL(2, ℝ)) ∈ coverGroup n := by rw [← hX]; exact γ.2
    obtain ⟨h5, _⟩ := hmem
    have hne5 : (⟨(γ : SL(2, ℝ)), h5⟩ : congGroup 5) ≠ 1 := fun he =>
      hγ (Subtype.ext (congrArg (fun x : congGroup 5 => (x : SL(2, ℝ))) he))
    exact two_lt_abs_trSL_congGroup (by norm_num : 3 ≤ 5) ⟨(γ : SL(2, ℝ)), h5⟩ hne5
  set s₀ : ℂ := ((1 / 2 + Real.sqrt (1 / 4 - X.spectralParam ha j) : ℝ) : ℂ) with hs₀def
  have hsqrt_pos : 0 < Real.sqrt (1 / 4 - X.spectralParam ha j) :=
    Real.sqrt_pos.mpr (by linarith)
  have hsqrt_lt : Real.sqrt (1 / 4 - X.spectralParam ha j) < 1 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  have hs₀_re1 : 1 / 2 < s₀.re := by rw [hs₀def, Complex.ofReal_re]; linarith
  have hs₀_re2 : s₀.re < 1 := by rw [hs₀def, Complex.ofReal_re]; linarith
  have hs₀_mem : s₀ ∈ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ s.re ≠ 1 / 2 ∧ X.selbergZeta ha s = 0} := by
    rw [X.offLine_zeros_eq hhyp ha]
    exact ⟨j, hj0, hj1, Or.inl rfl⟩
  refine ⟨n, X, s₀, hn_odd, hn3, hX, ?_, ?_, ?_, ?_, hs₀_re1, hs₀_re2, hs₀_mem.2.2.2, ?_, ?_⟩
  · intro γ U V z
    exact ⟨kruskalEmbedding_smul_SL2R U V (γ : SL(2, ℝ)) z,
      (kruskalEmbedding_neg U V _ _).symm⟩
  · intro x s hfac
    unfold CompactQuotient.eulerFactor at hfac
    have hexp : Complex.exp (-((s + x.2) * X.classLen x.1.1)) = 1 :=
      (sub_eq_zero.mp hfac).symm
    have hnorm := congrArg norm hexp
    rw [norm_one, Complex.norm_exp] at hnorm
    have hre0 : (-((s + (x.2 : ℂ)) * (X.classLen x.1.1 : ℂ))).re = 0 :=
      Real.exp_eq_one_iff.mp hnorm
    have hre_calc : (-((s + (x.2 : ℂ)) * (X.classLen x.1.1 : ℂ))).re =
        -((s.re + x.2) * X.classLen x.1.1) := by simp
    rw [hre_calc, neg_eq_zero, mul_eq_zero] at hre0
    have hlen_pos : 0 < X.classLen x.1.1 := X.pLen_pos hhyp x.1
    have hsum0 : s.re + x.2 = 0 := hre0.resolve_right hlen_pos.ne'
    have hx_nonneg : (0 : ℝ) ≤ x.2 := Nat.cast_nonneg x.2
    linarith
  · intro s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : X.selbergZeta ha =ᶠ[𝓝 s] X.eulerZeta :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hs) fun z hz =>
        (X.eulerZeta_eq_selbergZeta hhyp ha hz).symm
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds,
      ← logDeriv_apply, X.logDeriv_eulerZeta hhyp hs]
  · intro s hs
    exact (X.meromorphicOrderAt_logDeriv_selbergZeta hhyp ha hs).1
  · exact (X.meromorphicOrderAt_logDeriv_selbergZeta hhyp ha (by linarith)).2 hs₀_mem.2.2.2
  · linarith

#print axioms primeTwoFactor_div_eq_primeTwoScatteringGate
#print axioms norm_deformedReducedScattering_le_one
#print axioms integral_cexp_mul_deformedEchoKernel
#print axioms deformedWightmanRL_order_lower
#print axioms deformedReflectedField_decay
#print axioms not_deformedReflectedField_decay_gt
#print axioms universal_causal_ringdown_infimum_zero
#print axioms exists_eternalAdS_compact_blackHole_violating_quarter_decay

end

end GaloisForLFunctions.BlackHoleRingdown
