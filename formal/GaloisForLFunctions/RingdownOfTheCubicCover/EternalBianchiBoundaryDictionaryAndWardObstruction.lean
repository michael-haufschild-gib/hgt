import GaloisForLFunctions.RingdownOfTheCubicCover.BianchiHorizonRingdownEquivalence
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import GaloisForLFunctions.BlackHoleRingdown.CausalIdentitiesCannotForceQuarterRingdown

/-!
# Eternal Bianchi Horizon Dictionary and Causal Ward Obstruction (`SL₂(ℤ[ω])\ℍ³`)

Companion resolution on the three-dimensional Bianchi / Eisenstein modular quotient
`SL₂(ℤ[ω])\ℍ³` (`K = ℚ(√−3) = ℚ(ζ₃)`) of the eternal-AdS / modular-horizon question:

1. **Independent Prime-Marked Bianchi Gate and Euler Factorization**:
   Each rational prime `p` carries the primitive cycle delay `2 log p` together with the split /
   inert / ramified quadratic reciprocity twist `χ₋₃(p)`, defining `chi3EchoSeries p w` and
   `bianchiPrimeGate p w = primeEchoGate p w * chi3EchoGate p w` without naming `ζ` or `L(·, χ₋₃)`.
   On `Re w > 1/2`, the Euler product over `Nat.Primes` converges (`hasProd_bianchiPrimeGate`) to
   `(ζ(2w) L(2w, χ₋₃)) / (ζ(2w + 1) L(2w + 1, χ₋₃))`, and multiplying by the Archimedean ratio
   recovers `bianchiScatteringPhase w` (`bianchiPrimeProduct_mul_archimedean_eq_scatteringPhase`).

2. **Complete Single- and Two-Boundary Singularity Dictionary**:
   For both `bianchiRetardedCorrelator ω = φ_K(-iω)` (`ω ≠ i/2`) and the trans-horizon thermofield
   Wightman correlator `bianchiWightmanRL ω` on `0 < |Im ω| < 1/2`, poles correspond bijectively
   with exact multiplicity `-ord_ρ xiBianchi` to nontrivial zeros of `ζ_K(s) = ζ(s) L(s, χ₋₃)`
   (`bianchiRetardedCorrelator_isPole_iff`, `bianchiWightmanRL_isPole_iff`). Consequently,
   analyticity of `bianchiWightmanRL` on `0 < |Im ω| < 1/4` is equivalent to GRH for `ζ_K` and
   implies `RiemannHypothesis` (`dedekind_rh_iff_bianchiWightmanRL_quarter_strip`,
   `bianchiWightmanRL_quarter_strip_implies_riemannHypothesis`), while `bianchiWightmanRL` is
   unconditionally analytic on `0 < |Im ω| < 1/16` (`bianchiWightmanRL_analyticOnNhd_one_sixteenth`).

3. **Universal Causal Ringdown Infimum is Zero on the Bianchi Horizon**:
   Coupling the retarded causal prime-`2` Schur gate (`1/2 < α < 1`) to `SL₂(ℤ[ω])\ℍ³` preserves
   Euler factorization over `Nat.Primes`, the completed functional equation `ξ_{K,α}(1 - s) =
   ξ_{K,α}(s)`, continuous-spectrum unitarity `‖φ_{K,α}(it)‖ = 1`, retarded time-domain echo
   causality (`deformedEchoKernel α τ = 0` for `τ ≤ 0`), and the complete `G_{R,K,α}` and
   `G_{RL,K,α}` singularity dictionary for all nontrivial zeros of `ζ(s) L(s, χ₋₃)`. Every smooth
   compact pulse decays as `O(e^{-σ τ})` for `0 < σ < min(1/16, (1 - α)/2)`
   (`bianchiDeformedReflectedField_decay`), while `excitingPulse (((α : ℂ) - 1) / 2)` fails
   `O(e^{-δ τ})` for every `δ > (1 - α)/2` (`not_bianchiDeformedReflectedField_decay_gt`), forcing
   the universal causal ringdown infimum on the Bianchi horizon to vanish
   (`bianchi_universal_causal_ringdown_infimum_zero`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff FourierTransform

noncomputable section

namespace GaloisForLFunctions.RingdownOfTheCubicCover

open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.BlackHoleRingdown.RingdownRate
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
  (riemannZeta_ne_zero_of_seven_eighths_lt_re)
open _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-! ## 1. Independent Prime-Marked Bianchi Gate and Euler Factorization -/

/-- Quadratic-reciprocity twisted prime echo series at primitive cycle length `2 log p` (`p ∈ ℙ`),
defined from multiple traversals `2(k + 1) log p` and character weights `χ₋₃(p)^{k+1}` without
naming `ζ` or `L(·, χ₋₃)`. -/
def chi3EchoSeries (p : Nat.Primes) (w : ℂ) : ℂ :=
  1 + ∑' k : ℕ, (1 - 1 / (p : ℂ)) * (chi3D (p : ℕ)) ^ (k + 1) *
    Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ))

/-- Closed `χ₋₃`-twisted prime transfer gate `(1 - χ₋₃(p) p^{-(2w+1)}) / (1 - χ₋₃(p) p^{-2w})`. -/
def chi3EchoGate (p : Nat.Primes) (w : ℂ) : ℂ :=
  (1 - chi3D (p : ℕ) * (p : ℂ) ^ (-(2 * w + 1))) /
    (1 - chi3D (p : ℕ) * (p : ℂ) ^ (-(2 * w)))

/-- Combined Bianchi prime-marked scattering gate on `SL₂(ℤ[ω])\ℍ³` indexed over rational primes. -/
def bianchiPrimeGate (p : Nat.Primes) (w : ℂ) : ℂ :=
  primeEchoGate p w * chi3EchoGate p w

/-- On `Re w > 0`, the twisted prime echo series sums to `chi3EchoGate p w`. -/
theorem chi3EchoSeries_eq_chi3EchoGate {w : ℂ} (hw : 0 < w.re) (p : Nat.Primes) :
    chi3EchoSeries p w = chi3EchoGate p w := by
  have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  have hppos : (0 : ℝ) < (p : ℕ) := by linarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hppos.ne'
  set z0 : ℂ := (p : ℂ) ^ (-(2 * w)) with hz0def
  set z : ℂ := chi3D (p : ℕ) * z0 with hzdef
  have hz0_lt : ‖z0‖ < 1 := by
    rw [hz0def, show (p : ℂ) = (((p : ℕ) : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hppos]
    have hre : (-(2 * w)).re = -2 * w.re := by simp
    rw [hre]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hchi_le : ‖chi3D (p : ℕ)‖ ≤ 1 := chi3D.norm_le_one (p : ℕ)
  have hznorm : ‖z‖ < 1 := by
    rw [hzdef, norm_mul]
    calc ‖chi3D (p : ℕ)‖ * ‖z0‖
        ≤ 1 * ‖z0‖ := mul_le_mul_of_nonneg_right hchi_le (norm_nonneg _)
      _ = ‖z0‖ := one_mul _
      _ < 1 := hz0_lt
  have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr fun h => by
    rw [← h, norm_one] at hznorm
    exact lt_irrefl _ hznorm
  have hexp_pow : ∀ k : ℕ,
      (chi3D (p : ℕ)) ^ (k + 1) *
        Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ)) =
        z * z ^ k := by
    intro k
    have hz0_exp : z0 = Complex.exp (-(2 * w) * ((Real.log (p : ℕ) : ℝ) : ℂ)) := by
      rw [hz0def, Complex.cpow_def_of_ne_zero hpC, ← Complex.natCast_log, mul_comm]
    have hexp_k : Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ)) =
        z0 ^ (k + 1) := by
      rw [hz0_exp, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    rw [hexp_k, ← mul_pow, ← hzdef, pow_succ']
  have hzp : chi3D (p : ℕ) * (p : ℂ) ^ (-(2 * w + 1)) = z / (p : ℂ) := by
    rw [hzdef, hz0def, show -(2 * w + 1) = -(2 * w) - 1 by ring,
      Complex.cpow_sub _ _ hpC, Complex.cpow_one, mul_div_assoc]
  unfold chi3EchoSeries chi3EchoGate
  have hterm : ∀ k : ℕ,
      (1 - 1 / (p : ℂ)) * (chi3D (p : ℕ)) ^ (k + 1) *
        Complex.exp (-w * ((2 * ((k + 1 : ℕ) : ℝ) * Real.log (p : ℕ) : ℝ) : ℂ)) =
        ((1 - 1 / (p : ℂ)) * z) * z ^ k := by
    intro k
    rw [mul_assoc, hexp_pow k, ← mul_assoc]
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hznorm, hzp, ← hzdef]
  field_simp
  ring

/-- On `Re w > 1/2`, the Euler product of `chi3EchoGate p w` over `Nat.Primes` converges to
`L(2w, χ₋₃) / L(2w + 1, χ₋₃)`. -/
theorem hasProd_chi3EchoGate {w : ℂ} (hw : 1 / 2 < w.re) :
    HasProd (fun p : Nat.Primes => chi3EchoGate p w)
      (DirichletCharacter.LFunction chi3D (2 * w) /
        DirichletCharacter.LFunction chi3D (2 * w + 1)) := by
  have h1 : 1 < (2 * w).re := by simp; linarith
  have h2 : 1 < (2 * w + 1).re := by simp; linarith
  have hp1 : HasProd (fun p : Nat.Primes => (1 - chi3D (p : ℕ) * (p : ℂ) ^ (-(2 * w)))⁻¹)
      (DirichletCharacter.LFunction chi3D (2 * w)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi3D h1]
    exact DirichletCharacter.LSeries_eulerProduct_hasProd chi3D h1
  have hp2 : HasProd (fun p : Nat.Primes => (1 - chi3D (p : ℕ) * (p : ℂ) ^ (-(2 * w + 1)))⁻¹)
      (DirichletCharacter.LFunction chi3D (2 * w + 1)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi3D h2]
    exact DirichletCharacter.LSeries_eulerProduct_hasProd chi3D h2
  have hz2 : DirichletCharacter.LFunction chi3D (2 * w + 1) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) h2.le
  have hinv : HasProd (fun p : Nat.Primes => 1 - chi3D (p : ℕ) * (p : ℂ) ^ (-(2 * w + 1)))
      (DirichletCharacter.LFunction chi3D (2 * w + 1))⁻¹ := by
    have htend : Tendsto (fun s : Finset Nat.Primes =>
        (∏ p ∈ s, (1 - chi3D (p : ℕ) * (p : ℂ) ^ (-(2 * w + 1)))⁻¹)⁻¹) atTop
        (𝓝 (DirichletCharacter.LFunction chi3D (2 * w + 1))⁻¹) :=
      Filter.Tendsto.inv₀ hp2 hz2
    refine htend.congr fun s => ?_
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun p _ => inv_inv _
  have hmul := hinv.mul hp1
  rw [div_eq_mul_inv, mul_comm]
  exact hmul.congr_fun fun p => (div_eq_mul_inv _ _).symm

/-- **Independent Prime-Marked Bianchi Euler Product.** On `Re w > 1/2`, the product of
`bianchiPrimeGate p w` over `Nat.Primes` converges to
`(ζ(2w) L(2w, χ₋₃)) / (ζ(2w + 1) L(2w + 1, χ₋₃))`. -/
theorem hasProd_bianchiPrimeGate {w : ℂ} (hw : 1 / 2 < w.re) :
    HasProd (fun p : Nat.Primes => bianchiPrimeGate p w)
      ((riemannZeta (2 * w) * DirichletCharacter.LFunction chi3D (2 * w)) /
        (riemannZeta (2 * w + 1) * DirichletCharacter.LFunction chi3D (2 * w + 1))) := by
  have h := (hasProd_primeEchoGate hw).mul (hasProd_chi3EchoGate hw)
  rwa [div_mul_div_comm] at h

/-- Archimedean completion ratio of the Bianchi horizon on `SL₂(ℤ[ω])\ℍ³`. -/
def bianchiArchimedeanFactor (w : ℂ) : ℂ :=
  ((3 : ℂ) ^ (2 * w / 2) / (3 : ℂ) ^ ((1 + 2 * w) / 2)) *
    (Complex.Gammaℝ (2 * w) / Complex.Gammaℝ (2 * w + 1)) *
    (DirichletCharacter.gammaFactor chi3D (2 * w) /
      DirichletCharacter.gammaFactor chi3D (2 * w + 1))

/-- Multiplying the convergent prime-gate product by `bianchiArchimedeanFactor w` on `Re w > 1/2`
recovers the exact Bianchi scattering phase `bianchiScatteringPhase w`. -/
theorem bianchiPrimeProduct_mul_archimedean_eq_scatteringPhase {w : ℂ} (hw : 1 / 2 < w.re) :
    bianchiArchimedeanFactor w * (∏' p : Nat.Primes, bianchiPrimeGate p w) =
      bianchiScatteringPhase w := by
  rw [(hasProd_bianchiPrimeGate hw).tprod_eq]
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; norm_num at hw
  have h2w0 : 2 * w ≠ 0 := mul_ne_zero two_ne_zero hw0
  have hwhalf : 2 * w - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hwneg : 1 + 2 * w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hwone : 2 * w ≠ 1 := fun h => hwhalf (sub_eq_zero.mpr h)
  have hwm1 : 1 + 2 * w ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [← completedBianchiZeta_div_eq_bianchiScatteringPhase hw0 hwhalf hwneg hwone hwm1]
  have h2pos : 0 < (2 * w).re := by simp; linarith
  have h21pos : 0 < (2 * w + 1).re := by simp; linarith
  have h21ne0 : 2 * w + 1 ≠ 0 := by rw [add_comm]; exact hwneg
  have hΓ1 : Complex.Gammaℝ (2 * w) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h2pos
  have hΓ2 : Complex.Gammaℝ (2 * w + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h21pos
  have hgf1 := gammaFactor_chi3D_ne_zero_of_re_pos h2pos
  have hgf2 := gammaFactor_chi3D_ne_zero_of_re_pos h21pos
  have hζ1 : riemannZeta (2 * w) * Complex.Gammaℝ (2 * w) = completedRiemannZeta (2 * w) := by
    rw [riemannZeta_def_of_ne_zero h2w0, div_mul_cancel₀ _ hΓ1]
  have hζ2 : riemannZeta (2 * w + 1) * Complex.Gammaℝ (2 * w + 1) =
      completedRiemannZeta (1 + 2 * w) := by
    rw [riemannZeta_def_of_ne_zero h21ne0, div_mul_cancel₀ _ hΓ2, add_comm]
  have hL1 : DirichletCharacter.LFunction chi3D (2 * w) *
      DirichletCharacter.gammaFactor chi3D (2 * w) =
      DirichletCharacter.completedLFunction chi3D (2 * w) :=
    (completedLFunction_chi3D_eq_mul h2w0 hgf1).symm
  have hL2 : DirichletCharacter.LFunction chi3D (2 * w + 1) *
      DirichletCharacter.gammaFactor chi3D (2 * w + 1) =
      DirichletCharacter.completedLFunction chi3D (1 + 2 * w) := by
    rw [add_comm (2 * w) 1]
    exact (completedLFunction_chi3D_eq_mul hwneg (by rwa [add_comm] at hgf2)).symm
  have hz2 : riemannZeta (2 * w + 1) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hLz2 : DirichletCharacter.LFunction chi3D (2 * w + 1) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one)
      (by simp; linarith)
  have h3ne : (3 : ℂ) ^ ((1 + 2 * w) / 2) ≠ 0 := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hc1 : completedRiemannZeta (1 + 2 * w) ≠ 0 := by
    rw [← hζ2]; exact mul_ne_zero hz2 hΓ2
  have hc2 : DirichletCharacter.completedLFunction chi3D (1 + 2 * w) ≠ 0 := by
    rw [← hL2]; exact mul_ne_zero hLz2 hgf2
  unfold bianchiArchimedeanFactor completedBianchiZeta
  rw [← hζ1, ← hζ2, ← hL1, ← hL2]
  field_simp

/-! ## 2. Complete Single- and Two-Boundary Singularity Dictionary -/

/-- Retarded boundary correlator `G_{R,K}(ν) = φ_K(-iν)` on the Bianchi horizon. -/
def bianchiRetardedCorrelator (ν : ℂ) : ℂ :=
  bianchiScatteringPhase (-I * ν)

/-- Advanced boundary correlator `G_{A,K}(ν) = φ_K(iν)` on the Bianchi horizon. -/
def bianchiAdvancedCorrelator (ν : ℂ) : ℂ :=
  bianchiScatteringPhase (I * ν)

/-- Trans-horizon thermofield Wightman correlator `G_{RL,K}(ν)` at inverse Hawking temperature
`β_H = 2π`. -/
def bianchiWightmanRL (ν : ℂ) : ℂ :=
  (bianchiRetardedCorrelator ν - bianchiAdvancedCorrelator ν) /
    (2 * I * Complex.sinh (Real.pi * ν))

theorem analyticAt_bianchiRetardedCorrelator {ν : ℂ}
    (hne : ν ≠ I / 2) (hxi : xiBianchi (1 - 2 * I * ν) ≠ 0) :
    AnalyticAt ℂ bianchiRetardedCorrelator ν := by
  set U : Set ℂ := {z : ℂ | z ≠ I / 2 ∧ xiBianchi (1 - 2 * I * z) ≠ 0}
  have hUo : IsOpen U :=
    isOpen_ne.inter (isOpen_ne.preimage (differentiable_xiBianchi.continuous.comp (by fun_prop)))
  have hdiff : DifferentiableOn ℂ bianchiRetardedCorrelator U := by
    intro z hz
    have h1 : -I * z ≠ 1 / 2 := fun h =>
      hz.1 (by linear_combination I * h + z * I_sq)
    have h2 : xiBianchi (1 + 2 * (-I * z)) ≠ 0 := by
      simpa [sub_eq_add_neg, mul_assoc] using hz.2
    exact ((differentiableAt_bianchiScatteringPhase h1 h2).comp z (by fun_prop)).differentiableWithinAt
  exact (hdiff.analyticOnNhd hUo) ν ⟨hne, hxi⟩

theorem analyticAt_bianchiAdvancedCorrelator {ν : ℂ}
    (hne : ν ≠ -(I / 2)) (hxi : xiBianchi (1 + 2 * I * ν) ≠ 0) :
    AnalyticAt ℂ bianchiAdvancedCorrelator ν := by
  set U : Set ℂ := {z : ℂ | z ≠ -(I / 2) ∧ xiBianchi (1 + 2 * I * z) ≠ 0}
  have hUo : IsOpen U :=
    isOpen_ne.inter (isOpen_ne.preimage (differentiable_xiBianchi.continuous.comp (by fun_prop)))
  have hdiff : DifferentiableOn ℂ bianchiAdvancedCorrelator U := by
    intro z hz
    have h1 : I * z ≠ 1 / 2 := fun h =>
      hz.1 (by linear_combination (-I) * h + z * I_sq)
    have h2 : xiBianchi (1 + 2 * (I * z)) ≠ 0 := by simpa [mul_assoc] using hz.2
    exact ((differentiableAt_bianchiScatteringPhase h1 h2).comp z (by fun_prop)).differentiableWithinAt
  exact (hdiff.analyticOnNhd hUo) ν ⟨hne, hxi⟩

/-- Every zero `ρ` of `xiBianchi` produces an isolated pole of `bianchiRetardedCorrelator` at
`ν_ρ = i(ρ - 1)/2` of exact multiplicity `-ord_ρ xiBianchi < 0`. -/
theorem bianchiRetardedCorrelator_order_at_zero {ρ : ℂ} (hρ : xiBianchi ρ = 0) :
    meromorphicOrderAt bianchiRetardedCorrelator (I * (ρ - 1) / 2) =
      -meromorphicOrderAt xiBianchi ρ := by
  have hcoord : -I * (I * (ρ - 1) / 2) = (ρ - 1) / 2 := by
    linear_combination (-(ρ - 1) / 2) * I_sq
  have hd : HasDerivAt (fun ν : ℂ => -I * ν) (-I) (I * (ρ - 1) / 2) := hasDerivAt_const_mul (-I)
  have hcomp : meromorphicOrderAt bianchiRetardedCorrelator (I * (ρ - 1) / 2) =
      meromorphicOrderAt bianchiScatteringPhase ((ρ - 1) / 2) := by
    rw [← hcoord]
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := bianchiScatteringPhase) (g := fun ν : ℂ => -I * ν) (by fun_prop)
      (by rw [hd.deriv]; exact neg_ne_zero.mpr I_ne_zero)
  rw [hcomp]
  exact scatteringPhase_meromorphicOrderAt_at_zero differentiable_xiBianchi
    (fun _ => xiBianchi_ne_zero_of_one_le_re) xiBianchi_one_sub hρ

/-- Bijective single-boundary singularity characterization for `SL₂(ℤ[ω])\ℍ³` (`ν ≠ i/2`). -/
theorem bianchiRetardedCorrelator_isPole_iff {ν : ℂ} (hν : ν ≠ I / 2) :
    meromorphicOrderAt bianchiRetardedCorrelator ν < 0 ↔
      (riemannZeta (1 - 2 * I * ν) * DirichletCharacter.LFunction chi3D (1 - 2 * I * ν) = 0 ∧
        0 < (1 - 2 * I * ν).re ∧ (1 - 2 * I * ν).re < 1) := by
  have hxi_iff : xiBianchi (1 - 2 * I * ν) = 0 ↔
      (riemannZeta (1 - 2 * I * ν) * DirichletCharacter.LFunction chi3D (1 - 2 * I * ν) = 0 ∧
        0 < (1 - 2 * I * ν).re ∧ (1 - 2 * I * ν).re < 1) := by
    constructor
    · intro hz
      obtain ⟨h0, h1⟩ := zero_mem_openStrip_of_xiBianchi_eq_zero hz
      have hne1 : 1 - 2 * I * ν ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl _ h1
      exact ⟨(xiBianchi_eq_zero_iff h0 hne1).mp hz, h0, h1⟩
    · rintro ⟨hz, h0, h1⟩
      have hne1 : 1 - 2 * I * ν ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl _ h1
      exact (xiBianchi_eq_zero_iff h0 hne1).mpr hz
  rw [← hxi_iff]
  constructor
  · intro hpole
    by_contra hnz
    have han := analyticAt_bianchiRetardedCorrelator hν hnz
    exact (not_lt_of_ge han.meromorphicOrderAt_nonneg) hpole
  · intro hz
    have hν_eq : ν = I * ((1 - 2 * I * ν) - 1) / 2 := by linear_combination ν * I_sq
    nth_rw 1 [hν_eq]
    rw [bianchiRetardedCorrelator_order_at_zero hz]
    exact (meromorphicOrderAt_pos_of_entire_zero differentiable_xiBianchi
      (fun _ => xiBianchi_ne_zero_of_one_le_re) hz).2.1

/-- Lower-strip (`-1/2 < Im ν < 0`) pole-order identity for `bianchiWightmanRL`. -/
theorem bianchiWightmanRL_order_lower {ν : ℂ}
    (hlo : -(1 / 2 : ℝ) < ν.im) (hhi : ν.im < 0) (hz : xiBianchi (1 - 2 * I * ν) = 0) :
    meromorphicOrderAt bianchiWightmanRL ν =
      -meromorphicOrderAt xiBianchi (1 - 2 * I * ν) := by
  have habs0 : 0 < |ν.im| := abs_pos.mpr hhi.ne
  have habs1 : |ν.im| < 1 := by rw [abs_of_neg hhi]; linarith
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ν) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one habs0 habs1)
  have hadv_ne : ν ≠ -(I / 2) := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hadv_xi : xiBianchi (1 + 2 * I * ν) ≠ 0 :=
    xiBianchi_ne_zero_of_one_le_re (by simp; linarith)
  have hadv_an : AnalyticAt ℂ (fun z => -bianchiAdvancedCorrelator z) ν :=
    (analyticAt_bianchiAdvancedCorrelator hadv_ne hadv_xi).neg
  have hν_eq : ν = I * ((1 - 2 * I * ν) - 1) / 2 := by linear_combination ν * I_sq
  have hret_ord : meromorphicOrderAt bianchiRetardedCorrelator ν =
      -meromorphicOrderAt xiBianchi (1 - 2 * I * ν) := by
    nth_rw 1 [hν_eq]
    exact bianchiRetardedCorrelator_order_at_zero hz
  have hret_neg : meromorphicOrderAt bianchiRetardedCorrelator ν < 0 := by
    rw [hret_ord]
    exact (meromorphicOrderAt_pos_of_entire_zero differentiable_xiBianchi
      (fun _ => xiBianchi_ne_zero_of_one_le_re) hz).2.1
  have hlt : meromorphicOrderAt bianchiRetardedCorrelator ν <
      meromorphicOrderAt (fun z => -bianchiAdvancedCorrelator z) ν :=
    lt_of_lt_of_le hret_neg hadv_an.meromorphicOrderAt_nonneg
  have hden_an : AnalyticAt ℂ (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) ν :=
    AnalyticAt.inv (by fun_prop) hsinh_ne
  have hW : bianchiWightmanRL =
      (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) *
        (bianchiRetardedCorrelator + (fun z => -bianchiAdvancedCorrelator z)) := by
    funext z; simp only [bianchiWightmanRL, Pi.mul_apply, Pi.add_apply]; ring
  rw [hW, meromorphicOrderAt_mul_of_ne_zero hden_an (inv_ne_zero hsinh_ne),
    meromorphicOrderAt_add_eq_left_of_lt hadv_an.meromorphicAt hlt, hret_ord]

/-- Upper-strip (`0 < Im ν < 1/2`) pole-order identity for `bianchiWightmanRL`. -/
theorem bianchiWightmanRL_order_upper {ν : ℂ}
    (hlo : 0 < ν.im) (hhi : ν.im < 1 / 2) (hz : xiBianchi (1 + 2 * I * ν) = 0) :
    meromorphicOrderAt bianchiWightmanRL ν =
      -meromorphicOrderAt xiBianchi (1 + 2 * I * ν) := by
  have habs0 : 0 < |ν.im| := abs_pos.mpr hlo.ne'
  have habs1 : |ν.im| < 1 := by rw [abs_of_pos hlo]; linarith
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ν) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one habs0 habs1)
  have hret_ne : ν ≠ I / 2 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hret_xi : xiBianchi (1 - 2 * I * ν) ≠ 0 :=
    xiBianchi_ne_zero_of_one_le_re (by simp; linarith)
  have hret_an : AnalyticAt ℂ bianchiRetardedCorrelator ν :=
    analyticAt_bianchiRetardedCorrelator hret_ne hret_xi
  have hneg_ord : meromorphicOrderAt (fun z => -bianchiAdvancedCorrelator z) ν =
      -meromorphicOrderAt xiBianchi (1 + 2 * I * ν) := by
    rw [show (fun z => -bianchiAdvancedCorrelator z) = -bianchiAdvancedCorrelator from rfl,
      ← meromorphicOrderAt_neg]
    have hadv_eq : bianchiAdvancedCorrelator = fun z => bianchiRetardedCorrelator (-z) := by
      funext z; simp [bianchiAdvancedCorrelator, bianchiRetardedCorrelator]
    rw [hadv_eq]
    have hd : HasDerivAt (fun z : ℂ => -z) (-1) ν := (hasDerivAt_id ν).neg
    have hcomp : meromorphicOrderAt (fun z => bianchiRetardedCorrelator (-z)) ν =
        meromorphicOrderAt bianchiRetardedCorrelator (-ν) :=
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := bianchiRetardedCorrelator)
        (g := fun z : ℂ => -z) (by fun_prop) (by rw [hd.deriv]; norm_num)
    rw [hcomp]
    have hν_eq : -ν = I * ((1 + 2 * I * ν) - 1) / 2 := by linear_combination (-ν) * I_sq
    nth_rw 1 [hν_eq]
    exact bianchiRetardedCorrelator_order_at_zero hz
  have hadv_neg : meromorphicOrderAt (fun z => -bianchiAdvancedCorrelator z) ν < 0 := by
    rw [hneg_ord]
    exact (meromorphicOrderAt_pos_of_entire_zero differentiable_xiBianchi
      (fun _ => xiBianchi_ne_zero_of_one_le_re) hz).2.1
  have hlt : meromorphicOrderAt (fun z => -bianchiAdvancedCorrelator z) ν <
      meromorphicOrderAt bianchiRetardedCorrelator ν :=
    lt_of_lt_of_le hadv_neg hret_an.meromorphicOrderAt_nonneg
  have hden_an : AnalyticAt ℂ (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) ν :=
    AnalyticAt.inv (by fun_prop) hsinh_ne
  have hW : bianchiWightmanRL =
      (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) *
        (bianchiRetardedCorrelator + (fun z => -bianchiAdvancedCorrelator z)) := by
    funext z; simp only [bianchiWightmanRL, Pi.mul_apply, Pi.add_apply]; ring
  rw [hW, meromorphicOrderAt_mul_of_ne_zero hden_an (inv_ne_zero hsinh_ne),
    meromorphicOrderAt_add_eq_right_of_lt hret_an.meromorphicAt hlt, hneg_ord]

/-- **Complete Two-Boundary Eternal Bianchi Dictionary.** On `0 < |Im ν| < 1/2` (disjoint from all
Hawking–Matsubara thermal poles `ν = ik`), `bianchiWightmanRL` has a pole at `ν` iff
`xiBianchi (1 - 2iν) = 0 ∨ xiBianchi (1 + 2iν) = 0`. -/
theorem bianchiWightmanRL_isPole_iff {ν : ℂ}
    (h0 : 0 < |ν.im|) (h1 : |ν.im| < 1 / 2) :
    meromorphicOrderAt bianchiWightmanRL ν < 0 ↔
      (xiBianchi (1 - 2 * I * ν) = 0 ∨ xiBianchi (1 + 2 * I * ν) = 0) := by
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ν) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one h0 (by linarith))
  have hne_pos : ν ≠ I / 2 := fun h => by
    have := congrArg Complex.im h; simp at this; rw [this] at h1; norm_num at h1
  have hne_neg : ν ≠ -(I / 2) := fun h => by
    have := congrArg Complex.im h; simp at this; rw [this] at h1; norm_num at h1
  constructor
  · intro hpole
    by_contra hnone
    push Not at hnone
    have han_ret := analyticAt_bianchiRetardedCorrelator hne_pos hnone.1
    have han_adv := analyticAt_bianchiAdvancedCorrelator hne_neg hnone.2
    have han_den : AnalyticAt ℂ (fun z => 2 * I * Complex.sinh (Real.pi * z)) ν := by fun_prop
    have han_W : AnalyticAt ℂ bianchiWightmanRL ν :=
      (han_ret.sub han_adv).div han_den hsinh_ne
    exact (not_lt_of_ge han_W.meromorphicOrderAt_nonneg) hpole
  · intro hzero
    rcases lt_trichotomy ν.im 0 with hneg | heq0 | hpos
    · have hadv_nz : xiBianchi (1 + 2 * I * ν) ≠ 0 :=
        xiBianchi_ne_zero_of_one_le_re (by simp; linarith)
      have hz := hzero.resolve_right hadv_nz
      have hlo : -(1 / 2 : ℝ) < ν.im := by rw [abs_of_neg hneg] at h1; linarith
      rw [bianchiWightmanRL_order_lower hlo hneg hz]
      exact (meromorphicOrderAt_pos_of_entire_zero differentiable_xiBianchi
        (fun _ => xiBianchi_ne_zero_of_one_le_re) hz).2.1
    · exfalso; rw [heq0, abs_zero] at h0; exact lt_irrefl _ h0
    · have hret_nz : xiBianchi (1 - 2 * I * ν) ≠ 0 :=
        xiBianchi_ne_zero_of_one_le_re (by simp; linarith)
      have hz := hzero.resolve_left hret_nz
      have hhi : ν.im < 1 / 2 := by rwa [abs_of_pos hpos] at h1
      rw [bianchiWightmanRL_order_upper hpos hhi hz]
      exact (meromorphicOrderAt_pos_of_entire_zero differentiable_xiBianchi
        (fun _ => xiBianchi_ne_zero_of_one_le_re) hz).2.1

/-! ## 3. Eternal Bianchi Strip Equivalences and Unconditional `1/16` Corollary -/

/-- `xiBianchi` is unconditionally nonvanishing on `Re s > 7/8`. -/
theorem xiBianchi_ne_zero_of_seven_eighths_lt_re {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    xiBianchi s ≠ 0 := by
  rcases lt_or_ge s.re 1 with hlt | hge
  · have hne1 : s ≠ 1 := fun h => by rw [h, one_re] at hlt; exact lt_irrefl _ hlt
    rw [Ne, xiBianchi_eq_zero_iff (by linarith) hne1]
    exact mul_ne_zero (riemannZeta_ne_zero_of_seven_eighths_lt_re hs)
      (GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
        chi3D hs (fun h => chi3D_ne_one h.1))
  · exact xiBianchi_ne_zero_of_one_le_re hge

/-- Every zero of `xiBianchi` lies unconditionally in `1/8 ≤ Re s ≤ 7/8`. -/
theorem xiBianchi_re_mem_Icc_of_eq_zero {s : ℂ} (hz : xiBianchi s = 0) :
    s.re ∈ Icc (1 / 8 : ℝ) (7 / 8 : ℝ) := by
  refine ⟨le_of_not_gt fun hlt => ?_, le_of_not_gt fun hgt =>
    xiBianchi_ne_zero_of_seven_eighths_lt_re hgt hz⟩
  have h1 : (7 / 8 : ℝ) < (1 - s).re := by simp; linarith
  exact xiBianchi_ne_zero_of_seven_eighths_lt_re h1 (by rw [xiBianchi_one_sub]; exact hz)

/-- For `0 < δ ≤ 1/4`, `bianchiWightmanRL` is analytic on `{0 < |Im ν| < δ}` iff `xiBianchi` has no
zeros outside `[2δ, 1 - 2δ]`. -/
theorem bianchiWightmanRL_analyticOnNhd_strip_iff {δ : ℝ} (_h0 : 0 < δ) (h1 : δ ≤ 1 / 4) :
    AnalyticOnNhd ℂ bianchiWightmanRL {ν : ℂ | 0 < |ν.im| ∧ |ν.im| < δ} ↔
      ∀ ρ : ℂ, xiBianchi ρ = 0 → 2 * δ ≤ ρ.re ∧ ρ.re ≤ 1 - 2 * δ := by
  constructor
  · intro han ρ hρ
    obtain ⟨hr0, hr1⟩ := zero_mem_openStrip_of_xiBianchi_eq_zero hρ
    have hupper : ρ.re ≤ 1 - 2 * δ := by
      by_contra hgt
      push Not at hgt
      set ν : ℂ := I * (ρ - 1) / 2 with hν
      have him : ν.im = (ρ.re - 1) / 2 := by rw [hν]; simp
      have hmem : ν ∈ {z : ℂ | 0 < |z.im| ∧ |z.im| < δ} := by
        have hneg : ν.im < 0 := by rw [him]; linarith
        refine ⟨abs_pos.mpr hneg.ne, ?_⟩
        rw [abs_of_neg hneg, him]; linarith
      have hpole : meromorphicOrderAt bianchiWightmanRL ν < 0 := by
        rw [bianchiWightmanRL_isPole_iff hmem.1 (lt_of_lt_of_le hmem.2 (by linarith))]
        left
        have heq : 1 - 2 * I * ν = ρ := by rw [hν]; linear_combination (1 - ρ) * I_sq
        rwa [heq]
      exact (not_lt_of_ge (han ν hmem).meromorphicOrderAt_nonneg) hpole
    have hlower : 2 * δ ≤ ρ.re := by
      have hsym : xiBianchi (1 - ρ) = 0 := by rwa [xiBianchi_one_sub]
      by_contra hlt
      push Not at hlt
      set ν : ℂ := I * ((1 - ρ) - 1) / 2 with hν
      have him : ν.im = -ρ.re / 2 := by rw [hν]; simp
      have hmem : ν ∈ {z : ℂ | 0 < |z.im| ∧ |z.im| < δ} := by
        have hneg : ν.im < 0 := by rw [him]; linarith
        refine ⟨abs_pos.mpr hneg.ne, ?_⟩
        rw [abs_of_neg hneg, him]; linarith
      have hpole : meromorphicOrderAt bianchiWightmanRL ν < 0 := by
        rw [bianchiWightmanRL_isPole_iff hmem.1 (lt_of_lt_of_le hmem.2 (by linarith))]
        left
        have heq : 1 - 2 * I * ν = 1 - ρ := by rw [hν]; linear_combination ρ * I_sq
        rwa [heq]
      exact (not_lt_of_ge (han ν hmem).meromorphicOrderAt_nonneg) hpole
    exact ⟨hlower, hupper⟩
  · intro hstrip ν hν
    have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ν) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
        (sinh_pi_mul_ne_zero_of_abs_im_lt_one hν.1 (by linarith [hν.2]))
    have hne_pos : ν ≠ I / 2 := fun h => by
      have him := congrArg Complex.im h; simp at him
      have h2 : |ν.im| < δ := hν.2
      rw [him] at h2; norm_num at h2; linarith
    have hne_neg : ν ≠ -(I / 2) := fun h => by
      have him := congrArg Complex.im h; simp at him
      have h2 : |ν.im| < δ := hν.2
      rw [him] at h2; norm_num at h2; linarith
    have hnz1 : xiBianchi (1 - 2 * I * ν) ≠ 0 := fun hz => by
      have hbd := (hstrip _ hz).2
      have hre : (1 - 2 * I * ν).re = 1 + 2 * ν.im := by simp
      have habs := abs_lt.mp hν.2
      linarith
    have hnz2 : xiBianchi (1 + 2 * I * ν) ≠ 0 := fun hz => by
      have hbd := (hstrip _ hz).2
      have hre : (1 + 2 * I * ν).re = 1 - 2 * ν.im := by simp; ring
      have habs := abs_lt.mp hν.2
      linarith
    exact ((analyticAt_bianchiRetardedCorrelator hne_pos hnz1).sub
      (analyticAt_bianchiAdvancedCorrelator hne_neg hnz2)).div (by fun_prop) hsinh_ne

/-- Analyticity of `bianchiWightmanRL` on the punctured quarter-strip `0 < |Im ν| < 1/4` is
equivalent to GRH for `ζ_K(s) = ζ(s) L(s, χ₋₃)`. -/
theorem dedekind_rh_iff_bianchiWightmanRL_quarter_strip :
    AnalyticOnNhd ℂ bianchiWightmanRL {ν : ℂ | 0 < |ν.im| ∧ |ν.im| < 1 / 4} ↔
      ∀ ρ : ℂ, xiBianchi ρ = 0 → ρ.re = 1 / 2 := by
  rw [bianchiWightmanRL_analyticOnNhd_strip_iff (by norm_num) le_rfl]
  constructor
  · intro h ρ hρ
    have hb := h ρ hρ
    linarith
  · intro h ρ hρ
    have heq := h ρ hρ
    exact ⟨by linarith, by linarith⟩

/-- Quarter-strip analyticity of `bianchiWightmanRL` implies `RiemannHypothesis`. -/
theorem bianchiWightmanRL_quarter_strip_implies_riemannHypothesis
    (han : AnalyticOnNhd ℂ bianchiWightmanRL {ν : ℂ | 0 < |ν.im| ∧ |ν.im| < 1 / 4}) :
    RiemannHypothesis := by
  have hgrh := dedekind_rh_iff_bianchiWightmanRL_quarter_strip.mp han
  rw [RingdownRate.riemannHypothesis_iff_pulse_ringdown,
    ← RingdownRate.zeroFreeStrip_iff_pulse_ringdown (by norm_num) le_rfl]
  intro ρ hζ hρ0
  have hρ1 : ρ.re < 1 := lt_of_not_ge fun h1 => riemannZeta_ne_zero_of_one_le_re h1 hζ
  have hne1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
  have hb0 : xiBianchi ρ = 0 :=
    (xiBianchi_eq_zero_iff hρ0 hne1).mpr (mul_eq_zero_of_left hζ _)
  linarith [hgrh ρ hb0]

/-- **Unconditional Eternal Bianchi Analytic Strip.** `bianchiWightmanRL` is unconditionally
analytic on `{ν ∈ ℂ | 0 < |Im ν| < 1/16}`. -/
theorem bianchiWightmanRL_analyticOnNhd_one_sixteenth :
    AnalyticOnNhd ℂ bianchiWightmanRL {ν : ℂ | 0 < |ν.im| ∧ |ν.im| < 1 / 16} := by
  rw [bianchiWightmanRL_analyticOnNhd_strip_iff (by norm_num) (by norm_num)]
  intro ρ hρ
  have hmem := xiBianchi_re_mem_Icc_of_eq_zero hρ
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-! ## 4. Bianchi Prime-`2` Causal Deformation and Universal Decay Collapse to `0` -/

/-- Entire deformed Bianchi `ξ`-function `ξ_{K,α}(s) = primeTwoFactor α s * xiBianchi s`. -/
def xiBianchiDeformed (α : ℝ) (s : ℂ) : ℂ :=
  primeTwoFactor α s * xiBianchi s

theorem differentiable_xiBianchiDeformed (α : ℝ) : Differentiable ℂ (xiBianchiDeformed α) :=
  (differentiable_primeTwoFactor α).mul differentiable_xiBianchi

theorem xiBianchiDeformed_one_sub (α : ℝ) (s : ℂ) :
    xiBianchiDeformed α (1 - s) = xiBianchiDeformed α s := by
  rw [xiBianchiDeformed, primeTwoFactor_one_sub, xiBianchi_one_sub, xiBianchiDeformed]

theorem xiBianchiDeformed_conj (α : ℝ) (s : ℂ) :
    xiBianchiDeformed α (starRingEnd ℂ s) = starRingEnd ℂ (xiBianchiDeformed α s) := by
  rw [xiBianchiDeformed, xiBianchiDeformed, map_mul, primeTwoFactor_conj, xiBianchi_conj]

theorem xiBianchiDeformed_ne_zero_of_one_le_re {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {s : ℂ} (hs : 1 ≤ s.re) : xiBianchiDeformed α s ≠ 0 :=
  mul_ne_zero (primeTwoFactor_ne_zero_of_gt h0 (by linarith) (by linarith))
    (xiBianchi_ne_zero_of_one_le_re hs)

/-- Deformed Bianchi scattering phase `φ_{K,α}(w) = ((1 + 2w)/(2w - 1)) · (ξ_{K,α}(2w)/ξ_{K,α}(1 + 2w))`. -/
def bianchiDeformedScatteringPhase (α : ℝ) (w : ℂ) : ℂ :=
  ((1 + 2 * w) / (2 * w - 1)) * (xiBianchiDeformed α (2 * w) / xiBianchiDeformed α (1 + 2 * w))

theorem bianchiDeformedScatteringPhase_eq_mul (α : ℝ) (w : ℂ) :
    bianchiDeformedScatteringPhase α w =
      primeTwoScatteringGate α w * bianchiScatteringPhase w := by
  rw [bianchiDeformedScatteringPhase, xiBianchiDeformed, xiBianchiDeformed, mul_div_mul_comm,
    primeTwoFactor_div_eq_primeTwoScatteringGate, bianchiScatteringPhase]
  ring

/-- Continuous-spectrum unitarity `‖φ_{K,α}(it)‖ = 1` for all `t ∈ ℝ` (`0 < α < 1`). -/
theorem norm_bianchiDeformedScatteringPhase_axis {α : ℝ} (h0 : 0 < α) (h1 : α < 1) (t : ℝ) :
    ‖bianchiDeformedScatteringPhase α ((t : ℂ) * I)‖ = 1 := by
  rw [bianchiDeformedScatteringPhase_eq_mul, norm_mul, norm_primeTwoScatteringGate_axis h0 h1 t,
    norm_bianchiScatteringPhase_axis t, one_mul]

/-- Deformed Bianchi prime-marked Euler gates over `Nat.Primes`. -/
def bianchiDeformedPrimeGate (α : ℝ) (p : Nat.Primes) (w : ℂ) : ℂ :=
  if (p : ℕ) = 2 then primeTwoScatteringGate α w * bianchiPrimeGate p w else bianchiPrimeGate p w

/-- Convergent Euler product of `bianchiDeformedPrimeGate α p w` over `Nat.Primes` on `Re w > 1/2`. -/
theorem hasProd_bianchiDeformedPrimeGate {α : ℝ} {w : ℂ} (hw : 1 / 2 < w.re) :
    HasProd (fun p : Nat.Primes => bianchiDeformedPrimeGate α p w)
      (primeTwoScatteringGate α w *
        ((riemannZeta (2 * w) * DirichletCharacter.LFunction chi3D (2 * w)) /
          (riemannZeta (2 * w + 1) * DirichletCharacter.LFunction chi3D (2 * w + 1)))) := by
  let p2 : Nat.Primes := ⟨2, Nat.prime_two⟩
  let m : Nat.Primes → ℂ := fun p => if p = p2 then primeTwoScatteringGate α w else 1
  have hm : HasProd m (primeTwoScatteringGate α w) := by
    simpa [m] using hasProd_ite_eq p2 (primeTwoScatteringGate α w)
  have hgate : (fun p : Nat.Primes => bianchiDeformedPrimeGate α p w) =
      fun p => m p * bianchiPrimeGate p w := by
    funext p
    unfold bianchiDeformedPrimeGate
    by_cases hp : p = p2
    · subst hp; simp [m, p2]
    · have hp2 : (p : ℕ) ≠ 2 := fun h => hp (Subtype.ext h)
      simp [m, hp, hp2]
  rw [hgate]
  exact hm.mul (hasProd_bianchiPrimeGate hw)

/-- Deformed Bianchi retarded, advanced, and two-boundary Wightman correlators. -/
def bianchiDeformedRetardedCorrelator (α : ℝ) (ν : ℂ) : ℂ :=
  bianchiDeformedScatteringPhase α (-I * ν)

def bianchiDeformedAdvancedCorrelator (α : ℝ) (ν : ℂ) : ℂ :=
  bianchiDeformedScatteringPhase α (I * ν)

def bianchiDeformedWightmanRL (α : ℝ) (ν : ℂ) : ℂ :=
  (bianchiDeformedRetardedCorrelator α ν - bianchiDeformedAdvancedCorrelator α ν) /
    (2 * I * Complex.sinh (Real.pi * ν))

theorem bianchiDeformedRetardedCorrelator_order_at_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {ρ : ℂ} (hρ : xiBianchiDeformed α ρ = 0) :
    meromorphicOrderAt (bianchiDeformedRetardedCorrelator α) (I * (ρ - 1) / 2) =
      -meromorphicOrderAt (xiBianchiDeformed α) ρ := by
  have hcoord : -I * (I * (ρ - 1) / 2) = (ρ - 1) / 2 := by
    linear_combination (-(ρ - 1) / 2) * I_sq
  have hd : HasDerivAt (fun ν : ℂ => -I * ν) (-I) (I * (ρ - 1) / 2) := hasDerivAt_const_mul (-I)
  have hcomp : meromorphicOrderAt (bianchiDeformedRetardedCorrelator α) (I * (ρ - 1) / 2) =
      meromorphicOrderAt (bianchiDeformedScatteringPhase α) ((ρ - 1) / 2) := by
    rw [← hcoord]
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := bianchiDeformedScatteringPhase α) (g := fun ν : ℂ => -I * ν) (by fun_prop)
      (by rw [hd.deriv]; exact neg_ne_zero.mpr I_ne_zero)
  rw [hcomp]
  exact scatteringPhase_meromorphicOrderAt_at_zero (differentiable_xiBianchiDeformed α)
    (fun _ => xiBianchiDeformed_ne_zero_of_one_le_re h0 h1) (xiBianchiDeformed_one_sub α) hρ

theorem differentiableAt_bianchiDeformedScatteringPhase {α : ℝ}
    {w : ℂ} (hne : w ≠ 1 / 2) (hxi : xiBianchiDeformed α (1 + 2 * w) ≠ 0) :
    DifferentiableAt ℂ (bianchiDeformedScatteringPhase α) w := by
  have hd : 2 * w - 1 ≠ 0 := fun h0 => hne (by linear_combination h0 / 2)
  exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) w).div (by fun_prop) hd).mul
    ((((differentiable_xiBianchiDeformed α) _).comp w (by fun_prop)).div
      (((differentiable_xiBianchiDeformed α) _).comp w (by fun_prop)) hxi)

theorem analyticAt_bianchiDeformedAdvancedCorrelator {α : ℝ} {ν : ℂ}
    (hne : ν ≠ -(I / 2)) (hxi : xiBianchiDeformed α (1 + 2 * I * ν) ≠ 0) :
    AnalyticAt ℂ (bianchiDeformedAdvancedCorrelator α) ν := by
  set U : Set ℂ := {z : ℂ | z ≠ -(I / 2) ∧ xiBianchiDeformed α (1 + 2 * I * z) ≠ 0}
  have hUo : IsOpen U :=
    isOpen_ne.inter
      (isOpen_ne.preimage ((differentiable_xiBianchiDeformed α).continuous.comp (by fun_prop)))
  have hdiff : DifferentiableOn ℂ (bianchiDeformedAdvancedCorrelator α) U := by
    intro z hz
    have h1 : I * z ≠ 1 / 2 := fun h => hz.1 (by linear_combination (-I) * h + z * I_sq)
    have h2 : xiBianchiDeformed α (1 + 2 * (I * z)) ≠ 0 := by simpa [mul_assoc] using hz.2
    exact ((differentiableAt_bianchiDeformedScatteringPhase h1 h2).comp z
      (by fun_prop)).differentiableWithinAt
  exact (hdiff.analyticOnNhd hUo) ν ⟨hne, hxi⟩

theorem bianchiDeformedWightmanRL_order_lower {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {ν : ℂ}
    (hlo : -(1 / 2 : ℝ) < ν.im) (hhi : ν.im < 0) (hz : xiBianchiDeformed α (1 - 2 * I * ν) = 0) :
    meromorphicOrderAt (bianchiDeformedWightmanRL α) ν =
      -meromorphicOrderAt (xiBianchiDeformed α) (1 - 2 * I * ν) := by
  have habs0 : 0 < |ν.im| := abs_pos.mpr hhi.ne
  have habs1 : |ν.im| < 1 := by rw [abs_of_neg hhi]; linarith
  have hsinh_ne : 2 * I * Complex.sinh (Real.pi * ν) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (sinh_pi_mul_ne_zero_of_abs_im_lt_one habs0 habs1)
  have hadv_ne : ν ≠ -(I / 2) := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hadv_xi : xiBianchiDeformed α (1 + 2 * I * ν) ≠ 0 :=
    xiBianchiDeformed_ne_zero_of_one_le_re h0 h1 (by simp; linarith)
  have hadv_an : AnalyticAt ℂ (fun z => -bianchiDeformedAdvancedCorrelator α z) ν :=
    (analyticAt_bianchiDeformedAdvancedCorrelator hadv_ne hadv_xi).neg
  have hν_eq : ν = I * ((1 - 2 * I * ν) - 1) / 2 := by linear_combination ν * I_sq
  have hret_ord : meromorphicOrderAt (bianchiDeformedRetardedCorrelator α) ν =
      -meromorphicOrderAt (xiBianchiDeformed α) (1 - 2 * I * ν) := by
    nth_rw 1 [hν_eq]
    exact bianchiDeformedRetardedCorrelator_order_at_zero h0 h1 hz
  obtain ⟨_, hneg, _⟩ := meromorphicOrderAt_pos_of_entire_zero (differentiable_xiBianchiDeformed α)
    (fun _ => xiBianchiDeformed_ne_zero_of_one_le_re h0 h1) hz
  have hlt : meromorphicOrderAt (bianchiDeformedRetardedCorrelator α) ν <
      meromorphicOrderAt (fun z => -bianchiDeformedAdvancedCorrelator α z) ν :=
    lt_of_lt_of_le (by rw [hret_ord]; exact hneg) hadv_an.meromorphicOrderAt_nonneg
  have hden_an : AnalyticAt ℂ (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) ν :=
    AnalyticAt.inv (by fun_prop) hsinh_ne
  have hW : bianchiDeformedWightmanRL α =
      (fun z => (2 * I * Complex.sinh (Real.pi * z))⁻¹) *
        (bianchiDeformedRetardedCorrelator α +
          (fun z => -bianchiDeformedAdvancedCorrelator α z)) := by
    funext z; simp only [bianchiDeformedWightmanRL, Pi.mul_apply, Pi.add_apply]; ring
  rw [hW, meromorphicOrderAt_mul_of_ne_zero hden_an (inv_ne_zero hsinh_ne),
    meromorphicOrderAt_add_eq_left_of_lt hadv_an.meromorphicAt hlt, hret_ord]

/-- Reflected wavepacket on the prime-`2` deformed Bianchi horizon. -/
def bianchiDeformedReflectedField (α : ℝ) (h : CompactPulse) (τ : ℝ) : ℂ :=
  ∫ t : ℝ, pulseAmplitude h (t : ℂ) * bianchiDeformedScatteringPhase α ((t : ℂ) * I) *
    Complex.exp (I * (t : ℂ) * (τ : ℂ))

def bianchiDeformedLineField (α : ℝ) (h : CompactPulse) (c τ : ℝ) : ℂ :=
  ∫ t : ℝ, pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    bianchiDeformedScatteringPhase α ((c : ℂ) + (t : ℂ) * I) *
    Complex.exp (((c : ℂ) + (t : ℂ) * I) * (τ : ℂ))

theorem bianchiDeformedLineField_zero (α : ℝ) (h : CompactPulse) (τ : ℝ) :
    bianchiDeformedLineField α h 0 τ = bianchiDeformedReflectedField α h τ := by
  unfold bianchiDeformedLineField bianchiDeformedReflectedField
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  have e : ((0 : ℝ) : ℂ) + (t : ℂ) * I = (t : ℂ) * I := by simp
  rw [e, show -I * ((t : ℂ) * I) = (t : ℂ) by linear_combination (-(t : ℂ)) * I_sq]
  congr 2; ring

theorem continuous_bianchiDeformedReflectedField_and_bounded {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) :
    Continuous (bianchiDeformedReflectedField α h) ∧
      ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ τ : ℝ, ‖bianchiDeformedReflectedField α h τ‖ ≤ M₀ := by
  have hint_a : Integrable fun t : ℝ => ‖pulseAmplitude h (t : ℂ)‖ := by
    have h_line := (h.integrable_amplitude_line 0).norm
    exact h_line.congr (Eventually.of_forall fun t => by simp)
  have hpt : ∀ τ t : ℝ,
      ‖pulseAmplitude h (t : ℂ) * bianchiDeformedScatteringPhase α ((t : ℂ) * I) *
        Complex.exp (I * (t : ℂ) * (τ : ℂ))‖ = ‖pulseAmplitude h (t : ℂ)‖ := by
    intro τ t
    rw [norm_mul, norm_mul, norm_bianchiDeformedScatteringPhase_axis h0 h1 t, mul_one,
      Complex.norm_exp]
    have hre : (I * (t : ℂ) * (τ : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one]
  have hcont : Continuous (bianchiDeformedReflectedField α h) := by
    unfold bianchiDeformedReflectedField
    refine continuous_of_dominated (bound := fun t : ℝ => ‖pulseAmplitude h (t : ℂ)‖) ?_ ?_ hint_a ?_
    · intro τ
      refine (((h.differentiable_amplitude.continuous.comp Complex.continuous_ofReal).mul ?_).mul
        (by fun_prop)).aestronglyMeasurable
      refine continuous_iff_continuousAt.mpr fun t => ?_
      have hne : ((t : ℂ) * I) ≠ 1 / 2 := fun he => by
        have := congrArg Complex.re he; simp at this
      have hxi : xiBianchiDeformed α (1 + 2 * ((t : ℂ) * I)) ≠ 0 :=
        xiBianchiDeformed_ne_zero_of_one_le_re h0 h1 (by simp)
      exact ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) * I)
        (differentiableAt_bianchiDeformedScatteringPhase hne hxi).continuousAt (by fun_prop)
    · exact fun τ => ae_of_all _ fun t => (hpt τ t).le
    · exact ae_of_all _ fun t => by fun_prop
  refine ⟨hcont, ∫ t : ℝ, ‖pulseAmplitude h (t : ℂ)‖,
    integral_nonneg fun _ => norm_nonneg _, fun τ => ?_⟩
  exact norm_integral_le_of_norm_le hint_a (Eventually.of_forall fun t => (hpt τ t).le)

private theorem exists_amplitude_bianchiDeformed_right_le {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℂ, 0 ≤ u.re → u.re ≤ 3 / 8 →
      ‖pulseAmplitude h (-I * u) * bianchiDeformedScatteringPhase α u‖ ≤ B / (1 + u.im ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchi_right_le h
  refine ⟨B, hB0, fun u hu1 hu2 => ?_⟩
  rw [bianchiDeformedScatteringPhase_eq_mul, ← mul_left_comm, norm_mul]
  calc ‖primeTwoScatteringGate α u‖ * ‖pulseAmplitude h (-I * u) * bianchiScatteringPhase u‖
      ≤ 1 * (B / (1 + u.im ^ 2)) := mul_le_mul (norm_primeTwoScatteringGate_le_one h0 h1 hu1)
          (hB u hu1 hu2) (norm_nonneg _) (by positivity)
    _ = B / (1 + u.im ^ 2) := one_mul _

private theorem bianchiDeformedReflectedField_eq_lineField {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 3 / 8) (τ : ℝ) :
    bianchiDeformedReflectedField α h τ = bianchiDeformedLineField α h c τ := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchiDeformed_right_le h0 h1 h
  set Φ : ℂ → ℂ := fun u => pulseAmplitude h (-I * u) * bianchiDeformedScatteringPhase α u *
    Complex.exp (u * (τ : ℂ)) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c → 0 ≤ s.re ∧ s.re ≤ 3 / 8 := by
    intro s hs; rw [uIcc_of_le hc0] at hs; exact ⟨hs.1, hs.2.trans hc1⟩
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) c → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
    have hxi : xiBianchiDeformed α (1 + 2 * s) ≠ 0 :=
      xiBianchiDeformed_ne_zero_of_one_le_re h0 h1 (by simp; linarith)
    exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
      (differentiableAt_bianchiDeformedScatteringPhase hne hxi)).mul (by fun_prop))
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
    simp only [hΦ]; rw [norm_mul]
    calc ‖pulseAmplitude h (-I * s) * bianchiDeformedScatteringPhase α s‖ *
          ‖Complex.exp (s * (τ : ℂ))‖
        ≤ (B / (1 + s.im ^ 2)) * Real.exp ((3 / 8) * |τ|) :=
          mul_le_mul (hB s hs1 hs2) hexp (norm_nonneg _) (by positivity)
      _ = (B * Real.exp ((3 / 8) * |τ|)) / (1 + s.im ^ 2) := by ring
  rw [← bianchiDeformedLineField_zero]
  exact integral_vertical_line_shift_of_decay hd hbΦ

private theorem exists_bianchiDeformedReflectedField_early_decay {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, τ ≤ 0 →
      ‖bianchiDeformedReflectedField α h τ‖ ≤ C * Real.exp ((3 / 8) * τ) := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchiDeformed_right_le h0 h1 h
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  rw [bianchiDeformedReflectedField_eq_lineField h0 h1 h (c := 3 / 8) (by norm_num) le_rfl τ]
  unfold bianchiDeformedLineField
  have hpt : ∀ t : ℝ,
      ‖pulseAmplitude h (-I * (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I)) *
        bianchiDeformedScatteringPhase α (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
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
          bianchiDeformedScatteringPhase α (((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) *
          Complex.exp ((((3 / 8 : ℝ) : ℂ) + (t : ℂ) * I) * (τ : ℂ))‖
      ≤ ∫ t : ℝ, B * (1 + t ^ 2)⁻¹ * Real.exp ((3 / 8) * τ) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = B * Real.pi * Real.exp ((3 / 8) * τ) := by
        rw [integral_mul_const, integral_const_mul, integral_univ_inv_one_add_sq]

/-- Bilateral Laplace identity on `1/8 < Re w < 5/16` for `bianchiDeformedReflectedField α h`. -/
theorem bianchiDeformed_bilateral_laplace_eq {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    (h : CompactPulse) {w : ℂ} (hw1 : 1 / 8 < w.re) (hw2 : w.re < 5 / 16) :
    (∫ τ in Ioi (0 : ℝ), Complex.exp (-w * (τ : ℂ)) * bianchiDeformedReflectedField α h τ) +
      (∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * bianchiDeformedReflectedField α h (-σ)) =
      2 * Real.pi * pulseAmplitude h (-I * w) * bianchiDeformedScatteringPhase α w := by
  set c : ℝ := w.re
  set η : ℝ := w.im
  have hc0 : 0 ≤ c := by linarith
  have hc1 : c ≤ 3 / 8 := by linarith
  have hw_eq : w = (c : ℂ) + (η : ℂ) * I := by apply Complex.ext <;> simp [c, η]
  obtain ⟨hGc, M₀, hM₀, hGb⟩ := continuous_bianchiDeformedReflectedField_and_bounded h0 h1 h
  obtain ⟨Ce, hCe, hGe⟩ := exists_bianchiDeformedReflectedField_early_decay h0 h1 h
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bianchiDeformed_right_le h0 h1 h
  set f : ℝ → ℂ := fun t => pulseAmplitude h (-I * ((c : ℂ) + (t : ℂ) * I)) *
    bianchiDeformedScatteringPhase α ((c : ℂ) + (t : ℂ) * I) with hf_def
  have hf_cont : Continuous f := by
    refine (h.differentiable_amplitude.continuous.comp (by fun_prop)).mul ?_
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : ((c : ℂ) + (t : ℂ) * I) ≠ 1 / 2 := fun he => by
      have := congrArg Complex.re he; simp at this; linarith
    have hxi : xiBianchiDeformed α (1 + 2 * ((c : ℂ) + (t : ℂ) * I)) ≠ 0 :=
      xiBianchiDeformed_ne_zero_of_one_le_re h0 h1 (by simp; linarith)
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
      (differentiableAt_bianchiDeformedScatteringPhase hne hxi).continuousAt (by fun_prop)
  have hf_int : Integrable f := by
    refine (integrable_inv_one_add_sq.const_mul B).mono' hf_cont.aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    have hb := hB ((c : ℂ) + (t : ℂ) * I) (by simp; exact hc0) (by simp; exact hc1)
    simpa [hf_def, div_eq_mul_inv] using hb
  set g : ℝ → ℂ := fun τ => Complex.exp (-(c : ℂ) * (τ : ℂ)) * bianchiDeformedReflectedField α h τ
    with hg_def
  have hg_cont : Continuous g := (by fun_prop : Continuous fun τ : ℝ =>
    Complex.exp (-(c : ℂ) * (τ : ℂ))).mul hGc
  have hg_pos : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hdom : IntegrableOn (fun τ : ℝ => M₀ * Real.exp (-c * τ)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M₀
    refine hdom.mono' hg_cont.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ _ => ?_))
    simp only [hg_def]
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(c : ℂ) * (τ : ℂ)).re = -c * τ := by simp
    rw [hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hGb τ) (Real.exp_pos _).le
  have hg_neg : IntegrableOn g (Iic (0 : ℝ)) := by
    have hdom_i : IntegrableOn (fun σ : ℝ => Ce * Real.exp (-(3 / 8 - c) * σ)) (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul Ce
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
    calc Real.exp (-c * τ) * ‖bianchiDeformedReflectedField α h τ‖
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
    rw [bianchiDeformedReflectedField_eq_lineField h0 h1 h hc0 hc1 τ]
    unfold bianchiDeformedLineField
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
      2 * Real.pi * pulseAmplitude h (-I * w) * bianchiDeformedScatteringPhase α w := by
    simp only [hF_def, hf_def]
    rw [mul_div_cancel₀ _ hpi0, ← hw_eq]; ring
  set H : ℝ → ℂ := fun τ => Complex.exp (-w * (τ : ℂ)) * bianchiDeformedReflectedField α h τ
    with hH_def
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
      ∫ σ in Ioi (0 : ℝ), Complex.exp (w * (σ : ℂ)) * bianchiDeformedReflectedField α h (-σ) := by
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
    _ = 2 * Real.pi * pulseAmplitude h (-I * w) * bianchiDeformedScatteringPhase α w := hF_eval

/-- **Unconditional Sub-Threshold Bianchi Ringdown.** For `1/2 < α < 1`, every `h : CompactPulse`,
and every `0 < σ < min(1/16, (1 - α)/2)`, `bianchiDeformedReflectedField α h τ = O(e^{-σ τ})` on
`τ ≥ 0`. -/
theorem bianchiDeformedReflectedField_decay {α σ : ℝ}
    (h0 : 1 / 2 < α) (h1 : α < 1) (hσ0 : 0 < σ)
    (hσ16 : σ < 1 / 16) (hσα : σ < (1 - α) / 2) (h : CompactPulse) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      ‖bianchiDeformedReflectedField α h τ‖ ≤ C * Real.exp (-σ * τ) := by
  have hzf : ∀ ρ : ℂ, riemannZeta ρ * DirichletCharacter.LFunction chi3D ρ = 0 →
      0 < ρ.re → ρ.re ≤ 1 - 2 * (1 / 16 : ℝ) := by
    intro ρ hρ hρ0
    have hlt1 : ρ.re < 1 := by
      by_contra hge
      push Not at hge
      exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hge)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi3D (Or.inl chi3D_ne_one) hge) hρ
    have hne1 : ρ ≠ 1 := fun he => by rw [he, one_re] at hlt1; exact lt_irrefl _ hlt1
    have hxi0 : xiBianchi ρ = 0 := (xiBianchi_eq_zero_iff hρ0 hne1).mpr hρ
    linarith [(xiBianchi_re_mem_Icc_of_eq_zero hxi0).2]
  obtain ⟨B₀, hB₀, hB_base⟩ := exists_amplitude_bianchi_left_le (δ := 1 / 16) (σ := σ)
    (by norm_num) hσ0 hσ16 hzf h
  obtain ⟨KG, hKG, hG⟩ := exists_primeTwoScatteringGate_left_le h0 h1 hσ0 hσα
  set B : ℝ := KG * B₀
  have hB_left : ∀ u : ℂ, -σ ≤ u.re → u.re ≤ 0 →
      ‖pulseAmplitude h (-I * u) * bianchiDeformedScatteringPhase α u‖ ≤ B / (1 + u.im ^ 2) := by
    intro u hu1 hu2
    rw [bianchiDeformedScatteringPhase_eq_mul, ← mul_left_comm, norm_mul]
    calc ‖primeTwoScatteringGate α u‖ * ‖pulseAmplitude h (-I * u) * bianchiScatteringPhase u‖
        ≤ KG * (B₀ / (1 + u.im ^ 2)) := mul_le_mul (hG u hu1 hu2) (hB_base u hu1 hu2)
            (norm_nonneg _) (by positivity)
      _ = B / (1 + u.im ^ 2) := by simp only [B]; ring
  have hxi_left : ∀ u : ℂ, -σ ≤ u.re → xiBianchiDeformed α (1 + 2 * u) ≠ 0 := by
    intro u hu1
    exact mul_ne_zero
      (primeTwoFactor_ne_zero_of_gt (by linarith) (by simp; linarith) (by simp; linarith))
      (xiBianchi_ne_zero_of_seven_eighths_lt_re (by simp; linarith))
  refine ⟨B * Real.pi, by positivity, fun τ hτ => ?_⟩
  set Φ : ℂ → ℂ := fun u => pulseAmplitude h (-I * u) * bianchiDeformedScatteringPhase α u *
    Complex.exp (u * (τ : ℂ)) with hΦ
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → -σ ≤ s.re ∧ s.re ≤ 0 := by
    intro s hs; rw [uIcc_of_ge (by linarith)] at hs; exact hs
  have hd : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → DifferentiableAt ℂ Φ s := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have hne : s ≠ 1 / 2 := fun he => by rw [he] at hs2; norm_num at hs2
    exact ((((h.differentiable_amplitude _).comp s (by fun_prop)).mul
      (differentiableAt_bianchiDeformedScatteringPhase hne (hxi_left s hs1))).mul (by fun_prop))
  have hbΦ : ∀ s : ℂ, s.re ∈ uIcc (0 : ℝ) (-σ) → ‖Φ s‖ ≤ B / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hstrip s hs
    have he : ‖Complex.exp (s * (τ : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have : (s * (τ : ℂ)).re = s.re * τ := by simp
      rw [this]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hs2 hτ)
    simp only [hΦ]; rw [norm_mul]
    calc ‖pulseAmplitude h (-I * s) * bianchiDeformedScatteringPhase α s‖ *
          ‖Complex.exp (s * (τ : ℂ))‖
        ≤ B / (1 + s.im ^ 2) * 1 := mul_le_mul (hB_left s hs1 hs2) he
            (norm_nonneg _) (by positivity)
      _ = B / (1 + s.im ^ 2) := mul_one _
  have hshift := integral_vertical_line_shift_of_decay hd hbΦ
  have hpk : bianchiDeformedReflectedField α h τ =
      ∫ t : ℝ, Φ (((0 : ℝ) : ℂ) + (t : ℂ) * I) := by
    rw [← bianchiDeformedLineField_zero]; rfl
  rw [hpk, hshift]
  have hpt : ∀ t : ℝ,
      ‖Φ (((-σ : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * τ) := by
    intro t
    have hre : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).re = -σ := by simp
    have him : (((-σ : ℝ) : ℂ) + (t : ℂ) * I).im = t := by simp
    simp only [hΦ]; rw [norm_mul, Complex.norm_exp]
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

/-- **Strict Failure of Bianchi Decay Above `(1 - α) / 2`.** For `1/2 < α < 1` and every
`δ > (1 - α) / 2`, `excitingPulse (((α : ℂ) - 1) / 2)` fails `O(e^{-δ τ})` on the deformed
Bianchi horizon. -/
theorem not_bianchiDeformedReflectedField_decay_gt {α δ : ℝ}
    (h0 : 1 / 2 < α) (h1 : α < 1) (hδ : (1 - α) / 2 < δ) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖bianchiDeformedReflectedField α (excitingPulse (((α : ℂ) - 1) / 2)) τ‖ ≤
        C * Real.exp (-δ * τ) := by
  rintro ⟨C₀, hC₀⟩
  have hα0 : 0 < α := by linarith
  set p : ℂ := ((α : ℂ) - 1) / 2 with hpdef
  set h := excitingPulse p
  have hp1 : 1 + 2 * p = (α : ℂ) := by rw [hpdef]; ring
  have hpxi : xiBianchiDeformed α (1 + 2 * p) = 0 := by
    rw [hp1, xiBianchiDeformed, primeTwoFactor_eval_self, zero_mul]
  have hpre : p.re = (α - 1) / 2 := by rw [hpdef]; simp
  have hp_neg : p.re < 0 := by rw [hpre]; linarith
  have hp_gt : -δ < p.re := by rw [hpre]; linarith
  obtain ⟨hGc, -⟩ := continuous_bianchiDeformedReflectedField_and_bounded hα0 h1 h
  obtain ⟨Ce, hCe, hGe⟩ := exists_bianchiDeformedReflectedField_early_decay hα0 h1 h
  set Lpos : ℂ → ℂ := fun w => ∫ τ in Ioi (0 : ℝ),
    Complex.exp (-w * (τ : ℂ)) * bianchiDeformedReflectedField α h τ with hLpos
  have hC₀' : ∀ τ : ℝ, -0 < τ →
      ‖bianchiDeformedReflectedField α h τ‖ ≤ max C₀ 0 * Real.exp (-δ * τ) :=
    fun τ hτ => (hC₀ τ (by linarith)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hLpos_d : DifferentiableOn ℂ Lpos {w : ℂ | -δ < w.re} := by
    simpa [hLpos] using differentiableOn_laplace hGc (le_max_right C₀ 0) hC₀'
  set Lneg₀ : ℂ → ℂ := fun z => ∫ σ in Ioi (0 : ℝ),
    Complex.exp (-z * (σ : ℂ)) * bianchiDeformedReflectedField α h (-σ) with hLneg₀
  have hGe' : ∀ σ : ℝ, -(0 : ℝ) < σ →
      ‖bianchiDeformedReflectedField α h (-σ)‖ ≤ Ce * Real.exp (-(3 / 8) * σ) := by
    intro σ hσ; simpa [mul_neg, neg_mul] using hGe (-σ) (by linarith)
  have hLneg₀_d : DifferentiableOn ℂ Lneg₀ {z : ℂ | -(3 / 8 : ℝ) < z.re} := by
    simpa [hLneg₀] using differentiableOn_laplace (hGc.comp continuous_neg) hCe hGe'
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
  set Φ₁ : ℂ → ℂ := fun w => (2 * w - 1) * xiBianchiDeformed α (1 + 2 * w) * (Lpos w + Lneg w)
    with hΦ₁
  set Φ₂ : ℂ → ℂ := fun w =>
    2 * Real.pi * pulseAmplitude h (-I * w) * (1 + 2 * w) * xiBianchiDeformed α (2 * w) with hΦ₂
  have hUpos : IsOpen {w : ℂ | -δ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUneg : IsOpen {w : ℂ | w.re < 3 / 8} := isOpen_lt Complex.continuous_re continuous_const
  have hΦ₁a : AnalyticOnNhd ℂ Φ₁ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w hw
    have h1' := (hLpos_d w hw.1).differentiableAt (hUpos.mem_nhds hw.1)
    have h2' := (hLneg_d w hw.2).differentiableAt (hUneg.mem_nhds hw.2)
    have hxi : DifferentiableAt ℂ (fun v : ℂ => xiBianchiDeformed α (1 + 2 * v)) w :=
      ((differentiable_xiBianchiDeformed α) _).comp w (by fun_prop)
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 2 * v - 1) w).mul hxi).mul
      (h1'.add h2')).differentiableWithinAt
  have hΦ₂a : AnalyticOnNhd ℂ Φ₂ S := by
    refine DifferentiableOn.analyticOnNhd ?_ hSo
    intro w _
    have ha : DifferentiableAt ℂ (fun v : ℂ => pulseAmplitude h (-I * v)) w :=
      (h.differentiable_amplitude _).comp w (by fun_prop)
    have hxi : DifferentiableAt ℂ (fun v : ℂ => xiBianchiDeformed α (2 * v)) w :=
      ((differentiable_xiBianchiDeformed α) _).comp w (by fun_prop)
    exact ((((differentiableAt_const _).mul ha).mul (by fun_prop)).mul hxi).differentiableWithinAt
  have hagree : ∀ w : ℂ, 1 / 8 < w.re → w.re < 5 / 16 → Φ₁ w = Φ₂ w := by
    intro w hw1 hw2
    have hlap : Lpos w + Lneg w =
        2 * Real.pi * pulseAmplitude h (-I * w) * bianchiDeformedScatteringPhase α w := by
      have hneg_rw : Lneg w = ∫ σ in Ioi (0 : ℝ),
          Complex.exp (w * (σ : ℂ)) * bianchiDeformedReflectedField α h (-σ) := by
        simp only [hLneg, hLneg₀, neg_neg]
      rw [hneg_rw]
      exact bianchiDeformed_bilateral_laplace_eq hα0 h1 h hw1 hw2
    have h2w : 2 * w - 1 ≠ 0 := fun h0' => by
      have := congrArg Complex.re h0'; simp at this; linarith
    have hxi : xiBianchiDeformed α (1 + 2 * w) ≠ 0 :=
      xiBianchiDeformed_ne_zero_of_one_le_re hα0 h1 (by simp; linarith)
    simp only [hΦ₁, hΦ₂, hlap, bianchiDeformedScatteringPhase]
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
  have hxi2p : xiBianchiDeformed α (2 * p) ≠ 0 := by
    rw [← xiBianchiDeformed_one_sub α (2 * p)]
    exact xiBianchiDeformed_ne_zero_of_one_le_re hα0 h1 (by simp [hpre]; linarith)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi ha_ne) h12p) hxi2p hp_eq.symm

/-- **Universal Causal Decay Infimum is Zero on the Bianchi Horizon.** For every `δ > 0`
(including `δ = 1/4` and `δ = 1/16`), there exists `α ∈ (7/8, 1)` such that the prime-`2` deformed
Bianchi horizon satisfies retarded time-domain echo causality, convergent Euler factorization over
`Nat.Primes`, global Schur passivity of the prime-`2` gate, continuous-spectrum unitarity, the
complete two-boundary pole dictionary for every zero of `xiBianchi`, sub-threshold decay
`O(e^{-σ τ})` (`0 < σ < (1 - α)/2`), and strict failure of `O(e^{-δ τ})`. -/
theorem bianchi_universal_causal_ringdown_infimum_zero {δ : ℝ} (hδ : 0 < δ) :
    ∃ α : ℝ, 7 / 8 < α ∧ α < 1 ∧
      (∀ τ : ℝ, τ ≤ 0 → deformedEchoKernel α τ = 0) ∧
      (∀ w : ℂ, 1 / 2 < w.re →
        HasProd (fun p : Nat.Primes => bianchiDeformedPrimeGate α p w)
          (primeTwoScatteringGate α w *
            ((riemannZeta (2 * w) * DirichletCharacter.LFunction chi3D (2 * w)) /
              (riemannZeta (2 * w + 1) * DirichletCharacter.LFunction chi3D (2 * w + 1))))) ∧
      (∀ t : ℝ, ‖bianchiDeformedScatteringPhase α ((t : ℂ) * I)‖ = 1) ∧
      (∀ ρ : ℂ, xiBianchi ρ = 0 →
        meromorphicOrderAt (bianchiDeformedWightmanRL α) (I * (ρ - 1) / 2) < 0) ∧
      (∀ σ : ℝ, 0 < σ → σ < (1 - α) / 2 → ∀ h : CompactPulse, ∃ C : ℝ, 0 ≤ C ∧
        ∀ τ : ℝ, 0 ≤ τ → ‖bianchiDeformedReflectedField α h τ‖ ≤ C * Real.exp (-σ * τ)) ∧
      (∃ h : CompactPulse, ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖bianchiDeformedReflectedField α h τ‖ ≤ C * Real.exp (-δ * τ)) := by
  set α : ℝ := max (15 / 16) (1 - δ)
  have hα78 : 7 / 8 < α := lt_of_lt_of_le (by norm_num : (7 / 8 : ℝ) < 15 / 16) (le_max_left _ _)
  have hα1 : α < 1 := max_lt (by norm_num) (by linarith)
  have hα_half : 1 / 2 < α := by linarith
  have hδ_gt : (1 - α) / 2 < δ := by
    have hle : 1 - δ ≤ α := le_max_right _ _
    linarith
  refine ⟨α, hα78, hα1, fun τ hτ => deformedEchoKernel_eq_zero_of_nonpos α hτ,
    fun w hw => hasProd_bianchiDeformedPrimeGate hw,
    fun t => norm_bianchiDeformedScatteringPhase_axis (by linarith) hα1 t, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨hr0, hr1⟩ := zero_mem_openStrip_of_xiBianchi_eq_zero hρ
    set ν : ℂ := I * (ρ - 1) / 2 with hν
    have him : ν.im = (ρ.re - 1) / 2 := by rw [hν]; simp
    have h12 : 1 - 2 * I * ν = ρ := by rw [hν]; linear_combination (1 - ρ) * I_sq
    have hz : xiBianchiDeformed α (1 - 2 * I * ν) = 0 := by
      rw [h12, xiBianchiDeformed, hρ, mul_zero]
    rw [bianchiDeformedWightmanRL_order_lower (by linarith) hα1 (by rw [him]; linarith)
      (by rw [him]; linarith) hz]
    exact (meromorphicOrderAt_pos_of_entire_zero (differentiable_xiBianchiDeformed α)
      (fun _ => xiBianchiDeformed_ne_zero_of_one_le_re (by linarith) hα1) hz).2.1
  · intro σ hσ0 hσα h
    exact bianchiDeformedReflectedField_decay hα_half hα1 hσ0 (by linarith) hσα h
  · exact ⟨excitingPulse (((α : ℂ) - 1) / 2),
      not_bianchiDeformedReflectedField_decay_gt hα_half hα1 hδ_gt⟩

end GaloisForLFunctions.RingdownOfTheCubicCover

end
