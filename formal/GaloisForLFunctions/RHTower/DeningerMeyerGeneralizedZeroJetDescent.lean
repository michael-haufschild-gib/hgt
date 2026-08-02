import GaloisForLFunctions.RHTower.DeningerMeyerPoissonMellinFactorization

/-!
# Generalized zeta-zero jets on Meyer cohomology

Meyer's quotient must retain generalized eigendata when a zeta zero has
multiplicity greater than one.  Simple point evaluation is therefore
insufficient.  This file differentiates the exact Poisson Mellin factorization
to every finite order.

If zeta vanishes through order `k` at `ρ`, the `k`-th logarithmic Mellin jet
annihilates every genuine Poisson boundary and hence descends to the actual
all-weight Meyer quotient.  Paugam's weighted reciprocal involution reflects
that quotient functional from `ρ` to `1 - ρ` with the exact sign `(-1)^k`.

All statements are unconditional.  No simplicity, semisimplicity,
Riemann-hypothesis, trace, positivity, or numerical premise occurs.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Classical

namespace RHTower

noncomputable section

/-- The `k`-th logarithmic Mellin jet as a linear functional on the strong target. -/
def deningerMeyerStrongLogMellinJetLM (k : ℕ) (s : ℂ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ where
  toFun g :=
    ∫ t : ℝ,
      deningerMeyerStrongLogMellinJet k s g t
  map_add' g h := by
    change
      (∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            k s (g.val + h.val) t) =
        (∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            k s g.val t) +
        ∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            k s h.val t
    have heq :
        deningerMeyerStrongLogMellinJet
            k s (g.val + h.val) =
          deningerMeyerStrongLogMellinJet
              k s g.val +
            deningerMeyerStrongLogMellinJet
              k s h.val := by
      funext t
      simp only [
        deningerMeyerStrongLogMellinJet,
        Pi.add_apply]
      ring
    rw [heq]
    simpa only [Pi.add_apply] using
      integral_add
        (integrable_deningerMeyerStrongLogMellinJet
          g.property k s)
        (integrable_deningerMeyerStrongLogMellinJet
          h.property k s)
  map_smul' c g := by
    change
      (∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            k s (c • g.val) t) =
        c •
          ∫ t : ℝ,
            deningerMeyerStrongLogMellinJet
              k s g.val t
    have heq :
        deningerMeyerStrongLogMellinJet
            k s (c • g.val) =
          fun t =>
            c *
              deningerMeyerStrongLogMellinJet
                k s g.val t := by
      funext t
      simp only [
        deningerMeyerStrongLogMellinJet,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, integral_const_mul, smul_eq_mul]

theorem deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv
    (g : DeningerMeyerStrongLogTarget) (k : ℕ) (s : ℂ) :
    deningerMeyerStrongLogMellinJetLM k s g =
      iteratedDeriv k
        (deningerMeyerStrongLogMellin g) s := by
  exact
    (iteratedDeriv_deningerMeyerStrongLogMellin_eq_integral_jet
      g.property k s).symm

/--
Every Poisson boundary has zero `k`-jet at a zeta zero whose vanishing order
is greater than `k`.
-/
theorem
    deningerMeyerStrongLogMellin_boundary_iteratedDeriv_zero
    (f : DeningerMeyerCap) {ρ : ℂ}
    (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (k : ℕ)
    (hζjets :
      ∀ j ≤ k, iteratedDeriv j riemannZeta ρ = 0) :
    iteratedDeriv k
        (deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogSumLM f)) ρ = 0 := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {1}
  have hUopen : IsOpen U :=
    (isOpen_lt
      continuous_const Complex.continuous_re).sdiff
      isClosed_singleton
  have hρU : ρ ∈ U := ⟨hρ0, hρ1⟩
  have heq :
      (fun z : ℂ =>
        deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogSumLM f) z) =ᶠ[𝓝 ρ]
        fun z : ℂ => riemannZeta z * mellin f.val z := by
    filter_upwards [hUopen.mem_nhds hρU] with z hz
    simpa only [] using
      deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin_of_re_pos
        f hz.1 hz.2
  rw [heq.iteratedDeriv_eq k]
  have hζsmooth :
      ContDiffAt ℂ (k : WithTop ℕ∞) riemannZeta ρ :=
    (analyticOn_riemannZeta ρ hρ1).contDiffAt
  have hmellinAnalytic :
      AnalyticAt ℂ (mellin f.val) ρ := by
    apply
      DifferentiableOn.analyticAt
        (s := {z : ℂ | 0 < z.re})
    · intro z hz
      exact
        (differentiableAt_mellin_schwartzMap_of_re_pos
          f.val hz).differentiableWithinAt
    · exact
        (isOpen_lt
          continuous_const Complex.continuous_re).mem_nhds hρ0
  change
    iteratedDeriv k
      (riemannZeta * mellin f.val) ρ = 0
  rw [iteratedDeriv_mul
    hζsmooth hmellinAnalytic.contDiffAt]
  apply Finset.sum_eq_zero
  intro j hj
  have hjle : j ≤ k :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [hζjets j hjle]
  simp

/--
The `k`-th generalized zeta-zero jet descends to actual Meyer cohomology
whenever zeta vanishes through order `k` at the spectral point.
-/
def deningerMeyerZetaZeroJetEvaluationLM
    (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (k : ℕ)
    (hζjets :
      ∀ j ≤ k, iteratedDeriv j riemannZeta ρ = 0) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  (LinearMap.range deningerMeyerStrongLogSumLM).liftQ
    (deningerMeyerStrongLogMellinJetLM k ρ)
    (by
      rintro _ ⟨f, rfl⟩
      rw [LinearMap.mem_ker]
      rw [
        deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
        deningerMeyerStrongLogMellin_boundary_iteratedDeriv_zero
          f hρ0 hρ1 k hζjets])

@[simp]
theorem deningerMeyerZetaZeroJetEvaluationLM_mk
    (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (k : ℕ)
    (hζjets :
      ∀ j ≤ k, iteratedDeriv j riemannZeta ρ = 0)
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerZetaZeroJetEvaluationLM
        ρ hρ0 hρ1 k hζjets
        (Submodule.Quotient.mk g) =
      deningerMeyerStrongLogMellinJetLM k ρ g :=
  rfl

/--
Weighted reciprocal inversion reflects generalized Mellin jets and contributes
the exact parity sign from differentiating `s ↦ 1 - s`.
-/
theorem deningerMeyerStrongLogMellinJetLM_J
    (g : DeningerMeyerStrongLogTarget)
    (k : ℕ) (s : ℂ) :
    deningerMeyerStrongLogMellinJetLM k s
        (deningerMeyerStrongLogJ g) =
      (-1 : ℂ) ^ k *
        deningerMeyerStrongLogMellinJetLM k (1 - s) g := by
  change
    (∫ t : ℝ,
        deningerMeyerStrongLogMellinJet k s
          (deningerMeyerStrongLogJ g) t) =
      (-1 : ℂ) ^ k *
        ∫ t : ℝ,
          deningerMeyerStrongLogMellinJet
            k (1 - s) g t
  rw [← integral_const_mul,
    ← integral_neg_eq_self
      (fun t : ℝ =>
        (-1 : ℂ) ^ k *
          deningerMeyerStrongLogMellinJet
            k (1 - s) g t) volume]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerMeyerStrongLogMellinJet,
    deningerMeyerStrongLogMellinJet,
    deningerMeyerStrongLogJ_apply]
  simp only [Complex.ofReal_neg]
  rw [Complex.ofReal_exp]
  have hexp :
      Complex.exp (s * (t : ℂ)) *
          Complex.exp (-(t : ℂ)) =
        Complex.exp ((1 - s) * (-(t : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hpow :
      (-1 : ℂ) ^ k * (-(t : ℂ)) ^ k =
        (t : ℂ) ^ k := by
    rw [← mul_pow]
    ring_nf
  rw [show (((-t : ℝ) : ℂ)) = -(t : ℂ) by
    push_cast
    rfl]
  calc
    (t : ℂ) ^ k * Complex.exp (s * (t : ℂ)) *
          (Complex.exp (-(t : ℂ)) *
            (g : ℝ → ℂ) (-t)) =
        (t : ℂ) ^ k *
          (Complex.exp (s * (t : ℂ)) *
            Complex.exp (-(t : ℂ))) *
          (g : ℝ → ℂ) (-t) := by ring
    _ =
        (t : ℂ) ^ k *
          Complex.exp ((1 - s) * (-(t : ℂ))) *
          (g : ℝ → ℂ) (-t) := by rw [hexp]
    _ =
        (-1 : ℂ) ^ k *
          ((-(t : ℂ)) ^ k *
            Complex.exp ((1 - s) * (-(t : ℂ))) *
            (g : ℝ → ℂ) (-t)) := by
      rw [← hpow]
      ring

/--
On generalized zero-jet evaluations, descended `J` is reflection together
with the exact parity sign.
-/
theorem deningerMeyerZetaZeroJetEvaluationLM_J
    (ρ : ℂ) (hρ0 : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (hσ0 : 0 < (1 - ρ).re) (hσ1 : 1 - ρ ≠ 1)
    (k : ℕ)
    (hζjets :
      ∀ j ≤ k, iteratedDeriv j riemannZeta ρ = 0)
    (hζreflected :
      ∀ j ≤ k,
        iteratedDeriv j riemannZeta (1 - ρ) = 0)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerZetaZeroJetEvaluationLM
        ρ hρ0 hρ1 k hζjets
        (deningerMeyerStrongLogCohomologyJ u) =
      (-1 : ℂ) ^ k *
        deningerMeyerZetaZeroJetEvaluationLM
          (1 - ρ) hσ0 hσ1 k hζreflected u := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp only [
        deningerMeyerStrongLogCohomologyJ_mk,
        deningerMeyerZetaZeroJetEvaluationLM_mk,
        deningerMeyerStrongLogMellinJetLM_J]

end

end RHTower
