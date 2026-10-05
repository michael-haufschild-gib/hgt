import GaloisForLFunctions.HTGeometry.PositiveQuadrantMellinLines
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicConeMellin
import GaloisForLFunctions.RHTower.ChiRamanujanGrowingLabeledSource
/-!
# Actual physical cone pairing on moving near-pole Mellin lines

The full positive rational cone pairs with every physical Schwartz test on
any pair of lines with real parts greater than one. Absolute summability
and the positive-line Schwartz Mellin profile justify the full interchange.
The actual physical cutoff family is attached at 1+rho/log N with the original
prime cutoff N, both numerator cofactors, both masks and all profile dependence.
No uniform tail bound or signed asymptotic cancellation is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform ContDiff Topology BigOperators
namespace RHTower.BAGTrace
open HTGeometry
private abbrev RationalPair (P : Finset Nat.Primes) :=
  DenominatorRational P × DenominatorRational P

/-- Right-half-plane line parameters, viewed on the positive Mellin domain. -/
def bagConePositiveLines (σ : Fin 2 → {r : ℝ // 1 < r}) :
    Fin 2 → {r : ℝ // 0 < r} := fun i => ⟨σ i,zero_lt_one.trans (σ i).property⟩

/-- Full physical cone profile on the specified pair of Mellin lines. -/
def bagCubicConeLineProfile (σ : Fin 2 → {r : ℝ // 1 < r})
    (f : SchwartzMap BAGPhysicalSpace ℂ) : SchwartzMap BAGConeSpace ℂ :=
  PositiveLine.quadrantMellinProfile (bagConePositiveLines σ) (bagCubicConeSchwartz f)

variable (σ : Fin 2 → {r : ℝ // 1 < r})
private lemma moving_cone_factor (P : Finset Nat.Primes) (s t : ℂ) (w : RationalPair P) :
    criticalRationalCone P s t w=criticalRationalMass P w*
      rationalCharacter s w.1.val*rationalCharacter t w.2.val := by
  classical
  simp only [criticalRationalMass,criticalRationalCone,criticalRationalLabelCone,
    rationalCharacter,neg_zero,Complex.cpow_zero,mul_one,Finset.sum_mul,ite_mul,zero_mul]

private lemma moving_cone_line (P : Finset Nat.Primes) (w : RationalPair P) (v : BAGConeSpace) :
    criticalRationalCone P (PositiveLine.quadrantMellinLine (σ 0) (v 0)) (PositiveLine.quadrantMellinLine (σ 1) (v 1)) w=
      criticalRationalMass P w*PositiveLine.quadrantMellinKernel (bagConePositiveLines σ) (w.1.val.val : ℝ) (w.2.val.val : ℝ) v := by
  rw [moving_cone_factor]
  change _ = criticalRationalMass P w*(rationalCharacter _ w.1.val*rationalCharacter _ w.2.val)
  simp only [bagConePositiveLines]
  ring

private lemma moving_cone_norm (P : Finset Nat.Primes) (w : RationalPair P) (v : BAGConeSpace) :
    ‖criticalRationalCone P (PositiveLine.quadrantMellinLine (σ 0) (v 0)) (PositiveLine.quadrantMellinLine (σ 1) (v 1)) w‖=
      ‖criticalRationalCone P (σ 0 : ℂ) (σ 1 : ℂ) w‖ := by
  have he : criticalRationalCone P (σ 0 : ℂ) (σ 1 : ℂ) w=
      criticalRationalCone P (PositiveLine.quadrantMellinLine (σ 0) ((0 : BAGConeSpace) 0))
        (PositiveLine.quadrantMellinLine (σ 1) ((0 : BAGConeSpace) 1)) w := by simp [PositiveLine.quadrantMellinLine]
  rw [he,moving_cone_line σ,moving_cone_line σ,norm_mul,norm_mul,
    PositiveLine.norm_quadrantMellinKernel (bagConePositiveLines σ) (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property),
    PositiveLine.norm_quadrantMellinKernel (bagConePositiveLines σ) (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property)]

/-- The entire rational cone paired with any full three-coordinate Schwartz
Fourier profile. Both numerator cofactors, both label exclusions, and both
Mellin frequencies remain in the absolutely justified identity. -/
theorem criticalRationalCone_physical_line_hasSum (P : Finset Nat.Primes)
    (f : SchwartzMap BAGPhysicalSpace ℂ) :
    HasSum (fun w : RationalPair P => criticalRationalMass P w*
      (𝓕 f) (bagCubicConeNode (criticalRationalPoint P w)))
      (∫ v : BAGConeSpace,
        criticalCompletedConeEuler P (PositiveLine.quadrantMellinLine (σ 0) (v 0)) (PositiveLine.quadrantMellinLine (σ 1) (v 1))*
          bagCubicConeLineProfile σ f v) := by
  let Φ := bagCubicConeSchwartz f
  let Ψ := PositiveLine.quadrantMellinProfile (bagConePositiveLines σ) Φ
  let A (w : RationalPair P) (v : BAGConeSpace) : ℂ :=
    criticalRationalCone P (PositiveLine.quadrantMellinLine (σ 0) (v 0)) (PositiveLine.quadrantMellinLine (σ 1) (v 1)) w*Ψ v
  let B (w : RationalPair P) (v : BAGConeSpace) : ℝ :=
    ‖criticalRationalCone P (σ 0 : ℂ) (σ 1 : ℂ) w‖*‖Ψ v‖
  have hsum : Summable (fun w : RationalPair P => ‖criticalRationalCone P (σ 0 : ℂ) (σ 1 : ℂ) w‖) :=
    (criticalRationalCone_hasSum P (by simpa using (σ 0).property) (by simpa using (σ 1).property)).summable.norm
  have hmeas (w : RationalPair P) : AEStronglyMeasurable (A w) volume := by
    have h : A w=fun v => (criticalRationalMass P w*
        PositiveLine.quadrantMellinKernel (bagConePositiveLines σ) (w.1.val.val : ℝ) (w.2.val.val : ℝ) v)*Ψ v := by
      funext v
      dsimp only [A]
      rw [moving_cone_line σ]
    rw [h]
    exact ((continuous_const.mul (PositiveLine.continuous_quadrantMellinKernel (bagConePositiveLines σ)
      (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property))).mul
        Ψ.continuous).aestronglyMeasurable
  have hbound (w : RationalPair P) : ∀ᵐ v : BAGConeSpace,
      ‖A w v‖ ≤ B w v := by
    filter_upwards [] with v
    dsimp only [A,B]
    exact le_of_eq (by rw [norm_mul,moving_cone_norm σ])
  have hbsum : ∀ᵐ v : BAGConeSpace, Summable (fun w => B w v) := by
    filter_upwards [] with v
    exact hsum.mul_right ‖Ψ v‖
  have hbint : Integrable (fun v : BAGConeSpace => ∑' w, B w v) := by
    have he : (fun v : BAGConeSpace => ∑' w, B w v)=fun v =>
        (∑' w : RationalPair P, ‖criticalRationalCone P (σ 0 : ℂ) (σ 1 : ℂ) w‖)*‖Ψ v‖ := by
      funext v
      exact tsum_mul_right
    rw [he]
    exact Ψ.integrable.norm.const_mul _
  have hlim : ∀ᵐ v : BAGConeSpace,
      HasSum (fun w => A w v)
        (criticalCompletedConeEuler P (PositiveLine.quadrantMellinLine (σ 0) (v 0)) (PositiveLine.quadrantMellinLine (σ 1) (v 1))*Ψ v) := by
    filter_upwards [] with v
    apply HasSum.mul_right
    apply criticalRationalCone_hasSum P
    · simpa [PositiveLine.quadrantMellinLine] using (σ 0).property
    · simpa [PositiveLine.quadrantMellinLine] using (σ 1).property
  have h := hasSum_integral_of_dominated_convergence B hmeas hbound hbsum hbint hlim
  apply h.congr_fun
  intro w
  symm
  change (∫ v : BAGConeSpace, A w v)=_
  have he : A w=fun v => criticalRationalMass P w*
      (PositiveLine.quadrantMellinKernel (bagConePositiveLines σ) (w.1.val.val : ℝ) (w.2.val.val : ℝ) v*Ψ v) := by
    funext v
    dsimp only [A]
    rw [moving_cone_line σ,mul_assoc]
  rw [he,integral_const_mul]
  have hinv := PositiveLine.quadrantMellin_inversion (bagConePositiveLines σ) Φ (x := (w.1.val.val : ℝ)) (y := (w.2.val.val : ℝ))
    (by exact_mod_cast w.1.val.property) (by exact_mod_cast w.2.val.property)
  rw [hinv]
  rfl


/-- The literal logarithmic near-pole lines, at the original prime cutoff N. -/
def bagGrowingMellinLines (ρ : Fin 2 → {r : ℝ // 0 < r})
    (N : {n : ℕ // 2 ≤ n}) : Fin 2 → {r : ℝ // 1 < r} := fun i =>
  ⟨1+(ρ i : ℝ)/Real.log N.val,by
    have hn : 1 < (N.val : ℝ) := by exact_mod_cast (show 1 < N.val by have := N.property; omega)
    have hl := Real.log_pos hn
    have hp := div_pos (ρ i).property hl
    linarith⟩

/-- Actual physical cutoff family paired with the full original growing source
on its logarithmic near-pole lines. The moving profiles retain all dependence. -/
theorem exists_bagCubicPhysicalMovingMellinFamily :
    ∃ (η : ℕ → ℝ → ℝ) (A : ℕ → SchwartzMap BAGPhysicalSpace ℂ),
      (∀ᶠ N : ℕ in atTop,
        ContDiff ℝ ∞ (η N) ∧ HasCompactSupport (η N) ∧
        (∀ p : ℝ, η N p ∈ Icc (0 : ℝ) 1) ∧
        (∀ p : ℝ, p ∉ Ioo (N : ℝ) (2*N) → η N p=0) ∧
        (∀ p ∈ Icc ((N : ℝ)+(N : ℝ)^((1 : ℝ)/4))
          (2*N-(N : ℝ)^((1 : ℝ)/4)), η N p=1) ∧
        (∀ v : BAGPhysicalSpace, A N v=bagCubicPhysicalAmplitude N (η N) v) ∧
        (∀ a : BAGPhysicalSpace, Summable (fun k : ℤ × ℤ × ℤ =>
          ‖(𝓕 (A N)) (bagIntegerTriple k+a)‖))) ∧
      Tendsto (fun N : ℕ => (Real.log (N : ℝ))^2/(N : ℝ)*
        ‖primeGaussianCubicOffDiagonal (N : ℝ)-
          primeGaussianCubicSmoothedOffDiagonal N (η N)‖) atTop (𝓝 0) ∧
      (∀ (N : {n : ℕ // 2 ≤ n}) (ρ : Fin 2 → {r : ℝ // 0 < r}),
        HasSum (fun w : RationalPair (Sieve.primeSubtypeLE N.val) =>
          criticalRationalMass (Sieve.primeSubtypeLE N.val) w*
            (𝓕 (A N.val)) (bagCubicConeNode (criticalRationalPoint (Sieve.primeSubtypeLE N.val) w)))
          (∫ v : BAGConeSpace,
            criticalCompletedConeEuler (Sieve.primeSubtypeLE N.val)
              (PositiveLine.quadrantMellinLine (bagGrowingMellinLines ρ N 0) (v 0))
              (PositiveLine.quadrantMellinLine (bagGrowingMellinLines ρ N 1) (v 1))*
                bagCubicConeLineProfile (bagGrowingMellinLines ρ N) (A N.val) v)) := by
  obtain ⟨η,A,hreg,herr⟩ := exists_bagCubicPhysicalFourierFamily
  exact ⟨η,A,hreg,herr,fun N ρ => criticalRationalCone_physical_line_hasSum
    (bagGrowingMellinLines ρ N) (Sieve.primeSubtypeLE N.val) (A N.val)⟩

end RHTower.BAGTrace
