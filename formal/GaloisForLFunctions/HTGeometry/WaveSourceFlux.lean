import GaloisForLFunctions.HTGeometry.WaveEnergyDerivative
import GaloisForLFunctions.HTGeometry.WaveGreenIdentityIntegrable
import Mathlib.Analysis.ODE.Gronwall

/-!
# The flux identity with a source

The inhomogeneous clock equation `∂ₜ²u = Δu + Vu + f` has the same energy computation as the
homogeneous one, with one extra term: the source pairs with the time derivative. Everything else
cancels exactly as before, so

`∫ ∂ₜ(energy density) = 2∫ ((V+1)·u·∂ₜu + f·∂ₜu)`.

The extra pairing is what a Picard iteration on the Duhamel formula controls, so this identity is
the entry point to an existence proof by the energy method.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Source

variable {d : ℕ} {u V f : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)} {t : ℝ}

/-- The clock equation with a source. -/
def SolvesWaveEqSource (u V f : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ∀ p : ℝ × (Fin d → ℝ), waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u) p)
      + V p * u p + f p

/-- A source-free solution is the special case of a vanishing source. -/
theorem solvesWaveEqSource_zero (h : SolvesWaveEq u V) :
    SolvesWaveEqSource u V (fun _ => 0) := by
  intro p
  rw [show ((fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) p) = 0 from rfl, add_zero]
  exact h p

/-- **A source is absorbed into the potential wherever the field does not vanish**, so the
inhomogeneous equation is the homogeneous one for a modified potential off the zero set. -/
theorem solvesWaveEq_of_solvesWaveEqSource (h : SolvesWaveEqSource u V f)
    {p : ℝ × (Fin d → ℝ)} (hp : u p ≠ 0) :
    waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) p
      = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u) p)
        + (V p + f p / u p) * u p := by
  rw [h p]
  field_simp
  ring

/-- **The pointwise energy identity with a source.** -/
theorem waveDirDeriv_energyDensity_source (hu : ContDiff ℝ ∞ u)
    (hsolve : SolvesWaveEqSource u V f) (p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv (timeDir d) (energyDensity u) p
      = 2 * (waveDirDeriv (timeDir d) u p
          * ((∑ i : Fin d, waveDirDeriv (spaceDir d i)
              (waveDirDeriv (spaceDir d i) u) p) + V p * u p + f p))
        + (∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u p
            * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) p))
        + 2 * (u p * waveDirDeriv (timeDir d) u p) := by
  rw [waveDirDeriv_energyDensity hu p, hsolve p]

/-! ## The energy dominates the time derivative -/

/-- **The energy of a slice dominates the `L²` norm of the time derivative there.** This is what
bounds the source pairing in the inhomogeneous estimate. -/
theorem integral_sq_dirDeriv_le_waveEnergy
    (hsq : Integrable (fun x : Fin d → ℝ => (waveDirDeriv (timeDir d) u (t, x)) ^ 2)
      (volume : Measure (Fin d → ℝ)))
    (hden : Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
      (volume : Measure (Fin d → ℝ))) :
    (∫ x : Fin d → ℝ, (waveDirDeriv (timeDir d) u (t, x)) ^ 2) ≤ waveEnergy u t := by
  refine integral_mono hsq hden fun x => ?_
  have hsum : 0 ≤ ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u (t, x)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [energyDensity]
  nlinarith [sq_nonneg (u (t, x))]

/-- **The energy of a slice dominates the `L²` norm of the field there.** -/
theorem integral_sq_le_waveEnergy
    (hsq : Integrable (fun x : Fin d → ℝ => (u (t, x)) ^ 2) (volume : Measure (Fin d → ℝ)))
    (hden : Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
      (volume : Measure (Fin d → ℝ))) :
    (∫ x : Fin d → ℝ, (u (t, x)) ^ 2) ≤ waveEnergy u t := by
  refine integral_mono hsq hden fun x => ?_
  have hsum : 0 ≤ ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u (t, x)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [energyDensity]
  nlinarith [sq_nonneg (waveDirDeriv (timeDir d) u (t, x))]

/-! ## The integrated identity with a source -/

/-- **The energy flux identity for the inhomogeneous equation.** -/
theorem integral_dirDeriv_energyDensity_source (hu : ContDiff ℝ ∞ u)
    (hsolve : SolvesWaveEqSource u V f) (t : ℝ)
    (h1 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i (coordPartial i (slice u t)) x
        * slice (waveDirDeriv (timeDir d) u) t x) (volume : Measure (Fin d → ℝ)))
    (h2 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i (slice u t) x
        * coordPartial i (slice (waveDirDeriv (timeDir d) u) t) x)
      (volume : Measure (Fin d → ℝ)))
    (h3 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i (slice u t) x
        * slice (waveDirDeriv (timeDir d) u) t x) (volume : Measure (Fin d → ℝ)))
    (h4 : Integrable
      (fun x : Fin d → ℝ => 2 * ((V (t, x) + 1)
        * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))))
      (volume : Measure (Fin d → ℝ)))
    (h5 : Integrable
      (fun x : Fin d → ℝ => 2 * (f (t, x) * waveDirDeriv (timeDir d) u (t, x)))
      (volume : Measure (Fin d → ℝ))) :
    (∫ x : Fin d → ℝ, waveDirDeriv (timeDir d) (energyDensity u) (t, x))
      = (2 * ∫ x : Fin d → ℝ,
          (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)))
        + 2 * ∫ x : Fin d → ℝ, f (t, x) * waveDirDeriv (timeDir d) u (t, x) := by
  classical
  set F : (Fin d → ℝ) → ℝ := slice u t with hF
  set g : (Fin d → ℝ) → ℝ := slice (waveDirDeriv (timeDir d) u) t with hg
  have hFcd : ContDiff ℝ ∞ F := contDiff_slice hu t
  have hgcd : ContDiff ℝ ∞ g := contDiff_slice (contDiff_dirDeriv hu _) t
  have hpt : ∀ x : Fin d → ℝ, waveDirDeriv (timeDir d) (energyDensity u) (t, x)
      = (2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i F) x)
          + (∑ i : Fin d, 2 * (coordPartial i F x * coordPartial i g x)))
        + (2 * ((V (t, x) + 1) * (F x * g x)) + 2 * (f (t, x) * g x)) := by
    intro x
    have hexp := waveDirDeriv_energyDensity hu (t, x)
    have heq := hsolve (t, x)
    have hgeta : (fun y : Fin d → ℝ => waveDirDeriv (timeDir d) u (t, y)) = g := rfl
    have hfeta : (fun y : Fin d → ℝ => u (t, y)) = F := rfl
    have hspeta : ∀ i : Fin d, (fun y : Fin d → ℝ => waveDirDeriv (spaceDir d i) u (t, y))
        = coordPartial i F := by
      intro i
      funext y
      exact waveDirDeriv_spaceDir_eq hu i t y
    have hlap : ∀ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u) (t, x)
        = coordPartial i (coordPartial i F) x := by
      intro i
      rw [waveDirDeriv_spaceDir_eq (contDiff_dirDeriv hu _) i t x, hspeta i]
    have hmix : ∀ i : Fin d, waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (t, x)
        = coordPartial i g x := by
      intro i
      rw [waveDirDeriv_comm hu, waveDirDeriv_spaceDir_eq (contDiff_dirDeriv hu _) i t x, hgeta]
    have hsp : ∀ i : Fin d, waveDirDeriv (spaceDir d i) u (t, x) = coordPartial i F x := by
      intro i
      rw [waveDirDeriv_spaceDir_eq hu i t x, hfeta]
    have hsum : (∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (t, x)
          * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (t, x)))
        = ∑ i : Fin d, 2 * (coordPartial i F x * coordPartial i g x) :=
      Finset.sum_congr rfl fun i _ => by rw [hsp i, hmix i]
    have hlapsum : (∑ i : Fin d, waveDirDeriv (spaceDir d i)
          (waveDirDeriv (spaceDir d i) u) (t, x))
        = ∑ i : Fin d, coordPartial i (coordPartial i F) x :=
      Finset.sum_congr rfl fun i _ => hlap i
    have hg' : waveDirDeriv (timeDir d) u (t, x) = g x := rfl
    have hf' : u (t, x) = F x := rfl
    rw [hexp, heq, hlapsum, hsum, hg', hf']
    ring
  have hint1 : Integrable (fun x : Fin d → ℝ =>
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i F) x))
      (volume : Measure (Fin d → ℝ)) := by
    have hsumint : Integrable (fun x : Fin d → ℝ =>
        ∑ i : Fin d, coordPartial i (coordPartial i F) x * g x)
        (volume : Measure (Fin d → ℝ)) := integrable_finsetSum _ fun i _ => h1 i
    refine (hsumint.const_mul 2).congr (Filter.Eventually.of_forall fun x => ?_)
    show 2 * ∑ i : Fin d, coordPartial i (coordPartial i F) x * g x
      = 2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i F) x)
    rw [← Finset.sum_mul, mul_comm (∑ i : Fin d, coordPartial i (coordPartial i F) x) (g x)]
  have hint2' : Integrable
      (fun x : Fin d → ℝ => ∑ i : Fin d, 2 * (coordPartial i F x * coordPartial i g x))
      (volume : Measure (Fin d → ℝ)) :=
    integrable_finsetSum _ fun i _ => (h2 i).const_mul 2
  have h4' : Integrable (fun x : Fin d → ℝ => 2 * ((V (t, x) + 1) * (F x * g x)))
      (volume : Measure (Fin d → ℝ)) := h4
  have h5' : Integrable (fun x : Fin d → ℝ => 2 * (f (t, x) * g x))
      (volume : Measure (Fin d → ℝ)) := h5
  have hint12 : Integrable (fun x : Fin d → ℝ =>
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i F) x)
        + ∑ i : Fin d, 2 * (coordPartial i F x * coordPartial i g x))
      (volume : Measure (Fin d → ℝ)) := hint1.add hint2'
  have hint45 : Integrable (fun x : Fin d → ℝ =>
      2 * ((V (t, x) + 1) * (F x * g x)) + 2 * (f (t, x) * g x))
      (volume : Measure (Fin d → ℝ)) := h4'.add h5'
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hint12 hint45,
    integral_add hint1 hint2', integral_add h4' h5']
  have hgreen : (∫ x : Fin d → ℝ,
      2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i F) x))
      = -∑ i : Fin d, 2 * ∫ x : Fin d → ℝ, coordPartial i F x * coordPartial i g x := by
    have hcomm : (fun x : Fin d → ℝ =>
        2 * (g x * ∑ i : Fin d, coordPartial i (coordPartial i F) x))
        = fun x : Fin d → ℝ =>
          2 * ((∑ i : Fin d, coordPartial i (coordPartial i F) x) * g x) := by
      funext x
      ring
    rw [hcomm, integral_const_mul,
      integral_laplacian_mul_of_integrable hFcd hgcd h1 h2 h3, mul_neg, Finset.mul_sum]
  have hsum2 : (∫ x : Fin d → ℝ, ∑ i : Fin d, 2 * (coordPartial i F x * coordPartial i g x))
      = ∑ i : Fin d, 2 * ∫ x : Fin d → ℝ, coordPartial i F x * coordPartial i g x := by
    rw [integral_finsetSum _ fun i _ => (h2 i).const_mul 2]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  rw [hgreen, hsum2, neg_add_cancel, zero_add, integral_const_mul, integral_const_mul]
  rfl

/-! ## The source pairing is dominated by the energy -/

/-- **The source pairing is bounded by the `L²` norm of the source and the energy.** Using
`2|ab| ≤ a² + b²` rather than Cauchy–Schwarz keeps the estimate free of square roots, at the cost of
replacing `2‖f‖·√E` by `‖f‖² + E`. -/
theorem abs_integral_source_le
    (hfg : Integrable (fun x : Fin d → ℝ => f (t, x) * waveDirDeriv (timeDir d) u (t, x))
      (volume : Measure (Fin d → ℝ)))
    (hf2 : Integrable (fun x : Fin d → ℝ => (f (t, x)) ^ 2) (volume : Measure (Fin d → ℝ)))
    (hg2 : Integrable (fun x : Fin d → ℝ => (waveDirDeriv (timeDir d) u (t, x)) ^ 2)
      (volume : Measure (Fin d → ℝ)))
    (hden : Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
      (volume : Measure (Fin d → ℝ))) :
    |2 * ∫ x : Fin d → ℝ, f (t, x) * waveDirDeriv (timeDir d) u (t, x)|
      ≤ (∫ x : Fin d → ℝ, (f (t, x)) ^ 2) + waveEnergy u t := by
  have hpt : ∀ x : Fin d → ℝ,
      |f (t, x) * waveDirDeriv (timeDir d) u (t, x)|
        ≤ ((f (t, x)) ^ 2 + (waveDirDeriv (timeDir d) u (t, x)) ^ 2) / 2 := by
    intro x
    have h := two_mul_le_add_sq |f (t, x)| |waveDirDeriv (timeDir d) u (t, x)|
    rw [sq_abs, sq_abs] at h
    rw [abs_mul]
    linarith
  have hmono : (∫ x : Fin d → ℝ, |f (t, x) * waveDirDeriv (timeDir d) u (t, x)|)
      ≤ ∫ x : Fin d → ℝ,
          ((f (t, x)) ^ 2 + (waveDirDeriv (timeDir d) u (t, x)) ^ 2) / 2 :=
    integral_mono hfg.abs ((hf2.add hg2).div_const 2) hpt
  have hsplit : (∫ x : Fin d → ℝ,
      ((f (t, x)) ^ 2 + (waveDirDeriv (timeDir d) u (t, x)) ^ 2) / 2)
      = ((∫ x : Fin d → ℝ, (f (t, x)) ^ 2)
        + ∫ x : Fin d → ℝ, (waveDirDeriv (timeDir d) u (t, x)) ^ 2) / 2 := by
    rw [integral_div, integral_add hf2 hg2]
  have hnorm : |∫ x : Fin d → ℝ, f (t, x) * waveDirDeriv (timeDir d) u (t, x)|
      ≤ ∫ x : Fin d → ℝ, |f (t, x) * waveDirDeriv (timeDir d) u (t, x)| := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (f := fun x : Fin d → ℝ => f (t, x) * waveDirDeriv (timeDir d) u (t, x))
  have hE := integral_sq_dirDeriv_le_waveEnergy (u := u) (t := t) hg2 hden
  rw [hsplit] at hmono
  rw [abs_mul, abs_two]
  linarith

/-! ## The inhomogeneous estimate -/

/-- **The energy estimate for the inhomogeneous equation.** With the flux identity supplying the
derivative of the energy and the two bounds supplying its size, Grönwall gives the growth bound with
a source term. -/
theorem waveEnergy_le_gronwall_source
    (hderiv : ∀ s : ℝ, HasDerivAt (waveEnergy u)
      ((2 * ∫ x : Fin d → ℝ,
          (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x)))
        + 2 * ∫ x : Fin d → ℝ, f (s, x) * waveDirDeriv (timeDir d) u (s, x)) s)
    {M S : ℝ}
    (hVb : ∀ s : ℝ, |2 * ∫ x : Fin d → ℝ,
        (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x))|
      ≤ (M + 1) * waveEnergy u s)
    (hfb : ∀ s : ℝ, |2 * ∫ x : Fin d → ℝ,
        f (s, x) * waveDirDeriv (timeDir d) u (s, x)| ≤ S + waveEnergy u s)
    {t : ℝ} (ht : 0 ≤ t) :
    waveEnergy u t ≤ gronwallBound (waveEnergy u 0) (M + 2) S t := by
  have hcont : ContinuousOn (waveEnergy u) (Set.Icc 0 t) :=
    fun s _ => ((hderiv s).continuousAt).continuousWithinAt
  have ha : ‖waveEnergy u 0‖ ≤ waveEnergy u 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (waveEnergy_nonneg u 0)]
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖(2 * ∫ x : Fin d → ℝ,
          (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x)))
        + 2 * ∫ x : Fin d → ℝ, f (s, x) * waveDirDeriv (timeDir d) u (s, x)‖
        ≤ (M + 2) * ‖waveEnergy u s‖ + S := by
    intro s _
    have h1 := hVb s
    have h2 := hfb s
    have habs := abs_add_le
      (2 * ∫ x : Fin d → ℝ,
        (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x)))
      (2 * ∫ x : Fin d → ℝ, f (s, x) * waveDirDeriv (timeDir d) u (s, x))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (waveEnergy_nonneg u s)]
    linarith
  have hgb := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s _ => (hderiv s).hasDerivWithinAt) ha hbound t (Set.mem_Icc.mpr ⟨ht, le_rfl⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (waveEnergy_nonneg u t)] at hgb
  simpa using hgb

end Source

end GaloisForLFunctions.HTGeometry
