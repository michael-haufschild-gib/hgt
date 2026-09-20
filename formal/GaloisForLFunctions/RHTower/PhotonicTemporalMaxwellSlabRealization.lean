import GaloisForLFunctions.RHTower.PhotonicPrimeCyclicSlabParabolicRealization

/-!
# Literal temporal-Maxwell realization of the PTR cyclic slab

## PTR proof-chain position

This module discharges the physical transfer-matrix gap left by the cyclic
oscillator-slab construction.  It formalizes a spatial Fourier mode of the
source-free one-dimensional temporal Maxwell system in its physically
continuous state `(D, B)`, with positive permeability `μ = κ`, positive
permittivity `ε = κ⁻¹`, and conserved spatial wavenumber `Ω`:

`D' = (Ω / μ) B`, `B' = -(Ω / ε) D`.

Its exact propagator is the existing oscillator-flow matrix.  At each temporal
material boundary the state is retained, so a two-slab prime medium with
impedances `4 log p` and `log p` has exactly the PTR prime cyclic transfer,
and hence its established parabolic two-cycle intertwining.

This is a literal homogeneous magnetodielectric temporal-slab realization of
the transfer layer.  It does not derive the rotating-OAM Floquet overlap,
the complex infinite conormal ladder, or the defect-confinement law; those
remain the load-bearing PTR steps to RH.
-/

noncomputable section

open Complex Matrix
open scoped Matrix

namespace RHTower

/-- Strictly positive material parameter. -/
abbrev PTRTemporalMaxwellPositive := Set.Ioi (0 : ℝ)

/-- Real displacement--magnetic state of one spatial Fourier mode. -/
abbrev PTRTemporalMaxwellRealState := Fin 2 → ℝ

/-- Exact constant-material temporal-Maxwell propagator in the `(D,B)` state. -/
noncomputable def ptrTemporalMaxwellRealFlow
    (κ Ω : PTRTemporalMaxwellPositive) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos ((Ω : ℝ) * t), Real.sin ((Ω : ℝ) * t) / (κ : ℝ);
    -Real.sin ((Ω : ℝ) * t) * (κ : ℝ), Real.cos ((Ω : ℝ) * t)]

/-- Temporal-Maxwell plane-wave state with initial displacement--magnetic data. -/
noncomputable def ptrTemporalMaxwellRealMode
    (κ Ω : PTRTemporalMaxwellPositive) (u₀ : PTRTemporalMaxwellRealState) (t : ℝ) :
    PTRTemporalMaxwellRealState :=
  ptrTemporalMaxwellRealFlow κ Ω t *ᵥ u₀

/-- The displacement component obeys the exact temporal Maxwell evolution equation. -/
theorem deriv_ptrTemporalMaxwellRealMode_displacement
    (κ Ω : PTRTemporalMaxwellPositive) (u₀ : PTRTemporalMaxwellRealState) (t : ℝ) :
    deriv (fun τ => ptrTemporalMaxwellRealMode κ Ω u₀ τ 0) t =
      (Ω : ℝ) / (κ : ℝ) * ptrTemporalMaxwellRealMode κ Ω u₀ t 1 := by
  have hphase : HasDerivAt (fun τ : ℝ => (Ω : ℝ) * τ) (Ω : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (Ω : ℝ)
  have hcos := (Real.hasDerivAt_cos ((Ω : ℝ) * t)).comp t hphase
  have hsin := (Real.hasDerivAt_sin ((Ω : ℝ) * t)).comp t hphase
  have hsum := (hcos.mul_const (u₀ 0)).add
    ((hsin.div_const (κ : ℝ)).mul_const (u₀ 1))
  have hκ : (κ : ℝ) ≠ 0 := ne_of_gt κ.property
  have hstate0 (τ : ℝ) : ptrTemporalMaxwellRealMode κ Ω u₀ τ 0 =
      Real.cos ((Ω : ℝ) * τ) * u₀ 0 +
        Real.sin ((Ω : ℝ) * τ) / (κ : ℝ) * u₀ 1 := by
    simp [ptrTemporalMaxwellRealMode, ptrTemporalMaxwellRealFlow,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hstate1 : ptrTemporalMaxwellRealMode κ Ω u₀ t 1 =
      -Real.sin ((Ω : ℝ) * t) * (κ : ℝ) * u₀ 0 +
        Real.cos ((Ω : ℝ) * t) * u₀ 1 := by
    simp [ptrTemporalMaxwellRealMode, ptrTemporalMaxwellRealFlow,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [show (fun τ => ptrTemporalMaxwellRealMode κ Ω u₀ τ 0) =
      (fun τ => Real.cos ((Ω : ℝ) * τ) * u₀ 0 +
        Real.sin ((Ω : ℝ) * τ) / (κ : ℝ) * u₀ 1) from funext hstate0]
  have hfun :
      ((fun y => (Real.cos ∘ HMul.hMul (Ω : ℝ)) y * u₀ 0) +
        fun y => (Real.sin ∘ HMul.hMul (Ω : ℝ)) y / (κ : ℝ) * u₀ 1) =
      (fun τ => Real.cos ((Ω : ℝ) * τ) * u₀ 0 +
        Real.sin ((Ω : ℝ) * τ) / (κ : ℝ) * u₀ 1) := by
    funext τ
    rfl
  rw [← hfun, hsum.deriv, hstate1]
  field_simp [hκ]

/-- The magnetic component obeys the exact temporal Maxwell evolution equation. -/
theorem deriv_ptrTemporalMaxwellRealMode_magnetic
    (κ Ω : PTRTemporalMaxwellPositive) (u₀ : PTRTemporalMaxwellRealState) (t : ℝ) :
    deriv (fun τ => ptrTemporalMaxwellRealMode κ Ω u₀ τ 1) t =
      -(Ω : ℝ) * (κ : ℝ) * ptrTemporalMaxwellRealMode κ Ω u₀ t 0 := by
  have hphase : HasDerivAt (fun τ : ℝ => (Ω : ℝ) * τ) (Ω : ℝ) t := by
    simpa using (hasDerivAt_id t).const_mul (Ω : ℝ)
  have hcos := (Real.hasDerivAt_cos ((Ω : ℝ) * t)).comp t hphase
  have hsin := (Real.hasDerivAt_sin ((Ω : ℝ) * t)).comp t hphase
  have hsum := ((hsin.neg).mul_const ((κ : ℝ) * u₀ 0)).add
    (hcos.mul_const (u₀ 1))
  have hκ : (κ : ℝ) ≠ 0 := ne_of_gt κ.property
  have hstate0 : ptrTemporalMaxwellRealMode κ Ω u₀ t 0 =
      Real.cos ((Ω : ℝ) * t) * u₀ 0 +
        Real.sin ((Ω : ℝ) * t) / (κ : ℝ) * u₀ 1 := by
    simp [ptrTemporalMaxwellRealMode, ptrTemporalMaxwellRealFlow,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hstate1 (τ : ℝ) : ptrTemporalMaxwellRealMode κ Ω u₀ τ 1 =
      -Real.sin ((Ω : ℝ) * τ) * (κ : ℝ) * u₀ 0 +
        Real.cos ((Ω : ℝ) * τ) * u₀ 1 := by
    simp [ptrTemporalMaxwellRealMode, ptrTemporalMaxwellRealFlow,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [show (fun τ => ptrTemporalMaxwellRealMode κ Ω u₀ τ 1) =
      (fun τ => -Real.sin ((Ω : ℝ) * τ) * (κ : ℝ) * u₀ 0 +
        Real.cos ((Ω : ℝ) * τ) * u₀ 1) from funext hstate1]
  have hfun :
      ((fun y => (-Real.sin ∘ HMul.hMul (Ω : ℝ)) y * ((κ : ℝ) * u₀ 0)) +
        fun y => (Real.cos ∘ HMul.hMul (Ω : ℝ)) y * u₀ 1) =
      (fun τ => -Real.sin ((Ω : ℝ) * τ) * (κ : ℝ) * u₀ 0 +
        Real.cos ((Ω : ℝ) * τ) * u₀ 1) := by
    funext τ
    change -Real.sin ((Ω : ℝ) * τ) * ((κ : ℝ) * u₀ 0) +
      Real.cos ((Ω : ℝ) * τ) * u₀ 1 =
      -Real.sin ((Ω : ℝ) * τ) * (κ : ℝ) * u₀ 0 +
        Real.cos ((Ω : ℝ) * τ) * u₀ 1
    ring
  rw [← hfun, hsum.deriv, hstate0]
  field_simp [hκ]
  ring

/-- Complexifying the real physical propagator is exactly the existing PTR oscillator flow. -/
theorem ptrTemporalMaxwellRealFlow_complexification
    (κ Ω : PTRTemporalMaxwellPositive) (t : ℝ) :
    (fun i j => (ptrTemporalMaxwellRealFlow κ Ω t i j : ℂ)) =
      photonicDrivenOscillatorFlow ((κ : ℝ) : ℂ) (Ω : ℝ) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptrTemporalMaxwellRealFlow, photonicDrivenOscillatorFlow,
      photonicOscillatorFlow]

/-- Positive permeability of the temporal magnetodielectric material. -/
noncomputable def ptrTemporalMaxwellPermeability
    (κ : PTRTemporalMaxwellPositive) : ℝ := κ

/-- Positive permittivity of the temporal magnetodielectric material. -/
noncomputable def ptrTemporalMaxwellPermittivity
    (κ : PTRTemporalMaxwellPositive) : ℝ := ((κ : ℝ) : ℝ)⁻¹

theorem ptrTemporalMaxwellPermeability_pos
    (κ : PTRTemporalMaxwellPositive) : 0 < ptrTemporalMaxwellPermeability κ := κ.property

theorem ptrTemporalMaxwellPermittivity_pos
    (κ : PTRTemporalMaxwellPositive) : 0 < ptrTemporalMaxwellPermittivity κ := by
  exact inv_pos.mpr κ.property

/-- The real state solves the source-free constant-material temporal Maxwell plane-wave equations. -/
theorem ptrTemporalMaxwellRealMode_solves_constitutive_plane_wave
    (κ Ω : PTRTemporalMaxwellPositive) (u₀ : PTRTemporalMaxwellRealState) (t : ℝ) :
    deriv (fun τ => ptrTemporalMaxwellRealMode κ Ω u₀ τ 0) t =
      (Ω : ℝ) / ptrTemporalMaxwellPermeability κ *
        ptrTemporalMaxwellRealMode κ Ω u₀ t 1 ∧
    deriv (fun τ => ptrTemporalMaxwellRealMode κ Ω u₀ τ 1) t =
      -(Ω : ℝ) / ptrTemporalMaxwellPermittivity κ *
        ptrTemporalMaxwellRealMode κ Ω u₀ t 0 := by
  constructor
  · exact deriv_ptrTemporalMaxwellRealMode_displacement κ Ω u₀ t
  · rw [deriv_ptrTemporalMaxwellRealMode_magnetic,
      ptrTemporalMaxwellPermittivity]
    have hκ : (κ : ℝ) ≠ 0 := ne_of_gt κ.property
    field_simp [hκ]

/-- Prime impedance as a positive physical material parameter. -/
noncomputable def photonicPrimeTemporalMaxwellImpedance
    (p : Nat.Primes) : PTRTemporalMaxwellPositive :=
  ⟨Real.log ((p : ℕ) : ℝ), Nat.Prime.log_pos p.property⟩

/-- Fourfold prime impedance for the first temporal slab. -/
noncomputable def photonicPrimeTemporalMaxwellQuadImpedance
    (p : Nat.Primes) : PTRTemporalMaxwellPositive :=
  ⟨4 * Real.log ((p : ℕ) : ℝ), mul_pos (by positivity) (Nat.Prime.log_pos p.property)⟩

/-- Positive physical prime-clock wavenumber/frequency. -/
noncomputable def photonicPrimeTemporalMaxwellRate
    (p : Nat.Primes) : PTRTemporalMaxwellPositive :=
  ⟨photonicPrimeDriveRate p, photonicPrimeDriveRate_pos p⟩

theorem photonicPrimeTemporalMaxwellImpedance_coe
    (p : Nat.Primes) : ((photonicPrimeTemporalMaxwellImpedance p : ℝ) : ℂ) =
      photonicPrimeImpedance p := by
  rfl

theorem photonicPrimeTemporalMaxwellQuadImpedance_coe
    (p : Nat.Primes) : ((photonicPrimeTemporalMaxwellQuadImpedance p : ℝ) : ℂ) =
      4 * photonicPrimeImpedance p := by
  simp [photonicPrimeTemporalMaxwellQuadImpedance, photonicPrimeImpedance]

theorem photonicPrimeTemporalMaxwellRate_coe
    (p : Nat.Primes) : (photonicPrimeTemporalMaxwellRate p : ℝ) = photonicPrimeDriveRate p := rfl

/-- Physical two-slab prime temporal-Maxwell transfer, with `D,B` continuous at the switch. -/
noncomputable def photonicPrimeTemporalMaxwellCyclicTransfer
    (p : Nat.Primes) : Matrix (Fin 2) (Fin 2) ℂ :=
  @HMul.hMul (Matrix (Fin 2) (Fin 2) ℂ) (Matrix (Fin 2) (Fin 2) ℂ)
    (Matrix (Fin 2) (Fin 2) ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
  ((fun i j => (ptrTemporalMaxwellRealFlow
    (photonicPrimeTemporalMaxwellQuadImpedance p)
    (photonicPrimeTemporalMaxwellRate p)
    (photonicPrimeSlabDuration p) i j : ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
  ((fun i j => (ptrTemporalMaxwellRealFlow
    (photonicPrimeTemporalMaxwellImpedance p)
    (photonicPrimeTemporalMaxwellRate p)
    (photonicPrimeSlabDuration p) i j : ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)

/-- The literal two-slab temporal-Maxwell transfer is exactly the prior PTR cyclic cell. -/
theorem photonicPrimeTemporalMaxwellCyclicTransfer_eq_primeCyclicTimeCrystalCell
    (p : Nat.Primes) : photonicPrimeTemporalMaxwellCyclicTransfer p =
      photonicPrimeCyclicTimeCrystalCell p := by
  unfold photonicPrimeTemporalMaxwellCyclicTransfer
  rw [ptrTemporalMaxwellRealFlow_complexification,
    ptrTemporalMaxwellRealFlow_complexification]
  rw [photonicPrimeTemporalMaxwellQuadImpedance_coe,
    photonicPrimeTemporalMaxwellImpedance_coe,
    photonicPrimeTemporalMaxwellRate_coe]
  unfold photonicPrimeCyclicTimeCrystalCell
  rfl

/-- Two literal prime temporal-Maxwell slab cycles realize the PTR parabolic transfer. -/
theorem photonicPrimeTemporalMaxwellCyclicTransfer_square_intertwines
    (p : Nat.Primes) : photonicPrimeTemporalMaxwellCyclicTransfer p ^ 2 *
        (photonicPrimeFrame p * photonicParabolicBasis) =
      (photonicPrimeFrame p * photonicParabolicBasis) * photonicParabolic := by
  rw [photonicPrimeTemporalMaxwellCyclicTransfer_eq_primeCyclicTimeCrystalCell]
  exact photonicPrimeCyclicTimeCrystalCell_square_intertwines p

end RHTower
