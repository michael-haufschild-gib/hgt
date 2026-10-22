import GaloisForLFunctions.RHTower.CCM.CCMEulerGammaRadonNikodym

/-!
# The Gamma-damped Cauchy carrier is a channel-resolved frame

Four exact mechanisms of the card are formalized, over the data of a pointed unitary system
`(H, U, ξ)` — a Hilbert space, a one-parameter group of unitaries and a unit vector — whose overlap
function is `φ`.

*The rank-one compression.*  `P_ξ U P_ξ = ⟪ξ, U ξ⟫ · P_ξ`, which is `(1)`; the overlap is the whole
compression.

*The canonical half-density.*  `d(t) = √(φ(2t))` squares back to `φ(2t)`, which is `(2)`–`(3)`.

*Channel norms and the additive trace.*  The synthesis column `a · d · U_t ξ` has squared norm
exactly `|a|² φ(2t)`, so the frame energy is the diagonal sum `(5)`/`(9)` with no cross-prime terms.

*Full Gamma covariance in the Gram.*  The Gram entry is
`conj(a_p) a_q d_p d_q φ(t_q - t_p)`, which is `(8)`: every off-diagonal prime interaction survives
in the operator even though the trace reads only the diagonal.

The exact prime diagonal `(10)` is `gammaDiagSq_eq` at `k = 1`, already proved for
`ccm-euler-gamma-radon-nikodym-frame-law`.  The existence of the archimedean cyclic measure with
characteristic function `(cosh t)^{-1/2}`, the Hilbert–Schmidt synthesis theorem and the trace-class
statements are cited parents.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

section PointedSystem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The rank-one projection onto `ℂ ξ` for a unit vector `ξ`. -/
def rankOneProj (ξ : H) (x : H) : H := (inner ℂ ξ x : ℂ) • ξ

theorem rankOneProj_idem {ξ : H} (hξ : ‖ξ‖ = 1) (x : H) :
    rankOneProj ξ (rankOneProj ξ x) = rankOneProj ξ x := by
  have hself : (inner ℂ ξ ξ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  simp only [rankOneProj, inner_smul_right, hself]
  rw [mul_one]

/-- **Equation (1).**  The compression of any operator to the pointed line is the scalar overlap
times the projection. -/
theorem rankOneProj_compression (ξ : H) (U : H →L[ℂ] H) (x : H) :
    rankOneProj ξ (U (rankOneProj ξ x)) = (inner ℂ ξ (U ξ) : ℂ) • rankOneProj ξ x := by
  simp only [rankOneProj, map_smul, inner_smul_right, smul_smul]
  ring_nf

/-! ## Channel norms -/

/-- **Equations (4)–(5), one channel.**  The squared norm of a synthesis column is exactly
`|a|² d²`. -/
theorem norm_sq_synthesis_column {ξ : H} (hξ : ‖ξ‖ = 1) {U : H →L[ℂ] H}
    (hU : ∀ x, ‖U x‖ = ‖x‖) (a : ℂ) (d : ℝ) :
    ‖a • (d : ℂ) • U ξ‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) * d ^ (2 : ℕ) := by
  rw [norm_smul, norm_smul, hU, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs]

/-- **Equation (9).**  The frame energy is the diagonal sum: no cross-channel terms appear. -/
theorem sum_norm_sq_synthesis {ι : Type*} (s : Finset ι) {ξ : H} (hξ : ‖ξ‖ = 1)
    {U : H →L[ℂ] H} (hU : ∀ x, ‖U x‖ = ‖x‖) (a : ι → ℂ) (d : ι → ℝ) :
    (∑ i ∈ s, ‖a i • ((d i : ℝ) : ℂ) • U ξ‖ ^ (2 : ℕ)) = ∑ i ∈ s, ‖a i‖ ^ (2 : ℕ) * (d i) ^ (2 : ℕ) :=
  Finset.sum_congr rfl fun i _ => norm_sq_synthesis_column hξ hU (a i) (d i)

/-! ## The Gram entry retains full covariance -/

/-- **Equation (8).**  The Gram entry of two synthesis columns keeps the complete group overlap. -/
theorem gram_entry_synthesis {ξ : H} {U : ℝ → (H →L[ℂ] H)}
    (hiso : ∀ (s : ℝ) (x y : H), (inner ℂ (U s x) (U s y) : ℂ) = inner ℂ x y)
    (hgroup : ∀ (s t : ℝ) (x : H), U t x = U s (U (t - s) x))
    (a b : ℂ) (c e : ℝ) (s t : ℝ) :
    (inner ℂ (a • (c : ℂ) • U s ξ) (b • (e : ℂ) • U t ξ) : ℂ)
      = (starRingEnd ℂ) a * b * (c : ℂ) * (e : ℂ) * (inner ℂ ξ (U (t - s) ξ) : ℂ) := by
  rw [inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right]
  rw [hgroup s t ξ, hiso s ξ (U (t - s) ξ)]
  simp only [Complex.conj_ofReal]
  ring

end PointedSystem

/-! ## The exact prime diagonal -/

/-- **Equation (10).**  The Gamma diagonal at a prime is `√2 p / √(p⁴+1)`. -/
theorem gammaDiagSq_prime {p : ℕ} (hp : 2 ≤ p) :
    gammaDiagSq p 1 = Real.sqrt 2 * (p : ℝ) / Real.sqrt ((p : ℝ) ^ (4 : ℕ) + 1) := by
  have h := gammaDiagSq_eq hp 1
  simpa using h

/-- The canonical half-density `d(t) = √(φ(2t))` of `(3)`. -/
def halfDensity (t : ℝ) : ℝ := Real.sqrt (gammaDampingProfile (2 * t))

theorem gammaDampingProfile_pos (t : ℝ) : 0 < gammaDampingProfile t := by
  rw [gammaDampingProfile_eq_inv_sqrt]
  have : 0 < Real.sqrt (Real.cosh t) := Real.sqrt_pos.mpr (Real.cosh_pos t)
  positivity

/-- **Equations (2)–(3).**  The half-density squares back to the overlap. -/
theorem halfDensity_sq (t : ℝ) : halfDensity t ^ (2 : ℕ) = gammaDampingProfile (2 * t) := by
  rw [halfDensity, Real.sq_sqrt (le_of_lt (gammaDampingProfile_pos _))]

theorem halfDensity_pos (t : ℝ) : 0 < halfDensity t :=
  Real.sqrt_pos.mpr (gammaDampingProfile_pos _)

/-- **Equation (5).**  The channel energy of the Gamma-damped Cauchy packet is the diagonal sum of
`φ(2 t_i) |a_i|²`. -/
theorem sum_channel_energy {ι : Type*} (s : Finset ι) (a : ι → ℂ) (t : ι → ℝ) :
    (∑ i ∈ s, ‖a i‖ ^ (2 : ℕ) * (halfDensity (t i)) ^ (2 : ℕ))
      = ∑ i ∈ s, ‖a i‖ ^ (2 : ℕ) * gammaDampingProfile (2 * t i) :=
  Finset.sum_congr rfl fun i _ => by rw [halfDensity_sq]

end GaloisForLFunctions.RHTower

end
