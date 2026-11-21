import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.DampedGapResponse
import GaloisForLFunctions.HTGeometry.CaratheodoryKernelPositive
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant
import Mathlib.Analysis.Matrix.Order

/-!
# The Abel dephasing channel

At frequency zero the damped Hamiltonian response is Schur multiplication
by a normalized half-plane Cauchy matrix. Its nodes have common real part
equal to half the damping width and imaginary parts given by the energies.
-/

open Matrix Set
open scoped Matrix ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The complex attenuation at an energy difference. -/
def abelCoherence (ε : Ioi (0 : ℝ)) (g : ℝ) : ℂ :=
  ((ε : ℝ) : ℂ) / (⟨(ε : ℝ), g⟩ : ℂ)

private theorem abelDenominator_ne_zero (ε : Ioi (0 : ℝ)) (g : ℝ) :
    (⟨(ε : ℝ), g⟩ : ℂ) ≠ 0 := by
  intro h
  exact (show 0 < (ε : ℝ) from ε.2).ne' (congrArg Complex.re h)

theorem abelCoherence_eq_one_iff (ε : Ioi (0 : ℝ)) (g : ℝ) :
    abelCoherence ε g = 1 ↔ g = 0 := by
  rw [abelCoherence, div_eq_one_iff_eq (abelDenominator_ne_zero ε g)]
  constructor
  · intro h
    exact (congrArg Complex.im h).symm
  · rintro rfl
    rfl

theorem abelCoherence_zero (ε : Ioi (0 : ℝ)) : abelCoherence ε 0 = 1 :=
  (abelCoherence_eq_one_iff ε 0).mpr rfl

theorem norm_sq_abelCoherence (ε : Ioi (0 : ℝ)) (g : ℝ) :
    ‖abelCoherence ε g‖ ^ 2 = (ε : ℝ) ^ 2 / ((ε : ℝ) ^ 2 + g ^ 2) := by
  rw [abelCoherence, Complex.sq_norm, Complex.normSq_div, Complex.normSq_ofReal,
    Complex.normSq_apply]
  change ((ε : ℝ) * (ε : ℝ)) / ((ε : ℝ) * (ε : ℝ) + g * g) = _
  rw [pow_two, pow_two]

theorem abelCoherence_im (ε : Ioi (0 : ℝ)) (g : ℝ) :
    (abelCoherence ε g).im = -((ε : ℝ) * g / ((ε : ℝ) ^ 2 + g ^ 2)) := by
  rw [abelCoherence, Complex.div_im, Complex.ofReal_im, Complex.ofReal_re, Complex.normSq_apply]
  change (0 : ℝ) * (ε : ℝ) / _ - (ε : ℝ) * g / ((ε : ℝ) * (ε : ℝ) + g * g) = _
  rw [zero_mul, zero_div, zero_sub, pow_two, pow_two]

private def abelNode (ε : Ioi (0 : ℝ)) (e : ℝ) : ℂ := ⟨(ε : ℝ) / 2, e⟩

private theorem abelNode_add_star (ε : Ioi (0 : ℝ)) (e f : ℝ) :
    abelNode ε e + star (abelNode ε f) = (⟨(ε : ℝ), e - f⟩ : ℂ) := by
  apply Complex.ext
  · change (ε : ℝ) / 2 + (ε : ℝ) / 2 = (ε : ℝ)
    ring
  · change e + -f = e - f
    rw [sub_eq_add_neg]

/-- Normalized Cauchy matrix of the energy nodes. -/
def abelEnergySymbol {n : ℕ} (ε : Ioi (0 : ℝ)) (E : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => abelCoherence ε (E i - E j)

theorem abelEnergySymbol_posSemidef {n : ℕ} (ε : Ioi (0 : ℝ)) (E : Fin n → ℝ) :
    (abelEnergySymbol ε E).PosSemidef := by
  let u (i : Fin n) := abelNode ε (E i)
  let c : ℂ := (((ε : ℝ) / 2 : ℝ) : ℂ)
  have hε : 0 < (ε : ℝ) := ε.2
  have hp := posSemidef_halfPlaneCaratheodoryGram (F := fun _ => c)
    (fun _ _ => differentiableAt_const c) (fun _ _ => (half_pos hε).le) u (fun _ => half_pos hε)
  have he : (Matrix.of fun i j => (c + (starRingEnd ℂ) c) /
      (u i + (starRingEnd ℂ) (u j))) = abelEnergySymbol ε E := by
    ext i j
    change (c + (starRingEnd ℂ) c) / (abelNode ε (E i) + star (abelNode ε (E j))) =
      abelCoherence ε (E i - E j)
    rw [abelNode_add_star, abelCoherence]
    have hc : c + (starRingEnd ℂ) c = ((ε : ℝ) : ℂ) := by
      dsimp only [c]
      rw [Complex.conj_ofReal, ← Complex.ofReal_add]
      congr 1
      ring
    rw [hc]
  rw [← he]
  exact hp

/-- The symbol is strictly positive exactly when the energy nodes are
pairwise distinct. -/
theorem abelEnergySymbol_posDef_iff {n : ℕ} (ε : Ioi (0 : ℝ)) (E : Fin n → ℝ) :
    (abelEnergySymbol ε E).PosDef ↔ Function.Injective E := by
  rw [(abelEnergySymbol_posSemidef ε E).posDef_iff_det_ne_zero]
  constructor
  · intro h i j he
    by_contra hij
    apply h
    exact Matrix.det_zero_of_row_eq hij (funext fun k => by
      simp only [abelEnergySymbol, Matrix.of_apply, he])
  · intro hE
    let u (i : Fin n) := abelNode ε (E i)
    have hu : Function.Injective u := fun _ _ hij => hE (congrArg Complex.im hij)
    have hv : Function.Injective (fun j => star (u j)) := star_involutive.injective.comp hu
    have hd (i j : Fin n) : u i + star (u j) ≠ 0 := by
      change abelNode ε (E i) + star (abelNode ε (E j)) ≠ 0
      rw [abelNode_add_star]
      exact abelDenominator_ne_zero ε _
    have hprod : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (u i - u j) * (star (u i) - star (u j))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have hij := ne_of_lt (Finset.mem_Ioi.mp hj)
      exact mul_ne_zero (sub_ne_zero.mpr (fun h => hij (hu h)))
        (sub_ne_zero.mpr (fun h => hij (hv h)))
    have hdet : (cauchyMatrix u (fun j => star (u j))).det ≠ 0 := by
      intro h
      have he := det_cauchyMatrix u (fun j => star (u j)) hd
      rw [h, zero_mul] at he
      exact hprod he.symm
    have hsymb : abelEnergySymbol ε E = ((ε : ℝ) : ℂ) • cauchyMatrix u (fun j => star (u j)) := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, cauchyMatrix_apply]
      change abelCoherence ε (E i - E j) =
        ((ε : ℝ) : ℂ) * (abelNode ε (E i) + star (abelNode ε (E j)))⁻¹
      rw [abelNode_add_star, abelCoherence, div_eq_mul_inv]
    rw [hsymb, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (show 0 < (ε : ℝ) from ε.2).ne')) hdet

/-- The zero-centered Abel filter in energy coordinates. -/
def abelEnergyChannel {n : ℕ} (ε : Ioi (0 : ℝ)) (E : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  abelEnergySymbol ε E ⊙ X

theorem abelEnergyChannel_posSemidef {n : ℕ} (ε : Ioi (0 : ℝ)) (E : Fin n → ℝ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.PosSemidef) :
    (abelEnergyChannel ε E X).PosSemidef :=
  (abelEnergySymbol_posSemidef ε E).hadamard hX

theorem abelEnergyChannel_fixed_iff {n : ℕ} (ε : Ioi (0 : ℝ)) (E : Fin n → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    abelEnergyChannel ε E X = X ↔ ∀ i j, E i ≠ E j → X i j = 0 := by
  constructor
  · intro h i j hij
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h
    change abelCoherence ε (E i - E j) * X i j = X i j at he
    have hz : (abelCoherence ε (E i - E j) - 1) * X i j = 0 := by
      rw [sub_mul, he, one_mul, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr fun hq =>
      hij (sub_eq_zero.mp ((abelCoherence_eq_one_iff ε _).mp hq)))
  · intro h
    ext i j
    change abelCoherence ε (E i - E j) * X i j = X i j
    by_cases hij : E i = E j
    · rw [hij, sub_self, abelCoherence_zero, one_mul]
    · rw [h i j hij, mul_zero]

/-- Rotation by `i` puts the damped Green denominator in Cauchy form. -/
theorem dampedGapScalar_eq_abelCoherence (ε : Ioi (0 : ℝ)) (μ g : ℝ) (a : ℂ) :
    ((μ : ℂ) - ⟨μ, (ε : ℝ)⟩) * (((g : ℂ) - ⟨μ, (ε : ℝ)⟩)⁻¹ * a) =
      abelCoherence ε (g - μ) * a := by
  let p : ℂ := (μ : ℂ) - ⟨μ, (ε : ℝ)⟩
  let d : ℂ := (g : ℂ) - ⟨μ, (ε : ℝ)⟩
  let q : ℂ := ⟨(ε : ℝ), g - μ⟩
  have hrot : Complex.I * d = q := by
    apply Complex.ext <;> simp [d, q, Complex.mul_re, Complex.mul_im]
  have hnum : Complex.I * p = ((ε : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [p, Complex.mul_re, Complex.mul_im]
  have hqn : q ≠ 0 := abelDenominator_ne_zero ε _
  have hdn : d ≠ 0 := fun h => hqn (by rw [← hrot, h, mul_zero])
  change p * (d⁻¹ * a) = ((ε : ℝ) : ℂ) / q * a
  rw [← mul_assoc, ← div_eq_mul_inv]
  congr 1
  apply (div_eq_div_iff hdn hqn).mpr
  rw [← hrot, ← hnum]
  ring

variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ}

theorem energyCoordinates_dampedGapResponse_apply_coherence
    (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH μ ε X) i j =
      abelCoherence ε (hamiltonianGap hH i j - μ) * hamiltonianEnergyCoordinates hH X i j := by
  rw [energyCoordinates_dampedGapResponse_apply, dampedGapScalar_eq_abelCoherence]

/-- The zero-frequency Green filter is the normalized Cauchy Schur map. -/
theorem energyCoordinates_dampedGapResponse_zero_eq_abelEnergyChannel
    (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) (X : Matrix (Fin n) (Fin n) ℂ) :
    hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH 0 ε X) =
      abelEnergyChannel ε hH.eigenvalues (hamiltonianEnergyCoordinates hH X) := by
  ext i j
  simp only [energyCoordinates_dampedGapResponse_apply_coherence, sub_zero, hamiltonianGap,
    abelEnergyChannel, Matrix.hadamard_apply, abelEnergySymbol, Matrix.of_apply]

private theorem trace_energyCoordinates (hH : H.IsHermitian) (X : Matrix (Fin n) (Fin n) ℂ) :
    (hamiltonianEnergyCoordinates hH X).trace = X.trace := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  change (star U * X * U).trace = _
  rw [Matrix.trace_mul_comm (star U * X) U, ← Matrix.mul_assoc,
    show U * star U = 1 from Unitary.coe_mul_star_self hH.eigenvectorUnitary, Matrix.one_mul]

/-- Any center scales the trace by its attenuation at the zero Bohr
frequency. The physical channel is trace preserving at center zero. -/
theorem trace_hamiltonianDampedGapResponse (hH : H.IsHermitian) (μ : ℝ)
    (ε : Ioi (0 : ℝ)) (X : Matrix (Fin n) (Fin n) ℂ) :
    (hamiltonianDampedGapResponse hH μ ε X).trace = abelCoherence ε (-μ) * X.trace := by
  rw [← trace_energyCoordinates hH (hamiltonianDampedGapResponse hH μ ε X),
    ← trace_energyCoordinates hH X, Matrix.trace, Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, energyCoordinates_dampedGapResponse_apply_coherence,
    hamiltonianGap, sub_self, zero_sub]

theorem hamiltonianDampedGapResponse_one_eq (hH : H.IsHermitian) (μ : ℝ) (ε : Ioi (0 : ℝ)) :
    hamiltonianDampedGapResponse hH μ ε 1 =
      abelCoherence ε (-μ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine (hamiltonianEnergyCoordinates hH).injective (?_ :
    hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH μ ε 1) =
      hamiltonianEnergyCoordinates hH (abelCoherence ε (-μ) • 1))
  ext i j
  rw [energyCoordinates_dampedGapResponse_apply_coherence, map_smul, Matrix.smul_apply,
    map_one, smul_eq_mul]
  by_cases h : i = j
  · subst j
    simp only [hamiltonianGap, sub_self, zero_sub]
  · rw [Matrix.one_apply_ne h, mul_zero, mul_zero]

/-- At zero frequency the response fixes precisely the commutant of the
Hamiltonian, including full degenerate energy blocks. -/
theorem hamiltonianDampedGapResponse_zero_fixed_iff (hH : H.IsHermitian) (ε : Ioi (0 : ℝ))
    (X : Matrix (Fin n) (Fin n) ℂ) :
    hamiltonianDampedGapResponse hH 0 ε X = X ↔ H * X = X * H := by
  rw [← hamiltonianGapComponent_zero_eq_self_iff hH]
  have hchannel :
      hamiltonianDampedGapResponse hH 0 ε X = X ↔
        ∀ i j, hH.eigenvalues i ≠ hH.eigenvalues j →
          hamiltonianEnergyCoordinates hH X i j = 0 := by
    rw [← (hamiltonianEnergyCoordinates hH).injective.eq_iff]
    change hamiltonianEnergyCoordinates hH (hamiltonianDampedGapResponse hH 0 ε X) =
      hamiltonianEnergyCoordinates hH X ↔ _
    rw [energyCoordinates_dampedGapResponse_zero_eq_abelEnergyChannel, abelEnergyChannel_fixed_iff]
  rw [hchannel]
  constructor
  · intro he
    refine (hamiltonianEnergyCoordinates hH).injective (?_ :
      hamiltonianEnergyCoordinates hH (hamiltonianGapComponent hH 0 X) =
        hamiltonianEnergyCoordinates hH X)
    ext i j
    rw [energyCoordinates_gapComponent_apply]
    by_cases hij : hH.eigenvalues i = hH.eigenvalues j
    · simp only [hamiltonianGap, hij, sub_self, if_true]
    · have hg : hamiltonianGap hH i j ≠ 0 := sub_ne_zero.mpr hij
      rw [if_neg hg, he i j hij]
  · intro he i j hij
    have hh := congrArg (fun M => hamiltonianEnergyCoordinates hH M i j) he
    have hg : hamiltonianGap hH i j ≠ 0 := sub_ne_zero.mpr hij
    rw [energyCoordinates_gapComponent_apply, if_neg hg] at hh
    exact hh.symm

#print axioms abelEnergySymbol_posDef_iff
#print axioms abelEnergyChannel_posSemidef
#print axioms energyCoordinates_dampedGapResponse_zero_eq_abelEnergyChannel
#print axioms trace_hamiltonianDampedGapResponse
#print axioms hamiltonianDampedGapResponse_zero_fixed_iff

end

end GaloisForLFunctions.HTGeometry
