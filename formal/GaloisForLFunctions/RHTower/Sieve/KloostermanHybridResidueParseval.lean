import GaloisForLFunctions.RHTower.Sieve.KloostermanHybridLargeSieve

/-!
# Exact residue Parseval laws for the hybrid Kloosterman transform

The additive Fourier input to `kloostermanHybridTransform` is itself the Fourier
transform of the physical residue-class Dirichlet polynomials.  Character
orthogonality therefore identifies every unit Fourier coefficient exactly with
one physical residue class.  Combining this identity with Kloosterman Parseval
removes all nonunit residue classes without an inequality loss.

This is the exact finite bridge needed before any modulus or spectral averaging;
it does not assert the Deshouillers--Iwaniec spectral estimate.
-/

open Complex MeasureTheory Set Finset

noncomputable section

namespace RHTower.Sieve

/-- Dirichlet polynomial supported on one physical residue class modulo `q + 1`. -/
def physicalResidueDirichletPoly (q N : ℕ) (a : ℕ → ℂ)
    (r : ZMod (q + 1)) (t : ℝ) : ℂ :=
  logPoly a (additiveResidueInterval q N r) (t / (2 * Real.pi))

theorem continuous_physicalResidueDirichletPoly
    (q N : ℕ) (a : ℕ → ℂ) (r : ZMod (q + 1)) :
    Continuous (physicalResidueDirichletPoly q N a r) := by
  unfold physicalResidueDirichletPoly
  exact (continuous_logPoly a (additiveResidueInterval q N r)).comp (by fun_prop)

/-- Fourier inversion through the additive hybrid input: a unit-frequency
coefficient is exactly `(q + 1)` times the opposite physical residue class. -/
theorem kloostermanUnitFourierCoeff_additiveHybrid_eq
    (q N : ℕ) (a : ℕ → ℂ) (x : (ZMod (q + 1))ˣ) (t : ℝ) :
    kloostermanUnitFourierCoeff (q + 1)
        (fun d : ZMod (q + 1) => additiveHybridDirichletPoly q N a d t) x =
      ((q + 1 : ℕ) : ℂ) *
        physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t := by
  letI : NeZero (q + 1) := ⟨by omega⟩
  unfold kloostermanUnitFourierCoeff additiveHybridDirichletPoly
    physicalResidueDirichletPoly
  simp_rw [additiveHybridLogPoly_eq_sum_residues]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hdiag :
      (∑ d : ZMod (q + 1),
          ZMod.stdAddChar (d * (-(x : ZMod (q + 1)))) *
            ZMod.stdAddChar (d * (x : ZMod (q + 1)))) = ((q + 1 : ℕ) : ℂ) := by
    convert sum_stdAddChar_mul (q + 1)
        ((-(x : ZMod (q + 1))) + (x : ZMod (q + 1))) using 1 <;>
      simp only [neg_add_cancel, if_pos]
    apply Finset.sum_congr rfl
    intro d _
    rw [← AddChar.map_add_eq_mul]
    congr 2
    ring_nf
  rw [← hdiag]
  calc
    _ = logPoly a (additiveResidueInterval q N (-(x : ZMod (q + 1))))
          (t / (2 * Real.pi)) *
        ∑ d : ZMod (q + 1),
          ZMod.stdAddChar (d * (-(x : ZMod (q + 1)))) *
            ZMod.stdAddChar (d * (x : ZMod (q + 1))) := by
      apply Fintype.sum_eq_single (-(x : ZMod (q + 1)))
      intro r hr
      have hne : r + (x : ZMod (q + 1)) ≠ 0 := by
        intro h
        apply hr
        exact eq_neg_of_add_eq_zero_left h
      rw [show (∑ d : ZMod (q + 1),
            ZMod.stdAddChar (d * r) * ZMod.stdAddChar (d * (x : ZMod (q + 1)))) = 0 by
        calc
          _ = ∑ d : ZMod (q + 1),
              ZMod.stdAddChar (d * (r + (x : ZMod (q + 1)))) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [mul_add, AddChar.map_add_eq_mul]
          _ = 0 := by
            simpa [hne] using
              sum_stdAddChar_mul (q + 1) (r + (x : ZMod (q + 1)))]
      simp
    _ = _ := mul_comm _ _

/-- Exact hybrid Kloosterman energy law.  Its output energy is supported only
on unit physical residue classes, with the exact factor `(q + 1)^(3 : ℕ)`. -/
theorem sum_normSq_kloostermanHybridTransform_eq_unitResidueEnergy
    (q N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ∑ n : ZMod (q + 1), Complex.normSq (kloostermanHybridTransform q N a n t) =
      (((q + 1 : ℕ) : ℝ) ^ 3) *
        ∑ x : (ZMod (q + 1))ˣ,
          Complex.normSq
            (physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t) := by
  letI : NeZero (q + 1) := ⟨by omega⟩
  rw [show (∑ n : ZMod (q + 1), Complex.normSq
      (kloostermanHybridTransform q N a n t)) =
      ((q + 1 : ℕ) : ℝ) * ∑ x : (ZMod (q + 1))ˣ,
        Complex.normSq (kloostermanUnitFourierCoeff (q + 1)
          (fun d : ZMod (q + 1) => additiveHybridDirichletPoly q N a d t) x) by
    simpa only [kloostermanHybridTransform] using
      sum_normSq_kloostermanTransform_eq_unitEnergy (q + 1)
        (fun d : ZMod (q + 1) => additiveHybridDirichletPoly q N a d t)]
  simp_rw [kloostermanUnitFourierCoeff_additiveHybrid_eq]
  simp only [Complex.normSq_eq_norm_sq, norm_mul, norm_natCast, Finset.mul_sum]
  ring_nf

/-- The pointwise Kloosterman/residue Parseval law integrated over a symmetric physical-height
window.  Finite summation and integration commute exactly on both sides. -/
theorem sum_integral_normSq_kloostermanHybridTransform_eq_unitResidueEnergy
    (q N : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    ∑ n : ZMod (q + 1),
        (∫ t in Set.Icc (-T) T,
          ‖kloostermanHybridTransform q N a n t‖ ^ 2) =
      (((q + 1 : ℕ) : ℝ) ^ 3) *
        ∑ x : (ZMod (q + 1))ˣ,
          (∫ t in Set.Icc (-T) T,
            ‖physicalResidueDirichletPoly q N a
              (-(x : ZMod (q + 1))) t‖ ^ 2) := by
  let I : Set ℝ := Set.Icc (-T) T
  have hout : ∀ n : ZMod (q + 1),
      Integrable (fun t => ‖kloostermanHybridTransform q N a n t‖ ^ 2)
        (volume.restrict I) := by
    intro n
    exact (continuous_kloostermanHybridTransform q N a n).norm.pow 2 |>.integrableOn_Icc
  have hin : ∀ x : (ZMod (q + 1))ˣ,
      Integrable (fun t => ‖physicalResidueDirichletPoly q N a
        (-(x : ZMod (q + 1))) t‖ ^ 2) (volume.restrict I) := by
    intro x
    exact (continuous_physicalResidueDirichletPoly q N a
      (-(x : ZMod (q + 1)))).norm.pow 2 |>.integrableOn_Icc
  rw [← MeasureTheory.integral_finsetSum Finset.univ (fun n _ => hout n)]
  change (∫ t in I, ∑ n : ZMod (q + 1),
      ‖kloostermanHybridTransform q N a n t‖ ^ 2) = _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun t _ => by
    simpa only [Complex.normSq_eq_norm_sq] using
      sum_normSq_kloostermanHybridTransform_eq_unitResidueEnergy q N a t)]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun x _ => hin x)]

end RHTower.Sieve
