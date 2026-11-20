import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius
import GaloisForLFunctions.HTGeometry.OperatorCertificateGenealogy
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Equal-multiplicity compression of an autonomous unitary orbit

Sorting the energies once defines a tensor identification and a reduced
Hamiltonian. Every retained level has exactly the same spectator multiplicity.
The squared Hilbert–Schmidt error per level on a finite time interval is
controlled by the time-bandwidth product divided by the retained dimension.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem sum_blockWidths (b : ℕ → ℝ) (k : ℕ) :
    ∑ i : Fin k, (b (i.val + 1) - b i.val) = b k - b 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    ring

/-- One change of energy coordinates and one reduced Hamiltonian work at every
time. The unnormalized squared chord error is at most twice spectator
multiplicity times elapsed time times spectral width. -/
theorem exists_equalMultiplicity_spectralSimulation
    (k m : ℕ) (energy : Fin (k * m) → ℝ) (lo hi : ℝ)
    (hb : ∀ j, lo ≤ energy j ∧ energy j ≤ hi) (hwidth : lo ≤ hi) :
    ∃ (e : Fin k × Fin m ≃ Fin (k * m)) (reduced : Fin k → ℝ),
      ∀ t : ℝ, ∑ i : Fin k, ∑ j : Fin m,
        ‖Complex.exp (((t * energy (e (i,j)) : ℝ) : ℂ) * Complex.I) -
         Complex.exp (((t * reduced i : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
          2 * (m : ℝ) * |t| * (hi - lo) := by
  let p := Tuple.sort energy
  let f (s : ℕ) : ℝ := if h : s < k * m then energy (p ⟨s, h⟩) else hi
  have hf : Monotone f := by
    intro a b hab
    by_cases ha : a < k * m
    · by_cases hb' : b < k * m
      · dsimp only [f]
        rw [dif_pos ha, dif_pos hb']
        exact
          (Tuple.monotone_sort energy (show (⟨a, ha⟩ : Fin (k*m)) ≤ ⟨b, hb'⟩ from hab))
      · simpa only [f, dif_pos ha, dif_neg hb'] using (hb (p ⟨a, ha⟩)).2
    · have hb' : ¬ b < k * m := fun h => ha (lt_of_le_of_lt hab h)
      simp only [f, dif_neg ha, dif_neg hb', le_refl]
  let b (s : ℕ) := f (m * s)
  let e := (finProdFinEquiv (m := k) (n := m)).trans p
  refine ⟨e, fun i => b i.val, fun t => ?_⟩
  have hterm (i : Fin k) (j : Fin m) :
      ‖Complex.exp (((t * energy (e (i,j)) : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((t * b i.val : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        2 * |t| * (b (i.val + 1) - b i.val) := by
    have hidx := (finProdFinEquiv (i,j)).isLt
    change j.val + m * i.val < k * m at hidx
    have he : energy (e (i,j)) = f (j.val + m * i.val) := by
      simp only [f, dif_pos hidx]
      rfl
    have hlo : b i.val ≤ energy (e (i,j)) := by
      rw [he]
      exact hf (Nat.le_add_left _ _)
    have hhi : energy (e (i,j)) ≤ b (i.val + 1) := by
      rw [he]
      apply hf
      rw [Nat.mul_succ]
      omega
    let x := Complex.exp (((t * energy (e (i,j)) : ℝ) : ℂ) * Complex.I)
    let y := Complex.exp (((t * b i.val : ℝ) : ℂ) * Complex.I)
    have htwo : ‖x - y‖ ≤ 2 := by
      calc
        ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ = 2 := by
          rw [show ‖x‖ = 1 from Complex.norm_exp_ofReal_mul_I _,
            show ‖y‖ = 1 from Complex.norm_exp_ofReal_mul_I _]
          norm_num
    have hchord : ‖x - y‖ ≤ |t| * (b (i.val + 1) - b i.val) := by
      have h := norm_expI_sub_expI_le (t * energy (e (i,j))) (t * b i.val) 0
      simp only [Int.cast_zero, mul_zero, sub_zero, ← mul_sub, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hlo)] at h
      exact h.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hhi _) (abs_nonneg _))
    calc
      ‖x - y‖ ^ 2 = ‖x - y‖ * ‖x - y‖ := sq _
      _ ≤ 2 * (|t| * (b (i.val + 1) - b i.val)) :=
        mul_le_mul htwo hchord (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have htotal : ∑ i : Fin k, (b (i.val+1) - b i.val) ≤ hi - lo := by
    rw [sum_blockWidths]
    have htop : b k = hi := by simp [b, f, Nat.mul_comm m k]
    have hbot : lo ≤ b 0 := by
      simp only [b, Nat.mul_zero, f]
      split
      · exact (hb _).1
      · exact hwidth
    rw [htop]
    exact sub_le_sub_left hbot _
  calc
    _ ≤ ∑ i : Fin k, ∑ _j : Fin m, 2 * |t| * (b (i.val+1) - b i.val) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (2 * (m : ℝ) * |t|) * ∑ i : Fin k, (b (i.val+1) - b i.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal (by positivity)

/-- Lift the reduced diagonal Hamiltonian to the original energy basis. Each
retained energy occurs once for every value of the spectator coordinate. -/
def spectralBlockLift {k m : ℕ} (H : Matrix (Fin (k*m)) (Fin (k*m)) ℂ)
    (hH : H.IsHermitian) (e : Fin k × Fin m ≃ Fin (k*m)) (K : Fin k → ℝ) :=
  (hH.eigenvectorUnitary : Matrix _ _ ℂ) *
    Matrix.diagonal (fun x => (K (e.symm x).1 : ℂ)) *
    star (hH.eigenvectorUnitary : Matrix _ _ ℂ)

private theorem hsSq_diagonal (d : ℕ) (v : Fin d → ℂ) :
    hsSq (Matrix.diagonal v) = ∑ i, ‖v i‖ ^ 2 := by
  classical
  simp [hsSq, Matrix.diagonal, apply_ite]

private theorem hsSq_conj_diagonal_difference {d : ℕ}
    (V : Matrix.unitaryGroup (Fin d) ℂ) (u v : Fin d → ℂ) :
    hsSq ((V : Matrix _ _ ℂ) * Matrix.diagonal u * star (V : Matrix _ _ ℂ) -
      (V : Matrix _ _ ℂ) * Matrix.diagonal v * star (V : Matrix _ _ ℂ)) =
      ∑ x, ‖u x - v x‖ ^ 2 := by
  rw [← sub_mul, ← mul_sub, Matrix.diagonal_sub]
  exact (hsSq_unitary_mul_star (fun _ => (V : Matrix _ _ ℂ)) (fun _ => V.2)
    0 0 (Matrix.diagonal (fun x => u x - v x))).trans (hsSq_diagonal d _)

private theorem schrodingerPhase_eq (t x : ℝ) :
    Complex.exp (-(Complex.I * ((t : ℂ) * (x : ℂ)))) =
      Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) := by
  congr 1
  push_cast
  ring

private theorem hsSq_blockLift_eq {k m : ℕ} (H : Matrix (Fin (k*m)) (Fin (k*m)) ℂ)
    (hH : H.IsHermitian) (e : Fin k × Fin m ≃ Fin (k*m)) (K : Fin k → ℝ) (t : ℝ) :
    hsSq (unitaryEvolution H t - unitaryEvolution (spectralBlockLift H hH e K) t) =
      ∑ i : Fin k, ∑ j : Fin m,
        ‖Complex.exp (((-t * hH.eigenvalues (e (i,j)) : ℝ) : ℂ) * Complex.I) -
         Complex.exp (((-t * K i : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  rw [unitaryEvolution_spectral hH t, spectralBlockLift,
    unitaryEvolution_conj_diagonal _ hH.eigenvectorUnitary.2]
  let u (x : Fin (k*m)) := Complex.exp (-(Complex.I * ((t : ℂ) * hH.eigenvalues x)))
  let v (x : Fin (k*m)) := Complex.exp (-(Complex.I * ((t : ℂ) * K (e.symm x).1)))
  rw [hsSq_conj_diagonal_difference hH.eigenvectorUnitary u v]
  calc
    _ = ∑ ij : Fin k × Fin m, ‖u (e ij) - v (e ij)‖ ^ 2 :=
      (Equiv.sum_comp e (fun x => ‖u x - v x‖ ^ 2)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [u, v, Equiv.symm_apply_apply, schrodingerPhase_eq]

/-- Every finite Hamiltonian has a single autonomous equal-multiplicity
simulator; the estimate applies to its actual matrix evolution at every time. -/
theorem exists_equalMultiplicity_hamiltonianSimulation
    (k m : ℕ) (H : Matrix (Fin (k*m)) (Fin (k*m)) ℂ) (hH : H.IsHermitian) :
    ∃ (e : Fin k × Fin m ≃ Fin (k*m)) (K : Fin k → ℝ),
      ∀ t : ℝ, hsSq (unitaryEvolution H t -
        unitaryEvolution (spectralBlockLift H hH e K) t) ≤
        4 * (m : ℝ) * |t| * ‖hH.eigenvalues‖ := by
  let E := hH.eigenvalues
  have hb (j : Fin (k*m)) : -‖E‖ ≤ E j ∧ E j ≤ ‖E‖ :=
    abs_le.mp (norm_le_pi_norm E j)
  obtain ⟨e, K, h⟩ := exists_equalMultiplicity_spectralSimulation k m E
    (-‖E‖) ‖E‖ hb (by linarith only [norm_nonneg E])
  refine ⟨e, K, fun t => ?_⟩
  rw [hsSq_blockLift_eq H hH e K t]
  apply (h (-t)).trans
  rw [abs_neg]
  exact le_of_eq (by change 2 * (m : ℝ) * |t| * (‖E‖ - -‖E‖) = 4 * m * |t| * ‖E‖; ring)

#print axioms exists_equalMultiplicity_hamiltonianSimulation

end
end GaloisForLFunctions.HTGeometry
