import GaloisForLFunctions.RHTower.PaperHurwitzFredholmDeterminant
import GaloisForLFunctions.RHTower.PaperHurwitzCompactObservation

/-! # Exponential Fredholm escape under native compact-input convergence

The prescribed Hurwitz perturbations are uniformly subunit and trace class.
Their determinants grow exactly geometrically although every fixed compact
input converges in operator norm to its scalar multiple.
-/

namespace RHTower
noncomputable section
open Filter GaloisForLFunctions GaloisForLFunctions.HTGeometry HilbertSchmidt
open scoped Topology

def paperHurwitzFredholmPerturbation (t : ℝ) (N : ℕ) :
    PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  (9 / 16 : ℂ) • paperHurwitzResolvent (paperHurwitzApproachPoint t N)

def paperHurwitzFredholmValue (t : ℝ) (N : ℕ) : ℂ :=
  fredholmDetOp (lpBasis ℕ) (paperHurwitzFredholmPerturbation t N)

theorem paperHurwitzFredholmPerturbation_traceClass (t : ℝ) (N : ℕ) :
    MemSchattenClass 1 (paperHurwitzFredholmPerturbation t N) :=
  memSchattenClass_one_smul (paperHurwitzApproach_resolvent_traceClass t N) (9 / 16 : ℂ)

theorem norm_paperHurwitzFredholmPerturbation (t : ℝ) (N : ℕ) :
    ‖paperHurwitzFredholmPerturbation t N‖ = 9 / 16 := by
  rw [paperHurwitzFredholmPerturbation, norm_smul, norm_paperHurwitzResolvent, mul_one]
  norm_num

theorem paperHurwitzFredholmValue_exact (t : ℝ) (N : ℕ) :
    paperHurwitzFredholmValue t N = (5 / 4 : ℂ) * 2 ^ (N + 3) :=
  paperHurwitzApproach_fredholmDet_exact t N

theorem norm_paperHurwitzFredholmValue (t : ℝ) (N : ℕ) :
    ‖paperHurwitzFredholmValue t N‖ = 10 * (2 : ℝ) ^ N := by
  rw [paperHurwitzFredholmValue_exact]
  norm_num [norm_mul, norm_div, norm_pow, pow_add]
  ring

theorem paperHurwitzFredholmValue_tendsto_atTop (t : ℝ) :
    Tendsto (fun N => ‖paperHurwitzFredholmValue t N‖) atTop atTop := by
  apply tendsto_atTop_mono (f := fun N : ℕ => (2 : ℝ) ^ N)
    (fun N => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  rw [norm_paperHurwitzFredholmValue]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N]

theorem paperHurwitzFredholmPerturbation_strong_tendsto (t : ℝ) (f : PaperHurwitzHistory) :
    Tendsto (fun N => paperHurwitzFredholmPerturbation t N f) atTop (𝓝 ((9 / 16 : ℂ) • f)) := by
  simpa only [paperHurwitzFredholmPerturbation, smul_apply] using
    (tendsto_paperHurwitzApproachPoint_strong t f).const_smul (9 / 16 : ℂ)

theorem paperHurwitzFredholmPerturbation_comp_compact_tendsto (t : ℝ)
    (K : compactOperatorStarAlgebra PaperHurwitzHistory) :
    Tendsto (fun N => paperHurwitzFredholmPerturbation t N ∘L K.val)
      atTop (𝓝 ((9 / 16 : ℂ) • K.val)) := by
  simpa only [paperHurwitzFredholmPerturbation, ContinuousLinearMap.smul_comp] using
    (paperHurwitzApproachPoint_comp_compact_tendsto t K).const_smul (9 / 16 : ℂ)

theorem paperHurwitzFredholm_subunit_compact_escape (t : ℝ) :
    (∀ N, MemSchattenClass 1 (paperHurwitzFredholmPerturbation t N) ∧
      ‖paperHurwitzFredholmPerturbation t N‖ < 1) ∧
    (∀ K : compactOperatorStarAlgebra PaperHurwitzHistory,
      Tendsto (fun N => paperHurwitzFredholmPerturbation t N ∘L K.val)
        atTop (𝓝 ((9 / 16 : ℂ) • K.val))) ∧
    Tendsto (fun N => ‖paperHurwitzFredholmValue t N‖) atTop atTop := by
  refine ⟨fun N => ⟨paperHurwitzFredholmPerturbation_traceClass t N, ?_⟩,
    paperHurwitzFredholmPerturbation_comp_compact_tendsto t,
    paperHurwitzFredholmValue_tendsto_atTop t⟩
  rw [norm_paperHurwitzFredholmPerturbation]
  norm_num

end
end RHTower
