import GaloisForLFunctions.HTGeometry.ComplexGramPlucker

/-!
# The Evans Gram determinant and the missing determinant line

The finite Evans presentation of an aperture stratum is a linear map from a `d`-dimensional space
into a `(d+3)`-dimensional excess target.  Its top exterior power is a Pluecker vector, its squared
norm is the Gram determinant, and the Pluecker vector vanishes exactly when the map has a kernel.

Two obstructions are recorded.  The excess target has `Nat.choose (d+3) d > 1` top exterior
coordinates, so the Pluecker vector does not live on a line and admits no canonical scalar; and
reversing the sign of one source vector reverses the Pluecker vector while leaving the Gram
determinant unchanged, so the Gram determinant is blind to the orientation of a kernel crossing.
-/

namespace GaloisForLFunctions.RHTower

open Module GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- The Evans excess target of an aperture stratum of characteristic multiplicity `d`. -/
abbrev evansExcessTarget (d : ℕ) : Type := Fin (d + 3) → ℂ

/-- The Pluecker vector of a finite Evans presentation: the top exterior power of the images of a
basis of the source. -/
def evansPlucker (v : Fin d → evansExcessTarget d) : ⋀[ℂ]^d (evansExcessTarget d) :=
  hermFeatureWedge v

/-- The Evans Gram matrix of a finite presentation. -/
def evansGram (v : Fin d → evansExcessTarget d) : Matrix (Fin d) (Fin d) ℂ :=
  hermFeatureGram v

/-- **Equation (3).**  The Evans Gram determinant is the squared Pluecker norm of the top exterior
power of the images of an orthonormal basis of the source. -/
theorem det_evansGram_eq_pluckerNormSq (v : Fin d → evansExcessTarget d) :
    (evansGram v).det = (hermPluckerNormSq v : ℂ) :=
  det_hermFeatureGram_eq_pluckerNormSq v

/-- **Equation (4), Pluecker half.**  The Pluecker vector vanishes exactly when the Evans
presentation has a kernel. -/
theorem evansPlucker_eq_zero_iff (v : Fin d → evansExcessTarget d) :
    evansPlucker v = 0 ↔ ¬ LinearIndependent ℂ v :=
  hermFeatureWedge_eq_zero_iff v

/-- **Equation (4), Gram half.**  The Evans Gram determinant is nonzero exactly when the Evans
presentation has no kernel. -/
theorem det_evansGram_ne_zero_iff (v : Fin d → evansExcessTarget d) :
    (evansGram v).det ≠ 0 ↔ LinearIndependent ℂ v :=
  det_hermFeatureGram_ne_zero_iff v

/-- The Evans Gram determinant is a nonnegative real number. -/
theorem det_evansGram_eq_nonneg_real (v : Fin d → evansExcessTarget d) :
    ∃ r : ℝ, 0 ≤ r ∧ (evansGram v).det = (r : ℂ) :=
  ⟨hermPluckerNormSq v, hermPluckerNormSq_nonneg v, det_evansGram_eq_pluckerNormSq v⟩

/-! ## The target of the Pluecker vector is not a line -/

theorem finrank_evansExcessTarget (d : ℕ) : finrank ℂ (evansExcessTarget d) = d + 3 := by
  simp [evansExcessTarget]

/-- The number of top exterior coordinates of the excess target. -/
theorem finrank_exteriorPower_evansExcessTarget (d : ℕ) :
    finrank ℂ (⋀[ℂ]^d (evansExcessTarget d)) = Nat.choose (d + 3) d := by
  rw [exteriorPower.finrank_eq, finrank_evansExcessTarget]

theorem one_lt_choose_add_three {d : ℕ} (hd : 1 ≤ d) : 1 < Nat.choose (d + 3) d := by
  have hsymm : Nat.choose (d + 3) d = Nat.choose (d + 3) 3 := by
    have h3 : d + 3 - 3 = d := by omega
    have hs := Nat.choose_symm (n := d + 3) (k := 3) (by omega)
    rwa [h3] at hs
  have hmono : Nat.choose 4 3 ≤ Nat.choose (d + 3) 3 := Nat.choose_le_choose 3 (by omega)
  have : Nat.choose 4 3 = 4 := by decide
  omega

/-- **The Pluecker target is not a determinant line.**  At every positive characteristic
multiplicity the top exterior power of the excess target has more than one dimension. -/
theorem one_lt_finrank_exteriorPower_evansExcessTarget {d : ℕ} (hd : 1 ≤ d) :
    1 < finrank ℂ (⋀[ℂ]^d (evansExcessTarget d)) := by
  rw [finrank_exteriorPower_evansExcessTarget]
  exact one_lt_choose_add_three hd

/-- **No canonical scalar.**  Since the top exterior power of the excess target is not a line, it is
not linearly isomorphic to the scalars: the Pluecker vector is not a section of a determinant
line. -/
theorem not_nonempty_linearEquiv_exteriorPower_evansExcessTarget {d : ℕ} (hd : 1 ≤ d) :
    ¬ Nonempty ((⋀[ℂ]^d (evansExcessTarget d)) ≃ₗ[ℂ] ℂ) := by
  rintro ⟨e⟩
  have h := one_lt_finrank_exteriorPower_evansExcessTarget hd
  rw [e.finrank_eq, finrank_self] at h
  exact absurd h (by omega)

/-! ## The Gram determinant forgets the orientation -/

/-- Reversing the sign of one source vector reverses the Pluecker vector. -/
theorem evansPlucker_update_neg (v : Fin d → evansExcessTarget d) (i : Fin d) :
    evansPlucker (Function.update v i (-(v i))) = - evansPlucker v := by
  have hsmul : (-(v i)) = (-1 : ℂ) • v i := by simp
  unfold evansPlucker hermFeatureWedge
  rw [hsmul, AlternatingMap.map_update_smul, Function.update_eq_self]
  simp

/-- The Pluecker norm, hence the Gram determinant, is unchanged by that sign reversal. -/
theorem hermPluckerNormSq_update_neg (v : Fin d → evansExcessTarget d) (i : Fin d) :
    hermPluckerNormSq (Function.update v i (-(v i))) = hermPluckerNormSq v := by
  unfold hermPluckerNormSq
  refine Finset.sum_congr rfl fun s _ => ?_
  have hcoord : hermFeatureMinor (Function.update v i (-(v i))) s = - hermFeatureMinor v s := by
    have h1 := hermFeatureWedge_coordinate (Function.update v i (-(v i))) s
    have h2 := hermFeatureWedge_coordinate v s
    have h3 : hermFeatureWedge (Function.update v i (-(v i))) = - hermFeatureWedge v :=
      evansPlucker_update_neg v i
    rw [← h1, ← h2, h3, map_neg]
    rfl
  rw [hcoord, norm_neg]

/-- **The Gram determinant forgets the crossing orientation.**  A source sign reversal takes the
Pluecker vector to its negative while leaving the Gram determinant unchanged, so no orientation of a
kernel crossing can be read off the Gram determinant. -/
theorem det_evansGram_update_neg (v : Fin d → evansExcessTarget d) (i : Fin d) :
    (evansGram (Function.update v i (-(v i)))).det = (evansGram v).det := by
  rw [det_evansGram_eq_pluckerNormSq, det_evansGram_eq_pluckerNormSq,
    hermPluckerNormSq_update_neg]

/-- **Scalar extractions disagree.**  At every positive characteristic multiplicity and every
kernel-free Evans presentation there are two nonzero scalar extractions of the Pluecker vector, one
of which is nonzero and one of which vanishes.  A scalar read off the rectangular Pluecker vector
therefore does not detect the kernel; the Gram determinant does. -/
theorem exists_scalar_extraction_disagreement {d : ℕ} (hd : 1 ≤ d)
    (v : Fin d → evansExcessTarget d) (hv : LinearIndependent ℂ v) :
    ∃ φ ψ : Module.Dual ℂ (⋀[ℂ]^d (evansExcessTarget d)),
      φ (evansPlucker v) ≠ 0 ∧ ψ ≠ 0 ∧ ψ (evansPlucker v) = 0 := by
  classical
  have hP : evansPlucker v ≠ 0 := fun h => ((evansPlucker_eq_zero_iff v).1 h) hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (⋀[ℂ]^d (evansExcessTarget d)),
      φ (evansPlucker v) ≠ 0 := by
    by_contra hcon
    exact hP ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 (fun φ => not_not.1 (not_exists.1 hcon φ)))
  have hline : (ℂ ∙ evansPlucker v) < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => ?_
    have hrk : finrank ℂ (⋀[ℂ]^d (evansExcessTarget d)) = 1 := by
      have h1 := finrank_span_singleton (K := ℂ) hP
      rw [htop, finrank_top] at h1
      exact h1
    have := one_lt_finrank_exteriorPower_evansExcessTarget (d := d) hd
    omega
  obtain ⟨ψ, hψ0, hψ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hline inferInstance
  refine ⟨φ, ψ, hφ, hψ0, ?_⟩
  have hmem : evansPlucker v ∈ (ℂ ∙ evansPlucker v) := Submodule.mem_span_singleton_self _
  have : ψ (evansPlucker v) ∈ (ℂ ∙ evansPlucker v).map ψ := ⟨_, hmem, rfl⟩
  rw [hψ] at this
  simpa using this

end

end GaloisForLFunctions.RHTower
