import GaloisForLFunctions.HTGeometry.Critical.Schur.ResidueReduction

/-!
# The corner cofactor survives the ramification ideal

`SchurCofactorLocus` proves that the universal Schur section does not divide its corner cofactor,
in the indexing `(n'+1, m'+1)` with `n' + m' - 1 + 2` variables.  The actual objects use `(n, m)`
with `m + n - 1` variables; the two agree, and the identification is the `finCongr` rename that the
corpus already performs for the determinant.  Transporting it to the minor and using that the
variable shift reflects membership in a principal ideal:

```text
rename_finCongr_det_submatrix_rectangularSchurToeplitz
not_dvd_det_submatrix_rectangularSchur_actual
criticalSchur_cornerCofactor_notMem_ramificationIdeal
    ** the corner cofactor of the actual Schur section is not in the ramification ideal **
```

so the corank of the critical Jacobian jumps only on a proper closed subset of the Schur divisor,
and in particular not at its generic point.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix IsLocalRing MvPolynomial

set_option synthInstance.maxHeartbeats 1000000

variable {K : Type*} [Field K]

/-- Renaming along an equality of variable counts transports minors of the Schur section. -/
theorem rename_finCongr_det_submatrix_rectangularSchurToeplitz {L₁ L₂ : ℕ} (h : L₁ = L₂)
    (n m : ℕ) {k : ℕ} (ρ γ : Fin k → Fin m) :
    MvPolynomial.rename (R := K) (finCongr h)
        (((rectangularSchurToeplitz (schurVar K L₁) n m).submatrix ρ γ).det) =
      ((rectangularSchurToeplitz (schurVar K L₂) n m).submatrix ρ γ).det := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← Matrix.submatrix_map,
    map_rename_finCongr_rectangularSchurToeplitz h n m]

/-- **The corner cofactor of the actual Schur section is not divisible by the section.** -/
theorem not_dvd_det_submatrix_rectangularSchur_actual [DecidableEq K] {m' n' : ℕ}
    (hm : 0 < m') (hn : 0 < n') :
    ¬ ((rectangularSchurToeplitz (schurVar K ((m' + 1) + (n' + 1) - 1)) (n' + 1) (m' + 1)).det ∣
      ((rectangularSchurToeplitz (schurVar K ((m' + 1) + (n' + 1) - 1)) (n' + 1)
        (m' + 1)).submatrix (Fin.last m').succAbove Fin.succ).det) := by
  have h : n' + m' - 1 + 2 = (m' + 1) + (n' + 1) - 1 := by omega
  intro hdvd
  refine not_dvd_det_submatrix_rectangularSchur (K := K) hn hm ?_
  obtain ⟨g, hg⟩ := hdvd
  refine ⟨MvPolynomial.rename (R := K) (finCongr h.symm) g, ?_⟩
  have hinj : Function.Injective
      (MvPolynomial.rename (R := K) (finCongr h) :
        MvPolynomial (Fin (n' + m' - 1 + 2)) K → MvPolynomial (Fin ((m' + 1) + (n' + 1) - 1)) K) :=
    MvPolynomial.rename_injective _ (finCongr h).injective
  apply hinj
  rw [map_mul, rename_finCongr_det_rectangularSchurToeplitz h,
    rename_finCongr_det_submatrix_rectangularSchurToeplitz h,
    MvPolynomial.rename_rename,
    show ((⇑(finCongr h)) ∘ (⇑(finCongr h.symm))) = id by funext x; exact Fin.ext rfl,
    MvPolynomial.rename_id]
  exact hg

/-- **The corner cofactor survives the ramification ideal**, so the corank of the Jacobian jumps
only on a proper closed subset of the Schur divisor. -/
theorem criticalSchur_cornerCofactor_notMem_ramificationIdeal [DecidableEq K] {m' n' : ℕ}
    (hm : 0 < m') (hn : 0 < n') :
    MvPolynomial.rename Fin.succ
        (((rectangularSchurToeplitz (schurVar K ((m' + 1) + (n' + 1) - 1)) (n' + 1)
          (m' + 1)).submatrix (Fin.last m').succAbove Fin.succ).det)
      ∉ criticalSchurRamificationIdeal K (m' + 1) (n' + 1) := by
  intro hmem
  rw [criticalSchurRamificationIdeal, criticalSourceSchurRamificationPolynomial] at hmem
  have hspan := mem_span_of_rename_succ_mem_span hmem
  rw [Ideal.mem_span_singleton] at hspan
  exact not_dvd_det_submatrix_rectangularSchur_actual hm hn hspan

end

end GaloisForLFunctions.HTGeometry
