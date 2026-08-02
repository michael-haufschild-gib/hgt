import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreMap
import GaloisForLFunctions.HTGeometry.FreeDifferentialFrechet

/-!
# The differential substitution chain rule

A differential embedding of free differential rational fields is an algebra map

`Φ : C⟨y₁,…,y_s⟩ → C⟨x₁,…,x_r⟩`

commuting with the derivations.  Its Frechet matrix is the family of operator rows

`P i j = J(Φ y_i)_j`.

The chain rule states that the Frechet row of a substituted element is the matrix product of the
transported Frechet row of the element with the Frechet matrix:

`J(Φ u)_j = ∑_i Φ(J(u)_i) · P i j`.

Both sides are derivations in `u` with values in the operator module of the target field, so the
identity follows from the coordinate expansion of derivations together with its value on the
coordinates `y_i^{(n)}`, where it reduces to `∂ⁿ · P i j`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace JetField

noncomputable section

universe w

variable {C : Type u} {ι : Type v} {ι' : Type w} [Field C]

theorem differentialJet_jet (i : ι) (m n : ℕ) :
    differentialJet n (jet ((i, m) : ι × ℕ) : JetField C ι) = jet (i, m + n) := by
  induction n with
  | zero =>
    rw [differentialJet_zero]
    rfl
  | succ n ih =>
    rw [differentialJet_succ, ih, deriv_jet]
    rfl

section Embedding

variable [Algebra (JetField C ι') (JetField C ι)]
  [IsScalarTower C (JetField C ι') (JetField C ι)]

/-- The Frechet matrix of a differential embedding. -/
def frechetMatrix (i : ι') (j : ι) : DiffOp (JetField C ι) :=
  frechet (algebraMap (JetField C ι') (JetField C ι) (jet (i, 0))) j

variable (hδ : ∀ u : JetField C ι', algebraMap (JetField C ι') (JetField C ι) (u′)
  = (algebraMap (JetField C ι') (JetField C ι) u)′)

include hδ

omit [IsScalarTower C (JetField C ι') (JetField C ι)] in
theorem algebraMap_differentialJet (n : ℕ) (u : JetField C ι') :
    algebraMap (JetField C ι') (JetField C ι) (differentialJet n u)
      = differentialJet n (algebraMap (JetField C ι') (JetField C ι) u) := by
  induction n with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ n ih =>
    rw [differentialJet_succ, differentialJet_succ, hδ, ih]

omit [IsScalarTower C (JetField C ι') (JetField C ι)] in
theorem algebraMap_jet (i : ι') (n : ℕ) :
    algebraMap (JetField C ι') (JetField C ι) (jet (i, n))
      = differentialJet n (algebraMap (JetField C ι') (JetField C ι) (jet (i, 0))) := by
  rw [← algebraMap_differentialJet hδ, differentialJet_jet, Nat.zero_add]

omit [IsScalarTower C (JetField C ι') (JetField C ι)] in
theorem coeff_dpartial_iterate_frechetMatrix (i : ι') (n : ℕ) (j : ι) (m : ℕ) :
    DiffOp.coeff (DiffOp.dpartial^[n] (frechetMatrix (C := C) (ι' := ι') i j)) m
      = pd (j, m) (algebraMap (JetField C ι') (JetField C ι) (jet (i, n))) := by
  rw [frechetMatrix, ← frechet_differentialJet, coeff_frechet]
  conv_rhs => rw [algebraMap_jet hδ i n]

/-- **Chain rule, coefficientwise.** -/
theorem coeff_frechet_algebraMap [Fintype ι'] (u : JetField C ι') (j : ι) (m : ℕ) :
    pd (j, m) (algebraMap (JetField C ι') (JetField C ι) u)
      = ∑ i, DiffOp.coeff (DiffOp.map (algebraMap (JetField C ι') (JetField C ι))
          (frechet u i) * frechetMatrix i j) m := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_finset_pd_eq_zero u
  set T : Finset ℕ := s₀.image Prod.snd with hT
  have hTvanish : ∀ (i : ι') (n : ℕ), n ∉ T → pd ((i, n) : ι' × ℕ) u = 0 := by
    intro i n hn
    refine hs₀ (i, n) fun hmem => hn ?_
    exact Finset.mem_image.mpr ⟨(i, n), hmem, rfl⟩
  -- the left-hand side, by the coordinate expansion of the derivation `u ↦ ∂ (Φ u)`
  have hD : ((pd (C := C) (ι := ι) (j, m)).compAlgebraMap (JetField C ι')) u
      = ∑ p ∈ (Finset.univ : Finset ι') ×ˢ T,
          (pd p u) • ((pd (C := C) (ι := ι) (j, m)).compAlgebraMap (JetField C ι')) (jet p) := by
    refine pd_expansion _ u _ ?_
    intro p hp
    have hp2 : p.2 ∉ T := fun hmem =>
      hp (Finset.mem_product.mpr ⟨Finset.mem_univ p.1, hmem⟩)
    have := hTvanish p.1 p.2 hp2
    rwa [Prod.mk.eta] at this
  rw [Derivation.compAlgebraMap_apply] at hD
  rw [hD]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [DiffOp.coeff_mul_of_subset (t := T) (fun n hn => by
    rw [DiffOp.coeff_map, coeff_frechet, hTvanish i n hn, map_zero])]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [DiffOp.coeff_map, coeff_frechet, coeff_dpartial_iterate_frechetMatrix hδ,
    Derivation.compAlgebraMap_apply, Algebra.smul_def]

/-- **Chain rule.**  The Frechet row of a substituted element is the product of the transported
Frechet row with the Frechet matrix of the embedding. -/
theorem frechet_algebraMap_eq_vecMul [Fintype ι'] (u : JetField C ι') (j : ι) :
    frechet (algebraMap (JetField C ι') (JetField C ι) u) j
      = DiffOp.vecMul (fun i => DiffOp.map (algebraMap (JetField C ι') (JetField C ι))
          (frechet u i)) frechetMatrix j := by
  ext m
  rw [coeff_frechet, coeff_frechet_algebraMap hδ u j m, DiffOp.vecMul,
    ← DiffOp.coeffAddHom_apply m, map_sum]
  rfl

end Embedding

end

end JetField

end GaloisForLFunctions.HTGeometry
