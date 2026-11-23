import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedFibreParameters
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PullbackNormalizationTower
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedEtaleFibre

/-! Extension of normalized chart algebras carries origin equations to the
same origin equations in the upper field. -/

noncomputable section

open GlobalTheory.PD

namespace GlobalTheory.SchemeCohomology

variable {k F E L : Type} [Field k] [Field F] [Field E] [Field L]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d : ℕ} (x : Fin (d + 1) → F)

/-- The embedding of normalized charts induced by extending the field. -/
def rBPullback (I : Finset (Fin (d + 1))) : rB k E x I →ₐ[k] rB k L x I :=
  ((IsScalarTower.toAlgHom k E L).comp (rB k E x I).val).codRestrict _ fun a => by
    rw [← pullbackChartAlgebra_rB (E := E) (L := L) x I]
    let S := (rB k E x I).map (IsScalarTower.toAlgHom k E L)
    let b : S := ⟨algebraMap E L a.1, ⟨a.1, a.2, rfl⟩⟩
    exact isIntegral_algebraMap (x := b)

@[simp]
theorem rBPullback_coe (I : Finset (Fin (d + 1))) (b : rB k E x I) :
    (rBPullback (L := L) x I b : L) = algebraMap E L b.1 := rfl

theorem rBPullback_originCoordinate (j : Fin d) :
    rBPullback x {0} (⟨_, tco_mem k E x j⟩ : rB k E x {0}) =
      (⟨_, tco_mem k L x j⟩ : rB k L x {0}) :=
  Subtype.ext (IsScalarTower.algebraMap_apply F E L _).symm

/-- The reduced origin fibre of a finite cover remains reduced under
unramified extension of its chart ring. -/
theorem isReduced_normalizedOriginFibre_pullback [PerfectField k]
    (hE : IsFinCover k E x) (hL : IsFinCover k L x)
    (h : (rBPullback x {0} : rB k E x {0} →ₐ[k] rB k L x {0}).toRingHom.FormallyUnramified)
    [IsReduced ((rB k E x {0}) ⧸ Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem k E x j⟩ : rB k E x {0})))] :
    IsReduced ((rB k L x {0}) ⧸ Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem k L x j⟩ : rB k L x {0}))) := by
  let A := rB k E x {0}
  let B := rB k L x {0}
  let r (j : Fin d) : A := ⟨_, tco_mem k E x j⟩
  let t (j : Fin d) : B := ⟨_, tco_mem k L x j⟩
  let I := Ideal.span (Set.range r)
  let J := Ideal.span (Set.range t)
  let g : A →ₐ[k] B := rBPullback x {0}
  letI : Algebra A B := g.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  letI : Algebra.FormallyUnramified A B := h
  have e : I.map (algebraMap A B) = J := by
    rw [show I = Ideal.span (Set.range r) from rfl, Ideal.map_span,
      ← Set.range_comp (algebraMap A B) r]
    exact congrArg (fun u : Fin d → B => Ideal.span (Set.range u))
      (funext (rBPullback_originCoordinate (k := k) (E := E) (L := L) x))
  letI : Module.Finite k (A ⧸ I) := finite_originFibre hE
  letI : Module.Finite k (B ⧸ I.map (algebraMap A B)) := e.symm ▸ finite_originFibre hL
  change IsReduced (B ⧸ J)
  rw [← e]
  exact isReduced_quotient_map_of_formallyUnramified k I

end GlobalTheory.SchemeCohomology
