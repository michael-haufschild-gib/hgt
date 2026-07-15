import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolLowerLaw
import GaloisForLFunctions.HTGeometry.ProjectiveJetHorizon

/-!
# Matrix principal-symbol differential horizon

The block principal-symbol theorem is lifted from ordinary packet independence to genuine
differential algebraic independence.  A finite family whose complete differential jets obey an
explicit strict-lower-layer principal law is differentially independent exactly when every matrix
principal symbol is nonsingular.  For a flat law space, the exact differential-algebraic spectrum
is therefore either total or one first-layer determinantal horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set
open scoped Differential

variable {K L g ι : Type*} [Field K] [Field L] [Algebra K L] [Differential L]
  [Fintype ι] [DecidableEq ι]

/-- **General matrix principal-symbol hypertranscendence theorem.**  Relative to a differentially
independent source family, an explicit strict-lower-layer law transports differential independence
to the target family exactly when every matrix principal symbol is invertible. -/
theorem matrixPrincipalLowerLaw_differentialIndependent_iff
    (source target : ι → L) (symbol : ℕ → Matrix ι ι K)
    (hlaw : MatrixPrincipalLowerLaw
      (fun n i ↦ differentialJet n (source i))
      (fun n i ↦ differentialJet n (target i)) symbol)
    (hsource : DifferentialIndependent K source) :
    DifferentialIndependent K target ↔ ∀ n : ℕ, (symbol n).det ≠ 0 := by
  have hsourceJet : AlgebraicIndependent K
      (fun p : ℕ × ι ↦ differentialJet p.1 (source p.2)) := by
    unfold DifferentialIndependent at hsource
    let swap : ℕ × ι → ι × ℕ := fun p ↦ (p.2, p.1)
    have hswap : Function.Injective swap := by
      rintro ⟨n, i⟩ ⟨m, j⟩ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    simpa [swap, Function.comp_def] using hsource.comp swap hswap
  have hpacket := matrixPrincipalLowerLaw_algebraicIndependent_iff
    (fun n i ↦ differentialJet n (source i))
    (fun n i ↦ differentialJet n (target i)) symbol hlaw hsourceJet
  constructor
  · intro htarget
    apply hpacket.mp
    unfold DifferentialIndependent at htarget
    let swap : ℕ × ι → ι × ℕ := fun p ↦ (p.2, p.1)
    have hswap : Function.Injective swap := by
      rintro ⟨n, i⟩ ⟨m, j⟩ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    simpa [swap, Function.comp_def] using htarget.comp swap hswap
  · intro hsymbols
    have htargetJet := hpacket.mpr hsymbols
    unfold DifferentialIndependent
    let swap : ι × ℕ → ℕ × ι := fun p ↦ (p.2, p.1)
    have hswap : Function.Injective swap := by
      rintro ⟨i, n⟩ ⟨j, m⟩ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    simpa [swap, Function.comp_def] using htargetJet.comp swap hswap

/-- Rank-one specialization: an explicit principal law transports hypertranscendence of one
source element to one target element exactly off the scalar determinant horizon. -/
theorem matrixPrincipalLowerLaw_hypertranscendentalOver_iff
    (source target : L) (symbol : ℕ → Matrix Unit Unit K)
    (hlaw : MatrixPrincipalLowerLaw
      (fun n _ ↦ differentialJet n source)
      (fun n _ ↦ differentialJet n target) symbol)
    (hsource : HypertranscendentalOver K source) :
    HypertranscendentalOver K target ↔ ∀ n : ℕ, (symbol n).det ≠ 0 := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton K target]
  apply matrixPrincipalLowerLaw_differentialIndependent_iff
    (fun _ : Unit ↦ source) (fun _ : Unit ↦ target) symbol hlaw
  exact (hypertranscendentalOver_iff_differentialIndependent_singleton K source).mp hsource

/-- Law directions at which the target observable family is differentially algebraically
dependent. -/
def matrixDifferentialDependentSet
    (target : g → ι → L) : Set g :=
  {A | ¬ DifferentialIndependent K (target A)}

/-- The exact differential-algebraic law spectrum is the determinant characteristic set. -/
theorem matrixDifferentialDependentSet_eq_characteristicSet
    (source : ι → L) (target : g → ι → L)
    (symbol : ℕ → g → Matrix ι ι K)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw
      (fun n i ↦ differentialJet n (source i))
      (fun n i ↦ differentialJet n (target A i))
      (fun n ↦ symbol n A))
    (hsource : DifferentialIndependent K source) :
    matrixDifferentialDependentSet (K := K) target =
      matrixSymbolCharacteristicSet symbol := by
  ext A
  change (¬ DifferentialIndependent K (target A)) ↔ ∃ n, (symbol n A).det = 0
  rw [matrixPrincipalLowerLaw_differentialIndependent_iff
    source (target A) (fun n ↦ symbol n A) (hlaw A) hsource]
  push Not
  rfl

/-- **Differential holographic horizon.**  With flat matrix symbols and one regular law direction,
the actual differential-algebraic dependence spectrum of the target family is exactly the first
determinantal locus. -/
theorem matrixDifferentialDependentSet_eq_firstSingularSet_of_flat
    (source : ι → L) (target : g → ι → L)
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw
      (fun n i ↦ differentialJet n (source i))
      (fun n i ↦ differentialJet n (target A i))
      (fun n ↦ symbol n A))
    (hsource : DifferentialIndependent K source) :
    matrixDifferentialDependentSet (K := K) target =
      matrixSymbolSingularSet symbol 0 := by
  rw [matrixDifferentialDependentSet_eq_characteristicSet
    source target symbol hlaw hsource]
  exact matrixSymbolCharacteristicSet_eq_firstSingularSet symbol hflat A₀ hA₀

/-- **Flat differential-horizon dichotomy.**  A realized finite-rank flat law space has either no
differentially independent direction, or an exact dependence spectrum equal to one first-layer
determinantal horizon. -/
theorem matrixPrincipalLowerLaw_flat_differentialSpectrum_dichotomy
    (source : ι → L) (target : g → ι → L)
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (hlaw : ∀ A, MatrixPrincipalLowerLaw
      (fun n i ↦ differentialJet n (source i))
      (fun n i ↦ differentialJet n (target A i))
      (fun n ↦ symbol n A))
    (hsource : DifferentialIndependent K source) :
    matrixDifferentialDependentSet (K := K) target = Set.univ ∨
      ∃ A₀ : g, (∀ n, (symbol n A₀).det ≠ 0) ∧
        matrixDifferentialDependentSet (K := K) target =
          matrixSymbolSingularSet symbol 0 := by
  rw [matrixDifferentialDependentSet_eq_characteristicSet
    source target symbol hlaw hsource]
  exact matrixPrincipalSymbolFlat_characteristicSet_dichotomy symbol hflat

end

end GaloisForLFunctions.HTGeometry
