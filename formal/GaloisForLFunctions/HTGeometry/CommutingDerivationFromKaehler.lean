import GaloisForLFunctions.HTGeometry.RelativeKaehlerDiffOp
import GaloisForLFunctions.HTGeometry.DifferentialOperatorExtensionCogenerator
import GaloisForLFunctions.HTGeometry.DifferentialClosureClosed
import GaloisForLFunctions.HTGeometry.KaehlerKernel

/-!
# Commuting derivations from nonzero relative Kähler differentials

For a finitely differentially generated field extension `K/C`, every ordinary transcendental
direction produces a nonzero `C`-derivation `K → diffClosure K` commuting with the distinguished
derivation.  Relative Kähler differentials provide the universal source; the extension-valued Ore
cogenerator supplies a nonzero horizontal functional.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

universe u

variable {C K : Type u} [Field C] [Field K] [CharZero C] [Algebra ℚ C]
  [Algebra ℚ K] [Differential C] [Differential K]
  [Algebra C K] [DifferentialAlgebra C K]

/-- A type-separated differential closure carrying both the upper- and lower-field scalar
structures. -/
def RelativeDiffClosure (C K : Type u) [Field K] [Algebra ℚ K] [Differential K] :=
  diffClosure K

instance relativeDiffClosureField : Field (RelativeDiffClosure C K) :=
  inferInstanceAs (Field (diffClosure K))

instance relativeDiffClosureRatAlgebra : Algebra ℚ (RelativeDiffClosure C K) :=
  inferInstanceAs (Algebra ℚ (diffClosure K))

instance relativeDiffClosureDifferential : Differential (RelativeDiffClosure C K) :=
  inferInstanceAs (Differential (diffClosure K))

instance relativeDiffClosureUpperAlgebra : Algebra K (RelativeDiffClosure C K) :=
  inferInstanceAs (Algebra K (diffClosure K))

instance relativeDiffClosureLowerAlgebra : Algebra C (RelativeDiffClosure C K) :=
  ((algebraMap K (RelativeDiffClosure C K)).comp (algebraMap C K)).toAlgebra

instance relativeDiffClosureScalarTower :
    IsScalarTower C K (RelativeDiffClosure C K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance relativeDiffClosureDifferentialAlgebra :
    DifferentialAlgebra K (RelativeDiffClosure C K) := by
  constructor
  intro a
  exact (diffClosureExt K).compat a

instance relativeDiffClosureIsDifferentiallyClosed :
    IsDifferentiallyClosed (RelativeDiffClosure C K) :=
  isDifferentiallyClosed_diffClosure K

/-- The finite free Ore module mapping its coordinate basis to specified Kähler differentials. -/
def kaehlerDiffOpPresentation {κ : Type*} [Fintype κ]
    [Module (DiffOp K) Ω[K⁄C]] (y : κ → K) :
    (κ → DiffOp K) →ₗ[DiffOp K] Ω[K⁄C] where
  toFun p := ∑ i, p i • KaehlerDifferential.D C K (y i)
  map_add' p q := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' p q := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      change (p * q i) • KaehlerDifferential.D C K (y i) =
        p • q i • KaehlerDifferential.D C K (y i)
      rw [mul_smul]

theorem kaehlerDiffOpPresentation_single {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Module (DiffOp K) Ω[K⁄C]] (y : κ → K) (i : κ) :
    kaehlerDiffOpPresentation y (Pi.single i 1) = KaehlerDifferential.D C K (y i) := by
  classical
  simp [kaehlerDiffOpPresentation]

/-- **A transcendental direction yields a nonzero commuting derivation into the differential
closure.** -/
theorem exists_nonzero_commuting_derivation_to_diffClosure
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (y : κ → K) (hgen : differentialAdjoin C (Set.range y) = ⊤)
    {z : K} (hz : ¬ IsAlgebraic C z) :
    ∃ D : Derivation C K (RelativeDiffClosure C K), D ≠ 0 ∧
      ∀ x : K, D (Differential.deriv x) = Differential.deriv (D x) := by
  let E := RelativeDiffClosure C K
  letI : Module (DiffOp K) Ω[K⁄C] := relativeKaehlerDiffOpModule
  letI : IsScalarTower K (DiffOp K) Ω[K⁄C] :=
    ⟨fun a p ω => by
      change connectionDiffOpSMul relativeKaehlerConnection (a • p) ω =
        a • connectionDiffOpSMul relativeKaehlerConnection p ω
      exact connectionDiffOpSMul_smul relativeKaehlerConnection a p ω⟩
  letI : Module (DiffOp K) E := DiffOp.extensionModule
  letI : IsScalarTower K (DiffOp K) E :=
    ⟨fun a p x => by
      change DiffOp.fieldApply (DiffOp.mapCoeffs (algebraMap K E) (a • p)) x =
        a • DiffOp.fieldApply (DiffOp.mapCoeffs (algebraMap K E) p) x
      rw [DiffOp.mapCoeffs_smul, DiffOp.fieldApply_smul]
      rfl⟩
  let ψ : (κ → DiffOp K) →ₗ[DiffOp K] Ω[K⁄C] := kaehlerDiffOpPresentation y
  have hψsingle (i : κ) : ψ (Pi.single i 1) = KaehlerDifferential.D C K (y i) :=
    kaehlerDiffOpPresentation_single y i
  have hψrange : LinearMap.range ψ = ⊤ := by
    apply top_unique
    rw [← relative_span_diffOp_D_eq_top hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨s, ⟨i, rfl⟩, rfl⟩
    exact ⟨Pi.single i 1, hψsingle i⟩
  have hψsurj : Function.Surjective ψ := LinearMap.range_eq_top.mp hψrange
  have hzD : KaehlerDifferential.D C K z ≠ 0 := by
    intro hzero
    exact hz (kaehlerD_eq_zero_iff_isAlgebraic.mp hzero)
  have hkerProper : LinearMap.ker ψ ≠ ⊤ := by
    intro htop
    obtain ⟨p, hp⟩ := hψsurj (KaehlerDifferential.D C K z)
    have hpker : p ∈ LinearMap.ker ψ := by rw [htop]; trivial
    rw [LinearMap.mem_ker, hp] at hpker
    exact hzD hpker
  obtain ⟨pair, hpair, hker⟩ :=
    DiffOp.exists_ne_zero_linearMap_kerOver_of_ne_top
      (K := K) (E := E) (LinearMap.ker ψ) hkerProper
  let e : ((κ → DiffOp K) ⧸ LinearMap.ker ψ) ≃ₗ[DiffOp K] Ω[K⁄C] :=
    ψ.quotKerEquivOfSurjective hψsurj
  let pairQ : ((κ → DiffOp K) ⧸ LinearMap.ker ψ) →ₗ[DiffOp K] E :=
    (LinearMap.ker ψ).liftQ pair hker
  let φ : Ω[K⁄C] →ₗ[DiffOp K] E := pairQ.comp e.symm.toLinearMap
  have hφψ (p : κ → DiffOp K) : φ (ψ p) = pair p := by
    change pairQ (e.symm (ψ p)) = pair p
    have he : e (Submodule.Quotient.mk p) = ψ p :=
      LinearMap.quotKerEquivOfSurjective_apply_mk ψ hψsurj p
    rw [← he, e.symm_apply_apply]
    exact Submodule.liftQ_apply _ _ _
  have hφ : φ ≠ 0 := by
    intro hzero
    apply hpair
    apply LinearMap.ext
    intro p
    have hp := hφψ p
    rw [hzero] at hp
    simpa using hp.symm
  let φK : Ω[K⁄C] →ₗ[K] E := φ.restrictScalars K
  have hφK : φK ≠ 0 := by
    intro hzero
    apply hφ
    apply LinearMap.ext
    intro ω
    have := LinearMap.congr_fun hzero ω
    exact this
  let D : Derivation C K E := φK.compDer (KaehlerDifferential.D C K)
  have hpartialΩ (ω : Ω[K⁄C]) :
      (DiffOp.mono 1 1 : DiffOp K) • ω =
        relativeKaehlerConnection (C := C) (K := K) ω := by
    change connectionDiffOpSMul relativeKaehlerConnection (DiffOp.mono 1 1) ω = _
    rw [connectionDiffOpSMul_mono, one_smul]
    rfl
  have hpartialE (x : E) : (DiffOp.mono 1 1 : DiffOp K) • x = Differential.deriv x := by
    change DiffOp.fieldApply (DiffOp.mapCoeffs (algebraMap K E) (DiffOp.mono 1 1)) x = _
    rw [DiffOp.mapCoeffs_mono, map_one, DiffOp.fieldApply_mono]
    simp [differentialJet_succ]
  have hcomm : ∀ x : K, D (Differential.deriv x) = Differential.deriv (D x) := by
    intro x
    calc
      D (Differential.deriv x) =
          φ (KaehlerDifferential.D C K (Differential.deriv x)) := rfl
      _ = φ (relativeKaehlerConnection (C := C) (K := K)
          (KaehlerDifferential.D C K x)) := by rw [relativeKaehlerConnection_D]
      _ = φ ((DiffOp.mono 1 1 : DiffOp K) • KaehlerDifferential.D C K x) := by
          rw [hpartialΩ]
      _ = (DiffOp.mono 1 1 : DiffOp K) • φ (KaehlerDifferential.D C K x) := by
          rw [map_smul]
      _ = Differential.deriv (D x) := hpartialE _
  refine ⟨D, ?_, hcomm⟩
  intro hD
  apply hφK
  apply LinearMap.ext
  intro ω
  change φK ω = 0
  have hω : ω ∈ (⊤ : Submodule K Ω[K⁄C]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation C K] at hω
  induction hω using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨x, rfl⟩ := hw
      have hx := Derivation.congr_fun hD x
      exact hx
  | zero => exact map_zero φK
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

end

end GaloisForLFunctions.HTGeometry
