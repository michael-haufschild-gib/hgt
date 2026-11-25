import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedTwistSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleTwistDivision
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedDehomogenization
import Mathlib.RingTheory.QuotSMulTop

/-! Dividing by the distinguished section identifies the dehomogenized module on its chart. -/

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.SchemeCohomology
open scoped Pointwise

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} {M H : LB X} {ι : Type}
  {V : X.Opens} (s : ι → H.Sec) (i : ι) (h : V ≤ nonzeroLocus (s i))
  (r : ι → Γ(X, V))
  (hr : ∀ j k, resG X (inf_le_right : V ⊓ H.U k ≤ H.U k) ((s j).f k) =
    resG X inf_le_left (r j) * resG X inf_le_right ((s i).f k))

include h hr in
theorem sectionRatio_self (hH : H.IsLB) : r i = 1 := by
  refine fun_ext_of_cover (fun k => V ⊓ H.U k) (fun _ => inf_le_left)
    (by rw [← inf_iSup_eq, hH.cover, inf_top_eq]) fun k => ?_
  have hu := isUnit_coord_of_le_nonzeroLocus (s i) k
    (inf_le_right : V ⊓ H.U k ≤ H.U k) (inf_le_left.trans h)
  apply hu.mul_right_cancel
  rw [← hr i k, map_one, one_mul]

include h hr in
theorem nonempty_dehomogenizedTwistChartEquiv
    (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) (hH : H.IsLB) :
    letI := sectionAlgebra f V
    letI : Module Γ(X, V) (TwistSections f M H V 0) :=
      inferInstanceAs (Module Γ(X, V) Γ(toMod (twist M H 0), V))
    letI := Module.compHom (TwistSections f M H V 0) (MvPolynomial.aeval r).toRingHom
    Nonempty (QuotSMulTop (X i - 1 : MvPolynomial ι R) (gradedTwistSections f M V s)
      ≃ₗ[MvPolynomial ι R] TwistSections f M H V 0) := by
  let S := MvPolynomial ι R
  let G := gradedTwistSections f M V s
  let P := TwistSections f M H V 0
  letI := sectionAlgebra f V
  let π : S →ₐ[R] Γ(X, V) := MvPolynomial.aeval r
  letI : Module Γ(X, V) P := inferInstanceAs (Module Γ(X, V) Γ(toMod (twist M H 0), V))
  letI : Module S P := Module.compHom P π.toRingHom
  haveI : IsScalarTower R S P := IsScalarTower.of_algebraMap_smul fun a x => by
    change algebraMap R Γ(X, V) a • x = π (algebraMap R S a) • x
    rw [π.commutes]
  let δ (t : ℤ) : TwistSections f M H V t →ₗ[R] P :=
    { (divTwistSection M (s i) h t).toAddMonoidHom with
      map_smul' a x := (divTwistSection M (s i) h t).map_smul (algebraMap R Γ(X, V) a) x }
  have hδ (j : ι) (t : ℤ) (x : TwistSections f M H V t) :
      δ (t + 1) (twistSections_mul f M V (s j) t x) = (X j : S) • δ t x := by
    change divTwistSection M (s i) h (t + 1) (mulTwistSection M t (s j) V x) =
      π (X j) • divTwistSection M (s i) h t x
    rw [show π (X j) = r j from MvPolynomial.aeval_X r j,
      mulTwistSection_eq_smul (s i) (s j) (r j) (hr j), map_smul, divTwistSection_mulTwistSection]
  let F : G →ₗ[S] P := GrSum.lift (twistSections_commute f M V s) δ hδ
  let u : S := X i - 1
  let K : Submodule S G := u • ⊤
  have hkill (y : G) : F (u • y) = 0 := by
    rw [map_smul]
    change π (X i - 1) • F y = 0
    rw [map_sub, map_one, show π (X i) = r i from MvPolynomial.aeval_X r i,
      sectionRatio_self s i h r hr hH, sub_self, zero_smul]
  have hK : K ≤ LinearMap.ker F := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    exact LinearMap.mem_ker.2 (hkill z)
  let η := K.liftQ F hK
  refine ⟨LinearEquiv.ofBijective η ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := K.mkQ_surjective q
    change F y = 0 at hq
    let D := GrSum.grading (twistSections_commute f M V s)
    obtain ⟨n, hn⟩ := exists_homogeneous_add_X_sub_one_smul D i y
    obtain ⟨a, ha, w, hy⟩ := hn n le_rfl
    obtain ⟨z, rfl⟩ := (GrSum.mem_grading _).1 ha
    rw [hy, map_add, hkill, add_zero] at hq
    change δ n z = 0 at hq
    have hz : z = 0 := (divTwistSection_injective (s i) h n) (hq.trans (map_zero _).symm)
    change K.mkQ y = 0
    rw [hy, hz, map_zero, zero_add]
    exact (Submodule.Quotient.mk_eq_zero K).2
      (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  · intro x
    refine ⟨K.mkQ (GrSum.of (twistSections_commute f M V s) 0 x), ?_⟩
    exact divTwistSection_zero (s i) h x

end GlobalTheory.LineBundleSections
