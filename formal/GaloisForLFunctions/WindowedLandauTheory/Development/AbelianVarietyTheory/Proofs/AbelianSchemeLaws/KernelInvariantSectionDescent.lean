import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FormalSectionOperations
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TorsionInvariantFunctions

/-! Descent of sections of a formal product along an étale isogeny. -/

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FlatDescent

variable {X Y : Scheme.{0}} {G : Type}

/-- Invariant sections on each inverse image descend along the ring pullback. -/
def Descends (q : Y ⟶ Y) (τ : G → (Y ⟶ Y)) : Prop :=
  (∀ U : Y.Opens, Function.Injective (q.app U).hom) ∧
    ∀ (U : Y.Opens) (f : Γ(Y, q ⁻¹ᵁ U)),
      (∀ g, ∀ y ∈ q ⁻¹ᵁ U, gs (τ g) y (q ⁻¹ᵁ U) f = gs (𝟙 Y) y (q ⁻¹ᵁ U) f) →
        ∃ a, (q.app U).hom a = f

/-- Invariance of the germ coefficients gives an invariant section in each trivialization.
The descended coefficients satisfy the transition identities by injectivity of pullback. -/
theorem Descends.section {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ)
    (hτ : ∀ g, τ g ≫ q = q) {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    (f : I → (Y ⟶ X)) (d : I → ℤ)
    (s : (LB.LinComb L (fun i => q ≫ f i) d).Sec)
    (hs : ∀ g y J, Good L y J → sval s (τ g) y J = sval s (𝟙 Y) y J) :
    ∃ t : (LB.LinComb L f d).Sec, ∀ (r : Y ⟶ Y) (y : Y) J,
      Good L y J → sval t (r ≫ q) y J = sval s r y J := by
  let M := LB.LinComb L f d
  let M' := LB.LinComb L (fun i => q ≫ f i) d
  have le (j : I → L.ι) : q ⁻¹ᵁ M.U j ≤ M'.U j :=
    fun _ hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
  have ge (j : I → L.ι) : M'.U j ≤ q ⁻¹ᵁ M.U j :=
    fun _ hz => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
  have hchart (j : I → L.ι) : ∃ a : Γ(Y, M.U j), q.app (M.U j) a =
      (Y.presheaf.map (homOfLE (le j)).op).hom (s.f j) := by
    refine H.2 (M.U j) _ fun g y hy => ?_
    have hy' : τ g y ∈ q ⁻¹ᵁ M.U j := (congrArg (fun t => t y ∈ M.U j) (hτ g)).mpr hy
    choose J hJ using fun v : Y ⟶ X => exists_chart hL (v y)
    refine (gs_res (τ g) y (le j) hy' _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y (le j) hy _).symm)
    refine (sec_trans s (τ g) y (le j hy') (Good.mem hJ _ _)).trans
      (Eq.trans ?_ (sec_trans s (𝟙 Y) y (le j hy) (Good.mem hJ _ _)).symm)
    refine congrArg₂ (· * ·) (congrArg Units.val (Finset.prod_congr rfl fun i _ => ?_)) (hs g y J hJ)
    have e : τ g ≫ q ≫ f i = 𝟙 Y ≫ q ≫ f i := by
      rw [← Category.assoc, hτ, Category.id_comp]
    exact congrArg (fun v : Y ⟶ X =>
      gm v y (L.U (j i) ⊓ L.U (J v)) (L.g (j i) (J v)) ^ d i) e
  choose a ha using hchart
  have key (r : Y ⟶ Y) (y : Y) (j : I → L.ι) (hy : r y ∈ M'.U j) :
      gs (r ≫ q) y (M.U j) (a j) = gs r y (M'.U j) (s.f j) :=
    (gs_pull r q y (M.U j) (ge j hy) _).symm.trans
      ((congrArg (gs r y _) (ha j)).trans (gs_res r y (le j) (ge j hy) _))
  refine ⟨⟨a, fun j j' => H.1 _ (fn_ext fun y hy => ?_)⟩, fun r y J hJ => ?_⟩
  · let W := M.U j ⊓ M.U j'
    refine (gs_pull (𝟙 Y) q y W hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y) q y W hy _).symm)
    refine ((gs_res _ y _ hy _).trans (key (𝟙 Y) y j (le j hy.1))).trans
      ((sec_trans s (𝟙 Y) y (le j hy.1) (le j' hy.2)).trans (Eq.symm ?_))
    refine (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit _ y _ hy _).trans (congrArg Units.val ?_))
      ((gs_res _ y _ hy _).trans (key (𝟙 Y) y j' (le j' hy.2))))
    exact (gm_linComb L f d (𝟙 Y ≫ q) y j j' hy.1 hy.2).trans (by
      simp only [trF, Category.assoc])
  · let j : I → L.ι := fun i => J (r ≫ q ≫ f i)
    have e : (fun i => J ((r ≫ q) ≫ f i)) = j := funext fun i =>
      congrArg J (Category.assoc _ _ _)
    unfold sval
    rw [e]
    exact key r y j (hJ.mem _ r)

attribute [local instance] Over.cartesianMonoidalCategory

/-- The rational kernel translations detect descent of regular functions along an
étale surjective endomorphism over an algebraically closed field. -/
theorem descends_of_etale_isogeny {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] [IsReduced A.left] [LocallyOfFiniteType A.hom]
    (q : A ⟶ A) [IsMonHom q] [Etale q.left] [Surjective q.left] [QuasiCompact q.left] :
    Descends q.left (fun y : {y : 𝟙_ (Over (Spec (.of K))) ⟶ A // y ≫ q = 1} =>
      ((toUnit A ≫ y.1) * 𝟙 A).left) := by
  let D := {y : 𝟙_ (Over (Spec (.of K))) ⟶ A // y ≫ q = 1}
  let τ (y : D) : A ⟶ A := (toUnit A ≫ y.1) * 𝟙 A
  have e (y : D) : (τ y).left ≫ q.left = q.left := by
    change (τ y ≫ q).left = q.left
    refine congrArg Over.Hom.left ?_
    change ((toUnit A ≫ y.1) * 𝟙 A) ≫ q = q
    rw [MonObj.mul_comp, Category.assoc, y.2, MonObj.comp_one, _root_.one_mul, Category.id_comp]
  refine ⟨fun U a b hab => ?_, fun U f hf => ?_⟩
  · refine (existsUnique_descend_of_kernel_translation_invariant q U (q.left.app U a)
      (fun y hy hle => fn_ext fun z hz => ?_)).unique rfl hab.symm
    let y' : D := ⟨y, hy⟩
    refine (gs_appLE (τ y').left _ _ hle (𝟙 A.left) z hz _).trans ?_
    rw [Category.id_comp]
    exact (gs_pull (τ y').left q.left z U (hle hz) a).trans
      ((congrArg (fun r => gs r z U a) (e y')).trans
        ((congrArg (fun r => gs r z U a) (Category.id_comp q.left)).symm.trans
          (gs_pull (𝟙 A.left) q.left z U hz a).symm))
  · refine (existsUnique_descend_of_kernel_translation_invariant q U f
      (fun y hy hle => fn_ext fun z hz => ?_)).exists
    let y' : D := ⟨y, hy⟩
    refine (gs_appLE (τ y').left _ _ hle (𝟙 A.left) z hz f).trans ?_
    rw [Category.id_comp]
    exact hf y' z hz

end GlobalTheory.FlatDescent
