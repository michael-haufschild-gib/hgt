import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTwistSections
import GaloisForLFunctions.HTGeometry.ProjTwistedComparison

/-! The degree-`-e` localized fractions identify the Čech terms of the projective twist. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry

namespace GlobalTheory.SchemeCohomology.ProjTwist

universe u

variable {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
  {𝒜 : ℕ → Submodule K A} [GradedAlgebra 𝒜]
  {ι : Type*} [DecidableEq ι] {w : ι → A} (hw : ∀ i, w i ∈ 𝒜 1)

private theorem mem_awayDeg_iff {s : Finset ι} (hs : s.Nonempty) (e : ℕ) (z : LocAt w s) :
    z ∈ awayDeg 𝒜 (wProd_mem hw s) (Finset.card_pos.mpr hs) (-(e : ℤ)) ↔
      z ∈ twPart 𝒜 w s e := by
  rw [mem_twPart_iff hw hs]
  constructor
  · rintro ⟨m, i, a, ha, hdeg, rfl⟩
    refine ⟨m, i, a, ha, ?_, rfl⟩
    have h : ((i + e : ℕ) : ℤ) = ((m * s.card : ℕ) : ℤ) := by
      push_cast
      omega
    exact_mod_cast h
  · rintro ⟨m, i, a, ha, hdeg, rfl⟩
    refine ⟨m, i, a, ha, ?_, rfl⟩
    have h : (i : ℤ) + e = (m : ℤ) * s.card := by exact_mod_cast hdeg
    omega

private def chartLocalization (s : Finset ι) :
    LocAt w s →+ (∀ x : Proj.basicOpen 𝒜 (wProd w s), Loc 𝒜 x.1) where
  toFun z x := locMap x.1 (nmem_of_mem x) z
  map_zero' := funext fun _ => map_zero _
  map_add' z z' := funext fun _ => map_add _ z z'

include hw in
private theorem chartLocalization_mem (s : Finset ι) (e : ℕ) (z : twPart 𝒜 w s e) :
    chartLocalization s z.1 ∈ sectionsSubgroup (-(e : ℤ)) (Proj.basicOpen 𝒜 (wProd w s)) := by
  refine (AddSubgroup.closure_le ((sectionsSubgroup (-(e : ℤ))
    (Proj.basicOpen 𝒜 (wProd w s))).comap (chartLocalization s))).mpr ?_ z.2
  rintro _ ⟨m, j, a, ha, he, rfl⟩
  change (isLocallyFraction 𝒜 (-(e : ℤ))).pred (chartLocalization s (frac w s m a))
  have he' : (j : ℤ) + (e : ℤ) = ((m * s.card : ℕ) : ℤ) := by exact_mod_cast he
  intro x
  refine ⟨_, x.2, 𝟙 _, m * s.card, j, by omega, a, wProd w s ^ m, ha,
    wProd_pow_mem hw s m, fun y h => nmem_of_mem y (y.1.isPrime.mem_of_pow_mem m h), ?_⟩
  intro y
  exact locMap_mk y.1 (nmem_of_mem y) a m

private def chartSections (s : Finset ι) (e : ℕ) :
    twPart 𝒜 w s e →+ Γ(twistingSheaf 𝒜 (-(e : ℤ)), Proj.basicOpen 𝒜 (wProd w s)) where
  toFun z := mkSection (chartLocalization s z.1) (chartLocalization_mem hw s e z)
  map_zero' := ProjTwist.ext (map_zero (chartLocalization s))
  map_add' z z' := ProjTwist.ext (map_add (chartLocalization s) z.1 z'.1)

private def awayFraction {s : Finset ι} (hs : s.Nonempty) (e : ℕ) (z : twPart 𝒜 w s e) :
    awayDeg 𝒜 (wProd_mem hw s) (Finset.card_pos.mpr hs) (-(e : ℤ)) :=
  ⟨z.1, (mem_awayDeg_iff hw hs e z.1).2 z.2⟩

private theorem awayFraction_bijective {s : Finset ι} (hs : s.Nonempty) (e : ℕ) :
    Function.Bijective (awayFraction hw hs e) := by
  constructor
  · intro a b h
    have he := congrArg (fun z : awayDeg 𝒜 (wProd_mem hw s) (Finset.card_pos.mpr hs) (-(e : ℤ)) =>
      z.1) h
    exact Subtype.ext he
  · intro z
    exact ⟨⟨z.1, (mem_awayDeg_iff hw hs e z.1).1 z.2⟩, Subtype.ext rfl⟩

/-- A nonempty intersection has a degree-one factor in its defining product. -/
private theorem toSection_wProd_bijective {s : Finset ι} (hs : s.Nonempty) (k : ℤ) :
    Function.Bijective (toSection (wProd_mem hw s) (Finset.card_pos.mpr hs) k) := by
  obtain ⟨i, hi⟩ := hs
  let t := s.erase i
  have heq := Finset.insert_erase hi
  have hf : wProd w s = w i * wProd w t := by
    calc
      _ = wProd w (insert i t) := congrArg (wProd w) heq.symm
      _ = _ := Finset.prod_insert (Finset.notMem_erase i s)
  have hc : t.card + 1 = s.card :=
    (Finset.card_insert_of_notMem (Finset.notMem_erase i s)).symm.trans
      (congrArg Finset.card heq)
  have hb (d : ℕ) (hd : d = t.card + 1) (hf' : wProd w s ∈ 𝒜 d) :
      Function.Bijective (toSection hf' (show 0 < d by omega) k) := by
    subst d
    exact toSection_bijective (hw i) (wProd_mem hw t) hf hf' _
  exact hb s.card hc.symm (wProd_mem hw s)

private theorem chartSections_eq {s : Finset ι} (hs : s.Nonempty) (e : ℕ) :
    (chartSections hw s e : _ → _) =
      (toSection (wProd_mem hw s) (Finset.card_pos.mpr hs) (-(e : ℤ))) ∘ awayFraction hw hs e := by
  funext z
  exact ProjTwist.ext rfl

private theorem chartSections_bijective {s : Finset ι} (hs : s.Nonempty) (e : ℕ) :
    Function.Bijective (chartSections hw s e) := by
  rw [chartSections_eq hw hs]
  exact (toSection_wProd_bijective hw hs (-(e : ℤ))).comp (awayFraction_bijective hw hs e)

variable [LinearOrder ι]

private abbrev chartCech (e : ℕ) : FinsetCechDatum.{u} ι :=
  sheafCech ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).obj (twistingSheaf 𝒜 (-(e : ℤ))))
    ⊤ (projCover (𝒜 := 𝒜) w)

private abbrev intersection_le (s : Finset ι) :
    coverInter ⊤ (projCover (𝒜 := 𝒜) w) s ≤ Proj.basicOpen 𝒜 (wProd w s) :=
  (coverInter_projCover (𝒜 := 𝒜) (w := w) s).le

private def chartCechApp (s : Finset ι) (e : ℕ) :
    twPart 𝒜 w s e →+ (chartCech (𝒜 := 𝒜) (w := w) e).obj s :=
  ((twistingSheaf 𝒜 (-(e : ℤ))).presheaf.map
    (homOfLE (intersection_le (𝒜 := 𝒜) (w := w) s)).op).hom.comp
    (chartSections hw s e)

/-- The localized homogeneous Čech datum compares to actual sections of the negative twist. -/
def twistCechComparison (e : ℕ) : (twCech 𝒜 w hw e).Hom (chartCech (𝒜 := 𝒜) (w := w) e) where
  app s := chartCechApp hw s e
  comm {s t} h z := by
    apply ProjTwist.ext
    funext x
    let xt : Proj.basicOpen 𝒜 (wProd w t) := ⟨x.1, intersection_le t x.2⟩
    let xs : Proj.basicOpen 𝒜 (wProd w s) := ⟨x.1, intersection_le s (coverInter_anti h x.2)⟩
    exact (locMap_comp (resLoc w h) (RingHom.ext (resLoc_algebraMap h))
      x.1 (nmem_of_mem xt) (nmem_of_mem xs) z.1).symm

omit [LinearOrder ι] in
theorem twistCechComparison_app_val (s : Finset ι) (e : ℕ) (z : (twCech 𝒜 w hw e).obj s)
    (x : coverInter ⊤ (projCover (𝒜 := 𝒜) w) s) :
    val ((twistCechComparison hw e).app s z) x =
      locMap x.1 (nmem_of_mem ⟨x.1, intersection_le s x.2⟩) z.1 := rfl

omit [LinearOrder ι] in
theorem twistCechComparison_bijective {s : Finset ι} (hs : s.Nonempty) (e : ℕ) :
    Function.Bijective ((twistCechComparison hw e).app s) := by
  have he := coverInter_projCover (𝒜 := 𝒜) (w := w) s
  haveI : IsIso (homOfLE (intersection_le (𝒜 := 𝒜) (w := w) s)) := by
    have : homOfLE (intersection_le (𝒜 := 𝒜) (w := w) s) = eqToHom he := Subsingleton.elim _ _
    rw [this]
    infer_instance
  change Function.Bijective (chartCechApp hw s e)
  have hr := ConcreteCategory.bijective_of_isIso ((twistingSheaf 𝒜 (-(e : ℤ))).presheaf.map
    (homOfLE (intersection_le (𝒜 := 𝒜) (w := w) s)).op)
  exact hr.comp (chartSections_bijective hw hs e)

end GlobalTheory.SchemeCohomology.ProjTwist
