import GaloisForLFunctions.HTGeometry.StratifiedParametricAvoidance

/-!
# Hausdorff dimension of regular level-set strata

This module proves both dimension inequalities needed to read codimension from the project's local
regular-level-set interface.  The upper bound uses implicit-function charts and a Lindelöf cover.
The lower bound uses the same implicit parametrization together with its locally antilipschitz
estimate.  Consequently a finite zero-codimension stratification can be upgraded to a genuine
codimension-`c` stratification from a global Hausdorff-dimension bound.
-/

open Set Filter Topology MeasureTheory Module
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem exists_nhds_dimH_levelSet_le_finrank_ker
    {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (phi : E → Z) (x : E)
    (hphi : ContDiffAt ℝ 1 phi x)
    (hsurj : Function.Surjective (fderiv ℝ phi x)) :
    ∃ N ∈ 𝓝 x,
      dimH (N ∩ phi ⁻¹' {phi x}) ≤ Module.finrank ℝ (fderiv ℝ phi x).ker := by
  let L : E →L[ℝ] Z := fderiv ℝ phi x
  have hstrict : HasStrictFDerivAt phi L x := hphi.hasStrictFDerivAt one_ne_zero
  have hrange : LinearMap.range (L : E →ₗ[ℝ] Z) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let psi : L.ker → E := hstrict.implicitFunction phi L hrange (phi x)
  have hpsiStrict : HasStrictFDerivAt psi L.ker.subtypeL 0 := by
    simpa only [psi] using hstrict.to_implicitFunction hrange
  obtain ⟨C, V, hV, hpsiLip⟩ := hpsiStrict.exists_lipschitzOnWith
  let e := hstrict.implicitToOpenPartialHomeomorph phi L hrange
  let coord : E → L.ker := fun y => (e y).2
  have hxsource : x ∈ e.source := hstrict.mem_implicitToOpenPartialHomeomorph_source hrange
  have hcoordCont : ContinuousAt coord x := by
    exact continuous_snd.continuousAt.comp (e.continuousAt hxsource)
  have hcoord0 : coord x = 0 := by
    simp [coord, e, L]
  have hcoordV : coord ⁻¹' V ∈ 𝓝 x := by
    apply hcoordCont
    simpa only [hcoord0] using hV
  have himplicit : ∀ᶠ y in 𝓝 x,
      hstrict.implicitFunction phi L hrange (phi y) (coord y) = y := by
    simpa only [coord, e] using hstrict.eq_implicitFunction hrange
  let N : Set E :=
    {y | hstrict.implicitFunction phi L hrange (phi y) (coord y) = y} ∩ coord ⁻¹' V
  have hN : N ∈ 𝓝 x := inter_mem himplicit hcoordV
  refine ⟨N, hN, ?_⟩
  have hsubset : N ∩ phi ⁻¹' {phi x} ⊆ psi '' V := by
    rintro y ⟨hyN, hyLevel⟩
    have hyEq : hstrict.implicitFunction phi L hrange (phi y) (coord y) = y := hyN.1
    have hyV : coord y ∈ V := hyN.2
    refine ⟨coord y, hyV, ?_⟩
    rw [show phi y = phi x by simpa using hyLevel] at hyEq
    exact hyEq
  calc
    dimH (N ∩ phi ⁻¹' {phi x}) ≤ dimH (psi '' V) := dimH_mono hsubset
    _ ≤ dimH V := hpsiLip.dimH_image_le
    _ ≤ dimH (Set.univ : Set L.ker) := dimH_mono (subset_univ V)
    _ = Module.finrank ℝ (fderiv ℝ phi x).ker := by
      simpa only [L] using Real.dimH_univ_eq_finrank L.ker

theorem finrank_ker_eq_sub_of_surjective
    {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (L : E →L[ℝ] Z) (hL : Function.Surjective L) :
    Module.finrank ℝ L.ker = Module.finrank ℝ E - Module.finrank ℝ Z := by
  have hrange : LinearMap.range (L : E →ₗ[ℝ] Z) = ⊤ :=
    LinearMap.range_eq_top.mpr hL
  have hrank := LinearMap.finrank_range_add_finrank_ker (L : E →ₗ[ℝ] Z)
  rw [hrange, finrank_top] at hrank
  omega

theorem dimH_le_finrank_sub_of_isLocalRegularLevelSetOfCodimAtLeast
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} {c : ℕ}
    (hregular : IsLocalRegularLevelSetOfCodimAtLeast S c) :
    dimH S ≤ (Module.finrank ℝ E - c : ℕ) := by
  have hlocal : ∀ x ∈ S, ∃ N ∈ 𝓝 x,
      dimH (N ∩ S) ≤ (Module.finrank ℝ E - c : ℕ) := by
    intro x hx
    obtain ⟨m, hcm, U, hUopen, hxU, g, hg, hS, hsurjWithin⟩ := hregular x hx
    have hgAt : ContDiffAt ℝ 1 g x :=
      (hg x hxU).contDiffAt (hUopen.mem_nhds hxU) |>.of_le (by simp)
    have hsurj : Function.Surjective (fderiv ℝ g x) := by
      simpa only [fderivWithin_of_isOpen hUopen hxU] using hsurjWithin x hxU
    obtain ⟨N0, hN0, hN0dim⟩ :=
      exists_nhds_dimH_levelSet_le_finrank_ker g x hgAt hsurj
    let N := N0 ∩ U
    have hN : N ∈ 𝓝 x := inter_mem hN0 (hUopen.mem_nhds hxU)
    refine ⟨N, hN, ?_⟩
    have hgzero : g x = 0 := (hS x hxU).mp hx
    have hsubset : N ∩ S ⊆ N0 ∩ g ⁻¹' {g x} := by
      rintro y ⟨⟨hyN0, hyU⟩, hyS⟩
      exact ⟨hyN0, by simpa [hgzero] using (hS y hyU).mp hyS⟩
    have hker := finrank_ker_eq_sub_of_surjective (fderiv ℝ g x) hsurj
    have hker' : (Module.finrank ℝ (fderiv ℝ g x).ker : ℝ≥0∞) =
        (Module.finrank ℝ E - m : ℕ) := by
      rw [hker, Module.finrank_fin_fun]
    calc
      dimH (N ∩ S) ≤ dimH (N0 ∩ g ⁻¹' {g x}) := dimH_mono hsubset
      _ ≤ Module.finrank ℝ (fderiv ℝ g x).ker := hN0dim
      _ = ((Module.finrank ℝ E - m : ℕ) : ℝ≥0∞) := hker'
      _ ≤ ((Module.finrank ℝ E - c : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.sub_le_sub_left hcm (Module.finrank ℝ E)
  have hL : IsLindelof S := HereditarilyLindelofSpace.isLindelof S
  choose N hN hNdim using hlocal
  obtain ⟨t, htCount, hcover⟩ := hL.elim_nhds_subcover' N hN
  letI : Countable t := htCount.to_subtype
  have hsubset : S ⊆ ⋃ x : t, N x x.1.2 ∩ S := by
    intro x hx
    have hxCover := hcover hx
    simp only [mem_iUnion] at hxCover ⊢
    obtain ⟨y, hyT, hxy⟩ := hxCover
    exact ⟨⟨y, hyT⟩, hxy, hx⟩
  refine (dimH_mono hsubset).trans ?_
  rw [dimH_iUnion]
  exact iSup_le fun x => hNdim x x.1.2

theorem finrank_ker_le_dimH_of_mem_regularLevelSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} {m : ℕ} {x : E}
    (hx : x ∈ S)
    (U : Set E) (hUopen : IsOpen U) (hxU : x ∈ U)
    (g : E → (Fin m → ℝ)) (hg : ContDiffOn ℝ ⊤ g U)
    (hS : ∀ y ∈ U, y ∈ S ↔ g y = 0)
    (hsurjWithin : ∀ y ∈ U, Function.Surjective (fderivWithin ℝ g U y)) :
    Module.finrank ℝ (fderiv ℝ g x).ker ≤ dimH S := by
  have hgAt : ContDiffAt ℝ 1 g x :=
    (hg x hxU).contDiffAt (hUopen.mem_nhds hxU) |>.of_le (by simp)
  have hsurj : Function.Surjective (fderiv ℝ g x) := by
    simpa only [fderivWithin_of_isOpen hUopen hxU] using hsurjWithin x hxU
  let L : E →L[ℝ] (Fin m → ℝ) := fderiv ℝ g x
  have hstrict : HasStrictFDerivAt g L x := hgAt.hasStrictFDerivAt one_ne_zero
  have hrange : LinearMap.range (L : E →ₗ[ℝ] (Fin m → ℝ)) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let psi : L.ker → E := hstrict.implicitFunction g L hrange (g x)
  have hpsiStrict : HasStrictFDerivAt psi L.ker.subtypeL 0 := by
    simpa only [psi] using hstrict.to_implicitFunction hrange
  have hInducing : Topology.IsInducing (L.ker.subtypeL : L.ker → E) := by
    simpa only [Submodule.coe_subtypeL] using
      (isometry_subtype_coe : Isometry ((↑) : L.ker → E)).isUniformInducing.isInducing
  have hTheta := hpsiStrict.isTheta_sub hInducing
  obtain ⟨C, hCpos, hC⟩ := hTheta.isBigO_symm.exists_pos
  obtain ⟨V0, hV0open, h0V0, hV0bound⟩ := exists_nhds_square hC.bound
  have hpsiU : psi ⁻¹' U ∈ 𝓝 0 := by
    have hpsiT : Tendsto psi (𝓝 0) (𝓝 x) := by
      simpa only [psi] using
        hstrict.tendsto_implicitFunction hrange tendsto_const_nhds tendsto_id
    exact hpsiT (hUopen.mem_nhds hxU)
  have hmap : ∀ᶠ v in 𝓝 (0 : L.ker), g (psi v) = g x := by
    have hpairs := hstrict.map_implicitFunction_eq hrange
    have ht : Tendsto (fun v : L.ker => (g x, v)) (𝓝 0) (𝓝 (g x, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact hpairs.filter_mono ht
  let V : Set L.ker := V0 ∩ psi ⁻¹' U ∩ {v | g (psi v) = g x}
  have hV : V ∈ 𝓝 0 :=
    inter_mem (inter_mem (hV0open.mem_nhds h0V0) hpsiU) hmap
  have hanti : AntilipschitzWith ⟨C, hCpos.le⟩ (V.restrict psi) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have huv := hV0bound (show (u.1, v.1) ∈ V0 ×ˢ V0 from
      ⟨u.2.1.1, v.2.1.1⟩)
    simpa only [Set.restrict_apply, dist_eq_norm, Subtype.dist_eq,
      NNReal.smul_def, NNReal.coe_mk] using huv
  have hpsiS : psi '' V ⊆ S := by
    rintro y ⟨v, hv, rfl⟩
    have hxzero : g x = 0 := (hS x hxU).mp hx
    exact (hS (psi v) hv.1.2).mpr (by simpa [hxzero] using hv.2)
  have hdimV : dimH V = Module.finrank ℝ L.ker := Real.dimH_of_mem_nhds hV
  have hdimSub : dimH V ≤ dimH (psi '' V) := by
    have h := hanti.le_dimH_image (Set.univ : Set V)
    have hdom : dimH (Set.univ : Set V) = dimH V := by
      symm
      simpa using
        ((isometry_subtype_coe : Isometry ((↑) : V → L.ker)).dimH_image
          (Set.univ : Set V))
    have himage : (V.restrict psi) '' (Set.univ : Set V) = psi '' V := by
      ext y
      constructor
      · rintro ⟨v, -, rfl⟩
        exact ⟨v.1, v.2, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨⟨v, hv⟩, Set.mem_univ _, rfl⟩
    rwa [hdom, himage] at h
  rw [← hdimV]
  exact hdimSub.trans (dimH_mono hpsiS)

/-- Upgrade a finite regular stratification once the whole set has the corresponding Hausdorff
dimension bound. -/
noncomputable def FiniteRegularStratification.of_dimH_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} {c : ℕ}
    (hstrata : FiniteRegularStratification S 0)
    (hcE : c ≤ Module.finrank ℝ E)
    (hdim : dimH S ≤ (Module.finrank ℝ E - c : ℕ)) :
    FiniteRegularStratification S c := by
  refine {
    numberOfStrata := hstrata.numberOfStrata
    stratum := hstrata.stratum
    pairwise_disjoint := hstrata.pairwise_disjoint
    cover := hstrata.cover
    regular := ?_
  }
  intro i y hy
  obtain ⟨m, -, U, hUopen, hyU, g, hg, hzero, hsurjWithin⟩ :=
    hstrata.regular i y hy
  have hsurj : Function.Surjective (fderiv ℝ g y) := by
    simpa only [fderivWithin_of_isOpen hUopen hyU] using hsurjWithin y hyU
  have hrank := LinearMap.finrank_range_add_finrank_ker
    ((fderiv ℝ g y : E →L[ℝ] (Fin m → ℝ)) : E →ₗ[ℝ] (Fin m → ℝ))
  have hrange : LinearMap.range
      ((fderiv ℝ g y : E →L[ℝ] (Fin m → ℝ)) : E →ₗ[ℝ] (Fin m → ℝ)) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [hrange, finrank_top, Module.finrank_fin_fun] at hrank
  have hlower := finrank_ker_le_dimH_of_mem_regularLevelSet
    hy U hUopen hyU g hg hzero hsurjWithin
  have hstratumSub : hstrata.stratum i ⊆ S := by
    intro z hz
    rw [hstrata.cover]
    exact Set.mem_iUnion.mpr ⟨i, hz⟩
  have hchain : (Module.finrank ℝ E - m : ℕ) ≤
      Module.finrank ℝ E - c := by
    have hcast : ((Module.finrank ℝ E - m : ℕ) : ℝ≥0∞) ≤
        ((Module.finrank ℝ E - c : ℕ) : ℝ≥0∞) := by
      calc
        ((Module.finrank ℝ E - m : ℕ) : ℝ≥0∞) =
            Module.finrank ℝ (fderiv ℝ g y).ker := by
          norm_cast
          omega
        _ ≤ dimH (hstrata.stratum i) := hlower
        _ ≤ dimH S := dimH_mono hstratumSub
        _ ≤ ((Module.finrank ℝ E - c : ℕ) : ℝ≥0∞) := hdim
    exact_mod_cast hcast
  have hcm : c ≤ m := by omega
  exact ⟨m, hcm, U, hUopen, hyU, g, hg, hzero, hsurjWithin⟩

end

end GaloisForLFunctions.HTGeometry
