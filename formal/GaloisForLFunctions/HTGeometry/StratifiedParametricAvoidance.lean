import GaloisForLFunctions.HTGeometry.ClassicalStratifiedParametricAvoidance
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.MetricSpace.HausdorffDimension

open Set Filter Topology MeasureTheory Module
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem surjective_fderiv_of_surjective_parameter_fderiv
    {P H Y : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : P × H → Y) (p : P) (h : H)
    (hF : DifferentiableAt ℝ F (p, h))
    (hparameter : Function.Surjective (fderiv ℝ (fun v => F (v, h)) p)) :
    Function.Surjective (fderiv ℝ F (p, h)) := by
  have hslice :
      fderiv ℝ (fun v => F (v, h)) p =
        (fderiv ℝ F (p, h)).comp (ContinuousLinearMap.inl ℝ P H) := by
    have hc := fderiv_fun_comp (f := fun v : P => (v, h)) (g := F) p hF
      (hasFDerivAt_prodMk_left p h).differentiableAt
    rw [(hasFDerivAt_prodMk_left p h).fderiv] at hc
    exact hc
  intro y
  obtain ⟨v, hv⟩ := hparameter y
  refine ⟨(v, 0), ?_⟩
  have hv' := hv
  rw [hslice] at hv'
  simpa using hv'

theorem surjective_fderiv_comp_of_surjective_parameter_fderiv
    {P H Y Z : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : P × H → Y) (g : Y → Z) (p : P) (h : H)
    (hF : DifferentiableAt ℝ F (p, h))
    (hg : DifferentiableAt ℝ g (F (p, h)))
    (hparameter : Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hgSurj : Function.Surjective (fderiv ℝ g (F (p, h)))) :
    Function.Surjective (fderiv ℝ (fun x => g (F x)) (p, h)) := by
  have hfull := surjective_fderiv_of_surjective_parameter_fderiv
    F p h hF hparameter
  rw [fderiv_fun_comp (f := F) (g := g) (p, h) hg hF]
  exact hgSurj.comp hfull

theorem exists_nhds_dimH_parameter_image_levelSet_le_finrank_ker
    {P H Z : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (phi : P × H → Z) (x : P × H)
    (hphi : ContDiffAt ℝ 1 phi x)
    (hsurj : Function.Surjective (fderiv ℝ phi x)) :
    ∃ N ∈ 𝓝 x,
      dimH (Prod.fst '' (N ∩ phi ⁻¹' {phi x})) ≤
        Module.finrank ℝ (fderiv ℝ phi x).ker := by
  let L : (P × H) →L[ℝ] Z := fderiv ℝ phi x
  have hstrict : HasStrictFDerivAt phi L x := hphi.hasStrictFDerivAt one_ne_zero
  have hrange : LinearMap.range (L : (P × H) →ₗ[ℝ] Z) = ⊤ := by
    exact LinearMap.range_eq_top.mpr hsurj
  let psi : L.ker → P × H :=
    hstrict.implicitFunction phi L hrange (phi x)
  have hpsiStrict : HasStrictFDerivAt psi L.ker.subtypeL 0 := by
    simpa only [psi] using hstrict.to_implicitFunction hrange
  obtain ⟨C, V, hV, hpsiLip⟩ := hpsiStrict.exists_lipschitzOnWith
  let e := hstrict.implicitToOpenPartialHomeomorph phi L hrange
  let coord : P × H → L.ker := fun y => (e y).2
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
  let N : Set (P × H) :=
    {y | hstrict.implicitFunction phi L hrange (phi y) (coord y) = y} ∩ coord ⁻¹' V
  have hN : N ∈ 𝓝 x := inter_mem himplicit hcoordV
  refine ⟨N, hN, ?_⟩
  have hsubset : Prod.fst '' (N ∩ phi ⁻¹' {phi x}) ⊆ Prod.fst '' (psi '' V) := by
    rintro p ⟨y, ⟨hyN, hyLevel⟩, rfl⟩
    refine ⟨y, ?_, rfl⟩
    have hyEq : hstrict.implicitFunction phi L hrange (phi y) (coord y) = y := hyN.1
    have hyV : coord y ∈ V := hyN.2
    refine ⟨coord y, hyV, ?_⟩
    rw [show phi y = phi x by simpa using hyLevel] at hyEq
    exact hyEq
  calc
    dimH (Prod.fst '' (N ∩ phi ⁻¹' {phi x})) ≤ dimH (Prod.fst '' (psi '' V)) :=
      dimH_mono hsubset
    _ = dimH ((Prod.fst ∘ psi) '' V) := by
      apply congrArg dimH
      ext p
      constructor
      · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨psi v, ⟨v, hv, rfl⟩, rfl⟩
    _ ≤ dimH V := by
      exact ((ContinuousLinearMap.fst ℝ P H).lipschitz.comp_lipschitzOnWith
        hpsiLip).dimH_image_le
    _ ≤ dimH (Set.univ : Set L.ker) := dimH_mono (subset_univ V)
    _ = Module.finrank ℝ (fderiv ℝ phi x).ker := by
      simpa only [L] using Real.dimH_univ_eq_finrank L.ker

theorem finrank_ker_lt_parameter_finrank_of_surjective
    {P H : Type*} {m c : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (L : (P × H) →L[ℝ] (Fin m → ℝ))
    (hL : Function.Surjective L) (hcm : c ≤ m)
    (hdim : Module.finrank ℝ H < c) :
    Module.finrank ℝ L.ker < Module.finrank ℝ P := by
  have hrange : LinearMap.range (L : (P × H) →ₗ[ℝ] (Fin m → ℝ)) = ⊤ :=
    LinearMap.range_eq_top.mpr hL
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (L : (P × H) →ₗ[ℝ] (Fin m → ℝ))
  rw [hrange, finrank_top, Module.finrank_fin_fun,
    Module.finrank_prod] at hrank
  omega

theorem exists_nhds_dimH_parameter_image_preimage_stratum_lt
    {P H Y : Type*} {S : Set Y} {c : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : P × H → Y) (U : Set H) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hregular : IsLocalRegularLevelSetOfCodimAtLeast S c)
    (hdim : Module.finrank ℝ H < c)
    (x : P × H) (hxU : x.2 ∈ U) (hxS : F x ∈ S) :
    ∃ N ∈ 𝓝 x, dimH (Prod.fst '' (N ∩ F ⁻¹' S)) ≤
      (Module.finrank ℝ P - 1 : ℕ) := by
  obtain ⟨m, hcm, V, hVopen, hxV, g, hg, hS, hgSurjWithin⟩ := hregular (F x) hxS
  have hdomainOpen : IsOpen ((Set.univ : Set P) ×ˢ U) := isOpen_univ.prod hU
  have hxDomain : x ∈ (Set.univ : Set P) ×ˢ U := ⟨mem_univ _, hxU⟩
  have hFAt : ContDiffAt ℝ ⊤ F x :=
    (hF x hxDomain).contDiffAt (hdomainOpen.mem_nhds hxDomain)
  have hgAt : ContDiffAt ℝ ⊤ g (F x) :=
    (hg (F x) hxV).contDiffAt (hVopen.mem_nhds hxV)
  let phi : P × H → (Fin m → ℝ) := fun y => g (F y)
  have hphiAt : ContDiffAt ℝ 1 phi x := by
    exact (hgAt.of_le (by simp)).comp x (hFAt.of_le (by simp))
  have hgSurj : Function.Surjective (fderiv ℝ g (F x)) := by
    simpa only [fderivWithin_of_isOpen hVopen hxV] using hgSurjWithin (F x) hxV
  have hphiSurj : Function.Surjective (fderiv ℝ phi x) := by
    exact surjective_fderiv_comp_of_surjective_parameter_fderiv
      F g x.1 x.2 (hFAt.differentiableAt (by simp))
        (hgAt.differentiableAt (by simp)) (hparameter x.1 x.2 hxU) hgSurj
  obtain ⟨N0, hN0, hN0dim⟩ :=
    exists_nhds_dimH_parameter_image_levelSet_le_finrank_ker phi x hphiAt hphiSurj
  have hkerlt : Module.finrank ℝ (fderiv ℝ phi x).ker < Module.finrank ℝ P :=
    finrank_ker_lt_parameter_finrank_of_surjective
      (fderiv ℝ phi x) hphiSurj hcm hdim
  let N : Set (P × H) := N0 ∩ F ⁻¹' V
  have hFV : F ⁻¹' V ∈ 𝓝 x := hFAt.continuousAt (hVopen.mem_nhds hxV)
  have hN : N ∈ 𝓝 x := inter_mem hN0 hFV
  refine ⟨N, hN, ?_⟩
  have hsubset : Prod.fst '' (N ∩ F ⁻¹' S) ⊆
      Prod.fst '' (N0 ∩ phi ⁻¹' {phi x}) := by
    rintro p ⟨y, ⟨hyN, hyS⟩, rfl⟩
    refine ⟨y, ⟨hyN.1, ?_⟩, rfl⟩
    have hgy : g (F y) = 0 := (hS (F y) hyN.2).mp hyS
    have hgx : g (F x) = 0 := (hS (F x) hxV).mp hxS
    simp only [mem_preimage, mem_singleton_iff, phi, hgy, hgx]
  have hkerle : Module.finrank ℝ (fderiv ℝ phi x).ker ≤
      Module.finrank ℝ P - 1 := by omega
  have hkerle' :
      (Module.finrank ℝ (fderiv ℝ phi x).ker : ℝ≥0∞) ≤
        (Module.finrank ℝ P - 1 : ℕ) := by
    exact_mod_cast hkerle
  exact (dimH_mono hsubset |>.trans hN0dim).trans hkerle'

theorem dimH_parameter_preimage_stratum_le_pred
    {P H Y : Type*} {S : Set Y} {c : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : P × H → Y) (U : Set H) (K : Set H) (hU : IsOpen U)
    (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hregular : IsLocalRegularLevelSetOfCodimAtLeast S c)
    (hdim : Module.finrank ℝ H < c) :
    dimH {p : P | ∃ h ∈ K, F (p, h) ∈ S} ≤
      (Module.finrank ℝ P - 1 : ℕ) := by
  let T : Set (P × H) := {x | x.2 ∈ K ∧ F x ∈ S}
  have hlocal : ∀ x ∈ T, ∃ N ∈ 𝓝 x,
      dimH (Prod.fst '' (N ∩ F ⁻¹' S)) ≤
        (Module.finrank ℝ P - 1 : ℕ) := by
    intro x hx
    exact exists_nhds_dimH_parameter_image_preimage_stratum_lt
      F U hU hF hparameter hregular hdim x (hKU hx.1) hx.2
  choose N hN hNdim using hlocal
  have hT : IsLindelof T := HereditarilyLindelofSpace.isLindelof T
  obtain ⟨t, htCount, hcover⟩ := hT.elim_nhds_subcover' N hN
  letI : Countable t := htCount.to_subtype
  have hbadEq : {p : P | ∃ h ∈ K, F (p, h) ∈ S} = Prod.fst '' T := by
    ext p
    constructor
    · rintro ⟨h, hhK, hhS⟩
      exact ⟨(p, h), ⟨hhK, hhS⟩, rfl⟩
    · rintro ⟨x, hxT, rfl⟩
      exact ⟨x.2, hxT.1, hxT.2⟩
  rw [hbadEq]
  have hsubset : Prod.fst '' T ⊆
      ⋃ x : t, Prod.fst '' (N x x.1.2 ∩ F ⁻¹' S) := by
    rintro p ⟨x, hxT, rfl⟩
    have hxCover := hcover hxT
    simp only [mem_iUnion] at hxCover ⊢
    obtain ⟨y, hyT, hxy⟩ := hxCover
    refine ⟨⟨y, hyT⟩, ?_⟩
    exact ⟨x, ⟨hxy, hxT.2⟩, rfl⟩
  refine (dimH_mono hsubset).trans ?_
  rw [dimH_iUnion]
  exact iSup_le fun x => hNdim x x.1.2

theorem parameter_finrank_pos_of_hits_regular_stratum
    {P H Y : Type*} {S : Set Y} {c : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : P × H → Y) (U : Set H) (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hregular : IsLocalRegularLevelSetOfCodimAtLeast S c)
    (hdim : Module.finrank ℝ H < c)
    (p : P) (h : H) (hhU : h ∈ U) (hS : F (p, h) ∈ S) :
    0 < Module.finrank ℝ P := by
  obtain ⟨m, hcm, V, hVopen, hxV, g, hg, -, hgSurjWithin⟩ :=
    hregular (F (p, h)) hS
  have hdomainOpen : IsOpen ((Set.univ : Set P) ×ˢ U) := isOpen_univ.prod hU
  have hxDomain : (p, h) ∈ (Set.univ : Set P) ×ˢ U := ⟨mem_univ _, hhU⟩
  have hFAt : ContDiffAt ℝ ⊤ F (p, h) :=
    (hF (p, h) hxDomain).contDiffAt (hdomainOpen.mem_nhds hxDomain)
  have hgAt : ContDiffAt ℝ ⊤ g (F (p, h)) :=
    (hg (F (p, h)) hxV).contDiffAt (hVopen.mem_nhds hxV)
  let phi : P × H → (Fin m → ℝ) := fun y => g (F y)
  have hgSurj : Function.Surjective (fderiv ℝ g (F (p, h))) := by
    simpa only [fderivWithin_of_isOpen hVopen hxV] using
      hgSurjWithin (F (p, h)) hxV
  have hphiSurj : Function.Surjective (fderiv ℝ phi (p, h)) := by
    exact surjective_fderiv_comp_of_surjective_parameter_fderiv
      F g p h (hFAt.differentiableAt (by simp))
        (hgAt.differentiableAt (by simp)) (hparameter p h hhU) hgSurj
  have hkerlt : Module.finrank ℝ (fderiv ℝ phi (p, h)).ker <
      Module.finrank ℝ P :=
    finrank_ker_lt_parameter_finrank_of_surjective
      (fderiv ℝ phi (p, h)) hphiSurj hcm hdim
  omega

theorem dimH_parameter_preimage_finite_stratification_le_pred
    {P H Y : Type*} {bad : Set Y} {c : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : P × H → Y) (U : Set H) (K : Set H) (hU : IsOpen U)
    (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c) :
    dimH {p : P | ∃ h ∈ K, F (p, h) ∈ bad} ≤
      (Module.finrank ℝ P - 1 : ℕ) := by
  have hbadEq : {p : P | ∃ h ∈ K, F (p, h) ∈ bad} =
      ⋃ i, {p : P | ∃ h ∈ K, F (p, h) ∈ hstrata.stratum i} := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨h, hhK, hhbad⟩
      rw [hstrata.cover] at hhbad
      obtain ⟨i, hi⟩ := mem_iUnion.mp hhbad
      exact ⟨i, h, hhK, hi⟩
    · rintro ⟨i, h, hhK, hi⟩
      refine ⟨h, hhK, ?_⟩
      rw [hstrata.cover]
      exact mem_iUnion.mpr ⟨i, hi⟩
  rw [hbadEq, dimH_iUnion]
  exact iSup_le fun i => dimH_parameter_preimage_stratum_le_pred
    F U K hU hKU hF hparameter (hstrata.regular i) hdim

theorem compactConfigurationAvoidance_dense_of_finiteRegularStratification
    {P H Y : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (F : P × H → Y) (bad : Set Y) (c : ℕ)
    (U : Set H) (K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U))
    (hparameter : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hstrata : FiniteRegularStratification bad c)
    (hdim : Module.finrank ℝ H < c) :
    Dense (compactConfigurationAvoidance F bad K) := by
  let B : Set P := {p | ∃ h ∈ K, F (p, h) ∈ bad}
  have havoidEq : compactConfigurationAvoidance F bad K = Bᶜ := by
    ext p
    simp only [compactConfigurationAvoidance, B, mem_setOf_eq, mem_compl_iff]
    push Not
    rfl
  rw [havoidEq]
  by_cases hB : B.Nonempty
  · obtain ⟨p, hp⟩ := hB
    obtain ⟨h, hhK, hhbad⟩ := hp
    have hhcover := hhbad
    rw [hstrata.cover] at hhcover
    obtain ⟨i, hi⟩ := mem_iUnion.mp hhcover
    have hPpos : 0 < Module.finrank ℝ P :=
      parameter_finrank_pos_of_hits_regular_stratum
        F U hU hF hparameter (hstrata.regular i) hdim p h (hKU hhK) hi
    have hdimB : dimH B ≤ (Module.finrank ℝ P - 1 : ℕ) := by
      exact dimH_parameter_preimage_finite_stratification_le_pred
        F U K hU hKU hF hparameter hstrata hdim
    have hpredlt : ((Module.finrank ℝ P - 1 : ℕ) : ℝ≥0∞) <
        Module.finrank ℝ P := by
      exact_mod_cast Nat.sub_lt hPpos (by omega : 0 < 1)
    exact dense_compl_of_dimH_lt_finrank (hdimB.trans_lt hpredlt)
  · have hBempty : B = ∅ := not_nonempty_iff_eq_empty.mp hB
    rw [hBempty]
    simp

end
end GaloisForLFunctions.HTGeometry
