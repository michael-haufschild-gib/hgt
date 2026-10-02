import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetThetaDomain

/-!
# Exact closure of the actual two-prime Fourier-jet theta action

Every prime's literal depth tower is a core for the same even multiplication graph.
Distinct prime towers are algebraically disjoint, so their combined finite theta action
is single-valued. At every nonzero theta parameter, the difference between their two
limiting source actions is invertible. The graph closure is consequently the entire
product of completed even jet graphs. At parameter zero it is exactly the original
closed neutral graph. Thus a closed extension exists exactly at zero.

All source and response coordinates are retained. No assertion about the complete
mixed-prime modular cubic follows from nonclosability of its theta factor.
-/

open Complex MeasureTheory Set Filter Topology
open scoped LinearPMap
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The two separate multiplication graphs, before Fourier-jet assembly. -/
abbrev BurnolJetRaw := (SoninL2 × SoninL2) × (SoninL2 × SoninL2)

def burnolJetRawTheta (u w : ℂ) : BurnolJetRaw →L[ℂ] BurnolJetRaw where
  toFun z := (u • z.1+w • z.2,w • z.1+(1-u) • z.2)
  map_add' z t := by
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> module
  map_smul' a z := by
    apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,RingHom.id_apply] <;> module
  cont := by fun_prop

def burnolJetThetaRelationAssembly (p : Nat.Primes) (a : ℝ) :
    BurnolJetRaw →L[ℂ] (BurnolJetAmbient × BurnolJetAmbient) :=
  burnolJetGraphAssembly.prod (burnolJetGraphAssembly ∘L
    burnolJetRawTheta ((primeBurnolThetaVisibility a p : ℂ)^2)
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)))

/-- Actual theta graph on a single literal finite prime-depth source core. -/
def primeBurnolJetThetaCoreRelation (p : Nat.Primes) (a : ℝ) :
    Submodule ℂ (BurnolJetAmbient × BurnolJetAmbient) :=
  ((primeBurnolSquareGraphCore p).prod (primeBurnolSquareGraphCore p)).map
    (burnolJetThetaRelationAssembly p a).toLinearMap

/-- Retain both prime actions and every finite linear combination. -/
def primeBurnolJetTwoPrimeThetaRelation (p q : Nat.Primes) (a : ℝ) :
    Submodule ℂ (BurnolJetAmbient × BurnolJetAmbient) :=
  primeBurnolJetThetaCoreRelation p a ⊔ primeBurnolJetThetaCoreRelation q a

theorem burnolJetRawTheta_mem_prod (m : Submodule ℂ (SoninL2 × SoninL2))
    (u w : ℂ) {z : BurnolJetRaw} (hz : z ∈ m.prod m) :
    burnolJetRawTheta u w z ∈ m.prod m :=
  ⟨m.add_mem (m.smul_mem u hz.1) (m.smul_mem w hz.2),
    m.add_mem (m.smul_mem w hz.1) (m.smul_mem (1-u) hz.2)⟩

theorem burnolJetThetaRelationAssembly_source (p : Nat.Primes) (a : ℝ)
    (f g : burnolSquarePosition.domain) :
    burnolJetThetaRelationAssembly p a
      (((f : SoninL2),burnolSquarePosition f),((g : SoninL2),burnolSquarePosition g)) =
    (burnolJetGraphVector f g,burnolJetGraphLinear (burnolJetPrimeThetaSource p a (f,g))) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · let u : ℂ := (primeBurnolThetaVisibility a p : ℂ)^2
        let w : ℂ := (primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ)
        change (u • burnolSquarePosition f+w • burnolSquarePosition g)+
          fourierUnitary (w • burnolSquarePosition f+(1-u) • burnolSquarePosition g) =
          burnolSquarePosition.toFun (u • f+w • g)+
          fourierUnitary (burnolSquarePosition.toFun (w • f+(1-u) • g))
        simp only [map_add,map_smul]
        rfl

private theorem core_le_even (p : Nat.Primes) :
    primeBurnolSquareGraphCore p ≤ primeBurnolEvenSquareGraph := by
  rw [← primeBurnolSquareGraphCore_closure p]
  exact (primeBurnolSquareGraphCore p).le_topologicalClosure

theorem primeBurnolEvenFeatureLp_linearIndependent :
    LinearIndependent ℂ primeBurnolEvenFeatureLp := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let e := (Fintype.equivFin s).symm
  let pe : Fin (Fintype.card s) ↪ Nat.Primes × ℕ :=
    ⟨fun i => (e i).val,Subtype.val_injective.comp e.injective⟩
  have h := (primeBurnolFourierPair_linearIndependent pe).comp Sum.inl Sum.inl_injective
  exact (linearIndependent_equiv e).mp h

theorem primeBurnolSquareGraphCore_disjoint {p q : Nat.Primes} (hpq : p≠q) :
    Disjoint (primeBurnolSquareGraphCore p) (primeBurnolSquareGraphCore q) := by
  let v : Nat.Primes × ℕ → SoninL2 × SoninL2 :=
    fun pe => (primeBurnolEvenFeatureLp pe,burnolSquarePosition (primeBurnolSquareColumn pe))
  have hv : LinearIndependent ℂ v :=
    primeBurnolEvenFeatureLp_linearIndependent.of_comp (LinearMap.fst ℂ SoninL2 SoninL2)
  have hp (r : Nat.Primes) :
      v '' {pe | pe.1=r} = range (fun n => v (r,n)) := by
    ext z
    constructor
    · rintro ⟨⟨r',n⟩,h,rfl⟩
      exact ⟨n,by cases h; rfl⟩
    · rintro ⟨n,rfl⟩
      exact ⟨(r,n),rfl,rfl⟩
  have hd : Disjoint {pe : Nat.Primes × ℕ | pe.1=p} {pe | pe.1=q} := by
    rw [Set.disjoint_left]
    intro pe hp hq
    exact hpq (hp.symm.trans hq)
  simpa only [hp,primeBurnolSquareGraphCore,v] using hv.disjoint_span_image hd

private theorem raw_assembly_zero {z : BurnolJetRaw}
    (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph)
    (h0 : burnolJetGraphAssembly z=0) : z=0 := by
  have h1 : z.1.1=0 := congrArg (fun t : BurnolJetAmbient => t.1.1) h0
  have h2 : z.2.1=0 := congrArg (fun t : BurnolJetAmbient => t.1.2) h0
  obtain ⟨f,hf,hM⟩ := burnolSquarePosition.mem_graph_iff.mp hz.1.1
  obtain ⟨g,hg,hN⟩ := burnolSquarePosition.mem_graph_iff.mp hz.2.1
  have hf0 : f=0 := Subtype.ext (hf.trans h1)
  have hg0 : g=0 := Subtype.ext (hg.trans h2)
  have h3 : z.1.2=0 := hM.symm.trans (by rw [hf0]; exact map_zero burnolSquarePosition.toFun)
  have h4 : z.2.2=0 := hN.symm.trans (by rw [hg0]; exact map_zero burnolSquarePosition.toFun)
  exact Prod.ext (Prod.ext h1 h3) (Prod.ext h2 h4)

/-- The finite relation is genuinely single-valued; nonuniqueness can only enter on closure. -/
theorem primeBurnolJetTwoPrimeThetaRelation_singleValued {p q : Nat.Primes} (hpq : p≠q)
    (a : ℝ) {z : BurnolJetAmbient × BurnolJetAmbient}
    (hz : z ∈ primeBurnolJetTwoPrimeThetaRelation p q a) (h0 : z.1=0) : z.2=0 := by
  obtain ⟨x,⟨v,hv,rfl⟩,y,⟨w,hw,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hz
  change burnolJetGraphAssembly v+burnolJetGraphAssembly w=0 at h0
  rw [← map_add] at h0
  have hv' : v ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph :=
    ⟨core_le_even p hv.1,core_le_even p hv.2⟩
  have hw' : w ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph :=
    ⟨core_le_even q hw.1,core_le_even q hw.2⟩
  have hsum := raw_assembly_zero
    ((primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph).add_mem hv' hw') h0
  have he : v = -w := eq_neg_of_add_eq_zero_left hsum
  have hvq : v ∈ (primeBurnolSquareGraphCore q).prod (primeBurnolSquareGraphCore q) :=
    he ▸ ((primeBurnolSquareGraphCore q).prod (primeBurnolSquareGraphCore q)).neg_mem hw
  have hd := Submodule.disjoint_def.mp (primeBurnolSquareGraphCore_disjoint hpq)
  have hv0 : v=0 := Prod.ext (hd _ hv.1 hvq.1) (hd _ hv.2 hvq.2)
  have hw0 : w=0 := by simpa only [hv0,zero_add] using hsum
  simp only [hv0,hw0,map_zero,add_zero,Prod.snd_zero]

/-- Closure of either prime's separate raw graph core is the full admitted raw graph. -/
theorem burnolJetRawCore_closure (p : Nat.Primes) :
    ((primeBurnolSquareGraphCore p).prod (primeBurnolSquareGraphCore p)).topologicalClosure =
      primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph := by
  apply SetLike.ext'
  change closure ((primeBurnolSquareGraphCore p : Set (SoninL2 × SoninL2)) ×ˢ
    (primeBurnolSquareGraphCore p : Set (SoninL2 × SoninL2))) = _
  rw [closure_prod_eq]
  change ((primeBurnolSquareGraphCore p).topologicalClosure : Set (SoninL2 × SoninL2)) ×ˢ
    ((primeBurnolSquareGraphCore p).topologicalClosure : Set (SoninL2 × SoninL2)) = _
  rw [primeBurnolSquareGraphCore_closure]
  rfl

theorem burnolJetThetaRelationAssembly_mem_closure (p : Nat.Primes) (a : ℝ)
    {z : BurnolJetRaw} (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph) :
    burnolJetThetaRelationAssembly p a z ∈
      (primeBurnolJetThetaCoreRelation p a).topologicalClosure := by
  have h := ((primeBurnolSquareGraphCore p).prod
    (primeBurnolSquareGraphCore p)).topologicalClosure_map (burnolJetThetaRelationAssembly p a)
  rw [burnolJetRawCore_closure p] at h
  exact h ⟨z,hz,rfl⟩

theorem primeBurnolThetaVisibility_sq_injective {a : ℝ} (ha : a≠0) :
    Function.Injective (fun p : Nat.Primes => primeBurnolThetaVisibility a p^2) := by
  intro p q hpq
  have hp' := primeBurnolThetaVisibility_sq_add_contrast_sq a p
  have hq' := primeBurnolThetaVisibility_sq_add_contrast_sq a q
  have hs : primeBurnolThetaContrast a p^2=primeBurnolThetaContrast a q^2 := by linarith
  have hsign (r : Nat.Primes) :
      (0≤a → 0≤primeBurnolThetaContrast a r) ∧
      (a≤0 → primeBurnolThetaContrast a r≤0) := by
    constructor
    · intro ha
      have hh : 0≤primeBurnolThetaRapidity a r :=
        div_nonneg (mul_nonneg ha (primeBurnolLogRate r).property.le) (by norm_num)
      have h := _root_.HTGeometry.tanh_strictMono.monotone hh
      simpa only [Real.tanh_zero,primeBurnolThetaContrast] using h
    · intro ha
      have hh : primeBurnolThetaRapidity a r≤0 :=
        div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg ha (primeBurnolLogRate r).property.le) (by norm_num)
      have h := _root_.HTGeometry.tanh_strictMono.monotone hh
      simpa only [Real.tanh_zero,primeBurnolThetaContrast] using h
  have he : primeBurnolThetaContrast a p=primeBurnolThetaContrast a q := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact h
    · rcases le_total 0 a with ha | ha
      · have h1 := (hsign p).1 ha
        have h2 := (hsign q).1 ha
        linarith
      · have h1 := (hsign p).2 ha
        have h2 := (hsign q).2 ha
        linarith
  have hr := _root_.HTGeometry.tanh_strictMono.injective he
  change a*Real.log (p : ℝ)/2=a*Real.log (q : ℝ)/2 at hr
  have hprod : a*(Real.log (p : ℝ)-Real.log (q : ℝ))=0 := by linarith
  have hlog := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left ha)
  have hp0 : 0<(p : ℝ) := by exact_mod_cast p.property.pos
  have hq0 : 0<(q : ℝ) := by exact_mod_cast q.property.pos
  have heq := Real.log_injOn_pos hp0 hq0 hlog
  apply Subtype.ext
  exact_mod_cast heq

private def rawPrimeTheta (p : Nat.Primes) (a : ℝ) : BurnolJetRaw →L[ℂ] BurnolJetRaw :=
  burnolJetRawTheta ((primeBurnolThetaVisibility a p : ℂ)^2)
    ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ))

private theorem rawTheta_difference_square (u w u' w' : ℂ) (z : BurnolJetRaw) :
    (burnolJetRawTheta u w-burnolJetRawTheta u' w')
      ((burnolJetRawTheta u w-burnolJetRawTheta u' w') z) =
        ((u-u')^2+(w-w')^2) • z := by
  apply Prod.ext <;>
    simp only [sub_apply,burnolJetRawTheta,ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk,AddHom.coe_mk,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd] <;> module

private theorem rawPrimeTheta_difference_surjective {p q : Nat.Primes} (hpq : p≠q)
    {a : ℝ} (ha : a≠0) {z : BurnolJetRaw}
    (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph) :
    ∃ y ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph,
      rawPrimeTheta p a y-rawPrimeTheta q a y=z := by
  let d : ℝ := primeBurnolThetaVisibility a p^2-primeBurnolThetaVisibility a q^2
  let e : ℝ := primeBurnolThetaVisibility a p*primeBurnolThetaContrast a p-
    primeBurnolThetaVisibility a q*primeBurnolThetaContrast a q
  have hd : d≠0 := fun h => hpq (primeBurnolThetaVisibility_sq_injective ha (sub_eq_zero.mp h))
  have hk : d^2+e^2≠0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd) (sq_nonneg e))
  let k : ℂ := (d : ℂ)^2+(e : ℂ)^2
  have hk' : k≠0 := by
    change (d : ℂ)^2+(e : ℂ)^2≠0
    exact_mod_cast hk
  let D := rawPrimeTheta p a-rawPrimeTheta q a
  have hD : ∀ x ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph,
      D x ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph := by
    intro x hx
    exact (primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph).sub_mem
      (burnolJetRawTheta_mem_prod _ _ _ hx) (burnolJetRawTheta_mem_prod _ _ _ hx)
  have hDD : D (D z)=k • z := by
    have h := rawTheta_difference_square
      ((primeBurnolThetaVisibility a p : ℂ)^2)
      ((primeBurnolThetaVisibility a p : ℂ)*(primeBurnolThetaContrast a p : ℂ))
      ((primeBurnolThetaVisibility a q : ℂ)^2)
      ((primeBurnolThetaVisibility a q : ℂ)*(primeBurnolThetaContrast a q : ℂ)) z
    simpa only [D,rawPrimeTheta,k,d,e,Complex.ofReal_sub,Complex.ofReal_pow,
      Complex.ofReal_mul] using h
  refine ⟨k⁻¹ • D z,(primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph).smul_mem _
    (hD z hz),?_⟩
  change D (k⁻¹ • D z)=z
  rw [map_smul,hDD,smul_smul,inv_mul_cancel₀ hk',one_smul]

private theorem rawTheta_even (p : Nat.Primes) (a : ℝ) {z : BurnolJetRaw}
    (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph) :
    rawPrimeTheta p a z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph :=
  burnolJetRawTheta_mem_prod _ _ _ hz

private theorem full_relation_mem (p q : Nat.Primes) (a : ℝ) {z : BurnolJetRaw}
    (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph) :
    (burnolJetGraphAssembly z,burnolJetGraphAssembly (rawPrimeTheta p a z)) ∈
      (primeBurnolJetTwoPrimeThetaRelation p q a).topologicalClosure :=
  Submodule.topologicalClosure_mono le_sup_left
    (burnolJetThetaRelationAssembly_mem_closure p a hz)

private theorem core_relation_le (p : Nat.Primes) (a : ℝ) :
    primeBurnolJetThetaCoreRelation p a ≤
      primeBurnolFourierJetEvenGraph.prod primeBurnolFourierJetEvenGraph := by
  rintro _ ⟨z,hz,rfl⟩
  have hz' : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph :=
    ⟨core_le_even p hz.1,core_le_even p hz.2⟩
  exact ⟨⟨z,hz',rfl⟩,⟨rawPrimeTheta p a z,rawTheta_even p a hz',rfl⟩⟩

/-- Distinct actual prime actions make the closed relation the entire product of completed jets. -/
theorem primeBurnolJetTwoPrimeThetaRelation_closure_nonzero {p q : Nat.Primes} (hpq : p≠q)
    {a : ℝ} (ha : a≠0) :
    (primeBurnolJetTwoPrimeThetaRelation p q a).topologicalClosure =
      primeBurnolFourierJetEvenGraph.topologicalClosure.prod
        primeBurnolFourierJetEvenGraph.topologicalClosure := by
  let L := (primeBurnolJetTwoPrimeThetaRelation p q a).topologicalClosure
  have hfullq {z : BurnolJetRaw}
      (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph) :
      (burnolJetGraphAssembly z,burnolJetGraphAssembly (rawPrimeTheta q a z)) ∈ L :=
    Submodule.topologicalClosure_mono le_sup_right
      (burnolJetThetaRelationAssembly_mem_closure q a hz)
  have hvert0 {z : BurnolJetRaw}
      (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph) :
      (0,burnolJetGraphAssembly z) ∈ L := by
    obtain ⟨y,hy,he⟩ := rawPrimeTheta_difference_surjective hpq ha hz
    have h := L.sub_mem (full_relation_mem p q a hy) (hfullq hy)
    have heq : (burnolJetGraphAssembly y,burnolJetGraphAssembly (rawPrimeTheta p a y)) -
        (burnolJetGraphAssembly y,burnolJetGraphAssembly (rawPrimeTheta q a y)) =
          (0,burnolJetGraphAssembly z) := by
      apply Prod.ext
      · exact sub_self _
      · change burnolJetGraphAssembly (rawPrimeTheta p a y)-
          burnolJetGraphAssembly (rawPrimeTheta q a y)=_
        rw [← map_sub,he]
    exact heq ▸ h
  have hvert : ∀ w ∈ primeBurnolFourierJetEvenGraph.topologicalClosure,
      (0,w) ∈ L := by
    change closure (primeBurnolFourierJetEvenGraph : Set BurnolJetAmbient) ⊆ {w | (0,w) ∈ L}
    apply closure_minimal _ ((primeBurnolJetTwoPrimeThetaRelation p q a).isClosed_topologicalClosure.preimage
      (by fun_prop : Continuous fun w : BurnolJetAmbient => ((0 : BurnolJetAmbient),w)))
    rintro w ⟨z,hz,rfl⟩
    exact hvert0 hz
  have hhoriz : ∀ w ∈ primeBurnolFourierJetEvenGraph.topologicalClosure,
      (w,0) ∈ L := by
    change closure (primeBurnolFourierJetEvenGraph : Set BurnolJetAmbient) ⊆ {w | (w,0) ∈ L}
    apply closure_minimal _ ((primeBurnolJetTwoPrimeThetaRelation p q a).isClosed_topologicalClosure.preimage
      (by fun_prop : Continuous fun w : BurnolJetAmbient => (w,(0 : BurnolJetAmbient))))
    rintro w ⟨z,hz,rfl⟩
    have hout : burnolJetGraphAssembly (rawPrimeTheta p a z) ∈
        primeBurnolFourierJetEvenGraph.topologicalClosure :=
      primeBurnolFourierJetEvenGraph.le_topologicalClosure
        ⟨rawPrimeTheta p a z,rawTheta_even p a hz,rfl⟩
    have h := L.sub_mem (full_relation_mem p q a hz) (hvert _ hout)
    change (burnolJetGraphAssembly z,(0 : BurnolJetAmbient)) ∈ L
    simpa only [Prod.mk_sub_mk,sub_zero,sub_self] using h
  apply le_antisymm
  · apply (primeBurnolJetTwoPrimeThetaRelation p q a).topologicalClosure_minimal
    · apply sup_le
      · intro z hz
        have h := core_relation_le p a hz
        exact ⟨primeBurnolFourierJetEvenGraph.le_topologicalClosure h.1,
          primeBurnolFourierJetEvenGraph.le_topologicalClosure h.2⟩
      · intro z hz
        have h := core_relation_le q a hz
        exact ⟨primeBurnolFourierJetEvenGraph.le_topologicalClosure h.1,
          primeBurnolFourierJetEvenGraph.le_topologicalClosure h.2⟩
    · exact primeBurnolFourierJetEvenGraph.isClosed_topologicalClosure.prod
        primeBurnolFourierJetEvenGraph.isClosed_topologicalClosure
  · intro z hz
    have h := L.add_mem (hhoriz z.1 hz.1) (hvert z.2 hz.2)
    simpa only [Prod.mk_add_mk,add_zero,zero_add] using h

private theorem zero_relation_mem_neutral (p : Nat.Primes) {z : BurnolJetRaw}
    (hz : z ∈ primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph) :
    burnolJetThetaRelationAssembly p 0 z ∈ burnolJetNeutral.graph := by
  obtain ⟨f,hf,hM⟩ := burnolSquarePosition.mem_graph_iff.mp hz.1.1
  obtain ⟨g,hg,hN⟩ := burnolSquarePosition.mem_graph_iff.mp hz.2.1
  have hef : (f : SoninL2) ∈ evenSubspace := hf.symm ▸ hz.1.2.1
  have heg : (g : SoninL2) ∈ evenSubspace := hg.symm ▸ hz.2.2.1
  have he : (((f : SoninL2),burnolSquarePosition f),
      ((g : SoninL2),burnolSquarePosition g))=z :=
    Prod.ext (Prod.ext hf hM) (Prod.ext hg hN)
  rw [← he,burnolJetThetaRelationAssembly_source]
  simpa only [burnolJetPrimeThetaSource,primeBurnolThetaVisibility_zero,
    primeBurnolThetaContrast_zero,Complex.ofReal_one,Complex.ofReal_zero,one_pow,
    mul_zero,burnolJetThetaSource,LinearMap.coe_mk,AddHom.coe_mk,one_smul,zero_smul,
    add_zero,sub_self,zero_add,burnolJetGraphLinear] using
      burnolJetNeutral_source_graph f g hef heg

theorem primeBurnolJetTwoPrimeThetaRelation_closure_zero (p q : Nat.Primes) :
    (primeBurnolJetTwoPrimeThetaRelation p q 0).topologicalClosure=burnolJetNeutral.graph := by
  apply le_antisymm
  · apply (primeBurnolJetTwoPrimeThetaRelation p q 0).topologicalClosure_minimal
      _ burnolJetNeutral_isClosed
    have h (r : Nat.Primes) : primeBurnolJetThetaCoreRelation r 0 ≤ burnolJetNeutral.graph := by
      rintro _ ⟨z,hz,rfl⟩
      exact zero_relation_mem_neutral r ⟨core_le_even r hz.1,core_le_even r hz.2⟩
    exact sup_le (h p) (h q)
  · intro z hz
    have hd := burnolJetNeutral.mem_domain_of_mem_graph hz
    rw [burnolJetNeutral_domain] at hd
    obtain ⟨f,g,hf,hg,he⟩ := (mem_primeBurnolFourierJetEvenGraph z.1).mp hd
    have he' : burnolJetGraphVector f g=z.1 := he
    have hw : burnolJetGraphVector f 0=z.2 :=
      burnolJetNeutral.mem_graph_snd_inj (burnolJetNeutral_source_graph f g hf hg) hz he'
    have hraw : (((f : SoninL2),burnolSquarePosition f),
        ((g : SoninL2),burnolSquarePosition g)) ∈
        primeBurnolEvenSquareGraph.prod primeBurnolEvenSquareGraph :=
      ⟨⟨burnolSquarePosition.mem_graph f,hf,Submodule.mem_top⟩,
        ⟨burnolSquarePosition.mem_graph g,hg,Submodule.mem_top⟩⟩
    have h := full_relation_mem p q 0 hraw
    change burnolJetThetaRelationAssembly p 0 _ ∈ _ at h
    rw [burnolJetThetaRelationAssembly_source] at h
    simpa only [burnolJetPrimeThetaSource,primeBurnolThetaVisibility_zero,
      primeBurnolThetaContrast_zero,Complex.ofReal_one,Complex.ofReal_zero,one_pow,
      mul_zero,burnolJetThetaSource,LinearMap.coe_mk,AddHom.coe_mk,one_smul,zero_smul,
      add_zero,sub_self,zero_add,burnolJetGraphLinear,he',hw] using h

/-- The literal finite two-prime theta action, prior to taking any closure. -/
def primeBurnolJetTwoPrimeTheta (p q : Nat.Primes) (a : ℝ) :
    BurnolJetAmbient →ₗ.[ℂ] BurnolJetAmbient :=
  (primeBurnolJetTwoPrimeThetaRelation p q a).toLinearPMap

theorem primeBurnolJetTwoPrimeTheta_graph {p q : Nat.Primes} (hpq : p≠q) (a : ℝ) :
    (primeBurnolJetTwoPrimeTheta p q a).graph=primeBurnolJetTwoPrimeThetaRelation p q a :=
  (primeBurnolJetTwoPrimeThetaRelation p q a).toLinearPMap_graph_eq
    (fun _ hz h0 => primeBurnolJetTwoPrimeThetaRelation_singleValued hpq a hz h0)

/-- Exact closed-extension criterion for the actual finite two-prime action. -/
theorem primeBurnolJetTwoPrimeTheta_isClosable_iff {p q : Nat.Primes} (hpq : p≠q) (a : ℝ) :
    (primeBurnolJetTwoPrimeTheta p q a).IsClosable ↔ a=0 := by
  constructor
  · rintro ⟨T,hT⟩
    by_contra ha
    rw [primeBurnolJetTwoPrimeTheta_graph hpq,
      primeBurnolJetTwoPrimeThetaRelation_closure_nonzero hpq ha] at hT
    let f := primeBurnolSquareColumn (p,0)
    have hf : (f : SoninL2) ∈ evenSubspace := primeBurnolEvenFeatureLp_mem_evenSubspace (p,0)
    have hG : burnolJetGraphVector f 0 ∈ primeBurnolFourierJetEvenGraph.topologicalClosure :=
      primeBurnolFourierJetEvenGraph.le_topologicalClosure
        ((mem_primeBurnolFourierJetEvenGraph _).mpr ⟨f,0,hf,evenSubspace.zero_mem,rfl⟩)
    have hpair : (0,burnolJetGraphVector f 0) ∈ T.graph :=
      hT ▸ ⟨primeBurnolFourierJetEvenGraph.topologicalClosure.zero_mem,hG⟩
    have hzero := T.graph_fst_eq_zero_snd hpair rfl
    have hcol : primeBurnolEvenFeatureLp (p,0)=0 :=
      congrArg (fun z : BurnolJetAmbient => z.1.1) hzero
    exact primeBurnolEvenFeatureLp_linearIndependent.ne_zero (p,0) hcol
  · rintro rfl
    exact ⟨burnolJetNeutral,by rw [primeBurnolJetTwoPrimeTheta_graph hpq,
      primeBurnolJetTwoPrimeThetaRelation_closure_zero]⟩

end RHTower
