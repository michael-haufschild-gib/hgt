import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetPrimeCore
import GaloisForLFunctions.RHTower.PrimeBurnolFourierJetPhaseObstruction

/-!
# Closed unbounded neutral projection of the even Fourier jet

The two separately admitted physical source channels are disjoint closed subspaces.
Their sum is exactly the original even maximal-domain source graph. The neutral
coordinate projection is a closed idempotent with these exact range and kernel channels.

The quadratic-phase obstruction excludes a neutral graph bound, even on each single
prime's literal depth core. Consequently the channel sum is nonclosed and the neutral
domain is proper dense in the completed even source graph.
-/

open Complex MeasureTheory Set Filter Topology
open scoped LinearPMap
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The physical input pair together with its two Fourier-jet outputs. -/
abbrev BurnolJetAmbient := (SoninL2 × SoninL2) × (SoninL2 × SoninL2)

/-- The graph of the separately admitted first source channel. -/
def burnolJetFirstChannel : Submodule ℂ BurnolJetAmbient where
  carrier := {w | (w.1.1,w.2.2) ∈ primeBurnolEvenSquareGraph ∧
    w.1.2 = 0 ∧ w.2.1 = w.1.1}
  zero_mem' := ⟨primeBurnolEvenSquareGraph.zero_mem, rfl, rfl⟩
  add_mem' hz hw := ⟨primeBurnolEvenSquareGraph.add_mem hz.1 hw.1,
    by simp only [Prod.fst_add, Prod.snd_add, hz.2.1, hw.2.1, add_zero],
    by simp only [Prod.fst_add, Prod.snd_add, hz.2.2, hw.2.2]⟩
  smul_mem' c w hw := ⟨primeBurnolEvenSquareGraph.smul_mem c hw.1,
    by simp only [Prod.smul_fst, Prod.smul_snd, hw.2.1, smul_zero],
    by simp only [Prod.smul_fst, Prod.smul_snd, hw.2.2]⟩

/-- The graph of the separately admitted Fourier source channel. -/
def burnolJetSecondChannel : Submodule ℂ BurnolJetAmbient where
  carrier := {w | (w.1.2,fourierUnitary.symm w.2.2) ∈ primeBurnolEvenSquareGraph ∧
    w.1.1 = 0 ∧ w.2.1 = fourierUnitary w.1.2}
  zero_mem' := by
    refine ⟨?_,rfl,?_⟩
    · change ((0 : SoninL2),fourierUnitary.symm (0 : SoninL2)) ∈ primeBurnolEvenSquareGraph
      rw [map_zero]
      exact primeBurnolEvenSquareGraph.zero_mem
    · exact (map_zero fourierUnitary).symm
  add_mem' hz hw := ⟨by simpa only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]
      using primeBurnolEvenSquareGraph.add_mem hz.1 hw.1,
    by simp only [Prod.fst_add, hz.2.1, hw.2.1, add_zero],
    by simp only [Prod.fst_add, Prod.snd_add, map_add, hz.2.2, hw.2.2]⟩
  smul_mem' c w hw := ⟨by simpa only [Prod.smul_fst, Prod.smul_snd, map_smul, Prod.smul_mk]
      using primeBurnolEvenSquareGraph.smul_mem c hw.1,
    by simp only [Prod.smul_fst, hw.2.1, smul_zero],
    by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, hw.2.2]⟩

private theorem squareGraph_closed :
    IsClosed (primeBurnolEvenSquareGraph : Set (SoninL2 × SoninL2)) := by
  have hm : IsClosed (burnolSquarePosition.graph : Set (SoninL2 × SoninL2)) :=
    (maximalRealL2Mul_isSelfAdjoint volume (by fun_prop : Measurable fun x : ℝ => x^2)).isClosed
  have he : IsClosed (evenSubspace : Set SoninL2) := by
    convert isClosed_eq l2Reflection.continuous continuous_id using 1
    ext v
    exact mem_evenSubspace_iff v
  exact hm.inter (he.prod isClosed_univ)

theorem burnolJetFirstChannel_closed : IsClosed (burnolJetFirstChannel : Set BurnolJetAmbient) :=
  (squareGraph_closed.preimage (by fun_prop)).inter
    ((isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) (by fun_prop)))

theorem burnolJetSecondChannel_closed : IsClosed (burnolJetSecondChannel : Set BurnolJetAmbient) :=
  (squareGraph_closed.preimage (by fun_prop)).inter
    ((isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) (by fun_prop)))

private theorem channel_inter_zero {w : BurnolJetAmbient}
    (ha : w ∈ burnolJetFirstChannel) (hb : w ∈ burnolJetSecondChannel) : w = 0 := by
  have hv : w.2.2 = 0 := burnolSquarePosition.graph_fst_eq_zero_snd ha.1.1 hb.2.1
  apply Prod.ext
  · exact Prod.ext hb.2.1 ha.2.1
  · exact Prod.ext (ha.2.2.trans hb.2.1) hv

theorem burnolJetChannels_disjoint : Disjoint burnolJetFirstChannel burnolJetSecondChannel := by
  apply disjoint_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro w hw
  exact channel_inter_zero hw.1 hw.2

/-- The literal graph vector of an admitted pair of physical inputs. -/
def burnolJetGraphVector (f g : burnolSquarePosition.domain) : BurnolJetAmbient :=
  (((f : SoninL2),(g : SoninL2)), primeBurnolFourierJetSynthesis (f,g))

private theorem Mzero : burnolSquarePosition 0 = 0 := map_zero burnolSquarePosition.toFun

private theorem burnolJetGraphVector_first (f : burnolSquarePosition.domain)
    (hf : (f : SoninL2) ∈ evenSubspace) : burnolJetGraphVector f 0 ∈ burnolJetFirstChannel := by
  change (((f : SoninL2), burnolSquarePosition f + fourierUnitary (burnolSquarePosition 0))
    ∈ primeBurnolEvenSquareGraph) ∧ (0 : SoninL2) = 0 ∧
      (f : SoninL2) + fourierUnitary 0 = (f : SoninL2)
  refine ⟨?_,rfl,by simp⟩
  simpa only [Mzero, map_zero, add_zero] using
    (show ((f : SoninL2),burnolSquarePosition f) ∈ primeBurnolEvenSquareGraph from
      ⟨burnolSquarePosition.mem_graph f,hf,Submodule.mem_top⟩)

private theorem burnolJetGraphVector_second (g : burnolSquarePosition.domain)
    (hg : (g : SoninL2) ∈ evenSubspace) : burnolJetGraphVector 0 g ∈ burnolJetSecondChannel := by
  change (((g : SoninL2), fourierUnitary.symm
    (burnolSquarePosition 0 + fourierUnitary (burnolSquarePosition g)))
    ∈ primeBurnolEvenSquareGraph) ∧ (0 : SoninL2) = 0 ∧
      0 + fourierUnitary (g : SoninL2) = fourierUnitary (g : SoninL2)
  refine ⟨?_,rfl,by simp⟩
  simpa only [Mzero, zero_add, fourierUnitary.symm_apply_apply] using
    (show ((g : SoninL2),burnolSquarePosition g) ∈ primeBurnolEvenSquareGraph from
      ⟨burnolSquarePosition.mem_graph g,hg,Submodule.mem_top⟩)

private theorem firstChannel_source {w : BurnolJetAmbient} (hw : w ∈ burnolJetFirstChannel) :
    ∃ f : burnolSquarePosition.domain, (f : SoninL2) ∈ evenSubspace ∧ w = burnolJetGraphVector f 0 := by
  obtain ⟨f,hf,hm⟩ := burnolSquarePosition.mem_graph_iff.mp hw.1.1
  refine ⟨f,hf.symm ▸ hw.1.2.1, ?_⟩
  apply Prod.ext
  · exact Prod.ext hf.symm hw.2.1
  · change w.2 = ((f : SoninL2)+fourierUnitary 0,
      burnolSquarePosition f + fourierUnitary (burnolSquarePosition 0))
    simp only [Mzero, map_zero, add_zero]
    exact Prod.ext (hw.2.2.trans hf.symm) hm.symm

private theorem secondChannel_source {w : BurnolJetAmbient} (hw : w ∈ burnolJetSecondChannel) :
    ∃ g : burnolSquarePosition.domain, (g : SoninL2) ∈ evenSubspace ∧ w = burnolJetGraphVector 0 g := by
  obtain ⟨g,hg,hm⟩ := burnolSquarePosition.mem_graph_iff.mp hw.1.1
  refine ⟨g,hg.symm ▸ hw.1.2.1, ?_⟩
  apply Prod.ext
  · exact Prod.ext hw.2.1 hg.symm
  · change w.2 = (0+fourierUnitary (g : SoninL2),
      burnolSquarePosition 0 + fourierUnitary (burnolSquarePosition g))
    simp only [Mzero, zero_add]
    refine Prod.ext (hw.2.2.trans (congrArg fourierUnitary hg.symm)) ?_
    rw [hm, fourierUnitary.apply_symm_apply]

theorem burnolJetChannels_sum :
    burnolJetFirstChannel ⊔ burnolJetSecondChannel = primeBurnolFourierJetEvenGraph := by
  apply le_antisymm
  · apply sup_le
    · intro w hw
      obtain ⟨f,hf,rfl⟩ := firstChannel_source hw
      exact (mem_primeBurnolFourierJetEvenGraph _).mpr ⟨f,0,hf,evenSubspace.zero_mem,rfl⟩
    · intro w hw
      obtain ⟨g,hg,rfl⟩ := secondChannel_source hw
      exact (mem_primeBurnolFourierJetEvenGraph _).mpr ⟨0,g,evenSubspace.zero_mem,hg,rfl⟩
  · intro w hw
    obtain ⟨f,g,hf,hg,rfl⟩ := (mem_primeBurnolFourierJetEvenGraph w).mp hw
    refine Submodule.mem_sup.mpr ⟨burnolJetGraphVector f 0, burnolJetGraphVector_first f hf,
      burnolJetGraphVector 0 g, burnolJetGraphVector_second g hg, ?_⟩
    apply Prod.ext
    · simp [burnolJetGraphVector]
    · change ((f : SoninL2) + fourierUnitary 0,
        burnolSquarePosition f + fourierUnitary (burnolSquarePosition 0)) +
        (0 + fourierUnitary (g : SoninL2),
        burnolSquarePosition 0 + fourierUnitary (burnolSquarePosition g)) = _
      simp only [Mzero, map_zero, add_zero, zero_add, Prod.mk_add_mk]
      rfl

/-- The relation splitting a graph vector into its two separately admitted channels. -/
def burnolJetNeutralRelation : Submodule ℂ (BurnolJetAmbient × BurnolJetAmbient) :=
  (burnolJetFirstChannel.comap (LinearMap.snd ℂ _ _)) ⊓
    (burnolJetSecondChannel.comap (LinearMap.fst ℂ _ _ - LinearMap.snd ℂ _ _))

private theorem neutral_unique (z : BurnolJetAmbient × BurnolJetAmbient)
    (hz : z ∈ burnolJetNeutralRelation) (h0 : z.1 = 0) : z.2 = 0 := by
  change z.2 ∈ burnolJetFirstChannel ∧ z.1-z.2 ∈ burnolJetSecondChannel at hz
  apply channel_inter_zero hz.1
  have h : -z.2 ∈ burnolJetSecondChannel := by
    simpa only [h0, zero_sub] using hz.2
  simpa only [neg_neg] using burnolJetSecondChannel.neg_mem h

/-- The original neutral coordinate operation as a partial linear operator. -/
def burnolJetNeutral : BurnolJetAmbient →ₗ.[ℂ] BurnolJetAmbient :=
  burnolJetNeutralRelation.toLinearPMap

theorem burnolJetNeutral_graph : burnolJetNeutral.graph = burnolJetNeutralRelation :=
  burnolJetNeutralRelation.toLinearPMap_graph_eq neutral_unique

theorem burnolJetNeutral_isClosed : burnolJetNeutral.IsClosed := by
  change IsClosed (burnolJetNeutral.graph : Set (BurnolJetAmbient × BurnolJetAmbient))
  rw [burnolJetNeutral_graph]
  exact (burnolJetFirstChannel_closed.preimage continuous_snd).inter
    (burnolJetSecondChannel_closed.preimage (continuous_fst.sub continuous_snd))

theorem burnolJetNeutral_domain : burnolJetNeutral.domain = primeBurnolFourierJetEvenGraph := by
  rw [← burnolJetChannels_sum]
  ext z
  rw [LinearPMap.mem_domain_iff, burnolJetNeutral_graph]
  constructor
  · rintro ⟨w,hw⟩
    exact Submodule.mem_sup.mpr ⟨w,hw.1,z-w,hw.2,by abel⟩
  · intro hz
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hz
    refine ⟨a,ha,?_⟩
    change a+b-a ∈ burnolJetSecondChannel
    simpa only [add_sub_cancel_left] using hb

theorem burnolJetNeutral_idempotent (z : burnolJetNeutral.domain) :
    ∃ h : burnolJetNeutral z ∈ burnolJetNeutral.domain,
      burnolJetNeutral ⟨burnolJetNeutral z,h⟩ = burnolJetNeutral z := by
  have hz := burnolJetNeutral.mem_graph z
  rw [burnolJetNeutral_graph] at hz
  have hh : (burnolJetNeutral z,burnolJetNeutral z) ∈ burnolJetNeutral.graph := by
    rw [burnolJetNeutral_graph]
    refine ⟨hz.1,?_⟩
    change burnolJetNeutral z-burnolJetNeutral z ∈ burnolJetSecondChannel
    simpa only [sub_self] using burnolJetSecondChannel.zero_mem
  have hd := burnolJetNeutral.mem_domain_of_mem_graph hh
  refine ⟨hd, ?_⟩
  exact burnolJetNeutral.mem_graph_snd_inj (burnolJetNeutral.mem_graph ⟨_,hd⟩) hh rfl


theorem burnolJetNeutral_domain_closure :
    burnolJetNeutral.domain.topologicalClosure = primeBurnolFourierJetEvenGraph.topologicalClosure := by
  rw [burnolJetNeutral_domain]

theorem burnolJetNeutral_graph_iff (z w : BurnolJetAmbient) :
    (z,w) ∈ burnolJetNeutral.graph ↔ w ∈ burnolJetFirstChannel ∧ z-w ∈ burnolJetSecondChannel := by
  rw [burnolJetNeutral_graph]
  rfl

theorem burnolJetNeutral_range : LinearMap.range burnolJetNeutral.toFun = burnolJetFirstChannel := by
  apply le_antisymm
  · rintro _ ⟨z,rfl⟩
    exact ((burnolJetNeutral_graph_iff _ _).mp (burnolJetNeutral.mem_graph z)).1
  · intro w hw
    have hg : (w,w) ∈ burnolJetNeutral.graph :=
      (burnolJetNeutral_graph_iff _ _).mpr ⟨hw,by simpa only [sub_self] using burnolJetSecondChannel.zero_mem⟩
    obtain ⟨v,hv,hN⟩ := burnolJetNeutral.mem_graph_iff.mp hg
    exact ⟨v,hN⟩

theorem burnolJetNeutral_zero_iff (z : burnolJetNeutral.domain) :
    burnolJetNeutral z = 0 ↔ (z : BurnolJetAmbient) ∈ burnolJetSecondChannel := by
  constructor
  · intro h
    have hz := ((burnolJetNeutral_graph_iff _ _).mp (burnolJetNeutral.mem_graph z)).2
    simpa only [h,sub_zero] using hz
  · intro hz
    have hg : ((z : BurnolJetAmbient),0) ∈ burnolJetNeutral.graph :=
      (burnolJetNeutral_graph_iff _ _).mpr
        ⟨burnolJetFirstChannel.zero_mem,by simpa only [sub_zero] using hz⟩
    exact burnolJetNeutral.mem_graph_snd_inj (burnolJetNeutral.mem_graph z) hg rfl

theorem burnolJetNeutral_source_graph (f g : burnolSquarePosition.domain)
    (hf : (f : SoninL2) ∈ evenSubspace) (hg : (g : SoninL2) ∈ evenSubspace) :
    (burnolJetGraphVector f g,burnolJetGraphVector f 0) ∈ burnolJetNeutral.graph := by
  apply (burnolJetNeutral_graph_iff _ _).mpr
  refine ⟨burnolJetGraphVector_first f hf, ?_⟩
  have h : burnolJetGraphVector f g-burnolJetGraphVector f 0 = burnolJetGraphVector 0 g := by
    apply Prod.ext
    · simp [burnolJetGraphVector]
    · change ((f : SoninL2)+fourierUnitary (g : SoninL2),
        burnolSquarePosition f+fourierUnitary (burnolSquarePosition g)) -
        ((f : SoninL2)+fourierUnitary 0,
        burnolSquarePosition f+fourierUnitary (burnolSquarePosition 0)) =
        (0+fourierUnitary (g : SoninL2),
        burnolSquarePosition 0+fourierUnitary (burnolSquarePosition g))
      simp only [Mzero,map_zero,add_zero,zero_add,Prod.mk_sub_mk,add_sub_cancel_left]
  rw [h]
  exact burnolJetGraphVector_second g hg
private theorem second_square_graph_le (f g : burnolSquarePosition.domain) :
    ‖burnolSquarePosition g‖ ≤ ‖burnolJetGraphVector f g‖ + ‖burnolJetGraphVector f 0‖ := by
  have hf : ‖burnolSquarePosition f‖ ≤ ‖burnolJetGraphVector f 0‖ := by
    have h := (norm_snd_le (burnolJetGraphVector f 0).2).trans
      (norm_snd_le (burnolJetGraphVector f 0))
    change ‖burnolSquarePosition f + fourierUnitary (burnolSquarePosition 0)‖ ≤ _ at h
    simpa only [Mzero,map_zero,add_zero] using h
  have ho : ‖burnolSquarePosition f + fourierUnitary (burnolSquarePosition g)‖ ≤
      ‖burnolJetGraphVector f g‖ :=
    (norm_snd_le (burnolJetGraphVector f g).2).trans (norm_snd_le (burnolJetGraphVector f g))
  calc
    ‖burnolSquarePosition g‖ = ‖fourierUnitary (burnolSquarePosition g)‖ :=
      (fourierUnitary.norm_map _).symm
    _ = ‖(burnolSquarePosition f+fourierUnitary (burnolSquarePosition g)) -
        burnolSquarePosition f‖ := by rw [add_sub_cancel_left]
    _ ≤ ‖burnolSquarePosition f+fourierUnitary (burnolSquarePosition g)‖ +
        ‖burnolSquarePosition f‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add ho hf

/-- Retaining the input and output norms does not make the original neutral operation bounded. -/
theorem burnolJetNeutral_no_source_graph_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      (f : SoninL2) ∈ evenSubspace → (g : SoninL2) ∈ evenSubspace →
      ‖burnolJetGraphVector f 0‖ ≤ C*‖burnolJetGraphVector f g‖ := by
  rintro ⟨C,hC,hbound⟩
  apply burnolJetWeakTest_no_position_graph_bound
  let c : ℝ := ‖-((8*(Real.pi : ℂ)^2)⁻¹)‖
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨(1+C)*(1+c),mul_nonneg (by positivity) (by positivity),?_⟩
  intro φ hφ
  obtain ⟨f,g,hf,hg,hMg,hout⟩ := burnolJetSchwartz_cancelling_source φ
  have hfe : (f : SoninL2) ∈ evenSubspace := by
    rw [hf,mem_evenSubspace_iff, ← fourierUnitary_l2Reflection,
      (mem_evenSubspace_iff _).mp hφ]
  have hge : (g : SoninL2) ∈ evenSubspace := by rw [hg]; exact evenSubspace.neg_mem hφ
  have hz : ‖burnolJetGraphVector f g‖ ≤
      (1+c)*(‖φ.toLp 2 volume‖+‖burnolJetWeakTest φ‖) := by
    change ‖(((f : SoninL2),(g : SoninL2)),primeBurnolFourierJetSynthesis (f,g))‖ ≤ _
    rw [hout,hf,hg,Prod.norm_mk,Prod.norm_mk,Prod.norm_mk,
      fourierUnitary.norm_map,norm_neg,max_self,norm_zero,norm_smul,
      fourierUnitary.norm_map,max_eq_right (mul_nonneg hc (norm_nonneg _))]
    apply max_le
    · nlinarith [norm_nonneg (φ.toLp 2 volume),norm_nonneg (burnolJetWeakTest φ),
        mul_nonneg hc (norm_nonneg (φ.toLp 2 volume)),
        mul_nonneg hc (norm_nonneg (burnolJetWeakTest φ))]
    · nlinarith [norm_nonneg (φ.toLp 2 volume),norm_nonneg (burnolJetWeakTest φ),
        mul_nonneg hc (norm_nonneg (φ.toLp 2 volume))]
  calc
    ‖(mulXCLM (mulXCLM φ)).toLp 2 volume‖ = ‖burnolSquarePosition g‖ := by
      rw [hMg,norm_neg]
    _ ≤ ‖burnolJetGraphVector f g‖+‖burnolJetGraphVector f 0‖ := second_square_graph_le f g
    _ ≤ (1+C)*‖burnolJetGraphVector f g‖ := by
      have hh := hbound f g hfe hge
      nlinarith
    _ ≤ (1+C)*((1+c)*(‖φ.toLp 2 volume‖+‖burnolJetWeakTest φ‖)) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring

/-- The closed neutral operator is unbounded on its original even source domain. -/
theorem burnolJetNeutral_unbounded :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : burnolJetNeutral.domain,
      ‖burnolJetNeutral z‖ ≤ C*‖(z : BurnolJetAmbient)‖ := by
  rintro ⟨C,hC,hbound⟩
  apply burnolJetNeutral_no_source_graph_bound
  refine ⟨C,hC,?_⟩
  intro f g hf hg
  have hh := burnolJetNeutral_source_graph f g hf hg
  obtain ⟨z,hz,hN⟩ := burnolJetNeutral.mem_graph_iff.mp hh
  simpa only [hz,hN] using hbound z


/-- Every single prime's literal depth core already has unbounded neutral graph distortion. -/
theorem burnolJetNeutral_no_prime_graph_bound (p : Nat.Primes) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : burnolSquarePosition.domain,
      ((f : SoninL2),burnolSquarePosition f) ∈ primeBurnolSquareGraphCore p →
      ((g : SoninL2),burnolSquarePosition g) ∈ primeBurnolSquareGraphCore p →
      ‖burnolJetGraphVector f 0‖ ≤ C*‖burnolJetGraphVector f g‖ := by
  rintro ⟨C,hC,hbound⟩
  let E : (SoninL2 × SoninL2) × (SoninL2 × SoninL2) → BurnolJetAmbient :=
    fun z => ((z.1.1,z.2.1),(z.1.1+fourierUnitary z.2.1,z.1.2+fourierUnitary z.2.2))
  let A : (SoninL2 × SoninL2) × (SoninL2 × SoninL2) → BurnolJetAmbient :=
    fun z => ((z.1.1,0),(z.1.1,z.1.2))
  have hclosed : IsClosed {z | ‖A z‖ ≤ C*‖E z‖} := by
    apply isClosed_le <;> dsimp [A,E] <;> fun_prop
  have hsub : ((primeBurnolSquareGraphCore p : Set (SoninL2 × SoninL2)) ×ˢ
      (primeBurnolSquareGraphCore p : Set (SoninL2 × SoninL2))) ⊆
      {z | ‖A z‖ ≤ C*‖E z‖} := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have he {v : SoninL2 × SoninL2} (hv : v ∈ primeBurnolSquareGraphCore p) :
        v ∈ primeBurnolEvenSquareGraph := by
      rw [← primeBurnolSquareGraphCore_closure p]
      exact (primeBurnolSquareGraphCore p).le_topologicalClosure hv
    obtain ⟨f,hf,hMf⟩ := burnolSquarePosition.mem_graph_iff.mp (he hx).1
    obtain ⟨g,hg,hMg⟩ := burnolSquarePosition.mem_graph_iff.mp (he hy).1
    have hxf : x = ((f : SoninL2),burnolSquarePosition f) := Prod.ext hf.symm hMf.symm
    have hyg : y = ((g : SoninL2),burnolSquarePosition g) := Prod.ext hg.symm hMg.symm
    subst x y
    have hh := hbound f g hx hy
    have ha : A (((f : SoninL2),burnolSquarePosition f),
        ((g : SoninL2),burnolSquarePosition g)) = burnolJetGraphVector f 0 := by
      change (((f : SoninL2),0),((f : SoninL2),burnolSquarePosition f)) =
        (((f : SoninL2),0),((f : SoninL2)+fourierUnitary 0,
          burnolSquarePosition f+fourierUnitary (burnolSquarePosition 0)))
      simp only [Mzero,map_zero,add_zero]
    change ‖A (((f : SoninL2),burnolSquarePosition f),
      ((g : SoninL2),burnolSquarePosition g))‖ ≤ C*‖burnolJetGraphVector f g‖
    rw [ha]
    exact hh
  have hpass := closure_minimal hsub hclosed
  rw [closure_prod_eq] at hpass
  change ((primeBurnolSquareGraphCore p).topologicalClosure : Set (SoninL2 × SoninL2)) ×ˢ
    ((primeBurnolSquareGraphCore p).topologicalClosure : Set (SoninL2 × SoninL2)) ⊆ _ at hpass
  rw [primeBurnolSquareGraphCore_closure] at hpass
  apply burnolJetNeutral_no_source_graph_bound
  refine ⟨C,hC,?_⟩
  intro f g hf hg
  have hh := hpass (show (((f : SoninL2),burnolSquarePosition f),
      ((g : SoninL2),burnolSquarePosition g)) ∈
      (primeBurnolEvenSquareGraph : Set (SoninL2 × SoninL2)) ×ˢ
      (primeBurnolEvenSquareGraph : Set (SoninL2 × SoninL2)) from
      ⟨⟨burnolSquarePosition.mem_graph f,hf,Submodule.mem_top⟩,
        ⟨burnolSquarePosition.mem_graph g,hg,Submodule.mem_top⟩⟩)
  change ‖(((f : SoninL2),0),((f : SoninL2),burnolSquarePosition f))‖ ≤
    C*‖burnolJetGraphVector f g‖ at hh
  change ‖(((f : SoninL2),0),((f : SoninL2)+fourierUnitary 0,
    burnolSquarePosition f+fourierUnitary (burnolSquarePosition 0)))‖ ≤ _
  simpa only [Mzero,map_zero,add_zero] using hh

/-- The two individually closed source channels have a nonclosed algebraic sum. -/
theorem burnolJetNeutral_domain_not_closed :
    ¬ IsClosed (burnolJetNeutral.domain : Set BurnolJetAmbient) := by
  intro hd
  letI : CompleteSpace burnolJetNeutral.domain := hd.completeSpace_coe
  have hg : IsClosed (burnolJetNeutral.toFun.graph :
      Set (burnolJetNeutral.domain × BurnolJetAmbient)) := by
    have hh := burnolJetNeutral_isClosed.preimage
      (show Continuous (fun z : burnolJetNeutral.domain × BurnolJetAmbient =>
        ((z.1 : BurnolJetAmbient),z.2)) from
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    convert hh using 1
    ext z
    change z.2 = burnolJetNeutral z.1 ↔
      ((z.1 : BurnolJetAmbient),z.2) ∈ burnolJetNeutral.graph
    constructor
    · intro he
      rw [he]
      exact burnolJetNeutral.mem_graph z.1
    · intro he
      exact (burnolJetNeutral.mem_graph_snd_inj (burnolJetNeutral.mem_graph z.1) he rfl).symm
  let T : burnolJetNeutral.domain →L[ℂ] BurnolJetAmbient :=
    ContinuousLinearMap.ofIsClosedGraph hg
  exact burnolJetNeutral_unbounded ⟨‖T‖,norm_nonneg T,fun z => T.le_opNorm z⟩

theorem burnolJetChannels_sum_not_closed :
    ¬ IsClosed ((burnolJetFirstChannel ⊔ burnolJetSecondChannel : Submodule ℂ BurnolJetAmbient) :
      Set BurnolJetAmbient) := by
  rw [burnolJetChannels_sum, ← burnolJetNeutral_domain]
  exact burnolJetNeutral_domain_not_closed

/-- Some completed even graph vectors have no separately admitted pair of position-square inputs. -/
theorem burnolJetNeutral_domain_proper :
    ∃ z ∈ primeBurnolFourierJetEvenGraph.topologicalClosure, z ∉ burnolJetNeutral.domain := by
  by_contra h
  push Not at h
  have he : burnolJetNeutral.domain = primeBurnolFourierJetEvenGraph.topologicalClosure :=
    le_antisymm (by rw [burnolJetNeutral_domain]; exact Submodule.le_topologicalClosure _) h
  exact burnolJetNeutral_domain_not_closed
    (he.symm ▸ primeBurnolFourierJetEvenGraph.isClosed_topologicalClosure)

end RHTower
