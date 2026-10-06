import GaloisForLFunctions.RHTower.DeckEisensteinSpectralIsometry

/-!
# The Eisenstein transform takes values in the symmetric `V_∞`-valued subspace

On the critical line the scattering operator satisfies `Φ̃(½−it)Φ̃(½+it) w = w` for `w ∈ V_∞`, `t ≠ 0`
(isometry and adjointness on `V_∞`, which `Φ̃` preserves).  Hence the transform of every generator
satisfies `T(−t) = Φ̃(½+it) T(t)` with values in `V_∞`.  The set of `L²` classes with this property
is a closed subspace (closedness through almost everywhere convergent subsequences), so the whole
Eisenstein transform `T̄` lands in it (`eisTransformL2_mem_symSpace`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry
open _root_.RHTower (linePt linePt_re linePt_im)

noncomputable section

variable {N : ℕ}

/-! ## Linearity and the functional equation of the scattering operator -/

theorem scatVec_add (s : ℂ) (v w : DeckSpace N) : scatVec s (v + w) = scatVec s v + scatVec s w := by
  ext q
  simp only [scatVec_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib]

theorem scatVec_smul (s c : ℂ) (v : DeckSpace N) : scatVec s (c • v) = c • scatVec s v := by
  ext q
  simp only [scatVec_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  ring

/-- The scattering operator as a linear map. -/
def scatLin (s : ℂ) : DeckSpace N →ₗ[ℂ] DeckSpace N where
  toFun := scatVec s
  map_add' := scatVec_add s
  map_smul' := scatVec_smul s

theorem continuous_scatVec (s : ℂ) : Continuous (scatVec (N := N) s) :=
  (scatLin s).continuous_of_finiteDimensional

theorem isCuspVec_add {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) :
    IsCuspVec (v + w) := ⟨by rw [map_add, hv.1, hw.1], by rw [map_add, hv.2, hw.2]⟩

theorem isCuspVec_smul (c : ℂ) {v : DeckSpace N} (hv : IsCuspVec v) : IsCuspVec (c • v) :=
  ⟨by rw [map_smul, hv.1], by rw [map_smul, hv.2]⟩

theorem isCuspVec_zero : IsCuspVec (0 : DeckSpace N) := ⟨map_zero _, map_zero _⟩

theorem isCuspVec_sub {v w : DeckSpace N} (hv : IsCuspVec v) (hw : IsCuspVec w) :
    IsCuspVec (v - w) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ w]
  exact isCuspVec_add hv (isCuspVec_smul _ hw)

theorem isClosed_isCuspVec : IsClosed {v : DeckSpace N | IsCuspVec v} := by
  have h1 : IsClosed {v : DeckSpace N | deckRho N ModularGroup.T v = v} :=
    isClosed_eq (deckRho N ModularGroup.T).continuous continuous_id
  have h2 : IsClosed {v : DeckSpace N | deckRho N (-1) v = v} :=
    isClosed_eq (deckRho N (-1)).continuous continuous_id
  exact h1.inter h2

/-- **Functional equation on the critical line**: `Φ̃(½−it)Φ̃(½+it) w = w` for `w ∈ V_∞`, `t ≠ 0`. -/
theorem scatVec_linePt_neg_comp (hN : 2 ≤ N) {t : ℝ} (ht : t ≠ 0) {w : DeckSpace N}
    (hw : IsCuspVec w) : scatVec (linePt (-t)) (scatVec (linePt t) w) = w := by
  set x := scatVec (linePt (-t)) (scatVec (linePt t) w) - w
  have hx : IsCuspVec x :=
    isCuspVec_sub (scatVec_isCuspVec (scatVec_isCuspVec hw _) _) hw
  have horth : ∀ u : DeckSpace N, IsCuspVec u → ⟪u, x⟫_ℂ = 0 := fun u hu => by
    have h1 : ⟪u, scatVec (linePt (-t)) (scatVec (linePt t) w)⟫_ℂ =
        ⟪scatVec (linePt t) u, scatVec (linePt t) w⟫_ℂ := by
      rw [← inner_conj_symm, inner_scatVec_linePt_adjoint ht, inner_conj_symm]
    rw [inner_sub_right, h1, inner_scatVec_linePt hN ht hu hw, sub_self]
  have := horth x hx
  exact sub_eq_zero.mp (inner_self_eq_zero.mp this)

/-- **Symmetry of the generator transforms**: `T(−t) = Φ̃(½+it) T(t)`. -/
theorem eisTransform_neg (hN : 2 ≤ N) (ψ : HeightProfile) {v : DeckSpace N} (hv : IsCuspVec v)
    {t : ℝ} (ht : t ≠ 0) :
    eisTransform ψ v (-t) = scatVec (linePt t) (eisTransform ψ v t) := by
  have hne1 : linePt t ≠ 1 / 2 := linePt_ne_half ht
  have hne2 : linePt (-t) ≠ 1 / 2 := linePt_ne_half (neg_ne_zero.mpr ht)
  rw [eisTransform, eisTransform, neg_neg, scatExt_of_ne hne1, scatExt_of_ne hne2, scatVec_add,
    scatVec_smul, scatVec_smul]
  have hfe := scatVec_linePt_neg_comp hN (neg_ne_zero.mpr ht) hv
  rw [neg_neg] at hfe
  rw [hfe, add_comm]

theorem eisTransform_isCuspVec (ψ : HeightProfile) {v : DeckSpace N} (hv : IsCuspVec v)
    {t : ℝ} (ht : t ≠ 0) : IsCuspVec (eisTransform ψ v t) := by
  rw [eisTransform, scatExt_of_ne (linePt_ne_half (neg_ne_zero.mpr ht))]
  exact isCuspVec_add (isCuspVec_smul _ hv) (isCuspVec_smul _ (scatVec_isCuspVec hv _))

/-! ## The symmetric subspace -/

/-- The `L²` classes with values in `V_∞` and `F(−t) = Φ̃(½+it) F(t)`. -/
def symSpace (N : ℕ) : Submodule ℂ (Lp (DeckSpace N) 2 (volume : Measure ℝ)) where
  carrier := {F | ∀ᵐ t : ℝ ∂volume, IsCuspVec ((F : ℝ → DeckSpace N) t) ∧
    (F : ℝ → DeckSpace N) (-t) = scatVec (linePt t) ((F : ℝ → DeckSpace N) t)}
  zero_mem' := by
    have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (Lp.coeFn_zero (DeckSpace N) 2 (volume : Measure ℝ))
    filter_upwards [Lp.coeFn_zero (DeckSpace N) 2 (volume : Measure ℝ), hneg] with t h1 h2
    simp only [Pi.zero_apply] at h1 h2
    refine ⟨by rw [h1]; exact isCuspVec_zero, ?_⟩
    rw [h1, h2]
    have := scatVec_smul (N := N) (linePt t) 0 0
    simpa using this.symm
  add_mem' := by
    intro F G hF hG
    have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (Lp.coeFn_add F G)
    filter_upwards [hF, hG, Lp.coeFn_add F G, hneg] with t hFt hGt h1 h2
    simp only [Pi.add_apply] at h1 h2
    refine ⟨by rw [h1]; exact isCuspVec_add hFt.1 hGt.1, ?_⟩
    rw [h1, h2, hFt.2, hGt.2, scatVec_add]
  smul_mem' := by
    intro c F hF
    have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      (Lp.coeFn_smul c F)
    filter_upwards [hF, Lp.coeFn_smul c F, hneg] with t hFt h1 h2
    simp only [Pi.smul_apply] at h1 h2
    refine ⟨by rw [h1]; exact isCuspVec_smul c hFt.1, ?_⟩
    rw [h1, h2, hFt.2, scatVec_smul]

theorem isClosed_symSpace : IsClosed (symSpace N : Set (Lp (DeckSpace N) 2 (volume : Measure ℝ))) := by
  refine IsSeqClosed.isClosed fun {F G} hF hlim => ?_
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hae
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ i, IsCuspVec ((F (ns i) : ℝ → DeckSpace N) t) ∧
      (F (ns i) : ℝ → DeckSpace N) (-t) = scatVec (linePt t) ((F (ns i) : ℝ → DeckSpace N) t) :=
    ae_all_iff.mpr fun i => hF (ns i)
  filter_upwards [hae, hneg, hall] with t h1 h2 h3
  refine ⟨isClosed_isCuspVec.mem_of_tendsto h1 (Eventually.of_forall fun i => (h3 i).1), ?_⟩
  have h4 : Tendsto (fun i => scatVec (linePt t) ((F (ns i) : ℝ → DeckSpace N) t)) atTop
      (𝓝 (scatVec (linePt t) ((G : ℝ → DeckSpace N) t))) :=
    ((continuous_scatVec (linePt t)).tendsto _).comp h1
  refine tendsto_nhds_unique (h2.congr fun i => (h3 i).2) h4

theorem genTrans_mem_symSpace (hN : 2 ≤ N) (i : EisGenIndex N) : genTrans hN i ∈ symSpace N := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
    (genTrans_coeFn hN i)
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [genTrans_coeFn hN i, hneg, hne] with t h1 h2 ht
  refine ⟨by rw [h1]; exact eisTransform_isCuspVec i.prof i.cusp ht, ?_⟩
  rw [h1, h2]
  exact eisTransform_neg hN i.prof i.cusp ht

theorem combTrans_mem_symSpace (hN : 2 ≤ N) (x : EisGenIndex N →₀ ℂ) :
    combTrans hN x ∈ symSpace N := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact (symSpace N).zero_mem
  | add x y hx hy => rw [map_add]; exact (symSpace N).add_mem hx hy
  | single i a =>
    simp only [combTrans, Finsupp.linearCombination_single]
    exact (symSpace N).smul_mem a (genTrans_mem_symSpace hN i)

theorem eisTransformE_mem_symSpace (hN : 2 ≤ N) (x : eisSpace N) :
    eisTransformE hN x ∈ symSpace N := by
  refine denseRange_spanIncl.induction_on (p := fun x => eisTransformE hN x ∈ symSpace N) x
    (isClosed_symSpace.preimage (eisTransformE hN).continuous) fun y => ?_
  obtain ⟨c, hc⟩ := y.2
  have hy : y = ⟨combVec c, LinearMap.mem_range_self _ c⟩ := Subtype.ext hc.symm
  rw [hy, eisTransformE_spanIncl, transOnSpan_apply]
  exact combTrans_mem_symSpace hN c

/-- **The Eisenstein transform lands in the symmetric subspace.** -/
theorem eisTransformL2_mem_symSpace (hN : 2 ≤ N) (f : DeckL2 N) :
    eisTransformL2 hN f ∈ symSpace N :=
  eisTransformE_mem_symSpace hN _

end

end GaloisForLFunctions.RHTower.DeckPointPair
