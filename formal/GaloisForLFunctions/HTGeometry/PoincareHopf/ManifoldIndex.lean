import GaloisForLFunctions.HTGeometry.PoincareHopf.SmoothExtension
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# The index of a vector field at a zero on a manifold

For a manifold modelled on `ℝᵈ` and a vector field `V` on it, the chart representative at `p` is
the pullback of `V` along the inverse of the extended chart at `p`; it is a vector field on `ℝᵈ`,
smooth near the image of `p` because `V` is smooth.  The index of `V` at `p` is the local index of
that representative at the image of `p`.

The definition uses the distinguished chart at `p`, so it is well posed with no choices; that it may
be computed in any chart is the chart invariance of the local index, since the representatives in
two charts are related by the pushforward law `w ∘ ψ = Dψ · v` along the transition map.
-/

open Set VectorField
open scoped Manifold ContDiff

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]

/-- The chart representative at `p` of a vector field on `M`. -/
noncomputable def chartRep (V : Π x : M, TangentSpace 𝓘(ℝ, Fin d → ℝ) x) (p : M) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  mpullbackWithin 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
    (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm V (range 𝓘(ℝ, Fin d → ℝ))

/-- **The index of a vector field at a point of a manifold.** -/
noncomputable def mindex (V : Π x : M, TangentSpace 𝓘(ℝ, Fin d → ℝ) x) (p : M) : ℝ :=
  localIndex (chartRep V p) (extChartAt 𝓘(ℝ, Fin d → ℝ) p p)

section Smooth

variable [IsManifold 𝓘(ℝ, Fin d → ℝ) 3 M]
  {V : Π x : M, TangentSpace 𝓘(ℝ, Fin d → ℝ) x}

/-- The chart representative of a `C²` vector field is `C²` at the image of the base point. -/
theorem contDiffWithinAt_chartRep
    (hV : ContMDiff 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin d → ℝ)).tangent 2
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) M))) (p : M) :
    ContDiffWithinAt ℝ 2 (chartRep V p) (extChartAt 𝓘(ℝ, Fin d → ℝ) p).target
      (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) := by
  have h := contMDiffWithinAt_mpullbackWithin_extChartAt_symm (m := 2) (n := 3)
    ((hV p).contMDiffWithinAt) uniqueMDiffOn_univ (mem_univ p) (by norm_num)
  rw [contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt] at h
  simpa [chartRep] using h

/-- The chart representative is `C²` on a neighbourhood of the image of the base point. -/
theorem exists_contDiffOn_chartRep
    (hV : ContMDiff 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin d → ℝ)).tangent 2
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) M))) (p : M) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ extChartAt 𝓘(ℝ, Fin d → ℝ) p p ∈ U ∧
      ContDiffOn ℝ 2 (chartRep V p) U := by
  have htarget : IsOpen (extChartAt 𝓘(ℝ, Fin d → ℝ) p).target := isOpen_extChartAt_target p
  have hmem : extChartAt 𝓘(ℝ, Fin d → ℝ) p p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) p).target :=
    mem_extChartAt_target p
  have hat : ContDiffAt ℝ 2 (chartRep V p) (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) :=
    (contDiffWithinAt_chartRep hV p).contDiffAt (htarget.mem_nhds hmem)
  obtain ⟨u, hu, hcd⟩ := hat.contDiffOn (le_refl (2 : WithTop ℕ∞)) (by norm_num)
  obtain ⟨U, hUu, hUopen, hUmem⟩ := mem_nhds_iff.mp hu
  exact ⟨U, hUopen, hUmem, hcd.mono hUu⟩

/-- The chart representative vanishes exactly where the field does. -/
theorem chartRep_eq_zero_iff (V : Π x : M, TangentSpace 𝓘(ℝ, Fin d → ℝ) x) (p : M)
    {y : Fin d → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) p).target) :
    chartRep V p y = 0 ↔ V ((extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm y) = 0 := by
  have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, Fin d → ℝ)) (x := p) hy
  constructor
  · intro h
    have h2 := ContinuousLinearMap.IsInvertible.self_apply_inverse hinv
      (V ((extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm y))
    rw [show (mfderivWithin 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
        (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm (range 𝓘(ℝ, Fin d → ℝ)) y).inverse
        (V ((extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm y)) = chartRep V p y from rfl, h] at h2
    exact h2.symm.trans (map_zero _)
  · intro h
    show (mfderivWithin 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
      (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm (range 𝓘(ℝ, Fin d → ℝ)) y).inverse
      (V ((extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm y)) = 0
    rw [h, map_zero]

/-- `V` has an isolated zero at `p`. -/
def IsIsolatedZero (V : Π x : M, TangentSpace 𝓘(ℝ, Fin d → ℝ) x) (p : M) : Prop :=
  V p = 0 ∧ ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, x ≠ p → V x ≠ 0

/-- At an isolated zero the chart representative has a local index, so `mindex` is meaningful. -/
theorem exists_hasIndex_chartRep
    (hV : ContMDiff 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin d → ℝ)).tangent 2
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) M))) {p : M}
    (hiso : IsIsolatedZero V p) :
    ∃ k, HasIndex (chartRep V p) (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) k := by
  obtain ⟨hVp, UM, hUMopen, hpUM, hUM⟩ := hiso
  obtain ⟨U, hUopen, hUmem, hUcd⟩ := exists_contDiffOn_chartRep hV p
  set W : Set (Fin d → ℝ) :=
    U ∩ ((extChartAt 𝓘(ℝ, Fin d → ℝ) p).target ∩
      (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm ⁻¹' UM) with hW
  have hWopen : IsOpen W :=
    hUopen.inter ((continuousOn_extChartAt_symm p).isOpen_inter_preimage
      (isOpen_extChartAt_target p) hUMopen)
  have hpt : (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) = p :=
    extChartAt_to_inv p
  have hWmem : extChartAt 𝓘(ℝ, Fin d → ℝ) p p ∈ W := by
    refine ⟨hUmem, mem_extChartAt_target p, ?_⟩
    rw [mem_preimage, hpt]
    exact hpUM
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWopen _ hWmem
  have hsub : Metric.closedBall (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) (r / 2) ⊆ W := by
    intro y hy
    refine hball ?_
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    linarith
  refine hasIndex_of_contDiffOn hWopen (hUcd.mono (fun z hz => hz.1)) (by linarith) hsub ?_
  intro y hy hyne
  have hyW : y ∈ W := hsub hy
  have hytarget : y ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) p).target := hyW.2.1
  have hyUM : (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm y ∈ UM := hyW.2.2
  have hyp : (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm y ≠ p := by
    intro hcon
    refine hyne ?_
    have := (extChartAt 𝓘(ℝ, Fin d → ℝ) p).right_inv hytarget
    rw [← this, hcon]
  rw [Ne, chartRep_eq_zero_iff V p hytarget]
  exact hUM _ hyUM hyp

/-- The zero set of a `C²` vector field is closed. -/
theorem isClosed_zeroSet
    (hV : ContMDiff 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin d → ℝ)).tangent 2
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) M))) :
    IsClosed {x : M | V x = 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  have hpne : V p ≠ 0 := hp
  obtain ⟨U, hUopen, hUmem, hUcd⟩ := exists_contDiffOn_chartRep hV p
  have hpt : (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) = p :=
    extChartAt_to_inv p
  have hrepne : chartRep V p (extChartAt 𝓘(ℝ, Fin d → ℝ) p p) ≠ 0 := by
    rw [Ne, chartRep_eq_zero_iff V p (mem_extChartAt_target p), hpt]
    exact hpne
  have hcont : ContinuousOn (chartRep V p) U := hUcd.continuousOn
  have hopen2 : IsOpen (U ∩ chartRep V p ⁻¹' {z : Fin d → ℝ | z ≠ 0}) :=
    hcont.isOpen_inter_preimage hUopen (isOpen_ne_fun continuous_id continuous_const)
  set W : Set (Fin d → ℝ) :=
    U ∩ chartRep V p ⁻¹' {z : Fin d → ℝ | z ≠ 0} ∩ (extChartAt 𝓘(ℝ, Fin d → ℝ) p).target with hW
  have hWopen : IsOpen W := hopen2.inter (isOpen_extChartAt_target p)
  have hWmem : extChartAt 𝓘(ℝ, Fin d → ℝ) p p ∈ W :=
    ⟨⟨hUmem, hrepne⟩, mem_extChartAt_target p⟩
  refine ⟨(extChartAt 𝓘(ℝ, Fin d → ℝ) p).source ∩ extChartAt 𝓘(ℝ, Fin d → ℝ) p ⁻¹' W,
    ?_, ?_, ?_⟩
  · intro x hx
    have hxsrc : x ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) p).source := hx.1
    have hxW : extChartAt 𝓘(ℝ, Fin d → ℝ) p x ∈ W := hx.2
    have hinv : (extChartAt 𝓘(ℝ, Fin d → ℝ) p).symm (extChartAt 𝓘(ℝ, Fin d → ℝ) p x) = x :=
      (extChartAt 𝓘(ℝ, Fin d → ℝ) p).left_inv hxsrc
    intro hcon
    have hz : V x = 0 := hcon
    have hzero := (chartRep_eq_zero_iff V p hxW.2).mpr (by rw [hinv]; exact hz)
    exact hxW.1.2 hzero
  · exact (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) hWopen
  · exact ⟨mem_extChartAt_source p, hWmem⟩

/-- On a compact manifold a `C²` vector field with isolated zeros has finitely many zeros. -/
theorem finite_zeroSet [CompactSpace M]
    (hV : ContMDiff 𝓘(ℝ, Fin d → ℝ) (𝓘(ℝ, Fin d → ℝ)).tangent 2
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, Fin d → ℝ) M)))
    (hiso : ∀ p : M, V p = 0 → IsIsolatedZero V p) :
    {x : M | V x = 0}.Finite := by
  classical
  have hcl : IsClosed {x : M | V x = 0} := isClosed_zeroSet hV
  have hcomp : IsCompact {x : M | V x = 0} := hcl.isCompact
  have hnb : ∀ p ∈ {x : M | V x = 0}, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, x ∈ {x : M | V x = 0} → x = p := by
    intro p hp
    obtain ⟨-, U, hUopen, hpU, hU⟩ := hiso p hp
    refine ⟨U, hUopen, hpU, fun x hx hxz => ?_⟩
    by_contra hne
    exact hU x hx hne hxz
  choose! U hUopen hpU hUiso using hnb
  obtain ⟨t, hts, htcover⟩ := hcomp.elim_nhds_subcover U
    (fun p hp => (hUopen p hp).mem_nhds (hpU p hp))
  refine Set.Finite.subset t.finite_toSet fun x hx => ?_
  obtain ⟨p, hpt, hxU⟩ := Set.mem_iUnion₂.mp (htcover hx)
  have hxeq := hUiso p (hts p hpt) x hxU hx
  rw [hxeq]
  exact hpt

end Smooth

end GaloisForLFunctions.HTGeometry.PoincareHopf
