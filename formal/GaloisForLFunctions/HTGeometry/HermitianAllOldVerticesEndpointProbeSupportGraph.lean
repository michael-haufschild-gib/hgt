import GaloisForLFunctions.HTGeometry.HermitianAllLayerEndpointPhysicalActivation
import GaloisForLFunctions.HTGeometry.AllOldVerticesEndpointProbeSupportGraph

/-!
# Arbitrary-Hermitian simultaneous old-observer inheritance

Every old-site graph witness survives one leaf attachment simultaneously
when the old attachment is merely Hermitian.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter Topology

/-- **Arbitrary-Hermitian all-old-vertices leaf-extension law.**  A finite
family of connected, nonbipartite old-observer graphs survives one
Hermitian leaf attachment simultaneously, on one common punctured real
coupling interval. -/
theorem
    exists_eventually_allOldSystemProbeSupportGraphs_good_of_isHermitian
    {I ρ S : Type*} [Fintype I] [Fintype ρ] [Fintype S]
    [DecidableEq I] [DecidableEq ρ] [DecidableEq S]
    [Nonempty I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (anchor : ρ)
    (attachment : Matrix I I ℂ)
    (hattachmentHermitian : attachment.IsHermitian)
    (G : S → SimpleGraph I)
    (hGconnected : ∀ s : S, (G s).Preconnected)
    (hGnonbipartite : ∀ s : S, ¬ (G s).IsBipartite)
    (baseProbe : ∀ s : S, GraphEdge (G s) → Matrix I I ℂ)
    (hbaseProbeHermitian :
      ∀ (s : S) (e : GraphEdge (G s)),
        (baseProbe s e).IsHermitian)
    (hbaseProbeEntry :
      ∀ (s : S) (e : GraphEdge (G s)),
        baseProbe s e e.1.1 e.1.2 ≠ 0)
    (crossSource crossMiddle crossTarget :
      ∀ _s : S, NonanchorLayer anchor → I)
    (crossProbe :
      ∀ _s : S, NonanchorLayer anchor → Matrix I I ℂ)
    (hcrossProbeHermitian :
      ∀ (s : S) (q : NonanchorLayer anchor),
        (crossProbe s q).IsHermitian)
    (hsourceMiddle :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossSource s q ≠ crossMiddle s q)
    (hmiddleTarget :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossMiddle s q ≠ crossTarget s q)
    (hattachment :
      ∀ (s : S) (q : NonanchorLayer anchor),
        attachment (crossSource s q) (crossMiddle s q) ≠ 0)
    (hcrossProbe :
      ∀ (s : S) (q : NonanchorLayer anchor),
        crossProbe s q (crossMiddle s q) (crossTarget s q) ≠ 0) :
    ∃ n : ℕ, ∃ branch : I × ρ → ℂ → ℂ,
      ∃ probe :
          ∀ s : S,
            Sum (GraphEdge (G s)) (NonanchorLayer anchor) →
              Matrix I I ℂ,
        (∀ s p, (probe s p).IsHermitian) ∧
        (∀ s p,
          probe s p =
            Sum.elim (baseProbe s) (crossProbe s) p) ∧
        Function.Injective
          (layeredEnergy
            (fun i => (energy i : ℂ))
            (fun r =>
              (codedIntegerLayerShift anchor n r : ℂ))) ∧
        (∀ x, AnalyticAt ℂ (branch x) 0) ∧
        (∀ x,
          branch x 0 =
            layeredEnergy
              (fun i => (energy i : ℂ))
              (fun r =>
                (codedIntegerLayerShift anchor n r : ℂ)) x) ∧
        (∀ x,
          ∀ᶠ t in 𝓝 0,
            matrixCharpolyRelation
              (Matrix.diagonal
                  (layeredEnergy
                    (fun i => (energy i : ℂ))
                    (fun r =>
                      (codedIntegerLayerShift anchor n r : ℂ))) +
                t • layerMatrixCoupling attachment
                  (anchorStarLayerEdge anchor),
                branch x t) = 0) ∧
        ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ s,
          (oldSystemEigenbranchProbeSupportGraph
              (layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ)))
              (layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor))
              branch (probe s) t).Preconnected ∧
            ¬ (oldSystemEigenbranchProbeSupportGraph
              (layeredEnergy
                (fun i => (energy i : ℂ))
                (fun r =>
                  (codedIntegerLayerShift anchor n r : ℂ)))
              (layerMatrixCoupling attachment
                (anchorStarLayerEdge anchor))
              branch (probe s) t).IsBipartite := by
  classical
  let Layer := NonanchorLayer anchor
  letI : Fintype (NonanchorLayer anchor) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI (s : S) : Fintype (GraphEdge (G s)) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  let Persistent :=
    Σ s : S, GraphEdge (G s) × ρ
  let persistentProbe :
      Persistent → Matrix (I × ρ) (I × ρ) ℂ :=
    fun ser =>
      layerMatrixCoupling (baseProbe ser.1 ser.2.1)
        (1 : Matrix ρ ρ ℂ)
  let persistentSource : Persistent → I × ρ :=
    fun ser => (ser.2.1.1.1, ser.2.2)
  let persistentTarget : Persistent → I × ρ :=
    fun ser => (ser.2.1.1.2, ser.2.2)
  have hpersistent :
      ∀ ser : Persistent,
        persistentProbe ser
          (persistentSource ser) (persistentTarget ser) ≠ 0 := by
    intro ser
    simp [persistentProbe, persistentSource, persistentTarget,
      layerMatrixCoupling, hbaseProbeEntry]
  obtain ⟨n, branch, hinj, hbranchAnalytic,
      hbranchBase, hbranchRoot, hall⟩ :=
    exists_eventually_allLayerCrossAndPersistentProbes_ne_zero_of_isHermitian
      energy hmax anchor
      (fun q : Σ s : S, Layer => q.2.1)
      (fun q => q.2.2)
      attachment hattachmentHermitian
      (fun q : Σ s : S, Layer => crossProbe q.1 q.2)
      (fun q => hcrossProbeHermitian q.1 q.2)
      (fun q : Σ s : S, Layer => crossSource q.1 q.2)
      (fun q : Σ s : S, Layer => crossMiddle q.1 q.2)
      (fun q : Σ s : S, Layer => crossTarget q.1 q.2)
      (fun q => hsourceMiddle q.1 q.2)
      (fun q => hmiddleTarget q.1 q.2)
      (fun q => hattachment q.1 q.2)
      (fun q => hcrossProbe q.1 q.2)
      persistentProbe persistentSource persistentTarget hpersistent
  let probe :
      ∀ s,
        Sum (GraphEdge (G s)) Layer → Matrix I I ℂ :=
    fun s p =>
      match p with
      | Sum.inl e => baseProbe s e
      | Sum.inr q => crossProbe s q
  refine ⟨n, branch, probe, ?_, ?_, hinj, hbranchAnalytic,
    hbranchBase, hbranchRoot, ?_⟩
  · intro s p
    cases p with
    | inl e => exact hbaseProbeHermitian s e
    | inr q => exact hcrossProbeHermitian s q
  · intro s p
    cases p <;> rfl
  · filter_upwards [hall] with t ht
    intro s
    let center : I :=
      Classical.choice (inferInstance : Nonempty I)
    let source : ρ → I := fun r =>
      if hr : r ≠ anchor
      then crossSource s ⟨r, hr⟩
      else center
    let target : ρ → I := fun r =>
      if hr : r ≠ anchor
      then crossTarget s ⟨r, hr⟩
      else center
    have hle :
        anchoredReplicaGraph (G s) anchor source target ≤
          oldSystemEigenbranchProbeSupportGraph
            (layeredEnergy
              (fun i => (energy i : ℂ))
              (fun r =>
                (codedIntegerLayerShift anchor n r : ℂ)))
            (layerMatrixCoupling attachment
              (anchorStarLayerEdge anchor))
            branch (probe s) t := by
      apply anchoredReplicaGraph_le_oldSystemProbeSupportGraph
      · intro a b hab r
        let e : GraphEdge (G s) := ⟨(a, b), hab⟩
        refine ⟨Sum.inl e, ?_⟩
        simpa [probe, persistentProbe, persistentSource,
          persistentTarget, e] using ht.2 ⟨s, (e, r)⟩
      · intro r hr
        let q : Layer := ⟨r, hr⟩
        refine ⟨Sum.inr q, ?_⟩
        have hsource : source r = crossSource s q := by
          simp [source, q, hr]
        have htarget : target r = crossTarget s q := by
          simp [target, q, hr]
        rw [hsource, htarget]
        simpa [probe, q] using ht.1 ⟨s, q⟩
    exact ⟨
      preconnected_of_anchoredReplicaGraph_le
        (G s) (hGconnected s) anchor source target _ hle,
      not_isBipartite_of_anchoredReplicaGraph_le
        (G s) (hGnonbipartite s) anchor source target _ hle⟩

end

end GaloisForLFunctions.HTGeometry
