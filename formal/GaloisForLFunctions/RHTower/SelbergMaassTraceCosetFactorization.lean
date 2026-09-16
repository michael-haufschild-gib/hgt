import GaloisForLFunctions.RHTower.SelbergMaassFiniteIndexTrace

/-!
# Product coordinates for nested relative Maass trace quotients

For nested subgroups `G ≤ H ≤ K`, the direct relative quotient from `G` to `K`
factors as the outer quotient from `H` to `K` and the inner quotient from `G` to
`H`.  The equivalence is stated with the exact `subgroupOf` quotient types used
by `maassTraceFunction`; this is the group-theoretic coordinate change required
for a trace-composition theorem.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff

noncomputable section

variable {A : Type*} [Group A]
variable {G H K : Subgroup A}

/-- Transporting the smaller relative subgroup through `H.subgroupOf K ≃ H`
recovers the relative subgroup inside `H`. -/
theorem nested_subgroupOf_map (hHK : H ≤ K) :
    Subgroup.map (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
      ((G.subgroupOf K).subgroupOf (H.subgroupOf K)) = G.subgroupOf H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨⟨⟨x.1, hHK x.2⟩, x.2⟩, ?_, ?_⟩
    · exact hx
    · rfl

/-- The inner relative quotient inside `K` is canonically equivalent to the
ordinary relative quotient from `G` to `H`. -/
noncomputable def nestedRelativeCosetEquiv (hHK : H ≤ K) :
    (H.subgroupOf K) ⧸ (G.subgroupOf K).subgroupOf (H.subgroupOf K) ≃
      H ⧸ G.subgroupOf H :=
  Quotient.congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv (by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    change a⁻¹ * b ∈ (G.subgroupOf K).subgroupOf (H.subgroupOf K) ↔
      (Subgroup.subgroupOfEquivOfLe hHK a)⁻¹ * (Subgroup.subgroupOfEquivOfLe hHK b) ∈
        G.subgroupOf H
    rw [← (Subgroup.subgroupOfEquivOfLe hHK).map_inv,
      ← (Subgroup.subgroupOfEquivOfLe hHK).map_mul,
      ← nested_subgroupOf_map hHK]
    constructor
    · intro hab
      exact ⟨a⁻¹ * b, hab, rfl⟩
    · rintro ⟨c, hc, heq⟩
      have hca : c = a⁻¹ * b := by
        apply (Subgroup.subgroupOfEquivOfLe hHK).injective
        change (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom c =
          (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom (a⁻¹ * b)
        rw [map_mul, map_inv]
        exact heq
      rw [← hca]
      exact hc)

@[simp] theorem nestedRelativeCosetEquiv_mk (hHK : H ≤ K) (h : H.subgroupOf K) :
    nestedRelativeCosetEquiv (G := G) hHK (QuotientGroup.mk h) =
      QuotientGroup.mk (Subgroup.subgroupOfEquivOfLe hHK h) :=
  rfl

/-- Product coordinates for the direct relative quotient of a nested subgroup chain. -/
noncomputable def maassTraceCosetProductEquiv (hGH : G ≤ H) (hHK : H ≤ K) :
    K ⧸ G.subgroupOf K ≃
      (K ⧸ H.subgroupOf K) × (H ⧸ G.subgroupOf H) :=
  (Subgroup.quotientEquivProdOfLE (by
    intro x hx
    simp only [Subgroup.mem_subgroupOf] at hx ⊢
    exact hGH hx)).trans
    (Equiv.prodCongr (Equiv.refl _) (nestedRelativeCosetEquiv hHK))

/-- A direct trace summand in product coset coordinates is the corresponding
inner summand evaluated after the outer representative acts. -/
theorem maassTraceCosetProduct_summand
    {G₀ H₀ K₀ : Subgroup (GL (Fin 2) ℝ)} (hGH : G₀ ≤ H₀) (hHK : H₀ ≤ K₀)
    (f : glUpperHalfPlaneInvariantFunctions G₀)
    (p : K₀ ⧸ H₀.subgroupOf K₀) (r : H₀ ⧸ G₀.subgroupOf H₀) (z : ℍ) :
    maassTraceQuotientFunc (G := G₀) (H := K₀) f
      ((maassTraceCosetProductEquiv hGH hHK).symm (p, r)) z =
    maassTraceQuotientFunc (G := G₀) (H := H₀) f r (p.out.val⁻¹ • z) := by
  induction r using Quotient.inductionOn with
  | h r =>
    rw [maassTraceQuotientFunc_mk]
    have hr :
        (nestedRelativeCosetEquiv (G := G₀) hHK).symm (QuotientGroup.mk r) =
          QuotientGroup.mk ((Subgroup.subgroupOfEquivOfLe hHK).symm r) := by
      apply (nestedRelativeCosetEquiv (G := G₀) hHK).injective
      rw [Equiv.apply_symm_apply, nestedRelativeCosetEquiv_mk]
      simp
    unfold maassTraceCosetProductEquiv
    dsimp
    change maassTraceQuotientFunc f
      ((Subgroup.quotientEquivProdOfLE _).symm
        (p, (nestedRelativeCosetEquiv (G := G₀) hHK).symm (QuotientGroup.mk r))) z =
      f.1 (r.val⁻¹ • p.out.val⁻¹ • z)
    rw [hr]
    simp
    rw [mul_smul]

/-- A quotient summand of an already traced function is the inner trace evaluated
at the canonical outer representative. -/
theorem maassTraceQuotientFunc_of_trace
    {G₀ H₀ K₀ : Subgroup (GL (Fin 2) ℝ)} [G₀.IsFiniteRelIndex H₀]
    (hHK : H₀ ≤ K₀) (f : glUpperHalfPlaneInvariantFunctions G₀)
    (q : K₀ ⧸ H₀.subgroupOf K₀) (z : ℍ) :
    maassTraceQuotientFunc (G := H₀) (H := K₀)
      (maassTraceInvariant (G := G₀) (H := H₀) f) q z =
      maassTraceFunction (G := G₀) (H := H₀) f (q.out.val⁻¹ • z) := by
  induction q using Quotient.inductionOn with
  | h q =>
    rw [maassTraceQuotientFunc_mk]
    let q0 : K₀ := (QuotientGroup.mk q : K₀ ⧸ H₀.subgroupOf K₀).out
    have hq_mem : q0⁻¹ * q ∈ H₀.subgroupOf K₀ := by
      apply QuotientGroup.eq.mp
      exact Quotient.out_eq' (QuotientGroup.mk q)
    let hq : H₀ := ⟨(q0⁻¹ * q : K₀).val, hq_mem⟩
    let hqK : K₀ := ⟨hq.1, hHK hq.2⟩
    have hq_eq : q = q0 * hqK := by
      apply Subtype.ext
      simp [hqK, hq]
    change (maassTraceInvariant (G := G₀) (H := H₀) f).1 (q.val⁻¹ • z) =
      (maassTraceInvariant (G := G₀) (H := H₀) f).1 (q0.val⁻¹ • z)
    rw [hq_eq]
    change (maassTraceInvariant (G := G₀) (H := H₀) f).1 ((q0.val * hqK.val)⁻¹ • z) =
      (maassTraceInvariant (G := G₀) (H := H₀) f).1 (q0.val⁻¹ • z)
    rw [mul_inv_rev, mul_smul]
    exact (maassTraceInvariant (G := G₀) (H := H₀) f).2 ⟨hq⁻¹, inv_mem hq.2⟩ _

/-- Finite Maass traces compose along a nested finite-index subgroup chain. -/
theorem maassTraceFunction_transitive
    {G₀ H₀ K₀ : Subgroup (GL (Fin 2) ℝ)}
    [G₀.IsFiniteRelIndex H₀] [H₀.IsFiniteRelIndex K₀] [G₀.IsFiniteRelIndex K₀]
    (hGH : G₀ ≤ H₀) (hHK : H₀ ≤ K₀) (f : glUpperHalfPlaneInvariantFunctions G₀) :
    maassTraceFunction (G := G₀) (H := K₀) f =
      maassTraceFunction (G := H₀) (H := K₀) (maassTraceInvariant (G := G₀) (H := H₀) f) := by
  funext z
  letI := Fintype.ofFinite (K₀ ⧸ G₀.subgroupOf K₀)
  letI := Fintype.ofFinite (K₀ ⧸ H₀.subgroupOf K₀)
  letI := Fintype.ofFinite (H₀ ⧸ G₀.subgroupOf H₀)
  unfold maassTraceFunction
  calc
    ∑ q : K₀ ⧸ G₀.subgroupOf K₀, maassTraceQuotientFunc f q z =
        ∑ qr : (K₀ ⧸ H₀.subgroupOf K₀) × (H₀ ⧸ G₀.subgroupOf H₀),
          maassTraceQuotientFunc f ((maassTraceCosetProductEquiv hGH hHK).symm qr) z := by
      simpa using (Equiv.sum_comp (maassTraceCosetProductEquiv hGH hHK)
        fun qr => maassTraceQuotientFunc f ((maassTraceCosetProductEquiv hGH hHK).symm qr) z)
    _ = ∑ q : K₀ ⧸ H₀.subgroupOf K₀,
        ∑ r : H₀ ⧸ G₀.subgroupOf H₀,
          maassTraceQuotientFunc f r (q.out.val⁻¹ • z) := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro q
      apply Fintype.sum_congr
      intro r
      exact maassTraceCosetProduct_summand hGH hHK f q r z
    _ = ∑ q : K₀ ⧸ H₀.subgroupOf K₀,
        maassTraceQuotientFunc (maassTraceInvariant (G := G₀) (H := H₀) f) q z := by
      apply Fintype.sum_congr
      intro q
      rw [maassTraceQuotientFunc_of_trace hHK]
      rfl

end

end GaloisForLFunctions.RHTower
