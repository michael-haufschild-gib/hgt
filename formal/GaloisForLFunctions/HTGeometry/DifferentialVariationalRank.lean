import GaloisForLFunctions.HTGeometry.DifferentialVariationalOreModule
import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreField
import GaloisForLFunctions.HTGeometry.KaehlerDifferentialIndependence
import GaloisForLFunctions.HTGeometry.MvPolynomialGradient
import GaloisForLFunctions.HTGeometry.DifferentialTranscendenceDegree
import GaloisForLFunctions.HTGeometry.WickContractedMatroidPersistence

/-!
# Differential transcendence rank of the variational Ore module

This leaf proves the exact finite-rank bridge omitted from the original variational-building
infrastructure. Differential algebraicity gives an explicit nonzero Ore operator annihilating the
universal differential modulo torsion. For every finite family, differential independence is
therefore equivalent to linear independence of its variational classes, and also to independence
of their coordinates over the rational pseudodifferential skew field.

A differential-matroid basis of any finite differential generating tuple becomes a skew-field
basis of the localized coordinate space. Comparing its cardinality with an arbitrary finite
operator basis proves that the rank of `Ω[K⁄C] / Tor` is exactly the differential transcendence
degree over the canonical zero derivation on the constant base.
-/

open scoped Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]

private theorem coeff_unitJetOperator (c : Unit × ℕ →₀ K) (n : ℕ) :
    DiffOp.coeff (c.sum fun i a => DiffOp.mono i.2 a) n = c ((), n) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [DiffOp.coeff_zero]
  | @single_add i a p hia hip ih =>
      rw [Finsupp.sum_add_index
        (fun j _ => DiffOp.mono_zero j.2)
        (fun j _ => DiffOp.mono_add j.2)]
      have hs : (Finsupp.single i a).sum (fun j b => DiffOp.mono j.2 b) =
          DiffOp.mono i.2 a :=
        Finsupp.sum_single_index (DiffOp.mono_zero i.2)
      rw [hs, DiffOp.coeff_add, ih, DiffOp.coeff_mono]
      rcases i with ⟨u, m⟩
      cases u
      by_cases hmn : m = n
      · subst m
        simp
      · simp [hmn]

private theorem unitJetOperator_smul_D
    (hC : ∀ c : C, Differential.deriv (algebraMap C K c) = 0)
    (c : Unit × ℕ →₀ K) (x : K) :
    (letI : Module (DiffOp K) Ω[K⁄C] := kaehlerDiffOpModule hC;
      (c.sum fun i a => DiffOp.mono i.2 a) • KaehlerDifferential.D C K x) =
        c.sum fun i a => a • KaehlerDifferential.D C K (differentialJet i.2 x) := by
  letI : Module (DiffOp K) Ω[K⁄C] := kaehlerDiffOpModule hC
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add i a p hia hip ih =>
      rw [Finsupp.sum_add_index
        (fun j _ => DiffOp.mono_zero j.2)
        (fun j _ => DiffOp.mono_add j.2)]
      rw [Finsupp.sum_add_index
        (fun j _ => zero_smul K
          (KaehlerDifferential.D C K (differentialJet j.2 x)))
        (fun j _ b₁ b₂ => add_smul b₁ b₂
          (KaehlerDifferential.D C K (differentialJet j.2 x)))]
      have hop : (Finsupp.single i a).sum (fun j b => DiffOp.mono j.2 b) =
          DiffOp.mono i.2 a :=
        Finsupp.sum_single_index (DiffOp.mono_zero i.2)
      have hvec : (Finsupp.single i a).sum
          (fun j b => b • KaehlerDifferential.D C K (differentialJet j.2 x)) =
          a • KaehlerDifferential.D C K (differentialJet i.2 x) :=
        Finsupp.sum_single_index (zero_smul K _)
      have hmono : DiffOp.mono i.2 a • KaehlerDifferential.D C K x =
          a • KaehlerDifferential.D C K (differentialJet i.2 x) := by
        change diffOpSMul hC (DiffOp.mono i.2 a) (KaehlerDifferential.D C K x) = _
        rw [diffOpSMul_mono, kaehlerConnection_iterate_D]
      rw [hop, hvec, add_smul, ih, hmono]

theorem kaehlerD_mem_oreTorsion_of_differentialAlgebraicOver
    [IsConstantBase C K] [CharZero C] {x : K}
    (hx : DifferentialAlgebraicOver C x) :
    KaehlerDifferential.D C K x ∈
      DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C]) := by
  classical
  obtain ⟨c, hc, hrel⟩ :=
    GaloisForLFunctions.exists_nonzero_kaehler_relation_of_not_algebraicIndependent
      (fun i : Unit × ℕ => differentialJet i.2 x) hx
  let p : DiffOp K := c.sum fun i a => DiffOp.mono i.2 a
  refine ⟨p, ?_, ?_⟩
  · intro hp
    apply hc
    ext i
    rcases i with ⟨u, n⟩
    cases u
    have hcoeff := congrArg (fun q : DiffOp K => DiffOp.coeff q n) hp
    simpa [p, coeff_unitJetOperator] using hcoeff
  · rw [unitJetOperator_smul_D IsConstantBase.deriv_algebraMap]
    rw [Finsupp.linearCombination_apply] at hrel
    exact hrel

private noncomputable def jetRelationOperatorRow {ι : Type*} [Fintype ι]
    (c : ι × ℕ →₀ K) : ι → DiffOp K := by
  classical
  exact c.sum fun p a => Pi.single p.1 (DiffOp.mono p.2 a)

private theorem coeff_jetRelationOperatorRow {ι : Type*} [Fintype ι]
    (c : ι × ℕ →₀ K) (i : ι) (n : ℕ) :
    DiffOp.coeff (jetRelationOperatorRow c i) n = c (i, n) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [jetRelationOperatorRow]
  | @single_add p a c hp ha ih =>
      have hsum : jetRelationOperatorRow (Finsupp.single p a + c) =
          Pi.single p.1 (DiffOp.mono p.2 a) + jetRelationOperatorRow c := by
        unfold jetRelationOperatorRow
        rw [Finsupp.sum_add_index]
        · rw [Finsupp.sum_single_index]
          simp
        · intro q hq
          simp [DiffOp.mono_zero]
        · intro q hq b₁ b₂
          funext j
          by_cases hj : j = q.1
          · subst j
            simp [DiffOp.mono_add]
          · simp [Pi.single_eq_of_ne hj, DiffOp.mono_add]
      rw [hsum, Pi.add_apply, DiffOp.coeff_add, ih]
      rcases p with ⟨j, m⟩
      by_cases hji : j = i
      · subst j
        by_cases hmn : m = n
        · subst m
          simp
        · simp [Pi.single_eq_same, DiffOp.coeff_mono, hmn]
      · have hij : i ≠ j := Ne.symm hji
        rw [Pi.single_eq_of_ne hij]
        have hpair : (j, m) ≠ (i, n) := fun h => hji (congrArg Prod.fst h)
        simp [hpair]

private theorem jetRelationOperatorRow_ne_zero {ι : Type*} [Fintype ι]
    {c : ι × ℕ →₀ K} (hc : c ≠ 0) : jetRelationOperatorRow c ≠ 0 := by
  intro hrow
  apply hc
  ext p
  have h := congrArg (fun q : ι → DiffOp K => DiffOp.coeff (q p.1) p.2) hrow
  simpa [coeff_jetRelationOperatorRow] using h

private theorem jetRelationOperatorRow_smul_D {ι : Type*} [Fintype ι]
    [IsConstantBase C K] (c : ι × ℕ →₀ K) (y : ι → K) :
    ∑ i, jetRelationOperatorRow c i • KaehlerDifferential.D C K (y i) =
      c.sum fun p a => a • KaehlerDifferential.D C K (differentialJet p.2 (y p.1)) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [jetRelationOperatorRow]
  | @single_add p a c hp ha ih =>
      have hsum : jetRelationOperatorRow (Finsupp.single p a + c) =
          Pi.single p.1 (DiffOp.mono p.2 a) + jetRelationOperatorRow c := by
        unfold jetRelationOperatorRow
        rw [Finsupp.sum_add_index]
        · rw [Finsupp.sum_single_index]
          simp
        · intro q hq
          simp [DiffOp.mono_zero]
        · intro q hq b₁ b₂
          funext j
          by_cases hj : j = q.1
          · subst j
            simp [DiffOp.mono_add]
          · simp [Pi.single_eq_of_ne hj, DiffOp.mono_add]
      rw [Finsupp.sum_add_index]
      · have hscalar : (Finsupp.single p a).sum
            (fun q b => b • KaehlerDifferential.D C K (differentialJet q.2 (y q.1))) =
            a • KaehlerDifferential.D C K (differentialJet p.2 (y p.1)) :=
          Finsupp.sum_single_index (zero_smul K _)
        rw [hscalar]
        rw [hsum]
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ih]
        have hsingle : ∑ i : ι,
            ((Pi.single p.1 (DiffOp.mono p.2 a) : ι → DiffOp K) i) •
              KaehlerDifferential.D C K (y i) =
            a • KaehlerDifferential.D C K (differentialJet p.2 (y p.1)) := by
          rw [Finset.sum_eq_single p.1]
          · rw [Pi.single_eq_same, diffOp_smul_def, diffOpSMul_mono,
              kaehlerConnection_iterate_D]
          · intro i hi hne
            rw [Pi.single_eq_of_ne hne]
            simp
          · simp
        rw [hsingle]
      · intro q hq
        simp
      · intro q hq b₁ b₂
        exact add_smul b₁ b₂ _

theorem differentialIndependent_iff_linearIndependent_variationalOre
    {ι : Type*} [Fintype ι] [IsConstantBase C K] [CharZero C] (y : ι → K) :
    DifferentialIndependent C y ↔
      LinearIndependent (DiffOp K) (fun i =>
        (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
          (KaehlerDifferential.D C K (y i))) := by
  constructor
  · intro hy
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let yFin : Fin (Fintype.card ι) → K := fun j => y (e.symm j)
    have hyFin : DifferentialIndependent C yFin := by
      exact (differentialIndependent_equiv e.symm y).mpr hy
    have hfin : LinearIndependent (DiffOp K) (fun j =>
        (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
          (KaehlerDifferential.D C K (yFin j))) :=
      linearIndependent_mkQ_of_torsion
        (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C]))
        (fun _ hω => hω)
        (linearIndependent_diffOp_D_of_differentialIndependent hyFin)
    have h := (linearIndependent_equiv e).mpr hfin
    have hfamily :
        ((fun j =>
          (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
            (KaehlerDifferential.D C K (yFin j))) ∘ e) =
          (fun i =>
            (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
              (KaehlerDifferential.D C K (y i))) := by
      funext i
      change
        (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
            (KaehlerDifferential.D C K (y (e.symm (e i)))) =
          (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
            (KaehlerDifferential.D C K (y i))
      rw [e.symm_apply_apply]
    rwa [hfamily] at h
  · intro hlin
    unfold DifferentialIndependent
    by_contra hdep
    obtain ⟨c, hc, hrel⟩ :=
      GaloisForLFunctions.exists_nonzero_kaehler_relation_of_not_algebraicIndependent
        (fun p : ι × ℕ => differentialJet p.2 (y p.1)) hdep
    have hraw : ∑ i, jetRelationOperatorRow c i • KaehlerDifferential.D C K (y i) = 0 := by
      rw [jetRelationOperatorRow_smul_D]
      rwa [Finsupp.linearCombination_apply] at hrel
    have hquot : ∑ i, jetRelationOperatorRow c i •
        (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
          (KaehlerDifferential.D C K (y i)) = 0 := by
      have hmapped := congrArg
        (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ hraw
      rw [map_sum, map_zero] at hmapped
      simpa only [map_smul] using hmapped
    have hzero := (Fintype.linearIndependent_iff.mp hlin) (jetRelationOperatorRow c) hquot
    exact jetRelationOperatorRow_ne_zero hc (funext hzero)

/-- Coordinates of one variational class in a finite operator basis. -/
noncomputable def variationalOreCoordinateRow {m : ℕ}
    [IsConstantBase C K]
    (b : Module.Basis (Fin m) (DiffOp K) (VariationalOreModule C K))
    (v : VariationalOreModule C K) : Fin m → DiffOp K :=
  fun j => b.repr v j

/-- Operator-basis coordinates embedded in the rational pseudodifferential skew field. -/
noncomputable def localizedVariationalOreCoordinateRow {m : ℕ}
    [IsConstantBase C K]
    (b : Module.Basis (Fin m) (DiffOp K) (VariationalOreModule C K))
    (v : VariationalOreModule C K) : Fin m → DiffOp.PseudoDiffOp K :=
  fun j => OreLocalization.numeratorRingHom (variationalOreCoordinateRow b v j)

private theorem linearIndependent_variationalOreCoordinateRow_iff
    {ι : Type*} [Fintype ι] [IsConstantBase C K] {m : ℕ}
    (b : Module.Basis (Fin m) (DiffOp K) (VariationalOreModule C K))
    (v : ι → VariationalOreModule C K) :
    LinearIndependent (DiffOp K) (fun i => variationalOreCoordinateRow b (v i)) ↔
      LinearIndependent (DiffOp K) v := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h g hg i
    apply h g
    · funext j
      have hrepr := congrArg (fun w => b.repr w j) hg
      simpa [variationalOreCoordinateRow] using hrepr
  · intro h g hg i
    apply h g
    · apply b.repr.injective
      apply Finsupp.ext
      intro j
      have hcoord := congrFun hg j
      simpa [variationalOreCoordinateRow] using hcoord

private theorem linearIndependent_localizedVariationalOreCoordinateRow_iff
    {ι : Type*} [Fintype ι] [IsConstantBase C K] {m : ℕ}
    (b : Module.Basis (Fin m) (DiffOp K) (VariationalOreModule C K))
    (v : ι → VariationalOreModule C K) :
    LinearIndependent (DiffOp.PseudoDiffOp K)
        (fun i => localizedVariationalOreCoordinateRow b (v i)) ↔
      LinearIndependent (DiffOp K)
        (fun i => variationalOreCoordinateRow b (v i)) := by
  classical
  constructor
  · intro hQ
    rw [Fintype.linearIndependent_iff] at hQ ⊢
    intro g hg i
    have hQrel : ∑ k,
        (OreLocalization.numeratorRingHom (g k) : DiffOp.PseudoDiffOp K) •
          localizedVariationalOreCoordinateRow b (v k) = 0 := by
      funext j
      have hcoord := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      have hmapped := congrArg
        (OreLocalization.numeratorRingHom : DiffOp K → DiffOp.PseudoDiffOp K) hcoord
      rw [map_sum, map_zero] at hmapped
      simpa [localizedVariationalOreCoordinateRow, variationalOreCoordinateRow,
        Pi.smul_apply, smul_eq_mul, map_mul] using hmapped
    have hzero := hQ
      (fun k => (OreLocalization.numeratorRingHom (g k) : DiffOp.PseudoDiffOp K)) hQrel i
    exact DiffOp.numeratorRingHom_injective (by simpa using hzero)
  · intro hR
    have hrow : DiffOp.RowIndep
        (fun i => variationalOreCoordinateRow b (v i)) := by
      intro g hg
      funext i
      apply (Fintype.linearIndependent_iff.mp hR) g
      · funext j
        have hcoord := congrFun hg j
        simpa [DiffOp.vecMul, Pi.smul_apply, smul_eq_mul] using hcoord
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∀ j, ∑ i, g i *
        DiffOp.toPseudoMatrix
          (fun i => variationalOreCoordinateRow b (v i)) i j = 0 := by
      intro j
      have hcoord := congrFun hg j
      simpa [localizedVariationalOreCoordinateRow, DiffOp.toPseudoMatrix,
        Pi.smul_apply, smul_eq_mul] using hcoord
    have hzero := DiffOp.rowIndep_toPseudoMatrix
      (fun i => variationalOreCoordinateRow b (v i)) hrow g hg'
    exact fun i => congrFun hzero i

/-- Differential independence is exactly skew-field linear independence of the localized
coordinate rows of the variational classes of universal differentials. -/
theorem differentialIndependent_iff_linearIndependent_localizedVariationalOre
    {ι : Type*} [Fintype ι] [IsConstantBase C K] [CharZero C]
    {m : ℕ} (b : Module.Basis (Fin m) (DiffOp K) (VariationalOreModule C K))
    (y : ι → K) :
    DifferentialIndependent C y ↔
      LinearIndependent (DiffOp.PseudoDiffOp K) (fun i =>
        localizedVariationalOreCoordinateRow b
          ((DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
            (KaehlerDifferential.D C K (y i)))) := by
  rw [linearIndependent_localizedVariationalOreCoordinateRow_iff,
    linearIndependent_variationalOreCoordinateRow_iff]
  exact differentialIndependent_iff_linearIndependent_variationalOre y

/-- A finite differential generating tuple spans the variational Ore quotient by the classes of
its universal differentials. -/
theorem span_variationalOre_D_eq_top [IsConstantBase C K]
    {n : ℕ} {y : Fin n → K} (hy : differentialAdjoin C (Set.range y) = ⊤) :
    Submodule.span (DiffOp K) (Set.range fun i =>
      (DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
        (KaehlerDifferential.D C K (y i))) = ⊤ := by
  let N : Submodule (DiffOp K) (Ω[K⁄C]) :=
    DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])
  have himg : Submodule.map N.mkQ
      (Submodule.span (DiffOp K) (KaehlerDifferential.D C K '' Set.range y)) = ⊤ := by
    rw [span_diffOp_D_eq_top hy, Submodule.map_top, N.range_mkQ]
  rw [Submodule.map_span] at himg
  have hset : (N.mkQ : Ω[K⁄C] → (Ω[K⁄C]) ⧸ N) ''
      (KaehlerDifferential.D C K '' Set.range y) =
        Set.range fun i => N.mkQ (KaehlerDifferential.D C K (y i)) := by
    rw [← Set.image_comp, ← Set.range_comp]
    rfl
  rwa [hset] at himg

/-- After embedding operator coordinates in the skew field of fractions, a finite differential
generating tuple spans the full coordinate space of every finite variational basis. -/
theorem span_localizedVariationalOreCoordinateRow_eq_top
    [IsConstantBase C K] {n m : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤)
    (b : Module.Basis (Fin m) (DiffOp K) (VariationalOreModule C K)) :
    Submodule.span (DiffOp.PseudoDiffOp K) (Set.range fun i =>
      localizedVariationalOreCoordinateRow b
        ((DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])).mkQ
          (KaehlerDifferential.D C K (y i)))) = ⊤ := by
  classical
  let N : Submodule (DiffOp K) (Ω[K⁄C]) :=
    DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])
  let qD : K → VariationalOreModule C K := fun x =>
    N.mkQ (KaehlerDifferential.D C K x)
  let W : Submodule (DiffOp.PseudoDiffOp K) (Fin m → DiffOp.PseudoDiffOp K) :=
    Submodule.span (DiffOp.PseudoDiffOp K) (Set.range fun i =>
      localizedVariationalOreCoordinateRow b (qD (y i)))
  have hspanM : Submodule.span (DiffOp K) (Set.range fun i => qD (y i)) = ⊤ := by
    exact span_variationalOre_D_eq_top hy
  have hbmem : ∀ j : Fin m, localizedVariationalOreCoordinateRow b (b j) ∈ W := by
    intro j
    have hj : b j ∈ Submodule.span (DiffOp K) (Set.range fun i => qD (y i)) := by
      rw [hspanM]
      exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun v _ => localizedVariationalOreCoordinateRow b v ∈ W) ?_ ?_ ?_ ?_ hj
    · rintro v ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · have hzero : localizedVariationalOreCoordinateRow b 0 = 0 := by
        funext k
        simp [localizedVariationalOreCoordinateRow, variationalOreCoordinateRow]
      rw [hzero]
      exact W.zero_mem
    · intro v w _ _ hv hw
      have hadd : localizedVariationalOreCoordinateRow b (v + w) =
          localizedVariationalOreCoordinateRow b v +
            localizedVariationalOreCoordinateRow b w := by
        funext k
        simp [localizedVariationalOreCoordinateRow, variationalOreCoordinateRow]
      rw [hadd]
      exact W.add_mem hv hw
    · intro a v _ hv
      have hsmul : localizedVariationalOreCoordinateRow b (a • v) =
          (OreLocalization.numeratorRingHom a : DiffOp.PseudoDiffOp K) •
            localizedVariationalOreCoordinateRow b v := by
        funext k
        simp [localizedVariationalOreCoordinateRow, variationalOreCoordinateRow,
          Pi.smul_apply, smul_eq_mul, map_mul]
      rw [hsmul]
      exact W.smul_mem (OreLocalization.numeratorRingHom a : DiffOp.PseudoDiffOp K) hv
  apply le_antisymm le_top
  rw [← (Pi.basisFun (DiffOp.PseudoDiffOp K) (Fin m)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  have hbasis : localizedVariationalOreCoordinateRow b (b j) =
      Pi.basisFun (DiffOp.PseudoDiffOp K) (Fin m) j := by
    funext k
    by_cases hkj : k = j
    · subst k
      simp only [localizedVariationalOreCoordinateRow, variationalOreCoordinateRow,
        Module.Basis.repr_self, Finsupp.single_eq_same, Pi.basisFun_apply,
        Pi.single_eq_same]
      exact map_one OreLocalization.numeratorRingHom
    · simp [localizedVariationalOreCoordinateRow, variationalOreCoordinateRow,
        Pi.basisFun_apply, hkj]
  rw [← hbasis]
  exact hbmem j

/-- Canonical zero differential structure on a constant coefficient field. -/
@[reducible] noncomputable def constantBaseZeroDifferential
    (C : Type*) [Field C] : Differential C :=
  ⟨0⟩

/-- A constant-base embedding is a differential-algebra embedding when the base carries its
canonical zero derivation. -/
theorem constantBaseDifferentialAlgebra
    {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [IsConstantBase C K] :
    @DifferentialAlgebra C K _ _ _ (constantBaseZeroDifferential C) _ := by
  letI : Differential C := constantBaseZeroDifferential C
  exact ⟨fun c => by
    change Differential.deriv (algebraMap C K c) = algebraMap C K 0
    rw [map_zero]
    exact IsConstantBase.deriv_algebraMap c⟩

/-- Characteristic zero ascends canonically along a field extension. -/
theorem constantBaseTargetCharZero
    (C K : Type*) [Field C] [Field K] [Algebra C K] [CharZero C] : CharZero K :=
  CharZero.mk fun m n h =>
    Nat.cast_injective (R := C) ((algebraMap C K).injective (by simpa using h))

/-- Differential transcendence degree over a coefficient field canonically regarded as a field
of differential constants. -/
noncomputable def constantBaseDifferentialTranscendenceDegree
    (C K : Type u) [Field C] [Field K] [Algebra C K] [Differential K]
    [IsConstantBase C K] [CharZero C] : Cardinal :=
  @differentialTranscendenceDegree C K _ _ _
    (constantBaseZeroDifferential C) _
    (constantBaseDifferentialAlgebra (C := C) (K := K))
    (constantBaseTargetCharZero C K)

/-- **Exact variational rank identity.** For every finitely differentially generated extension
over a characteristic-zero constant base, the operator rank of the torsion-free variational
Kähler quotient is its differential transcendence degree. -/
theorem variationalOreModule_rank_eq_differentialTranscendenceDegree
    {C K : Type u} [Field C] [Field K] [Algebra C K] [Differential K]
    [IsConstantBase C K] [CharZero C] {n : ℕ} {y : Fin n → K}
    (hy : differentialAdjoin C (Set.range y) = ⊤) :
    Module.rank (DiffOp K) (VariationalOreModule C K) =
      constantBaseDifferentialTranscendenceDegree C K := by
  classical
  letI : Differential C := constantBaseZeroDifferential C
  letI : DifferentialAlgebra C K :=
    constantBaseDifferentialAlgebra (C := C) (K := K)
  letI : CharZero K := constantBaseTargetCharZero C K
  let M := differentialMatroid C K
  let S : Set K := Set.range y
  have hSground : S ⊆ M.E := by
    intro x hx
    change x ∈ (differentialMatroid C K).E
    rw [differentialMatroid_ground]
    exact Set.mem_univ x
  obtain ⟨B, hB⟩ := M.exists_isBasis S hSground
  have hBfin : B.Finite := (Set.finite_range y).subset hB.subset
  letI : Fintype B := hBfin.fintype
  obtain ⟨m, ⟨b⟩⟩ := exists_fin_basis_variationalOreModule hy
  let N : Submodule (DiffOp K) (Ω[K⁄C]) :=
    DiffOp.oreTorsionSubmodule (K := K) (M := Ω[K⁄C])
  let qD : K → VariationalOreModule C K := fun x =>
    N.mkQ (KaehlerDifferential.D C K x)
  let qrow : K → Fin m → DiffOp.PseudoDiffOp K := fun x =>
    localizedVariationalOreCoordinateRow b (qD x)
  have hBdiff : DifferentialIndependent C (fun z : B => (z : K)) := by
    change DiffIndepOn C B
    exact differentialMatroid_indep_iff.mp (by simpa [M] using hB.indep)
  have hBlin : LinearIndependent (DiffOp.PseudoDiffOp K) (fun z : B => qrow z) := by
    have h :=
      (differentialIndependent_iff_linearIndependent_localizedVariationalOre
        b (fun z : B => (z : K))).mp hBdiff
    simpa [qrow, qD, N] using h
  have hBlinOn : LinearIndepOn (DiffOp.PseudoDiffOp K) qrow B := hBlin
  let W : Submodule (DiffOp.PseudoDiffOp K) (Fin m → DiffOp.PseudoDiffOp K) :=
    Submodule.span (DiffOp.PseudoDiffOp K) (qrow '' B)
  have hyrow : ∀ i : Fin n, qrow (y i) ∈ W := by
    intro i
    letI : Fintype (Set.insert (y i) B) := (hBfin.insert (y i)).fintype
    apply hBlinOn.mem_span_iff.mpr
    intro hinsert
    have hdiffInsert : DiffIndepOn C (Set.insert (y i) B) := by
      have h :=
        (differentialIndependent_iff_linearIndependent_localizedVariationalOre
          b (fun z : Set.insert (y i) B => (z : K))).mpr hinsert
      change DifferentialIndependent C (fun z : Set.insert (y i) B => (z : K))
      simpa [qrow, qD, N] using h
    have hMind : M.Indep (Set.insert (y i) B) := by
      change (differentialMatroid C K).Indep (Set.insert (y i) B)
      exact differentialMatroid_indep_iff.mpr hdiffInsert
    exact hB.mem_of_insert_indep (Set.mem_range_self i) hMind
  have hallle : Submodule.span (DiffOp.PseudoDiffOp K)
      (Set.range fun i => qrow (y i)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hyrow i
  have hspanAll : Submodule.span (DiffOp.PseudoDiffOp K)
      (Set.range fun i => qrow (y i)) = ⊤ := by
    simpa [qrow, qD, N] using
      span_localizedVariationalOreCoordinateRow_eq_top hy b
  have hspanB : Submodule.span (DiffOp.PseudoDiffOp K)
      (Set.range fun z : B => qrow z) = ⊤ := by
    have hrange : Set.range (fun z : B => qrow z) = qrow '' B := by
      ext v
      simp
    rw [hrange]
    apply le_antisymm le_top
    rw [← hspanAll]
    exact hallle
  let bQ : Module.Basis B (DiffOp.PseudoDiffOp K)
      (Fin m → DiffOp.PseudoDiffOp K) :=
    Module.Basis.mk hBlin (by rw [hspanB])
  have hfinrank := Module.finrank_eq_card_basis bQ
  rw [Module.finrank_fin_fun] at hfinrank
  have hSclosure : M.closure S = M.E := by
    change (differentialMatroid C K).closure S = (differentialMatroid C K).E
    rw [differentialMatroid_ground]
    apply Set.eq_univ_of_forall
    intro x
    rw [differentialMatroid_mem_closure_iff_differentialAlgebraicOver_differentialAdjoin]
    let L := differentialAdjoin C S
    have hx : x ∈ L := by
      change x ∈ differentialAdjoin C (Set.range y)
      rw [hy]
      exact Set.mem_univ x
    let xL : L := ⟨x, hx⟩
    unfold DifferentialAlgebraicOver
    intro hdiff
    have htrans : Transcendental L x :=
      hdiff.algebraicIndependent.transcendental Unit.unit
    apply htrans
    simpa [xL] using (isAlgebraic_algebraMap (R := L) (A := K) xL)
  have hBase : M.IsBase B :=
    M.isBase_iff_indep_closure_eq.mpr
      ⟨hB.indep, hB.closure_eq_closure.trans hSclosure⟩
  have hcardB : Cardinal.mk B =
      constantBaseDifferentialTranscendenceDegree C K := by
    simpa [M, constantBaseDifferentialTranscendenceDegree,
      differentialTranscendenceDegree] using hBase.cardinalMk_eq_cRank
  letI : Module.Free (DiffOp K) (VariationalOreModule C K) :=
    variationalOreModule_free hy
  letI : Module.Finite (DiffOp K) (VariationalOreModule C K) :=
    variationalOreModule_finite hy
  calc
    Module.rank (DiffOp K) (VariationalOreModule C K) =
        (Module.finrank (DiffOp K) (VariationalOreModule C K) : Cardinal) :=
      (Module.finrank_eq_rank (DiffOp K) (VariationalOreModule C K)).symm
    _ = (m : Cardinal) := by simp [Module.finrank_eq_card_basis b]
    _ = (Fintype.card B : Cardinal) := by rw [hfinrank]
    _ = Cardinal.mk B := (Cardinal.mk_fintype B).symm
    _ = constantBaseDifferentialTranscendenceDegree C K := hcardB

end

end GaloisForLFunctions.HTGeometry
