import GaloisForLFunctions.RHTower.SelbergMaassTraceBaseChange

/-!
# Double-coset decomposition of finite Maass trace

The finite trace over `H / (G ∩ H)` decomposes along the orbits of any
intermediate subgroup `J ≤ H`.  Orbit representatives are double-coset terms;
the second finite sum is over the stabilizer quotient.  This is the exact
orbit--stabilizer combinatorics required for a Mackey product calculation.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

@[implicit_reducible]
private noncomputable def maassTraceDoubleCosetSigmaFintype
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H) :
    Fintype (Σ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
      J ⧸ MulAction.stabilizer J q.out) := by
  letI := Fintype.ofFinite (H ⧸ (G.subgroupOf H))
  exact Fintype.ofEquiv (H ⧸ (G.subgroupOf H))
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer J
      (H ⧸ (G.subgroupOf H)))

/-- A stabilizer of an actual relative coset has finite index in the acting
subgroup because its orbit lies in the finite relative-coset quotient. -/
theorem maassTrace_stabilizer_finiteIndex_at
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (x : H ⧸ (G.subgroupOf H)) :
    (MulAction.stabilizer J x).FiniteIndex := by
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  letI : Fintype (H ⧸ (G.subgroupOf H)) := Fintype.ofFinite _
  exact Finite.of_equiv (MulAction.orbit J x)
    (MulAction.orbitEquivQuotientStabilizer J x)

/-- The subgroup inclusion identifies the stabilizer quotient with the quotient
of its image inside the mapped acting subgroup. -/
noncomputable def maassTrace_mappedStabilizerQuotientEquiv
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H)
    (x : H ⧸ (G.subgroupOf H)) :
    J ⧸ MulAction.stabilizer J x ≃
      (J.map H.subtype) ⧸
        ((MulAction.stabilizer J x).map (H.subtype.comp J.subtype)).subgroupOf
          (J.map H.subtype) := by
  let S : Subgroup J := MulAction.stabilizer J x
  let φ : J →* GL (Fin 2) ℝ := H.subtype.comp J.subtype
  let K : Subgroup (GL (Fin 2) ℝ) := S.map φ
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  let ψ : J →* T :=
    { toFun := fun j => ⟨φ j, ⟨j.val, j.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        change φ 1 = 1
        exact map_one φ
      map_mul' := by
        intro a b
        apply Subtype.ext
        change φ (a * b) = φ a * φ b
        exact map_mul φ a b }
  let mapQuotient : J ⧸ S → T ⧸ K.subgroupOf T :=
    Quotient.map' ψ (by
      intro a b hab
      rw [QuotientGroup.leftRel_eq] at hab ⊢
      change (ψ a)⁻¹ * ψ b ∈ K.subgroupOf T
      change φ (a⁻¹ * b) ∈ K
      exact Subgroup.mem_map_of_mem φ hab)
  apply Equiv.ofBijective mapQuotient
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h a =>
      induction b using Quotient.inductionOn with
      | h b =>
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_eq]
        rw [show mapQuotient = Quotient.map' ψ _ by rfl] at hab
        have hmap :
            (QuotientGroup.mk (s := K.subgroupOf T) (ψ a) : T ⧸ K.subgroupOf T) =
              QuotientGroup.mk (s := K.subgroupOf T) (ψ b) := by
          simpa only [Quotient.map'_mk''] using hab
        rw [QuotientGroup.eq] at hmap
        change φ (a⁻¹ * b) ∈ K at hmap
        rcases hmap with ⟨s, hs, hsEq⟩
        have hφ : Function.Injective φ := by
          intro u v huv
          apply Subtype.ext
          apply Subtype.ext
          exact huv
        have hsab : s = a⁻¹ * b := hφ hsEq
        change a⁻¹ * b ∈ S
        exact hsab ▸ hs
  · intro y
    induction y using Quotient.inductionOn with
    | h t =>
      rcases t.2 with ⟨j, hj, hjEq⟩
      let j' : J := ⟨j, hj⟩
      have hψ : ψ j' = t := by
        apply Subtype.ext
        exact hjEq
      refine ⟨QuotientGroup.mk j', ?_⟩
      rw [show mapQuotient = Quotient.map' ψ _ by rfl,
        Quotient.map'_mk'', hψ]

/-- Mapping the finite-index stabilizer along its faithful subgroup inclusion
preserves finite relative index in the mapped acting subgroup. -/
theorem maassTrace_mapped_stabilizer_isFiniteRelIndex_at
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (x : H ⧸ (G.subgroupOf H)) :
    ((MulAction.stabilizer J x).map (H.subtype.comp J.subtype)).IsFiniteRelIndex
      (J.map H.subtype) := by
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  letI : (MulAction.stabilizer J x).FiniteIndex :=
    maassTrace_stabilizer_finiteIndex_at G H J x
  exact Finite.of_equiv (J ⧸ MulAction.stabilizer J x)
    (maassTrace_mappedStabilizerQuotientEquiv J x)

@[implicit_reducible]
noncomputable def maassTraceDoubleCosetOrbitFintype
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H) :
    Fintype (Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) := by
  letI := maassTraceDoubleCosetSigmaFintype G H J
  exact Fintype.ofInjective
    (fun q => (⟨q, QuotientGroup.mk 1⟩ :
      Σ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
        J ⧸ MulAction.stabilizer J q.out)) (by
      intro q q' h
      exact congrArg Sigma.fst h)

/-- The finite stabilizer quotient supplied by the finite ambient trace quotient. -/
@[implicit_reducible]
noncomputable def maassTraceDoubleCosetStabilizerFintype
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :
    Fintype (J ⧸ MulAction.stabilizer J q.out) := by
  letI := maassTraceDoubleCosetSigmaFintype G H J
  exact Fintype.ofInjective
    (fun r => (⟨q, r⟩ :
      Σ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
        J ⧸ MulAction.stabilizer J q.out)) (by
      intro r r' h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- The trace summand on the orbit of `x`, descended from the acting
subgroup to its stabilizer-coset quotient. -/
def maassTraceOrbitSummand
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H)
    (f : glUpperHalfPlaneInvariantFunctions G) (x : H ⧸ (G.subgroupOf H))
    (q : J ⧸ MulAction.stabilizer J x) (z : ℍ) : ℂ :=
  q.liftOn (fun j => maassTraceQuotientFunc f (j • x) z) (by
    intro j k hjk
    change (QuotientGroup.leftRel (MulAction.stabilizer J x)) j k at hjk
    rw [QuotientGroup.leftRel_apply] at hjk
    have hstab : (j⁻¹ * k) • x = x := (MulAction.mem_stabilizer_iff).mp hjk
    have hact : k • x = j • x := by
      calc
        k • x = (j * (j⁻¹ * k)) • x := by
          congr 1
          group
        _ = j • ((j⁻¹ * k) • x) := by rw [mul_smul]
        _ = j • x := by rw [hstab]
    exact congrArg (fun y => maassTraceQuotientFunc f y z) hact.symm)

/-- Evaluation of the descended orbit summand at a literal acting-group
representative. -/
@[simp] theorem maassTraceOrbitSummand_mk
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H)
    (f : glUpperHalfPlaneInvariantFunctions G) (x : H ⧸ (G.subgroupOf H))
    (j : J) (z : ℍ) :
    maassTraceOrbitSummand J f x (QuotientGroup.mk j) z =
      maassTraceQuotientFunc f (j • x) z :=
  rfl

/-- The mapped-stabilizer quotient equivalence sends a literal acting-group
representative to its literal image in the mapped acting subgroup. -/
@[simp] theorem maassTrace_mappedStabilizerQuotientEquiv_mk
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H)
    (x : H ⧸ (G.subgroupOf H)) (j : J) :
    maassTrace_mappedStabilizerQuotientEquiv J x
      (QuotientGroup.mk j) =
        QuotientGroup.mk (s :=
          ((MulAction.stabilizer J x).map (H.subtype.comp J.subtype)).subgroupOf
            (J.map H.subtype))
          ⟨H.subtype j, ⟨j.val, j.2, rfl⟩⟩ :=
  rfl

/-- The stabilizer of a literal relative coset is the corresponding conjugate
intersection condition. -/
theorem maassTrace_mem_stabilizer_iff
    (Γ H : Subgroup (GL (Fin 2) ℝ)) (J : Subgroup H)
    (r : H) (j : J) :
    j ∈ MulAction.stabilizer J
        (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H)) ↔
      r.val⁻¹ * j.val.val * r.val ∈ Γ := by
  rw [MulAction.mem_stabilizer_iff]
  change QuotientGroup.mk (j.val * r) = QuotientGroup.mk r ↔ _
  rw [QuotientGroup.eq]
  change (j.val * r).val⁻¹ * r.val ∈ Γ ↔ _
  constructor
  · intro h
    have hi := Γ.inv_mem h
    simpa [mul_assoc] using hi
  · intro h
    have hi := Γ.inv_mem h
    simpa [mul_assoc] using hi

/-- The stabilizer subgroup itself is the pullback of the conjugated source
subgroup along the inclusion of the acting subgroup. -/
theorem maassTrace_stabilizer_eq_conjugateComap
    (Γ H : Subgroup (GL (Fin 2) ℝ)) (J : Subgroup H)
    (r : H) :
    MulAction.stabilizer J
        (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H)) =
      (ConjAct.toConjAct r.val • Γ).comap (H.subtype.comp J.subtype) := by
  ext j
  rw [maassTrace_mem_stabilizer_iff]
  change r.val⁻¹ * j.val.val * r.val ∈ Γ ↔
    j.val.val ∈ ConjAct.toConjAct r.val • Γ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/-- Every stabilizer intersection in the double-coset decomposition retains
positive rational lifts from its ambient target. -/
theorem maassTrace_stabilizer_hasPositiveRationalLifts
    {Γ H : Subgroup (GL (Fin 2) ℝ)} (hH : HasPositiveRationalLifts H)
    (J : Subgroup H) (r : H) :
    HasPositiveRationalLifts
      ((MulAction.stabilizer J
        (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
          (H.subtype.comp J.subtype)) := by
  intro γ
  rcases γ.2 with ⟨j, hj, hjEq⟩
  obtain ⟨a, ha, hapos⟩ := hH j.val
  refine ⟨a, ?_, hapos⟩
  change a.map (algebraMap ℚ ℝ) = γ.val
  rw [ha]
  exact hjEq

/-- The pullback attached to a double-coset representative is invariant under
the corresponding stabilizer intersection. -/
def maassDoubleCosetBlockPullback
    (Γ H : Subgroup (GL (Fin 2) ℝ)) (J : Subgroup H)
    (r : H) (f : glUpperHalfPlaneInvariantFunctions Γ) :
    glUpperHalfPlaneInvariantFunctions
      ((MulAction.stabilizer J
        (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
          (H.subtype.comp J.subtype)) :=
  ⟨fun z => f.1 (r.val⁻¹ • z), by
    intro γ z
    rcases γ.2 with ⟨j, hj, hjEq⟩
    have hj' : r.val⁻¹ * j.val.val * r.val ∈ Γ :=
      (maassTrace_mem_stabilizer_iff Γ H J r j).mp hj
    change f.1 (r.val⁻¹ • (γ.val • z)) = f.1 (r.val⁻¹ • z)
    rw [← hjEq]
    rw [← mul_smul]
    change f.1 ((r.val⁻¹ * j.val.val) • z) = f.1 (r.val⁻¹ • z)
    have hmul : r.val⁻¹ * j.val.val =
        (r.val⁻¹ * j.val.val * r.val) * r.val⁻¹ := by
      group
    rw [hmul, mul_smul]
    exact f.2 ⟨r.val⁻¹ * j.val.val * r.val, hj'⟩ _⟩

/-- A double-coset block has the source Maass eigenvalue when the ambient
target has positive rational lifts. -/
theorem maassDoubleCosetBlockPullback_eigen
    {Γ H : Subgroup (GL (Fin 2) ℝ)} (hH : HasPositiveRationalLifts H)
    (J : Subgroup H) (r : H) (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions Γ) (hf : IsMaassEigenfunction lam f.1) :
    IsMaassEigenfunction lam (maassDoubleCosetBlockPullback Γ H J r f).1 := by
  obtain ⟨a, ha, hapos⟩ := hH r⁻¹
  change IsMaassEigenfunction lam (fun z => f.1 ((r⁻¹).val • z))
  rw [← ha]
  exact SelbergMaassCuspTransport.eigenfunction_pullback_gl
    (a.map (algebraMap ℚ ℝ)) hapos lam f.1 hf

/-- A double-coset block decays at every integral cusp when the ambient target
has positive rational lifts. -/
theorem maassDoubleCosetBlockPullback_cuspidal
    {Γ H : Subgroup (GL (Fin 2) ℝ)} (hH : HasPositiveRationalLifts H)
    (J : Subgroup H) (r : H)
    (f : glUpperHalfPlaneInvariantFunctions Γ) (hf : IsCuspidalAtIntegralCusps f.1) :
    IsCuspidalAtIntegralCusps (maassDoubleCosetBlockPullback Γ H J r f).1 := by
  obtain ⟨a, ha, hapos⟩ := hH r⁻¹
  change IsCuspidalAtIntegralCusps (fun z => f.1 ((r⁻¹).val • z))
  rw [← ha]
  exact rationalGL_cuspidal_pullback a f.1 hf

/-- Exact invariant, eigenfunction, and cusp data for a double-coset block. -/
def maassDoubleCosetBlockPullbackData_of_data
    {Γ H : Subgroup (GL (Fin 2) ℝ)} (hH : HasPositiveRationalLifts H)
    (J : Subgroup H) (r : H) (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions Γ)
    (heigen : IsMaassEigenfunction lam f.1)
    (hcusp : IsCuspidalAtIntegralCusps f.1) :
    {F : glUpperHalfPlaneInvariantFunctions
      ((MulAction.stabilizer J
        (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
          (H.subtype.comp J.subtype)) //
      IsMaassEigenfunction lam F.1 ∧ IsCuspidalAtIntegralCusps F.1} :=
  ⟨maassDoubleCosetBlockPullback Γ H J r f,
    ⟨maassDoubleCosetBlockPullback_eigen hH J r lam f heigen,
      maassDoubleCosetBlockPullback_cuspidal hH J r f hcusp⟩⟩

/-- Tracing a double-coset block to the mapped acting subgroup preserves its
invariance, Maass eigenvalue, and integral-cusp decay. -/
def maassDoubleCosetBlockTraceData_of_data
    {Γ H : Subgroup (GL (Fin 2) ℝ)} [Γ.IsFiniteRelIndex H]
    (hH : HasPositiveRationalLifts H) (J : Subgroup H) (r : H) (lam : ℝ)
    (f : glUpperHalfPlaneInvariantFunctions Γ)
    (heigen : IsMaassEigenfunction lam f.1)
    (hcusp : IsCuspidalAtIntegralCusps f.1) :
    {F : glUpperHalfPlaneInvariantFunctions (J.map H.subtype) //
      IsMaassEigenfunction lam F.1 ∧ IsCuspidalAtIntegralCusps F.1} := by
  letI : ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
        (H.subtype.comp J.subtype)).IsFiniteRelIndex (J.map H.subtype) :=
    maassTrace_mapped_stabilizer_isFiniteRelIndex_at Γ H J (QuotientGroup.mk r)
  exact positiveRationalMaassTraceData_of_data (hH.map_subgroup J) lam
    (maassDoubleCosetBlockPullback Γ H J r f)
    (maassDoubleCosetBlockPullback_eigen hH J r lam f heigen)
    (maassDoubleCosetBlockPullback_cuspidal hH J r f hcusp)

/-- The finite trace of one double-coset block is exactly the sum of the
original trace summands across its stabilizer-coset orbit. -/
theorem maassDoubleCosetBlockTraceFunction_eq_sum
    {Γ H : Subgroup (GL (Fin 2) ℝ)} [Γ.IsFiniteRelIndex H]
    (J : Subgroup H) (r : H) (f : glUpperHalfPlaneInvariantFunctions Γ) (z : ℍ) :
    letI : (MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).FiniteIndex :=
        maassTrace_stabilizer_finiteIndex_at Γ H J (QuotientGroup.mk r)
    letI : Fintype (J ⧸ MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))) := Fintype.ofFinite _
    letI : ((MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))).map
        (H.subtype.comp J.subtype)).IsFiniteRelIndex (J.map H.subtype) :=
      maassTrace_mapped_stabilizer_isFiniteRelIndex_at Γ H J (QuotientGroup.mk r)
    maassTraceFunction (H := J.map H.subtype)
      (maassDoubleCosetBlockPullback Γ H J r f) z =
      ∑ j : J ⧸ MulAction.stabilizer J
        (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H)),
        maassTraceOrbitSummand J f (QuotientGroup.mk r) j z := by
  let S : Subgroup J := MulAction.stabilizer J (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))
  let K : Subgroup (GL (Fin 2) ℝ) := S.map (H.subtype.comp J.subtype)
  let T : Subgroup (GL (Fin 2) ℝ) := J.map H.subtype
  letI : S.FiniteIndex := maassTrace_stabilizer_finiteIndex_at Γ H J (QuotientGroup.mk r)
  letI : K.IsFiniteRelIndex T :=
    maassTrace_mapped_stabilizer_isFiniteRelIndex_at Γ H J (QuotientGroup.mk r)
  letI : Fintype (J ⧸ S) := Fintype.ofFinite _
  letI : Fintype (T ⧸ K.subgroupOf T) := Fintype.ofFinite _
  let e := maassTrace_mappedStabilizerQuotientEquiv J
    (QuotientGroup.mk r : H ⧸ (Γ.subgroupOf H))
  unfold maassTraceFunction
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro q hq
  induction q using Quotient.inductionOn with
  | h j =>
    rw [maassTrace_mappedStabilizerQuotientEquiv_mk]
    simp only [maassTraceQuotientFunc_mk, maassTraceOrbitSummand_mk]
    change f.1 (r.val⁻¹ • ((j.val.val)⁻¹ • z)) =
      f.1 ((j.val * r).val⁻¹ • z)
    rw [← mul_smul]
    congr 2

/-- Finite Maass trace reindexed first by relative double cosets and then by
the corresponding stabilizer quotients. -/
theorem maassTraceFunction_doubleCoset
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (f : glUpperHalfPlaneInvariantFunctions G) (z : ℍ) :
    let Ω := Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))
    letI : Fintype Ω := maassTraceDoubleCosetOrbitFintype G H J
    letI (q : Ω) : Fintype (J ⧸ MulAction.stabilizer J q.out) :=
      maassTraceDoubleCosetStabilizerFintype G H J q
    maassTraceFunction (H := H) f z =
      ∑ q, ∑ r, maassTraceQuotientFunc f
        ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer J
          (H ⧸ (G.subgroupOf H))).symm ⟨q, r⟩) z := by
  dsimp only
  letI : Fintype (H ⧸ (G.subgroupOf H)) := Fintype.ofFinite _
  letI : Fintype (Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :=
    maassTraceDoubleCosetOrbitFintype G H J
  letI (q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H)))) :
      Fintype (J ⧸ MulAction.stabilizer J q.out) :=
    maassTraceDoubleCosetStabilizerFintype G H J q
  unfold maassTraceFunction
  let e := MulAction.selfEquivSigmaOrbitsQuotientStabilizer J
    (H ⧸ (G.subgroupOf H))
  calc
    ∑ q, maassTraceQuotientFunc f q z =
        ∑ p, maassTraceQuotientFunc f (e.symm p) z :=
      (e.symm.sum_comp (fun q => maassTraceQuotientFunc f q z)).symm
    _ = ∑ q, ∑ r, maassTraceQuotientFunc f (e.symm ⟨q, r⟩) z :=
      Fintype.sum_sigma _

end

end GaloisForLFunctions.RHTower
