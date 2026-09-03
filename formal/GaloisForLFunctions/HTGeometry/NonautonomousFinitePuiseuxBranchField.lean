import GaloisForLFunctions.HTGeometry.NonautonomousRamifiedPuiseuxCascadeActual

/-!
# Finite actual branch field for nonautonomous cascades

The full relative algebraic closure used by the first Puiseux-selection interface is too large for
one finitely ramified integer-valued Hahn field.  The actual differential law only needs finitely
many derivative branches.  This module adjoins exactly those branches to the actual state field.

The resulting extension is finite, contains the rational clock, embeds in the meromorphic field,
and is preserved by ordinary differentiation.  The closure proof is not assumed: differentiating
each algebraic generator's minimal equation expresses its derivative inside the same finite adjoin.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Algebraic generators add no derivative escape once derivatives of the base land in their
generated field. -/
theorem derivation_mem_adjoin_range_of_isAlgebraic
    {C M ι : Type*} [Field C] [Field M] [Algebra C M] [CharZero M]
    (D : Derivation C M M) (E : IntermediateField C M) (b : ι → M)
    (hb : ∀ i, IsAlgebraic E (b i))
    (hE : ∀ e : E, D (e : M) ∈ IntermediateField.adjoin E (Set.range b))
    {y : M} (hy : y ∈ IntermediateField.adjoin E (Set.range b)) :
    D y ∈ IntermediateField.adjoin E (Set.range b) := by
  classical
  let B := IntermediateField.adjoin E (Set.range b)
  letI : Differential M := ⟨toIntDerivation D⟩
  have hDb : ∀ j, D (b j) ∈ B := by
    intro j
    have hjalg : IsAlgebraic E (b j) := hb j
    have hjint : IsIntegral E (b j) := hjalg.isIntegral
    set p : Polynomial E := minpoly E (b j) with hp
    have hp0 : p ≠ 0 := minpoly.ne_zero hjint
    have hpdeg : 0 < p.natDegree := minpoly.natDegree_pos hjint
    set P : Polynomial M := p.map (algebraMap E M) with hP
    have hPeval : Polynomial.eval (b j) P = 0 := by
      rw [hP, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact minpoly.aeval E (b j)
    have hdp0 : Polynomial.derivative p ≠ 0 := by
      intro hcon
      have := Polynomial.derivative_eq_zero.mp hcon
      omega
    have hBne : Polynomial.eval (b j) (Polynomial.derivative P) ≠ 0 := by
      rw [hP, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]
      intro hcon
      have hle := minpoly.degree_le_of_ne_zero E (b j) hdp0 hcon
      have hlt := Polynomial.degree_derivative_lt hp0
      rw [← hp] at hle
      exact absurd hle (not_le.mpr hlt)
    have hjB : b j ∈ B :=
      IntermediateField.subset_adjoin E (Set.range b) (Set.mem_range_self j)
    have hAmem : Polynomial.eval (b j) (coeffDeriv P) ∈ B := by
      refine eval_mem_of_coeff_mem B (fun i => ?_) hjB
      rw [coeffDeriv_coeff, hP, Polynomial.coeff_map]
      exact hE (p.coeff i)
    have hBmem : Polynomial.eval (b j) (Polynomial.derivative P) ∈ B := by
      refine eval_mem_of_coeff_mem B (fun i => ?_) hjB
      rw [hP, Polynomial.derivative_map, Polynomial.coeff_map]
      exact IntermediateField.algebraMap_mem B _
    have hchain := deriv_eval P (b j)
    rw [hPeval, map_zero] at hchain
    change 0 = Polynomial.eval (b j) (coeffDeriv P) +
      Polynomial.eval (b j) (Polynomial.derivative P) * D (b j) at hchain
    have hsolve : D (b j) = -Polynomial.eval (b j) (coeffDeriv P) /
        Polynomial.eval (b j) (Polynomial.derivative P) := by
      rw [eq_div_iff hBne]
      linear_combination -hchain
    rw [hsolve]
    exact B.div_mem (B.neg_mem hAmem) hBmem
  exact (derivationInt_mem_of_mem_adjoin (C := E) (L := M) (toIntDerivation D)
    (M := B) (fun e => hE e) (fun x hx => by
      rcases hx with ⟨j, rfl⟩
      exact ⟨IntermediateField.subset_adjoin E (Set.range b) (Set.mem_range_self j),
        hDb j⟩) hy).2

open GaloisForLFunctions Bottcher
open scoped Differential

local instance finiteBranchDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

noncomputable local instance finiteBranchRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

noncomputable local instance finiteBranchComplexAlgebra :
    Algebra ℂ (meroField (Set.univ : Set ℂ)) :=
  ((ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra

local instance finiteBranchScalarTower :
    IsScalarTower ℂ (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable local instance finiteBranchDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

local instance finiteBranchCharZero : CharZero (meroField (Set.univ : Set ℂ)) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective

private theorem finiteBranch_deriv_complexConst (c : ℂ) :
    (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ = 0 := by
  change (algebraMap (RatFunc ℂ) (meroField Set.univ)
    (algebraMap ℂ (RatFunc ℂ) c))′ = 0
  change (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ (algebraMap ℂ (RatFunc ℂ) c))′ = 0
  rw [meroField_deriv_ratfuncToMero]
  have hzero : ratFuncCoordinateDerivation ℂ (algebraMap ℂ (RatFunc ℂ) c) = 0 :=
    (ratFuncCoordinateDerivation_eq_zero_iff
      (algebraMap ℂ (RatFunc ℂ) c)).mpr ⟨c, rfl⟩
  rw [hzero, map_zero]

private theorem finiteBranch_deriv_smul (c : ℂ)
    (x : meroField (Set.univ : Set ℂ)) : (c • x)′ = c • x′ := by
  rw [Algebra.smul_def c x, differential_deriv_mul,
    finiteBranch_deriv_complexConst, zero_mul, zero_add, Algebra.smul_def]

private theorem finiteBranch_deriv_one :
    (1 : meroField (Set.univ : Set ℂ))′ = 0 := by
  have h := finiteBranch_deriv_complexConst (1 : ℂ)
  rwa [map_one] at h

private theorem finiteBranch_deriv_leibniz
    (a b : meroField (Set.univ : Set ℂ)) : (a * b)′ = a • b′ + b • a′ := by
  rw [differential_deriv_mul]
  simp only [smul_eq_mul]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
private noncomputable def finiteBranchMeroComplexDerivation :
    Derivation ℂ (meroField (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) where
  toLinearMap :=
    { toAddHom := { toFun := fun x => x′, map_add' := fun x y => map_add _ x y }
      map_smul' := finiteBranch_deriv_smul }
  map_one_eq_zero' := finiteBranch_deriv_one
  leibniz' := finiteBranch_deriv_leibniz

@[simp] private theorem finiteBranchMeroComplexDerivation_apply
    (x : meroField (Set.univ : Set ℂ)) : finiteBranchMeroComplexDerivation x = x′ := rfl

/-- Finite field obtained by adjoining only actual cascade derivative branches to state field. -/
abbrev NonautonomousFiniteCascadeBranchFieldOverState
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (N : ℕ) :=
  IntermediateField.adjoin (NonautonomousRamifiedCascadeStateField hfan N)
    (Set.range (fun i : Fin (N + 1) => cascadeMeroDeriv hfan i))

/-- Same finite branch field, regarded over complex constants. -/
abbrev NonautonomousFiniteCascadeBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) (N : ℕ) :=
  (NonautonomousFiniteCascadeBranchFieldOverState hfan N).restrictScalars ℂ

/-- Rational clock field maps canonically into finite actual branch field. -/
noncomputable def nonautonomousFiniteRatFuncToBranch
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : RatFunc ℂ →+* NonautonomousFiniteCascadeBranchField hfan N :=
  (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).codRestrict
    (NonautonomousFiniteCascadeBranchField hfan N) (fun q => by
      change algebraMap (RatFunc ℂ) (meroField Set.univ) q ∈
        NonautonomousFiniteCascadeBranchFieldOverState hfan N
      have hle : IntermediateField.adjoin ℂ {cascadeMero hfan 0} ≤
          NonautonomousRamifiedCascadeStateField hfan N := by
        rw [IntermediateField.adjoin_le_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact IntermediateField.subset_adjoin ℂ _
          (Set.mem_range_self (⟨0, by omega⟩ : Fin (N + 1)))
      let e : NonautonomousRamifiedCascadeStateField hfan N :=
        ⟨algebraMap (RatFunc ℂ) (meroField Set.univ) q,
          hle (algebraMap_ratFunc_mem_adjoin_cascadeMero_zero hfan q)⟩
      change algebraMap (NonautonomousRamifiedCascadeStateField hfan N)
        (meroField Set.univ) e ∈ NonautonomousFiniteCascadeBranchFieldOverState hfan N
      exact IntermediateField.algebraMap_mem
        (NonautonomousFiniteCascadeBranchFieldOverState hfan N) e)

/-- Canonical rational-clock algebra on finite actual branch field. -/
noncomputable instance nonautonomousFiniteBranchRatFuncAlgebra
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : Algebra (RatFunc ℂ) (NonautonomousFiniteCascadeBranchField hfan N) :=
  (nonautonomousFiniteRatFuncToBranch hfan N).toAlgebra

noncomputable instance nonautonomousFiniteBranchScalarTower
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : IsScalarTower ℂ (RatFunc ℂ)
      (NonautonomousFiniteCascadeBranchField hfan N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable instance nonautonomousFiniteBranchAmbientScalarTower
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : IsScalarTower (RatFunc ℂ)
      (NonautonomousFiniteCascadeBranchField hfan N)
      (meroField (Set.univ : Set ℂ)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Inclusion of finite actual branch field into meromorphic field over rational clock. -/
noncomputable def nonautonomousFiniteBranchEmbedding
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) : NonautonomousFiniteCascadeBranchField hfan N →ₐ[RatFunc ℂ]
      meroField (Set.univ : Set ℂ) :=
  IsScalarTower.toAlgHom (RatFunc ℂ)
    (NonautonomousFiniteCascadeBranchField hfan N) (meroField Set.univ)

@[simp] theorem nonautonomousFiniteBranchEmbedding_apply
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (y : NonautonomousFiniteCascadeBranchField hfan N) :
    nonautonomousFiniteBranchEmbedding hfan N y =
      (y : meroField (Set.univ : Set ℂ)) := rfl

@[simp] theorem nonautonomousFiniteBranch_algebraMap_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (q : RatFunc ℂ) :
    ((algebraMap (RatFunc ℂ) (NonautonomousFiniteCascadeBranchField hfan N) q :
      NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ) =
        algebraMap (RatFunc ℂ) (meroField Set.univ) q := rfl

/-- Adjoining finitely many actual algebraic branches gives a finite state-field extension. -/
theorem finiteDimensional_nonautonomousFiniteCascadeBranchFieldOverState
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) :
    FiniteDimensional (NonautonomousRamifiedCascadeStateField hfan N)
      (NonautonomousFiniteCascadeBranchFieldOverState hfan N) := by
  let b : Fin (N + 1) → meroField (Set.univ : Set ℂ) := fun i => cascadeMeroDeriv hfan i
  letI : Finite (Set.range b) := Set.finite_range b
  exact IntermediateField.finiteDimensional_adjoin fun y hy => by
    rcases hy with ⟨i, rfl⟩
    exact (mem_algebraicClosure_iff.mp
      (cascadeMeroDeriv_mem_complexCascadeStateField_algebraicClosure hfan hall h1 i)).isIntegral

/-- Every actual state lies in finite branch field. -/
theorem cascadeMero_mem_nonautonomousFiniteCascadeBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) :
    cascadeMero hfan i ∈ NonautonomousFiniteCascadeBranchField hfan N := by
  exact IntermediateField.algebraMap_mem
    (NonautonomousFiniteCascadeBranchFieldOverState hfan N)
    ⟨cascadeMero hfan i,
      IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩

/-- Every actual derivative branch lies in finite branch field by construction. -/
theorem cascadeMeroDeriv_mem_nonautonomousFiniteCascadeBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) :
    cascadeMeroDeriv hfan i ∈ NonautonomousFiniteCascadeBranchField hfan N := by
  change cascadeMeroDeriv hfan i ∈
    NonautonomousFiniteCascadeBranchFieldOverState hfan N
  exact IntermediateField.subset_adjoin
    (NonautonomousRamifiedCascadeStateField hfan N) _ (Set.mem_range_self i)

/-- Actual cascade state as an element of finite branch field. -/
noncomputable def nonautonomousFiniteCascadeStateInBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) : NonautonomousFiniteCascadeBranchField hfan N :=
  ⟨cascadeMero hfan i,
    cascadeMero_mem_nonautonomousFiniteCascadeBranchField hfan N i⟩

/-- Actual derivative branch as an element of finite branch field. -/
noncomputable def nonautonomousFiniteCascadeDerivativeInBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) : NonautonomousFiniteCascadeBranchField hfan N :=
  ⟨cascadeMeroDeriv hfan i,
    cascadeMeroDeriv_mem_nonautonomousFiniteCascadeBranchField hfan N i⟩

@[simp] theorem nonautonomousFiniteCascadeStateInBranchField_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) :
    ((nonautonomousFiniteCascadeStateInBranchField hfan N i :
      NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ) =
        cascadeMero hfan i := rfl

/-- Rational coordinate is the actual clock in finite branch field. -/
theorem nonautonomousFiniteBranch_algebraMap_X
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) :
    algebraMap (RatFunc ℂ) (NonautonomousFiniteCascadeBranchField hfan N) RatFunc.X =
      nonautonomousFiniteCascadeStateInBranchField hfan N
        (⟨0, by omega⟩ : Fin (N + 1)) := by
  apply Subtype.ext
  rw [nonautonomousFiniteBranch_algebraMap_coe,
    nonautonomousFiniteCascadeStateInBranchField_coe, cascadeMero_zero]

@[simp] theorem nonautonomousFiniteCascadeDerivativeInBranchField_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ)
    (N : ℕ) (i : Fin (N + 1)) :
    ((nonautonomousFiniteCascadeDerivativeInBranchField hfan N i :
      NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ) =
        cascadeMeroDeriv hfan i := rfl

/-- Finite branch field is contained in full relative algebraic closure. -/
theorem nonautonomousFiniteCascadeBranchField_le_algebraicClosure
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) :
    NonautonomousFiniteCascadeBranchFieldOverState hfan N ≤
      NonautonomousRamifiedCascadeBranchField hfan N := by
  rw [IntermediateField.adjoin_le_iff]
  rintro y ⟨i, rfl⟩
  exact cascadeMeroDeriv_mem_complexCascadeStateField_algebraicClosure hfan hall h1 i

/-- Ordinary differentiation preserves finite actual branch field; no full closure is needed. -/
theorem deriv_mem_nonautonomousFiniteCascadeBranchField
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ NonautonomousFiniteCascadeBranchField hfan N) :
    y′ ∈ NonautonomousFiniteCascadeBranchField hfan N := by
  let E := NonautonomousRamifiedCascadeStateField hfan N
  let b : Fin (N + 1) → meroField (Set.univ : Set ℂ) := fun i => cascadeMeroDeriv hfan i
  let B := NonautonomousFiniteCascadeBranchFieldOverState hfan N
  have hb : ∀ i, IsAlgebraic E (b i) := fun i =>
    mem_algebraicClosure_iff.mp
      (cascadeMeroDeriv_mem_complexCascadeStateField_algebraicClosure hfan hall h1 i)
  have hE : ∀ e : E, finiteBranchMeroComplexDerivation (e : meroField Set.univ) ∈ B := by
    intro e
    exact (derivationBase_mem_of_mem_adjoin finiteBranchMeroComplexDerivation
      (M := B.restrictScalars ℂ) (fun x hx => by
        rcases hx with ⟨i, rfl⟩
        constructor
        · exact cascadeMero_mem_nonautonomousFiniteCascadeBranchField hfan N i
        · change (cascadeMero hfan i)′ ∈ B.restrictScalars ℂ
          rw [← differentialJet_zero (cascadeMero hfan i),
            ← differentialJet_succ, differentialJet_one_cascadeMero]
          exact cascadeMeroDeriv_mem_nonautonomousFiniteCascadeBranchField hfan N i)
      e.2).2
  exact derivation_mem_adjoin_range_of_isAlgebraic
    finiteBranchMeroComplexDerivation E b hb hE hy

/-- Ordinary derivative restricted to finite actual branch field. -/
noncomputable def nonautonomousFiniteCascadeDerivation
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1) :
    Derivation ℂ (NonautonomousFiniteCascadeBranchField hfan N)
      (NonautonomousFiniteCascadeBranchField hfan N) :=
  restrictDerivation finiteBranchMeroComplexDerivation
    (NonautonomousFiniteCascadeBranchField hfan N)
    (fun _ hy => deriv_mem_nonautonomousFiniteCascadeBranchField hfan hall h1 hy)

@[simp] theorem nonautonomousFiniteCascadeDerivation_coe
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (y : NonautonomousFiniteCascadeBranchField hfan N) :
    ((nonautonomousFiniteCascadeDerivation hfan hall h1 y :
      NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ) =
      ((y : NonautonomousFiniteCascadeBranchField hfan N) : meroField Set.univ)′ := rfl

/-- Restricted derivative sends each actual state to its actual derivative branch. -/
theorem nonautonomousFiniteCascadeDerivation_state
    {f : ℕ → ℂ → ℂ} (hfan : ∀ i : ℕ, AnalyticOnNhd ℂ (f i) Set.univ) {N : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < N → DifferentiallyAlgebraicOfOrder (f k) 1)
    (i : Fin (N + 1)) :
    nonautonomousFiniteCascadeDerivation hfan hall h1
        (nonautonomousFiniteCascadeStateInBranchField hfan N i) =
      nonautonomousFiniteCascadeDerivativeInBranchField hfan N i := by
  apply Subtype.ext
  rw [nonautonomousFiniteCascadeDerivation_coe,
    nonautonomousFiniteCascadeStateInBranchField_coe,
    nonautonomousFiniteCascadeDerivativeInBranchField_coe,
    ← differentialJet_zero (cascadeMero hfan i), ← differentialJet_succ,
    differentialJet_one_cascadeMero]

end

end GaloisForLFunctions.HTGeometry
