import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalSingletEdgeCasimirBridge

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

theorem booleanQubitClifford_mul
    (g h : QubitTwoDesign.BinaryOctahedral) :
    booleanQubitClifford (g * h) =
      booleanQubitClifford g * booleanQubitClifford h := by
  rw [booleanQubitClifford, booleanQubitClifford,
    booleanQubitClifford, QubitTwoDesign.qubitClifford_mul, map_mul]

theorem finiteProductCliffordGate_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (g h : V → QubitTwoDesign.BinaryOctahedral) :
    finiteProductCliffordGate (g * h) =
      finiteProductCliffordGate g * finiteProductCliffordGate h := by
  rw [finiteProductCliffordGate, finiteProductCliffordGate,
    finiteProductCliffordGate, finiteLocalMatrix_mul]
  congr 1
  funext v
  exact booleanQubitClifford_mul (g v) (h v)

theorem finiteProductCliffordDoubledGate_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (g h : V → QubitTwoDesign.BinaryOctahedral) :
    finiteProductCliffordDoubledGate (g * h) =
      finiteProductCliffordDoubledGate g *
        finiteProductCliffordDoubledGate h := by
  rw [finiteProductCliffordDoubledGate,
    finiteProductCliffordDoubledGate,
    finiteProductCliffordDoubledGate,
    finiteProductCliffordGate_mul,
    Matrix.mul_kronecker_mul]

theorem finiteProductCliffordDoubledGate_eq_localMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → QubitTwoDesign.BinaryOctahedral) :
    finiteProductCliffordDoubledGate g =
      finiteTwoReplicaLocalMatrix fun v =>
        booleanCliffordDoubledGate (g v) := by
  ext x y
  change
    (finiteProductCliffordGate g x.1 y.1) *
      (finiteProductCliffordGate g x.2 y.2) =
    ∏ v, booleanCliffordDoubledGate (g v)
      (x.1 v, x.2 v) (y.1 v, y.2 v)
  simp only [finiteProductCliffordGate, finiteLocalMatrix,
    booleanCliffordDoubledGate, cliffordToBooleanTwoReplicaAlgEquiv,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, doubledRep,
    cliffordTwoReplicaIndexEquiv, finTwoEquiv]
  rw [← Finset.prod_mul_distrib]
  rfl

theorem finiteTwoReplicaLocalMatrix_conjTranspose
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    (finiteTwoReplicaLocalMatrix M)ᴴ =
      finiteTwoReplicaLocalMatrix fun v => (M v)ᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, finiteTwoReplicaLocalMatrix]
  rw [← starRingEnd_apply, map_prod]
  rfl

def finiteProductCliffordTwoReplicaTwirlLinear
    {V : Type*} [Fintype V] [DecidableEq V] :
    FiniteTwoReplicaMatrix V →ₗ[ℂ] FiniteTwoReplicaMatrix V where
  toFun X := repTwirl finiteProductCliffordDoubledGate X
  map_add' X Y := by
    simp [repTwirl, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  map_smul' c X := by
    unfold repTwirl
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [← Finset.smul_sum, smul_smul, smul_smul, mul_comm]
    rfl

theorem finiteProductCliffordTwoReplicaTwirl_localMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : V → Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    finiteProductCliffordTwoReplicaTwirlLinear
        (finiteTwoReplicaLocalMatrix M) =
      finiteTwoReplicaLocalMatrix fun v =>
        booleanCliffordTwoReplicaTwirlLinear (M v) := by
  change repTwirl finiteProductCliffordDoubledGate
      (finiteTwoReplicaLocalMatrix M) = _
  rw [repTwirl]
  simp_rw [finiteProductCliffordDoubledGate_eq_localMatrix]
  simp_rw [finiteTwoReplicaLocalMatrix_conjTranspose]
  simp_rw [finiteTwoReplicaLocalMatrix_mul]
  ext x y
  rw [Matrix.smul_apply]
  rw [Matrix.sum_apply]
  change
    (Fintype.card
        (V → QubitTwoDesign.BinaryOctahedral) : ℂ)⁻¹ *
        (∑ g : V → QubitTwoDesign.BinaryOctahedral,
          ∏ v,
            (booleanCliffordDoubledGate (g v) * M v *
              (booleanCliffordDoubledGate (g v))ᴴ)
                (x.1 v, x.2 v) (y.1 v, y.2 v)) =
      ∏ v,
        (Fintype.card QubitTwoDesign.BinaryOctahedral : ℂ)⁻¹ *
          ∑ g : QubitTwoDesign.BinaryOctahedral,
            (booleanCliffordDoubledGate g * M v *
              (booleanCliffordDoubledGate g)ᴴ)
                (x.1 v, x.2 v) (y.1 v, y.2 v)
  rw [Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]
  simp [Finset.prod_const]

theorem exists_booleanCliffordTwirl_coeff
    (M : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) :
    ∃ a b : ℂ,
      booleanCliffordTwoReplicaTwirlLinear M =
        a • (1 : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ) +
          b • twoReplicaSwap := by
  have hmem : booleanCliffordTwoReplicaTwirlLinear M ∈
      Submodule.span ℂ
        ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
          Set TwoReplicaLocalMatrix) := by
    rw [← booleanCliffordTwoReplicaTwirlLinear_range_eq]
    exact ⟨M, rfl⟩
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  exact ⟨a, b, hab.symm⟩

def finiteTwoReplicaSwapProductCoeff
    {V : Type*} [Fintype V]
    (a b : V → ℂ) (x : V → Bool) : ℂ :=
  ∏ v, if x v then b v else a v

theorem finiteTwoReplicaLocalMatrix_linearCombo_eq_embed
    {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V → ℂ) :
    finiteTwoReplicaLocalMatrix (fun v =>
        a v • (1 : TwoReplicaLocalMatrix) +
          b v • twoReplicaSwap) =
      finiteTwoReplicaSwapInvariantEmbed
        (finiteTwoReplicaSwapProductCoeff a b) := by
  change finiteTwoReplicaLocalMatrix (fun v =>
      a v • (1 : TwoReplicaLocalMatrix) + b v • twoReplicaSwap) =
    ∑ choice : V → Bool,
      finiteTwoReplicaSwapProductCoeff a b choice •
        finiteTwoReplicaSwapRaw choice
  ext x y
  simp only [finiteTwoReplicaLocalMatrix, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sum_apply, finiteTwoReplicaSwapRaw,
    finiteTwoReplicaSwapProductCoeff, smul_eq_mul]
  change
    (∏ v,
      (a v * (1 : TwoReplicaLocalMatrix)
          (x.1 v, x.2 v) (y.1 v, y.2 v) +
        b v * twoReplicaSwap
          (x.1 v, x.2 v) (y.1 v, y.2 v))) =
      ∑ choice : V → Bool,
        (∏ v, if choice v then b v else a v) *
          ∏ v, twoReplicaLocalSwapRaw (choice v)
            (x.1 v, x.2 v) (y.1 v, y.2 v)
  let f := fun v (choice : Bool) =>
    (if choice then b v else a v) *
      twoReplicaLocalSwapRaw choice
        (x.1 v, x.2 v) (y.1 v, y.2 v)
  calc
    (∏ v,
      (a v * (1 : TwoReplicaLocalMatrix)
          (x.1 v, x.2 v) (y.1 v, y.2 v) +
        b v * twoReplicaSwap
          (x.1 v, x.2 v) (y.1 v, y.2 v))) =
        ∏ v, ∑ choice : Bool, f v choice := by
          apply Finset.prod_congr rfl
          intro v _hv
          rw [Fintype.sum_bool]
          simp [f, twoReplicaLocalSwapRaw]
          ring
    _ = ∑ choice : V → Bool, ∏ v, f v (choice v) :=
      Fintype.prod_sum f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro choice _hchoice
      rw [Finset.prod_mul_distrib]

def twoReplicaLocalMatrixUnit
    (i j : TwoReplicaLocalIndex) : TwoReplicaLocalMatrix :=
  fun p q => if p = i ∧ q = j then 1 else 0

def finiteTwoReplicaMatrixUnitFactors
    {V : Type*}
    (x y : FiniteTwoReplicaConfiguration V) (v : V) :
    TwoReplicaLocalMatrix :=
  twoReplicaLocalMatrixUnit
    (x.1 v, x.2 v) (y.1 v, y.2 v)

theorem finiteTwoReplicaLocalMatrix_unitFactors_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (x y a b : FiniteTwoReplicaConfiguration V) :
    finiteTwoReplicaLocalMatrix
        (finiteTwoReplicaMatrixUnitFactors x y) a b =
      if a = x ∧ b = y then 1 else 0 := by
  by_cases hax : a = x
  · subst a
    by_cases hby : b = y
    · subst b
      simp [finiteTwoReplicaLocalMatrix,
        finiteTwoReplicaMatrixUnitFactors,
        twoReplicaLocalMatrixUnit]
    · rw [if_neg (by simp [hby])]
      have hlocal :
          finiteTwoReplicaConfigurationEquiv V b ≠
            finiteTwoReplicaConfigurationEquiv V y := by
        intro h
        exact hby ((finiteTwoReplicaConfigurationEquiv V).injective h)
      obtain ⟨v, hv⟩ := Function.ne_iff.mp hlocal
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      change (if (x.1 v, x.2 v) = (x.1 v, x.2 v) ∧
          (b.1 v, b.2 v) = (y.1 v, y.2 v) then 1 else 0) = 0
      rw [if_neg (fun h => hv h.2)]
  · rw [if_neg (by simp [hax])]
    have hlocal :
        finiteTwoReplicaConfigurationEquiv V a ≠
          finiteTwoReplicaConfigurationEquiv V x := by
      intro h
      exact hax ((finiteTwoReplicaConfigurationEquiv V).injective h)
    obtain ⟨v, hv⟩ := Function.ne_iff.mp hlocal
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    change (if (a.1 v, a.2 v) = (x.1 v, x.2 v) ∧
        (b.1 v, b.2 v) = (y.1 v, y.2 v) then 1 else 0) = 0
    rw [if_neg (fun h => hv h.1)]

theorem finiteTwoReplicaMatrix_eq_sum_localUnits
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : FiniteTwoReplicaMatrix V) :
    X = ∑ x : FiniteTwoReplicaConfiguration V,
      ∑ y : FiniteTwoReplicaConfiguration V,
        X x y • finiteTwoReplicaLocalMatrix
          (finiteTwoReplicaMatrixUnitFactors x y) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    finiteTwoReplicaLocalMatrix_unitFactors_apply]
  symm
  rw [Fintype.sum_eq_single a]
  · rw [Fintype.sum_eq_single b]
    · simp
    · intro y hne
      have hby : b ≠ y := fun h => hne h.symm
      simp [hby]
  · intro x hne
    have hax : a ≠ x := fun h => hne h.symm
    simp [hax]

theorem finiteProductCliffordTwoReplicaTwirl_localMatrix_mem_range
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : V → TwoReplicaLocalMatrix) :
    finiteProductCliffordTwoReplicaTwirlLinear
        (finiteTwoReplicaLocalMatrix M) ∈
      LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) := by
  choose a b hab using fun v => exists_booleanCliffordTwirl_coeff (M v)
  refine ⟨finiteTwoReplicaSwapProductCoeff a b, ?_⟩
  rw [← finiteTwoReplicaLocalMatrix_linearCombo_eq_embed]
  rw [finiteProductCliffordTwoReplicaTwirl_localMatrix]
  congr 1
  funext v
  exact (hab v).symm

theorem finiteProductCliffordTwoReplicaTwirl_range_le
    {V : Type*} [Fintype V] [DecidableEq V] :
    LinearMap.range
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) ≤
      LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) := by
  rintro Y ⟨X, rfl⟩
  rw [finiteTwoReplicaMatrix_eq_sum_localUnits X]
  rw [map_sum]
  apply Submodule.sum_mem
  intro x _hx
  rw [map_sum]
  apply Submodule.sum_mem
  intro y _hy
  rw [map_smul]
  exact Submodule.smul_mem _ _
    (finiteProductCliffordTwoReplicaTwirl_localMatrix_mem_range
      (finiteTwoReplicaMatrixUnitFactors x y))

theorem booleanCliffordTwoReplicaTwirl_localSwapRaw
    (choice : Bool) :
    booleanCliffordTwoReplicaTwirlLinear
        (twoReplicaLocalSwapRaw choice) =
      twoReplicaLocalSwapRaw choice := by
  cases choice
  · exact booleanCliffordTwoReplica_twirl_eq_self_of_commute 1 (by simp)
  · exact booleanCliffordTwoReplica_twirl_eq_self_of_commute
      twoReplicaSwap booleanCliffordDoubledGate_commute_twoReplicaSwap

theorem finiteProductCliffordTwoReplicaTwirl_swapRaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (choice : V → Bool) :
    finiteProductCliffordTwoReplicaTwirlLinear
        (finiteTwoReplicaSwapRaw choice) =
      finiteTwoReplicaSwapRaw choice := by
  rw [finiteTwoReplicaSwapRaw,
    finiteProductCliffordTwoReplicaTwirl_localMatrix]
  congr 1
  funext v
  exact booleanCliffordTwoReplicaTwirl_localSwapRaw (choice v)

theorem finiteProductCliffordTwoReplicaTwirl_embed
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : TwoReplicaGlobalCoeff V) :
    finiteProductCliffordTwoReplicaTwirlLinear
        (finiteTwoReplicaSwapInvariantEmbed c) =
      finiteTwoReplicaSwapInvariantEmbed c := by
  change finiteProductCliffordTwoReplicaTwirlLinear
      (∑ choice : V → Bool,
        c choice • finiteTwoReplicaSwapRaw choice) =
    ∑ choice : V → Bool,
      c choice • finiteTwoReplicaSwapRaw choice
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro choice _hchoice
  rw [map_smul,
    finiteProductCliffordTwoReplicaTwirl_swapRaw]

/-- The product doubled-Clifford twirl has exactly the global sitewise
identity/swap algebra as its range. -/
theorem finiteProductCliffordTwoReplicaTwirl_range_eq
    {V : Type*} [Fintype V] [DecidableEq V] :
    LinearMap.range
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) =
      LinearMap.range (finiteTwoReplicaSwapInvariantEmbed (V := V)) := by
  apply le_antisymm
  · exact finiteProductCliffordTwoReplicaTwirl_range_le
  · rintro Y ⟨c, rfl⟩
    exact ⟨finiteTwoReplicaSwapInvariantEmbed c,
      finiteProductCliffordTwoReplicaTwirl_embed c⟩

theorem finiteProductCliffordTwoReplicaTwirl_idempotent
    {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ X : FiniteTwoReplicaMatrix V,
      finiteProductCliffordTwoReplicaTwirlLinear
          (finiteProductCliffordTwoReplicaTwirlLinear X) =
        finiteProductCliffordTwoReplicaTwirlLinear X := by
  intro X
  exact repTwirl_idem finiteProductCliffordDoubledGate
    finiteProductCliffordDoubledGate_mul X

theorem finiteProductCliffordTwoReplicaTwirl_range_inf_ker
    {V : Type*} [Fintype V] [DecidableEq V] :
    LinearMap.range
          (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) ⊓
        LinearMap.ker
          (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) =
      ⊥ := by
  apply le_antisymm
  · rintro X ⟨⟨Y, rfl⟩, hker⟩
    change finiteProductCliffordTwoReplicaTwirlLinear
        (finiteProductCliffordTwoReplicaTwirlLinear Y) = 0 at hker
    change finiteProductCliffordTwoReplicaTwirlLinear Y = 0
    rw [← finiteProductCliffordTwoReplicaTwirl_idempotent Y]
    exact hker
  · exact bot_le

theorem finiteProductCliffordTwoReplicaTwirl_mem_greatestMaximizer
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U)
    {X : FiniteTwoReplicaMatrix V} (hX : X ∈ U) :
    finiteProductCliffordTwoReplicaTwirlLinear X ∈ U := by
  have hterm : ∀ g : V → QubitTwoDesign.BinaryOctahedral,
      finiteProductCliffordDoubledGate g * X *
          (finiteProductCliffordDoubledGate g)ᴴ ∈ U := by
    intro g
    have hm : finiteProductCliffordDoubledConjugationEquiv g X ∈
        U.map (finiteProductCliffordDoubledConjugationEquiv g :
          FiniteTwoReplicaMatrix V →ₗ[ℂ] FiniteTwoReplicaMatrix V) :=
      Submodule.mem_map_of_mem hX
    rw [finiteTwoReplicaQLocal_greatestMaximizer_productClifford_fixed
      q U hgreatest g] at hm
    exact hm
  change repTwirl finiteProductCliffordDoubledGate X ∈ U
  unfold repTwirl
  exact U.smul_mem _ (Submodule.sum_mem U fun g _ => hterm g)

/-- Every canonical greatest weight-at-most-`q` two-replica Hall obstruction
splits uniquely into a global identity/swap component and a component with
zero product-Clifford twirl. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_productCliffordTwirl_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U) :
    U =
      (U ⊓ LinearMap.range
        (finiteTwoReplicaSwapInvariantEmbed (V := V))) ⊔
      (U ⊓ LinearMap.ker
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V))) := by
  rw [← finiteProductCliffordTwoReplicaTwirl_range_eq]
  exact invariantSubspace_eq_rangeKernel_split
    finiteProductCliffordTwoReplicaTwirlLinear
    finiteProductCliffordTwoReplicaTwirl_idempotent U
    (fun x hx =>
      finiteProductCliffordTwoReplicaTwirl_mem_greatestMaximizer
        q U hgreatest hx)

/-- A finite representation twirl is unchanged when its input is conjugated
by any represented group element. -/
theorem repTwirl_conjugated_input
    {G m : Type*} [Group G] [Fintype G]
    [Fintype m] [DecidableEq m]
    (u : G → Matrix m m ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b)
    (X : Matrix m m ℂ) (V : G) :
    repTwirl u (u V * X * (u V)ᴴ) = repTwirl u X := by
  unfold repTwirl
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight V)
    (fun g => u g * X * (u g)ᴴ)]
  apply Finset.sum_congr rfl
  intro g _hg
  simp only [Equiv.coe_mulRight]
  rw [hmul, Matrix.conjTranspose_mul]
  noncomm_ring

/-- Product-Clifford twirling is unchanged by any product-Clifford
conjugation of its input. -/
theorem finiteProductCliffordTwoReplicaTwirl_conjugated_input
    {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → QubitTwoDesign.BinaryOctahedral)
    (X : FiniteTwoReplicaMatrix V) :
    finiteProductCliffordTwoReplicaTwirlLinear
        (finiteProductCliffordDoubledConjugationEquiv g X) =
      finiteProductCliffordTwoReplicaTwirlLinear X := by
  exact repTwirl_conjugated_input
    finiteProductCliffordDoubledGate
    finiteProductCliffordDoubledGate_mul X g

/-- Strict Clifford code for an identity or Pauli half turn. -/
def cliffordPauliHalfTurnCode :
    Option (Fin 3) → QubitTwoDesign.BinaryOctahedral
  | none => 1
  | some a => cliffordQuarterTurnCode a * cliffordQuarterTurnCode a

/-- Scalar phase relating a strict Clifford half turn to its raw Pauli. -/
def cliffordPauliHalfTurnPhase : Option (Fin 3) → ℂ
  | none => 1
  | some _ => Complex.I

/-- A strict Clifford half turn is exactly the raw Pauli times its required
unit complex phase. -/
theorem booleanQubitClifford_pauliHalfTurn
    (p : Option (Fin 3)) :
    booleanQubitClifford (cliffordPauliHalfTurnCode p) =
      cliffordPauliHalfTurnPhase p • boolPauliOption p := by
  rcases p with _ | a
  · simp [cliffordPauliHalfTurnCode,
      cliffordPauliHalfTurnPhase, booleanQubitClifford_one,
      boolPauliOption]
  · rw [cliffordPauliHalfTurnCode,
      booleanQubitClifford_mul,
      booleanQubitClifford_quarterTurn_matrix]
    change (rt2inv • (1 + Complex.I • finiteQubitPauli a)) *
        (rt2inv • (1 + Complex.I • finiteQubitPauli a)) =
      Complex.I • finiteQubitPauli a
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hrt : (rt2inv : ℂ) * rt2inv = 1 / 2 := by
      exact_mod_cast rt2inv_mul_self
    rw [hrt]
    have hsq :
        (1 + Complex.I • finiteQubitPauli a) *
            (1 + Complex.I • finiteQubitPauli a) =
          (2 : ℂ) • (Complex.I • finiteQubitPauli a) := by
      rw [Matrix.add_mul]
      simp_rw [Matrix.mul_add]
      simp only [Matrix.one_mul, Matrix.mul_one]
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
        smul_smul, finiteQubitPauli_mul_self,
        Complex.I_mul_I]
      module
    rw [hsq, smul_smul]
    norm_num

/-- Sitewise strict Clifford realization of a phase-free Pauli word. -/
def finitePauliHalfTurnCode
    {V : Type*} (Q : V → Option (Fin 3)) :
    V → QubitTwoDesign.BinaryOctahedral :=
  fun v => cliffordPauliHalfTurnCode (Q v)

/-- Product phase of the strict realization of a Pauli word. -/
def finitePauliHalfTurnPhase
    {V : Type*} [Fintype V] (Q : V → Option (Fin 3)) : ℂ :=
  ∏ v, cliffordPauliHalfTurnPhase (Q v)

/-- A product of strict half turns equals the corresponding Pauli word up
to one explicit global phase. -/
theorem finiteProductCliffordGate_pauliHalfTurn
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Option (Fin 3)) :
    finiteProductCliffordGate (finitePauliHalfTurnCode Q) =
      finitePauliHalfTurnPhase Q • finitePauliMatrix Q := by
  rw [finiteProductCliffordGate,
    finitePauliMatrix_eq_finiteLocalMatrix,
    finitePauliHalfTurnPhase,
    ← finiteLocalMatrix_pointwise_smul]
  congr 1
  funext v
  exact booleanQubitClifford_pauliHalfTurn (Q v)

/-- The product half-turn phase has unit norm. -/
theorem finitePauliHalfTurnPhase_mul_conj
    {V : Type*} [Fintype V] (Q : V → Option (Fin 3)) :
    finitePauliHalfTurnPhase Q *
        star (finitePauliHalfTurnPhase Q) = 1 := by
  rw [finitePauliHalfTurnPhase, ← starRingEnd_apply, map_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro v _hv
  rcases h : Q v with _ | a
  · simp [cliffordPauliHalfTurnPhase]
  · simp [cliffordPauliHalfTurnPhase]

/-- Doubled conjugation by the strict product-Clifford code is literally
paired-Pauli conjugation; its global phase cancels. -/
theorem finiteProductCliffordDoubledConjugation_pauliHalfTurn
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Option (Fin 3)) (X : FiniteTwoReplicaMatrix V) :
    finiteProductCliffordDoubledConjugationEquiv
        (finitePauliHalfTurnCode Q) X =
      finiteTwoReplicaPairedPauliConjugationLinear Q X := by
  rw [finiteProductCliffordDoubledConjugationEquiv_apply]
  rw [finiteProductCliffordDoubledGate,
    finiteProductCliffordGate_pauliHalfTurn]
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
  let d := finitePauliHalfTurnPhase Q *
    finitePauliHalfTurnPhase Q
  have hd : d * star d = 1 := by
    dsimp [d]
    rw [map_mul]
    have hphase := finitePauliHalfTurnPhase_mul_conj Q
    calc
      finitePauliHalfTurnPhase Q *
          finitePauliHalfTurnPhase Q *
          (star (finitePauliHalfTurnPhase Q) *
            star (finitePauliHalfTurnPhase Q)) =
        (finitePauliHalfTurnPhase Q *
          star (finitePauliHalfTurnPhase Q)) *
        (finitePauliHalfTurnPhase Q *
          star (finitePauliHalfTurnPhase Q)) := by ring
      _ = 1 := by rw [hphase]; simp
  change (_ • finiteTwoReplicaPairedPauli Q) * X *
      (_ • finiteTwoReplicaPairedPauli Q)ᴴ = _
  change (d • finiteTwoReplicaPairedPauli Q) * X *
      (d • finiteTwoReplicaPairedPauli Q)ᴴ = _
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [mul_comm (star d) d, hd]
  simp [finiteTwoReplicaPairedPauliConjugationLinear,
    finiteTwoReplicaPairedPauli_conjTranspose]

/-- Product-Clifford twirling is unchanged by paired-Pauli conjugation of
the input. -/
theorem finiteProductCliffordTwoReplicaTwirl_pairedPauli_input
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Option (Fin 3)) (X : FiniteTwoReplicaMatrix V) :
    finiteProductCliffordTwoReplicaTwirlLinear
        (finiteTwoReplicaPairedPauliConjugationLinear Q X) =
      finiteProductCliffordTwoReplicaTwirlLinear X := by
  rw [← finiteProductCliffordDoubledConjugation_pauliHalfTurn]
  exact finiteProductCliffordTwoReplicaTwirl_conjugated_input _ _

/-- The exact zero-product-Clifford-twirl sector is invariant under every
paired-Pauli conjugation. -/
theorem finiteProductCliffordTwoReplicaTwirl_ker_pairedPauli_invariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : V → Option (Fin 3)) :
    (LinearMap.ker
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V))).map
        (finiteTwoReplicaPairedPauliConjugationLinear Q) ≤
      LinearMap.ker finiteProductCliffordTwoReplicaTwirlLinear := by
  rintro _ ⟨X, hX, rfl⟩
  change finiteProductCliffordTwoReplicaTwirlLinear X = 0 at hX
  change finiteProductCliffordTwoReplicaTwirlLinear
    (finiteTwoReplicaPairedPauliConjugationLinear Q X) = 0
  rw [finiteProductCliffordTwoReplicaTwirl_pairedPauli_input]
  exact hX


end

end GaloisForLFunctions.HTGeometry
