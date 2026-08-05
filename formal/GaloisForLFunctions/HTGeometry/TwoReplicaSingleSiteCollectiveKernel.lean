import GaloisForLFunctions.HTGeometry.TwoReplicaLocalCollectiveCommonKernel
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordTwirlRange

open scoped BigOperators Matrix Kronecker
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

abbrev FiniteTwoReplicaSiteOutside (V : Type*) (j : V) :=
  {s : V // s ≠ j} → TwoReplicaLocalIndex

def finiteTwoReplicaSingleSiteSplitEquiv (V : Type*) [DecidableEq V] (j : V) :
    FiniteTwoReplicaConfiguration V ≃
      TwoReplicaLocalIndex × FiniteTwoReplicaSiteOutside V j where
  toFun x := ((x.1 j, x.2 j), fun s => (x.1 s.1, x.2 s.1))
  invFun p :=
    (fun s => if hs : s = j then p.1.1 else (p.2 ⟨s, hs⟩).1,
     fun s => if hs : s = j then p.1.2 else (p.2 ⟨s, hs⟩).2)
  left_inv x := by
    apply Prod.ext <;> funext s <;> by_cases hs : s = j
    · subst s
      simp
    · simp [hs]
    · subst s
      simp
    · simp [hs]
  right_inv p := by
    rcases p with ⟨p, outside⟩
    apply Prod.ext
    · simp
    · funext s
      simp [s.2]

def matrixProdBlock
    {I O : Type*}
    (X : Matrix (I × O) (I × O) ℂ) (r s : O) : Matrix I I ℂ :=
  fun p q => X (p, r) (q, s)

theorem matrixProdBlock_ringCommutator_kronecker_one
    {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (H : Matrix I I ℂ) (X : Matrix (I × O) (I × O) ℂ) (r s : O) :
    matrixProdBlock (ringCommutator
      (H ⊗ₖ (1 : Matrix O O ℂ)) X) r s =
      ringCommutator H (matrixProdBlock X r s) := by
  ext p q
  simp [matrixProdBlock, ringCommutator, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply]

theorem finiteTwoReplicaSingleSite_collectiveGenerator_reindex
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) :
    Matrix.reindex (finiteTwoReplicaSingleSiteSplitEquiv V j)
        (finiteTwoReplicaSingleSiteSplitEquiv V j)
        (finiteTwoReplicaPauliLeft (finiteSingleSitePauliLabel j a) +
          finiteTwoReplicaPauliRight (finiteSingleSitePauliLabel j a)) =
      (twoReplicaPauliLeft a + twoReplicaPauliRight a) ⊗ₖ
        (1 : Matrix (FiniteTwoReplicaSiteOutside V j)
          (FiniteTwoReplicaSiteOutside V j) ℂ) := by
  simp only [finiteTwoReplicaPauliLeft, finiteTwoReplicaPauliRight]
  rw [← finiteSingleSiteMatrix_pauli j a]
  let e := finiteTwoReplicaSingleSiteSplitEquiv V j
  ext ⟨p, r⟩ ⟨q, s⟩
  let x := e.symm (p, r)
  let y := e.symm (q, s)
  have hx := e.apply_symm_apply (p, r)
  have hy := e.apply_symm_apply (q, s)
  have hxlocal : (x.1 j, x.2 j) = p := congrArg Prod.fst hx
  have hylocal : (y.1 j, y.2 j) = q := congrArg Prod.fst hy
  have hxj₁ : x.1 j = p.1 := congrArg Prod.fst hxlocal
  have hxj₂ : x.2 j = p.2 := congrArg Prod.snd hxlocal
  have hyj₁ : y.1 j = q.1 := congrArg Prod.fst hylocal
  have hyj₂ : y.2 j = q.2 := congrArg Prod.snd hylocal
  have hxout (t : {u : V // u ≠ j}) : (x.1 t.1, x.2 t.1) = r t := by
    exact congrFun (congrArg Prod.snd hx) t
  have hyout (t : {u : V // u ≠ j}) : (y.1 t.1, y.2 t.1) = s t := by
    exact congrFun (congrArg Prod.snd hy) t
  change
    (finiteSingleSiteMatrix j (finiteQubitPauli a) x.1 y.1 *
        (1 : Matrix (FiniteQubitConfiguration V)
          (FiniteQubitConfiguration V) ℂ) x.2 y.2 +
      (1 : Matrix (FiniteQubitConfiguration V)
          (FiniteQubitConfiguration V) ℂ) x.1 y.1 *
        finiteSingleSiteMatrix j (finiteQubitPauli a) x.2 y.2) =
      (twoReplicaPauliLeft a p q + twoReplicaPauliRight a p q) *
        (1 : Matrix (FiniteTwoReplicaSiteOutside V j)
          (FiniteTwoReplicaSiteOutside V j) ℂ) r s
  by_cases hrs : r = s
  · subst s
    have hout₁ : ∀ u ∈ Finset.univ.erase j, x.1 u = y.1 u := by
      intro u hu
      have hune : u ≠ j := Finset.ne_of_mem_erase hu
      have hx' := congrArg Prod.fst (hxout ⟨u, hune⟩)
      have hy' := congrArg Prod.fst (hyout ⟨u, hune⟩)
      exact hx'.trans hy'.symm
    have hout₂ : ∀ u ∈ Finset.univ.erase j, x.2 u = y.2 u := by
      intro u hu
      have hune : u ≠ j := Finset.ne_of_mem_erase hu
      have hx' := congrArg Prod.snd (hxout ⟨u, hune⟩)
      have hy' := congrArg Prod.snd (hyout ⟨u, hune⟩)
      exact hx'.trans hy'.symm
    have hprod₁ : (∏ u ∈ Finset.univ.erase j,
        (1 : Matrix Bool Bool ℂ) (x.1 u) (y.1 u)) = 1 := by
      apply Finset.prod_eq_one
      intro u hu
      simp [Matrix.one_apply, hout₁ u hu]
    have hprod₂ : (∏ u ∈ Finset.univ.erase j,
        (1 : Matrix Bool Bool ℂ) (x.2 u) (y.2 u)) = 1 := by
      apply Finset.prod_eq_one
      intro u hu
      simp [Matrix.one_apply, hout₂ u hu]
    have hone₁ : (1 : Matrix (FiniteQubitConfiguration V)
        (FiniteQubitConfiguration V) ℂ) x.1 y.1 =
        (1 : Matrix Bool Bool ℂ) p.1 q.1 := by
      rw [Matrix.one_apply, Matrix.one_apply]
      congr 1
      apply propext
      constructor
      · intro h
        have hj := congrFun h j
        exact hxj₁.symm.trans (hj.trans hyj₁)
      · intro hpq
        funext u
        by_cases hu : u = j
        · subst u
          exact hxj₁.trans (hpq.trans hyj₁.symm)
        · have hx' := congrArg Prod.fst (hxout ⟨u, hu⟩)
          have hy' := congrArg Prod.fst (hyout ⟨u, hu⟩)
          exact hx'.trans hy'.symm
    have hone₂ : (1 : Matrix (FiniteQubitConfiguration V)
        (FiniteQubitConfiguration V) ℂ) x.2 y.2 =
        (1 : Matrix Bool Bool ℂ) p.2 q.2 := by
      rw [Matrix.one_apply, Matrix.one_apply]
      congr 1
      apply propext
      constructor
      · intro h
        have hj := congrFun h j
        exact hxj₂.symm.trans (hj.trans hyj₂)
      · intro hpq
        funext u
        by_cases hu : u = j
        · subst u
          exact hxj₂.trans (hpq.trans hyj₂.symm)
        · have hx' := congrArg Prod.snd (hxout ⟨u, hu⟩)
          have hy' := congrArg Prod.snd (hyout ⟨u, hu⟩)
          exact hx'.trans hy'.symm
    rw [finiteSingleSiteMatrix_apply, finiteSingleSiteMatrix_apply,
      hprod₁, hprod₂, mul_one, mul_one, hone₁, hone₂]
    rw [hxj₁, hxj₂, hyj₁, hyj₂]
    simp [twoReplicaPauliLeft, twoReplicaPauliRight]
  · obtain ⟨t, ht⟩ := Function.ne_iff.mp hrs
    have hcomp : (r t).1 ≠ (s t).1 ∨ (r t).2 ≠ (s t).2 := by
      by_cases h₁ : (r t).1 = (s t).1
      · right
        intro h₂
        exact ht (Prod.ext h₁ h₂)
      · exact Or.inl h₁
    rcases hcomp with ht₁ | ht₂
    · have hxy : x.1 t.1 ≠ y.1 t.1 := by
        intro h
        apply ht₁
        rw [← hxout t, ← hyout t, h]
      have hsingle : finiteSingleSiteMatrix j (finiteQubitPauli a)
          x.1 y.1 = 0 := by
        rw [finiteSingleSiteMatrix_apply]
        have hp : (∏ u ∈ Finset.univ.erase j,
            (1 : Matrix Bool Bool ℂ) (x.1 u) (y.1 u)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨t.2, Finset.mem_univ _⟩)
          simp [hxy]
        rw [hp, mul_zero]
      have hone : (1 : Matrix (FiniteQubitConfiguration V)
          (FiniteQubitConfiguration V) ℂ) x.1 y.1 = 0 := by
        rw [Matrix.one_apply, if_neg]
        intro h
        exact hxy (congrFun h t.1)
      rw [hsingle, hone]
      simp [Matrix.one_apply, hrs]
    · have hxy : x.2 t.1 ≠ y.2 t.1 := by
        intro h
        apply ht₂
        rw [← hxout t, ← hyout t, h]
      have hsingle : finiteSingleSiteMatrix j (finiteQubitPauli a)
          x.2 y.2 = 0 := by
        rw [finiteSingleSiteMatrix_apply]
        have hp : (∏ u ∈ Finset.univ.erase j,
            (1 : Matrix Bool Bool ℂ) (x.2 u) (y.2 u)) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨t.2, Finset.mem_univ _⟩)
          simp [hxy]
        rw [hp, mul_zero]
      have hone : (1 : Matrix (FiniteQubitConfiguration V)
          (FiniteQubitConfiguration V) ℂ) x.2 y.2 = 0 := by
        rw [Matrix.one_apply, if_neg]
        intro h
        exact hxy (congrFun h t.1)
      rw [hone, hsingle]
      simp [Matrix.one_apply, hrs]

theorem finiteTwoReplicaSingleSite_collectiveCommutator_reindex
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V) :
    Matrix.reindex (finiteTwoReplicaSingleSiteSplitEquiv V j)
        (finiteTwoReplicaSingleSiteSplitEquiv V j)
        (finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X) =
      ringCommutator
        ((twoReplicaPauliLeft a + twoReplicaPauliRight a) ⊗ₖ
          (1 : Matrix (FiniteTwoReplicaSiteOutside V j)
            (FiniteTwoReplicaSiteOutside V j) ℂ))
        (Matrix.reindex (finiteTwoReplicaSingleSiteSplitEquiv V j)
          (finiteTwoReplicaSingleSiteSplitEquiv V j) X) := by
  let e := finiteTwoReplicaSingleSiteSplitEquiv V j
  change Matrix.reindexAlgEquiv ℂ ℂ e
      (finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X) = _
  rw [show finiteTwoReplicaCollectiveCommutatorLinear
      (finiteSingleSitePauliLabel j a) X =
      ringCommutator
        (finiteTwoReplicaPauliLeft (finiteSingleSitePauliLabel j a) +
          finiteTwoReplicaPauliRight (finiteSingleSitePauliLabel j a)) X by
    simp [finiteTwoReplicaCollectiveCommutatorLinear,
      finiteTwoReplicaCollectiveCommutator, ringCommutator]
    noncomm_ring]
  simp only [ringCommutator, map_sub, map_mul]
  rw [Matrix.coe_reindexAlgEquiv,
    finiteTwoReplicaSingleSite_collectiveGenerator_reindex]

theorem finiteTwoReplicaSingleSiteLocalMatrix_reindex
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (M : TwoReplicaLocalMatrix) :
    Matrix.reindex (finiteTwoReplicaSingleSiteSplitEquiv V j)
        (finiteTwoReplicaSingleSiteSplitEquiv V j)
        (finiteTwoReplicaLocalMatrix fun u => if u = j then M else 1) =
      M ⊗ₖ (1 : Matrix (FiniteTwoReplicaSiteOutside V j)
        (FiniteTwoReplicaSiteOutside V j) ℂ) := by
  let e := finiteTwoReplicaSingleSiteSplitEquiv V j
  ext ⟨p, r⟩ ⟨q, s⟩
  let x := e.symm (p, r)
  let y := e.symm (q, s)
  have hx := e.apply_symm_apply (p, r)
  have hy := e.apply_symm_apply (q, s)
  have hxlocal : (x.1 j, x.2 j) = p := congrArg Prod.fst hx
  have hylocal : (y.1 j, y.2 j) = q := congrArg Prod.fst hy
  have hxout (t : {u : V // u ≠ j}) : (x.1 t.1, x.2 t.1) = r t := by
    exact congrFun (congrArg Prod.snd hx) t
  have hyout (t : {u : V // u ≠ j}) : (y.1 t.1, y.2 t.1) = s t := by
    exact congrFun (congrArg Prod.snd hy) t
  change (∏ u, (if u = j then M else 1)
      (x.1 u, x.2 u) (y.1 u, y.2 u)) =
    M p q * (1 : Matrix (FiniteTwoReplicaSiteOutside V j)
      (FiniteTwoReplicaSiteOutside V j) ℂ) r s
  rw [← Finset.mul_prod_erase Finset.univ
    (fun u => (if u = j then M else 1)
      (x.1 u, x.2 u) (y.1 u, y.2 u)) (Finset.mem_univ j)]
  simp only [if_pos, hxlocal, hylocal]
  by_cases hrs : r = s
  · subst s
    have hp : (∏ u ∈ Finset.univ.erase j,
        (if u = j then M else 1)
          (x.1 u, x.2 u) (y.1 u, y.2 u)) = 1 := by
      apply Finset.prod_eq_one
      intro u hu
      have hune : u ≠ j := Finset.ne_of_mem_erase hu
      have hxy : (x.1 u, x.2 u) = (y.1 u, y.2 u) :=
        (hxout ⟨u, hune⟩).trans (hyout ⟨u, hune⟩).symm
      simp [hune, Matrix.one_apply, hxy]
    rw [hp, mul_one]
    simp
  · obtain ⟨t, ht⟩ := Function.ne_iff.mp hrs
    have hp : (∏ u ∈ Finset.univ.erase j,
        (if u = j then M else 1)
          (x.1 u, x.2 u) (y.1 u, y.2 u)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨t.2, Finset.mem_univ _⟩)
      have hxy : (x.1 t.1, x.2 t.1) ≠ (y.1 t.1, y.2 t.1) := by
        intro h
        exact ht ((hxout t).symm.trans (h.trans (hyout t)))
      simp [t.2, hxy]
    rw [hp, mul_zero]
    simp [hrs]

theorem finiteTwoReplicaSingleSiteLocalMatrix_commute_of_collectiveCommutators_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (M : TwoReplicaLocalMatrix) (X : FiniteTwoReplicaMatrix V)
    (hX : ∀ a : Fin 3,
      finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X = 0)
    (hM : ∀ B : TwoReplicaLocalMatrix,
      B ∈ Submodule.span ℂ
        ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
          Set TwoReplicaLocalMatrix) → M * B = B * M) :
    finiteTwoReplicaLocalMatrix (fun u => if u = j then M else 1) * X =
      X * finiteTwoReplicaLocalMatrix (fun u => if u = j then M else 1) := by
  let e := finiteTwoReplicaSingleSiteSplitEquiv V j
  let Y := Matrix.reindex e e X
  have hblocks : ∀ r s : FiniteTwoReplicaSiteOutside V j,
      M * matrixProdBlock Y r s = matrixProdBlock Y r s * M := by
    intro r s
    apply hM
    have hker : matrixProdBlock Y r s ∈
        {B : TwoReplicaLocalMatrix |
          ∀ a : Fin 3, twoReplicaLocalCollectiveCommutatorLinear a B = 0} := by
      intro a
      have hreindex := finiteTwoReplicaSingleSite_collectiveCommutator_reindex
        j a X
      rw [hX a] at hreindex
      change Matrix.reindexAlgEquiv ℂ ℂ e 0 = _ at hreindex
      rw [map_zero] at hreindex
      have hblock := congrArg (fun Z => matrixProdBlock Z r s) hreindex
      rw [matrixProdBlock_ringCommutator_kronecker_one] at hblock
      have hzero : matrixProdBlock
          (0 : Matrix (TwoReplicaLocalIndex × FiniteTwoReplicaSiteOutside V j)
            (TwoReplicaLocalIndex × FiniteTwoReplicaSiteOutside V j) ℂ) r s = 0 := rfl
      rw [hzero] at hblock
      change twoReplicaLocalCollectiveCommutatorLinear a
        (matrixProdBlock Y r s) = 0
      rw [show twoReplicaLocalCollectiveCommutatorLinear a
          (matrixProdBlock Y r s) =
          ringCommutator (twoReplicaPauliLeft a + twoReplicaPauliRight a)
            (matrixProdBlock Y r s) by
        simp [twoReplicaLocalCollectiveCommutatorLinear,
          twoReplicaLocalCollectiveCommutator, ringCommutator]
        noncomm_ring]
      simpa [Y, e] using hblock.symm
    rw [twoReplicaLocalCollectiveCommutator_commonKernel] at hker
    exact hker
  have hcomm : ringCommutator
      (M ⊗ₖ (1 : Matrix (FiniteTwoReplicaSiteOutside V j)
        (FiniteTwoReplicaSiteOutside V j) ℂ)) Y = 0 := by
    apply Matrix.ext
    rintro ⟨p, r⟩ ⟨q, s⟩
    have hblock := matrixProdBlock_ringCommutator_kronecker_one M Y r s
    have hlocal : ringCommutator M (matrixProdBlock Y r s) = 0 := by
      rw [ringCommutator, hblocks r s, sub_self]
    rw [hlocal] at hblock
    have hentry := congrFun (congrFun hblock p) q
    simpa [matrixProdBlock] using hentry
  apply (Matrix.reindexAlgEquiv ℂ ℂ e).injective
  simp only [map_mul, Matrix.coe_reindexAlgEquiv]
  rw [finiteTwoReplicaSingleSiteLocalMatrix_reindex]
  exact sub_eq_zero.mp hcomm

theorem finiteTwoReplicaSingleSiteClifford_commute_of_collectiveCommutators_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (g : QubitTwoDesign.BinaryOctahedral)
    (X : FiniteTwoReplicaMatrix V)
    (hX : ∀ a : Fin 3,
      finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X = 0) :
    finiteTwoReplicaLocalMatrix (fun u =>
        if u = j then booleanCliffordDoubledGate g else 1) * X =
      X * finiteTwoReplicaLocalMatrix (fun u =>
        if u = j then booleanCliffordDoubledGate g else 1) := by
  apply finiteTwoReplicaSingleSiteLocalMatrix_commute_of_collectiveCommutators_eq_zero
    j (booleanCliffordDoubledGate g) X hX
  intro B hB
  rw [Submodule.mem_span_pair] at hB
  obtain ⟨c, d, rfl⟩ := hB
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  rw [booleanCliffordDoubledGate_commute_twoReplicaSwap]

theorem finiteProductCliffordDoubledGate_commute_of_singleSiteCollective_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : FiniteTwoReplicaMatrix V)
    (hX : ∀ j : V, ∀ a : Fin 3,
      finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X = 0)
    (g : V → QubitTwoDesign.BinaryOctahedral) :
    finiteProductCliffordDoubledGate g * X =
      X * finiteProductCliffordDoubledGate g := by
  rw [finiteProductCliffordDoubledGate_eq_localMatrix]
  have hpartial : ∀ S : Finset V,
      finiteTwoReplicaLocalMatrix (fun u =>
          if u ∈ S then booleanCliffordDoubledGate (g u) else 1) * X =
        X * finiteTwoReplicaLocalMatrix (fun u =>
          if u ∈ S then booleanCliffordDoubledGate (g u) else 1) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        have hone : finiteTwoReplicaLocalMatrix
            (fun _ : V => (1 : TwoReplicaLocalMatrix)) = 1 := by
          ext x y
          simp only [finiteTwoReplicaLocalMatrix, Matrix.one_apply]
          by_cases hxy : x = y
          · subst y
            simp
          · rw [if_neg hxy]
            have hlocal : finiteTwoReplicaConfigurationEquiv V x ≠
                finiteTwoReplicaConfigurationEquiv V y := by
              exact fun h => hxy ((finiteTwoReplicaConfigurationEquiv V).injective h)
            obtain ⟨u, hu⟩ := Function.ne_iff.mp hlocal
            apply Finset.prod_eq_zero (Finset.mem_univ u)
            rw [if_neg]
            intro h
            exact hu h
        simp [hone]
    | @insert j S hj ih =>
        let A := finiteTwoReplicaLocalMatrix (fun u =>
          if u = j then booleanCliffordDoubledGate (g j) else 1)
        let B := finiteTwoReplicaLocalMatrix (fun u =>
          if u ∈ S then booleanCliffordDoubledGate (g u) else 1)
        have hA : A * X = X * A := by
          exact finiteTwoReplicaSingleSiteClifford_commute_of_collectiveCommutators_eq_zero
            j (g j) X (hX j)
        have hfactor : finiteTwoReplicaLocalMatrix (fun u =>
            if u ∈ insert j S then booleanCliffordDoubledGate (g u) else 1) =
            A * B := by
          dsimp only [A, B]
          rw [finiteTwoReplicaLocalMatrix_mul]
          congr 1
          funext u
          by_cases huj : u = j
          · subst u
            simp [hj]
          · simp [huj]
        rw [hfactor]
        calc
          A * B * X = A * (B * X) := by noncomm_ring
          _ = A * (X * B) := by rw [ih]
          _ = (A * X) * B := by noncomm_ring
          _ = (X * A) * B := by rw [hA]
          _ = X * (A * B) := by noncomm_ring
  have hall := hpartial Finset.univ
  simpa using hall

theorem finiteProductCliffordTwoReplicaTwirl_eq_self_of_singleSiteCollective_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : FiniteTwoReplicaMatrix V)
    (hX : ∀ j : V, ∀ a : Fin 3,
      finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X = 0) :
    finiteProductCliffordTwoReplicaTwirlLinear X = X := by
  haveI : Nonempty (V → QubitTwoDesign.BinaryOctahedral) := ⟨fun _ => 1⟩
  have hcard : (Fintype.card (V → QubitTwoDesign.BinaryOctahedral) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ g : V → QubitTwoDesign.BinaryOctahedral,
      finiteProductCliffordDoubledGate g * X *
          (finiteProductCliffordDoubledGate g)ᴴ = X := by
    intro g
    rw [finiteProductCliffordDoubledGate_commute_of_singleSiteCollective_eq_zero
      X hX g, Matrix.mul_assoc,
      mul_eq_one_comm.mp (finiteProductCliffordDoubledGate_unitary g),
      Matrix.mul_one]
  change repTwirl finiteProductCliffordDoubledGate X = X
  rw [repTwirl, Finset.sum_congr rfl (fun g _ => hterm g),
    Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

theorem finiteTwoReplica_singleSiteCollective_commonKernel_le_productCliffordTwirl_range
    {V : Type*} [Fintype V] [DecidableEq V] :
    {X : FiniteTwoReplicaMatrix V |
      ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X = 0} ⊆
      LinearMap.range
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) := by
  intro X hX
  exact ⟨X,
    finiteProductCliffordTwoReplicaTwirl_eq_self_of_singleSiteCollective_eq_zero X hX⟩

theorem finiteTwoReplicaSingleSite_collectiveGenerator_eq_localMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) :
    finiteTwoReplicaPauliLeft (finiteSingleSitePauliLabel j a) +
        finiteTwoReplicaPauliRight (finiteSingleSitePauliLabel j a) =
      finiteTwoReplicaLocalMatrix (fun u => if u = j then
        twoReplicaPauliLeft a + twoReplicaPauliRight a else 1) := by
  let e := finiteTwoReplicaSingleSiteSplitEquiv V j
  apply (Matrix.reindexAlgEquiv ℂ ℂ e).injective
  rw [Matrix.coe_reindexAlgEquiv,
    finiteTwoReplicaSingleSite_collectiveGenerator_reindex]
  rw [
    finiteTwoReplicaSingleSiteLocalMatrix_reindex]

theorem finiteTwoReplicaSingleSiteCollectiveCommutator_swapRaw_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) (choice : V → Bool) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a)
        (finiteTwoReplicaSwapRaw choice) = 0 := by
  rw [show finiteTwoReplicaCollectiveCommutatorLinear
      (finiteSingleSitePauliLabel j a) (finiteTwoReplicaSwapRaw choice) =
      ringCommutator
        (finiteTwoReplicaPauliLeft (finiteSingleSitePauliLabel j a) +
          finiteTwoReplicaPauliRight (finiteSingleSitePauliLabel j a))
        (finiteTwoReplicaSwapRaw choice) by
    simp [finiteTwoReplicaCollectiveCommutatorLinear,
      finiteTwoReplicaCollectiveCommutator, ringCommutator]
    noncomm_ring]
  rw [finiteTwoReplicaSingleSite_collectiveGenerator_eq_localMatrix,
    finiteTwoReplicaSwapRaw, ringCommutator,
    finiteTwoReplicaLocalMatrix_mul, finiteTwoReplicaLocalMatrix_mul]
  rw [sub_eq_zero]
  congr 1
  funext u
  by_cases hu : u = j
  · subst u
    have hlocal : twoReplicaLocalCollectiveCommutatorLinear a
        (twoReplicaLocalSwapRaw (choice j)) = 0 := by
      have hmem : twoReplicaLocalSwapRaw (choice j) ∈
          Submodule.span ℂ
            ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
              Set TwoReplicaLocalMatrix) := by
        cases hchoice : choice j
        · change (1 : TwoReplicaLocalMatrix) ∈
            Submodule.span ℂ
              ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
                Set TwoReplicaLocalMatrix)
          exact Submodule.subset_span (by simp)
        · change twoReplicaSwap ∈
            Submodule.span ℂ
              ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} :
                Set TwoReplicaLocalMatrix)
          exact Submodule.subset_span (by simp)
      have hker : twoReplicaLocalSwapRaw (choice j) ∈
          {B : TwoReplicaLocalMatrix |
            ∀ b : Fin 3, twoReplicaLocalCollectiveCommutatorLinear b B = 0} := by
        rw [twoReplicaLocalCollectiveCommutator_commonKernel]
        exact hmem
      exact hker a
    simp only [if_pos]
    change (twoReplicaPauliLeft a + twoReplicaPauliRight a) *
        twoReplicaLocalSwapRaw (choice j) =
      twoReplicaLocalSwapRaw (choice j) *
        (twoReplicaPauliLeft a + twoReplicaPauliRight a)
    apply sub_eq_zero.mp
    calc
      ringCommutator (twoReplicaPauliLeft a + twoReplicaPauliRight a)
          (twoReplicaLocalSwapRaw (choice j)) =
          twoReplicaLocalCollectiveCommutatorLinear a
            (twoReplicaLocalSwapRaw (choice j)) := by
              simp [twoReplicaLocalCollectiveCommutatorLinear,
                twoReplicaLocalCollectiveCommutator, ringCommutator]
              noncomm_ring
      _ = 0 := hlocal
  · simp [hu]

/-- Exact finite-register rigidity law: simultaneous commutation with every
one-site doubled Pauli generator is equivalent to belonging to the complete
sitewise identity/swap sector selected by the product-Clifford twirl. -/
theorem finiteTwoReplica_singleSiteCollective_commonKernel_eq_productCliffordTwirl_range
    {V : Type*} [Fintype V] [DecidableEq V] :
    {X : FiniteTwoReplicaMatrix V |
      ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X = 0} =
      (LinearMap.range
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) :
          Set (FiniteTwoReplicaMatrix V)) := by
  apply Set.Subset.antisymm
  · exact finiteTwoReplica_singleSiteCollective_commonKernel_le_productCliffordTwirl_range
  · intro X hX
    rw [finiteProductCliffordTwoReplicaTwirl_range_eq] at hX
    rcases hX with ⟨c, rfl⟩
    intro j a
    change finiteTwoReplicaCollectiveCommutatorLinear
      (finiteSingleSitePauliLabel j a)
      (∑ choice : V → Bool,
        c choice • finiteTwoReplicaSwapRaw choice) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro choice _
    rw [map_smul,
      finiteTwoReplicaSingleSiteCollectiveCommutator_swapRaw_eq_zero,
      smul_zero]

end

end GaloisForLFunctions.HTGeometry
