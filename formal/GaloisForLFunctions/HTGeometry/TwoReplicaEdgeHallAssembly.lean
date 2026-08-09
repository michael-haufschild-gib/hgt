import GaloisForLFunctions.HTGeometry.TwoReplicaEdgeHallExpansion

/-!
# Assembly of the fixed-orientation two-replica edge Hall expansion

The edge-defect sectors of distinct edges are Hilbert–Schmidt orthogonal, and one fixed-orientation
edge commutator is injective on the mismatch fibre of its own edge.  Together with faithfulness of
the stacked mismatch projections this gives the Hall inequality: on the sitewise singlet algebra,
the family of one-orientation edge commutators expands every subspace transverse to the global
permutation line.
-/

open Matrix Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The endpoint letters -/

/-- The local output letter at an endpoint: a replica difference, swap-translated when the word
carries a swap there. -/
def localDiffLetter (s : Bool) (a : Fin 3) : Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  if s then twoReplicaSwap * twoReplicaLocalDiff a else twoReplicaLocalDiff a

omit [Fintype V] in
theorem edgeOutputLocal_left_eq (u v : V) (a b : Fin 3) (x : V → Bool) :
    edgeOutputLocal u v a b x u = localDiffLetter (x u) a := by
  simp [edgeOutputLocal, localDiffLetter]

omit [Fintype V] in
theorem edgeOutputLocal_right_eq {u v : V} (huv : u ≠ v) (a b : Fin 3) (x : V → Bool) :
    edgeOutputLocal u v a b x v = localDiffLetter (x v) b := by
  simp [edgeOutputLocal, localDiffLetter, huv.symm]

theorem trace_conjTranspose_localDiffLetter_mul_swapRaw (s : Bool) (a : Fin 3) (t : Bool) :
    Matrix.trace ((localDiffLetter s a)ᴴ * twoReplicaLocalSwapRaw t) = 0 := by
  cases s with
  | false => simpa [localDiffLetter] using trace_conjTranspose_diff_mul_swapRaw a t
  | true => simpa [localDiffLetter] using trace_conjTranspose_swapDiff_mul_swapRaw a t

theorem trace_conjTranspose_swapRaw_mul_localDiffLetter (t s : Bool) (a : Fin 3) :
    Matrix.trace ((twoReplicaLocalSwapRaw t)ᴴ * localDiffLetter s a) = 0 := by
  cases s with
  | false => simpa [localDiffLetter] using trace_conjTranspose_swapRaw_mul_diff a t
  | true => simpa [localDiffLetter] using trace_conjTranspose_swapRaw_mul_swapDiff a t

theorem trace_conjTranspose_localDiffLetter_mul_of_ne {s s' : Bool} (hss : s ≠ s') (a : Fin 3) :
    Matrix.trace ((localDiffLetter s a)ᴴ * localDiffLetter s' a) = 0 := by
  cases s with
  | false =>
      cases s' with
      | false => exact absurd rfl hss
      | true => simpa [localDiffLetter] using trace_conjTranspose_diff_mul_swapDiff a
  | true =>
      cases s' with
      | false => simpa [localDiffLetter] using trace_conjTranspose_swapDiff_mul_diff a
      | true => exact absurd rfl hss

theorem trace_conjTranspose_localDiffLetter_self (s : Bool) (a : Fin 3) :
    Matrix.trace ((localDiffLetter s a)ᴴ * localDiffLetter s a) = 8 := by
  cases s with
  | false =>
      simp only [localDiffLetter, if_false, Bool.false_eq_true]
      rw [isHermitian_twoReplicaLocalDiff a, trace_twoReplicaLocalDiff_sq]
  | true =>
      simpa [localDiffLetter] using trace_conjTranspose_swapDiff_mul_swapDiff a

theorem localDiffLetter_ne_zero (s : Bool) (a : Fin 3) : localDiffLetter s a ≠ 0 := by
  intro h
  have h8 := trace_conjTranspose_localDiffLetter_self s a
  rw [h] at h8
  simp at h8

theorem exists_localDiffLetter_ne_zero (s : Bool) (a : Fin 3) :
    ∃ i j, localDiffLetter s a i j ≠ 0 := by
  by_contra hcon
  refine localDiffLetter_ne_zero s a (Matrix.ext fun i j => ?_)
  simp only [Matrix.zero_apply]
  by_contra hij
  exact hcon ⟨i, j, hij⟩

/-! ### Orthogonality of edge-defect sectors -/

theorem trace_conjTranspose_edgeOutput_mul_edgeOutput_of_outside
    {u v u' v' : V} (huv : u ≠ v) (a b : Fin 3) {w : V}
    (hw : w = u ∨ w = v) (hw' : w ≠ u') (hw'' : w ≠ v') (x y : V → Bool) :
    Matrix.trace ((edgeOutput u v a b x)ᴴ * edgeOutput u' v' a b y) = 0 := by
  unfold edgeOutput
  by_cases hx : x u = x v
  · rw [if_pos hx]; simp
  by_cases hy : y u' = y v'
  · rw [if_neg hx, if_pos hy]; simp
  rw [if_neg hx, if_neg hy, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  refine trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix_eq_zero _ _ (w := w) ?_
  rw [edgeOutputLocal_outside a b y hw' hw'']
  rcases hw with hwu | hwv
  · subst hwu
    rw [edgeOutputLocal_left_eq]
    exact trace_conjTranspose_localDiffLetter_mul_swapRaw _ _ _
  · subst hwv
    rw [edgeOutputLocal_right_eq huv]
    exact trace_conjTranspose_localDiffLetter_mul_swapRaw _ _ _

theorem trace_conjTranspose_edgeOutput_mul_edgeOutput_of_outside'
    {u v u' v' : V} (hu'v' : u' ≠ v') (a b : Fin 3) {w : V}
    (hw : w ≠ u) (hw' : w ≠ v) (hw'' : w = u' ∨ w = v') (x y : V → Bool) :
    Matrix.trace ((edgeOutput u v a b x)ᴴ * edgeOutput u' v' a b y) = 0 := by
  unfold edgeOutput
  by_cases hx : x u = x v
  · rw [if_pos hx]; simp
  by_cases hy : y u' = y v'
  · rw [if_neg hx, if_pos hy]; simp
  rw [if_neg hx, if_neg hy, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  refine trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix_eq_zero _ _ (w := w) ?_
  rw [edgeOutputLocal_outside a b x hw hw']
  rcases hw'' with hwu | hwv
  · subst hwu
    rw [edgeOutputLocal_left_eq]
    exact trace_conjTranspose_swapRaw_mul_localDiffLetter _ _ _
  · subst hwv
    rw [edgeOutputLocal_right_eq hu'v']
    exact trace_conjTranspose_swapRaw_mul_localDiffLetter _ _ _

/-- **Distinct edges give orthogonal defect sectors.** -/
theorem trace_conjTranspose_edgeOutput_mul_edgeOutput_cross
    {u v u' v' : V} (huv : u ≠ v) (hu'v' : u' ≠ v') (a b : Fin 3)
    (hsep : ∃ w : V, ((w = u ∨ w = v) ∧ ¬(w = u' ∨ w = v')) ∨
      (¬(w = u ∨ w = v) ∧ (w = u' ∨ w = v'))) (x y : V → Bool) :
    Matrix.trace ((edgeOutput u v a b x)ᴴ * edgeOutput u' v' a b y) = 0 := by
  obtain ⟨w, hw⟩ := hsep
  rcases hw with ⟨hin, hout⟩ | ⟨hout, hin⟩
  · exact trace_conjTranspose_edgeOutput_mul_edgeOutput_of_outside huv a b hin
      (fun h => hout (Or.inl h)) (fun h => hout (Or.inr h)) x y
  · exact trace_conjTranspose_edgeOutput_mul_edgeOutput_of_outside' hu'v' a b
      (fun h => hout (Or.inl h)) (fun h => hout (Or.inr h)) hin x y

/-- **Opposite mismatch types on one edge give orthogonal outputs.** -/
theorem trace_conjTranspose_edgeOutput_mul_edgeOutput_of_ne_left
    {u v : V} (a b : Fin 3) {x y : V → Bool} (hxy : x u ≠ y u) :
    Matrix.trace ((edgeOutput u v a b x)ᴴ * edgeOutput u v a b y) = 0 := by
  unfold edgeOutput
  by_cases hx : x u = x v
  · rw [if_pos hx]; simp
  by_cases hy : y u = y v
  · rw [if_neg hx, if_pos hy]; simp
  rw [if_neg hx, if_neg hy, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  refine trace_conjTranspose_mul_finiteTwoReplicaLocalMatrix_eq_zero _ _ (w := u) ?_
  rw [edgeOutputLocal_left_eq, edgeOutputLocal_left_eq]
  exact trace_conjTranspose_localDiffLetter_mul_of_ne hxy a

/-- Hilbert–Schmidt orthogonality passes to linear combinations. -/
theorem trace_conjTranspose_sum_mul_sum_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    {m : Type*} [Fintype m] (c : ι → ℂ) (d : κ → ℂ) (A : ι → Matrix m m ℂ) (B : κ → Matrix m m ℂ)
    (h : ∀ i j, c i ≠ 0 → d j ≠ 0 → Matrix.trace ((A i)ᴴ * B j) = 0) :
    Matrix.trace ((∑ i, c i • A i)ᴴ * (∑ j, d j • B j)) = 0 := by
  rw [Matrix.conjTranspose_sum, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hc : c i = 0
  · simp [hc]
  by_cases hd : d j = 0
  · simp [hd]
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul, h i j hc hd]
  simp

/-! ### Reading the identity/swap word back off one mismatch type -/

/-- Overwrite the two endpoint letters of a two-replica configuration. -/
def setEndpoints (u v : V) (X : FiniteTwoReplicaConfiguration V) (P : TwoReplicaEdgeIndex) :
    FiniteTwoReplicaConfiguration V :=
  (fun w => if w = u then P.1.1 else if w = v then P.2.1 else X.1 w,
   fun w => if w = u then P.1.2 else if w = v then P.2.2 else X.2 w)

omit [Fintype V] in
theorem setEndpoints_left (u v : V) (X : FiniteTwoReplicaConfiguration V)
    (P : TwoReplicaEdgeIndex) :
    ((setEndpoints u v X P).1 u, (setEndpoints u v X P).2 u) = P.1 := by
  simp [setEndpoints]

omit [Fintype V] in
theorem setEndpoints_right {u v : V} (huv : u ≠ v) (X : FiniteTwoReplicaConfiguration V)
    (P : TwoReplicaEdgeIndex) :
    ((setEndpoints u v X P).1 v, (setEndpoints u v X P).2 v) = P.2 := by
  simp [setEndpoints, huv.symm]

omit [Fintype V] in
theorem setEndpoints_outside {u v : V} (X : FiniteTwoReplicaConfiguration V)
    (P : TwoReplicaEdgeIndex) {w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    ((setEndpoints u v X P).1 w, (setEndpoints u v X P).2 w) = (X.1 w, X.2 w) := by
  simp [setEndpoints, hwu, hwv]

/-- The endpoint-evaluation reader that recovers the identity/swap word of one mismatch type. -/
def edgeReader (u v : V) (su sv : Bool) (P Q : TwoReplicaEdgeIndex) (kap : ℂ) :
    FiniteTwoReplicaMatrix V →ₗ[ℂ] FiniteTwoReplicaMatrix V where
  toFun M := Matrix.of fun X Z =>
    kap⁻¹ * twoReplicaLocalSwapRaw su (X.1 u, X.2 u) (Z.1 u, Z.2 u)
      * twoReplicaLocalSwapRaw sv (X.1 v, X.2 v) (Z.1 v, Z.2 v)
      * M (setEndpoints u v X P) (setEndpoints u v Z Q)
  map_add' M N := by
    ext X Z
    simp only [Matrix.of_apply, Matrix.add_apply]
    ring
  map_smul' r M := by
    ext X Z
    simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The reader turns a type-matched edge output back into its identity/swap word. -/
theorem edgeReader_edgeOutput {u v : V} (huv : u ≠ v) (a b : Fin 3) {su sv : Bool}
    (P Q : TwoReplicaEdgeIndex) (hsu : su ≠ sv)
    (hkap : localDiffLetter su a P.1 Q.1 * localDiffLetter sv b P.2 Q.2 ≠ 0)
    (x : V → Bool) (hxu : x u = su) (hxv : x v = sv) :
    edgeReader u v su sv P Q (localDiffLetter su a P.1 Q.1 * localDiffLetter sv b P.2 Q.2)
        (edgeOutput u v a b x) = -finiteTwoReplicaSwapRaw x := by
  have hmis : ¬ (x u = x v) := by rw [hxu, hxv]; exact hsu
  ext X Z
  simp only [edgeReader, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, edgeOutput,
    if_neg hmis, Matrix.neg_apply, Matrix.neg_apply]
  rw [finiteTwoReplicaLocalMatrix, finiteTwoReplicaSwapRaw, finiteTwoReplicaLocalMatrix]
  have hsplit1 : (∏ w, edgeOutputLocal u v a b x w
        ((setEndpoints u v X P).1 w, (setEndpoints u v X P).2 w)
        ((setEndpoints u v Z Q).1 w, (setEndpoints u v Z Q).2 w))
      = (localDiffLetter su a P.1 Q.1 * localDiffLetter sv b P.2 Q.2)
        * ∏ w : FiniteTwoReplicaEdgeOutside u v,
            twoReplicaLocalSwapRaw (x w.1) (X.1 w.1, X.2 w.1) (Z.1 w.1, Z.2 w.1) := by
    rw [finite_prod_eq_edge_mul_outside huv]
    rw [setEndpoints_left, setEndpoints_right huv, setEndpoints_left, setEndpoints_right huv,
      edgeOutputLocal_left_eq, edgeOutputLocal_right_eq huv, hxu, hxv]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [setEndpoints_outside X P w.2.1 w.2.2, setEndpoints_outside Z Q w.2.1 w.2.2,
      edgeOutputLocal_outside a b x w.2.1 w.2.2]
  have hsplit2 : (∏ w, twoReplicaLocalSwapRaw (x w) (X.1 w, X.2 w) (Z.1 w, Z.2 w))
      = twoReplicaLocalSwapRaw su (X.1 u, X.2 u) (Z.1 u, Z.2 u)
        * twoReplicaLocalSwapRaw sv (X.1 v, X.2 v) (Z.1 v, Z.2 v)
        * ∏ w : FiniteTwoReplicaEdgeOutside u v,
            twoReplicaLocalSwapRaw (x w.1) (X.1 w.1, X.2 w.1) (Z.1 w.1, Z.2 w.1) := by
    rw [finite_prod_eq_edge_mul_outside huv, hxu, hxv]
  have h1 : localDiffLetter su a P.1 Q.1 ≠ 0 := left_ne_zero_of_mul hkap
  have h2 : localDiffLetter sv b P.2 Q.2 ≠ 0 := right_ne_zero_of_mul hkap
  rw [hsplit1, hsplit2]
  field_simp


/-! ### The mismatch kernel of one fixed-orientation edge commutator -/

/-- The fixed-orientation edge commutator read on identity/swap coefficients. -/
def edgeCommutatorCoeff (u v : V) (a b : Fin 3) :
    TwoReplicaGlobalCoeff V →ₗ[ℂ] FiniteTwoReplicaMatrix V :=
  (finiteTwoReplicaCollectiveCommutatorLinear (finiteEdgePauliLabel u v a b)).comp
    finiteTwoReplicaSwapInvariantEmbed

theorem edgeCommutatorCoeff_eq_sum {u v : V} (huv : u ≠ v) (a b : Fin 3)
    (c : TwoReplicaGlobalCoeff V) :
    edgeCommutatorCoeff u v a b c = ∑ x : V → Bool, c x • edgeOutput u v a b x := by
  show finiteTwoReplicaCollectiveCommutatorLinear (finiteEdgePauliLabel u v a b)
      (finiteTwoReplicaSwapInvariantEmbed c) = _
  have hembed : finiteTwoReplicaSwapInvariantEmbed c
      = ∑ x : V → Bool, c x • finiteTwoReplicaSwapRaw x := rfl
  rw [hembed, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, finiteTwoReplicaCollectiveCommutator_swapRaw_eq_edgeOutput huv]

theorem edgeCommutatorCoeff_eq_zero_of_matched {u v : V} (huv : u ≠ v) (a b : Fin 3)
    {c : TwoReplicaGlobalCoeff V} (hc : ∀ x : V → Bool, x u ≠ x v → c x = 0) :
    edgeCommutatorCoeff u v a b c = 0 := by
  rw [edgeCommutatorCoeff_eq_sum huv]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x u = x v
  · rw [edgeOutput, if_pos hx, smul_zero]
  · rw [hc x hx, zero_smul]

/-- **Equation (12).**  One fixed-orientation edge commutator annihilates exactly the words that
match on its own edge: its kernel on the sitewise singlet algebra is the kernel of the mismatch
projection, no larger. -/
theorem edgeCommutatorCoeff_eq_zero_iff {u v : V} (huv : u ≠ v) (a b : Fin 3)
    (c : TwoReplicaGlobalCoeff V) :
    edgeCommutatorCoeff u v a b c = 0 ↔ ∀ x : V → Bool, x u ≠ x v → c x = 0 := by
  classical
  refine ⟨fun h => ?_, edgeCommutatorCoeff_eq_zero_of_matched huv a b⟩
  set cL : TwoReplicaGlobalCoeff V := fun y => if y u = false ∧ y v = true then c y else 0 with hcL
  set cR : TwoReplicaGlobalCoeff V := fun y => if y u = true ∧ y v = false then c y else 0 with hcR
  set SL : FiniteTwoReplicaMatrix V := ∑ y : V → Bool, cL y • edgeOutput u v a b y with hSL
  set SR : FiniteTwoReplicaMatrix V := ∑ y : V → Bool, cR y • edgeOutput u v a b y with hSR
  have hmisL : ∀ y : V → Bool, cL y ≠ 0 → y u = false ∧ y v = true := by
    intro y hy
    by_contra hcon
    exact hy (by simp only [hcL]; exact if_neg hcon)
  have hmisR : ∀ y : V → Bool, cR y ≠ 0 → y u = true ∧ y v = false := by
    intro y hy
    by_contra hcon
    exact hy (by simp only [hcR]; exact if_neg hcon)
  have hsplit : SL + SR = edgeCommutatorCoeff u v a b c := by
    rw [edgeCommutatorCoeff_eq_sum huv, hSL, hSR, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y u = y v
    · rw [edgeOutput, if_pos hy]; simp
    · simp only [hcL, hcR]
      rcases hyu : y u with _ | _
      · have hyv : y v = true := by
          rcases hb : y v with _ | _
          · exact absurd (hyu.trans hb.symm) hy
          · rfl
        simp [hyv]
      · have hyv : y v = false := by
          rcases hb : y v with _ | _
          · rfl
          · exact absurd (hyu.trans hb.symm) hy
        simp [hyv]
  have hzero : SL + SR = 0 := by rw [hsplit, h]
  have horthoLR : Matrix.trace (SLᴴ * SR) = 0 := by
    rw [hSL, hSR]
    refine trace_conjTranspose_sum_mul_sum_eq_zero _ _ _ _ fun y z hy hz => ?_
    refine trace_conjTranspose_edgeOutput_mul_edgeOutput_of_ne_left a b ?_
    rw [(hmisL y hy).1, (hmisR z hz).1]
    simp
  have horthoRL : Matrix.trace (SRᴴ * SL) = 0 := by
    rw [hSL, hSR]
    refine trace_conjTranspose_sum_mul_sum_eq_zero _ _ _ _ fun y z hy hz => ?_
    refine trace_conjTranspose_edgeOutput_mul_edgeOutput_of_ne_left a b ?_
    rw [(hmisR y hy).1, (hmisL z hz).1]
    simp
  have hSLzero : SL = 0 := by
    refine eq_zero_of_trace_conjTranspose_mul_self ?_
    have hstep := congrArg (fun M => Matrix.trace (SLᴴ * M)) hzero
    simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_zero, Matrix.trace_zero] at hstep
    linear_combination hstep - horthoLR
  have hSRzero : SR = 0 := by
    refine eq_zero_of_trace_conjTranspose_mul_self ?_
    have hstep := congrArg (fun M => Matrix.trace (SRᴴ * M)) hzero
    simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_zero, Matrix.trace_zero] at hstep
    linear_combination hstep - horthoRL
  obtain ⟨i1, j1, h1⟩ := exists_localDiffLetter_ne_zero false a
  obtain ⟨i2, j2, h2⟩ := exists_localDiffLetter_ne_zero true b
  obtain ⟨i3, j3, h3⟩ := exists_localDiffLetter_ne_zero true a
  obtain ⟨i4, j4, h4⟩ := exists_localDiffLetter_ne_zero false b
  have hcLzero : cL = 0 := by
    have hread : edgeReader u v false true (i1, i2) (j1, j2)
        (localDiffLetter false a i1 j1 * localDiffLetter true b i2 j2) SL
        = -finiteTwoReplicaSwapInvariantEmbed cL := by
      rw [hSL, map_sum]
      have hterm : ∀ y : V → Bool, edgeReader u v false true (i1, i2) (j1, j2)
          (localDiffLetter false a i1 j1 * localDiffLetter true b i2 j2) (cL y • edgeOutput u v a b y)
          = cL y • (-finiteTwoReplicaSwapRaw y) := by
        intro y
        rw [map_smul]
        by_cases hy : cL y = 0
        · rw [hy, zero_smul, zero_smul]
        · rw [edgeReader_edgeOutput huv a b (i1, i2) (j1, j2) (by simp)
            (mul_ne_zero h1 h2) y (hmisL y hy).1 (hmisL y hy).2]
      rw [Finset.sum_congr rfl fun y _ => hterm y]
      have hembed : finiteTwoReplicaSwapInvariantEmbed cL
          = ∑ y : V → Bool, cL y • finiteTwoReplicaSwapRaw y := rfl
      rw [hembed, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_neg]
    rw [hSLzero, map_zero] at hread
    have : finiteTwoReplicaSwapInvariantEmbed cL = 0 := by
      have := hread.symm
      rwa [neg_eq_zero] at this
    exact finiteTwoReplicaSwapInvariantEmbed_injective (by rw [this, map_zero])
  have hcRzero : cR = 0 := by
    have hread : edgeReader u v true false (i3, i4) (j3, j4)
        (localDiffLetter true a i3 j3 * localDiffLetter false b i4 j4) SR
        = -finiteTwoReplicaSwapInvariantEmbed cR := by
      rw [hSR, map_sum]
      have hterm : ∀ y : V → Bool, edgeReader u v true false (i3, i4) (j3, j4)
          (localDiffLetter true a i3 j3 * localDiffLetter false b i4 j4) (cR y • edgeOutput u v a b y)
          = cR y • (-finiteTwoReplicaSwapRaw y) := by
        intro y
        rw [map_smul]
        by_cases hy : cR y = 0
        · rw [hy, zero_smul, zero_smul]
        · rw [edgeReader_edgeOutput huv a b (i3, i4) (j3, j4) (by simp)
            (mul_ne_zero h3 h4) y (hmisR y hy).1 (hmisR y hy).2]
      rw [Finset.sum_congr rfl fun y _ => hterm y]
      have hembed : finiteTwoReplicaSwapInvariantEmbed cR
          = ∑ y : V → Bool, cR y • finiteTwoReplicaSwapRaw y := rfl
      rw [hembed, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun y _ => by rw [smul_neg]
    rw [hSRzero, map_zero] at hread
    have : finiteTwoReplicaSwapInvariantEmbed cR = 0 := by
      have := hread.symm
      rwa [neg_eq_zero] at this
    exact finiteTwoReplicaSwapInvariantEmbed_injective (by rw [this, map_zero])
  intro x hx
  rcases hxu : x u with _ | _
  · have hxv : x v = true := by
      rcases hb : x v with _ | _
      · exact absurd (hxu.trans hb.symm) hx
      · rfl
    have hval := congrFun hcLzero x
    simp only [hcL, hxu, hxv, and_self, if_pos, Pi.zero_apply] at hval
    exact hval
  · have hxv : x v = false := by
      rcases hb : x v with _ | _
      · rfl
      · exact absurd (hxu.trans hb.symm) hx
    have hval := congrFun hcRzero x
    simp only [hcR, hxu, hxv, and_self, if_pos, Pi.zero_apply] at hval
    exact hval

/-! ### The Hall inequality -/

/-- **Equation (4).**  A single Pauli orientation per edge expands every subspace of the sitewise
singlet algebra whose only vector with all-edge-matched coordinates is zero.  The three inputs are
faithfulness of the stacked mismatch projections, injectivity of each edge commutator on its own
mismatch fibre, and Hilbert–Schmidt orthogonality of distinct edge-defect sectors. -/
theorem twoReplicaEdgeHallExpansion
    {J : Type*} [Fintype J] [DecidableEq J]
    {uu vv : J → V} (a b : Fin 3)
    (hne : ∀ j, uu j ≠ vv j)
    (hsep : ∀ j k, j ≠ k → ∃ w : V,
      ((w = uu j ∨ w = vv j) ∧ ¬(w = uu k ∨ w = vv k)) ∨
      (¬(w = uu j ∨ w = vv j) ∧ (w = uu k ∨ w = vv k)))
    (U : Submodule ℂ (TwoReplicaGlobalCoeff V))
    (hU : ∀ c ∈ U, (∀ j, ∀ x : V → Bool, x (uu j) ≠ x (vv j) → c x = 0) → c = 0) :
    Module.finrank ℂ U
      ≤ Module.finrank ℂ
          (⨆ j : J, Submodule.map (edgeCommutatorCoeff (uu j) (vv j) a b) U :
            Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
  classical
  set W : Submodule ℂ (FiniteTwoReplicaMatrix V) :=
    ⨆ j : J, Submodule.map (edgeCommutatorCoeff (uu j) (vv j) a b) U with hW
  set G : TwoReplicaGlobalCoeff V →ₗ[ℂ] FiniteTwoReplicaMatrix V :=
    ∑ j, edgeCommutatorCoeff (uu j) (vv j) a b with hG
  have hGapply : ∀ c, G c = ∑ j, edgeCommutatorCoeff (uu j) (vv j) a b c := by
    intro c; rw [hG, LinearMap.sum_apply]
  have hmem : ∀ c ∈ U, G c ∈ W := by
    intro c hc
    rw [hGapply]
    refine Submodule.sum_mem W fun j _ => ?_
    exact Submodule.mem_iSup_of_mem j ⟨c, hc, rfl⟩
  have hker : ∀ c ∈ U, G c = 0 → c = 0 := by
    intro c hc hGc
    refine hU c hc fun j x hx => ?_
    have hterm : edgeCommutatorCoeff (uu j) (vv j) a b c = 0 := by
      refine eq_zero_of_trace_conjTranspose_mul_self ?_
      have hpair : ∀ k, k ≠ j →
          Matrix.trace ((edgeCommutatorCoeff (uu j) (vv j) a b c)ᴴ *
            edgeCommutatorCoeff (uu k) (vv k) a b c) = 0 := by
        intro k hk
        rw [edgeCommutatorCoeff_eq_sum (hne j), edgeCommutatorCoeff_eq_sum (hne k)]
        refine trace_conjTranspose_sum_mul_sum_eq_zero _ _ _ _ fun y z _ _ => ?_
        exact trace_conjTranspose_edgeOutput_mul_edgeOutput_cross (hne j) (hne k) a b
          (hsep j k (Ne.symm hk)) y z
      have hstep := congrArg
        (fun M => Matrix.trace ((edgeCommutatorCoeff (uu j) (vv j) a b c)ᴴ * M)) hGc
      simp only [hGapply, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_zero,
        Matrix.trace_zero] at hstep
      rw [Finset.sum_eq_single j] at hstep
      · exact hstep
      · intro k _ hk; exact hpair k hk
      · intro hj; exact absurd (Finset.mem_univ j) hj
    exact (edgeCommutatorCoeff_eq_zero_iff (hne j) a b c).mp hterm x hx
  let F : U →ₗ[ℂ] W := (G.domRestrict U).codRestrict W fun x => hmem x.1 x.2
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx0 : G x.1 = 0 := congrArg Subtype.val hx
    exact Subtype.ext (hker x.1 x.2 hx0)
  exact F.finrank_le_finrank_of_injective hF


/-- **Equation (4) on a connected interaction graph.**  For a connected graph the only
all-edge-matched identity/swap coefficients are the global identity and the global replica swap,
so the transversality hypothesis becomes `Ũ ∩ 𝒢₂ = 0`. -/
theorem twoReplicaEdgeHallExpansion_connected
    {J : Type*} [Fintype J] [DecidableEq J] [Nonempty V]
    {G : SimpleGraph V} (hG : G.Preconnected)
    {uu vv : J → V} (a b : Fin 3)
    (hne : ∀ j, uu j ≠ vv j)
    (hsep : ∀ j k, j ≠ k → ∃ w : V,
      ((w = uu j ∨ w = vv j) ∧ ¬(w = uu k ∨ w = vv k)) ∨
      (¬(w = uu j ∨ w = vv j) ∧ (w = uu k ∨ w = vv k)))
    (hcover : ∀ u v : V, G.Adj u v → ∃ j, (uu j = u ∧ vv j = v) ∨ (uu j = v ∧ vv j = u))
    (U : Submodule ℂ (TwoReplicaGlobalCoeff V))
    (hU : ∀ c ∈ U, ∀ p q : ℂ, c = twoReplicaGlobalSynchronizedCoeff p q → c = 0) :
    Module.finrank ℂ U
      ≤ Module.finrank ℂ
          (⨆ j : J, Submodule.map (edgeCommutatorCoeff (uu j) (vv j) a b) U :
            Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
  refine twoReplicaEdgeHallExpansion a b hne hsep U fun c hc hmatch => ?_
  have hall : ∀ ⦃u v : V⦄, G.Adj u v → ∀ x : V → Bool, x u ≠ x v → c x = 0 := by
    intro u v huv x hx
    obtain ⟨j, hj⟩ := hcover u v huv
    rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hmatch j x (by rw [h1, h2]; exact hx)
    · exact hmatch j x (by rw [h1, h2]; exact hx.symm)
  obtain ⟨p, q, hpq⟩ := (twoReplicaGlobal_edgeMismatch_zero_iff hG c).mp hall
  exact hU c hc p q hpq

end

end GaloisForLFunctions.HTGeometry
