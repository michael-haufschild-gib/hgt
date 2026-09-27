import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeDegree

/-!
# The three-part decomposition restricted to stable subspaces

The canonical pieces `B(S)` (forward bounded), `C(S)` (backward contracting) and
`N(S) = B(S) ⊓ B(S⁻¹)` (neutral) of a uniformizer-semilinear automorphism `S` cut every `S`-stable
subspace `W` compatibly:

* `DiffOp.inf_sup_inf_eq_of_invariant` — `W = (W ⊓ B(S)) ⊕ (W ⊓ C(S))`.  Write `w = b + c` in `E`;
  in the quotient `E ⧸ W` the image of `b` is both forward bounded and backward contracting for the
  induced automorphism, so it vanishes by the three-part theorem applied to the quotient space.
* `DiffOp.exists_stable_lattice_of_le_neutral` — every stable subspace of the neutral part carries a
  lattice `L` with `S L = L`: the vectors whose two-sided orbit stays in one finitely generated
  submodule.
* Degrees of the pieces: positive on `W ⊓ C(S)`, zero on `W ⊓ N(S)`, negative on `W ⊓ C(S⁻¹)` whenever
  the piece is nonzero (`DiffOp.semilinearDegree_pos_backwardContracting` and companions).
* The pieces of `S` are unchanged by passing to a power of `S`, and are preserved by every
  automorphism commuting with `S`.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]

variable {S T : E ≃ₗ[ℤ] E}

section Quotient

variable (hS : IsUniformizerSemilinear (K := K) S) {W : Submodule (CompletedPseudoDiffOp K) E}
  (hW : ∀ x ∈ W, S x ∈ W) (hW' : ∀ x ∈ W, S⁻¹ x ∈ W)

theorem quotientSemilinearAut_inv_mk (x : E) :
    (quotientSemilinearAut hS W hW hW')⁻¹ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (S⁻¹ x) :=
  Submodule.mapQ_apply W W hS.inv.semilinearMap (h := hW') x

theorem quotientSemilinearAut_inv_pow_mk (n : ℕ) (x : E) :
    ((quotientSemilinearAut hS W hW hW')⁻¹ ^ n) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((S⁻¹ ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, quotientSemilinearAut_inv_mk, pow_succ',
        LinearEquiv.mul_apply]

theorem mk_mem_uniformizerDilate_map {k : ℤ} {M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}
    {y : E} (hy : y ∈ uniformizerDilate k M) :
    (Submodule.Quotient.mk y : E ⧸ W) ∈ uniformizerDilate k
      (M.map (W.mkQ.restrictScalars (CompletedPseudoDiffOpInteger (K := K)))) := by
  obtain ⟨m, hm, rfl⟩ := mem_uniformizerDilate_iff_exists.1 hy
  rw [Submodule.Quotient.mk_smul]
  exact smul_mem_uniformizerDilate k (Submodule.mem_map_of_mem hm)

theorem mk_mem_forwardBoundedSubspace_quotient {x : E} (hx : x ∈ forwardBoundedSubspace S hS) :
    (Submodule.Quotient.mk x : E ⧸ W) ∈ forwardBoundedSubspace (quotientSemilinearAut hS W hW hW')
      (isUniformizerSemilinear_quotientSemilinearAut hS hW hW') := by
  obtain ⟨M, hM, hMx⟩ := mem_forwardBoundedSubspace.1 hx
  refine mem_forwardBoundedSubspace.2 ⟨_,
    hM.map (W.mkQ.restrictScalars (CompletedPseudoDiffOpInteger (K := K))), fun n => ?_⟩
  rw [quotientSemilinearAut_pow_mk]
  exact Submodule.mem_map_of_mem (hMx n)

theorem mk_mem_backwardContractingSubspace_quotient {x : E}
    (hx : x ∈ backwardContractingSubspace S hS) :
    (Submodule.Quotient.mk x : E ⧸ W) ∈ backwardContractingSubspace
      (quotientSemilinearAut hS W hW hW')
      (isUniformizerSemilinear_quotientSemilinearAut hS hW hW') := by
  obtain ⟨M, hM, hMx⟩ := mem_backwardContractingSubspace.1 hx
  refine mem_backwardContractingSubspace.2 ⟨_,
    hM.map (W.mkQ.restrictScalars (CompletedPseudoDiffOpInteger (K := K))), fun k => ?_⟩
  filter_upwards [hMx k] with n hn
  rw [quotientSemilinearAut_inv_pow_mk]
  exact mk_mem_uniformizerDilate_map hn

end Quotient

variable [FiniteDimensional (CompletedPseudoDiffOp K) E]

/-- **The forward-bounded / backward-contracting splitting of a stable subspace.** -/
theorem inf_sup_inf_eq_of_invariant (hS : IsUniformizerSemilinear (K := K) S)
    {W : Submodule (CompletedPseudoDiffOp K) E} (hW : ∀ x ∈ W, S x ∈ W)
    (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) :
    (W ⊓ forwardBoundedSubspace S hS) ⊔ (W ⊓ backwardContractingSubspace S hS) = W := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hxW => ?_
  have htop := forwardBoundedSubspace_sup_backwardContractingSubspace_eq_top hS
  have hx : x ∈ forwardBoundedSubspace S hS ⊔ backwardContractingSubspace S hS := by
    rw [htop]
    trivial
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
  have hbW : b ∈ W := by
    have hq := backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot
      (isUniformizerSemilinear_quotientSemilinearAut hS hW hW')
    have hmk : (Submodule.Quotient.mk b : E ⧸ W) = -Submodule.Quotient.mk c := by
      rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
      exact hxW
    have hmem : (Submodule.Quotient.mk b : E ⧸ W) ∈
        backwardContractingSubspace _ (isUniformizerSemilinear_quotientSemilinearAut hS hW hW') ⊓
          forwardBoundedSubspace _ (isUniformizerSemilinear_quotientSemilinearAut hS hW hW') := by
      refine ⟨?_, mk_mem_forwardBoundedSubspace_quotient hS hW hW' hb⟩
      rw [hmk]
      exact Submodule.neg_mem _ (mk_mem_backwardContractingSubspace_quotient hS hW hW' hc)
    rw [hq, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  have hcW : c ∈ W := by
    have := Submodule.sub_mem _ hxW hbW
    rwa [add_sub_cancel_left] at this
  exact Submodule.add_mem_sup ⟨hbW, hb⟩ ⟨hcW, hc⟩

/-- **Neutral splitting of a stable subspace.** -/
theorem inf_neutral_sup_inf_eq_of_invariant (hS : IsUniformizerSemilinear (K := K) S)
    {W : Submodule (CompletedPseudoDiffOp K) E} (hW : ∀ x ∈ W, S x ∈ W)
    (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) :
    (W ⊓ (forwardBoundedSubspace S hS ⊓ forwardBoundedSubspace S⁻¹ hS.inv)) ⊔
      (W ⊓ backwardContractingSubspace S⁻¹ hS.inv) = W ⊓ forwardBoundedSubspace S hS := by
  have hB : ∀ x ∈ W ⊓ forwardBoundedSubspace S hS, S⁻¹ x ∈ W ⊓ forwardBoundedSubspace S hS :=
    fun x hx => ⟨hW' x hx.1, inv_apply_mem_forwardBoundedSubspace hS hx.2⟩
  have hB' : ∀ x ∈ W ⊓ forwardBoundedSubspace S hS,
      S⁻¹⁻¹ x ∈ W ⊓ forwardBoundedSubspace S hS := fun x hx => by
    rw [inv_inv]
    exact ⟨hW x hx.1, apply_mem_forwardBoundedSubspace hx.2⟩
  have h := inf_sup_inf_eq_of_invariant hS.inv hB hB'
  have hCB : backwardContractingSubspace S⁻¹ hS.inv ≤ forwardBoundedSubspace S hS :=
    backwardContractingSubspace_inv_le_forwardBoundedSubspace hS
  rw [inf_assoc, inf_assoc, inf_eq_right.2 hCB] at h
  exact h

/-- **A stable lattice of a neutral stable subspace.**  Every subspace of the neutral part that is
stable under `S` and `S⁻¹` carries a lattice `L` with `S L = L`. -/
theorem exists_stable_lattice_of_le_neutral (hS : IsUniformizerSemilinear (K := K) S)
    {V : Submodule (CompletedPseudoDiffOp K) E} (hV : ∀ x ∈ V, S x ∈ V) (hV' : ∀ x ∈ V, S⁻¹ x ∈ V)
    (hVN : V ≤ forwardBoundedSubspace S hS ⊓ forwardBoundedSubspace S⁻¹ hS.inv) :
    ∃ L : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, IsLatticeOf L V ∧
      semilinearImage S hS L = L := by
  classical
  obtain ⟨d, e, c, he, hsum, hδ⟩ := exists_coordinates V
  have hfwd : ∀ i, ∃ M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, M.FG ∧
      ∀ n : ℕ, (S ^ n) (e i) ∈ M := fun i => mem_forwardBoundedSubspace.1 (hVN (he i)).1
  have hbwd : ∀ i, ∃ M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, M.FG ∧
      ∀ n : ℕ, (S⁻¹ ^ n) (e i) ∈ M := fun i => mem_forwardBoundedSubspace.1 (hVN (he i)).2
  choose Mf hMf hMfe using hfwd
  choose Mb hMb hMbe using hbwd
  set M := (⨆ i, Mf i) ⊔ ⨆ i, Mb i with hMdef
  have hMfg : M.FG := (Submodule.fg_iSup _ hMf).sup (Submodule.fg_iSup _ hMb)
  let L : Submodule (CompletedPseudoDiffOpInteger (K := K)) E :=
    orbitConfined hS M ⊓ orbitConfined hS.inv M ⊓
      V.restrictScalars (CompletedPseudoDiffOpInteger (K := K))
  have hLM : L ≤ M := inf_le_left.trans (inf_le_left.trans (orbitConfined_le hS))
  have hΛL : Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) ≤ L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨fun n => ?_, fun n => ?_⟩, he i⟩
    · exact Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i (hMfe i n))
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i (hMbe i n))
  have hLV : L ≤ V.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := inf_le_right
  have hlat : IsLatticeOf L V := by
    refine ⟨hMfg.of_le hLM, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      exact fun x hx => hLV hx
    · rw [← span_span_range_eq he hsum]
      exact Submodule.span_mono hΛL
  have hSL : ∀ y ∈ L, S y ∈ L := by
    rintro y ⟨⟨hf, hb⟩, hy⟩
    refine ⟨⟨apply_mem_orbitConfined hS hf, fun n => ?_⟩, hV y hy⟩
    cases n with
    | zero =>
        rw [pow_zero, LinearEquiv.coe_one, id]
        have := hf 1
        rwa [pow_one] at this
    | succ n =>
        rw [pow_succ, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply S⁻¹, inv_mul_cancel,
          LinearEquiv.coe_one, id]
        exact hb n
  have hSL' : ∀ y ∈ L, S⁻¹ y ∈ L := by
    rintro y ⟨⟨hf, hb⟩, hy⟩
    refine ⟨⟨fun n => ?_, apply_mem_orbitConfined hS.inv hb⟩, hV' y hy⟩
    cases n with
    | zero =>
        rw [pow_zero, LinearEquiv.coe_one, id]
        have := hb 1
        rwa [pow_one] at this
    | succ n =>
        rw [pow_succ, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply S, mul_inv_cancel,
          LinearEquiv.coe_one, id]
        exact hf n
  refine ⟨L, hlat, le_antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
    exact hSL x hx
  · intro y hy
    rw [mem_semilinearImage]
    exact hSL' y hy

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- An automorphism commuting with `S` preserves its forward-bounded subspace. -/
theorem apply_mem_forwardBoundedSubspace_of_commute (hS : IsUniformizerSemilinear (K := K) S)
    (hT : IsUniformizerSemilinear (K := K) T) (hc : Commute T S) {x : E}
    (hx : x ∈ forwardBoundedSubspace S hS) : T x ∈ forwardBoundedSubspace S hS := by
  obtain ⟨M, hM, hMx⟩ := mem_forwardBoundedSubspace.1 hx
  refine mem_forwardBoundedSubspace.2 ⟨semilinearImage T hT M, semilinearImage_fg hM,
    fun n => ?_⟩
  rw [← LinearEquiv.mul_apply, ← (hc.pow_right n).eq, LinearEquiv.mul_apply]
  exact apply_mem_semilinearImage (hMx n)

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- An automorphism commuting with `S` preserves its backward-contracting subspace. -/
theorem apply_mem_backwardContractingSubspace_of_commute (hS : IsUniformizerSemilinear (K := K) S)
    (hT : IsUniformizerSemilinear (K := K) T) (hc : Commute T S) {x : E}
    (hx : x ∈ backwardContractingSubspace S hS) : T x ∈ backwardContractingSubspace S hS := by
  obtain ⟨M, hM, hMx⟩ := mem_backwardContractingSubspace.1 hx
  refine mem_backwardContractingSubspace.2 ⟨semilinearImage T hT M, semilinearImage_fg hM,
    fun k => ?_⟩
  filter_upwards [hMx k] with n hn
  rw [← LinearEquiv.mul_apply, ← (hc.inv_right.pow_right n).eq, LinearEquiv.mul_apply,
    ← semilinearImage_uniformizerDilate]
  exact apply_mem_semilinearImage hn

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Passing to a positive power does not change the forward-bounded subspace. -/
theorem forwardBoundedSubspace_pow (hS : IsUniformizerSemilinear (K := K) S) {k : ℕ} (hk : 1 ≤ k) :
    forwardBoundedSubspace (S ^ k) (hS.pow k) = forwardBoundedSubspace S hS := by
  ext x
  rw [mem_forwardBoundedSubspace, mem_forwardBoundedSubspace]
  constructor
  · rintro ⟨M, hM, hMx⟩
    refine ⟨forwardHull hS M (k - 1), forwardHull_fg hS hM (k - 1), fun n => ?_⟩
    have hn : S ^ n = S ^ (n % k) * (S ^ k) ^ (n / k) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hn, LinearEquiv.mul_apply]
    have hr : n % k ≤ k - 1 := by
      have := Nat.mod_lt n (show 0 < k by omega)
      omega
    exact pow_apply_mem_forwardHull hS (k - 1) (n % k) hr _ (hMx (n / k))
  · rintro ⟨M, hM, hMx⟩
    refine ⟨M, hM, fun n => ?_⟩
    rw [← pow_mul]
    exact hMx (k * n)

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- Passing to a positive power does not change the backward-contracting subspace. -/
theorem backwardContractingSubspace_pow (hS : IsUniformizerSemilinear (K := K) S) {k : ℕ}
    (hk : 1 ≤ k) :
    backwardContractingSubspace (S ^ k) (hS.pow k) = backwardContractingSubspace S hS := by
  ext x
  rw [mem_backwardContractingSubspace, mem_backwardContractingSubspace]
  constructor
  · rintro ⟨M, hM, hMx⟩
    refine ⟨forwardHull hS.inv M (k - 1), forwardHull_fg hS.inv hM (k - 1), fun j => ?_⟩
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hMx j)
    refine eventually_atTop.2 ⟨k * N₀, fun n hn => ?_⟩
    have hn' : S⁻¹ ^ n = S⁻¹ ^ (n % k) * (S⁻¹ ^ k) ^ (n / k) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    rw [hn', LinearEquiv.mul_apply]
    have hr : n % k ≤ k - 1 := by
      have := Nat.mod_lt n (show 0 < k by omega)
      omega
    have hq : N₀ ≤ n / k := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    have hmem : ((S⁻¹ ^ k) ^ (n / k)) x ∈ uniformizerDilate (j : ℤ) M := by
      have := hN₀ (n / k) hq
      rwa [← inv_pow] at this
    obtain ⟨z, hz, hzeq⟩ := mem_uniformizerDilate_iff_exists.1 hmem
    rw [← hzeq, IsUniformizerSemilinear.map_uniformizerZPow_smul (hS.inv.pow (n % k))]
    exact smul_mem_uniformizerDilate _ (pow_apply_mem_forwardHull hS.inv (k - 1) (n % k) hr z hz)
  · rintro ⟨M, hM, hMx⟩
    refine ⟨M, hM, fun j => ?_⟩
    have ht : Tendsto (fun n : ℕ => k * n) atTop atTop :=
      tendsto_id.const_mul_atTop' (by omega)
    filter_upwards [ht.eventually (hMx j)] with n hn
    rwa [inv_pow, ← pow_mul, ← inv_pow]

theorem semilinearDegree_congr {S' : E ≃ₗ[ℤ] E} (h : S = S')
    (hS : IsUniformizerSemilinear (K := K) S) (hS' : IsUniformizerSemilinear (K := K) S')
    (W : Submodule (CompletedPseudoDiffOp K) E) :
    semilinearDegree S hS W = semilinearDegree S' hS' W := by
  subst h
  rfl

theorem semilinearDegree_one (W : Submodule (CompletedPseudoDiffOp K) E)
    (h1 : IsUniformizerSemilinear (K := K) (1 : E ≃ₗ[ℤ] E)) :
    semilinearDegree 1 h1 W = 0 := by
  rw [semilinearDegree, semilinearImage_one, latticeIndex_self]

/-- The degree of the inverse is the negative of the degree. -/
theorem semilinearDegree_inv (hS : IsUniformizerSemilinear (K := K) S)
    {W : Submodule (CompletedPseudoDiffOp K) E} (hW : ∀ x ∈ W, S x ∈ W)
    (hW' : ∀ x ∈ W, S⁻¹ x ∈ W) :
    semilinearDegree S⁻¹ hS.inv W = -semilinearDegree S hS W := by
  have h := semilinearDegree_mul hS hS.inv hW hW' hW' (fun x hx => by rw [inv_inv]; exact hW x hx)
  have h1 : semilinearDegree (S * S⁻¹) (hS.mul hS.inv) W = 0 := by
    rw [semilinearDegree_congr (mul_inv_cancel S) (hS.mul hS.inv)
      (IsUniformizerSemilinear.one (K := K)) W]
    exact semilinearDegree_one W _
  linarith

/-- **Positive degree on the backward-contracting part.** -/
theorem semilinearDegree_pos_of_le_backwardContracting (hS : IsUniformizerSemilinear (K := K) S)
    {V : Submodule (CompletedPseudoDiffOp K) E} (hV : ∀ x ∈ V, S x ∈ V)
    (hV' : ∀ x ∈ V, S⁻¹ x ∈ V) (hVC : V ≤ backwardContractingSubspace S hS) (hV0 : V ≠ ⊥) :
    0 < semilinearDegree S hS V := by
  have hB : forwardBoundedSubspace S hS ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxV⟩
    have := backwardContractingSubspace_inf_forwardBoundedSubspace_eq_bot hS
    rw [← this]
    exact ⟨hVC hxV, hxB⟩
  obtain ⟨P, hPfg, hPspan, m, _, hcontr⟩ :=
    exists_contracting_lattice_of_inf_forwardBoundedSubspace_eq_bot hS _ V rfl hV hV' hB
  exact semilinearDegree_pos_of_expanding hS hV hV' hV0 ⟨hPfg, hPspan⟩ hcontr

/-- **Negative degree on the forward-contracting part.** -/
theorem semilinearDegree_neg_of_le_backwardContracting_inv (hS : IsUniformizerSemilinear (K := K) S)
    {V : Submodule (CompletedPseudoDiffOp K) E} (hV : ∀ x ∈ V, S x ∈ V)
    (hV' : ∀ x ∈ V, S⁻¹ x ∈ V) (hVC : V ≤ backwardContractingSubspace S⁻¹ hS.inv) (hV0 : V ≠ ⊥) :
    semilinearDegree S hS V < 0 := by
  have h := semilinearDegree_pos_of_le_backwardContracting hS.inv hV'
    (fun x hx => by rw [inv_inv]; exact hV x hx) hVC hV0
  rw [semilinearDegree_inv hS hV hV'] at h
  linarith

/-- **Zero degree on the neutral part.** -/
theorem semilinearDegree_eq_zero_of_le_neutral (hS : IsUniformizerSemilinear (K := K) S)
    {V : Submodule (CompletedPseudoDiffOp K) E} (hV : ∀ x ∈ V, S x ∈ V)
    (hV' : ∀ x ∈ V, S⁻¹ x ∈ V)
    (hVN : V ≤ forwardBoundedSubspace S hS ⊓ forwardBoundedSubspace S⁻¹ hS.inv) :
    semilinearDegree S hS V = 0 := by
  obtain ⟨L, hL, hSL⟩ := exists_stable_lattice_of_le_neutral hS hV hV' hVN
  exact semilinearDegree_eq_zero_of_stable hS hV hV' hL hSL

end

end DiffOp

end GaloisForLFunctions.HTGeometry
