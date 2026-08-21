import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy
import GaloisForLFunctions.RHTower.SchattenApproximation

/-!
# Global regular inertia and Calkin faithfulness

The root-depth tower supplies one finite regular block `ℓ²(ZMod m)` at every depth `m ≥ 2`.  Their
Hilbert sum carries a block-diagonal translation unitary for each integer charge.  The assignment
of charges to Calkin classes is an injective group homomorphism whose image is maximally separated:
two distinct charges have essential distance exactly two, so no compact — indeed no Schatten or
determinant-class — correction can identify them.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.LpDiagonal RHTower

/-! ## The global regular packet -/

/-- Index of the global regular packet: the disjoint union of the depth-`n + 2` blocks. -/
abbrev GlobalIndex : Type := Σ n : ℕ, ZMod (n + 2)

/-- Block translation by the reduction of the integer charge. -/
def globalShift (q : ℤ) : GlobalIndex ≃ GlobalIndex :=
  Equiv.sigmaCongrRight fun n => Equiv.addRight ((q : ZMod (n + 2)))

@[simp] theorem globalShift_apply (q : ℤ) (n : ℕ) (x : ZMod (n + 2)) :
    globalShift q ⟨n, x⟩ = ⟨n, x + (q : ZMod (n + 2))⟩ := rfl

@[simp] theorem globalShift_symm_apply (q : ℤ) (n : ℕ) (x : ZMod (n + 2)) :
    (globalShift q).symm ⟨n, x⟩ = ⟨n, x - (q : ZMod (n + 2))⟩ := by
  simp [globalShift, sub_eq_add_neg]

/-- The global regular inertia unitary of a charge. -/
noncomputable def globalInertiaUnitary (q : ℤ) : LpTwo GlobalIndex ≃ₗᵢ[ℂ] LpTwo GlobalIndex :=
  lpReindex (globalShift q)

/-- The same operator as a continuous linear map. -/
noncomputable def globalInertiaCLM (q : ℤ) : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex :=
  lpReindexCLM (globalShift q)

/-- Its defect from the identity. -/
noncomputable def globalInertiaDefect (q : ℤ) : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex :=
  lpReindexDefect (globalShift q)

theorem globalInertiaDefect_eq (q : ℤ) :
    globalInertiaDefect q = globalInertiaCLM q - ContinuousLinearMap.id ℂ (LpTwo GlobalIndex) :=
  rfl

theorem globalShift_eq_refl_of_zero : globalShift 0 = Equiv.refl GlobalIndex := by
  refine Equiv.ext fun i => ?_
  obtain ⟨n, x⟩ := i
  simp

theorem globalInertiaCLM_zero :
    globalInertiaCLM 0 = ContinuousLinearMap.id ℂ (LpTwo GlobalIndex) := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun i => ?_)
  rw [globalInertiaCLM, lpReindexCLM_coe, globalShift_eq_refl_of_zero]
  rfl

/-- **The charge representation is a homomorphism** (GRC.4). -/
theorem globalInertiaCLM_comp (q q' : ℤ) :
    globalInertiaCLM q ∘L globalInertiaCLM q' = globalInertiaCLM (q + q') := by
  refine ContinuousLinearMap.ext fun v => lp.ext (funext fun i => ?_)
  obtain ⟨n, x⟩ := i
  rw [ContinuousLinearMap.comp_apply]
  rw [globalInertiaCLM, globalInertiaCLM, globalInertiaCLM, lpReindexCLM_coe, lpReindexCLM_coe,
    lpReindexCLM_coe, globalShift_symm_apply, globalShift_symm_apply, globalShift_symm_apply]
  push_cast
  ring_nf

/-! ## Nonvanishing of the reduced charge -/

theorem intCast_ne_zero_of_natAbs_lt {q : ℤ} (hq : q ≠ 0) {M : ℕ} (h : q.natAbs < M) :
    (q : ZMod M) ≠ 0 := by
  intro hc
  have hdvd : ((M : ℕ) : ℤ) ∣ q := (ZMod.intCast_zmod_eq_zero_iff_dvd q M).1 hc
  have := Int.natAbs_le_of_dvd_ne_zero hdvd hq
  simp only [Int.natAbs_natCast] at this
  omega

theorem globalShift_fix_iff (q : ℤ) (n : ℕ) (x : ZMod (n + 2)) :
    globalShift q ⟨n, x⟩ = ⟨n, x⟩ ↔ (q : ZMod (n + 2)) = 0 := by
  rw [globalShift_apply, Sigma.mk.injEq]
  simp

theorem movedSet_globalShift_infinite {q : ℤ} (hq : q ≠ 0) :
    {i : GlobalIndex | globalShift q i ≠ i}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (⟨q.natAbs + k, 0⟩ : GlobalIndex)) ?_ ?_
  · intro a b hab
    have := congrArg Sigma.fst hab
    simpa using this
  · intro k
    simp only [Set.mem_setOf_eq]
    intro hcon
    exact intCast_ne_zero_of_natAbs_lt hq (by omega : q.natAbs < q.natAbs + k + 2)
      ((globalShift_fix_iff q (q.natAbs + k) 0).1 hcon)

/-- **Vanishing.**  The global inertia defect is zero exactly at charge zero. -/
theorem globalInertiaDefect_eq_zero_iff (q : ℤ) : globalInertiaDefect q = 0 ↔ q = 0 := by
  rw [globalInertiaDefect, lpReindexDefect_eq_zero_iff]
  constructor
  · intro h
    by_contra hq
    obtain ⟨i, hi⟩ := (movedSet_globalShift_infinite hq).nonempty
    exact hi (h i)
  · rintro rfl
    intro i
    rw [globalShift_eq_refl_of_zero]
    rfl

/-- **Calkin properness.**  The defect is compact exactly at charge zero. -/
theorem isCompactOperator_globalInertiaDefect_iff (q : ℤ) :
    IsCompactOperator (globalInertiaDefect q) ↔ q = 0 := by
  rw [globalInertiaDefect, isCompactOperator_lpReindexDefect_iff]
  constructor
  · intro hfin
    by_contra hq
    exact (movedSet_globalShift_infinite hq) hfin
  · rintro rfl
    have : {i : GlobalIndex | globalShift 0 i ≠ i} = ∅ := by
      ext i
      simp [globalShift_eq_refl_of_zero]
    rw [this]
    exact Set.finite_empty

/-! ## Long chains and the essential norm -/

theorem globalShift_iterate (q : ℤ) (n j : ℕ) (x : ZMod (n + 2)) :
    ((globalShift q) ^[j]) (⟨n, x⟩ : GlobalIndex) = ⟨n, x + j • (q : ZMod (n + 2))⟩ := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, globalShift_apply, succ_nsmul]
      congr 1
      abel

theorem globalShift_chain_injOn {q : ℤ} (hq : q ≠ 0) (m n : ℕ)
    (hn : (m + 1) * q.natAbs < n + 2) :
    Set.InjOn (fun j : ℕ => ((globalShift q) ^[j]) (⟨n, 0⟩ : GlobalIndex))
      (Finset.range (m + 2)) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  rw [globalShift_iterate, globalShift_iterate] at hab
  have hsnd : (0 : ZMod (n + 2)) + a • (q : ZMod (n + 2))
      = 0 + b • (q : ZMod (n + 2)) := by
    rw [Sigma.mk.injEq] at hab
    exact eq_of_heq hab.2
  rw [zero_add, zero_add, nsmul_eq_mul, nsmul_eq_mul] at hsnd
  have hcast : (((a : ℤ) * q : ℤ) : ZMod (n + 2)) = (((b : ℤ) * q : ℤ) : ZMod (n + 2)) := by
    push_cast
    exact hsnd
  have hzero : ((((a : ℤ) - b) * q : ℤ) : ZMod (n + 2)) = 0 := by
    push_cast
    rw [sub_mul]
    push_cast at hcast
    rw [hcast, sub_self]
  have hdvd : (((n + 2 : ℕ)) : ℤ) ∣ ((a : ℤ) - b) * q :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  by_contra hne
  have hne' : ((a : ℤ) - b) * q ≠ 0 := by
    refine mul_ne_zero ?_ hq
    intro hc
    exact hne (by omega : a = b)
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hne'
  simp only [Int.natAbs_natCast, Int.natAbs_mul] at hle
  have hab' : ((a : ℤ) - b).natAbs ≤ m + 1 := by omega
  have hq1 : 1 ≤ q.natAbs := Int.natAbs_pos.2 hq
  nlinarith [hle, hab', hn, hq1]

theorem globalShift_chains {q : ℤ} (hq : q ≠ 0) (m N : ℕ) :
    ∃ x : Fin N → GlobalIndex,
      (∀ k, Set.InjOn (fun j : ℕ => ((globalShift q) ^[j]) (x k)) (Finset.range (m + 2))) ∧
      ∀ k l, k ≠ l → ∀ i ∈ Finset.range (m + 2), ∀ j ∈ Finset.range (m + 2),
        ((globalShift q) ^[i]) (x k) ≠ ((globalShift q) ^[j]) (x l) := by
  refine ⟨fun k => ⟨(m + 1) * q.natAbs + k, 0⟩, fun k => ?_, ?_⟩
  · exact globalShift_chain_injOn hq m _ (by omega)
  · intro k l hkl i _ j _ hcon
    have hfst := congrArg Sigma.fst hcon
    rw [globalShift_iterate, globalShift_iterate] at hfst
    simp only at hfst
    exact hkl (Fin.ext (by omega))

theorem two_le_norm_globalInertiaDefect_sub {q : ℤ} (hq : q ≠ 0)
    {K : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex} (hK : IsCompactOperator K) :
    2 ≤ ‖globalInertiaDefect q - K‖ :=
  two_le_norm_lpReindexDefect_sub (globalShift q) (fun m N => globalShift_chains hq m N) hK

theorem norm_globalInertiaCLM_le_one (q : ℤ) : ‖globalInertiaCLM q‖ ≤ 1 :=
  (lpReindex (globalShift q)).toLinearIsometry.norm_toContinuousLinearMap_le

theorem norm_globalInertiaDefect_le_two (q : ℤ) : ‖globalInertiaDefect q‖ ≤ 2 := by
  have h1 := norm_globalInertiaCLM_le_one q
  have h2 : ‖ContinuousLinearMap.id ℂ (LpTwo GlobalIndex)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have := norm_sub_le (globalInertiaCLM q) (ContinuousLinearMap.id ℂ (LpTwo GlobalIndex))
  rw [globalInertiaDefect_eq]
  linarith

/-! ## The exact Calkin metric -/

theorem norm_comp_isometry {A S : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex}
    (hA : ∀ x, ‖A x‖ = ‖x‖) : ‖A ∘L S‖ = ‖S‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun x => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_)
  · rw [ContinuousLinearMap.comp_apply, hA]
    exact S.le_opNorm x
  · rw [← hA (S x), ← ContinuousLinearMap.comp_apply]
    exact (A ∘L S).le_opNorm x

theorem norm_globalInertiaCLM_apply (q : ℤ) (x : LpTwo GlobalIndex) :
    ‖globalInertiaCLM q x‖ = ‖x‖ :=
  (lpReindex (globalShift q)).norm_map x

/-- The charge difference factors through the defect of the difference charge. -/
theorem globalInertiaCLM_sub (q q' : ℤ) :
    globalInertiaCLM q - globalInertiaCLM q'
      = globalInertiaCLM q' ∘L globalInertiaDefect (q - q') := by
  rw [globalInertiaDefect_eq, ContinuousLinearMap.comp_sub, globalInertiaCLM_comp,
    ContinuousLinearMap.comp_id]
  congr 2
  ring

/-- **The exact Calkin metric** (GRC.5) and **compact repair is impossible** (GRC.8).  Distinct
charges stay at essential distance two. -/
theorem two_le_norm_globalInertiaCLM_sub_sub {q q' : ℤ} (h : q ≠ q')
    {K : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex} (hK : IsCompactOperator K) :
    2 ≤ ‖globalInertiaCLM q - globalInertiaCLM q' - K‖ := by
  have hinv : globalInertiaCLM q' ∘L globalInertiaCLM (-q')
      = ContinuousLinearMap.id ℂ (LpTwo GlobalIndex) := by
    rw [globalInertiaCLM_comp, add_neg_cancel, globalInertiaCLM_zero]
  have hK' : IsCompactOperator (globalInertiaCLM (-q') ∘L K) := by
    rw [ContinuousLinearMap.coe_comp]
    exact hK.clm_comp _
  have hfac : globalInertiaCLM q - globalInertiaCLM q' - K
      = globalInertiaCLM q' ∘L (globalInertiaDefect (q - q')
          - globalInertiaCLM (-q') ∘L K) := by
    rw [ContinuousLinearMap.comp_sub, ← globalInertiaCLM_sub, ← ContinuousLinearMap.comp_assoc,
      hinv, ContinuousLinearMap.id_comp]
  rw [hfac, norm_comp_isometry (norm_globalInertiaCLM_apply q')]
  exact two_le_norm_globalInertiaDefect_sub (sub_ne_zero.2 h) hK'

theorem norm_globalInertiaCLM_sub_le_two (q q' : ℤ) :
    ‖globalInertiaCLM q - globalInertiaCLM q'‖ ≤ 2 := by
  have h1 := norm_globalInertiaCLM_le_one q
  have h2 := norm_globalInertiaCLM_le_one q'
  have := norm_sub_le (globalInertiaCLM q) (globalInertiaCLM q')
  linarith

/-- **The essential distance of two charges is exactly two** (GRC.5). -/
theorem isGLB_essDist_globalInertiaCLM {q q' : ℤ} (h : q ≠ q') :
    IsGLB {x : ℝ | ∃ K : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex,
      IsCompactOperator K ∧ x = ‖globalInertiaCLM q - globalInertiaCLM q' - K‖} 2 := by
  constructor
  · rintro x ⟨K, hK, rfl⟩
    exact two_le_norm_globalInertiaCLM_sub_sub h hK
  · intro b hb
    have hmem : ‖globalInertiaCLM q - globalInertiaCLM q'‖ ∈
        {x : ℝ | ∃ K : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex,
          IsCompactOperator K ∧ x = ‖globalInertiaCLM q - globalInertiaCLM q' - K‖} :=
      ⟨0, isCompactOperator_zero, by rw [sub_zero]⟩
    have := hb hmem
    linarith [norm_globalInertiaCLM_sub_le_two q q']

/-- **Equal charges have essential distance zero.** -/
theorem isGLB_essDist_globalInertiaCLM_self (q : ℤ) :
    IsGLB {x : ℝ | ∃ K : LpTwo GlobalIndex →L[ℂ] LpTwo GlobalIndex,
      IsCompactOperator K ∧ x = ‖globalInertiaCLM q - globalInertiaCLM q - K‖} 0 := by
  constructor
  · rintro x ⟨K, hK, rfl⟩
    exact norm_nonneg _
  · intro b hb
    exact hb ⟨0, isCompactOperator_zero, by simp⟩

/-! ## Faithfulness and the five-way selection -/

/-- **Calkin faithfulness** (GRC.4).  Charges with compactly equivalent inertia unitaries agree. -/
theorem globalInertiaCLM_eq_of_isCompactOperator_sub {q q' : ℤ}
    (h : IsCompactOperator (globalInertiaCLM q - globalInertiaCLM q')) : q = q' := by
  by_contra hne
  have := two_le_norm_globalInertiaCLM_sub_sub hne h
  rw [sub_self, norm_zero] at this
  linarith

/-- **Theorem 3.1 — the five-way global formation selection.**  Charge zero, vanishing of the
defect, compactness, membership in some Schatten class, and determinant class are the same
condition. -/
theorem globalInertia_tfae (q : ℤ) :
    List.TFAE
      [ q = 0,
        globalInertiaDefect q = 0,
        IsCompactOperator (globalInertiaDefect q),
        ∃ p : ℝ, 0 < p ∧ MemSchattenClass p (globalInertiaDefect q),
        MemSchattenClass 1 (globalInertiaDefect q) ] := by
  tfae_have 1 → 2 := fun h => (globalInertiaDefect_eq_zero_iff q).2 h
  tfae_have 2 → 5 := by
    intro h
    rw [h]
    exact memSchattenClass_of_hasRankLE one_pos (hasRankLE_zero (H := LpTwo GlobalIndex) 0)
  tfae_have 5 → 4 := fun h => ⟨1, one_pos, h⟩
  tfae_have 4 → 3 := fun ⟨p, hp, h⟩ => h.isCompactOperator hp
  tfae_have 3 → 1 := fun h => (isCompactOperator_globalInertiaDefect_iff q).1 h
  tfae_finish

/-- **Corollary 6.1 for an arbitrary local charge family.**  Vanishing of every local charge,
compactness, Schatten membership and determinant-class membership of every local global-inertia
packet are the same condition. -/
theorem globalInertiaSelection_tfae {Γ : Type*} (ord : Γ → ℤ) :
    List.TFAE
      [ ∀ γ, ord γ = 0,
        ∀ γ, IsCompactOperator (globalInertiaDefect (ord γ)),
        ∀ γ, ∃ p : ℝ, 0 < p ∧ MemSchattenClass p (globalInertiaDefect (ord γ)),
        ∀ γ, MemSchattenClass 1 (globalInertiaDefect (ord γ)) ] := by
  tfae_have 1 → 2 := fun h γ => ((globalInertia_tfae (ord γ)).out 0 2).1 (h γ)
  tfae_have 2 → 3 := fun h γ => ((globalInertia_tfae (ord γ)).out 2 3).1 (h γ)
  tfae_have 3 → 4 := fun h γ => ((globalInertia_tfae (ord γ)).out 3 4).1 (h γ)
  tfae_have 4 → 1 := fun h γ => ((globalInertia_tfae (ord γ)).out 4 0).1 (h γ)
  tfae_finish

end GaloisForLFunctions.HTGeometry
