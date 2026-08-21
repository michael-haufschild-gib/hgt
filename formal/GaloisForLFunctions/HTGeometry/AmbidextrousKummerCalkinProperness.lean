import GaloisForLFunctions.HTGeometry.AmbidextrousKummerDepthCalculus
import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy

/-!
# Ambidextrous Calkin properness of the regular Kummer packet

The doubling defect of an integer charge acts on each block `ℓ²(ZMod 2n)` by the regular
translation.  Assembling the blocks into one `ℓ²` space over the sigma index, the resulting unitary
differs from the identity by a compact operator exactly when the charge vanishes, in which case it
*is* the identity.  Since every Schatten class lies between the finite-rank operators and the
compact operators, the same dichotomy holds for Schatten membership.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.LpDiagonal

/-- Index of the ambidextrous regular packet: the disjoint union of the depth-`2(n+2)` blocks. -/
abbrev AmbIndex : Type := Σ n : ℕ, ZMod (2 * (n + 2))

/-- Block translation by the doubling defect of the charge. -/
def ambShift (q : ℤ) : AmbIndex ≃ AmbIndex :=
  Equiv.sigmaCongrRight fun n => Equiv.addRight (ambidextrousDoublingDefect (n + 2) q)

@[simp] theorem ambShift_apply (q : ℤ) (n : ℕ) (x : ZMod (2 * (n + 2))) :
    ambShift q ⟨n, x⟩ = ⟨n, x + ambidextrousDoublingDefect (n + 2) q⟩ := rfl

theorem ambShift_fix_iff (q : ℤ) (n : ℕ) (x : ZMod (2 * (n + 2))) :
    ambShift q ⟨n, x⟩ = ⟨n, x⟩ ↔ ambidextrousDoublingDefect (n + 2) q = 0 := by
  rw [ambShift_apply, Sigma.mk.injEq]
  simp

/-- The regular ambidextrous packet unitary. -/
noncomputable def ambPacketUnitary (q : ℤ) : LpTwo AmbIndex ≃ₗᵢ[ℂ] LpTwo AmbIndex :=
  lpReindex (ambShift q)

/-- Its defect from the identity. -/
noncomputable def ambPacketDefect (q : ℤ) : LpTwo AmbIndex →L[ℂ] LpTwo AmbIndex :=
  lpReindexDefect (ambShift q)

theorem ambShift_eq_refl_of_zero : ambShift 0 = Equiv.refl AmbIndex := by
  refine Equiv.ext fun i => ?_
  obtain ⟨n, x⟩ := i
  rw [ambShift_apply]
  simp [ambidextrousDoublingDefect]

theorem movedSet_ambShift_infinite {q : ℤ} (hq : q ≠ 0) :
    {i : AmbIndex | ambShift q i ≠ i}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (⟨q.natAbs + k, 0⟩ : AmbIndex)) ?_ ?_
  · intro a b hab
    have := congrArg Sigma.fst hab
    simpa using this
  · intro k
    simp only [Set.mem_setOf_eq]
    intro hcon
    exact ambidextrousDoublingDefect_ne_zero hq (by omega)
      ((ambShift_fix_iff q (q.natAbs + k) 0).1 hcon)

/-- **Vanishing.**  The packet defect is zero exactly at charge zero. -/
theorem ambPacketDefect_eq_zero_iff (q : ℤ) : ambPacketDefect q = 0 ↔ q = 0 := by
  rw [ambPacketDefect, lpReindexDefect_eq_zero_iff]
  constructor
  · intro h
    by_contra hq
    obtain ⟨i, hi⟩ := (movedSet_ambShift_infinite hq).nonempty
    exact hi (h i)
  · rintro rfl
    intro i
    rw [ambShift_eq_refl_of_zero]
    rfl

/-- **Ambidextrous Calkin properness.**  The packet defect is compact exactly at charge zero, and
there it vanishes identically. -/
theorem isCompactOperator_ambPacketDefect_iff (q : ℤ) :
    IsCompactOperator (ambPacketDefect q) ↔ q = 0 := by
  rw [ambPacketDefect, isCompactOperator_lpReindexDefect_iff]
  constructor
  · intro hfin
    by_contra hq
    exact (movedSet_ambShift_infinite hq) hfin
  · rintro rfl
    have : {i : AmbIndex | ambShift 0 i ≠ i} = ∅ := by
      ext i
      simp [ambShift_eq_refl_of_zero]
    rw [this]
    exact Set.finite_empty

/-- **Theorem 4.1.**  Vanishing, compactness of the defect, and charge zero are the same
condition. -/
theorem ambPacket_tfae (q : ℤ) :
    List.TFAE
      [ q = 0,
        ambPacketDefect q = 0,
        IsCompactOperator (ambPacketDefect q) ] := by
  tfae_have 1 → 2 := fun h => (ambPacketDefect_eq_zero_iff q).2 h
  tfae_have 2 → 3 := by
    intro h
    rw [h]
    exact isCompactOperator_zero
  tfae_have 3 → 1 := fun h => (isCompactOperator_ambPacketDefect_iff q).1 h
  tfae_finish

/-! ## The essential norm -/

theorem ambShift_iterate (q : ℤ) (n j : ℕ) (x : ZMod (2 * (n + 2))) :
    ((ambShift q) ^[j]) (⟨n, x⟩ : AmbIndex)
      = ⟨n, x + j • ambidextrousDoublingDefect (n + 2) q⟩ := by
  induction j with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, ambShift_apply, succ_nsmul]
      congr 1
      abel

theorem ambShift_chain_injOn {q : ℤ} (hq : q ≠ 0) (m n : ℕ)
    (hn : (m + 1) * q.natAbs < 2 * (n + 2)) :
    Set.InjOn (fun j : ℕ => ((ambShift q) ^[j]) (⟨n, 0⟩ : AmbIndex))
      (Finset.range (m + 2)) := by
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  rw [ambShift_iterate, ambShift_iterate] at hab
  have hsnd : (0 : ZMod (2 * (n + 2))) + a • ambidextrousDoublingDefect (n + 2) q
      = 0 + b • ambidextrousDoublingDefect (n + 2) q := by
    rw [Sigma.mk.injEq] at hab
    exact eq_of_heq hab.2
  rw [zero_add, zero_add, ambidextrousDoublingDefect_eq, nsmul_eq_mul, nsmul_eq_mul] at hsnd
  have hcast : (((a : ℤ) * (-q) : ℤ) : ZMod (2 * (n + 2)))
      = (((b : ℤ) * (-q) : ℤ) : ZMod (2 * (n + 2))) := by
    push_cast
    exact hsnd
  have hzero : ((((a : ℤ) - b) * (-q) : ℤ) : ZMod (2 * (n + 2))) = 0 := by
    push_cast
    rw [sub_mul]
    push_cast at hcast
    rw [hcast, sub_self]
  have hdvd : ((2 * (n + 2) : ℕ) : ℤ) ∣ ((a : ℤ) - b) * (-q) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  by_contra hne
  have hne' : ((a : ℤ) - b) * (-q) ≠ 0 := by
    refine mul_ne_zero ?_ (neg_ne_zero.2 hq)
    intro hc
    exact hne (by omega : a = b)
  have hle := Int.natAbs_le_of_dvd_ne_zero hdvd hne'
  simp only [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_neg] at hle
  have hab' : ((a : ℤ) - b).natAbs ≤ m + 1 := by omega
  have hq1 : 1 ≤ q.natAbs := Int.natAbs_pos.2 hq
  nlinarith [hle, hab', hn, hq1]

theorem ambShift_chains {q : ℤ} (hq : q ≠ 0) (m N : ℕ) :
    ∃ x : Fin N → AmbIndex,
      (∀ k, Set.InjOn (fun j : ℕ => ((ambShift q) ^[j]) (x k)) (Finset.range (m + 2))) ∧
      ∀ k l, k ≠ l → ∀ i ∈ Finset.range (m + 2), ∀ j ∈ Finset.range (m + 2),
        ((ambShift q) ^[i]) (x k) ≠ ((ambShift q) ^[j]) (x l) := by
  refine ⟨fun k => ⟨(m + 1) * q.natAbs + k, 0⟩, fun k => ?_, ?_⟩
  · exact ambShift_chain_injOn hq m _ (by omega)
  · intro k l hkl i _ j _ hcon
    have hfst := congrArg Sigma.fst hcon
    rw [ambShift_iterate, ambShift_iterate] at hfst
    simp only at hfst
    exact hkl (Fin.ext (by omega))

theorem two_le_norm_ambPacketDefect_sub {q : ℤ} (hq : q ≠ 0)
    {K : LpTwo AmbIndex →L[ℂ] LpTwo AmbIndex} (hK : IsCompactOperator K) :
    2 ≤ ‖ambPacketDefect q - K‖ :=
  two_le_norm_lpReindexDefect_sub (ambShift q) (fun m N => ambShift_chains hq m N) hK

theorem norm_ambPacketDefect_le_two (q : ℤ) : ‖ambPacketDefect q‖ ≤ 2 := by
  have h1 : ‖lpReindexCLM (ambShift q)‖ ≤ 1 :=
    (lpReindex (ambShift q)).toLinearIsometry.norm_toContinuousLinearMap_le
  have h2 : ‖ContinuousLinearMap.id ℂ (LpTwo AmbIndex)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have := norm_sub_le (lpReindexCLM (ambShift q)) (ContinuousLinearMap.id ℂ (LpTwo AmbIndex))
  rw [ambPacketDefect, lpReindexDefect]
  linarith

/-- **The exact essential norm** (ART.12).  For a nonzero charge the packet defect sits at
distance exactly two from the compact operators. -/
theorem isGLB_essNorm_ambPacketDefect {q : ℤ} (hq : q ≠ 0) :
    IsGLB {x : ℝ | ∃ K : LpTwo AmbIndex →L[ℂ] LpTwo AmbIndex,
      IsCompactOperator K ∧ x = ‖ambPacketDefect q - K‖} 2 := by
  constructor
  · rintro x ⟨K, hK, rfl⟩
    exact two_le_norm_ambPacketDefect_sub hq hK
  · intro b hb
    have hmem : ‖ambPacketDefect q‖ ∈ {x : ℝ | ∃ K : LpTwo AmbIndex →L[ℂ] LpTwo AmbIndex,
        IsCompactOperator K ∧ x = ‖ambPacketDefect q - K‖} := by
      refine ⟨0, isCompactOperator_zero, ?_⟩
      rw [sub_zero]
    have := hb hmem
    linarith [norm_ambPacketDefect_le_two q]

/-! ## Local charge families -/

/-- **Mackey-flat selection for a family of local charges** (ART, Corollary 6.1).  For a family of
local integer charges — the local orders of a meromorphic formation transfer — vanishing of the
family, universal ambidextrous flatness, cofinal doubling flatness, and compactness of every
regular ambidextrous packet are the same condition. -/
theorem mackeyFlatSelection_tfae {Γ : Type*} (ord : Γ → ℤ) :
    List.TFAE
      [ ∀ γ, ord γ = 0,
        ∀ γ, ∀ (n m : ℕ) (h : n ∣ m), ambidextrousDefect h (ord γ) = 0,
        ∀ γ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ambidextrousDoublingDefect n (ord γ) = 0,
        ∀ γ, IsCompactOperator (ambPacketDefect (ord γ)) ] := by
  tfae_have 1 → 2 := fun h γ => ((ambidextrousDefect_tfae (ord γ)).out 0 1).1 (h γ)
  tfae_have 2 → 3 := fun h γ => ((ambidextrousDefect_tfae (ord γ)).out 1 3).1 (h γ)
  tfae_have 3 → 1 := fun h γ => ((ambidextrousDefect_tfae (ord γ)).out 3 0).1 (h γ)
  tfae_have 1 → 4 := fun h γ => (isCompactOperator_ambPacketDefect_iff (ord γ)).2 (h γ)
  tfae_have 4 → 1 := fun h γ => (isCompactOperator_ambPacketDefect_iff (ord γ)).1 (h γ)
  tfae_finish

end GaloisForLFunctions.HTGeometry
