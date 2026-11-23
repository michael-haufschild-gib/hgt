import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCupProduct

/-! A homogeneous left cochain gives the usual degree sign in the
right term of the Čech cup-product rule. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.CechDR

variable {k ι E M N : Type*} [Field k] [LinearOrder ι]
  [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

omit [LinearOrder ι] in
theorem cechC_apply_empty {A : Finset ι → Submodule k E} {p : ℤ}
    {a : Finset ι → E} (ha : a ∈ cechC A p) : a ∅ = 0 := by
  have e := (Submodule.mem_pi.mp ha) ∅ (Set.mem_univ _)
  exact (Submodule.mem_bot k).mp (by simpa only [Finset.not_nonempty_empty, false_and, if_false] using e)

/-- The differential of the ordered cup of cochains, with the sign
determined by the degree of the left factor. -/
theorem deltaL_cechCup (μ : E →ₗ[k] M →ₗ[k] N) {A : Finset ι → Submodule k E}
    {p : ℕ} {a : Finset ι → E} (b : Finset ι → M) (ha : a ∈ cechC A p) (hb : b ∅ = 0) :
    deltaL k ι N (cechCup μ a b) =
      cechCup μ (deltaL k ι E a) b + (-1 : ℤ) ^ p • cechCup μ a (deltaL k ι M b) := by
  funext U
  let Φ : E →+ (Finset ι → N) := (LinearMap.pi fun J => μ.flip (b J)).toAddMonoidHom
  have h := delta_orderedCup Φ a
    (fun x => by change μ x (b ∅) = 0; rw [hb, map_zero]) (cechC_apply_empty ha) U
  change deltaL k ι N (cechCup μ a b) U = cechCup μ (deltaL k ι E a) b U + _ at h
  rw [Pi.add_apply, Pi.smul_apply, h, cechCup_apply μ a (deltaL k ι M b), Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  let I := U.filter (· ≤ j)
  let J := U.filter (j ≤ ·)
  have e : cechDModule ℤ (Φ (a I)) J = μ (a I) (deltaL k ι M b J) := by
    rw [deltaL_apply, map_sum]
    simp only [cechDModule, map_zsmul] <;> rfl
  change cubeSign U j • cechDModule ℤ (Φ (a I)) J =
    (-1 : ℤ) ^ p • μ (a I) (deltaL k ι M b J)
  rw [e]
  have hI := (Submodule.mem_pi.mp ha) I (Set.mem_univ _)
  split_ifs at hI with hI'
  · have hfilter : I = insert j (U.filter (· < j)) := by
      ext i
      simp only [I, Finset.mem_filter, Finset.mem_insert]
      exact ⟨fun ⟨hi, hij⟩ => hij.eq_or_lt.elim Or.inl fun h => Or.inr ⟨hi, h⟩,
        fun h => h.elim (fun e => e.symm ▸ ⟨hj, le_rfl⟩) (fun ⟨hi, hlt⟩ => ⟨hi, hlt.le⟩)⟩
    have hc : I.card = (U.filter (· < j)).card + 1 := by
      rw [hfilter, Finset.card_insert_of_notMem (by simp)]
    have hp := hI'.2
    change (-1 : ℤ) ^ (U.filter (· < j)).card • _ = _
    rw [show (U.filter (· < j)).card = p by omega]
  · simp only [(Submodule.mem_bot k).mp hI, map_zero, LinearMap.zero_apply, smul_zero]

section Boundaries

variable (μ : E →ₗ[k] M →ₗ[k] N)
  (A : Finset ι → Submodule k E) (B : Finset ι → Submodule k M) (C : Finset ι → Submodule k N)
  (hC : ∀ {I J U}, I.Nonempty → J.Nonempty → I ⊆ U → J ⊆ U →
    ∀ {x y}, x ∈ A I → y ∈ B J → μ x y ∈ C U)

include hC

/-- Cup product sends a left boundary and a right cocycle to a boundary. -/
theorem cechCup_boundary_left {p q : ℤ} {a : Finset ι → E} {b : Finset ι → M}
    (ha : a ∈ (cech A).B p) (hb : b ∈ (cech B).Z q) :
    cechCup μ a b ∈ (cech C).B (p + q) := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp ha
  have h := cechCup_mem μ A B C hC hv hb.1
  refine ⟨cechCup μ v b, ?_, ?_⟩
  · rw [show p + q - 1 = (p - 1) + q by omega]
    exact h
  · exact deltaL_cechCup_of_rightCycle μ v b (cechC_apply_empty hv) (cechC_apply_empty hb.1) hb.2

/-- Cup product sends a left cocycle and a right boundary to a boundary. -/
theorem cechCup_boundary_right {p : ℕ} {q : ℤ} {a : Finset ι → E} {b : Finset ι → M}
    (ha : a ∈ (cech A).Z p) (hb : b ∈ (cech B).B q) :
    cechCup μ a b ∈ (cech C).B ((p : ℤ) + q) := by
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hb
  have h := cechCup_mem μ A B C hC ha.1 hv
  have hD := deltaL_cechCup μ v ha.1 (cechC_apply_empty hv)
  have hda : deltaL k ι E a = 0 := ha.2
  have hzero : cechCup μ (0 : Finset ι → E) v = 0 := by
    funext U
    simp only [cechCup_apply, Pi.zero_apply, map_zero, LinearMap.zero_apply, Finset.sum_const_zero]
  rw [hda, hzero, zero_add] at hD
  refine ⟨(-1 : ℤ) ^ p • cechCup μ a v, ?_, ?_⟩
  · rw [show (p : ℤ) + q - 1 = p + (q - 1) by omega]
    exact zsmul_mem h _
  · change deltaL k ι N ((-1 : ℤ) ^ p • cechCup μ a v) = cechCup μ a (deltaL k ι M v)
    rw [map_zsmul, hD, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

end Boundaries

end GlobalTheory.CechDR
