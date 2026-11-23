import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex

/-! Čech–Koszul differentials with commuting coefficient endomorphisms. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k ι M : Type*} [LinearOrder ι] [AddCommGroup M]

section Weighted

variable [CommRing k] [Module k M]

/-- Apply the coefficient endomorphism corresponding to each deleted index. -/
def wd (w : ι → Module.End k M) : (Finset ι → M) →ₗ[k] (Finset ι → M) :=
  LinearMap.pi fun t => ∑ i ∈ t, cubeSign t i • (w i ∘ₗ LinearMap.proj (t.erase i))

theorem wd_apply (w : ι → Module.End k M) (a : Finset ι → M) (t : Finset ι) :
    wd w a t = ∑ i ∈ t, cubeSign t i • w i (a (t.erase i)) := by
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

private theorem wd_wd_term (w w' : ι → Module.End k M) (a : Finset ι → M)
    (t : Finset ι) (i : ι) :
    cubeSign t i • w i (wd w' a (t.erase i)) =
      ∑ j ∈ t.erase i, (cubeSign t i * cubeSign (t.erase i) j) •
        w i (w' j (a ((t.erase i).erase j))) := by
  rw [wd_apply, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, smul_smul]

/-- The two orders of deleting a pair cancel when their coefficient maps commute. -/
theorem wd_wd (w : ι → Module.End k M) (h : ∀ i j, Commute (w i) (w j)) (a : Finset ι → M) :
    wd w (wd w a) = 0 := by
  funext t
  rw [wd_apply, Pi.zero_apply]
  rw [Finset.sum_congr rfl fun i _ => wd_wd_term w w a t i, Finset.sum_sigma' t (fun i => t.erase i)
    (fun i j => (cubeSign t i * cubeSign (t.erase i) j) •
      w i (w j (a ((t.erase i).erase j))))]
  refine Finset.sum_involution (fun ij _ => ⟨ij.2, ij.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hij
    have hji := (Finset.mem_erase.mp hj).1
    have hjt := Finset.mem_of_mem_erase hj
    have he : (t.erase j).erase i = (t.erase i).erase j := Finset.erase_right_comm
    have hc (x : M) : w i (w j x) = w j (w i x) := LinearMap.congr_fun (h i j).eq x
    simp only [he]
    rw [hc, cubeSign_mul_erase hi hjt hji.symm, neg_smul, neg_add_cancel]
  · rintro ⟨i, j⟩ hij _
    intro e
    exact (Finset.mem_erase.mp (Finset.mem_sigma.mp hij).2).1
      (congrArg Sigma.fst e)
  · rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hij
    exact Finset.mem_sigma.mpr ⟨Finset.mem_of_mem_erase hj,
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1.symm, hi⟩⟩
  · rintro ⟨i, j⟩ _
    rfl

/-- Two weighted differentials anticommute if their cross weights commute. -/
theorem wd_anticommute (w w' : ι → Module.End k M)
    (h : ∀ i j, Commute (w i) (w' j)) (a : Finset ι → M) :
    wd w (wd w' a) + wd w' (wd w a) = 0 := by
  funext t
  simp only [Pi.add_apply, Pi.zero_apply, wd_apply w (wd w' a), wd_apply w' (wd w a),
    wd_wd_term]
  have swap (f : ι → ι → M) :
      (∑ i ∈ t, ∑ j ∈ t.erase i, f i j) = ∑ i ∈ t, ∑ j ∈ t.erase i, f j i := by
    apply Finset.sum_comm'
    intro i j
    simp only [Finset.mem_erase]
    exact ⟨fun ⟨hi, hji, hj⟩ => ⟨⟨hji.symm, hi⟩, hj⟩,
      fun ⟨⟨hij, hi⟩, hj⟩ => ⟨hi, hij.symm, hj⟩⟩
  conv_lhs => rhs; rw [swap]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  obtain ⟨hji, hjt⟩ := Finset.mem_erase.mp hj
  have he : (t.erase j).erase i = (t.erase i).erase j := Finset.erase_right_comm
  have hc : w i (w' j (a ((t.erase i).erase j))) =
      w' j (w i (a ((t.erase i).erase j))) := LinearMap.congr_fun (h i j).eq _
  rw [he, hc, cubeSign_mul_erase hi hjt hji.symm, neg_smul, neg_add_cancel]

theorem wd_add (w w' : ι → Module.End k M) : wd (w + w') = wd w + wd w' := by
  ext a t
  simp only [wd_apply, LinearMap.add_apply, Pi.add_apply, smul_add, Finset.sum_add_distrib]

end Weighted

variable [Field k] [Module k M]

theorem wd_one : wd (1 : ι → Module.End k M) = deltaL k ι M := by
  ext a t
  simp only [wd_apply, deltaL_apply, Pi.one_apply, Module.End.one_apply]

private def verticalD (κ : Module.End k M) : Module.End k (Finset ι → M) :=
  LinearMap.pi fun t => ((-1 : ℤ) ^ t.card) • (κ ∘ₗ LinearMap.proj t)

omit [LinearOrder ι] in
private theorem verticalD_apply (κ : Module.End k M) (a : Finset ι → M) (t : Finset ι) :
    verticalD κ a t = ((-1 : ℤ) ^ t.card) • κ (a t) := rfl

/-- Total differential, with the vertical map signed by the cardinality. -/
def tD (w : ι → Module.End k M) (κ : Module.End k M) : (Finset ι → M) →ₗ[k] (Finset ι → M) :=
  wd w + verticalD κ

theorem tD_apply (w : ι → Module.End k M) (κ : Module.End k M) (a : Finset ι → M) (t : Finset ι) :
    tD w κ a t = wd w a t + ((-1 : ℤ) ^ t.card) • κ (a t) := rfl

private theorem verticalD_anticommute (w : ι → Module.End k M) (κ : Module.End k M)
    (h : ∀ i, Commute (w i) κ) (a : Finset ι → M) :
    wd w (verticalD κ a) + verticalD κ (wd w a) = 0 := by
  funext t
  simp only [Pi.add_apply, Pi.zero_apply, wd_apply, verticalD_apply, map_sum, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hc : w i (κ (a (t.erase i))) = κ (w i (a (t.erase i))) :=
    LinearMap.congr_fun (h i).eq _
  rw [map_zsmul, hc, map_zsmul, smul_comm ((-1 : ℤ) ^ t.card) (cubeSign t i),
    ← smul_add, ← Finset.card_erase_add_one hi, pow_succ, mul_neg_one, neg_smul, add_neg_cancel, smul_zero]

/-- The signed total differential squares to zero. -/
theorem tD_tD (w : ι → Module.End k M) (κ : Module.End k M)
    (hw : ∀ i j, Commute (w i) (w j)) (hκ : ∀ i, Commute (w i) κ)
    (hκ₂ : ∀ x, κ (κ x) = 0) (a : Finset ι → M) : tD w κ (tD w κ a) = 0 := by
  have hVV : verticalD κ (verticalD κ a) = 0 := by
    funext t
    simp only [verticalD_apply, Pi.zero_apply, map_zsmul, hκ₂, smul_zero]
  simp only [tD, LinearMap.add_apply, map_add, wd_wd w hw, hVV, zero_add, add_zero]
  exact (add_comm _ _).trans (verticalD_anticommute w κ hκ a)

/-- The degree of a coefficient is its total degree minus the cardinality of its index set. -/
def tcx (T : ℤ → Finset ι → Submodule k M) (w : ι → Module.End k M) (κ : Module.End k M) :
    Cx k (Finset ι → M) :=
  ⟨fun n => Submodule.pi Set.univ fun t => T (n - t.card) t, tD w κ⟩

/-- The total complex is graded when the horizontal and vertical maps
preserve their respective chart and coefficient degrees. -/
theorem tcx_isCx (T : ℤ → Finset ι → Submodule k M) (w : ι → Module.End k M) (κ : Module.End k M)
    (hw : ∀ i j, Commute (w i) (w j)) (hκ : ∀ i, Commute (w i) κ)
    (hκ₂ : ∀ x, κ (κ x) = 0)
    (hH : ∀ n t i, i ∉ t → T n t ≤ (T n (insert i t)).comap (w i))
    (hV : ∀ n t, T n t ≤ (T (n + 1) t).comap κ) : (tcx T w κ).IsCx := by
  intro n a ha
  have ha' (t : Finset ι) : a t ∈ T (n - t.card) t :=
    (Submodule.mem_pi.mp ha) t (Set.mem_univ _)
  refine ⟨Submodule.mem_pi.mpr fun t _ => ?_, tD_tD w κ hw hκ hκ₂ a⟩
  change tD w κ a t ∈ T (n + 1 - t.card) t
  rw [tD_apply]
  apply Submodule.add_mem
  · rw [wd_apply]
    refine Submodule.sum_mem _ fun i hi => zsmul_mem ?_ _
    have hc : n - ((t.erase i).card : ℤ) = n + 1 - (t.card : ℤ) := by
      have := Finset.card_erase_add_one hi
      omega
    have h := hH _ (t.erase i) i (Finset.notMem_erase _ _) (ha' (t.erase i))
    rwa [Submodule.mem_comap, Finset.insert_erase hi, hc] at h
  · apply zsmul_mem
    have h := hV (n - t.card) t (ha' t)
    rwa [Submodule.mem_comap, show n - (t.card : ℤ) + 1 = n + 1 - (t.card : ℤ) by omega] at h

/-- The augmented weighted Čech terms include the empty intersection in degree zero. -/
def acx (A : Finset ι → Submodule k M) (w : ι → Module.End k M) : Cx k (Finset ι → M) :=
  ⟨fun n => Submodule.pi Set.univ fun t => if (t.card : ℤ) = n then A t else ⊥, wd w⟩

/-- If each weight sends the source chart into its extension, the augmented
terms form a complex. -/
theorem acx_isCx (A : Finset ι → Submodule k M) (w : ι → Module.End k M)
    (hc : ∀ i j, Commute (w i) (w j))
    (hA : ∀ t i, i ∉ t → A t ≤ (A (insert i t)).comap (w i)) :
    (acx A w).IsCx := by
  intro n a ha
  have ha' (t : Finset ι) : a t ∈ (if (t.card : ℤ) = n then A t else ⊥) :=
    (Submodule.mem_pi.mp ha) t (Set.mem_univ _)
  refine ⟨Submodule.mem_pi.mpr fun t _ => ?_, wd_wd w hc a⟩
  change wd w a t ∈ (if (t.card : ℤ) = n + 1 then A t else ⊥)
  rw [wd_apply]
  by_cases hdeg : (t.card : ℤ) = n + 1
  · rw [if_pos hdeg]
    refine Submodule.sum_mem _ fun i hi => zsmul_mem ?_ _
    have hcard : ((t.erase i).card : ℤ) = n := by
      have h := Finset.card_erase_add_one hi
      omega
    have hmem := ha' (t.erase i)
    rw [if_pos hcard] at hmem
    have h := hA (t.erase i) i (Finset.notMem_erase _ _) hmem
    rwa [Submodule.mem_comap, Finset.insert_erase hi] at h
  · rw [if_neg hdeg, Submodule.mem_bot]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : ((t.erase i).card : ℤ) ≠ n := by
      have h := Finset.card_erase_add_one hi
      omega
    have h := ha' (t.erase i)
    rw [if_neg hcard, Submodule.mem_bot] at h
    rw [h, map_zero, smul_zero]

end GlobalTheory.WH
