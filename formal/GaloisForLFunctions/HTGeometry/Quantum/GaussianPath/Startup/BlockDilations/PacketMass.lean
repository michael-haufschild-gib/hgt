import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SparsePacket
import Mathlib.Algebra.Order.Chebyshev

/-! # Longitudinal mass and squared norm in disjoint physical packets -/

open Finset Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {n : ℕ} {I : Type*} [Fintype I]

/-- Total absolute longitudinal field on the packet. -/
def longitudinal (R : Finset (Fin (n+2))) (u : PathShell n) : ℝ :=
  ∑ i ∈ R, |u (.inl (i,2))|

private theorem onsite_support (R : Finset (Fin (n+2))) (i : Fin (n+2)) :
    PathWordSupportedIn R (.inl (i,2)) ↔ i∈R := by
  constructor
  · intro h
    by_contra hi
    have he := h i hi
    simp [pathWord,onsiteWord] at he
  · intro hi j hj
    exact if_neg (show j≠i from fun h => hj (h ▸ hi))

theorem restricted_longitudinal (R : Finset (Fin (n+2))) (u : PathShell n) :
    (∑ j : Fin (n+2), |pathShellOnSites R u (.inl (j,2))|)=longitudinal R u := by
  unfold longitudinal
  have he (j : Fin (n+2)) : |pathShellOnSites R u (.inl (j,2))|=
      if j∈R then |u (.inl (j,2))| else 0 := by
    by_cases hj : j∈R <;> simp [pathShellOnSites,onsite_support,hj]
  simp_rw [he]
  rw [←sum_filter]
  congr 1
  ext; simp

/-- Cauchy–Schwarz charges only the wires of this packet. -/
theorem longitudinal_le (R : Finset (Fin (n+2))) (u : PathShell n) :
    longitudinal R u≤ sqrt R.card*‖pathShellOnSites R u‖ := by
  let v := pathShellOnSites R u
  let f (i : Fin (n+2)) : PathLabel n := .inl (i,2)
  have hf : Function.Injective f := fun _ _ h => (Prod.mk.inj (Sum.inl.inj h)).1
  have hs : ∑ i ∈ R, |u (f i)|^2≤‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (f:=fun j => v.ofLp j^2)
      (subset_univ (R.image f)) (fun _ _ _ => sq_nonneg _))
    rw [sum_image (fun _ _ _ _ h => hf h)]
    apply sum_le_sum
    intro i hi
    simp only [f,v,pathShellOnSites,WithLp.ofLp_toLp,onsite_support,if_pos hi,sq_abs,le_refl]
  have hh := (sq_sum_le_card_mul_sum_sq (s:=R) (f:=fun i => |u (f i)|)).trans
    (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  have hr := sqrt_le_sqrt hh
  rwa [sqrt_sq (sum_nonneg fun _ _ => abs_nonneg _),sqrt_mul (Nat.cast_nonneg _),
    sqrt_sq (norm_nonneg _)] at hr

/-- Internal packet energies sum to at most the energy of the full
coupling vector. Omitted or crossing words contribute zero. -/
theorem packet_energy_sum (R : I→Finset (Fin (n+2))) (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (u : PathShell n) : ∑ i, ‖pathShellOnSites (R i) u‖^2 ≤ ‖u‖^2 := by
  classical
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [sum_comm]
  apply sum_le_sum
  intro l _
  by_cases h : ∃ i, PathWordSupportedIn (R i) l
  · obtain ⟨i,hi⟩ := h
    rw [sum_eq_single i]
    · simp [pathShellOnSites,hi]
    · intro j _ hj
      have hn : ¬PathWordSupportedIn (R j) l := fun h => packet_support_intersects h hi (hR hj)
      simp only [pathShellOnSites,WithLp.ofLp_toLp,if_neg hn,zero_pow (by decide : 2≠0)]
    · exact fun hn => (hn (mem_univ i)).elim
  · have hn (i : I) : ¬PathWordSupportedIn (R i) l := fun hi => h ⟨i,hi⟩
    simp only [pathShellOnSites,WithLp.ofLp_toLp,if_neg (hn _),zero_pow (by decide : 2≠0),sum_const_zero]
    exact sq_nonneg _

/-- A large total longitudinal mass forces many packets above the field
threshold and below the norm threshold. The estimate is deterministic. -/
theorem longitudinal_mass_forces_packets (R : I→Finset (Fin (n+2)))
    (hR : Pairwise (fun i j => Disjoint (R i) (R j))) (u : PathShell n)
    (L : ℕ) (hL : ∀ i, (R i).card ≤ L) {m C : ℝ} (hm : 0 ≤ m) (hC : 0 < C) :
    open Classical in
    let G := univ.filter fun i => m≤longitudinal (R i) u ∧ ‖pathShellOnSites (R i) u‖≤C
    ∑ i, longitudinal (R i) u ≤ Fintype.card I*m+G.card*(sqrt L*C)+sqrt L/C*‖u‖^2 := by
  classical
  intro G
  let B := sqrt L
  let v := fun i => pathShellOnSites (R i) u
  have hB : 0≤B := sqrt_nonneg _
  have hh (i : I) : longitudinal (R i) u ≤ m+(if i∈G then B*C else 0)+B/C*‖v i‖^2 := by
    have hf : longitudinal (R i) u≤B*‖v i‖ := (longitudinal_le (R i) u).trans
      (mul_le_mul_of_nonneg_right (sqrt_le_sqrt (Nat.cast_le.mpr (hL i))) (norm_nonneg _))
    have hterm : 0≤B/C*‖v i‖^2 := mul_nonneg (div_nonneg hB hC.le) (sq_nonneg _)
    by_cases h : m≤longitudinal (R i) u
    · by_cases hi : ‖v i‖≤C
      · rw [if_pos (show i∈G from mem_filter.mpr ⟨mem_univ _,h,hi⟩)]
        linarith only [hf.trans (mul_le_mul_of_nonneg_left hi hB),hm,hterm]
      · have hn : i∉G := fun h => hi (mem_filter.mp h).2.2
        rw [if_neg hn,add_zero]
        have hp : C*‖v i‖≤‖v i‖^2 := by
          rw [sq]; exact mul_le_mul_of_nonneg_right (le_of_not_ge hi) (norm_nonneg _)
        have he := mul_le_mul_of_nonneg_left hp (div_nonneg hB hC.le)
        rw [←mul_assoc,div_mul_cancel₀ B hC.ne'] at he
        linarith only [hf.trans he,hm]
    · rw [if_neg (show i∉G from fun hi => h (mem_filter.mp hi).2.1),add_zero]
      linarith only [le_of_not_ge h,hterm]
  have hsum := sum_le_sum (s:=univ) (fun i _ => hh i)
  have he : (∑ i, if i∈G then B*C else 0)=(G.card:ℝ)*(B*C) := by
    rw [←sum_filter]
    simp only [filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul]
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,he,←mul_sum] at hsum
  exact hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (packet_energy_sum R hR u) (div_nonneg hB hC.le)))

#print axioms longitudinal_mass_forces_packets
end
end GaloisForLFunctions.HTGeometry.BlockDilations
