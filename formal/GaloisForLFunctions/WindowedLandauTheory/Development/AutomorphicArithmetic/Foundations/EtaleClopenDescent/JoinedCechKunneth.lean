import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechTensorDifferential
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.MixedCechCupBoundary
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact

/-! The cohomology of the joined intersections with tensor coefficients
is represented by products of cocycles on the two covers. -/

noncomputable section

open GlobalTheory.CechDR
open scoped TensorProduct

namespace GlobalTheory.WH

variable {k ι κ E M : Type} [Field k] [LinearOrder ι] [LinearOrder κ]
  [Fintype ι] [Fintype κ] [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]
  (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k M)
  (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
  (hB : ∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t)

local notation "G" => gradedCech A hA
local notation "G'" => gradedCech B hB
local notation "μ" => TensorProduct.mk k E M
local notation "C" => mixedCech (fun I J => Submodule.map₂ μ (A I) (B J))

private theorem cech_cycle_of_projected_cycle {p : ℕ}
    (a : regularCochains A) (ha : (G).π (p + 1) a = a) (hd : (G).d a = 0) :
    a.val ∈ (cech A).Z p := by
  obtain ⟨ha₀, haA⟩ := mem_regularCochains.mp a.property
  refine ⟨Submodule.mem_pi.mpr (fun I _ => ?_), ?_⟩
  · split_ifs with hI
    · exact haA I
    · have h : a.val I = 0 := by
        rcases I.eq_empty_or_nonempty with rfl | hne
        · exact ha₀
        have hc : I.card ≠ p + 1 := fun e => hI ⟨hne, by exact_mod_cast e⟩
        have e := congrFun (congrArg Subtype.val ha) I
        change ((G).π (p + 1) a).val I = a.val I at e
        rw [gradedCech_projection_apply, if_neg hc] at e
        exact e.symm
      rw [h]
      exact zero_mem _
  · exact LinearMap.mem_ker.mpr (congrArg Subtype.val hd)

private theorem exists_finite_sum_of_span {T : Type} [AddCommGroup T] [Module k T]
    (S : Set T) (hS : ∀ c : k, ∀ x ∈ S, c • x ∈ S) {x : T} (hx : x ∈ Submodule.span k S) :
    ∃ (m : ℕ) (f : Fin m → T), (∀ i, f i ∈ S) ∧ x = ∑ i, f i := by
  induction hx using Submodule.span_induction with
  | mem s hs => exact ⟨1, fun _ => s, fun _ => hs, by simp⟩
  | zero => exact ⟨0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, f, hf, rfl⟩ := hx
    obtain ⟨n, g, hg, rfl⟩ := hy
    refine ⟨m + n, Fin.append f g, ?_, by simp [Fin.sum_univ_add]⟩
    exact Fin.addCases (fun i => by simpa using hf i) (fun j => by simpa using hg j)
  | smul c x _ hx =>
    obtain ⟨n, f, hf, rfl⟩ := hx
    exact ⟨n, fun i => c • f i, fun i => hS c _ (hf i), by rw [Finset.smul_sum]⟩

include hA hB in
/-- A mixed cocycle of total Čech degree `d` is congruent modulo
mixed boundaries to a sum of products in complementary Čech degrees. -/
theorem mixedCech_kunneth (d : ℕ) {z : Finset (ι ⊕ₗ κ) → E ⊗[k] M}
    (hz : z ∈ (C).Z ((d : ℤ) + 2)) :
    ∃ (m : ℕ) (q : Fin m → ℕ) (a : Fin m → Finset ι → E) (b : Fin m → Finset κ → M),
      (∀ j, q j ≤ d ∧ a j ∈ (cech A).Z ((d - q j : ℕ) : ℤ) ∧ b j ∈ (cech B).Z (q j)) ∧
      z - ∑ j, cechJoin μ (a j) (b j) ∈ (C).B ((d : ℤ) + 2) := by
  let n : ℤ := (d : ℤ) + 2
  have hterm (s : Finset (ι ⊕ₗ κ)) :
      z s ∈ (if (s.card : ℤ) = n then joinedTensorCoefficients A B s else ⊥) := by
    rw [joinedTensorCoefficients_eq]
    exact acx_mem_terms_iff.mp hz.1 s
  have hsupport (s : Finset (ι ⊕ₗ κ)) (hs : (s.card : ℤ) ≠ n) : z s = 0 :=
    (Submodule.mem_bot k).mp (by simpa only [if_neg hs] using hterm s)
  have hc (s : Finset (ι ⊕ₗ κ)) : z s ∈ joinedTensorCoefficients A B s := by
    by_cases hs : (s.card : ℤ) = n
    · simpa only [if_pos hs] using hterm s
    · rw [hsupport s hs]
      exact zero_mem _
  obtain ⟨t, ht⟩ := exists_tensorToJoined A B z hc
  have ht' : t ∈ tensorDegree G G' n :=
    tensorDegree_of_joined_support hA hB t (fun s hs => (congrFun ht s).trans (hsupport s hs))
  have hdt : tensorDifferential G G' t = 0 := by
    apply tensorToJoined_injective A B
    rw [tensorToJoined_differential hA hB, ht, map_zero, ← wd_one]
    exact hz.2
  obtain ⟨v, hv, htv⟩ := tensor_kunneth G G' n t ht' hdt
  let S : Set (Finset (ι ⊕ₗ κ) → E ⊗[k] M) :=
    {w | ∃ (q : ℕ) (_ : q ≤ d) (a : Finset ι → E) (b : Finset κ → M),
      a ∈ (cech A).Z ((d - q : ℕ) : ℤ) ∧ b ∈ (cech B).Z q ∧ w = cechJoin μ a b}
  have hS : ∀ c : k, ∀ x ∈ S, c • x ∈ S := by
    rintro r _ ⟨q, hq, a, b, ha, hb, rfl⟩
    refine ⟨q, hq, r • a, b, Submodule.smul_mem _ _ ha, hb, ?_⟩
    funext s
    simp only [cechJoin, Pi.smul_apply, map_smul, LinearMap.smul_apply]
  have hspan (u : regularCochains A ⊗[k] regularCochains B) (hu : u ∈ tensorCycleSpan G G' n) :
      tensorToJoined A B u ∈ Submodule.span k S := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨a, b, p, q, hp, hq, hdeg, hda, hdb, rfl⟩ := hu
      rcases p with _ | p
      · rw [(G).zero] at hp
        rw [← hp, TensorProduct.zero_tmul, map_zero]
        exact zero_mem _
      rcases q with _ | q
      · rw [(G').zero] at hq
        rw [← hq, TensorProduct.tmul_zero, map_zero]
        exact zero_mem _
      have hqd : q ≤ d := by dsimp only [n] at hdeg; omega
      have hpd : p = d - q := by dsimp only [n] at hdeg; omega
      refine Submodule.subset_span ⟨q, hqd, a.val, b.val, ?_,
        cech_cycle_of_projected_cycle B hB b hq hdb, tensorToJoined_tmul A B a b⟩
      simpa only [hpd] using cech_cycle_of_projected_cycle A hA a hp hda
    | zero => rw [map_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact Submodule.smul_mem _ r hu
  obtain ⟨m, f, hf, hf'⟩ := exists_finite_sum_of_span S hS (hspan _ htv)
  choose q hq a b ha hb he using fun j => hf j
  refine ⟨m, q, a, b, fun j => ⟨hq j, ha j, hb j⟩, ?_⟩
  have e : (∑ j, f j) = ∑ j, cechJoin μ (a j) (b j) :=
    Finset.sum_congr rfl fun j _ => he j
  rw [← e]
  rw [map_sub, ht, tensorToJoined_differential hA hB, ← wd_one] at hf'
  rw [← hf', sub_sub_cancel]
  refine ⟨tensorToJoined A B v, acx_mem_terms_iff.mpr (fun s => ?_), rfl⟩
  by_cases hs : (s.card : ℤ) = n - 1
  · rw [if_pos hs]
    simpa only [joinedTensorCoefficients_eq] using tensorToJoined_mem A B v s
  · rw [if_neg hs, tensorToJoined_support hA hB hv s hs]
    exact zero_mem _

end GlobalTheory.WH
