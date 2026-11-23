import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GradedTensorContraction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex

/-! Alternating Čech cochains with chart coefficients form a finite
grading by the cardinality of intersections. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.CechDR

variable {k ι E : Type} [Field k] [LinearOrder ι] [AddCommGroup E] [Module k E]

/-- Cochains with chart coefficients, vanishing on the empty index set. -/
def regularCochains (F : Finset ι → Submodule k E) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty then F s else ⊥

theorem mem_regularCochains {F : Finset ι → Submodule k E} {a : Finset ι → E} : a ∈ regularCochains F ↔ a ∅ = 0 ∧ ∀ s, a s ∈ F s := by
  constructor
  · intro h
    have h' : ∀ s, a s ∈ (if s.Nonempty then F s else ⊥) := fun s => (Submodule.mem_pi.1 h) s (Set.mem_univ _)
    have h0 : a ∅ = 0 := by simpa using h' ∅
    refine ⟨h0, fun s => ?_⟩
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [h0]
      exact zero_mem _
    · simpa [hs] using h' s
  · rintro ⟨h0, h⟩
    refine Submodule.mem_pi.2 fun s _ => ?_
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using h0
    · simpa [hs] using h s

variable (k ι E) in

def cardProjection (c : ℕ) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun s => if s.card = c then LinearMap.proj s else 0

variable (k ι E) in

def cardParity : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • LinearMap.proj s

theorem cardProjection_apply (c : ℕ) (a : Finset ι → E) (s : Finset ι) : cardProjection k ι E c a s = if s.card = c then a s else 0 := by
  simp only [cardProjection, LinearMap.pi_apply]
  split_ifs <;> simp

theorem cardParity_apply (a : Finset ι → E) (s : Finset ι) : cardParity k ι E a s = ((-1 : ℤ) ^ s.card) • a s := by
  simp [cardParity]

theorem delta_mem {F : Finset ι → Submodule k E} (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t)
    (a : Finset ι → E) (ha : a ∈ regularCochains F) : deltaL k ι E a ∈ regularCochains F := by
  obtain ⟨h0, h⟩ := mem_regularCochains.1 ha
  refine mem_regularCochains.2 ⟨by simp [deltaL_apply], fun s => ?_⟩
  rw [deltaL_apply]
  refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
  rcases (s.erase i).eq_empty_or_nonempty with h1 | h1
  · rw [h1, h0]
    exact zero_mem _
  · exact hF _ _ h1 (Finset.erase_subset _ _) (h _)

theorem cardProjection_mem {F : Finset ι → Submodule k E} (c : ℕ) (a : Finset ι → E) (ha : a ∈ regularCochains F) :
    cardProjection k ι E c a ∈ regularCochains F := by
  obtain ⟨h0, h⟩ := mem_regularCochains.1 ha
  refine mem_regularCochains.2 ⟨by simp [cardProjection_apply, h0], fun s => ?_⟩
  rw [cardProjection_apply]
  split_ifs
  · exact h s
  · exact zero_mem _

theorem cardParity_mem {F : Finset ι → Submodule k E} (a : Finset ι → E) (ha : a ∈ regularCochains F) :
    cardParity k ι E a ∈ regularCochains F := by
  obtain ⟨h0, h⟩ := mem_regularCochains.1 ha
  refine mem_regularCochains.2 ⟨by simp [cardParity_apply, h0], fun s => ?_⟩
  rw [cardParity_apply]
  exact zsmul_mem (h s) _

/-- Grade the chart cochains by the cardinality of their index sets. -/
def gradedCech [Fintype ι] (F : Finset ι → Submodule k E) (hF : ∀ s t, s.Nonempty → s ⊆ t → F s ≤ F t) : FiniteGradedComplex k (regularCochains F) where
  d := (deltaL k ι E).restrict (delta_mem hF)
  π c := (cardProjection k ι E c).restrict (cardProjection_mem c)
  σ := (cardParity k ι E).restrict cardParity_mem
  N := Fintype.card ι + 1
  dd a := Subtype.ext (cechDModule_cechDModule ℤ a.1)
  idem c a := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, cardProjection_apply]
    split_ifs <;> rfl
  orth c c' a h := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, cardProjection_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    split_ifs with h1 h2
    · exact absurd (h1.symm.trans h2) h
    · rfl
    · rfl
  sum a := by
    refine Subtype.ext (funext fun s => ?_)
    have hs : s.card < Fintype.card ι + 1 := Nat.lt_succ_of_le (Finset.card_le_univ s)
    simp [cardProjection_apply, Finset.sum_apply, hs]
  zero a := by
    refine Subtype.ext (funext fun s => ?_)
    have h0 := (mem_regularCochains.1 a.2).1
    simp only [LinearMap.restrict_coe_apply, cardProjection_apply, ZeroMemClass.coe_zero, Pi.zero_apply]
    split_ifs with h
    · rw [Finset.card_eq_zero.1 h]
      exact h0
    · rfl
  dπ c a := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, cardProjection_apply, deltaL_apply]
    split_ifs with h
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [if_pos]
      rw [Finset.card_erase_of_mem hi]
      omega
    · refine Finset.sum_eq_zero fun i hi => ?_
      rw [if_neg, smul_zero]
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
  σπ c a := by
    refine Subtype.ext (funext fun s => ?_)
    simp only [LinearMap.restrict_coe_apply, cardProjection_apply, cardParity_apply, Submodule.coe_smul_of_tower, Pi.smul_apply]
    split_ifs with h
    · rw [h]
    · simp

theorem gradedCech_d_apply [Fintype ι] (A : Finset ι → Submodule k E)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
    (a : regularCochains A) (s : Finset ι) :
    ((gradedCech A hA).d a).val s = deltaL k ι E a.val s := rfl

theorem gradedCech_parity_apply [Fintype ι] (A : Finset ι → Submodule k E)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
    (a : regularCochains A) (s : Finset ι) :
    ((gradedCech A hA).σ a).val s = (-1 : ℤ) ^ s.card • a.val s :=
  cardParity_apply _ _

theorem gradedCech_projection_apply [Fintype ι] (A : Finset ι → Submodule k E)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t)
    (p : ℕ) (a : regularCochains A) (s : Finset ι) :
    ((gradedCech A hA).π p a).val s = if s.card = p then a.val s else 0 :=
  cardProjection_apply _ _ _

end GlobalTheory.CechDR
