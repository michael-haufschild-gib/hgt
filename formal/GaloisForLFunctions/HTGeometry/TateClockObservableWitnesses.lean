import GaloisForLFunctions.HTGeometry.ClockDescentAnomaly

/-!
# Realizations of the finite-observable clock interface

Finite observability asks that a space of admissible clock variations realize arbitrary values on
every finite window.  The finitely supported variations already do: the indicator extension of a
finite window is finitely supported.  The property is monotone, so it also holds for the full
product.

Substituting the finitely supported variations removes the interface from the conormal no-go, the
product-density statement and the Hausdorff blindness theorem.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K]

/-- Clock variations with finite support. -/
def finiteSupportClockSubmodule (K : Type*) [Field K] : Submodule K (ℕ → K) where
  carrier := {f | (Function.support f).Finite}
  add_mem' hf hg := (hf.union hg).subset (Function.support_add _ _)
  zero_mem' := by simp
  smul_mem' c f hf := hf.subset fun n hn => by
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul] at hn ⊢
    exact fun h => hn (by rw [h, mul_zero])

theorem mem_finiteSupportClockSubmodule {f : ℕ → K} :
    f ∈ finiteSupportClockSubmodule K ↔ (Function.support f).Finite := Iff.rfl

/-- The indicator extension of a finite window is finitely supported. -/
theorem finiteWindowExtension_mem (s : Finset ℕ) (target : s → K) :
    (fun n => if h : n ∈ s then target ⟨n, h⟩ else 0) ∈ finiteSupportClockSubmodule K := by
  rw [mem_finiteSupportClockSubmodule]
  apply (s.finite_toSet).subset
  intro n hn
  by_contra hns
  rw [Function.mem_support] at hn
  exact hn (dif_neg (fun h => hns (Finset.mem_coe.mpr h)))

/-! ## Realizations -/

/-- **Finitely supported variations are finite-observably free.** -/
theorem tateClockFiniteObservableSurjective_finiteSupport :
    TateClockFiniteObservableSurjective (finiteSupportClockSubmodule K) := by
  intro s target
  refine ⟨⟨_, finiteWindowExtension_mem s target⟩, ?_⟩
  funext i
  exact dif_pos i.2

theorem tateClockFiniteObservableSurjective_of_le {W W' : Submodule K (ℕ → K)}
    (hle : W ≤ W') (hW : TateClockFiniteObservableSurjective W) :
    TateClockFiniteObservableSurjective W' := by
  intro s target
  obtain ⟨w, hw⟩ := hW s target
  exact ⟨⟨w.1, hle w.2⟩, hw⟩

theorem tateClockFiniteObservableSurjective_top :
    TateClockFiniteObservableSurjective (⊤ : Submodule K (ℕ → K)) :=
  tateClockFiniteObservableSurjective_of_le le_top
    tateClockFiniteObservableSurjective_finiteSupport

/-! ## The interface disappears from the no-go statements -/

/-- **Conormal no-go for finitely supported variations.**  A finitely supported clock covector
annihilating every finitely supported variation vanishes. -/
theorem tateClock_conormal_eq_zero_of_annihilates_finiteSupport
    (a : ℕ →₀ K)
    (ha : ∀ w : finiteSupportClockSubmodule K, tateClockPairing a w.1 = 0) :
    a = 0 :=
  tateClock_finiteObservable_conormal_eq_zero (finiteSupportClockSubmodule K)
    tateClockFiniteObservableSurjective_finiteSupport a ha

section Topology

variable [TopologicalSpace K]

/-- **Product density of finitely supported variations.** -/
theorem denseRange_finiteSupportClockSubmodule :
    DenseRange (finiteSupportClockSubmodule K).subtype :=
  denseRange_subtype_of_tateClockFiniteObservableSurjective
    (finiteSupportClockSubmodule K) tateClockFiniteObservableSurjective_finiteSupport

/-- **Hausdorff blindness for finitely supported variations.**  A continuous linear map to a
Hausdorff target vanishing on every finitely supported clock variation vanishes identically. -/
theorem continuousLinearMap_eq_zero_of_vanishing_on_finiteSupport
    {Q : Type*} [AddCommGroup Q] [Module K Q] [TopologicalSpace Q] [T2Space Q]
    (L : (ℕ → K) →ₗ[K] Q) (hL : Continuous L)
    (hzero : ∀ w : finiteSupportClockSubmodule K, L w.1 = 0) :
    L = 0 :=
  continuousLinearMap_eq_zero_of_tateClockFiniteObservableSurjective
    (finiteSupportClockSubmodule K) tateClockFiniteObservableSurjective_finiteSupport
    L hL hzero

end Topology

end GaloisForLFunctions.HTGeometry
