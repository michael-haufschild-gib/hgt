import GaloisForLFunctions.HTGeometry.BorelWeil.FlagCech
import Mathlib.LinearAlgebra.Quotient.Basic

/-! A graded Čech complex realized in the space of all set-indexed cochains. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory

variable {ι : Type*} [LinearOrder ι]

/-- The integer sign of deleting an index from an ordered intersection. -/
abbrev cubeSign (s : Finset ι) (i : ι) : ℤ := cechSign s i

theorem cubeSign_mul_erase {s : Finset ι} {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (h : i ≠ j) :
    cubeSign s i * cubeSign (s.erase i) j = - (cubeSign s j * cubeSign (s.erase j) i) :=
  add_eq_zero_iff_eq_neg.mp (cechSign_erase_add hi hj h)

end GlobalTheory

namespace GlobalTheory.CechDR

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Graded terms and a common differential in an ambient module. -/
structure Cx (k M : Type*) [Field k] [AddCommGroup M] [Module k M] where
  C : ℤ → Submodule k M
  D : M →ₗ[k] M

namespace Cx

/-- The differential raises degree and squares to zero on the graded terms. -/
def IsCx (K : Cx k M) : Prop :=
  ∀ n, ∀ a ∈ K.C n, K.D a ∈ K.C (n + 1) ∧ K.D (K.D a) = 0

/-- The cycles of a given degree. -/
def Z (K : Cx k M) (n : ℤ) : Submodule k M := K.C n ⊓ LinearMap.ker K.D

/-- The boundaries of a given degree. -/
def B (K : Cx k M) (n : ℤ) : Submodule k M := (K.C (n - 1)).map K.D

/-- The cohomology of a given degree. -/
abbrev H (K : Cx k M) (n : ℤ) : Type _ := K.Z n ⧸ (K.B n).submoduleOf (K.Z n)

theorem boundaries_le_cycles {K : Cx k M} (h : K.IsCx) (n : ℤ) : K.B n ≤ K.Z n := by
  intro a ha
  change a ∈ (K.C (n - 1)).map K.D at ha
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp ha
  obtain ⟨hDb, hDDb⟩ := h (n - 1) b hb
  exact ⟨sub_add_cancel n 1 ▸ hDb, LinearMap.mem_ker.mpr hDDb⟩

end Cx

/-- A map of the ambient modules respecting the graded differential. -/
def IsMap (K : Cx k M) (L : Cx k N) (f : M →ₗ[k] N) : Prop :=
  ∀ n, ∀ a ∈ K.C n, f a ∈ L.C n ∧ f (K.D a) = L.D (f a)

/-- A map of complexes induces the map of the cycle quotients. -/
def Cx.hmap (K : Cx k M) (L : Cx k N) (f : M →ₗ[k] N) (hf : IsMap K L f)
    (n : ℤ) : K.H n →ₗ[k] L.H n :=
  Submodule.mapQ _ _ (f.restrict (p := K.Z n) (q := L.Z n) fun a ha => by
    refine ⟨(hf n a ha.1).1, ?_⟩
    change L.D (f a) = 0
    rw [← (hf n a ha.1).2, show K.D a = 0 from ha.2, map_zero])
    (by
      rintro ⟨a, ha⟩ hb
      change a ∈ (K.C (n - 1)).map K.D at hb
      obtain ⟨c, hc, e⟩ := Submodule.mem_map.mp hb
      refine ⟨f c, (hf (n - 1) c hc).1, ?_⟩
      change L.D (f c) = f a
      rw [← (hf (n - 1) c hc).2, e])

variable {ι : Type*} [LinearOrder ι]

/-- The alternating Čech differential on the ambient space of cochains. -/
def deltaL (k ι M : Type*) [Field k] [LinearOrder ι] [AddCommGroup M] [Module k M] :
    (Finset ι → M) →ₗ[k] (Finset ι → M) where
  toFun := cechDModule ℤ
  map_add' a b := by
    funext s
    simp only [cechDModule, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    funext s
    simp only [cechDModule, RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

theorem deltaL_apply (a : Finset ι → M) (s : Finset ι) :
    deltaL k ι M a s = ∑ i ∈ s, cubeSign s i • a (s.erase i) := rfl

/-- A cochain of degree `n` is supported on nonempty intersections of
cardinality `n + 1` with values in the corresponding chart modules. -/
def cechC (A : Finset ι → Submodule k M) (n : ℤ) : Submodule k (Finset ι → M) :=
  Submodule.pi Set.univ fun s => if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥

/-- The graded Čech complex attached to a family of chart submodules. -/
def cech (A : Finset ι → Submodule k M) : Cx k (Finset ι → M) :=
  ⟨cechC A, deltaL k ι M⟩

/-- The Čech differential respects the grading when restriction is
inclusion into the module of the smaller open. -/
theorem cech_isCx_of_mono (A : Finset ι → Submodule k M)
    (hA : ∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) : (cech A).IsCx := by
  intro n a ha
  have ha' (s : Finset ι) : a s ∈
      (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥) :=
    (Submodule.mem_pi.mp ha) s (Set.mem_univ _)
  refine ⟨?_, cechDModule_cechDModule ℤ a⟩
  refine Submodule.mem_pi.mpr fun t _ => ?_
  change deltaL k ι M a t ∈ (if t.Nonempty ∧ (t.card : ℤ) = n + 1 + 1 then A t else ⊥)
  rw [deltaL_apply]
  split_ifs with ht
  · refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
    have h := ha' (t.erase i)
    split_ifs at h with h'
    · exact hA _ _ h'.1 (Finset.erase_subset _ _) h
    · rw [Submodule.mem_bot] at h
      rw [h]
      exact zero_mem _
  · rw [Submodule.mem_bot]
    refine Finset.sum_eq_zero fun i hi => ?_
    have h := ha' (t.erase i)
    split_ifs at h with h'
    · exact False.elim (ht ⟨⟨i, hi⟩, by
        have hcard := Finset.card_erase_add_one hi
        have hdeg := h'.2
        omega⟩)
    · rw [Submodule.mem_bot] at h
      rw [h, smul_zero]

/-- Pair cochains by the ordered cup product on the full intersection. -/
def cupPair [Fintype ι] (β : M →ₗ[k] N →ₗ[k] k) :
    (Finset ι → M) →ₗ[k] (Finset ι → N) →ₗ[k] k :=
  ∑ j : ι, β.compl₁₂ (LinearMap.proj (Finset.univ.filter (· ≤ j)))
    (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

end GlobalTheory.CechDR
