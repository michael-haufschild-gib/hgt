import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# The stalk Tor class of the Kummer square-zero quotient

Let `E` be the exterior algebra of a vector space, `m` its augmentation ideal and `I = m²` the
part of degree at least two, so that `E/I` is the square-zero algebra `k ⊕ V`.  The augmentation
base change of `E/I` is derived-nontrivial: the first Tor group is `I/mI`, and the graded structure
computes it as the second exterior power.  So the derived stalk of a unit-amalgamated pushout
carries an extra class whenever `Λ²V ≠ 0`.

* `deningerExtGe` : the part of degree at least `j`.
* `deningerExtGe_one_mul` : `m · Λ^{≥j} = Λ^{≥j+1}`; in particular `m² = I` and `mI = Λ^{≥3}`.
* `deningerExtSquare_inf_ge_three` : the degree-two part meets `mI` trivially.
* `deningerExtGe_two_eq_sup` : `I = Λ²V ⊕ mI`, so `I/mI ≅ Λ²V`.
* `deningerStalkTor_ne` : hence `I ≠ mI` whenever `Λ²V ≠ 0`.
-/

namespace RHTower

open scoped ExteriorAlgebra

section StalkTor

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- The part of the exterior algebra of degree at least `j`. -/
def deningerExtGe (j : ℕ) : Submodule k (ExteriorAlgebra k V) :=
  ⨆ n : {n : ℕ // j ≤ n}, (⋀[k]^(n : ℕ) V)

theorem deningerExtPow_le_extGe {j n : ℕ} (h : j ≤ n) :
    (⋀[k]^n V) ≤ deningerExtGe k V j :=
  le_iSup (fun n : {n : ℕ // j ≤ n} => (⋀[k]^(n : ℕ) V)) ⟨n, h⟩

theorem deningerExtGe_mono {i j : ℕ} (h : i ≤ j) :
    deningerExtGe k V j ≤ deningerExtGe k V i :=
  iSup_le fun n => deningerExtPow_le_extGe k V (le_trans h n.2)

/-- Products raise the degree. -/
theorem deningerExtGe_mul_le (i j : ℕ) :
    deningerExtGe k V i * deningerExtGe k V j ≤ deningerExtGe k V (i + j) := by
  refine Submodule.mul_le.mpr fun x hx y hy => ?_
  induction hx using Submodule.iSup_induction' with
  | mem n x hxn =>
    induction hy using Submodule.iSup_induction' with
    | mem m y hym =>
      have hmul : x * y ∈ (⋀[k]^((n : ℕ) + (m : ℕ)) V) :=
        SetLike.mul_mem_graded hxn hym
      exact deningerExtPow_le_extGe k V (by
        have := n.2
        have := m.2
        omega) hmul
    | zero => simp
    | add u v _ _ hu hv =>
      rw [mul_add]
      exact Submodule.add_mem _ hu hv
  | zero => simp
  | add u v _ _ hu hv =>
    rw [add_mul]
    exact Submodule.add_mem _ hu hv

/-- A single vector lies in degree one. -/
theorem deningerIota_mem_one (v : V) : ExteriorAlgebra.ι k v ∈ (⋀[k]^1 V) := by
  rw [← exteriorPower.ιMulti_span_fixedDegree]
  refine Submodule.subset_span ⟨fun _ => v, ?_⟩
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

theorem deningerIotaMulti_mem (n : ℕ) (v : Fin n → V) :
    ExteriorAlgebra.ιMulti k n v ∈ (⋀[k]^n V) := by
  rw [← exteriorPower.ιMulti_span_fixedDegree]
  exact Submodule.subset_span ⟨v, rfl⟩

/-- **The augmentation ideal times the degree-`≥j` part is the degree-`≥j+1` part.**  In particular
`m · m = I` and `m · I` is the degree-`≥3` part. -/
theorem deningerExtGe_one_mul (j : ℕ) (hj : 1 ≤ j) :
    deningerExtGe k V 1 * deningerExtGe k V j = deningerExtGe k V (j + 1) := by
  refine le_antisymm ?_ ?_
  · have h := deningerExtGe_mul_le k V 1 j
    rwa [add_comm 1 j] at h
  · refine iSup_le fun n => ?_
    obtain ⟨nv, hn⟩ := n
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, nv = m + 1 := ⟨nv - 1, by omega⟩
    have hmj : j ≤ m := by omega
    rw [← exteriorPower.ιMulti_span_fixedDegree]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, rfl⟩
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    exact Submodule.mul_mem_mul
      (deningerExtPow_le_extGe k V le_rfl (deningerIota_mem_one k V (v 0)))
      (deningerExtPow_le_extGe k V hmj (deningerIotaMulti_mem k V m (Matrix.vecTail v)))

/-- The graded projection kills the higher-degree part. -/
theorem deningerProj_two_of_ge_three {x : ExteriorAlgebra k V} (hx : x ∈ deningerExtGe k V 3) :
    GradedRing.proj (fun n => (⋀[k]^n V : Submodule k (ExteriorAlgebra k V))) 2 x = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem n x hxn =>
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne (fun m => (⋀[k]^m V : Submodule k (ExteriorAlgebra k V)))
        hxn (show (n : ℕ) ≠ 2 by have := n.2; omega)]
  | zero => simp
  | add u v _ _ hu hv =>
    rw [map_add, hu, hv, add_zero]

/-- **The degree-two part meets the higher part trivially.** -/
theorem deningerExtSquare_inf_ge_three :
    (⋀[k]^2 V) ⊓ deningerExtGe k V 3 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro x ⟨hx2, hx3⟩
  have h2 : GradedRing.proj (fun n => (⋀[k]^n V : Submodule k (ExteriorAlgebra k V))) 2 x = x := by
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same (fun m => (⋀[k]^m V : Submodule k (ExteriorAlgebra k V)))
        hx2]
  have h3 := deningerProj_two_of_ge_three k V hx3
  rw [h2] at h3
  exact h3

/-- **The degree-`≥2` part splits as the degree-two part plus the degree-`≥3` part**, so the
quotient `I/mI` is the second exterior power. -/
theorem deningerExtGe_two_eq_sup :
    deningerExtGe k V 2 = (⋀[k]^2 V) ⊔ deningerExtGe k V 3 := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n => ?_
    rcases eq_or_lt_of_le n.2 with h | h
    · have : (⋀[k]^(n : ℕ) V) = (⋀[k]^2 V) := by rw [← h]
      rw [this]
      exact le_sup_left
    · exact le_trans (deningerExtPow_le_extGe k V (by omega)) le_sup_right
  · refine sup_le ?_ (deningerExtGe_mono k V (by omega))
    exact deningerExtPow_le_extGe k V le_rfl

/-- The higher part dies in its own quotient. -/
theorem deningerExtGe_three_map_mkQ :
    (deningerExtGe k V 3).map (deningerExtGe k V 3).mkQ = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro _ ⟨x, hx, rfl⟩
  exact (Submodule.Quotient.mk_eq_zero _).mpr hx

/-- **`I/mI` is the image of the second exterior power.** -/
theorem deningerTor_map_eq :
    (deningerExtGe k V 2).map (deningerExtGe k V 3).mkQ
      = (⋀[k]^2 V).map (deningerExtGe k V 3).mkQ := by
  rw [deningerExtGe_two_eq_sup, Submodule.map_sup, deningerExtGe_three_map_mkQ, sup_bot_eq]

/-- **The second exterior power injects into `I/mI`.**  Together with `deningerTor_map_eq` this is
the identification `Tor₁ ≅ I/mI ≅ Λ²V`. -/
theorem deningerTor_injective :
    Function.Injective
      (fun x : (⋀[k]^2 V) => (deningerExtGe k V 3).mkQ (x : ExteriorAlgebra k V)) := by
  intro x y hxy
  have hsub : ((x : ExteriorAlgebra k V) - y) ∈ deningerExtGe k V 3 := by
    rw [← Submodule.Quotient.eq]
    exact hxy
  have hmem : ((x : ExteriorAlgebra k V) - y) ∈ (⋀[k]^2 V) ⊓ deningerExtGe k V 3 :=
    ⟨Submodule.sub_mem _ x.2 y.2, hsub⟩
  rw [deningerExtSquare_inf_ge_three] at hmem
  have : (x : ExteriorAlgebra k V) - y = 0 := hmem
  exact Subtype.ext (sub_eq_zero.mp this)

/-- **The stalk Tor obstruction.**  If the second exterior power is nonzero then the degree-`≥2`
part is strictly larger than `m` times itself, so the first Tor group of the augmentation base
change of `E/I` does not vanish. -/
theorem deningerStalkTor_ne (h : (⋀[k]^2 V) ≠ ⊥) :
    deningerExtGe k V 2 ≠ deningerExtGe k V 1 * deningerExtGe k V 2 := by
  rw [deningerExtGe_one_mul k V 2 (by omega)]
  intro hcon
  refine h ?_
  have hle : (⋀[k]^2 V) ≤ deningerExtGe k V 3 := by
    rw [← hcon]
    exact deningerExtPow_le_extGe k V le_rfl
  have := deningerExtSquare_inf_ge_three k V
  rwa [inf_eq_left.mpr hle] at this

end StalkTor

end RHTower
