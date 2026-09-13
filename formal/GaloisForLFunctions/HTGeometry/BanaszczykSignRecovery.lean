import GaloisForLFunctions.HTGeometry.OpenBanaszczykTransform

/-!
# Finite sign recovery from open Banaszczyk transforms

This file isolates the finite backward-induction argument in Corollary 2.3.  It does not assume
the analytic stability theorem: the exact interface is membership of zero in the iterated
transform.  Symmetry, convexity, and nonemptiness supply that membership.
-/

open Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Successive open Banaszczyk transforms along a finite list of vectors. -/
def iteratedOpenBanaszczykTransform : Set E → List E → Set E
  | K, [] => K
  | K, v :: vs => iteratedOpenBanaszczykTransform (openBanaszczykTransform K v) vs

/-- `x` is a sum obtained by assigning either sign to every vector in the list. -/
inductive IsSignedSum : List E → E → Prop
  | nil : IsSignedSum [] 0
  | add {v : E} {vs : List E} {x : E} :
      IsSignedSum vs x → IsSignedSum (v :: vs) (x + v)
  | sub {v : E} {vs : List E} {x : E} :
      IsSignedSum vs x → IsSignedSum (v :: vs) (x - v)

@[simp] theorem iteratedOpenBanaszczykTransform_nil (K : Set E) :
    iteratedOpenBanaszczykTransform K [] = K := rfl

@[simp] theorem iteratedOpenBanaszczykTransform_cons (K : Set E) (v : E) (vs : List E) :
    iteratedOpenBanaszczykTransform K (v :: vs) =
      iteratedOpenBanaszczykTransform (openBanaszczykTransform K v) vs := rfl

theorem convex_iteratedOpenBanaszczykTransform {K : Set E} (hK : Convex ℝ K) :
    ∀ vs, Convex ℝ (iteratedOpenBanaszczykTransform K vs) := by
  intro vs
  induction vs generalizing K with
  | nil => exact hK
  | cons v vs ih =>
      exact ih (convex_openBanaszczykTransform hK v)

theorem neg_iteratedOpenBanaszczykTransform_eq {K : Set E} (hK : -K = K) :
    ∀ vs, -(iteratedOpenBanaszczykTransform K vs) =
      iteratedOpenBanaszczykTransform K vs := by
  intro vs
  induction vs generalizing K with
  | nil => exact hK
  | cons v vs ih =>
      exact ih (neg_openBanaszczykTransform_eq hK v)

theorem zero_mem_of_convex_of_neg_eq {K : Set E} (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hneg : -K = K) : 0 ∈ K := by
  obtain ⟨x, hx⟩ := hne
  have hnx : -x ∈ K := by
    rw [← hneg]
    exact Set.neg_mem_neg.mpr hx
  have hmid := hconv hx hnx (show 0 ≤ (1 / 2 : ℝ) by linarith)
    (show 0 ≤ (1 / 2 : ℝ) by linarith) (by ring)
  convert hmid using 1
  module

/-- Backward induction: zero in the final transform produces a signed sum in the initial set. -/
theorem exists_isSignedSum_mem_of_zero_mem_iterated {K : Set E} (hK : Convex ℝ K) :
    ∀ (vs : List E), 0 ∈ iteratedOpenBanaszczykTransform K vs →
      ∃ x ∈ K, IsSignedSum vs x := by
  intro vs
  induction vs generalizing K with
  | nil =>
      intro hzero
      exact ⟨0, hzero, IsSignedSum.nil⟩
  | cons v vs ih =>
      intro hzero
      obtain ⟨x, hx, hsigned⟩ := ih (convex_openBanaszczykTransform hK v) hzero
      have hcontain := openBanaszczykTransform_subset_translate_union hK v hx
      rcases hcontain with hminus | hplus
      · rcases hminus with ⟨k, hk, w, hw, hkw⟩
        rw [mem_singleton_iff] at hw
        subst w
        have hkx : k = x + v := by
          rw [← hkw]
          module
        refine ⟨k, hk, ?_⟩
        rw [hkx]
        exact IsSignedSum.add hsigned
      · rcases hplus with ⟨k, hk, w, hw, hkw⟩
        rw [mem_singleton_iff] at hw
        subst w
        have hkx : k = x - v := by
          rw [← hkw]
          module
        refine ⟨k, hk, ?_⟩
        rw [hkx]
        exact IsSignedSum.sub hsigned

/-- Purely geometric form of the symmetric-target signing reduction. -/
theorem exists_isSignedSum_mem_of_iterated_nonempty {K : Set E} (hK : Convex ℝ K)
    (hneg : -K = K) (vs : List E)
    (hne : (iteratedOpenBanaszczykTransform K vs).Nonempty) :
    ∃ x ∈ K, IsSignedSum vs x := by
  apply exists_isSignedSum_mem_of_zero_mem_iterated hK vs
  exact zero_mem_of_convex_of_neg_eq
    (convex_iteratedOpenBanaszczykTransform hK vs) hne
    (neg_iteratedOpenBanaszczykTransform_eq hneg vs)

/-- A zero step leaves every stage unchanged. -/
@[simp] theorem iteratedOpenBanaszczykTransform_zeros (K : Set E) :
    ∀ n : ℕ, iteratedOpenBanaszczykTransform K (List.replicate n 0) = K := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- Closed sanity application: every finite zero-vector family signs into every nonempty
origin-symmetric convex target. -/
theorem exists_zero_signedSum_mem_openBall (n : ℕ) :
    ∃ x ∈ Metric.ball (0 : E) 1, IsSignedSum (List.replicate n 0) x := by
  apply exists_isSignedSum_mem_of_iterated_nonempty (convex_ball 0 1) (neg_ball_zero_eq 1)
  rw [iteratedOpenBanaszczykTransform_zeros]
  exact ⟨0, by simp⟩

/-- Sum selected by an explicit Boolean sign list. A length mismatch maps to zero. -/
def signedListSum : List E → List Bool → E
  | [], _ => 0
  | _, [] => 0
  | v :: vs, sign :: signs =>
      (if sign then v else -v) + signedListSum vs signs

omit [NormedSpace ℝ E] in
theorem IsSignedSum.exists_signs {vs : List E} {x : E} (hx : IsSignedSum vs x) :
    ∃ signs : List Bool, signs.length = vs.length ∧ signedListSum vs signs = x := by
  induction hx with
  | nil =>
      exact ⟨[], rfl, rfl⟩
  | @add v vs x hx ih =>
      obtain ⟨signs, hlength, hsign⟩ := ih
      refine ⟨true :: signs, by simp [hlength], ?_⟩
      simp only [signedListSum, if_true]
      rw [hsign]
      exact add_comm v x
  | @sub v vs x hx ih =>
      obtain ⟨signs, hlength, hsign⟩ := ih
      refine ⟨false :: signs, by simp [hlength], ?_⟩
      simp only [signedListSum]
      rw [hsign]
      rw [sub_eq_add_neg]
      exact add_comm (-v) x

/-- Explicit Boolean-sign version of the symmetric-target recovery theorem. -/
theorem exists_signedListSum_mem_of_iterated_nonempty {K : Set E} (hK : Convex ℝ K)
    (hneg : -K = K) (vs : List E)
    (hne : (iteratedOpenBanaszczykTransform K vs).Nonempty) :
    ∃ signs : List Bool, signs.length = vs.length ∧ signedListSum vs signs ∈ K := by
  obtain ⟨x, hx, hsigned⟩ := exists_isSignedSum_mem_of_iterated_nonempty hK hneg vs hne
  obtain ⟨signs, hlength, hsign⟩ := hsigned.exists_signs
  exact ⟨signs, hlength, hsign ▸ hx⟩

theorem mem_openCoordinateCube_iff_norm_lt {ι : Type*} [Fintype ι]
    {C : ℝ} (hC : 0 < C) {x : ι → ℝ} :
    x ∈ openCoordinateCube ι C ↔ ‖x‖ < C := by
  rw [mem_openCoordinateCube, pi_norm_lt_iff hC]
  simp only [Real.norm_eq_abs]

theorem mem_komlosCube_iff_norm_lt {d : ℕ} {x : Fin d → ℝ} :
    x ∈ komlosCube d ↔ ‖x‖ < komlosCubeRadius := by
  exact mem_openCoordinateCube_iff_norm_lt komlosCubeRadius_pos

/-- Conditional only on geometric survival; no analytic stability theorem is assumed. -/
theorem komlos_sign_recovery_of_iterated_nonempty (d : ℕ)
    (vs : List (Fin d → ℝ))
    (hne : (iteratedOpenBanaszczykTransform (komlosCube d) vs).Nonempty) :
    ∃ signs : List Bool, signs.length = vs.length ∧
      ‖signedListSum vs signs‖ < komlosCubeRadius := by
  obtain ⟨signs, hlength, hmem⟩ :=
    exists_signedListSum_mem_of_iterated_nonempty
      (convex_openCoordinateCube _ _) (neg_openCoordinateCube_eq _ _) vs hne
  exact ⟨signs, hlength, mem_komlosCube_iff_norm_lt.mp hmem⟩

/-- Fully closed zero-family instance of the dimension-free cube bound. -/
theorem komlos_zero_family_signing (d n : ℕ) :
    ∃ signs : List Bool, signs.length = n ∧
      ‖signedListSum (List.replicate n (0 : Fin d → ℝ)) signs‖ < komlosCubeRadius := by
  have hne : (iteratedOpenBanaszczykTransform (komlosCube d)
      (List.replicate n (0 : Fin d → ℝ))).Nonempty := by
    rw [iteratedOpenBanaszczykTransform_zeros]
    exact komlosCube_nonempty d
  simpa using komlos_sign_recovery_of_iterated_nonempty d
    (List.replicate n (0 : Fin d → ℝ)) hne

end GaloisForLFunctions.HTGeometry
