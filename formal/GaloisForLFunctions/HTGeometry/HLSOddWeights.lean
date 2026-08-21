import GaloisForLFunctions.HTGeometry.HLSGradedSymmetry
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Weights of the odd part of an HLS graded symmetry

The odd part `V` of an `HLSGradedSymmetry` is a module over the complexified Lorentz
algebra `𝔰𝔩₂ ⊕ 𝔰𝔩₂`.  This file computes its joint generalized `(h, h̄)`-weights and shows
that they are confined to

  `(0, 0)`, `(1, 0)`, `(-1, 0)`, `(0, 1)`, `(0, -1)`,

i.e. the odd part is a sum of Lorentz scalars and Weyl spinors `(½,0) ⊕ (0,½)`.  This is
the first half of the Haag--Łopuszański--Sohnius theorem, and it needs neither Weyl's
complete-reducibility theorem nor `𝔰𝔩₂` highest-weight theory: positivity of the odd
sector plus the explicit weights of `𝔤₀` do all the work.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

/-- Intertwined powers: if `A' T = T A` then `A'ᵏ T = T Aᵏ`. -/
theorem hlsPowIntertwine {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A A' T : Module.End ℂ W) (h : A' * T = T * A) : ∀ k : ℕ, A' ^ k * T = T * A ^ k
  | 0 => by simp
  | k + 1 => by
      rw [pow_succ, pow_succ, mul_assoc, h, ← mul_assoc, hlsPowIntertwine A A' T h k, mul_assoc]

namespace HLSGradedSymmetry

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (S : HLSGradedSymmetry B V)

/-- Joint generalized `(h, h̄)`-weight space of the odd part. -/
def wt (a b : ℂ) : Submodule ℂ V :=
  S.hL.maxGenEigenspace a ⊓ S.hR.maxGenEigenspace b

theorem mem_wt {a b : ℂ} {v : V} :
    v ∈ S.wt a b ↔ (∃ k : ℕ, ((S.hL - a • (1 : Module.End ℂ V)) ^ k) v = 0) ∧
      (∃ m : ℕ, ((S.hR - b • (1 : Module.End ℂ V)) ^ m) v = 0) := by
  simp [wt]

/-- A linear operator with prescribed commutators against the two Cartan generators
shifts joint generalized weight spaces accordingly. -/
theorem shift_mem_wt {a b a' b' : ℂ} (T : Module.End ℂ V)
    (h1 : S.hL * T - T * S.hL = (a' - a) • T)
    (h2 : S.hR * T - T * S.hR = (b' - b) • T)
    {v : V} (hv : v ∈ S.wt a b) : T v ∈ S.wt a' b' := by
  rw [mem_wt] at hv ⊢
  obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := hv
  have e1 : ∀ c : ℂ, (c • (1 : Module.End ℂ V)) * T = c • T := by
    intro c; rw [smul_mul_assoc, one_mul]
  have e2 : ∀ c : ℂ, T * (c • (1 : Module.End ℂ V)) = c • T := by
    intro c; rw [mul_smul_comm, mul_one]
  have k1 : (S.hL - a' • (1 : Module.End ℂ V)) * T = T * (S.hL - a • (1 : Module.End ℂ V)) := by
    rw [sub_mul, mul_sub, e1, e2]
    have : S.hL * T = T * S.hL + (a' - a) • T := by rw [← h1]; abel
    rw [this, sub_smul]
    abel
  have k2 : (S.hR - b' • (1 : Module.End ℂ V)) * T = T * (S.hR - b • (1 : Module.End ℂ V)) := by
    rw [sub_mul, mul_sub, e1, e2]
    have : S.hR * T = T * S.hR + (b' - b) • T := by rw [← h2]; abel
    rw [this, sub_smul]
    abel
  refine ⟨⟨k, ?_⟩, ⟨m, ?_⟩⟩
  · have hp := congrArg (fun U : Module.End ℂ V => U v) (hlsPowIntertwine _ _ _ k1 k)
    simp only [Module.End.mul_apply] at hp
    rw [hp, hk, map_zero]
  · have hp := congrArg (fun U : Module.End ℂ V => U v) (hlsPowIntertwine _ _ _ k2 m)
    simp only [Module.End.mul_apply] at hp
    rw [hp, hm, map_zero]

theorem hR_eL_comm : S.hR * S.eL = S.eL * S.hR := (S.LL_RR_commute hlsSl2E hlsSl2H).symm

theorem hR_fL_comm : S.hR * S.fL = S.fL * S.hR := (S.LL_RR_commute hlsSl2F hlsSl2H).symm

theorem hL_eR_comm : S.hL * S.eR = S.eR * S.hL := S.LL_RR_commute hlsSl2H hlsSl2E

theorem hL_fR_comm : S.hL * S.fR = S.fR * S.hL := S.LL_RR_commute hlsSl2H hlsSl2F

theorem hL_hR_comm : S.hL * S.hR = S.hR * S.hL := S.LL_RR_commute hlsSl2H hlsSl2H

private theorem comm_zero_smul (T U : Module.End ℂ V) (c : ℂ) (h : T * U = U * T) :
    T * U - U * T = c • (0 : Module.End ℂ V) := by rw [h, sub_self, smul_zero]

/-- The undotted raising operator shifts the undotted weight by `+2`. -/
theorem eL_mem_wt {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) : S.eL v ∈ S.wt (a + 2) b := by
  refine S.shift_mem_wt S.eL ?_ ?_ hv
  · rw [S.hL_eL]; congr 1; ring
  · rw [S.hR_eL_comm, sub_self, sub_self, zero_smul]

/-- The undotted lowering operator shifts the undotted weight by `-2`. -/
theorem fL_mem_wt {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) : S.fL v ∈ S.wt (a - 2) b := by
  refine S.shift_mem_wt S.fL ?_ ?_ hv
  · rw [S.hL_fL]; congr 1; ring
  · rw [S.hR_fL_comm, sub_self, sub_self, zero_smul]

/-- The dotted raising operator shifts the dotted weight by `+2`. -/
theorem eR_mem_wt {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) : S.eR v ∈ S.wt a (b + 2) := by
  refine S.shift_mem_wt S.eR ?_ ?_ hv
  · rw [S.hL_eR_comm, sub_self, sub_self, zero_smul]
  · rw [S.hR_eR]; congr 1; ring

/-- The dotted lowering operator shifts the dotted weight by `-2`. -/
theorem fR_mem_wt {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) : S.fR v ∈ S.wt a (b - 2) := by
  refine S.shift_mem_wt S.fR ?_ ?_ hv
  · rw [S.hL_fR_comm, sub_self, sub_self, zero_smul]
  · rw [S.hR_fR]; congr 1; ring

/-- The Cartan generators preserve every joint weight space. -/
theorem hL_mem_wt {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) : S.hL v ∈ S.wt a b := by
  refine S.shift_mem_wt S.hL ?_ ?_ hv
  · rw [sub_self, sub_self, zero_smul]
  · rw [← S.hL_hR_comm, sub_self, sub_self, zero_smul]

theorem hR_mem_wt {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) : S.hR v ∈ S.wt a b := by
  refine S.shift_mem_wt S.hR ?_ ?_ hv
  · rw [S.hL_hR_comm, sub_self, sub_self, zero_smul]
  · rw [sub_self, sub_self, zero_smul]


theorem oddConj_hR_sub (b : ℂ) (v : V) :
    S.oddConj ((S.hR - b • (1 : Module.End ℂ V)) v)
      = (S.hL - (starRingEnd ℂ b) • (1 : Module.End ℂ V)) (S.oddConj v) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub]
  rw [S.oddConj_hR v]
  congr 1
  exact map_smulₛₗ S.oddConj b v

theorem oddConj_hL_sub (a : ℂ) (v : V) :
    S.oddConj ((S.hL - a • (1 : Module.End ℂ V)) v)
      = (S.hR - (starRingEnd ℂ a) • (1 : Module.End ℂ V)) (S.oddConj v) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub]
  rw [S.oddConj_hL v]
  congr 1
  exact map_smulₛₗ S.oddConj a v

theorem oddConj_pow_hR (b : ℂ) (k : ℕ) (v : V) :
    S.oddConj (((S.hR - b • (1 : Module.End ℂ V)) ^ k) v)
      = ((S.hL - (starRingEnd ℂ b) • (1 : Module.End ℂ V)) ^ k) (S.oddConj v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, S.oddConj_hR_sub, ← Module.End.mul_apply,
        ← pow_succ]

theorem oddConj_pow_hL (a : ℂ) (k : ℕ) (v : V) :
    S.oddConj (((S.hL - a • (1 : Module.End ℂ V)) ^ k) v)
      = ((S.hR - (starRingEnd ℂ a) • (1 : Module.End ℂ V)) ^ k) (S.oddConj v) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, S.oddConj_hL_sub, ← Module.End.mul_apply,
        ← pow_succ]

/-- The real form exchanges the dotted and undotted weights. -/
theorem oddConj_mem_wt {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) :
    S.oddConj v ∈ S.wt (starRingEnd ℂ b) (starRingEnd ℂ a) := by
  rw [mem_wt] at hv ⊢
  obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := hv
  refine ⟨⟨m, ?_⟩, ⟨k, ?_⟩⟩
  · rw [← S.oddConj_pow_hR b m v, hm, map_zero]
  · rw [← S.oddConj_pow_hL a k v, hk, map_zero]

/-- The three weights allowed on the diagonal of the even algebra. -/
def hlsAdmissible (c : ℂ) : Prop := c = 0 ∨ c = 1 ∨ c = -1

/-- **Positivity confines the joint weights of the odd part.**  For a nonzero joint
generalized weight vector of weight `(a, b)`, the combination `a + b̄` is `0`, `1` or `-1`. -/
theorem wt_constraint {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) (hv0 : v ≠ 0) :
    hlsAdmissible (a + starRingEnd ℂ b) := by
  by_contra hcon
  rw [hlsAdmissible] at hcon
  simp only [not_or] at hcon
  obtain ⟨h0, h1, hm1⟩ := hcon
  have hstar := S.oddConj_mem_wt hv
  rw [mem_wt] at hv hstar
  obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := hv
  obtain ⟨⟨k', hk'⟩, ⟨m', hm'⟩⟩ := hstar
  have hX1 : ((hlsEvenAdL B - (a + starRingEnd ℂ b) • (1 : Module.End ℂ (HLSEven B))) ^ (k + k'))
      (S.br v (S.oddConj v)) = 0 :=
    hlsGenEigen_bilinear S.br S.hL S.hL (hlsEvenAdL B) a (starRingEnd ℂ b) S.adL_br
      k k' v (S.oddConj v) hk hk'
  have hX2 : ((hlsEvenAdR B - (b + starRingEnd ℂ a) • (1 : Module.End ℂ (HLSEven B))) ^ (m + m'))
      (S.br v (S.oddConj v)) = 0 :=
    hlsGenEigen_bilinear S.br S.hR S.hR (hlsEvenAdR B) b (starRingEnd ℂ a) S.adR_br
      m m' v (S.oddConj v) hm hm'
  have hc2 : b + starRingEnd ℂ a = starRingEnd ℂ (a + starRingEnd ℂ b) := by
    simp only [map_add, Complex.conj_conj]
    ring
  have hne : b + starRingEnd ℂ a ≠ 0 := by
    rw [hc2]
    intro hz
    exact h0 (by simpa using congrArg (starRingEnd ℂ) hz)
  exact S.br_oddConj_ne_zero hv0
    (hlsEven_joint_weight_eq_zero h0 h1 hm1 hne _ _ _ hX1 hX2)

/-- On a joint weight space, a genuine `h`-eigenvalue must equal the generalized one. -/
theorem hL_eigen_eq {a b c : ℂ} {v : V} (hv : v ∈ S.wt a b) (hv0 : v ≠ 0)
    (h : S.hL v = c • v) : a = c := by
  rw [mem_wt] at hv
  obtain ⟨⟨k, hk⟩, -⟩ := hv
  have key : ∀ n : ℕ, ((S.hL - a • (1 : Module.End ℂ V)) ^ n) v = (c - a) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Module.End.mul_apply]
        have hstep : (S.hL - a • (1 : Module.End ℂ V)) v = (c - a) • v := by
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h, sub_smul]
        rw [hstep, map_smul, ih, smul_smul, pow_succ]
        ring_nf
  rw [key k] at hk
  rcases smul_eq_zero.mp hk with h' | h'
  · have hk0 : k ≠ 0 := by rintro rfl; simp at h'
    exact (sub_eq_zero.mp ((pow_eq_zero_iff hk0).mp h')).symm
  · exact absurd h' hv0

theorem hR_eigen_eq {a b c : ℂ} {v : V} (hv : v ∈ S.wt a b) (hv0 : v ≠ 0)
    (h : S.hR v = c • v) : b = c := by
  rw [mem_wt] at hv
  obtain ⟨-, ⟨k, hk⟩⟩ := hv
  have key : ∀ n : ℕ, ((S.hR - b • (1 : Module.End ℂ V)) ^ n) v = (c - b) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Module.End.mul_apply]
        have hstep : (S.hR - b • (1 : Module.End ℂ V)) v = (c - b) • v := by
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h, sub_smul]
        rw [hstep, map_smul, ih, smul_smul, pow_succ]
        ring_nf
  rw [key k] at hk
  rcases smul_eq_zero.mp hk with h' | h'
  · have hk0 : k ≠ 0 := by rintro rfl; simp at h'
    exact (sub_eq_zero.mp ((pow_eq_zero_iff hk0).mp h')).symm
  · exact absurd h' hv0



theorem eL_fL_apply (v : V) : S.eL (S.fL v) - S.fL (S.eL v) = S.hL v := by
  have := congrArg (fun T : Module.End ℂ V => T v) S.eL_fL
  simpa [Module.End.mul_apply] using this

theorem eR_fR_apply (v : V) : S.eR (S.fR v) - S.fR (S.eR v) = S.hR v := by
  have := congrArg (fun T : Module.End ℂ V => T v) S.eR_fR
  simpa [Module.End.mul_apply] using this

theorem hL_fL_apply (v : V) : S.hL (S.fL v) - S.fL (S.hL v) = (-2 : ℂ) • S.fL v := by
  have := congrArg (fun T : Module.End ℂ V => T v) S.hL_fL
  simpa [Module.End.mul_apply] using this

theorem hL_eL_apply (v : V) : S.hL (S.eL v) - S.eL (S.hL v) = (2 : ℂ) • S.eL v := by
  have := congrArg (fun T : Module.End ℂ V => T v) S.hL_eL
  simpa [Module.End.mul_apply] using this

theorem hR_fR_apply (v : V) : S.hR (S.fR v) - S.fR (S.hR v) = (-2 : ℂ) • S.fR v := by
  have := congrArg (fun T : Module.End ℂ V => T v) S.hR_fR
  simpa [Module.End.mul_apply] using this

theorem hR_eR_apply (v : V) : S.hR (S.eR v) - S.eR (S.hR v) = (2 : ℂ) • S.eR v := by
  have := congrArg (fun T : Module.End ℂ V => T v) S.hR_eR
  simpa [Module.End.mul_apply] using this

theorem eL_zero_of {a b : ℂ} {v : V} (hv : v ∈ S.wt a b)
    (h : ¬ hlsAdmissible (a + starRingEnd ℂ b + 2)) : S.eL v = 0 := by
  by_contra hne
  refine h ?_
  have := S.wt_constraint (S.eL_mem_wt hv) hne
  have he : a + 2 + starRingEnd ℂ b = a + starRingEnd ℂ b + 2 := by ring
  rwa [he] at this

theorem fL_zero_of {a b : ℂ} {v : V} (hv : v ∈ S.wt a b)
    (h : ¬ hlsAdmissible (a + starRingEnd ℂ b - 2)) : S.fL v = 0 := by
  by_contra hne
  refine h ?_
  have := S.wt_constraint (S.fL_mem_wt hv) hne
  have he : a - 2 + starRingEnd ℂ b = a + starRingEnd ℂ b - 2 := by ring
  rwa [he] at this

theorem eR_zero_of {a b : ℂ} {v : V} (hv : v ∈ S.wt a b)
    (h : ¬ hlsAdmissible (a + starRingEnd ℂ b + 2)) : S.eR v = 0 := by
  by_contra hne
  refine h ?_
  have := S.wt_constraint (S.eR_mem_wt hv) hne
  have he : a + starRingEnd ℂ (b + 2) = a + starRingEnd ℂ b + 2 := by
    simp only [map_add, map_ofNat]
    ring
  rwa [he] at this

theorem fR_zero_of {a b : ℂ} {v : V} (hv : v ∈ S.wt a b)
    (h : ¬ hlsAdmissible (a + starRingEnd ℂ b - 2)) : S.fR v = 0 := by
  by_contra hne
  refine h ?_
  have := S.wt_constraint (S.fR_mem_wt hv) hne
  have he : a + starRingEnd ℂ (b - 2) = a + starRingEnd ℂ b - 2 := by
    simp only [map_sub, map_ofNat]
    ring
  rwa [he] at this

theorem not_admissible_two : ¬ hlsAdmissible (2 : ℂ) := by
  simp only [hlsAdmissible, not_or]
  norm_num

theorem not_admissible_neg_two : ¬ hlsAdmissible (-2 : ℂ) := by
  simp only [hlsAdmissible, not_or]
  norm_num

theorem not_admissible_three : ¬ hlsAdmissible (3 : ℂ) := by
  simp only [hlsAdmissible, not_or]
  norm_num

theorem not_admissible_neg_three : ¬ hlsAdmissible (-3 : ℂ) := by
  simp only [hlsAdmissible, not_or]
  norm_num



private theorem neg_two_smul_eq {W : Type*} [AddCommGroup W] [Module ℂ W] (x : W) :
    (-2 : ℂ) • x = -x - x := by
  rw [show (-2 : ℂ) = -(2 : ℂ) by norm_num, neg_smul, two_smul]
  abel

private theorem two_smul_eq {W : Type*} [AddCommGroup W] [Module ℂ W] (x : W) :
    (2 : ℂ) • x = x + x := two_smul ℂ x

/-- **HLS spin-½ theorem, weight form.**  Every nonzero joint generalized `(h, h̄)`-weight
vector of the odd part has weight `(0,0)`, `(1,0)`, `(-1,0)`, `(0,1)` or `(0,-1)`.
Equivalently: the odd part carries only Lorentz scalars and Weyl spinors `(½,0) ⊕ (0,½)`. -/
theorem wt_weights {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) (hv0 : v ≠ 0) :
    (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨
      (a = 0 ∧ b = -1) := by
  have hw := S.wt_constraint hv hv0
  rcases hw with hw | hw | hw
  · -- weight sum `0`: the Lorentz-scalar sector
    have heL : S.eL v = 0 := S.eL_zero_of hv (by rw [hw]; simpa using not_admissible_two)
    have hfL : S.fL v = 0 := S.fL_zero_of hv (by rw [hw]; simpa using not_admissible_neg_two)
    have heR : S.eR v = 0 := S.eR_zero_of hv (by rw [hw]; simpa using not_admissible_two)
    have hfR : S.fR v = 0 := S.fR_zero_of hv (by rw [hw]; simpa using not_admissible_neg_two)
    have hLv : S.hL v = (0 : ℂ) • v := by
      have h := S.eL_fL_apply v
      rw [heL, hfL, map_zero, map_zero, sub_zero] at h
      rw [← h, zero_smul]
    have hRv : S.hR v = (0 : ℂ) • v := by
      have h := S.eR_fR_apply v
      rw [heR, hfR, map_zero, map_zero, sub_zero] at h
      rw [← h, zero_smul]
    exact Or.inl ⟨S.hL_eigen_eq hv hv0 hLv, S.hR_eigen_eq hv hv0 hRv⟩
  · -- weight sum `1`
    have heLall : ∀ x, x ∈ S.wt a b → S.eL x = 0 := fun x hx =>
      S.eL_zero_of hx (by rw [hw, show (1 : ℂ) + 2 = 3 by norm_num]
                          exact not_admissible_three)
    have hfLv : S.fL v ∈ S.wt (a - 2) b := S.fL_mem_wt hv
    have hff : S.fL (S.fL v) = 0 := by
      refine S.fL_zero_of hfLv ?_
      have he : a - 2 + starRingEnd ℂ b - 2 = -3 := by linear_combination hw
      rw [he]
      exact not_admissible_neg_three
    have hLv : S.hL v = S.eL (S.fL v) := by
      have h := S.eL_fL_apply v
      rw [heLall v hv, map_zero, sub_zero] at h
      exact h.symm
    have hLfLv : S.hL (S.fL v) = -S.fL (S.hL v) := by
      have h := S.eL_fL_apply (S.fL v)
      rw [hff, map_zero, ← hLv] at h
      rw [← h, zero_sub]
    have hcomm := S.hL_fL_apply v
    rw [hLfLv] at hcomm
    have key : S.fL (S.hL v) = S.fL v := by
      have h2 : (-2 : ℂ) • S.fL (S.hL v) = (-2 : ℂ) • S.fL v := by
        rw [neg_two_smul_eq, hcomm]
      exact smul_right_injective V (by norm_num : (-2 : ℂ) ≠ 0) h2
    have hu_mem : S.hL v - v ∈ S.wt a b := Submodule.sub_mem _ (S.hL_mem_wt hv) hv
    have hfLu : S.fL (S.hL v - v) = 0 := by rw [map_sub, key, sub_self]
    have heLu : S.eL (S.hL v - v) = 0 := heLall _ hu_mem
    have hLu : S.hL (S.hL v - v) = 0 := by
      have h := S.eL_fL_apply (S.hL v - v)
      rw [hfLu, heLu, map_zero, map_zero, sub_zero] at h
      exact h.symm
    by_cases hu0 : S.hL v - v = 0
    · have hv1 : S.hL v = (1 : ℂ) • v := by
        rw [one_smul]
        exact sub_eq_zero.mp hu0
      have ha : a = 1 := S.hL_eigen_eq hv hv0 hv1
      have hb : b = 0 := by
        have hcb : starRingEnd ℂ b = 0 := by rw [ha] at hw; linear_combination hw
        simpa using congrArg (starRingEnd ℂ) hcb
      exact Or.inr (Or.inl ⟨ha, hb⟩)
    · have ha : a = 0 := S.hL_eigen_eq hu_mem hu0 (by rw [hLu, zero_smul])
      have hb : b = 1 := by
        have hcb : starRingEnd ℂ b = 1 := by rw [ha] at hw; linear_combination hw
        simpa using congrArg (starRingEnd ℂ) hcb
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha, hb⟩)))
  · -- weight sum `-1`
    have hfLall : ∀ x, x ∈ S.wt a b → S.fL x = 0 := fun x hx =>
      S.fL_zero_of hx (by rw [hw, show (-1 : ℂ) - 2 = -3 by norm_num]
                          exact not_admissible_neg_three)
    have heLv : S.eL v ∈ S.wt (a + 2) b := S.eL_mem_wt hv
    have hee : S.eL (S.eL v) = 0 := by
      refine S.eL_zero_of heLv ?_
      have he : a + 2 + starRingEnd ℂ b + 2 = 3 := by linear_combination hw
      rw [he]
      exact not_admissible_three
    have hLv : S.hL v = -S.fL (S.eL v) := by
      have h := S.eL_fL_apply v
      rw [hfLall v hv, map_zero, zero_sub] at h
      exact h.symm
    have hLeLv : S.hL (S.eL v) = -S.eL (S.hL v) := by
      have h := S.eL_fL_apply (S.eL v)
      rw [hee, map_zero, sub_zero] at h
      rw [← h, hLv, map_neg, neg_neg]
    have hcomm := S.hL_eL_apply v
    rw [hLeLv] at hcomm
    have key : S.eL (S.hL v) = -S.eL v := by
      have h2 : (-2 : ℂ) • S.eL (S.hL v) = (-2 : ℂ) • (-S.eL v) := by
        rw [neg_two_smul_eq, neg_two_smul_eq]
        rw [show -S.eL (S.hL v) - S.eL (S.hL v) = -(S.eL (S.hL v) + S.eL (S.hL v)) by abel]
        rw [show - -S.eL v - -S.eL v = S.eL v + S.eL v by abel]
        have : S.eL (S.hL v) + S.eL (S.hL v) = -(S.eL v + S.eL v) := by
          have := hcomm
          rw [two_smul_eq] at this
          linear_combination (norm := abel) -this
        rw [this, neg_neg]
      exact smul_right_injective V (by norm_num : (-2 : ℂ) ≠ 0) h2
    have hu_mem : S.hL v + v ∈ S.wt a b := Submodule.add_mem _ (S.hL_mem_wt hv) hv
    have heLu : S.eL (S.hL v + v) = 0 := by rw [map_add, key, neg_add_cancel]
    have hfLu : S.fL (S.hL v + v) = 0 := hfLall _ hu_mem
    have hLu : S.hL (S.hL v + v) = 0 := by
      have h := S.eL_fL_apply (S.hL v + v)
      rw [hfLu, heLu, map_zero, map_zero, sub_zero] at h
      exact h.symm
    by_cases hu0 : S.hL v + v = 0
    · have hv1 : S.hL v = (-1 : ℂ) • v := by
        rw [neg_one_smul]
        exact eq_neg_of_add_eq_zero_left hu0
      have ha : a = -1 := S.hL_eigen_eq hv hv0 hv1
      have hb : b = 0 := by
        have hcb : starRingEnd ℂ b = 0 := by rw [ha] at hw; linear_combination hw
        simpa using congrArg (starRingEnd ℂ) hcb
      exact Or.inr (Or.inr (Or.inl ⟨ha, hb⟩))
    · have ha : a = 0 := S.hL_eigen_eq hu_mem hu0 (by rw [hLu, zero_smul])
      have hb : b = -1 := by
        have hcb : starRingEnd ℂ b = -1 := by rw [ha] at hw; linear_combination hw
        have := congrArg (starRingEnd ℂ) hcb
        simpa using this
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb⟩)))



/-- A weight not on the HLS list carries no odd generator at all. -/
theorem wt_eq_bot {a b : ℂ}
    (h : ¬((a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨
      (a = 0 ∧ b = -1))) : S.wt a b = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  exact h (S.wt_weights hv hv0)

theorem eL_zero_of_bot {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) (h : S.wt (a + 2) b = ⊥) :
    S.eL v = 0 := by
  have := S.eL_mem_wt hv
  rw [h, Submodule.mem_bot] at this
  exact this

theorem fL_zero_of_bot {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) (h : S.wt (a - 2) b = ⊥) :
    S.fL v = 0 := by
  have := S.fL_mem_wt hv
  rw [h, Submodule.mem_bot] at this
  exact this

theorem eR_zero_of_bot {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) (h : S.wt a (b + 2) = ⊥) :
    S.eR v = 0 := by
  have := S.eR_mem_wt hv
  rw [h, Submodule.mem_bot] at this
  exact this

theorem fR_zero_of_bot {a b : ℂ} {v : V} (hv : v ∈ S.wt a b) (h : S.wt a (b - 2) = ⊥) :
    S.fR v = 0 := by
  have := S.fR_mem_wt hv
  rw [h, Submodule.mem_bot] at this
  exact this

private theorem wt_bot_30 : S.wt ((1 : ℂ) + 2) 0 = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_m30 : S.wt ((-1 : ℂ) - 2) 0 = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_m10_down : S.wt ((-1 : ℂ) - 2) 0 = ⊥ := S.wt_bot_m30

private theorem wt_bot_12 : S.wt (1 : ℂ) ((0 : ℂ) + 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_1m2 : S.wt (1 : ℂ) ((0 : ℂ) - 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_m12 : S.wt (-1 : ℂ) ((0 : ℂ) + 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_m1m2 : S.wt (-1 : ℂ) ((0 : ℂ) - 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_20 : S.wt ((0 : ℂ) + 2) 0 = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_m20 : S.wt ((0 : ℂ) - 2) 0 = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_02 : S.wt (0 : ℂ) ((0 : ℂ) + 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_0m2 : S.wt (0 : ℂ) ((0 : ℂ) - 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_21 : S.wt ((0 : ℂ) + 2) 1 = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_m21 : S.wt ((0 : ℂ) - 2) 1 = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_2m1 : S.wt ((0 : ℂ) + 2) (-1) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_m2m1 : S.wt ((0 : ℂ) - 2) (-1) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_03up : S.wt (0 : ℂ) ((1 : ℂ) + 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

private theorem wt_bot_0m3 : S.wt (0 : ℂ) ((-1 : ℂ) - 2) = ⊥ := by
  refine S.wt_eq_bot ?_
  norm_num

/-- On the undotted highest-weight sector the Cartan generator acts as `+1` exactly. -/
theorem hL_eq_on_wt_pos {v : V} (hv : v ∈ S.wt 1 0) : S.hL v = v := by
  have heL : ∀ x, x ∈ S.wt (1 : ℂ) 0 → S.eL x = 0 := fun x hx => S.eL_zero_of_bot hx S.wt_bot_30
  have hfLv : S.fL v ∈ S.wt ((1 : ℂ) - 2) 0 := S.fL_mem_wt hv
  have hfLv' : S.fL v ∈ S.wt (-1 : ℂ) 0 := by
    have : (1 : ℂ) - 2 = -1 := by norm_num
    rwa [this] at hfLv
  have hff : S.fL (S.fL v) = 0 := S.fL_zero_of_bot hfLv' S.wt_bot_m30
  have hLv : S.hL v = S.eL (S.fL v) := by
    have h := S.eL_fL_apply v
    rw [heL v hv, map_zero, sub_zero] at h
    exact h.symm
  have hLfLv : S.hL (S.fL v) = -S.fL (S.hL v) := by
    have h := S.eL_fL_apply (S.fL v)
    rw [hff, map_zero, ← hLv] at h
    rw [← h, zero_sub]
  have hcomm := S.hL_fL_apply v
  rw [hLfLv] at hcomm
  have key : S.fL (S.hL v) = S.fL v := by
    have h2 : (-2 : ℂ) • S.fL (S.hL v) = (-2 : ℂ) • S.fL v := by
      rw [neg_two_smul_eq, hcomm]
    exact smul_right_injective V (by norm_num : (-2 : ℂ) ≠ 0) h2
  have hu_mem : S.hL v - v ∈ S.wt (1 : ℂ) 0 := Submodule.sub_mem _ (S.hL_mem_wt hv) hv
  have hfLu : S.fL (S.hL v - v) = 0 := by rw [map_sub, key, sub_self]
  have heLu : S.eL (S.hL v - v) = 0 := heL _ hu_mem
  have hLu : S.hL (S.hL v - v) = 0 := by
    have h := S.eL_fL_apply (S.hL v - v)
    rw [hfLu, heLu, map_zero, map_zero, sub_zero] at h
    exact h.symm
  by_contra hne
  have hu0 : S.hL v - v ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have : (1 : ℂ) = 0 := S.hL_eigen_eq hu_mem hu0 (by rw [hLu, zero_smul])
  exact one_ne_zero this

/-- On the undotted lowest-weight sector the Cartan generator acts as `-1` exactly. -/
theorem hL_eq_on_wt_neg {v : V} (hv : v ∈ S.wt (-1) 0) : S.hL v = -v := by
  have hfL : ∀ x, x ∈ S.wt (-1 : ℂ) 0 → S.fL x = 0 := fun x hx => S.fL_zero_of_bot hx S.wt_bot_m30
  have heLv : S.eL v ∈ S.wt ((-1 : ℂ) + 2) 0 := S.eL_mem_wt hv
  have heLv' : S.eL v ∈ S.wt (1 : ℂ) 0 := by
    have h : (-1 : ℂ) + 2 = 1 := by norm_num
    rwa [h] at heLv
  have hee : S.eL (S.eL v) = 0 := S.eL_zero_of_bot heLv' S.wt_bot_30
  have hLv : S.hL v = -S.fL (S.eL v) := by
    have h := S.eL_fL_apply v
    rw [hfL v hv, map_zero, zero_sub] at h
    exact h.symm
  have hLeLv : S.hL (S.eL v) = -S.eL (S.hL v) := by
    have h := S.eL_fL_apply (S.eL v)
    rw [hee, map_zero, sub_zero] at h
    rw [← h, hLv, map_neg, neg_neg]
  have hcomm := S.hL_eL_apply v
  rw [hLeLv] at hcomm
  have key : S.eL (S.hL v) = -S.eL v := by
    have h2 : (-2 : ℂ) • S.eL (S.hL v) = (-2 : ℂ) • (-S.eL v) := by
      rw [neg_two_smul_eq, neg_two_smul_eq]
      rw [show -S.eL (S.hL v) - S.eL (S.hL v) = -(S.eL (S.hL v) + S.eL (S.hL v)) by abel]
      rw [show - -S.eL v - -S.eL v = S.eL v + S.eL v by abel]
      have hcc : S.eL (S.hL v) + S.eL (S.hL v) = -(S.eL v + S.eL v) := by
        have h3 := hcomm
        rw [two_smul_eq] at h3
        linear_combination (norm := abel) -h3
      rw [hcc, neg_neg]
    exact smul_right_injective V (by norm_num : (-2 : ℂ) ≠ 0) h2
  have hu_mem : S.hL v + v ∈ S.wt (-1 : ℂ) 0 := Submodule.add_mem _ (S.hL_mem_wt hv) hv
  have heLu : S.eL (S.hL v + v) = 0 := by rw [map_add, key, neg_add_cancel]
  have hfLu : S.fL (S.hL v + v) = 0 := hfL _ hu_mem
  have hLu : S.hL (S.hL v + v) = 0 := by
    have h := S.eL_fL_apply (S.hL v + v)
    rw [hfLu, heLu, map_zero, map_zero, sub_zero] at h
    exact h.symm
  by_contra hne
  have hu0 : S.hL v + v ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
  have : (-1 : ℂ) = 0 := S.hL_eigen_eq hu_mem hu0 (by rw [hLu, zero_smul])
  norm_num at this



/-- On the dotted highest-weight sector the dotted Cartan acts as `+1` exactly. -/
theorem hR_eq_on_wt_pos {v : V} (hv : v ∈ S.wt 0 1) : S.hR v = v := by
  have heR : ∀ x, x ∈ S.wt (0 : ℂ) 1 → S.eR x = 0 := fun x hx => S.eR_zero_of_bot hx S.wt_bot_03up
  have hfRv : S.fR v ∈ S.wt (0 : ℂ) ((1 : ℂ) - 2) := S.fR_mem_wt hv
  have hfRv' : S.fR v ∈ S.wt (0 : ℂ) (-1) := by
    have h : (1 : ℂ) - 2 = -1 := by norm_num
    rwa [h] at hfRv
  have hff : S.fR (S.fR v) = 0 := S.fR_zero_of_bot hfRv' S.wt_bot_0m3
  have hRv : S.hR v = S.eR (S.fR v) := by
    have h := S.eR_fR_apply v
    rw [heR v hv, map_zero, sub_zero] at h
    exact h.symm
  have hRfRv : S.hR (S.fR v) = -S.fR (S.hR v) := by
    have h := S.eR_fR_apply (S.fR v)
    rw [hff, map_zero, ← hRv] at h
    rw [← h, zero_sub]
  have hcomm := S.hR_fR_apply v
  rw [hRfRv] at hcomm
  have key : S.fR (S.hR v) = S.fR v := by
    have h2 : (-2 : ℂ) • S.fR (S.hR v) = (-2 : ℂ) • S.fR v := by
      rw [neg_two_smul_eq, hcomm]
    exact smul_right_injective V (by norm_num : (-2 : ℂ) ≠ 0) h2
  have hu_mem : S.hR v - v ∈ S.wt (0 : ℂ) 1 := Submodule.sub_mem _ (S.hR_mem_wt hv) hv
  have hfRu : S.fR (S.hR v - v) = 0 := by rw [map_sub, key, sub_self]
  have heRu : S.eR (S.hR v - v) = 0 := heR _ hu_mem
  have hRu : S.hR (S.hR v - v) = 0 := by
    have h := S.eR_fR_apply (S.hR v - v)
    rw [hfRu, heRu, map_zero, map_zero, sub_zero] at h
    exact h.symm
  by_contra hne
  have hu0 : S.hR v - v ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have : (1 : ℂ) = 0 := S.hR_eigen_eq hu_mem hu0 (by rw [hRu, zero_smul])
  exact one_ne_zero this

/-- On the dotted lowest-weight sector the dotted Cartan acts as `-1` exactly. -/
theorem hR_eq_on_wt_neg {v : V} (hv : v ∈ S.wt 0 (-1)) : S.hR v = -v := by
  have hfR : ∀ x, x ∈ S.wt (0 : ℂ) (-1) → S.fR x = 0 := fun x hx =>
    S.fR_zero_of_bot hx S.wt_bot_0m3
  have heRv : S.eR v ∈ S.wt (0 : ℂ) ((-1 : ℂ) + 2) := S.eR_mem_wt hv
  have heRv' : S.eR v ∈ S.wt (0 : ℂ) 1 := by
    have h : (-1 : ℂ) + 2 = 1 := by norm_num
    rwa [h] at heRv
  have hee : S.eR (S.eR v) = 0 := S.eR_zero_of_bot heRv' S.wt_bot_03up
  have hRv : S.hR v = -S.fR (S.eR v) := by
    have h := S.eR_fR_apply v
    rw [hfR v hv, map_zero, zero_sub] at h
    exact h.symm
  have hReRv : S.hR (S.eR v) = -S.eR (S.hR v) := by
    have h := S.eR_fR_apply (S.eR v)
    rw [hee, map_zero, sub_zero] at h
    rw [← h, hRv, map_neg, neg_neg]
  have hcomm := S.hR_eR_apply v
  rw [hReRv] at hcomm
  have key : S.eR (S.hR v) = -S.eR v := by
    have h2 : (-2 : ℂ) • S.eR (S.hR v) = (-2 : ℂ) • (-S.eR v) := by
      rw [neg_two_smul_eq, neg_two_smul_eq]
      rw [show -S.eR (S.hR v) - S.eR (S.hR v) = -(S.eR (S.hR v) + S.eR (S.hR v)) by abel]
      rw [show - -S.eR v - -S.eR v = S.eR v + S.eR v by abel]
      have hcc : S.eR (S.hR v) + S.eR (S.hR v) = -(S.eR v + S.eR v) := by
        have h3 := hcomm
        rw [two_smul_eq] at h3
        linear_combination (norm := abel) -h3
      rw [hcc, neg_neg]
    exact smul_right_injective V (by norm_num : (-2 : ℂ) ≠ 0) h2
  have hu_mem : S.hR v + v ∈ S.wt (0 : ℂ) (-1) := Submodule.add_mem _ (S.hR_mem_wt hv) hv
  have heRu : S.eR (S.hR v + v) = 0 := by rw [map_add, key, neg_add_cancel]
  have hfRu : S.fR (S.hR v + v) = 0 := hfR _ hu_mem
  have hRu : S.hR (S.hR v + v) = 0 := by
    have h := S.eR_fR_apply (S.hR v + v)
    rw [hfRu, heRu, map_zero, map_zero, sub_zero] at h
    exact h.symm
  by_contra hne
  have hu0 : S.hR v + v ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
  have : (-1 : ℂ) = 0 := S.hR_eigen_eq hu_mem hu0 (by rw [hRu, zero_smul])
  norm_num at this

/-- The dotted Lorentz algebra acts trivially on the undotted spinor sector. -/
theorem hR_zero_on_wt_pos {v : V} (hv : v ∈ S.wt 1 0) : S.hR v = 0 := by
  have heR : S.eR v = 0 := S.eR_zero_of_bot hv S.wt_bot_12
  have hfR : S.fR v = 0 := S.fR_zero_of_bot hv S.wt_bot_1m2
  have h := S.eR_fR_apply v
  rw [heR, hfR, map_zero, map_zero, sub_zero] at h
  exact h.symm

theorem hR_zero_on_wt_neg {v : V} (hv : v ∈ S.wt (-1) 0) : S.hR v = 0 := by
  have heR : S.eR v = 0 := S.eR_zero_of_bot hv S.wt_bot_m12
  have hfR : S.fR v = 0 := S.fR_zero_of_bot hv S.wt_bot_m1m2
  have h := S.eR_fR_apply v
  rw [heR, hfR, map_zero, map_zero, sub_zero] at h
  exact h.symm

/-- The undotted Lorentz algebra acts trivially on the dotted spinor sector. -/
theorem hL_zero_on_wt_dotPos {v : V} (hv : v ∈ S.wt 0 1) : S.hL v = 0 := by
  have heL : S.eL v = 0 := S.eL_zero_of_bot hv S.wt_bot_21
  have hfL : S.fL v = 0 := S.fL_zero_of_bot hv S.wt_bot_m21
  have h := S.eL_fL_apply v
  rw [heL, hfL, map_zero, map_zero, sub_zero] at h
  exact h.symm

theorem hL_zero_on_wt_dotNeg {v : V} (hv : v ∈ S.wt 0 (-1)) : S.hL v = 0 := by
  have heL : S.eL v = 0 := S.eL_zero_of_bot hv S.wt_bot_2m1
  have hfL : S.fL v = 0 := S.fL_zero_of_bot hv S.wt_bot_m2m1
  have h := S.eL_fL_apply v
  rw [heL, hfL, map_zero, map_zero, sub_zero] at h
  exact h.symm

/-- The Lorentz algebra acts trivially on the scalar sector. -/
theorem hL_zero_on_wt_scalar {v : V} (hv : v ∈ S.wt 0 0) : S.hL v = 0 := by
  have heL : S.eL v = 0 := S.eL_zero_of_bot hv S.wt_bot_20
  have hfL : S.fL v = 0 := S.fL_zero_of_bot hv S.wt_bot_m20
  have h := S.eL_fL_apply v
  rw [heL, hfL, map_zero, map_zero, sub_zero] at h
  exact h.symm

theorem hR_zero_on_wt_scalar {v : V} (hv : v ∈ S.wt 0 0) : S.hR v = 0 := by
  have heR : S.eR v = 0 := S.eR_zero_of_bot hv S.wt_bot_02
  have hfR : S.fR v = 0 := S.fR_zero_of_bot hv S.wt_bot_0m2
  have h := S.eR_fR_apply v
  rw [heR, hfR, map_zero, map_zero, sub_zero] at h
  exact h.symm

/-- The lowering operator maps the undotted highest-weight sector into the lowest-weight one. -/
theorem fL_mem_wt_pos {v : V} (hv : v ∈ S.wt 1 0) : S.fL v ∈ S.wt (-1) 0 := by
  have := S.fL_mem_wt hv
  have h : (1 : ℂ) - 2 = -1 := by norm_num
  rwa [h] at this

theorem eL_mem_wt_neg {v : V} (hv : v ∈ S.wt (-1) 0) : S.eL v ∈ S.wt 1 0 := by
  have := S.eL_mem_wt hv
  have h : (-1 : ℂ) + 2 = 1 := by norm_num
  rwa [h] at this

/-- `e` and `f` are mutually inverse on the two undotted spinor sectors. -/
theorem eL_fL_id_pos {v : V} (hv : v ∈ S.wt 1 0) : S.eL (S.fL v) = v := by
  have heL : S.eL v = 0 := S.eL_zero_of_bot hv S.wt_bot_30
  have h := S.eL_fL_apply v
  rw [heL, map_zero, sub_zero, S.hL_eq_on_wt_pos hv] at h
  exact h

theorem fL_eL_id_neg {v : V} (hv : v ∈ S.wt (-1) 0) : S.fL (S.eL v) = v := by
  have hfL : S.fL v = 0 := S.fL_zero_of_bot hv S.wt_bot_m30
  have h := S.eL_fL_apply v
  rw [hfL, map_zero, zero_sub, S.hL_eq_on_wt_neg hv] at h
  exact neg_injective h

/-- The real form exchanges the undotted and dotted spinor sectors. -/
theorem oddConj_mem_wt_pos {v : V} (hv : v ∈ S.wt 1 0) : S.oddConj v ∈ S.wt 0 1 := by
  have := S.oddConj_mem_wt hv
  simpa using this

theorem oddConj_mem_wt_dotPos {v : V} (hv : v ∈ S.wt 0 1) : S.oddConj v ∈ S.wt 1 0 := by
  have := S.oddConj_mem_wt hv
  simpa using this

theorem oddConj_mem_wt_neg {v : V} (hv : v ∈ S.wt (-1) 0) : S.oddConj v ∈ S.wt 0 (-1) := by
  have := S.oddConj_mem_wt hv
  simpa using this

theorem oddConj_mem_wt_dotNeg {v : V} (hv : v ∈ S.wt 0 (-1)) : S.oddConj v ∈ S.wt (-1) 0 := by
  have := S.oddConj_mem_wt hv
  simpa using this

theorem oddConj_mem_wt_scalar {v : V} (hv : v ∈ S.wt 0 0) : S.oddConj v ∈ S.wt 0 0 := by
  have := S.oddConj_mem_wt hv
  simpa using this



section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- The odd part is spanned by its joint generalized `(h, h̄)`-weight spaces. -/
theorem wt_iSup_eq_top : ⨆ p : ℂ × ℂ, S.wt p.1 p.2 = ⊤ := by
  classical
  set f : Fin 2 → Module.End ℂ V := ![S.hL, S.hR] with hf
  have hf0 : f 0 = S.hL := rfl
  have hf1 : f 1 = S.hR := rfl
  have hcomm : Pairwise fun i j => Commute (f i) (f j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (show Commute S.hL S.hR; exact S.hL_hR_comm)
      | (show Commute S.hR S.hL; exact S.hL_hR_comm.symm)
  have htop : ∀ i, ⨆ μ, (f i).maxGenEigenspace μ = ⊤ := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hkey :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hcomm htop
  rw [eq_top_iff, ← hkey]
  refine iSup_le fun χ => ?_
  refine le_trans ?_ (le_iSup (fun p : ℂ × ℂ => S.wt p.1 p.2) (χ 0, χ 1))
  intro v hv
  rw [Submodule.mem_iInf] at hv
  exact ⟨by simpa [hf0] using hv 0, by simpa [hf1] using hv 1⟩

/-- **The odd part is a sum of Lorentz scalars and Weyl spinors.**  The five HLS weight
spaces span the whole odd part. -/
theorem wt_sectors_eq_top :
    S.wt 0 0 ⊔ (S.wt 1 0 ⊔ (S.wt (-1) 0 ⊔ (S.wt 0 1 ⊔ S.wt 0 (-1)))) = ⊤ := by
  rw [eq_top_iff, ← S.wt_iSup_eq_top]
  refine iSup_le fun p => ?_
  by_cases h : (p.1 = 0 ∧ p.2 = 0) ∨ (p.1 = 1 ∧ p.2 = 0) ∨ (p.1 = -1 ∧ p.2 = 0) ∨
      (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 = 0 ∧ p.2 = -1)
  · obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ := h <;> rw [h1, h2]
    · exact le_sup_left
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_right (le_sup_of_le_right le_sup_left)
    · exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_left))
    · exact le_sup_of_le_right (le_sup_of_le_right (le_sup_of_le_right le_sup_right))
  · rw [S.wt_eq_bot h]
    exact bot_le

end FiniteDimensional


end HLSGradedSymmetry

end GaloisForLFunctions.HTGeometry
