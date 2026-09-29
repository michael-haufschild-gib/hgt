import Mathlib

/-!
# Polynomials proportional to prescribed vectors at finitely many points

Given `s` points `t_j ∈ ℂ` and vectors `v(·, j) ∈ ℂ^{m+1}`, each with a nonzero entry, the linear
system

`P_μ(t_j) = c_j · v(μ, j)`,   `0 ≤ μ ≤ m`, `1 ≤ j ≤ s`,

in the coefficients of polynomials `P_μ` of degree at most `D` and the scalars `c_j` has
`(m+1)(D+1) + s` unknowns and `(m+1)s` equations.  When the unknowns outnumber the equations it has
a nonzero solution, and in any nonzero solution some `P_μ` is nonzero: if every `P_μ` vanished, each
`c_j` would be killed by a nonzero entry of `v(·, j)`.

This is the interpolation step in Steinmetz's reduction theorem: with `v(μ, j) = F_μ(t_j)` and a
relation `Σ F_μ(g) h_μ = 0`, the function `Σ P_μ(g) h_μ` vanishes wherever `g` takes a value `t_j`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Polynomials of bounded degree proportional to prescribed vectors at prescribed points.** -/
theorem exists_polynomials_proportional_at_points {m s D : ℕ}
    (hdim : (m + 1) * s < (m + 1) * (D + 1) + s) (t : Fin s → ℂ) (v : Fin (m + 1) → Fin s → ℂ)
    (hv : ∀ j, ∃ μ, v μ j ≠ 0) :
    ∃ (P : Fin (m + 1) → Polynomial ℂ) (c : Fin s → ℂ), (∃ μ, P μ ≠ 0) ∧
      (∀ μ, (P μ).natDegree ≤ D) ∧ ∀ μ j, (P μ).eval (t j) = c j * v μ j := by
  classical
  -- the linear system
  let L : ((Fin (m + 1) → Fin (D + 1) → ℂ) × (Fin s → ℂ)) →ₗ[ℂ] (Fin (m + 1) → Fin s → ℂ) :=
    { toFun := fun x μ j => (∑ i : Fin (D + 1), x.1 μ i * t j ^ (i : ℕ)) - x.2 j * v μ j
      map_add' := fun x y => by
        funext μ j
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun a x => by
        funext μ j
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [mul_sub, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring }
  have hrank : Module.finrank ℂ (Fin (m + 1) → Fin s → ℂ)
      < Module.finrank ℂ ((Fin (m + 1) → Fin (D + 1) → ℂ) × (Fin s → ℂ)) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    exact hdim
  obtain ⟨x, hxker, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hrank)
  have hL : ∀ μ j, (∑ i : Fin (D + 1), x.1 μ i * t j ^ (i : ℕ)) = x.2 j * v μ j := by
    intro μ j
    have h := congrFun (congrFun (LinearMap.mem_ker.mp hxker) μ) j
    exact sub_eq_zero.mp h
  -- the polynomials
  set P : Fin (m + 1) → Polynomial ℂ :=
    fun μ => ∑ i : Fin (D + 1), C (x.1 μ i) * X ^ (i : ℕ) with hP
  have hcoeff : ∀ μ (i : Fin (D + 1)), (P μ).coeff i = x.1 μ i := by
    intro μ i
    rw [hP, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i (fun b _ hb => if_neg (fun h => hb (Fin.ext h.symm)))
      (fun h => absurd (Finset.mem_univ i) h), if_pos rfl]
  refine ⟨P, x.2, ?_, fun μ => ?_, fun μ j => ?_⟩
  · by_contra hall
    push Not at hall
    apply hx0
    have h1 : x.1 = 0 := by
      funext μ i
      rw [← hcoeff μ i, hall μ, coeff_zero]
      rfl
    have h2 : x.2 = 0 := by
      funext j
      obtain ⟨μ, hμ⟩ := hv j
      have h := hL μ j
      rw [h1] at h
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_right hμ
    exact Prod.ext h1 h2
  · refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)
  · rw [hP, eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact hL μ j

end

end GaloisForLFunctions.HTGeometry
