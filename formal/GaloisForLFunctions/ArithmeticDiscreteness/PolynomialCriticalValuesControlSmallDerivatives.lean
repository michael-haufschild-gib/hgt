import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!+# Polynomial critical values control small derivatives

On a disc of radius `r`, values of a degree-`k` polynomial at points where its derivative has
modulus at most `ε` lie in at most `k+1` discs of radius `2^k r ε`. Their centres are the
critical values and the value at the centre of the original disc. Factoring the derivative
controls its growth along a segment to a nearest critical point or to the disc centre.
-/

open Polynomial Complex Metric Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

private theorem norm_rootProduct_le (s : Multiset ℂ) (z w : ℂ)
    (h : ∀ a ∈ s, ‖w - a‖ ≤ 2 * ‖z - a‖) :
    ‖(s.map (fun a => w - a)).prod‖ ≤
      2 ^ s.card * ‖(s.map (fun a => z - a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha := h a (Multiset.mem_cons_self _ _)
      have hs := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul]
      calc
        ‖w - a‖ * ‖(s.map (fun b => w - b)).prod‖
            ≤ (2 * ‖z - a‖) * (2 ^ s.card * ‖(s.map (fun b => z - b)).prod‖) :=
          mul_le_mul ha hs (norm_nonneg _) (by positivity)
        _ = 2 ^ (s.card + 1) * (‖z - a‖ * ‖(s.map (fun b => z - b)).prod‖) := by
          rw [pow_succ]
          ring

/-- Moving less than the distance to every root changes the polynomial's modulus by at most
`2^degree`. This estimate also covers constant and zero polynomials. -/
theorem norm_polynomial_eval_le_two_pow (P : ℂ[X]) (z w : ℂ)
    (h : ∀ a ∈ P.roots, ‖w - z‖ ≤ ‖z - a‖) :
    ‖P.eval w‖ ≤ 2 ^ P.natDegree * ‖P.eval z‖ := by
  have heval (u : ℂ) :
      P.eval u = P.leadingCoeff * (P.roots.map (fun a => u - a)).prod := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := P))]
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_apply,
      eval_sub, eval_X]
  have hprod := norm_rootProduct_le P.roots z w (fun a ha => by
    calc ‖w - a‖ = ‖(w - z) + (z - a)‖ := by congr 1; ring
      _ ≤ ‖w - z‖ + ‖z - a‖ := norm_add_le _ _
      _ ≤ 2 * ‖z - a‖ := by linarith only [h a ha])
  rw [IsAlgClosed.card_roots_eq_natDegree] at hprod
  rw [heval w, heval z, norm_mul, norm_mul]
  calc
    ‖P.leadingCoeff‖ * ‖(P.roots.map (fun a => w - a)).prod‖
        ≤ ‖P.leadingCoeff‖ * (2 ^ P.natDegree * ‖(P.roots.map (fun a => z - a)).prod‖) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by ring

/-- A segment shorter than every distance to a critical point has controlled image length. -/
theorem polynomial_image_sub_le_of_critical_points_far (P : ℂ[X]) (z w : ℂ)
    (h : ∀ a ∈ P.derivative.roots, ‖w - z‖ ≤ ‖z - a‖) :
    ‖P.eval w - P.eval z‖ ≤
      (2 ^ P.derivative.natDegree * ‖P.derivative.eval z‖) * ‖w - z‖ := by
  have hdist : ∀ u ∈ segment ℝ z w, ‖u - z‖ ≤ ‖w - z‖ := by
    intro u hu
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hu
    have he : a • z + b • w - z = b • (w - z) := by
      rw [show a = 1 - b by linarith only [hab]]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [ha, hab])
  apply (convex_segment z w).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (P.hasDerivAt u).differentiableAt) ?_
    (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  intro u hu
  rw [(P.hasDerivAt u).deriv]
  exact norm_polynomial_eval_le_two_pow P.derivative z u
    (fun a ha => (hdist u hu).trans (h a ha))

/-- The value at the disc centre together with the polynomial's critical values. -/
def polynomialCriticalCentres (P : ℂ[X]) (c : ℂ) : Finset ℂ := by
  classical
  exact insert (P.eval c) (P.derivative.roots.toFinset.image P.eval)

theorem polynomialCriticalCentres_card_le (P : ℂ[X]) (c : ℂ) :
    (polynomialCriticalCentres P c).card ≤ P.natDegree + 1 := by
  classical
  calc
    (polynomialCriticalCentres P c).card
        ≤ (P.derivative.roots.toFinset.image P.eval).card + 1 := Finset.card_insert_le _ _
    _ ≤ P.derivative.roots.toFinset.card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ P.derivative.roots.card + 1 :=
      Nat.add_le_add_right (Multiset.toFinset_card_le _) 1
    _ ≤ P.natDegree + 1 := by
      rw [IsAlgClosed.card_roots_eq_natDegree]
      exact Nat.add_le_add_right ((natDegree_derivative_le P).trans (Nat.sub_le _ _)) 1

/-- Small-derivative values admit a cover whose number of discs depends only on degree,
without a lower bound on the polynomial's coefficients. -/
theorem exists_polynomialCriticalCentre_near (P : ℂ[X]) (c z : ℂ) {r ε : ℝ}
    (hz : ‖z - c‖ ≤ r) (hε : ‖P.derivative.eval z‖ ≤ ε) :
    ∃ v ∈ polynomialCriticalCentres P c,
      ‖P.eval z - v‖ ≤ 2 ^ P.natDegree * r * ε := by
  classical
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hdegree : (2 : ℝ) ^ P.derivative.natDegree ≤ 2 ^ P.natDegree :=
    pow_le_pow_right₀ (by norm_num) ((natDegree_derivative_le P).trans (Nat.sub_le _ _))
  have hbound (w : ℂ) (hw : ‖w - z‖ ≤ r)
      (hfar : ∀ a ∈ P.derivative.roots, ‖w - z‖ ≤ ‖z - a‖) :
      ‖P.eval z - P.eval w‖ ≤ 2 ^ P.natDegree * r * ε := by
    rw [norm_sub_rev]
    refine (polynomial_image_sub_le_of_critical_points_far P z w hfar).trans ?_
    calc
      (2 ^ P.derivative.natDegree * ‖P.derivative.eval z‖) * ‖w - z‖
          ≤ (2 ^ P.natDegree * ε) * r :=
        mul_le_mul (mul_le_mul hdegree hε (norm_nonneg _) (by positivity)) hw
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  by_cases hnear : ∃ a ∈ P.derivative.roots.toFinset, ‖z - a‖ ≤ r
  · obtain ⟨a, ha, har⟩ := hnear
    obtain ⟨b, hb, hbmin⟩ := P.derivative.roots.toFinset.exists_min_image
      (fun w => ‖z - w‖) ⟨a, ha⟩
    refine ⟨P.eval b, ?_, hbound b ?_ ?_⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    · rw [norm_sub_rev]
      exact (hbmin a ha).trans har
    · intro a ha
      rw [norm_sub_rev]
      exact hbmin a (Multiset.mem_toFinset.mpr ha)
  · refine ⟨P.eval c, Finset.mem_insert_self _ _, hbound c ?_ ?_⟩
    · rwa [norm_sub_rev]
    · intro a ha
      have h : r < ‖z - a‖ := by
        by_contra h
        exact hnear ⟨a, Multiset.mem_toFinset.mpr ha, le_of_not_gt h⟩
      rw [norm_sub_rev]
      exact hz.trans h.le

end GaloisForLFunctions.ArithmeticDiscreteness
