import GaloisForLFunctions.HTGeometry.TopSymbolWimanPlace
import GaloisForLFunctions.HTGeometry.RootProximity

/-!
# The nondegenerate Wiman place

At a Wiman--Valiron point the top symbol of an algebraic differential relation is small, and a small
value of a complex polynomial forces proximity to a root.  Combining the two: along radii beyond
every bound, the logarithmic derivative `f'(z)/f(z)` is arbitrarily close to a root of the top
symbol, weighted by the leading coefficient of the top symbol at `z`.

This is the analytic content of the nondegenerate Wiman place — that `f'` sits over a root of the
top symbol — obtained without constructing a Newton--Puiseux branch.
-/

open Finset Complex Set Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The top symbol of the relation, as a polynomial in the ratio, evaluated at the point `z`. -/
noncomputable def topSymbolPoly (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) (z : ℂ) :
    Polynomial ℂ :=
  ∑ p ∈ S.filter (fun p => p.1 + p.2 = d), Polynomial.C ((A p).eval z) * Polynomial.X ^ p.2

theorem eval_topSymbolPoly (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) (z T : ℂ) :
    (topSymbolPoly S A d z).eval T
      = ∑ p ∈ S.filter (fun p => p.1 + p.2 = d), (A p).eval z * T ^ p.2 := by
  classical
  rw [topSymbolPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem natDegree_topSymbolPoly_le {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d m : ℕ}
    (htopdeg : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m) (z : ℂ) :
    (topSymbolPoly S A d z).natDegree ≤ m := by
  classical
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro p hp
  have hmem := Finset.mem_filter.mp hp
  calc (Polynomial.C ((A p).eval z) * Polynomial.X ^ p.2).natDegree
      ≤ (Polynomial.X ^ p.2 : Polynomial ℂ).natDegree := Polynomial.natDegree_C_mul_le _ _
    _ = p.2 := Polynomial.natDegree_X_pow p.2
    _ ≤ m := htopdeg p hmem.1 hmem.2

theorem coeff_topSymbolPoly {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d m : ℕ}
    (hmd : m ≤ d) (hmem : (d - m, m) ∈ S) (z : ℂ) :
    (topSymbolPoly S A d z).coeff m = (A (d - m, m)).eval z := by
  classical
  rw [topSymbolPoly, Polynomial.finsetSum_coeff]
  have hmemf : (d - m, m) ∈ S.filter (fun p => p.1 + p.2 = d) := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    simp only
    omega
  refine Finset.sum_eq_single_of_mem (d - m, m) hmemf ?_ |>.trans ?_
  · intro p hp hpne
    have hmem' := Finset.mem_filter.mp hp
    have hp2 : p.2 ≠ m := by
      intro hcon
      apply hpne
      have h1 : p.1 = d - m := by
        have := hmem'.2
        omega
      exact Prod.ext h1 hcon
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp [Ne.symm hp2]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp

/-- **The nondegenerate Wiman place.**  For a transcendental entire solution of an algebraic
differential relation of total degree at most `d` whose top symbol has `T`-degree `m ≥ 1` with a
nonzero coefficient polynomial, every `η, ε > 0` and every bound `R` admit a radius `e^y` past `R`, a
point `z` on that circle and a root `r` of the top symbol at `z` with

  `‖f'(z)/f(z) - r‖^m ‖A(z)‖ ≤ η`   and   `‖z f'/f - ν‖ ≤ ε ν`,

where `A` is the top coefficient.  The logarithmic derivative therefore sits over a root of the top
symbol. -/
theorem exists_radius_wiman_place
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d m : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ,
      ∑ p ∈ S, (A p).eval w * (coeffFun a w) ^ p.1 * (deriv (coeffFun a) w) ^ p.2 = 0)
    (hm : 1 ≤ m) (hmd : m ≤ d) (hmem : (d - m, m) ∈ S)
    (htopdeg : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m)
    (hAne : A (d - m, m) ≠ 0)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ R : ℝ, ∃ y, R ≤ y ∧
      y ≤ max R M + Nevanlinna.borelWindow (1 / 4) + 1 ∧ ∃ z : ℂ, ‖z‖ = Real.exp y ∧
      ‖z * deriv (coeffFun a) z / coeffFun a z - (centralIndex a (Real.exp y) : ℂ)‖
        ≤ ε * (centralIndex a (Real.exp y) : ℝ) ∧
      ∃ r : ℂ, (∑ p ∈ S.filter (fun p => p.1 + p.2 = d), (A p).eval z * r ^ p.2) = 0 ∧
        ‖deriv (coeffFun a) z / coeffFun a z - r‖ ^ m * ‖(A (d - m, m)).eval z‖ ≤ η := by
  classical
  set cb : ℝ := ((Polynomial.cauchyBound (A (d - m, m)) : NNReal) : ℝ) with hcbdef
  have hcb0 : (0 : ℝ) ≤ cb := by
    rw [hcbdef]
    exact NNReal.coe_nonneg _
  obtain ⟨M, hM⟩ := exists_radius_norm_topSymbol_le ha hn₀ htrans hdeg hrel hη hε
  refine ⟨max M (Real.log (cb + 1)), fun R => ?_⟩
  obtain ⟨y, hy, hyM, z, hz, htop, hbound⟩ := hM (max R (Real.log (cb + 1)))
  -- the top coefficient does not vanish at the selected point
  have hzcb : cb < ‖z‖ := by
    have hlog : Real.log (cb + 1) ≤ y := le_trans (le_max_right R _) hy
    have hpos : (0 : ℝ) < cb + 1 := by linarith
    have hstep : cb + 1 ≤ Real.exp y := by
      calc cb + 1 = Real.exp (Real.log (cb + 1)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp y := Real.exp_le_exp.mpr hlog
    rw [hz]
    linarith
  have hAz : (A (d - m, m)).eval z ≠ 0 := by
    intro hcon
    have hroot : (A (d - m, m)).IsRoot z := hcon
    have hlt := hroot.norm_lt_cauchyBound hAne
    have hlt' : ‖z‖ < cb := by
      rw [hcbdef]
      exact_mod_cast hlt
    linarith
  -- the top symbol as a polynomial in the ratio
  have hcoeff := coeff_topSymbolPoly (A := A) hmd hmem z
  have hdegle := natDegree_topSymbolPoly_le (A := A) (d := d) htopdeg z
  have hdegge : m ≤ (topSymbolPoly S A d z).natDegree := by
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [hcoeff]
    exact hAz
  have hnat : (topSymbolPoly S A d z).natDegree = m := le_antisymm hdegle hdegge
  have hlead : (topSymbolPoly S A d z).leadingCoeff = (A (d - m, m)).eval z := by
    rw [Polynomial.leadingCoeff, hnat, hcoeff]
  have hQ1 : 1 ≤ (topSymbolPoly S A d z).natDegree := by rw [hnat]; exact hm
  obtain ⟨r, hroot, hdist⟩ :=
    exists_root_pow_dist_le hQ1 (deriv (coeffFun a) z / coeffFun a z)
  rw [hnat, hlead] at hdist
  refine ⟨y, le_trans (le_max_left R _) hy, ?_, z, hz, hbound, r, ?_, ?_⟩
  · have heq : max (max R (Real.log (cb + 1))) M
        = max R (max M (Real.log (cb + 1))) := by
      rw [max_assoc, max_comm (Real.log (cb + 1)) M]
    rw [heq] at hyM
    exact hyM
  · have := hroot
    rw [Polynomial.IsRoot, eval_topSymbolPoly] at this
    exact this
  · have hev : (topSymbolPoly S A d z).eval (deriv (coeffFun a) z / coeffFun a z)
        = ∑ p ∈ S.filter (fun p => p.1 + p.2 = d),
            (A p).eval z * (deriv (coeffFun a) z / coeffFun a z) ^ p.2 :=
      eval_topSymbolPoly S A d z _
    rw [hev] at hdist
    linarith [hdist, htop]

end GaloisForLFunctions.HTGeometry
