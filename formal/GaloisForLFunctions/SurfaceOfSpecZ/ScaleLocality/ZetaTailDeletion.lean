import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ZetaMixedMomentBounds
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.ConfigurationTailIsolation
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion

/-!
# Cofinite zeta deletion with the ordinate-indexed filters

The fixed enumeration of zeta copies supplies the same filters used by
the mixed moment estimates. A sufficiently late tail preserves any chosen
exponent and deletes all but finitely many spline modes.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold Zeta23 _root_.RHTower
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- An ordinate-indexed tail preserves a chosen exponent and deletes a cofinite spline spectrum. -/
theorem exists_zeta_deletion_tail (α : ℝ) (w₀ : ℂ) :
    ∃ (M : ℕ) (S : Finset ℂ),
      (∏' n, quartetFactor (zetaDeletionDepth α (n + M))
        (zetaDeletionShift (n + M)) w₀) ≠ 0 ∧
      ∀ z ∉ S, evenCoeff zetaZeroConfig (boxSpline 1 3) z ≠ 0 →
        (∏' n, quartetFactor (zetaDeletionDepth α (n + M))
          (zetaDeletionShift (n + M)) (z - (α : ℂ))) = 0 := by
  classical
  obtain ⟨M, _, hkeep⟩ := exists_small_nonzero_tail_multiplier
    (zetaDeletionDepth α) zetaDeletionShift summable_zetaDeletionShift_sq w₀
    (by norm_num : (0 : ℝ) < 1)
  let e := xiZeroCopyThermalEquiv
  let S : Finset ℂ := (Finset.range M).image fun n => ((e n).1 : ℂ) - 1 / 2
  have hsq : Summable fun n => zetaDeletionShift (n + M) ^ 2 :=
    (summable_nat_add_iff M).mpr summable_zetaDeletionShift_sq
  refine ⟨M, S, hkeep, ?_⟩
  intro z hz hcz
  have hρ : (1 / 2 : ℂ) + z ∈ zetaZeroConfig.carrier := by
    rcases mem_of_evenCoeff_ne_zero hcz with hz | hz
    · exact hz
    · have hhalf : conj (1 / 2 : ℂ) = 1 / 2 := by
        rw [show (2 : ℂ) = 1 + 1 by norm_num, map_div₀, map_add, map_one]
      simpa only [map_add, hhalf, Complex.conj_conj] using conj_mem_zetaZeroConfig hz
  have hne1 : (1 / 2 : ℂ) + z ≠ 1 := by
    intro he
    have hr := hρ.2.2
    rw [he, Complex.one_re] at hr
    exact (lt_irrefl _ hr).elim
  have hxi := (xi_eq_zero_iff hρ.2.1 hne1).mpr hρ.1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  let n : ℕ := e.symm q
  have hen : ((e n).1 : ℂ) = (1 / 2 : ℂ) + z := by
    dsimp only [n]
    rw [e.apply_symm_apply, hq]
  have hM : M ≤ n := by
    by_contra hn
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨n, Finset.mem_range.mpr (lt_of_not_ge hn), ?_⟩
    rw [hen]
    ring
  have ha : (z - (α : ℂ)).re = zetaDeletionDepth α (n - M + M) := by
    rw [Nat.sub_add_cancel hM]
    dsimp only [zetaDeletionDepth]
    change _ = ((e n).1 : ℂ).re - 1 / 2 - α
    rw [hen]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    norm_num
  have hp : zetaDeletionShift (n - M + M) * (z - (α : ℂ)).im = Real.pi := by
    rw [Nat.sub_add_cancel hM]
    have him : zeroOrdinate (e n) = z.im := by
      dsimp only [zeroOrdinate]
      rw [hen]
      simp
    have hγ : z.im ≠ 0 := by rw [← him]; exact xiCopyOrdinate_ne_zero _
    change (Real.pi / zeroOrdinate (e n)) * (z - (α : ℂ)).im = Real.pi
    rw [him]
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact div_mul_cancel₀ _ hγ
  have he : (zetaDeletionDepth α (n - M + M) : ℂ) +
      ((z - (α : ℂ)).im : ℂ) * I = z - (α : ℂ) := by
    rw [← ha, Complex.re_add_im]
  have hk := tprod_quartetFactor_root (fun k => zetaDeletionDepth α (k + M))
    (fun k => zetaDeletionShift (k + M)) hsq (n - M) hp
  rwa [he] at hk

#print axioms exists_zeta_deletion_tail

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
