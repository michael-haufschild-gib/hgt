import GaloisForLFunctions.HTGeometry.SimplePoleResidueValue
import GaloisForLFunctions.RHTower.AnalyticDividedDifference

/-!
# A simple scale zero with an analytic background

Clearing the zero by a divided difference identifies the residue and
detects exactly when the meromorphic germ is singular.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift

open Filter
open scoped Topology

private theorem finite_drop (e : ℕ∞) :
    ((e.map (Nat.cast : ℕ → ℤ) - (1 : ℕ∞).map Nat.cast < 0) ↔ e = 0) ∧
    ((e.map (Nat.cast : ℕ → ℤ) - (1 : ℕ∞).map Nat.cast = ((-1:ℤ):WithTop ℤ)) ↔ e = 0) := by
  cases e with
  | top =>
    exact ⟨iff_of_false (not_lt_of_ge le_top) ENat.top_ne_zero,
      iff_of_false WithTop.top_ne_coe ENat.top_ne_zero⟩
  | coe n =>
    change ((↑((n:ℤ)-1) : WithTop ℤ) < ↑(0:ℤ) ↔ (n:ℕ∞) = (↑(0:ℕ):ℕ∞)) ∧
      ((↑((n:ℤ)-1) : WithTop ℤ) = ↑(-1:ℤ) ↔ (n:ℕ∞) = (↑(0:ℕ):ℕ∞))
    simp only [WithTop.coe_lt_coe,WithTop.coe_inj,ENat.coe_inj]
    omega

theorem simple_scale {H N D : ℂ → ℂ} {w : ℂ} (hH : AnalyticAt ℂ H w) (hN : AnalyticAt ℂ N w)
    (hD : AnalyticAt ℂ D w) (h₀ : D w = 0) (hd : deriv D w ≠ 0) :
    let f := fun z => H z+N z/D z
    HTGeometry.laurentCoeff f w (-1) = N w/deriv D w ∧
    (meromorphicOrderAt f w < 0 ↔ N w ≠ 0) ∧
    (meromorphicOrderAt f w = (-1:ℤ) ↔ N w ≠ 0) := by
  let f := fun z => H z+N z/D z
  let U := fun z => (z-w)*H z+N z/dslope D w z
  have hU : AnalyticAt ℂ U w := ((analyticAt_id.sub analyticAt_const).mul hH).add
    (hN.div (_root_.RHTower.analyticAt_dslope_of_analyticAt hD hD) (by rwa [dslope_same]))
  have hv : U w = N w/deriv D w := by simp only [U,sub_self,zero_mul,zero_add,dslope_same]
  have hf : MeromorphicAt f w := hH.meromorphicAt.add (hN.meromorphicAt.div hD.meromorphicAt)
  have he : f =ᶠ[𝓝[≠] w] fun z => U z/(z-w) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : z-w ≠ 0 := sub_ne_zero.mpr (show z ≠ w from hz)
    have hs := sub_smul_dslope D w z
    rw [h₀,sub_zero,smul_eq_mul] at hs
    change H z+N z/D z = ((z-w)*H z+N z/dslope D w z)/(z-w)
    rw [add_div,mul_div_cancel_left₀ _ hn,div_div,mul_comm (dslope D w z),hs]
  refine ⟨(HTGeometry.laurentCoeff_congr hf he (-1)).trans
    ((HTGeometry.laurentCoeff_analytic_div_sub hU).trans hv),?_⟩
  have hlin : AnalyticAt ℂ (fun z => z-w) w := analyticAt_id.sub analyticAt_const
  have hlin' : HasDerivAt (fun z : ℂ => z-w) 1 w := (hasDerivAt_id w).sub_const w
  have ho := hlin.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (sub_self w)
    (by rw [hlin'.deriv]; exact one_ne_zero)
  have horder : meromorphicOrderAt f w =
      (analyticOrderAt U w).map (Nat.cast : ℕ → ℤ) - (1 : ℕ∞).map Nat.cast := by
    rw [meromorphicOrderAt_congr he]
    change meromorphicOrderAt (U/(fun z => z-w)) w = _
    rw [meromorphicOrderAt_div hU.meromorphicAt hlin.meromorphicAt,hU.meromorphicOrderAt_eq,
      hlin.meromorphicOrderAt_eq,ho]
  change (meromorphicOrderAt f w < 0 ↔ N w ≠ 0) ∧ (meromorphicOrderAt f w = (-1:ℤ) ↔ N w ≠ 0)
  rw [horder]
  have hn : (analyticOrderAt U w = 0) ↔ N w ≠ 0 := by
    rw [hU.analyticOrderAt_eq_zero,hv,div_ne_zero_iff]
    exact and_iff_left hd
  exact ⟨(finite_drop _).1.trans hn,(finite_drop _).2.trans hn⟩

#print axioms simple_scale

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.BalancedShift
