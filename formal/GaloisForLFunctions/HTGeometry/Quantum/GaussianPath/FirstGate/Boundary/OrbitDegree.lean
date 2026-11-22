import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.SpectralAlgebra
import GaloisForLFunctions.HTGeometry.EscapingRealSequenceCover
import GaloisForLFunctions.RHTower.ExponentialSumMeanSquareLower

/-! # Exact degree of spectral interpolation along a simple orbit -/
open Polynomial Set Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The polynomial evaluated on separating diagonal entries z to produce the
time evolution with energies E. -/
def orbitInterpolant (z : I→ℂ) (E : I→ℝ) (t : ℝ) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ z (fun i => Complex.exp (Complex.I * ((t * -E i : ℝ):ℂ)))

/-- The highest available coefficient vanishes at only finitely many times
on each compact interval. Its barycentric formula is a nonzero sum of
distinct-frequency exponentials. -/
theorem finite_exceptional_degree [Nonempty I] (z : I→ℂ) (E : I→ℝ)
    (hz : Function.Injective z) (hE : Function.Injective E) (a b : ℝ) :
    {t ∈ Icc a b | (orbitInterpolant z E t).coeff (Fintype.card I-1)=0}.Finite := by
  classical
  let c (j : I) := (∏ k ∈ Finset.univ.erase j, (z j-z k))⁻¹
  let φ (j : I) (t : ℝ) := Complex.exp (Complex.I * ((t * -E j : ℝ):ℂ))
  let F (t : ℝ) := ∑ j, c j*φ j t
  have hn : Set.InjOn z (↑(Finset.univ : Finset I)) := hz.injOn
  have he (t : ℝ) : (orbitInterpolant z E t).coeff (Fintype.card I-1)=F t := by
    have h := Lagrange.coeff_eq_sum hn (Lagrange.degree_interpolate_lt (fun j => φ j t) hn)
    simpa only [orbitInterpolant,Finset.card_univ,Lagrange.eval_interpolate_at_node _ hn (Finset.mem_univ _),
      F,c,div_eq_mul_inv,mul_comm] using h
  have hc (j : I) : c j≠0 := inv_ne_zero (Finset.prod_ne_zero_iff.mpr
    (fun k hk => sub_ne_zero.mpr (hz.ne (Finset.ne_of_mem_erase hk).symm)))
  have hnorm : (0:ℝ)^2 < ∑ j : I, ‖c j‖^2 := by
    rw [zero_pow (by decide)]
    exact Finset.sum_pos (fun j _ => sq_pos_of_pos (norm_pos_iff.mpr (hc j))) Finset.univ_nonempty
  obtain ⟨t,ht'⟩ := (RHTower.frequently_lt_norm_expSum Finset.univ c E hE.injOn hnorm).exists
  have hfun : RHTower.expSum_exponentialSumMeanSquareLower Finset.univ c E t=F t := by
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun a : ℂ => c j*Complex.exp a)
    push_cast
    ring
  have ht : F t≠0 := norm_pos_iff.mp (hfun ▸ ht')
  have ha (x : ℝ) : AnalyticAt ℝ F x := by
    apply Finset.analyticAt_fun_sum
    intro j _
    apply analyticAt_const.mul
    have hA : AnalyticAt ℂ (fun y : ℂ => Complex.exp (Complex.I*(y*((-E j:ℝ):ℂ)))) (x:ℂ) :=
      by fun_prop
    simpa only [φ,Complex.ofReal_mul] using analyticAt_comp_ofReal hA
  have hfinite := finite_zeros_of_analyticOnNhd_complex isPreconnected_univ (fun x _ => ha x)
    (mem_univ t) ht (isCompact_Icc (a := a) (b := b)) (subset_univ _)
  exact hfinite.subset (fun t h => ⟨h.1,(he t).symm.trans h.2⟩)

#print axioms finite_exceptional_degree
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
