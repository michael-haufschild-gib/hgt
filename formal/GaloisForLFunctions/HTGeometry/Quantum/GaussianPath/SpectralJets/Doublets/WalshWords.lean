import GaloisForLFunctions.HTGeometry.HypercubeWalshDiagonalisation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BranchEvaluation
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic

/-! # Mixed derivatives in longitudinal Ising fields -/
open Filter Topology Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- Longitudinal field energy of a fixed spin configuration. -/
def fieldEnergy {ι : Type*} [Fintype ι] (s x : ι → ℂ) : ℂ := ∑ i, s i * x i

private theorem coordinate_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s x : ι → ℂ) (i : ι) (t : ℂ) :
    fieldEnergy s (coordLine x i t) = fieldEnergy s x + s i*t := by
  simp only [fieldEnergy,coordLine,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero]
  simp

private theorem analytic_iterate {f : ℂ → ℂ} {z : ℂ} (h : AnalyticAt ℂ f z) (n : ℕ) :
    AnalyticAt ℂ (iteratedDeriv n f) z := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- Each coordinate derivative of a scalar function of the field energy
contributes the corresponding spin and one ordinary derivative. -/
theorem mixed_fieldEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℂ)
    (f : ℂ → ℂ) (w : List ι) (x : ι → ℂ) (hf : AnalyticAt ℂ f (fieldEnergy s x)) :
    mixed w (fun y => f (fieldEnergy s y)) x =
      iteratedDeriv w.length f (fieldEnergy s x) * (w.map s).prod := by
  induction w generalizing x with
  | nil => simp only [mixed,List.length_nil,List.map_nil,List.prod_nil,iteratedDeriv_zero,mul_one]
  | cons i w ih =>
    let z := fieldEnergy s x
    have hline : HasDerivAt (fun t : ℂ => z+s i*t) (s i) 0 := by
      simpa using (((hasDerivAt_id (0:ℂ)).const_mul (s i)).const_add z)
    have he : (fun t => mixed w (fun y => f (fieldEnergy s y)) (coordLine x i t)) =ᶠ[𝓝 0]
        fun t => iteratedDeriv w.length f (z+s i*t) * (w.map s).prod := by
      have ht : Tendsto (fun t : ℂ => z+s i*t) (𝓝 0) (𝓝 z) := by simpa using hline.continuousAt.tendsto
      filter_upwards [ht hf.eventually_analyticAt] with t ht'
      rw [ih _ (by rwa [coordinate_energy]),coordinate_energy]
    have ha := (analytic_iterate hf w.length).differentiableAt.hasDerivAt
    have hb : HasDerivAt (fun t : ℂ => iteratedDeriv w.length f (z+s i*t))
        (deriv (iteratedDeriv w.length f) z * s i) 0 :=
      (show HasDerivAt (iteratedDeriv w.length f) _ (z+s i*0) by simpa using ha).comp 0 hline
    change deriv _ 0 = _
    rw [he.deriv_eq,(hb.mul_const _).deriv,List.length_cons,iteratedDeriv_succ,
      List.map_cons,List.prod_cons,mul_assoc]

/-- A representative modulo global spin reversal with the first spin positive. -/
def orientedSpin {n : ℕ} (s : Fin n → Bool) : Fin (n+1) → ℂ := Fin.cons 1 (fun i => Walsh.boolSign (s i))

/-- Each mask chooses one derivative in each selected field. The remaining
derivatives act on the boundary spin so all masks have the same even order. -/
def maskWord {n : ℕ} (a : Fin n → Bool) : List (Fin (n+1)) :=
  List.ofFn (fun i => if a i then i.succ else 0) ++ List.replicate (n%2) 0

theorem maskWord_length {n : ℕ} (a : Fin n → Bool) : (maskWord a).length = n+n%2 := by
  simp [maskWord]

private theorem spin_product {n : ℕ} (a s : Fin n → Bool) :
    ((maskWord a).map (orientedSpin s)).prod = Walsh.cubeSign a s := by
  simp only [maskWord,List.map_append,List.map_ofFn,List.map_replicate,List.prod_append,
    List.prod_ofFn,List.prod_replicate,orientedSpin,Fin.cons_zero,one_pow,mul_one,Walsh.cubeSign]
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a i <;> simp [ha]

/-- The full matrix of these mixed derivatives at zero field is a single
scalar times the Walsh character table of the spin-reversal classes. -/
theorem mixed_mask_zero {n : ℕ} (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (a s : Fin n → Bool) :
    mixed (maskWord a) (fun h => f (fieldEnergy (orientedSpin s) h)) 0 =
      iteratedDeriv (n+n%2) f 0 * Walsh.cubeSign a s := by
  have hz : fieldEnergy (orientedSpin s) 0 = 0 := by simp [fieldEnergy]
  rw [mixed_fieldEnergy _ _ _ _ (hz ▸ hf),hz,maskWord_length,spin_product]

#print axioms mixed_mask_zero
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
