import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.LimitBlock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.NormalizedJets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PairPolynomial

/-! # Persistence of the longitudinal Walsh minor under doublet splitting -/
open MvPolynomial Matrix Topology Filter
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

def limitPoly {n : ℕ} (q : ℂ) (s : Fin n → ℂ) : MvPolynomial (Option (Fin n)) ℂ :=
  C q * ((X none)^2-1-(fieldPoly s)^2)

private theorem limitPoly_simple {n : ℕ} (q : ℂ) (s : Fin n → ℂ) :
    atUpper (pderiv none (limitPoly q s)) = 2*q := by
  have h : pderiv none (fieldPoly s) = 0 := by
    simp [fieldPoly,Derivation.leibniz]
  simp [limitPoly,atUpper,pow_two,Derivation.leibniz,h]
  ring

private theorem upperResponse_limit {n : ℕ} (q : ℂ) (hq : q ≠ 0) (s : Fin n → ℂ) (w : List (Fin n)) :
    upperResponse (limitPoly q s) w = mixed w (fun h => doubletRoot (fieldEnergy s h)) 0 := by
  have hz : fieldEnergy s 0=0 := by simp [fieldEnergy]
  apply upperResponse_eq_mixed
  · apply analyticAt_doubletRoot_zero.fun_comp_of_eq _ hz
    exact Finset.analyticAt_fun_sum _ (fun i _ => analyticAt_const.mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt _))
  · rw [hz,doubletRoot_zero]
  · apply Filter.Eventually.of_forall
    intro x
    simp only [onRoot,limitPoly,map_mul,eval_C,map_sub,map_pow,map_one,eval_X,Option.elim_none,
      eval_fieldPoly,Option.elim_some,doubletRoot_sq,fieldEnergy]
    ring
  · rw [limitPoly_simple]
    exact mul_ne_zero (by norm_num) hq

/-- A continuous coefficient specialization reaching all isolated two-level polynomials
has a nonvanishing longitudinal derivative minor throughout a neighborhood. -/
theorem eventually_upper_minor {T R : Type*} [CommRing R] {F : Filter T} (n : ℕ)
    (p : (Fin n → Bool) → MvPolynomial (Option (Fin (n+1))) R)
    (φ : T → R →+* ℂ) (ψ : R →+* ℂ) (hc : ∀ r, Tendsto (fun v => φ v r) F (𝓝 (ψ r)))
    (q : (Fin n → Bool) → ℂ) (hq : ∀ s, q s≠0)
    (hp : ∀ s, MvPolynomial.map ψ (p s) = limitPoly (q s) (orientedSpin s)) :
    ∀ᶠ v in F, (Matrix.of fun a s : Fin n → Bool =>
      upperResponse (MvPolynomial.map (φ v) (p s)) (maskWord a)).det ≠ 0 := by
  let M (v : T) := Matrix.of fun a s : Fin n → Bool => upperResponse (MvPolynomial.map (φ v) (p s)) (maskWord a)
  let W := Matrix.of fun a s : Fin n → Bool =>
    mixed (maskWord a) (fun h => doubletRoot (fieldEnergy (orientedSpin s) h)) 0
  have hT : Tendsto M F (𝓝 W) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro s
    have hpart : ψ (atUpper (pderiv none (p s))) ≠ 0 := by
      rw [←atUpper_map,←pderiv_map,hp,limitPoly_simple]
      exact mul_ne_zero (by norm_num) (hq s)
    simpa only [M,W,Matrix.of_apply,hp,upperResponse_limit _ (hq s)] using
      tendsto_upperResponse φ ψ hc (p s) (maskWord a) hpart
  have hd : Continuous (fun H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ => H.det) :=
    continuous_id.matrix_det
  exact (hd.continuousAt.tendsto.comp hT).eventually_ne (doublet_jet_det_ne_zero n)

#print axioms eventually_upper_minor
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
