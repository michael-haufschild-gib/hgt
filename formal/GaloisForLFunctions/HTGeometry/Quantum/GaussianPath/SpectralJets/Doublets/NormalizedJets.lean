import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SimpleBranches

/-! # Continuity of a simple normalized spectral jet through a doublet limit -/
open MvPolynomial Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- Evaluation at zero applied field and normalized upper root one. -/
def atUpper {ι : Type*} (p : MvPolynomial (Option ι) R) : R :=
  eval (fun o : Option ι => o.elim 1 0) p

theorem atUpper_map {ι : Type*} (φ : R →+* S) (p : MvPolynomial (Option ι) R) :
    atUpper (map φ p) = φ (atUpper p) := by
  rw [atUpper,atUpper,MvPolynomial.map_eval]
  apply congrArg (fun f => eval f (map φ p))
  funext o
  cases o <;> simp [Function.comp_apply]

/-- The rational jet evaluated using only polynomial coefficients.
Its denominator is nonzero at a simple normalized upper root. -/
def upperResponse (p : MvPolynomial (Option (Fin n)) ℂ) (w : List (Fin n)) : ℂ :=
  atUpper (jetRow p w.length (some w)) / (atUpper (pderiv none p))^(2*w.length)

/-- Algebraic specialization makes the same-order response continuous,
even when the original unscaled pair gap tends to zero. -/
theorem tendsto_upperResponse {T : Type*} {F : Filter T} (φ : T → R →+* ℂ) (ψ : R →+* ℂ)
    (hh : ∀ r, Tendsto (fun t => φ t r) F (𝓝 (ψ r))) (p : MvPolynomial (Option (Fin n)) R)
    (w : List (Fin n)) (hs : ψ (atUpper (pderiv none p)) ≠ 0) :
    Tendsto (fun t => upperResponse (map (φ t) p) w) F (𝓝 (upperResponse (map ψ p) w)) := by
  simp only [upperResponse,←jetRow_map,pderiv_map,atUpper_map]
  exact (hh _).div ((hh _).pow _) (pow_ne_zero _ hs)

/-- The coefficient formula equals the mixed derivative of any analytic
root through the normalized upper level. -/
theorem upperResponse_eq_mixed (p : MvPolynomial (Option (Fin n)) ℂ) (w : List (Fin n))
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) (he : f 0=1)
    (hz : onRoot p f =ᶠ[𝓝 0] fun _ => 0) (hs : atUpper (pderiv none p) ≠ 0) :
    upperResponse p w = mixed w f 0 := by
  have hEval (q : MvPolynomial (Option (Fin n)) ℂ) : onRoot q f 0 = atUpper q := by
    simp only [onRoot,atUpper,he]
  have hco : ContinuousAt (onRoot (pderiv none p) f) 0 := by
    apply (contDiff_mvPolynomial_eval _).continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro o
    cases o with
    | none => exact hf.continuousAt
    | some i => exact (continuous_apply i).continuousAt
  obtain ⟨U,hU,ho,h0⟩ := mem_nhds_iff.mp
    ((hf.eventually_analyticAt.and hz).and (hco.eventually_ne (by rwa [hEval])))
  have h := row_eval p w.length (some w) (by intro v hv; cases hv; rfl) f ho
    (fun x hx => (hU hx).1.1.differentiableAt.differentiableWithinAt)
    (fun x hx => (hU hx).1.2) (fun x hx => (hU hx).2) 0 h0
  unfold upperResponse
  apply (div_eq_iff (pow_ne_zero _ hs)).mpr
  simpa only [hEval,rowValue,Option.elim_some] using h

#print axioms tendsto_upperResponse
#print axioms upperResponse_eq_mixed
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
