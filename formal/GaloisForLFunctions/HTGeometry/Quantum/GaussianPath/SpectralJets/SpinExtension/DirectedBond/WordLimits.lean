import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Words

/-! # Regular limits of ordered energy responses -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every derivative in an old control removes a control-independent energy shift. -/
theorem response_shift (v : E) (w : List E) (f : E→ℂ) (c : ℂ) (x : E) :
    response (v::w) (fun p => c+f p) x = response (v::w) f x := by
  induction w generalizing v x with
  | nil => simp only [response,deriv_const_add]
  | cons d ds ih =>
    exact congrArg (fun h : ℂ→ℂ => deriv h 0) (funext fun t => ih d (x+t • v))

/-- In a joint analytic germ, evaluating an ordered response in the old
variables is continuous in the inverse splitting. -/
theorem slice_limit (w : List E) (f : E × ℂ → ℂ) (x : E) (ha : AnalyticAt ℂ f (x,0)) :
    Tendsto (fun u : ℂ => response w (fun p => f (p,u)) x) (𝓝 0)
      (𝓝 (response w (fun p => f (p,0)) x)) := by
  simp only [←response_slice]
  exact (response_analytic (liftWord w) ha).continuousAt.tendsto.comp
    (continuousAt_const.prodMk continuousAt_id).tendsto

/-- Both endpoint derivatives distribute over analytic energy branches. -/
theorem jet_add (j : Bool) {f g : ℂ→ℂ} {v : ℂ} (hf : AnalyticAt ℂ f v) (hg : AnalyticAt ℂ g v) :
    jet j (fun t => f t+g t) v = jet j f v+jet j g v := by
  have he : deriv (fun t => f t+g t) =ᶠ[𝓝 v] fun t => deriv f t+deriv g t := by
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with t ht hu
    exact (ht.differentiableAt.hasDerivAt.add hu.differentiableAt.hasDerivAt).deriv
  cases j with
  | false => exact he.self_of_nhds
  | true => exact he.deriv_eq.trans (hf.deriv.differentiableAt.hasDerivAt.add
      hg.deriv.differentiableAt.hasDerivAt).deriv

/-- In the signed sectors, taking at least one bond derivative kills the
entire fast energy, including both of its terminal derivatives. -/
theorem fast_energy_cancel (j m : Bool) (w : List E) (f : (E × ℂ) × ℂ → ℂ)
    (g : ℂ→ℂ) :
    response (extendWord j (extendWord m w)) (fun p => g p.2+f p) 0 =
      response (extendWord j (extendWord m w)) f 0 := by
  change response _ _ ((0 : E × ℂ),(0:ℂ))=_
  rw [read_extendWord,read_extendWord]
  apply congrArg (fun h : ℂ→ℂ => jet j h 0)
  funext t
  cases m with
  | false => exact response_shift ((0:E),(1:ℂ)) (liftWord w) (fun y => f (y,t)) (g t) 0
  | true =>
    exact response_shift ((0:E),(1:ℂ)) (((0:E),(1:ℂ)) :: liftWord w) (fun y => f (y,t)) (g t) 0

#print axioms slice_limit
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
