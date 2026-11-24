import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.ResponseTransport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectionalWords
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Ordered local responses when an endpoint becomes a bond -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Earlier coordinates retain their direction after appending a scalar control. -/
def liftWord (w : List E) := w.map (fun v => (v,(0:ℂ)))

theorem response_slice (w : List E) (f : E × ℂ →ℂ) (x : E) (v : ℂ) :
    response (liftWord w) f (x,v) = response w (fun y => f (y,v)) x := by
  symm
  apply response_affine (fun y => (y,v)) (fun d => (d,0))
  intro y d t
  ext <;> simp

private def ones : Bool → List ℂ | false => [1] | true => [1,1]

private theorem response_one (f : ℂ→ℂ) (z : ℂ) : response [1] f z=deriv f z := by
  simp only [response,smul_eq_mul,mul_one,deriv_comp_const_add,add_zero]

private theorem response_ones (m : Bool) (f : ℂ→ℂ) (z : ℂ) : response (ones m) f z=jet m f z := by
  cases m with
  | false => exact response_one f z
  | true =>
    change response ([1]++[1]) f z = _
    rw [response_append,show response [1] f=deriv f from funext (response_one f),response_one]
    rfl

/-- One or two terminal derivatives, outside every derivative in the old word. -/
def extendWord (m : Bool) (w : List E) : List (E × ℂ) :=
  (ones m).map (fun h => ((0:E),h)) ++ liftWord w

omit [NormedSpace ℂ E] in
theorem length_extendWord (m : Bool) (w : List E) : (extendWord m w).length=order m+w.length := by
  cases m <;> simp [extendWord,ones,liftWord,order] <;> omega

theorem read_extendWord (m : Bool) (w : List E) (f : E × ℂ →ℂ) (x : E) (v : ℂ) :
    response (extendWord m w) f (x,v) = jet m (fun t => response w (fun y => f (y,t)) x) v := by
  have h (y d t : ℂ) : (x,y+t • d)=(x,y)+t • ((0:E),d) := by ext <;> simp
  rw [extendWord,response_append,←response_affine (fun y => (x,y)) (fun d => ((0:E),d)) h]
  simp only [Function.comp_def,response_slice,response_ones]

/-- Any old word, including its terminal multiplicity, acquires exactly the
signed tilt factor under projection onto the fast spin. -/
theorem read_projected (j m : Bool) (w : List E) (f : E × ℂ →ℂ) (x : E) (s : ℂ) :
    jet j (fun t => response (extendWord m w)
      (fun q => f (q.1,(s*alignment t)*q.2)) (x,0)) 0 =
      (s^order m*jet j (fun t => alignment t^order m) 0)*response (extendWord m w) f (x,0) := by
  simp only [read_extendWord]
  exact projected_response j m s (fun J => response w (fun y => f (y,J)) x)

/-- Converting the normalized tilt back to a physical terminal field
rescales every row in a fixed terminal order by the same power. -/
theorem read_scaled (j : Bool) (w : List E) (f : E × ℂ → ℂ) (u : ℂ) :
    response (extendWord j w) (fun p => f (p.1,u*p.2)) 0 =
      u^order j*response (extendWord j w) f 0 := by
  change response _ _ ((0:E),(0:ℂ))=u^order j*response _ _ ((0:E),(0:ℂ))
  simp only [read_extendWord]
  exact jet_rescale j (fun t => response w (fun y => f (y,t)) 0) u

#print axioms read_projected
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
