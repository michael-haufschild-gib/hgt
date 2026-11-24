import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.FiniteEnergy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.WordLimits

/-! # Large-splitting limits of physical energy derivatives -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local notation "P" => (E × ℂ) × ℂ

/-- For every old word, the finite physical response converges to the old
response with the sign dictated by its bond order. -/
theorem bond_reading_limit (b j m : Bool) (w : List E) (f : E × ℂ → ℂ) (e : P × ℂ → ℂ)
    (ha : AnalyticAt ℂ e 0) (hπ : ∀ᶠ p : P in 𝓝 0, e (p,0)=f (projectField b p)) :
    Tendsto (fun n => response (extendWord j (extendWord m w)) (energy b e n) 0) atTop
      (𝓝 ((sign b^order m*jet j (fun t => alignment t^order m) 0)*
        response (extendWord m w) f 0)) := by
  let v := extendWord j (extendWord m w)
  have hs : response v (fun p => e (p,0)) 0 =
      (sign b^order m*jet j (fun t => alignment t^order m) 0)*response (extendWord m w) f 0 := by
    rw [(response_germ v hπ).self_of_nhds]
    change response (extendWord j (extendWord m w)) _ ((0 : E × ℂ),(0:ℂ))=_
    rw [read_extendWord]
    exact read_projected j m w f 0 (sign b)
  have h := (slice_limit v e 0 ha).comp inverseHeight_tendsto
  rw [hs] at h
  apply h.congr
  intro n
  exact (fast_energy_cancel j m w (fun p => e (p,inverseHeight n))
    (fun t => (sign b*splitting t)*height n)).symm

/-- After multiplication by inverse splitting, the new endpoint alone
converges to the signed terminal derivative, independently of the old level. -/
theorem endpoint_reading_limit (b j : Bool) (e : P × ℂ → ℂ) (ha : AnalyticAt ℂ e 0) :
    Tendsto (fun n => inverseHeight n*response (extendWord j ([] : List (E × ℂ))) (energy b e n) 0)
      atTop (𝓝 (sign b*jet j splitting 0)) := by
  let v := extendWord j ([] : List (E × ℂ))
  have hR := (slice_limit v e 0 ha).comp inverseHeight_tendsto
  have hconst : Tendsto (fun _ : ℕ => sign b*jet j splitting 0) atTop (𝓝 (sign b*jet j splitting 0)) :=
    tendsto_const_nhds
  have hlim := hconst.add (inverseHeight_tendsto.mul hR)
  have ht : Tendsto (fun n => ((0:P),inverseHeight n)) atTop (𝓝 0) :=
    tendsto_const_nhds.prodMk_nhds inverseHeight_tendsto
  apply Tendsto.congr' _ (show Tendsto (fun n => sign b*jet j splitting 0 +
      inverseHeight n*response v (fun p => e (p,inverseHeight n)) 0) atTop
      (𝓝 (sign b*jet j splitting 0)) from by simpa only [Function.comp_apply,zero_mul,add_zero] using hlim)
  filter_upwards [ht.eventually ha.eventually_analyticAt] with n hn
  have hslice : AnalyticAt ℂ (fun t : ℂ => e (((0:E × ℂ),t),inverseHeight n)) 0 :=
    hn.comp (f:=fun t : ℂ => (((0:E × ℂ),t),inverseHeight n)) (x:=0)
      ((analyticAt_const.prod analyticAt_id).prod analyticAt_const)
  have hs : AnalyticAt ℂ (fun t => (sign b*height n)*splitting t) 0 :=
    analyticAt_const.mul (profile_analytic _)
  have he (t : ℂ) : energy b e n ((0:E × ℂ),t) =
      (sign b*height n)*splitting t+e (((0:E × ℂ),t),inverseHeight n) := by unfold energy; ring
  have hread : response v (fun p => e (p,inverseHeight n)) 0 =
      jet j (fun t => e (((0:E × ℂ),t),inverseHeight n)) 0 := by
    exact read_extendWord j ([] : List (E × ℂ)) (fun p => e (p,inverseHeight n)) 0 0
  change _=inverseHeight n*response (extendWord j []) (energy b e n) ((0:E × ℂ),0)
  rw [hread]
  simp only [read_extendWord,response,he,jet_add j hs hslice,jet_const_mul]
  rw [mul_add]
  have hB := height_mul_inverse n
  calc _ = (height n*inverseHeight n)*(sign b*jet j splitting 0)+_ := by rw [hB,one_mul]
       _ = _ := by ring

#print axioms bond_reading_limit
#print axioms endpoint_reading_limit
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
