import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.ResponseLimit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Reading

/-! # Normalization of the two response matrices at finite splitting -/
open Filter Topology Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {I : Type*} [DecidableEq I]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local notation "P" => (E × ℂ) × ℂ

/-- The odd anchor gives the endpoint alone. The even anchor is the constant row. -/
def weight (k : I) (j m : Bool) (i : I) : ℂ :=
  if i=k then (if m then 1 else jet j splitting 0) else jet j (fun t => alignment t^order m) 0

theorem weight_ne (k : I) (j m : Bool) (i : I) : weight k j m i≠0 := by
  by_cases h : i=k
  · cases m <;> simp [weight,h,jet_splitting_ne]
  · simpa only [weight,if_neg h] using jet_alignment_pow_ne j m

/-- Multiply the pure terminal response, and only that response, by the inverse splitting. -/
def sectorEntry (k : I) (w : I → List E) (j m : Bool) (i : I) (u : ℂ) (F : P→ℂ) : ℂ :=
  if i=k then (if m then 1 else u*response (extendWord j ([] : List (E × ℂ))) F 0)
  else response (extendWord j (extendWord m (w i))) F 0

theorem sectorEntry_limit (k : I) (w : I → List E) (j m b : Bool) (i : I)
    (f : E × ℂ → ℂ) (e : P × ℂ → ℂ) (ha : AnalyticAt ℂ e 0)
    (hπ : ∀ᶠ p : P in 𝓝 0, e (p,0)=f (projectField b p)) :
    Tendsto (fun n => sectorEntry k w j m i (inverseHeight n) (energy b e n)) atTop
      (𝓝 ((sign b^order m*weight k j m i)*(if i=k then 1 else response (extendWord m (w i)) f 0))) := by
  by_cases h : i=k
  · cases m with
    | false =>
      simpa only [sectorEntry,weight,if_pos h,Bool.false_eq_true,if_false,order,pow_one,mul_one]
        using endpoint_reading_limit b j e ha
    | true => cases b <;> simp [sectorEntry,weight,h,sign,order]
  · simpa only [sectorEntry,weight,if_neg h] using bond_reading_limit b j m (w i) f e ha hπ

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
