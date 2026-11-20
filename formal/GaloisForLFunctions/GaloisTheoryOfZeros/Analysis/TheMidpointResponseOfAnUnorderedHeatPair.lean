import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.TheCommonDriftOfAllSheetsAtAHeatCollision
import GaloisForLFunctions.GaloisTheoryOfZeros.Analysis.ExactlyWhichHeatPairsHaveAMidpointReadFromTheirGap

/-!
# The midpoint response of an unordered heat pair

Dividing the midpoint displacement by the squared gap gives a simple
pole on the square-root cover with residue (ρ+η)/(2(ρ−η)²). Its finite
part is the common translation divided by (ρ−η)². For a reflected pair
the pole disappears and the reading measures the next spatial jet.
-/

noncomputable section
open Complex Filter Topology RHTower.DeBruijn
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- Both the numerator and denominator depend only on the unordered pair. -/
def pairMidpointResponse (τ z : ℂ) (m : ℕ) (ρ η s : ℂ) :=
  let x := collisionZero τ z m ρ s
  let y := collisionZero τ z m η s
  ((x+y)/2-z)/(x-y)^2

/-- Pole coefficient of the midpoint response on the square-root cover. -/
def pairResponseResidue (ρ η : ℂ) := ((ρ+η)/2)/(ρ-η)^2

private theorem response_identity (a b d e c s : ℂ) (hb : b≠0) (hs : s≠0) (hD : b+s^2*c≠0) :
    (s*a+s^2*d+s^3*e)/(s*(b+s^2*c))^2 =
      (a/b^2)/s+(d+s*e-(a/b^2)*s*c*(2*b+s^2*c))/(b+s^2*c)^2 := by
  field_simp [hb,hs,hD]
  ring

/-- Full polar part and constant term, with an analytic remainder at zero.
The formula includes both reflected and nonreflected pairs. -/
theorem IsCollision.pair_response_laurent {τ z ρ η : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hρ : heatModelFwd m ρ=0) (hη : heatModelFwd m η=0) (hne : ρ≠η) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ R 0=collisionDrift τ z m/(ρ-η)^2 ∧
      ∀ᶠ s in 𝓝[≠] 0, pairMidpointResponse τ z m ρ η s=pairResponseResidue ρ η/s+R s := by
  obtain ⟨u,hu,h₁⟩ := hc.sheet_after_common_translation hρ
  obtain ⟨v,hv,h₂⟩ := hc.sheet_after_common_translation hη
  let d := collisionDrift τ z m
  let b := ρ-η
  let a := (ρ+η)/2
  let c (s : ℂ) := u s-v s
  let e (s : ℂ) := (u s+v s)/2
  let D (s : ℂ) := b+s^2*c s
  let R (s : ℂ) := (d+s*e s-(a/b^2)*s*c s*(2*b+s^2*c s))/(D s)^2
  have hb : b≠0 := sub_ne_zero.mpr hne
  have hD₀ : D 0=b := by simp [D]
  have hDanalytic : AnalyticAt ℂ D 0 := analyticAt_const.add ((analyticAt_id.pow 2).mul (hu.sub hv))
  have hDne : D 0≠0 := hD₀.trans_ne hb
  have he : AnalyticAt ℂ e 0 := (hu.add hv).div analyticAt_const (by norm_num)
  have hR : AnalyticAt ℂ R 0 :=
    ((analyticAt_const.add (analyticAt_id.mul he)).sub
      (((analyticAt_const.mul analyticAt_id).mul (hu.sub hv)).mul
        (analyticAt_const.add ((analyticAt_id.pow 2).mul (hu.sub hv))))).div
          (hDanalytic.pow 2) (pow_ne_zero 2 hDne)
  refine ⟨R,hR,by simp [R,hD₀,d,b],?_⟩
  filter_upwards [h₁.filter_mono nhdsWithin_le_nhds,h₂.filter_mono nhdsWithin_le_nhds,
    (hDanalytic.continuousAt.eventually_ne hDne).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hu' hv' hD hs
  have hs' : s≠0 := hs
  have hmid : (collisionZero τ z m ρ s+collisionZero τ z m η s)/2-z=s*a+s^2*d+s^3*e s := by
    rw [hu',hv']; dsimp only [a,d,e]; ring
  have hgap : collisionZero τ z m ρ s-collisionZero τ z m η s=s*(b+s^2*c s) := by
    rw [hu',hv']; dsimp only [b,c]; ring
  rw [pairMidpointResponse,hmid,hgap]
  exact response_identity a b d (e s) (c s) s hb hs' hD

/-- At a reflected pair the observed secant reads the common drift
divided by four times the square of the marked profile root. -/
theorem IsCollision.reflected_midpoint_response {τ z ρ : ℂ} {m : ℕ} (hc : IsCollision τ z m)
    (hρ : heatModelFwd m ρ=0) (h : ρ≠0) :
    Tendsto (pairMidpointResponse τ z m ρ (-ρ)) (𝓝[≠] 0) (𝓝 (collisionDrift τ z m/(4*ρ^2))) := by
  have hn : ρ≠ -ρ := fun he => h (by linear_combination (1/2:ℂ)*he)
  have hneg : heatModelFwd m (-ρ)=0 := by rw [heatModelFwd_neg,hρ,mul_zero]
  obtain ⟨R,hR,h₀,hs⟩ := hc.pair_response_laurent hρ hneg hn
  have hlim := hR.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ)≤𝓝 0)
  rw [h₀,show (ρ- -ρ)^2=4*ρ^2 by ring] at hlim
  exact hlim.congr' (hs.mono fun s he => by simpa [pairResponseResidue] using he.symm)

/-- For double zeros the geometric measurement equals H‴/(12 H″),
independently of the collision location and the branch labeling. -/
theorem IsCollision.double_midpoint_reads_third_derivative {τ z : ℂ} (hc : IsCollision τ z 2) :
    Tendsto (pairMidpointResponse τ z 2 (Real.sqrt 2) (-(Real.sqrt 2:ℂ))) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv 3 (complexHeat τ) z/(12*iteratedDeriv 2 (complexHeat τ) z))) := by
  let r : ℂ := (Real.sqrt 2:ℝ)
  have hr : heatModelFwd 2 r=0 := heatModelFwd_profileRoot
    (by rw [profileRoots_two]; exact Finset.mem_insert_self ..)
  have hs : r^2=2 := by dsimp only [r]; exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn : r≠0 := fun he => by rw [he] at hs; norm_num at hs
  have ht := hc.reflected_midpoint_response hr hn
  rw [hs] at ht
  convert ht using 2
  unfold collisionDrift
  push_cast
  field_simp [hc.top_ne_zero] <;> ring

#print axioms IsCollision.pair_response_laurent
#print axioms IsCollision.reflected_midpoint_response
#print axioms IsCollision.double_midpoint_reads_third_derivative
end GaloisForLFunctions.GaloisTheoryOfZeros
