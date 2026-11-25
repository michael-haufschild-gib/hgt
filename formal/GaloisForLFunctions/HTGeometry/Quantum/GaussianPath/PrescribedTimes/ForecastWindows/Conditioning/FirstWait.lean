import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Conditioning.Dilation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Conditional forecast resolution for the original first excursion -/

open Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
noncomputable section

/-- Keep the revealed coefficients of x and supply every other coefficient
from y. Independent standard Gaussians on y give the conditional prefix law. -/
def reveal {I : Type*} (S : Set I) (x y : I→ℝ) (i : I) : ℝ := by
  classical
  exact S.piecewise x y i

/-- The observable after completing the revealed block with the hidden Gaussian coordinates. -/
def revealedPassage (n j s : ℕ) (S : Set (PrefixIndex n)) (a b : ℝ)
    (p : (PrefixIndex n→ℝ)×(PrefixIndex n→ℝ)) : ℝ :=
  let z := reveal S p.1 p.2
  a*crossingOrigin n j (9/80) z+b*crossingWait n j s z

theorem revealedPassage_properties (n j s : ℕ) (S : Set (PrefixIndex n)) (a b : ℝ) :
    let F := revealedPassage n j s S a b
    Measurable F ∧ ∀ c > (0:ℝ), ∀ x y, c*F (c • x,c • y)=F (x,y) := by
  classical
  intro F
  let z (p : (PrefixIndex n→ℝ)×(PrefixIndex n→ℝ)) := reveal S p.1 p.2
  have hz : Measurable z := by
    apply measurable_pi_lambda
    intro i
    have hi' : Measurable (fun x : PrefixIndex n→ℝ => x i) := measurable_pi_apply i
    by_cases hi : i∈S
    · simp only [z,reveal,Set.piecewise_eq_of_mem _ _ _ hi]
      exact hi'.comp measurable_fst
    · simp only [z,reveal,Set.piecewise_eq_of_notMem _ _ _ hi]
      exact hi'.comp measurable_snd
  refine ⟨(((measurable_crossingOrigin n j (9/80)).comp hz).const_mul a).add
    (((measurable_crossingWait n j s).comp hz).const_mul b),?_⟩
  intro c hc x y
  have he : z (c • x,c • y)=c • z (x,y) := by
    funext i
    by_cases hi : i∈S <;> simp only [z,reveal,Set.piecewise,hi,ite_true,ite_false,Pi.smul_apply]
  change c*(a*crossingOrigin n j (9/80) (z (c • x,c • y))+b*crossingWait n j s (z (c • x,c • y))) =
    a*crossingOrigin n j (9/80) (z (x,y))+b*crossingWait n j s (z (x,y))
  rw [he,mul_add,mul_left_comm c a,mul_left_comm c b,smul_crossingOrigin n j (9/80) hc,
    smul_crossingWait n j s hc]

/-- At each prescribed positive forecast time the first wait has locally
linear conditional window mass for almost every revealed background, for
arbitrary crossing and return budgets. Taking (a,b)=(1,0) or (1,1) gives
the crossing or the absolute first return, respectively. -/
theorem gaussian_first_wait_conditional_resolution (n j s : ℕ) (S : Set (PrefixIndex n))
    (a b : ℝ) {T : ℝ} (hT : 0<T) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j s
    ∀ᵐ x ∂μ, ∃ C ≥ (0:ℝ), ∀ h> (0:ℝ), μ.real {y | let z := reveal S x y
      |a*σ z+b*Δ z-T|<h}≤C*h := by
  obtain ⟨hm,hs⟩ := revealedPassage_properties n j s S a b
  exact gaussian_conditional_window _ hm hs hT

#print axioms gaussian_first_wait_conditional_resolution
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
