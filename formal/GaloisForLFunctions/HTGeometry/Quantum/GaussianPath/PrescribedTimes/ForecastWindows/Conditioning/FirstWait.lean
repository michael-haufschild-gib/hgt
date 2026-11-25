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
  classical
  intro μ σ Δ
  let z (p : (PrefixIndex n→ℝ)×(PrefixIndex n→ℝ)) := reveal S p.1 p.2
  have hz : Measurable z := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i∈S
    · simpa only [z,reveal,Set.piecewise_eq_of_mem _ _ _ hi] using (measurable_pi_apply i).comp
        (measurable_fst : Measurable (Prod.fst : (PrefixIndex n→ℝ)×(PrefixIndex n→ℝ)→_))
    · simpa only [z,reveal,Set.piecewise_eq_of_notMem _ _ _ hi] using (measurable_pi_apply i).comp
        (measurable_snd : Measurable (Prod.snd : (PrefixIndex n→ℝ)×(PrefixIndex n→ℝ)→_))
  let F (p : (PrefixIndex n→ℝ)×(PrefixIndex n→ℝ)) := a*σ (z p)+b*Δ (z p)
  have hF : Measurable F := (((measurable_crossingOrigin ..).comp hz).const_mul a).add
    (((measurable_crossingWait ..).comp hz).const_mul b)
  apply gaussian_conditional_window F hF _ hT
  intro c hc x y
  have he : z (c • x,c • y)=c • z (x,y) := by
    funext i
    by_cases hi : i∈S <;> simp only [z,reveal,Set.piecewise,hi,ite_true,ite_false,Pi.smul_apply]
  dsimp only [F]
  rw [he,mul_add,mul_left_comm c a,mul_left_comm c b,smul_crossingOrigin n j (9/80) hc,
    smul_crossingWait n j s hc]

#print axioms gaussian_first_wait_conditional_resolution
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows.Conditioning
