import GaloisForLFunctions.RHTower.SuzukiTorqueTailCarrier
import GaloisForLFunctions.RHTower.SuzukiTorqueContinuationPole
import GaloisForLFunctions.RHTower.RealJetsOfHolomorphic

/-!
# The transform of a thickened one-sign tail

The tail carrier's transform is the profile's own continuation, rescaled by the cut and with its head
removed, plus the reference pole at `1/4`.  Its convergence abscissa is pinned into `[1/4, 3/2]` by
the two mass bounds, and it is analytic wherever the continuation is — which is what Landau's
theorem will contradict.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa tailCarrier
  tailMeasure headLaplace exists_isAbscissa complexLaplace_ofReal differentiable_headLaplace
  laplaceMass_tailMeasure_eq_top laplaceMass_tailMeasure_ne_top)

noncomputable section

namespace RHTower

/-- The Laplace transform of a thickened one-sign tail, written through the profile's
continuation. -/
def tailTransform (g : ℝ → ℝ) (Gc : ℂ → ℂ) (H : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (H : ℂ)) * (Gc s - headLaplace g H s) + 1 / (s - 1 / 4)

theorem analyticAt_headLaplace {g : ℝ → ℝ} (hgc : Continuous g) {H : ℝ} (hH : 0 ≤ H) (z : ℂ) :
    AnalyticAt ℂ (headLaplace g H) z :=
  (differentiable_headLaplace hgc hH).differentiableOn.analyticAt
    (Filter.univ_mem' fun _ => trivial)

/-- **The tail transform is analytic wherever the continuation is, away from the reference
pole.** -/
theorem analyticAt_tailTransform {g : ℝ → ℝ} (hgc : Continuous g) {Gc : ℂ → ℂ} {H : ℝ}
    (hH : 0 ≤ H) {z : ℂ} (hz4 : z ≠ 1 / 4) (hG : AnalyticAt ℂ Gc z) :
    AnalyticAt ℂ (tailTransform g Gc H) z := by
  have hhead := analyticAt_headLaplace hgc hH z
  have hexp : AnalyticAt ℂ (fun s : ℂ => Complex.exp (s * (H : ℂ))) z :=
    (analyticAt_id.mul analyticAt_const).cexp
  have hpole : AnalyticAt ℂ (fun s : ℂ => 1 / (s - 1 / 4)) z :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz4)
  have hfun : tailTransform g Gc H = fun s : ℂ =>
      Complex.exp (s * (H : ℂ)) * (Gc s - headLaplace g H s) + 1 / (s - 1 / 4) := rfl
  rw [hfun]
  exact (hexp.mul (hG.sub hhead)).add hpole

/-- At every real point where the profile transform converges, the tail transform is the tail's
real Laplace transform. -/
theorem tailTransform_ofReal {g : ℝ → ℝ} (hgc : Continuous g) {Gc : ℂ → ℂ} {H σ : ℝ}
    (hH : 0 ≤ H) (hσ : 1 / 4 < σ)
    (hgi : IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0))
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u))
    (htrans : ((∫ L in Ioi (0 : ℝ), g L * Real.exp (-σ * L) : ℝ) : ℂ) = Gc ((σ : ℂ))) :
    tailTransform g Gc H ((σ : ℂ)) = ((laplaceReal (tailMeasure g H) σ : ℝ) : ℂ) := by
  have hhead : headLaplace g H ((σ : ℂ))
      = ((∫ L in Ioc (0 : ℝ) H, g L * Real.exp (-σ * L) : ℝ) : ℂ) := by
    have h : (∫ L in Ioc (0 : ℝ) H, ((g L * Real.exp (-σ * L) : ℝ) : ℂ))
        = ((∫ L in Ioc (0 : ℝ) H, g L * Real.exp (-σ * L) : ℝ) : ℂ) := integral_ofReal
    rw [headLaplace, ← h]
    refine setIntegral_congr_fun measurableSet_Ioc fun L _ => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  rw [laplaceReal_tailMeasure_eq hgc hH hσ hgi hpos, tailTransform, hhead, ← htrans]
  push_cast
  ring

theorem laplaceMass_tail_ne_top {g : ℝ → ℝ} (hgc : Continuous g) {H σ : ℝ} (hH : 0 ≤ H)
    (hσ : 1 / 4 < σ) (hgi : IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0))
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u)) :
    laplaceMass (tailMeasure g H) σ ≠ ⊤ :=
  laplaceMass_tailMeasure_ne_top hgc.measurable hpos (integrableOn_tailCarrier_mul_exp hH hσ hgi)

/-- **The thickened tail has a convergence abscissa in `[1/4, 3/2]`.** -/
theorem exists_isAbscissa_tail {g : ℝ → ℝ} (hgc : Continuous g) {H : ℝ} (hH : 0 ≤ H)
    (hgi : ∀ σ : ℝ, 3 / 2 < σ → IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0))
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u)) :
    ∃ c : ℝ, IsAbscissa (tailMeasure g H) c ∧ 1 / 4 ≤ c ∧ c ≤ 3 / 2 := by
  obtain ⟨c, hc⟩ := exists_isAbscissa
    ⟨2, laplaceMass_tail_ne_top hgc hH (by norm_num) (hgi 2 (by norm_num)) hpos⟩
    ⟨0, laplaceMass_tailMeasure_eq_top hgc.measurable hpos (by norm_num)⟩
  refine ⟨c, hc, ?_, ?_⟩
  · by_contra hcon
    have hlt : c < 1 / 4 := lt_of_not_ge hcon
    obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : ℝ, c < σ ∧ σ < 1 / 4 := ⟨(c + 1 / 4) / 2, by linarith, by linarith⟩
    exact hc.1 σ hσ1 (laplaceMass_tailMeasure_eq_top hgc.measurable hpos hσ2)
  · by_contra hcon
    have hlt : 3 / 2 < c := lt_of_not_ge hcon
    obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : ℝ, 3 / 2 < σ ∧ σ < c := ⟨(3 / 2 + c) / 2, by linarith, by linarith⟩
    exact laplaceMass_tail_ne_top hgc hH (by linarith) (hgi σ hσ1) hpos (hc.2 σ hσ2)

end RHTower
