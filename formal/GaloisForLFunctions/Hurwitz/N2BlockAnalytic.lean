/-
# Hurwitz N=2 — the block sum is analytic on the deep half-plane (discharges `hanalytic`)

With the factored tail `R_k z = tailFactored s k n (e^z)` (analytic on `{‖x‖ < 1/2}` by
`N2TailAnalytic.tailFactored_analytic`), the three monodromy blocks `Φb, Ψb, Θb` of `N2Main` are built
from the entire functions `e^{c·z}` and `p(−n+e^z)` together with that analytic tail, so their sum is
analytic on the half-plane `{Re z < −log 2}` — the `hanalytic` input of `n2_blocks_vanish`.
-/
import GaloisForLFunctions.Hurwitz.N2Main
import GaloisForLFunctions.Hurwitz.N2TailAnalytic

open Complex HurwitzN2Main HurwitzN2Tail

namespace HurwitzN2BlockAnalytic

/-- The deep left half-plane `{Re z < −log 2}` = `exp⁻¹ {‖x‖ < 1/2}`. -/
def region : Set ℂ := {z : ℂ | z.re < -Real.log 2}

theorem isOpen_region : IsOpen region :=
  isOpen_lt Complex.continuous_re continuous_const

/-- `exp` maps the region into the `1/2`-disk where `tailFactored` is analytic. -/
theorem exp_mapsTo : Set.MapsTo Complex.exp region {x : ℂ | ‖x‖ < 1 / 2} := by
  intro z hz
  simp only [region, Set.mem_setOf_eq, Complex.norm_exp] at hz ⊢
  calc Real.exp z.re < Real.exp (-Real.log 2) := Real.exp_lt_exp.mpr hz
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- **The block sum is analytic on the deep half-plane** — the `hanalytic` input of `n2_blocks_vanish`,
discharged from the factored-tail analyticity (`tailFactored_analytic ∘ exp`) plus the entire pieces. -/
theorem blockSum_analytic {s : ℂ} (hs : 1 < s.re) (n : ℕ) (q : Fin 3 → Fin 3 → Polynomial ℂ)
    (l : Fin 3 → Polynomial ℂ) (cc : Polynomial ℂ) :
    AnalyticOnNhd ℂ (fun z => PhiB s n q z
      + PsiB s n q l (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z
      + ThetaB s n q l cc (fun k z => tailFactored s (k : ℕ) n (Complex.exp z)) z) region := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_region
  have htail : ∀ k : Fin 3,
      DifferentiableOn ℂ (fun z => tailFactored s (k : ℕ) n (Complex.exp z)) region :=
    fun k => (tailFactored_analytic hs (k : ℕ) n).differentiableOn.comp
      Complex.differentiable_exp.differentiableOn exp_mapsTo
  have hpoly : ∀ p : Polynomial ℂ,
      DifferentiableOn ℂ (fun z => p.eval (-(n : ℂ) + Complex.exp z)) region := by
    intro p; fun_prop
  have hexp : ∀ c : ℂ, DifferentiableOn ℂ (fun z => Complex.exp (c * z)) region := by
    intro c; fun_prop
  unfold PhiB PsiB ThetaB
  refine ((DifferentiableOn.fun_sum fun w _ => (hpoly _).mul (hexp _)).add
    ((DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (hpoly _).mul (((hexp _).mul (htail j)).add ((hexp _).mul (htail i)))).add
      (DifferentiableOn.fun_sum fun k _ => (hpoly _).mul (hexp _)))).add
    (((DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (hpoly _).mul ((htail i).mul (htail j))).add
      (DifferentiableOn.fun_sum fun k _ => (hpoly _).mul (htail k))).add (hpoly cc))

end HurwitzN2BlockAnalytic
