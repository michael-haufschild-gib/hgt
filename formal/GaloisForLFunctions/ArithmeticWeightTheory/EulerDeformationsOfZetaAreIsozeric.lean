import GaloisForLFunctions.ArithmeticWeightTheory.TheTrivialFibreIsTheJump
import GaloisForLFunctions.PrimeTorusTheory.TheNaturalBoundaryOfTheHull
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus

/-!
# Euler deformations of `ζ` are isozeric

A family carries monodromy on zeros only if its fibres move them. Inside the gauge family the
fibres that stay analytically comparable to `ζ` do not: deforming the local roots of the Euler
product of `ζ` by an absolutely summable prime perturbation changes the fibre by a nowhere-vanishing
analytic factor.

**Theorem** (`exists_isozeric`). If `Σ_p |χ_x(p) − 1| p^{−σ₀} < ∞` with `σ₀ ≥ ½`, then
`F = Σ_p (χ_x(p) − 1) p^{−s} + h_x − h_0` (`deformationExponent`, `h` the analytic remainder of
the logarithm of a fibre) is analytic on `Re s > σ₀`, and on `Re s > 1`

  `ζ_x(s) = ζ(s) e^{F(s)}`  (`gaugeFibre_eq_zeta_mul_exp`, valid for every fibre).

So `ζ_x` continues to `Re s > σ₀` as `ζ e^F`: same pole, same zeros, same multiplicities
(`analyticOrderAt_isozeric`). Euler deformations deform no zero.

**Theorem** (`gaugeHaar_isozericClass_eq_zero`). For `½ ≤ σ₀ < 1` the isozeric class of `ζ` is
Haar-null: a fibre in it carries the pole of `ζ` at `s = 1`, which the almost-sure zero-free
extension of a generic fibre to `Re s > ½` excludes (residue of `ζ` at `1`). The generic fibre is
analytically disconnected from `ζ`; the fibres that are analytically connected keep its zeros.
-/

open MeasureTheory Filter Topology
open scoped LSeries.notation

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry PrimeTorusTheory

/-- The prime part `Σ_p (χ_x(p) − 1) p^{−s}` of the Euler deformation from `ζ` to the fibre `x`. -/
def deformationPrimeSum (x : GaugeTorus) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (twist x p - 1) * ((p : ℕ) : ℂ) ^ (-s)

/-- The exponent `F` of the Euler deformation: `ζ_x = ζ e^F` on `Re s > 1`. -/
def deformationExponent (x : GaugeTorus) (s : ℂ) : ℂ :=
  deformationPrimeSum x s + hullRem s (twist x) - hullRem s (twist 0)

/-- The fibre at the trivial point is `ζ`. -/
theorem gaugeFibre_trivial {s : ℂ} (hs : 1 < s.re) : gaugeFibre 0 s = riemannZeta s := by
  have h : twist (0 : GaugeTorus) = 1 := funext twist_trivial
  rw [gaugeFibre, h, LSeries_one_eq_riemannZeta hs]

/-- **Every fibre is `ζ` times an exponential** on `Re s > 1`. -/
theorem gaugeFibre_eq_zeta_mul_exp (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    gaugeFibre x s = riemannZeta s * Complex.exp (deformationExponent x s) := by
  have hx := exp_tsum_eq_gaugeFibre x hs
  have h0 := exp_tsum_eq_gaugeFibre (0 : GaugeTorus) hs
  rw [gaugeFibre_trivial hs] at h0
  rw [← hx, ← h0, ← Complex.exp_add]
  congr 1
  have hD : deformationPrimeSum x s = (∑' p : Nat.Primes, eulerVar s (twist x) p) -
      ∑' p : Nat.Primes, eulerVar s (twist 0) p := by
    rw [← (summable_eulerVar (norm_twist_prime x) hs).tsum_sub
      (summable_eulerVar (norm_twist_prime 0) hs)]
    unfold deformationPrimeSum
    refine tsum_congr fun p => ?_
    simp only [eulerVar, powCoeff, twist_trivial]
    ring
  unfold deformationExponent
  rw [hD]
  ring

/-- The prime part is analytic where the perturbation is absolutely summable. -/
theorem differentiableOn_deformationPrimeSum {x : GaugeTorus} {σ₀ : ℝ}
    (hsum : Summable fun p : Nat.Primes => ‖twist x p - 1‖ * ((p : ℕ) : ℝ) ^ (-σ₀)) :
    DifferentiableOn ℂ (deformationPrimeSum x) {s | σ₀ < s.re} := by
  refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun p => ?_)
    (isOpen_lt continuous_const Complex.continuous_re) (fun p w hw => ?_)
  · intro s _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).mul ((differentiableAt_id.neg).const_cpow
      (Or.inl (by exact_mod_cast p.2.ne_zero)))
  · have hw' : σ₀ < w.re := hw
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.2.one_lt.le) ?_
    simp only [Complex.neg_re]
    linarith

/-- **Euler deformations are isozeric.** A summable prime perturbation on `Re s > σ₀ ≥ ½`
gives `ζ_x = ζ e^F` with `F` analytic on `Re s > σ₀`. -/
theorem exists_isozeric {x : GaugeTorus} {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hsum : Summable fun p : Nat.Primes => ‖twist x p - 1‖ * ((p : ℕ) : ℝ) ^ (-σ₀)) :
    AnalyticOnNhd ℂ (deformationExponent x) {s | σ₀ < s.re} ∧
      ∀ s : ℂ, 1 < s.re → gaugeFibre x s = riemannZeta s * Complex.exp (deformationExponent x s) := by
  refine ⟨?_, fun s hs => gaugeFibre_eq_zeta_mul_exp x hs⟩
  have hsub : {s : ℂ | σ₀ < s.re} ⊆ rightHalf := fun s hs => by
    show 1 / 2 < s.re
    have : σ₀ < s.re := hs
    linarith
  have hD := (differentiableOn_deformationPrimeSum hsum).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)
  exact (hD.add ((analyticOnNhd_hullRem (norm_twist_prime x)).mono hsub)).sub
    ((analyticOnNhd_hullRem (norm_twist_prime 0)).mono hsub)

/-- **Same zeros, same multiplicities.** Off the pole, the continuation `ζ e^F` vanishes to
exactly the order of `ζ`. -/
theorem analyticOrderAt_isozeric {x : GaugeTorus} {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hsum : Summable fun p : Nat.Primes => ‖twist x p - 1‖ * ((p : ℕ) : ℝ) ^ (-σ₀)) {s₀ : ℂ}
    (hs₀ : σ₀ < s₀.re) (hs₁ : s₀ ≠ 1) :
    analyticOrderAt (fun s => riemannZeta s * Complex.exp (deformationExponent x s)) s₀ =
      analyticOrderAt riemannZeta s₀ := by
  have hF : AnalyticAt ℂ (deformationExponent x) s₀ := (exists_isozeric hσ₀ hsum).1 s₀ hs₀
  have hζ : AnalyticAt ℂ riemannZeta s₀ := by
    have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun s hs =>
      (differentiableAt_riemannZeta hs).differentiableWithinAt
    exact hd.analyticOnNhd hU s₀ hs₁
  have he : AnalyticAt ℂ (fun s => Complex.exp (deformationExponent x s)) s₀ := hF.cexp
  show analyticOrderAt (riemannZeta * fun s => Complex.exp (deformationExponent x s)) s₀ = _
  rw [analyticOrderAt_mul hζ he]
  have h0 : analyticOrderAt (fun s => Complex.exp (deformationExponent x s)) s₀ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (Complex.exp_ne_zero _))
  rw [h0, add_zero]

/-- The isozeric class of `ζ` at abscissa `σ₀`: fibres with summable prime perturbation. -/
def isozericClass (σ₀ : ℝ) : Set GaugeTorus :=
  {x | Summable fun p : Nat.Primes => ‖twist x p - 1‖ * ((p : ℕ) : ℝ) ^ (-σ₀)}

/-- **The isozeric class is Haar-null.** For `½ ≤ σ₀ < 1` a fibre analytically connected to `ζ`
carries its pole at `1`; almost every fibre extends holomorphically across `1`. -/
theorem gaugeHaar_isozericClass_eq_zero {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₁ : σ₀ < 1) :
    gaugeHaar (isozericClass σ₀) = 0 := by
  refine measure_mono_null ?_ (ae_iff.mp ae_fibre_extends_zeroFree)
  intro x hx
  rintro ⟨G, hGa, hGeq, -⟩
  obtain ⟨hFa, hid⟩ := exists_isozeric hσ₀ hx
  set F := deformationExponent x
  have h1R : (1 : ℂ) ∈ rightHalf := by
    show (1 / 2 : ℝ) < (1 : ℂ).re
    norm_num
  have h1F : (1 : ℂ) ∈ {s : ℂ | σ₀ < s.re} := by
    show σ₀ < (1 : ℂ).re
    simpa using hσ₁
  have hGc : ContinuousAt G 1 := (hGa 1 h1R).continuousAt
  have hFc : ContinuousAt F 1 := (hFa 1 h1F).continuousAt
  have hcont : ContinuousAt (fun s => (s - 1) * (G s * Complex.exp (-F s))) 1 :=
    (continuousAt_id.sub continuousAt_const).mul (hGc.mul hFc.neg.cexp)
  have hof : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
    have h := Complex.continuous_ofReal.tendsto (1 : ℝ)
    rw [Complex.ofReal_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hof, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact (ne_of_gt ht) (Complex.ofReal_eq_one.mp h)
  have hlim1 := riemannZeta_residue_one.comp hmap
  have hlim0 : Tendsto (fun t : ℝ => ((t : ℂ) - 1) * (G (t : ℂ) * Complex.exp (-F (t : ℂ))))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    have h := hcont.tendsto.comp hof
    rw [sub_self, zero_mul] at h
    exact h
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 1, ((t : ℂ) - 1) * riemannZeta (t : ℂ) =
      ((t : ℂ) - 1) * (G (t : ℂ) * Complex.exp (-F (t : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hre : 1 < (t : ℂ).re := by simpa using ht
    rw [hGeq t hre, hid t hre, mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
      mul_one]
  exact one_ne_zero (tendsto_nhds_unique (hlim1.congr' heq) hlim0)

end GaloisForLFunctions.ArithmeticWeightTheory
