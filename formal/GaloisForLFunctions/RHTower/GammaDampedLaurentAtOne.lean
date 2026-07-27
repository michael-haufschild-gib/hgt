import GaloisForLFunctions.RHTower.GammaDampedDirichletSeries

/-!
# The Laurent structure of the damped squarefree series at the critical point

Removing the pole of `ζ` in its completed normalisation gives an entire function

```text
A(z) = ζ(z) - 1/((z-1) Γℝ(z)) ,
```

so on the Euler half plane the damped series splits as

```text
F(z) = C(z) + B(z)/(z-1),
B(z) = 1/(Γℝ(z) ζ(2z)),   C(z) = A(z)/ζ(2z) + H(z),
```

with `B` and `C` holomorphic on `re z > 1/2` and `B(1) = 1/ζ(2)`.  This is the exact additive form
of the Dirichlet reduction, and it gives both critical scalings

```text
(z-1) F(z) → 1/ζ(2),        (z-1)² F'(z) → -1/ζ(2).
```
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ### Entire pole-free part of zeta -/

/-- Riemann zeta with its pole removed in the completed normalisation. -/
def zetaPoleFree (s : ℂ) : ℂ := riemannZeta s - 1 / (s - 1) / Complex.Gammaℝ s

theorem differentiable_zetaPoleFree : Differentiable ℂ zetaPoleFree := by
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · have h := HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div 0
    rw [HurwitzZeta.hurwitzZeta_zero] at h
    exact h
  · have h1 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
    have h2 : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1) / Complex.Gammaℝ z) s := by
      have hinv : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s :=
        Complex.differentiable_Gammaℝ_inv s
      have hd : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
        DifferentiableAt.div (differentiableAt_const 1) (by fun_prop) (sub_ne_zero.mpr hs)
      simpa [div_eq_mul_inv] using hd.mul hinv
    exact h1.sub h2

theorem analyticAt_zetaPoleFree (s : ℂ) : AnalyticAt ℂ zetaPoleFree s :=
  (differentiable_zetaPoleFree.differentiableOn.analyticOnNhd isOpen_univ) s (Set.mem_univ s)

/-! ### The doubled zeta factor -/

theorem re_two_mul (z : ℂ) : (2 * z).re = 2 * z.re := by simp

theorem riemannZeta_two_mul_ne_zero {s : ℂ} (hs : 1 / 2 ≤ s.re) : riemannZeta (2 * s) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_le_re ?_
  rw [re_two_mul]
  linarith

theorem analyticAt_riemannZeta_two_mul {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s := by
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (DifferentiableOn.analyticOnNhd ?_ hopen) s hs
  intro z hz
  have hz2 : (2 * z) ≠ 1 := by
    intro h
    have hre : (2 * z).re = 1 := by rw [h]; simp
    rw [re_two_mul] at hre
    have : 1 / 2 < z.re := hz
    linarith
  exact ((differentiableAt_riemannZeta hz2).comp z (by fun_prop)).differentiableWithinAt

/-! ### The Laurent parts -/

/-- Residue factor `B(z) = 1/(Γℝ(z) ζ(2z))`. -/
def gammaDampedResidueFactor (s : ℂ) : ℂ := (Complex.Gammaℝ s)⁻¹ * (riemannZeta (2 * s))⁻¹

/-- Pole-free part `C(z) = A(z)/ζ(2z) + H(z)`. -/
def gammaDampedPoleFree (s : ℂ) : ℂ :=
  zetaPoleFree s * (riemannZeta (2 * s))⁻¹ + gammaDampedCorrectionLSeries s

theorem gammaDampedResidueFactor_one : gammaDampedResidueFactor 1 = 1 / riemannZeta 2 := by
  rw [gammaDampedResidueFactor, Complex.Gammaℝ_one]
  norm_num

theorem analyticAt_gammaDampedResidueFactor {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ gammaDampedResidueFactor s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s :=
    (Complex.differentiable_Gammaℝ_inv.differentiableOn.analyticOnNhd isOpen_univ) s
      (Set.mem_univ s)
  have h2 : AnalyticAt ℂ (fun z : ℂ => (riemannZeta (2 * z))⁻¹) s :=
    (analyticAt_riemannZeta_two_mul hs).inv (riemannZeta_two_mul_ne_zero hs.le)
  exact h1.mul h2

theorem analyticAt_gammaDampedPoleFree {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ gammaDampedPoleFree s := by
  have h1 : AnalyticAt ℂ zetaPoleFree s := analyticAt_zetaPoleFree s
  have h2 : AnalyticAt ℂ (fun z : ℂ => (riemannZeta (2 * z))⁻¹) s :=
    (analyticAt_riemannZeta_two_mul hs).inv (riemannZeta_two_mul_ne_zero hs.le)
  have h3 : AnalyticAt ℂ gammaDampedCorrectionLSeries s :=
    analyticOnNhd_gammaDampedCorrectionLSeries s (by
      have : (1 : ℝ) / 2 < s.re := hs
      simp only [Set.mem_setOf_eq]
      linarith)
  exact (h1.mul h2).add h3

/-- **The Laurent form of the damped series.**  `F(z) = C(z) + B(z)/(z-1)` on `re z > 1`. -/
theorem lSeries_gammaDampedCoeff_laurent {s : ℂ} (hs : 1 < s.re) :
    LSeries gammaDampedCoeff s
      = gammaDampedPoleFree s + gammaDampedResidueFactor s / (s - 1) := by
  have hz : riemannZeta s = zetaPoleFree s + 1 / (s - 1) / Complex.Gammaℝ s := by
    rw [zetaPoleFree]
    ring
  rw [lSeries_gammaDampedCoeff hs, gammaDampedPoleFree, gammaDampedResidueFactor, hz]
  simp only [div_eq_mul_inv]
  ring

/-! ### The two critical scalings -/

theorem hasDerivAt_gammaDampedLaurent {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (fun z : ℂ => gammaDampedPoleFree z + gammaDampedResidueFactor z / (z - 1))
      (deriv gammaDampedPoleFree s +
        (deriv gammaDampedResidueFactor s * (s - 1) - gammaDampedResidueFactor s * 1) /
          (s - 1) ^ 2) s := by
  have hhalf : (1 : ℝ) / 2 < s.re := by linarith
  have hC : HasDerivAt gammaDampedPoleFree (deriv gammaDampedPoleFree s) s :=
    (analyticAt_gammaDampedPoleFree hhalf).differentiableAt.hasDerivAt
  have hB : HasDerivAt gammaDampedResidueFactor (deriv gammaDampedResidueFactor s) s :=
    (analyticAt_gammaDampedResidueFactor hhalf).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => z - 1) 1 s := by
    simpa using (hasDerivAt_id s).sub_const 1
  have hne : s - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hs
    simp at hs
  exact hC.add (hB.div hd hne)

theorem deriv_lSeries_gammaDampedCoeff {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries gammaDampedCoeff) s
      = deriv gammaDampedPoleFree s +
        (deriv gammaDampedResidueFactor s * (s - 1) - gammaDampedResidueFactor s * 1) /
          (s - 1) ^ 2 := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : Set.EqOn (LSeries gammaDampedCoeff)
      (fun z : ℂ => gammaDampedPoleFree z + gammaDampedResidueFactor z / (z - 1))
      {z : ℂ | 1 < z.re} := fun _ hz => lSeries_gammaDampedCoeff_laurent hz
  rw [(heq.eventuallyEq_of_mem (hopen.mem_nhds hs)).deriv_eq]
  exact (hasDerivAt_gammaDampedLaurent hs).deriv

/-- **The derivative scaling.**  `(z-1)² F'(z) → -1/ζ(2)` in the Euler half plane. -/
theorem tendsto_sub_one_sq_mul_deriv_lSeries_gammaDampedCoeff :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv (LSeries gammaDampedCoeff) s)
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) (nhds (-(1 / riemannZeta 2))) := by
  have hhalf : (1 : ℝ) / 2 < (1 : ℂ).re := by norm_num
  have hC : ContinuousAt (deriv gammaDampedPoleFree) 1 :=
    ((analyticAt_gammaDampedPoleFree hhalf).deriv).continuousAt
  have hB : ContinuousAt (deriv gammaDampedResidueFactor) 1 :=
    ((analyticAt_gammaDampedResidueFactor hhalf).deriv).continuousAt
  have hB0 : ContinuousAt gammaDampedResidueFactor 1 :=
    (analyticAt_gammaDampedResidueFactor hhalf).continuousAt
  have hsub : Tendsto (fun s : ℂ => s - 1) (nhds (1 : ℂ)) (nhds 0) := by
    simpa using (continuous_sub_right (1 : ℂ)).tendsto (1 : ℂ)
  have h1 : Tendsto (fun s : ℂ => (s - 1) ^ 2 * deriv gammaDampedPoleFree s)
      (nhds (1 : ℂ)) (nhds 0) := by
    have := (hsub.pow 2).mul hC.tendsto
    simpa using this
  have h2 : Tendsto (fun s : ℂ => deriv gammaDampedResidueFactor s * (s - 1) -
      gammaDampedResidueFactor s * 1) (nhds (1 : ℂ)) (nhds (-(1 / riemannZeta 2))) := by
    have ha := hB.tendsto.mul hsub
    have hb := hB0.tendsto
    rw [gammaDampedResidueFactor_one] at hb
    have hb1 : Tendsto (fun s : ℂ => gammaDampedResidueFactor s * 1) (nhds (1 : ℂ))
        (nhds (1 / riemannZeta 2)) := by simpa using hb
    have := ha.sub hb1
    simpa using this
  have hmain := h1.add h2
  rw [zero_add] at hmain
  refine Tendsto.congr' ?_ (hmain.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hne : s - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hs
    simp at hs
  rw [deriv_lSeries_gammaDampedCoeff hs]
  field_simp

/-- **The value scaling in Laurent form.**  `(z-1) F(z) → 1/ζ(2)`. -/
theorem tendsto_sub_one_mul_lSeries_gammaDampedCoeff_laurent :
    Tendsto (fun s : ℂ => (s - 1) * LSeries gammaDampedCoeff s)
      (nhdsWithin 1 {s : ℂ | 1 < s.re}) (nhds (1 / riemannZeta 2)) :=
  tendsto_sub_one_mul_lSeries_gammaDampedCoeff

end

end RHTower
