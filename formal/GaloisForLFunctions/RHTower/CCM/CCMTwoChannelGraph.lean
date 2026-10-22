import GaloisForLFunctions.RHTower.CCM.CCMWeightedSchurSeam

/-!
# The canonical closed two-channel graph of the completed logarithmic source

Three exact mechanisms of the card are formalized here.

*Paired closedness.*  If multiplication by the source is a closed operator and the two channel
projections are complementary idempotents, then the *paired* map `f ↦ (P₊(qf), P₋(qf))` is closed:
the two channels recombine to `qf`, so closedness belongs to the full source constraint.

*One pole is one residue coordinate.*  The Cauchy insertion splits exactly,

```text
c f(z)/(z - w) = c (f z - f w)/(z - w) + c f w/(z - w) ,
```

the first summand being causal and the second the rank-one anti-causal residue coordinate.  Its
reflected Paley–Wiener vector is `c e^{-Im w · t} e^{-i Re w · t}`, whose `L²` energy is exactly
`|c|²/(2 Im w)` — the inverse-horizontal charge.

*The bilateral atom.*  The polarized exponential atom factors through `L²(0,1)` with two feature
maps of **opposite** causal orientation, which is the atomic form of the paired graph.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Paired closedness -/

/-- **Section 1, statement 2.**  The paired channel map of a closed source operator is closed: the
two Hardy channels recombine to the full source constraint. -/
theorem pairedGraph_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Pp Pm : E →L[ℂ] E) (hsum : ∀ x, Pp x + Pm x = x)
    (hPP : ∀ x, Pp (Pp x) = Pp x) (hPM : ∀ x, Pp (Pm x) = 0)
    (hMM : ∀ x, Pm (Pm x) = Pm x) (hMP : ∀ x, Pm (Pp x) = 0)
    {D : Set E} {T : E → E}
    (hTclosed : ∀ (u : ℕ → E) (f g : E), (∀ n, u n ∈ D) → Tendsto u atTop (nhds f) →
      Tendsto (fun n => T (u n)) atTop (nhds g) → f ∈ D ∧ T f = g)
    (u : ℕ → E) (f gp gm : E) (hu : ∀ n, u n ∈ D)
    (huf : Tendsto u atTop (nhds f))
    (hgp : Tendsto (fun n => Pp (T (u n))) atTop (nhds gp))
    (hgm : Tendsto (fun n => Pm (T (u n))) atTop (nhds gm)) :
    f ∈ D ∧ Pp (T f) = gp ∧ Pm (T f) = gm := by
  have hTu : Tendsto (fun n => T (u n)) atTop (nhds (gp + gm)) := by
    refine (hgp.add hgm).congr fun n => ?_
    exact hsum (T (u n))
  obtain ⟨hfD, hTf⟩ := hTclosed u f (gp + gm) hu huf hTu
  refine ⟨hfD, ?_, ?_⟩
  · have hfix : Pp gp = gp := by
      have h1 : Tendsto (fun n => Pp (Pp (T (u n)))) atTop (nhds (Pp gp)) :=
        (Pp.continuous.tendsto gp).comp hgp
      have h2 : Tendsto (fun n => Pp (Pp (T (u n)))) atTop (nhds gp) := by
        refine hgp.congr fun n => (hPP (T (u n))).symm
      exact tendsto_nhds_unique h1 h2
    have hkill : Pp gm = 0 := by
      have h1 : Tendsto (fun n => Pp (Pm (T (u n)))) atTop (nhds (Pp gm)) :=
        (Pp.continuous.tendsto gm).comp hgm
      have h2 : Tendsto (fun n => Pp (Pm (T (u n)))) atTop (nhds 0) := by
        refine tendsto_const_nhds.congr fun n => (hPM (T (u n))).symm
      exact tendsto_nhds_unique h1 h2
    rw [hTf, map_add, hfix, hkill, add_zero]
  · have hfix : Pm gm = gm := by
      have h1 : Tendsto (fun n => Pm (Pm (T (u n)))) atTop (nhds (Pm gm)) :=
        (Pm.continuous.tendsto gm).comp hgm
      have h2 : Tendsto (fun n => Pm (Pm (T (u n)))) atTop (nhds gm) := by
        refine hgm.congr fun n => (hMM (T (u n))).symm
      exact tendsto_nhds_unique h1 h2
    have hkill : Pm gp = 0 := by
      have h1 : Tendsto (fun n => Pm (Pp (T (u n)))) atTop (nhds (Pm gp)) :=
        (Pm.continuous.tendsto gp).comp hgp
      have h2 : Tendsto (fun n => Pm (Pp (T (u n)))) atTop (nhds 0) := by
        refine tendsto_const_nhds.congr fun n => (hMP (T (u n))).symm
      exact tendsto_nhds_unique h1 h2
    rw [hTf, map_add, hfix, hkill, zero_add]

/-! ## One pole is one residue coordinate -/

/-- **Equation (12).**  The Cauchy insertion splits exactly into a causal difference quotient and a
rank-one anti-causal residue term. -/
theorem cauchy_insertion_split (c w z : ℂ) (F : ℂ → ℂ) (hz : z - w ≠ 0) :
    c / (z - w) * F z = c * ((F z - F w) / (z - w)) + c * F w / (z - w) := by
  field_simp
  ring

/-- **Equation (14), energy.**  The reflected Paley–Wiener residue vector has `L²` energy exactly
`|c|²/(2 Im w)`: the inverse-horizontal charge. -/
theorem residue_vector_energy {c : ℂ} {a b : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), ‖c * Complex.exp (-(a : ℂ) * (t : ℂ))
        * Complex.exp (-Complex.I * (b : ℂ) * (t : ℂ))‖ ^ (2 : ℕ))
      = ‖c‖ ^ (2 : ℕ) / (2 * a) := by
  have hpt : ∀ t : ℝ, ‖c * Complex.exp (-(a : ℂ) * (t : ℂ))
      * Complex.exp (-Complex.I * (b : ℂ) * (t : ℂ))‖ ^ (2 : ℕ)
      = ‖c‖ ^ (2 : ℕ) * (Real.exp (-(a * t)) * Real.exp (-(a * t))) := by
    intro t
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : (-(a : ℂ) * (t : ℂ)).re = -(a * t) := by
      simp [Complex.mul_re]
    have h2 : (-Complex.I * (b : ℂ) * (t : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [h1, h2, Real.exp_zero, mul_one]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t]
  rw [MeasureTheory.integral_const_mul]
  have hray : (∫ t in Ioi (0 : ℝ), Real.exp (-(a * t)) * Real.exp (-(a * t)))
      = 1 / (a + a) := integral_exp_ray (by linarith)
  rw [hray]
  have : a + a = 2 * a := by ring
  rw [this]
  ring

/-! ## The bilateral atom -/

/-- The exponential average appearing in the bilateral factorization. -/
theorem integral_cexp_unit {α : ℂ} (hα : α ≠ 0) :
    (∫ u in (0 : ℝ)..1, Complex.exp (α * (u : ℂ))) = (Complex.exp α - 1) / α := by
  have hderiv : ∀ u : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (α * (s : ℂ)) / α)
      (Complex.exp (α * (u : ℂ))) u := by
    intro u
    have hofr : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
    have hlin : HasDerivAt (fun s : ℝ => α * (s : ℂ)) α u := by
      simpa using hofr.const_mul α
    have hexp := hlin.cexp
    have hdiv := hexp.div_const α
    refine hdiv.congr_deriv ?_
    field_simp
  have hcont : Continuous fun s : ℝ => Complex.exp (α * (s : ℂ)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (hcont.intervalIntegrable 0 1)]
  push_cast
  rw [mul_one, mul_zero, Complex.exp_zero, div_sub_div_same]

/-- **Equation (17a).**  The polarized exponential atom factors through `L²(0,1)` with two feature
maps of opposite causal orientation. -/
theorem bilateral_atom_factorization {t : ℝ} {z c : ℂ} (ht : t ≠ 0) (hzc : z - c ≠ 0) :
    (Complex.exp (-Complex.I * c * (t : ℂ)) - Complex.exp (-Complex.I * z * (t : ℂ))) / (z - c)
      = Complex.I * (t : ℂ)
        * ∫ u in (0 : ℝ)..1, Complex.exp (-Complex.I * (t : ℂ) * (1 - (u : ℂ)) * z)
            * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ) * c) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hα : Complex.I * (t : ℂ) * (z - c) ≠ 0 :=
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero htC) hzc
  have hcongr : ∀ u : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (1 - (u : ℂ)) * z)
      * Complex.exp (-Complex.I * (t : ℂ) * (u : ℂ) * c)
      = Complex.exp (-Complex.I * (t : ℂ) * z)
        * Complex.exp ((Complex.I * (t : ℂ) * (z - c)) * (u : ℂ)) := by
    intro u
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [intervalIntegral.integral_congr fun u _ => hcongr u]
  rw [intervalIntegral.integral_const_mul, integral_cexp_unit hα]
  field_simp
  rw [mul_sub, mul_one,
    show Complex.exp (-(Complex.I * (t : ℂ) * z)) * Complex.exp (Complex.I * (t : ℂ) * (z - c))
      = Complex.exp (-(Complex.I * c * (t : ℂ))) from by
      rw [← Complex.exp_add]
      congr 1
      ring]

end GaloisForLFunctions.RHTower

end
