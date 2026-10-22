import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalArithmeticMellin

/-!
# Suzuki completion annihilates the positive Euler main pole

For `ω > 0` the shifted Euler quotient `C_ω(s) = ζ(s-ω)/ζ(s+ω)` has its leading pole at
`s₀ = 1 + ω`, with residue `1/ζ(1+2ω) > 0`.  The archimedean quotient
`G_ω(s) = γ(s-ω)/γ(s+ω)` built from the pole-cleared factor
`γ(s) = s(s-1)π^{-s/2}Γ(s/2)/2` has a simple *zero* at exactly the same point, because `γ(1) = 0`.

This module proves, unconditionally:

* the exact residue `Res_{s=s₀} C_ω = 1/ζ(1+2ω)`;
* the exact simple-zero factorization `G_ω(s) = (s - s₀) · γ̃(s-ω)/γ(s+ω)` with `γ̃(1) = 1/2`,
  hence `G_ω(s)/(s-s₀) → 1/(2γ(1+2ω))`;
* the finite completed limit `G_ω(s) C_ω(s) → 1/(2 Ξ(1+2ω)) = Ξ(1)/Ξ(1+2ω)`;
* the two archimedean moment annihilations `∫₀¹ g_ω(x) x^{1+ω} dx/x = 0` and
  `∫₀¹ g_ω^{⟨1⟩}(x) x^{1+ω} dx/x = 0` for Suzuki's literal compact kernel and its literal
  once-integrated primitive.

The moment statements are the exact Mellin transforms of the literal source kernels
`suzukiSourceG` and `suzukiSourceGOne` at the boundary point `s = 1 + ω`, a point outside the
half-plane `1 + ω < Re s` used by the existing convergence theorems; the boundary case is
established here directly from the explicit Gamma-ratio transform.
-/

namespace RHTower

noncomputable section

open Complex Filter Topology Set MeasureTheory

/-! ## The reduced archimedean factor -/

/-- The archimedean factor with its zero at `s = 1` divided out:
`γ̃(s) = (s/2) Γ_ℝ(s)`, so that `γ(s) = (s-1) γ̃(s)`. -/
def suzukiReducedArchimedeanFactor (s : ℂ) : ℂ := s / 2 * Complex.Gammaℝ s

/-- The archimedean factor is `(s-1)` times its reduced form. -/
theorem suzukiArchimedeanFactor_eq_sub_one_mul_reduced (s : ℂ) :
    suzukiArchimedeanFactor s = (s - 1) * suzukiReducedArchimedeanFactor s := by
  rw [suzukiArchimedeanFactor_eq_archFactor, archFactor, suzukiReducedArchimedeanFactor]
  ring

/-- `γ̃(1) = 1/2`; equivalently `γ` has derivative `1/2` at its simple zero `s = 1`. -/
theorem suzukiReducedArchimedeanFactor_one : suzukiReducedArchimedeanFactor 1 = 1 / 2 := by
  rw [suzukiReducedArchimedeanFactor]
  simp

/-- `Γ_ℝ` is differentiable off the Gamma poles. -/
theorem differentiableAt_Gammaℝ_of_ne {z : ℂ} (hne : ∀ m : ℕ, z / 2 ≠ -(m : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ z := by
  have hdiv : DifferentiableAt ℂ (fun s : ℂ => s / 2) z := by fun_prop
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) z :=
    (Complex.differentiableAt_Gamma (z / 2) hne).comp z hdiv
  rw [show (Complex.Gammaℝ) = fun s => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) by
    funext s; rw [Complex.Gammaℝ_def]]
  exact (DifferentiableAt.const_cpow (by fun_prop)
      (Or.inl (by exact_mod_cast Real.pi_ne_zero))).mul h2

/-- At a point of positive real part the Gamma poles are avoided. -/
theorem gammaHalf_ne_neg_nat {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z / 2 ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- `Γ_ℝ` is continuous on the open right half-plane. -/
theorem continuousAt_Gammaℝ_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.Gammaℝ z :=
  (differentiableAt_Gammaℝ_of_ne (gammaHalf_ne_neg_nat hz)).continuousAt

/-- The reduced archimedean factor is continuous on the open right half-plane. -/
theorem continuousAt_suzukiReducedArchimedeanFactor_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt suzukiReducedArchimedeanFactor z := by
  show ContinuousAt (fun s : ℂ => s / 2 * Complex.Gammaℝ s) z
  exact (continuousAt_id.div_const 2).mul (continuousAt_Gammaℝ_of_re_pos hz)

/-- The archimedean factor is continuous on the open right half-plane. -/
theorem continuousAt_suzukiArchimedeanFactor_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt suzukiArchimedeanFactor z := by
  have h : ContinuousAt (fun s : ℂ => (s - 1) * suzukiReducedArchimedeanFactor s) z :=
    (continuousAt_id.sub continuousAt_const).mul
      (continuousAt_suzukiReducedArchimedeanFactor_of_re_pos hz)
  refine h.congr ?_
  filter_upwards with s
  exact (suzukiArchimedeanFactor_eq_sub_one_mul_reduced s).symm

/-- The archimedean factor is nonzero at a real point `> 1`. -/
theorem suzukiArchimedeanFactor_ne_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    suzukiArchimedeanFactor ((x : ℝ) : ℂ) ≠ 0 := by
  have h0 : ((x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have h1 : ((x : ℝ) : ℂ) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hG : Complex.Gammaℝ ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using by linarith)
  rw [suzukiArchimedeanFactor_eq_archFactor, archFactor]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 h1) two_ne_zero) hG

/-! ## The two quotients at the Euler pole -/

/-- The shifted Euler quotient `C_ω(s) = ζ(s-ω)/ζ(s+ω)`. -/
def suzukiEulerQuotient (ω : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s - (ω : ℂ)) / riemannZeta (s + (ω : ℂ))

/-- The archimedean quotient `G_ω(s) = γ(s-ω)/γ(s+ω)`. -/
def suzukiArchimedeanQuotient (ω : ℝ) (s : ℂ) : ℂ :=
  suzukiArchimedeanFactor (s - (ω : ℂ)) / suzukiArchimedeanFactor (s + (ω : ℂ))

/-- The base point `s₀ = 1 + ω` of the shifted Euler pole. -/
def suzukiEulerPolePoint (ω : ℝ) : ℂ := ((1 + ω : ℝ) : ℂ)

theorem suzukiEulerPolePoint_re (ω : ℝ) : (suzukiEulerPolePoint ω).re = 1 + ω := by
  simp [suzukiEulerPolePoint]

theorem suzukiEulerPolePoint_sub (ω : ℝ) : suzukiEulerPolePoint ω - (ω : ℂ) = 1 := by
  rw [suzukiEulerPolePoint]
  push_cast
  ring

theorem suzukiEulerPolePoint_add (ω : ℝ) :
    suzukiEulerPolePoint ω + (ω : ℂ) = ((1 + 2 * ω : ℝ) : ℂ) := by
  rw [suzukiEulerPolePoint]
  push_cast
  ring

theorem sub_suzukiEulerPolePoint (ω : ℝ) (s : ℂ) :
    s - (ω : ℂ) - 1 = s - suzukiEulerPolePoint ω := by
  rw [suzukiEulerPolePoint]
  push_cast
  ring

/-- Punctured approach in the shifted variable. -/
theorem tendsto_sub_nhdsWithin_suzukiEulerPolePoint (ω : ℝ) :
    Tendsto (fun s : ℂ => s - (ω : ℂ)) (𝓝[≠] (suzukiEulerPolePoint ω)) (𝓝[≠] 1) := by
  have hcont : Tendsto (fun s : ℂ => s - (ω : ℂ)) (𝓝 (suzukiEulerPolePoint ω)) (𝓝 1) := by
    have h : ContinuousAt (fun s : ℂ => s - (ω : ℂ)) (suzukiEulerPolePoint ω) := by fun_prop
    have h2 := h.tendsto
    rwa [suzukiEulerPolePoint_sub ω] at h2
  rw [tendsto_nhdsWithin_iff]
  refine ⟨hcont.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_compl_iff, mem_singleton_iff] at hs ⊢
  intro h
  exact hs (by linear_combination h - sub_suzukiEulerPolePoint ω s)

/-- **Theorem A, equation (4).**  The shifted Euler quotient has residue `1/ζ(1+2ω) > 0` at its
leading pole `s₀ = 1 + ω`. -/
theorem tendsto_sub_mul_suzukiEulerQuotient {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun s => (s - suzukiEulerPolePoint ω) * suzukiEulerQuotient ω s)
      (𝓝[≠] (suzukiEulerPolePoint ω))
      (𝓝 (1 / riemannZeta ((1 + 2 * ω : ℝ) : ℂ))) := by
  have hζne : riemannZeta ((1 + 2 * ω : ℝ) : ℂ) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp
    linarith
  have hnum :
      Tendsto (fun s : ℂ => (s - (ω : ℂ) - 1) * riemannZeta (s - (ω : ℂ)))
        (𝓝[≠] (suzukiEulerPolePoint ω)) (𝓝 1) :=
    riemannZeta_residue_one.comp (tendsto_sub_nhdsWithin_suzukiEulerPolePoint ω)
  have hne : suzukiEulerPolePoint ω + (ω : ℂ) ≠ 1 := by
    rw [suzukiEulerPolePoint_add ω]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hz : ContinuousAt riemannZeta (suzukiEulerPolePoint ω + (ω : ℂ)) :=
    (differentiableAt_riemannZeta hne).continuousAt
  have hshift : ContinuousAt (fun s : ℂ => s + (ω : ℂ)) (suzukiEulerPolePoint ω) := by fun_prop
  have hdenC : ContinuousAt (fun s : ℂ => riemannZeta (s + (ω : ℂ)))
      (suzukiEulerPolePoint ω) :=
    ContinuousAt.comp (g := riemannZeta) (f := fun s : ℂ => s + (ω : ℂ))
      (x := suzukiEulerPolePoint ω) hz hshift
  have hden : Tendsto (fun s : ℂ => riemannZeta (s + (ω : ℂ)))
      (𝓝[≠] (suzukiEulerPolePoint ω)) (𝓝 (riemannZeta ((1 + 2 * ω : ℝ) : ℂ))) := by
    have h2 := hdenC.tendsto.mono_left
      (nhdsWithin_le_nhds (a := suzukiEulerPolePoint ω) (s := {suzukiEulerPolePoint ω}ᶜ))
    rwa [suzukiEulerPolePoint_add ω] at h2
  have hquot := hnum.div hden hζne
  refine hquot.congr fun s => ?_
  show (s - (ω : ℂ) - 1) * riemannZeta (s - (ω : ℂ)) / riemannZeta (s + (ω : ℂ)) = _
  rw [suzukiEulerQuotient, sub_suzukiEulerPolePoint ω s, mul_div_assoc]

/-! ## The archimedean simple zero -/

/-- **Theorem A, equation (5), exact form.**  The archimedean quotient vanishes to first order at
`s₀ = 1 + ω`, with the explicit cofactor `γ̃(s-ω)/γ(s+ω)`. -/
theorem suzukiArchimedeanQuotient_eq_sub_mul (ω : ℝ) (s : ℂ) :
    suzukiArchimedeanQuotient ω s =
      (s - suzukiEulerPolePoint ω) *
        (suzukiReducedArchimedeanFactor (s - (ω : ℂ)) /
          suzukiArchimedeanFactor (s + (ω : ℂ))) := by
  rw [suzukiArchimedeanQuotient, suzukiArchimedeanFactor_eq_sub_one_mul_reduced (s - (ω : ℂ)),
    sub_suzukiEulerPolePoint ω s, mul_div_assoc]

/-- The archimedean quotient vanishes at the Euler pole: the completion kills the main term. -/
theorem suzukiArchimedeanQuotient_eq_zero (ω : ℝ) :
    suzukiArchimedeanQuotient ω (suzukiEulerPolePoint ω) = 0 := by
  rw [suzukiArchimedeanQuotient_eq_sub_mul, sub_self, zero_mul]

/-- The cofactor of the archimedean simple zero is continuous at the Euler pole, with value
`1/(2γ(1+2ω))`. -/
theorem tendsto_suzukiArchimedeanCofactor {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun s : ℂ => suzukiReducedArchimedeanFactor (s - (ω : ℂ)) /
        suzukiArchimedeanFactor (s + (ω : ℂ)))
      (𝓝 (suzukiEulerPolePoint ω))
      (𝓝 (1 / (2 * suzukiArchimedeanFactor ((1 + 2 * ω : ℝ) : ℂ)))) := by
  have hγne : suzukiArchimedeanFactor ((1 + 2 * ω : ℝ) : ℂ) ≠ 0 :=
    suzukiArchimedeanFactor_ne_zero_of_one_lt (by linarith)
  have hreM : (0 : ℝ) < ((suzukiEulerPolePoint ω) - (ω : ℂ)).re := by
    rw [suzukiEulerPolePoint_sub ω]
    norm_num
  have hreP : (0 : ℝ) < ((suzukiEulerPolePoint ω) + (ω : ℂ)).re := by
    rw [suzukiEulerPolePoint_add ω]
    simp
    linarith
  have hsubC : ContinuousAt (fun s : ℂ => s - (ω : ℂ)) (suzukiEulerPolePoint ω) := by fun_prop
  have haddC : ContinuousAt (fun s : ℂ => s + (ω : ℂ)) (suzukiEulerPolePoint ω) := by fun_prop
  have hnum : ContinuousAt (fun s : ℂ => suzukiReducedArchimedeanFactor (s - (ω : ℂ)))
      (suzukiEulerPolePoint ω) :=
    ContinuousAt.comp (g := suzukiReducedArchimedeanFactor) (f := fun s : ℂ => s - (ω : ℂ))
      (x := suzukiEulerPolePoint ω)
      (continuousAt_suzukiReducedArchimedeanFactor_of_re_pos hreM) hsubC
  have hden : ContinuousAt (fun s : ℂ => suzukiArchimedeanFactor (s + (ω : ℂ)))
      (suzukiEulerPolePoint ω) :=
    ContinuousAt.comp (g := suzukiArchimedeanFactor) (f := fun s : ℂ => s + (ω : ℂ))
      (x := suzukiEulerPolePoint ω)
      (continuousAt_suzukiArchimedeanFactor_of_re_pos hreP) haddC
  have hdenne : suzukiArchimedeanFactor (suzukiEulerPolePoint ω + (ω : ℂ)) ≠ 0 := by
    rw [suzukiEulerPolePoint_add ω]
    exact hγne
  have hct : ContinuousAt (fun s : ℂ => suzukiReducedArchimedeanFactor (s - (ω : ℂ)) /
      suzukiArchimedeanFactor (s + (ω : ℂ))) (suzukiEulerPolePoint ω) :=
    hnum.div hden hdenne
  have h := hct.tendsto
  have hval : suzukiReducedArchimedeanFactor (suzukiEulerPolePoint ω - (ω : ℂ)) /
      suzukiArchimedeanFactor (suzukiEulerPolePoint ω + (ω : ℂ))
      = 1 / (2 * suzukiArchimedeanFactor ((1 + 2 * ω : ℝ) : ℂ)) := by
    rw [suzukiEulerPolePoint_sub ω, suzukiEulerPolePoint_add ω,
      suzukiReducedArchimedeanFactor_one, div_div]
  rw [hval] at h
  exact h

/-- **Theorem A, equation (5).**  The archimedean quotient divided by `(s - s₀)` converges to
`1/(2γ(1+2ω))`: the zero is simple with the stated leading coefficient. -/
theorem tendsto_suzukiArchimedeanQuotient_div_sub {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun s => suzukiArchimedeanQuotient ω s / (s - suzukiEulerPolePoint ω))
      (𝓝[≠] (suzukiEulerPolePoint ω))
      (𝓝 (1 / (2 * suzukiArchimedeanFactor ((1 + 2 * ω : ℝ) : ℂ)))) := by
  refine ((tendsto_suzukiArchimedeanCofactor hω).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hsne : s - suzukiEulerPolePoint ω ≠ 0 := sub_ne_zero_of_ne hs
  rw [suzukiArchimedeanQuotient_eq_sub_mul, mul_comm, mul_div_assoc, div_self hsne, mul_one]

/-! ## The completed limit -/

/-- The completed function `Ξ` factors as archimedean factor times zeta at real points `> 1`. -/
theorem xi_eq_suzukiArchimedeanFactor_mul_zeta_of_one_lt {x : ℝ} (hx : 1 < x) :
    xi ((x : ℝ) : ℂ) = suzukiArchimedeanFactor ((x : ℝ) : ℂ) * riemannZeta ((x : ℝ) : ℂ) := by
  have h0 : ((x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have h1 : ((x : ℝ) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hG : Complex.Gammaℝ ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using by linarith)
  rw [suzukiArchimedeanFactor_eq_archFactor, xi_eq_archFactor_mul_zeta h0 h1 hG]

/-- **Theorem A, equation (6).**  The completed product has a finite limit at the annihilated
Euler pole, equal to `1/(2 Ξ(1+2ω))`. -/
theorem tendsto_suzukiArchimedeanQuotient_mul_suzukiEulerQuotient {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun s => suzukiArchimedeanQuotient ω s * suzukiEulerQuotient ω s)
      (𝓝[≠] (suzukiEulerPolePoint ω))
      (𝓝 (1 / (2 * xi ((1 + 2 * ω : ℝ) : ℂ)))) := by
  have hγne : suzukiArchimedeanFactor ((1 + 2 * ω : ℝ) : ℂ) ≠ 0 :=
    suzukiArchimedeanFactor_ne_zero_of_one_lt (by linarith)
  have hζne : riemannZeta ((1 + 2 * ω : ℝ) : ℂ) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp
    linarith
  have hcof := (tendsto_suzukiArchimedeanCofactor hω).mono_left
    (nhdsWithin_le_nhds (a := suzukiEulerPolePoint ω) (s := {suzukiEulerPolePoint ω}ᶜ))
  have hpole := tendsto_sub_mul_suzukiEulerQuotient hω
  have hmul := hcof.mul hpole
  have hlimval : (1 / (2 * suzukiArchimedeanFactor ((1 + 2 * ω : ℝ) : ℂ))) *
      (1 / riemannZeta ((1 + 2 * ω : ℝ) : ℂ)) = 1 / (2 * xi ((1 + 2 * ω : ℝ) : ℂ)) := by
    rw [xi_eq_suzukiArchimedeanFactor_mul_zeta_of_one_lt (x := 1 + 2 * ω) (by linarith),
      div_mul_div_comm, one_mul]
    congr 1
    ring
  rw [← hlimval]
  refine hmul.congr fun s => ?_
  rw [suzukiArchimedeanQuotient_eq_sub_mul]
  ring

/-- **Theorem A, equation (6), source form.**  The completed limit is `Ξ(1)/Ξ(1+2ω)`. -/
theorem tendsto_suzukiArchimedeanQuotient_mul_suzukiEulerQuotient_xi_ratio {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun s => suzukiArchimedeanQuotient ω s * suzukiEulerQuotient ω s)
      (𝓝[≠] (suzukiEulerPolePoint ω))
      (𝓝 (xi 1 / xi ((1 + 2 * ω : ℝ) : ℂ))) := by
  have h := tendsto_suzukiArchimedeanQuotient_mul_suzukiEulerQuotient hω
  have hxi : xi 1 = 1 / 2 := by simp [xi]
  rw [hxi, div_div]
  exact h

/-! ## Archimedean moment annihilation -/

/-- **Theorem B, equation (7).**  Suzuki's literal compact kernel has vanishing `(1+ω)`-moment:
the archimedean factor kills the Euler main term exactly. -/
theorem hasMellin_suzukiCanonicalG_at_eulerPole {ω : ℝ} (hω : 0 < ω) :
    HasMellin (suzukiCanonicalG ω) (suzukiEulerPolePoint ω) 0 := by
  have hre : (suzukiEulerPolePoint ω).re = 1 + ω := suzukiEulerPolePoint_re ω
  have h := hasMellin_suzukiCanonicalG_explicit (omega := ω) hω
    (s := suzukiEulerPolePoint ω) (by rw [hre]; linarith) (by rw [hre]; linarith)
  have hval : ((Real.pi : ℂ) ^ (ω : ℂ) *
        (Complex.Gamma ((suzukiEulerPolePoint ω - (ω : ℂ)) / 2 + 1) /
          Complex.Gamma ((suzukiEulerPolePoint ω + (ω : ℂ)) / 2 + 1)) -
      ((2 * ω : ℝ) : ℂ) * (Real.pi : ℂ) ^ (ω : ℂ) *
        ((Complex.Gamma ((suzukiEulerPolePoint ω - (ω : ℂ)) / 2 + 1) /
            Complex.Gamma ((suzukiEulerPolePoint ω + (ω : ℂ)) / 2 + 1)) *
          (1 / (suzukiEulerPolePoint ω + (ω : ℂ) - 1)))) = 0 := by
    have hsub : suzukiEulerPolePoint ω + (ω : ℂ) - 1 = ((2 * ω : ℝ) : ℂ) := by
      rw [suzukiEulerPolePoint]
      push_cast
      ring
    have hne : ((2 * ω : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    rw [hsub]
    field_simp
    simp
  rwa [hval] at h

/-- The same statement for the totalized source kernel `g_ω`. -/
theorem mellin_suzukiSourceG_at_eulerPole {ω : ℝ} (hω : 0 < ω) :
    mellin (suzukiSourceG ω) (suzukiEulerPolePoint ω) = 0 := by
  have h := hasMellin_suzukiCanonicalG_at_eulerPole hω
  have hae := suzukiCanonicalG_ae_eq_sourceG ω
  rw [← h.2, mellin, mellin]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  rw [hx]

/-- **Theorem B, equation (8), convolution form.**  The once-integrated kernel also has vanishing
`(1+ω)`-moment: the extra Mellin factor `(s - 1/2)^{-1}` is finite at `s = 1 + ω`. -/
theorem hasMellin_suzukiIntegratedG_at_eulerPole {ω : ℝ} (hω : 0 < ω) :
    HasMellin (suzukiIntegratedG ω) (suzukiEulerPolePoint ω) 0 := by
  have hre : (suzukiEulerPolePoint ω).re = 1 + ω := suzukiEulerPolePoint_re ω
  have hg := hasMellin_suzukiCanonicalG_at_eulerPole hω
  have hp := hasMellin_suzukiPoleKernel (omega := (1 / 2 : ℝ))
    (s := suzukiEulerPolePoint ω) (by rw [hre]; linarith)
  have hc := hasMellin_positiveMellinConvolution
    (measurable_suzukiCanonicalG ω)
    (measurable_suzukiPoleKernel (1 / 2)) hg.1 hp.1
  rw [suzukiIntegratedG]
  refine ⟨hc.1, ?_⟩
  rw [hc.2, hg.2, zero_mul]

/-- **Theorem B, equation (8).**  Suzuki's literal once-integrated kernel `g_ω^{⟨1⟩}` has
vanishing `(1+ω)`-moment. -/
theorem mellin_suzukiSourceGOne_at_eulerPole {ω : ℝ} (hω : 0 < ω) :
    mellin (suzukiSourceGOne ω) (suzukiEulerPolePoint ω) = 0 := by
  have h := hasMellin_suzukiIntegratedG_at_eulerPole hω
  have hae := suzukiIntegratedG_ae_eq_sourceGOne ω
  rw [← h.2, mellin, mellin]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  rw [hx]

/-- **Equation (4) of the tail card, integral form.**  The `ω`-moment of the once-integrated
kernel vanishes on the positive half-line. -/
theorem integral_rpow_mul_suzukiSourceGOne_eq_zero {ω : ℝ} (hω : 0 < ω) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((ω : ℝ) : ℂ) * suzukiSourceGOne ω x = 0 := by
  have h := mellin_suzukiSourceGOne_at_eulerPole hω
  rw [mellin] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul]
  congr 2
  rw [suzukiEulerPolePoint]
  push_cast
  ring

end

end RHTower
