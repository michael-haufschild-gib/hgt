import GaloisForLFunctions.RHTower.ArchimedeanGamma
import GaloisForLFunctions.HTGeometry.LerchHurwitzDerivative

/-!
# The archimedean Euler factor as a rank-one difference-differential module

`Γ_ℝ(s) = π^{-s/2} Γ(s/2)` generates a rank-one module over the base carrying the shift
`σ_∞ : s ↦ s + 2` and the derivation `∂_s`:

* the **difference structure** is the degree-one polynomial multiplier `Γ_ℝ(s+2) = (s/2π)Γ_ℝ(s)`;
* the **differential structure** is the connection coefficient
  `∂_s log Γ_ℝ = −½ log π + ½ ψ(s/2)`;
* the multiplier is **not** constant — `∂_s log (s/2π) = 1/s ≠ 0` — which is what separates the
  archimedean place from the finite places, whose multipliers `p^{-1}` are constant.

Tensoring with the rank-one zeta module produces the completed module whose diagonal section is
`Λ(s) = Γ_ℝ(s)ζ(s)`, on which the functional equation `Λ(s) = Λ(1−s)` acts.
-/

open Complex Set

namespace GaloisForLFunctions

noncomputable section

/-! ## Real part of the halved argument -/

theorem half_re (s : ℂ) : (s / 2).re = s.re / 2 := Complex.div_ofNat_re s 2

theorem half_ne_negNat {s : ℂ} (hs : 0 < s.re) (m : ℕ) : s / 2 ≠ -(m : ℂ) := by
  intro h
  have hre : (s / 2).re = (-(m : ℂ)).re := by rw [h]
  rw [half_re] at hre
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-! ## Differentiability and nonvanishing of the archimedean factor -/

theorem differentiableAt_piCpow (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => ((Real.pi : ℝ) : ℂ) ^ (-z / 2)) s := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact DifferentiableAt.const_cpow (by fun_prop) (Or.inl hpi)

theorem hasDerivAt_piCpow (s : ℂ) :
    HasDerivAt (fun z : ℂ => ((Real.pi : ℝ) : ℂ) ^ (-z / 2))
      (((Real.pi : ℝ) : ℂ) ^ (-s / 2) * Complex.log ((Real.pi : ℝ) : ℂ) * (-(1 : ℂ) / 2)) s := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : HasDerivAt (fun z : ℂ => -z) (-1 : ℂ) s := (hasDerivAt_id s).neg
  have hb : HasDerivAt (fun z : ℂ => -z / 2) (-(1 : ℂ) / 2) s := h1.div_const 2
  exact hb.const_cpow (Or.inl hpi)

theorem differentiableAt_gammaHalf {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
  have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ (half_ne_negNat hs)
  have hin : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
  exact hΓ.comp s hin

theorem Gammaℝ_eq_fun :
    Complex.Gammaℝ = fun z : ℂ => ((Real.pi : ℝ) : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) :=
  funext Complex.Gammaℝ_def

theorem differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  rw [Gammaℝ_eq_fun]
  exact (differentiableAt_piCpow s).mul (differentiableAt_gammaHalf hs)

/-! ## The connection coefficient -/

/-- **The archimedean connection.**  `∂_s log Γ_ℝ(s) = −½ log π + ½ ψ(s/2)`. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = gammaRealLogConnection s := by
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero (half_ne_negNat hs)
  have hpine : ((Real.pi : ℝ) : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpi]
    exact Complex.exp_ne_zero _
  have h1 : logDeriv (fun z : ℂ => ((Real.pi : ℝ) : ℂ) ^ (-z / 2)) s
      = -(Complex.log ((Real.pi : ℝ) : ℂ)) / 2 := by
    rw [logDeriv_apply, (hasDerivAt_piCpow s).deriv]
    field_simp
  have h2 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s = Complex.digamma (s / 2) / 2 := by
    have hcomp : (fun z : ℂ => Complex.Gamma (z / 2)) = Complex.Gamma ∘ fun z : ℂ => z / 2 := rfl
    have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
    have hlc := logDeriv_comp (f := Complex.Gamma) (g := fun z : ℂ => z / 2) (x := s)
      (Complex.differentiableAt_Gamma _ (half_ne_negNat hs)) hdiv
    rw [hcomp, hlc, ← Complex.digamma_def]
    have hd : deriv (fun z : ℂ => z / 2) s = 1 / 2 := by
      simp
    rw [hd]
    ring
  rw [Gammaℝ_eq_fun, logDeriv_mul s hpine hΓne (differentiableAt_piCpow s)
    (differentiableAt_gammaHalf hs), h1, h2, gammaRealLogConnection,
    Complex.ofReal_log Real.pi_pos.le]
  ring

/-! ## Nonvanishing -/

theorem Gammaℝ_ne_zero {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℝ s ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos hs

/-! ## Rank-one difference-differential data -/

/-- A rank-one difference-differential module: a nonvanishing differentiable generator on a
shift-stable domain, with shift multiplier `mult` and connection coefficient `conn`. -/
structure RankOneShiftDiffDatum where
  /-- The generator of the rank-one module. -/
  gen : ℂ → ℂ
  /-- The shift acting on the base. -/
  shift : ℂ → ℂ
  /-- The shift multiplier: `gen (shift s) = mult s * gen s`. -/
  mult : ℂ → ℂ
  /-- The connection coefficient: `logDeriv gen = conn`. -/
  conn : ℂ → ℂ
  /-- The region on which the datum is defined. -/
  domain : Set ℂ
  shift_stable : ∀ s ∈ domain, shift s ∈ domain
  gen_ne_zero : ∀ s ∈ domain, gen s ≠ 0
  gen_differentiableAt : ∀ s ∈ domain, DifferentiableAt ℂ gen s
  gen_shift : ∀ s ∈ domain, gen (shift s) = mult s * gen s
  gen_conn : ∀ s ∈ domain, logDeriv gen s = conn s

/-- **Tensor product of rank-one data.**  Multipliers multiply and connections add; the diagonal
section of the tensor is the product of the generators. -/
def RankOneShiftDiffDatum.tensor (M N : RankOneShiftDiffDatum) (hsh : M.shift = N.shift) :
    RankOneShiftDiffDatum where
  gen := fun s => M.gen s * N.gen s
  shift := M.shift
  mult := fun s => M.mult s * N.mult s
  conn := fun s => M.conn s + N.conn s
  domain := M.domain ∩ N.domain
  shift_stable := fun s hs =>
    ⟨M.shift_stable s hs.1, by
      have := N.shift_stable s hs.2
      rwa [← hsh] at this⟩
  gen_ne_zero := fun s hs => mul_ne_zero (M.gen_ne_zero s hs.1) (N.gen_ne_zero s hs.2)
  gen_differentiableAt := fun s hs =>
    (M.gen_differentiableAt s hs.1).mul (N.gen_differentiableAt s hs.2)
  gen_shift := fun s hs => by
    have hM := M.gen_shift s hs.1
    have hN := N.gen_shift s hs.2
    rw [← hsh] at hN
    rw [hM, hN]
    ring
  gen_conn := fun s hs => by
    rw [logDeriv_mul s (M.gen_ne_zero s hs.1) (N.gen_ne_zero s hs.2)
      (M.gen_differentiableAt s hs.1) (N.gen_differentiableAt s hs.2),
      M.gen_conn s hs.1, N.gen_conn s hs.2]

/-! ## `M_∞`: the archimedean module -/

/-- **`M_∞`.**  The archimedean Euler factor `Γ_ℝ` as a rank-one `(σ_∞, ∂_s)`-module with the
degree-one polynomial multiplier `s/2π` and the digamma connection. -/
def archimedeanGammaModule : RankOneShiftDiffDatum where
  gen := Complex.Gammaℝ
  shift := fun s => s + 2
  mult := fun s => s / (2 * ((Real.pi : ℝ) : ℂ))
  conn := gammaRealLogConnection
  domain := {s : ℂ | 0 < s.re}
  shift_stable := fun s hs => by
    have hre : (0 : ℝ) < s.re := hs
    have : (s + 2).re = s.re + 2 := by simp
    show (0 : ℝ) < (s + 2).re
    rw [this]
    linarith
  gen_ne_zero := fun s hs => Gammaℝ_ne_zero hs
  gen_differentiableAt := fun s hs => differentiableAt_Gammaℝ hs
  gen_shift := fun s hs => by
    have hre : (0 : ℝ) < s.re := hs
    have hne : s ≠ 0 := by
      intro h
      rw [h] at hre
      simp at hre
    exact gammaReal_shift_two hne
  gen_conn := fun s hs => logDeriv_Gammaℝ hs

/-! ## `M_ζ` and the completed module `M_Λ` -/

/-- **`M_ζ`.**  The zeta module on the Euler-product half-plane. -/
def zetaModule : RankOneShiftDiffDatum where
  gen := riemannZeta
  shift := fun s => s + 2
  mult := fun s => riemannZeta (s + 2) / riemannZeta s
  conn := logDeriv riemannZeta
  domain := {s : ℂ | 1 < s.re}
  shift_stable := fun s hs => by
    have hre : (1 : ℝ) < s.re := hs
    have h2 : (s + 2).re = s.re + 2 := by simp
    show (1 : ℝ) < (s + 2).re
    rw [h2]
    linarith
  gen_ne_zero := fun s hs => riemannZeta_ne_zero_of_one_lt_re hs
  gen_differentiableAt := fun s hs => by
    refine differentiableAt_riemannZeta ?_
    intro h
    have hre : (1 : ℝ) < s.re := hs
    rw [h] at hre
    simp at hre
  gen_shift := fun s hs => by
    have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    field_simp
  gen_conn := fun _ _ => rfl

/-- **`M_Λ = M_∞ ⊗ M_ζ`.**  The completed constraint module. -/
def completedZetaModule : RankOneShiftDiffDatum :=
  archimedeanGammaModule.tensor zetaModule rfl

/-- **The diagonal section of `M_Λ` is the completed zeta function.** -/
theorem completedZetaModule_gen_eq {s : ℂ} (hs : s ∈ completedZetaModule.domain) :
    completedZetaModule.gen s = completedRiemannZeta s := by
  have hre : (0 : ℝ) < s.re := hs.1
  have hne : s ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
  have hg : Complex.Gammaℝ s ≠ 0 := Gammaℝ_ne_zero hre
  show Complex.Gammaℝ s * riemannZeta s = completedRiemannZeta s
  rw [riemannZeta_def_of_ne_zero hne]
  field_simp

/-- The multiplier of the completed module is the product of the two place multipliers. -/
theorem completedZetaModule_mult (s : ℂ) :
    completedZetaModule.mult s
      = (s / (2 * ((Real.pi : ℝ) : ℂ))) * (riemannZeta (s + 2) / riemannZeta s) := rfl

/-- The connection of the completed module is the sum of the two place connections. -/
theorem completedZetaModule_conn (s : ℂ) :
    completedZetaModule.conn s = gammaRealLogConnection s + logDeriv riemannZeta s := rfl

/-- The domain of the completed module is the Euler-product half-plane. -/
theorem completedZetaModule_domain :
    completedZetaModule.domain = {s : ℂ | 0 < s.re} ∩ {s : ℂ | 1 < s.re} := rfl

/-- **The functional equation acts on `M_Λ`.** -/
theorem completedZetaModule_functional_equation (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-! ## The multiplier dichotomy -/

/-- The archimedean multiplier is the evaluation of a degree-one polynomial. -/
theorem archimedeanGammaModule_mult_polynomial :
    archimedeanGammaModule.mult
      = fun s => Polynomial.eval s
          (Polynomial.C (2 * ((Real.pi : ℝ) : ℂ))⁻¹ * Polynomial.X) := by
  funext s
  simp [archimedeanGammaModule, div_eq_mul_inv, mul_comm]

theorem archimedeanGammaModule_mult_natDegree :
    (Polynomial.C (2 * ((Real.pi : ℝ) : ℂ))⁻¹ * Polynomial.X).natDegree = 1 := by
  have hne : (2 * ((Real.pi : ℝ) : ℂ))⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [Polynomial.natDegree_C_mul hne, Polynomial.natDegree_X]

/-- **The archimedean multiplier is non-CC**: its logarithmic derivative is `1/s ≠ 0`. -/
theorem logDeriv_archimedeanGammaModule_mult {s : ℂ} (hs : s ≠ 0) :
    logDeriv archimedeanGammaModule.mult s = 1 / s := by
  have hpi : (2 * ((Real.pi : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfun : archimedeanGammaModule.mult = fun z : ℂ => z / (2 * ((Real.pi : ℝ) : ℂ)) := rfl
  rw [hfun, logDeriv_apply]
  have hd : deriv (fun z : ℂ => z / (2 * ((Real.pi : ℝ) : ℂ))) s
      = 1 / (2 * ((Real.pi : ℝ) : ℂ)) := by
    simp
  rw [hd]
  field_simp

/-- A constant multiplier — the finite-place case `p^{-s}`-free normalization — has vanishing
logarithmic derivative. -/
theorem logDeriv_const (c : ℂ) (s : ℂ) : logDeriv (fun _ : ℂ => c) s = 0 := by
  rw [logDeriv_apply, deriv_const]
  simp

/-- **The multiplier dichotomy.**  The archimedean multiplier is not constant. -/
theorem archimedeanGammaModule_mult_not_const :
    ¬ ∃ c : ℂ, archimedeanGammaModule.mult = fun _ : ℂ => c := by
  rintro ⟨c, hc⟩
  have h1 : logDeriv archimedeanGammaModule.mult 1 = 1 / 1 :=
    logDeriv_archimedeanGammaModule_mult one_ne_zero
  rw [hc, logDeriv_const] at h1
  norm_num at h1

/-! ## The generator as an inverse regularized determinant -/

/-- **`M_∞` is the object whose inverse ζ-regularized determinant is the archimedean Euler
factor.**  `Γ_ℝ(s)·det_ζ(N + s/2) = π^{-s/2}√(2π)`. -/
theorem archimedeanGammaModule_gen_mul_zetaRegDet {s : ℝ} (hs : 0 < s) :
    archimedeanGammaModule.gen ((s : ℝ) : ℂ) * ((HTGeometry.zetaRegDet (s / 2) : ℝ) : ℂ)
      = ((Real.pi : ℝ) : ℂ) ^ (-((s : ℝ) : ℂ) / 2) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) :=
  HTGeometry.Gammaℝ_mul_zetaRegDet hs

/-- The spectral zeta function of `N + a` really is the convergent spectral series where it
converges. -/
theorem archimedeanSpectralZeta_eq_tsum {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 1 < w.re) :
    HTGeometry.hurwitzZetaEM a w = ∑' n : ℕ, (((n : ℝ) + a : ℝ) : ℂ) ^ (-w) :=
  HTGeometry.hurwitzZetaEM_eq_tsum ha hw

/-- **Lerch's formula** in the form used by the archimedean module. -/
theorem archimedeanSpectralZeta_deriv_zero {a : ℝ} (ha : 0 < a) :
    deriv (HTGeometry.hurwitzZetaEM a) 0
      = ((Real.log (Real.Gamma a) - Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) :=
  HTGeometry.deriv_hurwitzZetaEM_zero ha

end

end GaloisForLFunctions
