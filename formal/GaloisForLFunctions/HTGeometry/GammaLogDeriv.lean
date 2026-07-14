import Mathlib

/-!
# Logarithmic derivative of a scaled-shifted Gamma factor

The logarithmic derivative of `s ↦ Γ(a·s + b)` is `a · ψ(a·s + b)`, where `ψ = digamma` is the
logarithmic derivative of `Γ` (mathlib's `Complex.digamma`).  This is the per-factor building block of
the logarithmic derivative of a signed Gamma product `G(s) = e^{α s} ∏_j Γ(λ_j s + μ_j)^{m_j}`:
`G'/G = α + ∑_j m_j λ_j ψ(λ_j s + μ_j)` — the object whose shift-orbit charge governs the
differential-algebraic/hypertranscendental dichotomy of `signed-archimedean-gamma-orbit-charge-phase-law`.
-/

open Complex

namespace HTGeometry

/-- **Logarithmic derivative of a scaled-shifted Gamma factor.**  Away from the poles of `Γ` at the
non-positive integers, `logDeriv (fun s => Γ(a·s + b)) s = a · ψ(a·s + b)` (chain rule for `logDeriv`,
with `ψ = digamma = logDeriv Γ`). -/
theorem logDeriv_Gamma_affine {a b : ℂ} (s : ℂ) (hs : ∀ m : ℕ, a * s + b ≠ -m) :
    logDeriv (fun z => Complex.Gamma (a * z + b)) s = a * Complex.digamma (a * s + b) := by
  have hf : DifferentiableAt ℂ (fun z : ℂ => a * z + b) s :=
    (differentiableAt_id.const_mul a).add_const b
  have hg : DifferentiableAt ℂ Complex.Gamma (a * s + b) := Complex.differentiableAt_Gamma _ hs
  have hderiv : deriv (fun z : ℂ => a * z + b) s = a := by
    rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  rw [show (fun z => Complex.Gamma (a * z + b)) = Complex.Gamma ∘ (fun z => a * z + b) from rfl,
    logDeriv_comp (g := fun z : ℂ => a * z + b) hg hf, hderiv, Complex.digamma_def, mul_comm]

/-- **Logarithmic derivative of an integer power.**  `logDeriv (f^n) = n · logDeriv f` for `f`
differentiable and nonzero at `x` and any `n : ℤ` (chain rule through `w ↦ w^n`, whose log-derivative is
`n/w`).  Handles the Gamma *ratios* (`n < 0`) of a signed product. -/
theorem logDeriv_fun_zpow {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℂ f x) (hfx : f x ≠ 0) (n : ℤ) :
    logDeriv (fun z => f z ^ n) x = (n : ℂ) * logDeriv f x := by
  have hzpow : DifferentiableAt ℂ (fun w : ℂ => w ^ n) (f x) := differentiableAt_zpow.mpr (Or.inl hfx)
  rw [show (fun z => f z ^ n) = (fun w : ℂ => w ^ n) ∘ f from rfl,
    logDeriv_comp (g := f) hzpow hf, logDeriv_zpow, logDeriv_apply]
  ring

/-- **Logarithmic derivative of `e^{a·s}` is the slope `a`.** -/
theorem logDeriv_exp_linear (a s : ℂ) : logDeriv (fun z => Complex.exp (a * z)) s = a := by
  have hf : DifferentiableAt ℂ (fun z : ℂ => a * z) s := differentiableAt_id.const_mul a
  have hderiv : deriv (fun z : ℂ => a * z) s = a := by
    rw [deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]
  rw [show (fun z => Complex.exp (a * z)) = Complex.exp ∘ (fun z => a * z) from rfl,
    logDeriv_comp (g := fun z : ℂ => a * z) Complex.differentiableAt_exp hf, logDeriv_exp, hderiv]
  simp

/-- **Logarithmic derivative of a signed Gamma product.**  For
`G(s) = e^{α s} ∏_j Γ(λ_j s + μ_j)^{m_j}` (`m_j : ℤ`, negative allowed → Gamma ratios), off the poles,
`G'/G(s) = α + ∑_j m_j λ_j ψ(λ_j s + μ_j)`.  This is the exact carrier the shift-orbit charge analysis of
`signed-archimedean-gamma-orbit-charge-phase-law` operates on: the differential-algebraic vs.
hypertranscendental dichotomy is read off the digamma coefficients `m_j λ_j`. -/
theorem logDeriv_signedGammaProduct {d : ℕ} (α : ℂ) (lam mu : Fin d → ℂ) (m : Fin d → ℤ) (s : ℂ)
    (hpole : ∀ j, ∀ k : ℕ, lam j * s + mu j ≠ -(k : ℂ)) :
    logDeriv (fun z => Complex.exp (α * z) * ∏ j, Complex.Gamma (lam j * z + mu j) ^ m j) s
      = α + ∑ j, (m j : ℂ) * lam j * Complex.digamma (lam j * s + mu j) := by
  have hGdiff : ∀ j, DifferentiableAt ℂ (fun z => Complex.Gamma (lam j * z + mu j)) s := fun j =>
    (Complex.differentiableAt_Gamma _ (hpole j)).comp s ((differentiableAt_id.const_mul _).add_const _)
  have hGne : ∀ j, Complex.Gamma (lam j * s + mu j) ≠ 0 := fun j => Complex.Gamma_ne_zero (hpole j)
  have hfdiff : ∀ j, DifferentiableAt ℂ (fun z => Complex.Gamma (lam j * z + mu j) ^ m j) s := fun j =>
    (hGdiff j).zpow (Or.inl (hGne j))
  have hfne : ∀ j, Complex.Gamma (lam j * s + mu j) ^ m j ≠ 0 := fun j => zpow_ne_zero _ (hGne j)
  have hEdiff : DifferentiableAt ℂ (fun z => Complex.exp (α * z)) s :=
    Complex.differentiableAt_exp.comp s (differentiableAt_id.const_mul α)
  have hPdiff : DifferentiableAt ℂ (fun z => ∏ j, Complex.Gamma (lam j * z + mu j) ^ m j) s :=
    DifferentiableAt.fun_finsetProd (fun j _ => hfdiff j)
  have hPne : (∏ j, Complex.Gamma (lam j * s + mu j) ^ m j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hfne j)
  rw [logDeriv_mul (f := fun z => Complex.exp (α * z))
      (g := fun z => ∏ j, Complex.Gamma (lam j * z + mu j) ^ m j) s
      (Complex.exp_ne_zero _) hPne hEdiff hPdiff, logDeriv_exp_linear]
  congr 1
  rw [logDeriv_prod (f := fun (j : Fin d) (z : ℂ) => Complex.Gamma (lam j * z + mu j) ^ m j)
      (fun j _ => hfne j) (fun j _ => hfdiff j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [logDeriv_fun_zpow (hGdiff j) (hGne j) (m j), logDeriv_Gamma_affine s (hpole j)]
  ring

/-- **Finite integer-shift digamma recurrence.**  `ψ(w + n) = ψ(w) + ∑_{i<n} 1/(w+i)` for `n : ℕ`, off
the poles.  Iterates mathlib's single-step `digamma_apply_add_one`; the digamma *difference* across an
integer shift is thus a rational function of `w`. -/
theorem digamma_add_nat (w : ℂ) (hw : ∀ k : ℕ, w ≠ -(k : ℂ)) (n : ℕ) :
    Complex.digamma (w + n) = Complex.digamma w + ∑ i ∈ Finset.range n, (w + i)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hwn : ∀ k : ℕ, w + (n : ℂ) ≠ -(k : ℂ) := by
      intro k hk
      refine hw (k + n) ?_
      push_cast
      linear_combination hk
    have hstep : Complex.digamma (w + ((n : ℂ) + 1)) = Complex.digamma (w + n) + (w + n)⁻¹ := by
      rw [show w + ((n : ℂ) + 1) = (w + (n : ℂ)) + 1 from by ring,
        Complex.digamma_apply_add_one (w + n) hwn]
    push_cast
    rw [hstep, ih, Finset.sum_range_succ]
    ring

/-- **Charge-collapse (DA-direction witness).**  Along a single shift-orbit `w + n_j` (integer offsets
`n_j` from a common base `w = λs + μ`), if the total orbit charge `∑_j m_j` vanishes then the digamma
content collapses to a rational function: `∑_j m_j ψ(w + n_j) = ∑_j m_j ∑_{i<n_j} 1/(w+i)`, with no
transcendental `ψ(w)` term surviving.  This is the differential-algebraic direction of the
signed-archimedean orbit-charge dichotomy: zero charge ⟹ the Gamma carrier's `ψ` content is rational. -/
theorem digamma_charge_collapse {d : ℕ} (w : ℂ) (hw : ∀ k : ℕ, w ≠ -(k : ℂ)) (nn : Fin d → ℕ)
    (m : Fin d → ℂ) (hcharge : ∑ j, m j = 0) :
    ∑ j, m j * Complex.digamma (w + nn j)
      = ∑ j, m j * ∑ i ∈ Finset.range (nn j), (w + i)⁻¹ := by
  simp_rw [digamma_add_nat w hw, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hcharge,
    zero_mul, zero_add]

/-- **Gamma integer-shift is the Pochhammer factor times Gamma.**  `Γ(s + n) = (∏_{i<n}(s+i))·Γ(s)` for
`n : ℕ`, off the poles.  Iterates mathlib's single-step `Gamma_add_one`; the multiplicative companion of
`digamma_add_nat`.  In particular the canonical neutral-charge orbit ratio `Γ(s+n)/Γ(s)` is the explicit
Pochhammer polynomial `∏_{i<n}(s+i)` — the concrete differentially-algebraic carrier of the
signed-archimedean dichotomy in the integer-shift case. -/
theorem gamma_add_nat (s : ℂ) (hs : ∀ k : ℕ, s + (k : ℂ) ≠ 0) (n : ℕ) :
    Complex.Gamma (s + n) = (∏ i ∈ Finset.range n, (s + i)) * Complex.Gamma s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsn : s + (n : ℂ) ≠ 0 := hs n
    rw [show s + ((n : ℕ) + 1 : ℕ) = (s + (n : ℂ)) + 1 from by push_cast; ring,
      Complex.Gamma_add_one _ hsn, ih, Finset.prod_range_succ]
    ring

/-- **Charge-zero common-scale signed product has rational logarithmic derivative.**  For a signed Gamma
product with a *single* scale `λ` and integer-shifted parameters `μ + n_j`, if the orbit charge
`∑_j m_j` vanishes then `G'/G(s) = α + λ·∑_j m_j·∑_{i<n_j} 1/(λs + μ + i)` — a rational function of `s`
(no transcendental digamma surviving).  Combines `logDeriv_signedGammaProduct` (the carrier) with
`digamma_charge_collapse` (charge cancels the `ψ` term).  This is the penultimate step of the
differential-algebraic direction: it exhibits `G'/G` explicitly rational, which
`differentiallyAlgebraic_of_firstOrder_poly_ode` turns into differential algebraicity once cleared to a
polynomial `Q·G' = P·G` (a pole-robust step, since the `DifferentiablyAlgebraic` `∀z` quantifier meets
the Gamma-pole junk values of the meromorphic `G`). -/
theorem logDeriv_commonScale_chargeZero {d : ℕ} (α lam μ : ℂ) (nn : Fin d → ℕ) (m : Fin d → ℤ) (s : ℂ)
    (hw : ∀ k : ℕ, lam * s + μ ≠ -(k : ℂ)) (hcharge : ∑ j, (m j : ℂ) = 0) :
    logDeriv (fun z => Complex.exp (α * z)
        * ∏ j, Complex.Gamma (lam * z + (μ + nn j)) ^ m j) s
      = α + lam * ∑ j, (m j : ℂ) * ∑ i ∈ Finset.range (nn j), (lam * s + μ + i)⁻¹ := by
  have hpole : ∀ j (k : ℕ), lam * s + (μ + (nn j : ℂ)) ≠ -(k : ℂ) := by
    intro j k hk
    refine hw (k + nn j) ?_
    push_cast at hk ⊢
    linear_combination hk
  rw [logDeriv_signedGammaProduct α (fun _ => lam) (fun j => μ + nn j) m s hpole]
  congr 1
  have hcollapse := digamma_charge_collapse (lam * s + μ) hw nn (fun j => (m j : ℂ)) hcharge
  calc ∑ j, (m j : ℂ) * lam * Complex.digamma (lam * s + (μ + (nn j : ℂ)))
      = lam * ∑ j, (m j : ℂ) * Complex.digamma (lam * s + μ + (nn j : ℂ)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by rw [add_assoc]; ring)
    _ = lam * ∑ j, (m j : ℂ) * ∑ i ∈ Finset.range (nn j), (lam * s + μ + i)⁻¹ := by rw [hcollapse]

/-- **Digamma reflection formula.**  `ψ(1-s) - ψ(s) = π·cot(πs)` (with `cot = cos/sin`), for `s ∉ ℤ`.
The logarithmic-derivative form of Euler's Gamma reflection `Γ(s)·Γ(1-s) = π/sin(πs)`: taking `logDeriv`
of both sides gives `ψ(s) - ψ(1-s)` on the left and `-π·cot(πs)` on the right.  This is the trigonometric
carrier that a *reflected* (negative-slope) Gamma factor introduces — the boundary between the
differentially-algebraic same-slope regime and the transcendental reflected regime of
`signed-archimedean-gamma-orbit-charge-phase-law`. -/
theorem digamma_reflection (s : ℂ) (hs : ∀ k : ℤ, s ≠ (k : ℂ)) :
    Complex.digamma (1 - s) - Complex.digamma s
      = (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * s) / Complex.sin ((Real.pi : ℂ) * s)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓs : ∀ m : ℕ, s ≠ -(m : ℂ) := fun m => by
    have := hs (-(m : ℤ)); push_cast at this; exact this
  have hΓ1s : ∀ m : ℕ, (1 - s) ≠ -(m : ℂ) := fun m => by
    have := hs (1 + (m : ℤ)); push_cast at this ⊢; intro h; apply this; linear_combination -h
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]; intro k h
    exact hs k (mul_left_cancel₀ hπ (by rw [h]; ring))
  have hΓsne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hΓs
  have hΓ1sne : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hΓ1s
  have hΓsd : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma _ hΓs
  have hshiftd : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
    (differentiableAt_const 1).sub differentiableAt_id
  have hΓ1sd : DifferentiableAt ℂ (fun z => Complex.Gamma (1 - z)) s :=
    (Complex.differentiableAt_Gamma _ hΓ1s).comp s hshiftd
  have hL : logDeriv (fun z => Complex.Gamma z * Complex.Gamma (1 - z)) s
      = Complex.digamma s - Complex.digamma (1 - s) := by
    rw [logDeriv_mul s hΓsne hΓ1sne hΓsd hΓ1sd]
    have hcomp : logDeriv (fun z => Complex.Gamma (1 - z)) s = -Complex.digamma (1 - s) := by
      rw [show (fun z => Complex.Gamma (1 - z)) = Complex.Gamma ∘ (fun z => 1 - z) from rfl,
        logDeriv_comp (g := fun z => 1 - z) (Complex.differentiableAt_Gamma _ hΓ1s) hshiftd,
        ← Complex.digamma_def, show deriv (fun z : ℂ => 1 - z) s = -1 from by simp]
      ring
    rw [hcomp, Complex.digamma_def]; ring
  have hsind : DifferentiableAt ℂ (fun z => Complex.sin ((Real.pi : ℂ) * z)) s :=
    Complex.differentiableAt_sin.comp s (differentiableAt_id.const_mul _)
  have hlogsin : logDeriv (fun z => Complex.sin ((Real.pi : ℂ) * z)) s
      = Complex.cos ((Real.pi : ℂ) * s) / Complex.sin ((Real.pi : ℂ) * s) * (Real.pi : ℂ) := by
    rw [show (fun z => Complex.sin ((Real.pi : ℂ) * z))
          = Complex.sin ∘ (fun z => (Real.pi : ℂ) * z) from rfl,
      logDeriv_comp (g := fun z => (Real.pi : ℂ) * z) Complex.differentiableAt_sin
        (differentiableAt_id.const_mul _), logDeriv_apply, Complex.deriv_sin,
      show deriv (fun z => (Real.pi : ℂ) * z) s = (Real.pi : ℂ) from by
        rw [deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]]
  have hR : logDeriv (fun z => Complex.Gamma z * Complex.Gamma (1 - z)) s
      = -((Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * s) / Complex.sin ((Real.pi : ℂ) * s))) := by
    rw [show (fun z => Complex.Gamma z * Complex.Gamma (1 - z))
          = fun z => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) from
        funext (fun z => Complex.Gamma_mul_Gamma_one_sub z),
      show (fun z => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z))
          = fun z => (Real.pi : ℂ) * (Complex.sin ((Real.pi : ℂ) * z))⁻¹ from
        funext (fun z => div_eq_mul_inv _ _),
      logDeriv_const_mul s (Real.pi : ℂ) hπ,
      show (fun z => (Complex.sin ((Real.pi : ℂ) * z))⁻¹)
          = fun z => (Complex.sin ((Real.pi : ℂ) * z)) ^ (-1 : ℤ) from
        funext (fun z => (zpow_neg_one _).symm),
      logDeriv_fun_zpow hsind hsin (-1), hlogsin]
    push_cast; ring
  have hkey := hL.symm.trans hR
  linear_combination -hkey

/-- **Logarithmic derivative of the base-2 power `2^{1-2z}`.**  `logDeriv (z ↦ 2^{1-2z}) s = -2·log 2`
(via `2^w = exp(log 2 · w)` and the chain rule).  The elementary carrier of Legendre's duplication
formula's power factor. -/
theorem logDeriv_two_cpow_linear (s : ℂ) :
    logDeriv (fun z => (2 : ℂ) ^ (1 - 2 * z)) s = -2 * Complex.log 2 := by
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [show (fun z => (2 : ℂ) ^ (1 - 2 * z))
        = fun z => Complex.exp (Complex.log 2 * (1 - 2 * z)) from
      funext (fun z => Complex.cpow_def_of_ne_zero h2 _)]
  have hd : HasDerivAt (fun z : ℂ => Complex.log 2 * (1 - 2 * z)) (Complex.log 2 * (-2)) s := by
    have h1 : HasDerivAt (fun z : ℂ => 1 - 2 * z) (-2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).const_sub 1
    simpa using h1.const_mul (Complex.log 2)
  rw [show (fun z => Complex.exp (Complex.log 2 * (1 - 2 * z)))
        = Complex.exp ∘ (fun z => Complex.log 2 * (1 - 2 * z)) from rfl,
    logDeriv_comp (g := fun z => Complex.log 2 * (1 - 2 * z)) Complex.differentiableAt_exp
      hd.differentiableAt, logDeriv_exp]
  simp only [Pi.one_apply, one_mul, hd.deriv]
  ring

/-- **Digamma duplication (Gauss/Legendre) formula.**  `2·ψ(2s) = ψ(s) + ψ(s+½) + 2·log 2`, for `2s`
not a non-positive integer.  The logarithmic-derivative form of Legendre's Gamma duplication
`Γ(s)·Γ(s+½) = Γ(2s)·2^{1-2s}·√π`: `logDeriv` of the left gives `ψ(s) + ψ(s+½)`, of the right gives
`2·ψ(2s) - 2·log 2` (the `2^{1-2s}` factor contributes `-2·log 2` via `logDeriv_two_cpow_linear`).  The
third classical Gamma functional-equation carrier, completing recurrence (`digamma_add_nat`) and
reflection (`digamma_reflection`). -/
theorem digamma_duplication (s : ℂ) (hcond : ∀ n : ℕ, 2 * s ≠ -(n : ℂ)) :
    2 * Complex.digamma (2 * s)
      = Complex.digamma s + Complex.digamma (s + 1 / 2) + 2 * Complex.log 2 := by
  have hΓ2s : ∀ m : ℕ, 2 * s ≠ -(m : ℂ) := hcond
  have hΓs : ∀ m : ℕ, s ≠ -(m : ℂ) := fun m h => hcond (2 * m) (by push_cast; linear_combination 2 * h)
  have hΓsh : ∀ m : ℕ, s + 1 / 2 ≠ -(m : ℂ) := fun m h =>
    hcond (2 * m + 1) (by push_cast; linear_combination 2 * h)
  have hΓsne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hΓs
  have hΓshne : Complex.Gamma (s + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero hΓsh
  have hΓ2sne : Complex.Gamma (2 * s) ≠ 0 := Complex.Gamma_ne_zero hΓ2s
  have hcpowne : (2 : ℂ) ^ (1 - 2 * s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero two_ne_zero]; exact Complex.exp_ne_zero _
  have hsqrtπ : (↑(Real.sqrt Real.pi) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hΓsd : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma _ hΓs
  have hΓshd : DifferentiableAt ℂ (fun z => Complex.Gamma (z + 1 / 2)) s :=
    (Complex.differentiableAt_Gamma _ hΓsh).comp s (differentiableAt_id.add_const _)
  have hΓ2sd : DifferentiableAt ℂ (fun z => Complex.Gamma (2 * z)) s :=
    (Complex.differentiableAt_Gamma _ hΓ2s).comp s (differentiableAt_id.const_mul _)
  have hcpowd : DifferentiableAt ℂ (fun z => (2 : ℂ) ^ (1 - 2 * z)) s := by
    rw [show (fun z => (2 : ℂ) ^ (1 - 2 * z)) = fun z => Complex.exp (Complex.log 2 * (1 - 2 * z)) from
      funext (fun z => Complex.cpow_def_of_ne_zero two_ne_zero _)]
    fun_prop
  have hL : logDeriv (fun z => Complex.Gamma z * Complex.Gamma (z + 1 / 2)) s
      = Complex.digamma s + Complex.digamma (s + 1 / 2) := by
    rw [logDeriv_mul s hΓsne hΓshne hΓsd hΓshd]
    have hc : logDeriv (fun z => Complex.Gamma (z + 1 / 2)) s = Complex.digamma (s + 1 / 2) := by
      rw [show (fun z => Complex.Gamma (z + 1 / 2)) = Complex.Gamma ∘ (fun z => z + 1 / 2) from rfl,
        logDeriv_comp (g := fun z => z + 1 / 2) (Complex.differentiableAt_Gamma _ hΓsh)
          (differentiableAt_id.add_const _), ← Complex.digamma_def,
        show deriv (fun z : ℂ => z + 1 / 2) s = 1 from by simp]
      ring
    rw [hc, Complex.digamma_def]
  have hR : logDeriv (fun z => Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z)
        * (↑(Real.sqrt Real.pi) : ℂ)) s
      = 2 * Complex.digamma (2 * s) - 2 * Complex.log 2 := by
    rw [show (fun z => Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * (↑(Real.sqrt Real.pi) : ℂ))
          = fun z => (↑(Real.sqrt Real.pi) : ℂ) * (Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z)) from
        funext (fun z => by ring),
      logDeriv_const_mul s (↑(Real.sqrt Real.pi) : ℂ) hsqrtπ,
      logDeriv_mul s hΓ2sne hcpowne hΓ2sd hcpowd, logDeriv_two_cpow_linear]
    have hc2 : logDeriv (fun z => Complex.Gamma (2 * z)) s = 2 * Complex.digamma (2 * s) := by
      rw [show (fun z => Complex.Gamma (2 * z)) = Complex.Gamma ∘ (fun z => 2 * z) from rfl,
        logDeriv_comp (g := fun z => 2 * z) (Complex.differentiableAt_Gamma _ hΓ2s)
          (differentiableAt_id.const_mul _), ← Complex.digamma_def,
        show deriv (fun z : ℂ => 2 * z) s = 2 from by simp]
      ring
    rw [hc2]; ring
  have hfeq : (fun z => Complex.Gamma z * Complex.Gamma (z + 1 / 2))
      = fun z => Complex.Gamma (2 * z) * (2 : ℂ) ^ (1 - 2 * z) * (↑(Real.sqrt Real.pi) : ℂ) :=
    funext (fun z => Complex.Gamma_mul_Gamma_add_half z)
  have hkey : Complex.digamma s + Complex.digamma (s + 1 / 2)
      = 2 * Complex.digamma (2 * s) - 2 * Complex.log 2 := by rw [← hL, hfeq]; exact hR
  linear_combination -hkey

/-- **First-order difference equation of a signed Gamma product.**  For the unit-scale product
`G(s) = ∏_j Γ(s + μ_j)^{m_j}` (`m_j : ℤ`), the shift satisfies `G(s+1) = R(s)·G(s)` with rational
coefficient `R(s) = ∏_j (s + μ_j)^{m_j}` (off the poles `s + μ_j = 0`), by the Gamma recurrence
`Γ(w+1) = w·Γ(w)` applied factorwise.  This is the difference-equation structure on which the
Adamczewski–Dreyfus–Hardouin dichotomy operates: the whole hypertranscendence classification of the
signed-archimedean orbit-charge law reads the shift ratio `R` — its ℤ-orbit charges decide whether `R`
telescopes (`R = g(s+1)/g(s)`, `g` rational ⟹ `G` differentially algebraic) or not (⟹ hypertranscendental).
The multiplicative companion of `logDeriv_signedGammaProduct`. -/
theorem signedGammaProduct_shift {d : ℕ} (μ : Fin d → ℂ) (m : Fin d → ℤ) (s : ℂ)
    (hs : ∀ j, s + μ j ≠ 0) :
    (∏ j, Complex.Gamma (s + 1 + μ j) ^ m j)
      = (∏ j, (s + μ j) ^ m j) * ∏ j, Complex.Gamma (s + μ j) ^ m j := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [show s + 1 + μ j = (s + μ j) + 1 from by ring, Complex.Gamma_add_one _ (hs j), mul_zpow]

/-- **Charge-zero integer-shift signed Gamma product is rational.**  The constructive
differential-algebraic witness (the telescoping half of the ADH dichotomy): if the total orbit charge
`∑_j m_j` vanishes, then `∏_j Γ(s + n_j)^{m_j} = ∏_j (∏_{i<n_j}(s+i))^{m_j}` — a ratio of Pochhammer
polynomials, hence a rational function of `s`, with all Gamma content cancelling.  Uses `gamma_add_nat`
(`Γ(s+n) = Pochhammer·Γ(s)`) factorwise: the `Γ(s)^{m_j}` factors collect to `Γ(s)^{∑ m_j} = Γ(s)^0 = 1`.
A rational function is differentially algebraic, so this exhibits the charge-zero product as DA — no
difference-Galois machinery needed for this direction. -/
theorem signedGammaProduct_chargeZero_rational {d : ℕ} (nn : Fin d → ℕ) (m : Fin d → ℤ) (s : ℂ)
    (hs : ∀ k : ℕ, s + (k : ℂ) ≠ 0) (hcharge : ∑ j, m j = 0) :
    (∏ j, Complex.Gamma (s + nn j) ^ m j)
      = ∏ j, (∏ i ∈ Finset.range (nn j), (s + i)) ^ m j := by
  have hΓpole : ∀ m : ℕ, s ≠ -(m : ℂ) := fun m h => hs m (by rw [h]; ring)
  have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hΓpole
  have hpz : ∀ t : Finset (Fin d), (∏ j ∈ t, Complex.Gamma s ^ m j)
      = Complex.Gamma s ^ (∑ j ∈ t, m j) := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | @insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hΓne]
  simp_rw [gamma_add_nat s hs, mul_zpow]
  rw [Finset.prod_mul_distrib, hpz Finset.univ, hcharge, zpow_zero, mul_one]

/-- **Charge-zero shift ratio telescopes.**  The explicit telescoping witness: for a charge-zero
integer-shift orbit, the rational shift coefficient `R(s) = ∏_j (s+n_j)^{m_j}` is `g(s+1)/g(s)` with
`g(s) = ∏_j (∏_{i<n_j}(s+i))^{m_j}` the Pochhammer-ratio rational carrier — i.e. `R(s)·g(s) = g(s+1)`.
This is the constructive telescoping half of the ADH dichotomy in shift form: charge `0` makes the
difference equation `G(s+1) = R(s)·G(s)` solvable in the rational function field, forcing `G` differentially
algebraic.  Chained from `signedGammaProduct_chargeZero_rational` (at `s` and `s+1`) and
`signedGammaProduct_shift`. -/
theorem signedGammaProduct_chargeZero_telescopes {d : ℕ} (nn : Fin d → ℕ) (m : Fin d → ℤ) (s : ℂ)
    (hs : ∀ k : ℕ, s + (k : ℂ) ≠ 0) (hcharge : ∑ j, m j = 0) :
    (∏ j, (∏ i ∈ Finset.range (nn j), (s + 1 + i)) ^ m j)
      = (∏ j, (s + nn j) ^ m j) * ∏ j, (∏ i ∈ Finset.range (nn j), (s + i)) ^ m j := by
  have hs1 : ∀ k : ℕ, (s + 1) + (k : ℂ) ≠ 0 := fun k => by
    have h := hs (k + 1); intro hh; apply h; push_cast at hh ⊢; linear_combination hh
  have hG := signedGammaProduct_chargeZero_rational nn m s hs hcharge
  have hG1 := signedGammaProduct_chargeZero_rational nn m (s + 1) hs1 hcharge
  have hshift := signedGammaProduct_shift (fun j => (nn j : ℂ)) m s (fun j => hs (nn j))
  rw [← hG1, ← hG, ← hshift]

end HTGeometry
