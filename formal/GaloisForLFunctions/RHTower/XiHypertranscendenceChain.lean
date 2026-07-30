import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.XiLogDerivNotHolonomic
import GaloisForLFunctions.HTGeometry.WatsonFlatnessDischarge

/-!
# The hypertranscendence chain for the completed ξ

The route from Hölder's theorem to the hypertranscendence of `ξ` runs through the
logarithmic-derivative weld: on the half-plane of absolute convergence,

`ξ'/ξ = 1/s + 1/(s-1) − (log π)/2 + ½·ψ(s/2) + ζ'/ζ`

(`xiLogDeriv_split`), so a differential-algebraic relation for `ξ` mixes the rational leg,
the half-argument digamma jets, and the prime-log Dirichlet jets of `ζ'/ζ`.  Collapsing the
Dirichlet frequencies (grouping the relation by frequency and applying the
minimal-frequency estimate and the prime-power Vandermonde extraction) produces a nonzero
half-argument digamma jet polynomial that is exponentially small on the real ray — the
object that quantitative Hölder (`QuantitativeHolder`) kills.

* `xi_eq_weld`, `xiLogDeriv_split`, `xiLogDeriv_eventuallyEq_split` — the weld identity and
  its logarithmic derivative, unconditional.
* `XiFrequencyCollapse` — the named Dirichlet-side input: a nonzero jet annihilator of `ξ`
  yields a nonzero exponentially small half-argument digamma jet polynomial.
* `xi_hypertranscendental_of_quantitativeHolder`,
  `xi_hypertranscendental_of_watsonFlatness` — **the chain theorems**: QH (or its
  Watson-flatness reduction, whose vanishing side is the machine-checked Hölder theorem)
  together with the frequency collapse forces `Hypertranscendental xi`.
-/

noncomputable section

namespace RHTower

open Complex Filter GaloisForLFunctions

/-! ## The weld identity and its logarithmic derivative -/

theorem xi_eq_weld {s : ℂ} (hs : 1 < s.re) :
    xi s = s * (s - 1) / 2 * (Gammaℝ s * riemannZeta s) := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have h1 : s ≠ 1 := fun h => by simp [h] at hs
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [xi_eq_half_mul h0 h1, riemannZeta_def_of_ne_zero h0]
  field_simp

/-- **The logarithmic-derivative weld**: on the half-plane of absolute convergence,
`ξ'/ξ = 1/s + 1/(s−1) − (log π)/2 + ½·ψ(s/2) + ζ'/ζ`. -/
theorem xiLogDeriv_split {s : ℂ} (hs : 1 < s.re) :
    xiLogDeriv s = 1 / s + 1 / (s - 1) - (Real.log Real.pi) / 2
      + (1 / 2) * Complex.digamma (s / 2) + zetaLogDeriv s := by
  have h0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  have h1 : s ≠ 1 := fun h => by simp [h] at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hΓpoles : ∀ p : ℕ, s / 2 ≠ -(p : ℂ) := by
    intro p hEq
    have hre := congrArg Complex.re hEq
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hΓpoles
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hF : s * (s - 1) / 2 ≠ 0 := by
    apply div_ne_zero (mul_ne_zero h0 hs1)
    norm_num
  -- the three legs are differentiable
  have hπC : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hdF : HasDerivAt (fun w : ℂ => w * (w - 1) / 2) ((s - 1 + s) / 2) s := by
    have := ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
    simpa [mul_one, one_mul] using this
  have hdπ : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have hlin : HasDerivAt (fun w : ℂ => -w / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    exact hlin.const_cpow (Or.inl hπC)
  have hdΓhalf : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
    have hg : HasDerivAt Complex.Gamma (deriv Complex.Gamma (s / 2)) (s / 2) :=
      ((analyticAt_Gamma (s / 2) hΓpoles).differentiableAt).hasDerivAt
    have hf : HasDerivAt (fun w : ℂ => w / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    simpa using! hg.comp s hf
  have hdΓℝ : HasDerivAt Gammaℝ
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)
          * Complex.Gamma (s / 2)
        + (Real.pi : ℂ) ^ (-s / 2) * (deriv Complex.Gamma (s / 2) * (1 / 2))) s := by
    have h := hdπ.mul hdΓhalf
    have hfun : ((fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) * fun w : ℂ =>
        Complex.Gamma (w / 2)) = Gammaℝ := by
      funext w
      rw [Pi.mul_apply, Gammaℝ_def]
    rwa [hfun] at h
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta h1
  -- rewrite `xi` as the product near `s`
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : xi =ᶠ[nhds s] fun w => w * (w - 1) / 2 * (Gammaℝ w * riemannZeta w) := by
    filter_upwards [hopen.mem_nhds hs] with w hw
    exact xi_eq_weld hw
  have hderiv_eq : deriv xi s
      = deriv (fun w => w * (w - 1) / 2 * (Gammaℝ w * riemannZeta w)) s :=
    hev.deriv_eq
  have hval : xi s = s * (s - 1) / 2 * (Gammaℝ s * riemannZeta s) := xi_eq_weld hs
  -- split the logarithmic derivative of the triple product
  have hlog : xiLogDeriv s
      = logDeriv (fun w => w * (w - 1) / 2 * (Gammaℝ w * riemannZeta w)) s := by
    rw [xiLogDeriv, logDeriv_apply, ← hderiv_eq, ← hval]
  rw [hlog, logDeriv_mul (f := fun w : ℂ => w * (w - 1) / 2)
      (g := fun w => Gammaℝ w * riemannZeta w) s hF (mul_ne_zero hΓℝ hζ)
      hdF.differentiableAt ((hdΓℝ.differentiableAt).mul hdζ),
    logDeriv_mul (f := Gammaℝ) (g := riemannZeta) s hΓℝ hζ
      hdΓℝ.differentiableAt hdζ]
  -- the rational leg
  have hlegF : logDeriv (fun w : ℂ => w * (w - 1) / 2) s = 1 / s + 1 / (s - 1) := by
    rw [logDeriv_apply, hdF.deriv]
    field_simp
  -- the archimedean leg
  have hlegΓ : logDeriv Gammaℝ s
      = -(Real.log Real.pi) / 2 + (1 / 2) * Complex.digamma (s / 2) := by
    rw [logDeriv_apply, hdΓℝ.deriv, Gammaℝ_def]
    have hπpow : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
      intro h
      exact hπC (Complex.cpow_eq_zero_iff _ _ |>.mp h).1
    have hψ : Complex.digamma (s / 2)
        = deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2) := by
      rw [Complex.digamma_def, logDeriv_apply]
    rw [hψ]
    have hlogπ : Complex.log Real.pi = (Real.log Real.pi : ℂ) := by
      rw [Complex.ofReal_log Real.pi_pos.le]
    rw [hlogπ]
    field_simp
  -- the Dirichlet leg
  have hlegζ : logDeriv riemannZeta s = zetaLogDeriv s := by
    rw [logDeriv_apply, zetaLogDeriv]
  rw [hlegF, hlegΓ, hlegζ]
  ring

/-- The weld split as a local identity of functions: every jet of `ξ'/ξ` on the half-plane
splits into the rational, half-argument digamma, and Dirichlet legs. -/
theorem xiLogDeriv_eventuallyEq_split {s : ℂ} (hs : 1 < s.re) :
    xiLogDeriv =ᶠ[nhds s] fun w =>
      1 / w + 1 / (w - 1) - (Real.log Real.pi) / 2
        + (1 / 2) * Complex.digamma (w / 2) + zetaLogDeriv w := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with w hw
  exact xiLogDeriv_split hw

/-! ## The chain: frequency collapse plus QH forces `ξ` hypertranscendental -/

/-- **The Dirichlet frequency collapse** — the named analytic input of the chain: a nonzero
jet annihilator of `ξ` produces, through the weld split, the grouping of the relation by
Dirichlet frequency, the minimal-frequency estimate, and the prime-power Vandermonde
extraction, a nonzero half-argument digamma jet polynomial exponentially small on the real
ray. -/
def XiFrequencyCollapse : Prop :=
  ∀ (m : ℕ) (Q : MvPolynomial (Fin (m + 2)) ℂ), Q ≠ 0 →
    (∀ z : ℂ, MvPolynomial.eval (Fin.cons z fun j : Fin (m + 1) =>
      iteratedDeriv (j : ℕ) xi z) Q = 0) →
    ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
      ∃ c : ℝ, 0 < c ∧
        (fun σ : ℝ => halfDigammaJetEval n P σ) =O[atTop] fun σ => Real.exp (-c * σ)

/-- **The chain theorem**: quantitative Hölder and the Dirichlet frequency collapse force
the completed `ξ` to be hypertranscendental. -/
theorem xi_hypertranscendental_of_quantitativeHolder
    (hQH : QuantitativeHolder) (hFC : XiFrequencyCollapse) :
    Hypertranscendental xi := by
  rintro ⟨m, Q, hQ0, hQz⟩
  obtain ⟨n, P, hP0, c, hc, hO⟩ := hFC m Q hQ0 hQz
  exact hP0 (hQH n P ⟨c, hc, hO⟩)

/-- **The chain theorem, Watson form**: the sectorial Gevrey–Watson input and the Dirichlet
frequency collapse force `ξ` hypertranscendental — the vanishing side of QH being the
machine-checked Hölder theorem. -/
theorem xi_hypertranscendental_of_watsonFlatness
    (hW : WatsonFlatness) (hFC : XiFrequencyCollapse) :
    Hypertranscendental xi :=
  xi_hypertranscendental_of_quantitativeHolder
    (quantitativeHolder_of_watsonFlatness hW) hFC

/-- The Watson-flatness input is now unconditional: only the independent Dirichlet-frequency
collapse remains in the completed-`xi` chain. -/
theorem xi_hypertranscendental_of_frequencyCollapse
    (hFC : XiFrequencyCollapse) : Hypertranscendental xi :=
  xi_hypertranscendental_of_watsonFlatness HTGeometry.watsonFlatness hFC

end RHTower

end
