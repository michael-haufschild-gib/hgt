/-
# The dyadic non-square obstruction from the odd cover period (the Kummer analytic input)

The Kummer route to `hDisc` (`KummerDeck.lean`, `Q62KummerAssembly.lean`) is algebraically
complete: `kummer_irreducible` builds the order-`2ᵏ` deck cover field `B[w]/(X^{2ᵏ} − a)` from the
single input **`a = φ_{c₁}∘f^[k]` is not a square in the base field** (the `p = 2` Capelli case, via
`−1` square).  That non-square condition is the genuine analytic content of the disconnected case —
the *dyadic monodromy* — and this file proves it from the realized **odd** cover period.

The mechanism (the heart of the argument principle):

* a single-valued nowhere-zero analytic `b` integrated around a closed loop has integer winding
  `∮ d log b ∈ 2πiℤ`  (`pathWinding_integer`, already in `CoverConstruction`);
* if `b² = a` then `∮ d log a = 2 ∮ d log b ∈ 2·2πiℤ` is an **even** multiple of `2πi`;
* but the genuine radicand `a = φ_{c₁}∘f^[k]` has period exactly `2πi` over the depth-`k` cover loop
  (`circleIntegral_dlog_bottcher` scaled by `pathInt_iterate_comp`) — an **odd** multiple.

Even ≠ odd, so no analytic square root of `a` exists: `a` is not a square.  This is the concrete,
loop-level realization of the abstract `not_square_of_period_ftc`, lifted to the statement
"`a`'s germ is not a square in `analyticSubring U`" that the Kummer irreducibility consumes.
Axiom-clean; no Riemann-surface gluing.
-/
import GaloisForLFunctions.Bottcher.CoverConstruction

open Set Filter

namespace Bottcher

open Complex

/-- **[Path core] No odd-period square root.** If `B = b∘γ` is a closed, nowhere-zero,
differentiable loop and `La` is an antiderivative of `2·d log B` (i.e. of `d log(B²)`) whose total
change over the loop is an **odd** multiple `2πi·(2m+1)`, a contradiction follows.  By
`pathWinding_integer` the half-period `∮ d log B = ½·La` is an integer multiple of `2πi`, so its
double `La` is an *even* multiple — incompatible with odd.  This is the parity engine of the dyadic
non-square; `not_eqOn_sq_of_odd_period` feeds it `B = (√a)∘γ`. -/
theorem False_of_sqrt_odd_period {B La : ℝ → ℂ} {m : ℤ}
    (hBclosed : B (2 * Real.pi) = B 0)
    (hBne : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), B t ≠ 0)
    (hdB : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt B (deriv B t) t)
    (hLa : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt La (2 * (deriv B t / B t)) t)
    (hperiod : La (2 * Real.pi) - La 0
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)) : False := by
  have hdLb : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      HasDerivAt (fun s => (2:ℂ)⁻¹ * La s) (deriv B t / B t) t := by
    intro t ht
    have h := (hLa t ht).const_mul (2:ℂ)⁻¹
    have he : (2:ℂ)⁻¹ * (2 * (deriv B t / B t)) = deriv B t / B t := by
      rw [← mul_assoc, inv_mul_cancel₀ (two_ne_zero), one_mul]
    rwa [he] at h
  obtain ⟨k, hk⟩ := pathWinding_integer hBclosed hBne hdB hdLb
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hcollect : (2:ℂ)⁻¹ * (La (2 * Real.pi) - La 0)
      = 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) := by
    rw [mul_sub]; exact hk
  rw [hperiod] at hcollect
  have h2 : 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)
      = (2 * (Real.pi : ℂ) * Complex.I) * (2 * (k : ℂ)) := by
    field_simp at hcollect ⊢; linear_combination hcollect
  have h3 : (2 * (m : ℂ) + 1) = 2 * (k : ℂ) := mul_left_cancel₀ hne (by linear_combination h2)
  have h4 : (2 * m + 1 : ℤ) = 2 * k := by exact_mod_cast h3
  omega

/-- **[Function level] An odd-period nonvanishing `a` has no analytic square root.** For `a`
nowhere-zero on an open `U`, a closed `C¹` loop `γ` in `U`, and an antiderivative `La` of
`d log a` along `γ` with odd total change `2πi·(2m+1)`, no analytic `b` on `U` satisfies `b² = a`
on `U`.  The would-be root composes to a closed nowhere-zero loop `b∘γ`; the chain rule and
`logDeriv_sq` turn `La` into an antiderivative of `2·d log(b∘γ)`, and `False_of_sqrt_odd_period`
fires.  This is the genuine dyadic monodromy: the multivaluedness of `φ_{c₁}^{1/2}` on the cover. -/
theorem not_eqOn_sq_of_odd_period {U : Set ℂ} {a : ℂ → ℂ} {γ γ' La : ℝ → ℂ} {m : ℤ}
    (hUo : IsOpen U) (ha_ne : ∀ w ∈ U, a w ≠ 0)
    (hγU : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), γ t ∈ U)
    (hγclosed : γ (2 * Real.pi) = γ 0)
    (hdγ : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' t) t)
    (hLa : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt La (logDeriv a (γ t) * γ' t) t)
    (hperiod : La (2 * Real.pi) - La 0
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))
    (b : ℂ → ℂ) (hb : AnalyticOnNhd ℂ b U) :
    ¬ Set.EqOn (fun w => b w ^ (2 : ℕ)) a U := by
  intro hb2
  set B : ℝ → ℂ := fun t => b (γ t) with hBdef
  have hbdiff : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt b (deriv b (γ t)) (γ t) :=
    fun t ht => (hb (γ t) (hγU t ht)).differentiableAt.hasDerivAt
  have hBderiv : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      HasDerivAt B (deriv b (γ t) * γ' t) t :=
    fun t ht => (hbdiff t ht).comp t (hdγ t ht)
  have hderivB : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), deriv B t = deriv b (γ t) * γ' t :=
    fun t ht => (hBderiv t ht).deriv
  have hbne : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), b (γ t) ≠ 0 := by
    intro t ht h0
    apply ha_ne _ (hγU t ht)
    rw [← hb2 (hγU t ht)]; simp [h0]
  have hBne : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), B t ≠ 0 := hbne
  have hBclosed : B (2 * Real.pi) = B 0 := by simp only [hBdef, hγclosed]
  have hdB : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt B (deriv B t) t := by
    intro t ht; rw [hderivB t ht]; exact hBderiv t ht
  have hlog : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      logDeriv a (γ t) * γ' t = 2 * (deriv B t / B t) := by
    intro t ht
    have hmem : γ t ∈ U := hγU t ht
    have hEq : a =ᶠ[nhds (γ t)] (fun w => b w ^ (2 : ℕ)) :=
      Filter.eventuallyEq_of_mem (hUo.mem_nhds hmem) (fun w hw => (hb2 hw).symm)
    have hcong : logDeriv a (γ t) = logDeriv (fun w => b w ^ (2 : ℕ)) (γ t) := by
      rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.eq_of_nhds]
    rw [hcong, logDeriv_sq (hbdiff t ht).differentiableAt, hderivB t ht, logDeriv_apply]
    have hBt : B t = b (γ t) := rfl
    rw [hBt]
    field_simp
  have hLa' : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      HasDerivAt La (2 * (deriv B t / B t)) t := by
    intro t ht; rw [← hlog t ht]; exact hLa t ht
  exact False_of_sqrt_odd_period hBclosed hBne hdB hLa' hperiod

/-- **[Carrier level] The radicand germ is not a square in `analyticSubring U`.** Lifting
`not_eqOn_sq_of_odd_period` to the genuine carrier: under the same odd-period loop data, no
analytic germ `g ∈ analyticSubring U` satisfies `g·g = ↑a`.  A germ square `↑f·↑f = ↑a` unfolds
(`Germ.coe_mul`, `Germ.coe_eq`, `eventually_principal`) to the pointwise `f² = a` on `U`, refuted
above.  This is exactly the "`a` not a square" hypothesis that `kummer_irreducible` turns into the
irreducible Kummer polynomial `X^{2ᵏ} − C a`, hence the order-`2ᵏ` deck cover field of `hDisc`. -/
theorem germ_not_sq_of_odd_period {U : Set ℂ} {a : ℂ → ℂ} {γ γ' La : ℝ → ℂ} {m : ℤ}
    (hUo : IsOpen U) (ha_ne : ∀ w ∈ U, a w ≠ 0)
    (hγU : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), γ t ∈ U)
    (hγclosed : γ (2 * Real.pi) = γ 0)
    (hdγ : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' t) t)
    (hLa : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt La (logDeriv a (γ t) * γ' t) t)
    (hperiod : La (2 * Real.pi) - La 0
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)) :
    ∀ g : Filter.Germ (𝓟 U) ℂ, g ∈ analyticSubring U → g * g ≠ (↑a : Filter.Germ (𝓟 U) ℂ) := by
  rintro g ⟨f, hf, rfl⟩ hgg
  have hgg' : (↑f : Filter.Germ (𝓟 U) ℂ) * ↑f = (↑a : Filter.Germ (𝓟 U) ℂ) := hgg
  rw [← Germ.coe_mul] at hgg'
  have hEq : (fun w => f w * f w) =ᶠ[𝓟 U] a := Germ.coe_eq.mp hgg'
  have hpt : ∀ w ∈ U, f w * f w = a w := Filter.eventually_principal.mp hEq
  exact not_eqOn_sq_of_odd_period hUo ha_ne hγU hγclosed hdγ hLa hperiod f hf
    (fun w hw => by show f w ^ (2 : ℕ) = a w; rw [sq]; exact hpt w hw)

end Bottcher
