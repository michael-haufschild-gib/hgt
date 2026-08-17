import Mathlib

/-!
# Linear response of a zeta zero to a single Dirichlet coefficient

Perturbing one Dirichlet coefficient gives the family `ζ_ε(s) = ζ(s) + ε·n^{-s}`.  At a simple
nontrivial zero `ρ` the implicit function theorem produces an analytic branch `ε ↦ r ε` of zeros
with `r 0 = ρ`, and differentiating the identity `ζ_ε(r ε) = 0` gives the response

`dρ/dε = −n^{-ρ}/ζ'(ρ)`.

Without simplicity the same balance is a Puiseux law: if `f = (· − ρ)^m·G` with `G(ρ) ≠ 0`, then
along any sequence of zeros of `f + ε·h` approaching `ρ` the normalized displacement
`(s − ρ)^m/ε` converges to `−h(ρ)/G(ρ)`, so the splitting distance scales like `|ε|^{1/m}`.

The mirror-pair ratio of the resulting susceptibilities carries the probe frequency `n` only
through the exponent `1 − 2β`, and that exponent is trivial exactly on the critical line.  Finally
the probe `n^{-(1/2 + i(t+z))}` has a nonzero section-Taylor coefficient at every order, so a single
frequency is an all-orders transverse object rather than an affine mode.
-/

namespace RHTower.Susceptibility

open Complex Filter Topology

noncomputable section

/-- The single-coefficient perturbation `ζ(s) + ε·n^{-s}` of the Riemann zeta function. -/
noncomputable def perturbedZeta (n : ℕ) (ε s : ℂ) : ℂ :=
  riemannZeta s + ε * (n : ℂ) ^ (-s)

theorem hasDerivAt_cpow_neg {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    HasDerivAt (fun t : ℂ => (n : ℂ) ^ (-t))
      (-((n : ℂ) ^ (-s) * Complex.log (n : ℂ))) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h : HasDerivAt (fun y : ℂ => (n : ℂ) ^ y) ((n : ℂ) ^ (-s) * Complex.log (n : ℂ)) (-s) :=
    (hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := -s) (Or.inl hn0)).hasDerivAt
  have hneg : HasDerivAt (fun t : ℂ => -t) (-1 : ℂ) s := hasDerivAt_neg' s
  have hcomp : HasDerivAt (fun t : ℂ => (n : ℂ) ^ (-t))
      ((n : ℂ) ^ (-s) * Complex.log (n : ℂ) * (-1 : ℂ)) s := h.comp s hneg
  simpa using hcomp

/-- The partial derivative of the perturbed zeta in the perturbation parameter. -/
theorem hasDerivAt_perturbedZeta_fst (n : ℕ) (ε s : ℂ) :
    HasDerivAt (fun e : ℂ => perturbedZeta n e s) ((n : ℂ) ^ (-s)) ε := by
  unfold perturbedZeta
  simpa using ((hasDerivAt_id ε).mul_const ((n : ℂ) ^ (-s))).const_add (riemannZeta s)

/-- The partial derivative of the perturbed zeta in the spectral variable. -/
theorem hasDerivAt_perturbedZeta_snd {n : ℕ} (hn : n ≠ 0) (ε : ℂ) {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (fun t : ℂ => perturbedZeta n ε t)
      (deriv riemannZeta s - ε * ((n : ℂ) ^ (-s) * Complex.log (n : ℂ))) s := by
  unfold perturbedZeta
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  have hp := (hasDerivAt_cpow_neg hn s).const_mul ε
  have hsum : HasDerivAt (fun t : ℂ => riemannZeta t + ε * (n : ℂ) ^ (-t))
      (deriv riemannZeta s + ε * -((n : ℂ) ^ (-s) * Complex.log (n : ℂ))) s := hζ.add hp
  simpa [mul_neg, sub_eq_add_neg] using hsum

end

end RHTower.Susceptibility

namespace RHTower.Susceptibility

open Complex Filter Topology

noncomputable section

theorem isInvertible_smulRight {a : ℂ} (ha : a ≠ 0) :
    (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).IsInvertible :=
  ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 a ha), rfl⟩

theorem continuous_smulRight_comp {g : ℂ × ℂ → ℂ} (hg : Continuous g) :
    Continuous (fun v : ℂ × ℂ => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (g v)) :=
  (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous.comp hg

theorem continuousAt_deriv_riemannZeta {ρ : ℂ} (hρ : ρ ≠ 1) :
    ContinuousAt (deriv riemannZeta) ρ := by
  have hopen : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have han : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := hdiff.analyticOnNhd hopen
  exact ((han ρ hρ).deriv).continuousAt

/-- **Single-coefficient zero response.**  A simple nontrivial zero of `ζ` moves analytically under
the perturbation `ζ + ε·n^{-s}`, with response `dρ/dε = -n^{-ρ}/ζ'(ρ)`. -/
theorem exists_zeroBranch_hasDerivAt {n : ℕ} (hn : n ≠ 0) {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hζ : riemannZeta ρ = 0) (hsimple : deriv riemannZeta ρ ≠ 0) :
    ∃ r : ℂ → ℂ, r 0 = ρ ∧ (∀ᶠ ε in 𝓝 (0 : ℂ), perturbedZeta n ε (r ε) = 0) ∧
      HasDerivAt r (-((n : ℂ) ^ (-ρ)) / deriv riemannZeta ρ) 0 := by
  classical
  set f : ℂ → ℂ → ℂ := fun e s => perturbedZeta n e s with hfdef
  set f₁ : ℂ → ℂ → (ℂ →L[ℂ] ℂ) := fun _ s =>
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((n : ℂ) ^ (-s)) with hf₁
  set f₂ : ℂ → ℂ → (ℂ →L[ℂ] ℂ) := fun e s =>
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (deriv riemannZeta s - e * ((n : ℂ) ^ (-s) * Complex.log (n : ℂ))) with hf₂
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have df₁ : ∀ᶠ v in 𝓝 ((0 : ℂ), ρ), HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1 :=
    Filter.Eventually.of_forall
      (fun v => (hasDerivAt_perturbedZeta_fst n v.1 v.2).hasFDerivAt)
  have hne1 : ∀ᶠ v in 𝓝 ((0 : ℂ), ρ), v.2 ≠ 1 := by
    have hs : ∀ᶠ s in 𝓝 ρ, s ≠ 1 := isOpen_compl_singleton.eventually_mem hρ1
    exact (continuous_snd.tendsto ((0 : ℂ), ρ)).eventually hs
  have df₂ : ∀ᶠ v in 𝓝 ((0 : ℂ), ρ), HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2 := by
    filter_upwards [hne1] with v hv
    exact (hasDerivAt_perturbedZeta_snd hn v.1 hv).hasFDerivAt
  have hcpow : Continuous (fun v : ℂ × ℂ => (n : ℂ) ^ (-v.2)) :=
    Continuous.const_cpow continuous_snd.neg (Or.inl hn0)
  have cf₁ : ContinuousAt (Function.uncurry f₁) ((0 : ℂ), ρ) :=
    (continuous_smulRight_comp hcpow).continuousAt
  have cf₂ : ContinuousAt (Function.uncurry f₂) ((0 : ℂ), ρ) := by
    have hg : ContinuousAt (fun v : ℂ × ℂ =>
        deriv riemannZeta v.2 - v.1 * ((n : ℂ) ^ (-v.2) * Complex.log (n : ℂ)))
        ((0 : ℂ), ρ) := by
      refine ContinuousAt.sub ?_ ?_
      · exact ContinuousAt.comp (x := ((0 : ℂ), ρ)) (continuousAt_deriv_riemannZeta hρ1)
          continuousAt_snd
      · exact continuousAt_fst.mul (hcpow.continuousAt.mul continuousAt_const)
    exact ((ContinuousLinearMap.smulRightL ℂ ℂ ℂ
      (1 : ℂ →L[ℂ] ℂ)).continuous.continuousAt).comp hg
  have if₂ : (f₂ (0 : ℂ) ρ).IsInvertible := by
    have : f₂ (0 : ℂ) ρ = ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (deriv riemannZeta ρ) := by
      simp [hf₂]
    rw [this]
    exact isInvertible_smulRight hsimple
  set r : ℂ → ℂ := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂ with hr
  have hzero : f (0 : ℂ) ρ = 0 := by
    simp [hfdef, perturbedZeta, hζ]
  have hr0 : r 0 = ρ := by
    have h := (eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).self_of_nhds
    exact h.mp rfl
  have hzeros : ∀ᶠ ε in 𝓝 (0 : ℂ), perturbedZeta n ε (r ε) = 0 := by
    have h := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂
    filter_upwards [h] with ε hε
    rw [show perturbedZeta n ε (r ε) = f ε (r ε) from rfl, hε, hzero]
  have hdiff : DifferentiableAt ℂ r 0 :=
    (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂).hasFDerivAt.differentiableAt
  refine ⟨r, hr0, hzeros, ?_⟩
  set d : ℂ := deriv r 0 with hddef
  have hrd : HasDerivAt r d 0 := hdiff.hasDerivAt
  have hζd : HasDerivAt riemannZeta (deriv riemannZeta ρ) (r 0) := by
    rw [hr0]
    exact (differentiableAt_riemannZeta hρ1).hasDerivAt
  have h1 : HasDerivAt (fun ε : ℂ => riemannZeta (r ε)) (deriv riemannZeta ρ * d) 0 :=
    hζd.comp 0 hrd
  have hcp : HasDerivAt (fun t : ℂ => (n : ℂ) ^ (-t))
      (-((n : ℂ) ^ (-(r 0)) * Complex.log (n : ℂ))) (r 0) := hasDerivAt_cpow_neg hn (r 0)
  have h2 : HasDerivAt (fun ε : ℂ => (n : ℂ) ^ (-(r ε)))
      (-((n : ℂ) ^ (-(r 0)) * Complex.log (n : ℂ)) * d) 0 := hcp.comp 0 hrd
  have h3 : HasDerivAt (fun ε : ℂ => ε * (n : ℂ) ^ (-(r ε)))
      (1 * (n : ℂ) ^ (-(r 0)) +
        0 * (-((n : ℂ) ^ (-(r 0)) * Complex.log (n : ℂ)) * d)) 0 :=
    (hasDerivAt_id (0 : ℂ)).mul h2
  have hF : HasDerivAt (fun ε : ℂ => perturbedZeta n ε (r ε))
      (deriv riemannZeta ρ * d +
        (1 * (n : ℂ) ^ (-(r 0)) +
          0 * (-((n : ℂ) ^ (-(r 0)) * Complex.log (n : ℂ)) * d))) 0 := h1.add h3
  have hF0 : HasDerivAt (fun ε : ℂ => perturbedZeta n ε (r ε)) 0 0 := by
    refine (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hzeros] with ε hε
    exact hε
  have huniq := hF.unique hF0
  rw [hr0] at huniq
  have hkey : deriv riemannZeta ρ * d + (n : ℂ) ^ (-ρ) = 0 := by
    simpa using huniq
  have hdval : d = -((n : ℂ) ^ (-ρ)) / deriv riemannZeta ρ := by
    field_simp
    linear_combination hkey
  rw [← hdval]
  exact hrd

end

end RHTower.Susceptibility

namespace RHTower.Susceptibility

open Complex Filter Topology

noncomputable section

/-- **Multiplicity splitting law.**  If `f = (· − ρ)^m · G` with `G` continuous and nonzero at `ρ`,
then along any sequence of zeros of `f + ε·h` approaching `ρ` with `ε → 0`, the normalized
displacement `(s − ρ)^m / ε` converges to `−h(ρ)/G(ρ)`.  This is the Puiseux response law: the
splitting distance is asymptotically `|ε·h(ρ)/G(ρ)|^{1/m}`. -/
theorem tendsto_multiplicitySplit {m : ℕ} {ρ c : ℂ} {G h : ℂ → ℂ}
    (hG : ContinuousAt G ρ) (hGval : G ρ = c) (hc : c ≠ 0) (hh : ContinuousAt h ρ)
    {ε s : ℕ → ℂ} (hε0 : ∀ k, ε k ≠ 0) (hs : Tendsto s atTop (𝓝 ρ))
    (heq : ∀ k, (s k - ρ) ^ m * G (s k) + ε k * h (s k) = 0) :
    Tendsto (fun k => (s k - ρ) ^ m / ε k) atTop (𝓝 (-h ρ / c)) := by
  have hGne : ∀ᶠ k in atTop, G (s k) ≠ 0 := by
    have hnb : ∀ᶠ z in 𝓝 ρ, G z ≠ 0 := by
      have : ContinuousAt G ρ := hG
      exact this.eventually_ne (by rw [hGval]; exact hc)
    exact hs.eventually hnb
  have hcongr : (fun k => (s k - ρ) ^ m / ε k) =ᶠ[atTop] fun k => -h (s k) / G (s k) := by
    filter_upwards [hGne] with k hk
    have hεk : ε k ≠ 0 := hε0 k
    have h1 : (s k - ρ) ^ m * G (s k) = -(ε k * h (s k)) :=
      eq_neg_of_add_eq_zero_left (heq k)
    rw [div_eq_div_iff hεk hk, h1]
    ring
  refine Tendsto.congr' hcongr.symm ?_
  have hnum : Tendsto (fun k => -h (s k)) atTop (𝓝 (-h ρ)) := (hh.tendsto.comp hs).neg
  have hden : Tendsto (fun k => G (s k)) atTop (𝓝 c) := by
    have hcomp := hG.tendsto.comp hs
    rwa [hGval] at hcomp
  exact hnum.div hden hc

/-- **Frequency independence of the mirror ratio characterizes the critical line.**  The
mirror-pair susceptibility ratio carries the probe frequency only through the exponent `1 − 2β`,
which is trivial exactly on the critical line. -/
theorem rpow_frequency_independent_iff {β : ℝ} :
    (∀ m n : ℕ, 2 ≤ m → 2 ≤ n →
        (m : ℝ) ^ (1 - 2 * β) = (n : ℝ) ^ (1 - 2 * β)) ↔ β = 1 / 2 := by
  constructor
  · intro h
    have h23 := h 2 3 (le_refl 2) (by norm_num)
    have h2 : (0 : ℝ) < 2 := by norm_num
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hlog := congrArg Real.log h23
    rw [Real.log_rpow (by exact_mod_cast h2), Real.log_rpow (by exact_mod_cast h3)] at hlog
    have hne : Real.log 2 ≠ Real.log 3 := by
      intro heq
      have := Real.exp_log h2
      have h2' : (2 : ℝ) = 3 := by
        rw [← Real.exp_log h2, ← Real.exp_log h3, heq]
      norm_num at h2'
    have hzero : (1 : ℝ) - 2 * β = 0 := by
      by_contra hne0
      apply hne
      have := mul_left_cancel₀ hne0 (by push_cast at hlog ⊢; linarith [hlog] : (1 - 2 * β) * Real.log 2 = (1 - 2 * β) * Real.log 3)
      exact this
    linarith
  · intro h m n _ _
    rw [h]
    norm_num

/-- **All-orders transversality of a single frequency.**  Every section-Taylor coefficient of the
probe `n^{-(1/2 + i(t+z))}` in `z` is nonzero, so the response is not an affine mode. -/
theorem transverse_coefficient_ne_zero {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    (-Complex.I * Complex.log (n : ℂ)) ^ k / (Nat.factorial k : ℂ) ≠ 0 := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hn
  have hlog : Complex.log (n : ℂ) ≠ 0 := by
    have hpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    have hre : (Complex.log (n : ℂ)).re = Real.log (n : ℝ) := by
      rw [Complex.log_re, Complex.norm_natCast]
    intro h0
    rw [h0] at hre
    simp at hre
    linarith
  have hfac : (Nat.factorial k : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  exact div_ne_zero (pow_ne_zero k (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hlog)) hfac

/-- The section expansion of the probe frequency about a base height. -/
theorem cpow_section_factor {n : ℕ} (hn : n ≠ 0) (t z : ℂ) :
    (n : ℂ) ^ (-(1 / 2 + Complex.I * (t + z)))
      = (n : ℂ) ^ (-(1 / 2 + Complex.I * t)) *
          Complex.exp (-Complex.I * z * Complex.log (n : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_add]
  congr 1
  ring

end

end RHTower.Susceptibility
