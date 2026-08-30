import GaloisForLFunctions.HTGeometry.ScalingGermRigidity

/-!
# The Ritt cocycle form of a Poincaré germ

For a germ `R` fixing the origin with multiplier `λ` and its Poincaré germ `σ` (`σ (λ z) = R (σ z)`,
`σ 0 = 0`, `σ' 0 = 1`), an order-one relation

```text
(σ')^r = a z^j A(σ)
```

is equivalent to the multiplicative cocycle

```text
(R')^r A = λ^(r+j) (A ∘ R)
```

near the fixed point.  Differentiating the Poincaré equation converts one into the other; the
converse needs only that the quotient `(σ')^r / A(σ)` transforms by `λ^j` under the scaling, whence
scaling rigidity forces it to be the monomial `a z^j`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The chain rule for the Poincaré equation. -/
theorem deriv_poincare {sigma R : ℂ → ℂ} {lam : ℂ} (hsig : AnalyticAt ℂ sigma 0)
    (hR : AnalyticAt ℂ R 0) (hsig0 : sigma 0 = 0)
    (hpoin : ∀ᶠ z in 𝓝 (0 : ℂ), sigma (lam * z) = R (sigma z)) :
    ∀ᶠ z in 𝓝 (0 : ℂ), lam * deriv sigma (lam * z) = deriv R (sigma z) * deriv sigma z := by
  have hscale : Filter.Tendsto (fun z : ℂ => lam * z) (𝓝 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun z : ℂ => lam * z) (𝓝 0) (𝓝 (lam * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using h
  have hsigTo : Filter.Tendsto sigma (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have := hsig.continuousAt.tendsto
    rwa [hsig0] at this
  filter_upwards [hpoin.eventually_nhds, hsig.eventually_analyticAt,
    hscale.eventually hsig.eventually_analyticAt,
    hsigTo.eventually hR.eventually_analyticAt] with z hz hsz hslz hrz
  have hleft : HasDerivAt (fun y : ℂ => sigma (lam * y)) (deriv sigma (lam * z) * lam) z := by
    have hin : HasDerivAt (fun y : ℂ => lam * y) lam z := by
      simpa using (hasDerivAt_id z).const_mul lam
    exact (hslz.differentiableAt.hasDerivAt).comp z hin
  have hright : HasDerivAt (fun y : ℂ => R (sigma y)) (deriv R (sigma z) * deriv sigma z) z :=
    (hrz.differentiableAt.hasDerivAt).comp z hsz.differentiableAt.hasDerivAt
  have hd : deriv sigma (lam * z) * lam = deriv R (sigma z) * deriv sigma z := by
    rw [← hleft.deriv, ← hright.deriv]
    exact Filter.EventuallyEq.deriv_eq hz
  linear_combination hd

/-- **The cocycle produces the Ritt form.**  A multiplicative cocycle for `A` along `R` forces the
Poincaré germ to satisfy the order-one relation `(σ')^r = a z^j A(σ)`. -/
theorem ritt_form_of_cocycle {sigma R A : ℂ → ℂ} {lam : ℂ} {r j : ℕ} (hr : 0 < r)
    (hlam0 : lam ≠ 0) (hlam : ‖lam‖ < 1)
    (hsig : AnalyticAt ℂ sigma 0) (hsig0 : sigma 0 = 0) (hsig' : deriv sigma 0 = 1)
    (hR : AnalyticAt ℂ R 0) (hR' : deriv R 0 = lam)
    (hA : AnalyticAt ℂ A 0) (hA0 : A 0 ≠ 0)
    (hpoin : ∀ᶠ z in 𝓝 (0 : ℂ), sigma (lam * z) = R (sigma z))
    (hcoc : ∀ᶠ t in 𝓝 (0 : ℂ), deriv R t ^ r * A t = lam ^ (r + j) * A (R t)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), deriv sigma z ^ r = a * z ^ j * A (sigma z) := by
  have hsigTo : Filter.Tendsto sigma (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have := hsig.continuousAt.tendsto
    rwa [hsig0] at this
  have hAsig : AnalyticAt ℂ (fun z => A (sigma z)) 0 := by
    have hA' : AnalyticAt ℂ A (sigma 0) := by rw [hsig0]; exact hA
    exact hA'.comp hsig
  have hAsig0 : A (sigma 0) ≠ 0 := by rw [hsig0]; exact hA0
  set H : ℂ → ℂ := fun z => deriv sigma z ^ r / A (sigma z) with hHdef
  have hHan : AnalyticAt ℂ H 0 := ((hsig.deriv).pow r).div hAsig hAsig0
  -- the transformation law
  have hderivR : ∀ᶠ z in 𝓝 (0 : ℂ), deriv R (sigma z) ≠ 0 := by
    have hcont : ContinuousAt (fun z => deriv R (sigma z)) 0 := by
      have h1 : ContinuousAt (deriv R) (sigma 0) := by rw [hsig0]; exact (hR.deriv).continuousAt
      exact h1.comp hsig.continuousAt
    have hval : deriv R (sigma 0) ≠ 0 := by rw [hsig0, hR']; exact hlam0
    exact hcont.eventually_ne hval
  have hAne : ∀ᶠ z in 𝓝 (0 : ℂ), A (sigma z) ≠ 0 :=
    hAsig.continuousAt.eventually_ne hAsig0
  have hlaw : ∀ᶠ z in 𝓝 (0 : ℂ), H (lam * z) = lam ^ j * H z := by
    filter_upwards [deriv_poincare hsig hR hsig0 hpoin, hpoin, hderivR, hAne,
      hsigTo.eventually hcoc] with z hd hp hRne hAz hc
    have hnum : deriv sigma (lam * z) ^ r
        = deriv R (sigma z) ^ r * deriv sigma z ^ r / lam ^ r := by
      have hstep : deriv sigma (lam * z) = deriv R (sigma z) * deriv sigma z / lam := by
        field_simp at hd ⊢
        linear_combination hd
      rw [hstep, div_pow, mul_pow]
    have hden : A (R (sigma z)) = deriv R (sigma z) ^ r * A (sigma z) / lam ^ (r + j) := by
      have hlamrj : lam ^ (r + j) ≠ 0 := pow_ne_zero _ hlam0
      field_simp
      linear_combination -hc
    show deriv sigma (lam * z) ^ r / A (sigma (lam * z))
      = lam ^ j * (deriv sigma z ^ r / A (sigma z))
    rw [hp, hnum, hden]
    have hRr : deriv R (sigma z) ^ r ≠ 0 := pow_ne_zero r hRne
    have hlr : (lam : ℂ) ^ r ≠ 0 := pow_ne_zero r hlam0
    have hlrj : (lam : ℂ) ^ (r + j) ≠ 0 := pow_ne_zero _ hlam0
    field_simp
    ring
  -- rigidity
  rcases eq_monomial_of_scaling hlam0 hlam hHan hlaw with hzero | ⟨m, a, ha, hcm, hmono⟩
  · exfalso
    have h0 : H 0 = 0 := hzero.self_of_nhds
    have : deriv sigma 0 ^ r / A (sigma 0) = 0 := h0
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · rw [hsig', one_pow] at h
      exact one_ne_zero h
    · exact hAsig0 h
  · have hjm : j = m := by
      have hnorm : ‖lam‖ ^ j = ‖lam‖ ^ m := by
        have := congrArg norm hcm
        simpa [norm_pow] using this
      have hpos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam0
      exact pow_right_injective₀ hpos hlam.ne hnorm
    subst hjm
    refine ⟨a, ha, ?_⟩
    filter_upwards [hmono, hAne] with z hz hAz
    have : deriv sigma z ^ r / A (sigma z) = a * z ^ j := hz
    field_simp at this
    linear_combination this

/-- **The Ritt form produces the cocycle.**  An order-one relation `(σ')^r = a z^j A(σ)` for the
Poincaré germ is a multiplicative cocycle for `A` along `R`. -/
theorem cocycle_of_ritt_form {sigma R A : ℂ → ℂ} {lam a : ℂ} {r j : ℕ}
    (hlam0 : lam ≠ 0) (ha : a ≠ 0)
    (hsig : AnalyticAt ℂ sigma 0) (hsig0 : sigma 0 = 0) (hsig' : deriv sigma 0 = 1)
    (hR : AnalyticAt ℂ R 0) (hA : AnalyticAt ℂ A 0)
    (hpoin : ∀ᶠ z in 𝓝 (0 : ℂ), sigma (lam * z) = R (sigma z))
    (hritt : ∀ᶠ z in 𝓝 (0 : ℂ), deriv sigma z ^ r = a * z ^ j * A (sigma z)) :
    ∀ᶠ t in 𝓝 (0 : ℂ), deriv R t ^ r * A t = lam ^ (r + j) * A (R t) := by
  have hscale : Filter.Tendsto (fun z : ℂ => lam * z) (𝓝 0) (𝓝 0) := by
    have h : Filter.Tendsto (fun z : ℂ => lam * z) (𝓝 0) (𝓝 (lam * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using h
  have hR0 : R 0 = 0 := by
    have h := hpoin.self_of_nhds
    rw [mul_zero, hsig0] at h
    exact h.symm
  -- the cocycle along the Poincaré germ, off the origin
  have hpunct : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv R (sigma z) ^ r * A (sigma z) = lam ^ (r + j) * A (R (sigma z)) := by
    filter_upwards [nhdsWithin_le_nhds (deriv_poincare hsig hR hsig0 hpoin),
      nhdsWithin_le_nhds hritt, nhdsWithin_le_nhds (hscale.eventually hritt),
      nhdsWithin_le_nhds hpoin, self_mem_nhdsWithin] with z hd h1 h2 hp hz0
    have hzj : (z : ℂ) ^ j ≠ 0 := pow_ne_zero j hz0
    have hlr : (lam : ℂ) ^ r ≠ 0 := pow_ne_zero r hlam0
    have hstep : deriv sigma (lam * z) = deriv R (sigma z) * deriv sigma z / lam := by
      field_simp at hd ⊢
      linear_combination hd
    have h2' : deriv R (sigma z) ^ r * deriv sigma z ^ r / lam ^ r
        = a * (lam * z) ^ j * A (R (sigma z)) := by
      rw [← hp, ← h2, hstep, div_pow, mul_pow]
    rw [h1] at h2'
    have h3 : deriv R (sigma z) ^ r * (a * z ^ j * A (sigma z))
        = lam ^ r * (a * (lam * z) ^ j * A (R (sigma z))) := by
      rw [← h2']
      field_simp
    rw [mul_pow] at h3
    refine mul_left_cancel₀ (mul_ne_zero ha hzj) ?_
    linear_combination h3
  -- transport along the local inverse of the Poincaré germ
  have hsd : HasStrictDerivAt sigma 1 0 := by
    have h := hsig.hasStrictDerivAt
    rwa [hsig'] at h
  have hone : (1 : ℂ) ≠ 0 := one_ne_zero
  set kappa : ℂ → ℂ := hsd.localInverse sigma 1 0 hone with hkdef
  have hright : ∀ᶠ t in 𝓝 (sigma 0), sigma (kappa t) = t := hsd.eventually_right_inverse hone
  rw [hsig0] at hright
  have hk0 : kappa 0 = 0 := by
    have hleft : ∀ᶠ x in 𝓝 (0 : ℂ), kappa (sigma x) = x := hsd.eventually_left_inverse hone
    have h := hleft.self_of_nhds
    rwa [hsig0] at h
  have hkTo : Filter.Tendsto kappa (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hkc : ContinuousAt kappa 0 := by
      have h := hsd.to_localInverse hone
      rw [hsig0] at h
      exact h.hasDerivAt.continuousAt
    have := hkc.tendsto
    rwa [hk0] at this
  have hkpunct : ∀ᶠ t in 𝓝[≠] (0 : ℂ), deriv R t ^ r * A t = lam ^ (r + j) * A (R t) := by
    have hmapsW : Filter.Tendsto kappa (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hkTo.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [nhdsWithin_le_nhds hright, self_mem_nhdsWithin] with t ht ht0
      intro hk
      apply ht0
      rw [← ht, hk, hsig0]
      rfl
    filter_upwards [hmapsW.eventually hpunct, nhdsWithin_le_nhds hright] with t ht hrt
    rwa [hrt] at ht
  -- extend across the origin by continuity
  have hcont1 : ContinuousAt (fun t : ℂ => deriv R t ^ r * A t) 0 :=
    ((hR.deriv).continuousAt.pow r).mul hA.continuousAt
  have hcont2 : ContinuousAt (fun t : ℂ => lam ^ (r + j) * A (R t)) 0 := by
    have hA' : ContinuousAt A (R 0) := by rw [hR0]; exact hA.continuousAt
    exact continuousAt_const.mul (hA'.comp hR.continuousAt)
  have hat0 : deriv R 0 ^ r * A 0 = lam ^ (r + j) * A (R 0) := by
    have h1 := (hcont1.tendsto).mono_left (nhdsWithin_le_nhds (s := ({(0:ℂ)}ᶜ)))
    have h2 := (hcont2.tendsto).mono_left (nhdsWithin_le_nhds (s := ({(0:ℂ)}ᶜ)))
    exact tendsto_nhds_unique (h1.congr' hkpunct) h2
  rw [← nhdsNE_sup_pure (0 : ℂ)]
  exact Filter.eventually_sup.mpr ⟨hkpunct, by simpa using hat0⟩

end

end GaloisForLFunctions.HTGeometry
