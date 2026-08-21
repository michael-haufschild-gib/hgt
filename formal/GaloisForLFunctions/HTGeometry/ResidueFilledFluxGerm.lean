import Mathlib

/-!
# The residue-filled completed-flux germ

At a zero of finite order the normalized logarithmic derivative `-x f'(w+x)/f(w+x)` has a removable
singularity at `x = 0`, and filling it with the negative vanishing order produces one canonical
analytic germ.  Writing `f z = (z-w)^m g z` with `g(w) ≠ 0`, the germ is exactly

```text
-m - x·g'(w+x)/g(w+x),
```

which is manifestly analytic.  This is the local object whose Taylor coefficients are the
"completed-flux passport" of `f` at `w`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- The residue-filled completed-flux germ of `f` based at `w`. -/
noncomputable def fluxGerm (f : ℂ → ℂ) (w : ℂ) (x : ℂ) : ℂ :=
  if x = 0 then -((analyticOrderAt f w).toNat : ℂ) else -x * deriv f (w + x) / f (w + x)

@[simp] theorem fluxGerm_zero (f : ℂ → ℂ) (w : ℂ) :
    fluxGerm f w 0 = -((analyticOrderAt f w).toNat : ℂ) := by
  simp [fluxGerm]

theorem fluxGerm_of_ne_zero (f : ℂ → ℂ) (w : ℂ) {x : ℂ} (hx : x ≠ 0) :
    fluxGerm f w x = -x * deriv f (w + x) / f (w + x) := by
  simp [fluxGerm, hx]

/-- **The residue-filled germ is analytic at its centre.** -/
theorem fluxGerm_analyticAt_zero {f : ℂ → ℂ} {w : ℂ} {m : ℕ} (hf : AnalyticAt ℂ f w)
    (hord : analyticOrderAt f w = m) : AnalyticAt ℂ (fluxGerm f w) 0 := by
  obtain ⟨g, hg, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp hord
  have hfacmul : ∀ᶠ z in 𝓝 w, f z = (z - w) ^ m * g z := by
    filter_upwards [hfac] with z hz
    simpa using hz
  have htoNat : ((analyticOrderAt f w).toNat : ℂ) = (m : ℂ) := by
    rw [hord]
    simp
  -- the analytic model
  set G : ℂ → ℂ := fun x => -(m : ℂ) - x * (deriv g (w + x) / g (w + x)) with hG
  have hshift : AnalyticAt ℂ (fun x : ℂ => w + x) 0 := analyticAt_const.add analyticAt_id
  have hquot : AnalyticAt ℂ (fun z : ℂ => deriv g z / g z) w := hg.deriv.div hg hg0
  have hcomp : AnalyticAt ℂ (fun x : ℂ => deriv g (w + x) / g (w + x)) 0 := by
    have := hquot.comp_of_eq hshift (by simp)
    simpa [Function.comp_def] using this
  have hGan : AnalyticAt ℂ G 0 := analyticAt_const.sub (analyticAt_id.mul hcomp)
  refine hGan.congr ?_
  -- transport the local data to the `x` coordinate
  have htend : Tendsto (fun x : ℂ => w + x) (𝓝 0) (𝓝 w) := by
    have hc : Continuous (fun x : ℂ => w + x) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  have hfacNhds : ∀ᶠ x : ℂ in 𝓝 0, ∀ᶠ y in 𝓝 (w + x), f y = (y - w) ^ m * g y :=
    htend.eventually hfacmul.eventually_nhds
  have hgNe : ∀ᶠ x : ℂ in 𝓝 0, g (w + x) ≠ 0 :=
    htend.eventually (hg.continuousAt.eventually_ne hg0)
  have hgAn : ∀ᶠ x : ℂ in 𝓝 0, AnalyticAt ℂ g (w + x) :=
    htend.eventually hg.eventually_analyticAt
  filter_upwards [hfacNhds, hgNe, hgAn] with x hfx hgx hgax
  by_cases hx : x = 0
  · subst x
    rw [fluxGerm_zero, htoNat, hG]
    simp
  rw [fluxGerm_of_ne_zero f w hx, hG]
  have hderivf : deriv f (w + x) = deriv (fun y : ℂ => (y - w) ^ m * g y) (w + x) :=
    Filter.EventuallyEq.deriv_eq hfx
  have hgd : HasDerivAt g (deriv g (w + x)) (w + x) := hgax.differentiableAt.hasDerivAt
  have hpow : HasDerivAt (fun y : ℂ => (y - w) ^ m) ((m : ℂ) * x ^ (m - 1)) (w + x) := by
    have h1 : HasDerivAt (fun y : ℂ => y - w) 1 (w + x) := (hasDerivAt_id _).sub_const w
    have := h1.fun_pow m
    simpa using this
  have hprod : deriv (fun y : ℂ => (y - w) ^ m * g y) (w + x)
      = (m : ℂ) * x ^ (m - 1) * g (w + x) + x ^ m * deriv g (w + x) := by
    have := (hpow.fun_mul hgd).deriv
    simpa using this
  have hfval : f (w + x) = x ^ m * g (w + x) := by
    have := hfx.self_of_nhds
    simpa using this
  rw [hderivf, hprod, hfval]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul, neg_zero, zero_sub]
    field_simp
    ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hxk : x ^ (k + 1) ≠ 0 := pow_ne_zero _ hx
    simp only [Nat.succ_sub_one, pow_succ]
    field_simp
    ring

/-- A zero of finite order is isolated. -/
theorem eventually_ne_zero_of_analyticOrderAt_eq {f : ℂ → ℂ} {w : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f w) (hord : analyticOrderAt f w = m) :
    ∀ᶠ x : ℂ in 𝓝 0, x ≠ 0 → f (w + x) ≠ 0 := by
  obtain ⟨g, hg, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp hord
  have htend : Tendsto (fun x : ℂ => w + x) (𝓝 0) (𝓝 w) := by
    have hc : Continuous (fun x : ℂ => w + x) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  have hfacx : ∀ᶠ x : ℂ in 𝓝 0, f (w + x) = x ^ m * g (w + x) := by
    filter_upwards [htend.eventually hfac] with x hx
    simpa using hx
  have hgx : ∀ᶠ x : ℂ in 𝓝 0, g (w + x) ≠ 0 :=
    htend.eventually (hg.continuousAt.eventually_ne hg0)
  filter_upwards [hfacx, hgx] with x hfx hgx hx
  rw [hfx]
  exact mul_ne_zero (pow_ne_zero _ hx) hgx

/-- **The flux germ of a product is the sum of the flux germs.** -/
theorem fluxGerm_mul {f g : ℂ → ℂ} {w : ℂ} {m n : ℕ}
    (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (hfo : analyticOrderAt f w = m) (hgo : analyticOrderAt g w = n) :
    fluxGerm (f * g) w =ᶠ[𝓝 0] fluxGerm f w + fluxGerm g w := by
  have htend : Tendsto (fun x : ℂ => w + x) (𝓝 0) (𝓝 w) := by
    have hc : Continuous (fun x : ℂ => w + x) := continuous_const.add continuous_id
    simpa using hc.tendsto 0
  have hordmul : analyticOrderAt (f * g) w = ((m + n : ℕ) : ℕ∞) := by
    rw [analyticOrderAt_mul hf hg, hfo, hgo]
    exact (Nat.cast_add m n).symm
  have hfa : ∀ᶠ x : ℂ in 𝓝 0, AnalyticAt ℂ f (w + x) :=
    htend.eventually hf.eventually_analyticAt
  have hga : ∀ᶠ x : ℂ in 𝓝 0, AnalyticAt ℂ g (w + x) :=
    htend.eventually hg.eventually_analyticAt
  filter_upwards [eventually_ne_zero_of_analyticOrderAt_eq hf hfo,
    eventually_ne_zero_of_analyticOrderAt_eq hg hgo, hfa, hga] with x hfx hgx hfax hgax
  by_cases hx : x = 0
  · subst x
    rw [Pi.add_apply, fluxGerm_zero, fluxGerm_zero, fluxGerm_zero, hordmul, hfo, hgo]
    simp only [ENat.toNat_coe]
    push_cast
    ring
  · have hfv : f (w + x) ≠ 0 := hfx hx
    have hgv : g (w + x) ≠ 0 := hgx hx
    have hd : deriv (f * g) (w + x)
        = deriv f (w + x) * g (w + x) + f (w + x) * deriv g (w + x) := by
      have h1 : HasDerivAt f (deriv f (w + x)) (w + x) := hfax.differentiableAt.hasDerivAt
      have h2 : HasDerivAt g (deriv g (w + x)) (w + x) := hgax.differentiableAt.hasDerivAt
      exact (h1.mul h2).deriv
    rw [Pi.add_apply, fluxGerm_of_ne_zero _ _ hx, fluxGerm_of_ne_zero _ _ hx,
      fluxGerm_of_ne_zero _ _ hx, Pi.mul_apply, hd]
    field_simp
    ring

/-! ## Affine change of the local coordinate -/

theorem analyticAt_comp_affine {f : ℂ → ℂ} {μ ν z : ℂ} (hf : AnalyticAt ℂ f (μ * z + ν)) :
    AnalyticAt ℂ (fun s : ℂ => f (μ * s + ν)) z :=
  hf.comp_of_eq ((analyticAt_const.mul analyticAt_id).add analyticAt_const) rfl

/-- The vanishing order is unchanged by an invertible affine change of the local coordinate. -/
theorem analyticOrderAt_comp_affine {f : ℂ → ℂ} {μ ν z : ℂ} {n : ℕ} (hμ : μ ≠ 0)
    (hf : AnalyticAt ℂ f (μ * z + ν)) (h : analyticOrderAt f (μ * z + ν) = n) :
    analyticOrderAt (fun s : ℂ => f (μ * s + ν)) z = n := by
  obtain ⟨g, hg, hg0, hfac⟩ := hf.analyticOrderAt_eq_natCast.mp h
  refine (analyticAt_comp_affine hf).analyticOrderAt_eq_natCast.mpr
    ⟨fun s => μ ^ n * g (μ * s + ν), ?_, ?_, ?_⟩
  · exact (analyticAt_const.mul (analyticAt_comp_affine hg))
  · exact mul_ne_zero (pow_ne_zero _ hμ) hg0
  · have htend : Filter.Tendsto (fun s : ℂ => μ * s + ν) (𝓝 z) (𝓝 (μ * z + ν)) := by
      have hc : Continuous (fun s : ℂ => μ * s + ν) := (continuous_const.mul continuous_id).add
        continuous_const
      simpa using hc.tendsto z
    filter_upwards [htend.eventually hfac] with s hs
    simp only [smul_eq_mul] at hs ⊢
    rw [hs, show μ * s + ν - (μ * z + ν) = μ * (s - z) by ring, mul_pow]
    ring

/-- The residue-filled germ of an entire function transforms by rescaling the local coordinate. -/
theorem fluxGerm_comp_affine {f : ℂ → ℂ} {μ ν z : ℂ} {n : ℕ} (hμ : μ ≠ 0)
    (hf : ∀ w, AnalyticAt ℂ f w) (h : analyticOrderAt f (μ * z + ν) = n) (x : ℂ) :
    fluxGerm (fun s : ℂ => f (μ * s + ν)) z x = fluxGerm f (μ * z + ν) (μ * x) := by
  have hord := analyticOrderAt_comp_affine hμ (hf _) h
  by_cases hx : x = 0
  · subst x
    rw [mul_zero, fluxGerm_zero, fluxGerm_zero, hord, h]
  · have hmx : μ * x ≠ 0 := mul_ne_zero hμ hx
    have hval : μ * (z + x) + ν = μ * z + ν + μ * x := by ring
    have hd : deriv (fun s : ℂ => f (μ * s + ν)) (z + x)
        = μ * deriv f (μ * z + ν + μ * x) := by
      have hbase : HasDerivAt f (deriv f (μ * (z + x) + ν)) (μ * (z + x) + ν) :=
        (hf _).differentiableAt.hasDerivAt
      have hinner : HasDerivAt (fun s : ℂ => μ * s + ν) μ (z + x) := by
        simpa using ((hasDerivAt_id (z + x)).const_mul μ).add_const ν
      have hcomp := hbase.comp (z + x) hinner
      rw [hval] at hcomp
      simpa [Function.comp_def, mul_comm] using hcomp.deriv
    rw [fluxGerm_of_ne_zero _ _ hx, fluxGerm_of_ne_zero _ _ hmx, hd, hval]
    ring

/-! ## Stability of the normalized logarithmic derivative under a flat perturbation -/

/-- **Flat-perturbation stability.**  If two germs that are units at the centre differ by a factor
`x^{K+1}`, then their `-x`-normalized logarithmic derivatives differ by the same flat factor times
an analytic function.  This is the exact statement behind "matching a finite jet of the function
matches the corresponding finite jet of its completed flux". -/
theorem exists_pow_mul_of_normalizedLogDeriv_sub {m n E : ℂ → ℂ} {K : ℕ}
    (hm : AnalyticAt ℂ m 0) (hn : AnalyticAt ℂ n 0) (hm0 : m 0 ≠ 0) (hn0 : n 0 ≠ 0)
    (hE : AnalyticAt ℂ E 0)
    (he : ∀ᶠ x in 𝓝 (0 : ℂ), m x - n x = x ^ (K + 1) * E x) :
    ∃ W : ℂ → ℂ, AnalyticAt ℂ W 0 ∧ ∀ᶠ x in 𝓝 (0 : ℂ),
      (-x * deriv m x / m x) - (-x * deriv n x / n x) = x ^ (K + 1) * W x := by
  classical
  refine ⟨fun x => -((((K : ℂ) + 1) * E x + x * deriv E x) * n x - x * deriv n x * E x)
      / (m x * n x), ?_, ?_⟩
  · refine AnalyticAt.div (AnalyticAt.neg ?_) (hm.mul hn) (mul_ne_zero hm0 hn0)
    exact (((analyticAt_const.mul hE).add (analyticAt_id.mul hE.deriv)).mul hn).sub
      ((analyticAt_id.mul hn.deriv).mul hE)
  · have hmne : ∀ᶠ x in 𝓝 (0 : ℂ), m x ≠ 0 := hm.continuousAt.eventually_ne hm0
    have hnne : ∀ᶠ x in 𝓝 (0 : ℂ), n x ≠ 0 := hn.continuousAt.eventually_ne hn0
    have hEan : ∀ᶠ x in 𝓝 (0 : ℂ), AnalyticAt ℂ E x := hE.eventually_analyticAt
    have hnan : ∀ᶠ x in 𝓝 (0 : ℂ), AnalyticAt ℂ n x := hn.eventually_analyticAt
    have hderive : ∀ᶠ x in 𝓝 (0 : ℂ),
        deriv (fun y : ℂ => m y - n y) x
          = ((K : ℂ) + 1) * x ^ K * E x + x ^ (K + 1) * deriv E x := by
      filter_upwards [he.eventually_nhds, hEan] with x hx hEx
      have hx' : (fun y : ℂ => m y - n y) =ᶠ[𝓝 x] fun y : ℂ => y ^ (K + 1) * E y := hx
      rw [hx'.deriv_eq]
      have hpow : HasDerivAt (fun y : ℂ => y ^ (K + 1)) (((K : ℂ) + 1) * x ^ K) x := by
        simpa using (hasDerivAt_id x).fun_pow (K + 1)
      have hmul := hpow.fun_mul hEx.differentiableAt.hasDerivAt
      rw [hmul.deriv]
    have hderivm : ∀ᶠ x in 𝓝 (0 : ℂ), deriv m x = deriv n x
        + (((K : ℂ) + 1) * x ^ K * E x + x ^ (K + 1) * deriv E x) := by
      filter_upwards [hderive, hm.eventually_analyticAt, hnan] with x hx hmx hnx
      have hsub : deriv (fun y : ℂ => m y - n y) x = deriv m x - deriv n x :=
        deriv_sub hmx.differentiableAt hnx.differentiableAt
      rw [hsub] at hx
      linear_combination hx
    filter_upwards [he, hmne, hnne, hderivm] with x hx hmx hnx hdx
    have hmval : m x = n x + x ^ (K + 1) * E x := by linear_combination hx
    have hnum : deriv m x * n x - deriv n x * m x
        = x ^ K * (((((K : ℂ) + 1) * E x + x * deriv E x) * n x - x * deriv n x * E x)) := by
      rw [hdx, hmval]
      ring
    have hLHS : (-x * deriv m x / m x) - (-x * deriv n x / n x)
        = -x * (deriv m x * n x - deriv n x * m x) / (m x * n x) := by
      field_simp
      ring
    rw [hLHS, hnum]
    field_simp
    ring

end GaloisForLFunctions.HTGeometry
