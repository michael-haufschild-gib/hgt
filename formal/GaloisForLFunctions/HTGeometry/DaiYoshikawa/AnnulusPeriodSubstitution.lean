import GaloisForLFunctions.HTGeometry.DaiYoshikawa.AnnulusLaurentPairing

/-!
# The vanishing-cycle substitution `y = t/x`

Near a node of the singular fibre Dai–Yoshikawa, *Degeneration of Riemann surfaces and small
eigenvalues of the Laplacian* (arXiv:2509.06151v2), write the fibre as `xy = t`, so that a
holomorphic function `α(x,y)` on the bidisc restricts to the annulus `|t| ≤ |x| ≤ 1` as
`α(x, t/x)`.  Expanding `α` in its Taylor series turns this into a Laurent expansion in `x`,

```text
α(x, t/x) = Σ_k c_k(t) x^k ,      c_k(t) = Σ_{m−n=k} a_{mn} t^n .
```

This file proves that substitution identity for polynomial `α` and reads off the annulus period
integral through `setIntegral_laurentPairing`: the only divergent contribution as `t → 0` is the
`k = 0` term, whose coefficient `c₀(t)` tends to the value `α(0,0)` — the residue that appears in
(5.3).
-/

open MeasureTheory Set Real Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

open _root_.HTGeometry (deningerAnnulus)

/-- The Laurent coefficient at exponent `k` of `α(x, t/x)`, for `α` with coefficient family `a`
supported on `S`. -/
noncomputable def substCoeff (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) (k : ℤ) (t : ℂ) : ℂ :=
  ∑ p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = k, a p * t ^ p.2

/-- Outside the set of realised exponents the Laurent coefficient vanishes. -/
theorem substCoeff_eq_zero_of_notMem {S : Finset (ℕ × ℕ)} {a : ℕ × ℕ → ℂ} {k : ℤ} (t : ℂ)
    (hk : k ∉ S.image fun p => (p.1 : ℤ) - (p.2 : ℤ)) : substCoeff S a k t = 0 := by
  rw [substCoeff, Finset.sum_eq_zero]
  intro p hp
  rw [Finset.mem_filter] at hp
  exact absurd (Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩) hk

/-- **The substitution identity.**

For `x ≠ 0`, the restriction of a polynomial `α(x,y) = Σ a_{mn} x^m y^n` to the fibre `xy = t` is the
Laurent polynomial with coefficients `substCoeff`. -/
theorem sum_bipoly_subst_eq_laurentPoly (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ)
    {s : Finset ℤ} (hs : (S.image fun p => (p.1 : ℤ) - (p.2 : ℤ)) ⊆ s)
    (t : ℂ) {x : ℂ} (hx : x ≠ 0) :
    (∑ p ∈ S, a p * x ^ p.1 * (t / x) ^ p.2)
      = laurentPoly s (fun k => substCoeff S a k t) x := by
  have hterm : ∀ p ∈ S,
      a p * x ^ p.1 * (t / x) ^ p.2 = (a p * t ^ p.2) * x ^ ((p.1 : ℤ) - (p.2 : ℤ)) := by
    intro p _
    rw [div_pow, zpow_sub₀ hx, zpow_natCast, zpow_natCast]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hmaps : ∀ p ∈ S, ((p.1 : ℤ) - (p.2 : ℤ)) ∈ s := fun p hp =>
    hs (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun p => (a p * t ^ p.2) * x ^ ((p.1 : ℤ) - (p.2 : ℤ)))]
  rw [laurentPoly]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [substCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [hp.2]

/-- The `k = 0` coefficient at `t = 0` is the value `α(0,0)`. -/
theorem substCoeff_zero_zero (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) :
    substCoeff S a 0 0 = if ((0, 0) : ℕ × ℕ) ∈ S then a (0, 0) else 0 := by
  have hfib : ∀ p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = 0, p.2 = 0 → p = ((0, 0) : ℕ × ℕ) := by
    intro p hp hp2
    rw [Finset.mem_filter] at hp
    have hp1 : (p.1 : ℤ) = 0 := by
      have h := hp.2
      rw [hp2] at h
      simpa using h
    exact Prod.ext (by exact_mod_cast hp1) hp2
  rw [substCoeff]
  by_cases h00 : ((0, 0) : ℕ × ℕ) ∈ S
  · rw [if_pos h00]
    have hmem : ((0, 0) : ℕ × ℕ) ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = 0 :=
      Finset.mem_filter.mpr ⟨h00, by norm_num⟩
    have hzero : ∀ p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = 0,
        p ≠ ((0, 0) : ℕ × ℕ) → a p * (0 : ℂ) ^ p.2 = 0 := by
      intro p hp hne
      have hp2 : p.2 ≠ 0 := fun hz => hne (hfib p hp hz)
      rw [zero_pow hp2, mul_zero]
    rw [Finset.sum_eq_single_of_mem _ hmem hzero]
    norm_num
  · rw [if_neg h00]
    refine Finset.sum_eq_zero fun p hp => ?_
    by_cases hp2 : p.2 = 0
    · exact absurd (by rw [← hfib p hp hp2]; exact (Finset.mem_filter.mp hp).1) h00
    · rw [zero_pow hp2, mul_zero]

/-- The `k = 0` coefficient is continuous in `t`, so it tends to `α(0,0)`. -/
theorem tendsto_substCoeff_zero (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) :
    Tendsto (fun t => substCoeff S a 0 t) (𝓝 0) (𝓝 (substCoeff S a 0 0)) := by
  have hcont : Continuous fun t : ℂ => substCoeff S a 0 t := by
    simp only [substCoeff]
    exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_pow _)
  exact hcont.tendsto 0

/-- **The annulus period integral of a substituted pair.**

Combining the substitution identity with `setIntegral_laurentPairing`: the period integral over the
vanishing annulus `|t| < |x| < 1` splits into the logarithmically divergent `k = 0` term and a sum
of bounded terms. -/
theorem setIntegral_substPairing (S T : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℂ)
    {s : Finset ℤ}
    (hS : (S.image fun p => (p.1 : ℤ) - (p.2 : ℤ)) ⊆ s)
    (hT : (T.image fun p => (p.1 : ℤ) - (p.2 : ℤ)) ⊆ s)
    {t : ℂ} (ht : 0 < ‖t‖) (ht1 : ‖t‖ ≤ 1) :
    (∫ w in deningerAnnulus ‖t‖ 1,
        (∑ p ∈ S, a p * w ^ p.1 * (t / w) ^ p.2)
          * (starRingEnd ℂ) (∑ q ∈ T, b q * w ^ q.1 * (t / w) ^ q.2) / ((‖w‖ : ℂ) ^ 2))
      = ∑ k ∈ s, substCoeff S a k t * (starRingEnd ℂ) (substCoeff T b k t)
          * (if k = 0 then (2 * π * Real.log (1 / ‖t‖) : ℂ)
             else 2 * π * ((1 ^ (2 * k) - (‖t‖ : ℝ) ^ (2 * k)) / (2 * k))) := by
  have hcongr : ∀ w ∈ deningerAnnulus ‖t‖ 1,
      (∑ p ∈ S, a p * w ^ p.1 * (t / w) ^ p.2)
          * (starRingEnd ℂ) (∑ q ∈ T, b q * w ^ q.1 * (t / w) ^ q.2) / ((‖w‖ : ℂ) ^ 2)
        = laurentPairing s (fun k => substCoeff S a k t) (fun k => substCoeff T b k t) w := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro hz
      have h1 : ‖t‖ < ‖w‖ := hw.1
      rw [hz, norm_zero] at h1
      linarith
    rw [laurentPairing, sum_bipoly_subst_eq_laurentPoly S a hS t hw0,
      sum_bipoly_subst_eq_laurentPoly T b hT t hw0]
  have hAmeas : MeasurableSet (deningerAnnulus ‖t‖ 1) := by
    have hpre : deningerAnnulus ‖t‖ 1 = (fun w : ℂ => ‖w‖) ⁻¹' Set.Ioo ‖t‖ 1 := by
      ext w
      simp [_root_.HTGeometry.deningerAnnulus, Set.mem_Ioo]
    rw [hpre]
    exact (isOpen_Ioo.preimage continuous_norm).measurableSet
  rw [MeasureTheory.setIntegral_congr_fun hAmeas hcongr]
  exact setIntegral_laurentPairing s _ _ ht ht1

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
