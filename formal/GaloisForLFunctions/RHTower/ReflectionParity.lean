/-
Reflection parity (MWM lane, Arc B base — task #114).

The first "constraint forces parity" theorem, from the functional equation alone, with
NO descent construction: if `f` is reflection-symmetric about `c` (`f(2c−s) = f(s)`)
then its vanishing order AT the fixed point is EVEN. Proof: peel `f = (s−c)^m·h`,
reflect, cancel the monomial off the puncture, and evaluate at `c`:
`h(c) = (−1)^m·h(c)` with `h(c) ≠ 0`.

Applied to ξ (via the banked `xi_one_sub`): the central multiplicity is even, the k = 1
rung clause holds at the FE fixed point, and w₁ is trivial there
(`xi_deckClass_central_sq_trivial`). The mechanism this names is RAMIFICATION: the
fixed point of the FE involution is exactly where the constraint sees parity. Off the
fixed locus the reflection is free — Davenport–Heilbronn (FE, simple off-line zeros)
shows FE alone CANNOT force off-line parity — so the Arc B hunt is for correspondences
whose fixed/ramified locus reaches off-line points (14-parity-stratum.md).

The generic theorem applies to every reflection-symmetric member of the measured pencil
— a family-wide central-parity anchor for the conservation program.
-/
import GaloisForLFunctions.RHTower.XiDeck

namespace RHTower

open Complex Filter Topology

/-- **The signed reflection-parity law.**  If `f` is analytic on `ℂ`, symmetric with a sign under the
reflection `s ↦ 2c − s` (`f(2c − s) = ε·f(s)`, `ε = ±1`), and has finite vanishing order at the fixed
point `c`, then `(−1)^{ord} = ε`.  The reflection sign is exactly the parity of the central order:
`ε = +1 ⟹` even order, `ε = −1 ⟹` odd order. -/
theorem neg_one_pow_orderAt_of_signed_reflection {f : ℂ → ℂ} {c ε : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hε : ε = 1 ∨ ε = -1)
    (hsym : ∀ s, f (2 * c - s) = ε * f s)
    (hne : analyticOrderAt f c ≠ ⊤) :
    (-1 : ℂ) ^ (analyticOrderAt f c).toNat = ε := by
  set m : ℕ := (analyticOrderAt f c).toNat with hm_def
  have hcoe : analyticOrderAt f c = (m : ℕ∞) := (ENat.coe_toNat hne).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ := exists_peel isOpen_univ hf (Set.mem_univ c) hcoe
  have h2cc : (2 * c - c : ℂ) = c := by ring
  have hεsq : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> ring
  -- off the puncture, the sign-reflected peel gives `h s = ε·(−1)^m·h(2c − s)`
  have key : ∀ᶠ s in 𝓝[≠] c, h s = ε * (-1 : ℂ) ^ m * h (2 * c - s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ c := hs
    have e1 : f s = (s - c) ^ m * h s := hfact s (Set.mem_univ s)
    have e2 : f (2 * c - s) = (2 * c - s - c) ^ m * h (2 * c - s) := hfact _ (Set.mem_univ _)
    have e4 : f (2 * c - s) = ε * f s := hsym s
    have hpow : ((s - c : ℂ)) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hs')
    have E : (-1 : ℂ) ^ m * (s - c) ^ m * h (2 * c - s) = ε * ((s - c) ^ m * h s) := by
      have hrw : f (2 * c - s) = (-1 : ℂ) ^ m * (s - c) ^ m * h (2 * c - s) := by
        rw [e2, show (2 * c - s - c : ℂ) = -(s - c) by ring, neg_pow]
      rw [← hrw, e4, e1]
    have hcancel : (-1 : ℂ) ^ m * h (2 * c - s) = ε * h s :=
      mul_left_cancel₀ hpow (by linear_combination E)
    linear_combination -ε * hcancel - h s * hεsq
  -- pass to the fixed point by continuity
  have hcont1 : Tendsto h (𝓝[≠] c) (𝓝 (h c)) :=
    ((hhan c (Set.mem_univ c)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hcont2 : Tendsto (fun s : ℂ => ε * (-1 : ℂ) ^ m * h (2 * c - s)) (𝓝[≠] c)
      (𝓝 (ε * (-1 : ℂ) ^ m * h c)) := by
    have hrefl : Tendsto (fun s : ℂ => 2 * c - s) (𝓝 c) (𝓝 (2 * c - c)) :=
      continuousAt_const.sub continuousAt_id
    rw [h2cc] at hrefl
    have hcomp : Tendsto (fun s : ℂ => h (2 * c - s)) (𝓝 c) (𝓝 (h c)) :=
      ((hhan c (Set.mem_univ c)).continuousAt.tendsto).comp hrefl
    exact (hcomp.const_mul _).mono_left nhdsWithin_le_nhds
  have heq : h c = ε * (-1 : ℂ) ^ m * h c := tendsto_nhds_unique (hcont1.congr' key) hcont2
  have hεm : ε * (-1 : ℂ) ^ m = 1 := by
    have h1 : ε * (-1 : ℂ) ^ m * h c = 1 * h c := by rw [one_mul, ← heq]
    exact mul_right_cancel₀ hh0 h1
  have hmul : ε * (ε * (-1 : ℂ) ^ m) = ε * 1 := congrArg (fun z => ε * z) hεm
  rwa [← mul_assoc, hεsq, one_mul, mul_one] at hmul

/-- **Reflection forces even order at the fixed point.** If `f` is analytic on `ℂ`,
symmetric under the reflection `s ↦ 2c − s`, and has finite vanishing order at the
fixed point `c`, that order is even. -/
theorem analyticOrderAt_even_of_reflection {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hsym : ∀ s, f (2 * c - s) = f s)
    (hne : analyticOrderAt f c ≠ ⊤) :
    Even (analyticOrderAt f c).toNat := by
  have h := neg_one_pow_orderAt_of_signed_reflection hf (Or.inl rfl)
    (fun s => by rw [hsym s]; ring) hne
  rcases Nat.even_or_odd (analyticOrderAt f c).toNat with he | ho
  · exact he
  · rw [ho.neg_one_pow] at h; norm_num at h
/-- **The signed reflection-parity law, germ form.**  Only the germ at `c` is needed: if `f` is
analytic at `c`, locally sign-symmetric under `s ↦ 2c − s` (`f(2c − s) = ε·f(s)` near `c`, `ε = ±1`),
and has finite order at `c`, then `(−1)^{ord} = ε`.  This is the form consumed by carriers analytic
only on a strip neighbourhood of the fixed point. -/
theorem neg_one_pow_orderAt_of_signed_reflection_eventually {f : ℂ → ℂ} {c ε : ℂ}
    (hf : AnalyticAt ℂ f c) (hε : ε = 1 ∨ ε = -1)
    (hsym : ∀ᶠ s in 𝓝 c, f (2 * c - s) = ε * f s)
    (hne : analyticOrderAt f c ≠ ⊤) :
    (-1 : ℂ) ^ (analyticOrderAt f c).toNat = ε := by
  set m : ℕ := (analyticOrderAt f c).toNat with hm_def
  have hcoe : (m : ℕ∞) = analyticOrderAt f c := ENat.coe_toNat hne
  obtain ⟨p, hp, hp0, hfact⟩ := (hf.analyticOrderAt_eq_natCast).mp hcoe.symm
  have h2cc : (2 * c - c : ℂ) = c := by ring
  have hεsq : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> ring
  have hrefl_nhds : Tendsto (fun s : ℂ => 2 * c - s) (𝓝 c) (𝓝 c) := by
    have h := (continuousAt_const (x := c) (y := 2 * c)).sub continuousAt_id
    simpa [h2cc] using h.tendsto
  have hrefl_within : Tendsto (fun s : ℂ => 2 * c - s) (𝓝[≠] c) (𝓝 c) :=
    hrefl_nhds.mono_left nhdsWithin_le_nhds
  have hfact_ref : ∀ᶠ s in 𝓝[≠] c, f (2 * c - s) = (2 * c - s - c) ^ m * p (2 * c - s) := by
    simpa [smul_eq_mul] using hrefl_within.eventually hfact
  have hfact_self : ∀ᶠ s in 𝓝[≠] c, f s = (s - c) ^ m * p s := by
    simpa [smul_eq_mul] using hfact.filter_mono nhdsWithin_le_nhds
  have hsym_within : ∀ᶠ s in 𝓝[≠] c, f (2 * c - s) = ε * f s :=
    hsym.filter_mono nhdsWithin_le_nhds
  have key : ∀ᶠ s in 𝓝[≠] c, p s = ε * (-1 : ℂ) ^ m * p (2 * c - s) := by
    filter_upwards [self_mem_nhdsWithin, hfact_self, hfact_ref, hsym_within] with
      s hs hs1 hs2 hsyms
    have hs' : s ≠ c := hs
    have hpow : (s - c) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hs')
    have E : (-1 : ℂ) ^ m * (s - c) ^ m * p (2 * c - s) = ε * ((s - c) ^ m * p s) := by
      have hrw : f (2 * c - s) = (-1 : ℂ) ^ m * (s - c) ^ m * p (2 * c - s) := by
        rw [hs2, show (2 * c - s - c : ℂ) = -(s - c) by ring, neg_pow]
      rw [← hrw, hsyms, hs1]
    have hcancel : (-1 : ℂ) ^ m * p (2 * c - s) = ε * p s :=
      mul_left_cancel₀ hpow (by linear_combination E)
    linear_combination -ε * hcancel - p s * hεsq
  have hcont1 : Tendsto p (𝓝[≠] c) (𝓝 (p c)) :=
    hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hcont2 : Tendsto (fun s : ℂ => ε * (-1 : ℂ) ^ m * p (2 * c - s)) (𝓝[≠] c)
      (𝓝 (ε * (-1 : ℂ) ^ m * p c)) := by
    have hcomp : Tendsto (fun s : ℂ => p (2 * c - s)) (𝓝 c) (𝓝 (p c)) :=
      hp.continuousAt.tendsto.comp hrefl_nhds
    exact (hcomp.const_mul _).mono_left nhdsWithin_le_nhds
  have heq : p c = ε * (-1 : ℂ) ^ m * p c := tendsto_nhds_unique (hcont1.congr' key) hcont2
  have hεm : ε * (-1 : ℂ) ^ m = 1 := by
    have h1 : ε * (-1 : ℂ) ^ m * p c = 1 * p c := by rw [one_mul, ← heq]
    exact mul_right_cancel₀ hp0 h1
  have hmul : ε * (ε * (-1 : ℂ) ^ m) = ε * 1 := congrArg (fun z => ε * z) hεm
  rwa [← mul_assoc, hεsq, one_mul, mul_one] at hmul

/-- **Local reflection forces even order at the fixed point.**  The global theorem
`analyticOrderAt_even_of_reflection` only needs the germ: if `f` is analytic at `c`,
locally symmetric under `s ↦ 2c-s` near `c`, and has finite order at `c`, then that
order is even.  This is the form consumed by completed finite carriers that are analytic
only on a strip neighbourhood. -/
theorem analyticOrderAt_even_of_reflection_eventually {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c)
    (hsym : ∀ᶠ s in 𝓝 c, f (2 * c - s) = f s)
    (hne : analyticOrderAt f c ≠ ⊤) :
    Even (analyticOrderAt f c).toNat := by
  have h := neg_one_pow_orderAt_of_signed_reflection_eventually hf (Or.inl rfl)
    (hsym.mono fun s hs => by rw [hs]; ring) hne
  rcases Nat.even_or_odd (analyticOrderAt f c).toNat with he | ho
  · exact he
  · rw [ho.neg_one_pow] at h; norm_num at h
/-- **The central multiplicity of ξ is even** — the functional equation sees parity at
its fixed point. -/
theorem xi_central_order_even : Even ((analyticOrderAt xi (1 / 2 : ℂ)).toNat) := by
  refine analyticOrderAt_even_of_reflection xi_analyticOnNhd_univ (fun s => ?_)
    (xi_orderAt_ne_top _)
  have e : (2 * (1 / 2 : ℂ) - s) = 1 - s := by ring
  rw [e, xi_one_sub]

/-- The k = 1 rung clause holds at the FE fixed point: `2 ∣ ord_{1/2}(ξ)` in `ℕ∞`. -/
theorem xi_central_ladder_two : ((2 : ℕ) : ℕ∞) ∣ analyticOrderAt xi (1 / 2 : ℂ) := by
  obtain ⟨k, hk⟩ := xi_central_order_even
  have hcoe : analyticOrderAt xi (1 / 2 : ℂ) =
      (((analyticOrderAt xi (1 / 2 : ℂ)).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_orderAt_ne_top _)).symm
  rw [hcoe, hk]
  exact ⟨(k : ℕ∞), by push_cast; ring⟩

/-- **w₁ is trivial at the FE fixed point**: any local square roots of ξ on the charts
of a small ball at `1/2` have deck class `1` — the first constraint-forces-parity
instance, from the functional equation alone. -/
theorem xi_deckClass_central_sq_trivial :
    ∃ R₀ > 0, ∀ {R : ℝ}, 0 < R → R ≤ R₀ → ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR (1 / 2 : ℂ) R) →
      AnalyticOnNhd ℂ G₂ (chartL (1 / 2 : ℂ) R) →
      (∀ z ∈ chartR (1 / 2 : ℂ) R, G₁ z ^ 2 = xi z) →
      (∀ z ∈ chartL (1 / 2 : ℂ) R, G₂ z ^ 2 = xi z) →
      deckClass G₁ G₂ ((1 / 2 : ℂ) + ((R / 2 : ℝ) : ℂ) * I)
        ((1 / 2 : ℂ) - ((R / 2 : ℝ) : ℂ) * I) = 1 := by
  obtain ⟨R₀, hR₀, hiff⟩ := xi_deckClass_eq_one_iff_ladder_dvd (1 / 2 : ℂ) 1
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle G₁ G₂ hG₁ hG₂ hp₁ hp₂
  rw [hiff hR hRle hG₁ hG₂ (by simpa only [pow_one] using hp₁)
    (by simpa only [pow_one] using hp₂)]
  simpa only [pow_one] using xi_central_ladder_two

end RHTower
