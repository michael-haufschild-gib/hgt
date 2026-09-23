import GaloisForLFunctions.RHTower.ProlateWKBSubsolution
import GaloisForLFunctions.RHTower.ProlateForbiddenEndpoint

/-!
# The WKB-anchored Riccati barrier

The radial barrier `c sqrt(1-s) y / sqrt(1-y²)` is a Riccati subsolution only for `c s ≥ 4`, and it
exceeds the WKB profile by a quantity whose mass against the WKB measure is a logarithm of the
bandwidth.  Both defects disappear for the barrier anchored on the profile itself,

```text
U(y) = prolateWKB c χ y + 1/y + 1/(1-y) ,
```

whose Riccati defect collapses to a single elementary inequality.  Writing `A = χ + c²y²` and
`W = prolateWKB c χ y`, so that `W² = A/(1-y²)`, the two added terms satisfy

```text
(1/y + 1/(1-y))' ≤ (1/y + 1/(1-y))²      identically on `(0,1)` ,
```

so the whole requirement reduces to `W' ≤ (2/y + 2y/(1-y²)) W`, and after clearing denominators to

```text
(2c²y(1-y²) + 2yA)·y ≤ 4A     ⟺     0 ≤ χ(2 - y²) + c²y² ,
```

which for `χ = -s c²` is `y²(1+s) ≥ 2s` — satisfied on the whole band beyond `y = sqrt(2s)`, at
*every* separation.  So the anchored barrier dominates the logarithmic derivative of a positive mode
past the doubled turning point with no lower bound on `c s` at all, and it exceeds the WKB profile by
only `1/y + 1/(1-y)`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The Riccati barrier anchored on the WKB profile. -/
def prolateAnchoredBarrier (c χ : ℝ) (y : ℝ) : ℝ :=
  prolateWKB c χ y + 1 / y + 1 / (1 - y)

/-- Its derivative. -/
def prolateAnchoredBarrierDeriv (c χ : ℝ) (y : ℝ) : ℝ :=
  (2 * c ^ (2 : ℕ) * y * (1 - y ^ (2 : ℕ)) + 2 * y * (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ))) / (1 - y ^ (2 : ℕ)) ^ (2 : ℕ)
      / (2 * prolateWKB c χ y)
    + (-(1 / y ^ (2 : ℕ)) + 1 / (1 - y) ^ (2 : ℕ))

theorem hasDerivAt_prolateAnchoredBarrier {c χ y : ℝ} (hy0 : 0 < y) (hy1 : y < 1)
    (hR : 0 < (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ))) :
    HasDerivAt (prolateAnchoredBarrier c χ) (prolateAnchoredBarrierDeriv c χ y) y := by
  have hw : (1 : ℝ) - y ^ (2 : ℕ) ≠ 0 := by nlinarith
  have h1 := hasDerivAt_prolateWKB (c := c) (χ := χ) hw hR
  have h2 : HasDerivAt (fun t : ℝ => 1 / t) (-(1 / y ^ (2 : ℕ))) y := by
    have h := (hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_id y) hy0.ne'
    refine h.congr_deriv ?_
    simp only [id_eq]
    field_simp
    ring
  have h3 : HasDerivAt (fun t : ℝ => 1 / (1 - t)) (1 / (1 - y) ^ (2 : ℕ)) y := by
    have hb : HasDerivAt (fun t : ℝ => 1 - t) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
    have hne : (1 : ℝ) - y ≠ 0 := by linarith
    have h := (hasDerivAt_const y (1 : ℝ)).div hb hne
    refine h.congr_deriv ?_
    field_simp
    ring
  have h := (h1.add h2).add h3
  refine h.congr_deriv ?_
  rw [prolateAnchoredBarrierDeriv]
  ring

/-- **The anchored barrier is a Riccati subsolution past the doubled turning point.**  No lower
bound on `c s` is needed: the condition is `0 ≤ χ(2 - y²) + c²y²`, which for `χ = -s c²` reads
`y²(1+s) ≥ 2s`. -/
theorem prolateAnchoredBarrier_subsolution {c χ y : ℝ} (hy0 : 0 < y) (hy1 : y < 1)
    (hQ : 0 < χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) (hcond : 0 ≤ χ * (2 - y ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ)) :
    prolateAnchoredBarrierDeriv c χ y
      ≤ prolateAnchoredBarrier c χ y ^ (2 : ℕ)
        + (2 * y / (1 - y ^ (2 : ℕ))) * prolateAnchoredBarrier c χ y
        - (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)) := by
  have hp : (0 : ℝ) < 1 - y ^ (2 : ℕ) := by nlinarith
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have hR : 0 < (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)) := div_pos hQ hp
  set W : ℝ := prolateWKB c χ y with hWdef
  have hW : 0 < W := by
    rw [hWdef, prolateWKB]
    exact Real.sqrt_pos.2 hR
  have hWsq : W ^ (2 : ℕ) = (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)) := by
    rw [hWdef, prolateWKB]
    exact Real.sq_sqrt hR.le
  set w : ℝ := 1 / y + 1 / (1 - y) with hwdef
  have hwpos : 0 < w := by
    rw [hwdef]
    positivity
  -- the added terms are self-dominating
  have hwsq : -(1 / y ^ (2 : ℕ)) + 1 / (1 - y) ^ (2 : ℕ) ≤ w ^ (2 : ℕ) := by
    have hval : w ^ (2 : ℕ) = 1 / y ^ (2 : ℕ) + 2 / (y * (1 - y)) + 1 / (1 - y) ^ (2 : ℕ) := by
      rw [hwdef]
      field_simp
      ring
    have hcross : (0 : ℝ) < 2 / (y * (1 - y)) := by positivity
    have hy2 : (0 : ℝ) < 1 / y ^ (2 : ℕ) := by positivity
    rw [hval]
    linarith
  -- the profile part
  have hnum : (2 * c ^ (2 : ℕ) * y * (1 - y ^ (2 : ℕ)) + 2 * y * (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ))) * y
      ≤ 4 * (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) := by nlinarith [hcond]
  have hkey : (2 * c ^ (2 : ℕ) * y * (1 - y ^ (2 : ℕ)) + 2 * y * (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ))) / (1 - y ^ (2 : ℕ)) ^ (2 : ℕ)
      / (2 * W)
      ≤ 2 * W / y + (2 * y / (1 - y ^ (2 : ℕ))) * W := by
    rw [div_div, div_le_iff₀ (by positivity : (0 : ℝ) < (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) * (2 * W))]
    have hexp : (2 * W / y + (2 * y / (1 - y ^ (2 : ℕ))) * W) * ((1 - y ^ (2 : ℕ)) ^ (2 : ℕ) * (2 * W))
        = 4 * W ^ (2 : ℕ) * (1 - y ^ (2 : ℕ)) ^ (2 : ℕ) * (1 / y + y / (1 - y ^ (2 : ℕ))) := by ring
    rw [hexp, hWsq]
    have hval : 4 * ((χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ))) * (1 - y ^ (2 : ℕ)) ^ (2 : ℕ)
        * (1 / y + y / (1 - y ^ (2 : ℕ))) = 4 * (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / y := by
      field_simp
      ring
    rw [hval, le_div_iff₀ hy0]
    linarith [hnum]
  -- assemble
  have hbw : (0 : ℝ) ≤ (2 * y / (1 - y ^ (2 : ℕ))) * w := by positivity
  have hWw : 2 * W / y ≤ 2 * W * w := by
    have h1 : 1 / y ≤ w := by
      rw [hwdef]
      have : (0 : ℝ) < 1 / (1 - y) := by positivity
      linarith
    have h2 : 2 * W / y = 2 * W * (1 / y) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hexpand : prolateAnchoredBarrier c χ y ^ (2 : ℕ)
      + (2 * y / (1 - y ^ (2 : ℕ))) * prolateAnchoredBarrier c χ y
      - (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ))
      = 2 * W * w + w ^ (2 : ℕ) + (2 * y / (1 - y ^ (2 : ℕ))) * W + (2 * y / (1 - y ^ (2 : ℕ))) * w := by
    rw [prolateAnchoredBarrier, ← hWsq, hwdef]
    ring
  rw [hexpand, prolateAnchoredBarrierDeriv, ← hWdef]
  linarith [hkey, hwsq, hbw, hWw]


theorem continuousOn_prolateAnchoredBarrier {c χ a b : ℝ}
    (hpne : ∀ y ∈ Icc a b, (1 : ℝ) - y ^ (2 : ℕ) ≠ 0)
    (hyne : ∀ y ∈ Icc a b, y ≠ 0) (hy1ne : ∀ y ∈ Icc a b, (1 : ℝ) - y ≠ 0) :
    ContinuousOn (prolateAnchoredBarrier c χ) (Icc a b) := by
  have h1 : ContinuousOn (fun y : ℝ => 1 / y) (Icc a b) :=
    continuousOn_const.div continuousOn_id hyne
  have h2 : ContinuousOn (fun y : ℝ => 1 / (1 - y)) (Icc a b) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id) hy1ne
  exact ((continuousOn_prolateWKB hpne).add h1).add h2

/-- **The anchored barrier dominates the logarithmic derivative.**  Backward Riccati comparison,
valid at every separation past the doubled turning point. -/
theorem prolateLogDeriv_le_anchoredBarrier {c χ a b : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < 1)
    (hQ : ∀ y ∈ Icc a b, 0 < χ + c ^ (2 : ℕ) * y ^ (2 : ℕ))
    (hcond : ∀ y ∈ Icc a b, 0 ≤ χ * (2 - y ^ (2 : ℕ)) + c ^ (2 : ℕ) * y ^ (2 : ℕ))
    (hpos : ∀ y ∈ Icc a b, 0 < Φ y)
    (hinit : prolateLogDeriv Φ b ≤ prolateAnchoredBarrier c χ b) :
    ∀ y ∈ Icc a b, prolateLogDeriv Φ y ≤ prolateAnchoredBarrier c χ y := by
  have hp : ∀ y ∈ Icc a b, (0 : ℝ) < 1 - y ^ (2 : ℕ) := by
    intro y hy
    nlinarith [ha, hy.1, hy.2, hb]
  refine HTGeometry.riccati_le_of_le_of_subsolution
    (u := prolateLogDeriv Φ) (U := prolateAnchoredBarrier c χ)
    (u' := fun y => prolateLogDeriv Φ y ^ (2 : ℕ)
      + (2 * y / (1 - y ^ (2 : ℕ))) * prolateLogDeriv Φ y - (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)))
    (U' := prolateAnchoredBarrierDeriv c χ)
    (bcoef := fun y => 2 * y / (1 - y ^ (2 : ℕ)))
    (q := fun y => (χ + c ^ (2 : ℕ) * y ^ (2 : ℕ)) / (1 - y ^ (2 : ℕ)))
    hab (continuousOn_prolateLogDeriv hsm fun y hy => ne_of_gt (hpos y hy))
    (continuousOn_prolateAnchoredBarrier (fun y hy => (hp y hy).ne')
      (fun y hy => by have := hy.1; linarith)
      (fun y hy => by have h1 : y ≤ b := hy.2; linarith)) ?_ ?_ ?_ ?_ ?_ hinit
  · intro y hy
    have hymem : y ∈ Icc a b := ⟨hy.1.le, hy.2.le⟩
    have hyband : y ∈ Ioo (-1 : ℝ) 1 := by
      constructor <;> nlinarith [ha, hy.1, hy.2, hb]
    exact hasDerivAt_prolateLogDeriv hsm heig hyband (ne_of_gt (hpos y hymem))
  · intro y hy
    have hymem : y ∈ Icc a b := ⟨hy.1.le, hy.2.le⟩
    have hy0 : (0 : ℝ) < y := lt_trans ha hy.1
    have hy1 : y < 1 := lt_trans hy.2 hb
    exact hasDerivAt_prolateAnchoredBarrier hy0 hy1 (div_pos (hQ y hymem) (hp y hymem))
  · have hnum : ContinuousOn (fun y : ℝ => 2 * y) (Icc a b) := by fun_prop
    have hden : ContinuousOn (fun y : ℝ => 1 - y ^ (2 : ℕ)) (Icc a b) := by fun_prop
    exact hnum.div hden fun y hy => ne_of_gt (hp y hy)
  · intro _ _
    rfl
  · intro y hy
    have hymem : y ∈ Icc a b := ⟨hy.1.le, hy.2.le⟩
    have hy0 : (0 : ℝ) < y := lt_trans ha hy.1
    have hy1 : y < 1 := lt_trans hy.2 hb
    exact prolateAnchoredBarrier_subsolution hy0 hy1 (hQ y hymem) (hcond y hymem)


/-- Close enough to the endpoint the anchored barrier dominates the logarithmic derivative, so the
backward comparison has its terminal inequality automatically. -/
theorem eventually_prolateLogDeriv_le_anchoredBarrier_at_one {c s : ℝ} {Φ : ℝ → ℝ}
    (hc : 0 < c) (hs : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hΦ1 : Φ 1 = 1) :
    ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1),
      prolateLogDeriv Φ b ≤ prolateAnchoredBarrier c (-(s * c ^ (2 : ℕ))) b := by
  have hbase := eventually_prolateLogDeriv_le_prolateWKB_radial_at_one hc hs hsm hΦ1
  have h0 : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1), (0 : ℝ) < b :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num))
  have hlt : ∀ᶠ b : ℝ in nhdsWithin 1 (Iio 1), b < 1 := self_mem_nhdsWithin
  filter_upwards [hbase, h0, hlt] with b hb hb0 hb1
  have h1 : (0 : ℝ) < 1 / b := by positivity
  have h2 : (0 : ℝ) < 1 / (1 - b) := by
    have : (0 : ℝ) < 1 - b := by linarith
    positivity
  rw [prolateAnchoredBarrier]
  linarith

end GaloisForLFunctions.RHTower

end
