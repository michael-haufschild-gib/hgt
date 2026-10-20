import GaloisForLFunctions.RHTower.ZetaPartialSumIsolatedZeroHeightsAndUniformPairReturns
import GaloisForLFunctions.RHTower.Sieve.SubCriticalPowerSum

/-!
# Size of zeta on discs at typical heights, and precompactness of the typical orbit

Write `head_M(s) = Σ_{n ≤ M} n^{-s}`, `σ₀ = Re c − 2r`, and `K = (1 + r/(1 − (Re c + 2r)))²`.

**Explicit bounds.**  On `Re w ≥ σ₀` the head is at most `A_M = M^{1−σ₀}/(1−σ₀) + 1`
(`norm_edPoly_one_Icc_le_of_re_ge`), and the Carlson tail mass is at most
`(2σ₀/(2σ₀−1)) (M+1)^{1−2σ₀}` (`zetaCoefficientTailMass_le`).  Hence the bad heights of the
disc-uniform Carlson tail law have density at most `28 K (2σ₀/(2σ₀−1)) (M+1)^{1−2σ₀}/ε² + κ`
(`eventually_volume_discTailBadSet_le_explicit`).

**Power-law tail of `sup |ζ|` on discs** (`eventually_volume_discZetaLargeSet_le`).  Heights at
which `|ζ| ≥ 2A_M` somewhere on `closedBall c r + iτ` have asymptotic density at most
`28 K (2σ₀/(2σ₀−1)) (1−σ₀)²/M + κ`.  Since `A_M ≍ M^{1−σ₀}`, the density of heights where
`sup_disc |ζ| ≥ B` decays like `B^{-1/(1−σ₀)}`, uniformly in the window length `T`: at a height
where `ζ` is large on the disc, the Carlson tail `ζ − head_M` must already be large for the
`M` at which the head is bounded by `B/2`.

**Precompactness of the typical orbit** (`exists_finite_headTranslates_cover_typicalHeights`).
The phases `n^{-iτ}`, `n ≤ M`, have a totally bounded orbit (Bochner), so finitely many head
translates `head_M(· + is)`, `s ∈ S`, approximate every head translate on the disc; at tail-good
heights they approximate `ζ(· + iτ)` itself.  Thus for every `ε, δ` the orbit `τ ↦ ζ(· + iτ)|_disc`
lies within `ε` of a finite set of model functions at all heights outside a set of density `≤ δ`.
-/

open Complex Filter Topology MeasureTheory Set Metric
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

noncomputable section

namespace RHTower

/-! ## 1. Explicit head and tail-mass bounds -/

/-- On `Re w ≥ σ₀`, `|head_M(w)| ≤ M^{1−σ₀}/(1−σ₀) + 1`. -/
theorem norm_edPoly_one_Icc_le_of_re_ge {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1) (M : ℕ)
    {w : ℂ} (hw : σ₀ ≤ w.re) :
    ‖edPoly (fun _ => 1) (Finset.Icc 1 M) w‖ ≤ (M : ℝ) ^ (1 - σ₀) / (1 - σ₀) + 1 := by
  unfold edPoly
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans
    (Sieve.sum_rpow_neg_subcritical_le hσ₀ hσ₁ M))
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)

/-- A nonpositive real power is antitone in the base. -/
theorem rpow_le_rpow_of_le_of_nonpos {x y e : ℝ} (hx : 0 < x) (hxy : x ≤ y) (he : e ≤ 0) :
    y ^ e ≤ x ^ e := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [← neg_neg e, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy (by linarith))

/-- The Carlson tail mass is at most `(2σ/(2σ−1)) (M+1)^{1−2σ}`. -/
theorem zetaCoefficientTailMass_le (M : ℕ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    zetaCoefficientTailMass M σ ≤ 2 * σ / (2 * σ - 1) * ((M : ℝ) + 1) ^ (1 - 2 * σ) := by
  classical
  unfold zetaCoefficientTailMass
  have hc : 1 < 2 * σ := by linarith
  refine (summable_zetaCoefficientTail M hσ).tsum_le_of_sum_le fun s => ?_
  have hfilter : (∑ n ∈ s, if n ≤ M then (0 : ℝ) else (n : ℝ) ^ (-2 * σ)) =
      ∑ n ∈ s.filter (fun n => ¬ n ≤ M), (n : ℝ) ^ (-(2 * σ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n ≤ M
    · simp [h]
    · simp [h, neg_mul]
  rw [hfilter]
  have hsub : s.filter (fun n => ¬ n ≤ M) ⊆ Finset.Icc (M + 1) (s.sup id) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_Icc.mpr ⟨by omega, Finset.le_sup (f := id) hn.1⟩
  calc (∑ n ∈ s.filter (fun n => ¬ n ≤ M), (n : ℝ) ^ (-(2 * σ)))
      ≤ ∑ n ∈ Finset.Icc (M + 1) (s.sup id), (n : ℝ) ^ (-(2 * σ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ 2 * σ / (2 * σ - 1) * ((M + 1 : ℕ) : ℝ) ^ (1 - 2 * σ) :=
        Sieve.sum_rpow_neg_tail_le hc (by omega)
    _ = 2 * σ / (2 * σ - 1) * ((M : ℝ) + 1) ^ (1 - 2 * σ) := by push_cast; ring

/-- Fully explicit fixed-`M` density of the bad heights. -/
theorem eventually_volume_discTailBadSet_le_explicit (M : ℕ) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε : ℝ} (hε : 0 < ε) {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, volume (discTailBadSet M c r ε ∩ Icc 0 T) ≤
      ENNReal.ofReal ((28 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 / ε ^ 2 *
        (2 * (c.re - 2 * r) / (2 * (c.re - 2 * r) - 1) *
          ((M : ℝ) + 1) ^ (1 - 2 * (c.re - 2 * r))) + κ) * T) := by
  filter_upwards [eventually_volume_discTailBadSet_le_tailMass M hr h0 h1 hε hκ,
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have hL : 0 < 1 - (c.re + 2 * r) := by linarith
  have hK0 : 0 ≤ 28 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 / ε ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (zetaCoefficientTailMass_le M h0) hK0
  exact mul_le_mul_of_nonneg_right (by linarith) hT0

/-! ## 2. Power-law tail of `sup |ζ|` on discs at typical heights -/

/-- Heights at which `|ζ| ≥ B` somewhere on `closedBall c r + iτ`. -/
def discZetaLargeSet (c : ℂ) (r B : ℝ) : Set ℝ :=
  {τ : ℝ | ∃ z ∈ closedBall c r, B ≤ ‖riemannZeta (z + τ * I)‖}

/-- Where `ζ` exceeds twice the head bound, the tail exceeds the head bound. -/
theorem discZetaLargeSet_subset_discTailBadSet {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) (M : ℕ) :
    discZetaLargeSet c r (2 * ((M : ℝ) ^ (1 - (c.re - 2 * r)) / (1 - (c.re - 2 * r)) + 1)) ⊆
      discTailBadSet M c r ((M : ℝ) ^ (1 - (c.re - 2 * r)) / (1 - (c.re - 2 * r)) + 1) := by
  rintro τ ⟨z, hz, hB⟩
  refine ⟨z, hz, ?_⟩
  have hσ₀ : 0 < c.re - 2 * r := by linarith
  have hσ₁ : c.re - 2 * r < 1 := by linarith
  have hre : (z + τ * I).re = z.re := by simp
  have hzre : c.re - 2 * r ≤ (z + τ * I).re := by
    rw [hre]
    have := re_ge_of_mem_closedBall hz
    linarith
  have hhead := norm_edPoly_one_Icc_le_of_re_ge hσ₀ hσ₁ M hzre
  have htri := norm_sub_norm_le (riemannZeta (z + τ * I))
    (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I))
  show _ ≤ ‖zetaTailFun M (z + τ * I)‖
  unfold zetaTailFun
  linarith

/-- `(2σ₀/(2σ₀−1)) (M+1)^{1−2σ₀} / A_M² ≤ (2σ₀/(2σ₀−1)) (1−σ₀)² / M`. -/
theorem tailMass_bound_div_headBound_sq_le {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (hσ₁ : σ₀ < 1) {M : ℕ}
    (hM : 1 ≤ M) :
    2 * σ₀ / (2 * σ₀ - 1) * ((M : ℝ) + 1) ^ (1 - 2 * σ₀) /
        ((M : ℝ) ^ (1 - σ₀) / (1 - σ₀) + 1) ^ 2 ≤
      2 * σ₀ / (2 * σ₀ - 1) * (1 - σ₀) ^ 2 / M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hL : 0 < 1 - σ₀ := by linarith
  have hQ0 : 0 < 2 * σ₀ / (2 * σ₀ - 1) := div_pos (by linarith) (by linarith)
  have h1' : ((M : ℝ) + 1) ^ (1 - 2 * σ₀) ≤ (M : ℝ) ^ (1 - 2 * σ₀) :=
    rpow_le_rpow_of_le_of_nonpos hM0 (by linarith) (by linarith)
  have h2' : (M : ℝ) ^ (1 - σ₀) / (1 - σ₀) ≤ (M : ℝ) ^ (1 - σ₀) / (1 - σ₀) + 1 := by linarith
  have hpow : 0 < ((M : ℝ) ^ (1 - σ₀) / (1 - σ₀)) ^ 2 := by positivity
  have h3' : ((M : ℝ) ^ (1 - σ₀) / (1 - σ₀)) ^ 2 ≤ ((M : ℝ) ^ (1 - σ₀) / (1 - σ₀) + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2' 2
  have e1 : ((M : ℝ) ^ (1 - σ₀)) ^ 2 = (M : ℝ) ^ (2 - 2 * σ₀) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
    congr 1
    push_cast
    ring
  have e2 : (M : ℝ) ^ (1 - 2 * σ₀) / (M : ℝ) ^ (2 - 2 * σ₀) = (M : ℝ)⁻¹ := by
    rw [← Real.rpow_sub hM0, show (1 - 2 * σ₀) - (2 - 2 * σ₀) = -1 by ring, Real.rpow_neg_one]
  calc 2 * σ₀ / (2 * σ₀ - 1) * ((M : ℝ) + 1) ^ (1 - 2 * σ₀) /
        ((M : ℝ) ^ (1 - σ₀) / (1 - σ₀) + 1) ^ 2
      ≤ 2 * σ₀ / (2 * σ₀ - 1) * (M : ℝ) ^ (1 - 2 * σ₀) /
          ((M : ℝ) ^ (1 - σ₀) / (1 - σ₀)) ^ 2 :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left h1' hQ0.le) hpow h3'
    _ = 2 * σ₀ / (2 * σ₀ - 1) * (1 - σ₀) ^ 2 *
          ((M : ℝ) ^ (1 - 2 * σ₀) / (M : ℝ) ^ (2 - 2 * σ₀)) := by
        rw [div_pow, e1, div_div_eq_mul_div]
        ring
    _ = 2 * σ₀ / (2 * σ₀ - 1) * (1 - σ₀) ^ 2 / M := by
        rw [e2]
        ring

/-- **Power-law tail of `sup |ζ|` on discs at typical heights.**  With `σ₀ = Re c − 2r` and
`A_M = M^{1−σ₀}/(1−σ₀) + 1`, the heights at which `|ζ| ≥ 2A_M` somewhere on
`closedBall c r + iτ` have asymptotic density at most
`28 K (2σ₀/(2σ₀−1)) (1−σ₀)² / M + κ`, uniformly in the window `[0, T]`. -/
theorem eventually_volume_discZetaLargeSet_le {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {M : ℕ} (hM : 1 ≤ M) {κ : ℝ}
    (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop,
      volume (discZetaLargeSet c r
        (2 * ((M : ℝ) ^ (1 - (c.re - 2 * r)) / (1 - (c.re - 2 * r)) + 1)) ∩ Icc 0 T) ≤
      ENNReal.ofReal ((28 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 *
        (2 * (c.re - 2 * r) / (2 * (c.re - 2 * r) - 1) * (1 - (c.re - 2 * r)) ^ 2 / M) + κ) *
          T) := by
  have hL' : 0 < 1 - (c.re - 2 * r) := by linarith
  have hApos : 0 < (M : ℝ) ^ (1 - (c.re - 2 * r)) / (1 - (c.re - 2 * r)) + 1 := by positivity
  have hsub := discZetaLargeSet_subset_discTailBadSet hr h0 h1 M
  have hkey := tailMass_bound_div_headBound_sq_le h0 (by linarith) hM
  have hL : 0 < 1 - (c.re + 2 * r) := by linarith
  have hK0 : 0 ≤ 28 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 := by positivity
  filter_upwards [eventually_volume_discTailBadSet_le_explicit M hr h0 h1 hApos hκ,
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  refine (measure_mono (inter_subset_inter_left _ hsub)).trans
    (hT.trans (ENNReal.ofReal_le_ofReal ?_))
  refine mul_le_mul_of_nonneg_right ?_ hT0
  have hmul := mul_le_mul_of_nonneg_left hkey hK0
  have e : 28 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 /
      ((M : ℝ) ^ (1 - (c.re - 2 * r)) / (1 - (c.re - 2 * r)) + 1) ^ 2 *
        (2 * (c.re - 2 * r) / (2 * (c.re - 2 * r) - 1) *
          ((M : ℝ) + 1) ^ (1 - 2 * (c.re - 2 * r))) =
      28 * (1 + r / (1 - (c.re + 2 * r))) ^ 2 *
        (2 * (c.re - 2 * r) / (2 * (c.re - 2 * r) - 1) *
          ((M : ℝ) + 1) ^ (1 - 2 * (c.re - 2 * r)) /
            ((M : ℝ) ^ (1 - (c.re - 2 * r)) / (1 - (c.re - 2 * r)) + 1) ^ 2) := by
    ring
  linarith [e, hmul]

/-! ## 3. Precompactness of the typical orbit on a disc -/

/-- Two head translates whose phases are within `θ` differ by at most `M θ` on `Re w ≥ 0`. -/
theorem norm_edPoly_one_Icc_shift_sub_shift_le {M : ℕ} {θ τ s : ℝ}
    (h : ∀ n ∈ Finset.Icc 1 M, ‖bohrChar (Real.log n) τ - bohrChar (Real.log n) s‖ ≤ θ)
    {w : ℂ} (hw : 0 ≤ w.re) :
    ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (w + τ * I) -
      edPoly (fun _ => 1) (Finset.Icc 1 M) (w + s * I)‖ ≤ M * θ := by
  unfold edPoly
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      ‖(1 : ℂ) * ((n : ℝ) : ℂ) ^ (-(w + τ * I)) - 1 * ((n : ℝ) : ℂ) ^ (-(w + s * I))‖ ≤ θ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : 0 < n := hn1
    rw [one_mul, one_mul, nat_cpow_neg_vertical_translate hn0, nat_cpow_neg_vertical_translate hn0,
      ← mul_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn0)]
    have h1 : (n : ℝ) ^ (-w).re ≤ 1 := by
      rw [Complex.neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by linarith)
    calc (n : ℝ) ^ (-w).re * ‖bohrChar (Real.log n) τ - bohrChar (Real.log n) s‖ ≤ 1 * θ :=
          mul_le_mul h1 (h n hn) (norm_nonneg _) zero_le_one
      _ = θ := one_mul θ
  calc (∑ n ∈ Finset.Icc 1 M,
        ‖(1 : ℂ) * ((n : ℝ) : ℂ) ^ (-(w + τ * I)) - 1 * ((n : ℝ) : ℂ) ^ (-(w + s * I))‖)
      ≤ ∑ _n ∈ Finset.Icc 1 M, θ := Finset.sum_le_sum hterm
    _ = M * θ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

/-- **Precompactness of the typical orbit.**  For every disc of the strip and `ε, δ > 0` there are
`M` and a finite set `S` of heights such that, outside a set of heights of density `≤ δ`,
`ζ(· + iτ)` is within `ε` of one of the head translates `head_M(· + is)`, `s ∈ S`, uniformly on
the disc. -/
theorem exists_finite_headTranslates_cover_typicalHeights {c : ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : 1 / 2 < c.re - 2 * r) (h1 : c.re + 2 * r < 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M : ℕ, ∃ S : Finset ℝ, S.Nonempty ∧ ∀ᶠ T : ℝ in atTop,
      volume ({τ : ℝ | ¬ ∃ s ∈ S, ∀ z ∈ closedBall c r,
        ‖riemannZeta (z + τ * I) - edPoly (fun _ => 1) (Finset.Icc 1 M) (z + s * I)‖ < ε} ∩
          Icc 0 T) ≤ ENNReal.ofReal (δ * T) := by
  obtain ⟨M, hM⟩ :=
    (eventually_eventually_volume_discTailBadSet_le hr h0 h1 (half_pos hε) hδ).exists
  set u : Fin M → ℝ := fun j => Real.log ((j : ℕ) + 1) with hu
  have hθ : 0 < ε / (2 * (M + 1)) := by positivity
  obtain ⟨S, hSne, hS⟩ := hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic
    (continuous_bohrCharVector u) (isBohrAlmostPeriodic_bohrCharVector M u) _ hθ
  refine ⟨M, S, hSne, hM.mono fun T hT =>
    le_trans (measure_mono (inter_subset_inter_left _ ?_)) hT⟩
  intro τ hτ
  by_contra hgood
  apply hτ
  obtain ⟨s, hsS, hs⟩ := hS τ
  refine ⟨s, hsS, fun z hz => ?_⟩
  have hphase : ∀ n ∈ Finset.Icc 1 M,
      ‖bohrChar (Real.log n) τ - bohrChar (Real.log n) s‖ ≤ ε / (2 * (M + 1)) := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    have h := hs 0
    rw [zero_add, zero_add] at h
    have h' := (pi_norm_le_iff_of_nonneg hθ.le).mp h ⟨n - 1, by omega⟩
    rw [Pi.sub_apply] at h'
    simp only [bohrCharVector, hu] at h'
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn1
    rw [hcast] at h'
    exact h'
  have hzre : 0 ≤ z.re := by
    have := re_ge_of_mem_closedBall hz
    linarith
  have hhead : ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
      edPoly (fun _ => 1) (Finset.Icc 1 M) (z + s * I)‖ ≤ ε / 2 := by
    refine (norm_edPoly_one_Icc_shift_sub_shift_le hphase hzre).trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith
  have htail : ‖zetaTailFun M (z + τ * I)‖ < ε / 2 := by
    by_contra hcon
    exact hgood ⟨z, hz, not_lt.mp hcon⟩
  have hid : riemannZeta (z + τ * I) - edPoly (fun _ => 1) (Finset.Icc 1 M) (z + s * I) =
      zetaTailFun M (z + τ * I) + (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) (z + s * I)) := by
    unfold zetaTailFun
    ring
  rw [hid]
  calc ‖zetaTailFun M (z + τ * I) + (edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
        edPoly (fun _ => 1) (Finset.Icc 1 M) (z + s * I))‖
      ≤ ‖zetaTailFun M (z + τ * I)‖ + ‖edPoly (fun _ => 1) (Finset.Icc 1 M) (z + τ * I) -
          edPoly (fun _ => 1) (Finset.Icc 1 M) (z + s * I)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end RHTower
