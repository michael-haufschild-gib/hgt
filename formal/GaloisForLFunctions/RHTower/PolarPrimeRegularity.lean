import GaloisForLFunctions.RHTower.WindowRHCriterion
import GaloisForLFunctions.RHTower.PrimePolarRHCriterion
import GaloisForLFunctions.RHTower.PrimePolarHLHolomorphic
import GaloisForLFunctions.HTGeometry.RemovableSingularity

/-!
# Exact polar cancellation at the shifted `ζ`-pole

The bare windowed observable `W(s)·(-ζ'/ζ)(s-½)` (`windowObservable`) inherits `ζ`'s pole at `s-½ = 1`,
i.e. an unconditional singularity at `s = 3/2`, which is why the windowed RH criterion excludes that
point.  The *renormalized* observable of the moving-tent tomography restores regularity there by adding
back an elementary polar term `κ·ζ(s-½)`: its own pole at `s = 3/2` (residue `κ`, since `ζ` has residue
`1` at `1`) exactly cancels the prime channel's pole (residue `W(3/2)`, since `-ζ'/ζ` has residue `+1`
at `1`) precisely when

`W(3/2) = -κ`.

This is §5 ("exact polar cancellation") of `prime-polar-moving-tent-divisor-tomography` in abstract form.
Near `3/2`, with `G = zetaResidueUnit` (the analytic unit `G(s) = (s-1)·ζ(s)`, `G(1) = 1`),

`ζ(s-½) = G(s-½)/(s-3/2)`   and   `-ζ'/ζ(s-½) = -logDeriv G(s-½) + 1/(s-3/2)`   (`logDeriv_zeta_eq`),

so the combined observable equals `N(s)/(s-3/2) - W(s)·logDeriv G(s-½)` with the analytic numerator
`N(s) = κ·G(s-½) + W(s)` vanishing at `3/2` under the matching condition.  The removable-singularity
lemma `HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero` reads off the finite boundary value `N'(3/2)`,
and the second term is continuous — so the renormalized observable is regular at the shifted pole.
-/

open Filter Topology

namespace RHTower

/-- The polar-renormalized prime observable at coefficient `κ`: the bare windowed prime observable
`W(s)·(-ζ'/ζ)(s-½)` plus the elementary polar correction `κ·ζ(s-½)`. -/
noncomputable def polarPrimeObservable (κ : ℂ) (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  κ * riemannZeta (s - 1 / 2) + windowObservable W s

/-- **Exact polar cancellation.**  If the window value `W(3/2)` matches the polar coefficient by
`W(3/2) = -κ`, then the renormalized observable `κ·ζ(s-½) + W(s)·(-ζ'/ζ)(s-½)` is *regular* at the
shifted `ζ`-pole `s = 3/2`: it has a finite limit there, even though each of its two summands has a
simple pole.  This is the mechanism that removes the `s = 3/2` exclusion of the windowed RH criterion
for the renormalized (moving-tent) observable. -/
theorem polarPrimeObservable_regular_at_pole (κ : ℂ) (W : ℂ → ℂ)
    (hW : DifferentiableAt ℂ W (3 / 2)) (hmatch : W (3 / 2) = -κ) :
    ∃ M : ℂ, Tendsto (polarPrimeObservable κ W) (𝓝[≠] (3 / 2)) (𝓝 M) := by
  have h1 : (3 / 2 : ℂ) - 1 / 2 = 1 := by norm_num
  have hG1ne : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  -- `s ↦ G(s-½)` is differentiable at 3/2 (`G` analytic at `1 = 3/2 - ½`).
  have hshiftdiff : DifferentiableAt ℂ (fun s : ℂ => s - 1 / 2) (3 / 2) :=
    differentiableAt_id.sub_const _
  have hGana : DifferentiableAt ℂ zetaResidueUnit (3 / 2 - 1 / 2) := by
    rw [h1]; exact zetaResidueUnit_analyticAt.differentiableAt
  have hGdiff : DifferentiableAt ℂ (fun s => zetaResidueUnit (s - 1 / 2)) (3 / 2) :=
    hGana.comp (3 / 2) hshiftdiff
  -- The numerator `N s = κ·G(s-½) + W s` is differentiable at 3/2 and vanishes there.
  have hNdiff : DifferentiableAt ℂ (fun s => κ * zetaResidueUnit (s - 1 / 2) + W s) (3 / 2) :=
    (hGdiff.const_mul κ).add hW
  have hN0 : (fun s => κ * zetaResidueUnit (s - 1 / 2) + W s) (3 / 2) = 0 := by
    simp only [h1, zetaResidueUnit_one, hmatch]; ring
  have hfirst := HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero hNdiff hN0
  -- The analytic remainder `W(s)·logDeriv G(s-½)` is continuous, hence has a limit, at 3/2.
  have hlogG_cont1 : ContinuousAt (logDeriv zetaResidueUnit) 1 :=
    (zetaResidueUnit_analyticAt.deriv.continuousAt).div zetaResidueUnit_analyticAt.continuousAt hG1ne
  have hshift_tendsto : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝 (3 / 2)) (𝓝 1) := by
    have h : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝 (3 / 2)) (𝓝 (3 / 2 - 1 / 2)) :=
      hshiftdiff.continuousAt
    rwa [h1] at h
  have hWt : Tendsto W (𝓝[≠] (3 / 2)) (𝓝 (W (3 / 2))) :=
    hW.continuousAt.mono_left nhdsWithin_le_nhds
  have hlogGt : Tendsto (fun s => logDeriv zetaResidueUnit (s - 1 / 2)) (𝓝[≠] (3 / 2))
      (𝓝 (logDeriv zetaResidueUnit 1)) :=
    hlogG_cont1.tendsto.comp (hshift_tendsto.mono_left nhdsWithin_le_nhds)
  have hsecond_tendsto :
      Tendsto (fun s => W s * logDeriv zetaResidueUnit (s - 1 / 2)) (𝓝[≠] (3 / 2))
        (𝓝 (W (3 / 2) * logDeriv zetaResidueUnit 1)) :=
    hWt.mul hlogGt
  -- Near 3/2 (off the pole), `G(s-½) ≠ 0`.
  have hGne_near : ∀ᶠ s in 𝓝 (3 / 2 : ℂ), zetaResidueUnit (s - 1 / 2) ≠ 0 :=
    hshift_tendsto.eventually zetaResidueUnit_ne_zero_eventually
  -- The observable equals `N(s)/(s-3/2) − W(s)·logDeriv G(s-½)` off the pole.
  have hEq : polarPrimeObservable κ W =ᶠ[𝓝[≠] (3 / 2)]
      fun s => (fun t => κ * zetaResidueUnit (t - 1 / 2) + W t) s / (s - 3 / 2)
        - W s * logDeriv zetaResidueUnit (s - 1 / 2) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hGne_near] with s hs hGs
    have hs' : s ≠ 3 / 2 := hs
    have hsub : s - 3 / 2 ≠ 0 := sub_ne_zero.mpr hs'
    have hw1 : s - 1 / 2 ≠ 1 := fun h => hs' (by linear_combination h)
    have hζ : riemannZeta (s - 1 / 2) = zetaResidueUnit (s - 1 / 2) / (s - 3 / 2) := by
      have hval : zetaResidueUnit (s - 1 / 2) = (s - 3 / 2) * riemannZeta (s - 1 / 2) := by
        simp only [zetaResidueUnit, Function.update_of_ne hw1]
        rw [show s - 1 / 2 - 1 = s - 3 / 2 by ring]
      rw [hval, mul_comm, mul_div_assoc, div_self hsub, mul_one]
    have hlog : -deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2)
        = -logDeriv zetaResidueUnit (s - 1 / 2) + (s - 3 / 2)⁻¹ := by
      rw [neg_div, ← logDeriv_apply, logDeriv_zeta_eq hw1 hGs,
        show s - 1 / 2 - 1 = s - 3 / 2 by ring]
      ring
    simp only [polarPrimeObservable, windowObservable]
    rw [hlog, hζ]
    field_simp
    ring
  exact ⟨_, (tendsto_congr' hEq).mpr (hfirst.sub hsecond_tendsto)⟩

/-- **The moving-tent renormalized observable is regular at the shifted pole.**  The concrete instance of
the polar cancellation for `prime-polar-moving-tent-divisor-tomography`: the tent window multiplier is
`W(s) = -2·A_L(s-1)²` and the polar coefficient is `κ = 8α²` with `α = 1 - e^{-L/2}`, so the paper's
matching identity `W(3/2) = -2·A_L(½)² = -2·(2α)² = -8α² = -κ` (via `rectangularWindowAmplitude_at_half`)
gives the exact cancellation.  Hence the renormalized observable `8α²·ζ(s-½) + primeObservable L s` — the
polar term `(21)`'s leading piece plus the moving-tent prime channel `(20)` — has a finite limit at
`s = 3/2`, restoring regularity at the point the bare-observable criterion had to exclude. -/
theorem primeObservable_polar_regular_at_pole (L : ℝ) :
    ∃ M : ℂ, Tendsto (fun s => 8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2 * riemannZeta (s - 1 / 2)
        + primeObservable L s) (𝓝[≠] (3 / 2)) (𝓝 M) := by
  have hconv : (fun s => 8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2 * riemannZeta (s - 1 / 2)
      + primeObservable L s)
      = polarPrimeObservable (8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2)
        (fun s => -2 * (rectangularWindowAmplitude L (s - 1)) ^ 2) := by
    funext s
    simp only [polarPrimeObservable, windowObservable, primeObservable]
  rw [hconv]
  apply polarPrimeObservable_regular_at_pole
  · exact (((rectangularWindowAmplitude_differentiable L).comp
      (differentiable_id.sub_const 1)).pow 2).differentiableAt.const_mul (-2)
  · show -2 * (rectangularWindowAmplitude L (3 / 2 - 1)) ^ 2
        = -(8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2)
    rw [rectangularWindowAmplitude_at_half]; ring

/-- Detection: regularity of the renormalized observable at the off-critical shifts forces RH.  At
`s = ρ+½` the polar correction `κ·ζ(s-½)` is continuous (`ρ ≠ 1`), so `polarPrimeObservable κ W` and
`windowObservable W` are simultaneously regular there; the latter has a genuine pole, contradiction. -/
theorem RH_of_polarPrimeObservable_regular (κ : ℂ) (W : ℂ → ℂ) (hWcont : Continuous W)
    (hWne : ∀ ρ : ℂ, 1 / 2 < ρ.re → W (ρ + 1 / 2) ≠ 0)
    (hreg : ∀ a : ℂ, 1 < a.re → ∃ M : ℂ, Tendsto (polarPrimeObservable κ W) (𝓝[≠] a) (𝓝 M)) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2 := by
  intro ρ hζρ hρ1
  by_contra h
  have hgt : 1 / 2 < ρ.re := not_le.mp h
  have hre : 1 < (ρ + 1 / 2).re := by rw [Complex.add_re]; simp; linarith
  obtain ⟨M, hM⟩ := hreg (ρ + 1 / 2) hre
  have hζρ_diff : DifferentiableAt ℂ riemannZeta ρ := differentiableAt_riemannZeta hρ1
  have hshift : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝 (ρ + 1 / 2)) (𝓝 ρ) := by
    have hsd : DifferentiableAt ℂ (fun s : ℂ => s - 1 / 2) (ρ + 1 / 2) := differentiableAt_id.sub_const _
    have h : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝 (ρ + 1 / 2)) (𝓝 (ρ + 1 / 2 - 1 / 2)) := hsd.continuousAt
    rwa [show ρ + 1 / 2 - 1 / 2 = ρ by ring] at h
  have hpolar : Tendsto (fun s => κ * riemannZeta (s - 1 / 2)) (𝓝[≠] (ρ + 1 / 2))
      (𝓝 (κ * riemannZeta ρ)) :=
    (tendsto_const_nhds.mul (hζρ_diff.continuousAt.tendsto.comp hshift)).mono_left nhdsWithin_le_nhds
  have hwin : Tendsto (windowObservable W) (𝓝[≠] (ρ + 1 / 2)) (𝓝 (M - κ * riemannZeta ρ)) := by
    refine (hM.sub hpolar).congr (fun s => ?_)
    simp only [polarPrimeObservable]; ring
  exact windowObservable_no_limit W hρ1 hζρ hWcont.continuousAt (hWne ρ hgt) ⟨_, hwin⟩

/-- Converse (satisfiability under RH).  If `ζ` has no zeros with `Re > ½` then the renormalized
observable is regular at *every* point of `Re s > 1` — including `s = 3/2`, where the polar term supplies
the cancellation (`polarPrimeObservable_regular_at_pole`).  Off `3/2`, `windowObservable W` is regular by
RH and the polar term `κ·ζ(s-½)` is continuous (`a-½ ≠ 1`), so their sum is regular. -/
theorem polarPrimeObservable_regular_of_RH (κ : ℂ) (W : ℂ → ℂ) (hWdiff : Differentiable ℂ W)
    (hW32 : W (3 / 2) = -κ)
    (hRH : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2) :
    ∀ a : ℂ, 1 < a.re → ∃ M : ℂ, Tendsto (polarPrimeObservable κ W) (𝓝[≠] a) (𝓝 M) := by
  intro a ha
  by_cases ha32 : a = 3 / 2
  · subst ha32
    exact polarPrimeObservable_regular_at_pole κ W hWdiff.differentiableAt hW32
  · obtain ⟨Mw, hMw⟩ := windowObservable_regular_of_RH W hWdiff.continuous hRH a ha ha32
    have ha1 : a - 1 / 2 ≠ 1 := fun h => ha32 (by linear_combination h)
    have hζad : DifferentiableAt ℂ riemannZeta (a - 1 / 2) := differentiableAt_riemannZeta ha1
    have hsd : DifferentiableAt ℂ (fun s : ℂ => s - 1 / 2) a := differentiableAt_id.sub_const _
    have hshift : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝 a) (𝓝 (a - 1 / 2)) := hsd.continuousAt
    have hpolar : Tendsto (fun s => κ * riemannZeta (s - 1 / 2)) (𝓝[≠] a)
        (𝓝 (κ * riemannZeta (a - 1 / 2))) :=
      (tendsto_const_nhds.mul (hζad.continuousAt.tendsto.comp hshift)).mono_left nhdsWithin_le_nhds
    exact ⟨_, (hpolar.add hMw).congr (fun s => by simp only [polarPrimeObservable])⟩

/-- **Exclusion-free renormalized RH equivalence.**  For a differentiable window `W` nonvanishing at
every off-critical shift `ρ+½` and matching the polar coefficient by `W(3/2) = -κ`, RH is equivalent to
regularity of the renormalized observable `κ·ζ(s-½) + W(s)·(-ζ'/ζ)(s-½)` on *all* of `Re s > 1` — with
**no excluded point**: the polar term cancels `ζ`'s pole at `s = 3/2`. -/
theorem RH_iff_polarPrimeObservable_regular (κ : ℂ) (W : ℂ → ℂ) (hWdiff : Differentiable ℂ W)
    (hWne : ∀ ρ : ℂ, 1 / 2 < ρ.re → W (ρ + 1 / 2) ≠ 0) (hW32 : W (3 / 2) = -κ) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2)
      ↔ (∀ a : ℂ, 1 < a.re → ∃ M : ℂ, Tendsto (polarPrimeObservable κ W) (𝓝[≠] a) (𝓝 M)) :=
  ⟨polarPrimeObservable_regular_of_RH κ W hWdiff hW32,
    RH_of_polarPrimeObservable_regular κ W hWdiff.continuous hWne⟩

/-- **The moving-tent exclusion-free RH criterion `(28)`.**  RH ⟺ the renormalized moving-tent
observable `8α²·ζ(s-½) + primeObservable L s` (`α = 1 - e^{-L/2}`) is regular on all of `Re s > 1`.  The
tent window `W(s) = -2·A_L(s-1)²` is entire, nonvanishing on the off-critical shifts
(`rectangularWindowAmplitude_ne_zero`), and matches `W(3/2) = -8α² = -κ`. -/
theorem RH_iff_primeObservable_polar_regular (L : ℝ) (hL : 0 < L) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2)
      ↔ (∀ a : ℂ, 1 < a.re → ∃ M : ℂ,
          Tendsto (fun s => 8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2 * riemannZeta (s - 1 / 2)
            + primeObservable L s) (𝓝[≠] a) (𝓝 M)) := by
  have hconv : (fun s => 8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2 * riemannZeta (s - 1 / 2)
      + primeObservable L s)
      = polarPrimeObservable (8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2)
        (fun s => -2 * (rectangularWindowAmplitude L (s - 1)) ^ 2) := by
    funext s; simp only [polarPrimeObservable, windowObservable, primeObservable]
  rw [hconv]
  refine RH_iff_polarPrimeObservable_regular _ _
    (((rectangularWindowAmplitude_differentiable L).comp (differentiable_id.sub_const 1)).pow 2
      |>.const_mul (-2)) (fun ρ hρ => ?_) ?_
  · have e2 : ((1 / 2 : ℂ)).re = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
    have hpos : 0 < ((ρ + 1 / 2 : ℂ) - 1).re := by
      rw [Complex.sub_re, Complex.add_re, Complex.one_re, e2]; linarith
    have hAne : rectangularWindowAmplitude L (ρ + 1 / 2 - 1) ≠ 0 :=
      rectangularWindowAmplitude_ne_zero hL hpos
    show -2 * (rectangularWindowAmplitude L (ρ + 1 / 2 - 1)) ^ 2 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hAne)
  · show -2 * (rectangularWindowAmplitude L (3 / 2 - 1)) ^ 2
        = -(8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2)
    rw [rectangularWindowAmplitude_at_half]; ring

/-- Adding a function continuous at `a` does not change whether a function has a finite limit at `a`
(through the punctured neighborhood). -/
theorem exists_tendsto_add_continuousAt_iff {f C : ℂ → ℂ} {a : ℂ} (hC : ContinuousAt C a) :
    (∃ M : ℂ, Tendsto (fun s => f s + C s) (𝓝[≠] a) (𝓝 M))
      ↔ (∃ M : ℂ, Tendsto f (𝓝[≠] a) (𝓝 M)) := by
  have hCt : Tendsto C (𝓝[≠] a) (𝓝 (C a)) := hC.mono_left nhdsWithin_le_nhds
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M - C a, (hM.sub hCt).congr (fun s => by ring)⟩
  · rintro ⟨M, hM⟩
    exact ⟨M + C a, hM.add hCt⟩

/-- The three terms of `Pcal_L` `(22)` that are holomorphic throughout `Re s > 1`: the two lower polar
`ζ`-terms `16αβ·ζ(s) + 8β²·ζ(s+½)` and the holomorphic Riemann-sum error `-2·H_L(s)`.  Here
`α = 1 - e^{-L/2}`, `β = e^{L/2} - 1`. -/
noncomputable def PcalCorrection (L : ℝ) (s : ℂ) : ℂ :=
  16 * (1 - (Real.exp (-(L / 2)) : ℂ)) * ((Real.exp (L / 2) : ℂ) - 1) * riemannZeta s
    + 8 * ((Real.exp (L / 2) : ℂ) - 1) ^ 2 * riemannZeta (s + 1 / 2)
    - 2 * HL L s

/-- The full moving-tent observable `Pcal_L` of `(22)`: the ordinary Dirichlet series of the
prime–polar coefficient `p_L`, meromorphically continued to `Re s > 1`.  It is the renormalized
observable `8α²·ζ(s-½) + primeObservable L s` plus the holomorphic correction `PcalCorrection`. -/
noncomputable def PcalObservable (L : ℝ) (s : ℂ) : ℂ :=
  8 * (1 - (Real.exp (-(L / 2)) : ℂ)) ^ 2 * riemannZeta (s - 1 / 2)
    + primeObservable L s + PcalCorrection L s

/-- The `Pcal_L` correction terms are continuous at every `a` with `Re a > 1`: `ζ(s)` (`a ≠ 1`),
`ζ(s+½)` (`a+½ ≠ 1`), and `H_L` (`HL_differentiableOn` on the open region `Re > 1`). -/
theorem PcalCorrection_continuousAt (L : ℝ) (hL : 0 < L) {a : ℂ} (ha : 1 < a.re) :
    ContinuousAt (PcalCorrection L) a := by
  have e2 : ((1 / 2 : ℂ)).re = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  have ha1 : a ≠ 1 := fun h => by rw [h] at ha; simp at ha
  have ha12 : a + 1 / 2 ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    rw [Complex.add_re, Complex.one_re, e2] at hr; linarith
  have hζs : ContinuousAt (fun s => riemannZeta s) a := (differentiableAt_riemannZeta ha1).continuousAt
  have hζs2 : ContinuousAt (fun s => riemannZeta (s + 1 / 2)) a :=
    ((differentiableAt_riemannZeta ha12).comp a (differentiableAt_id.add_const _)).continuousAt
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hHL : ContinuousAt (HL L) a :=
    ((HL_differentiableOn L hL.le).differentiableAt (hopen.mem_nhds ha)).continuousAt
  unfold PcalCorrection
  exact ((continuousAt_const.mul hζs).add (continuousAt_const.mul hζs2)).sub
    (continuousAt_const.mul hHL)

/-- **The full moving-tent RH criterion `(28)`, exact `Pcal_L` form.**  RH ⟺ the ordinary Dirichlet
series `Pcal_L` of the prime–polar coefficient `p_L` is regular (has a finite limit) at every point of
`Re s > 1`.  The three correction terms are continuous on `Re s > 1` (`PcalCorrection_continuousAt`), so
they do not affect regularity, and the renormalized-observable criterion
`RH_iff_primeObservable_polar_regular` supplies the equivalence — the moving-tent card's headline
theorem in its verbatim `Pcal_L` statement. -/
theorem RH_iff_PcalObservable_regular (L : ℝ) (hL : 0 < L) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2)
      ↔ (∀ a : ℂ, 1 < a.re → ∃ M : ℂ, Tendsto (PcalObservable L) (𝓝[≠] a) (𝓝 M)) := by
  rw [RH_iff_primeObservable_polar_regular L hL]
  refine forall_congr' (fun a => imp_congr_right (fun ha => ?_))
  exact (exists_tendsto_add_continuousAt_iff (PcalCorrection_continuousAt L hL ha)).symm

/-- **The sharp bounded-variation-window exclusion-free RH criterion.**  The instance for
`bounded-variation-prime-window-divisor-tomography`: its canonical polar counterterm `R_W(N) =
2·I_W(3/2)·√N` contributes `2·A_L(½)·ζ(s-½) = 4α·ζ(s-½)`, and the sharp prime channel `-2·T_W` gives
`-2·A_L(s-1)·(-ζ'/ζ)(s-½)`.  The counterterm is defined precisely so that `W(3/2) = -2·A_L(½) = -4α = -κ`,
so RH is equivalent to regularity of the renormalized sharp observable on **all** of `Re s > 1` (with no
excluded point — the linear sharp window, versus the tent's squared window). -/
theorem RH_iff_sharpWindowPolar_regular (L : ℝ) (hL : 0 < L) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2)
      ↔ (∀ a : ℂ, 1 < a.re → ∃ M : ℂ,
          Tendsto (fun s => 4 * (1 - (Real.exp (-(L / 2)) : ℂ)) * riemannZeta (s - 1 / 2)
            + -2 * rectangularWindowAmplitude L (s - 1)
              * (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2))) (𝓝[≠] a) (𝓝 M)) := by
  have hconv : (fun s => 4 * (1 - (Real.exp (-(L / 2)) : ℂ)) * riemannZeta (s - 1 / 2)
      + -2 * rectangularWindowAmplitude L (s - 1)
        * (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2)))
      = polarPrimeObservable (4 * (1 - (Real.exp (-(L / 2)) : ℂ)))
        (fun s => -2 * rectangularWindowAmplitude L (s - 1)) := by
    funext s; simp only [polarPrimeObservable, windowObservable]
  rw [hconv]
  refine RH_iff_polarPrimeObservable_regular _ _
    (((rectangularWindowAmplitude_differentiable L).comp (differentiable_id.sub_const 1)).const_mul (-2))
    (fun ρ hρ => ?_) ?_
  · have e2 : ((1 / 2 : ℂ)).re = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
    have hpos : 0 < ((ρ + 1 / 2 : ℂ) - 1).re := by
      rw [Complex.sub_re, Complex.add_re, Complex.one_re, e2]; linarith
    have hAne : rectangularWindowAmplitude L (ρ + 1 / 2 - 1) ≠ 0 :=
      rectangularWindowAmplitude_ne_zero hL hpos
    show -2 * rectangularWindowAmplitude L (ρ + 1 / 2 - 1) ≠ 0
    exact mul_ne_zero (by norm_num) hAne
  · show -2 * rectangularWindowAmplitude L (3 / 2 - 1)
        = -(4 * (1 - (Real.exp (-(L / 2)) : ℂ)))
    rw [rectangularWindowAmplitude_at_half]; ring

end RHTower
