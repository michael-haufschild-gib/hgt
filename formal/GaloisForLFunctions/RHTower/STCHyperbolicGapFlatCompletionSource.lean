import GaloisForLFunctions.HTGeometry.HyperbolicGapFlatCompletion
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne
import GaloisForLFunctions.RHTower.DeningerGammaAllPrimeStokesPairBridge
import GaloisForLFunctions.RHTower.STCPrimeWindowPackets
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse
import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthHilbertSource
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Hyperbolic-gap flat completion of the literal Gamma prime pair

At common valuation depth `e` (`n = e+1`), the literal reflection-odd Gamma exterior normalized
by its critical amplitudes is `n(y-x)/2 · sinh(g(x+y)/2)` with `x = log p`, `y = log q`.  The
positive gap factor `S(g(y-x)/2)`, `S(t) = sinh t/t`, makes it the exact coboundary
`n/2 (cosh(gy) - cosh(gx))` of the one-prime potential `cosh(g log p)`.

This gap factor is **forced**:

* among continuous gap-only normalizations `F` with `F(0) = 1` making the pair flat for all real
  log coordinates, `F(d) = S(gd/2)` and the potential is `cosh(gx)/g + C`;
* already the flatness on actual ordered prime pairs forces `F(d) = S(gd/2)` for every real
  `d ≥ 0`: prime triples with prescribed limiting log gaps (a consequence of the prime number
  theorem) turn the triangle law into the exponential gap cocycle.

The canonical complex seam is the grade derivative of the flat potential, twisted by the
critical half-density and vertical phase.  The flat-completed kernel with the literal depth-zero
amplitude defines a bounded operator on `ℓ²(primes)` exactly when `u > 2|g|`, where it has rank
at most two and is compact; the critically weighted source wedge and its grade derivative are
square summable throughout `|g| < 1/2` and give a trace-class wedge.
-/

open Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry
open HTGeometry InnerProductSpace

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

namespace RHTower

noncomputable section

/-! ### The normalized source pair and its flat completion -/

/-- **(1)** The normalized literal reflection-odd pair: `n(y-x)/2 · sinh(g(x+y)/2)`. -/
theorem reflectionOddExterior_div_amplitudes (p q : Nat.Primes) (e : ℕ) (g : ℝ) :
    xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
        (sourcePrimeCell p e) (sourcePrimeCell q e) /
      (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
        xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e)) =
      ((e : ℝ) + 1) * (Real.log (q : ℝ) - Real.log (p : ℝ)) / 2 *
        Real.sinh (g * (Real.log (p : ℝ) + Real.log (q : ℝ)) / 2) := by
  have hp := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell p e)
  have hq := xiGammaEulerPrimitiveBoundaryAmplitude_pos 0 (sourcePrimeCell q e)
  rw [source_pair_commutator_identity]
  unfold sourcePairSymmetricKernel xiGammaEulerBoundaryHalfHeight routeRCrossPrimeStokesPhase
  field_simp
  ring

/-- **(2)** Division-free flat completion: the gap-corrected normalized pair is the coboundary
of the one-prime potential `cosh(g log p)`, at every real grade. -/
theorem flatGap_reflectionOddExterior_coboundary (p q : Nat.Primes) (e : ℕ) (g : ℝ) :
    g * hyperbolicGapSinc (g * (Real.log (q : ℝ) - Real.log (p : ℝ)) / 2) *
        (xiGammaEulerPrimitiveReflectionOddExterior (sourcePairLocalGrade g e)
            (sourcePrimeCell p e) (sourcePrimeCell q e) /
          (xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell p e) *
            xiGammaEulerPrimitiveBoundaryAmplitude 0 (sourcePrimeCell q e))) =
      ((e : ℝ) + 1) / 2 *
        (Real.cosh (g * Real.log (q : ℝ)) - Real.cosh (g * Real.log (p : ℝ))) := by
  rw [reflectionOddExterior_div_amplitudes, ← flatGapEdge_eq_cosh_sub]
  unfold flatGapEdge
  ring

/-! ### Rigidity for continuous gap factors on real log coordinates -/

/-- **(3)–(4) Continuous rigidity.** If a gap-only normalization `F`, continuous at `0` with
`F(0) = 1`, makes the normalized pair `(y-x) F(y-x) sinh(g(x+y)/2)` a coboundary `Φ(y) - Φ(x)`
for all `0 < x < y`, then `F(d) = S(gd/2)` for every `d ≥ 0` and `Φ(x) = cosh(gx)/g + C`. -/
theorem flatGap_continuous_rigidity {g : ℝ} (hg : g ≠ 0) {F Φ : ℝ → ℝ} (hF0 : F 0 = 1)
    (hFc : ContinuousWithinAt F (Set.Ici 0) 0)
    (hflat : ∀ x y : ℝ, 0 < x → x < y →
      (y - x) * F (y - x) * Real.sinh (g * (x + y) / 2) = Φ y - Φ x) :
    (∀ d : ℝ, 0 ≤ d → F d = hyperbolicGapSinc (g * d / 2)) ∧
      ∃ C : ℝ, ∀ x : ℝ, 0 < x → Φ x = Real.cosh (g * x) / g + C := by
  have hderiv : ∀ x : ℝ, 0 < x → HasDerivAt Φ (Real.sinh (g * x)) x := by
    intro x hx
    rw [hasDerivAt_iff_tendsto_slope]
    have hF : Tendsto (fun y => F |y - x|) (𝓝[≠] x) (𝓝 1) := by
      have h1 : Tendsto (fun y => |y - x|) (𝓝[≠] x) (𝓝[Set.Ici 0] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
          (Eventually.of_forall fun y => Set.mem_Ici.mpr (abs_nonneg _))
        have : Tendsto (fun y => |y - x|) (𝓝 x) (𝓝 |x - x|) :=
          ((continuous_id.sub continuous_const).abs).tendsto x
        simpa using this.mono_left nhdsWithin_le_nhds
      rw [← hF0]
      exact hFc.tendsto.comp h1
    have hS : Tendsto (fun y => Real.sinh (g * (x + y) / 2)) (𝓝[≠] x) (𝓝 (Real.sinh (g * x))) := by
      have hc : Continuous (fun y => Real.sinh (g * (x + y) / 2)) := by fun_prop
      have h2 := hc.tendsto x
      rw [show g * (x + x) / 2 = g * x by ring] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    have hlim := hF.mul hS
    rw [one_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hx)] with y hy hy0
    have hy' : y ≠ x := hy
    rw [slope_def_field]
    rcases lt_or_gt_of_ne hy' with hlt | hgt
    · have h := hflat y x hy0 hlt
      rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]
      have hne : y - x ≠ 0 := sub_ne_zero.mpr hy'
      rw [eq_div_iff hne]
      rw [show g * (y + x) / 2 = g * (x + y) / 2 by ring] at h
      linarith
    · have h := hflat x y hx hgt
      rw [abs_of_pos (sub_pos.mpr hgt)]
      have hne : y - x ≠ 0 := sub_ne_zero.mpr hy'
      rw [eq_div_iff hne]
      linarith
  -- the potential
  have hpot : ∃ C : ℝ, ∀ x : ℝ, 0 < x → Φ x = Real.cosh (g * x) / g + C := by
    have hG : ∀ x : ℝ, 0 < x → HasDerivAt (fun x => Φ x - Real.cosh (g * x) / g) 0 x := by
      intro x hx
      have hc : HasDerivAt (fun x => Real.cosh (g * x) / g) (Real.sinh (g * x)) x := by
        have h1 : HasDerivAt (fun x : ℝ => g * x) g x := by
          simpa using (hasDerivAt_id x).const_mul g
        have h2 := (Real.hasDerivAt_cosh (g * x)).comp x h1
        have h3 := h2.div_const g
        have e : Real.sinh (g * x) * g / g = Real.sinh (g * x) := by field_simp
        rwa [e] at h3
      have := (hderiv x hx).fun_sub hc
      rwa [sub_self] at this
    obtain ⟨C, hC⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hG x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hG x hx).deriv)
    exact ⟨C, fun x hx => by have := hC x hx; linarith⟩
  refine ⟨fun d hd => ?_, hpot⟩
  rcases hd.lt_or_eq with hd | hd
  · obtain ⟨C, hC⟩ := hpot
    have h := hflat 1 (1 + d) one_pos (by linarith)
    rw [hC (1 + d) (by linarith), hC 1 one_pos] at h
    have hedge := flatGapEdge_eq_cosh_sub g 1 (1 + d)
    unfold flatGapEdge at hedge
    have hs : Real.sinh (g * (1 + (1 + d)) / 2) ≠ 0 := by
      rw [Real.sinh_ne_zero]
      exact div_ne_zero (mul_ne_zero hg (by linarith)) two_ne_zero
    have hkey : (1 + d - 1) * F (1 + d - 1) * Real.sinh (g * (1 + (1 + d)) / 2) =
        (1 + d - 1) * Real.sinh (g * (1 + (1 + d)) / 2) *
          hyperbolicGapSinc (g * (1 + d - 1) / 2) := by
      have : g * ((1 + d - 1) * Real.sinh (g * (1 + (1 + d)) / 2) *
          hyperbolicGapSinc (g * (1 + d - 1) / 2)) = g * ((1 + d - 1) * F (1 + d - 1) *
            Real.sinh (g * (1 + (1 + d)) / 2)) := by
        rw [hedge, h]
        field_simp
        ring
      exact (mul_left_cancel₀ hg this).symm
    have hd' : (1 + d - 1) = d := by ring
    rw [hd'] at hkey
    have := mul_left_cancel₀ (mul_ne_zero hd.ne' hs) (by linarith [hkey] :
      d * Real.sinh (g * (1 + (1 + d)) / 2) * F d =
        d * Real.sinh (g * (1 + (1 + d)) / 2) * hyperbolicGapSinc (g * d / 2))
    exact this
  · subst hd
    rw [hF0, mul_zero, zero_div]
    simp [hyperbolicGapSinc]

/-! ### Prime-only rigidity -/

private theorem tendsto_sinh_shift_div_exp {a : ℝ} (ha : 0 < a) {X c : ℕ → ℝ} {c₀ : ℝ}
    (hX : Tendsto X atTop atTop) (hc : Tendsto c atTop (𝓝 c₀)) :
    Tendsto (fun k => Real.sinh (a * X k + a * c k / 2) / Real.exp (a * X k)) atTop
      (𝓝 (Real.exp (a * c₀ / 2) / 2)) := by
  have hexp1 : Tendsto (fun k => Real.exp (a * c k / 2)) atTop (𝓝 (Real.exp (a * c₀ / 2))) :=
    (Real.continuous_exp.tendsto _).comp ((hc.const_mul a).div_const 2)
  have hexp2 : Tendsto (fun k => Real.exp (-(a * c k / 2))) atTop
      (𝓝 (Real.exp (-(a * c₀ / 2)))) :=
    (Real.continuous_exp.tendsto _).comp (((hc.const_mul a).div_const 2).neg)
  have hdecay : Tendsto (fun k => Real.exp (-(2 * a * X k))) atTop (𝓝 0) := by
    have : Tendsto (fun k => 2 * a * X k) atTop atTop := hX.const_mul_atTop (by positivity)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp this
  have hlim := (hexp1.sub (hdecay.mul hexp2)).div_const 2
  rw [zero_mul, sub_zero] at hlim
  refine hlim.congr' (Eventually.of_forall fun k => ?_)
  show _ = Real.sinh (a * X k + a * c k / 2) / Real.exp (a * X k)
  rw [Real.sinh_eq]
  have h1 : Real.exp (a * X k + a * c k / 2) = Real.exp (a * X k) * Real.exp (a * c k / 2) :=
    Real.exp_add _ _
  have h2 : Real.exp (-(a * X k + a * c k / 2)) =
      Real.exp (a * X k) * (Real.exp (-(2 * a * X k)) * Real.exp (-(a * c k / 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [h1, h2]
  have hpos := Real.exp_pos (a * X k)
  field_simp

private theorem flatGap_prime_rigidity_pos {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF0 : F 0 = 1)
    (hFc : ContinuousOn F (Set.Ici 0)) {Φ : ℕ → ℝ}
    (hflat : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (Real.log q - Real.log p) * F (Real.log q - Real.log p) *
        Real.sinh (a * (Real.log p + Real.log q) / 2) = Φ q - Φ p) :
    ∀ d : ℝ, 0 ≤ d → F d = hyperbolicGapSinc (a * d / 2) := by
  set A : ℝ → ℝ := fun u => u * F u * Real.exp (a * u / 2) with hAdef
  have hcont : ∀ u : ℝ, 0 < u → ContinuousAt F u :=
    fun u hu => hFc.continuousAt (Ici_mem_nhds hu)
  -- the exponential gap cocycle
  have hcoc : ∀ d e : ℝ, 0 < d → 0 < e → A (d + e) = A d + Real.exp (a * d) * A e := by
    intro d e hd he
    obtain ⟨p, q, r, hprime, hord, hp, hd1, hd2⟩ := exists_prime_triples_logGap hd he
    have hXt : Tendsto (fun k => Real.log (p k : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hp
    have hD12 : Tendsto (fun k => (Real.log (q k : ℝ) - Real.log (p k : ℝ)) +
        (Real.log (r k : ℝ) - Real.log (q k : ℝ))) atTop (𝓝 (d + e)) := hd1.add hd2
    have hD112 : Tendsto (fun k => 2 * (Real.log (q k : ℝ) - Real.log (p k : ℝ)) +
        (Real.log (r k : ℝ) - Real.log (q k : ℝ))) atTop (𝓝 (2 * d + e)) :=
      (hd1.const_mul 2).add hd2
    have hpq := (hd1.mul ((hcont d hd).tendsto.comp hd1)).mul
      (tendsto_sinh_shift_div_exp ha hXt hd1)
    have hqr := (hd2.mul ((hcont e he).tendsto.comp hd2)).mul
      (tendsto_sinh_shift_div_exp ha hXt hD112)
    have hpr := (hD12.mul ((hcont (d + e) (by linarith)).tendsto.comp hD12)).mul
      (tendsto_sinh_shift_div_exp ha hXt hD12)
    have hsum := hqr.add hpq
    have heq : (d + e) * F (d + e) * (Real.exp (a * (d + e) / 2) / 2) =
        e * F e * (Real.exp (a * (2 * d + e) / 2) / 2) + d * F d * (Real.exp (a * d / 2) / 2) := by
      refine tendsto_nhds_unique (hpr.congr fun k => ?_) hsum
      obtain ⟨hpk, hqk, hrk⟩ := hprime k
      obtain ⟨hpq', hqr'⟩ := hord k
      have epr := hflat (p k) (r k) hpk hrk (hpq'.trans hqr')
      have eqr := hflat (q k) (r k) hqk hrk hqr'
      have epq := hflat (p k) (q k) hpk hqk hpq'
      simp only [Function.comp_apply]
      have h1 : (Real.log (q k : ℝ) - Real.log (p k : ℝ)) +
          (Real.log (r k : ℝ) - Real.log (q k : ℝ)) = Real.log (r k : ℝ) - Real.log (p k : ℝ) := by
        ring
      have h2 : a * Real.log (p k : ℝ) + a * ((Real.log (q k : ℝ) - Real.log (p k : ℝ)) +
          (Real.log (r k : ℝ) - Real.log (q k : ℝ))) / 2 =
          a * (Real.log (p k : ℝ) + Real.log (r k : ℝ)) / 2 := by ring
      have h3 : a * Real.log (p k : ℝ) + a * (2 * (Real.log (q k : ℝ) - Real.log (p k : ℝ)) +
          (Real.log (r k : ℝ) - Real.log (q k : ℝ))) / 2 =
          a * (Real.log (q k : ℝ) + Real.log (r k : ℝ)) / 2 := by ring
      have h4 : a * Real.log (p k : ℝ) + a * (Real.log (q k : ℝ) - Real.log (p k : ℝ)) / 2 =
          a * (Real.log (p k : ℝ) + Real.log (q k : ℝ)) / 2 := by ring
      rw [h2, h3, h4, h1, ← mul_div_assoc, ← mul_div_assoc, ← mul_div_assoc, ← add_div,
        epr, eqr, epq]
      ring
    simp only [hAdef]
    have hexp : Real.exp (a * (2 * d + e) / 2) = Real.exp (a * d) * Real.exp (a * e / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp] at heq
    linarith

  -- normalization at coincidence
  have hnorm : Tendsto (fun e : ℝ => A e / e) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      rw [← hF0]
      exact (hFc.continuousWithinAt Set.self_mem_Ici).tendsto.mono_left
        (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    have hE : Tendsto (fun e : ℝ => Real.exp (a * e / 2)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hc : Continuous fun e : ℝ => Real.exp (a * e / 2) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have hlim := hF.mul hE
    rw [one_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with e he
    have he' : e ≠ 0 := ne_of_gt he
    simp only [hAdef]
    field_simp
  have hA := HTGeometry.exponentialGapCocycle_rigidity a ha A hcoc hnorm
  intro d hd
  rcases hd.lt_or_eq with hd | hd
  · have h := hA d hd
    simp only [hAdef] at h
    have hE := Real.exp_pos (a * d / 2)
    have hsinc : hyperbolicGapSinc (a * d / 2) = Real.sinh (a * d / 2) / (a * d / 2) := by
      rw [hyperbolicGapSinc, if_neg (by positivity)]
    rw [hsinc, Real.sinh_eq]
    have hsq : Real.exp (a * d) = Real.exp (a * d / 2) * Real.exp (a * d / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hinv : Real.exp (-(a * d / 2)) = (Real.exp (a * d / 2))⁻¹ := Real.exp_neg _
    rw [hinv]
    rw [hsq] at h
    set E := Real.exp (a * d / 2)
    have hFd : F d = (E * E - 1) / (a * d * E) := by
      rw [eq_div_iff (by positivity)]
      rw [eq_div_iff ha.ne'] at h
      linarith
    rw [hFd]
    field_simp
  · subst hd
    rw [hF0]
    simp [hyperbolicGapSinc]

/-- **Prime-only rigidity.** If a continuous gap-only normalization `F` on `[0,∞)` with `F(0) = 1`
makes the normalized literal pair a coboundary `Φ(q) - Φ(p)` of an arbitrary prime potential on
every ordered prime pair, then `F(d) = S(gd/2)` for every real `d ≥ 0`. -/
theorem flatGap_prime_rigidity {g : ℝ} (hg : g ≠ 0) {F : ℝ → ℝ} (hF0 : F 0 = 1)
    (hFc : ContinuousOn F (Set.Ici 0)) {Φ : ℕ → ℝ}
    (hflat : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (Real.log q - Real.log p) * F (Real.log q - Real.log p) *
        Real.sinh (g * (Real.log p + Real.log q) / 2) = Φ q - Φ p) :
    ∀ d : ℝ, 0 ≤ d → F d = hyperbolicGapSinc (g * d / 2) := by
  rcases lt_or_gt_of_ne hg with hneg | hpos
  · intro d hd
    have h := flatGap_prime_rigidity_pos (neg_pos.mpr hneg) hF0 hFc (Φ := fun n => -Φ n)
      (fun p q hp hq hpq => by
        have := hflat p q hp hq hpq
        rw [show -g * (Real.log p + Real.log q) / 2 = -(g * (Real.log p + Real.log q) / 2) by ring,
          Real.sinh_neg]
        linarith) d hd
    rw [h, show -g * d / 2 = -(g * d / 2) by ring, hyperbolicGapSinc_even]
  · exact flatGap_prime_rigidity_pos hpos hF0 hFc hflat

/-! ### The canonical complex seam is the grade derivative of the flat potential -/

/-- **(5)** At `ρ = 1/2 + g + iτ`, the canonical prime seam charge is
`-2 p^{-1/2+iτ} ∂_g cosh(g log p)`. -/
theorem orbitwiseNatPrimeSeamCharge_eq_grade_derivative {p : ℕ} (hp : 0 < p) (g τ : ℝ) :
    orbitwiseNatPrimeSeamCharge p (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I) =
      -2 * (p : ℂ) ^ ((-1 / 2 : ℂ) + (τ : ℂ) * I) *
        ((deriv (fun t : ℝ => Real.cosh (t * Real.log p)) g : ℝ) : ℂ) := by
  rw [(HTGeometry.hasDerivAt_cosh_grade (Real.log p) g).deriv]
  unfold orbitwiseNatPrimeSeamCharge orbitwiseScaleSeamCharge
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (by positivity)]
  rw [show ((p : ℝ) : ℂ) = (p : ℂ) by push_cast; rfl, Complex.cpow_def_of_ne_zero hp0,
    Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0, hlog]
  set L : ℂ := (Real.log p : ℂ)
  have hconj : (starRingEnd ℂ) (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I) =
      ((1 / 2 + g : ℝ) : ℂ) - (τ : ℂ) * I := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj]
  have e1 : L * -(((1 / 2 + g : ℝ) : ℂ) - (τ : ℂ) * I) =
      L * ((-1 / 2 : ℂ) + (τ : ℂ) * I) + (-(g * L)) := by push_cast; ring
  have e2 : L * -(1 - (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I)) =
      L * ((-1 / 2 : ℂ) + (τ : ℂ) * I) + g * L := by push_cast; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  have hs : ((Real.log p * Real.sinh (g * Real.log p) : ℝ) : ℂ) =
      L * ((Complex.exp (g * L) - Complex.exp (-(g * L))) / 2) := by
    rw [Complex.ofReal_mul, Complex.ofReal_sinh, Complex.sinh, Complex.ofReal_mul]
  rw [hs]
  ring

/-! ### The flat kernel on `ℓ²(primes)` -/

/-- The literal depth-zero primitive source amplitude. -/
def stcDepthZeroAmplitude (u : ℝ) (p : Nat.Primes) : ℝ :=
  xiGammaEulerPrimitiveBoundaryAmplitude u (p, 0)

theorem stcDepthZeroAmplitude_pos (u : ℝ) (p : Nat.Primes) : 0 < stcDepthZeroAmplitude u p :=
  xiGammaEulerPrimitiveBoundaryAmplitude_pos u (p, 0)

theorem stcDepthZeroAmplitude_sq (u : ℝ) (p : Nat.Primes) :
    stcDepthZeroAmplitude u p ^ 2 = Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-1 - u) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  unfold stcDepthZeroAmplitude
  rw [xiGammaEulerPrimitiveBoundaryAmplitude_sq]
  have hv : (xiGammaEulerValuationNat (p, 0) : ℝ) = p := by
    simp [xiGammaEulerValuationNat]
  rw [hv, Real.rpow_def_of_pos hp, show Real.log (p : ℝ) * (-1 - u) =
    -Real.log p + -u * Real.log p by ring, Real.exp_add, Real.exp_neg, Real.exp_log hp]
  ring

/-- `b_u(p) p^a = b_{u-2a}(p)`. -/
theorem stcDepthZeroAmplitude_mul_rpow (u a : ℝ) (p : Nat.Primes) :
    stcDepthZeroAmplitude u p * (p : ℝ) ^ a = stcDepthZeroAmplitude (u - 2 * a) p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have h1 := stcDepthZeroAmplitude_pos u p
  have h2 := stcDepthZeroAmplitude_pos (u - 2 * a) p
  have hpa := Real.rpow_pos_of_pos hp a
  refine (pow_left_inj₀ (by positivity) h2.le two_ne_zero).mp ?_
  have hsq : ((p : ℝ) ^ a) ^ 2 = (p : ℝ) ^ (2 * a) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hp.le, mul_comm]
  rw [mul_pow, stcDepthZeroAmplitude_sq, stcDepthZeroAmplitude_sq, hsq, mul_assoc,
    ← Real.rpow_add hp]
  congr 2
  ring

private theorem eventually_cofinite_prime_ge (N : ℕ) :
    ∀ᶠ p : Nat.Primes in Filter.cofinite, N ≤ (p : ℕ) := by
  have hfin : {p : Nat.Primes | (p : ℕ) < N}.Finite :=
    (Set.finite_lt_nat N).preimage Subtype.val_injective.injOn
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  simpa using hp

/-- A prime family eventually bounded below by `c/p`, `c > 0`, is not summable. -/
theorem not_summable_of_eventually_ge_div_prime {f : Nat.Primes → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ p : Nat.Primes in Filter.cofinite, c / (p : ℝ) ≤ f p) : ¬ Summable f := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_norm_bounded_eventually (hs.mul_left c⁻¹) ?_
  filter_upwards [h] with p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [div_le_iff₀ hp0] at hp
  rw [div_le_iff₀ hp0, mul_assoc, mul_comm (f p), ← mul_assoc]
  rw [show c⁻¹ * (p : ℝ) * f p = c⁻¹ * ((p : ℝ) * f p) by ring]
  rw [le_inv_mul_iff₀ hc]
  linarith

/-- The depth-zero amplitude is square summable over the primes exactly when `v > 0`. -/
theorem summable_stcDepthZeroAmplitude_sq_iff (v : ℝ) :
    Summable (fun p : Nat.Primes => stcDepthZeroAmplitude v p ^ 2) ↔ 0 < v := by
  constructor
  · intro hs
    by_contra hv
    push Not at hv
    refine not_summable_of_eventually_ge_div_prime one_pos ?_ hs
    filter_upwards [eventually_cofinite_prime_ge 3] with p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hlog : 1 ≤ Real.log (p : ℝ) := by
      rw [Real.le_log_iff_exp_le hp0]; linarith [Real.exp_one_lt_d9]
    rw [stcDepthZeroAmplitude_sq]
    have hpow : (p : ℝ) ^ (-1 - v) ≥ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at hpow
    have hsq : 1 ≤ Real.log (p : ℝ) ^ 2 := by nlinarith
    calc 1 / (p : ℝ) = 1 * (p : ℝ)⁻¹ := by ring
      _ ≤ Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-1 - v) := by
          apply mul_le_mul hsq hpow (by positivity) (by positivity)
  · intro hv
    have h := summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_of_pos hv
    exact h.comp_injective (i := fun p : Nat.Primes => (p, 0))
      (fun a b hab => by simpa using congrArg Prod.fst hab)

/-- The flat-completed source kernel `b_u(p) b_u(q) [cosh(g log q) - cosh(g log p)]`. -/
def stcFlatGapKernel (u g : ℝ) (p q : Nat.Primes) : ℂ :=
  ((stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u q *
    (Real.cosh (g * Real.log (q : ℝ)) - Real.cosh (g * Real.log (p : ℝ))) : ℝ) : ℂ)

private theorem cosh_log_le_rpow (a : ℝ) (p : Nat.Primes) (g : ℝ) (hga : |g| = a) :
    Real.cosh (g * Real.log (p : ℝ)) ≤ (p : ℝ) ^ a := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  rw [Real.rpow_def_of_pos hp, ← Real.cosh_abs, abs_mul, hga, abs_of_nonneg hlog, Real.cosh_eq]
  have h1 := Real.exp_pos (a * Real.log p)
  have h2 : Real.exp (-(a * Real.log p)) ≤ Real.exp (a * Real.log p) := by
    rw [Real.exp_le_exp]; nlinarith [abs_nonneg g, hga ▸ abs_nonneg g]
  rw [mul_comm (Real.log (p : ℝ)) a]
  linarith

private theorem rpow_le_two_cosh_log (a : ℝ) (p : Nat.Primes) (g : ℝ) (hga : |g| = a) :
    (p : ℝ) ^ a ≤ 2 * Real.cosh (g * Real.log (p : ℝ)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  rw [Real.rpow_def_of_pos hp, ← Real.cosh_abs, abs_mul, hga, abs_of_nonneg hlog, Real.cosh_eq]
  have := Real.exp_pos (-(a * Real.log p))
  rw [mul_comm (Real.log (p : ℝ)) a]
  linarith

/-- `b_u cosh(g log ·)` is square summable when `u > 2|g|`. -/
theorem stcFlatGapCoshSummable {u g : ℝ} (hu : 2 * |g| < u) :
    Summable (fun p : Nat.Primes => (stcDepthZeroAmplitude u p *
      Real.cosh (g * Real.log (p : ℝ))) ^ 2) := by
  have hs := (summable_stcDepthZeroAmplitude_sq_iff (u - 2 * |g|)).mpr (by linarith)
  refine hs.of_nonneg_of_le (fun p => sq_nonneg _) fun p => ?_
  rw [← stcDepthZeroAmplitude_mul_rpow]
  have hc := cosh_log_le_rpow |g| p g rfl
  have hb := stcDepthZeroAmplitude_pos u p
  have hc0 := Real.cosh_pos (g * Real.log (p : ℝ))
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hc hb.le) 2

/-- In the chamber the kernel is the wedge of `b_u` and `b_u cosh(g log ·)`. -/
theorem stcFlatGapKernel_hasLpMatrix_wedge {u g : ℝ} (hg : g ≠ 0) (hu : 2 * |g| < u) :
    HasLpMatrix (lpWedge
        (lpOfReal (stcDepthZeroAmplitude u) ((summable_stcDepthZeroAmplitude_sq_iff u).mpr
          (by have := abs_pos.mpr hg; linarith)))
        (lpOfReal (fun p => stcDepthZeroAmplitude u p * Real.cosh (g * Real.log (p : ℝ)))
          (stcFlatGapCoshSummable hu)))
      (stcFlatGapKernel u g) := by
  have h := (hasLpMatrix_rankOne (lpOfReal (stcDepthZeroAmplitude u)
      ((summable_stcDepthZeroAmplitude_sq_iff u).mpr (by have := abs_pos.mpr hg; linarith)))
    (lpOfReal (fun p => stcDepthZeroAmplitude u p * Real.cosh (g * Real.log (p : ℝ)))
      (stcFlatGapCoshSummable hu))).sub
    (hasLpMatrix_rankOne (lpOfReal (fun p => stcDepthZeroAmplitude u p *
      Real.cosh (g * Real.log (p : ℝ))) (stcFlatGapCoshSummable hu))
      (lpOfReal (stcDepthZeroAmplitude u)
        ((summable_stcDepthZeroAmplitude_sq_iff u).mpr (by have := abs_pos.mpr hg; linarith))))
  refine h.congr fun i j => ?_
  simp only [lpOfReal_apply, Complex.conj_ofReal, stcFlatGapKernel]
  push_cast
  ring

/-- **(6) Domain classification.** For `g ≠ 0`, the flat-completed kernel is the matrix of a
bounded operator on `ℓ²(primes)` if and only if `u > 2|g|`. -/
theorem exists_hasLpMatrix_stcFlatGapKernel_iff {u g : ℝ} (hg : g ≠ 0) :
    (∃ T, HasLpMatrix T (stcFlatGapKernel u g)) ↔ 2 * |g| < u := by
  set a := |g| with hadef
  have ha : 0 < a := abs_pos.mpr hg
  constructor
  · rintro hT
    by_contra hu
    push Not at hu
    let two : Nat.Primes := ⟨2, Nat.prime_two⟩
    refine not_exists_hasLpMatrix_of_col (j := two) ?_ hT
    -- the column at the prime `2` is not square summable
    have hb2 := stcDepthZeroAmplitude_pos u two
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
      (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hpow.eventually_ge_atTop (4 * Real.cosh (g * Real.log ((two : ℕ) : ℝ))))
    refine not_summable_of_eventually_ge_div_prime (c := stcDepthZeroAmplitude u two ^ 2 / 16)
      (by positivity) ?_
    filter_upwards [eventually_cofinite_prime_ge (max N 3)] with p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (le_of_max_le_right hp)
    have hp0 : (0 : ℝ) < p := by linarith
    have hlog : 1 ≤ Real.log (p : ℝ) := by
      rw [Real.le_log_iff_exp_le hp0]; linarith [Real.exp_one_lt_d9]
    have hpN := hN p (le_of_max_le_left hp)
    have hcp := rpow_le_two_cosh_log a p g hadef.symm
    have hdiff : (p : ℝ) ^ a / 4 ≤
        Real.cosh (g * Real.log (p : ℝ)) - Real.cosh (g * Real.log ((two : ℕ) : ℝ)) := by
      clear_value a two
      linarith
    have hbp := stcDepthZeroAmplitude_pos u p
    have hK : stcDepthZeroAmplitude u two * stcDepthZeroAmplitude (u - 2 * a) p / 4 ≤
        |stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u two *
          (Real.cosh (g * Real.log ((two : ℕ) : ℝ)) - Real.cosh (g * Real.log (p : ℝ)))| := by
      rw [← stcDepthZeroAmplitude_mul_rpow, abs_mul, abs_of_pos (by positivity),
        abs_of_nonpos (by linarith [(by positivity : (0 : ℝ) ≤ (p : ℝ) ^ a / 4)])]
      have := mul_le_mul_of_nonneg_left hdiff (by positivity :
        (0 : ℝ) ≤ stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u two)
      nlinarith
    have hbsq := stcDepthZeroAmplitude_sq (u - 2 * a) p
    have hlow : (p : ℝ)⁻¹ ≤ stcDepthZeroAmplitude (u - 2 * a) p ^ 2 := by
      rw [hbsq]
      have hpow' : (p : ℝ) ^ (-1 : ℝ) ≤ (p : ℝ) ^ (-1 - (u - 2 * a)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [Real.rpow_neg_one] at hpow'
      have hsq : 1 ≤ Real.log (p : ℝ) ^ 2 := by nlinarith
      nlinarith [inv_pos.mpr hp0]
    have hnorm : ‖stcFlatGapKernel u g p two‖ =
        |stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u two *
          (Real.cosh (g * Real.log ((two : ℕ) : ℝ)) - Real.cosh (g * Real.log (p : ℝ)))| := by
      unfold stcFlatGapKernel
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    have hsq2 : (stcDepthZeroAmplitude u two * stcDepthZeroAmplitude (u - 2 * a) p / 4) ^ 2 ≤
        |stcDepthZeroAmplitude u p * stcDepthZeroAmplitude u two *
          (Real.cosh (g * Real.log ((two : ℕ) : ℝ)) - Real.cosh (g * Real.log (p : ℝ)))| ^ 2 :=
      pow_le_pow_left₀ (by have := stcDepthZeroAmplitude_pos (u - 2 * a) p; positivity) hK 2
    calc stcDepthZeroAmplitude u two ^ 2 / 16 / (p : ℝ)
        = stcDepthZeroAmplitude u two ^ 2 / 16 * (p : ℝ)⁻¹ := by ring
      _ ≤ stcDepthZeroAmplitude u two ^ 2 / 16 * stcDepthZeroAmplitude (u - 2 * a) p ^ 2 :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
      _ = (stcDepthZeroAmplitude u two * stcDepthZeroAmplitude (u - 2 * a) p / 4) ^ 2 := by ring
      _ ≤ _ := hsq2
  · intro hu
    exact ⟨_, stcFlatGapKernel_hasLpMatrix_wedge hg hu⟩

/-- In the chamber `u > 2|g|` the flat-completed kernel is realized by a compact operator of
rank at most two (the wedge of `b_u` and `b_u cosh(g log ·)`), and by no other bounded
operator. -/
theorem stcFlatGapKernel_compact_rank_two {u g : ℝ} (hg : g ≠ 0) (hu : 2 * |g| < u) :
    ∃ T, HasLpMatrix T (stcFlatGapKernel u g) ∧ IsCompactOperator T ∧
      Module.finrank ℂ (LinearMap.range ((T : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P)) ≤ 2 ∧
      ∀ S, HasLpMatrix S (stcFlatGapKernel u g) → S = T := by
  have h := stcFlatGapKernel_hasLpMatrix_wedge hg hu
  exact ⟨_, h, isCompactOperator_lpWedge _ _, finrank_range_le_two (range_lpWedge_le _ _),
    fun S hS => hS.ext h⟩

/-- At the neutral grade the flat kernel vanishes identically. -/
theorem stcFlatGapKernel_zero_grade (u : ℝ) (p q : Nat.Primes) :
    stcFlatGapKernel u 0 p q = 0 := by
  simp [stcFlatGapKernel]

/-! ### Critical half-density: finite rank throughout the strip -/

/-- The critically weighted source vector `a_p = b_0(p)/√p`. -/
def stcCriticalHalfDensity (p : Nat.Primes) : ℝ :=
  stcDepthZeroAmplitude 0 p / Real.sqrt (p : ℝ)

/-- Its grade derivative `d_p = a_p (log p) sinh(g log p)`. -/
def stcCriticalGradeDerivative (g : ℝ) (p : Nat.Primes) : ℝ :=
  stcCriticalHalfDensity p * Real.log (p : ℝ) * Real.sinh (g * Real.log (p : ℝ))

theorem stcCriticalHalfDensity_sq (p : Nat.Primes) :
    stcCriticalHalfDensity p ^ 2 = Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-2 : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  unfold stcCriticalHalfDensity
  rw [div_pow, stcDepthZeroAmplitude_sq, Real.sq_sqrt hp.le, show (-1 - 0 : ℝ) = -1 by ring,
    Real.rpow_neg_one, show (-2 : ℝ) = -1 + -1 by ring, Real.rpow_add hp, Real.rpow_neg_one]
  field_simp

theorem summable_sq_stcCriticalHalfDensity :
    Summable (fun p : Nat.Primes => stcCriticalHalfDensity p ^ 2) := by
  have h := (summable_abs_log_natCast_pow_mul_rpow_neg 2 2 (by norm_num)).comp_injective
    (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  refine h.congr fun p => ?_
  simp only [Function.comp_apply, sq_abs]
  exact (stcCriticalHalfDensity_sq p).symm

/-- The critically weighted grade derivative is square summable for every `|g| < 1/2`. -/
theorem summable_sq_stcCriticalGradeDerivative {g : ℝ} (hg : |g| < 1 / 2) :
    Summable (fun p : Nat.Primes => stcCriticalGradeDerivative g p ^ 2) := by
  have h := (summable_abs_log_natCast_pow_mul_rpow_neg 4 (2 - 2 * |g|) (by linarith)).comp_injective
    (i := fun p : Nat.Primes => (p : ℕ)) Subtype.coe_injective
  refine h.of_nonneg_of_le (fun p => sq_nonneg _) fun p => ?_
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  simp only [Function.comp_apply]
  unfold stcCriticalGradeDerivative
  rw [mul_pow, mul_pow, stcCriticalHalfDensity_sq, abs_of_nonneg hlog]
  have hsinh : Real.sinh (g * Real.log (p : ℝ)) ^ 2 ≤ (p : ℝ) ^ (2 * |g|) := by
    have hc := cosh_log_le_rpow |g| p g rfl
    have hsq := Real.cosh_sq (g * Real.log (p : ℝ))
    have hc0 := Real.cosh_pos (g * Real.log (p : ℝ))
    rw [show 2 * |g| = |g| * 2 by ring, Real.rpow_mul hp.le, Real.rpow_two]
    have := pow_le_pow_left₀ hc0.le hc 2
    linarith
  have hpow : (p : ℝ) ^ (-2 : ℝ) * (p : ℝ) ^ (2 * |g|) = (p : ℝ) ^ (-(2 - 2 * |g|)) := by
    rw [← Real.rpow_add hp]; ring_nf
  calc Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-2 : ℝ) * Real.log (p : ℝ) ^ 2 *
        Real.sinh (g * Real.log (p : ℝ)) ^ 2
      ≤ Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-2 : ℝ) * Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (2 * |g|) :=
        mul_le_mul_of_nonneg_left hsinh (by positivity)
    _ = Real.log (p : ℝ) ^ 4 * (p : ℝ) ^ (-(2 - 2 * |g|)) := by rw [← hpow]; ring

/-- Every wedge of two vectors of `ℓ²(primes)` is trace class: it factors through two orthonormal
basis vectors as a product of two Hilbert--Schmidt operators. -/
theorem isTraceClass_lpWedge_primes (x y : ℓ²P) :
    ContinuousLinearMap.IsTraceClass (lpWedge x y) := by
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  let three : Nat.Primes := ⟨3, Nat.prime_three⟩
  let e1 := lpBasisVec (I := Nat.Primes) two
  let e2 := lpBasisVec (I := Nat.Primes) three
  have h11 : ⟪e1, e1⟫_ℂ = 1 := by
    simp only [e1]; rw [inner_lpBasisVec_right]; simp [lpBasisVec]
  have h22 : ⟪e2, e2⟫_ℂ = 1 := by
    simp only [e2]; rw [inner_lpBasisVec_right]; simp [lpBasisVec]
  have hne : three ≠ two := fun h => absurd (congrArg Subtype.val h) (by decide)
  have h12 : ⟪e1, e2⟫_ℂ = 0 := by
    simp only [e1, e2]; rw [inner_lpBasisVec_right]
    simp [lpBasisVec, lp.single_apply, Pi.single_eq_of_ne hne]
  have h21 : ⟪e2, e1⟫_ℂ = 0 := by
    simp only [e1, e2]; rw [inner_lpBasisVec_right]
    simp [lpBasisVec, lp.single_apply, Pi.single_eq_of_ne hne.symm]
  refine ⟨rankOne ℂ x e1 + rankOne ℂ y e2, rankOne ℂ e1 y - rankOne ℂ e2 x,
    (isHilbertSchmidt_rankOne x e1).add (isHilbertSchmidt_rankOne y e2),
    (isHilbertSchmidt_rankOne e1 y).sub (isHilbertSchmidt_rankOne e2 x), ?_⟩
  unfold lpWedge
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_sub,
    InnerProductSpace.rankOne_comp_rankOne, h11, h22, h12, h21, one_smul, zero_smul]
  abel

/-- **Trace-class critical wedge.** Throughout the strip `|g| < 1/2`, the critically weighted
source wedge `a ∧ d` on `ℓ²(primes)` is compact, of rank at most two, and trace class; any
bounded two-sided transport of it remains compact. -/
theorem stcCriticalWedge_traceClass {g : ℝ} (hg : |g| < 1 / 2) :
    let a := lpOfReal stcCriticalHalfDensity summable_sq_stcCriticalHalfDensity
    let d := lpOfReal (stcCriticalGradeDerivative g) (summable_sq_stcCriticalGradeDerivative hg)
    IsCompactOperator (lpWedge a d) ∧
      Module.finrank ℂ (LinearMap.range ((lpWedge a d : ℓ²P →L[ℂ] ℓ²P) : ℓ²P →ₗ[ℂ] ℓ²P)) ≤ 2 ∧
      ContinuousLinearMap.IsTraceClass (lpWedge a d) ∧
      ∀ (L R : ℓ²P →L[ℂ] ℓ²P), IsCompactOperator (L ∘L lpWedge a d ∘L R) := by
  intro a d
  exact ⟨isCompactOperator_lpWedge a d, finrank_range_le_two (range_lpWedge_le a d),
    isTraceClass_lpWedge_primes a d,
    fun L R => isCompactOperator_transport (isCompactOperator_lpWedge a d) L R⟩

/-- The vertical phase `p^{iτ}` acts coordinatewise and preserves square summability. -/
def stcVerticalPhaseTwist (τ : ℝ) (f : ℓ²P) : ℓ²P :=
  ⟨fun p => ((p : ℕ) : ℂ) ^ ((τ : ℂ) * I) * (f : Nat.Primes → ℂ) p, by
    refine memℓp_gen ((summable_norm_sq_lp f).congr fun p => ?_)
    have hp : 0 < (p : ℕ) := p.property.pos
    rw [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_natCast_cpow_of_pos hp]
    simp⟩

/-- The phase-twisted critical wedge is trace class and compact as well: the vertical phase of
a zero ordinate is a unitary diagonal gauge that cannot create a nonzero Calkin class. -/
theorem stcCriticalWedge_phaseTwist_traceClass {g : ℝ} (hg : |g| < 1 / 2) (τ : ℝ) :
    let a := stcVerticalPhaseTwist τ
      (lpOfReal stcCriticalHalfDensity summable_sq_stcCriticalHalfDensity)
    let d := stcVerticalPhaseTwist τ
      (lpOfReal (stcCriticalGradeDerivative g) (summable_sq_stcCriticalGradeDerivative hg))
    IsCompactOperator (lpWedge a d) ∧ ContinuousLinearMap.IsTraceClass (lpWedge a d) := by
  intro a d
  exact ⟨isCompactOperator_lpWedge a d, isTraceClass_lpWedge_primes a d⟩

end

end RHTower
