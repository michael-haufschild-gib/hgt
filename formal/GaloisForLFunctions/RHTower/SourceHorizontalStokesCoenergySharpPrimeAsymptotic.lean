import GaloisForLFunctions.RHTower.SourceHorizontalStokesConditionedInformationCoenergy
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet

/-!
# The sharp prime–valuation asymptotic of the Stokes-conditioned coenergy

The corpus owns the exact source formulas for the complementary-coordinate information virial and
for the reflected Stokes weight, and the two-clock majorant `4(1-s)p^{-2-2se}/(e+1)²`.  This module
proves the withheld **sharp** law of ULF-SRFM-3:

`p^{2+2se} T_s(p,e) → (1-s) / (√2 (e+1)²)`  as `p → ∞` through the primes,

so the majorant carries the exact prime and valuation exponents and only its scalar constant is
nonsharp: the ratio tends to `1/(4√2)`.
-/

open Filter Topology Real

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-! ## The exact scaled product form -/

private theorem scaled_algebra {q r c V L k : ℝ} (hq : q ≠ 0) (hr : r ≠ 0)
    (hqden : (1 : ℝ) + q ≠ 0) (hL : L ≠ 0) (hk : k ≠ 0) (e : ℕ)
    (S : ℝ) (hS : S = (q ^ 2)⁻¹ * ((r ^ e) ^ 2)⁻¹) (U : ℝ) (hU : U = q ^ (e + 1) * (r ^ (e + 1))⁻¹) :
    S * (2 * q ^ (e + 1) / k * (2 * V) *
        (c ^ 2 * (q / (1 + q)) ^ 2 * (1 - r) ^ 2 * r ^ e / (k ^ 2 * L * r)))
      = 4 * c ^ 2 * (1 - r) ^ 2 / ((1 + q) ^ 2 * k ^ 3) * (U * V / L) := by
  subst hS hU
  field_simp
  ring

/-- **Exact scaled product form.**  After the sharp normalization the Stokes-conditioned coenergy
splits into a Gamma-sewn amplitude and a renormalized virial clock. -/
theorem stokesCoenergy_scaled_eq {s : ℝ} (hs : 0 < s) (p : Nat.Primes) (e : ℕ) :
    Real.exp ((2 + 2 * s * (e : ℝ)) * Real.log (p : ℝ)) *
        sourceHorizontalStokesConditionedInformationTerm s (p, e)
      = (4 * RHTower.gammaSewnMobiusValuationContractionMultiplier s p ^ 2 *
            (1 - RHTower.xiMobiusContinuousApertureDiskNode s p) ^ 2 /
          ((1 + RHTower.xiTransversePrimeApertureDiskNode 1 p) ^ 2 * ((e : ℝ) + 1) ^ 3)) *
        (Real.exp (-((1 - s) * ((e : ℝ) + 1) * Real.log (p : ℝ))) *
            sourceHorizontalHolonomyVirial ((1 - s) * ((e : ℝ) + 1) * Real.log (p : ℝ)) /
          Real.log (p : ℝ)) := by
  have hLpos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hqval : RHTower.xiTransversePrimeApertureDiskNode 1 p
      = Real.exp (-Real.log (p : ℝ)) := by
    rw [RHTower.xiTransversePrimeApertureDiskNode]
    norm_num
  have hrval : RHTower.xiMobiusContinuousApertureDiskNode s p
      = Real.exp (-(s * Real.log (p : ℝ))) := by
    rw [RHTower.xiMobiusContinuousApertureDiskNode]
    congr 1
    ring
  have hq0 : (0:ℝ) < Real.exp (-Real.log (p : ℝ)) := Real.exp_pos _
  have hr0 : (0:ℝ) < Real.exp (-(s * Real.log (p : ℝ))) := Real.exp_pos _
  have hS : Real.exp ((2 + 2 * s * (e : ℝ)) * Real.log (p : ℝ))
      = ((Real.exp (-Real.log (p : ℝ))) ^ 2)⁻¹ *
        (((Real.exp (-(s * Real.log (p : ℝ)))) ^ e) ^ 2)⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
      ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hU : Real.exp (-((1 - s) * ((e : ℝ) + 1) * Real.log (p : ℝ)))
      = (Real.exp (-Real.log (p : ℝ))) ^ (e + 1) *
        ((Real.exp (-(s * Real.log (p : ℝ)))) ^ (e + 1))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hvir : Real.exp (-Real.log (p : ℝ) * ((e : ℝ) + 1))
      = (Real.exp (-Real.log (p : ℝ))) ^ (e + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [sourceHorizontalStokesConditionedInformationTerm,
    gammaSewnMobiusApertureStokesReflectedWeight_eq_source hs p e,
    sourceHorizontalPrimeGeometricKLScaleTerm,
    sourceHorizontalPrimePowerHolonomy_scaleVirial,
    show 2 * ((e : ℝ) + 1) * Real.log (p : ℝ) * ((1 - s) / 2)
      = (1 - s) * ((e : ℝ) + 1) * Real.log (p : ℝ) from by ring,
    hqval, hrval, hvir, hS, hU]
  push_cast
  exact scaled_algebra (q := Real.exp (-Real.log (p : ℝ)))
    (r := Real.exp (-(s * Real.log (p : ℝ)))) hq0.ne' hr0.ne' (by positivity) hLpos.ne'
    (by positivity) e _ rfl _ rfl

/-! ## The renormalized virial clock -/

private theorem virialClock_eq {k L : ℝ} (hL : 0 < L) :
    Real.exp (-(k * L)) * sourceHorizontalHolonomyVirial (k * L) / L
      = k / 2 - 1 / (2 * L) + k / 2 * Real.exp (-(2 * (k * L)))
        + Real.exp (-(2 * (k * L))) / (2 * L) := by
  have hEF : Real.exp (-(k * L)) * Real.exp (k * L) = 1 := by
    rw [← Real.exp_add]; simp
  have hFF : Real.exp (-(2 * (k * L))) = Real.exp (-(k * L)) * Real.exp (-(k * L)) := by
    rw [← Real.exp_add]; congr 1; ring
  have key : Real.exp (-(k * L)) * sourceHorizontalHolonomyVirial (k * L)
      = (k * L) * (1 + Real.exp (-(2 * (k * L)))) / 2
        - (1 - Real.exp (-(2 * (k * L)))) / 2 := by
    rw [sourceHorizontalHolonomyVirial, Real.cosh_eq, Real.sinh_eq, hFF]
    linear_combination ((k * L - 1) / 2) * hEF
  rw [key]
  field_simp
  ring

/-- The renormalized virial clock converges to half the complementary rate. -/
theorem tendsto_virialClock {k : ℝ} (hk : 0 < k) :
    Tendsto (fun L : ℝ => Real.exp (-(k * L)) * sourceHorizontalHolonomyVirial (k * L) / L)
      atTop (𝓝 (k / 2)) := by
  have hEq : (fun L : ℝ => Real.exp (-(k * L)) * sourceHorizontalHolonomyVirial (k * L) / L)
      =ᶠ[atTop] fun L : ℝ => k / 2 - 1 / (2 * L) + k / 2 * Real.exp (-(2 * (k * L)))
          + Real.exp (-(2 * (k * L))) / (2 * L) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    exact virialClock_eq hL
  refine Tendsto.congr' hEq.symm ?_
  have hlin : Tendsto (fun L : ℝ => 2 * L) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have h0 : Tendsto (fun L : ℝ => 1 / (2 * L)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hlin
  have hexp : Tendsto (fun L : ℝ => Real.exp (-(2 * (k * L)))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have harg : Tendsto (fun L : ℝ => 2 * (k * L)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 2)
        (Filter.Tendsto.const_mul_atTop hk tendsto_id)
    exact tendsto_neg_atTop_atBot.comp harg
  have h1 : Tendsto (fun L : ℝ => k / 2 * Real.exp (-(2 * (k * L)))) atTop (𝓝 0) := by
    simpa using hexp.const_mul (k / 2)
  have h2 : Tendsto (fun L : ℝ => Real.exp (-(2 * (k * L))) / (2 * L)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun L : ℝ => Real.exp (-(2 * (k * L))) * (1 / (2 * L))) atTop (𝓝 (0 * 0)) :=
      hexp.mul h0
    simpa [div_eq_mul_inv, one_div] using hmul
  have hsum := ((tendsto_const_nhds (x := k / 2) (f := atTop (α := ℝ))).sub h0).add h1 |>.add h2
  simpa using hsum

/-! ## The Gamma-sewn amplitude at the prime boundary -/

private theorem tendsto_expNegScaledLog {a : ℝ} (ha : 0 < a) :
    Tendsto (fun p : Nat.Primes => Real.exp (-(a * Real.log (p : ℝ)))) cofinite (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
    (Filter.Tendsto.const_mul_atTop ha
      GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop))

/-- The true prime nodes vanish at the cofinite prime boundary. -/
theorem tendsto_xiMobiusContinuousApertureDiskNode_cofinite_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun p : Nat.Primes => RHTower.xiMobiusContinuousApertureDiskNode a p)
      cofinite (𝓝 0) := by
  refine (tendsto_expNegScaledLog ha).congr fun p => ?_
  rw [RHTower.xiMobiusContinuousApertureDiskNode]
  congr 1
  ring

/-- The unit-aperture transverse nodes vanish at the cofinite prime boundary. -/
theorem tendsto_xiTransversePrimeApertureDiskNode_one_cofinite_zero :
    Tendsto (fun p : Nat.Primes => RHTower.xiTransversePrimeApertureDiskNode 1 p)
      cofinite (𝓝 0) := by
  refine (tendsto_expNegScaledLog (a := 1) one_pos).congr fun p => ?_
  rw [RHTower.xiTransversePrimeApertureDiskNode]
  norm_num

/-- **Boundary value of the Gamma-sewn valuation contraction.**  The squared multiplier converges
to `1/(2√2)` along the cofinite prime filter at every positive aperture. -/
theorem tendsto_gammaSewnMobiusValuationContractionMultiplier_sq_cofinite {a : ℝ} (ha : 0 < a) :
    Tendsto (fun p : Nat.Primes => RHTower.gammaSewnMobiusValuationContractionMultiplier a p ^ 2)
      cofinite (𝓝 (1 / (2 * Real.sqrt 2))) := by
  have hsqrt : ∀ p : Nat.Primes,
      RHTower.gammaSewnMobiusValuationContractionMultiplier a p ^ 2
        = Real.sqrt ((1 + RHTower.xiMobiusContinuousApertureDiskNode a p) ^ 4 /
            (8 * (1 + RHTower.xiMobiusContinuousApertureDiskNode a p ^ 4))) := by
    intro p
    have h4 := RHTower.gammaSewnMobiusValuationContractionMultiplier_pow_four a p
    have hpos := RHTower.gammaSewnMobiusValuationContractionMultiplier_pos a p
    rw [← h4]
    rw [show RHTower.gammaSewnMobiusValuationContractionMultiplier a p ^ 4
        = (RHTower.gammaSewnMobiusValuationContractionMultiplier a p ^ 2) ^ 2 from by ring,
      Real.sqrt_sq (by positivity)]
  refine Tendsto.congr (fun p => (hsqrt p).symm) ?_
  have hbase : Tendsto (fun p : Nat.Primes =>
      (1 + RHTower.xiMobiusContinuousApertureDiskNode a p) ^ 4 /
        (8 * (1 + RHTower.xiMobiusContinuousApertureDiskNode a p ^ 4)))
      cofinite (𝓝 (1 / 8)) := by
    have hq := tendsto_xiMobiusContinuousApertureDiskNode_cofinite_zero ha
    have hnum : Tendsto (fun p : Nat.Primes =>
        (1 + RHTower.xiMobiusContinuousApertureDiskNode a p) ^ 4) cofinite (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).add hq).pow 4
    have hden : Tendsto (fun p : Nat.Primes =>
        8 * (1 + RHTower.xiMobiusContinuousApertureDiskNode a p ^ 4)) cofinite (𝓝 8) := by
      simpa using (((tendsto_const_nhds (x := (1:ℝ))).add (hq.pow 4))).const_mul (8:ℝ)
    have hdiv := hnum.div hden (by norm_num : (8:ℝ) ≠ 0)
    simpa [Pi.div_def] using hdiv
  have hcont : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝 (1 / 8)) (𝓝 (Real.sqrt (1 / 8))) :=
    (Real.continuous_sqrt.tendsto _)
  have hval : Real.sqrt (1 / 8 : ℝ) = 1 / (2 * Real.sqrt 2) := by
    rw [show (1 / 8 : ℝ) = (1 / (2 * Real.sqrt 2)) ^ 2 from by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hne : Real.sqrt 2 ≠ 0 := by positivity
      field_simp
      nlinarith [h2]]
    exact Real.sqrt_sq (by positivity)
  rw [← hval]
  exact hcont.comp hbase

/-! ## The sharp prime–valuation asymptotic law -/

/-- **Sharp asymptotic law (exponential normalization).** -/
theorem tendsto_stokesCoenergy_sharp_exp {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (e : ℕ) :
    Tendsto (fun p : Nat.Primes =>
        Real.exp ((2 + 2 * s * (e : ℝ)) * Real.log (p : ℝ)) *
          sourceHorizontalStokesConditionedInformationTerm s (p, e))
      cofinite (𝓝 ((1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2))) := by
  have hk : (0:ℝ) < (1 - s) * ((e : ℝ) + 1) := by
    have : (0:ℝ) < 1 - s := by linarith
    positivity
  have hamp : Tendsto (fun p : Nat.Primes =>
      4 * RHTower.gammaSewnMobiusValuationContractionMultiplier s p ^ 2 *
        (1 - RHTower.xiMobiusContinuousApertureDiskNode s p) ^ 2 /
        ((1 + RHTower.xiTransversePrimeApertureDiskNode 1 p) ^ 2 * ((e : ℝ) + 1) ^ 3))
      cofinite (𝓝 (4 * (1 / (2 * Real.sqrt 2)) * 1 / (1 * ((e : ℝ) + 1) ^ 3))) := by
    have hc := tendsto_gammaSewnMobiusValuationContractionMultiplier_sq_cofinite hs
    have hr := tendsto_xiMobiusContinuousApertureDiskNode_cofinite_zero hs
    have hq := tendsto_xiTransversePrimeApertureDiskNode_one_cofinite_zero
    have hnum : Tendsto (fun p : Nat.Primes =>
        4 * RHTower.gammaSewnMobiusValuationContractionMultiplier s p ^ 2 *
          (1 - RHTower.xiMobiusContinuousApertureDiskNode s p) ^ 2)
        cofinite (𝓝 (4 * (1 / (2 * Real.sqrt 2)) * 1)) := by
      refine (hc.const_mul (4:ℝ)).mul ?_
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub hr).pow 2
    have hden : Tendsto (fun p : Nat.Primes =>
        (1 + RHTower.xiTransversePrimeApertureDiskNode 1 p) ^ 2 * ((e : ℝ) + 1) ^ 3)
        cofinite (𝓝 (1 * ((e : ℝ) + 1) ^ 3)) := by
      refine Tendsto.mul ?_ tendsto_const_nhds
      simpa using ((tendsto_const_nhds (x := (1:ℝ))).add hq).pow 2
    exact hnum.div hden (by positivity)
  have hclock : Tendsto (fun p : Nat.Primes =>
      Real.exp (-((1 - s) * ((e : ℝ) + 1) * Real.log (p : ℝ))) *
        sourceHorizontalHolonomyVirial ((1 - s) * ((e : ℝ) + 1) * Real.log (p : ℝ)) /
        Real.log (p : ℝ))
      cofinite (𝓝 ((1 - s) * ((e : ℝ) + 1) / 2)) :=
    (tendsto_virialClock hk).comp
      GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop
  have hprod := hamp.mul hclock
  have heq : 4 * (1 / (2 * Real.sqrt 2)) * 1 / (1 * ((e : ℝ) + 1) ^ 3) *
      ((1 - s) * ((e : ℝ) + 1) / 2) = (1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2) := by
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have hke : ((e : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [← heq]
  exact Tendsto.congr (fun p => (stokesCoenergy_scaled_eq hs p e).symm) hprod

/-- **Sharp asymptotic law (ULF-SRFM-3, Theorem 3.1).**  At each fixed valuation depth the
Stokes-conditioned coenergy term has the exact prime decay `p^{-2-2se}` with the sharp constant
`(1-s)/(√2 (e+1)²)`. -/
theorem tendsto_stokesCoenergy_sharp {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (e : ℕ) :
    Tendsto (fun p : Nat.Primes =>
        (p : ℝ) ^ (2 + 2 * s * (e : ℝ)) *
          sourceHorizontalStokesConditionedInformationTerm s (p, e))
      cofinite (𝓝 ((1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2))) := by
  refine (tendsto_stokesCoenergy_sharp_exp hs hs1 e).congr fun p => ?_
  have hp : (0:ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.pos
  rw [Real.rpow_def_of_pos hp]
  ring_nf

/-- **Sharpness ratio (ULF-SRFM-3, Corollary 3.2).**  The coefficient-faithful two-clock majorant
has the exact prime and valuation exponents; only its scalar constant is nonsharp, by the universal
factor `4√2`. -/
theorem tendsto_stokesCoenergy_div_majorant {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (e : ℕ) :
    Tendsto (fun p : Nat.Primes =>
        sourceHorizontalStokesConditionedInformationTerm s (p, e) /
          sourceHorizontalStokesConditionedInformationMajorant s (p, e))
      cofinite (𝓝 (1 / (4 * Real.sqrt 2))) := by
  have hs1' : (0:ℝ) < 1 - s := by linarith
  have key : ∀ p : Nat.Primes,
      sourceHorizontalStokesConditionedInformationTerm s (p, e) /
          sourceHorizontalStokesConditionedInformationMajorant s (p, e)
        = ((e : ℝ) + 1) ^ 2 / (4 * (1 - s)) *
          (Real.exp ((2 + 2 * s * (e : ℝ)) * Real.log (p : ℝ)) *
            sourceHorizontalStokesConditionedInformationTerm s (p, e)) := by
    intro p
    have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hq : RHTower.xiTransversePrimeApertureDiskNode 1 p = Real.exp (-Real.log (p : ℝ)) := by
      rw [RHTower.xiTransversePrimeApertureDiskNode]; norm_num
    have hr : RHTower.xiMobiusContinuousApertureDiskNode s p
        = Real.exp (-(s * Real.log (p : ℝ))) := by
      rw [RHTower.xiMobiusContinuousApertureDiskNode]; congr 1; ring
    have hscale : Real.exp (-Real.log (p : ℝ)) ^ 2 *
        Real.exp (-(s * Real.log (p : ℝ))) ^ (2 * e)
          = (Real.exp ((2 + 2 * s * (e : ℝ)) * Real.log (p : ℝ)))⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    rw [sourceHorizontalStokesConditionedInformationMajorant, hq, hr]
    have hE : (0:ℝ) < Real.exp ((2 + 2 * s * (e : ℝ)) * Real.log (p : ℝ)) := Real.exp_pos _
    have hke : ((e : ℝ) + 1) ≠ 0 := by positivity
    rw [show (4 * (1 - s) * Real.exp (-Real.log (p : ℝ)) ^ 2 *
        Real.exp (-(s * Real.log (p : ℝ))) ^ (2 * e))
        = 4 * (1 - s) * (Real.exp (-Real.log (p : ℝ)) ^ 2 *
          Real.exp (-(s * Real.log (p : ℝ))) ^ (2 * e)) from by ring, hscale]
    push_cast
    field_simp
  have hmul := (tendsto_stokesCoenergy_sharp_exp hs hs1 e).const_mul
    (((e : ℝ) + 1) ^ 2 / (4 * (1 - s)))
  have heq : ((e : ℝ) + 1) ^ 2 / (4 * (1 - s)) * ((1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2))
      = 1 / (4 * Real.sqrt 2) := by
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have hke : ((e : ℝ) + 1) ≠ 0 := by positivity
    have hs' : (1 : ℝ) - s ≠ 0 := by linarith
    field_simp
  rw [← heq]
  exact Tendsto.congr (fun p => (key p).symm) hmul

/-- **Asymptotic equivalence form (ULF-SRFM-3, (3.2)).**  At fixed valuation depth the
Stokes-conditioned coenergy term is asymptotically equivalent, along the cofinite prime filter, to
the sharp power law `(1-s)(e+1)^{-2}2^{-1/2}p^{-2-2se}`. -/
theorem isEquivalent_stokesCoenergy_sharp {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (e : ℕ) :
    Asymptotics.IsEquivalent cofinite
      (fun p : Nat.Primes => sourceHorizontalStokesConditionedInformationTerm s (p, e))
      (fun p : Nat.Primes => (1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2) *
        (p : ℝ) ^ (-2 - 2 * s * (e : ℝ))) := by
  have hC : (1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2) ≠ 0 := by
    have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    have : (0:ℝ) < 1 - s := by linarith
    positivity
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have hquot :
      (fun p : Nat.Primes => sourceHorizontalStokesConditionedInformationTerm s (p, e)) /
        (fun p : Nat.Primes => (1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2) *
          (p : ℝ) ^ (-2 - 2 * s * (e : ℝ)))
        = fun p : Nat.Primes => ((Real.sqrt 2 * ((e : ℝ) + 1) ^ 2) / (1 - s)) *
          ((p : ℝ) ^ (2 + 2 * s * (e : ℝ)) *
            sourceHorizontalStokesConditionedInformationTerm s (p, e)) := by
    funext p
    have hp : (0:ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    have hrp : (p : ℝ) ^ (-2 - 2 * s * (e : ℝ)) = ((p : ℝ) ^ (2 + 2 * s * (e : ℝ)))⁻¹ := by
      rw [← Real.rpow_neg hp.le]
      congr 1
      ring
    have hpos : (0:ℝ) < (p : ℝ) ^ (2 + 2 * s * (e : ℝ)) := Real.rpow_pos_of_pos hp _
    have hs' : (1 : ℝ) - s ≠ 0 := by linarith
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have hke : ((e : ℝ) + 1) ≠ 0 := by positivity
    simp only [Pi.div_def, hrp]
    field_simp
  have hlim := (tendsto_stokesCoenergy_sharp hs hs1 e).const_mul
    ((Real.sqrt 2 * ((e : ℝ) + 1) ^ 2) / (1 - s))
  have hval : (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2) / (1 - s) *
      ((1 - s) / (Real.sqrt 2 * ((e : ℝ) + 1) ^ 2)) = 1 := by
    have hs' : (1 : ℝ) - s ≠ 0 := by linarith
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    have hke : ((e : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hval] at hlim
  rw [hquot]
  exact hlim

end

end RHTower.HedenmalmThetaSource
