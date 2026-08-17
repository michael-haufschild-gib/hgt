import Mathlib
import GaloisForLFunctions.HTGeometry.HelsonZetaMeasurable

/-!
# Analytic properties of the Helson zeta function on the half plane of absolute convergence

The Euler factors of a unimodular phase differ from `1` by at most `2 p^{-σ}` uniformly on
`Re s ≥ σ > 1`, so the product converges uniformly there — uniformly in `s` on every such half
plane, and uniformly in the phase on the whole torus.  Consequently

* `s ↦ Z(χ, s)` is holomorphic on `Re s > 1`,
* `χ ↦ Z(χ, s)` is continuous on the phase torus for each such `s`,
* `Z(χ, s) ≠ 0`, because the product of the Euler factors with their inverses is `1`.

Holomorphy in `s` and continuity in `χ` are the two inputs a descriptive-set-theoretic analysis of
the continuation stratum needs: the first to speak of Taylor coefficients at all, the second to make
the defining conditions closed.
-/

open Complex Filter Topology

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The phase torus is compact. -/
instance : CompactSpace PhaseTorus := by
  have hsph : IsCompact {z : ℂ | ‖z‖ = 1} := by
    have : {z : ℂ | ‖z‖ = 1} = Metric.sphere (0 : ℂ) 1 := by
      ext z
      simp
    rw [this]
    exact isCompact_sphere _ _
  haveI : CompactSpace {z : ℂ // ‖z‖ = 1} := isCompact_iff_compactSpace.mp hsph
  infer_instance

/-- Every coordinate of a point of the phase torus is unimodular. -/
theorem norm_phase_le_one (χ : PhaseTorus) (p : Nat.Primes) : ‖(χ p : ℂ)‖ ≤ 1 :=
  le_of_eq (χ p).2

/-- A uniform bound for the Euler factors on a closed half plane. -/
theorem norm_eulerFactor_sub_one_le_of_re_ge (χ : PhaseTorus) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖(1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-σ) := by
  have h1 : 1 < s.re := lt_of_lt_of_le hσ hs
  have h := norm_eulerFactor_sub_one_le (χ := fun p : Nat.Primes => (χ p : ℂ))
    (norm_phase_le_one χ) h1 p
  refine h.trans ?_
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    exact_mod_cast p.2.one_lt.le
  have hmono : ((p : ℕ) : ℝ) ^ (-s.re) ≤ ((p : ℕ) : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  linarith

/-- The Euler factor as a function of `s`, written through the exponential. -/
theorem eulerFactor_eq_exp (χ : PhaseTorus) (p : Nat.Primes) (s : ℂ) :
    (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹
      = (1 - (χ p : ℂ) * Complex.exp (Complex.log ((p : ℕ) : ℂ) * (-s)))⁻¹ := by
  have hne : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).2 p.2.ne_zero
  rw [Complex.cpow_def_of_ne_zero hne]

/-- The Euler factor is differentiable in `s` on the half plane of absolute convergence. -/
theorem differentiableOn_eulerFactor (χ : PhaseTorus) (p : Nat.Primes) {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (fun s : ℂ => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      {s : ℂ | σ < s.re} := by
  have hne : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).2 p.2.ne_zero
  have hrw : (fun s : ℂ => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      = fun s : ℂ => (1 - (χ p : ℂ) * Complex.exp (Complex.log ((p : ℕ) : ℂ) * (-s)))⁻¹ := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hne]
  rw [hrw]
  intro s hs
  have hsre : 1 < s.re := lt_trans hσ hs
  have hden : (1 : ℂ) - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) ≠ 0 :=
    one_sub_phase_prime_cpow_ne_zero (χ := fun p : Nat.Primes => (χ p : ℂ))
      (norm_phase_le_one χ) hsre
  have hden' : (1 : ℂ) - (χ p : ℂ) * Complex.exp (Complex.log ((p : ℕ) : ℂ) * (-s)) ≠ 0 := by
    rwa [← Complex.cpow_def_of_ne_zero hne]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.inv ?_ hden'
  refine DifferentiableAt.sub (differentiableAt_const _) ?_
  refine (differentiableAt_const _).mul ?_
  exact Complex.differentiable_exp.differentiableAt.comp s
    ((differentiableAt_const _).mul differentiableAt_id.neg)

/-- The Euler factor is continuous in the phase. -/
theorem continuous_eulerFactor_phase {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    Continuous (fun χ : PhaseTorus => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) := by
  have hcoord : Continuous (fun χ : PhaseTorus => (χ p : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply p)
  refine Continuous.inv₀ ((continuous_const).sub (hcoord.mul continuous_const)) ?_
  intro χ
  exact one_sub_phase_prime_cpow_ne_zero (χ := fun p : Nat.Primes => (χ p : ℂ))
    (norm_phase_le_one χ) hs

/-- **The Euler product converges locally uniformly in `s`.** -/
theorem hasProdLocallyUniformlyOn_helsonEuler (χ : PhaseTorus) {σ : ℝ} (hσ : 1 < σ) :
    HasProdLocallyUniformlyOn
      (fun (p : Nat.Primes) (s : ℂ) => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (fun s : ℂ => helsonZetaValue s χ) {s : ℂ | σ < s.re} := by
  have hopen : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hu : Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-σ)) :=
    (summable_prime_rpow_neg hσ).mul_left 2
  have hbound : ∀ᶠ p : Nat.Primes in cofinite, ∀ s ∈ {s : ℂ | σ < s.re},
      ‖(1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-σ) := by
    filter_upwards with p s hs
    exact norm_eulerFactor_sub_one_le_of_re_ge χ hσ (le_of_lt hs) p
  have hcts : ∀ p : Nat.Primes,
      ContinuousOn (fun s : ℂ => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1)
        {s : ℂ | σ < s.re} := fun p =>
    ((differentiableOn_eulerFactor χ p hσ).continuousOn).sub continuousOn_const
  have hmain := Summable.hasProdLocallyUniformlyOn_one_add (K := {s : ℂ | σ < s.re})
    (f := fun (p : Nat.Primes) (s : ℂ) => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1)
    hopen hu hbound hcts
  have hfun : (fun s : ℂ => ∏' p : Nat.Primes,
      (1 + ((1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1)))
      = fun s : ℂ => helsonZetaValue s χ := by
    funext s
    rw [helsonZetaValue]
    exact tprod_congr fun p => by ring
  rw [hfun] at hmain
  simpa only [add_sub_cancel] using hmain

/-- **The Helson zeta function is holomorphic on the half plane of absolute convergence.** -/
theorem differentiableOn_helsonZetaValue (χ : PhaseTorus) :
    DifferentiableOn ℂ (fun s : ℂ => helsonZetaValue s χ) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs' : 1 < s.re := hs
  set σ : ℝ := (1 + s.re) / 2 with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hsσ : σ < s.re := by rw [hσdef]; linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hlu := hasProdLocallyUniformlyOn_helsonEuler χ hσ1
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => helsonZetaValue z χ) {z : ℂ | σ < z.re} := by
    refine TendstoLocallyUniformlyOn.differentiableOn hlu ?_ hopen
    filter_upwards with P
    have hfp := DifferentiableOn.finsetProd (u := P) (s := {z : ℂ | σ < z.re})
      (f := fun (p : Nat.Primes) (z : ℂ) => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-z))⁻¹)
      (fun p _ => differentiableOn_eulerFactor χ p hσ1)
    have heq : (∏ i ∈ P, fun z : ℂ => (1 - (χ i : ℂ) * ((i : ℕ) : ℂ) ^ (-z))⁻¹)
        = fun z : ℂ => ∏ i ∈ P, (1 - (χ i : ℂ) * ((i : ℕ) : ℂ) ^ (-z))⁻¹ := by
      funext z
      simp [Finset.prod_apply]
    rw [heq] at hfp
    exact hfp
  exact ((hdiff.differentiableAt (hopen.mem_nhds hsσ)).differentiableWithinAt)

/-- **The Helson zeta function is continuous in the phase.** -/
theorem continuous_helsonZetaValue {s : ℂ} (hs : 1 < s.re) :
    Continuous (helsonZetaValue s) := by
  have hcompact : IsCompact (Set.univ : Set PhaseTorus) := isCompact_univ
  have hu : Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-s.re)) :=
    (summable_prime_rpow_neg hs).mul_left 2
  have hbound : ∀ᶠ p : Nat.Primes in cofinite, ∀ χ ∈ (Set.univ : Set PhaseTorus),
      ‖(1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-s.re) := by
    filter_upwards with p χ _
    exact norm_eulerFactor_sub_one_le (χ := fun p : Nat.Primes => (χ p : ℂ))
      (norm_phase_le_one χ) hs p
  have hcts : ∀ p : Nat.Primes,
      ContinuousOn (fun χ : PhaseTorus => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1)
        Set.univ := fun p =>
    ((continuous_eulerFactor_phase hs p).sub continuous_const).continuousOn
  have hmain := Summable.hasProdUniformlyOn_one_add (K := (Set.univ : Set PhaseTorus))
    (f := fun (p : Nat.Primes) (χ : PhaseTorus) => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1)
    hcompact hu hbound hcts
  have huniform := hmain.tendstoUniformlyOn
  have hcont : ContinuousOn (fun χ : PhaseTorus => ∏' p : Nat.Primes,
      (1 + ((1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1))) Set.univ := by
    refine huniform.continuousOn (Filter.Eventually.frequently ?_)
    filter_upwards with P
    exact continuousOn_finsetProd _ fun p _ =>
      (continuous_const.add ((continuous_eulerFactor_phase hs p).sub continuous_const)).continuousOn
  have hfun : (fun χ : PhaseTorus => ∏' p : Nat.Primes,
      (1 + ((1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ - 1)))
      = helsonZetaValue s := by
    funext χ
    rw [helsonZetaValue]
    exact tprod_congr fun p => by ring
  rw [hfun] at hcont
  exact continuousOn_univ.mp hcont

/-- **The Helson zeta function does not vanish on the half plane of absolute convergence.** -/
theorem helsonZetaValue_ne_zero {s : ℂ} (hs : 1 < s.re) (χ : PhaseTorus) :
    helsonZetaValue s χ ≠ 0 := by
  have hunit : ∀ p : Nat.Primes, ‖(χ p : ℂ)‖ ≤ 1 := norm_phase_le_one χ
  have hinv : Multipliable (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) :=
    multipliable_helsonEuler hunit hs
  have hden : Multipliable (fun p : Nat.Primes => 1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s)) := by
    have hsum : Summable (fun p : Nat.Primes => ‖-((χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))‖) := by
      refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) ?_ (summable_prime_rpow_neg hs)
      intro p
      rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
      calc ‖(χ p : ℂ)‖ * ((p : ℕ) : ℝ) ^ (-s.re)
          ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (hunit p) (Real.rpow_nonneg (by positivity) _)
        _ = ((p : ℕ) : ℝ) ^ (-s.re) := one_mul _
    have := multipliable_one_add_of_summable hsum
    exact this.congr fun p => by ring
  have hprod : (∏' p : Nat.Primes, (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      * (∏' p : Nat.Primes, (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))) = 1 := by
    rw [← Multipliable.tprod_mul hinv hden]
    have : ∀ p : Nat.Primes,
        (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹ * (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s)) = 1 :=
      fun p => inv_mul_cancel₀ (one_sub_phase_prime_cpow_ne_zero hunit hs)
    rw [tprod_congr this, tprod_one]
  intro hzero
  rw [helsonZetaValue] at hzero
  rw [hzero, zero_mul] at hprod
  exact zero_ne_one hprod

end GaloisForLFunctions.HTGeometry

end
