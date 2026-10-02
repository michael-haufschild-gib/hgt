import GaloisForLFunctions.RHTower.RoutePMovingDepthBoundary

/-!
# The complete parabolic boundary survives at zero Xi jet

Fixed stencils at three moving depths of one prime independently retain physical
mass, centroid, and half-second moment. Their Xi jets tend strongly to zero.
Consequently the closure of the literal primitive jet/moment relation contains
every vertical vector. The centroid stencil also retains a strictly negative
complete parabolic form, so no multiple of Xi Hilbert energy pays a lower bound
for this finite signed source family.

The exact source coefficients and physical moments remain present throughout.
This classifies a source-domain obstruction; it gives no bound for the native
positive prime-head matched-minus-quantile history and does not prove RH.
-/

open Complex Set Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

def routePDepthFullMomentGraph (p : Nat.Primes) :
    Submodule ℂ (DeningerArithmeticJetHilbert × (Fin 3 → ℂ)) :=
  Submodule.span ℂ (Set.range fun e : ℕ =>
    (routePDeningerUpperSquaredCauchyJet
      (-finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)))
      (routePPrimitiveDeningerUpperPoint (p, e) 0),
      fun i => (ccmActualHeadMatchedParabolicMoment (xiGammaEulerValuationNat (p, e)) i : ℂ)))

def routePDepthFullNormalizedMoment (p : Nat.Primes) (N : ℕ) : Fin 3 → ℝ :=
  ![1, 2 * routePDepthRadius p N + routePDepthCentroidRemainder p N,
    2 * routePDepthRadius p N ^ 2 +
      Real.log (p : ℝ) ^ 2 / 6 * (routePDepthRadius p N)⁻¹ ^ 2]

def routePDepthFullNormalizedPair (p : Nat.Primes) (N : ℕ) :
    DeningerArithmeticJetHilbert × (Fin 3 → ℂ) :=
  (routePDepthMassNormalizedXiJet p (2 * N + 1),
    fun i => (routePDepthFullNormalizedMoment p N i : ℂ))

theorem routePDepthFullNormalizedPair_mem (p : Nat.Primes) (N : ℕ) :
    routePDepthFullNormalizedPair p N ∈ routePDepthFullMomentGraph p := by
  have hw : (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, 2 * N + 1)) : ℂ) ≠ 0 := by
    exact_mod_cast (routeP_depth_weight_pos p (2 * N + 1)).ne'
  have h := (routePDepthFullMomentGraph p).smul_mem
    (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, 2 * N + 1)) : ℂ)⁻¹
    (Submodule.subset_span (Set.mem_range_self (2 * N + 1)))
  convert! h using 1
  apply Prod.ext
  · exact routePDepthMassNormalizedXiJet_eq p (2 * N + 1)
  · funext i
    fin_cases i
    · simp [routePDepthFullNormalizedPair, routePDepthFullNormalizedMoment,
        ccmActualHeadMatchedParabolicMoment_zero, hw]
    · change (2 * routePDepthRadius p N + routePDepthCentroidRemainder p N : ℝ) =
        (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, 2 * N + 1)) : ℂ)⁻¹ *
          (ccmActualHeadMatchedParabolicMoment (xiGammaEulerValuationNat (p, 2 * N + 1)) 1 : ℂ)
      rw [ccmActualHeadMatchedParabolicMoment_one_eq_weight_mul_centroid]
      unfold routePDepthCentroidRemainder
      push_cast
      field_simp
      ring
    · change (2 * routePDepthRadius p N ^ 2 +
          Real.log (p : ℝ) ^ 2 / 6 * (routePDepthRadius p N)⁻¹ ^ 2 : ℝ) =
        (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, 2 * N + 1)) : ℂ)⁻¹ *
          (ccmActualHeadMatchedParabolicMoment (xiGammaEulerValuationNat (p, 2 * N + 1)) 2 : ℂ)
      have hn : 0 < xiGammaEulerValuationNat (p, 2 * N + 1) := pow_pos p.property.pos _
      rw [routeP_matched_second_arithmetic _ hn]
      push_cast
      have hnC := congrArg Complex.ofReal (routeP_even_depth_node p N)
      push_cast at hnC
      rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul, hnC, routeP_even_depth_weight]
      push_cast
      ring

private theorem even_depth_atTop : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  exact eventually_atTop.mpr ⟨B, by omega⟩

private theorem normalized_pair_jet (p : Nat.Primes) :
    Tendsto (fun N => (routePDepthFullNormalizedPair p N).1) atTop (nhds 0) :=
  (tendsto_routePDepthMassNormalizedXiJet p).comp even_depth_atTop

private theorem radius_succ (p : Nat.Primes) (N : ℕ) :
    routePDepthRadius p (N + 1) = routePDepthRadius p N * p := by
  exact pow_succ (p : ℝ) (N + 1)

private theorem inv_radius_limit (p : Nat.Primes) :
    Tendsto (fun N => (routePDepthRadius p N)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (routePDepthRadius_tendsto p)

def routePDepthSecondStencil (p : Nat.Primes) (N : ℕ) :=
  ((routePDepthRadius p N)⁻¹ ^ 2 : ℂ) • routePDepthFullNormalizedPair p N

def routePDepthFirstStencil (p : Nat.Primes) (N : ℕ) :=
  ((routePDepthRadius p N)⁻¹ : ℂ) •
    (routePDepthFullNormalizedPair p (N + 1) - (p : ℂ) ^ 2 • routePDepthFullNormalizedPair p N)

def routePDepthMassStencil (p : Nat.Primes) (N : ℕ) :=
  routePDepthFullNormalizedPair p (N + 2) -
    ((p : ℂ) + (p : ℂ) ^ 2) • routePDepthFullNormalizedPair p (N + 1) +
    (p : ℂ) ^ 3 • routePDepthFullNormalizedPair p N

private theorem second_stencil_moment (p : Nat.Primes) (N : ℕ) :
    (routePDepthSecondStencil p N).2 = fun i =>
      ((![ (routePDepthRadius p N)⁻¹ ^ 2,
        2 * (routePDepthRadius p N)⁻¹ +
          (routePDepthRadius p N)⁻¹ ^ 2 * routePDepthCentroidRemainder p N,
        2 + Real.log (p : ℝ) ^ 2 / 6 * (routePDepthRadius p N)⁻¹ ^ 4] i : ℝ) : ℂ) := by
  funext i
  have hq : (routePDepthRadius p N : ℂ) ≠ 0 := by
    exact_mod_cast (routePDepthRadius_pos p N).ne'
  fin_cases i <;>
    simp [routePDepthSecondStencil, routePDepthFullNormalizedPair,
      routePDepthFullNormalizedMoment, smul_eq_mul] <;> field_simp

private theorem first_stencil_moment (p : Nat.Primes) (N : ℕ) :
    (routePDepthFirstStencil p N).2 = fun i =>
      ((![ (1 - (p : ℝ) ^ 2) * (routePDepthRadius p N)⁻¹,
        2 * ((p : ℝ) - (p : ℝ) ^ 2) + (routePDepthRadius p N)⁻¹ *
          (routePDepthCentroidRemainder p (N + 1) -
            (p : ℝ) ^ 2 * routePDepthCentroidRemainder p N),
        Real.log (p : ℝ) ^ 2 / 6 * (routePDepthRadius p N)⁻¹ ^ 3 *
          ((p : ℝ)⁻¹ ^ 2 - (p : ℝ) ^ 2)] i : ℝ) : ℂ) := by
  funext i
  have hq : (routePDepthRadius p N : ℂ) ≠ 0 := by
    exact_mod_cast (routePDepthRadius_pos p N).ne'
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  fin_cases i <;>
    simp [routePDepthFirstStencil, routePDepthFullNormalizedPair,
      routePDepthFullNormalizedMoment, radius_succ, smul_eq_mul] <;> field_simp <;> ring

private theorem mass_stencil_moment (p : Nat.Primes) (N : ℕ) :
    (routePDepthMassStencil p N).2 = fun i =>
      ((![ 1 - (p : ℝ) - (p : ℝ) ^ 2 + (p : ℝ) ^ 3,
        routePDepthCentroidRemainder p (N + 2) -
          ((p : ℝ) + (p : ℝ) ^ 2) * routePDepthCentroidRemainder p (N + 1) +
          (p : ℝ) ^ 3 * routePDepthCentroidRemainder p N,
        Real.log (p : ℝ) ^ 2 / 6 * (routePDepthRadius p N)⁻¹ ^ 2 *
          ((p : ℝ)⁻¹ ^ 4 - ((p : ℝ) + (p : ℝ) ^ 2) * (p : ℝ)⁻¹ ^ 2 + (p : ℝ) ^ 3)] i : ℝ) : ℂ) := by
  funext i
  have hq : (routePDepthRadius p N : ℂ) ≠ 0 := by
    exact_mod_cast (routePDepthRadius_pos p N).ne'
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  fin_cases i <;>
    simp [routePDepthMassStencil, routePDepthFullNormalizedPair,
      routePDepthFullNormalizedMoment, radius_succ, smul_eq_mul] <;>
      field_simp <;> ring

theorem tendsto_routePDepthSecondStencil (p : Nat.Primes) :
    Tendsto (routePDepthSecondStencil p) atTop (nhds (0, ![0, 0, 2])) := by
  have hi := inv_radius_limit p
  have he := tendsto_routePDepthCentroidRemainder p
  have hj : Tendsto (fun N => (routePDepthSecondStencil p N).1) atTop (nhds 0) := by
    have hs := (Complex.continuous_ofReal.tendsto ((0 : ℝ) ^ 2)).comp (hi.pow 2)
    simpa [routePDepthSecondStencil] using hs.smul (normalized_pair_jet p)
  have hm : Tendsto (fun N => (routePDepthSecondStencil p N).2) atTop (nhds ![0, 0, 2]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simp_rw [second_stencil_moment]
    fin_cases i
    · simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto ((0 : ℝ) ^ 2)).comp (hi.pow 2)
    · have h := (hi.const_mul 2).add ((hi.pow 2).mul he)
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp h
    · have h := ((hi.pow 4).const_mul (Real.log (p : ℝ) ^ 2 / 6)).const_add 2
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp h
  exact hj.prodMk_nhds hm

private theorem first_stencil_jet_limit (p : Nat.Primes) :
    Tendsto (fun N => (routePDepthFirstStencil p N).1) atTop (nhds 0) := by
  have hi := inv_radius_limit p
  have hj0 := normalized_pair_jet p
  have hj1 := hj0.comp (tendsto_add_atTop_nat 1)
  have hs := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hi
  simpa [routePDepthFirstStencil] using hs.smul (hj1.sub (hj0.const_smul ((p : ℂ) ^ 2)))

private theorem first_stencil_moment_limit (p : Nat.Primes) :
    Tendsto (fun N => (routePDepthFirstStencil p N).2) atTop
      (nhds ![0, ((2 * ((p : ℝ) - (p : ℝ) ^ 2) : ℝ) : ℂ), 0]) := by
  have hi := inv_radius_limit p
  have he := tendsto_routePDepthCentroidRemainder p
  have he1 := he.comp (tendsto_add_atTop_nat 1)
  apply tendsto_pi_nhds.mpr
  intro i
  simp_rw [first_stencil_moment]
  fin_cases i
  · change Tendsto (fun N => (((1 - (p : ℝ) ^ 2) * (routePDepthRadius p N)⁻¹ : ℝ) : ℂ))
      atTop (nhds 0)
    have h : Tendsto (fun N => (1 - (p : ℝ) ^ 2) * (routePDepthRadius p N)⁻¹)
        atTop (nhds 0) := by
      simpa only [mul_zero] using hi.const_mul (1 - (p : ℝ) ^ 2)
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h
  · change Tendsto (fun N => ((2 * ((p : ℝ) - (p : ℝ) ^ 2) +
        (routePDepthRadius p N)⁻¹ * (routePDepthCentroidRemainder p (N + 1) -
          (p : ℝ) ^ 2 * routePDepthCentroidRemainder p N) : ℝ) : ℂ))
        atTop (nhds ((2 * ((p : ℝ) - (p : ℝ) ^ 2) : ℝ) : ℂ))
    have h : Tendsto (fun N => 2 * ((p : ℝ) - (p : ℝ) ^ 2) +
        (routePDepthRadius p N)⁻¹ * (routePDepthCentroidRemainder p (N + 1) -
          (p : ℝ) ^ 2 * routePDepthCentroidRemainder p N)) atTop
        (nhds (2 * ((p : ℝ) - (p : ℝ) ^ 2))) := by
      simpa only [mul_zero, sub_zero, zero_mul, add_zero, Function.comp_def] using
        (hi.mul (he1.sub (he.const_mul ((p : ℝ) ^ 2)))).const_add
          (2 * ((p : ℝ) - (p : ℝ) ^ 2))
    exact (Complex.continuous_ofReal.tendsto _).comp h
  · change Tendsto (fun N => ((Real.log (p : ℝ) ^ 2 / 6 *
        (routePDepthRadius p N)⁻¹ ^ 3 * ((p : ℝ)⁻¹ ^ 2 - (p : ℝ) ^ 2) : ℝ) : ℂ))
        atTop (nhds 0)
    have h : Tendsto (fun N => Real.log (p : ℝ) ^ 2 / 6 *
        (routePDepthRadius p N)⁻¹ ^ 3 * ((p : ℝ)⁻¹ ^ 2 - (p : ℝ) ^ 2)) atTop (nhds 0) := by
      simpa only [zero_pow (by omega : 3 ≠ 0), mul_zero, zero_mul] using
        ((hi.pow 3).const_mul (Real.log (p : ℝ) ^ 2 / 6)).mul_const
          ((p : ℝ)⁻¹ ^ 2 - (p : ℝ) ^ 2)
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h

theorem tendsto_routePDepthFirstStencil (p : Nat.Primes) :
    Tendsto (routePDepthFirstStencil p) atTop
      (nhds (0, ![0, ((2 * ((p : ℝ) - (p : ℝ) ^ 2) : ℝ) : ℂ), 0])) :=
  (first_stencil_jet_limit p).prodMk_nhds (first_stencil_moment_limit p)

theorem tendsto_routePDepthMassStencil (p : Nat.Primes) :
    Tendsto (routePDepthMassStencil p) atTop
      (nhds (0, ![((1 - (p : ℝ) - (p : ℝ) ^ 2 + (p : ℝ) ^ 3 : ℝ) : ℂ), 0, 0])) := by
  have hi := inv_radius_limit p
  have he := tendsto_routePDepthCentroidRemainder p
  have he1 := he.comp (tendsto_add_atTop_nat 1)
  have he2 := he.comp (tendsto_add_atTop_nat 2)
  have hj0 := normalized_pair_jet p
  have hj1 := hj0.comp (tendsto_add_atTop_nat 1)
  have hj2 := hj0.comp (tendsto_add_atTop_nat 2)
  have hj : Tendsto (fun N => (routePDepthMassStencil p N).1) atTop (nhds 0) := by
    simpa [routePDepthMassStencil] using
      (hj2.sub (hj1.const_smul ((p : ℂ) + (p : ℂ) ^ 2))).add (hj0.const_smul ((p : ℂ) ^ 3))
  have hm : Tendsto (fun N => (routePDepthMassStencil p N).2) atTop
      (nhds ![((1 - (p : ℝ) - (p : ℝ) ^ 2 + (p : ℝ) ^ 3 : ℝ) : ℂ), 0, 0]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simp_rw [mass_stencil_moment]
    fin_cases i
    · exact tendsto_const_nhds
    · have h := (he2.sub (he1.const_mul ((p : ℝ) + (p : ℝ) ^ 2))).add
        (he.const_mul ((p : ℝ) ^ 3))
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp h
    · have h := ((hi.pow 2).const_mul (Real.log (p : ℝ) ^ 2 / 6)).mul_const
        ((p : ℝ)⁻¹ ^ 4 - ((p : ℝ) + (p : ℝ) ^ 2) * (p : ℝ)⁻¹ ^ 2 + (p : ℝ) ^ 3)
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp h
  exact hj.prodMk_nhds hm

private theorem second_vertical_mem (p : Nat.Primes) :
    (0, ![0, 0, 2]) ∈ (routePDepthFullMomentGraph p).topologicalClosure := by
  apply mem_closure_of_tendsto (tendsto_routePDepthSecondStencil p)
  exact Eventually.of_forall fun N => (routePDepthFullMomentGraph p).smul_mem _
    (routePDepthFullNormalizedPair_mem p N)

private theorem first_vertical_mem (p : Nat.Primes) :
    (0, ![0, ((2 * ((p : ℝ) - (p : ℝ) ^ 2) : ℝ) : ℂ), 0]) ∈
      (routePDepthFullMomentGraph p).topologicalClosure := by
  apply mem_closure_of_tendsto (tendsto_routePDepthFirstStencil p)
  exact Eventually.of_forall fun N => (routePDepthFullMomentGraph p).smul_mem _
    ((routePDepthFullMomentGraph p).sub_mem (routePDepthFullNormalizedPair_mem p (N + 1))
      ((routePDepthFullMomentGraph p).smul_mem _ (routePDepthFullNormalizedPair_mem p N)))

private theorem mass_vertical_mem (p : Nat.Primes) :
    (0, ![((1 - (p : ℝ) - (p : ℝ) ^ 2 + (p : ℝ) ^ 3 : ℝ) : ℂ), 0, 0]) ∈
      (routePDepthFullMomentGraph p).topologicalClosure := by
  apply mem_closure_of_tendsto (tendsto_routePDepthMassStencil p)
  exact Eventually.of_forall fun N => (routePDepthFullMomentGraph p).add_mem
    ((routePDepthFullMomentGraph p).sub_mem (routePDepthFullNormalizedPair_mem p (N + 2))
      ((routePDepthFullMomentGraph p).smul_mem _ (routePDepthFullNormalizedPair_mem p (N + 1))))
    ((routePDepthFullMomentGraph p).smul_mem _ (routePDepthFullNormalizedPair_mem p N))

/-- Every physical parabolic boundary vector survives at Xi jet zero. The witnesses use at
most three moving-depth atoms of one fixed prime, with their exact original coefficients. -/
theorem routePDepthFullMomentGraph_vertical_mem (p : Nat.Primes) (v : Fin 3 → ℂ) :
    (0, v) ∈ (routePDepthFullMomentGraph p).topologicalClosure := by
  let a : ℝ := 1 - (p : ℝ) - (p : ℝ) ^ 2 + (p : ℝ) ^ 3
  let b : ℝ := 2 * ((p : ℝ) - (p : ℝ) ^ 2)
  have hp : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have ha : a ≠ 0 := by
    have he : a = ((p : ℝ) - 1) * ((p : ℝ) ^ 2 - 1) := by dsimp [a]; ring
    rw [he]
    exact (mul_pos (by linarith) (by nlinarith)).ne'
  have hb : b ≠ 0 := by dsimp [b]; nlinarith
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  let G := (routePDepthFullMomentGraph p).topologicalClosure
  have h0 : (0, ![(a : ℂ), 0, 0]) ∈ G := mass_vertical_mem p
  have h1 : (0, ![0, (b : ℂ), 0]) ∈ G := first_vertical_mem p
  have h := G.add_mem
    (G.add_mem (G.smul_mem (v 0 / (a : ℂ)) h0)
      (G.smul_mem (v 1 / (b : ℂ)) h1))
    (G.smul_mem (v 2 / 2) (second_vertical_mem p))
  convert! h using 1
  apply Prod.ext
  · simp
  · funext i
    fin_cases i <;> simp [smul_eq_mul, haC, hbC]

theorem routePDepthFullMomentGraph_vertical_fiber (p : Nat.Primes) :
    {v : Fin 3 → ℂ | (0, v) ∈ (routePDepthFullMomentGraph p).topologicalClosure} = Set.univ := by
  exact Set.eq_univ_of_forall (routePDepthFullMomentGraph_vertical_mem p)

/-- The complete parabolic form of the literal first-moment stencil. -/
def routePDepthFirstStencilForm (p : Nat.Primes) (N : ℕ) : ℝ :=
  ccmParabolicForm (fun i => ((routePDepthFirstStencil p N).2 i).re)

/-- The surviving centroid boundary is timelike, not a null second-moment vector. -/
theorem tendsto_routePDepthFirstStencilForm (p : Nat.Primes) :
    Tendsto (routePDepthFirstStencilForm p) atTop
      (nhds (-(2 * ((p : ℝ) - (p : ℝ) ^ 2)) ^ 2)) := by
  have h := tendsto_pi_nhds.mp (first_stencil_moment_limit p)
  have h0 : Tendsto (fun N => ((routePDepthFirstStencil p N).2 0).re) atTop (nhds 0) := by
    convert! (Complex.continuous_re.tendsto _).comp (h 0) using 1
  have h1 : Tendsto (fun N => ((routePDepthFirstStencil p N).2 1).re) atTop
      (nhds (2 * ((p : ℝ) - (p : ℝ) ^ 2))) := by
    convert! (Complex.continuous_re.tendsto _).comp (h 1) using 1
  have h2 : Tendsto (fun N => ((routePDepthFirstStencil p N).2 2).re) atTop (nhds 0) := by
    convert! (Complex.continuous_re.tendsto _).comp (h 2) using 1
  convert! ((h0.const_mul 2).mul h2).sub (h1.pow 2) using 1
  simp

/-- The Xi Hilbert energy cannot pay even a finite lower bound for these complete physical
forms. This concerns signed primitive packets, not the native positive prime-head history. -/
theorem not_routePDepthFirstStencilForm_lower_bounded_by_Xi (p : Nat.Primes) :
    ¬ ∃ C : ℝ, ∀ N : ℕ,
      -C * ‖(routePDepthFirstStencil p N).1‖ ^ 2 ≤ routePDepthFirstStencilForm p N := by
  rintro ⟨C, hC⟩
  have hb : 2 * ((p : ℝ) - (p : ℝ) ^ 2) ≠ 0 := by
    have hp : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
    nlinarith
  have hn := ((first_stencil_jet_limit p).norm.pow 2).const_mul C
  have ht : Tendsto (fun N => routePDepthFirstStencilForm p N +
      C * ‖(routePDepthFirstStencil p N).1‖ ^ 2) atTop
      (nhds (-(2 * ((p : ℝ) - (p : ℝ) ^ 2)) ^ 2)) := by
    simpa only [norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] using
      (tendsto_routePDepthFirstStencilForm p).add hn
  obtain ⟨N, hN⟩ := (ht.eventually_lt_const (neg_neg_of_pos (sq_pos_of_ne_zero hb))).exists
  have h := hC N
  linarith

end
end RHTower
