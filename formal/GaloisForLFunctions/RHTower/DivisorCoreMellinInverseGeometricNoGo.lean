import GaloisForLFunctions.RHTower.DivisorCoreMellinBoundary
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleNoLimit

/-!
# Growing-core inverse-geometric amplification of the literal divisor Mellin factor

At the square-root Mellin boundary, each processed prime factor, normalized by its
zero-frequency value, is a unit phase times the reciprocal of the characteristic
factor of a geometric prime-log occupation.  The prime phase-defect theorem from
the Abelian zeta-gas corpus applies at the exact exponent `1/2`: for every fixed
nonzero frequency, the sum of defects diverges.  Consequently the norm of the
literal finite-core Euler multiplier divided by its residue factor tends to
infinity as the prime core grows.

This rules out core-uniform pointwise domination by the Mellin residue.  It does
not control the Fourier integral, signed source covariance, or endpoint terms:
those can still cancel across frequencies and require source-specific analysis.
-/

open Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem half_pos : (0 : ℝ) < 1 / 2 := by norm_num

/-- The geometric prime-log modulus debt at Route T's exact half-density exponent. -/
noncomputable def routeTInverseGeomDefect (t : ℝ) (p : Nat.Primes) : ℝ :=
  geomDefect (primeNome half_pos p).val (phaseAngle (primeNome half_pos p) (2 * t))

theorem routeTInverseGeomDefect_nonneg (t : ℝ) (p : Nat.Primes) :
    0 ≤ routeTInverseGeomDefect t p := by
  exact geomDefect_nonneg (primeNome half_pos p).pos
    (primeNome half_pos p).lt_one _

/-- At every fixed nonzero frequency, the prime-indexed inverse-smoothing debt diverges. -/
theorem not_summable_routeTInverseGeomDefect {t : ℝ} (ht : t ≠ 0) :
    ¬ Summable (routeTInverseGeomDefect t) := by
  intro hs
  have hlead := not_summable_leading (σ := (1 / 2 : ℝ)) (t := 2 * t)
    half_pos (by norm_num : (1 / 2 : ℝ) ≤ 1)
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ht)
  apply hlead
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) (hs.mul_left 4)
  · have hcos := Real.cos_le_one (phaseAngle (primeNome half_pos p) (2 * t))
    have hq := (primeNome half_pos p).pos
    dsimp [primeNome]
    positivity
  · have hge := geomDefect_ge (primeNome half_pos p).pos
      (primeNome half_pos p).lt_one (phaseAngle (primeNome half_pos p) (2 * t))
    change (primeNome half_pos p).val *
      (1 - Real.cos (phaseAngle (primeNome half_pos p) (2 * t))) ≤
        4 * routeTInverseGeomDefect t p
    unfold routeTInverseGeomDefect
    linarith

theorem tendsto_routeTInverseGeomDefect_sum {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun s : Finset Nat.Primes => ∑ p ∈ s, routeTInverseGeomDefect t p)
      atTop atTop :=
  tendsto_finsetSum_atTop_of_not_summable
    (routeTInverseGeomDefect_nonneg t) (not_summable_routeTInverseGeomDefect ht)

private theorem norm_geomFactor_pos (q φ : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < ‖geomFactor q φ‖ := by
  rw [norm_geomFactor hq1]
  have hden := norm_one_sub_geom_pos hq0 hq1 φ
  positivity

private theorem inverse_geom_factor_identity (q φ : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (1 - ((q : ℂ)⁻¹) * Complex.exp (-((φ : ℂ) * Complex.I))) /
        (1 - (q : ℂ)⁻¹) =
      Complex.exp (-((φ : ℂ) * Complex.I)) * (geomFactor q φ)⁻¹ := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have h1 : 1 - (q : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_gt hq1 : (1 : ℝ) ≠ q)
  have h1' : (q : ℂ) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (ne_of_lt hq1 : q ≠ (1 : ℝ))
  have hz : Complex.exp ((φ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hzq : 1 - (q : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) ≠ 0 := by
    have hn := norm_one_sub_geom_pos hq0 hq1 φ
    exact ne_zero_of_norm_ne_zero (ne_of_gt hn)
  unfold geomFactor
  rw [Complex.exp_neg]
  field_simp [hq, h1, h1', hz, hzq]
  ring

/-- One normalized Mellin Euler factor in inverse-geometric coordinates. -/
noncomputable def routeTNormalizedPrimeEuler (t : ℝ) (p : Nat.Primes) : ℂ :=
  let q := (primeNome half_pos p).val
  let φ := phaseAngle (primeNome half_pos p) (2 * t)
  (1 - ((q : ℂ)⁻¹) * Complex.exp (-((φ : ℂ) * Complex.I))) /
    (1 - (q : ℂ)⁻¹)

theorem norm_routeTNormalizedPrimeEuler (t : ℝ) (p : Nat.Primes) :
    ‖routeTNormalizedPrimeEuler t p‖ =
      Real.exp (routeTInverseGeomDefect t p) := by
  let q := (primeNome half_pos p).val
  let φ := phaseAngle (primeNome half_pos p) (2 * t)
  have hq0 : 0 < q := (primeNome half_pos p).pos
  have hq1 : q < 1 := (primeNome half_pos p).lt_one
  have hpos := norm_geomFactor_pos q φ hq0 hq1
  rw [routeTNormalizedPrimeEuler, inverse_geom_factor_identity q φ hq0 hq1,
    norm_mul]
  have hexp : ‖Complex.exp (-((φ : ℂ) * Complex.I))‖ = 1 := by
    have he : -((φ : ℂ) * Complex.I) = ((-φ : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, Complex.norm_exp_ofReal_mul_I]
  rw [hexp, one_mul, norm_inv]
  change (‖geomFactor q φ‖)⁻¹ = Real.exp (geomDefect q φ)
  rw [geomDefect, Real.exp_neg, Real.exp_log hpos]

noncomputable def routeTNormalizedEulerCore (t : ℝ) (s : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ s, routeTNormalizedPrimeEuler t p

theorem norm_routeTNormalizedEulerCore (t : ℝ) (s : Finset Nat.Primes) :
    ‖routeTNormalizedEulerCore t s‖ =
      Real.exp (∑ p ∈ s, routeTInverseGeomDefect t p) := by
  rw [routeTNormalizedEulerCore, norm_prod, Real.exp_sum]
  exact Finset.prod_congr rfl (fun p _ => norm_routeTNormalizedPrimeEuler t p)

theorem tendsto_norm_routeTNormalizedEulerCore_atTop {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun s : Finset Nat.Primes => ‖routeTNormalizedEulerCore t s‖)
      atTop atTop := by
  have h := Real.tendsto_exp_atTop.comp (tendsto_routeTInverseGeomDefect_sum ht)
  exact h.congr' (Filter.Eventually.of_forall fun s => (norm_routeTNormalizedEulerCore t s).symm)

private theorem prime_nome_half_exp (p : Nat.Primes) :
    (primeNome half_pos p).val = Real.exp (-Real.log (p : ℝ) / 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [primeNome_val, Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- The inverse-geometric factor is the literal one-prime divisor-core multiplier. -/
theorem divisorCoreMellinEuler_singleton_ratio (t : ℝ) (p : Nat.Primes) :
    divisorCoreMellinEuler {(p : ℕ)} ((t : ℂ) * Complex.I) /
        divisorCoreMellinEuler {(p : ℕ)} 0 = routeTNormalizedPrimeEuler t p := by
  let q : ℝ := (primeNome half_pos p).val
  let φ : ℝ := phaseAngle (primeNome half_pos p) (2 * t)
  let L : ℝ := Real.log (p : ℝ)
  have hqi : (q : ℂ)⁻¹ = Complex.exp ((1 / 2 : ℂ) * (L : ℂ)) := by
    rw [show q = Real.exp (-L / 2) by exact prime_nome_half_exp p,
      Complex.ofReal_exp, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hphase : φ = t * L := by
    dsimp [φ, L]
    rw [phaseAngle_primeNome half_pos]
    ring
  have harg : ((1 / 2 : ℂ) - (t : ℂ) * Complex.I) * (L : ℂ) =
      (1 / 2 : ℂ) * (L : ℂ) - (φ : ℂ) * Complex.I := by
    rw [hphase]
    push_cast
    ring
  simp only [divisorCoreMellinEuler, Finset.prod_singleton]
  change (1 - Complex.exp (((1 / 2 : ℂ) - (t : ℂ) * Complex.I) * (L : ℂ))) /
      (1 - Complex.exp (((1 / 2 : ℂ) - 0) * (L : ℂ))) =
    (1 - (q : ℂ)⁻¹ * Complex.exp (-((φ : ℂ) * Complex.I))) /
      (1 - (q : ℂ)⁻¹)
  have hden : Complex.exp (((1 / 2 : ℂ) - 0) * (L : ℂ)) = (q : ℂ)⁻¹ := by
    simpa using hqi.symm
  rw [hden, harg, Complex.exp_sub, ← hqi, Complex.exp_neg]
  simp only [div_eq_mul_inv]

/-- Exact identification of the full finite processed-prime core. -/
theorem divisorCoreMellinEuler_ratio_eq_inverse_geom
    (t : ℝ) (s : Finset Nat.Primes) :
    divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ)))
      ((t : ℂ) * Complex.I) /
      divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ))) 0 =
        routeTNormalizedEulerCore t s := by
  have himg : ∀ z : ℂ,
      divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ))) z =
        ∏ p ∈ s, divisorCoreMellinEuler {(p : ℕ)} z := by
    intro z
    simp only [divisorCoreMellinEuler, Finset.prod_singleton]
    rw [Finset.prod_image]
    intro a ha b hb hab
    exact Subtype.ext hab
  rw [himg, himg, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl (fun p _ => divisorCoreMellinEuler_singleton_ratio t p)

/-- The literal core is a deterministic phase times the inverse of a positive
geometric prime-log characteristic product. -/
theorem divisorCoreMellinEuler_ratio_eq_inverse_geometricProduct
    (t : ℝ) (s : Finset Nat.Primes) :
    divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ)))
      ((t : ℂ) * Complex.I) /
      divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ))) 0 =
        (∏ p ∈ s, Complex.exp (-((phaseAngle (primeNome half_pos p) (2 * t) : ℂ) *
          Complex.I))) *
        (∏ p ∈ s, geomFactor (primeNome half_pos p).val
          (phaseAngle (primeNome half_pos p) (2 * t)))⁻¹ := by
  rw [divisorCoreMellinEuler_ratio_eq_inverse_geom, routeTNormalizedEulerCore]
  calc
    (∏ p ∈ s, routeTNormalizedPrimeEuler t p) =
        ∏ p ∈ s, Complex.exp (-((phaseAngle (primeNome half_pos p) (2 * t) : ℂ) *
          Complex.I)) *
          (geomFactor (primeNome half_pos p).val
            (phaseAngle (primeNome half_pos p) (2 * t)))⁻¹ := by
              apply Finset.prod_congr rfl
              intro p hp
              exact inverse_geom_factor_identity _ _ (primeNome half_pos p).pos
                (primeNome half_pos p).lt_one
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

/-- No core-independent pointwise residue-dominance constant exists at a nonzero frequency. -/
theorem tendsto_divisorCoreMellinEuler_ratio_norm_atTop {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun s : Finset Nat.Primes =>
      ‖divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ)))
        ((t : ℂ) * Complex.I) /
        divisorCoreMellinEuler (s.image (fun p : Nat.Primes => (p : ℕ))) 0‖)
      atTop atTop := by
  simpa only [divisorCoreMellinEuler_ratio_eq_inverse_geom] using
    tendsto_norm_routeTNormalizedEulerCore_atTop ht

end RHTower
