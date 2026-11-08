import GaloisForLFunctions.ArithmeticCorrespondencePositivity.EveryXiZeroHasASourceField
import GaloisForLFunctions.RHTower.STCPrimeHeightFiberAbel

/-!+# The source field carried by distinct prime pairs

Let `P = -ζ′/ζ - H`, where `H` contains the proper prime powers. The diagonal
of `P²` is analytic on `Re s > 1/2`. Removing it leaves the ordered
distinct-prime pair source. At a zeta zero of multiplicity `m`, its simple
Laurent coefficient is the coefficient of `(ζ′/ζ)²` plus `2mH(ρ)`.
Thus the analytic prime-power tail survives in the nonlinear source field.
-/

open Filter Set RHTower
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.HTGeometry

/-- The same-prime diagonal of the square of the prime-log current. -/
def primePairDiagonal (s : ℂ) : ℂ :=
  -deriv xiPrimeLogDirichletContinuation (2 * s)

/-- The continued ordered distinct-prime pair source. -/
def primePairSource (s : ℂ) : ℂ :=
  xiPrimeLogDirichletContinuation s ^ 2 - primePairDiagonal s

private theorem analyticAt_primeLogContinuation {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ xiPrimeLogDirichletContinuation s := by
  have hdiff : DifferentiableOn ℂ xiPrimeLogDirichletContinuation {z : ℂ | 1 < z.re} :=
    fun z hz => (differentiableAt_xiPrimeLogDirichletContinuation_of_one_lt_re hz).differentiableWithinAt
  exact (hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)) s hs

/-- Proper prime powers are analytic throughout the open right half-strip. -/
theorem analyticAt_primePowerTail {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ xiPrimeLogHigherValuation s :=
  (differentiableOn_xiPrimeLogHigherValuation_halfPlane.analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)) s hs

/-- The diagonal is the absolutely convergent log-square prime series at `2s`. -/
theorem primePairDiagonal_eq {s : ℂ} (hs : 1 / 2 < s.re) :
    primePairDiagonal s = primeLogSquareComplex (2 * s) := by
  have htwo : 1 < (2 * s).re := by
    rw [two_mul, Complex.add_re]
    linarith only [hs]
  exact (primeLogSquareComplex_eq_neg_deriv_continuation htwo).symm

/-- The prime diagonal contributes no pole to the source in `Re s > 1/2`. -/
theorem analyticAt_primePairDiagonal {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ primePairDiagonal s := by
  have htwo : 1 < (2 * s).re := by
    rw [two_mul, Complex.add_re]
    linarith only [hs]
  exact (analyticAt_primeLogContinuation htwo).deriv.neg.comp (by fun_prop)

private theorem tsum_square_sub_diagonal {ι : Type*} [DecidableEq ι]
    (f : ι → ℂ) (hnorm : Summable (fun p => ‖f p‖)) :
    (∑' p, f p) ^ 2 - ∑' p, f p ^ 2 =
      ∑' p, ∑' q, if q = p then 0 else f p * f q := by
  have hf : Summable f := hnorm.of_norm
  have hprod : Summable (fun pq : ι × ι => f pq.1 * f pq.2) :=
    summable_mul_of_summable_norm hnorm hnorm
  have hdiag : Summable (fun p => f p ^ 2) := by
    have h := hprod.comp_injective (i := fun p => (p, p))
      (fun _ _ h => congrArg Prod.fst h)
    change Summable (fun p => f p * f p) at h
    simpa only [pow_two] using h
  have hrow : Summable (fun p => ∑' q, f p * f q) := hprod.prod
  have hsplit (p : ι) :
      (∑' q, f p * f q) - f p ^ 2 =
        ∑' q, if q = p then 0 else f p * f q := by
    rw [(hf.mul_left (f p)).tsum_eq_add_tsum_ite p, pow_two]
    ring
  calc
    (∑' p, f p) ^ 2 - ∑' p, f p ^ 2 =
        (∑' p, ∑' q, f p * f q) - ∑' p, f p ^ 2 := by
      rw [pow_two, hf.tsum_mul_tsum hf hprod, hprod.tsum_prod]
    _ = ∑' p, ((∑' q, f p * f q) - f p ^ 2) := (hrow.tsum_sub hdiag).symm
    _ = _ := tsum_congr hsplit

/-- On the Euler half-plane the continued source is the literal ordered
distinct-prime pair series, with positive coefficient `(log p)(log q)`. -/
theorem primePairSource_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    primePairSource s =
      ∑' p : Nat.Primes, ∑' q : Nat.Primes,
        if q = p then 0 else
          ((Real.log (p : ℝ) : ℂ) / (p : ℂ) ^ s) *
            ((Real.log (q : ℝ) : ℂ) / (q : ℂ) ^ s) := by
  let f : Nat.Primes → ℂ := fun p => (Real.log (p : ℝ) : ℂ) / (p : ℂ) ^ s
  have hf : Summable f :=
    (summable_xiPrimeLogDirichlet_term hs).congr (xiPrimeLogDirichlet_term_eq s)
  have hP : xiPrimeLogDirichletContinuation s = ∑' p, f p :=
    (xiPrimeLogDirichletContinuation_eq hs).trans
      (xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs)
  have hdiag : primePairDiagonal s = ∑' p, f p ^ 2 := by
    rw [primePairDiagonal_eq (by linarith only [hs]), primeLogSquareComplex]
    apply tsum_congr
    intro p
    have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
    dsimp only [f]
    rw [show -(2 * s) = -(s + s) by ring,
      Complex.cpow_neg, Complex.cpow_add s s hp, ← pow_two, div_pow]
    rfl
  rw [primePairSource, hP, hdiag]
  exact tsum_square_sub_diagonal f (summable_norm_iff.mpr hf)

private theorem meromorphicAt_zetaLogDeriv_zero (p : XiZeroCopy) :
    MeromorphicAt (logDeriv riemannZeta) (p.1 : ℂ) := by
  have hne : (p.1 : ℂ) ≠ 1 := by
    intro h
    have hlt := (xi_divisor_support_re_mem_open_unit p.1).2
    rw [h] at hlt
    norm_num at hlt
  have hζ := analyticOn_riemannZeta (p.1 : ℂ) (by simpa using hne)
  change MeromorphicAt (fun s => deriv riemannZeta s / riemannZeta s) (p.1 : ℂ)
  exact hζ.deriv.meromorphicAt.div hζ.meromorphicAt

private theorem laurentCoeff_inv_sq_mul_analytic_leading {A : ℂ → ℂ} {ρ : ℂ}
    (hA : AnalyticAt ℂ A ρ) :
    laurentCoeff (fun s => ((s - ρ) ^ 2)⁻¹ * A s) ρ (-2) = A ρ := by
  -- Cubic clearing also vanishes at the pole, respecting totalized inversion.
  have hshift : laurentShift (fun s => ((s - ρ) ^ 2)⁻¹ * A s) ρ 3 =
      fun t : ℂ => t * A (ρ + t) := by
    funext t
    simp only [laurentShift, add_sub_cancel_left]
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    · field_simp
  have hcomp : AnalyticAt ℂ (fun t : ℂ => A (ρ + t)) 0 :=
    analyticAt_comp_const_add hA
  have hcleared : AnalyticAt ℂ
      (laurentShift (fun s => ((s - ρ) ^ 2)⁻¹ * A s) ρ 3) 0 := by
    rw [hshift]
    exact analyticAt_id.mul hcomp
  have hd : HasDerivAt (fun t : ℂ => t * A (ρ + t)) (A ρ) 0 := by
    simpa only [Pi.mul_def, id_eq, add_zero, one_mul, zero_mul] using
      (hasDerivAt_id (0 : ℂ)).mul hcomp.differentiableAt.hasDerivAt
  rw [laurentCoeff_eq_taylorCoeffZero hcleared (by norm_num), hshift]
  change taylorCoeffZero (fun t : ℂ => t * A (ρ + t)) 1 = A ρ
  simpa only [taylorCoeffZero, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one,
    div_one] using hd.deriv

private theorem laurentCoeff_square_leading {F R : ℂ → ℂ} {ρ m : ℂ}
    (hF : MeromorphicAt F ρ) (hR : AnalyticAt ℂ R ρ)
    (hEq : F =ᶠ[𝓝[≠] ρ] fun s => m / (s - ρ) + R s) :
    laurentCoeff (fun s => F s ^ 2) ρ (-2) = m ^ 2 := by
  have hA : AnalyticAt ℂ (fun s => (m + (s - ρ) * R s) ^ 2) ρ :=
    (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hR)).pow 2
  have hF2 : MeromorphicAt (fun s => F s ^ 2) ρ := hF.pow 2
  have hmodel : (fun s => F s ^ 2) =ᶠ[𝓝[≠] ρ]
      (fun s => ((s - ρ) ^ 2)⁻¹ * (m + (s - ρ) * R s) ^ 2) := by
    filter_upwards [hEq, self_mem_nhdsWithin] with s hs hne
    change s ≠ ρ at hne
    rw [hs]
    field_simp [sub_ne_zero.mpr hne]
  rw [laurentCoeff_congr hF2 hmodel (-2), laurentCoeff_inv_sq_mul_analytic_leading hA,
    sub_self, zero_mul, add_zero]

/-- Squaring the prime-only current retains the mixed term with the analytic
proper-prime-power tail. All multiplicity copies are included. -/
theorem laurentCoeff_primeLogContinuation_sq (p : XiZeroCopy)
    (hp : 1 / 2 < (p.1 : ℂ).re) :
    laurentCoeff (fun s => xiPrimeLogDirichletContinuation s ^ 2) (p.1 : ℂ) (-1) =
      laurentCoeff (fun s => logDeriv riemannZeta s ^ 2) (p.1 : ℂ) (-1) +
        2 * ((xiZeroCopyFiber p.1).card : ℂ) * xiPrimeLogHigherValuation (p.1 : ℂ) := by
  obtain ⟨B, hB, hprincipal, hres⟩ := xiZero_exists_zeta_regular_part p
  have hH := analyticAt_primePowerTail hp
  have hmer : MeromorphicAt xiPrimeLogDirichletContinuation (p.1 : ℂ) :=
    (meromorphicAt_zetaLogDeriv_zero p).neg.sub hH.meromorphicAt
  have hprime : xiPrimeLogDirichletContinuation =ᶠ[𝓝[≠] (p.1 : ℂ)]
      (fun s => -((xiZeroCopyFiber p.1).card : ℂ) / (s - (p.1 : ℂ)) +
        (-B s - xiPrimeLogHigherValuation s)) := by
    filter_upwards [hprincipal] with s hs
    change -logDeriv riemannZeta s - xiPrimeLogHigherValuation s = _
    rw [hs]
    ring
  rw [laurentCoeff_square_of_pole_and_regular hmer (hB.neg.sub hH) hprime, hres]
  dsimp only [Pi.sub_apply, Pi.neg_apply]
  ring

/-- Removing the same-prime diagonal preserves the exact simple coefficient. -/
theorem laurentCoeff_primePairSource (p : XiZeroCopy)
    (hp : 1 / 2 < (p.1 : ℂ).re) :
    laurentCoeff primePairSource (p.1 : ℂ) (-1) =
      laurentCoeff (fun s => logDeriv riemannZeta s ^ 2) (p.1 : ℂ) (-1) +
        2 * ((xiZeroCopyFiber p.1).card : ℂ) * xiPrimeLogHigherValuation (p.1 : ℂ) := by
  have hmer : MeromorphicAt xiPrimeLogDirichletContinuation (p.1 : ℂ) :=
    (meromorphicAt_zetaLogDeriv_zero p).neg.sub (analyticAt_primePowerTail hp).meromorphicAt
  change laurentCoeff (fun s => xiPrimeLogDirichletContinuation s ^ 2 - primePairDiagonal s)
    (p.1 : ℂ) (-1) = _
  rw [laurentCoeff_sub (f := fun s => xiPrimeLogDirichletContinuation s ^ 2) (hmer.pow 2)
    (analyticAt_primePairDiagonal hp).meromorphicAt (-1),
    laurentCoeff_eq_zero_of_analyticAt (analyticAt_primePairDiagonal hp) (by norm_num),
    sub_zero, laurentCoeff_primeLogContinuation_sq p hp]

/-- Every actual right-hand zero contributes its squared multiplicity to the
double pole of the distinct-prime pair source. -/
theorem laurentCoeff_primePairSource_leading (p : XiZeroCopy)
    (hp : 1 / 2 < (p.1 : ℂ).re) :
    laurentCoeff primePairSource (p.1 : ℂ) (-2) =
      ((xiZeroCopyFiber p.1).card : ℂ) ^ 2 := by
  obtain ⟨B, hB, hprincipal, -⟩ := xiZero_exists_zeta_regular_part p
  have hH := analyticAt_primePowerTail hp
  have hmer : MeromorphicAt xiPrimeLogDirichletContinuation (p.1 : ℂ) :=
    (meromorphicAt_zetaLogDeriv_zero p).neg.sub hH.meromorphicAt
  have hprime : xiPrimeLogDirichletContinuation =ᶠ[𝓝[≠] (p.1 : ℂ)]
      (fun s => -((xiZeroCopyFiber p.1).card : ℂ) / (s - (p.1 : ℂ)) +
        (-B s - xiPrimeLogHigherValuation s)) := by
    filter_upwards [hprincipal] with s hs
    change -logDeriv riemannZeta s - xiPrimeLogHigherValuation s = _
    rw [hs]
    ring
  change laurentCoeff (fun s => xiPrimeLogDirichletContinuation s ^ 2 - primePairDiagonal s)
    (p.1 : ℂ) (-2) = _
  rw [laurentCoeff_sub (f := fun s => xiPrimeLogDirichletContinuation s ^ 2) (hmer.pow 2)
    (analyticAt_primePairDiagonal hp).meromorphicAt (-2),
    laurentCoeff_eq_zero_of_analyticAt (analyticAt_primePairDiagonal hp) (by norm_num),
    sub_zero, laurentCoeff_square_leading hmer (hB.neg.sub hH) hprime, neg_sq]

/-- The distinct-prime pair residue determines the actual transverse zero field,
with the proper-prime-power and archimedean corrections retained. -/
theorem xiTransverseField_eq_primePairSource (p : XiZeroCopy)
    (hp : 1 / 2 < (p.1 : ℂ).re) :
    xiTransverseField p =
      (laurentCoeff primePairSource (p.1 : ℂ) (-1) /
        (2 * ((xiZeroCopyFiber p.1).card : ℂ))).re -
          (xiPrimeLogHigherValuation (p.1 : ℂ)).re +
            (logDeriv archFactor (p.1 : ℂ)).re := by
  have hm : ((xiZeroCopyFiber p.1).card : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Finset.card_pos.mpr ⟨p, mem_xiZeroCopyFiber.mpr rfl⟩)
  have htwo : 2 * ((xiZeroCopyFiber p.1).card : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hm
  rw [← xiSourceField_eq_transverseField, xiSourceField, laurentCoeff_primePairSource p hp,
    add_div, mul_div_cancel_left₀ _ htwo, Complex.add_re]
  ring

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.analyticAt_primePowerTail
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.primePairDiagonal_eq
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.analyticAt_primePairDiagonal
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.primePairSource_eq_tsum
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.laurentCoeff_primeLogContinuation_sq
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.laurentCoeff_primePairSource
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.laurentCoeff_primePairSource_leading
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.xiTransverseField_eq_primePairSource
