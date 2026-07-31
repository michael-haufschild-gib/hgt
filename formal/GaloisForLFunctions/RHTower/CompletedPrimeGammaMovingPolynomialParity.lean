import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingComplexHankel
import GaloisForLFunctions.HTGeometry.RealEvenFactorizationSignTransfer

open Complex Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The moving completed-source quadratic Hankel test attached to one real polynomial. -/
def completedOddLogDerivPolynomialHankel (p : Polynomial ℝ) (sigma : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (((p.map (algebraMap ℝ ℂ)) ^ 2).natDegree + 1),
    ((p.map (algebraMap ℝ ℂ)) ^ 2).coeff k *
      completedOddLogDerivMoment sigma k

/-- The real-axis restriction of one moving polynomial Hankel test. -/
def completedOddLogDerivPolynomialHankelReal (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  (completedOddLogDerivPolynomialHankel p (x : ℂ)).re

/-- At the center, the moving polynomial test is exactly the established prime--Gamma source
quadratic test consumed by the countable RH criterion. -/
@[simp] theorem completedOddLogDerivPolynomialHankel_one_half (p : Polynomial ℝ) :
    completedOddLogDerivPolynomialHankel p (1 / 2) =
      primeArchSourceTraceHankel p := by
  rw [completedOddLogDerivPolynomialHankel, primeArchSourceTraceHankel]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← completedMovingComplexMoment_eq_completedOddLogDerivMoment_one_half,
    completedMovingComplexMoment_one_half]
  rfl

/-- Real center form of the polynomial bridge. -/
@[simp] theorem completedOddLogDerivPolynomialHankelReal_one_half (p : Polynomial ℝ) :
    completedOddLogDerivPolynomialHankelReal p (1 / 2) =
      (primeArchSourceTraceHankel p).re := by
  rw [completedOddLogDerivPolynomialHankelReal]
  norm_num

/-- Every finite polynomial Hankel test inherits exact functional-equation reflection. -/
@[simp] theorem completedOddLogDerivPolynomialHankel_one_sub
    (p : Polynomial ℝ) (sigma : ℂ) :
    completedOddLogDerivPolynomialHankel p (1 - sigma) =
      completedOddLogDerivPolynomialHankel p sigma := by
  simp only [completedOddLogDerivPolynomialHankel,
    completedOddLogDerivMoment_one_sub]

/-- Every finite polynomial Hankel test is Schwarz-equivariant. -/
@[simp] theorem completedOddLogDerivPolynomialHankel_conj
    (p : Polynomial ℝ) (sigma : ℂ) :
    completedOddLogDerivPolynomialHankel p ((starRingEnd ℂ) sigma) =
      (starRingEnd ℂ) (completedOddLogDerivPolynomialHankel p sigma) := by
  simp only [completedOddLogDerivPolynomialHankel,
    completedOddLogDerivMoment_conj, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [← Polynomial.map_pow, Polynomial.coeff_map]
  simp

/-- The moving polynomial test is real on the real base axis. -/
@[simp] theorem completedOddLogDerivPolynomialHankel_ofReal_im
    (p : Polynomial ℝ) (x : ℝ) :
    (completedOddLogDerivPolynomialHankel p (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa using (completedOddLogDerivPolynomialHankel_conj p (x : ℂ)).symm

/-- Paper-facing far-right input: every nonzero integer-polynomial test has some positive real
anchor to the right of the functional-equation center. -/
def CompletedOddLogDerivPolynomialFarRightPositive : Prop :=
  ∀ p : Polynomial ℤ, p ≠ 0 →
    ∃ R : ℝ, 1 / 2 < R ∧
      0 < completedOddLogDerivPolynomialHankelReal
        (p.map (Int.castRingHom ℝ)) R

/-- Source parity input: on every compact right segment, each nonzero integer-polynomial test
factors through only even-multiplicity real roots and a continuous nowhere-zero real cofactor.
The center may itself be an even root. -/
def CompletedOddLogDerivPolynomialRightEvenFactorization : Prop :=
  ∀ p : Polynomial ℤ, p ≠ 0 → ∀ R : ℝ, 1 / 2 < R →
    HTGeometry.RealEvenFactorizationOn
      (completedOddLogDerivPolynomialHankelReal
        (p.map (Int.castRingHom ℝ))) (1 / 2) R

/-- Far-right positivity plus even real-root factorization discharges the complete countable
prime--Gamma source cone.  No central nonvanishing hypothesis is required. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_movingPolynomialFarRight_evenFactorization
    (hfar : CompletedOddLogDerivPolynomialFarRightPositive)
    (heven : CompletedOddLogDerivPolynomialRightEvenFactorization) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  by_cases hp : p = 0
  · subst p
    simp [primeArchSourceTraceHankel]
  · obtain ⟨R, hR, hpos⟩ := hfar p hp
    have hcenter := HTGeometry.nonneg_left_of_realEvenFactorizationOn_of_right_pos
      hR (heven p hp R hR) hpos
    rw [completedOddLogDerivPolynomialHankelReal_one_half] at hcenter
    exact hcenter

/-- **Polynomial parity chain to RH.**  Eventual source positivity is already a paper consequence
of the completed prime--Gamma asymptotics.  The sole structural input is even factorization of the
moving scalar polynomial tests; zeros at the center are harmless. -/
theorem riemannHypothesis_of_movingPolynomialFarRight_evenFactorization
    (hfar : CompletedOddLogDerivPolynomialFarRightPositive)
    (heven : CompletedOddLogDerivPolynomialRightEvenFactorization) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_movingPolynomialFarRight_evenFactorization
      hfar heven)

end

end RHTower

namespace RHTower

noncomputable section

/-! ## Discharging polynomial far-right positivity from scalar moment asymptotics -/

/-- The exact scalar source asymptotic needed for every polynomial far-right anchor.  The
finite-polynomial theorem below shows that no uniformity in `k` is required. -/
def CompletedOddLogDerivMomentFarRightAsymptotic : Prop :=
  ∀ k : ℕ,
    Tendsto
      (fun x : ℝ => x ^ (2 * k + 1) *
        (completedOddLogDerivMoment (x : ℂ) k).re)
      atTop (nhds ((-1 : ℝ) ^ k / (2 * (2 * k + 1))))

/-- Real polynomial tests are the finite real linear combinations of completed odd moments
whose coefficients are those of the polynomial square. -/
theorem completedOddLogDerivPolynomialHankelReal_eq_sum
    (p : Polynomial ℝ) (x : ℝ) :
    completedOddLogDerivPolynomialHankelReal p x =
      ∑ k ∈ Finset.range ((p ^ 2).natDegree + 1),
        (p ^ 2).coeff k * (completedOddLogDerivMoment (x : ℂ) k).re := by
  simp [completedOddLogDerivPolynomialHankelReal,
    completedOddLogDerivPolynomialHankel, ← Polynomial.map_pow,
    Polynomial.natDegree_map]

/-- For an arbitrary real coefficient polynomial `q`, scaling by the order of its
lowest nonzero coefficient isolates exactly that coefficient.  Every higher completed moment
has an additional inverse even power and therefore vanishes in the limit. -/
theorem tendsto_scaled_completedOddLogDerivPolynomial_sum
    (hmom : CompletedOddLogDerivMomentFarRightAsymptotic)
    (q : Polynomial ℝ) :
    Tendsto
      (fun x : ℝ => x ^ (2 * q.natTrailingDegree + 1) *
        (∑ k ∈ Finset.range (q.natDegree + 1),
          q.coeff k * (completedOddLogDerivMoment (x : ℂ) k).re))
      atTop
      (nhds (q.trailingCoeff *
        ((-1 : ℝ) ^ q.natTrailingDegree /
          (2 * (2 * q.natTrailingDegree + 1))))) := by
  let d := q.natTrailingDegree
  let A : ℕ → ℝ := fun k =>
    if k = d then q.coeff k * ((-1 : ℝ) ^ k / (2 * (2 * k + 1))) else 0
  have hterms : ∀ k ∈ Finset.range (q.natDegree + 1),
      Tendsto
        (fun x : ℝ => x ^ (2 * d + 1) *
          (q.coeff k * (completedOddLogDerivMoment (x : ℂ) k).re))
        atTop (nhds (A k)) := by
    intro k hk
    by_cases hlt : k < d
    · have hcoeff : q.coeff k = 0 :=
        Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt
      simp [A, hcoeff, ne_of_lt hlt]
    · by_cases heq : k = d
      · subst k
        have h := (hmom d).const_mul (q.coeff d)
        simpa [A, mul_assoc, mul_left_comm, mul_comm] using h
      · have hdk : d < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
        have hinv := (tendsto_inv_atTop_zero :
          Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0)).pow (2 * (k - d))
        have hprod := hinv.mul (hmom k)
        have hscaled := hprod.const_mul (q.coeff k)
        have hexp : 2 * (k - d) ≠ 0 := by omega
        have hlim : q.coeff k *
            (0 ^ (2 * (k - d)) *
              ((-1 : ℝ) ^ k / (2 * (2 * k + 1)))) = 0 := by
          simp [hexp]
        rw [hlim] at hscaled
        have hevent :
            (fun x : ℝ => q.coeff k * ((x⁻¹) ^ (2 * (k - d)) *
                (x ^ (2 * k + 1) *
                  (completedOddLogDerivMoment (x : ℂ) k).re))) =ᶠ[atTop]
              (fun x : ℝ => x ^ (2 * d + 1) *
                (q.coeff k * (completedOddLogDerivMoment (x : ℂ) k).re)) := by
          filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
          symm
          rw [show 2 * k + 1 = (2 * d + 1) + 2 * (k - d) by omega, pow_add]
          rw [inv_pow]
          field_simp ; ring
        have ht := hscaled.congr' hevent
        simpa [A, heq] using ht
  have hsum := tendsto_finsetSum (Finset.range (q.natDegree + 1)) hterms
  have hdmem : d ∈ Finset.range (q.natDegree + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Polynomial.natTrailingDegree_le_natDegree q)
  have hAsum : (∑ k ∈ Finset.range (q.natDegree + 1), A k) =
      q.trailingCoeff * ((-1 : ℝ) ^ d / (2 * (2 * d + 1))) := by
    rw [Finset.sum_eq_single d]
    · simp [A, d, Polynomial.trailingCoeff]
    · intro b hb hbd
      simp [A, hbd]
    · exact fun h => (h hdmem).elim
  rw [hAsum] at hsum
  simpa [d, Finset.mul_sum] using hsum

/-- The scalar completed-moment asymptotics discharge the aggregate far-right hypothesis used by
the polynomial parity chain.  The lowest coefficient of a square is a positive square, while its
index is even, so the surviving asymptotic constant is strictly positive. -/
theorem completedOddLogDerivPolynomialFarRightPositive_of_momentAsymptotic
    (hmom : CompletedOddLogDerivMomentFarRightAsymptotic) :
    CompletedOddLogDerivPolynomialFarRightPositive := by
  intro p hp
  let pR : Polynomial ℝ := p.map (Int.castRingHom ℝ)
  let q : Polynomial ℝ := pR ^ 2
  have hpR : pR ≠ 0 := by
    dsimp [pR]
    exact (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hlim := tendsto_scaled_completedOddLogDerivPolynomial_sum hmom q
  have htrail : q.natTrailingDegree = pR.natTrailingDegree + pR.natTrailingDegree := by
    dsimp [q]
    rw [pow_two, Polynomial.natTrailingDegree_mul hpR hpR]
  have htc : q.trailingCoeff = pR.trailingCoeff * pR.trailingCoeff := by
    rw [Polynomial.trailingCoeff, htrail]
    dsimp [q]
    rw [pow_two, Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]
  have htcpos : 0 < q.trailingCoeff := by
    rw [htc]
    exact mul_self_pos.mpr ((Polynomial.trailingCoeff_eq_zero.not).mpr hpR)
  have heven : (-1 : ℝ) ^ q.natTrailingDegree = 1 := by
    rw [htrail,
      show pR.natTrailingDegree + pR.natTrailingDegree =
        2 * pR.natTrailingDegree by omega,
      pow_mul]
    norm_num
  have htarget : 0 < q.trailingCoeff *
      ((-1 : ℝ) ^ q.natTrailingDegree /
        (2 * (2 * q.natTrailingDegree + 1))) := by
    rw [heven]
    positivity
  have hscaledPos := hlim.eventually (Ioi_mem_nhds htarget)
  have hlarge : ∀ᶠ x : ℝ in atTop, 1 / 2 < x := eventually_gt_atTop (1 / 2)
  obtain ⟨R, hRlarge, hRscaled⟩ := (hlarge.and hscaledPos).exists
  refine ⟨R, hRlarge, ?_⟩
  rw [completedOddLogDerivPolynomialHankelReal_eq_sum]
  change 0 < ∑ k ∈ Finset.range ((pR ^ 2).natDegree + 1),
    (pR ^ 2).coeff k * (completedOddLogDerivMoment (R : ℂ) k).re
  have hRpos : 0 < R := lt_trans (by norm_num) hRlarge
  have hscale : 0 < R ^ (2 * q.natTrailingDegree + 1) := pow_pos hRpos _
  change 0 < R ^ (2 * q.natTrailingDegree + 1) *
    (∑ k ∈ Finset.range (q.natDegree + 1),
      q.coeff k * (completedOddLogDerivMoment (R : ℂ) k).re) at hRscaled
  exact (mul_pos_iff.mp hRscaled).resolve_right
    (not_and_of_not_left _ (not_lt_of_ge hscale.le)) |>.2

/-- **Moment-asymptotic polynomial parity chain to RH.**  After the scalar completed-source
asymptotics are supplied, even real factorization is the sole remaining source-side input. -/
theorem riemannHypothesis_of_momentAsymptotic_movingPolynomial_evenFactorization
    (hmom : CompletedOddLogDerivMomentFarRightAsymptotic)
    (heven : CompletedOddLogDerivPolynomialRightEvenFactorization) :
    RiemannHypothesis :=
  riemannHypothesis_of_movingPolynomialFarRight_evenFactorization
    (completedOddLogDerivPolynomialFarRightPositive_of_momentAsymptotic hmom) heven

end

end RHTower
