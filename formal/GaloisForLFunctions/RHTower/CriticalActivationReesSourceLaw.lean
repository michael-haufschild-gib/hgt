import GaloisForLFunctions.RHTower.EulerActivationSquarefreeDisintegration
import GaloisForLFunctions.RHTower.PrimeValuationNormalCornerDuality
import GaloisForLFunctions.RHTower.ArithmeticSchurRenormalizationLaw
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesJetStability
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Matrix.PosDef

/-!
# Critical activation--Rees source law

The diagonal Euler activation has two independent prime coordinates: radical occupancy and
conditional valuation depth.  At the critical reciprocal-prime nodes, occupancy has divergent
total mass, every fixed depth at least two has summable mass, and the Fisher-whitened Gamma fibre
again has divergent total mass.  No finite recurrence can compress the reciprocal-prime source.

At a divisor of order `d`, the overlap has order `d` while its first Fisher numerator has order
`d - 1`; positivity of a bounded two-by-two Gram completion is therefore impossible.  The correct
boundary algebra is Rees graded.

Finally, every finite-Rees operator preserves the all-orders-flat radical, independent of
dimension.  On the actual prime Wold boundary, the reflected irregular Gamma gauge is flat beyond
every Rees order, whereas the canonical vacuum half-density is not.  Thus a finite-order operator
cannot sew these sectors; only an essentially singular or non-operator correspondence can do so.
-/

open Complex
open Filter Asymptotics
open GaloisForLFunctions
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Critical radical-occupancy mass at one reciprocal-prime node. -/
def criticalActivationOccupancyMass (p : Nat.Primes) : ℝ :=
  diagonalActivationOccupancyProbability
    (xiTransversePrimeApertureDiskNode 1 p)

theorem criticalActivationOccupancyMass_eq (p : Nat.Primes) :
    criticalActivationOccupancyMass p = 1 / ((p : ℝ) + 1) := by
  rw [criticalActivationOccupancyMass,
    diagonalActivationOccupancyProbability,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp

/-- Critical occupancy remains prime-harmonic and is not summable. -/
theorem not_summable_criticalActivationOccupancyMass :
    ¬ Summable criticalActivationOccupancyMass := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes => (1 / 2 : ℝ) * (1 / (p : ℝ))) := by
    refine Summable.of_nonneg_of_le
      (f := fun p : Nat.Primes => criticalActivationOccupancyMass p)
      (fun p => by positivity) (fun p => ?_) hsum
    rw [criticalActivationOccupancyMass_eq]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
    calc
      (1 / 2 : ℝ) * (1 / (p : ℝ)) = 1 / (2 * (p : ℝ)) := by ring
      _ ≤ 1 / ((p : ℝ) + 1) := by
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hinv : Summable (fun p : Nat.Primes => (1 / (p : ℝ) : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)).mp hscaled
  exact Nat.Primes.not_summable_one_div hinv

/-- Mass of valuation depth at least `m` in the critical activation law. -/
def criticalActivationValuationTailMass (m : ℕ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  q ^ m / (1 + q)

theorem criticalActivationValuationTailMass_eq
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    criticalActivationValuationTailMass m p =
      1 / ((p : ℝ) ^ (m - 1) * ((p : ℝ) + 1)) := by
  rw [criticalActivationValuationTailMass,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [inv_pow]
  have hm' : m = (m - 1) + 1 := by omega
  rw [hm', pow_succ]
  field_simp
  congr 1

/-- Every fixed valuation tail of depth at least two is summable over primes. -/
theorem summable_criticalActivationValuationTailMass
    {m : ℕ} (hm : 2 ≤ m) :
    Summable (criticalActivationValuationTailMass m) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ m)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by exact_mod_cast hm)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ m)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le
    (f := fun p : Nat.Primes => ((p : ℝ) ^ m)⁻¹)
    (fun p : Nat.Primes => by
      change 0 ≤
        xiTransversePrimeApertureDiskNode 1 p ^ m /
          (1 + xiTransversePrimeApertureDiskNode 1 p)
      have hq : 0 < xiTransversePrimeApertureDiskNode 1 p :=
        xiTransversePrimeApertureDiskNode_pos 1 p
      exact div_nonneg (pow_nonneg hq.le m) (by linarith))
    (fun p => ?_) hprime
  change xiTransversePrimeApertureDiskNode 1 p ^ m /
      (1 + xiTransversePrimeApertureDiskNode 1 p) ≤
    ((p : ℝ) ^ m)⁻¹
  have hq0 : 0 ≤ xiTransversePrimeApertureDiskNode 1 p :=
    (xiTransversePrimeApertureDiskNode_pos 1 p).le
  calc
    xiTransversePrimeApertureDiskNode 1 p ^ m /
        (1 + xiTransversePrimeApertureDiskNode 1 p) ≤
      xiTransversePrimeApertureDiskNode 1 p ^ m := by
        exact div_le_self (pow_nonneg hq0 m) (by linarith)
    _ = ((p : ℝ) ^ m)⁻¹ := by
      rw [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow]

/-- Fisher-whitened Gamma-fibre mass at one reciprocal-prime node. -/
def criticalActivationGammaFibreMass (p : Nat.Primes) : ℝ :=
  xiTransverseGammaValuationSzegoKernel p p

theorem criticalActivationGammaFibreMass_eq (p : Nat.Primes) :
    criticalActivationGammaFibreMass p =
      ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) + 1)) := by
  change xiTransverseGammaValuationSzegoKernel p p = _
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hq1 : q < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hkernel :
      xiTransverseGammaValuationSzegoKernel p p =
        q * (1 - q) / (1 + q) := by
    simp only [xiTransverseGammaValuationSzegoKernel]
    rw [show xiTransversePrimeApertureDiskNode 1 p = q by rfl]
    rw [show Real.sqrt q * Real.sqrt q = q by
      rw [← pow_two, Real.sq_sqrt hq0]]
    rw [show 1 - q * q = (1 - q) * (1 + q) by ring]
    have hminus : 1 - q ≠ 0 := by linarith
    have hplus : 1 + q ≠ 0 := by linarith
    field_simp [hminus, hplus]
  rw [hkernel]
  rw [show q = (p : ℝ)⁻¹ by
    exact xiTransversePrimeApertureDiskNode_one_eq_inv p]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpone : (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Fisher whitening restores a prime-harmonic, nonsummable Gamma fibre. -/
theorem not_summable_criticalActivationGammaFibreMass :
    ¬ Summable criticalActivationGammaFibreMass := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes => (1 / 3 : ℝ) * (1 / (p : ℝ))) := by
    refine Summable.of_nonneg_of_le
      (f := fun p : Nat.Primes => criticalActivationGammaFibreMass p)
      (fun p => by positivity) (fun p => ?_) hsum
    rw [criticalActivationGammaFibreMass_eq]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    calc
      (1 / 3 : ℝ) * (1 / (p : ℝ)) =
          1 / (3 * (p : ℝ)) := by ring
      _ ≤ ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) + 1)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  have hinv : Summable (fun p : Nat.Primes => (1 / (p : ℝ) : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (1 / 3 : ℝ) ≠ 0)).mp hscaled
  exact Nat.Primes.not_summable_one_div hinv

/-- No nonzero polynomial recurrence vanishes on infinitely many reciprocal-prime nodes. -/
theorem polynomial_eq_zero_of_vanishes_on_infinite_prime_nodes
    (S : Set Nat.Primes) (hS : S.Infinite) (Q : Polynomial ℝ)
    (hQ : ∀ p ∈ S,
      Polynomial.eval (xiTransversePrimeApertureDiskNode 1 p) Q = 0) :
    Q = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot Q
  have himage :
      (fun p : Nat.Primes => xiTransversePrimeApertureDiskNode 1 p) '' S ⊆
        {x | Q.IsRoot x} := by
    intro x hx
    rcases hx with ⟨p, hpS, rfl⟩
    exact Polynomial.IsRoot.def.2 (hQ p hpS)
  exact (hS.image
    xiTransversePrimeApertureDiskNode_one_injective.injOn).mono himage

/-- Two-by-two Gram model for overlap, first numerator, and completion diagonal. -/
def divisorReesGram (B S C : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![B ^ 2, S; S, C]

theorem divisorReesGram_posSemidef_crossBound
    {B S C : ℝ} (h : (divisorReesGram B S C).PosSemidef) :
    S ^ 2 ≤ B ^ 2 * C := by
  have hdet := h.det_nonneg
  simpa [divisorReesGram, Matrix.det_fin_two, pow_two] using hdet

def monomialDivisorOverlap (d : ℕ) (t : ℝ) : ℝ := t ^ d

def monomialDivisorFisherNumerator (d : ℕ) (t : ℝ) : ℝ :=
  (d : ℝ) * t ^ (d - 1)

/-- Divisor differentiation drops exactly one grade, forcing an inverse-square Gram ratio. -/
theorem monomialDivisorFisher_ratio
    {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : t ≠ 0) :
    monomialDivisorFisherNumerator d t ^ 2 /
        monomialDivisorOverlap d t ^ 2 =
      (d : ℝ) ^ 2 / t ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  simp only [monomialDivisorFisherNumerator, monomialDivisorOverlap,
    Nat.succ_sub_one, pow_succ]
  field_simp [ht, pow_ne_zero]

theorem monomialDivisorFisher_ratio_unbounded
    {d : ℕ} (hd : 0 < d) (M : ℝ) :
    ∃ t : ℝ, 0 < t ∧
      M < monomialDivisorFisherNumerator d t ^ 2 /
        monomialDivisorOverlap d t ^ 2 := by
  let t : ℝ := (d : ℝ) / (|M| + 1)
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < |M| + 1 := by positivity
  have ht : 0 < t := div_pos hdR hden
  refine ⟨t, ht, ?_⟩
  rw [monomialDivisorFisher_ratio hd ht.ne']
  have hratio : (d : ℝ) ^ 2 / t ^ 2 = (|M| + 1) ^ 2 := by
    dsimp only [t]
    field_simp [hdR.ne', hden.ne']
  rw [hratio]
  nlinarith [le_abs_self M]

/-- No uniformly bounded positive Gram completion survives a nonzero divisor. -/
theorem no_bounded_positive_divisorReesGram
    {d : ℕ} (hd : 0 < d) (M : ℝ) :
    ∃ t : ℝ, 0 < t ∧ ∀ C : ℝ, C ≤ M →
      ¬ (divisorReesGram
          (monomialDivisorOverlap d t)
          (monomialDivisorFisherNumerator d t) C).PosSemidef := by
  obtain ⟨t, ht, hratio⟩ :=
    monomialDivisorFisher_ratio_unbounded hd M
  refine ⟨t, ht, ?_⟩
  intro C hC hpos
  have hcross := divisorReesGram_posSemidef_crossBound hpos
  have hBsq : 0 < monomialDivisorOverlap d t ^ 2 := by
    exact sq_pos_of_pos (pow_pos ht d)
  have hquot :
      monomialDivisorFisherNumerator d t ^ 2 /
          monomialDivisorOverlap d t ^ 2 ≤ C := by
    apply (div_le_iff₀ hBsq).2
    simpa [mul_comm] using hcross
  linarith

/-- Exponential decay is flat beyond every order of the reciprocal scale. -/
theorem expDecay_reesAllOrdersFlat_atTop
    {c : ℝ} (hc : 0 < c) :
    ReesAllOrdersFlat Filter.atTop (fun x : ℝ => x⁻¹)
      (fun x : ℝ => Real.exp (-c * x)) := by
  intro N
  have h :=
    isLittleO_exp_neg_mul_rpow_atTop hc (-(N : ℝ))
  apply h.congr' EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]
  rw [inv_pow]

/-- Positive exponential growth is not all-orders flat. -/
theorem expGrowth_not_reesAllOrdersFlat_atTop
    {c : ℝ} (hc : 0 < c) :
    ¬ ReesAllOrdersFlat Filter.atTop (fun x : ℝ => x⁻¹)
      (fun x : ℝ => Real.exp (c * x)) := by
  intro hflat
  have hsmall := (hflat 0).bound one_half_pos
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop,
      1 ≤ Real.exp (c * x) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.one_le_exp (mul_nonneg hc.le hx)
  obtain ⟨x, hxsmall, hxlarge⟩ := (hsmall.and hlarge).exists
  norm_num at hxsmall
  linarith

/-- The actual reflected irregular Gamma gauge is all-orders flat along the prime Wold boundary. -/
theorem norm_primeWoldReflectedIrregularGauge_reesAllOrdersFlat
    {t : ℂ} (ht : 0 < t.re) :
    ReesAllOrdersFlat Filter.atTop primeWoldBoundaryVolumeBelow
      (fun N => ‖primeWoldReflectedIrregularGauge t N‖) := by
  intro k
  have hflat :=
    (expDecay_reesAllOrdersFlat_atTop (c := 2 * t.re) (by positivity)) k
  have hcomp := hflat.comp_tendsto tendsto_primeWoldBoundaryScale_atTop
  apply hcomp.congr'
  · filter_upwards [] with N
    rw [norm_primeWoldReflectedIrregularGauge]
    dsimp only [Function.comp_apply]
    congr 1
    ring
  · filter_upwards [] with N
    simp only [Function.comp_apply, primeWoldBoundaryScale, inv_inv]

/-- Canonical half-density of the finite-prime vacuum event. -/
def primeWoldHalfNormalSector (N : ℕ) : ℝ :=
  Real.sqrt (primeWoldBoundaryVolumeBelow N)

theorem primeWoldHalfNormalSector_sq (N : ℕ) :
    primeWoldHalfNormalSector N ^ 2 =
      primeWoldBoundaryVolumeBelow N := by
  rw [primeWoldHalfNormalSector, Real.sq_sqrt
    (primeWoldBoundaryVolumeBelow_nonneg N)]

/-- The vacuum half-density has finite half-normal order and is not in the flat radical. -/
theorem primeWoldHalfNormalSector_not_reesAllOrdersFlat :
    ¬ ReesAllOrdersFlat Filter.atTop primeWoldBoundaryVolumeBelow
      primeWoldHalfNormalSector := by
  intro hflat
  have hbound := (hflat 1).bound one_pos
  have hsmall :
      ∀ᶠ N : ℕ in Filter.atTop, primeWoldBoundaryVolumeBelow N < 1 :=
    tendsto_primeWoldBoundaryVolumeBelow_zero.eventually
      (eventually_lt_nhds zero_lt_one)
  obtain ⟨N, hNbound, hNsmall⟩ := (hbound.and hsmall).exists
  have hvolPos := primeWoldBoundaryVolumeBelow_pos N
  have hsqrtPos : 0 < primeWoldHalfNormalSector N := by
    exact Real.sqrt_pos.2 hvolPos
  have hsqrtLtOne : primeWoldHalfNormalSector N < 1 := by
    change Real.sqrt (primeWoldBoundaryVolumeBelow N) < 1
    rw [← Real.sqrt_one]
    exact (Real.sqrt_lt_sqrt_iff hvolPos.le).2 hNsmall
  have hsquareLt :
      primeWoldHalfNormalSector N ^ 2 <
        primeWoldHalfNormalSector N := by
    nlinarith
  simp only [Real.norm_eq_abs, one_mul, pow_one,
    abs_of_pos hsqrtPos, abs_of_pos hvolPos] at hNbound
  rw [← primeWoldHalfNormalSector_sq] at hNbound
  exact (not_lt_of_ge hNbound) hsquareLt

/-- No multiplier of any fixed Rees order sews the actual flat irregular gauge to the Wold
half-density sector. -/
theorem no_finiteReesMultiplier_sews_flat_to_halfNormal
    (K : ℕ) (r : ℕ → ℝ)
    (hr : ReesGradeAtMost Filter.atTop
      primeWoldBoundaryVolumeBelow K r) :
    (fun N => r N *
      ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) ≠
        primeWoldHalfNormalSector := by
  intro hsew
  have hscale :
      ∀ᶠ N : ℕ in Filter.atTop,
        primeWoldBoundaryVolumeBelow N ≠ 0 :=
    Filter.Eventually.of_forall fun N =>
      (primeWoldBoundaryVolumeBelow_pos N).ne'
  have hflat :
      ReesAllOrdersFlat Filter.atTop primeWoldBoundaryVolumeBelow
        (fun N => r N *
          ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖) :=
    reesAllOrdersFlat_mul_reesGradeAtMost Filter.atTop
      primeWoldBoundaryVolumeBelow r
      (fun N => ‖primeWoldReflectedIrregularGauge (1 : ℂ) N‖)
      K hscale hr
      (norm_primeWoldReflectedIrregularGauge_reesAllOrdersFlat
        (t := 1) (by norm_num))
  apply primeWoldHalfNormalSector_not_reesAllOrdersFlat
  simpa only [hsew] using hflat

/-- Universal no-sewing law: finite operator-norm Rees order preserves the flat radical in
arbitrary dimension, so it cannot map a flat germ to a nonflat germ. -/
theorem no_finiteReesOperator_sews_flat_to_nonflat
    {α E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (l : Filter α) (a : α → ℝ) (K : ℕ)
    (R : α → (E →L[ℝ] F)) (f : α → E) (g : α → F)
    (ha : ∀ᶠ x in l, a x ≠ 0)
    (hR : ReesOperatorGradeAtMost l a K R)
    (hf : ReesAllOrdersFlat l a f)
    (hg : ¬ ReesAllOrdersFlat l a g) :
    (fun x => R x (f x)) ≠ g := by
  intro hsew
  apply hg
  have hflat :=
    reesAllOrdersFlat_apply_reesOperatorGradeAtMost
      l a K R f ha hR hf
  simpa only [hsew] using hflat

end

end RHTower
