import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction

/-!
# Gamma-sewn synchronized-lcm contraction

The pairwise Gamma-sewn valuation kernel is the arity-two member of a canonical
all-squarefree family.  For a finite nonempty prime support `P`, multiply the existing source
rays at a *common valuation depth* and then sum over that depth.  The resulting Hadamard-depth
coefficient is

`prod_{p in P} [C(x,p) a(p) (1-r(x,p))] / (1-prod_{p in P} r(x,p))`,

where `a(p)=p⁻¹/(1+p⁻¹)` and `r(x,p)=p⁻ˣ`.  Singleton support completes one source ray, pair
support is exactly the existing Gram kernel, and higher support supplies the missing lcm grades.

The insertion law below is state-dependent: adjoining a prime depends on the complete current
support through its synchronized aperture node.  Its cocycle identity proves that all orders of
future-prime insertion agree, including the first genuinely new three-prime test.  This is a
source-derived contraction coordinate, not an RH theorem: its inverse is not asserted bounded,
and target recovery must occur only after the physical signed response has joined.
-/

namespace RHTower

noncomputable section

open scoped BigOperators
open Filter Set

/-- The product of the true aperture nodes on a finite prime support. -/
def gammaSewnSynchronizedLcmNode
    (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P, xiMobiusContinuousApertureDiskNode x p

/-- The numerator left after synchronizing all prime rays at one valuation depth. -/
def gammaSewnSynchronizedLcmNumerator
    (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P,
    gammaSewnMobiusValuationContractionMultiplier x p *
      (xiTransversePrimeApertureDiskNode 1 p /
        (1 + xiTransversePrimeApertureDiskNode 1 p)) *
      (1 - xiMobiusContinuousApertureDiskNode x p)

/-- The common-depth Hadamard product of the Gamma-sewn source rays. -/
def gammaSewnSynchronizedLcmRay
    (x : ℝ) (P : Finset Nat.Primes) (e : ℕ) : ℝ :=
  ∏ p ∈ P, gammaSewnMobiusContinuousApertureFeature x p e

/-- Closed synchronized-lcm coefficient.  The empty support is the Boolean vacuum. -/
def gammaSewnSynchronizedLcmWeight
    (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  if P = ∅ then 1 else
    gammaSewnSynchronizedLcmNumerator x P /
      (1 - gammaSewnSynchronizedLcmNode x P)

/-- Each synchronized depth is one geometric ray whose ratio is the product aperture node. -/
theorem gammaSewnSynchronizedLcmRay_eq_geometric
    (x : ℝ) (P : Finset Nat.Primes) (e : ℕ) :
    gammaSewnSynchronizedLcmRay x P e =
      gammaSewnSynchronizedLcmNumerator x P *
        gammaSewnSynchronizedLcmNode x P ^ e := by
  classical
  calc
    gammaSewnSynchronizedLcmRay x P e =
        ∏ p ∈ P,
          ((gammaSewnMobiusValuationContractionMultiplier x p *
              (xiTransversePrimeApertureDiskNode 1 p /
                (1 + xiTransversePrimeApertureDiskNode 1 p)) *
              (1 - xiMobiusContinuousApertureDiskNode x p)) *
            xiMobiusContinuousApertureDiskNode x p ^ e) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [gammaSewnMobiusContinuousApertureFeature,
        xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
      ring
    _ = (∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            (xiTransversePrimeApertureDiskNode 1 p /
              (1 + xiTransversePrimeApertureDiskNode 1 p)) *
            (1 - xiMobiusContinuousApertureDiskNode x p))) *
        (∏ p ∈ P, xiMobiusContinuousApertureDiskNode x p ^ e) := by
      rw [Finset.prod_mul_distrib]
    _ = gammaSewnSynchronizedLcmNumerator x P *
        gammaSewnSynchronizedLcmNode x P ^ e := by
      simp only [gammaSewnSynchronizedLcmNumerator,
        gammaSewnSynchronizedLcmNode, Finset.prod_pow]

/-- A nonempty synchronized support has a genuine open-disk geometric ratio. -/
theorem gammaSewnSynchronizedLcmNode_nonneg_lt_one
    {x : ℝ} (hx : 0 < x) {P : Finset Nat.Primes} (hP : P.Nonempty) :
    0 ≤ gammaSewnSynchronizedLcmNode x P ∧
      gammaSewnSynchronizedLcmNode x P < 1 := by
  classical
  induction P using Finset.induction_on with
  | empty => simp at hP
  | @insert p P hp ih =>
      by_cases hPempty : P = ∅
      · subst P
        simp [gammaSewnSynchronizedLcmNode,
          (xiMobiusContinuousApertureDiskNode_pos x p).le,
          xiMobiusContinuousApertureDiskNode_lt_one hx p]
      · have hrest := ih (Finset.nonempty_iff_ne_empty.mpr hPempty)
        have hp0 := (xiMobiusContinuousApertureDiskNode_pos x p).le
        have hp1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
        simp only [gammaSewnSynchronizedLcmNode, Finset.prod_insert hp]
        exact ⟨mul_nonneg hp0 hrest.1,
          mul_lt_one_of_nonneg_of_lt_one_left hp0 hp1 hrest.2.le⟩

/-- **All-lcm collapse.**  The common-depth completion is the closed synchronized coefficient. -/
theorem tsum_gammaSewnSynchronizedLcmRay_eq_weight
    {x : ℝ} (hx : 0 < x) {P : Finset Nat.Primes} (hP : P.Nonempty) :
    (∑' e : ℕ, gammaSewnSynchronizedLcmRay x P e) =
      gammaSewnSynchronizedLcmWeight x P := by
  rw [gammaSewnSynchronizedLcmWeight, if_neg hP.ne_empty,
    show (fun e : ℕ => gammaSewnSynchronizedLcmRay x P e) =
        (fun e : ℕ => gammaSewnSynchronizedLcmNumerator x P *
          gammaSewnSynchronizedLcmNode x P ^ e) by
      funext e
      exact gammaSewnSynchronizedLcmRay_eq_geometric x P e,
    tsum_mul_left]
  rw [tsum_geometric_of_lt_one
    (gammaSewnSynchronizedLcmNode_nonneg_lt_one hx hP).1
    (gammaSewnSynchronizedLcmNode_nonneg_lt_one hx hP).2]
  simp only [div_eq_mul_inv]

/-- Singleton support is exactly the completed Gamma-sewn source ray. -/
theorem gammaSewnSynchronizedLcmWeight_singleton
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnSynchronizedLcmWeight x {p} =
      gammaSewnMobiusValuationContractionMultiplier x p *
        (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) := by
  have hr := xiMobiusContinuousApertureDiskNode_lt_one hx p
  simp only [gammaSewnSynchronizedLcmWeight, Finset.singleton_ne_empty,
    if_false, gammaSewnSynchronizedLcmNumerator,
    gammaSewnSynchronizedLcmNode, Finset.prod_singleton]
  field_simp [sub_ne_zero.mpr hr.ne']

/-- At arity two, synchronization is exactly the already constructed Gamma-sewn Gram kernel. -/
theorem gammaSewnSynchronizedLcmWeight_pair
    {x : ℝ} (hx : 0 < x) {p r : Nat.Primes} (hpr : p ≠ r) :
    gammaSewnSynchronizedLcmWeight x {p, r} =
      gammaSewnMobiusContinuousAperturePrimeKernel x p r := by
  rw [← tsum_gammaSewnSynchronizedLcmRay_eq_weight hx
    (show ({p, r} : Finset Nat.Primes).Nonempty by simp),
    ← tsum_gammaSewnMobiusContinuousApertureFeature_mul_eq_kernel hx p r]
  apply tsum_congr
  intro e
  simp [gammaSewnSynchronizedLcmRay, hpr]

/-! ## Rees-boundary recovery of the physical lcm density -/

/-- The predicted nonzero boundary symbol after removing the exact aperture order
`P.card - 1` from a synchronized support. -/
def gammaSewnSynchronizedLcmReesBoundary
    (P : Finset Nat.Primes) : ℝ :=
  if P = ∅ then 1 else
    (∏ p ∈ P, Real.log (p : ℝ) / ((p : ℝ) + 1)) /
      (∑ p ∈ P, Real.log (p : ℝ))

/-- A multiplicative squarefree density specified by its local prime root counts. -/
def synchronizedSquarefreePhysicalDensity
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ P, nu p / (p : ℝ)

/-- Exact boundary multiplier from the synchronized Rees symbol to a prescribed multiplicative
physical density.  For the quadratic congruence source, `nu p` is always `1` or `2`. -/
def gammaSewnSynchronizedDensityRecovery
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes) : ℝ :=
  (∑ p ∈ P, Real.log (p : ℝ)) *
    ∏ p ∈ P,
      nu p * ((p : ℝ) + 1) / ((p : ℝ) * Real.log (p : ℝ))

/-- **Exact resolution recovery.**  The collective lcm multiplier recovers the literal
multiplicative physical density from the synchronized Rees boundary.  No primewise inverse of the
Gamma-sewn contraction occurs. -/
theorem gammaSewnSynchronizedDensityRecovery_mul_reesBoundary
    (nu : Nat.Primes → ℝ) {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedDensityRecovery nu P *
        gammaSewnSynchronizedLcmReesBoundary P =
      synchronizedSquarefreePhysicalDensity nu P := by
  have hsum : 0 < ∑ p ∈ P, Real.log (p : ℝ) := by
    apply Finset.sum_pos
    intro p hp
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
    exact hP
  have hlocal (p : Nat.Primes) :
      (nu p * ((p : ℝ) + 1) / ((p : ℝ) * Real.log (p : ℝ))) *
          (Real.log (p : ℝ) / ((p : ℝ) + 1)) =
        nu p / (p : ℝ) := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    field_simp [hp0, (Real.log_pos hp1).ne']
  unfold gammaSewnSynchronizedDensityRecovery
    gammaSewnSynchronizedLcmReesBoundary
    synchronizedSquarefreePhysicalDensity
  rw [if_neg hP.ne_empty]
  field_simp [hsum.ne']
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p hp => hlocal p)

/-! ## Finite-aperture defect and the rank boundary of scalar recovery -/

/-- The all-grade Rees renormalization, with the Boolean vacuum fixed separately. -/
def gammaSewnSynchronizedLcmReesRenormalizedWeight
    (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  if P = ∅ then 1 else
    gammaSewnSynchronizedLcmWeight x P / x ^ (P.card - 1)

/-- Finite-aperture density recovery.  The vacuum is fixed to `1`; it is not obtained from the
nonempty-support recovery formula, whose logarithmic prefactor vanishes on the empty support. -/
def gammaSewnSynchronizedRecoveredDensity
    (nu : Nat.Primes → ℝ) (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  if P = ∅ then 1 else
    gammaSewnSynchronizedDensityRecovery nu P *
      gammaSewnSynchronizedLcmReesRenormalizedWeight x P

@[simp] theorem gammaSewnSynchronizedRecoveredDensity_empty
    (nu : Nat.Primes → ℝ) (x : ℝ) :
    gammaSewnSynchronizedRecoveredDensity nu x ∅ = 1 := by
  simp [gammaSewnSynchronizedRecoveredDensity]

/-- On a singleton, finite-aperture recovery is the physical local density times the strict
Gamma-sewn contraction multiplier.  Thus literal physical recovery occurs only at the Rees
boundary, not at a positive aperture. -/
theorem gammaSewnSynchronizedRecoveredDensity_singleton
    (nu : Nat.Primes → ℝ) {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnSynchronizedRecoveredDensity nu x {p} =
      (nu p / (p : ℝ)) * gammaSewnMobiusValuationContractionMultiplier x p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  rw [gammaSewnSynchronizedRecoveredDensity,
    if_neg (Finset.singleton_ne_empty p),
    gammaSewnSynchronizedLcmReesRenormalizedWeight,
    if_neg (Finset.singleton_ne_empty p)]
  simp only [gammaSewnSynchronizedDensityRecovery, Finset.sum_singleton,
    Finset.prod_singleton, Finset.card_singleton, Nat.reduceSubDiff, pow_zero, div_one]
  rw [gammaSewnSynchronizedLcmWeight_singleton hx,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  field_simp [hp0, hlog.ne']

/-- Every positive aperture strictly under-recovers every positive singleton density. -/
theorem gammaSewnSynchronizedRecoveredDensity_singleton_lt_physical
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    gammaSewnSynchronizedRecoveredDensity nu x {p} < nu p / (p : ℝ) := by
  rw [gammaSewnSynchronizedRecoveredDensity_singleton nu hx p]
  have hden : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  exact mul_lt_of_lt_one_right (div_pos (hnu p) hden)
    (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p)

/-- Exact singleton response defect. -/
theorem gammaSewnSynchronizedRecoveredDensity_singleton_defect
    (nu : Nat.Primes → ℝ) {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    nu p / (p : ℝ) - gammaSewnSynchronizedRecoveredDensity nu x {p} =
      (nu p / (p : ℝ)) *
        (1 - gammaSewnMobiusValuationContractionMultiplier x p) := by
  rw [gammaSewnSynchronizedRecoveredDensity_singleton nu hx p]
  ring

/-- The response defect begins at exact quadratic true-aperture order. -/
theorem gammaSewnSynchronizedRecoveredDensity_singleton_defect_eq_quadratic
    (nu : Nat.Primes → ℝ) {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    nu p / (p : ℝ) - gammaSewnSynchronizedRecoveredDensity nu x {p} =
      (nu p / (p : ℝ)) *
        (1 - xiMobiusContinuousApertureDiskNode x p) ^ 2 *
          gammaSewnMobiusValuationQuadraticDefectGain x p := by
  rw [gammaSewnSynchronizedRecoveredDensity_singleton_defect nu hx p,
    one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain]
  ring

/-- The exact low-support error exposed by the first nontrivial causal packet. -/
def gammaSewnSynchronizedSingletonResponseDefect
    (nu : Nat.Primes → ℝ) (x : ℝ) (S : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ S,
    (nu p / (p : ℝ) - gammaSewnSynchronizedRecoveredDensity nu x {p})

/-- The singleton response defect is strictly positive at every positive aperture.  In particular,
the recovered `{2,3,5}` low packet cannot equal the literal physical packet before the boundary. -/
theorem gammaSewnSynchronizedSingletonResponseDefect_pos
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x) {S : Finset Nat.Primes} (hS : S.Nonempty) :
    0 < gammaSewnSynchronizedSingletonResponseDefect nu x S := by
  unfold gammaSewnSynchronizedSingletonResponseDefect
  apply Finset.sum_pos
  · intro p hp
    exact sub_pos.mpr
      (gammaSewnSynchronizedRecoveredDensity_singleton_lt_physical nu hnu hx p)
  · exact hS

/-- The Cauchy pair symbol carried by the synchronized Rees boundary. -/
def synchronizedCauchyPairSymbol {α : Type*}
    (amplitude spectral : α → ℝ) (i j : α) : ℝ :=
  amplitude i * amplitude j / (spectral i + spectral j)

/-- Exact two-by-two Cauchy determinant factorization. -/
theorem synchronizedCauchyPairSymbol_two_by_two_det
    {α : Type*} (amplitude spectral : α → ℝ) (i₁ i₂ j₁ j₂ : α)
    (h11 : spectral i₁ + spectral j₁ ≠ 0)
    (h12 : spectral i₁ + spectral j₂ ≠ 0)
    (h21 : spectral i₂ + spectral j₁ ≠ 0)
    (h22 : spectral i₂ + spectral j₂ ≠ 0) :
    synchronizedCauchyPairSymbol amplitude spectral i₁ j₁ *
          synchronizedCauchyPairSymbol amplitude spectral i₂ j₂ -
        synchronizedCauchyPairSymbol amplitude spectral i₁ j₂ *
          synchronizedCauchyPairSymbol amplitude spectral i₂ j₁ =
      amplitude i₁ * amplitude i₂ * amplitude j₁ * amplitude j₂ *
        ((spectral i₁ - spectral i₂) * (spectral j₁ - spectral j₂)) /
        ((spectral i₁ + spectral j₁) * (spectral i₁ + spectral j₂) *
          (spectral i₂ + spectral j₁) * (spectral i₂ + spectral j₂)) := by
  unfold synchronizedCauchyPairSymbol
  field_simp
  ring_nf

/-- Every nondegenerate two-by-two minor of the synchronized Cauchy symbol is nonzero. -/
theorem synchronizedCauchyPairSymbol_two_by_two_det_ne_zero
    {α : Type*} (amplitude spectral : α → ℝ) (i₁ i₂ j₁ j₂ : α)
    (hai₁ : amplitude i₁ ≠ 0) (hai₂ : amplitude i₂ ≠ 0)
    (haj₁ : amplitude j₁ ≠ 0) (haj₂ : amplitude j₂ ≠ 0)
    (hi : spectral i₁ ≠ spectral i₂) (hj : spectral j₁ ≠ spectral j₂)
    (h11 : spectral i₁ + spectral j₁ ≠ 0)
    (h12 : spectral i₁ + spectral j₂ ≠ 0)
    (h21 : spectral i₂ + spectral j₁ ≠ 0)
    (h22 : spectral i₂ + spectral j₂ ≠ 0) :
    synchronizedCauchyPairSymbol amplitude spectral i₁ j₁ *
          synchronizedCauchyPairSymbol amplitude spectral i₂ j₂ -
        synchronizedCauchyPairSymbol amplitude spectral i₁ j₂ *
          synchronizedCauchyPairSymbol amplitude spectral i₂ j₁ ≠ 0 := by
  rw [synchronizedCauchyPairSymbol_two_by_two_det amplitude spectral i₁ i₂ j₁ j₂
    h11 h12 h21 h22]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hai₁ hai₂) haj₁) haj₂)
      (mul_ne_zero (sub_ne_zero.mpr hi) (sub_ne_zero.mpr hj)))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h11 h12) h21) h22)

/-- The arity-two Rees boundary is a weighted Cauchy kernel in the prime logarithms. -/
theorem gammaSewnSynchronizedLcmReesBoundary_pair
    {p q : Nat.Primes} (hpq : p ≠ q) :
    gammaSewnSynchronizedLcmReesBoundary {p, q} =
      synchronizedCauchyPairSymbol
        (fun r : Nat.Primes => Real.log (r : ℝ) / ((r : ℝ) + 1))
        (fun r : Nat.Primes => Real.log (r : ℝ)) p q := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hqLog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.2.one_lt)
  simp [gammaSewnSynchronizedLcmReesBoundary, synchronizedCauchyPairSymbol, hpq]
  field_simp [(add_pos hpLog hqLog).ne']

/-- Scalar physical-density recovery has product rank one on the pair layer. -/
theorem synchronizedSquarefreePhysicalDensity_pair_det_zero
    (nu : Nat.Primes → ℝ)
    (p₁ p₂ q₁ q₂ : Nat.Primes)
    (h11 : p₁ ≠ q₁) (h12 : p₁ ≠ q₂)
    (h21 : p₂ ≠ q₁) (h22 : p₂ ≠ q₂) :
    synchronizedSquarefreePhysicalDensity nu {p₁, q₁} *
          synchronizedSquarefreePhysicalDensity nu {p₂, q₂} -
        synchronizedSquarefreePhysicalDensity nu {p₁, q₂} *
          synchronizedSquarefreePhysicalDensity nu {p₂, q₁} = 0 := by
  simp [synchronizedSquarefreePhysicalDensity, h11, h12, h21, h22]
  field_simp [p₁.2.ne_zero, p₂.2.ne_zero, q₁.2.ne_zero, q₂.2.ne_zero]
  ring

/-- In contrast to physical product density, every nondegenerate two-by-two prime-log Cauchy minor
of the synchronized Rees boundary is nonzero.  A scalar exact-density recovery therefore discards
the first coupled rank already at arity two. -/
theorem gammaSewnSynchronizedLcmReesBoundary_pair_det_ne_zero
    (p₁ p₂ q₁ q₂ : Nat.Primes)
    (hi : p₁ ≠ p₂) (hj : q₁ ≠ q₂)
    (h11 : p₁ ≠ q₁) (h12 : p₁ ≠ q₂)
    (h21 : p₂ ≠ q₁) (h22 : p₂ ≠ q₂) :
    gammaSewnSynchronizedLcmReesBoundary {p₁, q₁} *
          gammaSewnSynchronizedLcmReesBoundary {p₂, q₂} -
        gammaSewnSynchronizedLcmReesBoundary {p₁, q₂} *
          gammaSewnSynchronizedLcmReesBoundary {p₂, q₁} ≠ 0 := by
  rw [gammaSewnSynchronizedLcmReesBoundary_pair h11,
    gammaSewnSynchronizedLcmReesBoundary_pair h22,
    gammaSewnSynchronizedLcmReesBoundary_pair h12,
    gammaSewnSynchronizedLcmReesBoundary_pair h21]
  let amplitude : Nat.Primes → ℝ :=
    fun r => Real.log (r : ℝ) / ((r : ℝ) + 1)
  let spectral : Nat.Primes → ℝ := fun r => Real.log (r : ℝ)
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hamp (p : Nat.Primes) : amplitude p ≠ 0 :=
    div_ne_zero (hlog p).ne' (by positivity)
  have hspec {p q : Nat.Primes} (hpq : p ≠ q) : spectral p ≠ spectral q := by
    intro heq
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.2.pos
    have hpqR : (p : ℝ) = (q : ℝ) :=
      Real.strictMonoOn_log.injOn hp0 hq0 heq
    apply hpq
    apply Subtype.ext
    exact_mod_cast hpqR
  apply synchronizedCauchyPairSymbol_two_by_two_det_ne_zero
  · exact hamp p₁
  · exact hamp p₂
  · exact hamp q₁
  · exact hamp q₂
  · exact hspec hi
  · exact hspec hj
  all_goals
    dsimp only [spectral]
    exact (add_pos (hlog _) (hlog _)).ne'

/-- State-dependent gain for adjoining a new prime to a nonempty lcm support. -/
def gammaSewnSynchronizedLcmInsertionGain
    (x : ℝ) (p : Nat.Primes) (P : Finset Nat.Primes) : ℝ :=
  gammaSewnMobiusValuationContractionMultiplier x p *
    (xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) *
    (1 - xiMobiusContinuousApertureDiskNode x p) *
    (1 - gammaSewnSynchronizedLcmNode x P) /
    (1 - xiMobiusContinuousApertureDiskNode x p *
      gammaSewnSynchronizedLcmNode x P)

/-- Adjoining a prime multiplies the all-lcm weight by the explicit state-dependent gain. -/
theorem gammaSewnSynchronizedLcmWeight_insert
    {x : ℝ} (hx : 0 < x) {p : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) :
    gammaSewnSynchronizedLcmWeight x (insert p P) =
      gammaSewnSynchronizedLcmInsertionGain x p P *
        gammaSewnSynchronizedLcmWeight x P := by
  have hnodeP := gammaSewnSynchronizedLcmNode_nonneg_lt_one hx hP
  have hnodeInsert := gammaSewnSynchronizedLcmNode_nonneg_lt_one hx
    (Finset.insert_nonempty p P)
  rw [gammaSewnSynchronizedLcmWeight, if_neg (Finset.insert_nonempty p P).ne_empty,
    gammaSewnSynchronizedLcmWeight, if_neg hP.ne_empty]
  have hnum : gammaSewnSynchronizedLcmNumerator x (insert p P) =
      (gammaSewnMobiusValuationContractionMultiplier x p *
        (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) *
        (1 - xiMobiusContinuousApertureDiskNode x p)) *
          gammaSewnSynchronizedLcmNumerator x P := by
    simp [gammaSewnSynchronizedLcmNumerator, hp]
  have hnode : gammaSewnSynchronizedLcmNode x (insert p P) =
      xiMobiusContinuousApertureDiskNode x p *
        gammaSewnSynchronizedLcmNode x P := by
    simp [gammaSewnSynchronizedLcmNode, hp]
  rw [hnum, hnode]
  unfold gammaSewnSynchronizedLcmInsertionGain
  field_simp [sub_ne_zero.mpr hnodeP.2.ne',
    sub_ne_zero.mpr (hnode ▸ hnodeInsert.2).ne']

/-- **Three-prime falsifier, in general form.**  Every two-step future insertion commutes.  The
gain is not prime-diagonal, but it is a flat multiplicative connection on the Boolean lcm cube. -/
theorem gammaSewnSynchronizedLcmInsertionGain_cocycle
    {x : ℝ} (hx : 0 < x) {p q : Nat.Primes} {P : Finset Nat.Primes}
    (hP : P.Nonempty) (hp : p ∉ P) (hq : q ∉ P) (hpq : p ≠ q) :
    gammaSewnSynchronizedLcmInsertionGain x p P *
        gammaSewnSynchronizedLcmInsertionGain x q (insert p P) =
      gammaSewnSynchronizedLcmInsertionGain x q P *
        gammaSewnSynchronizedLcmInsertionGain x p (insert q P) := by
  have hwp : gammaSewnSynchronizedLcmWeight x P ≠ 0 := by
    rw [gammaSewnSynchronizedLcmWeight, if_neg hP.ne_empty]
    have hnum : 0 < gammaSewnSynchronizedLcmNumerator x P := by
      unfold gammaSewnSynchronizedLcmNumerator
      apply Finset.prod_pos
      intro r hr
      exact mul_pos
        (mul_pos
          (gammaSewnMobiusValuationContractionMultiplier_pos x r)
          (div_pos
            (xiTransversePrimeApertureDiskNode_pos 1 r)
            (by linarith [xiTransversePrimeApertureDiskNode_pos 1 r])))
        (sub_pos.mpr (xiMobiusContinuousApertureDiskNode_lt_one hx r))
    exact (div_pos hnum
      (sub_pos.mpr
        (gammaSewnSynchronizedLcmNode_nonneg_lt_one hx hP).2)).ne'
  apply mul_right_cancel₀ hwp
  calc
    (gammaSewnSynchronizedLcmInsertionGain x p P *
          gammaSewnSynchronizedLcmInsertionGain x q (insert p P)) *
        gammaSewnSynchronizedLcmWeight x P =
      gammaSewnSynchronizedLcmInsertionGain x q (insert p P) *
        (gammaSewnSynchronizedLcmInsertionGain x p P *
          gammaSewnSynchronizedLcmWeight x P) := by ring
    _ = gammaSewnSynchronizedLcmInsertionGain x q (insert p P) *
        gammaSewnSynchronizedLcmWeight x (insert p P) := by
      rw [gammaSewnSynchronizedLcmWeight_insert hx hP hp]
    _ = gammaSewnSynchronizedLcmWeight x (insert q (insert p P)) := by
      rw [gammaSewnSynchronizedLcmWeight_insert hx
        (Finset.insert_nonempty p P) (by simp [hq, hpq.symm])]
    _ = gammaSewnSynchronizedLcmWeight x (insert p (insert q P)) := by
      congr 1
      ext r
      simp [or_left_comm]
    _ = gammaSewnSynchronizedLcmInsertionGain x p (insert q P) *
        gammaSewnSynchronizedLcmWeight x (insert q P) := by
      rw [gammaSewnSynchronizedLcmWeight_insert hx
        (Finset.insert_nonempty q P) (by simp [hp, hpq])]
    _ = (gammaSewnSynchronizedLcmInsertionGain x q P *
          gammaSewnSynchronizedLcmInsertionGain x p (insert q P)) *
        gammaSewnSynchronizedLcmWeight x P := by
      rw [gammaSewnSynchronizedLcmWeight_insert hx hP hq]
      ring

end

end RHTower
