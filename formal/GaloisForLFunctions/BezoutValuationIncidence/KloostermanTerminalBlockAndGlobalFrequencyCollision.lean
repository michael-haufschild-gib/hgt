import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalFrequencyParseval
import GaloisForLFunctions.BezoutValuationIncidence.VaughanTypeIIShortAndAllHorizonMobiusL2Energy

/-!
# Kloosterman Terminal-Block GCD-Fiber Multiplicity and Global Frequency Collision Energy

In `RHTower/Sieve/KloostermanGlobalFrequencyParseval.lean`, all distinct-modulus Kloosterman
correlations on `[1, M]` are reduced (by `kloostermanNaturalCrossIntervalCorrelation_eq_terminalBlock_of_ne`)
to their incomplete terminal block `kloostermanNaturalCrossIntervalTerminalBlock` of length
`M % Nat.lcm (q + 1) (r + 1)` and aggregated into the common-period frequency receiver
`kloostermanGlobalFrequencyCollisionEnergy Q w B b`, leaving the fiberwise collision energy bound
open.

This module connects `BezoutValuationIncidence`'s Bézout/gcd-fiber and linear-band energy bounds
directly to `kloostermanGlobalCrossPhaseFrequency`, `kloostermanGlobalPairFrequencyCoefficient`,
and `kloostermanGlobalFrequencyCollisionEnergy`:

1. **Global Frequency Fiber Multiplicity (`card_kloostermanGlobalCrossPhaseFrequencyFibre_le_gcd`,
   `card_filter_kloostermanGlobalCrossPhaseFrequency_le_gcd`):**
   For any stored moduli `q, r ∈ Q` and any common-period frequency
   `z : ZMod (kloostermanGlobalPeriod Q)`, the fiber of
   `kloostermanGlobalCrossPhaseFrequency Q q r` over `z` embeds injectively into
   `Fin ((q + 1).gcd (r + 1))` via `kloostermanProductGcdSliceLabel (q + 1) (r + 1)`, so its
   cardinality is at most `gcd(q + 1, r + 1)`.
2. **Fiberwise Cauchy–Schwarz and Parseval for Global Pair Coefficients
   (`sum_normSq_kloostermanGlobalPairFrequencyCoefficient_le_gcd_mul_fourierEnergy`,
   `sum_normSq_kloostermanGlobalPairFrequencyCoefficient_le_gcd_mul_residueEnergy`):**
   Summing the squared global pair coefficients over `ZMod (kloostermanGlobalPeriod Q)` partitions
   `(ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ` fiberwise, bounding the global frequency `L²` energy of the
   pair `(q, r)` by `gcd(q + 1, r + 1) * ‖w q‖^2 * ‖w r‖^2 * E_res(q, B, b) * E_res(r, B, b)`.
3. **Unconditional Global Frequency Collision Energy and Linear-Band Type-II Source Bounds
   (`kloostermanGlobalFrequencyCollisionEnergy_le_gcd_residueEnergy`,
   `kloostermanIntervalSourceEnergyBudget_typeIIShort_le_band_width_sq`,
   `norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_gcd_residueEnergy_erase_zero`):**
   Bounds `kloostermanGlobalFrequencyCollisionEnergy Q w B b` unconditionally in terms of the
   pairwise gcd-weighted source residue energies, and combines with BVI's log-free short-side
   bound `sum_typeIIShort_sq_le_band_width_sq` when the source coefficients are `typeIIShort V`.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset RHTower RHTower.Sieve
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Global Cross-Phase Frequency Fiber Multiplicity -/

/-- Fiber of `kloostermanGlobalCrossPhaseFrequency Q q r` over a common-period frequency
`z : ZMod (kloostermanGlobalPeriod Q)`. -/
def kloostermanGlobalCrossPhaseFrequencyFibre
    (Q : Finset ℕ) (q r : ℕ)
    (z : ZMod (kloostermanGlobalPeriod Q)) :=
  {p : (ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ //
    kloostermanGlobalCrossPhaseFrequency Q q r p.1 p.2 = z}

noncomputable instance kloostermanGlobalCrossPhaseFrequencyFibreFintype
    (Q : Finset ℕ) (q r : ℕ)
    (z : ZMod (kloostermanGlobalPeriod Q)) :
    Fintype (kloostermanGlobalCrossPhaseFrequencyFibre Q q r z) := by
  classical
  unfold kloostermanGlobalCrossPhaseFrequencyFibre
  infer_instance

/-- For any stored moduli `q, r ∈ Q`, the global cross-phase frequency fiber over any
`z : ZMod (kloostermanGlobalPeriod Q)` has cardinality at most `gcd(q + 1, r + 1)`. -/
theorem card_kloostermanGlobalCrossPhaseFrequencyFibre_le_gcd
    (Q : Finset ℕ) {q r : ℕ} (hq : q ∈ Q) (hr : r ∈ Q)
    (z : ZMod (kloostermanGlobalPeriod Q)) :
    Fintype.card (kloostermanGlobalCrossPhaseFrequencyFibre Q q r z) ≤
      (q + 1).gcd (r + 1) := by
  classical
  letI : NeZero ((q + 1) * (r + 1)) :=
    ⟨Nat.mul_ne_zero (Nat.succ_ne_zero q) (Nat.succ_ne_zero r)⟩
  let label : kloostermanGlobalCrossPhaseFrequencyFibre Q q r z →
      Fin ((q + 1).gcd (r + 1)) :=
    fun p => kloostermanProductGcdSliceLabel (q + 1) (r + 1) p.1
  have hinj : Function.Injective label := by
    intro p p' hlabel
    apply Subtype.ext
    apply kloostermanProductCrossPhaseFrequency_injective_on_gcdSlice
      (q + 1) (r + 1) p.1 p'.1 hlabel
    have hglob : kloostermanGlobalCrossPhaseFrequency Q q r p.1.1 p.1.2 =
        kloostermanGlobalCrossPhaseFrequency Q q r p'.1.1 p'.1.2 :=
      p.2.trans p'.2.symm
    have hratio : kloostermanCrossPhaseRatio (q + 1) (r + 1) p.1.1 p.1.2 =
        kloostermanCrossPhaseRatio (q + 1) (r + 1) p'.1.1 p'.1.2 :=
      (kloostermanGlobalCrossPhaseFrequency_eq_iff
        Q q r q r hq hr hq hr p.1.1 p.1.2 p'.1.1 p'.1.2).mp hglob
    apply stdAddChar_injective ((q + 1) * (r + 1))
    change ZMod.stdAddChar
        (kloostermanProductCrossPhaseFrequency (q + 1) (r + 1) p.1.1 p.1.2) =
      ZMod.stdAddChar
        (kloostermanProductCrossPhaseFrequency (q + 1) (r + 1) p'.1.1 p'.1.2)
    rw [kloostermanProductCrossPhaseFrequency_phase,
      kloostermanProductCrossPhaseFrequency_phase]
    exact hratio
  simpa [label] using Fintype.card_le_of_injective label hinj

/-- Finset-filter form of the global cross-phase frequency fiber bound. -/
theorem card_filter_kloostermanGlobalCrossPhaseFrequency_le_gcd
    (Q : Finset ℕ) {q r : ℕ} (hq : q ∈ Q) (hr : r ∈ Q)
    (z : ZMod (kloostermanGlobalPeriod Q)) :
    ((Finset.univ : Finset ((ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ)).filter
      (fun p => kloostermanGlobalCrossPhaseFrequency Q q r p.1 p.2 = z)).card ≤
      (q + 1).gcd (r + 1) := by
  classical
  have hcard :
      ((Finset.univ : Finset ((ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ)).filter
        (fun p => kloostermanGlobalCrossPhaseFrequency Q q r p.1 p.2 = z)).card =
        Fintype.card (kloostermanGlobalCrossPhaseFrequencyFibre Q q r z) := by
    unfold kloostermanGlobalCrossPhaseFrequencyFibre
    exact (Fintype.card_subtype
      (fun p : (ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ =>
        kloostermanGlobalCrossPhaseFrequency Q q r p.1 p.2 = z)).symm
  rw [hcard]
  exact card_kloostermanGlobalCrossPhaseFrequencyFibre_le_gcd Q hq hr z

/-! ## §2. Fiberwise Cauchy–Schwarz and Parseval for Global Pair Frequency Coefficients -/

/-- Rewrites `kloostermanGlobalPairFrequencyCoefficient` as a filtered sum over the product of unit
groups `(ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ`. -/
theorem kloostermanGlobalPairFrequencyCoefficient_eq_sum_filter
    (Q : Finset ℕ) (q r : ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (z : ZMod (kloostermanGlobalPeriod Q)) :
    kloostermanGlobalPairFrequencyCoefficient Q q r w B b z =
      ∑ p ∈ (Finset.univ : Finset ((ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ)).filter
          (fun p => kloostermanGlobalCrossPhaseFrequency Q q r p.1 p.2 = z),
        star (w q) * w r *
          (star (kloostermanSourceFourier (q + 1) B b p.1) *
            kloostermanSourceFourier (r + 1) B b p.2) := by
  classical
  unfold kloostermanGlobalPairFrequencyCoefficient
  symm
  rw [Finset.sum_filter, Fintype.sum_prod_type]

private theorem norm_sum_sq_le_card_mul_sum_norm_sq
    {α : Type*} (S : Finset α) (f : α → ℂ) :
    ‖∑ p ∈ S, f p‖ ^ (2 : ℕ) ≤
      (S.card : ℝ) * ∑ p ∈ S, ‖f p‖ ^ (2 : ℕ) := by
  have htri : ‖∑ p ∈ S, f p‖ ≤ ∑ p ∈ S, ‖f p‖ := norm_sum_le _ _
  calc
    ‖∑ p ∈ S, f p‖ ^ (2 : ℕ) ≤ (∑ p ∈ S, ‖f p‖) ^ (2 : ℕ) := by
      nlinarith [norm_nonneg (∑ p ∈ S, f p)]
    _ ≤ (S.card : ℝ) * ∑ p ∈ S, ‖f p‖ ^ (2 : ℕ) :=
      sq_sum_le_card_mul_sum_sq

/-- Pointwise fiber Cauchy–Schwarz bound on one global pair frequency coefficient using the
`gcd(q + 1, r + 1)` fiber multiplicity bound. -/
theorem norm_kloostermanGlobalPairFrequencyCoefficient_sq_le_gcd_mul_filter_sum
    (Q : Finset ℕ) {q r : ℕ} (hq : q ∈ Q) (hr : r ∈ Q) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (z : ZMod (kloostermanGlobalPeriod Q)) :
    ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) ≤
      ((q + 1).gcd (r + 1) : ℝ) * (‖w q‖ ^ (2 : ℕ) * ‖w r‖ ^ (2 : ℕ)) *
        ∑ p ∈ (Finset.univ : Finset ((ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ)).filter
            (fun p => kloostermanGlobalCrossPhaseFrequency Q q r p.1 p.2 = z),
          ‖kloostermanSourceFourier (q + 1) B b p.1‖ ^ (2 : ℕ) *
            ‖kloostermanSourceFourier (r + 1) B b p.2‖ ^ (2 : ℕ) := by
  classical
  rw [kloostermanGlobalPairFrequencyCoefficient_eq_sum_filter]
  let F := (Finset.univ : Finset ((ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ)).filter
    (fun p => kloostermanGlobalCrossPhaseFrequency Q q r p.1 p.2 = z)
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq F
    (fun p => star (w q) * w r *
      (star (kloostermanSourceFourier (q + 1) B b p.1) *
        kloostermanSourceFourier (r + 1) B b p.2))
  have hcard : (F.card : ℝ) ≤ ((q + 1).gcd (r + 1) : ℝ) := by
    exact_mod_cast card_filter_kloostermanGlobalCrossPhaseFrequency_le_gcd Q hq hr z
  have hnorm : ∀ p ∈ F,
      ‖star (w q) * w r *
        (star (kloostermanSourceFourier (q + 1) B b p.1) *
          kloostermanSourceFourier (r + 1) B b p.2)‖ ^ (2 : ℕ) =
        (‖w q‖ ^ (2 : ℕ) * ‖w r‖ ^ (2 : ℕ)) *
          (‖kloostermanSourceFourier (q + 1) B b p.1‖ ^ (2 : ℕ) *
            ‖kloostermanSourceFourier (r + 1) B b p.2‖ ^ (2 : ℕ)) := by
    intro p _
    simp only [norm_mul, norm_star]
    ring
  refine hcs.trans ?_
  rw [Finset.sum_congr rfl hnorm, ← Finset.mul_sum, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard (by positivity)) ?_
  exact Finset.sum_nonneg fun _ _ => by positivity

/-- Summing the squared global pair frequency coefficients over `ZMod (kloostermanGlobalPeriod Q)`
partitions `(ZMod (q + 1))ˣ × (ZMod (r + 1))ˣ` fiberwise, bounding the global frequency energy by
`gcd(q + 1, r + 1)` times the product of the source Fourier energies. -/
theorem sum_normSq_kloostermanGlobalPairFrequencyCoefficient_le_gcd_mul_fourierEnergy
    (Q : Finset ℕ) {q r : ℕ} (hq : q ∈ Q) (hr : r ∈ Q) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
      ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ)) ≤
      ((q + 1).gcd (r + 1) : ℝ) * (‖w q‖ ^ (2 : ℕ) * ‖w r‖ ^ (2 : ℕ)) *
        ((∑ x : (ZMod (q + 1))ˣ, ‖kloostermanSourceFourier (q + 1) B b x‖ ^ (2 : ℕ)) *
          ∑ y : (ZMod (r + 1))ˣ, ‖kloostermanSourceFourier (r + 1) B b y‖ ^ (2 : ℕ)) := by
  classical
  refine (Finset.sum_le_sum fun z _ =>
    norm_kloostermanGlobalPairFrequencyCoefficient_sq_le_gcd_mul_filter_sum
      Q hq hr w B b z).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  rw [Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-- Combining the global fiberwise bound with source Fourier Parseval
(`sum_normSq_kloostermanSourceFourier_le_residueEnergy`) bounds the global frequency `L²` energy
of one modulus pair `(q, r)` by `gcd(q + 1, r + 1) * ‖w q‖^2 * ‖w r‖^2` times the product of the
source residue-collision energies. -/
theorem sum_normSq_kloostermanGlobalPairFrequencyCoefficient_le_gcd_mul_residueEnergy
    (Q : Finset ℕ) {q r : ℕ} (hq : q ∈ Q) (hr : r ∈ Q) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
      ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ)) ≤
      ((q + 1).gcd (r + 1) : ℝ) * (‖w q‖ ^ (2 : ℕ) * ‖w r‖ ^ (2 : ℕ)) *
        (kloostermanSourceResidueEnergy q B b *
          kloostermanSourceResidueEnergy r B b) := by
  refine (sum_normSq_kloostermanGlobalPairFrequencyCoefficient_le_gcd_mul_fourierEnergy
    Q hq hr w B b).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hqF : (∑ x : (ZMod (q + 1))ˣ, ‖kloostermanSourceFourier (q + 1) B b x‖ ^ (2 : ℕ)) ≤
      kloostermanSourceResidueEnergy q B b := by
    unfold kloostermanSourceResidueEnergy
    simpa only [Complex.sq_norm] using
      sum_normSq_kloostermanSourceFourier_le_residueEnergy (q + 1) B b
  have hrF : (∑ y : (ZMod (r + 1))ˣ, ‖kloostermanSourceFourier (r + 1) B b y‖ ^ (2 : ℕ)) ≤
      kloostermanSourceResidueEnergy r B b := by
    unfold kloostermanSourceResidueEnergy
    simpa only [Complex.sq_norm] using
      sum_normSq_kloostermanSourceFourier_le_residueEnergy (r + 1) B b
  have hq0 : 0 ≤ kloostermanSourceResidueEnergy q B b := by
    unfold kloostermanSourceResidueEnergy
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  exact mul_le_mul hqF hrF (Finset.sum_nonneg fun _ _ => sq_nonneg _) hq0

/-! ## §3. Unconditional Bounds on `kloostermanGlobalFrequencyCollisionEnergy` -/

/-- Cauchy–Schwarz across the off-diagonal modulus pairs `(q, r)` bounds the global frequency
collision energy by `|Q|^2` times the sum of the pairwise global frequency energies. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_sum_pairFrequencyEnergy
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      (Q.card : ℝ) ^ (2 : ℕ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ∑ z : ZMod (kloostermanGlobalPeriod Q),
            ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) := by
  classical
  unfold kloostermanGlobalFrequencyCollisionEnergy kloostermanGlobalFrequencyCoefficient
  have hpoint : ∀ z : ZMod (kloostermanGlobalPeriod Q),
      ‖∑ q ∈ Q, ∑ r ∈ Q.erase q,
        kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) ≤
        (Q.card : ℝ) ^ (2 : ℕ) *
          ∑ q ∈ Q, ∑ r ∈ Q.erase q,
            ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) := by
    intro z
    have houter := norm_sum_sq_le_card_mul_sum_norm_sq Q
      (fun q => ∑ r ∈ Q.erase q, kloostermanGlobalPairFrequencyCoefficient Q q r w B b z)
    have hinner : ∀ q ∈ Q,
        ‖∑ r ∈ Q.erase q, kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) ≤
          (Q.card : ℝ) *
            ∑ r ∈ Q.erase q,
              ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) := by
      intro q _
      refine (norm_sum_sq_le_card_mul_sum_norm_sq (Q.erase q)
        (fun r => kloostermanGlobalPairFrequencyCoefficient Q q r w B b z)).trans ?_
      have hcard : ((Q.erase q).card : ℝ) ≤ (Q.card : ℝ) := by
        exact_mod_cast Finset.card_erase_le
      exact mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    refine houter.trans ?_
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hinner) (Nat.cast_nonneg _)).trans ?_
    rw [← Finset.mul_sum, ← mul_assoc, sq]
  refine (Finset.sum_le_sum fun z _ => hpoint z).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ z : ZMod (kloostermanGlobalPeriod Q),
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ))
      = ∑ q ∈ Q, ∑ z : ZMod (kloostermanGlobalPeriod Q), ∑ r ∈ Q.erase q,
          ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) := by
        rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ∑ z : ZMod (kloostermanGlobalPeriod Q),
            ‖kloostermanGlobalPairFrequencyCoefficient Q q r w B b z‖ ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_comm]

/-- **Unconditional GCD-Fiber Bound on `kloostermanGlobalFrequencyCollisionEnergy`
(`kloostermanGlobalFrequencyCollisionEnergy_le_gcd_residueEnergy`):**
Bounds the global frequency collision energy by `|Q|^2` times the gcd-weighted sum of pairwise
source residue-collision energies. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_le_gcd_residueEnergy
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b ≤
      (Q.card : ℝ) ^ (2 : ℕ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ((q + 1).gcd (r + 1) : ℝ) * (‖w q‖ ^ (2 : ℕ) * ‖w r‖ ^ (2 : ℕ)) *
            (kloostermanSourceResidueEnergy q B b *
              kloostermanSourceResidueEnergy r B b) := by
  refine (kloostermanGlobalFrequencyCollisionEnergy_le_sum_pairFrequencyEnergy Q w B b).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q hq =>
    Finset.sum_le_sum fun r hr => ?_) (sq_nonneg _)
  exact sum_normSq_kloostermanGlobalPairFrequencyCoefficient_le_gcd_mul_residueEnergy
    Q hq (Finset.mem_of_mem_erase hr) w B b

/-- Zero-mode-exact terminal Gram quadratic bound combining
`norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_globalFrequencyCollisionEnergy_erase_zero`
with the unconditional gcd-fiber collision energy bound. -/
theorem norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_gcd_residueEnergy_erase_zero
    (M : ℕ) (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    ‖kloostermanDistinctModulusTerminalGramQuadratic M Q w B b‖ ^ (2 : ℕ) ≤
      ((Q.card : ℝ) ^ (2 : ℕ) *
        ∑ q ∈ Q, ∑ r ∈ Q.erase q,
          ((q + 1).gcd (r + 1) : ℝ) * (‖w q‖ ^ (2 : ℕ) * ‖w r‖ ^ (2 : ℕ)) *
            (kloostermanSourceResidueEnergy q B b *
              kloostermanSourceResidueEnergy r B b)) *
        ((kloostermanGlobalPeriod Q : ℝ) *
            (M % kloostermanGlobalPeriod Q : ℕ) -
          ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ (2 : ℕ)) := by
  refine (norm_kloostermanDistinctModulusTerminalGramQuadratic_sq_le_globalFrequencyCollisionEnergy_erase_zero
    M Q w B b).trans ?_
  have horbit0 : 0 ≤ (kloostermanGlobalPeriod Q : ℝ) *
      (M % kloostermanGlobalPeriod Q : ℕ) -
      ((M % kloostermanGlobalPeriod Q : ℕ) : ℝ) ^ (2 : ℕ) := by
    rw [← sum_normSq_kloostermanGlobalTerminalOrbit_erase_zero_eq M Q]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right
    (kloostermanGlobalFrequencyCollisionEnergy_le_gcd_residueEnergy Q w B b) horbit0

/-! ## §4. Linear-Band Type-II Source Specialization for Interval Kloosterman Residue Energy -/

/-- When the Kloosterman source sequence on `[1, N]` is the Vaughan Type-II short coefficient
`b n = ((typeIIShort V n : ℝ) : ℂ)` in a linear horizon window `N ≤ (K + 1) * V` (`V, K ≥ 1`),
complementary-quotient compression (`sum_typeIIShort_sq_le_band_width_sq`) bounds the interval
source energy budget `kloostermanIntervalSourceEnergyBudget q N b` with no logarithmic factor. -/
theorem kloostermanIntervalSourceEnergyBudget_typeIIShort_le_band_width_sq
    (q : ℕ) {V K N : ℕ} (hV : 1 ≤ V) (hK : 1 ≤ K) (hhi : N ≤ (K + 1) * V) :
    kloostermanIntervalSourceEnergyBudget q N
        (fun n => ((typeIIShort V n : ℝ) : ℂ)) ≤
      ((q + 1 : ℕ) : ℝ) *
        ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
          ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ))) := by
  unfold kloostermanIntervalSourceEnergyBudget
  refine mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hnorm :
      (∑ n ∈ Finset.Icc 1 N, Complex.normSq ((typeIIShort V n : ℝ) : ℂ)) =
        ∑ n ∈ Finset.Icc 1 N, ‖((typeIIShort V n : ℝ) : ℂ)‖ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    exact (Complex.sq_norm _).symm
  rw [hnorm]
  exact sum_typeIIShort_sq_le_band_width_sq hV hK hhi

/-- Consequently, the exact Kloosterman source residue energy
`kloostermanSourceResidueEnergy q (Finset.Icc 1 N) (fun n => ((typeIIShort V n : ℝ) : ℂ))` is
bounded on any linear horizon window `N ≤ (K + 1) * V` by
`(q + 1) * kloostermanIntervalResidueMultiplicity q N * K^2 * (N - V)`. -/
theorem kloostermanSourceResidueEnergy_Icc_typeIIShort_le_band_width_sq
    (q : ℕ) {V K N : ℕ} (hV : 1 ≤ V) (hK : 1 ≤ K) (hhi : N ≤ (K + 1) * V) :
    kloostermanSourceResidueEnergy q (Finset.Icc 1 N)
        (fun n => ((typeIIShort V n : ℝ) : ℂ)) ≤
      ((q + 1 : ℕ) : ℝ) *
        ((kloostermanIntervalResidueMultiplicity q N : ℝ) *
          ((K : ℝ) ^ (2 : ℕ) * ((N - V : ℕ) : ℝ))) :=
  (kloostermanSourceResidueEnergy_Icc_le_intervalBudget q N
    (fun n => ((typeIIShort V n : ℝ) : ℂ))).trans
    (kloostermanIntervalSourceEnergyBudget_typeIIShort_le_band_width_sq q hV hK hhi)

end

end GaloisForLFunctions.BezoutValuationIncidence
