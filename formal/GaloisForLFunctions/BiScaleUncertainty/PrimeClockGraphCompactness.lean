import GaloisForLFunctions.RHTower.MobiusDivisorPrimeGraphClockRealization
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.Convex.Combination

/-!
# Compact prime-clock families in the complete graph

A fixed cutoff, a compact interval of logarithmic centers, and a bound on
total clock amplitude give a compact envelope in the mass-plus-edge norm.
The amplitude condition is imposed on the literal weights `sqrt N / p`.
-/

open Finset Set Filter Topology RHTower RHTower.CHMDDoobGraph
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.BiScaleUncertainty.PrimeClock
noncomputable section
set_option autoImplicit false

def curve (k : ℕ) : ℝ → SourceGraph :=
  criticalClockGraph (cutoff k)
    (boundedVariationOn_of_contDiff_compact ((cutoff_contDiff k).of_le (by norm_num))
      (cutoff_hasCompactSupport k))

theorem continuous_curve (k : ℕ) : Continuous (curve k) :=
  continuous_criticalClockGraph _ _ (cutoff_contDiff k).continuous (cutoff_hasCompactSupport k)

def packet (k N : ℕ) (S : Finset ℕ) : SourceGraph :=
  ∑ p ∈ S, canonicalPrimeGraphClockAtom k N p

theorem atom_eq (k N p : ℕ) :
    canonicalPrimeGraphClockAtom k N p =
      (Real.sqrt N / p) • curve k (Real.log ((N : ℝ) / p)) := rfl

/-- The clock normalization is retained in the full graph norm. -/
theorem atom_norm (k N p : ℕ) :
    ‖canonicalPrimeGraphClockAtom k N p‖ =
      (Real.sqrt N / p) * ‖curve k (Real.log ((N : ℝ) / p))‖ := by
  rw [atom_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg p))]

def centerHull (k : ℕ) (T R : ℝ) : Set SourceGraph :=
  closure (convexHull ℝ (insert 0 (curve k '' Icc T R)))

theorem isCompact_centerHull (k : ℕ) (T R : ℝ) : IsCompact (centerHull k T R) := by
  apply isCompact_iff_totallyBounded_isComplete.mpr
  refine ⟨?_, isClosed_closure.isComplete⟩
  exact (totallyBounded_convexHull _
    (((isCompact_Icc.image (continuous_curve k)).insert 0).totallyBounded)).closure

theorem zero_mem_centerHull (k : ℕ) (T R : ℝ) : (0 : SourceGraph) ∈ centerHull k T R :=
  subset_closure (subset_convexHull ℝ _ (mem_insert _ _))

def envelope (k : ℕ) (T R C : ℝ) : Set SourceGraph :=
  (fun z : ℝ × SourceGraph => z.1 • z.2) '' (Icc 0 C ×ˢ centerHull k T R)

theorem isCompact_envelope (k : ℕ) (T R C : ℝ) : IsCompact (envelope k T R C) :=
  (isCompact_Icc.prod (isCompact_centerHull k T R)).image
    (continuous_fst.smul continuous_snd)

theorem packet_mem_envelope (k N : ℕ) (S : Finset ℕ) (T R C : ℝ)
    (hcenter : ∀ p ∈ S, Real.log ((N : ℝ) / p) ∈ Icc T R)
    (hweight : (∑ p ∈ S, Real.sqrt N / (p : ℝ)) ≤ C) :
    packet k N S ∈ envelope k T R C := by
  classical
  let w : ℕ → ℝ := fun p => Real.sqrt N / p
  let z : ℕ → SourceGraph := fun p => curve k (Real.log ((N : ℝ) / p))
  have hw : ∀ p ∈ S, 0 ≤ w p := fun p _ =>
    div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg p)
  have hsum : 0 ≤ ∑ p ∈ S, w p := sum_nonneg hw
  have he : packet k N S = ∑ p ∈ S, w p • z p := rfl
  by_cases hz : ∑ p ∈ S, w p = 0
  · have hp : packet k N S = 0 := by
      rw [he]
      apply sum_eq_zero
      intro p hp
      rw [(sum_eq_zero_iff_of_nonneg hw).mp hz p hp, zero_smul]
    have hC : 0 ≤ C := by simpa only [w, hz] using hweight
    rw [hp]
    exact ⟨(0, 0), ⟨⟨le_rfl, hC⟩, zero_mem_centerHull k T R⟩, zero_smul ℝ 0⟩
  · have hpos : 0 < ∑ p ∈ S, w p := lt_of_le_of_ne hsum (Ne.symm hz)
    have hcm : S.centerMass w z ∈ centerHull k T R := by
      apply subset_closure
      apply (convex_convexHull ℝ _).centerMass_mem hw hpos
      intro p hp
      exact subset_convexHull ℝ _ (mem_insert_of_mem _ ⟨_, hcenter p hp, rfl⟩)
    refine ⟨(∑ p ∈ S, w p, S.centerMass w z), ⟨⟨hsum, hweight⟩, hcm⟩, ?_⟩
    simp only [Finset.centerMass, smul_smul, mul_inv_cancel₀ hz, one_smul]
    exact he.symm

/-- Actual-prime packets under explicit center and amplitude restrictions. -/
def confined (k : ℕ) (T R C : ℝ) : Set SourceGraph :=
  {q | ∃ N : ℕ, ∃ S : Finset ℕ,
    (∀ p ∈ S, p.Prime ∧ Real.log ((N : ℝ) / p) ∈ Icc T R) ∧
    (∑ p ∈ S, Real.sqrt N / (p : ℝ)) ≤ C ∧ q = packet k N S}

/-- Compactness holds in the complete receiving norm, including singular prime edges. -/
theorem isCompact_closure_confined (k : ℕ) (T R C : ℝ) :
    IsCompact (closure (confined k T R C)) := by
  apply (isCompact_envelope k T R C).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isCompact_envelope k T R C).isClosed
  rintro q ⟨N, S, hS, hweight, rfl⟩
  exact packet_mem_envelope k N S T R C (fun p hp => (hS p hp).2) hweight

end
end GaloisForLFunctions.BiScaleUncertainty.PrimeClock
