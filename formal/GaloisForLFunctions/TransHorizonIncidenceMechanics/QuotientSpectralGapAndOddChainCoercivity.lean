import GaloisForLFunctions.RHTower.CHMDCriticalBandReduction
import GaloisForLFunctions.RHTower.CHMDFullSpectralPairing
import GaloisForLFunctions.RHTower.CHMDOddSectorCriterion
import GaloisForLFunctions.RHTower.CHMDEvenSectorPointSpectrum
import GaloisForLFunctions.RHTower.CHMDPrimeChainSourceFactorization

/-!
# Pillar IV: Quotient Spectral Gap, Odd Primitive Orthogonality, and Complete Prime-Chain Coercivity (`QuotientSpectralGapAndOddChainCoercivity`)

This fourth foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**
establishes the archimedean–spectral operator framework on the quotient space
`signedRadicalᗮ` (`SourceGraph ⧸ signedRadical`), uniting:
- the critical-band radical reduction (`CHMDCriticalBandReduction`),
- the zero-silent polar pairing (`CHMDFullSpectralPairing`),
- the odd-sector spectral gap and unconditional simplicity of the ground eigenvalue `1`
  (`CHMDOddSectorCriterion`, `CHMDEvenSectorPointSpectrum`), and
- the complete bipartite prime-power chain variance factorization (`CHMDPrimeChainSourceFactorization`).

## Core Main Theorems (100% Unconditional)

1. **Automatic Primitive Orthogonality of the Odd Sector & Open Eigenvalue Interval `(1/2, 1)`
   (`inner_oneL_eq_zero_of_odd`, `odd_reducedSource_primitive`,
   `odd_eigenvector_eigenvalue_lt_one`,
   `not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one`)**:
   - Every odd vector `w ∈ MassSpace` (`reflectMass w = -w`) is automatically orthogonal to the
     ground state `oneL` (`⟪w, oneL⟫_ℝ = 0`), and its radical-reduced graph projection
     `reducedSource p` retains exact primitive orthogonality.
   - Consequently, by unconditional ergodicity of the archimedean jump measure
     (`eigenvalue_lt_one_of_primitive`), **every** nonzero odd eigenvector of `resolvent` has
     eigenvalue strictly below `1`, and `¬ RiemannHypothesis` is equivalent to the existence of a
     nonzero odd eigenvector of `resolvent` with eigenvalue strictly inside the open interval
     `μ ∈ Set.Ioo (1 / 2) 1`.

2. **Radical-Free Quotient Criterion for `RiemannHypothesis`
   (`riemannHypothesis_iff_odd_reducedSource_energy_nonneg`,
   `riemannHypothesis_of_primitive_radicalOrthogonal_energy_nonneg`)**:
   - Because `signedRadical` has zero slack (Wall 11), `sourceEnergy (reducedSource p) = sourceEnergy p`
     factors out the entire infinite-dimensional critical-band radical unconditionally, yielding:
     $$\text{RiemannHypothesis} \iff
       \forall p : \text{SourceGraph},\; p.\text{val.fst} \in \text{oddSector} \to
         0 \le \operatorname{sourceEnergy}(\operatorname{reducedSource} p).$$
   - In particular, non-negativity of `sourceEnergy` on primitive vectors in `signedRadicalᗮ`
     implies `RiemannHypothesis`.

3. **Zero-Silent Cosine-Null Positivity & Complete Odd Prime-Chain Coercivity Equivalence
   (`sourceEnergy_nonneg_of_fullSpectralNullspace_of_polarCosine_eq_zero`,
   `primeJump_tsum_eq_sameSide_add_chainIntegral`,
   `riemannHypothesis_iff_odd_primeChain_poincare`)**:
   - Every zero-silent vector `p ∈ fullSpectralNullspace` with vanishing polar cosine moment
     (`polarCosine p = 0`) has `sourceEnergy p = 2 * polarSine p ^ 2 ≥ 0`.
   - `RiemannHypothesis` is unconditionally equivalent to the statement that for every odd
     `v ∈ C²_c(ℝ)`, the sum of the archimedean jump energy, the same-side prime jump energies, and
     the complete bipartite prime-power chain variance sum `∑' q : ChainIndex, chainIntegral v q`
     dominates the quadratic polar mass `phiDoobCoshMass (fun x => v x ^ 2)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar RHTower.CHMDPrimeChain
open RHTower.CHMDPrimeChainSource RHTower.CHMDPrimeCuts RHTower.PhiDivisorEnergy
open scoped InnerProductSpace BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Automatic Primitive Orthogonality of the Odd Sector & Open Interval `(1/2, 1)` Spectrum -/

/-- **Automatic Ground-State Orthogonality of Odd Mass Vectors (`inner_oneL_eq_zero_of_odd`):**
Every odd vector `w : MassSpace` (`reflectMass w = -w`) is orthogonal to the ground state `oneL`. -/
theorem inner_oneL_eq_zero_of_odd {w : MassSpace} (hodd : reflectMass w = -w) :
    ⟪w, oneL⟫_ℝ = 0 := by
  have h := reflectMass.inner_map_map w oneL
  rw [hodd, reflectMass_oneL, inner_neg_left] at h
  linarith

/-- Membership in `oddSector` implies orthogonality to `oneL`. -/
theorem inner_oneL_eq_zero_of_mem_oddSector {w : MassSpace} (hw : w ∈ oddSector) :
    ⟪w, oneL⟫_ℝ = 0 :=
  inner_oneL_eq_zero_of_odd (mem_oddSector.mp hw)

/-- For every graph vector `p : SourceGraph` with `p.val.fst ∈ oddSector`, both `p` and its
radical-reduced projection `reducedSource p ∈ signedRadicalᗮ` are orthogonal to `(constantLift 1)`
and `oneL`. -/
theorem odd_reducedSource_primitive {p : SourceGraph} (hp : p.val.fst ∈ oddSector) :
    ⟪(reducedSource p).val.fst, (constantLift 1).val.fst⟫_ℝ = 0 ∧
      ⟪(reducedSource p).val.fst, oneL⟫_ℝ = 0 := by
  have h1 : ⟪p.val.fst, oneL⟫_ℝ = 0 := inner_oneL_eq_zero_of_mem_oddSector hp
  have hc1 : (constantLift 1).val.fst = oneL := by
    simpa only [one_smul] using constantLift_fst_eq_smul_oneL 1
  have hprim : ⟪(reducedSource p).val.fst, (constantLift 1).val.fst⟫_ℝ = 0 := by
    rw [reducedSource_primitive_pair, hc1, h1]
  have hprim_oneL : ⟪(reducedSource p).val.fst, oneL⟫_ℝ = 0 := by
    rwa [← hc1]
  exact ⟨hprim, hprim_oneL⟩

/-- **Unconditional Strict Upper Bound `< 1` on All Odd Eigenvectors
(`odd_eigenvector_eigenvalue_lt_one`):**
Every nonzero odd eigenvector `w` of `resolvent` (`resolvent w = μ • w`) has eigenvalue `μ < 1`. -/
theorem odd_eigenvector_eigenvalue_lt_one {μ : ℝ} {w : MassSpace} (hw : w ≠ 0)
    (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) :
    μ < 1 :=
  eigenvalue_lt_one_of_primitive hw (inner_oneL_eq_zero_of_odd hodd) heig

/-- **Open-Interval `(1/2, 1)` Odd Bound-State Characterization of `¬ RiemannHypothesis`
(`not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one`):**
`RiemannHypothesis` fails if and only if the arithmetic resolvent possesses a nonzero odd
eigenvector with eigenvalue strictly inside the open interval `Set.Ioo (1 / 2) 1`. -/
theorem not_riemannHypothesis_iff_exists_odd_eigenvector_mem_Ioo_half_one :
    ¬ RiemannHypothesis ↔
      ∃ (μ : ℝ) (w : MassSpace),
        μ ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧ w ≠ 0 ∧ reflectMass w = -w ∧ resolvent w = μ • w := by
  rw [not_riemannHypothesis_iff_exists_odd_bound_state]
  constructor
  · rintro ⟨μ, w, hμ, hw0, hodd, heig⟩
    exact ⟨μ, w, ⟨hμ, odd_eigenvector_eigenvalue_lt_one hw0 hodd heig⟩, hw0, hodd, heig⟩
  · rintro ⟨μ, w, ⟨hμ, _⟩, hw0, hodd, heig⟩
    exact ⟨μ, w, hμ, hw0, hodd, heig⟩

/-! ## §2. Radical-Free Quotient Criteria on `signedRadicalᗮ` -/

/-- **Radical-Reduced Odd Energy Criterion for `RiemannHypothesis`
(`riemannHypothesis_iff_odd_reducedSource_energy_nonneg`):**
`RiemannHypothesis` holds if and only if for every `p : SourceGraph` with `p.val.fst ∈ oddSector`,
its radical-orthogonal projection `reducedSource p ∈ signedRadicalᗮ` has non-negative
`sourceEnergy`. -/
theorem riemannHypothesis_iff_odd_reducedSource_energy_nonneg :
    RiemannHypothesis ↔
      ∀ p : SourceGraph, p.val.fst ∈ oddSector → 0 ≤ sourceEnergy (reducedSource p) := by
  simp_rw [sourceEnergy_reduced]
  exact ⟨sourceEnergy_nonneg_of_rh_odd, riemannHypothesis_of_odd_energy⟩

/-- **Primitive Radical-Orthogonal Sufficiency Bridge for `RiemannHypothesis`
(`riemannHypothesis_of_primitive_radicalOrthogonal_energy_nonneg`):**
If `0 ≤ sourceEnergy q` holds for every vector `q ∈ signedRadicalᗮ` that is orthogonal to the
ground state `oneL` (`⟪q.val.fst, oneL⟫_ℝ = 0`), then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_primitive_radicalOrthogonal_energy_nonneg
    (hpos : ∀ q : SourceGraph, q ∈ signedRadicalᗮ → ⟪q.val.fst, oneL⟫_ℝ = 0 → 0 ≤ sourceEnergy q) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_odd_reducedSource_energy_nonneg]
  intro p hp
  exact hpos (reducedSource p) (reducedSource_mem p) (odd_reducedSource_primitive hp).2

/-! ## §3. Zero-Silent Polar Positivity & Complete Odd Prime-Chain Coercivity Equivalence -/

/-- **Unconditional Non-Negativity of Cosine-Null Zero-Silent Vectors
(`sourceEnergy_nonneg_of_fullSpectralNullspace_of_polarCosine_eq_zero`):**
Every zero-silent vector `p ∈ fullSpectralNullspace` with vanishing polar cosine moment
(`polarCosine p = 0`) has `sourceEnergy p = 2 * polarSine p ^ 2 ≥ 0`. -/
theorem sourceEnergy_nonneg_of_fullSpectralNullspace_of_polarCosine_eq_zero
    {p : SourceGraph} (hp : p ∈ fullSpectralNullspace) (hcos : polarCosine p = 0) :
    sourceEnergy p = 2 * polarSine p ^ 2 ∧ 0 ≤ sourceEnergy p := by
  have heq : sourceEnergy p = 2 * polarSine p ^ 2 := by
    rw [full_nullspace_energy hp, hcos]
    ring
  exact ⟨heq, by rw [heq]; positivity⟩

/-- **Exact Decomposition of the Total Prime Jump Form into Same-Side and Complete Chain Variances
(`primeJump_tsum_eq_sameSide_add_chainIntegral`):**
For every `v ∈ C²_c(ℝ)`, the total prime Doob jump energy `∑' n, ∫ phiDoobPrimeJump v n` equals
`sameSide v + sameSide (fun x => v (-x)) + ∑' q : ChainIndex, chainIntegral v q`. -/
theorem primeJump_tsum_eq_sameSide_add_chainIntegral {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) =
      sameSide v + sameSide (fun x => v (-x)) +
        ∑' q : ChainIndex, chainIntegral v q := by
  have h1 := phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv hvc
  have h2 := doob_source_eq_chain_variances_sub_cosh hv hvc
  linarith

/-- **Complete Odd Prime-Chain Poincaré Equivalence for `RiemannHypothesis`
(`riemannHypothesis_iff_odd_primeChain_poincare`):**
`RiemannHypothesis` holds if and only if for every odd `v ∈ C²_c(ℝ)`, the sum of the archimedean
Doob jump energy, the same-side prime jump energies, and the complete bipartite prime-power chain
variance sum dominates the quadratic polar cosh mass:
`phiDoobCoshMass (fun x => v x ^ 2) ≤ phiDoobArchJumpEnergy v + sameSide v + sameSide (fun x => v (-x)) + ∑' q : ChainIndex, chainIntegral v q`. -/
theorem riemannHypothesis_iff_odd_primeChain_poincare :
    RiemannHypothesis ↔
      ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
        phiDoobCoshMass (fun x => v x ^ 2) ≤
          phiDoobArchJumpEnergy v + sameSide v + sameSide (fun x => v (-x)) +
            ∑' q : ChainIndex, chainIntegral v q := by
  rw [riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare]
  refine forall₄_congr fun v hv hvc _ => ?_
  rw [primeJump_tsum_eq_sameSide_add_chainIntegral hv hvc]
  ring_nf

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
