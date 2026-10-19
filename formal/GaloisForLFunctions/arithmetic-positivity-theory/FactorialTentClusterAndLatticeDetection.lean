import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTentOffLineDetection
import GaloisForLFunctions.SquareRootThreshold.WindowedBlindnessForClustersAndProfiles

/-!
# Constructive Period-Difference and Factorial-Tent Detection of Off-Line Clusters, Runs, and Lattices

This module connects the period-difference and smoothed factorial-tent explicit-formula machinery of
`ArithmeticPositivityTheory` (`PeriodDifferenceOffLineDetection`, `FactorialTentOffLineDetection`)
with the off-line cluster, contiguous run, uniform lattice, and windowed-blindness hierarchy of
`SquareRootThreshold` (`ClusterTotalVariationBlindness`, `OffLineRunEdgeVisibilityLaw`,
`WindowedBlindnessForClustersAndProfiles`, `ZeroLatticeDepthNyquistLaw`).

## Main results

1. **Universal vertical-lattice period-difference multiplier**
   (`Wsummand_shiftPair_verticalLatticePoint`):
   At every vertical lattice point `½ + δ + ik(2π/L)`, replacing a compactly supported real seed
   `liftC f` by its period difference `shiftPair f (-1) L` multiplies the Weil summand of any
   zero configuration `Z` by `-2(cosh(δL) - 1)`, independent of the ordinate index `k ∈ ℤ`.
   In particular, all on-line lattice points (`δ = 0`) are identically annihilated (`cosh 0 - 1 = 0`),
   while every off-line depth `δ ≠ 0` receives a strictly negative multiplier.

2. **Exact sign flip on the uniform off-line lattice**
   (`W_offLineLatticeConfig_shiftPair`, `W_offLineLatticeConfig_shiftPair_of_le_nyquist`,
   `factorialTentDetector_offLineLatticeConfig_eq`):
   On `offLineLatticeConfig hL hδ hδ'`, the period difference multiplies the entire Weil form of
   `liftC f` by `-2(cosh(δL) - 1)`. Below the Nyquist aperture `[-L/2, L/2]`, where `liftC f` is
   completely depth-blind (`W = 2L‖f‖²`), its period difference has exact negative Weil form
   `-4L(cosh(δL) - 1)‖f‖²`.

3. **Exact multi-zero cluster reduction and constructive negative margin**
   (`W_clusterConfig_shiftPair`, `clusterConfig_reflection_identity_of_online_zero`,
   `periodDifference_clusterConfig_negative_margin`, `periodDifference_clusterConfig_reflection_gap`):
   On any finite off-line cluster `clusterConfig hL S d hd0 hd1`, the period difference annihilates
   the infinite on-line background `k ∉ S` and reduces the Weil form, square mass, and reflection
   defect to finite sums over `k ∈ S`. When the nonnegative seed `f` has support radius `R`
   satisfying `|k(2π/L)| R ≤ 1/4` for all `k ∈ S`, all cluster pairs `k ∈ S` lie in a common
   coherent phase sector and add constructively without cancellation.

4. **Simultaneous full-Weil approximation and escape from sub-Nyquist / windowed cluster blindness**
   (`factorialTentDetector_clusterConfig_spec`, `factorialTentDetector_runConfig_negative_margin`,
   `cluster_blindness_vs_factorialTentDetector_visibility`):
   Above the explicit cluster scale `factorialTentClusterScale L K = ⌈32πK/L⌉₊`, a single native
   `C²_c(ℝ)` test function `factorialTentDetector n L q` simultaneously:
   * approximates the literal `Λ`-prime–Gamma–polar full Weil functional of the unsmoothed
     factorial-tent difference to within `1/(q + 1)`;
   * achieves constructive negative Weil form `≤ -∑_{k ∈ S} factorialTentDetectionMargin n L (d k)`
     and strict reflection-defect excess across any off-line cluster or contiguous run supported in
     `[-K, K]`, even in the small-total-variation regime `r · TV(d) · sinh(2δr) ≤ 1` (`4r ≤ L`)
     where every sub-Nyquist test and every height-windowed average `windowedW` of
     `factorialTentDetector n L q` itself is nonnegative.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology CompactlySupported ComplexConjugate Convolution
open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.WeilOneSided
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- At any vertical lattice frequency `k(2π/L) - iα`, the period exponential is `exp(αL)`,
independent of the lattice index `k ∈ ℤ`. -/
theorem lattice_pair_period_exponential {L : ℝ} (hL : 0 < L) (k : ℤ) (α : ℝ) :
    Complex.exp (I * ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ)) * (L : ℂ)) =
      (Real.exp (α * L) : ℂ) := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hI : I * I = -1 := Complex.I_mul_I
  have he :
      I * ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ)) * (L : ℂ) =
        ((α * L : ℝ) : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    push_cast
    calc
      I * ((k : ℂ) * (2 * ↑Real.pi / ↑L) - I * ↑α) * ↑L
          = (k : ℂ) * (2 * ↑Real.pi * I) * (↑L / ↑L) - (I * I) * (↑α * ↑L) := by ring
      _ = (k : ℂ) * (2 * ↑Real.pi * I) * 1 - (-1) * (↑α * ↑L) := by rw [div_self hL', hI]
      _ = ↑α * ↑L + (k : ℂ) * (2 * ↑Real.pi * I) := by ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ← Complex.ofReal_exp]

/-- Period-difference Fourier readout at an arbitrary vertical lattice point `k(2π/L) - iα`:
the period-difference multiplier `1 - exp(αL)` is independent of the lattice ordinate index `k`. -/
theorem periodDifference_lattice_pair_readout (f : C_c(ℝ, ℝ)) {L : ℝ} (hL : 0 < L)
    (k : ℤ) (α : ℝ) :
    paperFT (shiftPair f (-1) L) ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ)) =
      (1 - (Real.exp (α * L) : ℂ)) *
        paperFT (liftC f) ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ)) := by
  rw [paperFT_shiftPair (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport,
    lattice_pair_period_exponential hL k α]
  push_cast
  ring

/-- Universal period-difference multiplier law on vertical lattice points:
at every vertical lattice point `½ + δ + ik(2π/L)`, replacing `liftC f` by `shiftPair f (-1) L`
multiplies the Weil summand of any zero configuration `Z` by `-2(cosh(δL) - 1)`, independent of `k`. -/
theorem Wsummand_shiftPair_verticalLatticePoint (Z : ZeroConfig) (f : C_c(ℝ, ℝ))
    {L : ℝ} (hL : 0 < L) (δ : ℝ) (k : ℤ) :
    Z.Wsummand (shiftPair f (-1) L) (shiftPair f (-1) L) (verticalLatticePoint L δ k) =
      ((-2 * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) *
        Z.Wsummand (liftC f) (liftC f) (verticalLatticePoint L δ k) := by
  unfold ZeroConfig.Wsummand
  rw [gammaOf_verticalLatticePoint]
  have hconj :
      conj ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (δ : ℂ)) =
        (((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * ((-δ : ℝ) : ℂ) := by
    rw [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal,
      Complex.ofReal_neg]
    ring
  rw [hconj]
  rw [periodDifference_lattice_pair_readout f hL k δ,
    periodDifference_lattice_pair_readout f hL k (-δ)]
  have hcosh :
      (1 - Real.exp (δ * L)) * (1 - Real.exp (-δ * L)) = -2 * (Real.cosh (δ * L) - 1) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (δ * L) * Real.exp (-(δ * L)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 : -δ * L = -(δ * L) := by ring
    rw [h2]
    linarith
  have hcoshC :
      (1 - (Real.exp (δ * L) : ℂ)) * conj (1 - (Real.exp (-δ * L) : ℂ)) =
        ((-2 * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) := by
    rw [map_sub, map_one, Complex.conj_ofReal]
    have hsub : (1 - (Real.exp (δ * L) : ℂ)) * (1 - (Real.exp (-δ * L) : ℂ)) =
        (((1 - Real.exp (δ * L)) * (1 - Real.exp (-δ * L)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hsub, hcosh]
  rw [map_mul, ← hcoshC]
  ring

/-- On the uniform off-line lattice, a period difference multiplies the entire Weil form by
`-2(cosh(δL) - 1)`, for any compactly supported continuous seed `f`. -/
theorem W_offLineLatticeConfig_shiftPair {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (f : C_c(ℝ, ℝ)) :
    (offLineLatticeConfig hL hδ hδ').W (shiftPair f (-1) L) (shiftPair f (-1) L) =
      ((-2 * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) *
        (offLineLatticeConfig hL hδ hδ').W (liftC f) (liftC f) := by
  let Z := offLineLatticeConfig hL hδ hδ'
  have hneg : Real.cosh (-δ * L) = Real.cosh (δ * L) := by
    rw [neg_mul, Real.cosh_neg]
  have hterm (ρ : Z.carrier) :
      Z.Wsummand (shiftPair f (-1) L) (shiftPair f (-1) L) ρ =
        ((-2 * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) * Z.Wsummand (liftC f) (liftC f) ρ := by
    rcases ρ with ⟨_, ⟨k, rfl⟩ | ⟨k, rfl⟩⟩
    · exact Wsummand_shiftPair_verticalLatticePoint Z f hL δ k
    · change Z.Wsummand (shiftPair f (-1) L) (shiftPair f (-1) L) (verticalLatticePoint L (-δ) k) =
        ((-2 * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) *
          Z.Wsummand (liftC f) (liftC f) (verticalLatticePoint L (-δ) k)
      rw [Wsummand_shiftPair_verticalLatticePoint Z f hL (-δ) k, hneg]
  change (∑' ρ : Z.carrier, Z.Wsummand (shiftPair f (-1) L) (shiftPair f (-1) L) ρ) =
    ((-2 * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) * ∑' ρ : Z.carrier, Z.Wsummand (liftC f) (liftC f) ρ
  rw [tsum_congr hterm, tsum_mul_left]

/-- For a `C²` seed `f` supported below the Nyquist threshold `[-L/2, L/2]`, `liftC f` is blind to
the off-line lattice (`W = 2L‖f‖²`), whereas its period difference `shiftPair f (-1) L` has exact
negative Weil form `-4L(cosh(δL) - 1)‖f‖²`. -/
theorem W_offLineLatticeConfig_shiftPair_of_le_nyquist {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (liftC f))
    (hfs : tsupport (liftC f) ⊆ Icc (-(L / 2)) (L / 2)) :
    (offLineLatticeConfig hL hδ hδ').W (shiftPair f (-1) L) (shiftPair f (-1) L) =
      ((-4 * L * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) * ∫ t, liftC f t * conj (liftC f t) := by
  rw [W_offLineLatticeConfig_shiftPair hL hδ hδ' f,
    W_offLineLatticeConfig_of_le_nyquist hL hδ hδ' hf hf.continuous hfs hfs]
  push_cast
  ring

/-- On the uniform off-line lattice, the native factorial-tent detector multiplies the un-shifted
smoothed factorial-tent Weil form by `-2(cosh(δL) - 1)`. -/
theorem factorialTentDetector_offLineLatticeConfig_eq (n : ℕ) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (q : ℕ) :
    (offLineLatticeConfig hL hδ hδ').W
      (factorialTentDetector n L q) (factorialTentDetector n L q) =
      ((-2 * (Real.cosh (δ * L) - 1) : ℝ) : ℂ) *
        (offLineLatticeConfig hL hδ hδ').W
          (liftC (smoothCompactSource (factorialSourceRight n)
            (factorialTentDetectorSmoothingIndex n L q)))
          (liftC (smoothCompactSource (factorialSourceRight n)
            (factorialTentDetectorSmoothingIndex n L q))) := by
  rw [factorialTentDetector_eq_periodDifference, W_offLineLatticeConfig_shiftPair]

/-- A contiguous off-line run configuration is the special case of a cluster configuration with
constant depth `δ`. -/
theorem runConfig_eq_clusterConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (S : Finset ℤ) :
    runConfig hL hδ hδ' S =
      clusterConfig hL S (fun _ => δ) (fun _ _ => hδ) (fun _ _ => hδ') :=
  rfl

/-- Any channel `F` that vanishes on the on-line lattice outside `S` reduces on `clusterConfig`
to the finite sum over the off-line cluster pairs `k ∈ S`. -/
theorem clusterConfig_tsum_eq {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    (F : ℂ → E) (hF : ∀ k : ℤ, k ∉ S → F (verticalLatticePoint L 0 k) = 0) :
    (∑' ρ : (clusterConfig hL S d hd0 hd1).carrier, F ρ) =
      ∑ k ∈ S, (F (verticalLatticePoint L (d k) k) + F (verticalLatticePoint L (-d k) k)) := by
  have hA : HasSum (fun ρ : Set.range (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) =>
      F ρ) 0 := by
    have he : (fun ρ : Set.range (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) => F ρ) =
        fun _ => 0 := by
      funext ⟨_, k, rfl⟩
      exact hF k.1 k.2
    rw [he]
    exact hasSum_zero
  have hBp : HasSum (fun ρ : Set.range (fun k : S => verticalLatticePoint L (d k) k) =>
      F ρ) (∑ k : S, F (verticalLatticePoint L (d k) k)) := by
    have hinj : Function.Injective (fun k : S => verticalLatticePoint L (d k) k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_index_eq hL h)
    rw [hinj.hasSum_range_iff]
    exact hasSum_fintype _
  have hBm : HasSum (fun ρ : Set.range (fun k : S => verticalLatticePoint L (-d k) k) =>
      F ρ) (∑ k : S, F (verticalLatticePoint L (-d k) k)) := by
    have hinj : Function.Injective (fun k : S => verticalLatticePoint L (-d k) k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_index_eq hL h)
    rw [hinj.hasSum_range_iff]
    exact hasSum_fintype _
  have hd₁ : Disjoint (Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k)
      (Set.range fun k : S => verticalLatticePoint L (d k) k) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have hre := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at hre
    linarith [hd0 k' k'.2]
  have hd₂ : Disjoint ((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
      Set.range fun k : S => verticalLatticePoint L (d k) k)
      (Set.range fun k : S => verticalLatticePoint L (-d k) k) := by
    rw [Set.disjoint_left]
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) ⟨k', hk'⟩
    · have hre := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at hre
      linarith [hd0 k' k'.2]
    · have hre := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at hre
      linarith [hd0 k' k'.2, hd0 k k.2]
  have hall := HasSum.add_disjoint (f := F) hd₂
    (HasSum.add_disjoint (f := F) hd₁ hA hBp) hBm
  have heq :
      (∑' b : ↥(((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
          Set.range fun k : S => verticalLatticePoint L (d k) k) ∪
        Set.range fun k : S => verticalLatticePoint L (-d k) k), F b) =
      0 + (∑ k : S, F (verticalLatticePoint L (d k) k)) +
        ∑ k : S, F (verticalLatticePoint L (-d k) k) := by
    simpa only [Function.comp_def] using hall.tsum_eq
  change (∑' b : ↥(((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
      Set.range fun k : S => verticalLatticePoint L (d k) k) ∪
    Set.range fun k : S => verticalLatticePoint L (-d k) k), F b) = _
  rw [heq, zero_add, Finset.sum_coe_sort S (fun k => F (verticalLatticePoint L (d k) k)),
    Finset.sum_coe_sort S (fun k => F (verticalLatticePoint L (-d k) k)),
    ← Finset.sum_add_distrib]

/-- Exact multi-zero cluster period-difference formula: the infinite on-line background lattice
`k ∉ S` is identically annihilated, and each off-line cluster pair `k ∈ S` is weighted by
`-2(cosh(d_k L) - 1)`. -/
theorem W_clusterConfig_shiftPair {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) (f : C_c(ℝ, ℝ)) :
    (clusterConfig hL S d hd0 hd1).W (shiftPair f (-1) L) (shiftPair f (-1) L) =
      ∑ k ∈ S, ((-2 * (Real.cosh (d k * L) - 1) : ℝ) : ℂ) *
        ((clusterConfig hL S d hd0 hd1).Wsummand (liftC f) (liftC f)
            (verticalLatticePoint L (d k) k) +
          (clusterConfig hL S d hd0 hd1).Wsummand (liftC f) (liftC f)
            (verticalLatticePoint L (-d k) k)) := by
  let Z := clusterConfig hL S d hd0 hd1
  have honline (k : ℤ) (_ : k ∉ S) :
      Z.Wsummand (shiftPair f (-1) L) (shiftPair f (-1) L) (verticalLatticePoint L 0 k) = 0 := by
    rw [Wsummand_shiftPair_verticalLatticePoint Z f hL 0 k]
    simp
  change (∑' ρ : Z.carrier, Z.Wsummand (shiftPair f (-1) L) (shiftPair f (-1) L) ρ) = _
  rw [clusterConfig_tsum_eq hL S d hd0 hd1 _ honline]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hneg : Real.cosh (-d k * L) = Real.cosh (d k * L) := by
    rw [neg_mul, Real.cosh_neg]
  rw [Wsummand_shiftPair_verticalLatticePoint Z f hL (d k) k,
    Wsummand_shiftPair_verticalLatticePoint Z f hL (-d k) k, hneg, ← mul_add]

/-- When `paperFT g` vanishes on the on-line lattice, the cluster Weil form reduces to the finite
sum of off-line pair readouts over `k ∈ S`. -/
theorem clusterConfig_W_of_online_zero {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) (g : ℝ → ℂ)
    (hg : ∀ k : ℤ, paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ)) = 0) :
    (clusterConfig hL S d hd0 hd1).W g g =
      ∑ k ∈ S,
        (paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (d k : ℂ)) *
            conj (paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (d k : ℂ))) +
          paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (d k : ℂ)) *
            conj (paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (d k : ℂ)))) := by
  let Z := clusterConfig hL S d hd0 hd1
  have hm (k : ℤ) (α : ℝ) (hα : α ≠ 0) : Z.mult (verticalLatticePoint L α k) = 1 := by
    change (if (verticalLatticePoint L α k).re = 1 / 2 then 2 else 1) = 1
    rw [if_neg]
    simp only [verticalLatticePoint]
    intro he
    apply hα
    linarith
  have hconj₁ (k : ℤ) (α : ℝ) :
      conj ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ)) =
        (((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (α : ℂ) := by
    rw [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hconj₂ (k : ℤ) (α : ℝ) :
      conj ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (α : ℂ)) =
        (((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ) := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have honline (k : ℤ) (_ : k ∉ S) : Z.Wsummand g g (verticalLatticePoint L 0 k) = 0 := by
    unfold ZeroConfig.Wsummand
    rw [gammaOf_verticalLatticePoint]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero, hg k, zero_mul]
  change (∑' ρ : Z.carrier, Z.Wsummand g g ρ) = _
  rw [clusterConfig_tsum_eq hL S d hd0 hd1 (Z.Wsummand g g) honline]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : d k ≠ 0 := (hd0 k hk).ne'
  unfold ZeroConfig.Wsummand
  rw [hm k (d k) hk0, hm k (-d k) (neg_ne_zero.mpr hk0),
    gammaOf_verticalLatticePoint, gammaOf_verticalLatticePoint]
  simp only [Nat.cast_one, one_mul, Complex.ofReal_neg, mul_neg, sub_neg_eq_add, hconj₁, hconj₂]

/-- When `paperFT g` vanishes on the on-line lattice, the square mass and reflection defect of
`clusterConfig` reduce to finite sums over `k ∈ S`. -/
theorem clusterConfig_diagonal_defect_of_online_zero {L : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    (g : ℝ → ℂ)
    (hg : ∀ k : ℤ, paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ)) = 0) :
    configurationSquareMass (clusterConfig hL S d hd0 hd1) g =
      ∑ k ∈ S,
        (‖paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (d k : ℂ))‖ ^ 2 +
          ‖paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (d k : ℂ))‖ ^ 2) ∧
    configurationReflectionDefect (clusterConfig hL S d hd0 hd1) g =
      ∑ k ∈ S,
        ‖paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (d k : ℂ)) -
          paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (d k : ℂ))‖ ^ 2 := by
  let Z := clusterConfig hL S d hd0 hd1
  have hm (k : ℤ) (α : ℝ) (hα : α ≠ 0) : Z.mult (verticalLatticePoint L α k) = 1 := by
    change (if (verticalLatticePoint L α k).re = 1 / 2 then 2 else 1) = 1
    rw [if_neg]
    simp only [verticalLatticePoint]
    intro he
    apply hα
    linarith
  have hconj₁ (k : ℤ) (α : ℝ) :
      conj ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ)) =
        (((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (α : ℂ) := by
    rw [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hconj₂ (k : ℤ) (α : ℝ) :
      conj ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (α : ℂ)) =
        (((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (α : ℂ) := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hs (k : ℤ) (_ : k ∉ S) : (Z.mult (verticalLatticePoint L 0 k) : ℝ) *
      ‖paperFT g (gammaOf (verticalLatticePoint L 0 k))‖ ^ 2 = 0 := by
    rw [gammaOf_verticalLatticePoint]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero, hg k, norm_zero, pow_two, mul_zero]
  have hd (k : ℤ) (_ : k ∉ S) : (Z.mult (verticalLatticePoint L 0 k) : ℝ) / 2 *
      ‖paperFT g (gammaOf (verticalLatticePoint L 0 k)) -
        paperFT g (conj (gammaOf (verticalLatticePoint L 0 k)))‖ ^ 2 = 0 := by
    rw [gammaOf_verticalLatticePoint]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero, Complex.conj_ofReal, hg k,
      sub_self, norm_zero, pow_two, mul_zero]
  constructor
  · change (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * ‖paperFT g (gammaOf ρ)‖ ^ 2) = _
    rw [clusterConfig_tsum_eq hL S d hd0 hd1
      (fun ρ => (Z.mult ρ : ℝ) * ‖paperFT g (gammaOf ρ)‖ ^ 2) hs]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : d k ≠ 0 := (hd0 k hk).ne'
    rw [hm k (d k) hk0, hm k (-d k) (neg_ne_zero.mpr hk0),
      gammaOf_verticalLatticePoint, gammaOf_verticalLatticePoint]
    simp only [Nat.cast_one, one_mul, Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
  · change (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / 2 *
      ‖paperFT g (gammaOf ρ) - paperFT g (conj (gammaOf ρ))‖ ^ 2) = _
    rw [clusterConfig_tsum_eq hL S d hd0 hd1
      (fun ρ => (Z.mult ρ : ℝ) / 2 * ‖paperFT g (gammaOf ρ) - paperFT g (conj (gammaOf ρ))‖ ^ 2) hd]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : d k ≠ 0 := (hd0 k hk).ne'
    rw [hm k (d k) hk0, hm k (-d k) (neg_ne_zero.mpr hk0),
      gammaOf_verticalLatticePoint, gammaOf_verticalLatticePoint]
    simp only [Nat.cast_one, Complex.ofReal_neg, mul_neg, sub_neg_eq_add, hconj₁, hconj₂]
    rw [norm_sub_rev
      (paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (d k : ℂ)))
      (paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (d k : ℂ)))]
    ring

/-- Exact reflection identity on `clusterConfig` for any test function `g` annihilating the
on-line lattice. -/
theorem clusterConfig_reflection_identity_of_online_zero {L : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    (g : ℝ → ℂ)
    (hg : ∀ k : ℤ, paperFT g ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ)) = 0) :
    configurationSquareMass (clusterConfig hL S d hd0 hd1) g -
      ((clusterConfig hL S d hd0 hd1).W g g).re =
        configurationReflectionDefect (clusterConfig hL S d hd0 hd1) g := by
  obtain ⟨hs, hd⟩ := clusterConfig_diagonal_defect_of_online_zero hL S d hd0 hd1 g hg
  rw [hs, hd, clusterConfig_W_of_online_zero hL S d hd0 hd1 g hg, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  ring

private theorem re_mul_conj_lower_of_quarter' {U V : ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : ‖U - (A : ℂ)‖ ≤ A / 4) (hV : ‖V - (B : ℂ)‖ ≤ B / 4) :
    A * B / 2 ≤ (U * conj V).re := by
  have hUr : |U.re - A| ≤ A / 4 := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.abs_re_le_norm (U - (A : ℂ))).trans hU
  have hVr : |V.re - B| ≤ B / 4 := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.abs_re_le_norm (V - (B : ℂ))).trans hV
  have hUi : |U.im| ≤ A / 4 := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (U - (A : ℂ))).trans hU
  have hVi : |V.im| ≤ B / 4 := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      (Complex.abs_im_le_norm (V - (B : ℂ))).trans hV
  have hUr' : 3 * A / 4 ≤ U.re := by linarith [(abs_le.mp hUr).1]
  have hVr' : 3 * B / 4 ≤ V.re := by linarith [(abs_le.mp hVr).1]
  have hr : (3 * A / 4) * (3 * B / 4) ≤ U.re * V.re :=
    mul_le_mul hUr' hVr' (by positivity) (by linarith)
  have hi : |U.im * V.im| ≤ (A / 4) * (B / 4) := by
    rw [abs_mul]
    exact mul_le_mul hUi hVi (abs_nonneg _) (by positivity)
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
  nlinarith [(abs_le.mp hi).1]

/-- At any lattice index `k ∈ ℤ` whose ordinate `γ_k = k(2π/L)` satisfies `|γ_k| R ≤ 1/4`,
a thin nonnegative seed `f` produces a strictly negative period-difference pair contribution. -/
theorem periodDifference_lattice_pair_negative_margin (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0)
    (hmass : 1 ≤ ∫ x, f x) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (k : ℤ)
    (hthin : |(k : ℝ) * (2 * Real.pi / L)| * R ≤ 1 / 4) :
    (paperFT (shiftPair f (-1) L) ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (δ : ℂ)) *
        conj (paperFT (shiftPair f (-1) L)
          ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (δ : ℂ))) +
      paperFT (shiftPair f (-1) L) ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) + I * (δ : ℂ)) *
        conj (paperFT (shiftPair f (-1) L)
          ((((k : ℝ) * (2 * Real.pi / L) : ℝ) : ℂ) - I * (δ : ℂ)))).re ≤
      -((Real.exp (δ * L) - 1) * (1 - Real.exp (-(δ * L))) * Real.exp (-2 * δ * R)) := by
  let γ := (k : ℝ) * (2 * Real.pi / L)
  let U := paperFT (liftC f) ((γ : ℂ) - I * (δ : ℂ))
  let V := paperFT (liftC f) ((γ : ℂ) + I * (δ : ℂ))
  let A := realTiltMass f δ
  let B := realTiltMass f (-δ)
  have hA := compact_nonnegative_tilt_lower f hf hR hmass δ
  have hB := compact_nonnegative_tilt_lower f hf hR hmass (-δ)
  rw [abs_of_pos hδ] at hA
  rw [abs_neg, abs_of_pos hδ] at hB
  have hA0 : 0 ≤ A := (Real.exp_pos _).le.trans hA
  have hB0 : 0 ≤ B := (Real.exp_pos _).le.trans hB
  have hU : ‖U - (A : ℂ)‖ ≤ A / 4 := by
    have h := compact_nonnegative_readout_sector f hf hR δ γ
    exact h.trans ((mul_le_mul_of_nonneg_right hthin hA0).trans_eq (by ring))
  have hV : ‖V - (B : ℂ)‖ ≤ B / 4 := by
    have h := compact_nonnegative_readout_sector f hf hR (-δ) γ
    simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add] at h
    exact h.trans ((mul_le_mul_of_nonneg_right hthin hB0).trans_eq (by ring))
  have hUV := re_mul_conj_lower_of_quarter' hA0 hB0 hU hV
  have hAB : Real.exp (-2 * δ * R) ≤ A * B := by
    have h := mul_le_mul hA hB (Real.exp_pos _).le hA0
    rw [← Real.exp_add, show -δ * R + -δ * R = -2 * δ * R by ring] at h
    exact h
  have hplus : 0 < Real.exp (δ * L) - 1 := by
    have h := Real.one_lt_exp_iff.mpr (mul_pos hδ hL)
    linarith
  have hminus : 0 < 1 - Real.exp (-(δ * L)) := by
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hδ hL))
    linarith
  have hread₁ := periodDifference_lattice_pair_readout f hL k δ
  have hread₂ := periodDifference_lattice_pair_readout f hL k (-δ)
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add, neg_mul] at hread₂
  rw [hread₁, hread₂]
  have he : (((1 - (Real.exp (δ * L) : ℂ)) * U) * conj ((1 - (Real.exp (-(δ * L)) : ℂ)) * V) +
      ((1 - (Real.exp (-(δ * L)) : ℂ)) * V) * conj ((1 - (Real.exp (δ * L) : ℂ)) * U)).re =
      -2 * ((Real.exp (δ * L) - 1) * (1 - Real.exp (-(δ * L)))) * (U * conj V).re := by
    simp only [map_mul, map_sub, map_one, Complex.conj_ofReal]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im]
    ring
  change _ ≤ _
  rw [he]
  have hc : 0 ≤ (Real.exp (δ * L) - 1) * (1 - Real.exp (-(δ * L))) := mul_nonneg hplus.le hminus.le
  have h1 := mul_le_mul_of_nonneg_left hUV hc
  have h2 := mul_le_mul_of_nonneg_left hAB hc
  nlinarith

/-- Constructive negative margin for an arbitrary off-line cluster `clusterConfig hL S d hd0 hd1`
under a period-difference test: all cluster pairs `k ∈ S` add constructively without phase
cancellation once the seed radius `R` satisfies `|k(2π/L)| R ≤ 1/4` on `S`. -/
theorem periodDifference_clusterConfig_negative_margin (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0)
    (hmass : 1 ≤ ∫ x, f x) {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    (hthin : ∀ k ∈ S, |(k : ℝ) * (2 * Real.pi / L)| * R ≤ 1 / 4) :
    ((clusterConfig hL S d hd0 hd1).W (shiftPair f (-1) L) (shiftPair f (-1) L)).re ≤
      -∑ k ∈ S, (Real.exp (d k * L) - 1) * (1 - Real.exp (-(d k * L))) *
        Real.exp (-2 * d k * R) := by
  rw [clusterConfig_W_of_online_zero hL S d hd0 hd1 _ (periodDifference_online_readout_zero f hL),
    Complex.re_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun k hk =>
    periodDifference_lattice_pair_negative_margin f hf hR hmass hL (hd0 k hk) k (hthin k hk)

/-- Constructive reflection-defect gap for an arbitrary off-line cluster under a period-difference
test. -/
theorem periodDifference_clusterConfig_reflection_gap (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0)
    (hmass : 1 ≤ ∫ x, f x) {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    (hthin : ∀ k ∈ S, |(k : ℝ) * (2 * Real.pi / L)| * R ≤ 1 / 4) :
    (∑ k ∈ S, (Real.exp (d k * L) - 1) * (1 - Real.exp (-(d k * L))) *
        Real.exp (-2 * d k * R)) ≤
      configurationReflectionDefect (clusterConfig hL S d hd0 hd1) (shiftPair f (-1) L) -
        configurationSquareMass (clusterConfig hL S d hd0 hd1) (shiftPair f (-1) L) := by
  have hW := periodDifference_clusterConfig_negative_margin f hf hR hmass hL S d hd0 hd1 hthin
  have he := clusterConfig_reflection_identity_of_online_zero hL S d hd0 hd1
    (shiftPair f (-1) L) (periodDifference_online_readout_zero f hL)
  linarith

/-- Arithmetic scale chosen from the lattice period `L` and cluster index bound `K`:
every lattice index `|k| ≤ K` lies inside the coherent phase sector of `factorialTentDetector n L q`
once `n ≥ factorialTentClusterScale L K`. -/
def factorialTentClusterScale (L : ℝ) (K : ℕ) : ℕ := ⌈32 * Real.pi * (K : ℝ) / L⌉₊

theorem factorialTentClusterScale_le_thin {L : ℝ} (hL : 0 < L) {K n : ℕ}
    (hn : factorialTentClusterScale L K ≤ n) {k : ℤ} (hk : |k| ≤ (K : ℤ)) :
    |(k : ℝ) * (2 * Real.pi / L)| * (3 / ((n : ℝ) + 1)) ≤ 1 / 4 := by
  have hkR : |(k : ℝ)| ≤ (K : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast hk
  have hn' : (factorialTentClusterScale L K : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hpos : 0 < 2 * Real.pi / L := by positivity
  have h1 : |(k : ℝ) * (2 * Real.pi / L)| * (3 / ((n : ℝ) + 1)) ≤
      (K : ℝ) * (2 * Real.pi / L) * (3 / ((factorialTentClusterScale L K : ℝ) + 1)) := by
    rw [abs_mul, abs_of_pos hpos]
    have hr : 3 / ((n : ℝ) + 1) ≤ 3 / ((factorialTentClusterScale L K : ℝ) + 1) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith)
    have hK : |(k : ℝ)| * (2 * Real.pi / L) ≤ (K : ℝ) * (2 * Real.pi / L) :=
      mul_le_mul_of_nonneg_right hkR hpos.le
    exact mul_le_mul hK hr (by positivity) (by positivity)
  refine h1.trans ?_
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have hposX : 0 ≤ Real.pi * (K : ℝ) / L := by positivity
  have hlhs : (K : ℝ) * (2 * Real.pi / L) * 3 = 6 * (Real.pi * (K : ℝ) / L) := by ring
  have hceil : 32 * (Real.pi * (K : ℝ) / L) ≤ (factorialTentClusterScale L K : ℝ) := by
    calc 32 * (Real.pi * (K : ℝ) / L) = 32 * Real.pi * (K : ℝ) / L := by ring
      _ ≤ (factorialTentClusterScale L K : ℝ) := Nat.le_ceil (32 * Real.pi * (K : ℝ) / L)
  linarith

/-- The native smoothed factorial-tent period-difference detector achieves a strictly negative
Weil form on any off-line cluster supported in `[-K, K]`, summing the single-pair margins over all
cluster indices `k ∈ S`. -/
theorem factorialTentDetector_clusterConfig_negative_margin (n : ℕ) {L : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    {K : ℕ} (hS : ∀ k ∈ S, |k| ≤ (K : ℤ)) (hn : factorialTentClusterScale L K ≤ n) (q : ℕ) :
    ((clusterConfig hL S d hd0 hd1).W
      (factorialTentDetector n L q) (factorialTentDetector n L q)).re ≤
        -∑ k ∈ S, factorialTentDetectionMargin n L (d k) := by
  let idx := factorialTentDetectorSmoothingIndex n L q
  have hnk : n ≤ idx := le_max_left _ _
  have hmass : 1 ≤ ∫ x, smoothCompactSource (factorialSourceRight n) idx x := by
    rw [smoothCompactSource_integral]
    exact factorialSourceRight_integral_lower n
  rw [factorialTentDetector_eq_periodDifference]
  have h := periodDifference_clusterConfig_negative_margin
    (smoothCompactSource (factorialSourceRight n) idx)
    (smoothCompactSource_nonneg _ (factorialSourceRight_nonneg n) idx)
    (fun x hx => smoothedFactorialTent_thin n idx hnk hx) hmass hL S d hd0 hd1
    (fun k hk => factorialTentClusterScale_le_thin hL hn (hS k hk))
  refine h.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp [factorialTentDetectionMargin]
  rw [show -2 * d k * (3 / ((n : ℝ) + 1)) = -6 * d k / ((n : ℝ) + 1) by ring]

/-- The native smoothed factorial-tent detector forces a strict reflection-defect excess over the
square mass across the entire off-line cluster `S`. -/
theorem factorialTentDetector_clusterConfig_reflection_gap (n : ℕ) {L : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (d : ℤ → ℝ) (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    {K : ℕ} (hS : ∀ k ∈ S, |k| ≤ (K : ℤ)) (hn : factorialTentClusterScale L K ≤ n) (q : ℕ) :
    (∑ k ∈ S, factorialTentDetectionMargin n L (d k)) ≤
      configurationReflectionDefect (clusterConfig hL S d hd0 hd1) (factorialTentDetector n L q) -
        configurationSquareMass (clusterConfig hL S d hd0 hd1) (factorialTentDetector n L q) := by
  have hW := factorialTentDetector_clusterConfig_negative_margin n hL S d hd0 hd1 hS hn q
  have he := clusterConfig_reflection_identity_of_online_zero hL S d hd0 hd1
    (factorialTentDetector n L q) (factorialTentDetector_online_zero n hL q)
  linarith

/-- On any contiguous or finite off-line run `runConfig hL hδ hδ' S` supported in `[-K, K]`,
the native detector achieves negative margin proportional to the run cardinality `S.card`. -/
theorem factorialTentDetector_runConfig_negative_margin (n : ℕ) {L δ : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (S : Finset ℤ) {K : ℕ} (hS : ∀ k ∈ S, |k| ≤ (K : ℤ))
    (hn : factorialTentClusterScale L K ≤ n) (q : ℕ) :
    ((runConfig hL hδ hδ' S).W
      (factorialTentDetector n L q) (factorialTentDetector n L q)).re ≤
        -(S.card : ℝ) * factorialTentDetectionMargin n L δ := by
  rw [runConfig_eq_clusterConfig]
  refine (factorialTentDetector_clusterConfig_negative_margin n hL S (fun _ => δ)
    (fun _ _ => hδ) (fun _ _ => hδ') hS hn q).trans_eq ?_
  simp only [Finset.sum_const, nsmul_eq_mul, neg_mul]

/-- Joint specification of `factorialTentDetector n L q` on arbitrary off-line clusters:
a single `C²_c(ℝ)` native detector simultaneously approximates the literal `Λ`-prime–Gamma–polar
full Weil functional to within `1/(q+1)` and detects every off-line cluster `clusterConfig`
supported in `[-K, K]` with strictly negative Weil form and strict reflection-defect excess. -/
theorem factorialTentDetector_clusterConfig_spec (n : ℕ) {L : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (hS_nonempty : S.Nonempty) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2)
    {K : ℕ} (hS : ∀ k ∈ S, |k| ≤ (K : ℤ)) (hn : factorialTentClusterScale L K ≤ n) (q : ℕ) :
    ContDiff ℝ 2 (factorialTentDetector n L q) ∧
    HasCompactSupport (factorialTentDetector n L q) ∧
    |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
        (EF.weilTest (factorialTentDetector n L q) (factorialTentDetector n L q))).re -
      compactFullWeilEnergy (factorialTentPeriodDifference n L)| ≤ 1 / ((q : ℝ) + 1) ∧
    0 < ∑ k ∈ S, factorialTentDetectionMargin n L (d k) ∧
    ((clusterConfig hL S d hd0 hd1).W
      (factorialTentDetector n L q) (factorialTentDetector n L q)).re ≤
        -∑ k ∈ S, factorialTentDetectionMargin n L (d k) ∧
    (∑ k ∈ S, factorialTentDetectionMargin n L (d k)) ≤
      configurationReflectionDefect (clusterConfig hL S d hd0 hd1) (factorialTentDetector n L q) -
        configurationSquareMass (clusterConfig hL S d hd0 hd1) (factorialTentDetector n L q) :=
  ⟨(factorialTentDetector_admissible n L q).1,
    (factorialTentDetector_admissible n L q).2,
    factorialTentDetector_literal_fullWeil_approximation n L q,
    Finset.sum_pos (fun k hk => factorialTentDetectionMargin_pos n hL (hd0 k hk)) hS_nonempty,
    factorialTentDetector_clusterConfig_negative_margin n hL S d hd0 hd1 hS hn q,
    factorialTentDetector_clusterConfig_reflection_gap n hL S d hd0 hd1 hS hn q⟩

/-- **Sub-Nyquist & Windowed Blindness vs. Native Period-Difference Visibility:**
For any small-total-variation off-line cluster `clusterConfig hL S d hd0 hd1` (`4r ≤ L` and
`r · TV(d) · sinh(2δr) ≤ 1`), the cluster is:
1. Weil-nonnegative on every `C²` test supported in `[-r, r]` (`re_W_clusterConfig_nonneg`);
2. Windowed-Weil-nonnegative when `factorialTentDetector n L q` itself is height-averaged against
   any `C²` window `η` supported in `[-r, r]` (`re_windowedW_clusterConfig_nonneg`);
3. Yet strictly Weil-negative on the un-averaged `factorialTentDetector n L q` with margin
   `-∑_{k ∈ S} factorialTentDetectionMargin n L (d k) < 0`, while approximating the full arithmetic
   Weil functional to within `1/(q+1)`. -/
theorem cluster_blindness_vs_factorialTentDetector_visibility (n : ℕ) {L δ r : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (hS_nonempty : S.Nonempty) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) (hdδ : ∀ k ∈ S, d k ≤ δ) (hδ : 0 ≤ δ)
    (hr : 0 ≤ r) (hrL : 4 * r ≤ L) (hTV : r * depthVariation S d * Real.sinh (2 * δ * r) ≤ 1)
    {K : ℕ} (hS : ∀ k ∈ S, |k| ≤ (K : ℤ)) (hn : factorialTentClusterScale L K ≤ n) (q : ℕ) :
    (∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-r) r →
      0 ≤ ((clusterConfig hL S d hd0 hd1).W g g).re) ∧
    (∀ η : ℝ → ℂ, ContDiff ℝ 2 η → tsupport η ⊆ Icc (-r) r →
      0 ≤ (windowedW (clusterConfig hL S d hd0 hd1) (factorialTentDetector n L q) η).re) ∧
    0 < ∑ k ∈ S, factorialTentDetectionMargin n L (d k) ∧
    ((clusterConfig hL S d hd0 hd1).W
      (factorialTentDetector n L q) (factorialTentDetector n L q)).re ≤
        -∑ k ∈ S, factorialTentDetectionMargin n L (d k) ∧
    |(weilFullFunctional (fun m => (ArithmeticFunction.vonMangoldt m : ℝ))
        (EF.weilTest (factorialTentDetector n L q) (factorialTentDetector n L q))).re -
      compactFullWeilEnergy (factorialTentPeriodDifference n L)| ≤ 1 / ((q : ℝ) + 1) := by
  have hadm := factorialTentDetector_admissible n L q
  refine ⟨fun g hg hgs => re_W_clusterConfig_nonneg hL S d hd0 hd1 hdδ hδ hr hrL hTV hg hgs,
    fun η hη hηs => re_windowedW_clusterConfig_nonneg hL S d hd0 hd1 hdδ hδ hr hrL hTV
      hadm.1 hadm.2 hη hηs,
    Finset.sum_pos (fun k hk => factorialTentDetectionMargin_pos n hL (hd0 k hk)) hS_nonempty,
    factorialTentDetector_clusterConfig_negative_margin n hL S d hd0 hd1 hS hn q,
    factorialTentDetector_literal_fullWeil_approximation n L q⟩

end GaloisForLFunctions.ArithmeticPositivityTheory
