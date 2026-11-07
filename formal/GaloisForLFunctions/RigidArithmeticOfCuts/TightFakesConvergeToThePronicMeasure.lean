import GaloisForLFunctions.RigidArithmeticOfCuts.TheFakePrimeMeasureIsUnique
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Tight fakes converge to the pronic measure

Which fake prime measure of level `K` is closest to the true one? Two facts separate what is meaningful at finite level.

* Translating an atom by `lcm(1, …, K)` keeps every moment of level `K`, so a fake of level `K` can have no mass in any
  given window (`isFakePrimeMeasure_translate`), and no lower radius exists without a condition at infinity.
* The upper radius is the rate: the window mass is at most `A(K) (1 − 1/B)`, by weak duality.

With a condition at infinity the picture closes. **A sequence of fakes of levels `K_n → ∞`, dominated by one summable
sequence, converges pointwise to the pronic measure.** Every limit point is a fake of every level, and there is exactly
one such measure. So the extremal fake of level `K` has no independent limit: tight fakes collapse to
`1/(r (r + 1))`, which is `dy/y²` read on integer cells, and not a new Beurling system.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- A family of measures dominated by one summable sequence. -/
def IsTightFamily (U : ℕ → ℕ → ℝ) : Prop :=
  ∃ b : ℕ → ℝ, Summable b ∧ ∀ n j, U n j ≤ b j

variable {U : ℕ → ℕ → ℝ}

/-- **A pointwise limit of tight fakes is a fake of every level.** -/
theorem isFakePrimeMeasure_of_tendsto {K : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    (hU : ∀ n, IsFakePrimeMeasure (K n) (U n)) (ht : IsTightFamily U) {u : ℕ → ℝ}
    (hlim : ∀ j, Tendsto (fun n => U n j) atTop (𝓝 (u j))) (L : ℕ) : IsFakePrimeMeasure L u := by
  obtain ⟨b, hb, hle⟩ := ht
  refine ⟨fun j => ge_of_tendsto' (hlim j) fun n => (hU n).nonneg j, fun k hk => ?_⟩
  obtain ⟨hk1, hkL⟩ := mem_Icc.mp hk
  have hevK : ∀ᶠ n in atTop, k ≤ K n := hK.eventually_ge_atTop k
  have hbound : Summable fun j => b j * (k : ℝ) := hb.mul_right _
  have hterm : ∀ n j, ‖U n j * (((j + 1) % k : ℕ) : ℝ)‖ ≤ b j * (k : ℝ) := by
    intro n j
    have hnn := (hU n).nonneg j
    have hmod : (((j + 1) % k : ℕ) : ℝ) ≤ k := by
      exact_mod_cast (Nat.mod_lt _ (by omega : 0 < k)).le
    rw [Real.norm_of_nonneg (mul_nonneg hnn (Nat.cast_nonneg _))]
    have hb0 : 0 ≤ b j := hnn.trans (hle n j)
    exact mul_le_mul (hle n j) hmod (Nat.cast_nonneg _) hb0
  have hlimsum : Tendsto (fun n => ∑' j, U n j * (((j + 1) % k : ℕ) : ℝ)) atTop
      (𝓝 (∑' j, u j * (((j + 1) % k : ℕ) : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun j => (hlim j).mul_const _)
      (Eventually.of_forall hterm)
  have hval : ∀ᶠ n in atTop, ∑' j, U n j * (((j + 1) % k : ℕ) : ℝ) = Real.log k := by
    filter_upwards [hevK] with n hn
    exact ((hU n).moment k (mem_Icc.mpr ⟨hk1, hn⟩)).tsum_eq
  have hlog : ∑' j, u j * (((j + 1) % k : ℕ) : ℝ) = Real.log k :=
    tendsto_nhds_unique hlimsum (tendsto_const_nhds.congr' (hval.mono fun _ h => h.symm))
  have hsu : Summable fun j => u j * (((j + 1) % k : ℕ) : ℝ) := by
    refine Summable.of_norm_bounded hbound fun j => ?_
    exact le_of_tendsto (((hlim j).mul_const _).norm) (Eventually.of_forall fun n => hterm n j)
  rw [← hlog]
  exact hsu.hasSum

/-- **Tight fakes converge to the pronic measure.** A sequence of fake prime measures of levels tending to infinity,
dominated by one summable sequence, converges pointwise to `1/(r (r + 1))`. -/
theorem tendsto_pronic_of_tight {K : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    (hU : ∀ n, IsFakePrimeMeasure (K n) (U n)) (ht : IsTightFamily U) (j : ℕ) :
    Tendsto (fun n => U n j) atTop (𝓝 (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) := by
  obtain ⟨b, hb, hle⟩ := ht
  have hbnn : ∀ i, 0 ≤ b i := fun i => ((hU 0).nonneg i).trans (hle 0 i)
  -- Compactness of the product of intervals.
  have hcompact : IsCompact (Set.pi Set.univ fun i : ℕ => Set.Icc (0 : ℝ) (b i)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, U n ∈ Set.pi Set.univ fun i : ℕ => Set.Icc (0 : ℝ) (b i) :=
    fun n i _ => ⟨(hU n).nonneg i, hle n i⟩
  -- Every subsequence has a further subsequence converging to the pronic measure.
  rw [tendsto_iff_seq_tendsto]
  intro φ hφ
  refine tendsto_of_subseq_tendsto fun ψ hψ => ?_
  obtain ⟨u, _, χ, hχ, hlim⟩ := hcompact.tendsto_subseq fun n => hmem (φ (ψ n))
  refine ⟨χ, ?_⟩
  have hcoord : ∀ i, Tendsto (fun n => U (φ (ψ (χ n))) i) atTop (𝓝 (u i)) :=
    fun i => (tendsto_pi_nhds.mp hlim) i
  have htend : Tendsto (fun n => φ (ψ (χ n))) atTop atTop :=
    hφ.comp (hψ.comp hχ.tendsto_atTop)
  have hfake : ∀ L, IsFakePrimeMeasure L u :=
    isFakePrimeMeasure_of_tendsto (hK.comp htend) (fun n => hU _) ⟨b, hb, fun n j => hle _ j⟩ hcoord
  have hval := eq_pronic_of_forall_isFakePrimeMeasure hfake j
  have := hcoord j
  rwa [hval] at this

end GaloisForLFunctions.RigidArithmeticOfCuts
