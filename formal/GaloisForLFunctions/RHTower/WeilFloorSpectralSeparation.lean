import GaloisForLFunctions.RHTower.HodgeClusterNyquistExclusion

/-!
# Spectral separation of the finite-level Weil form

Let `μ(a)` be the bottom of the polar-constrained level-`a` Weil form of `ζ`, relative to
`∫|f|²`, and let `WeilFloorAtLevel ζ a η` say `μ(a) ≥ -η`. Connes, Consani and Moscovici prove the
limit statement `lim μ = 0 ⇒ RH`. This file resolves it in height.

**Spectral separation** (`weilFloor_spectral_separation`). If `μ(a) ≥ -η`, every zero
`β₀ + it₀` with `β₀ > ½` either lies above the Nyquist height,
`πe^{2a-3/4} ≤ πt₀/2 + O(polylog)`, or satisfies `log(1/η) ≤ πt₀/2 + O(polylog)`. Equivalently,
an off-line zero at height `t` below `≈ 2e^{2a-3/4}` produces an eigenvalue
`≤ -e^{-πt/2 - O(log t(log log t + log 1/δ) + log a)}`, whatever the configuration of nearby zeros.

Together with the unconditional near-radical cluster of `≍ e^{2a}` eigenvalues of size
`exp(-e^{2a-2})`, the spectrum of the level-`a` form near `0` separates into that cluster and one
negative eigenvalue of size `≥ e^{-πt/2}` for each off-line zero at height `t` below Nyquist.

The proof is the cluster test of `HodgeClusterNyquistExclusion` with the floor in place of
positivity. Its `L²` norm is controlled by `sup|f| ≤ 2a‖f''‖₁` (`norm_le_of_contDiff_two_supp`).
-/

open Complex MeasureTheory Filter Topology Set GaloisForLFunctions
open scoped Real Interval
open Zeta23

namespace RHTower

noncomputable section

/-- A `C²` function supported in `[-a, a]` has `sup |f| ≤ 2a ∫|f''|`. -/
theorem norm_le_of_contDiff_two_supp {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) (x : ℝ) :
    ‖f x‖ ≤ 2 * a * ∫ u, ‖deriv (deriv f) u‖ := by
  have hd1 : ∀ u, HasDerivAt f (deriv f u) u := fun u =>
    ((hf.differentiable (by norm_num)) u).hasDerivAt
  have hf1 : ContDiff ℝ 1 (deriv f) := by
    have := hf.iterate_deriv' 1 1
    simpa using this
  have hd2 : ∀ u, HasDerivAt (deriv f) (deriv (deriv f) u) u := fun u =>
    ((hf1.differentiable (by norm_num)) u).hasDerivAt
  have hc2 : Continuous (deriv (deriv f)) := by
    have h2 : ContDiff ℝ 0 (deriv (deriv f)) := by
      have := hf.iterate_deriv' 0 2
      simpa using this
    exact h2.continuous
  -- vanishing outside `[-a, a]`
  have hzero : ∀ u, a < |u| → f =ᶠ[𝓝 u] fun _ => 0 := by
    intro u hu
    have hopen : IsOpen {v : ℝ | a < |v|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hu] with v hv
    by_contra h
    exact absurd (hsupp v h) (not_le.mpr hv)
  have hd0 : ∀ u, a < |u| → deriv f u = 0 := fun u hu => by
    rw [(hzero u hu).deriv_eq]; simp
  have hdd0 : ∀ u, a < |u| → deriv (deriv f) u = 0 := by
    intro u hu
    have hopen : IsOpen {v : ℝ | a < |v|} := isOpen_lt continuous_const continuous_abs
    have hev : deriv f =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hu] with v hv
      exact hd0 v hv
    rw [hev.deriv_eq]; simp
  have hcs : HasCompactSupport (deriv (deriv f)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => hdd0 u ?_
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  have hint : Integrable (deriv (deriv f)) := hc2.integrable_of_hasCompactSupport hcs
  set M := ∫ u, ‖deriv (deriv f) u‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  -- `|f'| ≤ M`
  have hb1 : ∀ y, ‖deriv f y‖ ≤ M := by
    intro y
    set y₀ := -a - 1 - |y|
    have hy₀ : a < |y₀| := by
      rw [abs_of_neg (by have := abs_nonneg y; linarith)]; linarith [abs_nonneg y]
    have hle : y₀ ≤ y := by have := neg_abs_le y; linarith
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := y₀) (b := y)
      (fun t _ => hd2 t) (hc2.intervalIntegrable _ _)
    rw [hd0 y₀ hy₀, sub_zero] at hftc
    rw [← hftc]
    calc ‖∫ t in y₀..y, deriv (deriv f) t‖ ≤ ∫ t in y₀..y, ‖deriv (deriv f) t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hle
      _ ≤ M := by
          rw [intervalIntegral.integral_of_le hle]
          exact setIntegral_le_integral hint.norm (Eventually.of_forall fun _ => norm_nonneg _)
  -- `|f| ≤ 2a M`
  rcases le_or_gt (|x|) a with hx | hx
  · have ha' : -a ≤ x := by have := neg_abs_le x; linarith
    have hxa : x ≤ a := le_trans (le_abs_self x) hx
    have hfa : f (-a) = 0 := by
      have h1 : Tendsto f (𝓝[<] (-a)) (𝓝 (f (-a))) :=
        hf.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto f (𝓝[<] (-a)) (𝓝 0) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun v hv => by
          by_contra h
          have := hsupp v (Ne.symm h)
          rw [abs_of_neg (by simp only [mem_Iio] at hv; linarith)] at this
          simp only [mem_Iio] at hv; linarith)
      exact tendsto_nhds_unique h1 h2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -a) (b := x)
      (fun t _ => hd1 t) (hf1.continuous.intervalIntegrable _ _)
    rw [hfa, sub_zero] at hftc
    rw [← hftc]
    have hb : ∀ t ∈ Ι (-a) x, ‖deriv f t‖ ≤ M := fun t _ => hb1 t
    calc ‖∫ t in (-a)..x, deriv f t‖ ≤ M * |x - -a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ ≤ M * (2 * a) := by
          gcongr; rw [abs_of_nonneg (by linarith)]; linarith
      _ = 2 * a * M := by ring
  · have : f x = 0 := by
      by_contra h; have := hsupp x h; linarith
    rw [this, norm_zero]
    positivity

/-- `∫|f|² ≤ 2a (∫|f|)(∫|f''|)` for a `C²` function supported in `[-a, a]`. -/
theorem integral_norm_sq_le {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ a) :
    ∫ u, ‖f u‖ ^ 2 ≤ 2 * a * (∫ u, ‖deriv (deriv f) u‖) * ∫ u, ‖f u‖ := by
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => ?_
    by_contra h
    have := hsupp u h
    exact hu ⟨by linarith [neg_abs_le u], le_trans (le_abs_self u) this⟩
  have hint : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcs
  set M := 2 * a * ∫ u, ‖deriv (deriv f) u‖
  have hb : ∀ u, ‖f u‖ ^ 2 ≤ M * ‖f u‖ := by
    intro u
    rw [sq]
    exact mul_le_mul_of_nonneg_right (norm_le_of_contDiff_two_supp ha hf hsupp u) (norm_nonneg _)
  calc ∫ u, ‖f u‖ ^ 2 ≤ ∫ u, M * ‖f u‖ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => by positivity)
          (hint.norm.const_mul _) (Eventually.of_forall hb)
    _ = M * ∫ u, ‖f u‖ := integral_const_mul _ _

/-- The bottom of the level-`a` Weil form is at least `-η`: for every polar-constrained `C²` test
supported in `[-a, a]`, `Re W(f,f) ≥ -η ∫|f|²`. -/
def WeilFloorAtLevel (Z : ZeroConfig) (a η : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
    paperFT f (-(I / 2)) = 0 → -(η * ∫ u, ‖f u‖ ^ 2) ≤ (Z.W f f).re

theorem weilFloorAtLevel_of_hodgeIndex {Z : ZeroConfig} {a : ℝ} (h : HodgeIndexAtLevel Z a)
    {η : ℝ} (hη : 0 ≤ η) : WeilFloorAtLevel Z a η := by
  intro f hf hfs hp hm
  have := h f hf hfs hp hm
  have : 0 ≤ η * ∫ u, ‖f u‖ ^ 2 := mul_nonneg hη (integral_nonneg fun _ => by positivity)
  linarith

namespace ClusterSetup

variable (C : ClusterSetup)

local notation "shw" => OffLinePairData.sh

/-- **The cluster inequality under a floor.** If the bottom of the level-`a` Weil form is at
least `-η`, then with `η_t = 6 Σ|c_k| ε` and `B'` the norm bound of the test,
`1 ≤ η_t (4 + 14 S_Z e^{a/2} B') + 6 a η B'²`. -/
theorem cluster_floor_inequality {ρ₀ : XiDivisorSupport} (hρ₀ : ρ₀ ∈ C.nodes) {a η : ℝ}
    (ha : 1 ≤ a) (hη : 0 ≤ η) (hH : WeilFloorAtLevel zetaZeroConfig a η) {Kp : ℝ}
    (hKp2 : 2 ≤ Kp) (hKp : ∀ b x : ℝ, |plateau₁ b shw x| ≤ Kp ∧ |plateau₂ b shw x| ≤ Kp) :
    1 ≤ (6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh)) *
        (4 + 14 * zeroSumZ * Real.exp (a / 2) *
          (4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
            ((1 + (C.t₀ + 2)) ^ 2 * C.Bk))) +
      6 * a * η * (4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
            ((1 + (C.t₀ + 2)) ^ 2 * C.Bk)) ^ 2 := by
  classical
  set ηt := 6 * coeffMass C.Q * expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) with hηt
  have hηt0 : 0 ≤ ηt := by
    have := coeffMass_nonneg C.Q; have := expTail_nonneg C.K (1 / 2) (a - 1 / 4 - shw)
    positivity
  obtain ⟨hK, -, -⟩ := C.K_spec
  obtain ⟨k₁, k₂, hd1, hd2, ck₁, ck₂, ik₁, ik₂, nh, nk₁, nk₂⟩ := C.K_calculus hρ₀
  have hΓ : 0 ≤ C.t₀ + 2 := by linarith [C.ht₀]
  obtain ⟨hC2, hN12⟩ := clusterTest_calculus hK hd1 hd2 ck₁ ck₂ ik₁ ik₂ hΓ nh nk₁ nk₂ C.Q C.κ
    (heightPolarShift C.t₀) (a - 1 / 4) hKp2 hKp
  have hsp0 : 0 ≤ heightPolarShift C.t₀ := by linarith [(heightPolarShift_mem C.ht₀).1]
  have hsupp : ∀ u, C.test a u ≠ 0 → |u| ≤ a :=
    clusterTest_supp C.κ_pos.le hsp0 (C.test_supp_bound a)
  have htsupp : tsupport (C.test a) ⊆ Icc (-a) a :=
    tsupport_clusterTest C.κ_pos.le hsp0 (C.test_supp_bound a)
  have hp1 : paperFT (C.test a) (I / 2) = 0 := by
    unfold test; rw [paperFT_clusterTest hK, polarSymbol_half_I]; ring
  have hp2 : paperFT (C.test a) (-(I / 2)) = 0 := by
    unfold test; rw [paperFT_clusterTest hK, polarSymbol_neg_half_I]; ring
  have hC2' : ContDiff ℝ 2 (C.test a) := hC2
  have hW0 := hH (C.test a) hC2' htsupp hp1 hp2
  set F : Finset zetaZeroConfig.carrier := C.nodes.image toCarrier with hF
  have hother : ∀ ρ : zetaZeroConfig.carrier, ρ ∉ F →
      ‖paperFT (C.test a) (gammaOf (ρ : ℂ))‖ ≤ ηt := by
    intro ρ hρ
    refine C.test_off_node a fun ν hν e => hρ ?_
    rw [hF, Finset.mem_image]
    exact ⟨ν, hν, Subtype.ext e.symm⟩
  have hsplit := re_W_le_nodes_add (by linarith) hC2' hsupp F hηt0 hother
  set N12 := (∫ u, ‖C.test a u‖) + ∫ u, ‖deriv (deriv (C.test a)) u‖ with hN12def
  have hN1 : 0 ≤ ∫ u, ‖C.test a u‖ := integral_nonneg fun _ => norm_nonneg _
  have hN2 : 0 ≤ ∫ u, ‖deriv (deriv (C.test a)) u‖ := integral_nonneg fun _ => norm_nonneg _
  have hN120 : 0 ≤ N12 := by positivity
  have hS := zeroSumZ_nonneg
  have hsumF : ∑ ρ ∈ F, (zetaZeroConfig.Wsummand (C.test a) (C.test a) ρ).re =
      ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re :=
    Finset.sum_image fun x _ y _ h => toCarrier_injective h
  set B' := 4 * Kp * (coeffMass C.Q * (1 + Real.cosh (heightPolarShift C.t₀ / 2))) *
    ((1 + (C.t₀ + 2)) ^ 2 * C.Bk) with hB'
  have hNB : N12 ≤ B' := hN12
  have hexp := Real.exp_pos (a / 2)
  -- the `L²` norm of the test
  have hL2 : ∫ u, ‖C.test a u‖ ^ 2 ≤ 2 * a * N12 ^ 2 := by
    have h := integral_norm_sq_le (by linarith) hC2' hsupp
    have : (∫ u, ‖deriv (deriv (C.test a)) u‖) * (∫ u, ‖C.test a u‖) ≤ N12 ^ 2 := by
      rw [hN12def]; nlinarith
    have ha0 : 0 ≤ 2 * a := by linarith
    calc ∫ u, ‖C.test a u‖ ^ 2 ≤ 2 * a * (∫ u, ‖deriv (deriv (C.test a)) u‖) *
          ∫ u, ‖C.test a u‖ := h
      _ = 2 * a * ((∫ u, ‖deriv (deriv (C.test a)) u‖) * ∫ u, ‖C.test a u‖) := by ring
      _ ≤ 2 * a * N12 ^ 2 := mul_le_mul_of_nonneg_left this ha0
  have hfloor : η * ∫ u, ‖C.test a u‖ ^ 2 ≤ 2 * a * η * B' ^ 2 := by
    have hB'0 : 0 ≤ B' := hN120.trans hNB
    calc η * ∫ u, ‖C.test a u‖ ^ 2 ≤ η * (2 * a * N12 ^ 2) := mul_le_mul_of_nonneg_left hL2 hη
      _ ≤ η * (2 * a * B' ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hη
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact pow_le_pow_left₀ hN120 hNB 2
      _ = 2 * a * η * B' ^ 2 := by ring
  have hfl0 : 0 ≤ 2 * a * η * B' ^ 2 := by
    have : 0 ≤ a := by linarith
    positivity
  -- opaque atoms
  have hB'0 : 0 ≤ B' := hN120.trans hNB
  obtain ⟨E, hEdef⟩ : ∃ x, x = Real.exp (a / 2) := ⟨_, rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ x, x = zeroSumZ * ηt * E * B' := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ x, x = a * η * B' ^ 2 := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hEdef]; exact Real.exp_pos _
  have hT10 : 0 ≤ T1 := by
    rw [hT1]; exact mul_nonneg (mul_nonneg (mul_nonneg hS hηt0) hE0.le) hB'0
  have ha0 : 0 ≤ a := by linarith
  have hT20 : 0 ≤ T2 := by
    rw [hT2]; exact mul_nonneg (mul_nonneg ha0 hη) (sq_nonneg _)
  have hgoal : ηt * (4 + 14 * zeroSumZ * Real.exp (a / 2) * B') + 6 * a * η * B' ^ 2 =
      4 * ηt + 14 * T1 + 6 * T2 := by rw [hT1, hT2, hEdef]; ring
  rw [hgoal]
  by_cases hηs : ηt ≤ 1 / 4
  · have hsq : ηt ^ 2 ≤ (1 / 4) * ηt := by rw [sq]; exact mul_le_mul_of_nonneg_right hηs hηt0
    have hneg : -1 + 2 * ηt + ηt ^ 2 ≤ -(3 / 8) := by linarith
    have hterm : ∀ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤
        (zetaZeroConfig.mult (toCarrier ν) : ℝ) * (-(3 / 8)) := by
      intro ν hν
      refine (C.re_summand_node_le a hν).trans ?_
      exact mul_le_mul_of_nonneg_left hneg (Nat.cast_nonneg _)
    have hblock : ∑ ν ∈ C.nodes, (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤
        -(3 / 8) := by
      rw [← Finset.add_sum_erase _ _ hρ₀]
      have h1 := hterm ρ₀ hρ₀
      have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (toCarrier ρ₀) := by
        exact_mod_cast zetaZeroConfig.one_le_mult _ (toCarrier ρ₀).2
      have h2 : ∑ ν ∈ C.nodes.erase ρ₀,
          (zetaZeroConfig.Wsummand (C.test a) (C.test a) (toCarrier ν)).re ≤ 0 := by
        refine Finset.sum_nonpos fun ν hν => (hterm ν (Finset.mem_of_mem_erase hν)).trans ?_
        exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by norm_num)
      linarith
    rw [hsumF] at hsplit
    obtain ⟨P1, hP1⟩ : ∃ x, x = (5 / 4) * zeroSumZ * (ηt * (Real.exp (a / 2) *
        (4 * ((∫ u, ‖C.test a u‖) + ∫ u, ‖deriv (deriv (C.test a)) u‖)))) := ⟨_, rfl⟩
    rw [← hP1] at hsplit
    have hP1le : P1 ≤ 5 * T1 := by
      have e1 : P1 = 5 * (zeroSumZ * ηt * E * N12) := by rw [hP1, hEdef, hN12def]; ring
      have : zeroSumZ * ηt * E * N12 ≤ zeroSumZ * ηt * E * B' :=
        mul_le_mul_of_nonneg_left hNB (mul_nonneg (mul_nonneg hS hηt0) hE0.le)
      rw [e1, hT1]; linarith
    have hfl : η * ∫ u, ‖C.test a u‖ ^ 2 ≤ 2 * T2 := by rw [hT2]; linarith [hfloor]
    linarith
  · push Not at hηs
    linarith

end ClusterSetup

local notation "Φ" => riemannPhiKernel
local notation "Mθ" => jacobiThetaTailConstant

/-- **Spectral separation, product form.** There are absolute constants `K₀, K₁` such that, if
the bottom of the level-`a` Weil form is at least `-η` (`a ≥ 1`, `η ≥ 0`), then every zero
`ρ₀ = β₀ + it₀` with `β₀ > ½`, `t₀ ≥ 101` and `6 + 3N ≤ 2πe^{2X}` (`X = a - 3/8`) satisfies

`1 ≤ K₀ 2^N B ((N+1)M)² e^{a/2}(t₀+3)² e^{(5+3N)X - πe^{2X}} + K₁ a η ((N+1)M)² (t₀+3)⁴ B²`,

with `N`, `B = max(B_N, 1)` and `M = interpBound t₀ δ₀ N` as in
`hodgeIndex_excludes_clustered_zero`. -/
theorem weilFloor_excludes_clustered_zero :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {a η : ℝ}, 1 ≤ a → 0 ≤ η →
      WeilFloorAtLevel zetaZeroConfig a η →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) →
        1 ≤ K₀ * (2 ^ windowCount ρ₀.im *
            max (2 ^ windowCount ρ₀.im * expTail Φ (3 / 2 * windowCount ρ₀.im) 0) 1) *
          ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im)) ^ 2 *
          Real.exp (a / 2) * (ρ₀.im + 3) ^ 2 *
          Real.exp ((1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 9 / 2) * (a - 3 / 8) -
            π * Real.exp (2 * (a - 3 / 8))) +
        K₁ * a * η * ((windowCount ρ₀.im + 1) *
            ClusterSetup.interpBound ρ₀.im (ρ₀.re - 1 / 2) (windowCount ρ₀.im)) ^ 2 *
          (ρ₀.im + 3) ^ 4 *
          (max (2 ^ windowCount ρ₀.im * expTail Φ (3 / 2 * windowCount ρ₀.im) 0) 1) ^ 2 := by
  obtain ⟨Kp, hKp2, hKp⟩ := OffLinePairData.exists_plateau_constant
  have hS := zeroSumZ_nonneg
  have hM : 0 ≤ Mθ := jacobiThetaTailConstant_nonneg
  set c₁ : ℝ := 140 * zeroSumZ * Kp with hc₁
  have hK0 : 0 ≤ Kp := by linarith
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; exact mul_nonneg (mul_nonneg (by norm_num) hS) hK0
  refine ⟨6 * (4 + c₁) * (80 * Mθ * Real.exp π + 1), 6 * (10 * Kp) ^ 2, by positivity,
    by positivity, ?_⟩
  intro a η ha hη hH ρ₀ hρ₀ hβ ht hlam
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero (by
    rw [xi_eq_xiUnit_mul_zeta (fun h => by rw [h] at hβ; norm_num at hβ)
      (fun h => by rw [h] at hnt; exact absurd hnt.2.2 (by norm_num)) hnt.2.1, hnt.1, mul_zero])
  set ν₀ : XiDivisorSupport := q.1
  have hν₀ : (ν₀ : ℂ) = ρ₀ := hq
  obtain ⟨C, hCt, hCδ⟩ := exists_clusterSetup ht (δ₀ := ρ₀.re - 1 / 2) (by linarith)
    (by linarith [hnt.2.2])
  have hν₀N : ν₀ ∈ C.nodes := by
    rw [mem_nodeSet (by linarith [C.hX2]), hν₀, hCt, sub_self, abs_zero]
    refine ⟨by linarith [C.hX1], ?_⟩
    rw [abs_of_pos (by linarith)]
    have := C.hy₁; rw [hCδ] at this; linarith
  have hraw := C.cluster_floor_inequality hν₀N ha hη hH hKp2 hKp
  set W := windowCount C.t₀ with hWdef
  have hWt : windowCount C.t₀ = windowCount ρ₀.im := by rw [hCt]
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound C.t₀ C.δ₀ W := ⟨_, rfl⟩
  have hMi1 : 1 ≤ Mi := by rw [hMidef]; exact C.one_le_interpBound
  have hMi0 : 0 ≤ Mi := by linarith
  have hne : C.nodes.Nonempty := ⟨ν₀, hν₀N⟩
  have hcM : coeffMass C.Q ≤ (W + 1) * Mi := by
    rw [hMidef]
    exact (C.coeffMass_le hne).trans (mul_le_mul_of_nonneg_left C.Mq_le_interpBound (by positivity))
  have hcM0 := coeffMass_nonneg C.Q
  obtain ⟨εΦ, hεΦdef⟩ : ∃ x, x = (80 * Mθ * Real.exp π + 1) *
    Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) :=
    ⟨_, rfl⟩
  have hε : expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) ≤ 2 ^ W * εΦ := by
    have h1 := C.K_tail (1 / 2) (a - 1 / 4 - OffLinePairData.sh) (by norm_num)
    have hsh : a - 1 / 4 - OffLinePairData.sh = a - 3 / 8 := by unfold OffLinePairData.sh; ring
    rw [hsh] at h1
    have h2 : expTail Φ (1 / 2 + 3 / 2 * W) (a - 3 / 8) ≤
        expTail Φ (1 / 2 + 3 / 2 * ((2 * W : ℕ) : ℝ)) (a - 3 / 8) := by
      apply expTail_mono_weight superExpDecay_riemannPhiKernel
      push_cast; have : (0 : ℝ) ≤ W := Nat.cast_nonneg _; linarith
    have h3 := expTail_riemannPhiKernel_level_le ha W (by rw [hWdef, hWt]; exact hlam)
    rw [hsh]
    calc expTail C.K (1 / 2) (a - 3 / 8) ≤ 2 ^ W * expTail Φ (1 / 2 + 3 / 2 * W) (a - 3 / 8) := h1
      _ ≤ 2 ^ W * εΦ := by rw [hεΦdef]; gcongr; exact h2.trans h3
  have hε0 : 0 ≤ expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := expTail_nonneg _ _ _
  have hεΦ0 : 0 ≤ εΦ := by rw [hεΦdef]; positivity
  have hcosh : 1 + Real.cosh (heightPolarShift C.t₀ / 2) ≤ 5 / 2 := by
    have := (heightPolarShift_mem C.ht₀).2
    have h := cosh_le_exp_abs (heightPolarShift C.t₀ / 2)
    rw [abs_of_pos (by linarith [(heightPolarShift_mem C.ht₀).1])] at h
    have h2 : Real.exp (heightPolarShift C.t₀ / 2) ≤ 3 / 2 :=
      (Real.exp_le_exp.mpr (by unfold OffLinePairData.sh; linarith)).trans
        OffLinePairData.exp_sh_half_le
    linarith
  have hB := C.Bk_nonneg
  have hW1 : (1 : ℝ) ≤ W + 1 := by have : (0 : ℝ) ≤ W := Nat.cast_nonneg _; linarith
  have hea := Real.one_le_exp (by linarith : (0 : ℝ) ≤ a / 2)
  have hT1 : (1 : ℝ) ≤ (C.t₀ + 3) ^ 2 := by have := C.ht₀; nlinarith
  have hT : (1 + (C.t₀ + 2)) ^ 2 = (C.t₀ + 3) ^ 2 := by ring
  rw [hT] at hraw
  obtain ⟨cM, hcMdef⟩ : ∃ x, x = coeffMass C.Q := ⟨_, rfl⟩
  obtain ⟨ε, hεdef⟩ : ∃ x, x = expTail C.K (1 / 2) (a - 1 / 4 - OffLinePairData.sh) := ⟨_, rfl⟩
  obtain ⟨ch, hchdef⟩ : ∃ x, x = 1 + Real.cosh (heightPolarShift C.t₀ / 2) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ x, x = (C.t₀ + 3) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ea, hEadef⟩ : ∃ x, x = Real.exp (a / 2) := ⟨_, rfl⟩
  obtain ⟨Bk, hBkdef⟩ : ∃ x, x = C.Bk := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ x, x = zeroSumZ := ⟨_, rfl⟩
  rw [← hcMdef, ← hεdef, ← hchdef, ← hTdef, ← hEadef, ← hBkdef, ← hSdef] at hraw
  rw [← hcMdef] at hcM hcM0
  rw [← hεdef] at hε hε0
  rw [← hchdef] at hcosh
  rw [← hTdef] at hT1
  rw [← hEadef] at hea
  rw [← hBkdef] at hB
  rw [← hSdef] at hS hc₁
  have hch0 : 0 ≤ ch := by rw [hchdef]; have := Real.cosh_pos (heightPolarShift C.t₀ / 2); linarith
  set Bm := max Bk 1 with hBmdef
  have hBm : Bk ≤ Bm := le_max_left _ _
  have hBm1 : 1 ≤ Bm := le_max_right _ _
  obtain ⟨P, hPdef⟩ : ∃ x, x = (W + 1) * Mi * Ea * T * Bm := ⟨_, rfl⟩
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hW1 hMi1) hea) hT1) hBm1
  -- the norm bound `B'`
  obtain ⟨B', hB'def⟩ : ∃ x, x = 4 * Kp * (cM * ch) * (T * Bk) := ⟨_, rfl⟩
  rw [← hB'def] at hraw
  have hB'le : B' ≤ 10 * Kp * ((W + 1) * Mi) * T * Bm := by
    have h1 : cM * ch ≤ ((W + 1) * Mi) * (5 / 2) :=
      mul_le_mul hcM hcosh hch0 (by positivity)
    have h2 : T * Bk ≤ T * Bm := mul_le_mul_of_nonneg_left hBm (by linarith)
    rw [hB'def]
    calc 4 * Kp * (cM * ch) * (T * Bk) ≤ 4 * Kp * (((W + 1) * Mi) * (5 / 2)) * (T * Bm) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
            (mul_nonneg (by linarith) hB) (by positivity)
      _ = 10 * Kp * ((W + 1) * Mi) * T * Bm := by ring
  have hB'0 : 0 ≤ B' := by rw [hB'def]; exact mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hcM0 hch0)) (mul_nonneg (by linarith) hB)
  have hinner : 4 + 14 * S * Ea * B' ≤ (4 + c₁) * P := by
    have h4 : 14 * S * Ea * B' ≤ 14 * S * Ea * (10 * Kp * ((W + 1) * Mi) * T * Bm) :=
      mul_le_mul_of_nonneg_left hB'le (mul_nonneg (mul_nonneg (by norm_num) hS) (by linarith))
    have h5 : 14 * S * Ea * (10 * Kp * ((W + 1) * Mi) * T * Bm) = c₁ * P := by
      rw [hc₁, hPdef]; ring
    linarith
  have hA : (6 * cM * ε) * (4 + 14 * S * Ea * B') ≤
      (6 * ((W + 1) * Mi) * (2 ^ W * εΦ)) * ((4 + c₁) * P) := by
    have h14 : 0 ≤ 14 * S * Ea * B' :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hS) (by linarith)) hB'0
    refine mul_le_mul ?_ hinner (by linarith)
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hMi0))
        (mul_nonneg (by positivity) hεΦ0))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hcM (by norm_num)) hε hε0
      (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hMi0))
  have hBsq : 6 * a * η * B' ^ 2 ≤ 6 * a * η * (10 * Kp * ((W + 1) * Mi) * T * Bm) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hη)
    exact pow_le_pow_left₀ hB'0 hB'le 2
  have hgoal := hraw.trans (add_le_add hA hBsq)
  -- rewrite into the stated form
  rw [← hWt, ← hCt]
  have hδ' : ρ₀.re - 1 / 2 = C.δ₀ := hCδ.symm
  have hBkC : 2 ^ W * expTail Φ (3 / 2 * W) 0 = Bk := by rw [hBkdef]; rfl
  have hMiC : ClusterSetup.interpBound C.t₀ (ρ₀.re - 1 / 2) W = Mi := by rw [hδ', hMidef]
  have hT4 : (C.t₀ + 3) ^ 4 = T ^ 2 := by rw [hTdef]; ring
  rw [hBkC, hMiC, ← hEadef, hT4, ← hTdef]
  rw [hPdef, hεΦdef] at hgoal
  calc (1 : ℝ) ≤ _ := hgoal
    _ = _ := by ring

/-- **Spectral separation at finite level.** If the bottom of the level-`a` Weil form is at least
`-η` (`a ≥ 1`, `η > 0`), then every zero `ρ₀ = β₀+it₀` with `β₀ > ½`, `t₀ ≥ 101`, and
`6 + 3N ≤ 2πe^{2X}` (`X = a - 3/8`) lies above the Nyquist height,

`πe^{2X} ≤ π(t₀+1)/2 + 2 log(N+1) + 2 L + a/2 + 2 log(t₀+3) + (5+3N)X + log(2K₀ 2^N B)`,

or it forces the floor down,

`log(1/η) ≤ π(t₀+1)/2 + 2 log(N+1) + 2 L + 4 log(t₀+3) + 2 log B + log(2K₁ a)`,

where `L = log 32 + N log 3 + N log(32(N+1)) + 2N log(16e/δ₀) + 2 + N log 5 + 3C log t₀ - log δ₀`,
`δ₀ = β₀ - ½`, and `B = max(2^N ∫|Φ|e^{3N|u|/2}, 1)`. In words: an off-line zero at height `t`
below the Nyquist height `≈ 2e^{2a-3/4}` produces an eigenvalue `≤ -e^{-πt/2 - O(polylog)}`. -/
theorem weilFloor_spectral_separation :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ {a η : ℝ}, 1 ≤ a → 0 < η →
      WeilFloorAtLevel zetaZeroConfig a η →
      ∀ {ρ₀ : ℂ}, ρ₀ ∈ zetaZeroConfig.carrier → 1 / 2 < ρ₀.re → 101 ≤ ρ₀.im →
        1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 11 / 2 ≤ 2 * π * Real.exp (2 * (a - 3 / 8)) →
        (π * Real.exp (2 * (a - 3 / 8)) ≤ π * (ρ₀.im + 1) / 2 +
          2 * Real.log (windowCount ρ₀.im + 1) +
          2 * (Real.log 32 + windowCount ρ₀.im * Real.log 3 +
            windowCount ρ₀.im * Real.log (32 * (windowCount ρ₀.im + 1 : ℝ)) +
            2 * windowCount ρ₀.im * Real.log (16 * Real.exp 1 / (ρ₀.re - 1 / 2)) +
            (2 + windowCount ρ₀.im * Real.log 5 + 3 * (windowLogConst * Real.log ρ₀.im)) -
            Real.log (ρ₀.re - 1 / 2)) +
          a / 2 + 2 * Real.log (ρ₀.im + 3) +
          (1 / 2 + 3 * (windowCount ρ₀.im : ℝ) + 9 / 2) * (a - 3 / 8) +
          Real.log (2 * K₀ * (2 ^ windowCount ρ₀.im *
            max (2 ^ windowCount ρ₀.im * expTail Φ (3 / 2 * windowCount ρ₀.im) 0) 1))) ∨
        (Real.log (1 / η) ≤ π * (ρ₀.im + 1) / 2 +
          2 * Real.log (windowCount ρ₀.im + 1) +
          2 * (Real.log 32 + windowCount ρ₀.im * Real.log 3 +
            windowCount ρ₀.im * Real.log (32 * (windowCount ρ₀.im + 1 : ℝ)) +
            2 * windowCount ρ₀.im * Real.log (16 * Real.exp 1 / (ρ₀.re - 1 / 2)) +
            (2 + windowCount ρ₀.im * Real.log 5 + 3 * (windowLogConst * Real.log ρ₀.im)) -
            Real.log (ρ₀.re - 1 / 2)) +
          4 * Real.log (ρ₀.im + 3) +
          2 * Real.log (max (2 ^ windowCount ρ₀.im * expTail Φ (3 / 2 * windowCount ρ₀.im) 0) 1) +
          Real.log (2 * K₁ * a)) := by
  obtain ⟨K₀, K₁, hK₀, hK₁, h⟩ := weilFloor_excludes_clustered_zero
  refine ⟨K₀, K₁, hK₀, hK₁, fun {a η} ha hη hH {ρ₀} hρ₀ hβ ht hlam => ?_⟩
  have hmain := h ha hη.le hH hρ₀ hβ ht hlam
  set W := windowCount ρ₀.im
  set δ₀ := ρ₀.re - 1 / 2
  have hδ : 0 < δ₀ := by simp only [δ₀]; linarith
  obtain ⟨Mi, hMidef⟩ : ∃ x, x = ClusterSetup.interpBound ρ₀.im δ₀ W := ⟨_, rfl⟩
  obtain ⟨Bm, hBmdef⟩ : ∃ x, x = max (2 ^ W * expTail Φ (3 / 2 * W) 0) 1 := ⟨_, rfl⟩
  have hBm1 : 1 ≤ Bm := by rw [hBmdef]; exact le_max_right _ _
  have hBm : 0 < Bm := by linarith
  have hMi : 0 < Mi := by
    rw [hMidef]; unfold ClusterSetup.interpBound; have := Real.exp_pos 1; positivity
  rw [← hMidef, ← hBmdef] at hmain
  have hW1 : (0 : ℝ) < W + 1 := by positivity
  have ht3 : (0 : ℝ) < ρ₀.im + 3 := by linarith
  have hLMi := log_interpBound ρ₀.im δ₀ hδ W
  rw [← hMidef] at hLMi
  rw [← hBmdef]
  obtain ⟨A, hAdef⟩ : ∃ x, x = K₀ * (2 ^ W * Bm) * ((W + 1) * Mi) ^ 2 * Real.exp (a / 2) *
      (ρ₀.im + 3) ^ 2 * Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) -
        π * Real.exp (2 * (a - 3 / 8))) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ x, x = K₁ * a * η * ((W + 1) * Mi) ^ 2 * (ρ₀.im + 3) ^ 4 * Bm ^ 2 :=
    ⟨_, rfl⟩
  rw [← hAdef, ← hBdef] at hmain
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hapos : 0 < a := by linarith
  have hB0 : 0 < B := by
    rw [hBdef]
    exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hK₁ hapos) hη) (by positivity))
      (by positivity)) (by positivity)
  rcases le_or_gt (1 / 2) A with hA | hA
  · left
    have h2A : 1 ≤ 2 * A := by linarith
    have hlog := Real.log_nonneg h2A
    rw [hAdef] at hlog
    have e : 2 * (K₀ * (2 ^ W * Bm) * ((W + 1) * Mi) ^ 2 * Real.exp (a / 2) * (ρ₀.im + 3) ^ 2 *
        Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8)))) =
        (2 * K₀ * (2 ^ W * Bm)) * ((W + 1) * Mi) ^ 2 * Real.exp (a / 2) * (ρ₀.im + 3) ^ 2 *
        Real.exp ((1 / 2 + 3 * (W : ℝ) + 9 / 2) * (a - 3 / 8) - π * Real.exp (2 * (a - 3 / 8))) := by
      ring
    rw [e, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_mul hW1.ne' hMi.ne'] at hlog
    push_cast at hlog
    linarith [hLMi]
  · right
    have h2B : 1 ≤ 2 * B := by linarith
    have hlog := Real.log_nonneg h2B
    rw [hBdef] at hlog
    have e : 2 * (K₁ * a * η * ((W + 1) * Mi) ^ 2 * (ρ₀.im + 3) ^ 4 * Bm ^ 2) =
        (2 * K₁ * a) * η * ((W + 1) * Mi) ^ 2 * (ρ₀.im + 3) ^ 4 * Bm ^ 2 := by ring
    have ha0 : 0 < 2 * K₁ * a := mul_pos (by positivity) (by linarith)
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul ha0.ne' hη.ne', Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_mul hW1.ne' hMi.ne'] at hlog
    rw [one_div, Real.log_inv]
    push_cast at hlog
    linarith [hLMi]

end

end RHTower
