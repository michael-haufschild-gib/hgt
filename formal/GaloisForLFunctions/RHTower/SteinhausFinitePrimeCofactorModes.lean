import GaloisForLFunctions.RHTower.SteinhausFinitePrimeCofactorRank

/-!
# Prescribed cofactor modes on separated blocks

For any finite list of real twists, extend a prescribed finite prime phase assignment to one
phase realizing every corresponding Cauchy mode uniformly on a separated block `[M, 2*M]`.
The mean-weighted block length `M * norm(A)^2` exceeds any prescribed budget. Each new coherent
extension is frozen through the end of its block before the next extension is selected.

These are literal hard-cutoff cofactor sums. Smooth AFE weights, prime counts, conditional Gram
bounds, and the simultaneous target law still require separate transfer arguments.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

/-- The node direction of a prescribed coherent twist. -/
def cofactorCauchyMode {J : ℕ} (s : Fin J → ℂ) (t : ℝ) : Fin J → ℂ :=
  fun j => (s j + (t : ℂ) * Complex.I)⁻¹

/-- Remove the common twist phase and divide by the finite-prefix mean. -/
def relativeCofactorMode {J : ℕ} (s : Fin J → ℂ) (t : ℝ) (A : ℂ)
    (N : ℕ) (omega : SteinhausModel.Omega) : Fin J → ℂ :=
  A⁻¹ • ((N : ℂ) ^ (-((t : ℂ) * Complex.I)) • cofactorNodeVector s N omega)

/-- After division by its nonzero prefix mean, a coherent extension approaches its
prescribed Cauchy mode in the full finite node space. -/
theorem tendsto_relativeCofactorMode_extension
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (omega : SteinhausModel.Omega) (t : ℝ) :
    Tendsto (fun N => relativeCofactorMode s t
      (finitePrimePhaseMean S (fun p => omega p - t * Real.log p / (2 * Real.pi)))
      N (finitePrimeTwistExtension S omega t)) atTop (𝓝 (cofactorCauchyMode s t)) := by
  let A := finitePrimePhaseMean S (fun p => omega p - t * Real.log p / (2 * Real.pi))
  have hA : A ≠ 0 := finitePrimePhaseMean_ne_zero _ _
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (tendsto_finitePrimeTwistExtension_weighted_mean S omega t (hs j) (hs1 j)).const_mul A⁻¹
  have heq : A⁻¹ * (A / (s j + (t : ℂ) * Complex.I)) = cofactorCauchyMode s t j := by
    simp [cofactorCauchyMode, div_eq_mul_inv, hA]
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  change A⁻¹ * (_ * (N : ℂ) ^ (-(s j + (t : ℂ) * Complex.I))) =
    A⁻¹ * ((N : ℂ) ^ (-((t : ℂ) * Complex.I)) *
      ((_ : ℂ) * (N : ℂ) ^ (-s j)))
  congr 1
  rw [show -(s j + (t : ℂ) * Complex.I) = -s j + -((t : ℂ) * Complex.I) by ring,
    Complex.cpow_add _ _ hN0]
  ring

private theorem exists_cofactor_mode_block
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (omega : SteinhausModel.Omega) (t : ℝ) (B : ℕ) (K ε : ℝ) (hε : 0 < ε) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ M : ℕ, B ≤ M ∧ ∃ A : ℂ, A ≠ 0 ∧ K ≤ (M : ℝ) * ‖A‖ ^ 2 ∧
        ∀ L : ℕ, M ≤ L →
          ‖relativeCofactorMode s t A L omega' - cofactorCauchyMode s t‖ < ε := by
  let A := finitePrimePhaseMean S (fun p => omega p - t * Real.log p / (2 * Real.pi))
  have hA : A ≠ 0 := finitePrimePhaseMean_ne_zero _ _
  have hApos : 0 < ‖A‖ ^ 2 := pow_pos (norm_pos_iff.mpr hA) 2
  have hlim := tendsto_relativeCofactorMode_extension s hs hs1 S omega t
  have hev := hlim.eventually (Metric.ball_mem_nhds _ hε)
  simp only [dist_eq_norm] at hev
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hev
  obtain ⟨C, hC⟩ := exists_nat_gt (K / ‖A‖ ^ 2)
  let M := B + C + M₀
  refine ⟨finitePrimeTwistExtension S omega t,
    fun _ hp => finitePrimeTwistExtension_eq_on_prefix S omega t hp,
    M, by omega, A, hA, ?_, ?_⟩
  · have hc : K < (C : ℝ) * ‖A‖ ^ 2 := (div_lt_iff₀ hApos).mp hC
    exact hc.le.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show C ≤ M by omega)) hApos.le)
  · intro L hL
    exact hM₀ L (by omega)

/-- A single extending phase realizes any finite prescribed list of coherent modes on
separated cofactor blocks. Each block has arbitrarily large mean-weighted length. -/
theorem exists_prescribed_cofactor_mode_blocks
    {J : ℕ} (s : Fin J → ℂ) (hs : ∀ j, 0 < (s j).re)
    (hs1 : ∀ j, (s j).re < 1) (S : Finset ℕ)
    (omega : SteinhausModel.Omega) (B : ℕ) (K ε : ℝ) (hε : 0 < ε) :
    ∀ k : ℕ, ∀ t : Fin k → ℝ, ∃ omega' : SteinhausModel.Omega,
      (∀ p ∈ S, omega' p = omega p) ∧ ∃ M : Fin k → ℕ, ∃ A : Fin k → ℂ,
        (∀ i j, i < j → 2 * M i < M j) ∧
        ∀ i, B ≤ M i ∧ A i ≠ 0 ∧ K ≤ (M i : ℝ) * ‖A i‖ ^ 2 ∧
          ∀ L : ℕ, M i ≤ L → L ≤ 2 * M i →
            ‖relativeCofactorMode s (t i) (A i) L omega' - cofactorCauchyMode s (t i)‖ < ε := by
  classical
  intro k
  induction k with
  | zero =>
    intro t
    exact ⟨omega, fun _ _ => rfl, Fin.elim0, Fin.elim0,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro t
    obtain ⟨omega₀, hp₀, M, A, hsep, hblocks⟩ := ih (Fin.init t)
    let S' := S ∪ Finset.univ.biUnion (fun i => Finset.range (2 * M i + 1))
    let B' := B + (∑ i, 2 * M i) + 1
    obtain ⟨omega₁, hp₁, N, hN, a, ha, henergy, hmode⟩ :=
      exists_cofactor_mode_block s hs hs1 S' omega₀ (t (Fin.last k)) B' K ε hε
    have hpreserve : ∀ i L, L ≤ 2 * M i →
        cofactorNodeVector s L omega₁ = cofactorNodeVector s L omega₀ := by
      intro i L hL
      apply cofactorNodeVector_congr_prefix
      intro p hp
      apply hp₁ p
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_range.mpr (by omega)⟩)
    have hnewsep : ∀ i, 2 * M i < N := by
      intro i
      have hi : 2 * M i ≤ ∑ j, 2 * M j :=
        Finset.single_le_sum (fun j _ => show 0 ≤ 2 * M j from Nat.zero_le _) (Finset.mem_univ i)
      omega
    refine ⟨omega₁, ?_, Fin.snoc M N, Fin.snoc A a, ?_, ?_⟩
    · intro p hp
      exact (hp₁ p (Finset.mem_union_left _ hp)).trans (hp₀ p hp)
    · intro i j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · refine Fin.lastCases ?_ (fun i' => ?_) i
        · simp
        · intro _
          simpa using hnewsep i'
      · refine Fin.lastCases ?_ (fun i' => ?_) i
        · intro hij
          have hj := j'.isLt
          change k < j'.val at hij
          omega
        · intro hij
          simpa using hsep i' j' (by simpa using hij)
    · intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp only [Fin.snoc_last]
        exact ⟨by omega, ha, henergy, fun L hL _ => hmode L hL⟩
      · simp only [Fin.snoc_castSucc]
        refine ⟨(hblocks i').1, (hblocks i').2.1, (hblocks i').2.2.1, ?_⟩
        intro L hlo hhi
        have hh := (hblocks i').2.2.2 L hlo hhi
        simpa only [relativeCofactorMode, hpreserve i' L hhi, Fin.init] using hh

end RHTower
