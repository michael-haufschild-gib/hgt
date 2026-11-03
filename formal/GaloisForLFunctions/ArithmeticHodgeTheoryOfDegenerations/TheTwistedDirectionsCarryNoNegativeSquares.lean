import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerIsGradedByEveryConductor
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndexCountsTheRightZeros

/-!
# The twisted directions carry no negative squares

The window index counts the negative squares of the second-order term on a family of untwisted
windows. This file shows that windows twisted by Ramanujan expansions never add one: on a mixed
family (untwisted windows `h_i`, windows `g_j` twisted by `χ = Σ_{m ∈ S} a_m c_m`) the normalized
Gram matrices of the complete family converge to the graded limit

`fromBlocks P_K 0 0 (Λ · A(G))`,   `Λ = (Σ_m a_m² J_{β+1}(m)) βJ/K ≥ 0`,

(`tendsto_mixedGram`): the window pencil on the untwisted block, `Λ` times the aliasing Gram matrix on
the twisted block (polarization of Parseval for the count), and no coupling (orthogonality of
untwisted and twisted windows). Its negative index is `ind₋(P_K)` (block additivity, and `Λ A(G)` is
positive semidefinite), so the complete family reads exactly the window index on the mixed family
(`mixed_windowIndex`).
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ} {A : ℝ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### Mixed families -/

/-- The weights of a mixed family: untwisted windows `h_i` and windows `g_j` twisted by `χ`. -/
def mixedWeights (h : ι → ℝ → ℝ) (g : κ → ℝ → ℝ) (χ : ℕ → ℝ) (N : ℕ) : ι ⊕ κ → ℕ → ℝ
  | Sum.inl i => horizonWeights (h i) N
  | Sum.inr j => twistedWeights (g j) χ N

/-- The Gram matrix of Weil's form on the blocks of a mixed family. -/
def mixedGram (φ : ℝ → ℝ) (h : ι → ℝ → ℝ) (g : κ → ℝ → ℝ) (χ : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  weilGram Λw fun a => cx (atomicTest N (mixedWeights h g χ N a) (atomDilate φ (c / N)))

theorem atomicTest_weights_add (N : ℕ) (w w' : ℕ → ℝ) (f : ℝ → ℝ) :
    (fun u => atomicTest N w f u + atomicTest N w' f u) = atomicTest N (fun n => w n + w' n) f := by
  funext u
  simp only [atomicTest, add_mul, sum_add_distrib]

theorem atomicTest_weights_sub (N : ℕ) (w w' : ℕ → ℝ) (f : ℝ → ℝ) :
    (fun u => atomicTest N w f u - atomicTest N w' f u) = atomicTest N (fun n => w n - w' n) f := by
  funext u
  simp only [atomicTest, sub_mul, sum_sub_distrib]

theorem contDiff_atomicTest_dilate (hφ : ContDiff ℝ 2 φ) (N : ℕ) (w : ℕ → ℝ) (c : ℝ) :
    ContDiff ℝ 2 (atomicTest N w (atomDilate φ (c / N))) := by
  have hg : ContDiff ℝ 2 (atomDilate φ (c / N)) := by
    unfold atomDilate; exact hφ.comp (contDiff_id.div_const _)
  exact contDiff_atomicTest hg N _

theorem hasCompactSupport_atomicTest_dilate (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (N : ℕ)
    (w : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (hN : 1 ≤ N) :
    HasCompactSupport (atomicTest N w (atomDilate φ (c / N))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : ∀ u, u ∉ Set.Icc 0 (c / N) → atomDilate φ (c / N) u = 0 := fun u hu => by
    unfold atomDilate
    refine hφsupp _ fun hm => hu ?_
    obtain ⟨h0, h1⟩ := hm
    exact ⟨by rw [le_div_iff₀ hw, zero_mul] at h0; exact h0,
      by rw [div_le_one hw] at h1; exact h1⟩
  exact hasCompactSupport_atomicTest hg N _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- The entries of the mixed Gram matrix by polarization. -/
theorem mixedGram_apply (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (h : ι → ℝ → ℝ) (g : κ → ℝ → ℝ) (χ : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (a b : ι ⊕ κ) :
    mixedGram φ h g χ c N a b =
      (((weilQuad (atomicTest N (fun n => mixedWeights h g χ N a n + mixedWeights h g χ N b n)
          (atomDilate φ (c / N))) -
        weilQuad (atomicTest N (fun n => mixedWeights h g χ N a n - mixedWeights h g χ N b n)
          (atomDilate φ (c / N)))) / 4 : ℝ) : ℂ) := by
  unfold mixedGram weilGram
  rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (contDiff_atomicTest_dilate hφ N _ c)
    (hasCompactSupport_atomicTest_dilate hφsupp N _ hc hN) (contDiff_atomicTest_dilate hφ N _ c)
    (hasCompactSupport_atomicTest_dilate hφsupp N _ hc hN), atomicTest_weights_add,
    atomicTest_weights_sub]

/-- The limit of a twisted family: `Λ_χ` times the aliasing Gram matrix. -/
def twistLimitGram (β : ℝ) (Λ : ℝ) (g : κ → ℝ → ℝ) : Matrix κ κ ℂ := (Λ : ℂ) • aliasGram β g

/-- The second-order limit of a mixed family: the window pencil on the untwisted block, `Λ_χ` times
the aliasing Gram matrix on the twisted block, and no coupling. -/
def mixedLimitGram (φ : ℝ → ℝ) (β J K Λ : ℝ) (h : ι → ℝ → ℝ) (g : κ → ℝ → ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ :=
  fromBlocks (pencilGram φ β J K h) 0 0 (twistLimitGram β Λ g)

omit [Fintype κ] [DecidableEq κ] in
theorem twistLimitGram_isHermitian (β Λ : ℝ) (g : κ → ℝ → ℝ) :
    (twistLimitGram β Λ g).IsHermitian := by
  ext i j
  simp only [twistLimitGram, conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, aliasGram]
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
  congr 2
  exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)

/-- **The twisted block has no negative squares**: for `Λ ≥ 0` its negative index is `0`. -/
theorem hermNegIndex_twistLimitGram (β : ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) {g : κ → ℝ → ℝ}
    (hg : ∀ j, ContDiff ℝ 2 (g j)) (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) :
    hermNegIndex (twistLimitGram β Λ g) = 0 := by
  have h0 : hermNegIndex (twistLimitGram β Λ g) ≤ hermNegIndex (0 : Matrix κ κ ℂ) :=
    HeckeKreinToeplitz.hermNegIndex_le_of_hermQuad_le _ _ fun x => by
      unfold twistLimitGram
      rw [HTGeometry.hermQuad_smul]
      have := hermQuad_aliasGram_nonneg β hg hgsupp x
      simp only [hermQuad, zero_mulVec, dotProduct_zero, Complex.zero_re]
      exact mul_nonneg hΛ this
  have hz : hermNegIndex (0 : Matrix κ κ ℂ) = 0 := by
    have := HTGeometry.negIndex_diagonal (n := κ) (fun _ => (0 : ℝ))
    simp only [Complex.ofReal_zero, diagonal_zero] at this
    rw [this]
    simp
  omega

/-- The index of the mixed limit is the index of the untwisted pencil. -/
theorem hermNegIndex_mixedLimitGram {β J K Λ : ℝ} (hΛ : 0 ≤ Λ) {h : ι → ℝ → ℝ}
    (hP : (pencilGram φ β J K h).IsHermitian) {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) :
    hermNegIndex (mixedLimitGram φ β J K Λ h g) = hermNegIndex (pencilGram φ β J K h) := by
  unfold mixedLimitGram
  rw [negIndex_fromBlocks_zero hP (twistLimitGram_isHermitian β Λ g),
    hermNegIndex_twistLimitGram β hΛ hg hgsupp, add_zero]

/-! ### The mixed family converges to the graded limit -/

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- **Matrix convergence for a mixed family.** Along the critical curve, the normalized Gram matrix
of a family of untwisted windows `h_i` and windows `g_j` twisted by a Ramanujan expansion converges
entrywise to the graded limit: the window pencil on the untwisted block, `Λ` times the aliasing
Gram matrix on the twisted block, `Λ = (Σ_m a_m² J_{β+1}(m)) βJ/K`, and no coupling. -/
theorem tendsto_mixedGram (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hA : 0 ≤ A) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) (x y : ι ⊕ κ) :
    Tendsto (fun N : ℕ => ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
      mixedGram φ h g (ramComb S a) (c N) N) x y) atTop
      (𝓝 (mixedLimitGram φ β J K
        ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K) h g
          x y)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  set F : (ℕ → ℕ → ℝ) → ℕ → ℝ := fun w N => (c N)⁻¹ * (weilQuad (atomicTest N (w N)
    (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) with hF
  -- the scaled entries are polarizations of `F`
  have hentry : ∀ x y : ι ⊕ κ, ∀ᶠ N : ℕ in atTop,
      ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
        mixedGram φ h g (ramComb S a) (c N) N) x y =
      (((F (fun N n => mixedWeights h g (ramComb S a) N x n +
          mixedWeights h g (ramComb S a) N y n) N -
        F (fun N n => mixedWeights h g (ramComb S a) N x n -
          mixedWeights h g (ramComb S a) N y n) N) / 4 : ℝ) : ℂ) := fun x y => by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hc0 : 0 < c N := by linarith [hc1 N]
    simp only [Matrix.smul_apply, smul_eq_mul, hF]
    rw [mixedGram_apply hφ hφsupp h g _ hc0 hN, ← Complex.ofReal_mul]
    congr 1
    ring
  have hhwadd : ∀ (u v : ℝ → ℝ) (N : ℕ),
      (fun n => horizonWeights u N n + horizonWeights v N n) =
        horizonWeights (fun y => u y + v y) N := fun u v N => by
    funext n; simp only [horizonWeights]; ring
  have hhwsub : ∀ (u v : ℝ → ℝ) (N : ℕ),
      (fun n => horizonWeights u N n - horizonWeights v N n) =
        horizonWeights (fun y => u y - v y) N := fun u v N => by
    funext n; simp only [horizonWeights]; ring
  have htwadd : ∀ (u v : ℝ → ℝ) (N : ℕ),
      (fun n => twistedWeights u (ramComb S a) N n + twistedWeights v (ramComb S a) N n) =
        twistedWeights (fun y => u y + v y) (ramComb S a) N := fun u v N => by
    funext n; simp only [twistedWeights, horizonWeights]; ring
  have htwsub : ∀ (u v : ℝ → ℝ) (N : ℕ),
      (fun n => twistedWeights u (ramComb S a) N n - twistedWeights v (ramComb S a) N n) =
        twistedWeights (fun y => u y - v y) (ramComb S a) N := fun u v N => by
    funext n; simp only [twistedWeights, horizonWeights]; ring
  have hcase2 : ∀ (i : ι) (j : κ), Tendsto (fun N : ℕ =>
      ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
        mixedGram φ h g (ramComb S a) (c N) N) (Sum.inl i) (Sum.inr j)) atTop
      (𝓝 ((0 : ℝ) : ℂ)) := fun i j => by
    have hcross := cross_layer_vanishes_of_twist hφ hφsupp hφ2 hq hCφ hdecay (hh i) (hg j) hA
      (hsupp i) (hgsupp j) hc1 hcinf hclog (meanZeroTwist_ramComb hS a)
      (exists_ramCombLow_energy_le hφ hφsupp (by linarith : 0 ≤ q) hCφ hdecay (hg j) hA
        (hgsupp j) hS a)
    have hreal := hcross.div_const 4
    rw [zero_div] at hreal
    refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr' ?_
    filter_upwards [hentry (Sum.inl i) (Sum.inr j)] with N hN
    rw [hN]
    simp only [Function.comp_apply, hF, mixedWeights]
  rcases x with i | j <;> rcases y with i' | j'
  · -- the untwisted block
    have hp' := horizon_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk
      ((hh i).add (hh i')) hA (fun y hy => by simp [hsupp i y hy, hsupp i' y hy]) hc1 hK hcrit
    have hm' := horizon_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk
      ((hh i).sub (hh i')) hA (fun y hy => by simp [hsupp i y hy, hsupp i' y hy]) hc1 hK hcrit
    have hreal := (hp'.sub hm').div_const 4
    have hgoal : mixedLimitGram φ β J K
        ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K)
          h g (Sum.inl i) (Sum.inl i') = pencilGram φ β J K h i i' := by
      simp [mixedLimitGram]
    rw [hgoal]
    refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr' ?_
    filter_upwards [hentry (Sum.inl i) (Sum.inl i')] with N hN
    rw [hN]
    simp only [Function.comp_apply, hF, mixedWeights]
    rw [hhwadd (h i) (h i') N, hhwsub (h i) (h i') N]
  · -- untwisted against twisted
    have h0 : mixedLimitGram φ β J K
        ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K)
          h g (Sum.inl i) (Sum.inr j') = ((0 : ℝ) : ℂ) := by
      simp [mixedLimitGram]
    rw [h0]
    exact hcase2 i j'
  · -- twisted against untwisted, by Hermitian symmetry
    have h0 : mixedLimitGram φ β J K
        ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K)
          h g (Sum.inr j) (Sum.inl i') = star ((0 : ℝ) : ℂ) := by
      simp [mixedLimitGram]
    rw [h0]
    have h2 := (continuous_star.tendsto _).comp (hcase2 i' j)
    refine h2.congr fun N => ?_
    have hH : (mixedGram φ h g (ramComb S a) (c N) N).IsHermitian := weilGram_isHermitian _ _
    have hG := hH.apply (Sum.inr j) (Sum.inl i')
    simp only [Function.comp_apply, Matrix.smul_apply, smul_eq_mul]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, hG]
  · -- the twisted block
    have hp' := ramComb_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk
      ((hg j).add (hg j')) hA (fun y hy => by simp [hgsupp j y hy, hgsupp j' y hy]) hc1 hK hcrit
      hS a
    have hm' := ramComb_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk
      ((hg j).sub (hg j')) hA (fun y hy => by simp [hgsupp j y hy, hgsupp j' y hy]) hc1 hK hcrit
      hS a
    have hreal := (hp'.sub hm').div_const 4
    set Λ := (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K
      with hΛ
    have hval : (Λ * (∫ y, Real.exp (-((β + 1) * y)) * halfWeight (fun y => g j y + g j' y) y ^ 2) -
        Λ * ∫ y, Real.exp (-((β + 1) * y)) * halfWeight (fun y => g j y - g j' y) y ^ 2) / 4 =
        Λ * ∫ y, Real.exp (-((β + 1) * y)) * (halfWeight (g j) y * halfWeight (g j') y) := by
      have hpol := integral_polarize_of_window (A := A)
        (w := fun y => Real.exp (-((β + 1) * y))) (by fun_prop)
        (contDiff_halfWeight (hg j)).continuous (contDiff_halfWeight (hg j')).continuous
        (halfWeight_eq_zero_of_window (hgsupp j)) (halfWeight_eq_zero_of_window (hgsupp j'))
      rw [halfWeight_add, halfWeight_sub]
      beta_reduce at hpol ⊢
      rw [← hpol]
      ring
    rw [hval] at hreal
    have hgoal : mixedLimitGram φ β J K Λ h g (Sum.inr j) (Sum.inr j') =
        ((Λ * ∫ y, Real.exp (-((β + 1) * y)) * (halfWeight (g j) y * halfWeight (g j') y) : ℝ) :
          ℂ) := by
      simp only [mixedLimitGram, fromBlocks_apply₂₂, twistLimitGram, Matrix.smul_apply,
        smul_eq_mul, aliasGram]
      push_cast
      ring
    rw [hgoal]
    refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr' ?_
    filter_upwards [hentry (Sum.inr j) (Sum.inr j')] with N hN
    rw [hN]
    simp only [Function.comp_apply, hF, mixedWeights]
    rw [htwadd (g j) (g j') N, htwsub (g j) (g j') N]

/-! ### The twisted directions carry no negative squares -/

theorem jordanTotient_nonneg_of_nonneg {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    0 ≤ ArithmeticDegenerationTheory.jordanTotient k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ArithmeticDegenerationTheory.jordanTotient]
  have e : ArithmeticDegenerationTheory.jordanTotient k n = ArithmeticPositiveDuality.jordan k n := by
    rw [ArithmeticDegenerationTheory.jordanTotient, ArithmeticPositiveDuality.jordan,
      ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b =>
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) a *
          ArithmeticPositiveDuality.powFun k b)]
    refine sum_congr rfl fun d hd => ?_
    rw [ArithmeticPositiveDuality.powFun_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)),
      ArithmeticFunction.intCoe_apply]
  rw [e]
  exact ArithmeticPositiveDuality.jordan_nonneg hk n

/-- **The twisted directions carry no negative squares.** For a family of untwisted windows `h_i`
and windows `g_j` twisted by a Ramanujan expansion `χ = Σ_{m ∈ S} a_m c_m` (`m ≥ 2`), along the
critical curve the normalized Gram matrices of the complete family converge to the graded limit,
whose negative index is exactly the window index `ind₋(P_K)` of the untwisted windows; hence the
complete family reads `ind₋(P_K)` on the mixed family: eventually `ind₋(P_K) ≤ ind₋(G_N)`. Adding
twisted windows never adds a negative square at second order. -/
theorem mixed_windowIndex (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j))
    (hA : 0 ≤ A) (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) :
    hermNegIndex (mixedLimitGram φ β J K
        ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K)
          h g) = hermNegIndex (pencilGram φ β J K h) ∧
      ∀ᶠ N : ℕ in atTop, hermNegIndex (pencilGram φ β J K h) ≤
        hermNegIndex (mixedGram φ h g (ramComb S a) (c N) N) := by
  have hJ0 : 0 ≤ J := by
    refine ge_of_tendsto hbulk ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    exact mul_nonneg (Real.rpow_nonneg hs.le _)
      (completedShellEnergy_nonneg hφ hφsupp hφ2 hs)
  have hΛ : 0 ≤ (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β *
      J / K := by
    have : 0 ≤ ∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m :=
      Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _)
        (jordanTotient_nonneg_of_nonneg (by linarith) m)
    positivity
  have hP := pencilGram_isHermitian hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit
  have hidx := hermNegIndex_mixedLimitGram (φ := φ) (J := J) (K := K) hΛ hP hg hgsupp
  refine ⟨hidx, ?_⟩
  have hherm : (mixedLimitGram φ β J K
      ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K)
        h g).IsHermitian :=
    IsHermitian.fromBlocks hP (by simp) (twistLimitGram_isHermitian β _ g)
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex hherm
    (tendsto_mixedGram hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hg hA hsupp hgsupp hc1 hK hcrit hS a)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  rw [hermNegIndex_ofReal_smul hs, hidx] at hN
  exact hN

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
