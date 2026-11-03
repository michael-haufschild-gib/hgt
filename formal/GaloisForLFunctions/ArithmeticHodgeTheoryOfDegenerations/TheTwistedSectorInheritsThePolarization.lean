import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedDirectionsCarryNoNegativeSquares
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndexCountsTheJumpMultiples

/-!
# The twisted sector inherits the polarization of the count

Mechanism B of the field (a polarized second-order term is inherited by the nearby fibres) holds
unconditionally on the twisted sector. For an independent family of windows `g_j` twisted by a
Ramanujan expansion `χ = Σ_{m ∈ S} a_m c_m`, the second-order limit of the complete family is
`Λ A(G)`, `Λ = (Σ_m a_m² J_{β+1}(m)) βJ/K`, positive definite when `Λ > 0` (the count polarizes it,
`aliasGram_posDef`). Positive definiteness is an open condition, so along the critical curve the
Gram matrix of the complete family on the twisted family is eventually positive definite
(`twisted_sector_inherits`, `twisted_sector_inherits_exact` for the tilted spline).
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ : ℝ → ℝ} {A : ℝ} {κ : Type*} [Fintype κ] [DecidableEq κ]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-! ### Positive definiteness is inherited by limits -/

/-- **Positive definiteness is open**: if Hermitian matrices `H_n` converge entrywise to `H₀` whose
form is positive on nonzero vectors, then eventually every `H_n` has positive form on nonzero
vectors (lower semicontinuity of the positive index). -/
theorem eventually_hermQuad_pos_of_tendsto {H : ℕ → Matrix κ κ ℂ} {H₀ : Matrix κ κ ℂ}
    (hH₀ : H₀.IsHermitian) (hpos : ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad H₀ x)
    (hH : ∀ a b, Tendsto (fun n => H n a b) atTop (𝓝 (H₀ a b))) :
    ∀ᶠ n in atTop, ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (H n) x := by
  have hcard : Fintype.card κ ≤ hermPosIndex H₀ := by
    have := finrank_le_posIndex (H := H₀) (W := ⊤) fun x _ hx => hpos x hx
    rwa [finrank_top, Module.finrank_fintype_fun_eq_card] at this
  have hneg : (-H₀).IsHermitian := hH₀.neg
  have hlim : ∀ a b, Tendsto (fun n => (-H n) a b) atTop (𝓝 ((-H₀) a b)) := fun a b => by
    simpa using (hH a b).neg
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex hneg hlim
  filter_upwards [hev] with n hn
  have hn' : Fintype.card κ ≤ hermPosIndex (H n) := by
    have e1 : hermNegIndex (-H₀) = hermPosIndex H₀ := by rw [hermNegIndex, neg_neg]
    have e2 : hermNegIndex (-H n) = hermPosIndex (H n) := by rw [hermNegIndex, neg_neg]
    rw [e1, e2] at hn
    omega
  obtain ⟨W, hWdim, hWpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (H n)
  have hle : hermPosIndex (H n) ≤ Fintype.card κ := by
    have := Submodule.finrank_le W
    rw [Module.finrank_fintype_fun_eq_card] at this
    omega
  have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [Module.finrank_fintype_fun_eq_card]; omega)
  intro x hx
  exact hWpos x (by rw [htop]; trivial) hx

/-! ### The twisted Gram matrix -/

/-- The Gram matrix of Weil's form on a family of windows twisted by `χ`. -/
def twistGram (φ : ℝ → ℝ) (g : κ → ℝ → ℝ) (χ : ℕ → ℝ) (c : ℝ) (N : ℕ) : Matrix κ κ ℂ :=
  weilGram Λw fun j => cx (atomicTest N (twistedWeights (g j) χ N) (atomDilate φ (c / N)))

omit [Fintype κ] [DecidableEq κ] in
theorem twistGram_apply (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (g : κ → ℝ → ℝ) (χ : ℕ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (j j' : κ) :
    twistGram φ g χ c N j j' =
      (((weilQuad (atomicTest N (twistedWeights (fun y => g j y + g j' y) χ N)
          (atomDilate φ (c / N))) -
        weilQuad (atomicTest N (twistedWeights (fun y => g j y - g j' y) χ N)
          (atomDilate φ (c / N)))) / 4 : ℝ) : ℂ) := by
  unfold twistGram weilGram
  rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (contDiff_atomicTest_dilate hφ N _ c)
    (hasCompactSupport_atomicTest_dilate hφsupp N _ hc hN) (contDiff_atomicTest_dilate hφ N _ c)
    (hasCompactSupport_atomicTest_dilate hφsupp N _ hc hN), atomicTest_weights_add,
    atomicTest_weights_sub]
  have e1 : (fun n => twistedWeights (g j) χ N n + twistedWeights (g j') χ N n) =
      twistedWeights (fun y => g j y + g j' y) χ N := by
    funext n; simp only [twistedWeights, horizonWeights]; ring
  have e2 : (fun n => twistedWeights (g j) χ N n - twistedWeights (g j') χ N n) =
      twistedWeights (fun y => g j y - g j' y) χ N := by
    funext n; simp only [twistedWeights, horizonWeights]; ring
  rw [e1, e2]

omit [Fintype κ] [DecidableEq κ] in
/-- **Matrix convergence on the twisted sector**: `(c⁻¹/∫g²) G_N → Λ A(G)` entrywise. -/
theorem tendsto_twistGram (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j)) (hA : 0 ≤ A)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) (j j' : κ) :
    Tendsto (fun N : ℕ => ((((c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 : ℝ) : ℂ) •
      twistGram φ g (ramComb S a) (c N) N) j j') atTop
      (𝓝 (twistLimitGram β
        ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K) g
          j j')) := by
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
  have hgoal : twistLimitGram β Λ g j j' =
      ((Λ * ∫ y, Real.exp (-((β + 1) * y)) * (halfWeight (g j) y * halfWeight (g j') y) : ℝ) :
        ℂ) := by
    simp only [twistLimitGram, Matrix.smul_apply, smul_eq_mul, aliasGram]
    push_cast
    ring
  rw [hgoal]
  refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hc0 : 0 < c N := by linarith [hc1 N]
  simp only [Function.comp_apply, Matrix.smul_apply, smul_eq_mul]
  rw [twistGram_apply hφ hφsupp g _ hc0 hN, ← Complex.ofReal_mul]
  congr 1
  ring

/-! ### Inheritance -/

/-- **The twisted sector inherits the polarization of the count.** For a linearly independent family
of windows twisted by a Ramanujan expansion with `Λ = (Σ_m a_m² J_{β+1}(m)) βJ/K > 0`, along the
critical curve the Gram matrix of Weil's form of the complete family on the family is eventually
positive definite. -/
theorem twisted_sector_inherits (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j)) (hA : 0 ≤ A)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hlin : LinearIndependent ℝ g)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ)
    (hΛ : 0 < (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J /
      K) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 →
      0 < hermQuad (twistGram φ g (ramComb S a) (c N) N) x := by
  set Λ := (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K
    with hΛdef
  have hpos : ∀ x : κ → ℂ, x ≠ 0 → 0 < hermQuad (twistLimitGram β Λ g) x := fun x hx => by
    unfold twistLimitGram
    rw [HTGeometry.hermQuad_smul]
    have hA' := aliasGram_posDef β hg hgsupp hlin
    have : 0 < hermQuad (aliasGram β g) x := by
      have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp hA').2 hx
      simpa [hermQuad] using (Complex.lt_def.mp h1).1
    exact mul_pos hΛ this
  have hev := eventually_hermQuad_pos_of_tendsto (twistLimitGram_isHermitian β Λ g) hpos
    (tendsto_twistGram hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hg hA hgsupp hc1 hK hcrit hS a)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  have := hN x hx
  rw [HTGeometry.hermQuad_smul] at this
  exact pos_of_mul_pos_right this hs.le

/-- **Inheritance for the tilted spline.** Along `c⁸/log N → K`, the Gram matrix of the complete
family on a linearly independent family of windows twisted by a nonzero Ramanujan expansion
(`a_m ≠ 0` for some `m ∈ S`) is eventually positive definite. -/
theorem twisted_sector_inherits_exact {g : κ → ℝ → ℝ} (hg : ∀ j, ContDiff ℝ 2 (g j)) (hA : 0 ≤ A)
    (hgsupp : ∀ j y, y ∉ Set.Icc (-A) 0 → g j y = 0) (hlin : LinearIndependent ℝ g)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) (ha : ∃ m ∈ S, a m ≠ 0) :
    ∀ᶠ N : ℕ in atTop, ∀ x : κ → ℂ, x ≠ 0 →
      0 < hermQuad (twistGram tiltedUnitSpline g (ramComb S a) (c N) N) x := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsum : 0 < ∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient ((7 : ℝ) + 1) m := by
    obtain ⟨m₀, hm₀, ham₀⟩ := ha
    have h8 : ((7 : ℝ) + 1) = 8 := by norm_num
    rw [h8]
    have hnn : ∀ m ∈ S, 0 ≤ a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient 8 m := fun m hm =>
      mul_nonneg (sq_nonneg _)
        (ArithmeticDegenerationTheory.jordanTotient_eight_pos (by linarith [hS m hm])).le
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn hm₀)
    exact mul_pos (by positivity)
      (ArithmeticDegenerationTheory.jordanTotient_eight_pos (by linarith [hS m₀ hm₀]))
  exact twisted_sector_inherits contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC tiltedUnitSpline_decay (β := 7)
    (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted hg hA hgsupp hlin hc1 hK
    hcrit' hS a (by have := tiltedJordanOne_pos; positivity)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
