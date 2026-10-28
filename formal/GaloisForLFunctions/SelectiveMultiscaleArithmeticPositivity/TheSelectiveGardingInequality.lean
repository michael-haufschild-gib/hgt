import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneSeparatesTheFullWeilForms

/-!
# The selective Gårding inequality

The prime defect `D_N(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²` is a sum of squares of linear forms
that all vanish on the pole vector `u_n = n^{−1/2}`. So it reads only the component of `x`
orthogonal to the pole, and the uniform Poincaré gap of `ζ` on the harmonic hyperplane
(RenormalizedArithmeticPotentialTheory) pays that component for *every* `x`.

* **The pole projection** (`poleProj`, `harmonicSum_poleProj`, `sum_sq_poleProj`): removing
  `(ℓ(x)/H_N) u`, `ℓ(x) = Σ x_n/√n`, `H_N = Σ 1/n`, lands on the hyperplane and leaves mass
  `|x|² − ℓ(x)²/H_N`.
* **The defect ignores the pole** (`poleDefect_poleProj`): `D_N(x − c u) = D_N(x)`.
* **The selective Poincaré inequality** (`exists_poleDefect_ge_offPole`): one `G > 0` gives
  `D_N(x) ≥ G(|x|² − ℓ(x)²/H_N)` for all `N ≥ 1` and all `x`.
* **The selective Gårding inequality** (`exists_weilQuad_atomicTest_ge_selective`): eventually in
  `N`, every narrow atomic test has
  `W(f_x) ≥ (φ₀ + c₀G)‖f_x‖² − c₀G ‖g‖² ℓ(x)²/H_N + 2A(f_x)B(f_x)`.
  The gap acts on the whole test except its pole component, which is read by the pole term.

On the Liouville twin no positive `G` can play this role (`not_liouville_hasHyperplaneGap`): the
reserve `c₀G` is selective.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticLorentzianGeometry
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The harmonic (pole) coordinate `ℓ(x) = Σ_{n ≤ N} x_n/√n`. -/
def harmonicSum (N : ℕ) (x : ℕ → ℝ) : ℝ := ∑ n ∈ Icc 1 N, x n / Real.sqrt n

/-- The harmonic mass `H_N = Σ_{n ≤ N} 1/n = |u|²`. -/
def harmonicMass (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, 1 / (n : ℝ)

theorem harmonicMass_pos {N : ℕ} (hN : 1 ≤ N) : 0 < harmonicMass N :=
  sum_pos (fun n hn => by have := (mem_Icc.mp hn).1; positivity) ⟨1, mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- The projection of `x` onto the harmonic hyperplane along the pole vector `u_n = n^{−1/2}`. -/
def poleProj (N : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  x n - harmonicSum N x / harmonicMass N / Real.sqrt n

theorem sqrt_inv_sq {n : ℕ} (hn : 1 ≤ n) : 1 / Real.sqrt n / Real.sqrt n = 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_div, Real.mul_self_sqrt hn0.le]

/-- **The projection lands on the hyperplane.** -/
theorem harmonicSum_poleProj {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    harmonicSum N (poleProj N x) = 0 := by
  have hH := (harmonicMass_pos hN).ne'
  set c := harmonicSum N x / harmonicMass N
  have h : harmonicSum N (poleProj N x) = harmonicSum N x - c * harmonicMass N := by
    rw [harmonicSum, harmonicSum, harmonicMass, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun n hn => ?_
    rw [poleProj, sub_div, ← sqrt_inv_sq (mem_Icc.mp hn).1]
    ring
  rw [h]
  simp only [c]
  field_simp
  ring

/-- **The projection removes exactly the pole mass**: `|x_⊥|² = |x|² − ℓ(x)²/H_N`. -/
theorem sum_sq_poleProj {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, poleProj N x n ^ 2 =
      ∑ n ∈ Icc 1 N, x n ^ 2 - harmonicSum N x ^ 2 / harmonicMass N := by
  have hH := (harmonicMass_pos hN).ne'
  set c := harmonicSum N x / harmonicMass N
  have hexp : ∀ n ∈ Icc 1 N, poleProj N x n ^ 2 =
      x n ^ 2 - 2 * c * (x n / Real.sqrt n) + c ^ 2 * (1 / (n : ℝ)) := by
    intro n hn
    rw [poleProj, ← sqrt_inv_sq (mem_Icc.mp hn).1]
    ring
  rw [sum_congr rfl hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  change ∑ n ∈ Icc 1 N, x n ^ 2 - 2 * c * harmonicSum N x + c ^ 2 * harmonicMass N = _
  simp only [c]
  field_simp
  ring

/-- **The defect ignores the pole direction**: `D_N(x − c u) = D_N(x)`. -/
theorem poleDefect_sub_pole (N : ℕ) (x : ℕ → ℝ) (c : ℝ) :
    poleDefect N (fun n => x n - c / Real.sqrt n) = poleDefect N x := by
  unfold poleDefect
  refine sum_congr rfl fun m hm => sum_congr rfl fun t ht => ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
  have hsm := Real.sqrt_pos.mpr hm0
  have hst := Real.sqrt_pos.mpr ht0
  congr 1
  simp only [Nat.cast_mul, Real.sqrt_mul hm0.le]
  field_simp
  ring

theorem poleDefect_poleProj (N : ℕ) (x : ℕ → ℝ) :
    poleDefect N (poleProj N x) = poleDefect N x :=
  poleDefect_sub_pole N x _

/-- **The selective Poincaré inequality**: one `G > 0` gives `D_N(x) ≥ G(|x|² − ℓ(x)²/H_N)` for
every `N ≥ 1` and every `x`. -/
theorem exists_poleDefect_ge_offPole : ∃ G : ℝ, 0 < G ∧ ∀ N : ℕ, 1 ≤ N → ∀ x : ℕ → ℝ,
    G * (∑ n ∈ Icc 1 N, x n ^ 2 - harmonicSum N x ^ 2 / harmonicMass N) ≤ poleDefect N x := by
  obtain ⟨G, hG, hgap⟩ := exists_poleDefect_ge
  refine ⟨G, hG, fun N hN x => ?_⟩
  have h := hgap N (poleProj N x) (harmonicSum_poleProj hN x)
  rwa [sum_sq_poleProj hN, poleDefect_poleProj] at h

/-- **The selective Gårding inequality.** There is `G > 0` such that for every admissible profile
and slack, eventually in `N`, every atomic test at width `w ≤ δ_N/2` with nonnegative retained
defect fraction satisfies
`W(f_x) ≥ (φ₀ + c₀G)‖f_x‖² − c₀G ‖g‖² ℓ(x)²/H_N + 2A(f_x)B(f_x)`. -/
theorem exists_weilQuad_atomicTest_ge_selective :
    ∃ G : ℝ, 0 < G ∧ ∀ {φ : ℝ → ℝ}, ContDiff ℝ 2 φ → (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) →
      0 < (∫ u, φ u ^ 2) → ∀ {K : ℝ}, (∀ u v, |φ u - φ v| ≤ K * |u - v|) →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
        w * N ≤ markovOverlapBound → 0 ≤ defectFractionRetained ε w N → ∀ x : ℕ → ℝ,
          (markovFinitePart φ ε w N + defectFractionRetained ε w N * G) *
              (∫ u, atomicTest N x (atomDilate φ w) u ^ 2) -
            defectFractionRetained ε w N * G * (∫ u, atomDilate φ w u ^ 2) *
              (harmonicSum N x ^ 2 / harmonicMass N) +
            2 * (∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (-(u / 2))) *
              (∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (u / 2)) ≤
          weilQuad (atomicTest N x (atomDilate φ w)) := by
  obtain ⟨G, hG, hgap⟩ := exists_poleDefect_ge_offPole
  refine ⟨G, hG, fun {φ} hφ hφsupp hφ0 {K} hK {ε} hε hε1 => ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_ge_defect hφ hφsupp hφ0 hK hε hε1
  refine ⟨max N₀ 1, fun N hN w hw0 hw hwN hc₀ x => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hM := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw hwN x
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN1]
  rw [weilQuad_eq_markov_add_pole (contDiff_atomicTest hgc2 N x)
    (hasCompactSupport_atomicTest hgsupp N x)]
  rw [integral_atomicTest_sq hgc2 hgc hgsupp hw' x] at hM ⊢
  unfold markovFinitePart defectFractionRetained at *
  set A := ∫ u, atomDilate φ w u ^ 2
  set c₀ := 1 - ε - 32 * Real.exp 2 * (w * N)
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have h1 : A * c₀ * (G * (∑ n ∈ Icc 1 N, x n ^ 2 - harmonicSum N x ^ 2 / harmonicMass N)) ≤
      A * c₀ * poleDefect N x :=
    mul_le_mul_of_nonneg_left (hgap N hN1 x) (mul_nonneg hA hc₀)
  nlinarith

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
