import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderOfACharacterWindowReadsAnLValue

/-!
# The character windows are graded by parity

Windows of different conductors decouple at second order (Ramanujan sums are orthogonal at every
offset). Within one modulus the characters do not decouple in general: the second-order form on
the windows twisted by real parts of primitive characters is a form in `L`-values. This file
computes it.

* **Polarization of the second order** (`cross_layer_criticalCurve`): for mean-zero twists `χ₁, χ₂`
  of a common period `M`, the polarized form `(Q(T₁ + T₂) − Q(T₁ − T₂))/4` of the two twisted
  windows has second-order coefficient `βA_φ/(K∫φ²)` times the **cross-spectral sum**
  `2M^s Σ_j Re(S_j(χ₁) S̄_j(χ₂))/M² j^{−s}`, `s = β + 1`.
* **The cross spectrum of two characters** (`crossPower_charTwist`): for `ψ₁, ψ₂` primitive mod `q`
  with signs `ε_i = ψ_i(−1)`,

  `Re(S_k S̄'_k)/q² = (1 + ε₁ε₂)/(4q²) · Re(c₁c̄₂τ₁τ̄₂ ψ̄₁(k)ψ₂(k) + c₁c₂ψ̄₂(−1)τ₁τ₂ ψ̄₁(k)ψ̄₂(k))`.

* **Parity grading** (`crossPower_charTwist_eq_zero`, `cross_layer_charTwist_opposite_parity`):
  windows twisted by characters of opposite parity are orthogonal at second order.
* **Same parity couples through `L`-values** (`crossSpectralSum_charTwist`): the cross-spectral sum is
  `(1 + ε₁ε₂) q^s/(2q²) · Re(c₁c̄₂τ₁τ̄₂ L(s, ψ̄₁ψ₂) + c₁c₂ψ̄₂(−1)τ₁τ₂ L(s, ψ̄₁ψ̄₂))`.

So the character span carries a grading by parity, and on each parity class the second order is the
Hermitian form of the `L`-values of the products `ψ̄₁ψ₂` and `ψ̄₁ψ̄₂`; for `ψ₁ = ψ₂` it is the count
plus `L(s, ψ̄²)` (`twistSpectralSum_charTwist`).
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### Polarization of the second order -/

/-- The cross power `Re(S_j(χ₁) S̄_j(χ₂))/M²` of two twists. -/
def crossPower (χ₁ χ₂ : ℕ → ℝ) (M j : ℕ) : ℝ :=
  (twistCoeff χ₁ M j * conj (twistCoeff χ₂ M j)).re / (M : ℝ) ^ 2

theorem twistCoeff_add (χ₁ χ₂ : ℕ → ℝ) (M k : ℕ) :
    twistCoeff (fun n => χ₁ n + χ₂ n) M k = twistCoeff χ₁ M k + twistCoeff χ₂ M k := by
  unfold twistCoeff
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast; ring

theorem twistCoeff_sub (χ₁ χ₂ : ℕ → ℝ) (M k : ℕ) :
    twistCoeff (fun n => χ₁ n - χ₂ n) M k = twistCoeff χ₁ M k - twistCoeff χ₂ M k := by
  unfold twistCoeff
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast; ring

/-- `|χ̂₁ + χ̂₂|² − |χ̂₁ − χ̂₂|² = 4 Re(χ̂₁ \overline{χ̂₂})`. -/
theorem twistPower_add_sub_twistPower_sub (χ₁ χ₂ : ℕ → ℝ) (M k : ℕ) :
    twistPower (fun n => χ₁ n + χ₂ n) M k - twistPower (fun n => χ₁ n - χ₂ n) M k =
      4 * crossPower χ₁ χ₂ M k := by
  unfold twistPower crossPower
  rw [twistCoeff_add, twistCoeff_sub, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add,
    Complex.normSq_sub]
  ring

theorem MeanZeroTwist.add {χ₁ χ₂ : ℕ → ℝ} {M : ℕ} (h₁ : MeanZeroTwist χ₁ M)
    (h₂ : MeanZeroTwist χ₂ M) : MeanZeroTwist (fun n => χ₁ n + χ₂ n) M :=
  ⟨h₁.pos, fun n => by rw [h₁.periodic, h₂.periodic], by
    rw [Finset.sum_add_distrib, h₁.mean_zero, h₂.mean_zero, add_zero]⟩

theorem MeanZeroTwist.sub {χ₁ χ₂ : ℕ → ℝ} {M : ℕ} (h₁ : MeanZeroTwist χ₁ M)
    (h₂ : MeanZeroTwist χ₂ M) : MeanZeroTwist (fun n => χ₁ n - χ₂ n) M :=
  ⟨h₁.pos, fun n => by rw [h₁.periodic, h₂.periodic], by
    rw [Finset.sum_sub_distrib, h₁.mean_zero, h₂.mean_zero, sub_zero]⟩

/-- The power spectrum of a periodic twist is bounded, so its Dirichlet series converges. -/
theorem summable_twistPower_mul_rpow (χ : ℕ → ℝ) {M : ℕ} (hM : 0 < M) {s : ℝ} (hs : 1 < s) :
    Summable fun j : ℕ => twistPower χ M j * (j : ℝ) ^ (-s) := by
  have hgs : Summable fun j : ℕ => (j : ℝ) ^ (-s) := Real.summable_nat_rpow.mpr (by linarith)
  set B := ∑ r ∈ range M, twistPower χ M r with hB
  have hPb : ∀ j, twistPower χ M j ≤ B := fun j => by
    rw [twistPower_mod χ hM j]
    exact single_le_sum (fun r _ => twistPower_nonneg χ M r) (mem_range.mpr (Nat.mod_lt _ hM))
  exact (hgs.mul_left B).of_nonneg_of_le
    (fun j => mul_nonneg (twistPower_nonneg _ _ _) (by positivity))
    (fun j => mul_le_mul_of_nonneg_right (hPb j) (by positivity))

/-- The polarized Weil form `(Q(f + g) − Q(f − g))/4`. -/
def weilCross (f g : ℝ → ℝ) : ℝ := (weilQuad (fun u => f u + g u) - weilQuad (fun u => f u - g u)) / 4

theorem atomicTest_twistedWeights_add (χ₁ χ₂ : ℕ → ℝ) (N : ℕ) (g : ℝ → ℝ) :
    atomicTest N (twistedWeights h (fun n => χ₁ n + χ₂ n) N) g =
      fun u => atomicTest N (twistedWeights h χ₁ N) g u + atomicTest N (twistedWeights h χ₂ N) g u := by
  funext u
  simp only [atomicTest, twistedWeights, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem atomicTest_twistedWeights_sub (χ₁ χ₂ : ℕ → ℝ) (N : ℕ) (g : ℝ → ℝ) :
    atomicTest N (twistedWeights h (fun n => χ₁ n - χ₂ n) N) g =
      fun u => atomicTest N (twistedWeights h χ₁ N) g u - atomicTest N (twistedWeights h χ₂ N) g u := by
  funext u
  simp only [atomicTest, twistedWeights, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Polarization of the second order.** For mean-zero twists of a common period, the polarized
form of the two twisted windows has second-order coefficient `βA_φ/(K∫φ²)` times the
cross-spectral sum `2M^{β+1} Σ_j Re(S_j S̄'_j)/M² j^{−(β+1)}`. -/
theorem cross_layer_criticalCurve (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {χ₁ χ₂ : ℕ → ℝ} {M : ℕ} (h₁ : MeanZeroTwist χ₁ M) (h₂ : MeanZeroTwist χ₂ M) :
    Tendsto (fun N : ℕ => (c N)⁻¹ *
        (weilCross (atomicTest N (twistedWeights h χ₁ N) (atomDilate φ (c N / N)))
          (atomicTest N (twistedWeights h χ₂ N) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (β * Aφ / (K * ∫ u, φ u ^ 2) *
        (2 * (M : ℝ) ^ (β + 1) * ∑' j : ℕ, crossPower χ₁ χ₂ M j * (j : ℝ) ^ (-(β + 1))) *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  have hp' := periodicTwist_layer_criticalCurve_dirichlet hφ hφsupp hφ2 hp hCφ hdecay hβ hT hh hA
    hsupp hc1 hK hcrit (h₁.add h₂)
  have hm' := periodicTwist_layer_criticalCurve_dirichlet hφ hφsupp hφ2 hp hCφ hdecay hβ hT hh hA
    hsupp hc1 hK hcrit (h₁.sub h₂)
  simp_rw [atomicTest_twistedWeights_add, atomicTest_twistedWeights_sub] at hp' hm'
  have hlim := (hp'.sub hm').div_const 4
  have hs : 1 < β + 1 := by linarith
  have hsum : ∑' j : ℕ, crossPower χ₁ χ₂ M j * (j : ℝ) ^ (-(β + 1)) =
      (∑' j : ℕ, twistPower (fun n => χ₁ n + χ₂ n) M j * (j : ℝ) ^ (-(β + 1)) -
        ∑' j : ℕ, twistPower (fun n => χ₁ n - χ₂ n) M j * (j : ℝ) ^ (-(β + 1))) / 4 := by
    rw [← Summable.tsum_sub (summable_twistPower_mul_rpow _ h₁.pos hs)
      (summable_twistPower_mul_rpow _ h₁.pos hs), eq_div_iff (by norm_num : (4 : ℝ) ≠ 0),
      ← tsum_mul_right]
    refine tsum_congr fun j => ?_
    rw [← sub_mul, twistPower_add_sub_twistPower_sub]
    ring
  rw [hsum]
  convert hlim using 1
  · funext N
    unfold weilCross
    ring
  · congr 1
    ring

/-! ### Two characters -/

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- A Dirichlet character is a sign at `−1`. -/
theorem charSign_eq (ψ : DirichletCharacter ℂ q) : ψ (-1) = 1 ∨ ψ (-1) = -1 :=
  (DirichletCharacter.even_or_odd ψ).imp id id

/-- **The cross spectrum of two character twists.** -/
theorem crossPower_charTwist (c₁ c₂ : ℂ) {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hψ₁ : ψ₁.IsPrimitive) (hψ₂ : ψ₂.IsPrimitive) (k : ℕ) :
    crossPower (charTwist c₁ ψ₁) (charTwist c₂ ψ₂) q k =
      (1 + (ψ₁ (-1) * ψ₂ (-1)).re) / (4 * (q : ℝ) ^ 2) *
        (c₁ * conj c₂ * gaussSum ψ₁ (RHTower.stdChar q) * conj (gaussSum ψ₂ (RHTower.stdChar q)) *
            (conj (ψ₁ (k : ZMod q)) * ψ₂ (k : ZMod q)) +
          c₁ * c₂ * conj (ψ₂ (-1)) * gaussSum ψ₁ (RHTower.stdChar q) *
            gaussSum ψ₂ (RHTower.stdChar q) *
            (conj (ψ₁ (k : ZMod q)) * conj (ψ₂ (k : ZMod q)))).re := by
  unfold crossPower
  rw [twistCoeff_charTwist c₁ hψ₁, twistCoeff_charTwist c₂ hψ₂]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rcases charSign_eq ψ₁ with e₁ | e₁ <;> rcases charSign_eq ψ₂ with e₂ | e₂ <;>
  · rw [e₁, e₂]
    apply Complex.ofReal_injective
    push_cast
    simp only [Complex.re_eq_add_conj, map_add, map_mul, map_div₀, map_neg, map_one,
      Complex.conj_conj, map_ofNat]
    field_simp
    ring_nf

/-- **Parity grading**: characters of opposite parity have zero cross spectrum. -/
theorem crossPower_charTwist_eq_zero (c₁ c₂ : ℂ) {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hψ₁ : ψ₁.IsPrimitive) (hψ₂ : ψ₂.IsPrimitive) (hpar : ψ₁ (-1) = -ψ₂ (-1)) (k : ℕ) :
    crossPower (charTwist c₁ ψ₁) (charTwist c₂ ψ₂) q k = 0 := by
  rw [crossPower_charTwist c₁ c₂ hψ₁ hψ₂ k, hpar]
  have : (1 + (-ψ₂ (-1) * ψ₂ (-1)).re) = 0 := by
    rcases charSign_eq ψ₂ with e | e <;> rw [e] <;> norm_num
  rw [this, zero_div, zero_mul]

/-- **Opposite parity decouples at second order**: the polarized form of windows twisted by
`Re(c₁ψ₁)` and `Re(c₂ψ₂)`, `ψ₁(−1) = −ψ₂(−1)`, has vanishing second-order term. -/
theorem cross_layer_charTwist_opposite_parity (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    (c₁ c₂ : ℂ) {ψ₁ ψ₂ : DirichletCharacter ℂ q} (hψ₁ : ψ₁.IsPrimitive) (hψ₂ : ψ₂.IsPrimitive)
    (hq : 1 < q) (hpar : ψ₁ (-1) = -ψ₂ (-1)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ *
        (weilCross (atomicTest N (twistedWeights h (charTwist c₁ ψ₁) N) (atomDilate φ (c N / N)))
          (atomicTest N (twistedWeights h (charTwist c₂ ψ₂) N) (atomDilate φ (c N / N))) /
          ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop (𝓝 0) := by
  have h := cross_layer_criticalCurve hφ hφsupp hφ2 hp hCφ hdecay hβ hT hh hA hsupp hc1 hK hcrit
    (meanZeroTwist_charTwist c₁ (ne_one_of_isPrimitive hψ₁ hq))
    (meanZeroTwist_charTwist c₂ (ne_one_of_isPrimitive hψ₂ hq))
  simp_rw [crossPower_charTwist_eq_zero c₁ c₂ hψ₁ hψ₂ hpar, zero_mul, tsum_zero, mul_zero,
    zero_mul] at h
  exact h

/-- The Dirichlet series `Σ_j f(j) j^{−s}` of a coefficient sequence. -/
def dirichletL (f : ℕ → ℂ) (s : ℝ) : ℂ := ∑' j : ℕ, f j * (((j : ℝ) ^ (-s) : ℝ) : ℂ)

theorem summable_dirichletL_of_norm_le_one {f : ℕ → ℂ} (hf : ∀ j, ‖f j‖ ≤ 1) {s : ℝ}
    (hs : 1 < s) : Summable fun j : ℕ => f j * (((j : ℝ) ^ (-s) : ℝ) : ℂ) := by
  have hg : Summable fun j : ℕ => (j : ℝ) ^ (-s) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded hg fun j => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := hf j
  have h0 : (0 : ℝ) ≤ (j : ℝ) ^ (-s) := by positivity
  nlinarith

/-- **Same parity couples through `L`-values**: the cross-spectral sum of two character windows is
`(1 + ε₁ε₂) q^s/(2q²) Re(c₁c̄₂τ₁τ̄₂ L(s, ψ̄₁ψ₂) + c₁c₂ψ̄₂(−1)τ₁τ₂ L(s, ψ̄₁ψ̄₂))`. -/
theorem crossSpectralSum_charTwist (c₁ c₂ : ℂ) {ψ₁ ψ₂ : DirichletCharacter ℂ q}
    (hψ₁ : ψ₁.IsPrimitive) (hψ₂ : ψ₂.IsPrimitive) {s : ℝ} (hs : 1 < s) :
    2 * (q : ℝ) ^ s * ∑' j : ℕ, crossPower (charTwist c₁ ψ₁) (charTwist c₂ ψ₂) q j * (j : ℝ) ^ (-s) =
      (1 + (ψ₁ (-1) * ψ₂ (-1)).re) * (q : ℝ) ^ s / (2 * (q : ℝ) ^ 2) *
        (c₁ * conj c₂ * gaussSum ψ₁ (RHTower.stdChar q) * conj (gaussSum ψ₂ (RHTower.stdChar q)) *
            dirichletL (fun j => conj (ψ₁ (j : ZMod q)) * ψ₂ (j : ZMod q)) s +
          c₁ * c₂ * conj (ψ₂ (-1)) * gaussSum ψ₁ (RHTower.stdChar q) *
            gaussSum ψ₂ (RHTower.stdChar q) *
            dirichletL (fun j => conj (ψ₁ (j : ZMod q)) * conj (ψ₂ (j : ZMod q))) s).re := by
  set P := c₁ * conj c₂ * gaussSum ψ₁ (RHTower.stdChar q) * conj (gaussSum ψ₂ (RHTower.stdChar q))
  set R := c₁ * c₂ * conj (ψ₂ (-1)) * gaussSum ψ₁ (RHTower.stdChar q) *
    gaussSum ψ₂ (RHTower.stdChar q)
  have hb₁ : ∀ j : ℕ, ‖conj (ψ₁ (j : ZMod q)) * ψ₂ (j : ZMod q)‖ ≤ 1 := fun j => by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
      (DirichletCharacter.norm_le_one _ _)
  have hb₂ : ∀ j : ℕ, ‖conj (ψ₁ (j : ZMod q)) * conj (ψ₂ (j : ZMod q))‖ ≤ 1 := fun j => by
    rw [norm_mul, Complex.norm_conj, Complex.norm_conj]
    exact mul_le_one₀ (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
      (DirichletCharacter.norm_le_one _ _)
  have hS₁ := summable_dirichletL_of_norm_le_one hb₁ hs
  have hS₂ := summable_dirichletL_of_norm_le_one hb₂ hs
  set e := (1 + (ψ₁ (-1) * ψ₂ (-1)).re) / (4 * (q : ℝ) ^ 2) with he
  have h1 := (hS₁.hasSum.mul_left P).add (hS₂.hasSum.mul_left R)
  have h2 := (Complex.hasSum_re h1).mul_left e
  have hF : (fun j : ℕ => crossPower (charTwist c₁ ψ₁) (charTwist c₂ ψ₂) q j * (j : ℝ) ^ (-s)) =
      fun j : ℕ => e * (P * (conj (ψ₁ (j : ZMod q)) * ψ₂ (j : ZMod q) *
          (((j : ℝ) ^ (-s) : ℝ) : ℂ)) +
        R * (conj (ψ₁ (j : ZMod q)) * conj (ψ₂ (j : ZMod q)) * (((j : ℝ) ^ (-s) : ℝ) : ℂ))).re := by
    funext j
    rw [crossPower_charTwist c₁ c₂ hψ₁ hψ₂ j]
    rw [show P * (conj (ψ₁ (j : ZMod q)) * ψ₂ (j : ZMod q) * (((j : ℝ) ^ (-s) : ℝ) : ℂ)) +
        R * (conj (ψ₁ (j : ZMod q)) * conj (ψ₂ (j : ZMod q)) * (((j : ℝ) ^ (-s) : ℝ) : ℂ)) =
        (P * (conj (ψ₁ (j : ZMod q)) * ψ₂ (j : ZMod q)) +
          R * (conj (ψ₁ (j : ZMod q)) * conj (ψ₂ (j : ZMod q)))) * (((j : ℝ) ^ (-s) : ℝ) : ℂ)
        by ring, Complex.re_mul_ofReal]
    ring
  rw [hF, h2.tsum_eq]
  unfold dirichletL
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [he]
  field_simp
  ring

#print axioms crossPower_charTwist
#print axioms crossPower_charTwist_eq_zero
#print axioms crossSpectralSum_charTwist

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
