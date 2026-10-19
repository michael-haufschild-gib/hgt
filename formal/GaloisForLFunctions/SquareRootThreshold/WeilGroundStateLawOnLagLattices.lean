import GaloisForLFunctions.SquareRootThreshold.OnLineShadowIndistinguishability

/-!
# The Weil ground state of lag-lattice configurations

Visibility asks *whether* `Re W(f, f) < 0` for some test of aperture `a`; the ground state asks
*how negative* the form can be per unit of `L²` mass. For a configuration with lag formula
`W(f, f) = ℓ Σ_m k(mℓ) D(m)` the answer is exact.

* **Ground-state law** (`weil_floor_iff_toeplitz_floor`, `hodge_floor_iff_toeplitz_floor`). For
  every `μ ∈ ℝ`, the floor `Re W(f, f) ≥ ℓμ ∫|f|²` holds on all tests of aperture `a` iff it holds
  on the polar-constrained (Hodge) tests, iff `Re T_D(c) ≥ μ‖c‖²` on the Toeplitz section of size
  `⌈2a/ℓ⌉`. So the Weil ground energy at aperture `a` is `ℓ` times the lowest eigenvalue of the
  Toeplitz section, and the polar constraint does not raise it. The proof shifts the symbol by
  `μ` at lag `0` (`k(0) = ∫|f|²`) and reuses the Toeplitz law; lag-point bump tests have mass
  `∫|f|² = (∫|β|²)‖c‖²`.
* **The off-line lattice** (`offLineLattice_weil_floor`, `offLineLattice_hodge_floor_sharp`). For
  `{½ ± δ + 2πik/L}` the symbol `2cosh(δmL)` gives the rank-two section `x yᵀ + y xᵀ`,
  `x_j = e^{δjL}`, `y_j = e^{−δjL}`, whose lowest eigenvalue is `n − √(S₊S₋)`,
  `S_± = Σ_{j<n} e^{±2δjL}`, `n = ⌈2a/L⌉` (`latticeFloor`). Hence the ground energy is exactly
  `L (n − √(S₊S₋))` for `a > L/2`, attained by polar-constrained tests.
* **Growth at the depth exponent** (`latticeFloor_aperture_bounds`). For `a > L/2`,
  `2a + L − L e^{δ(2a − L)} ≥ L · latticeFloor ≥ −(2a + L) e^{2δa}`: the ground energy decays like
  `−e^{2δa}`, with exponent exactly the depth.

The exponential floor growth in the aperture with exponent the depth is the model behaviour of
the restricted-Weil floor of `ζ` off RH (`RHTower.XiRestrictedWeilFloorGrowthUniversalityLaw`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Shifting the symbol at lag zero -/

/-- The lag-zero indicator. -/
def lagDelta (m : ℤ) : ℂ := if m = 0 then 1 else 0

/-- The symbol shifted by `μ` at lag `0`. -/
def shiftSymbol (D : ℤ → ℂ) (μ : ℝ) (m : ℤ) : ℂ := D m - μ * lagDelta m

theorem toeplitzForm_lagDelta {n : ℕ} (c : Fin n → ℂ) :
    toeplitzForm lagDelta n c = ((∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
  rw [toeplitzForm, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · rw [sub_self, lagDelta, if_pos rfl, mul_one, Complex.mul_conj']
    push_cast
    ring
  · intro j' _ hne
    rw [lagDelta, if_neg, mul_zero]
    intro h
    exact hne (Fin.ext (by omega)).symm
  · simp

theorem toeplitzForm_shiftSymbol (D : ℤ → ℂ) (μ : ℝ) {n : ℕ} (c : Fin n → ℂ) :
    toeplitzForm (shiftSymbol D μ) n c =
      toeplitzForm D n c - ((μ * ∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, ← toeplitzForm_lagDelta, toeplitzForm, toeplitzForm, toeplitzForm,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [shiftSymbol]
  ring

theorem lagSum_shiftSymbol {ℓ : ℝ} (hℓ : 0 < ℓ) {f : ℝ → ℂ} (hfc : HasCompactSupport f)
    (D : ℤ → ℂ) (μ : ℝ) :
    ∑' m : ℤ, EF.weilTest f f (m * ℓ) * shiftSymbol D μ m =
      ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m - μ * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨A, hfs⟩ := exists_Icc_of_hasCompactSupport hfc
  obtain ⟨S, hS⟩ := exists_lag_window (K := EF.weilTest f f) hℓ (weilTest_abs_le hfs hfs)
  have hS' : ∀ m : ℤ, m ∉ insert 0 S → EF.weilTest f f (m * ℓ) = 0 := fun m hm =>
    hS m fun h => hm (Finset.mem_insert_of_mem h)
  rw [tsum_eq_sum (s := insert 0 S) fun m hm => by rw [hS' m hm, zero_mul],
    tsum_eq_sum (s := insert 0 S) fun m hm => by rw [hS' m hm, zero_mul]]
  simp only [shiftSymbol, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [← weilTest_self_zero, Finset.sum_eq_single 0]
  · rw [lagDelta, if_pos rfl, Int.cast_zero, zero_mul]
    ring
  · intro m _ hm
    rw [lagDelta, if_neg hm]
    ring
  · intro h
    exact absurd (Finset.mem_insert_self 0 S) h

/-! ### The ground-state law -/

/-- Lag-point bump tests carry `L²` mass `(∫|β|²) ‖c‖²`. -/
theorem integral_norm_sq_bumpTest {ℓ w : ℝ} (hℓ : 0 < ℓ) (hwℓ : 2 * w < ℓ) {β : ℝ → ℂ}
    (hβc : Continuous β) (hβcs : HasCompactSupport β) (hβs : ∀ x, β x ≠ 0 → |x| ≤ w) {n : ℕ}
    (c : Fin n → ℂ) :
    ∫ t, ‖bumpTest β ℓ c t‖ ^ 2 = (∫ x, ‖β x‖ ^ 2) * ∑ j, ‖c j‖ ^ 2 := by
  have h := lagSum_bumpTest_eq_toeplitz hℓ hwℓ hβc hβcs hβs lagDelta c
  have hl : ∑' m : ℤ, EF.weilTest (bumpTest β ℓ c) (bumpTest β ℓ c) (m * ℓ) * lagDelta m =
      EF.weilTest (bumpTest β ℓ c) (bumpTest β ℓ c) 0 := by
    rw [tsum_eq_single 0 fun m hm => by rw [lagDelta, if_neg hm, mul_zero]]
    rw [lagDelta, if_pos rfl, mul_one, Int.cast_zero, zero_mul]
  rw [hl, weilTest_self_zero, toeplitzForm_lagDelta, ← Complex.ofReal_mul] at h
  exact_mod_cast h

/-- The Toeplitz floor from the Hodge floor: polar-free lag-point bumps realize every Toeplitz
Rayleigh quotient. -/
theorem toeplitz_floor_of_hodge_floor (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (D : ℤ → ℂ)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) (μ : ℝ)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
      paperFT f (-(I / 2)) = 0 → ℓ * μ * ∫ t, ‖f t‖ ^ 2 ≤ (Z.W f f).re)
    (c : Fin ⌈2 * a / ℓ⌉₊ → ℂ) :
    μ * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re := by
  have hna : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) * ℓ < 2 * a := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * a / ℓ)
    have : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) < 2 * a / ℓ := by linarith
    rwa [lt_div_iff₀ hℓ] at this
  have hgap : 0 < a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ,
      w = min (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1 / 4 := ⟨_, rfl⟩
  have hw0 : 0 < w := by
    rw [hw]; exact div_pos (lt_min (lt_min (by linarith) hgap) one_pos) (by norm_num)
  have hm1 := min_le_left (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1
  have hm2 := min_le_right (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1
  have hm3 := min_le_left (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)
  have hm4 := min_le_right (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)
  have hwℓ : 2 * w < ℓ := by rw [hw]; linarith
  have hwa : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ + w ≤ a := by rw [hw]; linarith
  have hw4 : 4 * w ≤ 1 := by rw [hw]; linarith
  obtain ⟨β, hβ2, hβcs, hβs, hβp, hβm, hB⟩ := exists_polarFree_bump hw0 hw4
  have hf := contDiff_bumpTest hβ2 ℓ c
  have hfs := tsupport_bumpTest_subset hβs hℓ.le hwa c
  have hpol : ∀ z : ℂ, paperFT β z = 0 → paperFT (bumpTest β ℓ c) z = 0 := fun z hz => by
    rw [paperFT_bumpTest hβ2.continuous hβcs, hz, mul_zero]
  have h1 := h _ hf hfs (hpol _ hβp) (hpol _ hβm)
  rw [hW _ hf (hasCompactSupport_of_tsupport_subset_Icc hfs),
    lagSum_bumpTest_eq_toeplitz hℓ hwℓ hβ2.continuous hβcs hβs, ← mul_assoc,
    show ((ℓ : ℝ) : ℂ) * ((∫ x, ‖β x‖ ^ 2 : ℝ) : ℂ) = ((ℓ * ∫ x, ‖β x‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.re_ofReal_mul,
    integral_norm_sq_bumpTest hℓ hwℓ hβ2.continuous hβcs hβs c] at h1
  have hpos : 0 < ℓ * ∫ x, ‖β x‖ ^ 2 := mul_pos hℓ hB
  nlinarith

/-- The Weil floor from the Toeplitz floor: periodization of the shifted symbol. -/
theorem weil_floor_of_toeplitz_floor (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (D : ℤ → ℂ)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (μ : ℝ)
    (hT : ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ, μ * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ℓ * μ * ∫ t, ‖f t‖ ^ 2 ≤ (Z.W f f).re := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have hT' : ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ,
      0 ≤ (toeplitzForm (shiftSymbol D μ) ⌈2 * a / ℓ⌉₊ c).re := fun c => by
    rw [toeplitzForm_shiftSymbol, Complex.sub_re, Complex.ofReal_re]
    linarith [hT c]
  have h := re_lagSum_nonneg_of_toeplitz hℓ (shiftSymbol D μ) hT' hf hfs
  rw [lagSum_shiftSymbol hℓ hfc D μ, mul_sub, ← hW f hf hfc, Complex.sub_re,
    show ((ℓ : ℝ) : ℂ) * ((μ : ℂ) * ((∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ)) =
      ((ℓ * μ * ∫ t, ‖f t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re] at h
  linarith

/-- **Ground-state law.** For a lag-lattice configuration and any `μ`, the Weil floor
`Re W(f, f) ≥ ℓμ ∫|f|²` at aperture `a` is the Toeplitz floor `Re T_D(c) ≥ μ‖c‖²` of size
`⌈2a/ℓ⌉`. -/
theorem weil_floor_iff_toeplitz_floor (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (D : ℤ → ℂ)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) (μ : ℝ) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        ℓ * μ * ∫ t, ‖f t‖ ^ 2 ≤ (Z.W f f).re) ↔
      ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ, μ * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re :=
  ⟨fun h => toeplitz_floor_of_hodge_floor Z hℓ D hW ha μ fun f hf hfs _ _ => h f hf hfs,
    fun hT _ hf hfs => weil_floor_of_toeplitz_floor Z hℓ D hW μ hT hf hfs⟩

/-- **Ground-state law for the Hodge class.** The polar constraint does not raise the floor. -/
theorem hodge_floor_iff_toeplitz_floor (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (D : ℤ → ℂ)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) (μ : ℝ) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
        paperFT f (-(I / 2)) = 0 → ℓ * μ * ∫ t, ‖f t‖ ^ 2 ≤ (Z.W f f).re) ↔
      ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ, μ * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re :=
  ⟨toeplitz_floor_of_hodge_floor Z hℓ D hW ha μ,
    fun hT _ hf hfs _ _ => weil_floor_of_toeplitz_floor Z hℓ D hW μ hT hf hfs⟩

/-! ### Rank-two sections -/

/-- **Rank-two floor.** For real vectors `x, y` with `X = ‖x‖`, `Y = ‖y‖` and `A = Σ c_j x_j`,
`B = Σ c_j y_j`: `2 Re(A conj B) ≥ (⟨x, y⟩ − XY) ‖c‖²`. -/
theorem rankTwo_floor {n : ℕ} (x y : Fin n → ℝ) (c : Fin n → ℂ) :
    (∑ j, x j * y j - √(∑ j, x j ^ 2) * √(∑ j, y j ^ 2)) * ∑ j, ‖c j‖ ^ 2 ≤
      2 * ((∑ j, c j * x j) * conj (∑ j, c j * y j)).re := by
  set X := √(∑ j, x j ^ 2) with hX
  set Y := √(∑ j, y j ^ 2) with hY
  set A := ∑ j, c j * x j with hA
  set B := ∑ j, c j * y j with hB
  have hX2 : X ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hY2 : Y ^ 2 = ∑ j, y j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  -- `V = Y A − X B` is a combination of `c` with the real vector `v = Y x − X y`
  set V : ℂ := (Y : ℂ) * A - (X : ℂ) * B with hV
  have hVsum : V = ∑ j, c j * ((Y * x j - X * y j : ℝ) : ℂ) := by
    rw [hV, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hCS : ‖V‖ ^ 2 ≤ (∑ j, ‖c j‖ ^ 2) * ∑ j, (Y * x j - X * y j) ^ 2 := by
    have h1 : ‖V‖ ≤ ∑ j, ‖c j‖ * |Y * x j - X * y j| := by
      rw [hVsum]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖c j‖)
      (fun j => |Y * x j - X * y j|)
    simp only [sq_abs] at h2
    calc ‖V‖ ^ 2 ≤ (∑ j, ‖c j‖ * |Y * x j - X * y j|) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hv : ∑ j, (Y * x j - X * y j) ^ 2 = 2 * (X * Y) * (X * Y - ∑ j, x j * y j) := by
    have : ∑ j, (Y * x j - X * y j) ^ 2 =
        Y ^ 2 * ∑ j, x j ^ 2 - 2 * (X * Y) * ∑ j, x j * y j + X ^ 2 * ∑ j, y j ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, ← hX2, ← hY2]
    ring
  -- polarization: `‖YA + XB‖² − ‖YA − XB‖² = 4XY Re(A conj B)`
  have hpol : ‖(Y : ℂ) * A + (X : ℂ) * B‖ ^ 2 - ‖V‖ ^ 2 = 4 * (X * Y) * (A * conj B).re := by
    rw [hV, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.normSq_sub]
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im]
    ring
  have hU := sq_nonneg ‖(Y : ℂ) * A + (X : ℂ) * B‖
  rcases (mul_nonneg hX0 hY0).eq_or_lt with hXY | hXY
  · -- degenerate case: one of the vectors vanishes
    have hzero : ∀ z : Fin n → ℝ, √(∑ j, z j ^ 2) = 0 → ∀ j, z j = 0 := by
      intro z hz j
      rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg _)] at hz
      exact pow_eq_zero_iff two_ne_zero |>.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (z j)).mp hz j (Finset.mem_univ j))
    rcases mul_eq_zero.mp hXY.symm with h | h
    · have hx := hzero x h
      rw [hA, h]
      simp [hx]
    · have hy := hzero y h
      rw [hB, h]
      simp [hy]
  · rw [hv] at hCS
    have key : 2 * (X * Y) * ((∑ j, x j * y j - X * Y) * ∑ j, ‖c j‖ ^ 2) ≤
        2 * (X * Y) * (2 * (A * conj B).re) := by nlinarith
    exact le_of_mul_le_mul_left key (by linarith)

/-- **Rank-two extremal vector.** For `c_j = Y x_j − X y_j` the floor is attained:
`2 A B = (⟨x, y⟩ − XY) ‖c‖²` with `‖c‖² = Σ_j (Y x_j − X y_j)²`. -/
theorem rankTwo_floor_attained {n : ℕ} (x y : Fin n → ℝ) :
    2 * ((∑ j, ((√(∑ j, y j ^ 2) * x j - √(∑ j, x j ^ 2) * y j : ℝ) : ℂ) * x j) *
        conj (∑ j, ((√(∑ j, y j ^ 2) * x j - √(∑ j, x j ^ 2) * y j : ℝ) : ℂ) * y j)).re =
      (∑ j, x j * y j - √(∑ j, x j ^ 2) * √(∑ j, y j ^ 2)) *
        ∑ j, ‖((√(∑ j, y j ^ 2) * x j - √(∑ j, x j ^ 2) * y j : ℝ) : ℂ)‖ ^ 2 := by
  set X := √(∑ j, x j ^ 2) with hX
  set Y := √(∑ j, y j ^ 2) with hY
  have hX2 : X ^ 2 = ∑ j, x j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hY2 : Y ^ 2 = ∑ j, y j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hA : ∑ j, ((Y * x j - X * y j : ℝ) : ℂ) * x j = ((Y * X ^ 2 - X * ∑ j, x j * y j : ℝ) : ℂ) := by
    rw [hX2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by ring
  have hB : ∑ j, ((Y * x j - X * y j : ℝ) : ℂ) * y j = ((Y * ∑ j, x j * y j - X * Y ^ 2 : ℝ) : ℂ) := by
    rw [hY2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by ring
  have hc : ∑ j, ‖((Y * x j - X * y j : ℝ) : ℂ)‖ ^ 2 =
      Y ^ 2 * ∑ j, x j ^ 2 - 2 * (X * Y) * ∑ j, x j * y j + X ^ 2 * ∑ j, y j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hA, hB, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, hc, ← hX2, ← hY2]
  ring

/-! ### The off-line lattice -/

/-- The lattice symbol `2cosh(δmL)`. -/
def latticeSymbol (L δ : ℝ) (m : ℤ) : ℂ := ((2 * Real.cosh (δ * (m * L)) : ℝ) : ℂ)

/-- The lattice floor `n − √(S₊ S₋)`, `S_± = Σ_{j<n} e^{±2δjL}`. -/
def latticeFloor (L δ : ℝ) (n : ℕ) : ℝ :=
  n - √(∑ j : Fin n, Real.exp (δ * (j * L)) ^ 2) * √(∑ j : Fin n, Real.exp (-(δ * (j * L))) ^ 2)

/-- The lattice section is the rank-two form `A conj B + B conj A`, `A = Σ c_j e^{δjL}`,
`B = Σ c_j e^{−δjL}`. -/
theorem toeplitzForm_latticeSymbol (L δ : ℝ) {n : ℕ} (c : Fin n → ℂ) :
    toeplitzForm (latticeSymbol L δ) n c =
      (∑ j, c j * (Real.exp (δ * (j * L)) : ℂ)) * conj (∑ j, c j * (Real.exp (-(δ * (j * L))) : ℂ)) +
      (∑ j, c j * (Real.exp (-(δ * (j * L))) : ℂ)) * conj (∑ j, c j * (Real.exp (δ * (j * L)) : ℂ)) := by
  rw [map_sum, map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib,
    toeplitzForm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have hcosh : 2 * Real.cosh (δ * ((((j : ℤ) - j' : ℤ) : ℝ) * L)) =
      Real.exp (δ * (j * L)) * Real.exp (-(δ * (j' * L))) +
        Real.exp (-(δ * (j * L))) * Real.exp (δ * (j' * L)) := by
    rw [Real.cosh_eq, ← Real.exp_add, ← Real.exp_add]
    push_cast
    ring_nf
  rw [latticeSymbol, hcosh, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  ring

theorem re_toeplitzForm_latticeSymbol (L δ : ℝ) {n : ℕ} (c : Fin n → ℂ) :
    (toeplitzForm (latticeSymbol L δ) n c).re =
      2 * ((∑ j, c j * (Real.exp (δ * (j * L)) : ℂ)) *
        conj (∑ j, c j * (Real.exp (-(δ * (j * L))) : ℂ))).re := by
  rw [toeplitzForm_latticeSymbol, Complex.add_re]
  have : ∀ u v : ℂ, (v * conj u).re = (u * conj v).re := fun u v => by
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  rw [this]
  ring

theorem sum_exp_mul_exp_neg (L δ : ℝ) (n : ℕ) :
    ∑ j : Fin n, Real.exp (δ * (j * L)) * Real.exp (-(δ * (j * L))) = n := by
  simp [← Real.exp_add]

/-- **The lattice Toeplitz floor.** `Re T(c) ≥ (n − √(S₊S₋)) ‖c‖²`. -/
theorem latticeSymbol_toeplitz_floor (L δ : ℝ) {n : ℕ} (c : Fin n → ℂ) :
    latticeFloor L δ n * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm (latticeSymbol L δ) n c).re := by
  rw [re_toeplitzForm_latticeSymbol]
  have h := rankTwo_floor (fun j : Fin n => Real.exp (δ * (j * L)))
    (fun j : Fin n => Real.exp (-(δ * (j * L)))) c
  rw [sum_exp_mul_exp_neg] at h
  exact h

/-- **The lattice floor is attained** for `n ≥ 2`: some `c` has `Re T(c) = (n − √(S₊S₋))‖c‖²`
with `‖c‖² > 0`. -/
theorem exists_latticeSymbol_toeplitz_floor_attained {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {n : ℕ}
    (hn : 2 ≤ n) : ∃ c : Fin n → ℂ, 0 < ∑ j, ‖c j‖ ^ 2 ∧
      (toeplitzForm (latticeSymbol L δ) n c).re = latticeFloor L δ n * ∑ j, ‖c j‖ ^ 2 := by
  set x : Fin n → ℝ := fun j => Real.exp (δ * (j * L)) with hx
  set y : Fin n → ℝ := fun j => Real.exp (-(δ * (j * L))) with hy
  refine ⟨fun j => ((√(∑ j, y j ^ 2) * x j - √(∑ j, x j ^ 2) * y j : ℝ) : ℂ), ?_, ?_⟩
  · -- the first coordinate is `Y − X ≠ 0`
    have hXY : √(∑ j, y j ^ 2) < √(∑ j, x j ^ 2) := by
      apply Real.sqrt_lt_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
      apply Finset.sum_lt_sum
      · intro j _
        simp only [hx, hy]
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ δ * (j * L) := by positivity
        push_cast
        linarith
      · refine ⟨⟨1, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [hx, hy]
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        apply Real.exp_lt_exp.mpr
        have : 0 < δ * (((⟨1, by omega⟩ : Fin n) : ℕ) * L) := by
          simp only [Nat.cast_one, one_mul]; positivity
        push_cast at this ⊢
        linarith
    have h0 := Finset.single_le_sum (f := fun j : Fin n =>
      ‖((√(∑ j, y j ^ 2) * x j - √(∑ j, x j ^ 2) * y j : ℝ) : ℂ)‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ ⟨0, by omega⟩)
    refine lt_of_lt_of_le ?_ h0
    simp only [hx, hy, Nat.cast_zero, zero_mul, mul_zero, neg_zero, Real.exp_zero,
      mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have : √(∑ j, y j ^ 2) - √(∑ j, x j ^ 2) ≠ 0 := by linarith
    positivity
  · rw [re_toeplitzForm_latticeSymbol]
    have h := rankTwo_floor_attained x y
    rw [sum_exp_mul_exp_neg] at h
    exact h

/-- **Ground energy of the off-line lattice.** On every test of aperture `a`,
`Re W(f, f) ≥ L (n − √(S₊S₋)) ∫|f|²`, `n = ⌈2a/L⌉`. -/
theorem offLineLattice_weil_floor {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {a : ℝ}
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    L * latticeFloor L δ ⌈2 * a / L⌉₊ * ∫ t, ‖f t‖ ^ 2 ≤
      ((offLineLatticeConfig hL hδ hδ').W f f).re :=
  weil_floor_of_toeplitz_floor _ hL (latticeSymbol L δ)
    (fun _ hf hfc => W_offLineLatticeConfig_lag hL hδ hδ' hf hfc) _
    (fun c => latticeSymbol_toeplitz_floor L δ c) hf hfs

/-- **The lattice ground energy is sharp in the Hodge class.** For `a > L/2` and every
`μ > n − √(S₊S₋)` some polar-constrained test of aperture `a` has `Re W(f, f) < Lμ ∫|f|²`. -/
theorem offLineLattice_hodge_floor_sharp {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {a : ℝ} (ha : L / 2 < a) {μ : ℝ} (hμ : latticeFloor L δ ⌈2 * a / L⌉₊ < μ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0 ∧
        ((offLineLatticeConfig hL hδ hδ').W f f).re < L * μ * ∫ t, ‖f t‖ ^ 2 := by
  have ha0 : 0 < a := lt_trans (by positivity) ha
  have hn : 2 ≤ ⌈2 * a / L⌉₊ := by
    have : 1 < ⌈2 * a / L⌉₊ := by
      rw [Nat.lt_ceil, lt_div_iff₀ hL]; push_cast; linarith
    omega
  by_contra hcon
  push Not at hcon
  have hT := (hodge_floor_iff_toeplitz_floor _ hL (latticeSymbol L δ)
    (fun _ hf hfc => W_offLineLatticeConfig_lag hL hδ hδ' hf hfc) ha0 μ).mp
    fun f hf hfs hp hm => hcon f hf hfs hp hm
  obtain ⟨c, hc0, hc⟩ := exists_latticeSymbol_toeplitz_floor_attained hL hδ hn
  have := hT c
  rw [hc] at this
  nlinarith

/-! ### Exponential growth at the depth exponent -/

theorem latticeFloor_le (L δ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    latticeFloor L δ n ≤ n - Real.exp (δ * (((n : ℝ) - 1) * L)) := by
  have hlast : Real.exp (δ * (((n : ℝ) - 1) * L)) ≤ √(∑ j : Fin n, Real.exp (δ * (j * L)) ^ 2) := by
    rw [← Real.sqrt_sq (Real.exp_pos _).le]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun j : Fin n => Real.exp (δ * (j * L)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ ⟨n - 1, by omega⟩)
    simp only [Nat.cast_sub hn, Nat.cast_one] at this
    exact this
  have hfirst : 1 ≤ √(∑ j : Fin n, Real.exp (-(δ * (j * L))) ^ 2) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (f := fun j : Fin n => Real.exp (-(δ * (j * L))) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ ⟨0, by omega⟩)
    simpa using this
  rw [latticeFloor]
  nlinarith [Real.exp_pos (δ * (((n : ℝ) - 1) * L))]

theorem latticeFloor_ge {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) :
    n - n * Real.exp (δ * (((n : ℝ) - 1) * L)) ≤ latticeFloor L δ n := by
  set E := Real.exp (δ * (((n : ℝ) - 1) * L)) with hE
  have hj : ∀ j : Fin n, (j : ℝ) ≤ (n : ℝ) - 1 := fun j => by
    have := j.isLt
    have : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast this
    linarith
  have h1 : √(∑ j : Fin n, Real.exp (δ * (j * L)) ^ 2) ≤ √n * E := by
    rw [show √n * E = √(n * E ^ 2) by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]]
    apply Real.sqrt_le_sqrt
    calc ∑ j : Fin n, Real.exp (δ * (j * L)) ^ 2 ≤ ∑ _j : Fin n, E ^ 2 := by
          refine Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (Real.exp_pos _).le ?_ 2
          rw [hE]
          apply Real.exp_le_exp.mpr
          have := hj j
          have : 0 ≤ δ * L := by positivity
          nlinarith
      _ = n * E ^ 2 := by simp
  have h2 : √(∑ j : Fin n, Real.exp (-(δ * (j * L))) ^ 2) ≤ √n := by
    apply Real.sqrt_le_sqrt
    calc ∑ j : Fin n, Real.exp (-(δ * (j * L))) ^ 2 ≤ ∑ _j : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Real.exp_nat_mul, Real.exp_le_one_iff]
          have : 0 ≤ δ * (j * L) := by positivity
          push_cast
          linarith
      _ = n := by simp
  have hsq : √(n : ℝ) * √n = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [latticeFloor]
  have := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  nlinarith [Real.exp_pos (δ * (((n : ℝ) - 1) * L))]

/-- **Depth-exponent growth of the lattice ground energy.** For `a > 0`, with `n = ⌈2a/L⌉`:
`−(2a + L) e^{2δa} ≤ L · latticeFloor ≤ 2a + L − L e^{δ(2a − L)}`. -/
theorem latticeFloor_aperture_bounds {L δ a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (ha : 0 < a) :
    -(2 * a + L) * Real.exp (2 * δ * a) ≤ L * latticeFloor L δ ⌈2 * a / L⌉₊ ∧
      L * latticeFloor L δ ⌈2 * a / L⌉₊ ≤ 2 * a + L - L * Real.exp (δ * (2 * a - L)) := by
  set n := ⌈2 * a / L⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hlo : 2 * a ≤ n * L := by
    have := Nat.le_ceil (2 * a / L)
    rwa [div_le_iff₀ hL] at this
  have hhi : (n : ℝ) * L < 2 * a + L := by
    have h2 : (n : ℝ) < 2 * a / L + 1 := Nat.ceil_lt_add_one (by positivity)
    have : (2 * a / L + 1) * L = 2 * a + L := by field_simp
    nlinarith
  constructor
  · have h := latticeFloor_ge hL hδ hn1
    have hE : Real.exp (δ * (((n : ℝ) - 1) * L)) ≤ Real.exp (2 * δ * a) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hE0 := Real.exp_pos (δ * (((n : ℝ) - 1) * L))
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [Real.exp_pos (2 * δ * a)]
  · have h := latticeFloor_le L δ hn1
    have hE : Real.exp (δ * (2 * a - L)) ≤ Real.exp (δ * (((n : ℝ) - 1) * L)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith

end GaloisForLFunctions.SquareRootThreshold
