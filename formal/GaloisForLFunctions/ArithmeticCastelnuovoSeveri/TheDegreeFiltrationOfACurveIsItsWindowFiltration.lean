import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanIsTheTowerOfTheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheVisibilityDegreeOfAnIsolatedPair
import GaloisForLFunctions.SquareRootThreshold.CrystallineFragilityOfOffLineLattices
import GaloisForLFunctions.SquareRootThreshold.HodgeIndexOnLagLatticeConfigurations
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations

/-!
# The degree filtration of a curve is its window filtration

A configuration has a **lag formula** when `W(f, f) = ℓ Σ_m k_f(mℓ) D(m)`, `k_f = f ⋆ f̃`: the
scaling surface of a curve (`ℓ = log q`, `D(m) = Σ_i β_i^m`, `W_curveConfig_lagFormula`), the
off-line lattices and every periodic pattern of Square-Root Threshold. For these the abstract
Toeplitz law (`SquareRootThreshold.weil_nonneg_iff_toeplitz_of_lagFormula`) decides Weil positivity
at aperture `a` by the Toeplitz window of size `⌈2a/ℓ⌉`. This file shows that the failure is never
partial:

  **the Hodge defect at degree `a` of a lag lattice is `0` if the window is positive semidefinite
  and `∞` otherwise** (`hodgeDefectAt_lagFormula`).

A negative vector `c` of the window gives block tests `Σ_b c_b g(· − x − bℓ)` on a narrow bump `g`.
Only the lag `b − b'` of a block meets the lattice, so each block has square `ℓ‖g‖² ⟨Tc, c⟩ < 0`
(`hasSum_lag_blockTest_self`). The slack `2a − (n − 1)ℓ > 0` holds `r` block bases that never meet
modulo `ℓ` (`sep_offsets`), so distinct blocks do not interact (`hasSum_lag_blockTest_sep`) and the
`r` blocks span a negative definite space, for every `r` (`hodgeDefectAt_eq_top_of_lagFormula`).

* **Curves** (`hodgeDefectAt_curveConfig`). The degree filtration of the scaling surface of a curve
  jumps from `0` straight to `∞` at the first Frobenius window with a negative square; every curve
  has Hodge index up to degree `log q / 2`, and from the window `2g` on the defect is `0` or `∞`
  according as the curve is pure or not. The golden fake curve jumps at `log 5 / 2`.
* **Off-line lattices** (`hodgeDefectAt_offLineLattice`). The lattice `{½ ± δ + 2πik/L}` has Hodge
  defect `0` up to its Nyquist degree `L/2` and `∞` beyond it.
-/

open Complex MeasureTheory Finset
open scoped Real ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig toeplitzForm
  weil_nonneg_iff_toeplitz_of_lagFormula)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Block tests on a lag lattice -/

/-- **Sesquilinearity of the Weil kernel** on finite combinations of tests. -/
theorem weilTest_finset_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (φ : ι → ℝ → ℂ)
    (ψ : κ → ℝ → ℂ) (hφ : ∀ p, Continuous (φ p)) (hφc : ∀ p, HasCompactSupport (φ p))
    (hψ : ∀ q, Continuous (ψ q)) (a : ι → ℂ) (b : κ → ℂ) (u : ℝ) :
    EF.weilTest (fun t => ∑ p, a p * φ p t) (fun t => ∑ q, b q * ψ q t) u =
      ∑ p, ∑ q, a p * conj (b q) * EF.weilTest (φ p) (ψ q) u := by
  have hint : ∀ p q, Integrable fun t => a p * φ p t * (conj (b q) * conj (ψ q (t - u))) := by
    intro p q
    have hc : Continuous fun t => a p * φ p t * (conj (b q) * conj (ψ q (t - u))) :=
      (continuous_const.mul (hφ p)).mul (continuous_const.mul
        (Complex.continuous_conj.comp ((hψ q).comp (continuous_sub_right u))))
    exact hc.integrable_of_hasCompactSupport (hφc p).mul_left.mul_right
  simp only [RHTower.weilTest_apply, map_sum, map_mul, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun q _ => hint p q]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext t
  ring

/-- Two translates of a narrow test in one coset of `ℓℤ`: only the lag `k` meets the lattice. -/
theorem hasSum_lag_translate_coset {g : ℝ → ℂ} {w ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwℓ : w < ℓ) (D : ℤ → ℂ) {x y : ℝ} {k : ℤ}
    (hxy : x - y = k * ℓ) :
    HasSum (fun m : ℤ => EF.weilTest (translate x g) (translate y g) (m * ℓ) * D m)
      (EF.weilTest g g 0 * D k) := by
  convert hasSum_single k (fun m hm => ?_) using 1
  · rw [weilTest_translate, hxy, sub_self]
  · rw [weilTest_translate]
    have hz : EF.weilTest g g (m * ℓ - (x - y)) = 0 := by
      by_contra hne
      have hmem := EF.tsupport_weilTest_subset hgs hgs (subset_tsupport _ hne)
      rw [hxy, show (m : ℝ) * ℓ - k * ℓ = ((m - k : ℤ) : ℝ) * ℓ by push_cast; ring] at hmem
      have h1 : (1 : ℝ) ≤ |((m - k : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hm)
      have h2 : |((m - k : ℤ) : ℝ) * ℓ| ≤ w := abs_le.mpr hmem
      rw [abs_mul, abs_of_pos hℓ] at h2
      nlinarith
    rw [hz, zero_mul]

/-- Two translates whose offset stays more than `w` away from `ℓℤ` do not meet the lattice. -/
theorem hasSum_lag_translate_sep {g : ℝ → ℂ} {w ℓ : ℝ}
    (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (D : ℤ → ℂ) {x y : ℝ}
    (hsep : ∀ k : ℤ, w < |k * ℓ - (x - y)|) :
    HasSum (fun m : ℤ => EF.weilTest (translate x g) (translate y g) (m * ℓ) * D m) 0 := by
  have hz : ∀ m : ℤ, EF.weilTest (translate x g) (translate y g) (m * ℓ) * D m = 0 := fun m => by
    rw [weilTest_translate]
    have : EF.weilTest g g (m * ℓ - (x - y)) = 0 := by
      by_contra hne
      exact absurd (abs_le.mpr (EF.tsupport_weilTest_subset hgs hgs (subset_tsupport _ hne)))
        (not_le.mpr (hsep m))
    rw [this, zero_mul]
  simpa only [hz] using (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℂ)) 0)

/-- The block test `Σ_b c_b g(· − x − bℓ)` built on the window vector `c`. -/
def blockTest (g : ℝ → ℂ) (ℓ : ℝ) {n : ℕ} (c : Fin n → ℂ) (x : ℝ) : ℝ → ℂ :=
  fun t => ∑ b : Fin n, c b * translate (x + ((b : ℕ) : ℝ) * ℓ) g t

theorem blockTest_eq_sum_smul (g : ℝ → ℂ) (ℓ : ℝ) {n : ℕ} (c : Fin n → ℂ) (x : ℝ) :
    blockTest g ℓ c x = ∑ b : Fin n, c b • translate (x + ((b : ℕ) : ℝ) * ℓ) g := by
  funext t
  simp [blockTest, Finset.sum_apply]

/-- **A block has square `‖g‖² ⟨Tc, c⟩`.** -/
theorem hasSum_lag_blockTest_self {g : ℝ → ℂ} {w ℓ : ℝ} (hℓ : 0 < ℓ) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (hwℓ : w < ℓ)
    (D : ℤ → ℂ) {n : ℕ} (c : Fin n → ℂ) (x : ℝ) :
    HasSum (fun m : ℤ => EF.weilTest (blockTest g ℓ c x) (blockTest g ℓ c x) (m * ℓ) * D m)
      (EF.weilTest g g 0 * toeplitzForm D n c) := by
  have hφ : ∀ b : Fin n, Continuous (translate (x + ((b : ℕ) : ℝ) * ℓ) g) := fun b =>
    hg.comp (continuous_sub_right _)
  have hφc : ∀ b : Fin n, HasCompactSupport (translate (x + ((b : ℕ) : ℝ) * ℓ) g) := fun b =>
    translate_hasCompactSupport hgc _
  have e : ∀ m : ℤ, EF.weilTest (blockTest g ℓ c x) (blockTest g ℓ c x) (m * ℓ) * D m =
      ∑ b, ∑ b', c b * conj (c b') * (EF.weilTest (translate (x + ((b : ℕ) : ℝ) * ℓ) g)
        (translate (x + ((b' : ℕ) : ℝ) * ℓ) g) (m * ℓ) * D m) := fun m => by
    unfold blockTest
    rw [weilTest_finset_sum _ _ hφ hφc hφ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b' _ => by ring
  rw [funext e, toeplitzForm, Finset.mul_sum]
  refine hasSum_sum fun b _ => ?_
  rw [Finset.mul_sum]
  refine hasSum_sum fun b' _ => ?_
  rw [show EF.weilTest g g 0 * (c b * conj (c b') * D ((b : ℤ) - b')) =
    c b * conj (c b') * (EF.weilTest g g 0 * D ((b : ℤ) - b')) by ring]
  refine (hasSum_lag_translate_coset hℓ hgs hwℓ D ?_).mul_left _
  push_cast
  ring

/-- **Separated blocks do not interact.** -/
theorem hasSum_lag_blockTest_sep {g : ℝ → ℂ} {w ℓ : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2)) (D : ℤ → ℂ)
    {n : ℕ} (c : Fin n → ℂ) {x y : ℝ} (hsep : ∀ k : ℤ, w < |k * ℓ - (x - y)|) :
    HasSum (fun m : ℤ => EF.weilTest (blockTest g ℓ c x) (blockTest g ℓ c y) (m * ℓ) * D m) 0 := by
  have hφ : ∀ (z : ℝ) (b : Fin n), Continuous (translate (z + ((b : ℕ) : ℝ) * ℓ) g) :=
    fun z b => hg.comp (continuous_sub_right _)
  have hφc : ∀ (z : ℝ) (b : Fin n), HasCompactSupport (translate (z + ((b : ℕ) : ℝ) * ℓ) g) :=
    fun z b => translate_hasCompactSupport hgc _
  have e : ∀ m : ℤ, EF.weilTest (blockTest g ℓ c x) (blockTest g ℓ c y) (m * ℓ) * D m =
      ∑ b, ∑ b', c b * conj (c b') * (EF.weilTest (translate (x + ((b : ℕ) : ℝ) * ℓ) g)
        (translate (y + ((b' : ℕ) : ℝ) * ℓ) g) (m * ℓ) * D m) := fun m => by
    unfold blockTest
    rw [weilTest_finset_sum _ _ (hφ x) (hφc x) (hφ y), Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b' _ => by ring
  rw [funext e]
  have h0 : (0 : ℂ) = ∑ b : Fin n, ∑ b' : Fin n, c b * conj (c b') * 0 := by simp
  rw [h0]
  refine hasSum_sum fun b _ => hasSum_sum fun b' _ => (hasSum_lag_translate_sep hgs D
    fun k => ?_).mul_left _
  have := hsep (k - ((b : ℕ) : ℤ) + ((b' : ℕ) : ℤ))
  convert this using 2
  push_cast
  ring

/-! ### Separated offsets and narrow bumps -/

/-- Two offsets `2iw`, `2jw` (`i ≠ j < r`) stay more than `w` apart modulo `L` when
`(2r − 1) w < L`. -/
theorem sep_offsets {L w : ℝ} (hw : 0 < w) (hL : 0 < L) {r : ℕ} (hrL : (2 * r - 1) * w < L)
    {i j : ℕ} (hi : i < r) (hj : j < r) (hij : i ≠ j) (k : ℤ) :
    w < |k * L - 2 * ((i : ℝ) - j) * w| := by
  have hi' : (i : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hj' : (j : ℝ) + 1 ≤ r := by exact_mod_cast hj
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    rw [lt_abs]; right
    nlinarith [mul_le_mul_of_nonneg_right hk' hL.le]
  · rcases Nat.lt_or_gt_of_ne hij with h | h
    · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [lt_abs]; left
      push_cast; nlinarith
    · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [lt_abs]; right
      push_cast; nlinarith
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    rw [lt_abs]; left
    nlinarith [mul_le_mul_of_nonneg_right hk' hL.le]

/-- A narrow bump: a `C²` test supported in `[−w/2, w/2]` with positive energy. -/
theorem exists_narrow_test {w : ℝ} (hw : 0 < w) :
    ∃ g : ℝ → ℂ, ContDiff ℝ 2 g ∧ tsupport g ⊆ Set.Icc (-(w / 2)) (w / 2) ∧
      0 < ∫ u, ‖g u‖ ^ 2 := by
  have hw2 : 0 < w / 2 := half_pos hw
  refine ⟨bumpTest (w / 2) hw2 0, bumpTest_contDiff hw2 0, ?_, ?_⟩
  · refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hu' : u - 0 ∈ Function.support (smallBump (w / 2) hw2) := fun h =>
      hu (show ((smallBump (w / 2) hw2 (u - 0) : ℝ) : ℂ) = 0 by rw [h, Complex.ofReal_zero])
    have hr : (smallBump (w / 2) hw2).rOut = w / 2 := rfl
    rw [ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, sub_zero, hr] at hu'
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  · have h0 : smallBump (w / 2) hw2 0 = 1 := (smallBump (w / 2) hw2).one_of_mem_closedBall
      (Metric.mem_closedBall_self (smallBump (w / 2) hw2).rIn_pos.le)
    have hval : ∀ u, ‖bumpTest (w / 2) hw2 0 u‖ ^ 2 =
        smallBump (w / 2) hw2 u * smallBump (w / 2) hw2 u := fun u => by
      simp only [bumpTest, sub_zero, Complex.norm_real, Real.norm_eq_abs, sq]
      exact abs_mul_abs_self _
    simp only [hval]
    exact ((smallBump (w / 2) hw2).continuous.mul
      (smallBump (w / 2) hw2).continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (smallBump (w / 2) hw2).hasCompactSupport.mul_left
        (fun t => mul_self_nonneg (smallBump (w / 2) hw2 t))
        (show (fun t => smallBump (w / 2) hw2 t * smallBump (w / 2) hw2 t) 0 ≠ 0 by simp [h0])

/-- `k_g(0) = ‖g‖²`. -/
theorem weilTest_self_zero (g : ℝ → ℂ) : EF.weilTest g g 0 = ((∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) := by
  rw [RHTower.weilTest_apply, ← integral_complex_ofReal]
  congr 1
  funext t
  rw [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-! ### The window filtration of a lag lattice -/

/-- **Infinite defect above the threshold.** If a tempered configuration has a lag formula and the
Toeplitz window of size `⌈2a/ℓ⌉` has a negative value, the Hodge defect at degree `a` is
infinite. -/
theorem hodgeDefectAt_eq_top_of_lagFormula (Z : ZeroConfig) (hZ : TemperedConfig Z) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (D : ℤ → ℂ) (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} {n : ℕ} (hn : n = ⌈2 * a / ℓ⌉₊) {c : Fin n → ℂ} (hc : (toeplitzForm D n c).re < 0) :
    hodgeDefectAt Z a = ⊤ := by
  classical
  -- the window is nonempty, so `(n − 1)ℓ < 2a`
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      simp [toeplitzForm] at hc
    · exact h0
  have hpos : 0 < 2 * a / ℓ := by
    by_contra h
    push Not at h
    have : ⌈2 * a / ℓ⌉₊ = 0 := Nat.ceil_eq_zero.mpr h
    omega
  have hgap : ((n : ℝ) - 1) * ℓ < 2 * a := by
    have h1 := Nat.ceil_lt_add_one hpos.le
    rw [← hn] at h1
    have : (n : ℝ) - 1 < 2 * a / ℓ := by linarith
    rwa [lt_div_iff₀ hℓ] at this
  refine top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun r _ => ?_)
  -- `r` block bases `x_i = −a + w/2 + 2iw` inside the slack
  obtain ⟨η, hη0, hηg, hηL⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 2 * a - ((n : ℝ) - 1) * ℓ ∧ η ≤ ℓ :=
    ⟨min _ _, lt_min (by linarith) hℓ, min_le_left _ _, min_le_right _ _⟩
  have hr0 : (0 : ℝ) < 2 * r + 2 := by positivity
  obtain ⟨w, hw0, hwη⟩ : ∃ w : ℝ, 0 < w ∧ (2 * r + 2) * w ≤ η :=
    ⟨η / (2 * r + 2), div_pos hη0 hr0, le_of_eq (by field_simp)⟩
  have hrw : (0 : ℝ) ≤ r * w := mul_nonneg (Nat.cast_nonneg r) hw0.le
  have hrL : (2 * r - 1) * w < ℓ := by nlinarith
  have hwL : w < ℓ := by nlinarith
  obtain ⟨g, hg, hgs, hg0⟩ := exists_narrow_test hw0
  have hgc : HasCompactSupport g := RHTower.hasCompactSupport_of_tsupport_subset_Icc hgs
  obtain ⟨x, hx⟩ : ∃ x : Fin r → ℝ, ∀ i, x i = -a + w / 2 + 2 * ((i : ℕ) : ℝ) * w :=
    ⟨_, fun _ => rfl⟩
  set h : Fin r → ℝ → ℂ := fun i => blockTest g ℓ c (x i) with hh
  have hC2 : ∀ i, ContDiff ℝ 2 (h i) := fun i => by
    simp only [hh, blockTest_eq_sum_smul]
    exact contDiff_sum_smul _ (fun b => translate_contDiff hg _) c
  have hcs : ∀ i, HasCompactSupport (h i) := fun i => by
    simp only [hh, blockTest_eq_sum_smul]
    exact hasCompactSupport_sum_smul _ (fun b => translate_hasCompactSupport hgc _) c
  -- the blocks live in `[−a, a]`
  have hsupp : ∀ i, tsupport (h i) ⊆ Set.Icc (-a) a := by
    intro i
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hout
    apply hu
    simp only [hh, blockTest, translate]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hz : g (u - (x i + ((b : ℕ) : ℝ) * ℓ)) = 0 := by
      by_contra hne
      have hmem := hgs (subset_tsupport _ hne)
      apply hout
      have hxi := hx i
      have hi : ((i : ℕ) : ℝ) + 1 ≤ r := by exact_mod_cast i.2
      have hb : ((b : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast b.2
      have hiw : 0 ≤ ((i : ℕ) : ℝ) * w := mul_nonneg (Nat.cast_nonneg _) hw0.le
      have hbL : 0 ≤ ((b : ℕ) : ℝ) * ℓ := mul_nonneg (Nat.cast_nonneg _) hℓ.le
      have hiw' : ((i : ℕ) : ℝ) * w ≤ ((r : ℝ) - 1) * w :=
        mul_le_mul_of_nonneg_right (by linarith) hw0.le
      have hbL' : ((b : ℕ) : ℝ) * ℓ ≤ ((n : ℝ) - 1) * ℓ :=
        mul_le_mul_of_nonneg_right (by linarith) hℓ.le
      constructor <;> nlinarith [hmem.1, hmem.2]
    rw [hz, mul_zero]
  -- the blocks span a negative definite space
  have hpd : IsPosDefOn (-(zeroGram Z h)) ⊤ := by
    intro y _ hy
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
    rw [hermQuad_neg, hermQuad_zeroGram_of_tempered Z hZ h hC2 hcs]
    set F : ℝ → ℂ := ∑ i, conj (y i) • h i with hF
    have hFeq : F = fun t => ∑ i, conj (y i) * h i t := by
      funext t
      simp [hF, Finset.sum_apply]
    have hFC2 : ContDiff ℝ 2 F := contDiff_sum_smul _ hC2 _
    have hFc : HasCompactSupport F := hasCompactSupport_sum_smul _ hcs _
    -- the lag sum of `F`, block by block
    have hblock : ∀ i j, HasSum (fun m : ℤ => EF.weilTest (h i) (h j) (m * ℓ) * D m)
        (if i = j then EF.weilTest g g 0 * toeplitzForm D n c else 0) := by
      intro i j
      split_ifs with hij
      · subst hij
        exact hasSum_lag_blockTest_self hℓ hg.continuous hgc hgs hwL D c (x i)
      · refine hasSum_lag_blockTest_sep hg.continuous hgc hgs D c fun k => ?_
        have := sep_offsets hw0 hℓ hrL i.2 j.2 (fun h' => hij (Fin.ext h')) k
        rw [hx i, hx j]
        convert this using 2
        ring
    have hlag : HasSum (fun m : ℤ => EF.weilTest F F (m * ℓ) * D m)
        (∑ i, ∑ j, conj (y i) * conj (conj (y j)) *
          (if i = j then EF.weilTest g g 0 * toeplitzForm D n c else 0)) := by
      have e : ∀ m : ℤ, EF.weilTest F F (m * ℓ) * D m = ∑ i, ∑ j, conj (y i) * conj (conj (y j)) *
          (EF.weilTest (h i) (h j) (m * ℓ) * D m) := fun m => by
        rw [hFeq, weilTest_finset_sum _ _ (fun i => (hC2 i).continuous) hcs
          (fun i => (hC2 i).continuous), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [funext e]
      exact hasSum_sum fun i _ => hasSum_sum fun j _ => (hblock i j).mul_left _
    have hval : ∑ i, ∑ j, conj (y i) * conj (conj (y j)) *
        (if i = j then EF.weilTest g g 0 * toeplitzForm D n c else 0) =
          ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) * (EF.weilTest g g 0 * toeplitzForm D n c) := by
      simp only [Complex.conj_conj, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.mul_conj']
      ring
    rw [hW F hFC2 hFc, hlag.tsum_eq, hval, weilTest_self_zero]
    have hy2 : 0 < ∑ i, ‖y i‖ ^ 2 :=
      lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi₀) 2)
        (Finset.single_le_sum (f := fun i => ‖y i‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i₀))
    rw [show ((ℓ : ℝ) : ℂ) * (((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) *
        (((∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) * toeplitzForm D n c)) =
          ((ℓ * (∑ i, ‖y i‖ ^ 2) * ∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) * toeplitzForm D n c by
        push_cast; ring, Complex.re_ofReal_mul]
    have : 0 < ℓ * (∑ i, ‖y i‖ ^ 2) * ∫ u, ‖g u‖ ^ 2 := by positivity
    nlinarith
  have h1 := finrank_le_posIndex hpd
  rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  exact (ENat.coe_le_coe.mpr h1).trans (le_hodgeDefectAt Z h fun i => ⟨hC2 i, hsupp i⟩)

open Classical in
/-- **The degree filtration of a lag lattice is its window filtration.** For a tempered
configuration with a lag formula and `a > 0`, the Hodge defect at degree `a` is `0` if the
Toeplitz window of size `⌈2a/ℓ⌉` is positive semidefinite and `∞` otherwise. -/
theorem hodgeDefectAt_lagFormula (Z : ZeroConfig) (hZ : TemperedConfig Z) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (D : ℤ → ℂ) (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) :
    hodgeDefectAt Z a =
      if ∀ c : Fin ⌈2 * a / ℓ⌉₊ → ℂ, 0 ≤ (toeplitzForm D ⌈2 * a / ℓ⌉₊ c).re then 0 else ⊤ := by
  split_ifs with hT
  · exact (hodgeDefectAt_eq_zero_iff Z hZ a).mpr
      ((weil_nonneg_iff_toeplitz_of_lagFormula Z hℓ D hW ha).mpr hT)
  · push Not at hT
    obtain ⟨c, hc⟩ := hT
    exact hodgeDefectAt_eq_top_of_lagFormula Z hZ hℓ D hW rfl hc

/-! ### Curves -/

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι) (hD : ∀ i, ‖D.β i‖ ≤ D.sqrtq)

/-- **The scaling surface of a curve is a lag lattice**: `ℓ = log q`, `D(m) = Σ_i β_i^{|m|}`. -/
theorem W_curveConfig_lagFormula {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (D.curveConfig hD).W f f = ((Real.log D.q : ℝ) : ℂ) *
      ∑' m : ℤ, EF.weilTest f f (m * Real.log D.q) * (D.trace m.natAbs : ℂ) := by
  have hL := D.log_q_pos
  obtain ⟨A, -, hA⟩ := GaloisForLFunctions.SquareRootThreshold.exists_radius_of_hasCompactSupport
    (EF.weilTest_hasCompactSupport hfc hfc)
  set M : ℕ := ⌈A / Real.log D.q⌉₊ with hM
  have hMA : A ≤ M * Real.log D.q := (div_le_iff₀ hL).mp (Nat.le_ceil _)
  have hKz : ∀ m : ℤ, m ∉ Icc (-(M : ℤ)) M → EF.weilTest f f (m * Real.log D.q) = 0 := by
    intro m hm
    apply hA
    simp only [Finset.mem_Icc, not_and_or, not_le] at hm
    rw [abs_mul, abs_of_pos hL]
    have hm1 : (M : ℝ) + 1 ≤ |(m : ℝ)| := by
      rcases hm with h | h
      · have h' : (m : ℝ) ≤ -(M : ℝ) - 1 := by exact_mod_cast (show m ≤ -(M : ℤ) - 1 by omega)
        rw [abs_of_neg (by linarith [Nat.cast_nonneg (α := ℝ) M])]
        linarith
      · have h' : (M : ℝ) + 1 ≤ m := by exact_mod_cast (show (M : ℤ) + 1 ≤ m by omega)
        rw [abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) M])]
        exact h'
    nlinarith
  have hfin : ∀ i, ∑' m : ℤ, EF.weilTest f f (m * Real.log D.q) * D.β i ^ m =
      ∑ m ∈ Icc (-(M : ℤ)) M, EF.weilTest f f (m * Real.log D.q) * D.β i ^ m :=
    fun i => tsum_eq_sum fun m hm => by rw [hKz m hm, zero_mul]
  have hfin' : ∑' m : ℤ, EF.weilTest f f (m * Real.log D.q) * (D.trace m.natAbs : ℂ) =
      ∑ m ∈ Icc (-(M : ℤ)) M, EF.weilTest f f (m * Real.log D.q) * (D.trace m.natAbs : ℂ) :=
    tsum_eq_sum fun m hm => by rw [hKz m hm, zero_mul]
  rw [D.W_curveConfig hD hf hfc hf.continuous hfc, ← Finset.mul_sum, hfin']
  congr 1
  simp only [hfin]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum, sum_zpow_eq_trace]

/-- The Toeplitz form of the traces is the window Gram form. -/
theorem re_toeplitzForm_trace (n : ℕ) (c : Fin n → ℂ) :
    (toeplitzForm (fun m => (D.trace m.natAbs : ℂ)) n c).re =
      hermQuad (D.spanGram n) (fun b => conj (c b)) := by
  rw [toeplitzForm, hermQuad]
  congr 1
  simp only [dotProduct, Matrix.mulVec, spanGram, Pi.star_apply, Complex.star_def,
    Complex.conj_conj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  rw [natAbs_sub_eq_dist]
  ring

theorem toeplitz_trace_nonneg_iff (n : ℕ) :
    (∀ c : Fin n → ℂ, 0 ≤ (toeplitzForm (fun m => (D.trace m.natAbs : ℂ)) n c).re) ↔
      hermNegIndex (D.spanGram n) = 0 := by
  constructor
  · intro h
    refine negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
    have := h fun b => conj (x b)
    rw [re_toeplitzForm_trace] at this
    simpa only [Complex.conj_conj] using this
  · intro h c
    rw [re_toeplitzForm_trace]
    exact hermQuad_nonneg_of_negIndex_eq_zero h _

/-- The first window `G₁ = (t₀)` is positive semidefinite. -/
theorem negIndex_spanGram_eq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) :
    hermNegIndex (D.spanGram n) = 0 := by
  refine negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
  interval_cases n
  · simp [hermQuad, dotProduct]
  · have ht : D.trace 0 = Fintype.card ι := by simp [trace, powerSum]
    simp only [hermQuad, dotProduct, Fin.sum_univ_one, Matrix.mulVec, spanGram, Pi.star_apply,
      Complex.star_def, Nat.dist_self]
    rw [show conj (x 0) * ((D.trace 0 : ℂ) * x 0) =
        ((D.trace 0 * Complex.normSq (x 0) : ℝ) : ℂ) by
      push_cast; rw [Complex.normSq_eq_conj_mul_self]; ring, Complex.ofReal_re]
    exact mul_nonneg (by rw [ht]; positivity) (Complex.normSq_nonneg _)

/-- **The degree filtration of a curve is its window filtration.** On the scaling surface of a
curve datum in the strip, the Hodge defect at degree `a` is `0` if the Frobenius window of size
`⌈2a / log q⌉` is positive semidefinite and `∞` otherwise. -/
theorem hodgeDefectAt_curveConfig (a : ℝ) :
    hodgeDefectAt (D.curveConfig hD) a =
      if hermNegIndex (D.spanGram ⌈2 * a / Real.log D.q⌉₊) = 0 then 0 else ⊤ := by
  have hL := D.log_q_pos
  have key : ∀ a : ℝ, 0 < a → hodgeDefectAt (D.curveConfig hD) a =
      if hermNegIndex (D.spanGram ⌈2 * a / Real.log D.q⌉₊) = 0 then 0 else ⊤ := fun a ha => by
    rw [hodgeDefectAt_lagFormula _ (D.temperedConfig_curveConfig hD) hL _
      (fun f hf hfc => D.W_curveConfig_lagFormula hD hf hfc) ha]
    simp only [D.toeplitz_trace_nonneg_iff]
  rcases lt_or_ge 0 a with ha | ha
  · exact key a ha
  · have hn : ⌈2 * a / Real.log D.q⌉₊ = 0 :=
      Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le)
    have hhalf := key (Real.log D.q / 2) (half_pos hL)
    rw [show 2 * (Real.log D.q / 2) / Real.log D.q = 1 by field_simp, Nat.ceil_one,
      if_pos (D.negIndex_spanGram_eq_zero_of_le_one le_rfl)] at hhalf
    rw [hn, if_pos (D.negIndex_spanGram_eq_zero_of_le_one (Nat.zero_le 1))]
    exact le_antisymm (hhalf ▸ hodgeDefectAt_mono _ (by linarith)) zero_le

/-- **Every curve satisfies the Hodge index up to degree `log q / 2`.** -/
theorem hodgeDefectAt_curveConfig_eq_zero_of_le {a : ℝ} (ha : a ≤ Real.log D.q / 2) :
    hodgeDefectAt (D.curveConfig hD) a = 0 := by
  have hn : ⌈2 * a / Real.log D.q⌉₊ ≤ 1 :=
    Nat.ceil_le.mpr (by rw [Nat.cast_one, div_le_iff₀ D.log_q_pos]; linarith)
  rw [D.hodgeDefectAt_curveConfig hD, if_pos (D.negIndex_spanGram_eq_zero_of_le_one hn)]

/-- **Purity decides the defect from the window `2g` on.** Once `⌈2a / log q⌉` reaches the number of
eigenvalues, the Hodge defect at degree `a` is `0` if no eigenvalue lies outside the unit circle and
`∞` otherwise. -/
theorem hodgeDefectAt_curveConfig_of_card_le {a : ℝ}
    (ha : Fintype.card ι ≤ ⌈2 * a / Real.log D.q⌉₊) :
    hodgeDefectAt (D.curveConfig hD) a = if D.outerSpectrum = ∅ then 0 else ⊤ := by
  rw [D.hodgeDefectAt_curveConfig hD, D.pontryagin_law_curve.2 _ ha]
  simp only [Finset.card_eq_zero]

end CurveDatum

open Real in
/-- **The golden fake curve.** Its Hodge defect vanishes up to degree `log 5 / 2` and is infinite
beyond: the window `G₂` already carries the negative square of `φ`. -/
theorem goldenDatum_hodgeDefectAt (a : ℝ) :
    hodgeDefectAt (goldenDatum.curveConfig goldenDatum_strip) a =
      if a ≤ Real.log 5 / 2 then 0 else ⊤ := by
  have hq : goldenDatum.q = 5 := rfl
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [goldenDatum.hodgeDefectAt_curveConfig goldenDatum_strip, hq]
  by_cases ha : a ≤ Real.log 5 / 2
  · have hn : ⌈2 * a / Real.log 5⌉₊ ≤ 1 :=
      Nat.ceil_le.mpr (by rw [Nat.cast_one, div_le_iff₀ h5]; linarith)
    rw [if_pos (goldenDatum.negIndex_spanGram_eq_zero_of_le_one hn), if_pos ha]
  · have hn : 2 ≤ ⌈2 * a / Real.log 5⌉₊ := by
      have h1 : ((1 : ℕ) : ℝ) < 2 * a / Real.log 5 := by
        rw [Nat.cast_one, lt_div_iff₀ h5]; push Not at ha; linarith
      have := Nat.lt_ceil.mpr h1
      omega
    rw [if_neg (by rw [goldenDatum_negIndex_spanGram hn]; norm_num), if_neg ha]

/-! ### Off-line lattices -/

/-- **The off-line lattice jumps from `0` to `∞` at its Nyquist degree.** The lattice
`{½ ± δ + 2πik/L}` has Hodge defect `0` at every degree `a ≤ L/2` and `∞` at every degree
`a > L/2`. -/
theorem hodgeDefectAt_offLineLattice {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (a : ℝ) :
    hodgeDefectAt (RHTower.offLineLatticeConfig hL hδ hδ') a = if a ≤ L / 2 then 0 else ⊤ := by
  have hZ := GaloisForLFunctions.SquareRootThreshold.temperedConfig_offLineLatticeConfig hL hδ hδ'
  have hW := fun f hf hfc =>
    GaloisForLFunctions.SquareRootThreshold.W_offLineLatticeConfig_lagFormula hL hδ hδ' f hf hfc
  split_ifs with ha
  · exact (hodgeDefectAt_eq_zero_iff _ hZ a).mpr
      ((RHTower.offLineLattice_weil_positive_iff hL hδ hδ' a).mpr ha)
  · have hpos : 0 < a := by linarith
    have hnot : ¬ ∀ c : Fin ⌈2 * a / L⌉₊ → ℂ, 0 ≤ (toeplitzForm
        (fun m : ℤ => (((2 * Real.cosh (δ * (m * L))) : ℝ) : ℂ)) ⌈2 * a / L⌉₊ c).re :=
      fun hT => ha ((RHTower.offLineLattice_weil_positive_iff hL hδ hδ' a).mp
        ((weil_nonneg_iff_toeplitz_of_lagFormula _ hL _ hW hpos).mpr hT))
    push Not at hnot
    obtain ⟨c, hc⟩ := hnot
    exact hodgeDefectAt_eq_top_of_lagFormula _ hZ hL _ hW rfl hc

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
