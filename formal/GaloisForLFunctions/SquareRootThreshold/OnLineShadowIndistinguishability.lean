import GaloisForLFunctions.SquareRootThreshold.HodgeIndexOnLagLatticeConfigurations
import GaloisForLFunctions.HTGeometry.CaratheodoryFejerPSDtoAtomicFactorization

/-!
# On-line shadows: invisibility is mimicry

A *weighted on-line periodic configuration* puts weight `w_k ≥ 0` at the ordinates
`c_k + 2πj/ℓ`, `j ∈ ℤ`, on the critical line. Its Weil form is manifestly nonnegative:

`Sh(f) = Σ_k w_k Σ_j |h_f(c_k + 2πj/ℓ)|²`  (`onLineShadow`).

**Indistinguishability principle** (`weil_nonneg_iff_onLineShadow_of_lagFormula`). Let `Z` have a
lag formula `W(f, f) = ℓ Σ_m k(mℓ) D(m)` with Hermitian symbol and `D(0) = d₀ > 0`. Then `Z` is
invisible at aperture `a` iff there is a weighted on-line periodic configuration with

* the same Weil form as `Z` on every test of aperture `a`,
* the same zero count `Σ_k w_k = d₀` per period `2π/ℓ`,
* at most `2⌈2a/ℓ⌉ − 1` ordinates per period.

So hiding is exactly mimicry: below its visibility aperture an off-line configuration *is*, for
every test the aperture allows, an on-line configuration of the same density. The proof turns the
positive semidefinite Toeplitz section of size `n = ⌈2a/ℓ⌉` (the Toeplitz law) into a finite atomic
measure on the circle by the Carathéodory–Fejér factorization
(`HTGeometry.exists_atomic_caratheodoryFejer_psd_factorization`); each atom `e^{iφ}` becomes an
on-line translate `φ/ℓ + 2πℤ/ℓ`, by Poisson summation, and the test kernel does not see lags
beyond `2a`.

The principle applies to periodic depth profiles, periodic off-line patterns and the off-line
lattice (`profileConfig_weil_nonneg_iff_onLineShadow`, `patternConfig_weil_nonneg_iff_onLineShadow`,
`offLineLattice_onLineShadow`), and, by polar blindness, to the Hodge index
(`hodgeIndex_iff_onLineShadow_of_lagFormula`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.HTGeometry

/-! ### Weighted on-line periodic configurations -/

/-- The Weil form of the weighted on-line configuration with weight `w_k` at `c_k + 2πℤ/ℓ`. -/
def onLineShadow (ℓ : ℝ) {r : ℕ} (c w : Fin r → ℝ) (f : ℝ → ℂ) : ℝ :=
  ∑ k, w k * ∑' j : ℤ, ‖paperFT f ((c k + j * (2 * π / ℓ) : ℝ) : ℂ)‖ ^ 2

theorem onLineShadow_nonneg (ℓ : ℝ) {r : ℕ} (c : Fin r → ℝ) {w : Fin r → ℝ}
    (hw : ∀ k, 0 ≤ w k) (f : ℝ → ℂ) : 0 ≤ onLineShadow ℓ c w f :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (tsum_nonneg fun _ => sq_nonneg _)

/-- A test of aperture `a` has Weil kernel vanishing at every lag `|v| ≥ 2a`. -/
theorem weilTest_eq_zero_of_two_mul_le {f : ℝ → ℂ} (hf : Continuous f) {a : ℝ}
    (hfs : tsupport f ⊆ Icc (-a) a) {v : ℝ} (hv : 2 * a ≤ |v|) : EF.weilTest f f v = 0 := by
  rw [weilTest_apply]
  have hfz : ∀ t, a ≤ |t| → f t = 0 := fun t ht => eq_zero_of_tsupport_subset_Icc hf hfs ht
  have hpt : ∀ t, f t * conj (f (t - v)) = 0 := by
    intro t
    by_cases ht : a ≤ |t|
    · rw [hfz t ht, zero_mul]
    · push Not at ht
      have h1 := abs_sub_abs_le_abs_sub v t
      rw [abs_sub_comm] at h1
      rw [hfz (t - v) (by linarith), map_zero, mul_zero]
  simp_rw [hpt, integral_zero]

/-- **Poisson for one on-line translate.** `ℓ Σ_m k(mℓ) e^{icmℓ} = Σ_j |h_f(c + 2πj/ℓ)|²`. -/
theorem lagSum_translate_eq_onLine {ℓ A : ℝ} (hℓ : 0 < ℓ) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(A / 2)) (A / 2)) (c : ℝ) :
    ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * cexp (I * c * (m * ℓ)) =
      ((∑' j : ℤ, ‖paperFT f ((c + j * (2 * π / ℓ) : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have h := hasSum_paperFT_translate hℓ (EF.weilTest_contDiff hf hf.continuous hfc)
    (weilTest_abs_le hfs hfs) c 0
  simp only [Complex.ofReal_zero, mul_zero, sub_zero, zero_mul, Real.exp_zero,
    Complex.ofReal_one, mul_one] at h
  have hpt : ∀ j : ℤ, paperFT (EF.weilTest f f) ((c + j * (2 * π / ℓ) : ℝ) : ℂ) =
      ((‖paperFT f ((c + j * (2 * π / ℓ) : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, Complex.conj_ofReal,
      Complex.mul_conj']
    push_cast
    ring
  simp_rw [hpt] at h
  rw [Complex.ofReal_tsum, h.tsum_eq]

/-! ### Hermitian Toeplitz sections and the Carathéodory–Fejér factorization -/

/-- A Hermitian symbol has real Toeplitz forms. -/
theorem toeplitzForm_im_eq_zero {D : ℤ → ℂ} (hD : ∀ m, D (-m) = conj (D m)) {n : ℕ}
    (c : Fin n → ℂ) : (toeplitzForm D n c).im = 0 := by
  have h : conj (toeplitzForm D n c) = toeplitzForm D n c := by
    simp only [toeplitzForm, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    rw [← hD, neg_sub]
    ring
  exact Complex.conj_eq_iff_im.mp h

/-- The normalized moment matrix `[D(k − j)/d₀]` of a Toeplitz-positive symbol is positive
semidefinite. -/
theorem circleToeplitzGram_posSemidef {D : ℤ → ℂ} (hD : ∀ m, D (-m) = conj (D m)) {d₀ : ℝ}
    (hd₀ : 0 < d₀) {N : ℕ} (hT : ∀ c : Fin (N + 1) → ℂ, 0 ≤ (toeplitzForm D (N + 1) c).re) :
    (circleToeplitzGram N fun q => D (-q) / d₀).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun j k => ?_
    simp only [circleToeplitzGram, Complex.star_def, map_div₀, Complex.conj_ofReal]
    rw [← hD]
    congr 2
    ring
  · have heq : dotProduct (star x) ((circleToeplitzGram N fun q => D (-q) / d₀).mulVec x) =
        toeplitzForm D (N + 1) x / d₀ := by
      simp only [dotProduct, Matrix.mulVec, circleToeplitzGram, toeplitzForm, Finset.sum_div,
        Finset.mul_sum, Pi.star_apply, Complex.star_def]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [neg_sub]
      ring
    rw [heq, Complex.nonneg_iff, Complex.div_ofReal_re, Complex.div_ofReal_im,
      toeplitzForm_im_eq_zero hD x, zero_div]
    exact ⟨div_nonneg (hT x) hd₀.le, rfl⟩

/-- **Atomic symbols.** A Hermitian Toeplitz-positive symbol with `D(0) = d₀ > 0` agrees on
`|m| ≤ N` with `Σ_i w_i e^{iφ_i m}`, for `2N + 1` atoms of weights `w_i ≥ 0`, `Σ w_i = d₀`. -/
theorem exists_atomic_lagSymbol {D : ℤ → ℂ} (hD : ∀ m, D (-m) = conj (D m)) {d₀ : ℝ}
    (hd₀ : 0 < d₀) (hD0 : D 0 = d₀) {N : ℕ}
    (hT : ∀ c : Fin (N + 1) → ℂ, 0 ≤ (toeplitzForm D (N + 1) c).re) :
    ∃ w φ : Fin (N + N + 1) → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = d₀ ∧
      ∀ m : ℤ, |m| ≤ N → D m = ∑ i, (w i : ℂ) * cexp (I * φ i * m) := by
  have hd₀c : (d₀ : ℂ) ≠ 0 := by exact_mod_cast hd₀.ne'
  have hherm : IsHermitianMoment fun q => D (-q) / d₀ := by
    intro r
    simp only [neg_neg, Complex.star_def, map_div₀, Complex.conj_ofReal]
    rw [hD, Complex.conj_conj]
  have h0 : (fun q => D (-q) / d₀) 0 = 1 := by simp [hD0, hd₀c]
  obtain ⟨weight, node, hw, hnode, hG⟩ := exists_atomic_caratheodoryFejer_psd_factorization _
    hherm h0 (circleToeplitzGram_posSemidef hD hd₀ hT)
  rw [caratheodoryFejerAtomicGram_eq_circleAtomicToeplitz node weight hw hnode] at hG
  -- the two-sided moment identity
  have hmom : ∀ q : ℤ, |q| ≤ N → D (-q) / d₀ = circleAtomicMoment node weight q := by
    intro q hq
    rw [abs_le] at hq
    rcases le_or_gt 0 q with h | h
    · lift q to ℕ using h
      have := congrFun (congrFun hG ⟨q, by omega⟩) ⟨0, by omega⟩
      simpa [circleToeplitzGram] using this
    · have := congrFun (congrFun hG ⟨0, by omega⟩) ⟨(-q).toNat, by omega⟩
      simp only [circleToeplitzGram] at this
      rwa [show ((0 : ℕ) : ℤ) - (((-q).toNat : ℕ) : ℤ) = q by omega] at this
  have hnode' : ∀ i, node i = cexp ((node i).arg * I) := fun i => by
    have := Complex.norm_mul_exp_arg_mul_I (node i)
    rw [hnode i, Complex.ofReal_one, one_mul] at this
    exact this.symm
  refine ⟨fun i => d₀ * weight i, fun i => (node i).arg, fun i => mul_nonneg hd₀.le (hw i),
    ?_, fun m hm => ?_⟩
  · have := hmom 0 (by simp)
    simp only [neg_zero, hD0, div_self hd₀c, circleAtomicMoment, zpow_zero, mul_one] at this
    rw [← Finset.mul_sum]
    have h1 : ∑ i, weight i = 1 := by exact_mod_cast this.symm
    rw [h1, mul_one]
  · have := hmom (-m) (by rwa [abs_neg])
    rw [neg_neg, div_eq_iff hd₀c, circleAtomicMoment, Finset.sum_mul] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_neg, hnode' i, ← Complex.exp_int_mul]
    push_cast
    ring_nf

/-! ### The indistinguishability principle -/

/-- **Indistinguishability principle.** A configuration with lag formula
`W(f, f) = ℓ Σ_m k(mℓ) D(m)`, Hermitian symbol and `D(0) = d₀ > 0` is invisible at aperture `a`
iff some weighted on-line periodic configuration with `2⌈2a/ℓ⌉ − 1` ordinates and `d₀` zeros per
period has the same Weil form on every test of aperture `a`. -/
theorem weil_nonneg_iff_onLineShadow_of_lagFormula (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (D : ℤ → ℂ) (hD : ∀ m, D (-m) = conj (D m)) {d₀ : ℝ} (hd₀ : 0 < d₀) (hD0 : D 0 = d₀)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → 0 ≤ (Z.W f f).re) ↔
      ∃ (r : ℕ) (c w : Fin r → ℝ), r + 1 = 2 * ⌈2 * a / ℓ⌉₊ ∧ (∀ k, 0 ≤ w k) ∧
        ∑ k, w k = d₀ ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          Z.W f f = ((onLineShadow ℓ c w f : ℝ) : ℂ) := by
  constructor
  · intro h
    rw [weil_nonneg_iff_toeplitz_of_lagFormula Z hℓ D hW ha] at h
    obtain ⟨N, hN⟩ : ∃ N, ⌈2 * a / ℓ⌉₊ = N + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ceil_pos.mpr (by positivity)).ne'
    rw [hN] at h
    obtain ⟨w, φ, hw, hsum, hrep⟩ := exists_atomic_lagSymbol hD hd₀ hD0 h
    refine ⟨N + N + 1, fun i => φ i / ℓ, w, by omega, hw, hsum, fun f hf hfs => ?_⟩
    have hfs' : tsupport f ⊆ Icc (-(2 * a / 2)) (2 * a / 2) := by
      rwa [show 2 * a / 2 = a by ring]
    have hn : 2 * a ≤ ((N : ℝ) + 1) * ℓ := by
      have := Nat.le_ceil (2 * a / ℓ)
      rw [hN, div_le_iff₀ hℓ] at this
      exact_mod_cast this
    set S : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hS
    have hk0 : ∀ m : ℤ, m ∉ S → EF.weilTest f f (m * ℓ) = 0 := by
      intro m hm
      apply weilTest_eq_zero_of_two_mul_le hf.continuous hfs
      rw [hS, Finset.mem_Icc, not_and_or, not_le, not_le] at hm
      have hm' : (N : ℝ) + 1 ≤ |(m : ℝ)| := by
        rcases hm with h1 | h1
        · have : (m : ℝ) ≤ -(N : ℝ) - 1 := by exact_mod_cast (by omega : m ≤ -(N : ℤ) - 1)
          rw [abs_of_neg (by linarith)]
          linarith
        · have : (N : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : (N : ℤ) + 1 ≤ m)
          rw [abs_of_pos (by linarith)]
          linarith
      rw [abs_mul, abs_of_pos hℓ]
      nlinarith
    have hlag : ∀ x : ℝ, ∑' m : ℤ, EF.weilTest f f (m * ℓ) * cexp (I * x * (m * ℓ)) =
        ∑ m ∈ S, EF.weilTest f f (m * ℓ) * cexp (I * x * (m * ℓ)) := fun x =>
      tsum_eq_sum fun m hm => by rw [hk0 m hm, zero_mul]
    rw [hW f hf (hasCompactSupport_of_tsupport_subset_Icc hfs),
      tsum_eq_sum fun m hm => by rw [hk0 m hm, zero_mul]]
    have hrep' : ∀ m ∈ S, EF.weilTest f f (m * ℓ) * D m = ∑ i, (w i : ℂ) *
        (EF.weilTest f f (m * ℓ) * cexp (I * ((φ i / ℓ : ℝ) : ℂ) * (m * ℓ))) := by
      intro m hm
      rw [hS, Finset.mem_Icc] at hm
      rw [hrep m (abs_le.mpr ⟨hm.1, hm.2⟩), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
      have : I * ((φ i / ℓ : ℝ) : ℂ) * ((m : ℂ) * (ℓ : ℂ)) = I * (φ i : ℂ) * m := by
        push_cast
        field_simp
      rw [this]
      ring
    rw [Finset.sum_congr rfl hrep', Finset.sum_comm, Finset.mul_sum, onLineShadow,
      Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, Complex.ofReal_mul, ← lagSum_translate_eq_onLine hℓ hf hfs' (φ i / ℓ),
      hlag]
    ring
  · rintro ⟨r, c, w, -, hw, -, hsh⟩ f hf hfs
    rw [hsh f hf hfs, Complex.ofReal_re]
    exact onLineShadow_nonneg ℓ c hw f

/-- **Indistinguishability for the Hodge index.** The same shadow criterion characterizes the
level-`a` Hodge index of a lag-lattice configuration. -/
theorem hodgeIndex_iff_onLineShadow_of_lagFormula (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (D : ℤ → ℂ) (hD : ∀ m, D (-m) = conj (D m)) {d₀ : ℝ} (hd₀ : 0 < d₀) (hD0 : D 0 = d₀)
    (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m)
    {a : ℝ} (ha : 0 < a) :
    HodgeIndexAtLevel Z a ↔
      ∃ (r : ℕ) (c w : Fin r → ℝ), r + 1 = 2 * ⌈2 * a / ℓ⌉₊ ∧ (∀ k, 0 ≤ w k) ∧
        ∑ k, w k = d₀ ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          Z.W f f = ((onLineShadow ℓ c w f : ℝ) : ℂ) := by
  rw [hodgeIndex_iff_weil_nonneg_of_lagFormula Z hℓ D hW ha]
  exact weil_nonneg_iff_onLineShadow_of_lagFormula Z hℓ D hD hd₀ hD0 hW ha

/-! ### Periodic configurations -/

/-- **Shadows of periodic depth profiles.** A profile of period `P` on the lattice `2πℤ/L` hides at
aperture `a` iff it has an on-line shadow with `2⌈2aP/L⌉ − 1` ordinates and `2P` zeros per period
`2πP/L`. -/
theorem profileConfig_weil_nonneg_iff_onLineShadow {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {a : ℝ} (ha : 0 < a) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((profileConfig hL hP d hd0 hd1).W f f).re) ↔
      ∃ (r : ℕ) (c w : Fin r → ℝ), r + 1 = 2 * ⌈2 * a / (L / P)⌉₊ ∧ (∀ k, 0 ≤ w k) ∧
        ∑ k, w k = 2 * P ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          (profileConfig hL hP d hd0 hd1).W f f = ((onLineShadow (L / P) c w f : ℝ) : ℂ) :=
  weil_nonneg_iff_onLineShadow_of_lagFormula _ (div_pos hL (by exact_mod_cast hP)) _
    (depthSymbol_neg L d) (by positivity) (by rw [depthSymbol_zero]; push_cast; ring)
    (fun _ hf hfc => W_profileConfig_lag hL hP d hd0 hd1 hf hfc) ha

/-- **Shadows of periodic off-line patterns.** -/
theorem patternConfig_weil_nonneg_iff_onLineShadow {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (hP : 0 < P)
    (c d : Fin P → ℝ) (hd0 : ∀ r, 0 < d r) (hd1 : ∀ r, d r ≤ 1 / 2)
    (hc : ∀ r r' : Fin P, ∀ j j' : ℤ, c r + j * (2 * π / ℓ) = c r' + j' * (2 * π / ℓ) →
      r = r' ∧ j = j') {a : ℝ} (ha : 0 < a) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((patternConfig hℓ c d hd0 hd1).W f f).re) ↔
      ∃ (r : ℕ) (c' w : Fin r → ℝ), r + 1 = 2 * ⌈2 * a / ℓ⌉₊ ∧ (∀ k, 0 ≤ w k) ∧
        ∑ k, w k = 2 * P ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          (patternConfig hℓ c d hd0 hd1).W f f = ((onLineShadow ℓ c' w f : ℝ) : ℂ) :=
  weil_nonneg_iff_onLineShadow_of_lagFormula _ hℓ _ (patternSymbol_neg ℓ c d) (by positivity)
    (by rw [patternSymbol_zero]; push_cast; ring)
    (fun _ hf hfc => W_patternConfig hℓ c d hd0 hd1 hc hf hfc) ha

/-- **The off-line lattice below Nyquist.** For `a ≤ L/2` the lattice `{½ ± δ + 2πik/L}` has a
one-ordinate on-line shadow of weight `2`: the doubled on-line lattice, translated. -/
theorem offLineLattice_onLineShadow {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2) :
    ∃ (c w : Fin 1 → ℝ), w 0 = 2 ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      (offLineLatticeConfig hL hδ hδ').W f f = ((onLineShadow L c w f : ℝ) : ℂ) := by
  have hD : ∀ m : ℤ, (((2 * Real.cosh (δ * ((-m : ℤ) * L))) : ℝ) : ℂ) =
      conj (((2 * Real.cosh (δ * (m * L))) : ℝ) : ℂ) := by
    intro m
    rw [Complex.conj_ofReal, Int.cast_neg, neg_mul, mul_neg, Real.cosh_neg]
  obtain ⟨r, c, w, hr, hw, hsum, hsh⟩ := (weil_nonneg_iff_onLineShadow_of_lagFormula
    (offLineLatticeConfig hL hδ hδ') hL (fun m : ℤ => (((2 * Real.cosh (δ * (m * L))) : ℝ) : ℂ))
    hD (d₀ := 2) (by norm_num) (by simp)
    (fun _ hf hfc => W_offLineLatticeConfig_lag hL hδ hδ' hf hfc) ha).mp
    ((offLineLattice_weil_positive_iff hL hδ hδ' a).mpr haL)
  have hn : ⌈2 * a / L⌉₊ = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num)]
    constructor
    · push_cast; positivity
    · rw [div_le_iff₀ hL]; push_cast; linarith
  rw [hn] at hr
  obtain rfl : r = 1 := by omega
  refine ⟨c, w, ?_, hsh⟩
  simpa using hsum

end GaloisForLFunctions.SquareRootThreshold
