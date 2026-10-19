import GaloisForLFunctions.SquareRootThreshold.ProfileRigidityAtTheSquareRootThreshold
import GaloisForLFunctions.SquareRootThreshold.OnLineNyquistPinning

/-!
# A variational principle for crystals

A periodic off-line pattern with `P` reflected pairs per period `2π/ℓ` carries `2P` zeros per
period, and no Weil form of such a lag-lattice configuration can beat the on-line value: some test
of every aperture has `Re W(f, f) ≤ 2Pℓ ∫|f|²` (`exists_weil_le_diagonal`), because the Toeplitz
floor never exceeds the diagonal `D(0) = 2P`.

**Variational principle** (`crystal_iff_weil_floor_diagonal`, `crystal_iff_hodge_floor_diagonal`).
At uniform depth `δ`, at every scale `ℓ` and every aperture `a ∈ ((P − 1)ℓ/2, Pℓ/2]`, the pattern
attains the maximal floor, `Re W(f, f) ≥ 2Pℓ ∫|f|²` on all tests (equivalently on all
polar-constrained tests) of aperture `a`, iff it is a crystal: `P(θ_r − θ_{r'}) ∈ ℤ`.

The proof: a Hermitian Toeplitz section whose floor equals its diagonal is diagonal
(`eq_zero_of_toeplitz_floor_diagonal`, the `2 × 2` minors of `T − D(0)`); at uniform depth the
off-diagonal modes are `2cosh(δmℓ)` times the power sums of the phases, and vanishing power sums
`p_1, …, p_{P−1}` force one common `P`-th power (Newton).

So among uniform-depth periodic off-line patterns of a given density the crystal is, at every
height, exactly the one that the Weil form cannot tell apart from on-line zeros up to the
square-root threshold: this is a non-asymptotic counterpart of crystal rigidity.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Diagonal floors force diagonal sections.** If a Hermitian Toeplitz section of size `n` has
floor `Re D(0)`, all modes `0 < |m| < n` vanish. -/
theorem eq_zero_of_toeplitz_floor_diagonal {D : ℤ → ℂ} (hD : ∀ m, D (-m) = conj (D m)) {n : ℕ}
    (hT : ∀ c : Fin n → ℂ, (D 0).re * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D n c).re) {m : ℤ}
    (hm0 : m ≠ 0) (hm : |m| < n) : D m = 0 := by
  have hD0 : (D 0).im = 0 := by
    have := hD 0
    rw [neg_zero] at this
    exact Complex.conj_eq_iff_im.mp this.symm
  have hE : ∀ k, shiftSymbol D (D 0).re (-k) = conj (shiftSymbol D (D 0).re k) := by
    intro k
    simp only [shiftSymbol, lagDelta, neg_eq_zero, map_sub, map_mul, Complex.conj_ofReal, hD]
    split_ifs <;> simp
  have hT' : ∀ c : Fin n → ℂ, 0 ≤ (toeplitzForm (shiftSymbol D (D 0).re) n c).re := fun c => by
    rw [toeplitzForm_shiftSymbol, Complex.sub_re, Complex.ofReal_re]
    linarith [hT c]
  have hE0 : (shiftSymbol D (D 0).re 0).re = 0 := by
    simp [shiftSymbol, lagDelta]
  have hpos : ∀ k : ℕ, 1 ≤ k → (k : ℤ) < n → D k = 0 := by
    intro k hk1 hkn
    have h1 := norm_le_of_toeplitzForm_nonneg hE hT' hk1 (by exact_mod_cast hkn)
    rw [hE0] at h1
    have h2 : shiftSymbol D (D 0).re k = D k := by
      simp only [shiftSymbol, lagDelta]
      rw [if_neg (by exact_mod_cast (by omega : k ≠ 0)), mul_zero, sub_zero]
    rw [h2] at h1
    exact norm_le_zero_iff.mp h1
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · exact hpos k (by omega) (by rw [abs_of_nonneg (by positivity)] at hm; exact hm)
  · rw [hD, hpos k (by omega) (by rw [abs_neg, abs_of_nonneg (by positivity)] at hm; exact hm),
      map_zero]

/-- The Toeplitz floor never exceeds the diagonal: `Re T(e₀) = Re D(0)`. -/
theorem exists_toeplitz_le_diagonal (D : ℤ → ℂ) {n : ℕ} (hn : 0 < n) :
    ∃ c : Fin n → ℂ, ∑ j, ‖c j‖ ^ 2 = 1 ∧ (toeplitzForm D n c).re = (D 0).re := by
  refine ⟨Pi.single ⟨0, hn⟩ 1, ?_, ?_⟩
  · rw [Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj => by simp [hj])
      (by simp)]
    simp
  · simp [toeplitzForm, Pi.single_apply]

/-- **No lag-lattice configuration beats its diagonal.** At every aperture `a > 0` some test has
`Re W(f, f) ≤ ℓ Re D(0) ∫|f|²`, with `∫|f|² > 0`. -/
theorem exists_weil_le_diagonal (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (D : ℤ → ℂ)
    {a : ℝ} (ha : 0 < a) (hW : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      Z.W f f = ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ 0 < ∫ t, ‖f t‖ ^ 2 ∧
      (Z.W f f).re ≤ ℓ * (D 0).re * ∫ t, ‖f t‖ ^ 2 := by
  have hn : 0 < ⌈2 * a / ℓ⌉₊ := Nat.ceil_pos.mpr (by positivity)
  obtain ⟨c, hc1, hc⟩ := exists_toeplitz_le_diagonal D hn
  obtain ⟨f, hf, hfs, B, hB, hlag⟩ := exists_bumpTest_universal hℓ ha c
  have hmass := hlag lagDelta
  have hl : ∑' m : ℤ, EF.weilTest f f (m * ℓ) * lagDelta m = EF.weilTest f f 0 := by
    rw [tsum_eq_single 0 fun m hm => by rw [lagDelta, if_neg hm, mul_zero]]
    rw [lagDelta, if_pos rfl, mul_one, Int.cast_zero, zero_mul]
  rw [hl, weilTest_self_zero, toeplitzForm_lagDelta, hc1, Complex.ofReal_one, mul_one] at hmass
  have hmass' : ∫ t, ‖f t‖ ^ 2 = B := by exact_mod_cast hmass
  refine ⟨f, hf, hfs, by rw [hmass']; exact hB, le_of_eq ?_⟩
  rw [hW f hf hfs, hlag D, ← mul_assoc, show ((ℓ : ℝ) : ℂ) * (B : ℂ) = ((ℓ * B : ℝ) : ℂ) by
    push_cast; ring, Complex.re_ofReal_mul, hc, hmass']
  ring

/-- At uniform depth the modes of a pattern are `2cosh(δmℓ)` times the power sums of its phases. -/
theorem patternSymbol_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) {P : ℕ} (θ : Fin P → ℝ) (δ : ℝ) (m : ℕ) :
    patternSymbol ℓ (scaledOffset ℓ θ) (fun _ => δ) m =
      ((2 * Real.cosh (δ * (m * ℓ)) : ℝ) : ℂ) * ∑ r, phasePoint θ r ^ m := by
  rw [patternSymbol_scaledOffset hℓ, Finset.mul_sum]

/-- **Variational principle for crystals.** At uniform depth, at every scale `ℓ` and every aperture
`a ∈ ((P − 1)ℓ/2, Pℓ/2]`, the pattern satisfies `Re W(f, f) ≥ 2Pℓ ∫|f|²` on all tests of
aperture `a` iff it is a crystal. -/
theorem crystal_iff_weil_floor_diagonal {P : ℕ} (hP : 0 < P) (θ : Fin P → ℝ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℝ} (ha1 : ((P : ℝ) - 1) * ℓ / 2 < a) (ha2 : a ≤ P * ℓ / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        ℓ * (2 * P) * ∫ t, ‖f t‖ ^ 2 ≤
          ((patternConfig hℓ (scaledOffset ℓ θ) (fun _ => δ) (fun _ => hδ0)
            (fun _ => hδ1)).W f f).re) ↔
      ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k := by
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have ha0 : 0 < a := lt_of_le_of_lt (by
    have : 0 ≤ ((P : ℝ) - 1) * ℓ := mul_nonneg (by linarith) hℓ.le
    linarith) ha1
  have hn : ⌈2 * a / ℓ⌉₊ = P := by
    rw [Nat.ceil_eq_iff (by omega)]
    constructor
    · rw [lt_div_iff₀ hℓ]
      have : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ P), Nat.cast_one]
      rw [this]; linarith
    · rw [div_le_iff₀ hℓ]; linarith
  set D := patternSymbol ℓ (scaledOffset ℓ θ) (fun _ => δ) with hDdef
  have hD0 : D 0 = 2 * P := patternSymbol_zero _ _ _
  have hD0re : (D 0).re = 2 * P := by rw [hD0]; simp
  rw [weil_floor_iff_toeplitz_floor _ hℓ D (fun _ hf hfc => W_patternConfig hℓ _ _ _ _
    (scaledOffset_injective hℓ hθ) hf hfc) ha0, hn]
  constructor
  · intro hT
    have hT' : ∀ c : Fin P → ℂ, (D 0).re * ∑ j, ‖c j‖ ^ 2 ≤ (toeplitzForm D P c).re := by
      rw [hD0re]; exact hT
    have hsum : ∀ m : ℕ, 1 ≤ m → m < P → ∑ r, phasePoint θ r ^ m = 0 := by
      intro m hm1 hmP
      have h0 := eq_zero_of_toeplitz_floor_diagonal (patternSymbol_neg ℓ _ _) hT'
        (m := m) (by exact_mod_cast (by omega : m ≠ 0))
        (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hmP)
      have h0' : patternSymbol ℓ (scaledOffset ℓ θ) (fun _ => δ) m = 0 := h0
      rw [patternSymbol_uniform hℓ] at h0'
      have hc : ((2 * Real.cosh (δ * (m * ℓ)) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.cosh (δ * (m * ℓ))).ne'
      exact (mul_eq_zero.mp h0').resolve_left hc
    intro r r'
    have := pow_card_eq_of_powerSums (phasePoint θ) (fun m hm1 hmP => by
      rw [Fintype.card_fin] at hmP; exact hsum m hm1 hmP) r r'
    rw [Fintype.card_fin] at this
    exact exists_int_of_phasePoint_pow_eq θ this
  · intro hcr c
    -- all off-diagonal modes vanish
    have hmode : ∀ k : ℕ, 1 ≤ k → k < P → D k = 0 := by
      intro k hk1 hkP
      rw [hDdef, patternSymbol_uniform hℓ, powerSum_eq_zero_of_pow_eq _ (phasePoint_injective hθ)
        (fun i => phasePoint_pow_eq_of_crystal θ hcr i ⟨0, hP⟩) hk1 hkP, mul_zero]
    have hzero : ∀ m ∈ (Finset.Ioo (-(P : ℤ)) P).erase 0, ‖D m‖ = 0 := by
      intro m hm
      rw [Finset.mem_erase, Finset.mem_Ioo] at hm
      obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
      · rw [hmode k (by omega) (by omega), norm_zero]
      · rw [hDdef, patternSymbol_neg, Complex.norm_conj, ← hDdef, hmode k (by omega) (by omega),
          norm_zero]
    have hG := re_toeplitzForm_ge D c
    rw [Finset.sum_eq_zero hzero, sub_zero, hD0re] at hG
    exact hG

/-- **Variational principle for the Hodge class.** -/
theorem crystal_iff_hodge_floor_diagonal {P : ℕ} (hP : 0 < P) (θ : Fin P → ℝ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hθ : ∀ r r' : Fin P, ∀ j j' : ℤ, θ r + j = θ r' + j' → r = r' ∧ j = j')
    {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℝ} (ha1 : ((P : ℝ) - 1) * ℓ / 2 < a) (ha2 : a ≤ P * ℓ / 2) :
    (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a → paperFT f (I / 2) = 0 →
        paperFT f (-(I / 2)) = 0 → ℓ * (2 * P) * ∫ t, ‖f t‖ ^ 2 ≤
          ((patternConfig hℓ (scaledOffset ℓ θ) (fun _ => δ) (fun _ => hδ0)
            (fun _ => hδ1)).W f f).re) ↔
      ∀ r r', ∃ k : ℤ, P * θ r - P * θ r' = k := by
  have hPr : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have ha0 : 0 < a := lt_of_le_of_lt (by
    have : 0 ≤ ((P : ℝ) - 1) * ℓ := mul_nonneg (by linarith) hℓ.le
    linarith) ha1
  rw [← crystal_iff_weil_floor_diagonal hP θ hδ0 hδ1 hθ hℓ ha1 ha2,
    hodge_floor_iff_toeplitz_floor _ hℓ _ (fun _ hf hfc => W_patternConfig hℓ _ _ _ _
      (scaledOffset_injective hℓ hθ) hf hfc) ha0,
    weil_floor_iff_toeplitz_floor _ hℓ _ (fun _ hf hfc => W_patternConfig hℓ _ _ _ _
      (scaledOffset_injective hℓ hθ) hf hfc) ha0]

end GaloisForLFunctions.SquareRootThreshold
