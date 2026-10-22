import GaloisForLFunctions.RHTower.ExponentialWeilFormDichotomy
import GaloisForLFunctions.RHTower.CCM.CCMRectangularTwoEdge

/-!
# One exponential Weil family decides RH: the Cayley multiplier

Let `c(s) = 1 − 1/s`, the Cayley map sending the critical line onto the unit circle, and

`G(z) = Σ_ρ exp(z c(ρ) + z̄ c(1−ρ))/(ρ(1−ρ))`   (`cayleyWeilForm`).

With `ĝ_z(s) = e^{z c(s)}/s` this is the Weil form `Σ_ρ ĝ_z(ρ) ĝ_z^♯(ρ)`.

**Theorem** (`riemannHypothesis_iff_cayleyWeilForm_nonneg`).  `RH ⟺ ∀ z ∈ ℂ, Re G(z) ≥ 0`.

One two-real-parameter family suffices: no shells, no large parameter, no side condition.

**Proof.**  Write `A = c(ρ)`.  Then `c(1−ρ) = A⁻¹`, so with `r = |A|`
* `A + conj c(1−ρ) = A(1 + r^{−2})` has modulus `r + 1/r ≥ 2`, and
  `A − conj c(1−ρ) = A(1 − r^{−2})` vanishes iff `r = 1`;
* `r² = |ρ−1|²/|ρ|²`, so `r = 1` iff `Re ρ = ½`, and
  `(r − 1/r)² = (1 − 2Re ρ)²/(|ρ|²|ρ−1|²) ≤ (Im ρ)^{−4}`.
Under RH, `c(1−ρ) = conj c(ρ)` and every term is `e^{2Re(z c(ρ))}/|ρ|² ≥ 0`.  Off RH a zero with
`Re ρ ≠ ½` has modulus part `r + 1/r > 2`; for `2 < L < r + 1/r` only finitely many zeros exceed
`L`, all with nonzero phase part, and the threshold negativity lemma
(`exists_re_expWeilForm_neg_of_threshold`) gives `Re G(z) < 0`.

The Taylor data are `Σ_ρ c(ρ)^m/(ρ(1−ρ))`, `m ∈ ℤ`, the second differences of Li's coefficients;
the shell damping `(s+1)^{−2}` of the shell criteria imitates the decay `|c(ρ)| − 1 = O(|ρ|^{−2})`
built into the Cayley map.
-/

open Complex Filter
open scoped ComplexConjugate Topology

namespace RHTower

noncomputable section

/-- The Cayley value `c(s) = 1 − 1/s`. -/
def cayleyValue (s : ℂ) : ℂ := 1 - 1 / s

/-- The Cayley Weil form `G(z) = Σ_ρ exp(z c(ρ) + z̄ c(1−ρ))/(ρ(1−ρ))`. -/
def cayleyWeilForm (z : ℂ) : ℂ :=
  expWeilForm (fun q => cayleyValue (q.1 : ℂ)) (fun q => cayleyValue (1 - (q.1 : ℂ))) z

theorem cayleyValue_eq_div {s : ℂ} (hs : s ≠ 0) : cayleyValue s = (s - 1) / s := by
  rw [cayleyValue]; field_simp

theorem cayleyValue_ne_zero {s : ℂ} (hs : s ≠ 0) (hs1 : 1 - s ≠ 0) : cayleyValue s ≠ 0 := by
  rw [cayleyValue_eq_div hs]
  exact div_ne_zero (fun h => hs1 (by rw [← neg_sub, h, neg_zero])) hs

theorem cayleyValue_one_sub {s : ℂ} (hs : s ≠ 0) (hs1 : 1 - s ≠ 0) :
    cayleyValue (1 - s) = (cayleyValue s)⁻¹ := by
  have hs1' : s - 1 ≠ 0 := fun h => hs1 (by rw [← neg_sub, h, neg_zero])
  rw [cayleyValue, cayleyValue_eq_div hs, inv_div, eq_div_iff hs1']
  field_simp
  ring

/-- `‖c(s)‖² = ‖s − 1‖²/‖s‖²`. -/
theorem norm_cayleyValue {s : ℂ} (hs : s ≠ 0) : ‖cayleyValue s‖ = ‖s - 1‖ / ‖s‖ := by
  rw [cayleyValue_eq_div hs, norm_div]

/-- `A + conj A⁻¹ = A (1 + ‖A‖^{−2})`. -/
theorem add_conj_inv_eq (A : ℂ) :
    A + conj A⁻¹ = A * ((1 + (‖A‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [map_inv₀, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj,
    Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- `A − conj A⁻¹ = A (1 − ‖A‖^{−2})`. -/
theorem sub_conj_inv_eq (A : ℂ) :
    A - conj A⁻¹ = A * ((1 - (‖A‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [map_inv₀, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj,
    Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- The modulus part has norm `r + 1/r`. -/
theorem norm_add_conj_inv {A : ℂ} (hA : A ≠ 0) : ‖A + conj A⁻¹‖ = ‖A‖ + ‖A‖⁻¹ := by
  have hn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  rw [add_conj_inv_eq, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  field_simp

/-- The phase part vanishes only on the unit circle. -/
theorem sub_conj_inv_ne_zero {A : ℂ} (hA : A ≠ 0) (h1 : ‖A‖ ≠ 1) : A - conj A⁻¹ ≠ 0 := by
  have hn : 0 < ‖A‖ := norm_pos_iff.mpr hA
  rw [sub_conj_inv_eq]
  refine mul_ne_zero hA ?_
  rw [Ne, Complex.ofReal_eq_zero, sub_eq_zero]
  intro h
  apply h1
  have h2 : ‖A‖ ^ 2 = 1 := by
    have := congrArg (fun x : ℝ => x⁻¹) h
    simp only [inv_inv, inv_one] at this
    exact this.symm
  nlinarith [sq_nonneg (‖A‖ - 1)]

/-- `r + 1/r > 2` off the unit circle. -/
theorem two_lt_add_inv {r : ℝ} (hr : 0 < r) (h1 : r ≠ 1) : 2 < r + r⁻¹ := by
  have h : 0 < (r - 1) ^ 2 := by
    have : r - 1 ≠ 0 := sub_ne_zero.mpr h1
    positivity
  have e : r + r⁻¹ - 2 = (r - 1) ^ 2 / r := by field_simp; ring
  have : 0 < r + r⁻¹ - 2 := by rw [e]; positivity
  linarith

/-- `‖c(ρ)‖ = 1` exactly on the critical line. -/
theorem norm_cayleyValue_eq_one_iff {s : ℂ} (hs : s ≠ 0) :
    ‖cayleyValue s‖ = 1 ↔ s.re = 1 / 2 := by
  rw [norm_cayleyValue hs, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hs)]
  constructor
  · intro h
    have h2 : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by rw [h]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply] at h2
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h2
    linarith
  · intro h
    have h2 : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
      rw [h]; ring
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `(r − 1/r)² ≤ (Im s)^{−4}` for `r = ‖c(s)‖`, `0 < Re s < 1`. -/
theorem sq_norm_cayleyValue_sub_inv_le {s : ℂ} (hs : s ≠ 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (him : s.im ≠ 0) :
    (‖cayleyValue s‖ - ‖cayleyValue s‖⁻¹) ^ 2 ≤ 1 / (s.im ^ 2) ^ 2 := by
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp at this
    exact him this
  have hX : s.im ^ 2 ≤ ‖s - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith
  have hY : s.im ^ 2 ≤ ‖s‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith
  have hXY : ‖s - 1‖ ^ 2 - ‖s‖ ^ 2 = 1 - 2 * s.re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    ring
  have hpX : 0 < ‖s - 1‖ := norm_pos_iff.mpr hs1
  have hpY : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have him2 : 0 < s.im ^ 2 := by positivity
  rw [norm_cayleyValue hs]
  have e : (‖s - 1‖ / ‖s‖ - (‖s - 1‖ / ‖s‖)⁻¹) ^ 2 =
      (‖s - 1‖ ^ 2 - ‖s‖ ^ 2) ^ 2 / (‖s - 1‖ ^ 2 * ‖s‖ ^ 2) := by
    field_simp
  rw [e, hXY, div_le_div_iff₀ (by positivity) (by positivity)]
  have hre : (1 - 2 * s.re) ^ 2 ≤ 1 := by nlinarith
  have hprod : s.im ^ 2 * s.im ^ 2 ≤ ‖s - 1‖ ^ 2 * ‖s‖ ^ 2 :=
    mul_le_mul hX hY (by positivity) (by positivity)
  nlinarith

/-! ## The criterion -/

/-- **RH ⟺ the Cayley Weil form is nonnegative on all of `ℂ`.** -/
theorem riemannHypothesis_iff_cayleyWeilForm_nonneg :
    RiemannHypothesis ↔ ∀ z : ℂ, 0 ≤ (cayleyWeilForm z).re := by
  obtain ⟨η, hη, hgap⟩ := exists_xiDivisorSupport_abs_im_lower_bound
  have hne : ∀ q : XiZeroCopy, (q.1 : ℂ) ≠ 0 := xiZeroCopy_ne_zero
  have hne1 : ∀ q : XiZeroCopy, 1 - (q.1 : ℂ) ≠ 0 := xiZeroCopy_one_sub_ne_zero
  have hinv : ∀ q : XiZeroCopy,
      cayleyValue (1 - (q.1 : ℂ)) = (cayleyValue (q.1 : ℂ))⁻¹ := fun q =>
    cayleyValue_one_sub (hne q) (hne1 q)
  have hA0 : ∀ q : XiZeroCopy, cayleyValue (q.1 : ℂ) ≠ 0 := fun q =>
    cayleyValue_ne_zero (hne q) (hne1 q)
  have himη : ∀ q : XiZeroCopy, η ≤ |(q.1 : ℂ).im| := fun q => hgap q.1
  -- bounds: `‖ρ‖, ‖ρ − 1‖ ≥ η`
  have hlow : ∀ q : XiZeroCopy, η ≤ ‖(q.1 : ℂ)‖ ∧ η ≤ ‖(q.1 : ℂ) - 1‖ := fun q =>
    ⟨(himη q).trans (Complex.abs_im_le_norm _), (himη q).trans (by
      have := Complex.abs_im_le_norm ((q.1 : ℂ) - 1)
      simpa using this)⟩
  have hbd : ∃ C : ℝ, ∀ q : XiZeroCopy, ‖cayleyValue (q.1 : ℂ)‖ ≤ C ∧
      ‖cayleyValue (1 - (q.1 : ℂ))‖ ≤ C := by
    refine ⟨1 + 1 / η, fun q => ⟨?_, ?_⟩⟩
    · rw [norm_cayleyValue (hne q), div_le_iff₀ ((hη.trans_le (hlow q).1))]
      have h1 := norm_sub_le (q.1 : ℂ) 1
      rw [norm_one] at h1
      have h2 : 1 ≤ (1 / η) * ‖(q.1 : ℂ)‖ := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hη]; linarith [(hlow q).1]
      nlinarith
    · rw [hinv q, norm_inv, norm_cayleyValue (hne q), inv_div,
        div_le_iff₀ (hη.trans_le (hlow q).2)]
      have h1 : ‖(q.1 : ℂ)‖ ≤ ‖(q.1 : ℂ) - 1‖ + 1 := by
        have := norm_sub_le ((q.1 : ℂ) - 1) (-1)
        rw [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at this
        linarith
      have h2 : 1 ≤ (1 / η) * ‖(q.1 : ℂ) - 1‖ := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hη]; linarith [(hlow q).2]
      nlinarith
  obtain ⟨C, hC⟩ := hbd
  constructor
  · intro hRH z
    refine re_expWeilForm_nonneg_of_riemannHypothesis hC hRH (fun q => ?_) z
    have hhalf := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
    have h1 : ‖cayleyValue (q.1 : ℂ)‖ = 1 := (norm_cayleyValue_eq_one_iff (hne q)).mpr hhalf
    rw [hinv q, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
    simp
  · intro hpos
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    have hr₁ : ‖cayleyValue (q₁.1 : ℂ)‖ ≠ 1 := fun h =>
      (ne_of_gt hq₁) ((norm_cayleyValue_eq_one_iff (hne q₁)).mp h)
    have hmod : ∀ q : XiZeroCopy, ‖cayleyValue (q.1 : ℂ) + conj (cayleyValue (1 - (q.1 : ℂ)))‖ =
        ‖cayleyValue (q.1 : ℂ)‖ + ‖cayleyValue (q.1 : ℂ)‖⁻¹ := fun q => by
      rw [hinv q, norm_add_conj_inv (hA0 q)]
    obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, M₁ = ‖cayleyValue (q₁.1 : ℂ)‖ + ‖cayleyValue (q₁.1 : ℂ)‖⁻¹ :=
      ⟨_, rfl⟩
    have hM₁2 : 2 < M₁ := hM₁ ▸ two_lt_add_inv (norm_pos_iff.mpr (hA0 q₁)) hr₁
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (2 + M₁) / 2 := ⟨_, rfl⟩
    have hL2 : 2 < L := by rw [hL]; linarith
    have hLM : L < M₁ := by rw [hL]; linarith
    -- the loud set is finite
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = L ^ 2 - 4 := ⟨_, rfl⟩
    have hκ0 : 0 < κ := by rw [hκ]; nlinarith
    have hfin : {q : XiZeroCopy | L < ‖cayleyValue (q.1 : ℂ) +
        conj (cayleyValue (1 - (q.1 : ℂ)))‖}.Finite := by
      refine (finite_xiZeroCopy_band 0 (r := max 1 (1 / κ)) (by positivity)).subset
        fun q hq => ?_
      simp only [Set.mem_setOf_eq] at hq ⊢
      rw [hmod q] at hq
      rw [sub_zero]
      obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖cayleyValue (q.1 : ℂ)‖ := ⟨_, rfl⟩
      rw [← hr] at hq
      have hr0 : 0 < r := hr ▸ norm_pos_iff.mpr (hA0 q)
      have him0 : (q.1 : ℂ).im ≠ 0 := fun h => by
        have := himη q; rw [h, abs_zero] at this; linarith
      have hsq := sq_norm_cayleyValue_sub_inv_le (hne q) (xiZeroCopy_re_pos q)
        (xiZeroCopy_re_lt_one q) him0
      rw [← hr] at hsq
      have hid : (r + r⁻¹) ^ 2 - 4 = (r - r⁻¹) ^ 2 := by field_simp; ring
      have hL0 : 0 < L := by linarith
      have hk : κ < 1 / ((q.1 : ℂ).im ^ 2) ^ 2 := by
        have h1 : L ^ 2 < (r + r⁻¹) ^ 2 := pow_lt_pow_left₀ hq hL0.le two_ne_zero
        rw [hκ]; linarith
      have hγ2 : 0 < ((q.1 : ℂ).im ^ 2) ^ 2 := by positivity
      rw [lt_div_iff₀ hγ2] at hk
      by_cases h1 : |(q.1 : ℂ).im| ≤ 1
      · exact h1.trans (le_max_left _ _)
      · push Not at h1
        refine le_trans ?_ (le_max_right _ _)
        rw [le_div_iff₀ hκ0]
        have hγ : |(q.1 : ℂ).im| ≤ ((q.1 : ℂ).im ^ 2) ^ 2 := by
          have e : ((q.1 : ℂ).im ^ 2) ^ 2 = |(q.1 : ℂ).im| ^ 4 := by
            rw [← sq_abs ((q.1 : ℂ).im)]; ring
          rw [e]
          calc |(q.1 : ℂ).im| = |(q.1 : ℂ).im| ^ 1 := (pow_one _).symm
            _ ≤ |(q.1 : ℂ).im| ^ 4 := pow_le_pow_right₀ h1.le (by norm_num)
        nlinarith
    -- every loud zero has a nonzero phase part
    have hbne : ∀ q : XiZeroCopy, L < ‖cayleyValue (q.1 : ℂ) +
        conj (cayleyValue (1 - (q.1 : ℂ)))‖ →
        cayleyValue (q.1 : ℂ) - conj (cayleyValue (1 - (q.1 : ℂ))) ≠ 0 := by
      intro q hq
      rw [hinv q]
      refine sub_conj_inv_ne_zero (hA0 q) fun h => ?_
      rw [hmod q, h, inv_one] at hq
      linarith
    obtain ⟨z, hz⟩ := exists_re_expWeilForm_neg_of_threshold (by linarith) hfin hbne
      (q₁ := q₁) (by rw [hmod q₁, ← hM₁]; exact hLM)
    exact (not_le.mpr hz) (hpos z)

end

end RHTower
