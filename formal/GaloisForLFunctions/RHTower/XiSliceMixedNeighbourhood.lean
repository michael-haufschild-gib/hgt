import GaloisForLFunctions.RHTower.XiSliceHeatPerPairPositivity

/-!
# The mixed class breaks the order-two slice sign on a punctured neighbourhood of its ordinate

Let a critical zero sit at the ordinate of an off-line pair: zero copies at the spectral points
`γ` and `γ ± δ i` (`δ > 0`).  At a height `t = γ + u`, `0 < |u| ≤ δ/2`, with `ΞC(t) ≠ 0`, the
critical atom is `A = 1/u²`, and the pair contributes the factor `1 + p₁ y + p₂ y²` with

  `p₁ = 2(u² − δ²)/(u² + δ²)²`,   `p₂ = 1/(u² + δ²)²`

to the normalised slice `Σ_j c_{2j}(t) y^j / ΞC(t)²` (`sliceTruncPoly`).  The order-one sign is
dominated by `A > 0`, so the first Laguerre inequality holds near the ordinate.  At order two the
product `(1 + A y)(1 + p₁ y + p₂ y²)` has coefficient

  `A p₁ + p₂ = (3u² − 2δ²) / (u² (u² + δ²)²) ≤ −(4/5) / (δ² u²)`.

The remaining zero copies enter through the coefficients of a product of factors
`1 + b y + c y²` (`abs_coeff_one_prod_quadFactor_le`, `abs_coeff_two_prod_quadFactor_le`).  With
atom mass `M`, this gives `|r₁| ≤ 6M` and `|r₂| ≤ 19M²`.

**Theorem** (`xiSliceCoeff_four_re_neg_near_mixed`).  If the copies other than these carry atom mass
`Σ 1/|z − t|² ≤ M` at `t` with `δ² M ≤ 1/13`, then `Re c₄(t) < 0`.

Together with `xiSliceCoeff_two_re_neg_near_offLine_pair` (order one, isolated pair, full
neighbourhood `|t − γ| ≤ δ/2`), both near-line classes behind the CANNOT-471 core force the slice
criterion to fail on a height interval of length comparable to the displacement `δ`: the isolated
class at order one, the mixed class at order two (at the ordinate itself the mixed class is
detected by `exists_re_xiSliceCoeff_neg_of_offLine_mass_of_order`).
-/

open Complex Filter Topology Polynomial

namespace RHTower.DeBruijn

noncomputable section

/-! ## Coefficients of products of quadratic factors -/

/-- The factor `1 + b y + c y²`. -/
def quadFactor (b c : ℝ) : ℝ[X] := 1 + C b * X + C c * X ^ 2

theorem coeff_quadFactor_mul (b c : ℝ) (Q : ℝ[X]) :
    (quadFactor b c * Q).coeff 0 = Q.coeff 0 ∧
      (quadFactor b c * Q).coeff 1 = Q.coeff 1 + b * Q.coeff 0 ∧
      (quadFactor b c * Q).coeff 2 = Q.coeff 2 + b * Q.coeff 1 + c * Q.coeff 0 := by
  have e : quadFactor b c * Q = Q + C b * (X * Q) + C c * (X ^ 2 * Q) := by
    unfold quadFactor; ring
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul']
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul]
    norm_num
  · simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul']
    rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_X_mul]
    norm_num

theorem coeff_zero_prod_quadFactor {ι : Type*} (s : Finset ι) (b c : ι → ℝ) :
    (∏ i ∈ s, quadFactor (b i) (c i)).coeff 0 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, (coeff_quadFactor_mul _ _ _).1, ih]

theorem abs_coeff_one_prod_quadFactor_le {ι : Type*} (s : Finset ι) (b c : ι → ℝ) :
    |(∏ i ∈ s, quadFactor (b i) (c i)).coeff 1| ≤ ∑ i ∈ s, |b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, (coeff_quadFactor_mul _ _ _).2.1, coeff_zero_prod_quadFactor,
      Finset.sum_insert ha, mul_one]
    calc _ ≤ |(∏ i ∈ s, quadFactor (b i) (c i)).coeff 1| + |b a| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem abs_coeff_two_prod_quadFactor_le {ι : Type*} (s : Finset ι) (b c : ι → ℝ) :
    |(∏ i ∈ s, quadFactor (b i) (c i)).coeff 2| ≤
      (∑ i ∈ s, |b i|) ^ 2 / 2 + ∑ i ∈ s, |c i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert a s ha ih =>
    have h1 := abs_coeff_one_prod_quadFactor_le s b c
    rw [Finset.prod_insert ha, (coeff_quadFactor_mul _ _ _).2.2, coeff_zero_prod_quadFactor,
      Finset.sum_insert ha, Finset.sum_insert ha, mul_one]
    set B := ∑ i ∈ s, |b i|
    have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hprod : |b a * (∏ i ∈ s, quadFactor (b i) (c i)).coeff 1| ≤ |b a| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    calc _ ≤ |(∏ i ∈ s, quadFactor (b i) (c i)).coeff 2| +
          |b a * (∏ i ∈ s, quadFactor (b i) (c i)).coeff 1| + |c a| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ (B ^ 2 / 2 + ∑ i ∈ s, |c i|) + |b a| * B + |c a| := by gcongr
      _ ≤ _ := by nlinarith [abs_nonneg (b a), sq_nonneg (b a)]

/-! ## The slice factors as quadratic factors -/

theorem sliceAtom_nonneg (t : ℝ) (q : XiZeroCopy) : 0 ≤ sliceAtom t q := by
  unfold sliceAtom; positivity

open scoped Classical in
/-- The coefficients of the normalised slice factor of a copy. -/
def sliceQuadB (t : ℝ) (q : XiZeroCopy) : ℝ :=
  if XiCopyCritical q then sliceAtom t q else 2 * sliceAtom t q - 4 * sliceDefect t q

open scoped Classical in
/-- The quadratic coefficient of the normalised slice factor of a copy. -/
def sliceQuadC (t : ℝ) (q : XiZeroCopy) : ℝ :=
  if XiCopyCritical q then 0 else sliceAtom t q ^ 2

theorem abs_sliceQuadB_le {t : ℝ} (ht : XiC t ≠ 0) (q : XiZeroCopy) :
    |sliceQuadB t q| ≤ 6 * sliceAtom t q := by
  classical
  have ha := sliceAtom_nonneg t q
  have hd := sliceDefect_le_sliceAtom ht q
  have hd0 : 0 ≤ sliceDefect t q := by unfold sliceDefect; positivity
  unfold sliceQuadB
  split_ifs
  · rw [abs_of_nonneg ha]; linarith
  · rw [abs_le]; constructor <;> linarith

theorem abs_sliceQuadC_le (t : ℝ) (q : XiZeroCopy) : |sliceQuadC t q| ≤ sliceAtom t q ^ 2 := by
  classical
  unfold sliceQuadC
  split_ifs
  · simp; positivity
  · rw [abs_of_nonneg (sq_nonneg _)]

theorem sliceCritFactor_eq_quadFactor (t : ℝ) {q : XiZeroCopy} (hq : XiCopyCritical q) :
    (1 + C (sliceAtom t q) * X : ℝ[X]) = quadFactor (sliceQuadB t q) (sliceQuadC t q) := by
  classical
  simp [quadFactor, sliceQuadB, sliceQuadC, hq]

theorem sliceUpFactor_eq_quadFactor (t : ℝ) {q : XiZeroCopy} (hq : ¬ XiCopyCritical q) :
    ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X : ℝ[X]) =
      quadFactor (sliceQuadB t q) (sliceQuadC t q) := by
  classical
  simp only [quadFactor, sliceQuadB, sliceQuadC, if_neg hq, C_sub, C_mul, C_pow, C_ofNat]
  ring


/-! ## The mixed configuration -/

/-- **Decomposition of the truncated slice polynomial.**  If `S` contains a critical copy `q₀` and an
upper copy `q₁`, its normalised slice polynomial is `(1 + A y)(1 + p₁ y + p₂ y²)` times a product
of quadratic factors over the remaining critical and upper copies. -/
theorem sliceTruncPoly_eq_mixed (t : ℝ) {S : Finset XiZeroCopy} {q₀ q₁ : XiZeroCopy}
    (h0S : q₀ ∈ S) (h1S : q₁ ∈ S) (h0 : XiCopyCritical q₀) (h1 : XiCopyUpper q₁) :
    sliceTruncPoly t S = quadFactor (sliceAtom t q₀) 0 *
      (quadFactor (sliceQuadB t q₁) (sliceQuadC t q₁) *
        ∏ q ∈ (sliceTruncCrit S).erase q₀ ∪ (sliceTruncUp S).erase q₁,
          quadFactor (sliceQuadB t q) (sliceQuadC t q)) := by
  classical
  have h1c : ¬ XiCopyCritical q₁ := by
    unfold XiCopyCritical; unfold XiCopyUpper at h1; exact h1.ne'
  have hdisj : Disjoint ((sliceTruncCrit S).erase q₀) ((sliceTruncUp S).erase q₁) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    have hc := (mem_sliceTruncCrit.mp (Finset.mem_of_mem_erase hq)).2
    have hu := (mem_sliceTruncUp.mp (Finset.mem_of_mem_erase hq')).2
    unfold XiCopyCritical at hc; unfold XiCopyUpper at hu; linarith
  rw [Finset.prod_union hdisj, sliceTruncPoly,
    ← Finset.mul_prod_erase (sliceTruncCrit S) _ (mem_sliceTruncCrit.mpr ⟨h0S, h0⟩),
    ← Finset.mul_prod_erase (sliceTruncUp S) _ (mem_sliceTruncUp.mpr ⟨h1S, h1⟩)]
  have hA : (1 + C (sliceAtom t q₀) * X : ℝ[X]) = quadFactor (sliceAtom t q₀) 0 := by
    simp [quadFactor]
  have hcrit : ∏ q ∈ (sliceTruncCrit S).erase q₀, (1 + C (sliceAtom t q) * X : ℝ[X]) =
      ∏ q ∈ (sliceTruncCrit S).erase q₀, quadFactor (sliceQuadB t q) (sliceQuadC t q) :=
    Finset.prod_congr rfl fun q hq =>
      sliceCritFactor_eq_quadFactor t (mem_sliceTruncCrit.mp (Finset.mem_of_mem_erase hq)).2
  have hup : ∏ q ∈ (sliceTruncUp S).erase q₁,
      ((1 + C (sliceAtom t q) * X) ^ 2 - C (4 * sliceDefect t q) * X : ℝ[X]) =
      ∏ q ∈ (sliceTruncUp S).erase q₁, quadFactor (sliceQuadB t q) (sliceQuadC t q) := by
    refine Finset.prod_congr rfl fun q hq => sliceUpFactor_eq_quadFactor t ?_
    have hu := (mem_sliceTruncUp.mp (Finset.mem_of_mem_erase hq)).2
    unfold XiCopyCritical; unfold XiCopyUpper at hu; exact hu.ne'
  rw [hA, hcrit, hup, sliceUpFactor_eq_quadFactor t h1c]
  ring

/-- The order-two coefficient of the mixed decomposition. -/
theorem coeff_two_mixed (A p₁ p₂ : ℝ) (R : ℝ[X]) (hR : R.coeff 0 = 1) :
    (quadFactor A 0 * (quadFactor p₁ p₂ * R)).coeff 2 =
      R.coeff 2 + (A + p₁) * R.coeff 1 + (A * p₁ + p₂) := by
  obtain ⟨g0, g1, g2⟩ := coeff_quadFactor_mul p₁ p₂ R
  obtain ⟨-, -, f2⟩ := coeff_quadFactor_mul A 0 (quadFactor p₁ p₂ * R)
  rw [f2, g2, g1, g0, hR]
  ring

/-- **The scalar inequality.**  For `0 < w ≤ δ²/4`, `|r₁| ≤ 6M`, `|r₂| ≤ 19M²`, `δ²M ≤ 1/13`, the
order-two coefficient `r₂ + (1/w + p₁) r₁ + (p₁/w + p₂)` with `p₁ = 2(w − δ²)/(w + δ²)²`,
`p₂ = 1/(w + δ²)²` is at most `−1/(15 δ² w)`. -/
theorem mixedSliceCoeffTwo_le {w δ M r₁ r₂ : ℝ} (hw : 0 < w) (hwδ : w ≤ δ ^ 2 / 4) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hsmall : δ ^ 2 * M ≤ 1 / 13) (hr₁ : |r₁| ≤ 6 * M) (hr₂ : |r₂| ≤ 19 * M ^ 2) :
    r₂ + (1 / w + 2 * (w - δ ^ 2) / (w + δ ^ 2) ^ 2) * r₁ +
        (1 / w * (2 * (w - δ ^ 2) / (w + δ ^ 2) ^ 2) + 1 / (w + δ ^ 2) ^ 2)
      ≤ -(1 / (15 * δ ^ 2 * w)) := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  set D := w + δ ^ 2 with hD
  have hD0 : 0 < D := by positivity
  have hDδ : δ ^ 2 ≤ D := by rw [hD]; linarith
  -- the three terms, multiplied by `w`
  have t1 : w * (1 / w * (2 * (w - δ ^ 2) / D ^ 2) + 1 / D ^ 2) ≤ -(4 / 5) / δ ^ 2 := by
    have e : w * (1 / w * (2 * (w - δ ^ 2) / D ^ 2) + 1 / D ^ 2) = (3 * w - 2 * δ ^ 2) / D ^ 2 := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) hδ2]
    nlinarith [mul_nonneg hw.le (by linarith : (0 : ℝ) ≤ δ ^ 2 / 4 - w)]
  have hp₁ : |2 * (w - δ ^ 2) / D ^ 2| ≤ 2 / D := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < D ^ 2), div_le_div_iff₀ (by positivity) hD0]
    have : |2 * (w - δ ^ 2)| ≤ 2 * D := by
      rw [abs_le]; constructor <;> nlinarith
    nlinarith
  have t2 : w * ((1 / w + 2 * (w - δ ^ 2) / D ^ 2) * r₁) ≤ 9 * M := by
    have e : w * ((1 / w + 2 * (w - δ ^ 2) / D ^ 2) * r₁) =
        (1 + w * (2 * (w - δ ^ 2) / D ^ 2)) * r₁ := by field_simp
    rw [e]
    have hfac : |1 + w * (2 * (w - δ ^ 2) / D ^ 2)| ≤ 3 / 2 := by
      have h1 : |w * (2 * (w - δ ^ 2) / D ^ 2)| ≤ w * (2 / D) := by
        rw [abs_mul, abs_of_pos hw]; exact mul_le_mul_of_nonneg_left hp₁ hw.le
      have h2 : w * (2 / D) ≤ 1 / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hD0]; nlinarith
      calc _ ≤ |(1 : ℝ)| + |w * (2 * (w - δ ^ 2) / D ^ 2)| := abs_add_le _ _
        _ ≤ 3 / 2 := by rw [abs_one]; linarith
    calc (1 + w * (2 * (w - δ ^ 2) / D ^ 2)) * r₁ ≤ |(1 + w * (2 * (w - δ ^ 2) / D ^ 2)) * r₁| :=
          le_abs_self _
      _ = |1 + w * (2 * (w - δ ^ 2) / D ^ 2)| * |r₁| := abs_mul _ _
      _ ≤ 3 / 2 * (6 * M) := mul_le_mul hfac hr₁ (abs_nonneg _) (by norm_num)
      _ = 9 * M := by ring
  have t3 : w * r₂ ≤ δ ^ 2 / 4 * (19 * M ^ 2) := by
    calc w * r₂ ≤ w * |r₂| := mul_le_mul_of_nonneg_left (le_abs_self _) hw.le
      _ ≤ δ ^ 2 / 4 * (19 * M ^ 2) := mul_le_mul hwδ hr₂ (abs_nonneg _) (by positivity)
  have hsum : w * (r₂ + (1 / w + 2 * (w - δ ^ 2) / D ^ 2) * r₁ +
      (1 / w * (2 * (w - δ ^ 2) / D ^ 2) + 1 / D ^ 2)) ≤ -(1 / (15 * δ ^ 2)) := by
    have e : w * (r₂ + (1 / w + 2 * (w - δ ^ 2) / D ^ 2) * r₁ +
        (1 / w * (2 * (w - δ ^ 2) / D ^ 2) + 1 / D ^ 2)) =
        w * r₂ + w * ((1 / w + 2 * (w - δ ^ 2) / D ^ 2) * r₁) +
          w * (1 / w * (2 * (w - δ ^ 2) / D ^ 2) + 1 / D ^ 2) := by ring
    rw [e]
    have key : δ ^ 2 * (δ ^ 2 / 4 * (19 * M ^ 2) + 9 * M) ≤ 4 / 5 - 1 / 15 := by
      nlinarith [mul_nonneg hδ2.le hM]
    have h45 : -(4 / 5) / δ ^ 2 + (δ ^ 2 / 4 * (19 * M ^ 2) + 9 * M) ≤ -(1 / (15 * δ ^ 2)) := by
      rw [show -(1 / (15 * δ ^ 2)) = -(1 / 15) / δ ^ 2 by field_simp]
      rw [← sub_nonneg]
      have : -(1 / 15) / δ ^ 2 - (-(4 / 5) / δ ^ 2 + (δ ^ 2 / 4 * (19 * M ^ 2) + 9 * M)) =
          ((4 / 5 - 1 / 15) - δ ^ 2 * (δ ^ 2 / 4 * (19 * M ^ 2) + 9 * M)) / δ ^ 2 := by
        field_simp; ring
      rw [this]
      exact div_nonneg (by linarith) hδ2.le
    linarith
  have hfinal : r₂ + (1 / w + 2 * (w - δ ^ 2) / D ^ 2) * r₁ +
      (1 / w * (2 * (w - δ ^ 2) / D ^ 2) + 1 / D ^ 2) ≤ -(1 / (15 * δ ^ 2)) / w := by
    rw [le_div_iff₀ hw]; linarith
  calc _ ≤ -(1 / (15 * δ ^ 2)) / w := hfinal
    _ = -(1 / (15 * δ ^ 2 * w)) := by field_simp

/-- **The mixed class breaks the order-two slice sign near its ordinate.**  Let `q₀` be a zero copy at
the real spectral point `γ` and `q₁` one at `γ + δ i`, `δ > 0`.  Let `0 < |t − γ|`,
`|t − γ| ≤ δ/2`, `ΞC(t) ≠ 0`, and let the copies other than `q₀, q₁` carry atom mass at most `M` at
`t`, with `δ² M ≤ 1/13`.  Then `Re c₄(t) < 0`. -/
theorem xiSliceCoeff_four_re_neg_near_mixed {γ δ t : ℝ} (hδ : 0 < δ)
    {q₀ q₁ : XiZeroCopy} (h0 : xiSpectralPoint q₀ = (γ : ℂ))
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) + (δ : ℂ) * I)
    (ht0 : t ≠ γ) (ht : |t - γ| ≤ δ / 2) (hXi : XiC (t : ℂ) ≠ 0) {M : ℝ}
    (hM : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, q ≠ q₀ ∧ q ≠ q₁) → ∑ q ∈ F, sliceAtom t q ≤ M)
    (hsmall : δ ^ 2 * M ≤ 1 / 13) :
    (xiSliceCoeff t 4).re < 0 := by
  classical
  have hcrit : XiCopyCritical q₀ := by unfold XiCopyCritical; rw [h0]; simp
  have hup : XiCopyUpper q₁ := by unfold XiCopyUpper; rw [h1]; simpa using hδ
  have hupc : ¬ XiCopyCritical q₁ := by
    unfold XiCopyCritical; unfold XiCopyUpper at hup; exact hup.ne'
  have hM0 : 0 ≤ M := by simpa using hM ∅ (by simp)
  set w := (γ - t) ^ 2 with hw
  have hw0 : 0 < w := by
    have : γ - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht0)
    rw [hw]; positivity
  have hwδ : w ≤ δ ^ 2 / 4 := by
    have h := mul_self_le_mul_self (abs_nonneg _) ht
    have e : |t - γ| * |t - γ| = w := by rw [hw, ← sq, sq_abs]; ring
    nlinarith
  -- the atom values
  have hA : sliceAtom t q₀ = 1 / w := by
    unfold sliceAtom
    rw [h0, show ((γ : ℂ) - (t : ℂ)) = ((γ - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hn1 : ‖xiSpectralPoint q₁ - (t : ℂ)‖ ^ 2 = w + δ ^ 2 := by
    rw [h1, show (γ : ℂ) + (δ : ℂ) * I - (t : ℂ) = ((γ - t : ℝ) : ℂ) + (δ : ℂ) * I by push_cast; ring,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I, hw]
  have ha1 : sliceAtom t q₁ = 1 / (w + δ ^ 2) := by unfold sliceAtom; rw [hn1]
  have hd1 : sliceDefect t q₁ = δ ^ 2 / (w + δ ^ 2) ^ 2 := by
    unfold sliceDefect
    rw [h1, show ‖(γ : ℂ) + (δ : ℂ) * I - (t : ℂ)‖ ^ 4 =
      (‖(γ : ℂ) + (δ : ℂ) * I - (t : ℂ)‖ ^ 2) ^ 2 by ring, ← h1, hn1, h1]
    simp
  have hp₁ : sliceQuadB t q₁ = 2 * (w - δ ^ 2) / (w + δ ^ 2) ^ 2 := by
    unfold sliceQuadB; rw [if_neg hupc, ha1, hd1]; field_simp; ring
  have hp₂ : sliceQuadC t q₁ = 1 / (w + δ ^ 2) ^ 2 := by
    unfold sliceQuadC; rw [if_neg hupc, ha1]; field_simp
  -- uniform bound along the truncations containing `q₀, q₁`
  have hbound : ∀ᶠ S in (atTop : Filter (Finset XiZeroCopy)),
      (sliceTruncPoly t S).coeff 2 ≤ -(1 / (15 * δ ^ 2 * w)) := by
    filter_upwards [eventually_ge_atTop ({q₀, q₁} : Finset XiZeroCopy)] with S hS
    have h0S : q₀ ∈ S := hS (by simp)
    have h1S : q₁ ∈ S := hS (by simp)
    set R := (sliceTruncCrit S).erase q₀ ∪ (sliceTruncUp S).erase q₁ with hR
    have hRavoid : ∀ q ∈ R, q ≠ q₀ ∧ q ≠ q₁ := by
      intro q hq
      rcases Finset.mem_union.mp hq with hc | hu
      · have hcq := (mem_sliceTruncCrit.mp (Finset.mem_of_mem_erase hc)).2
        exact ⟨Finset.ne_of_mem_erase hc, fun h => hupc (h ▸ hcq)⟩
      · have huq := (mem_sliceTruncUp.mp (Finset.mem_of_mem_erase hu)).2
        refine ⟨fun h => ?_, Finset.ne_of_mem_erase hu⟩
        rw [h] at huq
        unfold XiCopyUpper at huq; unfold XiCopyCritical at hcrit
        linarith
    have hmass : ∑ q ∈ R, sliceAtom t q ≤ M := hM R hRavoid
    have hr₁ : |(∏ q ∈ R, quadFactor (sliceQuadB t q) (sliceQuadC t q)).coeff 1| ≤ 6 * M := by
      refine (abs_coeff_one_prod_quadFactor_le R _ _).trans ?_
      calc ∑ q ∈ R, |sliceQuadB t q| ≤ ∑ q ∈ R, 6 * sliceAtom t q :=
            Finset.sum_le_sum fun q _ => abs_sliceQuadB_le hXi q
        _ = 6 * ∑ q ∈ R, sliceAtom t q := by rw [Finset.mul_sum]
        _ ≤ 6 * M := by linarith
    have hr₂ : |(∏ q ∈ R, quadFactor (sliceQuadB t q) (sliceQuadC t q)).coeff 2| ≤ 19 * M ^ 2 := by
      refine (abs_coeff_two_prod_quadFactor_le R _ _).trans ?_
      have hB : ∑ q ∈ R, |sliceQuadB t q| ≤ 6 * M := by
        calc ∑ q ∈ R, |sliceQuadB t q| ≤ ∑ q ∈ R, 6 * sliceAtom t q :=
              Finset.sum_le_sum fun q _ => abs_sliceQuadB_le hXi q
          _ = 6 * ∑ q ∈ R, sliceAtom t q := by rw [Finset.mul_sum]
          _ ≤ 6 * M := by linarith
      have hB0 : 0 ≤ ∑ q ∈ R, |sliceQuadB t q| := Finset.sum_nonneg fun q _ => abs_nonneg _
      have hC : ∑ q ∈ R, |sliceQuadC t q| ≤ M ^ 2 := by
        calc ∑ q ∈ R, |sliceQuadC t q| ≤ ∑ q ∈ R, sliceAtom t q ^ 2 :=
              Finset.sum_le_sum fun q _ => abs_sliceQuadC_le t q
          _ ≤ (∑ q ∈ R, sliceAtom t q) ^ 2 :=
              Finset.sum_sq_le_sq_sum_of_nonneg fun q _ => sliceAtom_nonneg t q
          _ ≤ M ^ 2 := by
              have h0 : 0 ≤ ∑ q ∈ R, sliceAtom t q := Finset.sum_nonneg fun q _ => sliceAtom_nonneg t q
              nlinarith
      nlinarith
    rw [sliceTruncPoly_eq_mixed t h0S h1S hcrit hup,
      coeff_two_mixed _ _ _ _ (coeff_zero_prod_quadFactor R _ _), hA, hp₁, hp₂]
    exact mixedSliceCoeffTwo_le hw0 hwδ hδ hM0 hsmall hr₁ hr₂
  -- pass to the limit
  have hlim := tendsto_sliceTruncPoly_coeff hXi 2
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  have hle := le_of_tendsto hre hbound
  have hH : xiHorizontalPair t 0 = ((Xi t ^ 2 : ℝ) : ℂ) := by
    unfold xiHorizontalPair; rw [add_zero, sub_zero, XiC_ofReal]; push_cast; ring
  have hXi' : Xi t ≠ 0 := by
    intro h; apply hXi; rw [XiC_ofReal, h]; simp
  have hpos : 0 < Xi t ^ 2 := by positivity
  rw [hH, show (2 * 2 : ℕ) = 4 from rfl, Complex.div_ofReal_re] at hle
  have hK : 0 < 1 / (15 * δ ^ 2 * w) := by positivity
  have := (div_le_iff₀ hpos).mp hle
  nlinarith

end

end RHTower.DeBruijn
