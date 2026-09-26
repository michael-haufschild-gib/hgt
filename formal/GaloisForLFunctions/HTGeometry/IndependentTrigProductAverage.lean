import GaloisForLFunctions.HTGeometry.WeylEquidistribution

/-!
# Time averages of products of trigonometric polynomials in independent frequencies

Let `ω : ι → ℝ` be `ℚ`-linearly independent (no nontrivial integer relation) and, for each coordinate
`i`, let `g_i(x) = Σ_{s ∈ S_i} c_i(s) e^{i k_i(s) x}` be a trigonometric polynomial.  Then

  `(1/T) ∫₀ᵀ ∏_i g_i(ω_i t) dt → ∏_i ĝ_i(0)`,   `ĝ_i(0) = Σ_{k_i(s) = 0} c_i(s)`.

Expanding the product gives frequencies `Σ_i k_i(s_i) ω_i`, which vanish only when every `k_i(s_i) = 0`.
-/

open MeasureTheory intervalIntegral Filter Topology Complex

namespace RHTower.Weyl

noncomputable section

/-- The one-coordinate trigonometric polynomial with terms indexed by `S`. -/
def trigPoly (S : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (k : ℕ × ℕ → ℤ) (x : ℝ) : ℂ :=
  ∑ s ∈ S, c s * Complex.exp ((k s : ℝ) * x * I)

/-- Its constant term. -/
def trigConst (S : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (k : ℕ × ℕ → ℤ) : ℂ :=
  ∑ s ∈ S.filter (fun s => k s = 0), c s

/-- **Product average in independent frequencies.** -/
theorem prod_trig_time_average {ι : Type*} [Fintype ι] [DecidableEq ι] (ω : ι → ℝ)
    (hω : ∀ m : ι → ℤ, ∑ i, (m i : ℝ) * ω i = 0 → m = 0)
    (S : ι → Finset (ℕ × ℕ)) (c : ι → ℕ × ℕ → ℂ) (k : ι → ℕ × ℕ → ℤ) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ * ∫ t in (0 : ℝ)..T, ∏ i, trigPoly (S i) (c i) (k i) (ω i * t))
      atTop (𝓝 (∏ i, trigConst (S i) (c i) (k i))) := by
  classical
  have hexp : ∀ t : ℝ, ∏ i, trigPoly (S i) (c i) (k i) (ω i * t) =
      ∑ p ∈ Fintype.piFinset S, (∏ i, c i (p i)) *
        Complex.exp (((∑ i, (k i (p i) : ℝ) * ω i : ℝ) : ℂ) * I * t) := by
    intro t
    unfold trigPoly
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
    congr 2
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hexp]
  have h := trig_time_average (Fintype.piFinset S) (fun p => ∑ i, (k i (p i) : ℝ) * ω i)
    (fun p => ∏ i, c i (p i))
  have hfilt : (Fintype.piFinset S).filter (fun p => ∑ i, (k i (p i) : ℝ) * ω i = 0) =
      Fintype.piFinset (fun i => (S i).filter (fun s => k i s = 0)) := by
    ext p
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hp, h0⟩
      have hz := hω (fun i => k i (p i)) h0
      exact fun i => ⟨hp i, congr_fun hz i⟩
    · intro hp
      refine ⟨fun i => (hp i).1, ?_⟩
      have : ∀ i, (k i (p i) : ℝ) = 0 := fun i => by rw [(hp i).2]; simp
      simp [this]
  rw [hfilt] at h
  unfold trigConst
  rw [Finset.prod_univ_sum]
  exact h

/-! ### The Fejér family -/

/-- Index set of the Fejér kernel: pairs `(j₁, j₂)` with `j₁, j₂ < L`. -/
def fejerSet (L : ℕ) : Finset (ℕ × ℕ) := Finset.range L ×ˢ Finset.range L

/-- Coefficients of `F_L(x - θ) = (1/L) Σ e^{i(j₁-j₂)(x-θ)}`. -/
def fejerCoeff (L : ℕ) (θ : ℝ) (s : ℕ × ℕ) : ℂ :=
  (1 / (L : ℂ)) * Complex.exp (-(((s.1 : ℤ) - s.2 : ℤ) : ℝ) * θ * I)

/-- Frequencies of `F_L(x - θ) e^{idx}`. -/
def fejerFreq (d : ℤ) (s : ℕ × ℕ) : ℤ := (s.1 : ℤ) - s.2 + d

/-- `F_L(x-θ) = (1/L) |Σ_{j<L} e^{ij(x-θ)}|²`. -/
theorem trigPoly_fejer_zero (L : ℕ) (θ x : ℝ) :
    trigPoly (fejerSet L) (fejerCoeff L θ) (fejerFreq 0) x =
      (((1 / (L : ℝ)) * ‖∑ j ∈ Finset.range L, Complex.exp ((j : ℝ) * (x - θ) * I)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum,
    ← Finset.sum_product']
  unfold trigPoly fejerSet
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold fejerCoeff fejerFreq
  rw [← Complex.exp_conj, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_sub]
  push_cast; ring

theorem trigPoly_fejer_shift (L : ℕ) (θ : ℝ) (d : ℤ) (x : ℝ) :
    trigPoly (fejerSet L) (fejerCoeff L θ) (fejerFreq d) x =
      trigPoly (fejerSet L) (fejerCoeff L θ) (fejerFreq 0) x * Complex.exp ((d : ℝ) * x * I) := by
  unfold trigPoly
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold fejerFreq
  rw [mul_assoc (fejerCoeff L θ s), ← Complex.exp_add]
  congr 2; push_cast; ring

/-- The Fejér weight is real, nonnegative and at most `L`. -/
theorem fejer_zero_re_bounds (L : ℕ) (hL : 0 < L) (θ x : ℝ) :
    (trigPoly (fejerSet L) (fejerCoeff L θ) (fejerFreq 0) x).im = 0 ∧
      0 ≤ (trigPoly (fejerSet L) (fejerCoeff L θ) (fejerFreq 0) x).re ∧
      (trigPoly (fejerSet L) (fejerCoeff L θ) (fejerFreq 0) x).re ≤ L := by
  rw [trigPoly_fejer_zero]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  refine ⟨by positivity, ?_⟩
  have hn : ‖∑ j ∈ Finset.range L, Complex.exp ((j : ℝ) * (x - θ) * I)‖ ≤ L := by
    refine (norm_sum_le _ _).trans ?_
    simp [Complex.norm_exp]
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  calc 1 / (L : ℝ) * ‖∑ j ∈ Finset.range L, Complex.exp ((j : ℝ) * (x - θ) * I)‖ ^ 2
      ≤ 1 / (L : ℝ) * (L : ℝ) ^ 2 := by gcongr
    _ = (L : ℝ) := by field_simp

theorem card_fejer_diag (L : ℕ) :
    ((fejerSet L).filter (fun s => fejerFreq 0 s = 0)).card = L := by
  have : (fejerSet L).filter (fun s => fejerFreq 0 s = 0) = (Finset.range L).image (fun j => (j, j)) := by
    ext ⟨j₁, j₂⟩
    simp only [fejerSet, fejerFreq, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_image, Prod.mk.injEq, add_zero]
    constructor
    · rintro ⟨⟨h1, _⟩, h⟩; exact ⟨j₁, h1, rfl, by omega⟩
    · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨⟨hj, hj⟩, by simp⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]

theorem card_fejer_off_pos (L : ℕ) :
    ((fejerSet L).filter (fun s => fejerFreq 1 s = 0)).card = L - 1 := by
  have : (fejerSet L).filter (fun s => fejerFreq 1 s = 0) =
      (Finset.range (L - 1)).image (fun j => (j, j + 1)) := by
    ext ⟨j₁, j₂⟩
    simp only [fejerSet, fejerFreq, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h⟩; exact ⟨j₁, by omega, rfl, by omega⟩
    · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨⟨by omega, by omega⟩, by push_cast; ring⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]

theorem card_fejer_off_neg (L : ℕ) :
    ((fejerSet L).filter (fun s => fejerFreq (-1) s = 0)).card = L - 1 := by
  have : (fejerSet L).filter (fun s => fejerFreq (-1) s = 0) =
      (Finset.range (L - 1)).image (fun j => (j + 1, j)) := by
    ext ⟨j₁, j₂⟩
    simp only [fejerSet, fejerFreq, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h⟩; exact ⟨j₂, by omega, by omega, rfl⟩
    · rintro ⟨j, hj, rfl, rfl⟩; exact ⟨⟨by omega, by omega⟩, by push_cast; ring⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]

/-- Constant terms of the Fejér family for `d ∈ {0, 1, -1}`. -/
theorem trigConst_fejer (L : ℕ) (hL : 0 < L) (θ : ℝ) (d : ℤ) (hd : d = 0 ∨ d = 1 ∨ d = -1) :
    trigConst (fejerSet L) (fejerCoeff L θ) (fejerFreq d) =
      Complex.exp ((d : ℝ) * θ * I) * (((L : ℝ) - |(d : ℝ)|) / L : ℝ) := by
  unfold trigConst
  have hcoef : ∀ s ∈ (fejerSet L).filter (fun s => fejerFreq d s = 0),
      fejerCoeff L θ s = (1 / (L : ℂ)) * Complex.exp ((d : ℝ) * θ * I) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    unfold fejerCoeff
    have h1 : ((s.1 : ℤ) - s.2 : ℤ) = -d := by have := hs.2; unfold fejerFreq at this; omega
    rw [h1]; push_cast; ring_nf
  rw [Finset.sum_congr rfl hcoef, Finset.sum_const, nsmul_eq_mul]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rcases hd with rfl | rfl | rfl
  · rw [card_fejer_diag]; push_cast; field_simp; norm_num
  · rw [card_fejer_off_pos, Nat.cast_sub (by omega)]; push_cast; field_simp; norm_num
  · rw [card_fejer_off_neg, Nat.cast_sub (by omega)]; push_cast; field_simp; norm_num

/-- Constant term of a single monomial `e^{idx}`. -/
theorem trigConst_mono (d : ℤ) :
    trigConst {(0, 0)} (fun _ => 1) (fun _ => d) = if d = 0 then 1 else 0 := by
  unfold trigConst
  split_ifs with h <;> simp [h]

theorem trigPoly_mono (d : ℤ) (x : ℝ) :
    trigPoly {(0, 0)} (fun _ => 1) (fun _ => d) x = Complex.exp ((d : ℝ) * x * I) := by
  simp [trigPoly]

end

end RHTower.Weyl
