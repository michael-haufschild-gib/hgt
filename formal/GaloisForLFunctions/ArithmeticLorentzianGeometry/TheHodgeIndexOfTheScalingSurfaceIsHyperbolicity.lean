import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianFormsAtDegreeTwo
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw

/-!
# The Hodge index of the scaling surface is hyperbolicity

For a Hermitian matrix `H` the reverse Cauchy–Schwarz inequality

    H[x] H[y] ≤ |x* H y|²    whenever H[x] > 0

says exactly that `H` has at most one positive square (`hermPosIndex_le_one_iff`). Applied to the
intersection form of the scaling surface of `ℤ` (ArithmeticCastelnuovoSeveri), whose pole plane
always supplies one positive square, this turns the Hodge index theorem into the inequality of
Khovanskii–Teissier type that Lorentzian theory works with
(`riemannHypothesis_iff_intersectionGram_isHyperbolicHerm`):

    RH  ⇔  D² E² ≤ |D·E|²  for all cycles D, E of every finite family with D² > 0.

**The nef shift** (`exists_nef_shift_nonneg`, `isLorentzian_nefShift_iff`): on any real symmetric
form containing a hyperbolic plane `⟨H, V⟩`, the change of basis `f_i ↦ f_i + t(H + V)` makes every
entry of a finite Gram matrix nonnegative for large `t`, without changing the signature. Hence
"Lorentzian in some nef basis" is equivalent to "hyperbolic": at degree two, nonnegativity of
coefficients carries information only in a fixed basis.
-/

noncomputable section

open Matrix Finset Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι]

/-! ### Hermitian hyperbolicity -/

/-- The sesquilinear pairing `x* H y`. -/
def hermPair (H : Matrix ι ι ℂ) (x y : ι → ℂ) : ℂ := star x ⬝ᵥ H *ᵥ y

theorem hermPair_swap {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (x y : ι → ℂ) :
    hermPair H y x = conj (hermPair H x y) := by
  unfold hermPair
  change _ = star _
  rw [star_dotProduct, star_star, star_mulVec, hH.eq, ← dotProduct_mulVec]

theorem hermPair_self {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (x : ι → ℂ) :
    hermPair H x x = (hermQuad H x : ℂ) := by
  have h := hermPair_swap hH x x
  apply Complex.ext
  · simp [hermQuad, hermPair]
  · have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    simp only [Complex.ofReal_im]
    linarith

theorem hermPair_add_right (H : Matrix ι ι ℂ) (x y z : ι → ℂ) :
    hermPair H x (y + z) = hermPair H x y + hermPair H x z := by
  simp only [hermPair, mulVec_add, dotProduct_add]

theorem hermPair_add_left (H : Matrix ι ι ℂ) (x y z : ι → ℂ) :
    hermPair H (x + y) z = hermPair H x z + hermPair H y z := by
  simp only [hermPair, star_add, add_dotProduct]

theorem hermPair_smul_right (H : Matrix ι ι ℂ) (c : ℂ) (x y : ι → ℂ) :
    hermPair H x (c • y) = c * hermPair H x y := by
  simp only [hermPair, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermPair_smul_left (H : Matrix ι ι ℂ) (c : ℂ) (x y : ι → ℂ) :
    hermPair H (c • x) y = conj c * hermPair H x y := by
  simp only [hermPair, star_smul, smul_dotProduct, smul_eq_mul]
  rfl

/-- Expansion along a `H`-orthogonal splitting: `H[c x + z] = |c|² H[x] + H[z]` when `x* H z = 0`. -/
theorem hermQuad_smul_add_of_orth {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (c : ℂ)
    {x z : ι → ℂ} (hxz : hermPair H x z = 0) :
    hermQuad H (c • x + z) = Complex.normSq c * hermQuad H x + hermQuad H z := by
  have hzx : hermPair H z x = 0 := by rw [hermPair_swap hH, hxz, map_zero]
  have e : hermPair H (c • x + z) (c • x + z) =
      conj c * c * hermPair H x x + hermPair H z z := by
    rw [hermPair_add_left, hermPair_add_right, hermPair_add_right, hermPair_smul_left,
      hermPair_smul_left, hermPair_smul_right, hermPair_smul_right, hxz, hzx]
    ring
  have h1 := congrArg Complex.re e
  rw [hermPair_self hH, hermPair_self hH, hermPair_self hH] at h1
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_im, mul_zero, sub_zero] at h1
  rw [h1, Complex.normSq_apply]
  ring

/-- **Hermitian hyperbolicity**: the reverse Cauchy–Schwarz inequality
`H[x] H[y] ≤ |x* H y|²` whenever `H[x] > 0`. -/
def IsHyperbolicHerm (H : Matrix ι ι ℂ) : Prop :=
  ∀ x y : ι → ℂ, 0 < hermQuad H x → hermQuad H x * hermQuad H y ≤ Complex.normSq (hermPair H x y)

variable [DecidableEq ι]

/-- **One positive square ⇔ reverse Cauchy–Schwarz.** -/
theorem hermPosIndex_le_one_iff {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    hermPosIndex H ≤ 1 ↔ IsHyperbolicHerm H := by
  constructor
  · intro hidx x y hx
    set A := hermQuad H x
    set c : ℂ := hermPair H x y / (A : ℂ) with hc
    set z := y - c • x with hz
    have hA : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hxz : hermPair H x z = 0 := by
      rw [hz, sub_eq_add_neg, hermPair_add_right, ← neg_smul, hermPair_smul_right,
        hermPair_self hH, hc]
      field_simp
      ring
    -- `H[z] ≤ 0`: otherwise `span {x, z}` is a positive definite plane
    have hzneg : hermQuad H z ≤ 0 := by
      by_contra hzpos
      push Not at hzpos
      have hpd : ∀ a b : ℂ, a • x + b • z ≠ 0 → 0 < hermQuad H (a • x + b • z) := by
        intro a b hne
        have hbz : hermPair H x (b • z) = 0 := by rw [hermPair_smul_right, hxz, mul_zero]
        rw [hermQuad_smul_add_of_orth hH a hbz]
        have hbz' : hermQuad H (b • z) = Complex.normSq b * hermQuad H z := by
          have := hermQuad_smul_add_of_orth hH b (x := z) (z := 0) (by simp [hermPair])
          simpa [hermQuad] using this
        rw [hbz']
        rcases eq_or_ne a 0 with rfl | ha
        · rcases eq_or_ne b 0 with rfl | hb
          · simp at hne
          · simp only [map_zero, zero_mul, zero_add]
            exact mul_pos (Complex.normSq_pos.mpr hb) hzpos
        · have := mul_pos (Complex.normSq_pos.mpr ha) hx
          have := mul_nonneg (Complex.normSq_nonneg b) hzpos.le
          linarith
      have hli : LinearIndependent ℂ ![x, z] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        by_contra hne
        have hne' : s • x + t • z ≠ 0 ∨ s • x + t • z = 0 := (em _).symm.elim Or.inr Or.inl
        have hpos := hpd s t
        rw [hst] at hpos
        have h0 : ¬ (0 : ℝ) < hermQuad H 0 := by simp [hermQuad]
        -- `(s, t) ≠ 0` yet the combination vanishes: test against `x`
        have hx0 : hermPair H x (s • x + t • z) = 0 := by rw [hst]; simp [hermPair]
        rw [hermPair_add_right, hermPair_smul_right, hermPair_smul_right, hxz, mul_zero,
          add_zero, hermPair_self hH] at hx0
        have hs : s = 0 := by
          rcases mul_eq_zero.mp hx0 with h | h
          · exact h
          · exact absurd h hA
        subst hs
        have ht : t ≠ 0 := fun ht => hne ⟨rfl, ht⟩
        rw [zero_smul, zero_add] at hst
        have hz0 : z = 0 := by
          rcases smul_eq_zero.mp hst with h | h
          · exact absurd h ht
          · exact h
        rw [hz0] at hzpos
        simp [hermQuad] at hzpos
      have hW : IsPosDefOn H (Submodule.span ℂ (Set.range ![x, z])) := by
        intro w hw hw0
        rw [Submodule.mem_span_range_iff_exists_fun] at hw
        obtain ⟨c', rfl⟩ := hw
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one] at hw0 ⊢
        exact hpd _ _ hw0
      have := finrank_le_posIndex hW
      rw [finrank_span_eq_card hli, Fintype.card_fin] at this
      omega
    -- `y = c x + z` with `x* H z = 0`
    have hy : y = c • x + z := by rw [hz]; abel
    have hq : hermQuad H y = Complex.normSq c * A + hermQuad H z := by
      rw [hy]; exact hermQuad_smul_add_of_orth hH c hxz
    have hcA : Complex.normSq c * A = Complex.normSq (hermPair H x y) / A := by
      rw [hc, Complex.normSq_div, Complex.normSq_ofReal]
      field_simp
    rw [hq, hcA]
    have hx' : A ≠ 0 := hx.ne'
    calc A * (Complex.normSq (hermPair H x y) / A + hermQuad H z)
        = Complex.normSq (hermPair H x y) + A * hermQuad H z := by field_simp
      _ ≤ Complex.normSq (hermPair H x y) := by nlinarith
  · intro h
    by_cases hpos : ∃ u, 0 < hermQuad H u
    · obtain ⟨u, hu⟩ := hpos
      let φ : Fin 1 → (ι → ℂ) →ₗ[ℂ] ℂ := fun _ =>
        { toFun := hermPair H u
          map_add' := hermPair_add_right H u
          map_smul' := fun c y => by simp [hermPair_smul_right] }
      have := negIndex_le_card_of_nonneg_on_ker (-H) φ fun y hy => by
        have hy0 : hermPair H u y = 0 := hy 0
        have := h u y hu
        rw [hy0, map_zero] at this
        rw [hermQuad_neg]
        nlinarith
      simpa [hermNegIndex] using this
    · push Not at hpos
      obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex H
      by_contra hgt
      have hne : W ≠ ⊥ := by
        rintro rfl
        rw [finrank_bot] at hrank
        omega
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      exact absurd (hpos w) (not_le.mpr (hW w hwW hw0))

/-! ### The scaling surface -/

/-- **The Hodge index theorem of the scaling surface as reverse Cauchy–Schwarz.** RH holds iff,
for every finite family of `C²` compactly supported tests, the arithmetic intersection form on
`H, V, f₁, …, f_n` satisfies `D² E² ≤ |D·E|²` whenever `D² > 0`. -/
theorem riemannHypothesis_iff_intersectionGram_isHyperbolicHerm :
    RiemannHypothesis ↔ ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) →
        IsHyperbolicHerm (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) := by
  rw [riemannHypothesis_iff_one_positive_square]
  refine forall_congr' fun n => forall_congr' fun f => forall_congr' fun _ =>
    forall_congr' fun _ => ?_
  have hH : (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f).IsHermitian := by
    unfold intersectionGram
    exact (Matrix.isHermitian_fromBlocks_iff).mpr ⟨polePlane_isHermitian, rfl,
      localGram_isHermitian _ f⟩
  rw [← hermPosIndex_le_one_iff hH, posIndex_intersectionGram]
  omega

/-! ### The nef shift -/

/-- The nef shift of a family: `f_i ↦ f_i + t(H + V)` on `Fin 2 ⊕ ι`, the identity on the pole
plane. -/
def nefShift (t : ℝ) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℝ :=
  fromBlocks 1 (Matrix.of fun _ _ => t) 0 1

theorem nefShift_mul_neg (t : ℝ) :
    (nefShift t : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℝ) * nefShift (-t) = 1 := by
  rw [nefShift, nefShift, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_zero]
  rw [← fromBlocks_one]
  congr 1
  ext i j
  simp

/-- **Signature is unchanged by the nef shift.** -/
theorem isHyperbolic_nefShift_iff {G : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℝ} (t : ℝ) :
    IsHyperbolic ((nefShift t)ᵀ * G * nefShift t) ↔ IsHyperbolic G := by
  refine ⟨fun h => ?_, fun h => h.pullback _⟩
  have := h.pullback (nefShift (-t))
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, nefShift_mul_neg, Matrix.mul_one, ← Matrix.mul_assoc,
    nefShift_mul_neg, transpose_one, Matrix.one_mul] at this

/-- The pole plane in real form: `H² = V² = 0`, `H·V = 1`. -/
def realPolePlane : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- **The nef shift makes every entry nonnegative.** For a real Gram matrix whose pole block is the
hyperbolic plane, all entries of the shifted Gram are nonnegative once `t` is large. -/
theorem exists_nef_shift_nonneg (B : Matrix (Fin 2) ι ℝ) (L : Matrix ι ι ℝ) :
    ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → ∀ a b,
      0 ≤ ((nefShift t)ᵀ * fromBlocks realPolePlane B Bᵀ L * nefShift t) a b := by
  -- the entries are `L_ij + t (ρ_i + ρ_j) + 2t²`, `B_ki + t` and the pole plane
  let M : ℝ := 1 + ∑ i, ∑ j, |L i j| + 2 * ∑ k, ∑ i, |B k i|
  have hM : 1 ≤ M := by
    have h1 : 0 ≤ ∑ i, ∑ j, |L i j| := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    have h2 : 0 ≤ ∑ k, ∑ i, |B k i| := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    simp only [M]; linarith
  have hL : ∀ i j, |L i j| ≤ M := fun i j => by
    have h2 : 0 ≤ ∑ k, ∑ i, |B k i| := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    have := (single_le_sum (fun j _ => abs_nonneg (L i j)) (mem_univ j)).trans
      (single_le_sum (f := fun i => ∑ j, |L i j|)
        (fun i _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ i))
    simp only [M]; linarith
  have hB : ∀ k i, |B k i| ≤ M := fun k i => by
    have h1 : 0 ≤ ∑ i, ∑ j, |L i j| := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    have := (single_le_sum (fun i _ => abs_nonneg (B k i)) (mem_univ i)).trans
      (single_le_sum (f := fun k => ∑ i, |B k i|)
        (fun k _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ k))
    simp only [M]; linarith
  refine ⟨M, fun t ht a b => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  rw [nefShift, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  rcases a with a | a <;> rcases b with b | b
  · simp only [fromBlocks_apply₁₁, transpose_one, transpose_zero, Matrix.one_mul, Matrix.zero_mul,
      add_zero, Matrix.mul_one, Matrix.mul_zero]
    fin_cases a <;> fin_cases b <;> simp [realPolePlane]
  · simp only [fromBlocks_apply₁₂, transpose_one, transpose_zero, Matrix.one_mul, Matrix.zero_mul,
      add_zero, Matrix.mul_one, Matrix.mul_zero]
    simp only [Matrix.add_apply, mul_apply, Fin.sum_univ_two, realPolePlane, Matrix.of_apply]
    fin_cases a <;> simp <;> linarith [neg_abs_le (B 0 b), neg_abs_le (B 1 b), hB 0 b, hB 1 b]
  · simp only [fromBlocks_apply₂₁, transpose_one, transpose_zero, Matrix.one_mul, Matrix.zero_mul,
      add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    simp only [Matrix.add_apply, mul_apply, Fin.sum_univ_two, realPolePlane, Matrix.of_apply,
      transpose_apply]
    fin_cases b <;> simp <;> linarith [neg_abs_le (B 0 a), neg_abs_le (B 1 a), hB 0 a, hB 1 a]
  · simp only [fromBlocks_apply₂₂, transpose_one, transpose_zero, Matrix.one_mul, Matrix.zero_mul,
      add_zero, Matrix.mul_one, Matrix.mul_zero, zero_add]
    simp only [Matrix.add_apply, mul_apply, Fin.sum_univ_two, realPolePlane, Matrix.of_apply,
      transpose_apply]
    simp
    nlinarith [neg_abs_le (L a b), neg_abs_le (B 0 a), neg_abs_le (B 1 a), neg_abs_le (B 0 b),
      neg_abs_le (B 1 b), hB 0 a, hB 1 a, hB 0 b, hB 1 b, hL a b]

/-- **Lorentzian in a nef basis is hyperbolic.** For a symmetric Gram matrix with a hyperbolic pole
plane, the shifted Gram is Lorentzian for all large `t` iff the Gram is hyperbolic: entrywise
nonnegativity in a nef basis carries no information beyond the signature. -/
theorem isLorentzian_nefShift_iff (B : Matrix (Fin 2) ι ℝ) {L : Matrix ι ι ℝ} (hL : L.IsSymm) :
    ∃ t₀ : ℝ, ∀ t, t₀ ≤ t →
      (IsLorentzian ((nefShift t)ᵀ * fromBlocks realPolePlane B Bᵀ L * nefShift t) ↔
        IsHyperbolic (fromBlocks realPolePlane B Bᵀ L)) := by
  obtain ⟨t₀, ht₀⟩ := exists_nef_shift_nonneg B L
  refine ⟨t₀, fun t ht => ⟨fun h => (isHyperbolic_nefShift_iff t).mp h.2.2, fun h => ⟨?_,
    ht₀ t ht, (isHyperbolic_nefShift_iff t).mpr h⟩⟩⟩
  have hG : (fromBlocks realPolePlane B Bᵀ L).IsSymm := by
    unfold Matrix.IsSymm
    rw [fromBlocks_transpose, transpose_transpose, hL.eq]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  unfold Matrix.IsSymm
  rw [transpose_mul, transpose_mul, transpose_transpose, hG.eq, Matrix.mul_assoc]

end GaloisForLFunctions.ArithmeticLorentzianGeometry
