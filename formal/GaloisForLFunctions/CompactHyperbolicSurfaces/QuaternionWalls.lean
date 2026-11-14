import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionCocompact
import GaloisForLFunctions.CompactHyperbolicSurfaces.HyperbolicElements

/-!
# Walls and a homomorphism `Γ(N) → ℤ`

A *wall* of level `N` is a pure quaternion `w ∈ O` with `nrd w = −2` and `w ≡ i mod N`.  For a
matrix `M` let `H_M(x + iy) = M₁₀(x² + y²) − (M₀₀ − M₁₁)x − M₀₁`; for `M = ι(w)` its zero set is the
geodesic fixed by the reflection in `w`, and

  `H_{gMg⁻¹}(gz) = H_M(z)/|cz + d|²`   (`hermForm_conj_smul`),

so the side of a wall on which a point lies is equivariant.  Conjugation by `γ ∈ Γ(N)` permutes the
walls (`wallEquiv`).  A wall separating two points `z, z'` meets the Euclidean segment `[z, z']`,
and a wall through `x + iy` has `(cx − a)² + (cy)² = 2`, so its entries are bounded in terms of
`|x|`, `y`, `1/y`: only finitely many walls separate points of a compact set
(`finite_separating`).

The signed count `θ(z) = Σ_w (1[H_w(z) > 0] − 1[H_w(z₀) > 0])` satisfies the cocycle law
`θ(γz) = θ(z) + θ(γz₀)` (`wallCount_smul`), so `χ(γ) = θ(γz₀)` is a homomorphism (`wallHom`);
`θ` is measurable and has bounded increments over bounded distances.

Also: every `γ ≠ 1` in `Γ(N)`, `N ≥ 3`, is hyperbolic (`two_lt_abs_trSL_congGroup`).
-/

open Matrix UpperHalfPlane Set Filter
open scoped MatrixGroups Topology

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Hyperbolicity in `Γ(N)` -/

/-- **Every nontrivial element of `Γ(N)` is hyperbolic**, `N ≥ 3`: `tr γ = 2x₀` with
`x₀ ≡ 1 mod N`, and `x₀ = 1` forces the pure part to have norm zero, hence to vanish. -/
theorem two_lt_abs_trSL_congGroup {N : ℕ} (hN : 3 ≤ N) (γ : congGroup N) (hγ : γ ≠ 1) :
    2 < |trSL (γ : SL(2, ℝ))| := by
  obtain ⟨x, hx1, ⟨u, hu⟩, hxg⟩ := γ.2
  have hent : ∀ i j, (γ : SL(2, ℝ)) i j = quatMat x i j := fun i j => by
    rw [show (γ : SL(2, ℝ)) i j = ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j from rfl, hxg]
  have htr : trSL (γ : SL(2, ℝ)) = 2 * (x 0 : ℝ) := by
    rw [trSL, hent, hent]; simp [quatMat_apply]; ring
  have hx0 : x 0 = 1 + (N : ℤ) * u 0 := by
    have := congrFun hu 0
    simpa [quatOne] using this
  have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
  rw [htr]
  by_contra hle
  have hle' : |(x 0 : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_two] at hle; linarith [not_lt.mp hle]
  have hle'' : |x 0| ≤ 1 := by exact_mod_cast hle'
  have hb := abs_le.mp hle''
  rcases (show x 0 = -1 ∨ x 0 = 0 ∨ x 0 = 1 by omega) with h | h | h
  · have hd : (N : ℤ) ∣ 2 := ⟨-u 0, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd; omega
  · have hd : (N : ℤ) ∣ 1 := ⟨-u 0, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd; omega
  · have hpure : nrd (x - quatOne) = 0 := by
      have h1 := hx1
      simp [nrd, quatOne, h] at h1 ⊢ <;> linarith
    have hxe : x = quatOne := sub_eq_zero.mp (eq_zero_of_nrd_eq_zero _ hpure)
    apply hγ
    apply Subtype.ext
    apply Subtype.ext
    rw [hxg, hxe, quatMat_one]
    rfl

/-! ### The Möbius action in coordinates -/

/-- `|cz + d|²`. -/
def denomSq (g : SL(2, ℝ)) (z : ℍ) : ℝ := (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2

theorem denomSq_pos (g : SL(2, ℝ)) (z : ℍ) : 0 < denomSq g z := by
  have hdet := det_SL g
  have hy := z.im_pos
  unfold denomSq
  rcases eq_or_ne (g 1 0) 0 with h | h
  · rw [h] at hdet ⊢
    have : g 1 1 ≠ 0 := fun h' => by rw [h'] at hdet; simp at hdet
    simp only [zero_mul, zero_add]
    positivity
  · have : 0 < (g 1 0 * z.im) ^ 2 := by positivity
    positivity

theorem coe_smul_SL (g : SL(2, ℝ)) (z : ℍ) : ((g • z : ℍ) : ℂ) =
    ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1) := by
  rw [coe_specialLinearGroup_apply]
  rfl

/-- `gz · |cz + d|² = (az + b)(c z̄ + d)`. -/
theorem smul_SL_mul_denomSq (g : SL(2, ℝ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) * (denomSq g z : ℂ) =
      ((g 0 0 : ℂ) * z + g 0 1) * ((g 1 0 : ℂ) * (starRingEnd ℂ) (z : ℂ) + g 1 1) := by
  have hne : ((g 1 0 : ℂ) * z + g 1 1) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero, Complex.zero_re,
      Complex.add_im, Complex.mul_im, add_zero, Complex.zero_im] at h1 h2
    have := denomSq_pos g z
    rw [denomSq, h1, h2] at this
    norm_num at this
  have hN : Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) = denomSq g z := by
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero, Complex.add_im,
      Complex.mul_im, add_zero]
    unfold denomSq; ring
  have hD : (denomSq g z : ℂ) =
      ((g 1 0 : ℂ) * z + g 1 1) * ((g 1 0 : ℂ) * (starRingEnd ℂ) (z : ℂ) + g 1 1) := by
    rw [← hN, ← Complex.mul_conj, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  rw [coe_smul_SL, hD, ← mul_assoc, div_mul_cancel₀ _ hne]

theorem re_smul_SL (g : SL(2, ℝ)) (z : ℍ) : (g • z).re =
    ((g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) + g 0 0 * g 1 0 * z.im ^ 2) /
      denomSq g z := by
  have h := congrArg Complex.re (smul_SL_mul_denomSq g z)
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.conj_re, Complex.conj_im,
    Complex.mul_im, Complex.add_im, zero_mul, sub_zero, add_zero, mul_zero] at h
  rw [eq_div_iff (denomSq_pos g z).ne']
  linear_combination h

theorem im_smul_SL (g : SL(2, ℝ)) (z : ℍ) : (g • z).im = z.im / denomSq g z := by
  have h := congrArg Complex.im (smul_SL_mul_denomSq g z)
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, Complex.conj_re, Complex.conj_im,
    Complex.mul_im, Complex.add_im, zero_mul, sub_zero, add_zero, mul_zero] at h
  have hdet := det_SL g
  rw [eq_div_iff (denomSq_pos g z).ne']
  linear_combination h + z.im * hdet

/-- `|gz|² = |az + b|²/|cz + d|²`. -/
theorem normSq_smul_SL (g : SL(2, ℝ)) (z : ℍ) : (g • z).re ^ 2 + (g • z).im ^ 2 =
    ((g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2) / denomSq g z := by
  have hD := (denomSq_pos g z).ne'
  have hdet := det_SL g
  have hAB : ((g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) + g 0 0 * g 1 0 * z.im ^ 2) ^ 2 +
      z.im ^ 2 = ((g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2) * denomSq g z := by
    unfold denomSq
    linear_combination (-(z.im ^ 2) * (g 0 0 * g 1 1 - g 0 1 * g 1 0 + 1)) * hdet
  rw [re_smul_SL, im_smul_SL, div_pow, div_pow, ← add_div, hAB, sq (denomSq g z),
    mul_div_mul_right _ _ hD]

/-! ### The side form -/

/-- `H_M(x + iy) = M₁₀(x² + y²) − (M₀₀ − M₁₁)x − M₀₁`. -/
def hermR (M : Matrix (Fin 2) (Fin 2) ℝ) (x y : ℝ) : ℝ :=
  M 1 0 * (x ^ 2 + y ^ 2) - (M 0 0 - M 1 1) * x - M 0 1

/-- `H_M` on `ℍ`. -/
def hermForm (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℍ) : ℝ := hermR M z.re z.im

theorem continuous_hermForm (M : Matrix (Fin 2) (Fin 2) ℝ) : Continuous (hermForm M) :=
  ((continuous_const.mul ((continuous_re.pow 2).add (continuous_im.pow 2))).sub
    (continuous_const.mul continuous_re)).sub continuous_const

/-- The Hermitian identity behind equivariance: `Q_{gMg^♯}(gv) = (det g)² Q_M(v)`. -/
theorem hermR_identity (p q r t m00 m01 m10 m11 x y : ℝ) :
    ((r * m00 + t * m10) * t + (r * m01 + t * m11) * -r) * ((p * x + q) ^ 2 + (p * y) ^ 2) -
      (((p * m00 + q * m10) * t + (p * m01 + q * m11) * -r) -
        ((r * m00 + t * m10) * -q + (r * m01 + t * m11) * p)) *
          ((p * x + q) * (r * x + t) + p * r * y ^ 2) -
      ((p * m00 + q * m10) * -q + (p * m01 + q * m11) * p) * ((r * x + t) ^ 2 + (r * y) ^ 2) =
    (p * t - q * r) ^ 2 * (m10 * (x ^ 2 + y ^ 2) - (m00 - m11) * x - m01) := by
  ring

/-- **Equivariance of the side form.**  `H_{gMg⁻¹}(gz) = H_M(z)/|cz + d|²`. -/
theorem hermForm_conj_smul (g : SL(2, ℝ)) (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℍ) :
    hermForm ((g : Matrix (Fin 2) (Fin 2) ℝ) * M * adjugate (g : Matrix (Fin 2) (Fin 2) ℝ))
      (g • z) = hermForm M z / denomSq g z := by
  have hD := (denomSq_pos g z).ne'
  have hdet := det_SL g
  have key : ∀ m c e B A : ℝ, m * (B / denomSq g z) - c * (A / denomSq g z) - e =
      (m * B - c * A - e * denomSq g z) / denomSq g z := fun m c e B A => by
    rw [sub_div, sub_div, mul_div_assoc, mul_div_assoc, mul_div_cancel_right₀ _ hD]
  simp only [hermForm, hermR]
  rw [normSq_smul_SL, re_smul_SL, key]
  congr 1
  simp only [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  unfold denomSq
  linear_combination hermR_identity (g 0 0) (g 0 1) (g 1 0) (g 1 1) (M 0 0) (M 0 1) (M 1 0)
      (M 1 1) z.re z.im +
    (g 0 0 * g 1 1 - g 0 1 * g 1 0 + 1) *
      (M 1 0 * (z.re ^ 2 + z.im ^ 2) - (M 0 0 - M 1 1) * z.re - M 0 1) * hdet

/-! ### Walls -/

/-- `y ≡ a mod N·O`. -/
def IsCongTo (N : ℕ) (a y : Fin 4 → ℤ) : Prop := ∃ u : Fin 4 → ℤ, y = a + (N : ℤ) • u

theorem isCongTo_mul {N : ℕ} {a b x y : Fin 4 → ℤ} (hx : IsCongTo N a x) (hy : IsCongTo N b y) :
    IsCongTo N (quatMul a b) (quatMul x y) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨quatMul a v + quatMul u b + (N : ℤ) • quatMul u v, ?_⟩
  funext k
  fin_cases k <;> simp [quatMul, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem isCongTo_conj {N : ℕ} {a x : Fin 4 → ℤ} (hx : IsCongTo N a x) :
    IsCongTo N (quatConj a) (quatConj x) := by
  obtain ⟨u, rfl⟩ := hx
  refine ⟨quatConj u, ?_⟩
  funext k
  fin_cases k <;> simp [quatConj] <;> ring

/-- The quaternion `i`. -/
def quatI : Fin 4 → ℤ := ![0, 1, 0, 0]

/-- **Walls of level `N`**: pure quaternions of norm `−2` congruent to `i` mod `N`. -/
def wallSet (N : ℕ) : Set (Fin 4 → ℤ) := {w | w 0 = 0 ∧ nrd w = -2 ∧ IsCongTo N quatI w}

/-- The side function `H_w` of a wall. -/
def wallSide (w : Fin 4 → ℤ) (z : ℍ) : ℝ := hermForm (quatMat w) z

/-- `x w x̄`. -/
def conjQ (x w : Fin 4 → ℤ) : Fin 4 → ℤ := quatMul (quatMul x w) (quatConj x)

theorem quatMat_conjQ (x w : Fin 4 → ℤ) :
    quatMat (conjQ x w) = quatMat x * quatMat w * adjugate (quatMat x) := by
  rw [conjQ, ← quatMat_mul, ← quatMat_mul, adjugate_quatMat]

theorem quatConj_quatConj (x : Fin 4 → ℤ) : quatConj (quatConj x) = x := by
  funext k; fin_cases k <;> simp [quatConj]

/-- `trd (x w x̄) = nrd x · trd w`. -/
theorem conjQ_zero (x w : Fin 4 → ℤ) : conjQ x w 0 = nrd x * w 0 := by
  simp [conjQ, quatMul, quatConj, nrd] <;> ring

theorem conjQ_mem_wallSet {N : ℕ} {x w : Fin 4 → ℤ} (hx1 : nrd x = 1) (hx : IsCong N x)
    (hw : w ∈ wallSet N) : conjQ x w ∈ wallSet N := by
  obtain ⟨hw0, hw2, hwc⟩ := hw
  have hx' : IsCongTo N quatOne x := hx
  refine ⟨by rw [conjQ_zero, hw0, mul_zero], ?_, ?_⟩
  · rw [conjQ, nrd_quatMul, nrd_quatMul, nrd_quatConj, hx1, hw2]; ring
  · have h := isCongTo_mul (isCongTo_mul hx' hwc) (isCongTo_conj hx')
    have hI : quatMul (quatMul quatOne quatI) (quatConj quatOne) = quatI := by
      funext k
      fin_cases k <;> simp [quatMul, quatOne, quatI, quatConj, Matrix.vecHead, Matrix.vecTail]
    rwa [hI] at h

/-- `x̄ (x w x̄) x = w` for `nrd x = 1`. -/
theorem conjQ_conj_conjQ {x : Fin 4 → ℤ} (hx1 : nrd x = 1) (w : Fin 4 → ℤ) :
    conjQ (quatConj x) (conjQ x w) = w := by
  apply quatMat_injective
  have hX : adjugate (quatMat x) * quatMat x = 1 := by
    rw [adjugate_mul, det_quatMat, hx1]; simp
  rw [quatMat_conjQ, quatMat_conjQ, adjugate_quatMat (quatConj x), quatConj_quatConj,
    ← adjugate_quatMat x]
  calc adjugate (quatMat x) * (quatMat x * quatMat w * adjugate (quatMat x)) * quatMat x
      = (adjugate (quatMat x) * quatMat x) * quatMat w * (adjugate (quatMat x) * quatMat x) := by
        simp only [Matrix.mul_assoc]
    _ = quatMat w := by rw [hX, Matrix.one_mul, Matrix.mul_one]

/-- The quaternion of `γ ∈ Γ(N)`. -/
def quatOf {N : ℕ} (γ : congGroup N) : Fin 4 → ℤ := Classical.choose (mem_congGroup.mp γ.2)

theorem quatOf_spec {N : ℕ} (γ : congGroup N) : nrd (quatOf γ) = 1 ∧ IsCong N (quatOf γ) ∧
    ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = quatMat (quatOf γ) :=
  Classical.choose_spec (mem_congGroup.mp γ.2)

theorem nrd_quatConj_quatOf {N : ℕ} (γ : congGroup N) : nrd (quatConj (quatOf γ)) = 1 := by
  rw [nrd_quatConj]; exact (quatOf_spec γ).1

/-- **`Γ(N)` permutes the walls** by `w ↦ γ w γ⁻¹`. -/
def wallEquiv {N : ℕ} (γ : congGroup N) : wallSet N ≃ wallSet N where
  toFun w := ⟨conjQ (quatOf γ) w, conjQ_mem_wallSet (quatOf_spec γ).1 (quatOf_spec γ).2.1 w.2⟩
  invFun w := ⟨conjQ (quatConj (quatOf γ)) w,
    conjQ_mem_wallSet (nrd_quatConj_quatOf γ) (isCong_conj (quatOf_spec γ).2.1) w.2⟩
  left_inv w := Subtype.ext (conjQ_conj_conjQ (quatOf_spec γ).1 w)
  right_inv w := by
    apply Subtype.ext
    have h := conjQ_conj_conjQ (nrd_quatConj_quatOf γ) w
    rwa [quatConj_quatConj] at h

theorem wallEquiv_apply {N : ℕ} (γ : congGroup N) (w : wallSet N) :
    ((wallEquiv γ w : wallSet N) : Fin 4 → ℤ) = conjQ (quatOf γ) w := rfl

theorem wallSide_conjQ {N : ℕ} (γ : congGroup N) (w : Fin 4 → ℤ) (z : ℍ) :
    wallSide (conjQ (quatOf γ) w) ((γ : SL(2, ℝ)) • z) = wallSide w z / denomSq γ z := by
  rw [wallSide, wallSide, quatMat_conjQ, ← (quatOf_spec γ).2.2]
  exact hermForm_conj_smul _ _ _

/-- `1` on the positive side, `0` otherwise. -/
def posInd (r : ℝ) : ℤ := if 0 < r then 1 else 0

theorem posInd_div {a b : ℝ} (hb : 0 < b) : posInd (a / b) = posInd a := by
  simp [posInd, div_pos_iff_of_pos_right hb]

theorem abs_posInd_sub_le (a b : ℝ) : |posInd a - posInd b| ≤ 1 := by
  unfold posInd; split_ifs <;> norm_num

theorem posInd_wallSide_conjQ {N : ℕ} (γ : congGroup N) (w : Fin 4 → ℤ) (z : ℍ) :
    posInd (wallSide (conjQ (quatOf γ) w) ((γ : SL(2, ℝ)) • z)) = posInd (wallSide w z) := by
  rw [wallSide_conjQ, posInd_div (denomSq_pos _ _)]

/-! ### Finitely many walls separate two points of a compact set -/

theorem finite_quatMat_le (t : ℝ) : {x : Fin 4 → ℤ | ∀ i j, |quatMat x i j| ≤ t}.Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin 4 => Set.Icc (-⌈t⌉) ⌈t⌉)
    fun _ => Set.finite_Icc _ _).subset ?_
  intro x hx
  refine Set.mem_univ_pi.mpr fun k => ?_
  have hb := abs_coord_le_of_entries hx k
  have h2 := Int.le_ceil t
  constructor
  · have : (-(⌈t⌉ : ℝ)) ≤ (x k : ℝ) := by linarith [(abs_le.mp hb).1]
    exact_mod_cast this
  · have : (x k : ℝ) ≤ (⌈t⌉ : ℝ) := by linarith [(abs_le.mp hb).2]
    exact_mod_cast this

/-- A trace-zero matrix of determinant `−2` whose form vanishes at `x + iy` satisfies
`(cx − a)² + (cy)² = 2`. -/
theorem sq_add_sq_of_hermR_eq_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M 1 1 = -M 0 0)
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = -2) {x y : ℝ} (h : hermR M x y = 0) :
    (M 1 0 * x - M 0 0) ^ 2 + (M 1 0 * y) ^ 2 = 2 := by
  unfold hermR at h
  linear_combination M 1 0 * h - hdet + (M 0 0 - M 1 0 * x) * hM

/-- The entry bound for walls through the box `|x| ≤ A`, `ε ≤ y ≤ B`. -/
def wallBound (A ε B : ℝ) : ℝ :=
  2 / ε * (A ^ 2 + B ^ 2) + 2 * (2 + 2 / ε * A) * A + (2 + 2 / ε * A) + 2 / ε

theorem abs_entries_le {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M 1 1 = -M 0 0)
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = -2) {x y A ε B : ℝ} (hε : 0 < ε) (hx : |x| ≤ A)
    (hyε : ε ≤ y) (hyB : y ≤ B) (h : hermR M x y = 0) : ∀ i j, |M i j| ≤ wallBound A ε B := by
  have key := sq_add_sq_of_hermR_eq_zero hM hdet h
  have hy : 0 < y := hε.trans_le hyε
  have hA : 0 ≤ A := (abs_nonneg x).trans hx
  have hc0 : 0 ≤ 2 / ε := by positivity
  have hcy : |M 1 0 * y| ≤ 2 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (M 1 0 * x - M 0 0)]) (by norm_num)
  have hcx : |M 1 0 * x - M 0 0| ≤ 2 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (M 1 0 * y)]) (by norm_num)
  have hc : |M 1 0| ≤ 2 / ε := by
    rw [le_div_iff₀ hε]
    rw [abs_mul, abs_of_pos hy] at hcy
    nlinarith [abs_nonneg (M 1 0)]
  have hcxA : |M 1 0 * x| ≤ 2 / ε * A := by
    rw [abs_mul]; exact mul_le_mul hc hx (abs_nonneg _) hc0
  have ha : |M 0 0| ≤ 2 + 2 / ε * A := by
    have h1 := abs_le.mp hcxA
    have h2 := abs_le.mp hcx
    rw [abs_le]; constructor <;> linarith
  have hxy : x ^ 2 + y ^ 2 ≤ A ^ 2 + B ^ 2 := by
    have h1 := abs_le.mp hx
    have : x ^ 2 ≤ A ^ 2 := sq_le_sq' h1.1 h1.2
    have : y ^ 2 ≤ B ^ 2 := sq_le_sq' (by linarith) hyB
    linarith
  have hb : |M 0 1| ≤ 2 / ε * (A ^ 2 + B ^ 2) + 2 * (2 + 2 / ε * A) * A := by
    have hbe : M 0 1 = M 1 0 * (x ^ 2 + y ^ 2) - 2 * M 0 0 * x := by
      unfold hermR at h; rw [hM] at h; linarith
    have hp : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have e1 : |M 1 0 * (x ^ 2 + y ^ 2)| ≤ 2 / ε * (A ^ 2 + B ^ 2) := by
      rw [abs_mul, abs_of_nonneg hp]; exact mul_le_mul hc hxy hp hc0
    have e2 : |2 * M 0 0 * x| ≤ 2 * (2 + 2 / ε * A) * A := by
      rw [abs_mul, abs_mul, abs_two]
      have := mul_le_mul ha hx (abs_nonneg _) (by linarith [abs_nonneg (M 0 0)])
      linarith
    rw [hbe]
    have f1 := abs_le.mp e1
    have f2 := abs_le.mp e2
    rw [abs_le]; constructor <;> linarith
  have t3 : 0 ≤ 2 + 2 / ε * A := by have := mul_nonneg hc0 hA; linarith
  have t2 : 0 ≤ 2 * (2 + 2 / ε * A) * A := mul_nonneg (mul_nonneg two_pos.le t3) hA
  have t1 : 0 ≤ 2 / ε * (A ^ 2 + B ^ 2) := mul_nonneg hc0 (by positivity)
  have hd : |M 1 1| = |M 0 0| := by rw [hM, abs_neg]
  intro i j
  unfold wallBound
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one] <;> linarith

theorem wall_trace {w : Fin 4 → ℤ} (hw0 : w 0 = 0) : quatMat w 1 1 = -quatMat w 0 0 := by
  simp [quatMat_apply, hw0]

theorem wall_det {w : Fin 4 → ℤ} (hw : nrd w = -2) :
    quatMat w 0 0 * quatMat w 1 1 - quatMat w 0 1 * quatMat w 1 0 = -2 := by
  have h := det_quatMat w
  rw [Matrix.det_fin_two, hw] at h
  rw [h]; norm_num

/-- Only finitely many walls pass through the box `|x| ≤ A`, `ε ≤ y ≤ B`. -/
theorem finite_walls_box (N : ℕ) {A ε B : ℝ} (hε : 0 < ε) :
    {w ∈ wallSet N | ∃ x y, |x| ≤ A ∧ ε ≤ y ∧ y ≤ B ∧ hermR (quatMat w) x y = 0}.Finite := by
  refine (finite_quatMat_le (wallBound A ε B)).subset ?_
  rintro w ⟨⟨hw0, hw2, -⟩, x, y, hx, hyε, hyB, h⟩
  exact abs_entries_le (wall_trace hw0) (wall_det hw2) hε hx hyε hyB h

/-- **Separation forces a zero on the segment.**  If `z, z'` lie on different sides of `H_M`,
then `H_M` vanishes at a point of the Euclidean segment `[z, z']`. -/
theorem exists_hermR_eq_zero (M : Matrix (Fin 2) (Fin 2) ℝ) {z z' : ℍ}
    (h : posInd (hermForm M z) ≠ posInd (hermForm M z')) :
    ∃ x y, |x| ≤ max |z.re| |z'.re| ∧ min z.im z'.im ≤ y ∧ y ≤ max z.im z'.im ∧
      hermR M x y = 0 := by
  have hcont : Continuous fun t : ℝ =>
      hermR M ((1 - t) * z.re + t * z'.re) ((1 - t) * z.im + t * z'.im) := by
    unfold hermR; fun_prop
  have h0 : hermR M ((1 - 0) * z.re + 0 * z'.re) ((1 - 0) * z.im + 0 * z'.im) = hermForm M z := by
    simp [hermForm]
  have h1 : hermR M ((1 - 1) * z.re + 1 * z'.re) ((1 - 1) * z.im + 1 * z'.im) = hermForm M z' := by
    simp [hermForm]
  have hzero : ∃ t ∈ Icc (0 : ℝ) 1,
      hermR M ((1 - t) * z.re + t * z'.re) ((1 - t) * z.im + t * z'.im) = 0 := by
    unfold posInd at h
    by_cases ha : 0 < hermForm M z
    · have hb : ¬ 0 < hermForm M z' := fun hb => h (by rw [if_pos ha, if_pos hb])
      exact intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn
        ⟨by rw [h1]; linarith [not_lt.mp hb], by rw [h0]; linarith⟩
    · have hb : 0 < hermForm M z' := by
        by_contra hb; exact h (by rw [if_neg ha, if_neg hb])
      exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn
        ⟨by rw [h0]; linarith [not_lt.mp ha], by rw [h1]; linarith⟩
  obtain ⟨t, ⟨ht0, ht1⟩, hφt⟩ := hzero
  have ht1' : 0 ≤ 1 - t := by linarith
  refine ⟨(1 - t) * z.re + t * z'.re, (1 - t) * z.im + t * z'.im, ?_, ?_, ?_, hφt⟩
  · have hm1 := abs_le.mp (le_max_left |z.re| |z'.re|)
    have hm2 := abs_le.mp (le_max_right |z.re| |z'.re|)
    rw [abs_le]; constructor
    · nlinarith [mul_nonneg ht1' (by linarith [hm1.1] : 0 ≤ z.re + max |z.re| |z'.re|),
        mul_nonneg ht0 (by linarith [hm2.1] : 0 ≤ z'.re + max |z.re| |z'.re|)]
    · nlinarith [mul_nonneg ht1' (by linarith [hm1.2] : 0 ≤ max |z.re| |z'.re| - z.re),
        mul_nonneg ht0 (by linarith [hm2.2] : 0 ≤ max |z.re| |z'.re| - z'.re)]
  · nlinarith [mul_nonneg ht1' (sub_nonneg.mpr (min_le_left z.im z'.im)),
      mul_nonneg ht0 (sub_nonneg.mpr (min_le_right z.im z'.im))]
  · nlinarith [mul_nonneg ht1' (sub_nonneg.mpr (le_max_left z.im z'.im)),
      mul_nonneg ht0 (sub_nonneg.mpr (le_max_right z.im z'.im))]

/-- **Local finiteness.**  Only finitely many walls separate two points of a compact set. -/
theorem finite_separating (N : ℕ) {K : Set ℍ} (hK : IsCompact K) :
    {w ∈ wallSet N | ∃ z ∈ K, ∃ z' ∈ K, posInd (wallSide w z) ≠ posInd (wallSide w z')}.Finite := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · convert Set.finite_empty
    ext w; simp
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℍ => z.re)
    continuous_re.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℍ => z.im)
    continuous_im.continuousOn
  obtain ⟨z₁, -, hmin⟩ := hK.exists_isMinOn hne (f := fun z : ℍ => z.im) continuous_im.continuousOn
  refine (finite_walls_box N (A := A) (B := B) z₁.im_pos).subset ?_
  rintro w ⟨hw, z, hz, z', hz', hne'⟩
  obtain ⟨x, y, hx, hy1, hy2, h0⟩ := exists_hermR_eq_zero (quatMat w) hne'
  refine ⟨hw, x, y, ?_, ?_, ?_, h0⟩
  · have h1 := hA z hz
    have h2 := hA z' hz'
    simp only [Real.norm_eq_abs] at h1 h2
    exact hx.trans (max_le h1 h2)
  · exact (le_min (isMinOn_iff.mp hmin z hz) (isMinOn_iff.mp hmin z' hz')).trans hy1
  · have h1 := hB z hz
    have h2 := hB z' hz'
    simp only [Real.norm_eq_abs] at h1 h2
    exact hy2.trans (max_le ((le_abs_self _).trans h1) ((le_abs_self _).trans h2))

/-- A finset containing every wall that separates two points of a compact set. -/
theorem exists_finset_separating (N : ℕ) {K : Set ℍ} (hK : IsCompact K) :
    ∃ s : Finset (wallSet N), ∀ w : wallSet N, ∀ z ∈ K, ∀ z' ∈ K,
      posInd (wallSide w z) ≠ posInd (wallSide w z') → w ∈ s := by
  classical
  refine ⟨((finite_separating N hK).preimage Subtype.val_injective.injOn).toFinset, ?_⟩
  intro w z hz z' hz' h
  rw [Set.Finite.mem_toFinset]
  exact ⟨w.2, z, hz, z', hz', h⟩

theorem finsum_eq_sum_of_separating {N : ℕ} {s : Finset (wallSet N)} {z z' : ℍ}
    (hs : ∀ w : wallSet N, posInd (wallSide w z) ≠ posInd (wallSide w z') → w ∈ s) :
    ∑ᶠ w : wallSet N, (posInd (wallSide w z) - posInd (wallSide w z')) =
      ∑ w ∈ s, (posInd (wallSide w z) - posInd (wallSide w z')) :=
  finsum_eq_sum_of_support_subset _ fun w hw => hs w fun h => hw (by simp only [h, sub_self])

theorem finite_support_sep {N : ℕ} (z z' : ℍ) :
    (Function.support fun w : wallSet N =>
      posInd (wallSide w z) - posInd (wallSide w z')).Finite := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_separating N ((Set.finite_singleton z').insert z).isCompact
  refine s.finite_toSet.subset fun w hw => ?_
  exact hs w z (by simp) z' (by simp) fun h => hw (by simp only [h, sub_self])

/-! ### The wall count -/

section wallCount

variable (N : ℕ) (z₀ : ℍ)

/-- **The wall count** `θ(z) = Σ_w (1[H_w(z) > 0] − 1[H_w(z₀) > 0])`. -/
def wallCount (z : ℍ) : ℤ := ∑ᶠ w : wallSet N, (posInd (wallSide w z) - posInd (wallSide w z₀))

variable {N}

theorem wallCount_self : wallCount N z₀ z₀ = 0 := by simp [wallCount]

theorem wallCount_sub (z z' : ℍ) : wallCount N z₀ z - wallCount N z₀ z' =
    ∑ᶠ w : wallSet N, (posInd (wallSide w z) - posInd (wallSide w z')) := by
  rw [wallCount, wallCount, ← finsum_sub_distrib (finite_support_sep z z₀)
    (finite_support_sep z' z₀)]
  congr 1; funext w; ring

theorem wallCount_smul_aux (γ : congGroup N) (z : ℍ) :
    wallCount N z₀ ((γ : SL(2, ℝ)) • z) =
      wallCount N z₀ z - wallCount N z₀ ((γ : SL(2, ℝ))⁻¹ • z₀) := by
  have he := finsum_comp_equiv (wallEquiv γ) (f := fun w : wallSet N =>
    posInd (wallSide w ((γ : SL(2, ℝ)) • z)) - posInd (wallSide w z₀))
  rw [wallCount_sub, wallCount, ← he]
  congr 1
  funext w
  have h2 := posInd_wallSide_conjQ γ w ((γ : SL(2, ℝ))⁻¹ • z₀)
  rw [smul_inv_smul] at h2
  simp only [wallEquiv_apply]
  rw [posInd_wallSide_conjQ, h2]

/-- **The cocycle law.**  `θ(γz) = θ(z) + θ(γz₀)` for `γ ∈ Γ(N)`. -/
theorem wallCount_smul (γ : congGroup N) (z : ℍ) :
    wallCount N z₀ ((γ : SL(2, ℝ)) • z) =
      wallCount N z₀ z + wallCount N z₀ ((γ : SL(2, ℝ)) • z₀) := by
  have h := wallCount_smul_aux z₀ γ z₀
  rw [wallCount_self, zero_sub] at h
  rw [wallCount_smul_aux, h, sub_eq_add_neg]

/-- **The wall homomorphism** `χ(γ) = θ(γz₀)`. -/
def wallHom : congGroup N →* Multiplicative ℤ where
  toFun γ := Multiplicative.ofAdd (wallCount N z₀ ((γ : SL(2, ℝ)) • z₀))
  map_one' := by simp [wallCount_self]
  map_mul' γ δ := by
    rw [Subgroup.coe_mul, mul_smul, wallCount_smul, ← ofAdd_add, add_comm]

theorem wallHom_apply (γ : congGroup N) :
    wallHom z₀ γ = Multiplicative.ofAdd (wallCount N z₀ ((γ : SL(2, ℝ)) • z₀)) := rfl

/-- The increments of `θ` over a compact set are bounded. -/
theorem exists_abs_wallCount_sub_le {K : Set ℍ} (hK : IsCompact K) :
    ∃ L : ℤ, ∀ z ∈ K, ∀ z' ∈ K, |wallCount N z₀ z - wallCount N z₀ z'| ≤ L := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_separating N hK
  refine ⟨s.card, fun z hz z' hz' => ?_⟩
  rw [wallCount_sub, finsum_eq_sum_of_separating (s := s) fun w h => hs w z hz z' hz' h]
  calc |∑ w ∈ s, (posInd (wallSide w z) - posInd (wallSide w z'))|
      ≤ ∑ w ∈ s, |posInd (wallSide w z) - posInd (wallSide w z')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w ∈ s, (1 : ℤ) := Finset.sum_le_sum fun w _ => abs_posInd_sub_le _ _
    _ = s.card := by simp

/-- **Bounded increments.**  `|θ(z) − θ(z')|` is bounded on `d(z, z') ≤ R`: translate `z` into a
compact set by `Γ(N)`, which preserves increments. -/
theorem exists_abs_wallCount_sub_le_of_dist (hN : 3 ≤ N) (R : ℝ) :
    ∃ L : ℤ, ∀ z z' : ℍ, dist z z' ≤ R → |wallCount N z₀ z - wallCount N z₀ z'| ≤ L := by
  obtain ⟨K, hK, hcov⟩ := (isCocompactFree_congGroup hN).exists_compact
  obtain ⟨L, hL⟩ := exists_abs_wallCount_sub_le z₀ (hK.cthickening (r := R))
  refine ⟨L, fun z z' hd => ?_⟩
  obtain ⟨γ, hγ⟩ := hcov z
  have hmem : (γ : SL(2, ℝ)) • z' ∈ Metric.cthickening R K :=
    Metric.mem_cthickening_of_dist_le _ _ R K hγ (by rw [dist_smul, dist_comm]; exact hd)
  have := hL _ (Metric.self_subset_cthickening K hγ) _ hmem
  rw [wallCount_smul z₀ γ z, wallCount_smul z₀ γ z'] at this
  simpa using this

theorem measurable_posInd_wallSide (w : Fin 4 → ℤ) :
    Measurable fun z : ℍ => (posInd (wallSide w z) : ℝ) := by
  simp only [posInd, Int.cast_ite, Int.cast_one, Int.cast_zero]
  exact Measurable.ite (measurableSet_lt measurable_const
    (continuous_hermForm (quatMat w)).measurable) measurable_const measurable_const

/-- `θ` is measurable: on the ball of radius `k` about `z₀` it is a finite sum. -/
theorem measurable_wallCount : Measurable fun z => (wallCount N z₀ z : ℝ) := by
  classical
  have hS : ∀ k : ℕ, ∃ s : Finset (wallSet N), ∀ z : ℍ, dist z z₀ ≤ k →
      (wallCount N z₀ z : ℝ) = ∑ w ∈ s, ((posInd (wallSide w z) : ℝ) - posInd (wallSide w z₀)) := by
    intro k
    obtain ⟨s, hs⟩ := exists_finset_separating N (isCompact_closedBall z₀ (k : ℝ))
    refine ⟨s, fun z hz => ?_⟩
    rw [wallCount, finsum_eq_sum_of_separating (s := s) fun w h =>
      hs w z (Metric.mem_closedBall.mpr hz) z₀ (Metric.mem_closedBall_self (Nat.cast_nonneg k)) h]
    simp only [Int.cast_sum, Int.cast_sub]
  choose s hs using hS
  refine measurable_of_tendsto_metrizable (f := fun k z =>
    ∑ w ∈ s k, ((posInd (wallSide w z) : ℝ) - posInd (wallSide w z₀))) (fun k => ?_) ?_
  · exact Finset.measurable_sum _ fun w _ => (measurable_posInd_wallSide w).sub measurable_const
  · rw [tendsto_pi_nhds]
    intro z
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈dist z z₀⌉₊) fun k hk => ?_
    exact (hs k z ((Nat.le_ceil _).trans (by exact_mod_cast hk))).symm

end wallCount

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
