import Mathlib
import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant

/-!
# Leading-order CCM parity: no symmetric eigenvalue pair at large apertures

For nodes `p : ι → ℂ` with `Re(p_i + p_l) > 0`, weights `γ_i ≠ 0` and distinct real frequencies
`ω_i`, consider the finite-rank operator on functions on `(0, ∞)`

`T_a u(s) = Σ_i γ_i e^{iω_i a} e^{−p_i s} ∫_0^∞ e^{−p_i t} u(t) dt`.

Its nonzero spectrum is that of the matrix `A(a) = diag(c(a)) · G`, `c_i(a) = γ_i e^{iω_i a}`,
`G = [(p_i + p_l)⁻¹]` the Cauchy Gram matrix of the exponentials
(`exists_mulVec_eigen_of_parityOperator_eigen`).

**Theorem** (`exists_large_aperture_no_symmetric_operator_pair`). For injective `p` and `ω`, at
arbitrarily large real apertures `a` the operator `T_a` has no pair of eigenvalues `μ, −μ` with
`μ ≠ 0`.

**Proof.**
* A pair `Av = μv`, `Aw = −μw` makes the second additive compound `A^{[2]}`,
  `A^{[2]}(v ∧ w) = Av ∧ w + v ∧ Aw`, singular, since `v ∧ w ≠ 0` and `A^{[2]}(v ∧ w) = 0`
  (`det_wedgeCompound_eq_zero`).
* The determinant `D(a)` of `A(a)^{[2]}` is entire in `a`. At `a = iy` the weights have the distinct
  scales `e^{−ω_i y}`. Divide each row `(i, j)` of the compound by its dominant weight. As `y → ∞` the
  matrix tends to a block-triangular matrix whose diagonal blocks are principal minors of `G`. Those
  are nonzero Cauchy determinants (`det_wedgeLead_ne_zero`), so `D(iy) ≠ 0` for large `y`.
* By the identity theorem `D` cannot vanish on a real half-line.

**CCM reading** (`ccm_exists_large_aperture_no_symmetric_pair`). For top quartets
`σ_j = t_j + iδ` (`t_j > 0` distinct, `δ > 0`, multiplicities `M_j ≠ 0`), the leading-order parity
operator `T(θ) = Re Σ_j M_j e^{iθ_j} ψ_j ⊗ ψ_j`, `ψ_j(s) = e^{−(δ − it_j)s}`, on the aperture line
`θ_j = −2t_j a` is the case `ι = Fin m ⊕ Fin m`. Hence `λ_max(T) + λ_min(T) ≠ 0` at arbitrarily
large apertures, for every finite top layer and all multiplicities. With the antisymmetry
`T(θ + π𝟙) = −T(θ)` this is the input from which the odd sector wins whenever `π𝟙` lies in the
orbit closure of the aperture line.
-/

open Matrix Complex Filter Topology MeasureTheory Set

namespace RHTower.CCMParityCauchy

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The second additive compound -/

/-- Ordered pairs `(i, j)` with `κ j < κ i`. For injective `κ` this is one orientation of every
two-element subset of `ι`, i.e. an index set for the basis `e_i ∧ e_j` of the second exterior
power. -/
abbrev OrientedPair (κ : ι → ℝ) := {x : ι × ι // κ x.2 < κ x.1}

/-- The coefficient of `e_{x₁} ∧ e_{x₂}` in `A e_{y₁} ∧ e_{y₂} + e_{y₁} ∧ A e_{y₂}`. -/
def wedgeEntry (A : Matrix ι ι ℂ) (x y : ι × ι) : ℂ :=
  (if y.2 = x.2 then A x.1 y.1 else 0) - (if y.2 = x.1 then A x.2 y.1 else 0) +
    (if y.1 = x.1 then A x.2 y.2 else 0) - (if y.1 = x.2 then A x.1 y.2 else 0)

/-- The second additive compound `A^{[2]}` in the basis of oriented pairs. -/
def wedgeCompound (κ : ι → ℝ) (A : Matrix ι ι ℂ) :
    Matrix (OrientedPair κ) (OrientedPair κ) ℂ :=
  Matrix.of fun x y => wedgeEntry A x.1 y.1

/-- The coordinates `v_r w_s − v_s w_r` of `v ∧ w`. -/
def wedgeVec (v w : ι → ℂ) (y : ι × ι) : ℂ := v y.1 * w y.2 - v y.2 * w y.1

omit [Fintype ι] in
theorem wedgeEntry_swap (A : Matrix ι ι ℂ) (x : ι × ι) (r s : ι) :
    wedgeEntry A x (s, r) = -wedgeEntry A x (r, s) := by
  simp only [wedgeEntry]
  ring

omit [DecidableEq ι] in
/-- Summing a symmetric function with zero diagonal over oriented pairs gives half the full sum. -/
theorem two_mul_sum_orientedPair {κ : ι → ℝ} (hκ : Function.Injective κ) (g : ι × ι → ℂ)
    (hsymm : ∀ r s, g (s, r) = g (r, s)) (hdiag : ∀ r, g (r, r) = 0) :
    2 * ∑ y : OrientedPair κ, g y.1 = ∑ y : ι × ι, g y := by
  classical
  have hsplit : ∀ y : ι × ι,
      g y = (if κ y.2 < κ y.1 then g y else 0) + (if κ y.1 < κ y.2 then g y else 0) := by
    intro y
    rcases lt_trichotomy (κ y.2) (κ y.1) with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · have hy : y.2 = y.1 := hκ h
      have hg : g y = 0 := by
        obtain ⟨a, b⟩ := y
        simp only at hy
        subst hy
        exact hdiag _
      rw [hg, if_neg (by rw [h]; exact lt_irrefl _), if_neg (by rw [h]; exact lt_irrefl _),
        add_zero]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
  rw [Finset.sum_congr rfl fun y _ => hsplit y, Finset.sum_add_distrib]
  have h1 : ∑ y : ι × ι, (if κ y.2 < κ y.1 then g y else 0) = ∑ y : OrientedPair κ, g y.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) g
  have h2 : ∑ y : ι × ι, (if κ y.1 < κ y.2 then g y else 0) =
      ∑ y : ι × ι, (if κ y.2 < κ y.1 then g y else 0) :=
    Fintype.sum_equiv (Equiv.prodComm ι ι) _ _ fun y => by
      obtain ⟨a, b⟩ := y
      simp [hsymm]
  rw [h2, h1]
  ring

theorem sum_ite_snd_mul (a : ι → ℂ) (j : ι) (f : ι × ι → ℂ) :
    ∑ y : ι × ι, (if y.2 = j then a y.1 else 0) * f y = ∑ r, a r * f (r, j) := by
  rw [Fintype.sum_prod_type]
  simp [ite_mul]

theorem sum_ite_fst_mul (a : ι → ℂ) (i : ι) (f : ι × ι → ℂ) :
    ∑ y : ι × ι, (if y.1 = i then a y.2 else 0) * f y = ∑ s, a s * f (i, s) := by
  rw [Fintype.sum_prod_type_right]
  simp [ite_mul]

omit [DecidableEq ι] in
theorem sum_mul_wedgeVec_snd (A : Matrix ι ι ℂ) (v w : ι → ℂ) (i j : ι) :
    ∑ r, A i r * wedgeVec v w (r, j) = (A *ᵥ v) i * w j - v j * (A *ᵥ w) i := by
  simp only [wedgeVec, mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun r _ => by ring

omit [DecidableEq ι] in
theorem sum_mul_wedgeVec_fst (A : Matrix ι ι ℂ) (v w : ι → ℂ) (i j : ι) :
    ∑ s, A j s * wedgeVec v w (i, s) = v i * (A *ᵥ w) j - (A *ᵥ v) j * w i := by
  simp only [wedgeVec, mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun r _ => by ring

/-- `A^{[2]}(v ∧ w) = Av ∧ w + v ∧ Aw`, in coordinates over all ordered pairs. -/
theorem sum_wedgeEntry_mul_wedgeVec (A : Matrix ι ι ℂ) (v w : ι → ℂ) (x : ι × ι) :
    ∑ y : ι × ι, wedgeEntry A x y * wedgeVec v w y =
      2 * ((A *ᵥ v) x.1 * w x.2 - v x.2 * (A *ᵥ w) x.1 +
        (v x.1 * (A *ᵥ w) x.2 - (A *ᵥ v) x.2 * w x.1)) := by
  simp only [wedgeEntry, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_ite_snd_mul (A x.1) x.2, sum_ite_snd_mul (A x.2) x.1, sum_ite_fst_mul (A x.2) x.1,
    sum_ite_fst_mul (A x.1) x.2, sum_mul_wedgeVec_snd, sum_mul_wedgeVec_snd, sum_mul_wedgeVec_fst,
    sum_mul_wedgeVec_fst]
  ring

/-- **A symmetric eigenvalue pair makes the compound singular.** If `Av = μv` and `Aw = −μw` with
`μ ≠ 0` and `v, w ≠ 0`, then `det A^{[2]} = 0`. -/
theorem det_wedgeCompound_eq_zero {κ : ι → ℝ} (hκ : Function.Injective κ) {A : Matrix ι ι ℂ}
    {μ : ℂ} (hμ : μ ≠ 0) {v w : ι → ℂ} (hv : v ≠ 0) (hw : w ≠ 0)
    (hAv : A *ᵥ v = μ • v) (hAw : A *ᵥ w = -μ • w) : (wedgeCompound κ A).det = 0 := by
  classical
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun y => wedgeVec v w y.1, ?_, ?_⟩
  · intro h0
    have hall : ∀ r s, v r * w s = v s * w r := by
      intro r s
      rcases lt_trichotomy (κ s) (κ r) with h | h | h
      · have := congr_fun h0 ⟨(r, s), h⟩
        simp only [wedgeVec, Pi.zero_apply] at this
        exact sub_eq_zero.mp this
      · rw [hκ h]
      · have := congr_fun h0 ⟨(s, r), h⟩
        simp only [wedgeVec, Pi.zero_apply] at this
        exact (sub_eq_zero.mp this).symm
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (funext hcon)
    have hwv : ∀ r, w r = (w k / v k) * v r := by
      intro r
      field_simp
      linear_combination hall k r
    apply hw
    funext r
    have hr := congr_fun hAw r
    have hwfun : w = (w k / v k) • v := funext fun r => by rw [hwv r]; rfl
    rw [hwfun, Matrix.mulVec_smul, hAv] at hr
    simp only [Pi.smul_apply, smul_eq_mul] at hr
    rw [Pi.zero_apply, hwv r]
    have h2 : 2 * μ * ((w k / v k) * v r) = 0 := by linear_combination hr
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hμ)
    · exact h
  · funext x
    have hsum := two_mul_sum_orientedPair hκ (fun y => wedgeEntry A x.1 y * wedgeVec v w y)
      (fun r s => by rw [wedgeEntry_swap]; simp only [wedgeVec]; ring)
      (fun r => by simp only [wedgeVec]; ring)
    rw [sum_wedgeEntry_mul_wedgeVec, hAv, hAw] at hsum
    simp only [Pi.smul_apply, smul_eq_mul] at hsum
    have h2 : 2 * ∑ y : OrientedPair κ, wedgeEntry A x.1 y.1 * wedgeVec v w y.1 = 0 := by
      rw [hsum]; ring
    have : ∑ y : OrientedPair κ, wedgeEntry A x.1 y.1 * wedgeVec v w y.1 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h two_ne_zero
      · exact h
    simpa [mulVec, dotProduct, wedgeCompound] using this

/-! ## Cauchy minors and the leading compound -/

/-- The Cauchy Gram matrix `[(p_i + p_l)⁻¹]` of the exponentials `e^{−p_i s}` on `(0, ∞)`. -/
def cauchyGram (p : ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun i l => (p i + p l)⁻¹

omit [Fintype ι] [DecidableEq ι] in
/-- **Every principal minor of a Cauchy Gram matrix with distinct nodes is nonzero.** -/
theorem det_cauchyGram_submatrix_ne_zero {S : Type*} [Fintype S] [DecidableEq S] {p : ι → ℂ}
    (hp : Function.Injective p) (hsum : ∀ i l, p i + p l ≠ 0) {e : S → ι}
    (he : Function.Injective e) : ((cauchyGram p).submatrix e e).det ≠ 0 := by
  classical
  set f := Fintype.equivFin S
  set x : Fin (Fintype.card S) → ℂ := fun a => p (e (f.symm a)) with hx
  have hreindex : Matrix.reindex f f ((cauchyGram p).submatrix e e) =
      GaloisForLFunctions.HTGeometry.cauchyMatrix x x := by
    ext a b
    simp [cauchyGram, hx, Matrix.reindex_apply]
  rw [← Matrix.det_reindex_self f, hreindex]
  have hdet := GaloisForLFunctions.HTGeometry.det_cauchyMatrix x x fun i j => hsum _ _
  intro h0
  rw [h0, zero_mul] at hdet
  have hne : ∏ i, ∏ j ∈ Finset.Ioi i, ((x i - x j) * (x i - x j)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    have hxij : x i ≠ x j := fun h => hij (f.symm.injective (he (hp h)))
    exact mul_ne_zero (sub_ne_zero.mpr hxij) (sub_ne_zero.mpr hxij)
  exact hne hdet.symm

/-- The part of row `(i, j)` of `(diag(c)·G)^{[2]}` carried by the weight `c_i`. -/
def wedgeLead (κ : ι → ℝ) (G : Matrix ι ι ℂ) : Matrix (OrientedPair κ) (OrientedPair κ) ℂ :=
  Matrix.of fun x y =>
    (if y.1.2 = x.1.2 then G x.1.1 y.1.1 else 0) - (if y.1.1 = x.1.2 then G x.1.1 y.1.2 else 0)

/-- The part of row `(i, j)` of `(diag(c)·G)^{[2]}` carried by the weight `c_j`. -/
def wedgeTrail (κ : ι → ℝ) (G : Matrix ι ι ℂ) : Matrix (OrientedPair κ) (OrientedPair κ) ℂ :=
  Matrix.of fun x y =>
    (if y.1.1 = x.1.1 then G x.1.2 y.1.2 else 0) - (if y.1.2 = x.1.1 then G x.1.2 y.1.1 else 0)

theorem wedgeCompound_diagonal_mul (κ : ι → ℝ) (c : ι → ℂ) (G : Matrix ι ι ℂ)
    (x y : OrientedPair κ) :
    wedgeCompound κ (diagonal c * G) x y =
      c x.1.1 * wedgeLead κ G x y + c x.1.2 * wedgeTrail κ G x y := by
  simp only [wedgeCompound, wedgeEntry, wedgeLead, wedgeTrail, Matrix.of_apply,
    Matrix.diagonal_mul]
  split_ifs <;> ring

omit [Fintype ι] in
/-- The leading compound is block lower triangular, blocks indexed by the smaller endpoint. -/
theorem wedgeLead_blockTriangular {κ : ι → ℝ} (G : Matrix ι ι ℂ) :
    (wedgeLead κ G).BlockTriangular fun x : OrientedPair κ => OrderDual.toDual (κ x.1.2) := by
  intro x y hxy
  have h : κ x.1.2 < κ y.1.2 := OrderDual.toDual_lt_toDual.mp hxy
  have h1 : ¬ y.1.2 = x.1.2 := fun he => by rw [he] at h; exact lt_irrefl _ h
  have h2 : ¬ y.1.1 = x.1.2 := fun he => by
    have hy := y.2
    rw [he] at hy
    exact lt_irrefl _ (hy.trans h)
  simp only [wedgeLead, Matrix.of_apply, if_neg h1, if_neg h2, sub_zero]

/-- **The leading compound of a Cauchy Gram matrix is nonsingular.** Its diagonal blocks are the
principal minors of `G` on `{i : κ j < κ i}`. -/
theorem det_wedgeLead_ne_zero {κ : ι → ℝ} (hκ : Function.Injective κ) {p : ι → ℂ}
    (hp : Function.Injective p) (hsum : ∀ i l, p i + p l ≠ 0) :
    (wedgeLead κ (cauchyGram p)).det ≠ 0 := by
  classical
  rw [(wedgeLead_blockTriangular (κ := κ) (cauchyGram p)).det]
  refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
  obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hk
  set j := x₀.1.2 with hj
  let E : {i : ι // κ j < κ i} ≃
      {x : OrientedPair κ // OrderDual.toDual (κ x.1.2) = OrderDual.toDual (κ j)} :=
    { toFun := fun i => ⟨⟨(i.1, j), i.2⟩, rfl⟩
      invFun := fun x => ⟨x.1.1.1, by
        have h := hκ (OrderDual.toDual.injective x.2)
        have hx : κ x.1.1.2 < κ x.1.1.1 := x.1.2
        rwa [h] at hx⟩
      left_inv := fun i => rfl
      right_inv := fun x => by
        have h := hκ (OrderDual.toDual.injective x.2)
        obtain ⟨⟨⟨a, b⟩, hab⟩, hx⟩ := x
        simp only at h
        subst h
        rfl }
  have hblock : (wedgeLead κ (cauchyGram p)).toSquareBlock
      (fun x : OrientedPair κ => OrderDual.toDual (κ x.1.2)) (OrderDual.toDual (κ j)) =
      Matrix.reindex E E ((cauchyGram p).submatrix (fun i : {i : ι // κ j < κ i} => i.1)
        fun i => i.1) := by
    ext x y
    have hx2 : x.1.1.2 = j := hκ (OrderDual.toDual.injective x.2)
    have hy2 : y.1.1.2 = j := hκ (OrderDual.toDual.injective y.2)
    have hy1 : ¬ y.1.1.1 = x.1.1.2 := by
      intro he
      have hlt : κ y.1.1.2 < κ y.1.1.1 := y.1.2
      rw [he, hx2] at hlt
      linarith [congrArg κ hy2]
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, wedgeLead, Matrix.reindex_apply,
      Matrix.submatrix_apply, if_pos (hy2.trans hx2.symm), if_neg hy1, sub_zero]
    rfl
  rw [hblock, Matrix.det_reindex_self]
  exact det_cauchyGram_submatrix_ne_zero hp hsum Subtype.val_injective

/-! ## The aperture family -/

/-- Aperture weights `c_i(a) = γ_i e^{iω_i a}`. -/
def apertureWeight (γ : ι → ℂ) (ω : ι → ℝ) (a : ℂ) (i : ι) : ℂ :=
  γ i * Complex.exp (I * ω i * a)

/-- The leading-order parity matrix `diag(c(a)) · [(p_i + p_l)⁻¹]`. -/
def parityMatrix (p γ : ι → ℂ) (ω : ι → ℝ) (a : ℂ) : Matrix ι ι ℂ :=
  diagonal (apertureWeight γ ω a) * cauchyGram p

/-- The pairing determinant `det A(a)^{[2]}`, pairs `(i, j)` oriented by `ω i < ω j`. -/
def pairingDet (p γ : ι → ℂ) (ω : ι → ℝ) (a : ℂ) : ℂ :=
  (wedgeCompound (fun i => -ω i) (parityMatrix p γ ω a)).det

theorem pairingDet_eq (p γ : ι → ℂ) (ω : ι → ℝ) (a : ℂ) :
    pairingDet p γ ω a = (Matrix.of fun x y : OrientedPair (fun i => -ω i) =>
      apertureWeight γ ω a x.1.1 * wedgeLead _ (cauchyGram p) x y +
        apertureWeight γ ω a x.1.2 * wedgeTrail _ (cauchyGram p) x y).det := by
  unfold pairingDet parityMatrix
  congr 1
  ext x y
  exact wedgeCompound_diagonal_mul _ _ _ x y

theorem differentiable_pairingDet (p γ : ι → ℂ) (ω : ι → ℝ) :
    Differentiable ℂ (pairingDet p γ ω) := by
  rw [show pairingDet p γ ω = _ from funext (pairingDet_eq p γ ω)]
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Differentiable.fun_sum fun σ _ => ?_
  refine (differentiable_const _).mul (Differentiable.fun_finsetProd fun z _ => ?_)
  simp only [Matrix.of_apply, apertureWeight]
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
theorem apertureWeight_I_mul (γ : ι → ℂ) (ω : ι → ℝ) (y : ℝ) (i : ι) :
    apertureWeight γ ω (I * y) i = γ i * ((Real.exp (-(ω i * y)) : ℝ) : ℂ) := by
  rw [apertureWeight, Complex.ofReal_exp]
  congr 2
  push_cast
  linear_combination ((ω i : ℂ) * y) * I_sq

omit [Fintype ι] [DecidableEq ι] in
/-- At imaginary aperture the weight ratio along an oriented pair decays exponentially. -/
theorem tendsto_apertureWeight_ratio {γ : ι → ℂ} (hγ : ∀ i, γ i ≠ 0) {ω : ι → ℝ} {i j : ι}
    (hij : ω i < ω j) :
    Tendsto (fun y : ℝ => apertureWeight γ ω (I * y) j / apertureWeight γ ω (I * y) i) atTop
      (𝓝 0) := by
  have hreal : Tendsto (fun y : ℝ => Real.exp ((ω i - ω j) * y)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hij))
  have hc : Tendsto (fun y : ℝ => γ j / γ i * ((Real.exp ((ω i - ω j) * y) : ℝ) : ℂ)) atTop
      (𝓝 (γ j / γ i * ((0 : ℝ) : ℂ))) :=
    ((Complex.continuous_ofReal.tendsto 0).comp hreal).const_mul _
  rw [Complex.ofReal_zero, mul_zero] at hc
  refine hc.congr fun y => ?_
  rw [apertureWeight_I_mul, apertureWeight_I_mul]
  have he : Real.exp ((ω i - ω j) * y) = Real.exp (-(ω j * y)) / Real.exp (-(ω i * y)) := by
    rw [← Real.exp_sub]
    ring_nf
  have h1 : ((Real.exp (-(ω i * y)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [he, Complex.ofReal_div]
  field_simp [hγ i]

/-- **The pairing determinant is nonzero far up the imaginary aperture axis.** -/
theorem exists_pairingDet_I_mul_ne_zero {p γ : ι → ℂ} {ω : ι → ℝ} (hp : Function.Injective p)
    (hsum : ∀ i l, p i + p l ≠ 0) (hγ : ∀ i, γ i ≠ 0) (hω : Function.Injective ω) :
    ∃ y : ℝ, pairingDet p γ ω (I * y) ≠ 0 := by
  classical
  have hκ : Function.Injective fun i => -ω i := fun a b h => hω (neg_injective h)
  have hcw : ∀ (y : ℝ) i, apertureWeight γ ω (I * y) i ≠ 0 := fun y i =>
    mul_ne_zero (hγ i) (Complex.exp_ne_zero _)
  set L := wedgeLead (fun i => -ω i) (cauchyGram p) with hL
  set Tr := wedgeTrail (fun i => -ω i) (cauchyGram p) with hTr
  set ρ : ℝ → OrientedPair (fun i => -ω i) → ℂ := fun y x =>
    apertureWeight γ ω (I * y) x.1.2 / apertureWeight γ ω (I * y) x.1.1 with hρdef
  have hfac : ∀ y : ℝ, pairingDet p γ ω (I * y) =
      (∏ x : OrientedPair (fun i => -ω i), apertureWeight γ ω (I * y) x.1.1) *
        (Matrix.of fun x z => L x z + ρ y x * Tr x z).det := by
    intro y
    rw [pairingDet_eq, ← Matrix.det_mul_column]
    congr 1
    ext x z
    simp only [Matrix.of_apply, hρdef]
    field_simp [hcw y x.1.1]
    rfl
  have hρ : ∀ x : OrientedPair (fun i => -ω i), Tendsto (fun y => ρ y x) atTop (𝓝 0) := by
    intro x
    have hx : -ω x.1.2 < -ω x.1.1 := x.2
    exact tendsto_apertureWeight_ratio hγ (by linarith)
  have hN : Tendsto (fun y => Matrix.of fun x z => L x z + ρ y x * Tr x z) atTop (𝓝 L) := by
    refine tendsto_pi_nhds.mpr fun x => tendsto_pi_nhds.mpr fun z => ?_
    have := (tendsto_const_nhds (x := L x z)).add ((hρ x).mul_const (Tr x z))
    simpa using this
  have hdet : Tendsto (fun y => (Matrix.of fun x z => L x z + ρ y x * Tr x z).det) atTop
      (𝓝 L.det) := ((continuous_id.matrix_det).tendsto L).comp hN
  obtain ⟨y, hy⟩ := (hdet.eventually_ne (det_wedgeLead_ne_zero hκ hp hsum)).exists
  exact ⟨y, by rw [hfac]; exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun x _ => hcw y _) hy⟩

omit [Fintype ι] [DecidableEq ι] in
/-- An entire function that is not identically zero does not vanish on any real half-line. -/
theorem exists_real_ge_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ} (hz : f z ≠ 0)
    (N : ℝ) : ∃ a : ℝ, N ≤ a ∧ f a ≠ 0 := by
  by_contra h
  push Not at h
  have han : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  have ht : Tendsto (fun k : ℕ => (((N + 1 + 1 / ((k : ℝ) + 1)) : ℝ) : ℂ)) atTop
      (𝓝[≠] ((N + 1 : ℝ) : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Tendsto (fun k : ℕ => N + 1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (N + 1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h0
      exact (Complex.continuous_ofReal.tendsto _).comp h0
    · refine Eventually.of_forall fun k => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      have h1 := Complex.ofReal_injective heq
      have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] ((N + 1 : ℝ) : ℂ), f w = 0 :=
    ht.frequently (Frequently.of_forall fun k => h _ (by
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith))
  exact hz (han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ _) hfreq (Set.mem_univ z))

/-- **No symmetric eigenvalue pair at large real apertures (matrix form).** -/
theorem exists_large_aperture_no_symmetric_pair {p γ : ι → ℂ} {ω : ι → ℝ}
    (hp : Function.Injective p) (hsum : ∀ i l, p i + p l ≠ 0) (hγ : ∀ i, γ i ≠ 0)
    (hω : Function.Injective ω) (N : ℝ) :
    ∃ a : ℝ, N ≤ a ∧ ∀ μ : ℂ, μ ≠ 0 → ∀ v w : ι → ℂ, v ≠ 0 → w ≠ 0 →
      parityMatrix p γ ω a *ᵥ v = μ • v → parityMatrix p γ ω a *ᵥ w ≠ -μ • w := by
  obtain ⟨y, hy⟩ := exists_pairingDet_I_mul_ne_zero hp hsum hγ hω
  obtain ⟨a, ha, hne⟩ := exists_real_ge_ne_zero (differentiable_pairingDet p γ ω) hy N
  exact ⟨a, ha, fun μ hμ v w hv hw hAv hAw =>
    hne (det_wedgeCompound_eq_zero (fun a b h => hω (neg_injective h)) hμ hv hw hAv hAw)⟩

/-! ## The operator on `(0, ∞)` -/

/-- The leading-order operator `T u(s) = Σ_i c_i e^{−p_i s} ∫_0^∞ e^{−p_i t} u(t) dt`. -/
def parityOperator (p c : ι → ℂ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∑ i, c i * Complex.exp (-p i * s) * ∫ t in Ioi (0 : ℝ), Complex.exp (-p i * t) * u t

omit [Fintype ι] [DecidableEq ι] in
theorem integral_exp_neg_mul_Ioi {q : ℂ} (hq : 0 < q.re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-q * t) = q⁻¹ := by
  have h := integral_exp_mul_complex_Ioi (a := -q) (by simpa using hq) 0
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq, one_div] at h
  exact h

/-- **Eigenfunctions become eigenvectors of `diag(c)·G`.** If `T u = μu` on `(0, ∞)` with `μ ≠ 0`
and `u ≢ 0` there, the moments `y_i = ∫ e^{−p_i t}u` give `x = c ⊙ y ≠ 0` with
`diag(c)·G x = μx`. -/
theorem exists_mulVec_eigen_of_parityOperator_eigen {p c : ι → ℂ}
    (hp : ∀ i l, 0 < (p i + p l).re) {μ : ℂ} (hμ : μ ≠ 0) {u : ℝ → ℂ}
    (hu : ∃ s ∈ Ioi (0 : ℝ), u s ≠ 0)
    (heig : ∀ s ∈ Ioi (0 : ℝ), parityOperator p c u s = μ * u s) :
    ∃ x : ι → ℂ, x ≠ 0 ∧ (diagonal c * cauchyGram p) *ᵥ x = μ • x := by
  classical
  set y : ι → ℂ := fun i => ∫ t in Ioi (0 : ℝ), Complex.exp (-p i * t) * u t with hy
  have hu_eq : ∀ s ∈ Ioi (0 : ℝ), u s = μ⁻¹ * ∑ i, c i * y i * Complex.exp (-p i * s) := by
    intro s hs
    have h := heig s hs
    simp only [parityOperator] at h
    rw [eq_inv_mul_iff_mul_eq₀ hμ, ← h]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hyl : ∀ l, μ * y l = ∑ i, (p l + p i)⁻¹ * (c i * y i) := by
    intro l
    have h1 : y l = ∫ t in Ioi (0 : ℝ),
        ∑ i, μ⁻¹ * (c i * y i) * Complex.exp (-(p l + p i) * t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [hu_eq t ht]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show -(p l + p i) * (t : ℂ) = -p l * t + -p i * t by ring, Complex.exp_add]
      ring
    rw [h1, integral_finsetSum _ fun i _ =>
      (integrableOn_exp_mul_complex_Ioi (by
        have := hp l i
        simp only [Complex.add_re, Complex.neg_re] at this ⊢
        linarith) 0).const_mul _]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_exp_neg_mul_Ioi (hp l i)]
    field_simp
  refine ⟨fun i => c i * y i, ?_, ?_⟩
  · intro hx0
    obtain ⟨s, hs, hus⟩ := hu
    apply hus
    rw [hu_eq s hs]
    have : ∀ i, c i * y i = 0 := fun i => congr_fun hx0 i
    simp [this]
  · funext l
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hG : (cauchyGram p *ᵥ fun i => c i * y i) l = μ * y l := by
      rw [hyl l]
      simp [mulVec, dotProduct, cauchyGram]
    rw [hG, Pi.smul_apply, smul_eq_mul]
    ring

/-- **No symmetric eigenvalue pair at large real apertures (operator form).** -/
theorem exists_large_aperture_no_symmetric_operator_pair {p γ : ι → ℂ} {ω : ι → ℝ}
    (hp : Function.Injective p) (hpos : ∀ i l, 0 < (p i + p l).re) (hγ : ∀ i, γ i ≠ 0)
    (hω : Function.Injective ω) (N : ℝ) :
    ∃ a : ℝ, N ≤ a ∧ ∀ μ : ℂ, μ ≠ 0 → ∀ u w : ℝ → ℂ,
      (∃ s ∈ Ioi (0 : ℝ), u s ≠ 0) → (∃ s ∈ Ioi (0 : ℝ), w s ≠ 0) →
      (∀ s ∈ Ioi (0 : ℝ), parityOperator p (apertureWeight γ ω a) u s = μ * u s) →
      ¬ ∀ s ∈ Ioi (0 : ℝ), parityOperator p (apertureWeight γ ω a) w s = -μ * w s := by
  have hsum : ∀ i l, p i + p l ≠ 0 := fun i l h => by
    have := hpos i l
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  obtain ⟨a, ha, hno⟩ := exists_large_aperture_no_symmetric_pair hp hsum hγ hω N
  refine ⟨a, ha, fun μ hμ u w hu hw hTu hTw => ?_⟩
  obtain ⟨v, hv, hAv⟩ := exists_mulVec_eigen_of_parityOperator_eigen hpos hμ hu hTu
  obtain ⟨v', hv', hAv'⟩ :=
    exists_mulVec_eigen_of_parityOperator_eigen hpos (neg_ne_zero.mpr hμ) hw hTw
  exact hno μ hμ v v' hv hv' hAv hAv'

/-! ## The CCM top layer -/

/-- The leading-order CCM parity operator of a top layer `σ_j = t_j + iδ` with multiplicities
`M_j` at phases `θ_j`. For real `u` it is `Re Σ_j M_j e^{iθ_j} ψ_j(s) ∫_0^∞ ψ_j u`,
`ψ_j(s) = e^{−(δ − it_j)s}`. -/
def ccmTopOperator {m : ℕ} (δ : ℝ) (t M θ : Fin m → ℝ) (u : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∑ j, ((M j / 2 : ℝ) : ℂ) *
    (Complex.exp (I * θ j) * Complex.exp (-(δ - I * t j) * s) *
        (∫ τ in Ioi (0 : ℝ), Complex.exp (-(δ - I * t j) * τ) * u τ) +
      Complex.exp (-(I * θ j)) * Complex.exp (-(δ + I * t j) * s) *
        (∫ τ in Ioi (0 : ℝ), Complex.exp (-(δ + I * t j) * τ) * u τ))

/-- The nodes `δ ∓ it_j` of the top-layer exponentials `ψ_j = e^{−(δ − it_j)s}` and their
conjugates. -/
def ccmNodes {m : ℕ} (δ : ℝ) (t : Fin m → ℝ) : Fin m ⊕ Fin m → ℂ :=
  Sum.elim (fun j => (δ : ℂ) - I * t j) (fun j => (δ : ℂ) + I * t j)

/-- The amplitudes `M_j/2` of the paired weights. -/
def ccmAmp {m : ℕ} (M : Fin m → ℝ) : Fin m ⊕ Fin m → ℂ :=
  Sum.elim (fun j => ((M j / 2 : ℝ) : ℂ)) (fun j => ((M j / 2 : ℝ) : ℂ))

/-- The aperture frequencies `∓2t_j`, so that the weights are `(M_j/2)e^{±iθ_j}`, `θ_j = −2t_j a`. -/
def ccmFreq {m : ℕ} (t : Fin m → ℝ) : Fin m ⊕ Fin m → ℝ :=
  Sum.elim (fun j => -2 * t j) (fun j => 2 * t j)

theorem ccmNodes_injective {m : ℕ} {δ : ℝ} {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) : Function.Injective (ccmNodes δ t) := by
  intro x y hxy
  rcases x with j | j <;> rcases y with k | k <;>
    simp only [ccmNodes, Sum.elim_inl, Sum.elim_inr, Complex.ext_iff, Complex.sub_re,
      Complex.add_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at hxy
  · exact congrArg Sum.inl (ht (by linarith [hxy.2]))
  · linarith [hxy.2, htpos j, htpos k]
  · linarith [hxy.2, htpos j, htpos k]
  · exact congrArg Sum.inr (ht (by linarith [hxy.2]))

theorem ccmNodes_re_add_pos {m : ℕ} {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (i l : Fin m ⊕ Fin m) :
    0 < (ccmNodes δ t i + ccmNodes δ t l).re := by
  rcases i with j | j <;> rcases l with k | k <;> simp [ccmNodes] <;> linarith

theorem ccmAmp_ne_zero {m : ℕ} {M : Fin m → ℝ} (hM : ∀ j, M j ≠ 0) (i : Fin m ⊕ Fin m) :
    ccmAmp M i ≠ 0 := by
  rcases i with j | j <;> simp [ccmAmp, hM j]

theorem ccmFreq_injective {m : ℕ} {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) : Function.Injective (ccmFreq t) := by
  intro x y hxy
  rcases x with j | j <;> rcases y with k | k <;>
    simp only [ccmFreq, Sum.elim_inl, Sum.elim_inr] at hxy
  · exact congrArg Sum.inl (ht (by linarith))
  · linarith [htpos j, htpos k]
  · linarith [htpos j, htpos k]
  · exact congrArg Sum.inr (ht (by linarith))

/-- The CCM top operator is the general parity operator for the CCM data. -/
theorem ccmTopOperator_eq_parityOperator {m : ℕ} (δ : ℝ) (t M : Fin m → ℝ) (a : ℝ)
    (u : ℝ → ℂ) (s : ℝ) :
    ccmTopOperator δ t M (fun j => -2 * t j * a) u s =
      parityOperator (ccmNodes δ t) (apertureWeight (ccmAmp M) (ccmFreq t) a) u s := by
  simp only [ccmTopOperator, parityOperator, Fintype.sum_sum_type, apertureWeight, ccmNodes,
    ccmAmp, ccmFreq, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : I * ((-2 * t j * a : ℝ) : ℂ) = I * ((-2 * t j : ℝ) : ℂ) * a := by push_cast; ring
  have e2 : -(I * ((-2 * t j : ℝ) : ℂ) * a) = I * ((2 * t j : ℝ) : ℂ) * a := by
    push_cast; ring
  rw [e1, e2]
  ring

/-- **CCM parity at leading order never balances on the aperture line (matrix form).** -/
theorem ccm_exists_large_aperture_no_symmetric_matrix_pair {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {t M : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hM : ∀ j, M j ≠ 0)
    (N : ℝ) :
    ∃ a : ℝ, N ≤ a ∧ ∀ μ : ℂ, μ ≠ 0 → ∀ v w : Fin m ⊕ Fin m → ℂ, v ≠ 0 → w ≠ 0 →
      parityMatrix (ccmNodes δ t) (ccmAmp M) (ccmFreq t) a *ᵥ v = μ • v →
      parityMatrix (ccmNodes δ t) (ccmAmp M) (ccmFreq t) a *ᵥ w ≠ -μ • w := by
  have hsum : ∀ i l, ccmNodes δ t i + ccmNodes δ t l ≠ 0 := by
    intro i l h
    have := ccmNodes_re_add_pos hδ t i l
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  exact exists_large_aperture_no_symmetric_pair (ccmNodes_injective ht htpos) hsum
    (ccmAmp_ne_zero hM) (ccmFreq_injective ht htpos) N

/-- **CCM parity at leading order never balances on the aperture line.** For a top layer with
distinct positive ordinates `t_j`, common real part offset `δ > 0` and nonzero multiplicities, at
arbitrarily large apertures `a` the operator at phases `θ_j = −2t_j a` has no pair of eigenvalues
`μ, −μ` with `μ ≠ 0`. -/
theorem ccm_exists_large_aperture_no_symmetric_pair {m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {t M : Fin m → ℝ} (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hM : ∀ j, M j ≠ 0)
    (N : ℝ) :
    ∃ a : ℝ, N ≤ a ∧ ∀ μ : ℂ, μ ≠ 0 → ∀ u w : ℝ → ℂ,
      (∃ s ∈ Ioi (0 : ℝ), u s ≠ 0) → (∃ s ∈ Ioi (0 : ℝ), w s ≠ 0) →
      (∀ s ∈ Ioi (0 : ℝ), ccmTopOperator δ t M (fun j => -2 * t j * a) u s = μ * u s) →
      ¬ ∀ s ∈ Ioi (0 : ℝ), ccmTopOperator δ t M (fun j => -2 * t j * a) w s = -μ * w s := by
  obtain ⟨a, ha, hno⟩ := exists_large_aperture_no_symmetric_operator_pair
    (ccmNodes_injective ht htpos) (ccmNodes_re_add_pos hδ t) (ccmAmp_ne_zero hM)
    (ccmFreq_injective ht htpos) N
  refine ⟨a, ha, fun μ hμ u w hu hw hTu hTw => hno μ hμ u w hu hw (fun s hs => ?_) ?_⟩
  · rw [← ccmTopOperator_eq_parityOperator]; exact hTu s hs
  · intro s hs; rw [← ccmTopOperator_eq_parityOperator]; exact hTw s hs

end

end RHTower.CCMParityCauchy
