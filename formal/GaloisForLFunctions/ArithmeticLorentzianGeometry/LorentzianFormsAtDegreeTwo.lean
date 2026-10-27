import Mathlib

/-!
# Lorentzian forms at degree two

A real symmetric form is **hyperbolic** when it has at most one positive square and **Lorentzian**
when, in addition, its entries are nonnegative (the degree-two case of Brändén–Huh). The
programme's degree-two theory:

* **Characterizations.** For symmetric `Q` the following are equivalent: the reverse
  Cauchy–Schwarz (Hodge index) inequality `Q[x] Q[y] ≤ (xᵀQy)²` whenever `Q[x] > 0`
  (`IsHyperbolic`); no plane on which `Q` is positive definite (`isHyperbolic_iff_forall_not_posDefOnPlane`);
  `Q ≤ 0` on some hyperplane (`isHyperbolic_iff_exists_nonpos_on_ker`). A hyperbolic form is
  `≤ 0` on the `Q`-orthogonal complement of every vector of positive square
  (`IsHyperbolic.nonpos_of_bil_eq_zero`).
* **Domination** (`IsHyperbolic.of_le`): a form dominated by a hyperbolic form is hyperbolic. This
  is the counterterm principle: subtracting a positive semidefinite counterterm never creates a
  positive square. Rank one plus negative semidefinite is hyperbolic (`isHyperbolic_rankOne_add`).
* **Closure.** Pullback along any linear map preserves hyperbolicity, along a nonnegative map the
  Lorentzian property (`IsHyperbolic.pullback`, `IsLorentzian.pullback`); the symmetric product of
  two nonnegative linear forms is Lorentzian (`isLorentzian_symmProd`). **Sums fail**
  (`not_isHyperbolic_add_rankOne`): two Lorentzian rank-one forms add to the identity of `ℝ²`.
* **Conditionally negative definite forms** (`IsCND`): `Q ≤ 0` on `{Σ x = 0}`. They are
  hyperbolic and closed under sums and nonnegative scaling (`IsCND.isHyperbolic`, `IsCND.add`):
  the one class in which local-to-global by summation preserves the signature.
-/

noncomputable section

open Matrix Finset

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### The form -/

/-- The bilinear form `xᵀ Q y`. -/
def bil (Q : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ := x ⬝ᵥ Q *ᵥ y

/-- The quadratic form `Q[x] = xᵀ Q x`. -/
def qf (Q : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := bil Q x x

theorem bil_add_left (Q : Matrix ι ι ℝ) (x x' y : ι → ℝ) :
    bil Q (x + x') y = bil Q x y + bil Q x' y := add_dotProduct _ _ _

theorem bil_add_right (Q : Matrix ι ι ℝ) (x y y' : ι → ℝ) :
    bil Q x (y + y') = bil Q x y + bil Q x y' := by
  simp only [bil, mulVec_add, dotProduct_add]

theorem bil_smul_left (Q : Matrix ι ι ℝ) (a : ℝ) (x y : ι → ℝ) :
    bil Q (a • x) y = a * bil Q x y := smul_dotProduct _ _ _

theorem bil_smul_right (Q : Matrix ι ι ℝ) (a : ℝ) (x y : ι → ℝ) :
    bil Q x (a • y) = a * bil Q x y := by
  simp only [bil, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bil_comm {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (x y : ι → ℝ) : bil Q x y = bil Q y x := by
  unfold bil
  rw [dotProduct_mulVec, ← mulVec_transpose, hQ.eq]
  exact dotProduct_comm _ _

theorem bil_add_matrix (Q N : Matrix ι ι ℝ) (x y : ι → ℝ) :
    bil (Q + N) x y = bil Q x y + bil N x y := by
  simp only [bil, add_mulVec, dotProduct_add]

theorem qf_add_matrix (Q N : Matrix ι ι ℝ) (x : ι → ℝ) : qf (Q + N) x = qf Q x + qf N x :=
  bil_add_matrix Q N x x

/-- The binary expansion `Q[a x + b y] = a² Q[x] + 2ab xᵀQy + b² Q[y]`. -/
theorem qf_add_smul {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (a b : ℝ) (x y : ι → ℝ) :
    qf Q (a • x + b • y) = a ^ 2 * qf Q x + 2 * a * b * bil Q x y + b ^ 2 * qf Q y := by
  simp only [qf, bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, bil_comm hQ y x]
  ring

/-- The functional `y ↦ a ⬝ᵥ y`. -/
def dotLeft (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun y := a ⬝ᵥ y
  map_add' := dotProduct_add a
  map_smul' c y := by simp only [dotProduct_smul, smul_eq_mul, RingHom.id_apply]

/-- The functional `y ↦ xᵀ Q y`. -/
def bilLeft (Q : Matrix ι ι ℝ) (x : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun := bil Q x
  map_add' := bil_add_right Q x
  map_smul' c y := by simp only [bil_smul_right, smul_eq_mul, RingHom.id_apply]

/-! ### Hyperbolic and Lorentzian forms -/

/-- **Hyperbolic**: at most one positive square, in reverse Cauchy–Schwarz form — the Hodge index
inequality `Q[x] Q[y] ≤ (xᵀQy)²` whenever `Q[x] > 0`. -/
def IsHyperbolic (Q : Matrix ι ι ℝ) : Prop :=
  ∀ x y : ι → ℝ, 0 < qf Q x → qf Q x * qf Q y ≤ bil Q x y ^ 2

/-- **Lorentzian** at degree two: symmetric, entrywise nonnegative, hyperbolic. -/
def IsLorentzian (Q : Matrix ι ι ℝ) : Prop :=
  Q.IsSymm ∧ (∀ i j, 0 ≤ Q i j) ∧ IsHyperbolic Q

/-- `Q` is positive definite on the plane spanned by `x` and `y`. -/
def PosDefOnPlane (Q : Matrix ι ι ℝ) (x y : ι → ℝ) : Prop :=
  ∀ a b : ℝ, a ≠ 0 ∨ b ≠ 0 → 0 < qf Q (a • x + b • y)

/-- **No positive definite plane.** A symmetric form is hyperbolic iff it is positive definite on
no plane: the reverse Cauchy–Schwarz inequality is the determinant of the `2 × 2` Gram matrix. -/
theorem isHyperbolic_iff_forall_not_posDefOnPlane {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) :
    IsHyperbolic Q ↔ ∀ x y, ¬ PosDefOnPlane Q x y := by
  constructor
  · intro h x y hxy
    have hx : 0 < qf Q x := by
      simpa [qf_add_smul hQ] using hxy 1 0 (Or.inl one_ne_zero)
    -- the vector `y − (xᵀQy / Q[x]) x` has square `Q[y] − (xᵀQy)²/Q[x] ≤ 0`
    have hz := hxy (-(bil Q x y / qf Q x)) 1 (Or.inr one_ne_zero)
    rw [qf_add_smul hQ] at hz
    have hcs := h x y hx
    have key : qf Q x * ((-(bil Q x y / qf Q x)) ^ 2 * qf Q x +
        2 * (-(bil Q x y / qf Q x)) * 1 * bil Q x y + 1 ^ 2 * qf Q y) =
        qf Q x * qf Q y - bil Q x y ^ 2 := by
      field_simp
      ring
    have := mul_pos hx hz
    linarith
  · intro h x y hx
    by_contra hlt
    push Not at hlt
    refine h x y fun a b hab => ?_
    rw [qf_add_smul hQ]
    have key : qf Q x * (a ^ 2 * qf Q x + 2 * a * b * bil Q x y + b ^ 2 * qf Q y) =
        (a * qf Q x + b * bil Q x y) ^ 2 + b ^ 2 * (qf Q x * qf Q y - bil Q x y ^ 2) := by ring
    rcases hab with ha | hb
    · by_cases hb : b = 0
      · subst hb
        have : 0 < a ^ 2 := by positivity
        nlinarith
      · have : 0 < b ^ 2 * (qf Q x * qf Q y - bil Q x y ^ 2) :=
          mul_pos (by positivity) (by linarith)
        have h2 : 0 < qf Q x * (a ^ 2 * qf Q x + 2 * a * b * bil Q x y + b ^ 2 * qf Q y) := by
          rw [key]; positivity
        exact pos_of_mul_pos_right h2 hx.le
    · have : 0 < b ^ 2 * (qf Q x * qf Q y - bil Q x y ^ 2) :=
        mul_pos (by positivity) (by linarith)
      have h2 : 0 < qf Q x * (a ^ 2 * qf Q x + 2 * a * b * bil Q x y + b ^ 2 * qf Q y) := by
        rw [key]; positivity
      exact pos_of_mul_pos_right h2 hx.le

/-- **Negative semidefinite on a hyperplane ⇒ hyperbolic.** -/
theorem isHyperbolic_of_nonpos_on_ker {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm)
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (h : ∀ z, ℓ z = 0 → qf Q z ≤ 0) : IsHyperbolic Q := by
  intro x y hx
  have hℓx : ℓ x ≠ 0 := fun h0 => (h x h0).not_gt hx
  set t := ℓ y / ℓ x with ht
  have hz : ℓ ((-t) • x + (1 : ℝ) • y) = 0 := by
    simp only [map_add, map_smul, smul_eq_mul, one_mul, ht]
    field_simp
    ring
  have h2 := h _ hz
  rw [qf_add_smul hQ] at h2
  nlinarith [mul_le_mul_of_nonneg_left h2 hx.le, sq_nonneg (bil Q x y - t * qf Q x)]

/-- A hyperbolic form is negative semidefinite on the `Q`-orthogonal complement of any vector of
positive square. -/
theorem IsHyperbolic.nonpos_of_bil_eq_zero {Q : Matrix ι ι ℝ} (h : IsHyperbolic Q)
    {u y : ι → ℝ} (hu : 0 < qf Q u) (hy : bil Q u y = 0) : qf Q y ≤ 0 := by
  have := h u y hu
  rw [hy] at this
  nlinarith

/-- **Hyperplane criterion.** A symmetric form is hyperbolic iff it is negative semidefinite on the
kernel of some linear functional. -/
theorem isHyperbolic_iff_exists_nonpos_on_ker {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) :
    IsHyperbolic Q ↔ ∃ ℓ : (ι → ℝ) →ₗ[ℝ] ℝ, ∀ z, ℓ z = 0 → qf Q z ≤ 0 := by
  refine ⟨fun h => ?_, fun ⟨ℓ, hℓ⟩ => isHyperbolic_of_nonpos_on_ker hQ ℓ hℓ⟩
  by_cases hpos : ∃ u, 0 < qf Q u
  · obtain ⟨u, hu⟩ := hpos
    exact ⟨bilLeft Q u, fun z hz => h.nonpos_of_bil_eq_zero hu hz⟩
  · push Not at hpos
    exact ⟨0, fun z _ => hpos z⟩

/-! ### Domination: the counterterm principle -/

/-- **Domination.** If `Q[x] ≤ Q'[x]` for all `x` and `Q'` is hyperbolic, then `Q` is hyperbolic:
a positive definite plane of `Q` would be one of `Q'`. -/
theorem IsHyperbolic.of_le {Q Q' : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hQ' : Q'.IsSymm)
    (hle : ∀ x, qf Q x ≤ qf Q' x) (h' : IsHyperbolic Q') : IsHyperbolic Q := by
  rw [isHyperbolic_iff_forall_not_posDefOnPlane hQ]
  intro x y hxy
  exact (isHyperbolic_iff_forall_not_posDefOnPlane hQ').mp h' x y fun a b hab =>
    (hxy a b hab).trans_le (hle _)

/-- Adding a negative semidefinite form preserves hyperbolicity. -/
theorem IsHyperbolic.add_of_nonpos {Q N : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hN : N.IsSymm)
    (h : IsHyperbolic Q) (hneg : ∀ x, qf N x ≤ 0) : IsHyperbolic (Q + N) :=
  h.of_le (hQ.add hN) hQ fun x => by rw [qf_add_matrix]; linarith [hneg x]

/-- **Rank one plus negative semidefinite is hyperbolic.** -/
theorem isHyperbolic_rankOne_add {N : Matrix ι ι ℝ} (hN : N.IsSymm) (v : ι → ℝ)
    (hneg : ∀ x, qf N x ≤ 0) : IsHyperbolic (vecMulVec v v + N) := by
  have hsymm : (vecMulVec v v).IsSymm := by
    ext i j; simp [vecMulVec_apply, mul_comm]
  refine isHyperbolic_of_nonpos_on_ker (hsymm.add hN) (dotLeft v) fun z hz => ?_
  have h1 : qf (vecMulVec v v) z = (v ⬝ᵥ z) ^ 2 := by
    simp only [qf, bil, vecMulVec_mulVec, dotProduct_smul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    rw [dotProduct_comm z v]; ring
  have hz' : v ⬝ᵥ z = 0 := hz
  rw [qf_add_matrix, h1, hz']
  simpa using hneg z

/-! ### Closure -/

theorem bil_pullback (Q : Matrix ι ι ℝ) (A : Matrix ι κ ℝ) (x y : κ → ℝ) :
    bil (Aᵀ * Q * A) x y = bil Q (A *ᵥ x) (A *ᵥ y) := by
  unfold bil
  simp only [← mulVec_mulVec]
  rw [dotProduct_mulVec x Aᵀ, vecMul_transpose]

/-- **Pullback** along any linear map preserves hyperbolicity. -/
theorem IsHyperbolic.pullback {Q : Matrix ι ι ℝ} (h : IsHyperbolic Q) (A : Matrix ι κ ℝ) :
    IsHyperbolic (Aᵀ * Q * A) := by
  intro x y hx
  simp only [qf, bil_pullback] at hx ⊢
  exact h _ _ hx

/-- **Nonnegative substitution** preserves the Lorentzian property. -/
theorem IsLorentzian.pullback {Q : Matrix ι ι ℝ} (h : IsLorentzian Q) {A : Matrix ι κ ℝ}
    (hA : ∀ i j, 0 ≤ A i j) : IsLorentzian (Aᵀ * Q * A) := by
  obtain ⟨hs, hnn, hh⟩ := h
  refine ⟨?_, fun i j => ?_, hh.pullback A⟩
  · unfold Matrix.IsSymm
    rw [transpose_mul, transpose_mul, transpose_transpose, hs.eq, Matrix.mul_assoc]
  · simp only [mul_apply, transpose_apply]
    exact sum_nonneg fun l _ => mul_nonneg (sum_nonneg fun k _ =>
      mul_nonneg (hA k i) (hnn k l)) (hA l j)

/-- The symmetric product `a bᵀ + b aᵀ` of two linear forms: `Q[x] = 2 (a·x)(b·x)`. -/
def symmProd (a b : ι → ℝ) : Matrix ι ι ℝ := vecMulVec a b + vecMulVec b a

theorem qf_symmProd (a b x : ι → ℝ) : qf (symmProd a b) x = 2 * ((a ⬝ᵥ x) * (b ⬝ᵥ x)) := by
  simp only [qf, bil, symmProd, add_mulVec, vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  rw [dotProduct_comm x a, dotProduct_comm x b]
  ring

/-- **The product of two nonnegative linear forms is Lorentzian** (the hyperbolic plane
`x_H x_V` is the case of two coordinate forms). -/
theorem isLorentzian_symmProd {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    IsLorentzian (symmProd a b) := by
  have hs : (symmProd a b).IsSymm := by
    ext i j; simp only [symmProd, transpose_apply, Matrix.add_apply, vecMulVec_apply]; ring
  refine ⟨hs, fun i j => ?_, isHyperbolic_of_nonpos_on_ker hs (dotLeft a) fun z hz => ?_⟩
  · simp only [symmProd, Matrix.add_apply, vecMulVec_apply]
    exact add_nonneg (mul_nonneg (ha i) (hb j)) (mul_nonneg (hb i) (ha j))
  · have hz' : a ⬝ᵥ z = 0 := hz
    rw [qf_symmProd, hz']
    simp

/-- **Sums are not closed.** The coordinate squares `x₀²` and `x₁²` are Lorentzian, their sum is
not hyperbolic. -/
theorem not_isHyperbolic_add_rankOne :
    IsLorentzian (vecMulVec (Pi.single 0 1) (Pi.single 0 1) : Matrix (Fin 2) (Fin 2) ℝ) ∧
      IsLorentzian (vecMulVec (Pi.single 1 1) (Pi.single 1 1) : Matrix (Fin 2) (Fin 2) ℝ) ∧
      ¬ IsHyperbolic (vecMulVec (Pi.single 0 1) (Pi.single 0 1) +
        vecMulVec (Pi.single 1 1) (Pi.single 1 1) : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hsq : ∀ v : Fin 2 → ℝ, (∀ i, 0 ≤ v i) → IsLorentzian (vecMulVec v v) := fun v hv => by
    have h := isLorentzian_symmProd hv hv
    have hhalf : vecMulVec v v = (1 / 2 : ℝ) • symmProd v v := by
      ext i j; simp only [symmProd, Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, smul_eq_mul]; ring
    refine ⟨?_, fun i j => by simp only [vecMulVec_apply]; exact mul_nonneg (hv i) (hv j), ?_⟩
    · ext i j; simp [vecMulVec_apply, mul_comm]
    · intro x y hx
      have e : ∀ z w, bil (vecMulVec v v) z w = (1 / 2) * bil (symmProd v v) z w := by
        intro z w; rw [hhalf]; simp only [bil, smul_mulVec, dotProduct_smul, smul_eq_mul]
      simp only [qf, e] at hx ⊢
      have := h.2.2 x y (by simpa [qf] using (by linarith : (0 : ℝ) < bil (symmProd v v) x x))
      simp only [qf] at this
      nlinarith
  refine ⟨hsq _ fun i => by fin_cases i <;> simp, hsq _ fun i => by fin_cases i <;> simp, ?_⟩
  intro h
  have := h (Pi.single 0 1) (Pi.single 1 1) (by
    simp [qf, bil, dotProduct, Fin.sum_univ_two, vecMulVec_apply])
  simp [qf, bil, dotProduct, Fin.sum_univ_two, vecMulVec_apply] at this
  linarith

/-! ### Conditionally negative definite forms -/

/-- **Conditionally negative definite**: `Q[x] ≤ 0` whenever `Σ x = 0`. -/
def IsCND (Q : Matrix ι ι ℝ) : Prop :=
  ∀ x : ι → ℝ, ∑ i, x i = 0 → qf Q x ≤ 0

/-- **CND forms are hyperbolic**: the hyperplane is `{Σ x = 0}`. -/
theorem IsCND.isHyperbolic {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (h : IsCND Q) : IsHyperbolic Q :=
  isHyperbolic_of_nonpos_on_ker hQ (dotLeft 1) fun z hz => h z (by
    simpa [dotLeft, one_dotProduct] using hz)

/-- **CND is closed under sums.** -/
theorem IsCND.add {Q N : Matrix ι ι ℝ} (hQ : IsCND Q) (hN : IsCND N) : IsCND (Q + N) :=
  fun x hx => by rw [qf_add_matrix]; linarith [hQ x hx, hN x hx]

/-- **CND is closed under nonnegative scaling.** -/
theorem IsCND.smul {Q : Matrix ι ι ℝ} (hQ : IsCND Q) {c : ℝ} (hc : 0 ≤ c) : IsCND (c • Q) :=
  fun x hx => by
    have : qf (c • Q) x = c * qf Q x := by
      simp only [qf, bil, smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hc (hQ x hx)

/-- **CND with nonnegative entries is Lorentzian.** -/
theorem IsCND.isLorentzian {Q : Matrix ι ι ℝ} (hQ : Q.IsSymm) (hnn : ∀ i j, 0 ≤ Q i j)
    (h : IsCND Q) : IsLorentzian Q :=
  ⟨hQ, hnn, h.isHyperbolic hQ⟩

end GaloisForLFunctions.ArithmeticLorentzianGeometry
