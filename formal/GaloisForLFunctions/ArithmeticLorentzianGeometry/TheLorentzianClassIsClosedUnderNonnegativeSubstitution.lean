import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheMixedHessiansOfALorentzianPolynomialAreHyperbolic
import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence
import GaloisForLFunctions.HTGeometry.CoordinateDerivationCommute
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The Lorentzian class is closed under nonnegative substitution

Polynomials are `MvPolynomial ι ℝ`. A polynomial is **mixed-Lorentzian** of degree `d`
(`IsMixedLorentzian`) if it has nonnegative coefficients, is homogeneous of degree `d`, and the
Hessian of every mixed quadratic derivative `∂_{v_1} ⋯ ∂_{v_{d−2}} p` along nonnegative
directions has one positive square.

* **Lorentzian polynomials are mixed-Lorentzian** (`IsLorentzianPolynomial.isMixedLorentzian`):
  the Hessian of `∂_{vs} p` is the mixed Hessian of the coefficients (`hess0_dirDerivs`),
  hyperbolic by the trickle-down theorem `isHyperbolic_mixHess`.
* **Differentiation** (`IsMixedLorentzian.differentiate`): `∂_v p`, `v ≥ 0`, is mixed-Lorentzian.
* **Nonnegative substitution** (`IsMixedLorentzian.subst`): `p(A y)`, `A ≥ 0`, is
  mixed-Lorentzian. The chain rule pushes directions forward, `∂_w (p ∘ A) = (∂_{A w} p) ∘ A`
  (`dirDerivs_subst`), and pulls Hessians back, `∇²(q ∘ A) = Aᵀ ∇²q A` (`hess0_subst`).
* **The Hessian at every nonnegative point has one positive square**
  (`IsMixedLorentzian.isHyperbolic_hessAt`), by Euler's identity
  `(d − 2)! ∇²p(x) = ∇²(∂_x^{d−2} p)` (`factorial_mul_hessAt`).
* **Strong log-concavity** (`IsMixedLorentzian.logConcave`): reverse Cauchy–Schwarz against the
  point itself, `∇²p(x) x = (d − 1) ∇p(x)`, gives `d p(x) ∂_v²p(x) ≤ (d − 1) (∂_v p(x))²` for
  `x ≥ 0` and every `v`: the restriction `t ↦ p(x + t v)` satisfies the Newton inequality of a
  real-rooted polynomial of degree `d` at `t = 0`.
-/

noncomputable section

open Matrix Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

variable {ι κ : Type*} [Fintype ι]

/-! ### Directional derivatives and Hessians -/

/-- The directional derivative `∂_v p = Σ_i v_i ∂_i p`. -/
def dirDeriv (v : ι → ℝ) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ := ∑ i, C (v i) * pderiv i p

/-- The iterated directional derivative `∂_{v_1} ⋯ ∂_{v_m} p`. -/
def dirDerivs (vs : List (ι → ℝ)) (p : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  vs.foldr dirDeriv p

/-- The Hessian at the origin, `(∂_j ∂_k q)(0)`: the Hessian of a quadratic. -/
def hess0 (q : MvPolynomial ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun j k => constantCoeff (pderiv j (pderiv k q))

/-- The Hessian `∇²p(x)`. -/
def hessAt (p : MvPolynomial ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun j k => eval x (pderiv j (pderiv k p))

/-- **Lorentzian polynomials** in coefficient form (`IsLorentzianPoly`). -/
def IsLorentzianPolynomial (d : ℕ) (p : MvPolynomial ι ℝ) : Prop :=
  IsLorentzianPoly d fun β => coeff β p

/-- **Mixed-Lorentzian polynomials**: nonnegative coefficients, homogeneous of degree `d`, and
every mixed quadratic derivative along nonnegative directions has a hyperbolic Hessian. -/
def IsMixedLorentzian (d : ℕ) (p : MvPolynomial ι ℝ) : Prop :=
  (∀ β, 0 ≤ coeff β p) ∧ p.IsHomogeneous d ∧
    ∀ vs : List (ι → ℝ), vs.length + 2 = d → (∀ v ∈ vs, ∀ i, 0 ≤ v i) →
      IsHyperbolic (hess0 (dirDerivs vs p))

theorem dirDerivs_cons (v : ι → ℝ) (vs : List (ι → ℝ)) (p : MvPolynomial ι ℝ) :
    dirDerivs (v :: vs) p = dirDeriv v (dirDerivs vs p) := rfl

theorem dirDerivs_append (vs ws : List (ι → ℝ)) (p : MvPolynomial ι ℝ) :
    dirDerivs (vs ++ ws) p = dirDerivs vs (dirDerivs ws p) := List.foldr_append

theorem coeff_dirDeriv (v : ι → ℝ) (p : MvPolynomial ι ℝ) (β : ι →₀ ℕ) :
    coeff β (dirDeriv v p) = ∑ i, v i * coeff β (pderiv i p) := by
  simp [dirDeriv, coeff_sum, coeff_C_mul]

variable [DecidableEq ι]

theorem mfact_mul_coeff_pderiv (p : MvPolynomial ι ℝ) (i : ι) (γ : ι →₀ ℕ) :
    mfact γ * coeff γ (pderiv i p) =
      mfact (γ + Finsupp.single i 1) * coeff (γ + Finsupp.single i 1) p := by
  rw [coeff_pderiv, mfact_add_single]; ring

/-- The coefficients of `∂_{vs} p`, times `γ!`, are the mixed derivative values. -/
theorem mfact_mul_coeff_dirDerivs (p : MvPolynomial ι ℝ) :
    ∀ (vs : List (ι → ℝ)) (γ : ι →₀ ℕ),
      mfact γ * coeff γ (dirDerivs vs p) = dval (fun β => coeff β p) vs γ
  | [], _ => rfl
  | v :: vs, γ => by
    rw [dirDerivs_cons, coeff_dirDeriv, mul_sum, dval]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, mfact_mul_coeff_pderiv, mfact_mul_coeff_dirDerivs p vs]

theorem hess0_apply_eq (q : MvPolynomial ι ℝ) (j k : ι) :
    hess0 q j k = mfact (0 + Finsupp.single j 1 + Finsupp.single k 1) *
      coeff (0 + Finsupp.single j 1 + Finsupp.single k 1) q := by
  have h0 : mfact (0 : ι →₀ ℕ) = 1 := by simp [mfact]
  calc hess0 q j k = mfact 0 * coeff 0 (pderiv j (pderiv k q)) := by
        rw [h0, one_mul]; rfl
    _ = _ := by rw [mfact_mul_coeff_pderiv, mfact_mul_coeff_pderiv]

/-- **The Hessian of `∂_{vs} p` is the mixed Hessian of the coefficients of `p`.** -/
theorem hess0_dirDerivs (vs : List (ι → ℝ)) (p : MvPolynomial ι ℝ) :
    hess0 (dirDerivs vs p) = mixHess (fun β => coeff β p) vs 0 := by
  ext j k
  rw [hess0_apply_eq, mfact_mul_coeff_dirDerivs]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem isHomogeneous_of_degree {p : MvPolynomial ι ℝ} {d : ℕ}
    (h : ∀ β, coeff β p ≠ 0 → Finsupp.degree β = d) : p.IsHomogeneous d := by
  intro β hβ
  have := h β hβ
  rw [Finsupp.degree_eq_weight_one] at this
  exact this

/-- **Lorentzian polynomials are mixed-Lorentzian.** -/
theorem IsLorentzianPolynomial.isMixedLorentzian {d : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsLorentzianPolynomial d p) : IsMixedLorentzian d p :=
  ⟨hp.1, isHomogeneous_of_degree hp.2.1, fun vs hvs hnn => by
    rw [hess0_dirDerivs]; exact isHyperbolic_mixHess hp (by simpa using hvs) hnn⟩

/-! ### Differentiation -/

omit [DecidableEq ι] in
theorem isHomogeneous_dirDeriv {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous (d + 1))
    (v : ι → ℝ) : (dirDeriv v p).IsHomogeneous d :=
  IsHomogeneous.sum _ _ _ fun i _ => by simpa using (hp.pderiv (i := i)).C_mul (v i)

omit [DecidableEq ι] in
theorem isHomogeneous_dirDerivs {p : MvPolynomial ι ℝ} :
    ∀ (vs : List (ι → ℝ)) {d : ℕ}, p.IsHomogeneous (d + vs.length) →
      (dirDerivs vs p).IsHomogeneous d
  | [], _, hp => hp
  | v :: vs, d, hp => by
    rw [dirDerivs_cons]
    refine isHomogeneous_dirDeriv (isHomogeneous_dirDerivs vs ?_) v
    simpa [add_assoc, add_comm 1] using hp

omit [DecidableEq ι] in
/-- **Differentiation**: `∂_v p` of a mixed-Lorentzian polynomial, `v ≥ 0`, is mixed-Lorentzian. -/
theorem IsMixedLorentzian.differentiate {d : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsMixedLorentzian (d + 1) p) {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    IsMixedLorentzian d (dirDeriv v p) := by
  refine ⟨fun β => ?_, isHomogeneous_dirDeriv hp.2.1 v, fun vs hvs hnn => ?_⟩
  · rw [coeff_dirDeriv]
    exact sum_nonneg fun i _ => mul_nonneg (hv i)
      (by rw [coeff_pderiv]; exact mul_nonneg (hp.1 _) (by positivity))
  · have h := hp.2.2 (vs ++ [v]) (by simp; omega) fun w hw => by
      rcases List.mem_append.mp hw with h | h
      · exact hnn w h
      · rw [List.mem_singleton.mp h]; exact hv
    rwa [dirDerivs_append] at h

/-! ### Nonnegative substitution -/

variable [Fintype κ] [DecidableEq κ]

/-- The linear substitution `x_i ↦ Σ_k A_{ik} y_k`. -/
def linSub (A : Matrix ι κ ℝ) : ι → MvPolynomial κ ℝ := fun i => ∑ k, C (A i k) * X k

omit [Fintype ι] [DecidableEq ι] in
theorem pderiv_linSub (A : Matrix ι κ ℝ) (i : ι) (k : κ) : pderiv k (linSub A i) = C (A i k) := by
  simp [linSub, pderiv_X, Pi.single_apply]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem constantCoeff_linSub (A : Matrix ι κ ℝ) (i : ι) : constantCoeff (linSub A i) = 0 := by
  simp [linSub]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem isHomogeneous_linSub (A : Matrix ι κ ℝ) (i : ι) : (linSub A i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- A linear substitution without constant terms preserves the constant coefficient. -/
theorem constantCoeff_aeval_of {g : ι → MvPolynomial κ ℝ} (hg : ∀ i, constantCoeff (g i) = 0)
    (r : MvPolynomial ι ℝ) : constantCoeff (aeval g r) = constantCoeff r := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p i hp => simp [hg]

theorem pderiv_subst (A : Matrix ι κ ℝ) (q : MvPolynomial ι ℝ) (k : κ) :
    pderiv k (aeval (linSub A) q) = aeval (linSub A) (dirDeriv (fun i => A i k) q) := by
  rw [MvPolynomial.pderiv_aeval_chain, dirDeriv, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [pderiv_linSub, map_mul, aeval_C, algebraMap_eq, mul_comm]

/-- **The chain rule for directional derivatives**: `∂_w (q ∘ A) = (∂_{A w} q) ∘ A`. -/
theorem dirDeriv_subst (A : Matrix ι κ ℝ) (w : κ → ℝ) (q : MvPolynomial ι ℝ) :
    dirDeriv w (aeval (linSub A) q) = aeval (linSub A) (dirDeriv (A *ᵥ w) q) := by
  simp only [dirDeriv, pderiv_subst, map_sum, map_mul, aeval_C, algebraMap_eq, mul_sum, mulVec,
    dotProduct, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring

theorem dirDerivs_subst (A : Matrix ι κ ℝ) (q : MvPolynomial ι ℝ) :
    ∀ ws : List (κ → ℝ),
      dirDerivs ws (aeval (linSub A) q) = aeval (linSub A) (dirDerivs (ws.map (A *ᵥ ·)) q)
  | [] => rfl
  | w :: ws => by
    rw [dirDerivs_cons, dirDerivs_subst A q ws, dirDeriv_subst, List.map_cons, dirDerivs_cons]

omit [DecidableEq ι] in
theorem constantCoeff_dirDeriv_dirDeriv (a b : ι → ℝ) (q : MvPolynomial ι ℝ) :
    constantCoeff (dirDeriv a (dirDeriv b q)) = bil (hess0 q) a b := by
  simp only [dirDeriv, map_sum, map_mul, constantCoeff_C, pderiv_C_mul, bil, dotProduct, mulVec,
    hess0, Matrix.of_apply, mul_sum]
  exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => by ring

/-- **Hessians pull back**: `∇²(q ∘ A) = Aᵀ ∇²q A`. -/
theorem hess0_subst (A : Matrix ι κ ℝ) (q : MvPolynomial ι ℝ) :
    hess0 (aeval (linSub A) q) = Aᵀ * hess0 q * A := by
  ext j k
  have h : hess0 (aeval (linSub A) q) j k =
      bil (hess0 q) (fun i => A i j) (fun i => A i k) := by
    rw [← constantCoeff_dirDeriv_dirDeriv, ← constantCoeff_aeval_of (constantCoeff_linSub A),
      ← pderiv_subst, ← pderiv_subst]
    rfl
  rw [h]
  simp only [bil, dotProduct, mulVec, Matrix.mul_apply, transpose_apply, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun l _ => by ring

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
/-- Substitution of polynomials with nonnegative coefficients into one with nonnegative
coefficients has nonnegative coefficients. -/
theorem coeff_aeval_nonneg {p : MvPolynomial ι ℝ} (hp : ∀ β, 0 ≤ coeff β p)
    {g : ι → MvPolynomial κ ℝ} (hg : ∀ i β, 0 ≤ coeff β (g i)) (β : κ →₀ ℕ) :
    0 ≤ coeff β (aeval g p) := by
  classical
  let P : MvPolynomial κ ℝ → Prop := fun q => ∀ β, 0 ≤ coeff β q
  have hmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb γ => by
    rw [coeff_mul]; exact sum_nonneg fun x _ => mul_nonneg (ha _) (hb _)
  have hone : P 1 := fun γ => by rw [coeff_one]; split_ifs <;> norm_num
  have hpow : ∀ a (n : ℕ), P a → P (a ^ n) := fun a n ha => by
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih ha
  conv_rhs => rw [p.as_sum, map_sum]
  rw [coeff_sum]
  refine sum_nonneg fun γ _ => ?_
  rw [aeval_monomial, algebraMap_eq, coeff_C_mul]
  refine mul_nonneg (hp γ) ?_
  exact Finset.prod_induction _ P hmul hone (fun i _ => hpow _ _ (hg i)) β

/-- **Nonnegative substitution**: `p(A y)`, `A ≥ 0`, of a mixed-Lorentzian `p` is
mixed-Lorentzian. -/
theorem IsMixedLorentzian.subst {d : ℕ} {p : MvPolynomial ι ℝ} (hp : IsMixedLorentzian d p)
    {A : Matrix ι κ ℝ} (hA : ∀ i k, 0 ≤ A i k) : IsMixedLorentzian d (aeval (linSub A) p) := by
  refine ⟨coeff_aeval_nonneg hp.1 fun i β => ?_, ?_, fun ws hws hnn => ?_⟩
  · simp only [linSub, coeff_sum, coeff_C_mul, coeff_X]
    exact sum_nonneg fun k _ => mul_nonneg (hA i k) (by split_ifs <;> norm_num)
  · simpa using hp.2.1.aeval (linSub A) (isHomogeneous_linSub A)
  · rw [dirDerivs_subst, hess0_subst]
    refine (hp.2.2 _ (by simpa using hws) fun v hv i => ?_).pullback A
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact sum_nonneg fun k _ => mul_nonneg (hA i k) (hnn w hw k)

/-! ### The Hessian at a nonnegative point -/

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- Euler's identity `∂_x q (x) = m q(x)` for `q` homogeneous of degree `m`. -/
theorem eval_dirDeriv_self {q : MvPolynomial ι ℝ} {m : ℕ} (hq : q.IsHomogeneous m)
    (x : ι → ℝ) : eval x (dirDeriv x q) = m * eval x q := by
  have h := congrArg (eval x) hq.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at h
  simp only [dirDeriv, map_sum, map_mul, eval_C]
  exact h

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
theorem dirDeriv_pderiv (v : ι → ℝ) (j : ι) (q : MvPolynomial ι ℝ) :
    dirDeriv v (pderiv j q) = pderiv j (dirDeriv v q) := by
  simp only [dirDeriv, map_sum, pderiv_C_mul, GaloisForLFunctions.pderiv_comm j]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
theorem dirDerivs_pderiv (j : ι) (q : MvPolynomial ι ℝ) :
    ∀ vs : List (ι → ℝ), dirDerivs vs (pderiv j q) = pderiv j (dirDerivs vs q)
  | [] => rfl
  | v :: vs => by rw [dirDerivs_cons, dirDerivs_pderiv j q vs, dirDeriv_pderiv, dirDerivs_cons]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- Iterating Euler's identity: `∂_x^m q (x) = m! q(x)` for `q` homogeneous of degree `m`. -/
theorem eval_dirDerivs_replicate (x : ι → ℝ) :
    ∀ (m : ℕ) {q : MvPolynomial ι ℝ}, q.IsHomogeneous m →
      eval x (dirDerivs (List.replicate m x) q) = (m ! : ℝ) * eval x q
  | 0, _, _ => by simp [dirDerivs]
  | m + 1, q, hq => by
    rw [List.replicate_succ', dirDerivs_append, show dirDerivs [x] q = dirDeriv x q from rfl,
      eval_dirDerivs_replicate x m (isHomogeneous_dirDeriv hq x), eval_dirDeriv_self hq,
      Nat.factorial_succ]
    push_cast; ring

omit [Fintype ι] [DecidableEq ι] in
theorem eval_eq_constantCoeff_of_isHomogeneous_zero {q : MvPolynomial ι ℝ}
    (hq : q.IsHomogeneous 0) (x : ι → ℝ) : eval x q = constantCoeff q := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hq
  rw [hq]; simp

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- **Euler's identity for the Hessian**: `(d − 2)! ∇²p(x) = ∇²(∂_x^{d−2} p)`. -/
theorem factorial_mul_hessAt {n : ℕ} {p : MvPolynomial ι ℝ} (hp : p.IsHomogeneous (n + 2))
    (x : ι → ℝ) (j k : ι) :
    (n ! : ℝ) * hessAt p x j k = hess0 (dirDerivs (List.replicate n x) p) j k := by
  have h2 : (pderiv j (pderiv k p)).IsHomogeneous n := by
    simpa using (hp.pderiv (i := k)).pderiv (i := j)
  rw [hessAt, Matrix.of_apply, ← eval_dirDerivs_replicate x n h2, dirDerivs_pderiv,
    dirDerivs_pderiv, hess0, Matrix.of_apply]
  refine eval_eq_constantCoeff_of_isHomogeneous_zero ?_ x
  rw [← dirDerivs_pderiv, ← dirDerivs_pderiv]
  exact isHomogeneous_dirDerivs _ (by simpa using h2)

omit [DecidableEq ι] in
theorem IsHyperbolic.smul_nonneg {Q : Matrix ι ι ℝ} (h : IsHyperbolic Q) {a : ℝ} (ha : 0 ≤ a) :
    IsHyperbolic (a • Q) := by
  have hb : ∀ x y, bil (a • Q) x y = a * bil Q x y := fun x y => by
    simp [bil, smul_mulVec, dotProduct_smul]
  intro u v hu
  simp only [qf, hb] at hu ⊢
  rcases ha.lt_or_eq with ha | ha
  · have := h u v (pos_of_mul_pos_right hu ha.le)
    simp only [qf] at this
    nlinarith [mul_pos ha ha]
  · rw [← ha] at hu; simp at hu

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- **The Hessian of a mixed-Lorentzian polynomial at every nonnegative point has one positive
square.** -/
theorem IsMixedLorentzian.isHyperbolic_hessAt {n : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsMixedLorentzian (n + 2) p) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    IsHyperbolic (hessAt p x) := by
  have h : hessAt p x = ((n ! : ℝ)⁻¹) • hess0 (dirDerivs (List.replicate n x) p) := by
    ext j k
    rw [Matrix.smul_apply, ← factorial_mul_hessAt hp.2.1, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (by positivity), one_mul]
  rw [h]
  refine (hp.2.2 _ (by simp) fun v hv => ?_).smul_nonneg (by positivity)
  rw [List.eq_of_mem_replicate hv]; exact hx

omit [Fintype ι] [DecidableEq ι] in
theorem eval_nonneg_of_coeff_nonneg {p : MvPolynomial ι ℝ} (hp : ∀ β, 0 ≤ coeff β p)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : 0 ≤ eval x p := by
  rw [eval_eq]
  exact sum_nonneg fun β _ => mul_nonneg (hp β) (prod_nonneg fun i _ => pow_nonneg (hx i) _)

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
/-- **Strong log-concavity**: `d p(x) ∂_v²p(x) ≤ (d − 1) (∂_v p(x))²` at every nonnegative
point, for every direction `v`. -/
theorem IsMixedLorentzian.logConcave {n : ℕ} {p : MvPolynomial ι ℝ}
    (hp : IsMixedLorentzian (n + 2) p) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (v : ι → ℝ) :
    ((n : ℝ) + 2) * eval x p * eval x (dirDeriv v (dirDeriv v p)) ≤
      ((n : ℝ) + 1) * eval x (dirDeriv v p) ^ 2 := by
  set H := hessAt p x
  have hdj : ∀ j, (pderiv j p).IsHomogeneous (n + 1) := fun j => by
    simpa using hp.2.1.pderiv (i := j)
  -- `∇²p(x) x = (d − 1) ∇p(x)`
  have hHx : ∀ j, (H *ᵥ x) j = ((n : ℝ) + 1) * eval x (pderiv j p) := fun j => by
    have := eval_dirDeriv_self (hdj j) x
    push_cast at this
    rw [← this]
    simp only [H, hessAt, mulVec, dotProduct, Matrix.of_apply, dirDeriv, map_sum, map_mul,
      eval_C, GaloisForLFunctions.pderiv_comm j]
    exact sum_congr rfl fun k _ => by ring
  have hqx : qf H x = ((n : ℝ) + 1) * ((n : ℝ) + 2) * eval x p := by
    have := eval_dirDeriv_self hp.2.1 x
    push_cast at this
    rw [qf, bil, dotProduct]
    simp only [hHx]
    simp only [dirDeriv, map_sum, map_mul, eval_C] at this
    rw [mul_assoc, ← this, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have hbx : bil H x v = ((n : ℝ) + 1) * eval x (dirDeriv v p) := by
    rw [bil_comm (Matrix.IsSymm.ext fun j k => by
      simp only [H, hessAt, Matrix.of_apply, GaloisForLFunctions.pderiv_comm j]), bil,
      dotProduct]
    simp only [hHx, dirDeriv, map_sum, map_mul, eval_C, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have hqv : qf H v = eval x (dirDeriv v (dirDeriv v p)) := by
    simp only [qf, bil, dotProduct, mulVec, H, hessAt, Matrix.of_apply, dirDeriv, map_sum,
      map_mul, eval_C, pderiv_C_mul, mul_sum]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  rcases (eval_nonneg_of_coeff_nonneg hp.1 hx).lt_or_eq with hpos | hzero
  · have hcs := hp.isHyperbolic_hessAt hx x v (by rw [hqx]; positivity)
    rw [hqx, hbx, hqv] at hcs
    have hn : (0 : ℝ) < n + 1 := by positivity
    nlinarith
  · rw [← hzero, mul_zero, zero_mul]
    positivity

end GaloisForLFunctions.ArithmeticLorentzianGeometry
