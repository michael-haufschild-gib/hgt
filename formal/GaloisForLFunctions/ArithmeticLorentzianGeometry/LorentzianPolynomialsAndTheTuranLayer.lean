import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianFormsAtDegreeTwo
import GaloisForLFunctions.RHTower.XiTaylorCoefficientsLogConcave

/-!
# Lorentzian polynomials and the Turán layer

A homogeneous polynomial `f = Σ_β c_β x^β` of degree `d` is **Lorentzian** (Brändén–Huh) when its
coefficients are nonnegative, its support is M-convex, and every quadratic derivative `∂^α f`,
`|α| = d − 2`, is a hyperbolic quadratic form (`IsLorentzianPoly`). The Hessian of `∂^α f` has
entries `(α + e_i + e_j)! c_{α + e_i + e_j}` (`quadDeriv`).

* **The `2 × 2` criterion** (`isHyperbolic_fin_two_iff`): a symmetric `2 × 2` form with nonnegative
  first diagonal entry is hyperbolic iff its determinant is `≤ 0`; the Lagrange identity
  `Q[x]Q[y] − (xᵀQy)² = det Q · (x₀y₁ − x₁y₀)²` (`qf_mul_qf_sub_bil_sq_fin_two`).
* **Bivariate Lorentzian = ultra-log-concave** (`isLorentzianPoly_bivariate_iff`): for
  `f = Σ_k a_k x^k y^{d−k}` with `a ≥ 0`, Lorentzian ⇔ interval support and
  `(a_i/C(d,i))(a_{i+2}/C(d,i+2)) ≤ (a_{i+1}/C(d,i+1))²` for `i ≤ d − 2`.
* **The Turán layer of `ξ`** (`isLorentzianPoly_jensen_of_turanSeq`, `xi_jensen_isLorentzianPoly`):
  the homogenized Jensen polynomial `Σ_k C(d,k) γ_{n+k} x^k y^{d−k}` of a Turán sequence is
  Lorentzian for all `d, n`. With `γ_k` the Taylor coefficients of `ξ(½ + x) = Σ γ_k x^{2k}`, which
  form a Turán sequence unconditionally (`RHTower.xi_centre_turanSeq`), every Jensen polynomial
  of `ξ` at the centre is Lorentzian.

Real-rootedness of these Jensen polynomials is a consequence of RH; Lorentzian is the
log-concavity layer of real stability, and at degree `d ≥ 3` it is strictly weaker. Pólya's
criterion uses the factorial normalization `k! γ_k`, whose Lorentzian layer is the sharper Newton
inequality `γ_k² ≥ (1 + 1/k) γ_{k−1} γ_{k+1}`.
-/

noncomputable section

open Matrix Finset
open scoped Nat

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

/-! ### The `2 × 2` criterion -/

/-- **The Lagrange identity** for a symmetric `2 × 2` form. -/
theorem qf_mul_qf_sub_bil_sq_fin_two {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.IsSymm)
    (x y : Fin 2 → ℝ) :
    qf Q x * qf Q y - bil Q x y ^ 2 = (Q 0 0 * Q 1 1 - Q 0 1 ^ 2) * (x 0 * y 1 - x 1 * y 0) ^ 2 := by
  have h10 : Q 1 0 = Q 0 1 := hQ.apply 0 1
  simp only [qf, bil, dotProduct, mulVec, Fin.sum_univ_two, h10]
  ring

/-- **A `2 × 2` form with `Q₀₀ ≥ 0` is hyperbolic iff `det Q ≤ 0`.** -/
theorem isHyperbolic_fin_two_iff {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.IsSymm)
    (h00 : 0 ≤ Q 0 0) : IsHyperbolic Q ↔ Q 0 0 * Q 1 1 ≤ Q 0 1 ^ 2 := by
  constructor
  · intro h
    by_contra hdet
    push Not at hdet
    have hpos : 0 < Q 0 0 := by
      rcases eq_or_lt_of_le h00 with h0 | h0
      · rw [← h0, zero_mul] at hdet; nlinarith [sq_nonneg (Q 0 1)]
      · exact h0
    have hx : qf Q (Pi.single 0 1) = Q 0 0 := by
      simp [qf, bil, dotProduct, mulVec, Fin.sum_univ_two]
    have := h (Pi.single 0 1) (Pi.single 1 1) (by rw [hx]; exact hpos)
    have e := qf_mul_qf_sub_bil_sq_fin_two hQ (Pi.single 0 1) (Pi.single 1 1)
    simp at e
    linarith
  · intro hdet x y _
    have e := qf_mul_qf_sub_bil_sq_fin_two hQ x y
    have : (Q 0 0 * Q 1 1 - Q 0 1 ^ 2) * (x 0 * y 1 - x 1 * y 0) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    linarith

/-! ### Lorentzian polynomials in coefficient form -/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multi-index factorial `β! = ∏_i β_i!`. -/
def mfact (β : ι →₀ ℕ) : ℝ := β.prod fun _ k => (k ! : ℝ)

/-- The Hessian of the quadratic derivative `∂^α f`: entries `(α + e_i + e_j)! c_{α+e_i+e_j}`. -/
def quadDeriv (c : (ι →₀ ℕ) → ℝ) (α : ι →₀ ℕ) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    mfact (α + Finsupp.single i 1 + Finsupp.single j 1) * c (α + Finsupp.single i 1 + Finsupp.single j 1)

/-- **M-convexity** (the exchange property of the support). -/
def IsMConvex (S : Set (ι →₀ ℕ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ i, β i < α i →
    ∃ j, α j < β j ∧ α - Finsupp.single i 1 + Finsupp.single j 1 ∈ S

/-- **Lorentzian polynomial** of degree `d` in coefficient form: nonnegative coefficients,
homogeneous of degree `d`, M-convex support, hyperbolic quadratic derivatives. -/
def IsLorentzianPoly (d : ℕ) (c : (ι →₀ ℕ) → ℝ) : Prop :=
  (∀ β, 0 ≤ c β) ∧ (∀ β, c β ≠ 0 → Finsupp.degree β = d) ∧ IsMConvex {β | c β ≠ 0} ∧
    ∀ α : ι →₀ ℕ, Finsupp.degree α + 2 = d → IsHyperbolic (quadDeriv c α)

omit [Fintype ι] [DecidableEq ι] in
theorem quadDeriv_isSymm (c : (ι →₀ ℕ) → ℝ) (α : ι →₀ ℕ) : (quadDeriv c α).IsSymm :=
  Matrix.IsSymm.ext fun i j => by
    simp only [quadDeriv, Matrix.of_apply, add_assoc, add_comm (Finsupp.single i 1)]

end General

/-! ### Bivariate polynomials -/

/-- The coefficient function of `Σ_k a_k x^k y^{d−k}`. -/
def bivariateCoeff (d : ℕ) (a : ℕ → ℝ) (β : Fin 2 →₀ ℕ) : ℝ :=
  if β 0 + β 1 = d then a (β 0) else 0

/-- The Hessian of `∂_x^i ∂_y^{d−2−i} f`. -/
def bivariateHessian (d : ℕ) (a : ℕ → ℝ) (i : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((i + 2)! * (d - (i + 2))! : ℝ) * a (i + 2), ((i + 1)! * (d - (i + 1))! : ℝ) * a (i + 1);
     ((i + 1)! * (d - (i + 1))! : ℝ) * a (i + 1), (i ! * (d - i)! : ℝ) * a i]

theorem mfact_fin_two (β : Fin 2 →₀ ℕ) : mfact β = (β 0)! * (β 1)! := by
  rw [mfact, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]

theorem quadDeriv_bivariateCoeff {d : ℕ} (a : ℕ → ℝ) {α : Fin 2 →₀ ℕ}
    (hα : α 0 + α 1 + 2 = d) : quadDeriv (bivariateCoeff d a) α = bivariateHessian d a (α 0) := by
  have h2 : d - (α 0 + 2) = α 1 := by omega
  have h1 : d - (α 0 + 1) = α 1 + 1 := by omega
  have h0 : d - α 0 = α 1 + 2 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadDeriv, bivariateCoeff, bivariateHessian, mfact_fin_two, Finsupp.single_apply, h0, h1,
      h2] <;> exact fun h => absurd (by omega) h

/-- `k! (d − k)! = d!/C(d,k)` as reals. -/
theorem factorial_mul_factorial_eq {d k : ℕ} (hk : k ≤ d) :
    ((k ! * (d - k)! : ℕ) : ℝ) = (d ! : ℝ) / (d.choose k : ℝ) := by
  have h := Nat.choose_mul_factorial_mul_factorial hk
  have hc : (0 : ℝ) < d.choose k := by exact_mod_cast Nat.choose_pos hk
  rw [eq_div_iff hc.ne', ← h]
  push_cast; ring

/-- **The quadratic derivatives are hyperbolic iff ultra-log-concavity.** -/
theorem isHyperbolic_bivariateHessian_iff {d : ℕ} {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) {i : ℕ}
    (hi : i + 2 ≤ d) :
    IsHyperbolic (bivariateHessian d a i) ↔
      a i / d.choose i * (a (i + 2) / d.choose (i + 2)) ≤ (a (i + 1) / d.choose (i + 1)) ^ 2 := by
  have hsymm : (bivariateHessian d a i).IsSymm := by
    ext j k; fin_cases j <;> fin_cases k <;> rfl
  rw [isHyperbolic_fin_two_iff hsymm (by
    simp only [bivariateHessian, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact mul_nonneg (by positivity) (ha _))]
  have w2 := factorial_mul_factorial_eq (d := d) (k := i + 2) hi
  have w1 := factorial_mul_factorial_eq (d := d) (k := i + 1) (by omega)
  have w0 := factorial_mul_factorial_eq (d := d) (k := i) (by omega)
  push_cast at w2 w1 w0
  have hc2 : (0 : ℝ) < d.choose (i + 2) := by exact_mod_cast Nat.choose_pos hi
  have hc1 : (0 : ℝ) < d.choose (i + 1) := by exact_mod_cast Nat.choose_pos (by omega)
  have hc0 : (0 : ℝ) < d.choose i := by exact_mod_cast Nat.choose_pos (by omega)
  have hD : (0 : ℝ) < (d ! : ℝ) ^ 2 := by positivity
  simp only [bivariateHessian, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [w2, w1, w0]
  have e1 : (d ! : ℝ) / d.choose (i + 2) * a (i + 2) * ((d ! : ℝ) / d.choose i * a i) =
      (d ! : ℝ) ^ 2 * (a i / d.choose i * (a (i + 2) / d.choose (i + 2))) := by
    field_simp
  have e2 : ((d ! : ℝ) / d.choose (i + 1) * a (i + 1)) ^ 2 =
      (d ! : ℝ) ^ 2 * (a (i + 1) / d.choose (i + 1)) ^ 2 := by
    field_simp
  rw [e1, e2]
  exact ⟨fun h => le_of_mul_le_mul_left h hD, fun h => mul_le_mul_of_nonneg_left h hD.le⟩

/-- Interval support of a coefficient sequence on `[0, d]`. -/
def IntervalSupport (d : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ l m k, l < m → m < k → k ≤ d → a l ≠ 0 → a k ≠ 0 → a m ≠ 0

/-- The degree-`d` bivariate monomial `x^k y^{d−k}` as a multi-index. -/
def bimon (d k : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (d - k)

theorem bimon_apply_zero (d k : ℕ) : bimon d k 0 = k := by simp [bimon]

theorem bimon_apply_one (d k : ℕ) : bimon d k 1 = d - k := by simp [bimon]

theorem eq_bimon {d : ℕ} {β : Fin 2 →₀ ℕ} (h : β 0 + β 1 = d) : β = bimon d (β 0) := by
  ext i; fin_cases i
  · simp [bimon_apply_zero]
  · simp only [Fin.mk_one, Fin.isValue, bimon_apply_one]; omega

/-- **Interval support ⇔ M-convex support** for bivariate coefficient functions. -/
theorem isMConvex_bivariate_iff {d : ℕ} {a : ℕ → ℝ} :
    IsMConvex {β | bivariateCoeff d a β ≠ 0} ↔ IntervalSupport d a := by
  have hmem : ∀ k, k ≤ d → (bimon d k ∈ {β | bivariateCoeff d a β ≠ 0} ↔ a k ≠ 0) := by
    intro k hk
    simp only [Set.mem_setOf_eq, bivariateCoeff, bimon_apply_zero, bimon_apply_one]
    rw [if_pos (by omega)]
  constructor
  · intro hM l m k hlm hmk hkd hl hk
    -- walk down from `k` towards `l`
    have key : ∀ t, t ≤ k - m → a (k - t) ≠ 0 := by
      intro t
      induction t with
      | zero => intro _; simpa using hk
      | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        obtain ⟨j, hj, hjS⟩ := hM (bimon d (k - t)) ((hmem _ (by omega)).mpr hprev) (bimon d l)
          ((hmem _ (by omega)).mpr hl) 0 (by rw [bimon_apply_zero, bimon_apply_zero]; omega)
        fin_cases j
        · simp [bimon_apply_zero] at hj; omega
        · have he : bimon d (k - t) - Finsupp.single 0 1 + Finsupp.single 1 1 =
              bimon d (k - (t + 1)) := by
            ext i; fin_cases i <;>
              simp [bimon] <;> omega
          simp only [Fin.mk_one] at hjS
          rw [he] at hjS
          exact (hmem _ (by omega)).mp hjS
    have := key (k - m) le_rfl
    rwa [show k - (k - m) = m by omega] at this
  · intro hI α hα β hβ i hi
    simp only [Set.mem_setOf_eq, bivariateCoeff] at hα hβ
    split_ifs at hα hβ with hα' hβ'
    · have hi01 : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      rcases hi01 with rfl | rfl
      · refine ⟨1, by omega, ?_⟩
        simp only [Set.mem_setOf_eq, bivariateCoeff]
        have h0 : (α - Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = α 0 - 1 := by
          simp
        have h1 : (α - Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 = α 1 + 1 := by
          simp
        rw [h0, h1, if_pos (by omega)]
        rcases eq_or_lt_of_le (show β 0 ≤ α 0 - 1 by omega) with he | hlt
        · rw [← he]; exact hβ
        · exact hI (β 0) (α 0 - 1) (α 0) hlt (by omega) (by omega) hβ hα
      · refine ⟨0, by omega, ?_⟩
        simp only [Set.mem_setOf_eq, bivariateCoeff]
        have h0 : (α - Finsupp.single 1 1 + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 0 = α 0 + 1 := by
          simp
        have h1 : (α - Finsupp.single 1 1 + Finsupp.single 0 1 : Fin 2 →₀ ℕ) 1 = α 1 - 1 := by
          simp
        rw [h0, h1, if_pos (by omega)]
        rcases eq_or_lt_of_le (show α 0 + 1 ≤ β 0 by omega) with he | hlt
        · rw [he]; exact hβ
        · exact hI (α 0) (α 0 + 1) (β 0) (by omega) hlt (by omega) hα hβ
    all_goals simp_all

/-- **Bivariate Lorentzian = ultra-log-concave with interval support.** -/
theorem isLorentzianPoly_bivariate_iff {d : ℕ} {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) :
    IsLorentzianPoly d (bivariateCoeff d a) ↔
      IntervalSupport d a ∧ ∀ i, i + 2 ≤ d →
        a i / d.choose i * (a (i + 2) / d.choose (i + 2)) ≤ (a (i + 1) / d.choose (i + 1)) ^ 2 := by
  have hnn : ∀ β, 0 ≤ bivariateCoeff d a β := fun β => by
    unfold bivariateCoeff; split_ifs; exacts [ha _, le_rfl]
  have hdeg : ∀ β, bivariateCoeff d a β ≠ 0 → Finsupp.degree β = d := fun β h => by
    unfold bivariateCoeff at h; split_ifs at h with hb
    · rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]; exact hb
    · exact absurd rfl h
  constructor
  · rintro ⟨-, -, hM, hQ⟩
    refine ⟨isMConvex_bivariate_iff.mp hM, fun i hi => ?_⟩
    have hα : Finsupp.degree (bimon (d - 2) i) + 2 = d := by
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, bimon_apply_zero, bimon_apply_one]; omega
    have := hQ _ hα
    rw [quadDeriv_bivariateCoeff a (by rw [bimon_apply_zero, bimon_apply_one]; omega),
      bimon_apply_zero] at this
    exact (isHyperbolic_bivariateHessian_iff ha hi).mp this
  · rintro ⟨hI, hU⟩
    refine ⟨hnn, hdeg, isMConvex_bivariate_iff.mpr hI, fun α hα => ?_⟩
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hα
    rw [quadDeriv_bivariateCoeff a hα]
    exact (isHyperbolic_bivariateHessian_iff ha (by omega)).mpr (hU _ (by omega))

/-! ### Jensen polynomials and the Turán layer of `ξ` -/

open GaloisForLFunctions.HTGeometry

/-- The coefficients `C(d,k) γ_{n+k}` of the homogenized Jensen polynomial. -/
def jensenCoeff (d n : ℕ) (γ : ℕ → ℝ) (k : ℕ) : ℝ := if k ≤ d then d.choose k * γ (n + k) else 0

theorem jensenCoeff_div_choose {d n : ℕ} (γ : ℕ → ℝ) {k : ℕ} (hk : k ≤ d) :
    jensenCoeff d n γ k / d.choose k = γ (n + k) := by
  have hc : (d.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [jensenCoeff, if_pos hk]; field_simp

/-- In a Turán sequence a vanishing term after a nonvanishing one kills every later term. -/
theorem TuranSeq.eq_zero_of_eq_zero {γ : ℕ → ℝ} (hγ : TuranSeq γ) {i j : ℕ} (hij : i < j)
    (hi : γ i ≠ 0) (hj : γ j = 0) : ∀ t, γ (j + t) = 0 := by
  intro t
  induction t with
  | zero => simpa using hj
  | succ t ih =>
    have h := hγ.2 i (j + t) (by omega)
    rw [ih, mul_zero] at h
    have hpos : 0 < γ i := lt_of_le_of_ne (hγ.1 i) (Ne.symm hi)
    have := hγ.1 (j + t + 1)
    rw [← add_assoc]
    nlinarith

/-- **Jensen polynomials of a Turán sequence are Lorentzian.** -/
theorem isLorentzianPoly_jensen_of_turanSeq {γ : ℕ → ℝ} (hγ : TuranSeq γ) (d n : ℕ) :
    IsLorentzianPoly d (bivariateCoeff d (jensenCoeff d n γ)) := by
  have ha : ∀ k, 0 ≤ jensenCoeff d n γ k := fun k => by
    unfold jensenCoeff; split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (hγ.1 _)
    · exact le_rfl
  refine (isLorentzianPoly_bivariate_iff ha).mpr ⟨fun l m k hlm hmk hkd hl hk => ?_, fun i hi => ?_⟩
  · have hlγ : γ (n + l) ≠ 0 := by
      intro h; apply hl; rw [jensenCoeff, if_pos (by omega), h, mul_zero]
    have hkγ : γ (n + k) ≠ 0 := by
      intro h; apply hk; rw [jensenCoeff, if_pos hkd, h, mul_zero]
    intro hm
    have hmγ : γ (n + m) = 0 := by
      rw [jensenCoeff, if_pos (by omega)] at hm
      rcases mul_eq_zero.mp hm with h | h
      · exact absurd h (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
      · exact h
    have := TuranSeq.eq_zero_of_eq_zero hγ (show n + l < n + m by omega) hlγ hmγ (k - m)
    rw [show n + m + (k - m) = n + k by omega] at this
    exact hkγ this
  · rw [jensenCoeff_div_choose γ (by omega), jensenCoeff_div_choose γ hi,
      jensenCoeff_div_choose γ (by omega)]
    have h := hγ.2 (n + i) (n + i + 1) (by omega)
    rw [show n + (i + 2) = n + i + 1 + 1 by ring, show n + (i + 1) = n + i + 1 by ring, sq]
    linarith

/-- **The Turán layer of `ξ` holds unconditionally**: every homogenized Jensen polynomial of the
Taylor coefficients of `ξ(½ + x) = Σ γ_k x^{2k}` is Lorentzian. -/
theorem xi_jensen_isLorentzianPoly (d n : ℕ) :
    IsLorentzianPoly d
      (bivariateCoeff d (jensenCoeff d n (RHTower.evenTaylorRe fun x => RHTower.xi (1 / 2 + x)))) :=
  isLorentzianPoly_jensen_of_turanSeq RHTower.xi_centre_turanSeq d n

end GaloisForLFunctions.ArithmeticLorentzianGeometry
