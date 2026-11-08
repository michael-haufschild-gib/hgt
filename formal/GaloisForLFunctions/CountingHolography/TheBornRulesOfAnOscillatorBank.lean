import GaloisForLFunctions.CountingHolography.TheBornRuleOfABlackHole
import GaloisForLFunctions.CountingHolography.TheBoundarySquareIsTheOscillation

/-!
# The Born rules of an oscillator bank

A curve over `𝔽_q` of genus `g` with Frobenius pairs `α_k, q/α_k` is a bank of `g` oscillators
`z² - t_k z + q`; the genus-two black hole is a bank of two. On the echo states of the bank, pairs of
consecutive echoes for each oscillator, one double tick acts by the block-diagonal companion matrix
`bankDelay` (`bankDelay_mode`: every root of every oscillator is a mode).

* **Every Born rule, block by block** (`bornRule_bank_blocks`): covariance forbids a Born rule to pair
  oscillators with `t_k ≠ t_l` (`block_eq_zero_of_ne`), and pairs two copies of one oscillator by
  `c 𝒬_t + d J`, the Krein square and the Wronskian (`block_eq_of_eq_trace`, `wronskian_bornRule`).
  With distinct traces a symmetric Born rule is `Σ c_k 𝒬_{t_k}` (`bornRule_bank_eq`).
* **A count exists exactly when every oscillator is damped**, whatever the traces
  (`exists_positive_bornRule_bank_iff'`); with distinct traces the positive Born rules are
  `Σ c_k 𝒬_{t_k}` with every `c_k > 0` (`bankKrein_positive_iff`).
* **A repeated damped oscillator carries a Hermitian form.** On `m` copies of an oscillator with
  `t² < 4q`, the echo states have complex coordinates `φ(u) = (u₁ − t u₀/2) + i s u₀`,
  `s = √(q − t²/4)`, in which a Born rule is `Re(z* H z)` (`quad_eq_bornHermitian`); it is positive iff
  `H` is positive definite (`bornRule_positive_iff_hermitian`). The counts of a curve with repeated
  Frobenius eigenvalues are the positive Hermitian forms on the multiplicity space.
* **The positive cone of a damped bank** is the direct sum over its trace classes: a Born rule splits
  as `S(x) = Σ_τ S(x_τ)` (`quad_eq_sum_classes`), is the Hermitian form of the class on each
  (`quad_class_eq_bornHermitian`), and is positive iff every class form is positive definite
  (`bornRule_positive_iff_classes`).
* **Four modes off the circle carry a hyperbolic Born rule and no count** (`offCircle_quadruple`): the
  delay of `α, ᾱ, q/α, q/ᾱ` pairs its two planes by a nondegenerate split form
  (`hyperbolicForm_bornRule`), and no positive form is covariant.

So at every genus the quadratic half of the count law is a family of Born rules present for every bank,
and the count half is the damping of all oscillators.
-/

open Matrix Finset

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

variable {g : Type*} [Fintype g] [DecidableEq g]

/-- The Krein square of one oscillator as a symmetric matrix on its echo state. -/
def kreinMatrix (q t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![q, -t / 2; -t / 2, 1]

/-- The delay of a bank of oscillators `z² - t_k z + q` on its echo states. -/
def bankDelay (q : ℝ) (t : g → ℝ) : Matrix (Fin 2 × g) (Fin 2 × g) ℝ :=
  Matrix.blockDiagonal fun k => lpMatrix q (t k)

/-- The weighted sum `Σ c_k 𝒬_{t_k}` of the Krein squares of the bank. -/
def bankKrein (q : ℝ) (t c : g → ℝ) : Matrix (Fin 2 × g) (Fin 2 × g) ℝ :=
  Matrix.blockDiagonal fun k => c k • kreinMatrix q (t k)

/-- The block of `S` pairing the echoes of oscillator `k` with those of oscillator `l`. -/
def block (S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ) (k l : g) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => S (a, k) (b, l)

/-- **Covariance block by block.** -/
theorem bankDelay_conj_apply (q : ℝ) (t : g → ℝ) (S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ)
    (a b : Fin 2) (k l : g) :
    ((bankDelay q t)ᵀ * S * bankDelay q t) (a, k) (b, l) =
      ((lpMatrix q (t k))ᵀ * block S k l * lpMatrix q (t l)) a b := by
  simp only [bankDelay, Matrix.mul_apply, Matrix.transpose_apply, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, block]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul]

/-- **No Born rule pairs two oscillators with different traces.** -/
theorem block_eq_zero_of_ne {q s u : ℝ} (hq : q ≠ 0) (hsu : s ≠ u) {X : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (lpMatrix q s)ᵀ * X * lpMatrix q u = q • X) : X = 0 := by
  have E (a b : Fin 2) := congrFun (congrFun h a) b
  have e00 := E 0 0
  have e01 := E 0 1
  have e10 := E 1 0
  have e11 := E 1 1
  simp [lpMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have f00 : X 0 0 = q * X 1 1 := mul_left_cancel₀ hq (by linear_combination -e00)
  have f01 : X 0 1 = -(X 1 1 * u) - X 1 0 := mul_left_cancel₀ hq (by linear_combination -e01)
  have f10 : X 1 0 = -(X 0 1 + s * X 1 1) := mul_left_cancel₀ hq (by linear_combination -e10)
  have h11 : X 1 1 = 0 := by
    have : (s - u) * X 1 1 = 0 := by linear_combination f10 - f01
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hsu)
  have h00 : X 0 0 = 0 := by rw [f00, h11, mul_zero]
  have h10 : X 1 0 = 0 := by
    have : (s - u) * X 1 0 = 0 := by
      linear_combination e11 - h00 - u * f01 - (s * u - q - u ^ 2) * h11
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hsu)
  have h01 : X 0 1 = 0 := by rw [f01, h11, h10]; ring
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h00, h01, h10, h11]

/-- **On one oscillator a symmetric Born rule is a multiple of its Krein square.** -/
theorem block_eq_krein {q s : ℝ} (hq : q ≠ 0) {X : Matrix (Fin 2) (Fin 2) ℝ} (hsym : X 1 0 = X 0 1)
    (h : (lpMatrix q s)ᵀ * X * lpMatrix q s = q • X) : X = X 1 1 • kreinMatrix q s := by
  have E (a b : Fin 2) := congrFun (congrFun h a) b
  have e00 := E 0 0
  have e01 := E 0 1
  simp [lpMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have f00 : X 0 0 = q * X 1 1 := mul_left_cancel₀ hq (by linear_combination -e00)
  have f01 : X 0 1 = -(X 1 1 * s) / 2 :=
    mul_left_cancel₀ hq (by linear_combination (-1 / 2 : ℝ) * e01 - (q / 2) * hsym)
  ext a b
  fin_cases a <;> fin_cases b <;> simp [kreinMatrix] <;> linarith

/-- **The Born rules of a bank with distinct traces are the weighted sums of its Krein squares.** -/
theorem bornRule_bank_eq {q : ℝ} (hq : q ≠ 0) {t : g → ℝ} (ht : Function.Injective t)
    {S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ} (hsym : Sᵀ = S) (h : IsBornRule S (bankDelay q t) q) :
    S = bankKrein q t fun k => S (1, k) (1, k) := by
  have hblock (k l : g) : (lpMatrix q (t k))ᵀ * block S k l * lpMatrix q (t l) = q • block S k l := by
    ext a b
    have e := bankDelay_conj_apply q t S a b k l
    rw [h] at e
    rw [← e]
    simp [block]
  ext ⟨a, k⟩ ⟨b, l⟩
  simp only [bankKrein, Matrix.blockDiagonal_apply]
  split_ifs with hkl
  · subst hkl
    have hs : block S k k 1 0 = block S k k 0 1 := by
      simp only [block]
      have := congrFun (congrFun hsym (0, k)) (1, k)
      rwa [Matrix.transpose_apply] at this
    have := congrFun (congrFun (block_eq_krein hq hs (hblock k k)) a) b
    simpa [block] using this
  · have := congrFun (congrFun (block_eq_zero_of_ne hq (fun h => hkl (ht h)) (hblock k l)) a) b
    simpa [block] using this

/-- The weighted Krein squares are a Born rule. -/
theorem bankKrein_bornRule (q : ℝ) (t c : g → ℝ) : IsBornRule (bankKrein q t c) (bankDelay q t) q := by
  unfold IsBornRule
  ext ⟨a, k⟩ ⟨b, l⟩
  rw [bankDelay_conj_apply]
  by_cases hkl : k = l
  · subst hkl
    have hb : block (bankKrein q t c) k k = c k • kreinMatrix q (t k) := by
      ext a' b'
      simp [block, bankKrein, Matrix.blockDiagonal_apply]
    rw [hb]
    simp only [Matrix.smul_apply, bankKrein, Matrix.blockDiagonal_apply, if_true, smul_eq_mul]
    fin_cases a <;> fin_cases b <;>
      simp [lpMatrix, kreinMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · have hb : block (bankKrein q t c) k l = 0 := by
      ext a' b'
      simp [block, bankKrein, Matrix.blockDiagonal_apply, hkl]
    rw [hb]
    simp [bankKrein, Matrix.blockDiagonal_apply, hkl]

/-- The form of the weighted Krein squares. -/
theorem bankKrein_quad (q : ℝ) (t c : g → ℝ) (x : Fin 2 × g → ℝ) :
    x ⬝ᵥ bankKrein q t c *ᵥ x = ∑ k, c k * kreinSquare q (t k) (x (0, k)) (x (1, k)) := by
  simp only [bankKrein, dotProduct, Matrix.mulVec, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [kreinMatrix, Fin.sum_univ_two, kreinSquare, Matrix.smul_apply]
  ring

/-- A Krein square is positive definite exactly in the damped case. -/
theorem kreinSquare_pos_iff {q t : ℝ} :
    (∀ u v : ℝ, (u ≠ 0 ∨ v ≠ 0) → 0 < kreinSquare q t u v) ↔ t ^ 2 < 4 * q := by
  constructor
  · intro h
    have := h 2 t (Or.inl two_ne_zero)
    simp [kreinSquare] at this
    nlinarith
  · intro ht u v huv
    rw [kreinSquare_eq_sum_sq ht.le]
    have hs : 0 < Real.sqrt (q - t ^ 2 / 4) := Real.sqrt_pos.mpr (by linarith)
    rcases eq_or_ne u 0 with hu | hu
    · subst hu
      have hv : v ≠ 0 := huv.resolve_left (by simp)
      simp only [mul_zero, sub_zero, zero_div]
      have : 0 < v ^ 2 := by positivity
      nlinarith
    · have : 0 < (Real.sqrt (q - t ^ 2 / 4) * u) ^ 2 := by positivity
      nlinarith [sq_nonneg (v - t * u / 2)]

/-- **The positive Born rules of a bank**: every weight positive and every oscillator damped. -/
theorem bankKrein_positive_iff (q : ℝ) (t c : g → ℝ) :
    IsPositive (bankKrein q t c) ↔ ∀ k, 0 < c k ∧ t k ^ 2 < 4 * q := by
  classical
  constructor
  · intro hpos k
    -- probes supported on the oscillator `k`
    have probe (u v : ℝ) (huv : u ≠ 0 ∨ v ≠ 0) : 0 < c k * kreinSquare q (t k) u v := by
      set x : Fin 2 × g → ℝ := fun p => if p.2 = k then (if p.1 = 0 then u else v) else 0
      have hx : x ≠ 0 := by
        intro h0
        rcases huv with hu | hv
        · exact hu (by simpa [x] using congrFun h0 (0, k))
        · exact hv (by simpa [x] using congrFun h0 (1, k))
      have hsum : ∑ l, c l * kreinSquare q (t l) (x (0, l)) (x (1, l)) =
          c k * kreinSquare q (t k) u v := by
        rw [Finset.sum_eq_single k]
        · simp [x]
        · intro l _ hl
          simp [x, hl, kreinSquare]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
      have := hpos x hx
      rwa [bankKrein_quad, hsum] at this
    have hc : 0 < c k := by
      have := probe 0 1 (Or.inr one_ne_zero)
      simp [kreinSquare] at this
      exact this
    refine ⟨hc, kreinSquare_pos_iff.mp fun u v huv => ?_⟩
    exact pos_of_mul_pos_right (probe u v huv) hc.le
  · intro h x hx
    rw [bankKrein_quad]
    obtain ⟨⟨a, k⟩, hk⟩ : ∃ p, x p ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (funext hall)
    have hnn : ∀ l, 0 ≤ c l * kreinSquare q (t l) (x (0, l)) (x (1, l)) := fun l => by
      rcases eq_or_ne (x (0, l)) 0 with h0 | h0
      · rcases eq_or_ne (x (1, l)) 0 with h1 | h1
        · simp [h0, h1, kreinSquare]
        · exact (mul_pos (h l).1 (kreinSquare_pos_iff.mpr (h l).2 _ _ (Or.inr h1))).le
      · exact (mul_pos (h l).1 (kreinSquare_pos_iff.mpr (h l).2 _ _ (Or.inl h0))).le
    have hkpos : 0 < c k * kreinSquare q (t k) (x (0, k)) (x (1, k)) := by
      refine mul_pos (h k).1 (kreinSquare_pos_iff.mpr (h k).2 _ _ ?_)
      fin_cases a
      · exact Or.inl hk
      · exact Or.inr hk
    calc 0 < c k * kreinSquare q (t k) (x (0, k)) (x (1, k)) := hkpos
      _ ≤ ∑ l, c l * kreinSquare q (t l) (x (0, l)) (x (1, l)) :=
        Finset.single_le_sum (fun l _ => hnn l) (Finset.mem_univ k)

/-- **A bank with distinct traces carries a count exactly when every oscillator is damped.** -/
theorem exists_positive_bornRule_bank_iff {q : ℝ} (hq : q ≠ 0) {t : g → ℝ} (ht : Function.Injective t) :
    (∃ S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ, Sᵀ = S ∧ IsBornRule S (bankDelay q t) q ∧ IsPositive S) ↔
      ∀ k, t k ^ 2 < 4 * q := by
  constructor
  · rintro ⟨S, hsym, hS, hpos⟩ k
    rw [bornRule_bank_eq hq ht hsym hS] at hpos
    exact ((bankKrein_positive_iff q t _).mp hpos k).2
  · intro h
    refine ⟨bankKrein q t fun _ => 1, ?_, bankKrein_bornRule q t _,
      (bankKrein_positive_iff q t _).mpr fun k => ⟨one_pos, h k⟩⟩
    unfold bankKrein
    rw [Matrix.blockDiagonal_transpose]
    congr 1
    funext k
    ext a b
    fin_cases a <;> fin_cases b <;> simp [kreinMatrix]

/-- Every root of every oscillator of the bank is a mode of the delay. -/
theorem bankDelay_mode {q : ℝ} {t : g → ℝ} (k : g) {z : ℂ} (hz : z ^ 2 - (t k : ℂ) * z + q = 0) :
    IsMode (bankDelay q t) z := by
  classical
  refine ⟨fun p => if p.2 = k then (if p.1 = 0 then 1 else z) else 0,
    fun h0 => by simpa using congrFun h0 (0, k), ?_⟩
  funext ⟨a, l⟩
  simp only [cplx_apply, bankDelay, Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply,
    Fintype.sum_prod_type, Pi.smul_apply, smul_eq_mul]
  by_cases hl : l = k
  · subst hl
    fin_cases a <;> simp [lpMatrix, Fin.sum_univ_two]
    linear_combination -hz
  · simp [hl]

/-! ### Repeated traces -/

/-- The Wronskian of two echo states: the antisymmetric form `J`. -/
def wronskianMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- **Two copies of one oscillator pair by the Krein square and the Wronskian.** A form covariant under
the same oscillator on both sides is `c 𝒬_t + d J`. -/
theorem block_eq_of_eq_trace {q s : ℝ} (hq : q ≠ 0) {X : Matrix (Fin 2) (Fin 2) ℝ}
    (h : (lpMatrix q s)ᵀ * X * lpMatrix q s = q • X) :
    X = X 1 1 • kreinMatrix q s + (X 0 1 + s * X 1 1 / 2) • wronskianMatrix := by
  have E (a b : Fin 2) := congrFun (congrFun h a) b
  have e00 := E 0 0
  have e01 := E 0 1
  have e10 := E 1 0
  simp [lpMatrix, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  have f00 : X 0 0 = q * X 1 1 := mul_left_cancel₀ hq (by linear_combination -e00)
  have f10 : X 1 0 = -(X 0 1 + s * X 1 1) := mul_left_cancel₀ hq (by linear_combination -e10)
  ext a b
  fin_cases a <;> fin_cases b <;> simp [kreinMatrix, wronskianMatrix] <;> linarith

/-- The Wronskian is covariant under every oscillator: `Zᵀ J Z = (det Z) J = q J`. -/
theorem wronskian_bornRule (q s : ℝ) : IsBornRule wronskianMatrix (lpMatrix q s) q := by
  unfold IsBornRule
  ext a b
  fin_cases a <;> fin_cases b <;> simp [lpMatrix, wronskianMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The quadratic form of a state supported on one oscillator is the form of its diagonal block. -/
theorem quad_single (S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ) (k : g) (u : Fin 2 → ℝ) :
    (fun p : Fin 2 × g => if p.2 = k then u p.1 else 0) ⬝ᵥ
        S *ᵥ (fun p : Fin 2 × g => if p.2 = k then u p.1 else 0) =
      u ⬝ᵥ block S k k *ᵥ u := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, block]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **A count of any bank needs every oscillator damped.** Whatever the traces, a positive symmetric
Born rule on the echo states exists exactly when every oscillator is damped. -/
theorem exists_positive_bornRule_bank_iff' {q : ℝ} (hq : q ≠ 0) (t : g → ℝ) :
    (∃ S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ, Sᵀ = S ∧ IsBornRule S (bankDelay q t) q ∧ IsPositive S) ↔
      ∀ k, t k ^ 2 < 4 * q := by
  constructor
  · rintro ⟨S, hsym, hS, hpos⟩ k
    have hblock : (lpMatrix q (t k))ᵀ * block S k k * lpMatrix q (t k) = q • block S k k := by
      ext a b
      have e := bankDelay_conj_apply q t S a b k k
      rw [hS] at e
      rw [← e]
      simp [block]
    have hs : block S k k 1 0 = block S k k 0 1 := by
      simp only [block]
      have := congrFun (congrFun hsym (0, k)) (1, k)
      rwa [Matrix.transpose_apply] at this
    have hK := block_eq_krein hq hs hblock
    set c := block S k k 1 1
    -- positivity on the states of the oscillator `k`
    have hu (u : Fin 2 → ℝ) (hu : u ≠ 0) : 0 < c * kreinSquare q (t k) (u 0) (u 1) := by
      have hx : (fun p : Fin 2 × g => if p.2 = k then u p.1 else 0) ≠ 0 := by
        intro h0
        apply hu
        funext a
        simpa using congrFun h0 (a, k)
      have := hpos _ hx
      rw [quad_single, hK] at this
      have hval : u ⬝ᵥ (c • kreinMatrix q (t k)) *ᵥ u = c * kreinSquare q (t k) (u 0) (u 1) := by
        simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, kreinMatrix, kreinSquare, Matrix.smul_apply]
        ring
      rwa [hval] at this
    have hc : 0 < c := by
      have := hu ![0, 1] (by intro h; simpa using congrFun h 1)
      simpa [kreinSquare] using this
    refine kreinSquare_pos_iff.mp fun a b hab => ?_
    have := hu ![a, b] (by
      intro h0
      rcases hab with ha | hb
      · exact ha (by simpa using congrFun h0 0)
      · exact hb (by simpa using congrFun h0 1))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact pos_of_mul_pos_right this hc.le
  · intro h
    refine ⟨bankKrein q t fun _ => 1, ?_, bankKrein_bornRule q t _,
      (bankKrein_positive_iff q t _).mpr fun k => ⟨one_pos, h k⟩⟩
    unfold bankKrein
    rw [Matrix.blockDiagonal_transpose]
    congr 1
    funext k
    ext a b
    fin_cases a <;> fin_cases b <;> simp [kreinMatrix]

/-! ### Four modes off the circle -/

/-- Multiplication by `μ ν` is the product of the two multiplications. -/
theorem mulMatrix_mul (μ ν : ℂ) : mulMatrix (μ * ν) = mulMatrix μ * mulMatrix ν := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [mulMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem mulMatrix_transpose (μ : ℂ) : (mulMatrix μ)ᵀ = mulMatrix (starRingEnd ℂ μ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [mulMatrix]

theorem mulMatrix_real (r : ℝ) : mulMatrix (r : ℂ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [mulMatrix]

/-- The delay of an off-circle quadruple `α, ᾱ, q/α, q/ᾱ`: multiplication by `α` on one plane and by
`q/ᾱ` on the other. -/
def quadrupleDelay (q : ℝ) (α : ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks (mulMatrix α) 0 0 (mulMatrix ((q : ℂ) / starRingEnd ℂ α))

/-- The hyperbolic form pairing the two planes. -/
def hyperbolicForm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ := Matrix.fromBlocks 0 1 1 0

/-- **An off-circle quadruple carries a hyperbolic Born rule.** -/
theorem hyperbolicForm_bornRule (q : ℝ) {α : ℂ} (hα : α ≠ 0) :
    IsBornRule hyperbolicForm (quadrupleDelay q α) q := by
  unfold IsBornRule quadrupleDelay hyperbolicForm
  have hα' : starRingEnd ℂ α ≠ 0 := (map_ne_zero _).mpr hα
  have h1 : (mulMatrix α)ᵀ * mulMatrix ((q : ℂ) / starRingEnd ℂ α) = q • 1 := by
    rw [mulMatrix_transpose, ← mulMatrix_mul, mul_div_cancel₀ _ hα', mulMatrix_real]
  have h2 : (mulMatrix ((q : ℂ) / starRingEnd ℂ α))ᵀ * mulMatrix α = q • 1 := by
    rw [mulMatrix_transpose, ← mulMatrix_mul, map_div₀, Complex.conj_ofReal, Complex.conj_conj,
      div_mul_cancel₀ _ hα, mulMatrix_real]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_one, h1, h2, Matrix.fromBlocks_smul, smul_zero]

/-- The hyperbolic form is nondegenerate. -/
theorem det_hyperbolicForm_ne_zero : (hyperbolicForm).det ≠ 0 := by
  have h : hyperbolicForm * hyperbolicForm = 1 := by
    unfold hyperbolicForm
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- `α` is a mode of the quadruple delay. -/
theorem quadrupleDelay_mode (q : ℝ) (α : ℂ) : IsMode (quadrupleDelay q α) α := by
  refine ⟨Sum.elim ![1, -Complex.I] 0, fun h => by simpa using congrFun h (Sum.inl 0), ?_⟩
  funext p
  rcases p with a | a <;> fin_cases a <;>
    simp [cplx_apply, quadrupleDelay, mulMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, Matrix.fromBlocks]
  all_goals apply Complex.ext <;> simp

/-- **An off-circle quadruple has the quadratic half and never the count half.** If `|α|² ≠ q`, the
quadruple delay carries a nondegenerate Born rule and no positive one. -/
theorem offCircle_quadruple {q : ℝ} {α : ℂ} (hα : α ≠ 0) (hoff : Complex.normSq α ≠ q) :
    (∃ S, S.det ≠ 0 ∧ IsBornRule S (quadrupleDelay q α) q) ∧
      ¬ ∃ S, IsBornRule S (quadrupleDelay q α) q ∧ IsPositive S :=
  ⟨⟨hyperbolicForm, det_hyperbolicForm_ne_zero, hyperbolicForm_bornRule q hα⟩,
    fun ⟨_, hS, hpos⟩ => hoff (normSq_eq_of_bornRule hS hpos (quadrupleDelay_mode q α))⟩

/-! ### Every Born rule of a bank, and the Hermitian form of a repeated oscillator -/

/-- **Every Born rule of a bank, block by block**: blocks between oscillators with different traces
vanish, and blocks between oscillators with the same trace are `c 𝒬_t + d J`. -/
theorem bornRule_bank_blocks {q : ℝ} (hq : q ≠ 0) (t : g → ℝ) {S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ}
    (h : IsBornRule S (bankDelay q t) q) (k l : g) :
    block S k l = if t k = t l then block S k l 1 1 • kreinMatrix q (t k) +
      (block S k l 0 1 + t k * block S k l 1 1 / 2) • wronskianMatrix else 0 := by
  have hblock : (lpMatrix q (t k))ᵀ * block S k l * lpMatrix q (t l) = q • block S k l := by
    ext a b
    have e := bankDelay_conj_apply q t S a b k l
    rw [h] at e
    rw [← e]
    simp [block]
  split_ifs with hkl
  · rw [← hkl] at hblock
    exact block_eq_of_eq_trace hq hblock
  · exact block_eq_zero_of_ne hq hkl hblock

/-- The complex coordinate of an echo state of a damped oscillator, `φ(u) = (u₁ − t u₀/2) + i s u₀` with
`s = √(q − t²/4)`: the Krein square is `|φ|²` and the Wronskian is `Im(φ φ̄')/s`. -/
def echoCoord (t s : ℝ) (u : Fin 2 → ℝ) : ℂ := ⟨u 1 - t * u 0 / 2, s * u 0⟩

/-- The Hermitian form of a symmetric Born rule on `m` copies of one oscillator. -/
def bornHermitian (t s : ℝ) (S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ) : Matrix g g ℂ :=
  fun k l => ⟨block S k l 1 1, (block S k l 0 1 + t * block S k l 1 1 / 2) / s⟩

/-- **A Born rule on copies of one damped oscillator is a Hermitian form.** With the complex coordinates
`z_k = φ(x_k)` of the echo states, `S(x) = Re(z* H z)`. -/
theorem quad_eq_bornHermitian {q t : ℝ} (hq : q ≠ 0) (ht : t ^ 2 < 4 * q)
    {S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ} (h : IsBornRule S (bankDelay q fun _ => t) q)
    (x : Fin 2 × g → ℝ) :
    x ⬝ᵥ S *ᵥ x = (star (fun k => echoCoord t (Real.sqrt (q - t ^ 2 / 4)) fun a => x (a, k)) ⬝ᵥ
      bornHermitian t (Real.sqrt (q - t ^ 2 / 4)) S *ᵥ
        fun k => echoCoord t (Real.sqrt (q - t ^ 2 / 4)) fun a => x (a, k)).re := by
  set s := Real.sqrt (q - t ^ 2 / 4) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hss : s ^ 2 = q - t ^ 2 / 4 := Real.sq_sqrt (by linarith)
  have hb := fun k l => bornRule_bank_blocks hq (fun _ => t) h k l
  simp only [if_true] at hb
  -- expand both sides as double sums over the oscillators
  have lhs : x ⬝ᵥ S *ᵥ x = ∑ k, ∑ l, ∑ a, ∑ b, x (a, k) * block S k l a b * x (b, l) := by
    have e1 : x ⬝ᵥ S *ᵥ x = ∑ a, ∑ k, ∑ b, ∑ l, x (a, k) * block S k l a b * x (b, l) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum, block, mul_assoc]
    rw [e1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc ∑ a, ∑ b, ∑ l, x (a, k) * block S k l a b * x (b, l)
        = ∑ a, ∑ l, ∑ b, x (a, k) * block S k l a b * x (b, l) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ l, ∑ a, ∑ b, x (a, k) * block S k l a b * x (b, l) := Finset.sum_comm
  rw [lhs]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hb k l]
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, kreinMatrix,
    wronskianMatrix, bornHermitian, echoCoord, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
  field_simp
  rw [hss]
  ring

/-- Every complex vector is the coordinate of an echo state. -/
theorem echoCoord_surjective {t s : ℝ} (hs : s ≠ 0) (z : ℂ) :
    echoCoord t s ![z.im / s, z.re + t * (z.im / s) / 2] = z := by
  apply Complex.ext
  · simp [echoCoord]
  · simp [echoCoord]
    field_simp

/-- **The positive Born rules of a repeated damped oscillator are the positive Hermitian forms.** For `m`
copies of an oscillator with `t² < 4q`, a symmetric Born rule is positive iff its Hermitian form is
positive definite. -/
theorem bornRule_positive_iff_hermitian {q t : ℝ} (hq : q ≠ 0) (ht : t ^ 2 < 4 * q)
    {S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ} (h : IsBornRule S (bankDelay q fun _ => t) q) :
    IsPositive S ↔ ∀ z : g → ℂ, z ≠ 0 →
      0 < (star z ⬝ᵥ bornHermitian t (Real.sqrt (q - t ^ 2 / 4)) S *ᵥ z).re := by
  set s := Real.sqrt (q - t ^ 2 / 4) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  -- the coordinates of a state, and the state of coordinates
  set coord : (Fin 2 × g → ℝ) → g → ℂ := fun x k => echoCoord t s fun a => x (a, k)
  set state : (g → ℂ) → Fin 2 × g → ℝ :=
    fun z p => ![(z p.2).im / s, (z p.2).re + t * ((z p.2).im / s) / 2] p.1
  have hcs (z : g → ℂ) : coord (state z) = z := by
    funext k
    have := echoCoord_surjective (t := t) hs0.ne' (z k)
    simp only [coord, state]
    convert this using 2
  have hc0 (x : Fin 2 × g → ℝ) (hx : x ≠ 0) : coord x ≠ 0 := by
    intro h0
    apply hx
    funext ⟨a, k⟩
    have hk := congrFun h0 k
    simp only [coord, echoCoord, Pi.zero_apply, Complex.ext_iff, Complex.zero_re,
      Complex.zero_im] at hk
    have h0' : x (0, k) = 0 := by
      have := hk.2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hs0.ne'
      · exact h
    fin_cases a
    · exact h0'
    · simpa [h0'] using hk.1
  constructor
  · intro hpos z hz
    have hx : state z ≠ 0 := by
      intro h0
      apply hz
      rw [← hcs z, h0]
      funext k
      simp [coord, echoCoord, Complex.ext_iff]
    have := hpos _ hx
    rwa [quad_eq_bornHermitian hq ht h, show (fun k => echoCoord t s fun a => state z (a, k)) = z from
      hcs z] at this
  · intro hH x hx
    rw [quad_eq_bornHermitian hq ht h]
    exact hH _ (hc0 x hx)

/-! ### Several repeated traces: the direct sum of the Hermitian forms -/

omit [DecidableEq g] in
/-- The quadratic form of a state, block by block. -/
theorem quad_blocks (S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ) (x : Fin 2 × g → ℝ) :
    x ⬝ᵥ S *ᵥ x = ∑ k, ∑ l, ∑ a, ∑ b, x (a, k) * block S k l a b * x (b, l) := by
  have e1 : x ⬝ᵥ S *ᵥ x = ∑ a, ∑ k, ∑ b, ∑ l, x (a, k) * block S k l a b * x (b, l) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum, block, mul_assoc]
  rw [e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ a, ∑ b, ∑ l, x (a, k) * block S k l a b * x (b, l)
      = ∑ a, ∑ l, ∑ b, x (a, k) * block S k l a b * x (b, l) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, x (a, k) * block S k l a b * x (b, l) := Finset.sum_comm

/-- The part of a state on the oscillators of trace `τ`. -/
def classPart (t : g → ℝ) (τ : ℝ) (x : Fin 2 × g → ℝ) : Fin 2 × g → ℝ :=
  fun p => if t p.2 = τ then x p else 0

/-- **A Born rule splits over the trace classes**: `S(x) = Σ_τ S(x_τ)`. -/
theorem quad_eq_sum_classes {q : ℝ} (hq : q ≠ 0) (t : g → ℝ) {S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ}
    (h : IsBornRule S (bankDelay q t) q) (x : Fin 2 × g → ℝ) :
    x ⬝ᵥ S *ᵥ x = ∑ τ ∈ Finset.univ.image t, classPart t τ x ⬝ᵥ S *ᵥ classPart t τ x := by
  classical
  simp only [quad_blocks, classPart]
  -- cross-class blocks vanish
  have hcross (k l : g) (hkl : t k ≠ t l) (a b : Fin 2) : block S k l a b = 0 := by
    rw [bornRule_bank_blocks hq t h k l, if_neg hkl]
    rfl
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : t k = t l
  · rw [Finset.sum_eq_single (t k)]
    · simp [hkl]
    · intro τ _ hτ
      simp [Ne.symm hτ]
    · intro hk
      exact absurd (Finset.mem_image_of_mem t (Finset.mem_univ k)) hk
  · rw [Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by rw [hcross k l hkl]; ring]
    symm
    refine Finset.sum_eq_zero fun τ _ => ?_
    by_cases hk : t k = τ
    · have hl : t l ≠ τ := fun hl => hkl (hk.trans hl.symm)
      simp [hl]
    · simp [hk]

/-- **On one trace class a Born rule is the Hermitian form of the class.** -/
theorem quad_class_eq_bornHermitian {q : ℝ} (hq : q ≠ 0) (t : g → ℝ) {τ : ℝ} (hτ : τ ^ 2 < 4 * q)
    {S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ} (h : IsBornRule S (bankDelay q t) q) (x : Fin 2 × g → ℝ)
    (hx : ∀ a k, t k ≠ τ → x (a, k) = 0) :
    x ⬝ᵥ S *ᵥ x = (star (fun k => echoCoord τ (Real.sqrt (q - τ ^ 2 / 4)) fun a => x (a, k)) ⬝ᵥ
      bornHermitian τ (Real.sqrt (q - τ ^ 2 / 4)) S *ᵥ
        fun k => echoCoord τ (Real.sqrt (q - τ ^ 2 / 4)) fun a => x (a, k)).re := by
  set s := Real.sqrt (q - τ ^ 2 / 4) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hss : s ^ 2 = q - τ ^ 2 / 4 := Real.sq_sqrt (by linarith)
  rw [quad_blocks]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases hk : t k = τ
  · by_cases hl : t l = τ
    · have hb := bornRule_bank_blocks hq t h k l
      rw [if_pos (hk.trans hl.symm), hk] at hb
      rw [hb]
      simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, kreinMatrix,
        wronskianMatrix, bornHermitian, echoCoord, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
      field_simp
      rw [hss]
      ring
    · simp [hx _ l hl, echoCoord]
  · simp [hx _ k hk, echoCoord]

/-- **The positive cone of a damped bank is the direct sum of the Hermitian cones of its trace
classes.** A Born rule of a bank whose oscillators are all damped is positive iff, for every trace `τ`
of the bank, its Hermitian form is positive definite on the vectors supported on the oscillators of
trace `τ`. -/
theorem bornRule_positive_iff_classes {q : ℝ} (hq : q ≠ 0) (t : g → ℝ) (ht : ∀ k, t k ^ 2 < 4 * q)
    {S : Matrix (Fin 2 × g) (Fin 2 × g) ℝ} (h : IsBornRule S (bankDelay q t) q) :
    IsPositive S ↔ ∀ k₀ : g, ∀ z : g → ℂ, z ≠ 0 → (∀ k, t k ≠ t k₀ → z k = 0) →
      0 < (star z ⬝ᵥ bornHermitian (t k₀) (Real.sqrt (q - t k₀ ^ 2 / 4)) S *ᵥ z).re := by
  classical
  -- states of coordinates, and coordinates of states, on one class
  have hstate (τ s : ℝ) (hs0 : 0 < s) (z : g → ℂ) :
      (fun k => echoCoord τ s fun a => (![(z k).im / s, (z k).re + τ * ((z k).im / s) / 2] a)) = z := by
    funext k
    have := echoCoord_surjective (t := τ) hs0.ne' (z k)
    convert this using 2
  constructor
  · intro hpos k₀ z hz hsupp
    set τ := t k₀
    set s := Real.sqrt (q - τ ^ 2 / 4)
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by have := ht k₀; linarith)
    set x : Fin 2 × g → ℝ := fun p => ![(z p.2).im / s, (z p.2).re + τ * ((z p.2).im / s) / 2] p.1
    have hxsupp : ∀ a k, t k ≠ τ → x (a, k) = 0 := by
      intro a k hk
      have hzk := hsupp k hk
      fin_cases a <;> simp [x, hzk]
    have hx0 : x ≠ 0 := by
      intro h0
      apply hz
      rw [← hstate τ s hs0 z]
      funext k
      have h1 := congrFun h0 (0, k)
      have h2 := congrFun h0 (1, k)
      simp only [x, Pi.zero_apply] at h1 h2
      simp only [Pi.zero_apply]
      apply Complex.ext <;> simp [echoCoord, h1, h2]
    have := hpos x hx0
    rw [quad_class_eq_bornHermitian hq t (ht k₀) h x hxsupp] at this
    rwa [show (fun k => echoCoord τ s fun a => x (a, k)) = z from hstate τ s hs0 z] at this
  · intro hH x hx
    rw [quad_eq_sum_classes hq t h]
    -- each class contributes a nonnegative amount, and some class a positive one
    have hclass (k₀ : g) : 0 ≤ classPart t (t k₀) x ⬝ᵥ S *ᵥ classPart t (t k₀) x ∧
        (classPart t (t k₀) x ≠ 0 → 0 < classPart t (t k₀) x ⬝ᵥ S *ᵥ classPart t (t k₀) x) := by
      set τ := t k₀
      set s := Real.sqrt (q - τ ^ 2 / 4)
      have hs0 : 0 < s := Real.sqrt_pos.mpr (by have := ht k₀; linarith)
      have hsupp : ∀ a k, t k ≠ τ → classPart t τ x (a, k) = 0 := fun a k hk => by
        simp [classPart, hk]
      rw [quad_class_eq_bornHermitian hq t (ht k₀) h _ hsupp]
      set z : g → ℂ := fun k => echoCoord τ s fun a => classPart t τ x (a, k)
      have hzsupp : ∀ k, t k ≠ τ → z k = 0 := fun k hk => by
        simp only [z]
        rw [show (fun a => classPart t τ x (a, k)) = 0 from funext fun a => hsupp a k hk]
        simp [echoCoord, Complex.ext_iff]
      by_cases hz : z = 0
      · have hx0 : classPart t τ x = 0 := by
          funext ⟨a, k⟩
          have hk := congrFun hz k
          simp only [z, Pi.zero_apply, echoCoord, Complex.ext_iff, Complex.zero_re,
            Complex.zero_im] at hk
          have h0 : classPart t τ x (0, k) = 0 := by
            rcases mul_eq_zero.mp hk.2 with h | h
            · exact absurd h hs0.ne'
            · exact h
          fin_cases a
          · exact h0
          · simpa [h0] using hk.1
        refine ⟨by rw [hz]; simp, fun hne => absurd hx0 hne⟩
      · have := hH k₀ z hz hzsupp
        exact ⟨this.le, fun _ => this⟩
    obtain ⟨⟨a₀, k₀⟩, hk₀⟩ : ∃ p, x p ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (funext hall)
    have hne : classPart t (t k₀) x ≠ 0 := fun h0 => hk₀ (by
      have := congrFun h0 (a₀, k₀)
      simpa [classPart] using this)
    have hmem : t k₀ ∈ Finset.univ.image t := Finset.mem_image_of_mem t (Finset.mem_univ k₀)
    rw [← Finset.add_sum_erase _ _ hmem]
    have hrest : 0 ≤ ∑ τ ∈ (Finset.univ.image t).erase (t k₀),
        classPart t τ x ⬝ᵥ S *ᵥ classPart t τ x := by
      refine Finset.sum_nonneg fun τ hτ => ?_
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hτ)
      exact (hclass k).1
    linarith [(hclass k₀).2 hne]

end GaloisForLFunctions.CountingHolography

end
