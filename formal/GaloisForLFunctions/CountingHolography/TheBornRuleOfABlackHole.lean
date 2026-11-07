import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.ArithmeticScatteringHolography.TheThroatOfABlackHole
import GaloisForLFunctions.ArithmeticScatteringHolography.TheLaxPhillipsSemigroup

/-!
# The Born rule of a black hole

A count law has two halves: it is **quadratic** (the parallelogram law) and it is a **count**
(nonnegative). A count of probes must also respect the dynamics: one double tick of the ringdown, the
delay `π`, multiplies the number of channels of every probe by `q`. Call a quadratic form `S` on the
states of a black hole a **Born rule** for the delay `M` if `Mᵀ S M = q S`.

* **The quadratic half is the partner law.** If a Born rule is nondegenerate, the modes come in
  partners: with `α` also `q/α` is a mode (`partner_of_bornRule`), and `(det M)² = q^d`
  (`det_sq_of_bornRule`). So a black hole without the functional equation has no Born rule: a throat
  with edge index `b ≠ 2` has none (`throat_no_bornRule`), although it has flux and unitarity.
* **The count half is universal damping.** If a Born rule is positive, every mode has `|α|² = q`
  (`normSq_eq_of_bornRule`): a positive conserved quadratic quantity of the normalized ringdown forces
  every mode onto the universal circle.
* **At genus one the Born rule is unique.** On the probes `y - x π` the delay is
  `(x, y) ↦ (t x - y, q x)`, and every covariant count law is `K(1) · 𝒬` (`countLaw_covariant_eq`). A
  count of the probes that is quadratic, covariant and counts the trivial probe once exists exactly
  under universal damping (`exists_covariantCountLaw_iff`). The channel numbers are not needed: the
  dynamics fixes the law up to one constant.
* **The fake keeps the count and loses the law.** The count `|𝒬|` of a fake is covariant
  (`probeCount_covariant`) and is a count; it is not quadratic.

So the physical origin of the parallelogram law is the delay: covariance determines the quadratic count
and requires the functional equation, and the count property is the sign.
-/

open Matrix Finset

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Born rules -/

/-- The complexification of a real matrix. -/
def cplx (M : Matrix d d ℝ) : Matrix d d ℂ := Complex.ofRealHom.mapMatrix M

theorem cplx_apply (M : Matrix d d ℝ) (i j : d) : cplx M i j = (M i j : ℂ) := rfl

theorem cplx_det (M : Matrix d d ℝ) : (cplx M).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

/-- `α` is a mode of the delay `M`: an eigenvalue of its complexification. -/
def IsMode (M : Matrix d d ℝ) (α : ℂ) : Prop := ∃ v : d → ℂ, v ≠ 0 ∧ cplx M *ᵥ v = α • v

/-- A **Born rule** for the delay `M` at ratio `q`: one tick multiplies the form by `q`. -/
def IsBornRule (S M : Matrix d d ℝ) (q : ℝ) : Prop := Mᵀ * S * M = q • S

theorem cplx_bornRule {S M : Matrix d d ℝ} {q : ℝ} (h : IsBornRule S M q) :
    (cplx M)ᵀ * cplx S * cplx M = (q : ℂ) • cplx S := by
  have e := congrArg cplx h
  have ht : cplx Mᵀ = (cplx M)ᵀ := by ext i j; rfl
  have hs : cplx (q • S) = (q : ℂ) • cplx S := by ext i j; simp [cplx_apply]
  unfold cplx at e ht hs ⊢
  rw [map_mul, map_mul, ht, hs] at e
  exact e

/-- **A nondegenerate Born rule fixes the determinant**: `(det M)² = q^d`. -/
theorem det_sq_of_bornRule {S M : Matrix d d ℝ} {q : ℝ} (h : IsBornRule S M q) (hS : S.det ≠ 0) :
    M.det ^ 2 = q ^ Fintype.card d := by
  have e := congrArg Matrix.det h
  rw [det_mul, det_mul, det_transpose, det_smul] at e
  have e' : (M.det ^ 2 - q ^ Fintype.card d) * S.det = 0 := by linear_combination e
  rcases mul_eq_zero.mp e' with h0 | h0
  · linear_combination h0
  · exact absurd h0 hS

/-- **The quadratic half is the partner law.** If the delay has a nondegenerate Born rule, every mode
`α` is nonzero and `q/α` is a mode as well. -/
theorem partner_of_bornRule {S M : Matrix d d ℝ} {q : ℝ} (h : IsBornRule S M q) (hS : S.det ≠ 0)
    (hq : q ≠ 0) {α : ℂ} (hα : IsMode M α) : α ≠ 0 ∧ IsMode M ((q : ℂ) / α) := by
  obtain ⟨v, hv0, hv⟩ := hα
  have hne : Nonempty d := by
    by_contra hd
    rw [not_nonempty_iff] at hd
    exact hv0 (Subsingleton.elim _ _)
  have hdetM : M.det ≠ 0 := by
    intro h0
    have e := det_sq_of_bornRule h hS
    rw [h0, zero_pow two_ne_zero] at e
    exact hq ((pow_eq_zero_iff Fintype.card_ne_zero).mp e.symm)
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply hdetM
    have : (cplx M).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, by rw [hv, zero_smul]⟩
    rw [cplx_det] at this
    exact_mod_cast this
  refine ⟨hα0, ?_⟩
  set w := cplx S *ᵥ v with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have : (cplx S).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, h0⟩
    rw [cplx_det] at this
    exact hS (by exact_mod_cast this)
  have h1 : ((cplx M)ᵀ * cplx S * cplx M) *ᵥ v = ((q : ℂ) • cplx S) *ᵥ v := by rw [cplx_bornRule h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.smul_mulVec] at h1
  have hkey : (cplx M)ᵀ *ᵥ w = ((q : ℂ) / α) • w := by
    calc (cplx M)ᵀ *ᵥ w = α⁻¹ • (α • ((cplx M)ᵀ *ᵥ w)) := by
          rw [smul_smul, inv_mul_cancel₀ hα0, one_smul]
      _ = ((q : ℂ) / α) • w := by rw [hw, h1, smul_smul, div_eq_inv_mul]
  have hdet : (((q : ℂ) / α) • (1 : Matrix d d ℂ) - (cplx M)ᵀ).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hkey, sub_self]
  have hdet' : (((q : ℂ) / α) • (1 : Matrix d d ℂ) - cplx M).det = 0 := by
    rw [← Matrix.det_transpose, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
    exact hdet
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
  refine ⟨u, hu0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hu
  exact hu.symm

/-! ### Positive Born rules -/

/-- The form is positive on every nonzero real state. -/
def IsPositive (S : Matrix d d ℝ) : Prop := ∀ x : d → ℝ, x ≠ 0 → 0 < x ⬝ᵥ S *ᵥ x

omit [DecidableEq d] in
/-- One tick multiplies the count of every state by `q`. -/
theorem quad_of_bornRule {S M : Matrix d d ℝ} {q : ℝ} (h : IsBornRule S M q) (x : d → ℝ) :
    (M *ᵥ x) ⬝ᵥ S *ᵥ (M *ᵥ x) = q * (x ⬝ᵥ S *ᵥ x) := by
  have e : x ⬝ᵥ (Mᵀ * S * M) *ᵥ x = x ⬝ᵥ (q • S) *ᵥ x := by rw [h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at e
  exact e

/-- The real and imaginary parts of a mode vector rotate under the delay. -/
theorem mulVec_re_im {M : Matrix d d ℝ} {α : ℂ} {v : d → ℂ} (hv : cplx M *ᵥ v = α • v) :
    M *ᵥ (fun i => (v i).re) = α.re • (fun i => (v i).re) - α.im • (fun i => (v i).im) ∧
      M *ᵥ (fun i => (v i).im) = α.im • (fun i => (v i).re) + α.re • (fun i => (v i).im) := by
  constructor <;> funext i <;> have e := congrFun hv i
  · have e' := congrArg Complex.re e
    simp only [Matrix.mulVec, dotProduct, cplx_apply, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re] at e'
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e']
  · have e' := congrArg Complex.im e
    simp only [Matrix.mulVec, dotProduct, cplx_apply, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Pi.smul_apply, smul_eq_mul,
      Complex.mul_im] at e'
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e']
    ring

/-- **The count half is universal damping.** If the delay has a positive Born rule, every mode lies on
the universal circle `|α|² = q`. -/
theorem normSq_eq_of_bornRule {S M : Matrix d d ℝ} {q : ℝ} (h : IsBornRule S M q)
    (hpos : IsPositive S) {α : ℂ} (hα : IsMode M α) : Complex.normSq α = q := by
  obtain ⟨v, hv0, hv⟩ := hα
  obtain ⟨ha, hb⟩ := mulVec_re_im hv
  set a : d → ℝ := fun i => (v i).re
  set b : d → ℝ := fun i => (v i).im
  have hR0 (x : d → ℝ) : 0 ≤ x ⬝ᵥ S *ᵥ x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  have hab : 0 < a ⬝ᵥ S *ᵥ a + b ⬝ᵥ S *ᵥ b := by
    by_cases hA : a = 0
    · have hB : b ≠ 0 := by
        intro hB
        apply hv0
        funext i
        apply Complex.ext
        · exact congrFun hA i
        · exact congrFun hB i
      linarith [hpos b hB, hR0 a]
    · linarith [hpos a hA, hR0 b]
  have hsum : (M *ᵥ a) ⬝ᵥ S *ᵥ (M *ᵥ a) + (M *ᵥ b) ⬝ᵥ S *ᵥ (M *ᵥ b) =
      Complex.normSq α * (a ⬝ᵥ S *ᵥ a + b ⬝ᵥ S *ᵥ b) := by
    rw [ha, hb]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_sub,
      dotProduct_add, sub_dotProduct, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      Complex.normSq_apply]
    ring
  rw [quad_of_bornRule h a, quad_of_bornRule h b] at hsum
  have : (Complex.normSq α - q) * (a ⬝ᵥ S *ᵥ a + b ⬝ᵥ S *ᵥ b) = 0 := by linear_combination -hsum
  rcases mul_eq_zero.mp this with h0 | h0
  · linarith
  · linarith

/-! ### Genus one: the Born rule is unique -/

/-- The delay acts on the probe `y - x π` by `π (y - x π) = q x - (t x - y) π`. -/
def IsCovariant (q t : ℤ) (K : ℤ → ℤ → ℕ) : Prop :=
  ∀ x y, (K (t * x - y) (q * x) : ℤ) = q * K x y

/-- The Krein square is covariant under the delay. -/
theorem kreinSquare_delay (q t x y : ℤ) :
    kreinSquare q t (t * x - y) (q * x) = q * kreinSquare q t x y := by
  unfold kreinSquare
  ring

/-- **The Born rule at genus one is unique.** A covariant count law is `K(1)` times the Krein square. -/
theorem countLaw_covariant_eq {q t : ℤ} (hq : q ≠ 0) {K : ℤ → ℤ → ℕ} (hK : CountLaw K)
    (hcov : IsCovariant q t K) (x y : ℤ) : (K x y : ℤ) = K 0 1 * kreinSquare q t x y := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = K 0 1 := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B : ℤ, B = K 1 0 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C = K 1 1 := ⟨_, rfl⟩
  have hform (x y : ℤ) : (K x y : ℤ) = A * y ^ 2 + (C - A - B) * x * y + B * x ^ 2 := by
    rw [hA, hB', hC]
    exact countLaw_eq_form hK x y
  have h01 := hcov 0 1
  have h10 := hcov 1 0
  have h11 := hcov 1 1
  simp only [hform] at h01 h10 h11
  -- the instance at `1` gives `K(π) = q K(1)`; those at `π` and `1 - π` fix the cross term
  have hB : B = q * A := by linear_combination h01
  have e1 : q * t * (C - A - B + A * t) = 0 := by linear_combination h10 - (t ^ 2 - q) * hB
  have e2 : q * (t - 2) * (C - A - B + A * t) = 0 := by
    linear_combination h11 - ((t - 1) ^ 2 - q) * hB
  have e3 : (2 * q) * (C - A - B + A * t) = 0 := by linear_combination e1 - e2
  have hD : C - A - B + A * t = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (by linarith : q = 0) hq
    · exact h
  rw [hform x y, ← hA]
  unfold kreinSquare
  linear_combination (x * y) * hD + x ^ 2 * hB

/-- **A covariant count of the probes exists exactly under universal damping.** It must be quadratic,
covariant under the delay, and count the trivial probe once. -/
theorem exists_covariantCountLaw_iff {q t : ℤ} (hq : 0 < q) :
    (∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ IsCovariant q t K ∧ K 0 1 = 1) ↔ t ^ 2 ≤ 4 * q := by
  rw [← kreinSquare_int_nonneg_iff]
  constructor
  · rintro ⟨K, hK, hcov, h1⟩ x y
    have := countLaw_covariant_eq hq.ne' hK hcov x y
    rw [h1, Nat.cast_one, one_mul] at this
    rw [← this]
    positivity
  · intro hn
    have hc (x y : ℤ) : ((kreinSquare q t x y).natAbs : ℤ) = kreinSquare q t x y :=
      Int.natAbs_of_nonneg (hn x y)
    refine ⟨fun x y => (kreinSquare q t x y).natAbs, fun x y u v => ?_, fun x y => ?_, ?_⟩
    · simp only [hc]
      unfold kreinSquare
      ring
    · simp only [hc]
      exact kreinSquare_delay q t x y
    · simp [kreinSquare]

/-- **The count of a fake is covariant.** `|𝒬|` is multiplied by `q` under the delay on every black hole,
true or fake. -/
theorem probeCount_covariant {q : ℤ} (hq : 0 ≤ q) (t : ℤ) : IsCovariant q t (probeCount q t) := by
  intro x y
  simp only [probeCount, kreinSquare_delay, Int.natCast_natAbs, abs_mul, abs_of_nonneg hq]

/-! ### The throat has no Born rule -/

/-- The echo state of the throat: the companion of `throatPoly`, with the modes multiplying to
`(b - 1) q`. -/
def throatEcho (q a b : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  lpMatrix (((b : ℝ) - 1) * q) (1 + ((b : ℝ) - 1) * q - a * b)

/-- The echo state of the throat is the companion of its polynomial of modes. -/
theorem throatPoly_eq_charpoly (q a b : ℕ) (z : ℂ) :
    throatPoly q a b z = z ^ 2 - ((1 + ((b : ℝ) - 1) * q - a * b : ℝ) : ℂ) * z +
      ((((b : ℝ) - 1) * q : ℝ) : ℂ) := by
  unfold throatPoly throatTrace
  push_cast
  ring

/-- **No Born rule without the functional equation.** For `1 ≤ b` and `1 ≤ q`, the echo state of a throat
carries a nondegenerate Born rule only if `b = 2`, the case of the functional equation. -/
theorem throat_no_bornRule {q a b : ℕ} (hq : 1 ≤ q) (hb : 1 ≤ b) {S : Matrix (Fin 2) (Fin 2) ℝ}
    (hS : S.det ≠ 0) (h : IsBornRule S (throatEcho q a b) q) : b = 2 := by
  have e := det_sq_of_bornRule h hS
  rw [throatEcho, lpMatrix_det, Fintype.card_fin] at e
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have e' : (q : ℝ) ^ 2 * (((b : ℝ) - 1) ^ 2 - 1) = 0 := by linear_combination e
  rcases mul_eq_zero.mp e' with h0 | h0
  · nlinarith
  · have : ((b : ℝ) - 2) * (b : ℝ) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h1 | h1
    · have : (b : ℝ) = 2 := by linarith
      exact_mod_cast this
    · linarith

end GaloisForLFunctions.CountingHolography

end
