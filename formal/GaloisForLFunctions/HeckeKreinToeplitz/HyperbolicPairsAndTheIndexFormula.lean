import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Order.Chebyshev

/-!
# Hyperbolic pairs and the Krein–Langer index formula

A **character** of a group `G` is a homomorphism `χ : G →* ℂ` (multiplicative monoid of `ℂ`); its
**reflection** is `χ†(u) = conj χ(u⁻¹)`, so `χ† = χ` iff `χ` is unitary. For `G = ℚ_{>0}` and
`χ(u) = u^{ρ−1/2}` the reflection is the character of `1 − ρ̄`. A **hyperbolic pair kernel** is the
Hermitian kernel `h_{χ,ω} = ωχ + ω̄χ†`.

**Hyperbolic plane law** (`hermQuad_gram_pairKernel`). The Toeplitz form of `h_{χ,ω}` is
`2 Re(ω A(c) conj B(c))`, with `A(c) = Σ c_a χ(x_a)` and `B(c) = Σ c_a χ†(x_a)`. For unitary `χ` the
two functionals agree and the form is `2 Re ω |A|²` (`hermQuad_gram_pairKernel_of_unitary`).

**Index formula** (`negIndex_add_sum_pairKernel_eq`). Let `p` be positive definite and
`k = p + Σ_{j<κ} h_{χ_j,ω_j}` with `ω_j ≠ 0`. Then

* `κ(k) ≤ κ` always (`negIndex_add_sum_pairKernel_le`): on the common kernel of the `κ` functionals
  `A_j` every pair term vanishes and `p` is nonnegative;
* `κ(k) = κ` as soon as one element `u` **separates** the pairs: every `|χ_j(u)| ≠ 1` and the `2κ`
  values `χ_j(u), χ_j†(u)` are distinct.

The lower bound is a growth argument. Orient each pair so that `|w_j| > 1`, `w_j = χ_j(u)`. On the
family `u^d, u^{N+d}` (`d < 2κ`) take coefficient vectors `c = X^N E − F` whose polynomials `E, F`
interpolate unit data at the `2κ` nodes through the inverse Vandermonde matrix: `E(w_j) = a_j θ_j`,
`E(w_j†) = 0`, `F(w_j) = 0`, `F(w_j†) = a_j`, with a unimodular phase `θ_j`. Then
`A_j = w_j^N a_j θ_j`, `B_j = −a_j`, and the pair terms sum to `−2 Σ_j |ω_j| |w_j|^N |a_j|²`, while the
positive part is at most `p(1) (Σ|c|)²`, bounded independently of `N`. For large `N` the form is
negative definite on a `κ`-dimensional space. A positive-definite part never pays a pair.
-/

open Complex Matrix Finset Filter
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality (IsPosDefOnGroup)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-! ### Characters and their reflection -/

theorem map_inv_eq_inv (χ : G →* ℂ) (u : G) : χ u⁻¹ = (χ u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

theorem map_ne_zero (χ : G →* ℂ) (u : G) : χ u ≠ 0 := fun h => by
  have := congrArg χ (mul_inv_cancel u)
  rw [map_mul, h, zero_mul, map_one] at this
  exact zero_ne_one this

/-- The reflection `χ†(u) = conj χ(u⁻¹)` of a character. -/
def reflectChar (χ : G →* ℂ) : G →* ℂ where
  toFun u := conj (χ u⁻¹)
  map_one' := by simp
  map_mul' u v := by rw [_root_.mul_inv_rev, map_mul, map_mul, mul_comm]

theorem reflectChar_apply (χ : G →* ℂ) (u : G) : reflectChar χ u = conj (χ u⁻¹) := rfl

theorem reflectChar_inv (χ : G →* ℂ) (u : G) : reflectChar χ u⁻¹ = conj (χ u) := by
  rw [reflectChar_apply, inv_inv]

theorem conj_reflectChar (χ : G →* ℂ) (u : G) : conj (reflectChar χ u) = χ u⁻¹ := by
  rw [reflectChar_apply, conj_conj]

theorem reflectChar_reflectChar (χ : G →* ℂ) : reflectChar (reflectChar χ) = χ := by
  ext u
  rw [reflectChar_apply, reflectChar_inv, conj_conj]

theorem norm_reflectChar (χ : G →* ℂ) (u : G) : ‖reflectChar χ u‖ = ‖χ u‖⁻¹ := by
  rw [reflectChar_apply, norm_conj, map_inv_eq_inv, norm_inv]

/-- A unitary character: every value has modulus one. -/
def IsUnitaryChar (χ : G →* ℂ) : Prop := ∀ u, ‖χ u‖ = 1

theorem reflectChar_eq_of_unitary {χ : G →* ℂ} (hχ : IsUnitaryChar χ) : reflectChar χ = χ := by
  ext u
  have h1 : χ u * conj (χ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ u]; norm_num
  rw [reflectChar_apply, map_inv_eq_inv, map_inv₀]
  exact inv_eq_of_mul_eq_one_left h1

/-! ### Hyperbolic pair kernels -/

/-- The hyperbolic pair kernel `ωχ + ω̄χ†`. -/
def pairKernel (χ : G →* ℂ) (ω : ℂ) (u : G) : ℂ := ω * χ u + conj ω * reflectChar χ u

theorem isHermKernel_pairKernel (χ : G →* ℂ) (ω : ℂ) : IsHermKernel (pairKernel χ ω) := fun u => by
  simp only [pairKernel, map_add, map_mul, conj_conj, reflectChar_inv, conj_reflectChar]
  ring

/-- A pair kernel is symmetric in the pair: `h_{χ†, ω̄} = h_{χ, ω}`. -/
theorem pairKernel_reflectChar (χ : G →* ℂ) (ω : ℂ) :
    pairKernel (reflectChar χ) (conj ω) = pairKernel χ ω := by
  ext u
  simp only [pairKernel, reflectChar_reflectChar, conj_conj]
  ring

/-- The evaluation functional `c ↦ Σ c_a χ(x_a)`. -/
def charEval (χ : G →* ℂ) {ι : Type*} [Fintype ι] (x : ι → G) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun c := ∑ a, c a * χ (x a)
  map_add' c d := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' t c := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

theorem charEval_apply (χ : G →* ℂ) {ι : Type*} [Fintype ι] (x : ι → G) (c : ι → ℂ) :
    charEval χ x c = ∑ a, c a * χ (x a) := rfl

variable {ι : Type*} [Fintype ι]

/-- The Toeplitz sum of a pair kernel factors through the two evaluation functionals. -/
theorem toeplitzSum_pairKernel (χ : G →* ℂ) (ω : ℂ) (x : ι → G) (c : ι → ℂ) :
    ∑ a, ∑ b, conj (c a) * pairKernel χ ω ((x a)⁻¹ * x b) * c b =
      ω * conj (charEval (reflectChar χ) x c) * charEval χ x c +
        conj ω * conj (charEval χ x c) * charEval (reflectChar χ) x c := by
  have key : ∀ a b, conj (c a) * pairKernel χ ω ((x a)⁻¹ * x b) * c b =
      ω * (conj (c a * reflectChar χ (x a)) * (c b * χ (x b))) +
        conj ω * (conj (c a * χ (x a)) * (c b * reflectChar χ (x b))) := fun a b => by
    simp only [pairKernel, map_mul, conj_reflectChar, reflectChar_inv]
    ring
  simp only [key, sum_add_distrib, ← mul_sum, ← sum_mul, charEval_apply, map_sum]
  ring

/-- **Hyperbolic plane law.** The Toeplitz form of `ωχ + ω̄χ†` is `2 Re(ω A conj B)`. -/
theorem hermQuad_gram_pairKernel (χ : G →* ℂ) (ω : ℂ) (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (pairKernel χ ω) x) c =
      2 * (ω * charEval χ x c * conj (charEval (reflectChar χ) x c)).re := by
  rw [hermQuad_gram, toeplitzSum_pairKernel]
  have : conj ω * conj (charEval χ x c) * charEval (reflectChar χ) x c =
      conj (ω * charEval χ x c * conj (charEval (reflectChar χ) x c)) := by
    simp only [map_mul, conj_conj]
  rw [this, Complex.add_re, Complex.conj_re]
  ring_nf

/-- For a unitary character the pair kernel is `2 Re ω` times a positive-definite kernel. -/
theorem hermQuad_gram_pairKernel_of_unitary {χ : G →* ℂ} (hχ : IsUnitaryChar χ) (ω : ℂ)
    (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (pairKernel χ ω) x) c = 2 * ω.re * Complex.normSq (charEval χ x c) := by
  rw [hermQuad_gram_pairKernel, reflectChar_eq_of_unitary hχ, mul_assoc, Complex.mul_conj,
    Complex.re_mul_ofReal]
  ring

/-! ### The upper bound -/

omit [Fintype ι] in
theorem gram_sum {J : Type*} (s : Finset J) (k : J → G → ℂ) (x : ι → G) :
    gram (fun u => ∑ j ∈ s, k j u) x = ∑ j ∈ s, gram (k j) x := by
  ext a b
  simp only [gram, Matrix.sum_apply]

theorem hermQuad_gram_sum {J : Type*} (s : Finset J) (k : J → G → ℂ) (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (fun u => ∑ j ∈ s, k j u) x) c = ∑ j ∈ s, hermQuad (gram (k j) x) c := by
  rw [gram_sum]
  simp only [hermQuad, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

/-- **Upper half of the index formula.** A positive-definite kernel plus `κ` hyperbolic pairs has
at most `κ` negative squares. -/
theorem negIndex_add_sum_pairKernel_le {J : Type*} [Fintype J] {p : G → ℂ}
    (hp : IsPosDefOnGroup p) (χ : J → G →* ℂ) (ω : J → ℂ) :
    negIndex (fun u => p u + ∑ j, pairKernel (χ j) (ω j) u) ≤ Fintype.card J := by
  have hp0 := negIndex_eq_zero_iff.mp
    ((isPosDefOnGroup_iff_negIndex_eq_zero (isHermKernel_of_isPosDefOnGroup hp)).mp hp)
  rw [negIndex_le_iff]
  intro n x
  refine Nat.cast_le.mpr (ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
    (fun j => charEval (χ j) x) fun c hc => ?_)
  rw [hermQuad_gram_add, hermQuad_gram_sum]
  have : ∀ j ∈ (univ : Finset J), hermQuad (gram (pairKernel (χ j) (ω j)) x) c = 0 := fun j _ => by
    rw [hermQuad_gram_pairKernel, hc j]; simp
  rw [sum_congr rfl this, sum_const_zero, add_zero]
  exact hp0 n x c

/-! ### The lower bound -/

section LowerBound

variable {J : Type*} [Fintype J]

/-- A linear map on which the form is negative definite gives that many negative squares. -/
theorem card_le_hermNegIndex_of_forall_neg (H : Matrix ι ι ℂ) (L : (J → ℂ) →ₗ[ℂ] (ι → ℂ))
    (h : ∀ a, a ≠ 0 → hermQuad H (L a) < 0) : Fintype.card J ≤ hermNegIndex H := by
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    by_contra ha0
    have := h a ha0
    rw [LinearMap.mem_ker.mp ha] at this
    simp [hermQuad] at this
  have hpos : IsPosDefOn (-H) (LinearMap.range L) := by
    rintro y ⟨a, rfl⟩ hy
    have ha : a ≠ 0 := by rintro rfl; exact hy (map_zero L)
    rw [hermQuad_neg]
    linarith [h a ha]
  have := finrank_le_posIndex hpos
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at this
  exact this

/-- A positive-definite kernel has Toeplitz form at most `p(1) (Σ|c_a|)²`. -/
theorem hermQuad_gram_le_of_isPosDef {p : G → ℂ} (hp : IsPosDefOnGroup p) (x : ι → G)
    (c : ι → ℂ) : hermQuad (gram p x) c ≤ (p 1).re * (∑ a, ‖c a‖) ^ 2 := by
  obtain ⟨r, hr, h1⟩ := hp.map_one_eq
  have hb : ∀ g, ‖p g‖ ≤ r := fun g => by
    have h := hp.normSq_le g
    rw [h1, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero).mp h
  rw [hermQuad_gram, h1, Complex.ofReal_re]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  calc ∑ a, ‖∑ b, conj (c a) * p ((x a)⁻¹ * x b) * c b‖
      ≤ ∑ a, ∑ b, ‖c a‖ * r * ‖c b‖ := by
        refine sum_le_sum fun a _ => (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        gcongr
        exact hb _
    _ = r * (∑ a, ‖c a‖) ^ 2 := by
        rw [sq, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun b _ => ?_
        ring

variable {κ : ℕ}

/-- The `2κ` interpolation nodes: the values at `u` of the characters and of their reflections. -/
def nodes (χ : Fin κ → G →* ℂ) (u : G) : Fin κ ⊕ Fin κ → ℂ :=
  Sum.elim (fun j => χ j u) fun j => reflectChar (χ j) u

/-- The Vandermonde matrix of the nodes. -/
def nodeVdm (χ : Fin κ → G →* ℂ) (u : G) : Matrix (Fin (κ + κ)) (Fin (κ + κ)) ℂ :=
  vandermonde (nodes χ u ∘ finSumFinEquiv.symm)

/-- **Interpolation at the nodes.** The columns of the inverse Vandermonde matrix are the
polynomials vanishing at all nodes but one, where they take the value one. -/
theorem sum_pow_mul_nodeVdm_inv {χ : Fin κ → G →* ℂ} {u : G}
    (hsep : Function.Injective (nodes χ u)) (m m' : Fin κ ⊕ Fin κ) :
    ∑ d : Fin (κ + κ), nodes χ u m ^ (d : ℕ) * (nodeVdm χ u)⁻¹ d (finSumFinEquiv m') =
      if m = m' then 1 else 0 := by
  have hdet : (nodeVdm χ u).det ≠ 0 :=
    det_vandermonde_ne_zero_iff.mpr (hsep.comp finSumFinEquiv.symm.injective)
  have h1 := congrFun₂ (mul_nonsing_inv (nodeVdm χ u) (isUnit_iff_ne_zero.mpr hdet))
    (finSumFinEquiv m) (finSumFinEquiv m')
  simp only [Matrix.mul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq] at h1
  rw [← h1]
  refine sum_congr rfl fun d _ => ?_
  simp [nodeVdm, vandermonde_apply]

/-- The unimodular phase that aligns the leading term of the `j`-th pair. -/
def phase (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (u : G) (N : ℕ) (j : Fin κ) : ℂ :=
  conj (χ j u) ^ N * conj (ω j) / ((‖χ j u‖ ^ N * ‖ω j‖ : ℝ) : ℂ)

theorem norm_phase {χ : Fin κ → G →* ℂ} {ω : Fin κ → ℂ} (hω : ∀ j, ω j ≠ 0) (u : G) (N : ℕ)
    (j : Fin κ) : ‖phase χ ω u N j‖ = 1 := by
  have h1 : ‖χ j u‖ ≠ 0 := norm_ne_zero_iff.mpr (map_ne_zero _ _)
  have h2 : ‖ω j‖ ≠ 0 := norm_ne_zero_iff.mpr (hω j)
  rw [phase, norm_div, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_conj, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

theorem mul_pow_mul_phase {χ : Fin κ → G →* ℂ} {ω : Fin κ → ℂ} (hω : ∀ j, ω j ≠ 0) (u : G)
    (N : ℕ) (j : Fin κ) :
    ω j * (χ j u ^ N * phase χ ω u N j) = ((‖ω j‖ * ‖χ j u‖ ^ N : ℝ) : ℂ) := by
  have h1 : ‖χ j u‖ ≠ 0 := norm_ne_zero_iff.mpr (map_ne_zero _ _)
  have h2 : ‖ω j‖ ≠ 0 := norm_ne_zero_iff.mpr (hω j)
  have e1 : ω j * conj (ω j) = ((‖ω j‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : χ j u ^ N * conj (χ j u) ^ N = (((‖χ j u‖ ^ 2) ^ N : ℝ) : ℂ) := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [phase, show ω j * (χ j u ^ N * (conj (χ j u) ^ N * conj (ω j) /
      ((‖χ j u‖ ^ N * ‖ω j‖ : ℝ) : ℂ))) = (ω j * conj (ω j)) * (χ j u ^ N * conj (χ j u) ^ N) /
      ((‖χ j u‖ ^ N * ‖ω j‖ : ℝ) : ℂ) by ring, e1, e2]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_div]
  congr 1
  field_simp
  ring

/-- The test family `u^d`, `u^{N+d}`, `d < 2κ`. -/
def testFamily (u : G) (N : ℕ) : Fin (κ + κ) ⊕ Fin (κ + κ) → G :=
  Sum.elim (fun d => u ^ (d : ℕ)) fun d => u ^ (N + d)

/-- The coefficient matrix of the test vectors `X^N E − F`. -/
def testMatrix (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (u : G) (N : ℕ) :
    Matrix (Fin (κ + κ) ⊕ Fin (κ + κ)) (Fin κ) ℂ :=
  fun s j => Sum.elim (fun d => -(nodeVdm χ u)⁻¹ d (finSumFinEquiv (Sum.inr j)))
    (fun d => (nodeVdm χ u)⁻¹ d (finSumFinEquiv (Sum.inl j)) * phase χ ω u N j) s

/-- Evaluation commutes with a coefficient matrix. -/
theorem charEval_mulVec (ψ : G →* ℂ) {J : Type*} [Fintype J] (x : ι → G) (M : Matrix ι J ℂ)
    (a : J → ℂ) : charEval ψ x (M *ᵥ a) = ∑ j, a j * charEval ψ x (fun s => M s j) := by
  simp only [charEval_apply, mulVec, dotProduct, sum_mul, mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun s _ => by ring

/-- Evaluation of the `j`-th test vector `X^N E_j − F_j` at a character, through `z = ψ(u)`. -/
theorem charEval_testColumn (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (u : G) (N : ℕ)
    (ψ : G →* ℂ) (j : Fin κ) :
    charEval ψ (testFamily u N) (fun s => testMatrix χ ω u N s j) =
      -(∑ d : Fin (κ + κ), ψ u ^ (d : ℕ) * (nodeVdm χ u)⁻¹ d (finSumFinEquiv (Sum.inr j))) +
        ψ u ^ N * phase χ ω u N j * ∑ d : Fin (κ + κ), ψ u ^ (d : ℕ) * (nodeVdm χ u)⁻¹ d
          (finSumFinEquiv (Sum.inl j)) := by
  simp only [charEval_apply, Fintype.sum_sum_type, testFamily, testMatrix, Sum.elim_inl,
    Sum.elim_inr, map_mul, map_pow, pow_add, mul_sum, ← sum_neg_distrib]
  congr 1 <;> refine sum_congr rfl fun d _ => ?_ <;> ring

theorem charEval_testMatrix_left {χ : Fin κ → G →* ℂ} {u : G}
    (hsep : Function.Injective (nodes χ u)) (ω : Fin κ → ℂ) (N : ℕ) (a : Fin κ → ℂ) (l : Fin κ) :
    charEval (χ l) (testFamily u N) (testMatrix χ ω u N *ᵥ a) =
      χ l u ^ N * phase χ ω u N l * a l := by
  have hl : χ l u = nodes χ u (Sum.inl l) := rfl
  simp only [charEval_mulVec, charEval_testColumn, hl, sum_pow_mul_nodeVdm_inv hsep,
    reduceCtorEq, if_false, neg_zero, zero_add, Sum.inl.injEq, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, if_true]
  ring

theorem charEval_testMatrix_right {χ : Fin κ → G →* ℂ} {u : G}
    (hsep : Function.Injective (nodes χ u)) (ω : Fin κ → ℂ) (N : ℕ) (a : Fin κ → ℂ) (l : Fin κ) :
    charEval (reflectChar (χ l)) (testFamily u N) (testMatrix χ ω u N *ᵥ a) = -a l := by
  have hl : reflectChar (χ l) u = nodes χ u (Sum.inr l) := rfl
  simp only [charEval_mulVec, charEval_testColumn, hl, sum_pow_mul_nodeVdm_inv hsep,
    reduceCtorEq, if_false, mul_zero, add_zero, Sum.inr.injEq, mul_neg, mul_ite, mul_one,
    sum_neg_distrib, sum_ite_eq, mem_univ, if_true]

/-- The entries of the coefficient matrix are bounded independently of `N`. -/
theorem norm_testMatrix_le {χ : Fin κ → G →* ℂ} {ω : Fin κ → ℂ} (hω : ∀ j, ω j ≠ 0) (u : G)
    (N : ℕ) (s : Fin (κ + κ) ⊕ Fin (κ + κ)) (j : Fin κ) :
    ‖testMatrix χ ω u N s j‖ ≤ ∑ d, ∑ m, ‖(nodeVdm χ u)⁻¹ d m‖ := by
  have hle : ∀ d m, ‖(nodeVdm χ u)⁻¹ d m‖ ≤ ∑ d, ∑ m, ‖(nodeVdm χ u)⁻¹ d m‖ := fun d m =>
    (single_le_sum (f := fun m => ‖(nodeVdm χ u)⁻¹ d m‖) (fun _ _ => norm_nonneg _)
      (mem_univ m)).trans (single_le_sum (f := fun d => ∑ m, ‖(nodeVdm χ u)⁻¹ d m‖)
        (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ d))
  rcases s with d | d
  · simp only [testMatrix, Sum.elim_inl, norm_neg]
    exact hle _ _
  · simp only [testMatrix, Sum.elim_inr, norm_mul, norm_phase hω, mul_one]
    exact hle _ _

/-- **Lower half of the index formula**, for pairs oriented outward at `u`. -/
theorem le_negIndex_of_separated_out {p : G → ℂ} (hp : IsPosDefOnGroup p)
    (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G)
    (hout : ∀ j, 1 < ‖χ j u‖) (hsep : Function.Injective (nodes χ u)) :
    (κ : ℕ∞) ≤ negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) := by
  set T : ℝ := ∑ d, ∑ m, ‖(nodeVdm χ u)⁻¹ d m‖
  set K₀ : ℝ := (p 1).re * (((κ + κ : ℕ) + (κ + κ : ℕ) : ℝ) * T) ^ 2 * κ
  have hev : ∀ᶠ N in atTop, ∀ j, K₀ < 2 * ‖ω j‖ * ‖χ j u‖ ^ N := by
    refine eventually_all.mpr fun j => ?_
    have hω' : 0 < 2 * ‖ω j‖ := by positivity [norm_pos_iff.mpr (hω j)]
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (hout j)).const_mul_atTop hω'
    exact ht.eventually_gt_atTop K₀
  obtain ⟨N, hN⟩ := hev.exists
  obtain ⟨r, hr, h1⟩ := hp.map_one_eq
  refine (Nat.cast_le.mpr ?_).trans
    (hermNegIndex_gram_le_negIndex _ (testFamily (κ := κ) u N))
  refine (Fintype.card_fin κ).symm.le.trans
    (card_le_hermNegIndex_of_forall_neg _ (testMatrix χ ω u N).mulVecLin fun a ha => ?_)
  set c := testMatrix χ ω u N *ᵥ a with hc
  rw [Matrix.mulVecLin_apply, hermQuad_gram_add, hermQuad_gram_sum]
  -- the pair terms
  have hpair : ∀ j ∈ (univ : Finset (Fin κ)),
      hermQuad (gram (pairKernel (χ j) (ω j)) (testFamily u N)) c =
        -(2 * ‖ω j‖ * ‖χ j u‖ ^ N * ‖a j‖ ^ 2) := fun j _ => by
    rw [hermQuad_gram_pairKernel, charEval_testMatrix_left hsep, charEval_testMatrix_right hsep,
      show ω j * (χ j u ^ N * phase χ ω u N j * a j) * conj (-a j) =
        -(ω j * (χ j u ^ N * phase χ ω u N j)) * (a j * conj (a j)) by rw [map_neg]; ring,
      mul_pow_mul_phase hω, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [sum_congr rfl hpair]
  -- the positive part
  have hsum : ∑ s, ‖c s‖ ≤ ((κ + κ : ℕ) + (κ + κ : ℕ) : ℝ) * T * ∑ j, ‖a j‖ := by
    calc ∑ s, ‖c s‖ ≤ ∑ s : Fin (κ + κ) ⊕ Fin (κ + κ), ∑ j, T * ‖a j‖ := by
          refine sum_le_sum fun s _ => ?_
          rw [hc, mulVec, dotProduct]
          refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_testMatrix_le hω u N s j) (norm_nonneg _)
      _ = ((κ + κ : ℕ) + (κ + κ : ℕ) : ℝ) * T * ∑ j, ‖a j‖ := by
          rw [sum_const, card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
          push_cast
          ring
  have hT : 0 ≤ T := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  have hcs : (∑ j, ‖a j‖) ^ 2 ≤ κ * ∑ j, ‖a j‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin κ))) (f := fun j => ‖a j‖)
    simpa using this
  have hpd : hermQuad (gram p (testFamily u N)) c ≤ K₀ * ∑ j, ‖a j‖ ^ 2 := by
    refine (hermQuad_gram_le_of_isPosDef hp _ c).trans ?_
    rw [h1, Complex.ofReal_re]
    have hpre : (p 1).re = r := by rw [h1, Complex.ofReal_re]
    calc r * (∑ s, ‖c s‖) ^ 2
        ≤ r * ((((κ + κ : ℕ) + (κ + κ : ℕ) : ℝ) * T) ^ 2 * (∑ j, ‖a j‖) ^ 2) := by
          rw [← mul_pow]
          gcongr
      _ ≤ r * ((((κ + κ : ℕ) + (κ + κ : ℕ) : ℝ) * T) ^ 2 * (κ * ∑ j, ‖a j‖ ^ 2)) := by
          gcongr
      _ = K₀ * ∑ j, ‖a j‖ ^ 2 := by simp only [K₀, hpre]; ring
  -- some coordinate is nonzero
  obtain ⟨l, hl⟩ : ∃ l, a l ≠ 0 := by
    by_contra h
    exact ha (funext fun j => not_not.mp fun hj => h ⟨j, hj⟩)
  have hneg : ∑ j, -(2 * ‖ω j‖ * ‖χ j u‖ ^ N * ‖a j‖ ^ 2) < -(K₀ * ∑ j, ‖a j‖ ^ 2) := by
    rw [sum_neg_distrib, neg_lt_neg_iff, mul_sum]
    refine sum_lt_sum (fun j _ => ?_) ⟨l, mem_univ l, ?_⟩
    · exact mul_le_mul_of_nonneg_right (hN j).le (sq_nonneg _)
    · exact mul_lt_mul_of_pos_right (hN l) (by positivity [norm_pos_iff.mpr hl])
  linarith

/-- Orientation of the `j`-th pair: flip `χ ↔ χ†` when `|χ(u)| ≤ 1`. -/
def flipIndex (χ : Fin κ → G →* ℂ) (u : G) : Fin κ ⊕ Fin κ → Fin κ ⊕ Fin κ :=
  Sum.elim (fun j => if 1 < ‖χ j u‖ then Sum.inl j else Sum.inr j)
    fun j => if 1 < ‖χ j u‖ then Sum.inr j else Sum.inl j

theorem flipIndex_flipIndex (χ : Fin κ → G →* ℂ) (u : G) (m : Fin κ ⊕ Fin κ) :
    flipIndex χ u (flipIndex χ u m) = m := by
  rcases m with j | j <;> by_cases h : 1 < ‖χ j u‖ <;> simp [flipIndex, h]

/-- **Lower half of the index formula.** If one element `u` separates the pairs, a
positive-definite kernel plus `κ` hyperbolic pairs has at least `κ` negative squares. -/
theorem le_negIndex_of_separated {p : G → ℂ} (hp : IsPosDefOnGroup p)
    (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G)
    (hne : ∀ j, ‖χ j u‖ ≠ 1) (hsep : Function.Injective (nodes χ u)) :
    (κ : ℕ∞) ≤ negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) := by
  classical
  set χ' : Fin κ → G →* ℂ := fun j => if 1 < ‖χ j u‖ then χ j else reflectChar (χ j)
  set ω' : Fin κ → ℂ := fun j => if 1 < ‖χ j u‖ then ω j else conj (ω j)
  have hk : (fun g => p g + ∑ j, pairKernel (χ' j) (ω' j) g) =
      fun g => p g + ∑ j, pairKernel (χ j) (ω j) g := by
    funext g
    congr 1
    refine sum_congr rfl fun j _ => ?_
    by_cases h : 1 < ‖χ j u‖
    · simp only [χ', ω', h, if_true]
    · simp only [χ', ω', h, if_false, pairKernel_reflectChar]
  rw [← hk]
  have hnodes : nodes χ' u = nodes χ u ∘ flipIndex χ u := by
    funext m
    rcases m with j | j <;> by_cases h : 1 < ‖χ j u‖ <;>
      simp [nodes, flipIndex, χ', h, reflectChar_reflectChar]
  refine le_negIndex_of_separated_out hp χ' ω' (fun j => ?_) u (fun j => ?_) ?_
  · by_cases h : 1 < ‖χ j u‖
    · simp only [ω', h, if_true]; exact hω j
    · simp only [ω', h, if_false]; exact (map_ne_zero_iff _ (RingHom.injective _)).mpr (hω j)
  · by_cases h : 1 < ‖χ j u‖
    · simpa only [χ', h, if_true] using h
    · simp only [χ', h, if_false]
      rw [norm_reflectChar]
      exact one_lt_inv₀ (norm_pos_iff.mpr (map_ne_zero _ _)) |>.mpr
        (lt_of_le_of_ne (not_lt.mp h) (hne j))
  · rw [hnodes]
    exact hsep.comp (Function.LeftInverse.injective (flipIndex_flipIndex χ u))

/-- **The Krein–Langer index formula.** A positive-definite kernel plus `κ` hyperbolic pairs
separated at one element has exactly `κ` negative squares. -/
theorem negIndex_add_sum_pairKernel_eq {p : G → ℂ} (hp : IsPosDefOnGroup p)
    (χ : Fin κ → G →* ℂ) (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G)
    (hne : ∀ j, ‖χ j u‖ ≠ 1) (hsep : Function.Injective (nodes χ u)) :
    negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) = κ :=
  le_antisymm ((negIndex_add_sum_pairKernel_le hp χ ω).trans (by simp))
    (le_negIndex_of_separated hp χ ω hω u hne hsep)

end LowerBound

/-! ### One pair -/

theorem reflectChar_ne_of_norm_ne_one {χ : G →* ℂ} {u : G} (h : ‖χ u‖ ≠ 1) :
    reflectChar χ u ≠ χ u := fun he => by
  have := congrArg norm he
  rw [norm_reflectChar] at this
  have hpos : 0 < ‖χ u‖ := norm_pos_iff.mpr (map_ne_zero _ _)
  have hsq : ‖χ u‖ * ‖χ u‖ = 1 := by
    calc ‖χ u‖ * ‖χ u‖ = ‖χ u‖⁻¹ * ‖χ u‖ := by rw [this]
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  exact h (by nlinarith)

/-- **A pair is never paid.** A positive-definite kernel plus one hyperbolic pair with
non-unitary character has exactly one negative square, however large the positive part. -/
theorem negIndex_add_pairKernel_eq_one {p : G → ℂ} (hp : IsPosDefOnGroup p) {χ : G →* ℂ}
    (hχ : ¬ IsUnitaryChar χ) {ω : ℂ} (hω : ω ≠ 0) :
    negIndex (fun g => p g + pairKernel χ ω g) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u, ‖χ u‖ ≠ 1 := by
    by_contra h
    exact hχ fun u => not_not.mp fun hu => h ⟨u, hu⟩
  have hsep : Function.Injective (nodes (fun _ : Fin 1 => χ) u) := by
    have hne := reflectChar_ne_of_norm_ne_one hu
    intro m m' hm
    rcases m with i | i <;> rcases m' with i' | i' <;>
      simp only [nodes, Sum.elim_inl, Sum.elim_inr] at hm <;>
      simp [Subsingleton.elim i i', hne, hne.symm] at hm ⊢
  have := negIndex_add_sum_pairKernel_eq hp (fun _ : Fin 1 => χ) (fun _ => ω) (fun _ => hω) u
    (fun _ => hu) hsep
  simpa using this

/-- For a unitary character and `Re ω ≥ 0` the pair kernel is positive definite. -/
theorem negIndex_pairKernel_of_unitary {χ : G →* ℂ} (hχ : IsUnitaryChar χ) {ω : ℂ}
    (hω : 0 ≤ ω.re) : negIndex (pairKernel χ ω) = 0 :=
  negIndex_eq_zero_iff.mpr fun n x c => by
    rw [hermQuad_gram_pairKernel_of_unitary hχ]
    exact mul_nonneg (mul_nonneg zero_le_two hω) (Complex.normSq_nonneg _)

end GaloisForLFunctions.HeckeKreinToeplitz
