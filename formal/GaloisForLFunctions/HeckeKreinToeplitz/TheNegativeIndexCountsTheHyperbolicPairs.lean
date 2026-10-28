import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The negative index counts the hyperbolic pairs

A character `χ : G →* ℂ` of a group has a **reflection** `χ†(u) = conj(χ u)⁻¹`; unitary characters
are fixed by it. A weight `ω ∈ ℂ` gives the Hermitian **hyperbolic pair kernel**
`h_{χ,ω} = ω χ + conj ω χ†`. On a family `x` its Toeplitz form is `2 Re(ω A(c) conj B(c))` with the two
evaluation functionals `A(c) = Σ_a c_a χ(x_a)` and `B(c) = Σ_a c_a χ†(x_a)` (`hermQuad_gram_hypPair`).

**Index formula.** For a positive-definite kernel `p` and `J` pairs,
`κ(p + Σ_j h_{χ_j,ω_j}) ≤ J` unconditionally (`negIndex_posDef_add_hypPairs_le`): on the common
kernel of the `J` functionals `A_j` the pairs vanish and only the positive part survives. Under
**separation at one element** `u` (the `2J` nodes `χ_j(u), χ_j†(u)` are pairwise distinct, which
forces every `χ_j(u)` off the unit circle) and nonzero weights, equality holds
(`negIndex_posDef_add_hypPairs_eq`): growth beats boundedness. A positive-definite kernel is bounded
by `p(1)`, while along the cyclic subgroup `⟨u⟩` each pair is a two-sided exponential. Test vectors
supported on two windows of length `2J` placed `N` steps apart, with coefficients prescribed by the
inverse Vandermonde matrix of the `2J` nodes, realize `A_j = χ_j(u)^N a_j` and `B_j = θ_j a_j` with
`|θ_j| = 1`; after normalizing every pair so that `|χ_j(u)| > 1`, the hyperbolic part is
`−2 Σ_j |ω_j| |χ_j(u)|^N |a_j|²` on a `J`-dimensional space of coefficient vectors, while the positive
part is `O(|a|²)` uniformly in `N`.

**Hyperbolic plane law.** A single pair with nonzero weight has index exactly one as soon as its
character leaves the unit circle somewhere (`negIndex_hypPair_eq_one`), and index zero when the
character is unitary and `Re ω ≥ 0` (`negIndex_hypPair_eq_zero_of_unitary`).

Arithmetic reading. For the Hecke orbit kernel `u ↦ W(g, τ_{log u} g)` on `ℚ_{>0}`, an on-line zero
`½ + iγ` is the unitary character `u ↦ u^{iγ}`, and an off-line zero `ρ` together with its reflection
`1 − ρ̄` is the hyperbolic pair of characters `u ↦ u^{ρ−1/2}`, `u ↦ u^{1/2−ρ̄}`. The index formula says
that the negative index of a kernel of this shape is not a size to be bounded but a count: the number
of hyperbolic pairs, each of which survives every positive-definite addition. Over a finite field the
same statement reads: the trace sequence of a curve is positive definite plus one hyperbolic pair for
each pair of Frobenius eigenvalues off the circle, and its index is the number of such pairs.
-/

open Complex Matrix Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality (IsPosDefOnGroup)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

variable {G : Type*} [Group G]

/-! ### Reflected characters and hyperbolic pairs -/

section Pairs

/-- The reflection `χ†(u) = conj(χ u)⁻¹` of a character. -/
def reflect (χ : G →* ℂ) : G →* ℂ where
  toFun u := (conj (χ u))⁻¹
  map_one' := by simp
  map_mul' a b := by simp [map_mul, mul_inv]

@[simp] theorem reflect_apply (χ : G →* ℂ) (u : G) : reflect χ u = (conj (χ u))⁻¹ := rfl

@[simp] theorem reflect_reflect (χ : G →* ℂ) : reflect (reflect χ) = χ := by
  ext u
  simp

/-- A character of a group never vanishes. -/
theorem char_ne_zero (χ : G →* ℂ) (u : G) : χ u ≠ 0 := by
  intro h
  have := map_mul χ u u⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem norm_reflect_apply (χ : G →* ℂ) (u : G) : ‖reflect χ u‖ = ‖χ u‖⁻¹ := by
  simp

/-- A unimodular value is fixed by reflection. -/
theorem reflect_apply_of_norm_eq_one {χ : G →* ℂ} {u : G} (h : ‖χ u‖ = 1) : reflect χ u = χ u := by
  rw [reflect_apply, Complex.inv_def, conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, h]
  simp

/-- The hyperbolic pair kernel `h_{χ,ω} = ω χ + conj ω χ†`. -/
def hypPair (χ : G →* ℂ) (ω : ℂ) : G → ℂ := fun u => ω * χ u + conj ω * reflect χ u

theorem hypPair_apply (χ : G →* ℂ) (ω : ℂ) (u : G) :
    hypPair χ ω u = ω * χ u + conj ω * reflect χ u := rfl

/-- Reflecting the character and conjugating the weight gives the same kernel. -/
theorem hypPair_reflect (χ : G →* ℂ) (ω : ℂ) : hypPair (reflect χ) (conj ω) = hypPair χ ω := by
  funext u
  simp only [hypPair, reflect_reflect, conj_conj]
  ring

theorem isHermKernel_hypPair (χ : G →* ℂ) (ω : ℂ) : IsHermKernel (hypPair χ ω) := by
  intro u
  simp only [hypPair, map_inv, reflect_apply, map_add, map_mul, map_inv₀, conj_conj, inv_inv]
  ring

variable {ι : Type*} [Fintype ι]

/-- The evaluation functional `A_χ(c) = Σ_a c_a χ(x_a)` of a character on a family. -/
def evalChar (χ : G →* ℂ) (x : ι → G) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun c := ∑ a, c a * χ (x a)
  map_add' c d := by simp [add_mul, sum_add_distrib]
  map_smul' r c := by simp [mul_sum, mul_assoc]

theorem evalChar_apply (χ : G →* ℂ) (x : ι → G) (c : ι → ℂ) :
    evalChar χ x c = ∑ a, c a * χ (x a) := rfl

/-- The Toeplitz sum of a pair factors through the two evaluation functionals. -/
theorem toeplitzSum_hypPair (χ : G →* ℂ) (ω : ℂ) (x : ι → G) (c : ι → ℂ) :
    ∑ a, ∑ b, conj (c a) * hypPair χ ω ((x a)⁻¹ * x b) * c b =
      ω * evalChar χ x c * conj (evalChar (reflect χ) x c) +
        conj ω * evalChar (reflect χ) x c * conj (evalChar χ x c) := by
  have h1 : ∀ v, conj (reflect χ v) = (χ v)⁻¹ := fun v => by simp
  have h2 : ∀ v, (reflect χ v)⁻¹ = conj (χ v) := fun v => by simp
  have hterm : ∀ a b, conj (c a) * hypPair χ ω ((x a)⁻¹ * x b) * c b =
      ω * (c b * χ (x b)) * (conj (c a) * (χ (x a))⁻¹) +
        conj ω * (c b * reflect χ (x b)) * (conj (c a) * conj (χ (x a))) := by
    intro a b
    simp only [hypPair_apply, map_mul, map_inv, h2]
    ring
  simp only [hterm, sum_add_distrib, evalChar_apply, map_sum, map_mul, h1]
  rw [mul_sum, mul_sum, sum_mul, sum_mul]
  simp only [mul_sum]
  rw [sum_comm (f := fun b a => ω * (c b * χ (x b)) * (conj (c a) * (χ (x a))⁻¹)),
    sum_comm (f := fun b a => conj ω * (c b * reflect χ (x b)) * (conj (c a) * conj (χ (x a))))]

/-- **The Toeplitz form of a hyperbolic pair is `2 Re(ω A conj B)`.** -/
theorem hermQuad_gram_hypPair (χ : G →* ℂ) (ω : ℂ) (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram (hypPair χ ω) x) c =
      2 * (ω * evalChar χ x c * conj (evalChar (reflect χ) x c)).re := by
  rw [hermQuad_gram, toeplitzSum_hypPair]
  have : conj ω * evalChar (reflect χ) x c * conj (evalChar χ x c) =
      conj (ω * evalChar χ x c * conj (evalChar (reflect χ) x c)) := by
    simp only [map_mul, conj_conj]
    ring
  rw [this, Complex.add_re, Complex.conj_re]
  ring

/-- The Toeplitz form of a finite sum of kernels is the sum of the forms. -/
theorem hermQuad_gram_finset_sum {J : Type*} (s : Finset J) (k : J → G → ℂ) (x : ι → G)
    (c : ι → ℂ) :
    hermQuad (gram (fun u => ∑ j ∈ s, k j u) x) c = ∑ j ∈ s, hermQuad (gram (k j) x) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermQuad, gram]
  | insert j s hj ih =>
    simp only [sum_insert hj]
    rw [hermQuad_gram_add, ih]

end Pairs

/-! ### Upper bound: at most one negative square per pair -/

section Upper

variable {ι : Type*} [Fintype ι]

/-- The Toeplitz form of a positive-definite kernel is nonnegative. -/
theorem hermQuad_gram_nonneg_of_posDef {p : G → ℂ} (hp : IsPosDefOnGroup p) (x : ι → G)
    (c : ι → ℂ) : 0 ≤ hermQuad (gram p x) c := by
  obtain ⟨r, hr, h⟩ := hp.form x c
  rw [hermQuad_gram]
  simp only [Complex.star_def] at h
  rw [h, Complex.ofReal_re]
  exact hr

/-- **Index formula, upper bound.** Adding `J` hyperbolic pairs to a positive-definite kernel
creates at most `J` negative squares: on the common kernel of the `J` evaluation functionals `A_j`
the pairs vanish and only the positive part survives. -/
theorem negIndex_posDef_add_hypPairs_le {J : Type*} [Fintype J] {p : G → ℂ}
    (hp : IsPosDefOnGroup p) (χ : J → G →* ℂ) (ω : J → ℂ) :
    negIndex (fun u => p u + ∑ j, hypPair (χ j) (ω j) u) ≤ Fintype.card J := by
  rw [negIndex_le_iff]
  intro n x
  refine Nat.cast_le.mpr (ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker _
    (fun j => evalChar (χ j) x) fun c hc => ?_)
  rw [hermQuad_gram_add, hermQuad_gram_finset_sum]
  have hz : ∑ j, hermQuad (gram (hypPair (χ j) (ω j)) x) c = 0 := by
    refine sum_eq_zero fun j _ => ?_
    rw [hermQuad_gram_hypPair, hc j]
    simp
  linarith [hermQuad_gram_nonneg_of_posDef hp x c]

end Upper

/-! ### Lower bound: every pair survives any positive-definite addition -/

section Lower

/-- A positive-definite kernel is bounded by its value at the identity. -/
theorem norm_le_re_one_of_posDef {p : G → ℂ} (hp : IsPosDefOnGroup p) (g : G) :
    ‖p g‖ ≤ (p 1).re := by
  have h := hp.normSq_le g
  rw [Complex.normSq_eq_norm_sq] at h
  have h0 : 0 ≤ (p 1).re := by
    obtain ⟨r, hr, hr'⟩ := hp.map_one_eq
    rw [hr', Complex.ofReal_re]
    exact hr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp h

theorem re_one_nonneg_of_posDef {p : G → ℂ} (hp : IsPosDefOnGroup p) : 0 ≤ (p 1).re :=
  (norm_nonneg _).trans (norm_le_re_one_of_posDef hp 1)

variable {ι : Type*} [Fintype ι]

/-- The Toeplitz form of a positive-definite kernel is at most `p(1)` times the squared
`ℓ¹`-norm of the coefficients. -/
theorem hermQuad_gram_le_of_posDef {p : G → ℂ} (hp : IsPosDefOnGroup p) (x : ι → G) (c : ι → ℂ) :
    hermQuad (gram p x) c ≤ (p 1).re * (∑ a, ‖c a‖) ^ 2 := by
  rw [hermQuad_gram]
  calc (∑ a, ∑ b, conj (c a) * p ((x a)⁻¹ * x b) * c b).re
      ≤ ‖∑ a, ∑ b, conj (c a) * p ((x a)⁻¹ * x b) * c b‖ := Complex.re_le_norm _
    _ ≤ ∑ a, ∑ b, ‖conj (c a) * p ((x a)⁻¹ * x b) * c b‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a, ∑ b, (p 1).re * (‖c a‖ * ‖c b‖) := by
        refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have hpb := norm_le_re_one_of_posDef hp ((x a)⁻¹ * x b)
        have hab : 0 ≤ ‖c a‖ * ‖c b‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        calc ‖c a‖ * ‖p ((x a)⁻¹ * x b)‖ * ‖c b‖
            = (‖c a‖ * ‖c b‖) * ‖p ((x a)⁻¹ * x b)‖ := by ring
          _ ≤ (‖c a‖ * ‖c b‖) * (p 1).re := mul_le_mul_of_nonneg_left hpb hab
          _ = (p 1).re * (‖c a‖ * ‖c b‖) := by ring
    _ = (p 1).re * (∑ a, ‖c a‖) ^ 2 := by
        rw [sq, sum_mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]

/-- The `ℓ¹`-norm of `M *ᵥ t` is at most the entrywise `ℓ¹`-norm of `M` times that of `t`. -/
theorem sum_norm_mulVec_le {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) (t : n → ℂ) :
    ∑ i, ‖(M *ᵥ t) i‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ∑ j, ‖t j‖ := by
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [sum_mul]
  simp only [Matrix.mulVec, dotProduct]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (single_le_sum (fun j _ => norm_nonneg (t j)) (mem_univ j)) (norm_nonneg _)

/-- The phase `θ = −q/|q|` turns the pairing `q a conj(θ a)` into `−|q| |a|²`. -/
theorem re_mul_conj_phase {q : ℂ} (hq : q ≠ 0) (a : ℂ) :
    (q * a * conj (-(q / (‖q‖ : ℂ)) * a)).re = -(‖q‖ * ‖a‖ ^ 2) := by
  have hq' : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq
  have hqq : q * conj q = ((‖q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have haa : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 : q * a * conj (-(q / (‖q‖ : ℂ)) * a) = -((q * conj q) * (a * conj a)) / (‖q‖ : ℂ) := by
    simp only [map_mul, map_neg, map_div₀, Complex.conj_ofReal]
    ring
  have h2 : -(((‖q‖ ^ 2 : ℝ) : ℂ) * ((‖a‖ ^ 2 : ℝ) : ℂ)) / (‖q‖ : ℂ) =
      ((-(‖q‖ * ‖a‖ ^ 2) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [h1, hqq, haa, h2, Complex.ofReal_re]

/-- `(V *ᵥ e) i = Σ_n z_i^n e_n` for the Vandermonde matrix of `z`. -/
theorem vandermonde_mulVec_apply {n : ℕ} (z : Fin n → ℂ) (e : Fin n → ℂ) (i : Fin n) :
    (vandermonde z *ᵥ e) i = ∑ m, z i ^ (m : ℕ) * e m := by
  simp [Matrix.mulVec, dotProduct, vandermonde_apply]

/-- Interpolation at distinct nodes: `V *ᵥ (V⁻¹ *ᵥ t) = t`. -/
theorem vandermonde_mulVec_inv_mulVec {n : ℕ} {z : Fin n → ℂ} (hz : Function.Injective z)
    (t : Fin n → ℂ) : vandermonde z *ᵥ ((vandermonde z)⁻¹ *ᵥ t) = t := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr hz)),
    Matrix.one_mulVec]

variable {J : ℕ} (χ : Fin J → G →* ℂ) (u : G)

/-- The `2J` nodes `χ_j(u)` (left) and `χ_j†(u)` (right) of a family of pairs at `u`. -/
def nodes : Fin J ⊕ Fin J → ℂ := Sum.elim (fun j => χ j u) (fun j => reflect (χ j) u)

/-- **Separation at `u`**: the `2J` nodes `χ_j(u), χ_j†(u)` are pairwise distinct. -/
def SeparatedAt : Prop := Function.Injective (nodes χ u)

/-- Separation forces every `χ_j(u)` off the unit circle. -/
theorem norm_ne_one_of_separatedAt (hsep : SeparatedAt χ u) (j : Fin J) : ‖χ j u‖ ≠ 1 := by
  intro h1
  have : nodes χ u (Sum.inl j) = nodes χ u (Sum.inr j) := by
    simp only [nodes, Sum.elim_inl, Sum.elim_inr]
    exact (reflect_apply_of_norm_eq_one h1).symm
  exact Sum.inl_ne_inr (hsep this)

/-- The nodes reindexed on `Fin (J + J)`. -/
def nodesFin : Fin (J + J) → ℂ := nodes χ u ∘ finSumFinEquiv.symm

theorem nodesFin_injective (hsep : SeparatedAt χ u) : Function.Injective (nodesFin χ u) :=
  hsep.comp finSumFinEquiv.symm.injective

theorem nodesFin_inl (j : Fin J) : nodesFin χ u (finSumFinEquiv (Sum.inl j)) = χ j u := by
  simp [nodesFin, nodes]

theorem nodesFin_inr (j : Fin J) :
    nodesFin χ u (finSumFinEquiv (Sum.inr j)) = reflect (χ j) u := by
  simp [nodesFin, nodes]

/-- The two-window family `u^0, …, u^{2J-1}` and `u^N, …, u^{N+2J-1}`. -/
def twoWindow (N : ℕ) : Fin (J + J) ⊕ Fin (J + J) → G :=
  Sum.elim (fun n => u ^ (n : ℕ)) (fun n => u ^ (N + (n : ℕ)))

/-- Evaluating a character on a two-window vector: a window polynomial at `ψ(u)` plus `ψ(u)^N`
times a second one. -/
theorem evalChar_twoWindow (ψ : G →* ℂ) (N : ℕ) (e f : Fin (J + J) → ℂ) :
    evalChar ψ (twoWindow (J := J) u N) (Sum.elim e f) =
      ∑ n, ψ u ^ (n : ℕ) * e n + ψ u ^ N * ∑ n, ψ u ^ (n : ℕ) * f n := by
  simp only [evalChar_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, twoWindow, map_pow,
    pow_add, mul_sum]
  congr 1
  · exact sum_congr rfl fun n _ => by ring
  · exact sum_congr rfl fun n _ => by ring

/-- The phase `θ_j = −q_j/|q_j|` with `q_j = ω_j χ_j(u)^N`. -/
def phase (ω : Fin J → ℂ) (N : ℕ) (j : Fin J) : ℂ :=
  -(ω j * χ j u ^ N / (‖ω j * χ j u ^ N‖ : ℂ))

theorem norm_phase {ω : Fin J → ℂ} (hω : ∀ j, ω j ≠ 0) (N : ℕ) (j : Fin J) :
    ‖phase χ u ω N j‖ = 1 := by
  have hq : ω j * χ j u ^ N ≠ 0 := mul_ne_zero (hω j) (pow_ne_zero _ (char_ne_zero _ _))
  simp [phase, norm_div, hq]

/-- Target values on the first window: `0` at `χ_j(u)` and `θ_j a_j` at `χ_j†(u)`. -/
def targetE (ω : Fin J → ℂ) (N : ℕ) (a : Fin J → ℂ) (i : Fin (J + J)) : ℂ :=
  Sum.elim (fun _ => 0) (fun j => phase χ u ω N j * a j) (finSumFinEquiv.symm i)

/-- Target values on the second window: `a_j` at `χ_j(u)` and `0` at `χ_j†(u)`. -/
def targetF (a : Fin J → ℂ) (i : Fin (J + J)) : ℂ :=
  Sum.elim a (fun _ => 0) (finSumFinEquiv.symm i)

theorem targetE_inl (ω : Fin J → ℂ) (N : ℕ) (a : Fin J → ℂ) (j : Fin J) :
    targetE χ u ω N a (finSumFinEquiv (Sum.inl j)) = 0 := by
  simp [targetE]

theorem targetE_inr (ω : Fin J → ℂ) (N : ℕ) (a : Fin J → ℂ) (j : Fin J) :
    targetE χ u ω N a (finSumFinEquiv (Sum.inr j)) = phase χ u ω N j * a j := by
  simp [targetE]

theorem targetF_inl (a : Fin J → ℂ) (j : Fin J) :
    targetF (J := J) a (finSumFinEquiv (Sum.inl j)) = a j := by
  simp [targetF]

theorem targetF_inr (a : Fin J → ℂ) (j : Fin J) :
    targetF (J := J) a (finSumFinEquiv (Sum.inr j)) = 0 := by
  simp [targetF]

theorem targetE_add (ω : Fin J → ℂ) (N : ℕ) (a b : Fin J → ℂ) :
    targetE χ u ω N (a + b) = targetE χ u ω N a + targetE χ u ω N b := by
  funext i
  simp only [targetE, Pi.add_apply]
  rcases finSumFinEquiv.symm i with j | j <;> simp [mul_add]

theorem targetE_smul (ω : Fin J → ℂ) (N : ℕ) (r : ℂ) (a : Fin J → ℂ) :
    targetE χ u ω N (r • a) = r • targetE χ u ω N a := by
  funext i
  simp only [targetE, Pi.smul_apply, smul_eq_mul]
  rcases finSumFinEquiv.symm i with j | j <;> simp ; ring

theorem targetF_add (a b : Fin J → ℂ) :
    targetF (J := J) (a + b) = targetF a + targetF b := by
  funext i
  simp only [targetF, Pi.add_apply]
  rcases finSumFinEquiv.symm i with j | j <;> simp

theorem targetF_smul (r : ℂ) (a : Fin J → ℂ) :
    targetF (J := J) (r • a) = r • targetF a := by
  funext i
  simp only [targetF, Pi.smul_apply, smul_eq_mul]
  rcases finSumFinEquiv.symm i with j | j <;> simp

theorem sum_norm_targetE {ω : Fin J → ℂ} (hω : ∀ j, ω j ≠ 0) (N : ℕ) (a : Fin J → ℂ) :
    ∑ i, ‖targetE χ u ω N a i‖ = ∑ j, ‖a j‖ := by
  unfold targetE
  rw [← finSumFinEquiv.symm.sum_comp]
  simp [Fintype.sum_sum_type, norm_phase χ u hω]

theorem sum_norm_targetF (a : Fin J → ℂ) : ∑ i, ‖targetF (J := J) a i‖ = ∑ j, ‖a j‖ := by
  unfold targetF
  rw [← finSumFinEquiv.symm.sum_comp]
  simp [Fintype.sum_sum_type]

/-- The two-window test vector: interpolate the targets on each window through the inverse
Vandermonde matrix of the nodes. -/
def twoWindowVec (ω : Fin J → ℂ) (N : ℕ) (a : Fin J → ℂ) : Fin (J + J) ⊕ Fin (J + J) → ℂ :=
  Sum.elim ((vandermonde (nodesFin χ u))⁻¹ *ᵥ targetE χ u ω N a)
    ((vandermonde (nodesFin χ u))⁻¹ *ᵥ targetF a)

/-- The two-window vector as a linear map in the parameters `a`. -/
def twoWindowMap (ω : Fin J → ℂ) (N : ℕ) :
    (Fin J → ℂ) →ₗ[ℂ] (Fin (J + J) ⊕ Fin (J + J) → ℂ) where
  toFun := twoWindowVec χ u ω N
  map_add' a b := by
    funext s
    rcases s with n | n <;> simp [twoWindowVec, targetE_add, targetF_add, Matrix.mulVec_add]
  map_smul' r a := by
    funext s
    rcases s with n | n <;> simp [twoWindowVec, targetE_smul, targetF_smul, Matrix.mulVec_smul]

theorem twoWindowMap_apply (ω : Fin J → ℂ) (N : ℕ) (a : Fin J → ℂ) :
    twoWindowMap χ u ω N a = twoWindowVec χ u ω N a := rfl

/-- The interpolated window polynomial takes the prescribed value at each node. -/
theorem window_eval (hsep : SeparatedAt χ u) (t : Fin (J + J) → ℂ) (i : Fin (J + J)) :
    ∑ n, nodesFin χ u i ^ (n : ℕ) * ((vandermonde (nodesFin χ u))⁻¹ *ᵥ t) n = t i := by
  rw [← vandermonde_mulVec_apply, vandermonde_mulVec_inv_mulVec (nodesFin_injective χ u hsep)]

/-- `A_j(c) = χ_j(u)^N a_j` on the two-window vector. -/
theorem evalChar_twoWindowVec_inl (hsep : SeparatedAt χ u) (ω : Fin J → ℂ) (N : ℕ)
    (a : Fin J → ℂ) (j : Fin J) :
    evalChar (χ j) (twoWindow u N) (twoWindowVec χ u ω N a) = χ j u ^ N * a j := by
  unfold twoWindowVec
  rw [evalChar_twoWindow]
  have hE := window_eval χ u hsep (targetE χ u ω N a) (finSumFinEquiv (Sum.inl j))
  have hF := window_eval χ u hsep (targetF a) (finSumFinEquiv (Sum.inl j))
  rw [nodesFin_inl] at hE hF
  rw [hE, hF, targetE_inl, targetF_inl, zero_add]

/-- `B_j(c) = θ_j a_j` on the two-window vector. -/
theorem evalChar_twoWindowVec_inr (hsep : SeparatedAt χ u) (ω : Fin J → ℂ) (N : ℕ)
    (a : Fin J → ℂ) (j : Fin J) :
    evalChar (reflect (χ j)) (twoWindow u N) (twoWindowVec χ u ω N a) =
      phase χ u ω N j * a j := by
  unfold twoWindowVec
  rw [evalChar_twoWindow]
  have hE := window_eval χ u hsep (targetE χ u ω N a) (finSumFinEquiv (Sum.inr j))
  have hF := window_eval χ u hsep (targetF a) (finSumFinEquiv (Sum.inr j))
  rw [nodesFin_inr] at hE hF
  rw [hE, hF, targetE_inr, targetF_inr, mul_zero, add_zero]

/-- The entrywise `ℓ¹`-norm of the inverse Vandermonde matrix of the nodes. -/
def vandermondeInvNorm : ℝ := ∑ n, ∑ i, ‖(vandermonde (nodesFin χ u))⁻¹ n i‖

theorem vandermondeInvNorm_nonneg : 0 ≤ vandermondeInvNorm χ u :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _

/-- The `ℓ¹`-norm of the two-window vector is `O(Σ_j |a_j|)` uniformly in `N`. -/
theorem sum_norm_twoWindowVec_le {ω : Fin J → ℂ} (hω : ∀ j, ω j ≠ 0) (N : ℕ) (a : Fin J → ℂ) :
    ∑ s, ‖twoWindowVec χ u ω N a s‖ ≤ 2 * vandermondeInvNorm χ u * ∑ j, ‖a j‖ := by
  unfold twoWindowVec
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hE := sum_norm_mulVec_le (vandermonde (nodesFin χ u))⁻¹ (targetE χ u ω N a)
  have hF := sum_norm_mulVec_le (vandermonde (nodesFin χ u))⁻¹ (targetF a)
  rw [sum_norm_targetE χ u hω] at hE
  rw [sum_norm_targetF] at hF
  unfold vandermondeInvNorm
  linarith

/-- The hyperbolic part on the two-window vector is `−2 Σ_j |ω_j| |χ_j(u)|^N |a_j|²`. -/
theorem hermQuad_hypPairs_twoWindowVec (hsep : SeparatedAt χ u) {ω : Fin J → ℂ}
    (hω : ∀ j, ω j ≠ 0) (N : ℕ) (a : Fin J → ℂ) :
    ∑ j, hermQuad (gram (hypPair (χ j) (ω j)) (twoWindow u N)) (twoWindowVec χ u ω N a) =
      -(2 * ∑ j, ‖ω j‖ * ‖χ j u‖ ^ N * ‖a j‖ ^ 2) := by
  rw [mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [hermQuad_gram_hypPair, evalChar_twoWindowVec_inl χ u hsep, evalChar_twoWindowVec_inr χ u hsep]
  have hq : ω j * χ j u ^ N ≠ 0 := mul_ne_zero (hω j) (pow_ne_zero _ (char_ne_zero _ _))
  have := re_mul_conj_phase hq (a j)
  rw [show ω j * (χ j u ^ N * a j) = ω j * χ j u ^ N * a j by ring]
  unfold phase
  rw [this, norm_mul, norm_pow]
  ring

/-- **Growth beats boundedness.** Once `|ω_j| |χ_j(u)|^N` exceeds the threshold set by `p(1)` and the
inverse Vandermonde matrix, the full form is negative on every nonzero two-window vector. -/
theorem hermQuad_twoWindowVec_neg {p : G → ℂ} (hp : IsPosDefOnGroup p) (hsep : SeparatedAt χ u)
    {ω : Fin J → ℂ} (hω : ∀ j, ω j ≠ 0) {N : ℕ}
    (hN : ∀ j, 2 * (p 1).re * vandermondeInvNorm χ u ^ 2 * J + 1 ≤ ‖ω j‖ * ‖χ j u‖ ^ N)
    {a : Fin J → ℂ} (ha : a ≠ 0) :
    hermQuad (gram (fun v => p v + ∑ j, hypPair (χ j) (ω j) v) (twoWindow u N))
      (twoWindowVec χ u ω N a) < 0 := by
  rw [hermQuad_gram_add, hermQuad_gram_finset_sum, hermQuad_hypPairs_twoWindowVec χ u hsep hω]
  set P := (p 1).re with hP
  set C := vandermondeInvNorm χ u with hC
  set S := ∑ j, ‖a j‖ ^ 2 with hS
  have hP0 : 0 ≤ P := re_one_nonneg_of_posDef hp
  have hC0 : 0 ≤ C := vandermondeInvNorm_nonneg χ u
  have hS0 : 0 < S := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    exact sum_pos' (fun j _ => by positivity) ⟨j, mem_univ j, by positivity⟩
  -- the positive part
  have hpos : hermQuad (gram p (twoWindow u N)) (twoWindowVec χ u ω N a) ≤ 4 * P * C ^ 2 * J * S := by
    refine (hermQuad_gram_le_of_posDef hp _ _).trans ?_
    have h1 := sum_norm_twoWindowVec_le χ u hω N a
    have h2 : (∑ j, ‖a j‖) ^ 2 ≤ J * S := by
      have := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun j => ‖a j‖)
      simpa [hS] using this
    have h0 : 0 ≤ ∑ s, ‖twoWindowVec χ u ω N a s‖ := sum_nonneg fun _ _ => norm_nonneg _
    have h3 : (∑ s, ‖twoWindowVec χ u ω N a s‖) ^ 2 ≤ (2 * C * ∑ j, ‖a j‖) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    calc P * (∑ s, ‖twoWindowVec χ u ω N a s‖) ^ 2
        ≤ P * (2 * C * ∑ j, ‖a j‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hP0
      _ = 4 * P * C ^ 2 * (∑ j, ‖a j‖) ^ 2 := by ring
      _ ≤ 4 * P * C ^ 2 * (J * S) := by
          refine mul_le_mul_of_nonneg_left h2 ?_
          positivity
      _ = 4 * P * C ^ 2 * J * S := by ring
  -- the hyperbolic part
  have hneg : (2 * P * C ^ 2 * J + 1) * S ≤ ∑ j, ‖ω j‖ * ‖χ j u‖ ^ N * ‖a j‖ ^ 2 := by
    rw [hS, mul_sum]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hN j) (by positivity)
  linarith

/-- **Lower bound in outer normalization.** With every `|χ_j(u)| > 1`, the index is at least `J`. -/
theorem le_negIndex_of_outer {p : G → ℂ} (hp : IsPosDefOnGroup p) {ω : Fin J → ℂ}
    (hω : ∀ j, ω j ≠ 0) (hout : ∀ j, 1 < ‖χ j u‖) (hsep : SeparatedAt χ u) :
    (J : ℕ∞) ≤ negIndex (fun v => p v + ∑ j, hypPair (χ j) (ω j) v) := by
  set K : ℝ := 2 * (p 1).re * vandermondeInvNorm χ u ^ 2 * J + 1 with hK
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j, K ≤ ‖ω j‖ * ‖χ j u‖ ^ N := by
    have hev : ∀ᶠ N : ℕ in Filter.atTop, ∀ j, K ≤ ‖ω j‖ * ‖χ j u‖ ^ N := by
      rw [Filter.eventually_all]
      intro j
      have hωj : 0 < ‖ω j‖ := norm_pos_iff.mpr (hω j)
      filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt (hout j)).eventually_ge_atTop
        (K / ‖ω j‖)] with N hN
      rwa [div_le_iff₀ hωj, mul_comm] at hN
    exact hev.exists
  set k : G → ℂ := fun v => p v + ∑ j, hypPair (χ j) (ω j) v with hk
  set x := twoWindow (J := J) u N with hx
  -- the `J`-dimensional negative-definite subspace
  have hinj : Function.Injective (twoWindowMap χ u ω N) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, twoWindowMap_apply] at ha
    funext j
    have h := evalChar_twoWindowVec_inl χ u hsep ω N a j
    rw [ha, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (char_ne_zero _ _))
  have hW : IsPosDefOn (-(gram k x)) (LinearMap.range (twoWindowMap χ u ω N)) := by
    rintro c ⟨a, rfl⟩ hc
    have ha : a ≠ 0 := by
      rintro rfl
      exact hc (map_zero _)
    rw [hermQuad_neg, neg_pos, twoWindowMap_apply]
    exact hermQuad_twoWindowVec_neg χ u hp hsep hω hN ha
  have hrank := finrank_le_posIndex hW
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun] at hrank
  exact (Nat.cast_le.mpr hrank).trans (hermNegIndex_gram_le_negIndex k x)

/-! ### Outer normalization: every pair may be written with `|χ_j(u)| > 1` -/

/-- Replace `χ_j` by its reflection when `|χ_j(u)| < 1`. -/
def outer (j : Fin J) : G →* ℂ := if 1 < ‖χ j u‖ then χ j else reflect (χ j)

/-- The weight matching `outer`. -/
def outerWeight (ω : Fin J → ℂ) (j : Fin J) : ℂ := if 1 < ‖χ j u‖ then ω j else conj (ω j)

theorem hypPair_outer (ω : Fin J → ℂ) (j : Fin J) :
    hypPair (outer χ u j) (outerWeight χ u ω j) = hypPair (χ j) (ω j) := by
  unfold outer outerWeight
  split_ifs
  · rfl
  · exact hypPair_reflect _ _

theorem outerWeight_ne_zero {ω : Fin J → ℂ} (hω : ∀ j, ω j ≠ 0) (j : Fin J) :
    outerWeight χ u ω j ≠ 0 := by
  unfold outerWeight
  split_ifs
  · exact hω j
  · simpa using hω j

theorem one_lt_norm_outer (hsep : SeparatedAt χ u) (j : Fin J) : 1 < ‖outer χ u j u‖ := by
  unfold outer
  split_ifs with h
  · exact h
  · have hne := norm_ne_one_of_separatedAt χ u hsep j
    have hlt : ‖χ j u‖ < 1 := lt_of_le_of_ne (not_lt.mp h) hne
    have hpos : 0 < ‖χ j u‖ := norm_pos_iff.mpr (char_ne_zero _ _)
    rw [norm_reflect_apply]
    exact (one_lt_inv₀ hpos).mpr hlt

/-- The outer normalization permutes the nodes, so separation is preserved. -/
theorem separatedAt_outer (hsep : SeparatedAt χ u) : SeparatedAt (outer χ u) u := by
  classical
  let σ : Fin J ⊕ Fin J → Fin J ⊕ Fin J :=
    Sum.elim (fun j => if 1 < ‖χ j u‖ then Sum.inl j else Sum.inr j)
      (fun j => if 1 < ‖χ j u‖ then Sum.inr j else Sum.inl j)
  have hσ : Function.LeftInverse σ σ := by
    intro s
    rcases s with j | j <;> simp only [σ, Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all
  have heq : nodes (outer χ u) u = nodes χ u ∘ σ := by
    funext s
    rcases s with j | j <;>
      simp only [nodes, outer, σ, Function.comp, Sum.elim_inl, Sum.elim_inr] <;>
      split_ifs <;> simp
  show Function.Injective (nodes (outer χ u) u)
  rw [heq]
  exact hsep.comp hσ.injective

end Lower

/-! ### The index formula and the hyperbolic plane law -/

section Formula

variable {J : ℕ}

/-- **Index formula.** For a positive-definite kernel `p`, nonzero weights and pairs separated at
some element `u`, `κ(p + Σ_j h_{χ_j,ω_j}) = J`: the negative index of a Krein–Langer kernel is the
number of its hyperbolic pairs. -/
theorem negIndex_posDef_add_hypPairs_eq {p : G → ℂ} (hp : IsPosDefOnGroup p)
    (χ : Fin J → G →* ℂ) {ω : Fin J → ℂ} (hω : ∀ j, ω j ≠ 0) {u : G} (hsep : SeparatedAt χ u) :
    negIndex (fun v => p v + ∑ j, hypPair (χ j) (ω j) v) = J := by
  apply le_antisymm
  · simpa using negIndex_posDef_add_hypPairs_le hp χ ω
  · have hk : (fun v => p v + ∑ j, hypPair (χ j) (ω j) v) =
        fun v => p v + ∑ j, hypPair (outer χ u j) (outerWeight χ u ω j) v := by
      funext v
      simp only [hypPair_outer]
    rw [hk]
    exact le_negIndex_of_outer (outer χ u) u hp (outerWeight_ne_zero χ u hω)
      (one_lt_norm_outer χ u hsep) (separatedAt_outer χ u hsep)

/-- Every pair survives any positive-definite addition: the index of a Krein–Langer kernel with `J`
separated pairs is at least `J`, whatever the positive part. -/
theorem le_negIndex_posDef_add_hypPairs {p : G → ℂ} (hp : IsPosDefOnGroup p)
    (χ : Fin J → G →* ℂ) {ω : Fin J → ℂ} (hω : ∀ j, ω j ≠ 0) {u : G} (hsep : SeparatedAt χ u) :
    (J : ℕ∞) ≤ negIndex (fun v => p v + ∑ j, hypPair (χ j) (ω j) v) :=
  (negIndex_posDef_add_hypPairs_eq hp χ hω hsep).ge

/-- The zero kernel is positive definite. -/
theorem isPosDefOnGroup_zero : IsPosDefOnGroup (fun _ : G => (0 : ℂ)) :=
  fun _ _ _ => ⟨0, le_rfl, by simp⟩

/-- A single pair is separated at `u` iff `|χ(u)| ≠ 1`. -/
theorem separatedAt_single {χ : G →* ℂ} {u : G} (hu : ‖χ u‖ ≠ 1) :
    SeparatedAt (fun _ : Fin 1 => χ) u := by
  have hne : χ u ≠ reflect χ u := by
    intro h
    apply hu
    have h2 : χ u * conj (χ u) = 1 := by
      rw [reflect_apply] at h
      have hc : conj (χ u) ≠ 0 := by simpa using char_ne_zero χ u
      rw [h]
      exact inv_mul_cancel₀ hc
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
    have h3 : ‖χ u‖ ^ 2 = 1 := by exact_mod_cast h2
    have h0 := norm_nonneg (χ u)
    nlinarith
  intro s t hst
  rcases s with i | i <;> rcases t with i' | i'
  · rw [Subsingleton.elim i i']
  · exact absurd hst hne
  · exact absurd hst.symm hne
  · rw [Subsingleton.elim i i']

/-- **Hyperbolic plane law, non-unitary case.** A pair with nonzero weight whose character leaves
the unit circle somewhere has index exactly one. -/
theorem negIndex_hypPair_eq_one (χ : G →* ℂ) {ω : ℂ} (hω : ω ≠ 0) {u : G} (hu : ‖χ u‖ ≠ 1) :
    negIndex (hypPair χ ω) = 1 := by
  have h := negIndex_posDef_add_hypPairs_eq isPosDefOnGroup_zero (fun _ : Fin 1 => χ)
    (ω := fun _ => ω) (fun _ => hω) (separatedAt_single hu)
  have hk : (fun v => (0 : ℂ) + ∑ _j : Fin 1, hypPair χ ω v) = hypPair χ ω := by
    funext v
    simp
  rw [hk] at h
  simpa using h

/-- **Hyperbolic plane law, unitary case.** For a unitary character the pair kernel is
`2 Re ω · χ`, positive definite when `Re ω ≥ 0`. -/
theorem negIndex_hypPair_eq_zero_of_unitary (χ : G →* ℂ) (hχ : ∀ v, ‖χ v‖ = 1) {ω : ℂ}
    (hω : 0 ≤ ω.re) : negIndex (hypPair χ ω) = 0 := by
  have hr : reflect χ = χ := by
    ext v
    exact reflect_apply_of_norm_eq_one (hχ v)
  rw [negIndex_eq_zero_iff]
  intro n x c
  rw [hermQuad_gram_hypPair, hr, mul_assoc, Complex.mul_conj]
  have : (ω * (Complex.normSq (evalChar χ x c) : ℂ)).re = ω.re * Complex.normSq (evalChar χ x c) := by
    rw [mul_comm, Complex.re_ofReal_mul, mul_comm]
  rw [this]
  have := Complex.normSq_nonneg (evalChar χ x c)
  positivity

end Formula

end GaloisForLFunctions.HeckeKreinToeplitz
