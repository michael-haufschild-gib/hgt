import GaloisForLFunctions.HTGeometry.SimplexTestSet
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Realizable-coefficient surjectivity for the friable auxiliary

At the arithmetic edge `s = 1` the `T`-th derivative of a friable Dirichlet polynomial is a
`ℚ`-linear form in the degree-`T` monomials of the prime logarithms, with coefficients

`C_a = (multinomial) · Σ_m λ_m (∏_p m_p^{a_p}) / n_m`.

This file proves that the coefficient map `λ ↦ (C_a)` is **surjective**: every `ℚ`-linear form in
degree-`T` prime-log monomials is realized by a friable auxiliary of degree at most `d ≥ T`.  There
is therefore no bypass — controlling the edge magnitude for the realizable forms is controlling it
for *all* of them.

The mathematical content is that the rows `v_a = ((∏_p m_p^{a_p})/n_m)_m` are linearly independent.
Clearing the nonzero denominators `n_m` turns this into: a combination of distinct degree-`T`
monomials vanishing on the lattice simplex `{‖m‖₁ ≤ d}` has zero coefficients — which is the simplex
test-set theorem.

Surjectivity itself follows from row independence by finite-dimensional duality.

## Main results

* `friableRow_linearIndependent` — the rows are linearly independent;
* `friableCoefficientMap_surjective` — hence the coefficient map is surjective;
* `friableCoefficientMap_weighted_surjective` — the multinomial-weighted form;
* `friable_no_soft_spot` — the range is everything at every truncation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {n : ℕ}

/-- The lattice simplex of exponent vectors of `ℓ¹`-degree at most `d`, as a finite set. -/
def simplexFinset (n d : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (d + 1)).filter fun m => ∑ i, m i ≤ d

theorem mem_simplexFinset {d : ℕ} {m : Fin n → ℕ} :
    m ∈ simplexFinset n d ↔ ∑ i, m i ≤ d := by
  classical
  unfold simplexFinset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    rw [Finset.mem_range]
    have : m i ≤ ∑ j, m j := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    omega

/-- The friable modulus `n_m = ∏ p^{m_p}` of an exponent vector. -/
def friableModulus (p : Fin n → ℕ) (m : Fin n → ℕ) : ℕ := ∏ i, (p i) ^ (m i)

theorem friableModulus_pos {p : Fin n → ℕ} (hp : ∀ i, 0 < p i) (m : Fin n → ℕ) :
    0 < friableModulus p m :=
  Finset.prod_pos fun i _ => pow_pos (hp i) _

/-- The row of the edge-coefficient matrix attached to a degree-`T` log-monomial index `a`. -/
def friableRow (p : Fin n → ℕ) (a : Fin n →₀ ℕ) (m : Fin n → ℕ) : ℚ :=
  (∏ i, ((m i : ℕ) : ℚ) ^ (a i)) / ((friableModulus p m : ℕ) : ℚ)

/-- **The rows are linearly independent.**  A vanishing `ℚ`-combination of the rows of the edge
matrix, over the whole simplex of degree bound `d ≥ T`, has zero coefficients. -/
theorem friableRow_linearIndependent {T d : ℕ} (hd : T ≤ d) {p : Fin n → ℕ}
    (hp : ∀ i, 0 < p i) (A : Finset (Fin n →₀ ℕ))
    (hA : ∀ a ∈ A, (a.sum fun _ e => e) ≤ T) (kappa : (Fin n →₀ ℕ) → ℚ)
    (hzero : ∀ m : Fin n → ℕ, (∑ i, m i) ≤ d →
      ∑ a ∈ A, kappa a * friableRow p a m = 0) :
    ∀ a ∈ A, kappa a = 0 := by
  classical
  refine coeff_eq_zero_of_monomialSum_vanishes_on_simplex hd A hA kappa (fun m hm => ?_)
  have hden : ((friableModulus p m : ℕ) : ℚ) ≠ 0 := by
    have := friableModulus_pos hp m
    exact_mod_cast this.ne'
  have h := hzero m hm
  have hmul := congrArg (fun z : ℚ => z * ((friableModulus p m : ℕ) : ℚ)) h
  simp only [zero_mul, Finset.sum_mul] at hmul
  rw [← hmul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [friableRow]
  field_simp

/-- The edge-coefficient map: a friable coefficient vector supported on the simplex is sent to the
family of its degree-`T` log-monomial coefficients. -/
def friableCoefficientMap {d : ℕ} (p : Fin n → ℕ) (A : Finset (Fin n →₀ ℕ)) :
    ((simplexFinset n d) → ℚ) →ₗ[ℚ] (A → ℚ) where
  toFun lam := fun a => ∑ m : (simplexFinset n d), lam m * friableRow p (a : Fin n →₀ ℕ) (m : Fin n → ℕ)
  map_add' lam mu := by
    funext a
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  map_smul' c lam := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)

/-- **Realizable-coefficient surjectivity.**  Every family of degree-`T` log-monomial coefficients is
realized by a friable auxiliary supported on the simplex of degree bound `d ≥ T`. -/
theorem friableCoefficientMap_surjective {T d : ℕ} (hd : T ≤ d) {p : Fin n → ℕ}
    (hp : ∀ i, 0 < p i) (A : Finset (Fin n →₀ ℕ))
    (hA : ∀ a ∈ A, (a.sum fun _ e => e) ≤ T) :
    Function.Surjective (friableCoefficientMap (d := d) p A) := by
  classical
  rw [← LinearMap.dualMap_injective_iff]
  intro phi psi hphi
  refine LinearMap.ext (fun psi' => ?_)
  -- expand `psi'` in the coordinate basis of `A → ℚ`
  set kappa : (Fin n →₀ ℕ) → ℚ := fun a => if h : a ∈ A then phi (Pi.single ⟨a, h⟩ 1) else 0
    with hkappa
  set kappa2 : (Fin n →₀ ℕ) → ℚ := fun a => if h : a ∈ A then psi (Pi.single ⟨a, h⟩ 1) else 0
    with hkappa2
  have hexpand : ∀ (chi : Module.Dual ℚ (A → ℚ)) (f : A → ℚ),
      chi f = ∑ a : A, f a * chi (Pi.single a 1) := by
    intro chi f
    have hf : f = ∑ a : A, f a • (Pi.single a 1 : A → ℚ) := by
      funext b
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hcb
        simp [hcb]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    calc chi f = chi (∑ a : A, f a • (Pi.single a 1 : A → ℚ)) := by rw [← hf]
      _ = ∑ a : A, f a * chi (Pi.single a 1) := by
          rw [map_sum]
          exact Finset.sum_congr rfl (fun a _ => by rw [map_smul, smul_eq_mul])
  -- the transposed relation on each simplex point
  have hrow : ∀ m ∈ simplexFinset n d,
      ∑ a ∈ A, (kappa a - kappa2 a) * friableRow p a m = 0 := by
    intro m hm
    have hcoord := congrArg (fun (chi : Module.Dual ℚ _) => chi (Pi.single ⟨m, hm⟩ 1)) hphi
    simp only [LinearMap.dualMap_apply] at hcoord
    have hval : ∀ (chi : Module.Dual ℚ (A → ℚ)),
        chi (friableCoefficientMap (d := d) p A (Pi.single ⟨m, hm⟩ 1))
          = ∑ a ∈ A, (if h : a ∈ A then chi (Pi.single ⟨a, h⟩ 1) else 0) * friableRow p a m := by
      intro chi
      rw [hexpand chi]
      rw [← Finset.sum_attach A (fun a => (if h : a ∈ A then chi (Pi.single ⟨a, h⟩ 1) else 0)
        * friableRow p a m)]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have hcomp : (friableCoefficientMap (d := d) p A (Pi.single ⟨m, hm⟩ 1)) a
          = friableRow p (a : Fin n →₀ ℕ) m := by
        show (∑ m' : ↥(simplexFinset n d),
          (Pi.single (⟨m, hm⟩ : ↥(simplexFinset n d)) (1 : ℚ) :
            ↥(simplexFinset n d) → ℚ) m'
            * friableRow p (a : Fin n →₀ ℕ) (m' : Fin n → ℕ)) = _
        rw [Finset.sum_eq_single (⟨m, hm⟩ : (simplexFinset n d))]
        · simp
        · intro c _ hc
          simp [hc]
        · intro hb
          exact absurd (Finset.mem_univ (⟨m, hm⟩ : (simplexFinset n d))) hb
      rw [hcomp, dif_pos a.2]
      ring
    have h1 := hval phi
    have h2 := hval psi
    rw [hcoord] at h1
    rw [h1] at h2
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hkappa2, hkappa]
    ring
  have hkap := friableRow_linearIndependent hd hp A hA (fun a => kappa a - kappa2 a)
    (fun m hm => hrow m (mem_simplexFinset.mpr hm))
  rw [hexpand phi psi', hexpand psi psi']
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have := hkap (a : Fin n →₀ ℕ) a.2
  rw [hkappa, hkappa2] at this
  simp only [dif_pos a.2] at this
  have heq : phi (Pi.single a 1) = psi (Pi.single a 1) := by
    have h0 : phi (Pi.single ⟨(a : Fin n →₀ ℕ), a.2⟩ 1)
        - psi (Pi.single ⟨(a : Fin n →₀ ℕ), a.2⟩ 1) = 0 := this
    have hsub : (⟨(a : Fin n →₀ ℕ), a.2⟩ : A) = a := Subtype.ext rfl
    rw [hsub] at h0
    linarith
  rw [heq]

/-- **The multinomial-weighted coefficient map is surjective as well.**  The card's `C_a` differ from
`friableCoefficientMap` by the nonzero multinomial factors `T!/∏ a_p!`, and rescaling coordinates by
nonzero scalars preserves surjectivity. -/
theorem friableCoefficientMap_weighted_surjective {T d : ℕ} (hd : T ≤ d) {p : Fin n → ℕ}
    (hp : ∀ i, 0 < p i) (A : Finset (Fin n →₀ ℕ))
    (hA : ∀ a ∈ A, (a.sum fun _ e => e) ≤ T) (w : A → ℚ) (hw : ∀ a, w a ≠ 0) :
    Function.Surjective
      (fun lam : ↥(simplexFinset n d) → ℚ =>
        fun a : A => w a * friableCoefficientMap (d := d) p A lam a) := by
  intro c
  obtain ⟨lam, hlam⟩ := friableCoefficientMap_surjective hd hp A hA (fun a => c a / w a)
  refine ⟨lam, ?_⟩
  funext a
  have := congrFun hlam a
  simp only at this ⊢
  rw [this]
  rw [mul_div_assoc']
  exact mul_div_cancel_left₀ (c a) (hw a)

/-- **No soft spot.**  For *every* finite prime set and *every* degree `T`, with any degree bound
`d ≥ T`, the realizable coefficients span the full degree-`T` log-monomial space: there is no
truncation of the edge problem whose realizable forms are a proper subspace. -/
theorem friable_no_soft_spot {T d : ℕ} (hd : T ≤ d) {p : Fin n → ℕ}
    (hp : ∀ i, 0 < p i) (A : Finset (Fin n →₀ ℕ))
    (hA : ∀ a ∈ A, (a.sum fun _ e => e) ≤ T) :
    LinearMap.range (friableCoefficientMap (d := d) p A) = ⊤ :=
  LinearMap.range_eq_top.mpr (friableCoefficientMap_surjective hd hp A hA)

end GaloisForLFunctions.HTGeometry
