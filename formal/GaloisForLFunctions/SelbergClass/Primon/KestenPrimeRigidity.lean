import GaloisForLFunctions.SelbergClass.Primon.KestenFiniteGreenBoundary
import GaloisForLFunctions.SelbergClass.Primon.KestenProjectiveShape
import GaloisForLFunctions.HTGeometry.LinearAlgebra.MatrixProjectiveShape
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Prime rigidity of finite Kesten Green clocks

For sections with at least two character coordinates, algebra transport up to
an arbitrary real scalar preserves both the prime and the scalar. Positivity
of the scalar follows from the positive trace. The determinant-to-trace ratio
of the precision matrix then identifies the prime by strict monotonicity.

The one-coordinate section is exactly `(p+1)⁻¹`, so two primes are related by
the unique scalar `(r+1)/(p+1)`. These two cases give a complete classification.
On a connected graph at positive depth, compatible transports consequently
force a constant prime assignment and every edge scalar to be one. The
algebra automorphisms themselves may still have nontrivial holonomy.
-/

noncomputable section
open _root_.RHTower Matrix GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.SelbergClass.Primon

/-- Every added coordinate contributes one factor of the prime to the precision determinant. -/
theorem det_kestenFiniteGreen_inverse (p : Nat.Primes) (n : ℕ) :
    ((kestenFiniteGreen p n)⁻¹).det = (p : ℝ) ^ n * ((p : ℝ) + 1) := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, det_kestenFiniteGreen]
  simp only [primeReciprocal, inv_pow, div_eq_mul_inv]
  rw [pow_succ]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  field_simp [hp]

/-- The precision trace retains the initial defect and terminal tail correction. -/
theorem trace_kestenFiniteGreen_inverse (p : Nat.Primes) (n : ℕ) :
    ((kestenFiniteGreen p n)⁻¹).trace =
      ((n : ℝ) + 1) * (p : ℝ) + (n : ℝ) / (p : ℝ) + 1 := by
  have hd (i : Fin (n + 1)) :
      (kestenFiniteGreen p n)⁻¹ i i =
        (kestenGreenParameter p - 2) + (if i = 0 then 1 else 0) -
          (if i = Fin.last n then primeReciprocal p else 0) := by
    rw [kestenFiniteGreen_inverse_diagonal]
    split_ifs <;> ring
  simp only [Matrix.trace, Matrix.diag_apply, hd, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [kestenGreenParameter_eq]
  simp only [primeReciprocal, Nat.cast_add, Nat.cast_one]
  ring

/-- Every Green diagonal entry is strictly positive. -/
theorem trace_kestenFiniteGreen_pos (p : Nat.Primes) (n : ℕ) :
    0 < (kestenFiniteGreen p n).trace := by
  apply Finset.sum_pos
  · intro i _
    exact kestenGreenEntry_pos p i i
  · exact Finset.univ_nonempty

/-- The actual precision matrix realizes the strictly monotone projective coordinate. -/
theorem matrixProjectiveShape_kestenFiniteGreen_inverse (p : Nat.Primes) (n : ℕ) :
    matrixProjectiveShape ((kestenFiniteGreen p n)⁻¹) = kestenProjectiveShape n (p : ℝ) := by
  rw [matrixProjectiveShape, det_kestenFiniteGreen_inverse, trace_kestenFiniteGreen_inverse,
    Fintype.card_fin]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have ht : ((n : ℝ) + 1) * (p : ℝ) + (n : ℝ) / (p : ℝ) + 1 =
      kestenPrecisionTraceNumerator n (p : ℝ) / (p : ℝ) := by
    unfold kestenPrecisionTraceNumerator
    field_simp [hp]
    ring
  rw [ht, div_pow, div_div_eq_mul_div, kestenProjectiveShape]
  congr 1
  rw [show 2 * n + 1 = n + (n + 1) by omega, pow_add]
  ring

/-- A compatible real scale is automatically positive because algebra transport preserves trace. -/
theorem kestenFiniteGreen_scale_pos (p r : Nat.Primes) (n : ℕ)
    (e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ₐ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (hscale : e (kestenFiniteGreen p n) = q • kestenFiniteGreen r n) : 0 < q := by
  have ht := congrArg Matrix.trace hscale
  rw [matrixAlgEquiv_trace, Matrix.trace_smul, smul_eq_mul] at ht
  exact (mul_pos_iff_of_pos_right (trace_kestenFiniteGreen_pos r n)).mp
    (ht ▸ trace_kestenFiniteGreen_pos p n)

/-- With at least two coordinates, scalar algebra transport forces equal primes and unit scale. -/
theorem kestenFiniteGreen_prime_rigid (p r : Nat.Primes) (n : ℕ) (hn : 0 < n)
    (e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ₐ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (q : ℝ) (hscale : e (kestenFiniteGreen p n) = q • kestenFiniteGreen r n) :
    p = r ∧ q = 1 := by
  have hq := kestenFiniteGreen_scale_pos p r n e q hscale
  have hinv := matrixAlgEquiv_inverse_of_scale e (kestenFiniteGreen p n)
    (kestenFiniteGreen r n) (isUnit_iff_ne_zero.mpr (det_kestenFiniteGreen_pos p n).ne')
    (isUnit_iff_ne_zero.mpr (det_kestenFiniteGreen_pos r n).ne') q hq.ne' hscale
  -- Inversion removes the covariance normalization; the projective ratio identifies the prime.
  have hs : kestenProjectiveShape n (p : ℝ) = kestenProjectiveShape n (r : ℝ) := by
    rw [← matrixProjectiveShape_kestenFiniteGreen_inverse,
      ← matrixProjectiveShape_kestenFiniteGreen_inverse]
    calc
      _ = matrixProjectiveShape (e (kestenFiniteGreen p n)⁻¹) :=
        (matrixProjectiveShape_algEquiv e _).symm
      _ = matrixProjectiveShape (q⁻¹ • (kestenFiniteGreen r n)⁻¹) := congrArg _ hinv
      _ = _ := matrixProjectiveShape_smul _ _ (inv_ne_zero hq.ne')
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hr : 0 < (r : ℝ) := by exact_mod_cast r.property.pos
  have hpr : (p : ℝ) = (r : ℝ) :=
    (strictMonoOn_kestenProjectiveShape n hn).injOn hp hr hs
  have hpr' : p = r := Subtype.ext (Nat.cast_injective hpr)
  refine ⟨hpr', ?_⟩
  subst r
  have ht := congrArg Matrix.trace hscale
  rw [matrixAlgEquiv_trace, Matrix.trace_smul, smul_eq_mul] at ht
  exact mul_right_cancel₀ (trace_kestenFiniteGreen_pos p n).ne'
    (by simpa only [one_mul] using ht.symm)

/-- The one-coordinate Green section is a scalar matrix. -/
theorem kestenFiniteGreen_zero_scalar (p : Nat.Primes) :
    kestenFiniteGreen p 0 = ((p : ℝ) + 1)⁻¹ • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hp1 : 0 < (p : ℝ) + 1 := add_pos hp zero_lt_one
  have h00 : kestenFiniteGreen p 0 0 0 = ((p : ℝ) + 1)⁻¹ := by
    calc
      _ = (kestenFiniteGreen p 0).det := (Matrix.det_fin_one (kestenFiniteGreen p 0)).symm
      _ = _ := by
        rw [det_kestenFiniteGreen]
        simp only [zero_add, pow_one, primeReciprocal]
        field_simp [hp.ne', hp1.ne']
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 0 := Fin.ext (by omega)
  subst i
  subst j
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using h00

/-- Exact classification of all prime pairs and real scales admitting algebra transport. -/
theorem kestenFiniteGreen_algEquiv_scale_iff (p r : Nat.Primes) (n : ℕ) (q : ℝ) :
    (∃ e : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ₐ[ℝ]
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      e (kestenFiniteGreen p n) = q • kestenFiniteGreen r n) ↔
      (n = 0 ∧ q = ((r : ℝ) + 1) / ((p : ℝ) + 1)) ∨
        (0 < n ∧ p = r ∧ q = 1) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hr : 0 < (r : ℝ) := by exact_mod_cast r.property.pos
  have hp1 : (p : ℝ) + 1 ≠ 0 := (add_pos hp zero_lt_one).ne'
  have hr1 : (r : ℝ) + 1 ≠ 0 := (add_pos hr zero_lt_one).ne'
  constructor
  · rintro ⟨e, he⟩
    by_cases hn : n = 0
    · left
      refine ⟨hn, ?_⟩
      subst n
      rw [kestenFiniteGreen_zero_scalar, kestenFiniteGreen_zero_scalar,
        map_smul, map_one, smul_smul] at he
      have hh := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℝ => M 0 0) he
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hh
      apply (eq_div_iff hp1).mpr
      field_simp [hp1, hr1] at hh
      linarith only [hh]
    · exact Or.inr ⟨Nat.pos_of_ne_zero hn, kestenFiniteGreen_prime_rigid p r n
        (Nat.pos_of_ne_zero hn) e q he⟩
  · rintro (⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩)
    · refine ⟨AlgEquiv.refl, ?_⟩
      change kestenFiniteGreen p 0 = _
      rw [kestenFiniteGreen_zero_scalar, kestenFiniteGreen_zero_scalar, smul_smul]
      congr 1
      field_simp [hp1, hr1]
    · exact ⟨AlgEquiv.refl, (one_smul ℝ _).symm⟩

/-- Compatible positive-depth networks have one prime throughout and unit edge scales. -/
theorem kestenNetwork_prime_rigid {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) (root : V) (n : ℕ) (hn : 0 < n)
    (prime : V → Nat.Primes) (c : V → V → ℝ)
    (t : V → V → (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ≃ₐ[ℝ]
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ))
    (ht : ∀ {u v}, G.Adj u v → t u v (kestenFiniteGreen (prime v) n) =
      c u v • kestenFiniteGreen (prime u) n) :
    (∀ v, prime v = prime root) ∧ (∀ {u v}, G.Adj u v → c u v = 1) := by
  have hedge {u v : V} (h : G.Adj u v) : prime v = prime u ∧ c u v = 1 :=
    kestenFiniteGreen_prime_rigid (prime v) (prime u) n hn (t u v) (c u v) (ht h)
  refine ⟨?_, fun h => (hedge h).2⟩
  intro v
  obtain ⟨p⟩ := hG root v
  induction p with
  | nil => rfl
  | cons h p ih => exact ih.trans (hedge h).1

end GaloisForLFunctions.SelbergClass.Primon

#print axioms GaloisForLFunctions.SelbergClass.Primon.matrixProjectiveShape_kestenFiniteGreen_inverse
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenFiniteGreen_algEquiv_scale_iff
#print axioms GaloisForLFunctions.SelbergClass.Primon.kestenNetwork_prime_rigid
