import GaloisForLFunctions.RHTower.QuartetSymmetryJets
import GaloisForLFunctions.RHTower.QuartetPassportRealizer
import GaloisForLFunctions.RHTower.EnvelopeJetAgreement
import GaloisForLFunctions.RHTower.FiniteHermiteCRT
import GaloisForLFunctions.RHTower.ImaginaryAxisPositiveRepair
import GaloisForLFunctions.RHTower.DeningerArithmeticFiniteJetInterpolation

/-!
# Arbitrary finite quartet-passport realization: the capstone

This module assembles the pieces of the arbitrary-finite-quartet-passport realization.

`quartetPoint α : Fin 4 → ℂ` lists the four points `α, -α, conj α, -conj α`, and `neg4`, `conj4`
are the two induced involutions of the four slots.  `quartetTarget P` generates the four target
jets of a quartet from the single base one by `P`, `P ∘ (-X)`, `P̄`, `P̄ ∘ (-X)`; with that choice
the two equivariance hypotheses of `FiniteHermiteCRT` become the polynomial identities
`quartetTarget_jet_neg` and `quartetTarget_jet_conj`, proved from `QuartetSymmetryJets`, rather
than analytic computations at each of the four points.

`exists_quartet_passport_polynomial` runs the equivariant Hermite interpolation against
`quartetBasePoly` — the local Taylor representative of `(z-α)/A(z)` — and then the global positive
repair, producing a real-even, Schwarz-real polynomial `B` that is strictly positive real on the
whole imaginary axis and still carries every prescribed jet.  The repair term does not disturb the
jets because `(X - α_j)^{N_j+2}` divides the packet polynomial
(`X_sub_C_pow_dvd_simultaneousFlatPolynomial`, `iterate_derivative_eval_eq_zero_of_pow_dvd`).

`exists_quartet_passport_realizer` is the card's positive theorem: `F = A · B` is even,
Schwarz-real, aperiodic, zero-free on the imaginary axis, and its germ at each quartet head agrees
with the simple linear germ `z - α_j` through order `N_j + 1`.  Exact order one, the strip-coordinate
functional equation, and the absence of nonzero quasi-periods come from
`RHTower/QuartetPassportRealizer.lean`.

**A note on the repair interface.**  The packaged
`exists_scalar_add_simultaneousFlatPolynomial_pos_real_on_imaginaryAxis` is *not* usable: its
hypothesis `∀ i y, (y : ℂ)^2 + (α i)^2 ≠ 0` binds `y` at type `ℂ` (the ascription is a no-op), and
that is unsatisfiable, since `y = ± i α i` is a root.  The intended reading quantifies `y` over `ℝ`.
This capstone therefore calls the primitive `exists_scalar_add_mul_pos_real_on_imaginaryAxis`
directly and supplies packet positivity from `simultaneousFlatPolynomial_mul_I_pos_real`, whose
`y : ℝ` is a genuine parameter.
-/

noncomputable section

open Complex Polynomial

namespace RHTower



/-! ## The four points of a quartet -/

/-- The four points `α, -α, conj α, -conj α` of a quartet. -/
private def quartetPoint (α : ℂ) : Fin 4 → ℂ
  | 0 => α
  | 1 => -α
  | 2 => (starRingEnd ℂ) α
  | 3 => -((starRingEnd ℂ) α)

/-- The reflection `z ↦ -z` as a permutation of the four quartet slots. -/
def neg4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The Schwarz reflection as a permutation of the four quartet slots. -/
def conj4 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The alternating sign attached to the four slots. -/
def sign4 : Fin 4 → ℂ
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => -1

theorem neg4_apply : ∀ k : Fin 4, neg4 k = if k = 0 then 1 else if k = 1 then 0
    else if k = 2 then 3 else 2 := by decide

theorem conj4_apply : ∀ k : Fin 4, conj4 k = if k = 0 then 2 else if k = 1 then 3
    else if k = 2 then 0 else 1 := by decide

theorem quartetPoint_neg4 (α : ℂ) (k : Fin 4) :
    quartetPoint α (neg4 k) = -(quartetPoint α k) := by
  fin_cases k <;> simp [quartetPoint, neg4, Equiv.swap_apply_def]

theorem quartetPoint_conj4 (α : ℂ) (k : Fin 4) :
    quartetPoint α (conj4 k) = (starRingEnd ℂ) (quartetPoint α k) := by
  fin_cases k <;> simp [quartetPoint, conj4, Equiv.swap_apply_def]

theorem sign4_neg4 (k : Fin 4) : sign4 (neg4 k) = -(sign4 k) := by
  fin_cases k <;> simp [sign4, neg4, Equiv.swap_apply_def]

theorem sign4_conj4 (k : Fin 4) : sign4 (conj4 k) = (starRingEnd ℂ) (sign4 k) := by
  fin_cases k <;> simp [sign4, conj4, Equiv.swap_apply_def]

theorem neg4_involutive : ∀ k : Fin 4, neg4 (neg4 k) = k := by decide

theorem conj4_involutive : ∀ k : Fin 4, conj4 (conj4 k) = k := by decide


/-! ## The four target polynomials of a quartet -/

/-- The four target jets of a quartet, generated from the base one by the two symmetries. -/
def quartetTarget (P : Polynomial ℂ) : Fin 4 → Polynomial ℂ
  | 0 => P
  | 1 => P.comp (-X)
  | 2 => P.map (starRingEnd ℂ)
  | 3 => (P.map (starRingEnd ℂ)).comp (-X)

theorem conj_neg_one_pow (n : ℕ) : (starRingEnd ℂ) ((-1 : ℂ) ^ n) = (-1 : ℂ) ^ n := by
  rw [map_pow, map_neg, map_one]

theorem neg_one_pow_sq (n : ℕ) : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- The reflection compatibility required by the equivariant Hermite interpolation. -/
theorem quartetTarget_jet_neg (P : Polynomial ℂ) (α : ℂ) (k : Fin 4) (n : ℕ) :
    (Polynomial.derivative^[n] (quartetTarget P (neg4 k))).eval (quartetPoint α (neg4 k))
      = (-1) ^ n * (Polynomial.derivative^[n] (quartetTarget P k)).eval (quartetPoint α k) := by
  have hsq := neg_one_pow_sq n
  fin_cases k
  · show (Polynomial.derivative^[n] (quartetTarget P 1)).eval (quartetPoint α 1)
      = (-1) ^ n * (Polynomial.derivative^[n] (quartetTarget P 0)).eval (quartetPoint α 0)
    simp only [quartetTarget, quartetPoint]
    exact iterate_derivative_comp_neg_eval P n α
  · show (Polynomial.derivative^[n] (quartetTarget P 0)).eval (quartetPoint α 0)
      = (-1) ^ n * (Polynomial.derivative^[n] (quartetTarget P 1)).eval (quartetPoint α 1)
    simp only [quartetTarget, quartetPoint]
    rw [iterate_derivative_comp_neg_eval P n α, ← mul_assoc, hsq, one_mul]
  · show (Polynomial.derivative^[n] (quartetTarget P 3)).eval (quartetPoint α 3)
      = (-1) ^ n * (Polynomial.derivative^[n] (quartetTarget P 2)).eval (quartetPoint α 2)
    simp only [quartetTarget, quartetPoint]
    exact iterate_derivative_comp_neg_eval (P.map (starRingEnd ℂ)) n ((starRingEnd ℂ) α)
  · show (Polynomial.derivative^[n] (quartetTarget P 2)).eval (quartetPoint α 2)
      = (-1) ^ n * (Polynomial.derivative^[n] (quartetTarget P 3)).eval (quartetPoint α 3)
    simp only [quartetTarget, quartetPoint]
    rw [iterate_derivative_comp_neg_eval (P.map (starRingEnd ℂ)) n ((starRingEnd ℂ) α),
      ← mul_assoc, hsq, one_mul]

/-- The Schwarz compatibility required by the equivariant Hermite interpolation. -/
theorem quartetTarget_jet_conj (P : Polynomial ℂ) (α : ℂ) (k : Fin 4) (n : ℕ) :
    (Polynomial.derivative^[n] (quartetTarget P (conj4 k))).eval (quartetPoint α (conj4 k))
      = (starRingEnd ℂ)
        ((Polynomial.derivative^[n] (quartetTarget P k)).eval (quartetPoint α k)) := by
  fin_cases k
  · show (Polynomial.derivative^[n] (quartetTarget P 2)).eval (quartetPoint α 2)
      = (starRingEnd ℂ) ((Polynomial.derivative^[n] (quartetTarget P 0)).eval (quartetPoint α 0))
    simp only [quartetTarget, quartetPoint]
    exact iterate_derivative_map_conj_eval P n α
  · show (Polynomial.derivative^[n] (quartetTarget P 3)).eval (quartetPoint α 3)
      = (starRingEnd ℂ) ((Polynomial.derivative^[n] (quartetTarget P 1)).eval (quartetPoint α 1))
    simp only [quartetTarget, quartetPoint]
    rw [iterate_derivative_comp_neg_eval (P.map (starRingEnd ℂ)) n ((starRingEnd ℂ) α),
      iterate_derivative_map_conj_eval P n α, iterate_derivative_comp_neg_eval P n α,
      map_mul, conj_neg_one_pow]
  · show (Polynomial.derivative^[n] (quartetTarget P 0)).eval (quartetPoint α 0)
      = (starRingEnd ℂ) ((Polynomial.derivative^[n] (quartetTarget P 2)).eval (quartetPoint α 2))
    simp only [quartetTarget, quartetPoint]
    rw [iterate_derivative_map_conj_eval P n α, Complex.conj_conj]
  · show (Polynomial.derivative^[n] (quartetTarget P 1)).eval (quartetPoint α 1)
      = (starRingEnd ℂ) ((Polynomial.derivative^[n] (quartetTarget P 3)).eval (quartetPoint α 3))
    simp only [quartetTarget, quartetPoint]
    rw [iterate_derivative_comp_neg_eval (P.map (starRingEnd ℂ)) n ((starRingEnd ℂ) α),
      iterate_derivative_map_conj_eval P n α, iterate_derivative_comp_neg_eval P n α,
      map_mul, conj_neg_one_pow, Complex.conj_conj]


/-! ## The repair term does not disturb the prescribed jets -/

theorem X_sub_C_dvd_quartetFlatPolynomial (α : ℂ) (k : Fin 4) :
    (X - Polynomial.C (quartetPoint α k)) ∣ quartetFlatPolynomial α := by
  have hroot : (quartetFlatPolynomial α).IsRoot (quartetPoint α k) := by
    fin_cases k <;>
      simp [quartetFlatPolynomial, quartetPoint, Polynomial.IsRoot, Complex.ext_iff] <;> ring_nf <;>
      simp
  exact Polynomial.dvd_iff_isRoot.mpr hroot

theorem X_sub_C_pow_dvd_simultaneousFlatPolynomial {J : Type} [Fintype J] [DecidableEq J]
    (M : J → ℕ) (α : J → ℂ) (j : J) (k : Fin 4) :
    (X - Polynomial.C (quartetPoint (α j) k)) ^ (M j) ∣ simultaneousFlatPolynomial M α := by
  obtain ⟨Q, hQ⟩ := quartetFlatPolynomial_pow_dvd_simultaneousFlatPolynomial M α j
  obtain ⟨R, hR⟩ := X_sub_C_dvd_quartetFlatPolynomial (α j) k
  refine ⟨R ^ (M j) * Q, ?_⟩
  rw [hQ, hR, mul_pow]
  ring

theorem iterate_derivative_eval_eq_zero_of_pow_dvd {Q : Polynomial ℂ} {w : ℂ} {M n : ℕ}
    (hQ : Q ≠ 0) (hdvd : (X - Polynomial.C w) ^ M ∣ Q) (hn : n < M) :
    (Polynomial.derivative^[n] Q).eval w = 0 := by
  have hmult : M ≤ Polynomial.rootMultiplicity w Q :=
    (Polynomial.le_rootMultiplicity_iff hQ).mpr hdvd
  exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (lt_of_lt_of_le hn hmult)


/-! ## Degrees -/

theorem natDegree_finiteHermiteModulus {ι : Type*} [Fintype ι] (w : ι → ℂ) (m : ι → ℕ) :
    (finiteHermiteModulus w m).natDegree = ∑ i, m i := by
  rw [finiteHermiteModulus, Polynomial.natDegree_prod _ _ (fun i _ =>
    ((Polynomial.monic_X_sub_C (w i)).pow (m i)).ne_zero)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

theorem sum_quartet_index {J : Type} [Fintype J] (N : J → ℕ) :
    ∑ i : J × Fin 4, (N i.1 + 2) = 4 * ∑ j : J, (N j + 2) := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Finset.sum_const, mul_comm]

/-! ## The base local jet polynomial -/

/-- The local Taylor representative of `(z - α)/A(z)` at the head of a quartet. -/
def quartetBasePoly (a : ℝ) (α : ℂ) (N : ℕ) : Polynomial ℂ :=
  deningerLocalJetPolynomial α
    (fun k : Fin (N + 2) =>
      iteratedDeriv k.val (fun z => (z - α) / coshQuartetEnvelope a z) α)

theorem quartetBasePoly_jets (a : ℝ) (α : ℂ) (N : ℕ) {n : ℕ} (hn : n < N + 2) :
    (Polynomial.derivative^[n] (quartetBasePoly a α N)).eval α
      = iteratedDeriv n (fun z => (z - α) / coshQuartetEnvelope a z) α := by
  rw [quartetBasePoly, deningerLocalJetPolynomial_iterateDerivative_eval α _ hn]


/-! ## Symmetries of the packet polynomial -/

theorem quartetFlatPolynomial_eval_neg (α z : ℂ) :
    (quartetFlatPolynomial α).eval (-z) = (quartetFlatPolynomial α).eval z := by
  simp [quartetFlatPolynomial]

theorem quartetFlatPolynomial_eval_conj (α z : ℂ) :
    (quartetFlatPolynomial α).eval ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) ((quartetFlatPolynomial α).eval z) := by
  simp [quartetFlatPolynomial, map_mul, map_sub, map_pow]
  ring

theorem simultaneousFlatPolynomial_eval_neg {J : Type} [Fintype J] (M : J → ℕ) (α : J → ℂ)
    (z : ℂ) :
    (simultaneousFlatPolynomial M α).eval (-z) = (simultaneousFlatPolynomial M α).eval z := by
  simp only [simultaneousFlatPolynomial, Polynomial.eval_prod, Polynomial.eval_pow]
  exact Finset.prod_congr rfl (fun j _ => by rw [quartetFlatPolynomial_eval_neg])

theorem simultaneousFlatPolynomial_eval_conj {J : Type} [Fintype J] (M : J → ℕ) (α : J → ℂ)
    (z : ℂ) :
    (simultaneousFlatPolynomial M α).eval ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) ((simultaneousFlatPolynomial M α).eval z) := by
  simp only [simultaneousFlatPolynomial, Polynomial.eval_prod, Polynomial.eval_pow, map_prod,
    map_pow]
  exact Finset.prod_congr rfl (fun j _ => by rw [quartetFlatPolynomial_eval_conj])


/-! ## The capstone: the interpolating polynomial -/

theorem iterate_derivative_add (P Q : Polynomial ℂ) (n : ℕ) :
    Polynomial.derivative^[n] (P + Q)
      = Polynomial.derivative^[n] P + Polynomial.derivative^[n] Q := by
  induction n generalizing P Q with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        map_add, ih]

theorem exists_quartet_passport_polynomial_of_base {J : Type} [Fintype J] [DecidableEq J]
    (α : J → ℂ) (N : J → ℕ) (base : J → Polynomial ℂ)
    (hαre : ∀ j, (α j).re ≠ 0)
    (hinj : Function.Injective (fun i : J × Fin 4 => quartetPoint (α i.1) i.2)) :
    ∃ B : Polynomial ℂ,
      (∀ z : ℂ, B.eval (-z) = B.eval z) ∧
      (∀ z : ℂ, B.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (B.eval z)) ∧
      (∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ B.eval ((y : ℂ) * I) = (r : ℂ)) ∧
      (∀ (j : J) (n : ℕ), n < N j + 2 →
        (Polynomial.derivative^[n] B).eval (α j)
          = (Polynomial.derivative^[n] (base j)).eval (α j)) := by
  classical
  set w : J × Fin 4 → ℂ := fun i => quartetPoint (α i.1) i.2 with hwdef
  set m : J × Fin 4 → ℕ := fun i => N i.1 + 2 with hmdef
  set target : J × Fin 4 → Polynomial ℂ := fun i => quartetTarget (base i.1) i.2 with htargetdef
  set negIdx : (J × Fin 4) ≃ (J × Fin 4) := (Equiv.refl J).prodCongr neg4 with hnegdef
  set conjIdx : (J × Fin 4) ≃ (J × Fin 4) := (Equiv.refl J).prodCongr conj4 with hconjdef
  obtain ⟨B₀, hdeg₀, heven₀, hreal₀, hjets₀⟩ :=
    exists_real_even_polynomial_iterateDerivative_eval_eq_degree_lt_modulus
      negIdx conjIdx w hinj m target
      (fun i => quartetPoint_neg4 (α i.1) i.2)
      (fun i => quartetPoint_conj4 (α i.1) i.2)
      (fun i => rfl) (fun i => rfl)
      (fun i n _ => quartetTarget_jet_neg (base i.1) (α i.1) i.2 n)
      (fun i n _ => quartetTarget_jet_conj (base i.1) (α i.1) i.2 n)
  set M : J → ℕ := fun j => N j + 2 with hMdef
  set S : Polynomial ℂ := simultaneousFlatPolynomial M α with hSdef
  -- the packet is strictly positive real on the imaginary axis
  have hneY : ∀ (y : ℝ) (j : J), ((y : ℂ) ^ 2) + (α j) ^ 2 ≠ 0 := by
    intro y j hzero
    have hfac : ((α j) + (y : ℂ) * I) * ((α j) - (y : ℂ) * I) = 0 := by
      have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
      calc ((α j) + (y : ℂ) * I) * ((α j) - (y : ℂ) * I)
          = (α j) ^ 2 - ((y : ℂ) ^ 2) * (I : ℂ) ^ 2 := by ring
        _ = (α j) ^ 2 + ((y : ℂ) ^ 2) := by rw [hI]; ring
        _ = 0 := by rw [add_comm]; exact hzero
    rcases mul_eq_zero.mp hfac with h | h
    · have hval : α j = -((y : ℂ) * I) := by linear_combination h
      exact hαre j (by rw [hval]; simp)
    · have hval : α j = (y : ℂ) * I := by linear_combination h
      exact hαre j (by rw [hval]; simp)
  have hSpos : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ S.eval ((y : ℂ) * I) = (r : ℂ) :=
    fun y => simultaneousFlatPolynomial_mul_I_pos_real M α y (hneY y)
  have hSreal : ∀ y : ℝ, (S.eval ((y : ℂ) * I)).im = 0 := by
    intro y
    obtain ⟨r, _, heq⟩ := hSpos y
    rw [heq]
    simp
  have hSre : ∀ y : ℝ, 0 < (S.eval ((y : ℂ) * I)).re := by
    intro y
    obtain ⟨r, hr, heq⟩ := hSpos y
    rw [heq]
    simpa using hr
  have hBreal : ∀ y : ℝ, (B₀.eval ((y : ℂ) * I)).im = 0 := by
    intro y
    have hc : (starRingEnd ℂ) ((y : ℂ) * I) = -((y : ℂ) * I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have h1 := hreal₀ ((y : ℂ) * I)
    rw [hc, heven₀] at h1
    exact (Complex.conj_eq_iff_im.mp h1.symm)
  have hdegree : (imaginaryAxisRealPolynomial B₀).degree
      < (imaginaryAxisRealPolynomial S).degree := by
    refine (degree_imaginaryAxisRealPolynomial_le B₀).trans_lt ?_
    rw [degree_imaginaryAxisRealPolynomial_simultaneousFlatPolynomial]
    have h1 : (finiteHermiteModulus w m).degree = S.degree := by
      rw [Polynomial.degree_eq_natDegree (finiteHermiteModulus_monic w m).ne_zero,
        Polynomial.degree_eq_natDegree (simultaneousFlatPolynomial_monic M α).ne_zero,
        natDegree_finiteHermiteModulus, simultaneousFlatPolynomial_natDegree]
      congr 1
      exact sum_quartet_index N
    rw [← h1]
    exact hdeg₀
  obtain ⟨L, hposL⟩ :=
    exists_scalar_add_mul_pos_real_on_imaginaryAxis B₀ S hBreal hSreal hSre hdegree
  refine ⟨B₀ + Polynomial.C (L : ℂ) * S, ?_, ?_, hposL, ?_⟩
  · intro z
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    rw [heven₀, simultaneousFlatPolynomial_eval_neg]
  · intro z
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, map_add, map_mul]
    rw [hreal₀, simultaneousFlatPolynomial_eval_conj, Complex.conj_ofReal]
  · intro j n hn
    have hS0 : S ≠ 0 := (simultaneousFlatPolynomial_monic M α).ne_zero
    have hdvd : (X - Polynomial.C (α j)) ^ (M j) ∣ S := by
      have hd := X_sub_C_pow_dvd_simultaneousFlatPolynomial M α j 0
      simpa [quartetPoint] using hd
    have hzero : (Polynomial.derivative^[n] (Polynomial.C (L : ℂ) * S)).eval (α j) = 0 := by
      rw [Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
        iterate_derivative_eval_eq_zero_of_pow_dvd hS0 hdvd hn, mul_zero]
    have hbase : (Polynomial.derivative^[n] B₀).eval (α j)
        = (Polynomial.derivative^[n] (base j)).eval (α j) := by
      have h := hjets₀ (j, (0 : Fin 4)) n hn
      simpa [hwdef, htargetdef, quartetPoint, quartetTarget] using h
    rw [iterate_derivative_add, Polynomial.eval_add, hzero, add_zero]
    exact hbase

/-- The original linear-germ quartet passport theorem, recovered from the reusable arbitrary-base
Hermite realization by choosing the local envelope-normalized linear target. -/
theorem exists_quartet_passport_polynomial {J : Type} [Fintype J] [DecidableEq J]
    (a₀ : ℝ) (α : J → ℂ) (N : J → ℕ)
    (hαre : ∀ j, (α j).re ≠ 0)
    (hinj : Function.Injective (fun i : J × Fin 4 => quartetPoint (α i.1) i.2)) :
    ∃ B : Polynomial ℂ,
      (∀ z : ℂ, B.eval (-z) = B.eval z) ∧
      (∀ z : ℂ, B.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (B.eval z)) ∧
      (∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ B.eval ((y : ℂ) * I) = (r : ℂ)) ∧
      (∀ (j : J) (n : ℕ), n < N j + 2 →
        (Polynomial.derivative^[n] B).eval (α j)
          = iteratedDeriv n (fun z => (z - α j) / coshQuartetEnvelope a₀ z) (α j)) := by
  obtain ⟨B, hBeven, hBreal, hBpos, hBjets⟩ :=
    exists_quartet_passport_polynomial_of_base α N
      (fun j => quartetBasePoly a₀ (α j) (N j)) hαre hinj
  refine ⟨B, hBeven, hBreal, hBpos, ?_⟩
  intro j n hn
  exact (hBjets j n hn).trans (quartetBasePoly_jets a₀ (α j) (N j) hn)


/-! ## The realization capstone -/

/-- **Arbitrary finite quartet-passport realization.**  Every finite symmetry-closed packet of
quartet centres, with arbitrary finite prescribed depths, is realized by a real-even, Schwarz-real,
aperiodic, exact-order-one entire function with a zero-free imaginary axis, whose germ at each
quartet head agrees with the simple linear germ `z - α_j` through order `N_j + 1`. -/
theorem exists_quartet_passport_realizer {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ : ℝ) (ha₀ : a₀ ≠ 0) (α : J → ℂ) (N : J → ℕ)
    (hαre : ∀ j, (α j).re ≠ 0)
    (hAne : ∀ j : J, coshQuartetEnvelope a₀ (α j) ≠ 0)
    (hinj : Function.Injective (fun i : J × Fin 4 => quartetPoint (α i.1) i.2)) :
    ∃ B : Polynomial ℂ,
      0 < B.degree ∧
      (∀ z : ℂ, quartetRealizer a₀ B (-z) = quartetRealizer a₀ B z) ∧
      (∀ z : ℂ, quartetRealizer a₀ B ((starRingEnd ℂ) z)
        = (starRingEnd ℂ) (quartetRealizer a₀ B z)) ∧
      (∀ y : ℝ, quartetRealizer a₀ B ((y : ℂ) * I) ≠ 0) ∧
      (∀ h : ℂ, Function.Periodic (quartetRealizer a₀ B) h → h = 0) ∧
      (∀ (j : J) (n : ℕ), n ≤ N j + 1 →
        iteratedDeriv n (quartetRealizer a₀ B) (α j)
          = iteratedDeriv n (fun z => z - α j) (α j)) := by
  classical
  obtain ⟨B, hBeven, hBreal, hBpos, hBjets⟩ :=
    exists_quartet_passport_polynomial a₀ α N hαre hinj
  -- the analytic jets of the product
  have hjetA : ∀ (j : J) (n : ℕ), n ≤ N j + 1 →
      iteratedDeriv n (fun z => coshQuartetEnvelope a₀ z * B.eval z) (α j)
        = iteratedDeriv n (fun z => (1 : ℂ) * (z - α j)) (α j) := by
    intro j
    refine iteratedDeriv_envelopeProduct_eq_linear
      (coshQuartetEnvelope_analyticAt a₀ (α j)) (hAne j) ?_
    intro n hn
    rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_polynomial_eval B n (α j)]
    have hone : (fun z : ℂ => (1 : ℂ) * (z - α j) / coshQuartetEnvelope a₀ z)
        = fun z : ℂ => (z - α j) / coshQuartetEnvelope a₀ z := by
      funext z
      rw [one_mul]
    rw [hone]
    exact hBjets j n (by omega)
  have hjet : ∀ (j : J) (n : ℕ), n ≤ N j + 1 →
      iteratedDeriv n (quartetRealizer a₀ B) (α j)
        = iteratedDeriv n (fun z => z - α j) (α j) := by
    intro j n hn
    have hone : (fun z : ℂ => (1 : ℂ) * (z - α j)) = fun z : ℂ => z - α j := by
      funext z
      rw [one_mul]
    have h := hjetA j n hn
    rw [hone] at h
    exact h
  -- `B` is nonconstant
  obtain ⟨j₀⟩ := ‹Nonempty J›
  have hB0 : B.eval (α j₀) = 0 := by
    have h := hBjets j₀ 0 (by omega)
    simpa using h
  have hBne : B ≠ 0 := by
    obtain ⟨r, hr, heq⟩ := hBpos 0
    intro hzero
    rw [hzero] at heq
    simp at heq
    exact (ne_of_gt hr) (Complex.ofReal_eq_zero.mp heq.symm)
  have hdeg : 0 < B.degree := by
    by_contra hcon
    push Not at hcon
    have hconst : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_degree_le_zero hcon
    apply hBne
    rw [hconst]
    have : B.coeff 0 = 0 := by
      rw [hconst] at hB0
      simpa using hB0
    rw [this, map_zero]
  refine ⟨B, hdeg, quartetRealizer_neg hBeven, quartetRealizer_conj hBreal,
    quartetRealizer_ne_zero_on_imaginaryAxis ha₀ hBpos, ?_, hjet⟩
  intro h hper
  exact (quartetRealizer_periodic_iff ha₀ hdeg h).mp hper


end RHTower

end
