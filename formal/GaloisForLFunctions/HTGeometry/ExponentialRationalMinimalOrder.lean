/-
# The minimal homogeneous order of an exponential-plus-rational carrier

For a carrier `q + ∑_i E_i` whose modes are derivation eigenvectors with distinct nonzero constant
eigenvalues, and whose rational shadow `h = ∏_i (D - λ_i) q` is nonzero, the least order of a
nonzero homogeneous linear differential equation over the base is exactly `r + 1`.

The lower bound: separating the operator forces its symbol to vanish at the `r` distinct
eigenvalues, so either the symbol is zero — all coefficients vanish — or it is divisible by the
monic `∏_i (X - λ_i)` of the same degree, hence a scalar multiple of it; but then the operator acts
on the rational part as that scalar times the shadow, which is nonzero.

The upper bound: the symbol `(h·X - h′)·∏_i (X - λ_i)` gives an explicit annihilator of order
`r + 1`.  Its base part is `h·h′ - h′·h = 0` and each mode is killed by the second factor.
-/
import GaloisForLFunctions.HTGeometry.LinearDifferentialOperatorSeparation

noncomputable section

open scoped Differential

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions.HTGeometry
open Polynomial

variable {F : Type*} [Field F] [Differential F]

/-- The symbol of a base-coefficient operator, as a polynomial. -/
def symbolPoly (c : ℕ → F) (n : ℕ) : Polynomial F :=
  ∑ j ∈ Finset.range (n + 1), Polynomial.C (c j) * Polynomial.X ^ j

omit [Differential F] in
theorem symbolPoly_natDegree_le (c : ℕ → F) (n : ℕ) : (symbolPoly c n).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)

omit [Differential F] in
theorem symbolPoly_eval (c : ℕ → F) (n : ℕ) (x : F) :
    (symbolPoly c n).eval x = symbolEval c n x := by
  rw [symbolPoly, symbolEval, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

omit [Differential F] in
theorem symbolPoly_coeff (c : ℕ → F) (n : ℕ) {j : ℕ} (hj : j ≤ n) :
    (symbolPoly c n).coeff j = c j := by
  classical
  rw [symbolPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hk), mul_zero]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) hnot

theorem linOpBase_symbolPoly (c : ℕ → F) (n : ℕ) (q : F) :
    linOpBase (symbolPoly c n).coeff n q = linOpBase c n q :=
  linOpBase_congr (fun _ hj => symbolPoly_coeff c n hj) q

theorem linOpBase_C_mul (a : F) (P : Polynomial F) (n : ℕ) (q : F) :
    linOpBase (Polynomial.C a * P).coeff n q = a * linOpBase P.coeff n q := by
  rw [linOpBase, linOpBase, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.coeff_C_mul]
  ring

omit [Differential F] in
/-- A monic divisor of matching degree exhausts the polynomial up to its leading scalar. -/
theorem eq_C_leadingCoeff_mul_of_monic_dvd {P Q : Polynomial F} (hQ : Q.Monic)
    (hdvd : Q ∣ P) (hP : P ≠ 0) (hdeg : P.natDegree = Q.natDegree) :
    P = Polynomial.C P.leadingCoeff * Q := by
  obtain ⟨R, hR⟩ := hdvd
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hR
    exact hP hR
  have hdegR : R.natDegree = 0 := by
    have hmul : (Q * R).natDegree = Q.natDegree + R.natDegree :=
      Polynomial.natDegree_mul hQ0 hR0
    rw [← hR, hdeg] at hmul
    omega
  obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hdegR
  have hlead : P.leadingCoeff = a := by
    rw [hR, ← ha, Polynomial.leadingCoeff_mul, hQ.leadingCoeff, one_mul,
      Polynomial.leadingCoeff_C]
  rw [hlead, hR, ← ha, mul_comm]

end GaloisForLFunctions.LinDiffOp

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions.HTGeometry
open Polynomial

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

/-- **Minimal order.**  Every base-coefficient operator of order at most `r` annihilating the
carrier `q + ∑_i E_i` has all of its coefficients zero: the least order of a nonzero homogeneous
annihilator is at least `r + 1`. -/
theorem coeff_eq_zero_of_annihilates {r : ℕ}
    (lam : Fin r → F) (hlam : Function.Injective lam) (hlam0 : ∀ i, lam i ≠ 0)
    (hlamc : ∀ i, (lam i)′ = 0)
    (E : Fin r → M) (hE : ∀ i, E i ≠ 0)
    (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (hconst : ∀ mu : F, mu′ = 0 → mu ≠ 0 → ∀ c : F, c ≠ 0 → c′ ≠ mu * c)
    (q : F) (hq : opList (List.ofFn lam) q ≠ 0)
    (c : ℕ → F) (n : ℕ) (hn : n ≤ r)
    (h : linOp c n (algebraMap F M q + ∑ i, E i) = 0) :
    ∀ j ≤ n, c j = 0 := by
  classical
  obtain ⟨hbase, hsym⟩ :=
    linOp_eq_zero_separation lam hlam hlam0 hlamc E hE heig hconst q c n h
  by_cases hP : symbolPoly c n = 0
  · intro j hj
    rw [← symbolPoly_coeff c n hj, hP, Polynomial.coeff_zero]
  · exfalso
    set l : List F := List.ofFn lam with hl
    have hlength : l.length = r := by rw [hl, List.length_ofFn]
    have hnodup : l.Nodup := by
      rw [hl]
      exact List.nodup_ofFn.mpr hlam
    have hlconst : ∀ mu ∈ l, mu′ = 0 := by
      intro mu hmu
      rw [hl, List.mem_ofFn] at hmu
      obtain ⟨i, rfl⟩ := hmu
      exact hlamc i
    have hle : (↑l : Multiset F) ≤ (symbolPoly c n).roots := by
      rw [Multiset.le_iff_count]
      intro a
      by_cases ha : a ∈ l
      · have hnodupM : (↑l : Multiset F).Nodup := by
          rw [Multiset.coe_nodup]
          exact hnodup
        have h1 : Multiset.count a (↑l : Multiset F) ≤ 1 :=
          Multiset.nodup_iff_count_le_one.mp hnodupM a
        have hroot : (symbolPoly c n).IsRoot a := by
          rw [hl, List.mem_ofFn] at ha
          obtain ⟨i, rfl⟩ := ha
          rw [Polynomial.IsRoot, symbolPoly_eval]
          exact hsym i
        have h2 : 1 ≤ Multiset.count a (symbolPoly c n).roots := by
          rw [Multiset.one_le_count_iff_mem, Polynomial.mem_roots hP]
          exact hroot
        omega
      · rw [Multiset.count_eq_zero_of_notMem (by simpa using ha)]
        exact Nat.zero_le _
    have hdvd : factorPoly l ∣ symbolPoly c n := by
      have hd := (Multiset.prod_X_sub_C_dvd_iff_le_roots hP (↑l : Multiset F)).mpr hle
      have heq : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) (↑l : Multiset F)).prod
          = factorPoly l := by
        rw [factorPoly]
        simp
      rwa [heq] at hd
    have hcard : r ≤ (symbolPoly c n).natDegree := by
      have h1 : (Multiset.card (↑l : Multiset F)) ≤ Multiset.card (symbolPoly c n).roots :=
        Multiset.card_le_card hle
      have h2 : Multiset.card (symbolPoly c n).roots ≤ (symbolPoly c n).natDegree :=
        Polynomial.card_roots' _
      rw [Multiset.coe_card, hlength] at h1
      omega
    have hdegP : (symbolPoly c n).natDegree = (factorPoly l).natDegree := by
      have h3 := symbolPoly_natDegree_le c n
      rw [factorPoly_natDegree, hlength]
      omega
    have hsplit := eq_C_leadingCoeff_mul_of_monic_dvd (factorPoly_monic l) hdvd hP hdegP
    have hnr : n = r := by
      have h3 := symbolPoly_natDegree_le c n
      omega
    have hval : linOpBase c n q
        = (symbolPoly c n).leadingCoeff * opList l q := by
      have h1 : linOpBase c n q = linOpBase (symbolPoly c n).coeff n q :=
        (linOpBase_symbolPoly c n q).symm
      have h2 : linOpBase (symbolPoly c n).coeff n q
          = (symbolPoly c n).leadingCoeff * linOpBase (factorPoly l).coeff n q := by
        conv_lhs => rw [hsplit]
        exact linOpBase_C_mul _ _ _ _
      have h3 : linOpBase (factorPoly l).coeff n q = opList l q := by
        rw [hnr, ← hlength]
        exact linOpBase_factorPoly hlconst q
      rw [h1, h2, h3]
    rw [hbase] at hval
    exact hq (by
      have hlead : (symbolPoly c n).leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr hP
      exact (mul_eq_zero.mp hval.symm).resolve_left hlead)

end GaloisForLFunctions.LinDiffOp

namespace GaloisForLFunctions.LinDiffOp

open GaloisForLFunctions.HTGeometry
open Polynomial

variable {F M : Type*} [Field F] [Field M] [Algebra F M]
  [Differential F] [Differential M] [DifferentialAlgebra F M]

omit [Differential F] in
theorem factorPoly_eval_eq_zero {l : List F} {a : F} (ha : a ∈ l) :
    (factorPoly l).eval a = 0 := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons mu l ih =>
      rw [factorPoly_cons, Polynomial.eval_mul]
      rcases List.mem_cons.mp ha with rfl | hmem
      · rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]
      · rw [ih hmem, mul_zero]

omit [Differential F] in
theorem symbolEval_coeff_eq_eval {P : Polynomial F} {n : ℕ} (hP : P.natDegree ≤ n) (x : F) :
    symbolEval P.coeff n x = P.eval x := by
  rw [symbolEval, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]

/-- **An annihilator of order `r + 1` exists.**  Its symbol is `(h·X - h′)·∏_i (X - λ_i)`, where
`h` is the rational shadow, so its leading coefficient is `h ≠ 0`. -/
theorem exists_annihilator_succ {r : ℕ}
    (lam : Fin r → F) (hlamc : ∀ i, (lam i)′ = 0)
    (E : Fin r → M) (heig : ∀ i, (E i)′ = algebraMap F M (lam i) * E i)
    (q : F) :
    linOp
      ((Polynomial.C (opList (List.ofFn lam) q) * Polynomial.X
          - Polynomial.C ((opList (List.ofFn lam) q))′) * factorPoly (List.ofFn lam)).coeff
      (r + 1) (algebraMap F M q + ∑ i, E i) = 0 := by
  classical
  set l : List F := List.ofFn lam with hl
  set h : F := opList l q with hh
  set P : Polynomial F :=
    (Polynomial.C h * Polynomial.X - Polynomial.C h′) * factorPoly l with hPdef
  have hlength : l.length = r := by rw [hl, List.length_ofFn]
  have hlconst : ∀ mu ∈ l, mu′ = 0 := by
    intro mu hmu
    rw [hl, List.mem_ofFn] at hmu
    obtain ⟨i, rfl⟩ := hmu
    exact hlamc i
  have hdegFac : (factorPoly l).natDegree ≤ r := by
    rw [factorPoly_natDegree, hlength]
  have hbase : linOpBase P.coeff (r + 1) q = 0 := by
    rw [hPdef, linOpBase_linear_mul hdegFac (factorPoly_coeff_deriv hlconst) q]
    have hfac : linOpBase (factorPoly l).coeff r q = h := by
      rw [hh, ← hlength]
      exact linOpBase_factorPoly hlconst q
    rw [hfac, hh]
    ring
  have hdegP : P.natDegree ≤ r + 1 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have h1 : (Polynomial.C h * Polynomial.X - Polynomial.C h′).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      refine max_le ?_ ?_
      · refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        rw [Polynomial.natDegree_X]
      · rw [Polynomial.natDegree_C]
        exact Nat.zero_le 1
    omega
  have hmodes : ∀ i, symbolEval P.coeff (r + 1) (lam i) = 0 := by
    intro i
    rw [symbolEval_coeff_eq_eval hdegP, hPdef, Polynomial.eval_mul]
    have hzero : (factorPoly l).eval (lam i) = 0 := by
      refine factorPoly_eval_eq_zero ?_
      rw [hl, List.mem_ofFn]
      exact ⟨i, rfl⟩
    rw [hzero, mul_zero]
  rw [linOp_add, linOp_algebraMap, hbase, map_zero, zero_add, linOp_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [linOp_eigen _ _ (hlamc i) (heig i), hmodes i, map_zero, zero_mul]

end GaloisForLFunctions.LinDiffOp
