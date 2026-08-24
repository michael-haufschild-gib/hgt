import GaloisForLFunctions.HTGeometry.NonlinearMailletUnconditional
import GaloisForLFunctions.HTGeometry.BalancedDiagonalNonvanishing
import GaloisForLFunctions.HTGeometry.FormalMahlerDescent
import GaloisForLFunctions.HTGeometry.MinimalAnnihilator
import GaloisForLFunctions.HTGeometry.PRecursiveDFinite
import GaloisForLFunctions.HTGeometry.IterateDerivativeFalling
import GaloisForLFunctions.HTGeometry.FormalMahlerIntegerNormalization
import GaloisForLFunctions.HTGeometry.GenericJetInjectivity
import GaloisForLFunctions.HTGeometry.ForwardRecurrenceFieldConfinement
import GaloisForLFunctions.HTGeometry.PrimeCyclotomicFieldEscape
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge

/-!
# Mahler coefficient-field confinement

Formal algebraic differential relations on algebraic-coefficient series force every coefficient
into one number field.  The proof compiles ordinary derivatives to Euler jets, selects a
field-preserving nondegenerate annihilator, and applies an exact forward coefficient recursion.
It also gives the prime-cyclotomic formal hypertranscendence consequence.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

def CoefficientsIn (K : IntermediateField ℚ ℂ) (F : PowerSeries ℂ) : Prop :=
  ∀ n, PowerSeries.coeff n F ∈ K

theorem coefficientsIn_formalEulerOp_iterate
    (K : IntermediateField ℚ ℂ) {F : PowerSeries ℂ}
    (hF : CoefficientsIn K F) (j : ℕ) :
    CoefficientsIn K (formalEulerOp^[j] F) := by
  intro n
  rw [coeff_formalEulerOp_iterate]
  exact K.mul_mem (K.pow_mem (K.natCast_mem n) j) (hF n)

theorem coefficientsIn_eulerJetVector
    (K : IntermediateField ℚ ℂ) {m : ℕ} {F : PowerSeries ℂ}
    (hF : CoefficientsIn K F) (j : Fin (m + 1)) :
    CoefficientsIn K (eulerJetVector F j) :=
  coefficientsIn_formalEulerOp_iterate K hF (j : ℕ)

theorem coeff_aeval_powerSeries_mem
    (K : IntermediateField ℚ ℂ) {ι : Type*} [Fintype ι]
    (S : ι → PowerSeries ℂ) (P : MvPolynomial ι (PowerSeries ℂ))
    (hS : ∀ i, CoefficientsIn K (S i))
    (hP : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P)) :
    CoefficientsIn K (MvPolynomial.aeval S P) := by
  classical
  have hEval : MvPolynomial.aeval S P =
      ∑ d ∈ P.support, MvPolynomial.coeff d P *
        ∏ i ∈ d.support, S i ^ d i := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    simp
  rw [hEval]
  intro n
  rw [map_sum]
  exact K.sum_mem fun d _ =>
    GaloisForLFunctions.coeff_mul_mem (K := K.toSubfield) (hP d)
      (GaloisForLFunctions.coeff_prod_mem d.support (fun i => S i ^ d i)
        (fun i _ => GaloisForLFunctions.coeff_pow_mem (fun k => hS i k) (d i))) n

theorem coeff_pderiv_powerSeries_mem
    (K : IntermediateField ℚ ℂ) {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial ι (PowerSeries ℂ))
    (hP : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P)) (j : ι) :
    ∀ d, CoefficientsIn K (MvPolynomial.coeff d (MvPolynomial.pderiv j P)) := by
  intro d n
  rw [MvPolynomial.coeff_pderiv, mul_comm, ← Nat.cast_one, ← Nat.cast_add,
    ← nsmul_eq_mul, map_nsmul]
  exact K.nsmul_mem (hP _ n) _

theorem coeff_linearizationCoeff_mem
    (K : IntermediateField ℚ ℂ) {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P))
    {Y : PowerSeries ℂ} (hY : CoefficientsIn K Y) (j : Fin (m + 1)) :
    CoefficientsIn K (linearizationCoeff P Y j) := by
  apply coeff_aeval_powerSeries_mem K (eulerJetVector Y) (MvPolynomial.pderiv j P)
  · exact coefficientsIn_eulerJetVector K hY
  · exact coeff_pderiv_powerSeries_mem K P hP j

theorem eval_shiftPolynomial_mem
    (K : IntermediateField ℚ ℂ) {m : ℕ}
    (B : Fin (m + 1) → PowerSeries ℂ) (hB : ∀ j, CoefficientsIn K (B j))
    (mu n : ℕ) : (shiftPolynomial B mu).eval (n : ℂ) ∈ K := by
  rw [eval_shiftPolynomial]
  exact K.sum_mem fun j _ =>
    K.mul_mem (hB j mu) (K.pow_mem (K.natCast_mem n) (j : ℕ))

theorem coeff_taylorDefect_mem
    (K : IntermediateField ℚ ℂ) {ι : Type*} [Fintype ι]
    (S L : ι → PowerSeries ℂ) (P : MvPolynomial ι (PowerSeries ℂ))
    (hS : ∀ i, CoefficientsIn K (S i)) (hL : ∀ i, CoefficientsIn K (L i))
    (hP : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P)) :
    CoefficientsIn K (taylorDefect S L P) := by
  classical
  intro n
  rw [taylorDefect, map_sub, map_sub, map_sum]
  refine K.sub_mem (K.sub_mem ?_ ?_) (K.sum_mem fun j _ => ?_)
  · apply coeff_aeval_powerSeries_mem K (S + L) P
    · intro i k
      exact K.add_mem (hS i k) (hL i k)
    · exact hP
  · exact coeff_aeval_powerSeries_mem K S P hS hP n
  · exact GaloisForLFunctions.coeff_mul_mem (K := K.toSubfield)
      (coeff_aeval_powerSeries_mem K S (MvPolynomial.pderiv j P) hS
        (coeff_pderiv_powerSeries_mem K P hP j)) (hL j) n

/-- A nondegenerate algebraic Euler differential equation has a field-independent cutoff after
which its coefficients are recursively confined. -/
theorem exists_forall_coefficientsIn_of_nondegenerate_eulerADE
    {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    {F : PowerSeries ℂ} (hsol : IsFormalEulerADESolution P F)
    (hnd : ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j P) ≠ 0) :
    ∃ N : ℕ, ∀ K : IntermediateField ℚ ℂ,
      (∀ d, CoefficientsIn K (MvPolynomial.coeff d P)) →
      (∀ n ≤ N, PowerSeries.coeff n F ∈ K) → CoefficientsIn K F := by
  classical
  set Bf : Fin (m + 1) → PowerSeries ℂ :=
    fun j => MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j P) with hBfdef
  obtain ⟨j0, hj0⟩ := hnd
  have hex : ∃ μ, shiftPolynomial Bf μ ≠ 0 := by
    obtain ⟨μ, hμ⟩ : ∃ μ, PowerSeries.coeff μ (Bf j0) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hj0 (PowerSeries.ext hc)
    exact ⟨μ, shiftPolynomial_ne_zero_of_coeff hμ⟩
  set v : ℕ := Nat.find hex with hvdef
  have hv : shiftPolynomial Bf v ≠ 0 := Nat.find_spec hex
  have hvlow : ∀ μ, μ < v → shiftPolynomial Bf μ = 0 := by
    intro μ hμ
    by_contra hc
    exact absurd hμ (not_lt.mpr (Nat.find_le hc))
  obtain ⟨N0, hN0⟩ := GaloisForLFunctions.poly_eventually_ne_zero_nat
    (shiftPolynomial Bf v) hv
  set N : ℕ := max v N0 with hNdef
  refine ⟨N, ?_⟩
  intro K hP hinit
  set Y : PowerSeries ℂ := truncPowerSeries N F with hYdef
  set H : PowerSeries ℂ := F - Y with hHdef
  set B : Fin (m + 1) → PowerSeries ℂ := linearizationCoeff P Y with hBdef
  have hvN : v ≤ N := by simp [N]
  have hN0N : N0 ≤ N := by simp [N]
  have hYmem : CoefficientsIn K Y := by
    intro n
    rw [hYdef, coeff_truncPowerSeries]
    split_ifs with hn
    · exact hinit n hn
    · exact K.zero_mem
  have hBmem : ∀ j, CoefficientsIn K (B j) := by
    intro j
    rw [hBdef]
    exact coeff_linearizationCoeff_mem K P hP hYmem j
  have hagree : ∀ μ, μ ≤ N → shiftPolynomial B μ = shiftPolynomial Bf μ := by
    intro μ hμ
    rw [shiftPolynomial, shiftPolynomial]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    rw [hBdef, linearizationCoeff, hYdef, hBfdef]
    exact coeff_aeval_eulerJetVector_truncPowerSeries_eq
      (MvPolynomial.pderiv j P) F hμ
  have hBlow : ∀ μ, μ < v → shiftPolynomial B μ = 0 := by
    intro μ hμ
    rw [hagree μ (by omega)]
    exact hvlow μ hμ
  have hBv : shiftPolynomial B v ≠ 0 := by
    rw [hagree v hvN]
    exact hv
  have hHdvd : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ H := by
    rw [hHdef, hYdef]
    exact X_pow_dvd_sub_truncPowerSeries N F
  have hYH : Y + H = F := by rw [hHdef]; ring
  have hsol' : IsFormalEulerADESolution P (Y + H) := by rw [hYH]; exact hsol
  have hLH : eulerLinearOp B H =
      -(MvPolynomial.aeval (eulerJetVector Y) P)
        - taylorDefect (eulerJetVector Y) (eulerJetVector H) P := by
    rw [hBdef]
    exact eulerLinearOp_linearization_eq P Y H hsol'
  have hVmem : CoefficientsIn K (MvPolynomial.aeval (eulerJetVector Y) P) :=
    coeff_aeval_powerSeries_mem K (eulerJetVector Y) P
      (coefficientsIn_eulerJetVector K hYmem) hP
  have hHmem : CoefficientsIn K H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n ≤ N
      · rw [hHdef, hYdef, map_sub, coeff_truncPowerSeries, if_pos hn, sub_self]
        exact K.zero_mem
      · have hnN : N < n := Nat.lt_of_not_ge hn
        have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnN
        have hnN0 : N0 ≤ n := le_trans hN0N (Nat.le_of_lt hnN)
        set H' : PowerSeries ℂ := truncPowerSeries (n - 1) H with hH'def
        have hH'mem : CoefficientsIn K H' := by
          intro k
          rw [hH'def, coeff_truncPowerSeries]
          split_ifs with hk
          · exact ih k (by omega)
          · exact K.zero_mem
        have hH'dvd : (PowerSeries.X : PowerSeries ℂ) ^ (N + 1) ∣ H' := by
          rw [hH'def]
          exact X_pow_dvd_truncPowerSeries hHdvd
        have hdiff : (PowerSeries.X : PowerSeries ℂ) ^ n ∣ H - H' := by
          rw [hH'def]
          simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn0))] using
            (X_pow_dvd_sub_truncPowerSeries (n - 1) H)
        have hdefeq := coeff_taylorDefect_eq_of_sub_dvd P Y H H'
          (j := n + v) (by omega) hHdvd hH'dvd hdiff
        have hdefmem' : PowerSeries.coeff (n + v)
            (taylorDefect (eulerJetVector Y) (eulerJetVector H') P) ∈ K :=
          coeff_taylorDefect_mem K (eulerJetVector Y) (eulerJetVector H') P
            (coefficientsIn_eulerJetVector K hYmem)
            (coefficientsIn_eulerJetVector K hH'mem) hP (n + v)
        have hdefmem : PowerSeries.coeff (n + v)
            (taylorDefect (eulerJetVector Y) (eulerJetVector H) P) ∈ K := by
          rw [hdefeq]
          exact hdefmem'
        have hlinmem : PowerSeries.coeff (n + v) (eulerLinearOp B H) ∈ K := by
          rw [hLH, map_sub, map_neg]
          exact K.sub_mem (K.neg_mem (hVmem (n + v))) hdefmem
        have hsummem : (∑ k ∈ Finset.range n,
            (shiftPolynomial B (n + v - k)).eval ((k : ℕ) : ℂ) *
              PowerSeries.coeff k H) ∈ K :=
          K.sum_mem fun k hk => K.mul_mem
            (eval_shiftPolynomial_mem K B hBmem (n + v - k) k)
            (ih k (Finset.mem_range.mp hk))
        have hrec := shiftPolynomial_shift_mul_coeff B v hBlow H n
        have hprod : (shiftPolynomial B v).eval ((n : ℕ) : ℂ) *
            PowerSeries.coeff n H ∈ K := by
          rw [hrec]
          exact K.sub_mem hlinmem hsummem
        have hfacmem : (shiftPolynomial B v).eval ((n : ℕ) : ℂ) ∈ K :=
          eval_shiftPolynomial_mem K B hBmem v n
        have hfacne : (shiftPolynomial B v).eval ((n : ℕ) : ℂ) ≠ 0 := by
          rw [hagree v hvN]
          exact hN0 n hnN0
        have hquot := K.mul_mem (K.inv_mem hfacmem) hprod
        simpa [hfacne, mul_assoc] using hquot
  intro n
  rw [← hYH, map_add]
  exact K.add_mem (hYmem n) (hHmem n)

/-- A nondegenerate algebraic Euler differential equation over a field confines every
coefficient of a formal solution to that field after finitely many initial coefficients. -/
theorem exists_coefficientsIn_of_nondegenerate_eulerADE
    (K : IntermediateField ℚ ℂ) {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (hP : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P))
    {F : PowerSeries ℂ} (hsol : IsFormalEulerADESolution P F)
    (hnd : ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j P) ≠ 0) :
    ∃ N : ℕ, (∀ n ≤ N, PowerSeries.coeff n F ∈ K) → CoefficientsIn K F := by
  obtain ⟨N, hN⟩ :=
    exists_forall_coefficientsIn_of_nondegenerate_eulerADE P hsol hnd
  exact ⟨N, hN K hP⟩

/-- Minimal-annihilator selection retaining the coefficient field. -/
theorem exists_field_nondegenerate_annihilator
    (K : IntermediateField ℚ ℂ) {m : ℕ} {F : PowerSeries ℂ} :
    ∀ (d : ℕ) (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)),
      P.totalDegree = d → P ≠ 0 → IsFormalEulerADESolution P F →
      (∀ e, CoefficientsIn K (MvPolynomial.coeff e P)) →
      ∃ Q : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ),
        Q ≠ 0 ∧ IsFormalEulerADESolution Q F ∧
          (∀ e, CoefficientsIn K (MvPolynomial.coeff e Q)) ∧
          ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j Q) ≠ 0 := by
  letI : CharZero (PowerSeries ℂ) := {
    cast_injective := by
      intro a b hab
      have h := congrArg (PowerSeries.coeff 0) hab
      simpa using h }
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro P hdeg hP0 hsol hcoeff
    by_cases hnd : ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j P) ≠ 0
    · exact ⟨P, hP0, hsol, hcoeff, hnd⟩
    · push Not at hnd
      by_cases hall : ∀ j, MvPolynomial.pderiv j P = 0
      · exfalso
        have hC := eq_C_of_forall_pderiv_eq_zero hall
        have hval : MvPolynomial.aeval (eulerJetVector (m := m) F) P
            = MvPolynomial.coeff 0 P := by
          rw [hC]
          simp
        rw [IsFormalEulerADESolution, hval] at hsol
        exact hP0 (by rw [hC, hsol, map_zero])
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        have hdeglt : (MvPolynomial.pderiv j P).totalDegree < P.totalDegree := by
          have hdrop := totalDegree_pderiv_add_one_le P j hj
          omega
        refine ih (MvPolynomial.pderiv j P).totalDegree
          (by rw [← hdeg]; exact hdeglt)
          (MvPolynomial.pderiv j P) rfl hj (hnd j)
          (coeff_pderiv_powerSeries_mem K P hcoeff j)

/-- Unconditional coefficient-field confinement for any nonzero algebraic Euler differential
equation over the field.  Nondegeneracy is obtained from a minimal annihilator. -/
theorem exists_coefficientsIn_of_eulerADE
    (K : IntermediateField ℚ ℂ) {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)) (hP0 : P ≠ 0)
    (hP : ∀ d, CoefficientsIn K (MvPolynomial.coeff d P))
    {F : PowerSeries ℂ} (hsol : IsFormalEulerADESolution P F) :
    ∃ N : ℕ, (∀ n ≤ N, PowerSeries.coeff n F ∈ K) → CoefficientsIn K F := by
  obtain ⟨Q, hQ0, hQsol, hQcoeff, hQnd⟩ :=
    exists_field_nondegenerate_annihilator K P.totalDegree P rfl hP0 hsol hP
  exact exists_coefficientsIn_of_nondegenerate_eulerADE K Q hQcoeff hQsol hQnd

/-! ### Ordinary jets to Euler jets -/

/-- Polynomial in Euler-jet coordinates representing `X^j F^(j)`. -/
noncomputable def scaledDerivativeEulerPolynomial {m : ℕ} (j : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1)) (PowerSeries ℂ) :=
  ∑ k : Fin (m + 1),
    MvPolynomial.C (PowerSeries.C ((fallingPoly (j : ℕ)).coeff (k : ℕ))) *
      MvPolynomial.X k

theorem aeval_scaledDerivativeEulerPolynomial {m : ℕ} (j : Fin (m + 1))
    (F : PowerSeries ℂ) :
    MvPolynomial.aeval (eulerJetVector F) (scaledDerivativeEulerPolynomial j) =
      PowerSeries.X ^ (j : ℕ) * (⇑(d⁄dX ℂ))^[(j : ℕ)] F := by
  ext n
  simp only [scaledDerivativeEulerPolynomial, map_sum, map_mul, MvPolynomial.aeval_def,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_sum]
  rw [Algebra.algebraMap_self]
  simp only [RingHom.id_apply, PowerSeries.coeff_C_mul, eulerJetVector,
    coeff_formalEulerOp_iterate]
  rw [PowerSeries.coeff_X_pow_mul']
  have hsum : (∑ k : Fin (m + 1),
      (fallingPoly (j : ℕ)).coeff (k : ℕ) * (n : ℂ) ^ (k : ℕ)) =
      (fallingPoly (j : ℕ)).eval (n : ℂ) := by
    rw [Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (fallingPoly (j : ℕ)).coeff k * (n : ℂ) ^ k) (m + 1),
      Polynomial.eval_eq_sum_range,
      natDegree_fallingPoly]
    symm
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    · intro k hkbig hksmall
      rw [Finset.mem_range] at hkbig
      have hkj : (j : ℕ) < k := by
        by_contra h
        exact hksmall (Finset.mem_range.mpr (by omega))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [natDegree_fallingPoly]
        exact hkj), zero_mul]
  rw [show (∑ x : Fin (m + 1),
      (fallingPoly (j : ℕ)).coeff (x : ℕ) *
        ((n : ℂ) ^ (x : ℕ) * PowerSeries.coeff n F)) =
      (∑ x : Fin (m + 1),
        (fallingPoly (j : ℕ)).coeff (x : ℕ) * (n : ℂ) ^ (x : ℕ)) *
          PowerSeries.coeff n F by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring, hsum]
  by_cases hjn : (j : ℕ) ≤ n
  · rw [if_pos hjn, GaloisForLFunctions.coeff_iterate_derivative_eq_descFactorial]
    have hidx : n - (j : ℕ) + (j : ℕ) = n := Nat.sub_add_cancel hjn
    rw [hidx]
    have heval : (fallingPoly (j : ℕ)).eval (n : ℂ) =
        (n.descFactorial (j : ℕ) : ℂ) := by
      rw [eval_fallingPoly, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro k hk
      rw [Nat.cast_sub]
      exact le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hjn
    rw [heval]
    ring
  · rw [if_neg hjn]
    have hnj : n < (j : ℕ) := Nat.lt_of_not_ge hjn
    have heval : (fallingPoly (j : ℕ)).eval (n : ℂ) = 0 := by
      rw [eval_fallingPoly]
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hnj)
      simp
    rw [heval, zero_mul]

/-- Total derivative weight of an ordinary differential monomial. -/
def ordinaryJetWeight {m : ℕ} (d : Fin (m + 1) →₀ ℕ) : ℕ :=
  ∑ j : Fin (m + 1), (j : ℕ) * d j

/-- Largest total derivative weight occurring in an ordinary differential polynomial. -/
def ordinaryADEWeight {m : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) ℂ) : ℕ :=
  Q.support.sup ordinaryJetWeight

/-- Clear all powers of `X` after replacing ordinary jets by scaled Euler jets. -/
noncomputable def ordinaryToEulerADE {m : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPolynomial (Fin (m + 1)) (PowerSeries ℂ) :=
  ∑ d ∈ Q.support,
    MvPolynomial.C
        (PowerSeries.C (MvPolynomial.coeff d Q) *
          PowerSeries.X ^ (ordinaryADEWeight Q - ordinaryJetWeight d)) *
      ∏ j : Fin (m + 1), (scaledDerivativeEulerPolynomial j) ^ d j

theorem aeval_ordinaryToEulerADE {m : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) ℂ) (F : PowerSeries ℂ) :
    MvPolynomial.aeval (eulerJetVector F) (ordinaryToEulerADE Q) =
      PowerSeries.X ^ ordinaryADEWeight Q *
        MvPolynomial.aeval (formalJetVector F) Q := by
  classical
  rw [ordinaryToEulerADE, map_sum]
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_mul, MvPolynomial.aeval_def, MvPolynomial.eval₂_C, map_prod]
  rw [Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_pow]
  rw [show (∏ j : Fin (m + 1),
      MvPolynomial.aeval (eulerJetVector F) (scaledDerivativeEulerPolynomial j) ^ d j) =
      ∏ j : Fin (m + 1),
        (PowerSeries.X ^ (j : ℕ) * (⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ d j by
      apply Finset.prod_congr rfl
      intro j _
      rw [aeval_scaledDerivativeEulerPolynomial]]
  have hsplit : (∏ j : Fin (m + 1),
      (PowerSeries.X ^ (j : ℕ) * (⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ d j) =
      (∏ j : Fin (m + 1), PowerSeries.X ^ ((j : ℕ) * d j)) *
        ∏ j : Fin (m + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ d j := by
    simp_rw [mul_pow, ← pow_mul]
    exact Finset.prod_mul_distrib
  rw [hsplit]
  have hXprod : (∏ j : Fin (m + 1),
      (PowerSeries.X : PowerSeries ℂ) ^ ((j : ℕ) * d j)) =
        (PowerSeries.X : PowerSeries ℂ) ^ ordinaryJetWeight d := by
    simpa [ordinaryJetWeight] using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin (m + 1)))
        (fun j : Fin (m + 1) => (j : ℕ) * d j)
        (PowerSeries.X : PowerSeries ℂ))
  rw [hXprod]
  have hall : (∏ j : Fin (m + 1), ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ d j) =
      ∏ j ∈ d.support, ((⇑(d⁄dX ℂ))^[(j : ℕ)] F) ^ d j := by
    symm
    apply Finset.prod_subset (Finset.subset_univ d.support)
    intro j _ hj
    simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hj
    rw [hj, pow_zero]
  rw [hall]
  have hw : ordinaryJetWeight d ≤ ordinaryADEWeight Q :=
    Finset.le_sup hd
  simp only [formalJetVector]
  rw [show algebraMap ℂ (PowerSeries ℂ) (MvPolynomial.coeff d Q) =
      PowerSeries.C (MvPolynomial.coeff d Q) by rfl]
  calc
    PowerSeries.C (MvPolynomial.coeff d Q) *
          PowerSeries.X ^ (ordinaryADEWeight Q - ordinaryJetWeight d) *
          (PowerSeries.X ^ ordinaryJetWeight d *
            ∏ j ∈ d.support, (⇑(d⁄dX ℂ))^[(j : ℕ)] F ^ d j) =
        PowerSeries.C (MvPolynomial.coeff d Q) *
          (PowerSeries.X ^ (ordinaryADEWeight Q - ordinaryJetWeight d) *
            PowerSeries.X ^ ordinaryJetWeight d) *
          ∏ j ∈ d.support, (⇑(d⁄dX ℂ))^[(j : ℕ)] F ^ d j := by ring
    _ = PowerSeries.C (MvPolynomial.coeff d Q) *
          PowerSeries.X ^ ordinaryADEWeight Q *
          ∏ j ∈ d.support, (⇑(d⁄dX ℂ))^[(j : ℕ)] F ^ d j := by
      rw [← pow_add, Nat.sub_add_cancel hw]
    _ = PowerSeries.X ^ ordinaryADEWeight Q *
          (PowerSeries.C (MvPolynomial.coeff d Q) *
            ∏ j ∈ d.support, (⇑(d⁄dX ℂ))^[(j : ℕ)] F ^ d j) := by ring

theorem ordinaryToEulerADE_ne_zero {m : ℕ}
    {Q : MvPolynomial (Fin (m + 1)) ℂ} (hQ : Q ≠ 0) :
    ordinaryToEulerADE Q ≠ 0 := by
  intro hzero
  have hord : ∀ F : PowerSeries ℂ,
      MvPolynomial.aeval (formalJetVector F) Q = 0 := by
    intro F
    have h := aeval_ordinaryToEulerADE Q F
    rw [hzero, map_zero] at h
    have hprod : PowerSeries.X ^ ordinaryADEWeight Q *
        MvPolynomial.aeval (formalJetVector F) Q = 0 := h.symm
    exact (mul_eq_zero.mp hprod).resolve_left
      (pow_ne_zero _ PowerSeries.X_ne_zero)
  have hren : MvPolynomial.rename Fin.succ Q = 0 := by
    apply GaloisForLFunctions.formalJets_substitution_injective
    intro F
    rw [MvPolynomial.aeval_rename]
    change MvPolynomial.aeval (formalJetVector (m := m) F) Q = 0
    exact hord F
  exact hQ (MvPolynomial.rename_injective Fin.succ (Fin.succ_injective (m + 1)) hren)

/-! ### Coefficient fields of the Euler conversion -/

def MvCoefficientsIn (K : IntermediateField ℚ ℂ) {ι : Type*}
    (P : MvPolynomial ι (PowerSeries ℂ)) : Prop :=
  ∀ d, CoefficientsIn K (MvPolynomial.coeff d P)

theorem coefficientsIn_C (K : IntermediateField ℚ ℂ) {c : ℂ} (hc : c ∈ K) :
    CoefficientsIn K (PowerSeries.C c) := by
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs
  exacts [hc, K.zero_mem]

theorem coefficientsIn_zero (K : IntermediateField ℚ ℂ) :
    CoefficientsIn K (0 : PowerSeries ℂ) := by
  intro n
  rw [map_zero]
  exact K.zero_mem

theorem coefficientsIn_one (K : IntermediateField ℚ ℂ) :
    CoefficientsIn K (1 : PowerSeries ℂ) := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  exacts [K.one_mem, K.zero_mem]

theorem coefficientsIn_add (K : IntermediateField ℚ ℂ) {A B : PowerSeries ℂ}
    (hA : CoefficientsIn K A) (hB : CoefficientsIn K B) :
    CoefficientsIn K (A + B) := by
  intro n
  rw [map_add]
  exact K.add_mem (hA n) (hB n)

theorem coefficientsIn_mul (K : IntermediateField ℚ ℂ) {A B : PowerSeries ℂ}
    (hA : CoefficientsIn K A) (hB : CoefficientsIn K B) :
    CoefficientsIn K (A * B) :=
  fun n => GaloisForLFunctions.coeff_mul_mem (K := K.toSubfield) hA hB n

theorem coefficientsIn_pow (K : IntermediateField ℚ ℂ) {A : PowerSeries ℂ}
    (hA : CoefficientsIn K A) (r : ℕ) : CoefficientsIn K (A ^ r) :=
  GaloisForLFunctions.coeff_pow_mem (K := K.toSubfield) hA r

theorem polynomialCoefficientsIn_fallingPoly (K : IntermediateField ℚ ℂ) (j : ℕ) :
    PolynomialCoefficientsIn K (fallingPoly j) := by
  induction j with
  | zero => simpa [fallingPoly] using polynomialCoefficientsIn_one K
  | succ j ih =>
      rw [fallingPoly, Finset.prod_range_succ, ← fallingPoly]
      apply ih.mul
      intro n
      by_cases hn1 : n = 1
      · subst n
        simp
      by_cases hn0 : n = 0
      · subst n
        simp
      · have h1n : 1 ≠ n := fun h => hn1 h.symm
        simp [Polynomial.coeff_sub, Polynomial.coeff_X, h1n, hn0]

theorem mvCoefficientsIn_zero (K : IntermediateField ℚ ℂ) {ι : Type*} :
    MvCoefficientsIn K (0 : MvPolynomial ι (PowerSeries ℂ)) := by
  intro d
  rw [MvPolynomial.coeff_zero]
  exact coefficientsIn_zero K

theorem mvCoefficientsIn_C (K : IntermediateField ℚ ℂ) {ι : Type*} [DecidableEq ι]
    {A : PowerSeries ℂ} (hA : CoefficientsIn K A) :
    MvCoefficientsIn K (MvPolynomial.C A : MvPolynomial ι (PowerSeries ℂ)) := by
  intro d
  rw [MvPolynomial.coeff_C]
  split_ifs
  exacts [hA, coefficientsIn_zero K]

theorem mvCoefficientsIn_X (K : IntermediateField ℚ ℂ) {ι : Type*} [DecidableEq ι]
    (i : ι) : MvCoefficientsIn K (MvPolynomial.X i : MvPolynomial ι (PowerSeries ℂ)) := by
  intro d
  rw [MvPolynomial.coeff_X]
  split_ifs
  exacts [coefficientsIn_one K, coefficientsIn_zero K]

theorem mvCoefficientsIn_add (K : IntermediateField ℚ ℂ) {ι : Type*}
    {P Q : MvPolynomial ι (PowerSeries ℂ)}
    (hP : MvCoefficientsIn K P) (hQ : MvCoefficientsIn K Q) :
    MvCoefficientsIn K (P + Q) := by
  intro d
  rw [MvPolynomial.coeff_add]
  exact coefficientsIn_add K (hP d) (hQ d)

theorem mvCoefficientsIn_mul (K : IntermediateField ℚ ℂ) {ι : Type*} [DecidableEq ι]
    {P Q : MvPolynomial ι (PowerSeries ℂ)}
    (hP : MvCoefficientsIn K P) (hQ : MvCoefficientsIn K Q) :
    MvCoefficientsIn K (P * Q) := by
  intro d n
  rw [MvPolynomial.coeff_mul, map_sum]
  exact K.sum_mem fun x _ => GaloisForLFunctions.coeff_mul_mem
    (K := K.toSubfield) (hP x.1) (hQ x.2) n

theorem mvCoefficientsIn_pow (K : IntermediateField ℚ ℂ) {ι : Type*} [DecidableEq ι]
    {P : MvPolynomial ι (PowerSeries ℂ)} (hP : MvCoefficientsIn K P) :
    ∀ r : ℕ, MvCoefficientsIn K (P ^ r)
  | 0 => by simpa using mvCoefficientsIn_C (ι := ι) K (coefficientsIn_one K)
  | r + 1 => by
      rw [pow_succ]
      exact mvCoefficientsIn_mul K (mvCoefficientsIn_pow K hP r) hP

theorem mvCoefficientsIn_sum (K : IntermediateField ℚ ℂ) {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (s : Finset κ) (P : κ → MvPolynomial ι (PowerSeries ℂ))
    (hP : ∀ k ∈ s, MvCoefficientsIn K (P k)) :
    MvCoefficientsIn K (∑ k ∈ s, P k) := by
  induction s using Finset.induction_on with
  | empty => simpa using mvCoefficientsIn_zero (ι := ι) K
  | @insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact mvCoefficientsIn_add K (hP k (Finset.mem_insert_self k s))
        (ih fun l hl => hP l (Finset.mem_insert_of_mem hl))

theorem mvCoefficientsIn_prod (K : IntermediateField ℚ ℂ) {ι κ : Type*}
    [DecidableEq ι] [DecidableEq κ]
    (s : Finset κ) (P : κ → MvPolynomial ι (PowerSeries ℂ))
    (hP : ∀ k ∈ s, MvCoefficientsIn K (P k)) :
    MvCoefficientsIn K (∏ k ∈ s, P k) := by
  induction s using Finset.induction_on with
  | empty => simpa using mvCoefficientsIn_C (ι := ι) K (coefficientsIn_one K)
  | @insert k s hk ih =>
      rw [Finset.prod_insert hk]
      exact mvCoefficientsIn_mul K (hP k (Finset.mem_insert_self k s))
        (ih fun l hl => hP l (Finset.mem_insert_of_mem hl))

theorem mvCoefficientsIn_scaledDerivativeEulerPolynomial
    (K : IntermediateField ℚ ℂ) {m : ℕ} (j : Fin (m + 1)) :
    MvCoefficientsIn K (scaledDerivativeEulerPolynomial j) := by
  rw [scaledDerivativeEulerPolynomial]
  apply mvCoefficientsIn_sum K Finset.univ
  intro k hk
  apply mvCoefficientsIn_mul K
  · apply mvCoefficientsIn_C K
    exact coefficientsIn_C K (polynomialCoefficientsIn_fallingPoly K (j : ℕ) (k : ℕ))
  · exact mvCoefficientsIn_X K k

theorem mvCoefficientsIn_ordinaryToEulerADE
    (K : IntermediateField ℚ ℂ) {m : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : ∀ d, MvPolynomial.coeff d Q ∈ K) :
    MvCoefficientsIn K (ordinaryToEulerADE Q) := by
  rw [ordinaryToEulerADE]
  apply mvCoefficientsIn_sum K Q.support
  intro d hd
  apply mvCoefficientsIn_mul K
  · apply mvCoefficientsIn_C K
    apply coefficientsIn_mul K
    · exact coefficientsIn_C K (hQ d)
    · exact coefficientsIn_pow K
        (GaloisForLFunctions.coeff_X_mem (K := K.toSubfield)) _
  · apply mvCoefficientsIn_prod K Finset.univ
    intro j hj
    exact mvCoefficientsIn_pow K
      (mvCoefficientsIn_scaledDerivativeEulerPolynomial K j) (d j)

/-! ### Uniform ordinary-ADE confinement and Mahler consequence -/

/-- An integer ordinary differential equation has one cutoff valid over every intermediate
coefficient field. -/
theorem exists_forall_coefficientsIn_of_integer_ordinaryADE
    {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) ℂ) (hQ0 : Q ≠ 0)
    (hQint : ∀ d, ∃ z : ℤ, MvPolynomial.coeff d Q = (z : ℂ))
    {F : PowerSeries ℂ}
    (hsol : MvPolynomial.aeval (formalJetVector F) Q = 0) :
    ∃ N : ℕ, ∀ K : IntermediateField ℚ ℂ,
      (∀ n ≤ N, PowerSeries.coeff n F ∈ K) → CoefficientsIn K F := by
  let P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ) := ordinaryToEulerADE Q
  have hP0 : P ≠ 0 := ordinaryToEulerADE_ne_zero hQ0
  have hPsol : IsFormalEulerADESolution P F := by
    rw [IsFormalEulerADESolution, show P = ordinaryToEulerADE Q from rfl,
      aeval_ordinaryToEulerADE, hsol, mul_zero]
  have hQrat : ∀ d, MvPolynomial.coeff d Q ∈ (⊥ : IntermediateField ℚ ℂ) := by
    intro d
    obtain ⟨z, hz⟩ := hQint d
    rw [hz]
    exact (⊥ : IntermediateField ℚ ℂ).intCast_mem z
  have hPrat : ∀ d, CoefficientsIn (⊥ : IntermediateField ℚ ℂ)
      (MvPolynomial.coeff d P) := by
    exact mvCoefficientsIn_ordinaryToEulerADE (⊥ : IntermediateField ℚ ℂ) Q hQrat
  obtain ⟨R, hR0, hRsol, hRrat, hRnd⟩ :=
    exists_field_nondegenerate_annihilator (⊥ : IntermediateField ℚ ℂ)
      P.totalDegree P rfl hP0 hPsol hPrat
  obtain ⟨N, hN⟩ :=
    exists_forall_coefficientsIn_of_nondegenerate_eulerADE R hRsol hRnd
  refine ⟨N, ?_⟩
  intro K hinit
  apply hN K
  · intro d n
    exact (show (⊥ : IntermediateField ℚ ℂ) ≤ K from bot_le) (hRrat d n)
  · exact hinit

/-- **Mahler coefficient-field confinement, formal version.** Any algebraic-coefficient formal
series satisfying a nonzero complex algebraic differential relation has all coefficients in one
number field. -/
theorem coefficientsConfinedToNumberField_of_formalRelation
    {F : PowerSeries ℂ} (hFalg : ∀ n, IsAlgebraic ℚ (PowerSeries.coeff n F))
    {r : ℕ} {P : MvPolynomial (Fin (r + 2)) ℂ} (hP0 : P ≠ 0)
    (hrel : MvPolynomial.aeval (GaloisForLFunctions.formalJets r F) P = 0) :
    CoefficientsConfinedToNumberField (fun n => PowerSeries.coeff n F) := by
  obtain ⟨m, Q, hQ0, hQint, hQsol⟩ :=
    GaloisForLFunctions.exists_integer_jet_relation_of_formalRelation hP0 hrel
  obtain ⟨N, hN⟩ :=
    exists_forall_coefficientsIn_of_integer_ordinaryADE Q hQ0 hQint hQsol
  let S : Set ℂ := (fun n => PowerSeries.coeff n F) '' Set.Iic N
  have hSfinite : S.Finite := Set.finite_Iic N |>.image (fun n => PowerSeries.coeff n F)
  letI : Finite S := hSfinite
  have hSint : ∀ x ∈ S, IsIntegral ℚ x := by
    rintro x ⟨n, hn, rfl⟩
    exact isAlgebraic_iff_isIntegral.mp (hFalg n)
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ S
  have hfinite : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin hSint
  refine ⟨K, ⟨hfinite⟩, ?_⟩
  apply hN K
  intro n hn
  exact IntermediateField.subset_adjoin ℚ S ⟨n, hn, rfl⟩

/-- Formal series carrying arbitrary nonzero rational magnitudes and prescribed phases. -/
noncomputable def scaledCyclotomicFormalSeries (r : ℕ → ℚ) (u : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (r n : ℂ) * u n

@[simp] theorem coeff_scaledCyclotomicFormalSeries (r : ℕ → ℚ) (u : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (scaledCyclotomicFormalSeries r u) = (r n : ℂ) * u n :=
  PowerSeries.coeff_mk _ _

theorem isAlgebraic_of_isPrimitiveRoot {p : ℕ} (hp : 0 < p) {u : ℂ}
    (hu : IsPrimitiveRoot u p) : IsAlgebraic ℚ u := by
  apply isAlgebraic_iff_isIntegral.mpr
  refine ⟨Polynomial.cyclotomic p ℚ, Polynomial.cyclotomic.monic p ℚ, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact (hu.isRoot_cyclotomic hp).eq_zero

/-- Pairwise-distinct prime cyclotomic phases with arbitrary nonzero rational magnitudes satisfy
no nonzero formal algebraic differential equation. -/
theorem aeval_formalJets_scaledCyclotomicFormalSeries_ne_zero
    (p : ℕ → ℕ) (u : ℕ → ℂ) (r : ℕ → ℚ)
    (hp_inj : Function.Injective p) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) (hr : ∀ n, r n ≠ 0)
    (m : ℕ) (P : MvPolynomial (Fin (m + 2)) ℂ) (hP0 : P ≠ 0) :
    MvPolynomial.aeval (GaloisForLFunctions.formalJets m
      (scaledCyclotomicFormalSeries r u)) P ≠ 0 := by
  intro hrel
  have hFalg : ∀ n, IsAlgebraic ℚ
      (PowerSeries.coeff n (scaledCyclotomicFormalSeries r u)) := by
    intro n
    rw [coeff_scaledCyclotomicFormalSeries]
    exact (isAlgebraic_algebraMap (r n)).mul
      (isAlgebraic_of_isPrimitiveRoot (hp n).pos (hu n))
  have hconf := coefficientsConfinedToNumberField_of_formalRelation hFalg hP0 hrel
  exact (not_coefficientsConfinedToNumberField_of_scaled_injective_primitive_prime_roots
    p u r hp_inj hp hu hr) (by
      simpa [coeff_scaledCyclotomicFormalSeries] using hconf)

/-- Analytic bridge: any smooth function whose Taylor coefficients are the scaled primitive-prime
cyclotomic sequence is hypertranscendental. -/
theorem hypertranscendental_of_taylorPS_scaledCyclotomic
    (p : ℕ → ℕ) (u : ℕ → ℂ) (r : ℕ → ℚ)
    (hp_inj : Function.Injective p) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) (hr : ∀ n, r n ≠ 0)
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (hcoeff : ∀ n, PowerSeries.coeff n (GaloisForLFunctions.taylorPS f) =
      (r n : ℂ) * u n) : GaloisForLFunctions.Hypertranscendental f := by
  apply GaloisForLFunctions.hypertranscendental_of_aeval_survives hf
  intro m Q hQ0
  have htaylor : GaloisForLFunctions.taylorPS f = scaledCyclotomicFormalSeries r u := by
    ext n
    rw [hcoeff n, coeff_scaledCyclotomicFormalSeries]
  rw [htaylor]
  exact aeval_formalJets_scaledCyclotomicFormalSeries_ne_zero
    p u r hp_inj hp hu hr m Q hQ0

end GaloisForLFunctions.HTGeometry
