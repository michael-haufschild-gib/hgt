import GaloisForLFunctions.HTGeometry.MahlerCoefficientFieldConfinement
import GaloisForLFunctions.HTGeometry.AsymptoticPolynomialCoefficients
import GaloisForLFunctions.HTGeometry.EulerADEConjugate

/-!
# Integer Euler differential equations

The Euler conversion of an ordinary differential polynomial with integer coefficients again has
integer polynomial coefficients: the falling factorials that appear in the conversion have integer
coefficients.  Selecting a minimal annihilator keeps that integrality, so every algebraic
differential relation of a formal series can be replaced by a nondegenerate one carried by a
differential polynomial over `ℤ[X]`.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-! ### Falling factorials over the integers -/

/-- The falling factorial polynomial over `ℤ`. -/
noncomputable def fallingPolyInt (m : ℕ) : Polynomial ℤ :=
  ∏ s ∈ Finset.range m, (Polynomial.X - Polynomial.C (s : ℤ))

theorem map_fallingPolyInt (m : ℕ) :
    Polynomial.map (Int.castRingHom ℂ) (fallingPolyInt m) = fallingPoly m := by
  rw [fallingPolyInt, fallingPoly, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  norm_num

theorem fallingPoly_coeff_int (m k : ℕ) :
    ∃ z : ℤ, (fallingPoly m).coeff k = (z : ℂ) := by
  refine ⟨(fallingPolyInt m).coeff k, ?_⟩
  rw [← map_fallingPolyInt m, Polynomial.coeff_map]
  rfl

/-! ### Power series carried by an integer polynomial -/

/-- The ring homomorphism sending an integer polynomial to the corresponding complex power
series. -/
noncomputable def intPolyHom : Polynomial ℤ →+* PowerSeries ℂ :=
  (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ).comp
    (Polynomial.mapRingHom (Int.castRingHom ℂ))

/-- The subring of complex power series carried by an integer polynomial. -/
noncomputable def intPolySubring : Subring (PowerSeries ℂ) := intPolyHom.range

theorem mem_intPolySubring_C {c : ℂ} (hc : ∃ z : ℤ, c = (z : ℂ)) :
    PowerSeries.C c ∈ intPolySubring := by
  obtain ⟨z, rfl⟩ := hc
  refine ⟨Polynomial.C z, ?_⟩
  rw [intPolyHom]
  simp

theorem mem_intPolySubring_X : (PowerSeries.X : PowerSeries ℂ) ∈ intPolySubring := by
  refine ⟨Polynomial.X, ?_⟩
  rw [intPolyHom]
  simp

/-! ### Coefficients in a subring -/

/-- Every coefficient of the differential polynomial lies in the subring. -/
def MvCoeffIn (R₀ : Subring (PowerSeries ℂ)) {ι : Type*}
    (P : MvPolynomial ι (PowerSeries ℂ)) : Prop :=
  ∀ d, MvPolynomial.coeff d P ∈ R₀

variable {R₀ : Subring (PowerSeries ℂ)} {ι : Type*}

theorem mvCoeffIn_zero : MvCoeffIn R₀ (0 : MvPolynomial ι (PowerSeries ℂ)) := by
  intro d
  simp only [MvPolynomial.coeff_zero]
  exact R₀.zero_mem

theorem mvCoeffIn_C {c : PowerSeries ℂ} (hc : c ∈ R₀) :
    MvCoeffIn R₀ (MvPolynomial.C c : MvPolynomial ι (PowerSeries ℂ)) := by
  classical
  intro d
  rw [MvPolynomial.coeff_C]
  split_ifs
  exacts [hc, R₀.zero_mem]

theorem mvCoeffIn_X [DecidableEq ι] (i : ι) :
    MvCoeffIn R₀ (MvPolynomial.X i : MvPolynomial ι (PowerSeries ℂ)) := by
  intro d
  rw [MvPolynomial.coeff_X]
  split_ifs
  exacts [R₀.one_mem, R₀.zero_mem]

theorem mvCoeffIn_add {P Q : MvPolynomial ι (PowerSeries ℂ)}
    (hP : MvCoeffIn R₀ P) (hQ : MvCoeffIn R₀ Q) : MvCoeffIn R₀ (P + Q) := by
  intro d
  rw [MvPolynomial.coeff_add]
  exact R₀.add_mem (hP d) (hQ d)

theorem mvCoeffIn_mul [DecidableEq ι] {P Q : MvPolynomial ι (PowerSeries ℂ)}
    (hP : MvCoeffIn R₀ P) (hQ : MvCoeffIn R₀ Q) : MvCoeffIn R₀ (P * Q) := by
  intro d
  rw [MvPolynomial.coeff_mul]
  exact Subring.sum_mem R₀ fun p _ => R₀.mul_mem (hP p.1) (hQ p.2)

theorem mvCoeffIn_sum {κ : Type*} (s : Finset κ) (P : κ → MvPolynomial ι (PowerSeries ℂ))
    (hP : ∀ k ∈ s, MvCoeffIn R₀ (P k)) : MvCoeffIn R₀ (∑ k ∈ s, P k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using mvCoeffIn_zero (R₀ := R₀) (ι := ι)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact mvCoeffIn_add (hP a (Finset.mem_insert_self a s))
        (ih fun k hk => hP k (Finset.mem_insert_of_mem hk))

theorem mvCoeffIn_prod [DecidableEq ι] {κ : Type*} (s : Finset κ)
    (P : κ → MvPolynomial ι (PowerSeries ℂ)) (hP : ∀ k ∈ s, MvCoeffIn R₀ (P k)) :
    MvCoeffIn R₀ (∏ k ∈ s, P k) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using mvCoeffIn_C (R₀ := R₀) (ι := ι) R₀.one_mem
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mvCoeffIn_mul (hP a (Finset.mem_insert_self a s))
        (ih fun k hk => hP k (Finset.mem_insert_of_mem hk))

theorem mvCoeffIn_pow [DecidableEq ι] {P : MvPolynomial ι (PowerSeries ℂ)}
    (hP : MvCoeffIn R₀ P) (r : ℕ) : MvCoeffIn R₀ (P ^ r) := by
  induction r with
  | zero => simpa using mvCoeffIn_C (R₀ := R₀) (ι := ι) R₀.one_mem
  | succ r ih =>
      rw [pow_succ]
      exact mvCoeffIn_mul ih hP

theorem mvCoeffIn_pderiv [DecidableEq ι] {P : MvPolynomial ι (PowerSeries ℂ)}
    (hP : MvCoeffIn R₀ P) (j : ι) : MvCoeffIn R₀ (MvPolynomial.pderiv j P) := by
  intro d
  rw [MvPolynomial.coeff_pderiv, mul_comm, ← Nat.cast_one, ← Nat.cast_add, ← nsmul_eq_mul]
  exact R₀.nsmul_mem (hP _) _

/-! ### The Euler conversion is integral -/

theorem mvCoeffIn_scaledDerivativeEulerPolynomial {m : ℕ} (j : Fin (m + 1)) :
    MvCoeffIn intPolySubring (scaledDerivativeEulerPolynomial j) := by
  rw [scaledDerivativeEulerPolynomial]
  refine mvCoeffIn_sum _ _ fun k _ => ?_
  refine mvCoeffIn_mul (mvCoeffIn_C ?_) (mvCoeffIn_X k)
  exact mem_intPolySubring_C (fallingPoly_coeff_int (j : ℕ) (k : ℕ))

theorem mvCoeffIn_ordinaryToEulerADE {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hQ : ∀ d, ∃ z : ℤ, MvPolynomial.coeff d Q = (z : ℂ)) :
    MvCoeffIn intPolySubring (ordinaryToEulerADE Q) := by
  rw [ordinaryToEulerADE]
  refine mvCoeffIn_sum _ _ fun d _ => ?_
  refine mvCoeffIn_mul (mvCoeffIn_C ?_) ?_
  · exact intPolySubring.mul_mem (mem_intPolySubring_C (hQ d))
      (intPolySubring.pow_mem mem_intPolySubring_X _)
  · exact mvCoeffIn_prod _ _ fun j _ =>
      mvCoeffIn_pow (mvCoeffIn_scaledDerivativeEulerPolynomial j) (d j)

/-! ### Lifting coefficients along a ring homomorphism -/

theorem exists_mvPolynomial_preimage {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {ι : Type*} [DecidableEq ι] (P : MvPolynomial ι B)
    (hP : ∀ d, MvPolynomial.coeff d P ∈ f.range) :
    ∃ Q : MvPolynomial ι A, MvPolynomial.map f Q = P := by
  classical
  choose g hg using hP
  refine ⟨∑ d ∈ P.support, MvPolynomial.monomial d (g d), ?_⟩
  ext d
  rw [MvPolynomial.coeff_map]
  have hcoeff : MvPolynomial.coeff d (∑ d' ∈ P.support, MvPolynomial.monomial d' (g d'))
      = if d ∈ P.support then g d else 0 := by
    rw [MvPolynomial.coeff_sum]
    by_cases hd : d ∈ P.support
    · rw [if_pos hd, Finset.sum_eq_single d]
      · rw [MvPolynomial.coeff_monomial, if_pos rfl]
      · intro d' _ hne
        rw [MvPolynomial.coeff_monomial, if_neg hne]
      · intro hcon
        exact absurd hd hcon
    · rw [if_neg hd]
      refine Finset.sum_eq_zero fun d' hd' => ?_
      rw [MvPolynomial.coeff_monomial, if_neg]
      rintro rfl
      exact hd hd'
  rw [hcoeff]
  by_cases hd : d ∈ P.support
  · rw [if_pos hd]
    exact hg d
  · rw [if_neg hd, map_zero]
    exact (MvPolynomial.notMem_support_iff.mp hd).symm

theorem coeToPowerSeries_comp :
    (PowerSeries.map (Int.castRingHom ℂ)).comp
        (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ) = intPolyHom := by
  refine RingHom.ext fun p => ?_
  ext n
  rw [RingHom.comp_apply, PowerSeries.coeff_map, intPolyHom, RingHom.comp_apply]
  simp [Polynomial.coeff_coe]

theorem isAnalytic_map_intPolyHom {m : ℕ} (PZ : MvPolynomial (Fin (m + 1)) (Polynomial ℤ)) :
    IsAnalyticDifferentialPolynomial (MvPolynomial.map intPolyHom PZ) := by
  have hcomp : MvPolynomial.map intPolyHom PZ
      = MvPolynomial.map
          (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
          (MvPolynomial.map (Polynomial.mapRingHom (Int.castRingHom ℂ)) PZ) := by
    rw [MvPolynomial.map_map]
    rfl
  rw [hcomp]
  exact isAnalyticDifferentialPolynomial_map_coe _

/-! ### A nondegenerate integral annihilator -/

theorem exists_intCoeff_nondegenerate_annihilator {m : ℕ} {F : PowerSeries ℂ} :
    ∀ (d : ℕ) (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ)),
      P.totalDegree = d → P ≠ 0 → IsFormalEulerADESolution P F →
      MvCoeffIn intPolySubring P →
      ∃ R : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ),
        R ≠ 0 ∧ IsFormalEulerADESolution R F ∧ MvCoeffIn intPolySubring R ∧
          ∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j R) ≠ 0 := by
  classical
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
          (MvPolynomial.pderiv j P) rfl hj (hnd j) (mvCoeffIn_pderiv hcoeff j)

/-! ### The integral Euler package -/

/-- **An integral ordinary differential equation yields a nondegenerate integral Euler
equation.** -/
theorem exists_integer_euler_ade {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) ℂ) (hQ0 : Q ≠ 0)
    (hQint : ∀ d, ∃ z : ℤ, MvPolynomial.coeff d Q = (z : ℂ))
    {F : PowerSeries ℂ} (hsol : MvPolynomial.aeval (formalJetVector F) Q = 0) :
    ∃ PZ : MvPolynomial (Fin (m + 1)) (PowerSeries ℤ),
      MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ ≠ 0 ∧
      IsAnalyticDifferentialPolynomial
        (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ) ∧
      IsFormalEulerADESolution
        (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ) F ∧
      (∃ j, MvPolynomial.aeval (eulerJetVector F) (MvPolynomial.pderiv j
        (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ)) ≠ 0) := by
  classical
  set P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ) := ordinaryToEulerADE Q with hPdef
  have hP0 : P ≠ 0 := ordinaryToEulerADE_ne_zero hQ0
  have hPsol : IsFormalEulerADESolution P F := by
    rw [IsFormalEulerADESolution, hPdef, aeval_ordinaryToEulerADE, hsol, mul_zero]
  have hPint : MvCoeffIn intPolySubring P := mvCoeffIn_ordinaryToEulerADE Q hQint
  obtain ⟨R, hR0, hRsol, hRint, hRnd⟩ :=
    exists_intCoeff_nondegenerate_annihilator P.totalDegree P rfl hP0 hPsol hPint
  obtain ⟨RZ, hRZ⟩ := exists_mvPolynomial_preimage intPolyHom R hRint
  refine ⟨MvPolynomial.map
    (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ) RZ, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [MvPolynomial.map_map, coeToPowerSeries_comp, hRZ]
  · exact hR0
  · rw [← hRZ]
    exact isAnalytic_map_intPolyHom RZ
  · exact hRsol
  · exact hRnd

end GaloisForLFunctions.HTGeometry
