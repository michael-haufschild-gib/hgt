import GaloisForLFunctions.HTGeometry.GammaPoleScalePrincipalRemainderUniversalityLaw
import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentCoefficientFormalGerm

/-!
# Moving-center Gamma scale-clock relative formal hypertranscendence

The moving-center Gamma atlas proves that reciprocal factorial scale and every nonlinear
inverse-branch coefficient are algebraically independent over `ℂ(N)`.  The inverse-clock module
turns the tail coefficients into a formally hypertranscendental germ, but only over `ℂ` and after
discarding scale.

This file supplies generic characteristic-zero base-field jet separation, then applies it to the
scale-headed inverse-Gamma clock.  The resulting germ satisfies no nonzero finite-order algebraic
differential equation even over the full moving-center field `ℂ(N)`.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-! ## Generic characteristic-zero formal-jet separation -/

/-- Constant-coefficient evaluation of a formal jet is valid over every field. -/
theorem constantCoeff_aeval_formalJetsOver_field
    {K : Type*} [Field K] (n : ℕ) (G : K⟦X⟧)
    (Q : MvPolynomial (Fin (n + 2)) K) :
    PowerSeries.constantCoeff (MvPolynomial.aeval (formalJetsOver n G) Q) =
      MvPolynomial.eval
        (fun i => PowerSeries.constantCoeff (formalJetsOver n G i)) Q := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left
    (PowerSeries.constantCoeff) (algebraMap K K⟦X⟧) (formalJetsOver n G) Q]
  have hid : (PowerSeries.constantCoeff (R := K)).comp (algebraMap K K⟦X⟧) =
      RingHom.id K := by
    ext c
    simp
  rw [hid]
  rfl

/-- A finite Taylor polynomial realizes arbitrary origin jets over a characteristic-zero field. -/
theorem constantCoeff_formalJetsOver_realization
    {K : Type*} [Field K] [CharZero K]
    (n : ℕ) (v : Fin (n + 1) → K) :
    (fun i => PowerSeries.constantCoeff
      (formalJetsOver n (PowerSeries.mk fun j =>
        if hj : j < n + 1 then v ⟨j, hj⟩ / (Nat.factorial j : K) else 0) i)) =
      Fin.cons 0 v := by
  funext i
  induction i using Fin.cases with
  | zero => simp [formalJetsOver]
  | succ j =>
    have hslot : formalJetsOver n (PowerSeries.mk fun j' =>
        if hj' : j' < n + 1 then v ⟨j', hj'⟩ / (Nat.factorial j' : K) else 0) j.succ =
        (⇑(d⁄dX K))^[(j : ℕ)] (PowerSeries.mk fun j' =>
        if hj' : j' < n + 1 then v ⟨j', hj'⟩ / (Nat.factorial j' : K) else 0) := by
      simp [formalJetsOver]
    rw [hslot, Fin.cons_succ, ← PowerSeries.coeff_zero_eq_constantCoeff,
      coeff_iterate_derivative _ (j : ℕ) 0]
    have hfac : ∏ i ∈ Finset.range (j : ℕ), ((0 + 1 + i : ℕ) : K) =
        ((Nat.factorial (j : ℕ) : ℕ) : K) := by
      rw [← Nat.cast_prod]
      congr 1
      rw [← Finset.prod_range_add_one_eq_factorial]
      exact Finset.prod_congr rfl fun i _ => by omega
    rw [hfac, PowerSeries.coeff_mk, dif_pos (by omega : (0 + (j : ℕ)) < n + 1)]
    have hne : ((Nat.factorial (j : ℕ) : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [show (⟨0 + (j : ℕ), by omega⟩ : Fin (n + 1)) = j from by
      ext
      simp]
    simp only [Nat.zero_add]
    field_simp

/-- Generic finite formal-jet substitution is injective over every characteristic-zero field. -/
theorem formalJetsOver_substitution_injective
    {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) K}
    (h : ∀ G : K⟦X⟧, MvPolynomial.aeval (formalJetsOver n G) P = 0) :
    P = 0 := by
  by_contra hP
  have hdvd : ∀ k : ℕ, (MvPolynomial.X 0 : MvPolynomial (Fin (n + 2)) K) ^ k ∣ P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨Q, hQ⟩ := ih
      have hQ0 : ∀ G : K⟦X⟧, MvPolynomial.aeval (formalJetsOver n G) Q = 0 := by
        intro G
        have hG := h G
        rw [hQ, map_mul, map_pow, MvPolynomial.aeval_X] at hG
        have hX0 : formalJetsOver n G 0 = PowerSeries.X := by
          simp [formalJetsOver]
        rw [hX0] at hG
        rcases mul_eq_zero.mp hG with h1 | h1
        · exact absurd h1 (pow_ne_zero k PowerSeries.X_ne_zero)
        · exact h1
      have hval : ∀ v : Fin (n + 1) → K, MvPolynomial.eval (Fin.cons 0 v) Q = 0 := by
        intro v
        have h0 := congrArg (PowerSeries.constantCoeff (R := K))
          (hQ0 (PowerSeries.mk fun j =>
            if hj : j < n + 1 then v ⟨j, hj⟩ / (Nat.factorial j : K) else 0))
        rw [constantCoeff_aeval_formalJetsOver_field,
          constantCoeff_formalJetsOver_realization] at h0
        simpa using h0
      have hXdvd : Polynomial.X ∣ (MvPolynomial.finSuccEquiv K (n + 1)) Q := by
        rw [Polynomial.X_dvd_iff]
        apply MvPolynomial.funext
        intro v
        rw [map_zero, Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.eval_zero_map,
          ← MvPolynomial.eval_eq_eval_mv_eval']
        exact hval v
      have hX0dvd : (MvPolynomial.X 0 : MvPolynomial (Fin (n + 2)) K) ∣ Q := by
        have h1 := map_dvd (MvPolynomial.finSuccEquiv K (n + 1)).symm hXdvd
        have h2 : (MvPolynomial.finSuccEquiv K (n + 1)).symm Polynomial.X =
            MvPolynomial.X 0 := by
          rw [← MvPolynomial.finSuccEquiv_X_zero (R := K) (n := n + 1)]
          exact AlgEquiv.symm_apply_apply _ _
        rwa [h2, AlgEquiv.symm_apply_apply] at h1
      obtain ⟨R, hR⟩ := hX0dvd
      exact ⟨R, by rw [hQ, hR]; ring⟩
  have heP : (MvPolynomial.finSuccEquiv K (n + 1)) P ≠ 0 := fun h0 =>
    hP ((MvPolynomial.finSuccEquiv K (n + 1)).injective (by rw [h0, map_zero]))
  set d := ((MvPolynomial.finSuccEquiv K (n + 1)) P).natDegree with hd
  have hk := hdvd (d + 1)
  have hkP := map_dvd (MvPolynomial.finSuccEquiv K (n + 1)) hk
  rw [map_pow, MvPolynomial.finSuccEquiv_X_zero] at hkP
  have hle := Polynomial.natDegree_le_of_dvd hkP heP
  rw [Polynomial.natDegree_X_pow] at hle
  omega

/-- Differential-polynomial evaluation is natural under maps of algebras over any base ring. -/
theorem map_aeval_powerSeries_over
    {K A B σ : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B)
    (g : σ → A⟦X⟧) (P : MvPolynomial σ K) :
    PowerSeries.mapAlgHom f (MvPolynomial.aeval g P) =
      MvPolynomial.aeval (fun i => PowerSeries.mapAlgHom f (g i)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP => simp [hP]

/-- Universal coefficient power series over an arbitrary commutative ring. -/
def genericCoefficientPowerSeriesOver
    (K : Type*) [CommRing K] : (MvPolynomial ℕ K)⟦X⟧ :=
  PowerSeries.mk fun k => MvPolynomial.X k

/-- Evaluating universal coefficients yields the prescribed power series. -/
theorem map_genericCoefficientPowerSeriesOver
    {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a : ℕ → A) :
    PowerSeries.map (MvPolynomial.aeval a).toRingHom
        (genericCoefficientPowerSeriesOver K) =
      PowerSeries.mk a := by
  ext k
  simp [genericCoefficientPowerSeriesOver]

/-- Every nonzero differential polynomial survives the universal formal germ over a
characteristic-zero field. -/
theorem aeval_genericFormalJetsOver_ne_zero
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) K} (hP : P ≠ 0) :
    MvPolynomial.aeval
      (formalJetsOver n (genericCoefficientPowerSeriesOver K)) P ≠ 0 := by
  intro hzero
  apply hP
  apply formalJetsOver_substitution_injective
  intro G
  let f : MvPolynomial ℕ K →ₐ[K] K :=
    MvPolynomial.aeval (fun k => PowerSeries.coeff k G)
  have hmap := congrArg (PowerSeries.mapAlgHom f) hzero
  rw [map_zero] at hmap
  rw [map_aeval_powerSeries_over] at hmap
  have hgen : PowerSeries.map f.toRingHom
      (genericCoefficientPowerSeriesOver K) = G := by
    rw [show G = PowerSeries.mk (fun k => PowerSeries.coeff k G) from by
      ext k
      simp]
    exact map_genericCoefficientPowerSeriesOver _
  have hjets :
      (fun i => PowerSeries.mapAlgHom f
        (formalJetsOver n (genericCoefficientPowerSeriesOver K) i)) =
        formalJetsOver n G := by
    simpa only [PowerSeries.mapAlgHom_apply, hgen] using
      map_formalJetsOver f.toRingHom n (genericCoefficientPowerSeriesOver K)
  rw [hjets] at hmap
  exact hmap

/-- **Relative formal hypertranscendence from independent coefficients.**  Algebraic
independence over any characteristic-zero field forces every finite formal differential
observable over that same field to remain nonzero. -/
theorem aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent_over
    {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    (a : ℕ → A) (ha : AlgebraicIndependent K a) {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) K} (hP : P ≠ 0) :
    MvPolynomial.aeval (formalJetsOver n (PowerSeries.mk a)) P ≠ 0 := by
  let U : (MvPolynomial ℕ K)⟦X⟧ :=
    MvPolynomial.aeval
      (formalJetsOver n (genericCoefficientPowerSeriesOver K)) P
  have hU : U ≠ 0 := aeval_genericFormalJetsOver_ne_zero hP
  obtain ⟨N, hN⟩ : ∃ N, PowerSeries.coeff N U ≠ 0 := by
    by_contra h
    push Not at h
    apply hU
    apply PowerSeries.ext
    intro N
    exact h N
  let f : MvPolynomial ℕ K →ₐ[K] A := MvPolynomial.aeval a
  have hf : Function.Injective f :=
    algebraicIndependent_iff_injective_aeval.mp ha
  intro hzero
  have hnat : PowerSeries.mapAlgHom f U =
      MvPolynomial.aeval (formalJetsOver n (PowerSeries.mk a)) P := by
    rw [show U = MvPolynomial.aeval
      (formalJetsOver n (genericCoefficientPowerSeriesOver K)) P from rfl,
      map_aeval_powerSeries_over]
    have hgen : PowerSeries.map f.toRingHom
        (genericCoefficientPowerSeriesOver K) = PowerSeries.mk a := by
      simpa [f] using map_genericCoefficientPowerSeriesOver a
    have hjets :
        (fun i => PowerSeries.mapAlgHom f
          (formalJetsOver n (genericCoefficientPowerSeriesOver K) i)) =
          formalJetsOver n (PowerSeries.mk a) := by
      simpa only [PowerSeries.mapAlgHom_apply, hgen] using
        map_formalJetsOver f.toRingHom n (genericCoefficientPowerSeriesOver K)
    rw [hjets]
  have hmap : PowerSeries.mapAlgHom f U = 0 := hnat.trans hzero
  have hc := congrArg (PowerSeries.coeff N) hmap
  simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map, map_zero] at hc
  have hz : PowerSeries.coeff N U = 0 := hf (by simpa using hc)
  exact hN hz

/-! ## Gamma moving-center scale clock -/

local instance gammaScaleClockRationalNatGermAlgebra :
    Algebra GammaPoleRationalBase NatGerm :=
  ratNatEval.toAlgebra

/-- Scale and nonlinear inverse-branch coefficients are jointly independent over `ℂ(N)`. -/
theorem
    algebraicIndependent_gammaPoleScaleAndInverseBranchCoefficientFamily_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleAndInverseBranchCoefficientFamily := by
  rw [algebraicIndependent_iff_injective_aeval]
  simpa [gammaPoleScaleAndInverseBranchCoefficientRationalEval,
    MvPolynomial.aeval_def] using
      gammaPoleScaleAndInverseBranchCoefficientRationalEval_injective

/-- Enumerate the scale head followed by every nonlinear inverse-branch coefficient. -/
def gammaPoleScaleHeadedInverseClockIndex : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n

theorem gammaPoleScaleHeadedInverseClockIndex_injective :
    Function.Injective gammaPoleScaleHeadedInverseClockIndex := by
  intro m n h
  cases m with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => simp [gammaPoleScaleHeadedInverseClockIndex] at h
  | succ m =>
      cases n with
      | zero => simp [gammaPoleScaleHeadedInverseClockIndex] at h
      | succ n =>
          simp [gammaPoleScaleHeadedInverseClockIndex] at h
          subst n
          rfl

/-- Reciprocal factorial scale at degree zero, followed by inverse-Gamma branch coefficients. -/
def gammaPoleScaleHeadedInverseClockCoefficientGerm : ℕ → NatGerm :=
  gammaPoleScaleAndInverseBranchCoefficientFamily ∘
    gammaPoleScaleHeadedInverseClockIndex

theorem
    algebraicIndependent_gammaPoleScaleHeadedInverseClockCoefficientGerm_over_ratFunc :
    AlgebraicIndependent GammaPoleRationalBase
      gammaPoleScaleHeadedInverseClockCoefficientGerm := by
  exact
    algebraicIndependent_gammaPoleScaleAndInverseBranchCoefficientFamily_over_ratFunc.comp
      gammaPoleScaleHeadedInverseClockIndex
      gammaPoleScaleHeadedInverseClockIndex_injective

/-- The moving-center scale-headed inverse-Gamma clock formal germ. -/
def gammaPoleScaleHeadedInverseClockFormalGerm : NatGerm⟦X⟧ :=
  PowerSeries.mk gammaPoleScaleHeadedInverseClockCoefficientGerm

/-- **Gamma moving-center scale-clock relative formal-hypertranscendence universality.**
No nonzero finite-order algebraic differential observable with coefficients in `ℂ(N)` vanishes
on the scale-headed inverse-Gamma clock germ. -/
theorem gammaPoleScaleHeadedInverseClockFormalGerm_formallyHypertranscendental_over_ratFunc
    {n : ℕ} {P : MvPolynomial (Fin (n + 2)) GammaPoleRationalBase}
    (hP : P ≠ 0) :
    MvPolynomial.aeval
      (formalJetsOver n gammaPoleScaleHeadedInverseClockFormalGerm) P ≠ 0 := by
  exact aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent_over
    gammaPoleScaleHeadedInverseClockCoefficientGerm
    algebraicIndependent_gammaPoleScaleHeadedInverseClockCoefficientGerm_over_ratFunc hP

end

end GaloisForLFunctions
