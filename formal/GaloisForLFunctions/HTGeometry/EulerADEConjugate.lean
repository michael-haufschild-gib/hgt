import GaloisForLFunctions.HTGeometry.NonlinearMailletUnconditional

/-!
# Conjugating a formal solution of an integral Euler differential equation

The Euler operator, its jet vector and the evaluation of a differential polynomial all commute with
a ring homomorphism applied coefficientwise.  Hence an embedding of the coefficient field of a
formal solution of an equation with integer coefficients carries that solution to another formal
solution of the same equation, and Maillet's theorem bounds every conjugate coefficient sequence.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-! ### The Euler operator over an arbitrary ring -/

/-- The Euler operator `θ = t d/dt` over any semiring. -/
noncomputable def eulerOpOver {R : Type*} [Semiring R] (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => (n : R) * PowerSeries.coeff n F

@[simp] theorem coeff_eulerOpOver {R : Type*} [Semiring R] (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (eulerOpOver F) = (n : R) * PowerSeries.coeff n F :=
  PowerSeries.coeff_mk _ _

theorem eulerOpOver_complex (F : PowerSeries ℂ) : eulerOpOver F = formalEulerOp F := by
  ext n
  rw [coeff_eulerOpOver, coeff_formalEulerOp]

/-- The jet vector of the Euler operator over any semiring. -/
noncomputable def eulerJetOver {R : Type*} [Semiring R] {m : ℕ} (F : PowerSeries R) :
    Fin (m + 1) → PowerSeries R :=
  fun j => eulerOpOver^[(j : ℕ)] F

theorem eulerJetOver_complex {m : ℕ} (F : PowerSeries ℂ) :
    eulerJetOver (m := m) F = eulerJetVector (m := m) F := by
  funext j
  simp only [eulerJetOver, eulerJetVector]
  induction (j : ℕ) with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, eulerOpOver_complex]

theorem map_eulerOpOver {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (F : PowerSeries R) :
    PowerSeries.map φ (eulerOpOver F) = eulerOpOver (PowerSeries.map φ F) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_eulerOpOver, coeff_eulerOpOver, map_mul, PowerSeries.coeff_map,
    map_natCast]

theorem map_eulerJetOver {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (F : PowerSeries R) (j : Fin (m + 1)) :
    PowerSeries.map φ (eulerJetOver (m := m) F j)
      = eulerJetOver (m := m) (PowerSeries.map φ F) j := by
  simp only [eulerJetOver]
  induction (j : ℕ) with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_eulerOpOver, ih]

/-- **Naturality of the Euler evaluation.**  Mapping the coefficients of a formal solution commutes
with evaluating a differential polynomial. -/
theorem map_aeval_eulerJetOver {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) (PowerSeries R)) (F : PowerSeries R) :
    PowerSeries.map φ (MvPolynomial.aeval (eulerJetOver (m := m) F) Q)
      = MvPolynomial.aeval (eulerJetOver (m := m) (PowerSeries.map φ F))
          (MvPolynomial.map (PowerSeries.map φ) Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, Algebra.algebraMap_self,
        RingHom.id_apply]
  | add p q hp hq =>
      simp only [map_add]
      rw [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X]
      rw [hp, map_eulerJetOver]



/-! ### Integer differential polynomials -/

/-- A differential polynomial all of whose coefficients are rational integers comes from a
differential polynomial over `ℤ`. -/
theorem exists_intPolynomial {ι : Type*} [DecidableEq ι] (P : MvPolynomial ι (PowerSeries ℂ))
    (hP : ∀ d n, ∃ z : ℤ, PowerSeries.coeff n (MvPolynomial.coeff d P) = (z : ℂ)) :
    ∃ PZ : MvPolynomial ι (PowerSeries ℤ),
      MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ = P := by
  classical
  choose z hz using hP
  refine ⟨∑ d ∈ P.support, MvPolynomial.monomial d (PowerSeries.mk fun n => z d n), ?_⟩
  ext d n
  rw [MvPolynomial.coeff_map, PowerSeries.coeff_map]
  have hcoeff : MvPolynomial.coeff d
      (∑ d' ∈ P.support, MvPolynomial.monomial d' (PowerSeries.mk fun n => z d' n))
      = if d ∈ P.support then (PowerSeries.mk fun n => z d n) else 0 := by
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
  · rw [if_pos hd, PowerSeries.coeff_mk]
    simpa using (hz d n).symm
  · rw [if_neg hd, MvPolynomial.notMem_support_iff.mp hd]
    simp

/-! ### Conjugating a solution -/

theorem powerSeries_map_injective {R S : Type*} [Semiring R] [Semiring S] {φ : R →+* S}
    (hφ : Function.Injective φ) : Function.Injective (PowerSeries.map φ) := by
  intro F G h
  ext n
  refine hφ ?_
  have := congrArg (PowerSeries.coeff n) h
  simpa using this

/-- **A conjugate of a formal solution of an integral equation is a formal solution.** -/
theorem isFormalEulerADESolution_conj {m : ℕ} (PZ : MvPolynomial (Fin (m + 1)) (PowerSeries ℤ))
    {K : Type*} [Field K] (φ ψ : K →+* ℂ) {FK : PowerSeries K}
    (hsol : IsFormalEulerADESolution
      (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ) (PowerSeries.map φ FK)) :
    IsFormalEulerADESolution
      (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ) (PowerSeries.map ψ FK) := by
  classical
  set PK : MvPolynomial (Fin (m + 1)) (PowerSeries K) :=
    MvPolynomial.map (PowerSeries.map (Int.castRingHom K)) PZ with hPKdef
  have hmapPK : ∀ χ : K →+* ℂ,
      MvPolynomial.map (PowerSeries.map χ) PK
        = MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ := by
    intro χ
    have hcomp : (PowerSeries.map χ).comp (PowerSeries.map (Int.castRingHom K))
        = PowerSeries.map (Int.castRingHom ℂ) := by
      refine RingHom.ext fun F => ?_
      ext n
      rw [RingHom.comp_apply, PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
      have hint : χ.comp (Int.castRingHom K) = Int.castRingHom ℂ := RingHom.ext_int _ _
      exact congrArg (fun f : ℤ →+* ℂ => f (PowerSeries.coeff n F)) hint
    rw [hPKdef, MvPolynomial.map_map, hcomp]
  have hnatφ := map_aeval_eulerJetOver φ PK FK
  rw [hmapPK φ] at hnatφ
  have hzero : MvPolynomial.aeval (eulerJetOver (m := m) FK) PK = 0 := by
    refine powerSeries_map_injective φ.injective ?_
    rw [hnatφ, map_zero]
    rw [eulerJetOver_complex]
    exact hsol
  have hnatψ := map_aeval_eulerJetOver ψ PK FK
  rw [hmapPK ψ, hzero, map_zero] at hnatψ
  rw [IsFormalEulerADESolution, ← eulerJetOver_complex]
  exact hnatψ.symm


/-! ### Maillet's bound for all conjugates at once -/

open NumberField in
/-- **Uniform Maillet bound over all embeddings.**  Every conjugate of the coefficient sequence of
a formal solution of an integral Euler equation is Gevrey, with constants independent of the
embedding. -/
theorem exists_uniform_conjugate_gevrey {m : ℕ} (PZ : MvPolynomial (Fin (m + 1)) (PowerSeries ℤ))
    (hP0 : MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ ≠ 0)
    (hPan : IsAnalyticDifferentialPolynomial
      (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ))
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) {FK : PowerSeries K}
    (hsol : IsFormalEulerADESolution
      (MvPolynomial.map (PowerSeries.map (Int.castRingHom ℂ)) PZ) (PowerSeries.map φ FK)) :
    ∃ (Cb Ab : ℝ) (r : ℕ), 0 < Cb ∧ 1 ≤ Ab ∧ ∀ (ψ : K →+* ℂ) (n : ℕ),
      ‖ψ (PowerSeries.coeff n FK)‖ ≤ Cb * Ab ^ n * ((Nat.factorial n : ℕ) : ℝ) ^ (r : ℝ) := by
  classical
  have hgev : ∀ ψ : K →+* ℂ, ∃ r : ℕ, IsGevreySeries (r : ℝ) (PowerSeries.map ψ FK) := by
    intro ψ
    exact exists_isGevreySeries_of_annihilator _ hPan hP0
      (isFormalEulerADESolution_conj PZ φ ψ hsol)
  choose rψ hrψ using hgev
  choose Cψ Aψ hCψ hAψ hbound using hrψ
  refine ⟨1 + ∑ ψ : K →+* ℂ, Cψ ψ, 1 + ∑ ψ : K →+* ℂ, Aψ ψ, ∑ ψ : K →+* ℂ, rψ ψ, ?_, ?_, ?_⟩
  · have : 0 ≤ ∑ ψ : K →+* ℂ, Cψ ψ := Finset.sum_nonneg fun ψ _ => le_of_lt (hCψ ψ)
    linarith
  · have : 0 ≤ ∑ ψ : K →+* ℂ, Aψ ψ := Finset.sum_nonneg fun ψ _ => le_of_lt (hAψ ψ)
    linarith
  · intro ψ n
    have hb := hbound ψ n
    rw [PowerSeries.coeff_map] at hb
    have hCle : Cψ ψ ≤ 1 + ∑ χ : K →+* ℂ, Cψ χ := by
      have h1 : Cψ ψ ≤ ∑ χ : K →+* ℂ, Cψ χ :=
        Finset.single_le_sum (fun χ _ => le_of_lt (hCψ χ)) (Finset.mem_univ ψ)
      linarith
    have hAle : Aψ ψ ≤ 1 + ∑ χ : K →+* ℂ, Aψ χ := by
      have h1 : Aψ ψ ≤ ∑ χ : K →+* ℂ, Aψ χ :=
        Finset.single_le_sum (fun χ _ => le_of_lt (hAψ χ)) (Finset.mem_univ ψ)
      linarith
    have hrle : (rψ ψ : ℝ) ≤ ((∑ χ : K →+* ℂ, rψ χ : ℕ) : ℝ) := by
      have : rψ ψ ≤ ∑ χ : K →+* ℂ, rψ χ :=
        Finset.single_le_sum (fun χ _ => Nat.zero_le (rψ χ)) (Finset.mem_univ ψ)
      exact_mod_cast this
    have hfac : (1 : ℝ) ≤ ((Nat.factorial n : ℕ) : ℝ) := one_le_factorial_cast n
    have hstep1 : Cψ ψ * Aψ ψ ^ n * ((Nat.factorial n : ℕ) : ℝ) ^ (rψ ψ : ℝ)
        ≤ (1 + ∑ χ : K →+* ℂ, Cψ χ) * (1 + ∑ χ : K →+* ℂ, Aψ χ) ^ n *
          ((Nat.factorial n : ℕ) : ℝ) ^ ((∑ χ : K →+* ℂ, rψ χ : ℕ) : ℝ) := by
      have hApow : Aψ ψ ^ n ≤ (1 + ∑ χ : K →+* ℂ, Aψ χ) ^ n :=
        pow_le_pow_left₀ (le_of_lt (hAψ ψ)) hAle n
      have hrpow : ((Nat.factorial n : ℕ) : ℝ) ^ (rψ ψ : ℝ) ≤ ((Nat.factorial n : ℕ) : ℝ) ^ ((∑ χ : K →+* ℂ, rψ χ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hfac hrle
      have hApos : (0 : ℝ) ≤ Aψ ψ ^ n := pow_nonneg (le_of_lt (hAψ ψ)) n
      have hrpos : (0 : ℝ) < ((Nat.factorial n : ℕ) : ℝ) ^ (rψ ψ : ℝ) := factorial_rpow_pos n _
      have hCpos : (0 : ℝ) < Cψ ψ := hCψ ψ
      have hAbig : (0 : ℝ) ≤ (1 + ∑ χ : K →+* ℂ, Aψ χ) ^ n := by
        refine pow_nonneg ?_ n
        have : 0 ≤ ∑ χ : K →+* ℂ, Aψ χ := Finset.sum_nonneg fun χ _ => le_of_lt (hAψ χ)
        linarith
      have hCbig : (0 : ℝ) ≤ 1 + ∑ χ : K →+* ℂ, Cψ χ := by
        have : 0 ≤ ∑ χ : K →+* ℂ, Cψ χ := Finset.sum_nonneg fun χ _ => le_of_lt (hCψ χ)
        linarith
      calc Cψ ψ * Aψ ψ ^ n * ((Nat.factorial n : ℕ) : ℝ) ^ (rψ ψ : ℝ)
          ≤ (1 + ∑ χ : K →+* ℂ, Cψ χ) * Aψ ψ ^ n *
              ((Nat.factorial n : ℕ) : ℝ) ^ (rψ ψ : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hrpos)
            exact mul_le_mul_of_nonneg_right hCle hApos
        _ ≤ (1 + ∑ χ : K →+* ℂ, Cψ χ) * (1 + ∑ χ : K →+* ℂ, Aψ χ) ^ n *
              ((Nat.factorial n : ℕ) : ℝ) ^ (rψ ψ : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hrpos)
            exact mul_le_mul_of_nonneg_left hApow hCbig
        _ ≤ (1 + ∑ χ : K →+* ℂ, Cψ χ) * (1 + ∑ χ : K →+* ℂ, Aψ χ) ^ n *
              ((Nat.factorial n : ℕ) : ℝ) ^ ((∑ χ : K →+* ℂ, rψ χ : ℕ) : ℝ) := by
            refine mul_le_mul_of_nonneg_left hrpow ?_
            exact mul_nonneg hCbig hAbig
    exact le_trans hb hstep1

end GaloisForLFunctions.HTGeometry
