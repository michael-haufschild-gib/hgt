import GaloisForLFunctions.CurvesOverFiniteFields.Residues
import GaloisForLFunctions.CurvesOverFiniteFields.ValuationSpaces
import GaloisForLFunctions.CurvesOverFiniteFields.EulerCharacteristic

/-!
# Divisors of a curve and the Euler characteristic

A divisor of `K` is a pair of finitely supported multiplicities on the finite and on the
infinite places (`Divisor`). Its degree weights each place by the dimension over `F` of its
residue ring (`Divisor.deg`). The finite chart gives `I(D)` (bounds at finite places), the infinite
chart gives `J(D)` (bounds at infinite places), and
`L(D) = I(D) ⊓ J(D)`, `H¹(D) = K/(I(D) ⊔ J(D))`, `χ(D) = dim L(D) − dim H¹(D)`.

* Raising `D` by one at a place keeps `L` and `H¹` finite-dimensional, in both directions, and adds
  the degree of the place to `χ` (`isFin_raiseFin_iff`, `chi_raiseFin`, `isFin_raiseInf_iff`,
  `chi_raiseInf`). This is the Euler step for the one-step quotient `I(D + P)/I(D) ≅ A/P`.
* Hence, if `L(0)` and `H¹(0)` are finite-dimensional, every divisor has finite-dimensional
  `L` and `H¹` and `χ(D) = deg D + χ(0)` (`chi_eq_deg_add_chi_zero`).
-/

noncomputable section

open Polynomial IsDedekindDomain

namespace GaloisForLFunctions.CurvesOverFiniteFields

variable (F : Type*) [Field F] [DecidableEq (RatFunc F)] (K : Type*) [Field K] [Algebra F[X] K]
  [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K]
  [Algebra.IsSeparable (RatFunc F) K] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K]

/-- A divisor: multiplicities at the finite and at the infinite places. -/
abbrev Divisor := (FinPlace F K →₀ ℤ) × (InfPlace F K →₀ ℤ)

/-- The degree of a finite place: the dimension of its residue ring over `F`. -/
def finDeg (P : FinPlace F K) : ℕ := Module.finrank F (finChart F K ⧸ P.asIdeal)

/-- The degree of an infinite place: the dimension of its residue ring over `F`. -/
def infDeg (Q : InfPlace F K) : ℕ := Module.finrank F (infChart F K ⧸ Q.asIdeal)

variable {F K}

/-- The degree of a divisor. -/
def Divisor.deg (D : Divisor F K) : ℤ :=
  (D.1.sum fun P n => n * (finDeg F K P : ℤ)) + D.2.sum fun Q n => n * (infDeg F K Q : ℤ)

/-- The finite-chart space `I(D)`: valuation bounds at every finite place. -/
abbrev finSpace (D : Divisor F K) : Submodule F K :=
  valSpaceF (R := finChart F K) (K := K) F D.1

/-- The infinite-chart space `J(D)`: valuation bounds at every infinite place. -/
abbrev infSpace (D : Divisor F K) : Submodule F K :=
  valSpaceF (R := infChart F K) (K := K) F D.2

/-- Both `L(D)` and `H¹(D)` are finite-dimensional. -/
def IsFin (D : Divisor F K) : Prop :=
  FiniteDimensional F (finSpace D ⊓ infSpace D : Submodule F K) ∧
    FiniteDimensional F (K ⧸ (finSpace D ⊔ infSpace D))

/-- `ℓ(D) = dim L(D)`. -/
def ell (D : Divisor F K) : ℕ := Module.finrank F (finSpace D ⊓ infSpace D : Submodule F K)

/-- `h¹(D) = dim H¹(D)`. -/
def hOne (D : Divisor F K) : ℕ := Module.finrank F (K ⧸ (finSpace D ⊔ infSpace D))

/-- The Euler characteristic `χ(D) = ℓ(D) − h¹(D)`. -/
def chi (D : Divisor F K) : ℤ := (ell D : ℤ) - hOne D

/-- Raise a divisor by one at a finite place. -/
def raiseFin (D : Divisor F K) (P : FinPlace F K) : Divisor F K := (D.1 + Finsupp.single P 1, D.2)

/-- Raise a divisor by one at an infinite place. -/
def raiseInf (D : Divisor F K) (Q : InfPlace F K) : Divisor F K := (D.1, D.2 + Finsupp.single Q 1)

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
theorem deg_raiseFin (D : Divisor F K) (P : FinPlace F K) :
    (raiseFin D P).deg = D.deg + finDeg F K P := by
  simp only [Divisor.deg, raiseFin]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring),
    Finsupp.sum_single_index (by simp)]
  ring

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] in
theorem deg_raiseInf (D : Divisor F K) (Q : InfPlace F K) :
    (raiseInf D Q).deg = D.deg + infDeg F K Q := by
  simp only [Divisor.deg, raiseInf]
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring),
    Finsupp.sum_single_index (by simp)]
  ring

omit [DecidableEq (RatFunc F)] in
/-- Residue rings of height-one primes have positive dimension. -/
theorem finrank_pos_quotient_place {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra F R]
    (v : HeightOneSpectrum R) [FiniteDimensional F (R ⧸ v.asIdeal)] :
    0 < Module.finrank F (R ⧸ v.asIdeal) := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  exact Module.finrank_pos

omit [IsScalarTower F (RatFunc F) K] in
theorem finSpace_le_raiseFin (D : Divisor F K) (P : FinPlace F K) :
    finSpace D ≤ finSpace (raiseFin D P) := fun _ hx =>
  valSpace_le_raise (K := K) D.1 P hx

omit [IsScalarTower F[X] (RatFunc F) K] [IsScalarTower F F[X] K] in
theorem infSpace_le_raiseInf (D : Divisor F K) (Q : InfPlace F K) :
    infSpace D ≤ infSpace (raiseInf D Q) := fun _ hx =>
  valSpace_le_raise (K := K) D.2 Q hx

omit [IsScalarTower F (RatFunc F) K] in
theorem finrank_subQuot_raiseFin (D : Divisor F K) (P : FinPlace F K) :
    Module.finrank F (subQuot (finSpace D) (finSpace (raiseFin D P))) = finDeg F K P :=
  finrank_valSpace_step (K := K) D.1 P F

omit [IsScalarTower F[X] (RatFunc F) K] [IsScalarTower F F[X] K] in
theorem finrank_subQuot_raiseInf (D : Divisor F K) (Q : InfPlace F K) :
    Module.finrank F (subQuot (infSpace D) (infSpace (raiseInf D Q))) = infDeg F K Q :=
  finrank_valSpace_step (K := K) D.2 Q F

instance finiteDimensional_subQuot_raiseFin (D : Divisor F K) (P : FinPlace F K) :
    FiniteDimensional F (subQuot (finSpace D) (finSpace (raiseFin D P))) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_subQuot_raiseFin]; exact finrank_pos_quotient_place P)

instance finiteDimensional_subQuot_raiseInf (D : Divisor F K) (Q : InfPlace F K) :
    FiniteDimensional F (subQuot (infSpace D) (infSpace (raiseInf D Q))) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_subQuot_raiseInf]; exact finrank_pos_quotient_place Q)

/-- Raising at a finite place preserves finiteness, in both directions. -/
theorem isFin_raiseFin_iff (D : Divisor F K) (P : FinPlace F K) :
    IsFin (raiseFin D P) ↔ IsFin D := by
  constructor
  · rintro ⟨h1, h2⟩
    haveI : FiniteDimensional F (finSpace (raiseFin D P) ⊓ infSpace D : Submodule F K) := h1
    haveI : FiniteDimensional F (K ⧸ (finSpace (raiseFin D P) ⊔ infSpace D)) := h2
    exact euler_step_down (U := infSpace D) (finSpace_le_raiseFin D P)
  · rintro ⟨h1, h2⟩
    obtain ⟨h3, h4, -⟩ := euler_step (U := infSpace D) (finSpace_le_raiseFin D P)
    exact ⟨h3, h4⟩

/-- Raising at a finite place adds its degree to `χ`. -/
theorem chi_raiseFin {D : Divisor F K} (hD : IsFin D) (P : FinPlace F K) :
    chi (raiseFin D P) = chi D + finDeg F K P := by
  obtain ⟨h1, h2⟩ := hD
  obtain ⟨-, -, h⟩ := euler_step (U := infSpace D) (finSpace_le_raiseFin D P)
  rw [finrank_subQuot_raiseFin] at h
  exact h

/-- Raising at an infinite place preserves finiteness, in both directions. -/
theorem isFin_raiseInf_iff (D : Divisor F K) (Q : InfPlace F K) :
    IsFin (raiseInf D Q) ↔ IsFin D := by
  unfold IsFin
  have hi : ∀ E : Divisor F K, finSpace E ⊓ infSpace E = infSpace E ⊓ finSpace E :=
    fun _ => inf_comm _ _
  have hs : ∀ E : Divisor F K, finSpace E ⊔ infSpace E = infSpace E ⊔ finSpace E :=
    fun _ => sup_comm _ _
  rw [hi, hs, hi, hs]
  constructor
  · rintro ⟨h1, h2⟩
    haveI : FiniteDimensional F (infSpace (raiseInf D Q) ⊓ finSpace D : Submodule F K) := h1
    haveI : FiniteDimensional F (K ⧸ (infSpace (raiseInf D Q) ⊔ finSpace D)) := h2
    exact euler_step_down (U := finSpace D) (infSpace_le_raiseInf D Q)
  · rintro ⟨h1, h2⟩
    obtain ⟨h3, h4, -⟩ := euler_step (U := finSpace D) (infSpace_le_raiseInf D Q)
    exact ⟨h3, h4⟩

/-- Raising at an infinite place adds its degree to `χ`. -/
theorem chi_raiseInf {D : Divisor F K} (hD : IsFin D) (Q : InfPlace F K) :
    chi (raiseInf D Q) = chi D + infDeg F K Q := by
  unfold chi ell hOne
  unfold IsFin at hD
  have hi : ∀ E : Divisor F K, finSpace E ⊓ infSpace E = infSpace E ⊓ finSpace E :=
    fun _ => inf_comm _ _
  have hs : ∀ E : Divisor F K, finSpace E ⊔ infSpace E = infSpace E ⊔ finSpace E :=
    fun _ => sup_comm _ _
  rw [hi, hs] at hD
  rw [hi, hs, hi, hs]
  obtain ⟨h1, h2⟩ := hD
  obtain ⟨-, -, h⟩ := euler_step (U := finSpace D) (infSpace_le_raiseInf D Q)
  rw [finrank_subQuot_raiseInf] at h
  exact h

/-- Adding `n` at a finite place. -/
theorem isFin_chi_addFin {D : Divisor F K} (hD : IsFin D) (P : FinPlace F K) (n : ℤ) :
    IsFin (D.1 + Finsupp.single P n, D.2) ∧
      chi (D.1 + Finsupp.single P n, D.2) = chi D + n * finDeg F K P := by
  induction n using Int.induction_on with
  | zero => simpa using hD
  | succ k ih =>
    have heq : ((D.1 + Finsupp.single P ((k : ℤ) + 1), D.2) : Divisor F K) =
        raiseFin (D.1 + Finsupp.single P (k : ℤ), D.2) P := by
      simp only [raiseFin, Finsupp.single_add, add_assoc]
    rw [heq]
    refine ⟨(isFin_raiseFin_iff _ P).mpr ih.1, ?_⟩
    rw [chi_raiseFin ih.1, ih.2]
    ring
  | pred k ih =>
    have heq : ((D.1 + Finsupp.single P (-(k : ℤ)), D.2) : Divisor F K) =
        raiseFin (D.1 + Finsupp.single P (-(k : ℤ) - 1), D.2) P := by
      simp only [raiseFin, add_assoc, ← Finsupp.single_add, sub_add_cancel]
    rw [heq] at ih
    have hfin : IsFin ((D.1 + Finsupp.single P (-(k : ℤ) - 1), D.2) : Divisor F K) :=
      (isFin_raiseFin_iff _ P).mp ih.1
    refine ⟨hfin, ?_⟩
    have := chi_raiseFin hfin P
    rw [ih.2] at this
    linarith

/-- Adding `n` at an infinite place. -/
theorem isFin_chi_addInf {D : Divisor F K} (hD : IsFin D) (Q : InfPlace F K) (n : ℤ) :
    IsFin (D.1, D.2 + Finsupp.single Q n) ∧
      chi (D.1, D.2 + Finsupp.single Q n) = chi D + n * infDeg F K Q := by
  induction n using Int.induction_on with
  | zero => simpa using hD
  | succ k ih =>
    have heq : ((D.1, D.2 + Finsupp.single Q ((k : ℤ) + 1)) : Divisor F K) =
        raiseInf (D.1, D.2 + Finsupp.single Q (k : ℤ)) Q := by
      simp only [raiseInf, Finsupp.single_add, add_assoc]
    rw [heq]
    refine ⟨(isFin_raiseInf_iff _ Q).mpr ih.1, ?_⟩
    rw [chi_raiseInf ih.1, ih.2]
    ring
  | pred k ih =>
    have heq : ((D.1, D.2 + Finsupp.single Q (-(k : ℤ))) : Divisor F K) =
        raiseInf (D.1, D.2 + Finsupp.single Q (-(k : ℤ) - 1)) Q := by
      simp only [raiseInf, add_assoc, ← Finsupp.single_add, sub_add_cancel]
    rw [heq] at ih
    have hfin : IsFin ((D.1, D.2 + Finsupp.single Q (-(k : ℤ) - 1)) : Divisor F K) :=
      (isFin_raiseInf_iff _ Q).mp ih.1
    refine ⟨hfin, ?_⟩
    have := chi_raiseInf hfin Q
    rw [ih.2] at this
    linarith

/-- Adding an arbitrary finite part. -/
theorem isFin_chi_addFinsupp_fin {D : Divisor F K} (hD : IsFin D) (E : FinPlace F K →₀ ℤ) :
    IsFin (D.1 + E, D.2) ∧
      chi (D.1 + E, D.2) = chi D + E.sum fun P n => n * (finDeg F K P : ℤ) := by
  induction E using Finsupp.induction with
  | zero => simpa using hD
  | single_add P n E _ _ ih =>
    have heq : ((D.1 + (Finsupp.single P n + E), D.2) : Divisor F K) =
        ((D.1 + E, D.2).1 + Finsupp.single P n, (D.1 + E, D.2).2) := by
      simp only [Prod.mk.injEq, and_true]
      abel
    rw [heq]
    obtain ⟨h1, h2⟩ := isFin_chi_addFin ih.1 P n
    refine ⟨h1, ?_⟩
    rw [h2, ih.2, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring),
      Finsupp.sum_single_index (by simp)]
    ring

/-- Adding an arbitrary infinite part. -/
theorem isFin_chi_addFinsupp_inf {D : Divisor F K} (hD : IsFin D) (E : InfPlace F K →₀ ℤ) :
    IsFin (D.1, D.2 + E) ∧
      chi (D.1, D.2 + E) = chi D + E.sum fun Q n => n * (infDeg F K Q : ℤ) := by
  induction E using Finsupp.induction with
  | zero => simpa using hD
  | single_add Q n E _ _ ih =>
    have heq : ((D.1, D.2 + (Finsupp.single Q n + E)) : Divisor F K) =
        ((D.1, D.2 + E).1, (D.1, D.2 + E).2 + Finsupp.single Q n) := by
      simp only [Prod.mk.injEq, true_and]
      abel
    rw [heq]
    obtain ⟨h1, h2⟩ := isFin_chi_addInf ih.1 Q n
    refine ⟨h1, ?_⟩
    rw [h2, ih.2, Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring),
      Finsupp.sum_single_index (by simp)]
    ring

/-- **Euler characteristic of a divisor**: if `L(0)` and `H¹(0)` are finite-dimensional, then so
are `L(D)` and `H¹(D)` for every divisor `D`, and `χ(D) = deg D + χ(0)`. -/
theorem chi_eq_deg_add_chi_zero (h0 : IsFin (0 : Divisor F K)) (D : Divisor F K) :
    IsFin D ∧ chi D = D.deg + chi (0 : Divisor F K) := by
  obtain ⟨h1, h2⟩ := isFin_chi_addFinsupp_fin h0 D.1
  have e1 : (((0 : Divisor F K).1 + D.1, (0 : Divisor F K).2) : Divisor F K) = (D.1, 0) := by
    simp
  rw [e1] at h1 h2
  obtain ⟨h3, h4⟩ := isFin_chi_addFinsupp_inf h1 D.2
  have e2 : (((D.1, (0 : InfPlace F K →₀ ℤ)) : Divisor F K).1,
      ((D.1, (0 : InfPlace F K →₀ ℤ)) : Divisor F K).2 + D.2) = D := by
    simp
  rw [e2] at h3 h4
  refine ⟨h3, ?_⟩
  rw [h4, h2, Divisor.deg]
  ring

end GaloisForLFunctions.CurvesOverFiniteFields
