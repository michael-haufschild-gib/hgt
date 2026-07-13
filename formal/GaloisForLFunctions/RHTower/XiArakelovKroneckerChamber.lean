import GaloisForLFunctions.RHTower.ArakelovW
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Arakelov algebraic-integrality times conjugate-contractivity criterion

The Arakelov coordinate `w_rho = 1 - rho⁻¹` sends the critical line to the unit circle and the
right half of the critical strip to the open unit disk.  This module gives a genuinely arithmetic
top-down collision.

If `w` is a nonzero algebraic integer, its monic integral minimal polynomial has nonzero integer
constant coefficient.  The product of all complex conjugates of `w` therefore has norm at least
one.  If every conjugate is contractive, the same product has norm at most one.  Removing the
distinguished factor shows `‖w‖ = 1`.

Applied at every Xi zero, unconditional strip localization then gives RH.  The two global premises
are kept separate:

* algebraic integrality alone does not constrain the distinguished complex embedding;
* the conjugate-contractivity predicate is empty when the integral minimal polynomial is zero.

Their conjunction, rather than either premise in isolation, reaches the critical-line boundary.
This is an arithmetic bridge and does not provide a source theorem establishing either premise.
-/

open Complex Polynomial

noncomputable section

namespace RHTower

/-- A nonzero algebraic integer has nonzero constant coefficient in its integral minimal
polynomial. -/
theorem minpolyInt_coeff_zero_ne_zero {w : ℂ}
    (hint : IsIntegral ℤ w) (hw0 : w ≠ 0) :
    (minpoly ℤ w).coeff 0 ≠ 0 := by
  intro hzero
  have hXd : (Polynomial.X : Polynomial ℤ) ∣ minpoly ℤ w :=
    Polynomial.X_dvd_iff.mpr hzero
  have hirr := (minpoly.prime_of_isIntegrallyClosed hint).irreducible
  rcases hirr.dvd_iff.mp hXd with hXunit | hassoc
  · have hdegree := Polynomial.degree_eq_zero_of_isUnit hXunit
    simp at hdegree
  · obtain ⟨q, hq⟩ := hassoc.dvd
    have heval := congrArg (Polynomial.aeval w) hq
    simp [minpoly.aeval] at heval
    exact hw0 heval

/-- A finite multiset of nonnegative real numbers bounded by one has product bounded by one,
specialized to complex norms. -/
theorem multiset_norm_prod_le_one
    (s : Multiset ℂ) (h : ∀ z ∈ s, ‖z‖ ≤ 1) :
    (s.map norm).prod ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have ha : ‖a‖ ≤ 1 := h a (by simp)
      have hs : (s.map norm).prod ≤ 1 := ih (fun z hz => h z (by simp [hz]))
      have hs0 : 0 ≤ (s.map norm).prod := Multiset.prod_nonneg fun x hx => by
        obtain ⟨z, _hz, rfl⟩ := Multiset.mem_map.mp hx
        exact norm_nonneg z
      exact (mul_le_mul ha hs hs0 zero_le_one).trans_eq (one_mul 1)

/-- **Kronecker boundary lemma.** A nonzero algebraic integer whose complete complex conjugate
packet is contractive lies on the unit circle. -/
theorem norm_eq_one_of_integral_conjugates_contractive
    {w : ℂ} (hint : IsIntegral ℤ w) (hw0 : w ≠ 0)
    (hcontract : ∀ z ∈ ((minpoly ℤ w).map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ 1) :
    ‖w‖ = 1 := by
  let P : Polynomial ℂ := (minpoly ℤ w).map (Int.castRingHom ℂ)
  have hmonic : P.Monic := (minpoly.monic hint).map (Int.castRingHom ℂ)
  have hP0 : P ≠ 0 := hmonic.ne_zero
  have hroot : P.eval w = 0 := by
    dsimp only [P]
    rw [Polynomial.eval_map]
    exact minpoly.aeval ℤ w
  have hwmem : w ∈ P.roots := (Polynomial.mem_roots hP0).mpr hroot
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hcoeff := hsplits.coeff_zero_eq_prod_roots_of_monic hmonic
  have hcoeffLower : 1 ≤ ‖P.coeff 0‖ := by
    have hnonzero : (minpoly ℤ w).coeff 0 ≠ 0 :=
      minpolyInt_coeff_zero_ne_zero hint hw0
    have hlower := Int.one_le_abs hnonzero
    dsimp only [P]
    rw [Polynomial.coeff_map]
    change (1 : ℝ) ≤ ‖(((minpoly ℤ w).coeff 0 : ℤ) : ℂ)‖
    rw [Complex.norm_intCast]
    exact_mod_cast hlower
  have hprodNorm : ‖P.roots.prod‖ = 1 := by
    have hn := congrArg norm hcoeff
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hn
    have hlower : 1 ≤ ‖P.roots.prod‖ := by
      rw [← hn]
      exact hcoeffLower
    have hmap : ‖P.roots.prod‖ = (P.roots.map norm).prod := by
      simpa using map_multiset_prod (normHom : ℂ →*₀ ℝ) P.roots
    have hupper : ‖P.roots.prod‖ ≤ 1 := by
      rw [hmap]
      exact multiset_norm_prod_le_one P.roots hcontract
    exact le_antisymm hupper hlower
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hwmem
  have hscontract : ∀ z ∈ s, ‖z‖ ≤ 1 := by
    intro z hz
    apply hcontract z
    rw [hs]
    simp [hz]
  have hsle : (s.map norm).prod ≤ 1 := multiset_norm_prod_le_one s hscontract
  have hfactor : ‖w‖ * (s.map norm).prod = 1 := by
    have hn := hprodNorm
    rw [hs, Multiset.prod_cons, norm_mul] at hn
    have hmap : ‖s.prod‖ = (s.map norm).prod := by
      simpa using map_multiset_prod (normHom : ℂ →*₀ ℝ) s
    rwa [hmap] at hn
  apply le_antisymm
  · exact hcontract w hwmem
  · calc
      1 = ‖w‖ * (s.map norm).prod := hfactor.symm
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hsle (norm_nonneg w)
      _ = ‖w‖ := mul_one _

/-- Arithmetic constraint: every actual Xi-zero Arakelov coordinate is an algebraic integer. -/
def XiArakelovCoordinatesIntegral : Prop :=
  ∀ rho : ℂ, xi rho = 0 → IsIntegral ℤ (GaloisForLFunctions.arakelovW rho)

/-- Orientation constraint on the arithmetic orbit: every complex root of the integral minimal
polynomial of each Xi-zero Arakelov coordinate lies in the closed unit disk. -/
def XiArakelovConjugateRootsContractive : Prop :=
  ∀ rho : ℂ, xi rho = 0 →
    ∀ z ∈ ((minpoly ℤ (GaloisForLFunctions.arakelovW rho)).map
      (Int.castRingHom ℂ)).roots, ‖z‖ ≤ 1

/-- Pointwise conjunction of the arithmetic and orientation constraints. -/
def XiArakelovIntegralConjugateChamberAt (rho : ℂ) : Prop :=
  IsIntegral ℤ (GaloisForLFunctions.arakelovW rho) ∧
    ∀ z ∈ ((minpoly ℤ (GaloisForLFunctions.arakelovW rho)).map
      (Int.castRingHom ℂ)).roots, ‖z‖ ≤ 1

/-- **Arithmetic constraint times conjugate orientation implies RH.** Integrality makes the full
conjugate product arithmetically nonvanishing; contractivity squeezes it onto the unit boundary;
the Arakelov coordinate then puts every Xi zero on the critical line. -/
theorem riemannHypothesis_of_xiArakelovCoordinatesIntegral_of_conjugateRootsContractive
    (hint : XiArakelovCoordinatesIntegral)
    (hcontract : XiArakelovConjugateRootsContractive) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hstrip := xi_zero_re_mem_open_unit hzero
  have hrho0 : rho ≠ 0 := by
    intro hz
    subst rho
    norm_num at hstrip
  have hrho1 : rho ≠ 1 := by
    intro hz
    subst rho
    norm_num at hstrip
  have hw0 : GaloisForLFunctions.arakelovW rho ≠ 0 := by
    rw [GaloisForLFunctions.arakelovW_eq_div rho hrho0]
    exact div_ne_zero (sub_ne_zero.mpr hrho1) hrho0
  have hnorm : ‖GaloisForLFunctions.arakelovW rho‖ = 1 :=
    norm_eq_one_of_integral_conjugates_contractive
      (hint rho hzero) hw0 (hcontract rho hzero)
  have hline :=
    (GaloisForLFunctions.arakelovW_norm_one_iff_critical rho hrho0).mp hnorm
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hline

/-- Pointwise chamber packaging of the same arithmetic route. -/
theorem riemannHypothesis_of_xiArakelovIntegralConjugateChamber
    (h : ∀ rho : ℂ, xi rho = 0 → XiArakelovIntegralConjugateChamberAt rho) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiArakelovCoordinatesIntegral_of_conjugateRootsContractive
  · intro rho hzero
    exact (h rho hzero).1
  · intro rho hzero
    exact (h rho hzero).2

end RHTower
