import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheCollisionMassIsTheWaveNumber
import GaloisForLFunctions.HeckeKreinToeplitz.AllButFinitelyManyPrimesSeeTheWholeIndex

/-!
# Prime towers of the actual Weil kernel on the finite stratum

The blind primes are defined directly from the right zeros of zeta, independently of an
enumeration. With finitely many right zeros, at most `κ.choose 2` primes are blind and every
other prime tower carries the full index of the cubic-spline Weil kernel. Consequently, within
the finite-support stratum, positivity on one non-blind tower or on infinitely many prime
towers is equivalent to RH. The on-line part, nonzero spline weights and both members of every
hyperbolic pair are retained in the decomposition.
-/

open Complex Finset Zeta23
open scoped ComplexConjugate
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros cx)
open GaloisForLFunctions.ArithmeticOrientationGeometry
  (rightZeros_zeta_finite_iff_finiteOffLine)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open GaloisForLFunctions.SquareRootThreshold (temperedConfig_zetaZeroConfig)
open RHTower.BacklundConverse

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

/-- A prime is blind when two actual right-zero characters agree on its generator. -/
def zetaBlindPrimes : Set ℕ :=
  {p | ∃ hp : p.Prime, ¬ Set.InjOn
    (fun ρ => zeroChar (conj ρ) (primeElt hp)) (rightZeros zetaZeroConfig)}

private theorem zetaBlindPrimes_eq (hfin : (rightZeros zetaZeroConfig).Finite) :
    zetaBlindPrimes = blindPrimes (fun j : Fin hfin.toFinset.card =>
      conj (hfin.toFinset.equivFin.symm j : ℂ)) := by
  classical
  ext p
  have hsep (hp : p.Prime) :
      Function.Injective (fun j : Fin hfin.toFinset.card =>
        zeroChar (conj (hfin.toFinset.equivFin.symm j : ℂ)) (primeElt hp)) ↔
      Set.InjOn (fun ρ => zeroChar (conj ρ) (primeElt hp)) (rightZeros zetaZeroConfig) := by
    constructor
    · intro h ρ hρ σ hσ heq
      have hij : hfin.toFinset.equivFin ⟨ρ, hfin.mem_toFinset.mpr hρ⟩ =
          hfin.toFinset.equivFin ⟨σ, hfin.mem_toFinset.mpr hσ⟩ :=
        h (by simpa only [Equiv.symm_apply_apply] using heq)
      exact congrArg Subtype.val (hfin.toFinset.equivFin.injective hij)
    · intro h i j hij
      apply hfin.toFinset.equivFin.symm.injective
      exact Subtype.ext (h (hfin.mem_toFinset.mp (hfin.toFinset.equivFin.symm i).2)
        (hfin.mem_toFinset.mp (hfin.toFinset.equivFin.symm j).2) hij)
  simp only [zetaBlindPrimes, blindPrimes, Set.mem_setOf_eq, hsep]

/-- At most one blind prime per unordered pair of distinct right zeros. -/
theorem zetaBlindPrimes_finite_card_le (hfin : (rightZeros zetaZeroConfig).Finite) :
    zetaBlindPrimes.Finite ∧ zetaBlindPrimes.ncard ≤ hfin.toFinset.card.choose 2 := by
  rw [zetaBlindPrimes_eq hfin]
  apply ncard_blindPrimes_le
  intro i j hij
  exact hfin.toFinset.equivFin.symm.injective
    (Subtype.ext ((RingHom.injective _) hij))

/-- A non-blind prime reads the complete index of the actual zeta kernel. -/
theorem negIndex_zetaKernel_prime_eq (hfin : (rightZeros zetaZeroConfig).Finite)
    {p : ℕ} (hp : p.Prime) (hnb : p ∉ zetaBlindPrimes) :
    negIndex (zetaKernel ∘ zpowersHom _ (primeElt hp)) = negIndex zetaKernel := by
  classical
  have hmem (j : Fin hfin.toFinset.card) :
      (hfin.toFinset.equivFin.symm j : ℂ) ∈ rightZeros zetaZeroConfig :=
    hfin.mem_toFinset.mp (hfin.toFinset.equivFin.symm j).2
  have hdecomp := funext (zetaKernel_eq_onLine_add_pairs_fin hfin)
  have hindex := negIndex_prime_eq_of_not_blind
    (isPosDefKernel_orbitKernel_onLine temperedConfig_zetaZeroConfig cubicSpline_mem_realTests)
    (fun j : Fin hfin.toFinset.card => conj (hfin.toFinset.equivFin.symm j : ℂ))
    (fun j => by simpa only [Complex.conj_re] using (hmem j).2)
    (fun j => conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline)
      (hfin.toFinset.equivFin.symm j : ℂ)))
    (fun j => (_root_.map_ne_zero _).mpr (Wsummand_ne_zero_of_rightZero (hmem j)))
    hp (by rwa [← zetaBlindPrimes_eq hfin])
  rw [← hdecomp] at hindex
  rw [hindex, negIndex_zetaKernel]
  exact hfin.encard_eq_coe_toFinset_card.symm

/-- In the finite-support stratum, any non-blind prime tower decides RH. -/
theorem riemannHypothesis_iff_zetaKernel_prime_posDef (hfin : FiniteOffLine)
    {p : ℕ} (hp : p.Prime) (hnb : p ∉ zetaBlindPrimes) :
    RiemannHypothesis ↔ IsPosDefKernel (zetaKernel ∘ zpowersHom _ (primeElt hp)) := by
  rw [isPosDefKernel_iff (isHermKernel_zetaKernel.comp _),
    negIndex_zetaKernel_prime_eq (rightZeros_zeta_finite_iff_finiteOffLine.mpr hfin) hp hnb]
  exact riemannHypothesis_iff_negIndex_zetaKernel_eq_zero

/-- Infinitely many positive prime towers decide RH on the finite-support stratum. -/
theorem riemannHypothesis_iff_infinitely_many_zetaKernel_prime_posDef (hfin : FiniteOffLine) :
    RiemannHypothesis ↔ {p : ℕ | ∃ hp : p.Prime,
      IsPosDefKernel (zetaKernel ∘ zpowersHom _ (primeElt hp))}.Infinite := by
  constructor
  · intro hRH
    have hpos := (isPosDefKernel_iff isHermKernel_zetaKernel).mpr
      (riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mp hRH)
    exact Nat.infinite_setOf_prime.mono fun p hp => ⟨hp, hpos.comp _⟩
  · intro hpos
    have hblind := (zetaBlindPrimes_finite_card_le
      (rightZeros_zeta_finite_iff_finiteOffLine.mpr hfin)).1
    obtain ⟨p, ⟨hp, hppos⟩, hnb⟩ := (hpos.sdiff hblind).nonempty
    exact (riemannHypothesis_iff_zetaKernel_prime_posDef hfin hp hnb).mpr hppos

end GaloisForLFunctions.ArithmeticKreinLangerTheory

#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.zetaBlindPrimes_finite_card_le
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.negIndex_zetaKernel_prime_eq
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.riemannHypothesis_iff_zetaKernel_prime_posDef
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.riemannHypothesis_iff_infinitely_many_zetaKernel_prime_posDef
