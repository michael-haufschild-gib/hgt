import GaloisForLFunctions.RHTower.SoninPrimeArchPerTestTransfer
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Finite Sonin moment blocks transfer to RH

The positive all-prime Sonin residual operator carries one intrinsic trace-moment sequence.  This
module isolates a source-value interface stronger and more coherent than choosing a separate
aperture schedule for every polynomial: for every finite cutoff, one positive aperture sequence
must converge simultaneously in all moments below that cutoff to the fixed prime--Gamma centered
moment block.

Finite coefficient support then transports this block convergence to every integer-polynomial
trace-Hankel test.  The existing per-test transfer closes the chain to RH.  No sign, Xi zero
location, real-rootedness, limiting divisor measure, or anti-Herglotz hypothesis occurs in the new
premise.  The remaining work is the analytic source-to-source moment convergence itself.
-/

open Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The trace-Hankel value of a finite coefficient vector is its quadratic pairing with the
intrinsic Sonin energy moments. -/
theorem soninAllPrimeTraceHankel_ofFn
    (a : ℝ) (ha : 0 < a) (n : ℕ) (c : Fin n → ℝ) :
    soninAllPrimeTraceHankel a (Polynomial.ofFn n c) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((c i * c j : ℝ) : ℂ) *
          soninAllPrimeEnergyMoment a ((i : ℕ) + (j : ℕ)) := by
  rw [soninAllPrimeTraceHankel_eq_energyMoment_sum a ha]
  let p : Polynomial ℝ := Polynomial.ofFn n c
  change (∑ m ∈ p.support, ∑ k ∈ p.support,
      ((p.coeff m : ℝ) : ℂ) * ((p.coeff k : ℝ) : ℂ) *
        soninAllPrimeEnergyMoment a (m + k)) = _
  have hsupp : p.support ⊆ Finset.range n := by
    intro k hk
    rw [Finset.mem_range]
    by_contra hnot
    have hge : n ≤ k := Nat.le_of_not_gt hnot
    have hz : p.coeff k = 0 := by
      exact Polynomial.ofFn_coeff_eq_zero_of_ge c hge
    exact (Polynomial.mem_support_iff.mp hk) hz
  have hinner (m : ℕ) :
      (∑ k ∈ p.support,
        ((p.coeff m : ℝ) : ℂ) * ((p.coeff k : ℝ) : ℂ) *
          soninAllPrimeEnergyMoment a (m + k)) =
      ∑ k ∈ Finset.range n,
        ((p.coeff m : ℝ) : ℂ) * ((p.coeff k : ℝ) : ℂ) *
          soninAllPrimeEnergyMoment a (m + k) := by
    apply Finset.sum_subset hsupp
    intro k hkRange hkNot
    have hz : p.coeff k = 0 := by
      by_contra hne
      exact hkNot (Polynomial.mem_support_iff.mpr hne)
    simp [hz]
  calc
    (∑ m ∈ p.support, ∑ k ∈ p.support,
      ((p.coeff m : ℝ) : ℂ) * ((p.coeff k : ℝ) : ℂ) *
        soninAllPrimeEnergyMoment a (m + k)) =
        ∑ m ∈ p.support, ∑ k ∈ Finset.range n,
          ((p.coeff m : ℝ) : ℂ) * ((p.coeff k : ℝ) : ℂ) *
            soninAllPrimeEnergyMoment a (m + k) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hinner m
    _ = ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range n,
          ((p.coeff m : ℝ) : ℂ) * ((p.coeff k : ℝ) : ℂ) *
            soninAllPrimeEnergyMoment a (m + k) := by
      apply Finset.sum_subset hsupp
      intro m hmRange hmNot
      have hz : p.coeff m = 0 := by
        by_contra hne
        exact hmNot (Polynomial.mem_support_iff.mpr hne)
      simp [hz]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((c i * c j : ℝ) : ℂ) *
          soninAllPrimeEnergyMoment a ((i : ℕ) + (j : ℕ)) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_range] at hm
      simp only [hm, dite_true]
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      simp only [hk, dite_true]
      rw [show p.coeff m = c ⟨m, hm⟩ by
          exact Polynomial.ofFn_coeff_eq_val_of_lt c hm,
        show p.coeff k = c ⟨k, hk⟩ by
          exact Polynomial.ofFn_coeff_eq_val_of_lt c hk]
      push_cast
      congr

/-- One aperture sequence for each finite cutoff simultaneously matches every Sonin trace moment
below that cutoff with the corresponding fixed prime--Gamma centered moment. -/
def SoninPrimeArchFiniteMomentCoupling
    (aperture : ℕ → ℕ → ℝ) : Prop :=
  (∀ N j, 0 < aperture N j) ∧
    ∀ N r, r < N →
      Tendsto
        (fun j : ℕ => soninAllPrimeEnergyMoment (aperture N j) r)
        atTop
        (nhds ((normalizedPrimeArchMoment r : ℝ) : ℂ))

/-- The per-polynomial schedule canonically extracted from a finite-moment-block schedule. -/
def soninPrimeArchPerTestApertureOfFiniteMoment
    (aperture : ℕ → ℕ → ℝ) (p : Polynomial ℤ) (j : ℕ) : ℝ :=
  let q := p.map (Int.castRingHom ℝ)
  aperture (2 * (q.natDegree + 1)) j

/-- Simultaneous finite moment-block convergence supplies the existing per-test trace-Hankel
coupling. -/
theorem soninPrimeArchPerTestCoupling_of_finiteMomentCoupling
    {aperture : ℕ → ℕ → ℝ}
    (h : SoninPrimeArchFiniteMomentCoupling aperture) :
    SoninPrimeArchPerTestTraceHankelCoupling
      (soninPrimeArchPerTestApertureOfFiniteMoment aperture) := by
  constructor
  · intro p j
    exact h.1 _ _
  · intro p
    let q : Polynomial ℝ := p.map (Int.castRingHom ℝ)
    let n : ℕ := q.natDegree + 1
    let N : ℕ := 2 * n
    let c : Fin n → ℝ := Polynomial.toFn n q
    have hn : q.natDegree < n := by omega
    have hq : Polynomial.ofFn n c = q := by
      exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hn
    have hpos (j : ℕ) : 0 < aperture N j := h.1 N j
    have hindex (i k : Fin n) : (i : ℕ) + (k : ℕ) < N := by
      dsimp only [N, n]
      omega
    have hterm (i k : Fin n) :
        Tendsto
          (fun j : ℕ => ((c i * c k : ℝ) : ℂ) *
            soninAllPrimeEnergyMoment (aperture N j)
              ((i : ℕ) + (k : ℕ)))
          atTop
          (nhds (((c i * c k : ℝ) : ℂ) *
            ((normalizedPrimeArchMoment ((i : ℕ) + (k : ℕ)) : ℝ) : ℂ))) := by
      exact (h.2 N ((i : ℕ) + (k : ℕ)) (hindex i k)).const_mul _
    have hsum :
        Tendsto
          (fun j : ℕ => ∑ i : Fin n, ∑ k : Fin n,
            ((c i * c k : ℝ) : ℂ) *
              soninAllPrimeEnergyMoment (aperture N j)
                ((i : ℕ) + (k : ℕ)))
          atTop
          (nhds (∑ i : Fin n, ∑ k : Fin n,
            ((c i * c k : ℝ) : ℂ) *
              ((normalizedPrimeArchMoment ((i : ℕ) + (k : ℕ)) : ℝ) : ℂ))) := by
      exact tendsto_finsetSum Finset.univ (fun i _ =>
        tendsto_finsetSum Finset.univ (fun k _ => hterm i k))
    have hsource (j : ℕ) :
        soninAllPrimeTraceHankel (aperture N j) q =
          ∑ i : Fin n, ∑ k : Fin n,
            ((c i * c k : ℝ) : ℂ) *
              soninAllPrimeEnergyMoment (aperture N j)
                ((i : ℕ) + (k : ℕ)) := by
      calc
        soninAllPrimeTraceHankel (aperture N j) q =
            soninAllPrimeTraceHankel (aperture N j)
              (Polynomial.ofFn n c) :=
          congrArg (soninAllPrimeTraceHankel (aperture N j)) hq.symm
        _ = _ := soninAllPrimeTraceHankel_ofFn
          (aperture N j) (hpos j) n c
    have htarget :
        (∑ i : Fin n, ∑ k : Fin n,
          ((c i * c k : ℝ) : ℂ) *
            ((normalizedPrimeArchMoment ((i : ℕ) + (k : ℕ)) : ℝ) : ℂ)) =
          primeArchSourceTraceHankel q := by
      calc
        (∑ i : Fin n, ∑ k : Fin n,
          ((c i * c k : ℝ) : ℂ) *
            ((normalizedPrimeArchMoment ((i : ℕ) + (k : ℕ)) : ℝ) : ℂ)) =
            ∑ i : Fin n, ∑ k : Fin n,
              ((c i * c k : ℝ) : ℂ) *
                xiCentralReciprocalMoment ((i : ℕ) + (k : ℕ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro k hk
          rw [primeArchSourceMoment_eq_xiCentralReciprocalMoment]
        _ = xiCentralTraceHankel (Polynomial.ofFn n c) :=
          (xiCentralTraceHankel_ofFn n c).symm
        _ = xiCentralTraceHankel q := congrArg xiCentralTraceHankel hq
        _ = primeArchSourceTraceHankel q :=
          xiCentralTraceHankel_eq_primeArchSourceTraceHankel q
    have hfinal : Tendsto
        (fun j : ℕ => soninAllPrimeTraceHankel (aperture N j) q)
        atTop (nhds (primeArchSourceTraceHankel q)) := by
      simpa only [hsource, htarget] using hsum
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hfinal
    simpa only [soninPrimeArchPerTestApertureOfFiniteMoment, q, n, N,
      Function.comp_apply] using hre

/-- **Finite source-moment chain to RH.**  Simultaneous convergence of every finite initial Sonin
moment block to the corresponding prime--Gamma block forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_soninPrimeArchFiniteMomentCoupling
    {aperture : ℕ → ℕ → ℝ}
    (h : SoninPrimeArchFiniteMomentCoupling aperture) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninPrimeArchPerTestTraceHankelCoupling
    (soninPrimeArchPerTestCoupling_of_finiteMomentCoupling h)

end

end RHTower
