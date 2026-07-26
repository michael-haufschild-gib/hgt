import GaloisForLFunctions.HilbertMetric.DegreeFiveCollisionGraphJet
import GaloisForLFunctions.HilbertMetric.DeterminantCurvatureJet
import GaloisForLFunctions.HilbertMetric.TransverseDegreeCurvature

/-!
# Degree-five Gaussian collision curvature

This module assembles every homogeneous degree from zero through five, normalizes the coherent
collision basis by its vanishing order, and identifies the full diagonal Fock-space two-jet.  At
the balanced transverse amplitude and ambient dimension sixteen, that limiting jet has the exact
strictly positive curvature `5 / 68` per top-degree channel.  Invertible recombination and
congruence then transport this sign to an actual finite Gaussian Gram matrix at nonzero collision
scale.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

theorem recombined_weightedDegreePolynomial_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (weight : ℕ → ℝ) (q r : DegreeFiveIndex d) (e : ℝ) :
    ∑ i, ∑ j, c q i * c r j *
      (∑ n ∈ Finset.range 6,
        weight n * e ^ (2 * n) * collisionBaseGramEntry nodes i j ^ n /
          (n.factorial : ℝ)) =
      if q = r then
        weight q.1 * e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0 := by
  calc
    _ = ∑ i, ∑ n ∈ Finset.range 6, ∑ j,
        weight n * e ^ (2 * n) / (n.factorial : ℝ) *
          (c q i * c r j * collisionBaseGramEntry nodes i j ^ n) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ n ∈ Finset.range 6, weight n * e ^ (2 * n) / (n.factorial : ℝ) *
        (∑ i, ∑ j, c q i * c r j * collisionBaseGramEntry nodes i j ^ n) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.range 6, weight n * e ^ (2 * n) / (n.factorial : ℝ) *
        (if q = r ∧ (q.1 : ℕ) = n then
          (Nat.multinomial Finset.univ q.2.1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hp := recombined_innerPower_eq_diagonal nodes c hdelta q r
        ⟨n, Finset.mem_range.mp hn⟩
      simpa [collisionBaseGramEntry, Fin.ext_iff] using congrArg
        (fun z => weight n * e ^ (2 * n) / (n.factorial : ℝ) * z) hp
    _ = _ := by
      by_cases hqr : q = r
      · subst r
        rw [if_pos rfl]
        calc
          _ = weight q.1 * e ^ (2 * (q.1 : ℕ)) / ((q.1 : ℕ).factorial : ℝ) *
              (if q = q ∧ (q.1 : ℕ) = q.1 then
                (Nat.multinomial Finset.univ q.2.1 : ℝ) else 0) := by
            apply Finset.sum_eq_single (q.1 : ℕ)
            · intro n hn hnq
              have hqn : (q.1 : ℕ) ≠ n := fun h => hnq h.symm
              simp [hqn]
            · simp
          _ = _ := by simp [fockMonomialWeight]; ring
      · rw [if_neg hqr]
        apply Finset.sum_eq_zero
        intro n hn
        simp [hqr]

theorem degreeFive_firstPolynomial_eq_weighted (a e : ℝ) :
    (∑ k ∈ Finset.range 5, e ^ (2 * (k + 1)) * a ^ (k + 1) / (k.factorial : ℝ)) =
      ∑ n ∈ Finset.range 6, (n : ℝ) * e ^ (2 * n) * a ^ n / (n.factorial : ℝ) := by
  simp [Finset.sum_range_succ, Nat.factorial]
  ring

theorem degreeFive_secondPolynomial_eq_weighted (a e : ℝ) :
    (∑ k ∈ Finset.range 4, e ^ (2 * (k + 2)) * a ^ (k + 2) / (k.factorial : ℝ)) =
      ∑ n ∈ Finset.range 6,
        ((n : ℝ) * (n - 1)) * e ^ (2 * n) * a ^ n / (n.factorial : ℝ) := by
  simp [Finset.sum_range_succ, Nat.factorial]
  ring

theorem recombined_valuePolynomial_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) (e : ℝ) :
    ∑ i, ∑ j, c q i * c r j *
      (∑ n ∈ Finset.range 6,
        e ^ (2 * n) * collisionBaseGramEntry nodes i j ^ n / (n.factorial : ℝ)) =
      if q = r then e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0 := by
  simpa using recombined_weightedDegreePolynomial_five nodes c hdelta (fun _ => 1) q r e

theorem recombined_firstPolynomial_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) (e : ℝ) :
    ∑ i, ∑ j, c q i * c r j *
      (∑ k ∈ Finset.range 5,
        e ^ (2 * (k + 1)) * collisionBaseGramEntry nodes i j ^ (k + 1) /
          (k.factorial : ℝ)) =
      if q = r then (q.1 : ℝ) * e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0 := by
  simp_rw [degreeFive_firstPolynomial_eq_weighted]
  simpa using recombined_weightedDegreePolynomial_five nodes c hdelta (fun n => (n : ℝ)) q r e

theorem recombined_secondPolynomial_five {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) (e : ℝ) :
    ∑ i, ∑ j, c q i * c r j *
      (∑ k ∈ Finset.range 4,
        e ^ (2 * (k + 2)) * collisionBaseGramEntry nodes i j ^ (k + 2) /
          (k.factorial : ℝ)) =
      if q = r then
        ((q.1 : ℝ) * (q.1 - 1)) * e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0 := by
  simp_rw [degreeFive_secondPolynomial_eq_weighted]
  simpa using recombined_weightedDegreePolynomial_five nodes c hdelta
    (fun n => (n : ℝ) * (n - 1)) q r e

def degreeFiveValueLimit {d : ℕ} (lam : ℝ) (q : DegreeFiveIndex d) : ℝ :=
  fockMonomialWeight q.2 *
    (1 + if q.1 = topDegreeIndex 5 then lam ^ 2 else 0)

def degreeFiveFirstLimit {d : ℕ} (lam : ℝ) (q : DegreeFiveIndex d) : ℝ :=
  fockMonomialWeight q.2 *
    ((q.1 : ℝ) + if q.1 = topDegreeIndex 5 then lam ^ 2 else 0)

def degreeFiveSecondLimit {d : ℕ} (q : DegreeFiveIndex d) : ℝ :=
  fockMonomialWeight q.2 * ((q.1 : ℝ) * (q.1 - 1))

theorem degreeFive_valueJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    (fun e =>
      (∑ i, ∑ j, c q i * c r j *
        Real.exp (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
          (transverseCollisionGramEntry lam nodes i j) e)) -
      ((if q = r then e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0) +
        e ^ 10 * (if q = r ∧ q.1 = topDegreeIndex 5 then
          lam ^ 2 * fockMonomialWeight q.2 else 0)))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hjet := coherentCollision_valueJet_finset
    (Finset.univ : Finset (DegreeFiveIndex d × DegreeFiveIndex d))
    (fun p => c q p.1 * c r p.2)
    (fun p => collisionBaseGramEntry nodes p.1 p.2)
    (fun p => transverseCollisionGramEntry lam nodes p.1 p.2)
  simp only [Fintype.sum_prod_type] at hjet
  have htransScaled (e : ℝ) :
      ∑ i, ∑ j, c q i * c r j *
        (e ^ 10 * transverseCollisionGramEntry lam nodes i j) =
      e ^ 10 *
        (if q = r ∧ q.1 = topDegreeIndex 5 then
          lam ^ 2 * fockMonomialWeight q.2 else 0) := by
    calc
      _ = e ^ 10 *
          (∑ i, ∑ j, c q i * c r j *
            transverseCollisionGramEntry lam nodes i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        congr 1
        exact recombined_transverseCollisionGramEntry_diagonal lam nodes c hdelta q r
  convert hjet using 1
  funext e
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [recombined_valuePolynomial_five nodes c hdelta q r e, htransScaled e]
  ring

theorem degreeFive_firstJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    (fun e =>
      (∑ i, ∑ j, c q i * c r j *
        (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
            (transverseCollisionGramEntry lam nodes i j) e *
          Real.exp (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
            (transverseCollisionGramEntry lam nodes i j) e))) -
      ((if q = r then
          (q.1 : ℝ) * e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0) +
        e ^ 10 * (if q = r ∧ q.1 = topDegreeIndex 5 then
          lam ^ 2 * fockMonomialWeight q.2 else 0)))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hjet := coherentCollision_firstJet_finset
    (Finset.univ : Finset (DegreeFiveIndex d × DegreeFiveIndex d))
    (fun p => c q p.1 * c r p.2)
    (fun p => collisionBaseGramEntry nodes p.1 p.2)
    (fun p => transverseCollisionGramEntry lam nodes p.1 p.2)
  simp only [Fintype.sum_prod_type] at hjet
  have htransScaled (e : ℝ) :
      ∑ i, ∑ j, c q i * c r j *
        (e ^ 10 * transverseCollisionGramEntry lam nodes i j) =
      e ^ 10 *
        (if q = r ∧ q.1 = topDegreeIndex 5 then
          lam ^ 2 * fockMonomialWeight q.2 else 0) := by
    calc
      _ = e ^ 10 *
          (∑ i, ∑ j, c q i * c r j *
            transverseCollisionGramEntry lam nodes i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        congr 1
        exact recombined_transverseCollisionGramEntry_diagonal lam nodes c hdelta q r
  convert hjet using 1
  funext e
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [recombined_firstPolynomial_five nodes c hdelta q r e, htransScaled e]
  ring

theorem degreeFive_secondJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    (fun e =>
      (∑ i, ∑ j, c q i * c r j *
        (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
            (transverseCollisionGramEntry lam nodes i j) e ^ 2 *
          Real.exp (coherentCollisionExponent (collisionBaseGramEntry nodes i j)
            (transverseCollisionGramEntry lam nodes i j) e))) -
      (if q = r then
        ((q.1 : ℝ) * (q.1 - 1)) * e ^ (2 * (q.1 : ℕ)) *
          fockMonomialWeight q.2 else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  have hjet := coherentCollision_secondJet_finset
    (Finset.univ : Finset (DegreeFiveIndex d × DegreeFiveIndex d))
    (fun p => c q p.1 * c r p.2)
    (fun p => collisionBaseGramEntry nodes p.1 p.2)
    (fun p => transverseCollisionGramEntry lam nodes p.1 p.2)
  simp only [Fintype.sum_prod_type] at hjet
  convert hjet using 1
  funext e
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [recombined_secondPolynomial_five nodes c hdelta q r e]
  ring

theorem degreeFive_gaussianValueJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    (fun e =>
      (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramEntry lam nodes e i j) -
      ((if q = r then e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0) +
        e ^ 10 * (if q = r ∧ q.1 = topDegreeIndex 5 then
          lam ^ 2 * fockMonomialWeight q.2 else 0)))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  unfold gaussianCollisionGramEntry
  simp_rw [degreeFiveCollisionPoint_inner]
  exact degreeFive_valueJet lam nodes c hdelta q r

theorem degreeFive_gaussianFirstJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    (fun e =>
      (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramFirstEntry lam nodes e i j) -
      ((if q = r then
          (q.1 : ℝ) * e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0) +
        e ^ 10 * (if q = r ∧ q.1 = topDegreeIndex 5 then
          lam ^ 2 * fockMonomialWeight q.2 else 0)))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  unfold gaussianCollisionGramFirstEntry gaussianCollisionGramEntry
  simp_rw [degreeFiveCollisionPoint_inner]
  exact degreeFive_firstJet lam nodes c hdelta q r

theorem degreeFive_gaussianSecondJet {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    (fun e =>
      (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramSecondEntry lam nodes e i j) -
      (if q = r then
        ((q.1 : ℝ) * (q.1 - 1)) * e ^ (2 * (q.1 : ℕ)) *
          fockMonomialWeight q.2 else 0))
      =o[nhds 0] (fun e : ℝ => e ^ 10) := by
  unfold gaussianCollisionGramSecondEntry gaussianCollisionGramEntry
  simp_rw [degreeFiveCollisionPoint_inner]
  exact degreeFive_secondJet lam nodes c hdelta q r

theorem degreeFive_pow_ten_isBigO_degreeSum {d : ℕ} (q r : DegreeFiveIndex d) :
    (fun e : ℝ => e ^ 10) =O[nhds 0]
      (fun e : ℝ => e ^ ((q.1 : ℕ) + (r.1 : ℕ))) := by
  have hle : (q.1 : ℕ) + (r.1 : ℕ) ≤ 10 := by
    have hq := q.1.isLt
    have hr := r.1.isLt
    omega
  rcases hle.eq_or_lt with h | h
  · simpa [h] using
      (isBigO_refl (fun e : ℝ => e ^ 10) (nhds 0))
  · exact (isLittleO_pow_pow h).isBigO

def degreeFiveValueRemainder {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (q r : DegreeFiveIndex d) (e : ℝ) : ℝ :=
  (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramEntry lam nodes e i j) -
    ((if q = r then e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0) +
      e ^ 10 * (if q = r ∧ q.1 = topDegreeIndex 5 then
        lam ^ 2 * fockMonomialWeight q.2 else 0))

def degreeFiveFirstRemainder {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (q r : DegreeFiveIndex d) (e : ℝ) : ℝ :=
  (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramFirstEntry lam nodes e i j) -
    ((if q = r then
        (q.1 : ℝ) * e ^ (2 * (q.1 : ℕ)) * fockMonomialWeight q.2 else 0) +
      e ^ 10 * (if q = r ∧ q.1 = topDegreeIndex 5 then
        lam ^ 2 * fockMonomialWeight q.2 else 0))

def degreeFiveSecondRemainder {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (q r : DegreeFiveIndex d) (e : ℝ) : ℝ :=
  (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramSecondEntry lam nodes e i j) -
    (if q = r then
      ((q.1 : ℝ) * (q.1 - 1)) * e ^ (2 * (q.1 : ℕ)) *
        fockMonomialWeight q.2 else 0)

def degreeFiveNormalizedValueEntry {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (e : ℝ) (q r : DegreeFiveIndex d) : ℝ :=
  (if q = r then degreeFiveValueLimit lam q else 0) +
    degreeFiveValueRemainder lam nodes c q r e /
      e ^ ((q.1 : ℕ) + (r.1 : ℕ))

def degreeFiveNormalizedFirstEntry {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (e : ℝ) (q r : DegreeFiveIndex d) : ℝ :=
  (if q = r then degreeFiveFirstLimit lam q else 0) +
    degreeFiveFirstRemainder lam nodes c q r e /
      e ^ ((q.1 : ℕ) + (r.1 : ℕ))

def degreeFiveNormalizedSecondEntry {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (e : ℝ) (q r : DegreeFiveIndex d) : ℝ :=
  (if q = r then degreeFiveSecondLimit q else 0) +
    degreeFiveSecondRemainder lam nodes c q r e /
      e ^ ((q.1 : ℕ) + (r.1 : ℕ))

/-- **Normalised-entry convergence.**  A remainder that is `o(e^10)` at the origin survives division
by `e^(q+r)` -- the degree sum never exceeds ten -- so the normalised entry converges to its constant
term.  Nothing about the jet enters: the statement quantifies over an arbitrary constant and an
arbitrary remainder, which is why the value, first and second jets all instantiate it. -/
theorem tendsto_degreeFiveNormalizedEntry {d : ℕ}
    (limitVal : ℝ) (remainder : ℝ → ℝ)
    (hrem : remainder =o[nhds 0] fun e : ℝ => e ^ 10)
    (q r : DegreeFiveIndex d) :
    Tendsto (fun e => limitVal + remainder e / e ^ ((q.1 : ℕ) + (r.1 : ℕ))) (nhds 0)
      (nhds limitVal) := by
  have hsmall := hrem.trans_isBigO (degreeFive_pow_ten_isBigO_degreeSum q r)
  simpa using (tendsto_const_nhds (x := limitVal) (f := nhds (0 : ℝ))).add
    hsmall.tendsto_div_nhds_zero

theorem tendsto_degreeFiveNormalizedValueEntry {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    Tendsto (fun e => degreeFiveNormalizedValueEntry lam nodes c e q r) (nhds 0)
      (nhds (if q = r then degreeFiveValueLimit lam q else 0)) := by
  have hrem : degreeFiveValueRemainder lam nodes c q r =o[nhds 0] (fun e : ℝ => e ^ 10) := by
    simpa only [degreeFiveValueRemainder] using degreeFive_gaussianValueJet lam nodes c hdelta q r
  simpa only [degreeFiveNormalizedValueEntry] using
    tendsto_degreeFiveNormalizedEntry (if q = r then degreeFiveValueLimit lam q else 0)
      (degreeFiveValueRemainder lam nodes c q r) hrem q r

theorem tendsto_degreeFiveNormalizedFirstEntry {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    Tendsto (fun e => degreeFiveNormalizedFirstEntry lam nodes c e q r) (nhds 0)
      (nhds (if q = r then degreeFiveFirstLimit lam q else 0)) := by
  have hrem : degreeFiveFirstRemainder lam nodes c q r =o[nhds 0] (fun e : ℝ => e ^ 10) := by
    simpa only [degreeFiveFirstRemainder] using degreeFive_gaussianFirstJet lam nodes c hdelta q r
  simpa only [degreeFiveNormalizedFirstEntry] using
    tendsto_degreeFiveNormalizedEntry (if q = r then degreeFiveFirstLimit lam q else 0)
      (degreeFiveFirstRemainder lam nodes c q r) hrem q r

theorem tendsto_degreeFiveNormalizedSecondEntry {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (q r : DegreeFiveIndex d) :
    Tendsto (fun e => degreeFiveNormalizedSecondEntry lam nodes c e q r) (nhds 0)
      (nhds (if q = r then degreeFiveSecondLimit q else 0)) := by
  have hrem : degreeFiveSecondRemainder lam nodes c q r =o[nhds 0] (fun e : ℝ => e ^ 10) := by
    simpa only [degreeFiveSecondRemainder] using degreeFive_gaussianSecondJet lam nodes c hdelta q r
  simpa only [degreeFiveNormalizedSecondEntry] using
    tendsto_degreeFiveNormalizedEntry (if q = r then degreeFiveSecondLimit q else 0)
      (degreeFiveSecondRemainder lam nodes c q r) hrem q r

def degreeFiveNormalizedValueMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun q r => degreeFiveNormalizedValueEntry lam nodes c e q r

def degreeFiveNormalizedFirstMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun q r => degreeFiveNormalizedFirstEntry lam nodes c e q r

def degreeFiveNormalizedSecondMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun q r => degreeFiveNormalizedSecondEntry lam nodes c e q r

def degreeFiveValueLimitMatrix {d : ℕ} (lam : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  Matrix.diagonal (degreeFiveValueLimit lam)

def degreeFiveFirstLimitMatrix {d : ℕ} (lam : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  Matrix.diagonal (degreeFiveFirstLimit lam)

def degreeFiveSecondLimitMatrix {d : ℕ} :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  Matrix.diagonal degreeFiveSecondLimit

/-- **Entrywise convergence to a diagonal matrix.**  A matrix-valued family whose `(q, r)` entry
tends to `lim q` on the diagonal and to zero off it converges to `Matrix.diagonal lim`, since the
matrix topology is the product topology in both indices. -/
theorem tendsto_matrix_of_tendsto_entry {d : ℕ}
    {M : ℝ → Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ}
    {lim : DegreeFiveIndex d → ℝ}
    (h : ∀ q r, Tendsto (fun e => M e q r) (nhds 0) (nhds (if q = r then lim q else 0))) :
    Tendsto M (nhds 0) (nhds (Matrix.diagonal lim)) := by
  refine tendsto_pi_nhds.2 fun q => tendsto_pi_nhds.2 fun r => ?_
  simpa only [Matrix.diagonal_apply] using h q r

theorem tendsto_degreeFiveNormalizedValueMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    Tendsto (degreeFiveNormalizedValueMatrix lam nodes c) (nhds 0)
      (nhds (degreeFiveValueLimitMatrix lam)) := by
  refine tendsto_matrix_of_tendsto_entry (M := degreeFiveNormalizedValueMatrix lam nodes c) ?_
  intro q r
  simpa only [degreeFiveNormalizedValueMatrix] using
    tendsto_degreeFiveNormalizedValueEntry lam nodes c hdelta q r

theorem tendsto_degreeFiveNormalizedFirstMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    Tendsto (degreeFiveNormalizedFirstMatrix lam nodes c) (nhds 0)
      (nhds (degreeFiveFirstLimitMatrix lam)) := by
  refine tendsto_matrix_of_tendsto_entry (M := degreeFiveNormalizedFirstMatrix lam nodes c) ?_
  intro q r
  simpa only [degreeFiveNormalizedFirstMatrix] using
    tendsto_degreeFiveNormalizedFirstEntry lam nodes c hdelta q r

theorem tendsto_degreeFiveNormalizedSecondMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    Tendsto (degreeFiveNormalizedSecondMatrix lam nodes c) (nhds 0)
      (nhds degreeFiveSecondLimitMatrix) := by
  refine tendsto_matrix_of_tendsto_entry
    (M := degreeFiveNormalizedSecondMatrix lam nodes c) ?_
  intro q r
  simpa only [degreeFiveNormalizedSecondMatrix] using
    tendsto_degreeFiveNormalizedSecondEntry lam nodes c hdelta q r


def degreeFiveBalancedAmplitude : ℝ := Real.sqrt (5 / 3)

theorem degreeFive_balancedAmplitude_sq : degreeFiveBalancedAmplitude ^ 2 = (5 / 3 : ℝ) := by
  unfold degreeFiveBalancedAmplitude
  rw [Real.sq_sqrt]
  positivity

theorem degreeFive_balanced_curvatureSummand {d : ℕ} (q : DegreeFiveIndex d) :
    degreeFiveSecondLimit q / degreeFiveValueLimit degreeFiveBalancedAmplitude q -
        (degreeFiveFirstLimit degreeFiveBalancedAmplitude q /
          degreeFiveValueLimit degreeFiveBalancedAmplitude q) ^ 2 =
      if q.1 = topDegreeIndex 5 then (5 / 4 : ℝ) else -(q.1 : ℝ) := by
  have hw : fockMonomialWeight q.2 ≠ 0 :=
    ne_of_gt (fockMonomialWeight_pos q.2)
  by_cases htop : q.1 = topDegreeIndex 5
  · rw [if_pos htop]
    unfold degreeFiveValueLimit degreeFiveFirstLimit degreeFiveSecondLimit
    simp only [if_pos htop]
    rw [degreeFive_balancedAmplitude_sq]
    have hdegree : (q.1 : ℕ) = 5 := by
      simpa [topDegreeIndex] using congrArg Fin.val htop
    have hcast : (q.1 : ℝ) = 5 := by exact_mod_cast hdegree
    rw [hcast]
    field_simp [hw]
    ring
  · rw [if_neg htop]
    unfold degreeFiveValueLimit degreeFiveFirstLimit degreeFiveSecondLimit
    simp only [if_neg htop, add_zero, mul_one]
    field_simp [hw]
    ring

theorem degreeFive_curvatureSummand_sum (d : ℕ) :
    (∑ q : DegreeFiveIndex d,
      if q.1 = topDegreeIndex 5 then (5 / 4 : ℝ) else -(q.1 : ℝ)) =
      -(fullTopLoweringCharge d 5 : ℝ) +
        (5 / 4 : ℝ) * (fullTopCount d 5 : ℝ) := by
  rw [Fintype.sum_sigma]
  rw [Fin.sum_univ_castSucc]
  have hlower :
      (∑ n : Fin 5, ∑ _a : HomogeneousMultiIndex d n.castSucc,
        (if n.castSucc = topDegreeIndex 5 then (5 / 4 : ℝ)
          else -(n.castSucc : ℝ))) =
        -(fullTopLoweringCharge d 5 : ℝ) := by
    rw [Finset.sum_fin_eq_sum_range]
    unfold fullTopLoweringCharge
    push_cast
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnlt : n < 5 := Finset.mem_range.mp hn
    have hne : (⟨n, by omega⟩ : Fin 6) ≠ topDegreeIndex 5 := by
      intro h
      have := congrArg Fin.val h
      simp [topDegreeIndex] at this
      omega
    simp only [dif_pos hnlt, hne, if_false, Fin.castSucc_mk, Fin.val_mk]
    rw [Finset.sum_const, Finset.card_univ]
    calc
      Fintype.card (HomogeneousMultiIndex d n) • -(n : ℝ) =
          Nat.choose (d + n - 1) n • -(n : ℝ) :=
        congrArg (fun m : ℕ => m • -(n : ℝ)) (homogeneousMultiIndex_card d n)
      _ = -((n : ℝ) * (Nat.choose (d + n - 1) n : ℝ)) := by
        rw [nsmul_eq_mul]
        ring
  have htop : Fin.last 5 = topDegreeIndex 5 := by
    apply Fin.ext
    simp [topDegreeIndex]
  have htopSum :
      (∑ _a : HomogeneousMultiIndex d 5, (5 / 4 : ℝ)) =
        (5 / 4 : ℝ) * (fullTopCount d 5 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ]
    calc
      Fintype.card (HomogeneousMultiIndex d 5) • (5 / 4 : ℝ) =
          Nat.choose (d + 5 - 1) 5 • (5 / 4 : ℝ) :=
        congrArg (fun m : ℕ => m • (5 / 4 : ℝ)) (homogeneousMultiIndex_card d 5)
      _ = _ := by
        rw [nsmul_eq_mul]
        unfold fullTopCount
        push_cast
        ring
  rw [hlower]
  simp only [htop, Fin.val_last, if_true]
  change -(fullTopLoweringCharge d 5 : ℝ) +
      (∑ _a : HomogeneousMultiIndex d 5, (5 / 4 : ℝ)) = _
  rw [htopSum]

theorem degreeFiveValueLimit_pos {d : ℕ} (lam : ℝ) (q : DegreeFiveIndex d) :
    0 < degreeFiveValueLimit lam q := by
  unfold degreeFiveValueLimit
  apply mul_pos (fockMonomialWeight_pos q.2)
  by_cases htop : q.1 = topDegreeIndex 5
  · rw [if_pos htop]
    positivity
  · rw [if_neg htop]
    positivity

theorem degreeFiveValueLimitMatrix_det_ne_zero {d : ℕ} (lam : ℝ) :
    (degreeFiveValueLimitMatrix (d := d) lam).det ≠ 0 := by
  unfold degreeFiveValueLimitMatrix
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun q hq => ne_of_gt (degreeFiveValueLimit_pos lam q)

theorem degreeFiveBalanced_limit_curvature (d : ℕ) :
    gramLogCurvatureJet
        (degreeFiveValueLimitMatrix (d := d) degreeFiveBalancedAmplitude)
        (degreeFiveFirstLimitMatrix (d := d) degreeFiveBalancedAmplitude)
        (degreeFiveSecondLimitMatrix (d := d)) =
      -(fullTopLoweringCharge d 5 : ℝ) +
        (5 / 4 : ℝ) * (fullTopCount d 5 : ℝ) := by
  unfold degreeFiveValueLimitMatrix degreeFiveFirstLimitMatrix degreeFiveSecondLimitMatrix
  rw [gramLogCurvatureJet_diagonal_of_ne]
  · simpa only [degreeFive_balanced_curvatureSummand] using
      degreeFive_curvatureSummand_sum d
  · intro q
    exact ne_of_gt (degreeFiveValueLimit_pos degreeFiveBalancedAmplitude q)

theorem degreeFiveSixteen_limit_curvature :
    gramLogCurvatureJet
        (degreeFiveValueLimitMatrix (d := 16) degreeFiveBalancedAmplitude)
        (degreeFiveFirstLimitMatrix (d := 16) degreeFiveBalancedAmplitude)
        (degreeFiveSecondLimitMatrix (d := 16)) =
      (5 / 68 : ℝ) * (fullTopCount 16 5 : ℝ) := by
  rw [degreeFiveBalanced_limit_curvature]
  have hcross := fullTopLoweringCharge_cross 16 3
  change 17 * fullTopLoweringCharge 16 5 = 5 * 4 * fullTopCount 16 5 at hcross
  have hcrossReal :
      (17 : ℝ) * (fullTopLoweringCharge 16 5 : ℝ) =
        (5 : ℝ) * 4 * (fullTopCount 16 5 : ℝ) := by
    exact_mod_cast hcross
  linarith

theorem degreeFiveSixteen_limit_curvature_pos :
    0 < gramLogCurvatureJet
        (degreeFiveValueLimitMatrix (d := 16) degreeFiveBalancedAmplitude)
        (degreeFiveFirstLimitMatrix (d := 16) degreeFiveBalancedAmplitude)
        (degreeFiveSecondLimitMatrix (d := 16)) := by
  rw [degreeFiveSixteen_limit_curvature]
  have hkNat : 0 < fullTopCount 16 5 := by
    unfold fullTopCount
    exact Nat.choose_pos (by omega)
  have hk : (0 : ℝ) < (fullTopCount 16 5 : ℝ) := by exact_mod_cast hkNat
  exact mul_pos (by positivity) hk

theorem eventually_pos_degreeFiveSixteen_normalizedCurvature
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in nhds 0,
      0 < gramLogCurvatureJet
        (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e)
        (degreeFiveNormalizedFirstMatrix degreeFiveBalancedAmplitude nodes c e)
        (degreeFiveNormalizedSecondMatrix degreeFiveBalancedAmplitude nodes c e) := by
  exact eventually_pos_gramLogCurvatureJet
    (tendsto_degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c hdelta)
    (tendsto_degreeFiveNormalizedFirstMatrix degreeFiveBalancedAmplitude nodes c hdelta)
    (tendsto_degreeFiveNormalizedSecondMatrix degreeFiveBalancedAmplitude nodes c hdelta)
    (degreeFiveValueLimitMatrix_det_ne_zero degreeFiveBalancedAmplitude)
    degreeFiveSixteen_limit_curvature_pos

theorem degreeFiveNormalizedValueEntry_eq_recombined_div {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) (q r : DegreeFiveIndex d) :
    degreeFiveNormalizedValueEntry lam nodes c e q r =
      (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramEntry lam nodes e i j) /
        e ^ ((q.1 : ℕ) + (r.1 : ℕ)) := by
  by_cases hqr : q = r
  · subst r
    by_cases htop : q.1 = topDegreeIndex 5
    · unfold degreeFiveNormalizedValueEntry degreeFiveValueRemainder degreeFiveValueLimit
      simp only [htop, and_self, if_true]
      norm_num [topDegreeIndex]
      field_simp [pow_ne_zero 10 he]
      ring
    · have hexp : (q.1 : ℕ) + (q.1 : ℕ) = 2 * (q.1 : ℕ) := by omega
      unfold degreeFiveNormalizedValueEntry degreeFiveValueRemainder degreeFiveValueLimit
      simp only [htop, and_false, if_false, add_zero, mul_one]
      rw [hexp]
      simp only [if_true]
      field_simp [pow_ne_zero (2 * (q.1 : ℕ)) he]
      ring
  · unfold degreeFiveNormalizedValueEntry degreeFiveValueRemainder
    simp only [if_neg hqr]
    have htrans : ¬(q = r ∧ q.1 = topDegreeIndex 5) := fun h => hqr h.1
    simp only [htrans, if_false, add_zero, zero_add, mul_zero, sub_zero]

theorem degreeFiveNormalizedFirstEntry_eq_recombined_div {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) (q r : DegreeFiveIndex d) :
    degreeFiveNormalizedFirstEntry lam nodes c e q r =
      (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramFirstEntry lam nodes e i j) /
        e ^ ((q.1 : ℕ) + (r.1 : ℕ)) := by
  by_cases hqr : q = r
  · subst r
    by_cases htop : q.1 = topDegreeIndex 5
    · unfold degreeFiveNormalizedFirstEntry degreeFiveFirstRemainder degreeFiveFirstLimit
      simp only [htop, and_self, if_true]
      norm_num [topDegreeIndex]
      field_simp [pow_ne_zero 10 he]
      ring
    · have hexp : (q.1 : ℕ) + (q.1 : ℕ) = 2 * (q.1 : ℕ) := by omega
      unfold degreeFiveNormalizedFirstEntry degreeFiveFirstRemainder degreeFiveFirstLimit
      simp only [htop, and_false, if_false, add_zero]
      rw [hexp]
      simp only [if_true]
      field_simp [pow_ne_zero (2 * (q.1 : ℕ)) he]
      ring
  · unfold degreeFiveNormalizedFirstEntry degreeFiveFirstRemainder
    simp only [if_neg hqr]
    have htrans : ¬(q = r ∧ q.1 = topDegreeIndex 5) := fun h => hqr h.1
    simp only [htrans, if_false, add_zero, zero_add, mul_zero, sub_zero]

theorem degreeFiveNormalizedSecondEntry_eq_recombined_div {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) (q r : DegreeFiveIndex d) :
    degreeFiveNormalizedSecondEntry lam nodes c e q r =
      (∑ i, ∑ j, c q i * c r j * gaussianCollisionGramSecondEntry lam nodes e i j) /
        e ^ ((q.1 : ℕ) + (r.1 : ℕ)) := by
  by_cases hqr : q = r
  · subst r
    have hexp : (q.1 : ℕ) + (q.1 : ℕ) = 2 * (q.1 : ℕ) := by omega
    unfold degreeFiveNormalizedSecondEntry degreeFiveSecondRemainder degreeFiveSecondLimit
    rw [hexp]
    simp only [if_true]
    field_simp [pow_ne_zero (2 * (q.1 : ℕ)) he]
    ring
  · unfold degreeFiveNormalizedSecondEntry degreeFiveSecondRemainder
    simp only [if_neg hqr, zero_add, sub_zero]


def degreeFiveRecombinedValueMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun q r => ∑ i, ∑ j, c q i * c r j * gaussianCollisionGramEntry lam nodes e i j

def degreeFiveRecombinedFirstMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun q r => ∑ i, ∑ j, c q i * c r j * gaussianCollisionGramFirstEntry lam nodes e i j

def degreeFiveRecombinedSecondMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun q r => ∑ i, ∑ j, c q i * c r j * gaussianCollisionGramSecondEntry lam nodes e i j

def degreeFiveInverseScaleMatrix {d : ℕ} (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  Matrix.diagonal fun q => (e ^ (q.1 : ℕ))⁻¹

theorem degreeFiveInverseScaleMatrix_det_isUnit {d : ℕ} {e : ℝ} (he : e ≠ 0) :
    IsUnit (degreeFiveInverseScaleMatrix (d := d) e).det := by
  apply (isUnit_iff_ne_zero).mpr
  unfold degreeFiveInverseScaleMatrix
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun q hq => inv_ne_zero (pow_ne_zero _ he)

/-- **Entrywise degree normalisation is diagonal conjugation.**  A matrix whose `(q, r)` entry is the
corresponding entry of `R` divided by `e ^ (deg q + deg r)` is exactly `R` conjugated by the inverse
scale matrix.  The identity is entrywise and uses nothing about `R`. -/
theorem matrix_eq_scale_conj_of_entry_div {d : ℕ}
    {N R : Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ} {e : ℝ} (he : e ≠ 0)
    (h : ∀ q r, N q r = R q r / e ^ ((q.1 : ℕ) + (r.1 : ℕ))) :
    N = degreeFiveInverseScaleMatrix e * R * degreeFiveInverseScaleMatrix e := by
  ext q r
  rw [h q r]
  simp only [degreeFiveInverseScaleMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [pow_add]
  field_simp [pow_ne_zero (q.1 : ℕ) he, pow_ne_zero (r.1 : ℕ) he]

theorem degreeFiveNormalizedValueMatrix_eq_scale_recombined {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) :
    degreeFiveNormalizedValueMatrix lam nodes c e =
      degreeFiveInverseScaleMatrix e * degreeFiveRecombinedValueMatrix lam nodes c e *
        degreeFiveInverseScaleMatrix e := by
  refine matrix_eq_scale_conj_of_entry_div he ?_
  intro q r
  exact degreeFiveNormalizedValueEntry_eq_recombined_div lam nodes c he q r

theorem degreeFiveNormalizedFirstMatrix_eq_scale_recombined {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) :
    degreeFiveNormalizedFirstMatrix lam nodes c e =
      degreeFiveInverseScaleMatrix e * degreeFiveRecombinedFirstMatrix lam nodes c e *
        degreeFiveInverseScaleMatrix e := by
  refine matrix_eq_scale_conj_of_entry_div he ?_
  intro q r
  exact degreeFiveNormalizedFirstEntry_eq_recombined_div lam nodes c he q r

theorem degreeFiveNormalizedSecondMatrix_eq_scale_recombined {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) :
    degreeFiveNormalizedSecondMatrix lam nodes c e =
      degreeFiveInverseScaleMatrix e * degreeFiveRecombinedSecondMatrix lam nodes c e *
        degreeFiveInverseScaleMatrix e := by
  refine matrix_eq_scale_conj_of_entry_div he ?_
  intro q r
  exact degreeFiveNormalizedSecondEntry_eq_recombined_div lam nodes c he q r

theorem degreeFive_normalizedCurvature_eq_recombined {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0) :
    gramLogCurvatureJet
        (degreeFiveNormalizedValueMatrix lam nodes c e)
        (degreeFiveNormalizedFirstMatrix lam nodes c e)
        (degreeFiveNormalizedSecondMatrix lam nodes c e) =
      gramLogCurvatureJet
        (degreeFiveRecombinedValueMatrix lam nodes c e)
        (degreeFiveRecombinedFirstMatrix lam nodes c e)
        (degreeFiveRecombinedSecondMatrix lam nodes c e) := by
  rw [degreeFiveNormalizedValueMatrix_eq_scale_recombined lam nodes c he,
    degreeFiveNormalizedFirstMatrix_eq_scale_recombined lam nodes c he,
    degreeFiveNormalizedSecondMatrix_eq_scale_recombined lam nodes c he]
  exact gramLogCurvatureJet_congr _ _ _ _ (degreeFiveInverseScaleMatrix_det_isUnit he)


def degreeFiveCoefficientMatrix {d : ℕ}
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ := c

def degreeFiveEvaluationMatrix {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ)) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun i q => monomialFeature GradedMultiIndex.exponent q (nodes i)

def degreeFiveGaussianValueMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  gaussianCollisionGramEntry lam nodes e

def degreeFiveGaussianFirstMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  gaussianCollisionGramFirstEntry lam nodes e

def degreeFiveGaussianSecondMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) :
    Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  gaussianCollisionGramSecondEntry lam nodes e

theorem degreeFiveCoefficientMatrix_mul_evaluationMatrix {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    degreeFiveCoefficientMatrix c * degreeFiveEvaluationMatrix nodes = 1 := by
  ext q r
  rw [Matrix.mul_apply]
  simp only [degreeFiveCoefficientMatrix, degreeFiveEvaluationMatrix, Matrix.one_apply]
  exact hdelta q r

theorem degreeFiveCoefficientMatrix_det_isUnit {d : ℕ}
    (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    IsUnit (degreeFiveCoefficientMatrix c).det := by
  exact Matrix.isUnit_det_of_right_inverse
    (degreeFiveCoefficientMatrix_mul_evaluationMatrix nodes c hdelta)

/-- **A coefficient-weighted double sum is a matrix congruence.**  If `R q r = ∑ i ∑ j, c q i · c r j ·
G i j`, then `R = C · G · Cᵀ` for the coefficient matrix `C = c`.  This is the entrywise expansion of
matrix multiplication and uses nothing about `G`. -/
theorem matrix_eq_congr_of_double_sum {d : ℕ}
    {R G : Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ}
    {c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ}
    (h : ∀ q r, R q r = ∑ i, ∑ j, c q i * c r j * G i j) :
    R = degreeFiveCoefficientMatrix c * G * Matrix.transpose (degreeFiveCoefficientMatrix c) := by
  ext q r
  rw [h q r]
  simp only [degreeFiveCoefficientMatrix, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem degreeFiveRecombinedValueMatrix_eq_congr {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    degreeFiveRecombinedValueMatrix lam nodes c e =
      degreeFiveCoefficientMatrix c * degreeFiveGaussianValueMatrix lam nodes e *
        Matrix.transpose (degreeFiveCoefficientMatrix c) := by
  exact matrix_eq_congr_of_double_sum fun q r => rfl

theorem degreeFiveRecombinedFirstMatrix_eq_congr {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    degreeFiveRecombinedFirstMatrix lam nodes c e =
      degreeFiveCoefficientMatrix c * degreeFiveGaussianFirstMatrix lam nodes e *
        Matrix.transpose (degreeFiveCoefficientMatrix c) := by
  exact matrix_eq_congr_of_double_sum fun q r => rfl

theorem degreeFiveRecombinedSecondMatrix_eq_congr {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ) (e : ℝ) :
    degreeFiveRecombinedSecondMatrix lam nodes c e =
      degreeFiveCoefficientMatrix c * degreeFiveGaussianSecondMatrix lam nodes e *
        Matrix.transpose (degreeFiveCoefficientMatrix c) := by
  exact matrix_eq_congr_of_double_sum fun q r => rfl

theorem degreeFive_recombinedCurvature_eq_gaussian {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0)
    (e : ℝ) :
    gramLogCurvatureJet
        (degreeFiveRecombinedValueMatrix lam nodes c e)
        (degreeFiveRecombinedFirstMatrix lam nodes c e)
        (degreeFiveRecombinedSecondMatrix lam nodes c e) =
      gramLogCurvatureJet
        (degreeFiveGaussianValueMatrix lam nodes e)
        (degreeFiveGaussianFirstMatrix lam nodes e)
        (degreeFiveGaussianSecondMatrix lam nodes e) := by
  rw [degreeFiveRecombinedValueMatrix_eq_congr,
    degreeFiveRecombinedFirstMatrix_eq_congr,
    degreeFiveRecombinedSecondMatrix_eq_congr]
  have hC := degreeFiveCoefficientMatrix_det_isUnit nodes c hdelta
  have hCT : IsUnit (Matrix.transpose (degreeFiveCoefficientMatrix c)).det :=
    Matrix.isUnit_det_transpose (degreeFiveCoefficientMatrix c) hC
  exact gramLogCurvatureJet_mul_equiv _ _ _ _ _ hC hCT

theorem eventually_pos_degreeFiveSixteen_gaussianCurvature
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      0 < gramLogCurvatureJet
        (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e)
        (degreeFiveGaussianFirstMatrix degreeFiveBalancedAmplitude nodes e)
        (degreeFiveGaussianSecondMatrix degreeFiveBalancedAmplitude nodes e) := by
  have hpos := eventually_pos_degreeFiveSixteen_normalizedCurvature nodes c hdelta
  have hposNE : ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      0 < gramLogCurvatureJet
        (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e)
        (degreeFiveNormalizedFirstMatrix degreeFiveBalancedAmplitude nodes c e)
        (degreeFiveNormalizedSecondMatrix degreeFiveBalancedAmplitude nodes c e) :=
    hpos.filter_mono inf_le_left
  filter_upwards [hposNE, self_mem_nhdsWithin] with e hepos he
  have he0 : e ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using he
  rw [degreeFive_normalizedCurvature_eq_recombined degreeFiveBalancedAmplitude nodes c he0,
    degreeFive_recombinedCurvature_eq_gaussian degreeFiveBalancedAmplitude nodes c hdelta e] at hepos
  exact hepos

theorem exists_degreeFiveSixteen_gaussianPositiveCurvature
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∃ e : ℝ, e ≠ 0 ∧
      0 < gramLogCurvatureJet
        (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e)
        (degreeFiveGaussianFirstMatrix degreeFiveBalancedAmplitude nodes e)
        (degreeFiveGaussianSecondMatrix degreeFiveBalancedAmplitude nodes e) := by
  have hpos := eventually_pos_degreeFiveSixteen_gaussianCurvature nodes c hdelta
  have hmem : ∀ᶠ e in 𝓝[≠] (0 : ℝ), e ∈ ({0} : Set ℝ)ᶜ := self_mem_nhdsWithin
  obtain ⟨e, hepos, he⟩ := (hpos.and hmem).exists
  exact ⟨e, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using he, hepos⟩


/-- Exponential inner-product Gram matrix of a finite real coordinate family. -/
def finiteExponentialInnerGram {ι κ : Type*} [Fintype κ]
    (x : ι → κ → ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (t * ∑ a, x i a * x j a)

/-- Conventional Gaussian distance Gram matrix of a finite real coordinate family. -/
def finiteGaussianDistanceGram {ι κ : Type*} [Fintype κ]
    (x : ι → κ → ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (-t * ∑ a, (x i a - x j a) ^ 2)

/-- Half-scaled Gaussian distance Gram matching coherent inner-product scale `t`. -/
def finiteHalfGaussianDistanceGram {ι κ : Type*} [Fintype κ]
    (x : ι → κ → ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.exp (-(t / 2) * ∑ a, (x i a - x j a) ^ 2)

def finiteGaussianGauge {ι κ : Type*} [Fintype κ]
    (x : ι → κ → ℝ) (t : ℝ) (i : ι) : ℝ :=
  Real.exp (-(t / 2) * ∑ a, x i a ^ 2)

theorem hasDerivAt_finiteExponentialInnerGram {ι κ : Type*} [Fintype κ]
    (x : ι → κ → ℝ) (t : ℝ) (i j : ι) :
    HasDerivAt (fun u => finiteExponentialInnerGram x u i j)
      ((∑ a, x i a * x j a) * finiteExponentialInnerGram x t i j) t := by
  let z : ℝ := ∑ a, x i a * x j a
  have hz : HasDerivAt (fun u : ℝ => u * z) z t := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (x := t)).mul_const z
  simpa [finiteExponentialInnerGram, z, mul_comm] using hz.exp

/-- A Gaussian distance Gram is a diagonal gauge of its exponential inner-product Gram. -/
theorem finiteHalfGaussianDistanceGram_eq_gauge {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (x : ι → κ → ℝ) (t : ℝ) :
    finiteHalfGaussianDistanceGram x t =
      Matrix.diagonal (finiteGaussianGauge x t) *
        finiteExponentialInnerGram x t *
          Matrix.diagonal (finiteGaussianGauge x t) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  simp
  simp only [finiteHalfGaussianDistanceGram, finiteGaussianGauge,
    finiteExponentialInnerGram]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Finset.sum_congr rfl (fun a _ => show (x i a - x j a) ^ 2 =
    x i a ^ 2 + x j a ^ 2 - 2 * (x i a * x j a) by ring_nf),
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  ring_nf

theorem finiteHalfGaussianDistanceGram_det {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (x : ι → κ → ℝ) (t : ℝ) :
    (finiteHalfGaussianDistanceGram x t).det =
      Real.exp (-t * ∑ i, ∑ a, x i a ^ 2) *
        (finiteExponentialInnerGram x t).det := by
  rw [finiteHalfGaussianDistanceGram_eq_gauge, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal]
  have hg : ∏ i, finiteGaussianGauge x t i =
      Real.exp (-(t / 2) * ∑ i, ∑ a, x i a ^ 2) := by
    simp only [finiteGaussianGauge]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  rw [hg]
  calc
    _ = (Real.exp (-(t / 2) * ∑ i, ∑ a, x i a ^ 2) *
        Real.exp (-(t / 2) * ∑ i, ∑ a, x i a ^ 2)) *
          (finiteExponentialInnerGram x t).det := by ring_nf
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

/-- Dividing every point by `sqrt 2` converts the conventional Gaussian parameterization
to the half-scaled coherent parameterization. -/
theorem finiteGaussianDistanceGram_div_sqrtTwo {ι κ : Type*}
    [Fintype κ] (x : ι → κ → ℝ) (t : ℝ) :
    finiteGaussianDistanceGram (fun i a => x i a / Real.sqrt 2) t =
      finiteHalfGaussianDistanceGram x t := by
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext i j
  simp only [finiteGaussianDistanceGram, finiteHalfGaussianDistanceGram]
  congr 1
  rw [Finset.sum_congr rfl (fun a _ => show
    (x i a / Real.sqrt 2 - x j a / Real.sqrt 2) ^ 2 =
      (x i a - x j a) ^ 2 / 2 by
        field_simp [hsqrt]
        nlinarith)]
  rw [← Finset.sum_div]
  ring_nf

theorem secondDerivative_affine_add
    (f : ℝ → ℝ) (c x : ℝ)
    (hf : ∀ᶠ t in nhds x, DifferentiableAt ℝ f t) :
    deriv (deriv (fun t => -t * c + f t)) x = deriv (deriv f) x := by
  have hfirst :
      deriv (fun t => -t * c + f t) =ᶠ[nhds x]
        fun t => deriv f t - c := by
    filter_upwards [hf] with t ht
    have hlin : HasDerivAt (fun s : ℝ => -s * c) (-c) t := by
      convert (hasDerivAt_id (x := t)).neg.mul_const c using 1
      all_goals ring_nf
    have hadd := hlin.add ht.hasDerivAt
    convert hadd.deriv using 1
    all_goals ring_nf
  calc
    deriv (deriv (fun t => -t * c + f t)) x =
        deriv (fun t => deriv f t - c) x := hfirst.deriv_eq
    _ = deriv (deriv f) x := deriv_sub_const c

/-- A diagonal exponential gauge contributes only an affine term to `log det`, so it leaves
literal second log-determinant curvature unchanged. -/
theorem finiteHalfGaussianDistance_logDet_secondDerivative_eq {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (x : ι → κ → ℝ) (s : ℝ)
    (hdet : ∀ᶠ t in nhds s, (finiteExponentialInnerGram x t).det ≠ 0) :
    deriv (deriv (fun t => Real.log (finiteHalfGaussianDistanceGram x t).det)) s =
      deriv (deriv (fun t => Real.log (finiteExponentialInnerGram x t).det)) s := by
  let c : ℝ := ∑ i, ∑ a, x i a ^ 2
  let f : ℝ → ℝ := fun t => Real.log (finiteExponentialInnerGram x t).det
  have hlog :
      (fun t => Real.log (finiteHalfGaussianDistanceGram x t).det) =ᶠ[nhds s]
        fun t => -t * c + f t := by
    filter_upwards [hdet] with t ht
    rw [finiteHalfGaussianDistanceGram_det, Real.log_mul (Real.exp_ne_zero _) ht,
      Real.log_exp]
  have hfdiff : ∀ᶠ t in nhds s, DifferentiableAt ℝ f t := by
    filter_upwards [hdet] with t ht
    dsimp [f]
    exact ((hasDerivAt_matrixDet (finiteExponentialInnerGram x)
      (fun i j => (∑ a, x i a * x j a) * finiteExponentialInnerGram x t i j)
      t (hasDerivAt_finiteExponentialInnerGram x t)).log ht).differentiableAt
  calc
    deriv (deriv (fun t => Real.log (finiteHalfGaussianDistanceGram x t).det)) s =
        deriv (deriv (fun t => -t * c + f t)) s := hlog.deriv.deriv_eq
    _ = deriv (deriv f) s := secondDerivative_affine_add f c s hfdiff
    _ = deriv (deriv (fun t => Real.log (finiteExponentialInnerGram x t).det)) s := rfl

theorem eventually_ne_degreeFiveNormalizedValueMatrix_det
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in nhds (0 : ℝ),
      (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e).det ≠ 0 := by
  have hm : Tendsto
      (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c)
      (nhds 0)
      (nhds (degreeFiveValueLimitMatrix (d := 16) degreeFiveBalancedAmplitude)) :=
    tendsto_degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c hdelta
  have hc : ContinuousAt
      (fun A : Matrix (DegreeFiveIndex 16) (DegreeFiveIndex 16) ℝ => A.det)
      (degreeFiveValueLimitMatrix (d := 16) degreeFiveBalancedAmplitude) :=
    continuous_id.matrix_det.continuousAt
  have ht : Tendsto
      (fun e => (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e).det)
      (nhds 0)
      (nhds (degreeFiveValueLimitMatrix
        (d := 16) degreeFiveBalancedAmplitude).det) :=
    hc.tendsto.comp hm
  have hnhds : ({0} : Set ℝ)ᶜ ∈
      nhds (degreeFiveValueLimitMatrix (d := 16) degreeFiveBalancedAmplitude).det :=
    isOpen_compl_singleton.mem_nhds (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        degreeFiveValueLimitMatrix_det_ne_zero (d := 16) degreeFiveBalancedAmplitude)
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht.eventually hnhds

theorem degreeFiveGaussianValueMatrix_det_ne_zero_of_normalized {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (c : DegreeFiveIndex d → DegreeFiveIndex d → ℝ)
    {e : ℝ} (he : e ≠ 0)
    (hnorm : (degreeFiveNormalizedValueMatrix lam nodes c e).det ≠ 0) :
    (degreeFiveGaussianValueMatrix lam nodes e).det ≠ 0 := by
  intro hgauss
  have hrecombined : (degreeFiveRecombinedValueMatrix lam nodes c e).det = 0 := by
    rw [degreeFiveRecombinedValueMatrix_eq_congr, Matrix.det_mul, Matrix.det_mul,
      hgauss, mul_zero, zero_mul]
  have hnormalized : (degreeFiveNormalizedValueMatrix lam nodes c e).det = 0 := by
    rw [degreeFiveNormalizedValueMatrix_eq_scale_recombined lam nodes c he,
      Matrix.det_mul, Matrix.det_mul, hrecombined, mul_zero, zero_mul]
  exact hnorm hnormalized

theorem eventually_ne_degreeFiveSixteen_gaussianValueMatrix_det
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e).det ≠ 0 := by
  have hnorm := eventually_ne_degreeFiveNormalizedValueMatrix_det nodes c hdelta
  have hnormNE : ∀ᶠ e in 𝓝[≠] (0 : ℝ),
      (degreeFiveNormalizedValueMatrix degreeFiveBalancedAmplitude nodes c e).det ≠ 0 :=
    hnorm.filter_mono inf_le_left
  filter_upwards [hnormNE, self_mem_nhdsWithin] with e hdet he
  have he0 : e ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using he
  exact degreeFiveGaussianValueMatrix_det_ne_zero_of_normalized
    degreeFiveBalancedAmplitude nodes c he0 hdet

def degreeFiveGaussianBandwidthMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (e t : ℝ) : Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun i j => Real.exp (t * (∑ x,
    degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x))

def degreeFiveGaussianBandwidthFirstMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (e t : ℝ) : Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun i j => (∑ x,
    degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x) *
      degreeFiveGaussianBandwidthMatrix lam nodes e t i j

def degreeFiveGaussianBandwidthSecondMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ))
    (e t : ℝ) : Matrix (DegreeFiveIndex d) (DegreeFiveIndex d) ℝ :=
  fun i j => (∑ x,
    degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x) ^ 2 *
      degreeFiveGaussianBandwidthMatrix lam nodes e t i j

theorem hasDerivAt_degreeFiveGaussianBandwidthMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e t : ℝ)
    (i j : DegreeFiveIndex d) :
    HasDerivAt (fun s => degreeFiveGaussianBandwidthMatrix lam nodes e s i j)
      (degreeFiveGaussianBandwidthFirstMatrix lam nodes e t i j) t := by
  let z : ℝ := ∑ x,
    degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x
  have hz : HasDerivAt (fun s : ℝ => s * z) z t :=
    by simpa only [id_eq, one_mul] using (hasDerivAt_id (x := t)).mul_const z
  simpa [degreeFiveGaussianBandwidthMatrix, degreeFiveGaussianBandwidthFirstMatrix, z,
    mul_comm] using hz.exp

theorem hasDerivAt_degreeFiveGaussianBandwidthFirstMatrix {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e t : ℝ)
    (i j : DegreeFiveIndex d) :
    HasDerivAt (fun s => degreeFiveGaussianBandwidthFirstMatrix lam nodes e s i j)
      (degreeFiveGaussianBandwidthSecondMatrix lam nodes e t i j) t := by
  let z : ℝ := ∑ x,
    degreeFiveCollisionPoint lam nodes e i x * degreeFiveCollisionPoint lam nodes e j x
  have hz : HasDerivAt (fun s : ℝ => s * z) z t :=
    by simpa only [id_eq, one_mul] using (hasDerivAt_id (x := t)).mul_const z
  change HasDerivAt (fun s => z * Real.exp (s * z))
    (z ^ 2 * Real.exp (t * z)) t
  convert hz.exp.const_mul z using 1
  all_goals ring_nf

theorem degreeFiveGaussianBandwidthMatrix_one {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) :
    degreeFiveGaussianBandwidthMatrix lam nodes e 1 =
      degreeFiveGaussianValueMatrix lam nodes e := by
  ext i j
  simp [degreeFiveGaussianBandwidthMatrix, degreeFiveGaussianValueMatrix,
    gaussianCollisionGramEntry]

theorem degreeFiveGaussianBandwidthFirstMatrix_one {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) :
    degreeFiveGaussianBandwidthFirstMatrix lam nodes e 1 =
      degreeFiveGaussianFirstMatrix lam nodes e := by
  ext i j
  simp [degreeFiveGaussianBandwidthFirstMatrix, degreeFiveGaussianBandwidthMatrix,
    degreeFiveGaussianFirstMatrix, gaussianCollisionGramFirstEntry,
    gaussianCollisionGramEntry]

theorem degreeFiveGaussianBandwidthSecondMatrix_one {d : ℕ}
    (lam : ℝ) (nodes : DegreeFiveIndex d → (Fin d → ℝ)) (e : ℝ) :
    degreeFiveGaussianBandwidthSecondMatrix lam nodes e 1 =
      degreeFiveGaussianSecondMatrix lam nodes e := by
  ext i j
  simp [degreeFiveGaussianBandwidthSecondMatrix, degreeFiveGaussianBandwidthMatrix,
    degreeFiveGaussianSecondMatrix, gaussianCollisionGramSecondEntry,
    gaussianCollisionGramEntry]

theorem exists_degreeFiveSixteen_gaussianPositiveLogDetCurvature
    (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ))
    (c : DegreeFiveIndex 16 → DegreeFiveIndex 16 → ℝ)
    (hdelta : ∀ q r, ∑ i, c q i * monomialFeature GradedMultiIndex.exponent r (nodes i) =
      if q = r then 1 else 0) :
    ∃ e : ℝ, e ≠ 0 ∧
      (degreeFiveGaussianValueMatrix degreeFiveBalancedAmplitude nodes e).det ≠ 0 ∧
      0 < deriv (deriv (fun t => Real.log
        (degreeFiveGaussianBandwidthMatrix degreeFiveBalancedAmplitude nodes e t).det)) 1 := by
  have hpos := eventually_pos_degreeFiveSixteen_gaussianCurvature nodes c hdelta
  have hdet := eventually_ne_degreeFiveSixteen_gaussianValueMatrix_det nodes c hdelta
  have hmem : ∀ᶠ e in 𝓝[≠] (0 : ℝ), e ∈ ({0} : Set ℝ)ᶜ := self_mem_nhdsWithin
  obtain ⟨e, hepos, hedet, he⟩ := (hpos.and (hdet.and hmem)).exists
  have he0 : e ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using he
  let A := degreeFiveGaussianBandwidthMatrix degreeFiveBalancedAmplitude nodes e
  let A₁ := degreeFiveGaussianBandwidthFirstMatrix degreeFiveBalancedAmplitude nodes e
  let A₂ := degreeFiveGaussianBandwidthSecondMatrix degreeFiveBalancedAmplitude nodes e
  have hA (t : ℝ) (i j : DegreeFiveIndex 16) :
      HasDerivAt (fun s => A s i j) (A₁ t i j) t :=
    hasDerivAt_degreeFiveGaussianBandwidthMatrix _ _ _ _ _ _
  have hA₁ (t : ℝ) (i j : DegreeFiveIndex 16) :
      HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t :=
    hasDerivAt_degreeFiveGaussianBandwidthFirstMatrix _ _ _ _ _ _
  have hdetAt := hasDerivAt_matrixDet A (A₁ 1) 1 (hA 1)
  have hdetOne : (A 1).det ≠ 0 := by
    simpa [A, degreeFiveGaussianBandwidthMatrix_one] using hedet
  have hdetNhds : ∀ᶠ t in nhds (1 : ℝ), (A t).det ≠ 0 :=
    (hdetAt.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hdetOne
  have hliteral := logDet_secondDerivative_eq_gramLogCurvatureJet
    A A₁ A₂ 1 hA hA₁ hdetNhds
  refine ⟨e, he0, hedet, ?_⟩
  rw [hliteral]
  simpa [A, A₁, A₂, degreeFiveGaussianBandwidthMatrix_one,
    degreeFiveGaussianBandwidthFirstMatrix_one,
    degreeFiveGaussianBandwidthSecondMatrix_one] using hepos

theorem exists_distinct_degreeFiveSixteen_gaussianPositiveLogDetCurvature :
    ∃ (nodes : DegreeFiveIndex 16 → (Fin 16 → ℝ)) (e : ℝ),
      Function.Injective nodes ∧ e ≠ 0 ∧
      Function.Injective (degreeFiveCollisionPoint degreeFiveBalancedAmplitude nodes e) ∧
      0 < deriv (deriv (fun t => Real.log
        (degreeFiveGaussianBandwidthMatrix degreeFiveBalancedAmplitude nodes e t).det)) 1 := by
  obtain ⟨nodes, c, hnodes, hdelta⟩ := exists_gradedMonomial_unisolvent_delta 16 5
  obtain ⟨e, he, _hdet, hpos⟩ :=
    exists_degreeFiveSixteen_gaussianPositiveLogDetCurvature nodes c hdelta
  exact ⟨nodes, e, hnodes, he,
    degreeFiveCollisionPoint_injective degreeFiveBalancedAmplitude nodes hnodes he, hpos⟩

/-- A finite Euclidean exponential-inner-product Gram determinant can be locally log-convex. -/
theorem exists_finiteExponentialInnerGram_positiveLogDetCurvature :
    ∃ x : DegreeFiveIndex 16 → (Fin 16 ⊕ DegreeFiveTopIndex 16 → ℝ),
      Function.Injective x ∧
      0 < deriv (deriv (fun t => Real.log (finiteExponentialInnerGram x t).det)) 1 := by
  obtain ⟨nodes, e, _hnodes, _he, hx, hpos⟩ :=
    exists_distinct_degreeFiveSixteen_gaussianPositiveLogDetCurvature
  let x := degreeFiveCollisionPoint degreeFiveBalancedAmplitude nodes e
  refine ⟨x, hx, ?_⟩
  simpa [finiteExponentialInnerGram, degreeFiveGaussianBandwidthMatrix, x] using hpos

/-- Universal log-concavity fails for finite Gaussian distance matrices: there is a finite
injective Euclidean configuration whose literal `log det` has positive second derivative. -/
theorem exists_finiteGaussianDistanceGram_positiveLogDetCurvature :
    ∃ x : DegreeFiveIndex 16 → (Fin 16 ⊕ DegreeFiveTopIndex 16 → ℝ),
      Function.Injective x ∧
      (finiteGaussianDistanceGram x 1).det ≠ 0 ∧
      0 < deriv (deriv (fun t => Real.log (finiteGaussianDistanceGram x t).det)) 1 := by
  obtain ⟨nodes, c, hnodes, hdelta⟩ := exists_gradedMonomial_unisolvent_delta 16 5
  obtain ⟨e, he, hvalueDet, hpos⟩ :=
    exists_degreeFiveSixteen_gaussianPositiveLogDetCurvature nodes c hdelta
  let x := degreeFiveCollisionPoint degreeFiveBalancedAmplitude nodes e
  let y := fun i a => x i a / Real.sqrt 2
  have hx : Function.Injective x :=
    degreeFiveCollisionPoint_injective degreeFiveBalancedAmplitude nodes hnodes he
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hy : Function.Injective y := by
    intro i j hij
    apply hx
    funext a
    exact (div_left_inj' hsqrt).mp (congrFun hij a)
  have hinnerMatrix (t : ℝ) : finiteExponentialInnerGram x t =
      degreeFiveGaussianBandwidthMatrix degreeFiveBalancedAmplitude nodes e t := by
    rfl
  have hinnerOne : (finiteExponentialInnerGram x 1).det ≠ 0 := by
    rw [hinnerMatrix, degreeFiveGaussianBandwidthMatrix_one]
    exact hvalueDet
  have hdetAt := hasDerivAt_matrixDet (finiteExponentialInnerGram x)
    (fun i j => (∑ a, x i a * x j a) * finiteExponentialInnerGram x 1 i j)
    1 (hasDerivAt_finiteExponentialInnerGram x 1)
  have hdetNhds : ∀ᶠ t in nhds (1 : ℝ), (finiteExponentialInnerGram x t).det ≠ 0 :=
    (hdetAt.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hinnerOne
  have hinnerPos :
      0 < deriv (deriv (fun t => Real.log (finiteExponentialInnerGram x t).det)) 1 := by
    have hfun :
        (fun t => Real.log (finiteExponentialInnerGram x t).det) =
          fun t => Real.log
            (degreeFiveGaussianBandwidthMatrix degreeFiveBalancedAmplitude nodes e t).det := by
      funext t
      rw [hinnerMatrix]
    rw [hfun]
    exact hpos
  have hhalfPos :
      0 < deriv (deriv (fun t => Real.log (finiteHalfGaussianDistanceGram x t).det)) 1 := by
    rw [finiteHalfGaussianDistance_logDet_secondDerivative_eq x 1 hdetNhds]
    exact hinnerPos
  have hhalfDet : (finiteHalfGaussianDistanceGram x 1).det ≠ 0 := by
    rw [finiteHalfGaussianDistanceGram_det]
    exact mul_ne_zero (Real.exp_ne_zero _) hinnerOne
  have hmatrix (t : ℝ) : finiteGaussianDistanceGram y t =
      finiteHalfGaussianDistanceGram x t := by
    simpa [y] using finiteGaussianDistanceGram_div_sqrtTwo x t
  refine ⟨y, hy, ?_, ?_⟩
  · rw [hmatrix]
    exact hhalfDet
  have hfun :
      (fun t => Real.log (finiteGaussianDistanceGram y t).det) =
        fun t => Real.log (finiteHalfGaussianDistanceGram x t).det := by
    funext t
    rw [hmatrix]
  rw [hfun]
  exact hhalfPos


end

end GaloisForLFunctions.HilbertMetric
