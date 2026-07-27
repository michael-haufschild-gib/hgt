import GaloisForLFunctions.HTGeometry.BalancedDiagonalNonvanishing
import GaloisForLFunctions.HTGeometry.FiberPermanentIdentity
import GaloisForLFunctions.HTGeometry.MagnitudeAtomGrading

/-!
# Balanced grouped weights for inhomogeneous differential polynomials

This module isolates the monomials whose jet degree and shifted differential order
can contribute to a prescribed injective source tuple. Their grouped Leibniz weight
is exactly the evaluation of a finite permanent-symbol polynomial. Combined with an
injective balanced diagonal, this supplies a nonzero balanced atom without any
leading-diagonal nondegeneracy assumption.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-- A family of naturals indexed by a nonempty `Fin D`, each entry at least `q`, sums to at
least `q`: one summand already reaches it. -/
theorem le_sum_of_le_apply {D q : ℕ} (hD : 0 < D) {s : Fin D → ℕ} (h : ∀ i, q ≤ s i) :
    q ≤ ∑ i, s i := by
  obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  exact (h i₀).trans
    (Finset.single_le_sum (f := s) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀))

/-- The same family sums to at least `D` copies of `q`, summand by summand. -/
theorem mul_le_sum_of_le_apply {D q : ℕ} {s : Fin D → ℕ} (h : ∀ i, q ≤ s i) :
    D * q ≤ ∑ i, s i := by
  calc
    D * q = ∑ _i : Fin D, q := by simp [Finset.sum_const]
    _ ≤ ∑ i, s i := Finset.sum_le_sum fun i _ => h i

/-- Dually, a family bounded above by `q` sums to at most `D` copies of `q`. -/
theorem sum_le_mul_of_apply_le {D q : ℕ} {s : Fin D → ℕ} (h : ∀ i, s i ≤ q) :
    ∑ i, s i ≤ D * q := by
  calc
    ∑ i, s i ≤ ∑ _i : Fin D, q := Finset.sum_le_sum fun i _ => h i
    _ = D * q := by simp [Finset.sum_const]

def jetMonomialDegree (n : ℕ) (m : Fin (n + 2) →₀ ℕ) : ℕ :=
  ∑ j : Fin (n + 1), m j.succ

def jetMonomialOrder (n : ℕ) (m : Fin (n + 2) →₀ ℕ) : ℕ :=
  ∑ j : Fin (n + 1), (j : ℕ) * m j.succ

def balancedJetGroup (n N D : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (s : Fin D → ℕ) : Finset (Fin (n + 2) →₀ ℕ) :=
  Q.support.filter fun m =>
    m 0 ≤ N ∧ jetMonomialDegree n m = D ∧
      N - m 0 + jetMonomialOrder n m = ∑ i, s i

theorem balancedJetGroup_degree {n N D : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {s : Fin D → ℕ} (m : ↥(balancedJetGroup n N D Q s)) :
    jetMonomialDegree n m.1 = D :=
  ((Finset.mem_filter.mp m.2).2).2.1

noncomputable def balancedJetCast {n N D : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {s : Fin D → ℕ} (m : ↥(balancedJetGroup n N D Q s)) :
    Fin (jetMonomialDegree n m.1) ≃ Fin D :=
  Equiv.cast (congrArg Fin (balancedJetGroup_degree m))

noncomputable def balancedJetSymbol (n N D : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (s : Fin D → ℕ) :
    MvPolynomial (Fin D) ℂ :=
  ∑ m ∈ (balancedJetGroup n N D Q s).attach,
    MvPolynomial.C (MvPolynomial.coeff m.1 Q) *
      MvPolynomial.rename (balancedJetCast m)
        ((permSymbolPoly (flatOrder (fun j => m.1 j.succ))).map (Int.castRingHom ℂ))

theorem aevalWeight_key_eq_balancedJetSymbol (n N D : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (s : Fin D → ℕ)
    (hs : Function.Injective s)
    (hdom : ∀ m : ↥(balancedJetGroup n N D Q s),
      ∀ i : Fin D, ∀ t : Fin (jetMonomialDegree n m.1),
        flatOrder (fun j => m.1 j.succ) t ≤ s i) :
    aevalWeight n N Q (key s) =
      MvPolynomial.eval (fun i => (s i : ℂ)) (balancedJetSymbol n N D Q s) := by
  classical
  have hfiber :
      (sigmaIdx n N Q).filter (fun x => atomKeyOf n x = key s) =
        (balancedJetGroup n N D Q s).sigma (fun m =>
          ((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
            (N - m 0)).filter
              (fun l => key (fun t => l t + flatOrder (fun j => m j.succ) t) = key s)) := by
    ext x
    rw [Finset.mem_filter, sigmaIdx, Finset.mem_sigma]
    rw [Finset.mem_sigma, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm, hl⟩, hkey⟩
      have hmQ : x.1 ∈ Q.support := hm.1
      have hmN : x.1 0 ≤ N := hm.2
      have hdeg : jetMonomialDegree n x.1 = D := by
        rw [jetMonomialDegree, ← atomKeyOf_count n x, hkey, key_total_count]
      have hord : N - x.1 0 + jetMonomialOrder n x.1 = ∑ i, s i := by
        rw [jetMonomialOrder, ← flatOrder_sum (fun j => x.1 j.succ),
          ← (Finset.mem_finsuppAntidiag.mp hl).1,
          ← Finset.sum_add_distrib, ← key_weighted_sum s, ← hkey, atomKeyOf,
          key_weighted_sum]
      exact ⟨Finset.mem_filter.mpr ⟨hmQ, hmN, hdeg, hord⟩,
        Finset.mem_filter.mpr ⟨hl, hkey⟩⟩
    · rintro ⟨hm, hl⟩
      obtain ⟨hmQ, hmN, _hdeg, _hord⟩ := Finset.mem_filter.mp hm
      obtain ⟨hlanti, hkey⟩ := Finset.mem_filter.mp hl
      exact ⟨⟨⟨hmQ, hmN⟩, hlanti⟩, hkey⟩
  rw [aevalWeight, hfiber]
  rw [show (∑ x ∈ (balancedJetGroup n N D Q s).sigma (fun m =>
          ((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
            (N - m 0)).filter
              (fun l => key (fun t => l t + flatOrder (fun j => m j.succ) t) = key s)),
        MvPolynomial.coeff x.1 Q * atomDescProd n x) =
      ∑ m ∈ balancedJetGroup n N D Q s,
        ∑ l ∈ ((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
            (N - m 0)).filter
              (fun l => key (fun t => l t + flatOrder (fun j => m j.succ) t) = key s),
          MvPolynomial.coeff m Q * atomDescProd n ⟨m, l⟩ by
        simpa only [jetMonomialDegree] using
          (Finset.sum_sigma (balancedJetGroup n N D Q s)
            (fun m => ((Finset.univ : Finset (Fin (∑ j : Fin (n + 1), m j.succ))).finsuppAntidiag
              (N - m 0)).filter
                (fun l => key (fun t => l t + flatOrder (fun j => m j.succ) t) = key s))
            (fun x => MvPolynomial.coeff x.1 Q * atomDescProd n x))]
  rw [balancedJetSymbol, map_sum]
  rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun m hm => ?_
  let e : Fin (jetMonomialDegree n m.1) ≃ Fin D := balancedJetCast m
  let μ : Fin (jetMonomialDegree n m.1) → ℕ := flatOrder (fun j => m.1 j.succ)
  let sm : Fin (jetMonomialDegree n m.1) → ℕ := fun i => s (e i)
  have hsm : Function.Injective sm := hs.comp e.injective
  have hsmμ : ∀ i t, μ t ≤ sm i := by
    intro i t
    exact hdom m (e i) t
  have hsmsum : ∑ i, sm i = ∑ i, s i := Equiv.sum_comp e s
  have hμsum : ∑ i, μ i = jetMonomialOrder n m.1 := by
    exact flatOrder_sum (fun j => m.1 j.succ)
  have hlevel : ∑ t, (sm t - μ t) = N - m.1 0 := by
    have hsubadd : (∑ t, (sm t - μ t)) + ∑ t, μ t = ∑ t, sm t := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => Nat.sub_add_cancel (hsmμ t t)
    have hgroup := ((Finset.mem_filter.mp m.2).2).2.2
    rw [hsmsum, hμsum] at hsubadd
    omega
  have hkeysm : key sm = key s := by
    rw [key, key]
    exact Equiv.sum_comp e (fun i => Finsupp.single (s i) 1)
  have hperm := fiber_perm_single sm hsm μ hsmμ
  have hpermC := congrArg (fun z : ℤ => (z : ℂ)) hperm
  push_cast at hpermC
  have hinner :
      ∑ l ∈ ((Finset.univ : Finset (Fin (jetMonomialDegree n m.1))).finsuppAntidiag
          (N - m.1 0)).filter
            (fun l => key (fun t => l t + flatOrder (fun j => m.1 j.succ) t) = key s),
        atomDescProd n ⟨m.1, l⟩ =
      MvPolynomial.eval (fun i => (s i : ℂ))
        (MvPolynomial.rename e
          ((permSymbolPoly (flatOrder (fun j => m.1 j.succ))).map (Int.castRingHom ℂ))) := by
    rw [MvPolynomial.eval_rename]
    change _ = MvPolynomial.eval (fun i => (sm i : ℂ))
      ((permSymbolPoly μ).map (Int.castRingHom ℂ))
    rw [eval_map_permSymbolPoly_complex]
    rw [← hpermC, hlevel, hkeysm]
    rfl
  rw [map_mul, MvPolynomial.eval_C]
  rw [← hinner]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rfl

end

end GaloisForLFunctions

