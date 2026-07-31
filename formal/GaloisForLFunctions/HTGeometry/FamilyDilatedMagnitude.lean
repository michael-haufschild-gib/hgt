import GaloisForLFunctions.HTGeometry.FamilyJetFlattening
import GaloisForLFunctions.HTGeometry.MagnitudeInhomogeneousSurvival

/-!
# Magnitude survival for a family of dilated sources

A differential relation among the dilates `H(q_i X)` of one source expands, at each degree, into a
sum over flattened jet splits.  Each split consumes a multiset of Taylor coefficients of `H` — its
*atom key* — and contributes a weight built from the Leibniz falling factorials and the dilation
powers `q_i^{order}`.  Because every dilate has the same underlying coefficient sequence, the
valuation of a split depends only on its atom key, so the magnitude domination criterion applies
verbatim with the profile of `H`; the whole dependence on which member of the family each slot came
from is carried by the weight.

* `famSlot`, `famOrder`, `famWeight` — the data of one flattened split;
* `coeff_aeval_famJets_sigma_sum` — the full expansion;
* `famAevalWeight`, `coeff_aeval_famJets_regrouped` — the expansion regrouped by atom key;
* `famAeval_coeff_ne_zero_of_dominant` — a dominant atom key with nonzero weight defeats the
  relation.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-! ### Generic support expansion of an evaluation -/

theorem aeval_as_support_sum {σ : Type*} (g : σ → ℂ⟦X⟧) (Q : MvPolynomial σ ℂ) :
    aeval g Q = ∑ m ∈ Q.support, MvPolynomial.coeff m Q • aeval g (monomial m (1 : ℂ)) := by
  classical
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff Q]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← map_smul (aeval g) (MvPolynomial.coeff m Q) (monomial m (1 : ℂ))]
  congr 1
  rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

theorem coeff_aeval_eq_support_sum_general {σ : Type*} (N : ℕ) (g : σ → ℂ⟦X⟧)
    (Q : MvPolynomial σ ℂ) :
    (coeff N) (aeval g Q)
      = ∑ m ∈ Q.support,
          MvPolynomial.coeff m Q * (coeff N) (aeval g (monomial m (1 : ℂ))) := by
  classical
  rw [aeval_as_support_sum, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_smul, smul_eq_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The data of one flattened split -/

/-- The jet variable attached to slot `t` when the jet-exponent profile of `m` is flattened. -/
noncomputable def famSlot (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ) :
    Fin (∑ p : ι × Fin (n + 1), m (some p)) → ι × Fin (n + 1) :=
  flatIndex (fun p => m (some p))

omit [DecidableEq ι] in
theorem famSlot_def (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ) :
    famSlot n m = flatIndex (fun p => m (some p)) := rfl

/-- The index of the source coefficient consumed at slot `t` of a split. -/
def famOrder (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ)
    (t : Fin (∑ p : ι × Fin (n + 1), m (some p))) : ℕ :=
  l t + ((famSlot n m t).2 : ℕ)

/-- The Leibniz-and-dilation weight of one flattened split. -/
noncomputable def famWeight (q : ι → ℂ) (n : ℕ) (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ) : ℂ :=
  ∏ t, (((famOrder n m l t).descFactorial ((famSlot n m t).2 : ℕ) : ℂ)
      * (q (famSlot n m t).1) ^ (famOrder n m l t))

omit [DecidableEq ι] in
/-- Every split weight is a product of nonzero factors when the dilations are nonzero. -/
theorem famWeight_ne_zero {q : ι → ℂ} (hq : ∀ i, q i ≠ 0) (n : ℕ)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ) : famWeight q n m l ≠ 0 := by
  rw [famWeight]
  refine Finset.prod_ne_zero_iff.mpr fun t _ => mul_ne_zero ?_ (pow_ne_zero _ (hq _))
  have hpos : 0 < (famOrder n m l t).descFactorial ((famSlot n m t).2 : ℕ) := by
    refine Nat.descFactorial_pos.mpr ?_
    rw [famOrder]
    omega
  exact_mod_cast hpos.ne'

/-! ### The expansion -/

omit [DecidableEq ι] in
/-- The `N`-th coefficient of one jet monomial of the dilated family. -/
theorem coeff_aeval_famJets_monomial_expand (n N : ℕ) (q : ι → ℂ) (H : ℂ⟦X⟧)
    (m : Option (ι × Fin (n + 1)) →₀ ℕ) :
    (coeff N) (aeval (familyJets n (fun i => rescale (q i) H)) (monomial m (1 : ℂ)))
      = if m none ≤ N then
          ∑ l ∈ (Finset.univ :
              Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag (N - m none),
            (∏ t, (coeff (famOrder n m l t)) H) * famWeight q n m l
        else 0 := by
  classical
  rw [coeff_aeval_familyJets_monomial_shift]
  split_ifs with h
  · rw [prod_pow_eq_flatIndex
      (fun p : ι × Fin (n + 1) => (⇑(d⁄dX ℂ))^[(p.2 : ℕ)] (rescale (q p.1) H))
      (fun p : ι × Fin (n + 1) => m (some p)), ← famSlot_def,
      coeff_prod_iterate_deriv_family (fun t => rescale (q (famSlot n m t).1) H)
        (fun t => ((famSlot n m t).2 : ℕ))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [famWeight, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [PowerSeries.coeff_rescale]
    show _ = (coeff (famOrder n m l t)) H
      * (((famOrder n m l t).descFactorial ((famSlot n m t).2 : ℕ) : ℂ)
        * (q (famSlot n m t).1) ^ (famOrder n m l t))
    rw [famOrder]
    ring
  · rfl

/-- The dependent-arity index of contributing `(monomial, split)` pairs. -/
noncomputable def famSigmaIdx (n N : ℕ) (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    Finset (Σ m : Option (ι × Fin (n + 1)) →₀ ℕ,
      Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ) := by
  classical
  exact (Q.support.filter (fun m => m none ≤ N)).sigma
    (fun m => (Finset.univ :
      Finset (Fin (∑ p : ι × Fin (n + 1), m (some p)))).finsuppAntidiag (N - m none))

/-- Order-blind atom key of a split: the multiset of source-coefficient indices it consumes. -/
noncomputable def famAtomKey (n : ℕ)
    (x : Σ m : Option (ι × Fin (n + 1)) →₀ ℕ,
      Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ) : ℕ →₀ ℕ :=
  key (famOrder n x.1 x.2)

omit [DecidableEq ι] in
/-- **The full expansion.** -/
theorem coeff_aeval_famJets_sigma_sum (n N : ℕ) (q : ι → ℂ) (H : ℂ⟦X⟧)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    (coeff N) (aeval (familyJets n (fun i => rescale (q i) H)) Q)
      = ∑ x ∈ famSigmaIdx n N Q,
          MvPolynomial.coeff x.1 Q
            * ((∏ t, (coeff (famOrder n x.1 x.2 t)) H) * famWeight q n x.1 x.2) := by
  classical
  rw [coeff_aeval_eq_support_sum_general]
  rw [Finset.sum_congr rfl (fun m (_ : m ∈ Q.support) => by
    rw [coeff_aeval_famJets_monomial_expand n N q H m])]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [famSigmaIdx, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]

/-- Weight of an atom key: the total coefficient-weighted contribution of the splits realizing it. -/
noncomputable def famAevalWeight (q : ι → ℂ) (n N : ℕ)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) (ν : ℕ →₀ ℕ) : ℂ := by
  classical
  exact ∑ x ∈ (famSigmaIdx n N Q).filter (fun x => famAtomKey n x = ν),
    MvPolynomial.coeff x.1 Q * famWeight q n x.1 x.2

omit [DecidableEq ι] in
/-- **The expansion regrouped by atom key.** -/
theorem coeff_aeval_famJets_regrouped (n N : ℕ) (q : ι → ℂ) (H : ℂ⟦X⟧)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) :
    (coeff N) (aeval (familyJets n (fun i => rescale (q i) H)) Q)
      = ∑ ν ∈ (famSigmaIdx n N Q).image (famAtomKey n),
          (ν.prod (fun i j => (coeff i H) ^ j)) * famAevalWeight q n N Q ν := by
  classical
  have hpair : (coeff N) (aeval (familyJets n (fun i => rescale (q i) H)) Q)
      = ∑ x ∈ famSigmaIdx n N Q,
          MvPolynomial.coeff x.1 Q
            * ((famAtomKey n x).prod (fun i j => (coeff i H) ^ j)) * famWeight q n x.1 x.2 := by
    rw [coeff_aeval_famJets_sigma_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [famAtomKey, prod_eq_key_prod (famOrder n x.1 x.2) (fun i => coeff i H)]
    ring
  rw [hpair, ← Finset.sum_fiberwise_of_maps_to
    (g := famAtomKey n) (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [famAevalWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨_, hkey⟩ := Finset.mem_filter.mp hx
  rw [hkey]
  ring

omit [DecidableEq ι] in
/-- **Family magnitude survival.**  If one atom key has nonzero weight and strictly minimal
valuation with a large enough gap, the relation fails at that degree. -/
theorem famAeval_coeff_ne_zero_of_dominant (n N : ℕ) (q : ι → ℂ) (H : ℂ⟦X⟧)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    {b : ℕ → ℝ} (hb : ∀ i, ‖coeff i H‖ = Real.exp (- b i))
    (ν₀ : ℕ →₀ ℕ) (hν₀ : ν₀ ∈ (famSigmaIdx n N Q).image (famAtomKey n))
    (hw₀ : famAevalWeight q n N Q ν₀ ≠ 0) {G : ℝ}
    (hgap : ∀ ν ∈ ((famSigmaIdx n N Q).image (famAtomKey n)).erase ν₀,
        ν₀.sum (fun i k => (k : ℝ) * b i) + G ≤ ν.sum (fun i k => (k : ℝ) * b i))
    (hG : (∑ ν ∈ (famSigmaIdx n N Q).image (famAtomKey n), ‖famAevalWeight q n N Q ν‖)
        < ‖famAevalWeight q n N Q ν₀‖ * Real.exp G) :
    (coeff N) (aeval (familyJets n (fun i => rescale (q i) H)) Q) ≠ 0 := by
  classical
  rw [coeff_aeval_famJets_regrouped]
  rw [Finset.sum_congr rfl fun ν (_ : ν ∈ (famSigmaIdx n N Q).image (famAtomKey n)) =>
      mul_comm (ν.prod (fun i j => (coeff i H) ^ j)) (famAevalWeight q n N Q ν)]
  exact weighted_sum_ne_zero_of_min_valuation_complex _
    (fun ν => ν.sum (fun i k => (k : ℝ) * b i)) _
    (fun ν => norm_aval (f := H) hb ν) _ hν₀ hw₀ hgap hG

end

end GaloisForLFunctions
