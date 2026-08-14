import GaloisForLFunctions.HTGeometry.BoundedRelationExponentialSurvival
import GaloisForLFunctions.HTGeometry.FamilyKeySeparation

/-!
# A dilated family of one bounded-relation source defeats every algebraic jet relation

The single source `H` has algebraic exponential coefficients whose log-magnitudes admit no small
integer relation far out.  Its dilates `H(q_i X)` share those coefficients: a dilation contributes
only the scalar `q_i^{index}`, which lands in the *weight* of a split and not in its atom.  So the
whole expansion of a jet relation regroups by atom key exactly as for a single series, and the
square-free key produced by the slot-sequence separation is alone in its valuation class once its
parts are pushed beyond the confinement threshold.  The finite Lindemann–Weierstrass theorem then
forbids cancellation between the remaining valuation classes, so the relation fails at that degree.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The largest slot count of a monomial of a family jet polynomial. -/
def famMaxSlotCount {n : ℕ} (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) : ℕ :=
  Q.support.sup fun m => ∑ p : ι × Fin (n + 1), m (some p)

omit [DecidableEq ι] [Nonempty ι] in
theorem famAppearing_atom_count_le {n N : ℕ}
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (famSigmaIdx n N Q).image (famAtomKey n)) :
    ν.sum (fun _ k => k) ≤ famMaxSlotCount Q := by
  classical
  obtain ⟨x, hx, hxν⟩ := Finset.mem_image.mp hν
  rw [famSigmaIdx, Finset.mem_sigma] at hx
  have hmem : x.1 ∈ Q.support := (Finset.mem_filter.mp hx.1).1
  rw [← hxν, famAtomKey, key_total_count, famMaxSlotCount]
  exact Finset.le_sup (f := fun m : Option (ι × Fin (n + 1)) →₀ ℕ =>
    ∑ p : ι × Fin (n + 1), m (some p)) hmem

omit [DecidableEq ι] [Nonempty ι] in
theorem famWeight_isAlgebraic {n : ℕ} (q : ι → ℂ) (hqAlg : ∀ i, IsAlgebraic ℚ (q i))
    (m : Option (ι × Fin (n + 1)) →₀ ℕ)
    (l : Fin (∑ p : ι × Fin (n + 1), m (some p)) →₀ ℕ) :
    IsAlgebraic ℚ (famWeight q n m l) := by
  classical
  rw [← Subalgebra.mem_algebraicClosure, famWeight]
  refine Subalgebra.prod_mem _ fun t _ => ?_
  refine Subalgebra.mul_mem _ ?_ ?_
  · exact Subalgebra.natCast_mem _ _
  · refine Subalgebra.pow_mem _ ?_ _
    rw [Subalgebra.mem_algebraicClosure]
    exact hqAlg _

omit [DecidableEq ι] [Nonempty ι] in
theorem famAevalWeight_isAlgebraic {n N : ℕ} (q : ι → ℂ) (hqAlg : ∀ i, IsAlgebraic ℚ (q i))
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    (hQalg : ∀ m, IsAlgebraic ℚ (MvPolynomial.coeff m Q)) (ν : ℕ →₀ ℕ) :
    IsAlgebraic ℚ (famAevalWeight q n N Q ν) := by
  classical
  rw [← Subalgebra.mem_algebraicClosure, famAevalWeight]
  refine Subalgebra.sum_mem _ fun x _ => ?_
  refine Subalgebra.mul_mem _ ?_ ?_
  · rw [Subalgebra.mem_algebraicClosure]
    exact hQalg _
  · rw [Subalgebra.mem_algebraicClosure]
    exact famWeight_isAlgebraic q hqAlg _ _

/-- A key produced for a prescribed monomial of the support. -/
theorem exists_key_famAevalWeight_ne_zero_of_mem (q : ι → ℂ) (hq0 : ∀ i, q i ≠ 0)
    (hqinj : Function.Injective q) {n : ℕ} {K₀ : ℕ} (hK₀ : n ≤ K₀)
    (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    {m₀ : Option (ι × Fin (n + 1)) →₀ ℕ} (hm₀ : m₀ ∈ Q.support) :
    ∃ k : Fin (∑ p : ι × Fin (n + 1), m₀ (some p)) → ℕ,
      (∀ s, K₀ < k s) ∧ Function.Injective k
        ∧ famAevalWeight q n (keyTrunc n m₀ k) Q (key k) ≠ 0 := by
  classical
  have hcoeff : MvPolynomial.coeff m₀ Q ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀
  by_contra hcon
  refine hcoeff (coeff_eq_zero_of_famAevalWeight_key_vanishing q hq0 hqinj hK₀ Q m₀ ?_)
  intro k hkn hkinj
  by_contra hne
  exact hcon ⟨k, hkn, hkinj, hne⟩

/-- **A dilated family of one bounded-relation source defeats every algebraic jet relation.** -/
theorem exists_coeff_ne_zero_famJets_of_boundedRelation
    {b : ℕ → ℝ} {u : ℕ → ℂ} {H : PowerSeries ℂ} (q : ι → ℂ)
    (hH : ∀ i, PowerSeries.coeff i H = u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i)) (hconf : BoundedRelationConfinement b)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i)) (hu0 : ∀ i, u i ≠ 0)
    (hqAlg : ∀ i, IsAlgebraic ℚ (q i)) (hq0 : ∀ i, q i ≠ 0) (hqinj : Function.Injective q)
    {n : ℕ} (Q : MvPolynomial (Option (ι × Fin (n + 1))) ℂ)
    (hQalg : ∀ m, IsAlgebraic ℚ (MvPolynomial.coeff m Q)) (hQ : Q ≠ 0) :
    ∃ N, PowerSeries.coeff N
      (MvPolynomial.aeval (familyJets n (fun i => rescale (q i) H)) Q) ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := hconf (famMaxSlotCount Q)
  have hsupport : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQ
  obtain ⟨m₀, hm₀, hsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupport
      (fun m => ∑ p : ι × Fin (n + 1), m (some p))
  have hcount₀ : (∑ p : ι × Fin (n + 1), m₀ (some p)) = famMaxSlotCount Q := by
    rw [famMaxSlotCount]
    exact hsup.symm
  obtain ⟨k, hkn, hkinj, hw⟩ :=
    exists_key_famAevalWeight_ne_zero_of_mem q hq0 hqinj (le_max_left n M) Q hm₀
  set N : ℕ := keyTrunc n m₀ k with hN
  set A : Finset (ℕ →₀ ℕ) := (famSigmaIdx n N Q).image (famAtomKey n) with hA
  have hstarMem : key k ∈ A := by
    by_contra hno
    refine hw ?_
    rw [famAevalWeight]
    refine Finset.sum_eq_zero fun x hx => ?_
    obtain ⟨hxmem, hxkey⟩ := Finset.mem_filter.mp hx
    exact absurd (hA ▸ Finset.mem_image_of_mem (famAtomKey n) hxmem) (hxkey ▸ hno)
  have hstarCount : (key k).sum (fun _ v => v) = famMaxSlotCount Q := by
    rw [key_total_count, hcount₀]
  have hstarTail : ∀ i, (key k) i ≠ 0 → M ≤ i := by
    intro i hi
    have hex : ∃ s, k s = i := by
      by_contra hno
      refine hi ?_
      rw [key_apply]
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun s hs => ?_)
      exact hno ⟨s, (Finset.mem_filter.mp hs).2⟩
    obtain ⟨s, rfl⟩ := hex
    have := hkn s
    have hle : M ≤ max n M := le_max_right n M
    omega
  have hstarUnique : ∀ μ ∈ A,
      boundedAtomValuation b μ = boundedAtomValuation b (key k) → μ = key k := by
    intro μ hμ hval
    exact atom_eq_of_valuation_eq_of_full_tail hM hstarCount
      (famAppearing_atom_count_le Q hμ) hstarTail hval
  refine ⟨N, ?_⟩
  intro hcoeff
  have hsumzero : ∑ ν ∈ A,
      ν.prod (fun i j => (PowerSeries.coeff i H) ^ j) * famAevalWeight q n N Q ν = 0 := by
    rw [← coeff_aeval_famJets_regrouped n N q H Q]
    exact hcoeff
  have hgroupzero :
      ∑ v ∈ A.image (boundedAtomValuation b),
          (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
            atomPhase u ν * famAevalWeight q n N Q ν) *
              Complex.exp (-((v : ℝ) : ℂ)) = 0 := by
    rw [← sum_atom_products_regrouped_by_valuation hH A (famAevalWeight q n N Q)]
    exact hsumzero
  set V : Finset ℝ := A.image (boundedAtomValuation b) with hV
  set I : Type _ := {v : ℝ // v ∈ V} with hI
  set E : I → ℂ := fun v => -((v.1 : ℝ) : ℂ) with hE
  set C : I → ℂ := fun v =>
    ∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v.1),
      atomPhase u ν * famAevalWeight q n N Q ν with hC
  have hEalg : ∀ v, IsAlgebraic ℚ (E v) := by
    intro v
    obtain ⟨ν, hν, hval⟩ := Finset.mem_image.mp v.2
    rw [hE]
    simpa [hval] using (boundedAtomValuation_coe_isAlgebraic hbAlg ν).neg
  have hEinj : Function.Injective E := by
    intro v w hvw
    refine Subtype.ext ?_
    rw [hE] at hvw
    exact Complex.ofReal_injective (neg_injective hvw)
  have hCAlg : ∀ v, IsAlgebraic ℚ (C v) := by
    intro v
    rw [hC, ← Subalgebra.mem_algebraicClosure]
    refine Subalgebra.sum_mem _ fun ν _ => ?_
    rw [Subalgebra.mem_algebraicClosure]
    exact (atomPhase_isAlgebraic huAlg ν).mul
      (famAevalWeight_isAlgebraic q hqAlg Q hQalg ν)
  have hrel : ∑ v : I, C v * Complex.exp (E v) = 0 := by
    show (∑ v ∈ V.attach, C v * Complex.exp (E v)) = 0
    rw [hC, hE]
    rw [Finset.sum_attach V (fun v : ℝ =>
      (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
        atomPhase u ν * famAevalWeight q n N Q ν) * Complex.exp (-((v : ℝ) : ℂ)))]
    exact hgroupzero
  have hallzero := GaloisForLFunctions.RHTower.exp_algebraic_relation_eq_zero
    E C hEalg hEinj hCAlg hrel
  have hvstar : boundedAtomValuation b (key k) ∈ V :=
    Finset.mem_image.mpr ⟨key k, hstarMem, rfl⟩
  have hfiber :
      A.filter (fun μ => boundedAtomValuation b μ = boundedAtomValuation b (key k)) = {key k} := by
    ext μ
    rw [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun hh => hstarUnique μ hh.1 hh.2, fun hh => by rw [hh]; exact ⟨hstarMem, rfl⟩⟩
  have hCstar : C ⟨boundedAtomValuation b (key k), hvstar⟩ ≠ 0 := by
    rw [hC]
    simp only
    rw [hfiber, Finset.sum_singleton]
    exact mul_ne_zero (atomPhase_ne_zero hu0 (key k)) hw
  exact hCstar (hallzero _)

end

end GaloisForLFunctions
