import GaloisForLFunctions.ArithmeticPositiveDuality.PhaseHullParity
import GaloisForLFunctions.ArithmeticPositiveDuality.PositivePhaseCombinations
import GaloisForLFunctions.ArithmeticPositiveDuality.OddOrdinateRelationsForceFrequencyCost

/-!
# Parity classifies exact annihilation with near-unit mass

A finite nonempty ordinate family admits normalized positive two-prime
annihilators of arbitrarily near-unit mass exactly when every integer relation
has even coefficient sum. Under this condition every mass strictly above one
is attained. Conversely, the phase-energy identity forces monomials arbitrarily
close to the simultaneous antipodal phase as annihilator mass tends to one.
-/

noncomputable section
set_option autoImplicit false
open Set Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

variable {ι : Type*} [Fintype ι]

/-- Parity permits exact annihilation at every prescribed mass above one. -/
theorem exists_exact_mass_annihilator_of_even_relations (γ : ι → ℝ)
    (hγ : EvenOrdinateRelations γ) (β H : ℝ) (hH : 1 < H) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β = H := by
  classical
  have hH0 : 0 < H := lt_trans zero_lt_one hH
  let r : ℝ := 1 / H
  have hr0 : 0 < r := one_div_pos.mpr hH0
  have hr1 : r < 1 := (div_lt_one hH0).mpr hH
  obtain ⟨κ, hκ, z, a, hz, _, ha, hsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull
      (neg_smul_one_mem_phaseConvexHull γ hγ hr0.le hr1)
  have hex : ∀ k, ∃ d : Fin 2 →₀ ℕ, d ≠ 0 ∧
      (fun i => monomialPhase (γ i) d) = z k := fun k => hz ⟨k, rfl⟩
  choose d hd he using hex
  let w : κ → ℝ≥0 := fun k => ⟨a k / r, div_nonneg (ha k).le hr0.le⟩
  have hw : ∑ k, (w k : ℝ) = H := by
    change (∑ k, a k / r) = H
    rw [← Finset.sum_div, hsum]
    simp only [r, one_div, inv_inv]
  have hphase (i : ι) : ∑ k, ((w k : ℝ) : ℂ) * monomialPhase (γ i) (d k) = -1 := by
    change (∑ k, ((a k / r : ℝ) : ℂ) * monomialPhase (γ i) (d k)) = -1
    have hc := congrFun hcomb i
    simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul] at hc
    have hz' (k : κ) : z k i = monomialPhase (γ i) (d k) := (congrFun (he k) i).symm
    simp_rw [hz'] at hc
    calc
      _ = (∑ k, (a k : ℂ) * monomialPhase (γ i) (d k)) / (r : ℂ) := by
        simp only [Complex.ofReal_div, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = -(r : ℂ) / (r : ℂ) := by rw [hc]
      _ = -1 := by rw [neg_div, div_self (Complex.ofReal_ne_zero.mpr hr0.ne')]
  obtain ⟨P, hc, heval, hmass⟩ := exists_annihilator_of_phase_combination β γ d w hd hphase
  exact ⟨P, hc, heval, hmass.trans hw⟩

private theorem exists_near_antipodal_monomial {P : MvPolynomial (Fin 2) ℝ≥0}
    (hc : MvPolynomial.constantCoeff P = 1) (β : ℝ) (γ : ι → ℝ)
    (heval : ∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0)
    (hm : 1 ≤ dirichletTailMass P β) {ε : ℝ} (hε : 0 < ε)
    (hsmall : 2 * (Fintype.card ι : ℝ) * (dirichletTailMass P β - 1) < ε ^ 2) :
    ∃ d : Fin 2 →₀ ℕ, d ≠ 0 ∧ ∀ i, ‖monomialPhase (γ i) d + 1‖ < ε := by
  classical
  by_contra! h
  have hlower (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      ε ^ 2 ≤ ∑ i, ‖monomialPhase (γ i) d + 1‖ ^ 2 := by
    obtain ⟨i, hi⟩ := h d (Finset.mem_erase.mp hd).1
    have hs : ε ^ 2 ≤ ‖monomialPhase (γ i) d + 1‖ ^ 2 := by
      simpa only [pow_two] using mul_le_mul hi hi hε.le (norm_nonneg _)
    exact hs.trans (Finset.single_le_sum
      (f := fun j : ι => ‖monomialPhase (γ j) d + 1‖ ^ 2)
      (fun j _ => sq_nonneg ‖monomialPhase (γ j) d + 1‖) (Finset.mem_univ i))
  have henergy : (∑ i, ∑ d ∈ P.support.erase 0,
      ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
        ‖monomialPhase (γ i) d + 1‖ ^ 2) =
      2 * (Fintype.card ι : ℝ) * (dirichletTailMass P β - 1) := by
    simp_rw [ordinate_phase_energy hc, heval, Complex.zero_re, add_zero]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hbound : ε ^ 2 * dirichletTailMass P β ≤
      ∑ i, ∑ d ∈ P.support.erase 0,
        ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) *
          ‖monomialPhase (γ i) d + 1‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ d ∈ P.support.erase 0,
          (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)) * ε ^ 2 := by
        rw [dirichletTailMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ ≤ ∑ d ∈ P.support.erase 0,
          (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)) *
            (∑ i, ‖monomialPhase (γ i) d + 1‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left (hlower d hd)
          (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le)
      _ = _ := by simp only [Finset.mul_sum]
  rw [henergy] at hbound
  have hunit := mul_le_mul_of_nonneg_left hm (sq_nonneg ε)
  nlinarith only [hsmall, hbound, hunit]

/-- Near-unit exact cancellation forces the antipodal point into the actual
nonconstant monomial phase closure. -/
theorem neg_one_mem_phaseHull_of_near_unit [Nonempty ι] (β : ℝ) (γ : ι → ℝ)
    (hnear : ∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β < 1 + δ) :
    (fun _ : ι => (-1 : ℂ)) ∈ closure (monomialPhaseSet γ) := by
  classical
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hden : 0 < 2 * (Fintype.card ι : ℝ) := mul_pos (by norm_num) hN
  obtain ⟨P, hc, he, hm⟩ := hnear (ε ^ 2 / (2 * (Fintype.card ι : ℝ)))
    (div_pos (pow_pos hε 2) hden)
  have hone : 1 ≤ dirichletTailMass P β := by
    have h := one_le_dirichletTailMass_of_zero hc (he (Classical.choice ‹Nonempty ι›))
    simpa [harmonicPacketPoint] using h
  have hsmall : 2 * (Fintype.card ι : ℝ) * (dirichletTailMass P β - 1) < ε ^ 2 := by
    have hs : dirichletTailMass P β - 1 < ε ^ 2 / (2 * (Fintype.card ι : ℝ)) := by
      linarith only [hm]
    have ht := (lt_div_iff₀ hden).mp hs
    nlinarith only [ht]
  obtain ⟨d, hd, hphase⟩ := exists_near_antipodal_monomial hc β γ he hone hε hsmall
  refine ⟨fun i => monomialPhase (γ i) d, ⟨d, hd, rfl⟩, (dist_pi_lt_iff hε).mpr ?_⟩
  intro i
  rw [dist_comm, dist_eq_norm, sub_neg_eq_add]
  exact hphase i

/-- Complete parity classification of near-unit exact positive annihilation
for a fixed nonempty finite family of ordinates. -/
theorem near_unit_annihilation_iff_even_relations [Nonempty ι] (β : ℝ) (γ : ι → ℝ) :
    (∀ δ : ℝ, 0 < δ → ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β < 1 + δ) ↔ EvenOrdinateRelations γ := by
  constructor
  · intro hnear
    exact (neg_one_mem_phaseHull_iff γ).mp (neg_one_mem_phaseHull_of_near_unit β γ hnear)
  · intro hγ δ hδ
    obtain ⟨P, hc, he, hm⟩ := exists_exact_mass_annihilator_of_even_relations γ hγ β
      (1 + δ / 2) (by linarith only [hδ])
    refine ⟨P, hc, he, ?_⟩
    rw [hm]
    linarith only [hδ]

#print axioms exists_exact_mass_annihilator_of_even_relations
#print axioms near_unit_annihilation_iff_even_relations

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
