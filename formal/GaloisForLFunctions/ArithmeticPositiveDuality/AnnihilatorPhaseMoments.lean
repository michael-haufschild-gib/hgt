import GaloisForLFunctions.ArithmeticPositiveDuality.PhaseHullParity
import GaloisForLFunctions.ArithmeticPositiveDuality.PositivePhaseCombinations

/-!
# Exact annihilator mass as a finite phase moment

Exponential rescaling removes the common real abscissa from the moment problem.
A prescribed positive tail mass is attainable exactly when the corresponding
antipodal vector belongs to the convex hull of actual nonconstant monomial
phases. No closure or approximate cancellation occurs in this equivalence.
-/

noncomputable section
set_option autoImplicit false
open Set Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- On a vertical line, positive monomial mass multiplies its unit phase. -/
theorem dirichletEval_ordinate_eq_phase_sum {P : MvPolynomial (Fin 2) ℝ≥0}
    (hc : MvPolynomial.constantCoeff P = 1) (β γ : ℝ) :
    dirichletEval (harmonicPacketPoint β γ 1) P = 1 +
      ∑ d ∈ P.support.erase 0,
        ((((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β) : ℝ) : ℂ) *
          monomialPhase γ d := by
  rw [dirichletEval_eq_one_add_tail hc]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [monomialPhase, harmonicPacketPoint, Nat.cast_one, one_mul,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

variable {ι : Type*}

/-- Exact simultaneous annihilation is a positive vector moment with value minus one. -/
theorem annihilator_phase_sum {P : MvPolynomial (Fin 2) ℝ≥0}
    (hc : MvPolynomial.constantCoeff P = 1) (β : ℝ) (γ : ι → ℝ)
    (he : ∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) :
    (∑ d ∈ P.support.erase 0,
      (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)) •
        (fun i => monomialPhase (γ i) d)) = (fun _ : ι => (-1 : ℂ)) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul]
  have h := dirichletEval_ordinate_eq_phase_sum hc β (γ i)
  rw [he i] at h
  linear_combination -h

/-- Normalizing the tail mass of an exact annihilator gives an actual finite
convex combination of nonconstant monomial phases. -/
theorem phase_point_mem_convexHull_of_annihilator {P : MvPolynomial (Fin 2) ℝ≥0}
    (hc : MvPolynomial.constantCoeff P = 1) (β : ℝ) (γ : ι → ℝ)
    (he : ∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0)
    {H : ℝ} (hH : 0 < H) (hmass : dirichletTailMass P β = H) :
    (fun _ : ι => -((1 / H : ℝ) : ℂ)) ∈ convexHull ℝ (monomialPhaseSet γ) := by
  classical
  let S := P.support.erase 0
  let w : (Fin 2 →₀ ℕ) → ℝ := fun d =>
    ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * β)
  have hw (d : Fin 2 →₀ ℕ) : 0 ≤ w d :=
    mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos _).le
  have hsum : ∑ d ∈ S, w d = H := hmass
  have hraw : (∑ d ∈ S, w d • (fun i => monomialPhase (γ i) d)) =
      (fun _ : ι => (-1 : ℂ)) := annihilator_phase_sum hc β γ he
  have hm : (∑ d ∈ S, (w d / H) • (fun i => monomialPhase (γ i) d)) ∈
      convexHull ℝ (monomialPhaseSet γ) := by
    apply (convex_convexHull ℝ (monomialPhaseSet γ)).sum_mem
    · intro d _
      exact div_nonneg (hw d) hH.le
    · rw [← Finset.sum_div, hsum, div_self hH.ne']
    · intro d hd
      exact subset_convexHull ℝ _ ⟨d, (Finset.mem_erase.mp hd).1, rfl⟩
  have hval : (∑ d ∈ S, (w d / H) • (fun i => monomialPhase (γ i) d)) =
      (fun _ : ι => -((1 / H : ℝ) : ℂ)) := by
    funext i
    have hs := congrFun hraw i
    simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul] at hs ⊢
    calc
      _ = (∑ d ∈ S, (w d : ℂ) * monomialPhase (γ i) d) / (H : ℂ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d _
        rw [Complex.ofReal_div]
        ring
      _ = (-1 : ℂ) / (H : ℂ) := by rw [hs]
      _ = _ := by simp only [Complex.ofReal_div, Complex.ofReal_one, neg_div]
  rwa [hval] at hm

/-- Every actual antipodal convex representation yields a positive polynomial
with exactly the prescribed mass at any real abscissa. -/
theorem exists_annihilator_of_phaseConvexHull (β : ℝ) (γ : ι → ℝ)
    {H : ℝ} (hH : 0 < H)
    (hx : (fun _ : ι => -((1 / H : ℝ) : ℂ)) ∈ convexHull ℝ (monomialPhaseSet γ)) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β = H := by
  classical
  obtain ⟨κ, hκ, z, a, hz, _, ha, hsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  have hex : ∀ k, ∃ d : Fin 2 →₀ ℕ, d ≠ 0 ∧
      (fun i => monomialPhase (γ i) d) = z k := fun k => hz ⟨k, rfl⟩
  choose d hd he using hex
  let w : κ → ℝ≥0 := fun k => ⟨a k * H, mul_nonneg (ha k).le hH.le⟩
  have hw : ∑ k, (w k : ℝ) = H := by
    change (∑ k, a k * H) = H
    rw [← Finset.sum_mul, hsum, one_mul]
  have hp (i : ι) : ∑ k, ((w k : ℝ) : ℂ) * monomialPhase (γ i) (d k) = -1 := by
    change (∑ k, ((a k * H : ℝ) : ℂ) * monomialPhase (γ i) (d k)) = -1
    have hc := congrFun hcomb i
    simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul] at hc
    have hz' (k : κ) : z k i = monomialPhase (γ i) (d k) := (congrFun (he k) i).symm
    simp_rw [hz'] at hc
    calc
      _ = (∑ k, (a k : ℂ) * monomialPhase (γ i) (d k)) * (H : ℂ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [Complex.ofReal_mul]
        ring
      _ = -((1 / H : ℝ) : ℂ) * (H : ℂ) := by rw [hc]
      _ = -1 := by
        rw [Complex.ofReal_div, Complex.ofReal_one]
        have hHc : (H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hH.ne'
        field_simp
  obtain ⟨P, hc, heval, hm⟩ := exists_annihilator_of_phase_combination β γ d w hd hp
  exact ⟨P, hc, heval, hm.trans hw⟩

/-- Exact positive annihilator mass is equivalent to actual finite phase-convex
membership, independently of the common real abscissa. -/
theorem exact_annihilator_mass_iff_phaseConvexHull (β : ℝ) (γ : ι → ℝ)
    {H : ℝ} (hH : 0 < H) :
    (∃ P : MvPolynomial (Fin 2) ℝ≥0, MvPolynomial.constantCoeff P = 1 ∧
      (∀ i, dirichletEval (harmonicPacketPoint β (γ i) 1) P = 0) ∧
      dirichletTailMass P β = H) ↔
    (fun _ : ι => -((1 / H : ℝ) : ℂ)) ∈ convexHull ℝ (monomialPhaseSet γ) := by
  constructor
  · rintro ⟨P, hc, he, hm⟩
    exact phase_point_mem_convexHull_of_annihilator hc β γ he hH hm
  · exact exists_annihilator_of_phaseConvexHull β γ hH

#print axioms exact_annihilator_mass_iff_phaseConvexHull

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
