import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.ActualBoundaryEnergy
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.PolynomialGapScale

/-!
# Polynomial repulsion from maximal zero width

Bounded natural two-prime cone coupling either implies RH or keeps every
zeta zero a polynomial height distance below maximal width. The boundary
energy inequality and a quadratic height cutoff exclude smaller gaps;
reflection gives the bound on both sides of the critical line.
-/

open Complex
open Zeta23
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.SquareRootThreshold
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
open ConeCoupling

/-- Bounded coupling on a natural two-prime cone either gives RH or forces
every actual zero to stay a polynomial height distance below maximal width. -/
theorem riemannHypothesis_or_polynomial_boundary_repulsion {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcone : ∃ M : ℝ, ∀ m n : ℕ,
      ‖coupling zetaKernel (primeElt hp^m) (primeElt hq^n)‖ ≤ M) :
    RiemannHypothesis ∨ ∃ c : ℝ, 0 < c ∧ ∃ A : ℕ, 0 < A ∧
      ∀ ρ : zetaZeroConfig.carrier,
        c/(1+|(ρ:ℂ).im|)^A ≤ zetaZeroWidth-|(ρ:ℂ).re-1/2| := by
  by_cases hD : zetaZeroWidth=0
  · exact Or.inl (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr hD)
  have hDpos : 0 < zetaZeroWidth := lt_of_le_of_ne zetaZeroWidth_nonneg (Ne.symm hD)
  obtain ⟨A,B,s₀,N,hA,hB,hs₀,_,_,henergy⟩ :=
    exists_actual_boundary_energy_bound hp hq hpq hDpos hcone
  obtain ⟨c,hc,hcs₀,hscale⟩ := exists_polynomial_gap_scale hA hB hs₀ N
  have hright (ρ : zetaZeroConfig.carrier) :
      c/(1+|(ρ:ℂ).im|)^(2*N+8) < zetaZeroWidth-(zeroOffset ρ).re := by
    let H := 1+|(ρ:ℂ).im|
    have hH : 1 ≤ H := le_add_of_nonneg_right (abs_nonneg _)
    have hHp : 0 < H := zero_lt_one.trans_le hH
    let s := c/H^(2*N+8)
    have hs : 0 < s := div_pos hc (pow_pos hHp _)
    have hss₀ : s ≤ s₀ :=
      (div_le_self hc.le (one_le_pow₀ hH)).trans hcs₀
    obtain ⟨T,hHT,hsmall⟩ := hscale H hH
    by_contra hgap
    have hgap' : zetaZeroWidth-(zeroOffset ρ).re ≤ s := le_of_not_gt hgap
    have hh := henergy ρ s T hs hss₀ hgap' hHT
    exact (not_lt_of_ge hh) hsmall
  refine Or.inr ⟨c,hc,2*N+8,by omega,?_⟩
  intro ρ
  by_cases hδ : 0 ≤ (ρ:ℂ).re-1/2
  · rw [abs_of_nonneg hδ]
    simpa only [zeroOffset_re] using (hright ρ).le
  let σ : zetaZeroConfig.carrier := ⟨Zeta23.reflect (ρ:ℂ),zetaZeroConfig.reflect_mem _ ρ.2⟩
  have hσre : (σ:ℂ).re=1-(ρ:ℂ).re := by simp only [σ,Zeta23.reflect,Complex.sub_re,
    Complex.one_re,Complex.conj_re]
  have hσim : (σ:ℂ).im=(ρ:ℂ).im := by simp only [σ,Zeta23.reflect,Complex.sub_im,
    Complex.one_im,Complex.conj_im,zero_sub,neg_neg]
  have hh := (hright σ).le
  rw [zeroOffset_re,hσre,hσim] at hh
  rw [abs_of_neg (lt_of_not_ge hδ)]
  linarith only [hh]

#print axioms riemannHypothesis_or_polynomial_boundary_repulsion
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
