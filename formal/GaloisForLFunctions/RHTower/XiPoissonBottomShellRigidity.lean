import GaloisForLFunctions.RHTower.XiPoissonShell
import GaloisForLFunctions.HTGeometry.RealExponentialSumRigidity
import GaloisForLFunctions.HTGeometry.AbstractSpectralShell

/-!
# Rigidity of the bottom Poisson shell

Every copy in a Poisson shell has the same height `R`, so on a vertical line the shell sum factors as

`sum_{q in shell} exp (-t alpha^ q) = exp (-t R) * sum_{q in shell} exp (-i sigma J q) * exp (u J q)`,

a pure phase times a **finite sum of real exponentials** in the vertical variable `u`, with exponents
the displacements `J q` and coefficients of modulus one.  Grouping equal displacements gives
coefficients `(multiplicity) * exp (-i sigma J)`, which are nonzero.  The rigidity of
`HTGeometry.abs_le_of_expSum_norm_le` then converts a growth bound on the shell sum into a bound on
the displacements themselves: a bounded shell sum forces the bottom shell onto the critical line.

No separation or Diophantine hypothesis on the divisor is used.  Shell homogeneity does the work,
and it is a property of the Poisson coordinate: in the squared coordinate a shell mixes heights and
displacements, and the extracted sum is not a real-exponential sum.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A copy of least height. -/
def xiPoissonBottomCopy : XiZeroCopy := Classical.choose exists_min_xiPoissonPoint_re

theorem xiPoissonBottomCopy_min (q : XiZeroCopy) :
    (xiPoissonPoint xiPoissonBottomCopy).re ≤ (xiPoissonPoint q).re :=
  Classical.choose_spec exists_min_xiPoissonPoint_re q

/-- The least height of the Xi divisor in the Poisson coordinate. -/
def xiPoissonBottomHeight : ℝ := (xiPoissonPoint xiPoissonBottomCopy).re

/-- The bottom Poisson shell, as a finite set of copies. -/
def xiPoissonBottomShell : Finset XiZeroCopy :=
  (finite_xiPoissonShell xiPoissonBottomHeight).toFinset

theorem mem_xiPoissonBottomShell {q : XiZeroCopy} :
    q ∈ xiPoissonBottomShell ↔ (xiPoissonPoint q).re = xiPoissonBottomHeight := by
  rw [xiPoissonBottomShell, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨fun h => le_antisymm h (xiPoissonBottomCopy_min q), fun h => le_of_eq h⟩

/-- The line factorization of a single Poisson multiplier at a fixed height. -/
theorem xiPoisson_line_factor (σ u R Jq : ℝ) :
    Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * ((R : ℂ) + (Jq : ℂ) * I)) =
      Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (R : ℂ)) *
        (Complex.exp (-(σ : ℂ) * I * (Jq : ℂ)) * ((Real.exp (u * Jq) : ℝ) : ℂ)) :=
  _root_.HTGeometry.vertLine_factor σ u R Jq

/-- The bottom-shell sum on the vertical line `Re t = sigma`. -/
def xiPoissonBottomShellSum (σ u : ℝ) : ℂ :=
  ∑ q ∈ xiPoissonBottomShell, xiPoissonTerm ((σ : ℂ) + (u : ℂ) * I) q

/-- Shell homogeneity: the shell sum factors as a height factor times a real-exponential sum in the
vertical variable. -/
theorem xiPoissonBottomShellSum_eq (σ u : ℝ) :
    xiPoissonBottomShellSum σ u =
      Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (xiPoissonBottomHeight : ℂ)) *
        ∑ q ∈ xiPoissonBottomShell,
          Complex.exp (-(σ : ℂ) * I * ((xiPoissonPoint q).im : ℂ)) *
            ((Real.exp (u * (xiPoissonPoint q).im) : ℝ) : ℂ) := by
  rw [xiPoissonBottomShellSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hsplit : xiPoissonPoint q =
      ((xiPoissonBottomHeight : ℝ) : ℂ) + ((xiPoissonPoint q).im : ℂ) * I := by
    rw [← mem_xiPoissonBottomShell.mp hq]
    exact (Complex.re_add_im _).symm
  rw [xiPoissonTerm]
  conv_lhs => rw [hsplit]
  exact xiPoisson_line_factor σ u xiPoissonBottomHeight (xiPoissonPoint q).im

/-- **Bottom-shell rigidity.**  If the bottom-shell sum on a vertical line grows no faster than
`exp (lam * |u|)`, every copy in the bottom shell has displacement at most `lam`.  With `lam = 0`
this says a bounded bottom-shell sum forces the lowest zeros onto the critical line. -/
theorem abs_im_xiPoissonPoint_le_of_bottomShellSum_growth {σ C lam : ℝ}
    (hgrowth : ∀ u : ℝ,
      ‖xiPoissonBottomShellSum σ u‖ ≤
        Real.exp (-(σ * xiPoissonBottomHeight)) * (C * Real.exp (lam * |u|))) :
    ∀ q ∈ xiPoissonBottomShell, |(xiPoissonPoint q).im| ≤ lam := by
  classical
  set s : Finset XiZeroCopy := xiPoissonBottomShell with hs
  set J : XiZeroCopy → ℝ := fun q => (xiPoissonPoint q).im with hJ
  set T : Finset ℝ := s.image J with hT
  set B : ℝ → ℂ := fun j => (((s.filter fun q => J q = j).card : ℝ) : ℂ) *
    Complex.exp (-(σ : ℂ) * I * (j : ℂ)) with hB
  -- the shell sum, regrouped by displacement
  have hregroup : ∀ u : ℝ,
      (∑ q ∈ s, Complex.exp (-(σ : ℂ) * I * ((J q : ℝ) : ℂ)) *
          ((Real.exp (u * J q) : ℝ) : ℂ))
        = ∑ j ∈ T, B j * ((Real.exp (u * j) : ℝ) : ℂ) := by
    intro u
    rw [← Finset.sum_fiberwise_of_maps_to (t := T)
      (fun q hq => Finset.mem_image_of_mem J hq)
      (fun q => Complex.exp (-(σ : ℂ) * I * ((J q : ℝ) : ℂ)) *
        ((Real.exp (u * J q) : ℝ) : ℂ))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hfib : ∀ q ∈ s.filter (fun q => J q = j),
        Complex.exp (-(σ : ℂ) * I * ((J q : ℝ) : ℂ)) * ((Real.exp (u * J q) : ℝ) : ℂ)
          = Complex.exp (-(σ : ℂ) * I * (j : ℂ)) * ((Real.exp (u * j) : ℝ) : ℂ) :=
      fun q hq => by rw [(Finset.mem_filter.mp hq).2]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul, hB]
    push_cast
    ring
  -- the growth hypothesis, transported to the regrouped sum
  have hbound : ∀ u : ℝ, ‖∑ j ∈ T, B j * ((Real.exp (u * j) : ℝ) : ℂ)‖ ≤
      C * Real.exp (lam * |u|) := by
    intro u
    rw [← hregroup u]
    have hfac := xiPoissonBottomShellSum_eq σ u
    have hnorm : ‖Complex.exp (-((σ : ℂ) + (u : ℂ) * I) * (xiPoissonBottomHeight : ℂ))‖ =
        Real.exp (-(σ * xiPoissonBottomHeight)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    have h := hgrowth u
    rw [hfac, norm_mul, hnorm] at h
    have hpos : 0 < Real.exp (-(σ * xiPoissonBottomHeight)) := Real.exp_pos _
    exact le_of_mul_le_mul_left (by simpa [mul_comm] using h) hpos
  -- coefficients are nonzero
  have hBne : ∀ j ∈ T, B j ≠ 0 := by
    intro j hj
    obtain ⟨q, hqs, hqj⟩ := Finset.mem_image.mp hj
    have hcard : 0 < (s.filter fun q => J q = j).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hqs, hqj⟩⟩
    rw [hB]
    exact mul_ne_zero (by exact_mod_cast Nat.cast_ne_zero.mpr hcard.ne') (Complex.exp_ne_zero _)
  have hkey := HTGeometry.abs_le_of_expSum_norm_le T (fun j => j) B
    (fun i _ j _ h => h) hBne hbound
  intro q hq
  exact hkey (J q) (Finset.mem_image_of_mem J hq)

/-- **A bounded bottom-shell sum puts the lowest zeros on the critical line.**  The case `lam = 0`
of bottom-shell rigidity. -/
theorem xiSpectralPoint_im_eq_zero_of_bottomShellSum_bounded {σ C : ℝ}
    (hbdd : ∀ u : ℝ,
      ‖xiPoissonBottomShellSum σ u‖ ≤ Real.exp (-(σ * xiPoissonBottomHeight)) * C) :
    ∀ q ∈ xiPoissonBottomShell, (xiSpectralPoint q).im = 0 := by
  intro q hq
  have h := abs_im_xiPoissonPoint_le_of_bottomShellSum_growth (σ := σ) (C := C) (lam := 0)
    (by intro u; simpa using hbdd u) q hq
  have hzero : (xiPoissonPoint q).im = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  rw [xiPoissonPoint] at hzero
  split_ifs at hzero with hcase
  · exact hzero
  · rw [Complex.neg_im, neg_eq_zero] at hzero
    exact hzero

end

end RHTower
