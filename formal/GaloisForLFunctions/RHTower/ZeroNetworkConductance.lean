import GaloisForLFunctions.RHTower.TransverseEquilibrium
import GaloisForLFunctions.RHTower.XiZeroBandFinite
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# The zero network is locally finite

Gate **R** of the transverse-equilibrium chain asks for recurrence of the network whose vertices are
the zeros and whose conductance between two of them is the reciprocal squared distance.  Before
recurrence one needs the network to exist: every vertex must have **finite total conductance**.  That
is proved here, and it simultaneously discharges the convergence obligation left open when
`transverseForce` was defined as an unrestricted sum.

The proof splits the divisor at a given zero into the points whose ordinate is within one of it —
finitely many, since the divisor is locally finite — and the rest, where the squared distance is at
least the squared ordinate gap and the corpus's Cauchy weight dominates.
-/

open Complex Set

namespace RHTower

noncomputable section

/-! ## Transporting the Cauchy weight from copies to support points -/

/-- The canonical first copy of a divisor point. -/
def supportToCopy (ρ : XiDivisorSupport) : XiZeroCopy :=
  ⟨ρ, ⟨0, by have := xi_divisor_pos_on_support ρ; omega⟩⟩

theorem supportToCopy_injective : Function.Injective supportToCopy := fun _ _ h =>
  congrArg Sigma.fst h

@[simp]
theorem supportToCopy_fst (ρ : XiDivisorSupport) : (supportToCopy ρ).1 = ρ := rfl

/-- The Cauchy weight as a function of a copy. -/
private def cauchyWeightCopy (x : ℝ) (q : XiZeroCopy) : ℝ :=
  (1 : ℝ) / (1 + (x - (q.1 : ℂ).im) ^ (2 : ℕ))

/-- The Cauchy weight is summable over the divisor support.  The statement is written in the exact
`∘` form produced by `Summable.comp_injective`, so the transport is a syntactic match and no
unification through the proof term inside `supportToCopy` is needed. -/
theorem summable_supportWeight (x : ℝ) :
    Summable (fun ρ : XiDivisorSupport => (1 : ℝ) / (1 + (x - (ρ : ℂ).im) ^ (2 : ℕ))) := by
  have h : Summable (cauchyWeightCopy x ∘ supportToCopy) :=
    (summable_xiZeroWeight x).comp_injective supportToCopy_injective
  exact h

/-! ## The conductance -/

/-- Every divisor point lies in the open critical strip. -/
theorem xiDivisorSupport_re_mem (ρ : XiDivisorSupport) :
    0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
  xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support ρ)

/-- The conductance of the zero network: the reciprocal squared distance. -/
def zeroConductance (j k : XiDivisorSupport) : ℝ := 1 / Complex.normSq ((j : ℂ) - (k : ℂ))

theorem zeroConductance_nonneg (j k : XiDivisorSupport) : 0 ≤ zeroConductance j k :=
  div_nonneg zero_le_one (Complex.normSq_nonneg _)

/-- The squared ordinate gap is at most the squared distance. -/
theorem sq_im_sub_le_normSq (j k : XiDivisorSupport) :
    ((j : ℂ).im - (k : ℂ).im) ^ (2 : ℕ) ≤ Complex.normSq ((j : ℂ) - (k : ℂ)) := by
  rw [Complex.normSq_apply, Complex.sub_im, pow_two]
  nlinarith [mul_self_nonneg (((j : ℂ) - (k : ℂ)).re)]

/-- Away from the ordinate of `j` the conductance is dominated by twice the Cauchy weight. -/
theorem zeroConductance_le_of_far {j k : XiDivisorSupport}
    (h : 1 < |(j : ℂ).im - (k : ℂ).im|) :
    zeroConductance j k ≤ 2 * ((1 : ℝ) / (1 + ((j : ℂ).im - (k : ℂ).im) ^ (2 : ℕ))) := by
  set d : ℝ := (j : ℂ).im - (k : ℂ).im with hd
  have h1 : 1 < d ^ (2 : ℕ) := by
    have hsq : (1 : ℝ) < |d| ^ (2 : ℕ) := by nlinarith [abs_nonneg d]
    rwa [sq_abs] at hsq
  have hpos : (0 : ℝ) < d ^ (2 : ℕ) := by linarith
  have hden : (0 : ℝ) < 1 + d ^ (2 : ℕ) := by linarith
  have step1 : zeroConductance j k ≤ 1 / d ^ (2 : ℕ) :=
    div_le_div_of_nonneg_left zero_le_one hpos (sq_im_sub_le_normSq j k)
  have heq : (1 : ℝ) / d ^ (2 : ℕ) = 2 / (2 * d ^ (2 : ℕ)) := by field_simp
  have step2 : (1 : ℝ) / d ^ (2 : ℕ) ≤ 2 * ((1 : ℝ) / (1 + d ^ (2 : ℕ))) := by
    rw [heq, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) hden (by linarith)
  exact step1.trans step2

/-- The near set at a vertex: divisor points whose ordinate is within one of it. -/
private def nearSet (j : XiDivisorSupport) : Set XiDivisorSupport :=
  {k | |(k : ℂ).im - (j : ℂ).im| ≤ 1}

private theorem nearSet_finite (j : XiDivisorSupport) : (nearSet j).Finite :=
  finite_xiDivisorSupport_band ((j : ℂ).im) zero_le_one

/-- **The total conductance at every vertex is finite**: the zero network is locally finite. -/
theorem summable_zeroConductance (j : XiDivisorSupport) :
    Summable (fun k : XiDivisorSupport => zeroConductance j k) := by
  refine summable_subtype_and_compl.mp
    ⟨(nearSet_finite j).summable (fun k => zeroConductance j k), ?_⟩
  refine Summable.of_nonneg_of_le (fun k => zeroConductance_nonneg j _) (fun k => ?_)
    (((summable_supportWeight ((j : ℂ).im)).subtype (nearSet j)ᶜ).mul_left 2)
  have hk : ¬ (|((k : XiDivisorSupport) : ℂ).im - (j : ℂ).im| ≤ 1) := k.2
  exact zeroConductance_le_of_far (by rw [abs_sub_comm]; exact lt_of_not_ge hk)

/-! ## Absolute convergence of the transverse force -/

/-- The transverse force term is bounded by the conductance, because both real parts lie in the
open unit interval. -/
theorem abs_transverseForceTerm_le (j k : XiDivisorSupport) :
    |transverseForceTerm j k| ≤ zeroConductance j k := by
  rw [transverseForceTerm, zeroConductance]
  split_ifs with h
  · rw [abs_zero]
    exact div_nonneg zero_le_one (Complex.normSq_nonneg _)
  · have hne : ((j : ℂ)) - ((k : ℂ)) ≠ 0 := fun hc =>
      h (Subtype.ext (by linear_combination -hc))
    have hpos : 0 < Complex.normSq ((j : ℂ) - (k : ℂ)) := Complex.normSq_pos.mpr hne
    rw [abs_div, abs_of_pos hpos]
    have hj := xiDivisorSupport_re_mem j
    have hk := xiDivisorSupport_re_mem k
    have hnum : |(j : ℂ).re - (k : ℂ).re| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hj.2, hk.1], by linarith [hj.1, hk.2]⟩
    gcongr

/-- **The transverse force is an absolutely convergent sum.**  This discharges the convergence
obligation implicit in the definition of `transverseForce`. -/
theorem summable_transverseForceTerm (j : XiDivisorSupport) :
    Summable (fun k : XiDivisorSupport => transverseForceTerm j k) :=
  (summable_zeroConductance j).of_norm_bounded fun k => by
    rw [Real.norm_eq_abs]; exact abs_transverseForceTerm_le j k

end

end RHTower
