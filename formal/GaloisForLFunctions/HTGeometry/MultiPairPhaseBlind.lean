import GaloisForLFunctions.HTGeometry.OnePairSumOfSquares
import GaloisForLFunctions.HTGeometry.BohrFiniteRecurrence

/-!
# Sums of Hermitian squares certify only the phase-blind condition

The unfolding obstruction separates growth from phase.  For a comparison with several conjugate
pairs the phase variable is shared, so a priori only the *coupled* phases are freed.  Bohr recurrence
removes the coupling: a finite family of characters returns simultaneously to `1` at arbitrarily
large times, whatever the frequencies, commensurable or not.  Hence

> if `R(t) - ∑_j 2 e^{β_j t} cos(γ_j t)` is a sum of Hermitian squares, then
> `R(t) ≥ ∑_j 2 e^{β_j t}` for every `t`.

That is exactly the per-pair relaxation, which `PerPairGapUnbounded` shows is off by a factor
growing linearly in the number of pairs.  Sums of Hermitian squares are therefore an unboundedly
weak certificate class for realizability with several complex zeros.
-/

open Finset Real

namespace GaloisForLFunctions.HTGeometry

/-! ## The obstruction over an arbitrary index type -/

/-- The unfolding of an exponential polynomial indexed by an arbitrary finite type. -/
noncomputable def unfoldSumIdx {ι : Type*} [Fintype ι] (w lam : ι → ℂ) (t u : ℝ) : ℂ :=
  ∑ i, w i * unfoldChar (lam i) t u

/-- `f` is a sum of Hermitian squares, with the exponential polynomial indexed by `ι`. -/
def IsHermitianSOSIdx {ι : Type*} [Fintype ι] {L m : ℕ} (w lam : ι → ℂ)
    (v : Fin L → Fin m → ℂ) (μ : Fin m → ℂ) : Prop :=
  ∀ t : ℝ, ∑ i, w i * Complex.exp (lam i * t)
    = ∑ l, ((Complex.normSq (∑ j, v l j * Complex.exp (μ j * t)) : ℝ) : ℂ)

theorem unfoldSumIdx_nonneg_of_isHermitianSOSIdx {ι : Type*} [Fintype ι] {L m : ℕ}
    (w lam : ι → ℂ) (v : Fin L → Fin m → ℂ) (μ : Fin m → ℂ)
    (h : IsHermitianSOSIdx w lam v μ) (t u : ℝ) : 0 ≤ (unfoldSumIdx w lam t u).re := by
  have hexp : ∀ s : ℝ, ∑ i, w i * Complex.exp (lam i * s)
      = ∑ p : Fin m × Fin m, (∑ l, v l p.1 * (starRingEnd ℂ) (v l p.2))
          * Complex.exp ((μ p.1 + (starRingEnd ℂ) (μ p.2)) * s) := by
    intro s
    rw [h s]
    refine gram_expand v μ (fun a => Complex.exp (a * s)) (fun a b => ?_) (fun a => ?_)
    · rw [← Complex.exp_add]; congr 1; ring
    · rw [← Complex.exp_conj]; congr 1; simp
  have hunf := unfold_eq_of_eq hexp t u
  rw [unfoldSumIdx, hunf]
  have hgram := gram_expand v μ (fun a => unfoldChar a t u)
    (fun a b => unfoldChar_add a b t u) (fun a => unfoldChar_conj a t u)
  rw [← hgram, Complex.re_sum]
  refine Finset.sum_nonneg (fun l _ => ?_)
  rw [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-! ## The multi-pair comparison and its unfolding -/

variable {m r : ℕ}

/-- Exponents of `R(t) - ∑_j 2 e^{β_j t} cos(γ_j t)`. -/
noncomputable def mpLam (a : Fin m → ℝ) (β γ : Fin r → ℝ) :
    Fin m ⊕ Fin r ⊕ Fin r → ℂ :=
  Sum.elim (fun i => ((a i : ℝ) : ℂ))
    (Sum.elim (fun j => ((β j : ℝ) : ℂ) + Complex.I * ((γ j : ℝ) : ℂ))
      (fun j => ((β j : ℝ) : ℂ) - Complex.I * ((γ j : ℝ) : ℂ)))

/-- Coefficients of `R(t) - ∑_j 2 e^{β_j t} cos(γ_j t)`. -/
noncomputable def mpW (c : Fin m → ℝ) (r : ℕ) : Fin m ⊕ Fin r ⊕ Fin r → ℂ :=
  Sum.elim (fun i => ((c i : ℝ) : ℂ)) (Sum.elim (fun _ => (-1 : ℂ)) (fun _ => (-1 : ℂ)))

private theorem unfoldChar_ofReal' (x t u : ℝ) :
    unfoldChar ((x : ℝ) : ℂ) t u = Complex.exp (((x * t : ℝ) : ℂ)) := by
  rw [unfoldChar]; norm_num

private theorem unfoldChar_pair (b g t u : ℝ) :
    unfoldChar (((b : ℝ) : ℂ) + Complex.I * ((g : ℝ) : ℂ)) t u
        + unfoldChar (((b : ℝ) : ℂ) - Complex.I * ((g : ℝ) : ℂ)) t u
      = ((2 * Real.exp (b * t) * Real.cos (g * u) : ℝ) : ℂ) := by
  have e1 : unfoldChar (((b : ℝ) : ℂ) + Complex.I * ((g : ℝ) : ℂ)) t u
      = Complex.exp (((b * t : ℝ) : ℂ) + Complex.I * ((g * u : ℝ) : ℂ)) := by
    rw [unfoldChar]; norm_num
  have e2 : unfoldChar (((b : ℝ) : ℂ) - Complex.I * ((g : ℝ) : ℂ)) t u
      = Complex.exp (((b * t : ℝ) : ℂ) + Complex.I * (((-g) * u : ℝ) : ℂ)) := by
    rw [unfoldChar]; norm_num
  have hz : Complex.I * ((g * u : ℝ) : ℂ) = ((g * u : ℝ) : ℂ) * Complex.I := by ring
  have hz2 : Complex.I * (((-g) * u : ℝ) : ℂ) = -((g * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e1, e2, Complex.exp_add, Complex.exp_add, hz, hz2]
  have h2 := Complex.two_cos ((g * u : ℝ) : ℂ)
  push_cast at h2 ⊢
  linear_combination (-(Complex.exp ((b : ℂ) * (t : ℂ)))) * h2

theorem unfoldSumIdx_multiPair (c a : Fin m → ℝ) (β γ : Fin r → ℝ) (t u : ℝ) :
    unfoldSumIdx (mpW c r) (mpLam a β γ) t u
      = ((∑ i, c i * Real.exp (a i * t)
          - ∑ j, 2 * Real.exp (β j * t) * Real.cos (γ j * u) : ℝ) : ℂ) := by
  rw [unfoldSumIdx, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [mpW, mpLam, Sum.elim_inl, Sum.elim_inr]
  rw [show (∑ i, ((c i : ℝ) : ℂ) * unfoldChar (((a i : ℝ) : ℂ)) t u)
      = ((∑ i, c i * Real.exp (a i * t) : ℝ) : ℂ) from by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [unfoldChar_ofReal', ← Complex.ofReal_exp, ← Complex.ofReal_mul])]
  rw [show ((∑ j, (-1 : ℂ) * unfoldChar (((β j : ℝ) : ℂ)
        + Complex.I * ((γ j : ℝ) : ℂ)) t u)
      + ∑ j, (-1 : ℂ) * unfoldChar (((β j : ℝ) : ℂ) - Complex.I * ((γ j : ℝ) : ℂ)) t u)
      = -((∑ j, 2 * Real.exp (β j * t) * Real.cos (γ j * u) : ℝ) : ℂ) from by
    rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← unfoldChar_pair (β j) (γ j) t u]
    ring]
  push_cast
  ring

/-! ## Bohr recurrence removes the phase coupling -/

/-- **Phase blindness.**  If the unfolded comparison is nonnegative — the phases coupled through a
single variable — then the fully decoupled comparison is nonnegative as well.  The reason is that a
finite family of characters returns simultaneously to `1`. -/
theorem phaseBlind_of_unfold_nonneg (c a : Fin m → ℝ) (β γ : Fin r → ℝ)
    (hunf : ∀ t u : ℝ, ∑ j, 2 * Real.exp (β j * t) * Real.cos (γ j * u)
        ≤ ∑ i, c i * Real.exp (a i * t)) (t : ℝ) :
    ∑ j, 2 * Real.exp (β j * t) ≤ ∑ i, c i * Real.exp (a i * t) := by
  set S : ℝ := ∑ j, 2 * Real.exp (β j * t) with hS
  set Rt : ℝ := ∑ i, c i * Real.exp (a i * t) with hR
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun j _ => by positivity)
  by_contra hcon
  push Not at hcon
  set ε : ℝ := (S - Rt) / (S + 1) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    apply div_pos (by linarith) (by linarith)
  obtain ⟨ξ, _, hξ⟩ := GaloisForLFunctions.exists_large_simultaneous_almostPeriod γ hεpos 0
  have hcos : ∀ j, 1 - ε ≤ Real.cos (γ j * ξ) := by
    intro j
    have hre : (Complex.exp (Complex.I * ((ξ : ℂ) * ((γ j : ℝ) : ℂ))) - 1).re
        = Real.cos (γ j * ξ) - 1 := by
      rw [Complex.sub_re, Complex.exp_re]
      simp only [Complex.one_re]
      have hre0 : (Complex.I * ((ξ : ℂ) * ((γ j : ℝ) : ℂ))).re = 0 := by simp
      have him : (Complex.I * ((ξ : ℂ) * ((γ j : ℝ) : ℂ))).im = ξ * γ j := by simp
      rw [hre0, him, Real.exp_zero, one_mul, mul_comm (γ j) ξ]
    have hbound : |(Complex.exp (Complex.I * ((ξ : ℂ) * ((γ j : ℝ) : ℂ))) - 1).re|
        ≤ ‖Complex.exp (Complex.I * ((ξ : ℂ) * ((γ j : ℝ) : ℂ))) - 1‖ :=
      Complex.abs_re_le_norm _
    rw [hre] at hbound
    have := (abs_le.mp (le_trans hbound (hξ j))).1
    linarith
  have hkey : (1 - ε) * S ≤ ∑ j, 2 * Real.exp (β j * t) * Real.cos (γ j * ξ) := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hpos : (0 : ℝ) < 2 * Real.exp (β j * t) := by positivity
    nlinarith [hcos j]
  have hfin := le_trans hkey (hunf t ξ)
  have hsmall : ε * S < S - Rt := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < S + 1)]
    nlinarith
  linarith

/-- **Sums of Hermitian squares certify only the per-pair condition.**  Combined with
`per_pair_cost_ge` and `offDiagonal_sum_le`, the certificate class is off by an unbounded factor. -/
theorem multiPair_phaseBlind_of_isHermitianSOS {L m' : ℕ} (c a : Fin m → ℝ) (β γ : Fin r → ℝ)
    (v : Fin L → Fin m' → ℂ) (μ : Fin m' → ℂ)
    (h : IsHermitianSOSIdx (mpW c r) (mpLam a β γ) v μ) (t : ℝ) :
    ∑ j, 2 * Real.exp (β j * t) ≤ ∑ i, c i * Real.exp (a i * t) := by
  refine phaseBlind_of_unfold_nonneg c a β γ (fun s u => ?_) t
  have := unfoldSumIdx_nonneg_of_isHermitianSOSIdx (mpW c r) (mpLam a β γ) v μ h s u
  rw [unfoldSumIdx_multiPair, Complex.ofReal_re] at this
  linarith


/-- **The per-pair cost is forced.**  With all pairs on the imaginary axis, a Hermitian-square
certificate forces the compared sum to dominate `2r` everywhere — exactly the cost of certifying the
pairs one at a time, which `offDiagonal_sum_le` shows can exceed the true requirement by a factor
growing linearly in the number of pairs. -/
theorem multiPair_const_bound {L m' : ℕ} (c a : Fin m → ℝ) (γ : Fin r → ℝ)
    (v : Fin L → Fin m' → ℂ) (μ : Fin m' → ℂ)
    (h : IsHermitianSOSIdx (mpW c r) (mpLam a (fun _ => 0) γ) v μ) (t : ℝ) :
    2 * r ≤ ∑ i, c i * Real.exp (a i * t) := by
  have hb := multiPair_phaseBlind_of_isHermitianSOS c a (fun _ => (0 : ℝ)) γ v μ h t
  have hval : (∑ _j : Fin r, 2 * Real.exp ((0 : ℝ) * t)) = 2 * r := by
    simp [Finset.sum_const, Finset.card_univ]
    ring
  rw [hval] at hb
  exact hb

end GaloisForLFunctions.HTGeometry
