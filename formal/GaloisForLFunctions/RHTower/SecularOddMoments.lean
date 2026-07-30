/-
# Secular odd moments of ξ's zeros vanish (foundations §22, `τ_{2m+1}=0`, for the actual ξ)

`FunctionalEquationParity.fe_centered_odd_moment_vanish` proves the σ-parity for an abstract
FE-reflection-invariant multiset.  This file instantiates it on the genuine object: the zeros of `ξ`
inside any ball centered at the critical point `½` form an FE-reflection-invariant configuration
(`ξ(1−s)=ξ(s)`, and the ball is invariant under `ρ ↦ 1−ρ`), and the reflection preserves multiplicity
(`xi_orderAt_one_sub`).  Hence every multiplicity-weighted centered odd moment of those zeros vanishes.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.Reflection

open Complex

namespace RHTower

noncomputable section

/-- **Secular odd moments vanish (for the actual ξ).**  For every radius `R` and every `m`, the
multiplicity-weighted centered odd moment of `ξ`'s zeros in the ball `‖s − ½‖ < R` vanishes:
`∑_{ρ : ‖ρ−½‖<R, ξ(ρ)=0} ord_ρ(ξ) · (ρ − ½)^{2m+1} = 0`.  The functional equation pairs each `ρ` with
`1−ρ` (same multiplicity, reflected through `½`), and the odd power makes the two contributions
cancel; the fixed point `½` contributes `0`.  This is `τ_{2m+1}=0` for the genuine ξ-divisor. -/
theorem xi_secular_odd_moment_ball_eq_zero (R : ℝ) (m : ℕ) :
    ∑ ρ ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset,
      ((analyticOrderAt xi ρ).toNat : ℂ) * (ρ - 1 / 2) ^ (2 * m + 1) = 0 := by
  refine Finset.sum_involution (fun ρ _ => 1 - ρ) ?_ ?_ ?_ ?_
  · -- pairing: f ρ + f (1−ρ) = 0
    intro ρ _
    have hord : analyticOrderAt xi (1 - ρ) = analyticOrderAt xi ρ := xi_orderAt_one_sub ρ
    have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
    have hpow : (1 - ρ - 1 / 2) ^ (2 * m + 1) = -((ρ - 1 / 2) ^ (2 * m + 1)) := by
      rw [show (1 - ρ - 1 / 2) = -(ρ - 1 / 2) by ring, hodd.neg_pow]
    rw [hord, hpow]; ring
  · -- if the term is nonzero, `ρ` is not a fixed point
    intro ρ _ hfne heq
    apply hfne
    have hhalf : ρ = 1 / 2 := by linear_combination (-1 / 2 : ℂ) * heq
    rw [hhalf]; simp
  · -- the reflection maps the zero-set to itself
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨hball, hz⟩ := hρ
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq] at hball ⊢
      rwa [show (1 - ρ) - 1 / 2 = -(ρ - 1 / 2) by ring, norm_neg]
    · rw [xi_one_sub]; exact hz
  · -- the reflection is an involution
    intro ρ _; ring

/-- **Conjugate parity of the centered moments (the critical-line reflection).**  The reflection
`ρ ↦ 1 − conj ρ` (whose fixed set is the critical line) preserves the ξ-divisor in a `½`-centered ball
(`ξ(1−conj ρ) = conj(ξ ρ)`, and multiplicity is preserved).  Hence every centered moment obeys
`conj(M_n) = (−1)^n M_n`: the even centered moments are real and the odd ones purely imaginary — the
functional-equation reality constraint on the ξ-divisor. -/
theorem xi_secular_moment_conj_parity (R : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (∑ ρ ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset,
        ((analyticOrderAt xi ρ).toNat : ℂ) * (ρ - 1 / 2) ^ n)
      = (-1) ^ n * ∑ ρ ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset,
        ((analyticOrderAt xi ρ).toNat : ℂ) * (ρ - 1 / 2) ^ n := by
  have hc12 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  have hkey : ∀ z : ℂ, (1 - (starRingEnd ℂ) z) - 1 / 2 = -((starRingEnd ℂ) (z - 1 / 2)) := by
    intro z; rw [map_sub, hc12]; ring
  have hrefl : ∀ z : ℂ, (1 : ℂ) - (starRingEnd ℂ) z = (starRingEnd ℂ) (1 - z) := by
    intro z; rw [map_sub, map_one]
  have hmem : ∀ ρ ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset,
      (1 - (starRingEnd ℂ) ρ) ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨hball, hz⟩ := hρ
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq] at hball ⊢
      rw [hkey ρ, norm_neg, Complex.norm_conj]; exact hball
    · rw [hrefl ρ, xi_conj, xi_one_sub, hz, map_zero]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_bij' (fun ρ _ => 1 - (starRingEnd ℂ) ρ) (fun ρ _ => 1 - (starRingEnd ℂ) ρ)
    hmem hmem ?_ ?_ ?_
  · intro ρ _; simp only [map_sub, map_one, Complex.conj_conj]; ring
  · intro ρ _; simp only [map_sub, map_one, Complex.conj_conj]; ring
  · intro ρ _
    have hord : analyticOrderAt xi (1 - (starRingEnd ℂ) ρ) = analyticOrderAt xi ρ := by
      rw [hrefl ρ, xi_orderAt_conj, xi_orderAt_one_sub]
    rw [map_mul, map_natCast, map_pow, hord, hkey ρ, mul_left_comm, ← mul_pow, neg_mul_neg,
      one_mul]

/-- **The off-line ξ-multiplicity in a `½`-centered ball is even.**  The critical-line reflection
`ρ ↦ 1 − conj ρ` (`Re ↦ 1 − Re`) is a fixed-point-free involution on the off-critical-line zeros
(`Re ≠ ½`) of `ξ` in the ball, preserving multiplicity.  Hence the total order of the off-line zeros is
even: off-line zeros occur in reflected pairs of equal multiplicity. -/
theorem xi_offline_multiplicity_even_ball (R : ℝ) :
    Even (∑ ρ ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset.filter (fun ρ => ρ.re ≠ 1 / 2),
      (analyticOrderAt xi ρ).toNat) := by
  have hrefl : ∀ z : ℂ, (1 : ℂ) - (starRingEnd ℂ) z = (starRingEnd ℂ) (1 - z) := by
    intro z; rw [map_sub, map_one]
  have hc12 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  have hre : ∀ z : ℂ, (1 - (starRingEnd ℂ) z).re = 1 - z.re := by
    intro z; simp [Complex.sub_re, Complex.conj_re]
  set S := (xi_zeros_finite_ball (1 / 2) R).toFinset.filter (fun ρ => ρ.re ≠ 1 / 2) with hS
  have hmem : ∀ ρ ∈ S, (1 - (starRingEnd ℂ) ρ) ∈ S := by
    intro ρ hρ
    rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨⟨hball, hz⟩, hoff⟩ := hρ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq] at hball ⊢
      rw [show (1 - (starRingEnd ℂ) ρ) - 1 / 2 = -((starRingEnd ℂ) (ρ - 1 / 2)) by
        rw [map_sub, hc12]; ring, norm_neg, Complex.norm_conj]; exact hball
    · rw [hrefl ρ, xi_conj, xi_one_sub, hz, map_zero]
    · rw [hre]; intro h; apply hoff; linarith
  have hzmod : ((∑ ρ ∈ S, (analyticOrderAt xi ρ).toNat : ℕ) : ZMod 2) = 0 := by
    push_cast
    refine Finset.sum_involution (fun ρ _ => 1 - (starRingEnd ℂ) ρ) ?_ ?_ hmem ?_
    · intro ρ _
      have hord : analyticOrderAt xi (1 - (starRingEnd ℂ) ρ) = analyticOrderAt xi ρ := by
        rw [hrefl ρ, xi_orderAt_conj, xi_orderAt_one_sub]
      rw [hord]; exact CharTwo.add_self_eq_zero _
    · intro ρ hρ _ heq
      rw [hS, Finset.mem_filter] at hρ
      apply hρ.2
      have := congrArg Complex.re heq
      rw [hre] at this; linarith
    · intro ρ _; simp only [map_sub, map_one, Complex.conj_conj]; ring
  obtain ⟨c, hc⟩ := (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp hzmod
  exact ⟨c, by omega⟩

/-- **Generic ξ-zeros come in Klein-four tuples: their multiplicity-sum is divisible by 4.**  A zero
off *both* symmetry axes (`Re ≠ ½` and `Im ≠ 0`) has a four-element orbit `{ρ, 1−ρ, conj ρ, 1−conj ρ}`
under the Klein-four group generated by the functional-equation reflection `ρ↦1−ρ` and conjugation
`ρ↦conj ρ`, all zeros of equal multiplicity.  So the total order of the off-both-axes zeros of `ξ` in a
`½`-centered ball is divisible by `4`: conjugation halves it onto the upper half, where the
critical-line reflection halves it again. -/
theorem xi_generic_multiplicity_div_four_ball (R : ℝ) :
    4 ∣ ∑ ρ ∈ (xi_zeros_finite_ball (1 / 2) R).toFinset.filter
        (fun ρ => ρ.re ≠ 1 / 2 ∧ ρ.im ≠ 0), (analyticOrderAt xi ρ).toNat := by
  have hrefl : ∀ z : ℂ, (1 : ℂ) - (starRingEnd ℂ) z = (starRingEnd ℂ) (1 - z) := by
    intro z; rw [map_sub, map_one]
  have hc12 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  have hre : ∀ z : ℂ, (1 - (starRingEnd ℂ) z).re = 1 - z.re := by
    intro z; simp [Complex.sub_re, Complex.conj_re]
  set S := (xi_zeros_finite_ball (1 / 2) R).toFinset.filter
      (fun ρ => ρ.re ≠ 1 / 2 ∧ ρ.im ≠ 0) with hS
  set Sp := S.filter (fun ρ => 0 < ρ.im) with hSp
  have hconj_mem : ∀ ρ ∈ S.filter (fun ρ => ¬ 0 < ρ.im), (starRingEnd ℂ) ρ ∈ Sp := by
    intro ρ hρ
    simp only [hSp, hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨⟨⟨hball, hz⟩, hoff, hnz⟩, hnp⟩ := hρ
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq] at hball ⊢
      rw [show (starRingEnd ℂ) ρ - 1 / 2 = (starRingEnd ℂ) (ρ - 1 / 2) by rw [map_sub, hc12],
        Complex.norm_conj]; exact hball
    · rw [xi_conj, hz, map_zero]
    · rw [Complex.conj_re]; exact hoff
    · rw [Complex.conj_im]; simpa using hnz
    · rw [Complex.conj_im]
      have : ρ.im < 0 := lt_of_le_of_ne (not_lt.mp hnp) hnz
      linarith
  have hhalves : (∑ ρ ∈ S.filter (fun ρ => ¬ 0 < ρ.im), (analyticOrderAt xi ρ).toNat)
      = ∑ ρ ∈ Sp, (analyticOrderAt xi ρ).toNat := by
    refine Finset.sum_nbij' (fun ρ => (starRingEnd ℂ) ρ) (fun ρ => (starRingEnd ℂ) ρ) hconj_mem
      ?_ ?_ ?_ ?_
    · intro ρ hρ
      simp only [hSp, hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
      obtain ⟨⟨⟨hball, hz⟩, hoff, hnz⟩, hp⟩ := hρ
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · rw [Metric.mem_ball, Complex.dist_eq] at hball ⊢
        rw [show (starRingEnd ℂ) ρ - 1 / 2 = (starRingEnd ℂ) (ρ - 1 / 2) by rw [map_sub, hc12],
          Complex.norm_conj]; exact hball
      · rw [xi_conj, hz, map_zero]
      · rw [Complex.conj_re]; exact hoff
      · rw [Complex.conj_im]; simpa using hnz
      · rw [Complex.conj_im]; simp only [not_lt]; linarith
    · intro ρ _; simp
    · intro ρ _; simp
    · intro ρ _; rw [xi_orderAt_conj]
  have hmem : ∀ ρ ∈ Sp, (1 - (starRingEnd ℂ) ρ) ∈ Sp := by
    intro ρ hρ
    simp only [hSp, hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨⟨⟨hball, hz⟩, hoff, hnz⟩, hp⟩ := hρ
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq] at hball ⊢
      rw [show (1 - (starRingEnd ℂ) ρ) - 1 / 2 = -((starRingEnd ℂ) (ρ - 1 / 2)) by
        rw [map_sub, hc12]; ring, norm_neg, Complex.norm_conj]; exact hball
    · rw [hrefl ρ, xi_conj, xi_one_sub, hz, map_zero]
    · rw [hre]; intro h; apply hoff; linarith
    · rw [show (1 - (starRingEnd ℂ) ρ).im = ρ.im by simp [Complex.sub_im, Complex.conj_im]]
      exact hnz
    · rw [show (1 - (starRingEnd ℂ) ρ).im = ρ.im by simp [Complex.sub_im, Complex.conj_im]]
      exact hp
  have heven : Even (∑ ρ ∈ Sp, (analyticOrderAt xi ρ).toNat) := by
    have hzmod : ((∑ ρ ∈ Sp, (analyticOrderAt xi ρ).toNat : ℕ) : ZMod 2) = 0 := by
      push_cast
      refine Finset.sum_involution (fun ρ _ => 1 - (starRingEnd ℂ) ρ) ?_ ?_ hmem ?_
      · intro ρ _
        have hord : analyticOrderAt xi (1 - (starRingEnd ℂ) ρ) = analyticOrderAt xi ρ := by
          rw [hrefl ρ, xi_orderAt_conj, xi_orderAt_one_sub]
        rw [hord]; exact CharTwo.add_self_eq_zero _
      · intro ρ hρ _ heq
        rw [hSp, hS, Finset.mem_filter, Finset.mem_filter] at hρ
        apply hρ.1.2.1
        have := congrArg Complex.re heq
        rw [hre] at this; linarith
      · intro ρ _; simp only [map_sub, map_one, Complex.conj_conj]; ring
    obtain ⟨c, hc⟩ := (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp hzmod
    exact ⟨c, by omega⟩
  obtain ⟨k, hk⟩ := heven
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun ρ => 0 < ρ.im)
    (fun ρ => (analyticOrderAt xi ρ).toNat)
  rw [← hSp, hhalves] at hsplit
  exact ⟨k, by omega⟩

end

end RHTower
