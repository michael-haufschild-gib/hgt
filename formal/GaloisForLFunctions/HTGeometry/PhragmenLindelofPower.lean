import GaloisForLFunctions.HTGeometry.StripLineBound

/-!
# Phragmén--Lindelöf with a power weight

The convexity step of Burnol's Theorem 4.8 is the following packaging of mathlib's
`PhragmenLindelof.vertical_strip`: if an entire function is bounded by `C·‖s-c₀‖^ν` on the two
edges of a vertical strip lying strictly right of `c₀`, and has at worst polynomial vertical growth
inside, then the same bound holds throughout the strip.

Dividing by `(s-c₀)^ν` turns the edge bounds into genuine boundedness; the polynomial growth is
dominated by `exp(B·exp(c|t|))` with `B = N/c`, since `1 + x ≤ exp x`.

## Main results

* `norm_cpow_ofReal_exponent`
* `norm_le_mul_rpow_of_vertical_strip`
-/

noncomputable section

open Complex Filter Topology Asymptotics Set

namespace GaloisForLFunctions.HTGeometry

theorem norm_cpow_ofReal_exponent {z : ℂ} (hz : z ≠ 0) (ν : ℝ) :
    ‖z ^ ((ν : ℝ) : ℂ)‖ = ‖z‖ ^ ν := by
  rw [Complex.norm_cpow_of_ne_zero hz]
  simp

theorem rpow_le_exp_mul {x N : ℝ} (hx : 0 ≤ x) (hN : 0 ≤ N) :
    (1 + x) ^ N ≤ Real.exp (N * x) := by
  have h1 : (1 : ℝ) + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  calc (1 + x) ^ N ≤ (Real.exp x) ^ N :=
        Real.rpow_le_rpow (by linarith) h1 hN
    _ = Real.exp (N * x) := by
        rw [← Real.exp_mul]
        ring_nf

/-- **Phragmén--Lindelöf with a power weight.** -/
theorem norm_le_mul_rpow_of_vertical_strip {F : ℂ → ℂ} {A B ν c₀ CA CB C N : ℝ}
    (hAB : A < B) (hν : 0 ≤ ν) (hc₀ : c₀ < A) (hF : Differentiable ℂ F)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hgrow : ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖F s‖ ≤ C * (1 + |s.im|) ^ N)
    (hA : ∀ z : ℂ, z.re = A → ‖F z‖ ≤ CA * ‖z - (c₀ : ℂ)‖ ^ ν)
    (hB : ∀ z : ℂ, z.re = B → ‖F z‖ ≤ CB * ‖z - (c₀ : ℂ)‖ ^ ν) :
    ∀ s : ℂ, A ≤ s.re → s.re ≤ B → ‖F s‖ ≤ max CA CB * ‖s - (c₀ : ℂ)‖ ^ ν := by
  have hne : ∀ s : ℂ, A ≤ s.re → s - (c₀ : ℂ) ≠ 0 := by
    intro s hs h
    have hre : (s - (c₀ : ℂ)).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    linarith
  have hlow : ∀ s : ℂ, A ≤ s.re → A - c₀ ≤ ‖s - (c₀ : ℂ)‖ := by
    intro s hs
    calc A - c₀ ≤ (s - (c₀ : ℂ)).re := by
          rw [Complex.sub_re, Complex.ofReal_re]; linarith
      _ ≤ |(s - (c₀ : ℂ)).re| := le_abs_self _
      _ ≤ ‖s - (c₀ : ℂ)‖ := Complex.abs_re_le_norm _
  have hAc₀ : 0 < A - c₀ := by linarith
  set g : ℂ → ℂ := fun s => F s / (s - (c₀ : ℂ)) ^ ((ν : ℝ) : ℂ) with hgdef
  -- holomorphy on the closed strip
  have hclosed : IsClosed (Complex.re ⁻¹' Icc A B) :=
    isClosed_Icc.preimage Complex.continuous_re
  have hsub : closure (Complex.re ⁻¹' Ioo A B) ⊆ Complex.re ⁻¹' Icc A B := by
    refine closure_minimal ?_ hclosed
    intro z hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hgdiff : DifferentiableOn ℂ g (closure (Complex.re ⁻¹' Ioo A B)) := by
    intro z hz
    have hzA : A ≤ z.re := (hsub hz).1
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (hF z).div ?_ (fun h => hne z hzA ((Complex.cpow_eq_zero_iff _ _).1 h).1)
    refine DifferentiableAt.cpow ?_ (differentiableAt_const _) ?_
    · exact differentiableAt_id.sub (differentiableAt_const _)
    · left
      have hre : 0 < (z - (c₀ : ℂ)).re := by
        rw [Complex.sub_re, Complex.ofReal_re]
        linarith
      exact hre
  refine fun s hs hsb => ?_
  have hsne := hne s hs
  have hpow : (0 : ℝ) < ‖s - (c₀ : ℂ)‖ ^ ν :=
    Real.rpow_pos_of_pos (norm_pos_iff.2 hsne) ν
  have hkey : ‖g s‖ ≤ max CA CB := by
    refine PhragmenLindelof.vertical_strip (a := A) (b := B) (C := max CA CB)
      (hgdiff.diffContOnCl) ?_ ?_ ?_ hs hsb
    · refine ⟨Real.pi / (2 * (B - A)), by
        have hpi : 0 < Real.pi := Real.pi_pos
        have : 0 < B - A := by linarith
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith, N / (Real.pi / (2 * (B - A))), ?_⟩
      set c : ℝ := Real.pi / (2 * (B - A)) with hcdef
      have hc0 : 0 < c := by
        rw [hcdef]
        have : 0 < B - A := by linarith
        positivity
      refine Asymptotics.isBigO_iff.2 ⟨C / (A - c₀) ^ ν, ?_⟩
      refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall ?_)
      intro z hz
      have hzA : A ≤ z.re := le_of_lt hz.1
      have hzB : z.re ≤ B := le_of_lt hz.2
      have hznorm : (0 : ℝ) < ‖z - (c₀ : ℂ)‖ := norm_pos_iff.2 (hne z hzA)
      have hlowz : (A - c₀) ^ ν ≤ ‖z - (c₀ : ℂ)‖ ^ ν :=
        Real.rpow_le_rpow hAc₀.le (hlow z hzA) hν
      have hlowpos : (0 : ℝ) < (A - c₀) ^ ν := Real.rpow_pos_of_pos hAc₀ ν
      have hgz : ‖g z‖ ≤ C * (1 + |z.im|) ^ N / (A - c₀) ^ ν := by
        rw [hgdef]
        simp only
        rw [norm_div, norm_cpow_ofReal_exponent (hne z hzA)]
        gcongr
        exact hgrow z hzA hzB
      refine hgz.trans ?_
      have hexp : (1 + |z.im|) ^ N ≤ Real.exp (N * |z.im|) :=
        rpow_le_exp_mul (abs_nonneg _) hN
      have hexp2 : Real.exp (N * |z.im|)
          ≤ Real.exp ((N / c) * Real.exp (c * |z.im|)) := by
        refine Real.exp_le_exp.2 ?_
        have h1 : 1 + c * |z.im| ≤ Real.exp (c * |z.im|) := by
          have := Real.add_one_le_exp (c * |z.im|)
          linarith
        have hNc : 0 ≤ N / c := by positivity
        have h2 : (N / c) * (1 + c * |z.im|) ≤ (N / c) * Real.exp (c * |z.im|) :=
          mul_le_mul_of_nonneg_left h1 hNc
        have h3 : (N / c) * (1 + c * |z.im|) = N / c + N * |z.im| := by
          field_simp
        rw [h3] at h2
        linarith
      have hnormexp : ‖Real.exp ((N / c) * Real.exp (c * |z.im|))‖
          = Real.exp ((N / c) * Real.exp (c * |z.im|)) := by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [hnormexp]
      calc C * (1 + |z.im|) ^ N / (A - c₀) ^ ν
          ≤ C * Real.exp ((N / c) * Real.exp (c * |z.im|)) / (A - c₀) ^ ν := by
            have hb : (1 + |z.im|) ^ N ≤ Real.exp ((N / c) * Real.exp (c * |z.im|)) :=
              le_trans hexp hexp2
            gcongr
        _ = C / (A - c₀) ^ ν * Real.exp ((N / c) * Real.exp (c * |z.im|)) := by ring
    · intro z hz
      have hzne := hne z (le_of_eq hz.symm)
      rw [hgdef]
      simp only
      rw [norm_div, norm_cpow_ofReal_exponent hzne, div_le_iff₀
        (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν)]
      exact le_trans (hA z hz) (by
        refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
        exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν).le)
    · intro z hz
      have hzA : A ≤ z.re := by rw [hz]; linarith
      have hzne := hne z hzA
      rw [hgdef]
      simp only
      rw [norm_div, norm_cpow_ofReal_exponent hzne, div_le_iff₀
        (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν)]
      exact le_trans (hB z hz) (by
        refine mul_le_mul_of_nonneg_right (le_max_right _ _) ?_
        exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hzne) ν).le)
  rw [hgdef] at hkey
  simp only at hkey
  rw [norm_div, norm_cpow_ofReal_exponent hsne, div_le_iff₀ hpow] at hkey
  exact hkey

end GaloisForLFunctions.HTGeometry

end
