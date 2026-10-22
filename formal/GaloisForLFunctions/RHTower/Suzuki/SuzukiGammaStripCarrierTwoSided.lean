import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaStripCarrierIntegrability

/-!
# Two-sided power bounds for the Suzuki Gamma strip carrier

On the shifted frequency line `z = x + iσ` the squared modulus of the scalar Gamma propagator

`z^{-1/2}[Γ(1+iz)/Γ(1-iz)]^{1/2}`

is `suzukiGammaStripNormSq σ x`.  The vertical Gamma-ratio theorem pins its exact tail exponent
`1 + 2σ = 2p`, and the density is continuous and strictly positive everywhere on the line.  Hence it
is trapped between two multiples of `(1+|x|)^{-2p}`:

`c (1+|x|)^{-(1+2σ)} ≤ suzukiGammaStripNormSq σ x ≤ C (1+|x|)^{-(1+2σ)}`.

The upper half is the propagator bound and the lower half is the bound on the inverse propagator;
together they are the literal content of the exact Gamma quotient on a shifted line.  The two are
obtained from the same asymptotic because the density is even in the height, by the conjugation
symmetry of the Gamma function on a vertical line.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem strip_gamma_ne_zero {a x : ℝ} (ha : 0 < a) :
    Complex.Gamma ((a : ℂ) + (x : ℂ) * I) ≠ 0 := by
  refine Complex.Gamma_ne_zero ?_
  intro n h
  have hre := congrArg Complex.re h
  simp at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem strip_line_ne_zero {σ : ℝ} (hσ0 : 0 < σ) (x : ℝ) :
    ‖(x : ℂ) + (σ : ℂ) * I‖ ≠ 0 := by
  intro h
  rw [norm_eq_zero] at h
  have him := congrArg Complex.im h
  simp at him
  linarith

theorem suzukiGammaStripNormSq_pos {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    0 < suzukiGammaStripNormSq σ x := by
  have hnum : 0 < ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * I)‖ :=
    norm_pos_iff.mpr (strip_gamma_ne_zero (by linarith))
  have hden : 0 < ‖Complex.Gamma (((1 + σ : ℝ) : ℂ) + (x : ℂ) * I)‖ :=
    norm_pos_iff.mpr (strip_gamma_ne_zero (by linarith))
  have hline : 0 < ‖(x : ℂ) + (σ : ℂ) * I‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm (strip_line_ne_zero hσ0 x))
  rw [suzukiGammaStripNormSq]
  positivity

/-- **`(3)`: the exact Gamma quotient traps the strip carrier between two powers.**  The
upper bound is the propagator estimate and the lower bound is the inverse-propagator estimate, both
with the sharp exponent `2p = 1 + 2σ`. -/
theorem exists_twoSided_suzukiGammaStripNormSq {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ,
      c * (1 + |x|) ^ (-(1 + 2 * σ)) ≤ suzukiGammaStripNormSq σ x ∧
        suzukiGammaStripNormSq σ x ≤ C * (1 + |x|) ^ (-(1 + 2 * σ)) := by
  set a : ℝ := 1 + 2 * σ with hadef
  have ha : 0 < a := by rw [hadef]; linarith
  set f : ℝ → ℝ := suzukiGammaStripNormSq σ with hfdef
  have hfpos : ∀ x : ℝ, 0 < f x := fun x => suzukiGammaStripNormSq_pos hσ0 hσ1 x
  have hfcont : Continuous f := continuous_suzukiGammaStripNormSq hσ0 hσ1
  have hfeven : ∀ x : ℝ, f (-x) = f x := fun x => suzukiGammaStripNormSq_neg σ x
  -- tail control from the exact vertical exponent
  have htend : Tendsto (fun x : ℝ => f x * x ^ a) atTop (nhds 1) :=
    suzukiGammaStripNormSq_rpow_tendsto (σ := σ) hσ0.le hσ1
  have htail : ∀ᶠ x : ℝ in atTop, f x * x ^ a ∈ Ioo (1 / 2 : ℝ) 2 :=
    htend.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨X₁, hX₁⟩ := mem_atTop_sets.mp (htail.and (eventually_ge_atTop (1 : ℝ)))
  set X : ℝ := max X₁ 1 with hXdef
  have hX1 : (1 : ℝ) ≤ X := le_max_right _ _
  have hXtail : ∀ x : ℝ, X ≤ x → 1 / 2 < f x * x ^ a ∧ f x * x ^ a < 2 := by
    intro x hx
    exact (hX₁ x (le_trans (le_max_left X₁ 1) hx)).1
  -- compact control on the collar
  obtain ⟨x₀, hx₀mem, hx₀min⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (by linarith : (0 : ℝ) ≤ X))
      hfcont.continuousOn
  obtain ⟨x₁, hx₁mem, hx₁max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith : (0 : ℝ) ≤ X))
      hfcont.continuousOn
  set m : ℝ := f x₀ with hmdef
  set Mc : ℝ := f x₁ with hMdef
  have hm : 0 < m := hfpos x₀
  have hM : 0 < Mc := hfpos x₁
  refine ⟨min (1 / 2) m, max (2 * 2 ^ a) (Mc * (1 + X) ^ a), by positivity, ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  intro x
  -- reduce to the nonnegative ray
  have hkey : ∀ y : ℝ, 0 ≤ y →
      min (1 / 2) m * (1 + y) ^ (-a) ≤ f y ∧
        f y ≤ max (2 * 2 ^ a) (Mc * (1 + X) ^ a) * (1 + y) ^ (-a) := by
    intro y hy
    have hy1 : (0 : ℝ) < 1 + y := by linarith
    have hg : 0 < (1 + y) ^ (-a) := Real.rpow_pos_of_pos hy1 _
    rcases le_or_gt y X with hyX | hyX
    · -- the collar
      have hmin : m ≤ f y := hx₀min ⟨hy, hyX⟩
      have hmax : f y ≤ Mc := hx₁max ⟨hy, hyX⟩
      constructor
      · have hle1 : (1 + y) ^ (-a) ≤ 1 := by
          calc (1 + y) ^ (-a) ≤ (1 : ℝ) ^ (-a) :=
                Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith) (by linarith)
            _ = 1 := Real.one_rpow _
        calc min (1 / 2) m * (1 + y) ^ (-a) ≤ m * (1 + y) ^ (-a) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hg.le
          _ ≤ m * 1 := mul_le_mul_of_nonneg_left hle1 hm.le
          _ = m := mul_one m
          _ ≤ f y := hmin
      · have hge : (1 + X) ^ (-a) ≤ (1 + y) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos hy1 (by linarith) (by linarith)
        have hmul : Mc ≤ Mc * (1 + X) ^ a * (1 + X) ^ (-a) := by
          rw [mul_assoc, ← Real.rpow_add (by linarith : (0 : ℝ) < 1 + X)]
          simp
        calc f y ≤ Mc := hmax
          _ ≤ Mc * (1 + X) ^ a * (1 + X) ^ (-a) := hmul
          _ ≤ Mc * (1 + X) ^ a * (1 + y) ^ (-a) :=
              mul_le_mul_of_nonneg_left hge (by positivity)
          _ ≤ max (2 * 2 ^ a) (Mc * (1 + X) ^ a) * (1 + y) ^ (-a) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hg.le
    · -- the tail
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by linarith) hyX.le
      have hyge1 : (1 : ℝ) ≤ y := le_trans hX1 hyX.le
      obtain ⟨hlow, hhigh⟩ := hXtail y hyX.le
      have hpow : 0 < y ^ a := Real.rpow_pos_of_pos hy0 _
      have hinv : y ^ (-a) = (y ^ a)⁻¹ := by
        rw [Real.rpow_neg hy0.le]
      have hcmp1 : (1 + y) ^ (-a) ≤ y ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hy0 (by linarith) (by linarith)
      have hcmp2 : y ^ (-a) ≤ 2 ^ a * (1 + y) ^ (-a) := by
        have h2y : (1 : ℝ) + y ≤ 2 * y := by linarith
        have hstep : (2 * y) ^ (-a) ≤ (1 + y) ^ (-a) :=
          Real.rpow_le_rpow_of_nonpos hy1 h2y (by linarith)
        have hsplit : (2 * y) ^ (-a) = 2 ^ (-a) * y ^ (-a) :=
          Real.mul_rpow (by norm_num) hy0.le
        have h2a : (0 : ℝ) < 2 ^ a := Real.rpow_pos_of_pos (by norm_num) _
        have h2inv : (2 : ℝ) ^ (-a) = (2 ^ a)⁻¹ := Real.rpow_neg (by norm_num) _
        rw [hsplit, h2inv] at hstep
        calc y ^ (-a) = 2 ^ a * ((2 ^ a)⁻¹ * y ^ (-a)) := by
              field_simp
          _ ≤ 2 ^ a * (1 + y) ^ (-a) := mul_le_mul_of_nonneg_left hstep h2a.le
      constructor
      · have : 1 / 2 * y ^ (-a) ≤ f y := by
          rw [hinv, ← div_eq_mul_inv, div_le_iff₀ hpow]
          linarith
        calc min (1 / 2) m * (1 + y) ^ (-a) ≤ 1 / 2 * (1 + y) ^ (-a) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hg.le
          _ ≤ 1 / 2 * y ^ (-a) := by
              refine mul_le_mul_of_nonneg_left hcmp1 (by norm_num)
          _ ≤ f y := this
      · have hup : f y ≤ 2 * y ^ (-a) := by
          rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hpow]
          linarith
        calc f y ≤ 2 * y ^ (-a) := hup
          _ ≤ 2 * (2 ^ a * (1 + y) ^ (-a)) :=
              mul_le_mul_of_nonneg_left hcmp2 (by norm_num)
          _ = 2 * 2 ^ a * (1 + y) ^ (-a) := by ring
          _ ≤ max (2 * 2 ^ a) (Mc * (1 + X) ^ a) * (1 + y) ^ (-a) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hg.le
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact hkey x hx
  · have hxabs : |x| = -x := abs_of_neg hx
    rw [hxabs, ← hfeven x]
    exact hkey (-x) (by linarith)

end GaloisForLFunctions.RHTower
