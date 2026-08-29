import GaloisForLFunctions.RHTower.PrimeKaramataHead

/-!
# The shell sandwich of the prime Karamata sum

On a shell `(aX, bX]` with `0 < a ≤ b ≤ 1` the weight `F(t) = t^{−α}L(t)` is, after normalisation by
`X^{−α}L(X)`, squeezed between `b^{−α}(1−ε)` and `a^{−α}(1+ε)`: the power factor is monotone and the
slowly varying factor is uniformly close to `1` by Karamata's uniform convergence theorem.  The
prime mass of the shell is `(b−a)X` up to `2εX` by the prime number theorem.  Multiplying the two
gives the shell sandwich, the building block of the Riemann sum.
-/

open Filter Topology HTGeometry

namespace RHTower

noncomputable section

theorem tendsto_const_mul_atTop_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ => c * X) atTop atTop :=
  Filter.Tendsto.const_mul_atTop hc tendsto_id

/-- **The shell sandwich.** -/
theorem karamata_shell_bounds {α : ℝ} (hα0 : 0 ≤ α) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ X in atTop,
      primeLogSum (rvPrimeWeight α L) (a * X) (b * X)
          ≤ (a ^ (-α) * (1 + ε) * ((b - a) + 2 * ε)) * (X ^ (1 - α) * L X)
        ∧ (b ^ (-α) * (1 - ε) * ((b - a) - 2 * ε)) * (X ^ (1 - α) * L X)
          ≤ primeLogSum (rvPrimeWeight α L) (a * X) (b * X) := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have huct := isSlowlyVarying_uniform hL ha (b := b) hε
  have hθa := (tendsto_const_mul_atTop_of_pos ha).eventually
    (chebyshevTheta_eventually_relative hε)
  have hθb := (tendsto_const_mul_atTop_of_pos hb0).eventually
    (chebyshevTheta_eventually_relative hε)
  filter_upwards [huct, hθa, hθb, eventually_gt_atTop (0 : ℝ)] with X hX hXa hXb hX0
  have hLX : 0 < L X := hL.pos _ hX0
  have haX : (0 : ℝ) ≤ a * X := by positivity
  have hfl : ⌊a * X⌋₊ ≤ ⌊b * X⌋₊ := Nat.floor_mono (by nlinarith [hab, hX0.le])
  have hXpow : (0 : ℝ) < X ^ (-α) := Real.rpow_pos_of_pos hX0 _
  have hXpow1 : X ^ (-α) * X = X ^ (1 - α) := by
    have hadd := Real.rpow_add hX0 (-α) 1
    rw [Real.rpow_one] at hadd
    rw [show (1 : ℝ) - α = -α + 1 by ring, hadd]
  -- pointwise weight bounds on the shell
  have hpt : ∀ t : ℝ, a * X < t → t ≤ b * X →
      rvPrimeWeight α L t ≤ a ^ (-α) * X ^ (-α) * ((1 + ε) * L X)
        ∧ b ^ (-α) * X ^ (-α) * ((1 - ε) * L X) ≤ rvPrimeWeight α L t := by
    intro t ht1 ht2
    have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht1
    set c : ℝ := t / X with hc
    have hc0 : 0 < c := by rw [hc]; positivity
    have hca : a < c := by rw [hc, lt_div_iff₀ hX0]; nlinarith [ht1]
    have hcb : c ≤ b := by rw [hc, div_le_iff₀ hX0]; nlinarith [ht2]
    have hcX : c * X = t := by rw [hc]; field_simp
    have hsplit : t ^ (-α) = c ^ (-α) * X ^ (-α) := by
      rw [← hcX, Real.mul_rpow hc0.le hX0.le]
    have hLratio := hX c ⟨hca.le, hcb⟩
    rw [hcX, abs_le] at hLratio
    have hLt : 0 < L t := hL.pos _ ht0
    have hLup : L t ≤ (1 + ε) * L X := by
      have h : L t / L X ≤ 1 + ε := by linarith [hLratio.2]
      rw [div_le_iff₀ hLX] at h
      exact h
    have hLlow : (1 - ε) * L X ≤ L t := by
      have h : 1 - ε ≤ L t / L X := by linarith [hLratio.1]
      rw [le_div_iff₀ hLX] at h
      exact h
    have hpowup : c ^ (-α) ≤ a ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos ha hca.le (by linarith)
    have hpowlow : b ^ (-α) ≤ c ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hc0 hcb (by linarith)
    have hc0' : (0 : ℝ) < c ^ (-α) := Real.rpow_pos_of_pos hc0 _
    have hb0' : (0 : ℝ) < b ^ (-α) := Real.rpow_pos_of_pos hb0 _
    constructor
    · rw [rvPrimeWeight, hsplit]
      have h1 : c ^ (-α) * X ^ (-α) * L t ≤ c ^ (-α) * X ^ (-α) * ((1 + ε) * L X) := by
        exact mul_le_mul_of_nonneg_left hLup (by positivity)
      have h2 : c ^ (-α) * X ^ (-α) * ((1 + ε) * L X)
          ≤ a ^ (-α) * X ^ (-α) * ((1 + ε) * L X) := by
        have hnn : (0 : ℝ) ≤ X ^ (-α) * ((1 + ε) * L X) := by positivity
        nlinarith [hpowup, hnn]
      linarith
    · rw [rvPrimeWeight, hsplit]
      have h1 : b ^ (-α) * X ^ (-α) * ((1 - ε) * L X)
          ≤ c ^ (-α) * X ^ (-α) * ((1 - ε) * L X) := by
        have hnn : (0 : ℝ) ≤ X ^ (-α) * ((1 - ε) * L X) := by
          have : (0 : ℝ) < 1 - ε := by linarith
          positivity
        nlinarith [hpowlow, hnn]
      have h2 : c ^ (-α) * X ^ (-α) * ((1 - ε) * L X) ≤ c ^ (-α) * X ^ (-α) * L t :=
        mul_le_mul_of_nonneg_left hLlow (by positivity)
      linarith
  -- the shell mass
  rw [abs_le] at hXa hXb
  have hmassup : Chebyshev.theta (b * X) - Chebyshev.theta (a * X) ≤ ((b - a) + 2 * ε) * X := by
    have h1 : Chebyshev.theta (b * X) ≤ b * X + ε * (b * X) := by linarith [hXb.2]
    have h2 : a * X - ε * (a * X) ≤ Chebyshev.theta (a * X) := by linarith [hXa.1]
    have hslack : ε * X * (2 - a - b) ≥ 0 := by
      have h3 : (0 : ℝ) ≤ 2 - a - b := by linarith
      positivity
    nlinarith [h1, h2, hslack]
  have hmasslow : ((b - a) - 2 * ε) * X ≤ Chebyshev.theta (b * X) - Chebyshev.theta (a * X) := by
    have h1 : b * X - ε * (b * X) ≤ Chebyshev.theta (b * X) := by linarith [hXb.1]
    have h2 : Chebyshev.theta (a * X) ≤ a * X + ε * (a * X) := by linarith [hXa.2]
    have hslack : ε * X * (2 - a - b) ≥ 0 := by
      have h3 : (0 : ℝ) ≤ 2 - a - b := by linarith
      positivity
    nlinarith [h1, h2, hslack]
  have hmassnn : 0 ≤ Chebyshev.theta (b * X) - Chebyshev.theta (a * X) := by
    have := chebyshevTheta_mono (show a * X ≤ b * X by nlinarith [hab, hX0.le])
    linarith
  have ha0' : (0 : ℝ) < a ^ (-α) := Real.rpow_pos_of_pos ha _
  have hb0' : (0 : ℝ) < b ^ (-α) := Real.rpow_pos_of_pos hb0 _
  constructor
  · have hup := primeLogSum_le (f := rvPrimeWeight α L) haX hfl
      (fun p _ h1 h2 => (hpt p h1 h2).1)
    have hcst : (0 : ℝ) ≤ a ^ (-α) * X ^ (-α) * ((1 + ε) * L X) := by positivity
    have hstep : a ^ (-α) * X ^ (-α) * ((1 + ε) * L X)
        * (Chebyshev.theta (b * X) - Chebyshev.theta (a * X))
        ≤ a ^ (-α) * X ^ (-α) * ((1 + ε) * L X) * (((b - a) + 2 * ε) * X) :=
      mul_le_mul_of_nonneg_left hmassup hcst
    have hid : a ^ (-α) * X ^ (-α) * ((1 + ε) * L X) * (((b - a) + 2 * ε) * X)
        = (a ^ (-α) * (1 + ε) * ((b - a) + 2 * ε)) * (X ^ (1 - α) * L X) := by
      rw [← hXpow1]
      ring
    linarith [hup, hstep, hid.le, hid.ge]
  · have hlow := le_primeLogSum (f := rvPrimeWeight α L) haX hfl
      (fun p _ h1 h2 => (hpt p h1 h2).2)
    have hcst : (0 : ℝ) ≤ b ^ (-α) * X ^ (-α) * ((1 - ε) * L X) := by
      have h1 : (0 : ℝ) < 1 - ε := by linarith
      positivity
    have hstep : b ^ (-α) * X ^ (-α) * ((1 - ε) * L X) * (((b - a) - 2 * ε) * X)
        ≤ b ^ (-α) * X ^ (-α) * ((1 - ε) * L X)
          * (Chebyshev.theta (b * X) - Chebyshev.theta (a * X)) :=
      mul_le_mul_of_nonneg_left hmasslow hcst
    have hid : b ^ (-α) * X ^ (-α) * ((1 - ε) * L X) * (((b - a) - 2 * ε) * X)
        = (b ^ (-α) * (1 - ε) * ((b - a) - 2 * ε)) * (X ^ (1 - α) * L X) := by
      rw [← hXpow1]
      ring
    linarith [hlow, hstep, hid.le, hid.ge]

end

end RHTower
