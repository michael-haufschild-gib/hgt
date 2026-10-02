import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Exact triangular inversion on a finite Fourier annulus

Forward dilations cannot return a discarded high-frequency component to the
annulus. Their compressions form a multiplicative semigroup and vanish when
the transported lower gap crosses the upper band. Every scalar-shifted local
factor is therefore invertible, without any small-norm hypothesis.
-/

noncomputable section

namespace RHTower

private theorem reciprocal_scale_le {a r : ℝ} (ha : 0 ≤ a) (hr : 1 ≤ r) :
    r⁻¹ * a ≤ a := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hid : r * (r⁻¹ * a) = a := by
    rw [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
  nlinarith

private theorem fourierCutoffs_commute (b c : ℝ) :
    evenFourierCutoff b * evenFourierCutoff c =
      evenFourierCutoff c * evenFourierCutoff b := by
  rcases le_total b c with h | h
  · rw [evenFourierCutoff_mul_of_le b c h, evenFourierCutoff_mul_of_le_rev b c h]
  · rw [evenFourierCutoff_mul_of_le c b h, evenFourierCutoff_mul_of_le_rev c b h]

private theorem upperCutoff_dilation_absorb (c r : ℝ) (hc : 0 ≤ c) (hr : 1 ≤ r) :
    evenFourierCutoff c * evenDilationCLM r (zero_lt_one.trans_le hr) *
        evenFourierCutoff c =
      evenFourierCutoff c * evenDilationCLM r (zero_lt_one.trans_le hr) := by
  rw [evenFourierCutoff_mul_evenDilationCLM, mul_assoc,
    evenFourierCutoff_mul_of_le _ _ (reciprocal_scale_le hc hr)]

private theorem lowerCutoff_dilation_gap (b r : ℝ) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    evenFourierCutoff b * evenDilationCLM r (zero_lt_one.trans_le hr) *
      (1 - evenFourierCutoff b) = 0 := by
  rw [evenFourierCutoff_mul_evenDilationCLM, mul_assoc, mul_sub, mul_one,
    evenFourierCutoff_mul_of_le _ _ (reciprocal_scale_le hb hr), sub_self, mul_zero]

/-- The actual forward dilation between the lower gap and upper cutoff. -/
def evenAnnularForwardDilation (b c r : ℝ) (hr : 0 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  evenFourierCutoff c * evenDilationCLM r hr * (1 - evenFourierCutoff b)

theorem evenFourierCutoff_mul_evenAnnularForwardDilation
    (b c r : ℝ) (hb : 0 ≤ b) (hr : 1 ≤ r) :
    evenFourierCutoff b * evenAnnularForwardDilation b c r (zero_lt_one.trans_le hr) = 0 := by
  unfold evenAnnularForwardDilation
  calc
    evenFourierCutoff b *
        (evenFourierCutoff c * evenDilationCLM r (zero_lt_one.trans_le hr) *
          (1 - evenFourierCutoff b)) =
        (evenFourierCutoff b * evenFourierCutoff c) *
          evenDilationCLM r (zero_lt_one.trans_le hr) * (1 - evenFourierCutoff b) := by
            simp only [mul_assoc]
    _ = evenFourierCutoff c *
        (evenFourierCutoff b * evenDilationCLM r (zero_lt_one.trans_le hr) *
          (1 - evenFourierCutoff b)) := by
            rw [fourierCutoffs_commute b c]
            simp only [mul_assoc]
    _ = 0 := by rw [lowerCutoff_dilation_gap b r hb hr, mul_zero]

/-- No discarded high-frequency term can return under a second forward dilation. -/
theorem evenAnnularForwardDilation_mul (b c r s : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    evenAnnularForwardDilation b c r (zero_lt_one.trans_le hr) *
      evenAnnularForwardDilation b c s (zero_lt_one.trans_le hs) =
    evenAnnularForwardDilation b c (r * s)
      (mul_pos (zero_lt_one.trans_le hr) (zero_lt_one.trans_le hs)) := by
  have hgap : (1 - evenFourierCutoff b) *
      evenAnnularForwardDilation b c s (zero_lt_one.trans_le hs) =
      evenAnnularForwardDilation b c s (zero_lt_one.trans_le hs) := by
    rw [sub_mul, one_mul, evenFourierCutoff_mul_evenAnnularForwardDilation b c s hb hs,
      sub_zero]
  change (evenFourierCutoff c * evenDilationCLM r (zero_lt_one.trans_le hr) *
    (1 - evenFourierCutoff b)) * _ = _
  rw [mul_assoc, hgap]
  unfold evenAnnularForwardDilation
  calc
    (evenFourierCutoff c * evenDilationCLM r (zero_lt_one.trans_le hr)) *
        (evenFourierCutoff c * evenDilationCLM s (zero_lt_one.trans_le hs) *
          (1 - evenFourierCutoff b)) =
        (evenFourierCutoff c * evenDilationCLM r (zero_lt_one.trans_le hr) *
          evenFourierCutoff c) * evenDilationCLM s (zero_lt_one.trans_le hs) *
            (1 - evenFourierCutoff b) := by simp only [mul_assoc]
    _ = evenFourierCutoff c *
        (evenDilationCLM r (zero_lt_one.trans_le hr) *
          evenDilationCLM s (zero_lt_one.trans_le hs)) * (1 - evenFourierCutoff b) := by
            rw [upperCutoff_dilation_absorb c r hc hr]
            simp only [mul_assoc]
    _ = _ := by rw [evenDilationCLM_mul]

/-- Identification with compression by the actual annular projection. -/
theorem evenAnnularForwardDilation_eq_compression (b c r : ℝ)
    (hb : 0 ≤ b) (hbc : b ≤ c) (hr : 1 ≤ r) :
    evenAnnularForwardDilation b c r (zero_lt_one.trans_le hr) =
      (evenFourierCutoff c - evenFourierCutoff b) *
        evenDilationCLM r (zero_lt_one.trans_le hr) *
          (evenFourierCutoff c - evenFourierCutoff b) := by
  have hleft : (1 - evenFourierCutoff b) * evenFourierCutoff c =
      evenFourierCutoff c - evenFourierCutoff b := by
    rw [sub_mul, one_mul, evenFourierCutoff_mul_of_le b c hbc]
  have hright : evenFourierCutoff c * (1 - evenFourierCutoff b) =
      evenFourierCutoff c - evenFourierCutoff b := by
    rw [mul_sub, mul_one, evenFourierCutoff_mul_of_le_rev b c hbc]
  symm
  calc
    (evenFourierCutoff c - evenFourierCutoff b) *
        evenDilationCLM r (zero_lt_one.trans_le hr) *
          (evenFourierCutoff c - evenFourierCutoff b) =
        ((1 - evenFourierCutoff b) * evenFourierCutoff c) *
          evenDilationCLM r (zero_lt_one.trans_le hr) *
            (evenFourierCutoff c * (1 - evenFourierCutoff b)) := by rw [hleft, hright]
    _ = (1 - evenFourierCutoff b) *
        (evenFourierCutoff c * evenDilationCLM r (zero_lt_one.trans_le hr) *
          evenFourierCutoff c) * (1 - evenFourierCutoff b) := by simp only [mul_assoc]
    _ = (1 - evenFourierCutoff b) *
        evenAnnularForwardDilation b c r (zero_lt_one.trans_le hr) := by
      rw [upperCutoff_dilation_absorb c r (hb.trans hbc) hr]
      rfl
    _ = evenAnnularForwardDilation b c r (zero_lt_one.trans_le hr) := by
      rw [sub_mul, one_mul, evenFourierCutoff_mul_evenAnnularForwardDilation b c r hb hr,
        sub_zero]

/-- The finite annulus has no surviving component once the lower gap crosses its upper edge. -/
theorem evenAnnularForwardDilation_eq_zero (b c r : ℝ) (hr : 0 < r) (hcross : c ≤ r * b) :
    evenAnnularForwardDilation b c r hr = 0 := by
  have hscale : r⁻¹ * c ≤ b := by
    have hid : r * (r⁻¹ * c) = c := by
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    nlinarith
  unfold evenAnnularForwardDilation
  rw [evenFourierCutoff_mul_evenDilationCLM, mul_assoc, mul_sub, mul_one,
    evenFourierCutoff_mul_of_le _ _ hscale, sub_self, mul_zero]

/-- Every genuinely expanding dilation is nilpotent after finite-annulus compression. -/
theorem isNilpotent_evenAnnularForwardDilation (b c p : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hp : 1 < p) :
    IsNilpotent (evenAnnularForwardDilation b c p (zero_lt_one.trans hp)) := by
  have hpow : ∀ n : ℕ,
      evenAnnularForwardDilation b c p (zero_lt_one.trans hp) ^ (n + 1) =
        evenAnnularForwardDilation b c (p ^ (n + 1))
          (pow_pos (zero_lt_one.trans hp) _) := by
    intro n
    induction n with
    | zero => simp only [Nat.zero_add, pow_one]
    | succ n ih =>
      rw [pow_succ, ih,
        evenAnnularForwardDilation_mul b c (p ^ (n + 1)) p hb.le hc
          (one_le_pow₀ hp.le) hp.le]
      simp only [pow_succ]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c / b) hp
  have hcross : c ≤ p ^ (n + 1) * b := by
    have hcb := (div_lt_iff₀ hb).mp hn
    rw [pow_succ]
    have hpos : 0 < p ^ n * b := mul_pos (pow_pos (zero_lt_one.trans hp) n) hb
    nlinarith
  exact ⟨n + 1, (hpow n).trans (evenAnnularForwardDilation_eq_zero b c
    (p ^ (n + 1)) (pow_pos (zero_lt_one.trans hp) _) hcross)⟩

/-- Exact local inversion for every scalar, including the Euler coefficient `sqrt p`. -/
theorem isUnit_one_sub_smul_evenAnnularForwardDilation (b c p : ℝ)
    (hb : 0 < b) (hc : 0 ≤ c) (hp : 1 < p) (z : ℂ) :
    IsUnit (1 - z • evenAnnularForwardDilation b c p (zero_lt_one.trans hp)) := by
  let W := evenAnnularForwardDilation b c p (zero_lt_one.trans hp)
  have hsmul : ∀ n : ℕ, (z • W) ^ n = z ^ n • W ^ n := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_smul]
    | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih]
      apply ContinuousLinearMap.ext
      intro f
      simp only [_root_.mul_apply_eq_comp, _root_.smul_apply, map_smul, smul_smul, mul_comm]
  apply IsNilpotent.isUnit_one_sub
  obtain ⟨n, hn⟩ := isNilpotent_evenAnnularForwardDilation b c p hb hc hp
  refine ⟨n, ?_⟩
  change (z • W) ^ n = 0
  rw [hsmul, hn]
  apply ContinuousLinearMap.ext
  intro f
  change z ^ n • (0 : evenSubspace) = 0
  exact smul_zero _

end RHTower
