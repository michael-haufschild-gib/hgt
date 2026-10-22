import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussEulerSummation

/-!
# Global Gauss summation by finite contiguous transport

Gauss's Gamma quotient is first proved in the Euler-integral chamber.  Exact contiguous
coboundaries then transport arbitrary nonresonant parameters with positive Gauss gap into that
chamber and back.  The only growth input is an explicit Archimedean natural shift.
-/

open Complex Nat Polynomial Filter Topology Set MeasureTheory

namespace RHTower
noncomputable section

def GaussSummationFormula (a b c : ℂ) : Prop :=
  ∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n =
    Complex.Gamma c * Complex.Gamma (c - a - b) /
      (Complex.Gamma (c - a) * Complex.Gamma (c - b))

theorem Gamma_ne_zero_of_avoidsNegNat (z : ℂ)
    (hz : ∀ k : ℕ, (k : ℂ) ≠ -z) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro k hk
  apply hz k
  linear_combination hk

theorem gaussSummationFormula_of_shift_b_c
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hca : ∀ k : ℕ, (k : ℂ) ≠ -(c - a))
    (hgap : 0 < (c - a - b).re)
    (hshift : GaussSummationFormula a (b + 1) (c + 1)) :
    GaussSummationFormula a b c := by
  rw [GaussSummationFormula] at hshift ⊢
  rw [← tsum_ordinaryHypergeometricCoefficient_shift_b_c_of_re_gap_pos
    a b c ha hb hc hgap]
  rw [hshift]
  have hc0 : c ≠ 0 := by
    intro hz
    apply hc 0
    simp [hz]
  have hca0 : c - a ≠ 0 := by
    intro hz
    apply hca 0
    simp [hz]
  rw [show c + 1 - a = (c - a) + 1 by ring,
    Complex.Gamma_add_one c hc0,
    Complex.Gamma_add_one (c - a) hca0]
  have hGc : Complex.Gamma c ≠ 0 := Gamma_ne_zero_of_avoidsNegNat c hc
  have hGca : Complex.Gamma (c - a) ≠ 0 :=
    Gamma_ne_zero_of_avoidsNegNat (c - a) hca
  (field_simp [hGc, hGca]; ring_nf)

theorem gaussSummationFormula_of_shift_a_c
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hcb : ∀ k : ℕ, (k : ℂ) ≠ -(c - b))
    (hgap : 0 < (c - a - b).re)
    (hshift : GaussSummationFormula (a + 1) b (c + 1)) :
    GaussSummationFormula a b c := by
  rw [GaussSummationFormula] at hshift ⊢
  rw [← tsum_ordinaryHypergeometricCoefficient_shift_a_c_of_re_gap_pos
    a b c ha hb hc hgap]
  rw [hshift]
  have hc0 : c ≠ 0 := by
    intro hz
    apply hc 0
    simp [hz]
  have hcb0 : c - b ≠ 0 := by
    intro hz
    apply hcb 0
    simp [hz]
  rw [show c + 1 - b = (c - b) + 1 by ring,
    Complex.Gamma_add_one c hc0,
    Complex.Gamma_add_one (c - b) hcb0]
  have hGc : Complex.Gamma c ≠ 0 := Gamma_ne_zero_of_avoidsNegNat c hc
  have hGcb : Complex.Gamma (c - b) ≠ 0 :=
    Gamma_ne_zero_of_avoidsNegNat (c - b) hcb
  (field_simp [hGc, hGcb]; ring_nf)

theorem avoidsNegNat_add_nat (z : ℂ)
    (hz : ∀ k : ℕ, (k : ℂ) ≠ -z) (n : ℕ) :
    ∀ k : ℕ, (k : ℂ) ≠ -(z + n) := by
  intro k hk
  apply hz (k + n)
  push_cast
  linear_combination hk

theorem gaussSummationFormula_of_shift_b_c_nat
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hca : ∀ k : ℕ, (k : ℂ) ≠ -(c - a))
    (hgap : 0 < (c - a - b).re)
    (n : ℕ)
    (hshift : GaussSummationFormula a (b + n) (c + n)) :
    GaussSummationFormula a b c := by
  induction n generalizing b c with
  | zero => simpa using hshift
  | succ n ih =>
      apply gaussSummationFormula_of_shift_b_c a b c ha hb hc hca hgap
      apply ih (b := b + 1) (c := c + 1)
      · simpa using avoidsNegNat_add_nat b hb 1
      · simpa using avoidsNegNat_add_nat c hc 1
      · simpa [show c + 1 - a = (c - a) + 1 by ring] using
          avoidsNegNat_add_nat (c - a) hca 1
      · have heq : c + 1 - a - (b + 1) = c - a - b := by ring
        simpa only [heq] using hgap
      · convert hshift using 1 <;> push_cast <;> ring

theorem gaussSummationFormula_of_shift_a_c_nat
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hcb : ∀ k : ℕ, (k : ℂ) ≠ -(c - b))
    (hgap : 0 < (c - a - b).re)
    (n : ℕ)
    (hshift : GaussSummationFormula (a + n) b (c + n)) :
    GaussSummationFormula a b c := by
  induction n generalizing a c with
  | zero => simpa using hshift
  | succ n ih =>
      apply gaussSummationFormula_of_shift_a_c a b c ha hb hc hcb hgap
      apply ih (a := a + 1) (c := c + 1)
      · simpa using avoidsNegNat_add_nat a ha 1
      · simpa using avoidsNegNat_add_nat c hc 1
      · simpa [show c + 1 - b = (c - b) + 1 by ring] using
          avoidsNegNat_add_nat (c - b) hcb 1
      · have heq : c + 1 - (a + 1) - b = c - a - b := by ring
        simpa only [heq] using hgap
      · convert hshift using 1 <;> push_cast <;> ring

theorem exists_nat_norm_add_lt_add_of_re_lt (a : ℂ) (r : ℝ)
    (h : a.re < r) :
    ∃ p : ℕ, ‖a + (p : ℂ)‖ < r + p := by
  let d : ℝ := r - a.re
  let M : ℝ := max (-r) ((a.im ^ (2 : ℕ) + a.re ^ (2 : ℕ) - r ^ (2 : ℕ)) / (2 * d))
  obtain ⟨p, hp⟩ := exists_nat_gt M
  refine ⟨p, ?_⟩
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hrp : 0 < r + p := by
    have hM : -r ≤ M := le_max_left _ _
    linarith
  rw [← sq_lt_sq₀ (norm_nonneg _) (le_of_lt hrp), Complex.sq_norm,
    Complex.normSq_apply]
  have hquot : (a.im ^ (2 : ℕ) + a.re ^ (2 : ℕ) - r ^ (2 : ℕ)) / (2 * d) < p := by
    have hM : (a.im ^ (2 : ℕ) + a.re ^ (2 : ℕ) - r ^ (2 : ℕ)) / (2 * d) ≤ M := le_max_right _ _
    linarith
  norm_num [Complex.add_re, Complex.add_im]
  have h2d : 0 < 2 * d := by positivity
  rw [div_lt_iff₀ h2d] at hquot
  dsimp [d] at hquot
  nlinarith

theorem gaussSummation
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hca : ∀ k : ℕ, (k : ℂ) ≠ -(c - a))
    (hcb : ∀ k : ℕ, (k : ℂ) ≠ -(c - b))
    (hgap : 0 < (c - a - b).re) :
    GaussSummationFormula a b c := by
  obtain ⟨q, hq⟩ := exists_nat_gt (-b.re)
  have hbq : ∀ k : ℕ, (k : ℂ) ≠ -(b + q) := avoidsNegNat_add_nat b hb q
  have hcq : ∀ k : ℕ, (k : ℂ) ≠ -(c + q) := avoidsNegNat_add_nat c hc q
  have hbqpos : 0 < (b + (q : ℂ)).re := by
    norm_num [Complex.add_re]
    linarith
  have hare : a.re < (c - b).re := by
    simp only [Complex.sub_re] at hgap ⊢
    linarith
  obtain ⟨p, hp⟩ := exists_nat_norm_add_lt_add_of_re_lt a (c - b).re hare
  have hap : ∀ k : ℕ, (k : ℂ) ≠ -(a + p) := avoidsNegNat_add_nat a ha p
  have hmargin : ‖a + (p : ℂ)‖ <
      ((c + (q : ℂ) + (p : ℂ)) - (b + (q : ℂ))).re := by
    have heq : ((c + (q : ℂ) + (p : ℂ)) - (b + (q : ℂ))).re =
        (c - b).re + p := by
      norm_num [Complex.add_re, Complex.sub_re]
      ring
    rw [heq]
    exact hp
  have hchamber : GaussSummationFormula
      (a + (p : ℂ)) (b + (q : ℂ)) (c + (q : ℂ) + (p : ℂ)) := by
    rw [GaussSummationFormula]
    exact gaussSummation_of_euler_chamber
      (a + (p : ℂ)) (b + (q : ℂ)) (c + (q : ℂ) + (p : ℂ))
      hap hbqpos hmargin
  have hcbq : ∀ k : ℕ, (k : ℂ) ≠ -((c + q) - (b + q)) := by
    have heq : (c + (q : ℂ)) - (b + (q : ℂ)) = c - b := by ring
    simpa only [heq] using hcb
  have hgapq : 0 < ((c + q) - a - (b + q)).re := by
    have heq : (c + (q : ℂ)) - a - (b + (q : ℂ)) = c - a - b := by ring
    simpa only [heq] using hgap
  have hafterA : GaussSummationFormula a (b + q) (c + q) := by
    apply gaussSummationFormula_of_shift_a_c_nat
      a (b + q) (c + q) ha hbq hcq hcbq hgapq p
    exact hchamber
  exact gaussSummationFormula_of_shift_b_c_nat
    a b c ha hb hc hca hgap q hafterA

end
end RHTower

