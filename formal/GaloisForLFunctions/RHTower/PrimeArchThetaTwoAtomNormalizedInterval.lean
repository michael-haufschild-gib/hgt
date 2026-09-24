import GaloisForLFunctions.RHTower.PrimeArchThetaSourceAtomDomination

/-!
# Two-atom intervals for every normalized theta moment

The raw theta moment is its first two atom moments plus a nonnegative remainder.
The previously established uniform remainder domination then transfers through
normalization, giving a source-specific interval at every order.
-/

open MeasureTheory Set
namespace RHTower
noncomputable section

private theorem thetaCuspBeyondSecondAtomRawEvenMoment_nonneg (j : ℕ) :
    0 ≤ thetaCuspBeyondSecondAtomRawEvenMoment j := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspFullSource x
  let g₁ : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspSourceTerm x 1
  let g₂ : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspSourceTerm x 2
  let r : ℝ → ℝ := fun x => x ^ (2 * j) *
    (thetaCuspFullSource x - thetaCuspSourceTerm x 1 - thetaCuspSourceTerm x 2)
  have hf : Integrable f mu := integrableOn_thetaCuspRawMoment (2 * j)
  have hg₁ : Integrable g₁ mu := integrableOn_pow_mul_thetaCuspSourceTerm j 1
  have hg₂ : Integrable g₂ mu := integrableOn_pow_mul_thetaCuspSourceTerm j 2
  have hr : Integrable r mu := by
    convert (hf.sub hg₁).sub hg₂ using 1
    funext x
    dsimp [f, g₁, g₂, r]
    ring
  have htail (x : ℝ) (hx : 0 < x) :
      0 ≤ thetaCuspFullSource x - thetaCuspSourceTerm x 1 -
        thetaCuspSourceTerm x 2 := by
    have hs := summable_thetaCuspSourceTerm x
    have ht : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 3)) :=
      hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
    have hhead : (∑ n ∈ Finset.range 3, thetaCuspSourceTerm x n) =
        thetaCuspSourceTerm x 1 + thetaCuspSourceTerm x 2 := by
      simp [Finset.sum_range_succ, thetaCuspSourceTerm, thetaCuspSeed]
    have heq : thetaCuspFullSource x - thetaCuspSourceTerm x 1 -
        thetaCuspSourceTerm x 2 =
          ∑' k : ℕ, thetaCuspSourceTerm x (k + 3) := by
      rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 3, hhead]
      ring
    rw [heq]
    exact tsum_nonneg (fun k => thetaCuspSourceTerm_nonneg_of_pos hx (k + 3))
  have hnonneg : 0 ≤ ∫ x, r x ∂mu := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (pow_nonneg hx.le _) (htail x hx)
  have hvalue : thetaCuspBeyondSecondAtomRawEvenMoment j =
      2 * ∫ x, r x ∂mu := by
    rw [thetaCuspBeyondSecondAtomRawEvenMoment,
      thetaCuspRawEvenMoment, thetaCuspAtomRawEvenMoment]
    change 2 * ∫ x, f x ∂mu - 2 * ∫ x, g₁ x ∂mu -
      2 * ∫ x, g₂ x ∂mu = 2 * ∫ x, r x ∂mu
    have hrfun : r = (f - g₁) - g₂ := by
      funext x
      dsimp [r, f, g₁, g₂]
      ring
    rw [hrfun]
    calc
      2 * ∫ x, f x ∂mu - 2 * ∫ x, g₁ x ∂mu -
          2 * ∫ x, g₂ x ∂mu =
        2 * ((∫ x, f x ∂mu) - (∫ x, g₁ x ∂mu) -
          (∫ x, g₂ x ∂mu)) := by ring
      _ = 2 * ∫ x, (f - g₁ - g₂) x ∂mu := by
        congr 1
        rw [← integral_sub hf hg₁]
        change (∫ x, (f - g₁) x ∂mu) - (∫ x, g₂ x ∂mu) =
          ∫ x, ((f - g₁) - g₂) x ∂mu
        exact (integral_sub (hf.sub hg₁) hg₂).symm
  rw [hvalue]
  exact mul_nonneg (by norm_num) hnonneg

/-- The exact tail past the second theta atom is nonnegative and at most
`1/374625` times the first atom, at every even moment order. -/
theorem thetaCuspBeyondSecondAtomRawEvenMoment_mem_interval (j : ℕ) :
    0 ≤ thetaCuspBeyondSecondAtomRawEvenMoment j ∧
      thetaCuspBeyondSecondAtomRawEvenMoment j ≤
        (1 : ℝ) / 374625 * thetaCuspAtomRawEvenMoment j 1 :=
  ⟨thetaCuspBeyondSecondAtomRawEvenMoment_nonneg j,
    thetaCuspBeyondSecondAtomRawEvenMoment_le_first_tiny j⟩

/-- A normalized moment lies between the two-atom moment divided by the maximal
possible total mass and the maximal numerator divided by the two-atom total mass. -/
theorem thetaCuspNormalizedEvenMoment_twoAtom_interval (j : ℕ) :
    let a₀ := thetaCuspAtomRawEvenMoment 0 1
    let b₀ := thetaCuspAtomRawEvenMoment 0 2
    let a := thetaCuspAtomRawEvenMoment j 1
    let b := thetaCuspAtomRawEvenMoment j 2
    (a + b) / (a₀ + b₀ + (1 : ℝ) / 374625 * a₀) ≤
      thetaCuspNormalizedEvenMoment j ∧
    thetaCuspNormalizedEvenMoment j ≤
      (a + b + (1 : ℝ) / 374625 * a) / (a₀ + b₀) := by
  dsimp only
  let a₀ := thetaCuspAtomRawEvenMoment 0 1
  let b₀ := thetaCuspAtomRawEvenMoment 0 2
  let a := thetaCuspAtomRawEvenMoment j 1
  let b := thetaCuspAtomRawEvenMoment j 2
  let r₀ := thetaCuspBeyondSecondAtomRawEvenMoment 0
  let r := thetaCuspBeyondSecondAtomRawEvenMoment j
  have ha₀ : 0 ≤ a₀ := thetaCuspAtomRawEvenMoment_nonneg 0 1
  have hb₀ : 0 ≤ b₀ := thetaCuspAtomRawEvenMoment_nonneg 0 2
  have ha : 0 ≤ a := thetaCuspAtomRawEvenMoment_nonneg j 1
  have hb : 0 ≤ b := thetaCuspAtomRawEvenMoment_nonneg j 2
  have hr₀ := thetaCuspBeyondSecondAtomRawEvenMoment_mem_interval 0
  have hr := thetaCuspBeyondSecondAtomRawEvenMoment_mem_interval j
  have hraw₀ : thetaCuspRawEvenMoment 0 = a₀ + b₀ + r₀ := by
    dsimp [a₀, b₀, r₀, thetaCuspBeyondSecondAtomRawEvenMoment]
    ring
  have hraw : thetaCuspRawEvenMoment j = a + b + r := by
    dsimp [a, b, r, thetaCuspBeyondSecondAtomRawEvenMoment]
    ring
  have hden : 0 < a₀ + b₀ := by
    have hm := thetaCuspRawEvenMoment_zero_pos
    rw [hraw₀] at hm
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 374625) ha₀]
  have hdenmax : 0 < a₀ + b₀ + (1 : ℝ) / 374625 * a₀ := by
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 374625) ha₀]
  have hrawpos : 0 < a₀ + b₀ + r₀ := by
    rw [← hraw₀]
    exact thetaCuspRawEvenMoment_zero_pos
  rw [thetaCuspNormalizedEvenMoment, hraw, hraw₀]
  constructor
  · apply (div_le_div_iff₀ hdenmax hrawpos).2
    have hgap : 0 ≤ (a + b) * ((1 : ℝ) / 374625 * a₀ - r₀) :=
      mul_nonneg (add_nonneg ha hb) (sub_nonneg.mpr hr₀.2)
    have htail : 0 ≤ r * (a₀ + b₀ + (1 : ℝ) / 374625 * a₀) :=
      mul_nonneg hr.1 hdenmax.le
    nlinarith
  · apply (div_le_div_iff₀ hrawpos hden).2
    have hgap : 0 ≤ ((1 : ℝ) / 374625 * a - r) * (a₀ + b₀) :=
      mul_nonneg (sub_nonneg.mpr hr.2) hden.le
    have htail : 0 ≤ (a + b + (1 : ℝ) / 374625 * a) * r₀ :=
      mul_nonneg (by nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 374625) ha]) hr₀.1
    nlinarith

end
end RHTower
