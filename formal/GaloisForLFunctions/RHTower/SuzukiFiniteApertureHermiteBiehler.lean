import GaloisForLFunctions.Bottcher.MontelNormal
import GaloisForLFunctions.HTGeometry.CayleyUnitCircleReality
import Mathlib.Analysis.Complex.Schwarz

/-!
# Suzuki's finite-aperture Hermite--Biehler carrier

Suzuki's 2026 screw-function construction produces, at every positive aperture and every shift
below the restricted Weil floor, a complete circle of entire characteristic functions

`W_u(z) = A(z) + u E(z)`,  `‖u‖ = 1`,

and proves that every zero of every `W_u` is real.  The factor `z - i` in Suzuki's formula gives
`A(i) = 0`.  This module extracts the consequence not stated in the source: the pair is strictly
Hermite--Biehler, so `A/E` is a Schur/Livšic function on the upper half-plane.  Its Cayley inverse
is Herglotz and is canonically normalized by `m(i)=i`; no aperture-dependent normalization remains.

The proof genuinely uses the whole extension circle.  Along the segment from `i` to an arbitrary
upper-half-plane point, a failure of `‖A‖ < ‖E‖` would produce an equal-modulus point.  At that
point the unit phase `u = -A/E` would make one characteristic function vanish off the real axis.

The strict disk bound makes the corrected finite-aperture carrier a normal family.  Reusing the
project's proved sequential Montel theorem gives an unconditional locally uniform subsequence on
every smaller ball.  Thus the compactness part of the corrected Suzuki limit problem is discharged;
nondegeneration, uniqueness, shift control, and identification with the global Xi/de Branges
carrier remain arithmetic problems.  No RH assumption and no numerical computation occur here.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The all-angle deficiency-index characteristic pencil `W_u = A + uE`. -/
def suzukiCharacteristicPencil (A E : ℂ → ℂ) (u z : ℂ) : ℂ :=
  A z + u * E z

/-- Every unitary member of the characteristic pencil has no nonreal zero.  Suzuki's Theorem 1.5
supplies exactly this predicate for his finite-aperture functions. -/
def SuzukiAllAngleRealZeros (A E : ℂ → ℂ) : Prop :=
  ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ,
    suzukiCharacteristicPencil A E u z = 0 → z.im = 0

/-- The Livšic quotient of the characteristic pair. -/
def suzukiLivsicQuotient (A E : ℂ → ℂ) (z : ℂ) : ℂ :=
  A z / E z

/-- The Cayley inverse of the Livšic quotient: the normalized Herglotz presentation of the
finite-aperture characteristic family. -/
def suzukiUpperCayleyInv (w : ℂ) : ℂ :=
  I * ((1 + w) / (1 - w))

/-- The Cayley inverse maps the open disk into the open upper half-plane. -/
theorem suzukiUpperCayleyInv_im_pos_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (suzukiUpperCayleyInv w).im := by
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, norm_one] at hw
    exact (lt_irrefl 1) hw
  have hden : 0 < Complex.normSq (1 - w) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hw1))
  rw [suzukiUpperCayleyInv, Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul,
    zero_add, Complex.div_re, ← add_div]
  apply div_pos _ hden
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im,
    Complex.one_im, Complex.sub_im]
  nlinarith [Complex.sq_norm w, Complex.normSq_apply w, norm_nonneg w]

/-- The upper-half-plane Cayley map and `suzukiUpperCayleyInv` are inverse away from the lower
anchor `-i`. -/
theorem suzukiUpperCayleyInv_lineCayley {z : ℂ} (hz : z + I ≠ 0) :
    suzukiUpperCayleyInv (GaloisForLFunctions.HTGeometry.lineCayley z) = z := by
  rw [suzukiUpperCayleyInv, GaloisForLFunctions.HTGeometry.lineCayley]
  field_simp
  ring

/-- **Anchored upper-half-plane Schwarz bound.**  A Schur function on the upper half-plane that
vanishes at `i` is pointwise dominated by the line-to-disk Cayley map. -/
theorem upperHalfPlane_schwarz_bound
    {θ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ θ {z : ℂ | 0 < z.im})
    (hθ : ∀ z : ℂ, 0 < z.im → ‖θ z‖ < 1)
    (hθi : θ I = 0)
    {z : ℂ} (hz : 0 < z.im) :
    ‖θ z‖ ≤ ‖GaloisForLFunctions.HTGeometry.lineCayley z‖ := by
  let f : ℂ → ℂ := fun w => θ (suzukiUpperCayleyInv w)
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, norm_one] at hwlt
      exact (lt_irrefl 1) hwlt
    have hinv : DifferentiableAt ℂ suzukiUpperCayleyInv w := by
      change DifferentiableAt ℂ (fun v : ℂ => I * ((1 + v) / (1 - v))) w
      fun_prop (disch := exact sub_ne_zero.mpr (Ne.symm hw1))
    have him := suzukiUpperCayleyInv_im_pos_of_norm_lt_one hwlt
    have hθat : DifferentiableAt ℂ θ (suzukiUpperCayleyInv w) :=
      hd.differentiableAt (hopen.mem_nhds him)
    exact (hθat.comp w hinv).differentiableWithinAt
  have hmaps : MapsTo f (ball 0 1) (closedBall 0 1) := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    exact (hθ _ (suzukiUpperCayleyInv_im_pos_of_norm_lt_one hwlt)).le
  have hf0 : f 0 = 0 := by
    simpa [f, suzukiUpperCayleyInv] using hθi
  have hden : z + I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
    linarith
  have hw := GaloisForLFunctions.cayley_upperHalfPlane_to_disk z hz
  have hsch := Complex.norm_le_norm_of_mapsTo_ball hfdiff hmaps hf0 hw
  change ‖θ (suzukiUpperCayleyInv ((z - I) / (z + I)))‖ ≤ ‖(z - I) / (z + I)‖ at hsch
  have hinv : suzukiUpperCayleyInv ((z - I) / (z + I)) = z := by
    simpa [GaloisForLFunctions.HTGeometry.lineCayley] using
      (suzukiUpperCayleyInv_lineCayley hden)
  rw [hinv] at hsch
  simpa [GaloisForLFunctions.HTGeometry.lineCayley] using hsch

/-- The normalized Herglotz presentation of the finite-aperture characteristic family. -/
def suzukiHerglotz (A E : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiUpperCayleyInv (suzukiLivsicQuotient A E z)

/-- Suzuki's factor `z-i` canonically anchors every Livšic quotient at zero. -/
theorem suzukiLivsicQuotient_I_eq_zero
    {A E : ℂ → ℂ} (hAi : A I = 0) :
    suzukiLivsicQuotient A E I = 0 := by
  simp [suzukiLivsicQuotient, hAi]

/-- The corresponding Herglotz carrier needs no aperture-dependent normalization: it sends `i`
to `i` for every aperture, shift, and characteristic pair. -/
theorem suzukiHerglotz_I_eq_I
    {A E : ℂ → ℂ} (hAi : A I = 0) :
    suzukiHerglotz A E I = I := by
  simp [suzukiHerglotz, suzukiUpperCayleyInv, suzukiLivsicQuotient_I_eq_zero hAi]

/-- **All-angle reality forces the Hermite--Biehler inequality.**  If the complete unitary
characteristic pencil has only real zeros and `A(i)=0`, then `‖A(z)‖ < ‖E(z)‖` throughout the open
upper half-plane. -/
theorem norm_lt_of_suzukiAllAngleRealZeros
    {A E : ℂ → ℂ} (hA : Continuous A) (hE : Continuous E)
    (hAi : A I = 0) (hreal : SuzukiAllAngleRealZeros A E)
    {z : ℂ} (hz : 0 < z.im) :
    ‖A z‖ < ‖E z‖ := by
  have hEi : E I ≠ 0 := by
    intro hEi
    have hzI := hreal 1 (norm_one : ‖(1 : ℂ)‖ = 1) I
    have hzero : suzukiCharacteristicPencil A E 1 I = 0 := by
      simp [suzukiCharacteristicPencil, hAi, hEi]
    have := hzI hzero
    simp at this
  by_contra hnot
  have hle : ‖E z‖ ≤ ‖A z‖ := le_of_not_gt hnot
  let γ : ℝ → ℂ := fun t => (1 - t) • I + t • z
  let f : ℝ → ℝ := fun t => ‖A (γ t)‖ - ‖E (γ t)‖
  have hγ : Continuous γ := by
    fun_prop
  have hf : Continuous f := by
    exact ((continuous_norm.comp (hA.comp hγ)).sub
      (continuous_norm.comp (hE.comp hγ)))
  have hf0 : f 0 < 0 := by
    simp [f, γ, hAi, norm_pos_iff.mpr hEi]
  have hf1 : 0 ≤ f 1 := by
    simpa [f, γ] using sub_nonneg.mpr hle
  have hmem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := ⟨hf0.le, hf1⟩
  obtain ⟨t, ht, hft⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf.continuousOn hmem
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hγim : 0 < (γ t).im := by
    simp only [γ, Complex.add_im, Complex.smul_im, Complex.I_im, smul_eq_mul]
    by_cases ht_eq : t = 1
    · simpa [ht_eq] using hz
    · have htlt : t < 1 := lt_of_le_of_ne ht1 ht_eq
      have hleft : 0 < 1 - t := sub_pos.mpr htlt
      have hright : 0 ≤ t * z.im := mul_nonneg ht0 hz.le
      nlinarith
  have hnormeq : ‖A (γ t)‖ = ‖E (γ t)‖ := by
    exact sub_eq_zero.mp hft
  by_cases hEt : E (γ t) = 0
  · have hAt : A (γ t) = 0 := by
      apply norm_eq_zero.mp
      rw [hnormeq, hEt, norm_zero]
    have hzero : suzukiCharacteristicPencil A E 1 (γ t) = 0 := by
      simp [suzukiCharacteristicPencil, hAt, hEt]
    have him := hreal 1 (norm_one : ‖(1 : ℂ)‖ = 1) (γ t) hzero
    linarith
  · let u : ℂ := -A (γ t) / E (γ t)
    have hu : ‖u‖ = 1 := by
      change ‖-A (γ t) / E (γ t)‖ = 1
      rw [norm_div, norm_neg, hnormeq, div_self (norm_ne_zero_iff.mpr hEt)]
    have hzero : suzukiCharacteristicPencil A E u (γ t) = 0 := by
      change A (γ t) + (-A (γ t) / E (γ t)) * E (γ t) = 0
      rw [neg_div, neg_mul, div_mul_cancel₀ _ hEt, add_neg_cancel]
    have him := hreal u hu (γ t) hzero
    linarith

/-- The denominator of the finite-aperture Livšic quotient has no upper-half-plane zero. -/
theorem suzukiLivsic_denominator_ne_zero
    {A E : ℂ → ℂ} (hA : Continuous A) (hE : Continuous E)
    (hAi : A I = 0) (hreal : SuzukiAllAngleRealZeros A E)
    {z : ℂ} (hz : 0 < z.im) :
    E z ≠ 0 := by
  intro hzero
  have hlt := norm_lt_of_suzukiAllAngleRealZeros hA hE hAi hreal hz
  rw [hzero, norm_zero] at hlt
  exact (not_lt_of_ge (norm_nonneg _)) hlt

/-- The finite-aperture Livšic quotient lies strictly in the unit disk. -/
theorem norm_suzukiLivsicQuotient_lt_one
    {A E : ℂ → ℂ} (hA : Continuous A) (hE : Continuous E)
    (hAi : A I = 0) (hreal : SuzukiAllAngleRealZeros A E)
    {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiLivsicQuotient A E z‖ < 1 := by
  have hE0 := suzukiLivsic_denominator_ne_zero hA hE hAi hreal hz
  rw [suzukiLivsicQuotient, norm_div, div_lt_one (norm_pos_iff.mpr hE0)]
  exact norm_lt_of_suzukiAllAngleRealZeros hA hE hAi hreal hz

/-- The canonically anchored Cayley inverse of the Suzuki Livšic quotient is Herglotz on the upper
half-plane. -/
theorem suzukiHerglotz_im_nonneg
    {A E : ℂ → ℂ} (hA : Continuous A) (hE : Continuous E)
    (hAi : A I = 0) (hreal : SuzukiAllAngleRealZeros A E)
    {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (suzukiHerglotz A E z).im := by
  have hlt := norm_suzukiLivsicQuotient_lt_one hA hE hAi hreal hz
  have hne : suzukiLivsicQuotient A E z ≠ 1 := by
    intro h
    rw [h, norm_one] at hlt
    exact (lt_irrefl 1) hlt
  exact cayley_schur_herglotz (suzukiLivsicQuotient A E z) hlt.le hne

/-- The Schwarz-reflected entire function used in the Hermite--Biehler inequality. -/
def suzukiEntireSharp (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (E ((starRingEnd ℂ) z))

/-- The strict Hermite--Biehler inequality on the upper half-plane. -/
def SuzukiHermiteBiehler (E : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → ‖suzukiEntireSharp E z‖ < ‖E z‖

/-- Suzuki's all-angle real-zero theorem upgrades a reflected characteristic pair to a
Hermite--Biehler function. -/
theorem suzukiHermiteBiehler_of_allAngleRealZeros
    {A E : ℂ → ℂ} (hA : Continuous A) (hE : Continuous E)
    (hAi : A I = 0) (hreal : SuzukiAllAngleRealZeros A E)
    (hsharp : A = suzukiEntireSharp E) :
    SuzukiHermiteBiehler E := by
  intro z hz
  rw [← hsharp]
  exact norm_lt_of_suzukiAllAngleRealZeros hA hE hAi hreal hz

/-- The Livšic quotient is holomorphic on the upper half-plane. -/
theorem differentiableOn_suzukiLivsicQuotient_upperHalfPlane
    {A E : ℂ → ℂ} (hA : Differentiable ℂ A) (hE : Differentiable ℂ E)
    (hAi : A I = 0) (hreal : SuzukiAllAngleRealZeros A E) :
    DifferentiableOn ℂ (suzukiLivsicQuotient A E) {z : ℂ | 0 < z.im} := by
  intro z hz
  have hE0 := suzukiLivsic_denominator_ne_zero hA.continuous hE.continuous hAi hreal hz
  exact ((hA z).div (hE z) hE0).differentiableWithinAt

/-- **Aperture-uniform Schwarz--Pick bound.**  Every finite-aperture Suzuki Livšic quotient is
dominated by the fixed line Cayley map; the estimate contains no aperture, shift, or prime
constant. -/
theorem norm_suzukiLivsicQuotient_le_lineCayley
    {A E : ℂ → ℂ} (hA : Differentiable ℂ A) (hE : Differentiable ℂ E)
    (hAi : A I = 0) (hreal : SuzukiAllAngleRealZeros A E)
    {z : ℂ} (hz : 0 < z.im) :
    ‖suzukiLivsicQuotient A E z‖ ≤
      ‖GaloisForLFunctions.HTGeometry.lineCayley z‖ := by
  exact upperHalfPlane_schwarz_bound
    (differentiableOn_suzukiLivsicQuotient_upperHalfPlane hA hE hAi hreal)
    (fun _ hw => norm_suzukiLivsicQuotient_lt_one
      hA.continuous hE.continuous hAi hreal hw)
    (suzukiLivsicQuotient_I_eq_zero hAi) hz

/-- **Finite-aperture Suzuki normality.**  On every ball contained in the upper half-plane, any
sequence of all-angle characteristic pairs has a subsequence whose Livšic quotients converge
uniformly on a smaller closed ball to a holomorphic limit. -/
theorem exists_suzukiLivsic_montel_subseq
    {A E : ℕ → ℂ → ℂ} {c : ℂ} {R r : ℝ}
    (hr0 : 0 < r) (hrR : r < R / 2)
    (hupper : ∀ z ∈ ball c R, 0 < z.im)
    (hA : ∀ n, Differentiable ℂ (A n))
    (hE : ∀ n, Differentiable ℂ (E n))
    (hAi : ∀ n, A n I = 0)
    (hreal : ∀ n, SuzukiAllAngleRealZeros (A n) (E n)) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧
      TendstoUniformlyOn
        (fun k => suzukiLivsicQuotient (A (φ k)) (E (φ k))) g atTop (closedBall c r) ∧
      DifferentiableOn ℂ g (ball c r) := by
  refine Bottcher.montel_subseq
    (F := fun n => suzukiLivsicQuotient (A n) (E n)) (c := c) (C := 1)
    hr0 hrR ?_ ?_
  · intro n
    exact (differentiableOn_suzukiLivsicQuotient_upperHalfPlane
      (hA n) (hE n) (hAi n) (hreal n)).mono hupper
  · intro n z hz
    exact (norm_suzukiLivsicQuotient_lt_one
      (hA n).continuous (hE n).continuous (hAi n) (hreal n) (hupper z hz)).le

/-- A quotient of two extension angles is a fixed Möbius transform of the Livšic quotient. -/
theorem suzuki_twoAngle_quotient_eq_mobius
    (A E : ℂ → ℂ) (u₀ u₁ z : ℂ) (hE : E z ≠ 0) :
    suzukiCharacteristicPencil A E u₀ z /
        suzukiCharacteristicPencil A E u₁ z =
      (suzukiLivsicQuotient A E z + u₀) /
        (suzukiLivsicQuotient A E z + u₁) := by
  have hform (u : ℂ) : suzukiLivsicQuotient A E z + u =
      suzukiCharacteristicPencil A E u z / E z := by
    rw [suzukiLivsicQuotient, suzukiCharacteristicPencil]
    field_simp
  rw [hform u₀, hform u₁]
  exact (div_div_div_cancel_right₀ hE _ _).symm

/-- Two distinct extension angles recover the Livšic quotient by a fixed Möbius transform. -/
theorem suzuki_twoAngle_reconstruct_livsic
    (A E : ℂ → ℂ) (u₀ u₁ z : ℂ) (hE : E z ≠ 0)
    (hW₁ : suzukiCharacteristicPencil A E u₁ z ≠ 0)
    (hu : u₀ ≠ u₁) :
    suzukiLivsicQuotient A E z =
      (u₀ - u₁ *
          (suzukiCharacteristicPencil A E u₀ z /
            suzukiCharacteristicPencil A E u₁ z)) /
        ((suzukiCharacteristicPencil A E u₀ z /
            suzukiCharacteristicPencil A E u₁ z) - 1) := by
  let θ := suzukiLivsicQuotient A E z
  let q := suzukiCharacteristicPencil A E u₀ z /
    suzukiCharacteristicPencil A E u₁ z
  have hq : q = (θ + u₀) / (θ + u₁) := by
    exact suzuki_twoAngle_quotient_eq_mobius A E u₀ u₁ z hE
  have hden : θ + u₁ ≠ 0 := by
    intro hzero
    have hform : θ + u₁ = suzukiCharacteristicPencil A E u₁ z / E z := by
      dsimp [θ]
      rw [suzukiLivsicQuotient, suzukiCharacteristicPencil]
      field_simp
    rw [hzero] at hform
    have : suzukiCharacteristicPencil A E u₁ z = 0 := by
      exact (div_eq_zero_iff).mp hform.symm |>.resolve_right hE
    exact hW₁ this
  have hq1 : q - 1 ≠ 0 := by
    rw [hq]
    have hident : (θ + u₀) / (θ + u₁) - 1 = (u₀ - u₁) / (θ + u₁) := by
      field_simp
      ring
    rw [hident]
    exact div_ne_zero (sub_ne_zero.mpr hu) hden
  change θ = (u₀ - u₁ * q) / (q - 1)
  field_simp
  rw [hq]
  field_simp
  ring

/-- A common nonvanishing entire normalization cancels exactly from the two-angle quotient. -/
theorem suzuki_twoAngle_common_gauge_cancels
    (A E : ℂ → ℂ) (g u₀ u₁ z : ℂ) (hg : g ≠ 0) :
    (g * suzukiCharacteristicPencil A E u₀ z) /
        (g * suzukiCharacteristicPencil A E u₁ z) =
      suzukiCharacteristicPencil A E u₀ z /
        suzukiCharacteristicPencil A E u₁ z := by
  exact mul_div_mul_left _ _ hg

end GaloisForLFunctions.RHTower
