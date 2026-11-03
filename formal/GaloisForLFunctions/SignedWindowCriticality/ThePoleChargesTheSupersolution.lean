import GaloisForLFunctions.SignedWindowCriticality.NoMarkovGroundStateOnAWindowLongerThanTheDeathWidth

/-!
# The pole charges the supersolution

Weil's form is `Ẑ(F) = M(F) − 2B(F)² + 2A(F)²` with `A = ∫F cosh(x/2)`, `B = ∫F sinh(x/2)` (ACT
`fullZeroForm`). Allegretto–Piepenbrink certifies the Markov part `M` by a positive supersolution;
the Markov part dies at length `e^{−3/4}` (`TheMarkovPartDiesBeforeTheFirstPrime`). This file states
what replaces Allegretto–Piepenbrink when the pole is kept: on a window `S = (b, c)` every square of
the pole becomes a *charge* of the gauge.

For a gauge `ω ∈ C²_c` put `M = Φω`, `m_s = M sinh(x/2)`, `m_c = M cosh(x/2)`, the charges
`σ_s = ∫_S m_s`, `σ_c = ∫_S m_c`, and the **pole-charged defect**
`𝒢_S(ω) = (𝓛_D ω − Φ cosh(x/2) ω) − 2σ_s Φ sinh(x/2) + 2σ_c Φ cosh(x/2)`.

* **Exact representation** (`fullZeroForm_phiDoob_mul_eq`). For every `u ∈ C²_c` vanishing off `S`,
  `Ẑ(Φωu) = J_{Φω}(u) + ∫ u²ω 𝒢_S(ω) + 2V_s(u) − 2V_c(u)`, with charge variances
  `V(u) = (∫_S m)(∫u²m) − (∫um)² = ½∫∫_{S²} m(x)m(y)(u(x) − u(y))²`. Together
  `2V_s − 2V_c = −∫∫_{S²} M(x)M(y) cosh((x − y)/2)(u(x) − u(y))²`: the pole is a negative
  long-range conductance of the gauge, and its charges move into the potential.
* **The negative square is a sinh charge** (`signedJumpEnergy_add_le_fullZeroForm_of_sinhCharged`).
  If `m_s ≥ 0` on `S` and `ω(𝓛_Dω − Φcosh ω − 2σ_sΦ sinh) ≥ 0` on `S`, then
  `Ẑ(Φωu) ≥ J_{Φω}(u) + 2A²`: the supersolution must carry the sinh charge, and then the pole's
  negative square is paid (Cauchy–Schwarz for `m_s`).
* **The positive square is a cosh credit** (`signedJumpEnergy_sub_le_fullZeroForm_of_coshCharged`).
  If `ω ≥ 0` on `S` and `ω(𝓛_Dω − Φcosh ω + 2σ_cΦ cosh) ≥ 0` on `S`, then
  `Ẑ(Φωu) ≥ J_{Φω}(u) − 2V_c(u) − 2B²`: the gauge may be a subsolution by the cosh charge, at the
  price of the negative conductance `−2V_c`.

On symmetric windows the two statements are the odd and even sectors (`A = 0` on odd tests, `B = 0`
on even tests). A signed supersolution is a gauge satisfying the charged inequality whose signed
Dirichlet form (`J_{Φω}` in the odd sector, `J_{Φω} − 2V_c` in the even sector) is nonnegative.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The sinh charge `∫_S Φω sinh(x/2)` of a gauge on a window. -/
def sinhCharge (ω : ℝ → ℝ) (S : Set ℝ) : ℝ :=
  ∫ x in S, riemannKernelReal x * ω x * Real.sinh (x / 2)

/-- The cosh charge `∫_S Φω cosh(x/2)` of a gauge on a window. -/
def coshCharge (ω : ℝ → ℝ) (S : Set ℝ) : ℝ :=
  ∫ x in S, riemannKernelReal x * ω x * Real.cosh (x / 2)

/-- The pole-charged defect `𝓛_Dω − Φcosh ω − 2σ_sΦ sinh + 2σ_cΦ cosh`. -/
def poleChargedDefect (ω : ℝ → ℝ) (S : Set ℝ) (x : ℝ) : ℝ :=
  markovDefect ω x - 2 * sinhCharge ω S * (riemannKernelReal x * Real.sinh (x / 2)) +
    2 * coshCharge ω S * (riemannKernelReal x * Real.cosh (x / 2))

/-- The charge variance `(∫_S m)(∫u²m) − (∫um)²` of a weight `m` on a window. -/
def chargeVariance (m : ℝ → ℝ) (S : Set ℝ) (u : ℝ → ℝ) : ℝ :=
  (∫ x in S, m x) * (∫ x, u x ^ 2 * m x) - (∫ x, u x * m x) ^ 2

variable {ω u : ℝ → ℝ} {b c : ℝ}

theorem integrableOn_Ioo_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Ioo b c) :=
  (hf.integrableOn_Icc).mono_set Ioo_subset_Icc_self

/-- **Cauchy–Schwarz for a charge.** A weight nonnegative on the window has nonnegative charge
variance against every profile vanishing off the window. -/
theorem chargeVariance_nonneg {m : ℝ → ℝ} (hm : Continuous m) (hm0 : ∀ x ∈ Ioo b c, 0 ≤ m x)
    (hu : Continuous u) (hub : ∀ x, x ∉ Ioo b c → u x = 0) :
    0 ≤ chargeVariance m (Ioo b c) u := by
  have e2 : (∫ x, u x ^ 2 * m x) = ∫ x in Ioo b c, u x ^ 2 * m x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hub x hx]).symm
  have e1 : (∫ x, u x * m x) = ∫ x in Ioo b c, u x * m x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hub x hx]).symm
  set σ := ∫ x in Ioo b c, m x
  set A₁ := ∫ x in Ioo b c, u x * m x
  set A₂ := ∫ x in Ioo b c, u x ^ 2 * m x
  have hq : ∀ t : ℝ, 0 ≤ σ * (t * t) + (-2 * A₁) * t + A₂ := by
    intro t
    have hi1 : IntegrableOn (fun x => u x ^ 2 * m x) (Ioo b c) :=
      integrableOn_Ioo_of_continuous ((hu.pow 2).mul hm)
    have hi2 : IntegrableOn (fun x => u x * m x) (Ioo b c) :=
      integrableOn_Ioo_of_continuous (hu.mul hm)
    have hi3 : IntegrableOn m (Ioo b c) := integrableOn_Ioo_of_continuous hm
    have h0 : 0 ≤ ∫ x in Ioo b c, m x * (u x - t) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioo fun x hx => mul_nonneg (hm0 x hx) (sq_nonneg _)
    have hexp : (∫ x in Ioo b c, m x * (u x - t) ^ 2) = A₂ - 2 * t * A₁ + t ^ 2 * σ := by
      have hpt : (fun x => m x * (u x - t) ^ 2) =
          fun x => (u x ^ 2 * m x - (2 * t) * (u x * m x)) + t ^ 2 * m x := by
        funext x; ring
      have h1 : (∫ x in Ioo b c, ((u x ^ 2 * m x - (2 * t) * (u x * m x)) + t ^ 2 * m x)) =
          (∫ x in Ioo b c, (u x ^ 2 * m x - (2 * t) * (u x * m x))) +
            ∫ x in Ioo b c, t ^ 2 * m x :=
        integral_add (hi1.sub (hi2.const_mul _)) (hi3.const_mul _)
      have h2 : (∫ x in Ioo b c, (u x ^ 2 * m x - (2 * t) * (u x * m x))) =
          A₂ - ∫ x in Ioo b c, (2 * t) * (u x * m x) :=
        integral_sub hi1 (hi2.const_mul _)
      rw [hpt, h1, h2, integral_const_mul, integral_const_mul]
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  unfold chargeVariance
  rw [e1, e2]
  nlinarith

theorem continuous_mul_sinh {ω : ℝ → ℝ} (hω : Continuous ω) :
    Continuous fun x => riemannKernelReal x * ω x * Real.sinh (x / 2) :=
  (continuous_riemannKernelReal.mul hω).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))

theorem continuous_mul_cosh {ω : ℝ → ℝ} (hω : Continuous ω) :
    Continuous fun x => riemannKernelReal x * ω x * Real.cosh (x / 2) :=
  (continuous_riemannKernelReal.mul hω).mul (Real.continuous_cosh.comp (continuous_id.div_const 2))

/-- The pole moments of `Φωu` are the pairings of `u` with the charge weights. -/
theorem oddPoleMoment_phiDoob_mul (ω u : ℝ → ℝ) :
    oddPoleMoment (phiDoobTest fun y => ω y * u y) =
      ∫ x, u x * (riemannKernelReal x * ω x * Real.sinh (x / 2)) := by
  unfold oddPoleMoment phiDoobTest
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

theorem evenPoleMoment_phiDoob_mul (ω u : ℝ → ℝ) :
    evenPoleMoment (phiDoobTest fun y => ω y * u y) =
      ∫ x, u x * (riemannKernelReal x * ω x * Real.cosh (x / 2)) := by
  unfold evenPoleMoment phiDoobTest
  exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)

/-- **Exact pole-charged representation on a window.** For `ω, u ∈ C²_c` with `u = 0` off
`S = (b, c)`: `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s(u) − 2V_c(u)`. -/
theorem fullZeroForm_phiDoob_mul_eq (hω : ContDiff ℝ 2 ω) (hωc : HasCompactSupport ω)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    fullZeroForm (phiDoobTest fun y => ω y * u y) =
      signedJumpEnergy (fun y => riemannKernelReal y * ω y) u +
        (∫ x, u x ^ 2 * ω x * poleChargedDefect ω (Ioo b c) x) +
        2 * chargeVariance (fun x => riemannKernelReal x * ω x * Real.sinh (x / 2)) (Ioo b c) u -
        2 * chargeVariance (fun x => riemannKernelReal x * ω x * Real.cosh (x / 2)) (Ioo b c) u := by
  have hD := continuous_markovDefect hω hωc
  have huc' := hu.continuous
  have hsupp2 : HasCompactSupport fun x => u x ^ 2 :=
    huc.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  have hiD : Integrable fun x => u x ^ 2 * ω x * markovDefect ω x :=
    (((huc'.pow 2).mul hω.continuous).mul hD).integrable_of_hasCompactSupport
      (hsupp2.mul_right.mul_right)
  have his : Integrable fun x => u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)) :=
    ((huc'.pow 2).mul (continuous_mul_sinh hω.continuous)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hic : Integrable fun x => u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2)) :=
    ((huc'.pow 2).mul (continuous_mul_cosh hω.continuous)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hsplit : (∫ x, u x ^ 2 * ω x * poleChargedDefect ω (Ioo b c) x) =
      (∫ x, u x ^ 2 * ω x * markovDefect ω x) -
        2 * sinhCharge ω (Ioo b c) *
          (∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))) +
        2 * coshCharge ω (Ioo b c) *
          (∫ x, u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2))) := by
    have h1 : (∫ x, ((u x ^ 2 * ω x * markovDefect ω x - 2 * sinhCharge ω (Ioo b c) *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)))) +
          2 * coshCharge ω (Ioo b c) *
            (u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2))))) =
        (∫ x, (u x ^ 2 * ω x * markovDefect ω x - 2 * sinhCharge ω (Ioo b c) *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))))) +
          ∫ x, 2 * coshCharge ω (Ioo b c) *
            (u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2))) :=
      integral_add (hiD.sub (his.const_mul _)) (hic.const_mul _)
    have h2 : (∫ x, (u x ^ 2 * ω x * markovDefect ω x - 2 * sinhCharge ω (Ioo b c) *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))))) =
        (∫ x, u x ^ 2 * ω x * markovDefect ω x) - ∫ x, 2 * sinhCharge ω (Ioo b c) *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2))) :=
      integral_sub hiD (his.const_mul _)
    have h0 : (∫ x, u x ^ 2 * ω x * poleChargedDefect ω (Ioo b c) x) =
        ∫ x, ((u x ^ 2 * ω x * markovDefect ω x - 2 * sinhCharge ω (Ioo b c) *
          (u x ^ 2 * (riemannKernelReal x * ω x * Real.sinh (x / 2)))) +
          2 * coshCharge ω (Ioo b c) *
            (u x ^ 2 * (riemannKernelReal x * ω x * Real.cosh (x / 2)))) :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only [poleChargedDefect]; ring)
    rw [h0, h1, h2, integral_const_mul, integral_const_mul]
  unfold fullZeroForm
  rw [markovEnergy_phiDoob_mul_eq_signedJump_add_defect hω hωc hu huc, hsplit,
    oddPoleMoment_phiDoob_mul, evenPoleMoment_phiDoob_mul]
  unfold chargeVariance sinhCharge coshCharge
  ring

/-- **The negative square is a sinh charge.** If the sinh weight `Φω sinh(x/2)` is nonnegative on
the window and the gauge's Markov defect carries the sinh charge there, then
`Ẑ(Φωu) ≥ J_{Φω}(u) + 2A(Φωu)²` for every `u ∈ C²_c` vanishing off the window. -/
theorem signedJumpEnergy_add_le_fullZeroForm_of_sinhCharged (hω : ContDiff ℝ 2 ω)
    (hωc : HasCompactSupport ω) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (hub : ∀ x, x ∉ Ioo b c → u x = 0)
    (hs : ∀ x ∈ Ioo b c, 0 ≤ ω x * Real.sinh (x / 2))
    (hsuper : ∀ x ∈ Ioo b c, 0 ≤ ω x * (markovDefect ω x -
      2 * sinhCharge ω (Ioo b c) * (riemannKernelReal x * Real.sinh (x / 2)))) :
    signedJumpEnergy (fun y => riemannKernelReal y * ω y) u +
        2 * evenPoleMoment (phiDoobTest fun y => ω y * u y) ^ 2 ≤
      fullZeroForm (phiDoobTest fun y => ω y * u y) := by
  have hD := continuous_markovDefect hω hωc
  have huc' := hu.continuous
  have hsupp2 : HasCompactSupport fun x => u x ^ 2 :=
    huc.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  set σ := sinhCharge ω (Ioo b c)
  set m : ℝ → ℝ := fun x => riemannKernelReal x * ω x * Real.sinh (x / 2)
  have hiD : Integrable fun x => u x ^ 2 * ω x * markovDefect ω x :=
    (((huc'.pow 2).mul hω.continuous).mul hD).integrable_of_hasCompactSupport
      (hsupp2.mul_right.mul_right)
  have his : Integrable fun x => u x ^ 2 * m x :=
    ((huc'.pow 2).mul (continuous_mul_sinh hω.continuous)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hpot : 2 * σ * (∫ x, u x ^ 2 * m x) ≤ ∫ x, u x ^ 2 * ω x * markovDefect ω x := by
    have hsub : 0 ≤ ∫ x, (u x ^ 2 * ω x * markovDefect ω x - 2 * σ * (u x ^ 2 * m x)) := by
      refine integral_nonneg fun x => ?_
      by_cases hx : x ∈ Ioo b c
      · have h := mul_nonneg (sq_nonneg (u x)) (hsuper x hx)
        have e : u x ^ 2 * ω x * markovDefect ω x - 2 * σ * (u x ^ 2 * m x) =
            u x ^ 2 * (ω x * (markovDefect ω x - 2 * σ *
              (riemannKernelReal x * Real.sinh (x / 2)))) := by simp only [m]; ring
        rw [e]; exact h
      · simp [hub x hx]
    rw [integral_sub hiD (his.const_mul _), integral_const_mul] at hsub
    linarith
  have hV := chargeVariance_nonneg (m := m) (continuous_mul_sinh hω.continuous)
    (fun x hx => by
      have h1 := hs x hx
      have h2 := (riemannKernelReal_pos x).le
      simp only [m]; nlinarith) huc' hub
  unfold chargeVariance at hV
  unfold fullZeroForm
  rw [markovEnergy_phiDoob_mul_eq_signedJump_add_defect hω hωc hu huc,
    oddPoleMoment_phiDoob_mul]
  have hσ : σ = ∫ x in Ioo b c, m x := rfl
  rw [← hσ] at hV
  nlinarith

/-- **The positive square is a cosh credit.** If the gauge is nonnegative on the window and its
Markov defect is at least minus the cosh charge there, then
`Ẑ(Φωu) ≥ J_{Φω}(u) − 2V_c(u) − 2B(Φωu)²` for every `u ∈ C²_c` vanishing off the window. -/
theorem signedJumpEnergy_sub_le_fullZeroForm_of_coshCharged (hω : ContDiff ℝ 2 ω)
    (hωc : HasCompactSupport ω) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (hub : ∀ x, x ∉ Ioo b c → u x = 0)
    (hsub : ∀ x ∈ Ioo b c, 0 ≤ ω x * (markovDefect ω x +
      2 * coshCharge ω (Ioo b c) * (riemannKernelReal x * Real.cosh (x / 2)))) :
    signedJumpEnergy (fun y => riemannKernelReal y * ω y) u -
        2 * chargeVariance (fun x => riemannKernelReal x * ω x * Real.cosh (x / 2)) (Ioo b c) u -
        2 * oddPoleMoment (phiDoobTest fun y => ω y * u y) ^ 2 ≤
      fullZeroForm (phiDoobTest fun y => ω y * u y) := by
  have hD := continuous_markovDefect hω hωc
  have huc' := hu.continuous
  have hsupp2 : HasCompactSupport fun x => u x ^ 2 :=
    huc.comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
  set σ := coshCharge ω (Ioo b c)
  set m : ℝ → ℝ := fun x => riemannKernelReal x * ω x * Real.cosh (x / 2)
  have hiD : Integrable fun x => u x ^ 2 * ω x * markovDefect ω x :=
    (((huc'.pow 2).mul hω.continuous).mul hD).integrable_of_hasCompactSupport
      (hsupp2.mul_right.mul_right)
  have hic : Integrable fun x => u x ^ 2 * m x :=
    ((huc'.pow 2).mul (continuous_mul_cosh hω.continuous)).integrable_of_hasCompactSupport
      hsupp2.mul_right
  have hpot : -(2 * σ * (∫ x, u x ^ 2 * m x)) ≤ ∫ x, u x ^ 2 * ω x * markovDefect ω x := by
    have hadd : 0 ≤ ∫ x, (u x ^ 2 * ω x * markovDefect ω x + 2 * σ * (u x ^ 2 * m x)) := by
      refine integral_nonneg fun x => ?_
      by_cases hx : x ∈ Ioo b c
      · have h := mul_nonneg (sq_nonneg (u x)) (hsub x hx)
        have e : u x ^ 2 * ω x * markovDefect ω x + 2 * σ * (u x ^ 2 * m x) =
            u x ^ 2 * (ω x * (markovDefect ω x + 2 * σ *
              (riemannKernelReal x * Real.cosh (x / 2)))) := by simp only [m]; ring
        rw [e]; exact h
      · simp [hub x hx]
    rw [integral_add hiD (hic.const_mul _), integral_const_mul] at hadd
    linarith
  unfold fullZeroForm chargeVariance
  rw [markovEnergy_phiDoob_mul_eq_signedJump_add_defect hω hωc hu huc,
    evenPoleMoment_phiDoob_mul]
  have hσ : σ = ∫ x in Ioo b c, m x := rfl
  rw [← hσ]
  nlinarith

end GaloisForLFunctions.SignedWindowCriticality

end
