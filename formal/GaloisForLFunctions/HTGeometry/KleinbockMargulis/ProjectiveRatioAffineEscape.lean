import GaloisForLFunctions.HTGeometry.KleinbockMargulis.AnalyticNondegeneracy
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.FirstReturnExponent

/-!
# Projective spectral ratios preserve affine escape

Normalizing a finite spectrum by two anchor levels removes translation and
scale. Any constant linear relation among the remaining projective ratios
clears its denominator to a balanced constant-coefficient relation among
the raw levels. Thus affine escape of raw spectral actions implies
Kleinbock--Margulis affine fullness of the projective ratio map.
-/

open scoped BigOperators
open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def projectiveTailIndex {r : ℕ} (j : Fin r) : Fin (r + 2) :=
  j.succ.succ

def anchoredProjectiveRatio {r : ℕ} {P : Type*}
    (energy : Fin (r + 2) → P → ℝ) (p : P) (j : Fin r) : ℝ :=
  (energy (projectiveTailIndex j) p - energy 0 p) /
    (energy 1 p - energy 0 p)

def projectiveAffineCoefficient {r : ℕ}
    (w : Fin r → ℝ) (target : ℝ) : Fin (r + 2) → ℝ :=
  Fin.cons (target - ∑ j, w j) (Fin.cons (-target) w)

theorem sum_projectiveAffineCoefficient {r : ℕ}
    (w : Fin r → ℝ) (target : ℝ) :
    ∑ i, projectiveAffineCoefficient w target i = 0 := by
  simp [projectiveAffineCoefficient, Fin.sum_univ_succ]

theorem projectiveAffineCoefficient_not_constant {r : ℕ}
    {w : Fin r → ℝ} (hw : w ≠ 0) (target : ℝ) :
    ¬ ∀ x y, projectiveAffineCoefficient w target x =
      projectiveAffineCoefficient w target y := by
  intro hconstant
  have hzero : projectiveAffineCoefficient w target = 0 := by
    have hsum := sum_projectiveAffineCoefficient w target
    let x₀ : Fin (r + 2) := 0
    have hcard : (Fintype.card (Fin (r + 2)) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin (r + 2)) ≠ 0)
    have hx₀ : projectiveAffineCoefficient w target x₀ = 0 := by
      have hmul : (Fintype.card (Fin (r + 2)) : ℝ) *
          projectiveAffineCoefficient w target x₀ = 0 := by
        calc
          (Fintype.card (Fin (r + 2)) : ℝ) *
              projectiveAffineCoefficient w target x₀ =
              ∑ _i : Fin (r + 2), projectiveAffineCoefficient w target x₀ := by
                symm
                simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ∑ i, projectiveAffineCoefficient w target i := by
                apply Finset.sum_congr rfl
                intro i _hi
                exact (hconstant i x₀).symm
          _ = 0 := hsum
      exact (mul_eq_zero.mp hmul).resolve_left hcard
    funext i
    rw [hconstant i x₀, hx₀]
    rfl
  apply hw
  funext j
  have hj := congrFun hzero (projectiveTailIndex j)
  simpa [projectiveAffineCoefficient, projectiveTailIndex] using hj

theorem sum_projectiveAffineCoefficient_mul_energy
    {r : ℕ} {P : Type*}
    (energy : Fin (r + 2) → P → ℝ)
    (p : P) (w : Fin r → ℝ) (target : ℝ)
    (hden : energy 1 p - energy 0 p ≠ 0) :
    ∑ i, projectiveAffineCoefficient w target i * energy i p =
      (energy 1 p - energy 0 p) *
        ((∑ j, w j * anchoredProjectiveRatio energy p j) - target) := by
  simp only [projectiveAffineCoefficient, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, projectiveTailIndex,
    anchoredProjectiveRatio]
  rw [mul_sub, Finset.mul_sum]
  have hterm : ∀ j : Fin r,
      (energy 1 p - energy 0 p) *
          (w j * ((energy j.succ.succ p - energy 0 p) /
            (energy 1 p - energy 0 p))) =
        w j * (energy j.succ.succ p - energy 0 p) := by
    intro j
    field_simp [hden]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  have hsum :
      (∑ j, w j * (energy j.succ.succ p - energy 0 p)) =
        (∑ j, w j * energy j.succ.succ p) -
          (∑ j, w j) * energy 0 p := by
    calc
      (∑ j, w j * (energy j.succ.succ p - energy 0 p)) =
          ∑ j, (w j * energy j.succ.succ p - w j * energy 0 p) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j, w j * energy j.succ.succ p) -
          ∑ j, w j * energy 0 p := by
            rw [← Finset.sum_sub_distrib]
      _ = (∑ j, w j * energy j.succ.succ p) -
          (∑ j, w j) * energy 0 p := by rw [Finset.sum_mul]
  rw [hsum]
  have hone : (Fin.succ 0 : Fin (r + 2)) = 1 := rfl
  rw [hone]
  ring

/-- If every nonconstant raw spectral action escapes every constant on a
parameter set, no nonzero linear combination of anchored projective ratios
can be constant there. -/
theorem noConstantCombination_anchoredProjectiveRatio_of_affineEscape
    {r : ℕ} {P : Type*} {U : Set P}
    (energy : Fin (r + 2) → P → ℝ)
    (p₀ : P) (hp₀ : p₀ ∈ U)
    (hden : ∀ p ∈ U, energy 1 p - energy 0 p ≠ 0)
    (hescape : ∀ c : Fin (r + 2) → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ p ∈ U, (∑ i, c i * energy i p) ≠ target) :
    ∀ w : Fin r → ℝ,
      (∀ x ∈ U, ∀ y ∈ U,
        ∑ j, w j * anchoredProjectiveRatio energy x j =
          ∑ j, w j * anchoredProjectiveRatio energy y j) →
      w = 0 := by
  intro w hconstant
  by_contra hw
  let target : ℝ :=
    ∑ j, w j * anchoredProjectiveRatio energy p₀ j
  let c := projectiveAffineCoefficient w target
  obtain ⟨p, hpU, hpne⟩ :=
    hescape c (projectiveAffineCoefficient_not_constant hw target) 0
  have hratio :
      ∑ j, w j * anchoredProjectiveRatio energy p j = target := by
    exact hconstant p hpU p₀ hp₀
  have hzero : ∑ i, c i * energy i p = 0 := by
    rw [sum_projectiveAffineCoefficient_mul_energy
      energy p w target (hden p hpU), hratio, sub_self, mul_zero]
  exact hpne hzero

/-- Analytic affine escape of raw levels implies simultaneous extremality
of the anchored projective spectral-ratio map. -/
theorem volume_vwa_anchoredProjectiveRatio_eq_zero_of_affineEscape
    {d r : ℕ} [NeZero d] (hr : 0 < r)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (energy : Fin (r + 2) → (Fin d → ℝ) → ℝ)
    (henergy : ∀ i, AnalyticOnNhd ℝ (energy i) U)
    (p₀ : Fin d → ℝ) (hp₀ : p₀ ∈ U)
    (hden : ∀ p ∈ U, energy 1 p - energy 0 p ≠ 0)
    (hescape : ∀ c : Fin (r + 2) → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ p ∈ U, (∑ i, c i * energy i p) ≠ target) :
    volume {p ∈ U |
      KleinbockMargulis.VWA
        (fun j => anchoredProjectiveRatio energy p j)} = 0 := by
  apply KleinbockMargulis.theoremA_analytic hr hU hUc
  · intro p hp
    apply AnalyticAt.pi
    intro j
    exact ((henergy (projectiveTailIndex j) p hp).sub
      (henergy 0 p hp)).div
        ((henergy 1 p hp).sub (henergy 0 p hp)) (hden p hp)
  · exact noConstantCombination_anchoredProjectiveRatio_of_affineEscape
      energy p₀ hp₀ hden hescape

/-- Analytic affine escape gives the optimal continuous first-return lower
exponent for almost every parameter in the same physical chart. -/
theorem volume_not_optimalReturn_anchoredProjectiveRatio_eq_zero_of_affineEscape
    {d r : ℕ} [NeZero d] (hr : 0 < r)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (energy : Fin (r + 2) → (Fin d → ℝ) → ℝ)
    (henergy : ∀ i, AnalyticOnNhd ℝ (energy i) U)
    (p₀ : Fin d → ℝ) (hp₀ : p₀ ∈ U)
    (hden : ∀ p ∈ U, energy 1 p - energy 0 p ≠ 0)
    (hescape : ∀ c : Fin (r + 2) → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ p ∈ U, (∑ i, c i * energy i p) ≠ target) :
    volume {p ∈ U |
      ¬ KleinbockMargulis.HasOptimalContinuousReturnLower
        (fun j => anchoredProjectiveRatio energy p j)} = 0 := by
  refine measure_mono_null (fun p hp => ?_)
    (volume_vwa_anchoredProjectiveRatio_eq_zero_of_affineEscape
      hr hU hUc energy henergy p₀ hp₀ hden hescape)
  rcases hp with ⟨hpU, hpbad⟩
  refine ⟨hpU, ?_⟩
  by_contra hvwa
  exact hpbad
    (KleinbockMargulis.hasOptimalContinuousReturnLower_of_not_vwa
      hr hvwa)

/-! ## Physical-time spectral recurrence -/

/-- The complete packet of gaps from the first labelled energy level. -/
def anchoredSpectralGapPacket {r : ℕ} {P : Type*}
    (energy : Fin (r + 2) → P → ℝ) (p : P) : Fin (r + 1) → ℝ :=
  fun j => energy j.succ p - energy 0 p

@[simp] theorem anchoredSpectralGapPacket_zero {r : ℕ} {P : Type*}
    (energy : Fin (r + 2) → P → ℝ) (p : P) :
    anchoredSpectralGapPacket energy p 0 = energy 1 p - energy 0 p := rfl

@[simp] theorem gapRatio_anchoredSpectralGapPacket_succ
    {r : ℕ} {P : Type*}
    (energy : Fin (r + 2) → P → ℝ) (p : P) (j : Fin r) :
    gapRatio (anchoredSpectralGapPacket energy p) j.succ =
      anchoredProjectiveRatio energy p j := by
  rfl

/-- The projective-ratio packet bounds every ratio in the physical gap
packet, including its unit anchor. -/
theorem abs_gapRatio_anchoredSpectralGapPacket_le
    {r : ℕ} {P : Type*}
    (energy : Fin (r + 2) → P → ℝ) (p : P)
    (hden : energy 1 p - energy 0 p ≠ 0)
    (j : Fin (r + 1)) :
    |gapRatio (anchoredSpectralGapPacket energy p) j| ≤
      KleinbockMargulis.unitAnchoredRatioBound
        (fun k => anchoredProjectiveRatio energy p k) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [gapRatio_zero _ hden]
    simp only [abs_one, KleinbockMargulis.unitAnchoredRatioBound]
    have hsum : 0 ≤ ∑ k, |anchoredProjectiveRatio energy p k| :=
      Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  · rw [gapRatio_anchoredSpectralGapPacket_succ]
    simp only [KleinbockMargulis.unitAnchoredRatioBound]
    have hk : |anchoredProjectiveRatio energy p k| ≤
        ∑ j, |anchoredProjectiveRatio energy p j| :=
      Finset.single_le_sum
        (fun j _ => abs_nonneg (anchoredProjectiveRatio energy p j))
        (Finset.mem_univ k)
    linarith

/-- Optimal lower first-return exponent stated in the Hamiltonian's actual
time and energy units.  Translation is removed by anchoring one level;
scale remains explicitly in the elapsed-time term through the first gap. -/
def HasOptimalPhysicalContinuousReturnLower
    {r : ℕ} {P : Type*}
    (energy : Fin (r + 2) → P → ℝ) (p : P) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ Q : ℕ, ∀ {radius time : ℝ},
    (Q : ℝ) + radius ≤
      |gapTurn (anchoredSpectralGapPacket energy p) time 0| →
    ContinuousReturn (anchoredSpectralGapPacket energy p) radius time →
    (radius * (1 + KleinbockMargulis.unitAnchoredRatioBound
        (fun j => anchoredProjectiveRatio energy p j))) ^
        (-(1 / (((r : ℝ))⁻¹ + eta))) <
      |time| * |energy 1 p - energy 0 p| / (2 * Real.pi) + radius

/-- Non-VWA projective ratios give the optimal first-return lower exponent
in the original Hamiltonian's physical time and energy units. -/
theorem hasOptimalPhysicalContinuousReturnLower_of_not_vwa
    {r : ℕ} (hr : 0 < r) {P : Type*}
    (energy : Fin (r + 2) → P → ℝ) (p : P)
    (hden : energy 1 p - energy 0 p ≠ 0)
    (hvwa : ¬ KleinbockMargulis.VWA
      (fun j => anchoredProjectiveRatio energy p j)) :
    HasOptimalPhysicalContinuousReturnLower energy p := by
  intro eta heta
  simpa only [anchoredSpectralGapPacket_zero] using
    (KleinbockMargulis.eventually_continuousReturn_lower_of_not_vwa
      hr (anchoredSpectralGapPacket energy p) hden
      (abs_gapRatio_anchoredSpectralGapPacket_le energy p hden)
      (by simpa only [gapRatio_anchoredSpectralGapPacket_succ] using hvwa)
      heta)

/-- Analytic affine escape gives the optimal lower return exponent in
actual physical time for almost every Hamiltonian in the same chart. -/
theorem volume_not_optimalPhysicalReturn_eq_zero_of_affineEscape
    {d r : ℕ} [NeZero d] (hr : 0 < r)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (energy : Fin (r + 2) → (Fin d → ℝ) → ℝ)
    (henergy : ∀ i, AnalyticOnNhd ℝ (energy i) U)
    (p₀ : Fin d → ℝ) (hp₀ : p₀ ∈ U)
    (hden : ∀ p ∈ U, energy 1 p - energy 0 p ≠ 0)
    (hescape : ∀ c : Fin (r + 2) → ℝ,
      (¬ ∀ x y, c x = c y) → ∀ target : ℝ,
        ∃ p ∈ U, (∑ i, c i * energy i p) ≠ target) :
    volume {p ∈ U |
      ¬ HasOptimalPhysicalContinuousReturnLower energy p} = 0 := by
  refine measure_mono_null (fun p hp => ?_)
    (volume_vwa_anchoredProjectiveRatio_eq_zero_of_affineEscape
      hr hU hUc energy henergy p₀ hp₀ hden hescape)
  rcases hp with ⟨hpU, hpbad⟩
  refine ⟨hpU, ?_⟩
  by_contra hvwa
  exact hpbad (hasOptimalPhysicalContinuousReturnLower_of_not_vwa
    hr energy p (hden p hpU) hvwa)

end

end GaloisForLFunctions.HTGeometry
