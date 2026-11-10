import GaloisForLFunctions.RHTower.XiNewtonSchwarzPickCriticalLine

/-!
# A defect of index one is pure off the real axis

Let `θ` be holomorphic with `‖θ‖ ≤ 1` on the half-plane `Re s > ½` (a Schur function). A completed
function `F = E + E♯` whose Hermite–Biehler half `E` has one zero or pole `w` on the wrong side
vanishes right of the line exactly where `θ = E♯/E` meets the defect factor

`b_w(s) = (s − w) / (s − (1 − w̄))`

up to a unimodular constant `c`. The defect factor is a conformal map of the half-plane onto the unit
disc, so `θ = c · b_w` is a fixed-point equation for a holomorphic self-map of the disc.

* `eqOn_of_two_agreements`: two distinct solutions force `θ = c · b_w` on the whole half-plane
  (Schwarz–Pick: a self-map of the disc with two fixed points is the identity).
* `agreement_subsingleton`: if `θ ≠ c · b_w` somewhere, there is at most one solution.
* `im_eq_zero_of_agreement`: if moreover `θ`, `w` and `c` are real, the solution is real, because a
  non-real solution comes with its complex conjugate.

So a defect of index one admits at most one exceptional point on each side, and complex conjugation,
which acts freely on non-real exceptional points, leaves no room for a non-real one.
-/

open Complex Set Metric

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open RHTower.XiNewtonCriticalLine

/-- The open half-plane right of the centre line `Re s = ½`. -/
def rightHalf : Set ℂ := {s | 1 / 2 < s.re}

theorem isOpen_rightHalf : IsOpen rightHalf :=
  isOpen_lt continuous_const Complex.continuous_re

theorem conj_mem_rightHalf {s : ℂ} (hs : s ∈ rightHalf) : (starRingEnd ℂ) s ∈ rightHalf := by
  simpa [rightHalf] using hs

/-- The defect factor of a point `w`: `b_w(s) = (s − w) / (s − (1 − w̄))`. -/
noncomputable def defectFactor (w s : ℂ) : ℂ := (s - w) / (s - (1 - (starRingEnd ℂ) w))

/-- The inverse of the defect factor: `ζ ↦ (w − ζ (1 − w̄)) / (1 − ζ)`. -/
noncomputable def defectInv (w ζ : ℂ) : ℂ := (w - ζ * (1 - (starRingEnd ℂ) w)) / (1 - ζ)

theorem defect_denom_ne_zero {w s : ℂ} (hw : w ∈ rightHalf) (hs : s ∈ rightHalf) :
    s - (1 - (starRingEnd ℂ) w) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [sub_re, one_re, conj_re, zero_re] at hre
  have h1 : (1 : ℝ) / 2 < w.re := hw
  have h2 : (1 : ℝ) / 2 < s.re := hs
  linarith

/-- `|s − (1 − w̄)|² − |s − w|² = (2 Re w − 1)(2 Re s − 1)`. -/
theorem normSq_defect_identity (w s : ℂ) :
    Complex.normSq (s - (1 - (starRingEnd ℂ) w)) - Complex.normSq (s - w) =
      (2 * w.re - 1) * (2 * s.re - 1) := by
  simp only [Complex.normSq_apply, sub_re, sub_im, one_re, one_im, conj_re, conj_im]
  ring

/-- The defect factor maps the half-plane into the unit disc. -/
theorem defectFactor_mem_ball {w s : ℂ} (hw : w ∈ rightHalf) (hs : s ∈ rightHalf) :
    defectFactor w s ∈ ball (0 : ℂ) 1 := by
  have hD := defect_denom_ne_zero hw hs
  have hDpos : 0 < ‖s - (1 - (starRingEnd ℂ) w)‖ := norm_pos_iff.mpr hD
  rw [mem_ball_zero_iff, defectFactor, norm_div, div_lt_one hDpos]
  have hid := normSq_defect_identity w s
  have h1 : (1 : ℝ) / 2 < w.re := hw
  have h2 : (1 : ℝ) / 2 < s.re := hs
  have hpos : 0 < (2 * w.re - 1) * (2 * s.re - 1) := by nlinarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hid
  nlinarith [norm_nonneg (s - w), norm_nonneg (s - (1 - (starRingEnd ℂ) w))]

theorem one_sub_ne_zero_of_mem_ball {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) : 1 - ζ ≠ 0 := by
  intro h
  have h1 : ζ = 1 := by linear_combination -h
  rw [h1, mem_ball_zero_iff, norm_one] at hζ
  exact lt_irrefl _ hζ

/-- `Re (defectInv w ζ) − ½ = (1 − |ζ|²)(Re w − ½) / |1 − ζ|²`. -/
theorem defectInv_re (w : ℂ) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    (defectInv w ζ).re - 1 / 2 =
      (1 - Complex.normSq ζ) * (w.re - 1 / 2) / Complex.normSq (1 - ζ) := by
  have hne := one_sub_ne_zero_of_mem_ball hζ
  have hN : Complex.normSq (1 - ζ) ≠ 0 := fun h => hne (Complex.normSq_eq_zero.mp h)
  have hNval : Complex.normSq (1 - ζ) = (1 - ζ.re) ^ 2 + ζ.im ^ 2 := by
    simp only [Complex.normSq_apply, sub_re, sub_im, one_re, one_im]
    ring
  rw [defectInv, Complex.div_re, ← add_div, eq_div_iff hN, sub_mul, div_mul_cancel₀ _ hN, hNval]
  simp only [Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, one_re, one_im, conj_re,
    conj_im]
  ring

/-- The inverse maps the unit disc into the half-plane. -/
theorem defectInv_mem_rightHalf {w ζ : ℂ} (hw : w ∈ rightHalf) (hζ : ζ ∈ ball (0 : ℂ) 1) :
    defectInv w ζ ∈ rightHalf := by
  have hne := one_sub_ne_zero_of_mem_ball hζ
  have hN : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr hne
  have hζ1 : Complex.normSq ζ < 1 := by
    have := mem_ball_zero_iff.mp hζ
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ζ]
  have h1 : (1 : ℝ) / 2 < w.re := hw
  have hre := defectInv_re w hζ
  have hpos : 0 < (1 - Complex.normSq ζ) * (w.re - 1 / 2) / Complex.normSq (1 - ζ) :=
    div_pos (mul_pos (by linarith) (by linarith)) hN
  show (1 : ℝ) / 2 < (defectInv w ζ).re
  linarith

theorem defectInv_defectFactor {w s : ℂ} (hw : w ∈ rightHalf) (hs : s ∈ rightHalf) :
    defectInv w (defectFactor w s) = s := by
  have hD := defect_denom_ne_zero hw hs
  have hw2 : (2 : ℂ) * w.re - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [sub_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
      one_re, zero_re] at hre
    have h1 : (1 : ℝ) / 2 < w.re := hw
    linarith
  have hsum : w + (starRingEnd ℂ) w = 2 * w.re := by
    rw [Complex.add_conj]
    push_cast
    ring
  have h1 : 1 - defectFactor w s =
      (w + (starRingEnd ℂ) w - 1) / (s - (1 - (starRingEnd ℂ) w)) := by
    rw [defectFactor]
    field_simp
    ring
  have hne : w + (starRingEnd ℂ) w - 1 ≠ 0 := by rw [hsum]; exact hw2
  rw [defectInv, h1, defectFactor]
  field_simp
  ring

theorem defectFactor_defectInv {w ζ : ℂ} (hw : w ∈ rightHalf) (hζ : ζ ∈ ball (0 : ℂ) 1) :
    defectFactor w (defectInv w ζ) = ζ := by
  have hne := one_sub_ne_zero_of_mem_ball hζ
  have hD := defect_denom_ne_zero hw (defectInv_mem_rightHalf hw hζ)
  have hsum : w + (starRingEnd ℂ) w = 2 * w.re := by
    rw [Complex.add_conj]
    push_cast
    ring
  have hw2 : w + (starRingEnd ℂ) w - 1 ≠ 0 := by
    rw [hsum]
    intro h
    have hre := congrArg Complex.re h
    simp only [sub_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero,
      one_re, zero_re] at hre
    have h1 : (1 : ℝ) / 2 < w.re := hw
    linarith
  have hden : defectInv w ζ - (1 - (starRingEnd ℂ) w) =
      (w + (starRingEnd ℂ) w - 1) / (1 - ζ) := by
    rw [defectInv]
    field_simp
    ring
  have hnum : defectInv w ζ - w = ζ * (w + (starRingEnd ℂ) w - 1) / (1 - ζ) := by
    rw [defectInv]
    field_simp
    ring
  rw [defectFactor, hden, hnum]
  field_simp

theorem differentiableOn_defectInv (w : ℂ) : DifferentiableOn ℂ (defectInv w) (ball 0 1) := by
  intro ζ hζ
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun ζ => (w - ζ * (1 - (starRingEnd ℂ) w)) / (1 - ζ)) ζ
  exact (by fun_prop : DifferentiableAt ℂ (fun ζ : ℂ => w - ζ * (1 - (starRingEnd ℂ) w)) ζ).div
    (by fun_prop) (one_sub_ne_zero_of_mem_ball hζ)

/-- For a real point `w` the defect factor commutes with complex conjugation. -/
theorem defectFactor_conj {w : ℂ} (hw : (starRingEnd ℂ) w = w) (s : ℂ) :
    defectFactor w ((starRingEnd ℂ) s) = (starRingEnd ℂ) (defectFactor w s) := by
  simp only [defectFactor, map_div₀, map_sub, map_one, hw]

/-- **Two agreements force identity.** A Schur function on the half-plane that meets `c · b_w`,
`‖c‖ = 1`, at two distinct points equals it everywhere on the half-plane. -/
theorem eqOn_of_two_agreements {θ : ℂ → ℂ} {w c : ℂ}
    (hθ : DifferentiableOn ℂ θ rightHalf) (hb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1)
    (hw : w ∈ rightHalf) (hc : ‖c‖ = 1)
    {s₁ s₂ : ℂ} (h₁ : s₁ ∈ rightHalf) (h₂ : s₂ ∈ rightHalf) (hne : s₁ ≠ s₂)
    (e₁ : θ s₁ = c * defectFactor w s₁) (e₂ : θ s₂ = c * defectFactor w s₂) :
    EqOn θ (fun s => c * defectFactor w s) rightHalf := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  -- the self-map of the disc
  set g : ℂ → ℂ := fun ζ => c⁻¹ * θ (defectInv w ζ) with hg
  have hgd : DifferentiableOn ℂ g (ball 0 1) := by
    have hcomp : DifferentiableOn ℂ (fun ζ => θ (defectInv w ζ)) (ball 0 1) :=
      hθ.comp (differentiableOn_defectInv w) (fun ζ hζ => defectInv_mem_rightHalf hw hζ)
    exact hcomp.const_mul c⁻¹
  have hgle : ∀ ζ ∈ ball (0 : ℂ) 1, ‖g ζ‖ ≤ 1 := by
    intro ζ hζ
    rw [hg]
    simp only [norm_mul, norm_inv, hc, inv_one, one_mul]
    exact hb _ (defectInv_mem_rightHalf hw hζ)
  -- the two fixed points
  set ζ₁ := defectFactor w s₁ with hζ₁
  set ζ₂ := defectFactor w s₂ with hζ₂
  have hm₁ : ζ₁ ∈ ball (0 : ℂ) 1 := defectFactor_mem_ball hw h₁
  have hm₂ : ζ₂ ∈ ball (0 : ℂ) 1 := defectFactor_mem_ball hw h₂
  have hfix₁ : g ζ₁ = ζ₁ := by
    rw [hg]
    simp only
    rw [hζ₁, defectInv_defectFactor hw h₁, e₁, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hfix₂ : g ζ₂ = ζ₂ := by
    rw [hg]
    simp only
    rw [hζ₂, defectInv_defectFactor hw h₂, e₂, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hζne : ζ₁ ≠ ζ₂ := by
    intro h
    apply hne
    rw [← defectInv_defectFactor hw h₁, ← defectInv_defectFactor hw h₂, ← hζ₁, ← hζ₂, h]
  -- maximum modulus: `g` maps the disc into the open disc
  have hmaps : MapsTo g (ball 0 1) (ball 0 1) := by
    intro ζ hζ
    rw [mem_ball_zero_iff]
    rcases (hgle ζ hζ).lt_or_eq with h | h
    · exact h
    · exfalso
      have hmax : IsMaxOn (norm ∘ g) (ball 0 1) ζ := by
        intro z hz
        show ‖g z‖ ≤ ‖g ζ‖
        rw [h]
        exact hgle z hz
      have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
        (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hgd hζ hmax
      have h1 : g ζ₁ = g ζ := hconst hm₁
      rw [hfix₁] at h1
      have h2 : ‖ζ₁‖ < 1 := mem_ball_zero_iff.mp hm₁
      rw [h1, h] at h2
      exact lt_irrefl _ h2
  have hid := eqOn_id_of_two_fixedPoints one_pos hgd hmaps hm₁ hm₂ hζne hfix₁ hfix₂
  intro s hs
  have hm : defectFactor w s ∈ ball (0 : ℂ) 1 := defectFactor_mem_ball hw hs
  have h := hid hm
  rw [hg] at h
  simp only [id] at h
  rw [defectInv_defectFactor hw hs] at h
  show θ s = c * defectFactor w s
  rw [← h, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

/-- **At most one exceptional point.** If the Schur function `θ` differs from `c · b_w` somewhere on
the half-plane, the equation `θ = c · b_w` has at most one solution there. -/
theorem agreement_subsingleton {θ : ℂ → ℂ} {w c : ℂ}
    (hθ : DifferentiableOn ℂ θ rightHalf) (hb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1)
    (hw : w ∈ rightHalf) (hc : ‖c‖ = 1)
    (hdiff : ∃ z ∈ rightHalf, θ z ≠ c * defectFactor w z) :
    {s | s ∈ rightHalf ∧ θ s = c * defectFactor w s}.Subsingleton := by
  rintro s₁ ⟨h₁, e₁⟩ s₂ ⟨h₂, e₂⟩
  by_contra hne
  obtain ⟨z, hz, hzne⟩ := hdiff
  exact hzne (eqOn_of_two_agreements hθ hb hw hc h₁ h₂ hne e₁ e₂ hz)

/-- **Purity by parity.** Let `θ` be a real Schur function on the half-plane, `w` a real point and
`c` a real unimodular constant. If `θ ≠ c · b_w` somewhere, every solution of `θ = c · b_w` in the
half-plane is real: a non-real solution and its conjugate would be two solutions. -/
theorem im_eq_zero_of_agreement {θ : ℂ → ℂ} {w c : ℂ}
    (hθ : DifferentiableOn ℂ θ rightHalf) (hb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1)
    (hreal : ∀ s ∈ rightHalf, θ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (θ s))
    (hw : w ∈ rightHalf) (hwr : (starRingEnd ℂ) w = w) (hc : ‖c‖ = 1)
    (hcr : (starRingEnd ℂ) c = c)
    (hdiff : ∃ z ∈ rightHalf, θ z ≠ c * defectFactor w z)
    {s : ℂ} (hs : s ∈ rightHalf) (e : θ s = c * defectFactor w s) : s.im = 0 := by
  by_contra him
  have hconj : θ ((starRingEnd ℂ) s) = c * defectFactor w ((starRingEnd ℂ) s) := by
    rw [hreal s hs, e, map_mul, hcr, defectFactor_conj hwr]
  have hne : s ≠ (starRingEnd ℂ) s := by
    intro h
    exact him (Complex.conj_eq_iff_im.mp h.symm)
  exact hne (agreement_subsingleton hθ hb hw hc hdiff ⟨hs, e⟩ ⟨conj_mem_rightHalf hs, hconj⟩)

/-- **Hermite–Biehler sums with one real defect.** Let `E`, `E'` be holomorphic on the half-plane
with `E ≠ 0` and `‖E'‖ ≤ ‖E‖` there, both commuting with complex conjugation, let `w > ½` be real
and `c = ±1`. If `F(s) = (s − w) E(s) − c (s − (1 − w)) E'(s)` does not vanish identically on the
half-plane, then `F` has at most one zero there and that zero is real. -/
theorem hermiteBiehler_indexOne {E E' : ℂ → ℂ} {w c : ℂ}
    (hE : DifferentiableOn ℂ E rightHalf) (hE' : DifferentiableOn ℂ E' rightHalf)
    (hne : ∀ s ∈ rightHalf, E s ≠ 0) (hle : ∀ s ∈ rightHalf, ‖E' s‖ ≤ ‖E s‖)
    (hEr : ∀ s ∈ rightHalf, E ((starRingEnd ℂ) s) = (starRingEnd ℂ) (E s))
    (hE'r : ∀ s ∈ rightHalf, E' ((starRingEnd ℂ) s) = (starRingEnd ℂ) (E' s))
    (hw : w ∈ rightHalf) (hwr : (starRingEnd ℂ) w = w) (hc : ‖c‖ = 1)
    (hcr : (starRingEnd ℂ) c = c)
    (hdiff : ∃ z ∈ rightHalf, (z - w) * E z - c * (z - (1 - w)) * E' z ≠ 0) :
    {s | s ∈ rightHalf ∧ (s - w) * E s - c * (s - (1 - w)) * E' s = 0}.Subsingleton ∧
      ∀ s ∈ rightHalf, (s - w) * E s - c * (s - (1 - w)) * E' s = 0 → s.im = 0 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  have hcc : c * c = 1 := by
    have h1 : c * (starRingEnd ℂ) c = ((Complex.normSq c : ℝ) : ℂ) := Complex.mul_conj c
    rw [hcr, Complex.normSq_eq_norm_sq, hc] at h1
    simpa using h1
  -- the Schur function `θ = E'/E` and the constant `c⁻¹ = c`
  set θ : ℂ → ℂ := fun s => E' s / E s with hθdef
  have hθ : DifferentiableOn ℂ θ rightHalf := hE'.div hE hne
  have hθb : ∀ s ∈ rightHalf, ‖θ s‖ ≤ 1 := by
    intro s hs
    rw [hθdef]
    simp only [norm_div]
    exact div_le_one_of_le₀ (hle s hs) (norm_nonneg _)
  have hθr : ∀ s ∈ rightHalf, θ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (θ s) := by
    intro s hs
    rw [hθdef]
    simp only [map_div₀, hEr s hs, hE'r s hs]
  -- zeros of `F` are agreements of `θ` with `c · b_w`
  have key : ∀ s ∈ rightHalf, ((s - w) * E s - c * (s - (1 - w)) * E' s = 0 ↔
      θ s = c * defectFactor w s) := by
    intro s hs
    have hD : s - (1 - w) ≠ 0 := by
      have := defect_denom_ne_zero hw hs
      rwa [hwr] at this
    have hEs := hne s hs
    rw [hθdef, defectFactor, hwr]
    simp only
    constructor
    · intro h
      have h1 : c * (s - (1 - w)) * E' s = (s - w) * E s := by linear_combination -h
      field_simp
      linear_combination c * h1 + (-(s - (1 - w)) * E' s) * hcc
    · intro h
      field_simp at h
      linear_combination (-c) * h - ((s - w) * E s) * hcc
  have hdiff' : ∃ z ∈ rightHalf, θ z ≠ c * defectFactor w z := by
    obtain ⟨z, hz, hzne⟩ := hdiff
    exact ⟨z, hz, fun h => hzne ((key z hz).mpr h)⟩
  refine ⟨?_, ?_⟩
  · rintro s₁ ⟨h₁, e₁⟩ s₂ ⟨h₂, e₂⟩
    exact agreement_subsingleton hθ hθb hw hc hdiff' ⟨h₁, (key s₁ h₁).mp e₁⟩
      ⟨h₂, (key s₂ h₂).mp e₂⟩
  · intro s hs e
    exact im_eq_zero_of_agreement hθ hθb hθr hw hwr hc hcr hdiff' hs ((key s hs).mp e)

end GaloisForLFunctions.InfiniteRankPurityTheory
