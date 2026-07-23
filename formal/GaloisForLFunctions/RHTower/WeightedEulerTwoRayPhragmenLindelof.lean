import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Two-ray Phragmén–Lindelöf bound for exponential-type functions

An entire function of exponential type `τ` that
decays like `e^{-ε|x|}` on **both** real rays satisfies the global bound

`‖g z‖ ≤ K · e^{-ε|Re z| + τ|Im z|}`.

This is the quantitative half of the classical indicator inequality
`h(0) + h(π) ≥ 0`: it will feed the Paley–Wiener contour-shift argument that
forces such a function to vanish identically, which — applied to the
Fourier–Borel transform of `B = A - R_*A` with the ray decay supplied by the
oversampling lemma and Möbius transfer — is exactly the carrier
separation `B = 0`.

The proof multiplies `g` by the exponential `e^{mz}` adapted to each
coordinate quadrant and applies mathlib's Phragmén–Lindelöf principle there.
Everything is unconditional.
-/

noncomputable section

namespace RHTower

open Complex Set Filter Asymptotics Bornology

private theorem norm_mul_exp (g : ℂ → ℂ) (m z : ℂ) :
    ‖g z * Complex.exp (m * z)‖ = ‖g z‖ * Real.exp ((m * z).re) := by
  rw [norm_mul, Complex.norm_exp]

private theorem re_mul_ofReal (m : ℂ) (x : ℝ) : (m * (x : ℂ)).re = m.re * x := by
  simp [Complex.mul_re]

private theorem re_mul_ofReal_mul_I (m : ℂ) (x : ℝ) :
    (m * ((x : ℂ) * I)).re = -(m.im * x) := by
  simp [Complex.mul_re]

/-- The multiplied function inherits an exponential-type big-O bound on any
filter from the global growth bound on `g`. -/
private theorem isBigO_mul_exp {g : ℂ → ℂ} {A τ : ℝ} (hA : 0 ≤ A)
    (hgrow : ∀ z : ℂ, ‖g z‖ ≤ A * Real.exp (τ * ‖z‖)) (m : ℂ) (l : Filter ℂ) :
    (fun z => g z * Complex.exp (m * z))
      =O[l] fun z => Real.exp ((τ + ‖m‖) * ‖z‖ ^ (1 : ℝ)) := by
  refine IsBigO.of_bound A (Eventually.of_forall fun z => ?_)
  rw [norm_mul_exp]
  have h1 : (m * z).re ≤ ‖m‖ * ‖z‖ := by
    calc (m * z).re ≤ ‖m * z‖ := Complex.re_le_norm _
      _ = ‖m‖ * ‖z‖ := norm_mul _ _
  have h2 : ‖g z‖ * Real.exp ((m * z).re)
      ≤ (A * Real.exp (τ * ‖z‖)) * Real.exp (‖m‖ * ‖z‖) := by
    apply mul_le_mul (hgrow z) (Real.exp_le_exp.2 h1) (Real.exp_nonneg _)
    positivity
  calc ‖g z‖ * Real.exp ((m * z).re)
      ≤ (A * Real.exp (τ * ‖z‖)) * Real.exp (‖m‖ * ‖z‖) := h2
    _ = A * Real.exp ((τ + ‖m‖) * ‖z‖) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ = A * ‖Real.exp ((τ + ‖m‖) * ‖z‖ ^ (1 : ℝ))‖ := by
        rw [Real.rpow_one, Real.norm_of_nonneg (Real.exp_nonneg _)]

private theorem norm_le_of_mul_exp_le {g : ℂ → ℂ} {m z : ℂ} {M : ℝ}
    (h : ‖g z * Complex.exp (m * z)‖ ≤ M) :
    ‖g z‖ ≤ M * Real.exp (-((m * z).re)) := by
  rw [norm_mul_exp] at h
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).2 h

/-- **Two-ray Phragmén–Lindelöf bound** (quantitative `h(0) + h(π) ≥ 0`
input): an entire function of exponential type `τ` decaying like `e^{-ε|x|}`
on both real rays obeys `‖g z‖ ≤ max C A · e^{-ε|Re z| + τ|Im z|}` on all of
`ℂ`. -/
theorem norm_le_exp_of_two_ray_exponential_decay
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {A τ C ε : ℝ} (hA : 0 ≤ A)
    (hgrow : ∀ z : ℂ, ‖g z‖ ≤ A * Real.exp (τ * ‖z‖))
    (hplus : ∀ x : ℝ, 0 ≤ x → ‖g (x : ℂ)‖ ≤ C * Real.exp (-(ε * x)))
    (hminus : ∀ x : ℝ, x ≤ 0 → ‖g (x : ℂ)‖ ≤ C * Real.exp (ε * x)) :
    ∀ z : ℂ, ‖g z‖ ≤ max C A * Real.exp (-(ε * |z.re|) + τ * |z.im|) := by
  intro z
  -- ray-boundary bound for a general multiplier with `m.re = ±ε`
  have hray_plus : ∀ (m : ℂ), m.re = ε → ∀ x : ℝ, 0 ≤ x →
      ‖g (x : ℂ) * Complex.exp (m * (x : ℂ))‖ ≤ max C A := by
    intro m hm x hx
    rw [norm_mul_exp, re_mul_ofReal, hm]
    calc ‖g (x : ℂ)‖ * Real.exp (ε * x)
        ≤ (C * Real.exp (-(ε * x))) * Real.exp (ε * x) :=
          mul_le_mul_of_nonneg_right (hplus x hx) (Real.exp_nonneg _)
      _ = C := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, mul_one]
      _ ≤ max C A := le_max_left _ _
  have hray_minus : ∀ (m : ℂ), m.re = -ε → ∀ x : ℝ, x ≤ 0 →
      ‖g (x : ℂ) * Complex.exp (m * (x : ℂ))‖ ≤ max C A := by
    intro m hm x hx
    rw [norm_mul_exp, re_mul_ofReal, hm]
    calc ‖g (x : ℂ)‖ * Real.exp (-ε * x)
        ≤ (C * Real.exp (ε * x)) * Real.exp (-ε * x) :=
          mul_le_mul_of_nonneg_right (hminus x hx) (Real.exp_nonneg _)
      _ = C := by
          rw [mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel,
            Real.exp_zero, mul_one]
      _ ≤ max C A := le_max_left _ _
  -- imaginary-boundary bound for a multiplier with `m.im = ±τ`
  have him_plus : ∀ (m : ℂ), m.im = τ → ∀ x : ℝ, 0 ≤ x →
      ‖g ((x : ℂ) * I) * Complex.exp (m * ((x : ℂ) * I))‖ ≤ max C A := by
    intro m hm x hx
    rw [norm_mul_exp, re_mul_ofReal_mul_I, hm]
    have hnorm : ‖(x : ℂ) * I‖ = x := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hx]
    calc ‖g ((x : ℂ) * I)‖ * Real.exp (-(τ * x))
        ≤ (A * Real.exp (τ * x)) * Real.exp (-(τ * x)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          have := hgrow ((x : ℂ) * I)
          rwa [hnorm] at this
      _ = A := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]
      _ ≤ max C A := le_max_right _ _
  have him_minus : ∀ (m : ℂ), m.im = -τ → ∀ x : ℝ, x ≤ 0 →
      ‖g ((x : ℂ) * I) * Complex.exp (m * ((x : ℂ) * I))‖ ≤ max C A := by
    intro m hm x hx
    rw [norm_mul_exp, re_mul_ofReal_mul_I, hm]
    have hnorm : ‖(x : ℂ) * I‖ = -x := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonpos hx]
    calc ‖g ((x : ℂ) * I)‖ * Real.exp (-(-τ * x))
        ≤ (A * Real.exp (τ * -x)) * Real.exp (-(-τ * x)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          have := hgrow ((x : ℂ) * I)
          rwa [hnorm] at this
      _ = A := by
          rw [mul_assoc, ← Real.exp_add, neg_mul, neg_neg, mul_neg,
            neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ max C A := le_max_right _ _
  -- differentiability of the multiplied function, any multiplier
  have hdiff : ∀ m : ℂ, Differentiable ℂ fun w => g w * Complex.exp (m * w) :=
    fun m => hg.mul (Complex.differentiable_exp.comp
      (differentiable_id.const_mul m))
  have hBig : ∀ (m : ℂ) (l : Filter ℂ), ∃ c < (2 : ℝ), ∃ B,
      (fun w => g w * Complex.exp (m * w))
        =O[l] fun w => Real.exp (B * ‖w‖ ^ c) :=
    fun m l => ⟨1, one_lt_two, τ + ‖m‖, isBigO_mul_exp hA hgrow m l⟩
  -- final unwrap, shared by all four quadrants
  have hfinish : ∀ m : ℂ,
      ‖g z * Complex.exp (m * z)‖ ≤ max C A →
      ‖g z‖ ≤ max C A * Real.exp (-(m.re * z.re) + m.im * z.im) := by
    intro m h
    calc ‖g z‖ ≤ max C A * Real.exp (-((m * z).re)) :=
          norm_le_of_mul_exp_le h
      _ = max C A * Real.exp (-(m.re * z.re) + m.im * z.im) := by
          congr 1
          rw [Real.exp_eq_exp, Complex.mul_re]
          ring
  rcases le_total 0 z.re with hzre | hzre <;> rcases le_total 0 z.im with hzim | hzim
  · -- quadrant I : m = ε + τ I
    set m : ℂ := (ε : ℂ) + (τ : ℂ) * I with hm
    have hmre : m.re = ε := by simp [hm]
    have hmim : m.im = τ := by simp [hm]
    have hb := PhragmenLindelof.quadrant_I ((hdiff m).diffContOnCl)
      (hBig m _) (hray_plus m hmre) (him_plus m hmim) hzre hzim
    calc ‖g z‖ ≤ max C A * Real.exp (-(m.re * z.re) + m.im * z.im) :=
          hfinish m hb
      _ = max C A * Real.exp (-(ε * |z.re|) + τ * |z.im|) := by
          rw [hmre, hmim, abs_of_nonneg hzre, abs_of_nonneg hzim]
  · -- quadrant IV : m = ε - τ I
    set m : ℂ := (ε : ℂ) - (τ : ℂ) * I with hm
    have hmre : m.re = ε := by simp [hm]
    have hmim : m.im = -τ := by simp [hm]
    have hb := PhragmenLindelof.quadrant_IV ((hdiff m).diffContOnCl)
      (hBig m _) (hray_plus m hmre) (him_minus m hmim) hzre hzim
    calc ‖g z‖ ≤ max C A * Real.exp (-(m.re * z.re) + m.im * z.im) :=
          hfinish m hb
      _ = max C A * Real.exp (-(ε * |z.re|) + τ * |z.im|) := by
          rw [hmre, hmim, abs_of_nonneg hzre, abs_of_nonpos hzim]
          congr 1
          rw [Real.exp_eq_exp]
          ring
  · -- quadrant II : m = -ε + τ I
    set m : ℂ := -(ε : ℂ) + (τ : ℂ) * I with hm
    have hmre : m.re = -ε := by simp [hm]
    have hmim : m.im = τ := by simp [hm]
    have hb := PhragmenLindelof.quadrant_II ((hdiff m).diffContOnCl)
      (hBig m _) (hray_minus m hmre) (him_plus m hmim) hzre hzim
    calc ‖g z‖ ≤ max C A * Real.exp (-(m.re * z.re) + m.im * z.im) :=
          hfinish m hb
      _ = max C A * Real.exp (-(ε * |z.re|) + τ * |z.im|) := by
          rw [hmre, hmim, abs_of_nonpos hzre, abs_of_nonneg hzim]
          congr 1
          rw [Real.exp_eq_exp]
          ring
  · -- quadrant III : m = -ε - τ I
    set m : ℂ := -(ε : ℂ) - (τ : ℂ) * I with hm
    have hmre : m.re = -ε := by simp [hm]
    have hmim : m.im = -τ := by simp [hm]
    have hb := PhragmenLindelof.quadrant_III ((hdiff m).diffContOnCl)
      (hBig m _) (hray_minus m hmre) (him_minus m hmim) hzre hzim
    calc ‖g z‖ ≤ max C A * Real.exp (-(m.re * z.re) + m.im * z.im) :=
          hfinish m hb
      _ = max C A * Real.exp (-(ε * |z.re|) + τ * |z.im|) := by
          rw [hmre, hmim, abs_of_nonpos hzre, abs_of_nonpos hzim]
          congr 1
          rw [Real.exp_eq_exp]
          ring

end RHTower
