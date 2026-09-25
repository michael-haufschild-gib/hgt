import GaloisForLFunctions.RHTower.PhotonicPassiveMultimodeFluxNoGo
import GaloisForLFunctions.HTGeometry.PhotonicTimeCrystalComplexModulation

/-!
# Conductive Floquet balance: modulation work survives in the bulk

The prior uniform-imaginary-permittivity flux theorem has a telescoping
positive loss. A conductivity-type material response instead contributes an
imaginary term proportional to signed physical frequency. Pairing the full
spatial-Hilbert recurrence with its grade state and dividing by the *first*
frequency power produces a frequency-weighted current. Its adjacent-grade
difference leaves a modulation-work term proportional to the Floquet step.

This is an exact multimode recurrence theorem, not a derivation of the
rotating-cylinder Maxwell boundary operator. `kappa` retains the chosen
Fourier-sign convention. At a zero-frequency grade the material terms vanish
and division is invalid; the exceptional constraint is stated separately.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

/-- Extension of the corpus's positive-frequency conductivity material
formula to signed physical frequencies. Physical use requires `nu ≠ 0`;
Lean's totalized division assigns a formal value at zero. -/
noncomputable def ptrSignedConductivePermittivity
    (epsilon sigma epsilon0 nu : ℝ) : ℂ :=
  (epsilon : ℂ) - I * ((sigma / (nu * epsilon0) : ℝ) : ℂ)

theorem ptrSignedConductivePermittivity_im
    (epsilon sigma epsilon0 nu : ℝ) :
    (ptrSignedConductivePermittivity epsilon sigma epsilon0 nu).im =
      -sigma / (nu * epsilon0) := by
  simp only [ptrSignedConductivePermittivity, Complex.sub_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The signed-frequency material formula retains a fixed conductivity
coefficient after multiplying its imaginary part by physical frequency. -/
theorem ptrSignedConductivePermittivity_frequency_loss
    (epsilon sigma epsilon0 nu : ℝ)
    (hnu : nu ≠ 0) (hepsilon0 : epsilon0 ≠ 0) :
    nu * (ptrSignedConductivePermittivity epsilon sigma epsilon0 nu).im =
      -sigma / epsilon0 := by
  rw [ptrSignedConductivePermittivity_im]
  field_simp

/-- The Maxwell frequency-square factor converts the corpus's `1/nu`
conductivity response into a *first-power* frequency term. This is the
constitutive bridge to the recurrence below, with
`kappa = -sigma / epsilon0` in the corpus's Fourier convention. -/
theorem ptrSignedConductivePermittivity_wave_factor
    (epsilon sigma epsilon0 nu : ℝ) :
    (((nu ^ 2 : ℝ) : ℂ) *
      ptrSignedConductivePermittivity epsilon sigma epsilon0 nu) =
      (((nu ^ 2 * epsilon : ℝ) : ℂ) -
        I * ((sigma * nu / epsilon0 : ℝ) : ℂ)) := by
  have hfactor : nu ^ 2 * (sigma / (nu * epsilon0)) =
      sigma * nu / epsilon0 := by
    by_cases hnu : nu = 0
    · simp [hnu]
    by_cases hepsilon0 : epsilon0 = 0
    · simp [hepsilon0]
    field_simp [hnu, hepsilon0]
  calc
    _ = (((nu ^ 2 * epsilon : ℝ) : ℂ) -
      I * ((nu ^ 2 * (sigma / (nu * epsilon0)) : ℝ) : ℂ)) := by
        simp only [ptrSignedConductivePermittivity]
        push_cast
        ring
    _ = _ := by rw [hfactor]

/-- Exact agreement with the corpus's positive-frequency conductivity law. -/
theorem ptrSignedConductivePermittivity_pos_eq_pcm
    (epsilon sigma : ℝ)
    (omega epsilon0 : GaloisForLFunctions.HTGeometry.PositiveOpticalParameter) :
    ptrSignedConductivePermittivity epsilon sigma (epsilon0 : ℝ) (omega : ℝ) =
      GaloisForLFunctions.HTGeometry.pcmComplexMaterial epsilon sigma omega epsilon0 := by
  rw [GaloisForLFunctions.HTGeometry.pcmComplexMaterial_eq]
  rfl

/-- A real time-domain response has the expected negative-frequency
conjugation in this conductivity model. -/
theorem ptrSignedConductivePermittivity_schwarz
    (epsilon sigma epsilon0 nu : ℝ) :
    ptrSignedConductivePermittivity epsilon sigma epsilon0 (-nu) =
      starRingEnd ℂ (ptrSignedConductivePermittivity epsilon sigma epsilon0 nu) := by
  simp [ptrSignedConductivePermittivity]
  rw [div_neg]
  ring

/-- No real-response material can retain one strictly positive imaginary
permittivity at every signed nonzero frequency. The old uniform-loss current
therefore cannot be transported unchanged to a causal bilateral ladder. -/
theorem ptr_no_real_response_uniform_bilateral_positive_imaginary_loss :
    ¬ ∃ chi : ℝ → ℂ,
      (∀ nu : ℝ, chi (-nu) = starRingEnd ℂ (chi nu)) ∧
      ∃ gamma : ℝ, 0 < gamma ∧
        ∀ nu : ℝ, nu ≠ 0 → (chi nu).im = gamma := by
  rintro ⟨chi, hsch, gamma, hgamma, huniform⟩
  have hp := huniform 1 (by norm_num)
  have hm := huniform (-1) (by norm_num)
  rw [show (-1 : ℝ) = -(1 : ℝ) by ring, hsch, Complex.conj_im] at hm
  linarith

private theorem conductive_imag_algebra
    (a b d e h : ℂ) (nu kappa : ℝ)
    (ha : a.im = 0) (hh : h.im = 0)
    (hrec : ((nu ^ 2 : ℝ) : ℂ) * (a + b + d) +
      (I * ((kappa * nu : ℝ) : ℂ)) * e = h) :
    nu * (kappa * e.re + nu * (b.im + d.im)) = 0 := by
  have hi := congrArg Complex.im hrec
  have hprod : (I * ((kappa * nu : ℝ) : ℂ)) * e =
      ((kappa * nu : ℝ) : ℂ) * (I * e) := by ring
  rw [hprod] at hi
  simp only [Complex.add_im, Complex.im_ofReal_mul, ha, hh] at hi
  rw [Complex.I_mul_im] at hi
  nlinarith

/-- Exact conductive balance in every nonzero signed-frequency grade, with
arbitrary spatial-mode mixing. The `Omega * J` term is work by temporal
modulation; it is not a boundary flux and cannot be dropped. -/
theorem ptr_conductive_multimode_pump_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : ℤ → E →ₗ[ℂ] E) (M0 Mp Mm G : E →ₗ[ℂ] E)
    (c : ℤ → E) (nu : ℤ → ℝ) (kappa Omega : ℝ)
    (hstep : ∀ n : ℤ, nu n - nu (n - 1) = Omega)
    (hH : ∀ n x, (inner ℂ x (H n x)).im = 0)
    (hM0 : ∀ x, (inner ℂ x (M0 x)).im = 0)
    (hAdj : ∀ x y, inner ℂ x (Mm y) =
      starRingEnd ℂ (inner ℂ y (Mp x)))
    (hrec : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) •
        (M0 (c n) + Mp (c (n-1)) + Mm (c (n+1))) +
      (I * ((kappa * nu n : ℝ) : ℂ)) • G (c n) = H n (c n)) :
    ∀ n : ℤ, nu n ≠ 0 →
      kappa * (inner ℂ (c n) (G (c n))).re +
        Omega * (inner ℂ (c n) (Mp (c (n-1)))).im =
      nu n * (inner ℂ (c (n+1)) (Mp (c n))).im -
        nu (n-1) * (inner ℂ (c n) (Mp (c (n-1)))).im := by
  intro n hnu
  have hinner := congrArg (fun v : E => inner ℂ (c n) v) (hrec n)
  simp only [inner_smul_right, inner_add_right] at hinner
  have hi := conductive_imag_algebra
    (inner ℂ (c n) (M0 (c n)))
    (inner ℂ (c n) (Mp (c (n-1))))
    (inner ℂ (c n) (Mm (c (n+1))))
    (inner ℂ (c n) (G (c n)))
    (inner ℂ (c n) (H n (c n))) (nu n) kappa
    (hM0 (c n)) (hH n (c n)) hinner
  have hm : (inner ℂ (c n) (Mm (c (n+1)))).im =
      -(inner ℂ (c (n+1)) (Mp (c n))).im := by
    rw [hAdj, Complex.conj_im]
  rw [hm] at hi
  have hlocal : kappa * (inner ℂ (c n) (G (c n))).re =
      nu n * ((inner ℂ (c (n+1)) (Mp (c n))).im -
        (inner ℂ (c n) (Mp (c (n-1)))).im) := by
    have hzero := (mul_eq_zero.mp hi).resolve_left hnu
    linarith
  rw [← hstep n]
  linear_combination hlocal

/-- At a zero-frequency grade, the conductive material and helical
convolution terms drop out of this recurrence. It is governed only by the
static spatial kernel; no loss conclusion follows from the grade equation. -/
theorem ptr_conductive_zero_frequency_grade
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : ℤ → E →ₗ[ℂ] E) (M0 Mp Mm G : E →ₗ[ℂ] E)
    (c : ℤ → E) (nu : ℤ → ℝ) (kappa : ℝ)
    (hrec : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) •
        (M0 (c n) + Mp (c (n-1)) + Mm (c (n+1))) +
      (I * ((kappa * nu n : ℝ) : ℂ)) • G (c n) = H n (c n))
    (n : ℤ) (hzero : nu n = 0) : H n (c n) = 0 := by
  simpa [hzero] using (hrec n).symm

/-- Arbitrary finite grade windows retain the modulation work in their
interior; only the frequency-weighted current telescopes. -/
theorem ptr_conductive_pump_window
    (g J K : ℤ → ℝ) (kappa Omega : ℝ)
    (hlocal : ∀ n : ℤ, kappa * g n + Omega * J n = K (n + 1) - K n)
    (j : ℤ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N,
      (kappa * g (j + (k : ℤ)) + Omega * J (j + (k : ℤ)))) =
        K (j + (N : ℤ) + 1) - K j := by
  calc
    _ = ∑ k ∈ Finset.Icc 0 N,
        (K (j + (k : ℤ) + 1) - K (j + (k : ℤ))) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hlocal (j + (k : ℤ))
    _ = K (j + (N : ℤ) + 1) - K j := by
          simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
            zero_add, add_zero, add_assoc] using
            (Finset.sum_Icc_sub (m := 0) (n := N) (Nat.zero_le N)
              (fun k : ℕ => K (j + (k : ℤ))))

/-- Complete finite-window identity for the conductive multimode recurrence.
The signed conductivity term and modulation work remain; only the
frequency-weighted helical current is a boundary term. -/
theorem ptr_conductive_multimode_window_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H : ℤ → E →ₗ[ℂ] E) (M0 Mp Mm G : E →ₗ[ℂ] E)
    (c : ℤ → E) (nu : ℤ → ℝ) (kappa Omega : ℝ)
    (hnu : ∀ n : ℤ, nu n ≠ 0)
    (hstep : ∀ n : ℤ, nu n - nu (n - 1) = Omega)
    (hH : ∀ n x, (inner ℂ x (H n x)).im = 0)
    (hM0 : ∀ x, (inner ℂ x (M0 x)).im = 0)
    (hAdj : ∀ x y, inner ℂ x (Mm y) =
      starRingEnd ℂ (inner ℂ y (Mp x)))
    (hrec : ∀ n : ℤ,
      (((nu n)^2 : ℝ) : ℂ) •
        (M0 (c n) + Mp (c (n-1)) + Mm (c (n+1))) +
      (I * ((kappa * nu n : ℝ) : ℂ)) • G (c n) = H n (c n))
    (j : ℤ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N,
      (kappa * (inner ℂ (c (j + (k : ℤ))) (G (c (j + (k : ℤ))))).re +
        Omega * (inner ℂ (c (j + (k : ℤ)))
          (Mp (c (j + (k : ℤ) - 1)))).im)) =
      nu (j + (N : ℤ)) *
        (inner ℂ (c (j + (N : ℤ) + 1)) (Mp (c (j + (N : ℤ))))).im -
      nu (j - 1) * (inner ℂ (c j) (Mp (c (j-1)))).im := by
  let g : ℤ → ℝ := fun n => (inner ℂ (c n) (G (c n))).re
  let J : ℤ → ℝ := fun n => (inner ℂ (c n) (Mp (c (n-1)))).im
  let K : ℤ → ℝ := fun n => nu (n-1) * J n
  have hlocal (n : ℤ) :
      kappa * g n + Omega * J n = K (n+1) - K n := by
    have h := ptr_conductive_multimode_pump_identity H M0 Mp Mm G c nu kappa Omega
      hstep hH hM0 hAdj hrec n (hnu n)
    simpa only [g, J, K, add_sub_cancel_right] using h
  have hw := ptr_conductive_pump_window g J K kappa Omega hlocal j N
  simpa only [g, J, K, add_sub_cancel_right] using hw

end RHTower
