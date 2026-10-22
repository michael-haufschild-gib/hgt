import GaloisForLFunctions.RHTower.Suzuki.SuzukiParityHankelDecomposition

/-!
# The Hankel parity carrier: regular density minus finite prime-power atoms

The Hankel form `H φ ψ = ∫∫ K (x + y) φ y ψ x` of a kernel is the pairing of `K` against the
convolution `c (t) = ∫ φ y * ψ (t - y) dy`.  When the kernel is a regular density minus an atomic
measure carried by the prime-power positions `log n` with weights `Λ n * n^(-1/2)`, the Hankel form
splits accordingly, the atomic part being the finite sum

```text
∑ Λ n * n^(-1/2) * c (log n).
```

Two facts make the sum finite and explicit for `φ, ψ` supported in `(0, a)`:

* `screwConvolve_eq_zero_of_two_mul_le` — the convolution vanishes at `t ≥ 2a`, so only prime
  powers with `log n < 2a`, i.e. `n < lambda^(2 : ℕ)` in the multiplicative parameter `lambda = e^a`,
  contribute;
* `screwConvolve_eq_intervalIntegral` — at any `0 < t < 2a` the convolution is the integral over the
  explicit window `(max 0 (t - a), min a t)`.

Together with the coefficient-linearity of the atomic part this gives the exact cocycle law for a
finite change of the von Mangoldt coefficient vector.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory

/-! ## The convolution carrier -/

/-- The convolution `c (t) = ∫ φ y * ψ (t - y) dy`. -/
def screwConvolve (φ ψ : ℝ → ℝ) (t : ℝ) : ℝ := ∫ y : ℝ, φ y * ψ (t - y)

/-- Reflecting the left factor turns the correlation into the convolution. -/
theorem screwCrossCorr_negReflect (φ ψ : ℝ → ℝ) (u : ℝ) :
    screwCrossCorr (negReflect φ) ψ u = screwConvolve φ ψ u := by
  rw [screwCrossCorr, screwConvolve, ← integral_neg_eq_self (fun y : ℝ => φ y * ψ (u - y)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [negReflect]
  rw [show u - -y = u + y from by ring]

/-- **The convolution window closes at `2a`.**  If `φ` and `ψ` vanish off `(0, a)` then the
convolution vanishes at every `t ≥ 2a`. -/
theorem screwConvolve_eq_zero_of_two_mul_le {a t : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Ioo 0 a) (hψ : ∀ x, ψ x ≠ 0 → x ∈ Ioo 0 a)
    (ht : 2 * a ≤ t) : screwConvolve φ ψ t = 0 := by
  have hzero : (fun y : ℝ => φ y * ψ (t - y)) = fun _ : ℝ => (0 : ℝ) := by
    funext y
    by_cases hy : φ y = 0
    · rw [hy, zero_mul]
    by_cases hz : ψ (t - y) = 0
    · rw [hz, mul_zero]
    obtain ⟨hy1, hy2⟩ := hφ y hy
    obtain ⟨hz1, hz2⟩ := hψ (t - y) hz
    exact absurd ht (by linarith)
  rw [screwConvolve, hzero, integral_zero]

/-- **The explicit convolution window.**  For `φ, ψ` vanishing off `(0, a)` and `0 < t < 2a` the
convolution is the integral over `(max 0 (t - a), min a t)`. -/
theorem screwConvolve_eq_intervalIntegral {a t : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Ioo 0 a) (hψ : ∀ x, ψ x ≠ 0 → x ∈ Ioo 0 a)
    (ht0 : 0 < t) (ht2 : t < 2 * a) :
    screwConvolve φ ψ t = ∫ y in (max 0 (t - a))..(min a t), φ y * ψ (t - y) := by
  have hle : max 0 (t - a) ≤ min a t := by
    have hapos : 0 < a := by linarith
    refine max_le (le_min hapos.le ht0.le) ?_
    exact le_min (by linarith) (by linarith)
  have hout : ∀ y ∉ Ioo (max 0 (t - a)) (min a t), φ y * ψ (t - y) = 0 := by
    intro y hy
    by_cases hφy : φ y = 0
    · rw [hφy, zero_mul]
    by_cases hψy : ψ (t - y) = 0
    · rw [hψy, mul_zero]
    obtain ⟨hy1, hy2⟩ := hφ y hφy
    obtain ⟨hz1, hz2⟩ := hψ (t - y) hψy
    refine absurd (show y ∈ Ioo (max 0 (t - a)) (min a t) from ?_) hy
    exact ⟨max_lt hy1 (by linarith), lt_min hy2 (by linarith)⟩
  calc screwConvolve φ ψ t
      = ∫ y in Ioo (max 0 (t - a)) (min a t), φ y * ψ (t - y) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm
    _ = ∫ y in Ioc (max 0 (t - a)) (min a t), φ y * ψ (t - y) :=
        setIntegral_congr_set Ioo_ae_eq_Ioc
    _ = ∫ y in (max 0 (t - a))..(min a t), φ y * ψ (t - y) :=
        (intervalIntegral.integral_of_le hle).symm

/-! ## The shear identity for the sum form -/

/-- The two-variable integrand of the difference form. -/
def diffFormIntegrand (K φ ψ : ℝ → ℝ) (x y : ℝ) : ℝ := K (x - y) * φ y * ψ x

/-- The same integrand after the shear `x = u + y`. -/
def diffShearIntegrand (K φ ψ : ℝ → ℝ) (y u : ℝ) : ℝ := K u * φ y * ψ (u + y)

theorem diffBilinForm_eq_integral_uncurry (K φ ψ : ℝ → ℝ) :
    diffBilinForm K φ ψ = ∫ p : ℝ × ℝ, Function.uncurry (diffFormIntegrand K φ ψ) p := rfl

/-- **The difference form is the kernel paired with the correlation.**  The general form of the
shear identity, with the two integrability hypotheses left explicit. -/
theorem diffBilinForm_eq_correlation_pairing (K φ ψ : ℝ → ℝ)
    (hd : Integrable (Function.uncurry (diffFormIntegrand K φ ψ)) (volume.prod volume))
    (hsh : Integrable (Function.uncurry (diffShearIntegrand K φ ψ)) (volume.prod volume)) :
    diffBilinForm K φ ψ = ∫ u : ℝ, K u * screwCrossCorr φ ψ u := by
  calc diffBilinForm K φ ψ
      = ∫ p : ℝ × ℝ, Function.uncurry (diffFormIntegrand K φ ψ) p :=
        diffBilinForm_eq_integral_uncurry K φ ψ
    _ = ∫ x : ℝ, ∫ y : ℝ, diffFormIntegrand K φ ψ x y := by
        rw [Measure.volume_eq_prod ℝ ℝ]
        exact (integral_integral hd).symm
    _ = ∫ y : ℝ, ∫ x : ℝ, diffFormIntegrand K φ ψ x y := integral_integral_swap hd
    _ = ∫ y : ℝ, ∫ u : ℝ, diffShearIntegrand K φ ψ y u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        calc ∫ x : ℝ, diffFormIntegrand K φ ψ x y
            = ∫ u : ℝ, diffFormIntegrand K φ ψ (u + y) y :=
              (integral_add_right_eq_self (fun x => diffFormIntegrand K φ ψ x y) y).symm
          _ = ∫ u : ℝ, diffShearIntegrand K φ ψ y u := by
              simp only [diffFormIntegrand, diffShearIntegrand, add_sub_cancel_right]
    _ = ∫ u : ℝ, ∫ y : ℝ, diffShearIntegrand K φ ψ y u := integral_integral_swap hsh
    _ = ∫ u : ℝ, K u * screwCrossCorr φ ψ u := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show (∫ y : ℝ, diffShearIntegrand K φ ψ y u) = K u * screwCrossCorr φ ψ u
        have hpt : ∀ y : ℝ, diffShearIntegrand K φ ψ y u = K u * (φ y * ψ (u + y)) := by
          intro y
          simp only [diffShearIntegrand]
          ring
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
        rfl

/-- **The sum form is the kernel paired with the convolution.** -/
theorem sumBilinForm_eq_convolution_pairing (K φ ψ : ℝ → ℝ)
    (hd : Integrable (Function.uncurry (diffFormIntegrand K (negReflect φ) ψ))
      (volume.prod volume))
    (hsh : Integrable (Function.uncurry (diffShearIntegrand K (negReflect φ) ψ))
      (volume.prod volume)) :
    sumBilinForm K φ ψ = ∫ u : ℝ, K u * screwConvolve φ ψ u := by
  rw [← diffBilinForm_negReflect_left K φ ψ, diffBilinForm_eq_correlation_pairing K _ ψ hd hsh]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show K u * screwCrossCorr (negReflect φ) ψ u = K u * screwConvolve φ ψ u
  rw [screwCrossCorr_negReflect]

/-! ## The finite prime-power atomic part -/

/-- The atomic part of the Hankel carrier: the finite sum of prime-power convolution samples with
an arbitrary coefficient vector. -/
def atomicHankelPart (b : ℕ → ℝ) (N : ℕ) (φ ψ : ℝ → ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N, b n * screwConvolve φ ψ (Real.log n)

/-- The von Mangoldt atomic part of the Hankel carrier at aperture `a`. -/
def primeHankelPart (a : ℝ) (φ ψ : ℝ → ℝ) : ℝ :=
  atomicHankelPart screwPrimeWeight ⌊Real.exp (2 * a)⌋₊ φ ψ

/-- **The cutoff `n < lambda^(2 : ℕ)`.**  Enlarging the atomic index range beyond `e^(2a)` adds nothing:
every further prime-power sample of the convolution vanishes. -/
theorem atomicHankelPart_eq_primeHankelPart {a : ℝ} {φ ψ : ℝ → ℝ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Ioo 0 a) (hψ : ∀ x, ψ x ≠ 0 → x ∈ Ioo 0 a)
    (b : ℕ → ℝ) (hb : b = screwPrimeWeight) {N : ℕ} (hN : ⌊Real.exp (2 * a)⌋₊ ≤ N) :
    atomicHankelPart b N φ ψ = primeHankelPart a φ ψ := by
  subst hb
  rw [primeHankelPart, atomicHankelPart, atomicHankelPart]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hN⟩
  · intro n hn hnot
    simp only [Finset.mem_Icc] at hn
    have hgt : ⌊Real.exp (2 * a)⌋₊ < n := by
      by_contra hle
      exact hnot (Finset.mem_Icc.mpr ⟨hn.1, by omega⟩)
    have hexp : Real.exp (2 * a) < (n : ℝ) :=
      (Nat.floor_lt (Real.exp_pos (2 * a)).le).mp hgt
    have hnpos : (0 : ℝ) < (n : ℝ) := (Real.exp_pos (2 * a)).trans hexp
    have hlog : 2 * a ≤ Real.log n :=
      le_of_lt ((Real.lt_log_iff_exp_lt hnpos).mpr hexp)
    rw [screwConvolve_eq_zero_of_two_mul_le hφ hψ hlog, mul_zero]

/-- **The coefficient cocycle.**  A finite change of the coefficient vector changes the atomic
Hankel part by exactly the paired increment. -/
theorem atomicHankelPart_add (b c : ℕ → ℝ) (N : ℕ) (φ ψ : ℝ → ℝ) :
    atomicHankelPart (b + c) N φ ψ = atomicHankelPart b N φ ψ + atomicHankelPart c N φ ψ := by
  simp only [atomicHankelPart, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

/-- The cocycle in difference form: the Hankel margin moves by `-∑ δb n * c (log n)` when the
carrier is `regular part - atomic part`. -/
theorem atomicHankelPart_sub (b c : ℕ → ℝ) (N : ℕ) (φ ψ : ℝ → ℝ) :
    atomicHankelPart (b + c) N φ ψ - atomicHankelPart b N φ ψ
      = ∑ n ∈ Finset.Icc 2 N, c n * screwConvolve φ ψ (Real.log n) := by
  rw [atomicHankelPart_add]
  simp only [atomicHankelPart]
  ring

/-! ## The autocorrelation form of the Hankel carrier -/

/-- **The Hankel carrier as a regular pairing minus a finite prime-power sum.**  With
`K = K_reg - (atomic part)` the Hankel form of `K` is the regular convolution pairing minus the
finite prime-power convolution samples.  Stated for a general coefficient vector and index range so
that the cocycle law applies verbatim. -/
theorem sumBilinForm_sub_atomic (Kreg φ ψ : ℝ → ℝ) (b : ℕ → ℝ) (N : ℕ)
    (hd : Integrable (Function.uncurry (diffFormIntegrand Kreg (negReflect φ) ψ))
      (volume.prod volume))
    (hsh : Integrable (Function.uncurry (diffShearIntegrand Kreg (negReflect φ) ψ))
      (volume.prod volume)) :
    sumBilinForm Kreg φ ψ - atomicHankelPart b N φ ψ
      = (∫ u : ℝ, Kreg u * screwConvolve φ ψ u)
        - ∑ n ∈ Finset.Icc 2 N, b n * screwConvolve φ ψ (Real.log n) := by
  rw [sumBilinForm_eq_convolution_pairing Kreg φ ψ hd hsh, atomicHankelPart]


/-- **The parity gap is twice the Hankel carrier.**  Combining the parity decomposition with the
regular-minus-atomic split of the Hankel form: the even sector exceeds the odd sector by exactly
twice the difference between the regular convolution pairing and the finite prime-power convolution
samples. -/
theorem parityGap_eq_regular_sub_atomic (K Kreg φ ψ : ℝ → ℝ) (b : ℕ → ℝ) (N : ℕ)
    (hK : ∀ t, K (-t) = K t)
    (hφ0 : ∀ x ≤ (0 : ℝ), φ x = 0) (hψ0 : ∀ x ≤ (0 : ℝ), ψ x = 0)
    (hd : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1)
    (hs : Integrable fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1)
    (hsplit : sumBilinForm K φ ψ
      = (∫ u : ℝ, Kreg u * screwConvolve φ ψ u)
        - ∑ n ∈ Finset.Icc 2 N, b n * screwConvolve φ ψ (Real.log n)) :
    diffBilinForm K (evenParityLift φ) (evenParityLift ψ)
        - diffBilinForm K (oddParityLift φ) (oddParityLift ψ)
      = 2 * ((∫ u : ℝ, Kreg u * screwConvolve φ ψ u)
        - ∑ n ∈ Finset.Icc 2 N, b n * screwConvolve φ ψ (Real.log n)) := by
  rw [diffBilinForm_parity_difference K φ ψ hK hφ0 hψ0 hd hs, hsplit]

/-- The autocorrelation form of the parity gap: the diagonal case `ψ = φ`. -/
theorem parityGap_autocorrelation (K Kreg φ : ℝ → ℝ) (b : ℕ → ℝ) (N : ℕ)
    (hK : ∀ t, K (-t) = K t) (hφ0 : ∀ x ≤ (0 : ℝ), φ x = 0)
    (hd : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * φ p.1)
    (hs : Integrable fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * φ p.1)
    (hsplit : sumBilinForm K φ φ
      = (∫ u : ℝ, Kreg u * screwConvolve φ φ u)
        - ∑ n ∈ Finset.Icc 2 N, b n * screwConvolve φ φ (Real.log n)) :
    diffBilinForm K (evenParityLift φ) (evenParityLift φ)
        - diffBilinForm K (oddParityLift φ) (oddParityLift φ)
      = 2 * ((∫ u : ℝ, Kreg u * screwConvolve φ φ u)
        - ∑ n ∈ Finset.Icc 2 N, b n * screwConvolve φ φ (Real.log n)) :=
  parityGap_eq_regular_sub_atomic K Kreg φ φ b N hK hφ0 hφ0 hd hs hsplit

end GaloisForLFunctions.RHTower

end
