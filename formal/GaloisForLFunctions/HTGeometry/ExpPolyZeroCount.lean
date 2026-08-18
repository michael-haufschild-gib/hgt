import GaloisForLFunctions.HTGeometry.HarmonicZeroCount
import GaloisForLFunctions.HTGeometry.SimpleZeroEnergy

/-!
# The Pólya-type zero count for real exponential polynomials

The descent is complete.  A real-valued exponential polynomial `f(t) = Re ∑_{y ∈ S} C_y e^{y t}` with
nonzero coefficients is counted by induction on the number of non-real exponents:

* if every exponent is real the sum is a real exponential sum and Laguerre's rule gives `|S| - 1`;
* otherwise pick `y₀` with `Im y₀ ≠ 0`, translate the exponents by `Re y₀` — which multiplies `f` by
  a nowhere-zero factor — and apply `D² + γ²` with `γ = |Im y₀|`.  That deletes the pair `± iγ` and
  rescales every other coefficient by a nonzero number, so the support loses at least one non-real
  exponent, and `card_zeros_le_reduce` bounds `f` by the reduced count.

The step needs a *finite* set carrying the zeros of the reduced polynomial, which fails in exactly
one case: when nothing survives the reduction, i.e. when the support is contained in `{± iγ}`.  There
`f'' + γ² f` vanishes identically, the energy `f'² + γ² f²` is constant, the zeros are simple, and
`zero_count_le_of_simple` counts them — that is the branch which closes the induction.

The same branch also admits a sharp count: the polynomial *is* the harmonic `A cos γt + B sin γt`,
whose zeros are exactly `π/γ` apart by a determinant argument (`HarmonicZeroCount`).  Both are
recorded; the induction runs on the energy route and the harmonic route is exported alongside,
since it halves the constant in that branch.

The resulting bound is effective: with `n = |S|`, `γ₀` an upper bound for `|Im y|`, and
`L = (b-a)γ₀/π`, the zeros of `f` in `[a,b]` number at most `3^N (n + 2L + 1) - (2L + 1)`, where `N`
is the number of non-real exponents.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-! ## The exponents killed by the Sturm operator -/

/-- The Sturm operator annihilates a term only at `± iγ`. -/
theorem eq_pair_of_sturmCoeff_eq_zero {C : ℂ → ℂ} {γ : ℝ} {y : ℂ} (hC : C y ≠ 0)
    (h : sturmCoeff C γ y = 0) :
    y = Complex.I * ((γ : ℝ) : ℂ) ∨ y = -(Complex.I * ((γ : ℝ) : ℂ)) := by
  by_contra hcon
  push Not at hcon
  exact sturmCoeff_ne_zero hC hcon.1 hcon.2 h

/-- Which member of the conjugate pair an exponent is. -/
noncomputable def pairSign (γ : ℝ) (y : ℂ) : ℝ :=
  if y = Complex.I * ((γ : ℝ) : ℂ) then 1 else -1

/-- The real part of a purely imaginary exponential term. -/
theorem re_term_imag (c : ℂ) (ω t : ℝ) :
    (c * Complex.exp ((Complex.I * ((ω : ℝ) : ℂ)) * t)).re
      = c.re * cos (ω * t) - c.im * sin (ω * t) := by
  have harg : (Complex.I * ((ω : ℝ) : ℂ)) * (t : ℂ) = ((ω * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hexp : Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (ω * t) : ℝ) : ℂ) + ((Real.sin (ω * t) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [harg, hexp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Each member of the pair contributes the same cosine and opposite sines. -/
theorem re_term_of_pair {c : ℂ} {γ : ℝ} {y : ℂ} (hγ : γ ≠ 0)
    (hy : y = Complex.I * ((γ : ℝ) : ℂ) ∨ y = -(Complex.I * ((γ : ℝ) : ℂ))) (t : ℝ) :
    (c * Complex.exp (y * t)).re
      = c.re * cos (γ * t) - pairSign γ y * c.im * sin (γ * t) := by
  rcases hy with hy | hy
  · rw [hy, re_term_imag, pairSign, if_pos rfl]
    ring
  · have hne : y ≠ Complex.I * ((γ : ℝ) : ℂ) := by
      rw [hy]
      intro hcon
      have h2 : (2 : ℂ) * (Complex.I * ((γ : ℝ) : ℂ)) = 0 := by linear_combination -hcon
      rcases mul_eq_zero.mp h2 with h | h
      · norm_num at h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact Complex.I_ne_zero h'
        · exact hγ (by exact_mod_cast h')
    have hyeq : y = Complex.I * (((-γ : ℝ)) : ℂ) := by rw [hy]; push_cast; ring
    rw [hyeq, re_term_imag, pairSign, if_neg (by rw [← hyeq]; exact hne)]
    rw [show (-γ) * t = -(γ * t) by ring, Real.cos_neg, Real.sin_neg]
    ring

/-- **A pair-supported exponential polynomial is a harmonic.** -/
theorem re_expCombo_of_pair {S : Finset ℂ} {C : ℂ → ℂ} {γ : ℝ} (hγ : γ ≠ 0)
    (hS : ∀ y ∈ S, y = Complex.I * ((γ : ℝ) : ℂ) ∨ y = -(Complex.I * ((γ : ℝ) : ℂ))) (t : ℝ) :
    (∑ y ∈ S, C y * Complex.exp (y * t)).re
      = (∑ y ∈ S, (C y).re) * cos (γ * t)
        + (∑ y ∈ S, -(pairSign γ y * (C y).im)) * sin (γ * t) := by
  rw [Complex.re_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [re_term_of_pair hγ (hS y hy) t]
  ring

/-! ## The degenerate branch -/

/-- **The degenerate branch, by energy conservation.**  When every exponent is `± iγ` the Sturm
expression vanishes identically, so the energy `f'² + γ² f²` is constant, the zeros of a nonzero
such polynomial are simple, and `card_zeros_le_of_sturm_zero` counts them. -/
theorem card_zeros_degenerate_energy {S : Finset ℂ} {C : ℂ → ℂ} {γ a b : ℝ} (hγ : 0 < γ)
    (hab : a ≤ b)
    (hpair : ∀ y ∈ S, y = Complex.I * ((γ : ℝ) : ℂ) ∨ y = -(Complex.I * ((γ : ℝ) : ℂ)))
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0)
    {t₁ : ℝ} (hne : (∑ y ∈ S, C y * Complex.exp (y * t₁)).re ≠ 0)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b)
    (hZzero : ∀ x ∈ Z, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0)
    (hZall : ∀ x ∈ Icc a b, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0 → x ∈ Z) :
    (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 2 := by
  set f : ℝ → ℝ := fun t => (∑ y ∈ S, C y * Complex.exp (y * t)).re with hfdef
  set fd : ℝ → ℝ := deriv f with hfd
  set fdd : ℝ → ℝ := deriv (deriv f) with hfdd
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    Complex.reCLM.contDiff.comp (contDiff_expCombo S C)
  have hfderiv : ∀ t, HasDerivAt f (fd t) t := fun t =>
    (hsmooth.differentiable (by simp) t).hasDerivAt
  have hfdsmooth : ContDiff ℝ (⊤ : ℕ∞) fd := by
    rw [hfd]
    simpa using hsmooth.iterate_deriv 1
  have hfdderiv : ∀ t, HasDerivAt fd (fdd t) t := fun t =>
    (hfdsmooth.differentiable (by simp) t).hasDerivAt
  have hiter2 : ∀ t, iteratedDeriv 2 f t = fdd t := by
    intro t
    rw [hfdd, iteratedDeriv_succ, iteratedDeriv_one]
  have hkill : ∀ t : ℝ, fdd t + γ ^ 2 * f t = 0 := by
    intro t
    rw [← hiter2 t, sturm_expr_expCombo hreal γ t]
    have hz : ∑ y ∈ S, sturmCoeff C γ y * Complex.exp (y * t) = 0 := by
      refine Finset.sum_eq_zero (fun y hy => ?_)
      rcases hpair y hy with hcase | hcase
      · rw [sturmCoeff_eq_zero_of_mem hcase, zero_mul]
      · rw [sturmCoeff_eq_zero_of_mem' hcase, zero_mul]
    rw [hz, Complex.zero_re]
  exact card_zeros_le_of_sturm_zero hγ hab hfderiv hfdderiv hkill hne Z hZmem hZzero hZall

/-- **The degenerate branch, sharply.**  The same polynomial is the harmonic
`A cos γt + B sin γt`, whose distinct zeros are at least `π/γ` apart, so the count is
`(b-a)γ/π + 1` — half the density of the energy route, and attained by `2 cos γt`. -/
theorem card_zeros_degenerate_sharp {S : Finset ℂ} {C : ℂ → ℂ} {γ a b : ℝ} (hγ : 0 < γ)
    (hab : a ≤ b)
    (hpair : ∀ y ∈ S, y = Complex.I * ((γ : ℝ) : ℂ) ∨ y = -(Complex.I * ((γ : ℝ) : ℂ)))
    {t₁ : ℝ} (hne : (∑ y ∈ S, C y * Complex.exp (y * t₁)).re ≠ 0)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b)
    (hZzero : ∀ x ∈ Z, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0) :
    (Z.card : ℝ) ≤ (b - a) * γ / π + 1 := by
  have hform := re_expCombo_of_pair (C := C) (ne_of_gt hγ) hpair
  refine card_zeros_harmonic hγ hab (A := ∑ y ∈ S, (C y).re)
    (B := ∑ y ∈ S, -(pairSign γ y * (C y).im)) ?_ Z hZmem (fun x hx => by
      rw [← hform x]; exact hZzero x hx)
  rintro ⟨hA0, hB0⟩
  exact hne (by rw [hform t₁, hA0, hB0]; ring)

/-! ## The induction -/

open Classical in
/-- **The Pólya-type count.**  A real-valued exponential polynomial with nonzero coefficients, at
most `N` non-real exponents, all of imaginary part at most `γ₀` in absolute value, has at most
`3^N (|S| + 2L + 1) - (2L + 1)` zeros in `[a,b]`, where `L = (b-a)γ₀/π`. -/
theorem card_zeros_expPoly :
    ∀ (N : ℕ) (S : Finset ℂ) (C : ℂ → ℂ) (γ₀ a b : ℝ) (Z : Finset ℝ),
      (S.filter (fun y => y.im ≠ 0)).card ≤ N →
      S.Nonempty → (∀ y ∈ S, C y ≠ 0) → (∀ y ∈ S, |y.im| ≤ γ₀) →
      (∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) →
      a < b →
      (∀ x ∈ Z, x ∈ Icc a b) →
      (∀ x ∈ Z, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0) →
      (∀ x ∈ Icc a b, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0 → x ∈ Z) →
      (Z.card : ℝ)
        ≤ 3 ^ N * ((S.card : ℝ) + 2 * ((b - a) * γ₀ / π) + 1)
          - (2 * ((b - a) * γ₀ / π) + 1) := by
  classical
  intro N
  induction N with
  | zero =>
    intro S C γ₀ a b Z hN hSne hCne hγ₀ hreal hab hZmem hZzero hZall
    have hSreal : ∀ y ∈ S, y.im = 0 := by
      intro y hy
      by_contra hcon
      have hmem : y ∈ S.filter (fun y => y.im ≠ 0) := Finset.mem_filter.mpr ⟨hy, hcon⟩
      have := Finset.card_pos.mpr ⟨y, hmem⟩
      omega
    obtain ⟨y₁, hy₁⟩ := hSne
    have hγ₀nn : (0 : ℝ) ≤ γ₀ := le_trans (abs_nonneg _) (hγ₀ y₁ hy₁)
    have hba : (0 : ℝ) ≤ b - a := by linarith
    have hL : (0 : ℝ) ≤ (b - a) * γ₀ / π :=
      div_nonneg (mul_nonneg hba hγ₀nn) Real.pi_pos.le
    have hbase := card_zeros_le_realExponents hSreal hCne ⟨y₁, hy₁⟩ hreal Z hZzero
    have hcast : (Z.card : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hbase
    simp only [pow_zero, one_mul]
    linarith
  | succ N ih =>
    intro S C γ₀ a b Z hN hSne hCne hγ₀ hreal hab hZmem hZzero hZall
    obtain ⟨y₁, hy₁⟩ := hSne
    have hSne : S.Nonempty := ⟨y₁, hy₁⟩
    set L : ℝ := (b - a) * γ₀ / π with hLdef
    have hγ₀nn : (0 : ℝ) ≤ γ₀ := le_trans (abs_nonneg _) (hγ₀ y₁ hy₁)
    have hba : (0 : ℝ) ≤ b - a := by linarith
    have hL : (0 : ℝ) ≤ L := by
      rw [hLdef]; exact div_nonneg (mul_nonneg hba hγ₀nn) Real.pi_pos.le
    have hn1 : (1 : ℝ) ≤ (S.card : ℝ) := by
      have := Finset.card_pos.mpr hSne
      exact_mod_cast this
    have hpow1 : (1 : ℝ) ≤ 3 ^ N := one_le_pow₀ (by norm_num)
    have hpownn : (0 : ℝ) ≤ 3 ^ N := by positivity
    have hpowsucc : (3 : ℝ) ^ (N + 1) = 3 * 3 ^ N := by ring
    have hslack : (0 : ℝ) ≤ ((3 : ℝ) ^ (N + 1) - 3) * ((S.card : ℝ) + 2 * L + 1) := by
      refine mul_nonneg ?_ (by linarith)
      rw [hpowsucc]; linarith
    by_cases hall : ∀ y ∈ S, y.im = 0
    · have hbase := card_zeros_le_realExponents hall hCne hSne hreal Z hZzero
      have hcast : (Z.card : ℝ) + 1 ≤ (S.card : ℝ) := by exact_mod_cast hbase
      nlinarith [hslack, hL, hn1]
    · push Not at hall
      obtain ⟨y₀, hy₀S, hy₀im⟩ := hall
      set β : ℝ := y₀.re with hβ
      set γ : ℝ := |y₀.im| with hγdef
      have hγ : 0 < γ := by rw [hγdef]; exact abs_pos.mpr hy₀im
      have hγγ₀ : γ ≤ γ₀ := by rw [hγdef]; exact hγ₀ y₀ hy₀S
      set S' : Finset ℂ := shiftSupport S β with hS'
      set C' : ℂ → ℂ := shiftCoeff C β with hC'
      have hS'card : S'.card = S.card := shiftSupport_card S β
      have hS'ne : S'.Nonempty := by
        rw [← Finset.card_pos, hS'card]
        exact Finset.card_pos.mpr hSne
      have hC'ne : ∀ z ∈ S', C' z ≠ 0 := shift_coeff_ne S C β hCne
      have hreal' : ∀ t : ℝ, (∑ z ∈ S', C' z * Complex.exp (z * t)).im = 0 :=
        shift_real S C β hreal
      have hzeroiff : ∀ t : ℝ, (∑ z ∈ S', C' z * Complex.exp (z * t)).re = 0
          ↔ (∑ y ∈ S, C y * Complex.exp (y * t)).re = 0 := shift_zero_iff S C β
      have hmemS' : ∀ z ∈ S', z + ((β : ℝ) : ℂ) ∈ S :=
        fun z hz => (mem_shiftSupport_iff S β).mp hz
      have him' : ∀ z ∈ S', |z.im| ≤ γ₀ := by
        intro z hz
        have h1 := hγ₀ _ (hmemS' z hz)
        rwa [← shift_im_eq β z] at h1
      set z₀ : ℂ := y₀ - ((β : ℝ) : ℂ) with hz₀d
      have hz₀S' : z₀ ∈ S' := by
        rw [hS', hz₀d]
        exact (mem_shiftSupport_iff S β).mpr (by simpa using hy₀S)
      have hz₀eq : z₀ = Complex.I * ((y₀.im : ℝ) : ℂ) := by
        rw [hz₀d, hβ]; exact shift_target y₀
      have hz₀im : z₀.im = y₀.im := by rw [hz₀eq]; simp
      have hz₀coeff : sturmCoeff C' γ z₀ = 0 := by
        rcases abs_cases y₀.im with ⟨he, _⟩ | ⟨he, _⟩
        · have hgy : γ = y₀.im := by rw [hγdef, he]
          refine sturmCoeff_eq_zero_of_mem ?_
          rw [hz₀eq, hgy]
        · have hgy : γ = -y₀.im := by rw [hγdef, he]
          refine sturmCoeff_eq_zero_of_mem' ?_
          rw [hz₀eq, hgy]
          push_cast; ring
      set S₁ : Finset ℂ := S'.filter (fun z => sturmCoeff C' γ z ≠ 0) with hS₁d
      set C₁ : ℂ → ℂ := sturmCoeff C' γ with hC₁d
      have hsub1 : S₁ ⊆ S' := Finset.filter_subset _ _
      have hsum1 : ∀ t : ℝ, ∑ z ∈ S₁, C₁ z * Complex.exp (z * t)
          = ∑ z ∈ S', C₁ z * Complex.exp (z * t) := by
        intro t
        refine Finset.sum_subset hsub1 (fun x hx hnx => ?_)
        have hzz : C₁ x = 0 := by
          by_contra hc
          exact hnx (by rw [hS₁d, Finset.mem_filter]; exact ⟨hx, hc⟩)
        rw [hzz, zero_mul]
      by_cases hS₁ne : S₁.Nonempty
      · -- the generic branch: the reduction leaves something
        obtain ⟨w, hw⟩ := hS₁ne
        have hC₁ne : ∀ z ∈ S₁, C₁ z ≠ 0 := by
          intro z hz
          rw [hS₁d, Finset.mem_filter] at hz
          exact hz.2
        have hreal₁ : ∀ t : ℝ, (∑ z ∈ S₁, C₁ z * Complex.exp (z * t)).im = 0 := by
          intro t
          rw [hsum1 t]
          exact sturm_expCombo_real hreal' γ t
        have hγ₁ : ∀ z ∈ S₁, |z.im| ≤ γ₀ := fun z hz => him' z (hsub1 hz)
        have hcard₁ : S₁.card ≤ S.card :=
          le_trans (Finset.card_le_card hsub1) (le_of_eq hS'card)
        have hz₀mem : z₀ ∈ S'.filter (fun z => z.im ≠ 0) :=
          Finset.mem_filter.mpr ⟨hz₀S', by rw [hz₀im]; exact hy₀im⟩
        have hle' : (S'.filter (fun z => z.im ≠ 0)).card
            ≤ (S.filter (fun y => y.im ≠ 0)).card := by
          refine Finset.card_le_card_of_injOn (fun z => z + ((β : ℝ) : ℂ)) ?_ ?_
          · intro z hz
            simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
            refine ⟨hmemS' z hz.1, ?_⟩
            rw [← shift_im_eq β z]
            exact hz.2
          · intro x _ y _ hxy
            simpa using hxy
        have hposc : 1 ≤ (S'.filter (fun z => z.im ≠ 0)).card :=
          Finset.card_pos.mpr ⟨z₀, hz₀mem⟩
        have hfilt : (S₁.filter (fun z => z.im ≠ 0)).card ≤ N := by
          have hsube : S₁.filter (fun z => z.im ≠ 0)
              ⊆ (S'.filter (fun z => z.im ≠ 0)).erase z₀ := by
            intro z hz
            rw [Finset.mem_filter] at hz
            refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hsub1 hz.1, hz.2⟩⟩
            intro hcon
            exact hC₁ne z hz.1 (by rw [hcon]; exact hz₀coeff)
          have hcarderase : ((S'.filter (fun z => z.im ≠ 0)).erase z₀).card
              = (S'.filter (fun z => z.im ≠ 0)).card - 1 := Finset.card_erase_of_mem hz₀mem
          have hstep := Finset.card_le_card hsube
          omega
        have hfin : {t : ℝ | t ∈ Icc a b ∧ (∑ z ∈ S₁, C₁ z * Complex.exp (z * t)).re = 0}.Finite :=
          finite_zeros_expPoly hw (hC₁ne w hw) hreal₁
        set W₀ : Finset ℝ := hfin.toFinset with hW₀d
        have hW₀mem : ∀ x ∈ W₀, x ∈ Icc a b := by
          intro x hx
          rw [hW₀d, Set.Finite.mem_toFinset] at hx
          exact hx.1
        have hW₀zero : ∀ x ∈ W₀, (∑ z ∈ S₁, C₁ z * Complex.exp (z * x)).re = 0 := by
          intro x hx
          rw [hW₀d, Set.Finite.mem_toFinset] at hx
          exact hx.2
        have hW₀all : ∀ x ∈ Icc a b,
            (∑ z ∈ S₁, C₁ z * Complex.exp (z * x)).re = 0 → x ∈ W₀ := by
          intro x hx hz
          rw [hW₀d, Set.Finite.mem_toFinset]
          exact ⟨hx, hz⟩
        have hIH := ih S₁ C₁ γ₀ a b W₀ hfilt ⟨w, hw⟩ hC₁ne hγ₁ hreal₁ hab hW₀mem hW₀zero hW₀all
        set W : Finset ℝ := W₀.filter (fun x => a < x ∧ x < b) with hWd
        have hWcard : W.card ≤ W₀.card := Finset.card_le_card (Finset.filter_subset _ _)
        have hWmem : ∀ x ∈ W, x ∈ Ioo a b := by
          intro x hx
          rw [hWd, Finset.mem_filter] at hx
          exact ⟨hx.2.1, hx.2.2⟩
        have hWall : ∀ x ∈ Ioo a b,
            (∑ z ∈ S', sturmCoeff C' γ z * Complex.exp (z * x)).re = 0 → x ∈ W := by
          intro x hx hzz
          rw [hWd, Finset.mem_filter]
          refine ⟨hW₀all x ⟨hx.1.le, hx.2.le⟩ ?_, hx.1, hx.2⟩
          rw [hsum1 x]
          exact hzz
        have hZzero' : ∀ x ∈ Z, (∑ z ∈ S', C' z * Complex.exp (z * x)).re = 0 :=
          fun x hx => (hzeroiff x).mpr (hZzero x hx)
        have hZall' : ∀ x ∈ Icc a b,
            (∑ z ∈ S', C' z * Complex.exp (z * x)).re = 0 → x ∈ Z :=
          fun x hx hzz => hZall x hx ((hzeroiff x).mp hzz)
        have hred := card_zeros_le_reduce (S := S') (C := C') hγ hab hreal' Z W
          (M := W.card) le_rfl hWmem hWall hZmem hZzero' hZall'
        have hlen : (b - a) * γ / π ≤ L := by
          have hd : L - (b - a) * γ / π = (b - a) * (γ₀ - γ) / π := by
            rw [hLdef]; field_simp
          have hnn : (0 : ℝ) ≤ (b - a) * (γ₀ - γ) / π :=
            div_nonneg (mul_nonneg hba (by linarith)) Real.pi_pos.le
          linarith
        have hWc : (W.card : ℝ) ≤ (W₀.card : ℝ) := by exact_mod_cast hWcard
        have hn₁ : (S₁.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard₁
        have hmul : (3 : ℝ) ^ N * ((S₁.card : ℝ) + 2 * L + 1)
            ≤ 3 ^ N * ((S.card : ℝ) + 2 * L + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hpownn
        rw [hpowsucc]
        nlinarith [hred, hWc, hIH, hmul, hlen, hL]
      · -- the degenerate branch: the reduction annihilates everything
        rw [Finset.not_nonempty_iff_eq_empty] at hS₁ne
        have hpair : ∀ z ∈ S', z = Complex.I * ((γ : ℝ) : ℂ)
            ∨ z = -(Complex.I * ((γ : ℝ) : ℂ)) := by
          intro z hz
          have hzero : sturmCoeff C' γ z = 0 := by
            by_contra hc
            have hmem : z ∈ S₁ := by rw [hS₁d, Finset.mem_filter]; exact ⟨hz, hc⟩
            rw [hS₁ne] at hmem
            exact absurd hmem (Finset.notMem_empty z)
          exact eq_pair_of_sturmCoeff_eq_zero (hC'ne z hz) hzero
        have hZzero' : ∀ x ∈ Z, (∑ z ∈ S', C' z * Complex.exp (z * x)).re = 0 :=
          fun x hx => (hzeroiff x).mpr (hZzero x hx)
        have hZall' : ∀ x ∈ Icc a b,
            (∑ z ∈ S', C' z * Complex.exp (z * x)).re = 0 → x ∈ Z :=
          fun x hx hzz => hZall x hx ((hzeroiff x).mp hzz)
        have hex : ∃ t₁ : ℝ, (∑ z ∈ S', C' z * Complex.exp (z * t₁)).re ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact not_finset_covers_Icc hab Z (fun x hx => hZall' x hx (hcon x))
        obtain ⟨t₁, ht₁⟩ := hex
        have hcnt := card_zeros_degenerate_energy hγ hab.le hpair hreal' ht₁ Z hZmem
          hZzero' hZall'
        have hlen : (b - a) * γ / π ≤ L := by
          have hd : L - (b - a) * γ / π = (b - a) * (γ₀ - γ) / π := by
            rw [hLdef]; field_simp
          have hnn : (0 : ℝ) ≤ (b - a) * (γ₀ - γ) / π :=
            div_nonneg (mul_nonneg hba (by linarith)) Real.pi_pos.le
          linarith
        nlinarith [hcnt, hlen, hslack, hL, hn1]

/-! ## The usable form -/

open Classical in
/-- **The zero count of a real exponential polynomial.**  Any set of zeros in `[a,b]` of a
real-valued exponential polynomial with nonzero coefficients and imaginary parts bounded by `γ₀`
obeys the bound with `N = |S|`; no hypothesis that the set is *all* the zeros is needed, because the
full zero set is finite and contains it. -/
theorem card_zeros_le_expPoly {S : Finset ℂ} {C : ℂ → ℂ} {γ₀ a b : ℝ}
    (hSne : S.Nonempty) (hCne : ∀ y ∈ S, C y ≠ 0) (hγ₀ : ∀ y ∈ S, |y.im| ≤ γ₀)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) (hab : a < b)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b)
    (hZzero : ∀ x ∈ Z, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0) :
    (Z.card : ℝ)
      ≤ 3 ^ S.card * ((S.card : ℝ) + 2 * ((b - a) * γ₀ / π) + 1)
        - (2 * ((b - a) * γ₀ / π) + 1) := by
  classical
  obtain ⟨y₁, hy₁⟩ := hSne
  have hfin : {t : ℝ | t ∈ Icc a b ∧ (∑ y ∈ S, C y * Complex.exp (y * t)).re = 0}.Finite :=
    finite_zeros_expPoly hy₁ (hCne y₁ hy₁) hreal
  set Z' : Finset ℝ := hfin.toFinset with hZ'd
  have hZ'mem : ∀ x ∈ Z', x ∈ Icc a b := by
    intro x hx
    rw [hZ'd, Set.Finite.mem_toFinset] at hx
    exact hx.1
  have hZ'zero : ∀ x ∈ Z', (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0 := by
    intro x hx
    rw [hZ'd, Set.Finite.mem_toFinset] at hx
    exact hx.2
  have hZ'all : ∀ x ∈ Icc a b, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0 → x ∈ Z' := by
    intro x hx hz
    rw [hZ'd, Set.Finite.mem_toFinset]
    exact ⟨hx, hz⟩
  have hsub : Z ⊆ Z' := fun x hx => hZ'all x (hZmem x hx) (hZzero x hx)
  have hcard : (Z.card : ℝ) ≤ (Z'.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hbound := card_zeros_expPoly S.card S C γ₀ a b Z' (Finset.card_filter_le _ _)
    ⟨y₁, hy₁⟩ hCne hγ₀ hreal hab hZ'mem hZ'zero hZ'all
  linarith

open Classical in
/-- **The Pólya shape.**  The same bound read as a constant plus a linear density in the interval
length: the zero count grows at most linearly in `(b-a)γ₀/π`, with both constants depending only on
the number of exponents. -/
theorem card_zeros_le_expPoly_linear {S : Finset ℂ} {C : ℂ → ℂ} {γ₀ a b : ℝ}
    (hSne : S.Nonempty) (hCne : ∀ y ∈ S, C y ≠ 0) (hγ₀ : ∀ y ∈ S, |y.im| ≤ γ₀)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) (hab : a < b)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b)
    (hZzero : ∀ x ∈ Z, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0) :
    (Z.card : ℝ)
      ≤ (3 ^ S.card * ((S.card : ℝ) + 1) - 1)
        + 2 * (3 ^ S.card - 1) * ((b - a) * γ₀ / π) := by
  have h := card_zeros_le_expPoly hSne hCne hγ₀ hreal hab Z hZmem hZzero
  nlinarith [h]

end GaloisForLFunctions.HTGeometry
