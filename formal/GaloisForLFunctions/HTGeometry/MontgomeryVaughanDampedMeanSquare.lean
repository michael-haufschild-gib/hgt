import GaloisForLFunctions.HTGeometry.MontgomeryVaughanBandPerturbation
import GaloisForLFunctions.HTGeometry.RiemannGaussian.MontgomeryVaughan.Spacing

/-!
# Damped Montgomery–Vaughan inequality

For frequencies `u_r` with pairwise gaps at least `D` and *nonpositive* exponents
`−K ≤ θ_r ≤ 0`, the mean square of the damped exponential sum
`S(α) = Σ_r d_r e^{θ_r α} e^{2πi u_r α}` over `[a, a+ℓ]` satisfies

`(ℓ₀ e^{−2Kℓ₀} − 26/(πD) − 9K/(π²D²)) · Σ_r |d_r|² e^{2θ_r a} ≤ ∫_a^{a+ℓ} |S|²
   ≤ (ℓ + 26/(πD) + 9K/(π²D²)) · Σ_r |d_r|² e^{2θ_r a}`

for every `0 ≤ ℓ₀ ≤ ℓ`.  The weights `|d_r|² e^{2θ_r a}` are the energies of the individual
terms at the bottom of the window.  The mechanism: the pair integral has the exact value
`(e^{w b} − e^{w a})/w` with `w = (θ_r+θ_s) + 2πi(u_r−u_s)`; replacing `1/w` by
`1/(2πi(u_r−u_s))` costs `|θ_r+θ_s|/(|w|·2π|u_r−u_s|) ≤ K/(2π²(u_r−u_s)²)` because
`|w| ≥ |Im w|`, and the two endpoint Hilbert forms are bounded by the corpus's
Montgomery–Vaughan inequality (constant `26`), while the inverse-square remainder is bounded by
the spacing lemma `Σ_{s≠r} 1/(u_r−u_s)² ≤ 9/D²`.  No decay-versus-gap hypothesis is needed:
the dependence on `K` is polynomial, and the bound is uniform in the number of terms.

Consequently, for a band whose top exponent `θ_top` is nonnegative, the same lower bound holds
for `Σ_r |d_r|² e^{2θ_r a}` with `K` the width of the band of exponents.
-/

open Complex MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Complex exponent of the pair `(r, s)`: `(θ r + θ s) + 2πi(u r − u s)`. -/
def mvPairExponent {ι : Type} (u θ : ι → ℝ) (r s : ι) : ℂ :=
  ((θ r + θ s : ℝ) : ℂ) + 2 * Real.pi * I * ((u r - u s : ℝ) : ℂ)

/-- The coefficient of the `r`-th term evaluated at time `t`: `d r e^{θ r t} e^{2πi u r t}`. -/
def mvEndCoeff {ι : Type} (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (t : ℝ) (r : ι) : ℂ :=
  d r * ((Real.exp (θ r * t) : ℝ) : ℂ) * mvExp (u r) t

/-- The bilinear Hilbert form `Σ_{r≠s} x r conj (x s) / (u r − u s)`. -/
def mvHilbertForm {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) (x : ι → ℂ) : ℂ :=
  ∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((u r - u s : ℝ) : ℂ)

/-- The remainder kernel of the pair `(r, s)` between the endpoints `a` and `b`. -/
def mvDampedRem {ι : Type} (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (a b : ℝ) (r s : ι) : ℂ :=
  -(d r * conj (d s) *
      (cexp (mvPairExponent u θ r s * (b : ℂ)) - cexp (mvPairExponent u θ r s * (a : ℂ))) *
        ((θ r + θ s : ℝ) : ℂ) /
          (mvPairExponent u θ r s * (2 * Real.pi * I * ((u r - u s : ℝ) : ℂ))))

theorem two_pi_I_ne_zero_montgomeryVaughanDampedMeanSquare : (2 * Real.pi * I : ℂ) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

theorem mvBandSum_eq_sum_mvEndCoeff {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ)
    (t : ℝ) : mvBandSum u d θ t = ∑ r, mvEndCoeff u d θ t r := rfl

/-- The product of an endpoint coefficient with the conjugate of another is a single
exponential at the pair exponent. -/
theorem mvEndCoeff_mul_conj {ι : Type} (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (t : ℝ) (r s : ι) :
    mvEndCoeff u d θ t r * conj (mvEndCoeff u d θ t s) =
      d r * conj (d s) * cexp (mvPairExponent u θ r s * (t : ℂ)) := by
  unfold mvEndCoeff
  simp only [map_mul, Complex.conj_ofReal]
  have h1 := mvExp_mul_conj_mvExp (u r) (u s) t
  have h2 : ((Real.exp (θ r * t) : ℝ) : ℂ) * ((Real.exp (θ s * t) : ℝ) : ℂ) =
      cexp (((θ r + θ s : ℝ) : ℂ) * (t : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    d r * ((Real.exp (θ r * t) : ℝ) : ℂ) * mvExp (u r) t *
        (conj (d s) * ((Real.exp (θ s * t) : ℝ) : ℂ) * conj (mvExp (u s) t)) =
      d r * conj (d s) *
        ((((Real.exp (θ r * t) : ℝ) : ℂ) * ((Real.exp (θ s * t) : ℝ) : ℂ)) *
          (mvExp (u r) t * conj (mvExp (u s) t))) := by ring
    _ = d r * conj (d s) * (cexp (((θ r + θ s : ℝ) : ℂ) * (t : ℂ)) *
          cexp ((2 * Real.pi * I * ((u r - u s : ℝ) : ℂ)) * (t : ℂ))) := by rw [h1, h2]
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      unfold mvPairExponent
      ring

/-- Pointwise expansion of the squared modulus of the band sum. -/
theorem normSq_mvBandSum_eq_double_sum {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ)
    (θ : ι → ℝ) (t : ℝ) :
    ((‖mvBandSum u d θ t‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ∑ r, ∑ s, d r * conj (d s) * cexp (mvPairExponent u θ r s * (t : ℂ)) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mvBandSum_eq_sum_mvEndCoeff]
  simp only [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  exact mvEndCoeff_mul_conj u d θ t r s

theorem mvPairExponent_ne_zero {ι : Type} (u θ : ι → ℝ) {r s : ι} (h : u r ≠ u s) :
    mvPairExponent u θ r s ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp only [mvPairExponent, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    Complex.zero_im] at him
  have : (u r - u s) ≠ 0 := sub_ne_zero.mpr h
  have hpi := Real.pi_pos
  nlinarith [mul_pos hpi (mul_self_pos.mpr this)]

/-- The norm of the pair exponent is at least the modulus of its imaginary part `2π|u r − u s|`. -/
theorem two_pi_abs_sub_le_norm_mvPairExponent {ι : Type} (u θ : ι → ℝ) (r s : ι) :
    2 * Real.pi * |u r - u s| ≤ ‖mvPairExponent u θ r s‖ := by
  have h := Complex.abs_im_le_norm (mvPairExponent u θ r s)
  have him : (mvPairExponent u θ r s).im = 2 * Real.pi * (u r - u s) := by
    simp [mvPairExponent]
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
  exact h

/-- Real part of the pair exponent times a real number. -/
theorem re_mvPairExponent_mul {ι : Type} (u θ : ι → ℝ) (r s : ι) (t : ℝ) :
    (mvPairExponent u θ r s * (t : ℂ)).re = (θ r + θ s) * t := by
  simp [mvPairExponent]

/-- Norm of the pair exponential at time `t`. -/
theorem norm_cexp_mvPairExponent_mul {ι : Type} (u θ : ι → ℝ) (r s : ι) (t : ℝ) :
    ‖cexp (mvPairExponent u θ r s * (t : ℂ))‖ = Real.exp ((θ r + θ s) * t) := by
  rw [Complex.norm_exp, re_mvPairExponent_mul]

/-- The pair integral over `[a, b]`. -/
theorem integral_cexp_mvPairExponent {ι : Type} (u θ : ι → ℝ) {r s : ι} (h : u r ≠ u s)
    (a b : ℝ) :
    ∫ t in a..b, cexp (mvPairExponent u θ r s * (t : ℂ)) =
      (cexp (mvPairExponent u θ r s * (b : ℂ)) - cexp (mvPairExponent u θ r s * (a : ℂ))) /
        mvPairExponent u θ r s :=
  integral_exp_mul_complex (mvPairExponent_ne_zero u θ h)

/-- Exact decomposition of the off-diagonal pair term into the two endpoint Hilbert terms and
the remainder kernel. -/
theorem offDiagonal_pair_decomposition {ι : Type} (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ)
    (a b : ℝ) {r s : ι} (h : u r ≠ u s) :
    d r * conj (d s) *
        ((cexp (mvPairExponent u θ r s * (b : ℂ)) - cexp (mvPairExponent u θ r s * (a : ℂ))) /
          mvPairExponent u θ r s) =
      (1 / (2 * Real.pi * I)) *
        (mvEndCoeff u d θ b r * conj (mvEndCoeff u d θ b s) / ((u r - u s : ℝ) : ℂ) -
          mvEndCoeff u d θ a r * conj (mvEndCoeff u d θ a s) / ((u r - u s : ℝ) : ℂ)) +
        mvDampedRem u d θ a b r s := by
  rw [mvEndCoeff_mul_conj, mvEndCoeff_mul_conj]
  unfold mvDampedRem
  have hw : mvPairExponent u θ r s ≠ 0 := mvPairExponent_ne_zero u θ h
  have hΔ : ((u r - u s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
  have hP : (2 * Real.pi * I : ℂ) ≠ 0 := two_pi_I_ne_zero_montgomeryVaughanDampedMeanSquare
  have hwdef : mvPairExponent u θ r s =
      ((θ r + θ s : ℝ) : ℂ) + 2 * Real.pi * I * ((u r - u s : ℝ) : ℂ) := rfl
  set w := mvPairExponent u θ r s with hwset
  set E := cexp (w * (b : ℂ)) - cexp (w * (a : ℂ)) with hE
  set Δ := ((u r - u s : ℝ) : ℂ) with hΔdef
  set P := (2 * Real.pi * I : ℂ) with hPdef
  have hkey : (1 / w : ℂ) = 1 / (P * Δ) - ((θ r + θ s : ℝ) : ℂ) / (w * (P * Δ)) := by
    have hPΔ : P * Δ ≠ 0 := mul_ne_zero hP hΔ
    rw [eq_sub_iff_add_eq, div_add_div _ _ hw (mul_ne_zero hw hPΔ),
      div_eq_div_iff (mul_ne_zero hw (mul_ne_zero hw hPΔ)) hPΔ, hwdef]
    ring
  calc
    d r * conj (d s) * (E / w) = d r * conj (d s) * E * (1 / w) := by ring
    _ = d r * conj (d s) * E * (1 / (P * Δ)) -
          d r * conj (d s) * E * ((θ r + θ s : ℝ) : ℂ) / (w * (P * Δ)) := by
      rw [hkey]; ring
    _ = _ := by ring

/-- Norm bound for the remainder kernel: `|rem| ≤ |d r| e^{θ r a} · |d s| e^{θ s a} · K/(π²(u r − u s)²)`
when the exponents lie in `[−K, 0]` and `a ≤ b`. -/
theorem norm_mvDampedRem_le {ι : Type} (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {a b K : ℝ}
    (hab : a ≤ b) (hθ : ∀ r, -K ≤ θ r ∧ θ r ≤ 0) {r s : ι} (h : u r ≠ u s) :
    ‖mvDampedRem u d θ a b r s‖ ≤
      (‖d r‖ * Real.exp (θ r * a)) * (‖d s‖ * Real.exp (θ s * a)) *
        (K / (Real.pi ^ (2 : ℕ) * (u r - u s) ^ (2 : ℕ))) := by
  have hK0 : 0 ≤ K := by linarith [(hθ r).1, (hθ r).2]
  unfold mvDampedRem
  rw [norm_neg, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs]
  have hΔ : 0 < |u r - u s| := abs_pos.mpr (sub_ne_zero.mpr h)
  have hw := two_pi_abs_sub_le_norm_mvPairExponent u θ r s
  have hwpos : 0 < ‖mvPairExponent u θ r s‖ := by
    have : 0 < 2 * Real.pi * |u r - u s| := by positivity
    linarith
  have hE : ‖cexp (mvPairExponent u θ r s * (b : ℂ)) - cexp (mvPairExponent u θ r s * (a : ℂ))‖ ≤
      2 * (Real.exp (θ r * a) * Real.exp (θ s * a)) := by
    have h1 := norm_sub_le (cexp (mvPairExponent u θ r s * (b : ℂ)))
      (cexp (mvPairExponent u θ r s * (a : ℂ)))
    rw [norm_cexp_mvPairExponent_mul, norm_cexp_mvPairExponent_mul] at h1
    have hb : Real.exp ((θ r + θ s) * b) ≤ Real.exp ((θ r + θ s) * a) := by
      apply Real.exp_le_exp.mpr
      nlinarith [(hθ r).2, (hθ s).2]
    have ha : Real.exp ((θ r + θ s) * a) = Real.exp (θ r * a) * Real.exp (θ s * a) := by
      rw [← Real.exp_add]; ring_nf
    linarith
  have hθsum : |θ r + θ s| ≤ 2 * K := by
    rw [abs_le]; constructor <;> linarith [(hθ r).1, (hθ r).2, (hθ s).1, (hθ s).2]
  have hP : ‖(2 * Real.pi * I * ((u r - u s : ℝ) : ℂ) : ℂ)‖ = 2 * Real.pi * |u r - u s| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hP]
  have hden : 2 * Real.pi * |u r - u s| * (2 * Real.pi * |u r - u s|) ≤
      ‖mvPairExponent u θ r s‖ * (2 * Real.pi * |u r - u s|) :=
    mul_le_mul_of_nonneg_right hw (by positivity)
  have hnum : ‖d r‖ * ‖d s‖ *
      ‖cexp (mvPairExponent u θ r s * (b : ℂ)) - cexp (mvPairExponent u θ r s * (a : ℂ))‖ *
        |θ r + θ s| ≤
      ‖d r‖ * ‖d s‖ * (2 * (Real.exp (θ r * a) * Real.exp (θ s * a))) * (2 * K) := by
    have h0 : 0 ≤ ‖d r‖ * ‖d s‖ := by positivity
    have h1 : ‖d r‖ * ‖d s‖ *
        ‖cexp (mvPairExponent u θ r s * (b : ℂ)) - cexp (mvPairExponent u θ r s * (a : ℂ))‖ ≤
        ‖d r‖ * ‖d s‖ * (2 * (Real.exp (θ r * a) * Real.exp (θ s * a))) :=
      mul_le_mul_of_nonneg_left hE h0
    calc
      _ ≤ ‖d r‖ * ‖d s‖ * (2 * (Real.exp (θ r * a) * Real.exp (θ s * a))) * |θ r + θ s| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hθsum (by positivity)
  have hsq : (2 * Real.pi * |u r - u s|) * (2 * Real.pi * |u r - u s|) =
      4 * Real.pi ^ (2 : ℕ) * (u r - u s) ^ (2 : ℕ) := by
    rw [show (u r - u s) ^ (2 : ℕ) = |u r - u s| ^ (2 : ℕ) from (sq_abs _).symm]; ring
  calc
    ‖d r‖ * ‖d s‖ *
        ‖cexp (mvPairExponent u θ r s * (b : ℂ)) - cexp (mvPairExponent u θ r s * (a : ℂ))‖ *
          |θ r + θ s| / (‖mvPairExponent u θ r s‖ * (2 * Real.pi * |u r - u s|))
      ≤ ‖d r‖ * ‖d s‖ * (2 * (Real.exp (θ r * a) * Real.exp (θ s * a))) * (2 * K) /
          (2 * Real.pi * |u r - u s| * (2 * Real.pi * |u r - u s|)) := by
      apply div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = _ := by
      rw [hsq]
      field_simp
      ring

/-- Montgomery–Vaughan bound for the Hilbert form of a coefficient vector. -/
theorem norm_mvHilbertForm_le {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) (x : ι → ℂ)
    {D : ℝ} (hD : 0 < D) (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    ‖mvHilbertForm u x‖ ≤ 26 * ((∑ r, ‖x r‖ ^ (2 : ℕ)) / D) := by
  have hinj : Function.Injective u := by
    intro r s h
    by_contra hrs
    have := hsep r s hrs
    rw [h, sub_self, abs_zero] at this
    linarith
  have hmv := RiemannGaussian.MontgomeryVaughan.mvHilbert_twentySix ι u (fun _ => D)
    x x hinj (fun _ => hD) (fun r s hrs => hsep r s hrs)
  have hsum : (∑ r, ‖x r‖ ^ (2 : ℕ) / D) = (∑ r, ‖x r‖ ^ (2 : ℕ)) / D := (Finset.sum_div _ _ _).symm
  rw [hsum] at hmv
  have hS0 : 0 ≤ (∑ r, ‖x r‖ ^ (2 : ℕ)) / D := by positivity
  have hsq : Real.sqrt ((∑ r, ‖x r‖ ^ (2 : ℕ)) / D) * Real.sqrt ((∑ r, ‖x r‖ ^ (2 : ℕ)) / D) =
      (∑ r, ‖x r‖ ^ (2 : ℕ)) / D := Real.mul_self_sqrt hS0
  calc
    ‖mvHilbertForm u x‖ ≤ 26 * Real.sqrt ((∑ r, ‖x r‖ ^ (2 : ℕ)) / D) *
        Real.sqrt ((∑ r, ‖x r‖ ^ (2 : ℕ)) / D) := hmv
    _ = _ := by rw [mul_assoc, hsq]

/-- Energy of the endpoint coefficients: `‖mvEndCoeff t r‖ = ‖d r‖ e^{θ r t}`. -/
theorem norm_mvEndCoeff {ι : Type} (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (t : ℝ) (r : ι) :
    ‖mvEndCoeff u d θ t r‖ = ‖d r‖ * Real.exp (θ r * t) := by
  unfold mvEndCoeff
  rw [norm_mul, norm_mul, norm_mvExp, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- Inverse-square spacing sum for `D`-separated frequencies: `Σ_{s≠r} 1/(u r − u s)² ≤ 9/D²`. -/
theorem sum_inv_sq_sub_le {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) {D : ℝ}
    (hD : 0 < D) (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) (r : ι) :
    (∑ s, if r = s then (0 : ℝ) else 1 / (u r - u s) ^ (2 : ℕ)) ≤ 9 / D ^ (2 : ℕ) := by
  have hinj : Function.Injective u := by
    intro r s h
    by_contra hrs
    have := hsep r s hrs
    rw [h, sub_self, abs_zero] at this
    linarith
  have hadm : RiemannGaussian.MontgomeryVaughan.Adm u (fun _ => D) :=
    ⟨hinj, fun _ => hD, fun r s hrs => hsep r s hrs⟩
  have hsp := RiemannGaussian.MontgomeryVaughan.Adm.spacing_sq hadm r
  have heq : (∑ s, if r = s then (0 : ℝ) else 1 / (u r - u s) ^ (2 : ℕ)) =
      ∑ s ∈ Finset.univ.erase r, 1 / (u r - u s) ^ (2 : ℕ) := by
    rw [← Finset.sum_erase (Finset.univ) (a := r) (f := fun s => if r = s then (0 : ℝ)
      else 1 / (u r - u s) ^ (2 : ℕ)) (by simp)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have : r ≠ s := fun h => (Finset.mem_erase.mp hs).1 h.symm
    simp [this]
  rw [heq]
  have hmul : D * ∑ s ∈ Finset.univ.erase r, 1 / (u r - u s) ^ (2 : ℕ) ≤ 9 / D := by
    rw [Finset.mul_sum]
    calc
      ∑ s ∈ Finset.univ.erase r, D * (1 / (u r - u s) ^ (2 : ℕ))
          = ∑ s ∈ Finset.univ.erase r, D / (u r - u s) ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
      _ ≤ 9 / D := hsp
  have h9 : 9 / D ^ (2 : ℕ) = (9 / D) / D := by field_simp
  rw [h9, le_div_iff₀ hD]
  linarith

/-- Weighted Schur bound for a symmetric nonnegative kernel: `Σ_{r≠s} w_r w_s k_{rs} ≤ M Σ_r w_r²`
when every row sum `Σ_{s≠r} k_{rs}` is at most `M`. -/
theorem sum_offDiagonal_weighted_le {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (k : ι → ι → ℝ) (hk : ∀ r s, 0 ≤ k r s) (hsymm : ∀ r s, k r s = k s r) {M : ℝ}
    (hrow : ∀ r, (∑ s, if r = s then (0 : ℝ) else k r s) ≤ M) :
    (∑ r, ∑ s, if r = s then (0 : ℝ) else w r * w s * k r s) ≤ M * ∑ r, w r ^ (2 : ℕ) := by
  have hamgm : ∀ r s, w r * w s * k r s ≤ (w r ^ (2 : ℕ) * k r s + w s ^ (2 : ℕ) * k r s) / 2 := by
    intro r s
    have := two_mul_le_add_sq (w r) (w s)
    nlinarith [hk r s]
  have h1 : (∑ r, ∑ s, if r = s then (0 : ℝ) else w r * w s * k r s) ≤
      ∑ r, ∑ s, if r = s then (0 : ℝ) else (w r ^ (2 : ℕ) * k r s + w s ^ (2 : ℕ) * k r s) / 2 := by
    refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => ?_
    split_ifs
    · exact le_rfl
    · exact hamgm r s
  have h2 : (∑ r, ∑ s, if r = s then (0 : ℝ) else (w r ^ (2 : ℕ) * k r s + w s ^ (2 : ℕ) * k r s) / 2) =
      ∑ r, ∑ s, if r = s then (0 : ℝ) else w r ^ (2 : ℕ) * k r s := by
    have hsplit : (∑ r, ∑ s, if r = s then (0 : ℝ) else (w r ^ (2 : ℕ) * k r s + w s ^ (2 : ℕ) * k r s) / 2) =
        (∑ r, ∑ s, if r = s then (0 : ℝ) else w r ^ (2 : ℕ) * k r s / 2) +
          ∑ r, ∑ s, if r = s then (0 : ℝ) else w s ^ (2 : ℕ) * k r s / 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs
      · simp
      · ring
    have hswap : (∑ r, ∑ s, if r = s then (0 : ℝ) else w s ^ (2 : ℕ) * k r s / 2) =
        ∑ r, ∑ s, if r = s then (0 : ℝ) else w r ^ (2 : ℕ) * k r s / 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
      rw [hsymm r s]
      by_cases h : r = s
      · subst h; simp
      · have h' : s ≠ r := fun e => h e.symm
        simp [h, h']
    rw [hsplit, hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · simp
    · ring
  have h3 : (∑ r, ∑ s, if r = s then (0 : ℝ) else w r ^ (2 : ℕ) * k r s) ≤ M * ∑ r, w r ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have : (∑ s, if r = s then (0 : ℝ) else w r ^ (2 : ℕ) * k r s) =
        w r ^ (2 : ℕ) * ∑ s, if r = s then (0 : ℝ) else k r s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> simp
    rw [this, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hrow r) (sq_nonneg _)
  linarith

/-- The off-diagonal remainder sum is bounded by `9K/(π²D²)` times the bottom energy. -/
theorem norm_sum_mvDampedRem_le {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) (d : ι → ℂ)
    (θ : ι → ℝ) {D a b K : ℝ} (hD : 0 < D) (hab : a ≤ b) (hK0 : 0 ≤ K)
    (hθ : ∀ r, -K ≤ θ r ∧ θ r ≤ 0) (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s‖ ≤
      9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ)) * ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
  have hne : ∀ r s, r ≠ s → u r ≠ u s := by
    intro r s hrs h
    have := hsep r s hrs
    rw [h, sub_self, abs_zero] at this
    linarith
  set wt : ι → ℝ := fun r => ‖d r‖ * Real.exp (θ r * a) with hwt
  set kk : ι → ι → ℝ := fun r s => if r = s then 0 else K / (Real.pi ^ (2 : ℕ) * (u r - u s) ^ (2 : ℕ)) with hkk
  have hkk0 : ∀ r s, 0 ≤ kk r s := by
    intro r s; simp only [hkk]; split_ifs
    · exact le_rfl
    · positivity
  have hkksymm : ∀ r s, kk r s = kk s r := by
    intro r s; simp only [hkk]
    by_cases h : r = s
    · subst h; simp
    · have h' : s ≠ r := fun e => h e.symm
      simp only [h, h', if_false]
      rw [show (u r - u s) ^ (2 : ℕ) = (u s - u r) ^ (2 : ℕ) by ring]
  have hrow : ∀ r, (∑ s, if r = s then (0 : ℝ) else kk r s) ≤ K / Real.pi ^ (2 : ℕ) * (9 / D ^ (2 : ℕ)) := by
    intro r
    have h1 : (∑ s, if r = s then (0 : ℝ) else kk r s) =
        K / Real.pi ^ (2 : ℕ) * ∑ s, if r = s then (0 : ℝ) else 1 / (u r - u s) ^ (2 : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [hkk]
      split_ifs
      · simp
      · field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_sub_le u hD hsep r) (by positivity)
  have hterm : ∀ r s, ‖(if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s)‖ ≤
      (if r = s then (0 : ℝ) else wt r * wt s * kk r s) := by
    intro r s
    by_cases h : r = s
    · simp [h]
    · simp only [h, if_false, hkk, hwt]
      exact norm_mvDampedRem_le u d θ hab hθ (hne r s h)
  calc
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s‖
        ≤ ∑ r, ‖∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s‖ := norm_sum_le _ _
    _ ≤ ∑ r, ∑ s, ‖(if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s)‖ :=
        Finset.sum_le_sum fun r _ => norm_sum_le _ _
    _ ≤ ∑ r, ∑ s, if r = s then (0 : ℝ) else wt r * wt s * kk r s :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hterm r s
    _ ≤ K / Real.pi ^ (2 : ℕ) * (9 / D ^ (2 : ℕ)) * ∑ r, wt r ^ (2 : ℕ) :=
        sum_offDiagonal_weighted_le wt kk hkk0 hkksymm hrow
    _ = 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ)) * ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
      have : ∀ r, wt r ^ (2 : ℕ) = ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
        intro r
        simp only [hwt]
        rw [mul_pow, ← Real.exp_nat_mul]
        push_cast
        ring_nf
      simp_rw [this]
      ring

theorem continuous_mvBandSum' {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) :
    Continuous (mvBandSum u d θ) := by
  unfold mvBandSum
  fun_prop

/-- The diagonal pair exponential is the real exponential `e^{2θ r t}`. -/
theorem cexp_mvPairExponent_diag {ι : Type} (u θ : ι → ℝ) (r : ι) (t : ℝ) :
    cexp (mvPairExponent u θ r r * (t : ℂ)) = ((Real.exp (2 * θ r * t) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  simp only [mvPairExponent, sub_self, Complex.ofReal_zero, mul_zero, add_zero]
  push_cast
  ring

/-- Splitting a double sum into its diagonal and off-diagonal parts. -/
theorem double_sum_split {ι : Type} [Fintype ι] [DecidableEq ι] {M : Type} [AddCommMonoid M]
    (g : ι → ι → M) :
    (∑ r, ∑ s, g r s) = ∑ r, g r r + ∑ r, ∑ s, (if r = s then 0 else g r s) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpt' : ∀ s, g r s = (if r = s then g r s else 0) + (if r = s then 0 else g r s) := by
    intro s
    split_ifs <;> simp
  conv_lhs => rw [Finset.sum_congr rfl fun s _ => hpt' s]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

/-- **Exact decomposition** of the interval mean square of a band sum: diagonal energies plus the
real part of the two endpoint Hilbert forms and the remainder sum. -/
theorem integral_normSq_mvBandSum_eq {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (d : ι → ℂ) (θ : ι → ℝ) {D : ℝ} (hD : 0 < D) (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|)
    (a b : ℝ) :
    (∫ α in a..b, ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) =
      (∑ r, ‖d r‖ ^ (2 : ℕ) * ∫ α in a..b, Real.exp (2 * θ r * α)) +
        ((1 / (2 * Real.pi * I)) *
            (mvHilbertForm u (mvEndCoeff u d θ b) - mvHilbertForm u (mvEndCoeff u d θ a)) +
          ∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s).re := by
  classical
  have hne : ∀ r s, r ≠ s → u r ≠ u s := by
    intro r s hrs h
    have := hsep r s hrs
    rw [h, sub_self, abs_zero] at this
    linarith
  have hcont : ∀ r s, Continuous
      (fun α : ℝ => d r * conj (d s) * cexp (mvPairExponent u θ r s * (α : ℂ))) := by
    intro r s
    fun_prop
  -- the real integral as the real part of a complex double sum of pair integrals
  have hint : (∫ α in a..b, ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) =
      (∑ r, ∑ s, d r * conj (d s) * ∫ α in a..b, cexp (mvPairExponent u θ r s * (α : ℂ))).re := by
    have h1 : ((∫ α in a..b, ‖mvBandSum u d θ α‖ ^ (2 : ℕ) : ℝ) : ℂ) =
        ∫ α in a..b, ((‖mvBandSum u d θ α‖ ^ (2 : ℕ) : ℝ) : ℂ) :=
      (intervalIntegral.integral_ofReal).symm
    have h2 : (∫ α in a..b, ((‖mvBandSum u d θ α‖ ^ (2 : ℕ) : ℝ) : ℂ)) =
        ∑ r, ∑ s, d r * conj (d s) * ∫ α in a..b, cexp (mvPairExponent u θ r s * (α : ℂ)) := by
      simp_rw [normSq_mvBandSum_eq_double_sum]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun s _ => ?_
          rw [intervalIntegral.integral_const_mul]
        · intro s _
          exact (hcont r s).intervalIntegrable _ _
      · intro r _
        exact (continuous_finsetSum _ fun s _ => hcont r s).intervalIntegrable _ _
    have h3 := congrArg Complex.re (h1.trans h2)
    rw [Complex.ofReal_re] at h3
    exact h3
  -- diagonal pair integrals are real
  have hdiag : ∀ r, d r * conj (d r) * ∫ α in a..b, cexp (mvPairExponent u θ r r * (α : ℂ)) =
      ((‖d r‖ ^ (2 : ℕ) * ∫ α in a..b, Real.exp (2 * θ r * α) : ℝ) : ℂ) := by
    intro r
    simp_rw [cexp_mvPairExponent_diag]
    rw [intervalIntegral.integral_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  -- off-diagonal pair integrals decompose
  have hoff : ∀ r s, r ≠ s →
      d r * conj (d s) * ∫ α in a..b, cexp (mvPairExponent u θ r s * (α : ℂ)) =
        (1 / (2 * Real.pi * I)) *
          (mvEndCoeff u d θ b r * conj (mvEndCoeff u d θ b s) / ((u r - u s : ℝ) : ℂ) -
            mvEndCoeff u d θ a r * conj (mvEndCoeff u d θ a s) / ((u r - u s : ℝ) : ℂ)) +
          mvDampedRem u d θ a b r s := by
    intro r s hrs
    rw [integral_cexp_mvPairExponent u θ (hne r s hrs)]
    exact offDiagonal_pair_decomposition u d θ a b (hne r s hrs)
  rw [hint, double_sum_split]
  have hd : (∑ r, d r * conj (d r) * ∫ α in a..b, cexp (mvPairExponent u θ r r * (α : ℂ))) =
      ((∑ r, ‖d r‖ ^ (2 : ℕ) * ∫ α in a..b, Real.exp (2 * θ r * α) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun r _ => hdiag r
  have ho : (∑ r, ∑ s, if r = s then (0 : ℂ)
      else d r * conj (d s) * ∫ α in a..b, cexp (mvPairExponent u θ r s * (α : ℂ))) =
      (1 / (2 * Real.pi * I)) *
          (mvHilbertForm u (mvEndCoeff u d θ b) - mvHilbertForm u (mvEndCoeff u d θ a)) +
        ∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s := by
    simp only [mvHilbertForm, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    split_ifs with hrs
    · simp
    · exact hoff r s hrs
  rw [hd, ho, Complex.add_re, Complex.ofReal_re]

/-- Diagonal energy lower bound: `ℓ₀ e^{−2Kℓ₀} e^{2θa} ≤ ∫_a^{a+ℓ} e^{2θα}` for `−K ≤ θ ≤ 0`
and `0 ≤ ℓ₀ ≤ ℓ`. -/
theorem integral_exp_two_mul_ge {θ a ℓ ℓ₀ K : ℝ} (hℓ₀ : 0 ≤ ℓ₀) (hℓ : ℓ₀ ≤ ℓ) (hθK : -K ≤ θ)
    (hθ0 : θ ≤ 0) :
    ℓ₀ * Real.exp (-(2 * K * ℓ₀)) * Real.exp (2 * θ * a) ≤
      ∫ α in a..a + ℓ, Real.exp (2 * θ * α) := by
  have hK : 0 ≤ K := by linarith
  have hcont : Continuous (fun α : ℝ => Real.exp (2 * θ * α)) := by fun_prop
  have h1 : (∫ α in a..a + ℓ₀, Real.exp (2 * θ * α)) ≤ ∫ α in a..a + ℓ, Real.exp (2 * θ * α) := by
    apply intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
    · exact MeasureTheory.ae_of_all _ fun x => (Real.exp_pos _).le
    · exact hcont.intervalIntegrable _ _
  have h2 : (∫ α in a..a + ℓ₀, Real.exp (-(2 * K * ℓ₀)) * Real.exp (2 * θ * a)) ≤
      ∫ α in a..a + ℓ₀, Real.exp (2 * θ * α) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact intervalIntegrable_const
    · exact hcont.intervalIntegrable _ _
    · intro α hα
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 := hα.1
      have h2 := hα.2
      nlinarith
  have h3 : (∫ α in a..a + ℓ₀, Real.exp (-(2 * K * ℓ₀)) * Real.exp (2 * θ * a)) =
      ℓ₀ * Real.exp (-(2 * K * ℓ₀)) * Real.exp (2 * θ * a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-- Diagonal energy upper bound: `∫_a^{a+ℓ} e^{2θα} ≤ ℓ e^{2θa}` for `θ ≤ 0` and `0 ≤ ℓ`. -/
theorem integral_exp_two_mul_le {θ a ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hθ0 : θ ≤ 0) :
    (∫ α in a..a + ℓ, Real.exp (2 * θ * α)) ≤ ℓ * Real.exp (2 * θ * a) := by
  have hcont : Continuous (fun α : ℝ => Real.exp (2 * θ * α)) := by fun_prop
  have h2 : (∫ α in a..a + ℓ, Real.exp (2 * θ * α)) ≤
      ∫ α in a..a + ℓ, Real.exp (2 * θ * a) := by
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact hcont.intervalIntegrable _ _
    · exact intervalIntegrable_const
    · intro α hα
      rw [Real.exp_le_exp]
      have h1 := hα.1
      nlinarith
  have h3 : (∫ α in a..a + ℓ, Real.exp (2 * θ * a)) = ℓ * Real.exp (2 * θ * a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-- Bottom energy of the endpoint coefficients. -/
theorem sum_normSq_mvEndCoeff {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ)
    (t : ℝ) :
    (∑ r, ‖mvEndCoeff u d θ t r‖ ^ (2 : ℕ)) = ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * t) := by
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [norm_mvEndCoeff, mul_pow, ← Real.exp_nat_mul]
  push_cast
  ring_nf

/-- The off-diagonal term is bounded by `(26/(πD) + 9K/(π²D²))` times the bottom energy. -/
theorem norm_offDiagonal_le {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) (d : ι → ℂ)
    (θ : ι → ℝ) {D a b K : ℝ} (hD : 0 < D) (hab : a ≤ b) (hK0 : 0 ≤ K)
    (hθ : ∀ r, -K ≤ θ r ∧ θ r ≤ 0) (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    ‖(1 / (2 * Real.pi * I)) *
          (mvHilbertForm u (mvEndCoeff u d θ b) - mvHilbertForm u (mvEndCoeff u d θ a)) +
        ∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s‖ ≤
      (26 / (Real.pi * D) + 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
        ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
  set W : ℝ := ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun r _ => by positivity
  have hWb : (∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * b)) ≤ W := by
    refine Finset.sum_le_sum fun r _ => ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.exp_le_exp]
    nlinarith [(hθ r).2]
  have hHb : ‖mvHilbertForm u (mvEndCoeff u d θ b)‖ ≤ 26 * (W / D) := by
    have := norm_mvHilbertForm_le u (mvEndCoeff u d θ b) hD hsep
    rw [sum_normSq_mvEndCoeff] at this
    calc
      _ ≤ _ := this
      _ ≤ 26 * (W / D) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_right hWb hD.le
  have hHa : ‖mvHilbertForm u (mvEndCoeff u d θ a)‖ ≤ 26 * (W / D) := by
    have := norm_mvHilbertForm_le u (mvEndCoeff u d θ a) hD hsep
    rw [sum_normSq_mvEndCoeff] at this
    exact this
  have hrem := norm_sum_mvDampedRem_le u d θ hD hab hK0 hθ hsep
  rw [← hW] at hrem
  have hmain : ‖(1 / (2 * Real.pi * I : ℂ)) *
      (mvHilbertForm u (mvEndCoeff u d θ b) - mvHilbertForm u (mvEndCoeff u d θ a))‖ ≤
      26 / (Real.pi * D) * W := by
    rw [norm_mul, norm_div, norm_one, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
    have h3 : ‖mvHilbertForm u (mvEndCoeff u d θ b) - mvHilbertForm u (mvEndCoeff u d θ a)‖ ≤
        2 * (26 * (W / D)) := by
      calc
        _ ≤ ‖mvHilbertForm u (mvEndCoeff u d θ b)‖ + ‖mvHilbertForm u (mvEndCoeff u d θ a)‖ :=
          norm_sub_le _ _
        _ ≤ 26 * (W / D) + 26 * (W / D) := add_le_add hHb hHa
        _ = _ := by ring
    calc
      1 / (2 * Real.pi) *
          ‖mvHilbertForm u (mvEndCoeff u d θ b) - mvHilbertForm u (mvEndCoeff u d θ a)‖
        ≤ 1 / (2 * Real.pi) * (2 * (26 * (W / D))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 26 / (Real.pi * D) * W := by
        field_simp
  calc
    _ ≤ ‖(1 / (2 * Real.pi * I : ℂ)) *
          (mvHilbertForm u (mvEndCoeff u d θ b) - mvHilbertForm u (mvEndCoeff u d θ a))‖ +
        ‖∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a b r s‖ := norm_add_le _ _
    _ ≤ 26 / (Real.pi * D) * W + 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ)) * W := add_le_add hmain hrem
    _ = _ := by ring

/-- **Damped Montgomery–Vaughan inequality, lower bound.**  For `D`-separated frequencies and
exponents in `[−K, 0]`, the mean square over `[a, a+ℓ]` is at least
`(ℓ₀ e^{−2Kℓ₀} − 26/(πD) − 9K/(π²D²))` times the bottom energy `Σ_r |d_r|² e^{2θ_r a}`, for every
`0 ≤ ℓ₀ ≤ ℓ`. -/
theorem interval_integral_normSq_mvBandSum_ge_damped {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ ℓ₀ K : ℝ} (hD : 0 < D) (hℓ₀ : 0 ≤ ℓ₀)
    (hℓ : ℓ₀ ≤ ℓ) (hK0 : 0 ≤ K) (hθ : ∀ r, -K ≤ θ r ∧ θ r ≤ 0)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    (ℓ₀ * Real.exp (-(2 * K * ℓ₀)) - 26 / (Real.pi * D) - 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
        ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) ≤
      ∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ) := by
  rw [integral_normSq_mvBandSum_eq u d θ hD hsep]
  set W : ℝ := ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) with hW
  have hab : a ≤ a + ℓ := by linarith
  have hdiag : ℓ₀ * Real.exp (-(2 * K * ℓ₀)) * W ≤
      ∑ r, ‖d r‖ ^ (2 : ℕ) * ∫ α in a..a + ℓ, Real.exp (2 * θ r * α) := by
    rw [hW, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have := integral_exp_two_mul_ge (a := a) hℓ₀ hℓ (hθ r).1 (hθ r).2
    calc
      ℓ₀ * Real.exp (-(2 * K * ℓ₀)) * (‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a))
          = ‖d r‖ ^ (2 : ℕ) * (ℓ₀ * Real.exp (-(2 * K * ℓ₀)) * Real.exp (2 * θ r * a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have hoff := norm_offDiagonal_le u d θ hD hab hK0 hθ hsep
  rw [← hW] at hoff
  have hre : -((26 / (Real.pi * D) + 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) * W) ≤
      ((1 / (2 * Real.pi * I)) *
          (mvHilbertForm u (mvEndCoeff u d θ (a + ℓ)) - mvHilbertForm u (mvEndCoeff u d θ a)) +
        ∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a (a + ℓ) r s).re := by
    have h1 := Complex.abs_re_le_norm ((1 / (2 * Real.pi * I)) *
      (mvHilbertForm u (mvEndCoeff u d θ (a + ℓ)) - mvHilbertForm u (mvEndCoeff u d θ a)) +
        ∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a (a + ℓ) r s)
    have h2 := (abs_le.mp h1).1
    linarith
  nlinarith [hdiag, hre]

/-- **Damped Montgomery–Vaughan inequality, upper bound.** -/
theorem interval_integral_normSq_mvBandSum_le_damped {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ K : ℝ} (hD : 0 < D) (hℓ : 0 ≤ ℓ)
    (hK0 : 0 ≤ K) (hθ : ∀ r, -K ≤ θ r ∧ θ r ≤ 0)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    (∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) ≤
      (ℓ + 26 / (Real.pi * D) + 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
        ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
  rw [integral_normSq_mvBandSum_eq u d θ hD hsep]
  set W : ℝ := ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) with hW
  have hab : a ≤ a + ℓ := by linarith
  have hdiag : (∑ r, ‖d r‖ ^ (2 : ℕ) * ∫ α in a..a + ℓ, Real.exp (2 * θ r * α)) ≤ ℓ * W := by
    rw [hW, Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have := integral_exp_two_mul_le (a := a) hℓ (hθ r).2
    calc
      ‖d r‖ ^ (2 : ℕ) * ∫ α in a..a + ℓ, Real.exp (2 * θ r * α)
          ≤ ‖d r‖ ^ (2 : ℕ) * (ℓ * Real.exp (2 * θ r * a)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hoff := norm_offDiagonal_le u d θ hD hab hK0 hθ hsep
  rw [← hW] at hoff
  have hre : ((1 / (2 * Real.pi * I)) *
          (mvHilbertForm u (mvEndCoeff u d θ (a + ℓ)) - mvHilbertForm u (mvEndCoeff u d θ a)) +
        ∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a (a + ℓ) r s).re ≤
      (26 / (Real.pi * D) + 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) * W := by
    have h1 := Complex.re_le_norm ((1 / (2 * Real.pi * I)) *
      (mvHilbertForm u (mvEndCoeff u d θ (a + ℓ)) - mvHilbertForm u (mvEndCoeff u d θ a)) +
        ∑ r, ∑ s, if r = s then (0 : ℂ) else mvDampedRem u d θ a (a + ℓ) r s)
    linarith
  nlinarith [hdiag, hre]

/-- Shifting all exponents by a constant `c` multiplies the band sum by `e^{cα}`. -/
theorem mvBandSum_eq_exp_mul_shift {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ)
    (c α : ℝ) :
    mvBandSum u d θ α = ((Real.exp (c * α) : ℝ) : ℂ) * mvBandSum u d (fun r => θ r - c) α := by
  unfold mvBandSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have : ((Real.exp (θ r * α) : ℝ) : ℂ) =
      ((Real.exp (c * α) : ℝ) : ℂ) * ((Real.exp ((θ r - c) * α) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [this]
  ring

/-- **Damped Montgomery–Vaughan for a band with nonnegative top.**  If the exponents lie in
`[θ_top − K, θ_top]` with `θ_top ≥ 0`, the mean square over `[a, a+ℓ]` is at least
`(ℓ₀ e^{−2Kℓ₀} − 26/(πD) − 9K/(π²D²)) Σ_r |d_r|² e^{2θ_r a}`. -/
theorem interval_integral_normSq_mvBandSum_ge_band {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ ℓ₀ K θtop : ℝ} (hD : 0 < D) (hℓ₀ : 0 ≤ ℓ₀)
    (hℓ : ℓ₀ ≤ ℓ) (hK0 : 0 ≤ K) (hθtop : 0 ≤ θtop) (hθ : ∀ r, θtop - K ≤ θ r ∧ θ r ≤ θtop)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    (ℓ₀ * Real.exp (-(2 * K * ℓ₀)) - 26 / (Real.pi * D) - 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
        ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) ≤
      ∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ) := by
  set θ' : ι → ℝ := fun r => θ r - θtop with hθ'
  have hθ'K : ∀ r, -K ≤ θ' r ∧ θ' r ≤ 0 := by
    intro r
    simp only [hθ']
    constructor <;> linarith [(hθ r).1, (hθ r).2]
  have hcore := interval_integral_normSq_mvBandSum_ge_damped u d θ' (a := a) hD hℓ₀ hℓ hK0 hθ'K hsep
  have hℓ0 : 0 ≤ ℓ := le_trans hℓ₀ hℓ
  -- pointwise comparison on the window
  have hpt : ∀ α ∈ Set.Icc a (a + ℓ),
      Real.exp (2 * θtop * a) * ‖mvBandSum u d θ' α‖ ^ (2 : ℕ) ≤ ‖mvBandSum u d θ α‖ ^ (2 : ℕ) := by
    intro α hα
    rw [mvBandSum_eq_exp_mul_shift u d θ θtop α, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    push_cast
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.exp_le_exp]
    nlinarith [hα.1]
  have hint : Real.exp (2 * θtop * a) * (∫ α in a..a + ℓ, ‖mvBandSum u d θ' α‖ ^ (2 : ℕ)) ≤
      ∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact (((continuous_mvBandSum' u d θ').norm.pow 2).const_mul _).intervalIntegrable _ _
    · exact ((continuous_mvBandSum' u d θ).norm.pow 2).intervalIntegrable _ _
    · exact hpt
  have hweights : Real.exp (2 * θtop * a) * ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ' r * a) =
      ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hθ']
    rw [show ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) =
      ‖d r‖ ^ (2 : ℕ) * (Real.exp (2 * θtop * a) * Real.exp (2 * (θ r - θtop) * a)) by
        rw [← Real.exp_add]; ring_nf]
    ring
  have hE : 0 < Real.exp (2 * θtop * a) := Real.exp_pos _
  calc
    (ℓ₀ * Real.exp (-(2 * K * ℓ₀)) - 26 / (Real.pi * D) - 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
        ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a)
      = Real.exp (2 * θtop * a) *
          ((ℓ₀ * Real.exp (-(2 * K * ℓ₀)) - 26 / (Real.pi * D) - 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
            ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ' r * a)) := by
        rw [← hweights]; ring
    _ ≤ Real.exp (2 * θtop * a) * ∫ α in a..a + ℓ, ‖mvBandSum u d θ' α‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hcore hE.le
    _ ≤ _ := hint

/-- **Damped Montgomery–Vaughan for a band with nonnegative top, upper bound**: the mean square is
at most `e^{2θ_top ℓ} (ℓ + 26/(πD) + 9K/(π²D²)) Σ_r |d_r|² e^{2θ_r a}`. -/
theorem interval_integral_normSq_mvBandSum_le_band {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ K θtop : ℝ} (hD : 0 < D) (hℓ : 0 ≤ ℓ)
    (hK0 : 0 ≤ K) (hθtop : 0 ≤ θtop) (hθ : ∀ r, θtop - K ≤ θ r ∧ θ r ≤ θtop)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    (∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) ≤
      Real.exp (2 * θtop * ℓ) * (ℓ + 26 / (Real.pi * D) + 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
        ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
  set θ' : ι → ℝ := fun r => θ r - θtop with hθ'
  have hθ'K : ∀ r, -K ≤ θ' r ∧ θ' r ≤ 0 := by
    intro r
    simp only [hθ']
    constructor <;> linarith [(hθ r).1, (hθ r).2]
  have hcore := interval_integral_normSq_mvBandSum_le_damped u d θ' (a := a) hD hℓ hK0 hθ'K hsep
  have hpt : ∀ α ∈ Set.Icc a (a + ℓ),
      ‖mvBandSum u d θ α‖ ^ (2 : ℕ) ≤ Real.exp (2 * θtop * (a + ℓ)) * ‖mvBandSum u d θ' α‖ ^ (2 : ℕ) := by
    intro α hα
    rw [mvBandSum_eq_exp_mul_shift u d θ θtop α, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
    push_cast
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [Real.exp_le_exp]
    nlinarith [hα.2]
  have hint : (∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) ≤
      Real.exp (2 * θtop * (a + ℓ)) * ∫ α in a..a + ℓ, ‖mvBandSum u d θ' α‖ ^ (2 : ℕ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact ((continuous_mvBandSum' u d θ).norm.pow 2).intervalIntegrable _ _
    · exact (((continuous_mvBandSum' u d θ').norm.pow 2).const_mul _).intervalIntegrable _ _
    · exact hpt
  have hweights : Real.exp (2 * θtop * a) * ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ' r * a) =
      ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hθ']
    rw [show ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ r * a) =
      ‖d r‖ ^ (2 : ℕ) * (Real.exp (2 * θtop * a) * Real.exp (2 * (θ r - θtop) * a)) by
        rw [← Real.exp_add]; ring_nf]
    ring
  have hsplit : Real.exp (2 * θtop * (a + ℓ)) = Real.exp (2 * θtop * ℓ) * Real.exp (2 * θtop * a) := by
    rw [← Real.exp_add]; ring_nf
  calc
    (∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ))
        ≤ Real.exp (2 * θtop * (a + ℓ)) * ∫ α in a..a + ℓ, ‖mvBandSum u d θ' α‖ ^ (2 : ℕ) := hint
    _ ≤ Real.exp (2 * θtop * (a + ℓ)) *
          ((ℓ + 26 / (Real.pi * D) + 9 * K / (Real.pi ^ (2 : ℕ) * D ^ (2 : ℕ))) *
            ∑ r, ‖d r‖ ^ (2 : ℕ) * Real.exp (2 * θ' r * a)) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
    _ = _ := by
      rw [hsplit, ← hweights]; ring

end

end GaloisForLFunctions.HTGeometry
