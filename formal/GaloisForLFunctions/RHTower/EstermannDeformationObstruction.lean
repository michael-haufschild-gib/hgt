import GaloisForLFunctions.RHTower.EstermannKloostermanSaving
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion

/-!
# Square-root cancellation does not constrain the zeros

Weil's bound on the Kloosterman coefficients is a statement about the modulus, not about the
coefficient sequence: it holds for **any** sequence bounded by a constant times the divisor
function.  So the pair of inputs

* `‖f N‖ ≤ C d(N)`,
* square-root cancellation `‖∑_N f(N) S(N,b;p) N^{−s}‖ ≤ C · 2√p · ∑_N d(N)N^{−σ}`,

is satisfied by the deformed divisor coefficients `f_c(N) = d(N) − c·d(N/2)·[2 ∣ N]`, whose Dirichlet
series is `ζ(s)²(1 − c·2^{−s})`.  Taking `c = 2^θ` puts a zero at `s = θ` for **any** `θ`, in
particular anywhere in the critical strip.  The two inputs are therefore compatible with zeros
arbitrarily placed: they carry no information about the location of the zeros at all.

What the deformation destroys is the functional equation, and nothing else.  In this lane the
functional equation is the only input that can pin a zero.
-/

open Complex Finset
open RHTower.Sieve

namespace RHTower

noncomputable section

/-! ## The divisor Dirichlet series in term form -/

theorem hasSum_divisorTerm {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun N : ℕ => (N.divisors.card : ℂ) * LSeries.term (1 : ℕ → ℂ) s N)
      (riemannZeta s ^ 2) := by
  have hsum : HasSum (LSeries.term (fun N : ℕ => (N.divisors.card : ℂ)) s)
      (riemannZeta s ^ 2) := by
    have h := (RHTower.Sieve.LSeriesSummable_card_divisors hs).hasSum
    have he : LSeries (fun N : ℕ => (N.divisors.card : ℂ)) s = riemannZeta s ^ 2 :=
      RHTower.Sieve.LSeries_card_divisors_eq_riemannZeta_sq hs
    rw [← he]
    exact h
  refine hsum.congr_fun (fun N => ?_)
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · rw [LSeries.term_of_ne_zero hN, LSeries.term_of_ne_zero hN]
    simp only [Pi.one_apply, one_div]
    exact (div_eq_mul_inv _ _).symm

/-- The weight `n ↦ n^{-s}` is completely multiplicative, with the value `0` at `n = 0`. -/
theorem term_one_mul (s : ℂ) (a b : ℕ) :
    LSeries.term (1 : ℕ → ℂ) s (a * b)
      = LSeries.term (1 : ℕ → ℂ) s a * LSeries.term (1 : ℕ → ℂ) s b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hab : a * b ≠ 0 := Nat.mul_ne_zero ha hb
  have hcast : ((((a * b : ℕ)) : ℂ)) ^ s = ((a : ℂ)) ^ s * ((b : ℂ)) ^ s := by
    have h1 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
    have h := Complex.mul_cpow_ofReal_nonneg h1 h2 s
    push_cast at h ⊢
    exact h
  rw [LSeries.term_of_ne_zero hab, LSeries.term_of_ne_zero ha, LSeries.term_of_ne_zero hb, hcast]
  simp only [Pi.one_apply, one_div, mul_inv]

theorem norm_term_one (s : ℂ) (N : ℕ) :
    ‖LSeries.term (1 : ℕ → ℂ) s N‖ = (N : ℝ) ^ (-s.re) ∨ N = 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact Or.inr rfl
  · refine Or.inl ?_
    rw [LSeries.term_of_ne_zero hN, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN), Real.rpow_neg (Nat.cast_nonneg N)]
    simp

/-! ## The deformation -/

/-- The divisor coefficients deformed by an Euler factor `1 − c·2^{−s}` at the prime two. -/
def deformedDivisorCoeff (c : ℂ) (N : ℕ) : ℂ :=
  (N.divisors.card : ℂ) - c * (if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℂ) else 0)

theorem norm_deformedDivisorCoeff_le (c : ℂ) (N : ℕ) :
    ‖deformedDivisorCoeff c N‖ ≤ (1 + ‖c‖) * (N.divisors.card : ℝ) := by
  classical
  have hsub : ((if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℝ) else 0))
      ≤ (N.divisors.card : ℝ) := by
    by_cases hd : 2 ∣ N
    · rw [if_pos hd]
      rcases eq_or_ne N 0 with rfl | hN
      · simp
      · have hdvd : N / 2 ∣ N := Nat.div_dvd_of_dvd hd
        have := Finset.card_le_card (Nat.divisors_subset_of_dvd hN hdvd)
        exact_mod_cast this
    · rw [if_neg hd]
      exact Nat.cast_nonneg _
  have hnn : (0 : ℝ) ≤ ((if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℝ) else 0)) := by
    by_cases hd : 2 ∣ N <;> simp [hd]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have h1 : ‖((N.divisors.card : ℕ) : ℂ)‖ = (N.divisors.card : ℝ) := by
    simp
  have h2 : ‖(if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℂ) else 0)‖
      = (if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℝ) else 0) := by
    by_cases hd : 2 ∣ N <;> simp [hd]
  rw [h1, h2]
  nlinarith [hsub, hnn, norm_nonneg c, Nat.cast_nonneg (α := ℝ) N.divisors.card]

/-- The deformed coefficients carry the Euler factor. -/
theorem hasSum_deformedDivisorCoeff (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun N : ℕ => deformedDivisorCoeff c N * LSeries.term (1 : ℕ → ℂ) s N)
      (riemannZeta s ^ 2 * (1 - c * LSeries.term (1 : ℕ → ℂ) s 2)) := by
  classical
  have hshift : HasSum (fun N : ℕ =>
      (if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℂ) else 0) * LSeries.term (1 : ℕ → ℂ) s N)
      (LSeries.term (1 : ℕ → ℂ) s 2 * riemannZeta s ^ 2) := by
    have hinj : Function.Injective (fun M : ℕ => 2 * M) := fun a b hab => by
      simpa using hab
    have hoff : ∀ N : ℕ, N ∉ Set.range (fun M : ℕ => 2 * M) →
        (if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℂ) else 0) *
          LSeries.term (1 : ℕ → ℂ) s N = 0 := by
      intro N hN
      rw [if_neg, zero_mul]
      intro hd
      exact hN ⟨N / 2, (Nat.mul_div_cancel' hd)⟩
    refine (Function.Injective.hasSum_iff hinj hoff).mp ?_
    have hcomp : ∀ M : ℕ,
        ((fun N : ℕ => (if 2 ∣ N then (((N / 2).divisors.card : ℕ) : ℂ) else 0) *
          LSeries.term (1 : ℕ → ℂ) s N) ∘ (fun M : ℕ => 2 * M)) M
          = LSeries.term (1 : ℕ → ℂ) s 2 *
              ((M.divisors.card : ℂ) * LSeries.term (1 : ℕ → ℂ) s M) := by
      intro M
      simp only [Function.comp_apply, if_pos (Dvd.intro M rfl), Nat.mul_div_cancel_left M two_pos]
      rw [term_one_mul s 2 M]
      ring
    exact ((hasSum_divisorTerm hs).mul_left _).congr_fun hcomp
  have hmain := (hasSum_divisorTerm hs).sub (hshift.mul_left c)
  have hval : riemannZeta s ^ 2 - c * (LSeries.term (1 : ℕ → ℂ) s 2 * riemannZeta s ^ 2)
      = riemannZeta s ^ 2 * (1 - c * LSeries.term (1 : ℕ → ℂ) s 2) := by ring
  rw [← hval]
  refine hmain.congr_fun (fun N => ?_)
  rw [deformedDivisorCoeff]
  ring

/-! ## The two inputs are blind to the zeros -/

/-- **Weil's saving depends only on the size of the coefficients.**  Any sequence dominated by the
divisor function inherits the full square-root cancellation in the modulus. -/
theorem norm_tsum_kloosterman_weighted_le (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ N : ℕ, ‖f N‖ ≤ C * (N.divisors.card : ℝ)) {s : ℂ} (hs : 1 < s.re) :
    ‖∑' N : ℕ, f N * (kloostermanSum p ((N : ZMod p)) b * LSeries.term (1 : ℕ → ℂ) s N)‖
      ≤ C * (2 * Real.sqrt p) * divisorMass s.re := by
  classical
  have hsq0 : (0 : ℝ) ≤ 2 * Real.sqrt p := by positivity
  have hmaj : ∀ N : ℕ,
      ‖f N * (kloostermanSum p ((N : ZMod p)) b * LSeries.term (1 : ℕ → ℂ) s N)‖
        ≤ C * (2 * Real.sqrt p) * ((N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re)) := by
    intro N
    rcases eq_or_ne N 0 with rfl | hN
    · have h0 : ‖f 0‖ ≤ 0 := by simpa using hf 0
      have : f 0 = 0 := by
        have := norm_nonneg (f 0)
        exact norm_eq_zero.mp (le_antisymm h0 this)
      simp [this]
    · have hterm : ‖LSeries.term (1 : ℕ → ℂ) s N‖ = (N : ℝ) ^ (-s.re) := by
        rcases norm_term_one s N with h | h
        · exact h
        · exact absurd h hN
      rw [norm_mul, norm_mul, hterm]
      have hS := norm_kloostermanSum_le_weil p hp2 ((N : ZMod p)) hb
      have hrp : (0 : ℝ) ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hd0 : (0 : ℝ) ≤ (N.divisors.card : ℝ) := Nat.cast_nonneg _
      have hstep : ‖f N‖ * ‖kloostermanSum p ((N : ZMod p)) b‖ * (N : ℝ) ^ (-s.re)
          ≤ (C * (N.divisors.card : ℝ)) * (2 * Real.sqrt p) * (N : ℝ) ^ (-s.re) := by
        refine mul_le_mul_of_nonneg_right ?_ hrp
        exact mul_le_mul (hf N) hS (norm_nonneg _) (by positivity)
      nlinarith [hstep]
  have hmajsum : Summable
      (fun N : ℕ => C * (2 * Real.sqrt p) * ((N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re))) :=
    (summable_divisorCount_rpow hs).mul_left _
  have hfsum : Summable
      (fun N : ℕ => ‖f N * (kloostermanSum p ((N : ZMod p)) b * LSeries.term (1 : ℕ → ℂ) s N)‖) :=
    Summable.of_nonneg_of_le (fun N => norm_nonneg _) hmaj hmajsum
  calc ‖∑' N : ℕ, f N * (kloostermanSum p ((N : ZMod p)) b * LSeries.term (1 : ℕ → ℂ) s N)‖
      ≤ ∑' N : ℕ, ‖f N * (kloostermanSum p ((N : ZMod p)) b * LSeries.term (1 : ℕ → ℂ) s N)‖ :=
        norm_tsum_le_tsum_norm hfsum
    _ ≤ ∑' N : ℕ, C * (2 * Real.sqrt p) * ((N.divisors.card : ℝ) * (N : ℝ) ^ (-s.re)) :=
        Summable.tsum_le_tsum hmaj hfsum hmajsum
    _ = C * (2 * Real.sqrt p) * divisorMass s.re := by rw [divisorMass, tsum_mul_left]

/-- **The deformed family satisfies the same square-root cancellation.** -/
theorem norm_tsum_kloosterman_deformed_le (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {b : ZMod p} (hb : b ≠ 0) (c : ℂ) {s : ℂ} (hs : 1 < s.re) :
    ‖∑' N : ℕ, deformedDivisorCoeff c N *
        (kloostermanSum p ((N : ZMod p)) b * LSeries.term (1 : ℕ → ℂ) s N)‖
      ≤ (1 + ‖c‖) * (2 * Real.sqrt p) * divisorMass s.re :=
  norm_tsum_kloosterman_weighted_le p hp2 hb (by positivity)
    (norm_deformedDivisorCoeff_le c) hs

/-! ## The deformed Dirichlet series has a zero wherever one likes -/

/-- **The deformation places a zero at any prescribed abscissa.**  For real `θ` the deformed series
`ζ(s)²(1 − 2^{θ−s})` vanishes at `s = θ`. -/
theorem deformed_zero_at (θ : ℝ) :
    riemannZeta ((θ : ℂ)) ^ 2 *
        (1 - (((2 : ℝ) ^ θ : ℝ) : ℂ) * LSeries.term (1 : ℕ → ℂ) ((θ : ℂ)) 2) = 0 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  have hcast : (((2 : ℝ) ^ θ : ℝ) : ℂ) = ((2 : ℕ) : ℂ) ^ ((θ : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hne : ((2 : ℕ) : ℂ) ^ ((θ : ℝ) : ℂ) ≠ 0 := by
    rw [← hcast]
    exact_mod_cast ne_of_gt hpos
  have hterm : LSeries.term (1 : ℕ → ℂ) ((θ : ℂ)) 2
      = (((2 : ℕ) : ℂ) ^ ((θ : ℝ) : ℂ))⁻¹ := by
    rw [LSeries.term_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)]
    simp only [Pi.one_apply, one_div]
  rw [hterm, hcast, mul_inv_cancel₀ hne, sub_self, mul_zero]

/-- **The obstruction.**  For every real `θ` there is a coefficient sequence dominated by the
divisor function, hence carrying the full square-root cancellation in the modulus, whose Dirichlet
series vanishes at `s = θ`.  Taking `θ = 3/4` places the zero inside the critical strip and off the
critical line, so the two inputs are compatible with a violation of the Riemann Hypothesis. -/
theorem exists_weil_compatible_zero (θ : ℝ) :
    ∃ f : ℕ → ℂ,
      (∀ N : ℕ, ‖f N‖ ≤ (1 + (2 : ℝ) ^ θ) * (N.divisors.card : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re →
        HasSum (fun N : ℕ => f N * LSeries.term (1 : ℕ → ℂ) s N)
          (riemannZeta s ^ 2 *
            (1 - (((2 : ℝ) ^ θ : ℝ) : ℂ) * LSeries.term (1 : ℕ → ℂ) s 2))) ∧
      riemannZeta ((θ : ℂ)) ^ 2 *
        (1 - (((2 : ℝ) ^ θ : ℝ) : ℂ) * LSeries.term (1 : ℕ → ℂ) ((θ : ℂ)) 2) = 0 := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ θ := Real.rpow_pos_of_pos (by norm_num) θ
  have hnorm : ‖(((2 : ℝ) ^ θ : ℝ) : ℂ)‖ = (2 : ℝ) ^ θ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  refine ⟨deformedDivisorCoeff (((2 : ℝ) ^ θ : ℝ) : ℂ), fun N => ?_,
    fun s hs => hasSum_deformedDivisorCoeff _ hs, deformed_zero_at θ⟩
  have h := norm_deformedDivisorCoeff_le (((2 : ℝ) ^ θ : ℝ) : ℂ) N
  rwa [hnorm] at h

/-- **What the deformation destroys, and only that.**  The zero set of the deformed series is not
symmetric about the critical line: the factor `1 − 2^{θ−s}` vanishes at `s = θ` but not at
`s = 1 − θ` unless `θ = 1/2`.  So the deformed object has no functional equation of the `ζ²` shape.
Together with the two preceding theorems: the coefficient bound and Weil's square-root cancellation
hold for it, the functional equation does not, and it violates the Riemann Hypothesis.  In this lane
the functional equation is the only input that can pin a zero. -/
theorem deformation_factor_ne_zero_at_reflection {θ : ℝ} (hθ : θ ≠ 1 / 2) :
    (1 : ℂ) - (((2 : ℝ) ^ θ : ℝ) : ℂ) *
        LSeries.term (1 : ℕ → ℂ) (((1 - θ : ℝ) : ℝ) : ℂ) 2 ≠ 0 := by
  have hcast : ∀ u : ℝ, (((2 : ℝ) ^ u : ℝ) : ℂ) = ((2 : ℕ) : ℂ) ^ ((u : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hposu : ∀ u : ℝ, (0 : ℝ) < (2 : ℝ) ^ u := fun u => Real.rpow_pos_of_pos (by norm_num) u
  have hterm : LSeries.term (1 : ℕ → ℂ) (((1 - θ : ℝ) : ℝ) : ℂ) 2
      = ((((2 : ℝ) ^ (1 - θ) : ℝ) : ℂ))⁻¹ := by
    rw [LSeries.term_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0), hcast (1 - θ)]
    simp only [Pi.one_apply, one_div]
  rw [hterm]
  have hne : ((((2 : ℝ) ^ (1 - θ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (hposu (1 - θ))
  have hquot : (((2 : ℝ) ^ θ : ℝ) : ℂ) * ((((2 : ℝ) ^ (1 - θ) : ℝ) : ℂ))⁻¹
      = (((2 : ℝ) ^ (2 * θ - 1) : ℝ) : ℂ) := by
    have hr : (2 : ℝ) ^ θ * ((2 : ℝ) ^ (1 - θ))⁻¹ = (2 : ℝ) ^ (2 * θ - 1) := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [← hr]
    push_cast
    ring
  rw [hquot]
  intro hcon
  have hreal : (2 : ℝ) ^ (2 * θ - 1) = 1 := by
    have := sub_eq_zero.mp hcon
    exact_mod_cast this.symm
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at hreal
  have hlog : Real.log 2 * (2 * θ - 1) = 0 := by
    have h0 : Real.exp (Real.log 2 * (2 * θ - 1)) = Real.exp 0 := by
      rw [hreal, Real.exp_zero]
    exact Real.exp_injective h0
  have hlog2 : Real.log 2 ≠ 0 := by
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  have : 2 * θ - 1 = 0 := by
    rcases mul_eq_zero.mp hlog with h | h
    · exact absurd h hlog2
    · exact h
  apply hθ
  linarith

end

end RHTower
