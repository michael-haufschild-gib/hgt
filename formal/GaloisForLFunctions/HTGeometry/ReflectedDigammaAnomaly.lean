import GaloisForLFunctions.RHTower.WindingAmplitude

/-!
# Reality of the reflected digamma anomaly

For positive height, the imaginary part of `ψ(σ+it)` is strictly decreasing in the
horizontal coordinate `σ ≥ 0`.  Consequently the reflected anomaly

`ψ(σ+it) + ψ(1-σ-it)`

is real in the open strip exactly at `σ=1/2`.  This is the formal archimedean
selector underlying the universal term in the reflected bi-heat finite part.
-/

noncomputable section

namespace ReflectedDigammaAnomaly

open Complex Filter
open scoped ComplexConjugate

/-- Imaginary part of digamma on a positive-height vertical line. -/
def verticalDigammaIm (sigma t : ℝ) : ℝ :=
  (Complex.digamma ((sigma : ℂ) + (t : ℂ) * Complex.I)).im

/-- The positive partial-fraction sums converge to the imaginary part of digamma. -/
theorem tendsto_verticalDigammaIm_partialSums {sigma t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N, t / ((sigma + n) ^ 2 + t ^ 2))
      atTop (nhds (verticalDigammaIm sigma t)) := by
  let z : ℂ := (sigma : ℂ) + (t : ℂ) * Complex.I
  have hz : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.im hm
    dsimp [z] at him
    simp at him
    linarith
  have hsum : ∀ N : ℕ,
      (Complex.digamma z).im -
          (Complex.digamma (z + (N : ℂ))).im =
        ∑ n ∈ Finset.range N, t / ((sigma + n) ^ 2 + t ^ 2) := by
    intro N
    rw [RHTower.digamma_apply_add_nat z hz N, Complex.add_im, Complex.im_sum]
    rw [show ∑ n ∈ Finset.range N, ((z + (n : ℂ))⁻¹).im =
        ∑ n ∈ Finset.range N, -(t / ((sigma + n) ^ 2 + t ^ 2)) from
      Finset.sum_congr rfl fun n _ => by
        dsimp [z]
        exact RHTower.im_inv_shift sigma t n]
    rw [Finset.sum_neg_distrib]
    ring
  have hlim : Tendsto
      (fun N : ℕ =>
        (Complex.digamma z).im -
          (Complex.digamma (z + (N : ℂ))).im)
      atTop (nhds ((Complex.digamma z).im)) := by
    simpa using
      (tendsto_const_nhds.sub
        (RHTower.im_digamma_vertical_anchor_tendsto sigma t))
  exact (hlim.congr fun N => hsum N)

/-- At positive height, `Im ψ(σ+it)` is strictly decreasing for `σ ≥ 0`. -/
theorem verticalDigammaIm_strictAnti {sigma tau t : ℝ}
    (hsigma : 0 ≤ sigma) (hst : sigma < tau) (ht : 0 < t) :
    verticalDigammaIm tau t < verticalDigammaIm sigma t := by
  have htau : 0 < tau := lt_of_le_of_lt hsigma hst
  have hlim :=
    (tendsto_verticalDigammaIm_partialSums (sigma := tau) ht).sub
      (tendsto_verticalDigammaIm_partialSums (sigma := sigma) ht)
  let C : ℝ := t / (tau ^ 2 + t ^ 2) - t / (sigma ^ 2 + t ^ 2)
  have hCneg : C < 0 := by
    dsimp [C]
    have hsq : sigma ^ 2 < tau ^ 2 := by nlinarith
    have hds : 0 < sigma ^ 2 + t ^ 2 := by positivity
    have hdt : 0 < tau ^ 2 + t ^ 2 := by positivity
    have hfrac : t / (tau ^ 2 + t ^ 2) < t / (sigma ^ 2 + t ^ 2) := by
      rw [div_lt_div_iff₀ hdt hds]
      nlinarith
    linarith
  have hbound : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, t / ((tau + n) ^ 2 + t ^ 2)) -
          (∑ n ∈ Finset.range N, t / ((sigma + n) ^ 2 + t ^ 2)) ≤ C := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have htail :
        (∑ n ∈ Finset.range M,
            t / ((tau + (n + 1)) ^ 2 + t ^ 2)) -
          (∑ n ∈ Finset.range M,
            t / ((sigma + (n + 1)) ^ 2 + t ^ 2)) ≤ 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_nonpos
      intro n _
      have hspos : 0 < sigma + (n + 1) := by positivity
      have hlt : sigma + (n + 1) < tau + (n + 1) := by linarith
      have hsqn : (sigma + (n + 1)) ^ 2 < (tau + (n + 1)) ^ 2 := by nlinarith
      have hds : 0 < (sigma + (n + 1)) ^ 2 + t ^ 2 := by positivity
      have hdt : 0 < (tau + (n + 1)) ^ 2 + t ^ 2 := by positivity
      have hfrac :
          t / ((tau + (n + 1)) ^ 2 + t ^ 2) ≤
            t / ((sigma + (n + 1)) ^ 2 + t ^ 2) := by
        rw [div_le_div_iff₀ hdt hds]
        nlinarith
      linarith
    have hzero :
        t / ((tau + (0 : ℕ)) ^ 2 + t ^ 2) -
            t / ((sigma + (0 : ℕ)) ^ 2 + t ^ 2) = C := by
      simp [C]
    push_cast at htail hzero ⊢
    linarith
  have hle : verticalDigammaIm tau t - verticalDigammaIm sigma t ≤ C :=
    le_of_tendsto hlim hbound
  linarith

/-- Digamma respects complex conjugation. -/
theorem digamma_conj (z : ℂ) :
    Complex.digamma (conj z) = conj (Complex.digamma z) := by
  have hfun : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
    funext w
    simp [Function.comp_def, Complex.Gamma_conj]
  have hderiv := deriv_conj_conj (f := Complex.Gamma)
  rw [hfun] at hderiv
  have hd : deriv Complex.Gamma (conj z) = conj (deriv Complex.Gamma z) := by
    have := congrFun hderiv (conj z)
    simpa [Function.comp_def] using this
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, hd,
    Complex.Gamma_conj, map_div₀]

/-- The reflected archimedean finite-part anomaly. -/
def anomaly (sigma t : ℝ) : ℂ :=
  Complex.digamma ((sigma : ℂ) + (t : ℂ) * Complex.I) +
    Complex.digamma (((1 - sigma : ℝ) : ℂ) - (t : ℂ) * Complex.I)

/-- The imaginary anomaly is the difference of the two positive-height digamma profiles. -/
theorem anomaly_im_eq_sub (sigma t : ℝ) :
    (anomaly sigma t).im =
      verticalDigammaIm sigma t - verticalDigammaIm (1 - sigma) t := by
  have harg :
      (((1 - sigma : ℝ) : ℂ) - (t : ℂ) * Complex.I) =
        conj (((1 - sigma : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  rw [anomaly, Complex.add_im, harg, digamma_conj, Complex.conj_im]
  rfl

/-- For positive height and inside the open strip, the reflected digamma anomaly is real
exactly at the critical line. -/
theorem anomaly_im_eq_zero_iff {sigma t : ℝ}
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (ht : 0 < t) :
    (anomaly sigma t).im = 0 ↔ sigma = 1 / 2 := by
  rw [anomaly_im_eq_sub, sub_eq_zero]
  constructor
  · intro heq
    rcases lt_trichotomy sigma (1 - sigma) with hlt | heq' | hgt
    · exfalso
      have hstrict := verticalDigammaIm_strictAnti hsigma.le hlt ht
      exact (ne_of_lt hstrict) heq.symm
    · linarith
    · exfalso
      have hnonneg : 0 ≤ 1 - sigma := by linarith
      have hstrict := verticalDigammaIm_strictAnti hnonneg hgt ht
      exact (ne_of_lt hstrict) heq
  · intro hs
    subst sigma
    norm_num

end ReflectedDigammaAnomaly
