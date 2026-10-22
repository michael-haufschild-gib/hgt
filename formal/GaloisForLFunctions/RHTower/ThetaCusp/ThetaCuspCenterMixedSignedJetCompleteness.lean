import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmRawHankelRH
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmAutocorrelationPath
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedFivePointCluster
import GaloisForLFunctions.HTGeometry.SchwartzSpectralQuadraticSeparation

/-!
# Completeness of the actual signed center-mixed source jets

Fourier inversion identifies every raw Hedenmalm current moment with the corresponding literal
center-mixed derivative at the difference origin. The exact relation is

`(2 I)^n m_n = 2 pi f_a^(n)(0)`.

Consequently `m_n = 2 pi * 2^(-n) * s_n`, where `s_(2k) = (-1)^k f_a^(2k)(0)` and
`s_(2k+1) = 0`. Positive geometric scaling preserves the complete Hankel cone. The unwindowed
moment sign theorem therefore makes positivity of this entire signed source-jet hierarchy
throughout the critical aperture equivalent to RH. All-order smoothness, Fourier incidence,
exponential decay, and moment determinacy are source theorems, not remaining assumptions.

The existing physical five-point theorem gives a strict five-dimensional Hankel section of this
very hierarchy. Positivity at every order remains open.
-/

set_option backward.isDefEq.respectTransparency false
open Complex Real MeasureTheory
open scoped FourierTransform SchwartzMap
namespace RHTower
noncomputable section

private theorem coe_iterate_schwartz_deriv (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    ⇑((SchwartzMap.derivCLM ℂ ℂ)^[n] f) = iteratedDeriv n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    change deriv ⇑((SchwartzMap.derivCLM ℂ ℂ)^[n] f) = _
    rw [ih]

/-- The complete jet of a Schwartz source is its Fourier moment sequence at the origin. -/
theorem schwartz_iteratedDeriv_zero_eq_fourierMoment (f : SchwartzMap ℝ ℂ) (n : ℕ) :
    iteratedDeriv n f 0 =
      ∫ ξ : ℝ, (2 * (Real.pi : ℂ) * I * (ξ : ℂ)) ^ n * 𝓕 (f : ℝ → ℂ) ξ := by
  let g : SchwartzMap ℝ ℂ := (SchwartzMap.derivCLM ℂ ℂ)^[n] f
  have hg : (g : ℝ → ℂ) = iteratedDeriv n f := coe_iterate_schwartz_deriv f n
  have hinv := congrFun
    (g.continuous.fourierInv_fourier_eq g.integrable (𝓕 g).integrable) 0
  rw [Real.fourierInv_eq_fourier_neg] at hinv
  rw [Real.fourier_eq] at hinv
  simp only [neg_zero, inner_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul] at hinv
  have hf : 𝓕 (g : ℝ → ℂ) = fun ξ : ℝ =>
      (2 * (Real.pi : ℂ) * I * (ξ : ℂ)) ^ n * 𝓕 (f : ℝ → ℂ) ξ := by
    rw [hg]
    simpa only [smul_eq_mul] using Real.fourier_iteratedDeriv
      (N := (⊤ : ℕ∞)) (f.smooth ⊤)
      (fun k _ => by rw [← coe_iterate_schwartz_deriv f k]; exact
        ((SchwartzMap.derivCLM ℂ ℂ)^[k] f).integrable) (by simp : (n : ℕ∞) ≤ ⊤)
  rw [hf, hg] at hinv
  exact hinv.symm

/-- The actual center-mixed source is smooth at every order throughout its Fourier strip. -/
theorem contDiff_infty_thetaCuspCenterMixedDensity (a : ℝ) (ha : |a| < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (thetaCuspCenterMixedDensity a) := by
  have heq : thetaCuspCenterMixedDensity a = fun x : ℝ =>
      (thetaCuspHorizontalAutocorrelationTangent a ha (2 * x)).re := by
    funext x
    rw [thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity ha]
    simp
  rw [heq]
  exact Complex.reCLM.contDiff.comp
    ((thetaCuspHorizontalAutocorrelationTangent a ha).smooth ⊤ |>.comp
      (contDiff_const.mul contDiff_id))

/-- Exact complex form of the real Hedenmalm current. -/
theorem ofReal_thetaCuspCenterMixedFourierCurrent (a : ℝ) (ha : |a| < 1) (b : ℝ) :
    (thetaCuspCenterMixedFourierCurrent a ha b : ℂ) =
      𝓕 (thetaCuspHorizontalAutocorrelationTangent a ha : ℝ → ℂ) (b / (2 * Real.pi)) := by
  simp only [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm,
    Complex.ofReal_re]
  exact (fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm ha b).symm

/-- **All-order source/moment identity.** The raw current moments are precisely the literal
center-mixed derivatives, with the exact Fourier scale and phase retained. -/
theorem thetaCuspCenterMixed_rawMoment_jet_identity
    (a : ℝ) (ha : |a| < 1) (n : ℕ) :
    (2 * I) ^ n * (weightedMoment volume (thetaCuspCenterMixedFourierCurrent a ha) n : ℂ) =
      (2 * (Real.pi : ℂ)) * ((iteratedDeriv n (thetaCuspCenterMixedDensity a) (0 : ℝ) : ℝ) : ℂ) := by
  let F := thetaCuspHorizontalAutocorrelationTangent a ha
  let H : ℝ → ℂ := fun b => (I * (b : ℂ)) ^ n *
    (thetaCuspCenterMixedFourierCurrent a ha b : ℂ)
  have hphase : (∫ b : ℝ, H b) = I ^ n *
      (weightedMoment volume (thetaCuspCenterMixedFourierCurrent a ha) n : ℂ) := by
    dsimp only [H, weightedMoment]
    simp_rw [mul_pow, mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [integral_const_mul, integral_complex_ofReal]
  have hF : (fun x : ℝ => F (2 * x)) =
      (fun x => (thetaCuspCenterMixedDensity a x : ℂ)) := by
    funext x
    dsimp only [F]
    rw [thetaCuspHorizontalAutocorrelationTangent_eq_centerMixedDensity ha]
    simp
  have hjet : ((iteratedDeriv n (thetaCuspCenterMixedDensity a) (0 : ℝ) : ℝ) : ℂ) =
      (2 : ℂ) ^ n * iteratedDeriv n F 0 := by
    rw [← SchwartzMap.iteratedDeriv_ofReal _
      (contDiff_infty_thetaCuspCenterMixedDensity a ha), ← hF,
      iteratedDeriv_comp_const_smul (F.smooth n) 2]
    simp only [mul_zero, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have hscale := MeasureTheory.Measure.integral_comp_mul_left H (2 * Real.pi)
  have hscaled : (∫ b : ℝ, H b) = (2 * (Real.pi : ℂ)) * iteratedDeriv n F 0 := by
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hH : (fun ξ : ℝ => H ((2 * Real.pi) * ξ)) = fun ξ : ℝ =>
        (2 * (Real.pi : ℂ) * I * (ξ : ℂ)) ^ n * 𝓕 (F : ℝ → ℂ) ξ := by
      funext ξ
      dsimp only [H]
      rw [ofReal_thetaCuspCenterMixedFourierCurrent,
        mul_div_cancel_left₀ _ hpi]
      congr 2
      push_cast
      ring
    rw [hH, ← schwartz_iteratedDeriv_zero_eq_fourierMoment,
      abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)),
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
      Complex.ofReal_ofNat] at hscale
    have hpiC : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast hpi
    rw [hscale, ← mul_assoc, mul_inv_cancel₀ hpiC, one_mul]
  rw [mul_pow, mul_assoc, ← hphase, hscaled, hjet]
  ring

/-- The real signed derivative sequence selected by Fourier duality. Odd orders carry zero
real Fourier phase; even orders alternate sign. -/
def thetaCuspCenterMixedSignedJet (a : ℝ) (n : ℕ) : ℝ :=
  ((-I) ^ n).re * iteratedDeriv n (thetaCuspCenterMixedDensity a) 0

/-- Even source jets carry the alternating Fourier sign. -/
theorem thetaCuspCenterMixedSignedJet_even (a : ℝ) (n : ℕ) :
    thetaCuspCenterMixedSignedJet a (2 * n) =
      (-1 : ℝ) ^ n * iteratedDeriv (2 * n) (thetaCuspCenterMixedDensity a) 0 := by
  have hI : (-I : ℂ) ^ 2 = ((-1 : ℝ) : ℂ) := by norm_num
  simp only [thetaCuspCenterMixedSignedJet, pow_mul, hI, ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- Odd source jets carry zero real Fourier phase. -/
theorem thetaCuspCenterMixedSignedJet_odd (a : ℝ) (n : ℕ) :
    thetaCuspCenterMixedSignedJet a (2 * n + 1) = 0 := by
  have hI : (-I : ℂ) ^ 2 = ((-1 : ℝ) : ℂ) := by norm_num
  simp only [thetaCuspCenterMixedSignedJet, pow_add, pow_mul, hI, pow_one,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.I_re, neg_zero, mul_zero, zero_mul, sub_zero]

/-- Raw moments and signed source jets differ only by their explicit positive scale. -/
theorem thetaCuspCenterMixed_rawMoment_eq_signedJet
    (a : ℝ) (ha : |a| < 1) (n : ℕ) :
    weightedMoment volume (thetaCuspCenterMixedFourierCurrent a ha) n =
      (2 * Real.pi) * (1 / 2 : ℝ) ^ n * thetaCuspCenterMixedSignedJet a n := by
  have h := thetaCuspCenterMixed_rawMoment_jet_identity a ha n
  have hinv : ((-I / 2) : ℂ) * (2 * I) = 1 := by
    calc (-I / 2) * (2 * I) = -(I * I) := by ring
      _ = 1 := by rw [I_mul_I]; norm_num
  have hm := congrArg (fun z : ℂ => (-I / 2) ^ n * z) h
  rw [← mul_assoc, ← mul_pow, hinv, one_pow, one_mul] at hm
  have hp : (-I / 2 : ℂ) ^ n = (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * (-I) ^ n := by
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  rw [hp] at hm
  have hre := congrArg Complex.re hm
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    show (2 : ℂ).re = 2 from rfl, show (2 : ℂ).im = 0 from rfl, zero_mul, mul_zero, add_zero, sub_zero] at hre
  simpa only [thetaCuspCenterMixedSignedJet, mul_assoc, mul_left_comm, mul_comm] using hre

/-- A positive mass factor and an invertible geometric change of scale preserve the complete
Hankel cone exactly. -/
theorem completeHankelCone_positive_geometric_iff (s : ℕ → ℝ)
    {C r : ℝ} (hC : 0 < C) (hr : r ≠ 0) :
    CompleteHankelCone (fun n => C * r ^ n * s n) ↔ CompleteHankelCone s := by
  have forward (q : ℕ → ℝ) (c t : ℝ) (hc : 0 ≤ c)
      (hq : CompleteHankelCone q) : CompleteHankelCone (fun n => c * t ^ n * q n) := by
    intro N v
    have h := mul_nonneg hc (hq N (fun i => t ^ (i : ℕ) * v i))
    convert h using 1 <;> try rfl
    simp_rw [Finset.mul_sum, pow_add]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  constructor
  · intro h
    have hh := forward (fun n => C * r ^ n * s n) C⁻¹ r⁻¹ (inv_pos.mpr hC).le h
    have heq : (fun n => C⁻¹ * (r⁻¹) ^ n * (C * r ^ n * s n)) = s := by
      funext n
      rw [inv_pow]
      field_simp [hC.ne', hr]
    rw [heq] at hh
    exact hh
  · exact forward s C r hC.le

/-- At each aperture the complete signed source jet is exactly the global Fourier sign. -/
theorem thetaCuspCenterMixedSignedJetCone_at_iff_pointwise (a : ℝ) (ha : |a| < 1) :
    CompleteHankelCone (thetaCuspCenterMixedSignedJet a) ↔
      ∀ b : ℝ, 0 ≤ thetaCuspCenterMixedFourierCurrent a ha b := by
  rw [← hedenmalmRawHankelCone_at_iff_pointwise]
  have heq : weightedMoment volume (thetaCuspCenterMixedFourierCurrent a ha) =
      fun n => (2 * Real.pi) * (1 / 2 : ℝ) ^ n * thetaCuspCenterMixedSignedJet a n :=
    funext (thetaCuspCenterMixed_rawMoment_eq_signedJet a ha)
  rw [heq, completeHankelCone_positive_geometric_iff _ (by positivity) (by norm_num)]

/-- Positivity at every order of the actual signed center-mixed derivative hierarchy. -/
def ThetaCuspCenterMixedSignedJetCone : Prop :=
  ∀ a : ℝ, 0 < a → a < 1/2 → CompleteHankelCone (thetaCuspCenterMixedSignedJet a)

/-- **Source-jet completeness.** The full signed derivative hierarchy of the actual center-mixed
theta density at the single difference origin is equivalent to RH. All analytic continuation,
Fourier normalization, and moment-determinacy inputs are proved from the source. -/
theorem thetaCuspCenterMixedSignedJetCone_iff_riemannHypothesis :
    ThetaCuspCenterMixedSignedJetCone ↔ RiemannHypothesis := by
  rw [← hedenmalmRawHankelCone_iff_riemannHypothesis]
  constructor
  · intro h a ha ha0 hahalf
    apply (hedenmalmRawHankelCone_at_iff_pointwise a ha).mpr
    exact (thetaCuspCenterMixedSignedJetCone_at_iff_pointwise a ha).mp (h a ha0 hahalf)
  · intro h a ha0 hahalf
    have ha : |a| < 1 := by rw [abs_of_pos ha0]; linarith
    apply (thetaCuspCenterMixedSignedJetCone_at_iff_pointwise a ha).mpr
    exact (hedenmalmRawHankelCone_at_iff_pointwise a ha).mp (h a ha ha0 hahalf)


/-- The finite Hankel matrix of the signed physical derivative sequence. -/
def thetaCuspCenterMixedSignedHankel (a : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => thetaCuspCenterMixedSignedJet a (i.val + j.val)

/-- The already proved five-point source chamber supplies a strict rank-five section of the
complete RH-equivalent signed derivative hierarchy. -/
theorem thetaCuspCenterMixedSignedHankel_five_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a 5).PosDef := by
  let T := GaloisForLFunctions.HTGeometry.translationJetMatrix 5 (thetaCuspCenterMixedDensity a)
  have hT : T.PosDef := thetaCuspCenterMixed_translationJetMatrix_five_posDef ha0 ha
  let S : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal
    (fun i => (i.val.factorial : ℝ) * (-1) ^ (i.val / 2))
  have hS : Function.Injective S.mulVec := by
    intro v w hvw
    funext i
    have hi := congrFun hvw i
    simp only [S, Matrix.mulVec_diagonal] at hi
    exact (mul_left_cancel₀
      (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val)
        (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)))) hi
  have hodd (n : ℕ) (hn : Odd n) : iteratedDeriv n (thetaCuspCenterMixedDensity a) 0 = 0 :=
    iteratedDeriv_zero_of_even_real_of_odd (thetaCuspCenterMixedDensity_even a) hn
  have h1 := hodd 1 (by norm_num)
  have h3 := hodd 3 (by norm_num)
  have h5 := hodd 5 (by norm_num)
  have h7 := hodd 7 (by norm_num)
  have hi6 : I ^ 6 = (-1 : ℂ) := by
    rw [show 6 = 2 * 3 by norm_num, pow_mul]
    norm_num
  have hi8 : I ^ 8 = (1 : ℂ) := by
    rw [show 8 = 2 * 4 by norm_num, pow_mul]
    norm_num
  have heq : thetaCuspCenterMixedSignedHankel a 5 = S.conjTranspose * T * S := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [thetaCuspCenterMixedSignedHankel, thetaCuspCenterMixedSignedJet,
        T, S, GaloisForLFunctions.HTGeometry.translationJetMatrix, Matrix.diagonal,
        Matrix.mul_apply, Fin.sum_univ_succ, h1, h3, h5, h7, Complex.mul_re,
        Complex.mul_im, Complex.I_mul_I, hi6, hi8] <;> ring
  rw [heq]
  exact hT.conjTranspose_mul_mul_same hS

end
end RHTower
