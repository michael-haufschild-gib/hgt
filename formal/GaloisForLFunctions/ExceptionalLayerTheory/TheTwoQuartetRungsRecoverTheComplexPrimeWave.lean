import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.RHTower.ZetaFractLaplace

/-!
# The two confined rungs resolve the complex phase of the prime wave

The quartet contribution to the bare energy pairs two Laplace evaluations.
On a negative plane their real coordinate maps have determinants of the
same nonzero sign. In particular the two rung amplitudes at the right zero
provide independent real readings of the conjugate-pair oscillation.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExceptionalLayerTheory

open ExclusionOfTheCriticalState ArithmeticHodgeTheoryOfDegenerations
  ArithmeticCastelnuovoSeveri HTGeometry

private abbrev sample (F : ℝ → ℝ) (w : ℂ) := negativeHalfLineLaplace (cx F) w

/-- Signed area of a pair of complex amplitudes in real phase coordinates. -/
def phaseArea (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

private abbrev realPair (a b : ℂ) : ℝ := (a * conj b).re

private theorem area_product_pos {a b c d : ℂ}
    (h : ∀ s t : ℝ, (s,t) ≠ (0,0) →
      realPair ((s : ℂ)*a + (t : ℂ)*b) ((s : ℂ)*c + (t : ℂ)*d) < 0) :
    0 < phaseArea a b * phaseArea c d := by
  let u := realPair a c
  let v := realPair a d
  let w := realPair b c
  let z := realPair b d
  have hq : ∀ s t : ℝ, (s,t) ≠ (0,0) → s^2*u + 2*s*t*((v+w)/2) + t^2*z < 0 := by
    intro s t hst
    apply lt_of_eq_of_lt _ (h s t hst)
    simp only [u,v,w,z, realPair, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hdet := (binary_neg_iff.mp hq).2
  have hid : phaseArea a b * phaseArea c d =
      (u*z - ((v+w)/2)^2) + ((v-w)/2)^2 := by
    simp only [phaseArea, u,v,w,z, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hid]
  exact add_pos_of_pos_of_nonneg hdet (sq_nonneg _)

/-- The right and reflected Laplace samples of every negative plane have
the same orientation. Both pairs separately resolve the real phase plane. -/
theorem negativePlane_quartet_phase_orientation {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ)
    {R : ℝ} (hR : 0 < R) {F G : ℝ → ℝ} (hplane : IsNegativePlane R F G) :
    0 < phaseArea (sample F (ρ-1/2)) (sample G (ρ-1/2)) *
      phaseArea (sample F (1/2-conj ρ)) (sample G (1/2-conj ρ)) := by
  apply area_product_pos
  intro s t hst
  let H := fun u => s*F u + t*G u
  have hH : CriticalHalfLineEnergyDomain H := (hplane.1.const_mul s).add_const_mul hplane.2.1 t
  have hneg := hplane.2.2 s t hst
  change criticalHalfLineFullEnergy R H < 0 at hneg
  rw [← criticalHalfLineMixedEnergy_self R hH, criticalHalfLineMixedEnergy_eq_bare_add,
    bareMixedEnergy_self_singleQuartet hq hH] at hneg
  have hc : 0 ≤ criticalAliasCoefficient R * (∫ u in Iio 0, H u * H u * Real.exp (-(8*u))) :=
    mul_nonneg (criticalAliasCoefficient_positive hR).le
      (integral_nonneg fun u => mul_nonneg (mul_self_nonneg (H u)) (Real.exp_pos _).le)
  have hone := onLineEnergy_nonneg H
  have hmass : 0 < 4 * (quartetCopyMult ρ : ℝ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast hq.quartetCopyMult_pos)
  have hh : realPair (sample H (ρ-1/2)) (sample H (1/2-conj ρ)) < 0 := by
    by_contra! he
    have hprod := mul_nonneg hmass.le he
    change _ + 4 * (quartetCopyMult ρ : ℝ) *
      realPair (sample H (ρ-1/2)) (sample H (1/2-conj ρ)) + _ < 0 at hneg
    linarith only [hone,hprod,hc,hneg]
  have hsamp (w : ℂ) (hw : -4 < w.re) :
      sample H w = (s : ℂ)*sample F w + (t : ℂ)*sample G w := by
    dsimp only [sample,H]
    rw [laplace_cx_add (hplane.1.const_mul s) (hplane.2.1.const_mul t) hw,
      laplace_cx_const_mul, laplace_cx_const_mul]
  have hz : -4 < (ρ-1/2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith only [hq.1]
  have hz' : -4 < (1/2-conj ρ).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.conj_re]
    linarith only [hq.re_lt_one]
  rwa [hsamp _ hz, hsamp _ hz'] at hh

private theorem phase_readings_resolve {a b : ℂ} (hD : phaseArea a b ≠ 0) :
    ∃ u v : ℂ, ∀ z : ℂ, u * ((a*z).re : ℂ) + v * ((b*z).re : ℂ) = z := by
  let D := phaseArea a b
  refine ⟨(I*conj b) / D, -(I*conj a) / D, fun z => ?_⟩
  have hDC : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  field_simp [hDC]
  apply Complex.ext <;>
    simp only [D, phaseArea, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring

private theorem scaled_area (a b z : ℂ) (s t : ℝ) :
    phaseArea ((s : ℂ)*a*z) ((t : ℂ)*b*z) = s*t * Complex.normSq z * phaseArea a b := by
  simp only [phaseArea, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- On a single quartet the two actual confined rungs determine the full
complex wave whose real part gives the ordinary prime error. One pair of
complex weights works at every positive log scale. -/
theorem twoRung_recovers_complex_prime_wave {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    ∃ (R₀ R₁ : ℝ) (F G : ℝ → ℝ), 0 < R₀ ∧ R₀ < R₁ ∧
      IsConfinedNullVector R₀ F ∧ IsConfinedNullVector R₁ G ∧
      ∃ u v : ℂ, ∃ K : ℝ, ∀ t : ℝ, 0 < t →
        ‖u * (averagedState F t : ℂ) + v * (averagedState G t : ℂ) -
          Complex.exp ((ρ-1/2-8)*(t : ℂ)) / ρ‖ ≤ K * Real.exp (-(8*t)) := by
  obtain ⟨R₀,R₁,F,G,hR, hlt, _, _, hF,hG, _,_,_,_,_,_,_,hplane,_⟩ :=
    singleQuartet_complete_twoRung_ladder hq
  refine ⟨R₀,R₁,F,G,hR,hlt,hF,hG,?_⟩
  let z := ρ - 1/2
  let Z := averageSymbol (z-8)
  let c (R : ℝ) := -(criticalAliasCoefficient R)⁻¹
  let a := (c R₀ : ℂ)*sample F z*Z
  let b := (c R₁ : ℂ)*sample G z*Z
  let m := 2 * (quartetCopyMult ρ : ℝ)
  have hm : m ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hq.quartetCopyMult_pos)).ne'
  have hρ : ρ ≠ 0 := fun he => hq.im_ne_zero (by simp [he])
  obtain ⟨ha, K₀, h₀⟩ := singleQuartet_nullVector_averagedState_singleConjugatePair hq hR hF
  obtain ⟨_, K₁, h₁⟩ := singleQuartet_nullVector_averagedState_singleConjugatePair hq (hR.trans hlt) hG
  have ha' : a ≠ 0 := by simpa only [a,c,z,Z,sample, Complex.ofReal_neg, Complex.ofReal_inv] using ha
  have hZ : Complex.normSq Z ≠ 0 := (Complex.normSq_pos.mpr (right_ne_zero_of_mul ha')).ne'
  have hc (R : ℝ) (hp : 0 < R) : c R ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (criticalAliasCoefficient_positive hp).ne')
  have hO := negativePlane_quartet_phase_orientation hq
    (show 0 < R₁+1 by linarith only [hR,hlt]) (hplane _ (lt_add_one R₁))
  have hD : phaseArea a b ≠ 0 := by
    dsimp only [a,b]
    rw [scaled_area]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hc _ hR) (hc _ (hR.trans hlt))) hZ)
      (left_ne_zero_of_mul hO.ne')
  obtain ⟨u,v,huv⟩ := phase_readings_resolve hD
  let k := (m : ℂ)*ρ
  refine ⟨u/k,v/k, ‖u/k‖*K₀ + ‖v/k‖*K₁, fun t ht => ?_⟩
  let w := Complex.exp ((z-8)*(t : ℂ))
  have hw : u/k * ((m*(a*w).re : ℝ) : ℂ) + v/k * ((m*(b*w).re : ℝ) : ℂ) = w/ρ := by
    push_cast
    calc
      _ = (u * ((a*w).re : ℂ) + v * ((b*w).re : ℂ)) * (m : ℂ) / k := by ring
      _ = w/ρ := by rw [huv]; dsimp only [k]; field_simp [Complex.ofReal_ne_zero.mpr hm, hρ]
  have he (x : ℝ) (h : ℝ) : ‖((x-h : ℝ) : ℂ)‖ = |x-h| := Complex.norm_real _
  have hF' : |averagedState F t - m*(a*w).re| ≤ K₀*Real.exp (-(8*t)) := by
    simpa only [a,c,m,z,Z,w,sample, Complex.ofReal_neg, Complex.ofReal_inv] using h₀ t ht
  have hG' : |averagedState G t - m*(b*w).re| ≤ K₁*Real.exp (-(8*t)) := by
    simpa only [b,c,m,z,Z,w,sample, Complex.ofReal_neg, Complex.ofReal_inv] using h₁ t ht
  change ‖_ + _ - w/ρ‖ ≤ _
  rw [← hw]
  calc
    _ = ‖u/k * ((averagedState F t - m*(a*w).re : ℝ) : ℂ) +
          v/k * ((averagedState G t - m*(b*w).re : ℝ) : ℂ)‖ := by
      congr 1
      push_cast
      ring
    _ ≤ _ := (norm_add_le _ _).trans (by
      simp only [norm_mul, he, add_mul, mul_assoc]
      exact add_le_add (mul_le_mul_of_nonneg_left hF' (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hG' (norm_nonneg _)))

#print axioms negativePlane_quartet_phase_orientation
#print axioms twoRung_recovers_complex_prime_wave

/-- In prime coordinates, the same pair of rung weights gives both the
complex power and the actual Chebyshev error. The phase error is of
square-root order even where the real part of the power vanishes. -/
theorem twoRung_complex_wave_and_chebyshev {ρ : ℂ} (hq : HasSingleOffLineQuartet ρ) :
    ∃ (R₀ R₁ : ℝ) (F G : ℝ → ℝ), 0 < R₀ ∧ R₀ < R₁ ∧
      IsConfinedNullVector R₀ F ∧ IsConfinedNullVector R₁ G ∧
      ∃ u v : ℂ, ∃ K L : ℝ, ∀ t : ℝ, 0 < t → 16 ≤ Real.exp t →
        let x := Real.exp t
        let H := (Real.exp (17/2*t) : ℂ) *
          (u * (averagedState F t : ℂ) + v * (averagedState G t : ℂ))
        ‖H - (x : ℂ)^ρ/ρ‖ ≤ K * Real.sqrt x ∧
          |Chebyshev.psi x - x + 2*(quartetCopyMult ρ : ℝ)*H.re| ≤
            Real.sqrt x * (2*(quartetCopyMult ρ : ℝ)*K + L*t^2) := by
  obtain ⟨R₀,R₁,F,G,hR,hlt,hF,hG,u,v,K,h⟩ := twoRung_recovers_complex_prime_wave hq
  obtain ⟨L,hψ⟩ := (hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave hq.1
    ⟨hq.2.1.1,by linarith only [hq.1],hq.re_lt_one⟩).mp hq
  refine ⟨R₀,R₁,F,G,hR,hlt,hF,hG,u,v,K,L,fun t ht hx => ?_⟩
  let x := Real.exp t
  let E := Real.exp (17/2*t)
  let H := (E : ℂ)*(u * (averagedState F t : ℂ) + v * (averagedState G t : ℂ))
  let Z := (x : ℂ)^ρ/ρ
  let m := 2*(quartetCopyMult ρ : ℝ)
  change ‖H-Z‖ ≤ K*Real.sqrt x ∧ |Chebyshev.psi x - x + m*H.re| ≤ Real.sqrt x * (m*K + L*t^2)
  have hz : (E : ℂ) * (Complex.exp ((ρ-1/2-8)*(t : ℂ))/ρ) = Z := by
    dsimp only [Z,x,E]
    rw [RHTower.cpow_ofReal_exp, ← mul_div_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hs : E * Real.exp (-(8*t)) = Real.sqrt x := by
    change Real.exp (17/2*t) * Real.exp (-(8*t)) = Real.sqrt (Real.exp t)
    rw [← Real.exp_half, ← Real.exp_add]
    congr 1
    ring
  have hnorm : ‖H-Z‖ ≤ K*Real.sqrt x := by
    dsimp only [H]
    rw [← hz, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ E * (K * Real.exp (-(8*t))) := mul_le_mul_of_nonneg_left (h t ht) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, hs]
  refine ⟨hnorm,?_⟩
  have hreal : |H.re-Z.re| ≤ K*Real.sqrt x := (Complex.abs_re_le_norm (H-Z)).trans hnorm
  have hprime := hψ x hx
  change |Chebyshev.psi x - x + m * Z.re| ≤ L*Real.sqrt x*(Real.log x)^2 at hprime
  rw [show Real.log x = t from Real.log_exp t] at hprime
  have hm : 0 ≤ m := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  calc
    _ = |(Chebyshev.psi x - x + m*Z.re) + m*(H.re-Z.re)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (by
      rw [abs_mul, abs_of_nonneg hm]
      calc
        _ ≤ L*Real.sqrt x*t^2 + m*(K*Real.sqrt x) := add_le_add hprime (mul_le_mul_of_nonneg_left hreal hm)
        _ = _ := by ring)

#print axioms twoRung_complex_wave_and_chebyshev

end GaloisForLFunctions.ExceptionalLayerTheory
