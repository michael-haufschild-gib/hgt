import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.LogarithmicallyWeightedZeroSamples
import GaloisForLFunctions.HTGeometry.FiniteExponentialHankel

/-!
# Synthesis of unheated zero modes

Pair the half-ray exponential with its exponentially damped reflection. The
sum of the two Gram kernels is a product of resolvents. Its quadratic decay
makes each row summable with the known logarithmic bound for the zero mass.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Reflection about the midpoint of a vertical strip cancels the first-order
tail of the Cauchy Gram kernel. -/
private theorem norm_paired_resolvent_le {u v : ℂ} {e R : ℝ} (he : 0 < e)
    (hu : e ≤ u.re) (hv : e ≤ v.re) (hu' : e ≤ R-u.re) (hv' : e ≤ R-v.re) :
    ‖1/(u+star v) + 1/(((R:ℂ)-u)+star ((R:ℂ)-v))‖ ≤
      (2*R*(e^2)⁻¹ + 2*R) / (1+(u.im-v.im)^2) := by
  let A := u + star v
  let B := ((R:ℂ)-u) + star ((R:ℂ)-v)
  have ha : A.re = u.re+v.re := by simp [A]
  have hb : B.re = R-u.re+(R-v.re) := by simp [B]
  have hai : A.im = u.im-v.im := by simp [A, sub_eq_add_neg]
  have hbi : B.im = -(u.im-v.im) := by simp [B]; ring
  have hA : e ≤ ‖A‖ := by linarith only [Complex.re_le_norm A,ha,hu,hv,he]
  have hB : e ≤ ‖B‖ := by linarith only [Complex.re_le_norm B,hb,hu',hv',he]
  have hnA : A ≠ 0 := norm_pos_iff.mp (he.trans_le hA)
  have hnB : B ≠ 0 := norm_pos_iff.mp (he.trans_le hB)
  have hAB : 1/A + 1/B = (2*(R:ℂ))/(A*B) := by
    have hsum : A+B = 2*(R:ℂ) := by simp [A,B]; ring
    rw [← hsum]; field_simp; ring
  have h0 : 0 ≤ 2*R := by linarith only [hu,hu',he]
  have h1 : e^2 ≤ ‖A‖*‖B‖ := by simpa [sq] using mul_le_mul hA hB he.le (norm_nonneg _)
  have h2 : (u.im-v.im)^2 ≤ ‖A‖*‖B‖ := by
    have h := Complex.abs_im_le_norm A
    have k := Complex.abs_im_le_norm B
    rw [hai] at h
    rw [hbi, abs_neg] at k
    simpa only [← sq, sq_abs] using mul_le_mul h k (abs_nonneg _) (norm_nonneg _)
  have h3 : 1 ≤ (e^2)⁻¹*(‖A‖*‖B‖) := (one_le_inv_mul₀ (sq_pos_of_pos he)).mpr h1
  change ‖1/A + 1/B‖ ≤ _
  have hnum : ‖2*(R:ℂ)‖ = 2*R := by
    rw [show 2*(R:ℂ) = ((2*R:ℝ):ℂ) by norm_cast,Complex.norm_real, Real.norm_of_nonneg h0]
  rw [hAB, norm_div, hnum, norm_mul,
    div_le_div_iff₀ (mul_pos (he.trans_le hA) (he.trans_le hB)) (by positivity)]
  calc 2*R*(1+(u.im-v.im)^2) ≤ 2*R*((e^2)⁻¹*(‖A‖*‖B‖)+‖A‖*‖B‖) :=
          mul_le_mul_of_nonneg_left (add_le_add h3 h2) h0
    _ = _ := by ring

/-- The two orientations in a symmetric quadratic sum have the same row mass. -/
private theorem sum_pair_weights_le {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (k : ι → ι → ℝ) (hk : ∀ i j, 0 ≤ k i j) (hs : ∀ i j, k i j = k j i) :
    ∑ i ∈ S, ∑ j ∈ S, x i*x j*k i j ≤ ∑ i ∈ S, x i^2 * ∑ j ∈ S, k i j := by
  have hswap : (∑ i ∈ S, ∑ j ∈ S, x j^2*k i j) = ∑ i ∈ S, ∑ j ∈ S, x i^2*k i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hs j i]
  have h : (∑ i ∈ S, ∑ j ∈ S, x i*x j*k i j) ≤
      ∑ i ∈ S, ∑ j ∈ S, (x i^2*k i j + x j^2*k i j)/2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      nlinarith only [mul_nonneg (sq_nonneg (x i-x j)) (hk i j)]
  simp only [← Finset.sum_div, Finset.sum_add_distrib, hswap, ← Finset.mul_sum] at h
  linarith only [h]

private theorem inner_weighted_sum {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Finset ι) (c : ι → ℂ) (v : ι → H) :
    inner ℂ (∑ i ∈ S, c i • v i) (∑ i ∈ S, c i • v i) =
      ∑ i ∈ S, ∑ j ∈ S, (star (c i)*c j)*inner ℂ (v i) (v j) := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [inner_smul_left,inner_smul_right,mul_assoc]
  exact mul_left_comm _ _ _

/-- Adding a second squared norm permits a bound by the absolute values
of the combined Gram entries. -/
private theorem norm_sq_sum_le_paired_gram {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Finset ι) (c : ι → ℂ) (v v' : ι → H) :
    ‖∑ i ∈ S, c i • v i‖^2 ≤ ∑ i ∈ S, ∑ j ∈ S,
      (‖c i‖*‖c j‖)*‖inner ℂ (v i) (v j)+inner ℂ (v' i) (v' j)‖ := by
  let U := ∑ i ∈ S, c i • v i
  let V := ∑ i ∈ S, c i • v' i
  let G := fun i j => inner ℂ (v i) (v j)+inner ℂ (v' i) (v' j)
  have hg : inner ℂ U U + inner ℂ V V =
      ∑ i ∈ S, ∑ j ∈ S, (star (c i)*c j)*G i j := by
    rw [inner_weighted_sum S c v,inner_weighted_sum S c v']
    simp only [G,mul_add,Finset.sum_add_distrib]
  have hre (u : H) : (inner ℂ u u).re = ‖u‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  calc ‖U‖^2 ≤ ‖U‖^2 + ‖V‖^2 := le_add_of_nonneg_right (sq_nonneg _)
    _ = (inner ℂ U U + inner ℂ V V).re := by rw [Complex.add_re,hre,hre]
    _ ≤ ‖inner ℂ U U + inner ℂ V V‖ := Complex.re_le_norm _
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖(star (c i)*c j)*G i j‖ := by
      rw [hg]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = _ := by simp only [norm_mul,norm_star,G]

/-- A logarithmic row bound controls every finite exponential sum uniformly in
the selected zeros and in the choice of its coefficients. -/
private theorem norm_sq_sum_halfLineLaplaceFeature_le {ι : Type*} (q : ι ↪ XiZeroCopy)
    (w : ι → ℂ) {e R : ℝ} (he : 0 < e) (hR : 0 < R)
    (hw : ∀ i, e ≤ (w i).re) (hw' : ∀ i, e ≤ R-(w i).re)
    (him : ∀ i, (w i).im = (centredZero (q i)).im) (c : ι → ℂ) (S : Finset ι) :
    ‖∑ i ∈ S, c i • halfLineLaplaceFeature (w i) (he.trans_le (hw i))‖^2 ≤
      ((2*R*(e^2)⁻¹ + 2*R)*8) * ∑ i ∈ S,
        (xiLineTwoLogDerivConstant + Real.log (|(centredZero (q i)).im|+4)) * ‖c i‖^2 := by
  classical
  let v := fun i => halfLineLaplaceFeature (w i) (he.trans_le (hw i))
  have hr (i) : 0 < ((R:ℂ)-w i).re := by simpa using he.trans_le (hw' i)
  let v' := fun i => halfLineLaplaceFeature ((R:ℂ)-w i) (hr i)
  let D := 2*R*(e^2)⁻¹+2*R
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let k := fun i j => lorentzMassTerm (centredZero (q i)).im (q j)
  have hsym (i j) : k i j = k j i := by
    unfold k lorentzMassTerm
    simp only [im_centredZero]
    rw [show (((q i).1:ℂ).im-((q j).1:ℂ).im)^2 = (((q j).1:ℂ).im-((q i).1:ℂ).im)^2 by ring]
  have hrow (i) : ∑ j ∈ S, k i j ≤ 8*(xiLineTwoLogDerivConstant + Real.log (|(centredZero (q i)).im|+4)) := by
    have hh := (summable_lorentzMassTerm (centredZero (q i)).im).sum_le_tsum (S.map q)
      (fun j _ => lorentzMassTerm_nonneg _ j)
    have hle : (∑ j ∈ S, k i j) ≤ lorentzMass (centredZero (q i)).im := by
      unfold lorentzMass
      simpa only [Finset.sum_map,k] using hh
    exact hle.trans (lorentzMass_le_log _)
  have hkernel (i j) : ‖inner ℂ (v i) (v j) + inner ℂ (v' i) (v' j)‖ ≤ D*k i j := by
    simp only [v,v',inner_halfLineLaplaceFeature]
    simpa [D,k,lorentzMassTerm,him,im_centredZero,div_eq_mul_inv] using
      norm_paired_resolvent_le he (hw i) (hw j) (hw' i) (hw' j)
  let weight := fun i => xiLineTwoLogDerivConstant + Real.log (|(centredZero (q i)).im|+4)
  have hentry (i j) : (‖c i‖*‖c j‖)*‖inner ℂ (v i) (v j) + inner ℂ (v' i) (v' j)‖ ≤
      D*(‖c i‖*‖c j‖*k i j) := by
    exact (mul_le_mul_of_nonneg_left (hkernel i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq
      (by ring)
  have hrows : (∑ i ∈ S, ‖c i‖^2 * ∑ j ∈ S, k i j) ≤ 8 * ∑ i ∈ S, weight i * ‖c i‖^2 := by
    calc _ ≤ ∑ i ∈ S, 8 * (weight i * ‖c i‖^2) := Finset.sum_le_sum fun i _ =>
              (mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)).trans_eq (by dsimp only [weight]; ring)
      _ = _ := (Finset.mul_sum ..).symm
  calc ‖∑ i ∈ S, c i • v i‖^2 ≤ _ := norm_sq_sum_le_paired_gram S c v v'
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, D*(‖c i‖*‖c j‖*k i j) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = D * ∑ i ∈ S, ∑ j ∈ S, ‖c i‖*‖c j‖*k i j := by simp only [Finset.mul_sum]
    _ ≤ D * (8 * ∑ i ∈ S, weight i * ‖c i‖^2) :=
      mul_le_mul_of_nonneg_left ((sum_pair_weights_le S _ k
        (fun i j => lorentzMassTerm_nonneg _ _) hsym).trans hrows) hD
    _ = _ := (mul_assoc D 8 _).symm

/-- Weighted square summability gives unconditional Hilbert-space convergence
of exponentials indexed by any subset of the zeros in a fixed depth strip. -/
theorem summable_zero_exponentials_of_log_mass {ι : Type*} (q : ι ↪ XiZeroCopy)
    (w : ι → ℂ) {e R : ℝ} (he : 0 < e) (hR : 0 < R)
    (hw : ∀ i, e ≤ (w i).re) (hw' : ∀ i, e ≤ R-(w i).re)
    (him : ∀ i, (w i).im = (centredZero (q i)).im) (c : ι → ℂ)
    (hc : Summable fun i => (xiLineTwoLogDerivConstant + Real.log (|(centredZero (q i)).im|+4)) *
      ‖c i‖^2) :
    Summable fun i => c i • halfLineLaplaceFeature (w i) (he.trans_le (hw i)) := by
  rw [summable_iff_vanishing_norm] at hc ⊢
  intro ε hε
  let K := (2*R*(e^2)⁻¹+2*R)*8
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨S,hS⟩ := hc (ε^2/K) (by positivity)
  refine ⟨S, fun T hT => ?_⟩
  have hh := hS T hT
  rw [Real.norm_eq_abs] at hh
  have h := lt_of_le_of_lt (le_abs_self _) hh
  rw [lt_div_iff₀ hK] at h
  have h2 := norm_sq_sum_halfLineLaplaceFeature_le q w he hR hw hw' him c T
  change _ ≤ K*_ at h2
  rw [mul_comm] at h
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp (h2.trans_lt h)

/-- The positive-ray exponential `exp((z-s)t)` as an actual square-integrable datum. -/
def zeroRayFeature (s : ℝ) (q : XiZeroCopy) (hq : (centredZero q).re < s) :
    HalfLineLaplaceL2 :=
  halfLineLaplaceFeature ((s:ℂ)-star (centredZero q)) (by simpa using sub_pos.mpr hq)

/-- A separated damping line suffices for synthesis on any subset carrying
finite logarithmically weighted coefficient mass. -/
theorem summable_zeroRayFeature_of_log_mass {ι : Type*} (q : ι ↪ XiZeroCopy) (c : ι → ℂ)
    {b s : ℝ} (hbs : b < s) (hb : ∀ i, (centredZero (q i)).re ≤ b)
    (hc : Summable fun i => (xiLineTwoLogDerivConstant + Real.log (|(centredZero (q i)).im|+4)) *
      ‖c i‖^2) :
    Summable fun i => c i • zeroRayFeature s (q i) ((hb i).trans_lt hbs) := by
  let e := s-b
  let R := |s|+e+2
  have he : 0 < e := sub_pos.mpr hbs
  have hR : 0 < R := by dsimp [R]; positivity
  apply summable_zero_exponentials_of_log_mass q (fun i => (s:ℂ)-star (centredZero (q i)))
    he hR
  · intro i; simp only [Complex.sub_re,Complex.ofReal_re,Complex.star_def,Complex.conj_re]
    exact sub_le_sub_left (hb i) s
  · intro i
    have hh := (abs_lt.mp (abs_re_centredZero_lt (q i))).1
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.star_def,Complex.conj_re,R]
    linarith only [le_abs_self s, hh]
  · intro i; simp
  · exact hc

/-- The unheated zero series of a critical state converges in square mean
over every layer lying strictly to the left of the damping line. -/
theorem criticalState_summable_zeroRayFeature {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    {ι : Type*} (q : ι ↪ XiZeroCopy) {b s : ℝ} (hbs : b < s)
    (hb : ∀ i, (centredZero (q i)).re ≤ b) :
    Summable fun i => negativeHalfLineLaplace (cx F) (centredZero (q i)) •
      zeroRayFeature s (q i) ((hb i).trans_lt hbs) := by
  exact summable_zeroRayFeature_of_log_mass q _ hbs hb
    ((criticalState_summable_zero_density_mass hW ht hF).comp_injective q.injective)

#print axioms criticalState_summable_zeroRayFeature

end GaloisForLFunctions.ExclusionOfTheCriticalState
