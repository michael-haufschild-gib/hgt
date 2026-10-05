import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareAxis
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareMellin
import GaloisForLFunctions.RHTower.RectangleConfluentTwoPoleResidue
import GaloisForLFunctions.RHTower.AnalyticDividedDifference

/-!
# Actual BAG divisor-square moving rectangle

The literal normalized source has two poles at `1` and `1-2ε`.
Two successive removable divided differences construct its holomorphic
remainder. The actual polynomial zero-free disks contain the full moving
rectangle, so the four-edge integral equals both explicit residues.
No analytic-remainder or zero-free-region premise is assumed.

Infinite right tails and the joint damping-height limit remain separate work.
-/

noncomputable section
open Complex Set Filter
open scoped Topology
namespace RHTower.BAGTrace

private def squareSourceDomain (ε : ℂ) : Set ℂ :=
  {s | 7/8 < (s+ε).re ∧ |ε.re| < 1/16 ∧ zetaResidueFactor (s+ε) ≠ 0}

private theorem analyticOnNhd_squareSource (ε : ℂ) :
    AnalyticOnNhd ℂ (fun s => dampedSquareRegularSource (s+ε) (-ε))
      (squareSourceDomain ε) := by
  intro s hs
  have hg : Differentiable ℂ (fun z : ℂ => ![z+ε,-ε]) := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i
    · exact differentiable_id.add_const ε
    · exact differentiable_const _
  have ha := analyticOnNhd_regularAxisSource ![s+ε,-ε]
    (show ![s+ε,-ε] ∈ axisCoordinateTube from ⟨hs.1,by simpa using hs.2.1⟩)
  have hnum : AnalyticAt ℂ (fun z => regularAxisSource (z+ε) (-ε)) s :=
    ha.comp (f := fun z : ℂ => ![z+ε,-ε]) (hg.analyticAt s)
  have hden : AnalyticAt ℂ (fun z => zetaResidueFactor (z+ε)^2) s :=
    ((differentiable_zetaResidueFactor.analyticAt _).comp
      (analyticAt_id.add analyticAt_const)).pow 2
  exact hnum.div hden (pow_ne_zero 2 hs.2.2)

/-- Actual Mellin numerator retaining the complete arithmetic cofactor. -/
def dampedSquareMellinNumerator (ε : ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  dampedSquareRegularSource (s+ε) (-ε) * dampedSquareWindowMellin s * (X : ℂ)^s

/-- The actual normalized source; subtracting one removes the n=1 coefficient. -/
def dampedSquareContourIntegrand (ε : ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  (dampedSquareContinuation ε s-1)/ε^2 * dampedSquareWindowMellin s * (X : ℂ)^s

private theorem two_pole_dslope (g : ℂ → ℂ) {p q s : ℂ}
    (hpq : p ≠ q) (hsp : s ≠ p) (hsq : s ≠ q) :
    g s/((s-p)*(s-q)) =
      g p/(p-q)*(s-p)⁻¹ +
        (g q/(q-p)*(s-q)⁻¹ + dslope (dslope g p) q s) := by
  rw [dslope_of_ne _ hsq, slope_def_field, dslope_of_ne _ hsp,
    dslope_of_ne _ hpq.symm, slope_def_field, slope_def_field]
  field_simp [sub_ne_zero.mpr hpq, sub_ne_zero.mpr hpq.symm,
    sub_ne_zero.mpr hsp, sub_ne_zero.mpr hsq]
  ring

private theorem square_contour_split {ε : ℂ} (hε : ε ≠ 0) (X : ℝ) (s : ℂ) :
    dampedSquareContourIntegrand ε X s =
      (dampedSquareRegularSource (s+ε) (-ε)-1)/ε^2 *
        dampedSquareWindowMellin s * (X : ℂ)^s +
      dampedSquareMellinNumerator ε X s / ((s-1)*(s-(1-2*ε))) := by
  unfold dampedSquareContourIntegrand dampedSquareContinuation dampedSquareMellinNumerator
  rw [show s-(1-2*ε) = s+2*ε-1 by ring]
  have hc : ε^2*(ε^2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hε)
  simp only [div_eq_mul_inv]
  calc _ = ((dampedSquareRegularSource (s+ε) (-ε)-1)*(ε^2)⁻¹ +
      dampedSquareRegularSource (s+ε) (-ε)*((s-1)*(s+2*ε-1))⁻¹ *
        (ε^2*(ε^2)⁻¹)) * dampedSquareWindowMellin s * (X : ℂ)^s := by ring
    _ = _ := by rw [hc]; ring

private theorem actual_square_remainder {ε : ℂ} (hε : ε ≠ 0)
    {X : ℝ} (hX : 0 < X)
    (hp : (1 : ℂ) ∈ squareSourceDomain ε)
    (hq : 1-2*ε ∈ squareSourceDomain ε) :
    ∃ R : ℂ → ℂ, AnalyticOnNhd ℂ R (squareSourceDomain ε) ∧
      ∀ s, s ≠ 1 → s ≠ 1-2*ε →
        dampedSquareContourIntegrand ε X s =
          (0 : ℂ)*(s-(1-2*ε))⁻¹^2 +
          (dampedSquareMellinNumerator ε X 1/(2*ε)*(s-1)⁻¹ +
            (dampedSquareMellinNumerator ε X (1-2*ε)/(-2*ε)*(s-(1-2*ε))⁻¹+R s)) := by
  let g := dampedSquareMellinNumerator ε X
  let A : ℂ → ℂ := fun s => (dampedSquareRegularSource (s+ε) (-ε)-1)/ε^2 *
    dampedSquareWindowMellin s * (X : ℂ)^s
  let R : ℂ → ℂ := fun s => A s + dslope (dslope g 1) (1-2*ε) s
  have hx0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hpow : Differentiable ℂ (fun s : ℂ => (X : ℂ)^s) :=
    differentiable_id.const_cpow (.inl hx0)
  have hg : AnalyticOnNhd ℂ g (squareSourceDomain ε) := by
    intro s hs
    exact ((analyticOnNhd_squareSource ε s hs).mul
      (differentiable_dampedSquareWindowMellin.analyticAt s)).mul (hpow.analyticAt s)
  have hA : AnalyticOnNhd ℂ A (squareSourceDomain ε) := by
    intro s hs
    exact ((((analyticOnNhd_squareSource ε s hs).sub analyticAt_const).div
      analyticAt_const (pow_ne_zero 2 hε)).mul
      (differentiable_dampedSquareWindowMellin.analyticAt s)).mul (hpow.analyticAt s)
  have hd : AnalyticOnNhd ℂ (dslope g 1) (squareSourceDomain ε) :=
    fun s hs => analyticAt_dslope_of_analyticAt (hg 1 hp) (hg s hs)
  refine ⟨R,fun s hs => (hA s hs).add
    (analyticAt_dslope_of_analyticAt (hd _ hq) (hd s hs)),?_⟩
  intro s hs1 hs2
  have hpq : (1 : ℂ) ≠ 1-2*ε := by
    intro he
    apply hε
    linear_combination he / 2
  rw [square_contour_split hε, two_pole_dslope g hpq hs1 hs2]
  dsimp only [R, A, g]
  rw [show (1 : ℂ)-(1-2*ε)=2*ε by ring,
    show (1-2*ε)-(1 : ℂ)= -2*ε by ring]
  ring

private theorem exists_square_rectangle_domain :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ {T δ ε b : ℝ},
      0 < T → 0 < δ → δ ≤ d/(1+T)^9 → 0 < ε → ε < δ/4 →
      0 < b → b ≤ δ → ∀ s : ℂ,
        s.re ∈ Icc (1-δ) (1+b) → s.im ∈ Icc (-T) T →
          s ∈ squareSourceDomain ε := by
  obtain ⟨c,hc,M,hM,hF⟩ := exists_residue_global_polynomial_disks
  let d := min (c/8) (1/128)
  have hc0 : 0 ≤ c := hc.1.le
  have hd0 : 0 < d := lt_min (div_pos hc.1 (by norm_num)) (by norm_num)
  have hdc : d ≤ c/8 := min_le_left _ _
  have hd1 : d ≤ 1/128 := min_le_right _ _
  refine ⟨d,⟨hd0,hd1⟩,?_⟩
  intro T δ ε b hT hδ hδd hε hεδ hb hbδ s hs ht
  have hTp : 1 ≤ (1+T)^9 := one_le_pow₀ (by linarith)
  have hTpos : 0 < (1+T)^9 := by positivity
  have hδsmall : δ ≤ d := hδd.trans ((div_le_iff₀ hTpos).mpr (by nlinarith))
  have hab : |s.im| ≤ T := abs_le.mpr ht
  have hσ : 7/8 < (s+(ε : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hs.1]
  have hεsmall : |(ε : ℂ).re| < 1/16 := by
    rw [Complex.ofReal_re,abs_of_pos hε]
    linarith
  refine ⟨hσ,hεsmall,?_⟩
  apply (hF 1 ⟨le_rfl,by norm_num⟩ s.im (s+ε) ?_).1
  rw [Metric.mem_closedBall,dist_eq_norm]
  have he : s+(ε : ℂ)-((1 : ℝ)+s.im*I) = ((s.re+ε-1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  calc |s.re+ε-1| ≤ 2*δ := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    _ ≤ 2*(d/(1+T)^9) := by gcongr
    _ ≤ c/(1+T)^9 := by rw [← mul_div_assoc]; gcongr; linarith
    _ ≤ c/(1+|s.im|)^9 := by gcongr

/-- Exact four-edge identity for the actual square source, with both moving poles.
The zero-free neighborhood and holomorphic remainder are constructed from the source. -/
theorem exists_dampedSquareContour_rectangle :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ {T δ ε b X : ℝ},
      0 < T → 0 < δ → δ ≤ d/(1+T)^9 → 0 < ε → ε < δ/4 →
      0 < b → b ≤ δ → 0 < X →
      rectIntegral (dampedSquareContourIntegrand ε X)
        ((1-δ : ℝ)-T*I) ((1+b : ℝ)+T*I) =
      2*Real.pi*I*(dampedSquareMellinNumerator ε X 1/(2*ε) +
        dampedSquareMellinNumerator ε X (1-2*ε)/(-2*ε)) := by
  obtain ⟨d,hd,hdom⟩ := exists_square_rectangle_domain
  refine ⟨d,hd,?_⟩
  intro T δ ε b X hT hδ hδd hε hεδ hb hbδ hX
  have hrect := hdom hT hδ hδd hε hεδ hb hbδ
  have hp : (1 : ℂ) ∈ squareSourceDomain ε :=
    hrect 1 (by constructor <;> simp <;> linarith) (by constructor <;> simp <;> linarith)
  have hq : 1-2*(ε : ℂ) ∈ squareSourceDomain ε := by
    apply hrect
    · constructor <;> simp <;> linarith
    · constructor <;> simp <;> linarith
  obtain ⟨R,hR,hdecomp⟩ := actual_square_remainder
    (Complex.ofReal_ne_zero.mpr hε.ne') hX hp hq
  apply rectIntegral_eq_confluent_two_pole_residues_of_analyticOnNhd
    (R := R) (U := squareSourceDomain ε) (p := 1) (q := 1-2*ε) (dq := 0)
  all_goals try (simp; linarith)
  · intro s hs
    apply hrect
    · have hr := (Complex.mem_reProdIm.mp hs).1
      simpa only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
        uIcc_of_le (show 1-δ ≤ 1+b by linarith)] using hr
    · have hi := (Complex.mem_reProdIm.mp hs).2
      simpa only [Complex.sub_im,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,
        zero_sub,uIcc_of_le (show -T ≤ T by linarith)] using hi
  · exact hR
  · exact hdecomp

end RHTower.BAGTrace
