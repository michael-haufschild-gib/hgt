import GaloisForLFunctions.SquareRootThreshold.SechStripKernel
import GaloisForLFunctions.RHTower.ZetaLogDerivSelbergExplicitFormulaHeight
import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination

/-!
# Vanishing horizontal edges for the sech contour

Separated heights in successive unit intervals make the residue-unit
logarithmic derivative polylogarithmic. The strip kernel's exponential decay
then removes both horizontal edges of an exhausting rectangle.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open _root_.RHTower GaloisForLFunctions.HTGeometry

private theorem tendsto_height_index :
    Tendsto (fun n : ℕ => (n : ℝ)+12) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  obtain ⟨N,hN⟩ := exists_nat_ge B
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith only [hN,hcast]

private theorem tendsto_polynomial_exp_height {c : ℝ} (hc : 0 < c) (M : ℝ)
    (hM : 0 ≤ M) :
    Tendsto (fun n : ℕ => M*((n : ℝ)+12)^2*Real.exp (-(c*((n : ℝ)+12))))
      atTop (𝓝 0) := by
  have hc2 : 0 < c/2 := by positivity
  have harg : Tendsto (fun n : ℕ => -(c/2*((n : ℝ)+12))) atTop atBot := by
    apply tendsto_atBot.2
    intro B
    filter_upwards [tendsto_height_index.eventually (eventually_ge_atTop (-B/(c/2)))] with n hn
    have hh := (div_le_iff₀ hc2).mp hn
    linarith only [hh]
  have hexp := Real.tendsto_exp_atBot.comp harg
  have hbound (n : ℕ) :
      M*((n : ℝ)+12)^2*Real.exp (-(c*((n : ℝ)+12))) ≤
        (M*(2/(c/2)^2))*Real.exp (-(c/2*((n : ℝ)+12))) := by
    have hp := pow_mul_exp_neg_le hc2 2 (show 0 ≤ (n : ℝ)+12 by positivity)
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat] at hp
    have he : Real.exp (-(c*((n : ℝ)+12))) =
        Real.exp (-(c/2*((n : ℝ)+12))) * Real.exp (-(c/2*((n : ℝ)+12))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    calc
      _ = M*(((n : ℝ)+12)^2*Real.exp (-(c/2*((n : ℝ)+12)))) *
          Real.exp (-(c/2*((n : ℝ)+12))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hM)
        (Real.exp_pos _).le
  simpa only [mul_zero] using squeeze_zero (fun n => by positivity) hbound
    (hexp.const_mul (M*(2/(c/2)^2)))

private theorem sech_horizontal_tendsto_zero {a b K : ℝ} (hb : 0 < b)
    (hba : b < a) (hK : 0 ≤ K) (T : ℝ) (Y : ℕ → ℝ)
    (hY : ∀ n : ℕ, (n : ℝ)+12-1/2 ≤ |Y n|)
    (hlog : ∀ (n : ℕ) (x : ℝ), x ∈ Icc (1/2-b) (1/2+b) →
      ‖logDeriv zetaResidueUnit ((x : ℂ)+(Y n : ℂ)*I)‖ ≤
        K*(1+Real.log ((n : ℝ)+12))^2) :
    Tendsto (fun n : ℕ => ∫ x in (1/2-b)..(1/2+b),
      sechStripWeight a T ((x : ℂ)+(Y n : ℂ)*I) *
        logDeriv zetaResidueUnit ((x : ℂ)+(Y n : ℂ)*I)) atTop (𝓝 0) := by
  let c := Real.pi/(2*a)
  let D := |2/Real.cos (c*b)|
  let M := 4*D*K*(2*b)*Real.exp (c*(1/2+|T|))
  have hc : 0 < c := by dsimp [c]; have ha := hb.trans hba; positivity
  have hD : 0 ≤ D := abs_nonneg _
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hn (n : ℕ) :
      ‖∫ x in (1/2-b)..(1/2+b), sechStripWeight a T ((x : ℂ)+(Y n : ℂ)*I) *
        logDeriv zetaResidueUnit ((x : ℂ)+(Y n : ℂ)*I)‖ ≤
          M*((n : ℝ)+12)^2*Real.exp (-(c*((n : ℝ)+12))) := by
    let X : ℝ := (n : ℝ)+12
    have hX1 : 1 ≤ X := by
      dsimp [X]
      linarith only [Nat.cast_nonneg (α := ℝ) n]
    have hlog0 : 0 ≤ 1+Real.log X := by
      have hh := Real.log_nonneg hX1
      linarith only [hh]
    have hlog2 : (1+Real.log X)^2 ≤ 4*X^2 := by
      have hh := Real.log_le_self (zero_le_one.trans hX1)
      have hs := mul_self_le_mul_self hlog0 (show 1+Real.log X ≤ 2*X by linarith only [hh,hX1])
      nlinarith only [hs]
    have hdist : X-(1/2+|T|) ≤ |Y n-T| := by
      have hh := abs_add_le (Y n-T) T
      rw [sub_add_cancel] at hh
      have hy := hY n
      change X-1/2 ≤ |Y n| at hy
      linarith only [hh,hy]
    have hexp : Real.exp (-(c*|Y n-T|)) ≤
        Real.exp (c*(1/2+|T|))*Real.exp (-(c*X)) := by
      calc
        _ ≤ Real.exp (-(c*(X-(1/2+|T|)))) := Real.exp_le_exp.mpr
          (neg_le_neg (mul_le_mul_of_nonneg_left hdist hc.le))
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hp (x : ℝ) (hx : x ∈ Icc (1/2-b) (1/2+b)) :
        ‖sechStripWeight a T ((x : ℂ)+(Y n : ℂ)*I) *
          logDeriv zetaResidueUnit ((x : ℂ)+(Y n : ℂ)*I)‖ ≤
            D*(Real.exp (c*(1/2+|T|))*Real.exp (-(c*X)))*(K*(4*X^2)) := by
      have hs : |(((x : ℂ)+(Y n : ℂ)*I)).re-1/2| ≤ b := by
        simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
          Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
        exact abs_le.mpr ⟨by linarith only [hx.1],by linarith only [hx.2]⟩
      have hk := norm_sechStripWeight_le_exp hb.le hba (T := T) hs
      simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hk
      have hk' : ‖sechStripWeight a T ((x : ℂ)+(Y n : ℂ)*I)‖ ≤
          D*(Real.exp (c*(1/2+|T|))*Real.exp (-(c*X))) := by
        exact (hk.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)).trans
          (mul_le_mul_of_nonneg_left hexp hD)
      rw [norm_mul]
      exact mul_le_mul hk' ((hlog n x hx).trans (mul_le_mul_of_nonneg_left hlog2 hK))
        (norm_nonneg _) (by positivity)
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x (hx : x ∈ uIoc (1/2-b) (1/2+b)) => hp x (by
        rw [uIoc_of_le (by linarith only [hb])] at hx
        exact ⟨hx.1.le,hx.2⟩))
    have hlen : |(1/2+b)-(1/2-b)| = 2*b := by
      rw [show (1/2+b)-(1/2-b)=2*b by ring,abs_of_pos (by positivity)]
    rw [hlen] at hi
    convert hi using 1 <;> dsimp only [M,X] <;> ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun n => norm_nonneg _) hn
    (tendsto_polynomial_exp_height hc M hM)

/-- Actual zero-free lower and upper edges exhaust the strip while both weighted
horizontal integrals tend to zero. -/
theorem exists_sech_horizontal_exhaustion {a b : ℝ} (hb : 0 < b)
    (hbhalf : b < 1/2) (hba : b < a) (T : ℝ) :
    ∃ lo hi : ℕ → ℝ, Tendsto lo atTop atBot ∧ Tendsto hi atTop atTop ∧
      (∀ n, lo n < hi n) ∧
      (∀ (n : ℕ) (x : ℝ), x ∈ Icc (1/2-b) (1/2+b) →
        zetaResidueUnit ((x : ℂ)+(lo n : ℂ)*I) ≠ 0 ∧
        zetaResidueUnit ((x : ℂ)+(hi n : ℂ)*I) ≠ 0) ∧
      Tendsto (fun n => ∫ x in (1/2-b)..(1/2+b),
        sechStripWeight a T ((x : ℂ)+(lo n : ℂ)*I) *
          logDeriv zetaResidueUnit ((x : ℂ)+(lo n : ℂ)*I)) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in (1/2-b)..(1/2+b),
        sechStripWeight a T ((x : ℂ)+(hi n : ℂ)*I) *
          logDeriv zetaResidueUnit ((x : ℂ)+(hi n : ℂ)*I)) atTop (𝓝 0) := by
  classical
  obtain ⟨K,hK,hhor⟩ := exists_horizontal_height_polylog
  have hXn (n : ℕ) : 0 ≤ (n : ℝ)+12 := by positivity
  have hpos (n : ℕ) := hhor (X := n+12) (τ := (n : ℝ)+12)
    (by omega)
    (by simp only [Nat.cast_add,Nat.cast_ofNat,abs_of_nonneg (hXn n)]; linarith only [hXn n])
    (by simp only [Nat.cast_add,Nat.cast_ofNat,abs_of_nonneg (hXn n)]; linarith only [hXn n])
  have hneg (n : ℕ) := hhor (X := n+12) (τ := -((n : ℝ)+12))
    (by omega)
    (by simp only [Nat.cast_add,Nat.cast_ofNat,abs_neg,abs_of_nonneg (hXn n)]; linarith only [hXn n])
    (by simp only [Nat.cast_add,Nat.cast_ofNat,abs_neg,abs_of_nonneg (hXn n)]; linarith only [hXn n])
  choose hi hhi hhiB using hpos
  choose lo hlo hloB using hneg
  have hlolim : Tendsto lo atTop atBot := by
    apply tendsto_atBot.2
    intro B
    filter_upwards [tendsto_height_index.eventually (eventually_ge_atTop (1/2-B))] with n hn
    have hh := (hlo n).2
    linarith only [hh,hn]
  have hhilim : Tendsto hi atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [tendsto_height_index.eventually (eventually_ge_atTop (B+1/2))] with n hn
    have hh := (hhi n).1
    linarith only [hh,hn]
  have hx (x : ℝ) (hh : x ∈ Icc (1/2-b) (1/2+b)) : x ∈ Icc (-1/2 : ℝ) 2 :=
    ⟨by linarith only [hh.1,hbhalf],by linarith only [hh.2,hbhalf]⟩
  refine ⟨lo,hi,hlolim,hhilim,?_,?_,?_,?_⟩
  · intro n
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith only [(hlo n).2,(hhi n).1,hn]
  · intro n x hh
    exact ⟨(hloB n x (hx x hh)).1,(hhiB n x (hx x hh)).1⟩
  · apply sech_horizontal_tendsto_zero hb hba hK T lo
    · intro n
      have hh := (hlo n).2
      linarith only [hh,neg_le_abs (lo n)]
    · intro n x hh
      simpa only [Nat.cast_add,Nat.cast_ofNat] using (hloB n x (hx x hh)).2
  · apply sech_horizontal_tendsto_zero hb hba hK T hi
    · intro n
      have hh := (hhi n).1
      linarith only [hh,le_abs_self (hi n)]
    · intro n x hh
      simpa only [Nat.cast_add,Nat.cast_ofNat] using (hhiB n x (hx x hh)).2

end GaloisForLFunctions.SquareRootThreshold

#print axioms GaloisForLFunctions.SquareRootThreshold.exists_sech_horizontal_exhaustion
