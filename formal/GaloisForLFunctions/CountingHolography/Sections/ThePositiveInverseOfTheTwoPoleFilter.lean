import GaloisForLFunctions.CountingHolography.Sections.ThreeSquareConductorsWithZeroPoleDegree

/-!
# A positive inverse for the two-pole filter

The atom at conductors 1, 4 and 16 acts on the spline correlation by four
first-order differences. Each inverse preserves a constant lower bound.
One log-four orbit above each prime therefore suffices for the filtered trace.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology SquareRootThreshold ArithmeticOrientationGeometry
open Zeta23 RenormalizedIntersectionTheory SurfaceOfSpecZ ArithmeticScatteringHolography

private def step {ι : Type*} (s : ι → ι) (f : ι → ℝ) (i : ι) := 2*f i-f (s i)

private def controlled {ι : Type*} (X f : ι → ℝ) := ∃ C : ℝ, 0 ≤ C ∧ ∀ i, |f i| ≤ C*X i

private theorem step_controlled {ι : Type*} {X f : ι → ℝ} {s : ι → ι} {r : ℝ}
    (hr : 0 ≤ r) (hs : ∀ i, X (s i) ≤ r*X i) (hf : controlled X f) :
    controlled X (step s f) := by
  obtain ⟨C,hC,h⟩ := hf
  refine ⟨(2+r)*C,mul_nonneg (by linarith only [hr]) hC,fun i => ?_⟩
  have hshift := (h (s i)).trans (mul_le_mul_of_nonneg_left (hs i) hC)
  have htri := abs_sub (2*f i) (f (s i))
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)] at htri
  unfold step
  linarith only [htri,h i,hshift]

/-- Iterate the deficit from a lower bound. Its weighted envelope contracts
by r/2 at each step. -/
private theorem lower_of_step {ι : Type*} {X f : ι → ℝ} {s : ι → ι} {r A : ℝ}
    (hr : 0 ≤ r) (hr' : r < 2) (hX : ∀ i, 1 ≤ X i)
    (hs : ∀ i, X (s i) ≤ r*X i) (hf : controlled X f)
    (h : ∀ i, A ≤ step s f i) : ∀ i, A ≤ f i := by
  obtain ⟨C,hC,hC'⟩ := hf
  let B := |A|+C
  have hB : 0 ≤ B := add_nonneg (abs_nonneg _) hC
  have hr0 : 0 ≤ r/2 := half_nonneg hr
  have hiter (k : ℕ) : ∀ i, A-f i ≤ B*(r/2)^k*X i := by
    induction k with
    | zero =>
      intro i
      rw [pow_zero,mul_one]
      have hA := le_mul_of_one_le_right (abs_nonneg A) (hX i)
      unfold B
      linarith only [le_abs_self A,neg_le_abs (f i),hC' i,hA]
    | succ k ih =>
      intro i
      have ht := (ih (s i)).trans
        (mul_le_mul_of_nonneg_left (hs i) (mul_nonneg hB (pow_nonneg hr0 k)))
      have hd := h i
      unfold step at hd
      rw [pow_succ]
      linarith only [hd,ht]
  intro i
  have hlim := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 (by linarith only [hr'])).const_mul B).mul_const (X i)
  have hz : A-f i ≤ 0 := by
    apply ge_of_tendsto' (by simpa only [mul_zero,zero_mul] using hlim)
    exact fun k => hiter k i
  linarith only [hz]

private theorem trace_growth {w : ℝ} (hw : 0 ≤ w) (hz : zetaZeroWidth ≤ w) :
    controlled (fun x : ℝ => Real.exp (w*|x|)) realSplineTrace := by
  obtain ⟨C,hC⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hw).mpr hz
  refine ⟨|C|,abs_nonneg _,fun t => ?_⟩
  have h := hC |t| (abs_nonneg _)
  have ht : zetaScalingDatum.orbitCorr splineCycle |t| = realSplineTrace t := by
    rcases le_total 0 t with hh | hh
    · simp only [abs_of_nonneg hh,orbitCorr_splineCycle_eq,realSplineTrace]
    · simp only [abs_of_nonpos hh,zetaScalingDatum.orbitCorr_neg,orbitCorr_splineCycle_eq,realSplineTrace]
  rw [ht] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)

/-- The five correlation lags in the self-pairing of the two-pole-free atom. -/
def twoPoleTrace (t : ℝ) : ℝ :=
  let h := Real.log 4
  33*realSplineTrace t-20*(realSplineTrace (t+h)+realSplineTrace (t-h))+
    4*(realSplineTrace (t+2*h)+realSplineTrace (t-2*h))

/-- A lower bound on one full log-four orbit passes unchanged to the
unfiltered trace at its center. -/
theorem twoPoleTrace_lower_on_orbit {t A : ℝ}
    (h : ∀ j : ℤ, A ≤ twoPoleTrace (t+j*Real.log 4)) : A ≤ realSplineTrace t := by
  let d := Real.log 4
  let w : ℝ := 3/8
  let r := Real.exp (w*d)
  let u := fun j : ℤ => t+(j:ℝ)*d
  let X := fun j : ℤ => Real.exp (w*|u j|)
  let f := fun j : ℤ => realSplineTrace (u j)
  let p := fun j : ℤ => j+1
  let m := fun j : ℤ => j-1
  have hd : 0 < d := Real.log_pos (by norm_num)
  have hw : 0 ≤ w := by norm_num [w]
  have hr := (Real.exp_pos (w*d)).le
  have hr' : r < 2 := by
    have he : Real.log 4 = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
    calc r = Real.exp (w*(2*Real.log 2)) := by dsimp only [r,d]; rw [he]
      _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr (by
          dsimp only [w]
          linarith only [Real.log_pos (by norm_num : (1:ℝ) < 2)])
      _ = 2 := Real.exp_log (by norm_num)
  have hX (j : ℤ) : 1 ≤ X j := Real.one_le_exp (mul_nonneg hw (abs_nonneg _))
  have hp (j : ℤ) : u (p j) = u j+d := by dsimp only [u,p]; push_cast; ring
  have hm (j : ℤ) : u (m j) = u j-d := by dsimp only [u,m]; push_cast; ring
  have hg {x y : ℝ} (hxy : |y| ≤ |x|+d) : Real.exp (w*|y|) ≤ r*Real.exp (w*|x|) := by
    unfold r
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_left hxy hw])
  have hp' (j : ℤ) : X (p j) ≤ r*X j := hg (by rw [hp]; simpa only [abs_of_pos hd] using abs_add_le (u j) d)
  have hm' (j : ℤ) : X (m j) ≤ r*X j := hg (by rw [hm]; simpa only [abs_of_pos hd] using abs_sub (u j) d)
  obtain ⟨C,hC,hf⟩ := trace_growth hw (ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths.trans (by norm_num [w]))
  have h₀ : controlled X f := ⟨C,hC,fun i => hf (u i)⟩
  have h₁ := step_controlled hr hm' h₀
  have h₂ := step_controlled hr hp' h₁
  have h₃ := step_controlled hr hm' h₂
  have h₄ (j : ℤ) : A ≤ step p (step m (step p (step m f))) j := by
    convert h j using 1
    simp only [twoPoleTrace,step,f,u,p,m,d,Int.cast_add,Int.cast_sub,Int.cast_one]
    ring_nf
  have hlo := lower_of_step hr hr' hX hm' h₀
    (lower_of_step hr hr' hX hp' h₁ (lower_of_step hr hr' hX hm' h₂ (lower_of_step hr hr' hX hp' h₃ h₄))) 0
  simpa only [f,u,Int.cast_zero,zero_mul,add_zero] using hlo

/-- Only prime-centered log-four orbits of the two-pole-free trace are
needed in the one-sided test. -/
theorem riemannHypothesis_iff_twoPoleTrace_prime_orbits :
    RiemannHypothesis ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime → ∀ j : ℤ,
      A ≤ twoPoleTrace (Real.log p+j*Real.log 4) := by
  constructor
  · intro hRH
    obtain ⟨C,hC,h⟩ := trace_growth (w := 0) le_rfl (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH).le
    simp only [zero_mul,Real.exp_zero,mul_one] at h
    refine ⟨-81*C,fun p _ j => ?_⟩
    let t := Real.log p+j*Real.log 4
    let d := Real.log 4
    change -81*C ≤ 33*realSplineTrace t-20*(realSplineTrace (t+d)+realSplineTrace (t-d))+
      4*(realSplineTrace (t+2*d)+realSplineTrace (t-2*d))
    linarith only [(abs_le.mp (h t)).1,(abs_le.mp (h (t+d))).2,(abs_le.mp (h (t-d))).2,
      (abs_le.mp (h (t+2*d))).1,(abs_le.mp (h (t-2*d))).1]
  · rintro ⟨A,h⟩
    apply riemannHypothesis_iff_bddBelow_primeDegrees'.mpr
    refine ⟨-A,fun p hp => ?_⟩
    rw [neg_neg,orbitCorr_splineCycle_eq]
    exact twoPoleTrace_lower_on_orbit (h p hp)

end GaloisForLFunctions.CountingHolography.Sections
