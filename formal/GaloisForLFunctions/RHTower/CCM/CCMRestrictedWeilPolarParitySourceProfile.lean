import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarSourceNonvanishing

/-!
# The actual even and odd boundary–arithmetic source profiles

Both reflected source channels share one singular Gamma boundary term. Their
remaining arithmetic and boundary-asymmetry terms have an explicit finite
aperture bound, retaining every prime power. At the right endpoint the common
singular coefficient is positive in both parity sectors. Thus both source
profiles diverge there; no parity can cancel this source singularity.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology ENNReal
noncomputable section
namespace RHTower

/-- The two literal arithmetic errors entering the completed pole source. -/
def ccmPolarBoundaryArithmeticError (a : SuzukiPositiveAperture) (x : ℝ) : ℝ :=
  (Chebyshev.psi (Real.exp (a.1-x))-Real.exp (a.1-x))+ccmReciprocalMangoldtError (a.1+x)

/-- The arithmetic residual is bounded on every finite aperture, retaining all prime powers. -/
theorem abs_ccmPolarBoundaryArithmeticError_le (a : SuzukiPositiveAperture) {x : ℝ}
    (hx : x ∈ Ioo (-a.1) a.1) :
    |ccmPolarBoundaryArithmeticError a x| ≤
      Chebyshev.psi (Real.exp (2*a.1))+Real.exp (2*a.1)+(Real.log 4+5) := by
  have he : Real.exp (a.1-x)≤Real.exp (2*a.1) := Real.exp_le_exp.mpr (by linarith [hx.1])
  have hp := Chebyshev.psi_mono he
  have hm := abs_ccmReciprocalMangoldtError_le (show 0≤a.1+x by linarith [hx.1])
  unfold ccmPolarBoundaryArithmeticError
  calc
    _ ≤ |Chebyshev.psi (Real.exp (a.1-x))-Real.exp (a.1-x)|+|ccmReciprocalMangoldtError (a.1+x)| := abs_add_le _ _
    _ ≤ _ := by
      have h : |Chebyshev.psi (Real.exp (a.1-x))-Real.exp (a.1-x)| ≤
          Chebyshev.psi (Real.exp (a.1-x))+Real.exp (a.1-x) := by
        rw [abs_le]
        constructor <;> linarith [Chebyshev.psi_nonneg (Real.exp (a.1-x)), Real.exp_pos (a.1-x)]
      linarith

/-- The full boundary–arithmetic source profile in a reflection channel. -/
def ccmPolarParityBoundaryProfile (a : SuzukiPositiveAperture) (r x : ℝ) : ℂ :=
  ccmPolarBoundaryArithmeticProfile a x+(r:ℂ)*ccmPolarBoundaryArithmeticProfile a (-x)

/-- The exact finite remainder after collecting the common parity boundary singularity. -/
def ccmPolarParityArithmeticRemainder (a : SuzukiPositiveAperture) (r x : ℝ) : ℝ :=
  Real.exp (x/2)*ccmPolarBoundaryArithmeticError a x+
    r*Real.exp (-x/2)*(ccmPolarBoundaryArithmeticError a (-x)+
      (ccmGammaPolarBoundary (a.1-x) (a.1+x)-ccmGammaPolarBoundary (a.1+x) (a.1-x)))

/-- Exact channel decomposition into one common singular boundary and a finite arithmetic remainder. -/
theorem ccmPolarParityBoundaryProfile_re_decomposition (a : SuzukiPositiveAperture) (r x : ℝ) :
    (ccmPolarParityBoundaryProfile a r x).re =
      (Real.exp (x/2)+r*Real.exp (-x/2))*ccmGammaPolarBoundary (a.1-x) (a.1+x)-
        ccmPolarParityArithmeticRemainder a r x := by
  simp only [ccmPolarParityBoundaryProfile,ccmPolarBoundaryArithmeticProfile,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    sub_neg_eq_add,← sub_eq_add_neg,neg_div]
  unfold ccmPolarParityArithmeticRemainder ccmPolarBoundaryArithmeticError
  ring

/-- Uniform control of the complete arithmetic and boundary-asymmetry remainder at fixed aperture. -/
theorem abs_ccmPolarParityArithmeticRemainder_le (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) {x : ℝ} (hx : x ∈ Ioo (-a.1) a.1) :
    |ccmPolarParityArithmeticRemainder a r x| ≤ Real.exp (a.1/2)*
      (2*(Chebyshev.psi (Real.exp (2*a.1))+Real.exp (2*a.1)+(Real.log 4+5))+Real.log 2) := by
  let C := Chebyshev.psi (Real.exp (2*a.1))+Real.exp (2*a.1)+(Real.log 4+5)
  have hnx : -x ∈ Ioo (-a.1) a.1 := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hp := abs_ccmPolarBoundaryArithmeticError_le a hx
  have hm := abs_ccmPolarBoundaryArithmeticError_le a hnx
  have hB := (abs_ccmGammaPolarBoundary_sub_swap_lt
    (show 0<a.1-x by linarith [hx.2]) (show 0<a.1+x by linarith [hx.1])).le
  have hE : Real.exp (x/2)≤Real.exp (a.1/2) := Real.exp_le_exp.mpr (by linarith [hx.2])
  have hF : Real.exp (-x/2)≤Real.exp (a.1/2) := Real.exp_le_exp.mpr (by linarith [hx.1])
  have hc : 0≤C := (abs_nonneg _).trans hp
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hrabs : |r|=1 := by rcases hr with rfl | rfl <;> norm_num
  have hsum := abs_add_le (ccmPolarBoundaryArithmeticError a (-x))
    (ccmGammaPolarBoundary (a.1-x) (a.1+x)-ccmGammaPolarBoundary (a.1+x) (a.1-x))
  unfold ccmPolarParityArithmeticRemainder
  calc
    _ ≤ |Real.exp (x/2)*ccmPolarBoundaryArithmeticError a x|+
      |r*Real.exp (-x/2)*(ccmPolarBoundaryArithmeticError a (-x)+
        (ccmGammaPolarBoundary (a.1-x) (a.1+x)-ccmGammaPolarBoundary (a.1+x) (a.1-x)))| := abs_add_le _ _
    _ = Real.exp (x/2)*|ccmPolarBoundaryArithmeticError a x|+
      Real.exp (-x/2)*|ccmPolarBoundaryArithmeticError a (-x)+
        (ccmGammaPolarBoundary (a.1-x) (a.1+x)-ccmGammaPolarBoundary (a.1+x) (a.1-x))| := by
      rw [abs_mul,abs_mul,abs_mul,hrabs,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _),one_mul]
    _ ≤ Real.exp (a.1/2)*C+Real.exp (a.1/2)*(C+Real.log 2) := by
      apply add_le_add
      · exact mul_le_mul hE hp (abs_nonneg _) (Real.exp_pos _).le
      · exact mul_le_mul hF (hsum.trans (add_le_add hm hB)) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := by dsimp [C]; ring

/-- The common singular coefficient is positive at the right endpoint in both parity channels. -/
theorem polarParityEndpointCoefficient_pos (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) : 0<Real.exp (a.1/2)+r*Real.exp (-a.1/2) := by
  rcases hr with rfl | rfl
  · positivity
  · have h := Real.exp_lt_exp.mpr (show -a.1/2<a.1/2 by linarith [a.property])
    linarith

/-- Each actual parity source profile diverges at the right endpoint; neither parity cancels the source. -/
theorem tendsto_ccmPolarParityBoundaryProfile_re_right (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) :
    Tendsto (fun x : ℝ => (ccmPolarParityBoundaryProfile a r x).re) (𝓝[<] a.1) atTop := by
  let M := Real.exp (a.1/2)*
    (2*(Chebyshev.psi (Real.exp (2*a.1))+Real.exp (2*a.1)+(Real.log 4+5))+Real.log 2)
  have hc : Tendsto (fun x : ℝ => Real.exp (x/2)+r*Real.exp (-x/2)) (𝓝[<] a.1)
      (𝓝 (Real.exp (a.1/2)+r*Real.exp (-a.1/2))) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (x/2)+r*Real.exp (-x/2))).tendsto a.1 |>.mono_left nhdsWithin_le_nhds
  have h := Filter.Tendsto.pos_mul_atTop (polarParityEndpointCoefficient_pos a hr) hc
    (tendsto_ccmGammaPolarBoundary_right a)
  have hl := tendsto_atTop_add_const_right _ (-M) h
  apply tendsto_atTop_mono' _ _ hl
  filter_upwards [Ioo_mem_nhdsLT (show -a.1<a.1 by linarith [a.property])] with x hx
  rw [ccmPolarParityBoundaryProfile_re_decomposition]
  have hb := (abs_le.mp (abs_ccmPolarParityArithmeticRemainder_le a hr hx)).2
  dsimp [M]
  linarith
end RHTower
