import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicGaussConnectionCoefficient

/-! Independent Laplace-frequency chamber for the physical BM radial equation. -/

open Complex Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

def gaussA (w chi : ℂ) : ℂ := 1/4+w/2+Complex.I*chi/2
def gaussB (w chi : ℂ) : ℂ := 1/4+w/2-Complex.I*chi/2
def gaussC (w : ℂ) : ℂ := 1+w

/-- An explicit open time-transform chamber, with angular momentum held fixed. -/
def Chamber (w chi : ℂ) : Prop := |chi.im| < w.re

theorem chamber_re_pos {w chi : ℂ} (h : Chamber w chi) : 0 < w.re :=
  lt_of_le_of_lt (abs_nonneg _) h

/-- The Gauss parameters belong to the original physical operator at omega=i*w. -/
theorem gaussParameters_physical (w chi : ℂ) :
    gaussA w chi = d4BMCausalHypergeometricA (Complex.I*w) chi ∧
    gaussB w chi = d4BMCausalHypergeometricB (Complex.I*w) chi ∧
    gaussC w = d4BMCausalRadialC (Complex.I*w) := by
  simp only [gaussA,gaussB,gaussC,d4BMCausalHypergeometricA,d4BMCausalHypergeometricB,
    d4BMCausalRadialA,d4BMCausalRadialB,d4BMCausalRadialC]
  constructor
  · ring_nf; simp only [Complex.I_sq]; ring
  constructor <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem gauss_gap (w chi : ℂ) : gaussC w-gaussA w chi-gaussB w chi=1/2 := by
  unfold gaussC gaussA gaussB
  ring

/-- All five Gauss and connection arguments have positive real part in the
independent frequency chamber, even for complex angular momentum. -/
theorem chamber_parameters {w chi : ℂ} (h : Chamber w chi) :
    0 < (gaussA w chi).re ∧ 0 < (gaussB w chi).re ∧ 0 < (gaussC w).re ∧
    0 < (gaussC w-gaussA w chi).re ∧ 0 < (gaussC w-gaussB w chi).re := by
  have hp := chamber_re_pos h
  have hm := neg_abs_le chi.im
  have hl := le_abs_self chi.im
  dsimp [Chamber] at h
  simp only [gaussA,gaussB,gaussC,Complex.add_re,Complex.sub_re]
  norm_num [Complex.div_re,Complex.mul_re]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> linarith

theorem avoidsNegNat_of_re_pos {z : ℂ} (hz : 0 < z.re) (n : ℕ) : (n:ℂ) ≠ -z := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.natCast_re,Complex.neg_re] at hr
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

def horizonSeries (w chi : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ (gaussA w chi) (gaussB w chi) (gaussC w)

def outerSeries (w chi : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ (gaussC w-gaussA w chi) (gaussC w-gaussB w chi) (3/2)

theorem horizonSeries_radius {w chi : ℂ} (h : Chamber w chi) :
    (horizonSeries w chi).radius=1 := by
  obtain ⟨ha,hb,hc,-⟩ := chamber_parameters h
  exact ordinaryHypergeometricSeries_radius_eq_one ℂ _ _ _
    (fun n => ⟨avoidsNegNat_of_re_pos ha n,avoidsNegNat_of_re_pos hb n,avoidsNegNat_of_re_pos hc n⟩)

theorem outerSeries_radius {w chi : ℂ} (h : Chamber w chi) :
    (outerSeries w chi).radius=1 := by
  obtain ⟨-,-,-,ha,hb⟩ := chamber_parameters h
  exact ordinaryHypergeometricSeries_radius_eq_one ℂ _ _ _
    (fun n => ⟨avoidsNegNat_of_re_pos ha n,avoidsNegNat_of_re_pos hb n,
      avoidsNegNat_of_re_pos (by norm_num : 0 < (3/2:ℂ).re) n⟩)

/-- The boundary coefficient of the horizon solution, with its full normalization. -/
def connection (w chi : ℂ) : ℂ :=
  Complex.Gamma (gaussC w)*Complex.Gamma (1/2:ℂ)/
    (Complex.Gamma (gaussC w-gaussA w chi)*Complex.Gamma (gaussC w-gaussB w chi))

theorem connection_ne_zero {w chi : ℂ} (h : Chamber w chi) : connection w chi ≠ 0 := by
  obtain ⟨-,-,hc,ha,hb⟩ := chamber_parameters h
  exact div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hc)
    (Complex.Gamma_ne_zero_of_re_pos (by norm_num)))
    (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos ha) (Complex.Gamma_ne_zero_of_re_pos hb))

end
end RHTower.D4BMLaplaceRadial
