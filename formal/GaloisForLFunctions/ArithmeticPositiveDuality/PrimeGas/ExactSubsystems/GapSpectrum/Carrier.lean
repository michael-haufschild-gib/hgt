import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.VisibilityThreshold.Profile
import GaloisForLFunctions.HTGeometry.ExponentialSeriesFiberwise
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleWeights

/-! # The spectrum of the squared optimal overlap -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open CopyExchange

/-- The observed Fourier coefficient of the squared lower endpoint of finite-factor overlaps. -/
def overlapCoefficient (x ω : ℝ) : ℂ :=
  bohrCoefficient (fun t => (finiteOverlapFloor x t : ℂ)^2) ω

/-- Oppositely evolving heat waves double every energy difference. -/
def gapFrequency (q : ℕ+ × ℕ+) : ℝ := 2*(energy q.1-energy q.2)

/-- Weight of an ordered pair of states in two independent Gibbs samples. -/
def gapAmplitude (x : ℝ) (q : ℕ+ × ℕ+) : ℂ :=
  heat ((x+x:ℝ):ℂ) (q.1*q.2) / (‖riemannZeta ((x+x:ℝ):ℂ)‖ : ℂ)^2

theorem gapAmplitude_summable {x : ℝ} (hx : 1/2 < x) :
    Summable (fun q => ‖gapAmplitude x q‖) := by
  let s : ℂ := ((x+x:ℝ):ℂ)
  have hsum := (heat_abs_summable s).mpr (by change 1 < x+x; linarith)
  have hp := (summable_norm_mul hsum hsum).div_const ‖(‖riemannZeta s‖:ℂ)^2‖
  simpa only [gapAmplitude,heat_mul,norm_div,s] using hp

private theorem split_heat (x t : ℝ) (n : ℕ+) :
    heat (thermalPoint (x+x) (t+t)) n = heat ((x+x:ℝ):ℂ) n * expChar (-(2*energy n)) t := by
  rw [thermalPoint,heat_add]
  congr 1
  unfold heat expChar
  congr 1
  push_cast
  ring

/-- Multiplication of the two Gibbs series exhibits the measured squared overlap as an absolutely convergent Fourier series. -/
theorem squared_floor_eq_carrier {x : ℝ} (hx : 1/2 < x) (t : ℝ) :
    (finiteOverlapFloor x t : ℂ)^2 = expSeriesCarrier (gapAmplitude x) gapFrequency t := by
  let s : ℂ := ((x+x:ℝ):ℂ)
  let w := thermalPoint (x+x) (t+t)
  let B := heat s
  have hs : 1 < s.re := by change 1 < x+x; linarith
  have hw : 1 < w.re := by rw [show w.re = x+x from thermalPoint_re _ _]; change 1 < x+x at hs; exact hs
  have hB := (heat_abs_summable s).mpr hs
  have hz : ∑' n, heat w n = riemannZeta w := (heat_hasSum ⟨w,hw⟩).tsum_eq
  have hminus : riemannZeta w = expSeriesCarrier B (fun n => -(2*energy n)) t := by
    rw [← hz]
    exact tsum_congr (split_heat x t)
  have hplus : (starRingEnd ℂ) (riemannZeta w) = expSeriesCarrier B (fun n => 2*energy n) t := by
    rw [← hz,Complex.conj_tsum]
    apply tsum_congr
    intro n
    change (starRingEnd ℂ) (heat (thermalPoint (x+x) (t+t)) n) = _
    rw [split_heat,map_mul]
    change _ = heat ((x+x:ℝ):ℂ) n * expChar (2*energy n) t
    congr 1
    · simp [heat,← Complex.exp_conj]
    · have htwo : (starRingEnd ℂ) (2:ℂ) = 2 := by
        rw [show (2:ℂ) = 1+1 by norm_num,map_add,map_one]
      simp [expChar,← Complex.exp_conj,htwo]
  have hprod : (‖riemannZeta w‖:ℂ)^2 =
      expSeriesCarrier (fun q : ℕ+ × ℕ+ => B q.1*B q.2) gapFrequency t := by
    calc
      _ = (starRingEnd ℂ) (riemannZeta w)*riemannZeta w := (Complex.conj_mul' _).symm
      _ = expSeriesCarrier (fun q : ℕ+ × ℕ+ => B q.1*B q.2)
          (fun q => 2*energy q.1 + -(2*energy q.2)) t := by
        rw [hplus,hminus,expSeriesCarrier_mul _ _ hB hB]
      _ = _ := by
        have hf : (fun q : ℕ+ × ℕ+ => 2*energy q.1 + -(2*energy q.2)) = gapFrequency := by
          funext q
          unfold gapFrequency
          ring
        rw [hf]
  rw [finiteOverlapFloor_above hx,partitionVisibility,thermalPoint_re,Complex.ofReal_div,div_pow]
  change (‖riemannZeta w‖:ℂ)^2 / (‖riemannZeta s‖:ℂ)^2 = _
  rw [hprod,expSeriesCarrier,expSeriesCarrier,← tsum_div_const]
  apply tsum_congr
  intro q
  simp only [gapAmplitude,heat_mul,B,s]
  ring

/-- Each measured line sums the Gibbs probabilities of all pairs sharing its energy difference. -/
theorem overlapCoefficient_fiber {x : ℝ} (hx : 1/2 < x) (ω : ℝ) :
    overlapCoefficient x ω = fiberAmplitude (gapAmplitude x) gapFrequency ω := by
  unfold overlapCoefficient
  rw [funext (squared_floor_eq_carrier hx)]
  exact bohrCoefficient_expSeriesCarrier_fiber _ _ (gapAmplitude_summable hx) _

#print axioms gapAmplitude_summable
#print axioms squared_floor_eq_carrier
#print axioms overlapCoefficient_fiber

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
