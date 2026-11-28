import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Selection
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement.Observables
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement.Scaling

/-! # The critical line from entanglement of the physical divisor outputs -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement

open Filter Real Collisions
open scoped Topology

def linearReading (s : ℕ → ℂ) (z : ℕ → SplitParameter) (N : ℕ) :=
  scale N*linearEntropy (s N) N (z N)

def entropyReading (s : ℕ → ℂ) (z : ℕ → SplitParameter) (N : ℕ) :=
  scale N*spectralEntropy (s N) N (z N)/log (scale N)

private theorem finite_rates (s : ℕ → ℂ) (z : ℕ → SplitParameter) {v : ℝ}
    (h : Tendsto (fun N => scale N*vacuumWeight (s N) N (z N)) atTop (𝓝 v)) :
    Tendsto (linearReading s z) atTop (𝓝 (2*v)) ∧ Tendsto (entropyReading s z) atTop (𝓝 v) := by
  have box (N : ℕ) : 0≤vacuumWeight (s N) N (z N) ∧ vacuumWeight (s N) N (z N)≤1 :=
    ⟨(vacuum_pos _ _ _).le,(vacuum_le_half _ _ _).trans (by norm_num)⟩
  unfold linearReading entropyReading
  simpa only [linear_eq,spectral_eq] using
    And.intro (linear_scale h) (entropy_scale box h)

theorem below_line (s : ℂ) (z : ℕ → SplitParameter) (hs : s.re<1/2) :
    Tendsto (linearReading (fun _ => s) z) atTop (𝓝 0) ∧
    Tendsto (entropyReading (fun _ => s) z) atTop (𝓝 0) := by
  have h := finite_rates (fun _ => s) z (v:=0)
    (Vacuum.diluted 0 s (fun N _ => z N) (by linarith only [hs]))
  simpa only [mul_zero] using h

/-- The two entropies have different critical scales and coefficients.
Both the preparation and the split may have independently moving clock times. -/
theorem on_line (s z : ℕ → SplitParameter) :
    Tendsto (linearReading (fun N => (s N).val) z) atTop (𝓝 (2*_root_.RHTower.primeZeta 2)) ∧
    Tendsto (entropyReading (fun N => (s N).val) z) atTop (𝓝 (_root_.RHTower.primeZeta 2)) := by
  exact finite_rates _ _ (Vacuum.reading_limit s (fun N _ => z N) 0)

theorem above_line (s : ℂ) (z : ℕ → SplitParameter) (hs : 1/2<s.re) :
    Tendsto (linearReading (fun _ => s) z) atTop atTop ∧
    Tendsto (entropyReading (fun _ => s) z) atTop atTop := by
  let a := 1-2*s.re
  have ha : a<0 := by dsimp [a]; linarith only [hs]
  have hn : a-1<0 := by linarith only [ha]
  let v := primeTotal (a-1)/primeTotal a
  have h : Tendsto (fun N : ℕ => vacuumWeight s N (z N)) atTop (𝓝 v) := by
    have lim := ((powerMass_limit hn).comp tendsto_natCast_atTop_atTop).div
      ((powerMass_limit ha).comp tendsto_natCast_atTop_atTop) (primeTotal_pos ha).ne'
    apply lim.congr
    intro N
    change powerMass (a-1) N/powerMass a N=_
    rw [vacuumWeight,probability_eq,pow_one,Nat.cast_one]
  have hv : 0<v := div_pos (primeTotal_pos hn) (primeTotal_pos ha)
  have hv' : v≤1/2 := le_of_tendsto' h (fun N => vacuum_le_half s N (z N))
  unfold linearReading entropyReading
  simpa only [linear_eq,spectral_eq] using
    positive_entropy_growth hv (hv'.trans_lt (by norm_num)) h

private theorem selects (f : ℕ → ℝ) (s : ℂ) {v : ℝ} (pos : 0<v)
    (hot : s.re<1/2 → Tendsto f atTop (𝓝 0))
    (cold : 1/2<s.re → Tendsto f atTop atTop)
    (critical : s.re=1/2 → Tendsto f atTop (𝓝 v)) :
    (∃ d : ℝ, 0<d ∧ Tendsto f atTop (𝓝 d)) ↔ ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ x y,T x y=split s x y := by
  rw [split_isometric_iff]
  constructor
  · rintro ⟨d,hd,h⟩
    rcases lt_trichotomy s.re (1/2) with low|eq|high
    · exact False.elim (hd.ne' (tendsto_nhds_unique h (hot low)))
    · exact eq
    · obtain ⟨_,p,q⟩ := (((cold high).eventually_gt_atTop (d+1)).and
        (h.eventually_lt_const (lt_add_one d))).exists
      exact False.elim (p.asymm q)
  · exact fun hs => ⟨v,pos,critical hs⟩

private theorem prime_two_pos : 0<_root_.RHTower.primeZeta 2 := by
  rw [←total_eq_primeZeta]
  exact primeTotal_pos (by norm_num)

theorem linear_isometric_iff (s : ℂ) (z : ℕ → SplitParameter) :
    (∃ v : ℝ, 0<v ∧ Tendsto (linearReading (fun _ => s) z) atTop (𝓝 v)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x,T f x=split s f x :=
  selects _ s (mul_pos (by norm_num) prime_two_pos)
    (fun h => (below_line s z h).1) (fun h => (above_line s z h).1)
    (fun h => (on_line (fun _ => ⟨s,h⟩) z).1)

theorem entropy_isometric_iff (s : ℂ) (z : ℕ → SplitParameter) :
    (∃ v : ℝ, 0<v ∧ Tendsto (entropyReading (fun _ => s) z) atTop (𝓝 v)) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x,T f x=split s f x :=
  selects _ s prime_two_pos
    (fun h => (below_line s z h).2) (fun h => (above_line s z h).2)
    (fun h => (on_line (fun _ => ⟨s,h⟩) z).2)

#print axioms below_line
#print axioms on_line
#print axioms above_line
#print axioms linear_isometric_iff
#print axioms entropy_isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement
