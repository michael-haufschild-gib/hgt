import GaloisForLFunctions.HTGeometry.QuantumChannels.OscillatorHeatingThreshold
import GaloisForLFunctions.HTGeometry.CPVPrimeOccupation
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet

/-!
# A heating threshold for the prime-frequency thermal oscillators

Give the prime thermal mode its corpus frequency log p and a common heating
and damping rate. At the limiting threshold every individual mode is stable
but the spectral gap vanishes. Beyond it the stable primes form a finite
initial segment, with an explicit cutoff.
-/

noncomputable section
namespace GaloisForLFunctions.OscillatorHeating.PrimeModes
open Filter HTGeometry HTGeometry.CPV
open scoped Topology NNReal

/-- Real exponent of the undamped prime mode. -/
def exponent (G : ℝ≥0) (p : Nat.Primes) := growth (primeThermalCoordinate p) G

private theorem log_pos (p : Nat.Primes) : 0 < Real.log (p:ℝ) :=
  Real.log_pos (by exact_mod_cast p.2.one_lt)

private theorem frequency (p : Nat.Primes) : Real.exp (primeThermalCoordinate p) = Real.log (p:ℝ) :=
  Real.exp_log (log_pos p)

/-- Stability refers to every root of the actual three-by-three characteristic determinant. -/
def Stable (G : ℝ≥0) (d : ℝ) (p : Nat.Primes) :=
  ∀ z : ℂ, (pencil (primeThermalCoordinate p) d G z).det = 0 → z.re < 0

theorem stable_iff (G : ℝ≥0) (d : ℝ) (p : Nat.Primes) :
    Stable G d p ↔ exponent G p < d := by
  exact (spectral_stability _ _ _).trans (growth_lt_iff _ _ _).symm

private theorem bound (G : ℝ≥0) (p : Nat.Primes) :
    0 ≤ exponent G p ∧ exponent G p ≤ (G:ℝ)/2 := growth_interval _ _

/-- The exact prime-frequency defect. -/
theorem rate_gap (G : ℝ≥0) (p : Nat.Primes) :
    Real.log (p:ℝ)^2*((G:ℝ)/2-exponent G p) = exponent G p^3/4 := by
  simpa only [frequency,exponent] using growth_gap (primeThermalCoordinate p) G

/-- Growth tends to half the heating strength along the cofinite prime filter. -/
theorem exponent_limit (G : ℝ≥0) : Tendsto (exponent G) cofinite (𝓝 ((G:ℝ)/2)) := by
  have hden := (tendsto_pow_atTop (α := ℝ) (by norm_num : (2:ℕ) ≠ 0)).comp
    tendsto_primeRealLog_cofinite_atTop
  have hlim : Tendsto (fun p : Nat.Primes => (exponent G p^3/4)/(Real.log (p:ℝ)^2)) cofinite (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := 0) (B := ((G:ℝ)/2)^3/4) _ _ hden
    · exact Eventually.of_forall fun p => div_nonneg (pow_nonneg (bound G p).1 _) (by norm_num)
    · exact Eventually.of_forall fun p => div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (bound G p).1 (bound G p).2 3) (by norm_num)
  have he (p : Nat.Primes) : (G:ℝ)/2-(exponent G p^3/4)/(Real.log (p:ℝ)^2) = exponent G p := by
    have hp := rate_gap G p
    field_simp [(log_pos p).ne']
    linarith only [hp]
  simpa only [sub_zero,he] using (tendsto_const_nhds (x := (G:ℝ)/2)).sub hlim

/-- Leading coefficient of the inverse-log-squared spectral gap, valid also at zero heating. -/
theorem scaled_gap_limit (G : ℝ≥0) :
    Tendsto (fun p : Nat.Primes => Real.log (p:ℝ)^2*((G:ℝ)/2-exponent G p))
      cofinite (𝓝 ((G:ℝ)^3/32)) := by
  simp_rw [rate_gap]
  convert ((exponent_limit G).pow 3).div_const 4 using 1 <;> ring

/-- A common positive decay margin exists exactly below the limiting threshold. -/
theorem uniform_margin (d : ℝ) (G : ℝ≥0) :
    (∃ ε > 0, ∀ p, exponent G p ≤ d-ε) ↔ (G:ℝ) < 2*d := by
  constructor
  · rintro ⟨ε,hε,h⟩
    have hh := le_of_tendsto (exponent_limit G) (Eventually.of_forall h)
    linarith only [hh,hε]
  · intro h
    exact ⟨d-(G:ℝ)/2,by linarith only [h],fun p => by linarith only [(bound G p).2]⟩

/-- All individual prime modes decay up to and including the limiting threshold. -/
theorem all_stable (v : ℝ) (G : ℝ≥0) :
    (∀ p, Stable G (Real.exp v) p) ↔ (G:ℝ) ≤ 2*Real.exp v := by
  constructor
  · intro h
    have hh := le_of_tendsto (exponent_limit G)
      (Eventually.of_forall fun p => ((stable_iff _ _ _).mp (h p)).le)
    linarith only [hh]
  · intro h p
    rw [Stable,spectral_stability,strength,frequency]
    have hp : 0 < (Real.exp v)^3/(2*Real.log (p:ℝ)^2) :=
      div_pos (pow_pos (Real.exp_pos _) _) (mul_pos (by norm_num) (sq_pos_of_pos (log_pos _)))
    linarith only [h,hp]

/-- At equality every mode decays at a rate asymptotic to d³/(4 log² p). -/
theorem critical_prime_modes (v : ℝ) :
    let d := Real.exp v
    let G : ℝ≥0 := ⟨2*d,by positivity⟩
    (∀ p, Stable G d p) ∧
      (¬ ∃ ε > 0, ∀ p, exponent G p ≤ d-ε) ∧
      Tendsto (fun p : Nat.Primes => Real.log (p:ℝ)^2*(d-exponent G p)) cofinite (𝓝 (d^3/4)) := by
  intro d G
  refine ⟨(all_stable v G).mpr le_rfl,?_,?_⟩
  · rw [uniform_margin]
    exact lt_irrefl _
  · have h := scaled_gap_limit G
    change Tendsto (fun p : Nat.Primes => Real.log (p:ℝ)^2*((2*d)/2-exponent G p))
      cofinite (𝓝 ((2*d)^3/32)) at h
    simpa only [show 2*d/2 = d by ring,show (2*d)^3/32 = d^3/4 by ring] using h

/-- For strength 2d+e with e>0 the stable primes are precisely those below
exp(sqrt(d³/(2e))). Equality gives a neutral real eigenvalue. -/
theorem explicit_cutoff (v t : ℝ) (p : Nat.Primes) :
    let d := Real.exp v
    let e := Real.exp t
    let G : ℝ≥0 := ⟨2*d+e,by positivity⟩
    Stable G d p ↔ (p:ℝ) < Real.exp (Real.sqrt (d^3/(2*e))) := by
  intro d e G
  have hd : 0 < d := Real.exp_pos _
  have he : 0 < e := Real.exp_pos _
  have hl := log_pos p
  have hp : 0 < (p:ℝ) := by exact_mod_cast p.2.pos
  rw [Stable,spectral_stability,strength,frequency,← Real.log_lt_iff_lt_exp hp]
  change 2*d+e < 2*d+d^3/(2*Real.log (p:ℝ)^2) ↔ _
  rw [add_lt_add_iff_left,lt_div_iff₀ (by positivity),
    Real.lt_sqrt hl.le]
  rw [lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith only [h]

/-- Finitely many stable prime modes occur exactly above the limiting threshold. -/
theorem finite_stable (v : ℝ) (G : ℝ≥0) :
    {p : Nat.Primes | Stable G (Real.exp v) p}.Finite ↔ 2*Real.exp v < (G:ℝ) := by
  constructor
  · intro hf
    by_contra! h
    have ha := (all_stable v G).mpr h
    have hu : {p : Nat.Primes | Stable G (Real.exp v) p} = Set.univ := Set.eq_univ_of_forall ha
    rw [hu] at hf
    exact Set.infinite_univ hf
  · intro h
    have hev := (exponent_limit G).eventually_const_lt (show Real.exp v < (G:ℝ)/2 by linarith only [h])
    have hc : ∀ᶠ p : Nat.Primes in cofinite, ¬ Stable G (Real.exp v) p :=
      hev.mono fun p hp => fun hs => (not_lt_of_ge hp.le) ((stable_iff _ _ _).mp hs)
    simpa using (Filter.eventually_cofinite.mp hc)

#print axioms rate_gap
#print axioms exponent_limit
#print axioms scaled_gap_limit
#print axioms uniform_margin
#print axioms all_stable
#print axioms critical_prime_modes
#print axioms explicit_cutoff
#print axioms finite_stable
end GaloisForLFunctions.OscillatorHeating.PrimeModes
