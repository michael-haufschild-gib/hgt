import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction.Intensity
import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-! # Unique spectral intensity from unlabelled replica outcomes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction

open Filter Real MeasureTheory
open scoped Topology

/-- Equality-event calibration using the actual normalized Hilbert coefficients. -/
def waveReading (k : ℕ) (s : ℂ) (N : ℕ) :=
  (log (log N))^(k+2)*∑ p : PrimeAt N, (‖elementaryWave s N p‖^2)^(k+2)

theorem wave_probability (s : ℂ) (x : ℝ) (p : PrimeAt x) :
    ‖elementaryWave s x p‖^2=Ordinary.primeProbability (1-2*s.re) x p := by
  change ‖(‖rawWave s x‖:ℂ)⁻¹*heat s (primeLabel p)‖^2=_
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),
    mul_pow,inv_pow,rawWave_sq,Ordinary.heat_square,Ordinary.primeProbability]
  ring

theorem wave_reading (k : ℕ) (s : ℂ) (N : ℕ) :
    waveReading k s N=(log (log N))^(k+2)*coincidence (k+2) (1-2*s.re) N := by
  simp only [waveReading,coincidence,wave_probability]

/-- On the isometric line the calibration of each coincidence uses only the cutoff. -/
def reading (k N : ℕ) := (log (log N))^(k+2)*coincidence (k+2) 0 N

theorem reading_limit (k : ℕ) :
    Tendsto (reading k) atTop (𝓝 (_root_.RHTower.primeZeta ((k+2:ℕ):ℝ))) := by
  have ha := (powerMass_limit (replicated_negative k)).comp tendsto_natCast_atTop_atTop
  have hH := harmonic_mass_ratio.comp tendsto_natCast_atTop_atTop
  have lim := ha.div (hH.pow (k+2)) (by positivity)
  rw [one_pow,div_one,total_eq_primeZeta] at lim
  apply lim.congr'
  filter_upwards [Crossover.logEnergy_growth.eventually_gt_atTop 0] with N hL
  change powerMass (1-((k+2:ℕ):ℝ)) N/(powerMass 0 N/log (log N))^(k+2)=_
  rw [reading,coincidence_eq (by omega : 0<k+2),div_pow,
    show replicaIndex (k+2) 0=1-((k+2:ℕ):ℝ) by unfold replicaIndex; ring]
  field_simp [(powerMass_pos 0 N).ne',(show 0<log (log (N:ℝ)) from hL).ne']

theorem critical_reading (k N : ℕ) (t : ℝ) :
    waveReading k (Crossover.indexParameter 0 t) N=reading k N := by
  rw [wave_reading,reading]
  have hi : (Crossover.indexParameter 0 t).re=(1-0)/2 := by simp [Crossover.indexParameter]
  rw [hi,show (1:ℝ)-2*((1-0)/2)=0 by ring]

/-- Every moment must agree with its corresponding measured coincidence. -/
def realizes (μ : Measure ℝ) := ∀ k : ℕ, Tendsto (reading k) atTop (𝓝 (∫ x,(x:ℝ)^k ∂μ))

theorem realizes_intensity : realizes intensity := by
  intro k
  rw [moment]
  exact reading_limit k

/-- A positive Borel measure with these readings is forced to be finite
and compactly carried. No support or integrability assumption is needed. -/
theorem realizes_iff (μ : Measure ℝ) : realizes μ ↔ μ=intensity := by
  constructor
  · intro h
    let s (k : ℕ) := _root_.RHTower.primeZeta ((k+2:ℕ):ℝ)
    have readingμ (k : ℕ) : s k=∫ x,(x:ℝ)^k ∂μ := tendsto_nhds_unique (reading_limit k) (h k)
    have pos (k : ℕ) : 0<s k := by
      change 0<_root_.RHTower.primeZeta ((k+2:ℕ):ℝ)
      rw [←total_eq_primeZeta]
      exact primeTotal_pos (replicated_negative k)
    have hint (k : ℕ) : Integrable (fun x : ℝ => x^k) μ := by
      by_contra bad
      exact (pos k).ne' ((readingμ k).trans (integral_undef bad))
    have one : Integrable (fun _ : ℝ => (1:ℝ)) μ := by simpa only [pow_zero] using hint 0
    letI : IsFiniteMeasure μ := (integrable_const_iff_isFiniteMeasure one_ne_zero).mp one
    have sI (k : ℕ) : s k=∫ x,(x:ℝ)^k ∂intensity := (moment k).symm
    have ci : intensity (Set.Icc ((0:ℝ)-1) (0+1))ᶜ=0 := by simpa only [zero_sub,zero_add] using carried
    exact (_root_.HTGeometry.measure_eq_of_moments_eq_of_one_carried (c:=0) (r:=1) zero_lt_one
      ci sI integrable_moment readingμ hint).symm
  · rintro rfl
    exact realizes_intensity

/-- The common-outcome experiments determine a unique positive Borel measure. -/
theorem unique_readout : ∃! μ : Measure ℝ, realizes μ :=
  ⟨intensity,realizes_intensity,fun μ h => (realizes_iff μ).mp h⟩

theorem wave_realizes_iff (t : ℕ → ℝ) (μ : Measure ℝ) :
    (∀ k : ℕ, Tendsto (fun N => waveReading k (Crossover.indexParameter 0 (t N)) N)
      atTop (𝓝 (∫ x,(x:ℝ)^k ∂μ))) ↔ μ=intensity := by
  simpa only [critical_reading,realizes] using realizes_iff μ

/-- Spectral measure specified solely by the limiting yes/no readings. -/
def reconstructed : Measure ℝ := Classical.choose unique_readout.exists

theorem reconstructed_eq : reconstructed=intensity :=
  (realizes_iff reconstructed).mp (Classical.choose_spec unique_readout.exists)

/-- The apparatus can recover which integer labels are elementary from its inferred atoms. -/
theorem detects_prime (n : ℕ) : 0<reconstructed.real {node n} ↔ n.Prime := by
  rw [reconstructed_eq,atom]
  by_cases hp : n.Prime
  · rw [weight,if_pos hp]
    exact iff_of_true (pow_pos (inv_pos.mpr (Nat.cast_pos.mpr hp.pos)) 2) hp
  · rw [weight,if_neg hp]
    exact iff_of_false (lt_irrefl 0) hp

/-- All positive atoms, including tests at arbitrary real spectral points. -/
theorem atoms (x : ℝ) : 0<reconstructed.real {x} ↔ ∃ p : Nat.Primes, x=node p.val := by
  constructor
  · intro hx
    by_contra absent
    have vanish (n : ℕ) :
        ENNReal.ofReal (weight n)*({x} : Set ℝ).indicator (1 : ℝ → ENNReal) (node n)=0 := by
      by_cases hp : n.Prime
      · have off : node n∉({x} : Set ℝ) := fun eq => absent ⟨⟨n,hp⟩,(Set.mem_singleton_iff.mp eq).symm⟩
        rw [Set.indicator_of_notMem off,mul_zero]
      · simp only [weight,if_neg hp,ENNReal.ofReal_zero,zero_mul]
    rw [reconstructed_eq,Measure.real,intensity,_root_.HTGeometry.countableWeightedDirac_apply
      _ _ (measurableSet_singleton x),tsum_congr vanish,tsum_zero,ENNReal.toReal_zero] at hx
    exact (lt_irrefl _ hx)
  · rintro ⟨p,rfl⟩
    exact (detects_prime p.val).mpr p.property

#print axioms reading_limit
#print axioms wave_reading
#print axioms wave_realizes_iff
#print axioms unique_readout
#print axioms detects_prime
#print axioms atoms

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.Reconstruction
