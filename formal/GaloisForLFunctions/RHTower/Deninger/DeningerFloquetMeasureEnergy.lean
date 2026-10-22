import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetLatticeMeasure

/-!
# The half-density Floquet energy is an `L²` norm on the arithmetic lattice

Parseval on each prime circle writes the circle energy as the sum of the squared Fourier-transform
samples at the lattice frequencies `m/log q`.  Assembling the primes, the half-density Floquet
energy is exactly the `L²(μ_Fl)` norm of the sampling map

`h ↦ 𝓕(e^{t/2}h)`,

so the arithmetic lattice measure is the measure that turns the energy into a Hilbert norm.

* `deningerFloquetSample` : **the Mellin sampling map `h ↦ 𝓕(e^{t/2}h)`.**
* `deningerFourierSample_hasSum` : Parseval as a `HasSum` over the lattice.
* `deningerFloquetTerm_eq_sample` : the prime term is the weighted lattice sum.
* `lintegral_deningerFloquetSample_normSq` : **`E_Fl(h) = ∫ ‖𝓕(e^{t/2}h)‖² dμ_Fl`.**
-/

namespace RHTower

open SchwartzMap MeasureTheory Set
open scoped FourierTransform ENNReal

noncomputable section

/-- **The Mellin sampling map.**  On the critical line `s = 1/2 - 2πiξ` the Mellin transform of a
source cochain is the Fourier transform of its half-density trivialization. -/
def deningerFloquetSample (h : DeningerExpSchwartz) (ξ : ℝ) : ℂ :=
  𝓕 (((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ

/-- The prime-circle trace is square integrable on the fundamental cell. -/
theorem deningerPeriodizationSum_memLp {h : DeningerExpSchwartz} {L : ℝ} (hL : Real.log 2 ≤ L) :
    MemLp (deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L) 2
      (volume.restrict (Set.Ioc (0 : ℝ) L)) := by
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos one_lt_two) hL
  have hcont := deningerPeriodizationSum_continuous (h := h) hLpos
  have hbdd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) L)),
      ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖
        ≤ 5 * deningerMeyerSeminormFun 1 0 h := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun t ht => ?_)
    exact deningerPeriodizationSum_norm_le_period hL ht.1.le ht.2
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) L)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_Ioc_lt_top
  exact MemLp.of_bound hcont.aestronglyMeasurable _ hbdd

/-- **Parseval on the prime circle, as a `HasSum` over the frequency lattice.** -/
theorem deningerFourierSample_hasSum {h : DeningerExpSchwartz} {L : ℝ} (hL : Real.log 2 ≤ L) :
    HasSum (fun m : ℤ => ‖𝓕 (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ((m : ℝ) / L)‖ ^ 2)
      (L * ∫ t in (0 : ℝ)..L,
        ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖ ^ 2) := by
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos one_lt_two) hL
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hbase := hasSum_sq_fourierCoeffOn hLpos (deningerPeriodizationSum_memLp (h := h) hL)
  have hcoef : ∀ m : ℤ,
      ‖fourierCoeffOn hLpos (deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L) m‖
          ^ 2
        = (L ^ 2)⁻¹ * ‖𝓕 (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ((m : ℝ) / L)‖ ^ 2 := by
    intro m
    rw [deningerFourierCoeffOn_periodization
      (SchwartzMap.integrable ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) hLpos m]
    have harg : (1 / L) * (m : ℝ) = (m : ℝ) / L := by field_simp
    rw [harg, norm_smul, mul_pow]
    congr 1
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / L)]
    field_simp
  simp only [hcoef, sub_zero, smul_eq_mul] at hbase
  have hscaled := hbase.mul_left (L ^ 2)
  have hfun : (fun m : ℤ => L ^ 2
        * ((L ^ 2)⁻¹ * ‖𝓕 (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ((m : ℝ) / L)‖ ^ 2))
      = fun m : ℤ => ‖𝓕 (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ((m : ℝ) / L)‖ ^ 2 := by
    funext m
    field_simp
  rw [hfun] at hscaled
  have hval : L ^ 2 * (L⁻¹ * ∫ t in (0 : ℝ)..L,
        ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖ ^ 2)
      = L * ∫ t in (0 : ℝ)..L,
        ‖deningerPeriodizationSum ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) L t‖ ^ 2 := by
    field_simp
  rwa [hval] at hscaled

/-- The squared Fourier samples of a source cochain are summable along every prime lattice. -/
theorem deningerFloquetSample_summable (h : DeningerExpSchwartz) (q : Nat.Primes) :
    Summable fun m : ℤ => ‖deningerFloquetSample h (deningerFloquetNode (q : ℕ) m)‖ ^ 2 :=
  (deningerFourierSample_hasSum (h := deningerHalfDensityLift h)
    (deningerLog_two_le_primeLog q)).summable

/-- The prime Floquet term is the weighted lattice sum of squared Fourier samples. -/
theorem deningerFloquetTerm_eq_sample (h : DeningerExpSchwartz) (q : Nat.Primes) :
    deningerFloquetTerm (deningerHalfDensityLift h) (q : ℕ)
      = ((((q : ℕ) : ℝ) ^ 2)⁻¹ / Real.log ((q : ℕ) : ℝ))
        * ∑' m : ℤ, ‖deningerFloquetSample h (deningerFloquetNode (q : ℕ) m)‖ ^ 2 := by
  have hLpos := deningerPrimeLog_pos q
  have hsum := deningerFourierSample_hasSum (h := deningerHalfDensityLift h)
    (deningerLog_two_le_primeLog q)
  have htsum : (∑' m : ℤ, ‖deningerFloquetSample h (deningerFloquetNode (q : ℕ) m)‖ ^ 2)
      = Real.log ((q : ℕ) : ℝ) * ∫ t in (0 : ℝ)..Real.log ((q : ℕ) : ℝ),
        ‖deningerPeriodizationSum
          ((deningerHalfDensityLift h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))
          (Real.log ((q : ℕ) : ℝ)) t‖ ^ 2 := hsum.tsum_eq
  rw [htsum, deningerFloquetTerm]
  field_simp

/-- **The half-density Floquet energy is the `L²(μ_Fl)` norm of the Mellin sampling map.**  This
is the arithmetic lattice form of the energy, with the lattice weights packaged as a measure. -/
theorem lintegral_deningerFloquetSample_normSq (h : DeningerExpSchwartz) :
    ∫⁻ ξ, ENNReal.ofReal (‖deningerFloquetSample h ξ‖ ^ 2) ∂deningerFloquetMeasure
      = ENNReal.ofReal (deningerHalfDensityFloquetEnergy h) := by
  rw [lintegral_deningerFloquetMeasure, deningerHalfDensityFloquetEnergy, deningerFloquetEnergy,
    ENNReal.ofReal_tsum_of_nonneg
      (fun q => deningerFloquetTerm_nonneg _ q.2.one_lt.le)
      (deningerFloquetTerm_summable _)]
  refine tsum_congr fun q => ?_
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
  have hLpos := deningerPrimeLog_pos q
  have hwnn : (0 : ℝ) ≤ (((q : ℕ) : ℝ) ^ 2)⁻¹ / Real.log ((q : ℕ) : ℝ) := by positivity
  rw [deningerFloquetTerm_eq_sample, deningerFloquetWeight,
    ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity)
      (deningerFloquetSample_summable h q),
    ← ENNReal.ofReal_mul hwnn]

end

end RHTower
