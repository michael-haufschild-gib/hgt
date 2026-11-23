import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Mixture

/-! # Probability amplitudes and the heat-range moment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology
open GaloisForLFunctions.HTGeometry

/-- A gas vector specified by square-summable coefficients in increasing energy order. -/
def gasOfCoords (z : ℕ → ℂ) (hz : Summable (fun k => ‖z k‖^2)) : Gas :=
  ⟨fun n => z (Equiv.pnatEquivNat n),HilbertSchmidt.memℓp_of_sq (Equiv.pnatEquivNat.summable_iff.mpr hz)⟩

theorem gasOfCoords_at (z : ℕ → ℂ) (hz) (k : ℕ) : gasOfCoords z hz (number k) = z k := rfl

theorem gas_norm_sq (v : Gas) : ‖v‖^2 = ∑' k, ‖v (number k)‖^2 :=
  (lp_norm_sq_eq_tsum v).trans (Equiv.pnatEquivNat.symm.tsum_eq _).symm

theorem gas_coords_summable (v : Gas) : Summable (fun k => ‖v (number k)‖^2) :=
  Equiv.pnatEquivNat.symm.summable_iff.mpr (lp_summable_norm_sq v)

private theorem norm_inverse_heat (v : Gas) (k : ℕ) :
    ‖(attenuation (number k):ℂ)⁻¹*v (number k)‖^2 = ‖v (number k)‖^2/occupationWeight k := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le,mul_pow,inv_pow,div_eq_inv_mul]
  rfl

/-- A missing wave lies in the range of the critical propagator exactly when its inverse occupation moment is finite. -/
theorem heat_range_iff_summable (v : Gas) :
    v ∈ LinearMap.range criticalOperator.toLinearMap ↔ Summable (fun k => ‖v (number k)‖^2/occupationWeight k) := by
  constructor
  · rintro ⟨f,rfl⟩
    have he (k : ℕ) : ‖criticalOperator f (number k)‖^2/occupationWeight k = ‖f (number k)‖^2 := by
      rw [critical_apply,norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (attenuation_pos _).ne')
    exact (gas_coords_summable f).congr (fun k => (he k).symm)
  · intro hs
    let z (k : ℕ) := (attenuation (number k):ℂ)⁻¹*v (number k)
    have hz : Summable (fun k => ‖z k‖^2) := hs.congr (fun k => (norm_inverse_heat v k).symm)
    refine ⟨gasOfCoords z hz,lp.ext (funext (fun n => ?_))⟩
    obtain ⟨k,rfl⟩ := number_surjective n
    change (attenuation (number k):ℂ)*((attenuation (number k):ℂ)⁻¹*v (number k)) = v (number k)
    rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (attenuation_pos _).ne')]

private theorem sqrt_probability_sq {m : ℕ} (b : PrefixData m) (k : ℕ) :
    ‖(Real.sqrt (prefixProbability b k):ℂ)‖^2 = prefixProbability b k := by
  rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (probability_nonneg b k)]

/-- The canonical real nonnegative missing wave for a prescribed prefix. -/
def prefixWave {m : ℕ} (b : PrefixData m) : Gas :=
  gasOfCoords (fun k => (Real.sqrt (prefixProbability b k):ℂ))
    ((probability_hasSum b).summable.congr (fun k => (sqrt_probability_sq b k).symm))

theorem prefixWave_at {m : ℕ} (b : PrefixData m) (k : ℕ) :
    prefixWave b (number k) = (Real.sqrt (prefixProbability b k):ℂ) := rfl

theorem prefixWave_mass {m : ℕ} (b : PrefixData m) (k : ℕ) : ‖prefixWave b (number k)‖^2 = prefixProbability b k :=
  sqrt_probability_sq b k

theorem prefixWave_norm {m : ℕ} (b : PrefixData m) : ‖prefixWave b‖ = 1 := by
  have he := gas_norm_sq (prefixWave b)
  simp only [prefixWave_mass,(probability_hasSum b).tsum_eq] at he
  nlinarith only [he,norm_nonneg (prefixWave b)]

/-- Pointwise continuity of the square-root amplitudes upgrades to Hilbert norm continuity under the fixed summable tail. -/
theorem prefixWave_continuous (m : ℕ) : Continuous (prefixWave (m := m)) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let f (c : PrefixData m) (k : ℕ) := (Real.sqrt (prefixProbability c k)-Real.sqrt (prefixProbability b k))^2
  have hcont (k : ℕ) : Continuous (fun c => f c k) := ((Real.continuous_sqrt.comp (probability_continuous k)).sub continuous_const).pow 2
  have hbound (k : ℕ) (c : PrefixData m) : ‖f c k‖ ≤ 4*prefixCap m k := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hc := probability_le_cap c k
    have hb := probability_le_cap b k
    have hprod := mul_nonneg (Real.sqrt_nonneg (prefixProbability c k)) (Real.sqrt_nonneg (prefixProbability b k))
    dsimp only [f]
    nlinarith only [hc,hb,Real.sq_sqrt (probability_nonneg c k),Real.sq_sqrt (probability_nonneg b k),hprod,probability_nonneg c k]
  have he (c : PrefixData m) : ‖prefixWave c-prefixWave b‖^2 = ∑' k, f c k := by
    rw [gas_norm_sq]
    apply tsum_congr
    intro k
    change ‖(Real.sqrt (prefixProbability c k):ℂ)-(Real.sqrt (prefixProbability b k):ℂ)‖^2 = _
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hlim := ((continuous_tsum hcont ((prefixCap_summable m).mul_left 4) hbound).tendsto b).sqrt
  simpa only [← he,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using hlim

#print axioms heat_range_iff_summable
#print axioms prefixWave_norm
#print axioms prefixWave_continuous

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
