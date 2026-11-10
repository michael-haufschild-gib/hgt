import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeLogarithmicWindows

/-!
# Local tensor moments detect RH

The logarithmically weighted even moments of the prime traces may be
bounded on arbitrarily late logarithmic windows. A growth exponent
independent of the tensor order is equivalent to RH; the constants and
the chosen windows may depend on that order.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Primes in the logarithmic observation window. -/
def logarithmicPrimeWindow (T : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊Real.exp (T + primeLogarithmicRadius T)⌋₊ + 1)).filter
    fun p => p.Prime ∧ |Real.log p - T| ≤ primeLogarithmicRadius T

theorem mem_logarithmicPrimeWindow {p : ℕ} {T : ℝ} :
    p ∈ logarithmicPrimeWindow T ↔
      p.Prime ∧ |Real.log p - T| ≤ primeLogarithmicRadius T := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · rintro ⟨hp, hwin⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ?_), hp, hwin⟩
    apply Nat.le_floor
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    calc (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log hp0).symm
      _ ≤ Real.exp (T + primeLogarithmicRadius T) :=
        Real.exp_le_exp.mpr (by linarith only [(abs_le.mp hwin).2])

/-- The even moment of the prime trace on one logarithmic window. -/
def localPrimeTraceMoment (k : ℕ) (T : ℝ) : ℝ :=
  ∑ p ∈ logarithmicPrimeWindow T,
    Real.log p * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k)

theorem localPrimeTraceMoment_term_nonneg (k : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log p *
      (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k) := by
  refine mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) ?_
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- An absolute trace bound gives a moment bound with a common exponential rate. -/
theorem localPrimeTraceMoment_le_of_abs_bound {T K : ℝ} (hT : 0 ≤ T)
    (hR : primeLogarithmicRadius T ≤ T)
    (hbound : ∀ p ∈ logarithmicPrimeWindow T,
      |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K)
    (k : ℕ) : localPrimeTraceMoment k T ≤ 2 * |K| ^ (2 * k) * Real.exp (4 * T) := by
  classical
  have hE : 1 ≤ Real.exp (2 * T) := Real.one_le_exp (by linarith only [hT])
  have hcut : (⌊Real.exp (T + primeLogarithmicRadius T)⌋₊ : ℝ) ≤ Real.exp (2 * T) :=
    (Nat.floor_le (Real.exp_pos _).le).trans
      (Real.exp_le_exp.mpr (by linarith only [hR]))
  have hcard : ((logarithmicPrimeWindow T).card : ℝ) ≤ 2 * Real.exp (2 * T) := by
    have hn : (logarithmicPrimeWindow T).card ≤
        ⌊Real.exp (T + primeLogarithmicRadius T)⌋₊ + 1 := by
      exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_range])
    have hn' : ((logarithmicPrimeWindow T).card : ℝ) ≤
        (⌊Real.exp (T + primeLogarithmicRadius T)⌋₊ : ℝ) + 1 := by exact_mod_cast hn
    linarith only [hn', hcut, hE]
  have hterm : ∀ p ∈ logarithmicPrimeWindow T,
      Real.log p * (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k) ≤
        Real.exp (2 * T) * |K| ^ (2 * k) := by
    intro p hp
    obtain ⟨hpp, hwin⟩ := mem_logarithmicPrimeWindow.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hpN : (p : ℝ) ≤ Real.exp (2 * T) := by
      have hn := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hn' : (p : ℝ) ≤ (⌊Real.exp (T + primeLogarithmicRadius T)⌋₊ : ℝ) := by
        exact_mod_cast hn
      exact hn'.trans hcut
    have hlog : Real.log p ≤ Real.exp (2 * T) :=
      (Real.log_le_sub_one_of_pos hp0).trans (by linarith only [hpN])
    have hpow : (2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) ^ (2 * k) ≤
        |K| ^ (2 * k) := by
      rw [pow_mul, pow_mul, ← sq_abs]
      exact pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ (abs_nonneg _)
        ((hbound p hp).trans (le_abs_self K)) 2) k
    exact mul_le_mul hlog hpow
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _) (Real.exp_pos _).le
  calc localPrimeTraceMoment k T
      ≤ ∑ _p ∈ logarithmicPrimeWindow T, Real.exp (2 * T) * |K| ^ (2 * k) :=
        Finset.sum_le_sum hterm
    _ = (logarithmicPrimeWindow T).card * (Real.exp (2 * T) * |K| ^ (2 * k)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.exp (2 * T)) * (Real.exp (2 * T) * |K| ^ (2 * k)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * |K| ^ (2 * k) * Real.exp (4 * T) := by
      rw [show 4 * T = 2 * T + 2 * T by ring, Real.exp_add]
      ring

/-- One tensor order bounds the width by its common growth rate divided by that order. -/
theorem zeta_re_le_of_localPrimeTraceMoment_bound {A C : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hbound : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      localPrimeTraceMoment k T ≤ C * Real.exp (A * T)) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + |A| / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.succ_le_iff.mp hk)
  have hlate : ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ primeLogarithmicRadius T ≤ T / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      primeLogarithmicRadius_div_tendsto_zero.eventually_le_const
        (by norm_num : (0 : ℝ) < 1 / 2)] with T hT hR
    refine ⟨hT, ?_⟩
    have h := (div_le_iff₀ (by linarith only [hT] : 0 < T)).mp hR
    linarith only [h]
  obtain ⟨W, hW⟩ := eventually_atTop.mp hlate
  apply (zeta_re_le_iff_abs_prime_logarithmic_power_windows (by positivity)).mpr
  refine ⟨|C| ^ ((1 : ℝ) / (2 * k)), fun U => ?_⟩
  obtain ⟨T, hT, hmoment⟩ := hbound (max U W)
  obtain ⟨hT2, hR⟩ := hW T ((le_max_right _ _).trans hT)
  refine ⟨T, (le_max_left _ _).trans hT, fun p hp hwin => ?_⟩
  have hlog : 1 ≤ Real.log p := by
    linarith only [(abs_le.mp hwin).1, hR, hT2]
  have hTlog : T ≤ 2 * Real.log p := by
    linarith only [(abs_le.mp hwin).1, hR]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let c : ℝ := 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re
  have hc0 : 0 ≤ c ^ (2 * k) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
  have hsingle : Real.log p * c ^ (2 * k) ≤ localPrimeTraceMoment k T :=
    Finset.single_le_sum
      (fun q hq => localPrimeTraceMoment_term_nonneg k (mem_logarithmicPrimeWindow.mp hq).1)
      (mem_logarithmicPrimeWindow.mpr ⟨hp, hwin⟩)
  have hexp : Real.exp (A * T) ≤ (p : ℝ) ^ (2 * |A|) := by
    rw [Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self A)
      (by linarith only [hT2] : 0 ≤ T)
    have h2 := mul_le_mul_of_nonneg_left hTlog (abs_nonneg A)
    linarith only [h1, h2]
  have hc2k : |c| ^ (2 * k) ≤ |C| * (p : ℝ) ^ (2 * |A|) := by
    rw [show |c| ^ (2 * k) = c ^ (2 * k) by rw [pow_mul, pow_mul, sq_abs]]
    calc
      c ^ (2 * k) ≤ Real.log p * c ^ (2 * k) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hlog hc0
      _ ≤ C * Real.exp (A * T) := hsingle.trans hmoment
      _ ≤ |C| * (p : ℝ) ^ (2 * |A|) :=
        mul_le_mul (le_abs_self C) hexp (Real.exp_pos _).le (abs_nonneg C)
  have hroot := Real.rpow_le_rpow (by positivity) hc2k
    (by positivity : (0 : ℝ) ≤ 1 / (2 * k))
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c),
    show ((2 * k : ℕ) : ℝ) * (1 / (2 * k)) = 1 by
      push_cast; field_simp [hk0.ne'],
    Real.rpow_one, Real.mul_rpow (abs_nonneg C) (by positivity),
    ← Real.rpow_mul hp0.le] at hroot
  convert hroot using 3
  ring

/-- Uniform growth of local tensor moments is exactly RH. Constants and windows may depend on `k`. -/
theorem riemannHypothesis_iff_localPrimeTraceMoments :
    RiemannHypothesis ↔ ∃ A : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ,
      ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ localPrimeTraceMoment k T ≤ C * Real.exp (A * T) := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_abs_prime_logarithmic_windows.mp hRH
    obtain ⟨W, hW⟩ := eventually_atTop.mp
      (primeLogarithmicRadius_shape.and (eventually_ge_atTop (0 : ℝ)))
    refine ⟨4, fun k _ => ⟨2 * |K| ^ (2 * k), fun U => ?_⟩⟩
    obtain ⟨T, hT, hbound⟩ := hK (max U W)
    obtain ⟨hshape, hT0⟩ := hW T ((le_max_right _ _).trans hT)
    exact ⟨T, (le_max_left _ _).trans hT,
      localPrimeTraceMoment_le_of_abs_bound hT0 hshape.2
        (fun p hp => hbound p (mem_logarithmicPrimeWindow.mp hp).1
          (mem_logarithmicPrimeWindow.mp hp).2) k⟩
  · rintro ⟨A, hA⟩
    apply riemannHypothesis_of_forall_re_le
    intro ρ hρ
    by_contra h
    have hdepth : 0 < ρ.re - 1 / 2 := by linarith only [lt_of_not_ge h]
    obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (|A| / (ρ.re - 1 / 2)))
    have hk1 : 1 ≤ k := by
      have hh : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
      exact_mod_cast hh.le
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Nat.succ_le_iff.mp hk1)
    obtain ⟨C, hC⟩ := hA k hk1
    have hw := zeta_re_le_of_localPrimeTraceMoment_bound hk1 hC ρ hρ
    have hlarge : |A| / (ρ.re - 1 / 2) < k := (le_max_right _ _).trans_lt hk
    rw [div_lt_iff₀ hdepth] at hlarge
    have hsmall : |A| / k < ρ.re - 1 / 2 :=
      (div_lt_iff₀ hk0).mpr (by nlinarith only [hlarge])
    linarith only [hw, hsmall]

#print axioms zeta_re_le_of_localPrimeTraceMoment_bound
#print axioms riemannHypothesis_iff_localPrimeTraceMoments

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
