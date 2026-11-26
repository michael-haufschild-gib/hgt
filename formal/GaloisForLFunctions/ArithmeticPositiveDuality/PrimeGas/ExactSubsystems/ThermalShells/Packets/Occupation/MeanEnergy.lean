import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Reflection

/-! # Mean total energy determines the critical split -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation

open Finset Filter Topology Real

private theorem succ_cell (n j : ℕ) (p : ℝ) :
    bin (n+1) (j+1) p*((j+1:ℕ):ℝ) = ((n+1:ℕ):ℝ)*p*bin n j p := by
  have h : (((n+1).choose (j+1):ℕ):ℝ)*((j+1:ℕ):ℝ) = ((n+1:ℕ):ℝ)*(n.choose j:ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n j).symm
  simp only [bin,Nat.succ_sub_succ_eq_sub,pow_succ]
  linear_combination (p^j*p*(1-p)^(n-j))*h

private theorem bin_mean (m : ℕ) (p : ℝ) :
    (∑ j ∈ range (m+1), bin m j p*(j:ℝ)) = (m:ℝ)*p := by
  cases m with
  | zero => simp
  | succ n =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero,mul_zero,add_zero,succ_cell,← mul_sum]
    have total := bin_sum n p
    unfold binEvent at total
    rw [total,mul_one]

/-- The mean of the physical Hamiltonian above the lower endpoint is the packet gap
times the limiting mean number of upper occupations. -/
theorem mean_energy_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k)
    (b : ℝ) (m : ℕ) : Tendsto (energyRead c d D k b m id) criticalApproach
      (𝓝 ((m:ℝ)*D*upperProbability D k b)) := by
  have h := energy_limit hc hcd hD hk b m id continuous_id
  simp only [id_eq,← mul_assoc,← sum_mul,bin_mean] at h
  rwa [mul_right_comm (m:ℝ) (upperProbability D k b) D] at h

/-- Two scalar mean readings determine whether the full split preserves norm. -/
theorem split_isometric_iff_reflected_means {c d D : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D)
    {m : ℕ} (hm : 0 < m) (s : ℂ) (a : ℝ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      Tendsto (fun h => energyRead c d D 1 (2*s.re-a) m id h+energyRead c d D 1 (2*s.re+a) m id h)
        criticalApproach (𝓝 ((m:ℝ)*D)) := by
  letI := criticalApproach_neBot
  let b := 2*s.re-a
  let g := 2*s.re+a
  let p := upperProbability D 1 b
  let q := upperProbability D 1 g
  have mass (j : ℕ) := (cell_limit hc hcd hD zero_lt_one b m j).sub
    (cell_limit hc hcd hD zero_lt_one g m (m-j))
  have atom (j : ℕ) : Tendsto (fun h => read c d D 1 b m {j} h-read c d D 1 g m {m-j} h)
      criticalApproach (𝓝 0) ↔ bin m j p=bin m (m-j) q := by
    refine ⟨fun h => sub_eq_zero.mp (tendsto_nhds_unique (mass j) h),fun h => ?_⟩
    exact (sub_eq_zero.mpr h) ▸ mass j
  have hp : 0 ≤ p := div_nonneg (odds_pos D zero_lt_one b).le (add_pos zero_lt_one (odds_pos D zero_lt_one b)).le
  have hq : q ≤ 1 := (div_le_one (add_pos zero_lt_one (odds_pos D zero_lt_one g))).mpr (by linarith)
  have counts : (∀ j ≤ m, Tendsto (fun h => read c d D 1 b m {j} h-read c d D 1 g m {m-j} h) criticalApproach (𝓝 0)) ↔ p=1-q := by
    constructor
    · intro h
      exact (bin_reflect_iff hm hp hq).mp fun j hj => (atom j).mp (h j hj)
    · intro h j hj
      exact (atom j).mpr ((bin_reflect_iff hm hp hq).mpr h j hj)
  have L := (mean_energy_limit hc hcd hD zero_lt_one b m).add (mean_energy_limit hc hcd hD zero_lt_one g m)
  change Tendsto _ _ (𝓝 ((m:ℝ)*D*p+(m:ℝ)*D*q)) at L
  rw [← mul_add] at L
  have hpos : 0 < (m:ℝ)*D := mul_pos (Nat.cast_pos.mpr hm) hD
  rw [split_isometric_iff_reflected_counts hc hcd hD hm s a,counts]
  constructor
  · intro h
    have he : p+q=1 := by linarith only [h]
    simpa only [he,mul_one] using L
  · intro h
    have he := tendsto_nhds_unique L h
    have eqv : p+q=1 := mul_left_cancel₀ hpos.ne' (he.trans (mul_one _).symm)
    linarith only [eqv]

/-- A single temperature suffices when the tested expectation is the midpoint energy. -/
theorem split_isometric_iff_mean_midpoint {c d D : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D)
    {m : ℕ} (hm : 0 < m) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      Tendsto (energyRead c d D 1 (2*s.re) m id) criticalApproach (𝓝 ((m:ℝ)*D/2)) := by
  have both := split_isometric_iff_reflected_means hc hcd hD hm s 0
  simp only [sub_zero,add_zero] at both
  rw [both]
  constructor
  · intro h
    apply (h.div_const 2).congr
    intro u
    change (_+_)/2=_
    ring
  · intro h
    simpa only [show (m:ℝ)*D/2+((m:ℝ)*D/2)=(m:ℝ)*D by ring] using h.add h

/-- With two occupied primes and unit separation, one energy reading has limit one
exactly on the critical line. -/
theorem critical_line_iff_mean_two (s : ℂ) :
    s.re=1/2 ↔ Tendsto (energyRead 1 2 1 1 (2*s.re) 2 id) criticalApproach (𝓝 1) := by
  have h := split_isometric_iff_mean_midpoint (c:=1) (d:=2) (D:=1) zero_lt_one one_lt_two zero_lt_one
    (Nat.zero_lt_succ 1) s
  rw [split_isometric_iff] at h
  simpa only [Nat.cast_ofNat,mul_one,div_self (two_ne_zero : (2:ℝ) ≠ 0)] using h

#print axioms mean_energy_limit
#print axioms split_isometric_iff_reflected_means
#print axioms split_isometric_iff_mean_midpoint
#print axioms critical_line_iff_mean_two

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation
