import GaloisForLFunctions.HTGeometry.NearestNeighborQuditPathRecurrenceLaw

/-!
# Thermodynamic extinction of generic global projective recurrence

The generic static nearest-neighbour qudit-path theorem gives the exact
completed-time density of a strict coordinatewise projective return target at
every finite chain length.  This module takes the thermodynamic limit of that
exact density.  At every fixed strict tolerance the density decays
exponentially in Hilbert-space dimension and therefore doubly exponentially
in chain length.

Time completion is taken first at each finite size.  The result does not claim
a first-return distribution or construct an infinite-volume global orbit.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One-coordinate Haar mass of the strict chordal return target. -/
def projectiveReturnDensityBase (ε : ℝ) : ℝ :=
  2 * Real.arcsin (ε / 2) / Real.pi

/-- Exact large-deviation rate of the strict projective return target. -/
def thermodynamicProjectiveReturnRate (ε : ℝ) : ℝ :=
  -Real.log (projectiveReturnDensityBase ε)

/-- Completed strict-return density for a maximally projective `n`-site
`q`-level path. -/
def quditPathProjectiveReturnDensity (q : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  projectiveReturnDensityBase ε ^ (q ^ n - 1)

/-- Every positive tolerance has positive one-coordinate return mass. -/
theorem projectiveReturnDensityBase_pos {ε : ℝ} (hε0 : 0 < ε) :
    0 < projectiveReturnDensityBase ε := by
  have hx : 0 < ε / 2 := by linarith
  exact div_pos (mul_pos (by norm_num) (Real.arcsin_pos.mpr hx)) Real.pi_pos

/-- Every strict tolerance below the chordal diameter has one-coordinate
return mass strictly below one. -/
theorem projectiveReturnDensityBase_lt_one {ε : ℝ} (hε2 : ε < 2) :
    projectiveReturnDensityBase ε < 1 := by
  have hx : ε / 2 < 1 := by linarith
  have ha := Real.arcsin_lt_pi_div_two.mpr hx
  rw [projectiveReturnDensityBase, div_lt_one Real.pi_pos]
  linarith

/-- The thermodynamic return-density rate is strictly positive at every
fixed strict tolerance. -/
theorem thermodynamicProjectiveReturnRate_pos {ε : ℝ}
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    0 < thermodynamicProjectiveReturnRate ε := by
  rw [thermodynamicProjectiveReturnRate]
  exact neg_pos.mpr (Real.log_neg
    (projectiveReturnDensityBase_pos hε0)
    (projectiveReturnDensityBase_lt_one hε2))

/-- Exact exponential large-deviation form of the finite-size density. -/
theorem quditPathProjectiveReturnDensity_eq_exp {q n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) :
    quditPathProjectiveReturnDensity q ε n =
      Real.exp (-((q ^ n - 1 : ℕ) : ℝ) *
        thermodynamicProjectiveReturnRate ε) := by
  rw [quditPathProjectiveReturnDensity, thermodynamicProjectiveReturnRate]
  calc
    projectiveReturnDensityBase ε ^ (q ^ n - 1) =
        Real.exp (((q ^ n - 1 : ℕ) : ℝ) *
          Real.log (projectiveReturnDensityBase ε)) := by
      rw [Real.exp_nat_mul, Real.exp_log (projectiveReturnDensityBase_pos hε0)]
    _ = Real.exp (-((q ^ n - 1 : ℕ) : ℝ) *
          -Real.log (projectiveReturnDensityBase ε)) := by ring_nf

/-- At every fixed strict tolerance, generic global projective return density
vanishes in the thermodynamic limit. -/
theorem quditPathProjectiveReturnDensity_tendsto_zero
    {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} (hε0 : 0 < ε) (hε2 : ε < 2) :
    Tendsto (quditPathProjectiveReturnDensity q ε) atTop (𝓝 0) := by
  change Tendsto
    (fun n : ℕ => projectiveReturnDensityBase ε ^ (q ^ n - 1)) atTop (𝓝 0)
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have hexp : Tendsto (fun n : ℕ => q ^ n - 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [hpow.eventually_ge_atTop (b + 1)] with n hn
    omega
  have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one
    (projectiveReturnDensityBase_pos hε0).le
    (projectiveReturnDensityBase_lt_one hε2)
  simpa [Function.comp_def] using hbase.comp hexp

/-- Exact negative-log density in terms of Hilbert-space dimension. -/
theorem neg_log_quditPathProjectiveReturnDensity_eq
    {q n : ℕ} {ε : ℝ} :
    -Real.log (quditPathProjectiveReturnDensity q ε n) =
      ((q ^ n - 1 : ℕ) : ℝ) * thermodynamicProjectiveReturnRate ε := by
  rw [quditPathProjectiveReturnDensity, Real.log_pow,
    thermodynamicProjectiveReturnRate]
  ring

/-- Exact normalized finite-size rate identity. -/
theorem normalized_neg_log_quditPathProjectiveReturnDensity_eq
    {q n : ℕ} (hq : 2 ≤ q) {ε : ℝ} :
    -Real.log (quditPathProjectiveReturnDensity q ε n) / (q : ℝ) ^ n =
      (1 - ((q : ℝ) ^ n)⁻¹) * thermodynamicProjectiveReturnRate ε := by
  rw [neg_log_quditPathProjectiveReturnDensity_eq]
  have hqpow : 1 ≤ q ^ n := Nat.one_le_pow n q (by omega)
  rw [Nat.cast_sub hqpow, Nat.cast_pow]
  have hne : (q : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp
  ring

/-- The negative logarithm per Hilbert-space dimension converges to the exact
strict-return rate. -/
theorem normalized_neg_log_quditPathProjectiveReturnDensity_tendsto_rate
    {q : ℕ} (hq : 2 ≤ q) {ε : ℝ} :
    Tendsto
      (fun n : ℕ =>
        -Real.log (quditPathProjectiveReturnDensity q ε n) / (q : ℝ) ^ n)
      atTop (𝓝 (thermodynamicProjectiveReturnRate ε)) := by
  have hpow : Tendsto (fun n : ℕ => (q : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1 < q by omega))
  have hinv : Tendsto (fun n : ℕ => ((q : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    hpow.inv_tendsto_atTop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hmain := (hone.sub hinv).mul_const
    (thermodynamicProjectiveReturnRate ε)
  simpa using hmain.congr (fun n =>
    (normalized_neg_log_quditPathProjectiveReturnDensity_eq hq).symm)

/-- Exact finite-size decomposition of the site-normalized double logarithm. -/
theorem doubleLog_quditPathProjectiveReturnDensity_decomposition
    {q n : ℕ} (hq : 2 ≤ q) (hn : 0 < n) {ε : ℝ}
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    Real.log (-Real.log (quditPathProjectiveReturnDensity q ε n)) / (n : ℝ) =
      Real.log (q : ℝ) +
        Real.log (1 - ((q : ℝ) ^ n)⁻¹) / (n : ℝ) +
        Real.log (thermodynamicProjectiveReturnRate ε) / (n : ℝ) := by
  rw [neg_log_quditPathProjectiveReturnDensity_eq]
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hqpos : (0 : ℝ) < q := lt_trans zero_lt_one hqR
  have hQpos : 0 < (q : ℝ) ^ n := pow_pos hqpos _
  have hQone : 1 < (q : ℝ) ^ n := one_lt_pow₀ hqR hn.ne'
  have hfacpos : 0 < 1 - ((q : ℝ) ^ n)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ hQone)
  have hRpos := thermodynamicProjectiveReturnRate_pos hε0 hε2
  have hqpow : 1 ≤ q ^ n := Nat.one_le_pow n q (by omega)
  rw [Nat.cast_sub hqpow, Nat.cast_pow]
  have hfactor :
      ((q : ℝ) ^ n - 1) * thermodynamicProjectiveReturnRate ε =
        ((q : ℝ) ^ n * (1 - ((q : ℝ) ^ n)⁻¹)) *
          thermodynamicProjectiveReturnRate ε := by
    field_simp
  norm_num only [Nat.cast_one]
  rw [hfactor,
    Real.log_mul (mul_ne_zero (ne_of_gt hQpos) (ne_of_gt hfacpos)) (ne_of_gt hRpos),
    Real.log_mul (ne_of_gt hQpos) (ne_of_gt hfacpos), Real.log_pow]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The return density is doubly exponential in site count: its normalized
double logarithm converges to `log q`. -/
theorem doubleLog_quditPathProjectiveReturnDensity_tendsto_log_q
    {q : ℕ} (hq : 2 ≤ q) {ε : ℝ}
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    Tendsto
      (fun n : ℕ =>
        Real.log (-Real.log (quditPathProjectiveReturnDensity q ε n)) / (n : ℝ))
      atTop (𝓝 (Real.log (q : ℝ))) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hpow : Tendsto (fun n : ℕ => (q : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hqR
  have hinv : Tendsto (fun n : ℕ => ((q : ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
    hpow.inv_tendsto_atTop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub : Tendsto (fun n : ℕ => 1 - ((q : ℝ) ^ n)⁻¹) atTop (𝓝 1) := by
    simpa using hone.sub hinv
  have hlogsub :
      Tendsto (fun n : ℕ => Real.log (1 - ((q : ℝ) ^ n)⁻¹)) atTop (𝓝 0) := by
    simpa using hsub.log one_ne_zero
  have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hterm1 : Tendsto
      (fun n : ℕ => Real.log (1 - ((q : ℝ) ^ n)⁻¹) / (n : ℝ))
      atTop (𝓝 0) := hlogsub.div_atTop hncast
  have hterm2 : Tendsto
      (fun n : ℕ => Real.log (thermodynamicProjectiveReturnRate ε) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hncast
  have hsum : Tendsto
      (fun n : ℕ => Real.log (q : ℝ) +
        Real.log (1 - ((q : ℝ) ^ n)⁻¹) / (n : ℝ) +
        Real.log (thermodynamicProjectiveReturnRate ε) / (n : ℝ))
      atTop (𝓝 (Real.log (q : ℝ))) := by
    simpa using (tendsto_const_nhds.add hterm1).add hterm2
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (doubleLog_quditPathProjectiveReturnDensity_decomposition
    hq (by omega) hε0 hε2).symm

/-- **Thermodynamic projective-recurrence extinction law.** At every fixed
strict tolerance, the completed return density of the generic maximally
projective `q`-level path has a positive Hilbert-dimension rate, vanishes in
the size limit, and has site-normalized double logarithm converging to
`log q`.  The completed-time limit supplying this density is taken at each
finite size before this theorem's size limit. -/
theorem thermodynamicProjectiveRecurrenceExtinctionLaw
    {q : ℕ} (hq : 2 ≤ q) {ε : ℝ}
    (hε0 : 0 < ε) (hε2 : ε < 2) :
    0 < thermodynamicProjectiveReturnRate ε ∧
      Tendsto (quditPathProjectiveReturnDensity q ε) atTop (𝓝 0) ∧
      Tendsto
        (fun n : ℕ =>
          -Real.log (quditPathProjectiveReturnDensity q ε n) / (q : ℝ) ^ n)
        atTop (𝓝 (thermodynamicProjectiveReturnRate ε)) ∧
      Tendsto
        (fun n : ℕ =>
          Real.log (-Real.log (quditPathProjectiveReturnDensity q ε n)) /
            (n : ℝ))
        atTop (𝓝 (Real.log (q : ℝ))) := by
  exact ⟨thermodynamicProjectiveReturnRate_pos hε0 hε2,
    quditPathProjectiveReturnDensity_tendsto_zero hq hε0 hε2,
    normalized_neg_log_quditPathProjectiveReturnDensity_tendsto_rate hq,
    doubleLog_quditPathProjectiveReturnDensity_tendsto_log_q hq hε0 hε2⟩

end

end GaloisForLFunctions.HTGeometry
