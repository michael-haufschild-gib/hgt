import GaloisForLFunctions.RHTower.PMPowerDampedMobiusNegativePrimeCurrent

/-!
# Complete signed prime-update energy balance

Finite prime insertion telescopes pointwise. At the physical horizon the
canonical finite core equals the full PM source. Integration retains the
quadratic current and both signed mixed-current parts exactly. No canonical
L2-admission premise is used.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem pmqb_norm_sub (z w : ℂ) (r : ℝ) :
    ‖z-(r : ℂ)*w‖^2 = ‖z‖^2+r^2*‖w‖^2-2*r*(z*(starRingEnd ℂ) w).re := by
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,
    Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

/-- Pointwise telescoping of every actual prime update, with the complete
signed density retained at each prime. -/
theorem pmPrimeUpdate_pointwise_energy_balance (ε : ℝ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε t‖^2 =
      ‖fermiNymanGen 1 t‖^2+
      ∑ p ∈ mobiusFinitePrimeAperture N,
        ((p : ℝ)^(-2*ε)*
          ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (p-1)) ε ((p : ℝ)*t)‖^2-
            2*pmPrimeMixedDensity ε p t) := by
  induction N with
  | zero =>
    have hzero : mobiusFinitePrimeAperture 0 = ∅ := by
      ext p
      simp only [mobiusFinitePrimeAperture,Finset.mem_filter,Finset.mem_range,Finset.notMem_empty,iff_false,not_and]
      intro hp
      have hp0 : p = 0 := by omega
      simpa only [hp0] using Nat.not_prime_zero
    rw [hzero,pmFinitePrimePowerDampedFermiSource_empty]
    simp
  | succ N ih =>
    by_cases hp : (N+1).Prime
    · have hn : N+1 ∉ mobiusFinitePrimeAperture N := by
        intro h
        have hh := (Finset.mem_filter.mp h).1
        have := Finset.mem_range.mp hh
        omega
      have hS : ∀ p ∈ mobiusFinitePrimeAperture N,p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
      rw [pm_mobiusFinitePrimeAperture_succ,if_pos hp,Finset.sum_insert hn,
        pmFinitePrimePowerDampedFermiSource_insert ε _ hS hp hn ht,pmqb_norm_sub,ih]
      have hp0 : (0 : ℝ) < (N+1 : ℕ) := by positivity
      have hrpow : (((N+1 : ℕ) : ℝ)^(-ε))^2 = ((N+1 : ℕ) : ℝ)^(-2*ε) := by
        rw [← Real.rpow_mul_natCast hp0.le]
        congr 1
        norm_num
        ring
      rw [hrpow]
      simp only [pmPrimeMixedDensity,Nat.add_sub_cancel]
      ring
    · rw [pm_mobiusFinitePrimeAperture_succ,if_neg hp]
      exact ih

/-- Complete signed mixed current, retaining both signs. -/
def pmPrimeUpdateMixedCurrent (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ mobiusFinitePrimeAperture N, ∫ t in Ioi (1/(N : ℝ)), pmPrimeMixedDensity ε p t

/-- Positive part of the complete actual mixed current. -/
def pmPrimeUpdatePositiveMixedCurrent (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ mobiusFinitePrimeAperture N,
    ∫ t in Ioi (1/(N : ℝ)), max (pmPrimeMixedDensity ε p t) 0

/-- Energy of the actual full source above the physical reciprocal horizon. -/
def pmPowerDampedFermiTruncatedEnergy (ε : ℝ) (N : ℕ) : ℝ :=
  ∫ t in Ioi (1/(N : ℝ)), ‖pmPowerDampedFermiSource ε t‖^2

private theorem pmqb_cut_pos (N : ℕ) {t : ℝ} (ht : t ∈ Ioi (1/(N : ℝ))) : 0 < t :=
  (one_div_nonneg.mpr (Nat.cast_nonneg N)).trans_lt ht

private theorem pmqb_quadratic_integrable (ε : ℝ) {p : ℕ} (hp : 0 < p) :
    IntegrableOn (fun t =>
      ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (p-1)) ε ((p : ℝ)*t)‖^2)
        (Ioi (0 : ℝ)) := by
  let f := pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (p-1)) ε
  have hi : IntegrableOn (fun t => ‖f t‖^2) (Ioi (0 : ℝ)) :=
    (memLp_pmFinitePrimePowerDampedFermiSource _ _).norm.integrable_sq
  apply (integrableOn_Ioi_comp_mul_left_iff (fun t => ‖f t‖^2) 0
    (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
  simpa only [mul_zero] using hi

private theorem pmqb_core_eq_source (ε : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Ioi (1/(N : ℝ))) :
    pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε t =
      pmPowerDampedFermiSource ε t := by
  have ht0 := pmqb_cut_pos N ht
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hrec : 1/t ≤ (N : ℝ) := by
    apply (div_le_iff₀ ht0).mpr
    have hh := (div_lt_iff₀ hN0).mp ht
    nlinarith only [hh]
  have hfloor : ⌊1/t⌋₊ ≤ N := by
    have hh := (Nat.floor_le (by positivity : 0 ≤ 1/t)).trans hrec
    exact_mod_cast hh
  apply pmFinitePrimePowerDampedFermiSource_eq_of_covers
    (fun p hp => (Finset.mem_filter.mp hp).2) ε ht0
  intro p hp
  obtain ⟨hr,hprime⟩ := Finset.mem_filter.mp hp
  have hh := Finset.mem_range.mp hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hprime⟩

/-- The actual truncated source has finite energy for every finite horizon;
this does not assume admission on the entire half-line. -/
theorem integrableOn_pmPowerDampedFermiSource_truncated_sq (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun t => ‖pmPowerDampedFermiSource ε t‖^2) (Ioi (1/(N : ℝ))) := by
  have hi : IntegrableOn (fun t =>
      ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε t‖^2) (Ioi (0 : ℝ)) :=
    (memLp_pmFinitePrimePowerDampedFermiSource _ _).norm.integrable_sq
  apply (hi.mono_set (fun t ht => pmqb_cut_pos N ht)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [pmqb_core_eq_source ε hN ht]

/-- Exact complete prime-current balance at the physical horizon. -/
theorem pmPowerDampedFermiTruncatedEnergy_prime_balance (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    pmPowerDampedFermiTruncatedEnergy ε N =
      (∫ t in Ioi (1/(N : ℝ)), ‖fermiNymanGen 1 t‖^2)+
        pmPrimeUpdateQuadraticCurrent ε N-2*pmPrimeUpdateMixedCurrent ε N := by
  let Q := fun p : ℕ => fun t : ℝ => (p : ℝ)^(-2*ε)*
    ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (p-1)) ε ((p : ℝ)*t)‖^2
  have hQ (p : ℕ) (hp : p ∈ mobiusFinitePrimeAperture N) :
      IntegrableOn (Q p) (Ioi (1/(N : ℝ))) := by
    have hh : IntegrableOn (Q p) (Ioi (0 : ℝ)) :=
      (pmqb_quadratic_integrable ε (Finset.mem_filter.mp hp).2.pos).const_mul _
    exact hh.mono_set (fun t ht => pmqb_cut_pos N ht)
  have hM (p : ℕ) (hp : p ∈ mobiusFinitePrimeAperture N) :
      IntegrableOn (pmPrimeMixedDensity ε p) (Ioi (1/(N : ℝ))) :=
    (integrableOn_pmPrimeMixedDensity ε (Finset.mem_filter.mp hp).2.pos).mono_set
      (fun t ht => pmqb_cut_pos N ht)
  have hseed0 : IntegrableOn (fun t => ‖fermiNymanGen 1 t‖^2) (Ioi (0 : ℝ)) :=
    (memLp_pm_fermiNymanGen (by norm_num : (0 : ℝ) < 1)).norm.integrable_sq
  have hseed : IntegrableOn (fun t => ‖fermiNymanGen 1 t‖^2) (Ioi (1/(N : ℝ))) :=
    hseed0.mono_set (fun t ht => pmqb_cut_pos N ht)
  have hsum (p : ℕ) (hp : p ∈ mobiusFinitePrimeAperture N) :
      IntegrableOn (fun t => Q p t-2*pmPrimeMixedDensity ε p t) (Ioi (1/(N : ℝ))) :=
    (hQ p hp).sub ((hM p hp).const_mul 2)
  calc
    _ = ∫ t in Ioi (1/(N : ℝ)),
        ‖pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture N) ε t‖^2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [pmqb_core_eq_source ε hN ht]
    _ = ∫ t in Ioi (1/(N : ℝ)), (‖fermiNymanGen 1 t‖^2+
        ∑ p ∈ mobiusFinitePrimeAperture N,(Q p t-2*pmPrimeMixedDensity ε p t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact pmPrimeUpdate_pointwise_energy_balance ε N (pmqb_cut_pos N ht)
    _ = (∫ t in Ioi (1/(N : ℝ)), ‖fermiNymanGen 1 t‖^2)+
        ∑ p ∈ mobiusFinitePrimeAperture N,
          ((∫ t in Ioi (1/(N : ℝ)), Q p t)-2*∫ t in Ioi (1/(N : ℝ)), pmPrimeMixedDensity ε p t) := by
      rw [integral_add hseed (integrable_finsetSum _ hsum),integral_finsetSum _ hsum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [integral_sub (hQ p hp) ((hM p hp).const_mul 2)]
      simp only [integral_const_mul]
    _ = _ := by
      simp only [Q,integral_const_mul,Finset.sum_sub_distrib,← Finset.mul_sum,
        pmPrimeUpdateQuadraticCurrent,pmPrimeUpdateMixedCurrent]
      ring

/-- The positive and negative parts reconstruct the complete mixed current. -/
theorem pmPrimeUpdateMixedCurrent_eq_positive_sub_negative (ε : ℝ) (N : ℕ) :
    pmPrimeUpdateMixedCurrent ε N =
      pmPrimeUpdatePositiveMixedCurrent ε N-pmPrimeUpdateNegativeMixedCurrent ε N := by
  unfold pmPrimeUpdateMixedCurrent pmPrimeUpdatePositiveMixedCurrent pmPrimeUpdateNegativeMixedCurrent
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hi : Integrable (pmPrimeMixedDensity ε p) (volume.restrict (Ioi (1/(N : ℝ)))) :=
    (integrableOn_pmPrimeMixedDensity ε (Finset.mem_filter.mp hp).2.pos).mono_set
      (fun t ht => pmqb_cut_pos N ht)
  have hpos : Integrable (fun t => max (pmPrimeMixedDensity ε p t) 0)
      (volume.restrict (Ioi (1/(N : ℝ)))) := hi.sup (integrable_zero _ _ _)
  have hneg : Integrable (fun t => max (-pmPrimeMixedDensity ε p t) 0)
      (volume.restrict (Ioi (1/(N : ℝ)))) := hi.neg.sup (integrable_zero _ _ _)
  unfold pmPrimeNegativeMixedMass
  rw [← integral_sub hpos hneg]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases hh : 0 ≤ pmPrimeMixedDensity ε p t
  · rw [max_eq_left hh,max_eq_right (neg_nonpos.mpr hh),sub_zero]
  · have hh' := le_of_lt (lt_of_not_ge hh)
    rw [max_eq_right hh',max_eq_left (neg_nonneg.mpr hh'),zero_sub,neg_neg]

/-- Signed balance with both mixed-current parts explicitly retained. -/
theorem pmPowerDampedFermiTruncatedEnergy_signed_balance (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    pmPowerDampedFermiTruncatedEnergy ε N =
      (∫ t in Ioi (1/(N : ℝ)), ‖fermiNymanGen 1 t‖^2)+
        pmPrimeUpdateQuadraticCurrent ε N-
          2*(pmPrimeUpdatePositiveMixedCurrent ε N-pmPrimeUpdateNegativeMixedCurrent ε N) := by
  rw [pmPowerDampedFermiTruncatedEnergy_prime_balance ε hN,
    pmPrimeUpdateMixedCurrent_eq_positive_sub_negative]

end RHTower
