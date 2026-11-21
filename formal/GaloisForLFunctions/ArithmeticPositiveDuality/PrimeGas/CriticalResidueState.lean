import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ThermalPhaseAttainment
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Cyclic-order measurements at the partition pole

Reading a shell modulo a fixed positive integer inserts a periodic multiplier
in the Gibbs trace. At the pole every periodic readout tends to its uniform
mean. For each nonvacuum shell, agreement of a single limiting order
probability with its Born weight detects the isometry line.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Set Topology
open GaloisForLFunctions.HTGeometry

private theorem periodic_half_summable (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (s : {z : ℂ // 1 < z.re}) :
    Summable (fun n : ℕ+ => ‖F (n : ℕ) * heat (s.val / 2) n‖ ^ 2) := by
  let C := ∑ j, ‖F j‖
  have hF (j : ZMod (m : ℕ)) : ‖F j‖ ≤ C :=
    Finset.single_le_sum (fun i _ => norm_nonneg (F i)) (Finset.mem_univ j)
  have hs := (summable_heat_sq_iff (s.val / 2)).2
    (by rw [Complex.div_ofNat_re]; linarith [s.property])
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hs.mul_left (C^2))
  intro n
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF _) 2) (sq_nonneg _)

/-- Gibbs propagation with a complex observable of the shell residue inserted. -/
def periodicGibbsOperator (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (s : {z : ℂ // 1 < z.re}) :
    Gas →L[ℂ] Gas :=
  HilbertSchmidt.diagOp (fun n : ℕ+ => F (n : ℕ) * heat (s.val / 2) n)
    (periodic_half_summable m F s) ∘L
  HilbertSchmidt.diagOp (heat (s.val / 2)) ((summable_heat_sq_iff _).2
    (by rw [Complex.div_ofNat_re]; linarith [s.property]))

theorem periodicGibbsOperator_apply (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (s : {z : ℂ // 1 < z.re}) (f : Gas) (n : ℕ+) :
    periodicGibbsOperator m F s f n = F (n : ℕ) * heat s.val n * f n := by
  simp only [periodicGibbsOperator, ContinuousLinearMap.comp_apply, HilbertSchmidt.diagOp_apply,
    ← mul_assoc, mul_assoc (F _) (heat _ _) (heat _ _), ← heat_add, add_halves]

theorem periodicGibbs_trace_series (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (s : {z : ℂ // 1 < z.re}) :
    ContinuousLinearMap.opTrace (periodicGibbsOperator m F s) =
      ∑' n : ℕ+, F (n : ℕ) * heat s.val n := by
  rw [periodicGibbsOperator, HilbertSchmidt.opTrace_diagOp_comp]
  exact tsum_congr fun n => by rw [mul_assoc, ← heat_add, add_halves]

/-- The continued periodic trace is the congruence L-function of the readout. -/
theorem periodicGibbs_trace (m : ℕ+) (F : ZMod (m : ℕ) → ℂ)
    (s : {z : ℂ // 1 < z.re}) :
    ContinuousLinearMap.opTrace (periodicGibbsOperator m F s) = ZMod.LFunction F s.val := by
  rw [periodicGibbs_trace_series, ZMod.LFunction_eq_LSeries F s.property, LSeries]
  have hs : Function.support (LSeries.term (fun k : ℕ => F k) s.val) ⊆
      Set.range ((↑) : ℕ+ → ℕ) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · exact (hk (LSeries.term_zero ..)).elim
    · exact ⟨⟨k,hk'⟩,rfl⟩
  rw [← PNat.coe_injective.tsum_eq hs]
  exact tsum_congr fun n => by rw [LSeries.term_of_ne_zero n.ne_zero, heat_eq_cpow,
    Complex.cpow_neg, div_eq_mul_inv]

/-- Approach the trace boundary through real trace-class temperatures. -/
def atPartitionPole : Filter TraceTemperature :=
  comap Subtype.val (𝓝[>] (1 : ℝ))

instance : NeBot atPartitionPole := by
  change NeBot (comap ((↑) : TraceTemperature → ℝ) (𝓝[>] (1 : ℝ)))
  rw [comap_neBot_iff_frequently]
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), 1 < x := self_mem_nhdsWithin
  exact hpos.frequently.mono
    (fun x hx => ⟨⟨x,hx⟩,rfl⟩)

theorem tendsto_temperature_punctured :
    Tendsto (fun β : TraceTemperature => (β.val : ℂ)) atPartitionPole (𝓝[≠] 1) := by
  have hr : Tendsto ((↑) : TraceTemperature → ℝ) atPartitionPole (𝓝 (1 : ℝ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun β h => ?_⟩
  · simpa only [Complex.ofReal_one, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 1).comp hr
  · change (β.val : ℂ) = 1 at h
    exact β.property.ne' (by exact_mod_cast h)

/-- Normalized operator trace of a periodic measurement at a real temperature. -/
def periodicGibbsMean (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) (β : TraceTemperature) : ℂ :=
  let s : {z : ℂ // 1 < z.re} := ⟨(β.val : ℂ), β.property⟩
  ContinuousLinearMap.opTrace (periodicGibbsOperator m F s) /
    ContinuousLinearMap.opTrace (gibbsOperator s)

/-- Every finite periodic measurement has the uniform mean in the boundary state. -/
theorem periodicGibbsMean_limit (m : ℕ+) (F : ZMod (m : ℕ) → ℂ) :
    Tendsto (periodicGibbsMean m F) atPartitionPole (𝓝 ((∑ j, F j) / (m : ℕ))) := by
  have h := ((ZMod.LFunction_residue_one F).div riemannZeta_residue_one one_ne_zero).comp
    tendsto_temperature_punctured
  rw [div_one, ← Finset.sum_div] at h
  apply h.congr'
  filter_upwards with β
  change ((β.val : ℂ) - 1) * ZMod.LFunction F β.val / (((β.val : ℂ) - 1) * riemannZeta β.val) =
    periodicGibbsMean m F β
  have hb : (β.val : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast β.property.ne')
  rw [mul_div_mul_left _ _ hb, periodicGibbsMean, periodicGibbs_trace, partition_eq_zeta]

/-- Probability of reading a residue in A. -/
def residueProbability (m : ℕ+) (A : Finset (ZMod (m : ℕ))) (β : TraceTemperature) : ℝ :=
  (periodicGibbsMean m (fun j => if j ∈ A then 1 else 0) β).re

theorem residueProbability_limit (m : ℕ+) (A : Finset (ZMod (m : ℕ))) :
    Tendsto (residueProbability m A) atPartitionPole (𝓝 ((A.card : ℝ) / (m : ℕ))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (periodicGibbsMean_limit m (fun j => if j ∈ A then 1 else 0))
  have hsum : (∑ j : ZMod (m : ℕ), if j ∈ A then (1 : ℂ) else 0) = A.card := by
    rw [Finset.sum_boole]
    simp
  rw [hsum, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div] at h
  exact h

/-- Measuring order a on a shell of size ab gives φ(a)/(ab) at the boundary. -/
def orderProbability (a b : ℕ+) := residueProbability (a*b)
  (Finset.univ.filter (fun j : ZMod ((a*b : ℕ+) : ℕ) => addOrderOf j = (a : ℕ)))

theorem orderProbability_limit (a b : ℕ+) :
    Tendsto (orderProbability a b) atPartitionPole
      (𝓝 (((a : ℕ).totient : ℝ) / ((a*b : ℕ+) : ℕ))) := by
  have h := residueProbability_limit (a*b)
    (Finset.univ.filter (fun j : ZMod ((a*b : ℕ+) : ℕ) => addOrderOf j = (a : ℕ)))
  rwa [channel_order_count] at h

private theorem shellMass_one_iff (s : ℂ) (n : ℕ+) :
    shellMass s n = 1 ↔ n = 1 ∨ s.re = 1/2 := by
  by_cases hn : n = 1
  · simp [hn, shellMass, energy]
  rw [or_iff_right hn, shellMass, Real.exp_eq_one_iff]
  have hlt : 1 < n := lt_of_le_of_ne (show 1 ≤ n from one_le) (Ne.symm hn)
  have hE : energy n ≠ 0 := (Real.log_pos (by exact_mod_cast hlt : (1 : ℝ) < (n : ℕ))).ne'
  rw [mul_eq_zero, or_iff_left hE]
  constructor <;> intro h <;> linarith

/-- Each individual order class of every nonvacuum shell tests the critical line. -/
theorem orderProbability_born_iff (s : ℂ) (a b : ℕ+) :
    Tendsto (orderProbability a b) atPartitionPole (𝓝 (‖channel s (a*b) a‖^2)) ↔
      a*b = 1 ∨ s.re = 1/2 := by
  have hprob := orderProbability_limit a b
  have hlim : Tendsto (orderProbability a b) atPartitionPole (𝓝 (‖channel s (a*b) a‖^2)) ↔
      ‖channel s (a*b) a‖^2 = ((a : ℕ).totient : ℝ) / ((a*b : ℕ+) : ℕ) :=
    ⟨fun h => tendsto_nhds_unique h hprob, fun h => h ▸ hprob⟩
  have hn : (((a*b : ℕ+) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (a*b).ne_zero
  have hc : ((a : ℕ).totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr a.pos).ne'
  rw [hlim, channel_norm_sq, eq_div_iff hn, mul_assoc,
    mul_comm (‖heat s (a*b)‖ ^ 2), ← shellMass_eq, ← shellMass_one_iff]
  exact ⟨fun h => mul_left_cancel₀ hc (h.trans (mul_one _).symm), fun h => by rw [h, mul_one]⟩

/-- Consistency of the limiting Gibbs measurements with all order channels
is equivalent to the isometry of the full two-copy quantum map. -/
theorem pole_measurements_iff_split_isometry (s : ℂ) :
    (∀ a b : ℕ+, Tendsto (orderProbability a b) atPartitionPole (𝓝 (‖channel s (a*b) a‖^2))) ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff]
  constructor
  · intro h
    have hne : (1 : ℕ+) * 2 ≠ 1 := by
      rw [one_mul]
      exact fun he => Nat.succ_ne_self 1 (congrArg PNat.val he)
    exact ((orderProbability_born_iff s 1 2).mp (h 1 2)).resolve_left hne
  · intro h a b
    exact (orderProbability_born_iff s a b).mpr (Or.inr h)

#print axioms periodicGibbsOperator_apply
#print axioms periodicGibbs_trace
#print axioms periodicGibbsMean_limit
#print axioms residueProbability_limit
#print axioms orderProbability_limit
#print axioms orderProbability_born_iff
#print axioms pole_measurements_iff_split_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
