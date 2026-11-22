import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ThermalPhaseAttainment
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleWeights

/-!
# A single trace and conservation determine the shell energies

Cyclic-order resolution fixes all shell energies up to a common scale.
A single zeta trace fixes that scale by strict comparison at shell two.
The input spectrum can be any real function on the positive integers.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum

/-- Total probability of all cyclic-order outcomes on each shell. -/
def Conserves (E : ℕ+ → ℝ) (s : ℂ) : Prop :=
  ∀ n : ℕ+, ∑ d ∈ n.val.divisors, (d.totient:ℝ)*‖Complex.exp (-s*(E n:ℂ))‖^2 = 1

/-- A trace measurement includes convergence of the Gibbs series. -/
def ZetaReading (β : TraceTemperature) (E : ℕ+ → ℝ) : Prop :=
  HasSum (fun n => Real.exp (-β.val*E n)) (riemannZeta β.val).re

/-- Conservation measures the product of real temperature and each unknown energy. -/
theorem conserves_iff (E : ℕ+ → ℝ) (s : ℂ) :
    Conserves E s ↔ ∀ n, 2*s.re*E n = energy n := by
  have mass (n : ℕ+) :
      ∑ d ∈ n.val.divisors, (d.totient:ℝ)*‖Complex.exp (-s*(E n:ℂ))‖^2 =
        Real.exp (energy n-2*s.re*E n) := by
    rw [← Finset.sum_mul,← Nat.cast_sum,Nat.sum_totient,Complex.norm_exp,Complex.mul_re,Complex.neg_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,sq,← Real.exp_add]
    have hn : Real.exp (energy n) = (n.val:ℝ) := Real.exp_log (by exact_mod_cast n.pos)
    rw [← hn,← Real.exp_add]
    congr 1
    ring
  unfold Conserves
  simp_rw [mass,Real.exp_eq_one_iff,sub_eq_zero]
  exact forall_congr' fun _ => eq_comm

private def weight (β : TraceTemperature) (c : ℝ) (n : ℕ+) := Real.exp (-β.val*c*energy n)

private theorem canonical_reading (β : TraceTemperature) : ZetaReading β energy := by
  have he := congrArg Complex.re (thermalWeight_partition β)
  change (∑' n, thermalWeight β n) = (riemannZeta β.val).re at he
  rw [ZetaReading,← he]
  exact (thermalWeight_summable β).hasSum

private theorem compare_scales {β : TraceTemperature} {a b L : ℝ} (hab : a < b)
    (ha : HasSum (weight β a) L) (hb : HasSum (weight β b) L) : False := by
  have hβ : -β.val < 0 := neg_neg_of_pos (zero_lt_one.trans β.property)
  have hcoef := mul_lt_mul_of_neg_left hab hβ
  have hall (n : ℕ+) : weight β b n ≤ weight β a n := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hcoef.le (Real.log_nonneg (by exact_mod_cast n.pos))
  have h₂ : weight β b 2 < weight β a 2 := by
    apply Real.exp_lt_exp.mpr
    exact mul_lt_mul_of_pos_right hcoef (Real.log_pos (by norm_num : 1 < ((2:ℕ+).val:ℝ)))
  have h := Summable.tsum_lt_tsum hall h₂ hb.summable ha.summable
  rw [hb.tsum_eq,ha.tsum_eq] at h
  exact h.false

/-- Without any additivity or positivity assumption on the energies, one trace and conservation
recover the logarithmic Hamiltonian and select the critical line. -/
theorem energy_and_temperature_iff (β : TraceTemperature) (E : ℕ+ → ℝ) (s : ℂ) :
    Conserves E s ∧ ZetaReading β E ↔ E = energy ∧ s.re = 1/2 := by
  constructor
  · rintro ⟨h,hZ⟩
    have H := (conserves_iff E s).mp h
    have hn : 2*s.re ≠ 0 := by
      intro hz
      have h₂ := H 2
      rw [hz,zero_mul] at h₂
      exact (Real.log_pos (by norm_num : 1 < ((2:ℕ+).val:ℝ))).ne' h₂.symm
    let c := (2*s.re)⁻¹
    have hE (n : ℕ+) : E n = c*energy n := by
      rw [← H n,← mul_assoc]
      change E n = ((2*s.re)⁻¹*(2*s.re))*E n
      rw [inv_mul_cancel₀ hn,one_mul]
    have hmeas : HasSum (weight β c) (riemannZeta β.val).re := by
      have heq (n : ℕ+) : weight β c n = Real.exp (-β.val*E n) := by
        rw [weight,hE,mul_assoc]
      rw [funext heq]
      exact hZ
    have hcan : HasSum (weight β 1) (riemannZeta β.val).re := by
      change HasSum (fun n : ℕ+ => Real.exp (-β.val*1*energy n)) _
      rw [mul_one]
      exact canonical_reading β
    have hc : c = 1 := by
      rcases lt_trichotomy c 1 with hc|hc|hc
      · exact (compare_scales hc hmeas hcan).elim
      · exact hc
      · exact (compare_scales hc hcan hmeas).elim
    have htemp : 2*s.re*c = 1 := mul_inv_cancel₀ hn
    rw [hc,mul_one] at htemp
    exact ⟨funext fun n => by rw [hE,hc,one_mul],by linarith only [htemp]⟩
  · rintro ⟨rfl,hs⟩
    refine ⟨(conserves_iff energy s).mpr (fun n => ?_),canonical_reading β⟩
    rw [hs]
    ring

/-- The cyclic-order split with an arbitrary heat multiplier on its input shell. -/
def wave (E : ℕ+ → ℝ) (s : ℂ) (f : ℕ+ → ℂ) (x : ℕ+ × ℕ+) : ℂ :=
  (Real.sqrt x.1.val.totient:ℂ)*Complex.exp (-s*(E (x.1*x.2):ℂ))*f (x.1*x.2)

def Isometric (E : ℕ+ → ℝ) (s : ℂ) : Prop :=
  ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = wave E s f x

private theorem bare_wave (E : ℕ+ → ℝ) (s : ℂ) (f : ℕ+ → ℂ) :
    wave E s f = split 0 (fun n => Complex.exp (-s*(E n:ℂ))*f n) := by
  funext x
  simp only [wave,split,channel,heat,neg_zero,zero_mul,Complex.exp_zero,mul_one,mul_assoc]

private theorem conserves_of_isometry {E : ℕ+ → ℝ} {s : ℂ} (h : Isometric E s) : Conserves E s := by
  obtain ⟨T,hT⟩ := h
  intro n
  let v : Gas := lp.single 2 n (1:ℂ)
  have hh : HasSum (fun x => ‖wave E s v x‖^2) (‖v‖^2) := by
    simp_rw [← hT]
    rw [← T.norm_map v,HTGeometry.lp_norm_sq_eq_tsum]
    exact (HTGeometry.lp_summable_norm_sq (T v)).hasSum
  rw [bare_wave] at hh
  have H := ((split_hasSum_iff _ _ _).mp hh).tsum_eq
  rw [tsum_eq_single n] at H
  · rw [← Finset.sum_mul,← Nat.cast_sum,Nat.sum_totient]
    simpa [v,lp.norm_single,lp.single_apply,shellMass_eq,heat] using H
  · intro k hk
    simp [v,lp.single_apply,Pi.single_eq_of_ne hk]

/-- A full Hilbert-space isometry and one trace reading identify the Hamiltonian and temperature. -/
theorem isometry_and_trace_iff (β : TraceTemperature) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ ZetaReading β E ↔ E = energy ∧ s.re = 1/2 := by
  constructor
  · rintro ⟨hi,hZ⟩
    exact (energy_and_temperature_iff β E s).mp ⟨conserves_of_isometry hi,hZ⟩
  · rintro ⟨rfl,hs⟩
    exact ⟨(split_isometric_iff s).mpr hs,canonical_reading β⟩

/-- One real zeta reading and an isometry determine the partition function on the full trace half-plane. -/
theorem one_trace_iff_all (β : TraceTemperature) (E : ℕ+ → ℝ) (s : ℂ) :
    Isometric E s ∧ ZetaReading β E ↔ Isometric E s ∧
      ∀ z : {w : ℂ // 1 < w.re}, HasSum (fun n => Complex.exp (-z.val*(E n:ℂ))) (riemannZeta z.val) := by
  constructor
  · intro h
    obtain ⟨rfl,_⟩ := (isometry_and_trace_iff β E s).mp h
    exact ⟨h.1,CopyExchange.heat_hasSum⟩
  · rintro ⟨hi,h⟩
    refine ⟨hi,?_⟩
    have hr := Complex.hasSum_re (h ⟨(β.val:ℂ),β.property⟩)
    change HasSum (fun n => (Complex.exp (-(β.val:ℂ)*(E n:ℂ))).re) (riemannZeta β.val).re at hr
    unfold ZetaReading
    simpa only [← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp,Complex.ofReal_re] using hr

#print axioms isometry_and_trace_iff

#print axioms conserves_iff
#print axioms energy_and_temperature_iff
#print axioms one_trace_iff_all

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum
