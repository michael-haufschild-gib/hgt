import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.BlockDeletion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.PrimeParityPartition

/-! # The meromorphic return determined by a projected heat trace -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ContinuousLinearMap HTGeometry
open _root_.RHTower.PrimeCoShift
local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Delete the range of the isometry inserting a whole block. -/
def blockDeletionProjection (a : ℕ+) : Gas →L[ℂ] Gas :=
  ContinuousLinearMap.id ℂ Gas - shiftObservable a a (ContinuousLinearMap.id ℂ Gas)

theorem blockDeletionProjection_basis (a n : ℕ+) :
    blockDeletionProjection a (lp.single 2 n (1:ℂ)) =
      if a ∣ n then 0 else (lp.single 2 n (1:ℂ) : Gas) := by
  have hV (v : Gas) : primeCoShift a (primeShift a v) = v := by
    apply lp.ext
    funext k
    exact _root_.RHTower.lpScalarInjection_coordinate _ (mulLeft_injective a) v k
  change (lp.single 2 n (1:ℂ) : Gas) - primeShift a (primeCoShift a (lp.single 2 n (1:ℂ))) = _
  by_cases hd : a ∣ n
  · obtain ⟨k,rfl⟩ := hd
    have hs : primeShift a (lp.single 2 k (1:ℂ)) = (lp.single 2 (a*k) 1 : Gas) :=
      _root_.RHTower.lpScalarInjection_single _ _ _ _
    rw [if_pos (dvd_mul_right _ _),← hs,hV,sub_self]
  · have hz : primeCoShift a (lp.single 2 n (1:ℂ)) = 0 := by
      apply lp.ext
      funext k
      have hn : a*k ≠ n := fun e => hd ⟨k,e.symm⟩
      simp only [primeCoShift_apply,lp.single_apply,Pi.single_eq_of_ne hn,lp.coeFn_zero,Pi.zero_apply]
    rw [if_neg hd,hz,map_zero,sub_zero]

/-- Continuation of the projected trace from complex trace-class temperatures. -/
def deletedPartition (a : ℕ+) (s : ℂ) := (1 - heat s a) * riemannZeta s

theorem deletedPartition_trace (a : ℕ+) (s : {z : ℂ // 1 < z.re}) :
    opTrace (blockDeletionProjection a ∘L gibbsOperator s) = deletedPartition a s.val := by
  let I := ContinuousLinearMap.id ℂ Gas
  have hT := hsTraceIdeal_comp_left (gibbs_mem_traceIdeal s) (shiftObservable a a I)
  rw [blockDeletionProjection,sub_comp,id_comp,opTrace_sub_of_mem (gibbs_mem_traceIdeal s) hT,
    diagonal_shift_trace,id_comp,partition_eq_zeta,deletedPartition]
  ring

/-- Meromorphic reciprocal of the block-deleted trace. -/
def continuedClockReturn (p : Nat.Primes) (D : ℕ+) : ℂ → ℂ :=
  (deletedPartition (primeRayLabel p D.val))⁻¹

theorem continuedClockReturn_real (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    continuedClockReturn p D (β.val:ℂ) = (gibbsClockReturn χ β p D:ℂ) := by
  have hz : ((riemannZeta β.val).re:ℂ) = riemannZeta β.val := by rw [← thermalWeight_partition]; rfl
  have hh : heat (β.val:ℂ) (primeRayLabel p D.val) = (gibbsBlockRatio β p D:ℂ) := by
    simp only [heat,energy_primeRayLabel,gibbsBlockRatio,Complex.ofReal_exp,Complex.ofReal_mul,
      Complex.ofReal_neg]
  change ((1-heat (β.val:ℂ) (primeRayLabel p D.val))*riemannZeta β.val)⁻¹ = _
  rw [gibbsClockReturn_eq,Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one,hz,hh]
  simp only [mul_inv_rev,div_eq_mul_inv,mul_comm]

theorem clockFactor_analytic (a : ℕ+) (s : ℂ) : AnalyticAt ℂ (fun z => 1-heat z a) s :=
  analyticAt_const.sub ((analyticAt_id.neg.mul analyticAt_const).cexp)

theorem clockFactor_ne_zero (p : Nat.Primes) (D : ℕ+) {s : ℂ} (hs : 0 < s.re) :
    1-heat s (primeRayLabel p D.val) ≠ 0 := by
  have ha : 0 < energy (primeRayLabel p D.val) := Real.log_pos (by exact_mod_cast clockBlock_gt_one p D)
  have h : ‖heat s (primeRayLabel p D.val)‖ < 1 := by
    rw [norm_heat,Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) ha
  intro he
  have h₁ := (sub_eq_zero.mp he).symm
  rw [h₁,norm_one] at h
  exact h.false

theorem continuedClockReturn_meromorphic (p : Nat.Primes) (D : ℕ+) (s : ℂ) :
    MeromorphicAt (continuedClockReturn p D) s :=
  (((clockFactor_analytic (primeRayLabel p D.val) s).meromorphicAt).mul
    (ZeroForcingCalculus.meromorphicAt_riemannZeta s)).inv

/-- Globally meromorphic extensions of the real probability curve have the same punctured germ everywhere. -/
theorem continuedClockReturn_unique (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) {F : ℂ → ℂ}
    (hF : Meromorphic F) (hR : ∀ β : TraceTemperature, F β.val = (gibbsClockReturn χ β p D:ℂ)) (s : ℂ) :
    F =ᶠ[𝓝[≠] s] continuedClockReturn p D := by
  let G := F - continuedClockReturn p D
  have hm (z : ℂ) : MeromorphicAt G z := (hF z).sub (continuedClockReturn_meromorphic p D z)
  have ht : meromorphicOrderAt G 1 = ⊤ := by
    by_contra hn
    obtain ⟨β,hβ⟩ := (tendsto_temperature_punctured.eventually
      ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm 1)).mp hn)).exists
    exact hβ (sub_eq_zero.mpr ((hR β).trans (continuedClockReturn_real χ β p D).symm))
  have hs : meromorphicOrderAt G s = ⊤ := by
    by_contra hn
    have hu : MeromorphicOn G Set.univ := fun z _ => hm z
    exact (hu.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ s) (Set.mem_univ 1) hn) ht
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hs] with z hz
  exact sub_eq_zero.mp hz

/-- In the entire right half-plane the returned germ reverses the full zeta divisor. -/
theorem continuedClockReturn_order (p : Nat.Primes) (D : ℕ+) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (continuedClockReturn p D) s = -meromorphicOrderAt riemannZeta s := by
  rw [continuedClockReturn,meromorphicOrderAt_inv]
  change -meromorphicOrderAt ((fun z => 1-heat z (primeRayLabel p D.val)) * riemannZeta) s = _
  rw [meromorphicOrderAt_mul_of_ne_zero (clockFactor_analytic _ _) (clockFactor_ne_zero p D hs)]

#print axioms blockDeletionProjection_basis
#print axioms deletedPartition_trace
#print axioms continuedClockReturn_real
#print axioms clockFactor_analytic
#print axioms clockFactor_ne_zero
#print axioms continuedClockReturn_meromorphic
#print axioms continuedClockReturn_unique
#print axioms continuedClockReturn_order

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
