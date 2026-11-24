import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BoundaryLoss.RadialEstimate
import Mathlib.Analysis.Meromorphic.Order

/-! # Counting the nonresonant modes bounds the multiplicity of every boundary zero -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology InverseSpectrum.ShellMixing
open _root_.RHTower.PrimeCoShift

private theorem radialFactor_analytic (p : Nat.Primes) (z : ℂ) :
    AnalyticAt ℂ (fun w => heat (w-z) (primePNat p)-1) z :=
  (((analyticAt_id.sub analyticAt_const).neg.mul analyticAt_const).cexp).sub analyticAt_const

private theorem radialFactor_order (p : Nat.Primes) (z : ℂ) :
    meromorphicOrderAt (fun w => heat (w-z) (primePNat p)-1) z = 1 := by
  have ha := radialFactor_analytic p z
  have hd := ((Complex.hasDerivAt_exp _).comp z (((hasDerivAt_id z).sub_const z).neg.mul_const
    (energy (primePNat p):ℂ))).sub_const 1
  have hd' : HasDerivAt (fun w => heat (w-z) (primePNat p)-1) (-(energy (primePNat p):ℂ)) z := by
    simpa [heat,Function.comp_def] using hd
  rw [ha.meromorphicOrderAt_eq,ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp [heat])
    (hd'.deriv ▸ neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (prime_energy_pos p).ne'))]
  rfl

theorem radialProduct_order (Q : Finset Nat.Primes) (z : ℂ) :
    meromorphicOrderAt (radialProduct Q z) z = (Q.card : WithTop ℤ) := by
  unfold radialProduct
  rw [meromorphicOrderAt_fun_prod (fun p _ => (radialFactor_analytic p z).meromorphicAt)]
  simp only [radialFactor_order,Finset.sum_const,nsmul_one]

private theorem right_radius (z : ℂ) :
    Tendsto (fun x : ℝ => z+(x:ℂ)) (𝓝[>] 0) (𝓝[≠] z) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have ht := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa only [Complex.ofReal_zero,add_zero] using (tendsto_const_nhds (x := z)).add ht
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    exact fun h => hx.ne' (Complex.ofReal_eq_zero.mp (add_eq_left.mp h))

/-- The exact trace loses at most one order per prime whose phase differs from the vacuum. -/
theorem finite_trace_order_le_nonresonant {ι κ : Type*} [Fintype ι] (P : Finset Nat.Primes)
    {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers (primeWindow P)) {z : ℂ} (hz : z.re = 0) :
    meromorphicOrderAt (finiteHeatTrace a) z ≤ ((nonresonantModes P z).card : WithTop ℤ) := by
  let Q := nonresonantModes P z
  let G := radialProduct Q z
  have hF : AnalyticAt ℂ (finiteHeatTrace a) z :=
    Finset.analyticAt_fun_sum _ (fun _ _ => (analyticAt_id.neg.mul analyticAt_const).cexp)
  have hG : AnalyticAt ℂ G z :=
    Finset.analyticAt_fun_prod _ (fun p _ => radialFactor_analytic p z)
  by_contra! hgt
  have ho : 0 < meromorphicOrderAt (finiteHeatTrace a / G) z := by
    rw [meromorphicOrderAt_div hF.meromorphicAt hG.meromorphicAt,show meromorphicOrderAt G z = _ from radialProduct_order Q z]
    change (Q.card : WithTop ℤ) < _ at hgt
    by_cases ht : meromorphicOrderAt (finiteHeatTrace a) z = ⊤
    · simp [ht,sub_eq_add_neg]
    lift meromorphicOrderAt (finiteHeatTrace a) z to ℤ using ht with k
    have hk : (Q.card : ℤ) < k := by exact_mod_cast hgt
    exact_mod_cast (sub_pos.mpr hk)
  have hl := ((tendsto_zero_of_meromorphicOrderAt_pos ho).comp (right_radius z)).norm
  have hb : ∀ᶠ x : ℝ in 𝓝[>] 0, (1:ℝ)/2^Q.card ≤ ‖((finiteHeatTrace a / G) (z+(x:ℂ)))‖ := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [Pi.div_apply,norm_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr (radialProduct_ne_zero Q z hx))).mpr
    rw [one_div,inv_mul_eq_div]
    exact radial_trace_bound P h ha hz hx
  have hc := ge_of_tendsto hl hb
  rw [norm_zero] at hc
  exact (not_le_of_gt (by positivity : (0:ℝ) < 1/2^Q.card)) hc

/-- The prime species actually occurring in a finite spectrum. -/
def spectrumPrimes {ι : Type*} [Fintype ι] (a : ι → ℕ+) : Finset Nat.Primes :=
  (Finset.univ.biUnion (fun i => (a i).val.primeFactors)).subtype Nat.Prime

theorem spectrumPrimes_support {ι : Type*} [Fintype ι] (a : ι → ℕ+) (i : ι) :
    (a i).val ∈ Nat.factoredNumbers (primeWindow (spectrumPrimes a)) := by
  apply Nat.mem_factoredNumbers_of_primeFactors_subset (a i).ne_zero
  intro p hp
  let q : Nat.Primes := ⟨p,Nat.prime_of_mem_primeFactors hp⟩
  apply Finset.mem_map.mpr
  refine ⟨q,?_,rfl⟩
  exact Finset.mem_subtype.mpr (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hp⟩)

/-- Intrinsic multiplicity bound, using only the labels and the temperature. -/
theorem finite_trace_order_bound {ι κ : Type*} [Fintype ι] {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) {z : ℂ} (hz : z.re = 0) :
    meromorphicOrderAt (finiteHeatTrace a) z ≤ ((nonresonantModes (spectrumPrimes a) z).card : WithTop ℤ) :=
  finite_trace_order_le_nonresonant _ h (spectrumPrimes_support a) hz

#print axioms spectrumPrimes_support
#print axioms finite_trace_order_bound
#print axioms radialProduct_order
#print axioms finite_trace_order_le_nonresonant

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
