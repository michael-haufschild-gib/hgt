import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.ExactFactors
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.CycleWeights
import GaloisForLFunctions.ZeroForcingCalculus.WittMonomialsShiftedConvolutionsAndBrauerCancellation
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # The complement of a finite-prime subsystem retains the zeta divisor -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ZeroForcingCalculus

variable {ι κ : Type*}

/-- Thermal sum over the actual subsystem states. -/
def subsystemTrace (a : ι → ℕ+) (s : ℂ) := ∑' i, heat s (a i)

/-- Exact independent composition gives the full trace in the Gibbs half-plane. -/
theorem exactSubsystem_product {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    {s : ℂ} (hs : 1 < s.re) : subsystemTrace a s * subsystemTrace b s = riemannZeta s := by
  let e := Equiv.ofBijective (fun u : ι × κ => a u.1 * b u.2) h
  have hz := (e.hasSum_iff (f := heat s)).mpr (CopyExchange.heat_hasSum ⟨s,hs⟩)
  have ht : HasSum (fun u : ι × κ => heat s (a u.1) * heat s (b u.2)) (riemannZeta s) :=
    hz.congr_fun (fun u => (heat_mul s _ _).symm)
  rw [← ht.tsum_eq,ht.summable.tsum_prod]
  simp only [subsystemTrace,tsum_mul_left,tsum_mul_right]

/-- Divide the measured partition by the trace of the extracted subsystem. -/
def complementPartition (a : ι → ℕ+) : ℂ → ℂ := riemannZeta / subsystemTrace a

private theorem subsystem_heat_analytic (n : ℕ+) (s : ℂ) : AnalyticAt ℂ (fun z => heat z n) s :=
  (analyticAt_id.neg.mul analyticAt_const).cexp

/-- Uniform domination by the real weights at any smaller positive abscissa. -/
theorem exactWindow_analytic (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ (windowTrace P a) s := by
  obtain ⟨t,ht,hts⟩ := exists_between hs
  have hsum := (exactWindow_absolute P hP h (s := (t:ℂ)) ht).1
  have hU : IsOpen {z : ℂ | t < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (windowTrace P a) {z : ℂ | t < z.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun i z _ => (subsystem_heat_analytic (a i.val) z).differentiableAt.differentiableWithinAt) hU ?_
    intro i z (hz : t < z.re)
    rw [norm_heat,norm_heat,Complex.ofReal_re]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hz.le)
      (Real.log_nonneg (by exact_mod_cast (a i.val).pos)))
  exact hd.analyticOnNhd hU s hts

/-- In the trace-class half-plane the quotient is the sum over complementary states. -/
theorem complementPartition_trace {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b)
    {s : ℂ} (hs : 1 < s.re) : complementPartition a s = subsystemTrace b s := by
  have hm := exactSubsystem_product h hs
  have hn := (mul_ne_zero_iff.mp (hm.trans_ne (riemannZeta_ne_zero_of_one_lt_re hs))).1
  rw [complementPartition,Pi.div_apply,← hm,mul_div_cancel_left₀ _ hn]

private theorem window_all_eq (P : Finset ℕ) {a : ι → ℕ+} (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers P) :
    windowTrace P a = subsystemTrace a := by
  funext z
  exact (Equiv.subtypeUnivEquiv ha).tsum_eq (fun i => heat z (a i))

/-- A subsystem using finitely many primes is a holomorphic unit on the right half-plane. -/
theorem finitePrimeSubsystem_unit (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers P) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (subsystemTrace a) s ∧ subsystemTrace a s ≠ 0 := by
  rw [← window_all_eq P ha]
  exact ⟨exactWindow_analytic P hP h hs,(exactWindow_zero_free P hP h hs).1⟩

/-- Every zero and the pole at one survive deletion of an exact finite-prime factor with their full orders. -/
theorem finitePrimeComplement_divisor (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers P) {s : ℂ} (hs : 0 < s.re) :
    MeromorphicAt (complementPartition a) s ∧
      meromorphicOrderAt (complementPartition a) s = meromorphicOrderAt riemannZeta s := by
  obtain ⟨han,hn⟩ := finitePrimeSubsystem_unit P hP h ha hs
  exact ⟨(meromorphicAt_riemannZeta s).div han.meromorphicAt,by
    rw [complementPartition,meromorphicOrderAt_div (meromorphicAt_riemannZeta s) han.meromorphicAt,
      meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero han hn,sub_zero]⟩

/-- The trace on its convergence half-plane fixes the punctured complementary germ everywhere
in the right half-plane for every finite-prime extraction. -/
theorem finitePrimeComplement_unique (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (ha : ∀ i, (a i).val ∈ Nat.factoredNumbers P) {F : ℂ → ℂ}
    (hF : MeromorphicOn F {z : ℂ | 0 < z.re}) (hG : ∀ z : ℂ, 1 < z.re → F z = subsystemTrace b z)
    {s : ℂ} (hs : 0 < s.re) : F =ᶠ[𝓝[≠] s] complementPartition a := by
  let U := {z : ℂ | 0 < z.re}
  have hm : MeromorphicOn (F - complementPartition a) U :=
    hF.sub fun z hz => (finitePrimeComplement_divisor P hP h ha hz).1
  have ht : meromorphicOrderAt (F - complementPartition a) (2:ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    have hnb : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by change (1:ℝ)<2; norm_num)
    filter_upwards [nhdsWithin_le_nhds hnb] with z hz
    exact sub_eq_zero.mpr ((hG z hz).trans (complementPartition_trace h hz).symm)
  have hs' : meromorphicOrderAt (F - complementPartition a) s = ⊤ := by
    by_contra hn
    exact (hm.meromorphicOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt 0).isPreconnected
      hs (show (2:ℂ) ∈ U by change (0:ℝ)<2; norm_num) hn) ht
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hs'] with z hz
  exact sub_eq_zero.mp hz

/-- For a finite-state factor, the complementary trace extends meromorphically to the whole plane. -/
theorem finiteStateComplement_meromorphic [Fintype ι] (a : ι → ℕ+) : Meromorphic (complementPartition a) := by
  intro s
  have he : subsystemTrace a = fun z => ∑ i, heat z (a i) := funext fun _ => tsum_fintype _
  have ha : AnalyticAt ℂ (subsystemTrace a) s := by
    rw [he]
    exact Finset.analyticAt_fun_sum _ (fun i _ => subsystem_heat_analytic (a i) s)
  exact (meromorphicAt_riemannZeta s).div ha.meromorphicAt

#print axioms exactSubsystem_product
#print axioms exactWindow_analytic
#print axioms complementPartition_trace
#print axioms finitePrimeSubsystem_unit
#print axioms finitePrimeComplement_divisor
#print axioms finitePrimeComplement_unique
#print axioms finiteStateComplement_meromorphic

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
