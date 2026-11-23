import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Section

/-! # Exact physical approximation and intermediate readings on a prescribed prefix -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- Continuous reconstruction from the first N levels alone. -/
def physicalCompletion (N : ℕ) (b : SpectralBand 1) := prescribedSpectrum (fun j : Fin N => b j.val)

theorem completion_continuous (N : ℕ) : Continuous (physicalCompletion N) :=
  (prescribedSpectrum_continuous N).comp (continuous_pi (fun j => continuous_apply j.val))

theorem completion_physical (N : ℕ) (b : SpectralBand 1) : physicalCompletion N b ∈ physicalSpectra 1 :=
  prescribedSpectrum_physical _

theorem completion_fixes {N k : ℕ} (b : SpectralBand 1) (hk : k < N) : physicalCompletion N b k = b k :=
  Subtype.ext (prescribedSpectrum_prefix (fun j : Fin N => b j.val) ⟨k,hk⟩)

theorem completion_tendsto (b : SpectralBand 1) : Tendsto (fun N => physicalCompletion N b) atTop (𝓝 b) := by
  apply tendsto_pi_nhds.mpr
  intro k
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop k] with n hn
  exact (completion_fixes b hn).symm

def prefixFiber (N : ℕ) (a : SpectralBand 1) : Set (SpectralBand 1) := {b | ∀ k < N, b k = a k}

/-- Closure within any prescribed fiber includes both ends of every free interlacing gap. -/
theorem closure_physical_fiber (N : ℕ) (a : SpectralBand 1) :
    closure (physicalSpectra 1 ∩ prefixFiber N a) = prefixFiber N a := by
  ext b
  constructor
  · intro hb
    obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hb
    intro k hk
    exact tendsto_nhds_unique (tendsto_pi_nhds.mp ht k)
      (tendsto_const_nhds.congr (fun n => ((hu n).2 k hk).symm))
  · intro hb
    apply mem_closure_of_tendsto (completion_tendsto b)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact ⟨completion_physical n b,fun k hk => (completion_fixes b (hk.trans_le hn)).trans (hb k hk)⟩

private def pinPrefix (N : ℕ) (a b : SpectralBand 1) : SpectralBand 1 := fun k => if k < N then a k else b k

private theorem pin_continuous (N : ℕ) (a : SpectralBand 1) : Continuous (pinPrefix N a) := by
  apply continuous_pi
  intro k
  by_cases hk : k < N
  · simpa only [pinPrefix,if_pos hk] using (continuous_const : Continuous (fun _ : SpectralBand 1 => a k))
  · simpa only [pinPrefix,if_neg hk] using (continuous_apply k : Continuous (fun b : SpectralBand 1 => b k))

private theorem pin_eq {N : ℕ} {a b : SpectralBand 1} (hb : b ∈ prefixFiber N a) : pinPrefix N a b = b := by
  funext k
  by_cases hk : k < N
  · exact (if_pos hk).trans (hb k hk).symm
  · exact if_neg hk

/-- A strict intermediate value of any continuous real measurement on a prescribed fiber is attained physically on that fiber. -/
theorem physical_intermediate_on_fiber {N : ℕ} {a b c : SpectralBand 1} (hb : b ∈ prefixFiber N a)
    (hc : c ∈ prefixFiber N a) {F : SpectralBand 1 → ℝ} (hF : Continuous F) {y : ℝ} (hby : F b < y) (hyc : y < F c) :
    ∃ d ∈ physicalSpectra 1 ∩ prefixFiber N a, F d = y := by
  have hb' := ((hF.tendsto b).comp (completion_tendsto b)).eventually_lt_const hby
  have hc' := (tendsto_order.mp ((hF.tendsto c).comp (completion_tendsto c))).1 y hyc
  obtain ⟨n,hn,hb',hc'⟩ := ((eventually_ge_atTop N).and (hb'.and hc')).exists
  let G (d : SpectralBand 1) := F (physicalCompletion n (pinPrefix N a d))
  have hg : Continuous G := hF.comp ((completion_continuous n).comp (pin_continuous N a))
  have hl : G b ≤ y := by simpa only [G,pin_eq hb,Function.comp_apply] using hb'.le
  have hu : y ≤ G c := by simpa only [G,pin_eq hc,Function.comp_apply] using hc'.le
  letI (k : ℕ) : PreconnectedSpace (Icc (occupationWeight (k+1)) (occupationWeight k)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  obtain ⟨d,hd⟩ := intermediate_value_univ b c hg ⟨hl,hu⟩
  exact ⟨_,⟨completion_physical n _,fun k hk => (completion_fixes _ (hk.trans_le hn)).trans (if_pos hk)⟩,hd⟩

#print axioms completion_tendsto
#print axioms closure_physical_fiber
#print axioms physical_intermediate_on_fiber

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
