import GaloisForLFunctions.RHTower.ChiRamanujanUniformEulerComparison
import GaloisForLFunctions.RHTower.ChiRamanujanGlobalResidueControl

/-!
# Uniform pole geometry of the original finite Euler products

The all-frequency Euler–zeta comparison and the corpus's unconditional
bounds for the filled zeta residue factor control the original product
by the pole distance, in both directions, with a global polynomial weight.
This supplies arithmetic domination through the shrinking pole scale.
The full labelled source and its moving physical Mellin integral remain
separate obligations.
-/

noncomputable section
open Filter Set Metric
open scoped BigOperators Topology
namespace RHTower.BAGTrace

/-- Pole geometry of the original finite Euler product, uniformly in every
frequency and every bounded signed logarithmic abscissa displacement. -/
theorem criticalFiniteEulerProduct_pole_comparison (A : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ a : ℝ, |a|≤|A| → ∀ t : ℝ,
      ‖((1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I‖ ≤ C*(1+|t|)^9 *
        ‖∏ p ∈ Nat.primesLE N,(1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I))‖ ∧
      ‖∏ p ∈ Nat.primesLE N,(1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I))‖ ≤
        C*(1+|t|)^9 * ‖((1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I‖ := by
  obtain ⟨B,hB,hcomp⟩ := criticalFiniteEulerProduct_zeta_comparison A
  obtain ⟨c,hc,M,hM,hres⟩ := exists_residue_global_polynomial_disks
  refine ⟨Real.exp B*M, mul_pos (Real.exp_pos _) hM,?_⟩
  filter_upwards [hcomp,eventually_ge_atTop 3] with N hN hN3
  intro a ha t
  have hNr : (3 : ℝ)≤N := by exact_mod_cast hN3
  have hL : 1≤Real.log N := by
    have he : Real.exp 1≤(N : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hh := Real.log_le_log (Real.exp_pos 1) he
    simpa using hh
  have hL0 : 0<Real.log N := by linarith
  have hdiv : 0<1/Real.log N := by positivity
  have hdiv1 : 1/Real.log N≤1 := by
    rw [div_le_iff₀ hL0]
    simpa using hL
  let s : ℂ := ((1+1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I
  let d : ℂ := ((1/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I
  let Q : ℂ := ∏ p ∈ Nat.primesLE N,
    (1-(p : ℂ)^(-1-(a/Real.log N : ℝ)-(t : ℂ)*Complex.I))
  have hsre : s.re=1+1/Real.log N := by
    simp only [s,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,mul_zero,zero_mul,sub_self,add_zero]
  have hsne : s≠1 := by
    intro hh
    have hre := congrArg Complex.re hh
    rw [hsre] at hre
    simp only [Complex.one_re] at hre
    linarith
  have hd : s-1=d := by dsimp [s,d]; push_cast; ring
  have hdne : d≠0 := by rw [← hd]; exact sub_ne_zero.mpr hsne
  have hz : riemannZeta s≠0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; linarith)
  have hb := hres (1+1/Real.log N) ⟨by linarith,by linarith⟩ t s
    (by simpa only [mem_closedBall,s,dist_self] using
      (show (0 : ℝ)≤c/(1+|t|)^9 from div_nonneg hc.1.le (by positivity)))
  have hfactor : zetaResidueFactor s=d*riemannZeta s := by
    rw [zetaResidueFactor_of_ne hsne,hd]
  have hnorm : ‖d‖*‖riemannZeta s‖≤M*(1+|t|)^9 := by
    simpa only [hfactor,norm_mul] using hb.2.1
  have hinv : ‖d‖⁻¹*‖riemannZeta s‖⁻¹≤M*(1+|t|)^9 := by
    simpa only [hfactor,mul_inv_rev,norm_mul,norm_inv,mul_comm] using hb.2.2
  have hQ := hN a ha t
  change Real.exp (-B)≤‖Q‖*‖riemannZeta s‖ ∧ ‖Q‖*‖riemannZeta s‖≤Real.exp B at hQ
  have he : Real.exp B*Real.exp (-B)=1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hlower : 1≤Real.exp B*(‖Q‖*‖riemannZeta s‖) := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left hQ.1 (Real.exp_pos _).le
  have hdpos : 0<‖d‖ := norm_pos_iff.mpr hdne
  have hzpos : 0<‖riemannZeta s‖ := norm_pos_iff.mpr hz
  constructor
  · change ‖d‖≤(Real.exp B*M)*(1+|t|)^9*‖Q‖
    calc ‖d‖ ≤ Real.exp B*(‖Q‖*‖riemannZeta s‖)*‖d‖ := by nlinarith
         _ = (Real.exp B*‖Q‖)*(‖d‖*‖riemannZeta s‖) := by ring
         _ ≤ (Real.exp B*‖Q‖)*(M*(1+|t|)^9) := by gcongr
         _ = _ := by ring
  · change ‖Q‖≤(Real.exp B*M)*(1+|t|)^9*‖d‖
    have hi : ‖riemannZeta s‖⁻¹≤M*(1+|t|)^9*‖d‖ := by
      have hh := mul_le_mul_of_nonneg_right hinv hdpos.le
      have heq : (‖d‖⁻¹*‖riemannZeta s‖⁻¹)*‖d‖=‖riemannZeta s‖⁻¹ := by
        field_simp
      rwa [heq] at hh
    calc ‖Q‖ = (‖Q‖*‖riemannZeta s‖)*‖riemannZeta s‖⁻¹ := by field_simp
         _ ≤ Real.exp B*‖riemannZeta s‖⁻¹ := by gcongr; exact hQ.2
         _ ≤ Real.exp B*(M*(1+|t|)^9*‖d‖) := by gcongr
         _ = _ := by ring

end RHTower.BAGTrace
