import GaloisForLFunctions.RHTower.JointAncestryPointwiseCriterion
import GaloisForLFunctions.RHTower.JointAncestrySimilarityLaw
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import GaloisForLFunctions.HTGeometry.ArchimedeanCorank

/-!
# The vertical (Kronecker-line) criterion for dressed positivity

The pointwise criterion asks for nonnegativity of the zero sum of twisted local Euler densities at
every point of every finite prime torus `T^P`.  The zero sum is continuous on the torus, and the
vertical flow `τ ↦ (p^{-iτ})_{p ∈ P}` is dense in `T^P` (Kronecker; the `log p` are rationally
independent).  Hence it suffices to test the points of the vertical flow: for `c > 0`,

`PSD(1/2 + c) ⟺ ∀ P finite, ∀ τ ∈ ℝ,  0 ≤ Re Σ_ρ (1/(ρ(1-ρ))) ∏_{p ∈ P} ℓ_p^ρ(p^{-iτ})`,

and at the vertical point the local density is the Euler factor
`(1 - p^{-2σ}) / ((1 - p^{-(σ+ρ-½+iτ)}) (1 - p^{-(σ-ρ+½-iτ)}))`.  At `σ = 1` the summand of an on-line
zero `ρ = ½ + iγ` is `|ζ_P(1 + i(γ+τ))|² / (ζ_P(2) |ρ|²)`.  So RH holds, up to an off-line chain
with no farthest zero, exactly when every finite partial-Euler-product zero sum
`Re Σ_ρ ζ_P(ρ + ½ + iτ) ζ_P(3/2 - ρ - iτ) / (ρ(1-ρ))` is nonnegative.
-/

open Complex Filter Topology
open scoped ComplexConjugate BigOperators

namespace RHTower

noncomputable section

/-- The vertical point `(p^{-iτ})_p`. -/
def jasVerticalPoint (τ : ℝ) (p : Nat.Primes) : ℂ :=
  cexp (((-τ * Real.log (p : ℕ) : ℝ) : ℂ) * I)

theorem norm_jasVerticalPoint (τ : ℝ) (p : Nat.Primes) : ‖jasVerticalPoint τ p‖ = 1 := by
  rw [jasVerticalPoint, Complex.norm_exp_ofReal_mul_I]

/-- The zero sum of twisted local Euler densities at a point of the torus `T^P`. -/
def jasZeroSumDensity (c : ℝ) (P : Finset Nat.Primes) (w : ↥P → ℂ) : ℂ :=
  ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
    ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i) (w i)

theorem continuousOn_jasHoloLocal {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ContinuousOn (jasHoloLocal a b) {w : ℂ | ‖w‖ = 1} := by
  have h1 : ContinuousOn (fun w : ℂ => (1 - a * w)⁻¹) {w : ℂ | ‖w‖ = 1} := by
    refine (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.inv₀ ?_
    intro w hw
    have : ‖a * w‖ < 1 := by rw [norm_mul, hw, mul_one]; exact ha
    show (1 : ℂ) - a * w ≠ 0
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  have h2 : ContinuousOn (fun w : ℂ => (1 - b * conj w)⁻¹) {w : ℂ | ‖w‖ = 1} := by
    refine (continuous_const.sub (continuous_const.mul
      Complex.continuous_conj)).continuousOn.inv₀ ?_
    intro w hw
    have : ‖b * conj w‖ < 1 := by rw [norm_mul, Complex.norm_conj, hw, mul_one]; exact hb
    show (1 : ℂ) - b * conj w ≠ 0
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  unfold jasHoloLocal
  exact (h1.add h2).sub continuousOn_const

theorem norm_jasHoloLocal_le_of_norm_eq_one {a b w : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1)
    (hw : ‖w‖ = 1) : ‖jasHoloLocal a b w‖ ≤ 1 / (1 - ‖a‖) + 1 / (1 - ‖b‖) + 1 := by
  unfold jasHoloLocal
  have h1 := norm_inv_one_sub_le (z := a * w) (by rw [norm_mul, hw, mul_one]; exact ha)
  have h2 := norm_inv_one_sub_le (z := b * conj w)
    (by rw [norm_mul, Complex.norm_conj, hw, mul_one]; exact hb)
  rw [norm_mul, hw, mul_one] at h1
  rw [norm_mul, Complex.norm_conj, hw, mul_one] at h2
  calc _ ≤ ‖(1 - a * w)⁻¹ + (1 - b * conj w)⁻¹‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖(1 - a * w)⁻¹‖ + ‖(1 - b * conj w)⁻¹‖ + 1 := by
        rw [norm_one]; gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr

/-- The zero sum is continuous on the torus `T^P`. -/
theorem continuousOn_jasZeroSumDensity {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes) :
    ContinuousOn (jasZeroSumDensity c P) {w : ↥P → ℂ | ∀ i, ‖w i‖ = 1} := by
  unfold jasZeroSumDensity
  refine continuousOn_tsum (u := fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
    ∏ i : ↥P, jasCircleBound c i) (fun q => ?_) (summable_inv_mul_one_sub.norm.mul_right _) ?_
  · have h0 := (xi_divisor_support_re_mem_open_unit q.1).1
    have h1 := (xi_divisor_support_re_mem_open_unit q.1).2
    refine continuousOn_const.mul (continuousOn_finsetProd _ fun i _ => ?_)
    have hm := exp_neg_mul_log_lt_one hc i
    exact (continuousOn_jasHoloLocal ((norm_jasHoloA_dressed_le (c := c) h0 i).trans_lt hm)
      ((norm_jasHoloB_dressed_le (c := c) h1 i).trans_lt hm)).comp (continuous_apply i).continuousOn
      (fun w hw => hw i)
  · intro q w hw
    have h0 := (xi_divisor_support_re_mem_open_unit q.1).1
    have h1 := (xi_divisor_support_re_mem_open_unit q.1).2
    rw [norm_mul, norm_prod]
    gcongr with i _
    have hm := exp_neg_mul_log_lt_one hc i
    have hA := norm_jasHoloA_dressed_le (c := c) h0 i
    have hB := norm_jasHoloB_dressed_le (c := c) h1 i
    refine (norm_jasHoloLocal_le_of_norm_eq_one (hA.trans_lt hm) (hB.trans_lt hm) (hw i)).trans ?_
    have hpos : 0 < 1 - Real.exp (-c * Real.log i) := by linarith
    have e1 : 1 / (1 - ‖jasHoloA ((q.1 : ℂ) + c) i‖) ≤ (1 - Real.exp (-c * Real.log i))⁻¹ := by
      rw [one_div]; exact inv_anti₀ hpos (by linarith)
    have e2 : 1 / (1 - ‖jasHoloB ((q.1 : ℂ) - c) i‖) ≤ (1 - Real.exp (-c * Real.log i))⁻¹ := by
      rw [one_div]; exact inv_anti₀ hpos (by linarith)
    unfold jasCircleBound
    linarith

/-- The vertical flow approximates every point of the torus `T^P`. -/
theorem exists_jasVerticalPoint_near (P : Finset Nat.Primes) {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ τ : ℝ, ∀ i : ↥P, ‖jasVerticalPoint τ i - w i‖ < ε := by
  classical
  obtain ⟨t, ht⟩ := GaloisForLFunctions.kronecker_approx
    (GaloisForLFunctions.primeLogFiniteSlice_linearIndependent P)
    (fun i => (w i).arg) hε
  refine ⟨-t, fun i => ?_⟩
  have hwi : cexp (((w i).arg : ℂ) * I) = w i := by
    have := Complex.norm_mul_exp_arg_mul_I (w i)
    rwa [hw i, Complex.ofReal_one, one_mul] at this
  have hv : jasVerticalPoint (-t) i = GaloisForLFunctions.expChar (Real.log ((i : Nat.Primes) : ℕ)) t := by
    rw [jasVerticalPoint, GaloisForLFunctions.expChar]
    congr 3
    ring
  rw [hv, ← hwi]
  exact ht i

/-- **Vertical criterion.**  For `c > 0` the `σ`-dressed aggregate (`σ = 1/2 + c`) is positive
semidefinite if and only if, for every finite prime set and every real `τ`, the zero sum of the
local Euler densities at the vertical point `(p^{-iτ})_p` has nonnegative real part. -/
theorem jasDressedPSD_iff_vertical {c : ℝ} (hc : 0 < c) :
    JasDressedPSD (1 / 2 + c) ↔ ∀ (P : Finset Nat.Primes) (τ : ℝ),
      0 ≤ (jasZeroSumDensity c P (fun i => jasVerticalPoint τ i)).re := by
  rw [jasDressedPSD_iff_pointwise hc]
  constructor
  · intro h P τ
    exact h P _ fun i => norm_jasVerticalPoint τ i
  · intro h P w hw
    show 0 ≤ (jasZeroSumDensity c P w).re
    have hcont := continuousOn_jasZeroSumDensity hc P w hw
    have hseq : ∀ k : ℕ, ∃ τ : ℝ, ∀ i : ↥P,
        ‖jasVerticalPoint τ i - w i‖ < 1 / ((k : ℝ) + 1) :=
      fun k => exists_jasVerticalPoint_near P hw (by positivity)
    choose τ hτ using hseq
    have htend : Tendsto (fun k => fun i : ↥P => jasVerticalPoint (τ k) i) atTop
        (𝓝[{w : ↥P → ℂ | ∀ i, ‖w i‖ = 1}] w) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨tendsto_pi_nhds.mpr fun i => ?_, Eventually.of_forall fun k i =>
        norm_jasVerticalPoint (τ k) i⟩
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hτ k i).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim := ((Complex.continuous_re.tendsto _).comp (hcont.tendsto.comp htend))
    exact ge_of_tendsto' hlim fun k => h P (τ k)

/-- **RH in vertical Euler form.**  Under RH every vertical zero sum at `σ = 1` is nonnegative;
conversely their nonnegativity forces RH unless the off-line zeros form a chain with no farthest
zero. -/
theorem riemannHypothesis_or_chain_of_vertical_one
    (h : ∀ (P : Finset Nat.Primes) (τ : ℝ),
      0 ≤ (jasZeroSumDensity (1 / 2) P (fun i => jasVerticalPoint τ i)).re) :
    RiemannHypothesis ∨ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
      ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| := by
  have hpsd := (jasDressedPSD_iff_vertical (by norm_num : (0 : ℝ) < 1 / 2)).mpr h
  norm_num at hpsd
  exact riemannHypothesis_or_offLine_chain_of_jasDressedPSD le_rfl hpsd

theorem vertical_one_of_riemannHypothesis (hRH : RiemannHypothesis) (P : Finset Nat.Primes)
    (τ : ℝ) : 0 ≤ (jasZeroSumDensity (1 / 2) P (fun i => jasVerticalPoint τ i)).re := by
  have hpsd := jasDressedPSD_of_riemannHypothesis hRH (σ := 1 / 2 + 1 / 2) (by norm_num)
  exact (jasDressedPSD_iff_vertical (by norm_num : (0 : ℝ) < 1 / 2)).mp hpsd P τ

/-- The vertical local density is the Euler factor
`(1 - p^{-2σ}) / ((1 - p^{-(σ+ρ-½+iτ)}) (1 - p^{-(σ-ρ+½-iτ)}))`, written in exponential form. -/
theorem jasHoloLocal_jasVerticalPoint {s : ℂ} {c : ℝ} (τ : ℝ) {p : Nat.Primes}
    (hA : ‖jasHoloA (s + c) p‖ < 1) (hB : ‖jasHoloB (s - c) p‖ < 1) :
    jasHoloLocal (jasHoloA (s + c) p) (jasHoloB (s - c) p) (jasVerticalPoint τ p) =
      (1 - cexp (-(1 + 2 * c) * (Real.log (p : ℕ) : ℂ))) /
        ((1 - cexp (-(s + c + τ * I) * (Real.log (p : ℕ) : ℂ))) *
          (1 - cexp (-(1 - s + c - τ * I) * (Real.log (p : ℕ) : ℂ)))) := by
  have hw := norm_jasVerticalPoint τ p
  have e1 : jasHoloA (s + c) p * jasVerticalPoint τ p =
      cexp (-(s + c + τ * I) * (Real.log (p : ℕ) : ℂ)) := by
    rw [jasHoloA, jasVerticalPoint, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : jasHoloB (s - c) p * conj (jasVerticalPoint τ p) =
      cexp (-(1 - s + c - τ * I) * (Real.log (p : ℕ) : ℂ)) := by
    rw [jasHoloB, jasVerticalPoint, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have e3 : jasHoloA (s + c) p * jasHoloB (s - c) p =
      cexp (-(1 + 2 * c) * (Real.log (p : ℕ) : ℂ)) := by
    rw [jasHoloA, jasHoloB, ← Complex.exp_add]
    congr 1
    ring
  have hne1 : 1 - jasHoloA (s + c) p * jasVerticalPoint τ p ≠ 0 := by
    intro h
    have : ‖jasHoloA (s + c) p * jasVerticalPoint τ p‖ = 1 := by
      rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_mul, hw, mul_one] at this
    exact absurd this hA.ne
  have hne2 : 1 - jasHoloB (s - c) p * conj (jasVerticalPoint τ p) ≠ 0 := by
    intro h
    have : ‖jasHoloB (s - c) p * conj (jasVerticalPoint τ p)‖ = 1 := by
      rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_mul, Complex.norm_conj, hw, mul_one] at this
    exact absurd this hB.ne
  rw [jasHoloLocal_eq_div hw hne1 hne2, e1, e2, e3]

end

end RHTower
