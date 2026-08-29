import GaloisForLFunctions.HTGeometry.NevanlinnaTranslationCharacteristic
import GaloisForLFunctions.HTGeometry.DivisorMassCounting

/-!
# The pole-mass bound at an arbitrary larger radius

The corpus's `log_two_mul_poleMultiplicityMass_le_logCounting` compares the pole mass in the disc of
radius `R` with the counting function at `2R`.  Nevanlinna's error term needs the comparison radius
to be *close* to `R` instead, because the characteristic of an entire function at twice the radius is
not controlled by its value at the radius; only the ratio enters, and it enters logarithmically.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Topology Filter ValueDistribution Asymptotics
open PoissonJensen MeromorphicOn

noncomputable section

/-- **Pole mass in a disc, at an arbitrary larger radius.**  The corpus's
`log_two_mul_poleMultiplicityMass_le_logCounting` is the case `R' = 2R`; the ratio `R'/R` may be
taken close to one, which is what the Nevanlinna error term needs. -/
theorem log_ratio_mul_poleMultiplicityMass_le_logCounting
    {f : ℂ → ℂ} (hf : Meromorphic f) {R R' : ℝ} (hR : 1 ≤ R) (hRR' : R < R') :
    Real.log (R' / R) * poleMultiplicityMass f R ≤ logCounting f ⊤ R' := by
  classical
  let D : Function.locallyFinsupp ℂ ℤ := (divisor f Set.univ)⁻
  let DR := divisor f (closedBall (0 : ℂ) |R|)
  let P := (Function.locallyFinsuppWithin.toClosedBall R') D
  have hR'pos : 0 < R' := by linarith
  have hRabs : |R| = R := abs_of_nonneg (le_trans zero_le_one hR)
  have hR'abs : |R'| = R' := abs_of_pos hR'pos
  have hDRfin : DR.support.Finite :=
    DR.finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  have hmassFin : (Function.support fun u : ℂ ↦ (DR u : ℝ)⁻).Finite :=
    hDRfin.subset (by
      intro u hu
      have hu' := Function.mem_support.mp hu
      exact Function.mem_support.mpr fun hzero ↦ hu' (by simp [hzero]))
  let S := hmassFin.toFinset
  have hmass : poleMultiplicityMass f R = ∑ u ∈ S, (DR u : ℝ)⁻ := by
    rw [poleMultiplicityMass]
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
    intro hDu
    rw [hDu] at hu
    simp at hu
  have hPfin : P.support.Finite :=
    P.finiteSupport (isCompact_closedBall (0 : ℂ) |R'|)
  let T := hPfin.toFinset
  have hcount : logCounting f ⊤ R' =
      ∑ u ∈ T, (P u : ℝ) * Real.log (R' * ‖u‖⁻¹) +
        (D 0 : ℝ) * Real.log R' := by
    rw [logCounting_top]
    change Function.locallyFinsuppWithin.logCounting D R' = _
    change (∑ᶠ u : ℂ, (P u : ℝ) * Real.log (R' * ‖u‖⁻¹)) +
        (D 0 : ℝ) * Real.log R' = _
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro u hu
    simp only [Function.mem_support] at hu
    simp only [T, Set.Finite.coe_toFinset, Function.mem_support]
    intro hPu
    exact hu (by simp [hPu])
  have hlocalGlobalInt : ∀ u ∈ closedBall (0 : ℂ) R, (DR u)⁻ = D u := by
    intro u hu
    have huabs : u ∈ closedBall (0 : ℂ) |R| := by
      rw [hRabs]
      exact hu
    have hlocal := divisor_apply (fun z _ => hf z) huabs
    have hglobal := divisor_apply (fun z _ => hf z) (Set.mem_univ u)
    dsimp [DR, D]
    rw [hlocal, hglobal]
  have hlocalGlobal : ∀ u ∈ closedBall (0 : ℂ) R, (DR u : ℝ)⁻ = (D u : ℝ) := by
    intro u hu
    rw [← hlocalGlobalInt u hu]
    change max (-(DR u : ℝ)) 0 = ((max (-DR u) 0 : ℤ) : ℝ)
    norm_cast
  have hSball : ∀ u ∈ S, u ∈ closedBall (0 : ℂ) R := by
    intro u hu
    have huMass : (DR u : ℝ)⁻ ≠ 0 := by simpa [S] using hu
    have huSupp : u ∈ DR.support := by
      apply Function.mem_support.mpr
      intro hzero
      rw [hzero] at huMass
      simp at huMass
    have huDomain := DR.supportWithinDomain huSupp
    rw [hRabs] at huDomain
    exact huDomain
  have hST : ∀ u ∈ S, u ≠ 0 → u ∈ T := by
    intro u huS hu0
    have huBall := hSball u huS
    have hu2Ball : u ∈ closedBall (0 : ℂ) |R'| := by
      rw [hR'abs, mem_closedBall_zero_iff]
      have := mem_closedBall_zero_iff.mp huBall
      linarith
    have hDu : D u ≠ 0 := by
      have huMass : (DR u : ℝ)⁻ ≠ 0 := by simpa [S] using huS
      have hlocal := hlocalGlobal u huBall
      intro hzero
      rw [hzero] at hlocal
      exact huMass (by simpa using hlocal)
    have hPu : P u ≠ 0 := by
      change (if u ∈ closedBall (0 : ℂ) |R'| then D u else 0) ≠ 0
      rw [if_pos hu2Ball]
      exact hDu
    simpa [T] using hPu
  have hweight : ∀ u ∈ S, u ≠ 0 →
      Real.log (R' / R) * (DR u : ℝ)⁻ ≤
        (P u : ℝ) * Real.log (R' * ‖u‖⁻¹) := by
    intro u huS hu0
    have huBall := hSball u huS
    have huNorm : ‖u‖ ≤ R := by simpa [mem_closedBall_zero_iff] using huBall
    have huNormPos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hu2Ball : u ∈ closedBall (0 : ℂ) |R'| := by
      rw [hR'abs, mem_closedBall_zero_iff]
      linarith
    have hPD : P u = D u := by
      change (if u ∈ closedBall (0 : ℂ) |R'| then D u else 0) = D u
      rw [if_pos hu2Ball]
    have hcoeff : (P u : ℝ) = (DR u : ℝ)⁻ := by
      rw [hPD, ← hlocalGlobal u huBall]
    rw [hcoeff]
    have hRpos : (0 : ℝ) < R := by linarith
    have hlog : Real.log (R' / R) ≤ Real.log (R' * ‖u‖⁻¹) := by
      refine Real.log_le_log (by positivity) ?_
      have hR'0 : (0 : ℝ) ≤ R' := by linarith
      rw [← div_eq_mul_inv]
      gcongr
    calc
      Real.log (R' / R) * (DR u : ℝ)⁻ = (DR u : ℝ)⁻ * Real.log (R' / R) := mul_comm _ _
      _ ≤ (DR u : ℝ)⁻ * Real.log (R' * ‖u‖⁻¹) :=
        mul_le_mul_of_nonneg_left hlog (negPart_nonneg _)
  have hsumNonzero : Real.log (R' / R) * ∑ u ∈ S.erase 0, (DR u : ℝ)⁻ ≤
      ∑ u ∈ T, (P u : ℝ) * Real.log (R' * ‖u‖⁻¹) := by
    rw [Finset.mul_sum]
    calc
      ∑ u ∈ S.erase 0, Real.log (R' / R) * (DR u : ℝ)⁻ ≤
          ∑ u ∈ S.erase 0, (P u : ℝ) * Real.log (R' * ‖u‖⁻¹) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hweight u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)
      _ ≤ ∑ u ∈ T, (P u : ℝ) * Real.log (R' * ‖u‖⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          exact hST u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)
        · intro u huT _
          have huSupp : u ∈ P.support := by simpa [T] using huT
          have huBall := P.supportWithinDomain huSupp
          have huNorm : ‖u‖ ≤ R' := by
            simpa [hR'abs, mem_closedBall_zero_iff] using huBall
          have hPD : P u = D u := by
            change (if u ∈ closedBall (0 : ℂ) |R'| then D u else 0) = D u
            rw [if_pos huBall]
          have hcoeff : 0 ≤ (P u : ℝ) := by
            rw [hPD]
            norm_cast
            dsimp [D]
            exact negPart_nonneg _
          have hlog : 0 ≤ Real.log (R' * ‖u‖⁻¹) := by
            by_cases hu0 : u = 0
            · simp [hu0]
            · apply Real.log_nonneg
              rw [inv_eq_one_div, mul_div]
              exact (one_le_div (norm_pos_iff.mpr hu0)).2 (by simpa using huNorm)
          positivity
  have hzeroCoeff : (DR 0 : ℝ)⁻ = (D 0 : ℝ) := by
    exact hlocalGlobal 0 (by simp [le_trans zero_le_one hR])
  have hzero : Real.log (R' / R) * (DR 0 : ℝ)⁻ ≤ (D 0 : ℝ) * Real.log R' := by
    rw [hzeroCoeff]
    have hRpos2 : (0 : ℝ) < R := by linarith
    have hlog : Real.log (R' / R) ≤ Real.log R' := by
      refine Real.log_le_log (by positivity) ?_
      exact div_le_self (by linarith) hR
    calc
      Real.log (R' / R) * (D 0 : ℝ) = (D 0 : ℝ) * Real.log (R' / R) := mul_comm _ _
      _ ≤ (D 0 : ℝ) * Real.log R' := by
        apply mul_le_mul_of_nonneg_left hlog
        norm_cast
        dsimp [D]
        exact negPart_nonneg _
  rw [hmass, hcount]
  by_cases h0S : 0 ∈ S
  · rw [← Finset.sum_erase_add S (fun u ↦ (DR u : ℝ)⁻) h0S, mul_add]
    linarith
  · rw [Finset.erase_eq_self.mpr h0S] at hsumNonzero
    have hmass0 : (DR 0 : ℝ)⁻ = 0 := by
      have hnot : 0 ∉ Function.support (fun u : ℂ ↦ (DR u : ℝ)⁻) := by
        simpa [S] using h0S
      simpa [Function.mem_support] using hnot
    rw [hmass0] at hzeroCoeff
    rw [← hzeroCoeff]
    simp
    exact hsumNonzero


/-- **The counting bridge at an arbitrary larger radius.**  The total divisor mass in the disc of
radius `R` is controlled by the counting functions at any radius `R' > R`, with the loss
`log(R'/R)`. -/
theorem log_ratio_mul_divisorMass_le_logCounting {f : ℂ → ℂ} (hf : Meromorphic f)
    {R R' : ℝ} (hR : 1 ≤ R) (hRR' : R < R') :
    Real.log (R' / R) * (∑ᶠ u : ℂ, |((divisor f (closedBall (0 : ℂ) |R|) u : ℤ) : ℝ)|)
      ≤ logCounting f ⊤ R' + logCounting f 0 R' := by
  have hinv : Meromorphic f⁻¹ := fun z => (hf z).inv
  have h₁ := log_ratio_mul_poleMultiplicityMass_le_logCounting hf hR hRR'
  have h₂ := log_ratio_mul_poleMultiplicityMass_le_logCounting hinv hR hRR'
  rw [ValueDistribution.logCounting_inv] at h₂
  rw [divisorMass_eq_add, mul_add]
  linarith

end

end GaloisForLFunctions.HTGeometry
