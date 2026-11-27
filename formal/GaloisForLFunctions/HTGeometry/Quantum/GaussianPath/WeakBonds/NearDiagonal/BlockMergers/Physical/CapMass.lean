import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.FinalSeam
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.HierarchicalSpacing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.MaximumCDF

/-! # Gaussian probability of a linear-in-dimension all-time gate budget -/
open Set MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open PrescribedTimes PrescribedTimes.JointSpeeds DiagonalSynthesis.CommutatorBounds
noncomputable section

/-- Every date on this physical orbit fits within 213 times its Hilbert dimension. -/
def capEvent (n : ℕ) (ε : ℝ) : Set (PathLabel n→ℝ) :=
  (fun x i => x (pathCoeffEquiv n i)) ⁻¹' orbitBudget n (213*2^(n+2)) ε

theorem measurable_capEvent (n : ℕ) (ε : ℝ) : MeasurableSet (capEvent n ε) :=
  (isClosed_orbitBudget ..).measurableSet.preimage (measurable_pi_lambda _ fun i => measurable_pi_apply (pathCoeffEquiv n i))

/-- The same coefficients obey both the all-time circuit cap and the spectral gap. -/
def separatedCap (n : ℕ) (ε : ℝ) := capEvent n ε ∩ gapEvent n (gapScale (n+2))

private theorem cap_with_children : ∃ ρ ∈ Ioc (0:ℝ) 1, ∃ b ∈ Ioc (0:ℝ) 1,
    ∀ l r : ℕ, l ≤ r → r ≤ l+1 → ∀ ε ∈ Ioc (0:ℝ) 1,
      ρ^(l+r+4)*gapMass l*gapMass r*(b*ε)^9 ≤
        (standardLaw (PathLabel (l+r+2))).real (separatedCap (l+r+2) ε) := by
  obtain ⟨ρ,hρ,hprice⟩ := priced_join_mass
  let p := sqrt packConstant
  let b := 1/(1+p)
  have hp : 0 ≤ p := sqrt_nonneg _
  have hp' : 0 < 1+p := by linarith only [hp]
  have hb : b∈Ioc (0:ℝ) 1 := ⟨one_div_pos.mpr hp',(div_le_one hp').mpr (by linarith only [hp])⟩
  refine ⟨ρ,hρ,b,hb,?_⟩
  intro l r hl hr ε hε
  let K := l+r+4
  let g := gapScale K
  let z := b*ε
  have hz : z∈Ioc (0:ℝ) 1 := ⟨mul_pos hb.1 hε.1,(mul_le_of_le_one_right hb.1.le hε.2).trans hb.2⟩
  have hg := gapScale_pos K
  apply hprice l r z hz _ measureReal_nonneg
  apply joined_event_mass l r hl hr
  intro x hx hs
  have herr : 4*p/(2*g)*(9*(g/20*z)) ≤ ε := by
    calc _ = ((9/10:ℝ)*p/(1+p))*ε := by
           dsimp only [z,b,g]; field_simp [hg.ne',hp'.ne']; ring
         _ ≤ ε := mul_le_of_le_one_left hε.1.le ((div_le_one hp').mpr (by linarith only [hp]))
  have hcap := final_seam_cap l r hl hr x (mul_pos two_pos hg) hx herr (fun i => abs_le.mpr (hs i (mem_univ i)))
  constructor
  · let u : PathShell (l+r+2) := WithLp.toLp 2 x
    intro t
    change pathGateDistance (l+r+2) _ (fun i => u (pathCoeffEquiv _ i)) t ≤ ε
    rw [pathGateDistance,numberedGenerator_shell]
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mp (hcap t)
  · intro i j hij
    have hsmall (t) : |(extractBlocks l r x).2 t| ≤ g/20 :=
      (abs_le.mpr (hs t (mem_univ t))).trans (mul_le_of_le_one_right (by positivity) hz.2)
    have h := physical_merge_gap l r x (mul_pos two_pos hg) hx
      (fun t => (hsmall t).trans (by linarith only [hg])) i j hij
    change 2*g/2 ≤ _ at h
    rw [show 2*g/2=g by ring] at h
    exact h

/-- The full chain is drawn once. Only its last nine joining coefficients
pay for accuracy. Balanced internal gap constraints cost K times the tree depth. -/
theorem hierarchical_gap_cap_mass : ∃ a ∈ Ioc (0:ℝ) 1, ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, 2 ≤ n → ∀ ε ∈ Ioc (0:ℝ) 1,
      let K := n+2
      a*ε^9*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤
        (standardLaw (PathLabel n)).real (separatedCap n ε) := by
  obtain ⟨ρ,hρ,b,hb,hcap⟩ := cap_with_children
  obtain ⟨c,hc,hgap⟩ := hierarchical_gap_mass
  let C := c-log ρ
  have hlog : log ρ ≤ 0 := log_nonpos hρ.1.le hρ.2
  refine ⟨b^9,⟨pow_pos hb.1 _,pow_le_one₀ hb.1.le hb.2⟩,C,by dsimp only [C]; linarith only [hc,hlog],?_⟩
  intro n hn ε hε K
  let l := (n+2)/2-2
  let r := (n+3)/2-2
  have hsum : l+r+2=n := by dsimp only [l,r]; omega
  have hK : l+r+4=K := by dsimp only [K]; omega
  let d := (Nat.clog 2 K:ℝ)+1
  have hd : 1 ≤ d := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hparts (s : ℕ) (hs : s+2 ≤ K) : exp (-c*((s+2:ℕ):ℝ)*d) ≤ gapMass s := by
    apply (exp_le_exp.mpr _).trans (hgap s)
    exact mul_le_mul_of_nonpos_left (add_le_add (Nat.cast_le.mpr (Nat.clog_mono_right 2 hs)) (le_refl (1:ℝ)))
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Nat.cast_nonneg _))
  have hl := hparts l (by omega)
  have hr := hparts r (by omega)
  have he : (((l+2:ℕ):ℝ)+((r+2:ℕ):ℝ))=(K:ℝ) := by exact_mod_cast (by omega : l+2+(r+2)=K)
  have hm : exp (-c*(K:ℝ)*d) ≤ gapMass l*gapMass r := by
    rw [←he,show -c*(((l+2:ℕ):ℝ)+((r+2:ℕ):ℝ))*d=
      -c*((l+2:ℕ):ℝ)*d+ -c*((r+2:ℕ):ℝ)*d by ring,exp_add]
    exact mul_le_mul hl hr (exp_pos _).le measureReal_nonneg
  have hρK : exp (log ρ*(K:ℝ))=ρ^K := by rw [mul_comm,exp_nat_mul,exp_log hρ.1]
  have hexp : exp (-C*(K:ℝ)*d) ≤ ρ^K*exp (-c*(K:ℝ)*d) := by
    rw [←hρK,←exp_add]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_left hd (mul_nonpos_of_nonpos_of_nonneg hlog (Nat.cast_nonneg K))
    dsimp only [C]
    linarith only [h]
  have H := hcap l r (by dsimp only [l,r]; omega) (by dsimp only [l,r]; omega) ε hε
  rw [hsum,hK,mul_pow] at H
  apply le_trans _ H
  calc b^9*ε^9*exp (-C*(K:ℝ)*d) ≤ b^9*ε^9*(ρ^K*(gapMass l*gapMass r)) :=
         mul_le_mul_of_nonneg_left (hexp.trans (mul_le_mul_of_nonneg_left hm (pow_nonneg hρ.1.le K)))
           (mul_nonneg (pow_nonneg hb.1.le _) (pow_nonneg hε.1.le _))
       _ = _ := by ring

theorem hierarchical_cap_mass : ∃ a ∈ Ioc (0:ℝ) 1, ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, 2 ≤ n → ∀ ε ∈ Ioc (0:ℝ) 1,
      let K := n+2
      a*ε^9*exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤
        (standardLaw (PathLabel n)).real (capEvent n ε) := by
  obtain ⟨a,ha,C,hC,h⟩ := hierarchical_gap_cap_mass
  exact ⟨a,ha,C,hC,fun n hn ε he => (h n hn ε he).trans (measureReal_mono inter_subset_left)⟩

#print axioms hierarchical_gap_cap_mass
#print axioms hierarchical_cap_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
