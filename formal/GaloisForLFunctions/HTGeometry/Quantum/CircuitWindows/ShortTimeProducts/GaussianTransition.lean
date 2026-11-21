import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ShortTimeProducts.GaussianPacking

/-! # Linear-budget returns overwhelm every untouched-qubit budget at small error -/
open Matrix MeasureTheory Filter Topology Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ShortTimeProducts
noncomputable section
open SharpOccupation

/-- Even after multiplying the error of the smaller budget by any fixed
factor, the ratio of occupation fractions is unbounded. The same linear
product-word budget and the same tolerances work for every time origin. -/
theorem gaussian_linear_budget_occupation_transition :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let J := Fintype.card (PathLabel (k+1))
      ∃ B > 0, ∀ L R : ℝ, 0<L → 0<R → ∀ᶠ m : ℕ in atTop,
        let ε := B/(m:ℝ)^2
        ∀ a : ℝ, ∀ s : ℕ, 2*s<N → ∀ᶠ T : ℝ in atTop,
          R*visitFraction H s (L*ε) a T < visitFraction H J ε a T := by
  filter_upwards [gaussian_low_gate_occupation_order,gaussian_product_step_occupation] with ω hsmall hlarge k
  intro N H J
  obtain ⟨A,hA,hs⟩ := hsmall k
  obtain ⟨B,hB,hb⟩ := hlarge k
  refine ⟨B,hB,?_⟩
  intro L R hL hR
  let D := 2^N
  let d := D-1
  let K := 2*π*A*L*B
  have castTop : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1,castTop.eventually_gt_atTop (L*B),
    castTop.eventually_gt_atTop (A*(L*B)),castTop.eventually_gt_atTop (8*R*K^d)] with m hm h1 h2 h3
  intro ε a s hcount
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm' : (0:ℝ)<m := zero_lt_one.trans_le hmR
  have hm2 : (m:ℝ) ≤ (m:ℝ)^2 := by nlinarith only [sq_nonneg ((m:ℝ)-1),hmR]
  have hr : 0<ε := by dsimp only [ε]; positivity
  have hroot : (1:ℝ) < sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have hL' : L*ε < sqrt 2 := by
    apply lt_trans _ hroot
    change L*(B/(m:ℝ)^2)<1
    rw [←mul_div_assoc,div_lt_one (by positivity)]
    exact h1.trans_le hm2
  have hA' : A*(L*ε) < sqrt 2 := by
    apply lt_trans _ hroot
    change A*(L*(B/(m:ℝ)^2))<1
    rw [←mul_div_assoc,←mul_div_assoc,div_lt_one (by positivity)]
    exact h2.trans_le hm2
  let q := 1/(4*π*(m:ℝ)^2)
  have hq : 0<q := by dsimp only [q]; positivity
  have hD : (0:ℝ)<D := by dsimp only [D]; positivity
  have he : A*(L*ε)/2=K*q := by dsimp only [K,q,ε]; field_simp; ring
  have hfactor : R*(2*(D:ℝ)*(A*(L*ε)/2)^d) < (m:ℝ)*D/4*q^d := by
    rw [he,mul_pow]
    calc
      _ = (8*R*K^d)*((D:ℝ)/4*q^d) := by ring
      _ < (m:ℝ)*((D:ℝ)/4*q^d) := mul_lt_mul_of_pos_right h3 (by positivity)
      _ = _ := by ring
  filter_upwards [hs (L*ε) (mul_pos hL hr) hL' hA' a s hcount,hb m hm a] with T ht hl
  exact ((mul_lt_mul_of_pos_left ht.2 hR).trans hfactor).trans_le hl

/-- Arbitrarily late, a one-step path budget can beat every fixed
multiplicative enlargement of the empty-circuit error. -/
theorem gaussian_late_product_returns :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let J := Fintype.card (PathLabel (k+1))
      ∃ B > 0, ∀ L > 0, ∀ᶠ m : ℕ in atTop, ∀ a : ℝ, ∃ t ≥ a,
        t ∈ visitSet H J (B/(m:ℝ)^2) ∧ t ∉ visitSet H 0 (L*(B/(m:ℝ)^2)) := by
  filter_upwards [gaussian_linear_budget_occupation_transition] with ω hω k
  intro N H J
  obtain ⟨B,hB,h⟩ := hω k
  refine ⟨B,hB,?_⟩
  intro L hL
  filter_upwards [h L 1 hL zero_lt_one] with m hM
  intro a
  obtain ⟨T,hT,ht⟩ := ((hM a 0 (by dsimp only [N]; omega)).and (eventually_ge_atTop a)).exists
  rw [one_mul] at hT
  by_contra! hall
  apply hT.not_ge
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ht)
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  exact fun t hmem => ⟨hall t hmem.2.1 hmem.1,hmem.2⟩

#print axioms gaussian_linear_budget_occupation_transition
#print axioms gaussian_late_product_returns
end
end GaloisForLFunctions.HTGeometry.ShortTimeProducts
