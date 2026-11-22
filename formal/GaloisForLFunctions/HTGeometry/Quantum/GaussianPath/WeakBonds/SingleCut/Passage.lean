import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.HalfBudget
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.DisorderTails

/-! # Survival of the actual first excursion at one small middle bond -/
open MeasureTheory Filter Real Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
noncomputable section
open DiagonalSynthesis
open PrescribedTimes

def bondIndex {n : ℕ} (a : Fin (n+1)) (ab : Fin 3 × Fin 3) := (pathCoeffEquiv n).symm (Sum.inr (a,ab))
def bondSites {n : ℕ} (a : Fin (n+1)) := Finset.univ.image (bondIndex a)

theorem bondSites_card {n : ℕ} (a : Fin (n+1)) : (bondSites a).card=9 := by
  have hi : Function.Injective (bondIndex a) := fun _ _ h =>
    (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv n).symm.injective h))).2
  rw [bondSites,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]

private theorem weak_error {n : ℕ} (u : PathShell n) (a : Fin (n+1)) {T : ℝ} (hT : 0 < T)
    (hs : ∀ i∈bondSites a, |u (pathCoeffEquiv n i)| ≤ 1/(1800*T)) (t : ℝ) (ht : |t| ≤ T) :
    ‖unitaryEvolution (pathHamiltonian u) t-unitaryEvolution (pathHamiltonianCut u a) t‖ ≤ 1/200 := by
  have hn : ‖edgePart u a‖ ≤ 9*(1/(1800*T)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _ : Fin 3 × Fin 3, (1/(1800*T)) := Finset.sum_le_sum fun ab _ => by
        rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one]
        simpa only [bondIndex,Equiv.apply_symm_apply] using hs (bondIndex a ab) (Finset.mem_image.mpr ⟨ab,Finset.mem_univ _,rfl⟩)
      _ = _ := by simp [nsmul_eq_mul]
  have h := norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian u) (isSelfAdjoint_pathHamiltonianCut u a) t
  rw [pathHamiltonian_sub_cut] at h
  exact h.trans ((mul_le_mul ht hn (norm_nonneg _) hT.le).trans_eq (by field_simp; ring))

/-- For any positive onsite scale, a fixed neighborhood of the uncut
coordinates and a middle bond of size O(1/T) delay the first crossing
and every half-budget first return by at least T. -/
theorem gaussian_middle_bond_delays {A : ℝ} (hA : 0 < A) :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let x₀ := fun i => sepCarrier n A 0 (pathCoeffEquiv n i)
      ∃ a : Fin (n+1), ∃ r > (0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw,
        let x := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
        ∀ T > (0:ℝ), (∀ i, |x i-x₀ i| < r) → (∀ i∈bondSites a, |x i| ≤ 1/(1800*T)) →
          T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x := by
  have hent := (tendsto_add_atTop_nat 3).eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier
  filter_upwards [hent,eventually_ge_atTop 64] with k hent hk
  intro n P x₀
  obtain ⟨a,hL,hR,hcost⟩ := affordable_middle_edge n (by dsimp [n]; omega)
  obtain ⟨r,hr,hcut⟩ := cut_neighborhood a hL hR hA (by norm_num : (0:ℝ)<1/200)
  refine ⟨a,r,hr,?_⟩
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro x T hT hx hw
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Register (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
  let d := 2^(n+2)-1
  let e : (Fin (n+2)→Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hd : 0 < (2:ℕ)^(n+2) := by positivity
                  dsimp [d]; omega))
  have hinc (t : ℝ) (ht : |t| ≤ T) : HasProjectiveCircuitApproximation (n+2) (1/100:ℝ)
      (blockCost (leftBlock a).card+blockCost (rightBlock a).card) (unitaryEvolution H.val t) := by
    obtain ⟨z,hz,C,hC,herr⟩ := hcut u hx t
    refine ⟨z,hz,C,hC,?_⟩
    have h := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H.val t) (unitaryEvolution (pathHamiltonianCut u a) t) (z • C.eval.val)
    exact h.trans ((add_le_add (weak_error u a hT hw t ht) herr).trans_eq (by norm_num))
  obtain ⟨σ,hσ,hd,hpre,hnone,_⟩ := first_circuit_threshold_of_increment e H
    ((hω k).comp_equiv e.symm) hent T hT.le hcost hinc
  have hdist (j : ℕ) (t : ℝ) : pathGateDistance n j x t=orbitCircuitDistance H j t := by
    change pathGateDistance n j (fun i => u (pathCoeffEquiv n i)) t=_
    rw [pathGateDistance,numberedGenerator_shell]; rfl
  have ho := crossingOrigin_eq_of_first (hT.trans hσ).le ((hdist P σ).trans hd)
    (fun t ht => (hdist P t).trans_lt (hpre t ht))
  refine ⟨ho.symm ▸ hσ,fun s hs => ?_⟩
  by_contra! h
  obtain ⟨t,ht,hvisit⟩ := (crossingWait_le_iff n P s x T).mp h
  rw [ho] at ht
  obtain ⟨z,hz,C,hC,he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr ((hdist s t).symm.trans_le hvisit)
  exact (hnone t ⟨(sub_le_self σ hT.le).trans ht.1,ht.2⟩ z hz C (hC.trans hs)).not_ge he

#print axioms gaussian_middle_bond_delays
end
end GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
