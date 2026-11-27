import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Carrier
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.PhaseCost
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Incident

/-! # Cheap physical increments near a conserved central spin -/
open Set Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds.SingleCut DiagonalSynthesis
open private numberedGenerator_continuous from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.WindowEvent
noncomputable section
variable {n : ℕ}

/-- The residual norm is at most 14/(1800√T). A gap of two pays for
both endpoint rotations and the accumulated quadratic phase error. -/
private theorem quadratic_error {s v g t : ℝ} (hs : 1 ≤ s) (hv : 0 ≤ v) (hg : 2 < g)
    (hb : v ≤ 14*(1/(1800*s))) (ht : |t| ≤ s^2) : (2+|t| * v)*(v/(2*g)) ≤ 1/200 := by
  have hs₀ := zero_lt_one.trans_le hs
  have hvs : v*s ≤ 1/120 := by
    have he : 14*(1/(1800*s))*s=14/1800 := by field_simp
    exact ((mul_le_mul_of_nonneg_right hb hs₀.le).trans_eq he).trans (by norm_num)
  have hv₁ : v ≤ 1/120 := (le_mul_of_one_le_right hv hs).trans hvs
  have hsq := pow_le_pow_left₀ (mul_nonneg hv hs₀.le) hvs 2
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by linarith only [hg] : 0 < 2*g)).mpr
  nlinarith only [hsq,hv₁,hg,mul_le_mul_of_nonneg_right ht (sq_nonneg v)]

/-- In a fixed neighbourhood with all longitudinal bonds strong,
shrinking only the transverse coordinates gives the two half-chain
phase budgets on the full interval |t| ≤ T. -/
theorem cheap_central_neighborhood {a b : Fin (n+1)} (hab : a.succ=b.castSucc)
    (hL : 2 ≤ (Finset.Iic a.succ).card) (hR : 2 ≤ (Finset.Ici a.succ).card) :
    ∃ x₀ : PrefixIndex n→ℝ, ∃ r > (0:ℝ),
      (∀ l∈transverseLabels a b, x₀ ((pathCoeffEquiv n).symm l)=0) ∧
      (∀ e : Fin (n+1), x₀ ((pathCoeffEquiv n).symm (.inr (e,(2,2))))=1) ∧
      ∀ (u : PathShell n), (∀ i, |u (pathCoeffEquiv n i)-x₀ i| < r) →
        ∀ T ≥ (1:ℝ), (∀ l∈transverseLabels a b, |u l| ≤ 1/(1800*Real.sqrt T)) →
        ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation (n+2) (1/100)
          (blockCost (Finset.Iic a.succ).card+blockCost (Finset.Ici a.succ).card)
          (unitaryEvolution (pathHamiltonian u) t) := by
  classical
  let q := a.succ
  obtain ⟨w,h,_,d,hd,hw,hcw,hg,_,hedge,hoz⟩ := exists_gapped_carrier q
  let x₀ := fun i => w (pathCoeffEquiv n i)
  let mask (x : PrefixIndex n→ℝ) (i : PrefixIndex n) :=
    if axial q (pathCoeffEquiv n i) then x i else 0
  let D := (numberedGenerator n) ∘ mask
  have hc : Continuous D := (numberedGenerator_continuous n).comp (continuous_pi fun i => by
    by_cases hi : axial q (pathCoeffEquiv n i)
    · simpa only [mask,if_pos hi] using (continuous_apply i : Continuous (fun x : PrefixIndex n→ℝ => x i))
    · simpa only [mask,if_neg hi] using (continuous_const : Continuous (fun _ : PrefixIndex n→ℝ => (0:ℝ))))
  have hD (u : PathShell n) : D (fun i => u (pathCoeffEquiv n i))=pathHamiltonian (core q u) := by
    rw [←numberedGenerator_shell (core q u)]
    apply congrArg (numberedGenerator n)
    funext i
    by_cases hi : axial q (pathCoeffEquiv n i)
    · exact (if_pos hi).trans (restricted_eq u hi).symm
    · exact (if_neg hi).trans (restricted_zero u hi).symm
  have hbase : D x₀=diagonal d := by rw [hD w,hcw,hw]
  have hlim : Tendsto D (𝓝 x₀) (𝓝 (diagonal d)) := hbase ▸ hc.continuousAt
  have hcost := hlim.eventually (eventual_conserved_cost a hL hR d hd (by norm_num : (0:ℝ) < 1/200))
  have hgap : ∀ᶠ x in 𝓝 x₀, ‖D x-h • spin q‖+2 < h := by
    apply (isOpen_lt ((hc.sub continuous_const).norm.add continuous_const) continuous_const).mem_nhds
    change ‖D x₀-h • spin q‖+2 < h
    rwa [hbase,←hw]
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hcost.and hgap)
  refine ⟨x₀,r,hr,?_,fun e => by simpa only [x₀,Equiv.apply_symm_apply] using hedge e,?_⟩
  · intro l hl
    simp only [x₀,Equiv.apply_symm_apply]
    apply hoz
    rcases Finset.mem_union.mp hl with hl|hl
    · rcases Finset.mem_union.mp hl with hl|hl
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hl
        exact (Finset.mem_erase.mp hp).1
      · obtain ⟨⟨p,j⟩,hp,rfl⟩ := Finset.mem_image.mp hl
        exact fun he => (Finset.mem_erase.mp (Finset.mem_product.mp hp).2).1 (congrArg Prod.snd he)
    · obtain ⟨⟨p,j⟩,hp,rfl⟩ := Finset.mem_image.mp hl
      exact fun he => (Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1 (congrArg Prod.fst he)
  · intro u hu T hT hδ t ht
    let x := fun i => u (pathCoeffEquiv n i)
    have hx : x∈Metric.ball x₀ r := Metric.mem_ball.mpr ((dist_pi_lt_iff hr).mpr
      fun i => by simpa only [Real.dist_eq] using hu i)
    obtain ⟨hc₀,hgap⟩ := hball hx
    have href := hc₀ (core q u) (hD u) (core_longitudinal q u) t
    rw [hD u] at hgap href
    have hg' : 2 < h-‖pathHamiltonian (core q u)-h • spin q‖ := by linarith only [hgap]
    have herr := core_evolution_bound q u h (by linarith only [hgap]) t
    let V := pathHamiltonian (offAxis q u)
    have hs : 1 ≤ Real.sqrt T := (Real.one_le_sqrt).mpr hT
    have hnorm := offAxis_norm hab u (by positivity : 0 ≤ 1/(1800*Real.sqrt T)) hδ
    have hb := quadratic_error hs (norm_nonneg V) hg' hnorm
      (ht.trans_eq (Real.sq_sqrt (zero_le_one.trans hT)).symm)
    obtain ⟨z,hz,C,hC,hfit⟩ := href
    refine ⟨z,hz,C,hC,?_⟩
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add (herr.trans hb) hfit).trans_eq (by norm_num))

#print axioms cheap_central_neighborhood
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
