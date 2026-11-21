import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ArcLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.BudgetOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw

/-! # Cheap circuits along arithmetic samples of a fixed Gaussian chain -/
open Filter MeasureTheory Set Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling
noncomputable section
open SharpOccupation

/-- An s-gate net pays the Haar arc mass for all but one of the energies.
One and the same nonzero step may be chosen using the entire Hamiltonian. -/
theorem finite_circuit_bound {n : ℕ} (hn : 0 < n) (H : selfAdjoint (Register n))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) (s : ℕ)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hy : y < 1/2) (a τ : ℝ) (hτ : τ ≠ 0)
    (b : ℝ) (hb : let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
      ((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s*zeroGateArcDensity (2^n-1) y < b) :
    ∀ᶠ M : ℕ in atTop, (timeLaw a τ M).real (visitSet H s (zeroGateArcTolerance x)) < b := by
  classical
  let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
  have hδ : 0 < δ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance
    ⟨hx,(hxy.trans hy).le⟩ ⟨hx.trans hxy.le,hy.le⟩ hxy)
  obtain ⟨F,hcover,hcard⟩ := exists_budget_net n s δ hδ
  choose ψ hψ using unitary_visits_subset_shifted H
  let E := fun j => -H.2.isHermitian.eigenvalues j
  let i : Fin n → Bool := fun _ => false
  letI : Nonempty {j : Fin n → Bool // j ≠ i} :=
    ⟨⟨fun _ => true,fun h => (by decide : true ≠ false) (congrFun h ⟨0,hn⟩)⟩⟩
  obtain ⟨v,hv⟩ := exists_arc_majorant E (maximallyProjectiveEnergy_neg hmax) i τ hτ
  let r : Icc (0:ℝ) (1/2) := ⟨y,hx.trans hxy.le,hy.le⟩
  let B (w : F) := retainedArcTimes i v E (fun j => -ψ w.val j) y
  have hsub : visitSet H s (zeroGateArcTolerance x) ⊆ ⋃ w : F, B w := by
    rintro t ⟨c,hc,C,hC,he⟩
    obtain ⟨W,hW,hclose⟩ := hcover C hC
    refine mem_iUnion.mpr ⟨⟨W,hW⟩,(hv (fun j => -ψ W j) r a).1 ?_⟩
    have htri := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H.val t)
      (c • (C.eval : Register n)) (c • (W : Register n))
    rw [←smul_sub,norm_smul,hc,one_mul] at htri
    have h := hψ W y (hx.trans hxy.le) hy t c hc
      (htri.trans ((add_le_add he hclose).trans_eq (by dsimp [δ]; ring)))
    simpa only [arcTimes,shiftedTimes,E,r,mem_setOf_eq,mul_neg,sub_eq_add_neg] using h
  let p := zeroGateArcDensity (2^n-1) y
  have ht (w : F) : Tendsto (fun M => (timeLaw a τ M).real (B w)) atTop (𝓝 p) := by
    simpa only [B,p,r,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using
      (hv (fun j => -ψ w.val j) r a).2
  have hsum := tendsto_finsetSum Finset.univ (fun w _ => ht w)
  have hlim : Tendsto (fun M => ∑ w : F, (timeLaw a τ M).real (B w)) atTop (𝓝 ((F.card:ℝ)*p)) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using hsum
  have hp : 0 ≤ p := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hx.trans hxy.le) _)
  filter_upwards [hlim.eventually_lt_const ((mul_le_mul_of_nonneg_right hcard hp).trans_lt hb)] with M hm
  exact ((measureReal_mono (μ := timeLaw a τ M) hsub).trans (measureReal_iUnion_fintype_le B)).trans_lt hm

/-- Almost surely, on every prefix the quantitative finite-net bound holds
for all lattice origins and periods simultaneously. -/
theorem gaussian_adaptive_circuit_bound :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let n := k+3
      let H : selfAdjoint (Register n) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ (s : ℕ) (x y : ℝ), 0 ≤ x → x < y → y < 1/2 → ∀ a τ : ℝ, τ ≠ 0 → ∀ b : ℝ,
        (let δ := zeroGateArcTolerance y-zeroGateArcTolerance x
         ((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s*zeroGateArcDensity (2^n-1) y < b) →
        ∀ᶠ M : ℕ in atTop, (timeLaw a τ M).real (visitSet H s (zeroGateArcTolerance x)) < b := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro k n H s x y hx hxy hy a τ hτ b hb
  exact finite_circuit_bound (by dsimp [n]; omega) H (hω k) s hx hxy hy a τ hτ b hb

#print axioms gaussian_adaptive_circuit_bound
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling
