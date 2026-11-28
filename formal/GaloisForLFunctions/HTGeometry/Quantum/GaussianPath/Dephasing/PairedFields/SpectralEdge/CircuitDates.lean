import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.PhysicalReadings
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.RestrictedNorm

/-! # Circuit tests on a spectral edge of a frozen Gaussian path -/

open Matrix Set Finset MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
open private wave from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.FrozenBasis
noncomputable section
private abbrev Index (n : ℕ) := Fin (n+2) → Bool

/-- The first r vectors of the base energy frame in descending order. -/
def firstRanks (I : Type*) [Fintype I] (r : ℕ) (hr : r ≤ Fintype.card I) : Finset I :=
  (univ : Finset (Fin r)).map ((Fin.castLEEmb hr).trans (eigenIndex I).toEmbedding)

theorem firstRanks_weight {I : Type*} [Fintype I] [DecidableEq I] (r : ℕ) (hr : r ≤ Fintype.card I) :
    rankWeight (firstRanks I r hr)=r^2 := by
  have h (j : I) : (preceding j).card+(insert j (preceding j)).card=2*((eigenIndex I).symm j).val+1 := by
    have hj : j∉preceding j := fun h => lt_irrefl _ (mem_Iio.mp (mem_map_equiv.mp h))
    rw [card_insert_of_notMem hj,preceding,card_map,Fin.card_Iio]
    omega
  have hs (k : ℕ) : ∑ i : Fin k, (2*i.val+1)=k^2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simpa only [Fin.val_castSucc,Fin.val_last,ih] using (by ring : k^2+(2*k+1)=(k+1)^2)
  simp only [rankWeight,firstRanks,sum_map,h]
  simpa only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Equiv.symm_apply_apply,Fin.coe_castLEEmb,Fin.val_castLE] using hs r

/-- One circuit must implement the affine phases on every superposition
of the selected base eigenvectors, in physical operator norm. -/
def edgeFit (n s : ℕ) (R : Finset (Index n)) (a b t ε : ℝ) : Set (FieldPair n) :=
  {x | ∃ c : ℂ, ‖c‖=1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount ≤ s ∧
    let U := (generator (base x)).2.isHermitian.eigenvectorUnitary
    let z := fun j => wave t (diagonalEnergy U (generator (rotated a b x)).val j)
    ‖(U.valᴴ*(c • C.eval.val)*U.val-diagonal z)*coordinateProjection R‖ ≤ ε}

private theorem fit_subspace {n : ℕ} (R : Finset (Index n)) (a b : ℝ) (x : FieldPair n)
    (t ε ρ : ℝ) (hρ : 0<ρ) (h : readingError R a b x t ≤ ρ^2/2)
    (C : TwoQubitCircuit (n+2)) (c : ℂ)
    (herr : ‖unitaryEvolution (generator (rotated a b x)).val t-c • C.eval.val‖ ≤ ε) :
    let U := (generator (base x)).2.isHermitian.eigenvectorUnitary
    let z := fun j => wave t (diagonalEnergy U (generator (rotated a b x)).val j)
    ‖(U.valᴴ*(c • C.eval.val)*U.val-diagonal z)*coordinateProjection R‖ ≤ ε+ρ := by
  intro U z
  let B := generator (rotated a b x)
  let V := unitaryEvolution B.val t
  let A := U.valᴴ*V*U.val
  let W := U.valᴴ*(c • C.eval.val)*U.val
  let P := coordinateProjection R
  have hA : A ∈ unitary _ := mul_mem (mul_mem (Unitary.star_mem U.2) (unitaryEvolution_mem_unitary B.2 t)) U.2
  have hz (j) : ‖z j‖=1 := by simp [z,wave,Complex.norm_exp]
  have hsq : ‖(A-diagonal z)*P‖^2 ≤ 2*readingError R a b x t := restricted_norm_sq R A hA z hz
  have hp : ‖(A-diagonal z)*P‖ ≤ ρ :=
    (sq_le_sq₀ (norm_nonneg _) hρ.le).mp (hsq.trans (by linarith only [h]))
  have hd : ‖W-A‖ ≤ ε := by
    dsimp only [W,A]
    rw [←Matrix.sub_mul,←Matrix.mul_sub,CStarRing.norm_mul_mem_unitary _ U.2,←Matrix.star_eq_conjTranspose,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem U.2),norm_sub_rev]
    exact herr
  have he : ‖(W-A)*P‖ ≤ ε :=
    (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (projection_norm_le R)).trans hd)
  change ‖(W-diagonal z)*P‖ ≤ ε+ρ
  rw [show (W-diagonal z)*P=(W-A)*P+(A-diagonal z)*P by rw [←add_mul,sub_add_sub_cancel]]
  exact (norm_add_le ..).trans (add_le_add he hp)

/-- At a physical date T the first r ranked phase tests have total
exceptional probability at most 8 m r² L²/(Tρ²), where m is the number
of physical coefficients and L is the independent phase displacement. -/
theorem physical_edge_circuit_date (n s r : ℕ) (hr : r ≤ Fintype.card (Index n))
    {T L ρ : ℝ} (hT : 0<T) (hL : |L| ≤ T) (hρ : 0<ρ) (ε : ℝ) :
    let b := L/T
    let a := Real.sqrt (1-b^2)
    let R := firstRanks (Index n) r hr
    pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹'
      BlockDilations.affordableDraw n s ε T) ≤ (pairLaw n).real (edgeFit n s R a b T (ε+ρ))+
        8*Fintype.card (PathLabel n)*(r:ℝ)^2*L^2/(T*ρ^2) := by
  intro b a R
  have hb : |b| ≤ 1 := by rwa [abs_div,abs_of_pos hT,div_le_one hT]
  have hb₂ : b^2 ≤ 1 := by simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have hab : a^2+b^2=1 := by rw [Real.sq_sqrt (sub_nonneg.mpr hb₂)]; ring
  have ha := Real.sqrt_nonneg (1-b^2)
  have ha' : a≤1 := (Real.sqrt_le_iff).mpr ⟨zero_le_one,by nlinarith only [sq_nonneg b]⟩
  have hsmall : 1-a≤b^2 := by nlinarith only [hab,mul_nonneg ha (sub_nonneg.mpr ha')]
  let A := BlockDilations.affordableDraw n s ε T
  let bad : Set (FieldPair n) := {x | ∃ u : ℝ, |u| ≤ T ∧ ρ^2/2<readingError R a b x u}
  have hm : MeasurableSet A := BlockDilations.measurable_affordableDraw ..
  have he : pathPauliDisorderLaw.real ((fun ω l => pathPauliDisorderShell ω n l) ⁻¹' A)=
      (pairLaw n).real (rotated a b ⁻¹' A) := by
    unfold Measure.real
    rw [(BlockDilations.prefix_measure n).measure_preimage hm.nullMeasurableSet,
      (rotated_law n hab).measure_preimage hm.nullMeasurableSet]
  rw [he]
  have hs : rotated a b ⁻¹' A ⊆ edgeFit n s R a b T (ε+ρ) ∪ bad := by
    rintro x ⟨c,hc,C,hsize,herr⟩
    by_cases h : ρ^2/2<readingError R a b x T
    · exact Or.inr ⟨T,(abs_of_pos hT).le,h⟩
    · exact Or.inl ⟨c,hc,C,hsize,fit_subspace R a b x T ε ρ hρ (le_of_not_gt h) C c herr⟩
  apply (measureReal_mono hs).trans ((measureReal_union_le ..).trans (add_le_add le_rfl ?_))
  have hρ₂ : 0<ρ^2/2 := by positivity
  apply (gaussian_ranked_readings n R hab hT hρ₂).trans
  rw [firstRanks_weight,Nat.cast_pow]
  calc
    _ ≤ 4*T*b^2*(r:ℝ)^2*Fintype.card (PathLabel n)/(ρ^2/2) := by gcongr
    _ = _ := by dsimp only [b]; field_simp; ring

#print axioms physical_edge_circuit_date
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
