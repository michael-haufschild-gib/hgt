import GaloisForLFunctions.RHTower.WeilLogShiftFiniteKernelClassification
import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticDomain
import GaloisForLFunctions.HTGeometry.WignerSmithFiniteResolutionLawEscape

/-!
# Exact finite reconstruction from actual paired-log kernel samples

The arithmetic tail has no finite invisible direction. Every finite packet
admits an invertible sampling map, with stability controlled by its inverse.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

/-- Removing the forced arithmetic head removes the entire finite kernel. -/
theorem linearIndependent_pairedLogKernel_tail :
    LinearIndependent ℝ (fun n : ℕ => fun y : ℝ => pairedLogKernel y (n + 2)) := by
  rw [linearIndependent_iff]
  intro d hd
  let v := d.mapDomain (fun n : ℕ => n + 2)
  have hv : ∀ y : ℝ, v.sum (fun n c => c * pairedLogKernel y n) = 0 := by
    intro y
    dsimp only [v]
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _)
      (fun _ _ _ => add_mul _ _ _)]
    have h := congrFun hd y
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply] using h
  have htail := (finite_pairedLogKernel_sum_eq_zero_iff v).mp hv
  ext n
  have h := htail.2 (n + 2) (by omega)
  simpa only [v, Finsupp.mapDomain_apply (show Function.Injective
    (fun n : ℕ => n + 2) from fun _ _ h => Nat.add_right_cancel h),
    Finsupp.zero_apply] using h

/-- Exactly one real sample per coefficient gives a continuous linear
equivalence, hence both exact interpolation and stable reconstruction. -/
theorem exists_finite_pairedLogKernel_sampling (s : Finset ℕ) :
    ∃ (y : s → ℝ) (T : (s → ℝ) ≃L[ℝ] (s → ℝ)),
      (∀ (c : s → ℝ) (j : s),
        T c j = ∑ i : s, c i * pairedLogKernel (y j) ((i : ℕ) + 2)) ∧
      ∀ c d : s → ℝ,
        ‖c - d‖ ≤ ‖T.symm.toContinuousLinearMap‖ *
          ‖fun j : s => ∑ i : s, (c i - d i) *
            pairedLogKernel (y j) ((i : ℕ) + 2)‖ := by
  classical
  have hlin := linearIndependent_pairedLogKernel_tail.comp
    (fun i : s => (i : ℕ)) Subtype.val_injective
  obtain ⟨y, hy⟩ :=
    GaloisForLFunctions.HTGeometry.exists_fullRank_real_evaluation_packet _ hlin
  let M : Matrix s s ℝ := Matrix.of fun j i => pairedLogKernel (y j) ((i : ℕ) + 2)
  have hM : IsUnit M := hy
  have hb : Function.Bijective (Matrix.toLin' M) :=
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hM,
      Matrix.mulVec_surjective_iff_isUnit.mpr hM⟩
  let T := (LinearEquiv.ofBijective (Matrix.toLin' M) hb).toContinuousLinearEquiv
  have hT (c : s → ℝ) (j : s) :
      T c j = ∑ i : s, c i * pairedLogKernel (y j) ((i : ℕ) + 2) := by
    change M.mulVec c j = _
    simp [M, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨y, T, hT, ?_⟩
  intro c d
  have h := T.symm.toContinuousLinearMap.le_opNorm (T (c - d))
  have hsum : T (c - d) = fun j : s => ∑ i : s, (c i - d i) *
      pairedLogKernel (y j) ((i : ℕ) + 2) := by
    funext j
    exact hT (c - d) j
  have hbound : ‖c - d‖ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (c - d)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply] using h
  simpa only [hsum] using hbound

/-- The sample count above is minimal: no choice of fewer shifts can give
an injective sampling map. -/
theorem finite_pairedLogKernel_sampling_card_bound
    (s : Finset ℕ) (m : ℕ) (y : Fin m → ℝ) :
    Function.Injective (fun c : s → ℝ => fun j : Fin m =>
      ∑ i : s, c i * pairedLogKernel (y j) ((i : ℕ) + 2)) → s.card ≤ m := by
  classical
  intro h
  let M : Matrix (Fin m) s ℝ :=
    Matrix.of fun j i => pairedLogKernel (y j) ((i : ℕ) + 2)
  have hM : Function.Injective (Matrix.toLin' M) := by
    intro c d hcd
    apply h
    funext j
    have hj := congrFun hcd j
    simpa [Matrix.toLin'_apply, M, Matrix.mulVec, dotProduct, mul_comm] using hj
  have hdim := LinearMap.finrank_le_finrank_of_injective hM
  simpa only [Module.finrank_pi, Fintype.card_coe, Fintype.card_fin] using hdim

/-- A finite arithmetic packet, supported entirely above the forced head. -/
def finiteWeilPacket (s : Finset ℕ) (c : s → ℝ) : ℕ →₀ ℝ :=
  ∑ i : s, Finsupp.single ((i : ℕ) + 2) (c i)

theorem finiteWeilPacket_head (s : Finset ℕ) (c : s → ℝ) (n : ℕ) (hn : n < 2) :
    finiteWeilPacket s c n = 0 := by
  classical
  simp only [finiteWeilPacket, Finsupp.finsetSum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (by omega)

theorem finiteWeilPacket_synthesis (s : Finset ℕ) (c : s → ℝ) (y : ℝ) :
    (finiteWeilPacket s c).sum (fun n a => a * pairedLogKernel y n) =
      ∑ i : s, c i * pairedLogKernel y ((i : ℕ) + 2) := by
  classical
  unfold finiteWeilPacket
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)]
  apply Finset.sum_congr rfl
  intro i _
  exact Finsupp.sum_single_index (zero_mul _)

/-- The finite receiver uses the literal arithmetic series and records its
convergence, not merely an equality of totalized infinite sums. -/
theorem hasSum_finiteWeilPacket_deviation (s : Finset ℕ) (c : s → ℝ) (y : ℝ) :
    HasSum (fun n : ℕ => weilDeviation (weilCoefficientLift (finiteWeilPacket s c)) n *
      pairedLogKernel y n)
      (∑ i : s, c i * pairedLogKernel y ((i : ℕ) + 2)) := by
  classical
  have hdev (n : ℕ) :
      weilDeviation (weilCoefficientLift (finiteWeilPacket s c)) n =
        finiteWeilPacket s c n := by
    rw [weilDeviation_coefficientLift]
    split_ifs with hn
    · rfl
    · exact (finiteWeilPacket_head s c n (by omega)).symm
  simp_rw [hdev]
  rw [← finiteWeilPacket_synthesis]
  exact hasSum_sum_of_ne_finset_zero (s := (finiteWeilPacket s c).support)
    (fun n hn => by rw [Finsupp.notMem_support_iff.mp hn, zero_mul])

/-- A single finite set of shifts reconstructs every arithmetic packet,
with an explicit inverse-operator stability constant. -/
theorem exists_finiteWeilPacket_reconstruction (s : Finset ℕ) :
    ∃ (y : s → ℝ) (T : (s → ℝ) ≃L[ℝ] (s → ℝ)),
      (∀ (c : s → ℝ) (j : s),
        HasSum (fun n : ℕ => weilDeviation
          (weilCoefficientLift (finiteWeilPacket s c)) n * pairedLogKernel (y j) n)
          (T c j)) ∧
      (∀ b : s → ℝ, ∃! c : s → ℝ, ∀ j : s,
        HasSum (fun n : ℕ => weilDeviation
          (weilCoefficientLift (finiteWeilPacket s c)) n * pairedLogKernel (y j) n)
          (b j)) ∧
      ∀ c d : s → ℝ,
        ‖c - d‖ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T c - T d‖ := by
  obtain ⟨y, T, hT, _⟩ := exists_finite_pairedLogKernel_sampling s
  have hvalue (c : s → ℝ) (j : s) :
      HasSum (fun n : ℕ => weilDeviation
        (weilCoefficientLift (finiteWeilPacket s c)) n * pairedLogKernel (y j) n)
        (T c j) := by
    rw [hT]
    exact hasSum_finiteWeilPacket_deviation s c (y j)
  refine ⟨y, T, hvalue, ?_, ?_⟩
  · intro b
    refine ⟨T.symm b, ?_, ?_⟩
    · intro j
      simpa only [T.apply_symm_apply] using hvalue (T.symm b) j
    · intro c hc
      apply T.injective
      rw [T.apply_symm_apply]
      funext j
      exact (hvalue c j).unique (hc j)
  · intro c d
    have h := T.symm.toContinuousLinearMap.le_opNorm (T (c - d))
    simpa only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply, map_sub] using h

end RHTower
