import GaloisForLFunctions.HTGeometry.FiniteUnitaryEnergyDefectLaw

/-!
# Choi shortcut to energy-defect law

For a Hermitian source with bounded spectral fourth moment, high normalized-trace fidelity of a
unitary shortcut to any commuting autonomous target forces that shortcut into the gap-free
half-energy commutator tube.  The proof is an exact transport inequality for the unistochastic
coupling formed by the shortcut in the source eigenbasis; no minimum spectral gap or operator-norm
comparison enters.
-/

open scoped BigOperators Matrix ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem fourth_power_sub_le (a b : ℝ) :
    (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a - b),
    sq_nonneg (a ^ 2 - b ^ 2)]

theorem doublyStochastic_quadraticTransport_sq_le_offDiag_fourth
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (w : ι → ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = 1)
    (hcol : ∀ j, ∑ i, w i j = 1) :
    (∑ i, ∑ j, (s i - s j) ^ 2 * w i j) ^ 2 ≤
      16 * (∑ i, ∑ j, if i = j then 0 else w i j) *
        (∑ i, s i ^ 4) := by
  let f : ι × ι → ℝ := fun p => (s p.1 - s p.2) ^ 2 * w p.1 p.2
  let g : ι × ι → ℝ := fun p => if p.1 = p.2 then 0 else w p.1 p.2
  let h : ι × ι → ℝ := fun p => (s p.1 - s p.2) ^ 4 * w p.1 p.2
  have hg : ∀ p ∈ (Finset.univ : Finset (ι × ι)), 0 ≤ g p := by
    intro p _hp
    simp only [g]
    split_ifs
    · exact le_rfl
    · exact hw _ _
  have hh : ∀ p ∈ (Finset.univ : Finset (ι × ι)), 0 ≤ h p := by
    intro p _hp
    exact mul_nonneg (by positivity) (hw _ _)
  have hpoint : ∀ p ∈ (Finset.univ : Finset (ι × ι)),
      f p ^ 2 ≤ g p * h p := by
    intro p _hp
    by_cases hpq : p.1 = p.2
    · simp [f, g, h, hpq]
    · simp [f, g, h, hpq]
      ring_nf
      exact le_rfl
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (ι × ι)) hg hh hpoint
  have hfourth : (∑ p : ι × ι, h p) ≤ 16 * ∑ i, s i ^ 4 := by
    calc
      (∑ p : ι × ι, h p) = ∑ i, ∑ j, (s i - s j) ^ 4 * w i j := by
        simp only [h, Fintype.sum_prod_type]
      _ ≤ ∑ i, ∑ j, (8 * (s i ^ 4 + s j ^ 4)) * w i j := by
        apply Finset.sum_le_sum
        intro i _hi
        apply Finset.sum_le_sum
        intro j _hj
        exact mul_le_mul_of_nonneg_right (fourth_power_sub_le (s i) (s j)) (hw i j)
      _ = 16 * ∑ i, s i ^ 4 := by
        calc
          _ = 8 * (∑ i, ∑ j, (s i ^ 4 + s j ^ 4) * w i j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _hj
                ring
          _ = 8 * ((∑ i, ∑ j, s i ^ 4 * w i j) +
              ∑ i, ∑ j, s j ^ 4 * w i j) := by
                congr 1
                simp_rw [add_mul, Finset.sum_add_distrib]
          _ = 8 * ((∑ i, s i ^ 4) + ∑ j, s j ^ 4) := by
                congr 1
                · apply congrArg₂ (· + ·)
                  · apply Finset.sum_congr rfl
                    intro i _hi
                    rw [← Finset.mul_sum, hrow, mul_one]
                  · rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro j _hj
                    rw [← Finset.mul_sum, hcol, mul_one]
          _ = _ := by ring
  have hnonneg : 0 ≤ ∑ p : ι × ι, g p := Finset.sum_nonneg fun p _ => hg p (Finset.mem_univ p)
  calc
    (∑ i, ∑ j, (s i - s j) ^ 2 * w i j) ^ 2 =
        (∑ p : ι × ι, f p) ^ 2 := by simp only [f, Fintype.sum_prod_type]
    _ ≤ (∑ p : ι × ι, g p) * ∑ p : ι × ι, h p := hcs
    _ ≤ (∑ p : ι × ι, g p) * (16 * ∑ i, s i ^ 4) :=
      mul_le_mul_of_nonneg_left hfourth hnonneg
    _ = 16 * (∑ i, ∑ j, if i = j then 0 else w i j) *
        (∑ i, s i ^ 4) := by
      simp only [g, Fintype.sum_prod_type]
      ring

theorem normSq_sum_le_card_mul_sum_normSq
    {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    Complex.normSq (∑ i, z i) ≤
      (Fintype.card ι : ℝ) * ∑ i, Complex.normSq (z i) := by
  rw [← Complex.sq_norm]
  have hnorm : ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := norm_sum_le _ _
  have hsq : (∑ i, ‖z i‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, ‖z i‖ ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) (fun i => ‖z i‖))
  calc
    ‖∑ i, z i‖ ^ 2 ≤ (∑ i, ‖z i‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg (z i))).2 hnorm
    _ ≤ _ := hsq
    _ = _ := by simp_rw [Complex.sq_norm]

theorem sum_offDiag_finiteUnitaryEntryWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    (∑ i, ∑ j, if i = j then 0 else finiteUnitaryEntryWeight U i j) =
      (Fintype.card ι : ℝ) - ∑ i, finiteUnitaryEntryWeight U i i := by
  calc
    _ = (∑ i, ∑ j, finiteUnitaryEntryWeight U i j) -
        ∑ i, ∑ j, if i = j then finiteUnitaryEntryWeight U i j else 0 := by
      simp_rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      split_ifs <;> ring
    _ = (∑ i, ∑ j, finiteUnitaryEntryWeight U i j) -
        ∑ i, finiteUnitaryEntryWeight U i i := by simp
    _ = _ := by simp_rw [sum_finiteUnitaryEntryWeight_row]; simp

theorem finiteUnitaryDiagonal_commutatorEnergy_eq_transport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (U : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (Matrix.diagonal (fun i => (s i : ℂ)) * (U : Matrix ι ι ℂ) -
          (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (s i : ℂ))) =
      ∑ i, ∑ j, (s i - s j) ^ 2 * finiteUnitaryEntryWeight U j i := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [finiteUnitaryEntryWeight, Complex.normSq_apply]
  ring

theorem finiteUnitaryDiagonal_commutatorEnergy_sq_le_fourthMoment_traceDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (U : Matrix.unitaryGroup ι ℂ) :
    (Fintype.card ι : ℝ) *
        finiteMatrixHilbertSchmidtEnergy
          (Matrix.diagonal (fun i => (s i : ℂ)) * (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (s i : ℂ))) ^ 2 ≤
      16 * ((Fintype.card ι : ℝ) ^ 2 -
        Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ))) *
        (∑ i, s i ^ 4) := by
  let E := ∑ i, ∑ j, (s i - s j) ^ 2 * finiteUnitaryEntryWeight U j i
  let Q := ∑ i, ∑ j, if i = j then 0 else finiteUnitaryEntryWeight U j i
  let S4 := ∑ i, s i ^ 4
  have htransport : E ^ 2 ≤ 16 * Q * S4 := by
    exact doublyStochastic_quadraticTransport_sq_le_offDiag_fourth s
      (fun i j => finiteUnitaryEntryWeight U j i)
      (fun i j => Complex.normSq_nonneg ((U : Matrix ι ι ℂ) j i))
      (sum_finiteUnitaryEntryWeight_column U)
      (sum_finiteUnitaryEntryWeight_row U)
  have hdiag : Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ)) ≤
      (Fintype.card ι : ℝ) * ∑ i, finiteUnitaryEntryWeight U i i := by
    simpa [Matrix.trace, finiteUnitaryEntryWeight, Complex.sq_norm] using
      (normSq_sum_le_card_mul_sum_normSq (fun i => (U : Matrix ι ι ℂ) i i))
  have hQ : (Fintype.card ι : ℝ) * Q ≤
      (Fintype.card ι : ℝ) ^ 2 -
        Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ)) := by
    rw [show Q = (Fintype.card ι : ℝ) -
      ∑ i, finiteUnitaryEntryWeight U i i from by
        change (∑ i, ∑ j, if i = j then 0 else finiteUnitaryEntryWeight U j i) = _
        rw [Finset.sum_comm]
        simpa [eq_comm] using sum_offDiag_finiteUnitaryEntryWeight U]
    nlinarith
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun i _ => by positivity
  rw [finiteUnitaryDiagonal_commutatorEnergy_eq_transport]
  change (Fintype.card ι : ℝ) * E ^ 2 ≤
    16 * ((Fintype.card ι : ℝ) ^ 2 -
      Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ))) * S4
  calc
    (Fintype.card ι : ℝ) * E ^ 2 ≤
        (Fintype.card ι : ℝ) * (16 * Q * S4) :=
      mul_le_mul_of_nonneg_left htransport hcard
    _ = 16 * ((Fintype.card ι : ℝ) * Q) * S4 := by ring
    _ ≤ 16 * ((Fintype.card ι : ℝ) ^ 2 -
        Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ))) * S4 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ (by norm_num)) hS4

theorem finiteUnitary_trace_normSq_le_card_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ)) ≤
      (Fintype.card ι : ℝ) ^ 2 := by
  have hdiag : Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ)) ≤
      (Fintype.card ι : ℝ) * ∑ i, finiteUnitaryEntryWeight U i i := by
    simpa [Matrix.trace, finiteUnitaryEntryWeight, Complex.sq_norm] using
      (normSq_sum_le_card_mul_sum_normSq (fun i => (U : Matrix ι ι ℂ) i i))
  have hone (i : ι) : finiteUnitaryEntryWeight U i i ≤ 1 := by
    calc
      finiteUnitaryEntryWeight U i i ≤ ∑ j, finiteUnitaryEntryWeight U i j := by
        exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg ((U : Matrix ι ι ℂ) i j))
          (Finset.mem_univ i)
      _ = 1 := sum_finiteUnitaryEntryWeight_row U i
  have hsum : (∑ i, finiteUnitaryEntryWeight U i i) ≤ (Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => hone i
      _ = _ := by simp
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  calc
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, finiteUnitaryEntryWeight U i i := hdiag
    _ ≤ (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) :=
      mul_le_mul_of_nonneg_left hsum hcard
    _ = _ := by ring

/-- A fourth-moment bound converts high Choi trace fidelity into the half-energy
approximate-centralizer tube, without an operator-norm or spectral-gap loss. -/
theorem finiteUnitaryDiagonal_commutatorEnergy_le_traceEnergy_of_kurtosis
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (s : ι → ℝ) (U : Matrix.unitaryGroup ι ℂ) (κ : ℝ)
    (hkurt : (Fintype.card ι : ℝ) * (∑ i, s i ^ 4) ≤
      κ * (∑ i, s i ^ 2) ^ 2)
    (hfidelity : 16 * κ *
        ((Fintype.card ι : ℝ) ^ 2 -
          Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ))) ≤
      (Fintype.card ι : ℝ) ^ 2) :
    finiteMatrixHilbertSchmidtEnergy
        (Matrix.diagonal (fun i => (s i : ℂ)) * (U : Matrix ι ι ℂ) -
          (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (s i : ℂ))) ≤
      ∑ i, s i ^ 2 := by
  let D : ℝ := Fintype.card ι
  let E : ℝ := finiteMatrixHilbertSchmidtEnergy
    (Matrix.diagonal (fun i => (s i : ℂ)) * (U : Matrix ι ι ℂ) -
      (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (s i : ℂ)))
  let A : ℝ := Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ))
  let S2 : ℝ := ∑ i, s i ^ 2
  let S4 : ℝ := ∑ i, s i ^ 4
  have hD : 0 < D := by
    change (0 : ℝ) < (Fintype.card ι : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hdefect : 0 ≤ D ^ 2 - A := by
    exact sub_nonneg.mpr (finiteUnitary_trace_normSq_le_card_sq U)
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun i _ => sq_nonneg (s i)
  have hbase : D * E ^ 2 ≤ 16 * (D ^ 2 - A) * S4 := by
    exact finiteUnitaryDiagonal_commutatorEnergy_sq_le_fourthMoment_traceDefect s U
  have hsquare : D ^ 2 * E ^ 2 ≤ D ^ 2 * S2 ^ 2 := by
    calc
      D ^ 2 * E ^ 2 = D * (D * E ^ 2) := by ring
      _ ≤ D * (16 * (D ^ 2 - A) * S4) :=
        mul_le_mul_of_nonneg_left hbase hD.le
      _ = 16 * (D ^ 2 - A) * (D * S4) := by ring
      _ ≤ 16 * (D ^ 2 - A) * (κ * S2 ^ 2) := by
        exact mul_le_mul_of_nonneg_left hkurt
          (mul_nonneg (by norm_num) hdefect)
      _ = (16 * κ * (D ^ 2 - A)) * S2 ^ 2 := by ring
      _ ≤ D ^ 2 * S2 ^ 2 :=
        mul_le_mul_of_nonneg_right hfidelity (sq_nonneg S2)
  have hEsq : E ^ 2 ≤ S2 ^ 2 := by nlinarith [sq_pos_of_pos hD]
  have hE : 0 ≤ E := finiteMatrixHilbertSchmidtEnergy_nonneg _
  exact (sq_le_sq₀ hE hS2).mp hEsq

theorem finiteMatrixHilbertSchmidtEnergy_unitaryConjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (K : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (star (K : Matrix ι ι ℂ) * A * (K : Matrix ι ι ℂ)) =
      finiteMatrixHilbertSchmidtEnergy A := by
  unfold finiteMatrixHilbertSchmidtEnergy
  have hleft : star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self K
  have hright : (K : Matrix ι ι ℂ) * star (K : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_mul_star_self K
  congr 1
  calc
    Matrix.trace
        (star (star (K : Matrix ι ι ℂ) * A * (K : Matrix ι ι ℂ)) *
          (star (K : Matrix ι ι ℂ) * A * (K : Matrix ι ι ℂ))) =
      Matrix.trace
        (star (K : Matrix ι ι ℂ) * (star A * A) * (K : Matrix ι ι ℂ)) := by
        congr 1
        rw [star_mul, star_mul, star_star]
        calc
          star (K : Matrix ι ι ℂ) * (star A * (K : Matrix ι ι ℂ)) *
              (star (K : Matrix ι ι ℂ) * A * (K : Matrix ι ι ℂ)) =
            star (K : Matrix ι ι ℂ) * star A *
              ((K : Matrix ι ι ℂ) * star (K : Matrix ι ι ℂ)) * A *
                (K : Matrix ι ι ℂ) := by noncomm_ring
          _ = _ := by rw [hright]; noncomm_ring
    _ = Matrix.trace
        ((K : Matrix ι ι ℂ) * star (K : Matrix ι ι ℂ) * (star A * A)) :=
      Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (star A * A) := by rw [hright, Matrix.one_mul]

theorem trace_unitaryConjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (K : Matrix.unitaryGroup ι ℂ) :
    Matrix.trace (star (K : Matrix ι ι ℂ) * A * (K : Matrix ι ι ℂ)) =
      Matrix.trace A := by
  have hright : (K : Matrix ι ι ℂ) * star (K : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_mul_star_self K
  calc
    _ = Matrix.trace
        ((K : Matrix ι ι ℂ) * star (K : Matrix ι ι ℂ) * A) :=
      Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hright, Matrix.one_mul]

/-- Coordinate-free kurtosis bridge: high normalized-trace (Choi) fidelity to the identity
forces a unitary into the half-energy commutator tube of every Hermitian source with bounded
spectral fourth moment. -/
theorem finiteUnitary_commutatorEnergy_le_traceEnergy_of_eigenKurtosis
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) (κ : ℝ)
    (hkurt : (Fintype.card ι : ℝ) *
        (∑ i, hH.eigenvalues i ^ 4) ≤
      κ * (∑ i, hH.eigenvalues i ^ 2) ^ 2)
    (hfidelity : 16 * κ *
        ((Fintype.card ι : ℝ) ^ 2 -
          Complex.normSq (Matrix.trace (U : Matrix ι ι ℂ))) ≤
      (Fintype.card ι : ℝ) ^ 2) :
    finiteMatrixHilbertSchmidtEnergy
        (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) ≤
      (Matrix.trace (H * H)).re := by
  let K := hH.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  let V : Matrix.unitaryGroup ι ℂ := star K * U * K
  have hdiag := finiteUnitaryDiagonal_commutatorEnergy_le_traceEnergy_of_kurtosis
    hH.eigenvalues V κ hkurt
  have htraceV : Matrix.trace (V : Matrix ι ι ℂ) =
      Matrix.trace (U : Matrix ι ι ℂ) := by
    exact trace_unitaryConjugate (U : Matrix ι ι ℂ) K
  rw [htraceV] at hdiag
  have hdiag' := hdiag hfidelity
  have hspec : H = (K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ) :=
    hH.spectral_theorem
  have hcomm :
      D * (V : Matrix ι ι ℂ) - (V : Matrix ι ι ℂ) * D =
        star (K : Matrix ι ι ℂ) *
          (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) *
            (K : Matrix ι ι ℂ) := by
    dsimp [V]
    rw [hspec]
    have hleft : star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ) = 1 :=
      Unitary.coe_star_mul_self K
    symm
    calc
      star (K : Matrix ι ι ℂ) *
          ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ) *
              (U : Matrix ι ι ℂ) -
            (U : Matrix ι ι ℂ) *
              ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ))) *
            (K : Matrix ι ι ℂ) =
        (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ)) * D *
            star (K : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) *
              (K : Matrix ι ι ℂ) -
          star (K : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) *
            (K : Matrix ι ι ℂ) * D *
              (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ)) := by
                noncomm_ring
      _ = _ := by rw [hleft]; noncomm_ring
  rw [hcomm, finiteMatrixHilbertSchmidtEnergy_unitaryConjugate] at hdiag'
  rwa [trace_mul_self_re_eq_sum_sq_eigenvalues H hH]

theorem finiteMatrixHilbertSchmidtEnergy_unitaryMulLeft
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (K : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy ((K : Matrix ι ι ℂ) * A) =
      finiteMatrixHilbertSchmidtEnergy A := by
  unfold finiteMatrixHilbertSchmidtEnergy
  have hleft : star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self K
  congr 1
  congr 1
  rw [star_mul]
  calc
    star A * star (K : Matrix ι ι ℂ) * ((K : Matrix ι ι ℂ) * A) =
        star A * (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ)) * A := by
      noncomm_ring
    _ = star A * A := by rw [hleft]; noncomm_ring

/-- **Choi-shortcut to energy-defect law.** For a Hermitian source with bounded spectral
kurtosis, every unitary having sufficiently high normalized Choi fidelity with any commuting
autonomous target lies in the same gap-free half-energy tube. -/
theorem finiteUnitary_choiShortcut_commutatorEnergy_le_traceEnergy_of_eigenKurtosis
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (T W : Matrix.unitaryGroup ι ℂ)
    (hcomm : H * (T : Matrix ι ι ℂ) = (T : Matrix ι ι ℂ) * H)
    (κ : ℝ)
    (hkurt : (Fintype.card ι : ℝ) *
        (∑ i, hH.eigenvalues i ^ 4) ≤
      κ * (∑ i, hH.eigenvalues i ^ 2) ^ 2)
    (hfidelity : 16 * κ *
        ((Fintype.card ι : ℝ) ^ 2 -
          Complex.normSq
            (Matrix.trace
              (star (T : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ)))) ≤
      (Fintype.card ι : ℝ) ^ 2) :
    finiteMatrixHilbertSchmidtEnergy
        (H * (W : Matrix ι ι ℂ) - (W : Matrix ι ι ℂ) * H) ≤
      (Matrix.trace (H * H)).re := by
  let R : Matrix.unitaryGroup ι ℂ := star T * W
  have hR := finiteUnitary_commutatorEnergy_le_traceEnergy_of_eigenKurtosis
    H hH R κ hkurt
  have htraceR : Matrix.trace (R : Matrix ι ι ℂ) =
      Matrix.trace (star (T : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ)) := rfl
  rw [htraceR] at hR
  have hR' := hR hfidelity
  have hstarcomm : H * star (T : Matrix ι ι ℂ) =
      star (T : Matrix ι ι ℂ) * H := by
    have hs := congrArg star hcomm
    rw [star_mul, star_mul] at hs
    have hstarH : star H = H := hH
    simpa [hstarH] using hs.symm
  have hcommR :
      H * (R : Matrix ι ι ℂ) - (R : Matrix ι ι ℂ) * H =
        star (T : Matrix ι ι ℂ) *
          (H * (W : Matrix ι ι ℂ) - (W : Matrix ι ι ℂ) * H) := by
    dsimp [R]
    calc
      H * (star (T : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ)) -
          star (T : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ) * H =
        (H * star (T : Matrix ι ι ℂ)) * (W : Matrix ι ι ℂ) -
          star (T : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ) * H := by
            noncomm_ring
      _ = (star (T : Matrix ι ι ℂ) * H) * (W : Matrix ι ι ℂ) -
          star (T : Matrix ι ι ℂ) * (W : Matrix ι ι ℂ) * H := by
            rw [hstarcomm]
      _ = _ := by noncomm_ring
  rw [hcommR] at hR'
  have henergy := finiteMatrixHilbertSchmidtEnergy_unitaryMulLeft
    (H * (W : Matrix ι ι ℂ) - (W : Matrix ι ι ℂ) * H) (star T)
  change finiteMatrixHilbertSchmidtEnergy
      (star (T : Matrix ι ι ℂ) *
        (H * (W : Matrix ι ι ℂ) - (W : Matrix ι ι ℂ) * H)) =
    finiteMatrixHilbertSchmidtEnergy
      (H * (W : Matrix ι ι ℂ) - (W : Matrix ι ι ℂ) * H) at henergy
  rw [henergy] at hR'
  exact hR'

end
end GaloisForLFunctions.HTGeometry
