import GaloisForLFunctions.HTGeometry.AdaptiveEigenframeTwoQuerySourceMemory

open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem exchangeable_second_moment_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (A B : ℝ) :
    (∑ i, ∑ k, s i * s k * (if i = k then A else B)) =
      B * (∑ i, s i) ^ 2 + (A - B) * ∑ i, (s i) ^ 2 := by
  let diag := fun i k : ι => if i = k then s i * s k else 0
  have hterm (i k : ι) :
      s i * s k * (if i = k then A else B) =
        B * s i * s k + (A - B) * diag i k := by
    by_cases hik : i = k <;> simp [diag, hik] <;> ring
  have hdiag : (∑ i, ∑ k, diag i k) = ∑ i, (s i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_eq_single i]
    · simp [diag, pow_two]
    · intro k _hk hki
      simp [diag, hki.symm]
    · simp
  have hsplit :
      (∑ i, ∑ k, (B * s i * s k + (A - B) * diag i k)) =
        (∑ i, ∑ k, B * s i * s k) +
          ∑ i, ∑ k, (A - B) * diag i k := by
    calc
      _ = ∑ i, ((∑ k, B * s i * s k) +
          ∑ k, (A - B) * diag i k) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact Finset.sum_add_distrib
      _ = _ := Finset.sum_add_distrib
  have htotal :
      (∑ i, ∑ k, B * s i * s k) = B * (∑ i, s i) ^ 2 := by
    calc
      _ = B * ∑ i, ∑ k, s i * s k := by
        symm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ = _ := by rw [pow_two, Finset.sum_mul_sum]
  have hscaled :
      (∑ i, ∑ k, (A - B) * diag i k) =
        (A - B) * ∑ i, ∑ k, diag i k := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k, (B * s i * s k + (A - B) * diag i k) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro k _hk
      exact hterm i k
    _ = _ := by rw [hsplit, htotal, hscaled, hdiag]

theorem finiteUnitaryDiagonalProbeHaarSignal_eq_sq_sum_div
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ)
    (j : Fin 2 ⊕ Fin d) (hsum : ∑ i, s i = 0) :
    finiteUnitaryDiagonalProbeHaarSignal d s j =
      (∑ i, (s i) ^ 2) /
        (((d + 2 : ℕ) : ℝ) * ((d + 3 : ℕ) : ℝ)) := by
  rw [finiteUnitaryDiagonalProbeHaarSignal_eq_sum,
    exchangeable_second_moment_sum, hsum, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add, finiteUnitaryHaarFourthMoment_eq_two_mul_cross,
    finiteUnitaryHaarCrossMoment_eq]
  have hd2 : (((d + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hd3 : (((d + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

def finiteUnitaryDiagonalCoordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (U : Matrix.unitaryGroup ι ℂ) (j : ι) : ℝ :=
  ∑ i, s i * finiteUnitaryEntryWeight U i j

theorem finiteUnitaryEntryWeight_mul_permutation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (U : Matrix.unitaryGroup ι ℂ) (i j : ι) :
    finiteUnitaryEntryWeight (U * finiteUnitaryPermutation e) i j =
      finiteUnitaryEntryWeight U i (e j) := by
  simp [finiteUnitaryEntryWeight, finiteUnitaryPermutation, Matrix.mul_apply]

theorem finiteUnitaryDiagonalCoordinate_mul_permutation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (s : ι → ℝ) (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    finiteUnitaryDiagonalCoordinate s (U * finiteUnitaryPermutation e) j =
      finiteUnitaryDiagonalCoordinate s U (e j) := by
  simp only [finiteUnitaryDiagonalCoordinate,
    finiteUnitaryEntryWeight_mul_permutation]

theorem integral_finiteUnitaryDiagonalCoordinate_mul_equiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (s : ι → ℝ) (j k : ι) :
    (∫ U, finiteUnitaryDiagonalCoordinate s U (e j) *
        finiteUnitaryDiagonalCoordinate s U (e k) ∂finiteUnitaryHaar ι) =
      ∫ U, finiteUnitaryDiagonalCoordinate s U j *
        finiteUnitaryDiagonalCoordinate s U k ∂finiteUnitaryHaar ι := by
  have h := integral_finiteUnitaryHaar_mul_right
    (fun U : Matrix.unitaryGroup ι ℂ =>
      finiteUnitaryDiagonalCoordinate s U j *
        finiteUnitaryDiagonalCoordinate s U k)
    (finiteUnitaryPermutation e)
  simpa only [finiteUnitaryDiagonalCoordinate_mul_permutation] using h

theorem continuous_finiteUnitaryDiagonalCoordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (j : ι) :
    Continuous fun U : Matrix.unitaryGroup ι ℂ =>
      finiteUnitaryDiagonalCoordinate s U j := by
  unfold finiteUnitaryDiagonalCoordinate
  exact continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_finiteUnitaryEntryWeight i j)

theorem integrable_finiteUnitaryDiagonalCoordinate_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (j k : ι) :
    Integrable
      (fun U : Matrix.unitaryGroup ι ℂ =>
        finiteUnitaryDiagonalCoordinate s U j *
          finiteUnitaryDiagonalCoordinate s U k)
      (finiteUnitaryHaar ι) := by
  apply integrable_finiteUnitaryHaar_of_continuous
  exact (continuous_finiteUnitaryDiagonalCoordinate s j).mul
    (continuous_finiteUnitaryDiagonalCoordinate s k)

theorem sum_finiteUnitaryEntryWeight_row
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, finiteUnitaryEntryWeight U i j = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M i i)
    ((Matrix.mem_unitaryGroup_iff.mp U.2))
  simp only [Matrix.mul_apply, Matrix.star_apply,
    Matrix.one_apply, if_pos] at h
  have hr := congrArg Complex.re h
  simpa [finiteUnitaryEntryWeight, Complex.normSq_apply] using hr

theorem sum_finiteUnitaryDiagonalCoordinate_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (hsum : ∑ i, s i = 0)
    (U : Matrix.unitaryGroup ι ℂ) :
    ∑ j, finiteUnitaryDiagonalCoordinate s U j = 0 := by
  unfold finiteUnitaryDiagonalCoordinate
  rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j, s i * finiteUnitaryEntryWeight U i j) =
        ∑ i, s i * ∑ j, finiteUnitaryEntryWeight U i j := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = ∑ i, s i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [sum_finiteUnitaryEntryWeight_row, mul_one]
    _ = 0 := hsum

def finiteUnitaryDiagonalAdjointAutocorrelationHaarSignal
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ) : ℝ :=
  ∫ U, (∑ j, s j * finiteUnitaryDiagonalCoordinate s U j) ^ 2
    ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)

theorem finiteUnitaryDiagonalAdjointAutocorrelationHaarSignal_eq
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ)
    (hsum : ∑ i, s i = 0) :
    finiteUnitaryDiagonalAdjointAutocorrelationHaarSignal d s =
      (∑ i, (s i) ^ 2) ^ 2 /
        ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
  let ι := Fin 2 ⊕ Fin d
  let μ := finiteUnitaryHaar ι
  let X := fun (j : ι) (U : Matrix.unitaryGroup ι ℂ) =>
    finiteUnitaryDiagonalCoordinate s U j
  let a : ι := Sum.inl 0
  let b : ι := Sum.inl 1
  have hab : a ≠ b := by
    intro h
    injection h with h'
    omega
  let v : ℝ := (∑ i, (s i) ^ 2) /
    (((d + 2 : ℕ) : ℝ) * ((d + 3 : ℕ) : ℝ))
  let c : ℝ := ∫ U, X a U * X b U ∂μ
  have hv : (∫ U, X a U * X a U ∂μ) = v := by
    dsimp [X, μ, v, a]
    unfold finiteUnitaryDiagonalCoordinate
    simpa only [finiteUnitaryDiagonalProbeHaarSignal, pow_two] using
      finiteUnitaryDiagonalProbeHaarSignal_eq_sq_sum_div d s (Sum.inl 0) hsum
  have hmom (j k : ι) :
      (∫ U, X j U * X k U ∂μ) = if j = k then v else c := by
    by_cases hjk : j = k
    · subst k
      rw [if_pos rfl]
      have h := integral_finiteUnitaryDiagonalCoordinate_mul_equiv
        (Equiv.swap a j) s a a
      simpa [X, μ, Equiv.swap_apply_left, hv] using h
    · rw [if_neg hjk]
      obtain ⟨e, hea, heb⟩ := exists_equiv_map_ordered_pair hab hjk
      have h := integral_finiteUnitaryDiagonalCoordinate_mul_equiv e s a b
      simpa [X, μ, c, hea, heb] using h
  have hzero : (∑ k : ι, ∫ U, X a U * X k U ∂μ) = 0 := by
    rw [← integral_finsetSum Finset.univ
      (fun k _ => integrable_finiteUnitaryDiagonalCoordinate_mul s a k)]
    calc
      (∫ U, ∑ k, X a U * X k U ∂μ) = ∫ _U, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with U
        rw [← Finset.mul_sum, show (∑ k, X k U) = 0 by
          exact sum_finiteUnitaryDiagonalCoordinate_eq_zero s hsum U]
        ring
      _ = 0 := by simp
  have hvc : v + (((d + 1 : ℕ) : ℝ)) * c = 0 := by
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun k : ι => ∫ U, X a U * X k U ∂μ) (Finset.mem_univ a)
    rw [hmom a a, if_pos rfl] at hsplit
    have herase :
        (∑ k ∈ Finset.univ.erase a, ∫ U, X a U * X k U ∂μ) =
          (((d + 1 : ℕ) : ℝ)) * c := by
      rw [Finset.sum_congr rfl fun k hk => by
        rw [hmom, if_neg (Finset.ne_of_mem_erase hk).symm]]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem,
        Finset.mem_univ, Finset.card_univ]
      have hcard : Fintype.card ι = d + 2 := by simp [ι, Nat.add_comm]
      rw [hcard]
      push_cast
      ring
    linarith [hsplit, herase, hzero]
  have hexpand (U : Matrix.unitaryGroup ι ℂ) :
      (∑ j, s j * X j U) ^ 2 =
        ∑ j, ∑ k, s j * s k * (X j U * X k U) := by
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hint :
      (∫ U, (∑ j, s j * X j U) ^ 2 ∂μ) =
        ∑ j, ∑ k, s j * s k * (if j = k then v else c) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j _hj
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro k _hk
        rw [integral_const_mul]
        rw [hmom]
      · intro k _hk
        exact (integrable_finiteUnitaryDiagonalCoordinate_mul s j k).const_mul
          (s j * s k)
    · intro j _hj
      apply integrable_finsetSum
      intro k _hk
      exact (integrable_finiteUnitaryDiagonalCoordinate_mul s j k).const_mul
        (s j * s k)
  rw [finiteUnitaryDiagonalAdjointAutocorrelationHaarSignal]
  change (∫ U, (∑ j, s j * X j U) ^ 2 ∂μ) = _
  rw [hint, exchangeable_second_moment_sum, hsum,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add]
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hd2 : (0 : ℝ) < d + 2 := by positivity
  have hd3 : (0 : ℝ) < d + 3 := by positivity
  have hd1ne : (((d + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hc : c = -v / (((d + 1 : ℕ) : ℝ)) := by
    apply (eq_div_iff hd1ne).2
    nlinarith [hvc]
  rw [hc]
  dsimp [v]
  have hdenpos : (0 : ℝ) < (d + 2) ^ 2 - 1 := by nlinarith
  have hden : (d + 2 : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt hdenpos
  field_simp [hden]
  push_cast
  ring

theorem trace_diagonal_adjoint_autocorrelation_re
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ)
    (U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
    (Matrix.trace
      (Matrix.diagonal (fun i => (s i : ℂ)) *
        star (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) *
        Matrix.diagonal (fun i => (s i : ℂ)) *
        (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ))).re =
      ∑ j, s j * finiteUnitaryDiagonalCoordinate s U j := by
  let D : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ :=
    Matrix.diagonal (fun i => (s i : ℂ))
  let Y : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ :=
    star (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * D *
      (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)
  have hcyc : Matrix.trace (D * star (U : Matrix (Fin 2 ⊕ Fin d)
      (Fin 2 ⊕ Fin d) ℂ) * D *
        (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) =
      Matrix.trace (Y * D) := by
    calc
      Matrix.trace (D * star (U : Matrix (Fin 2 ⊕ Fin d)
          (Fin 2 ⊕ Fin d) ℂ) * D *
            (U : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) =
          Matrix.trace (D * Y) := by
            congr 1
            simp only [D, Y, Matrix.mul_assoc]
      _ = Matrix.trace (Y * D) := Matrix.trace_mul_comm D Y
  have hdiag : Matrix.trace (Y * D) = ∑ j, Y j j * (s j : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    apply Finset.sum_congr rfl
    intro j _hj
    simp [D, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [hcyc, hdiag, ← Complex.reCLM_apply, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, mul_comm]
  congr 1
  simpa [Y, D, finiteUnitaryDiagonalCoordinate] using
    probeCoordinate_diagonal_eq d s U j

def finiteUnitaryAdjointAutocorrelationIntegrand
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ) : ℝ :=
    (Matrix.trace
      (H * star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ))).re ^ 2

def finiteUnitaryAdjointAutocorrelationHaarSignal
    (d : ℕ) (H : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) : ℝ :=
  ∫ U : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ,
    finiteUnitaryAdjointAutocorrelationIntegrand H U
    ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)

theorem finiteUnitaryAdjointAutocorrelationHaarSignal_diagonal
    (d : ℕ) (s : (Fin 2 ⊕ Fin d) → ℝ) :
    finiteUnitaryAdjointAutocorrelationHaarSignal d
        (Matrix.diagonal (fun i => (s i : ℂ))) =
      finiteUnitaryDiagonalAdjointAutocorrelationHaarSignal d s := by
  apply integral_congr_ae
  filter_upwards [] with U
  unfold finiteUnitaryAdjointAutocorrelationIntegrand
  rw [trace_diagonal_adjoint_autocorrelation_re]

theorem trace_conjugated_adjoint_autocorrelation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H U K : Matrix ι ι ℂ) :
    Matrix.trace ((K * H * star K) * star U * (K * H * star K) * U) =
      Matrix.trace (H * (star K * star U * K) * H * (star K * U * K)) := by
  calc
    _ = Matrix.trace
        (K * (H * star K * star U * K * H * star K * U)) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace
        ((H * star K * star U * K * H * star K * U) * K) :=
      Matrix.trace_mul_comm _ _
    _ = _ := by
      congr 1
      noncomm_ring

theorem finiteUnitaryAdjointAutocorrelationIntegrand_conjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (U K : Matrix.unitaryGroup ι ℂ) :
    finiteUnitaryAdjointAutocorrelationIntegrand
        ((K : Matrix ι ι ℂ) * H * star (K : Matrix ι ι ℂ)) U =
      finiteUnitaryAdjointAutocorrelationIntegrand H (star K * U * K) := by
  unfold finiteUnitaryAdjointAutocorrelationIntegrand
  have hstarMatrix :
      star (star (K : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) *
          (K : Matrix ι ι ℂ)) =
        star (K : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) *
          (K : Matrix ι ι ℂ) := by
    simp only [star_mul, star_star, Matrix.mul_assoc]
  have hcoe :
      (((star K * U * K : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)) =
        star (K : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) *
          (K : Matrix ι ι ℂ) := rfl
  have hcoeStar :
      star (((star K * U * K : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)) =
        star (K : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) *
          (K : Matrix ι ι ℂ) := by
    rw [hcoe, hstarMatrix]
  rw [hcoeStar, hcoe]
  exact congrArg (fun z : ℂ => z.re ^ 2)
    (trace_conjugated_adjoint_autocorrelation H U K)

theorem integral_finiteUnitaryHaar_conjugate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : Matrix.unitaryGroup ι ℂ → ℝ) (K : Matrix.unitaryGroup ι ℂ) :
    (∫ U, f (star K * U * K) ∂finiteUnitaryHaar ι) =
      ∫ U, f U ∂finiteUnitaryHaar ι := by
  calc
    _ = ∫ U, f (star K * U) ∂finiteUnitaryHaar ι :=
      by simpa only [mul_assoc] using
        (integral_finiteUnitaryHaar_mul_right (fun U => f (star K * U)) K)
    _ = _ := integral_finiteUnitaryHaar_mul_left f (star K)

theorem finiteUnitaryAdjointAutocorrelationHaarSignal_conjugate
    (d : ℕ) (H : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)
    (K : Matrix.unitaryGroup (Fin 2 ⊕ Fin d) ℂ) :
    finiteUnitaryAdjointAutocorrelationHaarSignal d
        ((K : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * H *
          star (K : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) =
      finiteUnitaryAdjointAutocorrelationHaarSignal d H := by
  unfold finiteUnitaryAdjointAutocorrelationHaarSignal
  calc
    (∫ U, finiteUnitaryAdjointAutocorrelationIntegrand
        ((K : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) * H *
          star (K : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) U
        ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d)) =
      ∫ U, finiteUnitaryAdjointAutocorrelationIntegrand H (star K * U * K)
        ∂finiteUnitaryHaar (Fin 2 ⊕ Fin d) := by
        apply integral_congr_ae
        filter_upwards [] with U
        exact finiteUnitaryAdjointAutocorrelationIntegrand_conjugate H U K
    _ = _ := integral_finiteUnitaryHaar_conjugate
      (finiteUnitaryAdjointAutocorrelationIntegrand H) K

theorem finiteUnitaryAdjointAutocorrelationHaarSignal_eq_eigenvalues
    (d : ℕ) (H : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)
    (hH : H.IsHermitian) (htrace : H.trace = 0) :
    finiteUnitaryAdjointAutocorrelationHaarSignal d H =
      (∑ i, (hH.eigenvalues i) ^ 2) ^ 2 /
        ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
  have hspec : H =
      (hH.eigenvectorUnitary : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) *
        Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) *
        star (hH.eigenvectorUnitary :
          Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) := by
    convert hH.spectral_theorem using 1
    rfl
  calc
    finiteUnitaryAdjointAutocorrelationHaarSignal d H =
        finiteUnitaryAdjointAutocorrelationHaarSignal d
          ((hH.eigenvectorUnitary :
              Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ) *
            Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) *
            star (hH.eigenvectorUnitary :
              Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)) :=
      congrArg (finiteUnitaryAdjointAutocorrelationHaarSignal d) hspec
    _ = finiteUnitaryAdjointAutocorrelationHaarSignal d
        (Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))) :=
      finiteUnitaryAdjointAutocorrelationHaarSignal_conjugate d _ _
    _ = finiteUnitaryDiagonalAdjointAutocorrelationHaarSignal d hH.eigenvalues :=
      finiteUnitaryAdjointAutocorrelationHaarSignal_diagonal d hH.eigenvalues
    _ = _ := finiteUnitaryDiagonalAdjointAutocorrelationHaarSignal_eq d hH.eigenvalues
      (sum_hermitianEigenvalues_eq_zero_of_trace_eq_zero hH htrace)

/-- Spectral energy is exactly the real trace of `H²`. -/
theorem trace_mul_self_re_eq_sum_sq_eigenvalues
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (Matrix.trace (H * H)).re = ∑ i, (hH.eigenvalues i) ^ 2 := by
  let K := hH.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ))
  have hspec : H = (K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ) := by
    exact hH.spectral_theorem
  have hcollapse :
      Matrix.trace
          (((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)) *
            ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ))) =
        Matrix.trace (D * D) := by
    calc
      _ = Matrix.trace
          ((K : Matrix ι ι ℂ) * (D * D) * star (K : Matrix ι ι ℂ)) := by
            congr 1
            calc
              ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)) *
                  ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)) =
                (K : Matrix ι ι ℂ) * D *
                  (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ)) * D *
                  star (K : Matrix ι ι ℂ) := by noncomm_ring
              _ = _ := by
                rw [show star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ) = 1 from
                  Unitary.coe_star_mul_self K]
                noncomm_ring
      _ = Matrix.trace
          (star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ) * (D * D)) :=
            Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (D * D) := by
        rw [show star (K : Matrix ι ι ℂ) * (K : Matrix ι ι ℂ) = 1 from
          Unitary.coe_star_mul_self K, Matrix.one_mul]
  calc
    (Matrix.trace (H * H)).re =
        (Matrix.trace
          (((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)) *
            ((K : Matrix ι ι ℂ) * D * star (K : Matrix ι ι ℂ)))).re :=
      congrArg (fun A : Matrix ι ι ℂ => (Matrix.trace (A * A)).re) hspec
    _ = (Matrix.trace (D * D)).re := congrArg Complex.re hcollapse
    _ = _ := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      rw [← Complex.reCLM_apply, _root_.map_sum]
      simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- Every nonzero Hermitian matrix has strictly positive spectral energy. -/
theorem sum_sq_eigenvalues_pos_of_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (hzero : H ≠ 0) :
    0 < ∑ i, (hH.eigenvalues i) ^ 2 := by
  have heig : hH.eigenvalues ≠ 0 := by
    exact (not_congr hH.eigenvalues_eq_zero_iff).mpr hzero
  obtain ⟨i, hi⟩ := Function.ne_iff.mp heig
  apply Finset.sum_pos'
  · exact fun j _hj => sq_nonneg (hH.eigenvalues j)
  · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

/-- The squared adjoint autocorrelation is continuous on the unitary group. -/
theorem continuous_finiteUnitaryAdjointAutocorrelationIntegrand
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    Continuous fun U : Matrix.unitaryGroup ι ℂ =>
      finiteUnitaryAdjointAutocorrelationIntegrand H U := by
  simpa only [finiteUnitaryAdjointAutocorrelationIntegrand, Matrix.mul_assoc] using
    (continuous_sq_trace_conj H H)

/-- The squared adjoint autocorrelation is Haar-integrable. -/
theorem integrable_finiteUnitaryAdjointAutocorrelationIntegrand
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    Integrable (finiteUnitaryAdjointAutocorrelationIntegrand H)
      (finiteUnitaryHaar ι) :=
  integrable_finiteUnitaryHaar_of_continuous _
    (continuous_finiteUnitaryAdjointAutocorrelationIntegrand H)

/-- **Dimension-only Haar lower tail.** For every nonzero traceless Hermitian `H`, the Haar
probability that its adjoint autocorrelation retains at least half of its full spectral-energy
amplitude is at most `4 / (D² - 1)`. -/
theorem haar_measureReal_half_energy_adjointAutocorrelation_le
    (d : ℕ) (H : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ)
    (hH : H.IsHermitian) (htrace : H.trace = 0) (hzero : H ≠ 0) :
    (finiteUnitaryHaar (Fin 2 ⊕ Fin d)).real
        {U | ((∑ i, (hH.eigenvalues i) ^ 2) / 2) ^ 2 ≤
          finiteUnitaryAdjointAutocorrelationIntegrand H U} ≤
      4 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
  let S : ℝ := ∑ i, (hH.eigenvalues i) ^ 2
  let ε : ℝ := (S / 2) ^ 2
  have hS : 0 < S := sum_sq_eigenvalues_pos_of_ne_zero H hH hzero
  have hε : 0 < ε := sq_pos_of_pos (div_pos hS (by norm_num))
  have hnonneg :
      0 ≤ᵐ[finiteUnitaryHaar (Fin 2 ⊕ Fin d)]
        finiteUnitaryAdjointAutocorrelationIntegrand H :=
    Filter.Eventually.of_forall fun U => by
      unfold finiteUnitaryAdjointAutocorrelationIntegrand
      positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg
    (integrable_finiteUnitaryAdjointAutocorrelationIntegrand H) ε
  change ε * (finiteUnitaryHaar (Fin 2 ⊕ Fin d)).real
      {U | ε ≤ finiteUnitaryAdjointAutocorrelationIntegrand H U} ≤
        finiteUnitaryAdjointAutocorrelationHaarSignal d H at hmarkov
  rw [finiteUnitaryAdjointAutocorrelationHaarSignal_eq_eigenvalues d H hH htrace]
    at hmarkov
  have hraw :
      (finiteUnitaryHaar (Fin 2 ⊕ Fin d)).real
          {U | ε ≤ finiteUnitaryAdjointAutocorrelationIntegrand H U} ≤
        (S ^ 2 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1)) / ε := by
    exact (le_div_iff₀ hε).2 (by simpa [S, mul_comm] using hmarkov)
  have hden : 0 < ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
    have hn : 2 ≤ d + 2 := by omega
    have : (2 : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := by exact_mod_cast hn
    nlinarith
  change (finiteUnitaryHaar (Fin 2 ⊕ Fin d)).real
      {U | ε ≤ finiteUnitaryAdjointAutocorrelationIntegrand H U} ≤ _
  calc
    _ ≤ (S ^ 2 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1)) / ε := hraw
    _ = 4 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
      dsimp [ε]
      field_simp [ne_of_gt hS, ne_of_gt hden]
      ring

/-- Reindexing both the Hamiltonian and Haar unitary leaves the squared adjoint autocorrelation
unchanged. -/
theorem finiteUnitaryAdjointAutocorrelationIntegrand_reindex
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype κ'] [DecidableEq κ']
    (e : κ ≃ κ') (H : Matrix κ κ ℂ) (U : Matrix.unitaryGroup κ ℂ) :
    finiteUnitaryAdjointAutocorrelationIntegrand
        (Matrix.reindexAlgEquiv ℂ ℂ e H) (unitaryGroupReindex e U) =
      finiteUnitaryAdjointAutocorrelationIntegrand H U := by
  unfold finiteUnitaryAdjointAutocorrelationIntegrand
  have hcoe :
      (((unitaryGroupReindex e U : Matrix.unitaryGroup κ' ℂ) : Matrix κ' κ' ℂ)) =
        Matrix.reindexAlgEquiv ℂ ℂ e (U : Matrix κ κ ℂ) := rfl
  rw [hcoe]
  rw [← reindexAlgEquiv_star, ← map_mul, ← map_mul, ← map_mul,
    reindexAlgEquiv_trace]

/-- **Exact adjoint-autocorrelation Haar law on every finite register.** If the register has
dimension `D = d + 2`, every traceless Hermitian source has Haar second moment
`tr(H²)² / (D² - 1)`. -/
theorem haar_adjointAutocorrelationIntegral_eq_traceEnergy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d : ℕ) (e : κ ≃ Fin 2 ⊕ Fin d)
    (H : Matrix κ κ ℂ) (hH : H.IsHermitian) (htrace : H.trace = 0) :
    (∫ U : Matrix.unitaryGroup κ ℂ,
        finiteUnitaryAdjointAutocorrelationIntegrand H U ∂finiteUnitaryHaar κ) =
      (Matrix.trace (H * H)).re ^ 2 /
        ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
  let A : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ :=
    Matrix.reindexAlgEquiv ℂ ℂ e H
  have hA : A.IsHermitian := reindexAlgEquiv_isHermitian e hH
  have hAtrace : A.trace = 0 := by
    change (Matrix.reindexAlgEquiv ℂ ℂ e H).trace = 0
    rw [reindexAlgEquiv_trace]
    exact htrace
  have htrans := integral_finiteUnitaryHaar_reindex e
    (finiteUnitaryAdjointAutocorrelationIntegrand A)
    (continuous_finiteUnitaryAdjointAutocorrelationIntegrand A)
  calc
    (∫ U : Matrix.unitaryGroup κ ℂ,
        finiteUnitaryAdjointAutocorrelationIntegrand H U ∂finiteUnitaryHaar κ) =
      ∫ U : Matrix.unitaryGroup κ ℂ,
        finiteUnitaryAdjointAutocorrelationIntegrand A (unitaryGroupReindex e U)
          ∂finiteUnitaryHaar κ := by
            apply integral_congr_ae
            filter_upwards [] with U
            exact (finiteUnitaryAdjointAutocorrelationIntegrand_reindex e H U).symm
    _ = finiteUnitaryAdjointAutocorrelationHaarSignal d A := htrans
    _ = (∑ i, (hA.eigenvalues i) ^ 2) ^ 2 /
        ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) :=
      finiteUnitaryAdjointAutocorrelationHaarSignal_eq_eigenvalues d A hA hAtrace
    _ = (Matrix.trace (A * A)).re ^ 2 /
        ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
      rw [trace_mul_self_re_eq_sum_sq_eigenvalues A hA]
    _ = _ := by
      change (Matrix.trace
        (Matrix.reindexAlgEquiv ℂ ℂ e H * Matrix.reindexAlgEquiv ℂ ℂ e H)).re ^ 2 /
          ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) = _
      rw [← map_mul, reindexAlgEquiv_trace]

/-- **Register-independent half-energy Haar tail.** On every finite register of dimension
`D ≥ 2`, Haar probability of retaining at least half the full adjoint autocorrelation of a fixed
nonzero traceless Hermitian source is at most `4 / (D² - 1)`. -/
theorem haar_measureReal_half_traceEnergy_adjointAutocorrelation_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d : ℕ) (e : κ ≃ Fin 2 ⊕ Fin d)
    (H : Matrix κ κ ℂ) (hH : H.IsHermitian)
    (htrace : H.trace = 0) (hzero : H ≠ 0) :
    (finiteUnitaryHaar κ).real
        {U | ((Matrix.trace (H * H)).re / 2) ^ 2 ≤
          finiteUnitaryAdjointAutocorrelationIntegrand H U} ≤
      4 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
  let S : ℝ := (Matrix.trace (H * H)).re
  let ε : ℝ := (S / 2) ^ 2
  have hS : 0 < S := by
    change 0 < (Matrix.trace (H * H)).re
    rw [trace_mul_self_re_eq_sum_sq_eigenvalues H hH]
    exact sum_sq_eigenvalues_pos_of_ne_zero H hH hzero
  have hε : 0 < ε := sq_pos_of_pos (div_pos hS (by norm_num))
  have hnonneg : 0 ≤ᵐ[finiteUnitaryHaar κ]
      finiteUnitaryAdjointAutocorrelationIntegrand H :=
    Filter.Eventually.of_forall fun U => by
      unfold finiteUnitaryAdjointAutocorrelationIntegrand
      positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg
    (integrable_finiteUnitaryAdjointAutocorrelationIntegrand H) ε
  rw [haar_adjointAutocorrelationIntegral_eq_traceEnergy d e H hH htrace] at hmarkov
  have hraw :
      (finiteUnitaryHaar κ).real
          {U | ε ≤ finiteUnitaryAdjointAutocorrelationIntegrand H U} ≤
        (S ^ 2 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1)) / ε := by
    exact (le_div_iff₀ hε).2 (by simpa [S, mul_comm] using hmarkov)
  have hden : 0 < ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
    have hn : 2 ≤ d + 2 := by omega
    have hd : (2 : ℝ) ≤ ((d + 2 : ℕ) : ℝ) := by exact_mod_cast hn
    nlinarith
  change (finiteUnitaryHaar κ).real
      {U | ε ≤ finiteUnitaryAdjointAutocorrelationIntegrand H U} ≤ _
  calc
    _ ≤ (S ^ 2 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1)) / ε := hraw
    _ = 4 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
      dsimp [ε]
      field_simp [ne_of_gt hS, ne_of_gt hden]
      ring

end

end GaloisForLFunctions.HTGeometry
