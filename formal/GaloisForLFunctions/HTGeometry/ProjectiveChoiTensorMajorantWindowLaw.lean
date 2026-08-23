import GaloisForLFunctions.HTGeometry.ProjectiveChoiCenterFreeUnionWindowLaw

open Real intervalIntegral MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Uniform one-dimensional Fejér error for the periodic tent. -/
noncomputable def periodicTentFejerError (N : ℕ) (rho : ℝ) : ℝ :=
  (1 / rho) * (2 * π / Real.sqrt ((N : ℝ) + 1))

/-- Tensorized positive Fejér majorant. -/
noncomputable def periodicProductFejerMajorant
    (N : ℕ) (rho : ℝ) (c theta : Fin d → ℝ) : ℝ :=
  ∏ j, (fejerConv N (perTent rho) (theta j - c j) +
    periodicTentFejerError N rho)

theorem periodicTentFejerError_pos (N : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    0 < periodicTentFejerError N rho := by
  rw [periodicTentFejerError]
  positivity

theorem perTent_le_fejerConv_add_error
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (theta : ℝ) :
    perTent rho theta ≤
      fejerConv N (perTent rho) theta + periodicTentFejerError N rho := by
  have h := abs_fejerConv_perTent_sub_le N hrho theta
  rw [show (1 / rho) * (2 * π / Real.sqrt ((N : ℝ) + 1)) =
      periodicTentFejerError N rho by rfl] at h
  linarith [neg_le_of_abs_le h]

/-- Product majorization tensorizes the one-dimensional error instead of
paying an additive dimension-linear remainder. -/
theorem periodicProductTent_le_periodicProductFejerMajorant
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (c theta : Fin d → ℝ) :
    periodicProductTent rho c theta ≤
      periodicProductFejerMajorant N rho c theta := by
  classical
  rw [periodicProductTent, periodicProductFejerMajorant]
  refine Finset.prod_le_prod (fun j _ => perTent_nonneg _ _) ?_
  intro j _
  exact perTent_le_fejerConv_add_error N hrho _

/-- One sheet coefficient after distributing the positive majorant shift
equally over diagonal Fejér sheets. -/
noncomputable def majorantSheetCoeff
    (N : ℕ) (rho e : ℝ) (pq : ℕ × ℕ) : ℂ :=
  ((N : ℂ) + 1)⁻¹ *
      perFourierCoeff (perTent rho) ((pq.1 : ℝ) - (pq.2 : ℝ)) +
    if pq.1 = pq.2 then ((N : ℂ) + 1)⁻¹ * (e : ℂ) else 0

theorem sum_diagonalShiftSheet (N : ℕ) (e theta : ℝ) :
    (∑ pq ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        (if pq.1 = pq.2 then ((N : ℂ) + 1)⁻¹ * (e : ℂ) else 0) *
          Complex.exp (((((pq.1 : ℝ) - (pq.2 : ℝ)) * theta) : ℝ) * Complex.I)) =
      (e : ℂ) := by
  classical
  rw [Finset.sum_product]
  have hinner : ∀ p ∈ Finset.range (N + 1),
      (∑ q ∈ Finset.range (N + 1),
          (if p = q then ((N : ℂ) + 1)⁻¹ * (e : ℂ) else 0) *
            Complex.exp (((((p : ℝ) - (q : ℝ)) * theta) : ℝ) * Complex.I)) =
        ((N : ℂ) + 1)⁻¹ * (e : ℂ) := by
    intro p hp
    rw [Finset.sum_eq_single p]
    · simp
    · intro q hq hqp
      simp [Ne.symm hqp]
    · exact fun hpnot => (hpnot hp).elim
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : ((N : ℂ) + 1) ≠ 0 := by
    have hR : ((N : ℝ) + 1) ≠ 0 := by positivity
    intro h
    exact hR (by exact_mod_cast h)
  push_cast
  field_simp

/-- Exact one-dimensional Fourier representation of the shifted majorant. -/
theorem fejerConv_add_eq_majorantSheetSum
    (N : ℕ) (rho e theta : ℝ) :
    ((fejerConv N (perTent rho) theta + e : ℝ) : ℂ) =
      ∑ pq ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        majorantSheetCoeff N rho e pq *
          Complex.exp (((((pq.1 : ℝ) - (pq.2 : ℝ)) * theta) : ℝ) * Complex.I) := by
  classical
  rw [Complex.ofReal_add, fejerConv_eq_pairSum N
    (continuous_perTent rho) (periodic_perTent rho)]
  simp only [majorantSheetCoeff, add_mul]
  rw [Finset.sum_add_distrib, sum_diagonalShiftSheet]

/-- One tensor-product mode of the shifted majorant. -/
noncomputable def majorantPacketMode
    (N : ℕ) (rho e : ℝ) (c theta : Fin d → ℝ)
    (k : Fin d → ℕ × ℕ) : ℂ :=
  ∏ j, majorantSheetCoeff N rho e (k j) *
    Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) *
      (theta j - c j) : ℝ) * Complex.I)

theorem periodicProductFejerMajorant_eq_modeSum
    (N : ℕ) (rho : ℝ) (c theta : Fin d → ℝ) :
    ((periodicProductFejerMajorant N rho c theta : ℝ) : ℂ) =
      ∑ k ∈ Fintype.piFinset (fun _ : Fin d =>
          Finset.range (N + 1) ×ˢ Finset.range (N + 1)),
        majorantPacketMode N rho (periodicTentFejerError N rho) c theta k := by
  classical
  rw [periodicProductFejerMajorant, Complex.ofReal_prod]
  rw [Finset.prod_congr rfl fun j _ =>
    fejerConv_add_eq_majorantSheetSum N rho
      (periodicTentFejerError N rho) (theta j - c j)]
  rw [Finset.prod_univ_sum]
  rfl

theorem majorantSheetCoeff_diagonal
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (e : ℝ) {pq : ℕ × ℕ} (hpq : pq.1 = pq.2) :
    majorantSheetCoeff N rho e pq =
      ((N : ℂ) + 1)⁻¹ * ((rho / (2 * π) + e : ℝ) : ℂ) := by
  rw [majorantSheetCoeff, if_pos hpq]
  have hzero : (pq.1 : ℝ) - (pq.2 : ℝ) = 0 := by rw [hpq]; ring
  rw [hzero, perFourierCoeff_perTent_zero hrho hrhopi]
  push_cast
  ring

theorem majorantPacketMode_diagonal
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (e : ℝ) (c theta : Fin d → ℝ) {k : Fin d → ℕ × ℕ}
    (hk : ∀ j, (k j).1 = (k j).2) :
    majorantPacketMode N rho e c theta k =
      (((((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ d : ℝ) : ℂ) := by
  classical
  have hterm : ∀ j : Fin d,
      majorantSheetCoeff N rho e (k j) *
          Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) *
            (theta j - c j) : ℝ) * Complex.I) =
        ((((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e) : ℝ) : ℂ) := by
    intro j
    rw [majorantSheetCoeff_diagonal N hrho hrhopi e (hk j)]
    have hzero : (k j).1 = (k j).2 := hk j
    rw [hzero]
    push_cast
    simp
  rw [majorantPacketMode, Finset.prod_congr rfl fun j _ => hterm j,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

theorem sum_diagonal_majorantPacketMode
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (e : ℝ) (c theta : Fin d → ℝ) :
    ∑ k ∈ Fintype.piFinset (fun _ : Fin d => diagPairs N),
        majorantPacketMode N rho e c theta k =
      ((((rho / (2 * π) + e) ^ d : ℝ) : ℂ)) := by
  classical
  have hterm : ∀ k ∈ Fintype.piFinset (fun _ : Fin d => diagPairs N),
      majorantPacketMode N rho e c theta k =
        (((((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ d : ℝ) : ℂ) := by
    intro k hk
    exact majorantPacketMode_diagonal N hrho hrhopi e c theta fun j =>
      fst_eq_snd_of_mem_diagPairs (Fintype.mem_piFinset.mp hk j)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Fintype.card_piFinset]
  have hcard : (∏ _j : Fin d, (diagPairs N).card) = (N + 1) ^ d := by
    rw [Finset.prod_congr rfl fun j _ => card_diagPairs N, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [hcard, nsmul_eq_mul]
  push_cast
  rw [mul_pow, ← mul_assoc]
  rw [show ((N : ℂ) + 1) ^ d * (((N : ℂ) + 1)⁻¹) ^ d = 1 by
    rw [← mul_pow, mul_inv_cancel₀ (by
      have hR : ((N : ℝ) + 1) ≠ 0 := by positivity
      intro h
      exact hR (by exact_mod_cast h)), one_pow]]
  rw [one_mul]

theorem periodicProductFejerMajorant_eq_const_add
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (c theta : Fin d → ℝ) :
    ((periodicProductFejerMajorant N rho c theta : ℝ) : ℂ) =
      ((((rho / (2 * π) + periodicTentFejerError N rho) ^ d : ℝ) : ℂ)) +
        ∑ k ∈ nonconstantPacketIndexSet N d,
          majorantPacketMode N rho (periodicTentFejerError N rho) c theta k := by
  classical
  have hsub : Fintype.piFinset (fun _ : Fin d => diagPairs N) ⊆
      Fintype.piFinset (fun _ : Fin d =>
        Finset.range (N + 1) ×ˢ Finset.range (N + 1)) :=
    Fintype.piFinset_subset _ _ fun _ => diagPairs_subset N
  rw [periodicProductFejerMajorant_eq_modeSum, ← Finset.sum_sdiff hsub,
    sum_diagonal_majorantPacketMode N hrho hrhopi]
  change
    (∑ k ∈ nonconstantPacketIndexSet N d,
      majorantPacketMode N rho (periodicTentFejerError N rho) c theta k) +
        ((((rho / (2 * π) + periodicTentFejerError N rho) ^ d : ℝ) : ℂ)) = _
  exact add_comm _ _

/-- Time-independent amplitude of a shifted-majorant sheet. -/
noncomputable def majorantPacketAmp
    (N : ℕ) (rho e : ℝ) (c : Fin d → ℝ)
    (k : Fin d → ℕ × ℕ) : ℂ :=
  ∏ j, majorantSheetCoeff N rho e (k j) *
    Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) * Complex.I)

theorem majorantPacketMode_linearPhase
    (N : ℕ) (rho e : ℝ) (c omega : Fin d → ℝ)
    (k : Fin d → ℕ × ℕ) (t : ℝ) :
    majorantPacketMode N rho e c (fun j => t * omega j) k =
      majorantPacketAmp N rho e c k *
        Complex.exp ((t : ℂ) * (packetFreq omega k : ℂ) * Complex.I) := by
  classical
  have hchar : Complex.exp ((t : ℂ) * (packetFreq omega k : ℂ) * Complex.I) =
      ∏ j, Complex.exp ((((((k j).1 : ℝ) - ((k j).2 : ℝ)) * omega j * t : ℝ)) *
        Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    rw [packetFreq]
    push_cast
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [majorantPacketAmp, hchar, ← Finset.prod_mul_distrib, majorantPacketMode]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hexp :
      Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) *
          (t * omega j - c j) : ℝ) * Complex.I) =
        Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) * Complex.I) *
          Complex.exp (((((k j).1 : ℝ) - ((k j).2 : ℝ)) * omega j * t : ℝ) *
            Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

theorem norm_majorantSheetCoeff_le
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    {e : ℝ} (he : 0 ≤ e) (pq : ℕ × ℕ) :
    ‖majorantSheetCoeff N rho e pq‖ ≤
      ((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e) := by
  have hinv : ‖((N : ℂ) + 1)⁻¹‖ = ((N : ℝ) + 1)⁻¹ := by
    rw [norm_inv]
    congr 1
    have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [majorantSheetCoeff]
  calc
    ‖((N : ℂ) + 1)⁻¹ *
          perFourierCoeff (perTent rho) ((pq.1 : ℝ) - (pq.2 : ℝ)) +
        (if pq.1 = pq.2 then ((N : ℂ) + 1)⁻¹ * (e : ℂ) else 0)‖ ≤
      ‖((N : ℂ) + 1)⁻¹ *
          perFourierCoeff (perTent rho) ((pq.1 : ℝ) - (pq.2 : ℝ))‖ +
        ‖if pq.1 = pq.2 then ((N : ℂ) + 1)⁻¹ * (e : ℂ) else 0‖ :=
      norm_add_le _ _
    _ ≤ ((N : ℝ) + 1)⁻¹ * (rho / (2 * π)) +
        ((N : ℝ) + 1)⁻¹ * e := by
      apply add_le_add
      · rw [norm_mul, hinv]
        exact mul_le_mul_of_nonneg_left
          (norm_perFourierCoeff_perTent_le hrho hrhopi _) (by positivity)
      · split_ifs
        · rw [norm_mul, hinv, Complex.norm_real, Real.norm_of_nonneg he]
        · simpa using mul_nonneg (by positivity : 0 ≤ ((N : ℝ) + 1)⁻¹) he
    _ = ((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e) := by ring

theorem norm_majorantPacketAmp_le
    (N : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    {e : ℝ} (he : 0 ≤ e) (c : Fin d → ℝ) (k : Fin d → ℕ × ℕ) :
    ‖majorantPacketAmp N rho e c k‖ ≤
      (((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ d := by
  classical
  calc
    ‖majorantPacketAmp N rho e c k‖ =
        ∏ j, ‖majorantSheetCoeff N rho e (k j) *
          Complex.exp ((-((((k j).1 : ℝ) - ((k j).2 : ℝ)) * c j) : ℝ) *
            Complex.I)‖ := by
      rw [majorantPacketAmp, norm_prod]
    _ ≤ ∏ _j : Fin d, ((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e) := by
      refine Finset.prod_le_prod (fun j _ => norm_nonneg _) ?_
      intro j _
      rw [norm_mul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, sub_zero, Real.exp_zero, mul_one]
      exact norm_majorantSheetCoeff_le N hrho hrhopi he (k j)
    _ = (((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_majorantPacketAmp_center_independent
    (N : ℕ) (rho e : ℝ) (c c' : Fin d → ℝ) (k : Fin d → ℕ × ℕ) :
    ‖majorantPacketAmp N rho e c k‖ = ‖majorantPacketAmp N rho e c' k‖ := by
  classical
  simp only [majorantPacketAmp, norm_prod, norm_mul, Complex.norm_exp]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  simp

/-- Exact multiplicative Fourier cost of the shifted nonconstant sheets. -/
noncomputable def periodicFejerMajorantMultiplicativeCost
    (N : ℕ) (rho e : ℝ) (c : Fin d → ℝ) (eps : ℝ) : ℝ :=
  KleinbockMargulis.indexedMultiplicativeFourierL1Cost
    (ι := {k // k ∈ nonconstantPacketIndexSet N d})
    (fun k => majorantPacketAmp N rho e c k.1)
    (fun k => packetCharacter k.1) eps

theorem periodicFejerMajorantMultiplicativeCost_center_independent
    (N : ℕ) (rho e : ℝ) (c c' : Fin d → ℝ) (eps : ℝ) :
    periodicFejerMajorantMultiplicativeCost N rho e c eps =
      periodicFejerMajorantMultiplicativeCost N rho e c' eps := by
  classical
  simp only [periodicFejerMajorantMultiplicativeCost,
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost]
  apply Finset.sum_congr rfl
  intro k _
  rw [norm_majorantPacketAmp_center_independent N rho e c c' k.1]

/-- Same strong-extremality constant controls every translated tensor
majorant; its Haar term is multiplicative in dimension. -/
theorem exists_uniform_periodicProductFejerMajorant_multiplicativeWindowDiscrepancy
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : Fin d → ℝ) (u T : ℝ), 0 < T →
      ‖((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ((periodicProductFejerMajorant N rho c
              (fun j => t * omega j) : ℝ) : ℂ)) -
          ((((rho / (2 * π) + periodicTentFejerError N rho) ^ d : ℝ) : ℂ))‖ ≤
        (2 * C / T) * periodicFejerMajorantMultiplicativeCost N rho
          (periodicTentFejerError N rho) c eps := by
  classical
  set S := nonconstantPacketIndexSet N d with hS
  obtain ⟨C, hC, hpacket⟩ :=
    KleinbockMargulis.exists_global_indexedFourierPacketHaarDiscrepancy
      (n := d) (ι := {k // k ∈ S}) homega heps
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hpoint : ∀ t : ℝ,
      ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ) =
        ((((rho / (2 * π) + periodicTentFejerError N rho) ^ d : ℝ) : ℂ)) +
          ∑ i : {k // k ∈ S},
            majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1 *
              Complex.exp ((t : ℂ) *
                (KleinbockMargulis.dotProd (packetCharacter i.1) omega : ℂ) *
                  Complex.I) := by
    intro t
    rw [periodicProductFejerMajorant_eq_const_add N hrho hrhopi]
    rw [← hS]
    congr 1
    rw [Finset.sum_coe_sort S (fun k =>
      majorantPacketAmp N rho (periodicTentFejerError N rho) c k *
        Complex.exp ((t : ℂ) *
          (KleinbockMargulis.dotProd (packetCharacter k) omega : ℂ) * Complex.I))]
    exact Finset.sum_congr rfl fun k _ => by
      rw [majorantPacketMode_linearPhase N rho (periodicTentFejerError N rho)
        c omega k t, dotProd_packetCharacter]
  have hmain := hpacket
    (((rho / (2 * π) + periodicTentFejerError N rho) ^ d : ℝ) : ℂ)
    (fun i : {k // k ∈ S} =>
      majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1)
    (fun i : {k // k ∈ S} => packetCharacter i.1)
    (fun i => by
      apply packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet
      rw [← hS]
      exact i.2) u T hT
  rw [show periodicFejerMajorantMultiplicativeCost N rho
      (periodicTentFejerError N rho) c eps =
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost
      (fun i : {k // k ∈ S} =>
        majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1)
      (fun i : {k // k ∈ S} => packetCharacter i.1) eps by rfl]
  have hInt :
      (∫ t in u..(u + T),
        ((periodicProductFejerMajorant N rho c
          (fun j => t * omega j) : ℝ) : ℂ)) =
      ∫ t in u..(u + T),
        (((((rho / (2 * π) + periodicTentFejerError N rho) ^ d : ℝ) : ℂ)) +
          ∑ i : {k // k ∈ S},
            majorantPacketAmp N rho (periodicTentFejerError N rho) c i.1 *
              Complex.exp ((t : ℂ) *
                (KleinbockMargulis.dotProd (packetCharacter i.1) omega : ℂ) *
                  Complex.I)) :=
    intervalIntegral.integral_congr fun t _ => hpoint t
  rw [hInt]
  exact hmain

theorem continuous_periodicProductFejerMajorant
    (N : ℕ) (rho : ℝ) (c omega : Fin d → ℝ) :
    Continuous fun t : ℝ =>
      periodicProductFejerMajorant N rho c (fun j => t * omega j) := by
  unfold periodicProductFejerMajorant
  refine continuous_finsetProd _ fun j _ => ?_
  exact ((continuous_fejerConv N (continuous_perTent rho) (periodic_perTent rho)).comp
    (by fun_prop)).add continuous_const

/-- Tensor-majorant upper law for the actual product tent. The former
additive `d * error` term is replaced by the multiplicative Haar term
`(rho/(2*pi) + error)^d`. -/
theorem exists_uniform_windowMean_periodicProductTent_le_tensorMajorant
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (c : Fin d → ℝ) (u T : ℝ), 0 < T →
      (1 / T) * ∫ t in u..(u + T),
          periodicProductTent rho c (fun j => t * omega j) ≤
        (rho / (2 * π) + periodicTentFejerError N rho) ^ d +
          (2 * C / T) * periodicFejerMajorantMultiplicativeCost N rho
            (periodicTentFejerError N rho) c eps := by
  obtain ⟨C, hC, hdisc⟩ :=
    exists_uniform_periodicProductFejerMajorant_multiplicativeWindowDiscrepancy
      homega heps N hrho hrhopi
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hcontM := continuous_periodicProductFejerMajorant N rho c omega
  have hcontT := continuous_periodicProductTent rho c omega
  have hd := hdisc c u T hT
  let Z : ℂ :=
    ((1 / (T : ℂ)) *
        ∫ t in u..(u + T),
          ((periodicProductFejerMajorant N rho c
            (fun j => t * omega j) : ℝ) : ℂ)) -
      ((((rho / (2 * π) + periodicTentFejerError N rho) ^ d : ℝ) : ℂ))
  have hre : |Z.re| ≤ ‖Z‖ := Complex.abs_re_le_norm Z
  have hdZ : ‖Z‖ ≤
      (2 * C / T) * periodicFejerMajorantMultiplicativeCost N rho
        (periodicTentFejerError N rho) c eps := by
    simpa [Z] using hd
  have hupper := (abs_le.mp (hre.trans hdZ)).2
  dsimp [Z] at hupper
  rw [re_window_mean_ofReal hcontM hT u] at hupper
  have hpi : u ≤ u + T := by linarith
  have hmono :
      (∫ t in u..(u + T),
          periodicProductTent rho c (fun j => t * omega j)) ≤
        ∫ t in u..(u + T),
          periodicProductFejerMajorant N rho c (fun j => t * omega j) := by
    refine intervalIntegral.integral_mono_on hpi
      (hcontT.intervalIntegrable _ _) (hcontM.intervalIntegrable _ _) ?_
    intro t _
    exact periodicProductTent_le_periodicProductFejerMajorant N hrho c _
  have hupper' :
      (1 / T) * ∫ t in u..(u + T),
          periodicProductFejerMajorant N rho c (fun j => t * omega j) ≤
        (rho / (2 * π) + periodicTentFejerError N rho) ^ d +
          (2 * C / T) * periodicFejerMajorantMultiplicativeCost N rho
            (periodicTentFejerError N rho) c eps := by
    linarith
  exact le_trans (mul_le_mul_of_nonneg_left hmono (by positivity)) hupper'

/-- Explicit centre-free cost envelope for the tensor majorant. -/
noncomputable def periodicFejerMajorantMultiplicativeCostUpperBound
    (N d : ℕ) (rho e eps : ℝ) : ℝ :=
  ((N : ℝ) + 1) ^ (2 * d) *
    (((((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ d) *
      (2 * ((N : ℝ) + 1)) ^ ((d : ℝ) * (1 + eps)))

theorem periodicFejerMajorantMultiplicativeCost_le_explicit
    (N : ℕ) {rho e eps : ℝ} (hrho : 0 < rho) (hrhopi : rho ≤ π)
    (he : 0 ≤ e) (heps : 0 ≤ eps) (c : Fin d → ℝ) :
    periodicFejerMajorantMultiplicativeCost N rho e c eps ≤
      periodicFejerMajorantMultiplicativeCostUpperBound N d rho e eps := by
  classical
  let A : ℝ := (((N : ℝ) + 1)⁻¹ * (rho / (2 * π) + e)) ^ d
  let W : ℝ := (2 * ((N : ℝ) + 1)) ^ ((d : ℝ) * (1 + eps))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hW : 0 ≤ W := Real.rpow_nonneg (by positivity) _
  rw [periodicFejerMajorantMultiplicativeCost,
    KleinbockMargulis.indexedMultiplicativeFourierL1Cost]
  calc
    (∑ k : {k // k ∈ nonconstantPacketIndexSet N d},
        ‖majorantPacketAmp N rho e c k.1‖ *
          (KleinbockMargulis.PiPlus (packetCharacter k.1) /
            KleinbockMargulis.PiPlus (packetCharacter k.1) ^ (-eps))) ≤
      ∑ _k : {k // k ∈ nonconstantPacketIndexSet N d}, A * W := by
        refine Finset.sum_le_sum fun k _ => ?_
        apply mul_le_mul
        · exact norm_majorantPacketAmp_le N hrho hrhopi he c k.1
        · exact packetCharacter_multiplicativeWeight_le N heps k.2
        · have hP := KleinbockMargulis.PiPlus_pos (packetCharacter k.1)
          exact div_nonneg hP.le (Real.rpow_pos_of_pos hP _).le
        · exact hA
    _ = (((nonconstantPacketIndexSet N d).card : ℝ) * (A * W)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      exact_mod_cast Fintype.card_coe (nonconstantPacketIndexSet N d)
    _ ≤ ((N : ℝ) + 1) ^ (2 * d) * (A * W) := by
      exact mul_le_mul_of_nonneg_right (card_modeIndex_le (d := d) N)
        (mul_nonneg hA hW)
    _ = periodicFejerMajorantMultiplicativeCostUpperBound N d rho e eps := by rfl

/-- **Tensorized adaptive finite-union law.** Complete finite target unions
pay a multiplicative box mass; no additive dimension-linear approximation
remainder remains. -/
theorem exists_adaptiveFiniteCubeUnion_tensorMajorantWindowUpper
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps : ℝ} (heps : 0 < eps) (N m : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : 2 * rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : Fin m → Fin d → ℝ) (u T : ℝ), 0 < T →
        (volume (finiteCubeVisit rho c omega ∩ Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
              (2 * C / T) * ∑ a : Fin m,
                periodicFejerMajorantMultiplicativeCost N (2 * rho)
                  (periodicTentFejerError N (2 * rho)) (c a) eps) := by
  have h2rho : 0 < 2 * rho := by positivity
  obtain ⟨C, hC, hsingle⟩ :=
    exists_uniform_windowMean_periodicProductTent_le_tensorMajorant
      homega heps N h2rho hrhopi
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  have hcont : ∀ a : Fin m, Continuous fun t : ℝ =>
      periodicProductTent (2 * rho) (c a) (fun j => t * omega j) :=
    fun a => continuous_periodicProductTent (2 * rho) (c a) omega
  have hsumInt :
      (1 / T) * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
            (fun j => t * omega j) ≤
        ((m : ℕ) : ℝ) *
            (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
          (2 * C / T) * ∑ a : Fin m,
            periodicFejerMajorantMultiplicativeCost N (2 * rho)
              (periodicTentFejerError N (2 * rho)) (c a) eps := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      calc
        ∑ a : Fin m, (1 / T) *
            ∫ t in u..(u + T),
              periodicProductTent (2 * rho) (c a) (fun j => t * omega j) ≤
          ∑ a : Fin m,
            ((2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
              (2 * C / T) * periodicFejerMajorantMultiplicativeCost N (2 * rho)
                (periodicTentFejerError N (2 * rho)) (c a) eps) := by
            exact Finset.sum_le_sum fun a _ => hsingle (c a) u T hT
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    · intro a _
      exact (hcont a).intervalIntegrable u (u + T)
  have hle : u ≤ u + T := by linarith
  have hfin : volume (Set.Ioc u (u + T)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hIf : IntegrableOn
      (Set.indicator (finiteCubeVisit rho c omega) (fun _ => (1 : ℝ)))
      (Set.Ioc u (u + T)) :=
    (integrableOn_const (C := (1 : ℝ)) hfin (by simp)).indicator
      (measurableSet_finiteCubeVisit rho c omega)
  have hIg : IntegrableOn
      (fun t => (2 : ℝ) ^ d * ∑ a : Fin m,
        periodicProductTent (2 * rho) (c a) (fun j => t * omega j))
      (Set.Ioc u (u + T)) := by
    have hc : Continuous fun t : ℝ => ∑ a : Fin m,
        periodicProductTent (2 * rho) (c a) (fun j => t * omega j) :=
      continuous_finsetSum _ fun a _ => hcont a
    exact (continuous_const.mul hc).intervalIntegrable u (u + T) |>.1
  have hmono :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho c omega) (fun _ => (1 : ℝ)) t ≤
        ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ d * ∑ a : Fin m,
            periodicProductTent (2 * rho) (c a) (fun j => t * omega j) :=
    setIntegral_mono_on hIf hIg measurableSet_Ioc fun t _ =>
      indicator_finiteCubeVisit_le_scaled_sum_tent hrho c omega t
  have hind :
      ∫ t in Set.Ioc u (u + T),
          Set.indicator (finiteCubeVisit rho c omega) (fun _ => (1 : ℝ)) t =
        (volume (finiteCubeVisit rho c omega ∩ Set.Ioc u (u + T))).toReal := by
    rw [setIntegral_indicator (measurableSet_finiteCubeVisit rho c omega),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [Set.inter_comm]
  have hright :
      ∫ t in Set.Ioc u (u + T),
          (2 : ℝ) ^ d * ∑ a : Fin m,
            periodicProductTent (2 * rho) (c a) (fun j => t * omega j) =
        (2 : ℝ) ^ d * ∫ t in u..(u + T),
          ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
            (fun j => t * omega j) := by
    rw [← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_const_mul]
  rw [hind, hright] at hmono
  have hTmul := mul_le_mul_of_nonneg_left hsumInt (le_of_lt hT)
  have hInt :
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
          (fun j => t * omega j)) ≤
        T * (((m : ℕ) : ℝ) *
              (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
            (2 * C / T) * ∑ a : Fin m,
              periodicFejerMajorantMultiplicativeCost N (2 * rho)
                (periodicTentFejerError N (2 * rho)) (c a) eps) := by
    calc
      (∫ t in u..(u + T),
        ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
          (fun j => t * omega j)) =
          T * ((1 / T) * ∫ t in u..(u + T),
            ∑ a : Fin m, periodicProductTent (2 * rho) (c a)
              (fun j => t * omega j)) := by field_simp
      _ ≤ _ := hTmul
  have hscale : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
  exact hmono.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hInt hscale)

/-- Explicit center-free version of the tensorized complete-union law. -/
theorem exists_adaptiveFiniteCubeUnion_centerFreeTensorMajorantWindowUpper
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps : ℝ} (heps : 0 < eps) (N m : ℕ) {rho : ℝ}
    (hrho : 0 < rho) (hrhopi : 2 * rho ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : Fin m → Fin d → ℝ) (u T : ℝ), 0 < T →
        (volume (finiteCubeVisit rho c omega ∩ Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (2 * rho / (2 * π) + periodicTentFejerError N (2 * rho)) ^ d +
              (2 * C / T) * ((m : ℝ) *
                periodicFejerMajorantMultiplicativeCostUpperBound N d (2 * rho)
                  (periodicTentFejerError N (2 * rho)) eps)) := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_adaptiveFiniteCubeUnion_tensorMajorantWindowUpper
      homega heps N m hrho hrhopi
  refine ⟨C, hC, ?_⟩
  intro c u T hT
  refine (hbase c u T hT).trans ?_
  have he : 0 ≤ periodicTentFejerError N (2 * rho) :=
    (periodicTentFejerError_pos N (by positivity)).le
  have hsum :
      (∑ a : Fin m,
          periodicFejerMajorantMultiplicativeCost N (2 * rho)
            (periodicTentFejerError N (2 * rho)) (c a) eps) ≤
        (m : ℝ) * periodicFejerMajorantMultiplicativeCostUpperBound N d (2 * rho)
          (periodicTentFejerError N (2 * rho)) eps := by
    calc
      (∑ a : Fin m,
          periodicFejerMajorantMultiplicativeCost N (2 * rho)
            (periodicTentFejerError N (2 * rho)) (c a) eps) ≤
        ∑ _a : Fin m,
          periodicFejerMajorantMultiplicativeCostUpperBound N d (2 * rho)
            (periodicTentFejerError N (2 * rho)) eps := by
        exact Finset.sum_le_sum fun a _ =>
          periodicFejerMajorantMultiplicativeCost_le_explicit N
            (by positivity) hrhopi he heps.le _
      _ = (m : ℝ) *
          periodicFejerMajorantMultiplicativeCostUpperBound N d (2 * rho)
            (periodicTentFejerError N (2 * rho)) eps := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  gcongr

/-- Arbitrary projective-Choi target families inherit the center-free
tensor-majorant law. -/
theorem exists_zeroAnchoredMetricBallFamilyAngularVisit_centerFreeTensorWindowUpper
    {omega : Fin d → ℝ}
    (homega : ¬ KleinbockMargulis.VWMA omega)
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta)
    (N m : ℕ)
    (hsmall : 2 * zeroAnchoredChoiAngularRadius d delta ≤ π) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
        (u T : ℝ), 0 < T →
        (volume
          (zeroAnchoredMetricBallFamilyAngularVisit d m delta target omega ∩
            Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (2 * zeroAnchoredChoiAngularRadius d delta / (2 * π) +
                  periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius d delta)) ^ d +
              (2 * C / T) * ((m : ℝ) *
                periodicFejerMajorantMultiplicativeCostUpperBound N d
                  (2 * zeroAnchoredChoiAngularRadius d delta)
                  (periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius d delta)) eps)) := by
  let rho : ℝ := zeroAnchoredChoiAngularRadius d delta
  have hrho : 0 < rho := by
    change 0 < zeroAnchoredChoiAngularRadius d delta
    rw [zeroAnchoredChoiAngularRadius]
    positivity
  obtain ⟨C, hC, hcube⟩ :=
    exists_adaptiveFiniteCubeUnion_centerFreeTensorMajorantWindowUpper
      homega heps N m hrho (by simpa only [rho] using hsmall)
  refine ⟨C, hC, ?_⟩
  intro target u T hT
  have hsub :
      zeroAnchoredMetricBallFamilyAngularVisit d m delta target omega ∩
          Set.Ioc u (u + T) ⊆
        finiteCubeVisit rho
            (fun a => zeroAnchoredMetricBallAngularCenter d (target a) delta) omega ∩
          Set.Ioc u (u + T) :=
    Set.inter_subset_inter_left _
      (zeroAnchoredMetricBallFamilyAngularVisit_subset_finiteCubeVisit
        d m hdelta target omega)
  have hrhsFinite :
      volume
          (finiteCubeVisit rho
              (fun a => zeroAnchoredMetricBallAngularCenter d (target a) delta) omega ∩
            Set.Ioc u (u + T)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top measure_Ioc_lt_top.ne
      (measure_mono Set.inter_subset_right)
  have hreal :
      (volume
        (zeroAnchoredMetricBallFamilyAngularVisit d m delta target omega ∩
          Set.Ioc u (u + T))).toReal ≤
      (volume
        (finiteCubeVisit rho
            (fun a => zeroAnchoredMetricBallAngularCenter d (target a) delta) omega ∩
          Set.Ioc u (u + T))).toReal := by
    rw [← measureReal_def, ← measureReal_def]
    exact measureReal_mono hsub hrhsFinite
  have hc := hcube
    (fun a => zeroAnchoredMetricBallAngularCenter d (target a) delta) u T hT
  exact hreal.trans (by simpa only [rho] using hc)

/-- Complete center-free tensor-majorant law carried by one frequency
packet. -/
def HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
    (omega : Fin d → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
    ∀ N m : ℕ, 2 * zeroAnchoredChoiAngularRadius d delta ≤ π →
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
        (u T : ℝ), 0 < T →
        (volume
          (zeroAnchoredMetricBallFamilyAngularVisit d m delta target omega ∩
            Set.Ioc u (u + T))).toReal ≤
          (2 : ℝ) ^ d * T *
            (((m : ℕ) : ℝ) *
                (2 * zeroAnchoredChoiAngularRadius d delta / (2 * π) +
                  periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius d delta)) ^ d +
              (2 * C / T) * ((m : ℝ) *
                periodicFejerMajorantMultiplicativeCostUpperBound N d
                  (2 * zeroAnchoredChoiAngularRadius d delta)
                  (periodicTentFejerError N
                    (2 * zeroAnchoredChoiAngularRadius d delta)) eps))

theorem hasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper_of_not_vwma
    {omega : Fin d → ℝ} (homega : ¬ KleinbockMargulis.VWMA omega) :
    HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper omega := by
  intro eps heps delta hdelta N m hsmall
  exact exists_zeroAnchoredMetricBallFamilyAngularVisit_centerFreeTensorWindowUpper
    homega heps hdelta N m hsmall

variable {K D n : ℕ} {P : Fin K → Matrix (Fin D) (Fin D) ℂ}

theorem volume_not_hasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper_eq_zero
    [NeZero K]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock)
    (hac : anchor ≠ clock) :
    volume {x ∈ simpleEnsembleLocus hP |
      ¬ HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
        (fun k => anchoredGapRatioMap
          (sortedEnsembleSpectrum hP x) anchor clock ι k)} = 0 := by
  refine measure_mono_null ?_
    (volume_vwma_sortedGapRatio_eq_zero hP hS hι hanchor hclock hac)
  rintro x ⟨hx, hfail⟩
  refine ⟨hx, ?_⟩
  by_contra hvwma
  exact hfail
    (hasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper_of_not_vwma hvwma)

/-- **One-draw tensorized projective-Choi law.** Almost every standard
Gaussian nearest-neighbour time-independent Pauli Hamiltonian has simple
spectrum and the center-free complete-union law without a dimension-linear
approximation remainder. -/
theorem chainGapRatio_hasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper_ae_stdGaussian
    (k : ℕ)
    {anchor clock : Fin (2 ^ (k + 3))}
    {ι : Fin n → Fin (2 ^ (k + 3))}
    (hι : Function.Injective ι) (hanchor : ∀ j, ι j ≠ anchor)
    (hclock : ∀ j, ι j ≠ clock) (hac : anchor ≠ clock) :
    ∀ᵐ x ∂(ProbabilityTheory.stdGaussian
      (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))),
      WithLp.ofLp x ∈ simpleEnsembleLocus
        (chainPauliFin_isHermitian (k + 3)) ∧
      HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
        (fun j => anchoredGapRatioMap
          (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3))
            (WithLp.ofLp x)) anchor clock ι j) := by
  classical
  let m := Fintype.card (ChainLabel (k + 3))
  let hP := chainPauliFin_isHermitian (k + 3)
  have hmp := PiLp.volume_preserving_ofLp (Fin m)
  have hnullSimple :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} = 0 := by
    have hsub :
        {theta : Fin m → ℝ | theta ∉ simpleEnsembleLocus hP} ⊆
          {theta | ¬ MaximallyProjectiveEnergy
            (isHermitian_spectralEnsembleMatrix hP theta).eigenvalues} := by
      intro theta htheta hmax
      exact htheta hmax.injective
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {theta | theta ∉ simpleEnsembleLocus hP} = 0 :=
      measure_mono_null hsub (volume_notMaximallyProjective_chain_eq_zero k)
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∉ simpleEnsembleLocus hP} =
          WithLp.ofLp ⁻¹' {theta | theta ∉ simpleEnsembleLocus hP} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullLaw :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
          ¬ HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
            (fun j => anchoredGapRatioMap
              (sortedEnsembleSpectrum hP (WithLp.ofLp x))
              anchor clock ι j)} = 0 := by
    have hbase :
        (volume : Measure (Fin m → ℝ))
          {theta ∈ simpleEnsembleLocus hP |
            ¬ HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP theta) anchor clock ι j)} = 0 :=
      volume_not_hasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper_eq_zero
        hP (chainPauliFin_spectrumEscapesRealRelations k)
        hι hanchor hclock hac
    have hpre :
        {x : EuclideanSpace ℝ (Fin m) |
          WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)} =
          WithLp.ofLp ⁻¹' {theta ∈ simpleEnsembleLocus hP |
            ¬ HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP theta) anchor clock ι j)} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullBad :
      (volume : Measure (EuclideanSpace ℝ (Fin m)))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    measure_union_null hnullSimple hnullLaw
  have hgauss :
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasAdaptiveProjectiveChoiUnionCenterFreeTensorWindowUpper
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                anchor clock ι j)}) = 0 :=
    (stdGaussian_absolutelyContinuous_volume_finEuclidean m) hnullBad
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hgauss)
  intro x hx
  by_cases hs : WithLp.ofLp x ∈ simpleEnsembleLocus hP
  · exact Or.inr ⟨hs, fun hlaw => hx ⟨hs, hlaw⟩⟩
  · exact Or.inl hs

end


end GaloisForLFunctions.HTGeometry
