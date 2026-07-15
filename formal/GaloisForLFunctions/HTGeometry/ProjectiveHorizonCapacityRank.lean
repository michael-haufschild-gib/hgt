import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFiniteJetRank
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonCapacity

/-!
# Exact algebraic rank of higher-rank projective horizon packets

For the normal-form chart transition `(q,v)=(p⁻¹,p⁻¹u)`, this module constructs every
finite transition jet as a universal polynomial.  Its Jacobian at an exponential longitudinal
base point and zero transverse base point is block diagonal: the longitudinal block is the
reciprocal Pascal minor and every transverse block is a weighted Pascal minor.  The resulting
nonzero determinant feeds the characteristic-zero Jacobian criterion.

Combining the maximal independent subpacket with ambient and displayed-coordinate upper bounds
gives exact algebraic-matroid rank `d * finiteHorizonObservationRank m n N`.  The last section
identifies the universal polynomials with the actual differential jets of a differential-generic
projective source.
-/

open scoped BigOperators Differential
open Matrix MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Replace one coordinate of a family by its multiplicative inverse. -/
noncomputable def singleInverseCoordinateFamily
    {I E : Type*} [DecidableEq I] [Field E]
    (x : I → E) (i₀ : I) : I → E :=
  fun i => if i = i₀ then (x i₀)⁻¹ else x i

/-- Inverting one member of an algebraically independent family preserves independence. -/
theorem singleInverseCoordinateFamily_algebraicIndependent
    {F E I : Type*} [Field F] [Field E] [Algebra F E] [DecidableEq I]
    (x : I → E) (hx : AlgebraicIndependent F x) (i₀ : I) :
    AlgebraicIndependent F (singleInverseCoordinateFamily x i₀) := by
  let tail : {i : I // i ≠ i₀} → E := fun i => x i
  have htail : AlgebraicIndependent F tail :=
    hx.comp Subtype.val Subtype.val_injective
  let e : Option {i : I // i ≠ i₀} ≃ I := Equiv.optionSubtypeNe i₀
  let withHead : Option {i : I // i ≠ i₀} → E :=
    fun o => o.elim (x i₀) tail
  have hwithHeadComp : withHead ∘ e.symm = x := by
    funext i
    by_cases hi : i = i₀
    · subst i
      simp [withHead, e]
    · simp [withHead, tail, e, Equiv.optionSubtypeNe_symm_of_ne hi]
  have hwithHead : AlgebraicIndependent F withHead :=
    (algebraicIndependent_equiv' e.symm hwithHeadComp).mp hx
  have hheadTrans : Transcendental (Algebra.adjoin F (Set.range tail)) (x i₀) :=
    (htail.option_iff_transcendental (x i₀)).mp hwithHead
  have hinvTrans : Transcendental (Algebra.adjoin F (Set.range tail)) (x i₀)⁻¹ := by
    intro hinv
    exact hheadTrans (by simpa using hinv.inv)
  let withInverse : Option {i : I // i ≠ i₀} → E :=
    fun o => o.elim (x i₀)⁻¹ tail
  have hwithInverse : AlgebraicIndependent F withInverse :=
    (htail.option_iff_transcendental (x i₀)⁻¹).mpr hinvTrans
  have hwithInverseComp : withInverse ∘ e.symm =
      singleInverseCoordinateFamily x i₀ := by
    funext i
    by_cases hi : i = i₀
    · subst i
      simp [withInverse, e, singleInverseCoordinateFamily]
    · simp [withInverse, tail, e, singleInverseCoordinateFamily, hi,
        Equiv.optionSubtypeNe_symm_of_ne hi]
  exact (algebraicIndependent_equiv' e.symm hwithInverseComp).mpr hwithInverse

/-- The distinguished longitudinal channel of a positive-dimensional affine chart. -/
def projectiveLongitudinalChannel {d : ℕ} (hd : 0 < d) : Fin d := ⟨0, hd⟩

/-- Rename a scalar reciprocal-jet polynomial into the longitudinal channel. -/
noncomputable def longitudinalReciprocalJetPolynomial
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (j : ℕ) : MvPolynomial (Fin d × ℕ) K :=
  MvPolynomial.rename (fun k => (projectiveLongitudinalChannel hd, k))
    (universalReciprocalJetPolynomialOver K j)

/-- Universal polynomial for the projective transition `(q,v)=(p⁻¹,p⁻¹u)`. -/
noncomputable def projectiveTransitionJetPolynomial
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (c : Fin d) (j : ℕ) :
    MvPolynomial (Fin d × ℕ) K :=
  if c = projectiveLongitudinalChannel hd then
    longitudinalReciprocalJetPolynomial K hd j
  else
    ∑ k ∈ Finset.range (j + 1),
      MvPolynomial.C (Nat.choose j k : K) *
        longitudinalReciprocalJetPolynomial K hd k *
          MvPolynomial.X (c, j - k)

/-- Exponential longitudinal base point and zero transverse base point. -/
noncomputable def projectiveTransitionExponentialBase
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) : Fin d × ℕ → K
  | (c, k) =>
      if c = projectiveLongitudinalChannel hd then
        reciprocalExponentialBaseOver K k
      else 0

theorem longitudinalReciprocalJetPolynomial_aeval_base
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (j : ℕ) :
    MvPolynomial.aeval (projectiveTransitionExponentialBase K hd)
        (longitudinalReciprocalJetPolynomial K hd j) =
      algebraMap ℚ K ((1 / 2 : ℚ) ^ j) := by
  rw [longitudinalReciprocalJetPolynomial, MvPolynomial.aeval_rename]
  change MvPolynomial.aeval (reciprocalExponentialBaseOver K)
      (universalReciprocalJetPolynomialOver K j) = _
  rw [universalReciprocalJetPolynomialOver]
  calc
    MvPolynomial.aeval (reciprocalExponentialBaseOver K)
        (MvPolynomial.map (algebraMap ℚ K)
          (universalReciprocalJetPolynomial j)) =
      algebraMap ℚ K
        (MvPolynomial.aeval reciprocalExponentialBase
          (universalReciprocalJetPolynomial j)) := by
        simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
        rw [MvPolynomial.eval₂_comp_right]
        have hmapid : MvPolynomial.map (algebraMap ℚ ℚ)
            (universalReciprocalJetPolynomial j) =
              universalReciprocalJetPolynomial j := by
          change MvPolynomial.map (RingHom.id ℚ)
            (universalReciprocalJetPolynomial j) = _
          exact MvPolynomial.map_id _
        rw [hmapid]
        rfl
    _ = _ := by rw [universalReciprocalJetPolynomial_aeval_base]

theorem pderiv_rename_eq_zero_of_notMem
    {K σ τ : Type*} [CommSemiring K] [DecidableEq τ]
    (f : σ → τ) (j : τ) (h : ∀ i, f i ≠ j) (P : MvPolynomial σ K) :
    MvPolynomial.pderiv j (MvPolynomial.rename f P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp [map_mul, MvPolynomial.rename_X, MvPolynomial.pderiv_X, hp, h i]

theorem longitudinalReciprocalJetPolynomial_pderiv_aeval
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (c : Fin d) (k j : ℕ) :
    MvPolynomial.aeval (projectiveTransitionExponentialBase K hd)
        (MvPolynomial.pderiv (c, k)
          (longitudinalReciprocalJetPolynomial K hd j)) =
      if c = projectiveLongitudinalChannel hd then
        if k = 0 then 1 else -(Nat.choose j k : K)
      else 0 := by
  classical
  let c₀ := projectiveLongitudinalChannel hd
  by_cases hc : c = c₀
  · subst c
    rw [if_pos rfl]
    rw [longitudinalReciprocalJetPolynomial,
      MvPolynomial.pderiv_rename (f := fun s : ℕ => (c₀, s))
        (by intro a b h; exact congrArg Prod.snd h) k]
    rw [MvPolynomial.aeval_rename]
    change MvPolynomial.aeval (reciprocalExponentialBaseOver K)
        (MvPolynomial.pderiv k
          (universalReciprocalJetPolynomialOver K j)) = _
    exact universalReciprocalJetPolynomialOver_pderiv_aeval_eq K k j
  · rw [if_neg hc]
    rw [longitudinalReciprocalJetPolynomial,
      pderiv_rename_eq_zero_of_notMem]
    · simp
    · intro s hs
      exact hc (congrArg Prod.fst hs.symm)

theorem projectiveTransitionJetPolynomial_pderiv_aeval
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (c c' : Fin d) (k j : ℕ) :
    MvPolynomial.aeval (projectiveTransitionExponentialBase K hd)
        (MvPolynomial.pderiv (c', k)
          (projectiveTransitionJetPolynomial K hd c j)) =
      if c = projectiveLongitudinalChannel hd then
        if c' = projectiveLongitudinalChannel hd then
          if k = 0 then 1 else -(Nat.choose j k : K)
        else 0
      else if c' = c ∧ k ≤ j then
        (Nat.choose j k : K) * algebraMap ℚ K ((1 / 2 : ℚ) ^ (j - k))
      else 0 := by
  classical
  let c₀ := projectiveLongitudinalChannel hd
  by_cases hc : c = c₀
  · subst c
    rw [projectiveTransitionJetPolynomial, if_pos rfl,
      longitudinalReciprocalJetPolynomial_pderiv_aeval]
    rfl
  · rw [projectiveTransitionJetPolynomial, if_neg hc, if_neg hc]
    simp only [map_sum, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
      zero_mul, zero_add, map_add, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, MvPolynomial.pderiv_X, Pi.single_apply]
    change c ≠ projectiveLongitudinalChannel hd at hc
    have hXzero : ∀ s : ℕ,
        projectiveTransitionExponentialBase K hd (c, j - s) = 0 := by
      intro s
      simp only [projectiveTransitionExponentialBase]
      rw [if_neg hc]
    simp_rw [hXzero, longitudinalReciprocalJetPolynomial_aeval_base]
    simp only [mul_zero, zero_add]
    by_cases hcc : c' = c
    · subst c'
      by_cases hkj : k ≤ j
      · rw [if_pos ⟨rfl, hkj⟩]
        rw [Finset.sum_eq_single (j - k)]
        · have hsub : j - (j - k) = k := by omega
          rw [hsub, if_pos rfl, Nat.choose_symm hkj]
          simp
        · intro s hs hne
          have hsle : s ≤ j := by
            have := Finset.mem_range.mp hs
            omega
          have hneq : j - s ≠ k := by
            intro heq
            apply hne
            omega
          rw [if_neg]
          simp
          exact fun h => hneq (congrArg Prod.snd h)
        · intro hnot
          exact (hnot (Finset.mem_range.mpr (by omega))).elim
      · rw [if_neg (by simp [hkj])]
        apply Finset.sum_eq_zero
        intro s hs
        have hsle : s ≤ j := by
          have := Finset.mem_range.mp hs
          omega
        have hneq : j - s ≠ k := by omega
        rw [if_neg]
        simp
        exact fun h => hneq (congrArg Prod.snd h)
    · rw [if_neg (by simp [hcc])]
      apply Finset.sum_eq_zero
      intro s hs
      rw [if_neg]
      · simp
      · intro h
        exact hcc (congrArg Prod.fst h).symm

/-- The transverse weighted-Pascal block at the exponential base point. -/
noncomputable def projectiveTransverseLinearizationMinorOver
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (n r : ℕ) : Matrix (Fin r) (Fin r) K :=
  fun i k => (Nat.choose (n + i) k : K) *
    algebraMap ℚ K ((1 / 2 : ℚ) ^ (n + i - k))

theorem projectiveTransverseLinearizationMinorOver_det_ne_zero
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    (n r : ℕ) :
    (projectiveTransverseLinearizationMinorOver K n r).det ≠ 0 := by
  classical
  let q : K := algebraMap ℚ K (1 / 2 : ℚ)
  let P : Matrix (Fin r) (Fin r) K :=
    (shiftedPascalMatrix n r).map (Int.castRingHom K)
  let row : Fin r → K := fun i => q ^ (n + i)
  let col : Fin r → K := fun k => q⁻¹ ^ (k : ℕ)
  have hq : q ≠ 0 := by
    dsimp [q]
    norm_num
  have hmatrix : projectiveTransverseLinearizationMinorOver K n r =
      Matrix.diagonal row * P * Matrix.diagonal col := by
    ext i k
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
      projectiveTransverseLinearizationMinorOver]
    rw [map_pow]
    dsimp only [row, col]
    by_cases hle : (k : ℕ) ≤ n + (i : ℕ)
    · have hpow : q ^ (n + (i : ℕ) - (k : ℕ)) =
          q ^ (n + (i : ℕ)) * q⁻¹ ^ (k : ℕ) := by
        rw [inv_pow, pow_sub₀ q hq hle]
      change (Nat.choose (n + i) k : K) *
          q ^ (n + (i : ℕ) - (k : ℕ)) =
        q ^ (n + (i : ℕ)) *
          (Int.castRingHom K) (shiftedPascalMatrix n r i k) *
            q⁻¹ ^ (k : ℕ)
      rw [show (Int.castRingHom K) (shiftedPascalMatrix n r i k) =
          (Nat.choose (n + i) k : K) by
        simp [shiftedPascalMatrix]]
      rw [hpow]
      ring
    · have hlt : n + (i : ℕ) < (k : ℕ) := by omega
      have hchoose : Nat.choose (n + (i : ℕ)) (k : ℕ) = 0 :=
        Nat.choose_eq_zero_of_lt hlt
      simp [P, shiftedPascalMatrix, hchoose]
  have hPdet : P.det ≠ 0 := by
    have hmap := (Int.castRingHom K).map_det (shiftedPascalMatrix n r)
    change (Int.castRingHom K) (shiftedPascalMatrix n r).det = P.det at hmap
    rw [shiftedPascalMatrix_det] at hmap
    rw [← hmap]
    simp
  have hrow : (Matrix.diagonal row).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i hi
    exact pow_ne_zero _ hq
  have hcol : (Matrix.diagonal col).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k hk
    exact pow_ne_zero _ (inv_ne_zero hq)
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hrow hPdet) hcol

/-- One low-mode channel block: reciprocal longitudinal and weighted transverse blocks. -/
noncomputable def projectiveTransitionChannelMinorOver
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (n r : ℕ) (c : Fin d) :
    Matrix (Fin r) (Fin r) K :=
  if c = projectiveLongitudinalChannel hd then
    reciprocalJetZLinearizationMinorOver K n r
  else projectiveTransverseLinearizationMinorOver K n r

/-- Full low-mode projective transition minor, block diagonal in affine channels. -/
noncomputable def projectiveTransitionLowModeMinorOver
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (n r : ℕ) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) K :=
  Matrix.blockDiagonal (projectiveTransitionChannelMinorOver K hd n r)

theorem projectiveTransitionLowModeMinorOver_det_ne_zero
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (n r : ℕ) :
    (projectiveTransitionLowModeMinorOver K hd n r).det ≠ 0 := by
  classical
  rw [projectiveTransitionLowModeMinorOver, Matrix.det_blockDiagonal,
    Finset.prod_ne_zero_iff]
  intro c hc
  rw [projectiveTransitionChannelMinorOver]
  split_ifs
  · exact reciprocalJetZLinearizationMinorOver_det_ne_zero K n r
  · exact projectiveTransverseLinearizationMinorOver_det_ne_zero K n r

noncomputable def projectiveHorizonSelectedPolynomial
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (m n a r : ℕ) :
    (Fin r × Fin d) ⊕ (Fin a × Fin d) → MvPolynomial (Fin d × ℕ) K
  | Sum.inl i => projectiveTransitionJetPolynomial K hd i.2 (n + i.1)
  | Sum.inr i => MvPolynomial.X (i.2, m + i.1)

def projectiveHorizonSelectedCoordinate
    {d : ℕ} (m a r : ℕ) :
    (Fin r × Fin d) ⊕ (Fin a × Fin d) → Fin d × ℕ
  | Sum.inl k => (k.2, k.1)
  | Sum.inr k => (k.2, m + k.1)

theorem projectiveHorizonSelectedPolynomial_algebraicIndependent
    (K : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    {d : ℕ} (hd : 0 < d) (m n a r : ℕ) (hrm : r ≤ m) :
    AlgebraicIndependent K
      (projectiveHorizonSelectedPolynomial K hd m n a r) := by
  classical
  let f := projectiveHorizonSelectedPolynomial K hd m n a r
  let coordinate := projectiveHorizonSelectedCoordinate (d := d) m a r
  let M := MvPolynomial.polynomialJacobianMinor f coordinate
  let J := M.map (MvPolynomial.aeval (projectiveTransitionExponentialBase K hd))
  let C : Matrix (Fin a × Fin d) (Fin r × Fin d) K :=
    fun i k => J (Sum.inr i) (Sum.inl k)
  have hJ : J = Matrix.fromBlocks
      (projectiveTransitionLowModeMinorOver K hd n r).transpose 0 C 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [J, M, Matrix.map_apply,
          MvPolynomial.polynomialJacobianMinor, f, coordinate,
          projectiveHorizonSelectedPolynomial,
          projectiveHorizonSelectedCoordinate, Matrix.fromBlocks_apply₁₁,
          Matrix.transpose_apply]
      rw [projectiveTransitionJetPolynomial_pderiv_aeval]
      simp only [projectiveTransitionLowModeMinorOver,
        Matrix.blockDiagonal_apply, projectiveTransitionChannelMinorOver]
      by_cases hj : j.2 = projectiveLongitudinalChannel hd
      · by_cases hi : i.2 = projectiveLongitudinalChannel hd
        · simp [hj, hi, reciprocalJetZLinearizationMinorOver]
        · have h₀i : projectiveLongitudinalChannel hd ≠ i.2 :=
            fun h => hi h.symm
          simp [hj, hi, h₀i]
      · by_cases hci : i.2 = j.2
        ·
          by_cases hle : (i.1 : ℕ) ≤ n + (j.1 : ℕ)
          · simp [hj, hci, hle,
              projectiveTransverseLinearizationMinorOver]
          ·
            have hchoose : Nat.choose (n + (j.1 : ℕ)) (i.1 : ℕ) = 0 :=
              Nat.choose_eq_zero_of_lt (by omega)
            simp [hj, hci, hle,
              projectiveTransverseLinearizationMinorOver, hchoose]
        · have hjci : j.2 ≠ i.2 := Ne.symm hci
          simp [hj, hci, hjci]
    · have hne : (i.2, (i.1 : ℕ)) ≠ (j.2, m + (j.1 : ℕ)) := by
          intro h
          have hord := congrArg Prod.snd h
          omega
      simp [J, M, f, coordinate, projectiveHorizonSelectedPolynomial,
        projectiveHorizonSelectedCoordinate,
        MvPolynomial.polynomialJacobianMinor, Matrix.fromBlocks_apply₁₂, hne]
    · rfl
    · by_cases hij : i = j
      · subst j
        simp [J, M, f, coordinate, projectiveHorizonSelectedPolynomial,
          projectiveHorizonSelectedCoordinate,
          MvPolynomial.polynomialJacobianMinor]
      · have hne : (i.2, m + (i.1 : ℕ)) ≠
            (j.2, m + (j.1 : ℕ)) := by
          intro h
          apply hij
          apply Prod.ext
          · exact Fin.ext (Nat.add_left_cancel (congrArg Prod.snd h))
          · exact congrArg Prod.fst h
        simp [J, M, f, coordinate, projectiveHorizonSelectedPolynomial,
          projectiveHorizonSelectedCoordinate,
          MvPolynomial.polynomialJacobianMinor, hij, hne]
  have hJdet : J.det ≠ 0 := by
    rw [hJ, Matrix.det_fromBlocks_zero₁₂, Matrix.det_transpose,
      Matrix.det_one, mul_one]
    exact projectiveTransitionLowModeMinorOver_det_ne_zero K hd n r
  have hMdet : M.det ≠ 0 := by
    intro hzero
    have hmap :=
      (MvPolynomial.aeval (projectiveTransitionExponentialBase K hd)).map_det M
    change MvPolynomial.aeval (projectiveTransitionExponentialBase K hd) M.det =
      J.det at hmap
    rw [hzero, map_zero] at hmap
    exact hJdet hmap.symm
  exact MvPolynomial.algebraicIndependent_of_jacobian_det_ne_zero
    f coordinate hMdet

noncomputable def projectiveInverseCoordinateFamily
    {E : Type*} [Field E] {d : ℕ} (hd : 0 < d)
    (x : Fin d × ℕ → E) : Fin d × ℕ → E :=
  singleInverseCoordinateFamily x (projectiveLongitudinalChannel hd, 0)

theorem projectiveInverseCoordinateFamily_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (hx : AlgebraicIndependent F x) :
    AlgebraicIndependent F (projectiveInverseCoordinateFamily hd x) :=
  singleInverseCoordinateFamily_algebraicIndependent x hx
    (projectiveLongitudinalChannel hd, 0)

noncomputable def projectiveHorizonSelectedObservation
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (m n a r : ℕ) : (Fin r × Fin d) ⊕ (Fin a × Fin d) → E :=
  fun i => MvPolynomial.aeval (projectiveInverseCoordinateFamily hd x)
    (projectiveHorizonSelectedPolynomial F hd m n a r i)

theorem projectiveHorizonSelectedObservation_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (hx : AlgebraicIndependent F x) (m n a r : ℕ) (hrm : r ≤ m) :
    AlgebraicIndependent F
      (projectiveHorizonSelectedObservation (F := F) hd x m n a r) := by
  have hpoly := projectiveHorizonSelectedPolynomial_algebraicIndependent
    F hd m n a r hrm
  have hcoord := projectiveInverseCoordinateFamily_algebraicIndependent hd x hx
  have hinj : Function.Injective
      (MvPolynomial.aeval (projectiveInverseCoordinateFamily hd x) :
        MvPolynomial (Fin d × ℕ) F → E) :=
    algebraicIndependent_iff_injective_aeval.mp hcoord
  exact hpoly.map hinj.injOn

noncomputable def projectiveHorizonObservation
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (m n N : ℕ) :
    (Fin (finiteHorizonObservableCount N n) × Fin d) ⊕
      (Fin (finiteHorizonObservableCount N m) × Fin d) → E
  | Sum.inl i => MvPolynomial.aeval (projectiveInverseCoordinateFamily hd x)
      (projectiveTransitionJetPolynomial F hd i.2 (n + i.1))
  | Sum.inr i => projectiveInverseCoordinateFamily hd x (i.2, m + i.1)

noncomputable def projectiveFiniteAmbientCoordinate
    {E : Type*} [Field E] {d : ℕ} (hd : 0 < d)
    (x : Fin d × ℕ → E) (N : ℕ) : Fin (N + 1) × Fin d → E :=
  fun i => projectiveInverseCoordinateFamily hd x (i.2, i.1)

theorem projectiveFiniteAmbientCoordinate_algebraicIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (hx : AlgebraicIndependent F x) (N : ℕ) :
    AlgebraicIndependent F (projectiveFiniteAmbientCoordinate hd x N) := by
  have hcoord := projectiveInverseCoordinateFamily_algebraicIndependent hd x hx
  exact hcoord.comp (fun i : Fin (N + 1) × Fin d => (i.2, (i.1 : ℕ))) (by
    intro i j h
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.snd h)
    · exact congrArg Prod.fst h)

theorem longitudinalReciprocalJetPolynomial_aeval_eq_finiteReciprocalJetValue
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E) (j : ℕ) :
    MvPolynomial.aeval (projectiveInverseCoordinateFamily hd x)
        (longitudinalReciprocalJetPolynomial F hd j) =
      finiteReciprocalJetValue (F := F)
        (fun k => x (projectiveLongitudinalChannel hd, k)) j := by
  rw [longitudinalReciprocalJetPolynomial, MvPolynomial.aeval_rename]
  apply congrArg (fun v : ℕ → E =>
    MvPolynomial.aeval v (universalReciprocalJetPolynomialOver F j))
  funext k
  rcases k with _ | k
  · simp [projectiveInverseCoordinateFamily, singleInverseCoordinateFamily,
      reciprocalCoordinateFamily]
  · simp [projectiveInverseCoordinateFamily, singleInverseCoordinateFamily,
      reciprocalCoordinateFamily]

theorem longitudinalReciprocalJetPolynomial_aeval_mem_adjoin_ambient
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    {j N : ℕ} (hjN : j ≤ N) :
    MvPolynomial.aeval (projectiveInverseCoordinateFamily hd x)
        (longitudinalReciprocalJetPolynomial F hd j) ∈
      Algebra.adjoin F (Set.range (projectiveFiniteAmbientCoordinate hd x N)) := by
  rw [longitudinalReciprocalJetPolynomial_aeval_eq_finiteReciprocalJetValue]
  apply Algebra.adjoin_mono (R := F) (A := E) _
    (finiteReciprocalJetValue_mem_adjoin_ambient
      (F := F) (E := E)
      (fun k => x (projectiveLongitudinalChannel hd, k)) hjN)
  intro z hz
  obtain ⟨i, rfl⟩ := hz
  refine ⟨(i, projectiveLongitudinalChannel hd), ?_⟩
  rcases i with ⟨(_ | i), hi⟩
  · simp [projectiveFiniteAmbientCoordinate,
      projectiveInverseCoordinateFamily, singleInverseCoordinateFamily,
      finiteReciprocalAmbientCoordinate, reciprocalCoordinateFamily]
  · simp [projectiveFiniteAmbientCoordinate,
      projectiveInverseCoordinateFamily, singleInverseCoordinateFamily,
      finiteReciprocalAmbientCoordinate, reciprocalCoordinateFamily]

theorem projectiveTransitionJetPolynomial_aeval_mem_adjoin_ambient
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (c : Fin d) {j N : ℕ} (hjN : j ≤ N) :
    MvPolynomial.aeval (projectiveInverseCoordinateFamily hd x)
        (projectiveTransitionJetPolynomial F hd c j) ∈
      Algebra.adjoin F (Set.range (projectiveFiniteAmbientCoordinate hd x N)) := by
  let A := Algebra.adjoin F
    (Set.range (projectiveFiniteAmbientCoordinate hd x N))
  rw [projectiveTransitionJetPolynomial]
  split_ifs with hc
  · exact longitudinalReciprocalJetPolynomial_aeval_mem_adjoin_ambient
      (F := F) hd x hjN
  · simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    apply A.sum_mem
    intro k hk
    apply A.mul_mem
    · apply A.mul_mem
      · exact A.algebraMap_mem _
      · exact longitudinalReciprocalJetPolynomial_aeval_mem_adjoin_ambient
          (F := F) hd x (by
            have := Finset.mem_range.mp hk
            omega)
    · have hkN : j - k ≤ N := by omega
      exact Algebra.subset_adjoin
        (Set.mem_range_self
          ((⟨j - k, by omega⟩ : Fin (N + 1)), c))

theorem projectiveHorizonObservation_range_subset_closure
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    {m n N : ℕ} (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    Set.range (projectiveHorizonObservation (F := F) hd x m n N) ⊆
      (AlgebraicIndependent.matroid F E).closure
        (Set.range (projectiveFiniteAmbientCoordinate hd x N)) := by
  intro z hz
  obtain ⟨i, rfl⟩ := hz
  rw [AlgebraicIndependent.matroid_closure_eq]
  change IsAlgebraic
    (Algebra.adjoin F (Set.range (projectiveFiniteAmbientCoordinate hd x N))) _
  rcases i with i | i
  · have hjN : n + (i.1 : ℕ) ≤ N := by
      have hi := i.1.isLt
      simp only [finiteHorizonObservableCount] at hi
      omega
    have hmem := projectiveTransitionJetPolynomial_aeval_mem_adjoin_ambient
      (F := F) hd x i.2 hjN
    exact isAlgebraic_algebraMap
      (⟨_, hmem⟩ : Algebra.adjoin F
        (Set.range (projectiveFiniteAmbientCoordinate hd x N)))
  · have hidx : m + (i.1 : ℕ) ≤ N := by
      have hi := i.1.isLt
      simp only [finiteHorizonObservableCount] at hi
      omega
    have hmem : projectiveInverseCoordinateFamily hd x (i.2, m + i.1) ∈
        Algebra.adjoin F
          (Set.range (projectiveFiniteAmbientCoordinate hd x N)) :=
      Algebra.subset_adjoin
        (Set.mem_range_self ((⟨m + i.1, by omega⟩ : Fin (N + 1)), i.2))
    exact isAlgebraic_algebraMap
      (⟨_, hmem⟩ : Algebra.adjoin F
        (Set.range (projectiveFiniteAmbientCoordinate hd x N)))

noncomputable def projectiveHorizonObservationTranscendenceRank
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (m n N : ℕ) : ℕ :=
  ((AlgebraicIndependent.matroid F E).eRk
    (Set.range (projectiveHorizonObservation (F := F) hd x m n N))).toNat

/-- Exact `d`-channel rank of the universal projective transition packet. -/
theorem projectiveHorizonObservationTranscendenceRank_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F]
    {d : ℕ} (hd : 0 < d) (x : Fin d × ℕ → E)
    (hx : AlgebraicIndependent F x)
    {m n N : ℕ} (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    projectiveHorizonObservationTranscendenceRank
        (F := F) hd x m n N =
      projectiveFiniteHorizonObservationRank d m n N := by
  classical
  let a := finiteHorizonObservableCount N m
  let b := finiteHorizonObservableCount N n
  let r := min m b
  let selected := projectiveHorizonSelectedObservation
    (F := F) hd x m n a r
  let observed := projectiveHorizonObservation (F := F) hd x m n N
  let M := AlgebraicIndependent.matroid F E
  have hrm : r ≤ m := min_le_left _ _
  have hselected : AlgebraicIndependent F selected := by
    simpa [selected] using
      projectiveHorizonSelectedObservation_algebraicIndependent
        (F := F) hd x hx m n a r hrm
  have hselinj : Function.Injective selected :=
    algebraicIndependent_function_injective hselected
  have hselRange : M.Indep (Set.range selected) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    exact (algebraicIndependent_subtype_range hselinj).mpr hselected
  have hselCard : (Set.range selected).encard =
      ENat.card ((Fin r × Fin d) ⊕ (Fin a × Fin d)) := by
    calc
      (Set.range selected).encard =
          (Set.univ : Set ((Fin r × Fin d) ⊕ (Fin a × Fin d))).encard := by
        simpa only [Set.image_univ] using hselinj.encard_image Set.univ
      _ = ENat.card ((Fin r × Fin d) ⊕ (Fin a × Fin d)) :=
        Set.encard_univ _
  have hsubset : Set.range selected ⊆ Set.range observed := by
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    rcases i with i | i
    · let j : Fin b := ⟨i.1, by omega⟩
      refine ⟨Sum.inl (j, i.2), ?_⟩
      simp [selected, observed, projectiveHorizonSelectedObservation,
        projectiveHorizonSelectedPolynomial, projectiveHorizonObservation, j]
    · refine ⟨Sum.inr i, ?_⟩
      simp [selected, observed, projectiveHorizonSelectedObservation,
        projectiveHorizonSelectedPolynomial, projectiveHorizonObservation]
  have hlowerEN : ((d * (r + a) : ℕ) : ℕ∞) ≤
      M.eRk (Set.range observed) := by
    have h := hselRange.encard_le_eRk_of_subset hsubset
    rw [hselCard] at h
    simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using h
  have hambientAI :=
    projectiveFiniteAmbientCoordinate_algebraicIndependent hd x hx N
  have hambientInj : Function.Injective (projectiveFiniteAmbientCoordinate hd x N) :=
    algebraicIndependent_function_injective hambientAI
  have hambientIndep : M.Indep
      (Set.range (projectiveFiniteAmbientCoordinate hd x N)) := by
    rw [AlgebraicIndependent.matroid_indep_iff]
    exact (algebraicIndependent_subtype_range hambientInj).mpr hambientAI
  have hambientCard :
      (Set.range (projectiveFiniteAmbientCoordinate hd x N)).encard =
        ENat.card (Fin (N + 1) × Fin d) := by
    calc
      (Set.range (projectiveFiniteAmbientCoordinate hd x N)).encard =
          (Set.univ : Set (Fin (N + 1) × Fin d)).encard := by
        simpa only [Set.image_univ] using hambientInj.encard_image Set.univ
      _ = ENat.card (Fin (N + 1) × Fin d) := Set.encard_univ _
  have hambientEN : M.eRk (Set.range observed) ≤
      ((d * (N + 1) : ℕ) : ℕ∞) := by
    have hsub := projectiveHorizonObservation_range_subset_closure
      (F := F) hd x hm hn
    have h := M.eRk_mono hsub
    rw [M.eRk_closure_eq, hambientIndep.eRk_eq_encard,
      hambientCard] at h
    simpa [Nat.mul_comm] using h
  have hdisplayEN : M.eRk (Set.range observed) ≤
      ((d * (a + b) : ℕ) : ℕ∞) := by
    refine (M.eRk_le_encard (Set.range observed)).trans ?_
    calc
      (Set.range observed).encard = (observed '' Set.univ).encard := by
        rw [Set.image_univ]
      _ ≤ Set.univ.encard := Set.encard_image_le observed Set.univ
      _ = ENat.card ((Fin b × Fin d) ⊕ (Fin a × Fin d)) := Set.encard_univ _
      _ = ((d * (a + b) : ℕ) : ℕ∞) := by
        simp [Nat.mul_add, Nat.mul_comm]
        ac_rfl
  have hfinite : M.eRk (Set.range observed) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hambientEN
  have hlower : d * (r + a) ≤ (M.eRk (Set.range observed)).toNat :=
    ENat.toNat_le_toNat hlowerEN hfinite
  have hambient : (M.eRk (Set.range observed)).toNat ≤ d * (N + 1) :=
    ENat.toNat_le_toNat hambientEN (ENat.coe_ne_top _)
  have hdisplay : (M.eRk (Set.range observed)).toNat ≤ d * (a + b) :=
    ENat.toNat_le_toNat hdisplayEN (ENat.coe_ne_top _)
  have hscalar : r + a = min (N + 1) (a + b) := by
    simp [r, a, b, finiteHorizonObservableCount]
    omega
  have htarget : d * (r + a) =
      min (d * (N + 1)) (d * (a + b)) := by
    rw [hscalar, mul_min]
  change (M.eRk (Set.range observed)).toNat = _
  rw [projectiveFiniteHorizonObservationRank]
  change (M.eRk (Set.range observed)).toNat = d * (a + r)
  rw [Nat.add_comm a r]
  apply Nat.le_antisymm
  · rw [htarget]
    exact le_min hambient hdisplay
  · exact hlower

theorem projectiveTransitionJetPolynomial_differentialJet_aeval
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F] [Differential E]
    {d : ℕ} (hd : 0 < d) (source : Fin d → E)
    (h₀ : source (projectiveLongitudinalChannel hd) ≠ 0)
    (c : Fin d) (j : ℕ) :
    MvPolynomial.aeval
        (projectiveInverseCoordinateFamily hd
          (fun p : Fin d × ℕ => differentialJet p.2 (source p.1)))
        (projectiveTransitionJetPolynomial F hd c j) =
      if c = projectiveLongitudinalChannel hd then
        differentialJet j (source (projectiveLongitudinalChannel hd))⁻¹
      else
        differentialJet j
          ((source (projectiveLongitudinalChannel hd))⁻¹ * source c) := by
  classical
  let c₀ := projectiveLongitudinalChannel hd
  by_cases hc : c = c₀
  · subst c
    rw [if_pos rfl, projectiveTransitionJetPolynomial, if_pos rfl,
      longitudinalReciprocalJetPolynomial_aeval_eq_finiteReciprocalJetValue]
    exact finiteReciprocalJetValue_differentialJet_eq
      (F := F) (source c₀) h₀ j
  · rw [if_neg hc, projectiveTransitionJetPolynomial, if_neg hc]
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    have hlong : ∀ k : ℕ,
        MvPolynomial.aeval
            (projectiveInverseCoordinateFamily hd
              (fun p : Fin d × ℕ => differentialJet p.2 (source p.1)))
            (longitudinalReciprocalJetPolynomial F hd k) =
          differentialJet k (source c₀)⁻¹ := by
      intro k
      rw [longitudinalReciprocalJetPolynomial_aeval_eq_finiteReciprocalJetValue]
      exact finiteReciprocalJetValue_differentialJet_eq
        (F := F) (source c₀) h₀ k
    simp_rw [hlong]
    change c ≠ projectiveLongitudinalChannel hd at hc
    have hraw : ∀ k : ℕ,
        projectiveInverseCoordinateFamily hd
            (fun p : Fin d × ℕ => differentialJet p.2 (source p.1)) (c, k) =
          differentialJet k (source c) := by
      intro k
      simp [projectiveInverseCoordinateFamily, singleInverseCoordinateFamily, hc]
    simp_rw [hraw]
    simpa only [map_natCast, nsmul_eq_mul, mul_assoc] using
      (differentialJet_mul_binomial' j (source c₀)⁻¹ (source c)).symm

/-- The actual pair of projective differential-jet horizon packets. -/
noncomputable def finiteProjectiveDifferentialHorizonObservation
    {E : Type*} [Field E] [Differential E]
    {d : ℕ} (hd : 0 < d) (source : Fin d → E)
    (m n N : ℕ) :
    (Fin (finiteHorizonObservableCount N n) × Fin d) ⊕
      (Fin (finiteHorizonObservableCount N m) × Fin d) → E
  | Sum.inl i =>
      if i.2 = projectiveLongitudinalChannel hd then
        differentialJet (n + i.1) (source (projectiveLongitudinalChannel hd))⁻¹
      else differentialJet (n + i.1)
        ((source (projectiveLongitudinalChannel hd))⁻¹ * source i.2)
  | Sum.inr i => differentialJet (m + i.1) (source i.2)

theorem projectiveHorizonObservation_differentialJet_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F] [Differential E]
    {d : ℕ} (hd : 0 < d) (source : Fin d → E)
    (h₀ : source (projectiveLongitudinalChannel hd) ≠ 0)
    {m n N : ℕ} (hm0 : 0 < m) :
    projectiveHorizonObservation (F := F) hd
        (fun p : Fin d × ℕ => differentialJet p.2 (source p.1)) m n N =
      finiteProjectiveDifferentialHorizonObservation hd source m n N := by
  funext i
  rcases i with i | i
  · exact projectiveTransitionJetPolynomial_differentialJet_aeval
      (F := F) hd source h₀ i.2 (n + i.1)
  · rcases m with _ | m
    · omega
    · simp [projectiveHorizonObservation,
        finiteProjectiveDifferentialHorizonObservation,
        projectiveInverseCoordinateFamily, singleInverseCoordinateFamily,
        Nat.succ_add]

noncomputable def finiteProjectiveDifferentialHorizonTranscendenceRank
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    {d : ℕ} (hd : 0 < d) (source : Fin d → E)
    (m n N : ℕ) : ℕ :=
  ((AlgebraicIndependent.matroid F E).eRk
    (Set.range
      (finiteProjectiveDifferentialHorizonObservation hd source m n N))).toNat

/-- Exact Page-capacity rank for a differential-generic projective source. -/
theorem finiteProjectiveDifferentialHorizonTranscendenceRank_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra ℚ F] [Differential E]
    {d : ℕ} (hd : 0 < d) (source : Fin d → E)
    (hsource : DifferentialIndependent F source)
    {m n N : ℕ} (hm0 : 0 < m) (hm : m ≤ N + 1) (hn : n ≤ N + 1) :
    finiteProjectiveDifferentialHorizonTranscendenceRank
        (F := F) hd source m n N =
      projectiveFiniteHorizonObservationRank d m n N := by
  let c₀ := projectiveLongitudinalChannel hd
  have h₀ : source c₀ ≠ 0 := by
    intro hzero
    apply (hsource.algebraicIndependent.transcendental c₀)
    simpa [hzero] using (isAlgebraic_zero : IsAlgebraic F (0 : E))
  have hjets : AlgebraicIndependent F
      (fun p : Fin d × ℕ => differentialJet p.2 (source p.1)) := by
    exact hsource
  have hrank := projectiveHorizonObservationTranscendenceRank_eq
    (F := F) hd
    (fun p : Fin d × ℕ => differentialJet p.2 (source p.1))
    hjets hm hn
  unfold projectiveHorizonObservationTranscendenceRank at hrank
  unfold finiteProjectiveDifferentialHorizonTranscendenceRank
  rw [projectiveHorizonObservation_differentialJet_eq
    (F := F) hd source h₀ hm0] at hrank
  exact hrank

end

end GaloisForLFunctions.HTGeometry
