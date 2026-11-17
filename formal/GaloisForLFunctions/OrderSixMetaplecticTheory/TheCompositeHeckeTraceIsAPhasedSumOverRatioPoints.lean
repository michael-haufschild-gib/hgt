import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsASumOverPairsOfCosets

/-!
# The Hecke points of the composite trace

For `m = pq` the Hecke points of a coset of `Γ_m` are of four kinds (`hh`, `ll`, `hl`, `lh`):

* `A_mw` (`z ↦ mz`) and `A_m⁻¹T_tw` (`z ↦ (z + 3t)/m`), as at a prime with `p ↦ m`;
* the ratio points `A_q⁻¹T_tA_pw` (`z ↦ (pz + 3t)/q`, height `|p/q|v`) and `A_p⁻¹T_tA_qw`.

The factorizations behind them: the prime identities at `p` and at `q`, the commutation of the diagonal
matrices, `A_pL(py) = L(y)A_p`, and conjugation `A_p[[a, b], [pc, d]]A_p⁻¹ = [[a, pb], [c, d]]`; for the composite
`W_m` and `L(y)` (`y` prime to `m`) the prime Bezout factorizations with `p` replaced by `m`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- `A_pL(py) = L(y)A_p`. -/
theorem dilation_lowerThree_mul (y : O) :
    P.dilation * complexMatrix (lowerThree (P.p * y)) = complexMatrix (lowerThree y) * P.dilation := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, lowerThree,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hr]
  field_simp

/-- `A_p⁻¹T_{pt} = T_tA_p⁻¹`. -/
theorem contraction_transThree_mul (t : O) :
    P.contraction * complexMatrix (transThree (P.p * t)) = complexMatrix (transThree t) * P.contraction := by
  have hP := P.ringComplex_ne_zero
  have hr := P.root_sq
  have hr0 := P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, complexDiagonal, complexMatrix_apply, transThree,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hr]
  field_simp

end PrimaryPrime

theorem lowerThree_zero : lowerThree 0 = 1 := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerThree]

namespace PrimaryPair

variable (R : PrimaryPair)

/-! ### Diagonal matrices commute -/

theorem dil_dil : R.P.dilation * R.Q.dilation = R.Q.dilation * R.P.dilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm]

theorem con_con : R.P.contraction * R.Q.contraction = R.Q.contraction * R.P.contraction := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, complexDiagonal, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm]

theorem dilP_conQ : R.P.dilation * R.Q.contraction = R.Q.contraction * R.P.dilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, PrimaryPrime.contraction, complexDiagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dilQ_conP : R.Q.dilation * R.P.contraction = R.P.contraction * R.Q.dilation := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, PrimaryPrime.contraction, complexDiagonal, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-! ### The pure types: the prime factorizations with `p ↦ m` -/

theorem dilation_transThree (t : O) :
    R.dilation * complexMatrix (transThree t) =
      complexMatrix (transThree (R.P.p * (R.Q.p * t))) * R.dilation := by
  rw [dilation, mul_assoc, R.Q.dilation_transThree, ← mul_assoc, R.P.dilation_transThree, mul_assoc]

theorem contraction_lowerThree (y : O) :
    R.contraction * complexMatrix (lowerThree y) =
      complexMatrix (lowerThree (R.P.p * (R.Q.p * y))) * R.contraction := by
  rw [contraction, mul_assoc, R.Q.contraction_lowerThree, ← mul_assoc, R.P.contraction_lowerThree, mul_assoc]

theorem exists_mLowBezout (y : O) (hy : IsCoprime (R.P.p * R.Q.p) y) :
    ∃ δ β : O, R.P.p * R.Q.p * δ - 9 * y * β = 1 := by
  have h9 : IsCoprime (R.P.p * R.Q.p) 9 := (R.isCoprime_nine_p.mul_right R.isCoprime_nine_q).symm
  obtain ⟨u, v, h⟩ := h9.mul_right hy
  exact ⟨u, -v, by linear_combination h⟩

/-- `δ_y` in `mδ_y − 9yβ_y = 1`. -/
def mLowDelta (y : O) : O := if hy : IsCoprime (R.P.p * R.Q.p) y then (R.exists_mLowBezout y hy).choose else 0

/-- `β_y` in `mδ_y − 9yβ_y = 1`. -/
def mLowBeta (y : O) : O :=
  if hy : IsCoprime (R.P.p * R.Q.p) y then (R.exists_mLowBezout y hy).choose_spec.choose else 0

theorem m_low_det (y : O) (hy : IsCoprime (R.P.p * R.Q.p) y) :
    R.P.p * R.Q.p * R.mLowDelta y - 9 * y * R.mLowBeta y = 1 := by
  simp only [mLowDelta, mLowBeta, dif_pos hy]
  exact (R.exists_mLowBezout y hy).choose_spec.choose_spec

/-- `M_y = [[m, 3β_y], [3y, δ_y]]`. -/
def mLowMat (y : O) (hy : IsCoprime (R.P.p * R.Q.p) y) : levelThree :=
  ⟨⟨!![R.P.p * R.Q.p, 3 * R.mLowBeta y; 3 * y, R.mLowDelta y], by
      rw [Matrix.det_fin_two_of]; linear_combination R.m_low_det y hy⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using R.three_dvd_m_sub_one
      · simp
      · simp
      · simpa using three_dvd_delta_sub_one R.three_dvd_m_sub_one
          (show R.P.p * R.Q.p * R.mLowDelta y - 9 * (y * R.mLowBeta y) = 1 by
            linear_combination R.m_low_det y hy))⟩

theorem dilation_lowerThree (y : O) (hy : IsCoprime (R.P.p * R.Q.p) y) :
    R.dilation * complexMatrix (lowerThree y) =
      complexMatrix (R.mLowMat y hy) * R.contraction * complexMatrix (transThree (-R.mLowBeta y)) := by
  have hp := R.P.root_sq
  have hq := R.Q.root_sq
  have hp0 := R.P.root_ne_zero
  have hq0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have hd := congrArg ringComplex (R.m_low_det y hy)
  simp only [map_sub, map_mul, map_one, map_ofNat] at hd
  rw [← hp, ← hq] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dilation, contraction, PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal,
      complexMatrix_apply, mLowMat, transThree, lowerThree, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hp, ← hq])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd | linear_combination -hd)

theorem contraction_wM :
    R.contraction * complexMatrix R.wM =
      complexMatrix (lowerThree R.mK) * complexMatrix (transThree 1) * R.dilation := by
  have hp := R.P.root_sq
  have hq := R.Q.root_sq
  have hp0 := R.P.root_ne_zero
  have hq0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have hd := congrArg ringComplex R.m_det
  simp only [map_sub, map_mul, map_one, map_ofNat] at hd
  rw [← hp, ← hq] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dilation, contraction, PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal,
      complexMatrix_apply, wM, transThree, lowerThree, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hp, ← hq])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd)

theorem exists_mHighBezout : ∃ n M : O, (R.P.p * R.Q.p) ^ 2 * n - 9 * R.mK * M = 1 := by
  have hk : IsCoprime (R.P.p * R.Q.p) R.mK := ⟨R.mDelta, -9, by linear_combination R.m_det⟩
  have h9 : IsCoprime (R.P.p * R.Q.p) 9 := (R.isCoprime_nine_p.mul_right R.isCoprime_nine_q).symm
  obtain ⟨u, v, h⟩ := (h9.mul_right hk).pow_left (m := 2)
  exact ⟨u, -v, by linear_combination h⟩

/-- `n` in `m²n − 9kM = 1`. -/
def mHighN : O := R.exists_mHighBezout.choose
/-- `M` in `m²n − 9kM = 1`. -/
def mHighM : O := R.exists_mHighBezout.choose_spec.choose
theorem mHigh_det : (R.P.p * R.Q.p) ^ 2 * R.mHighN - 9 * R.mK * R.mHighM = 1 :=
  R.exists_mHighBezout.choose_spec.choose_spec

/-- `M_W = [[m², 3M], [3k, n]]`. -/
def mHighMat : levelThree :=
  ⟨⟨!![(R.P.p * R.Q.p) ^ 2, 3 * R.mHighM; 3 * R.mK, R.mHighN], by
      rw [Matrix.det_fin_two_of]; linear_combination R.mHigh_det⟩,
    levelThree_of_entries _ (by
      obtain ⟨t, ht⟩ := R.three_dvd_m_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨t * (R.P.p * R.Q.p + 1), by simp; linear_combination (R.P.p * R.Q.p + 1) * ht⟩
      · simp
      · simp
      · exact ⟨3 * R.mK * R.mHighM - R.mHighN * t * (R.P.p * R.Q.p + 1), by
          simp; linear_combination R.mHigh_det - R.mHighN * (R.P.p * R.Q.p + 1) * ht⟩)⟩

/-- The shift `f = mn − Mδ` of the `W_m`-type Hecke points. -/
def mShift : O := R.P.p * R.Q.p * R.mHighN - R.mHighM * R.mDelta

theorem dilation_wM :
    R.dilation * complexMatrix R.wM = complexMatrix R.mHighMat * R.contraction * complexMatrix (transThree R.mShift) := by
  have hp := R.P.root_sq
  have hq := R.Q.root_sq
  have hp0 := R.P.root_ne_zero
  have hq0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have hd := congrArg ringComplex R.m_det
  have hh := congrArg ringComplex R.mHigh_det
  simp only [map_sub, map_mul, map_one, map_ofNat, map_pow] at hd hh
  rw [← hp, ← hq] at hd hh
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dilation, contraction, PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal,
      complexMatrix_apply, mHighMat, transThree, wM, mShift, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hp, ← hq])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd | linear_combination -hd |
    linear_combination (-1) * hh + ringComplex R.mHighM * hd |
    linear_combination (-ringComplex R.mDelta) * hh +
      (R.P.root ^ 2 * R.Q.root ^ 2 * ringComplex R.mHighN) * hd)

/-! ### The ratio types: `U` at one prime, `W` at the other -/

theorem contraction_wQ :
    R.Q.contraction * complexMatrix R.wQ =
      complexMatrix (lowerThree (R.P.p * R.qK)) * complexMatrix (transThree 1) * R.Q.dilation := by
  have hr := R.Q.root_sq
  have hr0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have hd := congrArg ringComplex R.q_det
  simp only [map_sub, map_mul, map_one, map_ofNat] at hd
  rw [← hr] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, lowerThree,
      transThree, wQ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd)

theorem contraction_wP :
    R.P.contraction * complexMatrix R.wP =
      complexMatrix (lowerThree (R.Q.p * R.pK)) * complexMatrix (transThree 1) * R.P.dilation := by
  have hr := R.P.root_sq
  have hr0 := R.P.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have hd := congrArg ringComplex R.p_det
  simp only [map_sub, map_mul, map_one, map_ofNat] at hd
  rw [← hr] at hd
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, lowerThree,
      transThree, wP, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd)

theorem exists_qHighBezout : ∃ n M : O, R.Q.p ^ 2 * n - 9 * (R.P.p * R.qK) * M = 1 := by
  have hk : IsCoprime R.Q.p (R.P.p * R.qK) := ⟨R.qDelta, -9, by linear_combination R.q_det⟩
  obtain ⟨u, v, h⟩ := (R.isCoprime_nine_q.symm.mul_right hk).pow_left (m := 2)
  exact ⟨u, -v, by linear_combination h⟩

theorem exists_pHighBezout : ∃ n M : O, R.P.p ^ 2 * n - 9 * (R.Q.p * R.pK) * M = 1 := by
  have hk : IsCoprime R.P.p (R.Q.p * R.pK) := ⟨R.pDelta, -9, by linear_combination R.p_det⟩
  obtain ⟨u, v, h⟩ := (R.isCoprime_nine_p.symm.mul_right hk).pow_left (m := 2)
  exact ⟨u, -v, by linear_combination h⟩

def qHighN : O := R.exists_qHighBezout.choose
def qHighM : O := R.exists_qHighBezout.choose_spec.choose
theorem qHigh_det : R.Q.p ^ 2 * R.qHighN - 9 * (R.P.p * R.qK) * R.qHighM = 1 :=
  R.exists_qHighBezout.choose_spec.choose_spec

def pHighN : O := R.exists_pHighBezout.choose
def pHighM : O := R.exists_pHighBezout.choose_spec.choose
theorem pHigh_det : R.P.p ^ 2 * R.pHighN - 9 * (R.Q.p * R.pK) * R.pHighM = 1 :=
  R.exists_pHighBezout.choose_spec.choose_spec

theorem three_dvd_sq_mul_sub_one {n : O} (hn : (3 : O) ∣ n - 1) {a b : O} (h : n ^ 2 * a - 9 * b = 1) :
    (3 : O) ∣ a - 1 := by
  obtain ⟨t, ht⟩ := hn
  exact ⟨3 * b - a * t * (n + 1), by linear_combination h - a * (n + 1) * ht⟩

/-- `[[q², 3M], [3pk', n]]`. -/
def qHighMat : levelThree :=
  ⟨⟨!![R.Q.p ^ 2, 3 * R.qHighM; 3 * (R.P.p * R.qK), R.qHighN], by
      rw [Matrix.det_fin_two_of]; linear_combination R.qHigh_det⟩,
    levelThree_of_entries _ (by
      obtain ⟨t, ht⟩ := R.Q.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨t * (R.Q.p + 1), by simp; linear_combination (R.Q.p + 1) * ht⟩
      · simp
      · simp
      · simpa using three_dvd_sq_mul_sub_one R.Q.three_dvd_sub_one
          (show R.Q.p ^ 2 * R.qHighN - 9 * (R.P.p * R.qK * R.qHighM) = 1 by linear_combination R.qHigh_det))⟩

/-- `A_p[[q², 3M], [3pk', n]]A_p⁻¹ = [[q², 3pM], [3k', n]]`. -/
def qHighUp : levelThree :=
  ⟨⟨!![R.Q.p ^ 2, 3 * (R.P.p * R.qHighM); 3 * R.qK, R.qHighN], by
      rw [Matrix.det_fin_two_of]; linear_combination R.qHigh_det⟩,
    levelThree_of_entries _ (by
      obtain ⟨t, ht⟩ := R.Q.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨t * (R.Q.p + 1), by simp; linear_combination (R.Q.p + 1) * ht⟩
      · simp
      · simp
      · simpa using three_dvd_sq_mul_sub_one R.Q.three_dvd_sub_one
          (show R.Q.p ^ 2 * R.qHighN - 9 * (R.P.p * R.qK * R.qHighM) = 1 by linear_combination R.qHigh_det))⟩

/-- `[[p², 3M], [3qk'', n]]`. -/
def pHighMat : levelThree :=
  ⟨⟨!![R.P.p ^ 2, 3 * R.pHighM; 3 * (R.Q.p * R.pK), R.pHighN], by
      rw [Matrix.det_fin_two_of]; linear_combination R.pHigh_det⟩,
    levelThree_of_entries _ (by
      obtain ⟨t, ht⟩ := R.P.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨t * (R.P.p + 1), by simp; linear_combination (R.P.p + 1) * ht⟩
      · simp
      · simp
      · simpa using three_dvd_sq_mul_sub_one R.P.three_dvd_sub_one
          (show R.P.p ^ 2 * R.pHighN - 9 * (R.Q.p * R.pK * R.pHighM) = 1 by linear_combination R.pHigh_det))⟩

/-- `A_q[[p², 3M], [3qk'', n]]A_q⁻¹ = [[p², 3qM], [3k'', n]]`. -/
def pHighUp : levelThree :=
  ⟨⟨!![R.P.p ^ 2, 3 * (R.Q.p * R.pHighM); 3 * R.pK, R.pHighN], by
      rw [Matrix.det_fin_two_of]; linear_combination R.pHigh_det⟩,
    levelThree_of_entries _ (by
      obtain ⟨t, ht⟩ := R.P.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · exact ⟨t * (R.P.p + 1), by simp; linear_combination (R.P.p + 1) * ht⟩
      · simp
      · simp
      · simpa using three_dvd_sq_mul_sub_one R.P.three_dvd_sub_one
          (show R.P.p ^ 2 * R.pHighN - 9 * (R.Q.p * R.pK * R.pHighM) = 1 by linear_combination R.pHigh_det))⟩

/-- The shift `f' = qn − Mδ'`. -/
def qShift : O := R.Q.p * R.qHighN - R.qHighM * R.qDelta

/-- The shift `f'' = pn − Mδ''`. -/
def pShift : O := R.P.p * R.pHighN - R.pHighM * R.pDelta

theorem dilation_wQ :
    R.Q.dilation * complexMatrix R.wQ =
      complexMatrix R.qHighMat * R.Q.contraction * complexMatrix (transThree R.qShift) := by
  have hr := R.Q.root_sq
  have hr0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have hd := congrArg ringComplex R.q_det
  have hh := congrArg ringComplex R.qHigh_det
  simp only [map_sub, map_mul, map_one, map_ofNat, map_pow] at hd hh
  rw [← hr] at hd hh
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, qHighMat,
      transThree, wQ, qShift, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd | linear_combination -hd |
    linear_combination (-1) * hh + ringComplex R.qHighM * hd |
    linear_combination (-ringComplex R.qDelta) * hh + (R.Q.root ^ 2 * ringComplex R.qHighN) * hd)

theorem dilation_wP :
    R.P.dilation * complexMatrix R.wP =
      complexMatrix R.pHighMat * R.P.contraction * complexMatrix (transThree R.pShift) := by
  have hr := R.P.root_sq
  have hr0 := R.P.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have hd := congrArg ringComplex R.p_det
  have hh := congrArg ringComplex R.pHigh_det
  simp only [map_sub, map_mul, map_one, map_ofNat, map_pow] at hd hh
  rw [← hr] at hd hh
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, pHighMat,
      transThree, wP, pShift, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination hd | linear_combination -hd |
    linear_combination (-1) * hh + ringComplex R.pHighM * hd |
    linear_combination (-ringComplex R.pDelta) * hh + (R.P.root ^ 2 * ringComplex R.pHighN) * hd)

theorem dilP_qHighMat : R.P.dilation * complexMatrix R.qHighMat = complexMatrix R.qHighUp * R.P.dilation := by
  have hr := R.P.root_sq
  have hr0 := R.P.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, qHighMat, qHighUp,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (try ring1)

theorem dilQ_pHighMat : R.Q.dilation * complexMatrix R.pHighMat = complexMatrix R.pHighUp * R.Q.dilation := by
  have hr := R.Q.root_sq
  have hr0 := R.Q.root_ne_zero
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [PrimaryPrime.dilation, complexDiagonal, complexMatrix_apply, pHighMat, pHighUp,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try rw [← hr])
  all_goals (try field_simp)
  all_goals (try ring1)

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
