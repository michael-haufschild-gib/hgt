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

/-! ### The mixed `W`–`L` types -/

/-- `c = p²y + qk''`: `L(py)W'_p = [[p, 3], [3c, 9py + δ'']]`. -/
def wlC (y : O) : O := R.P.p ^ 2 * y + R.Q.p * R.pK

/-- `c = q²y + pk'`: `L(qy)W'_q = [[q, 3], [3c, 9qy + δ']]`. -/
def lwC (y : O) : O := R.Q.p ^ 2 * y + R.P.p * R.qK

theorem three_dvd_sq_mul_other_sub_one {a b : O} (ha : (3 : O) ∣ a - 1) (hb : (3 : O) ∣ b - 1) :
    (3 : O) ∣ a ^ 2 * b - 1 := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨t, ht⟩ := hb
  exact ⟨s * (a + 1) * b + t, by linear_combination (a + 1) * b * hs + ht⟩

theorem isCoprime_wl (y : O) (hy : ¬ R.Q.p ∣ y) : IsCoprime (R.P.p ^ 2 * R.Q.p) (9 * R.wlC y) := by
  have hP : IsCoprime R.P.p (R.wlC y) := ⟨R.pDelta + 9 * (R.P.p * y), -9, by unfold wlC; linear_combination R.p_det⟩
  have hQy : IsCoprime R.Q.p (R.P.p ^ 2 * y) :=
    (R.coprime.symm.pow_right).mul_right ((Irreducible.coprime_iff_not_dvd R.Q.prime.irreducible).mpr hy)
  obtain ⟨u, v, h⟩ := hQy
  have hQ : IsCoprime R.Q.p (R.wlC y) := ⟨u - v * R.pK, v, by unfold wlC; linear_combination h⟩
  have h9 : IsCoprime (R.P.p ^ 2 * R.Q.p) 9 :=
    (R.isCoprime_nine_p.pow_right.mul_right R.isCoprime_nine_q).symm
  exact h9.mul_right (hP.pow_left.mul_left hQ)

theorem isCoprime_lw (y : O) (hy : ¬ R.P.p ∣ y) : IsCoprime (R.Q.p ^ 2 * R.P.p) (9 * R.lwC y) := by
  have hQ : IsCoprime R.Q.p (R.lwC y) := ⟨R.qDelta + 9 * (R.Q.p * y), -9, by unfold lwC; linear_combination R.q_det⟩
  have hPy : IsCoprime R.P.p (R.Q.p ^ 2 * y) :=
    (R.coprime.pow_right).mul_right ((Irreducible.coprime_iff_not_dvd R.P.prime.irreducible).mpr hy)
  obtain ⟨u, v, h⟩ := hPy
  have hP : IsCoprime R.P.p (R.lwC y) := ⟨u - v * R.qK, v, by unfold lwC; linear_combination h⟩
  have h9 : IsCoprime (R.Q.p ^ 2 * R.P.p) 9 :=
    (R.isCoprime_nine_q.pow_right.mul_right R.isCoprime_nine_p).symm
  exact h9.mul_right (hQ.pow_left.mul_left hP)

theorem exists_wlBezout (y : O) (hy : ¬ R.Q.p ∣ y) :
    ∃ δ β : O, R.P.p ^ 2 * R.Q.p * δ - 9 * R.wlC y * β = 1 := by
  obtain ⟨u, v, h⟩ := R.isCoprime_wl y hy
  exact ⟨u, -v, by linear_combination h⟩

theorem exists_lwBezout (y : O) (hy : ¬ R.P.p ∣ y) :
    ∃ δ β : O, R.Q.p ^ 2 * R.P.p * δ - 9 * R.lwC y * β = 1 := by
  obtain ⟨u, v, h⟩ := R.isCoprime_lw y hy
  exact ⟨u, -v, by linear_combination h⟩

def wlDelta (y : O) : O := if hy : ¬ R.Q.p ∣ y then (R.exists_wlBezout y hy).choose else 0
def wlBeta (y : O) : O := if hy : ¬ R.Q.p ∣ y then (R.exists_wlBezout y hy).choose_spec.choose else 0
def lwDelta (y : O) : O := if hy : ¬ R.P.p ∣ y then (R.exists_lwBezout y hy).choose else 0
def lwBeta (y : O) : O := if hy : ¬ R.P.p ∣ y then (R.exists_lwBezout y hy).choose_spec.choose else 0

theorem wl_det (y : O) (hy : ¬ R.Q.p ∣ y) : R.P.p ^ 2 * R.Q.p * R.wlDelta y - 9 * R.wlC y * R.wlBeta y = 1 := by
  simp only [wlDelta, wlBeta, dif_pos hy]
  exact (R.exists_wlBezout y hy).choose_spec.choose_spec

theorem lw_det (y : O) (hy : ¬ R.P.p ∣ y) : R.Q.p ^ 2 * R.P.p * R.lwDelta y - 9 * R.lwC y * R.lwBeta y = 1 := by
  simp only [lwDelta, lwBeta, dif_pos hy]
  exact (R.exists_lwBezout y hy).choose_spec.choose_spec

/-- `[[p²q, 3β], [3c, δ]]`. -/
def wlMat (y : O) (hy : ¬ R.Q.p ∣ y) : levelThree :=
  ⟨⟨!![R.P.p ^ 2 * R.Q.p, 3 * R.wlBeta y; 3 * R.wlC y, R.wlDelta y], by
      rw [Matrix.det_fin_two_of]; linear_combination R.wl_det y hy⟩,
    levelThree_of_entries _ (by
      have h3 := three_dvd_sq_mul_other_sub_one R.P.three_dvd_sub_one R.Q.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using h3
      · simp
      · simp
      · simpa using three_dvd_delta_sub_one h3
          (show R.P.p ^ 2 * R.Q.p * R.wlDelta y - 9 * (R.wlC y * R.wlBeta y) = 1 by
            linear_combination R.wl_det y hy))⟩

/-- `[[q²p, 3β], [3c, δ]]`. -/
def lwMat (y : O) (hy : ¬ R.P.p ∣ y) : levelThree :=
  ⟨⟨!![R.Q.p ^ 2 * R.P.p, 3 * R.lwBeta y; 3 * R.lwC y, R.lwDelta y], by
      rw [Matrix.det_fin_two_of]; linear_combination R.lw_det y hy⟩,
    levelThree_of_entries _ (by
      have h3 := three_dvd_sq_mul_other_sub_one R.Q.three_dvd_sub_one R.P.three_dvd_sub_one
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using h3
      · simp
      · simp
      · simpa using three_dvd_delta_sub_one h3
          (show R.Q.p ^ 2 * R.P.p * R.lwDelta y - 9 * (R.lwC y * R.lwBeta y) = 1 by
            linear_combination R.lw_det y hy))⟩

/-- `t = mδ − β(9py + δ'')`. -/
def wlShift (y : O) : O := R.P.p * R.Q.p * R.wlDelta y - R.wlBeta y * (9 * R.P.p * y + R.pDelta)

/-- `t = mδ − β(9qy + δ')`. -/
def lwShift (y : O) : O := R.P.p * R.Q.p * R.lwDelta y - R.lwBeta y * (9 * R.Q.p * y + R.qDelta)

/-- **Hermite normal form.** If `[[m, 0], [0, 1]]A = B[[1, 3t], [0, m]]` entrywise, then
`A_mA = B·A_m⁻¹T_t`. -/
theorem dilation_of_hermite (A B : levelThree) (t : O)
    (h00 : R.P.p * R.Q.p * (A : SL(2, O)) 0 0 = (B : SL(2, O)) 0 0)
    (h01 : (A : SL(2, O)) 0 1 = 3 * t * (A : SL(2, O)) 0 0 + (B : SL(2, O)) 0 1)
    (h10 : (A : SL(2, O)) 1 0 = (B : SL(2, O)) 1 0)
    (h11 : (A : SL(2, O)) 1 1 = 3 * t * (B : SL(2, O)) 1 0 + R.P.p * R.Q.p * (B : SL(2, O)) 1 1) :
    R.dilation * complexMatrix A = complexMatrix B * R.contraction * complexMatrix (transThree t) := by
  have hp := R.P.root_sq
  have hq := R.Q.root_sq
  have hp0 := R.P.root_ne_zero
  have hq0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have e00 : ringComplex ((B : SL(2, O)) 0 0) = R.P.root ^ 2 * R.Q.root ^ 2 * ringComplex ((A : SL(2, O)) 0 0) := by
    rw [← h00, map_mul, map_mul, hp, hq]
  have e01 : ringComplex ((A : SL(2, O)) 0 1) =
      3 * ringComplex t * ringComplex ((A : SL(2, O)) 0 0) + ringComplex ((B : SL(2, O)) 0 1) := by
    rw [h01]; simp [map_add, map_mul, hc3]
  have e10 : ringComplex ((A : SL(2, O)) 1 0) = ringComplex ((B : SL(2, O)) 1 0) := by rw [h10]
  have e11 : ringComplex ((A : SL(2, O)) 1 1) = 3 * ringComplex t * ringComplex ((B : SL(2, O)) 1 0) +
      R.P.root ^ 2 * R.Q.root ^ 2 * ringComplex ((B : SL(2, O)) 1 1) := by
    rw [h11]; simp [map_add, map_mul, hc3, hp, hq]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [dilation, contraction, PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal,
      complexMatrix_apply, transThree, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      e00, e01, e10, e11, hc3]
  all_goals field_simp

theorem dilation_wl (y : O) (hy : ¬ R.Q.p ∣ y) :
    R.dilation * complexMatrix (lowerThree (R.P.p * y) * R.wP) =
      complexMatrix (R.wlMat y hy) * R.contraction * complexMatrix (transThree (R.wlShift y)) := by
  have hd := R.wl_det y hy
  unfold wlC at hd
  have he := R.p_det
  apply R.dilation_of_hermite
  · simp [wlMat, wP, lowerThree, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [wlMat, wP, lowerThree, wlShift, wlC, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-3) * hd + 3 * R.wlBeta y * he
  · simp [wlMat, wP, lowerThree, wlC, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [wlMat, wP, lowerThree, wlShift, wlC, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(9 * R.P.p * y + R.pDelta)) * hd + (R.P.p * R.Q.p * R.wlDelta y) * he

theorem contraction_wl (y : O) :
    R.contraction * complexMatrix (lowerThree (R.P.p * y) * R.wP) =
      complexMatrix (lowerThree (R.Q.p * R.wlC y)) * R.Q.contraction * complexMatrix (transThree 1) *
        R.P.dilation := by
  have hp := R.P.root_sq
  have hq := R.Q.root_sq
  have hp0 := R.P.root_ne_zero
  have hq0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have he := congrArg ringComplex R.p_det
  simp only [map_sub, map_mul, map_one, map_ofNat] at he
  rw [← hp, ← hq] at he
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [contraction, PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal,
      complexMatrix_apply, wlC, transThree, lowerThree, wP, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try simp only [← hp, ← hq])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination he)

theorem dilation_lw (y : O) (hy : ¬ R.P.p ∣ y) :
    R.dilation * complexMatrix (lowerThree (R.Q.p * y) * R.wQ) =
      complexMatrix (R.lwMat y hy) * R.contraction * complexMatrix (transThree (R.lwShift y)) := by
  have hd := R.lw_det y hy
  unfold lwC at hd
  have he := R.q_det
  apply R.dilation_of_hermite
  · simp [lwMat, wQ, lowerThree, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [lwMat, wQ, lowerThree, lwShift, lwC, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-3) * hd + 3 * R.lwBeta y * he
  · simp [lwMat, wQ, lowerThree, lwC, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [lwMat, wQ, lowerThree, lwShift, lwC, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(9 * R.Q.p * y + R.qDelta)) * hd + (R.P.p * R.Q.p * R.lwDelta y) * he

theorem contraction_lw (y : O) :
    R.contraction * complexMatrix (lowerThree (R.Q.p * y) * R.wQ) =
      complexMatrix (lowerThree (R.P.p * R.lwC y)) * R.P.contraction * complexMatrix (transThree 1) *
        R.Q.dilation := by
  have hp := R.P.root_sq
  have hq := R.Q.root_sq
  have hp0 := R.P.root_ne_zero
  have hq0 := R.Q.root_ne_zero
  have hc3 := PrimaryPrime.ringComplex_three
  have he := congrArg ringComplex R.q_det
  simp only [map_sub, map_mul, map_one, map_ofNat] at he
  rw [← hp, ← hq] at he
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [contraction, PrimaryPrime.contraction, PrimaryPrime.dilation, complexDiagonal,
      complexMatrix_apply, lwC, transThree, lowerThree, wQ, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (try simp only [hc3] at *)
  all_goals (try simp only [← hp, ← hq])
  all_goals (try field_simp)
  all_goals (first | ring1 | linear_combination he)

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
