import GaloisForLFunctions.RHTower.MobiusDivisorUniformSuccessorTransport
import GaloisForLFunctions.RHTower.MobiusDivisorFirstPrimeReserve

/-!
# The positive normalization cost of the actual Möbius divisor source

Write `U = ∑ |C_d|` for absolute source mass and `Q = ∑ C_d²` for
the unprocessed diagonal energy. The actual source satisfies
`c M Q ≤ U² ≤ M Q` for all sufficiently large `M`, with a fixed `c > 0`.

Every nonnegative probability weighting that gives positive weight to
nonzero source coefficients has weighted energy at least `U²`. The
weights `|C_d| / U` attain this minimum. Strictly positive probability
weights can attain energy at most `2 U²`.

Thus probability normalization has an initial cost of order `M`
relative to the original diagonal, even after optimizing the weights.
Monotonicity of a subsequent conditional energy alone does not remove
this cost. No terminal signed-source bound or RH conclusion is asserted.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- Absolute mass of the literal Möbius divisor dilation coefficients. -/
def mobiusDivisorAbsoluteMass (M : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, |mobiusDivisorDilationChannel M d|

private lemma channel_bound (M d : ℕ) :
    |mobiusDivisorDilationChannel M d| ≤ (3/5:ℝ)*Real.sqrt M := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,abs_mul,
    abs_of_nonneg (divisorUnsignedDilationChannel_nonneg M d)]
  have hm : |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
  calc
    _ ≤ 1*divisorUnsignedDilationChannel M d :=
      mul_le_mul_of_nonneg_right hm (divisorUnsignedDilationChannel_nonneg M d)
    _ ≤ _ := by simpa using divisorUnsignedDilationChannel_le_three_fifths_sqrt M d

private lemma mass_nonneg (M : ℕ) : 0 ≤ mobiusDivisorAbsoluteMass M :=
  sum_nonneg (fun _ _ => abs_nonneg _)

private lemma energy_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorSelectionEnergy M P := by
  change 0 ≤ ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    (mobiusDivisorSelectionFibre M P R)^(2 : ℕ)
  exact sum_nonneg (fun _ _ => sq_nonneg _)

/-- The uniform channel ceiling gives the upper absolute mass scale. -/
theorem mobiusDivisorAbsoluteMass_le (M : ℕ) :
    mobiusDivisorAbsoluteMass M ≤ (3/5:ℝ)*(M:ℝ)*Real.sqrt M := by
  calc
    _ ≤ ∑ _d ∈ Icc 1 M,(3/5:ℝ)*Real.sqrt M := sum_le_sum (fun d _ => channel_bound M d)
    _ = _ := by simp; ring

/-- Every diagonal term is bounded by its absolute amplitude times `sqrt M`. -/
theorem mobiusDivisorDiagonal_le_sqrt_mul_absoluteMass (M : ℕ) :
    mobiusDivisorSelectionEnergy M ∅ ≤ Real.sqrt M*mobiusDivisorAbsoluteMass M := by
  rw [mobiusDivisorSelectionEnergy_empty,mobiusDivisorAbsoluteMass,mul_sum]
  apply sum_le_sum
  intro d hd
  have hb : |mobiusDivisorDilationChannel M d| ≤ Real.sqrt M :=
    (channel_bound M d).trans (by nlinarith [Real.sqrt_nonneg (M:ℝ)])
  have hh := mul_le_mul_of_nonneg_right hb (abs_nonneg (mobiusDivisorDilationChannel M d))
  simpa only [← pow_two,sq_abs] using hh

/-- The actual first-prime reserve forces a positive quadratic diagonal. -/
theorem exists_mobiusDivisorDiagonal_quadratic_lower :
    ∃ c : ℝ,0<c ∧ ∃ N : ℕ,1≤N ∧ ∀ M : ℕ,N≤M →
      c*(M:ℝ)^(2 : ℕ) ≤ mobiusDivisorSelectionEnergy M ∅ := by
  obtain ⟨c,hc,T,hT,hreserve⟩ := exists_mobiusDivisorSelectionEnergy_first_prime_reserve
  refine ⟨c/2,by positivity,2*T,by omega,?_⟩
  intro M hM
  have h := hreserve M 2 Nat.prime_two (by omega)
  have hn := energy_nonneg M {2}
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h,hn]

/-- Actual source mass has a positive lower bound at scale `M sqrt M`. -/
theorem exists_mobiusDivisorAbsoluteMass_lower :
    ∃ c : ℝ,0<c ∧ ∃ N : ℕ,1≤N ∧ ∀ M : ℕ,N≤M →
      c*(M:ℝ)*Real.sqrt M ≤ mobiusDivisorAbsoluteMass M := by
  obtain ⟨c,hc,N,hN,hbound⟩ := exists_mobiusDivisorDiagonal_quadratic_lower
  refine ⟨c,hc,N,hN,?_⟩
  intro M hM
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have h := (hbound M hM).trans (mobiusDivisorDiagonal_le_sqrt_mul_absoluteMass M)
  have hs := Real.sq_sqrt hm.le
  have he : c*(M:ℝ)^(2 : ℕ) = Real.sqrt M*(c*(M:ℝ)*Real.sqrt M) := by
    calc
      _ = c*(M:ℝ)*(Real.sqrt M)^(2 : ℕ) := by rw [hs]; ring
      _ = _ := by ring
  rw [he] at h
  exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hm)).mp h

/-- Finite Cauchy bounds the effective source size above by `M`. -/
theorem mobiusDivisorAbsoluteMass_sq_le_card_diagonal (M : ℕ) :
    (mobiusDivisorAbsoluteMass M)^(2 : ℕ) ≤ (M:ℝ)*mobiusDivisorSelectionEnergy M ∅ := by
  have hh := sum_mul_sq_le_sq_mul_sq (Icc 1 M)
    (fun d => |mobiusDivisorDilationChannel M d|) (fun _ => (1:ℝ))
  simpa [mobiusDivisorAbsoluteMass,mobiusDivisorSelectionEnergy_empty,sq_abs,mul_comm] using hh

/-- The effective size of the actual source is at least a fixed multiple of `M`. -/
theorem exists_mobiusDivisorAbsoluteMass_sq_lower_diagonal :
    ∃ c : ℝ,0<c ∧ ∃ N : ℕ,1≤N ∧ ∀ M : ℕ,N≤M →
      c*(M:ℝ)*mobiusDivisorSelectionEnergy M ∅ ≤ (mobiusDivisorAbsoluteMass M)^(2 : ℕ) := by
  obtain ⟨c,hc,N,hN,hbound⟩ := exists_mobiusDivisorDiagonal_quadratic_lower
  refine ⟨c,hc,N,hN,?_⟩
  intro M hM
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hQ := energy_nonneg M ∅
  have hU := mass_nonneg M
  have he := mobiusDivisorDiagonal_le_sqrt_mul_absoluteMass M
  have he2 := mul_le_mul he he hQ (by positivity)
  have hs := Real.sq_sqrt hm.le
  have he2' : (mobiusDivisorSelectionEnergy M ∅)^(2 : ℕ) ≤ (M:ℝ)*(mobiusDivisorAbsoluteMass M)^(2 : ℕ) := by
    nlinarith only [he2,hs]
  have hl := mul_le_mul_of_nonneg_right (hbound M hM) hQ
  have hfinal : (M:ℝ)*(c*(M:ℝ)*mobiusDivisorSelectionEnergy M ∅) ≤
      (M:ℝ)*(mobiusDivisorAbsoluteMass M)^(2 : ℕ) := by nlinarith only [hl,he2']
  exact (mul_le_mul_iff_right₀ hm).mp hfinal

/-- Probability normalization cannot reduce weighted energy below absolute mass squared. -/
theorem mobiusDivisorAbsoluteMass_sq_le_weightedEnergy
    (M : ℕ) (w : ℕ→ℝ) (hw : ∀d∈Icc 1 M,0≤w d)
    (hsum : ∑d∈Icc 1 M,w d=1)
    (hsupport : ∀d∈Icc 1 M,w d=0 → mobiusDivisorDilationChannel M d=0) :
    (mobiusDivisorAbsoluteMass M)^(2 : ℕ) ≤
      ∑d∈Icc 1 M,(mobiusDivisorDilationChannel M d)^(2 : ℕ)/w d := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 M)
    (r:=fun d => |mobiusDivisorDilationChannel M d|)
    (f:=fun d => (mobiusDivisorDilationChannel M d)^(2 : ℕ)/w d) (g:=w)
    (fun d hd => div_nonneg (sq_nonneg _) (hw d hd)) hw ?_
  · simpa only [hsum,mul_one,mobiusDivisorAbsoluteMass] using h
  · intro d hd
    by_cases hz : w d=0
    · simp [hz,hsupport d hd hz]
    · rw [div_mul_cancel₀ _ hz,sq_abs]

/-- Weight proportional to absolute amplitude attains the lower weighted energy bound. -/
theorem mobiusDivisorAbsoluteMass_optimal_weights (M : ℕ)
    (hU : 0 < mobiusDivisorAbsoluteMass M) :
    let w := fun d => |mobiusDivisorDilationChannel M d|/mobiusDivisorAbsoluteMass M
    (∀d∈Icc 1 M,0≤w d) ∧ (∑d∈Icc 1 M,w d=1) ∧
      (∀d∈Icc 1 M,w d=0 → mobiusDivisorDilationChannel M d=0) ∧
      (∑d∈Icc 1 M,(mobiusDivisorDilationChannel M d)^(2 : ℕ)/w d)=(mobiusDivisorAbsoluteMass M)^(2 : ℕ) := by
  dsimp only
  refine ⟨fun _ _ => div_nonneg (abs_nonneg _) hU.le,?_,?_,?_⟩
  · rw [← sum_div]
    exact div_self hU.ne'
  · intro d hd hz
    exact abs_eq_zero.mp ((div_eq_zero_iff).mp hz |>.resolve_right hU.ne')
  · have he (d : ℕ) : (mobiusDivisorDilationChannel M d)^(2 : ℕ)/
        (|mobiusDivisorDilationChannel M d|/mobiusDivisorAbsoluteMass M)=
        |mobiusDivisorDilationChannel M d| * mobiusDivisorAbsoluteMass M := by
      by_cases hz : mobiusDivisorDilationChannel M d=0
      · simp [hz]
      · have hn := abs_ne_zero.mpr hz
        rw [← sq_abs (mobiusDivisorDilationChannel M d)]
        field_simp
    simp_rw [he]
    rw [← sum_mul]
    change mobiusDivisorAbsoluteMass M*mobiusDivisorAbsoluteMass M=_
    ring

/-- Every compatible probability weighting incurs an order-`M` diagonal cost. -/
theorem exists_mobiusDivisor_positiveNormalization_cost :
    ∃ c : ℝ,0<c ∧ ∃ N : ℕ,1≤N ∧ ∀ M : ℕ,N≤M → ∀ w : ℕ→ℝ,
      (∀d∈Icc 1 M,0≤w d) → (∑d∈Icc 1 M,w d=1) →
      (∀d∈Icc 1 M,w d=0 → mobiusDivisorDilationChannel M d=0) →
      c*(M:ℝ)*mobiusDivisorSelectionEnergy M ∅ ≤
        ∑d∈Icc 1 M,(mobiusDivisorDilationChannel M d)^(2 : ℕ)/w d := by
  obtain ⟨c,hc,N,hN,hbound⟩ := exists_mobiusDivisorAbsoluteMass_sq_lower_diagonal
  exact ⟨c,hc,N,hN,fun M hM w hw hsum hs =>
    (hbound M hM).trans (mobiusDivisorAbsoluteMass_sq_le_weightedEnergy M w hw hsum hs)⟩

/-- Adding a uniform positive component gives strictly positive weights within factor two
of the optimal weighted energy. -/
theorem exists_mobiusDivisor_strictlyPositiveNormalization_upper (M : ℕ)
    (hM : 0<M) (hU : 0 < mobiusDivisorAbsoluteMass M) :
    ∃ w : ℕ→ℝ,(∀d∈Icc 1 M,0<w d) ∧ (∑d∈Icc 1 M,w d=1) ∧
      (∑d∈Icc 1 M,(mobiusDivisorDilationChannel M d)^(2 : ℕ)/w d) ≤
        2*(mobiusDivisorAbsoluteMass M)^(2 : ℕ) := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  let U := mobiusDivisorAbsoluteMass M
  let e := U/(M:ℝ)
  have he : 0<e := div_pos hU hm
  let w := fun d => (|mobiusDivisorDilationChannel M d|+e)/(2*U)
  have hden : 0<2*U := by dsimp [U]; positivity
  refine ⟨w,fun d _ => div_pos (by positivity) hden,?_,?_⟩
  · have hsum : (∑d∈Icc 1 M,(|mobiusDivisorDilationChannel M d|+e))=2*U := by
      rw [sum_add_distrib]
      change U+(∑_d∈Icc 1 M,e)=2*U
      simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
      dsimp [e]
      field_simp
      ring
    dsimp [w]
    rw [← sum_div,hsum,div_self hden.ne']
  · have hterm (d : ℕ) : (mobiusDivisorDilationChannel M d)^(2 : ℕ)/w d ≤
        2*U*|mobiusDivisorDilationChannel M d| := by
      have ha := abs_nonneg (mobiusDivisorDilationChannel M d)
      have ha' : 0 < |mobiusDivisorDilationChannel M d|+e := by positivity
      dsimp [w]
      rw [div_div_eq_mul_div]
      apply (div_le_iff₀ ha').mpr
      have hs := sq_abs (mobiusDivisorDilationChannel M d)
      have hn := mul_nonneg (mul_nonneg hden.le ha) he.le
      rw [← hs]
      nlinarith only [hn]
    calc
      _ ≤ ∑d∈Icc 1 M,2*U*|mobiusDivisorDilationChannel M d| := sum_le_sum (fun d _ => hterm d)
      _ = _ := by rw [← mul_sum]; change 2*U*U=2*U^(2 : ℕ); ring

end RHTower
