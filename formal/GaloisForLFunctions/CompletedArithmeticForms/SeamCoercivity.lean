import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailSeamGram
import GaloisForLFunctions.CompletedArithmeticForms.NativeGaussianHorizon

/-!
# Strictness and local reserves of the complete theta seam

Polynomial moments recover every coefficient of a finite theta derivative
packet. The exact seam Gram therefore has zero radical at every rank. The
native decay constants control its perturbation under displacement of the
tail endpoint in the full seam norm.
-/

noncomputable section

open MeasureTheory Finset Matrix Set

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower

/-- Polynomial moments recover every coefficient of a vanishing finite
derivative packet of the literal complete theta source. -/
theorem thetaDerivativePacket_coefficients_eq_zero {N : ℕ} (v : Fin N → ℝ)
    (hzero : ∀ x : ℝ, ∑ j : Fin N, v j * iteratedDeriv j.val thetaCuspFullSource x = 0) :
    v = 0 := by
  have hmom (k : ℕ) :
      (∑ j : Fin N, v j * ∫ x : ℝ, x ^ k * iteratedDeriv j.val thetaCuspFullSource x) = 0 := by
    calc
      _ = ∫ x : ℝ, ∑ j : Fin N, v j * (x ^ k * iteratedDeriv j.val thetaCuspFullSource x) := by
        rw [integral_finsetSum _ fun j _ =>
          (integrable_pow_mul_iteratedDeriv_thetaCuspFullSource j.val k).const_mul (v j)]
        simp only [integral_const_mul]
      _ = ∫ x : ℝ, x ^ k * (∑ j : Fin N, v j * iteratedDeriv j.val thetaCuspFullSource x) := by
        congr 1
        funext x
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j _
        ring
      _ = 0 := by simp only [hzero, mul_zero, integral_zero]
  have hv : ∀ k : ℕ, ∀ hk : k < N, v ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      let i : Fin N := ⟨k, hk⟩
      have hsingle :
          (∑ j : Fin N, v j * ∫ x : ℝ, x ^ k * iteratedDeriv j.val thetaCuspFullSource x) =
            v i * ∫ x : ℝ, x ^ k * iteratedDeriv k thetaCuspFullSource x := by
        apply sum_eq_single i
        · intro j _ hji
          rcases lt_trichotomy j.val k with hj | hj | hj
          · have hz : v j = 0 := ih j.val hj j.isLt
            rw [hz, zero_mul]
          · exact (hji (Fin.ext hj)).elim
          · rw [integral_pow_mul_iteratedDeriv_thetaCuspFullSource_eq_zero hj, mul_zero]
        · simp
      have hz := hmom k
      rw [hsingle, integral_pow_mul_iteratedDeriv_thetaCuspFullSource,
        Nat.descFactorial_self, Nat.sub_self] at hz
      simp only [pow_zero, one_mul] at hz
      have hmass : (∫ x : ℝ, thetaCuspFullSource x) ≠ 0 := integral_thetaCuspFullSource_pos.ne'
      have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero k)
      exact (mul_eq_zero.mp hz).resolve_right
        (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) hf) hmass)
  funext i
  exact hv i.val i.isLt

/-- A finite complex theta derivative packet. -/
def thetaSeamPacket {N : ℕ} (c : Fin N → ℂ) (x : ℝ) : ℂ :=
  ∑ j : Fin N, c j * ((iteratedDeriv j.val thetaCuspFullSource x : ℝ) : ℂ)

theorem thetaSeamPacket_eq_zero_iff {N : ℕ} (c : Fin N → ℂ) :
    (∀ x : ℝ, thetaSeamPacket c x = 0) ↔ c = 0 := by
  constructor
  · intro h
    have hre : (fun j => (c j).re) = 0 :=
      thetaDerivativePacket_coefficients_eq_zero _ (by
        intro x
        have hh := congrArg Complex.re (h x)
        simpa only [thetaSeamPacket, Complex.re_sum, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] using hh)
    have him : (fun j => (c j).im) = 0 :=
      thetaDerivativePacket_coefficients_eq_zero _ (by
        intro x
        have hh := congrArg Complex.im (h x)
        simpa only [thetaSeamPacket, Complex.im_sum, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Complex.zero_im] using hh)
    funext j
    exact Complex.ext (congrFun hre j) (congrFun him j)
  · rintro rfl x
    simp only [thetaSeamPacket, Pi.zero_apply, zero_mul, sum_const_zero]

theorem continuous_thetaSeamPacket {N : ℕ} (c : Fin N → ℂ) :
    Continuous (thetaSeamPacket c) := by
  unfold thetaSeamPacket
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_iteratedDeriv_thetaCuspFullSource j.val x).continuousAt))

theorem integrable_thetaSeamPacket {N : ℕ} (c : Fin N → ℂ) :
    Integrable (thetaSeamPacket c) := by
  unfold thetaSeamPacket
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  have hi : Integrable (fun x => |iteratedDeriv j.val thetaCuspFullSource x|) := by
    simpa only [zero_mul, Real.exp_zero, one_mul] using
      integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource j.val 0
  apply hi.mono' ((Complex.continuous_ofReal.comp
    (continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_iteratedDeriv_thetaCuspFullSource j.val x).continuousAt)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖((iteratedDeriv j.val thetaCuspFullSource x : ℝ) : ℂ)‖ ≤
      |iteratedDeriv j.val thetaCuspFullSource x|
    simp only [Complex.norm_real, Real.norm_eq_abs, le_refl]

/-- Finite packets have integrable square mass because their exact source
derivatives are both bounded and integrable. -/
theorem integrable_normSq_thetaSeamPacket {N : ℕ} (c : Fin N → ℂ) :
    Integrable (fun x => Complex.normSq (thetaSeamPacket c x)) := by
  let C : ℝ := ∑ j : Fin N, ‖c j‖ * thetaCuspDerivativeExpConstant j.val
  have hb (x : ℝ) : ‖thetaSeamPacket c x‖ ≤ C := by
    unfold thetaSeamPacket
    refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs j.val x).trans
      (mul_le_of_le_one_right (thetaCuspDerivativeExpConstant_nonneg _)
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg x))))
  have hi := (integrable_thetaSeamPacket c).norm.const_mul C
  apply hi.mono' ((Complex.continuous_normSq.comp (continuous_thetaSeamPacket c)).aestronglyMeasurable)
  filter_upwards with x
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simpa only [pow_two] using mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (thetaSeamPacket c x))

/-- The finite derivative packet has zero square mass exactly for zero coefficients. -/
theorem integral_normSq_thetaSeamPacket_pos {N : ℕ} {c : Fin N → ℂ} (hc : c ≠ 0) :
    0 < ∫ x : ℝ, Complex.normSq (thetaSeamPacket c x) := by
  have hn : ¬ ∀ x : ℝ, thetaSeamPacket c x = 0 := fun h =>
    hc ((thetaSeamPacket_eq_zero_iff c).mp h)
  obtain ⟨x, hx⟩ := not_forall.mp hn
  have hcont := Complex.continuous_normSq.comp (continuous_thetaSeamPacket c)
  rw [integral_pos_iff_support_of_nonneg (fun x => Complex.normSq_nonneg _)
    (integrable_normSq_thetaSeamPacket c)]
  exact hcont.isOpen_support.measure_pos volume ⟨x, (Complex.normSq_pos.mpr hx).ne'⟩

/-- The literal complete signed tail head. -/
def nativeTailHead (N : ℕ) (r : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  finiteHankelMatrix (fun k => thetaCuspNativeSignedJetTail k r) N

/-- Every finite seam head is strict: its exact derivative Gram has zero radical. -/
theorem nativeTailHead_zero_posDef (N : ℕ) : (nativeTailHead N 0).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeTailHead, finiteHankelMatrix, Nat.add_comm]
  · intro v hv
    let c : Fin N → ℂ := fun j => ((v j * 2 ^ j.val : ℝ) : ℂ) * Complex.I ^ j.val
    have hc : c ≠ 0 := by
      intro hz
      apply hv
      funext j
      have hj := congrFun hz j
      have hI : Complex.I ^ j.val ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
      have hreal : ((v j * 2 ^ j.val : ℝ) : ℂ) = 0 :=
        (mul_eq_zero.mp hj).resolve_right hI
      have hr : v j * 2 ^ j.val = 0 := Complex.ofReal_eq_zero.mp hreal
      exact (mul_eq_zero.mp hr).resolve_right (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
    have he : star v ⬝ᵥ nativeTailHead N 0 *ᵥ v = thetaCuspNativeTailHankelForm 0 v := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum,
        nativeTailHead, finiteHankelMatrix, thetaCuspNativeTailHankelForm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    rw [he, thetaCuspNativeTailHankelForm_zero_eq]
    have hpacket (x : ℝ) :
        (∑ j : Fin N, ((v j * 2 ^ j.val * iteratedDeriv j.val thetaCuspFullSource x : ℝ) : ℂ) *
          Complex.I ^ j.val) = thetaSeamPacket c x := by
      unfold thetaSeamPacket
      apply sum_congr rfl
      intro j _
      dsimp only [c]
      push_cast
      ring
    simp_rw [hpacket]
    exact integral_normSq_thetaSeamPacket_pos hc

/-- Moving the tail endpoint has a literal entrywise cost fixed by native decay. -/
theorem nativeSignedJetTail_seam_error_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    |thetaCuspNativeSignedJetTail k r - thetaCuspNativeSignedJetTail k 0| ≤
      r * thetaCuspNativeJetDecayConstant k := by
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_thetaCuspNativeSignedJet_half k le_rfl)
    (integrableOn_thetaCuspNativeSignedJet_half k hr)
  have he : thetaCuspNativeSignedJetTail k r - thetaCuspNativeSignedJetTail k 0 =
      -(∫ s : ℝ in 0..r, thetaCuspNativeSignedJet (s / 2) k) := by
    unfold thetaCuspNativeSignedJetTail
    linarith only [hsplit]
  have hb : ‖∫ s : ℝ in 0..r, thetaCuspNativeSignedJet (s / 2) k‖ ≤
      thetaCuspNativeJetDecayConstant k * |r - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [Set.uIoc_of_le hr] at hs
    rw [Real.norm_eq_abs]
    exact (abs_thetaCuspNativeSignedJet_half_le k hs.1.le).trans
      (mul_le_of_le_one_right (thetaCuspNativeJetDecayConstant_nonneg _)
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1.le)))
  rw [he, abs_neg]
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hr, mul_comm] using hb

/-- A finite native decay envelope containing every entry of the requested head. -/
def nativeSeamDecayEnvelope (N : ℕ) : ℝ :=
  ∑ k ∈ range (2 * N + 1), thetaCuspNativeJetDecayConstant k

theorem nativeSeamDecayEnvelope_nonneg (N : ℕ) : 0 ≤ nativeSeamDecayEnvelope N :=
  sum_nonneg fun k _ => thetaCuspNativeJetDecayConstant_nonneg k

private theorem nativeSeamDecayEnvelope_entry_le (N : ℕ) (i j : Fin N) :
    thetaCuspNativeJetDecayConstant (i.val + j.val) ≤ nativeSeamDecayEnvelope N :=
  single_le_sum (fun k _ => thetaCuspNativeJetDecayConstant_nonneg k)
    (mem_range.mpr (by omega))

/-- Full seam inverse cost of moving the tail endpoint by one unit. -/
def nativeSeamErrorRate (N : ℕ) : ℝ :=
  (N : ℝ) * nativeSeamDecayEnvelope N * (nativeTailHead N 0)⁻¹.trace

theorem nativeSeamErrorRate_nonneg (N : ℕ) : 0 ≤ nativeSeamErrorRate N := by
  have ht : 0 ≤ (nativeTailHead N 0)⁻¹.trace :=
    sum_nonneg fun i _ => (nativeTailHead_zero_posDef N).inv.posSemidef.diag_nonneg
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (nativeSeamDecayEnvelope_nonneg _)) ht

private theorem nativeTailHead_seam_entry_error_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (i j : Fin N) :
    |nativeTailHead N r i j - nativeTailHead N 0 i j| ≤ r * nativeSeamDecayEnvelope N :=
  (nativeSignedJetTail_seam_error_le (i.val + j.val) hr).trans
    (mul_le_mul_of_nonneg_left (nativeSeamDecayEnvelope_entry_le N i j) hr)

/-- The displaced complete tail is controlled in its full seam quadratic norm. -/
theorem nativeTailHead_seam_relative_error_le (N : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (nativeTailHead N r - nativeTailHead N 0) *ᵥ v| ≤
      (r * nativeSeamErrorRate N) * (v ⬝ᵥ nativeTailHead N 0 *ᵥ v) := by
  have h := relative_error_le_inverseTrace (nativeTailHead_zero_posDef N)
    (mul_nonneg hr (nativeSeamDecayEnvelope_nonneg N)) (nativeTailHead_seam_entry_error_le N hr) v
  convert h using 1
  unfold nativeSeamErrorRate
  ring

/-- Explicit positive interval retaining half the entire complete-source seam form. -/
def nativeSeamRadius (N : ℕ) : ℝ := 1 / (2 * (1 + nativeSeamErrorRate N))

theorem nativeSeamRadius_pos (N : ℕ) : 0 < nativeSeamRadius N := by
  have h := nativeSeamErrorRate_nonneg N
  unfold nativeSeamRadius
  positivity

/-- Every rank has an explicit source interval with strict half-seam reserve. -/
theorem nativeTailHead_half_posDef_of_seam_radius (N : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hradius : r ≤ nativeSeamRadius N) :
    (nativeTailHead N r - (1 / 2 : ℝ) • nativeTailHead N 0).PosDef := by
  have hA : (nativeTailHead N r).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [nativeTailHead, finiteHankelMatrix, Nat.add_comm]
  apply half_relative_posDef_of_inverseTrace (nativeTailHead_zero_posDef N) hA
    (mul_nonneg hr (nativeSeamDecayEnvelope_nonneg N)) (nativeTailHead_seam_entry_error_le N hr)
  have hrate := nativeSeamErrorRate_nonneg N
  have hden : 0 < 2 * (1 + nativeSeamErrorRate N) := by positivity
  have hratio : nativeSeamErrorRate N / (2 * (1 + nativeSeamErrorRate N)) < 1 / 2 := by
    apply (div_lt_iff₀ hden).mpr
    linarith only
  have hrpay : r * nativeSeamErrorRate N ≤
      nativeSeamErrorRate N / (2 * (1 + nativeSeamErrorRate N)) := by
    have h := mul_le_mul_of_nonneg_right hradius hrate
    simpa only [nativeSeamRadius, one_div, mul_comm, div_eq_mul_inv, one_mul] using h
  have hcost := hrpay.trans_lt hratio
  have he : (N : ℝ) * (r * nativeSeamDecayEnvelope N) * (nativeTailHead N 0)⁻¹.trace =
      r * nativeSeamErrorRate N := by unfold nativeSeamErrorRate; ring
  rw [he]
  exact hcost

private theorem finiteHankel_energy (m : ℕ → ℝ) {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ finiteHankelMatrix m N *ᵥ v = ∑ i : Fin N, ∑ j : Fin N, v i * v j * m (i.val + j.val) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, finiteHankelMatrix]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- The unweighted complete native form remains integrable beyond every nonnegative center. -/
theorem integrableOn_nativeSignedHankelForm_tail {N : ℕ} (v : Fin N → ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun s => thetaCuspNativeSignedHankelForm (s / 2) v) (Ioi r) := by
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrableOn_thetaCuspNativeSignedJet_half (i.val + j.val) hr).const_mul (v i * v j)

/-- Tail compression retains every mixed entry of the literal native form. -/
theorem nativeTailHead_quadratic_eq_integral {N : ℕ} (v : Fin N → ℝ)
    {r : ℝ} (hr : 0 ≤ r) :
    v ⬝ᵥ nativeTailHead N r *ᵥ v =
      ∫ s in Ioi r, thetaCuspNativeSignedHankelForm (s / 2) v := by
  have hi (i j : Fin N) :=
    (integrableOn_thetaCuspNativeSignedJet_half (i.val + j.val) hr).const_mul (v i * v j)
  unfold nativeTailHead
  rw [finiteHankel_energy]
  unfold thetaCuspNativeSignedHankelForm
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ => hi i j]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul]
  rfl

/-- The explicit native horizon also gives a strict complete tail head at every later endpoint. -/
theorem nativeTailHead_posDef_of_horizon (N : ℕ) {r : ℝ}
    (hr : 2 * nativeMixedHorizon N ≤ r) : (nativeTailHead N r).PosDef := by
  have hH : 0 ≤ nativeMixedHorizon N := le_max_left _ _
  have hr0 : 0 ≤ r := by linarith only [hr, hH]
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian]
    ext i j
    simp [nativeTailHead, finiteHankelMatrix, Nat.add_comm]
  · intro v hv
    have hpos (s : ℝ) (hs : s ∈ Ioi r) :
        0 < thetaCuspNativeSignedHankelForm (s / 2) v := by
      have hsH : nativeMixedHorizon N ≤ s / 2 := by
        have hs' : r < s := hs
        linarith only [hr, hs']
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp
        (nativeSignedHead_posDef_of_horizon N hsH)).2 (x := v) hv
      simpa only [star_trivial, finiteHankel_energy, thetaCuspNativeSignedHankelForm] using h
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi r)]
        (fun s => thetaCuspNativeSignedHankelForm (s / 2) v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact (hpos s hs).le
    rw [star_trivial, nativeTailHead_quadratic_eq_integral v hr0,
      setIntegral_pos_iff_support_of_nonneg_ae hnn (integrableOn_nativeSignedHankelForm_tail v hr0)]
    have hsupport : Ioi r ⊆ Function.support (fun s => thetaCuspNativeSignedHankelForm (s / 2) v) :=
      fun s hs => (hpos s hs).ne'
    rw [Set.inter_eq_right.mpr hsupport]
    exact isOpen_Ioi.measure_pos volume ⟨r + 1, by change r < r + 1; linarith⟩

#print axioms thetaDerivativePacket_coefficients_eq_zero
#print axioms thetaSeamPacket_eq_zero_iff
#print axioms nativeTailHead_zero_posDef
#print axioms nativeSignedJetTail_seam_error_le
#print axioms nativeTailHead_seam_relative_error_le
#print axioms nativeTailHead_half_posDef_of_seam_radius
#print axioms nativeTailHead_posDef_of_horizon

end GaloisForLFunctions.CompletedArithmeticForms
