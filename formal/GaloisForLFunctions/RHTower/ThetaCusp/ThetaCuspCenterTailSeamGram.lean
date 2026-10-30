import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailRepresentation
import GaloisForLFunctions.RHTower.ThetaDerivativePacketDivisor

/-!
# The seam tail is a Plancherel Gram at every order

At the self-dual seam the center tail of every finite signed section is a sum of squares:

`Σ_{i,j} v_i v_j U_{i+j}(0) = ∫_ℝ |Σ_j v_j (2i)^j Φ^{(j)}(x)|² dx`.

Integration by parts moves derivatives between the two reflected factors, and the alternating
Fourier signs of the signed jets are exactly the phases `(-i)^a i^b` that turn the pairings
`∫ Φ^{(a)} Φ^{(b)}` into a Hermitian Gram matrix. Thus the tail certificate of
`ThetaCuspCenterTailRepresentation` holds at the seam unconditionally and at every order.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

/-- The `L²(ℝ)` pairing of two derivatives of the complete theta source. -/
def thetaCuspDerivativePairing (i j : ℕ) : ℝ :=
  ∫ x, iteratedDeriv i thetaCuspFullSource x * iteratedDeriv j thetaCuspFullSource x

private theorem integrable_abs_iteratedDeriv (j : ℕ) :
    Integrable (fun x => |iteratedDeriv j thetaCuspFullSource x|) := by
  simpa using integrable_exp_abs_mul_abs_iteratedDeriv_thetaCuspFullSource j 0

private theorem continuous_iteratedDeriv_source (j : ℕ) :
    Continuous (iteratedDeriv j thetaCuspFullSource) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_iteratedDeriv_thetaCuspFullSource j x).continuousAt

theorem integrable_iteratedDeriv_mul_iteratedDeriv (i j : ℕ) :
    Integrable (fun x => iteratedDeriv i thetaCuspFullSource x *
      iteratedDeriv j thetaCuspFullSource x) := by
  refine ((integrable_abs_iteratedDeriv j).const_mul (thetaCuspDerivativeExpConstant i)).mono'
    ((continuous_iteratedDeriv_source i).mul (continuous_iteratedDeriv_source j)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hi := abs_iteratedDeriv_thetaCuspFullSource_le_exp_neg_abs i x
  have he : thetaCuspDerivativeExpConstant i * Real.exp (-|x|) ≤
      thetaCuspDerivativeExpConstant i :=
    mul_le_of_le_one_right (thetaCuspDerivativeExpConstant_nonneg i)
      (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x]))
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hi.trans he) (abs_nonneg _)

/-- One integration by parts moves a derivative across the pairing. -/
theorem thetaCuspDerivativePairing_succ_left (i j : ℕ) :
    thetaCuspDerivativePairing (i+1) j = -thetaCuspDerivativePairing i (j+1) := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := iteratedDeriv j thetaCuspFullSource) (v := iteratedDeriv i thetaCuspFullSource)
    (u' := iteratedDeriv (j+1) thetaCuspFullSource) (v' := iteratedDeriv (i+1) thetaCuspFullSource)
    (fun x _ => hasDerivAt_iteratedDeriv_thetaCuspFullSource j x)
    (fun x _ => hasDerivAt_iteratedDeriv_thetaCuspFullSource i x)
    (integrable_iteratedDeriv_mul_iteratedDeriv j (i+1))
    (integrable_iteratedDeriv_mul_iteratedDeriv (j+1) i)
    (integrable_iteratedDeriv_mul_iteratedDeriv j i)
  unfold thetaCuspDerivativePairing
  simp_rw [mul_comm (iteratedDeriv (i+1) thetaCuspFullSource _),
    mul_comm (iteratedDeriv i thetaCuspFullSource _)]
  exact h

/-- **Phase transport.** The Fourier phase `(-i)^a i^b` turns every pairing into the same
value, determined by the total order. -/
theorem re_phase_mul_thetaCuspDerivativePairing (i j : ℕ) :
    ((-Complex.I)^i * Complex.I^j).re * thetaCuspDerivativePairing i j =
      ((-Complex.I)^(i+j)).re * thetaCuspDerivativePairing 0 (i+j) := by
  induction i generalizing j with
  | zero =>
    have hc : (Complex.I^j).re = ((-Complex.I)^j).re := by
      rw [← Complex.conj_re (Complex.I^j), map_pow, Complex.conj_I]
    simp only [pow_zero, one_mul, zero_add, hc]
  | succ i ih =>
    have hz : (-Complex.I)^(i+1) * Complex.I^j = -((-Complex.I)^i * Complex.I^(j+1)) := by ring
    rw [thetaCuspDerivativePairing_succ_left, hz, Complex.neg_re, neg_mul_neg, ih (j+1),
      show i + (j+1) = i + 1 + j by omega]

/-- The whole-line integral of a native reflection jet. -/
theorem integral_thetaCuspNativeReflectionJet (k : ℕ) :
    ∫ x, thetaCuspNativeReflectionJet k x =
      ∑ l ∈ Finset.range (k+1), (k.choose l : ℝ) * (-1 : ℝ)^(k-l) *
        thetaCuspDerivativePairing l (k-l) := by
  have hpoint : (fun x => thetaCuspNativeReflectionJet k x) = fun x =>
      ∑ l ∈ Finset.range (k+1), ((k.choose l : ℝ) * (-1 : ℝ)^(k-l)) *
        (iteratedDeriv l thetaCuspFullSource x * iteratedDeriv (k-l) thetaCuspFullSource x) := by
    funext x
    rw [thetaCuspNativeReflectionJet_eq]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hpoint, integral_finsetSum _ fun l _ =>
    (integrable_iteratedDeriv_mul_iteratedDeriv l (k-l)).const_mul _]
  exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul]; rfl

/-- **Seam moment law.** The whole-line integral of the signed jet of order `k` is
`2^k Re((-i)^k) ∫ Φ Φ^{(k)}`. -/
theorem integral_thetaCuspNativeSignedJet (k : ℕ) :
    ∫ x, thetaCuspNativeSignedJet x k =
      2^k * (((-Complex.I)^k).re * thetaCuspDerivativePairing 0 k) := by
  have hterm (l : ℕ) (hl : l ∈ Finset.range (k+1)) :
      ((-Complex.I)^k).re * ((k.choose l : ℝ) * (-1 : ℝ)^(k-l) * thetaCuspDerivativePairing l (k-l)) =
        (k.choose l : ℝ) * (((-Complex.I)^k).re * thetaCuspDerivativePairing 0 k) := by
    have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hphase : ((-Complex.I)^k).re * (-1 : ℝ)^(k-l) = ((-Complex.I)^l * Complex.I^(k-l)).re := by
      have hz : (-Complex.I)^l * Complex.I^(k-l) = (((-1 : ℝ)^(k-l) : ℝ) : ℂ) * (-Complex.I)^k := by
        have h1 : Complex.I^(k-l) = (-1 : ℂ)^(k-l) * (-Complex.I)^(k-l) := by
          rw [← mul_pow]; congr 1; ring
        rw [h1, show (-Complex.I)^k = (-Complex.I)^l * (-Complex.I)^(k-l) by
          rw [← pow_add, Nat.add_sub_cancel' hlk]]
        push_cast
        ring
      rw [hz, Complex.re_ofReal_mul]
      ring
    have h := re_phase_mul_thetaCuspDerivativePairing l (k-l)
    rw [Nat.add_sub_cancel' hlk] at h
    calc ((-Complex.I)^k).re * ((k.choose l : ℝ) * (-1 : ℝ)^(k-l) * thetaCuspDerivativePairing l (k-l))
        = (k.choose l : ℝ) * ((((-Complex.I)^k).re * (-1 : ℝ)^(k-l)) *
            thetaCuspDerivativePairing l (k-l)) := by ring
      _ = _ := by rw [hphase, h]
  unfold thetaCuspNativeSignedJet
  rw [integral_const_mul, integral_thetaCuspNativeReflectionJet, Finset.mul_sum,
    Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- Signed jets are even in the center. -/
theorem thetaCuspNativeSignedJet_neg (x : ℝ) (k : ℕ) :
    thetaCuspNativeSignedJet (-x) k = thetaCuspNativeSignedJet x k := by
  unfold thetaCuspNativeSignedJet thetaCuspNativeReflectionJet
  congr 2
  funext t
  rw [show -x + t = -(x - t) by ring, show -x - t = -(x + t) by ring,
    thetaCuspFullSource_neg, thetaCuspFullSource_neg]
  ring

theorem integrable_thetaCuspNativeSignedJet (k : ℕ) :
    Integrable (fun x => thetaCuspNativeSignedJet x k) := by
  have h : Integrable (fun x => thetaCuspNativeReflectionJet k x) := by
    have hpoint : (fun x => thetaCuspNativeReflectionJet k x) = fun x =>
        ∑ l ∈ Finset.range (k+1), ((k.choose l : ℝ) * (-1 : ℝ)^(k-l)) *
          (iteratedDeriv l thetaCuspFullSource x * iteratedDeriv (k-l) thetaCuspFullSource x) := by
      funext x
      rw [thetaCuspNativeReflectionJet_eq]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hpoint]
    exact integrable_finsetSum _ fun l _ =>
      (integrable_iteratedDeriv_mul_iteratedDeriv l (k-l)).const_mul _
  unfold thetaCuspNativeSignedJet
  exact h.const_mul _

/-- The seam tail is the whole-line integral of the signed jet. -/
theorem thetaCuspNativeSignedJetTail_zero (k : ℕ) :
    thetaCuspNativeSignedJetTail k 0 = ∫ x, thetaCuspNativeSignedJet x k := by
  have hf := integrable_thetaCuspNativeSignedJet k
  have hscale : (∫ s in Ioi (0 : ℝ), thetaCuspNativeSignedJet (s/2) k) =
      2 * ∫ x in Ioi (0 : ℝ), thetaCuspNativeSignedJet x k := by
    have h := integral_comp_mul_left_Ioi (fun x => thetaCuspNativeSignedJet x k) 0
      (show (0 : ℝ) < 1/2 by norm_num)
    simp only [mul_zero, smul_eq_mul] at h
    rw [show (fun s : ℝ => thetaCuspNativeSignedJet (s/2) k) =
      fun s => thetaCuspNativeSignedJet (1/2 * s) k by funext s; ring_nf, h]
    norm_num
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := 0) hf.integrableOn hf.integrableOn
  have hneg : (∫ x in Iic (0 : ℝ), thetaCuspNativeSignedJet x k) =
      ∫ x in Ioi (0 : ℝ), thetaCuspNativeSignedJet x k := by
    have h := integral_comp_neg_Iic 0 (fun x => thetaCuspNativeSignedJet x k)
    simp only [thetaCuspNativeSignedJet_neg, neg_zero] at h
    exact h
  unfold thetaCuspNativeSignedJetTail
  rw [hscale]
  linarith

/-- **Seam Gram law.** At the self-dual seam every finite tail Hankel form is the squared
`L²` norm of `Σ_j v_j (2i)^j Φ^{(j)}`; in particular it is nonnegative at every order. -/
theorem thetaCuspNativeTailHankelForm_zero_eq {N : ℕ} (v : Fin N → ℝ) :
    thetaCuspNativeTailHankelForm 0 v =
      ∫ x, Complex.normSq (∑ j : Fin N,
        ((v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource x : ℝ) : ℂ) * Complex.I^(j : ℕ)) := by
  have hpair (i j : Fin N) :
      thetaCuspNativeSignedJetTail ((i : ℕ) + j) 0 =
        2^((i : ℕ) + j) * (((-Complex.I)^(i : ℕ) * Complex.I^(j : ℕ)).re * thetaCuspDerivativePairing i j) := by
    rw [thetaCuspNativeSignedJetTail_zero, integral_thetaCuspNativeSignedJet,
      re_phase_mul_thetaCuspDerivativePairing]
  have hpoint (x : ℝ) : Complex.normSq (∑ j : Fin N,
      ((v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource x : ℝ) : ℂ) * Complex.I^(j : ℕ)) =
      ∑ i : Fin N, ∑ j : Fin N, (v i * v j * 2^((i : ℕ) + j) * ((-Complex.I)^(i : ℕ) * Complex.I^(j : ℕ)).re) *
        (iteratedDeriv i thetaCuspFullSource x * iteratedDeriv j thetaCuspFullSource x) := by
    have hn : ∀ z : ℂ, Complex.normSq z = ((starRingEnd ℂ) z * z).re := fun z => by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    rw [hn, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_ofReal, map_pow, Complex.conj_I]
    have hz : ((v i * 2^(i : ℕ) * iteratedDeriv i thetaCuspFullSource x : ℝ) : ℂ) * (-Complex.I)^(i : ℕ) *
        (((v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource x : ℝ) : ℂ) * Complex.I^(j : ℕ)) =
        (((v i * 2^(i : ℕ) * iteratedDeriv i thetaCuspFullSource x) *
          (v j * 2^(j : ℕ) * iteratedDeriv j thetaCuspFullSource x) : ℝ) : ℂ) *
            ((-Complex.I)^(i : ℕ) * Complex.I^(j : ℕ)) := by push_cast; ring
    rw [hz, Complex.re_ofReal_mul, pow_add]
    ring
  have hint (i j : Fin N) := (integrable_iteratedDeriv_mul_iteratedDeriv i j).const_mul
    (v i * v j * 2^((i : ℕ) + j) * ((-Complex.I)^(i : ℕ) * Complex.I^(j : ℕ)).re)
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  unfold thetaCuspNativeTailHankelForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hpair]
  unfold thetaCuspDerivativePairing
  ring

theorem thetaCuspNativeTailHankelForm_zero_nonneg {N : ℕ} (v : Fin N → ℝ) :
    0 ≤ thetaCuspNativeTailHankelForm 0 v := by
  rw [thetaCuspNativeTailHankelForm_zero_eq]
  exact integral_nonneg fun x => Complex.normSq_nonneg _

end
end RHTower
