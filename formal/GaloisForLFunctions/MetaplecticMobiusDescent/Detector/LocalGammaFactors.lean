/-
Local Gamma factors adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.PrincipalSignalComparison

/-!
# Local Gamma factors

Even ratios and the actual cube of the Euler coordinates; positive scalars and local Gamma
factors of prime powers; the normalized prime trace Gauss sum and corrected cubic signals.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace ProbePrimePower
open Eisenstein

local notation "O" => Eisenstein.O

theorem higher_outer_lift_annihilated (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) {n : ℕ} (hn : 0 < n) (m : O) :
    ξ (Ideal.Quotient.mk (Ideal.span {p}) m) * primePowerGauss p hp χ n (-m) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hG : primePowerGauss p hp χ n (-m) = 0
  · rw [hG, mul_zero]
  · have hdneg := primePowerGauss_support p hp χ n (-m) hG
    have hdpow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hdm : p ∣ m := dvd_neg.mp (hdpow.trans hdneg)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdm)
    rw [hz, MulChar.map_zero, zero_mul]

def scalarKOne (p : O) (hp : p ≠ 0)
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {p}, χ d * primePowerGauss p hp ξ n
    (h - p ^ n * GaussianShiftedPartition.representative p d)

theorem scalarKOne_eq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    scalarKOne p hp χ ξ n h =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (ξ * χ⁻¹) n h := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  by_cases hdiv : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hdiv
    have hmk (d : O ⧸ Ideal.span {p}) :
        Ideal.Quotient.mk (Ideal.span {p})
          (k - GaussianShiftedPartition.representative p d) =
          Ideal.Quotient.mk (Ideal.span {p}) k - d := by
      rw [map_sub, GaussianShiftedPartition.representative_spec]
    have hscalar : scalarKOne p hp χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : O ⧸ Ideal.span {p}, χ d * ProbeGauss.frequencyGauss ξ
            (primitiveTrace p hp) (Ideal.Quotient.mk _ k - d) := by
      unfold scalarKOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, primePowerGauss_lift]
      have he : primeGauss p hp ξ (k - GaussianShiftedPartition.representative p d) =
          ProbeGauss.frequencyGauss ξ (primitiveTrace p hp) (Ideal.Quotient.mk _ k - d) := by
        rw [primeGauss, tsum_fintype]
        simp only [hmk, ProbeGauss.frequencyGauss]
      rw [he]
      ring
    rw [hscalar, ProbeGauss.finite_gauss_convolution, primePowerGauss_lift]
    have hG : primeGauss p hp χ 1 = gaussSum χ (primitiveTrace p hp) := by
      simp [primeGauss, tsum_fintype, gaussSum]
    have hF : primeGauss p hp (ξ * χ⁻¹) k =
        ProbeGauss.frequencyGauss (ξ * χ⁻¹) (primitiveTrace p hp) (Ideal.Quotient.mk _ k) := by
      simp only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss]
    rw [hG, hF]
    ring
  · rw [primePowerGauss_zero_off_support p hp (ξ * χ⁻¹) n h hdiv, mul_zero]
    unfold scalarKOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hndiv : ¬p ^ n ∣ h - p ^ n * GaussianShiftedPartition.representative p d := by
      intro hd
      apply hdiv
      have ha := dvd_add hd (dvd_mul_right (p ^ n)
        (GaussianShiftedPartition.representative p d))
      simpa only [sub_add_cancel] using ha
    rw [primePowerGauss_zero_off_support p hp ξ n _ hndiv, mul_zero]

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePrimePower
open Eisenstein GaussianShiftedPartition
local notation "O" => Eisenstein.O

def positiveScalar (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) : ℂ :=
  if k = 0 then primePowerGauss p hp (χ^(n+1)) n (p^j)
  else ∑' d : O ⧸ Ideal.span {p^k},
    if h : p^k ∣ p^j-p^(n+1)*representative (p^k) d then
      (χ^k) (Ideal.Quotient.mk (Ideal.span {p}) (representative (p^k) d)) *
        primePowerGauss p hp (χ^(n+1)) n
          (exactQuotient (p^j-p^(n+1)*representative (p^k) d) (p^k) h)
    else 0

@[simp] theorem positiveScalar_kzero (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 0 j = primePowerGauss p hp (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, ite_true]

theorem positiveScalar_kone_jzero (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    positiveScalar p hp.ne_zero χ n 1 0 = 0 := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false]
  rw [pow_one]
  simp only [pow_zero, pow_one]
  refine (tsum_congr (g := fun _ => (0:ℂ)) ?_).trans tsum_zero
  intro d
  rw [dif_neg]
  intro hd
  have hd2 : p ∣ p^(n+1)*representative p d :=
    (dvd_pow_self p (by omega : n+1 ≠ 0)).mul_right _
  have hunit : p ∣ (1:O) := by
    have := dvd_add hd hd2
    simpa only [sub_add_cancel] using this
  exact hp.not_unit (isUnit_iff_dvd_one.mpr hunit)

theorem positiveScalar_kone_convolution (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) = scalarKOne p hp χ (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false, scalarKOne]
  rw [pow_one]
  simp only [pow_one]
  apply tsum_congr
  intro d
  have he : p^(j+1)-p^(n+1)*representative p d = p*(p^j-p^n*representative p d) := by
    simp only [pow_succ]
    ring
  have hd : p ∣ p^(j+1)-p^(n+1)*representative p d := ⟨_,he⟩
  rw [dif_pos hd, exactQuotient_eq _ _ _ hd hp he, representative_spec]

theorem positiveScalar_kone (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (χ^n) n (p^j) := by
  rw [positiveScalar_kone_convolution, scalarKOne_eq]
  have he : χ^(n+1)*χ⁻¹ = χ^n := by rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePrimePower
open Eisenstein GaussianShiftedPartition
local notation "O" => Eisenstein.O

theorem primePowerGauss_lift_add (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    primePowerGauss p hp.ne_zero χ (n+k) (p^k*h) =
      (Ideal.absNorm (Ideal.span {p}):ℂ)^k * primePowerGauss p hp.ne_zero χ n h := by
  by_cases hd : p^n ∣ h
  · obtain ⟨a, rfl⟩ := hd
    have he : p^k*(p^n*a) = p^(n+k)*a := by rw [pow_add]; ring
    rw [he, primePowerGauss_lift, primePowerGauss_lift, pow_add]
    ring
  · have hbig : ¬p^(n+k) ∣ p^k*h := by
      rw [pow_add, mul_comm (p^n) (p^k), mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
      exact hd
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hbig,
      primePowerGauss_zero_off_support _ _ _ _ _ hd, mul_zero]

theorem primePowerGauss_add_period (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h a : O) :
    primePowerGauss p hp χ n (h+p^(n+1)*a) = primePowerGauss p hp χ n h := by
  unfold primePowerGauss conductorFourier
  apply tsum_congr
  intro x
  have hz : Ideal.Quotient.mk (Ideal.span {p*p^n}) (p^(n+1)*a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    rw [pow_succ']
  simp only [map_add, hz, add_zero]

theorem gauss_exactQuotient_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    (if hd : p^k ∣ h then primePowerGauss p hp.ne_zero χ n (exactQuotient h (p^k) hd) else 0) =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ * primePowerGauss p hp.ne_zero χ (n+k) h := by
  have hq : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  by_cases hd : p^k ∣ h
  · rw [dif_pos hd]
    conv_rhs => rw [exactQuotient_spec h (p^k) hd]
    rw [primePowerGauss_lift_add p hp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  · rw [dif_neg hd]
    have hnd : ¬p^(n+k) ∣ h := by
      intro he
      exact hd ((show p^k ∣ p^(n+k) from ⟨p^n, by rw [pow_add]; ring⟩).trans he)
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hnd, mul_zero]

theorem positiveScalar_full_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) (hk : k ≠ 0) :
    positiveScalar p hp.ne_zero χ n k j =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ *
        ∑' d : O ⧸ Ideal.span {p^k},
          (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) *
            primePowerGauss p hp.ne_zero (χ^(n+1)) (n+k)
              (p^j-p^(n+1)*representative (p^k) d) := by
  rw [positiveScalar, if_neg hk, ← tsum_mul_left]
  apply tsum_congr
  intro d
  have he := gauss_exactQuotient_lift p hp (χ^(n+1)) n k
    (p^j-p^(n+1)*representative (p^k) d)
  by_cases hd : p^k ∣ p^j-p^(n+1)*representative (p^k) d
  · rw [dif_pos hd] at he ⊢
    rw [he]
    ring
  · rw [dif_neg hd] at he ⊢
    linear_combination (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) * he

lemma primitiveTrace_split_frequency (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (H d v : O) :
    primitiveTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ ((H-b*d)*v)) =
      primitiveTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (H*v)) *
        primitiveTrace a ha (Ideal.Quotient.mk _ ((-v)*d)) := by
  simp only [CenteredMomentFourier.primitiveTrace, residueTraceQuotientChar_phase, one_mul]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [map_mul, map_sub, map_neg]
  field_simp [ringComplex_ne_zero ha, ringComplex_ne_zero hb,
    ringComplex_ne_zero traceLambda_ne_zero] <;> ring


end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePrimePower
open Eisenstein GaussianShiftedPartition
local notation "O" => Eisenstein.O

theorem higher_convolution_zero (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m : ℕ) (H : O) :
    (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        primePowerGauss p hp.ne_zero ξ (n+(m+2))
          (H-p^(n+1)*representative (p^(m+2)) d)) = 0 := by
  let : Finite (O ⧸ Ideal.span {p^(m+2)}) :=
    finiteEisensteinQuotientOfNonzero (pow_ne_zero _ hp.ne_zero)
  let : Fintype (O ⧸ Ideal.span {p^(m+2)}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {p*p^(n+(m+2))}) :=
    finiteEisensteinQuotientOfNonzero (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
  let : Fintype (O ⧸ Ideal.span {p*p^(n+(m+2))}) := Fintype.ofFinite _
  have hmod : p*p^(n+(m+2)) = p^(m+2)*p^(n+1) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  have hinner (V : O) : (∑' d : O ⧸ Ideal.span {p^(m+2)},
      χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
        primitiveTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
          (Ideal.Quotient.mk _ ((-V)*representative (p^(m+2)) d))) =
      primePowerGauss p hp.ne_zero χ (m+1) (-V) := by
    change quotientFourier p (p^(m+2)) (pow_ne_zero _ hp.ne_zero) χ (-V) = _
    rw [primePowerGauss_eq_quotientFourier]
    apply quotientFourier_congr
    rw [← pow_succ']
  unfold primePowerGauss conductorFourier
  simp_rw [tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
  change (∑ d : O ⧸ Ideal.span {p^(m+2)},
    χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
      (ξ (Ideal.Quotient.mk _ v) *
        primitiveTrace (p*p^(n+(m+2))) _
          (Ideal.Quotient.mk _ (H-p^(n+1)*representative (p^(m+2)) d)*Ideal.Quotient.mk _ v))) = 0
  have ht (d : O ⧸ Ideal.span {p^(m+2)}) :
      primitiveTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ ((H-p^(n+1)*representative (p^(m+2)) d)*v)) =
      primitiveTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ (H*v)) *
      primitiveTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
        (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
    have ht := primitiveTrace_split_frequency (p^(m+2)) (p^(n+1))
      (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero) H
      (representative (p^(m+2)) d) v
    simp only [residueTraceQuotientChar_phase] at ht ⊢
    simpa only [← hmod] using ht
  simp_rw [← map_mul, ht]
  calc
    _ = ξ (Ideal.Quotient.mk _ v) *
        primitiveTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        ∑ d : O ⧸ Ideal.span {p^(m+2)},
          χ (Ideal.Quotient.mk _ (representative (p^(m+2)) d)) *
            primitiveTrace (p^(m+2)) (pow_ne_zero _ hp.ne_zero)
              (Ideal.Quotient.mk _ ((-v)*representative (p^(m+2)) d)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = primitiveTrace (p*p^(n+(m+2))) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
          (Ideal.Quotient.mk _ (H*v)) *
        (ξ (Ideal.Quotient.mk _ v) * primePowerGauss p hp.ne_zero χ (m+1) (-v)) := by
      have hi := hinner v
      rw [tsum_fintype] at hi
      rw [hi]
      ring
    _ = 0 := by rw [higher_outer_lift_annihilated p hp.ne_zero χ ξ (by omega : 0 < m+1) v, mul_zero]

theorem positiveScalar_kge_two (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n m j : ℕ) :
    positiveScalar p hp.ne_zero χ n (m+2) j = 0 := by
  rw [positiveScalar_full_lift p hp χ n (m+2) j (by omega),
    higher_convolution_zero p hp (χ^(m+2)) (χ^(n+1)) n m (p^j), mul_zero]

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePrimePower
open Eisenstein CompletedGauss 
local notation "O" => Eisenstein.O

def gaussValuationTable (Q G : ℂ) (r n j : ℕ) : ℂ :=
  if 6 ∣ r then (if n+1 ≤ j then Q^(n+1) else 0) - (if n ≤ j then Q^n else 0)
  else if j=n then Q^n*G else 0

theorem complexSexticChar_gaussValuationTable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r n j : ℕ) :
    primePowerGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg ^ r) n (p^j) =
      gaussValuationTable (Ideal.absNorm (Ideal.span {p}))
        (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg ^ r) 1) r n j :=
  complexSexticChar_primePowerGauss_at_pow p hp hg hc r n j

theorem positiveScalar_actual_table (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k j : ℕ) :
    let χ := complexSexticChar (Ideal.span {p}) hg
    let Q : ℂ := Ideal.absNorm (Ideal.span {p})
    positiveScalar p hp.ne_zero χ n k j =
      if k=0 then gaussValuationTable Q (primeGauss p hp.ne_zero (χ^(n+1)) 1) (n+1) n j
      else if k=1 ∧ 1 ≤ j then
        (χ (-1))⁻¹ * primeGauss p hp.ne_zero χ 1 *
          gaussValuationTable Q (primeGauss p hp.ne_zero (χ^n) 1) n n (j-1)
      else 0 := by
  dsimp only
  rcases k with _ | k
  · rw [if_pos rfl, positiveScalar_kzero, complexSexticChar_gaussValuationTable p hp hg hc]
  rcases k with _ | k
  · rcases j with _ | j
    · simp only [ zero_add, Nat.one_ne_zero, ite_false,
          show ¬(1:ℕ) ≤ 0 by omega, and_false]
      exact positiveScalar_kone_jzero p hp _ n
    · rw [if_neg (by omega : (1:ℕ) ≠ 0), if_pos ⟨rfl, by omega⟩,
        positiveScalar_kone p hp.ne_zero, MulChar.inv_apply_eq_inv',
        complexSexticChar_gaussValuationTable p hp hg hc]
      simp
  · rw [if_neg (by omega), if_neg (by omega), positiveScalar_kge_two p hp]

theorem zero_index_scalar (p : O) (_hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (k j : ℕ) (_hk : k ≠ 0) :
    (χ^k) (Ideal.Quotient.mk _ (p^j)) = if j=0 then 1 else 0 := by
  by_cases hj : j=0
  · simp [hj]
  · rw [if_neg hj]
    have hz : Ideal.Quotient.mk (Ideal.span {p}) (p^j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_pow_self p hj))
    rw [hz, MulChar.map_zero]

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss  CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower 
local notation "O" => Eisenstein.O

lemma outerQuotient_prime_power (p : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : lambda∉Ideal.span {p}) (k : ℕ) (hk : k≠0) (d : O ⧸ Ideal.span {p^k}) :
    outerQuotient (p^k) d =
      (complexSexticChar (Ideal.span {p}) hg ^ k)
        (Ideal.Quotient.mk _ (representative (p^k) d)) := by
  unfold outerQuotient
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg, MulChar.pow_apply' _ hk]

theorem bareCongruenceCoefficient_prime_power_pos (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (n k j : ℕ) (hk : k≠0) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k j := by
  unfold bareCongruenceCoefficient congruenceCoefficient
  rw [positiveScalar, if_neg hk]
  apply tsum_congr
  intro d
  rw [outerQuotient_prime_power p hg k hk]
  split_ifs with hd
  · rw [rawFourier_outer, sexticGauss_prime_power p hp hg]
  · ring

lemma sexticGauss_one (H : O) : sexticGauss 1 one_ne_zero H=1 := by
  let : Subsingleton (O ⧸ Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one]
    infer_instance
  let : Unique (O ⧸ Ideal.span {(1:O)}) := uniqueOfSubsingleton 0
  let : Fintype (O ⧸ Ideal.span {(1:O)}) := Fintype.ofFinite _
  unfold sexticGauss
  have ht (d : O ⧸ Ideal.span {(1:O)}) :
      primitiveTrace 1 one_ne_zero (Ideal.Quotient.mk _ H*d)=1 := by
    rw [Subsingleton.elim (Ideal.Quotient.mk _ H*d) 0, AddChar.map_zero_eq_one]
  have hrow (d : O ⧸ Ideal.span {(1:O)}) :
      idealRowHom (Quotient.out d) (Ideal.span {(1:O)}) = 1 := by
    exact (congrArg (idealRowHom (Quotient.out d))
      (Ideal.span_singleton_one.trans Ideal.one_eq_top.symm)).trans (map_one _)
  simp only [hrow, ht, one_mul, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_unique, one_smul]

lemma barePhysicalFourier_outer_one (A : O) (hA : A≠0) (H : O) :
    barePhysicalFourier A 1 hA one_ne_zero H = sexticGauss A hA H := by
  unfold barePhysicalFourier
  rw [elementFourier_congr (A*1) A (mul_ne_zero hA one_ne_zero) hA _ H (mul_one A)]
  simp only [sexticGauss_one, mul_one]
  rfl

lemma bareCongruenceCoefficient_outer_one (A : O) (hA : A≠0) (H : O) :
    bareCongruenceCoefficient A 1 hA H=sexticGauss A hA H := by
  have he := barePhysicalFourier_eq A 1 hA one_ne_zero H
  rw [barePhysicalFourier_outer_one] at he
  simpa only [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, Nat.cast_one, one_mul] using he.symm

theorem bareCongruenceCoefficient_prime_power (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p}) (n k j : ℕ) :
    bareCongruenceCoefficient (p^(n+1)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) n k j := by
  by_cases hk : k=0
  · subst k
    rw [pow_zero, bareCongruenceCoefficient_outer_one, sexticGauss_prime_power p hp hg,
      positiveScalar_kzero]
  · exact bareCongruenceCoefficient_prime_power_pos p hp hg n k j hk

theorem bareCongruenceCoefficient_inner_one (s : O) (hs : s≠0) (H : O) :
    bareCongruenceCoefficient 1 s one_ne_zero H = outerQuotient s (Ideal.Quotient.mk _ H) := by
  let := finiteEisensteinQuotientOfNonzero hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  have htest (d : O ⧸ Ideal.span {s}) :
      s∣H-1*representative s d ↔ d=Ideal.Quotient.mk _ H := by
    rw [one_mul, ← Ideal.mem_span_singleton, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      representative_spec, eq_comm]
  have hraw (k : O) : rawFourier 1 one_ne_zero (outerQuotient 1) k=1 := by
    rw [rawFourier_outer, sexticGauss_one]
  unfold bareCongruenceCoefficient congruenceCoefficient
  simp_rw [hraw]
  simp only [tsum_fintype]
  rw [Finset.sum_eq_single (Ideal.Quotient.mk _ H)]
  · rw [dif_pos ((htest _).mpr rfl), mul_one]
  · intro d hd hne
    rw [dif_neg ((htest d).not.mpr hne), mul_zero]
  · simp

end ProbePhysical
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePrimePower
open Eisenstein CompletedGauss   CubicEisenstein
local notation "O" => Eisenstein.O

lemma complexSexticChar_six (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) : complexSexticChar P hg ^ 6 = 1 :=
  (complexSexticChar_pow_eq_one_iff P hg hc 6).mpr (by decide)

lemma complexSexticChar_neg_one_sq (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) : complexSexticChar P hg (-1)^2 = 1 := by
  rw [← map_pow]
  norm_num

lemma complexSexticChar_pow_six_mul_add (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) (r j : ℕ) :
    complexSexticChar P hg ^ (6*r+j) = complexSexticChar P hg ^ j := by
  rw [pow_add, pow_mul, complexSexticChar_six P hg hc, one_pow, one_mul]

lemma complexSexticChar_fifth_inverse (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hc : ringChar (O ⧸ P) ≠ 2) :
    complexSexticChar P hg ^ 5 = (complexSexticChar P hg)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact complexSexticChar_six P hg hc

lemma primeGauss_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) :
    primeGauss p hp χ 1 * primeGauss p hp χ⁻¹ 1 =
      χ (-1) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have ht := ProbeGauss.gauss_inverse_pair χ (primitiveTrace p hp) hχ
    (residueTraceQuotientChar_primitive p hp)
  have hcard : Nat.card (O ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := rfl
  simpa only [primeGauss, tsum_fintype, map_one, one_mul, gaussSum,
    ← Nat.card_eq_fintype_card, hcard] using ht

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePrimePower
open Eisenstein CompletedGauss 
local notation "O" => Eisenstein.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem unramified_even_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r+5) 0 (6*m) =
      if r+1 ≤ m then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else 0 := by
  rw [positiveScalar_kzero, complexSexticChar_primePowerGauss_at_pow p hp hg hc,
    if_pos (by omega : 6 ∣ 6*r+5+1)]
  by_cases hm : r+1 ≤ m
  · rw [if_pos hm, if_pos (by omega), if_pos (by omega), pow_succ]
    ring
  · rw [if_neg hm, if_neg (by omega), if_neg (by omega), sub_self]

theorem unramified_squarefree_kzero (r m : ℕ) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r) 0 (6*m) =
      if m=r then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) *
        primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 else 0 := by
  rw [positiveScalar_kzero, complexSexticChar_primePowerGauss_at_pow p hp hg hc,
    if_neg (by omega : ¬6 ∣ 6*r+1), complexSexticChar_pow_six_mul_add _ hg hc, pow_one]
  by_cases hm : m=r
  · rw [if_pos hm, if_pos (by omega)]
  · rw [if_neg hm, if_neg (by omega)]

theorem unramified_squarefree_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r) 1 (6*m) =
      if r< m then
        ((complexSexticChar (Ideal.span {p}) hg (-1))⁻¹ *
          primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1) *
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r) * ((Ideal.absNorm (Ideal.span {p}):ℂ)-1))
      else 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  rw [if_neg (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : r< m
  · rw [if_pos ⟨rfl, by omega⟩, if_pos hm, gaussValuationTable,
      if_pos (by omega : 6 ∣ 6*r), if_pos (by omega), if_pos (by omega), pow_succ]
    ring
  · rw [if_neg hm]
    by_cases hm0 : m=0
    · subst m
      rw [if_neg (by omega)]
    · rw [if_pos ⟨rfl, by omega⟩, gaussValuationTable,
        if_pos (by omega : 6 ∣ 6*r), if_neg (by omega), if_neg (by omega), sub_self, mul_zero]

theorem unramified_odd_zero (r m k : ℕ) (d : ℕ) (hd : d=2 ∨ d=3) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r+d) k (6*m) = 0 := by
  rw [positiveScalar_actual_table p hp hg hc]
  split_ifs with hk hk1
  · rw [gaussValuationTable, if_neg (by rcases hd with rfl | rfl <;> omega),
      if_neg (by rcases hd with rfl | rfl <;> omega)]
  · rw [gaussValuationTable, if_neg (by rcases hd with rfl | rfl <;> omega),
      if_neg (by rcases hd with rfl | rfl <;> omega), mul_zero]
  · rfl

theorem unramified_even_kone (r m : ℕ) :
    positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (6*r+5) 1 (6*m) =
      if m=r+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+6) else 0 := by
  rw [positiveScalar_actual_table p hp hg hc, if_neg (by decide : (1:ℕ) ≠ 0)]
  by_cases hm : m=r+1
  · subst m
    rw [if_pos ⟨rfl, by omega⟩, if_pos rfl, gaussValuationTable,
      if_neg (by omega : ¬6 ∣ 6*r+5), if_pos (by omega),
      complexSexticChar_pow_six_mul_add _ hg hc, complexSexticChar_fifth_inverse _ hg hc]
    have hχ : complexSexticChar (Ideal.span {p}) hg ≠ 1 := by
      intro h
      have hpow : complexSexticChar (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
      have hdiv := (complexSexticChar_pow_eq_one_iff _ hg hc 1).mp hpow
      norm_num at hdiv
    have hi := primeGauss_inverse_pair p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) hχ
    have hω : complexSexticChar (Ideal.span {p}) hg (-1) ≠ 0 :=
      (complexSexticChar (Ideal.span {p}) hg).apply_ne_zero_iff.mpr (isUnit_one.neg : IsUnit (-1 : O ⧸ Ideal.span {p}))
    calc
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) *
          ((complexSexticChar (Ideal.span {p}) hg (-1))⁻¹ *
            (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 *
              primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg)⁻¹ 1)) := by ring
      _ = (Ideal.absNorm (Ideal.span {p}):ℂ)^(6*r+5) * (Ideal.absNorm (Ideal.span {p}):ℂ) := by
        rw [hi]
        field_simp
      _ = _ := (pow_succ _ (6*r+5)).symm
  · rw [if_neg hm]
    by_cases hm0 : m=0
    · subst m
      rw [if_neg (by omega)]
    · rw [if_pos ⟨rfl, by omega⟩, gaussValuationTable,
        if_neg (by omega : ¬6 ∣ 6*r+5), if_neg (by omega), mul_zero]

end ProbePrimePower
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

lemma even_diagonal_exponent (r : ℕ) : r + (2*r).choose 2 = 2*r*r := by
  rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  cases r with
  | zero => simp
  | succ r =>
    rw [show 2*(r+1)-1 = 2*r+1 by omega]
    ring

def localCubePhase (C omega : ℂ) (e l k : ℕ) : ℂ :=
  C ^ l * omega^((e+3*l)*k+e*l+l.choose 2)

theorem localCubePhase_even (C omega : ℂ) (hC : C ^ 2=omega) (ho : omega^2=1)
    (e r k : ℕ) : localCubePhase C omega e (2*r) k = omega^(e*k) := by
  unfold localCubePhase
  rw [pow_mul C 2 r, hC, ← pow_add]
  have he : r+((e+3*(2*r))*k+e*(2*r)+(2*r).choose 2) =
      e*k+2*(3*r*k+e*r+r*r) := by
    have hd := even_diagonal_exponent r
    nlinarith only [hd]
  rw [he, pow_add, pow_mul omega 2, ho, one_pow, mul_one]

def weightedScalar (Q eta a G1 C omega X W V scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (-eta*X/G1)^e * (a*X^3/Q)^l * localCubePhase C omega e l k * scalar * W^k * V^m

lemma weightedScalar_zero (Q eta a G1 C omega X W V : ℂ) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V 0 e l k m = 0 := by
  simp [weightedScalar]

def evenRatio (Q a X V : ℂ) : ℂ := a^2*Q^4*X^6*V

lemma weighted_squarefree_boundary (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C ^ 2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r)*G1) 1 (2*r) 0 r =
      evenRatio Q a X V ^ r * (-eta*X) := by
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [mul_zero, pow_zero, pow_one, mul_one]
  unfold evenRatio
  rw [mul_pow, mul_pow, mul_pow, div_pow, mul_pow, pow_mul, pow_mul, pow_mul, pow_mul]
  field_simp
  ring

lemma weighted_even_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C ^ 2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+5)*(Q-1))
      0 (2*r+2) 0 (r+1+d) =
      evenRatio Q a X V ^ r * (evenRatio Q a X V*(1-Q⁻¹)*V^d) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [zero_mul, pow_zero, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_even_kone (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C ^ 2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+6))
      0 (2*r+2) 1 (r+1) = evenRatio Q a X V ^ r * (W*evenRatio Q a X V) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_squarefree_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C ^ 2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V
      ((omega⁻¹*G1)*(Q^(6*r)*(Q-1))) 1 (2*r) 1 (r+1+d) =
      evenRatio Q a X V ^ r * (-eta*(Q-1)*X*W*V^(d+1)) := by
  have hω : omega ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at ho; norm_num at ho
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [one_mul, pow_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson

namespace ProbePrimePower
local notation "O" => Eisenstein.O

/-- The prime trace Gauss sum divided by the square root of its residue-field size. -/
def localGamma (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (r : ℕ) : ℂ :=
  primeGauss p hp (complexSexticChar (Ideal.span {p}) hg ^ r) 1 /
    (Real.sqrt (Ideal.absNorm (Ideal.span {p})) : ℂ)

lemma localGamma_norm_one (p : O) (hp : p ≠ 0) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) : ‖localGamma p hp hg r‖ = 1 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hχ : complexSexticChar (Ideal.span {p}) hg ^ r ≠ 1 := by
    intro he
    have hd := (complexSexticChar_pow_eq_one_iff _ hg hc r).mp he
    exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr) hr6) hd
  have he := ProbeGauss.normalizedGauss_norm
    (complexSexticChar (Ideal.span {p}) hg ^ r) (primitiveTrace p hp) hχ
    (residueTraceQuotientChar_primitive p hp)
  have hcard : Nat.card (O ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := rfl
  simpa only [localGamma, ProbeGauss.normalizedGauss, primeGauss, tsum_fintype,
    map_one, one_mul, gaussSum, ← Nat.card_eq_fintype_card, hcard] using he

/-- Complementary sextic powers pair to the character evaluated at minus one. -/
theorem localGamma_inverse_pair (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (r : ℕ) (hr : r ≠ 0) (hr6 : r < 6) :
    localGamma p hp hg r * localGamma p hp hg (6-r) =
      complexSexticChar (Ideal.span {p}) hg (-1)^r := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := complexSexticChar (Ideal.span {p}) hg
  have hχ : χ^r ≠ 1 := by
    intro he
    have hd := (complexSexticChar_pow_eq_one_iff _ hg hc r).mp he
    exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hr) hr6) hd
  have hinv : (χ^r)⁻¹ = χ^(6-r) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, Nat.add_sub_of_le hr6.le]
    exact complexSexticChar_six _ hg hc
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ^r) (primitiveTrace p hp) hχ
    (residueTraceQuotientChar_primitive p hp)
  rw [hinv] at he
  have hcard : Nat.card (O ⧸ Ideal.span {p}) = Ideal.absNorm (Ideal.span {p}) := rfl
  simpa only [localGamma, ProbeGauss.normalizedGauss, primeGauss, tsum_fintype,
    map_one, one_mul, gaussSum, ← Nat.card_eq_fintype_card, hcard,
    MulChar.pow_apply' _ hr] using he

lemma localGamma_two_four (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    localGamma p hp hg 2 * localGamma p hp hg 4 = 1 := by
  have he := localGamma_inverse_pair p hp hg hc 2 (by decide) (by decide)
  simpa only [show 6-2=4 from rfl, complexSexticChar_neg_one_sq] using he

lemma localGamma_three_sq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    localGamma p hp hg 3 ^ 2 = complexSexticChar (Ideal.span {p}) hg (-1) := by
  have he := localGamma_inverse_pair p hp hg hc 3 (by decide) (by decide)
  have hcube : complexSexticChar (Ideal.span {p}) hg (-1)^3 =
      complexSexticChar (Ideal.span {p}) hg (-1) := by
    rw [pow_succ, complexSexticChar_neg_one_sq, one_mul]
  simpa only [show 6-3=3 from rfl, ← pow_two, hcube] using he

end ProbePrimePower
end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalMarkedTerm (eta a X W V : ℂ) (e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (complexSexticChar (Ideal.span {p}) hg (-1)) X W V
      (positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (e+3*l-1) k (6*m)) e l k m

include hc in
lemma localGamma_conjugate_three_sq :
    (star (localGamma p hp.ne_zero hg 3))^2 = complexSexticChar (Ideal.span {p}) hg (-1) := by
  have hg3 : localGamma p hp.ne_zero hg 3 ^ 2 = complexSexticChar (Ideal.span {p}) hg (-1) :=
    localGamma_three_sq p hp.ne_zero hg hc
  rw [← star_pow, hg3]
  have hω := complexSexticChar_neg_one_sq (Ideal.span {p}) hg
  rcases (sq_eq_one_iff).mp hω with h | h
  · simp [h]
  · simp [h]

include hc in
lemma firstGauss_ne_zero : primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 ≠ 0 := by
  have hχ : complexSexticChar (Ideal.span {p}) hg ≠ 1 := by
    intro h
    have he : complexSexticChar (Ideal.span {p}) hg ^ 1 = 1 := by simpa using h
    have hd := (complexSexticChar_pow_eq_one_iff _ hg hc 1).mp he
    norm_num at hd
  have he := primeGauss_inverse_pair p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) hχ
  have hω : complexSexticChar (Ideal.span {p}) hg (-1) ≠ 0 :=
    (complexSexticChar (Ideal.span {p}) hg).apply_ne_zero_iff.mpr isUnit_one.neg
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  intro hz
  rw [hz, zero_mul] at he
  exact (mul_ne_zero hω hQ) he.symm

omit [(Ideal.span {p}).IsMaximal] in
include hp in
lemma primeNorm_ne_zero : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
  exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)

include hc

omit hc in
@[simp] theorem markedTerm_zero_index (eta a X W V : ℂ) (k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 0 k m = 0 := by
  simp only [principalMarkedTerm, mul_zero, add_zero, ite_true]

omit hc in
lemma markedTerm_higher_outer (eta a X W V : ℂ) (e l k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V e l (k+2) m = 0 := by
  unfold principalMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp, weightedScalar_zero]

lemma markedTerm_odd (eta a X W V : ℂ) (e r k m : ℕ) (he : e ≤ 1) :
    principalMarkedTerm p hp hg eta a X W V e (2*r+1) k m = 0 := by
  unfold principalMarkedTerm
  rw [if_neg (by omega)]
  have hn : e+3*(2*r+1)-1 = 6*r+(e+2) := by omega
  rw [hn, unramified_odd_zero p hp hg hc r m k (e+2) (by omega), weightedScalar_zero]

lemma markedTerm_squarefree_boundary (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 r =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X) := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, if_pos rfl]
  exact weighted_squarefree_boundary _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (complexSexticChar_neg_one_sq _ hg) r

lemma markedTerm_squarefree_boundary_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kzero p hp hg hc, if_neg hm, weightedScalar_zero]

lemma markedTerm_even_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*V^d) := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, if_pos (by omega)]
  exact weighted_even_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (complexSexticChar_neg_one_sq _ hg) r d

lemma markedTerm_even_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m = 0 := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kzero p hp hg hc, if_neg (by omega), weightedScalar_zero]

lemma markedTerm_even_kone (eta a X W V : ℂ) (r : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 (r+1) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, if_pos rfl]
  exact weighted_even_kone _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (complexSexticChar_neg_one_sq _ hg) r

lemma markedTerm_even_kone_off (eta a X W V : ℂ) (r m : ℕ) (hm : m ≠ r+1) :
    principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 0+3*(2*r+2)-1=6*r+5 by omega,
    unramified_even_kone p hp hg hc, if_neg hm, weightedScalar_zero]

lemma markedTerm_squarefree_bulk (eta a X W V : ℂ) (r d : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 (r+1+d) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V^(d+1)) := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, if_pos (by omega)]
  exact weighted_squarefree_bulk _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (firstGauss_ne_zero p hp hg hc) (localGamma_conjugate_three_sq p hp hg hc)
    (complexSexticChar_neg_one_sq _ hg) r d

lemma markedTerm_squarefree_bulk_off (eta a X W V : ℂ) (r m : ℕ) (hm : m < r+1) :
    principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m = 0 := by
  unfold principalMarkedTerm
  rw [if_neg (by omega), show 1+3*(2*r)-1=6*r by omega,
    unramified_squarefree_kone p hp hg hc, if_neg (by omega), weightedScalar_zero]

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

lemma hasSum_geometric_tail (f : ℕ → ℂ) (a : ℕ) (B V : ℂ) (hV : ‖V‖<1)
    (hz : ∀ m, m< a → f m=0) (hf : ∀ n, f (n+a)=B*V^n) :
    HasSum f (B/(1-V)) := by
  have ht : HasSum (fun n => f (n+a)) (B/(1-V)) := by
    simpa only [hf, div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hV).mul_left B
  have hs : (∑ i ∈ Finset.range a, f i) = 0 :=
    Finset.sum_eq_zero (fun i hi => hz i (Finset.mem_range.mp hi))
  simpa only [hs, zero_add] using ht.sum_range_add

lemma tsum_two_of_rest_zero (f : ℕ → ℂ) (hf : ∀ k, f (k+2)=0) :
    (∑' k, f k) = f 0+f 1 := by
  rw [tsum_eq_sum (s := {0,1})]
  · simp
  · intro k hk
    have hk2 : 2 ≤ k := by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk; omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hk2
    simpa only [Nat.add_comm] using hf k

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalInner (eta a X W V : ℂ) (e l : ℕ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ, principalMarkedTerm p hp hg eta a X W V e l k m

include hc

lemma squarefree_boundary_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r * (-eta*X)) := by
  apply (hasSum_ite_eq r _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r
  · subst m
    rw [if_pos rfl, markedTerm_squarefree_boundary p hp hg hc]
  · rw [if_neg hm, markedTerm_squarefree_boundary_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_kone_hasSum (eta a X W V : ℂ) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply (hasSum_ite_eq (r+1) _).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hmS
  dsimp only
  by_cases hm : m=r+1
  · subst m
    rw [if_pos rfl, markedTerm_even_kone p hp hg hc]
  · rw [if_neg hm, markedTerm_even_kone_off p hp hg hc _ _ _ _ _ _ _ hm]

lemma even_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 0 (2*r+2) 0 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_even_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_even_bulk p hp hg hc]
    ring

lemma squarefree_bulk_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    HasSum (fun m => principalMarkedTerm p hp hg eta a X W V 1 (2*r) 1 m)
      (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V) / (1-V)) := by
  apply hasSum_geometric_tail _ (r+1) _ V hV
  · exact markedTerm_squarefree_bulk_off p hp hg hc eta a X W V r
  · intro n
    rw [Nat.add_comm n (r+1), markedTerm_squarefree_bulk p hp hg hc, pow_succ]
    ring

omit hc in
lemma principalInner_two (eta a X W V : ℂ) (e l : ℕ) :
    principalInner p hp hg eta a X W V e l =
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 0 m) +
      (∑' m, principalMarkedTerm p hp hg eta a X W V e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [markedTerm_higher_outer p hp hg, tsum_zero]

lemma principalInner_squarefree (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 1 (2*r) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (-eta*X - eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) := by
  rw [principalInner_two p hp hg, (squarefree_boundary_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq,
    (squarefree_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq]
  ring

lemma principalInner_even (eta a X W V : ℂ) (hV : ‖V‖<1) (r : ℕ) :
    principalInner p hp hg eta a X W V 0 (2*r+2) =
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V ^ r *
        (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  rw [principalInner_two p hp hg, (even_bulk_hasSum p hp hg hc _ _ _ _ _ hV r).tsum_eq,
    (even_kone_hasSum p hp hg hc _ _ _ _ _ r).tsum_eq]
  ring

lemma principalInner_odd (eta a X W V : ℂ) (e r : ℕ) (he : e≤1) :
    principalInner p hp hg eta a X W V e (2*r+1) = 0 := by
  simp only [principalInner, markedTerm_odd p hp hg hc _ _ _ _ _ e r _ _ he, tsum_zero]

omit hc in
@[simp] lemma principalInner_zero (eta a X W V : ℂ) :
    principalInner p hp hg eta a X W V 0 0 = 0 := by
  simp only [principalInner, markedTerm_zero_index p hp hg, tsum_zero]

lemma principalInner_squarefree_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 1 l)
      ((-eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := -eta*X-eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W*V/(1-V)
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r))
      ((1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)⁻¹ * B) := by
    simpa only [principalInner_squarefree p hp hg hc eta a X W V hV, B] using
      (hasSum_geometric_of_norm_lt_one hR).mul_right B
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 1 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 1 _ (by omega)]
    exact hasSum_zero
  convert he.even_add_odd ho using 1 <;> first | rfl | (simp only [add_zero, div_eq_mul_inv, B]; ring)

lemma principalInner_even_hasSum (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    HasSum (fun l => principalInner p hp hg eta a X W V 0 l)
      ((evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) /
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  let B := evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
          (1-(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)/(1-V) +
          W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V
  have he : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r))
      (B/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    apply hasSum_geometric_tail _ 1 B _ hR
    · intro m hm
      have hm0 : m=0 := by omega
      simp [hm0, principalInner_zero p hp hg]
    · intro r
      rw [show 2*(r+1)=2*r+2 by ring, principalInner_even p hp hg hc _ _ _ _ _ hV]
      ring
  have ho : HasSum (fun r => principalInner p hp hg eta a X W V 0 (2*r+1)) 0 := by
    simp only [principalInner_odd p hp hg hc eta a X W V 0 _ (by omega)]
    exact hasSum_zero
  simpa only [add_zero, B] using he.even_add_odd ho

def principalMarkedSeries (eta a X W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, principalInner p hp hg eta a X W V e.val l

theorem principalMarkedSeries_eq (eta a X W V : ℂ) (hV : ‖V‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    principalMarkedSeries p hp hg eta a X W V =
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-eta*X+W*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  unfold principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [(principalInner_even_hasSum p hp hg hc eta a X W V hV hR).tsum_eq,
    (principalInner_squarefree_hasSum p hp hg hc eta a X W V hV hR).tsum_eq]
  unfold markedFactor
  simp only [pow_one]
  ring

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

lemma evenRatio_eq_coordR (Q : ℝ) (hQ : 0< Q) (a x z : ℂ) :
    evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z) = coordR Q (a^2) x z := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold evenRatio coordR coordV
  calc
    _ = a^2 * ((Q:ℂ)^4 * ((Q:ℂ)^(-x))^6 * (Q:ℂ)^(-6*z)) := by ring
    _ = a^2 * ((Q:ℂ)^(4:ℂ) * (Q:ℂ)^((6:ℂ)*(-x)) * (Q:ℂ)^(-6*z)) := by
      rw [Complex.cpow_ofNat]
      have h6 : (Q:ℂ)^((6:ℂ)*(-x)) = ((Q:ℂ)^(-x))^6 := by
        simpa using Complex.cpow_nat_mul (Q:ℂ) 6 (-x)
      rw [h6]
    _ = a^2 * (Q:ℂ)^((4:ℂ)+6*(-x)+(-6*z)) := by
      rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
    _ = _ := by congr 2; ring

lemma coordK_eq_geometric (Q : ℝ) (hQ : 0< Q) (eta x w : ℂ) :
    coordK Q eta x w = eta*((Q:ℂ)-1)*((Q:ℂ)^(-x))*((Q:ℂ)^(-w)) := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold coordK
  rw [show -x-w = -x+(-w) by ring, Complex.cpow_add _ _ hn]
  ring

lemma one_sub_ne_zero_of_norm_lt_one (a : ℂ) (ha : ‖a‖<1) : 1-a ≠ 0 := by
  intro h
  have he : a=1 := by linear_combination -h
  rw [he, norm_one] at ha
  exact lt_irrefl _ ha

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalFullSeries (eta a X W V : ℂ) : ℂ :=
  1/(1-V)+W/(1-W)+principalMarkedSeries p hp hg eta a X W V

include hc

theorem principalFullSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  dsimp only
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simp only [Complex.ofReal_natCast]
  have hratio := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hratio
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hratio]
    exact hR
  rw [principalFullSeries, principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV hr,
    hratio]
  unfold unramifiedClosed
  dsimp only
  rw [coordK_eq_geometric _ hQ]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [coordW, coordD, star_one, mul_one, one_mul, Complex.ofReal_natCast] at hD hw ⊢
  unfold ProbeLocal.continuedCorrection
  field_simp [hD, hv, hw]
  ring

omit hc

def actualACube (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (CompletedGauss.angularFactor p)^3 * HeckeFamily.elementCoeff eta p^3

lemma actualACube_sq (eta : HeckeFamily.Character) (p : O) :
    actualACube eta p ^ 2 = actualAPhase eta p := by
  unfold actualACube actualAPhase
  ring

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

lemma signed_diagonal_phase (omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    omega^(((e+3*l)*k:ℕ):ℤ) * omega^(-((e*l+l.choose 2:ℕ):ℤ)) =
      omega^((e+3*l)*k+e*l+l.choose 2) := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  have hi : omega⁻¹=omega := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using ho
  rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, hi, ← pow_add]
  congr 1
  omega

lemma source_signed_phase (C omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    C ^ l * omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) =
      localCubePhase C omega e l k := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  rw [sub_eq_add_neg, zpow_add₀ hn, signed_diagonal_phase omega ho]
  rfl

lemma spectral_power_split (Q : ℝ) (hQ : 0< Q) (x w z : ℂ) (e l k m : ℕ) :
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
      ((Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ))^e *
      (((Q:ℂ)^(-x))^3/(Q:ℂ))^l * ((Q:ℂ)^(-w))^k * ((Q:ℂ)^(-6*z))^m := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have h1 : (Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ) = (Q:ℂ)^(-x-(1/2:ℂ)) :=
    (Complex.cpow_sub _ _ hn).symm
  have h3 : ((Q:ℂ)^(-x))^3/(Q:ℂ) = (Q:ℂ)^(-1-3*x) := by
    rw [← Complex.cpow_nat_mul (Q:ℂ) 3 (-x)]
    calc
      _ = (Q:ℂ)^(3*(-x)) / (Q:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]; norm_num
      _ = (Q:ℂ)^(3*(-x)-1) := (Complex.cpow_sub _ _ hn).symm
      _ = _ := by congr 1; ring
  rw [h1, h3, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
  congr 1
  ring

lemma cpow_half_eq_sqrt (Q : ℝ) (hQ : 0≤ Q) :
    (Q:ℂ)^(1/2:ℂ) = (Real.sqrt Q:ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hQ (1/2:ℝ)).symm

def sourceWeightedScalar (Q : ℝ) (eta a gamma1 C omega x w z scalar : ℂ)
    (e l k m : ℕ) : ℂ :=
  (-1:ℂ)^e * gamma1^(-(e:ℤ)) * eta^e * (a*C)^l *
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) * scalar *
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ))

theorem sourceWeightedScalar_eq (Q : ℝ) (hQ : 0< Q)
    (eta a gamma1 G1 C omega x w z scalar : ℂ) (hG : G1=gamma1*(Real.sqrt Q:ℂ))
    (ho : omega^2=1) (e l k m : ℕ) :
    sourceWeightedScalar Q eta a gamma1 C omega x w z scalar e l k m =
      weightedScalar Q eta a G1 C omega ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w))
        ((Q:ℂ)^(-6*z)) scalar e l k m := by
  unfold sourceWeightedScalar weightedScalar
  rw [spectral_power_split Q hQ, cpow_half_eq_sqrt Q hQ.le]
  rw [zpow_neg, zpow_natCast]
  have hphase := source_signed_phase 1 omega ho e l k
  simp only [localCubePhase, one_pow, one_mul] at hphase
  unfold localCubePhase
  rw [hphase, mul_pow a C, hG]
  simp only [mul_pow, div_pow]

  ring

open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

lemma firstGauss_eq_gamma_sqrt (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p}) :
    primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1 =
      localGamma p hp.ne_zero hg 1 *
        (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hs : (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  simp only [localGamma, pow_one, div_mul_cancel₀ _ hs]

theorem sourceWeightedScalar_actual (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p})
    (eta a x w z scalar : ℂ) (e l k m : ℕ) :
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (complexSexticChar (Ideal.span {p}) hg (-1)) x w z scalar e l k m =
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (complexSexticChar (Ideal.span {p}) hg (-1))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-6*z)) scalar e l k m := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simpa only [Complex.ofReal_natCast] using
    sourceWeightedScalar_eq _ hQ eta a (localGamma p hp.ne_zero hg 1) _
      (star (localGamma p hp.ne_zero hg 3)) (complexSexticChar (Ideal.span {p}) hg (-1))
      x w z scalar (firstGauss_eq_gamma_sqrt p hp hg)
      (complexSexticChar_neg_one_sq _ hg) e l k m

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]

def zeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(6*m)))) * W^k * V^m

omit [(Ideal.span {p}).IsMaximal] in
lemma zeroIndex_inner_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hV : ‖V‖<1) :
    HasSum (fun m => zeroIndexTerm p χ W V 0 m) (1/(1-V)) := by
  simpa [zeroIndexTerm, one_div] using hasSum_geometric_of_norm_lt_one hV

include hp in
lemma zeroIndex_inner_pos (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (k : ℕ) (hk : k≠0) :
    HasSum (fun m => zeroIndexTerm p χ W V k m) (W^k) := by
  apply (hasSum_ite_eq 0 (W^k)).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  unfold zeroIndexTerm
  rw [if_neg hk, zero_index_scalar p hp χ k (6*m) hk]
  by_cases h : m=0
  · subst m; simp
  · have h6 : 6*m≠0 := by omega
    simp [h, h6]

def zeroIndexSeries (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) : ℂ :=
  ∑' k, ∑' m, zeroIndexTerm p χ W V k m

include hp in
lemma zeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hW : ‖W‖<1) (hV : ‖V‖<1) :
    zeroIndexSeries p χ W V = 1/(1-V)+W/(1-W) := by
  have htail : HasSum (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) (W/(1-W)) := by
    have he : (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) =
        (fun k => W * W^k) := by
      funext k
      rw [(zeroIndex_inner_pos p hp χ W V (k+1) (by omega)).tsum_eq, pow_succ]
      ring
    rw [he]
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hW).mul_left W
  have hall := HasSum.sum_range_add (f := fun k => ∑' m, zeroIndexTerm p χ W V k m) (k := 1) htail
  simpa only [zeroIndexSeries, Finset.sum_range_one,
    (zeroIndex_inner_zero p χ W V hV).tsum_eq] using hall.tsum_eq

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def sourceScalar (t k j : ℕ) : ℂ :=
  if t=0 then
    if k=0 then 1 else (complexSexticChar (Ideal.span {p}) hg ^ k) (Ideal.Quotient.mk _ (p^j))
  else positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) (t-1) k j

def sourcePrincipalTerm (eta a x w z : ℂ) (e l k m : ℕ) : ℂ :=
  sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (complexSexticChar (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (6*m)) e l k m

lemma sourcePrincipalTerm_pos (eta a x w z : ℂ) (e l k m : ℕ) (ht : e+3*l≠0) :
    sourcePrincipalTerm p hp hg eta a x w z e l k m =
      principalMarkedTerm p hp hg eta a
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) e l k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [sourceScalar, ht, ite_false, principalMarkedTerm, coordV, Complex.ofReal_natCast]

lemma sourcePrincipalTerm_zero (eta a x w z : ℂ) (k m : ℕ) :
    sourcePrincipalTerm p hp hg eta a x w z 0 0 k m =
      zeroIndexTerm p (complexSexticChar (Ideal.span {p}) hg)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [weightedScalar, localCubePhase, sourceScalar, zeroIndexTerm, coordV,
    mul_zero, add_zero, pow_zero,  one_mul, zero_mul, Nat.choose_zero_succ,
    ite_true, Complex.ofReal_natCast]

def sourcePrincipalSeries (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z e.val l k m

include hc in
lemma sourcePrincipalSeries_eq (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) := by
  dsimp only
  simp only [Complex.ofReal_natCast]
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1 := by
    have he := evenRatio_eq_coordR _ hQ a x z
    simp only [Complex.ofReal_natCast] at he
    change ‖evenRatio _ a _ _‖<1
    rw [he]
    exact hR
  have hW' : ‖W‖<1 := by simpa only [W, coordW, one_mul, Complex.ofReal_natCast] using hW
  have he : Summable (fun l => principalInner p hp hg eta a X W V 0 l) :=
    (principalInner_even_hasSum p hp hg hc eta a X W V hV hr).summable
  have h0 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 0 l k m) =
      (fun l => principalInner p hp hg eta a X W V 0 l +
        if l=0 then zeroIndexSeries p (complexSexticChar (Ideal.span {p}) hg) W V else 0) := by
    funext l
    by_cases hl : l=0
    · subst l
      simp only [sourcePrincipalTerm_zero, principalInner_zero p hp hg,  ite_true,
        zero_add, zeroIndexSeries, W, V]
    · rw [if_neg hl, add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourcePrincipalTerm_pos p hp hg eta a x w z 0 l k m (by omega)
  have h1 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 1 l k m) =
      (fun l => principalInner p hp hg eta a X W V 1 l) := by
    funext l
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourcePrincipalTerm_pos p hp hg eta a x w z 1 l k m (by omega)
  unfold sourcePrincipalSeries principalFullSeries principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [h0, h1, he.tsum_add (hasSum_ite_eq 0 _).summable, tsum_ite_eq]
  rw [zeroIndexSeries_eq p hp _ W V hW' hV]
  change _ = 1/(1-V)+W/(1-W)+((∑' l, principalInner p hp hg eta a X W V 0 l)+
    ∑' l, principalInner p hp hg eta a X W V 1 l)
  ring

include hc in

theorem sourcePrincipalSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [sourcePrincipalSeries_eq p hp hg hc eta a x w z hV hR hW]
  exact principalFullSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD

end ProbeEuler
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein CompletedGauss  CanonicalRowCompletion
open CubicEisenstein GaussianShiftedPartition ProbePrimePower ProbeEuler ProbeLocal
local notation "O" => Eisenstein.O

theorem bareCongruenceCoefficient_all_prime_powers (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p}) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      sourceScalar p hp hg t k j := by
  cases t with
  | zero =>
    simp only [pow_zero]
    rw [bareCongruenceCoefficient_inner_one _ (pow_ne_zero _ hp.ne_zero), outerQuotient_mk]
    unfold sourceScalar
    rw [if_pos rfl]
    by_cases hk : k=0
    · subst k
      simp only [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, ite_true]
    · rw [if_neg hk, ← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg,
        MulChar.pow_apply' _ hk]
  | succ n =>
    rw [bareCongruenceCoefficient_prime_power p hp hg n k j]
    simp only [sourceScalar, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]

def physicalPrincipalSeries (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (complexSexticChar (Ideal.span {p}) hg (-1)) x w z
      (bareCongruenceCoefficient (p^(e.val+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)))
      e.val l k m

theorem physicalPrincipalSeries_eq (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (eta a x w z : ℂ) :
    physicalPrincipalSeries p hp hg eta a x w z = sourcePrincipalSeries p hp hg eta a x w z := by
  simp only [physicalPrincipalSeries, sourcePrincipalSeries, sourcePrincipalTerm,
    bareCongruenceCoefficient_all_prime_powers p hp hg]

theorem physicalPrincipalSeries_euler_identity (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    physicalPrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [physicalPrincipalSeries_eq]
  exact sourcePrincipalSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion
open SchwartzPlanePoisson CenteredMomentFourier CubicSieve

namespace ProbePrimePower
local notation "O" => Eisenstein.O

lemma norm_eq_sqrt_primeNorm (p : O) :
    ‖ringComplex p‖ = Real.sqrt (Ideal.absNorm (Ideal.span {p})) := by
  rw [← ringComplex_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]

/-- The quadratic member of the local Gauss family is the fixed phase modulo four. -/
lemma localGamma_three_phase (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    localGamma p hp hg 3 = QuadraticPhase.Eisenstein.fixedDualAverage p := by
  let : NeZero p := ⟨hp⟩
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have htwo : (2 : O) ∉ Ideal.span {p} := by
    intro h
    apply Ring.two_ne_zero hc
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hs := SchwartzPlanePoisson.sum_traceChar_mul_sq p htwo (u := 1) one_ne_zero
  simp only [one_mul, MulChar.map_one] at hs
  have hgauss : primeGauss p hp (complexSexticChar (Ideal.span {p}) hg ^ 3) 1 =
      QuadraticPhase.Eisenstein.quadraticTraceGauss p hp := by
    simp only [primeGauss, tsum_fintype, map_one, one_mul, primitiveTrace,
      residueTraceQuotientChar_eq_principal, (complexSexticChar_powers _ hg).2.1]
    rw [SchwartzPlanePoisson.quadraticTraceGauss_eq_sum, hs]
    rfl
  unfold localGamma
  rw [hgauss, ← norm_eq_sqrt_primeNorm]
  exact QuadraticPhase.Eisenstein.normalizedQuadraticTraceGauss_eq_fixedDualAverage p hp

/-- Hasse–Davenport in the native trace normalization. -/
lemma localGamma_sextic_product (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (hprimary : lambda^2 ∣ p-1) :
    complexSexticChar (Ideal.span {p}) hg 4 * localGamma p hp hg 1 *
      localGamma p hp hg 2 = -angularFactor p * localGamma p hp hg 3 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hgen : primaryGenerator (Ideal.span {p}) hg = p :=
    (primaryGenerator_unique _ hg p rfl hprimary).symm
  have h := sextic_cubic_gauss_product (Ideal.span {p}) hg hc (primitiveTrace p hp)
    (residueTraceQuotientChar_primitive p hp)
  rw [hgen, ← (complexSexticChar_powers _ hg).1,
    ← (complexSexticChar_powers _ hg).2.1] at h
  simp only [gaussSum] at h
  have hn : (‖ringComplex p‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (ringComplex_ne_zero hp)
  simp only [localGamma, primeGauss, tsum_fintype, map_one, one_mul, pow_one,
    ← norm_eq_sqrt_primeNorm, angularFactor]
  change _ = -(ringComplex p / (‖ringComplex p‖ : ℂ)) *
    (gaussSum (complexSexticChar (Ideal.span {p}) hg ^ 3) (primitiveTrace p hp) /
      (‖ringComplex p‖ : ℂ))
  simp only [gaussSum]
  field_simp [hn]
  linear_combination h

end ProbePrimePower

namespace ProbePhysical
open ProbePrimePower ProbePhase
local notation "O" => Eisenstein.O

lemma angularFactor_mul_star (p : O) (hp : p ≠ 0) :
    angularFactor p * star (angularFactor p) = 1 := by
  rw [mul_comm, Complex.star_def, Complex.conj_mul', norm_angularFactor p hp]
  norm_num

/-- At a primary prime, the completed cubic row is the second normalized Gauss sum. -/
theorem gaussTwo_prime_localGamma (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p})
    (hprimary : lambda^2 ∣ p-1) (hI : primaryIdealGenerator (Ideal.span {p}) ≠ 0) :
    gaussTwo (Ideal.span {p}) hI = localGamma p hp.ne_zero hg 2 := by
  have hrow : cubicRow (Ideal.span {p}) = fun x =>
      (complexSexticChar (Ideal.span {p}) hg ^ 2) (Ideal.Quotient.mk _ x) := by
    funext x
    unfold cubicRow
    rw [← idealRowHom_square, idealRowHom_prime _ _ hg,
      MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
  unfold gaussTwo localGamma
  simp only [primaryIdealGenerator_span p hp.ne_zero hprimary]
  rw [← norm_eq_sqrt_primeNorm]
  congr 1
  simp only [residueRowGauss, primeGauss, hrow, mk_qrep, map_one, one_mul, primitiveTrace]

/-- The sextic–cubic product has exactly the fixed phase used by the completed source. -/
theorem localGamma_one_two_full_signal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (hprimary : lambda^2 ∣ p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 = -angularFactor p * G p := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finiteEisensteinQuotientOfNonzero hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hgen : primaryGenerator (Ideal.span {p}) hg = p :=
    (primaryGenerator_unique _ hg p rfl hprimary).symm
  have hfour : complexSexticChar (Ideal.span {p}) hg 4 = cubicTwoSupplement p := by
    have he := complexSextic_four_eq_fixed_two (Ideal.span {p}) hg hc
    rw [hgen] at he
    exact he
  have h4 : (4 : O ⧸ Ideal.span {p}) ≠ 0 := by
    rw [show (4 : O ⧸ Ideal.span {p}) = 2^2 by ring]
    exact pow_ne_zero 2 (Ring.two_ne_zero hc)
  have hn : ‖complexSexticChar (Ideal.span {p}) hg 4‖ = 1 :=
    FiniteRayExpansion.norm_char_unit _ (Units.mk0 4 h4)
  have hcancel : star (complexSexticChar (Ideal.span {p}) hg 4) *
      complexSexticChar (Ideal.span {p}) hg 4 = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hn]
    norm_num
  have he := congrArg (fun z : ℂ => star (complexSexticChar (Ideal.span {p}) hg 4) * z)
    (localGamma_sextic_product p hp hg hc hprimary)
  calc
    _ = (star (complexSexticChar (Ideal.span {p}) hg 4) *
        complexSexticChar (Ideal.span {p}) hg 4) *
        localGamma p hp hg 1 * localGamma p hp hg 2 := by rw [hcancel, one_mul]
    _ = -angularFactor p * (star (complexSexticChar (Ideal.span {p}) hg 4) *
        localGamma p hp hg 3) := by linear_combination he
    _ = -angularFactor p * G p := by rw [hfour, localGamma_three_phase p hp hg hc, G_eq]

lemma gaussTwo_one : gaussTwo (1 : Ideal O)
    (by rw [primaryIdealGenerator_one]; exact one_ne_zero) = 1 := by
  have hrow : cubicRow (1 : Ideal O) = fun _ => (1 : ℂ) := by
    funext x
    rw [cubicRow, ← idealRowHom_square, map_one, one_pow]
  simp only [gaussTwo, primaryIdealGenerator_one, map_one, norm_one, Complex.ofReal_one, div_one,
    hrow]
  have he : residueRowGauss 1 one_ne_zero (fun _ => 1) = sexticGauss 1 one_ne_zero 1 := by
    unfold residueRowGauss sexticGauss
    apply tsum_congr
    intro x
    simp only [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, one_mul, primitiveTrace]
  rw [he, sexticGauss_one]

end ProbePhysical
end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein Eisenstein.Coordinates CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve  CubicEisenstein 
open ProbePhase ProbeEuler ProbePrimePower 
local notation "O" => Eisenstein.O

lemma angularFactor_pow (p : O) (n : ℕ) : angularFactor (p^n)=angularFactor p^n := by
  simp only [angularFactor,map_pow,norm_pow,Complex.ofReal_pow,div_pow]

lemma gaussTwo_prime_power_small (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hprimary : lambda^2∣p-1) (e : ℕ) (he : e≤1)
    (hI : primaryIdealGenerator (Ideal.span {p^e})≠0) :
    gaussTwo (Ideal.span {p^e}) hI=localGamma p hp.ne_zero hg 2^e := by
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero,Ideal.span_singleton_one,←Ideal.one_eq_top] using gaussTwo_one
  · have hi : primaryIdealGenerator (Ideal.span {p})≠0 := by simpa only [pow_one] using hI
    simpa only [pow_one] using gaussTwo_prime_localGamma p hp hg hprimary hi

lemma corrected_prime_cubic_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : lambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) :
    localGamma p hp hg 2 * star (angularFactor p) * star (G p) = -(localGamma p hp hg 1)⁻¹ := by
  have hsig := localGamma_one_two_full_signal p hp hg hchar hprimary
  have hn := localGamma_norm_one p hp hg hchar 1 (by decide) (by decide)
  have hne : localGamma p hp hg 1≠0 := by intro h; rw [h,norm_zero] at hn; norm_num at hn
  have hG : G p*star (G p)=1 := by
    rw [mul_comm]
    exact G_conjugate_cancel p (odd_of_supported p hs)
  apply mul_left_cancel₀ hne
  calc
    _ = (localGamma p hp hg 1*localGamma p hp hg 2)*star (angularFactor p)*star (G p) := by ring
    _ = -1 := by
      rw [hsig]
      calc
        _ = -(angularFactor p*star (angularFactor p))*(G p*star (G p)) := by ring
        _ = _ := by rw [angularFactor_mul_star p hp,hG]; ring
    _ = _ := by rw [mul_neg,mul_inv_cancel₀ hne]

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion
open SchwartzPlanePoisson

namespace ProbePhase
open ProbePrimePower QuadraticPhase.Eisenstein
local notation "O" => Eisenstein.O

/-- The self-reciprocity sign is the sextic character at minus one. -/
lemma reciprocitySign_self_eq_sextic_neg_one (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (ho : Odd p) :
    reciprocitySign p p = complexSexticChar (Ideal.span {p}) hg (-1) := by
  have hg1 : fixedDualAverage (p*p) = 1 := by
    have he := FixedRayArithmetic.gamma_mul_sq (c := 1) (d := p)
      (fun h => odd_one (Ideal.mem_span_singleton.mp h))
      (fun h => ho (Ideal.mem_span_singleton.mp h))
    simpa only [one_mul, fixedDualAverage_one, pow_two] using he
  have hg2 : fixedDualAverage p ^ 2 = complexSexticChar (Ideal.span {p}) hg (-1) := by
    rw [← localGamma_three_phase p hp hg hc]
    exact localGamma_three_sq p hp hg hc
  rw [reciprocitySign, sexticReciprocityPhase_good p p ho ho,
    FixedRayArithmetic.quadraticPhase, hg1, ← pow_two, hg2]
  have hw := complexSexticChar_neg_one_sq (Ideal.span {p}) hg
  have hn : complexSexticChar (Ideal.span {p}) hg (-1) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hw
    exact zero_ne_one hw
  apply (div_eq_iff hn).mpr
  simpa only [pow_two] using hw.symm

lemma G_cube_eq_localGamma (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : lambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (ho : Odd p) :
    G (p^3) = localGamma p hp hg 3 := by
  rw [G_cube p ho]
  exact (localGamma_three_phase p hp hg hc).symm

end ProbePhase
end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
