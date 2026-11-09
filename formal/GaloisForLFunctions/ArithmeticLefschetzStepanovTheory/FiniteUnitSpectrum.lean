import GaloisForLFunctions.HTGeometry.BohrDerivativeSpectrum

/-!
# A finite unimodular spectrum is a single character

The largest difference of two support frequencies has a unique source
pair in the squared modulus. Its nonzero coefficient excludes constant
modulus unless the support consists of one frequency.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {ι : Type*}

/-- A finite complex wave with real frequencies. -/
def finiteExpWave (s : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ s, c i * expChar (ω i) t

private theorem conj_expChar_eq (a t : ℝ) :
    (starRingEnd ℂ) (expChar a t) = expChar (-a) t := by
  rw [expChar, expChar, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem bohrCoefficient_constant (c : ℂ) (a : ℝ) :
    bohrCoefficient (fun _ : ℝ => c) a = if a = 0 then c else 0 := by
  change bohrMean (fun t => c * bohrChar a t) = _
  rw [bohrMean_const_mul c (continuous_bohrChar a) (isBohrAlmostPeriodic_bohrChar a),
    bohrMean_bohrChar]
  split_ifs <;> simp

/-- Squaring the modulus pairs each frequency with the negative of every other frequency. -/
theorem finiteExpWave_mul_conj (s : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) (t : ℝ) :
    finiteExpWave s c ω t * (starRingEnd ℂ) (finiteExpWave s c ω t) =
      ∑ k ∈ s ×ˢ s, (c k.1 * (starRingEnd ℂ) (c k.2)) * expChar (ω k.1 - ω k.2) t := by
  rw [finiteExpWave, map_sum, Finset.sum_mul_sum, Finset.sum_product]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [map_mul, conj_expChar_eq]
  calc
    (c i * expChar (ω i) t) * ((starRingEnd ℂ) (c j) * expChar (-ω j) t) =
        (c i * (starRingEnd ℂ) (c j)) * (expChar (ω i) t * expChar (-ω j) t) := by ring
    _ = _ := by rw [expChar_add, sub_eq_add_neg]

/-- A nonempty, reduced finite spectrum of constant modulus has no distinct endpoints. -/
theorem finiteExpWave_extreme_frequencies_eq (s : Finset ι) (c : ι → ℂ) (ω : ι → ℝ)
    (hinj : Set.InjOn ω s) (hc : ∀ i ∈ s, c i ≠ 0)
    (hunit : ∀ t, ‖finiteExpWave s c ω t‖ = 1)
    (a b : ι) (ha : a ∈ s) (hb : b ∈ s)
    (hmax : ∀ i ∈ s, ω i ≤ ω a) (hmin : ∀ i ∈ s, ω b ≤ ω i) : ω a = ω b := by
  classical
  by_contra hab
  have hgap : ω a - ω b ≠ 0 := sub_ne_zero.mpr hab
  have hfun : (fun t => ∑ k ∈ s ×ˢ s,
      (c k.1 * (starRingEnd ℂ) (c k.2)) * expChar (ω k.1 - ω k.2) t) =
      fun _ : ℝ => (1 : ℂ) := by
    funext t
    rw [← finiteExpWave_mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, hunit]
    simp
  have hcoef := congrArg (fun f : ℝ → ℂ => bohrCoefficient f (ω a - ω b)) hfun
  rw [bohrCoefficient_sum_expChar, bohrCoefficient_constant, if_neg hgap] at hcoef
  have hone : (∑ k ∈ s ×ˢ s,
      if ω k.1 - ω k.2 = ω a - ω b then c k.1 * (starRingEnd ℂ) (c k.2) else 0) =
      c a * (starRingEnd ℂ) (c b) := by
    rw [sum_eq_single (a, b)]
    · simp only [if_true]
    · intro k hk hkab
      apply if_neg
      intro he
      have hk' := mem_product.mp hk
      have hka : ω k.1 = ω a := by linarith [hmax k.1 hk'.1, hmin k.2 hk'.2]
      have hkb : ω k.2 = ω b := by linarith [hmax k.1 hk'.1, hmin k.2 hk'.2]
      apply hkab
      exact Prod.ext (hinj hk'.1 ha hka) (hinj hk'.2 hb hkb)
    · intro hnot
      exact (hnot (mem_product.mpr ⟨ha, hb⟩)).elim
  rw [hone] at hcoef
  exact (mul_ne_zero (hc a ha) ((map_ne_zero (starRingEnd ℂ)).mpr (hc b hb))) hcoef

/-- Every finite unimodular wave with distinct, nonzero terms is one unimodular character. -/
theorem finiteExpWave_unit_support (s : Finset ι) (c : ι → ℂ) (ω : ι → ℝ)
    (hinj : Set.InjOn ω s) (hc : ∀ i ∈ s, c i ≠ 0)
    (hunit : ∀ t, ‖finiteExpWave s c ω t‖ = 1) :
    ∃ a, s = {a} ∧ ‖c a‖ = 1 := by
  classical
  have hs : s.Nonempty := by
    by_contra h
    have he : s = ∅ := not_nonempty_iff_eq_empty.mp h
    have h0 := hunit 0
    simp only [finiteExpWave, he, sum_empty, norm_zero] at h0
    exact zero_ne_one h0
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image ω hs
  obtain ⟨b, hb, hmin⟩ := s.exists_min_image ω hs
  have he := finiteExpWave_extreme_frequencies_eq s c ω hinj hc hunit a b ha hb hmax hmin
  have hsingleton : s = {a} := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      apply mem_singleton.mpr
      exact hinj hi ha (by linarith [hmax i hi, hmin i hi])
    · intro hi
      exact mem_singleton.mp hi ▸ ha
  refine ⟨a, hsingleton, ?_⟩
  have h0 := hunit 0
  simpa only [finiteExpWave, hsingleton, sum_singleton, expChar, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] using h0

#print axioms finiteExpWave_unit_support

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
