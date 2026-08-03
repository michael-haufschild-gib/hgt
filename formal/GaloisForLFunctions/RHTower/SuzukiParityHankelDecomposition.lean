import GaloisForLFunctions.RHTower.SuzukiScrewCorrelationPairing
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Data.Real.Sign

/-!
# Parity reduction of an even convolution kernel: `Q_even = T + H`, `Q_odd = T - H`

For an even kernel `K` the two-variable form `∫∫ K (x - y) f y g x` on the whole line splits under
the unitary parity lifts

```text
(U₊ φ) x = φ |x| / √2,      (U₋ φ) x = sign x * φ |x| / √2
```

of a function `φ` supported in `(0, ∞)` into the difference (Toeplitz) part and the sum (Hankel)
part:

```text
Q (U₊ φ) (U₊ ψ) = T φ ψ + H φ ψ,
Q (U₋ φ) (U₋ ψ) = T φ ψ - H φ ψ,
Q (U₊ φ) (U₊ ψ) - Q (U₋ φ) (U₋ ψ) = 2 * H φ ψ.
```

Here `T = diffBilinForm K` and `H = sumBilinForm K`.  For `φ, ψ` supported in `(0, a)` these are
exactly the half-line forms `T_a`, `H_a` of the card, the zero extension being harmless.

The mechanism is that on functions vanishing on `(-∞, 0]` the parity lifts are simply
symmetrisation and antisymmetrisation,

```text
U₊ φ = (φ + φ∘(-·)) / √2,    U₋ φ = (φ - φ∘(-·)) / √2,
```

so the four cross terms are reflections of the two basic forms.  Each reflection is a
measure-preserving map of `ℝ × ℝ`, so the identifications

```text
T (φ∘(-·)) ψ = H φ ψ,   T φ (ψ∘(-·)) = H φ ψ,   T (φ∘(-·)) (ψ∘(-·)) = T φ ψ
```

need no integrability hypothesis at all; only the expansion of the product does.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory

/-! ## Measure-preserving reflections of the plane -/

theorem measurePreserving_negSnd :
    MeasurePreserving (Prod.map (id : ℝ → ℝ) (Neg.neg : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume) :=
  (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)

theorem measurableEmbedding_negSnd :
    MeasurableEmbedding (Prod.map (id : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) :=
  ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding

theorem measurePreserving_negFst :
    MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume) :=
  (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)

theorem measurableEmbedding_negFst :
    MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) :=
  ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding

theorem measurePreserving_negBoth :
    MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume) :=
  (Measure.measurePreserving_neg volume).prod (Measure.measurePreserving_neg volume)

theorem measurableEmbedding_negBoth :
    MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (Neg.neg : ℝ → ℝ)) :=
  ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding

theorem integral_comp_negSnd (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, F (p.1, -p.2)) = ∫ p : ℝ × ℝ, F p := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact measurePreserving_negSnd.integral_comp measurableEmbedding_negSnd F

theorem integral_comp_negFst (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, F (-p.1, p.2)) = ∫ p : ℝ × ℝ, F p := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact measurePreserving_negFst.integral_comp measurableEmbedding_negFst F

theorem integral_comp_negBoth (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × ℝ, F (-p.1, -p.2)) = ∫ p : ℝ × ℝ, F p := by
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact measurePreserving_negBoth.integral_comp measurableEmbedding_negBoth F

theorem integrable_comp_negSnd {F : ℝ × ℝ → ℝ} (hF : Integrable F) :
    Integrable fun p : ℝ × ℝ => F (p.1, -p.2) := by
  rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
  exact (measurePreserving_negSnd.integrable_comp_emb measurableEmbedding_negSnd).mpr hF

theorem integrable_comp_negFst {F : ℝ × ℝ → ℝ} (hF : Integrable F) :
    Integrable fun p : ℝ × ℝ => F (-p.1, p.2) := by
  rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
  exact (measurePreserving_negFst.integrable_comp_emb measurableEmbedding_negFst).mpr hF

theorem integrable_comp_negBoth {F : ℝ × ℝ → ℝ} (hF : Integrable F) :
    Integrable fun p : ℝ × ℝ => F (-p.1, -p.2) := by
  rw [Measure.volume_eq_prod ℝ ℝ] at hF ⊢
  exact (measurePreserving_negBoth.integrable_comp_emb measurableEmbedding_negBoth).mpr hF

/-! ## The two forms and the parity lifts -/

/-- The difference (Toeplitz) form `∫∫ K (x - y) f y g x` of a kernel. -/
def diffBilinForm (K f g : ℝ → ℝ) : ℝ := ∫ p : ℝ × ℝ, K (p.1 - p.2) * f p.2 * g p.1

/-- The sum (Hankel) form `∫∫ K (x + y) f y g x` of a kernel. -/
def sumBilinForm (K f g : ℝ → ℝ) : ℝ := ∫ p : ℝ × ℝ, K (p.1 + p.2) * f p.2 * g p.1

/-- Reflection of a function of the line. -/
def negReflect (f : ℝ → ℝ) : ℝ → ℝ := fun x => f (-x)

@[simp] theorem negReflect_apply (f : ℝ → ℝ) (x : ℝ) : negReflect f x = f (-x) := rfl

/-- The even parity lift `U₊ φ x = φ |x| / √2`. -/
def evenParityLift (φ : ℝ → ℝ) (x : ℝ) : ℝ := φ |x| / Real.sqrt 2

/-- The odd parity lift `U₋ φ x = sign x * φ |x| / √2`. -/
def oddParityLift (φ : ℝ → ℝ) (x : ℝ) : ℝ := Real.sign x * φ |x| / Real.sqrt 2

theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

/-- **On functions vanishing on `(-∞, 0]` the even lift is symmetrisation.** -/
theorem evenParityLift_eq_of_vanishing {φ : ℝ → ℝ} (hφ : ∀ x ≤ (0 : ℝ), φ x = 0) (x : ℝ) :
    evenParityLift φ x = (φ x + negReflect φ x) / Real.sqrt 2 := by
  simp only [evenParityLift, negReflect]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [abs_of_neg h, hφ x h.le, zero_add]
  · subst h; simp [hφ 0 le_rfl]
  · rw [abs_of_pos h, hφ (-x) (by linarith), add_zero]

/-- **On functions vanishing on `(-∞, 0]` the odd lift is antisymmetrisation.** -/
theorem oddParityLift_eq_of_vanishing {φ : ℝ → ℝ} (hφ : ∀ x ≤ (0 : ℝ), φ x = 0) (x : ℝ) :
    oddParityLift φ x = (φ x - negReflect φ x) / Real.sqrt 2 := by
  simp only [oddParityLift, negReflect]
  rcases lt_trichotomy x 0 with h | h | h
  · rw [abs_of_neg h, Real.sign_of_neg h, hφ x h.le, zero_sub]
    ring
  · subst h; simp [hφ 0 le_rfl]
  · rw [abs_of_pos h, Real.sign_of_pos h, hφ (-x) (by linarith), sub_zero, one_mul]

/-! ## The reflection identities -/

/-- Reflecting the left slot of the difference form produces the sum form.  No evenness and no
integrability is needed. -/
theorem diffBilinForm_negReflect_left (K φ ψ : ℝ → ℝ) :
    diffBilinForm K (negReflect φ) ψ = sumBilinForm K φ ψ := by
  rw [diffBilinForm, sumBilinForm,
    ← integral_comp_negSnd fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [negReflect]
  rw [show p.1 + -p.2 = p.1 - p.2 from by ring]

/-- Reflecting the right slot of the difference form produces the sum form, for an even kernel. -/
theorem diffBilinForm_negReflect_right (K φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    diffBilinForm K φ (negReflect ψ) = sumBilinForm K φ ψ := by
  rw [diffBilinForm, sumBilinForm,
    ← integral_comp_negFst fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [negReflect]
  rw [show -p.1 + p.2 = -(p.1 - p.2) from by ring, hK]

/-- Reflecting both slots leaves the difference form unchanged, for an even kernel. -/
theorem diffBilinForm_negReflect_both (K φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t) :
    diffBilinForm K (negReflect φ) (negReflect ψ) = diffBilinForm K φ ψ := by
  rw [diffBilinForm, diffBilinForm,
    ← integral_comp_negBoth fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [negReflect]
  rw [show -p.1 - -p.2 = -(p.1 - p.2) from by ring, hK]

/-! ## Integrability of the four cross terms -/

theorem integrable_diff_negReflect_left {K φ ψ : ℝ → ℝ}
    (hs : Integrable fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1) :
    Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * negReflect φ p.2 * ψ p.1 := by
  refine (integrable_comp_negSnd hs).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [negReflect]
  rw [show p.1 + -p.2 = p.1 - p.2 from by ring]

theorem integrable_diff_negReflect_right {K φ ψ : ℝ → ℝ} (hK : ∀ t, K (-t) = K t)
    (hs : Integrable fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1) :
    Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * negReflect ψ p.1 := by
  refine (integrable_comp_negFst hs).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [negReflect]
  rw [show -p.1 + p.2 = -(p.1 - p.2) from by ring, hK]

theorem integrable_diff_negReflect_both {K φ ψ : ℝ → ℝ} (hK : ∀ t, K (-t) = K t)
    (hd : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1) :
    Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1 := by
  refine (integrable_comp_negBoth hd).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [negReflect]
  rw [show -p.1 - -p.2 = -(p.1 - p.2) from by ring, hK]

/-! ## The parity decomposition -/

/-- **The even parity sector is `T + H`.** -/
theorem diffBilinForm_evenParityLift (K φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t)
    (hφ : ∀ x ≤ (0 : ℝ), φ x = 0) (hψ : ∀ x ≤ (0 : ℝ), ψ x = 0)
    (hd : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1)
    (hs : Integrable fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1) :
    diffBilinForm K (evenParityLift φ) (evenParityLift ψ)
      = diffBilinForm K φ ψ + sumBilinForm K φ ψ := by
  have hi2 := integrable_diff_negReflect_left (K := K) (φ := φ) (ψ := ψ) hs
  have hi3 := integrable_diff_negReflect_right (K := K) (φ := φ) (ψ := ψ) hK hs
  have hi4 := integrable_diff_negReflect_both (K := K) (φ := φ) (ψ := ψ) hK hd
  have hpt : ∀ p : ℝ × ℝ,
      K (p.1 - p.2) * evenParityLift φ p.2 * evenParityLift ψ p.1
        = (1 / 2 : ℝ) * (K (p.1 - p.2) * φ p.2 * ψ p.1
            + K (p.1 - p.2) * negReflect φ p.2 * ψ p.1
            + K (p.1 - p.2) * φ p.2 * negReflect ψ p.1
            + K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1) := by
    intro p
    rw [evenParityLift_eq_of_vanishing hφ, evenParityLift_eq_of_vanishing hψ]
    have hstep : K (p.1 - p.2) * ((φ p.2 + negReflect φ p.2) / Real.sqrt 2)
          * ((ψ p.1 + negReflect ψ p.1) / Real.sqrt 2)
        = K (p.1 - p.2) * (φ p.2 + negReflect φ p.2) * (ψ p.1 + negReflect ψ p.1)
          / (Real.sqrt 2 * Real.sqrt 2) := by ring
    rw [hstep, sqrt_two_mul_self]
    ring
  calc diffBilinForm K (evenParityLift φ) (evenParityLift ψ)
      = ∫ p : ℝ × ℝ, (1 / 2 : ℝ) * (K (p.1 - p.2) * φ p.2 * ψ p.1
            + K (p.1 - p.2) * negReflect φ p.2 * ψ p.1
            + K (p.1 - p.2) * φ p.2 * negReflect ψ p.1
            + K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1) := by
        rw [diffBilinForm]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (1 / 2 : ℝ) * ∫ p : ℝ × ℝ, (K (p.1 - p.2) * φ p.2 * ψ p.1
            + K (p.1 - p.2) * negReflect φ p.2 * ψ p.1
            + K (p.1 - p.2) * φ p.2 * negReflect ψ p.1
            + K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1) := integral_const_mul _ _
    _ = (1 / 2 : ℝ) * (diffBilinForm K φ ψ + sumBilinForm K φ ψ + sumBilinForm K φ ψ
          + diffBilinForm K φ ψ) := by
        have hA : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1
            + K (p.1 - p.2) * negReflect φ p.2 * ψ p.1 := hd.add hi2
        have hB : Integrable fun p : ℝ × ℝ => (K (p.1 - p.2) * φ p.2 * ψ p.1
              + K (p.1 - p.2) * negReflect φ p.2 * ψ p.1)
            + K (p.1 - p.2) * φ p.2 * negReflect ψ p.1 := hA.add hi3
        rw [integral_add hB hi4, integral_add hA hi3, integral_add hd hi2]
        rw [show (∫ p : ℝ × ℝ, K (p.1 - p.2) * negReflect φ p.2 * ψ p.1)
            = sumBilinForm K φ ψ from diffBilinForm_negReflect_left K φ ψ,
          show (∫ p : ℝ × ℝ, K (p.1 - p.2) * φ p.2 * negReflect ψ p.1)
            = sumBilinForm K φ ψ from diffBilinForm_negReflect_right K φ ψ hK,
          show (∫ p : ℝ × ℝ, K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1)
            = diffBilinForm K φ ψ from diffBilinForm_negReflect_both K φ ψ hK]
        rfl
    _ = diffBilinForm K φ ψ + sumBilinForm K φ ψ := by ring

/-- **The odd parity sector is `T - H`.** -/
theorem diffBilinForm_oddParityLift (K φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t)
    (hφ : ∀ x ≤ (0 : ℝ), φ x = 0) (hψ : ∀ x ≤ (0 : ℝ), ψ x = 0)
    (hd : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1)
    (hs : Integrable fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1) :
    diffBilinForm K (oddParityLift φ) (oddParityLift ψ)
      = diffBilinForm K φ ψ - sumBilinForm K φ ψ := by
  have hi2 := integrable_diff_negReflect_left (K := K) (φ := φ) (ψ := ψ) hs
  have hi3 := integrable_diff_negReflect_right (K := K) (φ := φ) (ψ := ψ) hK hs
  have hi4 := integrable_diff_negReflect_both (K := K) (φ := φ) (ψ := ψ) hK hd
  have hpt : ∀ p : ℝ × ℝ,
      K (p.1 - p.2) * oddParityLift φ p.2 * oddParityLift ψ p.1
        = (1 / 2 : ℝ) * (K (p.1 - p.2) * φ p.2 * ψ p.1
            + (-1 : ℝ) * (K (p.1 - p.2) * negReflect φ p.2 * ψ p.1)
            + (-1 : ℝ) * (K (p.1 - p.2) * φ p.2 * negReflect ψ p.1)
            + K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1) := by
    intro p
    rw [oddParityLift_eq_of_vanishing hφ, oddParityLift_eq_of_vanishing hψ]
    have hstep : K (p.1 - p.2) * ((φ p.2 - negReflect φ p.2) / Real.sqrt 2)
          * ((ψ p.1 - negReflect ψ p.1) / Real.sqrt 2)
        = K (p.1 - p.2) * (φ p.2 - negReflect φ p.2) * (ψ p.1 - negReflect ψ p.1)
          / (Real.sqrt 2 * Real.sqrt 2) := by ring
    rw [hstep, sqrt_two_mul_self]
    ring
  calc diffBilinForm K (oddParityLift φ) (oddParityLift ψ)
      = ∫ p : ℝ × ℝ, (1 / 2 : ℝ) * (K (p.1 - p.2) * φ p.2 * ψ p.1
            + (-1 : ℝ) * (K (p.1 - p.2) * negReflect φ p.2 * ψ p.1)
            + (-1 : ℝ) * (K (p.1 - p.2) * φ p.2 * negReflect ψ p.1)
            + K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1) := by
        rw [diffBilinForm]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (1 / 2 : ℝ) * ∫ p : ℝ × ℝ, (K (p.1 - p.2) * φ p.2 * ψ p.1
            + (-1 : ℝ) * (K (p.1 - p.2) * negReflect φ p.2 * ψ p.1)
            + (-1 : ℝ) * (K (p.1 - p.2) * φ p.2 * negReflect ψ p.1)
            + K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1) := integral_const_mul _ _
    _ = (1 / 2 : ℝ) * (diffBilinForm K φ ψ + (-1 : ℝ) * sumBilinForm K φ ψ
          + (-1 : ℝ) * sumBilinForm K φ ψ + diffBilinForm K φ ψ) := by
        have hc2 : Integrable fun p : ℝ × ℝ =>
            (-1 : ℝ) * (K (p.1 - p.2) * negReflect φ p.2 * ψ p.1) := hi2.const_mul (-1 : ℝ)
        have hc3 : Integrable fun p : ℝ × ℝ =>
            (-1 : ℝ) * (K (p.1 - p.2) * φ p.2 * negReflect ψ p.1) := hi3.const_mul (-1 : ℝ)
        have hA : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1
            + (-1 : ℝ) * (K (p.1 - p.2) * negReflect φ p.2 * ψ p.1) := hd.add hc2
        have hB : Integrable fun p : ℝ × ℝ => (K (p.1 - p.2) * φ p.2 * ψ p.1
              + (-1 : ℝ) * (K (p.1 - p.2) * negReflect φ p.2 * ψ p.1))
            + (-1 : ℝ) * (K (p.1 - p.2) * φ p.2 * negReflect ψ p.1) := hA.add hc3
        rw [integral_add hB hi4, integral_add hA hc3, integral_add hd hc2,
          integral_const_mul, integral_const_mul]
        rw [show (∫ p : ℝ × ℝ, K (p.1 - p.2) * negReflect φ p.2 * ψ p.1)
            = sumBilinForm K φ ψ from diffBilinForm_negReflect_left K φ ψ,
          show (∫ p : ℝ × ℝ, K (p.1 - p.2) * φ p.2 * negReflect ψ p.1)
            = sumBilinForm K φ ψ from diffBilinForm_negReflect_right K φ ψ hK,
          show (∫ p : ℝ × ℝ, K (p.1 - p.2) * negReflect φ p.2 * negReflect ψ p.1)
            = diffBilinForm K φ ψ from diffBilinForm_negReflect_both K φ ψ hK]
        rfl
    _ = diffBilinForm K φ ψ - sumBilinForm K φ ψ := by ring

/-- **The parity difference is twice the Hankel form.** -/
theorem diffBilinForm_parity_difference (K φ ψ : ℝ → ℝ) (hK : ∀ t, K (-t) = K t)
    (hφ : ∀ x ≤ (0 : ℝ), φ x = 0) (hψ : ∀ x ≤ (0 : ℝ), ψ x = 0)
    (hd : Integrable fun p : ℝ × ℝ => K (p.1 - p.2) * φ p.2 * ψ p.1)
    (hs : Integrable fun p : ℝ × ℝ => K (p.1 + p.2) * φ p.2 * ψ p.1) :
    diffBilinForm K (evenParityLift φ) (evenParityLift ψ)
        - diffBilinForm K (oddParityLift φ) (oddParityLift ψ)
      = 2 * sumBilinForm K φ ψ := by
  rw [diffBilinForm_evenParityLift K φ ψ hK hφ hψ hd hs,
    diffBilinForm_oddParityLift K φ ψ hK hφ hψ hd hs]
  ring

end GaloisForLFunctions.RHTower

end
