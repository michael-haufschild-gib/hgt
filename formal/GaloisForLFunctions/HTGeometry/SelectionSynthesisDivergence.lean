import Mathlib

/-!
# Selection information and synthesis divergence

The geometrically killed local-word prior assigns a word the mass `(1-a)(a/M)^{|w|}`; summing over
words of each length gives a geometric series, so it is a probability law.  Its negative logarithm
is affine in the word length, so the expected gate cost is exactly the cross entropy of the encoder
against the prior.

Cross entropy splits as entropy plus relative entropy, and relative entropy is nonnegative and
vanishes only at the prior itself.  Expected circuit length is therefore selection information plus
synthesis divergence, with the two summands equal only in the matched-prior regime.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The local gate-word prior -/

section Prior

variable {Γ : Type*} [Fintype Γ]

/-- The geometrically killed local-word prior. -/
def wordPrior (a : ℝ) (w : List Γ) : ℝ :=
  (1 - a) * (a / (Fintype.card Γ : ℝ)) ^ w.length

theorem wordPrior_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ)
    (w : List Γ) : 0 < wordPrior a w := by
  have hMpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hM
  rw [wordPrior]
  have : 0 < a / (Fintype.card Γ : ℝ) := by positivity
  positivity

/-- **`(7)`: the prior has affine negative logarithm.** -/
theorem neg_log_wordPrior {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ)
    (w : List Γ) :
    -Real.log (wordPrior a w)
      = -Real.log (1 - a) + (w.length : ℝ) * Real.log ((Fintype.card Γ : ℝ) / a) := by
  have hMpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hM
  have hratio : 0 < a / (Fintype.card Γ : ℝ) := by positivity
  rw [wordPrior, Real.log_mul (by linarith) (by positivity), Real.log_pow]
  have hinv : Real.log (a / (Fintype.card Γ : ℝ))
      = -Real.log ((Fintype.card Γ : ℝ) / a) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  rw [hinv]
  ring

/-- The words of a fixed length carry total prior mass `(1-a)a^ℓ`. -/
theorem sum_wordPrior_length {a : ℝ} (hM : 0 < Fintype.card Γ) (ℓ : ℕ) :
    ∑ w : List.Vector Γ ℓ, wordPrior a w.1 = (1 - a) * a ^ ℓ := by
  classical
  have hMpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hM
  have hconst : ∀ w : List.Vector Γ ℓ,
      wordPrior a w.1 = (1 - a) * (a / (Fintype.card Γ : ℝ)) ^ ℓ := by
    intro w
    rw [wordPrior, w.2]
  rw [Finset.sum_congr rfl fun w _ => hconst w, Finset.sum_const, Finset.card_univ,
    card_vector, nsmul_eq_mul]
  push_cast
  rw [div_pow]
  field_simp

/-- **`(2)`: the prior is a probability law on words.** -/
theorem hasSum_wordPrior {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ) :
    HasSum (wordPrior (Γ := Γ) a) 1 := by
  classical
  have hMpos : (0 : ℝ) < (Fintype.card Γ : ℝ) := by exact_mod_cast hM
  have hnn : ∀ w : List Γ, 0 ≤ wordPrior (Γ := Γ) a w :=
    fun w => le_of_lt (wordPrior_pos ha ha1 hM w)
  have hfiber : ∀ ℓ : ℕ,
      ∑' w : List.Vector Γ ℓ, ENNReal.ofReal (wordPrior (Γ := Γ) a w.1)
        = ENNReal.ofReal ((1 - a) * a ^ ℓ) := by
    intro ℓ
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun w _ => hnn _]
    congr 1
    exact sum_wordPrior_length (Γ := Γ) hM ℓ
  have hsigma : ∑' w : List Γ, ENNReal.ofReal (wordPrior (Γ := Γ) a w)
      = ∑' ℓ : ℕ, ENNReal.ofReal ((1 - a) * a ^ ℓ) := by
    rw [← (Equiv.sigmaFiberEquiv (List.length : List Γ → ℕ)).tsum_eq
      (fun w => ENNReal.ofReal (wordPrior (Γ := Γ) a w))]
    have hcongr : ∀ c : (y : ℕ) × {x : List Γ // x.length = y},
        ENNReal.ofReal
            (wordPrior (Γ := Γ) a ((Equiv.sigmaFiberEquiv (List.length : List Γ → ℕ)) c))
          = ENNReal.ofReal (wordPrior (Γ := Γ) a c.2.1) := fun c => rfl
    rw [tsum_congr hcongr]
    rw [ENNReal.tsum_sigma (fun ℓ (w : {x : List Γ // x.length = ℓ}) =>
      ENNReal.ofReal (wordPrior (Γ := Γ) a w.1))]
    exact tsum_congr hfiber
  have hgeom : ∑' ℓ : ℕ, ENNReal.ofReal ((1 - a) * a ^ ℓ) = 1 := by
    have hterm : ∀ ℓ : ℕ, ENNReal.ofReal ((1 - a) * a ^ ℓ)
        = ENNReal.ofReal (1 - a) * (ENNReal.ofReal a) ^ ℓ := by
      intro ℓ
      rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_pow (le_of_lt ha)]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hsub : 1 - ENNReal.ofReal a = ENNReal.ofReal (1 - a) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (le_of_lt ha)]
    rw [hsub, ENNReal.mul_inv_cancel (by
      simpa using (by linarith : (0:ℝ) < 1 - a)) ENNReal.ofReal_ne_top]
  have htotal : ∑' w : List Γ, ENNReal.ofReal (wordPrior (Γ := Γ) a w) = 1 := by
    rw [hsigma, hgeom]
  have hsummable : Summable (wordPrior (Γ := Γ) a) := by
    have h := ENNReal.summable_toReal (f := fun w : List Γ =>
      ENNReal.ofReal (wordPrior (Γ := Γ) a w)) (by rw [htotal]; exact ENNReal.one_ne_top)
    refine h.congr fun w => ?_
    exact ENNReal.toReal_ofReal (hnn w)
  have hval : ∑' w : List Γ, wordPrior (Γ := Γ) a w = 1 := by
    have hof := ENNReal.ofReal_tsum_of_nonneg hnn hsummable
    rw [htotal] at hof
    have hcast := congrArg ENNReal.toReal hof
    rw [ENNReal.toReal_ofReal (tsum_nonneg hnn)] at hcast
    simpa using hcast
  exact hval ▸ hsummable.hasSum

end Prior

/-! ## Entropy, relative entropy and cross entropy -/

section Entropy

variable {α : Type*}

/-- Shannon entropy of a discrete law. -/
def entropy (q : α → ℝ) : ℝ := ∑' w, -(q w * Real.log (q w))

/-- Relative entropy of a discrete law against a reference. -/
def relEntropy (q p : α → ℝ) : ℝ := ∑' w, q w * Real.log (q w / p w)

/-- Cross entropy of a discrete law against a reference. -/
def crossEntropy (q p : α → ℝ) : ℝ := ∑' w, -(q w * Real.log (p w))

/-- **`(9)` pointwise.**  At every point the three densities satisfy the exact identity. -/
theorem entropy_add_relEntropy_pointwise {q p : α → ℝ} (hq : ∀ w, 0 ≤ q w) (hp : ∀ w, 0 < p w)
    (w : α) :
    -(q w * Real.log (q w)) + q w * Real.log (q w / p w) = -(q w * Real.log (p w)) := by
  rcases eq_or_lt_of_le (hq w) with hzero | hpos
  · rw [← hzero]
    simp
  · rw [Real.log_div (ne_of_gt hpos) (ne_of_gt (hp w))]
    ring

/-- **`(9)`: cross entropy is entropy plus relative entropy.** -/
theorem entropy_add_relEntropy {q p : α → ℝ} (hq : ∀ w, 0 ≤ q w) (hp : ∀ w, 0 < p w)
    (hs1 : Summable fun w => -(q w * Real.log (q w)))
    (hs2 : Summable fun w => q w * Real.log (q w / p w)) :
    entropy q + relEntropy q p = crossEntropy q p := by
  rw [entropy, relEntropy, crossEntropy, ← hs1.tsum_add hs2]
  exact tsum_congr fun w => entropy_add_relEntropy_pointwise hq hp w

end Entropy

/-! ## The gate-cost identity -/

section GateCost

variable {Γ : Type*} [Fintype Γ]

/-- Expected word length of a discrete law on words. -/
def expectedLength (q : List Γ → ℝ) : ℝ := ∑' w, q w * (w.length : ℝ)

/-- **`(8)`: the cross entropy against the prior is affine in the expected length.** -/
theorem crossEntropy_wordPrior {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hM : 0 < Fintype.card Γ)
    {q : List Γ → ℝ} (hsum : HasSum q 1)
    (hlen : Summable fun w => q w * (w.length : ℝ)) :
    crossEntropy q (wordPrior a)
      = -Real.log (1 - a) + Real.log ((Fintype.card Γ : ℝ) / a) * expectedLength q := by
  have hpoint : ∀ w : List Γ, -(q w * Real.log (wordPrior a w))
      = q w * (-Real.log (1 - a))
        + Real.log ((Fintype.card Γ : ℝ) / a) * (q w * (w.length : ℝ)) := by
    intro w
    have h := neg_log_wordPrior (Γ := Γ) ha ha1 hM w
    have hmul : -(q w * Real.log (wordPrior a w)) = q w * (-Real.log (wordPrior a w)) := by ring
    rw [hmul, h]
    ring
  have hs1 : Summable fun w : List Γ => q w * (-Real.log (1 - a)) :=
    hsum.summable.mul_right _
  have hs2 : Summable fun w : List Γ =>
      Real.log ((Fintype.card Γ : ℝ) / a) * (q w * (w.length : ℝ)) :=
    hlen.mul_left _
  rw [crossEntropy, tsum_congr hpoint, hs1.tsum_add hs2, tsum_mul_right, hsum.tsum_eq,
    tsum_mul_left, expectedLength]
  ring

/-- **`(5)`: expected gate cost is entropy plus synthesis divergence.**  This is Theorem A in the
form that does not use the mutual-information chain rule. -/
theorem gateCost_eq_entropy_add_relEntropy {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hM : 0 < Fintype.card Γ) {q : List Γ → ℝ} (hq : ∀ w, 0 ≤ q w) (hsum : HasSum q 1)
    (hlen : Summable fun w => q w * (w.length : ℝ))
    (hs1 : Summable fun w => -(q w * Real.log (q w)))
    (hs2 : Summable fun w => q w * Real.log (q w / wordPrior a w)) :
    entropy q + relEntropy q (wordPrior a)
      = -Real.log (1 - a) + Real.log ((Fintype.card Γ : ℝ) / a) * expectedLength q := by
  rw [entropy_add_relEntropy hq (fun w => wordPrior_pos ha ha1 hM w) hs1 hs2,
    crossEntropy_wordPrior ha ha1 hM hsum hlen]

end GateCost

/-! ## Nonnegativity of the synthesis divergence -/

section Gibbs

variable {α : Type*}

/-- The elementary logarithm bound behind Gibbs' inequality. -/
theorem log_le_sub_one {t : ℝ} (ht : 0 < t) : Real.log t ≤ t - 1 :=
  Real.log_le_sub_one_of_pos ht

/-- **Gibbs' inequality.**  Relative entropy is nonnegative. -/
theorem relEntropy_nonneg {q p : α → ℝ} (hq : ∀ w, 0 ≤ q w) (hp : ∀ w, 0 < p w)
    (hqsum : HasSum q 1) (hpsum : HasSum p 1)
    (hs : Summable fun w => q w * Real.log (q w / p w)) :
    0 ≤ relEntropy q p := by
  have hbound : ∀ w, -(q w * Real.log (q w / p w)) ≤ p w - q w := by
    intro w
    rcases eq_or_lt_of_le (hq w) with hzero | hpos
    · rw [← hzero]
      simp
      linarith [hp w]
    · have hratio : 0 < p w / q w := div_pos (hp w) hpos
      have hlog := log_le_sub_one hratio
      have hneg : -(q w * Real.log (q w / p w)) = q w * Real.log (p w / q w) := by
        rw [show p w / q w = (q w / p w)⁻¹ by rw [inv_div], Real.log_inv]
        ring
      rw [hneg]
      calc q w * Real.log (p w / q w) ≤ q w * (p w / q w - 1) :=
            mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
        _ = p w - q w := by field_simp
  have hneg : Summable fun w => -(q w * Real.log (q w / p w)) := hs.neg
  have hdiff : HasSum (fun w => p w - q w) 0 := by
    have := hpsum.sub hqsum
    simpa using this
  have hle : ∑' w, -(q w * Real.log (q w / p w)) ≤ 0 := by
    calc ∑' w, -(q w * Real.log (q w / p w)) ≤ ∑' w, (p w - q w) :=
          hneg.tsum_le_tsum hbound hdiff.summable
      _ = 0 := hdiff.tsum_eq
  rw [relEntropy]
  rw [tsum_neg] at hle
  linarith

/-- **Corollary A.1.**  The entropy-only accounting is exact only at the prior: if the encoder's
word law is the prior, the synthesis divergence vanishes. -/
theorem relEntropy_self_eq_zero {p : α → ℝ} (hp : ∀ w, 0 < p w) :
    relEntropy p p = 0 := by
  have h : ∀ w, p w * Real.log (p w / p w) = 0 := by
    intro w
    rw [div_self (ne_of_gt (hp w)), Real.log_one, mul_zero]
  rw [relEntropy, tsum_congr h, tsum_zero]

end Gibbs

end

end GaloisForLFunctions.HTGeometry
