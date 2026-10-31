import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentNormalization
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticGapTopology
import GaloisForLFunctions.HTGeometry.LoopEisenstein.TriangularHaarProbability

/-!
# Invariant probability on normalized elliptic unipotent streams

Left matrix multiplication followed by rational reduction acts on each
free coordinate by a translation depending only on earlier coordinates.
These continuous triangular translations preserve the countable product
of the actual additive-domain Haar probabilities.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein MeasureTheory
noncomputable section

/-- Left multiplication followed by canonical normalization into domain streams. -/
def adeleUnipotentDomainAction (g : unipotentCoefficientGroup Adeles)
    (d : ℕ → ellipticAdditiveDomain) : ℕ → ellipticAdditiveDomain :=
  adeleUnipotentNormalization (unipotentStreamProduct
    (unipotentCoefficientStreamEquiv Adeles g, fun n => (d n : Adeles)))

theorem continuous_adeleUnipotentDomainAction (g : unipotentCoefficientGroup Adeles) :
    Continuous (adeleUnipotentDomainAction g) := by
  have hd : Continuous fun d : ℕ → ellipticAdditiveDomain => (fun n => (d n : Adeles)) :=
    continuous_pi fun n => continuous_subtype_val.comp (continuous_apply n)
  have hp : Continuous fun d : ℕ → ellipticAdditiveDomain => unipotentStreamProduct
      (unipotentCoefficientStreamEquiv Adeles g, fun n => (d n : Adeles)) :=
    Continuous.comp (g := unipotentStreamProduct (R := Adeles))
      (f := fun d : ℕ → ellipticAdditiveDomain =>
        (unipotentCoefficientStreamEquiv Adeles g, fun n => (d n : Adeles)))
      continuous_unipotentStreamProduct (continuous_const.prodMk hd)
  exact continuous_adeleUnipotentNormalization.comp hp

/-- Extend a finite domain prefix by zero. -/
def unipotentDomainZeroExtension {N : ℕ} (d : Fin N → ellipticAdditiveDomain)
    (n : ℕ) : ellipticAdditiveDomain := if h : n < N then d ⟨n, h⟩ else 0

theorem continuous_unipotentDomainZeroExtension (N : ℕ) :
    Continuous (unipotentDomainZeroExtension (N := N)) := by
  classical
  apply continuous_pi
  intro n
  by_cases hn : n < N
  · simpa only [unipotentDomainZeroExtension, dif_pos hn] using
      (continuous_apply (⟨n, hn⟩ : Fin N) : Continuous fun d : Fin N → ellipticAdditiveDomain => d ⟨n, hn⟩)
  · simpa only [unipotentDomainZeroExtension, dif_neg hn] using
      (continuous_const : Continuous fun _ : Fin N → ellipticAdditiveDomain => (0 : ellipticAdditiveDomain))

/-- The current normalized value of a zero-extended strict prefix. -/
def adeleUnipotentDomainShift (g : unipotentCoefficientGroup Adeles) (n : ℕ)
    (d : Fin n → ellipticAdditiveDomain) : ellipticAdditiveDomain :=
  adeleUnipotentDomainAction g (unipotentDomainZeroExtension d) n

theorem continuous_adeleUnipotentDomainShift (g : unipotentCoefficientGroup Adeles) (n : ℕ) :
    Continuous (adeleUnipotentDomainShift g n) :=
  (continuous_apply n).comp
    ((continuous_adeleUnipotentDomainAction g).comp (continuous_unipotentDomainZeroExtension n))

private theorem streamProduct_coordinate (x y : ℕ → Adeles) (n : ℕ) :
    unipotentStreamProduct (x, y) n = x n + y n +
      unipotentTriangularCorrection n (fun i => x i.val) (fun i => y i.val) := by
  unfold unipotentStreamProduct
  rw [unipotentStream_mul]
  simp only [Equiv.apply_symm_apply]

/-- The normalized left action is an actual triangular translation with diagonal coefficient one. -/
theorem adeleUnipotentDomainAction_triangular (g : unipotentCoefficientGroup Adeles)
    (d : ℕ → ellipticAdditiveDomain) (n : ℕ) :
    adeleUnipotentDomainAction g d n =
      d n + adeleUnipotentDomainShift g n (fun i => d i.val) := by
  let y := unipotentDomainZeroExtension (fun i : Fin n => d i.val)
  let x := unipotentCoefficientStreamEquiv Adeles g
  let a := unipotentStreamProduct (x, fun k => (d k : Adeles))
  let b := unipotentStreamProduct (x, fun k => (y k : Adeles))
  have hy (k : ℕ) (hk : k < n) : y k = d k := by
    simp only [y, unipotentDomainZeroExtension, dif_pos hk]
  have hyn : y n = 0 := by
    simp only [y, unipotentDomainZeroExtension, dif_neg (show ¬ n < n by omega)]
  have hc (k : ℕ) (hk : k ≤ n) :
      (fun i : Fin k => (d i.val : Adeles)) = (fun i : Fin k => (y i.val : Adeles)) := by
    funext i
    exact congrArg (fun z : ellipticAdditiveDomain => (z : Adeles))
      (hy i.val (lt_of_lt_of_le i.isLt hk)).symm
  have hp : ∀ k, k < n → a k = b k := by
    intro k hk
    change unipotentStreamProduct (x, fun j => (d j : Adeles)) k =
      unipotentStreamProduct (x, fun j => (y j : Adeles)) k
    rw [streamProduct_coordinate, streamProduct_coordinate, hc k hk.le, hy k hk]
  have hn : a n = b n + (d n : Adeles) := by
    change unipotentStreamProduct (x, fun j => (d j : Adeles)) n =
      unipotentStreamProduct (x, fun j => (y j : Adeles)) n + (d n : Adeles)
    rw [streamProduct_coordinate, streamProduct_coordinate, hc n le_rfl, hyn]
    change x n + (d n : Adeles) + _ = (x n + 0 + _) + (d n : Adeles)
    abel
  have he := adeleUnipotentNormalization_coordinate_add a b n (d n) hp hn
  change adeleUnipotentDomainAction g d n = adeleUnipotentDomainAction g y n + d n at he
  exact he.trans (add_comm _ _)

/-- Product probability of the actual compact additive-domain coordinates. -/
def adeleUnipotentDomainProbability : Measure (ℕ → ellipticAdditiveDomain) :=
  Measure.infinitePi (fun _ : ℕ => ellipticDomainHaar)

instance adeleUnipotentDomainProbability_isProbability :
    IsProbabilityMeasure adeleUnipotentDomainProbability := by
  unfold adeleUnipotentDomainProbability
  infer_instance

/-- Every actual left matrix action preserves the normalized coefficient-domain probability. -/
theorem measurePreserving_adeleUnipotentDomainAction (g : unipotentCoefficientGroup Adeles) :
    MeasurePreserving (adeleUnipotentDomainAction g)
      adeleUnipotentDomainProbability adeleUnipotentDomainProbability := by
  have he : adeleUnipotentDomainAction g = triangularSequence (adeleUnipotentDomainShift g) := by
    funext d n
    exact adeleUnipotentDomainAction_triangular g d n
  rw [he]
  exact measurePreserving_triangularSequence ellipticDomainHaar (adeleUnipotentDomainShift g)
    (fun n => (continuous_adeleUnipotentDomainShift g n).measurable)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentDomainAction_triangular
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.measurePreserving_adeleUnipotentDomainAction
