import GaloisForLFunctions.HTGeometry.ProductLawLowSubalgebra

/-!
# Bell iterates in the rational model

If `δ H = A·H` then every jet of `H` is `H` times a Bell iterate of `A`, defined by the recursion
`B_0 = 1`, `B_(i+1) = δB_i + A·B_i`.  Both objects of the product law are of this shape: the head
product has multiplier the logarithmic sum, and the full jet has multiplier that sum plus the
terminal factor's own logarithmic derivative.

So all jets of the law factor as (the object) × (a Bell iterate of a multiplier), with the multiplier
built from strictly lower data — the decomposition the height induction runs on.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-- The Bell iterates of a multiplier: `B_0 = 1`, `B_(i+1) = δB_i + A·B_i`. -/
noncomputable def prodBell (A : CascadeField) : ℕ → CascadeField
  | 0 => 1
  | (i + 1) => prodDerivation Q v (prodBell A i) + A * prodBell A i

@[simp] theorem prodBell_zero (A : CascadeField) : prodBell Q v A 0 = 1 := rfl

theorem prodBell_succ (A : CascadeField) (i : ℕ) :
    prodBell Q v A (i + 1) = prodDerivation Q v (prodBell Q v A i) + A * prodBell Q v A i := rfl

/-- **The jets of a logarithmically linear element.** -/
theorem iterate_prodDerivation_of_logLinear {H A : CascadeField}
    (hH : prodDerivation Q v H = A * H) (i : ℕ) :
    ((prodDerivation Q v : CascadeField → CascadeField)^[i]) H = H * prodBell Q v A i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.leibniz, hH, prodBell_succ]
      simp only [smul_eq_mul]
      ring

theorem prodBell_mem_lowSub {m : ℕ} {A : CascadeField} (hA : A ∈ lowSub Q v m) (i : ℕ) :
    prodBell Q v A i ∈ lowSub Q v m := by
  induction i with
  | zero => simp [prodBell]
  | succ i ih =>
      rw [prodBell_succ]
      exact Subalgebra.add_mem _ (prodDerivation_mem_lowSub Q v ih) (Subalgebra.mul_mem _ hA ih)

/-! ## The two multipliers -/

/-- The full logarithmic multiplier of a coordinate jet. -/
noncomputable def totalLog (k : ℕ) : CascadeField :=
  logSum Q v k + logFactor (v k) k * prodJet Q v k

theorem totalLog_mem_lowSub {k m : ℕ} (h : k ≤ m) : totalLog Q v k ∈ lowSub Q v m :=
  Subalgebra.add_mem _ (logSum_mem_lowSub Q v h)
    (Subalgebra.mul_mem _ (logFactorV_mem_lowSub Q v h) (prodJet_mem_lowSub Q v h))

/-- **The head product is logarithmically linear.** -/
theorem prodDerivation_prodHead' {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (k : ℕ) :
    prodDerivation Q v (prodHead Q k) = logSum Q v k * prodHead Q k := by
  rw [prodDerivation_prodHead hQ]
  ring

/-- **The coordinate jet is logarithmically linear.** -/
theorem prodDerivation_prodJet' {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (k : ℕ) :
    prodDerivation Q v (prodJet Q v k) = totalLog Q v k * prodJet Q v k := by
  rw [prodDerivation_prodJet hQ, totalLog]
  ring

/-- **The jets of the head product.** -/
theorem iterate_prodHead {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (k i : ℕ) :
    ((prodDerivation Q v : CascadeField → CascadeField)^[i]) (prodHead Q k)
      = prodHead Q k * prodBell Q v (logSum Q v k) i :=
  iterate_prodDerivation_of_logLinear Q v (prodDerivation_prodHead' v hQ k) i

/-- **The jets of a coordinate jet.** -/
theorem iterate_prodJet {Q : ℕ → Polynomial ℂ} (hQ : ∀ j, Q j ≠ 0) (k i : ℕ) :
    ((prodDerivation Q v : CascadeField → CascadeField)^[i]) (prodJet Q v k)
      = prodJet Q v k * prodBell Q v (totalLog Q v k) i :=
  iterate_prodDerivation_of_logLinear Q v (prodDerivation_prodJet' v hQ k) i

/-! ## Splitting off the newest coordinate -/

/-- The logarithmic sum grows by one term, carrying the newest coordinate's factor. -/
theorem logSum_succ' (k : ℕ) :
    logSum Q v (k + 1) = logSum Q v k + logFactor (Q k) k * prodJet Q v k :=
  logSum_succ Q v k

/-- **The newest coordinate enters the new logarithmic sum only through the newest jet.**  Every
higher coordinate derivation annihilates the older part. -/
theorem fpderiv_logSum_succ {k m : ℕ} (hk : k ≤ m) (j : ℕ) (hj : m < j) :
    fpderiv j (logSum Q v k) = 0 :=
  fpderiv_eq_zero_of_mem_lowSub Q v hj (logSum_mem_lowSub Q v hk)

theorem fpderiv_prodBell_of_low {m j : ℕ} (hj : m < j) {A : CascadeField}
    (hA : A ∈ lowSub Q v m) (i : ℕ) :
    fpderiv j (prodBell Q v A i) = 0 :=
  fpderiv_eq_zero_of_mem_lowSub Q v hj (prodBell_mem_lowSub Q v hA i)

theorem fpderiv_iterate_of_low {m j : ℕ} (hj : m < j) {P : CascadeField}
    (hP : P ∈ lowSub Q v m) (i : ℕ) :
    fpderiv j (((prodDerivation Q v : CascadeField → CascadeField)^[i]) P) = 0 :=
  fpderiv_eq_zero_of_mem_lowSub Q v hj (iterate_prodDerivation_mem_lowSub Q v hP i)

end GaloisForLFunctions.HTGeometry
