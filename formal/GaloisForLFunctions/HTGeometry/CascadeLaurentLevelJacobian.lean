import GaloisForLFunctions.HTGeometry.LaurentLeadCalculus
import GaloisForLFunctions.HTGeometry.LaurentOutputJacobianLead

/-!
# The derivations of one Laurent layer of the cascade tower and the Jacobian descent

Let `K` be a field over `ℂ` with a time derivation `δ_K` and coordinate derivations `∂_K`.  A layer
`K((t))` in which the new state is `X = t^(-N)` and the logarithmic velocity of `X` is a series `A`
of order zero carries

* the time derivation `δ = δ_K (coefficientwise) - (A/N) t d/dt`, so that `δ(t^(-N)) = A t^(-N)`;
* the coordinate derivations `∂_i` (coefficientwise) and the new one `∂ = -(1/N) t^N t d/dt`.

Their boundary-coefficient laws are those of `outputJacobian_det_ne_zero_of_hasLead` with
`a₀ = -A₀/N` and `κ = -1/N`.  For `Y = δV/V + λ W` with `W` of negative degree `w` and boundary
coefficient `κ_W A₀` (`κ_W, λ` complex), the lower Jacobian that governs `det(∂_i δ^r Y)` is that
of `δA₀/A₀ + (-w/N) A₀`: the same shape one level down.  This is the descent step of the cascade's
exact-order argument.
-/

open HahnSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LaurentDerivation

variable {K : Type*} [Field K] [Algebra ℂ K]

attribute [local instance 2000] Algebra.toModule

namespace LaurentDerivation

/-- A Laurent multiple `a D` of a derivation of `K((t))`. -/
def mulDerivation (a : LaurentSeries K) (D : LaurentComplexDerivation K) :
    LaurentComplexDerivation K where
  toFun x := a * D x
  map_add' x y := by rw [map_add, mul_add]
  map_smul' c x := by
    rw [RingHom.id_apply, D.map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  map_one_eq_zero' := by
    change a * D 1 = 0
    rw [D.map_one_eq_zero, mul_zero]
  leibniz' x y := by
    change a * D (x * y) = x • (a * D y) + y • (a * D x)
    rw [D.leibniz]
    simp only [smul_eq_mul]
    ring

@[simp] theorem mulDerivation_apply (a : LaurentSeries K) (D : LaurentComplexDerivation K)
    (x : LaurentSeries K) : mulDerivation a D x = a * D x := rfl

/-- The time derivation of a layer: `δ_K` on coefficients minus `(A/N) t d/dt`. -/
def levelTime (δK : Derivation ℂ K K) (N : ℕ) (A : LaurentSeries K) :
    LaurentComplexDerivation K :=
  coeffDerivation δK + mulDerivation (HahnSeries.C (-(N : K)⁻¹) * A) eulerDerivation

theorem levelTime_apply (δK : Derivation ℂ K K) (N : ℕ) (A x : LaurentSeries K) :
    levelTime δK N A x =
      coeffDerivation δK x + HahnSeries.C (-(N : K)⁻¹) * A * eulerDerivation x := rfl

/-- The coordinate derivations of a layer: the lower ones coefficientwise, the new one
`-(1/N) t^N t d/dt`. -/
def levelCoord {m : ℕ} (pK : Fin m → Derivation ℂ K K) (N : ℕ) :
    Fin (m + 1) → LaurentComplexDerivation K :=
  Fin.lastCases (mulDerivation (single (N : ℤ) (-(N : K)⁻¹)) eulerDerivation)
    (fun i => coeffDerivation (pK i))

@[simp] theorem levelCoord_castSucc {m : ℕ} (pK : Fin m → Derivation ℂ K K) (N : ℕ) (i : Fin m) :
    levelCoord pK N i.castSucc = coeffDerivation (pK i) := by
  simp [levelCoord]

@[simp] theorem levelCoord_last {m : ℕ} (pK : Fin m → Derivation ℂ K K) (N : ℕ) :
    levelCoord pK N (Fin.last m) =
      mulDerivation (single (N : ℤ) (-(N : K)⁻¹)) eulerDerivation := by
  simp [levelCoord]

end LaurentDerivation

/-! ## Boundary-coefficient laws -/

theorem HasLead.levelTime {δK : Derivation ℂ K K} {N : ℕ} {A : LaurentSeries K}
    {A₀ : K} (hA : HasLead A 0 A₀) {f : LaurentSeries K} {d : ℤ} {c : K} (hf : HasLead f d c) :
    HasLead (levelTime δK N A f) d (δK c + (d : K) * (-A₀ / N) * c) := by
  have h1 := hf.coeffDerivation (D := δK)
  have h2 := (hA.mul_const (-(N : K)⁻¹)).mul_euler hf
  rw [levelTime_apply]
  convert h1.add h2 using 1
  ring

theorem HasLead.levelCoord_castSucc {m : ℕ} (pK : Fin m → Derivation ℂ K K) (N : ℕ) (i : Fin m)
    {f : LaurentSeries K} {d : ℤ} {c : K} (hf : HasLead f d c) :
    HasLead (levelCoord pK N i.castSucc f) d (pK i c) := by
  rw [LaurentDerivation.levelCoord_castSucc]
  exact hf.coeffDerivation

theorem HasLead.levelCoord_last {m : ℕ} (pK : Fin m → Derivation ℂ K K) (N : ℕ)
    {f : LaurentSeries K} {d : ℤ} {c : K} (hf : HasLead f d c) :
    HasLead (levelCoord pK N (Fin.last m) f) (d + N) (-(N : K)⁻¹ * ((d : K) * c)) := by
  rw [LaurentDerivation.levelCoord_last, mulDerivation_apply]
  exact hf.single_mul_euler (N : ℤ) (-(N : K)⁻¹)

/-! ## Values on constants and on the new state -/

theorem coeffDerivation_C (D : Derivation ℂ K K) (c : K) :
    coeffDerivation D (HahnSeries.C c) = HahnSeries.C (D c) := by
  refine HahnSeries.ext (funext fun n => ?_)
  rw [coeff_coeffDerivation, C_apply, C_apply, coeff_single, coeff_single]
  split_ifs <;> simp

theorem eulerDerivation_C (c : K) : eulerDerivation (HahnSeries.C c : LaurentSeries K) = 0 := by
  refine HahnSeries.ext (funext fun n => ?_)
  rw [coeff_eulerDerivation, C_apply, coeff_single, HahnSeries.coeff_zero]
  split_ifs with h
  · subst h
    simp
  · simp

theorem levelTime_C (δK : Derivation ℂ K K) (N : ℕ) (A : LaurentSeries K) (c : K) :
    levelTime δK N A (HahnSeries.C c) = HahnSeries.C (δK c) := by
  rw [levelTime_apply, coeffDerivation_C, eulerDerivation_C, mul_zero, add_zero]

theorem levelCoord_castSucc_C {m : ℕ} (pK : Fin m → Derivation ℂ K K) (N : ℕ) (i : Fin m)
    (c : K) : levelCoord pK N i.castSucc (HahnSeries.C c) = HahnSeries.C (pK i c) := by
  rw [levelCoord_castSucc, coeffDerivation_C]

theorem levelCoord_last_C {m : ℕ} (pK : Fin m → Derivation ℂ K K) (N : ℕ) (c : K) :
    levelCoord pK N (Fin.last m) (HahnSeries.C c) = 0 := by
  rw [levelCoord_last, mulDerivation_apply, eulerDerivation_C, mul_zero]

/-- The time derivation of the new state `t^(-N)` is `A t^(-N)`. -/
theorem levelTime_single_neg {N : ℕ} (hN : N ≠ 0) (δK : Derivation ℂ K K)
    (A : LaurentSeries K) :
    levelTime δK N A (single (-(N : ℤ)) 1) = A * single (-(N : ℤ)) 1 := by
  have hcoeff : coeffDerivation δK (single (-(N : ℤ)) (1 : K)) = 0 := by
    refine HahnSeries.ext (funext fun n => ?_)
    rw [coeff_coeffDerivation, coeff_single, HahnSeries.coeff_zero]
    split_ifs <;> simp
  have heuler : eulerDerivation (single (-(N : ℤ)) (1 : K)) =
      HahnSeries.C (-(N : K)) * single (-(N : ℤ)) 1 := by
    refine HahnSeries.ext (funext fun n => ?_)
    rw [coeff_eulerDerivation, C_mul_eq_smul, HahnSeries.coeff_smul, coeff_single,
      smul_eq_mul]
    split_ifs with h
    · rw [h]
      push_cast
      ring
    · simp
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hC : (HahnSeries.C (-(N : K)⁻¹) : LaurentSeries K) * HahnSeries.C (-(N : K)) = 1 := by
    rw [← map_mul, show -(N : K)⁻¹ * -(N : K) = 1 by field_simp, map_one]
  rw [levelTime_apply, hcoeff, heuler, zero_add]
  linear_combination (A * single (-(N : ℤ)) (1 : K)) * hC

/-! ## The Jacobian descent -/

/-- The logarithmic derivative `δV/V` plus a complex multiple of a series `W` of negative degree has
the boundary coefficient of the multiple: `δV/V` has degree at least zero. -/
theorem hasLead_levelTime_logDeriv_add (δK : Derivation ℂ K K) (N : ℕ) {A : LaurentSeries K}
    {A₀ : K} (hA : HasLead A 0 A₀) {V : LaurentSeries K} (hV : V ≠ 0) {W : LaurentSeries K}
    {w : ℤ} {cW : K} (hW : HasLead W w cW) (hw : w < 0) (lam : K) :
    HasLead (levelTime δK N A V * V⁻¹ + HahnSeries.C lam * W) w (lam * cW) := by
  have hV0 : V.coeff V.order ≠ 0 := mt coeff_order_eq_zero.mp hV
  have hlog := (HasLead.levelTime (δK := δK) (N := N) hA (hasLead_order V)).mul_inv_of_same
    (hasLead_order V) hV0
  rw [add_comm]
  exact (hW.mul_const lam).add_of_vanishing (hlog.vanishing_le hw)

/-- **Base of the descent.**  With one coordinate derivation, the Jacobian of a series of nonzero
degree and nonzero boundary coefficient is nonzero. -/
theorem levelJacobian_one_ne_zero (δK : Derivation ℂ K K) {N : ℕ} (hN : N ≠ 0)
    (A : LaurentSeries K) (pK : Fin 0 → Derivation ℂ K K) {Y : LaurentSeries K} {d : ℤ} {h : K}
    (hY : HasLead Y d h) (hh : h ≠ 0) (hd : d ≠ 0) :
    (Matrix.of fun i j : Fin 1 => levelCoord pK N j (((levelTime δK N A : LaurentSeries K →
      LaurentSeries K)^[(i : ℕ)]) Y)).det ≠ 0 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  rw [Matrix.det_fin_one, Matrix.of_apply]
  have hl := hY.levelCoord_last pK N
  have hnz : -(N : K)⁻¹ * ((d : K) * h) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr hN)))
      (mul_ne_zero (Int.cast_ne_zero.mpr hd) hh)
  exact hl.ne_zero hnz

/-- **The descent step.**  The Jacobian of `δV/V + λW`, `W` of negative degree `w` with boundary
coefficient `κ_W A₀`, is nonzero as soon as the lower Jacobian of `δA₀/A₀ + (-w/N) A₀` is. -/
theorem levelJacobian_step_ne_zero {n : ℕ} (δK : Derivation ℂ K K)
    (pK : Fin (n + 1) → Derivation ℂ K K) {N : ℕ} (hN : N ≠ 0) {A : LaurentSeries K} {A₀ : K}
    (hA : HasLead A 0 A₀) (hA₀ : A₀ ≠ 0) {W : LaurentSeries K} {w : ℤ} (hw : w < 0) (κW : ℂ)
    (hκW : κW ≠ 0) (hW : HasLead W w (algebraMap ℂ K κW * A₀))
    (hlower : (Matrix.of fun i j : Fin (n + 1) => pK j (((δK : K → K)^[(i : ℕ)])
      (δK A₀ / A₀ + ((-w : ℤ) : K) / N * A₀))).det ≠ 0)
    {V : LaurentSeries K} (hV : V ≠ 0) (lam : ℂ) (hlam : lam ≠ 0) :
    (Matrix.of fun i j : Fin (n + 2) => levelCoord pK N j (((levelTime δK N A : LaurentSeries K →
      LaurentSeries K)^[(i : ℕ)]) (levelTime δK N A V * V⁻¹ +
        HahnSeries.C (algebraMap ℂ K lam) * W))).det ≠ 0 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set c : K := algebraMap ℂ K (lam * κW) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, map_eq_zero_iff _ (algebraMap ℂ K).injective]
    exact mul_ne_zero hlam hκW
  have hY := hasLead_levelTime_logDeriv_add δK N hA hV hW hw (algebraMap ℂ K lam)
  have hh : algebraMap ℂ K lam * (algebraMap ℂ K κW * A₀) = c * A₀ := by
    rw [hc, map_mul, mul_assoc]
  rw [hh] at hY
  let pK' : Fin (n + 2) → Derivation ℂ K K := Fin.lastCases 0 pK
  refine outputJacobian_det_ne_zero_of_hasLead δK pK' (levelTime δK N A)
    (fun j => ⇑(levelCoord pK N j)) (-A₀ / N) (-(N : K)⁻¹) N
    (fun f d c' hf => HasLead.levelTime hA hf) (fun j f d c' hf => ?_)
    (fun f d c' hf => hf.levelCoord_last pK N) hY (mul_ne_zero hc0 hA₀)
    (neg_ne_zero.mpr (inv_ne_zero hN')) (Int.cast_ne_zero.mpr hw.ne) ?_
  · simp only [pK', Fin.lastCases_castSucc]
    exact hf.levelCoord_castSucc pK N j
  · have hδc : δK (c * A₀) = c * δK A₀ := by
      rw [hc, ← Algebra.smul_def, Derivation.map_smul, Algebra.smul_def]
    have hU : δK (c * A₀) / (c * A₀) + (w : K) * (-A₀ / N) =
        δK A₀ / A₀ + ((-w : ℤ) : K) / N * A₀ := by
      rw [hδc]
      push_cast
      field_simp
    rw [hU]
    convert hlower using 2
    ext i j
    simp only [derivationLowerJetJacobian, Matrix.of_apply, pK', Fin.lastCases_castSucc]

/-- **The top of the descent.**  The Jacobian of the new state `t^(-N)` is nonzero as soon as the
lower Jacobian of the constant term `A₀` of its logarithmic velocity is. -/
theorem levelJacobian_top_ne_zero {n : ℕ} (δK : Derivation ℂ K K)
    (pK : Fin (n + 1) → Derivation ℂ K K) {N : ℕ} (hN : N ≠ 0) {A : LaurentSeries K} {A₀ : K}
    (hA : HasLead A 0 A₀)
    (hlower : (Matrix.of fun i j : Fin (n + 1) => pK j (((δK : K → K)^[(i : ℕ)]) A₀)).det ≠ 0) :
    (Matrix.of fun i j : Fin (n + 2) => levelCoord pK N j (((levelTime δK N A : LaurentSeries K →
      LaurentSeries K)^[(i : ℕ)]) (single (-(N : ℤ)) 1))).det ≠ 0 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let pK' : Fin (n + 2) → Derivation ℂ K K := Fin.lastCases 0 pK
  refine outputJacobian_det_ne_zero_of_hasLead δK pK' (levelTime δK N A)
    (fun j => ⇑(levelCoord pK N j)) (-A₀ / N) (-(N : K)⁻¹) N
    (fun f d c' hf => HasLead.levelTime hA hf) (fun j f d c' hf => ?_)
    (fun f d c' hf => hf.levelCoord_last pK N) (hasLead_single (-(N : ℤ)) (1 : K)) one_ne_zero
    (neg_ne_zero.mpr (inv_ne_zero hN')) (by push_cast; exact neg_ne_zero.mpr hN') ?_
  · simp only [pK', Fin.lastCases_castSucc]
    exact hf.levelCoord_castSucc pK N j
  · have hU : δK 1 / 1 + (((-(N : ℤ)) : ℤ) : K) * (-A₀ / N) = A₀ := by
      rw [Derivation.map_one_eq_zero]
      push_cast
      field_simp
      ring
    rw [hU]
    convert hlower using 2
    ext i j
    simp only [derivationLowerJetJacobian, Matrix.of_apply, pK', Fin.lastCases_castSucc]

end

end GaloisForLFunctions.HTGeometry
