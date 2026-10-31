import GaloisForLFunctions.AdelicKreinGeometry.TheGluingSquareIsSharp

/-!
# The glue sees the order of the pole

The archimedean glue `K ↦ K(|a|) − c|a|^{−1/2}|b|` is blind to a simple pole: adding the pole pair
`u^{1/2} + u^{−1/2}` at any real strength leaves the glued index unchanged
(`negIndex_archGlue_add_polePair`), and the glued pole pair alone has one square
(`negIndex_archGlue_smul_polePair`), the same as the glued zero datum (`negIndex_archGlue_zero`).

A double pole is seen. Its pair is the derivative of `u^α + u^{−α}` at `α = 1/2`,

  `D(u) = log u · (u^{1/2} − u^{−1/2})`  (`doublePole`).

* **The form** (`hermQuad_gram_doublePole`): at slopes `u_i`, with the moments `ℓ = Σ w_i u_i^{−1/2}`,
  `M = Σ w_i log u_i · u_i^{1/2}`, `L₁ = Σ w_i log u_i · u_i^{−1/2}`, `L₂ = Σ w_i u_i^{1/2}`, the form
  of `D` is `2 Re(ℓ̄M) − 2 Re(L̄₁L₂)`: two hyperbolic pairs, one of them on the boost coordinate.
* **On the boost hyperplane** only the pair `(L₁, L₂)` survives, `Q ≥ −|L₁ + L₂|²`, so
  `κ^{(½)}(D) ≤ 1` (`negIndexOn_gram_doublePole_le_one`); the slopes `1, 4` with weights `−1/2, 1`
  give `Q = −(3/2) log 4 < 0` (`boostPolarIndex_doublePole`: `κ^{(½)}(D) = 1`).
* **The double pole costs a square** (`negIndex_archGlue_doublePole`): `κ(D glued) = 2`, against
  `1` for a simple pole at any strength.

So the glue selects by the order of the pole: the boost hyperplane is exactly the null direction of
the simple pole pair, and the second-order term `log u` moves the pole off it.
-/

open Complex Finset
open scoped ComplexConjugate Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Coordinates of a positive slope -/

/-- `log u` for a positive slope. -/
def logSlope (u : posUnits) : ℝ := Real.log (((u : ℚˣ) : ℚ) : ℝ)

/-- `u^{1/2}` for a positive slope. -/
def halfPow (u : posUnits) : ℝ := (((u : ℚˣ) : ℚ) : ℝ) ^ (1 / 2 : ℝ)

theorem val_inv_mul_posUnits (u v : posUnits) :
    ((((u⁻¹ * v : posUnits) : ℚˣ) : ℚ) : ℝ) = ((((u : ℚˣ) : ℚ) : ℝ))⁻¹ * (((v : ℚˣ) : ℚ) : ℝ) := by
  simp [Units.val_mul, Units.val_inv_eq_inv_val]

theorem logSlope_inv_mul (u v : posUnits) : logSlope (u⁻¹ * v) = logSlope v - logSlope u := by
  rw [logSlope, val_inv_mul_posUnits, Real.log_mul (inv_ne_zero (posUnits_val_pos u).ne')
    (posUnits_val_pos v).ne', Real.log_inv, logSlope, logSlope]
  ring

theorem halfPow_inv_mul (u v : posUnits) : halfPow (u⁻¹ * v) = (halfPow u)⁻¹ * halfPow v := by
  rw [halfPow, val_inv_mul_posUnits, Real.mul_rpow (inv_nonneg.mpr (posUnits_val_pos u).le)
    (posUnits_val_pos v).le, Real.inv_rpow (posUnits_val_pos u).le]
  rfl

theorem logSlope_one : logSlope 1 = 0 := by simp [logSlope]

theorem halfPow_one : halfPow 1 = 1 := by simp [halfPow]

/-! ### The double pole pair -/

/-- **The double pole pair** `log u · (u^{1/2} − u^{−1/2})`, the `α`-derivative of `u^α + u^{−α}` at
`α = 1/2`. -/
def doublePole (u : posUnits) : ℂ := ((logSlope u * (halfPow u - (halfPow u)⁻¹) : ℝ) : ℂ)

theorem doublePole_inv_mul (u v : posUnits) :
    doublePole (u⁻¹ * v) = (((logSlope v - logSlope u) *
      ((halfPow u)⁻¹ * halfPow v - halfPow u * (halfPow v)⁻¹) : ℝ) : ℂ) := by
  rw [doublePole, logSlope_inv_mul, halfPow_inv_mul, mul_inv, inv_inv]

theorem isHermKernel_doublePole : IsHermKernel doublePole := fun u => by
  have h := doublePole_inv_mul u 1
  rw [mul_one] at h
  rw [h, doublePole, Complex.conj_ofReal, logSlope_one, halfPow_one]
  congr 1
  ring

/-- The moment `Σ w_i φ(u_i)` of a weight vector at slopes `u_i`. -/
def slopeMoment (φ : posUnits → ℝ) {n : ℕ} (u : Fin n → posUnits) (w : Fin n → ℂ) : ℂ :=
  ∑ a, w a * (φ (u a) : ℂ)

theorem boostMassU_eq_slopeMoment {n : ℕ} (u : Fin n → posUnits) (w : Fin n → ℂ) :
    boostMassU u w = slopeMoment (fun v => (halfPow v)⁻¹) u w := by
  simp only [boostMassU, LinearMap.coe_mk, AddHom.coe_mk, slopeMoment, halfPow]
  refine sum_congr rfl fun a _ => ?_
  rw [Real.rpow_neg (posUnits_val_pos _).le]

/-- **The form of the double pole**: `2 Re(ℓ̄M) − 2 Re(L̄₁L₂)`. -/
theorem hermQuad_gram_doublePole {n : ℕ} (u : Fin n → posUnits) (w : Fin n → ℂ) :
    hermQuad (gram doublePole u) w =
      (conj (slopeMoment (fun v => (halfPow v)⁻¹) u w) *
          slopeMoment (fun v => logSlope v * halfPow v) u w +
        conj (slopeMoment (fun v => logSlope v * halfPow v) u w) *
          slopeMoment (fun v => (halfPow v)⁻¹) u w -
        conj (slopeMoment (fun v => logSlope v * (halfPow v)⁻¹) u w) *
          slopeMoment halfPow u w -
        conj (slopeMoment halfPow u w) *
          slopeMoment (fun v => logSlope v * (halfPow v)⁻¹) u w).re := by
  rw [hermQuad_gram]
  congr 1
  simp only [slopeMoment, doublePole_inv_mul, map_sum, map_mul, Complex.conj_ofReal,
    Finset.sum_mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  push_cast
  ring

/-- On the boost hyperplane the form of the double pole is at least `−|L₁ + L₂|²`. -/
theorem neg_normSq_le_hermQuad_gram_doublePole {n : ℕ} (u : Fin n → posUnits) {w : Fin n → ℂ}
    (hw : boostMassU u w = 0) :
    -Complex.normSq (slopeMoment (fun v => logSlope v * (halfPow v)⁻¹) u w +
      slopeMoment halfPow u w) ≤ hermQuad (gram doublePole u) w := by
  rw [boostMassU_eq_slopeMoment] at hw
  rw [hermQuad_gram_doublePole, hw]
  set L₁ := slopeMoment (fun v => logSlope v * (halfPow v)⁻¹) u w
  set L₂ := slopeMoment halfPow u w
  simp only [map_zero, zero_mul, mul_zero, add_zero, Complex.sub_re, Complex.zero_re,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply, Complex.add_re,
    Complex.add_im]
  nlinarith [sq_nonneg L₁.re, sq_nonneg L₁.im, sq_nonneg L₂.re, sq_nonneg L₂.im]

/-- The rank-one form `−|Σ c_a z_a|²`. -/
private def negOuter {ι : Type*} (z : ι → ℂ) : Matrix ι ι ℂ := fun a b => -(conj (z a) * z b)

private theorem hermQuad_negOuter {ι : Type*} [Fintype ι] (z c : ι → ℂ) :
    hermQuad (negOuter z) c = -Complex.normSq (∑ a, c a * z a) := by
  have he : (Complex.normSq (∑ a, c a * z a) : ℂ) =
      ∑ a, ∑ b, conj (c a) * (conj (z a) * z b * c b) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, Finset.sum_mul_sum, map_mul]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have e : star c ⬝ᵥ negOuter z *ᵥ c = -(Complex.normSq (∑ a, c a * z a) : ℂ) := by
    rw [he, ← Finset.sum_neg_distrib]
    simp only [dotProduct, Matrix.mulVec, negOuter, Pi.star_apply, Complex.star_def,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  rw [hermQuad, e, Complex.neg_re, Complex.ofReal_re]

/-- **At most one square on the boost hyperplane.** -/
theorem negIndexOn_gram_doublePole_le_one {n : ℕ} (u : Fin n → posUnits) :
    negIndexOn (gram doublePole u) (LinearMap.ker (boostMassU u)) ≤ 1 := by
  set z : Fin n → ℂ := fun a => ((logSlope (u a) * (halfPow (u a))⁻¹ + halfPow (u a) : ℝ) : ℂ)
  let φ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun w => ∑ a, w a * z a
      map_add' := fun w w' => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun t w => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have h1 : negIndexOn (gram doublePole u) (LinearMap.ker (boostMassU u)) ≤
      negIndexOn (negOuter z) (LinearMap.ker (boostMassU u)) :=
    negIndexOn_le_of_hermQuad_le fun w hw => by
      rw [hermQuad_negOuter]
      have hz : ∑ a, w a * z a = slopeMoment (fun v => logSlope v * (halfPow v)⁻¹) u w +
          slopeMoment halfPow u w := by
        simp only [z, slopeMoment, ← Finset.sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        push_cast; ring
      rw [hz]
      exact neg_normSq_le_hermQuad_gram_doublePole u (LinearMap.mem_ker.mp hw)
  have h2 := negIndexOn_le_hermNegIndex (negOuter z) (LinearMap.ker (boostMassU u))
  have h3 := hermNegIndex_le_negIndexOn_ker_add_one (negOuter z) φ
  have h4 : negIndexOn (negOuter z) (LinearMap.ker φ) = 0 :=
    negIndexOn_eq_zero_of_nonneg fun w hw => by
      rw [hermQuad_negOuter, show ∑ a, w a * z a = 0 from LinearMap.mem_ker.mp hw]
      simp
  omega

theorem halfPow_posFour : halfPow posFour = 2 := by
  have h : (((posFour : ℚˣ) : ℚ) : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; norm_num [posFour]
  rw [halfPow, h, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem logSlope_posFour_pos : 0 < logSlope posFour := by
  have h : (((posFour : ℚˣ) : ℚ) : ℝ) = 4 := by norm_num [posFour]
  rw [logSlope, h]
  exact Real.log_pos (by norm_num)

/-- **The boost-polar index of the double pole is one.** -/
theorem boostPolarIndex_doublePole : boostPolarIndex doublePole = 1 := by
  refine le_antisymm (iSup₂_le fun n u => by exact_mod_cast negIndexOn_gram_doublePole_le_one u) ?_
  -- slopes `1, 4`, weights `−1/2, 1`: `ℓ = 0` and `Q = −2 · (log 4 / 2) · (3/2)`
  set u : Fin 2 → posUnits := ![1, posFour]
  set w : Fin 2 → ℂ := ![-(1 / 2), 1]
  have hℓ : boostMassU u w = 0 := by
    rw [boostMassU_eq_slopeMoment]
    simp [slopeMoment, u, w, Fin.sum_univ_two, halfPow_one, halfPow_posFour]
  have hneg : hermQuad (gram doublePole u) w < 0 := by
    rw [hermQuad_gram_doublePole, ← boostMassU_eq_slopeMoment, hℓ]
    have hL₁ : slopeMoment (fun v => logSlope v * (halfPow v)⁻¹) u w =
        ((logSlope posFour / 2 : ℝ) : ℂ) := by
      simp [slopeMoment, u, w, Fin.sum_univ_two, logSlope_one, halfPow_posFour]
      ring
    have hL₂ : slopeMoment halfPow u w = ((3 / 2 : ℝ) : ℂ) := by
      simp [slopeMoment, u, w, Fin.sum_univ_two, halfPow_one, halfPow_posFour]
      norm_num
    rw [hL₁, hL₂]
    simp only [map_zero, zero_mul, mul_zero, add_zero, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Complex.sub_re, Complex.zero_re, Complex.ofReal_re]
    nlinarith [logSlope_posFour_pos]
  exact le_trans (by exact_mod_cast one_le_negIndexOn hℓ hneg)
    (negIndexOn_le_boostPolarIndex doublePole u)

/-- **The glue sees a double pole**: glued to the archimedean successor, `D` has two squares. -/
theorem negIndex_archGlue_doublePole {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue doublePole c) = 2 := by
  rw [negIndex_archGlue_eq isHermKernel_doublePole hc, boostPolarIndex_doublePole]
  rfl

/-! ### The simple pole costs one square at any strength -/

theorem isHermKernel_zero_posUnits : IsHermKernel fun _ : posUnits => (0 : ℂ) := fun _ => by simp

theorem boostPolarIndex_zero : boostPolarIndex (fun _ : posUnits => (0 : ℂ)) = 0 :=
  nonpos_iff_eq_zero.mp (iSup₂_le fun n u => by
    rw [negIndexOn_eq_zero_of_nonneg fun w _ => by simp [hermQuad_gram]]
    rfl)

/-- The zero datum glued to the archimedean successor keeps the successor's square. -/
theorem negIndex_archGlue_zero {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (fun _ => 0) c) = 1 := by
  rw [negIndex_archGlue_eq isHermKernel_zero_posUnits hc, boostPolarIndex_zero, zero_add]

/-- **A simple pole costs nothing**: the pole pair at any real strength glued at `∞` has one square. -/
theorem negIndex_archGlue_smul_polePair (t : ℝ) {c : ℝ} (hc : 0 < c) :
    negIndex (archGlue (fun u => t * polePair u) c) = 1 := by
  have e : (fun u => (t : ℂ) * polePair u) = fun u => (fun _ : posUnits => (0 : ℂ)) u + t * polePair u :=
    funext fun u => (zero_add _).symm
  rw [e, negIndex_archGlue_add_polePair isHermKernel_zero_posUnits t hc, negIndex_archGlue_zero hc]

end GaloisForLFunctions.AdelicKreinGeometry

#print axioms GaloisForLFunctions.AdelicKreinGeometry.negIndex_archGlue_doublePole
#print axioms GaloisForLFunctions.AdelicKreinGeometry.negIndex_archGlue_smul_polePair
