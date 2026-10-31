import GaloisForLFunctions.AdelicKreinGeometry.EveryPlaceCarriesAPoleSuccessorState

/-!
# The shell decomposition of a pole–successor form

At a nonarchimedean place `v` two points *agree to radius `r`* when `|x − y|_v ≤ r`; the agreement
shells of radius `r` are the classes of `K` modulo the ball `{|z|_v ≤ r}`.

* **Shell identity** (`hermQuad_gram_negUltra_eq`): for every `R` bounding the distances,
  `Q_{−|·|_v}(c) = −R |Σ c|² + ∫_0^R Σ_B |Σ_{x_a ∈ B} c_a|² dr`, the inner sum over the shells `B` of
  radius `r` (`shellSquares`).
* **The pole–successor form** (`hermQuad_gram_poleSuccessor_negUltra_eq`):
  `Q_Φ(w) = 2 Re(X̄Y) − cR|X|² + c ∫_0^R Σ_B |Σ_{b_g ∈ B} w_g |a_g|_v^{−1/2}|² dr`.

So the form of the local pole–successor state is a hyperbolic pair renormalized by the counterterm
`cR` on the pole coordinate `X`, plus squares indexed by agreement shells. The counterterm runs with
the cutoff `R`, as the matched counterterm `log N − γ` runs with the horizon; for every `R` the
renormalized pair `2 Re(X̄Y) − cR|X|²` has signature `(1, 1)`, and on its null hyperplane `X = 0` only
the shell squares remain (`hermQuad_gram_poleSuccessor_negUltra_of_mass_zero`): positivity off the
pole is an identity.
-/

open Complex Finset MeasureTheory
open scoped ComplexConjugate Classical
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}

/-- The ball of radius `max r 0`. -/
def ballOf (hv : IsUltra v) (r : ℝ) : AddSubgroup K := ballSubgroup hv (le_max_right r 0)

/-- **Shell squares** of radius `r`: `Σ_B |Σ_{y_a ∈ B} c_a|²` over the classes modulo the ball. -/
def shellSquares (hv : IsUltra v) {n : ℕ} (y : Fin n → K) (c : Fin n → ℂ) (r : ℝ) : ℝ :=
  ∑ B ∈ univ.image (fun a => (QuotientAddGroup.mk (y a) : K ⧸ ballOf hv r)),
    normSq (∑ b ∈ univ.filter (fun b => (QuotientAddGroup.mk (y b) : K ⧸ ballOf hv r) = B), c b)

/-- The shell squares are the ball form: `Σ_{a,b} Re(c̄_a c_b) 1[|y_b − y_a|_v ≤ r]`. -/
theorem shellSquares_eq (hv : IsUltra v) {n : ℕ} (y : Fin n → K) (c : Fin n → ℂ) {r : ℝ}
    (hr : 0 ≤ r) : shellSquares hv y c r =
      ∑ a, ∑ b, (conj (c a) * c b).re * (Set.Ici (v (-y a + y b))).indicator (fun _ => (1 : ℝ)) r := by
  rw [shellSquares, ← re_sum_ite_eq_sum_normSq, Complex.re_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine sum_congr rfl fun b _ => ?_
  have e : ((QuotientAddGroup.mk (y a) : K ⧸ ballOf hv r) = QuotientAddGroup.mk (y b)) ↔
      v (-y a + y b) ≤ r := by
    rw [QuotientAddGroup.eq]
    show v (-y a + y b) ≤ max r 0 ↔ _
    rw [max_eq_left hr]
  simp only [Set.indicator, Set.mem_Ici]
  by_cases h : v (-y a + y b) ≤ r
  · rw [if_pos (e.mpr h), if_pos h, mul_one, mul_one]
  · rw [if_neg (fun h' => h (e.mp h')), if_neg h, mul_zero, mul_zero, Complex.zero_re]

/-- **The shell identity** for `−|·|_v`. -/
theorem hermQuad_gram_negUltra_eq (hv : IsUltra v) {n : ℕ} (x : Fin n → Multiplicative K)
    (c : Fin n → ℂ) {R : ℝ}
    (hR : ∀ a b, v (-Multiplicative.toAdd (x a) + Multiplicative.toAdd (x b)) ≤ R) :
    hermQuad (gram (negUltra v) x) c = -R * normSq (∑ a, c a) +
      ∫ r in Set.Icc 0 R, shellSquares hv (fun a => Multiplicative.toAdd (x a)) c r := by
  set y : Fin n → K := fun a => Multiplicative.toAdd (x a)
  set z : Fin n → Fin n → ℝ := fun a b => v (-y a + y b)
  set ρ : Fin n → Fin n → ℝ := fun a b => (conj (c a) * c b).re
  have hz0 : ∀ a b, 0 ≤ z a b := fun a b => v.nonneg _
  have hmass : ∑ a, ∑ b, ρ a b = normSq (∑ a, c a) := by
    simp only [ρ, ← Complex.re_sum]
    rw [← sum_mul_sum, ← map_sum, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hform : hermQuad (gram (negUltra v) x) c =
      ∑ a, ∑ b, ρ a b * (R - z a b) - R * ∑ a, ∑ b, ρ a b := by
    rw [hermQuad_gram, Complex.re_sum]
    simp_rw [Complex.re_sum]
    have e : ∀ a b, (conj (c a) * negUltra v ((x a)⁻¹ * x b) * c b).re = ρ a b * (R - z a b) -
        R * ρ a b := fun a b => by
      simp only [negUltra, toAdd_mul, toAdd_inv, z, y, ρ]
      rw [show conj (c a) * -((v (-Multiplicative.toAdd (x a) + Multiplicative.toAdd (x b)) : ℝ) : ℂ)
          * c b = ((-v (-Multiplicative.toAdd (x a) + Multiplicative.toAdd (x b)) : ℝ) : ℂ) *
            (conj (c a) * c b) by push_cast; ring, Complex.re_ofReal_mul]
      ring
    simp_rw [e, sum_sub_distrib, ← mul_sum]
  have hlayer : ∑ a, ∑ b, ρ a b * (R - z a b) =
      ∫ r in Set.Icc 0 R, ∑ a, ∑ b, ρ a b * (Set.Ici (z a b)).indicator (fun _ => (1 : ℝ)) r := by
    have hint : ∀ a b, Integrable (fun r => ρ a b * (Set.Ici (z a b)).indicator (fun _ => (1 : ℝ)) r)
        (volume.restrict (Set.Icc 0 R)) := fun a b =>
      ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul _
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
    refine sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint a b]
    refine sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_indicator_Ici_eq (hz0 a b) (hR a b)]
  have hcongr : ∫ r in Set.Icc 0 R, ∑ a, ∑ b, ρ a b * (Set.Ici (z a b)).indicator (fun _ => (1 : ℝ)) r =
      ∫ r in Set.Icc 0 R, shellSquares hv y c r :=
    setIntegral_congr_fun measurableSet_Icc fun r hr => (shellSquares_eq hv y c hr.1).symm
  rw [hform, hlayer, hcongr, hmass]
  ring

/-- **The shell decomposition of the local pole–successor form**: a hyperbolic pair renormalized by
the counterterm `cR` on the pole coordinate, plus shell squares. -/
theorem hermQuad_gram_poleSuccessor_negUltra_eq (hv : IsUltra v) (c : ℝ) {n : ℕ}
    (g : Fin n → AffineGroupOf K) (w : Fin n → ℂ) {R : ℝ}
    (hR : ∀ a b, v (-shiftOf (g a) + shiftOf (g b)) ≤ R) :
    hermQuad (gram (poleSuccessor v 1 fun m => (c : ℂ) * negUltra v m) g) w =
      (conj (∑ a, boostWeights v 1 g w a) * ∑ a, w a * slopePow v 1 (g a) +
        conj (∑ a, w a * slopePow v 1 (g a)) * ∑ a, boostWeights v 1 g w a).re -
      c * R * normSq (∑ a, boostWeights v 1 g w a) +
      c * ∫ r in Set.Icc 0 R, shellSquares hv (fun a => shiftOf (g a)) (boostWeights v 1 g w) r := by
  rw [hermQuad_gram_poleSuccessor (isConformal_negUltra v c)]
  have e : gram (fun m => (c : ℂ) * negUltra v m) (shifts g) =
      (c : ℂ) • gram (negUltra v) (shifts g) := by
    ext a b; simp [gram]
  rw [e, hermQuad_smul, hermQuad_gram_negUltra_eq hv (shifts g) _ (fun a b => by
    simpa [shifts] using hR a b)]
  simp only [shifts, toAdd_ofAdd]
  ring

/-- On the null hyperplane `X = 0` of the pole coordinate only the shell squares remain. -/
theorem hermQuad_gram_poleSuccessor_negUltra_of_mass_zero (hv : IsUltra v) (c : ℝ) {n : ℕ}
    (g : Fin n → AffineGroupOf K) (w : Fin n → ℂ) {R : ℝ}
    (hR : ∀ a b, v (-shiftOf (g a) + shiftOf (g b)) ≤ R) (hX : ∑ a, boostWeights v 1 g w a = 0) :
    hermQuad (gram (poleSuccessor v 1 fun m => (c : ℂ) * negUltra v m) g) w =
      c * ∫ r in Set.Icc 0 R, shellSquares hv (fun a => shiftOf (g a)) (boostWeights v 1 g w) r := by
  rw [hermQuad_gram_poleSuccessor_negUltra_eq hv c g w hR, hX]
  simp

end GaloisForLFunctions.AdelicKreinGeometry
