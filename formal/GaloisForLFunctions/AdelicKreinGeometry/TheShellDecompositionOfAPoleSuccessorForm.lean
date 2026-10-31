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
* **The real place** (`hermQuad_gram_negAbsRat_eq`, `hermQuad_gram_poleSuccessorState_eq`): the shells
  are the half-lines `(−∞, t)`, `Q_{−|·|}(c) = 2 ∫_L^R |T_t|² dt − 2 Re(S̄ Z)` with tail sums `T_t`
  (`tailSum`), and `Q_Φ(w) = 2 Re(X̄ Y_R) + 2c ∫_L^R |T_t|² dt` with the renormalized coordinate
  `Y_R = Y − c Σ w_g|a_g|^{−1/2}(R − b_g)`.

So at every place the form of the local pole–successor state is a renormalized hyperbolic pair plus
squares indexed by agreement shells. The counterterm runs with
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

/-! ### The real place: half-line shells -/

/-- The tail sum `T_t = Σ_{y_a < t} c_a`, the class sum of the half-line shell `(−∞, t)`. -/
def tailSum {n : ℕ} (y : Fin n → ℝ) (c : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∑ a, if y a < t then c a else 0

/-- `R − a = ∫_L^R 1[a < t] dt` for `L ≤ a ≤ R`. -/
theorem integral_indicator_Ioi_eq {a L R : ℝ} (hLa : L ≤ a) (haR : a ≤ R) :
    ∫ t in Set.Icc L R, (Set.Ioi a).indicator (fun _ => (1 : ℝ)) t = R - a := by
  have e : Set.Ioi a ∩ Set.Icc L R = Set.Ioc a R := Set.ext fun t => by
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hLa.trans h.1.le, h.2⟩⟩
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, e,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith)]

theorem indicator_Ioi_mul (a b t : ℝ) :
    (Set.Ioi a).indicator (fun _ => (1 : ℝ)) t * (Set.Ioi b).indicator (fun _ => (1 : ℝ)) t =
      (Set.Ioi (max a b)).indicator (fun _ => (1 : ℝ)) t := by
  simp only [Set.indicator, Set.mem_Ioi, max_lt_iff]
  split_ifs <;> simp_all

/-- `|T_t|² = Σ_{a,b} Re(c̄_a c_b) 1[max(y_a, y_b) < t]`. -/
theorem normSq_tailSum {n : ℕ} (y : Fin n → ℝ) (c : Fin n → ℂ) (t : ℝ) :
    normSq (tailSum y c t) =
      ∑ a, ∑ b, (conj (c a) * c b).re * (Set.Ioi (max (y a) (y b))).indicator (fun _ => 1) t := by
  rw [← Complex.ofReal_re (normSq _), Complex.normSq_eq_conj_mul_self, tailSum, map_sum,
    sum_mul_sum, Complex.re_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine sum_congr rfl fun b _ => ?_
  by_cases ha : y a < t <;> by_cases hb : y b < t <;>
    simp [ha, hb, Set.indicator]

/-- **The shell identity at the real place**: for points in `[L, R]`,
`Q_{−|·|}(c) = 2 ∫_L^R |T_t|² dt − 2 Re(S̄ Z)`, `S = Σ c_a`, `Z = Σ c_a (R − y_a)`. -/
theorem hermQuad_gram_negAbsRat_eq {n : ℕ} (x : Fin n → Multiplicative ℚ) (c : Fin n → ℂ)
    {L R : ℝ} (hL : ∀ a, L ≤ ((Multiplicative.toAdd (x a) : ℚ) : ℝ))
    (hR : ∀ a, ((Multiplicative.toAdd (x a) : ℚ) : ℝ) ≤ R) :
    hermQuad (gram negAbsRat x) c =
      2 * (∫ t in Set.Icc L R, normSq (tailSum (fun a => ((Multiplicative.toAdd (x a) : ℚ) : ℝ)) c t)) -
      2 * (conj (∑ a, c a) * ∑ a, c a * ((R - ((Multiplicative.toAdd (x a) : ℚ) : ℝ) : ℝ) : ℂ)).re := by
  set y : Fin n → ℝ := fun a => ((Multiplicative.toAdd (x a) : ℚ) : ℝ)
  set ρ : Fin n → Fin n → ℝ := fun a b => (conj (c a) * c b).re
  -- `−|y_a − y_b| = 2(R − max) − (R − y_a) − (R − y_b)`
  have hform : hermQuad (gram negAbsRat x) c = ∑ a, ∑ b, ρ a b *
      (2 * (R - max (y a) (y b)) - (R - y a) - (R - y b)) := by
    rw [hermQuad_gram, Complex.re_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum]
    refine sum_congr rfl fun b _ => ?_
    have hab : -|y b - y a| = 2 * (R - max (y a) (y b)) - (R - y a) - (R - y b) := by
      rcases le_total (y a) (y b) with h | h
      · rw [max_eq_right h, abs_of_nonneg (by linarith)]; ring
      · rw [max_eq_left h, abs_of_nonpos (by linarith)]; ring
    simp only [negAbsRat, absRat, toAdd_mul, toAdd_inv, neg_add_eq_sub]
    have hq : ((|Multiplicative.toAdd (x b) - Multiplicative.toAdd (x a)| : ℚ) : ℂ) =
        ((|y b - y a| : ℝ) : ℂ) := by
      simp only [y]
      rw [← Complex.ofReal_ratCast, Rat.cast_abs, Rat.cast_sub]
    rw [hq, show conj (c a) * -((|y b - y a| : ℝ) : ℂ) * c b =
        ((-|y b - y a| : ℝ) : ℂ) * (conj (c a) * c b) by push_cast; ring, Complex.re_ofReal_mul,
      hab, mul_comm]
  -- the linear part is `2 Re(S̄ Z)`
  have hlin : ∑ a, ∑ b, ρ a b * ((R - y a) + (R - y b)) =
      2 * (conj (∑ a, c a) * ∑ a, c a * ((R - y a : ℝ) : ℂ)).re := by
    have h1 : ∑ a, ∑ b, ρ a b * (R - y a) =
        (conj (∑ a, c a * ((R - y a : ℝ) : ℂ)) * ∑ b, c b).re := by
      rw [map_sum, sum_mul_sum, Complex.re_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [Complex.re_sum]
      refine sum_congr rfl fun b _ => ?_
      rw [map_mul, Complex.conj_ofReal, show conj (c a) * ((R - y a : ℝ) : ℂ) * c b =
        ((R - y a : ℝ) : ℂ) * (conj (c a) * c b) by ring, Complex.re_ofReal_mul, mul_comm]
    have h2 : ∑ a, ∑ b, ρ a b * (R - y b) =
        (conj (∑ a, c a) * ∑ b, c b * ((R - y b : ℝ) : ℂ)).re := by
      rw [map_sum, sum_mul_sum, Complex.re_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [Complex.re_sum]
      refine sum_congr rfl fun b _ => ?_
      rw [show conj (c a) * (c b * ((R - y b : ℝ) : ℂ)) =
        ((R - y b : ℝ) : ℂ) * (conj (c a) * c b) by ring, Complex.re_ofReal_mul, mul_comm]
    have h3 : (conj (∑ a, c a * ((R - y a : ℝ) : ℂ)) * ∑ b, c b).re =
        (conj (∑ a, c a) * ∑ a, c a * ((R - y a : ℝ) : ℂ)).re := by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
    simp_rw [mul_add, sum_add_distrib]
    rw [h1, h2, h3]
    ring
  -- the quadratic part is the integral of the tail squares
  have hquad : ∑ a, ∑ b, ρ a b * (R - max (y a) (y b)) =
      ∫ t in Set.Icc L R, normSq (tailSum y c t) := by
    have hint : ∀ a b, Integrable
        (fun t => ρ a b * (Set.Ioi (max (y a) (y b))).indicator (fun _ => (1 : ℝ)) t)
        (volume.restrict (Set.Icc L R)) := fun a b =>
      ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi).const_mul _
    simp_rw [normSq_tailSum]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
    refine sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hint a b]
    refine sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, integral_indicator_Ioi_eq ((hL a).trans (le_max_left _ _))
      (max_le (hR a) (hR b))]
  rw [hform]
  have : ∑ a, ∑ b, ρ a b * (2 * (R - max (y a) (y b)) - (R - y a) - (R - y b)) =
      2 * ∑ a, ∑ b, ρ a b * (R - max (y a) (y b)) -
        ∑ a, ∑ b, ρ a b * ((R - y a) + (R - y b)) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ => by ring
  rw [this, hquad, hlin]

/-- **The shell decomposition of the archimedean pole–successor form**: with `X = Σ w_g|a_g|^{−1/2}`,
`Y = Σ w_g|a_g|^{1/2}` and the renormalized coordinate `Y_R = Y − c Σ_g w_g|a_g|^{−1/2}(R − b_g)`,
`Q_Φ(w) = 2 Re(X̄ Y_R) + 2c ∫_L^R |T_t|² dt` over the half-line shells. -/
theorem hermQuad_gram_poleSuccessorState_eq (c : ℝ) {n : ℕ} (g : Fin n → AffineGroupOf ℚ)
    (w : Fin n → ℂ) {L R : ℝ} (hL : ∀ a, L ≤ ((shiftOf (g a) : ℚ) : ℝ))
    (hR : ∀ a, ((shiftOf (g a) : ℚ) : ℝ) ≤ R) :
    hermQuad (gram (poleSuccessor Rat.AbsoluteValue.real 1 fun m => (c : ℂ) * negAbsRat m) g) w =
      2 * (conj (∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a) *
        (∑ a, w a * slopePow Rat.AbsoluteValue.real 1 (g a) -
          c * ∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a *
            ((R - ((shiftOf (g a) : ℚ) : ℝ) : ℝ) : ℂ))).re +
      2 * c * ∫ t in Set.Icc L R, normSq
        (tailSum (fun a => ((shiftOf (g a) : ℚ) : ℝ)) (boostWeights Rat.AbsoluteValue.real 1 g w) t) := by
  rw [hermQuad_gram_poleSuccessor (isConformal_negAbsRat c)]
  have e : gram (fun m => (c : ℂ) * negAbsRat m) (shifts g) = (c : ℂ) • gram negAbsRat (shifts g) := by
    ext a b; simp [gram]
  rw [e, hermQuad_smul, hermQuad_gram_negAbsRat_eq (shifts g) _ (L := L) (R := R)
    (fun a => by simpa [shifts] using hL a) (fun a => by simpa [shifts] using hR a)]
  simp only [shifts, toAdd_ofAdd]
  set X := ∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a
  set Y := ∑ a, w a * (slopePow Rat.AbsoluteValue.real 1 (g a) : ℂ)
  set Z := ∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a * ((R - ((shiftOf (g a) : ℚ) : ℝ) : ℝ) : ℂ)
  have hYX : (conj Y * X).re = (conj X * Y).re := by
    rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]
  have hZ : (conj X * ((c : ℂ) * Z)).re = c * (conj X * Z).re := by
    rw [mul_left_comm, Complex.re_ofReal_mul]
  rw [mul_sub (conj X) Y ((c : ℂ) * Z), Complex.sub_re, hZ, Complex.add_re, hYX]
  ring

end GaloisForLFunctions.AdelicKreinGeometry
