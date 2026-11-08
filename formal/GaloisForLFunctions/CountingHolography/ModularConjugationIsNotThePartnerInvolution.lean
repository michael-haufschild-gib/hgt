import GaloisForLFunctions.BlackHoleRingdown.TheModularBlackHoleIsAQuotientOfAntiDeSitter
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleReadsTheZeros
import GaloisForLFunctions.CountingHolography.TheBoundaryAlgebraOfABlackHole
import GaloisForLFunctions.CountingHolography.TheTateLimitOfACount
import GaloisForLFunctions.ArithmeticScatteringHolography.TheKMSStripOfTheHorizon
import GaloisForLFunctions.ArithmeticPositiveDuality.WeilsCorrelationCarriesNoSuccessor
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# Modular conjugation of the AdS₄ wedge is not the partner involution

Section 2.7 (Question 1) asks whether there is a von Neumann algebra of `SL₂(ℤ)`-invariant
observables of the AdS₄ Rindler wedge, in standard form `(H, M, Ω, J)`, whose Tomita–Takesaki
conjugation `J` acts on integer sources as the partner involution of the Eisenstein channel so that
the natural positive cone yields a positive Born rule with quadratic growth `Q`.

The answer splits into an unconditional geometric obstruction on `SL₂(ℤ) \ AdS₄` and an
unconditional operator-algebraic collapse on any standard-form von Neumann algebra:

* **Causal separation and Rindler rigidity** (`spacelike_right_left_mod_sl2z`,
  `rindler_wedge_involution_unique`, `rindler_kms_period_mismatch`). Every point of the right AdS₄
  Rindler wedge is strictly spacelike separated from every `SL₂(ℤ)` image of the opposite wedge
  (`ambientForm (X - X') (X - X') > 0`). The unique boost-commuting Lorentz involution exchanging
  the two wedges is `(X₃, X₄) ↦ (-X₃, -X₄)`, which fixes `(t, r, x, y)` rather than inverting
  cusp height, while geometric Rindler time has KMS period `2π` rather than the arithmetic strip
  period `1`.
* **Normalizer rigidity of `PSL₂(ℤ)`** (`normalizer_psl2z_entries_int`, `gl2z_eq_sl2z_or_reflect`,
  `pseudoEisenstein_reflect_eq`). Every matrix in `GL₂(ℝ)` with `det = ±1` normalizing `±SL₂(ℤ)` has
  integer entries, hence lies in `GL₂(ℤ) = SL₂(ℤ) ⋊ ⟨diag(-1, 1)⟩`. Its induced symmetry on
  `SL₂(ℤ) \ ℍ` is `[x + iy] ↦ [±x + iy]`, which fixes cusp height `y` and leaves every
  pseudo-Eisenstein series invariant; no geometric involution of `SL₂(ℤ) \ AdS₄` implements the
  Eisenstein partner involution, and integer shifts `{log n : n ≥ 1}` are not closed under negation
  (`integer_shifts_not_partner_closed`).
* **Tomita central collapse** (`tomita_central_eq_star`). In any standard-form von Neumann algebra
  `(M, Ω, J)` satisfying `J M J = M'` and natural-cone positivity `Re ⟪Ω, A (J A J) Ω⟫ ≥ 0`, every
  operator `Z ∈ M` whose modular conjugate `J Z J` also lies in `M` belongs to the center
  `M ∩ M'`, satisfies `J Z J = Z*`, and has natural-cone pairing `⟪Ω, Z (J Z J) Ω⟫ = ‖Z Ω‖²`.
  Requiring `J · J` to act internally on a source algebra reduces modular positivity to Hilbert
  adjoint positivity.
* **Graph calibration and exact classification over `ℤ`**
  (`exists_standardForm_partner_rep_iff_damped`,
  `riemannHypothesis_iff_exists_standardForm_bornRule`,
  `riemannHypothesis_iff_exists_standardForm_tateLimit`). On a graph black hole of trace `t` and
  size `q`, a nontrivial standard-form realization intertwining `J · J` with the partner involution
  exists iff `t² ≤ 4q`. Over `ℤ`, a standard-form von Neumann algebra carrying rational dilations
  with `J U(r) J = U(r⁻¹)` whose natural-cone form on integer sources equals `integerProbe` (or has
  Tate limit `integerProbe`) exists if and only if `RiemannHypothesis` holds.
-/

set_option autoImplicit false

open Complex Filter Topology Finset Matrix UpperHalfPlane
open scoped MatrixGroups ComplexConjugate ENNReal

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open BlackHoleRingdown ArithmeticScatteringHolography ArithmeticPositiveDuality

/-! ### 1. Causal separation and Rindler wedge rigidity in AdS₄ -/

/-- The right Rindler wedge `X₃ > |X₄|` in ambient `ℝ^{3,2}`. -/
def inRightWedge (X : Fin 5 → ℝ) : Prop := |X 4| < X 3

/-- The left Rindler wedge `X₃ < -|X₄|` in ambient `ℝ^{3,2}`. -/
def inLeftWedge (X : Fin 5 → ℝ) : Prop := X 3 < -|X 4|

/-- Geometric Rindler wedge reflection `(X₀, X₁, X₂, X₃, X₄) ↦ (X₀, X₁, X₂, -X₃, -X₄)`. -/
def wedgeReflect (X : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![X 0, X 1, X 2, -X 3, -X 4]

theorem wedgeReflect_involutive (X : Fin 5 → ℝ) : wedgeReflect (wedgeReflect X) = X := by
  ext i
  fin_cases i <;> simp [wedgeReflect]

theorem ambientForm_wedgeReflect (X Y : Fin 5 → ℝ) :
    ambientForm (wedgeReflect X) (wedgeReflect Y) = ambientForm X Y := by
  simp only [ambientForm, wedgeReflect, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem adsEmbedding_inRightWedge (t : ℝ) {r : ℝ} (hr : 1 < r) (x y : ℝ) :
    inRightWedge (adsEmbedding t r x y) := by
  have hpos : 0 < Real.sqrt (r ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  have hlt : |Real.sinh t| < Real.cosh t := by
    rw [abs_lt]
    have h1 := Real.cosh_sq_sub_sinh_sq t
    have hc : 0 < Real.cosh t := Real.cosh_pos t
    constructor <;> nlinarith [sq_nonneg (Real.cosh t + Real.sinh t),
      sq_nonneg (Real.cosh t - Real.sinh t)]
  simp only [inRightWedge, adsEmbedding, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, abs_mul, abs_of_pos hpos]
  exact mul_lt_mul_of_pos_left hlt hpos

theorem wedgeReflect_inLeftWedge {X : Fin 5 → ℝ} (hX : inRightWedge X) :
    inLeftWedge (wedgeReflect X) := by
  simp only [inRightWedge] at hX
  simp only [inLeftWedge, wedgeReflect, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, abs_neg]
  linarith

/-- Ambient bilinear pairing between a right-wedge point and a reflected exterior point is strictly
less than `-1`. -/
theorem ambientForm_right_left_lt_neg_one (t t' : ℝ) {r r' : ℝ} (hr : 1 < r) (hr' : 1 < r')
    (x x' : ℝ) {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    ambientForm (adsEmbedding t r x y) (wedgeReflect (adsEmbedding t' r' x' y')) < -1 := by
  have hyy : 0 < 4 * y * y' := by positivity
  have hhyp :
      -(hyperboloid x y 0 * hyperboloid x' y' 0) +
        hyperboloid x y 1 * hyperboloid x' y' 1 +
        hyperboloid x y 2 * hyperboloid x' y' 2 =
      -((x - x') ^ 2 + y ^ 2 + y' ^ 2) / (2 * y * y') := by
    simp only [hyperboloid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    field_simp
    ring
  have hhyp_le : -((x - x') ^ 2 + y ^ 2 + y' ^ 2) / (2 * y * y') ≤ -1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - x'), sq_nonneg (y - y')]
  have hrr : 1 < r * r' := by nlinarith
  have hrad_neg : r * r' * (-((x - x') ^ 2 + y ^ 2 + y' ^ 2) / (2 * y * y')) < -1 := by
    nlinarith
  have hboost_nonneg :
      0 ≤ Real.sqrt (r ^ 2 - 1) * Real.sqrt (r' ^ 2 - 1) *
        (Real.cosh t * Real.cosh t' - Real.sinh t * Real.sinh t') := by
    have hcosh : Real.cosh (t - t') = Real.cosh t * Real.cosh t' - Real.sinh t * Real.sinh t' :=
      Real.cosh_sub t t'
    rw [← hcosh]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.cosh_pos _).le
  have hform :
      ambientForm (adsEmbedding t r x y) (wedgeReflect (adsEmbedding t' r' x' y')) =
        r * r' * (-(hyperboloid x y 0 * hyperboloid x' y' 0) +
          hyperboloid x y 1 * hyperboloid x' y' 1 +
          hyperboloid x y 2 * hyperboloid x' y' 2) -
        Real.sqrt (r ^ 2 - 1) * Real.sqrt (r' ^ 2 - 1) *
          (Real.cosh t * Real.cosh t' - Real.sinh t * Real.sinh t') := by
    simp only [ambientForm, adsEmbedding, wedgeReflect, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  rw [hform, hhyp]
  linarith

/-- **Strict spacelike separation across `SL₂(ℤ)` cosets.** Every point of the right Rindler wedge
is strictly spacelike separated in `ℝ^{3,2}` from every `SL₂(ℤ)` image of the left Rindler wedge. -/
theorem spacelike_right_left_mod_sl2z (t t' : ℝ) {r r' : ℝ} (hr : 1 < r) (hr' : 1 < r')
    (z z' : ℍ) (g : SL(2, ℤ)) :
    let X := adsEmbedding t r z.re z.im
    let X' := wedgeReflect (adsEmbedding t' r' (g • z').re (g • z').im)
    0 < ambientForm (X - X') (X - X') := by
  intro X X'
  have hX : ambientForm X X = -1 :=
    ambientForm_adsEmbedding t hr.le z.re z.im_pos.ne'
  have hX' : ambientForm X' X' = -1 := by
    rw [show X' = wedgeReflect (adsEmbedding t' r' (g • z').re (g • z').im) from rfl,
      ambientForm_wedgeReflect]
    exact ambientForm_adsEmbedding t' hr'.le (g • z').re (g • z').im_pos.ne'
  have hcross : ambientForm X X' < -1 :=
    ambientForm_right_left_lt_neg_one t t' hr hr' z.re (g • z').re z.im_pos (g • z').im_pos
  have hexpand : ambientForm (X - X') (X - X') =
      ambientForm X X + ambientForm X' X' - 2 * ambientForm X X' := by
    simp only [ambientForm, Pi.sub_apply]
    ring
  linarith

/-- The `2 × 2` Rindler boost matrix in the `(X₃, X₄)` plane. -/
def rindlerBoostMatrix (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh τ, Real.sinh τ; Real.sinh τ, Real.cosh τ]

/-- **Uniqueness of the geometric Rindler involution.** Every linear involution of the `(X₃, X₄)`
plane that commutes with all Rindler boosts and maps `(1, 0)` into `{u₀ < 0}` is `-1`. -/
theorem rindler_wedge_involution_unique (L : Matrix (Fin 2) (Fin 2) ℝ)
    (hinvol : L * L = 1)
    (hcomm : ∀ τ : ℝ, L * rindlerBoostMatrix τ = rindlerBoostMatrix τ * L)
    (hwedge : L 0 0 < 0) :
    L = !![-1, 0; 0, -1] := by
  have hs : Real.sinh 1 ≠ 0 := by
    have hpos : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr one_pos
    exact hpos.ne'
  have hc1 := hcomm 1
  have h00 := congr_fun (congr_fun hc1 0) 0
  have h01 := congr_fun (congr_fun hc1 0) 1
  simp only [rindlerBoostMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
  have hbc : L 0 1 = L 1 0 := by
    have : (L 0 1 - L 1 0) * Real.sinh 1 = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
  have had : L 0 0 = L 1 1 := by
    have : (L 0 0 - L 1 1) * Real.sinh 1 = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
  have hi00 : L 0 0 * L 0 0 + L 0 1 * L 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congr_fun (congr_fun hinvol 0) 0
  have hi01 : L 0 0 * L 0 1 + L 0 1 * L 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congr_fun (congr_fun hinvol 0) 1
  rw [hbc] at hi00 hi01
  rw [← had] at hi01
  have hab0 : L 0 0 * L 1 0 = 0 := by linarith
  have hb0 : L 1 0 = 0 := (mul_eq_zero.mp hab0).resolve_left hwedge.ne
  rw [hb0] at hi00
  have ha : L 0 0 = -1 := by nlinarith
  have hc0 : L 0 1 = 0 := hbc.trans hb0
  have hd : L 1 1 = -1 := had.symm.trans ha
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb0, hc0, hd]

/-- **KMS period mismatch.** Geometric Rindler boosts are `2πi`-periodic (`β_geom = 2π`), whereas
the arithmetic horizon KMS strip (`xi_kms_condition`) has period `i` (`β_arith = 1 ≠ 2π`). -/
theorem rindler_kms_period_mismatch :
    (∀ z : ℂ, Complex.cosh (z + 2 * Real.pi * Complex.I) = Complex.cosh z ∧
      Complex.sinh (z + 2 * Real.pi * Complex.I) = Complex.sinh z) ∧
    (∀ z : ℂ, kmsCorrelator _root_.RHTower.xi (z + Complex.I) =
      kmsCorrelator _root_.RHTower.xi (-z)) ∧
    (2 * Real.pi : ℝ) ≠ 1 :=
  ⟨fun z => ⟨Complex.cosh_periodic z, Complex.sinh_periodic z⟩,
    xi_kms_condition, by linarith [Real.pi_gt_three]⟩

/-! ### 2. Normalizer rigidity of `PSL₂(ℤ)` and non-closure of integer shifts -/

/-- If coprime natural numbers multiply to a square, the first factor is a square. -/
theorem isSquare_of_coprime_mul_eq_sq {A B k : ℕ} (hcop : Nat.Coprime A B) (hsq : A * B = k ^ 2) :
    ∃ d : ℕ, A = d ^ 2 := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · exact ⟨0, by simp⟩
  set d := Nat.gcd A k
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left k hA
  have hdA : d ∣ A := Nat.gcd_dvd_left A k
  have hdk : d ∣ k := Nat.gcd_dvd_right A k
  have hd2A : d ^ 2 ∣ A := by
    have hcop_d : Nat.Coprime (d ^ 2) B := (hcop.coprime_dvd_left hdA).pow_left 2
    have hd2_ab : d ^ 2 ∣ A * B := by
      rw [hsq]
      exact pow_dvd_pow_of_dvd hdk 2
    exact hcop_d.dvd_of_dvd_mul_right hd2_ab
  have hAd2 : A ∣ d ^ 2 := by
    set a' := A / d
    set k' := k / d
    have ha' : d * a' = A := Nat.mul_div_cancel' hdA
    have hk' : d * k' = k := Nat.mul_div_cancel' hdk
    have hcop' : Nat.Coprime a' k' := Nat.coprime_div_gcd_div_gcd hd_pos
    have hrel : d * (a' * B) = d * (d * k' ^ 2) := by
      calc d * (a' * B) = (d * a') * B := by ring
        _ = A * B := by rw [ha']
        _ = k ^ 2 := hsq
        _ = (d * k') ^ 2 := by rw [hk']
        _ = d * (d * k' ^ 2) := by ring
    have hrel' : a' * B = d * k' ^ 2 := Nat.eq_of_mul_eq_mul_left hd_pos hrel
    have ha'd : a' ∣ d := by
      refine (hcop'.pow_right 2).dvd_of_dvd_mul_right ?_
      exact ⟨B, hrel'.symm⟩
    rw [← ha', sq]
    exact mul_dvd_mul_left d ha'd
  exact ⟨d, Nat.dvd_antisymm hAd2 hd2A⟩

private theorem real_mem_int_of_sq_mem_int {x : ℝ} {m : ℤ} (hm : x ^ 2 = (m : ℝ))
    (hsq : ∃ d : ℕ, m.natAbs = d ^ 2) : ∃ z : ℤ, x = (z : ℝ) := by
  obtain ⟨d, hd⟩ := hsq
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ (m : ℝ) := by rw [← hm]; exact sq_nonneg x
    exact_mod_cast this
  have hmd : m = (d : ℤ) ^ 2 := by
    have h1 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm0
    rw [← h1, hd]
    push_cast
    rfl
  have hx2 : x ^ 2 = (d : ℝ) ^ 2 := by
    rw [hm, hmd]
    push_cast
    rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx2 with rfl | rfl
  · exact ⟨d, by push_cast; rfl⟩
  · exact ⟨-(d : ℤ), by push_cast; rfl⟩

/-- **Normalizer rigidity of `PSL₂(ℤ)` in `PGL₂(ℝ)`.** Every real `2 × 2` matrix with `det = ±1`
normalizing `±SL₂(ℤ)` has integer entries (`g ∈ GL₂(ℤ)`). -/
theorem normalizer_psl2z_entries_int (g : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : g.det = 1 ∨ g.det = -1)
    (hnorm : ∀ γ : SL(2, ℤ), ∃ (γ' : SL(2, ℤ)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧
        g * γ.1.map (Int.cast : ℤ → ℝ) = s • (γ'.1.map (Int.cast : ℤ → ℝ) * g)) :
    ∃ G : Matrix (Fin 2) (Fin 2) ℤ, (G.det = 1 ∨ G.det = -1) ∧
      g = G.map (Int.cast : ℤ → ℝ) := by
  set a := g 0 0
  set b := g 0 1
  set c := g 1 0
  set d := g 1 1
  have hdet_eq : a * d - b * c = g.det := (Matrix.det_fin_two g).symm
  obtain ⟨δz, hδz, hδ_cast⟩ : ∃ δz : ℤ, (δz = 1 ∨ δz = -1) ∧ g.det = (δz : ℝ) := by
    rcases hdet with h1 | h1
    · exact ⟨1, Or.inl rfl, by simp [h1]⟩
    · exact ⟨-1, Or.inr rfl, by simp [h1]⟩
  set gAdj : Matrix (Fin 2) (Fin 2) ℝ := !![d, -b; -c, a]
  have hg_adj : g * gAdj = g.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, b, c, d, gAdj, Matrix.mul_apply, Fin.sum_univ_two, ← hdet_eq] <;> ring
  have hM_int : ∀ γ : SL(2, ℤ), ∀ i j : Fin 2,
      ∃ m : ℤ, (g * γ.1.map (Int.cast : ℤ → ℝ) * gAdj) i j = (m : ℝ) := by
    intro γ i j
    obtain ⟨γ', s, hs, hγ⟩ := hnorm γ
    obtain ⟨sz, rfl⟩ : ∃ sz : ℤ, s = (sz : ℝ) := by
      rcases hs with rfl | rfl
      · exact ⟨1, by simp⟩
      · exact ⟨-1, by simp⟩
    have hmul : g * γ.1.map (Int.cast : ℤ → ℝ) * gAdj =
        ((sz : ℝ) * (δz : ℝ)) • γ'.1.map (Int.cast : ℤ → ℝ) := by
      rw [hγ, Matrix.smul_mul, Matrix.mul_assoc, hg_adj, Matrix.mul_smul, smul_smul,
        mul_one, hδ_cast]
    refine ⟨sz * δz * γ'.1 i j, ?_⟩
    rw [hmul]
    simp
  let γT : SL(2, ℤ) := ⟨!![1, 1; 0, 1], by decide⟩
  let γTt : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by decide⟩
  let γST : SL(2, ℤ) := ⟨!![0, -1; 1, 1], by decide⟩
  have heval : ∀ (M : Matrix (Fin 2) (Fin 2) ℤ),
      g * M.map (Int.cast : ℤ → ℝ) * gAdj =
        !![(a * (M 0 0 : ℝ) + b * (M 1 0 : ℝ)) * d - (a * (M 0 1 : ℝ) + b * (M 1 1 : ℝ)) * c,
           -(a * (M 0 0 : ℝ) + b * (M 1 0 : ℝ)) * b + (a * (M 0 1 : ℝ) + b * (M 1 1 : ℝ)) * a;
           (c * (M 0 0 : ℝ) + d * (M 1 0 : ℝ)) * d - (c * (M 0 1 : ℝ) + d * (M 1 1 : ℝ)) * c,
           -(c * (M 0 0 : ℝ) + d * (M 1 0 : ℝ)) * b + (c * (M 0 1 : ℝ) + d * (M 1 1 : ℝ)) * a] := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, b, c, d, gAdj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  obtain ⟨m_a2, hm_a2⟩ := hM_int γT 0 1
  obtain ⟨m_nc2, hm_nc2⟩ := hM_int γT 1 0
  obtain ⟨m_ac', hm_ac'⟩ := hM_int γT 1 1
  obtain ⟨m_nb2, hm_nb2⟩ := hM_int γTt 0 1
  obtain ⟨m_d2, hm_d2⟩ := hM_int γTt 1 0
  obtain ⟨m_bd', hm_bd'⟩ := hM_int γTt 0 0
  obtain ⟨m_st00, hm_st00⟩ := hM_int γST 0 0
  obtain ⟨m_st01, hm_st01⟩ := hM_int γST 0 1
  obtain ⟨m_st10, hm_st10⟩ := hM_int γST 1 0
  simp only [γT, heval] at hm_a2 hm_nc2 hm_ac'
  simp only [γTt, heval] at hm_nb2 hm_d2 hm_bd'
  simp only [γST, heval] at hm_st00 hm_st01 hm_st10
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, Int.cast_zero] at hm_a2 hm_nc2 hm_ac' hm_nb2 hm_d2 hm_bd'
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_one, Int.cast_zero, Int.cast_neg] at hm_st00 hm_st01 hm_st10
  have ha2 : a ^ 2 = (m_a2 : ℝ) := by linarith
  have hc2 : c ^ 2 = ((-m_nc2 : ℤ) : ℝ) := by push_cast; linarith
  have hb2 : b ^ 2 = ((-m_nb2 : ℤ) : ℝ) := by push_cast; linarith
  have hd2 : d ^ 2 = (m_d2 : ℝ) := by linarith
  have hac : a * c = ((m_ac' - δz : ℤ) : ℝ) := by
    push_cast
    linarith [hdet_eq, hδ_cast]
  have hbd : b * d = ((m_bd' - δz : ℤ) : ℝ) := by
    push_cast
    linarith [hdet_eq, hδ_cast]
  set m_bc : ℤ := (m_bd' - δz) + (m_ac' - δz) - m_st00
  have hbc : b * c = (m_bc : ℝ) := by
    simp only [m_bc, Int.cast_sub, Int.cast_add]
    linarith [hbd, hac, hm_st00]
  set m_ad : ℤ := m_bc + δz
  have had : a * d = (m_ad : ℝ) := by
    simp only [m_ad, Int.cast_add]
    linarith [hbc, hdet_eq, hδ_cast]
  set m_ab : ℤ := m_st01 + m_a2 - m_nb2
  have hab : a * b = (m_ab : ℝ) := by
    simp only [m_ab, Int.cast_sub, Int.cast_add]
    linarith [ha2, hb2, hm_st01]
  set m_cd : ℤ := m_d2 - m_nc2 - m_st10
  have hcd : c * d = (m_cd : ℝ) := by
    simp only [m_cd, Int.cast_sub]
    linarith [hc2, hd2, hm_st10]
  set A := m_a2.natAbs
  set B := (-m_nb2).natAbs
  set C := (-m_nc2).natAbs
  set D := m_d2.natAbs
  have hA_eq : (A : ℝ) = a ^ 2 := by
    have h0 : 0 ≤ m_a2 := by
      have : (0 : ℝ) ≤ (m_a2 : ℝ) := by rw [← ha2]; exact sq_nonneg a
      exact_mod_cast this
    calc (A : ℝ) = ((m_a2.natAbs : ℤ) : ℝ) := by norm_cast
      _ = (m_a2 : ℝ) := by rw [Int.natAbs_of_nonneg h0]
      _ = a ^ 2 := ha2.symm
  have hB_eq : (B : ℝ) = b ^ 2 := by
    have h0 : 0 ≤ -m_nb2 := by
      have : (0 : ℝ) ≤ ((-m_nb2 : ℤ) : ℝ) := by rw [← hb2]; exact sq_nonneg b
      exact_mod_cast this
    calc (B : ℝ) = (((-m_nb2).natAbs : ℤ) : ℝ) := by norm_cast
      _ = ((-m_nb2 : ℤ) : ℝ) := by rw [Int.natAbs_of_nonneg h0]
      _ = b ^ 2 := hb2.symm
  have hC_eq : (C : ℝ) = c ^ 2 := by
    have h0 : 0 ≤ -m_nc2 := by
      have : (0 : ℝ) ≤ ((-m_nc2 : ℤ) : ℝ) := by rw [← hc2]; exact sq_nonneg c
      exact_mod_cast this
    calc (C : ℝ) = (((-m_nc2).natAbs : ℤ) : ℝ) := by norm_cast
      _ = ((-m_nc2 : ℤ) : ℝ) := by rw [Int.natAbs_of_nonneg h0]
      _ = c ^ 2 := hc2.symm
  have hD_eq : (D : ℝ) = d ^ 2 := by
    have h0 : 0 ≤ m_d2 := by
      have : (0 : ℝ) ≤ (m_d2 : ℝ) := by rw [← hd2]; exact sq_nonneg d
      exact_mod_cast this
    calc (D : ℝ) = ((m_d2.natAbs : ℤ) : ℝ) := by norm_cast
      _ = (m_d2 : ℝ) := by rw [Int.natAbs_of_nonneg h0]
      _ = d ^ 2 := hd2.symm
  have hnatAbs_sq : ∀ m : ℤ, (m.natAbs : ℝ) ^ 2 = (m : ℝ) ^ 2 := fun m => by
    rcases le_or_gt 0 m with hm | hm
    · have h0 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm
      have h1 := congrArg (Int.cast (R := ℝ)) h0
      rw [Int.cast_natCast] at h1
      rw [h1]
    · have h0 : ((-m).natAbs : ℤ) = -m := Int.natAbs_of_nonneg (by omega)
      rw [Int.natAbs_neg] at h0
      have h1 := congrArg (Int.cast (R := ℝ)) h0
      rw [Int.cast_natCast, Int.cast_neg] at h1
      rw [h1, neg_sq]
  have hAD_sq : A * D = m_ad.natAbs ^ 2 := by
    have hr : ((A * D : ℕ) : ℝ) = ((m_ad.natAbs ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [hA_eq, hD_eq, hnatAbs_sq m_ad, ← had]
      ring
    exact_mod_cast hr
  have hBC_sq : B * C = m_bc.natAbs ^ 2 := by
    have hr : ((B * C : ℕ) : ℝ) = ((m_bc.natAbs ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [hB_eq, hC_eq, hnatAbs_sq m_bc, ← hbc]
      ring
    exact_mod_cast hr
  have hAB_sq : A * B = m_ab.natAbs ^ 2 := by
    have hr : ((A * B : ℕ) : ℝ) = ((m_ab.natAbs ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [hA_eq, hB_eq, hnatAbs_sq m_ab, ← hab]
      ring
    exact_mod_cast hr
  have hCD_sq : C * D = m_cd.natAbs ^ 2 := by
    have hr : ((C * D : ℕ) : ℝ) = ((m_cd.natAbs ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [hC_eq, hD_eq, hnatAbs_sq m_cd, ← hcd]
      ring
    exact_mod_cast hr
  have hcop_AD_BC : Nat.Coprime (A * D) (B * C) := by
    rw [hAD_sq, hBC_sq]
    have hcop_int : IsCoprime m_ad m_bc := by
      rcases hδz with h1 | h1
      · refine ⟨1, -1, ?_⟩; simp [m_ad, h1]
      · refine ⟨-1, 1, ?_⟩; simp [m_ad, h1]
    have hcop_nat : Nat.Coprime m_ad.natAbs m_bc.natAbs := Int.isCoprime_iff_nat_coprime.mp hcop_int
    exact (hcop_nat.pow_left 2).pow_right 2
  have hcop_AB : Nat.Coprime A B :=
    (hcop_AD_BC.coprime_dvd_left (dvd_mul_right A D)).coprime_dvd_right (dvd_mul_right B C)
  have hcop_CD : Nat.Coprime C D :=
    ((hcop_AD_BC.symm).coprime_dvd_left (dvd_mul_left C B)).coprime_dvd_right (dvd_mul_left D A)
  obtain ⟨za, hza⟩ := real_mem_int_of_sq_mem_int ha2 (isSquare_of_coprime_mul_eq_sq hcop_AB hAB_sq)
  obtain ⟨zb, hzb⟩ := real_mem_int_of_sq_mem_int hb2
    (isSquare_of_coprime_mul_eq_sq hcop_AB.symm (mul_comm B A ▸ hAB_sq))
  obtain ⟨zc, hzc⟩ := real_mem_int_of_sq_mem_int hc2 (isSquare_of_coprime_mul_eq_sq hcop_CD hCD_sq)
  obtain ⟨zd, hzd⟩ := real_mem_int_of_sq_mem_int hd2
    (isSquare_of_coprime_mul_eq_sq hcop_CD.symm (mul_comm D C ▸ hCD_sq))
  let G : Matrix (Fin 2) (Fin 2) ℤ := !![za, zb; zc, zd]
  have hgG : g = G.map (Int.cast : ℤ → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, c, d, G, hza, hzb, hzc, hzd]
  have hGdet : G.det = 1 ∨ G.det = -1 := by
    have hcast : (G.det : ℝ) = g.det := by
      rw [hgG, Matrix.det_fin_two, Matrix.det_fin_two]
      simp
    rcases hdet with h1 | h1
    · left; exact_mod_cast hcast.trans h1
    · right; exact_mod_cast hcast.trans h1
  exact ⟨G, hGdet, hgG⟩

/-- Every matrix in `GL₂(ℤ)` lies in `SL₂(ℤ)` or `SL₂(ℤ) · diag(-1, 1)`. -/
theorem gl2z_eq_sl2z_or_reflect (G : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : G.det = 1 ∨ G.det = -1) :
    (∃ γ : SL(2, ℤ), G = γ.1) ∨ (∃ γ : SL(2, ℤ), G = γ.1 * !![-1, 0; 0, 1]) := by
  rcases hdet with h1 | h1
  · exact Or.inl ⟨⟨G, h1⟩, rfl⟩
  · right
    let J₀ : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]
    have hJ₀_sq : J₀ * J₀ = 1 := by decide
    have hJ₀_det : J₀.det = -1 := by decide
    have hGJ_det : (G * J₀).det = 1 := by rw [Matrix.det_mul, h1, hJ₀_det]; ring
    refine ⟨⟨G * J₀, hGJ_det⟩, ?_⟩
    calc G = G * (J₀ * J₀) := by rw [hJ₀_sq, mul_one]
      _ = (G * J₀) * J₀ := (Matrix.mul_assoc G J₀ J₀).symm

/-- **Orientation-reversing reflection fixes every pseudo-Eisenstein series.** The unique
nontrivial `GL₂(ℤ)` coset representative `x + iy ↦ -x + iy` preserves every `pseudoEisenstein ψ`
identically instead of applying the Eisenstein functional-equation partner involution. -/
theorem pseudoEisenstein_reflect_eq (ψ : ℝ → ℂ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    pseudoEisenstein ψ (ofComplex ⟨-x, y⟩) = pseudoEisenstein ψ (ofComplex ⟨x, y⟩) := by
  unfold pseudoEisenstein
  let negRow : EisensteinSeries.gammaSet 1 1 0 → EisensteinSeries.gammaSet 1 1 0 :=
    fun p => ⟨![-p.1 0, p.1 1], by
      rw [EisensteinSeries.gammaSet_one_mem_iff]
      have h := (EisensteinSeries.gammaSet_one_mem_iff 1 p.1).mp p.2
      simpa using h⟩
  have hneg : ∀ p, negRow (negRow p) = p := fun p => by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [negRow]
  let e : EisensteinSeries.gammaSet 1 1 0 ≃ EisensteinSeries.gammaSet 1 1 0 :=
    ⟨negRow, negRow, hneg, hneg⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun p => ?_
  congr 1
  rw [RHTower.DeckPointPair.im_gammaSetMatrix_smul, RHTower.DeckPointPair.im_gammaSetMatrix_smul,
    im_ofComplex_mk hy, im_ofComplex_mk hy]
  have hz1 : ((ofComplex (⟨-x, y⟩ : ℂ) : ℍ) : ℂ) = ⟨-x, y⟩ := by
    rw [ofComplex_apply_of_im_pos (z := ⟨-x, y⟩) hy]
  have hz2 : ((ofComplex (⟨x, y⟩ : ℂ) : ℍ) : ℂ) = ⟨x, y⟩ := by
    rw [ofComplex_apply_of_im_pos (z := ⟨x, y⟩) hy]
  rw [hz1, hz2]
  dsimp [e, negRow]
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Int.cast_neg, Complex.neg_re, Complex.neg_im, Complex.intCast_re, Complex.intCast_im]
  ring

/-- **Integer shifts are not closed under the partner involution.** For every `n ≥ 2`, `-log n` is
not of the form `log m` for any positive integer `m`. -/
theorem integer_shifts_not_partner_closed {n : ℕ} (hn : 2 ≤ n) :
    -Real.log (n : ℝ) ∉ {u : ℝ | ∃ m : ℕ, 1 ≤ m ∧ u = Real.log (m : ℝ)} := by
  rintro ⟨m, hm, heq⟩
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have hnonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  linarith

/-! ### 3. Standard-form von Neumann algebras and Tomita central collapse -/

/-- An antiunitary involution `J : H → H` on a complex Hilbert space. -/
structure AntiunitaryInvol (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  toFun : H → H
  invol' : ∀ x, toFun (toFun x) = x
  map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul' : ∀ (c : ℂ) (x : H), toFun (c • x) = starRingEnd ℂ c • toFun x
  inner_map' : ∀ x y, inner ℂ (toFun x) (toFun y) = inner ℂ y x

namespace AntiunitaryInvol

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : FunLike (AntiunitaryInvol H) H H where
  coe J := J.toFun
  coe_injective J₁ J₂ h := by cases J₁; cases J₂; congr

@[simp] theorem invol (J : AntiunitaryInvol H) (x : H) : J (J x) = x := J.invol' x
@[simp] theorem map_add (J : AntiunitaryInvol H) (x y : H) : J (x + y) = J x + J y := J.map_add' x y
@[simp] theorem map_smul (J : AntiunitaryInvol H) (c : ℂ) (x : H) :
    J (c • x) = starRingEnd ℂ c • J x := J.map_smul' c x
@[simp] theorem inner_map (J : AntiunitaryInvol H) (x y : H) :
    inner ℂ (J x) (J y) = inner ℂ y x := J.inner_map' x y

@[simp] theorem map_zero (J : AntiunitaryInvol H) : J 0 = 0 := by
  simpa using J.map_smul 0 0

@[simp] theorem map_neg (J : AntiunitaryInvol H) (x : H) : J (-x) = -J x := by
  simpa using J.map_smul (-1) x

@[simp] theorem map_sub (J : AntiunitaryInvol H) (x y : H) : J (x - y) = J x - J y := by
  rw [sub_eq_add_neg, J.map_add, J.map_neg, sub_eq_add_neg]

@[simp] theorem norm_map (J : AntiunitaryInvol H) (x : H) : ‖J x‖ = ‖x‖ := by
  have hsq : ‖J x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), J.inner_map]
  have h := congr_arg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

/-- Operator conjugation `A ↦ J A J` by an antiunitary involution. -/
def conjOp (J : AntiunitaryInvol H) (A : H →L[ℂ] H) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => J (A (J x))
      map_add' := fun x y => by simp [J.map_add]
      map_smul' := fun c x => by simp [J.map_smul] }
    ‖A‖
    (fun x => by
      show ‖J (A (J x))‖ ≤ ‖A‖ * ‖x‖
      rw [J.norm_map]
      simpa only [J.norm_map] using A.le_opNorm (J x))

@[simp] theorem conjOp_apply (J : AntiunitaryInvol H) (A : H →L[ℂ] H) (x : H) :
    J.conjOp A x = J (A (J x)) := rfl

@[simp] theorem conjOp_invol (J : AntiunitaryInvol H) (A : H →L[ℂ] H) :
    J.conjOp (J.conjOp A) = A := by
  ext x
  simp

@[simp] theorem conjOp_zero (J : AntiunitaryInvol H) : J.conjOp (0 : H →L[ℂ] H) = 0 := by
  ext x
  simp

@[simp] theorem conjOp_one (J : AntiunitaryInvol H) : J.conjOp (1 : H →L[ℂ] H) = 1 := by
  ext x
  simp

@[simp] theorem conjOp_add (J : AntiunitaryInvol H) (A B : H →L[ℂ] H) :
    J.conjOp (A + B) = J.conjOp A + J.conjOp B := by
  ext x
  simp

theorem conjOp_sum {ι : Type*} (J : AntiunitaryInvol H) (s : Finset ι) (f : ι → H →L[ℂ] H) :
    J.conjOp (∑ i ∈ s, f i) = ∑ i ∈ s, J.conjOp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, conjOp_add, ih, Finset.sum_insert ha]

@[simp] theorem conjOp_neg (J : AntiunitaryInvol H) (A : H →L[ℂ] H) :
    J.conjOp (-A) = -J.conjOp A := by
  ext x
  simp

@[simp] theorem conjOp_sub (J : AntiunitaryInvol H) (A B : H →L[ℂ] H) :
    J.conjOp (A - B) = J.conjOp A - J.conjOp B := by
  ext x
  simp

@[simp] theorem conjOp_smul (J : AntiunitaryInvol H) (c : ℂ) (A : H →L[ℂ] H) :
    J.conjOp (c • A) = starRingEnd ℂ c • J.conjOp A := by
  ext x
  simp

@[simp] theorem conjOp_mul (J : AntiunitaryInvol H) (A B : H →L[ℂ] H) :
    J.conjOp (A * B) = J.conjOp A * J.conjOp B := by
  ext x
  simp

theorem star_conjOp [CompleteSpace H] (J : AntiunitaryInvol H) (A : H →L[ℂ] H) :
    star (J.conjOp A) = J.conjOp (star A) := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    conjOp_apply, conjOp_apply]
  calc inner ℂ (J (A (J x))) y
      = inner ℂ (J (A (J x))) (J (J y)) := by rw [J.invol]
    _ = inner ℂ (J y) (A (J x)) := J.inner_map _ _
    _ = inner ℂ ((ContinuousLinearMap.adjoint A) (J y)) (J x) :=
        (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
    _ = inner ℂ ((star A) (J y)) (J x) := by rw [← ContinuousLinearMap.star_eq_adjoint]
    _ = inner ℂ (J (J x)) (J ((star A) (J y))) := (J.inner_map _ _).symm
    _ = inner ℂ x (J ((star A) (J y))) := by rw [J.invol]

end AntiunitaryInvol

/-- A von Neumann algebra `M` on `H` in Tomita–Takesaki standard form with cyclic separating vector
`Ω`, modular conjugation `J` fixing `Ω` (`J M J = M'`), and natural-cone positivity
`Re ⟪Ω, A (J A J) Ω⟫ ≥ 0`. -/
structure StandardForm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) where
  Ω : H
  separating : ∀ A ∈ M, A Ω = 0 → A = 0
  cyclic : DenseRange (fun A : M => (A : H →L[ℂ] H) Ω)
  J : AntiunitaryInvol H
  J_omega : J Ω = Ω
  conj_mem_commutant_iff : ∀ A : H →L[ℂ] H, J.conjOp A ∈ M.commutant ↔ A ∈ M
  natural_cone_pos : ∀ A ∈ M, 0 ≤ (inner ℂ Ω (A (J.conjOp A Ω))).re

namespace StandardForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Double commutation turns `J A J ∈ M' ↔ A ∈ M` into `J A J ∈ M ↔ A ∈ M'`. -/
theorem conjOp_mem_iff_mem_commutant (ms : StandardForm M) (A : H →L[ℂ] H) :
    ms.J.conjOp A ∈ M ↔ A ∈ M.commutant := by
  have h := ms.conj_mem_commutant_iff (ms.J.conjOp A)
  rw [ms.J.conjOp_invol] at h
  exact h.symm

/-- On self-adjoint central elements of `M`, Tomita conjugation is the identity. -/
theorem conjOp_eq_self_of_selfAdjoint_central (ms : StandardForm M) {Z : H →L[ℂ] H}
    (hZ : Z ∈ M) (hZc : Z ∈ M.commutant) (hsa : star Z = Z) :
    ms.J.conjOp Z = Z := by
  have hJZ_mem : ms.J.conjOp Z ∈ M := (ms.conjOp_mem_iff_mem_commutant Z).mpr hZc
  set D : H →L[ℂ] H := Z - ms.J.conjOp Z
  have hD_mem : D ∈ M := sub_mem hZ hJZ_mem
  have hD_sa : star D = D := by
    simp only [D, star_sub, ms.J.star_conjOp, hsa]
  have hD_anti : ms.J.conjOp D = -D := by
    simp only [D, AntiunitaryInvol.conjOp_sub, AntiunitaryInvol.conjOp_invol]
    abel
  have hpos := ms.natural_cone_pos D hD_mem
  rw [hD_anti, _root_.neg_apply, map_neg, inner_neg_right, Complex.neg_re] at hpos
  have hnorm : (inner ℂ ms.Ω (D (D ms.Ω))).re = ‖D ms.Ω‖ ^ 2 := by
    have hadj : inner ℂ ms.Ω (D (D ms.Ω)) = inner ℂ (D ms.Ω) (D ms.Ω) := by
      calc inner ℂ ms.Ω (D (D ms.Ω))
          = inner ℂ (ContinuousLinearMap.adjoint D ms.Ω) (D ms.Ω) :=
            (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
        _ = inner ℂ ((star D) ms.Ω) (D ms.Ω) := by rw [← ContinuousLinearMap.star_eq_adjoint]
        _ = inner ℂ (D ms.Ω) (D ms.Ω) := by rw [hD_sa]
    have hsq : inner ℂ (D ms.Ω) (D ms.Ω) = ((‖D ms.Ω‖ ^ 2 : ℝ) : ℂ) :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (D ms.Ω)).trans (Complex.ofReal_pow _ 2).symm
    rw [hadj, hsq, Complex.ofReal_re]
  rw [hnorm] at hpos
  have hDΩ : D ms.Ω = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (D ms.Ω)])
  have hD0 : D = 0 := ms.separating D hD_mem hDΩ
  exact (sub_eq_zero.mp hD0).symm

/-- **Tomita central collapse.** Any operator `Z ∈ M` whose modular conjugate `J Z J` also lies in
`M` belongs to the center `M ∩ M'`, satisfies `J Z J = Z*`, and has natural-cone form `‖Z Ω‖²`. -/
theorem tomita_central_eq_star (ms : StandardForm M) {Z : H →L[ℂ] H}
    (hZ : Z ∈ M) (hJZ : ms.J.conjOp Z ∈ M) :
    Z ∈ M.commutant ∧ ms.J.conjOp Z = star Z ∧
      inner ℂ ms.Ω (Z (ms.J.conjOp Z ms.Ω)) = ((‖Z ms.Ω‖ ^ 2 : ℝ) : ℂ) := by
  have hZc : Z ∈ M.commutant := (ms.conjOp_mem_iff_mem_commutant Z).mp hJZ
  have hZs_mem : star Z ∈ M := star_mem hZ
  have hZs_comm : star Z ∈ M.commutant := star_mem hZc
  set A : H →L[ℂ] H := (1 / 2 : ℂ) • (Z + star Z)
  set B : H →L[ℂ] H := (-(Complex.I / 2) : ℂ) • (Z - star Z)
  have hA_mem : A ∈ M := M.toStarSubalgebra.smul_mem (add_mem hZ hZs_mem) _
  have hA_comm : A ∈ M.commutant := M.commutant.toStarSubalgebra.smul_mem (add_mem hZc hZs_comm) _
  have hA_sa : star A = A := by
    simp only [A, star_smul, star_add, star_star, RCLike.star_def, map_div₀, map_one, map_ofNat]
    rw [add_comm]
  have hB_mem : B ∈ M := M.toStarSubalgebra.smul_mem (sub_mem hZ hZs_mem) _
  have hB_comm : B ∈ M.commutant := M.commutant.toStarSubalgebra.smul_mem (sub_mem hZc hZs_comm) _
  have hB_sa : star B = B := by
    have hstar_c : star (-(Complex.I / 2) : ℂ) = Complex.I / 2 := by
      simp [RCLike.star_def]
      ring
    rw [show B = (-(Complex.I / 2) : ℂ) • (Z - star Z) from rfl, star_smul, star_sub, star_star,
      hstar_c, ← neg_sub, smul_neg, ← _root_.neg_smul]
  have hJA : ms.J.conjOp A = A := ms.conjOp_eq_self_of_selfAdjoint_central hA_mem hA_comm hA_sa
  have hJB : ms.J.conjOp B = B := ms.conjOp_eq_self_of_selfAdjoint_central hB_mem hB_comm hB_sa
  have hZ_decomp : Z = A + Complex.I • B := by
    have hI2 : Complex.I * (-(Complex.I / 2)) = (1 / 2 : ℂ) := by
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination -(1 / 2 : ℂ) * this
    rw [show A = (1 / 2 : ℂ) • (Z + star Z) from rfl,
      show B = (-(Complex.I / 2) : ℂ) • (Z - star Z) from rfl, smul_smul, hI2]
    module
  have hZs_decomp : star Z = A - Complex.I • B := by
    have h1 : star (A + Complex.I • B) = star A + star (Complex.I • B) := star_add _ _
    have h2 : star (Complex.I • B) = -(Complex.I • B) := by
      rw [star_smul, hB_sa, RCLike.star_def, conj_I, _root_.neg_smul]
    calc star Z = star (A + Complex.I • B) := congr_arg star hZ_decomp
      _ = A + -(Complex.I • B) := h1.trans (congr_arg₂ (· + ·) hA_sa h2)
      _ = A - Complex.I • B := (sub_eq_add_neg _ _).symm
  have hJZ_eq : ms.J.conjOp Z = star Z := by
    have h1 : ms.J.conjOp (A + Complex.I • B) = ms.J.conjOp A + ms.J.conjOp (Complex.I • B) :=
      AntiunitaryInvol.conjOp_add ms.J _ _
    have h2 : ms.J.conjOp (Complex.I • B) = -(Complex.I • B) := by
      rw [AntiunitaryInvol.conjOp_smul, hJB, conj_I, _root_.neg_smul]
    calc ms.J.conjOp Z = ms.J.conjOp (A + Complex.I • B) := congr_arg ms.J.conjOp hZ_decomp
      _ = A + -(Complex.I • B) := h1.trans (congr_arg₂ (· + ·) hJA h2)
      _ = star Z := by rw [← sub_eq_add_neg, hZs_decomp]
  refine ⟨hZc, hJZ_eq, ?_⟩
  rw [hJZ_eq]
  have hcomm_star : Z * star Z = star Z * Z :=
    ((VonNeumannAlgebra.mem_commutant_iff.mp hZc) _ hZs_mem).symm
  have happ : Z ((star Z) ms.Ω) = (star Z) (Z ms.Ω) :=
    congr_arg (fun T : H →L[ℂ] H => T ms.Ω) hcomm_star
  rw [happ, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ 2).symm

end StandardForm

/-! ### 4. Graph black hole and fake continuous horizon calibrations -/

/-- **Graph black hole calibration.** A nontrivial standard-form von Neumann algebra carries a
unital `ℝ`-algebra representation of `QuadraticAlgebra ℝ (-q) t` intertwining `J · J` with the
partner involution `star` if and only if `t² ≤ 4q`. -/
theorem exists_standardForm_partner_rep_iff_damped {q t : ℝ} :
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (_ : Nontrivial H) (M : VonNeumannAlgebra H) (ms : StandardForm M)
      (π : QuadraticAlgebra ℝ (-q) t →ₐ[ℝ] (H →L[ℂ] H)),
      (∀ z, π z ∈ M) ∧ (∀ z, ms.J.conjOp (π z) = π (star z))) ↔ t ^ 2 ≤ 4 * q := by
  constructor
  · rintro ⟨H, _, _, _, hnt, M, ms, π, hπM, hπJ⟩
    have hΩ_ne : ms.Ω ≠ 0 := by
      intro h0
      have h10 : (1 : H →L[ℂ] H) = 0 := ms.separating 1 M.one_mem (by simp [h0])
      obtain ⟨v, hv⟩ := exists_ne (0 : H)
      exact hv (by simpa using congr_arg (fun T : H →L[ℂ] H => T v) h10)
    have hr_smul : ∀ (r : ℝ) (v : H), r • v = (r : ℂ) • v := fun r v => by
      calc r • v = r • ((1 : ℂ) • v) := by rw [one_smul]
        _ = (r • (1 : ℂ)) • v := (smul_assoc r (1 : ℂ) v).symm
        _ = (r : ℂ) • v := by rw [Complex.real_smul, mul_one]
    rw [← norm_nonneg_iff]
    intro z
    have hzJ : ms.J.conjOp (π z) ∈ M := by rw [hπJ]; exact hπM (star z)
    obtain ⟨_, _, hcone⟩ := ms.tomita_central_eq_star (hπM z) hzJ
    have hmul : π z ((ms.J.conjOp (π z)) ms.Ω) = (z.norm : ℂ) • ms.Ω := by
      rw [hπJ]
      change (π z * π (star z)) ms.Ω = _
      rw [← map_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one]
      exact hr_smul z.norm ms.Ω
    rw [hmul, inner_smul_right] at hcone
    have hreal : z.norm * ‖ms.Ω‖ ^ 2 = ‖π z ms.Ω‖ ^ 2 := by
      have hsq : inner ℂ ms.Ω ms.Ω = ((‖ms.Ω‖ ^ 2 : ℝ) : ℂ) :=
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ms.Ω).trans (Complex.ofReal_pow _ 2).symm
      rw [hsq] at hcone
      have hre := congr_arg Complex.re hcone
      rwa [Complex.re_ofReal_mul, Complex.ofReal_re, Complex.ofReal_re] at hre
    have hΩ2 : 0 < ‖ms.Ω‖ ^ 2 := sq_pos_of_pos (_root_.norm_pos_iff.mpr hΩ_ne)
    nlinarith [sq_nonneg ‖π z ms.Ω‖]
  · intro ht
    obtain ⟨ρ, hρ⟩ := exists_starRep_iff.mpr ht
    have hclm_mul : ∀ A B : ℂ →L[ℂ] ℂ, A * B = B * A := by
      intro A B
      ext
      have hAB : A (B 1) = B 1 * A 1 := by simpa [mul_comm] using A.map_smul (B 1) 1
      have hBA : B (A 1) = A 1 * B 1 := by simpa [mul_comm] using B.map_smul (A 1) 1
      exact hAB.trans ((mul_comm _ _).trans hBA.symm)
    let topVN : VonNeumannAlgebra ℂ :=
      { toStarSubalgebra := ⊤
        centralizer_centralizer' := by
          ext T
          change T ∈ Set.centralizer (Set.centralizer Set.univ) ↔ T ∈ Set.univ
          simp only [Set.mem_centralizer_iff, Set.mem_univ, iff_true]
          exact fun S _ => hclm_mul S T }
    have hcomm_top : ∀ A : ℂ →L[ℂ] ℂ, A ∈ topVN.commutant := fun A =>
      VonNeumannAlgebra.mem_commutant_iff.mpr fun B _ => hclm_mul _ _
    let Jc : AntiunitaryInvol ℂ :=
      { toFun := starRingEnd ℂ
        invol' := Complex.conj_conj
        map_add' := map_add _
        map_smul' := fun c x => by simp
        inner_map' := fun x y => by simp [RCLike.inner_apply, mul_comm] }
    let ms : StandardForm topVN :=
      { Ω := 1
        separating := fun A _ hA => by
          ext
          simpa using hA
        cyclic := fun z => by
          refine subset_closure ⟨⟨z • 1, trivial⟩, ?_⟩
          simp
        J := Jc
        J_omega := by
          show starRingEnd ℂ 1 = 1
          exact map_one _
        conj_mem_commutant_iff := fun A => ⟨fun _ => trivial, fun _ => hcomm_top _⟩
        natural_cone_pos := fun A _ => by
          have hA : ∀ z : ℂ, A z = z * A 1 := fun z => by simpa [mul_comm] using A.map_smul z 1
          have hJ1 : Jc 1 = 1 := map_one (starRingEnd ℂ)
          have hval : A ((Jc.conjOp A) 1) = A 1 * starRingEnd ℂ (A 1) := by
            show A (Jc (A (Jc 1))) = _
            rw [hJ1, hA (Jc (A 1))]
            show starRingEnd ℂ (A 1) * A 1 = A 1 * starRingEnd ℂ (A 1)
            ring
          rw [RCLike.inner_apply, map_one (starRingEnd ℂ), mul_one, hval, Complex.mul_conj,
            Complex.ofReal_re]
          exact Complex.normSq_nonneg _ }
    let π : QuadraticAlgebra ℝ (-q) t →ₐ[ℝ] (ℂ →L[ℂ] ℂ) :=
      { toFun := fun z => ρ z • (1 : ℂ →L[ℂ] ℂ)
        map_one' := by rw [map_one, one_smul]
        map_mul' := fun x y => by rw [map_mul, smul_mul_smul_comm, mul_one]
        map_zero' := by rw [map_zero, zero_smul ℂ (1 : ℂ →L[ℂ] ℂ)]
        map_add' := by intro x y; rw [map_add, add_smul (ρ x) (ρ y) (1 : ℂ →L[ℂ] ℂ)]
        commutes' := fun r => by
          ext
          simp [Algebra.algebraMap_eq_smul_one, Complex.real_smul] }
    refine ⟨ℂ, inferInstance, inferInstance, inferInstance, inferInstance, topVN, ms, π,
      fun _ => trivial, fun z => ?_⟩
    ext
    show starRingEnd ℂ ((ρ z • (1 : ℂ →L[ℂ] ℂ)) (starRingEnd ℂ 1)) = (ρ (star z) • (1 : ℂ →L[ℂ] ℂ)) 1
    simp [hρ]

/-! ### 5. Diagonal standard-form von Neumann algebra and exact RH classification over `ℤ` -/

section DiagonalStandardForm

variable {ι : Type*}

/-- Coordinate rank-one projection `e_i ⟪e_i, ·⟫` on `ℓ²(ι)`. -/
def lpCoordProj [DecidableEq ι] (i : ι) : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  lpDiagonalCLM (fun j => if j = i then 1 else 0) zero_le_one
    (fun j => by split_ifs <;> simp)

theorem lpCoordProj_apply [DecidableEq ι] (i : ι) (f : lp (fun _ : ι => ℂ) 2) (j : ι) :
    lpCoordProj i f j = (if j = i then 1 else 0) * f j := rfl

theorem lpCoordProj_eq_single [DecidableEq ι] (i : ι) (f : lp (fun _ : ι => ℂ) 2) :
    lpCoordProj i f = lp.single 2 i (f i) := by
  ext j
  rw [lpCoordProj_apply, lp.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h; simp
  · simp

theorem star_lpCoordProj [DecidableEq ι] (i : ι) :
    star (lpCoordProj i) = lpCoordProj i := by
  refine ContinuousLinearMap.ext fun g => ext_inner_left ℂ fun f => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [lpCoordProj_apply, lpCoordProj_apply, RCLike.inner_apply, RCLike.inner_apply]
  split_ifs <;> simp

/-- The maximal abelian von Neumann algebra of bounded diagonal operators on `ℓ²(ι)`, defined as
the commutant of the coordinate projections. -/
def diagVN (ι : Type*) [DecidableEq ι] : VonNeumannAlgebra (lp (fun _ : ι => ℂ) 2) where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (Set.range (lpCoordProj (ι := ι)))
  centralizer_centralizer' := by
    have hcoe : (StarSubalgebra.centralizer ℂ (Set.range (lpCoordProj (ι := ι))) :
        Set (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)) =
        Set.centralizer (Set.range (lpCoordProj (ι := ι))) := by
      ext T
      rw [SetLike.mem_coe, StarSubalgebra.mem_centralizer_iff]
      refine ⟨fun h S hS => (h S hS).1, fun h S hS => ?_⟩
      rcases hS with ⟨i, rfl⟩
      refine ⟨h _ ⟨i, rfl⟩, ?_⟩
      rw [star_lpCoordProj]
      exact h _ ⟨i, rfl⟩
    change (StarSubalgebra.centralizer ℂ (Set.range (lpCoordProj (ι := ι))) :
        Set (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2)).centralizer.centralizer =
      (StarSubalgebra.centralizer ℂ (Set.range (lpCoordProj (ι := ι))) :
        Set (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
    rw [hcoe]
    ext T
    refine ⟨fun hT S hS => ?_, fun hT S hS => (hS T hT).symm⟩
    exact hT S fun U hU => (hU S hS).symm

theorem mem_diagVN_iff [DecidableEq ι] (T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :
    T ∈ diagVN ι ↔ ∀ i : ι, lpCoordProj i * T = T * lpCoordProj i := by
  change T ∈ StarSubalgebra.centralizer ℂ (Set.range (lpCoordProj (ι := ι))) ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  refine ⟨fun h i => (h _ ⟨i, rfl⟩).1, fun h S hS => ?_⟩
  rcases hS with ⟨i, rfl⟩
  refine ⟨h i, ?_⟩
  rw [star_lpCoordProj]
  exact h i

theorem lpDiagonalCLM_mem_diagVN [DecidableEq ι] (lam : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖lam i‖ ≤ C) : lpDiagonalCLM lam hC0 hC ∈ diagVN ι := by
  rw [mem_diagVN_iff]
  intro i
  refine ContinuousLinearMap.ext fun f => lp.ext <| funext fun j => ?_
  change lpCoordProj i (lpDiagonalCLM lam hC0 hC f) j = lpDiagonalCLM lam hC0 hC (lpCoordProj i f) j
  rw [lpCoordProj_apply, lpDiagonalCLM_apply, lpDiagonalCLM_apply, lpCoordProj_apply]
  ring

theorem lpCoordProj_mem_diagVN [DecidableEq ι] (i : ι) : lpCoordProj i ∈ diagVN ι :=
  lpDiagonalCLM_mem_diagVN _ zero_le_one _

/-- Every operator in `diagVN ι` acts coordinatewise by `(T e_i)_i`. -/
theorem diagVN_apply_eq [DecidableEq ι] {T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    (hT : T ∈ diagVN ι) (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    T f i = T (lp.single 2 i 1) i * f i := by
  have hcomm := (mem_diagVN_iff T).mp hT i
  have happ : lpCoordProj i (T f) i = T (lpCoordProj i f) i :=
    congr_arg (fun S : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 => S f i) hcomm
  rw [lpCoordProj_apply, if_pos rfl, one_mul] at happ
  rw [happ, lpCoordProj_eq_single]
  have hsmul : lp.single (E := fun _ : ι => ℂ) 2 i (f i) = f i • lp.single 2 i 1 := by
    ext j
    simp [lp.single_apply, Pi.single_apply]
  rw [hsmul, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- `diagVN ι` is maximal abelian: `M' = M`. -/
theorem diagVN_commutant_eq [DecidableEq ι] : (diagVN ι).commutant = diagVN ι := by
  ext T
  rw [VonNeumannAlgebra.mem_commutant_iff]
  refine ⟨fun h => (mem_diagVN_iff T).mpr fun i => h _ (lpCoordProj_mem_diagVN i),
    fun hT S hS => ?_⟩
  refine ContinuousLinearMap.ext fun f => lp.ext <| funext fun i => ?_
  calc (S * T) f i = S (T f) i := rfl
    _ = S (lp.single 2 i 1) i * (T f i) := diagVN_apply_eq hS (T f) i
    _ = S (lp.single 2 i 1) i * (T (lp.single 2 i 1) i * f i) := by rw [diagVN_apply_eq hT f i]
    _ = T (lp.single 2 i 1) i * (S (lp.single 2 i 1) i * f i) := by ring
    _ = T (lp.single 2 i 1) i * (S f i) := by rw [← diagVN_apply_eq hS f i]
    _ = T (S f) i := (diagVN_apply_eq hT (S f) i).symm
    _ = (T * S) f i := rfl

/-- Coordinatewise complex conjugation on `ℓ²(ι)` as an antiunitary involution. -/
def lpConjInvol (ι : Type*) : AntiunitaryInvol (lp (fun _ : ι => ℂ) 2) where
  toFun f := ⟨fun i => starRingEnd ℂ (f i), by
    have hf : Memℓp (f : ι → ℂ) 2 := lp.memℓp f
    refine memℓp_gen ?_
    simpa [RCLike.norm_conj] using hf.summable (by norm_num)⟩
  invol' f := by ext i; exact Complex.conj_conj (f i)
  map_add' f g := by ext i; exact map_add _ (f i) (g i)
  map_smul' c f := by ext i; exact map_mul _ c (f i)
  inner_map' f g := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i => ?_
    simp [RCLike.inner_apply, mul_comm]

@[simp] theorem lpConjInvol_apply (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpConjInvol ι f i = starRingEnd ℂ (f i) := rfl

theorem lpConjInvol_conjOp_coordProj [DecidableEq ι] (i : ι) :
    (lpConjInvol ι).conjOp (lpCoordProj i) = lpCoordProj i := by
  refine ContinuousLinearMap.ext fun f => lp.ext <| funext fun j => ?_
  simp only [AntiunitaryInvol.conjOp_apply, lpConjInvol_apply, lpCoordProj_apply]
  split_ifs <;> simp

/-- The cyclic separating vector `(√(w i))_{i ∈ ι}` in `ℓ²(ι)` for a positive summable weight `w`. -/
def diagOmega (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hsum : Summable w) : lp (fun _ : ι => ℂ) 2 :=
  ⟨fun i => ((Real.sqrt (w i) : ℝ) : ℂ), by
    refine memℓp_gen ?_
    have h2 : ENNReal.toReal 2 = (2 : ℝ) := by norm_num
    refine hsum.congr fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      h2, Real.rpow_two, Real.sq_sqrt (hw i).le]⟩

@[simp] theorem diagOmega_apply (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hsum : Summable w) (i : ι) :
    diagOmega w hw hsum i = ((Real.sqrt (w i) : ℝ) : ℂ) := rfl

/-- Standard form on `diagVN ι` associated to a strictly positive summable weight `w`. -/
def diagStandardForm [DecidableEq ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hsum : Summable w) :
    StandardForm (diagVN ι) where
  Ω := diagOmega w hw hsum
  separating := fun A hA hA0 => by
    have hdiag0 : ∀ i : ι, A (lp.single 2 i 1) i = 0 := by
      intro i
      have hi : A (diagOmega w hw hsum) i = 0 := by
        rw [hA0]; rfl
      rw [diagVN_apply_eq hA, diagOmega_apply] at hi
      have hne : (((Real.sqrt (w i) : ℝ) : ℂ)) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw i)).ne'
      exact (mul_eq_zero.mp hi).resolve_right hne
    refine ContinuousLinearMap.ext fun f => lp.ext <| funext fun i => ?_
    rw [diagVN_apply_eq hA, hdiag0 i, zero_mul]
    rfl
  cyclic := fun f => by
    let Ωv := diagOmega w hw hsum
    have hhas : HasSum (fun i : ι => lp.single 2 i (f i)) f :=
      lp.hasSum_single ENNReal.ofNat_ne_top f
    refine mem_closure_of_tendsto hhas ?_
    refine Eventually.of_forall fun s => ?_
    let A_s : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
      ∑ i ∈ s, (f i / Ωv i) • lpCoordProj i
    have hAs_mem : A_s ∈ diagVN ι :=
      sum_mem fun i _ => (diagVN ι).toStarSubalgebra.smul_mem (lpCoordProj_mem_diagVN i) _
    refine ⟨⟨A_s, hAs_mem⟩, ?_⟩
    change A_s Ωv = ∑ i ∈ s, lp.single 2 i (f i)
    simp only [A_s, _root_.sum_apply, _root_.smul_apply, lpCoordProj_eq_single]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hΩi : Ωv i ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw i)).ne'
    ext j
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
    split_ifs with hj
    · subst hj; exact div_mul_cancel₀ (f j) hΩi
    · simp
  J := lpConjInvol ι
  J_omega := by ext i; exact Complex.conj_ofReal _
  conj_mem_commutant_iff := fun A => by
    rw [diagVN_commutant_eq, mem_diagVN_iff, mem_diagVN_iff]
    refine ⟨fun h i => ?_, fun h i => ?_⟩
    · have hi := congr_arg (lpConjInvol ι).conjOp (h i)
      simpa [AntiunitaryInvol.conjOp_mul, lpConjInvol_conjOp_coordProj] using hi
    · have hi := congr_arg (lpConjInvol ι).conjOp (h i)
      simpa [AntiunitaryInvol.conjOp_mul, lpConjInvol_conjOp_coordProj] using hi
  natural_cone_pos := fun A hA => by
    let Ωv := diagOmega w hw hsum
    have hterm : ∀ i : ι,
        (inner ℂ (Ωv i) (A ((lpConjInvol ι).conjOp A Ωv) i)).re =
          w i * ‖A (lp.single 2 i 1) i‖ ^ 2 := by
      intro i
      have hJA_mem : (lpConjInvol ι).conjOp A ∈ diagVN ι := by
        rw [mem_diagVN_iff]
        intro j
        have hj := congr_arg (lpConjInvol ι).conjOp ((mem_diagVN_iff A).mp hA j)
        simpa [AntiunitaryInvol.conjOp_mul, lpConjInvol_conjOp_coordProj] using hj
      have hJA_diag : (lpConjInvol ι).conjOp A (lp.single 2 i 1) i =
          starRingEnd ℂ (A (lp.single 2 i 1) i) := by
        change starRingEnd ℂ (A (lpConjInvol ι (lp.single 2 i 1)) i) = _
        have hs : lpConjInvol ι (lp.single 2 i 1) = lp.single 2 i 1 := by
          ext j
          simp only [lpConjInvol_apply, lp.single_apply, Pi.single_apply]
          split_ifs <;> simp
        rw [hs]
      rw [diagVN_apply_eq hA, diagVN_apply_eq hJA_mem, hJA_diag, RCLike.inner_apply]
      simp only [Ωv, diagOmega_apply, Complex.conj_ofReal]
      set z := A (lp.single 2 i 1) i
      have hz : z * starRingEnd ℂ z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hcalc : (z * (starRingEnd ℂ z * ((Real.sqrt (w i) : ℝ) : ℂ))) *
            ((Real.sqrt (w i) : ℝ) : ℂ) = ((w i * ‖z‖ ^ 2 : ℝ) : ℂ) := by
        calc (z * (starRingEnd ℂ z * ((Real.sqrt (w i) : ℝ) : ℂ))) * ((Real.sqrt (w i) : ℝ) : ℂ)
            = (z * starRingEnd ℂ z) * (((Real.sqrt (w i) : ℝ) : ℂ) ^ 2) := by ring
          _ = ((‖z‖ ^ 2 : ℝ) : ℂ) * ((w i : ℝ) : ℂ) := by
              rw [hz, ← Complex.ofReal_pow, Real.sq_sqrt (hw i).le]
          _ = ((w i * ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hcalc, Complex.ofReal_re]
    have hsum_inner := lp.summable_inner (𝕜 := ℂ) Ωv (A ((lpConjInvol ι).conjOp A Ωv))
    have hre_eq : (inner ℂ Ωv (A ((lpConjInvol ι).conjOp A Ωv))).re =
        ∑' i : ι, (inner ℂ (Ωv i) (A ((lpConjInvol ι).conjOp A Ωv) i)).re := by
      rw [lp.inner_eq_tsum]
      exact Complex.reCLM.map_tsum hsum_inner
    change 0 ≤ (inner ℂ Ωv (A ((lpConjInvol ι).conjOp A Ωv))).re
    rw [hre_eq]
    exact tsum_nonneg fun i => by
      rw [hterm i]
      exact mul_nonneg (hw i).le (sq_nonneg _)

end DiagonalStandardForm

/-- The positive rational unit `n + 1 ∈ ℚ_{>0}` attached to `n : ℕ`. -/
def natPosUnit (n : ℕ) : posUnits :=
  ⟨Units.mk0 ((n : ℚ) + 1) (by positivity), by
    show (0 : ℚ) < (n : ℚ) + 1
    positivity⟩

theorem logPos_natPosUnit (n : ℕ) : logPos (natPosUnit n) = Real.log ((n : ℝ) + 1) := by
  simp [logPos, natPosUnit]

/-- **Every standard-form partner representation of `ℚ_{>0}` is central and unitary.** -/
theorem standardForm_partner_rep_is_central_unitary
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (ms : StandardForm M)
    {U : posUnits → H →L[ℂ] H} (hU1 : U 1 = 1) (hUmul : ∀ r s, U (r * s) = U r * U s)
    (hUM : ∀ r, U r ∈ M) (hUJ : ∀ r, ms.J.conjOp (U r) = U r⁻¹) (r : posUnits) :
    U r ∈ M.commutant ∧ U r⁻¹ = star (U r) ∧ U r * star (U r) = 1 ∧ star (U r) * U r = 1 := by
  have hJmem : ms.J.conjOp (U r) ∈ M := by rw [hUJ]; exact hUM r⁻¹
  obtain ⟨hcomm, hstar, _⟩ := ms.tomita_central_eq_star (hUM r) hJmem
  have hinv_star : U r⁻¹ = star (U r) := hUJ r ▸ hstar
  refine ⟨hcomm, hinv_star, ?_, ?_⟩
  · rw [← hinv_star, ← hUmul, mul_inv_cancel, hU1]
  · rw [← hinv_star, ← hUmul, inv_mul_cancel, hU1]

/-- **Exact operator-algebraic characterization of Question 1 over `ℤ` (exact Born rule).**
There exists a standard-form von Neumann algebra `(H, M, ms)` carrying rational dilations `U` on
which modular conjugation acts as the partner involution `U(r) ↦ U(r⁻¹)` and whose natural-cone
form on integer sources `∑_{i < N} a_i U(i + 1)` equals `integerProbe N a` if and only if
`RiemannHypothesis` holds. -/
theorem riemannHypothesis_iff_exists_standardForm_bornRule :
    RiemannHypothesis ↔
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (M : VonNeumannAlgebra H) (ms : StandardForm M) (U : posUnits → H →L[ℂ] H),
        U 1 = 1 ∧ (∀ r s, U (r * s) = U r * U s) ∧ (∀ r, U r ∈ M) ∧
        (∀ r, ms.J.conjOp (U r) = U r⁻¹) ∧
        ∀ (N : ℕ) (a : Fin N → ℤ),
          let X : H →L[ℂ] H := ∑ i : Fin N, (a i : ℂ) • U (natPosUnit i)
          (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re = integerProbe N a := by
  classical
  constructor
  · intro hRH
    have hW := RHTower.weilPositiveFull_vonMangoldt_of_riemannHypothesis hRH
    obtain ⟨γ, c, _, hc0, hcsum, hreindex⟩ :=
      exists_nat_reindex RHTower.WeilConditional.countable_criticalOrdinates
        (weilWeight hW) (weilWeight_nonneg hW) (summable_weilWeight hW)
    let spos : Set ℕ := {n : ℕ | 0 < c n}
    let ι := spos
    let w : ι → ℝ := fun i => c i.1
    have hw : ∀ i : ι, 0 < w i := fun i => i.2
    have hwsum : Summable w := hcsum.comp_injective Subtype.val_injective
    let H := lp (fun _ : ι => ℂ) 2
    let M := diagVN ι
    let ms := diagStandardForm w hw hwsum
    let U : posUnits → H →L[ℂ] H := fun r =>
      lpDiagonalCLM (fun i : ι => archChar (-γ i.1) ((r : ℚˣ) : ℚ)) zero_le_one
        (fun i => (norm_archChar _ _).le)
    have hU1 : U 1 = 1 := by
      refine ContinuousLinearMap.ext fun f => lp.ext <| funext fun i => ?_
      change archChar (-γ i.1) ((((1 : posUnits) : ℚˣ) : ℚ)) * f i = f i
      rw [Subgroup.coe_one, Units.val_one, archChar_one, one_mul]
    have hUmul : ∀ r s : posUnits, U (r * s) = U r * U s := by
      intro r s
      refine ContinuousLinearMap.ext fun f => lp.ext <| funext fun i => ?_
      change archChar (-γ i.1) ((((r * s : posUnits) : ℚˣ) : ℚ)) * f i =
        archChar (-γ i.1) ((r : ℚˣ) : ℚ) * (archChar (-γ i.1) ((s : ℚˣ) : ℚ) * f i)
      rw [Subgroup.coe_mul, Units.val_mul, archChar_mul (-γ i.1) r.2 s.2, mul_assoc]
    have hUM : ∀ r : posUnits, U r ∈ M := fun r =>
      lpDiagonalCLM_mem_diagVN _ zero_le_one _
    have hUJ : ∀ r : posUnits, ms.J.conjOp (U r) = U r⁻¹ := by
      intro r
      refine ContinuousLinearMap.ext fun f => lp.ext <| funext fun i => ?_
      change starRingEnd ℂ (archChar (-γ i.1) ((r : ℚˣ) : ℚ) * starRingEnd ℂ (f i)) =
        archChar (-γ i.1) (((r⁻¹ : posUnits) : ℚˣ) : ℚ) * f i
      rw [map_mul, Complex.conj_conj, Subgroup.coe_inv, Units.val_inv_eq_inv_val,
        archChar_inv (-γ i.1) r.2]
      rfl
    have hcorr : ∀ u : posUnits, inner ℂ ms.Ω (U u ms.Ω) = ratCorr u := by
      intro u
      rw [lp.inner_eq_tsum]
      have hterm : ∀ i : ι,
          inner ℂ (ms.Ω i) (U u ms.Ω i) = (c i.1 : ℂ) * archChar (-γ i.1) ((u : ℚˣ) : ℚ) := by
        intro i
        rw [RCLike.inner_apply]
        change (archChar (-γ i.1) ((u : ℚˣ) : ℚ) * ((Real.sqrt (c i.1) : ℝ) : ℂ)) *
          starRingEnd ℂ ((Real.sqrt (c i.1) : ℝ) : ℂ) = _
        rw [Complex.conj_ofReal]
        calc (archChar (-γ i.1) ((u : ℚˣ) : ℚ) * ((Real.sqrt (c i.1) : ℝ) : ℂ)) *
              ((Real.sqrt (c i.1) : ℝ) : ℂ)
            = (((Real.sqrt (c i.1) : ℝ) ^ 2 : ℝ) : ℂ) * archChar (-γ i.1) ((u : ℚˣ) : ℚ) := by
              push_cast; ring
          _ = (c i.1 : ℂ) * archChar (-γ i.1) ((u : ℚˣ) : ℚ) := by
              rw [Real.sq_sqrt i.2.le]
      simp_rw [hterm]
      let g : ℕ → ℂ := fun n => (c n : ℂ) * archChar (-γ n) ((u : ℚˣ) : ℚ)
      have hsub : (∑' i : spos, g i.1) = ∑' n : ℕ, g n := by
        refine @tsum_subtype_eq_of_support_subset ℂ ℕ _ _ g spos ?_
        intro n hn
        have hcn : c n ≠ 0 := by
          intro h0
          exact hn (by simp [g, h0])
        exact lt_of_le_of_ne (hc0 n) hcn.symm
      change (∑' i : spos, g i.1) = ratCorr u
      rw [hsub]
      change (∑' n : ℕ, (c n : ℂ) * archChar (-γ n) ((u : ℚˣ) : ℚ)) = ratCorr u
      rw [hreindex (fun r => archChar (-r) ((u : ℚˣ) : ℚ)), ratCorr_eq_tsum hW u]
    refine ⟨H, inferInstance, inferInstance, inferInstance, M, ms, U, hU1, hUmul, hUM, hUJ,
      fun N a => ?_⟩
    intro X
    have hXJ : ms.J.conjOp X = ∑ i : Fin N, (a i : ℂ) • U (natPosUnit i)⁻¹ := by
      simp only [X, AntiunitaryInvol.conjOp_sum, AntiunitaryInvol.conjOp_smul, hUJ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_intCast]
    have hexp :
        inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω)) =
          ∑ i : Fin N, ∑ j : Fin N,
            star (a i : ℂ) * ratCorr ((natPosUnit i)⁻¹ * natPosUnit j) * (a j : ℂ) := by
      rw [hXJ]
      simp only [X, _root_.sum_apply, _root_.smul_apply,
        map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have hUij : U (natPosUnit j) (U (natPosUnit i)⁻¹ ms.Ω) =
          U ((natPosUnit i)⁻¹ * natPosUnit j) ms.Ω := by
        rw [mul_comm (natPosUnit i)⁻¹, hUmul]
        rfl
      rw [hUij, hcorr]
      have hconj : star (a i : ℂ) = (a i : ℂ) := by simp
      rw [hconj]
      ring
    have hgram := dotProduct_weilGram_eq_ratCorr (fun i : Fin N => natPosUnit i)
      (fun i : Fin N => (a i : ℂ))
    simp_rw [logPos_natPosUnit] at hgram
    unfold integerProbe HTGeometry.hermQuad atomGram
    rw [hexp, ← hgram]
  · rintro ⟨H, _, _, _, M, ms, U, _, _, hUM, _, hform⟩
    refine riemannHypothesis_iff_integerProbes.mpr fun N a => ?_
    let X : H →L[ℂ] H := ∑ i : Fin N, (a i : ℂ) • U (natPosUnit i)
    have hXM : X ∈ M := sum_mem fun i _ => M.toStarSubalgebra.smul_mem (hUM _) _
    rw [← hform N a]
    exact ms.natural_cone_pos X hXM

/-- **Asymptotic (Tate-limit) characterization of Question 1 over `ℤ`.** Relaxing equality to
asymptotic quadratic growth `Q` along integer rays yields the exact same `RiemannHypothesis`
criterion. -/
theorem riemannHypothesis_iff_exists_standardForm_tateLimit :
    RiemannHypothesis ↔
      ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
        (M : VonNeumannAlgebra H) (ms : StandardForm M) (U : posUnits → H →L[ℂ] H),
        U 1 = 1 ∧ (∀ r s, U (r * s) = U r * U s) ∧ (∀ r, U r ∈ M) ∧
        (∀ r, ms.J.conjOp (U r) = U r⁻¹) ∧
        ∀ (N : ℕ) (a : Fin N → ℤ),
          Tendsto (fun m : ℕ =>
            let X : H →L[ℂ] H := ∑ i : Fin N, ((m • a) i : ℂ) • U (natPosUnit i)
            (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re / (m : ℝ) ^ 2)
            atTop (𝓝 (integerProbe N a)) := by
  constructor
  · intro hRH
    obtain ⟨H, inst1, inst2, inst3, M, ms, U, h1, hmul, hM, hJ, hform⟩ :=
      riemannHypothesis_iff_exists_standardForm_bornRule.mp hRH
    refine ⟨H, inst1, inst2, inst3, M, ms, U, h1, hmul, hM, hJ, fun N a => ?_⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm2 : (m : ℝ) ^ 2 ≠ 0 := by positivity
    dsimp only
    rw [hform N (m • a), integerProbe_smul, mul_div_cancel_left₀ _ hm2]
  · rintro ⟨H, _, _, _, M, ms, U, _, _, hUM, _, htate⟩
    refine riemannHypothesis_iff_integerProbes.mpr fun N a => ?_
    refine nonneg_of_tateLimit
      (K := fun b : Fin N → ℤ =>
        let X : H →L[ℂ] H := ∑ i : Fin N, (b i : ℂ) • U (natPosUnit i)
        (inner ℂ ms.Ω (X (ms.J.conjOp X ms.Ω))).re)
      (fun b => ms.natural_cone_pos _ (sum_mem fun i _ => M.toStarSubalgebra.smul_mem (hUM _) _))
      (htate N a)

end GaloisForLFunctions.CountingHolography
