import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SpanContactLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw
import GaloisForLFunctions.HTGeometry.IsometricCongruenceInertia
import Mathlib.LinearAlgebra.Lagrange

/-!
# The Pontryagin law over `𝔽_q`: the span defect counts the outer eigenvalues

For a curve datum the defect Gram of the window `Γ₀, …, Γ_{n−1}` of Frobenius graphs, in the
normalized coordinates `e_k = q^{k/2} d_k`, is the Toeplitz matrix `G_{kl} = Re Σ_i β_i^{|k−l|}`
(`spanGram`); on real classes it is the Castelnuovo–Severi defect (`hermQuad_spanGram_ofReal`).
The functional equation and conjugation make the eigenvalues closed under the circle reflection
`β ↦ 1/β̄` (`β_reflPerm`), and the Gram is the reflected evaluation form (`spanGram_sesq`)

    x* G y = Σ_i conj(E_x(β_i)) E_y(1/β̄_i),     E_x(z) = Σ_{k < n} x_k z^k.

This is the zero-configuration form of the scaling surface with `ρ ↦ 1 − ρ̄` replaced by
`β ↦ 1/β̄`, and its negative squares are counted exactly (`pontryagin_law_curve`):

* *upper bound* (`negIndex_spanGram_le`): on the common kernel of the evaluations at the
  eigenvalues outside the unit circle every summand is `|E(β)|² ≥ 0` or `0`, so the defect has at
  most `#{distinct β : |β| > 1}` negative squares on every window;
* *attainment* (`negIndex_spanGram_eq`): once the window holds the spectrum (`n ≥ #{β}`, at most
  `2g`), Lagrange interpolation gives, for each outer `z`, a window class with `E = 1` at `z`,
  `−1` at `1/z̄` and `0` elsewhere on the spectrum; their Gram matrix is diagonal with entries
  `−(m(z) + m(1/z̄))`.

So the Hodge defect over `𝔽_q` is the number of distinct Frobenius eigenvalues of absolute value
`> √q`, independent of their depth and multiplicity, nondecreasing in the window
(`negIndex_spanGram_mono`) and fully visible at window `2g`. In particular Hodge index on the
window `2g` is RH for the datum (`unitary_iff_negIndex_spanGram_eq_zero`), and the golden fake curve
has Hodge defect exactly `1` from window `2` on (`goldenDatum_negIndex_spanGram`). This is the
`𝔽_q` calibration of `pontryagin_law`: over `ℚ` the genus is infinite, there is no finite window
that holds the spectrum, and the degree filtration `hodgeDefectAt` replaces the window.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Complex Finset Matrix Polynomial
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Compression -/

/-- Compression never increases the negative index: `#neg(Sᴴ H S) ≤ #neg H` for every
rectangular `S`. -/
theorem negIndex_compress_le {m n : Type*} [Fintype m] [Fintype n] (H : Matrix m m ℂ)
    (S : Matrix m n ℂ) : hermNegIndex (Sᴴ * H * S) ≤ hermNegIndex H := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(Sᴴ * H * S))
  have hq : ∀ x, hermQuad (-(Sᴴ * H * S)) x = hermQuad (-H) (S *ᵥ x) := fun x => by
    rw [hermQuad_neg, hermQuad_neg, hermQuad_rect_conjugate]
  have hinj : Function.Injective (S.mulVecLin.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, Matrix.mulVecLin_apply] at hy
    by_contra hy0
    have hpos := hW _ y.2 fun h => hy0 (Subtype.ext h)
    rw [hq, hy] at hpos
    simp [hermQuad] at hpos
  have hmap : IsPosDefOn (-H) (W.map S.mulVecLin) := by
    rintro _ ⟨x, hx, rfl⟩ hx0
    have hxne : x ≠ 0 := fun h => hx0 (by simp [h])
    have := hW x hx hxne
    rwa [hq] at this
  have heq : Module.finrank ℂ W = Module.finrank ℂ (W.map S.mulVecLin) := by
    rw [← LinearMap.range_domRestrict]
    exact (LinearEquiv.ofInjective _ hinj).finrank_eq
  rw [hermNegIndex, hermNegIndex, ← hrank, heq]
  exact finrank_le_posIndex hmap

/-- Entries of a compression are values of the sesquilinear form on the columns. -/
theorem compress_apply {m n : Type*} [Fintype m] (H : Matrix m m ℂ) (S : Matrix m n ℂ) (a b : n) :
    (Sᴴ * H * S) a b = star (fun k => S k a) ⬝ᵥ (H *ᵥ fun k => S k b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, mulVec, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ### The circle reflection -/

/-- Reflection in the unit circle, `z ↦ 1/z̄`: the functional equation composed with
conjugation. -/
def circleReflect (z : ℂ) : ℂ := (starRingEnd ℂ z)⁻¹

theorem circleReflect_circleReflect (z : ℂ) : circleReflect (circleReflect z) = z := by
  simp [circleReflect, map_inv₀]

theorem norm_circleReflect (z : ℂ) : ‖circleReflect z‖ = ‖z‖⁻¹ := by
  rw [circleReflect, norm_inv, Complex.norm_conj]

theorem circleReflect_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : circleReflect z = z := by
  have h : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [circleReflect]
  exact (eq_inv_of_mul_eq_one_left h).symm

/-- An outer point reflects inside the unit circle. -/
theorem norm_circleReflect_lt_one {z : ℂ} (hz : 1 < ‖z‖) : ‖circleReflect z‖ < 1 := by
  rw [norm_circleReflect]
  exact inv_lt_one_of_one_lt₀ hz

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

theorem β_ne_zero (i : ι) : D.β i ≠ 0 := fun h => by
  have := D.β_fePerm i
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-- The circle reflection permutes the eigenvalues. -/
def reflPerm : Equiv.Perm ι := D.conjPerm.symm.trans D.fePerm

theorem β_reflPerm (j : ι) : D.β (D.reflPerm j) = circleReflect (D.β j) := by
  have h2 := D.β_conjPerm (D.conjPerm.symm j)
  rw [Equiv.apply_symm_apply] at h2
  have h3 : D.β (D.conjPerm.symm j) = starRingEnd ℂ (D.β j) := by rw [h2, Complex.conj_conj]
  show D.β (D.fePerm (D.conjPerm.symm j)) = _
  rw [circleReflect, ← h3]
  exact eq_inv_of_mul_eq_one_left (D.β_fePerm _)

/-- The power sum at lag `|k − l|` splits along the functional equation:
`Σ_i β_i^{|k−l|} = Σ_i β_i^k β_{fe i}^l`. -/
theorem powerSum_dist (k l : ℕ) :
    D.powerSum (Nat.dist k l) = ∑ i, D.β i ^ k * D.β (D.fePerm i) ^ l := by
  rcases le_total l k with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left, powerSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : D.β i ^ (l + d) * D.β (D.fePerm i) ^ l = D.β i ^ d * (D.β (D.fePerm i) * D.β i) ^ l := by
      ring
    rw [e, D.β_fePerm, one_pow, mul_one]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left, powerSum,
      ← Equiv.sum_comp D.fePerm (fun j => D.β j ^ d)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : D.β i ^ k * D.β (D.fePerm i) ^ (k + d) =
        D.β (D.fePerm i) ^ d * (D.β (D.fePerm i) * D.β i) ^ k := by
      ring
    rw [e, D.β_fePerm, one_pow, mul_one]

end CurveDatum

/-! ### The window Gram -/

/-- Evaluation of the window polynomial `Σ_{k < n} x_k X^k` at `z`. -/
def windowEval (n : ℕ) (z : ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ k, x k * z ^ (k : ℕ)
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

theorem windowEval_apply (n : ℕ) (z : ℂ) (x : Fin n → ℂ) :
    windowEval n z x = ∑ k, x k * z ^ (k : ℕ) := rfl

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The defect Gram of the window `Γ₀, …, Γ_{n−1}` in normalized coordinates,
`G_{kl} = Re Σ_i β_i^{|k−l|}`. -/
def spanGram (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun k l => (D.trace (Nat.dist k l) : ℂ)

/-- On real window classes the Gram form is the Toeplitz form, i.e. the Castelnuovo–Severi defect
`2(D·H)(D·V) − D²` of `Σ_k q^{−k/2} e_k Γ_k` (`spanDefect_eq_toeplitz`). -/
theorem hermQuad_spanGram_ofReal (n : ℕ) (e : ℕ → ℝ) :
    hermQuad (D.spanGram n) (fun k => (e k : ℂ)) = D.toeplitz (range n) e := by
  rw [hermQuad, toeplitz, ← Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ range n,
    e k * e l * D.trace (Nat.dist k l))]
  simp only [mulVec, dotProduct, spanGram, Pi.star_apply, Complex.star_def, Complex.conj_ofReal,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => e k * e l * D.trace (Nat.dist k l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (e k : ℂ) * ((D.trace (Nat.dist k l) : ℂ) * (e l : ℂ)) =
    ((e k * e l * D.trace (Nat.dist k l) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-- **The Gram is the reflected evaluation form**:
`x* G y = Σ_i conj(E_x(β_i)) E_y(1/β̄_i)`. -/
theorem spanGram_sesq (n : ℕ) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (D.spanGram n *ᵥ y) =
      ∑ j, starRingEnd ℂ (windowEval n (D.β j) x) * windowEval n (circleReflect (D.β j)) y := by
  have hG : ∀ k l : Fin n,
      D.spanGram n k l = ∑ i, D.β i ^ (k : ℕ) * D.β (D.fePerm i) ^ (l : ℕ) := fun k l => by
    rw [spanGram, ← powerSum_eq_trace, powerSum_dist]
  have hr : ∀ i, circleReflect (starRingEnd ℂ (D.β i)) = D.β (D.fePerm i) := fun i => by
    rw [circleReflect, Complex.conj_conj]
    exact (eq_inv_of_mul_eq_one_left (D.β_fePerm i)).symm
  have hL : star x ⬝ᵥ (D.spanGram n *ᵥ y) = ∑ k : Fin n, ∑ l : Fin n, ∑ i,
      starRingEnd ℂ (x k) * (D.β i ^ (k : ℕ) * D.β (D.fePerm i) ^ (l : ℕ) * y l) := by
    simp only [dotProduct, mulVec, hG, Pi.star_apply, Complex.star_def, Finset.mul_sum,
      Finset.sum_mul]
  rw [hL, ← Equiv.sum_comp D.conjPerm]
  simp only [D.β_conjPerm, hr, windowEval_apply, map_sum, map_mul, map_pow, Complex.conj_conj,
    Finset.sum_mul, Finset.mul_sum]
  calc ∑ k : Fin n, ∑ l : Fin n, ∑ i,
        starRingEnd ℂ (x k) * (D.β i ^ (k : ℕ) * D.β (D.fePerm i) ^ (l : ℕ) * y l)
      = ∑ k : Fin n, ∑ i, ∑ l : Fin n,
        starRingEnd ℂ (x k) * (D.β i ^ (k : ℕ) * D.β (D.fePerm i) ^ (l : ℕ) * y l) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ k : Fin n, ∑ l : Fin n,
        starRingEnd ℂ (x k) * (D.β i ^ (k : ℕ) * D.β (D.fePerm i) ^ (l : ℕ) * y l) :=
        Finset.sum_comm
    _ = ∑ i, ∑ l : Fin n, ∑ k : Fin n,
        starRingEnd ℂ (x k) * (D.β i ^ (k : ℕ) * D.β (D.fePerm i) ^ (l : ℕ) * y l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ =>
        Finset.sum_congr rfl fun k _ => by ring

/-- The eigenvalues outside the unit circle, i.e. `|α| > √q`, without multiplicity. -/
def outerSpectrum : Finset ℂ := D.spectrum.filter fun z => 1 < ‖z‖

theorem mem_outerSpectrum {i : ι} (hi : 1 < ‖D.β i‖) : D.β i ∈ D.outerSpectrum :=
  Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩

/-- **Upper bound.** On every window the defect has at most `#{distinct β : |β| > 1}` negative
squares. -/
theorem negIndex_spanGram_le (n : ℕ) : hermNegIndex (D.spanGram n) ≤ D.outerSpectrum.card := by
  have h := negIndex_le_card_of_nonneg_on_ker (D.spanGram n)
    (fun z : D.outerSpectrum => windowEval n (z : ℂ)) fun x hx => ?_
  · simpa using h
  have hker : ∀ i, 1 < ‖D.β i‖ → windowEval n (D.β i) x = 0 := fun i hi =>
    hx ⟨D.β i, D.mem_outerSpectrum hi⟩
  rw [hermQuad, spanGram_sesq, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  rcases lt_trichotomy ‖D.β j‖ 1 with h | h | h
  · have hout : 1 < ‖D.β (D.reflPerm j)‖ := by
      rw [D.β_reflPerm, norm_circleReflect]
      exact one_lt_inv₀ (norm_pos_iff.mpr (D.β_ne_zero j)) |>.mpr h
    rw [← D.β_reflPerm, hker _ hout, mul_zero, Complex.zero_re]
  · rw [circleReflect_of_norm_one h, mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · rw [hker j h, map_zero, zero_mul, Complex.zero_re]

/-- The interpolation target of an outer point: `1` at `z`, `−1` at `1/z̄`. -/
def pairValue (z w : ℂ) : ℂ := (if w = z then 1 else 0) - (if w = circleReflect z then 1 else 0)

/-- The reflected product of two targets is diagonal in the outer points. -/
theorem pairValue_mul {z w : ℂ} (hz : 1 < ‖z‖) (hw : 1 < ‖w‖) (v : ℂ) :
    starRingEnd ℂ (pairValue z v) * pairValue w (circleReflect v) =
      if z = w then -((if v = z then 1 else 0) + (if v = circleReflect z then 1 else 0)) else 0 := by
  have hzr : circleReflect z ≠ z := fun h => by
    have := norm_circleReflect_lt_one hz; rw [h] at this; linarith
  have hzw : z ≠ circleReflect w := fun h => by
    have := norm_circleReflect_lt_one hw; rw [← h] at this; linarith
  have hwz : circleReflect z ≠ w := fun h => by
    have := norm_circleReflect_lt_one hz; rw [h] at this; linarith
  have hinj : ∀ a b : ℂ, circleReflect a = circleReflect b ↔ a = b := fun a b =>
    ⟨fun h => by rw [← circleReflect_circleReflect a, h, circleReflect_circleReflect], fun h => h ▸ rfl⟩
  have hcr : ∀ a b : ℂ, circleReflect a = b ↔ a = circleReflect b := fun a b => by
    rw [← hinj, circleReflect_circleReflect]
  simp only [pairValue, hinj, hcr]
  by_cases hvz : v = z
  · subst hvz
    by_cases h : v = w
    · subst h; simp [hzr.symm]
    · simp [h, hzw, hzr.symm]
  · by_cases hvr : v = circleReflect z
    · subst hvr
      by_cases h : z = w
      · subst h; simp [hvz]
      · have h' : circleReflect z ≠ circleReflect w := fun e => h ((hinj z w).mp e)
        simp [h, hvz, h', hwz]
    · simp [hvz, hvr]

/-- The Lagrange interpolant of the target of `z` on the spectrum. -/
def pairPoly (z : ℂ) : ℂ[X] := Lagrange.interpolate D.spectrum id (pairValue z)

/-- The interpolant as a window class. -/
def pairClass (n : ℕ) (z : ℂ) : Fin n → ℂ := fun k => (D.pairPoly z).coeff k

theorem windowEval_pairClass {n : ℕ} (hn : D.spectrum.card ≤ n) (z : ℂ) {w : ℂ}
    (hw : w ∈ D.spectrum) : windowEval n w (D.pairClass n z) = pairValue z w := by
  have hinj : Set.InjOn (id : ℂ → ℂ) D.spectrum := Set.injOn_id _
  have hdeg : (D.pairPoly z).degree < D.spectrum.card := Lagrange.degree_interpolate_lt _ hinj
  have hpos : 0 < n := lt_of_lt_of_le (Finset.card_pos.mpr ⟨w, hw⟩) hn
  have hnat : (D.pairPoly z).natDegree < n := by
    by_cases hP : D.pairPoly z = 0
    · rw [hP, natDegree_zero]; exact hpos
    · exact lt_of_lt_of_le ((natDegree_lt_iff_degree_lt hP).mpr hdeg) hn
  simp only [windowEval_apply, pairClass]
  rw [Fin.sum_univ_eq_sum_range (fun k => (D.pairPoly z).coeff k * w ^ k),
    ← eval_eq_sum_range' hnat]
  exact Lagrange.eval_interpolate_at_node _ hinj hw

/-- **Attainment.** Once the window holds the spectrum, the defect has exactly
`#{distinct β : |β| > 1}` negative squares. -/
theorem negIndex_spanGram_eq {n : ℕ} (hn : D.spectrum.card ≤ n) :
    hermNegIndex (D.spanGram n) = D.outerSpectrum.card := by
  classical
  refine le_antisymm (D.negIndex_spanGram_le n) ?_
  set S : Matrix (Fin n) D.outerSpectrum ℂ := fun k z => D.pairClass n z k
  set μ : D.outerSpectrum → ℝ := fun z =>
    -(((univ.filter fun j => D.β j = z).card : ℝ) +
      (univ.filter fun j => D.β j = circleReflect z).card)
  have hout : ∀ z : D.outerSpectrum, 1 < ‖(z : ℂ)‖ := fun z => (Finset.mem_filter.mp z.2).2
  have hspec : ∀ z : D.outerSpectrum, (z : ℂ) ∈ D.spectrum := fun z => (Finset.mem_filter.mp z.2).1
  have hgram : Sᴴ * D.spanGram n * S = diagonal fun z => (μ z : ℂ) := by
    refine Matrix.ext fun z w => ?_
    rw [compress_apply, spanGram_sesq, diagonal_apply]
    have hval : ∀ (a : D.outerSpectrum) (v : ℂ), v ∈ D.spectrum →
        windowEval n v (fun k => S k a) = pairValue a v := fun a v hv =>
      D.windowEval_pairClass hn a hv
    have hβ : ∀ j, D.β j ∈ D.spectrum := fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j)
    simp_rw [hval _ _ (hβ _), ← D.β_reflPerm, hval _ _ (hβ _), D.β_reflPerm,
      pairValue_mul (hout z) (hout w)]
    by_cases hzw : z = w
    · subst hzw
      simp only [if_true, μ, Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_boole]
      push_cast; ring
    · have hne : (z : ℂ) ≠ w := fun h => hzw (Subtype.ext h)
      simp [hne, hzw]
  have hμ : ∀ z, μ z < 0 := fun z => by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp (hspec z)
    have : 0 < (univ.filter fun i => D.β i = z).card :=
      Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
    have : (0 : ℝ) < (univ.filter fun i => D.β i = z).card := by exact_mod_cast this
    have : (0 : ℝ) ≤ (univ.filter fun i => D.β i = circleReflect z).card := Nat.cast_nonneg _
    simp only [μ]
    linarith
  have h := negIndex_compress_le (D.spanGram n) S
  rw [hgram, negIndex_diagonal] at h
  have huniv : (univ.filter fun z => μ z < 0) = univ := Finset.filter_true_of_mem fun z _ => hμ z
  rwa [huniv, Finset.card_univ, Fintype.card_coe] at h

/-- The window defect is nondecreasing in the window. -/
theorem negIndex_spanGram_mono {m n : ℕ} (h : m ≤ n) :
    hermNegIndex (D.spanGram m) ≤ hermNegIndex (D.spanGram n) := by
  classical
  set S : Matrix (Fin n) (Fin m) ℂ := fun k l => if k = Fin.castLE h l then 1 else 0
  have hS : Sᴴ * D.spanGram n * S = D.spanGram m := by
    refine Matrix.ext fun a b => ?_
    rw [compress_apply]
    simp [S, dotProduct, mulVec, spanGram]
  have := negIndex_compress_le (D.spanGram n) S
  rwa [hS] at this

/-- **The Pontryagin law over `𝔽_q`.** The defect of the Frobenius span has at most
`#{distinct β : |β| > 1}` negative squares on every window, and exactly that many on every window
of length `≥ 2g`. -/
theorem pontryagin_law_curve :
    (∀ n, hermNegIndex (D.spanGram n) ≤ D.outerSpectrum.card) ∧
      ∀ n, Fintype.card ι ≤ n → hermNegIndex (D.spanGram n) = D.outerSpectrum.card :=
  ⟨D.negIndex_spanGram_le, fun _ hn =>
    D.negIndex_spanGram_eq ((Finset.card_image_le.trans (by simp)).trans hn)⟩

/-- **Hodge index on the window `2g` is RH for the datum.** -/
theorem unitary_iff_negIndex_spanGram_eq_zero :
    (∀ i, ‖D.β i‖ = 1) ↔ hermNegIndex (D.spanGram (Fintype.card ι)) = 0 := by
  rw [D.pontryagin_law_curve.2 _ le_rfl, Finset.card_eq_zero]
  constructor
  · intro hU
    refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨hzs, hz1⟩ := Finset.mem_filter.mp hz
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hzs
    rw [hU j] at hz1
    exact lt_irrefl _ hz1
  · intro h0 i
    have hle : ∀ j, ‖D.β j‖ ≤ 1 := fun j => by
      by_contra hj
      have := D.mem_outerSpectrum (not_le.mp hj)
      rw [h0] at this
      exact Finset.notMem_empty _ this
    refine le_antisymm (hle i) ?_
    have h := hle (D.reflPerm i)
    rw [D.β_reflPerm, norm_circleReflect] at h
    exact (inv_le_one₀ (norm_pos_iff.mpr (D.β_ne_zero i))).mp h

end CurveDatum

open Real in
/-- **The golden fake curve has Hodge defect exactly `1`** from the window `2` on: one negative
square, from the outer eigenvalue `φ`. -/
theorem goldenDatum_negIndex_spanGram {n : ℕ} (hn : 2 ≤ n) :
    hermNegIndex (goldenDatum.spanGram n) = 1 := by
  rw [goldenDatum.pontryagin_law_curve.2 n (by simpa using hn), Finset.card_eq_one]
  refine ⟨((goldenRatio : ℝ) : ℂ), Finset.ext fun z => ?_⟩
  have hφ : ‖((goldenRatio : ℝ) : ℂ)‖ = goldenRatio := by
    rw [Complex.norm_real, Real.norm_of_nonneg goldenRatio_pos.le]
  have hψ : ‖((goldenRatio⁻¹ : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr goldenRatio_pos).le]
    exact inv_lt_one_of_one_lt₀ one_lt_goldenRatio
  simp only [CurveDatum.outerSpectrum, CurveDatum.spectrum, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and, Fin.exists_fin_two, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hz⟩
    · exact h.symm
    · rw [← h] at hz
      exact absurd hz (not_lt.mpr hψ.le)
  · rintro rfl
    exact ⟨Or.inl rfl, by rw [hφ]; exact one_lt_goldenRatio⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
