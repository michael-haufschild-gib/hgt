import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.UpperLefschetzBoundsAreBlindOnlyToRealZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceRiemannRochAwayFromTheLowFrequencyDivisor

/-!
# The defect of a graph is twice its degree

On a polar surface, a cycle `x` with `x · V = 1` and `x² = 0` has `defect(x, x) = 2 (x · H)`: for
isotropic classes of unit vertical degree the Castelnuovo–Severi defect is a *linear* reading
(`PolarSurface.defect_self_of_isotropic`).

Over `𝔽_q` in genus one these are the graphs of endomorphisms. On the window surface `{Δ, Γ_F}`
of a curve datum, the class `graphCycle m n` of `m − nF` has `x · V = 1`,
`x · H = deg(m − nF) = m² − t m n + q n²` with `t = q + 1 − N₁` the Frobenius trace, and span
defect `2g(m² + qn²) − 2tmn` (`CurveDatum.windowSurface_defect_graphCycle`). In genus one it is
isotropic (adjunction) and its defect is `2 deg(m − nF)` (`CurveDatum.defect_graphCycle_of_genusOne`).
So in genus one the Hodge index on the window is degree positivity of `ℤ[F]`, which is Hasse's
proof: unitarity ⟺ `deg(m − nF) ≥ 0` for all integers ⟺ `t² ≤ 4q`
(`CurveDatum.genusOne_hasse_tfae`). The golden datum has `t = 5` and `deg(2 − F) = −1`.

Geometrically the classes `graphCycle m n` are graphs of isogenies, effective curves whose degree
counts a kernel; Hasse's positivity uses that `ℤ[F]` is a *ring* of correspondences, so additive
combinations of Frobenius have graphs, and the graph map is quadratic (theorem of the square,
`CurveDatum.graphCycle_square`). The scaling surface of `ℤ` has Hecke graphs of the
multiplicative monoid only: distinct Hecke scales are numerically free, so no parallelogram
relation holds among them even up to fibre classes (`heckeCorrespondence_no_square_relation`).
-/

open Complex Finset

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

namespace PolarSurface

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- **Isotropic classes of unit vertical degree have linear defect**: if `x · V = 1` and `x² = 0`,
then `defect(x, x) = 2 (x · H)`. -/
theorem defect_self_of_isotropic {x : E} (hV : S.pair x S.V = 1) (hx : S.pair x x = 0) :
    S.defect x x = 2 * S.pair x S.H := by
  rw [S.defect_self, hV, hx]; ring

end PolarSurface

namespace CurveDatum

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The Frobenius trace `t = √q · trace 1 = q + 1 − N₁`. -/
def frobTrace : ℝ := D.sqrtq * D.trace 1

theorem pointCount_one_eq : D.pointCount 1 = D.q + 1 - D.frobTrace := by
  simp [pointCount, frobTrace]

/-- The degree of `m − nF`: the norm form `m² − t m n + q n²`. -/
def endDeg (m n : ℝ) : ℝ := m ^ 2 - D.frobTrace * m * n + D.q * n ^ 2

/-- `deg(1 − F) = N₁`: the fixed points of Frobenius. -/
theorem endDeg_one_one : D.endDeg 1 1 = D.pointCount 1 := by
  rw [pointCount_one_eq]; unfold endDeg; ring

/-- The graph coefficients `d₀ = m`, `d₁ = −n` of `mΔ − nΓ_F`. -/
def graphCoeff (m n : ℝ) : ℕ → ℝ := fun k => if k = 0 then m else if k = 1 then -n else 0

/-- The class of the graph of `m − nF` on the window `{Δ, Γ_F}`: the combination `mΔ − nΓ_F`
corrected by fibres so that `x · V = 1` and `x · H = deg(m − nF)`. -/
def graphCycle (m n : ℝ) : SpanCycle :=
  (1 - m + n, D.endDeg m n - m + n * D.q, graphCoeff m n)

theorem windowB_graphCoeff (m n : ℝ) : windowB {0, 1} (graphCoeff m n) = m - n := by
  simp [windowB, graphCoeff]; ring

theorem windowA_graphCoeff (m n : ℝ) : D.windowA {0, 1} (graphCoeff m n) = m - n * D.q := by
  simp [windowA, graphCoeff]; ring

theorem pair_graphCycle_V (m n : ℝ) :
    (D.windowSurface {0, 1}).pair (D.graphCycle m n) (D.windowSurface {0, 1}).V = 1 := by
  rw [windowSurface_pair_V]
  simp only [graphCycle]
  rw [windowB_graphCoeff]; ring

theorem pair_graphCycle_H (m n : ℝ) :
    (D.windowSurface {0, 1}).pair (D.graphCycle m n) (D.windowSurface {0, 1}).H = D.endDeg m n := by
  rw [windowSurface_pair_H]
  simp only [graphCycle]
  rw [windowA_graphCoeff]; ring

/-- **The span defect of a graph class** on the window `{Δ, Γ_F}`:
`defect = 2g (m² + q n²) − 2 t m n` with `2g = #ι`. -/
theorem windowSurface_defect_graphCycle (m n : ℝ) :
    (D.windowSurface {0, 1}).defect (D.graphCycle m n) (D.graphCycle m n) =
      Fintype.card ι * (m ^ 2 + D.q * n ^ 2) - 2 * m * n * D.frobTrace := by
  rw [windowSurface_defect_self, spanDefect_eq_toeplitz]
  simp only [graphCycle, toeplitz, graphCoeff]
  simp [Finset.sum_insert, Nat.dist, D.trace_zero, frobTrace]
  rw [← D.sqrtq_sq]
  ring

/-- **Genus-one adjunction and the graph defect law.** If `#ι = 2`, the graph class of `m − nF`
is isotropic and its defect is twice its degree. -/
theorem defect_graphCycle_of_genusOne (hg : Fintype.card ι = 2) (m n : ℝ) :
    (D.windowSurface {0, 1}).defect (D.graphCycle m n) (D.graphCycle m n) = 2 * D.endDeg m n ∧
      (D.windowSurface {0, 1}).pair (D.graphCycle m n) (D.graphCycle m n) = 0 := by
  have hdef : (D.windowSurface {0, 1}).defect (D.graphCycle m n) (D.graphCycle m n) =
      2 * D.endDeg m n := by
    rw [windowSurface_defect_graphCycle, hg]; unfold endDeg; push_cast; ring
  refine ⟨hdef, ?_⟩
  have h := (D.windowSurface {0, 1}).defect_self (D.graphCycle m n)
  rw [hdef, pair_graphCycle_H, pair_graphCycle_V] at h
  linarith

/-- The real norm form `m² − t m n + q n²` is nonnegative everywhere iff `t² ≤ 4q`, and already
iff it is nonnegative at all integer points. -/
theorem endDeg_int_nonneg_iff : (∀ m n : ℤ, 0 ≤ D.endDeg m n) ↔ D.frobTrace ^ 2 ≤ 4 * D.q := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    -- a rational point strictly between the two real roots of `x² − t x + q`
    set t := D.frobTrace
    set r := Real.sqrt (t ^ 2 - 4 * D.q)
    have hr : 0 < r := Real.sqrt_pos.mpr (by linarith)
    have hr2 : r ^ 2 = t ^ 2 - 4 * D.q := Real.sq_sqrt (by linarith)
    obtain ⟨x, hx1, hx2⟩ := exists_rat_btwn (show (t - r) / 2 < (t + r) / 2 by linarith)
    have hneg : (x : ℝ) ^ 2 - t * x + D.q < 0 := by nlinarith
    have hden : (0 : ℝ) < (x.den : ℝ) := by exact_mod_cast x.den_pos
    have hxq : (x : ℝ) = (x.num : ℝ) / (x.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den x).symm
    have hval := h x.num x.den
    have heq : D.endDeg (x.num : ℤ) ((x.den : ℕ) : ℤ) =
        (x.den : ℝ) ^ 2 * ((x : ℝ) ^ 2 - t * x + D.q) := by
      rw [hxq]; unfold endDeg; push_cast; field_simp; ring
    have : D.endDeg (x.num : ℤ) ((x.den : ℕ) : ℤ) < 0 := by
      rw [heq]; exact mul_neg_of_pos_of_neg (by positivity) hneg
    push_cast at hval this
    linarith
  · intro h m n
    unfold endDeg
    nlinarith [sq_nonneg ((m : ℝ) - D.frobTrace * n / 2), sq_nonneg (n : ℝ)]

end CurveDatum

namespace CurveDatum

variable (D : CurveDatum (Fin 2))

/-- In genus one, a trace in `[−2, 2]` forces both eigenvalues onto the unit circle. -/
theorem unitary_of_abs_trace_one_le_two (h : |D.trace 1| ≤ 2) : ∀ i, ‖D.β i‖ = 1 := by
  -- the two eigenvalues are either self-reciprocal or reciprocal to each other
  have hsum : D.β 0 + D.β 1 = (D.trace 1 : ℂ) := by
    rw [← D.powerSum_eq_trace]; simp [powerSum, Fin.sum_univ_two]
  rcases Fin.exists_fin_two.mp ⟨D.fePerm 0, rfl⟩ with h0 | h0
  · -- `fePerm 0 = 0`, hence `fePerm 1 = 1`: both eigenvalues square to one
    have h1 : D.fePerm 1 = 1 := by
      have hinj := D.fePerm.injective
      rcases Fin.exists_fin_two.mp ⟨D.fePerm 1, rfl⟩ with h1 | h1
      · exact absurd (hinj (h1.trans h0.symm)) (by decide)
      · exact h1
    have hsq : ∀ i, D.β i * D.β i = 1 := by
      intro i; fin_cases i
      · have := D.β_fePerm 0; rwa [h0] at this
      · have := D.β_fePerm 1; rwa [h1] at this
    intro i
    have := congrArg norm (hsq i)
    rw [norm_mul, norm_one] at this
    nlinarith [norm_nonneg (D.β i)]
  · -- `fePerm 0 = 1`: `β₀ β₁ = 1` and `β₀ + β₁ = s` real with `|s| ≤ 2`
    have hprod : D.β 1 * D.β 0 = 1 := by have := D.β_fePerm 0; rwa [h0] at this
    set s := D.trace 1
    have hs2 : s ^ 2 ≤ 4 := by nlinarith [abs_le.mp h]
    have hroot : ∀ z : ℂ, z * ((s : ℂ) - z) = 1 → ‖z‖ = 1 := by
      intro z hz
      have hre := congrArg Complex.re hz
      have him := congrArg Complex.im hz
      simp [Complex.mul_re, Complex.mul_im] at hre him
      -- `y (s − 2x) = 0` and `x (s − x) + y² = 1`
      have hnorm : Complex.normSq z = 1 := by
        rw [Complex.normSq_apply]
        rcases mul_eq_zero.mp (show z.im * (s - 2 * z.re) = 0 by linarith) with hy | hx
        · rw [hy] at hre ⊢
          have : (z.re - s / 2) ^ 2 = s ^ 2 / 4 - 1 := by nlinarith
          have hsq : s ^ 2 = 4 := by nlinarith [sq_nonneg (z.re - s / 2)]
          nlinarith
        · have hxr : z.re = s / 2 := by linarith
          rw [hxr] at hre ⊢
          nlinarith
      rw [Complex.normSq_eq_norm_sq] at hnorm
      nlinarith [norm_nonneg z]
    have hb1 : D.β 1 = (s : ℂ) - D.β 0 := by rw [← hsum]; ring
    have h0' : ‖D.β 0‖ = 1 := hroot (D.β 0) (by rw [← hb1, mul_comm]; exact hprod)
    intro i; fin_cases i
    · exact h0'
    · have := congrArg norm hprod
      rw [norm_mul, norm_one, h0', mul_one] at this
      exact this

/-- **Hasse's theorem in the language of graphs.** For a genus-one curve datum the following are
equivalent: unitarity; nonnegativity of `deg(m − nF)` at all integers `m, n`; `t² ≤ 4q`;
nonnegativity of the defect of every graph class `graphCycle m n`. -/
theorem genusOne_hasse_tfae :
    List.TFAE
      [ ∀ i, ‖D.β i‖ = 1,
        ∀ m n : ℤ, 0 ≤ D.endDeg m n,
        D.frobTrace ^ 2 ≤ 4 * D.q,
        ∀ m n : ℝ, 0 ≤ (D.windowSurface {0, 1}).defect (D.graphCycle m n) (D.graphCycle m n) ] := by
  have hcard : Fintype.card (Fin 2) = 2 := Fintype.card_fin 2
  have hsq : D.sqrtq ^ 2 = D.q := D.sqrtq_sq
  tfae_have 2 ↔ 3 := D.endDeg_int_nonneg_iff
  tfae_have 1 → 3 := by
    intro hU
    have ht : |D.trace 1| ≤ 2 := by
      have := D.abs_trace_le_card_of_unitary hU 1
      rw [hcard] at this; exact_mod_cast this
    unfold frobTrace
    have : D.trace 1 ^ 2 ≤ 4 := by nlinarith [abs_le.mp ht]
    rw [mul_pow, hsq]
    nlinarith [D.one_lt_q]
  tfae_have 3 → 1 := by
    intro ht
    refine D.unitary_of_abs_trace_one_le_two ?_
    unfold frobTrace at ht
    rw [mul_pow, hsq] at ht
    have hq : 0 < D.q := by linarith [D.one_lt_q]
    have : D.trace 1 ^ 2 ≤ 4 := by nlinarith
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  tfae_have 3 → 4 := by
    intro ht m n
    rw [(D.defect_graphCycle_of_genusOne hcard m n).1]
    unfold endDeg
    nlinarith [sq_nonneg (m - D.frobTrace * n / 2), sq_nonneg n]
  tfae_have 4 → 2 := by
    intro h m n
    have := h m n
    rw [(D.defect_graphCycle_of_genusOne hcard m n).1] at this
    linarith
  tfae_finish

end CurveDatum

/-! ### The golden datum has an endomorphism of negative degree -/

open Real in
theorem goldenDatum_frobTrace : goldenDatum.frobTrace = 5 := by
  have hφ : goldenRatio + goldenRatio⁻¹ = Real.sqrt 5 := by
    rw [inv_goldenRatio]; simp only [goldenRatio, goldenConj]; ring
  have hs : goldenDatum.sqrtq = Real.sqrt 5 := by simp [CurveDatum.sqrtq, goldenDatum]
  unfold CurveDatum.frobTrace
  rw [goldenDatum_trace, pow_one, pow_one, hφ, hs, Real.mul_self_sqrt (by norm_num)]

/-- **`deg(2 − F) = −1` on the golden curve**: its graph class is isotropic with defect `−2`. -/
theorem goldenDatum_endDeg_two_one :
    goldenDatum.endDeg 2 1 = -1 ∧
      (goldenDatum.windowSurface {0, 1}).defect (goldenDatum.graphCycle 2 1)
        (goldenDatum.graphCycle 2 1) = -2 := by
  have hdeg : goldenDatum.endDeg 2 1 = -1 := by
    unfold CurveDatum.endDeg
    rw [goldenDatum_frobTrace]
    simp [goldenDatum]; norm_num
  refine ⟨hdeg, ?_⟩
  rw [(goldenDatum.defect_graphCycle_of_genusOne (Fintype.card_fin 2) 2 1).1, hdeg]; norm_num

/-! ### Hecke graphs of `ℤ` obey no theorem of the square -/

/-- **Genus one: the graph map is quadratic** (theorem of the square). The graph classes satisfy
`G(v + w) + G(v − w) = 2 G(v) + G(w) + G(−w) − 2 G(0)`, with `G(0) = H` the graph of `0`. -/
theorem CurveDatum.graphCycle_square {ι : Type*} [Fintype ι] (D : CurveDatum ι) (m n m' n' : ℝ) :
    D.graphCycle (m + m') (n + n') + D.graphCycle (m - m') (n - n') =
      (2 : ℝ) • D.graphCycle m n + D.graphCycle m' n' + D.graphCycle (-m') (-n') -
        (2 : ℝ) • D.graphCycle 0 0 := by
  ext
  · simp [CurveDatum.graphCycle]; ring
  · simp [CurveDatum.graphCycle, CurveDatum.endDeg]; ring
  · rename_i k
    simp only [CurveDatum.graphCycle, Prod.snd_add, Prod.snd_sub, Prod.smul_snd, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, CurveDatum.graphCoeff]
    split_ifs <;> ring

theorem CurveDatum.graphCycle_zero {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    D.graphCycle 0 0 = (D.windowSurface {0, 1}).H := by
  ext
  · simp [CurveDatum.graphCycle, windowSurface]
  · simp [CurveDatum.graphCycle, CurveDatum.endDeg, windowSurface]
  · rename_i k
    simp [CurveDatum.graphCycle, CurveDatum.graphCoeff, windowSurface]

/-- **No theorem of the square for the Hecke graphs of `ℤ`.** For `0 < b < a`, `a ≠ 2b`, and a
cycle with nonzero compact source, `T_{a+b}x + T_{a−b}x − 2T_a x − 2T_b x` is never a fibre class:
distinct Hecke scales are numerically free, so `a ↦ [T_a x]` satisfies no parallelogram law. -/
theorem heckeCorrespondence_no_square_relation {a b : ℝ} (hb : 0 < b) (hab : b < a)
    (h2 : a ≠ 2 * b) (x : ScalingCycle) (hx : x.2.2 ≠ 0) (α β : ℝ) :
    heckeCorrespondence (a + b) x + heckeCorrespondence (a - b) x -
        (2 : ℝ) • heckeCorrespondence a x - (2 : ℝ) • heckeCorrespondence b x ≠
      α • scalingSurface.H + β • scalingSurface.V := by
  intro h
  have hsrc : x.2.2.1 ≠ 0 := fun h0 => hx (Subtype.ext h0)
  set q : Fin 4 → ℝ := ![a + b, a - b, a, b] with hq_def
  have hq : ∀ i, 0 < q i := by
    intro i; fin_cases i <;> simp [q] <;> linarith
  have hinj : Function.Injective fun i => Real.log (q i) := by
    intro i j hij
    have hqij : q i = q j := Real.log_injOn_pos (hq i) (hq j) hij
    fin_cases i <;> fin_cases j <;> simp [q] at hqij ⊢ <;>
      first | rfl | (exfalso; linarith) | exact absurd (by linarith) h2
  have hli := linearIndependent_real_translate hinj x.2.2.2.2 hsrc
  have hfun : ∑ i : Fin 4, (![1, 1, -2, -2] i * Real.sqrt (q i)) •
      (fun u => x.2.2.1 (u - Real.log (q i))) = 0 := by
    funext u
    have hu := congrArg (fun y : ScalingCycle => (y.2.2 : ℝ → ℝ) u) h
    simp [heckeCorrespondence, adamsOp, scalingAction, scaleShift, scalingSurface] at hu
    simp [Fin.sum_univ_four, q]
    linarith
  have hc := (Fintype.linearIndependent_iff.mp hli) _ hfun 0
  simp [q] at hc
  exact (Real.sqrt_pos.mpr (by linarith : 0 < a + b)).ne' hc

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
