import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestHorizonBlowup

/-!
# Singular endpoint score of the primitive Euler common-test horizon

This module constructs Route R's first genuinely singular source boundary
object.  Before any divisor is selected, the normalized von-Mangoldt
prime-power law evaluates the compact-head/tail split at its moving endpoint
`t = log n`.  The resulting endpoint kernel is an exact positive Gram at
every `σ > 1`.

A centered endpoint secant is then formed on the retained prime-power label.
Its finite-`σ` augmented Gram is positive by an explicit source congruence.
The joint pole/clock limit and then the zero-secant limit produce an
unconditional augmented boundary Gram with

* test block `1 / (1 + a + star b)`,
* Fisher column `2a / (1 + a)^2`,
* Fisher energy exactly `4`.

The module also identifies the finite mismatch between compact head and
endpoint trace:

`[1 - (1 + a + star b) Rσ(1 + a + star b)] / (a + star b)`.

This memoryless seam defect vanishes at the critical source blow-up.  It is
the exact singular trace seam that a Gamma/co-Poisson-to-Ward comparison must
cross.  No Ward sign or RH conclusion is asserted here.
-/

open Complex Filter Set Matrix
open scoped Topology ComplexOrder

namespace RHTower

noncomputable section

def eulerPrimitiveBoundaryEndpointGram
    {ι : Type*} [Fintype ι] (sigma : ℝ) (a : ι → ℂ) :
    Matrix ι ι ℂ :=
  fun i j =>
    eulerPrimeCurrentComplexBlowupResponse sigma
      (1 + a i + star (a j))

def eulerPrimitiveBoundaryEndpointPrimeNode
    {ι : Type*} (sigma : ℝ) (a : ι → ℂ) (i : ι) : ℂ :=
  ((sigma : ℂ) - 1) * (a i + 1 / 2)

/-- Literal endpoint trace of the compact-head/translated-tail split.  The
prime-power label is retained; no divisor has been selected. -/
def eulerPrimitiveBoundaryEndpointFeature
    (sigma : ℝ) (a : ℂ) (n : ℕ) : ℂ :=
  eulerPrimitiveHorizonMultiplier n (((sigma : ℂ) - 1) * a)

theorem summable_eulerPrimitiveBoundaryEndpointPair
    {sigma : ℝ} (hsigma : 1 < sigma)
    {a b : ℂ} (ha : -(1 / 2 : ℝ) < a.re)
    (hb : -(1 / 2 : ℝ) < b.re) :
    Summable (fun n : ℕ =>
      (eulerPrimeCurrentProbability sigma n : ℂ) *
        eulerPrimitiveBoundaryEndpointFeature sigma a n *
        star (eulerPrimitiveBoundaryEndpointFeature sigma b n)) := by
  let wa : ℂ := ((sigma : ℂ) - 1) * a
  let wb : ℂ := ((sigma : ℂ) - 1) * b
  have hs :
      Summable
        (LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((sigma : ℂ) + wa + star wb)) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    simp [wa, wb]
    have heps : 0 < sigma - 1 := by linarith
    nlinarith
  apply
    (hs.mul_left
      (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹)).congr
  intro n
  simpa [eulerPrimitiveBoundaryEndpointFeature, wa, wb] using
    (eulerPrimitiveHorizonProbability_tailTerm_eq
      hsigma wa wb n).symm

theorem tsum_eulerPrimitiveBoundaryEndpointPair
    {sigma : ℝ} (hsigma : 1 < sigma)
    {a b : ℂ} (ha : -(1 / 2 : ℝ) < a.re)
    (hb : -(1 / 2 : ℝ) < b.re) :
    (∑' n : ℕ,
      (eulerPrimeCurrentProbability sigma n : ℂ) *
        eulerPrimitiveBoundaryEndpointFeature sigma a n *
        star (eulerPrimitiveBoundaryEndpointFeature sigma b n)) =
      eulerPrimeCurrentComplexBlowupResponse sigma
        (1 + a + star b) := by
  let wa : ℂ := ((sigma : ℂ) - 1) * a
  let wb : ℂ := ((sigma : ℂ) - 1) * b
  have hs :
      Summable
        (LSeries.term
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((sigma : ℂ) + wa + star wb)) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    simp [wa, wb]
    have heps : 0 < sigma - 1 := by linarith
    nlinarith
  rw [show
      (fun n : ℕ =>
        (eulerPrimeCurrentProbability sigma n : ℂ) *
          eulerPrimitiveBoundaryEndpointFeature sigma a n *
          star (eulerPrimitiveBoundaryEndpointFeature sigma b n)) =
        fun n : ℕ =>
          (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹) *
            LSeries.term
              (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
              ((sigma : ℂ) + wa + star wb) n by
      funext n
      simpa [eulerPrimitiveBoundaryEndpointFeature, wa, wb] using
        eulerPrimitiveHorizonProbability_tailTerm_eq hsigma wa wb n,
    hs.tsum_mul_left]
  rw [ofReal_eulerPrimeCurrentTotal_eq hsigma]
  have harg :
      (sigma : ℂ) + wa + star wb =
        1 + (((sigma : ℂ) - 1) * (1 + a + star b)) := by
    simp [wa, wb]
    ring
  have hre : 1 < ((sigma : ℂ) + wa + star wb).re := by
    simp [wa, wb]
    have heps : 0 < sigma - 1 := by linarith
    nlinarith
  change
    (infinitePrimeFlux (sigma : ℂ))⁻¹ *
        LSeries
          (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((sigma : ℂ) + wa + star wb) =
      eulerPrimeCurrentComplexBlowupResponse sigma
        (1 + a + star b)
  rw [← infinitePrimeFlux_eq_vonMangoldtLSeries hre]
  unfold eulerPrimeCurrentComplexBlowupResponse
  rw [← harg]
  ring

theorem eulerPrimitiveBoundaryEndpointGram_eq_prime
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (a : Fin N → ℂ) (ha : ∀ i, -(1 / 2 : ℝ) < (a i).re) :
    eulerPrimitiveBoundaryEndpointGram sigma a =
      (((eulerPrimeCurrentTotal sigma : ℝ) : ℂ)⁻¹) •
        vonMangoldtPrimeRightHalfPlaneGram
          (eulerPrimitiveBoundaryEndpointPrimeNode sigma a) := by
  ext i j
  rw [eulerPrimitiveBoundaryEndpointGram,
    eulerPrimeCurrentComplexBlowupResponse]
  simp only [Matrix.smul_apply, smul_eq_mul,
    vonMangoldtPrimeRightHalfPlaneGram]
  rw [ofReal_eulerPrimeCurrentTotal_eq hsigma]
  have harg :
      (1 + (((sigma : ℂ) - 1) *
          (1 + a i + star (a j)))) =
        eulerPrimitiveBoundaryEndpointPrimeNode sigma a i +
          star (eulerPrimitiveBoundaryEndpointPrimeNode sigma a j) + 1 := by
    simp [eulerPrimitiveBoundaryEndpointPrimeNode]
    ring
  have hre :
      1 <
        (eulerPrimitiveBoundaryEndpointPrimeNode sigma a i +
          star (eulerPrimitiveBoundaryEndpointPrimeNode sigma a j) + 1).re := by
    simp [eulerPrimitiveBoundaryEndpointPrimeNode]
    have heps : 0 < sigma - 1 := by linarith
    nlinarith [ha i, ha j]
  rw [harg, infinitePrimeFlux_eq_vonMangoldtLSeries hre]
  unfold vonMangoldtPrimeLaplaceChannelComplex
  ring

theorem eulerPrimitiveBoundaryEndpointGram_posSemidef_fin
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (a : Fin N → ℂ) (ha : ∀ i, -(1 / 2 : ℝ) < (a i).re) :
    (eulerPrimitiveBoundaryEndpointGram sigma a).PosSemidef := by
  rw [eulerPrimitiveBoundaryEndpointGram_eq_prime hsigma a ha]
  apply Matrix.PosSemidef.smul
  · apply vonMangoldtPrimeRightHalfPlaneGram_posSemidef
    intro i
    simp [eulerPrimitiveBoundaryEndpointPrimeNode]
    have heps : 0 < sigma - 1 := by linarith
    nlinarith [ha i]
  · apply Complex.nonneg_iff.mpr
    constructor
    · have hpos : 0 < (eulerPrimeCurrentTotal sigma)⁻¹ :=
        inv_pos.mpr (eulerPrimeCurrentTotal_pos hsigma)
      simpa using hpos.le
    · simp

theorem eulerPrimitiveBoundaryEndpointGram_posSemidef
    {ι : Type*} [Fintype ι] {sigma : ℝ} (hsigma : 1 < sigma)
    (a : ι → ℂ) (ha : ∀ i, -(1 / 2 : ℝ) < (a i).re) :
    (eulerPrimitiveBoundaryEndpointGram sigma a).PosSemidef := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let b : Fin (Fintype.card ι) → ℂ := fun k => a (e.symm k)
  have hb : ∀ k, -(1 / 2 : ℝ) < (b k).re :=
    fun k => ha (e.symm k)
  have hfin :=
    eulerPrimitiveBoundaryEndpointGram_posSemidef_fin hsigma b hb
  have heq :
      eulerPrimitiveBoundaryEndpointGram sigma a =
        (eulerPrimitiveBoundaryEndpointGram sigma b).submatrix e e := by
    ext i j
    simp [eulerPrimitiveBoundaryEndpointGram, b]
  rw [heq]
  exact hfin.submatrix e

def eulerPrimitiveBoundarySecantNodes
    {ι : Type*} (h : ℝ) (a : ι → ℂ) : ι ⊕ Fin 2 → ℂ
  | Sum.inl i => a i
  | Sum.inr k => if k = 0 then (h : ℂ) else 0

/-- Centered prime-current endpoint secant.  This is a literal function of
the retained prime-power label. -/
def eulerPrimitiveBoundarySecantScoreFeature
    (sigma h : ℝ) (n : ℕ) : ℂ :=
  (2 / (h : ℂ)) *
    (eulerPrimitiveBoundaryEndpointFeature sigma (h : ℂ) n -
      eulerPrimeCurrentComplexBlowupResponse sigma (1 + (h : ℂ)) *
        eulerPrimitiveBoundaryEndpointFeature sigma 0 n)

theorem tsum_eulerPrimitiveBoundarySecantScoreFeature_eq_zero
    {sigma h : ℝ} (hsigma : 1 < sigma) (hh : 0 < h) :
    (∑' n : ℕ,
      (eulerPrimeCurrentProbability sigma n : ℂ) *
        eulerPrimitiveBoundarySecantScoreFeature sigma h n) = 0 := by
  let R : ℂ :=
    eulerPrimeCurrentComplexBlowupResponse sigma (1 + (h : ℂ))
  have hp : Summable (fun n : ℕ =>
      (eulerPrimeCurrentProbability sigma n : ℂ)) := by
    exact Complex.ofRealCLM.summable
      (summable_eulerPrimeCurrentProbability hsigma)
  have hpair := summable_eulerPrimitiveBoundaryEndpointPair
    hsigma (a := (h : ℂ)) (b := 0) (by simp; linarith) (by norm_num)
  have hfeature0 (n : ℕ) :
      star (eulerPrimitiveBoundaryEndpointFeature sigma 0 n) = 1 := by
    simp [eulerPrimitiveBoundaryEndpointFeature,
      eulerPrimitiveHorizonMultiplier]
  have hfeature0plain (n : ℕ) :
      eulerPrimitiveBoundaryEndpointFeature sigma 0 n = 1 := by
    simp [eulerPrimitiveBoundaryEndpointFeature,
      eulerPrimitiveHorizonMultiplier]
  have hhpair : Summable (fun n : ℕ =>
      (eulerPrimeCurrentProbability sigma n : ℂ) *
        eulerPrimitiveBoundaryEndpointFeature sigma (h : ℂ) n) := by
    apply hpair.congr
    intro n
    rw [hfeature0 n, mul_one]
  have hscaled : Summable (fun n : ℕ =>
      R * (eulerPrimeCurrentProbability sigma n : ℂ)) :=
    hp.mul_left R
  rw [show
      (fun n : ℕ =>
        (eulerPrimeCurrentProbability sigma n : ℂ) *
          eulerPrimitiveBoundarySecantScoreFeature sigma h n) =
        fun n : ℕ =>
          (2 / (h : ℂ)) *
            ((eulerPrimeCurrentProbability sigma n : ℂ) *
                eulerPrimitiveBoundaryEndpointFeature sigma (h : ℂ) n -
              R * (eulerPrimeCurrentProbability sigma n : ℂ)) by
      funext n
      rw [eulerPrimitiveBoundarySecantScoreFeature,
        hfeature0plain n]
      simp only [mul_one]
      dsimp only [R]
      ring,
    tsum_mul_left,
    Summable.tsum_sub hhpair hscaled,
    tsum_mul_left]
  have hendpoint :=
    tsum_eulerPrimitiveBoundaryEndpointPair
      hsigma (a := (h : ℂ)) (b := 0)
        (by simp; linarith) (by norm_num)
  have hp_tsum :
      (∑' n : ℕ,
        (eulerPrimeCurrentProbability sigma n : ℂ)) = 1 := by
    have hmap :=
      Complex.ofRealCLM.map_tsum
        (summable_eulerPrimeCurrentProbability hsigma)
    simpa [tsum_eulerPrimeCurrentProbability hsigma] using hmap.symm
  rw [show
      (∑' n : ℕ,
        (eulerPrimeCurrentProbability sigma n : ℂ) *
          eulerPrimitiveBoundaryEndpointFeature sigma (h : ℂ) n) =
        R by
      simpa [hfeature0, R] using hendpoint,
    hp_tsum]
  ring

noncomputable def eulerPrimitiveBoundarySecantTransform
    {ι : Type*} [Fintype ι]
    (sigma h : ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Fin 2) ℂ := by
  classical
  exact fun r c =>
    match r, c with
    | Sum.inl i, Sum.inl j => if i = j then 1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr _, Sum.inr k =>
        if k = 0 then 2 / (h : ℂ)
        else -(2 / (h : ℂ)) *
          eulerPrimeCurrentComplexBlowupResponse sigma (1 + (h : ℂ))

def eulerPrimitiveBoundarySecantGram
    {ι : Type*} [Fintype ι]
    (sigma h : ℝ) (a : ι → ℂ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ :=
  eulerPrimitiveBoundarySecantTransform (ι := ι) sigma h *
    eulerPrimitiveBoundaryEndpointGram sigma
      (eulerPrimitiveBoundarySecantNodes h a) *
    (eulerPrimitiveBoundarySecantTransform (ι := ι) sigma h)ᴴ

theorem eulerPrimitiveBoundarySecantGram_posSemidef
    {ι : Type*} [Fintype ι] {sigma h : ℝ}
    (hsigma : 1 < sigma) (hh : 0 < h)
    (a : ι → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveBoundarySecantGram sigma h a).PosSemidef := by
  rw [eulerPrimitiveBoundarySecantGram]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply eulerPrimitiveBoundaryEndpointGram_posSemidef hsigma
  intro k
  rcases k with i | k
  · simp [eulerPrimitiveBoundarySecantNodes]
    linarith [ha i]
  · fin_cases k
    · simp [eulerPrimitiveBoundarySecantNodes]
      linarith
    · simp [eulerPrimitiveBoundarySecantNodes]

def eulerPrimitiveBoundaryLimitGram
    {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    Matrix ι ι ℂ :=
  fun i j => 1 / (1 + a i + star (a j))

theorem eulerPrimitiveBoundaryLimitGram_posSemidef
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, -(1 / 2 : ℝ) < (a i).re) :
    (eulerPrimitiveBoundaryLimitGram a).PosSemidef := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let b : Fin (Fintype.card ι) → ℂ := fun k => a (e.symm k)
  have hb : ∀ k, 0 < (b k + 1 / 2).re := by
    intro k
    simp [b]
    linarith [ha (e.symm k)]
  have hfin :=
    rightHalfPlaneHardyCauchyGram_posSemidef hb
  have heq :
      eulerPrimitiveBoundaryLimitGram a =
        (rightHalfPlaneHardyCauchyGram
          (fun k => b k + 1 / 2)).submatrix e e := by
    ext i j
    simp [eulerPrimitiveBoundaryLimitGram,
      rightHalfPlaneHardyCauchyGram, b]
    ring
  rw [heq]
  exact hfin.submatrix e

noncomputable def eulerPrimitiveBoundaryLimitSecantTransform
    {ι : Type*} [Fintype ι] (h : ℝ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Fin 2) ℂ := by
  classical
  exact fun r c =>
    match r, c with
    | Sum.inl i, Sum.inl j => if i = j then 1 else 0
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr _, Sum.inr k =>
        if k = 0 then 2 / (h : ℂ)
        else -(2 / (h : ℂ)) * (1 / (1 + (h : ℂ)))

def eulerPrimitiveBoundaryLimitSecantGram
    {ι : Type*} [Fintype ι]
    (h : ℝ) (a : ι → ℂ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ :=
  eulerPrimitiveBoundaryLimitSecantTransform (ι := ι) h *
    eulerPrimitiveBoundaryLimitGram
      (eulerPrimitiveBoundarySecantNodes h a) *
    (eulerPrimitiveBoundaryLimitSecantTransform (ι := ι) h)ᴴ

theorem eulerPrimitiveBoundaryLimitSecantGram_posSemidef
    {ι : Type*} [Fintype ι] {h : ℝ}
    (hh : 0 < h) (a : ι → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveBoundaryLimitSecantGram h a).PosSemidef := by
  rw [eulerPrimitiveBoundaryLimitSecantGram]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply eulerPrimitiveBoundaryLimitGram_posSemidef
  intro k
  rcases k with i | k
  · simp [eulerPrimitiveBoundarySecantNodes]
    linarith [ha i]
  · fin_cases k
    · simp [eulerPrimitiveBoundarySecantNodes]
      linarith
    · simp [eulerPrimitiveBoundarySecantNodes]

theorem tendsto_eulerPrimitiveBoundaryEndpointGram
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, -(1 / 2 : ℝ) < (a i).re) :
    Tendsto
      (fun sigma : ℝ => eulerPrimitiveBoundaryEndpointGram sigma a)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveBoundaryLimitGram a)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let q : ℂ := 1 + a i + star (a j)
  have hq : q ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    change 1 + (a i).re + (a j).re = 0 at hre
    linarith [ha i, ha j]
  simpa [eulerPrimitiveBoundaryEndpointGram,
    eulerPrimitiveBoundaryLimitGram, q] using
    tendsto_eulerPrimeCurrentComplexBlowupResponse hq

theorem tendsto_eulerPrimitiveBoundarySecantTransform
    {ι : Type*} [Fintype ι] {h : ℝ} (hh : 0 < h) :
    Tendsto
      (fun sigma : ℝ =>
        eulerPrimitiveBoundarySecantTransform (ι := ι) sigma h)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveBoundaryLimitSecantTransform
        (ι := ι) h)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  rcases i with i | _
  · rcases j with j | j
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  · rcases j with j | j
    · exact tendsto_const_nhds
    · fin_cases j
      · exact tendsto_const_nhds
      · have hq : (1 + (h : ℂ)) ≠ 0 := by
          intro hz
          have hre := congrArg Complex.re hz
          simp at hre
          linarith
        have hresponse :=
          (tendsto_eulerPrimeCurrentComplexBlowupResponse hq).const_mul
            (-(2 / (h : ℂ)))
        simpa [eulerPrimitiveBoundarySecantTransform,
          eulerPrimitiveBoundaryLimitSecantTransform] using hresponse

private theorem tendsto_boundary_matrix_mul
    {α m n p : Type*} [Fintype n] {l : Filter α}
    {A : α → Matrix m n ℂ} {B : α → Matrix n p ℂ}
    {A₀ : Matrix m n ℂ} {B₀ : Matrix n p ℂ}
    (hA : Tendsto A l (nhds A₀))
    (hB : Tendsto B l (nhds B₀)) :
    Tendsto (fun x => A x * B x) l (nhds (A₀ * B₀)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply tendsto_finsetSum
  intro k hk
  exact
    ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hA i) k).mul
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hB k) j))

private theorem tendsto_boundary_matrix_conjTranspose
    {α m n : Type*} {l : Filter α}
    {A : α → Matrix m n ℂ} {A₀ : Matrix m n ℂ}
    (hA : Tendsto A l (nhds A₀)) :
    Tendsto (fun x => (A x)ᴴ) l (nhds A₀ᴴ) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa [Matrix.conjTranspose_apply] using
    (tendsto_pi_nhds.mp
      (tendsto_pi_nhds.mp hA j) i).star

theorem tendsto_eulerPrimitiveBoundarySecantGram
    {ι : Type*} [Fintype ι] {h : ℝ} (hh : 0 < h)
    (a : ι → ℂ) (ha : ∀ i, 0 < (a i).re) :
    Tendsto
      (fun sigma : ℝ => eulerPrimitiveBoundarySecantGram sigma h a)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveBoundaryLimitSecantGram h a)) := by
  have hB :=
    tendsto_eulerPrimitiveBoundarySecantTransform (ι := ι) hh
  have hK :=
    tendsto_eulerPrimitiveBoundaryEndpointGram
      (eulerPrimitiveBoundarySecantNodes h a) (by
        intro k
        rcases k with i | k
        · simp [eulerPrimitiveBoundarySecantNodes]
          linarith [ha i]
        · fin_cases k
          · simp [eulerPrimitiveBoundarySecantNodes]
            linarith
          · simp [eulerPrimitiveBoundarySecantNodes]
            )
  have hBK := tendsto_boundary_matrix_mul hB hK
  have hBH := tendsto_boundary_matrix_conjTranspose hB
  have htotal := tendsto_boundary_matrix_mul hBK hBH
  simpa only [eulerPrimitiveBoundarySecantGram,
    eulerPrimitiveBoundaryLimitSecantGram] using htotal

theorem eulerPrimitiveBoundaryLimitSecantGram_test_test
    {ι : Type*} [Fintype ι] {h : ℝ} (a : ι → ℂ) (i j : ι) :
    eulerPrimitiveBoundaryLimitSecantGram h a
        (Sum.inl i) (Sum.inl j) =
      1 / (1 + a i + star (a j)) := by
  classical
  simp [eulerPrimitiveBoundaryLimitSecantGram,
    eulerPrimitiveBoundaryLimitSecantTransform,
    eulerPrimitiveBoundaryLimitGram, Matrix.mul_apply,
    eulerPrimitiveBoundarySecantNodes]

theorem eulerPrimitiveBoundaryLimitSecantGram_test_score
    {ι : Type*} [Fintype ι] {h : ℝ} (hh : 0 < h)
    (a : ι → ℂ) (ha : ∀ k, 0 < (a k).re) (i : ι) :
    eulerPrimitiveBoundaryLimitSecantGram h a
        (Sum.inl i) (Sum.inr ()) =
      2 * a i /
        ((1 + (h : ℂ)) * (1 + a i) * (1 + (h : ℂ) + a i)) := by
  classical
  simp [eulerPrimitiveBoundaryLimitSecantGram,
    eulerPrimitiveBoundaryLimitSecantTransform,
    eulerPrimitiveBoundaryLimitGram, Matrix.mul_apply,
    eulerPrimitiveBoundarySecantNodes]
  have hh0 : (h : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hh.ne'
  have h1h : 1 + (h : ℂ) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  have h1a : 1 + a i ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith [ha i]
  have h1ha : 1 + (h : ℂ) + a i ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith [ha i]
  have h1ah : 1 + a i + (h : ℂ) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith [ha i]
  rw [map_ofNat (starRingEnd ℂ) 2]
  field_simp [hh0, h1h, h1a, h1ha, h1ah]
  ring

theorem eulerPrimitiveBoundaryLimitSecantGram_score_score
    {ι : Type*} [Fintype ι] {h : ℝ} (hh : 0 < h)
    (a : ι → ℂ) :
    eulerPrimitiveBoundaryLimitSecantGram h a
        (Sum.inr ()) (Sum.inr ()) =
      4 / ((1 + (h : ℂ)) ^ 2 * (1 + 2 * (h : ℂ))) := by
  classical
  simp [eulerPrimitiveBoundaryLimitSecantGram,
    eulerPrimitiveBoundaryLimitSecantTransform,
    eulerPrimitiveBoundaryLimitGram, Matrix.mul_apply,
    eulerPrimitiveBoundarySecantNodes]
  have hh0 : (h : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hh.ne'
  have h1h : 1 + (h : ℂ) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  have h12h : 1 + 2 * (h : ℂ) ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp at hre
    linarith
  rw [map_ofNat (starRingEnd ℂ) 2]
  field_simp [hh0, h1h, h12h]
  ring

def eulerPrimitiveBoundaryFisherColumn
    {ι : Type*} (a : ι → ℂ) (i : ι) : ℂ :=
  2 * a i / (1 + a i) ^ 2

def eulerPrimitiveBoundaryFisherGram
    {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ
  | Sum.inl i, Sum.inl j => 1 / (1 + a i + star (a j))
  | Sum.inl i, Sum.inr _ => eulerPrimitiveBoundaryFisherColumn a i
  | Sum.inr _, Sum.inl j => star (eulerPrimitiveBoundaryFisherColumn a j)
  | Sum.inr _, Sum.inr _ => 4

theorem tendsto_eulerPrimitiveBoundaryLimitSecantGram_fisher
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, 0 < (a i).re) :
    Tendsto
      (fun h : ℝ => eulerPrimitiveBoundaryLimitSecantGram h a)
      (nhdsWithin 0 (Ioi 0))
      (nhds (eulerPrimitiveBoundaryFisherGram a)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  rcases i with i | _
  · rcases j with j | _
    · apply tendsto_const_nhds.congr'
      filter_upwards with h
      rw [eulerPrimitiveBoundaryLimitSecantGram_test_test]
      rfl
    · let f : ℝ → ℂ := fun h =>
          2 * a i /
            ((1 + (h : ℂ)) * (1 + a i) *
              (1 + (h : ℂ) + a i))
      have h1a : 1 + a i ≠ 0 := by
        intro hz
        have hre := congrArg Complex.re hz
        simp at hre
        linarith [ha i]
      have hf : ContinuousAt f 0 := by
        dsimp [f]
        have hc : ContinuousAt (fun h : ℝ => (h : ℂ)) 0 :=
          Complex.continuous_ofReal.continuousAt
        have hc1 : ContinuousAt (fun h : ℝ => 1 + (h : ℂ)) 0 :=
          continuousAt_const.add hc
        have hca :
            ContinuousAt (fun h : ℝ => 1 + (h : ℂ) + a i) 0 :=
          hc1.add continuousAt_const
        apply continuousAt_const.div
          ((hc1.mul continuousAt_const).mul hca)
        simpa using mul_ne_zero (mul_ne_zero one_ne_zero h1a) h1a
      have hlim :
          Tendsto f (nhdsWithin 0 (Ioi 0))
            (nhds (eulerPrimitiveBoundaryFisherColumn a i)) := by
        have h0 :
            f 0 = eulerPrimitiveBoundaryFisherColumn a i := by
          dsimp [f, eulerPrimitiveBoundaryFisherColumn]
          field_simp [h1a]
          ring
        rw [← h0]
        exact hf.tendsto.mono_left nhdsWithin_le_nhds
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact
        (eulerPrimitiveBoundaryLimitSecantGram_test_score
          hh a ha i).symm
  · rcases j with j | _
    · have htest :
          Tendsto
            (fun h : ℝ =>
              eulerPrimitiveBoundaryLimitSecantGram h a
                (Sum.inl j) (Sum.inr ()))
            (nhdsWithin 0 (Ioi 0))
            (nhds (eulerPrimitiveBoundaryFisherColumn a j)) := by
        let f : ℝ → ℂ := fun h =>
          2 * a j /
            ((1 + (h : ℂ)) * (1 + a j) *
              (1 + (h : ℂ) + a j))
        have h1a : 1 + a j ≠ 0 := by
          intro hz
          have hre := congrArg Complex.re hz
          simp at hre
          linarith [ha j]
        have hf : ContinuousAt f 0 := by
          dsimp [f]
          have hc : ContinuousAt (fun h : ℝ => (h : ℂ)) 0 :=
            Complex.continuous_ofReal.continuousAt
          have hc1 : ContinuousAt (fun h : ℝ => 1 + (h : ℂ)) 0 :=
            continuousAt_const.add hc
          have hca :
              ContinuousAt (fun h : ℝ => 1 + (h : ℂ) + a j) 0 :=
            hc1.add continuousAt_const
          apply continuousAt_const.div
            ((hc1.mul continuousAt_const).mul hca)
          simpa using mul_ne_zero (mul_ne_zero one_ne_zero h1a) h1a
        have hlim :
            Tendsto f (nhdsWithin 0 (Ioi 0))
              (nhds (eulerPrimitiveBoundaryFisherColumn a j)) := by
          have h0 :
              f 0 = eulerPrimitiveBoundaryFisherColumn a j := by
            dsimp [f, eulerPrimitiveBoundaryFisherColumn]
            field_simp [h1a]
            ring
          rw [← h0]
          exact hf.tendsto.mono_left nhdsWithin_le_nhds
        apply hlim.congr'
        filter_upwards [self_mem_nhdsWithin] with h hh
        exact
          (eulerPrimitiveBoundaryLimitSecantGram_test_score
            hh a ha j).symm
      have hstar := htest.star
      apply hstar.congr'
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hps :=
        eulerPrimitiveBoundaryLimitSecantGram_posSemidef
          hh a ha
      exact congrFun₂ hps.isHermitian.eq (Sum.inr ()) (Sum.inl j)
    · let f : ℝ → ℂ := fun h =>
          4 / ((1 + (h : ℂ)) ^ 2 * (1 + 2 * (h : ℂ)))
      have hf : ContinuousAt f 0 := by
        dsimp [f]
        have hc : ContinuousAt (fun h : ℝ => (h : ℂ)) 0 :=
          Complex.continuous_ofReal.continuousAt
        have hc1 : ContinuousAt (fun h : ℝ => 1 + (h : ℂ)) 0 :=
          continuousAt_const.add hc
        have hc2 : ContinuousAt (fun h : ℝ => 1 + 2 * (h : ℂ)) 0 :=
          continuousAt_const.add (continuousAt_const.mul hc)
        apply continuousAt_const.div ((hc1.pow 2).mul hc2)
        norm_num
      have hlim : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds 4) := by
        have h0 : f 0 = 4 := by norm_num [f]
        rw [← h0]
        exact hf.tendsto.mono_left nhdsWithin_le_nhds
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact
        (eulerPrimitiveBoundaryLimitSecantGram_score_score
          hh a).symm

theorem eulerPrimitiveBoundaryFisherGram_posSemidef
    {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveBoundaryFisherGram a).PosSemidef := by
  haveI :=
    nhdsWithin_Ioi_neBot (a := (0 : ℝ)) (b := (0 : ℝ)) le_rfl
  exact Matrix.PosSemidef.of_tendsto_complex
    (l := nhdsWithin 0 (Ioi 0))
    (A := fun h : ℝ => eulerPrimitiveBoundaryLimitSecantGram h a)
    (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact eulerPrimitiveBoundaryLimitSecantGram_posSemidef hh a ha)
    (tendsto_eulerPrimitiveBoundaryLimitSecantGram_fisher a ha)

/-- Failure of the finite prime-current endpoint trace to equal the compact
head.  Its vanishing is exactly the exponential memoryless seam created by
the critical source blow-up. -/
def eulerPrimitiveBoundaryMemorylessSeamDefect
    {N : ℕ} (sigma : ℝ) (a : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  eulerPrimitiveHorizonScaledHeadGram sigma a -
    eulerPrimitiveBoundaryEndpointGram sigma a

theorem eulerPrimitiveBoundaryMemorylessSeamDefect_apply
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re)
    (i j : Fin N) :
    eulerPrimitiveBoundaryMemorylessSeamDefect sigma a i j =
      (1 -
        (1 + a i + star (a j)) *
          eulerPrimeCurrentComplexBlowupResponse sigma
            (1 + a i + star (a j))) /
        (a i + star (a j)) := by
  let s : ℂ := a i + star (a j)
  have hs : s ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    change (a i).re + (a j).re = 0 at hre
    linarith [ha i, ha j]
  have hsplit :
      eulerPrimitiveHorizonScaledHeadGram sigma a i j +
          eulerPrimitiveHorizonScaledTailGram sigma a i j =
        rightHalfPlaneHardyCauchyGram a i j := by
    simpa only [Matrix.add_apply] using
      congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j)
        (eulerPrimitiveHorizonScaledHeadGram_add_tail hsigma a ha)
  have htail :=
    eulerPrimitiveHorizonScaledTailGram_apply_eq_response
      hsigma a ha i j
  rw [eulerPrimitiveBoundaryMemorylessSeamDefect,
    Matrix.sub_apply]
  rw [show
      eulerPrimitiveHorizonScaledHeadGram sigma a i j =
        rightHalfPlaneHardyCauchyGram a i j -
          eulerPrimitiveHorizonScaledTailGram sigma a i j by
      linear_combination hsplit,
    htail]
  rw [eulerPrimitiveBoundaryEndpointGram,
    rightHalfPlaneHardyCauchyGram]
  dsimp only [s] at hs
  field_simp [hs]
  ring

theorem tendsto_eulerPrimitiveBoundaryMemorylessSeamDefect
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    Tendsto
      (fun sigma : ℝ =>
        eulerPrimitiveBoundaryMemorylessSeamDefect sigma a)
      (nhdsWithin 1 (Ioi 1))
      (nhds 0) := by
  have hhead :=
    tendsto_eulerPrimitiveHorizonScaledHeadGram a ha
  have hendpoint :=
    tendsto_eulerPrimitiveBoundaryEndpointGram a
      (fun i => by linarith [ha i])
  have heq :
      eulerPrimitiveBoundaryLimitGram a =
        eulerPrimitiveHorizonBlowupHeadGram a := by
    ext i j
    simp [eulerPrimitiveBoundaryLimitGram,
      eulerPrimitiveHorizonBlowupHeadGram,
      shiftedPolarRightHalfPlaneGram, add_assoc, add_comm,
      add_left_comm]
  rw [heq] at hendpoint
  have hsub := hhead.sub hendpoint
  simpa [eulerPrimitiveBoundaryMemorylessSeamDefect] using hsub

end

end RHTower
