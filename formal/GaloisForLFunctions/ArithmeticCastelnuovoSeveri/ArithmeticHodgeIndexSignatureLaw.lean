import GaloisForLFunctions.RHTower.OddWeilGramLimit
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.HTGeometry.HaynsworthInertia
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# The arithmetic Hodge index theorem: one positive square, and the Pontryagin bound

The scaling surface of `ℤ` has as cycles the pole plane `⟨H, V⟩` and the `C²` compactly supported
tests. A test `f` meets the pole directions in its transform at `∓ i/2`,

    ⟨f, H⟩ = h_f(i/2) = ∫ f e^{−u/2},   ⟨f, V⟩ = h_f(−i/2) = ∫ f e^{u/2},

and two tests meet in the **local intersection** `⟨f, g⟩ = (prime comb) − (archimedean collar)`,
the local side of the explicit formula (`localGram_apply`): with `k = f ⋆ g̃`,

    ⟨f, g⟩ = Σ_n λ(n) n^{−1/2} (k(log n) + k(−log n)) − (1/2π) ∫ h_k(r) [Re ψ(1/4 + ir/2) − log π] dr.

The Castelnuovo–Severi defect of this pairing is Weil's functional: `polar − local = W`. The
Gram matrix of `H, V, f₁, …, f_n` is the block matrix `[[J, B], [Bᴴ, BᴴJB − W]]` with `J` the
hyperbolic plane, and Haynsworth's inertia additivity gives the **signature law**
(`posIndex_intersectionGram`)

    #positive squares(H, V, f₁, …, f_n) = 1 + #negative squares(W(f_i, f_j)).

Hence (`riemannHypothesis_iff_one_positive_square`): **RH holds iff the arithmetic intersection form
has exactly one positive square on every finite family of cycles** — the Hodge index theorem of
the scaling surface, with the pole plane as its unique positive direction. Every negative square of
Weil's form is an *excess* positive square of the intersection form. For a general prime weight `λ`
the same signature holds iff RH holds and `λ = Λ` (`one_positive_square_iff_vonMangoldt`): the
Hodge index selects the von Mangoldt weight among all weightings of the prime comb.

## The Pontryagin bound: the Hodge defect is at most the number of off-line zeros

On the zero side Weil's form is `W(F, F) = Σ_ρ m_ρ h_F(γ_ρ) conj h_F(γ̄_ρ)`, `γ_ρ = (ρ − ½)/i`. An
on-line zero contributes `m_ρ |h_F(γ_ρ)|² ≥ 0`. An off-line zero `ρ` and its reflection
`ρ' = 1 − ρ̄` have `γ_{ρ'} = γ̄_ρ`, so each of their two terms contains the factor `h_F(γ_ρ)` for
the member with `Re ρ > ½`. On the subspace of combinations killed by the finitely many
functionals `F ↦ h_F(γ_ρ)`, `Re ρ > ½`, the form is a sum of nonnegative terms, and a negative
definite subspace meets that subspace only in `0` (`negIndex_le_card_of_nonneg_on_ker`). Hence
(`negIndex_weilGram_le_offLineCount`)

    #negative squares of W on any finite family ≤ #{zeros ρ of ζ with Re ρ > ½},

and by the signature law the arithmetic intersection form has at most `1 + #{Re ρ > ½}` positive
squares (`posIndex_intersectionGram_le`): every excess positive square of the scaling surface is
paid for by a zero right of the critical line. The count is in `ℕ∞`; the statement is unconditional.
-/

open Complex Matrix
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Weil Gram matrix `W(f_i, f_j)` of a finite family of tests, for the prime weight `λ`. -/
def weilGram (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) : Matrix ι ι ℂ :=
  fun i j => RHTower.weilFullFunctional lam (EF.weilTest (f i) (f j))

/-- The hyperbolic pole plane `J = [[0, 1], [1, 0]]` (`H² = V² = 0`, `H·V = 1`). -/
def polePlane : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The pole row: the pairings `⟨H, f_j⟩ = conj h_{f_j}(i/2)`, `⟨V, f_j⟩ = conj h_{f_j}(−i/2)`. -/
def poleRow (f : ι → ℝ → ℂ) : Matrix (Fin 2) ι ℂ :=
  fun a j => if a = 0 then conj (paperFT (f j) (I / 2)) else conj (paperFT (f j) (-(I / 2)))

/-- The Gram matrix of the local intersection on tests: polar part minus Weil's form. -/
def localGram (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) : Matrix ι ι ℂ :=
  (poleRow f)ᴴ * polePlane * poleRow f - weilGram lam f

/-- The Gram matrix of the cycles `H, V, f₁, …, f_n` under the arithmetic intersection form. -/
def intersectionGram (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℂ :=
  fromBlocks polePlane (poleRow f) (poleRow f)ᴴ (localGram lam f)

theorem polePlane_isHermitian : polePlane.IsHermitian := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [polePlane]

theorem polePlane_mul_self : polePlane * polePlane = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [polePlane, Matrix.mul_apply, Fin.sum_univ_two]

theorem polePlane_inv : polePlane⁻¹ = polePlane :=
  Matrix.inv_eq_left_inv polePlane_mul_self

theorem isUnit_polePlane : IsUnit polePlane := by
  rw [Matrix.isUnit_iff_isUnit_det, polePlane, Matrix.det_fin_two_of]
  norm_num

/-- The pole plane is congruent to `diag(1/2, −1/2)`. -/
theorem polePlane_eq_congr :
    polePlane = (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
      diagonal (fun i : Fin 2 => (((![1 / 2, -1 / 2] : Fin 2 → ℝ) i : ℝ) : ℂ)) *
      !![1, 1; 1, -1] := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [polePlane, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> norm_num

theorem isUnit_hadamard : IsUnit (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
  norm_num

/-- **The pole plane has one positive square.** -/
theorem posIndex_polePlane : hermPosIndex polePlane = 1 := by
  rw [polePlane_eq_congr, posIndex_conjugate _ isUnit_hadamard, posIndex_diagonal]
  have : ({i | 0 < (![1 / 2, -1 / 2] : Fin 2 → ℝ) i} : Finset (Fin 2)) = {0} := by
    ext i; fin_cases i <;> simp
  rw [this, Finset.card_singleton]

/-- **The pole plane has one negative square.** -/
theorem negIndex_polePlane : hermNegIndex polePlane = 1 := by
  rw [polePlane_eq_congr, negIndex_conjugate _ isUnit_hadamard, negIndex_diagonal]
  have : ({i | (![1 / 2, -1 / 2] : Fin 2 → ℝ) i < 0} : Finset (Fin 2)) = {1} := by
    ext i; fin_cases i <;> norm_num
  rw [this, Finset.card_singleton]

omit [Fintype ι] [DecidableEq ι] in
/-- Weil's Gram matrix is Hermitian. -/
theorem weilGram_isHermitian (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) : (weilGram lam f).IsHermitian := by
  ext i j
  simp only [weilGram, Matrix.conjTranspose_apply, star_def]
  rw [← RHTower.WeilSpectral.weilFullFunctional_tilde, RHTower.OddResolvent.tilde_weilTest_mixed]

theorem localGram_isHermitian (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) : (localGram lam f).IsHermitian := by
  unfold localGram
  refine Matrix.IsHermitian.sub ?_ (weilGram_isHermitian lam f)
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, polePlane_isHermitian.eq, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- The polar part of the Gram is the pole term of Weil's functional:
`(BᴴJB)_{ij} = h_k(i/2) + h_k(−i/2)` for `k = f_i ⋆ f̃_j`. -/
theorem polarGram_apply (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (i j : ι) :
    ((poleRow f)ᴴ * polePlane * poleRow f) i j
      = paperFT (EF.weilTest (f i) (f j)) (I / 2) + paperFT (EF.weilTest (f i) (f j)) (-(I / 2)) := by
  have hc1 : conj (I / 2) = -(I / 2) := by rw [map_div₀, Complex.conj_I, map_ofNat]; ring
  have hc2 : conj (-(I / 2)) = I / 2 := by rw [map_neg, hc1, neg_neg]
  rw [EF.paperFT_weilTest (hf i) (hf j) (hfc i) (hfc j),
    EF.paperFT_weilTest (hf i) (hf j) (hfc i) (hfc j), hc1, hc2]
  simp [Matrix.mul_apply, Fin.sum_univ_two, poleRow, polePlane, Matrix.conjTranspose_apply]
  ring

/-- **The local intersection is the local side of the explicit formula**: prime comb minus
archimedean collar, with the pole cancelled. -/
theorem localGram_apply (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) (hf : ∀ i, Continuous (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (i j : ι) :
    localGram lam f i j
      = (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (EF.weilTest (f i) (f j) (Real.log n) + EF.weilTest (f i) (f j) (-Real.log n)))
        - (1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ, paperFT (EF.weilTest (f i) (f j)) r * (EF.gammaBracket r : ℂ) := by
  rw [localGram, Matrix.sub_apply, polarGram_apply f hf hfc, weilGram,
    RHTower.weilFullFunctional]
  have : -(I / 2) = -I / 2 := by ring
  rw [this]
  ring

/-- **The signature law.** The cycles `H, V, f₁, …, f_n` have exactly `1 + κ` positive squares,
`κ` the number of negative squares of Weil's form on `f₁, …, f_n`. -/
theorem posIndex_intersectionGram (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) :
    hermPosIndex (intersectionGram lam f) = 1 + hermNegIndex (weilGram lam f) := by
  rw [intersectionGram, haynsworth_posIndex isUnit_polePlane polePlane_isHermitian (poleRow f)
    (localGram_isHermitian lam f), posIndex_polePlane, polePlane_inv, localGram, sub_sub_cancel_left,
    hermNegIndex]

/-- **Dual signature law**: `1 + #positive squares of W` negative squares. -/
theorem negIndex_intersectionGram (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) :
    hermNegIndex (intersectionGram lam f) = 1 + hermPosIndex (weilGram lam f) := by
  rw [intersectionGram, haynsworth_negIndex isUnit_polePlane polePlane_isHermitian (poleRow f)
    (localGram_isHermitian lam f), negIndex_polePlane, polePlane_inv, localGram, sub_sub_cancel_left,
    hermNegIndex, neg_neg]

omit [DecidableEq ι] in
/-- The quadratic form of Weil's Gram matrix is Weil's functional of the combined test. -/
theorem hermQuad_weilGram (lam : ℕ → ℝ) (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) (x : ι → ℂ) :
    hermQuad (weilGram lam f) x = (RHTower.weilFullFunctional lam
      (EF.weilTest (∑ i, conj (x i) • f i) (∑ i, conj (x i) • f i))).re := by
  rw [RHTower.OddResolvent.weilFullFunctional_finset_gram lam Finset.univ (fun i => conj (x i)) f
    hf hfc, hermQuad]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, weilGram, conj_conj,
    Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Weil positivity is the Hodge index**: `W ≥ 0` on all tests iff every finite family of cycles
has exactly one positive square. -/
theorem weilPositiveFull_iff_one_positive_square (lam : ℕ → ℝ) :
    RHTower.WeilPositiveFull lam ↔ ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) → hermPosIndex (intersectionGram lam f) = 1 := by
  constructor
  · intro hW n f hf hfc
    rw [posIndex_intersectionGram, negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_]
    rw [hermQuad_weilGram lam f hf hfc]
    exact hW _ (contDiff_sum_smul f hf _) (hasCompactSupport_sum_smul f hfc _)
  · intro h g hg hgc
    have h1 := h 1 (fun _ => g) (fun _ => hg) (fun _ => hgc)
    rw [posIndex_intersectionGram] at h1
    have h0 : hermNegIndex (weilGram lam fun _ : Fin 1 => g) = 0 := by omega
    have hq := hermQuad_nonneg_of_negIndex_eq_zero h0 (fun _ => 1)
    rw [hermQuad_weilGram lam _ (fun _ => hg) (fun _ => hgc)] at hq
    simpa using hq

/-- **The arithmetic Hodge index theorem is the Riemann hypothesis.** RH holds iff the arithmetic
intersection form of `ζ` has exactly one positive square on every finite family of cycles. -/
theorem riemannHypothesis_iff_one_positive_square :
    RiemannHypothesis ↔ ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) →
        hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1 :=
  RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt.trans
    (weilPositiveFull_iff_one_positive_square _)

/-- **Hodge index selects `Λ`.** A prime weight `λ` gives an intersection form with one positive
square on every family iff RH holds and `λ = Λ` on `n ≥ 2`. -/
theorem one_positive_square_iff_vonMangoldt (lam : ℕ → ℝ) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) →
      (∀ i, HasCompactSupport (f i)) → hermPosIndex (intersectionGram lam f) = 1) ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  (weilPositiveFull_iff_one_positive_square lam).symm.trans
    RHTower.WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt

/-! ### The Pontryagin bound -/

/-- **The Pontryagin bound for `ζ`.** Weil's form has at most as many negative squares on any
finite family of `C²` compactly supported tests as `ζ` has zeros right of the critical line. -/
theorem negIndex_weilGram_le_offLineCount (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℕ∞)
      ≤ {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  set R := {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}
  rcases R.finite_or_infinite with hR | hR
  · haveI := hR.fintype
    rw [hR.encard_eq_coe_toFinset_card, Set.Finite.card_toFinset]
    refine ENat.coe_le_coe.mpr (negIndex_le_card_of_nonneg_on_ker _
      (fun ρ : R => evalFunctional f (gammaOf ρ)) fun x hx => ?_)
    set F := ∑ i, conj (x i) • f i
    have hFv : ∀ ρ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ.re → paperFT F (gammaOf ρ) = 0 := by
      intro ρ hρ hre
      have := hx ⟨ρ, hρ, hre⟩
      rw [evalFunctional_eq f (fun i => (hf i).continuous) hfc] at this
      simpa using this
    rw [hermQuad_weilGram _ f hf hfc x,
      ← RHTower.zeta_W_eq_weilFullFunctional_mixed (contDiff_sum_smul f hf _)
        (hasCompactSupport_sum_smul f hfc _) (contDiff_sum_smul f hf _)
        (hasCompactSupport_sum_smul f hfc _), ZeroConfig.W,
      Complex.re_tsum (RHTower.zeta_Wsummand_summable (contDiff_sum_smul f hf _)
        (contDiff_sum_smul f hf _) (hasCompactSupport_sum_smul f hfc _)
        (hasCompactSupport_sum_smul f hfc _))]
    exact tsum_nonneg fun ρ => re_Wsummand_nonneg zetaZeroConfig hFv ρ
  · rw [hR.encard_eq]; exact le_top

/-- **The Hodge defect of the scaling surface.** The arithmetic intersection form has at most
`1 + #{zeros with Re ρ > ½}` positive squares on any finite family of cycles. -/
theorem posIndex_intersectionGram_le (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℕ∞)
      ≤ 1 + {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}.encard := by
  rw [posIndex_intersectionGram, Nat.cast_add, Nat.cast_one]
  exact add_le_add le_rfl (negIndex_weilGram_le_offLineCount f hf hfc)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
