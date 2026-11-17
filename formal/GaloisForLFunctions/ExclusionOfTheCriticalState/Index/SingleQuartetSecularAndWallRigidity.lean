import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheOnLineResolventOfAFiniteLayer
import GaloisForLFunctions.ExclusionOfTheCriticalState.Energy.TheChargeHyperplaneHasItsOwnCriticalRatio
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheProfileBeyondTheWallInPrimeForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheAveragedStateIsTheSumOfItsZeroModes
import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.TheOffLineLayersOfTheBeurlingAndTwinModelsCarryCriticalStates
import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ANonRealPairAloneOnTopOfATwoSidedEdit
import GaloisForLFunctions.RHTower.FiniteOffLineConverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix

/-!
# Single off-line quartet secular equation, two-rung rigidity, wall laws, and prime continuation

This module establishes the unconditional structure of a hypothetical single off-line zero quartet
`Q(ρ₀) = {ρ₀, conj ρ₀, 1 - ρ₀, 1 - conj ρ₀}` (`1/2 < Re ρ₀ < 1`) of `ζ`, together with its direct-sum
coupling to individual beyond-the-wall prime continuation:

1. **Single-quartet geometry and four-term off-line Parseval block
   (`HasSingleOffLineQuartet`, `sum_offLineCopyFinset_of_singleQuartet`,
   `bareMixedEnergy_singleQuartet`).**
   By functional-equation reflection and Schwarz conjugation of `ξ`, all four points of `Q(ρ₀)` are
   distinct non-real strip zeros with `4 < |Im ρ₀|` and common divisor multiplicity `m ≥ 1`. On the
   entire half-line energy domain, Weil's bare mixed form splits into the Hermitian on-line pairing
   plus the `4 × 4` off-line block `2 m · v_Fᵀ J₄ v_G` at `(z₊, z₋) = (ρ₀ - ½, ½ - conj ρ₀)`.

2. **Exact `4 × 4` Birman–Schwinger secular equation and first-root characterization of `a(W₀)`
   (`quartetSecularMatrix`, `nullVector_iff_secularKernel`,
   `exists_confinedNullVector_iff_quartetSecularDet_eq_zero`,
   `quartetSecularDet_pos_below_threshold`).**
   Evaluating the four real on-line mode resolvents at `(z₊, z₋)` forms the `4 × 4` symmetric on-line
   resolvent matrix `G_on(a)`. Confined null vectors `(R, F)` (`R > 0`, `a = a(R)`) stand in a.e.
   bijection with nonzero kernel vectors of `I₄ + 2 m G_on(a(R)) J₄`; hence `R` carries a confined
   null vector iff `det(I₄ + 2 m G_on(a(R)) J₄) = 0`, and `det > 0` for all `0 < R < W₀`.

3. **Complete two-rung spectral ladder, 1D simplicity, Cauchy interlacing, and Bessel trace bound
   (`singleQuartet_complete_twoRung_ladder`, `singleQuartet_alias_sum_le`).**
   Under `HasSingleOffLineQuartet ρ₀`, the confined form has **exact** null-ratio spectrum `{W₀, R₂}`
   (`0 < W₀ < R₂`), both null spaces are 1-dimensional up to a.e. equality, `Q_R` is negative
   definite on `ℝ F₀ ⊕ ℝ F₁` for all `R > R₂`, the charge-hyperplane positivity threshold `R₁`
   interlaces `0 < W₀ < R₁ ≤ R₂`, and Bessel's inequality in `L²((-∞, 0), e^{-8u})` bounds the joint
   trace by `a(W₀) + a(R₂) ≤ 2 m / √(16 - (Re ρ₀ - ½)²)`.

4. **Direct-sum synthesis with beyond-the-wall prime continuation
   (`singleQuartet_hasBeyondTheWallPrimeContinuation_iff`,
   `singleQuartet_directSum_primeContinuation`,
   `singleQuartet_exists_poleNeutral_no_primeHeadContinuation`).**
   Under `HasSingleOffLineQuartet ρ₀`, a domain profile `G` satisfies `HasBeyondTheWallPrimeContinuation G`
   iff `L G(½ - conj ρ₀) = 0`. Evaluation at `½ - conj ρ₀` is an `ℝ`-linear isomorphism on `ℝ F₀ ⊕ ℝ F₁`,
   splitting the energy domain into `(ℝ F₀ ⊕ ℝ F₁) ⊕ {G : HasBeyondTheWallPrimeContinuation G}`, where
   `B < 0` on `(ℝ F₀ ⊕ ℝ F₁) \ {0}` and `B ≥ 0` on the continuation hyperplane, and producing a
   nonzero pole-neutral ladder state whose bare `primeHead` fails holomorphic continuation to `Re p < 0`.

5. **Two-rung wall laws, prime/PNT form of `F₀⁺, F₁⁺`, two-mode `averagedState`, and exact single-wave
   Chebyshev equivalence (`singleQuartet_twoRung_wall_and_primeForm`,
   `singleQuartet_averagedState_singleConjugatePair`,
   `hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave`).**
   Both rungs satisfy the diagonal and cross-rung wall laws and the a.e. prime/PNT representations of
   `F₀⁺, F₁⁺`; `averagedState F₀` equals `2 m Re(c₊ e^{(z₊ - 8)t}) + O(e^{-8t})`; and for any strip
   zero `ρ₀` of `ζ` with `1/2 < Re ρ₀`, `HasSingleOffLineQuartet ρ₀` holds **iff**
   `ψ(x) - x = -2 m Re(x^{ρ₀}/ρ₀) + O(√x log² x)`.

6. **Global `E-Q1` equivalence and single-quartet model separation (`eq1_global_and_profile_synthesis`,
   `singleQuartet_realized_in_models`).**
-/

noncomputable section

open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis HTGeometry _root_.RHTower

/-! ### 1. Single-quartet geometry, multiplicity invariance, and four-term off-line Parseval -/

/-- The functional-equation and conjugation quartet `{ρ, conj ρ, 1 - ρ, 1 - conj ρ}` in `ℂ`. -/
def zeroQuartetSet (ρ : ℂ) : Set ℂ :=
  {ρ, conj ρ, 1 - ρ, 1 - conj ρ}

/-- `ζ` has a single off-line quartet generated by `ρ₀`: `1/2 < Re ρ₀`, `ρ₀` is a strip zero of `ζ`,
and the off-line strip zeros of `ζ` are precisely `zeroQuartetSet ρ₀`. -/
def HasSingleOffLineQuartet (ρ₀ : ℂ) : Prop :=
  1 / 2 < ρ₀.re ∧ ρ₀ ∈ zetaZeroConfig.carrier ∧
    {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} = zeroQuartetSet ρ₀

/-- Exact divisor multiplicity of a complex point in the global `ξ` divisor. -/
def quartetCopyMult (ρ : ℂ) : ℕ :=
  ((MeromorphicOn.divisor xi Set.univ) ρ).toNat

theorem quartetCopyMult_conj (ρ : ℂ) : quartetCopyMult (conj ρ) = quartetCopyMult ρ := by
  unfold quartetCopyMult
  rw [xi_divisor_conj]

theorem quartetCopyMult_one_sub (ρ : ℂ) : quartetCopyMult (1 - ρ) = quartetCopyMult ρ := by
  unfold quartetCopyMult
  rw [xi_divisor_one_sub]

theorem quartetCopyMult_one_sub_conj (ρ : ℂ) :
    quartetCopyMult (1 - conj ρ) = quartetCopyMult ρ := by
  rw [quartetCopyMult_one_sub, quartetCopyMult_conj]

theorem HasSingleOffLineQuartet.re_lt_one {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    ρ₀.re < 1 :=
  hq.2.1.2.2

theorem HasSingleOffLineQuartet.xi_eq_zero {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    xi ρ₀ = 0 := by
  obtain ⟨hζ, h0, h1⟩ := hq.2.1
  have hne1 : ρ₀ ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  exact (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mpr hζ

theorem HasSingleOffLineQuartet.four_lt_abs_im {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    4 < |ρ₀.im| := by
  obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hq.xi_eq_zero
  have h := four_lt_abs_zeroOrdinate q
  rwa [zeroOrdinate, hq_eq] at h

theorem HasSingleOffLineQuartet.im_ne_zero {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    ρ₀.im ≠ 0 := by
  intro h0
  have h := hq.four_lt_abs_im
  rw [h0, abs_zero] at h
  linarith

theorem HasSingleOffLineQuartet.not_riemannHypothesis {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨hζ, h0, h1⟩ := hq.2.1
  have hhalf : ρ₀.re = 1 / 2 := by
    refine hRH ρ₀ hζ ?_ (fun heq1 => by rw [heq1] at h1; norm_num at h1)
    rintro ⟨n, hn⟩
    rw [hn] at h0; simp at h0
    linarith [Nat.cast_nonneg (α := ℝ) n]
  linarith [hq.1]

theorem HasSingleOffLineQuartet.quartetCopyMult_pos {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    0 < quartetCopyMult ρ₀ := by
  obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hq.xi_eq_zero
  have hpos := xi_divisor_pos_on_support q.1
  unfold quartetCopyMult
  rw [← hq_eq]
  omega

private theorem xiZeroCopy_mem_zetaZeroConfig (q : XiZeroCopy) :
    (q.1 : ℂ) ∈ zetaZeroConfig.carrier := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hne1 : (q.1 : ℂ) ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  have hζ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mp
    (xi_eq_zero_of_mem_divisor_support q.1)
  exact ⟨hζ, h0, h1⟩

private theorem finite_xiZeroCopy_fiber (z : ℂ) :
    Set.Finite {q : XiZeroCopy | (q.1 : ℂ) = z} := by
  by_cases hz : z ∈ (MeromorphicOn.divisor xi Set.univ).support
  · let ρ_s : XiDivisorSupport := ⟨z, hz⟩
    refine ((Set.finite_univ :
      Set.Finite (Set.univ : Set (Fin (((MeromorphicOn.divisor xi Set.univ) z).toNat)))).image
      (fun k => (⟨ρ_s, k⟩ : XiZeroCopy))).subset fun q hq => ?_
    have hρ : q.1 = ρ_s := Subtype.ext hq
    cases q with | mk ρ k =>
    dsimp only at hρ
    subst hρ
    exact ⟨k, Set.mem_univ k, rfl⟩
  · have hemp : {q : XiZeroCopy | (q.1 : ℂ) = z} = ∅ :=
      Set.eq_empty_of_forall_notMem fun q hq => hz (hq ▸ q.1.2)
    rw [hemp]
    exact Set.finite_empty

theorem HasSingleOffLineQuartet.finiteOffLine_copies {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    Set.Finite {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1 / 2} := by
  refine (((finite_xiZeroCopy_fiber ρ₀).union (finite_xiZeroCopy_fiber (conj ρ₀))).union
    ((finite_xiZeroCopy_fiber (1 - ρ₀)).union (finite_xiZeroCopy_fiber (1 - conj ρ₀)))).subset
    fun q hne => ?_
  have hmem : (q.1 : ℂ) ∈ {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} :=
    ⟨xiZeroCopy_mem_zetaZeroConfig q, hne⟩
  rw [hq.2.2] at hmem
  simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h1 | h2 | h3 | h4
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h2)
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr h4)

theorem HasSingleOffLineQuartet.finiteOffLine {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    BacklundConverse.FiniteOffLine := by
  unfold BacklundConverse.FiniteOffLine
  refine hq.finiteOffLine_copies.subset fun q hq_im => ?_
  have him : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  intro hre
  apply hq_im
  rw [him, hre, sub_self]

private theorem quartet_points_pairwise_ne {ρ₀ : ℂ} (hre : 1 / 2 < ρ₀.re) (him : ρ₀.im ≠ 0) :
    ρ₀ ≠ conj ρ₀ ∧ ρ₀ ≠ 1 - ρ₀ ∧ ρ₀ ≠ 1 - conj ρ₀ ∧
      conj ρ₀ ≠ 1 - ρ₀ ∧ conj ρ₀ ≠ 1 - conj ρ₀ ∧ 1 - ρ₀ ≠ 1 - conj ρ₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply him; have := congrArg Complex.im h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; apply him; have := congrArg Complex.im h; simp at this; linarith

private theorem xi_quartet_eq_zero {ρ₀ : ℂ} (hxi : xi ρ₀ = 0) :
    xi (conj ρ₀) = 0 ∧ xi (1 - ρ₀) = 0 ∧ xi (1 - conj ρ₀) = 0 := by
  have hc : xi (conj ρ₀) = 0 := by rw [xi_conj, hxi, map_zero]
  have hr : xi (1 - ρ₀) = 0 := by rw [xi_one_sub, hxi]
  have hrc : xi (1 - conj ρ₀) = 0 := by rw [xi_one_sub, hc]
  exact ⟨hc, hr, hrc⟩

theorem rightCentredZeros_eq_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    rightCentredZeros hq.finiteOffLine = {ρ₀ - 1 / 2, conj ρ₀ - 1 / 2} := by
  ext z
  rw [mem_rightCentredZeros_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hzre, hxi⟩
    obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hmem : (1 : ℂ) / 2 + z ∈ {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} := by
      rw [← hq_eq]
      refine ⟨xiZeroCopy_mem_zetaZeroConfig q, ?_⟩
      rw [hq_eq]; simp; linarith
    rw [hq.2.2] at hmem
    rcases hmem with h1 | h2 | h3 | h4
    · left; linear_combination h1
    · right; linear_combination h2
    · exfalso; have := congrArg Complex.re h3; simp at this; linarith [hq.1]
    · exfalso; have := congrArg Complex.re h4; simp at this; linarith [hq.1]
  · rintro (rfl | rfl)
    · refine ⟨by simp; linarith [hq.1], ?_⟩
      rw [show (1 : ℂ) / 2 + (ρ₀ - 1 / 2) = ρ₀ by ring]
      exact hq.xi_eq_zero
    · refine ⟨by simp; linarith [hq.1], ?_⟩
      rw [show (1 : ℂ) / 2 + (conj ρ₀ - 1 / 2) = conj ρ₀ by ring]
      exact (xi_quartet_eq_zero hq.xi_eq_zero).1

theorem card_rightCentredZeros_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    (rightCentredZeros hq.finiteOffLine).card = 2 := by
  rw [rightCentredZeros_eq_singleQuartet hq, Finset.card_pair]
  intro h
  exact (quartet_points_pairwise_ne hq.1 hq.im_ne_zero).1 (by linear_combination h)

theorem leftCentredZeros_eq_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    leftCentredZeros hq.finiteOffLine = {1 / 2 - ρ₀, 1 / 2 - conj ρ₀} := by
  ext z
  rw [mem_leftCentredZeros_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hzre, hxi⟩
    obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have hmem : (1 : ℂ) / 2 + z ∈ {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} := by
      rw [← hq_eq]
      refine ⟨xiZeroCopy_mem_zetaZeroConfig q, ?_⟩
      rw [hq_eq]; simp; linarith
    rw [hq.2.2] at hmem
    simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h2 | h3 | h4
    · exfalso; have := congrArg Complex.re h1; simp at this; linarith [hq.1]
    · exfalso; have := congrArg Complex.re h2; simp at this; linarith [hq.1]
    · left; linear_combination h3
    · right; linear_combination h4
  · rintro (rfl | rfl)
    · refine ⟨by simp; linarith [hq.1], ?_⟩
      rw [show (1 : ℂ) / 2 + (1 / 2 - ρ₀) = 1 - ρ₀ by ring]
      exact (xi_quartet_eq_zero hq.xi_eq_zero).2.1
    · refine ⟨by simp; linarith [hq.1], ?_⟩
      rw [show (1 : ℂ) / 2 + (1 / 2 - conj ρ₀) = 1 - conj ρ₀ by ring]
      exact (xi_quartet_eq_zero hq.xi_eq_zero).2.2

private theorem card_offLineFiber_eq_quartetCopyMult {hfin : BacklundConverse.FiniteOffLine}
    {z : ℂ} (hxi : xi z = 0) (hz_re : z.re ≠ 1 / 2) :
    ((offLineCopyFinset hfin).filter fun q => (q.1 : ℂ) = z).card = quartetCopyMult z := by
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  have hsupp : z ∈ (MeromorphicOn.divisor xi Set.univ).support := by
    rw [← hq₀]; exact q₀.1.2
  let ρ_s : XiDivisorSupport := ⟨z, hsupp⟩
  symm
  rw [quartetCopyMult, ← Fintype.card_fin (((MeromorphicOn.divisor xi Set.univ) z).toNat),
    ← Finset.card_univ]
  refine Finset.card_bij (fun (k : Fin (((MeromorphicOn.divisor xi Set.univ) z).toNat)) _ =>
      (⟨ρ_s, k⟩ : XiZeroCopy))
    (fun k _ => ?_)
    (fun a _ b _ h => by
      have h2 := (Sigma.mk.inj_iff.mp h).2
      exact eq_of_heq h2)
    (fun q hq => ?_)
  · refine Finset.mem_filter.mpr ⟨mem_offLineCopyFinset.mpr ?_, rfl⟩
    change (z - 1 / 2).re ≠ 0
    rw [Complex.sub_re]
    norm_num
    intro h0; apply hz_re; linarith
  · obtain ⟨hq_off, hq_val⟩ := Finset.mem_filter.mp hq
    have hρ_eq : q.1 = ρ_s := Subtype.ext hq_val
    cases q with | mk ρ k =>
    dsimp only at hρ_eq
    subst hρ_eq
    exact ⟨k, Finset.mem_univ k, rfl⟩

/-- **Master single-quartet off-line sum formula.** Under `HasSingleOffLineQuartet ρ₀`, summing any
pointwise function `f (q.1 : ℂ)` over `offLineCopyFinset` evaluates to `m` times the sum over the
four points `{ρ₀, conj ρ₀, 1 - ρ₀, 1 - conj ρ₀}`. -/
theorem sum_offLineCopyFinset_of_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    (f : ℂ → ℂ) :
    ∑ q ∈ offLineCopyFinset hq.finiteOffLine, f (q.1 : ℂ) =
      (quartetCopyMult ρ₀ : ℂ) *
        (f ρ₀ + f (conj ρ₀) + f (1 - ρ₀) + f (1 - conj ρ₀)) := by
  classical
  set S := offLineCopyFinset hq.finiteOffLine
  obtain ⟨hne12, hne13, hne14, hne23, hne24, hne34⟩ :=
    quartet_points_pairwise_ne hq.1 hq.im_ne_zero
  let Q : Finset ℂ := {ρ₀, conj ρ₀, 1 - ρ₀, 1 - conj ρ₀}
  have hmaps : ∀ q ∈ S, (q.1 : ℂ) ∈ Q := by
    intro q hqS
    have hne_half : (q.1 : ℂ).re ≠ 1 / 2 := by
      have hne0 := mem_offLineCopyFinset.mp hqS
      rw [centredZero, Complex.sub_re] at hne0
      norm_num at hne0
      intro h; apply hne0; linarith
    have hmem : (q.1 : ℂ) ∈ {ρ ∈ zetaZeroConfig.carrier | ρ.re ≠ 1 / 2} :=
      ⟨xiZeroCopy_mem_zetaZeroConfig q, hne_half⟩
    rw [hq.2.2] at hmem
    simpa [Q, zeroQuartetSet] using hmem
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hsum_Q : ∀ g : ℂ → ℂ, ∑ z ∈ Q, g z =
      g ρ₀ + g (conj ρ₀) + g (1 - ρ₀) + g (1 - conj ρ₀) := by
    intro g
    dsimp [Q]
    rw [Finset.sum_insert (by simp [hne12, hne13, hne14]),
      Finset.sum_insert (by simp [hne23, hne24]),
      Finset.sum_insert (by simp [hne34]),
      Finset.sum_singleton]
    ring
  rw [hsum_Q]
  have hfib : ∀ {z : ℂ}, xi z = 0 → z.re ≠ 1 / 2 → quartetCopyMult z = quartetCopyMult ρ₀ →
      (∑ q ∈ S.filter (fun q => (q.1 : ℂ) = z), f (q.1 : ℂ)) =
        (quartetCopyMult ρ₀ : ℂ) * f z := by
    intro z hxi hre hm
    have hc : ∀ q ∈ S.filter (fun q => (q.1 : ℂ) = z), f (q.1 : ℂ) = f z :=
      fun q hq_f => congrArg f (Finset.mem_filter.mp hq_f).2
    rw [Finset.sum_congr rfl hc, Finset.sum_const,
      card_offLineFiber_eq_quartetCopyMult hxi hre, hm, nsmul_eq_mul]
  obtain ⟨hxi_c, hxi_r, hxi_rc⟩ := xi_quartet_eq_zero hq.xi_eq_zero
  rw [hfib hq.xi_eq_zero (by linarith [hq.1]) rfl,
    hfib hxi_c (by simp; linarith [hq.1]) (quartetCopyMult_conj ρ₀),
    hfib hxi_r (by simp; linarith [hq.1]) (quartetCopyMult_one_sub ρ₀),
    hfib hxi_rc (by simp; linarith [hq.1]) (quartetCopyMult_one_sub_conj ρ₀)]
  ring

/-- Four-component real evaluation vector
`((L F(ρ₀ - ½)).re, (L F(ρ₀ - ½)).im, (L F(½ - conj ρ₀)).re, (L F(½ - conj ρ₀)).im)`. -/
def quartetEvalVec (ρ₀ : ℂ) (F : ℝ → ℝ) : Fin 4 → ℝ :=
  ![(negativeHalfLineLaplace (cx F) (ρ₀ - 1 / 2)).re,
    (negativeHalfLineLaplace (cx F) (ρ₀ - 1 / 2)).im,
    (negativeHalfLineLaplace (cx F) (1 / 2 - conj ρ₀)).re,
    (negativeHalfLineLaplace (cx F) (1 / 2 - conj ρ₀)).im]

/-- Block-swap matrix `J₄ = [0, I₂; I₂, 0]` coupling `(ρ₀ - ½)` and `(½ - conj ρ₀)`. -/
def quartetSwapMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, 1, 0, 0]

theorem quartetSwapMatrix_mulVec (v : Fin 4 → ℝ) :
    quartetSwapMatrix *ᵥ v = ![v 2, v 3, v 0, v 1] := by
  ext i
  fin_cases i <;> simp [quartetSwapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem quartetSwapMatrix_mul_self :
    quartetSwapMatrix * quartetSwapMatrix = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quartetSwapMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem dotProduct_quartetSwapMatrix_symm (u v : Fin 4 → ℝ) :
    dotProduct (quartetSwapMatrix *ᵥ u) v = dotProduct u (quartetSwapMatrix *ᵥ v) := by
  rw [quartetSwapMatrix_mulVec, quartetSwapMatrix_mulVec]
  simp only [dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- **Four-term off-line Parseval block on the energy domain.** Under `HasSingleOffLineQuartet ρ₀`,
for all `F, G` in the energy domain, Weil's bare mixed form equals the Hermitian on-line pairing plus
`2 m · v_Fᵀ J₄ v_G`. -/
theorem bareMixedEnergy_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    bareMixedEnergy F G = onLineMixed F G +
      2 * (quartetCopyMult ρ₀ : ℝ) *
        dotProduct (quartetEvalVec ρ₀ F) (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ G) := by
  rw [bareMixedEnergy_eq_onLineMixed_add_re_offLine hF hG hq.finiteOffLine]
  congr 1
  have hsum : (∑ q ∈ offLineCopyFinset hq.finiteOffLine,
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q)) =
      ∑ q ∈ offLineCopyFinset hq.finiteOffLine,
        (fun ρ : ℂ => negativeHalfLineLaplace (cx F) (ρ - 1 / 2) *
          negativeHalfLineLaplace (cx G) (1 / 2 - ρ)) (q.1 : ℂ) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    dsimp only
    rw [centredZero]
    congr 2
    ring
  rw [hsum, sum_offLineCopyFinset_of_singleQuartet hq
    (fun ρ : ℂ => negativeHalfLineLaplace (cx F) (ρ - 1 / 2) *
      negativeHalfLineLaplace (cx G) (1 / 2 - ρ))]
  set zPos : ℂ := ρ₀ - 1 / 2
  set zNeg : ℂ := 1 / 2 - conj ρ₀
  have hc₁ : conj ρ₀ - 1 / 2 = conj zPos := by
    dsimp [zPos]; apply Complex.ext <;> simp
  have hz1 : (1 : ℂ) / 2 - ρ₀ = conj zNeg := by
    dsimp [zNeg]; apply Complex.ext <;> simp
  have hz2 : (1 : ℂ) - ρ₀ - 1 / 2 = conj zNeg := by
    dsimp [zNeg]; (apply Complex.ext <;> simp); ring
  have hz3 : (1 : ℂ) / 2 - (1 - ρ₀) = zPos := by dsimp [zPos]; ring
  have hz4 : (1 : ℂ) - conj ρ₀ - 1 / 2 = zNeg := by dsimp [zNeg]; ring
  have hz5 : (1 : ℂ) / 2 - (1 - conj ρ₀) = conj zPos := by
    dsimp [zPos]; (apply Complex.ext <;> simp); ring
  have hreal_F : ∀ w : ℂ, negativeHalfLineLaplace (cx F) (conj w) =
      conj (negativeHalfLineLaplace (cx F) w) := fun w =>
    negativeHalfLineLaplace_real_conj F w
  have hreal_G : ∀ w : ℂ, negativeHalfLineLaplace (cx G) (conj w) =
      conj (negativeHalfLineLaplace (cx G) w) := fun w =>
    negativeHalfLineLaplace_real_conj G w
  have hdot : dotProduct (quartetEvalVec ρ₀ F) (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ G) =
      (negativeHalfLineLaplace (cx F) zPos).re * (negativeHalfLineLaplace (cx G) zNeg).re +
        (negativeHalfLineLaplace (cx F) zPos).im * (negativeHalfLineLaplace (cx G) zNeg).im +
        (negativeHalfLineLaplace (cx F) zNeg).re * (negativeHalfLineLaplace (cx G) zPos).re +
        (negativeHalfLineLaplace (cx F) zNeg).im * (negativeHalfLineLaplace (cx G) zPos).im := by
    rw [quartetSwapMatrix_mulVec]
    simp only [quartetEvalVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  rw [hdot, hc₁, hz1, hz2, hz3, hz4, hz5, hreal_G zNeg, hreal_F zPos, hreal_F zNeg, hreal_G zPos]
  simp only [Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.conj_im,
    Complex.natCast_re, Complex.natCast_im]
  ring

/-- Diagonal specialization of the single-quartet Parseval identity. -/
theorem bareMixedEnergy_self_singleQuartet {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    bareMixedEnergy G G = onLineEnergy G +
      4 * (quartetCopyMult ρ₀ : ℝ) *
        (negativeHalfLineLaplace (cx G) (ρ₀ - 1 / 2) *
          conj (negativeHalfLineLaplace (cx G) (1 / 2 - conj ρ₀))).re := by
  rw [bareMixedEnergy_singleQuartet hq hG hG, onLineMixed_self, quartetSwapMatrix_mulVec]
  simp only [quartetEvalVec, dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-! ### 2. The `4 × 4` Birman–Schwinger secular equation of the quartet -/

/-- The four real half-line exponential mode targets representing `quartetEvalVec ρ₀ ·` in `W₈`. -/
def quartetModeTarget (ρ₀ : ℂ) : Fin 4 → ℝ → ℝ
  | 0 => modeCos (ρ₀ - 1 / 2)
  | 1 => modeSin (ρ₀ - 1 / 2)
  | 2 => modeCos (1 / 2 - conj ρ₀)
  | 3 => modeSin (1 / 2 - conj ρ₀)

theorem isW8Target_quartetModeTarget {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) (i : Fin 4) :
    IsW8Target (quartetModeTarget ρ₀ i) := by
  have hre_pos : -4 < (ρ₀ - 1 / 2).re := by simp; linarith [hq.1]
  have hre_neg : -4 < (1 / 2 - conj ρ₀).re := by simp; linarith [hq.re_lt_one]
  fin_cases i
  · exact isW8Target_modeCos hre_pos
  · exact isW8Target_modeSin hre_pos
  · exact isW8Target_modeCos hre_neg
  · exact isW8Target_modeSin hre_neg

theorem w8Pair_quartetModeTarget_eq {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (i : Fin 4) :
    w8Pair (quartetModeTarget ρ₀ i) G = quartetEvalVec ρ₀ G i := by
  have hre_pos : -4 < (ρ₀ - 1 / 2).re := by simp; linarith [hq.1]
  have hre_neg : -4 < (1 / 2 - conj ρ₀).re := by simp; linarith [hq.re_lt_one]
  fin_cases i
  · exact w8Pair_modeCos_eq_re_laplace hG hre_pos
  · exact w8Pair_modeSin_eq_im_laplace hG hre_pos
  · exact w8Pair_modeCos_eq_re_laplace hG hre_neg
  · exact w8Pair_modeSin_eq_im_laplace hG hre_neg

/-- The four Birman–Schwinger on-line mode resolvents attached to the quartet `Q(ρ₀)` at `a > 0`. -/
def quartetModeResolvent {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) {a : ℝ} (ha : 0 < a)
    (i : Fin 4) : ℝ → ℝ :=
  zetaOnLineResolvent hq.finiteOffLine ha (isW8Target_quartetModeTarget hq i)

theorem quartetModeResolvent_solves {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {a : ℝ} (ha : 0 < a) (i : Fin 4) :
    SolvesZetaOnLineResolvent a (quartetModeTarget ρ₀ i) (quartetModeResolvent hq ha i) :=
  zetaOnLineResolvent_solves hq.finiteOffLine ha (isW8Target_quartetModeTarget hq i)

/-- The `4 × 4` on-line resolvent Gram matrix `G_on(a)_{ij} = quartetEvalVec(Φ_j)_i`. -/
def quartetOnLineGram {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) {a : ℝ} (ha : 0 < a) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => quartetEvalVec ρ₀ (quartetModeResolvent hq ha j) i

theorem quartetOnLineGram_symm {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) {a : ℝ} (ha : 0 < a)
    (i j : Fin 4) :
    quartetOnLineGram hq ha i j = quartetOnLineGram hq ha j i := by
  unfold quartetOnLineGram
  have hi := quartetModeResolvent_solves hq ha i
  have hj := quartetModeResolvent_solves hq ha j
  rw [← w8Pair_quartetModeTarget_eq hq hj.1 i, ← w8Pair_quartetModeTarget_eq hq hi.1 j,
    ← hi.2 _ hj.1, ← hj.2 _ hi.1, onLineMixed_comm, w8Pair_comm]

/-- **The `4 × 4` secular matrix `I₄ + 2 m G_on(a(R)) J₄` of the single quartet at ratio `R > 0`.** -/
def quartetSecularMatrix {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) {R : ℝ} (hR : 0 < R) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  1 + (2 * (quartetCopyMult ρ₀ : ℝ)) •
    (quartetOnLineGram hq (criticalAliasCoefficient_positive hR) * quartetSwapMatrix)

private theorem isW8Target_quartetComb {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    (c : Fin 4 → ℝ) :
    IsW8Target fun u => ∑ j : Fin 4, c j * quartetModeTarget ρ₀ j u := by
  have h01 := isW8Target_add
    (isW8Target_const_mul (isW8Target_quartetModeTarget hq 0) (c 0))
    (isW8Target_const_mul (isW8Target_quartetModeTarget hq 1) (c 1))
  have h23 := isW8Target_add
    (isW8Target_const_mul (isW8Target_quartetModeTarget hq 2) (c 2))
    (isW8Target_const_mul (isW8Target_quartetModeTarget hq 3) (c 3))
  have heq : (fun u => ∑ j : Fin 4, c j * quartetModeTarget ρ₀ j u) =
      fun u => (c 0 * quartetModeTarget ρ₀ 0 u + c 1 * quartetModeTarget ρ₀ 1 u) +
        (c 2 * quartetModeTarget ρ₀ 2 u + c 3 * quartetModeTarget ρ₀ 3 u) := by
    funext u; rw [Fin.sum_univ_four]; ring
  rw [heq]
  exact isW8Target_add h01 h23

private theorem w8Pair_quartetTargetComb {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    (c : Fin 4 → ℝ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    w8Pair (fun u => ∑ j : Fin 4, c j * quartetModeTarget ρ₀ j u) G =
      ∑ j : Fin 4, c j * quartetEvalVec ρ₀ G j := by
  have hy := fun j : Fin 4 => isW8Target_const_mul (isW8Target_quartetModeTarget hq j) (c j)
  have heq : (fun u => ∑ j : Fin 4, c j * quartetModeTarget ρ₀ j u) =
      fun u => (c 0 * quartetModeTarget ρ₀ 0 u + c 1 * quartetModeTarget ρ₀ 1 u) +
        (c 2 * quartetModeTarget ρ₀ 2 u + c 3 * quartetModeTarget ρ₀ 3 u) := by
    funext u; rw [Fin.sum_univ_four]; ring
  rw [heq,
    w8Pair_add_left (isW8Target_add (hy 0) (hy 1)) (isW8Target_add (hy 2) (hy 3))
      (isW8Target_of_domain hG),
    w8Pair_add_left (hy 0) (hy 1) (isW8Target_of_domain hG),
    w8Pair_add_left (hy 2) (hy 3) (isW8Target_of_domain hG)]
  simp only [w8Pair_const_mul_left, w8Pair_quartetModeTarget_eq hq hG, Fin.sum_univ_four]
  ring

private theorem solvesResolvent_quartetLinearComb {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {a : ℝ} (ha : 0 < a) (c : Fin 4 → ℝ) :
    SolvesZetaOnLineResolvent a
      (fun u => ∑ j : Fin 4, c j * quartetModeTarget ρ₀ j u)
      (fun u => ∑ j : Fin 4, c j * quartetModeResolvent hq ha j u) ∧
    quartetEvalVec ρ₀ (fun u => ∑ j : Fin 4, c j * quartetModeResolvent hq ha j u) =
      quartetOnLineGram hq ha *ᵥ c := by
  let Φ := quartetModeResolvent hq ha
  have hΦ := quartetModeResolvent_solves hq ha
  have h01 : CriticalHalfLineEnergyDomain fun u => c 0 * Φ 0 u + c 1 * Φ 1 u :=
    ((hΦ 0).1.const_mul (c 0)).add_const_mul (hΦ 1).1 (c 1)
  have h23 : CriticalHalfLineEnergyDomain fun u => c 2 * Φ 2 u + c 3 * Φ 3 u :=
    ((hΦ 2).1.const_mul (c 2)).add_const_mul (hΦ 3).1 (c 3)
  have hX_eq : (fun u => ∑ j : Fin 4, c j * Φ j u) =
      fun u => (c 0 * Φ 0 u + c 1 * Φ 1 u) + 1 * (c 2 * Φ 2 u + c 3 * Φ 3 u) := by
    funext u; rw [Fin.sum_univ_four]; ring
  have hX_dom : CriticalHalfLineEnergyDomain fun u => ∑ j : Fin 4, c j * Φ j u := by
    rw [hX_eq]; exact h01.add_const_mul h23 1
  have hsol : SolvesZetaOnLineResolvent a
      (fun u => ∑ j : Fin 4, c j * quartetModeTarget ρ₀ j u)
      (fun u => ∑ j : Fin 4, c j * Φ j u) := by
    refine ⟨hX_dom, fun G hG => ?_⟩
    rw [w8Pair_quartetTargetComb hq c hG, hX_eq,
      onLineMixed_add_left h01 (h23.const_mul 1) hG hq.finiteOffLine,
      onLineMixed_const_mul_left 1,
      onLineMixed_add_left ((hΦ 0).1.const_mul (c 0)) ((hΦ 1).1.const_mul (c 1)) hG hq.finiteOffLine,
      onLineMixed_add_left ((hΦ 2).1.const_mul (c 2)) ((hΦ 3).1.const_mul (c 3)) hG hq.finiteOffLine,
      onLineMixed_const_mul_left, onLineMixed_const_mul_left,
      onLineMixed_const_mul_left, onLineMixed_const_mul_left,
      w8Pair_add_left (isW8Target_of_domain h01) (isW8Target_of_domain (h23.const_mul 1))
        (isW8Target_of_domain hG),
      w8Pair_const_mul_left 1,
      w8Pair_add_left (isW8Target_of_domain ((hΦ 0).1.const_mul (c 0)))
        (isW8Target_of_domain ((hΦ 1).1.const_mul (c 1))) (isW8Target_of_domain hG),
      w8Pair_add_left (isW8Target_of_domain ((hΦ 2).1.const_mul (c 2)))
        (isW8Target_of_domain ((hΦ 3).1.const_mul (c 3))) (isW8Target_of_domain hG),
      w8Pair_const_mul_left, w8Pair_const_mul_left,
      w8Pair_const_mul_left, w8Pair_const_mul_left, Fin.sum_univ_four]
    have e0 := ((hΦ 0).2 G hG).trans (w8Pair_quartetModeTarget_eq hq hG 0)
    have e1 := ((hΦ 1).2 G hG).trans (w8Pair_quartetModeTarget_eq hq hG 1)
    have e2 := ((hΦ 2).2 G hG).trans (w8Pair_quartetModeTarget_eq hq hG 2)
    have e3 := ((hΦ 3).2 G hG).trans (w8Pair_quartetModeTarget_eq hq hG 3)
    linear_combination c 0 * e0 + c 1 * e1 + c 2 * e2 + c 3 * e3
  refine ⟨hsol, ?_⟩
  ext i
  rw [← w8Pair_quartetModeTarget_eq hq hX_dom i, w8Pair_comm, hX_eq,
    w8Pair_add_left (isW8Target_of_domain h01) (isW8Target_of_domain (h23.const_mul 1))
      (isW8Target_quartetModeTarget hq i),
    w8Pair_const_mul_left 1,
    w8Pair_add_left (isW8Target_of_domain ((hΦ 0).1.const_mul (c 0)))
      (isW8Target_of_domain ((hΦ 1).1.const_mul (c 1))) (isW8Target_quartetModeTarget hq i),
    w8Pair_add_left (isW8Target_of_domain ((hΦ 2).1.const_mul (c 2)))
      (isW8Target_of_domain ((hΦ 3).1.const_mul (c 3))) (isW8Target_quartetModeTarget hq i),
    w8Pair_const_mul_left, w8Pair_const_mul_left,
    w8Pair_const_mul_left, w8Pair_const_mul_left]
  rw [w8Pair_comm (Φ 0), w8Pair_comm (Φ 1), w8Pair_comm (Φ 2), w8Pair_comm (Φ 3),
    w8Pair_quartetModeTarget_eq hq (hΦ 0).1 i, w8Pair_quartetModeTarget_eq hq (hΦ 1).1 i,
    w8Pair_quartetModeTarget_eq hq (hΦ 2).1 i, w8Pair_quartetModeTarget_eq hq (hΦ 3).1 i]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, quartetOnLineGram]
  ring

private theorem quartetEvalVec_congr_ae {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {F₁ F₂ : ℝ → ℝ} (h₁ : CriticalHalfLineEnergyDomain F₁) (h₂ : CriticalHalfLineEnergyDomain F₂)
    (hae : F₁ =ᵐ[volume] F₂) :
    quartetEvalVec ρ₀ F₁ = quartetEvalVec ρ₀ F₂ := by
  ext i
  rw [← w8Pair_quartetModeTarget_eq hq h₁ i, ← w8Pair_quartetModeTarget_eq hq h₂ i]
  unfold w8Pair
  exact integral_congr_ae (hae.mono fun u hu => by dsimp only; rw [hu])

private theorem setIntegral_Iio_w8_eq' {F G : ℝ → ℝ} (hF0 : ∀ u, 0 ≤ u → F u = 0) :
    (∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) = w8Pair F G :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
    rw [hF0 u (not_lt.mp hu), zero_mul, zero_mul]

/-- **Birman–Schwinger bijection between confined null vectors and the kernel of `quartetSecularMatrix`.**
Under `HasSingleOffLineQuartet ρ₀`, for every `R > 0`:
1. Every confined null vector `(R, F)` satisfies `quartetEvalVec ρ₀ F ≠ 0`,
   `quartetSecularMatrix hq hR *ᵥ quartetEvalVec ρ₀ F = 0`, and its explicit 4-mode resolvent expansion.
2. Every nonzero kernel vector `v` of `quartetSecularMatrix hq hR` produces a confined null vector `F`
   at ratio `R` with `quartetEvalVec ρ₀ F = v`. -/
theorem nullVector_iff_secularKernel {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {R : ℝ} (hR : 0 < R) :
    (∀ {F : ℝ → ℝ}, IsConfinedNullVector R F →
      quartetEvalVec ρ₀ F ≠ 0 ∧
      quartetSecularMatrix hq hR *ᵥ quartetEvalVec ρ₀ F = 0 ∧
      F =ᵐ[volume] fun u => ∑ j : Fin 4,
        (-(2 * (quartetCopyMult ρ₀ : ℝ)) * (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ F) j) *
          quartetModeResolvent hq (criticalAliasCoefficient_positive hR) j u) ∧
    (∀ {v : Fin 4 → ℝ}, v ≠ 0 → quartetSecularMatrix hq hR *ᵥ v = 0 →
      ∃ F : ℝ → ℝ, IsConfinedNullVector R F ∧ quartetEvalVec ρ₀ F = v) := by
  set a := criticalAliasCoefficient R
  have ha : 0 < a := criticalAliasCoefficient_positive hR
  constructor
  · intro F hF
    set v := quartetEvalVec ρ₀ F
    set c : Fin 4 → ℝ := fun j => -(2 * (quartetCopyMult ρ₀ : ℝ)) * (quartetSwapMatrix *ᵥ v) j
    have hsol_X := solvesResolvent_quartetLinearComb hq ha c
    have hsol_F : SolvesZetaOnLineResolvent a
        (fun u => ∑ j : Fin 4, c j * quartetModeTarget ρ₀ j u) F := by
      refine ⟨hF.1, fun G hG => ?_⟩
      have hnull := hF.2.2 G hG
      rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hF.1.support,
        bareMixedEnergy_singleQuartet hq hF.1 hG] at hnull
      rw [w8Pair_quartetTargetComb hq c hG]
      have hdot_c : ∑ j : Fin 4, c j * quartetEvalVec ρ₀ G j =
          -(2 * (quartetCopyMult ρ₀ : ℝ)) *
            dotProduct v (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ G) := by
        calc ∑ j : Fin 4, c j * quartetEvalVec ρ₀ G j
            = -(2 * (quartetCopyMult ρ₀ : ℝ)) *
                dotProduct (quartetSwapMatrix *ᵥ v) (quartetEvalVec ρ₀ G) := by
              simp only [c, dotProduct, Fin.sum_univ_four]; ring
          _ = -(2 * (quartetCopyMult ρ₀ : ℝ)) *
                dotProduct v (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ G) := by
              rw [dotProduct_quartetSwapMatrix_symm]
      rw [hdot_c]
      linarith
    have hae : F =ᵐ[volume] fun u => ∑ j : Fin 4, c j * quartetModeResolvent hq ha j u :=
      solvesZetaOnLineResolvent_ae_unique hq.finiteOffLine ha hsol_F hsol_X.1
    have hv_eq : v = quartetOnLineGram hq ha *ᵥ c :=
      (quartetEvalVec_congr_ae hq hF.1 hsol_X.1.1 hae).trans hsol_X.2
    have hv_ne : v ≠ 0 := by
      intro hv0
      have hc0 : c = 0 := by
        ext j; simp [c, hv0]
      have hae0 : F =ᵐ[volume] 0 := by
        refine hae.trans (Eventually.of_forall fun u => ?_)
        simp [hc0]
      apply hF.2.1
      exact integral_eq_zero_of_ae (hae0.mono fun u (hu : F u = 0) => by simp [hu])
    have hker : quartetSecularMatrix hq hR *ᵥ v = 0 := by
      unfold quartetSecularMatrix
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
      have hc_smul : c = -(2 * (quartetCopyMult ρ₀ : ℝ)) • (quartetSwapMatrix *ᵥ v) := by
        ext j; simp [c]
      rw [hc_smul, Matrix.mulVec_smul] at hv_eq
      ext i
      have hi := congrFun hv_eq i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
      linarith
    exact ⟨hv_ne, hker, hae⟩
  · intro v hv_ne hker
    set c : Fin 4 → ℝ := -(2 * (quartetCopyMult ρ₀ : ℝ)) • (quartetSwapMatrix *ᵥ v)
    obtain ⟨hsol_X, heval_X⟩ := solvesResolvent_quartetLinearComb hq ha c
    set F : ℝ → ℝ := fun u => ∑ j : Fin 4, c j * quartetModeResolvent hq ha j u
    have hvF : quartetEvalVec ρ₀ F = v := by
      rw [heval_X]
      dsimp [c]
      rw [Matrix.mulVec_smul]
      unfold quartetSecularMatrix at hker
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at hker
      ext i
      have hi := congrFun hker i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
      linarith
    have hF_sq_ne : (∫ u, F u ^ 2) ≠ 0 := by
      intro hsq0
      have hae : ∀ᵐ u ∂volume, F u ^ 2 = 0 :=
        (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun u => sq_nonneg (F u))
          hsol_X.1.sq).mp hsq0
      have hF0 : F =ᵐ[volume] fun _ => (0 : ℝ) := hae.mono fun u hu => sq_eq_zero_iff.mp hu
      have h0_dom : CriticalHalfLineEnergyDomain (fun _ : ℝ => (0 : ℝ)) := by
        simpa using (criticalHalfLineEnergyDomain_probe (by norm_num : (4 : ℝ) < 5)).const_mul 0
      have hv0 : quartetEvalVec ρ₀ F = 0 := by
        rw [quartetEvalVec_congr_ae hq hsol_X.1 h0_dom hF0]
        ext i; fin_cases i <;> simp [quartetEvalVec, cx, negativeHalfLineLaplace]
      exact hv_ne (hvF ▸ hv0)
    refine ⟨F, ⟨hsol_X.1, hF_sq_ne, fun G hG => ?_⟩, hvF⟩
    rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hsol_X.1.support,
      bareMixedEnergy_singleQuartet hq hsol_X.1 hG]
    have hFG := (hsol_X.2 G hG).trans (w8Pair_quartetTargetComb hq c hG)
    have hdot_c : ∑ j : Fin 4, c j * quartetEvalVec ρ₀ G j =
        -(2 * (quartetCopyMult ρ₀ : ℝ)) *
          dotProduct (quartetEvalVec ρ₀ F) (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ G) := by
      rw [hvF]
      calc ∑ j : Fin 4, c j * quartetEvalVec ρ₀ G j
          = -(2 * (quartetCopyMult ρ₀ : ℝ)) *
              dotProduct (quartetSwapMatrix *ᵥ v) (quartetEvalVec ρ₀ G) := by
            simp only [c, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_four]; ring
        _ = -(2 * (quartetCopyMult ρ₀ : ℝ)) *
              dotProduct v (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ G) := by
            rw [dotProduct_quartetSwapMatrix_symm]
    linarith

/-- **Secular determinant theorem of the single quartet.** Under `HasSingleOffLineQuartet ρ₀`, for
every ratio `R > 0`, the confined form `Q_R` admits a null vector if and only if
`det(I₄ + 2 m G_on(a(R)) J₄) = 0`. -/
theorem exists_confinedNullVector_iff_quartetSecularDet_eq_zero {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {R : ℝ} (hR : 0 < R) :
    (∃ F : ℝ → ℝ, IsConfinedNullVector R F) ↔ (quartetSecularMatrix hq hR).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  obtain ⟨hfwd, hbwd⟩ := nullVector_iff_secularKernel hq hR
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨hv_ne, hker, -⟩ := hfwd hF
    exact ⟨quartetEvalVec ρ₀ F, hv_ne, hker⟩
  · rintro ⟨v, hv_ne, hker⟩
    obtain ⟨F, hF, -⟩ := hbwd hv_ne hker
    exact ⟨F, hF⟩

/-- **First-root positivity of the quartet secular determinant below `W₀`.** At the ground threshold
`W₀`, `det(quartetSecularMatrix) = 0`, while for every `0 < R < W₀`, `0 < det(quartetSecularMatrix)`. -/
theorem quartetSecularDet_pos_below_threshold {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F₀ : ℝ → ℝ} (hF₀ : IsCriticalHalfLineGroundState W₀ F₀) :
    (quartetSecularMatrix hq hW).det = 0 ∧
      ∀ {R : ℝ} (hR : 0 < R), R < W₀ → 0 < (quartetSecularMatrix hq hR).det := by
  refine ⟨(exists_confinedNullVector_iff_quartetSecularDet_eq_zero hq hW).mp
    ⟨F₀, isConfinedNullVector_of_groundState hW ht hF₀⟩, fun {R} hR hRW => ?_⟩
  set a := criticalAliasCoefficient R
  have ha : 0 < a := criticalAliasCoefficient_positive hR
  let A : Matrix (Fin 4) (Fin 4) ℝ := quartetOnLineGram hq ha * quartetSwapMatrix
  let M : ℝ → Matrix (Fin 4) (Fin 4) ℝ :=
    fun t => 1 + (t * (2 * (quartetCopyMult ρ₀ : ℝ))) • A
  have hM0 : (M 0).det = 1 := by simp [M]
  have hM1 : M 1 = quartetSecularMatrix hq hR := by simp [M, A, quartetSecularMatrix]
  have hcont : Continuous fun t : ℝ => (M t).det := by
    refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
    have : (fun t : ℝ => M t i j) =
        fun t : ℝ => (1 : Matrix (Fin 4) (Fin 4) ℝ) i j +
          t * (2 * (quartetCopyMult ρ₀ : ℝ)) * A i j := by
      funext t; simp [M, mul_assoc]
    rw [this]; fun_prop
  have hne0 : ∀ t ∈ Icc (0 : ℝ) 1, (M t).det ≠ 0 := by
    intro t ht_mem hdet0
    rcases eq_or_lt_of_le ht_mem.1 with rfl | ht_pos
    · rw [hM0] at hdet0; exact one_ne_zero hdet0
    · obtain ⟨v, hv_ne, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
      set c : Fin 4 → ℝ := -(t * (2 * (quartetCopyMult ρ₀ : ℝ))) • (quartetSwapMatrix *ᵥ v)
      obtain ⟨hsol_X, heval_X⟩ := solvesResolvent_quartetLinearComb hq ha c
      set X : ℝ → ℝ := fun u => ∑ j : Fin 4, c j * quartetModeResolvent hq ha j u
      have hvX : quartetEvalVec ρ₀ X = v := by
        rw [heval_X]; dsimp [c]; rw [Matrix.mulVec_smul]
        dsimp [M, A] at hMv
        rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at hMv
        ext i
        have hi := congrFun hMv i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
        linarith
      have hw8_pos : 0 < w8Mass X := by
        refine lt_of_le_of_ne (w8Mass_nonneg X) fun hw0 => hv_ne ?_
        rw [← hvX]; ext i
        rw [← w8Pair_quartetModeTarget_eq hq hsol_X.1 i]
        have hcs := sq_w8Pair_le (isW8Target_quartetModeTarget hq i) (isW8Target_of_domain hsol_X.1)
        rw [← hw0, mul_zero] at hcs
        exact sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg _))
      set P_off : ℝ := 2 * (quartetCopyMult ρ₀ : ℝ) *
        dotProduct (quartetEvalVec ρ₀ X) (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ X)
      have hon_eq : onLineEnergy X + a * w8Mass X = -t * P_off := by
        have hXX := (hsol_X.2 X hsol_X.1).trans (w8Pair_quartetTargetComb hq c hsol_X.1)
        rw [onLineMixed_self, w8Pair_self] at hXX
        rw [hXX]
        dsimp [P_off]; rw [hvX]
        calc ∑ j : Fin 4, c j * v j
            = -(t * (2 * (quartetCopyMult ρ₀ : ℝ))) *
                dotProduct (quartetSwapMatrix *ᵥ v) v := by
              simp only [c, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_four]; ring
          _ = -t * (2 * (quartetCopyMult ρ₀ : ℝ) * dotProduct v (quartetSwapMatrix *ᵥ v)) := by
              rw [dotProduct_quartetSwapMatrix_symm]; ring
      have hpos_lhs : 0 < onLineEnergy X + a * w8Mass X :=
        add_pos_of_nonneg_of_pos (onLineEnergy_nonneg X) (mul_pos ha hw8_pos)
      have hP_neg : P_off < 0 := by nlinarith
      have hQR_eq : criticalHalfLineFullEnergy R X = (1 - t) * P_off := by
        have h1 := criticalHalfLineFullEnergy_add_const_mul R hsol_X.1 hsol_X.1 1
        have hfun : (fun u => X u + 1 * X u) = fun u => (2 : ℝ) * X u := by funext u; ring
        rw [hfun, criticalHalfLineFullEnergy_const_mul] at h1
        have hmix : criticalHalfLineMixedEnergy R X X = criticalHalfLineFullEnergy R X := by linarith
        rw [← hmix, criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hsol_X.1.support,
          w8Pair_self, bareMixedEnergy_singleQuartet hq hsol_X.1 hsol_X.1, onLineMixed_self]
        change onLineEnergy X + P_off + a * w8Mass X = (1 - t) * P_off
        linarith [hon_eq]
      have hQR_nonpos : criticalHalfLineFullEnergy R X ≤ 0 := by
        rw [hQR_eq]
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith [ht_mem.2]) hP_neg.le
      have hQW_nonneg : 0 ≤ criticalHalfLineFullEnergy W₀ X := by
        have h0 := criticalHalfLineGroundEnergy_mul_mass_le_all hW hsol_X.1
        rw [criticalHalfLineGroundEnergy_eq_zero hW ht hF₀, zero_mul] at h0
        exact h0
      have halias_gt : criticalAliasCoefficient W₀ < criticalAliasCoefficient R :=
        lt_of_le_of_ne (criticalAliasCoefficient_antitone hR hRW.le)
          fun heq => hRW.ne (criticalAliasCoefficient_injective_positive hR hW heq.symm)
      have hchange := criticalHalfLineFullEnergy_change_ratio R W₀ hsol_X.1
      change criticalHalfLineFullEnergy R X = criticalHalfLineFullEnergy W₀ X +
        (criticalAliasCoefficient R - criticalAliasCoefficient W₀) * w8Mass X at hchange
      have hQR_pos : 0 < criticalHalfLineFullEnergy R X := by
        rw [hchange]
        nlinarith [mul_pos (sub_pos.mpr halias_gt) hw8_pos]
      linarith
  rw [← hM1]
  by_contra hnot_pos
  have h1_neg : (M 1).det < 0 := lt_of_le_of_ne (not_lt.mp hnot_pos)
    (hne0 1 (right_mem_Icc.mpr zero_le_one))
  have hmem0 : (0 : ℝ) ∈ Icc ((M 1).det) ((M 0).det) := ⟨h1_neg.le, by rw [hM0]; norm_num⟩
  obtain ⟨t, ht_mem, ht0⟩ := isPreconnected_Icc.intermediate_value
    (right_mem_Icc.mpr zero_le_one) (left_mem_Icc.mpr zero_le_one) hcont.continuousOn hmem0
  exact hne0 t ht_mem ht0

/-! ### 3. Complete two-rung spectral ladder, 1D simplicity, Cauchy interlacing, and trace bound -/

private theorem criticalHalfLineMixedEnergy_add_const_mul_left (R : ℝ) {F₁ F₂ G : ℝ → ℝ}
    (h₁ : CriticalHalfLineEnergyDomain F₁) (h₂ : CriticalHalfLineEnergyDomain F₂)
    (hG : CriticalHalfLineEnergyDomain G) (hfin : BacklundConverse.FiniteOffLine) (c : ℝ) :
    criticalHalfLineMixedEnergy R (fun u => F₁ u + c * F₂ u) G =
      criticalHalfLineMixedEnergy R F₁ G + c * criticalHalfLineMixedEnergy R F₂ G := by
  have hc₂ := h₂.const_mul c
  have hsum := h₁.add_const_mul h₂ c
  rw [criticalHalfLineMixedEnergy_eq_bare_add, criticalHalfLineMixedEnergy_eq_bare_add,
    criticalHalfLineMixedEnergy_eq_bare_add,
    setIntegral_Iio_w8_eq' hsum.support, setIntegral_Iio_w8_eq' h₁.support,
    setIntegral_Iio_w8_eq' h₂.support,
    w8Pair_add_left (isW8Target_of_domain h₁) (isW8Target_of_domain hc₂) (isW8Target_of_domain hG),
    w8Pair_const_mul_left,
    bareMixedEnergy_eq_onLineMixed_add_re_offLine hsum hG hfin,
    bareMixedEnergy_eq_onLineMixed_add_re_offLine h₁ hG hfin,
    bareMixedEnergy_eq_onLineMixed_add_re_offLine h₂ hG hfin,
    onLineMixed_add_left h₁ hc₂ hG hfin, onLineMixed_const_mul_left]
  have hoff : (∑ q ∈ offLineCopyFinset hfin,
      negativeHalfLineLaplace (cx fun u => F₁ u + c * F₂ u) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q)).re =
      (∑ q ∈ offLineCopyFinset hfin,
        negativeHalfLineLaplace (cx F₁) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q)).re +
      c * (∑ q ∈ offLineCopyFinset hfin,
        negativeHalfLineLaplace (cx F₂) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q)).re := by
    rw [Complex.re_sum, Complex.re_sum, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hw : -4 < (centredZero q).re := by
      have := (abs_lt.mp (abs_re_centredZero_lt q)).1; linarith
    rw [laplace_cx_add h₁ hc₂ hw, laplace_cx_const_mul, add_mul, mul_assoc,
      Complex.add_re, Complex.re_ofReal_mul]
  rw [hoff]; ring

/-- Unified 1D simplicity lemma for each of the two rungs under `HasSingleOffLineQuartet`:
given two `W₈`-orthogonal confined null vectors `(R_*, F_*)` and `(R_other, F_other)` at distinct
positive ratios, any domain profile `G` annihilating `criticalHalfLineMixedEnergy R_* G ·` is a
scalar multiple of `F_*` almost everywhere. -/
private theorem singleQuartet_rung_ae_unique {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hne : R₁ ≠ R₂)
    {F₁ F₂ : ℝ → ℝ} (hF₁ : IsConfinedNullVector R₁ F₁) (hF₂ : IsConfinedNullVector R₂ F₂)
    (horth₁₂ : w8Pair F₁ F₂ = 0)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (hnullG : ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X →
      criticalHalfLineMixedEnergy R₁ G X = 0) :
    ∃ α : ℝ, G =ᵐ[volume] fun u => α * F₁ u := by
  have hw₁_pos : 0 < w8Mass F₁ := nullVector_confinementMass_pos hF₁
  set α : ℝ := w8Pair G F₁ / w8Mass F₁
  set D : ℝ → ℝ := fun u => G u + (-α) * F₁ u
  have hD_dom : CriticalHalfLineEnergyDomain D := hG.add_const_mul hF₁.1 (-α)
  have hD_null : ∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X →
      criticalHalfLineMixedEnergy R₁ D X = 0 := fun X hX => by
    dsimp [D]
    rw [criticalHalfLineMixedEnergy_add_const_mul_left R₁ hG hF₁.1 hX hq.finiteOffLine (-α),
      hnullG X hX, hF₁.2.2 X hX, mul_zero, add_zero]
  have hDF₁ : w8Pair D F₁ = 0 := by
    dsimp [D]
    rw [w8Pair_add_left (isW8Target_of_domain hG)
      (isW8Target_const_mul (isW8Target_of_domain hF₁.1) (-α)) (isW8Target_of_domain hF₁.1),
      w8Pair_const_mul_left, w8Pair_self]
    dsimp [α]; field_simp [hw₁_pos.ne']; ring
  have hD_sq0 : (∫ u, D u ^ 2) = 0 := by
    by_contra hD_sq_ne
    have hD_vec : IsConfinedNullVector R₁ D := ⟨hD_dom, hD_sq_ne, hD_null⟩
    have hDF₂ : w8Pair D F₂ = 0 := by
      have h := (confinedNullVectors_orthogonal hR₁ hR₂ hne hD_vec hF₂).1
      rwa [setIntegral_Iio_w8_eq' hD_dom.support] at h
    let Rs : Fin 3 → ℝ := ![R₁, R₂, R₁]
    let Fs : Fin 3 → ℝ → ℝ := ![F₁, F₂, D]
    have hRs : ∀ i, 0 < Rs i := fun i => by fin_cases i <;> assumption
    have hFs : ∀ i, IsConfinedNullVector (Rs i) (Fs i) := fun i => by
      fin_cases i <;> assumption
    have horth3 : ∀ i j : Fin 3, i ≠ j → (∫ u : ℝ, Fs i u * Fs j u * Real.exp (-(8 * u))) = 0 := by
      intro i j hij
      change w8Pair (Fs i) (Fs j) = 0
      fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
      · exact horth₁₂
      · rw [w8Pair_comm]; exact hDF₁
      · rw [w8Pair_comm]; exact horth₁₂
      · rw [w8Pair_comm]; exact hDF₂
      · exact hDF₁
      · exact hDF₂
    have hcard := (card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine
      hRs hFs horth3 hq.finiteOffLine).1
    rw [card_rightCentredZeros_singleQuartet hq] at hcard
    omega
  refine ⟨α, ?_⟩
  have hae : ∀ᵐ u ∂volume, D u ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun u => sq_nonneg (D u))
      hD_dom.sq).mp hD_sq0
  filter_upwards [hae] with u hu
  have hDu : D u = 0 := sq_eq_zero_iff.mp hu
  dsimp [D] at hDu
  linarith

/-- **Complete two-rung spectral ladder of a single off-line quartet.**
Under `HasSingleOffLineQuartet ρ₀`, there exist `0 < W₀ < R₂` and unit profiles `F₀, F₁` such that:
1. `W₀` is the critical ground threshold (`IsCriticalHalfLineGroundState W₀ F₀`), `F₀` and `F₁` are
   `W₈`-orthogonal confined null vectors at `W₀` and `R₂`;
2. `{R : ℝ | 0 < R ∧ ∃ F, IsConfinedNullVector R F} = {W₀, R₂}`;
3. Both null spaces at `W₀` and `R₂` are 1-dimensional up to a.e. equality;
4. No ratio `0 < R ≤ R₂` carries a negative plane, while `IsNegativePlane R F₀ F₁` holds for all
   `R > R₂`;
5. The charge-hyperplane positivity threshold `R₁` interlaces `0 < W₀ < R₁ ≤ R₂`. -/
theorem singleQuartet_complete_twoRung_ladder {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀) :
    ∃ (W₀ R₂ : ℝ) (F₀ F₁ : ℝ → ℝ),
      0 < W₀ ∧ W₀ < R₂ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F₀ ∧
      IsConfinedNullVector W₀ F₀ ∧ IsConfinedNullVector R₂ F₁ ∧
      (∫ u, F₀ u ^ 2) = 1 ∧ (∫ u, F₁ u ^ 2) = 1 ∧ w8Pair F₀ F₁ = 0 ∧
      {R : ℝ | 0 < R ∧ ∃ F : ℝ → ℝ, IsConfinedNullVector R F} = {W₀, R₂} ∧
      (∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        (∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X → criticalHalfLineMixedEnergy W₀ G X = 0) →
        ∃ c : ℝ, G =ᵐ[volume] fun u => c * F₀ u) ∧
      (∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
        (∀ X : ℝ → ℝ, CriticalHalfLineEnergyDomain X → criticalHalfLineMixedEnergy R₂ G X = 0) →
        ∃ c : ℝ, G =ᵐ[volume] fun u => c * F₁ u) ∧
      (∀ R : ℝ, 0 < R → R ≤ R₂ → ∀ G₁ G₂ : ℝ → ℝ, ¬ IsNegativePlane R G₁ G₂) ∧
      (∀ R : ℝ, R₂ < R → IsNegativePlane R F₀ F₁) ∧
      (∃ R₁ : ℝ, W₀ < R₁ ∧ R₁ ≤ R₂ ∧
        ∀ R : ℝ, 0 < R → R ≤ R₁ → ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
          growingPolarCharge G = 0 → 0 ≤ criticalHalfLineFullEnergy R G) := by
  obtain ⟨W₀, R₂, F₀, F₁, hW, ht, hF₀_gs, hWR₂, hF₁, hm₁, horth, hno_plane, _⟩ :=
    riemannHypothesis_or_secondCriticalState.resolve_left hq.not_riemannHypothesis
  have hR₂_pos : 0 < R₂ := hW.trans hWR₂
  have hF₀ : IsConfinedNullVector W₀ F₀ := isConfinedNullVector_of_groundState hW ht hF₀_gs
  have hm₀ : (∫ u, F₀ u ^ 2) = 1 := hF₀_gs.2.2.2.1
  have horth_w8 : w8Pair F₀ F₁ = 0 := horth
  have hspec : {R : ℝ | 0 < R ∧ ∃ F : ℝ → ℝ, IsConfinedNullVector R F} = {W₀, R₂} := by
    ext R
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hR, G, hG⟩
      by_contra hne_both
      push Not at hne_both
      obtain ⟨hneW, hneR₂⟩ := hne_both
      let Rs : Fin 3 → ℝ := ![W₀, R₂, R]
      let Fs : Fin 3 → ℝ → ℝ := ![F₀, F₁, G]
      have hRs : ∀ i, 0 < Rs i := fun i => by fin_cases i <;> assumption
      have hFs : ∀ i, IsConfinedNullVector (Rs i) (Fs i) := fun i => by
        fin_cases i <;> assumption
      have horth3 : ∀ i j : Fin 3, i ≠ j →
          (∫ u : ℝ, Fs i u * Fs j u * Real.exp (-(8 * u))) = 0 := by
        intro i j hij
        have hRS_ne : Rs i ≠ Rs j := by
          fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
          · exact hWR₂.ne
          · exact hneW.symm
          · exact hWR₂.ne'
          · exact hneR₂.symm
          · exact hneW
          · exact hneR₂
        have ho := (confinedNullVectors_orthogonal (hRs i) (hRs j) hRS_ne (hFs i) (hFs j)).1
        rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
          rw [(hFs i).1.support u (not_lt.mp hu), zero_mul, zero_mul])] at ho
      have hcard := (card_orthogonalNullVectors_le_rightZeros_of_finiteOffLine
        hRs hFs horth3 hq.finiteOffLine).1
      rw [card_rightCentredZeros_singleQuartet hq] at hcard
      omega
    · rintro (rfl | rfl)
      · exact ⟨hW, F₀, hF₀⟩
      · exact ⟨hR₂_pos, F₁, hF₁⟩
  have hplane_above : ∀ R : ℝ, R₂ < R → IsNegativePlane R F₀ F₁ := by
    intro R hR_gt
    have hR_pos : 0 < R := hR₂_pos.trans hR_gt
    refine ⟨hF₀.1, hF₁.1, fun s t hst => ?_⟩
    rw [criticalHalfLineFullEnergy_combination R hF₀.1 hF₁.1 s t]
    have hmix_zero : criticalHalfLineMixedEnergy R F₀ F₁ = 0 := by
      rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hF₀.1.support,
        horth_w8, mul_zero, add_zero]
      exact (confinedNullVectors_orthogonal hW hR₂_pos hWR₂.ne hF₀ hF₁).2
    have hE_null : ∀ {S : ℝ} {G : ℝ → ℝ}, IsConfinedNullVector S G →
        criticalHalfLineFullEnergy S G = 0 := by
      intro S G hG_null
      have h1 := criticalHalfLineFullEnergy_add_const_mul S hG_null.1 hG_null.1 1
      have hfun : (fun u => G u + 1 * G u) = fun u => (2 : ℝ) * G u := by funext u; ring
      rw [hfun, criticalHalfLineFullEnergy_const_mul, hG_null.2.2 G hG_null.1] at h1
      linarith
    have hE₀ : criticalHalfLineFullEnergy R F₀ < 0 := by
      have hc := criticalHalfLineFullEnergy_change_ratio R W₀ hF₀.1
      rw [hE_null hF₀, zero_add] at hc
      have hlt : criticalAliasCoefficient R < criticalAliasCoefficient W₀ :=
        lt_of_le_of_ne (criticalAliasCoefficient_antitone hW (hWR₂.trans hR_gt).le)
          fun heq => (hWR₂.trans hR_gt).ne' (criticalAliasCoefficient_injective_positive hR_pos hW heq)
      rw [hc]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (nullVector_confinementMass_pos hF₀)
    have hE₁ : criticalHalfLineFullEnergy R F₁ < 0 := by
      have hc := criticalHalfLineFullEnergy_change_ratio R R₂ hF₁.1
      rw [hE_null hF₁, zero_add] at hc
      have hlt : criticalAliasCoefficient R < criticalAliasCoefficient R₂ :=
        lt_of_le_of_ne (criticalAliasCoefficient_antitone hR₂_pos hR_gt.le)
          fun heq => hR_gt.ne' (criticalAliasCoefficient_injective_positive hR_pos hR₂_pos heq)
      rw [hc]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (nullVector_confinementMass_pos hF₁)
    rw [hmix_zero]
    by_cases hs : s = 0
    · have ht0 : t ≠ 0 := fun ht0 => hst (Prod.ext hs ht0)
      subst hs; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        mul_zero, zero_add]
      exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht0) hE₁
    · have hs2 : s ^ 2 * criticalHalfLineFullEnergy R F₀ < 0 :=
        mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hs) hE₀
      have ht2 : t ^ 2 * criticalHalfLineFullEnergy R F₁ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hE₁.le
      linarith
  obtain ⟨R₁', hWR₁', hcharge⟩ := criticalState_chargeHyperplane_nonneg_beyond_threshold hW ht hF₀_gs
  have hR₁'_le_R₂ : R₁' ≤ R₂ := by
    by_contra hgt
    push Not at hgt
    have hneg_plane := hplane_above R₁' hgt
    have hcomb : ∀ s t : ℝ, CriticalHalfLineEnergyDomain (fun u => s * F₀ u + t * F₁ u) :=
      fun s t => (hF₀.1.const_mul s).add_const_mul hF₁.1 t
    have hch : ∀ s t : ℝ, growingPolarCharge (fun u => s * F₀ u + t * F₁ u) =
        s * growingPolarCharge F₀ + t * growingPolarCharge F₁ := by
      intro s t
      have i0 := integrable_halfLineLaplace_of_domain hF₀.1 (s := 1 / 2) (by norm_num)
      have i1 := integrable_halfLineLaplace_of_domain hF₁.1 (s := 1 / 2) (by norm_num)
      unfold growingPolarCharge
      simp_rw [add_mul, mul_assoc]
      rw [integral_add (i0.const_mul s) (i1.const_mul t), integral_const_mul, integral_const_mul]
    have hex_zero : ∃ s t : ℝ, (s, t) ≠ (0, 0) ∧
        growingPolarCharge (fun u => s * F₀ u + t * F₁ u) = 0 := by
      by_cases h0 : growingPolarCharge F₀ = 0 ∧ growingPolarCharge F₁ = 0
      · exact ⟨1, 0, by simp, by rw [hch, h0.1, h0.2]; ring⟩
      · refine ⟨growingPolarCharge F₁, -growingPolarCharge F₀, fun he => h0 ?_,
          by rw [hch]; ring⟩
        simp only [Prod.mk.injEq, neg_eq_zero] at he
        exact ⟨he.2, he.1⟩
    obtain ⟨s, t, hst, hz⟩ := hex_zero
    have hge := hcharge R₁' (hW.trans hWR₁') le_rfl (hcomb s t) hz
    have hlt := hneg_plane.2.2 s t hst
    linarith
  exact ⟨W₀, R₂, F₀, F₁, hW, hWR₂, ht, hF₀_gs, hF₀, hF₁, hm₀, hm₁, horth_w8, hspec,
    fun G hG hnull => singleQuartet_rung_ae_unique hq hW hR₂_pos hWR₂.ne hF₀ hF₁ horth_w8 hG hnull,
    fun G hG hnull => singleQuartet_rung_ae_unique hq hR₂_pos hW hWR₂.ne' hF₁ hF₀
      (by rw [w8Pair_comm]; exact horth_w8) hG hnull,
    hno_plane, hplane_above, R₁', hWR₁', hR₁'_le_R₂,
    fun R hR hRR G hG hz => hcharge R hR hRR hG hz⟩

private theorem w8Mass_modeCos_add_modeSin {w : ℂ} (hw : -4 < w.re) :
    w8Mass (modeCos w) + w8Mass (modeSin w) = 1 / (8 + 2 * w.re) := by
  have hc : 0 < 8 + 2 * w.re := by linarith
  unfold w8Mass
  rw [← integral_add (isW8Target_modeCos hw).2.2 (isW8Target_modeSin hw).2.2]
  have hfun : (fun u : ℝ => modeCos w u ^ 2 * Real.exp (-(8 * u)) +
        modeSin w u ^ 2 * Real.exp (-(8 * u))) =
      Set.indicator (Iio (0 : ℝ)) (fun u => Real.exp ((8 + 2 * w.re) * u)) := by
    funext u
    by_cases hu : u ∈ Iio (0 : ℝ)
    · simp only [modeCos, modeSin, hu, Set.indicator_of_mem]
      have hsc : Real.cos (w.im * u) ^ 2 + Real.sin (w.im * u) ^ 2 = 1 :=
        Real.cos_sq_add_sin_sq (w.im * u)
      calc (Real.exp ((w.re + 8) * u) * Real.cos (w.im * u)) ^ 2 * Real.exp (-(8 * u)) +
            (Real.exp ((w.re + 8) * u) * Real.sin (w.im * u)) ^ 2 * Real.exp (-(8 * u))
          = (Real.cos (w.im * u) ^ 2 + Real.sin (w.im * u) ^ 2) *
              (Real.exp ((w.re + 8) * u) * Real.exp ((w.re + 8) * u) * Real.exp (-(8 * u))) := by ring
        _ = Real.exp ((8 + 2 * w.re) * u) := by
            rw [hsc, one_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    · simp [modeCos, modeSin, hu]
  rw [hfun, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_Iic hc, mul_zero, Real.exp_zero]

private theorem w8_bessel_two {e₀ e₁ y : ℝ → ℝ}
    (he₀ : IsW8Target e₀) (he₁ : IsW8Target e₁) (hy : IsW8Target y)
    (hm₀ : w8Mass e₀ = 1) (hm₁ : w8Mass e₁ = 1) (ho : w8Pair e₀ e₁ = 0) :
    w8Pair y e₀ ^ 2 + w8Pair y e₁ ^ 2 ≤ w8Mass y := by
  set p₀ := w8Pair y e₀
  set p₁ := w8Pair y e₁
  have h1 := w8Mass_add_const_mul hy he₀ (-p₀)
  have h2 := w8Mass_add_const_mul (isW8Target_add hy (isW8Target_const_mul he₀ (-p₀))) he₁ (-p₁)
  have hp1 : w8Pair (fun u => y u + -p₀ * e₀ u) e₁ = p₁ := by
    rw [w8Pair_add_left hy (isW8Target_const_mul he₀ (-p₀)) he₁, w8Pair_const_mul_left, ho,
      mul_zero, add_zero]
  have hnn := w8Mass_nonneg (fun u => (y u + -p₀ * e₀ u) + -p₁ * e₁ u)
  rw [hm₀] at h1
  rw [h1, hp1, hm₁] at h2
  nlinarith

/-- **Joint Bessel trace bound for the two-rung ladder.** Under `HasSingleOffLineQuartet ρ₀`, for
any two ratios `0 < R₁, R₂` (`R₁ ≠ R₂`) carrying confined null vectors,
`a(R₁) + a(R₂) ≤ 2 m / √(16 - (Re ρ₀ - ½)²)`. -/
theorem singleQuartet_alias_sum_le {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hne : R₁ ≠ R₂)
    {F₁ F₂ : ℝ → ℝ} (hF₁ : IsConfinedNullVector R₁ F₁) (hF₂ : IsConfinedNullVector R₂ F₂) :
    criticalAliasCoefficient R₁ + criticalAliasCoefficient R₂ ≤
      2 * (quartetCopyMult ρ₀ : ℝ) / Real.sqrt (16 - (ρ₀.re - 1 / 2) ^ 2) := by
  have hw₁_pos : 0 < w8Mass F₁ := nullVector_confinementMass_pos hF₁
  have hw₂_pos : 0 < w8Mass F₂ := nullVector_confinementMass_pos hF₂
  set c₁ := (Real.sqrt (w8Mass F₁))⁻¹
  set c₂ := (Real.sqrt (w8Mass F₂))⁻¹
  let e₁ : ℝ → ℝ := fun u => c₁ * F₁ u
  let e₂ : ℝ → ℝ := fun u => c₂ * F₂ u
  have he₁_dom : CriticalHalfLineEnergyDomain e₁ := hF₁.1.const_mul c₁
  have he₂_dom : CriticalHalfLineEnergyDomain e₂ := hF₂.1.const_mul c₂
  have hm₁ : w8Mass e₁ = 1 := by
    have hfun : (fun u => e₁ u ^ 2 * Real.exp (-(8 * u))) =
        fun u => c₁ ^ 2 * (F₁ u ^ 2 * Real.exp (-(8 * u))) := by funext u; dsimp [e₁]; ring
    unfold w8Mass
    rw [hfun, integral_const_mul]
    change c₁ ^ 2 * w8Mass F₁ = 1
    dsimp [c₁]; rw [inv_pow, Real.sq_sqrt hw₁_pos.le, inv_mul_cancel₀ hw₁_pos.ne']
  have hm₂ : w8Mass e₂ = 1 := by
    have hfun : (fun u => e₂ u ^ 2 * Real.exp (-(8 * u))) =
        fun u => c₂ ^ 2 * (F₂ u ^ 2 * Real.exp (-(8 * u))) := by funext u; dsimp [e₂]; ring
    unfold w8Mass
    rw [hfun, integral_const_mul]
    change c₂ ^ 2 * w8Mass F₂ = 1
    dsimp [c₂]; rw [inv_pow, Real.sq_sqrt hw₂_pos.le, inv_mul_cancel₀ hw₂_pos.ne']
  have ho : w8Pair e₁ e₂ = 0 := by
    have horth := (confinedNullVectors_orthogonal hR₁ hR₂ hne hF₁ hF₂).1
    rw [setIntegral_Iio_w8_eq' hF₁.1.support] at horth
    dsimp [e₁, e₂]
    rw [w8Pair_const_mul_left, w8Pair_comm F₁ _, w8Pair_const_mul_left, w8Pair_comm F₂ F₁,
      horth, mul_zero, mul_zero]
  set zPos : ℂ := ρ₀ - 1 / 2
  set zNeg : ℂ := 1 / 2 - conj ρ₀
  set δ : ℝ := ρ₀.re - 1 / 2
  have hδ_pos : 0 < δ := sub_pos.mpr hq.1
  have hδ_lt : δ < 1 / 2 := by dsimp [δ]; linarith [hq.re_lt_one]
  have hzPos_re : zPos.re = δ := by simp [zPos, δ]
  have hzNeg_re : zNeg.re = -δ := by simp [zNeg, δ]
  have hwPos : -4 < zPos.re := by linarith
  have hwNeg : -4 < zNeg.re := by linarith
  have hnorm_bessel : ∀ {w : ℂ} (hw : -4 < w.re),
      ‖negativeHalfLineLaplace (cx e₁) w‖ ^ 2 + ‖negativeHalfLineLaplace (cx e₂) w‖ ^ 2 ≤
        1 / (8 + 2 * w.re) := by
    intro w hw
    have hb_cos := w8_bessel_two (isW8Target_of_domain he₁_dom) (isW8Target_of_domain he₂_dom)
      (isW8Target_modeCos hw) hm₁ hm₂ ho
    have hb_sin := w8_bessel_two (isW8Target_of_domain he₁_dom) (isW8Target_of_domain he₂_dom)
      (isW8Target_modeSin hw) hm₁ hm₂ ho
    rw [w8Pair_modeCos_eq_re_laplace he₁_dom hw, w8Pair_modeCos_eq_re_laplace he₂_dom hw] at hb_cos
    rw [w8Pair_modeSin_eq_im_laplace he₁_dom hw, w8Pair_modeSin_eq_im_laplace he₂_dom hw] at hb_sin
    have hsq1 : ‖negativeHalfLineLaplace (cx e₁) w‖ ^ 2 =
        (negativeHalfLineLaplace (cx e₁) w).re ^ 2 + (negativeHalfLineLaplace (cx e₁) w).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hsq2 : ‖negativeHalfLineLaplace (cx e₂) w‖ ^ 2 =
        (negativeHalfLineLaplace (cx e₂) w).re ^ 2 + (negativeHalfLineLaplace (cx e₂) w).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    linarith [w8Mass_modeCos_add_modeSin hw]
  have hbPos := hnorm_bessel hwPos
  have hbNeg := hnorm_bessel hwNeg
  rw [hzPos_re] at hbPos
  rw [hzNeg_re] at hbNeg
  -- Bound each `a(R_i)` by `4 m ‖L e_i(zPos)‖ ‖L e_i(zNeg)‖`
  have halias_le : ∀ {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) (c : ℝ)
      (hm : w8Mass (fun u => c * F u) = 1),
      criticalAliasCoefficient R ≤ 4 * (quartetCopyMult ρ₀ : ℝ) *
        ‖negativeHalfLineLaplace (cx fun u => c * F u) zPos‖ *
          ‖negativeHalfLineLaplace (cx fun u => c * F u) zNeg‖ := by
    intro R F hF c hm
    set e : ℝ → ℝ := fun u => c * F u
    have he_dom : CriticalHalfLineEnergyDomain e := hF.1.const_mul c
    have hnull_F := hF.2.2 F hF.1
    rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hF.1.support,
      w8Pair_self] at hnull_F
    have hbare_e : bareMixedEnergy e e = -criticalAliasCoefficient R := by
      have hsc : bareMixedEnergy e e = c ^ 2 * bareMixedEnergy F F := by
        have h1 : criticalHalfLineFullEnergy R e = c ^ 2 * criticalHalfLineFullEnergy R F := by
          dsimp [e]; rw [criticalHalfLineFullEnergy_const_mul]
        have h1' : criticalHalfLineFullEnergy R e =
            bareMixedEnergy e e + criticalAliasCoefficient R * w8Mass e := by
          have ha1 := criticalHalfLineFullEnergy_add_const_mul R he_dom he_dom 1
          have hfun : (fun u => e u + 1 * e u) = fun u => (2 : ℝ) * e u := by funext u; ring
          rw [hfun, criticalHalfLineFullEnergy_const_mul] at ha1
          have hmix : criticalHalfLineMixedEnergy R e e = criticalHalfLineFullEnergy R e := by linarith
          rw [← hmix, criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' he_dom.support,
            w8Pair_self]
        have h2' : criticalHalfLineFullEnergy R F =
            bareMixedEnergy F F + criticalAliasCoefficient R * w8Mass F := by
          have ha2 := criticalHalfLineFullEnergy_add_const_mul R hF.1 hF.1 1
          have hfun : (fun u => F u + 1 * F u) = fun u => (2 : ℝ) * F u := by funext u; ring
          rw [hfun, criticalHalfLineFullEnergy_const_mul] at ha2
          have hmix : criticalHalfLineMixedEnergy R F F = criticalHalfLineFullEnergy R F := by linarith
          rw [← hmix, criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hF.1.support,
            w8Pair_self]
        have hw_sc : w8Mass e = c ^ 2 * w8Mass F := by
          unfold w8Mass
          have hfun : (fun u => (c * F u) ^ 2 * Real.exp (-(8 * u))) =
              fun u => c ^ 2 * (F u ^ 2 * Real.exp (-(8 * u))) := by funext u; ring
          rw [hfun, integral_const_mul]
        rw [h1', h2', hw_sc] at h1
        linarith
      have hw_sc : 1 = c ^ 2 * w8Mass F := by
        rw [← hm]; unfold w8Mass
        have hfun : (fun u => (c * F u) ^ 2 * Real.exp (-(8 * u))) =
            fun u => c ^ 2 * (F u ^ 2 * Real.exp (-(8 * u))) := by funext u; ring
        rw [hfun, integral_const_mul]
      have hbf : bareMixedEnergy F F = -(criticalAliasCoefficient R * w8Mass F) := by linarith
      calc bareMixedEnergy e e = c ^ 2 * bareMixedEnergy F F := hsc
        _ = c ^ 2 * -(criticalAliasCoefficient R * w8Mass F) := by rw [hbf]
        _ = -criticalAliasCoefficient R * (c ^ 2 * w8Mass F) := by ring
        _ = -criticalAliasCoefficient R * 1 := by rw [← hw_sc]
        _ = -criticalAliasCoefficient R := mul_one _
    have hpar := bareMixedEnergy_self_singleQuartet hq he_dom
    rw [hbare_e] at hpar
    have hon_nn := onLineEnergy_nonneg e
    have hre_neg : -(negativeHalfLineLaplace (cx e) zPos *
        conj (negativeHalfLineLaplace (cx e) zNeg)).re ≤
        ‖negativeHalfLineLaplace (cx e) zPos‖ * ‖negativeHalfLineLaplace (cx e) zNeg‖ := by
      have habs := Complex.abs_re_le_norm
        (negativeHalfLineLaplace (cx e) zPos * conj (negativeHalfLineLaplace (cx e) zNeg))
      rw [norm_mul, Complex.norm_conj] at habs
      exact (neg_le_abs _).trans habs
    have hm_nn : (0 : ℝ) ≤ 4 * (quartetCopyMult ρ₀ : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hre_neg hm_nn]
  have ha₁ := halias_le hF₁ c₁ hm₁
  have ha₂ := halias_le hF₂ c₂ hm₂
  set u₁ := ‖negativeHalfLineLaplace (cx e₁) zPos‖
  set u₂ := ‖negativeHalfLineLaplace (cx e₂) zPos‖
  set v₁ := ‖negativeHalfLineLaplace (cx e₁) zNeg‖
  set v₂ := ‖negativeHalfLineLaplace (cx e₂) zNeg‖
  have hcs2 : (u₁ * v₁ + u₂ * v₂) ^ 2 ≤ (u₁ ^ 2 + u₂ ^ 2) * (v₁ ^ 2 + v₂ ^ 2) := by
    nlinarith [sq_nonneg (u₁ * v₂ - u₂ * v₁)]
  have hprod_le : (u₁ ^ 2 + u₂ ^ 2) * (v₁ ^ 2 + v₂ ^ 2) ≤
      (1 / (8 + 2 * δ)) * (1 / (8 - 2 * δ)) := by
    rw [show 8 + 2 * -δ = 8 - 2 * δ by ring] at hbNeg
    exact mul_le_mul hbPos hbNeg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (by positivity : (0 : ℝ) ≤ 1 / (8 + 2 * δ))
  have hden_eq : (8 + 2 * δ) * (8 - 2 * δ) = 4 * (16 - δ ^ 2) := by ring
  have h16_pos : 0 < 16 - δ ^ 2 := by nlinarith
  have hrhs_sq : (1 / (8 + 2 * δ)) * (1 / (8 - 2 * δ)) =
      (1 / (2 * Real.sqrt (16 - δ ^ 2))) ^ 2 := by
    rw [one_div_mul_one_div, hden_eq, div_pow, one_pow, mul_pow, Real.sq_sqrt h16_pos.le]
    norm_num
  have huv_le : u₁ * v₁ + u₂ * v₂ ≤ 1 / (2 * Real.sqrt (16 - δ ^ 2)) :=
    (abs_le_of_sq_le_sq' (hcs2.trans (hprod_le.trans_eq hrhs_sq)) (by positivity)).2
  have hm_nn : (0 : ℝ) ≤ 4 * (quartetCopyMult ρ₀ : ℝ) := by positivity
  calc criticalAliasCoefficient R₁ + criticalAliasCoefficient R₂
      ≤ 4 * (quartetCopyMult ρ₀ : ℝ) * (u₁ * v₁ + u₂ * v₂) := by linarith
    _ ≤ 4 * (quartetCopyMult ρ₀ : ℝ) * (1 / (2 * Real.sqrt (16 - δ ^ 2))) :=
        mul_le_mul_of_nonneg_left huv_le hm_nn
    _ = 2 * (quartetCopyMult ρ₀ : ℝ) / Real.sqrt (16 - (ρ₀.re - 1 / 2) ^ 2) := by
        dsimp [δ]; field_simp [(Real.sqrt_pos.mpr h16_pos).ne']; ring

/-! ### 4. Direct-sum synthesis of `E-Q6` and `E-Q1` -/

/-- **Individual continuation criterion under a single off-line quartet.** For every profile `G` in
the half-line energy domain, `HasBeyondTheWallPrimeContinuation G` holds iff
`L G(½ - conj ρ₀) = 0`. -/
theorem singleQuartet_hasBeyondTheWallPrimeContinuation_iff {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    HasBeyondTheWallPrimeContinuation G ↔
      negativeHalfLineLaplace (cx G) (1 / 2 - conj ρ₀) = 0 := by
  rw [hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros hG]
  constructor
  · intro h
    obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero (xi_quartet_eq_zero hq.xi_eq_zero).2.2
    have hzc : centredZero q = 1 / 2 - conj ρ₀ := by
      rw [centredZero, hq_eq]; ring
    rw [← hzc]
    exact h q (by rw [hzc]; simp; linarith [hq.1])
  · intro h0 q hq_neg
    have hmem : centredZero q ∈ leftCentredZeros hq.finiteOffLine :=
      (mem_leftCentredZeros_iff hq.finiteOffLine).mpr ⟨hq_neg, xi_centredZero q⟩
    rw [leftCentredZeros_eq_singleQuartet hq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2
    · rw [h1]
      have hconj : (1 : ℂ) / 2 - ρ₀ = conj (1 / 2 - conj ρ₀) := by
        apply Complex.ext <;> simp
      have h0' : negativeHalfLineLaplace (fun u => (G u : ℂ)) (1 / 2 - conj ρ₀) = 0 := h0
      rw [hconj, show cx G = fun u => (G u : ℂ) from rfl, negativeHalfLineLaplace_real_conj,
        h0', map_zero]
    · rwa [h2]

/-- **Evaluation at `½ - conj ρ₀` is an `ℝ`-linear isomorphism on the two-rung span `ℝ F₀ ⊕ ℝ F₁`.** -/
theorem singleQuartet_leftPair_isolator_isomorphism {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hne : R₁ ≠ R₂)
    {F₀ F₁ : ℝ → ℝ} (hF₀ : IsConfinedNullVector R₁ F₀) (hF₁ : IsConfinedNullVector R₂ F₁)
    (w₀ : ℂ) :
    ∃! st : ℝ × ℝ,
      negativeHalfLineLaplace (cx fun u => st.1 * F₀ u + st.2 * F₁ u) (1 / 2 - conj ρ₀) = w₀ := by
  have horth_pair : ∀ i j : Fin 2, i ≠ j →
      (∫ u : ℝ, (![F₀, F₁] i) u * (![F₀, F₁] j) u * Real.exp (-(8 * u))) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij
    · have h := (confinedNullVectors_orthogonal hR₁ hR₂ hne hF₀ hF₁).1
      rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
        rw [hF₀.1.support u (not_lt.mp hu), zero_mul, zero_mul])] at h
    · have h := (confinedNullVectors_orthogonal hR₂ hR₁ hne.symm hF₁ hF₀).1
      rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
        rw [hF₁.1.support u (not_lt.mp hu), zero_mul, zero_mul])] at h
  have hRs : ∀ i : Fin 2, 0 < ![R₁, R₂] i := fun i => by fin_cases i <;> assumption
  have hFs : ∀ i : Fin 2, IsConfinedNullVector (![R₁, R₂] i) (![F₀, F₁] i) := fun i => by
    fin_cases i <;> assumption
  let Lmap : (Fin 2 → ℝ) →ₗ[ℝ] (ℝ × ℝ) := {
    toFun := fun c =>
      let v := negativeHalfLineLaplace (cx fun u => c 0 * F₀ u + c 1 * F₁ u) (1 / 2 - conj ρ₀)
      (v.re, v.im)
    map_add' := fun c₁ c₂ => by
      have hw : -4 < (1 / 2 - conj ρ₀).re := by simp; linarith [hq.re_lt_one]
      have hfun : (fun u => (c₁ + c₂) 0 * F₀ u + (c₁ + c₂) 1 * F₁ u) =
          fun u => (c₁ 0 * F₀ u + c₁ 1 * F₁ u) + (c₂ 0 * F₀ u + c₂ 1 * F₁ u) := by
        funext u; simp; ring
      dsimp only
      rw [hfun, laplace_cx_add ((hF₀.1.const_mul _).add_const_mul hF₁.1 _)
        ((hF₀.1.const_mul _).add_const_mul hF₁.1 _) hw]
      ext <;> simp
    map_smul' := fun r c => by
      have hfun : (fun u => (r • c) 0 * F₀ u + (r • c) 1 * F₁ u) =
          fun u => r * (c 0 * F₀ u + c 1 * F₁ u) := by
        funext u; simp; ring
      dsimp only
      rw [hfun, laplace_cx_const_mul]
      ext <;> simp
  }
  have hinj_L : Function.Injective Lmap := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have hval0 : negativeHalfLineLaplace (cx fun u => c 0 * F₀ u + c 1 * F₁ u) (1 / 2 - conj ρ₀) = 0 :=
      Complex.ext (congrArg Prod.fst hc) (congrArg Prod.snd hc)
    have hcont : HasBeyondTheWallPrimeContinuation (fun u => c 0 * F₀ u + c 1 * F₁ u) :=
      (singleQuartet_hasBeyondTheWallPrimeContinuation_iff hq
        ((hF₀.1.const_mul _).add_const_mul hF₁.1 _)).mpr hval0
    have hvan_up := (hasBeyondTheWallPrimeContinuation_iff_vanish_upperLeft_of_finiteOffLine
      ((hF₀.1.const_mul _).add_const_mul hF₁.1 _) hq.finiteOffLine).mp hcont
    have hinj := orthogonalNullSpan_eval_upperLeft_injective hRs hFs horth_pair hq.finiteOffLine
    apply hinj
    rw [map_zero]
    ext z
    · dsimp [upperLeftEvalMap]
      have hsum2 : (fun u => ∑ i : Fin 2, c i * (![F₀, F₁] i) u) =
          fun u => c 0 * F₀ u + c 1 * F₁ u := by funext u; simp [Fin.sum_univ_two]
      rw [hsum2, hvan_up z.1 z.2]; rfl
    · dsimp [upperLeftEvalMap]
      have hsum2 : (fun u => ∑ i : Fin 2, c i * (![F₀, F₁] i) u) =
          fun u => c 0 * F₀ u + c 1 * F₁ u := by funext u; simp [Fin.sum_univ_two]
      rw [hsum2, hvan_up z.1 z.2]; rfl
  have hrank : Module.finrank ℝ (LinearMap.range Lmap) = Module.finrank ℝ (ℝ × ℝ) := by
    rw [← (LinearEquiv.ofInjective Lmap hinj_L).finrank_eq, Module.finrank_fin_fun ℝ,
      Module.finrank_prod, Module.finrank_self]
  have hsurj_L : Function.Surjective Lmap := by
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq hrank
  obtain ⟨c, hc⟩ := hsurj_L (w₀.re, w₀.im)
  refine ⟨(c 0, c 1), Complex.ext (congrArg Prod.fst hc) (congrArg Prod.snd hc), ?_⟩
  rintro ⟨s, t⟩ hst
  dsimp only at hst
  have hL_st : Lmap ![s, t] = (w₀.re, w₀.im) := by
    dsimp [Lmap]
    rw [hst]
  have hc_eq := hinj_L (hL_st.trans hc.symm)
  exact Prod.ext (congrFun hc_eq 0) (congrFun hc_eq 1)

/-- **Direct-sum Krein and beyond-the-wall decomposition of the energy domain (`E-Q6` + `E-Q1`).**
Under `HasSingleOffLineQuartet ρ₀`, for the two-rung ladder `(W₀, F₀), (R₂, F₁)`:
1. Every nonzero combination `s • F₀ + t • F₁` has strictly negative bare Weil energy `B < 0` and
   fails `HasBeyondTheWallPrimeContinuation`.
2. Every `G` in the energy domain decomposes with **unique** `(s, t) : ℝ × ℝ` as
   `G = (s • F₀ + t • F₁) + G_cont` where `G_cont` lies in the energy domain, satisfies
   `HasBeyondTheWallPrimeContinuation G_cont`, and has `0 ≤ bareMixedEnergy G_cont G_cont`. -/
theorem singleQuartet_directSum_primeContinuation {ρ₀ : ℂ} (hq : HasSingleOffLineQuartet ρ₀)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hne : R₁ ≠ R₂)
    {F₀ F₁ : ℝ → ℝ} (hF₀ : IsConfinedNullVector R₁ F₀) (hF₁ : IsConfinedNullVector R₂ F₁) :
    (∀ s t : ℝ, (s, t) ≠ (0, 0) →
      bareMixedEnergy (fun u => s * F₀ u + t * F₁ u) (fun u => s * F₀ u + t * F₁ u) < 0 ∧
        ¬ HasBeyondTheWallPrimeContinuation (fun u => s * F₀ u + t * F₁ u)) ∧
    (∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
      ∃! st : ℝ × ℝ,
        let G_cont : ℝ → ℝ := fun u => G u - (st.1 * F₀ u + st.2 * F₁ u)
        CriticalHalfLineEnergyDomain G_cont ∧
        HasBeyondTheWallPrimeContinuation G_cont ∧
        0 ≤ bareMixedEnergy G_cont G_cont) := by
  constructor
  · intro s t hst
    set H : ℝ → ℝ := fun u => s * F₀ u + t * F₁ u
    have hH_dom : CriticalHalfLineEnergyDomain H := (hF₀.1.const_mul s).add_const_mul hF₁.1 t
    have hnot_cont : ¬ HasBeyondTheWallPrimeContinuation H := by
      intro hcont
      have h0 := (singleQuartet_hasBeyondTheWallPrimeContinuation_iff hq hH_dom).mp hcont
      obtain ⟨_, _, huniq⟩ := singleQuartet_leftPair_isolator_isomorphism hq hR₁ hR₂ hne hF₀ hF₁ 0
      have hzero : negativeHalfLineLaplace (cx fun u => (0 : ℝ) * F₀ u + (0 : ℝ) * F₁ u)
          (1 / 2 - conj ρ₀) = 0 := by
        simp [cx, negativeHalfLineLaplace]
      exact hst (huniq (s, t) h0 |>.trans (huniq (0, 0) hzero).symm)
    have hbare_neg : bareMixedEnergy H H < 0 := by
      have horth := confinedNullVectors_orthogonal hR₁ hR₂ hne hF₀ hF₁
      have hR_comb := criticalHalfLineFullEnergy_combination 1 hF₀.1 hF₁.1 s t
      have hfull_eq : ∀ G : ℝ → ℝ, CriticalHalfLineEnergyDomain G →
          criticalHalfLineFullEnergy 1 G =
            bareMixedEnergy G G + criticalAliasCoefficient 1 * w8Mass G := by
        intro G hG
        have h1 := criticalHalfLineFullEnergy_add_const_mul 1 hG hG 1
        have hfun : (fun u => G u + 1 * G u) = fun u => (2 : ℝ) * G u := by funext u; ring
        rw [hfun, criticalHalfLineFullEnergy_const_mul] at h1
        have hmix : criticalHalfLineMixedEnergy 1 G G = criticalHalfLineFullEnergy 1 G := by linarith
        rw [← hmix, criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hG.support,
          w8Pair_self]
      have hmix_01 : criticalHalfLineMixedEnergy 1 F₀ F₁ = 0 := by
        rw [criticalHalfLineMixedEnergy_eq_bare_add, horth.1, horth.2, mul_zero, add_zero]
      have hw_H : w8Mass H = s ^ 2 * w8Mass F₀ + t ^ 2 * w8Mass F₁ := by
        have horth_w8 : w8Pair F₀ F₁ = 0 := by
          have h := horth.1; rwa [setIntegral_Iio_w8_eq' hF₀.1.support] at h
        have h1 := w8Mass_add_const_mul (isW8Target_const_mul (isW8Target_of_domain hF₀.1) s)
          (isW8Target_of_domain hF₁.1) t
        have hw_s : w8Mass (fun u => s * F₀ u) = s ^ 2 * w8Mass F₀ := by
          unfold w8Mass
          have hf : (fun u => (s * F₀ u) ^ 2 * Real.exp (-(8 * u))) =
              fun u => s ^ 2 * (F₀ u ^ 2 * Real.exp (-(8 * u))) := by funext u; ring
          rw [hf, integral_const_mul]
        rw [hw_s, w8Pair_const_mul_left, horth_w8, mul_zero, mul_zero] at h1
        exact h1.trans (by ring)
      have hb₀ : bareMixedEnergy F₀ F₀ = -criticalAliasCoefficient R₁ * w8Mass F₀ := by
        have h := hF₀.2.2 F₀ hF₀.1
        rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hF₀.1.support,
          w8Pair_self] at h
        linarith
      have hb₁ : bareMixedEnergy F₁ F₁ = -criticalAliasCoefficient R₂ * w8Mass F₁ := by
        have h := hF₁.2.2 F₁ hF₁.1
        rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_Iio_w8_eq' hF₁.1.support,
          w8Pair_self] at h
        linarith
      change criticalHalfLineFullEnergy 1 H = _ at hR_comb
      rw [hfull_eq H hH_dom, hfull_eq F₀ hF₀.1, hfull_eq F₁ hF₁.1, hmix_01, hw_H, hb₀, hb₁] at hR_comb
      have hbare_H : bareMixedEnergy H H =
          -(s ^ 2 * criticalAliasCoefficient R₁ * w8Mass F₀ +
            t ^ 2 * criticalAliasCoefficient R₂ * w8Mass F₁) := by linarith
      rw [hbare_H]
      have ha₁ := criticalAliasCoefficient_positive hR₁
      have ha₂ := criticalAliasCoefficient_positive hR₂
      have hw₀ := nullVector_confinementMass_pos hF₀
      have hw₁ := nullVector_confinementMass_pos hF₁
      by_cases hs : s = 0
      · have ht0 : t ≠ 0 := fun ht0 => hst (Prod.ext hs ht0)
        subst hs
        have hpos : 0 < t ^ 2 * criticalAliasCoefficient R₂ * w8Mass F₁ :=
          mul_pos (mul_pos (sq_pos_of_ne_zero ht0) ha₂) hw₁
        linarith
      · have hpos : 0 < s ^ 2 * criticalAliasCoefficient R₁ * w8Mass F₀ :=
          mul_pos (mul_pos (sq_pos_of_ne_zero hs) ha₁) hw₀
        have hnn : 0 ≤ t ^ 2 * criticalAliasCoefficient R₂ * w8Mass F₁ := by positivity
        linarith
    exact ⟨hbare_neg, hnot_cont⟩
  · intro G hG
    set w₀ := negativeHalfLineLaplace (cx G) (1 / 2 - conj ρ₀)
    obtain ⟨st, hst_eq, hst_uniq⟩ :=
      singleQuartet_leftPair_isolator_isomorphism hq hR₁ hR₂ hne hF₀ hF₁ w₀
    have hw : -4 < (1 / 2 - conj ρ₀).re := by simp; linarith [hq.re_lt_one]
    refine ⟨st, ?_, ?_⟩
    · dsimp only
      set P : ℝ → ℝ := fun u => st.1 * F₀ u + st.2 * F₁ u
      have hP_dom : CriticalHalfLineEnergyDomain P := (hF₀.1.const_mul st.1).add_const_mul hF₁.1 st.2
      have hsub_eq : (fun u => G u - (st.1 * F₀ u + st.2 * F₁ u)) =
          fun u => G u + (-1) * P u := by funext u; dsimp [P]; ring
      have hcont_dom : CriticalHalfLineEnergyDomain (fun u => G u - (st.1 * F₀ u + st.2 * F₁ u)) := by
        rw [hsub_eq]; exact hG.add_const_mul hP_dom (-1)
      have hcont : HasBeyondTheWallPrimeContinuation
          (fun u => G u - (st.1 * F₀ u + st.2 * F₁ u)) := by
        rw [singleQuartet_hasBeyondTheWallPrimeContinuation_iff hq hcont_dom, hsub_eq,
          laplace_cx_add hG (hP_dom.const_mul (-1)) hw, laplace_cx_const_mul, hst_eq]
        push_cast; ring
      exact ⟨hcont_dom, hcont,
        (bareMixedEnergy_nonneg_of_hasBeyondTheWallPrimeContinuation hcont_dom hq.finiteOffLine
          hcont).2⟩
    · rintro ⟨s, t⟩ ⟨hdom', hcont', -⟩
      apply hst_uniq (s, t)
      have h0 := (singleQuartet_hasBeyondTheWallPrimeContinuation_iff hq hdom').mp hcont'
      set P : ℝ → ℝ := fun u => s * F₀ u + t * F₁ u
      have hP_dom : CriticalHalfLineEnergyDomain P := (hF₀.1.const_mul s).add_const_mul hF₁.1 t
      have hsub_eq : (fun u => G u - (s * F₀ u + t * F₁ u)) = fun u => G u + (-1) * P u := by
        funext u; dsimp [P]; ring
      rw [hsub_eq, laplace_cx_add hG (hP_dom.const_mul (-1)) hw, laplace_cx_const_mul] at h0
      push_cast at h0
      linear_combination -h0

/-- **Existence of a pole-neutral ladder state whose bare `primeHead` fails continuation.**
Under `HasSingleOffLineQuartet ρ₀`, some nonzero combination `Hstar = s • F₀ + t • F₁` has vanishing
`ζ(1)` pole residue `L Hstar(-½) = 0`, yet `primeHead Hstar` fails holomorphic continuation to `Re p < 0`. -/
theorem singleQuartet_exists_poleNeutral_no_primeHeadContinuation {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hne : R₁ ≠ R₂)
    {F₀ F₁ : ℝ → ℝ} (hF₀ : IsConfinedNullVector R₁ F₀) (hF₁ : IsConfinedNullVector R₂ F₁) :
    ∃ s t : ℝ, (s, t) ≠ (0, 0) ∧
      negativeHalfLineLaplace (cx fun u => s * F₀ u + t * F₁ u) (-(1 / 2)) = 0 ∧
      ¬ (∃ H : ℂ → ℂ, DifferentiableOn ℂ H {p : ℂ | p.re < 0} ∧
          EqOn H (primeHead fun u => s * F₀ u + t * F₁ u) {p : ℂ | p.re < -(1 / 2)}) := by
  have hreal_pole : ∀ G : ℝ → ℝ,
      negativeHalfLineLaplace (cx G) (-(1 / 2)) =
        (((negativeHalfLineLaplace (cx G) (-(1 / 2))).re : ℝ) : ℂ) := by
    intro G
    have hc : conj (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
      apply Complex.ext <;> norm_num
    have hr : negativeHalfLineLaplace (cx G) (conj (-(1 / 2))) =
        conj (negativeHalfLineLaplace (cx G) (-(1 / 2))) :=
      negativeHalfLineLaplace_real_conj G (-(1 / 2))
    rw [hc] at hr
    have him0 : (negativeHalfLineLaplace (cx G) (-(1 / 2))).im = 0 :=
      Complex.conj_eq_iff_im.mp hr.symm
    exact Complex.ext (Complex.ofReal_re _).symm (him0.trans (Complex.ofReal_im _).symm)
  set r₀ : ℝ := (negativeHalfLineLaplace (cx F₀) (-(1 / 2))).re
  set r₁ : ℝ := (negativeHalfLineLaplace (cx F₁) (-(1 / 2))).re
  have hex : ∃ s t : ℝ, (s, t) ≠ (0, 0) ∧ s * r₀ + t * r₁ = 0 := by
    by_cases h0 : r₀ = 0 ∧ r₁ = 0
    · exact ⟨1, 0, by simp, by rw [h0.1, h0.2]; ring⟩
    · refine ⟨r₁, -r₀, fun he => h0 ?_, by ring⟩
      simp only [Prod.mk.injEq, neg_eq_zero] at he
      exact ⟨he.2, he.1⟩
  obtain ⟨s, t, hst, hlin⟩ := hex
  set Hstar : ℝ → ℝ := fun u => s * F₀ u + t * F₁ u
  have hH_dom : CriticalHalfLineEnergyDomain Hstar := (hF₀.1.const_mul s).add_const_mul hF₁.1 t
  have hpole : negativeHalfLineLaplace (cx Hstar) (-(1 / 2)) = 0 := by
    dsimp [Hstar]
    rw [laplace_cx_add (hF₀.1.const_mul s) (hF₁.1.const_mul t) (by norm_num : (-4 : ℝ) < (-(1 / 2 : ℂ)).re),
      laplace_cx_const_mul, laplace_cx_const_mul, hreal_pole F₀, hreal_pole F₁]
    exact_mod_cast hlin
  refine ⟨s, t, hst, hpole, ?_⟩
  rw [purePrimeHeadContinuation_profile_iff_vanish_leftZeros hH_dom hpole,
    ← hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros hH_dom]
  exact ((singleQuartet_directSum_primeContinuation hq hR₁ hR₂ hne hF₀ hF₁).1 s t hst).2

/-! ### 5. Two-rung wall laws, prime/PNT form of `F⁺`, `averagedState`, and single-wave `ψ(x) - x` -/

/-- **Two-rung wall laws and beyond-the-wall prime/PNT representations.**
Packages for the two ladder states `(W₀, F₀)` and `(R₂, F₁)`:
1. Diagonal wall laws for `F₀⁺` and `F₁⁺`;
2. Cross-rung wall laws coupling `(W₀, F₀)` and `(R₂, F₁)`;
3. Almost-everywhere prime series and averaged PNT remainder representations of `F₀⁺` and `F₁⁺`. -/
theorem singleQuartet_twoRung_wall_and_primeForm
    {W₀ R₂ : ℝ} (hW : 0 < W₀) (hR₂ : 0 < R₂)
    {F₀ F₁ : ℝ → ℝ} (hF₀ : IsConfinedNullVector W₀ F₀) (hF₁ : IsConfinedNullVector R₂ F₁) :
    (∀ {k : ℝ}, 0 ≤ k →
      beyondWallPairing W₀ hF₀.1 (cx fun x => F₀ (x - k)) =
        -((1 - Real.exp (-(8 * k)) : ℝ) : ℂ) *
          ((∫ u : ℝ, F₀ (u + k) * F₀ u * Real.exp (-(8 * u)) : ℝ) : ℂ) ∧
      beyondWallPairing R₂ hF₁.1 (cx fun x => F₁ (x - k)) =
        -((1 - Real.exp (-(8 * k)) : ℝ) : ℂ) *
          ((∫ u : ℝ, F₁ (u + k) * F₁ u * Real.exp (-(8 * u)) : ℝ) : ℂ) ∧
      (criticalAliasCoefficient W₀ : ℂ) * beyondWallPairing W₀ hF₀.1 (cx fun x => F₁ (x - k)) =
        ((criticalAliasCoefficient W₀ * Real.exp (-(8 * k)) -
            criticalAliasCoefficient R₂ : ℝ) : ℂ) *
          ((∫ u : ℝ, F₀ (u + k) * F₁ u * Real.exp (-(8 * u)) : ℝ) : ℂ) ∧
      (criticalAliasCoefficient R₂ : ℂ) * beyondWallPairing R₂ hF₁.1 (cx fun x => F₀ (x - k)) =
        ((criticalAliasCoefficient R₂ * Real.exp (-(8 * k)) -
            criticalAliasCoefficient W₀ : ℝ) : ℂ) *
          ((∫ u : ℝ, F₁ (u + k) * F₀ u * Real.exp (-(8 * u)) : ℝ) : ℂ)) ∧
    (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      Summable (fun n : ℕ => (primeAtom n : ℂ) * (F₀ (x - Real.log n) : ℂ)) ∧
      -(criticalAliasCoefficient W₀ : ℂ) * beyondWallProfile W₀ hF₀.1 x =
        levyHeadProfile F₀ x - negativeHalfLineLaplace (cx F₀) (1 / 2) * (Real.exp (-(x / 2)) : ℂ) +
          ((∑' n : ℕ, (primeAtom n : ℂ) * (F₀ (x - Real.log n) : ℂ)) -
            ∫ y in Ioi x, (F₀ (x - y) : ℂ) * (Real.exp (y / 2) : ℂ))) ∧
    (∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
      Summable (fun n : ℕ => (primeAtom n : ℂ) * (F₁ (x - Real.log n) : ℂ)) ∧
      -(criticalAliasCoefficient R₂ : ℂ) * beyondWallProfile R₂ hF₁.1 x =
        levyHeadProfile F₁ x - negativeHalfLineLaplace (cx F₁) (1 / 2) * (Real.exp (-(x / 2)) : ℂ) +
          ((∑' n : ℕ, (primeAtom n : ℂ) * (F₁ (x - Real.log n) : ℂ)) -
            ∫ y in Ioi x, (F₁ (x - y) : ℂ) * (Real.exp (y / 2) : ℂ))) := by
  refine ⟨fun hk => ⟨nullVector_diagonalWallLaw hW hF₀ hk,
      nullVector_diagonalWallLaw hR₂ hF₁ hk,
      nullVector_crossWallLaw hW hF₀ hF₁ hk,
      nullVector_crossWallLaw hR₂ hF₁ hF₀ hk⟩, ?_, ?_⟩
  · filter_upwards [beyondWallProfile_primeForm hW hF₀.1, beyondWallProfile_pntForm hW hF₀.1]
      with x hp hpnt
    exact ⟨hp.1, hpnt⟩
  · filter_upwards [beyondWallProfile_primeForm hR₂ hF₁.1, beyondWallProfile_pntForm hR₂ hF₁.1]
      with x hp hpnt
    exact ⟨hp.1, hpnt⟩

/-- **Under a single off-line quartet, `averagedState F₀` equals one conjugate mode pair up to
`O(e^{-8t})`.** -/
theorem singleQuartet_averagedState_singleConjugatePair {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F₀ : ℝ → ℝ} (hF₀ : IsCriticalHalfLineGroundState W₀ F₀) :
    let zPos : ℂ := ρ₀ - 1 / 2
    let cPos : ℂ := -(criticalAliasCoefficient W₀ : ℂ)⁻¹ *
      negativeHalfLineLaplace (cx F₀) zPos * averageSymbol (zPos - 8)
    ∃ K : ℝ, ∀ t : ℝ, 0 < t →
      |averagedState F₀ t -
          2 * (quartetCopyMult ρ₀ : ℝ) * (cPos * Complex.exp ((zPos - 8) * (t : ℂ))).re| ≤
        K * Real.exp (-(8 * t)) := by
  intro zPos cPos
  have hfin_right : Set.Finite {q : XiZeroCopy | 0 < (centredZero q).re} :=
    hq.finiteOffLine_copies.subset fun q hpos => by
      change 0 < (centredZero q).re at hpos
      change (q.1 : ℂ).re ≠ 1 / 2
      rw [centredZero, Complex.sub_re] at hpos
      norm_num at hpos
      linarith
  obtain ⟨K, hK⟩ := criticalState_averagedState_finiteLayer hW ht hF₀ hfin_right
  refine ⟨K, fun t ht_pos => ?_⟩
  have hsum_eq : ∑ q ∈ hfin_right.toFinset,
      zeroModeCoeff W₀ F₀ q * Complex.exp ((centredZero q - 8) * (t : ℂ)) =
      ∑ q ∈ offLineCopyFinset hq.finiteOffLine,
        if 0 < (centredZero q).re then
          zeroModeCoeff W₀ F₀ q * Complex.exp ((centredZero q - 8) * (t : ℂ)) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext q
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_offLineCopyFinset]
    exact ⟨fun h => ⟨h.ne', h⟩, fun h => h.2⟩
  let g : ℂ → ℂ := fun ρ =>
    if 0 < (ρ - 1 / 2).re then
      (-(criticalAliasCoefficient W₀ : ℂ)⁻¹ *
        negativeHalfLineLaplace (cx F₀) (ρ - 1 / 2) * averageSymbol (ρ - 1 / 2 - 8)) *
        Complex.exp ((ρ - 1 / 2 - 8) * (t : ℂ))
    else 0
  have hsum_g : (∑ q ∈ offLineCopyFinset hq.finiteOffLine,
      if 0 < (centredZero q).re then
        zeroModeCoeff W₀ F₀ q * Complex.exp ((centredZero q - 8) * (t : ℂ)) else 0) =
      ∑ q ∈ offLineCopyFinset hq.finiteOffLine, g (q.1 : ℂ) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [g, zeroModeCoeff, centredZero]
  have hg_pos1 : g ρ₀ = cPos * Complex.exp ((zPos - 8) * (t : ℂ)) := by
    dsimp [g, cPos, zPos]
    rw [if_pos (by simp; linarith [hq.1])]
  have hg_pos2 : g (conj ρ₀) = conj (cPos * Complex.exp ((zPos - 8) * (t : ℂ))) := by
    dsimp [g, cPos, zPos]
    rw [if_pos (by simp; linarith [hq.1])]
    have hc_z : conj ρ₀ - 1 / 2 = conj (ρ₀ - 1 / 2) := by apply Complex.ext <;> simp
    have hc_8 : conj ρ₀ - 1 / 2 - 8 = conj (ρ₀ - 1 / 2 - 8) := by apply Complex.ext <;> simp
    have hc_t : (conj ρ₀ - 1 / 2 - 8) * (t : ℂ) = conj ((ρ₀ - 1 / 2 - 8) * (t : ℂ)) := by
      apply Complex.ext <;> simp
    have havg_conj : ∀ w : ℂ, averageSymbol (conj w) = conj (averageSymbol w) := fun w => by
      unfold averageSymbol
      simp only [map_inv₀, map_mul, map_add, map_ofNat]
    rw [hc_t, hc_8, hc_z, show cx F₀ = fun u => (F₀ u : ℂ) from rfl,
      negativeHalfLineLaplace_real_conj, havg_conj, Complex.exp_conj]
    simp
  have hg_neg1 : g (1 - ρ₀) = 0 := by
    dsimp [g]; rw [if_neg (by simp; linarith [hq.1])]
  have hg_neg2 : g (1 - conj ρ₀) = 0 := by
    dsimp [g]; rw [if_neg (by simp; linarith [hq.1])]
  have hval : ∑ q ∈ hfin_right.toFinset,
      zeroModeCoeff W₀ F₀ q * Complex.exp ((centredZero q - 8) * (t : ℂ)) =
      ((2 * (quartetCopyMult ρ₀ : ℝ) *
        (cPos * Complex.exp ((zPos - 8) * (t : ℂ))).re : ℝ) : ℂ) := by
    rw [hsum_eq, hsum_g, sum_offLineCopyFinset_of_singleQuartet hq g,
      hg_pos1, hg_pos2, hg_neg1, hg_neg2, add_zero, add_zero]
    set M := cPos * Complex.exp ((zPos - 8) * (t : ℂ))
    have hre : M + conj M = ((2 * M.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [two_mul]
    rw [hre]
    push_cast; ring
  have hbound := hK t ht_pos
  rw [hval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hbound
  exact hbound

private theorem cpow_ofReal_pos_conj {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ (conj w) = conj ((x : ℂ) ^ w) := by
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx_ne, Complex.cpow_def_of_ne_zero hx_ne,
    ← Complex.ofReal_log hx.le, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

/-- **Exact Chebyshev single-wave characterization of `HasSingleOffLineQuartet`.**
For any strip zero `ρ₀` of `ζ` with `1/2 < Re ρ₀`, `ζ` has `Q(ρ₀)` as its unique off-line quartet if
and only if `ψ(x) - x = -2 m Re(x^{ρ₀}/ρ₀) + O(√x log² x)` for `x ≥ 16`. -/
theorem hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave {ρ₀ : ℂ}
    (hre : 1 / 2 < ρ₀.re) (hmem : ρ₀ ∈ zetaZeroConfig.carrier) :
    HasSingleOffLineQuartet ρ₀ ↔
      ∃ K : ℝ, ∀ x : ℝ, 16 ≤ x →
        |Chebyshev.psi x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re| ≤
          K * Real.sqrt x * Real.log x ^ 2 := by
  have hxi₀ : xi ρ₀ = 0 := by
    obtain ⟨hζ, h0, h1⟩ := hmem
    have hne1 : ρ₀ ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
    exact (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos h0 hne1).mpr hζ
  have him_ne : ρ₀.im ≠ 0 := by
    obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi₀
    have h := four_lt_abs_zeroOrdinate q
    rw [zeroOrdinate, hq_eq] at h
    intro h0; rw [h0, abs_zero] at h; linarith
  constructor
  · intro hq
    set S := offLineCopyFinset hq.finiteOffLine
    set K₀ : ℝ := 200 * (xiLineTwoLogDerivConstant + 2) + 4 * S.card
    have h1_sub_ne : (1 : ℂ) - ρ₀ ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hq.re_lt_one]
    have h1_norm_pos : 0 < ‖(1 : ℂ) - ρ₀‖ := norm_pos_iff.mpr h1_sub_ne
    refine ⟨K₀ + 2 * (quartetCopyMult ρ₀ : ℝ) / ‖(1 : ℂ) - ρ₀‖, fun x hx => ?_⟩
    have hx_pos : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hvk := abs_chebyshevPsi_sub_add_offLineWave_le (S := S)
      (fun q hq_ne => mem_offLineCopyFinset.mpr (by
        rw [centredZero, Complex.sub_re]; norm_num; intro h; apply hq_ne; linarith)) hx
    have hwave : offLineWave S x =
        (quartetCopyMult ρ₀ : ℂ) *
          ((x : ℂ) ^ ρ₀ / ρ₀ + (x : ℂ) ^ (conj ρ₀) / (conj ρ₀) +
            (x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀) + (x : ℂ) ^ (1 - conj ρ₀) / (1 - conj ρ₀)) := by
      unfold offLineWave
      exact sum_offLineCopyFinset_of_singleQuartet hq (fun ρ => (x : ℂ) ^ ρ / ρ)
    have hconj1 : (x : ℂ) ^ (conj ρ₀) / (conj ρ₀) = conj ((x : ℂ) ^ ρ₀ / ρ₀) := by
      rw [cpow_ofReal_pos_conj hx_pos, map_div₀]
    have hconj2 : (x : ℂ) ^ (1 - conj ρ₀) / (1 - conj ρ₀) =
        conj ((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)) := by
      have hc : (1 : ℂ) - conj ρ₀ = conj (1 - ρ₀) := by apply Complex.ext <;> simp
      rw [hc, cpow_ofReal_pos_conj hx_pos, map_div₀]
    have hre_wave : (offLineWave S x).re =
        2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re +
          2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)).re := by
      rw [hwave, hconj1, hconj2]
      simp only [Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.natCast_re,
        Complex.natCast_im, zero_mul, sub_zero]
      ring
    have hleft_le : |2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)).re| ≤
        (2 * (quartetCopyMult ρ₀ : ℝ) / ‖(1 : ℂ) - ρ₀‖) * Real.sqrt x * Real.log x ^ 2 := by
      have hcpow_le : ‖(x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)‖ ≤ Real.sqrt x / ‖(1 : ℂ) - ρ₀‖ := by
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx_pos, Real.sqrt_eq_rpow]
        refine div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1 ?_) h1_norm_pos.le
        simp; linarith
      have hre_le : |((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)).re| ≤ Real.sqrt x / ‖(1 : ℂ) - ρ₀‖ :=
        (Complex.abs_re_le_norm _).trans hcpow_le
      have hlog2 : 1 ≤ Real.log x ^ 2 := by
        have h2 := two_le_log_of_sixteen_le hx
        nlinarith
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (quartetCopyMult ρ₀ : ℝ))]
      calc 2 * (quartetCopyMult ρ₀ : ℝ) * |((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)).re|
          ≤ 2 * (quartetCopyMult ρ₀ : ℝ) * (Real.sqrt x / ‖(1 : ℂ) - ρ₀‖) :=
            mul_le_mul_of_nonneg_left hre_le (by positivity)
        _ = ((2 * (quartetCopyMult ρ₀ : ℝ) / ‖(1 : ℂ) - ρ₀‖) * Real.sqrt x) * 1 := by ring
        _ ≤ ((2 * (quartetCopyMult ρ₀ : ℝ) / ‖(1 : ℂ) - ρ₀‖) * Real.sqrt x) * Real.log x ^ 2 :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = (2 * (quartetCopyMult ρ₀ : ℝ) / ‖(1 : ℂ) - ρ₀‖) * Real.sqrt x * Real.log x ^ 2 := by
            ring
    have hsplit : Chebyshev.psi x - x + 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re =
        (Chebyshev.psi x - x + (offLineWave S x).re) -
          2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)).re := by
      rw [hre_wave]; ring
    rw [hsplit]
    calc |(Chebyshev.psi x - x + (offLineWave S x).re) -
            2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)).re|
        ≤ |Chebyshev.psi x - x + (offLineWave S x).re| +
            |2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ (1 - ρ₀) / (1 - ρ₀)).re| := abs_sub _ _
      _ ≤ K₀ * Real.sqrt x * Real.log x ^ 2 +
            (2 * (quartetCopyMult ρ₀ : ℝ) / ‖(1 : ℂ) - ρ₀‖) * Real.sqrt x * Real.log x ^ 2 :=
          add_le_add hvk hleft_le
      _ = (K₀ + 2 * (quartetCopyMult ρ₀ : ℝ) / ‖(1 : ℂ) - ρ₀‖) *
            Real.sqrt x * Real.log x ^ 2 := by ring
  · rintro ⟨K, hK⟩
    classical
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi₀
    have hsupp₀ : ρ₀ ∈ (MeromorphicOn.divisor xi Set.univ).support := hq₀ ▸ q₀.1.2
    have hxi_c : xi (conj ρ₀) = 0 := (xi_quartet_eq_zero hxi₀).1
    obtain ⟨qc, hqc⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi_c
    have hsuppc : conj ρ₀ ∈ (MeromorphicOn.divisor xi Set.univ).support := hqc ▸ qc.1.2
    let ρ_s₀ : XiDivisorSupport := ⟨ρ₀, hsupp₀⟩
    let ρ_sc : XiDivisorSupport := ⟨conj ρ₀, hsuppc⟩
    let S₀ : Finset XiZeroCopy :=
      (Finset.univ : Finset (Fin (((MeromorphicOn.divisor xi Set.univ) ρ₀).toNat))).image
        fun k => (⟨ρ_s₀, k⟩ : XiZeroCopy)
    let Sc : Finset XiZeroCopy :=
      (Finset.univ : Finset (Fin (((MeromorphicOn.divisor xi Set.univ) (conj ρ₀)).toNat))).image
        fun k => (⟨ρ_sc, k⟩ : XiZeroCopy)
    have hne_conj : ρ₀ ≠ conj ρ₀ := (quartet_points_pairwise_ne hre him_ne).1
    have hdisj : Disjoint S₀ Sc := by
      rw [Finset.disjoint_left]
      intro q hqS₀ hqSc
      obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp hqS₀
      obtain ⟨_, -, heq⟩ := Finset.mem_image.mp hqSc
      exact hne_conj (congrArg Subtype.val (Sigma.mk.inj_iff.mp heq).1).symm
    let S_pair : Finset XiZeroCopy := S₀ ∪ Sc
    have hwave_re : ∀ x : ℝ, 16 ≤ x →
        (offLineWave S_pair x).re = 2 * (quartetCopyMult ρ₀ : ℝ) * ((x : ℂ) ^ ρ₀ / ρ₀).re := by
      intro x hx
      have hx_pos : 0 < x := by linarith
      unfold offLineWave
      rw [Finset.sum_union hdisj,
        Finset.sum_image (fun a _ b _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2),
        Finset.sum_image (fun a _ b _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (((quartetCopyMult ρ₀ : ℂ) * ((x : ℂ) ^ ρ₀ / ρ₀) +
        (quartetCopyMult (conj ρ₀) : ℂ) * ((x : ℂ) ^ (conj ρ₀) / (conj ρ₀)))).re = _
      rw [quartetCopyMult_conj, cpow_ofReal_pos_conj hx_pos, ← map_div₀]
      simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.natCast_re,
        Complex.natCast_im, zero_mul, sub_zero]
      ring
    have hK_pair : ∀ x : ℝ, 16 ≤ x →
        |Chebyshev.psi x - x + (offLineWave S_pair x).re| ≤
          K * Real.sqrt x * Real.log x ^ 2 := by
      intro x hx
      rw [hwave_re x hx]
      exact hK x hx
    have hpoles_sub : ∀ w ∈ offLinePoles S_pair, w = ρ₀ - 1 / 2 ∨ w = conj ρ₀ - 1 / 2 := by
      intro w hw
      have hmem_pair : ∀ q ∈ S_pair, (q.1 : ℂ) = ρ₀ ∨ (q.1 : ℂ) = conj ρ₀ := by
        intro q hq_mem
        rcases Finset.mem_union.mp hq_mem with h0 | hc
        · obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp h0; exact Or.inl rfl
        · obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp hc; exact Or.inr rfl
      rcases hw with ⟨q, hq_mem, rfl⟩ | ⟨q, hq_mem, rfl⟩
      · rcases hmem_pair q hq_mem with h1 | h2
        · left; simp [lagPole, h1]
        · right; simp [lagPole, h2]
      · rcases hmem_pair q hq_mem with h1 | h2
        · right; dsimp only; unfold lagPole; rw [h1]; apply Complex.ext <;> simp
        · left; dsimp only; unfold lagPole; rw [h2]; apply Complex.ext <;> simp
    have hmem_of_xi : ∀ {z : ℂ}, xi z = 0 → z ∈ zetaZeroConfig.carrier := by
      intro z hxi
      obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
      rw [← hq_eq]
      exact xiZeroCopy_mem_zetaZeroConfig q
    refine ⟨hre, hmem, ?_⟩
    ext ρ
    simp only [Set.mem_setOf_eq, zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hρ_mem, hρ_ne⟩
      have hright_case : ∀ {z : ℂ}, z ∈ zetaZeroConfig.carrier → 1 / 2 < z.re →
          z = ρ₀ ∨ z = conj ρ₀ := by
        intro z hz_mem hz_gt
        obtain ⟨hζ, hz0, hz1⟩ := hz_mem
        have hne1 : z ≠ 1 := fun h => by rw [h] at hz1; norm_num at hz1
        have hxi_z := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hz0 hne1).mpr hζ
        obtain ⟨q, hq_eq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi_z
        have hq_pole : lagPole q ∈ offLinePoles S_pair := by
          by_contra hnot
          have hle := re_le_half_of_abs_chebyshevPsi_sub_add_offLineWave_le S_pair hK_pair q hnot
          rw [hq_eq] at hle
          linarith
        rcases hpoles_sub (lagPole q) hq_pole with hp1 | hp2
        · left; unfold lagPole at hp1; rw [hq_eq] at hp1; linear_combination hp1
        · right; unfold lagPole at hp2; rw [hq_eq] at hp2; linear_combination hp2
      rcases lt_or_gt_of_ne hρ_ne with hlt | hgt
      · obtain ⟨hζ_ρ, hρ0, hρ1⟩ := hρ_mem
        have hne1_ρ : ρ ≠ 1 := fun h => by rw [h] at hρ1; norm_num at hρ1
        have hxi_ρ := (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos hρ0 hne1_ρ).mpr hζ_ρ
        have hrefl : 1 - ρ ∈ zetaZeroConfig.carrier :=
          hmem_of_xi (by rw [xi_one_sub]; exact hxi_ρ)
        have hrefl_gt : 1 / 2 < (1 - ρ).re := by simp; linarith
        rcases hright_case hrefl hrefl_gt with h1 | h2
        · right; right; left; linear_combination -h1
        · right; right; right; linear_combination -h2
      · rcases hright_case hρ_mem hgt with h1 | h2
        · left; exact h1
        · right; left; exact h2
    · obtain ⟨hxi_c, hxi_r, hxi_rc⟩ := xi_quartet_eq_zero hxi₀
      rintro (rfl | rfl | rfl | rfl)
      · exact ⟨hmem, by linarith⟩
      · exact ⟨hmem_of_xi hxi_c, by simp; linarith⟩
      · exact ⟨hmem_of_xi hxi_r, by simp; linarith⟩
      · exact ⟨hmem_of_xi hxi_rc, by simp; linarith⟩

/-! ### 6. Global `E-Q1` equivalence and single-quartet model separation -/

/-- **Complete global and profile-by-profile solution of `E-Q1`.**
1. Globally across all profiles in the half-line energy domain, `ZetaBeyondTheWallPrimeContinuation`
   (`∀ F ∈ H, Φ_F continues to Re p < 0`) is unconditionally equivalent both to
   `PurePrimeHeadContinuation` and to `RiemannHypothesis`.
2. Individually for each profile `F ∈ H`, `HasBeyondTheWallPrimeContinuation F` holds if and only if
   `L F(z) = 0` at every left-of-line centred zero `z` of `ζ` (`Re z < 0`). -/
theorem eq1_global_and_profile_synthesis :
    (ZetaBeyondTheWallPrimeContinuation ↔ RiemannHypothesis) ∧
    (PurePrimeHeadContinuation ↔ RiemannHypothesis) ∧
    (∀ {F : ℝ → ℝ}, CriticalHalfLineEnergyDomain F →
      (HasBeyondTheWallPrimeContinuation F ↔
        ∀ q : XiZeroCopy, (centredZero q).re < 0 →
          negativeHalfLineLaplace (cx F) (centredZero q) = 0)) :=
  ⟨zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis,
    purePrimeHeadContinuation_iff_zetaBeyondTheWallPrimeContinuation.trans
      zetaBeyondTheWallPrimeContinuation_iff_riemannHypothesis,
    fun hF => hasBeyondTheWallPrimeContinuation_iff_vanish_leftZeros hF⟩

/-- **Single-quartet model realization vs. Beurling–Lévy joint rigidity (`E-Q6` arithmetic boundary).**
1. Every two-sided rational-prime edit at `β > 1/2` realizes an integer-norm Beurling system whose
   fake off-line zeros right of the line are **one** non-real conjugate pair `{ρ, conj ρ}` with no
   real zero in `(1/2, ∞)` (`exists_isEdit_fake_without_real_zero`), and the abstract quartet
   `quartetConfig ρ` carries a confined critical state (`ModelStates.quartet_criticalState`).
2. Adjoining **both** a nonnegative Beurling prime system (`Λ_B ≥ 0`) **and** the `Γ_ℝ` functional
   equation up to `L²` strip defect uniquely forces `ζ_B = ζ` (`beurling_levy_rigidity_forces_zeta`). -/
theorem singleQuartet_realized_in_models {β : ℝ} (hβ : 1 / 2 < β) :
    (∃ (e : ℕ → ℤ) (ρ : ℂ),
      WorldsOfTheZeroConfiguration.TwoSidedEdits.IsEdit e ∧
      ρ.im ≠ 0 ∧ 1 / 2 < ρ.re ∧
      SumProductArithmeticOfTheLogarithm.IsIntegerNormFakeAt
        (WorldsOfTheZeroConfiguration.TwoSidedEdits.editSystem e) β ∧
      WorldsOfTheZeroConfiguration.HasFakeZeroSet
        (WorldsOfTheZeroConfiguration.TwoSidedEdits.editSystem e)
        {ρ, (starRingEnd ℂ) ρ} ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
        (∀ s : ℂ, 1 < s.re → G s =
          (s - 1) * (WorldsOfTheZeroConfiguration.TwoSidedEdits.editSystem e).zetaSeriesC s) ∧
        ∀ x : ℝ, 1 / 2 < x → G (x : ℂ) ≠ 0) ∧
    (∀ {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1), ρ.re ≠ 1 / 2 →
      ∃ hfin : (ModelStates.offLineSet (ModelStates.quartetConfig ρ h0 h1)).Finite,
        ∃ (a : ℝ) (F : ModelStates.ConfSpace), 0 < a ∧
          (ModelStates.configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧
          (ModelStates.configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
          ∀ G : ModelStates.ConfSpace, (ModelStates.configEnergy hfin).Admissible G →
            0 ≤ (ModelStates.configEnergy hfin).energy G + a * ‖G‖ ^ 2) :=
  ⟨WorldsOfTheZeroConfiguration.exists_isEdit_fake_without_real_zero hβ,
    fun h0 h1 hre => ModelStates.quartet_criticalState h0 h1 hre⟩

#print axioms bareMixedEnergy_singleQuartet
#print axioms exists_confinedNullVector_iff_quartetSecularDet_eq_zero
#print axioms quartetSecularDet_pos_below_threshold
#print axioms singleQuartet_complete_twoRung_ladder
#print axioms singleQuartet_alias_sum_le
#print axioms singleQuartet_directSum_primeContinuation
#print axioms singleQuartet_exists_poleNeutral_no_primeHeadContinuation
#print axioms singleQuartet_twoRung_wall_and_primeForm
#print axioms singleQuartet_averagedState_singleConjugatePair
#print axioms hasSingleOffLineQuartet_iff_chebyshevPsi_singleWave
#print axioms eq1_global_and_profile_synthesis
#print axioms singleQuartet_realized_in_models

end GaloisForLFunctions.ExclusionOfTheCriticalState
