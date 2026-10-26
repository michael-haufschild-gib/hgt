import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheSpectrumOfSymmetricSquaresIsTheSign
import GaloisForLFunctions.StripBochnerWeilForcing.TheSimplePoleClassIsZeta
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryPositivity

/-!
# Symmetric-square contractions and exterior kernel counts

`TheSpectrumOfSymmetricSquaresIsTheSign` shows that Weil's positivity is pointwise positivity of the
spectrum of symmetric squares `(α_i − c)(q/α_i − c) ≥ 0` (`c ∈ ℝ`), while degree-one kernel counts
on `H¹` miss complex off-line quartets (`KernelCountsAreBlindToComplexQuartets`) and kernel counts of
`f f′` are squares. This module constructs the spectrum-free arithmetic substitutes over curve data
of arbitrary genus and over `ℤ`:

* **Exterior-power kernel counts force unitarity across all genera**
  (`exteriorDetDeg_linear_nonneg_of_unitary`, `unitary_of_exteriorDetDeg_nonneg`,
  `complexFake_exteriorDetDeg_two_seventeen`). Passing from `H¹` to its exterior powers `Λ^k H¹`
  (`1 ≤ k ≤ |ι|/2`) collides the subset of maximum-modulus eigenvalues into a single real off-line
  eigenvalue `±R_max^k`, turning complex off-line quartets into real off-line factors. Nonnegativity
  of `exteriorDetDeg D k (C c ∓ X)` for `c > (√q)^k` holds on every unitary datum, evaluates to
  `−665379 < 0` on `complexFake` at `k = 2, c = 17`, and forces `∀ i, ‖D.β i‖ = 1` in every genus.
* **Vertical correspondence symmetric squares and simple-pole collapse**
  (`IsEvenPosDef.symSquareShift`, `symSquareShift_cos`, `isEvenPosDef_curveVerticalSection`,
  `isEvenPosDef_goldenDatum_verticalSection`, `isEvenPosDef_complexFake_verticalSection`). On any
  additive group `G`, `(1 + c²)φ(u) − c φ(u + h) − c φ(u − h)` preserves `IsEvenPosDef` for all
  `h ∈ G, c ∈ ℝ` and multiplies cosine modes `cos(tu)` by `|e^{−iht} − c|²` without reading the
  spectrum. Over `𝔽_q` both `goldenDatum` and `complexFake` have `IsEvenPosDef` vertical zeta
  sections on `σ > 1`, whereas over `ℤ` infinitesimal vertical symmetric-square differentiation plus
  the archimedean Gamma factor collapses `CompletedPositiveSystem 1 d` to `ℝ^× · ζ`
  (`completedPositiveSystem_one_iff`).
* **Archimedean midpoint symmetric-square contraction** (`archSymSquare_neg_eq_sq`,
  `isEvenPosDef_midpointSymSquare`, `CompletedPositiveSystem.contractRealPair`,
  `CompletedPositiveSystem.exists_real_offCritical_free`,
  `completedPositiveSystem_one_ne_zero_of_midpoint_contraction`). At the universal self-dual
  midpoint `c = 1`, minus the archimedean symmetric square
  `−e^{t/2}(e^{(β−½)t} − 1)(e^{(½−β)t} − 1) = (e^{βt/2} − e^{(1−β)t/2})² ≥ 0` is an exact square
  whose Laplace transform is `−logDeriv M_β` for `M_β(s) = (s − ½)² / ((s − β)(s − (1 − β)))`.
  Multiplying by `M_β` contracts any real off-critical zero pair `{β, 1 − β}` of a
  `CompletedPositiveSystem κ d` onto `s = 1/2` at zero pole cost (`Δκ = 0`), contracts every
  `CompletedPositiveSystem κ d` in finitely many steps to one free of real off-critical zeros, and
  at `κ = 1` forces `Λ(β) ≠ 0` (`β ≠ 1/2`) directly by self-similarity in `ℝ^× · ζ`.
* **Pole-paid symmetric-square contractions for complex quartets**
  (`CompletedPositiveSystem.contractComplexQuartet_of_le_quarter`,
  `CompletedPositiveSystem.contractComplexQuartet`). Any complex off-critical quartet
  `{ρ₀, 1 − ρ₀, ρ̄₀, 1 − ρ̄₀}` (`ρ₀ = 1/2 + a + iγ`, `0 < a < 1/2`, `γ ≠ 0`) of a
  `CompletedPositiveSystem κ d` contracts onto the critical line `{1/2, 1/2 ± iγ}` inside
  `CompletedPositiveSystem (κ + 1) d` when `a ≤ 1/4` and inside `CompletedPositiveSystem (κ + 2) d`
  for all `0 < a < 1/2`.
-/

open Complex Polynomial Finset Filter Topology Set MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri MultiplicativePositivityGeometry StripBochnerWeilForcing HTGeometry

/-! ### 1. Exterior-power kernel counts force unitarity across all genera -/

section ExteriorCounts

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The eigenvalue `Π_{i ∈ S} α_i` of `Λ^k F` attached to a subset `S ⊆ ι`. -/
def exteriorEigenvalue (S : Finset ι) : ℂ :=
  ∏ i ∈ S, eigenvalue D i

/-- The **`k`-th exterior determinant degree** `det(P(Λ^k F)) = Π_{|S| = k} P(Π_{i ∈ S} α_i)`. -/
def exteriorDetDeg (k : ℕ) (P : ℝ[X]) : ℂ :=
  ∏ S ∈ (Finset.univ : Finset ι).powersetCard k, aeval (exteriorEigenvalue D S) P

theorem exteriorEigenvalue_singleton (i : ι) :
    exteriorEigenvalue D {i} = eigenvalue D i := by
  simp [exteriorEigenvalue]

/-- At degree `k = 1`, the exterior determinant degree is `detDeg`. -/
theorem exteriorDetDeg_one (P : ℝ[X]) :
    exteriorDetDeg D 1 P = detDeg D P := by
  rw [exteriorDetDeg, Finset.powersetCard_one, Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [exteriorEigenvalue]

/-- Multiplicativity of the exterior determinant degree. -/
theorem exteriorDetDeg_mul (k : ℕ) (P Q : ℝ[X]) :
    exteriorDetDeg D k (P * Q) = exteriorDetDeg D k P * exteriorDetDeg D k Q := by
  simp only [exteriorDetDeg, map_mul, Finset.prod_mul_distrib]

theorem exteriorEigenvalue_map_conjPerm (S : Finset ι) :
    exteriorEigenvalue D (S.map D.conjPerm.toEmbedding) = conj (exteriorEigenvalue D S) := by
  simp only [exteriorEigenvalue, Finset.prod_map, map_prod]
  exact Finset.prod_congr rfl fun i _ => eigenvalue_conjPerm D i

theorem exteriorEigenvalue_map_conjPerm_symm (S : Finset ι) :
    exteriorEigenvalue D (S.map D.conjPerm.symm.toEmbedding) = conj (exteriorEigenvalue D S) := by
  have h : (S.map D.conjPerm.symm.toEmbedding).map D.conjPerm.toEmbedding = S := by
    ext i
    simp
  have h1 := exteriorEigenvalue_map_conjPerm D (S.map D.conjPerm.symm.toEmbedding)
  rw [h] at h1
  have h2 := congrArg conj h1
  rw [Complex.conj_conj] at h2
  exact h2.symm

/-- Every exterior determinant degree of a real polynomial is real. -/
theorem conj_exteriorDetDeg (k : ℕ) (P : ℝ[X]) :
    conj (exteriorDetDeg D k P) = exteriorDetDeg D k P := by
  rw [exteriorDetDeg, map_prod]
  refine Finset.prod_nbij'
    (fun S => S.map D.conjPerm.toEmbedding)
    (fun S => S.map D.conjPerm.symm.toEmbedding)
    (fun S hS => ?_) (fun S hS => ?_) (fun S _ => ?_) (fun S _ => ?_) (fun S _ => ?_)
  · rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map, hS.2]⟩
  · rw [Finset.mem_powersetCard] at hS ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map, hS.2]⟩
  · ext i; simp
  · ext i; simp
  · rw [← aeval_conj, ← exteriorEigenvalue_map_conjPerm]

theorem im_exteriorDetDeg (k : ℕ) (P : ℝ[X]) :
    (exteriorDetDeg D k P).im = 0 := by
  have h := congrArg Complex.im (conj_exteriorDetDeg D k P)
  rw [Complex.conj_im] at h
  linarith

/-- Decomposition of `exteriorDetDeg D k P` into conjugate non-real subset pairs and real subsets. -/
private theorem exteriorDetDeg_eq_normSq_mul_real [DecidableEq ι] (k : ℕ) (P : ℝ[X]) :
    let A := (Finset.univ : Finset ι).powersetCard k
    let Apos := A.filter fun S => 0 < (exteriorEigenvalue D S).im
    let Areal := A.filter fun S => (exteriorEigenvalue D S).im = 0
    exteriorDetDeg D k P =
      ((Complex.normSq (∏ S ∈ Apos, aeval (exteriorEigenvalue D S) P) : ℝ) : ℂ) *
        ∏ S ∈ Areal, aeval (exteriorEigenvalue D S) P := by
  intro A Apos Areal
  set F : Finset ι → ℂ := fun S => aeval (exteriorEigenvalue D S) P
  have hsplit1 : ∏ S ∈ A, F S =
      (∏ S ∈ A.filter (fun S => (exteriorEigenvalue D S).im ≠ 0), F S) *
        ∏ S ∈ Areal, F S := by
    have := (Finset.prod_filter_mul_prod_filter_not A
      (fun S => (exteriorEigenvalue D S).im = 0) F).symm
    rw [mul_comm] at this
    exact this
  set Anonreal := A.filter fun S => (exteriorEigenvalue D S).im ≠ 0
  have hsplit2 : ∏ S ∈ Anonreal, F S =
      (∏ S ∈ Anonreal.filter (fun S => 0 < (exteriorEigenvalue D S).im), F S) *
        ∏ S ∈ Anonreal.filter (fun S => ¬ 0 < (exteriorEigenvalue D S).im), F S :=
    (Finset.prod_filter_mul_prod_filter_not Anonreal (fun S => 0 < (exteriorEigenvalue D S).im) F).symm
  have hpos_eq : Anonreal.filter (fun S => 0 < (exteriorEigenvalue D S).im) = Apos := by
    ext S
    simp only [Anonreal, Apos, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ne_of_gt h.2⟩, h.2⟩⟩
  rw [hpos_eq] at hsplit2
  have hneg : ∏ S ∈ Anonreal.filter (fun S => ¬ 0 < (exteriorEigenvalue D S).im), F S =
      ∏ S ∈ Apos, conj (F S) := by
    refine Finset.prod_nbij'
      (fun S => S.map D.conjPerm.symm.toEmbedding)
      (fun S => S.map D.conjPerm.toEmbedding)
      (fun S hS => ?_) (fun S hS => ?_) (fun S _ => ?_) (fun S _ => ?_) (fun S _ => ?_)
    · simp only [Finset.mem_filter, Anonreal, Apos, A, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, not_lt] at hS ⊢
      refine ⟨by rw [Finset.card_map, hS.1.1], ?_⟩
      rw [exteriorEigenvalue_map_conjPerm_symm, Complex.conj_im]
      have hlt : (exteriorEigenvalue D S).im < 0 := lt_of_le_of_ne hS.2 hS.1.2
      linarith
    · simp only [Finset.mem_filter, Anonreal, Apos, A, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, not_lt] at hS ⊢
      rw [Finset.card_map, exteriorEigenvalue_map_conjPerm, Complex.conj_im]
      exact ⟨⟨hS.1, by linarith⟩, by linarith⟩
    · ext i; simp
    · ext i; simp
    · dsimp only [F]
      rw [← aeval_conj, exteriorEigenvalue_map_conjPerm_symm, Complex.conj_conj]
  change ∏ S ∈ A, F S = _
  rw [hsplit1, hsplit2, hneg, ← map_prod, Complex.mul_conj]

/-- **Unitary exterior positivity.** On every unitary curve datum, `exteriorDetDeg D k (C c ∓ X)`
is nonnegative for all `k` and all `c ≥ (√q)^k`. -/
theorem exteriorDetDeg_linear_nonneg_of_unitary (hU : ∀ i : ι, ‖D.β i‖ = 1) (k : ℕ) {c : ℝ}
    (hc : D.sqrtq ^ k ≤ c) :
    0 ≤ (exteriorDetDeg D k (C c - X)).re ∧ 0 ≤ (exteriorDetDeg D k (C c + X)).re := by
  classical
  have hnorm : ∀ S ∈ (Finset.univ : Finset ι).powersetCard k,
      ‖exteriorEigenvalue D S‖ = D.sqrtq ^ k := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [exteriorEigenvalue, norm_prod]
    have h1 : ∀ i ∈ S, ‖eigenvalue D i‖ = D.sqrtq := fun i _ => by
      rw [eigenvalue, norm_mul, Complex.norm_real, Real.norm_of_nonneg D.sqrtq_pos.le, hU i,
        mul_one]
    rw [Finset.prod_congr rfl h1, Finset.prod_const, hS.2]
  have hsign : ∀ sgn : ℝ, sgn = -1 ∨ sgn = 1 →
      0 ≤ (exteriorDetDeg D k (C c + C sgn * X)).re := by
    intro sgn hsgn
    rw [exteriorDetDeg_eq_normSq_mul_real]
    set A := (Finset.univ : Finset ι).powersetCard k
    set Apos := A.filter fun S => 0 < (exteriorEigenvalue D S).im
    set Areal := A.filter fun S => (exteriorEigenvalue D S).im = 0
    have hreal_prod : ∏ S ∈ Areal, aeval (exteriorEigenvalue D S) (C c + C sgn * X) =
        ((∏ S ∈ Areal, (c + sgn * (exteriorEigenvalue D S).re) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun S hS => ?_
      have him : (exteriorEigenvalue D S).im = 0 := (Finset.mem_filter.mp hS).2
      have hre : exteriorEigenvalue D S = ((exteriorEigenvalue D S).re : ℂ) :=
        Complex.ext rfl (by simp [him])
      simp only [map_add, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap]
      rw [hre, Complex.ofReal_re]
      push_cast; ring
    rw [hreal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
    refine mul_nonneg (Complex.normSq_nonneg _) (Finset.prod_nonneg fun S hS => ?_)
    have hSA : S ∈ A := (Finset.mem_filter.mp hS).1
    have habs : |(exteriorEigenvalue D S).re| ≤ c :=
      (Complex.abs_re_le_norm _).trans ((hnorm S hSA).le.trans hc)
    rw [abs_le] at habs
    rcases hsgn with rfl | rfl <;> linarith
  have hm : (C c - X : ℝ[X]) = C c + C (-1 : ℝ) * X := by simp [sub_eq_add_neg]
  have hp : (C c + X : ℝ[X]) = C c + C (1 : ℝ) * X := by simp
  rw [hm, hp]
  exact ⟨hsign (-1) (Or.inl rfl), hsign 1 (Or.inr rfl)⟩

/-- **Exterior kernel counts force unitarity across all genera.** If `exteriorDetDeg D k (C c ∓ X)`
is nonnegative in degrees `1 ≤ k ≤ |ι|/2` above the critical threshold `(√q)^k`, then every
normalized Frobenius eigenvalue of `D` has unit modulus. -/
theorem unitary_of_exteriorDetDeg_nonneg
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ Fintype.card ι / 2 → ∀ c : ℝ, D.sqrtq ^ k < c →
      0 ≤ (exteriorDetDeg D k (C c - X)).re ∧ 0 ≤ (exteriorDetDeg D k (C c + X)).re) :
    ∀ i : ι, ‖D.β i‖ = 1 := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨i₀, hi₀⟩ := hnot
  have hne : (Finset.univ : Finset ι).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
  set R : ℝ := Finset.univ.sup' hne (fun i => ‖eigenvalue D i‖)
  have hR_ge : ∀ i : ι, ‖eigenvalue D i‖ ≤ R := fun i =>
    Finset.le_sup' (fun j => ‖eigenvalue D j‖) (Finset.mem_univ i)
  have hqpos : 0 < D.q := by linarith [D.one_lt_q]
  have heig_pos : ∀ i : ι, 0 < ‖eigenvalue D i‖ := fun i => by
    rw [eigenvalue, norm_mul, Complex.norm_real, Real.norm_of_nonneg D.sqrtq_pos.le]
    exact mul_pos D.sqrtq_pos (norm_pos_iff.mpr (D.β_ne_zero i))
  have hR_gt : D.sqrtq < R := by
    have hprod_norm : ‖eigenvalue D i₀‖ * ‖eigenvalue D (D.fePerm i₀)‖ = D.q := by
      have hp := congrArg norm (eigenvalue_mul_fePerm D i₀)
      rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg hqpos.le] at hp
    have hne_sq : ‖eigenvalue D i₀‖ ≠ D.sqrtq := by
      intro heq
      rw [eigenvalue, norm_mul, Complex.norm_real, Real.norm_of_nonneg D.sqrtq_pos.le] at heq
      exact hi₀ (mul_left_cancel₀ D.sqrtq_pos.ne' (by linarith))
    rcases lt_or_gt_of_ne hne_sq with hlt | hgt
    · have hgt' : D.sqrtq < ‖eigenvalue D (D.fePerm i₀)‖ := by
        nlinarith [D.sqrtq_sq, D.sqrtq_pos, heig_pos (D.fePerm i₀),
          mul_lt_mul_of_pos_right hlt (heig_pos (D.fePerm i₀))]
      exact hgt'.trans_le (hR_ge _)
    · exact hgt.trans_le (hR_ge _)
  have hR_pos : 0 < R := D.sqrtq_pos.trans hR_gt
  obtain ⟨i_max, -, hi_max⟩ := Finset.exists_mem_eq_sup' hne (fun i => ‖eigenvalue D i‖)
  set M : Finset ι := Finset.univ.filter fun i => ‖eigenvalue D i‖ = R
  have hM_nonempty : M.Nonempty := ⟨i_max, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_max.symm⟩⟩
  set k : ℕ := M.card
  have hk1 : 1 ≤ k := Finset.card_pos.mpr hM_nonempty
  have hdisj : Disjoint M (M.map D.fePerm.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    obtain ⟨m, hmM, rfl⟩ := Finset.mem_map.mp hj2
    have hmR : ‖eigenvalue D m‖ = R := (Finset.mem_filter.mp hmM).2
    have hjR : ‖eigenvalue D (D.fePerm m)‖ = R := (Finset.mem_filter.mp hj1).2
    have hp := congrArg norm (eigenvalue_mul_fePerm D m)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hqpos.le, hmR, hjR] at hp
    nlinarith [D.sqrtq_sq, hR_gt, D.sqrtq_pos]
  have hk_half : k ≤ Fintype.card ι / 2 := by
    have hcard : 2 * k ≤ Fintype.card ι := by
      calc 2 * k = M.card + (M.map D.fePerm.toEmbedding).card := by rw [Finset.card_map]; ring
        _ = (M ∪ M.map D.fePerm.toEmbedding).card := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ Fintype.card ι := Finset.card_le_univ _
    omega
  have hM_conj : M.map D.conjPerm.toEmbedding = M := by
    refine Finset.eq_of_subset_of_card_le (fun j hj => ?_) (by rw [Finset.card_map])
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hj
    rw [Finset.mem_filter] at hm ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    change ‖eigenvalue D (D.conjPerm m)‖ = R
    rw [eigenvalue_conjPerm, Complex.norm_conj, hm.2]
  have hM_im : (exteriorEigenvalue D M).im = 0 := by
    have hc := exteriorEigenvalue_map_conjPerm D M
    rw [hM_conj] at hc
    have him := congrArg Complex.im hc
    rw [Complex.conj_im] at him
    linarith
  have hM_norm : ‖exteriorEigenvalue D M‖ = R ^ k := by
    rw [exteriorEigenvalue, norm_prod,
      Finset.prod_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.prod_const]
  set A := (Finset.univ : Finset ι).powersetCard k
  have hM_mem : M ∈ A := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
  have hlt_R : ∀ S ∈ A, S ≠ M → ‖exteriorEigenvalue D S‖ < R ^ k := by
    intro S hS hSM
    rw [Finset.mem_powersetCard] at hS
    have hnot_sub : ¬ S ⊆ M := fun hsub =>
      hSM (Finset.eq_of_subset_of_card_le hsub (by rw [hS.2]))
    obtain ⟨j, hjS, hjM⟩ := Finset.not_subset.mp hnot_sub
    have hj_lt : ‖eigenvalue D j‖ < R :=
      lt_of_le_of_ne (hR_ge j) fun heq => hjM (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
    rw [exteriorEigenvalue, norm_prod, ← Finset.mul_prod_erase S _ hjS]
    have herase_le : ∏ i ∈ S.erase j, ‖eigenvalue D i‖ ≤ R ^ (k - 1) := by
      calc ∏ i ∈ S.erase j, ‖eigenvalue D i‖
          ≤ ∏ _i ∈ S.erase j, R :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hR_ge i)
        _ = R ^ (k - 1) := by rw [Finset.prod_const, Finset.card_erase_of_mem hjS, hS.2]
    have hpos_erase : 0 < ∏ i ∈ S.erase j, ‖eigenvalue D i‖ :=
      Finset.prod_pos fun i _ => heig_pos i
    have hRk : R * R ^ (k - 1) = R ^ k := by
      rw [← pow_succ', Nat.sub_add_cancel hk1]
    calc ‖eigenvalue D j‖ * ∏ i ∈ S.erase j, ‖eigenvalue D i‖
        < R * ∏ i ∈ S.erase j, ‖eigenvalue D i‖ := mul_lt_mul_of_pos_right hj_lt hpos_erase
      _ ≤ R * R ^ (k - 1) := mul_le_mul_of_nonneg_left herase_le hR_pos.le
      _ = R ^ k := hRk
  set B := A.erase M
  set r₂ : ℝ := max (D.sqrtq ^ k)
    (if hB : B.Nonempty then B.sup' hB (fun S => ‖exteriorEigenvalue D S‖) else 0)
  have hsq_lt : D.sqrtq ^ k < R ^ k := pow_lt_pow_left₀ hR_gt D.sqrtq_pos.le (by omega)
  have hr₂_lt : r₂ < R ^ k := by
    refine max_lt hsq_lt ?_
    split_ifs with hB
    · rw [Finset.sup'_lt_iff]
      intro S hSB
      exact hlt_R S (Finset.mem_of_mem_erase hSB) (Finset.ne_of_mem_erase hSB)
    · positivity
  set c : ℝ := (r₂ + R ^ k) / 2
  have hc_gt : D.sqrtq ^ k < c := by
    have : D.sqrtq ^ k ≤ r₂ := le_max_left _ _
    dsimp [c]; linarith
  have hc_lt : c < R ^ k := by dsimp [c]; linarith
  have hc_gt_other : ∀ S ∈ A, S ≠ M → ‖exteriorEigenvalue D S‖ < c := by
    intro S hSA hSM
    have hSB : S ∈ B := Finset.mem_erase.mpr ⟨hSM, hSA⟩
    have hB : B.Nonempty := ⟨S, hSB⟩
    have hle : ‖exteriorEigenvalue D S‖ ≤ r₂ := by
      refine le_trans ?_ (le_max_right _ _)
      rw [dif_pos hB]
      exact Finset.le_sup' (fun T => ‖exteriorEigenvalue D T‖) hSB
    dsimp [c]; linarith
  have hneg_sign : ∀ sgn : ℝ, (sgn = -1 ∨ sgn = 1) →
      c + sgn * (exteriorEigenvalue D M).re < 0 →
      (exteriorDetDeg D k (C c + C sgn * X)).re < 0 := by
    intro sgn hsgn hM_neg
    rw [exteriorDetDeg_eq_normSq_mul_real]
    set Apos := A.filter fun S => 0 < (exteriorEigenvalue D S).im
    set Areal := A.filter fun S => (exteriorEigenvalue D S).im = 0
    have hreal_prod : ∏ S ∈ Areal, aeval (exteriorEigenvalue D S) (C c + C sgn * X) =
        ((∏ S ∈ Areal, (c + sgn * (exteriorEigenvalue D S).re) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun S hS => ?_
      have him : (exteriorEigenvalue D S).im = 0 := (Finset.mem_filter.mp hS).2
      have hre : exteriorEigenvalue D S = ((exteriorEigenvalue D S).re : ℂ) :=
        Complex.ext rfl (by simp [him])
      simp only [map_add, map_mul, aeval_C, aeval_X, Complex.coe_algebraMap]
      rw [hre, Complex.ofReal_re]
      push_cast; ring
    rw [hreal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hnormSq_pos : 0 < Complex.normSq
        (∏ S ∈ Apos, aeval (exteriorEigenvalue D S) (C c + C sgn * X)) := by
      rw [Complex.normSq_pos, Finset.prod_ne_zero_iff]
      intro S hS
      have him_pos : 0 < (exteriorEigenvalue D S).im := (Finset.mem_filter.mp hS).2
      intro hz
      have hz' : (c : ℂ) + (sgn : ℂ) * exteriorEigenvalue D S = 0 := by
        simpa [map_add, map_mul, aeval_C, aeval_X] using hz
      have him0 := congrArg Complex.im hz'
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.zero_im] at him0
      rcases hsgn with rfl | rfl <;> linarith
    have hM_real : M ∈ Areal := Finset.mem_filter.mpr ⟨hM_mem, hM_im⟩
    rw [← Finset.mul_prod_erase Areal _ hM_real]
    have herase_pos : 0 < ∏ S ∈ Areal.erase M, (c + sgn * (exteriorEigenvalue D S).re) := by
      refine Finset.prod_pos fun S hS => ?_
      have hSM : S ≠ M := Finset.ne_of_mem_erase hS
      have hSA : S ∈ A := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hS)).1
      have habs : |(exteriorEigenvalue D S).re| < c :=
        (Complex.abs_re_le_norm _).trans_lt (hc_gt_other S hSA hSM)
      rw [abs_lt] at habs
      rcases hsgn with rfl | rfl <;> linarith
    exact mul_neg_of_pos_of_neg hnormSq_pos (mul_neg_of_neg_of_pos hM_neg herase_pos)
  have hM_re_abs : |(exteriorEigenvalue D M).re| = R ^ k := by
    have hn := congrArg norm
      (Complex.ext rfl (by simp [hM_im]) : exteriorEigenvalue D M = ((exteriorEigenvalue D M).re : ℂ))
    rw [hM_norm, Complex.norm_real, Real.norm_eq_abs] at hn
    exact hn.symm
  obtain ⟨hminus, hplus⟩ := h k hk1 hk_half c hc_gt
  have hm_poly : (C c - X : ℝ[X]) = C c + C (-1 : ℝ) * X := by simp [sub_eq_add_neg]
  have hp_poly : (C c + X : ℝ[X]) = C c + C (1 : ℝ) * X := by simp
  rcases eq_or_eq_neg_of_abs_eq hM_re_abs with hpos_re | hneg_re
  · have hlt := hneg_sign (-1) (Or.inl rfl) (by rw [hpos_re]; linarith)
    rw [← hm_poly] at hlt
    linarith
  · have hlt := hneg_sign 1 (Or.inr rfl) (by rw [hneg_re]; linarith)
    rw [← hp_poly] at hlt
    linarith

/-- **Calibration on `complexFake`.** Although `detDeg complexFake P ≥ 0` for all `P ∈ ℝ[X]`, its
second exterior kernel count at `17 − X` (`17 > 16 = (√16)²`) is `−665379 < 0`: on `Λ² H¹`, the
conjugate pair `(8i, −8i)` collides into the real off-line eigenvalue `64`. -/
theorem complexFake_exteriorDetDeg_two_seventeen :
    exteriorDetDeg complexFake 2 (C 17 - X) = -665379 := by
  have huniv : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by decide
  rw [exteriorDetDeg, huniv]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [exteriorEigenvalue]
  rw [Finset.prod_pair (by decide), Finset.prod_pair (by decide),
      Finset.prod_pair (by decide), Finset.prod_pair (by decide),
      Finset.prod_pair (by decide), Finset.prod_pair (by decide)]
  simp only [complexFake_eigenvalue, map_sub, aeval_C, aeval_X, Complex.coe_algebraMap,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  rw [Complex.ext_iff]
  simp
  norm_num

end ExteriorCounts

/-! ### 2. Vertical correspondence symmetric squares and curve vertical positivity -/

/-- The **correspondence symmetric square**
`((I − c T_h)(I − c T_{−h}) φ)(u) = (1 + c²)φ(u) − c φ(u + h) − c φ(u − h)`
on an additive commutative group `G`. -/
def symSquareShift {G : Type*} [AddCommGroup G] (h : G) (c : ℝ) (φ : G → ℝ) (u : G) : ℝ :=
  (1 + c ^ 2) * φ u - c * φ (u + h) - c * φ (u - h)

/-- **Vertical symmetric-square positivity without reading the spectrum.** For every even
positive-definite `φ : G → ℝ`, every shift `h : G`, and every `c : ℝ`, `symSquareShift h c φ` is
even positive definite. -/
theorem IsEvenPosDef.symSquareShift {G : Type*} [AddCommGroup G] {φ : G → ℝ}
    (hφ : IsEvenPosDef φ) (h : G) (c : ℝ) :
    IsEvenPosDef (ArithmeticCorrespondencePositivity.symSquareShift h c φ) where
  even u := by
    dsimp [ArithmeticCorrespondencePositivity.symSquareShift]
    have e1 : -u + h = -(u - h) := by abel
    have e2 : -u - h = -(u + h) := by abel
    rw [hφ.even u, e1, e2, hφ.even (u - h), hφ.even (u + h)]
    ring
  posDef n x w := by
    have H := hφ.posDef (n + n) (Fin.append x fun i => x i + h) (Fin.append w fun i => -c * w i)
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right] at H
    have heq : ∑ i, ∑ j, w i * w j *
          ArithmeticCorrespondencePositivity.symSquareShift h c φ (x i - x j) =
        (∑ i, ((∑ j, w i * w j * φ (x i - x j)) + ∑ j, w i * (-c * w j) * φ (x i - (x j + h)))) +
        ∑ i, ((∑ j, (-c * w i) * w j * φ (x i + h - x j)) +
          ∑ j, (-c * w i) * (-c * w j) * φ (x i + h - (x j + h))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 : x i - (x j + h) = x i - x j - h := by abel
      have e2 : x i + h - x j = x i - x j + h := by abel
      have e3 : x i + h - (x j + h) = x i - x j := by abel
      rw [e1, e2, e3]
      dsimp [ArithmeticCorrespondencePositivity.symSquareShift]
      ring
    rw [heq]
    exact H

/-- `symSquareShift h c` multiplies each cosine mode `cos(tu)` by the local symmetric-square
eigenvalue `(e^{−iht} − c)(e^{iht} − c) = ‖e^{−iht} − c‖²`. -/
theorem symSquareShift_cos (t h c u : ℝ) :
    symSquareShift h c (fun v => Real.cos (t * v)) u =
      Complex.normSq (Complex.exp (-((t * h : ℝ) : ℂ) * I) - c) * Real.cos (t * u) := by
  dsimp [symSquareShift]
  have hc1 : Real.cos (t * (u + h)) =
      Real.cos (t * u) * Real.cos (t * h) - Real.sin (t * u) * Real.sin (t * h) := by
    rw [mul_add, Real.cos_add]
  have hc2 : Real.cos (t * (u - h)) =
      Real.cos (t * u) * Real.cos (t * h) + Real.sin (t * u) * Real.sin (t * h) := by
    rw [mul_sub, Real.cos_sub]
  have hns : Complex.normSq (Complex.exp (-((t * h : ℝ) : ℂ) * I) - c) =
      1 + c ^ 2 - 2 * c * Real.cos (t * h) := by
    have hexp : Complex.exp (-((t * h : ℝ) : ℂ) * I) =
        ((Real.cos (t * h) : ℝ) : ℂ) - ((Real.sin (t * h) : ℝ) : ℂ) * I := by
      have : -((t * h : ℝ) : ℂ) * I = ((-(t * h) : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg]
      push_cast; ring
    rw [hexp, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.sub_im, Complex.mul_im]
    have hsc := Real.sin_sq_add_cos_sq (t * h)
    nlinarith [hsc]
  rw [hc1, hc2, hns]
  ring

/-- The vertical logarithmic-derivative section `(log q) Σ_{m ≥ 1} N_m(D) q^{−mσ} cos(m (log q) u)`
of a curve datum `D` at abscissa `σ`. -/
def curveVerticalSection {ι : Type*} [Fintype ι] (D : CurveDatum ι) (σ u : ℝ) : ℝ :=
  cosineTrace
    (fun m : ℕ => Real.log D.q * D.pointCount (m + 1) * (D.q ^ (-σ)) ^ (m + 1))
    (fun m : ℕ => ((m + 1 : ℕ) : ℝ) * Real.log D.q) u

/-- Any curve datum with nonnegative point counts `N_m ≥ 0` (`m ≥ 1`) and strip-bounded normalized
eigenvalues `‖β_i‖ ≤ √q` (equivalently `|α_i| ≤ q`) has even positive-definite vertical zeta
sections on `σ > 1`. -/
theorem isEvenPosDef_curveVerticalSection {ι : Type*} [Fintype ι] (D : CurveDatum ι)
    (hN : ∀ m : ℕ, 1 ≤ m → 0 ≤ D.pointCount m)
    (hbdd : ∀ i : ι, ‖D.β i‖ ≤ D.sqrtq) {σ : ℝ} (hσ : 1 < σ) :
    IsEvenPosDef (curveVerticalSection D σ) := by
  have hq1 : 1 < D.q := D.one_lt_q
  have hq0 : 0 < D.q := by linarith
  have hlog : 0 ≤ Real.log D.q := Real.log_nonneg hq1.le
  let w : ℕ → ℝ := fun m => Real.log D.q * D.pointCount (m + 1) * (D.q ^ (-σ)) ^ (m + 1)
  have hw_nn : ∀ m : ℕ, 0 ≤ w m := fun m =>
    mul_nonneg (mul_nonneg hlog (hN (m + 1) (by omega)))
      (pow_nonneg (Real.rpow_nonneg hq0.le _) _)
  refine isEvenPosDef_cosineTrace hw_nn ?_ _
  have hgeom : Summable (fun m : ℕ =>
      Real.log D.q * ((Fintype.card ι : ℝ) + 2) * (D.q ^ (1 - σ)) ^ (m + 1)) := by
    have hlt1 : D.q ^ (1 - σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
    exact ((summable_nat_add_iff 1).mpr
      (summable_geometric_of_lt_one (Real.rpow_nonneg hq0.le _) hlt1)).mul_left _
  refine Summable.of_norm_bounded hgeom fun m => ?_
  rw [Real.norm_of_nonneg (hw_nn m)]
  have htr : |D.trace (m + 1)| ≤ (Fintype.card ι : ℝ) * D.sqrtq ^ (m + 1) := by
    calc |D.trace (m + 1)|
        ≤ ‖D.powerSum (m + 1)‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ i : ι, ‖D.β i‖ ^ (m + 1) := by
          rw [CurveDatum.powerSum]
          exact (norm_sum_le _ _).trans (by simp [norm_pow])
      _ ≤ ∑ _i : ι, D.sqrtq ^ (m + 1) :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hbdd i) _
      _ = (Fintype.card ι : ℝ) * D.sqrtq ^ (m + 1) := by simp
  have hsq_pow : D.sqrtq ^ (m + 1) * D.sqrtq ^ (m + 1) = D.q ^ (m + 1) := by
    rw [← mul_pow, ← sq, D.sqrtq_sq]
  have hpc : D.pointCount (m + 1) ≤ ((Fintype.card ι : ℝ) + 2) * D.q ^ (m + 1) := by
    rw [CurveDatum.pointCount]
    have hneg_tr : -D.trace (m + 1) ≤ (Fintype.card ι : ℝ) * D.sqrtq ^ (m + 1) :=
      (neg_le_abs _).trans htr
    have hmul_tr : D.sqrtq ^ (m + 1) * (-D.trace (m + 1)) ≤
        (Fintype.card ι : ℝ) * D.q ^ (m + 1) := by
      calc D.sqrtq ^ (m + 1) * (-D.trace (m + 1))
          ≤ D.sqrtq ^ (m + 1) * ((Fintype.card ι : ℝ) * D.sqrtq ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hneg_tr (pow_nonneg D.sqrtq_pos.le _)
        _ = (Fintype.card ι : ℝ) * (D.sqrtq ^ (m + 1) * D.sqrtq ^ (m + 1)) := by ring
        _ = (Fintype.card ι : ℝ) * D.q ^ (m + 1) := by rw [hsq_pow]
    have h1_le_q : (1 : ℝ) ≤ D.q ^ (m + 1) := one_le_pow₀ hq1.le
    linarith
  have hq_mul : D.q * D.q ^ (-σ) = D.q ^ (1 - σ) := by
    rw [show (1 - σ : ℝ) = 1 + (-σ) by ring, Real.rpow_add hq0, Real.rpow_one]
  have hrpow : D.q ^ (m + 1) * (D.q ^ (-σ)) ^ (m + 1) = (D.q ^ (1 - σ)) ^ (m + 1) := by
    rw [← mul_pow, hq_mul]
  calc w m
      ≤ Real.log D.q * (((Fintype.card ι : ℝ) + 2) * D.q ^ (m + 1)) *
          (D.q ^ (-σ)) ^ (m + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpc hlog)
          (pow_nonneg (Real.rpow_nonneg hq0.le _) _)
    _ = Real.log D.q * ((Fintype.card ι : ℝ) + 2) *
          (D.q ^ (m + 1) * (D.q ^ (-σ)) ^ (m + 1)) := by ring
    _ = Real.log D.q * ((Fintype.card ι : ℝ) + 2) * (D.q ^ (1 - σ)) ^ (m + 1) := by
        rw [hrpow]

/-- Both `goldenDatum` and `complexFake` have even positive-definite vertical zeta sections on
`σ > 1`, so bare vertical correspondence positivity over `𝔽_q` does not distinguish fake curves
from genuine ones (unlike `CompletedPositiveSystem 1 d` over `ℤ`, which `completedPositiveSystem_one_iff`
collapses to `ℝ^× · ζ`). -/
theorem isEvenPosDef_goldenDatum_verticalSection {σ : ℝ} (hσ : 1 < σ) :
    IsEvenPosDef (curveVerticalSection goldenDatum σ) := by
  refine isEvenPosDef_curveVerticalSection goldenDatum
    (fun _ hm => le_trans (by norm_num) (one_le_goldenDatum_pointCount hm)) (fun i => ?_) hσ
  have hs : goldenDatum.sqrtq = Real.sqrt 5 := rfl
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [hs]
  fin_cases i
  · show ‖((Real.goldenRatio : ℝ) : ℂ)‖ ≤ Real.sqrt 5
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    simp only [Real.goldenRatio]
    constructor <;> nlinarith [h5, h5pos]
  · show ‖((Real.goldenRatio⁻¹ : ℝ) : ℂ)‖ ≤ Real.sqrt 5
    rw [Complex.norm_real, Real.norm_eq_abs, Real.inv_goldenRatio, abs_le]
    simp only [Real.goldenConj]
    constructor <;> nlinarith [h5, h5pos]

theorem isEvenPosDef_complexFake_verticalSection {σ : ℝ} (hσ : 1 < σ) :
    IsEvenPosDef (curveVerticalSection complexFake σ) := by
  refine isEvenPosDef_curveVerticalSection complexFake
    (fun _ hm => complexFake_pointCount_nonneg hm) (fun i => ?_) hσ
  rw [complexFake_norm_β, complexFake_sqrtq]
  split_ifs <;> norm_num

/-! ### 3. Archimedean midpoint symmetric-square contraction on `CompletedPositiveSystem` -/

/-- **Archimedean midpoint symmetric-square identity.** At the universal self-dual midpoint `c = 1`,
minus the archimedean symmetric square `(e^{(β−½)t} − 1)(e^{(½−β)t} − 1)` scaled by `e^{t/2}` is
the exact square `(e^{βt/2} − e^{(1−β)t/2})²`. -/
theorem archSymSquare_neg_eq_sq (β t : ℝ) :
    -Real.exp (t / 2) * ((Real.exp ((β - 1 / 2) * t) - 1) * (Real.exp ((1 / 2 - β) * t) - 1)) =
      (Real.exp (β * t / 2) - Real.exp ((1 - β) * t / 2)) ^ 2 := by
  have h1 : Real.exp ((β - 1 / 2) * t) * Real.exp ((1 / 2 - β) * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have h2 : Real.exp (t / 2) * Real.exp ((β - 1 / 2) * t) = Real.exp (β * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (t / 2) * Real.exp ((1 / 2 - β) * t) = Real.exp ((1 - β) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (β * t / 2) ^ 2 = Real.exp (β * t) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h5 : Real.exp ((1 - β) * t / 2) ^ 2 = Real.exp ((1 - β) * t) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h6 : Real.exp (β * t / 2) * Real.exp ((1 - β) * t / 2) = Real.exp (t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  calc -Real.exp (t / 2) * ((Real.exp ((β - 1 / 2) * t) - 1) * (Real.exp ((1 / 2 - β) * t) - 1))
      = Real.exp (t / 2) * Real.exp ((β - 1 / 2) * t) +
          Real.exp (t / 2) * Real.exp ((1 / 2 - β) * t) -
          Real.exp (t / 2) * (Real.exp ((β - 1 / 2) * t) * Real.exp ((1 / 2 - β) * t) + 1) := by
        ring
    _ = Real.exp (β * t) + Real.exp ((1 - β) * t) - 2 * Real.exp (t / 2) := by
        rw [h1, h2, h3]; ring
    _ = Real.exp (β * t / 2) ^ 2 + Real.exp ((1 - β) * t / 2) ^ 2 -
          2 * (Real.exp (β * t / 2) * Real.exp ((1 - β) * t / 2)) := by
        rw [h4, h5, h6]
    _ = (Real.exp (β * t / 2) - Real.exp ((1 - β) * t / 2)) ^ 2 := by ring

/-- The **midpoint symmetric-square contraction multiplier**
`M_β(s) = (s − 1/2)² / ((s − β)(s − (1 − β)))`. -/
def midpointSymSquare (β : ℝ) (s : ℂ) : ℂ :=
  (s - 1 / 2) ^ 2 / realPairPoly β s

private theorem re_one_div_laplace_cos (a b : ℝ) (ha : 0 < a) :
    (1 / ((a : ℂ) + (b : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0, Real.exp (-a * t) * Real.cos (b * t) := by
  set w : ℂ := -((a : ℂ) + (b : ℂ) * I)
  have hw_re : w.re < 0 := by simp [w]; linarith
  have hint_c : IntegrableOn (fun t : ℝ => Complex.exp (w * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hw_re 0
  have hval := integral_exp_mul_complex_Ioi hw_re 0
  have hrhs_eq : -Complex.exp (w * (0 : ℝ)) / w = 1 / ((a : ℂ) + (b : ℂ) * I) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    dsimp only [w]
    rw [div_neg, neg_div, neg_neg]
  rw [hrhs_eq] at hval
  have hre_int : (∫ t : ℝ in Ioi 0, Complex.exp (w * t)).re =
      ∫ t : ℝ in Ioi 0, (Complex.exp (w * t)).re :=
    (Complex.reCLM.integral_comp_comm hint_c).symm
  rw [← hval, hre_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hw_t_re : (w * (t : ℂ)).re = -a * t := by simp [w]
  have hw_t_im : (w * (t : ℂ)).im = -(b * t) := by simp [w]
  rw [Complex.exp_re, hw_t_re, hw_t_im, Real.cos_neg]

private theorem integrableOn_exp_cos_Ioi (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Real.cos (b * t)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0)
    ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

private theorem isEvenPosDef_laplace_cos {w φ : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hw_cont : Continuous w)
    (hw_nn : ∀ t : ℝ, 0 < t → 0 ≤ w t)
    (hw_le : ∀ t : ℝ, 0 < t → w t ≤ C * Real.exp (-a * t))
    (hφ : ∀ u : ℝ, φ u = ∫ t : ℝ in Ioi 0, w t * Real.cos (t * u)) :
    IsEvenPosDef φ := by
  have hint_dom : IntegrableOn (fun t : ℝ => C * Real.exp (-a * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0).const_mul C
  have hint_ker : ∀ u : ℝ,
      IntegrableOn (fun t : ℝ => w t * Real.cos (t * u)) (Ioi 0) := by
    intro u
    refine Integrable.mono' hint_dom
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nn t ht)]
    exact (mul_le_of_le_one_right (hw_nn t ht) (Real.abs_cos_le_one _)).trans (hw_le t ht)
  refine ⟨fun u => ?_, fun n x c => ?_⟩
  · rw [hφ (-u), hφ u]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_neg, Real.cos_neg]
  · have hsum_int : ∑ i, ∑ j, c i * c j * φ (x i - x j) =
        ∫ t : ℝ in Ioi 0, w t * ∑ i, ∑ j, c i * c j * Real.cos (t * (x i - x j)) := by
      simp_rw [hφ, ← integral_const_mul]
      have h1 : ∀ i : Fin n,
          ∑ j : Fin n, ∫ t : ℝ in Ioi 0, c i * c j * (w t * Real.cos (t * (x i - x j))) =
          ∫ t : ℝ in Ioi 0, ∑ j : Fin n, c i * c j * (w t * Real.cos (t * (x i - x j))) :=
        fun i => (integral_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)).symm
      simp_rw [h1]
      rw [← integral_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum_int]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    refine mul_nonneg (hw_nn t ht) ?_
    rw [gram_cos_eq]
    positivity

private theorem isEvenPosDef_add {φ ψ : ℝ → ℝ} (hφ : IsEvenPosDef φ) (hψ : IsEvenPosDef ψ) :
    IsEvenPosDef (fun u => φ u + ψ u) where
  even u := by rw [hφ.even, hψ.even]
  posDef n x c := by
    have h : (∑ i, ∑ j, c i * c j * (φ (x i - x j) + ψ (x i - x j))) =
        (∑ i, ∑ j, c i * c j * φ (x i - x j)) + ∑ i, ∑ j, c i * c j * ψ (x i - x j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    rw [h]
    exact add_nonneg (hφ.posDef n x c) (hψ.posDef n x c)

private theorem re_neg_logDeriv_midpointSymSquare_eq {β σ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hσ : 1 < σ) (u : ℝ) :
    (-logDeriv (midpointSymSquare β) ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) * (Real.exp (β * t / 2) - Real.exp ((1 - β) * t / 2)) ^ 2 *
          Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  have hs_half : s - 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hs_β1 : s - (β : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hs_β2 : s - ((1 - β : ℝ) : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hd_lin : ∀ c : ℂ, logDeriv (fun z : ℂ => z - c) s = 1 / (s - c) := fun c => by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  have hld : -logDeriv (midpointSymSquare β) s =
      1 / (s - (β : ℂ)) + 1 / (s - ((1 - β : ℝ) : ℂ)) - 2 * (1 / (s - 1 / 2)) := by
    unfold midpointSymSquare realPairPoly
    rw [logDeriv_div (f := fun z : ℂ => (z - 1 / 2) ^ 2)
          (g := fun z : ℂ => (z - (β : ℂ)) * (z - ((1 - β : ℝ) : ℂ)))
          s (pow_ne_zero 2 hs_half) (mul_ne_zero hs_β1 hs_β2)
          ((differentiableAt_id.sub_const (1 / 2)).fun_pow 2)
          ((differentiableAt_id.sub_const (β : ℂ)).mul
            (differentiableAt_id.sub_const ((1 - β : ℝ) : ℂ))),
        logDeriv_fun_pow (differentiableAt_id.sub_const (1 / 2)) 2,
        logDeriv_mul (f := fun z : ℂ => z - (β : ℂ))
          (g := fun z : ℂ => z - ((1 - β : ℝ) : ℂ))
          s hs_β1 hs_β2
          (differentiableAt_id.sub_const (β : ℂ))
          (differentiableAt_id.sub_const ((1 - β : ℝ) : ℂ)),
        hd_lin, hd_lin, hd_lin]
    push_cast; ring
  have e1 : s - (β : ℂ) = (((σ - β : ℝ) : ℂ) + (u : ℂ) * I) := by rw [hs_def]; push_cast; ring
  have e2 : s - ((1 - β : ℝ) : ℂ) = (((σ - (1 - β) : ℝ) : ℂ) + (u : ℂ) * I) := by
    rw [hs_def]; push_cast; ring
  have e3 : s - 1 / 2 = (((σ - 1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by rw [hs_def]; push_cast; ring
  have hre : (-logDeriv (midpointSymSquare β) s).re =
      ((1 / (s - (β : ℂ))).re + (1 / (s - ((1 - β : ℝ) : ℂ))).re) -
        2 * (1 / (s - 1 / 2)).re := by
    rw [hld]
    have h2 : (2 * (1 / (s - 1 / 2))).re = 2 * (1 / (s - 1 / 2)).re := by
      simp [Complex.mul_re]
    rw [Complex.sub_re, Complex.add_re, h2]
  rw [hre, e1, e2, e3,
      re_one_div_laplace_cos (σ - β) u (by linarith),
      re_one_div_laplace_cos (σ - (1 - β)) u (by linarith),
      re_one_div_laplace_cos (σ - 1 / 2) u (by linarith)]
  have hi1 := integrableOn_exp_cos_Ioi (σ - β) u (by linarith)
  have hi2 := integrableOn_exp_cos_Ioi (σ - (1 - β)) u (by linarith)
  have hi3_base := integrableOn_exp_cos_Ioi (σ - 1 / 2) u (by linarith)
  have hi12 : IntegrableOn (fun t : ℝ =>
      Real.exp (-(σ - β) * t) * Real.cos (u * t) +
        Real.exp (-(σ - (1 - β)) * t) * Real.cos (u * t)) (Ioi 0) := hi1.add hi2
  have hi3 : IntegrableOn (fun t : ℝ =>
      2 * (Real.exp (-(σ - 1 / 2) * t) * Real.cos (u * t))) (Ioi 0) := hi3_base.const_mul 2
  symm
  calc ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) * (Real.exp (β * t / 2) - Real.exp ((1 - β) * t / 2)) ^ 2 *
          Real.cos (t * u)
      = ∫ t : ℝ in Ioi 0,
          ((Real.exp (-(σ - β) * t) * Real.cos (u * t) +
              Real.exp (-(σ - (1 - β)) * t) * Real.cos (u * t)) -
            2 * (Real.exp (-(σ - 1 / 2) * t) * Real.cos (u * t))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        have hexp1 : Real.exp (-(σ - β) * t) = Real.exp (-σ * t) * Real.exp (β * t / 2) ^ 2 := by
          rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have hexp2 : Real.exp (-(σ - (1 - β)) * t) =
            Real.exp (-σ * t) * Real.exp ((1 - β) * t / 2) ^ 2 := by
          rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have hexp3 : Real.exp (-(σ - 1 / 2) * t) =
            Real.exp (-σ * t) * (Real.exp (β * t / 2) * Real.exp ((1 - β) * t / 2)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [hexp1, hexp2, hexp3, mul_comm u t]
        ring
    _ = _ := by
        rw [integral_sub hi12 hi3, integral_add hi1 hi2, integral_const_mul]

/-- **Bochner positivity of the midpoint symmetric-square multiplier.** For every `β ∈ [0, 1]` and
`σ > 1`, `u ↦ Re(−logDeriv M_β(σ + iu))` is even positive definite. -/
theorem isEvenPosDef_midpointSymSquare {β σ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hσ : 1 < σ) :
    IsEvenPosDef (fun u : ℝ => (-logDeriv (midpointSymSquare β) ((σ : ℂ) + (u : ℂ) * I)).re) := by
  refine isEvenPosDef_laplace_cos (C := 2) (a := σ - 1) (by linarith) (by fun_prop)
    (fun t _ => by positivity) (fun t ht => ?_)
    (re_neg_logDeriv_midpointSymSquare_eq hβ0 hβ1 hσ)
  have hb1 : Real.exp (β * t / 2) ≤ Real.exp (t / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hb2 : Real.exp ((1 - β) * t / 2) ≤ Real.exp (t / 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hsq : (Real.exp (β * t / 2) - Real.exp ((1 - β) * t / 2)) ^ 2 ≤ 2 * Real.exp (t / 2) ^ 2 := by
    have h0a := Real.exp_pos (β * t / 2)
    have h0b := Real.exp_pos ((1 - β) * t / 2)
    nlinarith [sq_nonneg (Real.exp (β * t / 2) - Real.exp ((1 - β) * t / 2))]
  calc Real.exp (-σ * t) * (Real.exp (β * t / 2) - Real.exp ((1 - β) * t / 2)) ^ 2
      ≤ Real.exp (-σ * t) * (2 * Real.exp (t / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = 2 * (Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2))) := by ring
    _ = 2 * Real.exp (-(σ - 1) * t) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

private theorem orderOneEnvelope_sub_const (c : ℂ) :
    OrderOneEnvelope (fun s : ℂ => s - c) :=
  (RHTower.orderOneEnvelope_id.add (orderOneEnvelope_const (-c))).congr fun s => by ring

private theorem dslope_entire_and_orderOne {f : ℂ → ℂ} {z₀ : ℂ}
    (hd : Differentiable ℂ f) (hf : OrderOneEnvelope f) (hz₀ : f z₀ = 0) :
    Differentiable ℂ (dslope f z₀) ∧
      OrderOneEnvelope (dslope f z₀) ∧
      ∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s := by
  have hD : Differentiable ℂ (dslope f z₀) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 z₀)).mpr
      hd.differentiableOn
  have hid : ∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s := fun s => by
    simpa [hz₀, smul_eq_mul] using sub_smul_dslope f z₀ s
  refine ⟨hD, ?_, hid⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hDpos, hDb⟩ := orderOneEnvelope_const (B : ℂ)
  refine ⟨C + D, by linarith, fun z => ?_⟩
  by_cases hz : ‖z - z₀‖ ≤ 1
  · have hmem : z ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
    have hBabs : B ≤ ‖(B : ℂ)‖ := by simpa using le_abs_self B
    exact (hB z hmem).trans (hBabs.trans ((hDb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : D ≤ C + D) z))))
  · have hn := congrArg norm (hid z)
    rw [norm_mul] at hn
    have hle : ‖dslope f z₀ z‖ ≤ ‖f z‖ := by
      have hz1 : 1 ≤ ‖z - z₀‖ := le_of_not_ge hz
      nlinarith [norm_nonneg (dslope f z₀ z)]
    exact hle.trans ((hb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : C ≤ C + D) z)))

private theorem exists_quotient_prod_linear :
    ∀ (L : List ℂ) (f : ℂ → ℂ), L.Nodup → Differentiable ℂ f → OrderOneEnvelope f →
      (∀ r ∈ L, f r = 0) →
      ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ OrderOneEnvelope Q ∧
        ∀ s : ℂ, (L.map (fun r => s - r)).prod * Q s = f s
  | [], f, _, hdf, hof, _ => ⟨f, hdf, hof, fun s => by simp⟩
  | r :: rs, f, hnd, hdf, hof, hzero => by
      rw [List.nodup_cons] at hnd
      obtain ⟨hdg, hog, hg_eq⟩ := dslope_entire_and_orderOne hdf hof (hzero r (by simp))
      have hg_zero : ∀ w ∈ rs, dslope f r w = 0 := by
        intro w hw
        have hne : w - r ≠ 0 := sub_ne_zero.mpr fun heq => hnd.1 (heq ▸ hw)
        have hmul := hg_eq w
        rw [hzero w (by simp [hw])] at hmul
        exact (mul_eq_zero.mp hmul).resolve_left hne
      obtain ⟨Q, hdQ, hoQ, hQ_eq⟩ :=
        exists_quotient_prod_linear rs (dslope f r) hnd.2 hdg hog hg_zero
      refine ⟨Q, hdQ, hoQ, fun s => ?_⟩
      simp only [List.map_cons, List.prod_cons]
      rw [mul_assoc, hQ_eq s, hg_eq s]

private theorem continuous_eq_of_mul_eq_off_finset {g₁ g₂ P : ℂ → ℂ} (S : Finset ℂ)
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hP : ∀ z : ℂ, z ∉ S → P z ≠ 0)
    (hmul : ∀ z : ℂ, g₁ z * P z = g₂ z * P z) :
    ∀ s : ℂ, g₁ s = g₂ s := by
  intro s
  have hU : ((S.erase s : Set ℂ)ᶜ) ∈ 𝓝 s :=
    (S.erase s).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
  have hev : g₁ =ᶠ[𝓝[≠] s] g₂ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz1 hz2
    have hzS : z ∉ S := fun hmem => hz1 (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hz2, hmem⟩))
    exact mul_right_cancel₀ (hP z hzS) (hmul z)
  exact tendsto_nhds_unique (hg₁.continuousAt.continuousWithinAt.congr' hev)
    hg₂.continuousAt.continuousWithinAt

/-- **Zero-cost midpoint symmetric-square contraction (`Δκ = 0`).** Any real off-critical zero
`β ≠ 1/2` of a `CompletedPositiveSystem κ d F Λ` together with its partner `1 − β` contracts onto
`s = 1/2` via `midpointSymSquare β`, preserving `(κ, d)` and increasing the central vanishing order
at `1/2` by `2`. -/
theorem CompletedPositiveSystem.contractRealPair {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {β : ℝ} (hβ : β ≠ 1 / 2) (hzero : Λ (β : ℂ) = 0) :
    ∃ Λc : ℂ → ℂ,
      CompletedPositiveSystem κ d (fun s => F s * midpointSymSquare β s) Λc ∧
      (∀ s : ℂ, Λc s * realPairPoly β s = Λ s * (s - 1 / 2) ^ 2) ∧
      Λc (1 / 2) = 0 ∧
      (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 2 := by
  classical
  obtain ⟨hβ0, hβ1⟩ := hS.zero_re_mem_Icc hzero
  simp only [Complex.ofReal_re] at hβ0 hβ1
  have hzero_sym : Λ (((1 - β : ℝ) : ℂ)) = 0 := by
    have he : (((1 - β : ℝ) : ℂ)) = 1 - (β : ℂ) := by push_cast; ring
    rw [he, hS.sym_Λ, hzero]
  have hne_pair : (β : ℂ) ≠ ((1 - β : ℝ) : ℂ) := fun heq => by
    have := congrArg Complex.re heq
    simp at this
    exact hβ (by linarith)
  have hnd : ([(β : ℂ), ((1 - β : ℝ) : ℂ)] : List ℂ).Nodup := by
    rw [List.nodup_cons, List.mem_singleton]
    exact ⟨hne_pair, List.nodup_singleton _⟩
  obtain ⟨Q, hdQ, hoQ, hQ_eq⟩ := exists_quotient_prod_linear
    [(β : ℂ), ((1 - β : ℝ) : ℂ)] Λ hnd hS.entire_Λ hS.orderOne_Λ
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> assumption)
  have hQ_poly : ∀ s : ℂ, realPairPoly β s * Q s = Λ s := fun s => by
    have h := hQ_eq s
    simpa [realPairPoly, mul_assoc] using h
  let Λc : ℂ → ℂ := fun s => Q s * (s - 1 / 2) ^ 2
  have hdΛc : Differentiable ℂ Λc := hdQ.mul (by fun_prop)
  have ho_sq : OrderOneEnvelope (fun s : ℂ => (s - 1 / 2) ^ 2) :=
    ((orderOneEnvelope_sub_const (1 / 2)).mul (orderOneEnvelope_sub_const (1 / 2))).congr
      fun s => by ring
  have hoΛc : OrderOneEnvelope Λc := hoQ.mul ho_sq
  have hrel : ∀ s : ℂ, Λc s * realPairPoly β s = Λ s * (s - 1 / 2) ^ 2 := fun s => by
    dsimp [Λc]
    rw [← hQ_poly s]
    ring
  have hP_nz_off : ∀ z : ℂ, z ∉ ({(β : ℂ), ((1 - β : ℝ) : ℂ)} : Finset ℂ) →
      realPairPoly β z ≠ 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    exact mul_ne_zero (sub_ne_zero.mpr hz.1) (sub_ne_zero.mpr hz.2)
  have hsym_c : ∀ s : ℂ, Λc (1 - s) = Λc s := by
    refine continuous_eq_of_mul_eq_off_finset {(β : ℂ), ((1 - β : ℝ) : ℂ)}
      (hdΛc.continuous.comp (by fun_prop)) hdΛc.continuous hP_nz_off fun z => ?_
    have hP_sym : realPairPoly β z = realPairPoly β (1 - z) := by
      unfold realPairPoly; push_cast; ring
    have hC_sym : ((1 - z) - 1 / 2) ^ 2 = (z - 1 / 2) ^ 2 := by ring
    rw [hP_sym, hrel (1 - z), hS.sym_Λ z, hC_sym, ← hP_sym, ← hrel z]
  have hconj_c : ∀ s : ℂ, Λc (starRingEnd ℂ s) = starRingEnd ℂ (Λc s) := by
    have hinv := continuous_eq_of_mul_eq_off_finset {(β : ℂ), ((1 - β : ℝ) : ℂ)}
      (Complex.continuous_conj.comp (hdΛc.continuous.comp Complex.continuous_conj))
      hdΛc.continuous hP_nz_off fun z => by
        have hP_conj : starRingEnd ℂ (realPairPoly β (starRingEnd ℂ z)) = realPairPoly β z := by
          unfold realPairPoly
          simp only [map_mul, map_sub, Complex.conj_ofReal, RingHomCompTriple.comp_apply,
            RingHom.id_apply]
        have hC_conj : starRingEnd ℂ ((starRingEnd ℂ z - 1 / 2) ^ 2) = (z - 1 / 2) ^ 2 := by
          simp [map_ofNat]
        have h1 := congrArg (starRingEnd ℂ) (hrel (starRingEnd ℂ z))
        rw [map_mul (starRingEnd ℂ) (Λc (starRingEnd ℂ z)),
          map_mul (starRingEnd ℂ) (Λ (starRingEnd ℂ z)),
          hP_conj, hC_conj, hS.conj_Λ z, Complex.conj_conj, ← hrel z] at h1
        simpa only [Function.comp_apply] using h1
    intro s
    have hs := congrArg (starRingEnd ℂ) (hinv s)
    simpa [Function.comp_apply] using hs
  have hP_nz_re : ∀ s : ℂ, 1 < s.re → realPairPoly β s ≠ 0 := by
    intro s hs
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hM_nz : ∀ s : ℂ, 1 < s.re → midpointSymSquare β s ≠ 0 := by
    intro s hs
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact div_ne_zero (pow_ne_zero 2 hs_half) (hP_nz_re s hs)
  have hM_diffOn : DifferentiableOn ℂ (midpointSymSquare β) {s : ℂ | 1 < s.re} := by
    intro s hs
    change 1 < s.re at hs
    exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (z - 1 / 2) ^ 2) s).div
      (by unfold realPairPoly; fun_prop) (hP_nz_re s hs))).differentiableWithinAt
  have hSc : CompletedPositiveSystem κ d (fun s => F s * midpointSymSquare β s) Λc :=
    { degree_pos := hS.degree_pos
      diffOn_F := hS.diffOn_F.mul hM_diffOn
      ne_zero_F := fun s hs => mul_ne_zero (hS.ne_zero_F s hs) (hM_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => F s * midpointSymSquare β s) ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (midpointSymSquare β) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := midpointSymSquare β) s
                (hS.ne_zero_F s hs) (hM_nz s hs)
                ((hS.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                ((hM_diffOn s hs).differentiableAt (hopen.mem_nhds hs)),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add (hS.posDef_neg_logDeriv hσ) (isEvenPosDef_midpointSymSquare hβ0 hβ1 hσ)
      entire_Λ := hdΛc
      orderOne_Λ := hoΛc
      sym_Λ := hsym_c
      conj_Λ := hconj_c
      completed_eq := fun s hs => by
        have hP_nz := hP_nz_re s hs
        apply mul_right_cancel₀ hP_nz
        have hdiv : midpointSymSquare β s * realPairPoly β s = (s - 1 / 2) ^ 2 :=
          div_mul_cancel₀ _ hP_nz
        calc Λc s * realPairPoly β s
            = Λ s * (s - 1 / 2) ^ 2 := hrel s
          _ = ((s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * F s) *
                (midpointSymSquare β s * realPairPoly β s) := by
              rw [hS.completed_eq s hs, hdiv]
          _ = (s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * (F s * midpointSymSquare β s) *
                realPairPoly β s := by ring }
  have hord : (analyticOrderAt Λc (1 / 2)).toNat = (analyticOrderAt Λ (1 / 2)).toNat + 2 := by
    have hfun : Λc * realPairPoly β = Λ * ((· - (1 / 2 : ℂ)) ^ 2) := funext hrel
    have hP_half_nz : realPairPoly β (1 / 2) ≠ 0 := by
      unfold realPairPoly
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h; simp at this; exact hβ (by linarith)
      · have := congrArg Complex.re h; simp at this; exact hβ (by linarith)
    have hdP : Differentiable ℂ (realPairPoly β) := by unfold realPairPoly; fun_prop
    have hord_P : analyticOrderAt (realPairPoly β) (1 / 2) = 0 :=
      (hdP.analyticAt (1 / 2)).analyticOrderAt_eq_zero.mpr hP_half_nz
    have hord_L : analyticOrderAt (Λc * realPairPoly β) (1 / 2) = analyticOrderAt Λc (1 / 2) := by
      rw [analyticOrderAt_mul (hdΛc.analyticAt _) (hdP.analyticAt _), hord_P, add_zero]
    have hord_R : analyticOrderAt (Λ * ((· - (1 / 2 : ℂ)) ^ 2)) (1 / 2) =
        analyticOrderAt Λ (1 / 2) + (2 : ℕ) := by
      have han_mon : AnalyticAt ℂ ((· - (1 / 2 : ℂ)) ^ 2) (1 / 2) :=
        ((differentiable_id.sub_const (1 / 2 : ℂ)).pow 2).analyticAt (1 / 2)
      rw [analyticOrderAt_mul (hS.entire_Λ.analyticAt _) han_mon,
          analyticOrderAt_centeredMonomial]
    have heq_ord : analyticOrderAt Λc (1 / 2) = analyticOrderAt Λ (1 / 2) + (2 : ℕ) := by
      rw [← hord_L, hfun, hord_R]
    rw [heq_ord, ENat.toNat_add (hS.orderAt_ne_top (1 / 2)) (ENat.coe_ne_top 2), ENat.toNat_coe]
  exact ⟨Λc, hSc, hrel, by dsimp [Λc]; simp, hord⟩

/-- **Finite-step elimination of all real off-critical zeros.** Repeated midpoint symmetric-square
contraction transforms every `CompletedPositiveSystem κ d F Λ` into a `CompletedPositiveSystem κ d`
at the same `(κ, d)` with no real off-critical zeros (`∀ β ≠ 1/2, Λc(β) ≠ 0`). -/
theorem CompletedPositiveSystem.exists_real_offCritical_free {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) :
    ∃ Fc Λc : ℂ → ℂ,
      CompletedPositiveSystem κ d Fc Λc ∧
      ∀ β : ℝ, β ≠ 1 / 2 → Λc (β : ℂ) ≠ 0 := by
  suffices haux : ∀ (N : ℕ) {F' Λ' : ℂ → ℂ}, CompletedPositiveSystem κ d F' Λ' →
      9 * κ - (analyticOrderAt Λ' (1 / 2)).toNat ≤ N →
      ∃ Fc Λc : ℂ → ℂ,
        CompletedPositiveSystem κ d Fc Λc ∧ ∀ β : ℝ, β ≠ 1 / 2 → Λc (β : ℂ) ≠ 0 from
    haux (9 * κ - (analyticOrderAt Λ (1 / 2)).toNat) hS le_rfl
  intro N
  induction N with
  | zero =>
      intro F' Λ' hS' hN
      have hbud := real_zero_archimedean_budget hS' ∅ (fun _ hx => absurd hx (Finset.notMem_empty _))
      simp only [Finset.sum_empty, mul_zero, add_zero] at hbud
      have hd := hS'.degree_pos
      omega
  | succ N ih =>
      intro F' Λ' hS' hN
      by_cases hfree : ∀ β : ℝ, β ≠ 1 / 2 → Λ' (β : ℂ) ≠ 0
      · exact ⟨F', Λ', hS', hfree⟩
      · push Not at hfree
        obtain ⟨β, hβ, hzero⟩ := hfree
        obtain ⟨Λ₁, hS₁, -, -, hord₁⟩ := CompletedPositiveSystem.contractRealPair hS' hβ hzero
        have hbud := real_zero_archimedean_budget hS₁ ∅
          (fun _ hx => absurd hx (Finset.notMem_empty _))
        simp only [Finset.sum_empty, mul_zero, add_zero] at hbud
        have hd := hS₁.degree_pos
        exact ih hS₁ (by omega)

/-- **Real off-critical nonvanishing at `κ = 1` via midpoint contraction and `ζ`-rigidity.**
Without numerical Gamma or digamma bounds, combining `contractRealPair` (`Δκ = 0`) with
`completedPositiveSystem_one_iff` (`CompletedPositiveSystem 1 d = ℝ^× · ζ`) forces `M_β(2) = M_β(3)`,
hence `β = 1/2`. -/
theorem completedPositiveSystem_one_ne_zero_of_midpoint_contraction {d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem 1 d F Λ) {β : ℝ} (hβ : β ≠ 1 / 2) :
    Λ (β : ℂ) ≠ 0 := by
  intro hzero
  obtain ⟨hβ0, hβ1⟩ := hS.zero_re_mem_Icc hzero
  simp only [Complex.ofReal_re] at hβ0 hβ1
  obtain ⟨Λc, hSc, -, -, -⟩ := CompletedPositiveSystem.contractRealPair hS hβ hzero
  obtain ⟨-, K₁, hK₁, hF₁⟩ := completedPositiveSystem_one_iff hS
  obtain ⟨-, K₂, -, hF₂⟩ := completedPositiveSystem_one_iff hSc
  have hZ := completedPositiveSystem_riemannZeta
  have hZ2 : riemannZeta 2 ≠ 0 := hZ.ne_zero_F 2 (by norm_num)
  have hZ3 : riemannZeta 3 ≠ 0 := hZ.ne_zero_F 3 (by norm_num)
  have hK₁C : (K₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK₁
  have hM2 : midpointSymSquare β 2 = (K₂ : ℂ) / (K₁ : ℂ) := by
    have h2 := hF₂ 2 (by norm_num)
    rw [hF₁ 2 (by norm_num)] at h2
    rw [eq_div_iff hK₁C]
    apply mul_right_cancel₀ hZ2
    linear_combination h2
  have hM3 : midpointSymSquare β 3 = (K₂ : ℂ) / (K₁ : ℂ) := by
    have h3 := hF₂ 3 (by norm_num)
    rw [hF₁ 3 (by norm_num)] at h3
    rw [eq_div_iff hK₁C]
    apply mul_right_cancel₀ hZ3
    linear_combination h3
  have hM23 : midpointSymSquare β 2 = midpointSymSquare β 3 := hM2.trans hM3.symm
  have hc2 : midpointSymSquare β 2 =
      (((2 - 1 / 2) ^ 2 / ((2 - β) * (2 - (1 - β))) : ℝ) : ℂ) := by
    unfold midpointSymSquare realPairPoly; push_cast; ring
  have hc3 : midpointSymSquare β 3 =
      (((3 - 1 / 2) ^ 2 / ((3 - β) * (3 - (1 - β))) : ℝ) : ℂ) := by
    unfold midpointSymSquare realPairPoly; push_cast; ring
  rw [hc2, hc3] at hM23
  have hreal := Complex.ofReal_injective hM23
  have hd2 : 0 < (2 - β) * (2 - (1 - β)) := by nlinarith
  have hd3 : 0 < (3 - β) * (3 - (1 - β)) := by nlinarith
  rw [div_eq_div_iff hd2.ne' hd3.ne'] at hreal
  have hsq0 : (β - 1 / 2) ^ 2 = 0 := by nlinarith
  exact hβ (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq0))

/-! ### 4. Pole-paid symmetric-square contractions for complex off-critical quartets -/

/-- The off-critical quartet polynomial
`Q_off(a, γ; s) = ((s − (1/2 + a))² + γ²)((s − (1/2 − a))² + γ²)`. -/
def quartetOffPoly (a γ : ℝ) (s : ℂ) : ℂ :=
  ((s - ((1 / 2 + a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2) *
    ((s - ((1 / 2 - a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2)

/-- The contracted critical-line quartet polynomial
`Q_crit(γ; s) = ((s − 1/2)² + γ²)² = (s − (1/2 + iγ))² (s − (1/2 − iγ))²`. -/
def quartetCritPoly (γ : ℝ) (s : ℂ) : ℂ :=
  ((s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2) ^ 2

/-- Single-pole (`Δκ = 1`) symmetric-square quartet contraction multiplier (`0 < a ≤ 1/4`). -/
def quartetSymSquareOne (a γ : ℝ) (s : ℂ) : ℂ :=
  ((s - 1 / 2) ^ 2 * quartetCritPoly γ s) / ((s * (s - 1)) * quartetOffPoly a γ s)

/-- Double-pole (`Δκ = 2`) symmetric-square quartet contraction multiplier (`0 < a < 1/2`). -/
def quartetSymSquareTwo (a γ : ℝ) (s : ℂ) : ℂ :=
  ((s - 1 / 2) ^ 4 * quartetCritPoly γ s) / ((s * (s - 1)) ^ 2 * quartetOffPoly a γ s)

private theorem sq_add_sq_eq_mul_I (w : ℂ) (x γ : ℝ) :
    (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2 =
      (w - ((x : ℂ) + (γ : ℂ) * I)) * (w - ((x : ℂ) - (γ : ℂ) * I)) := by
  calc (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2
      = (w - (x : ℂ)) ^ 2 - ((γ : ℂ) * I) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    _ = (w - ((x : ℂ) + (γ : ℂ) * I)) * (w - ((x : ℂ) - (γ : ℂ) * I)) := by ring

private theorem re_logDeriv_sq_add_sq_laplace_cos (σ u x γ : ℝ) (hx : x < σ) :
    (logDeriv (fun w : ℂ => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2) ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0, 2 * Real.exp (-(σ - x) * t) * Real.cos (γ * t) * Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  set z₁ : ℂ := (x : ℂ) + (γ : ℂ) * I
  set z₂ : ℂ := (x : ℂ) - (γ : ℂ) * I
  have hz₁ : s - z₁ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def, z₁] at this; linarith
  have hz₂ : s - z₂ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def, z₂] at this; linarith
  have hfun : (fun w : ℂ => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2) =
      fun w : ℂ => (w - z₁) * (w - z₂) :=
    funext fun w => sq_add_sq_eq_mul_I w x γ
  have hld : logDeriv (fun w : ℂ => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2) s =
      1 / (s - z₁) + 1 / (s - z₂) := by
    rw [hfun, logDeriv_mul (f := fun w => w - z₁) (g := fun w => w - z₂) s hz₁ hz₂
      (differentiableAt_id.sub_const z₁) (differentiableAt_id.sub_const z₂)]
    congr 1 <;> rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  have e₁ : s - z₁ = (((σ - x : ℝ) : ℂ) + ((u - γ : ℝ) : ℂ) * I) := by
    dsimp [s, z₁]; push_cast; ring
  have e₂ : s - z₂ = (((σ - x : ℝ) : ℂ) + ((u + γ : ℝ) : ℂ) * I) := by
    dsimp [s, z₂]; push_cast; ring
  rw [hld, Complex.add_re, e₁, e₂,
      re_one_div_laplace_cos (σ - x) (u - γ) (by linarith),
      re_one_div_laplace_cos (σ - x) (u + γ) (by linarith),
      ← integral_add (integrableOn_exp_cos_Ioi (σ - x) (u - γ) (by linarith))
        (integrableOn_exp_cos_Ioi (σ - x) (u + γ) (by linarith))]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hc₁ : Real.cos ((u - γ) * t) =
      Real.cos (t * u) * Real.cos (γ * t) + Real.sin (t * u) * Real.sin (γ * t) := by
    rw [show (u - γ) * t = t * u - γ * t by ring, Real.cos_sub]
  have hc₂ : Real.cos ((u + γ) * t) =
      Real.cos (t * u) * Real.cos (γ * t) - Real.sin (t * u) * Real.sin (γ * t) := by
    rw [show (u + γ) * t = t * u + γ * t by ring, Real.cos_add]
  rw [hc₁, hc₂]
  ring

private def quartetPureRatio (a γ : ℝ) (s : ℂ) : ℂ :=
  quartetCritPoly γ s / quartetOffPoly a γ s

private theorem re_neg_logDeriv_quartetPureRatio_eq {a γ σ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hσ : 1 < σ) (u : ℝ) :
    (-logDeriv (quartetPureRatio a γ) ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) *
          (2 * Real.exp (t / 2) * Real.cos (γ * t) *
            (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  let qAt : ℝ → ℂ → ℂ := fun x w => (w - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2
  have hq_nz : ∀ x : ℝ, x < σ → qAt x s ≠ 0 := by
    intro x hx
    dsimp [qAt]
    rw [sq_add_sq_eq_mul_I]
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hnz_c := hq_nz (1 / 2) (by linarith)
  have hnz_p := hq_nz (1 / 2 + a) (by linarith)
  have hnz_m := hq_nz (1 / 2 - a) (by linarith)
  have hratio_eq : quartetPureRatio a γ =
      fun w => qAt (1 / 2) w ^ 2 / (qAt (1 / 2 + a) w * qAt (1 / 2 - a) w) := by
    funext w
    unfold quartetPureRatio quartetCritPoly quartetOffPoly
    dsimp [qAt]
    norm_num
  have hld : -logDeriv (quartetPureRatio a γ) s =
      logDeriv (qAt (1 / 2 + a)) s + logDeriv (qAt (1 / 2 - a)) s -
        2 * logDeriv (qAt (1 / 2)) s := by
    rw [hratio_eq,
        logDeriv_div (f := fun w => qAt (1 / 2) w ^ 2)
          (g := fun w => qAt (1 / 2 + a) w * qAt (1 / 2 - a) w)
          s (pow_ne_zero 2 hnz_c) (mul_ne_zero hnz_p hnz_m)
          (by dsimp [qAt]; fun_prop) (by dsimp [qAt]; fun_prop),
        logDeriv_fun_pow (by dsimp [qAt]; fun_prop) 2,
        logDeriv_mul (f := qAt (1 / 2 + a)) (g := qAt (1 / 2 - a)) s hnz_p hnz_m
          (by dsimp [qAt]; fun_prop) (by dsimp [qAt]; fun_prop)]
    push_cast; ring
  have hre : (-logDeriv (quartetPureRatio a γ) s).re =
      ((logDeriv (qAt (1 / 2 + a)) s).re + (logDeriv (qAt (1 / 2 - a)) s).re) -
        2 * (logDeriv (qAt (1 / 2)) s).re := by
    rw [hld]
    have h2 : (2 * logDeriv (qAt (1 / 2)) s).re = 2 * (logDeriv (qAt (1 / 2)) s).re := by
      simp [Complex.mul_re]
    rw [Complex.sub_re, Complex.add_re, h2]
  rw [hre]
  dsimp [qAt]
  rw [re_logDeriv_sq_add_sq_laplace_cos σ u (1 / 2 + a) γ (by linarith),
      re_logDeriv_sq_add_sq_laplace_cos σ u (1 / 2 - a) γ (by linarith),
      re_logDeriv_sq_add_sq_laplace_cos σ u (1 / 2) γ (by linarith)]
  have hint : ∀ x : ℝ, x < σ →
      IntegrableOn
        (fun t : ℝ => 2 * Real.exp (-(σ - x) * t) * Real.cos (γ * t) * Real.cos (t * u))
        (Ioi 0) := by
    intro x hx
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -(σ - x) < 0) 0).const_mul 2)
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (Real.exp_pos _)]
    have hc1 := Real.abs_cos_le_one (γ * t)
    have hc2 := Real.abs_cos_le_one (t * u)
    have hprod : |Real.cos (γ * t)| * |Real.cos (t * u)| ≤ 1 :=
      mul_le_one₀ hc1 (abs_nonneg _) hc2
    calc 2 * Real.exp (-(σ - x) * t) * |Real.cos (γ * t)| * |Real.cos (t * u)|
        = 2 * Real.exp (-(σ - x) * t) * (|Real.cos (γ * t)| * |Real.cos (t * u)|) := by ring
      _ ≤ 2 * Real.exp (-(σ - x) * t) * 1 :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 2 * Real.exp (-(σ - x) * t) := mul_one _
  have hip := hint (1 / 2 + a) (by linarith)
  have him := hint (1 / 2 - a) (by linarith)
  have hic_base := hint (1 / 2) (by linarith)
  have hipm : IntegrableOn (fun t : ℝ =>
      2 * Real.exp (-(σ - (1 / 2 + a)) * t) * Real.cos (γ * t) * Real.cos (t * u) +
        2 * Real.exp (-(σ - (1 / 2 - a)) * t) * Real.cos (γ * t) * Real.cos (t * u)) (Ioi 0) :=
    hip.add him
  have hic : IntegrableOn (fun t : ℝ =>
      2 * (2 * Real.exp (-(σ - 1 / 2) * t) * Real.cos (γ * t) * Real.cos (t * u))) (Ioi 0) :=
    hic_base.const_mul 2
  symm
  calc ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) *
          (2 * Real.exp (t / 2) * Real.cos (γ * t) *
            (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u)
      = ∫ t : ℝ in Ioi 0,
          ((2 * Real.exp (-(σ - (1 / 2 + a)) * t) * Real.cos (γ * t) * Real.cos (t * u) +
              2 * Real.exp (-(σ - (1 / 2 - a)) * t) * Real.cos (γ * t) * Real.cos (t * u)) -
            2 * (2 * Real.exp (-(σ - 1 / 2) * t) * Real.cos (γ * t) * Real.cos (t * u))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        have he_p : Real.exp (-(σ - (1 / 2 + a)) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) * Real.exp (a * t / 2) ^ 2 := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have he_m : Real.exp (-(σ - (1 / 2 - a)) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) * Real.exp (-(a * t / 2)) ^ 2 := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        have he_c : Real.exp (-(σ - 1 / 2) * t) =
            Real.exp (-σ * t) * Real.exp (t / 2) *
              (Real.exp (a * t / 2) * Real.exp (-(a * t / 2))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [he_p, he_m, he_c]
        ring
    _ = _ := by
        rw [integral_sub hipm hic, integral_add hip him, integral_const_mul]

private theorem re_neg_logDeriv_quartetPower_eq (m : ℕ) {a γ σ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hσ : 1 < σ) (u : ℝ) :
    (-logDeriv (fun s => midpointSymSquare 0 s ^ m * quartetPureRatio a γ s)
        ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) * Real.exp (t / 2) *
          ((m : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  have hs_re : 1 < s.re := by simp [hs_def]; exact hσ
  have hM0_nz : midpointSymSquare 0 s ≠ 0 := by
    unfold midpointSymSquare realPairPoly
    refine div_ne_zero (pow_ne_zero 2 (fun h => ?_)) (mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hQ_nz : quartetPureRatio a γ s ≠ 0 := by
    unfold quartetPureRatio quartetCritPoly quartetOffPoly
    have hnz : ∀ x : ℝ, x < σ → (s - (x : ℂ)) ^ 2 + (γ : ℂ) ^ 2 ≠ 0 := by
      intro x hx
      rw [sq_add_sq_eq_mul_I]
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h; simp [hs_def] at this; linarith
      · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    have hc : (s - 1 / 2) ^ 2 + (γ : ℂ) ^ 2 ≠ 0 := by
      simpa using hnz (1 / 2) (by linarith)
    exact div_ne_zero (pow_ne_zero 2 hc)
      (mul_ne_zero (hnz (1 / 2 + a) (by linarith)) (hnz (1 / 2 - a) (by linarith)))
  have hM0_diff : DifferentiableAt ℂ (midpointSymSquare 0) s := by
    unfold midpointSymSquare realPairPoly
    refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hQ_diff : DifferentiableAt ℂ (quartetPureRatio a γ) s := by
    unfold quartetPureRatio quartetCritPoly quartetOffPoly
    refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
    refine mul_ne_zero ?_ ?_ <;>
      (rw [sq_add_sq_eq_mul_I]; refine mul_ne_zero (fun h => ?_) (fun h => ?_))
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
    · have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hld : (-logDeriv (fun z => midpointSymSquare 0 z ^ m * quartetPureRatio a γ z) s).re =
      (m : ℝ) * (-logDeriv (midpointSymSquare 0) s).re +
        (-logDeriv (quartetPureRatio a γ) s).re := by
    rw [logDeriv_mul (f := fun z => midpointSymSquare 0 z ^ m) (g := quartetPureRatio a γ) s
          (pow_ne_zero m hM0_nz) hQ_nz (hM0_diff.fun_pow m) hQ_diff,
        logDeriv_fun_pow hM0_diff m, neg_add, Complex.add_re]
    congr 1
    have : -((m : ℂ) * logDeriv (midpointSymSquare 0) s) =
        ((m : ℝ) : ℂ) * (-logDeriv (midpointSymSquare 0) s) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [hld, re_neg_logDeriv_midpointSymSquare_eq le_rfl zero_le_one hσ u,
      re_neg_logDeriv_quartetPureRatio_eq ha0 ha1 hσ u]
  have hi1 : IntegrableOn
      (fun t : ℝ => Real.exp (-σ * t) *
        (Real.exp ((0 : ℝ) * t / 2) - Real.exp ((1 - (0 : ℝ)) * t / 2)) ^ 2 *
        Real.cos (t * u)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -(σ - 1) < 0) 0).const_mul 2)
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    have hcos := Real.abs_cos_le_one (t * u)
    have hsq : (Real.exp ((0 : ℝ) * t / 2) - Real.exp ((1 - (0 : ℝ)) * t / 2)) ^ 2 ≤
        2 * Real.exp (t / 2) ^ 2 := by
      simp only [zero_mul, zero_div, Real.exp_zero, sub_zero, one_mul]
      have h1 : (1 : ℝ) ≤ Real.exp (t / 2) := Real.one_le_exp (by linarith)
      nlinarith [sq_nonneg (1 - Real.exp (t / 2))]
    calc Real.exp (-σ * t) *
          (Real.exp ((0 : ℝ) * t / 2) - Real.exp ((1 - (0 : ℝ)) * t / 2)) ^ 2 * |Real.cos (t * u)|
        ≤ Real.exp (-σ * t) * (2 * Real.exp (t / 2) ^ 2) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le) hcos
            (abs_nonneg _) (by positivity)
      _ = 2 * (Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2))) := by ring
      _ = 2 * Real.exp (-(σ - 1) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hi2 : IntegrableOn
      (fun t : ℝ => Real.exp (-σ * t) *
        (2 * Real.exp (t / 2) * Real.cos (γ * t) *
          (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
        Real.cos (t * u)) (Ioi 0) := by
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (by linarith : -(σ - 1) < 0) 0).const_mul 4)
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hc1 := Real.abs_cos_le_one (γ * t)
    have hc2 := Real.abs_cos_le_one (t * u)
    have hdiff_le : Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) ≤ Real.exp (t / 4) := by
      have hle : Real.exp (a * t / 2) ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (-(a * t / 2))]
    have hdiff_nn : 0 ≤ Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) := by
      have hle : Real.exp (-(a * t / 2)) ≤ Real.exp (a * t / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hsq_le : (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤ Real.exp (t / 2) := by
      calc (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2
          ≤ Real.exp (t / 4) ^ 2 := pow_le_pow_left₀ hdiff_nn hdiff_le 2
        _ = Real.exp (t / 2) := by rw [sq, ← Real.exp_add]; congr 1; ring
    have hmid_le : |2 * Real.exp (t / 2) * Real.cos (γ * t) *
        (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2| ≤ 4 * Real.exp t := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))))]
      have hprod : |Real.cos (γ * t)| *
          (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤ Real.exp (t / 2) := by
        calc |Real.cos (γ * t)| * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2
            ≤ 1 * Real.exp (t / 2) :=
              mul_le_mul hc1 hsq_le (sq_nonneg _) zero_le_one
          _ = Real.exp (t / 2) := one_mul _
      have he_t : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
        rw [← Real.exp_add]; congr 1; ring
      calc 2 * Real.exp (t / 2) * |Real.cos (γ * t)| *
            (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2
          = 2 * Real.exp (t / 2) *
              (|Real.cos (γ * t)| * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) := by ring
        _ ≤ 2 * Real.exp (t / 2) * Real.exp (t / 2) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = 2 * Real.exp t := by rw [mul_assoc, he_t]
        _ ≤ 4 * Real.exp t := by linarith [Real.exp_pos t]
    calc Real.exp (-σ * t) * |2 * Real.exp (t / 2) * Real.cos (γ * t) *
          (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2| * |Real.cos (t * u)|
        ≤ Real.exp (-σ * t) * (4 * Real.exp t) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmid_le (Real.exp_pos _).le) hc2
            (abs_nonneg _) (by positivity)
      _ = 4 * (Real.exp (-σ * t) * Real.exp t) := by ring
      _ = 4 * Real.exp (-(σ - 1) * t) := by rw [← Real.exp_add]; congr 2; ring
  have hi1m : IntegrableOn
      (fun t : ℝ => (m : ℝ) * (Real.exp (-σ * t) *
        (Real.exp ((0 : ℝ) * t / 2) - Real.exp ((1 - (0 : ℝ)) * t / 2)) ^ 2 *
        Real.cos (t * u))) (Ioi 0) := hi1.const_mul (m : ℝ)
  symm
  calc ∫ t : ℝ in Ioi 0,
        Real.exp (-σ * t) * Real.exp (t / 2) *
          ((m : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
          Real.cos (t * u)
      = ∫ t : ℝ in Ioi 0,
          ((m : ℝ) * (Real.exp (-σ * t) *
              (Real.exp ((0 : ℝ) * t / 2) - Real.exp ((1 - (0 : ℝ)) * t / 2)) ^ 2 *
              Real.cos (t * u)) +
            Real.exp (-σ * t) *
              (2 * Real.exp (t / 2) * Real.cos (γ * t) *
                (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2) *
              Real.cos (t * u)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        have h0_id : (Real.exp ((0 : ℝ) * t / 2) - Real.exp ((1 - (0 : ℝ)) * t / 2)) ^ 2 =
            Real.exp (t / 2) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 := by
          simp only [zero_mul, zero_div, Real.exp_zero, sub_zero, one_mul]
          have hq1 : Real.exp (t / 2) * Real.exp (t / 4) ^ 2 = Real.exp t := by
            rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
          have hq2 : Real.exp (t / 2) * Real.exp (-(t / 4)) ^ 2 = 1 := by
            rw [sq, ← Real.exp_add, ← Real.exp_add]
            ring_nf
            exact Real.exp_zero
          have hq3 : Real.exp (t / 4) * Real.exp (-(t / 4)) = 1 := by
            rw [← Real.exp_add]
            ring_nf
            exact Real.exp_zero
          have hq4 : Real.exp (t / 2) ^ 2 = Real.exp t := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          calc (1 - Real.exp (t / 2)) ^ 2
              = 1 - 2 * Real.exp (t / 2) + Real.exp (t / 2) ^ 2 := by ring
            _ = Real.exp (t / 2) * Real.exp (-(t / 4)) ^ 2 -
                  2 * Real.exp (t / 2) * (Real.exp (t / 4) * Real.exp (-(t / 4))) +
                  Real.exp (t / 2) * Real.exp (t / 4) ^ 2 := by
                rw [hq2, hq3, hq1, hq4]; ring
            _ = Real.exp (t / 2) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 := by ring
        rw [h0_id]
        ring
    _ = _ := by
        rw [integral_add hi1m hi2, integral_const_mul]

private theorem isEvenPosDef_quartetSymSquareOne {a γ σ : ℝ}
    (ha0 : 0 < a) (ha_q : a ≤ 1 / 4) (hσ : 1 < σ) :
    IsEvenPosDef (fun u : ℝ => (-logDeriv (quartetSymSquareOne a γ) ((σ : ℂ) + (u : ℂ) * I)).re) := by
  have hfun : quartetSymSquareOne a γ =
      fun s => midpointSymSquare 0 s ^ 1 * quartetPureRatio a γ s := by
    funext s
    unfold quartetSymSquareOne midpointSymSquare realPairPoly quartetPureRatio
    simp only [pow_one, Complex.ofReal_zero, sub_zero, Complex.ofReal_one]
    rw [div_mul_div_comm]
  rw [hfun]
  refine isEvenPosDef_laplace_cos (C := 3) (a := σ - 1) (by linarith) (by fun_prop)
    (fun t ht => ?_) (fun t ht => ?_)
    (re_neg_logDeriv_quartetPower_eq 1 ha0 (by linarith) hσ)
  · have ha_le : Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) ≤
        Real.exp (t / 8) - Real.exp (-(t / 8)) := by
      have h1 : Real.exp (a * t / 2) ≤ Real.exp (t / 8) := Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (-(t / 8)) ≤ Real.exp (-(a * t / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have ha_nn : 0 ≤ Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) := by
      have h1 : Real.exp (-(a * t / 2)) ≤ Real.exp (a * t / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hsum_ge2 : 2 ≤ Real.exp (t / 8) + Real.exp (-(t / 8)) := by
      have hprod : Real.exp (t / 16) * Real.exp (-(t / 16)) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hsq1 : Real.exp (t / 16) ^ 2 = Real.exp (t / 8) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hsq2 : Real.exp (-(t / 16)) ^ 2 = Real.exp (-(t / 8)) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      nlinarith [sq_nonneg (Real.exp (t / 16) - Real.exp (-(t / 16))), hprod, hsq1, hsq2]
    have hfac : Real.exp (t / 4) - Real.exp (-(t / 4)) =
        (Real.exp (t / 8) - Real.exp (-(t / 8))) *
          (Real.exp (t / 8) + Real.exp (-(t / 8))) := by
      have hsq1 : Real.exp (t / 8) ^ 2 = Real.exp (t / 4) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have hsq2 : Real.exp (-(t / 8)) ^ 2 = Real.exp (-(t / 4)) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      nlinarith [hsq1, hsq2]
    have h2_le : 2 * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ≤
        Real.exp (t / 4) - Real.exp (-(t / 4)) := by
      rw [hfac]
      nlinarith [ha_le, ha_nn, hsum_ge2]
    have h4_sq : 4 * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 := by
      have hpow := pow_le_pow_left₀ (by positivity) h2_le 2
      linarith
    have hcos : -1 ≤ Real.cos (γ * t) := Real.neg_one_le_cos _
    have hinner : 0 ≤ (1 : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 := by
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), h4_sq, hcos]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (by simpa using hinner)
  · have hq_nn : 0 ≤ Real.exp (t / 4) - Real.exp (-(t / 4)) := by
      have : Real.exp (-(t / 4)) ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hq_le : Real.exp (t / 4) - Real.exp (-(t / 4)) ≤ Real.exp (t / 4) := by
      linarith [Real.exp_pos (-(t / 4))]
    have hq_sq : (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 ≤ Real.exp (t / 2) := by
      calc (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2
          ≤ Real.exp (t / 4) ^ 2 := pow_le_pow_left₀ hq_nn hq_le 2
        _ = Real.exp (t / 2) := by rw [sq, ← Real.exp_add]; congr 1; ring
    have ha_nn : 0 ≤ Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) := by
      have : Real.exp (-(a * t / 2)) ≤ Real.exp (a * t / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have ha_le : Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) ≤ Real.exp (t / 4) := by
      have : Real.exp (a * t / 2) ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (-(a * t / 2))]
    have ha_sq : (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤ Real.exp (t / 2) := by
      calc (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2
          ≤ Real.exp (t / 4) ^ 2 := pow_le_pow_left₀ ha_nn ha_le 2
        _ = Real.exp (t / 2) := by rw [sq, ← Real.exp_add]; congr 1; ring
    have hcos1 : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
    have hinner_le : ((1 : ℕ) : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        3 * Real.exp (t / 2) := by
      simp only [Nat.cast_one, one_mul]
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), hq_sq, ha_sq, hcos1]
    calc Real.exp (-σ * t) * Real.exp (t / 2) *
          (((1 : ℕ) : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2)
        ≤ Real.exp (-σ * t) * Real.exp (t / 2) * (3 * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left hinner_le (by positivity)
      _ = 3 * (Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2))) := by ring
      _ = 3 * Real.exp (-(σ - 1) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

private theorem isEvenPosDef_quartetSymSquareTwo {a γ σ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1 / 2) (hσ : 1 < σ) :
    IsEvenPosDef (fun u : ℝ => (-logDeriv (quartetSymSquareTwo a γ) ((σ : ℂ) + (u : ℂ) * I)).re) := by
  have hfun : quartetSymSquareTwo a γ =
      fun s => midpointSymSquare 0 s ^ 2 * quartetPureRatio a γ s := by
    funext s
    unfold quartetSymSquareTwo midpointSymSquare realPairPoly quartetPureRatio
    simp only [Complex.ofReal_zero, sub_zero, Complex.ofReal_one, div_pow, ← pow_mul]
    rw [div_mul_div_comm]
  rw [hfun]
  refine isEvenPosDef_laplace_cos (C := 4) (a := σ - 1) (by linarith) (by fun_prop)
    (fun t ht => ?_) (fun t ht => ?_)
    (re_neg_logDeriv_quartetPower_eq 2 ha0 ha1 hσ)
  · have ha_nn : 0 ≤ Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) := by
      have : Real.exp (-(a * t / 2)) ≤ Real.exp (a * t / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have ha_le : Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) ≤
        Real.exp (t / 4) - Real.exp (-(t / 4)) := by
      have h1 : Real.exp (a * t / 2) ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (-(t / 4)) ≤ Real.exp (-(a * t / 2)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have hsq_le : (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 :=
      pow_le_pow_left₀ ha_nn ha_le 2
    have hcos : -1 ≤ Real.cos (γ * t) := Real.neg_one_le_cos _
    have hinner : 0 ≤ ((2 : ℕ) : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 := by
      simp only [Nat.cast_ofNat]
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), hsq_le, hcos]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hinner
  · have hq_nn : 0 ≤ Real.exp (t / 4) - Real.exp (-(t / 4)) := by
      have : Real.exp (-(t / 4)) ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hq_le : Real.exp (t / 4) - Real.exp (-(t / 4)) ≤ Real.exp (t / 4) := by
      linarith [Real.exp_pos (-(t / 4))]
    have hq_sq : (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 ≤ Real.exp (t / 2) := by
      calc (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2
          ≤ Real.exp (t / 4) ^ 2 := pow_le_pow_left₀ hq_nn hq_le 2
        _ = Real.exp (t / 2) := by rw [sq, ← Real.exp_add]; congr 1; ring
    have ha_nn : 0 ≤ Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) := by
      have : Real.exp (-(a * t / 2)) ≤ Real.exp (a * t / 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    have ha_le : Real.exp (a * t / 2) - Real.exp (-(a * t / 2)) ≤ Real.exp (t / 4) := by
      have : Real.exp (a * t / 2) ≤ Real.exp (t / 4) := Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (-(a * t / 2))]
    have ha_sq : (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤ Real.exp (t / 2) := by
      calc (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2
          ≤ Real.exp (t / 4) ^ 2 := pow_le_pow_left₀ ha_nn ha_le 2
        _ = Real.exp (t / 2) := by rw [sq, ← Real.exp_add]; congr 1; ring
    have hcos1 : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
    have hinner_le : ((2 : ℕ) : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
        2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2 ≤
        4 * Real.exp (t / 2) := by
      simp only [Nat.cast_ofNat]
      nlinarith [sq_nonneg (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))), hq_sq, ha_sq, hcos1]
    calc Real.exp (-σ * t) * Real.exp (t / 2) *
          (((2 : ℕ) : ℝ) * (Real.exp (t / 4) - Real.exp (-(t / 4))) ^ 2 +
            2 * Real.cos (γ * t) * (Real.exp (a * t / 2) - Real.exp (-(a * t / 2))) ^ 2)
        ≤ Real.exp (-σ * t) * Real.exp (t / 2) * (4 * Real.exp (t / 2)) :=
          mul_le_mul_of_nonneg_left hinner_le (by positivity)
      _ = 4 * (Real.exp (-σ * t) * (Real.exp (t / 2) * Real.exp (t / 2))) := by ring
      _ = 4 * Real.exp (-(σ - 1) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring

private theorem orderOneEnvelope_pow_sub_half :
    ∀ n : ℕ, OrderOneEnvelope (fun s : ℂ => (s - 1 / 2) ^ n)
  | 0 => (orderOneEnvelope_const 1).congr fun s => by simp
  | n + 1 => ((orderOneEnvelope_pow_sub_half n).mul (orderOneEnvelope_sub_const (1 / 2))).congr
      fun s => by rw [pow_succ]

private theorem contractComplexQuartet_of_posDef {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ)
    {a γ : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hγ : γ ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) {W : ℂ → ℂ}
    (hW_eq : ∀ s : ℂ, W s =
      ((s - 1 / 2) ^ (2 * m) * quartetCritPoly γ s) / ((s * (s - 1)) ^ m * quartetOffPoly a γ s))
    (hposDef : ∀ {σ : ℝ}, 1 < σ →
      IsEvenPosDef (fun u : ℝ => (-logDeriv W ((σ : ℂ) + (u : ℂ) * I)).re))
    (hzero : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      CompletedPositiveSystem (κ + m) d (fun s => F s * W s) Λc ∧
      (∀ s : ℂ, Λc s * quartetOffPoly a γ s =
        Λ s * ((s - 1 / 2) ^ (2 * m) * quartetCritPoly γ s)) ∧
      Λc (1 / 2) = 0 ∧
      Λc (1 / 2 + (γ : ℂ) * I) = 0 ∧
      Λc (1 / 2 - (γ : ℂ) * I) = 0 := by
  classical
  set r₁ : ℂ := ((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I
  set r₂ : ℂ := ((1 / 2 + a : ℝ) : ℂ) - (γ : ℂ) * I
  set r₃ : ℂ := ((1 / 2 - a : ℝ) : ℂ) + (γ : ℂ) * I
  set r₄ : ℂ := ((1 / 2 - a : ℝ) : ℂ) - (γ : ℂ) * I
  have hr₁ : Λ r₁ = 0 := by
    have he : r₁ = 1 / 2 + (a : ℂ) + (γ : ℂ) * I := by dsimp [r₁]; push_cast; ring
    rwa [he]
  have hr₂ : Λ r₂ = 0 := by
    have he : r₂ = starRingEnd ℂ r₁ := by dsimp [r₁, r₂]; simp [map_ofNat]; ring
    rw [he, hS.conj_Λ, hr₁, map_zero]
  have hr₄ : Λ r₄ = 0 := by
    have he : r₄ = 1 - r₁ := by dsimp [r₁, r₄]; push_cast; ring
    rw [he, hS.sym_Λ, hr₁]
  have hr₃ : Λ r₃ = 0 := by
    have he : r₃ = 1 - r₂ := by dsimp [r₂, r₃]; push_cast; ring
    rw [he, hS.sym_Λ, hr₂]
  have h12 : r₁ ≠ r₂ := fun h => hγ (by have := congrArg Complex.im h; simp [r₁, r₂] at this; linarith)
  have h13 : r₁ ≠ r₃ := fun h => by have := congrArg Complex.re h; simp [r₁, r₃] at this; linarith
  have h14 : r₁ ≠ r₄ := fun h => by have := congrArg Complex.re h; simp [r₁, r₄] at this; linarith
  have h23 : r₂ ≠ r₃ := fun h => by have := congrArg Complex.re h; simp [r₂, r₃] at this; linarith
  have h24 : r₂ ≠ r₄ := fun h => by have := congrArg Complex.re h; simp [r₂, r₄] at this; linarith
  have h34 : r₃ ≠ r₄ := fun h => hγ (by have := congrArg Complex.im h; simp [r₃, r₄] at this; linarith)
  have hnd : ([r₁, r₂, r₃, r₄] : List ℂ).Nodup := by
    simp [h12, h13, h14, h23, h24, h34]
  obtain ⟨Q, hdQ, hoQ, hQ_eq⟩ := exists_quotient_prod_linear [r₁, r₂, r₃, r₄] Λ hnd
    hS.entire_Λ hS.orderOne_Λ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> assumption)
  have hOff_fac : ∀ s : ℂ, quartetOffPoly a γ s =
      (s - r₁) * (s - r₂) * (s - r₃) * (s - r₄) := fun s => by
    unfold quartetOffPoly
    rw [sq_add_sq_eq_mul_I s (1 / 2 + a) γ, sq_add_sq_eq_mul_I s (1 / 2 - a) γ]
    dsimp [r₁, r₂, r₃, r₄]; ring
  have hQ_poly : ∀ s : ℂ, quartetOffPoly a γ s * Q s = Λ s := fun s => by
    have h := hQ_eq s
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    rw [hOff_fac s]
    linear_combination h
  let C_num : ℂ → ℂ := fun s => (s - 1 / 2) ^ (2 * m) * quartetCritPoly γ s
  let Λc : ℂ → ℂ := fun s => Q s * C_num s
  have hdC : Differentiable ℂ C_num := by unfold C_num quartetCritPoly; fun_prop
  have hdΛc : Differentiable ℂ Λc := hdQ.mul hdC
  have ho_crit : OrderOneEnvelope (quartetCritPoly γ) := by
    let p₁ := orderOneEnvelope_sub_const (1 / 2 + (γ : ℂ) * I)
    let p₂ := orderOneEnvelope_sub_const (1 / 2 - (γ : ℂ) * I)
    refine ((p₁.mul p₂).mul (p₁.mul p₂)).congr fun s => ?_
    unfold quartetCritPoly
    have hf := sq_add_sq_eq_mul_I s (1 / 2) γ
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at hf
    rw [hf]
    ring
  have hoΛc : OrderOneEnvelope Λc :=
    hoQ.mul ((orderOneEnvelope_pow_sub_half (2 * m)).mul ho_crit)
  have hrel : ∀ s : ℂ, Λc s * quartetOffPoly a γ s = Λ s * C_num s := fun s => by
    dsimp [Λc]
    rw [← hQ_poly s]
    ring
  have hOff_nz_off : ∀ z : ℂ, z ∉ ({r₁, r₂, r₃, r₄} : Finset ℂ) → quartetOffPoly a γ z ≠ 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [hOff_fac z]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hz.1)
      (sub_ne_zero.mpr hz.2.1)) (sub_ne_zero.mpr hz.2.2.1)) (sub_ne_zero.mpr hz.2.2.2)
  have hsym_c : ∀ s : ℂ, Λc (1 - s) = Λc s := by
    refine continuous_eq_of_mul_eq_off_finset {r₁, r₂, r₃, r₄}
      (hdΛc.continuous.comp (by fun_prop)) hdΛc.continuous hOff_nz_off fun z => ?_
    have hP_sym : quartetOffPoly a γ z = quartetOffPoly a γ (1 - z) := by
      unfold quartetOffPoly; push_cast; ring
    have hC_sym : C_num (1 - z) = C_num z := by
      dsimp [C_num]
      unfold quartetCritPoly
      have h1 : ((1 - z) - 1 / 2) ^ (2 * m) = (z - 1 / 2) ^ (2 * m) := by
        rw [pow_mul, pow_mul]
        congr 1; ring
      have h2 : ((1 - z) - 1 / 2) ^ 2 = (z - 1 / 2) ^ 2 := by ring
      rw [h1, h2]
    rw [hP_sym, hrel (1 - z), hS.sym_Λ z, hC_sym, ← hP_sym, ← hrel z]
  have hconj_c : ∀ s : ℂ, Λc (starRingEnd ℂ s) = starRingEnd ℂ (Λc s) := by
    have hinv := continuous_eq_of_mul_eq_off_finset {r₁, r₂, r₃, r₄}
      (Complex.continuous_conj.comp (hdΛc.continuous.comp Complex.continuous_conj))
      hdΛc.continuous hOff_nz_off fun z => by
        have hP_conj : starRingEnd ℂ (quartetOffPoly a γ (starRingEnd ℂ z)) =
            quartetOffPoly a γ z := by
          unfold quartetOffPoly
          simp only [map_mul, map_add, map_pow, map_sub, Complex.conj_ofReal,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        have hC_conj : starRingEnd ℂ (C_num (starRingEnd ℂ z)) = C_num z := by
          dsimp [C_num]
          unfold quartetCritPoly
          simp [map_ofNat]
        have h1 := congrArg (starRingEnd ℂ) (hrel (starRingEnd ℂ z))
        rw [map_mul (starRingEnd ℂ) (Λc (starRingEnd ℂ z)),
          map_mul (starRingEnd ℂ) (Λ (starRingEnd ℂ z)),
          hP_conj, hC_conj, hS.conj_Λ z, Complex.conj_conj, ← hrel z] at h1
        simpa only [Function.comp_apply] using h1
    intro s
    have hs := congrArg (starRingEnd ℂ) (hinv s)
    simpa [Function.comp_apply] using hs
  have hDen_nz : ∀ s : ℂ, 1 < s.re → (s * (s - 1)) ^ m * quartetOffPoly a γ s ≠ 0 := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr fun h => by rw [h, Complex.one_re] at hs; linarith
    have hOff : quartetOffPoly a γ s ≠ 0 := by
      rw [hOff_fac s]
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_)) (fun h => ?_))
        (fun h => ?_)
      · have := congrArg Complex.re h; simp [r₁] at this; linarith
      · have := congrArg Complex.re h; simp [r₂] at this; linarith
      · have := congrArg Complex.re h; simp [r₃] at this; linarith
      · have := congrArg Complex.re h; simp [r₄] at this; linarith
    exact mul_ne_zero (pow_ne_zero m (mul_ne_zero hs0 hs1)) hOff
  have hW_nz : ∀ s : ℂ, 1 < s.re → W s ≠ 0 := by
    intro s hs
    rw [hW_eq s]
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hcrit_nz : quartetCritPoly γ s ≠ 0 := by
      unfold quartetCritPoly
      have hf := sq_add_sq_eq_mul_I s (1 / 2) γ
      have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
      rw [hc] at hf
      rw [hf]
      refine pow_ne_zero 2 (mul_ne_zero (fun h => ?_) (fun h => ?_))
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    exact div_ne_zero (mul_ne_zero (pow_ne_zero (2 * m) hs_half) hcrit_nz) (hDen_nz s hs)
  have hW_diffOn : DifferentiableOn ℂ W {s : ℂ | 1 < s.re} := by
    rw [funext hW_eq]
    intro s hs
    change 1 < s.re at hs
    have hdDen : DifferentiableAt ℂ (fun x : ℂ => (x * (x - 1)) ^ m * quartetOffPoly a γ x) s := by
      unfold quartetOffPoly; fun_prop
    exact ((hdC s).div hdDen (hDen_nz s hs)).differentiableWithinAt
  have hSc : CompletedPositiveSystem (κ + m) d (fun s => F s * W s) Λc :=
    { degree_pos := hS.degree_pos
      diffOn_F := hS.diffOn_F.mul hW_diffOn
      ne_zero_F := fun s hs => mul_ne_zero (hS.ne_zero_F s hs) (hW_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ => (-logDeriv (fun s => F s * W s) ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv F ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv W ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := F) (g := W) s
                (hS.ne_zero_F s hs) (hW_nz s hs)
                ((hS.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                ((hW_diffOn s hs).differentiableAt (hopen.mem_nhds hs)),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add (hS.posDef_neg_logDeriv hσ) (hposDef hσ)
      entire_Λ := hdΛc
      orderOne_Λ := hoΛc
      sym_Λ := hsym_c
      conj_Λ := hconj_c
      completed_eq := fun s hs => by
        have hden := hDen_nz s hs
        have hOff_nz : quartetOffPoly a γ s ≠ 0 := right_ne_zero_of_mul hden
        apply mul_right_cancel₀ hOff_nz
        have hdiv : W s * ((s * (s - 1)) ^ m * quartetOffPoly a γ s) = C_num s := by
          rw [hW_eq s]
          exact div_mul_cancel₀ _ hden
        calc Λc s * quartetOffPoly a γ s
            = Λ s * C_num s := hrel s
          _ = ((s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * F s) *
                (W s * ((s * (s - 1)) ^ m * quartetOffPoly a γ s)) := by
              rw [hS.completed_eq s hs, hdiv]
          _ = (s * (s - 1)) ^ (κ + m) * Complex.Gammaℝ s ^ d * (F s * W s) *
                quartetOffPoly a γ s := by
              rw [pow_add]; ring }
  have hzero_half : Λc (1 / 2) = 0 := by
    dsimp [Λc, C_num]
    rw [sub_self, zero_pow (by omega), zero_mul, mul_zero]
  have hcrit_plus : quartetCritPoly γ (1 / 2 + (γ : ℂ) * I) = 0 := by
    unfold quartetCritPoly
    have : ((1 / 2 + (γ : ℂ) * I) - 1 / 2) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
      calc ((1 / 2 + (γ : ℂ) * I) - 1 / 2) ^ 2 + (γ : ℂ) ^ 2
          = (γ : ℂ) ^ 2 * I ^ 2 + (γ : ℂ) ^ 2 := by ring
        _ = 0 := by rw [Complex.I_sq]; ring
    rw [this, zero_pow two_ne_zero]
  have hcrit_minus : quartetCritPoly γ (1 / 2 - (γ : ℂ) * I) = 0 := by
    unfold quartetCritPoly
    have : ((1 / 2 - (γ : ℂ) * I) - 1 / 2) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
      calc ((1 / 2 - (γ : ℂ) * I) - 1 / 2) ^ 2 + (γ : ℂ) ^ 2
          = (γ : ℂ) ^ 2 * I ^ 2 + (γ : ℂ) ^ 2 := by ring
        _ = 0 := by rw [Complex.I_sq]; ring
    rw [this, zero_pow two_ne_zero]
  exact ⟨Λc, hSc, hrel, hzero_half,
    by dsimp [Λc, C_num]; rw [hcrit_plus, mul_zero, mul_zero],
    by dsimp [Λc, C_num]; rw [hcrit_minus, mul_zero, mul_zero]⟩

/-- **Single-pole complex quartet contraction (`0 < a ≤ 1/4`, `Δκ = 1`).** Any complex off-critical
zero `1/2 + a + iγ` (`0 < a ≤ 1/4`, `γ ≠ 0`) of a `CompletedPositiveSystem κ d` together with its
dihedral quartet contracts onto `{1/2, 1/2 ± iγ}` inside `CompletedPositiveSystem (κ + 1) d`. -/
theorem CompletedPositiveSystem.contractComplexQuartet_of_le_quarter {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ)
    {a γ : ℝ} (ha0 : 0 < a) (ha_q : a ≤ 1 / 4) (hγ : γ ≠ 0)
    (hzero : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      CompletedPositiveSystem (κ + 1) d (fun s => F s * quartetSymSquareOne a γ s) Λc ∧
      (∀ s : ℂ, Λc s * quartetOffPoly a γ s =
        Λ s * ((s - 1 / 2) ^ 2 * quartetCritPoly γ s)) ∧
      Λc (1 / 2) = 0 ∧
      Λc (1 / 2 + (γ : ℂ) * I) = 0 ∧
      Λc (1 / 2 - (γ : ℂ) * I) = 0 :=
  contractComplexQuartet_of_posDef hS ha0 (by linarith) hγ 1 le_rfl
    (fun s => by simp [quartetSymSquareOne])
    (fun {σ} hσ => isEvenPosDef_quartetSymSquareOne ha0 ha_q hσ)
    hzero

/-- **Double-pole complex quartet contraction across the full strip (`0 < a < 1/2`, `Δκ = 2`).**
Any complex off-critical zero `1/2 + a + iγ` (`0 < a < 1/2`, `γ ≠ 0`) of a
`CompletedPositiveSystem κ d` together with its dihedral quartet contracts onto `{1/2, 1/2 ± iγ}`
inside `CompletedPositiveSystem (κ + 2) d`. -/
theorem CompletedPositiveSystem.contractComplexQuartet {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ)
    {a γ : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (hγ : γ ≠ 0)
    (hzero : Λ (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0) :
    ∃ Λc : ℂ → ℂ,
      CompletedPositiveSystem (κ + 2) d (fun s => F s * quartetSymSquareTwo a γ s) Λc ∧
      (∀ s : ℂ, Λc s * quartetOffPoly a γ s =
        Λ s * ((s - 1 / 2) ^ 4 * quartetCritPoly γ s)) ∧
      Λc (1 / 2) = 0 ∧
      Λc (1 / 2 + (γ : ℂ) * I) = 0 ∧
      Λc (1 / 2 - (γ : ℂ) * I) = 0 :=
  contractComplexQuartet_of_posDef hS ha0 ha1 hγ 2 (by omega)
    (fun s => by rfl)
    (fun {σ} hσ => isEvenPosDef_quartetSymSquareTwo ha0 ha1 hσ)
    hzero

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
