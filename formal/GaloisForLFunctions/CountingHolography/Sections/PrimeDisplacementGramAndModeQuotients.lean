import GaloisForLFunctions.CountingHolography.Sections.SharedMidpointEncodingOnPrimeDisplacementPlanes
import GaloisForLFunctions.ArithmeticOrientationGeometry.EventualHasseWeilIsHasseWeil
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations

/-!
# Prime-displacement Gram matrices, Gershgorin diagonal dominance, and mode quotients

This module studies the complete Gram matrix of families of signed prime-supported integer probes
`a : Fin m → (Fin N → ℤ)` under the polarized spline Krein pairing `probePairing`:

1. **Probe Gram matrices and Gershgorin diagonal dominance:**
   `probeGramMatrix N a` is the `m × m` Hermitian (real symmetric) matrix with entries
   `G_{rs} = probePairing N (a r) (a s)`. Its quadratic form on `ℤ^m` evaluates `integerProbe N`
   on linear combinations, and its negative index never exceeds `hermNegIndex (atomGram N)`.
   For `m = 2`, negative definiteness is `G₁₁ < 0 ∧ G₂₂ < 0 ∧ G₁₂² < G₁₁ G₂₂`.
   For arbitrary `m`, negative diagonals together with off-diagonal row sums
   `∑_{s ≠ r} |G_{rs}| / √(G_{rr} G_{ss}) < 1` force `hermNegIndex (probeGramMatrix N a) = m`.

2. **Co-scaled prime-cluster orthogonalization and the `m`-probe index law:**
   The zero-sum two-atom difference test `twoAtomDiffTest(u) = B(u) - B(u - log 2)` sees every
   right zero of any zero configuration (`seenRightZeros Z twoAtomDiffTest = rightZeros Z`).
   Spectral diagonalization of its real symmetric integer-window Gram matrices followed by rational
   approximation, denominator clearing, and co-scaled prime-cluster transport yields an exact
   equivalence for every `m`, prime cutoff `P₀`, and `ε ∈ (0, 1]`:
   `(m : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard` iff there exist `m` pairwise-disjoint signed
   prime-supported probes above `P₀` with `G_{rr} < 0` and normalized off-diagonal row sums `< ε`.
   Conjugate-pair symmetry upgrades any `2k + 1` negative-definite probes to `2k + 2` probes.

3. **Unconditional two-probe separation for `ζ` vs single-real-zero countermodel:**
   Every single negative integer probe `integerProbe N₀ a₀ < 0` for `ζ` unconditionally produces,
   above every prime cutoff `P₀` and for every `ε ∈ (0, 1]`, two pairwise-disjoint signed
   prime-supported probes `a₁, a₂` with `G₁₁ < 0`, `G₂₂ < 0`, `|G₁₂| < ε √(G₁₁ G₂₂)`, and
   `G₁₂² < G₁₁ G₂₂`. On an abstract functional-equation-symmetric tempered configuration with a
   single real right zero (`isolatedPairConfig` at `γ₀ = 0`), a negative test exists while no two
   real tests can satisfy `G₁₁ < 0`, `G₂₂ < 0`, and `G₁₂² < G₁₁ G₂₂`.

4. **Exponential off-diagonal blowup under asymptotic scale separation:**
   For every negative integer probe `u` (`integerProbe M u < 0`), its packet cannot be blind to the
   off-line zeros of `ζ`, so `blindAbove_of_eventually_le` forces exponential growth of the
   cross-scale autocorrelation `|probeAutocorr u Δ|`. Transporting two zero-sum copies of `u` to
   prime shells separated by any multiplicative ratio `R ≥ 2` produces `G₁₁ < 0`, `G₂₂ < 0`, and
   `G₁₂² > B · G₁₁ G₂₂` for every `B > 0`.

5. **Finite-mode quotient positivity and near-annihilating prime probes:**
   For any finite set `S₀ ⊂ {s : 1/2 < Re s}`, `rightZeros zetaZeroConfig ⊆ S₀` makes `atomGram N`
   positive definite on `ker (modeEvalMap S₀ N)` and gives an `N`-independent constant `η > 0` such
   that every negative probe has `modePairProduct ρ N a ≥ η · (-integerProbe N a)` for some
   `ρ ∈ S₀`. Conversely, any right zero outside `S₀ ∪ conj S₀` produces signed prime-supported
   negative probes above every `P₀` with `modePairProduct ρ N a < δ · (-integerProbe N a)` on `S₀`.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset Matrix Complex
open scoped ComplexConjugate Real
open Zeta23
open ArithmeticScatteringHolography CountingHolography HTGeometry
open HeckeKreinToeplitz RenormalizedIntersectionTheory ExclusionOfTheCriticalState
open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline)
open SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig offLinePoint
  isolatedPairConfig temperedConfig_isolatedPairConfig isolatedPairConfig_weil_nonneg_nyquist_iff)

/-! ### 1. Probe Gram matrices and Gershgorin diagonal dominance -/

/-- Polarized real spline pairing on integer probes `a, b : Fin N → ℤ`. -/
def probePairing (N : ℕ) (a b : Fin N → ℤ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, (atomGram N i j).re * (a i : ℝ) * (b j : ℝ)

/-- Complete `m × m` Hermitian Gram matrix of a family `a : Fin m → (Fin N → ℤ)` of integer probes. -/
def probeGramMatrix {m : ℕ} (N : ℕ) (a : Fin m → (Fin N → ℤ)) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun r s => (probePairing N (a r) (a s) : ℂ)

theorem atomGram_re_symm (N : ℕ) (i j : Fin N) :
    (atomGram N i j).re = (atomGram N j i).re := by
  have hH : starRingEnd ℂ (atomGram N j i) = atomGram N i j :=
    congr_fun (congr_fun (atomGram_isHermitian N) i) j
  simpa using (congr_arg Complex.re hH).symm

@[simp] theorem probePairing_self (N : ℕ) (a : Fin N → ℤ) :
    probePairing N a a = integerProbe N a :=
  (integerProbe_eq_sum N a).symm

theorem probePairing_symm (N : ℕ) (a b : Fin N → ℤ) :
    probePairing N a b = probePairing N b a := by
  unfold probePairing
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [atomGram_re_symm N i j]; ring

theorem probePairing_eq_polar (N : ℕ) (a b : Fin N → ℤ) :
    probePairing N a b = (integerProbe N (a + b) - integerProbe N a - integerProbe N b) / 2 := by
  have hsym := probePairing_symm N b a
  have hexp : integerProbe N (a + b) =
      probePairing N a a + probePairing N b b + probePairing N a b + probePairing N b a := by
    rw [integerProbe_eq_sum]
    unfold probePairing
    simp only [Pi.add_apply, Int.cast_add]
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    ring
  rw [hexp, probePairing_self, probePairing_self, hsym]
  ring

theorem probeGramMatrix_isHermitian {m : ℕ} (N : ℕ) (a : Fin m → (Fin N → ℤ)) :
    (probeGramMatrix N a).IsHermitian := by
  ext r s
  simp [probeGramMatrix, probePairing_symm N (a s) (a r)]

theorem probeGramMatrix_im {m : ℕ} (N : ℕ) (a : Fin m → (Fin N → ℤ)) (r s : Fin m) :
    (probeGramMatrix N a r s).im = 0 := by
  simp [probeGramMatrix]

/-- The Hermitian quadratic form of a complex matrix with real entries splits into real and
imaginary parts. -/
theorem hermQuad_ofReal_matrix {m : ℕ} (G : Fin m → Fin m → ℝ) (z : Fin m → ℂ) :
    hermQuad (Matrix.of fun r s => (G r s : ℂ)) z =
      realQuad G (fun r => (z r).re) + realQuad G (fun r => (z r).im) := by
  simp only [hermQuad, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
    Complex.re_sum, realQuad, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem hermQuad_probeGramMatrix_eq_atomGram {m : ℕ} (N : ℕ) (a : Fin m → (Fin N → ℤ))
    (z : Fin m → ℂ) :
    hermQuad (probeGramMatrix N a) z =
      hermQuad (atomGram N) (fun i => ∑ r : Fin m, (a r i : ℂ) * z r) := by
  have hreal (i j : Fin N) : atomGram N i j = ((atomGram N i j).re : ℂ) :=
    Complex.ext rfl (by simpa using atomGram_im N i j)
  unfold hermQuad probeGramMatrix probePairing
  congr 1
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Complex.star_def,
    map_sum, map_mul, map_intCast, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  simp_rw [hreal, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

/-- Evaluating `probeGramMatrix` on an integer coefficient vector computes `integerProbe` on the
resulting linear combination. -/
theorem hermQuad_probeGramMatrix_int {m : ℕ} (N : ℕ) (a : Fin m → (Fin N → ℤ)) (c : Fin m → ℤ) :
    hermQuad (probeGramMatrix N a) (fun r => (c r : ℂ)) =
      integerProbe N (∑ r : Fin m, c r • a r) := by
  rw [hermQuad_probeGramMatrix_eq_atomGram]
  unfold integerProbe
  congr 1
  funext i
  simp [Finset.sum_apply, zsmul_eq_mul, mul_comm]

/-- The negative index of any probe Gram matrix at horizon `N` is bounded by the negative index of
`atomGram N`. -/
theorem hermNegIndex_probeGramMatrix_le {m : ℕ} (N : ℕ) (a : Fin m → (Fin N → ℤ)) :
    hermNegIndex (probeGramMatrix N a) ≤ hermNegIndex (atomGram N) := by
  let L : (Fin m → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun z i => ∑ r : Fin m, (a r i : ℂ) * z r
      map_add' := fun x y => funext fun i => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => funext fun i => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring }
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-(probeGramMatrix N a))
  have hinj : Function.Injective (L.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have hxv : (x : Fin m → ℂ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hpos := hW x x.2 hxv
    rw [hermQuad_neg, hermQuad_probeGramMatrix_eq_atomGram] at hpos
    have hLx : L x = 0 := LinearMap.mem_ker.mp hx
    change hermQuad (atomGram N) (L x) < 0 at hpos
    rw [hLx] at hpos
    simp [hermQuad] at hpos
  have hmap : IsPosDefOn (-atomGram N) (W.map L) := by
    rintro y ⟨x, hx, rfl⟩ hy0
    have hx0 : x ≠ 0 := fun h => hy0 (by simp [h])
    have hpos := hW x hx hx0
    rwa [hermQuad_neg, hermQuad_probeGramMatrix_eq_atomGram, ← hermQuad_neg] at hpos
  have hle := finrank_le_posIndex hmap
  have heq : Module.finrank ℂ W ≤ Module.finrank ℂ (W.map L) := by
    have hdom := LinearMap.finrank_le_finrank_of_injective hinj
    have hrange : LinearMap.range (L.domRestrict W) = W.map L := by
      ext y; simp [LinearMap.domRestrict]
    rwa [hrange] at hdom
  unfold hermNegIndex
  omega

/-- An `m × m` matrix has full negative index `m` iff its Hermitian quadratic form is strictly
negative on every nonzero vector. -/
theorem hermNegIndex_eq_card_iff_negDef {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) :
    hermNegIndex H = m ↔ ∀ z : Fin m → ℂ, z ≠ 0 → hermQuad H z < 0 := by
  constructor
  · intro hm z hz
    obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
    rw [ ← hermNegIndex, hm] at hrank
    have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq
      (hrank.trans (Module.finrank_fintype_fun_eq_card ℂ).symm)
    have hpos := hW z (htop ▸ Submodule.mem_top) hz
    rw [hermQuad_neg] at hpos
    linarith
  · intro hneg
    apply le_antisymm
    · obtain ⟨W, hrank, _⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
      change hermPosIndex (-H) ≤ m
      rw [← hrank]
      simpa using Submodule.finrank_le W
    · have htop : IsPosDefOn (-H) ⊤ := fun z _ hz => by
        rw [hermQuad_neg]; linarith [hneg z hz]
      have hle := finrank_le_posIndex htop
      rwa [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle

/-- Exact negative-definiteness criterion for a real symmetric `2 × 2` Hermitian matrix. -/
theorem hermNegIndex_two_ofReal_iff (g₁₁ g₁₂ g₂₂ : ℝ) :
    hermNegIndex (Matrix.of ![![(g₁₁ : ℂ), (g₁₂ : ℂ)], ![(g₁₂ : ℂ), (g₂₂ : ℂ)]]) = 2 ↔
      g₁₁ < 0 ∧ g₂₂ < 0 ∧ g₁₂ ^ 2 < g₁₁ * g₂₂ := by
  set G : Fin 2 → Fin 2 → ℝ := ![![g₁₁, g₁₂], ![g₁₂, g₂₂]]
  have hM : (Matrix.of ![![(g₁₁ : ℂ), (g₁₂ : ℂ)], ![(g₁₂ : ℂ), (g₂₂ : ℂ)]]) =
      Matrix.of fun r s => (G r s : ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hQ (x : Fin 2 → ℝ) : realQuad G x =
      g₁₁ * (x 0) ^ 2 + 2 * g₁₂ * x 0 * x 1 + g₂₂ * (x 1) ^ 2 := by
    unfold realQuad
    simp only [Fin.sum_univ_two, G, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  rw [hM, hermNegIndex_eq_card_iff_negDef]
  constructor
  · intro hneg
    have h1 : g₁₁ < 0 := by
      have h := hneg ![1, 0] (fun h0 => one_ne_zero (congrFun h0 0))
      rw [hermQuad_ofReal_matrix, hQ, hQ] at h
      simp at h; linarith
    have h2 : g₂₂ < 0 := by
      have h := hneg ![0, 1] (fun h0 => one_ne_zero (congrFun h0 1))
      rw [hermQuad_ofReal_matrix, hQ, hQ] at h
      simp at h; linarith
    have h3 : g₁₂ ^ 2 < g₁₁ * g₂₂ := by
      let z : Fin 2 → ℂ := ![(-g₁₂ : ℂ), (g₁₁ : ℂ)]
      have hz : z ≠ 0 := by
        intro h0
        have := congrArg Complex.re (congrFun h0 1)
        simp [z] at this
        linarith
      have h := hneg z hz
      rw [hermQuad_ofReal_matrix, hQ, hQ] at h
      simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im] at h
      have hid : g₁₁ * (-g₁₂) ^ 2 + 2 * g₁₂ * (-g₁₂) * g₁₁ + g₂₂ * g₁₁ ^ 2 +
          (g₁₁ * (-0) ^ 2 + 2 * g₁₂ * (-0) * 0 + g₂₂ * 0 ^ 2) =
          g₁₁ * (g₁₁ * g₂₂ - g₁₂ ^ 2) := by ring
      rw [hid] at h
      nlinarith
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, hdet⟩ z hz
    have hreal_nonpos (x : Fin 2 → ℝ) : realQuad G x ≤ 0 := by
      rw [hQ]
      have hid : (-g₁₁) * (g₁₁ * (x 0) ^ 2 + 2 * g₁₂ * x 0 * x 1 + g₂₂ * (x 1) ^ 2) =
          -(g₁₁ * x 0 + g₁₂ * x 1) ^ 2 - (g₁₁ * g₂₂ - g₁₂ ^ 2) * (x 1) ^ 2 := by ring
      have hprod : (-g₁₁) * (g₁₁ * (x 0) ^ 2 + 2 * g₁₂ * x 0 * x 1 + g₂₂ * (x 1) ^ 2) ≤ 0 := by
        rw [hid]
        nlinarith [sq_nonneg (g₁₁ * x 0 + g₁₂ * x 1), sq_nonneg (x 1)]
      nlinarith
    have hreal_neg (x : Fin 2 → ℝ) (hx : x 0 ≠ 0 ∨ x 1 ≠ 0) : realQuad G x < 0 := by
      rw [hQ]
      by_cases hx1 : x 1 = 0
      · have hx0 : x 0 ≠ 0 := hx.resolve_right hx1
        rw [hx1]
        have hsq : 0 < (x 0) ^ 2 := sq_pos_of_ne_zero hx0
        nlinarith
      · have hid : (-g₁₁) * (g₁₁ * (x 0) ^ 2 + 2 * g₁₂ * x 0 * x 1 + g₂₂ * (x 1) ^ 2) =
            -(g₁₁ * x 0 + g₁₂ * x 1) ^ 2 - (g₁₁ * g₂₂ - g₁₂ ^ 2) * (x 1) ^ 2 := by ring
        have hsq1 : 0 < (x 1) ^ 2 := sq_pos_of_ne_zero hx1
        have hprod : (-g₁₁) * (g₁₁ * (x 0) ^ 2 + 2 * g₁₂ * x 0 * x 1 + g₂₂ * (x 1) ^ 2) < 0 := by
          rw [hid]
          nlinarith [sq_nonneg (g₁₁ * x 0 + g₁₂ * x 1)]
        nlinarith
    rw [hermQuad_ofReal_matrix]
    have hnz : ((z 0).re ≠ 0 ∨ (z 1).re ≠ 0) ∨ ((z 0).im ≠ 0 ∨ (z 1).im ≠ 0) := by
      by_contra! hall
      apply hz
      funext i
      fin_cases i
      · exact Complex.ext hall.1.1 hall.2.1
      · exact Complex.ext hall.1.2 hall.2.2
    rcases hnz with hre | him
    · linarith [hreal_neg _ hre, hreal_nonpos (fun r => (z r).im)]
    · linarith [hreal_nonpos (fun r => (z r).re), hreal_neg _ him]

/-- Two integer probes span a negative-definite `2 × 2` Gram matrix iff both have strictly negative
Krein square and `G₁₂² < G₁₁ G₂₂`. -/
theorem twoProbe_negDef_iff_det {N : ℕ} (a₁ a₂ : Fin N → ℤ) :
    hermNegIndex (probeGramMatrix N ![a₁, a₂]) = 2 ↔
      probePairing N a₁ a₁ < 0 ∧ probePairing N a₂ a₂ < 0 ∧
        (probePairing N a₁ a₂) ^ 2 < probePairing N a₁ a₁ * probePairing N a₂ a₂ := by
  have heq : probeGramMatrix N ![a₁, a₂] =
      Matrix.of ![![(probePairing N a₁ a₁ : ℂ), (probePairing N a₁ a₂ : ℂ)],
        ![(probePairing N a₁ a₂ : ℂ), (probePairing N a₂ a₂ : ℂ)]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [probeGramMatrix, probePairing_symm N a₂ a₁]
  rw [heq]
  exact hermNegIndex_two_ofReal_iff _ _ _

/-- **Gershgorin diagonal-dominance criterion for negative-definite probe Gram matrices.**
If every probe has `G_{rr} < 0` and normalized off-diagonal row sum
`∑_{s ≠ r} |G_{rs}| / √(G_{rr} G_{ss}) < 1`, then `probeGramMatrix N a` has full negative index `m`. -/
theorem hermNegIndex_eq_of_gershgorin_row_lt_one {m N : ℕ} (a : Fin m → (Fin N → ℤ))
    (hdiag : ∀ r : Fin m, probePairing N (a r) (a r) < 0)
    (hrow : ∀ r : Fin m,
      ∑ s ∈ Finset.univ.erase r,
        |probePairing N (a r) (a s)| /
          Real.sqrt (probePairing N (a r) (a r) * probePairing N (a s) (a s)) < 1) :
    hermNegIndex (probeGramMatrix N a) = m := by
  set G : Fin m → Fin m → ℝ := fun r s => probePairing N (a r) (a s)
  let d : Fin m → ℝ := fun r => Real.sqrt (-G r r)
  have hd_pos (r : Fin m) : 0 < d r := Real.sqrt_pos.mpr (neg_pos.mpr (hdiag r))
  have hd_sq (r : Fin m) : d r ^ 2 = -G r r := Real.sq_sqrt (neg_nonneg.mpr (hdiag r).le)
  have hd_mul (r s : Fin m) : d r * d s = Real.sqrt (G r r * G s s) := by
    dsimp [d]
    rw [← Real.sqrt_mul (neg_nonneg.mpr (hdiag r).le), neg_mul_neg]
  let K : Fin m → Fin m → ℝ := fun r s => |G r s| / (d r * d s)
  have hK_symm (r s : Fin m) : K r s = K s r := by
    dsimp [K]
    rw [probePairing_symm N (a r) (a s), mul_comm (d r) (d s)]
  have hK_nn (r s : Fin m) : 0 ≤ K r s :=
    div_nonneg (abs_nonneg _) (mul_pos (hd_pos r) (hd_pos s)).le
  have hrow' (r : Fin m) : ∑ s ∈ Finset.univ.erase r, K r s < 1 := by
    simpa only [K, hd_mul] using hrow r
  have hreal_le (x : Fin m → ℝ) :
      realQuad G x ≤ -∑ r : Fin m, (d r * x r) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r, K r s) := by
    let y : Fin m → ℝ := fun r => d r * x r
    have hsplit (r : Fin m) :
        ∑ s : Fin m, G r s * x r * x s =
          -y r ^ 2 + ∑ s ∈ Finset.univ.erase r, G r s * x r * x s := by
      rw [← Finset.add_sum_erase Finset.univ (fun s => G r s * x r * x s) (Finset.mem_univ r)]
      have hrr : G r r * x r * x r = -y r ^ 2 := by
        dsimp [y]; rw [mul_pow, hd_sq r]; ring
      rw [hrr]
    have hterm (r s : Fin m) :
        G r s * x r * x s ≤ K r s * (y r ^ 2 + y s ^ 2) / 2 := by
      have hdr : (d r) ≠ 0 := (hd_pos r).ne'
      have hds : (d s) ≠ 0 := (hd_pos s).ne'
      have hid : G r s * x r * x s = (G r s / (d r * d s)) * (y r * y s) := by
        dsimp [y]; field_simp
      have habs : (G r s / (d r * d s)) * (y r * y s) ≤ K r s * (|y r| * |y s|) := by
        calc (G r s / (d r * d s)) * (y r * y s)
            ≤ |(G r s / (d r * d s)) * (y r * y s)| := le_abs_self _
          _ = K r s * (|y r| * |y s|) := by
              rw [abs_mul, abs_div, abs_mul, abs_of_pos (hd_pos r), abs_of_pos (hd_pos s), abs_mul]
      have ham : |y r| * |y s| ≤ (y r ^ 2 + y s ^ 2) / 2 := by
        nlinarith [sq_abs (y r), sq_abs (y s), sq_nonneg (|y r| - |y s|)]
      calc G r s * x r * x s ≤ K r s * (|y r| * |y s|) := by rwa [hid]
        _ ≤ K r s * ((y r ^ 2 + y s ^ 2) / 2) := mul_le_mul_of_nonneg_left ham (hK_nn r s)
        _ = K r s * (y r ^ 2 + y s ^ 2) / 2 := by ring
    have hoff_bound :
        (∑ r : Fin m, ∑ s ∈ Finset.univ.erase r, G r s * x r * x s) ≤
          ∑ r : Fin m, y r ^ 2 * ∑ s ∈ Finset.univ.erase r, K r s := by
      have hle1 : (∑ r : Fin m, ∑ s ∈ Finset.univ.erase r, G r s * x r * x s) ≤
          ∑ r : Fin m, ∑ s ∈ Finset.univ.erase r, K r s * (y r ^ 2 + y s ^ 2) / 2 :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hterm r s
      have hsym_sum :
          (∑ r : Fin m, ∑ s ∈ Finset.univ.erase r, K r s * y s ^ 2) =
            ∑ r : Fin m, y r ^ 2 * ∑ s ∈ Finset.univ.erase r, K r s := by
        have h1 : ∀ r : Fin m, ∑ s ∈ Finset.univ.erase r, K r s * y s ^ 2 =
            ∑ s : Fin m, if s = r then 0 else K r s * y s ^ 2 := fun r => by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext s; simp
        simp_rw [h1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        have h2 : (∑ r : Fin m, if s = r then 0 else K r s * y s ^ 2) =
            ∑ r ∈ Finset.univ.erase s, y s ^ 2 * K s r := by
          rw [← Finset.sum_filter]
          refine (Finset.sum_congr ?_ fun r _ => ?_)
          · ext r; simp [eq_comm]
          · rw [hK_symm r s, mul_comm]
        rw [h2, ← Finset.mul_sum]
      have havg :
          (∑ r : Fin m, ∑ s ∈ Finset.univ.erase r, K r s * (y r ^ 2 + y s ^ 2) / 2) =
            ∑ r : Fin m, y r ^ 2 * ∑ s ∈ Finset.univ.erase r, K r s := by
        have hlin (r : Fin m) :
            (∑ s ∈ Finset.univ.erase r, K r s * (y r ^ 2 + y s ^ 2) / 2) =
              (y r ^ 2 * ∑ s ∈ Finset.univ.erase r, K r s) / 2 +
                (∑ s ∈ Finset.univ.erase r, K r s * y s ^ 2) / 2 := by
          rw [Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => by ring
        simp_rw [hlin, Finset.sum_add_distrib, ← Finset.sum_div, hsym_sum]
        ring
      exact hle1.trans_eq havg
    unfold realQuad
    simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have htarget :
        -∑ r : Fin m, y r ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r, K r s) =
          -(∑ r : Fin m, y r ^ 2) + ∑ r : Fin m, y r ^ 2 * ∑ s ∈ Finset.univ.erase r, K r s := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    linarith only [hoff_bound, htarget]
  rw [hermNegIndex_eq_card_iff_negDef]
  intro z hz
  rw [show probeGramMatrix N a = Matrix.of (fun r s => (G r s : ℂ)) from rfl,
    hermQuad_ofReal_matrix]
  obtain ⟨r₀, hr₀⟩ : ∃ r : Fin m, z r ≠ 0 := by
    by_contra! hall; exact hz (funext hall)
  have hre_le := hreal_le (fun r => (z r).re)
  have him_le := hreal_le (fun r => (z r).im)
  have hterm_nn (x : Fin m → ℝ) (r : Fin m) :
      0 ≤ (d r * x r) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r, K r s) :=
    mul_nonneg (sq_nonneg _) (sub_pos.mpr (hrow' r)).le
  have hsum_re_nn :
      0 ≤ ∑ r : Fin m, (d r * (z r).re) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r, K r s) :=
    Finset.sum_nonneg fun r _ => hterm_nn _ r
  have hsum_im_nn :
      0 ≤ ∑ r : Fin m, (d r * (z r).im) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r, K r s) :=
    Finset.sum_nonneg fun r _ => hterm_nn _ r
  have hnz_part : (z r₀).re ≠ 0 ∨ (z r₀).im ≠ 0 := by
    by_contra! hboth; exact hr₀ (Complex.ext hboth.1 hboth.2)
  rcases hnz_part with hre0 | him0
  · have hpos0 : 0 < (d r₀ * (z r₀).re) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r₀, K r₀ s) :=
      mul_pos (sq_pos_of_ne_zero (mul_ne_zero (hd_pos r₀).ne' hre0)) (sub_pos.mpr (hrow' r₀))
    have hgt : 0 < ∑ r : Fin m, (d r * (z r).re) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r, K r s) :=
      Finset.sum_pos' (fun r _ => hterm_nn _ r) ⟨r₀, Finset.mem_univ r₀, hpos0⟩
    linarith only [hre_le, him_le, hgt, hsum_im_nn]
  · have hpos0 : 0 < (d r₀ * (z r₀).im) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r₀, K r₀ s) :=
      mul_pos (sq_pos_of_ne_zero (mul_ne_zero (hd_pos r₀).ne' him0)) (sub_pos.mpr (hrow' r₀))
    have hgt : 0 < ∑ r : Fin m, (d r * (z r).im) ^ 2 * (1 - ∑ s ∈ Finset.univ.erase r, K r s) :=
      Finset.sum_pos' (fun r _ => hterm_nn _ r) ⟨r₀, Finset.mem_univ r₀, hpos0⟩
    linarith only [hre_le, him_le, hsum_re_nn, hgt]

/-! ### 2. Shifted prime-cluster approximations and the zero-loss `m`-probe index law -/

/-- Unified short-interval prime-block supply: for `m` blocks of length `M` with nonnegative
logarithmic shifts `Δ : Fin m → ℝ`, every sufficiently large base scale `T` admits `m · M`
pairwise-distinct primes above `P₀` approximating `T + Δ r + log(i + 1)` within `2 e^{-T/3}`. -/
theorem exists_shifted_primeBlocks_log_approx (m M P₀ : ℕ) (Δ : Fin m → ℝ)
    (hΔ : ∀ r : Fin m, 0 ≤ Δ r) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ T : ℝ, U ≤ T →
      ∃ (N : ℕ) (ι : Fin m → Fin M → Fin N),
        Function.Injective (fun p : Fin m × Fin M => ι p.1 p.2) ∧
        (∀ (r : Fin m) (i : Fin M),
          ((ι r i).val + 1).Prime ∧ P₀ < (ι r i).val + 1 ∧
          Real.log (((ι r i).val : ℝ) + 1) ≤ T + Δ r + Real.log ((i : ℝ) + 1) ∧
          (T + Δ r + Real.log ((i : ℝ) + 1)) - Real.log (((ι r i).val : ℝ) + 1) ≤
            2 * Real.exp (-(1 / 3 : ℝ) * T)) := by
  let L := m * M
  let eqv : Fin L ≃ Fin m × Fin M := finProdFinEquiv.symm
  obtain ⟨U, hU0, hU⟩ :=
    SurfaceOfSpecZ.ScaleLocality.exists_log_prime_avoiding_small_finset
      (γ := 0) (β := 2 / 3) (C := (L + P₀ + 3 : ℝ))
      le_rfl (by norm_num) (by norm_num) (by norm_num) (by positivity)
  refine ⟨U, hU0, fun T hTU => ?_⟩
  have hind : ∀ k : ℕ, (hk : k ≤ L) →
      ∃ f : Fin k → ℕ, Function.Injective f ∧
        ∀ j : Fin k,
          let p := eqv ⟨j.val, j.isLt.trans_le hk⟩
          (f j).Prime ∧ P₀ < f j ∧
          Real.log (f j) ≤ T + Δ p.1 + Real.log ((p.2 : ℝ) + 1) ∧
          (T + Δ p.1 + Real.log ((p.2 : ℝ) + 1)) - Real.log (f j) ≤
            2 * Real.exp (-(1 / 3 : ℝ) * T) := by
    intro k
    induction k with
    | zero =>
      exact fun _ => ⟨Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ k ih =>
      intro hkL
      obtain ⟨f, hf_inj, hf_props⟩ := ih (by omega)
      let p₀ := eqv ⟨k, hkL⟩
      let E : Finset ℕ := Finset.range (P₀ + 2) ∪ Finset.univ.image f
      let u := T + Δ p₀.1 + Real.log ((p₀.2 : ℝ) + 1)
      have hlog_nn : 0 ≤ Real.log ((p₀.2 : ℝ) + 1) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) p₀.2])
      have hΔ_nn : 0 ≤ Δ p₀.1 := hΔ p₀.1
      have hu_ge : U ≤ u := by dsimp [u]; linarith only [hTU, hΔ_nn, hlog_nn]
      have hE_card : (E.card : ℝ) ≤ (L + P₀ + 3 : ℝ) * Real.exp (0 * u) := by
        rw [zero_mul, Real.exp_zero, mul_one]
        have hc₁ : E.card ≤ (Finset.range (P₀ + 2)).card + (Finset.univ.image f).card :=
          Finset.card_union_le _ _
        have hc₂ : (Finset.univ.image f).card ≤ k :=
          (Finset.card_image_le (s := Finset.univ) (f := f)).trans_eq
            (by rw [Finset.card_univ, Fintype.card_fin])
        rw [Finset.card_range] at hc₁
        exact_mod_cast (by omega : E.card ≤ L + P₀ + 3)
      obtain ⟨q, hq_prime, hq_not, _, hq_le, hq_gap⟩ := hU u hu_ge E hE_card
      have hq_gt : P₀ < q := by
        by_contra! hle
        exact hq_not (Finset.mem_union_left _ (Finset.mem_range.mpr (by omega)))
      have hq_ne (j : Fin k) : q ≠ f j := fun h =>
        hq_not (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h.symm⟩))
      have hexp_le : 2 * Real.exp ((2 / 3 - 1 : ℝ) * u) ≤ 2 * Real.exp (-(1 / 3 : ℝ) * T) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        dsimp [u]; linarith only [hΔ_nn, hlog_nn]
      let f' : Fin (k + 1) → ℕ := fun j => if h : j.val < k then f ⟨j.val, h⟩ else q
      refine ⟨f', ?_, ?_⟩
      · intro j₁ j₂ hj
        dsimp only [f'] at hj
        by_cases h₁ : j₁.val < k <;> by_cases h₂ : j₂.val < k
        · rw [dif_pos h₁, dif_pos h₂] at hj
          exact Fin.ext (Fin.mk.inj_iff.mp (hf_inj hj))
        · rw [dif_pos h₁, dif_neg h₂] at hj
          exact (hq_ne ⟨j₁.val, h₁⟩ hj.symm).elim
        · rw [dif_neg h₁, dif_pos h₂] at hj
          exact (hq_ne ⟨j₂.val, h₂⟩ hj).elim
        · have := j₁.isLt; have := j₂.isLt
          exact Fin.ext (by omega)
      · intro j
        dsimp only [f']
        split_ifs with hj
        ·exact hf_props ⟨j.val, hj⟩
        · have hjk : (⟨j.val, j.isLt.trans_le hkL⟩ : Fin L) = ⟨k, hkL⟩ := by
            have := j.isLt; exact Fin.ext (by omega)
          rw [hjk]
          exact ⟨hq_prime, hq_gt, hq_le, hq_gap.trans hexp_le⟩
  obtain ⟨f, hf_inj, hf_props⟩ := hind L le_rfl
  let N := (Finset.univ.image f).sup id + 1
  let ι : Fin m → Fin M → Fin N := fun r i =>
    let j := eqv.symm (r, i)
    ⟨f j - 1, by
      have hle : f j ≤ (Finset.univ.image f).sup id :=
        Finset.le_sup (f := id) (Finset.mem_image_of_mem f (Finset.mem_univ j))
      have hpos : 0 < f j := (hf_props j).1.pos
      omega⟩
  have hι_val (r : Fin m) (i : Fin M) : (ι r i).val + 1 = f (eqv.symm (r, i)) := by
    dsimp [ι]
    have hpos : 0 < f (eqv.symm (r, i)) := (hf_props (eqv.symm (r, i))).1.pos
    omega
  refine ⟨N, ι, ?_, fun r i => ?_⟩
  · rintro ⟨r₁, i₁⟩ ⟨r₂, i₂⟩ hij
    have hv := congrArg Fin.val hij
    have h₁ := hι_val r₁ i₁
    have h₂ := hι_val r₂ i₂
    have hfeq : f (eqv.symm (r₁, i₁)) = f (eqv.symm (r₂, i₂)) := by omega
    exact eqv.symm.injective (hf_inj hfeq)
  · let j := eqv.symm (r, i)
    have hp := hf_props j
    have heqv : eqv ⟨j.val, j.isLt⟩ = (r, i) := by simp [j]
    rw [heqv] at hp
    have hc : (((ι r i).val : ℝ) + 1) = (f j : ℝ) := by exact_mod_cast hι_val r i
    rw [hι_val r i, hc]
    exact hp

private theorem extend_probePairing_eq {M N : ℕ} {ι₁ ι₂ : Fin M → Fin N}
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂) (u₁ u₂ : Fin M → ℤ) :
    probePairing N (Function.extend ι₁ u₁ 0) (Function.extend ι₂ u₂ 0) =
      ∑ i : Fin M, ∑ j : Fin M,
        (atomGram N (ι₁ i) (ι₂ j)).re * (u₁ i : ℝ) * (u₂ j : ℝ) := by
  have hsum_ext {ι : Fin M → Fin N} (hι : Function.Injective ι) (w : Fin N → ℝ) (u : Fin M → ℤ) :
      (∑ ℓ : Fin N, w ℓ * ((Function.extend ι u 0 ℓ : ℤ) : ℝ)) =
        ∑ i : Fin M, w (ι i) * (u i : ℝ) := by
    have hoff : ∀ ℓ : Fin N, ℓ ∉ Finset.univ.image ι →
        w ℓ * ((Function.extend ι u 0 ℓ : ℤ) : ℝ) = 0 := by
      intro ℓ hℓ
      have hz : Function.extend ι u 0 ℓ = 0 :=
        Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      rw [hz, Int.cast_zero, mul_zero]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)) fun ℓ _ hℓ => hoff ℓ hℓ,
      Finset.sum_image fun i _ j _ h => hι h]
    exact Finset.sum_congr rfl fun i _ => by rw [hι.extend_apply]
  unfold probePairing
  have houter :
      (∑ ℓ : Fin N, ∑ ℓ' : Fin N,
        (atomGram N ℓ ℓ').re * ((Function.extend ι₁ u₁ 0 ℓ : ℤ) : ℝ) *
          ((Function.extend ι₂ u₂ 0 ℓ' : ℤ) : ℝ)) =
      ∑ ℓ : Fin N,
        (∑ ℓ' : Fin N, (atomGram N ℓ ℓ').re * ((Function.extend ι₂ u₂ 0 ℓ' : ℤ) : ℝ)) *
          ((Function.extend ι₁ u₁ 0 ℓ : ℤ) : ℝ) := by
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun ℓ' _ => by ring
  rw [houter, hsum_ext hι₁ _ u₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum_ext hι₂ (fun ℓ' => (atomGram N (ι₁ i) ℓ').re) u₂, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem isSignedPrimeSupported_extend {M N P₀ : ℕ} {ι : Fin M → Fin N}
    (hι : Function.Injective ι)
    (hp : ∀ i : Fin M, ((ι i).val + 1).Prime ∧ P₀ < (ι i).val + 1)
    {u : Fin M → ℤ} (hu_ne : u ≠ 0) (hu_sum : (∑ i : Fin M, u i) = 0) :
    isSignedPrimeSupported (Function.extend ι u 0) ∧
      (∀ ℓ : Fin N, Function.extend ι u 0 ℓ ≠ 0 → P₀ < ℓ.val + 1) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by simpa [funext_iff] using hu_ne
  have hpos_u : ∃ i₁ : Fin M, 0 < u i₁ := by
    by_contra! hle
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · have hsplit := Finset.add_sum_erase Finset.univ u (Finset.mem_univ i₀)
      have hrest : ∑ i ∈ Finset.univ.erase i₀, u i ≤ 0 := Finset.sum_nonpos fun i _ => hle i
      linarith only [hsplit, hu_sum, hrest, hneg]
    · exact (hle i₀).not_gt hpos
  have hneg_u : ∃ i₂ : Fin M, u i₂ < 0 := by
    by_contra! hge
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · exact (hge i₀).not_gt hneg
    · have hsplit := Finset.add_sum_erase Finset.univ u (Finset.mem_univ i₀)
      have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase i₀, u i := Finset.sum_nonneg fun i _ => hge i
      linarith only [hsplit, hu_sum, hrest, hpos]
  obtain ⟨i₁, hi₁⟩ := hpos_u
  obtain ⟨i₂, hi₂⟩ := hneg_u
  have hsupp {ℓ : Fin N} (hℓ : Function.extend ι u 0 ℓ ≠ 0) :
      (ℓ.val + 1).Prime ∧ P₀ < ℓ.val + 1 := by
    by_cases hex : ∃ i : Fin M, ι i = ℓ
    · obtain ⟨i, rfl⟩ := hex; exact hp i
    · exact (hℓ (Function.extend_apply' _ _ _ hex)).elim
  have hsum : (∑ ℓ : Fin N, Function.extend ι u 0 ℓ) = 0 := by
    have hoff : ∀ ℓ : Fin N, ℓ ∉ Finset.univ.image ι → Function.extend ι u 0 ℓ = 0 := fun ℓ hℓ =>
      Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)) fun ℓ _ hℓ => hoff ℓ hℓ,
      Finset.sum_image fun i _ j _ h => hι h]
    have hcongr : (∑ i : Fin M, Function.extend ι u 0 (ι i)) = ∑ i : Fin M, u i :=
      Finset.sum_congr rfl fun i _ => hι.extend_apply u 0 i
    rw [hcongr, hu_sum]
  exact ⟨⟨fun ℓ hℓ => (hsupp hℓ).1, hsum,
    ⟨ι i₁, by simpa only [hι.extend_apply] using hi₁⟩,
    ⟨ι i₂, by simpa only [hι.extend_apply] using hi₂⟩⟩,
    fun ℓ hℓ => (hsupp hℓ).2⟩

/-- Co-scaled prime-cluster convergence: `m` nonzero zero-sum integer probes `u r : Fin M → ℤ` can
be transported simultaneously to `m` pairwise-disjoint signed prime-supported probes above any
cutoff `P₀` with every entry `(r, s)` of their probe Gram matrix arbitrarily close to
`probePairing M (u r) (u s)`. -/
theorem exists_coScaled_disjoint_primeProbes_near {m M : ℕ} (u : Fin m → (Fin M → ℤ))
    (hu_ne : ∀ r : Fin m, u r ≠ 0) (hu_sum : ∀ r : Fin m, (∑ i : Fin M, u r i) = 0)
    (P₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (a : Fin m → (Fin N → ℤ)),
      P₀ < N ∧
      (∀ r : Fin m, isSignedPrimeSupported (a r)) ∧
      (∀ (r : Fin m) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
      (∀ r s : Fin m, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
      (∀ r s : Fin m, |probePairing N (a r) (a s) - probePairing M (u r) (u s)| < δ) := by
  by_cases hm0 : m = 0
  · subst hm0
    exact ⟨P₀ + 1, Fin.elim0, Nat.lt_succ_self P₀, fun r => Fin.elim0 r,
      fun r => Fin.elim0 r, fun r => Fin.elim0 r, fun r => Fin.elim0 r⟩
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  let r₀ : Fin m := ⟨0, hm_pos⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin M, u r₀ i ≠ 0 := by simpa [funext_iff] using hu_ne r₀
  obtain ⟨U, _, hU⟩ := exists_shifted_primeBlocks_log_approx m M P₀ (fun _ => 0) (fun _ => le_rfl)
  have hseq (n : ℕ) := hU (max U (n : ℝ)) (le_max_left _ _)
  choose Nseq ιseq hι_inj hι_props using hseq
  have hι_row_inj (n : ℕ) (r : Fin m) : Function.Injective (ιseq n r) :=
    fun i j hij => Prod.mk.inj_iff.mp (hι_inj n (p₁ := (r, i)) (p₂ := (r, j)) hij) |>.2
  let aseq (n : ℕ) (r : Fin m) : Fin (Nseq n) → ℤ := Function.extend (ιseq n r) (u r) 0
  have hzero : Tendsto (fun n : ℕ => (6 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hexp_bound (n : ℕ) (hn1 : 1 ≤ n) :
      2 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ)) ≤ (6 : ℝ) / (n : ℝ) := by
    have hlin : (1 / 3 : ℝ) * (n : ℝ) ≤ Real.exp ((1 / 3 : ℝ) * (n : ℝ)) := by
      linarith [Real.add_one_le_exp ((1 / 3 : ℝ) * (n : ℝ))]
    rw [neg_mul, Real.exp_neg]
    have hinv := inv_anti₀ (by positivity : 0 < (1 / 3 : ℝ) * (n : ℝ)) hlin
    rw [show ((1 / 3 : ℝ) * (n : ℝ))⁻¹ = (3 : ℝ) / (n : ℝ) by field_simp] at hinv
    calc 2 * (Real.exp ((1 / 3 : ℝ) * (n : ℝ)))⁻¹ ≤ 2 * ((3 : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 6 / (n : ℝ) := by ring
  have hconv_entry (r s : Fin m) (i j : Fin M) :
      Tendsto (fun n : ℕ => (atomGram (Nseq n) (ιseq n r i) (ιseq n s j)).re)
        atTop (𝓝 (atomGram M i j).re) := by
    rw [atomGram_eq_splineSeries M i j]
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt U
    have harg : Tendsto
        (fun n : ℕ =>
          Real.log (((ιseq n r i).val : ℝ) + 1) - Real.log (((ιseq n s j).val : ℝ) + 1))
        atTop (𝓝 (Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (by simpa only [sub_zero] using tendsto_const_nhds.sub hzero)
        (by simpa only [add_zero] using tendsto_const_nhds.add hzero) ?_ ?_
      · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
        have hmax : max U (n : ℝ) = (n : ℝ) :=
          max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
        have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
        have hi := (hι_props n r i).2.2
        have hj := (hι_props n s j).2.2
        rw [hmax, add_zero] at hi hj
        linarith only [hi.2, hj.1, hb]
      · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
        have hmax : max U (n : ℝ) = (n : ℝ) :=
          max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
        have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
        have hi := (hι_props n r i).2.2
        have hj := (hι_props n s j).2.2
        rw [hmax, add_zero] at hi hj
        linarith only [hi.1, hj.2, hb]
    refine ((Complex.continuous_re.comp continuous_splineSeries).tendsto _).comp harg |>
      fun h => h.congr fun n => ?_
    dsimp only [Function.comp_apply]
    rw [atomGram_eq_splineSeries]
  have hconv_pair (r s : Fin m) :
      Tendsto (fun n : ℕ => probePairing (Nseq n) (aseq n r) (aseq n s))
        atTop (𝓝 (probePairing M (u r) (u s))) := by
    unfold probePairing
    refine (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ =>
        ((hconv_entry r s i j).mul_const (u r i : ℝ)).mul_const (u s j : ℝ)).congr fun n => ?_
    exact (extend_probePairing_eq (hι_row_inj n r) (hι_row_inj n s) (u r) (u s)).symm
  have hev_all : ∀ᶠ n : ℕ in atTop,
      ∀ r s : Fin m, |probePairing (Nseq n) (aseq n r) (aseq n s) - probePairing M (u r) (u s)| < δ := by
    rw [eventually_all]; intro r; rw [eventually_all]; intro s
    exact (Metric.tendsto_nhds.mp (hconv_pair r s) δ hδ).mono fun n hn => by
      rwa [Real.dist_eq] at hn
  obtain ⟨n, hn⟩ := hev_all.exists
  have hN_gt : P₀ < Nseq n := by
    have h1 := (hι_props n r₀ i₀).2.1
    have h2 := (ιseq n r₀ i₀).isLt
    omega
  refine ⟨Nseq n, aseq n, hN_gt,
    fun r => (isSignedPrimeSupported_extend (hι_row_inj n r)
      (fun i => ⟨(hι_props n r i).1, (hι_props n r i).2.1⟩) (hu_ne r) (hu_sum r)).1,
    fun r => (isSignedPrimeSupported_extend (hι_row_inj n r)
      (fun i => ⟨(hι_props n r i).1, (hι_props n r i).2.1⟩) (hu_ne r) (hu_sum r)).2,
    ?_, hn⟩
  intro r s hrs
  rw [disjoint_activeConductors_iff]
  intro ℓ
  by_contra! hboth
  have hex_r : ∃ i : Fin M, ιseq n r i = ℓ := by
    by_contra hno; exact hboth.1 (Function.extend_apply' _ _ _ hno)
  have hex_s : ∃ j : Fin M, ιseq n s j = ℓ := by
    by_contra hno; exact hboth.2 (Function.extend_apply' _ _ _ hno)
  obtain ⟨i, rfl⟩ := hex_r
  obtain ⟨j, hj⟩ := hex_s
  exact hrs (Prod.mk.inj_iff.mp (hι_inj n (p₁ := (r, i)) (p₂ := (s, j)) hj.symm)).1

/-- The zero-sum two-atom cubic-spline difference `B(u) - B(u - log 2)`. -/
def twoAtomDiffTest : ℝ → ℝ :=
  cubicSpline - scaleShift (Real.log 2) cubicSpline

theorem twoAtomDiffTest_mem_realTests : twoAtomDiffTest ∈ realTests :=
  Submodule.sub_mem _ cubicSpline_mem_realTests (scaleShift_mem (Real.log 2) cubicSpline_mem_realTests)

/-- `twoAtomDiffTest` sees every right zero of every zero configuration `Z`: at `Re ρ > 1/2`,
`|2^{ρ - 1/2}| = 2^{Re ρ - 1/2} > 1` and `|2^{1/2 - conj ρ}| = 2^{-(Re ρ - 1/2)} < 1`, so neither
factor `1 - 2^{±(ρ - 1/2)}` vanishes. -/
theorem seenRightZeros_twoAtomDiffTest (Z : ZeroConfig) :
    seenRightZeros Z twoAtomDiffTest = rightZeros Z := by
  ext ρ
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hft (z : ℂ) : paperFT (cx twoAtomDiffTest) z =
      (1 - cexp ((Real.log 2 : ℂ) * (I * z))) * paperFT (cx cubicSpline) z := by
    have hsh := scaleShift_mem (Real.log 2) cubicSpline_mem_realTests
    have hcx : cx twoAtomDiffTest = cx cubicSpline + (-1 : ℂ) • cx (scaleShift (Real.log 2) cubicSpline) := by
      funext u; simp [twoAtomDiffTest, cx, sub_eq_add_neg]
    rw [hcx, paperFT_add (cx_contDiff contDiff_cubicSpline).continuous
      (cx_hasCompactSupport hasCompactSupport_cubicSpline)
      ((cx_contDiff hsh.1).continuous.const_smul _) ((cx_hasCompactSupport hsh.2).smul_left),
      paperFT_smul, paperFT_cx_scaleShift_apply]
    ring
  simp only [seenRightZeros, rightZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hB : ρ ∈ seenRightZeros Z cubicSpline := by
      rw [seenRightZeros_cubicSpline]; exact ⟨h1, h2⟩
    obtain ⟨-, -, hB1, hB2⟩ := hB
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [hft]
      refine mul_ne_zero (sub_ne_zero.mpr fun heq => ?_) hB1
      have hI : I * gammaOf ρ = ρ - 1 / 2 := by
        rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]
      have hn := congrArg norm heq.symm
      rw [norm_one, hI, Complex.norm_exp, Complex.re_ofReal_mul, Complex.sub_re] at hn
      have hgt : 1 < Real.exp (Real.log 2 * (ρ.re - 1 / 2)) :=
        Real.one_lt_exp_iff.mpr (mul_pos hlog2 (by linarith))
      linarith
    · rw [hft]
      refine mul_ne_zero (sub_ne_zero.mpr fun heq => ?_) hB2
      have hI : I * conj (gammaOf ρ) = 1 / 2 - conj ρ := by
        rw [← gammaOf_reflect, gammaOf, mul_div_cancel₀ _ I_ne_zero, reflect]
      have hn := congrArg norm heq.symm
      rw [norm_one, hI, Complex.norm_exp, Complex.re_ofReal_mul, Complex.sub_re,
        Complex.conj_re] at hn
      have hlt : Real.exp (Real.log 2 * ((1 / 2 : ℝ) - ρ.re)) < 1 :=
        Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hlog2 (by linarith))
      linarith

/-- Standard zero-sum two-atom integer basis vector `e_k - e_{2k+1}` on `Fin (2 * K)`. -/
def dyadicDiffAtom (K : ℕ) (k : Fin K) : Fin (2 * K) → ℤ :=
  Pi.single ⟨k.val, by omega⟩ 1 - Pi.single ⟨2 * k.val + 1, by omega⟩ 1

theorem sum_dyadicDiffAtom (K : ℕ) (k : Fin K) :
    (∑ ℓ : Fin (2 * K), dyadicDiffAtom K k ℓ) = 0 := by
  unfold dyadicDiffAtom
  simp [Finset.sum_sub_distrib]

/-- The orbit-kernel Gram matrix of `twoAtomDiffTest` on `intWindow K` equals the `K × K` probe
Gram matrix of `dyadicDiffAtom K`. -/
theorem gram_twoAtomDiffTest_eq_probeGramMatrix (K : ℕ) :
    gram (orbitKernel zetaZeroConfig twoAtomDiffTest) (intWindow K) =
      probeGramMatrix (2 * K) (dyadicDiffAtom K) := by
  ext k k'
  let i₁ : Fin K → Fin (2 * K) := fun r => ⟨r.val, by omega⟩
  let i₂ : Fin K → Fin (2 * K) := fun r => ⟨2 * r.val + 1, by omega⟩
  have hlog₁ (r : Fin K) : Real.log (((i₁ r : ℕ) : ℝ) + 1) = Real.log ((r : ℝ) + 1) := rfl
  have hlog₂ (r : Fin K) :
      Real.log (((i₂ r : ℕ) : ℝ) + 1) = Real.log ((r : ℝ) + 1) + Real.log 2 := by
    have hval : (((i₂ r : ℕ) : ℝ) + 1) = 2 * (((r : ℕ) : ℝ) + 1) := by
      dsimp [i₂]; push_cast; ring
    rw [hval, Real.log_mul two_ne_zero (by positivity), add_comm]
  have hsh_eq (r : Fin K) :
      ArithmeticCastelnuovoSeveri.translate (scale heckeLogScale (intWindow K r))
        (cx twoAtomDiffTest) =
      ArithmeticCastelnuovoSeveri.translate (Real.log (((i₁ r : ℕ) : ℝ) + 1)) (cx cubicSpline) +
        (-1 : ℂ) • ArithmeticCastelnuovoSeveri.translate (Real.log (((i₂ r : ℕ) : ℝ) + 1))
          (cx cubicSpline) := by
    rw [scale_intWindow, hlog₁, hlog₂]
    funext u
    simp only [ArithmeticCastelnuovoSeveri.translate, twoAtomDiffTest, scaleShift, cx,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub]
    rw [sub_sub]
    ring
  have hcB (t : ℝ) : ContDiff ℝ 2 (ArithmeticCastelnuovoSeveri.translate t (cx cubicSpline)) :=
    translate_contDiff (cx_contDiff contDiff_cubicSpline) t
  have hsB (t : ℝ) : HasCompactSupport (ArithmeticCastelnuovoSeveri.translate t (cx cubicSpline)) :=
    translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) t
  have hW_atom (a b : Fin (2 * K)) :
      zetaZeroConfig.W
        (ArithmeticCastelnuovoSeveri.translate (Real.log (((a : ℕ) : ℝ) + 1)) (cx cubicSpline))
        (ArithmeticCastelnuovoSeveri.translate (Real.log (((b : ℕ) : ℝ) + 1)) (cx cubicSpline)) =
      atomGram (2 * K) a b := by
    have hw := weilGram_eq_zeroGram (f := fun c : Fin (2 * K) =>
      ArithmeticCastelnuovoSeveri.translate (Real.log (((c : ℕ) : ℝ) + 1)) (cx cubicSpline))
      (fun c => hcB _) (fun c => hsB _)
    exact (congr_fun (congr_fun hw a) b).symm
  rw [gram_orbitKernel]
  change zetaZeroConfig.W _ _ = _
  rw [hsh_eq k, hsh_eq k',
    W_add_left zetaZeroConfig temperedConfig_zetaZeroConfig (hcB _) (hsB _)
      ((hcB _).const_smul _) ((hsB _).smul_left)
      ((hcB _).add ((hcB _).const_smul _)) ((hsB _).add ((hsB _).smul_left)),
    W_add_right zetaZeroConfig temperedConfig_zetaZeroConfig (hcB _) (hsB _)
      (hcB _) (hsB _) ((hcB _).const_smul _) ((hsB _).smul_left),
    W_add_right zetaZeroConfig temperedConfig_zetaZeroConfig
      ((hcB _).const_smul _) ((hsB _).smul_left)
      (hcB _) (hsB _) ((hcB _).const_smul _) ((hsB _).smul_left),
    W_smul_left, W_smul_left, W_smul_right, W_smul_right,
    hW_atom, hW_atom, hW_atom, hW_atom]
  have hreal (a b : Fin (2 * K)) : atomGram (2 * K) a b = ((atomGram (2 * K) a b).re : ℂ) :=
    Complex.ext rfl (by simpa using atomGram_im (2 * K) a b)
  rw [hreal, hreal, hreal, hreal]
  simp only [probeGramMatrix, Matrix.of_apply, probePairing, dyadicDiffAtom, Pi.sub_apply,
    Pi.single_apply, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, map_neg, map_one]
  push_cast
  ring

/-- Spectral diagonalization over `ℝ` + rational approximation + denominator clearing: if a real
symmetric `K × K` matrix `A` has `m ≤ hermNegIndex (A.map Complex.ofReal)`, then for every
`η > 0` there exist `m` integer vectors `z : Fin m → (Fin K → ℤ)` whose induced Gram entries
satisfy `B(z r, z r) < 0` and `|B(z r, z s)| / √(B(z r, z r) B(z s, z s)) < η` for `r ≠ s`. -/
private theorem exists_intVectors_near_orthogonal_neg {m K : ℕ}
    (A : Matrix (Fin K) (Fin K) ℝ) (hAsym : ∀ i j, A i j = A j i)
    (hm : m ≤ hermNegIndex (Matrix.of fun i j => (A i j : ℂ)))
    {η : ℝ} (hη : 0 < η) :
    ∃ z : Fin m → (Fin K → ℤ),
      let B := fun x y : Fin K → ℝ => ∑ i : Fin K, ∑ j : Fin K, A i j * x i * y j
      (∀ r : Fin m, B (fun i => (z r i : ℝ)) (fun i => (z r i : ℝ)) < 0) ∧
      (∀ r s : Fin m, r ≠ s →
        |B (fun i => (z r i : ℝ)) (fun i => (z s i : ℝ))| /
          Real.sqrt (B (fun i => (z r i : ℝ)) (fun i => (z r i : ℝ)) *
            B (fun i => (z s i : ℝ)) (fun i => (z s i : ℝ))) < η) := by
  classical
  intro B
  have hAH : A.IsHermitian := by ext i j; simp [hAsym j i]
  set V : Matrix (Fin K) (Fin K) ℝ := (hAH.eigenvectorUnitary : Matrix (Fin K) (Fin K) ℝ)
  have hdiag_real : Vᵀ * A * V = diagonal hAH.eigenvalues := by
    have h := Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary hAH
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hVV1 : V * Vᵀ = 1 := by
    have h := Unitary.coe_mul_star_self hAH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hVT1 : Vᵀ * V = 1 := by
    have h := Unitary.coe_star_mul_self hAH.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set VC : Matrix (Fin K) (Fin K) ℂ := A.of fun i j => (V i j : ℂ) with hVC_def
  let VC' : Matrix (Fin K) (Fin K) ℂ := Matrix.of fun i j => (V i j : ℂ)
  have hVC_unit : IsUnit VC' := by
    refine ⟨⟨VC', VC'ᴴ, ?_, ?_⟩, rfl⟩
    · ext i j
      have hij := congr_fun (congr_fun hVV1 i) j
      simp only [VC', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Complex.star_def, Complex.conj_ofReal, Matrix.one_apply] at hij ⊢
      rw [← Complex.ofReal_Inj.eq_iff] at *
      exact_mod_cast hij
    · ext i j
      have hij := congr_fun (congr_fun hVT1 i) j
      simp only [VC', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
        Complex.star_def, Complex.conj_ofReal, Matrix.one_apply] at hij ⊢
      exact_mod_cast hij
  have hdiag_cx :
      VC'ᴴ * (Matrix.of fun i j => (A i j : ℂ)) * VC' =
        diagonal (fun i => (hAH.eigenvalues i : ℂ)) := by
    ext i j
    have hij := congr_fun (congr_fun hdiag_real i) j
    simp only [VC', Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Complex.star_def, Complex.conj_ofReal, Matrix.diagonal_apply] at hij ⊢
    simp_rw [Finset.sum_mul] at hij ⊢
    exact_mod_cast hij
  have hcard_eq : hermNegIndex (Matrix.of fun i j => (A i j : ℂ)) =
      ({i : Fin K | hAH.eigenvalues i < 0} : Finset (Fin K)).card := by
    rw [← negIndex_conjugate _ hVC_unit, hdiag_cx, negIndex_diagonal]
  rw [hcard_eq] at hm
  obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hm
  let emb : Fin m ↪ Fin K :=
    (S.equivFin.symm.toEmbedding).trans ⟨Subtype.val, Subtype.val_injective⟩
  have hemb_neg (r : Fin m) : hAH.eigenvalues (emb r) < 0 := by
    have hmem : emb r ∈ S := (S.equivFin.symm r).2
    exact (Finset.mem_filter.mp (hS_sub hmem)).2
  let v : Fin m → (Fin K → ℝ) := fun r i => V i (emb r)
  have hBv (r s : Fin m) :
      B (v r) (v s) = if r = s then hAH.eigenvalues (emb r) else 0 := by
    have hij := congr_fun (congr_fun hdiag_real (emb r)) (emb s)
    have hsum : (Vᵀ * A * V) (emb r) (emb s) = B (v r) (v s) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, B, v]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [← hsum, hij, Matrix.diagonal_apply]
    by_cases hrs : r = s
    · subst hrs; simp
    · rw [if_neg (emb.injective.ne hrs), if_neg hrs]
  have hdense : DenseRange (fun q : Fin m → (Fin K → ℚ) => fun r i => ((q r i : ℚ) : ℝ)) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => Rat.denseRange_cast
  have hB_cont (r s : Fin m) : Continuous (fun w : Fin m → (Fin K → ℝ) => B (w r) (w s)) := by
    dsimp [B]; fun_prop
  let Uset : Set (Fin m → (Fin K → ℝ)) :=
    {w | (∀ r : Fin m, B (w r) (w r) < 0) ∧
      (∀ r s : Fin m, r ≠ s → |B (w r) (w s)| < η * Real.sqrt (B (w r) (w r) * B (w s) (w s)))}
  have hU_open : IsOpen Uset := by
    refine (isOpen_iInter_of_finite fun r => isOpen_lt (hB_cont r r) continuous_const).inter ?_
    refine isOpen_iInter_of_finite fun r => isOpen_iInter_of_finite fun s => ?_
    by_cases hrs : r = s
    · subst hrs; simp
    · simp only [hrs, not_false_eq_true, Set.setOf_true, true_implies]
      exact isOpen_lt (continuous_abs.comp (hB_cont r s))
        (continuous_const.mul (Real.continuous_sqrt.comp ((hB_cont r r).mul (hB_cont s s))))
  have hv_mem : v ∈ Uset := by
    refine ⟨fun r => by rw [hBv r r, if_pos rfl]; exact hemb_neg r, fun r s hrs => ?_⟩
    rw [hBv r s, if_neg hrs, abs_zero, hBv r r, if_pos rfl, hBv s s, if_pos rfl]
    exact mul_pos hη (Real.sqrt_pos.mpr (mul_pos_of_neg_of_neg (hemb_neg r) (hemb_neg s)))
  obtain ⟨q, hq_mem⟩ := hdense.exists_mem_open hU_open ⟨v, hv_mem⟩
  choose D z hD_pos hz_eq using fun r => exists_common_denominator (q r)
  have hBz (r s : Fin m) :
      B (fun i => (z r i : ℝ)) (fun i => (z s i : ℝ)) =
        (D r : ℝ) * (D s : ℝ) * B (fun i => ((q r i : ℚ) : ℝ)) (fun i => ((q s i : ℚ) : ℝ)) := by
    dsimp [B]
    simp only [← hz_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨z, fun r => ?_, fun r s hrs => ?_⟩
  · rw [hBz r r]
    have hDr : (0 : ℝ) < D r := Nat.cast_pos.mpr (hD_pos r)
    exact mul_neg_of_pos_of_neg (mul_pos hDr hDr) (hq_mem.1 r)
  · have hDr : (0 : ℝ) < D r := Nat.cast_pos.mpr (hD_pos r)
    have hDs : (0 : ℝ) < D s := Nat.cast_pos.mpr (hD_pos s)
    have hBrr_neg := hq_mem.1 r
    have hBss_neg := hq_mem.1 s
    have hsqrt_pos :
        0 < Real.sqrt (B (fun i => ((q r i : ℚ) : ℝ)) (fun i => ((q r i : ℚ) : ℝ)) *
          B (fun i => ((q s i : ℚ) : ℝ)) (fun i => ((q s i : ℚ) : ℝ))) :=
      Real.sqrt_pos.mpr (mul_pos_of_neg_of_neg hBrr_neg hBss_neg)
    rw [hBz r s, hBz r r, hBz s s,
      abs_mul, abs_of_pos (mul_pos hDr hDs),
      show (D r : ℝ) * (D r : ℝ) * B (fun i => ((q r i : ℚ) : ℝ)) (fun i => ((q r i : ℚ) : ℝ)) *
          ((D s : ℝ) * (D s : ℝ) * B (fun i => ((q s i : ℚ) : ℝ)) (fun i => ((q s i : ℚ) : ℝ))) =
        ((D r : ℝ) * (D s : ℝ)) ^ 2 *
          (B (fun i => ((q r i : ℚ) : ℝ)) (fun i => ((q r i : ℚ) : ℝ)) *
            B (fun i => ((q s i : ℚ) : ℝ)) (fun i => ((q s i : ℚ) : ℝ))) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_pos hDr hDs).le,
      mul_div_mul_left _ _ (mul_pos hDr hDs).ne', div_lt_iff₀ hsqrt_pos]
    exact hq_mem.2 r s hrs

/-- **Exact `m`-probe Gershgorin and negative-index law on disjoint signed prime probes.**
For every `m : ℕ`, prime cutoff `P₀ : ℕ`, and `ε ∈ (0, 1]`, the following are equivalent:
1. `(m : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard`;
2. Above `P₀` there exist `m` pairwise-disjoint signed prime-supported probes `a r : Fin N → ℤ`
   with `G_{rr} < 0` and normalized off-diagonal row sums `< ε`;
3. Above `P₀` there exist `m` pairwise-disjoint signed prime-supported probes `a r : Fin N → ℤ`
   with `hermNegIndex (probeGramMatrix N a) = m`. -/
theorem disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge (m P₀ : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((m : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard ↔
      ∃ (N : ℕ) (a : Fin m → (Fin N → ℤ)),
        P₀ < N ∧
        (∀ r : Fin m, isSignedPrimeSupported (a r)) ∧
        (∀ (r : Fin m) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
        (∀ r s : Fin m, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
        (∀ r : Fin m, probePairing N (a r) (a r) < 0) ∧
        (∀ r : Fin m,
          ∑ s ∈ Finset.univ.erase r,
            |probePairing N (a r) (a s)| /
              Real.sqrt (probePairing N (a r) (a r) * probePairing N (a s) (a s)) < ε)) ∧
    ((m : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard ↔
      ∃ (N : ℕ) (a : Fin m → (Fin N → ℤ)),
        P₀ < N ∧
        (∀ r : Fin m, isSignedPrimeSupported (a r)) ∧
        (∀ (r : Fin m) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
        (∀ r s : Fin m, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
        hermNegIndex (probeGramMatrix N a) = m) := by
  have forward (hm_ge : (m : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard) :
      ∃ (N : ℕ) (a : Fin m → (Fin N → ℤ)),
        P₀ < N ∧
        (∀ r : Fin m, isSignedPrimeSupported (a r)) ∧
        (∀ (r : Fin m) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
        (∀ r s : Fin m, r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
        (∀ r : Fin m, probePairing N (a r) (a r) < 0) ∧
        (∀ r : Fin m,
          ∑ s ∈ Finset.univ.erase r,
            |probePairing N (a r) (a s)| /
              Real.sqrt (probePairing N (a r) (a r) * probePairing N (a s) (a s)) < ε) := by
    by_cases hm0 : m = 0
    · subst hm0
      exact ⟨P₀ + 1, Fin.elim0, Nat.lt_succ_self P₀, fun r => Fin.elim0 r,
        fun r => Fin.elim0 r, fun r => Fin.elim0 r, fun r => Fin.elim0 r, fun r => Fin.elim0 r⟩
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hidx : (rightZeros zetaZeroConfig).encard =
        ⨆ K : ℕ, (hermNegIndex (probeGramMatrix (2 * K) (dyadicDiffAtom K)) : ℕ∞) := by
      rw [← seenRightZeros_twoAtomDiffTest zetaZeroConfig,
        ← negIndex_orbitKernel zetaZeroConfig temperedConfig_zetaZeroConfig twoAtomDiffTest_mem_realTests,
        negIndex_eq_iSup_intWindow]
      exact iSup_congr fun K => by rw [gram_twoAtomDiffTest_eq_probeGramMatrix]
    rw [hidx] at hm_ge
    obtain ⟨K, hK⟩ : ∃ K : ℕ, m ≤ hermNegIndex (probeGramMatrix (2 * K) (dyadicDiffAtom K)) := by
      by_contra! hlt
      have hsup : (⨆ K : ℕ, (hermNegIndex (probeGramMatrix (2 * K) (dyadicDiffAtom K)) : ℕ∞)) ≤
          ((m - 1 : ℕ) : ℕ∞) := by
        refine iSup_le fun K => ?_
        exact_mod_cast Nat.le_sub_one_of_lt (hlt K)
      have hle : (m : ℕ∞) ≤ ((m - 1 : ℕ) : ℕ∞) := hm_ge.trans hsup
      have hnat : m ≤ m - 1 := by exact_mod_cast hle
      omega
    let A : Matrix (Fin K) (Fin K) ℝ :=
      Matrix.of fun i j => probePairing (2 * K) (dyadicDiffAtom K i) (dyadicDiffAtom K j)
    have hAsym (i j : Fin K) : A i j = A j i :=
      probePairing_symm (2 * K) (dyadicDiffAtom K i) (dyadicDiffAtom K j)
    let η := ε / (2 * ((m : ℝ) + 1))
    have hη : 0 < η := by positivity
    obtain ⟨z, hz_diag, hz_off⟩ := exists_intVectors_near_orthogonal_neg A hAsym hK hη
    let u : Fin m → (Fin (2 * K) → ℤ) := fun r => ∑ k : Fin K, z r k • dyadicDiffAtom K k
    have hu_pair (r s : Fin m) :
        probePairing (2 * K) (u r) (u s) =
          ∑ k : Fin K, ∑ k' : Fin K, A k k' * (z r k : ℝ) * (z s k' : ℝ) := by
      unfold probePairing u A
      simp only [Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, Int.cast_id,
        Int.cast_sum, Int.cast_mul]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k' _ => by ring
    have hu_neg (r : Fin m) : probePairing (2 * K) (u r) (u r) < 0 := by
      rw [hu_pair]; exact hz_diag r
    have hu_ne (r : Fin m) : u r ≠ 0 := by
      intro h0
      have := hu_neg r
      rw [h0] at this
      unfold probePairing at this
      simp at this
    have hu_sum (r : Fin m) : (∑ ℓ : Fin (2 * K), u r ℓ) = 0 := by
      dsimp [u]
      simp_rw [Finset.sum_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_id, ← Finset.mul_sum,
        sum_dyadicDiffAtom K k, mul_zero]
    -- Choose uniform entry approximation tolerance from continuity of the Gershgorin ratios at `u`
    let F : (Fin m → Fin m → ℝ) → ℝ := fun G =>
      ∑ r : Fin m, ∑ s ∈ Finset.univ.erase r, |G r s| / Real.sqrt (G r r * G s s)
    let G₀ : Fin m → Fin m → ℝ := fun r s => probePairing (2 * K) (u r) (u s)
    have hG₀_row (r : Fin m) :
        ∑ s ∈ Finset.univ.erase r, |G₀ r s| / Real.sqrt (G₀ r r * G₀ s s) < ε / 2 := by
      by_cases hm_eq1 : m = 1
      · have hempty : Finset.univ.erase r = ∅ := by
          ext s; simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.notMem_empty, iff_false, not_not]
          exact Subsingleton.elim s r
        rw [hempty, Finset.sum_empty]; positivity
      have hcard : (Finset.univ.erase r).card ≤ m :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin m)
      have hle : ∑ s ∈ Finset.univ.erase r, |G₀ r s| / Real.sqrt (G₀ r r * G₀ s s) ≤
          ∑ _s ∈ Finset.univ.erase r, η := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hrs : r ≠ s := (Finset.mem_erase.mp hs).1.symm
        dsimp [G₀]; rw [hu_pair, hu_pair, hu_pair]
        exact (hz_off r s hrs).le
      rw [Finset.sum_const, nsmul_eq_mul] at hle
      have hmul : ((Finset.univ.erase r).card : ℝ) * η < ε / 2 := by
        dsimp [η]
        have hc : ((Finset.univ.erase r).card : ℝ) ≤ m := by exact_mod_cast hcard
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
        nlinarith only [hc, hε]
      exact hle.trans_lt hmul
    have hcontAt (r : Fin m) : ContinuousAt
        (fun G : Fin m → Fin m → ℝ =>
          ∑ s ∈ Finset.univ.erase r, |G r s| / Real.sqrt (G r r * G s s)) G₀ := by
      refine tendsto_finsetSum _ fun s _ => ?_
      have hnum : ContinuousAt (fun G : Fin m → Fin m → ℝ => |G r s|) G₀ :=
        (continuous_abs.comp ((continuous_apply s).comp (continuous_apply r))).continuousAt
      have hden : ContinuousAt (fun G : Fin m → Fin m → ℝ => Real.sqrt (G r r * G s s)) G₀ :=
        (Real.continuous_sqrt.comp (((continuous_apply r).comp (continuous_apply r)).mul
          ((continuous_apply s).comp (continuous_apply s)))).continuousAt
      have hden_ne : Real.sqrt (G₀ r r * G₀ s s) ≠ 0 :=
        (Real.sqrt_pos.mpr (mul_pos_of_neg_of_neg (hu_neg r) (hu_neg s))).ne'
      exact hnum.div hden hden_ne
    have hev_nhds : ∀ᶠ G : Fin m → Fin m → ℝ in 𝓝 G₀,
        (∀ r : Fin m, G r r < 0) ∧
        (∀ r : Fin m, ∑ s ∈ Finset.univ.erase r, |G r s| / Real.sqrt (G r r * G s s) < ε) := by
      refine (eventually_all.mpr fun r =>
        (((continuous_apply r).comp (continuous_apply r)).continuousAt.eventually
          (gt_mem_nhds (hu_neg r)))).and ?_
      exact eventually_all.mpr fun r =>
        (hcontAt r).eventually (gt_mem_nhds ((hG₀_row r).trans (by linarith)))
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.eventually_nhds_iff.mp hev_nhds
    obtain ⟨N, a, hN_gt, ha_sig, ha_gt, ha_disj, ha_near⟩ :=
      exists_coScaled_disjoint_primeProbes_near u hu_ne hu_sum P₀ hδ_pos
    have hdist : dist (fun r s => probePairing N (a r) (a s)) G₀ < δ := by
      rw [dist_pi_lt_iff hδ_pos]; intro r
      rw [dist_pi_lt_iff hδ_pos]; intro s
      rw [Real.dist_eq]
      exact ha_near r s
    obtain ⟨hdiag_a, hrow_a⟩ := hball hdist
    exact ⟨N, a, hN_gt, ha_sig, ha_gt, ha_disj, hdiag_a, hrow_a⟩
  have middle_to_idx {N : ℕ} {a : Fin m → (Fin N → ℤ)}
      (hidx_eq : hermNegIndex (probeGramMatrix N a) = m) :
      (m : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
    rw [rightZeros_encard_eq_sectionIndex]
    simp only [sectionMatrix_eq_atomGram]
    calc (m : ℕ∞) = (hermNegIndex (probeGramMatrix N a) : ℕ∞) := by rw [hidx_eq]
      _ ≤ (hermNegIndex (atomGram N) : ℕ∞) := by
          exact_mod_cast hermNegIndex_probeGramMatrix_le N a
      _ ≤ ⨆ K : ℕ, (hermNegIndex (atomGram K) : ℕ∞) :=
          le_iSup (fun K : ℕ => (hermNegIndex (atomGram K) : ℕ∞)) N
  refine ⟨⟨forward, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨N, a, _, _, _, _, hdiag, hrow⟩
    exact middle_to_idx (hermNegIndex_eq_of_gershgorin_row_lt_one a hdiag fun r =>
      (hrow r).trans_le hε1)
  · intro hm_ge
    obtain ⟨N, a, hN, hsig, hgt, hdisj, hdiag, hrow⟩ := forward hm_ge
    exact ⟨N, a, hN, hsig, hgt, hdisj,
      hermNegIndex_eq_of_gershgorin_row_lt_one a hdiag fun r => (hrow r).trans_le hε1⟩
  · rintro ⟨N, a, _, _, _, _, hidx_eq⟩
    exact middle_to_idx hidx_eq

/-- **Odd-to-even parity jump for `ζ` probe Gram matrices.** Because right zeros of `ζ` come in
nonreal complex-conjugate pairs, any `2k + 1` negative-definite probes unconditionally force
`2k + 2` pairwise-disjoint signed prime-supported probes above every cutoff `P₀` with normalized
off-diagonal row sums `< ε`. -/
theorem odd_probe_rank_forces_even_succ {k N₀ : ℕ} (a₀ : Fin (2 * k + 1) → (Fin N₀ → ℤ))
    (hneg : hermNegIndex (probeGramMatrix N₀ a₀) = 2 * k + 1)
    (P₀ : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (N : ℕ) (a : Fin (2 * k + 2) → (Fin N → ℤ)),
      P₀ < N ∧
      (∀ r : Fin (2 * k + 2), isSignedPrimeSupported (a r)) ∧
      (∀ (r : Fin (2 * k + 2)) (ℓ : Fin N), a r ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
      (∀ r s : Fin (2 * k + 2), r ≠ s → Disjoint (activeConductors (a r)) (activeConductors (a s))) ∧
      (∀ r : Fin (2 * k + 2), probePairing N (a r) (a r) < 0) ∧
      (∀ r : Fin (2 * k + 2),
        ∑ s ∈ Finset.univ.erase r,
          |probePairing N (a r) (a s)| /
            Real.sqrt (probePairing N (a r) (a r) * probePairing N (a s) (a s)) < ε) ∧
      hermNegIndex (probeGramMatrix N a) = 2 * k + 2 := by
  have hodd_le : ((2 * k + 1 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
    rw [rightZeros_encard_eq_sectionIndex]
    simp only [sectionMatrix_eq_atomGram]
    calc ((2 * k + 1 : ℕ) : ℕ∞) = (hermNegIndex (probeGramMatrix N₀ a₀) : ℕ∞) := by rw [hneg]
      _ ≤ (hermNegIndex (atomGram N₀) : ℕ∞) := by
          exact_mod_cast hermNegIndex_probeGramMatrix_le N₀ a₀
      _ ≤ ⨆ K : ℕ, (hermNegIndex (atomGram K) : ℕ∞) :=
          le_iSup (fun K : ℕ => (hermNegIndex (atomGram K) : ℕ∞)) N₀
  have heven_le : ((2 * k + 2 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
    rw [zeta_rightZeros_encard_eq_two_mul_sectorZeros 1] at hodd_le ⊢
    rcases eq_or_ne (sectorZeros zetaZeroConfig 1).encard ⊤ with htop | hfin
    · rw [htop]; simp
    · obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hfin
      rw [← hc] at hodd_le ⊢
      have hnat : 2 * k + 1 ≤ 2 * c := by exact_mod_cast hodd_le
      have hnat2 : 2 * k + 2 ≤ 2 * c := by omega
      exact_mod_cast hnat2
  obtain ⟨N, a, hN, hsig, hgt, hdisj, hdiag, hrow⟩ :=
    (disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge (2 * k + 2) P₀ hε hε1).1.mp heven_le
  exact ⟨N, a, hN, hsig, hgt, hdisj, hdiag, hrow,
    hermNegIndex_eq_of_gershgorin_row_lt_one a hdiag fun r => (hrow r).trans_le hε1⟩

/-! ### 3. Unconditional two-probe separation for `ζ` and single-real-zero calibration -/

/-- **Unconditional solution of the two-probe separation problem for `ζ`.**
Given any single negative integer probe `integerProbe N₀ a₀ < 0`, for every prime cutoff `P₀`
and every `ε ∈ (0, 1]` there exist `N > P₀` and two pairwise-disjoint signed prime-supported
probes `a₁, a₂ : Fin N → ℤ` supported above `P₀` with `G₁₁ < 0`, `G₂₂ < 0`,
`|G₁₂| < ε √(G₁₁ G₂₂)`, `G₁₂² < G₁₁ G₂₂`, and `hermNegIndex (probeGramMatrix N ![a₁, a₂]) = 2`. -/
theorem twoProbe_gershgorin_and_det_of_neg_integerProbe {N₀ : ℕ} {a₀ : Fin N₀ → ℤ}
    (hneg₀ : integerProbe N₀ a₀ < 0) (P₀ : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (N : ℕ) (a₁ a₂ : Fin N → ℤ),
      P₀ < N ∧
      isSignedPrimeSupported a₁ ∧ isSignedPrimeSupported a₂ ∧
      (∀ i : Fin N, a₁ i ≠ 0 → P₀ < i.val + 1) ∧
      (∀ j : Fin N, a₂ j ≠ 0 → P₀ < j.val + 1) ∧
      Disjoint (activeConductors a₁) (activeConductors a₂) ∧
      probePairing N a₁ a₁ < 0 ∧ probePairing N a₂ a₂ < 0 ∧
      |probePairing N a₁ a₂| < ε * Real.sqrt (probePairing N a₁ a₁ * probePairing N a₂ a₂) ∧
      (probePairing N a₁ a₂) ^ 2 < probePairing N a₁ a₁ * probePairing N a₂ a₂ ∧
      hermNegIndex (probeGramMatrix N ![a₁, a₂]) = 2 := by
  have hnRH : ¬ RiemannHypothesis := fun hRH =>
    (not_lt_of_ge (riemannHypothesis_iff_integerProbes.mp hRH N₀ a₀)) hneg₀
  have htwo : ((2 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard :=
    two_le_rightZeros_encard_of_not_RH hnRH
  obtain ⟨N, a, hN, hsig, hgt, hdisj, hdiag, hrow⟩ :=
    (disjoint_signedPrimeProbes_gershgorin_iff_rightZeros_ge 2 P₀ hε hε1).1.mp htwo
  let a₁ := a 0
  let a₂ := a 1
  have herase0 : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  have hrow0 := hrow 0
  rw [herase0, Finset.sum_singleton] at hrow0
  have hsqrt_pos : 0 < Real.sqrt (probePairing N a₁ a₁ * probePairing N a₂ a₂) :=
    Real.sqrt_pos.mpr (mul_pos_of_neg_of_neg (hdiag 0) (hdiag 1))
  have habs_lt : |probePairing N a₁ a₂| <
      ε * Real.sqrt (probePairing N a₁ a₁ * probePairing N a₂ a₂) :=
    (div_lt_iff₀ hsqrt_pos).mp hrow0
  have habs_lt1 : |probePairing N a₁ a₂| <
      Real.sqrt (probePairing N a₁ a₁ * probePairing N a₂ a₂) :=
    habs_lt.trans_le (mul_le_of_le_one_left hsqrt_pos.le hε1)
  have hsq_lt : (probePairing N a₁ a₂) ^ 2 < probePairing N a₁ a₁ * probePairing N a₂ a₂ := by
    have h1 : |probePairing N a₁ a₂| ^ 2 <
        (Real.sqrt (probePairing N a₁ a₁ * probePairing N a₂ a₂)) ^ 2 :=
      pow_lt_pow_left₀ habs_lt1 (abs_nonneg _) two_ne_zero
    rwa [sq_abs, Real.sq_sqrt (mul_pos_of_neg_of_neg (hdiag 0) (hdiag 1)).le] at h1
  have heq_vec : (![a₁, a₂] : Fin 2 → (Fin N → ℤ)) = a := by
    funext r; fin_cases r <;> rfl
  exact ⟨N, a₁, a₂, hN, hsig 0, hsig 1, hgt 0, hgt 1, hdisj 0 1 (by decide),
    hdiag 0, hdiag 1, habs_lt, hsq_lt,
    heq_vec ▸ (twoProbe_negDef_iff_det a₁ a₂).mpr ⟨hdiag 0, hdiag 1, hsq_lt⟩⟩

/-- **Sharp model calibration:** on an abstract functional-equation-symmetric tempered zero
configuration with a single real right zero (`isolatedPairConfig` at `γ₀ = 0`, `L = 10`,
`δ = 1 / 2`), a compactly supported `C²` test has strictly negative Weil square, yet no pair of
compactly supported `C²` tests can achieve `hermNegIndex = 2` (and no pair of real tests can
satisfy `G₁₁ < 0`, `G₂₂ < 0`, and `G₁₂² < G₁₁ G₂₂`). -/
theorem singleRealRightZero_no_twoProbe_det :
    ∃ (Z : ZeroConfig),
      TemperedConfig Z ∧ FESymmetric Z ∧
      (rightZeros Z).encard = 1 ∧
      (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ (Z.W f f).re < 0) ∧
      (∀ g₁ g₂ : ℝ → ℝ, g₁ ∈ realTests → g₂ ∈ realTests →
        ¬ ((Z.W (cx g₁) (cx g₁)).re < 0 ∧ (Z.W (cx g₂) (cx g₂)).re < 0 ∧
            ((Z.W (cx g₁) (cx g₂)).re) ^ 2 <
              (Z.W (cx g₁) (cx g₁)).re * (Z.W (cx g₂) (cx g₂)).re)) := by
  have hL : (0 : ℝ) < 10 := by norm_num
  have hδ : (0 : ℝ) < 1 / 2 := by norm_num
  have hδ' : (1 / 2 : ℝ) ≤ 1 / 2 := le_rfl
  let Z := isolatedPairConfig hL hδ hδ' 0
  have hZ_temp : TemperedConfig Z := temperedConfig_isolatedPairConfig hL hδ hδ' 0
  have hZ_fe : FESymmetric Z := by
    intro ρ hρ
    have href : 1 - ρ = conj (reflect ρ) := by
      apply Complex.ext <;> simp [reflect]
    have hself (z : ℂ) (hz : z ∈ Z.carrier) : conj z ∈ Z.carrier ∧ Z.mult (conj z) = Z.mult z := by
      rcases hz with ((⟨k, rfl⟩ | h) | h)
      · refine ⟨Or.inl (Or.inl ⟨-k, ?_⟩), ?_⟩
        · apply Complex.ext <;> simp [ _root_.RHTower.verticalLatticePoint]
        · change (if (conj (_root_.RHTower.verticalLatticePoint 10 0 k)).re = 1 / 2 then 2 else 1) =
            (if (_root_.RHTower.verticalLatticePoint 10 0 k).re = 1 / 2 then 2 else 1)
          simp [_root_.RHTower.verticalLatticePoint]
      · rw [Set.mem_singleton_iff] at h; subst h
        have hc : conj (offLinePoint (1 / 2) 0) = offLinePoint (1 / 2) 0 := by
          apply Complex.ext <;> simp [offLinePoint]
        rw [hc]; exact ⟨Or.inl (Or.inr rfl), rfl⟩
      · rw [Set.mem_singleton_iff] at h; subst h
        have hc : conj (offLinePoint (-(1 / 2)) 0) = offLinePoint (-(1 / 2)) 0 := by
          apply Complex.ext <;> simp [offLinePoint]
        rw [hc]; exact ⟨Or.inr rfl, rfl⟩
    rw [href]
    obtain ⟨hmem, hmul⟩ := hself (reflect ρ) (Z.reflect_mem ρ hρ)
    exact ⟨hmem, hmul.trans (Z.mult_reflect ρ hρ)⟩
  have hright : rightZeros Z = {offLinePoint (1 / 2) 0} := by
    ext ρ
    simp only [rightZeros, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨((⟨k, rfl⟩ | h) | h), hgt⟩
      · simp [_root_.RHTower.verticalLatticePoint] at hgt
      · exact h
      · rw [Set.mem_singleton_iff] at h; subst h
        simp [offLinePoint] at hgt; linarith
    · rintro rfl
      refine ⟨Or.inl (Or.inr rfl), ?_⟩
      simp [offLinePoint]
  have henc : (rightZeros Z).encard = 1 := by rw [hright, Set.encard_singleton]
  have hsinh_gt : 3 * (1 / 2 : ℝ) * 10 < Real.sinh ((1 / 2 : ℝ) * 10) := by
    have he25 : (6 : ℝ) ≤ Real.exp (5 / 2) := by
      have hsum := Real.sum_le_exp_of_nonneg (x := (5 / 2 : ℝ)) (by norm_num) 3
      simp [Finset.sum_range_succ, Nat.factorial] at hsum
      linarith
    have he5 : (36 : ℝ) ≤ Real.exp 5 := by
      rw [show (5 : ℝ) = 5 / 2 + 5 / 2 by norm_num, Real.exp_add]
      nlinarith
    have hem5 : Real.exp (-5 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    rw [show (1 / 2 : ℝ) * 10 = 5 by norm_num, Real.sinh_eq]
    linarith
  have hnot_nn : ¬ (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Set.Icc (-(10 / 2)) (10 / 2) →
      0 ≤ (Z.W f f).re) := by
    rw [isolatedPairConfig_weil_nonneg_nyquist_iff hL hδ hδ' 0]
    linarith
  push Not at hnot_nn
  obtain ⟨f₀, hf₀_cd, hf₀_supp, hf₀_neg⟩ := hnot_nn
  have hf₀_cs : HasCompactSupport f₀ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport f₀).trans hf₀_supp)
  refine ⟨Z, hZ_temp, hZ_fe, henc, ⟨f₀, hf₀_cd, hf₀_cs, hf₀_neg⟩, ?_⟩
  intro g₁ g₂ hg₁ hg₂ ⟨h11, h22, hdet⟩
  let g : Fin 2 → ℝ → ℂ := ![cx g₁, cx g₂]
  have hg_cd : ∀ i, ContDiff ℝ 2 (g i) := fun i => by
    fin_cases i <;> exacts [cx_contDiff hg₁.1, cx_contDiff hg₂.1]
  have hg_cs : ∀ i, HasCompactSupport (g i) := fun i => by
    fin_cases i <;> exacts [cx_hasCompactSupport hg₁.2, cx_hasCompactSupport hg₂.2]
  have hle_enc : (hermNegIndex (zeroGram Z g) : ℕ∞) ≤ (rightZeros Z).encard :=
    negIndex_zeroGram_le_of_tempered Z hZ_temp g hg_cd hg_cs
  rw [henc] at hle_enc
  have hle1 : hermNegIndex (zeroGram Z g) ≤ 1 := by exact_mod_cast hle_enc
  have hreal_W (f₁ f₂ : ℝ → ℝ) : Z.W (cx f₁) (cx f₂) = ((Z.W (cx f₁) (cx f₂)).re : ℂ) := by
    have hc := W_real_of_fes Z hZ_fe f₁ f₂
    apply Complex.ext
    · rfl
    · have him := congrArg Complex.im hc
      rw [Complex.conj_im] at him
      simp; linarith
  have hsym_W : (Z.W (cx g₂) (cx g₁)).re = (Z.W (cx g₁) (cx g₂)).re := by
    have hc := W_conj_symm Z (cx g₁) (cx g₂)
    have him := congrArg Complex.re hc
    simpa using him.symm
  have hmat : zeroGram Z g =
      Matrix.of ![![(((Z.W (cx g₁) (cx g₁)).re : ℝ) : ℂ), (((Z.W (cx g₁) (cx g₂)).re : ℝ) : ℂ)],
        ![(((Z.W (cx g₁) (cx g₂)).re : ℝ) : ℂ), (((Z.W (cx g₂) (cx g₂)).re : ℝ) : ℂ)]] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [zeroGram, g, ← hreal_W, hsym_W]
  have heq2 : hermNegIndex (zeroGram Z g) = 2 := by
    rw [hmat]
    exact (hermNegIndex_two_ofReal_iff _ _ _).mpr ⟨h11, h22, hdet⟩
  omega

/-! ### 4. Exponential off-diagonal blowup under asymptotic prime-scale separation -/

/-- Real packet `f_u(t) = ∑_i u_i B(t - log(i + 1))` of an integer probe `u : Fin M → ℤ`. -/
def probePacket {M : ℕ} (u : Fin M → ℤ) : ℝ → ℝ :=
  ∑ i : Fin M, (u i : ℝ) • scaleShift (Real.log ((i : ℝ) + 1)) cubicSpline

theorem probePacket_mem_realTests {M : ℕ} (u : Fin M → ℤ) : probePacket u ∈ realTests :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (u i : ℝ) (scaleShift_mem _ cubicSpline_mem_realTests)

/-- Cross-scale autocorrelation `Φ_u(Δ) = Re W(f_u(· - Δ), f_u)` of an integer probe `u`. -/
def probeAutocorr {M : ℕ} (u : Fin M → ℤ) (Δ : ℝ) : ℝ :=
  ∑ i : Fin M, ∑ j : Fin M,
    (splineSeries (Δ + Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))).re *
      (u i : ℝ) * (u j : ℝ)

theorem probeAutocorr_zero {M : ℕ} (u : Fin M → ℤ) :
    probeAutocorr u 0 = integerProbe M u := by
  unfold probeAutocorr
  rw [integerProbe_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [zero_add, atomGram_eq_splineSeries]

private theorem W_sum_left_zeta {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (g : ℝ → ℂ)
    (hf_cd : ∀ i ∈ s, ContDiff ℝ 2 (f i)) (hf_cs : ∀ i ∈ s, HasCompactSupport (f i))
    (hg_cd : ContDiff ℝ 2 g) (hg_cs : HasCompactSupport g) :
    zetaZeroConfig.W (∑ i ∈ s, f i) g = ∑ i ∈ s, zetaZeroConfig.W (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : zetaZeroConfig.W 0 g = 0 := by
      simpa using W_smul_left zetaZeroConfig (0 : ℂ) g g
    simpa using hz
  | insert a s ha ih =>
    have hsum_cd : ContDiff ℝ 2 (∑ i ∈ s, f i) :=
      ContDiff.sum fun i hi => hf_cd i (Finset.mem_insert_of_mem hi)
    have hsum_cs : HasCompactSupport (∑ i ∈ s, f i) :=
      HasCompactSupport.sum fun i hi => hf_cs i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha,
      W_add_left zetaZeroConfig temperedConfig_zetaZeroConfig
        (hf_cd a (Finset.mem_insert_self a s)) (hf_cs a (Finset.mem_insert_self a s))
        hsum_cd hsum_cs hg_cd hg_cs,
      ih (fun i hi => hf_cd i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf_cs i (Finset.mem_insert_of_mem hi)),
      Finset.sum_insert ha]

private theorem W_sum_right_zeta {ι : Type*} (s : Finset ι) (f : ℝ → ℂ) (g : ι → ℝ → ℂ)
    (hf_cd : ContDiff ℝ 2 f) (hf_cs : HasCompactSupport f)
    (hg_cd : ∀ j ∈ s, ContDiff ℝ 2 (g j)) (hg_cs : ∀ j ∈ s, HasCompactSupport (g j)) :
    zetaZeroConfig.W f (∑ j ∈ s, g j) = ∑ j ∈ s, zetaZeroConfig.W f (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : zetaZeroConfig.W f 0 = 0 := by
      simpa using W_smul_right zetaZeroConfig (0 : ℂ) f f
    simpa using hz
  | insert a s ha ih =>
    have hsum_cd : ContDiff ℝ 2 (∑ j ∈ s, g j) :=
      ContDiff.sum fun j hj => hg_cd j (Finset.mem_insert_of_mem hj)
    have hsum_cs : HasCompactSupport (∑ j ∈ s, g j) :=
      HasCompactSupport.sum fun j hj => hg_cs j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert ha,
      W_add_right zetaZeroConfig temperedConfig_zetaZeroConfig hf_cd hf_cs
        (hg_cd a (Finset.mem_insert_self a s)) (hg_cs a (Finset.mem_insert_self a s))
        hsum_cd hsum_cs,
      ih (fun j hj => hg_cd j (Finset.mem_insert_of_mem hj))
        (fun j hj => hg_cs j (Finset.mem_insert_of_mem hj)),
      Finset.sum_insert ha]

private theorem orbitCorr_probePacket_eq {M : ℕ} (u : Fin M → ℤ) (Δ : ℝ) :
    (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).orbitCorr
      (0, 0, ⟨probePacket u, probePacket_mem_realTests u⟩) Δ = probeAutocorr u Δ := by
  rw [configScalingDatum_orbitCorr_eq, tsum_exp_Wsummand_eq_W]
  dsimp only
  let fi : Fin M → ℝ → ℂ := fun i =>
    (u i : ℂ) • ArithmeticCastelnuovoSeveri.translate (Δ + Real.log ((i : ℝ) + 1)) (cx cubicSpline)
  let gj : Fin M → ℝ → ℂ := fun j =>
    (u j : ℂ) • ArithmeticCastelnuovoSeveri.translate (Real.log ((j : ℝ) + 1)) (cx cubicSpline)
  have hcx_l : cx (scaleShift Δ (probePacket u)) = ∑ i : Fin M, fi i := by
    funext t
    simp only [cx, scaleShift, probePacket, fi, ArithmeticCastelnuovoSeveri.translate,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_intCast, sub_sub]
  have hcx_r : cx (probePacket u) = ∑ j : Fin M, gj j := by
    funext t
    simp only [cx, scaleShift, probePacket, gj, ArithmeticCastelnuovoSeveri.translate,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_intCast]
  have hfi_cd (i : Fin M) : ContDiff ℝ 2 (fi i) :=
    (translate_contDiff (cx_contDiff contDiff_cubicSpline) _).const_smul _
  have hfi_cs (i : Fin M) : HasCompactSupport (fi i) :=
    (translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) _).smul_left
  have hgj_cd (j : Fin M) : ContDiff ℝ 2 (gj j) :=
    (translate_contDiff (cx_contDiff contDiff_cubicSpline) _).const_smul _
  have hgj_cs (j : Fin M) : HasCompactSupport (gj j) :=
    (translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) _).smul_left
  rw [hcx_l, hcx_r,
    W_sum_left_zeta Finset.univ fi _ (fun i _ => hfi_cd i) (fun i _ => hfi_cs i)
      (ContDiff.sum fun j _ => hgj_cd j) (HasCompactSupport.sum fun j _ => hgj_cs j),
    Complex.re_sum]
  unfold probeAutocorr
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [W_sum_right_zeta Finset.univ (fi i) gj (hfi_cd i) (hfi_cs i)
    (fun j _ => hgj_cd j) (fun j _ => hgj_cs j), Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only [fi, gj]
  rw [W_smul_left, W_smul_right, W_shiftTest_shiftTest, splineSeries]
  have htsum :
      (∑' ρ : zetaZeroConfig.carrier,
        cexp (((Δ + Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1) : ℝ) : ℂ) * ((ρ : ℂ) - 1 / 2)) *
          zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ) =
      ∑' ρ : zetaZeroConfig.carrier,
        cexp ((((Δ + Real.log ((i : ℝ) + 1) : ℝ) : ℂ) - ((Real.log ((j : ℝ) + 1) : ℝ) : ℂ)) *
          ((ρ : ℂ) - 1 / 2)) *
          zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ :=
    tsum_congr fun ρ => by push_cast; rfl
  rw [← htsum]
  simp only [map_intCast, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
    sub_zero, mul_zero, add_zero]
  ring

/-- **Exponential unboundedness of the cross-scale autocorrelation of any negative witness.**
For every integer probe `u : Fin M → ℤ` with `integerProbe M u < 0` (without any finiteness
hypothesis on the off-line zeros), there exists `σ > 0` such that for every threshold `T₀` and
amplitude `K`, some scale shift `Δ ≥ T₀` satisfies `K * e^{σ Δ} < |probeAutocorr u Δ|`. -/
theorem probeAutocorr_exponential_unbounded_of_neg_integerProbe {M : ℕ} {u : Fin M → ℤ}
    (hneg : integerProbe M u < 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ (T₀ K : ℝ), ∃ Δ : ℝ, T₀ ≤ Δ ∧
      K * Real.exp (σ * Δ) < |probeAutocorr u Δ| := by
  let x_u : ScalingCycle := (0, 0, ⟨probePacket u, probePacket_mem_realTests u⟩)
  have hnot_blind : ¬ BlindOffLine zetaZeroConfig (probePacket u) := by
    intro hb
    have hhw := (configScalingDatum zetaZeroConfig
      temperedConfig_zetaZeroConfig).hasseWeilAt_of_orbitHodgeIndex
      (orbitHodgeIndex_of_blindOffLine zetaZeroConfig temperedConfig_zetaZeroConfig x_u hb) 0
    have hnn : 0 ≤ (configScalingDatum zetaZeroConfig temperedConfig_zetaZeroConfig).orbitCorr x_u 0 :=
      (abs_nonneg _).trans hhw
    rw [orbitCorr_probePacket_eq, probeAutocorr_zero] at hnn
    linarith only [hneg, hnn]
  unfold BlindOffLine at hnot_blind
  push Not at hnot_blind
  obtain ⟨ρ₀, hρ₀_mem, hρ₀_re, hft1, hft2⟩ := hnot_blind
  let σ : ℝ := |ρ₀.re - 1 / 2| / 2
  have hσ_pos : 0 < σ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hρ₀_re))
  have hnot_above : ¬ BlindAbove zetaZeroConfig σ (probePacket u) := by
    intro hab
    have hlt : σ < |ρ₀.re - 1 / 2| := half_lt_self (abs_pos.mpr (sub_ne_zero.mpr hρ₀_re))
    exact (hab ρ₀ hρ₀_mem hlt).elim hft1 hft2
  refine ⟨σ, hσ_pos, fun T₀ K => ?_⟩
  by_contra! hle
  apply hnot_above
  refine blindAbove_of_eventually_le zetaZeroConfig temperedConfig_zetaZeroConfig
    fesSymmetric_zetaZeroConfig hσ_pos.le x_u (T := T₀) (K := K) fun Δ hΔ => ?_
  rw [orbitCorr_probePacket_eq]
  exact hle Δ hΔ

/-- **Refutation of naive asymptotic prime-scale separation (`Δ → +∞`).**
For every zero-sum negative integer witness `u : Fin M → ℤ` (`integerProbe M u < 0`,
`∑ i, u i = 0`), every prime cutoff `P₀`, every multiplicative shell separation `R ≥ 2`, and
every `B > 0`, transporting `u` to two disjoint prime shells separated by factor `> R` yields
signed prime-supported probes `a₁, a₂` with `G₁₁ < 0`, `G₂₂ < 0`, yet `G₁₂² > B · G₁₁ G₂₂`. -/
theorem exists_scaleSeparated_primeCopies_violating_det {M : ℕ} {u : Fin M → ℤ}
    (hneg : integerProbe M u < 0) (hu_sum : (∑ i : Fin M, u i) = 0)
    (P₀ : ℕ) (R : ℕ) (hR : 2 ≤ R) {B : ℝ} (hB : 0 < B) :
    ∃ (N : ℕ) (a₁ a₂ : Fin N → ℤ),
      P₀ < N ∧
      isSignedPrimeSupported a₁ ∧ isSignedPrimeSupported a₂ ∧
      (∀ i : Fin N, a₁ i ≠ 0 → P₀ < i.val + 1) ∧
      (∀ j : Fin N, a₂ j ≠ 0 → P₀ < j.val + 1) ∧
      (∀ i j : Fin N, a₁ i ≠ 0 → a₂ j ≠ 0 → R * (i.val + 1) < j.val + 1) ∧
      Disjoint (activeConductors a₁) (activeConductors a₂) ∧
      probePairing N a₁ a₁ < 0 ∧ probePairing N a₂ a₂ < 0 ∧
      B * (probePairing N a₁ a₁ * probePairing N a₂ a₂) < (probePairing N a₁ a₂) ^ 2 := by
  have hu_ne : u ≠ 0 := by
    rintro rfl
    rw [integerProbe_eq_sum] at hneg
    simp at hneg
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin M, u i ≠ 0 := by simpa [funext_iff] using hu_ne
  obtain ⟨σ, hσ_pos, hunb⟩ := probeAutocorr_exponential_unbounded_of_neg_integerProbe hneg
  let T₀ : ℝ := Real.log (4 * (R : ℝ) * ((M : ℝ) + 1))
  have hT₀_pos : 0 < T₀ := by
    refine Real.log_pos ?_
    have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  let K_amp : ℝ := Real.sqrt (B + 1) * (-integerProbe M u) + 1
  obtain ⟨Δ, hΔ_ge, hΔ_gt⟩ := hunb T₀ K_amp
  have hΔ_nn : 0 ≤ Δ := hT₀_pos.le.trans hΔ_ge
  have hexp_ge1 : 1 ≤ Real.exp (σ * Δ) := Real.one_le_exp (mul_nonneg hσ_pos.le hΔ_nn)
  have hauto_gt : Real.sqrt (B + 1) * (-integerProbe M u) < |probeAutocorr u Δ| := by
    have hK_nn : 0 ≤ K_amp := by dsimp [K_amp]; positivity
    have h1 : K_amp ≤ K_amp * Real.exp (σ * Δ) := le_mul_of_one_le_right hK_nn hexp_ge1
    dsimp [K_amp] at h1
    linarith only [h1, hΔ_gt]
  have hlim_ineq : B * (integerProbe M u * integerProbe M u) < (probeAutocorr u Δ) ^ 2 := by
    have hsq1 : (Real.sqrt (B + 1) * (-integerProbe M u)) ^ 2 < |probeAutocorr u Δ| ^ 2 :=
      pow_lt_pow_left₀ hauto_gt (by positivity) two_ne_zero
    rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ B + 1), neg_sq, sq_abs] at hsq1
    have hq_pos : 0 < (integerProbe M u) ^ 2 := sq_pos_of_ne_zero hneg.ne
    nlinarith only [hsq1, hq_pos]
  let Δ_vec : Fin 2 → ℝ := ![0, Δ]
  have hΔ_vec (r : Fin 2) : 0 ≤ Δ_vec r := by fin_cases r <;> simp [Δ_vec, hΔ_nn]
  obtain ⟨U, _, hU⟩ := exists_shifted_primeBlocks_log_approx 2 M P₀ Δ_vec hΔ_vec
  have hseq (n : ℕ) := hU (max U (n : ℝ)) (le_max_left _ _)
  choose Nseq ιseq hι_inj hι_props using hseq
  have hι_row_inj (n : ℕ) (r : Fin 2) : Function.Injective (ιseq n r) :=
    fun i j hij => Prod.mk.inj_iff.mp (hι_inj n (p₁ := (r, i)) (p₂ := (r, j)) hij) |>.2
  let a₁seq (n : ℕ) : Fin (Nseq n) → ℤ := Function.extend (ιseq n 0) u 0
  let a₂seq (n : ℕ) : Fin (Nseq n) → ℤ := Function.extend (ιseq n 1) u 0
  have hzero : Tendsto (fun n : ℕ => (6 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hexp_bound (n : ℕ) (hn1 : 1 ≤ n) :
      2 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ)) ≤ (6 : ℝ) / (n : ℝ) := by
    have hlin : (1 / 3 : ℝ) * (n : ℝ) ≤ Real.exp ((1 / 3 : ℝ) * (n : ℝ)) := by
      linarith [Real.add_one_le_exp ((1 / 3 : ℝ) * (n : ℝ))]
    rw [neg_mul, Real.exp_neg]
    have hinv := inv_anti₀ (by positivity : 0 < (1 / 3 : ℝ) * (n : ℝ)) hlin
    rw [show ((1 / 3 : ℝ) * (n : ℝ))⁻¹ = (3 : ℝ) / (n : ℝ) by field_simp] at hinv
    calc 2 * (Real.exp ((1 / 3 : ℝ) * (n : ℝ)))⁻¹ ≤ 2 * ((3 : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 6 / (n : ℝ) := by ring
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt U
  have hconv_block (r s : Fin 2) :
      Tendsto (fun n : ℕ => probePairing (Nseq n)
        (Function.extend (ιseq n r) u 0) (Function.extend (ιseq n s) u 0))
        atTop (𝓝 (∑ i : Fin M, ∑ j : Fin M,
          (splineSeries (Δ_vec r - Δ_vec s + Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))).re *
            (u i : ℝ) * (u j : ℝ))) := by
    refine (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => ?_).congr fun n =>
        (extend_probePairing_eq (hι_row_inj n r) (hι_row_inj n s) u u).symm
    have harg : Tendsto
        (fun n : ℕ =>
          Real.log (((ιseq n r i).val : ℝ) + 1) - Real.log (((ιseq n s j).val : ℝ) + 1))
        atTop (𝓝 (Δ_vec r - Δ_vec s + Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (by simpa only [sub_zero] using tendsto_const_nhds.sub hzero)
        (by simpa only [add_zero] using tendsto_const_nhds.add hzero) ?_ ?_
      · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
        have hmax : max U (n : ℝ) = (n : ℝ) :=
          max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
        have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
        have hi := (hι_props n r i).2.2
        have hj := (hι_props n s j).2.2
        rw [hmax] at hi hj
        linarith only [hi.2, hj.1, hb]
      · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
        have hmax : max U (n : ℝ) = (n : ℝ) :=
          max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
        have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
        have hi := (hι_props n r i).2.2
        have hj := (hι_props n s j).2.2
        rw [hmax] at hi hj
        linarith only [hi.1, hj.2, hb]
    have hsp := ((Complex.continuous_re.comp continuous_splineSeries).tendsto _).comp harg
    refine ((hsp.mul_const (u i : ℝ)).mul_const (u j : ℝ)).congr fun n => ?_
    dsimp only [Function.comp_apply]
    rw [atomGram_eq_splineSeries]
  have hconv11 : Tendsto (fun n : ℕ => probePairing (Nseq n) (a₁seq n) (a₁seq n))
      atTop (𝓝 (integerProbe M u)) := by
    simpa only [Δ_vec, Matrix.cons_val_zero, sub_self, ← probeAutocorr, probeAutocorr_zero]
      using hconv_block 0 0
  have hconv22 : Tendsto (fun n : ℕ => probePairing (Nseq n) (a₂seq n) (a₂seq n))
      atTop (𝓝 (integerProbe M u)) := by
    simpa only [Δ_vec, Matrix.cons_val_one, Matrix.head_cons, sub_self, ← probeAutocorr,
      probeAutocorr_zero] using hconv_block 1 1
  have hconv12 : Tendsto (fun n : ℕ => probePairing (Nseq n) (a₁seq n) (a₂seq n))
      atTop (𝓝 (probeAutocorr u Δ)) := by
    have h21 := hconv_block 1 0
    simp only [Δ_vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_zero] at h21
    exact h21.congr fun n => probePairing_symm (Nseq n) (a₂seq n) (a₁seq n)
  have hev_ineq : ∀ᶠ n : ℕ in atTop,
      probePairing (Nseq n) (a₁seq n) (a₁seq n) < 0 ∧
      probePairing (Nseq n) (a₂seq n) (a₂seq n) < 0 ∧
      B * (probePairing (Nseq n) (a₁seq n) (a₁seq n) * probePairing (Nseq n) (a₂seq n) (a₂seq n)) <
        (probePairing (Nseq n) (a₁seq n) (a₂seq n)) ^ 2 := by
    refine (hconv11.eventually (gt_mem_nhds hneg)).and
      ((hconv22.eventually (gt_mem_nhds hneg)).and ?_)
    have hlhs := (hconv11.mul hconv22).const_mul B
    have hrhs := hconv12.pow 2
    exact (tendsto_order.mp (hrhs.sub hlhs)).1 0 (sub_pos.mpr hlim_ineq) |>.mono fun n hn => by
      linarith only [hn]
  obtain ⟨n, h11_n, h22_n, hdet_n⟩ := (hev_ineq.and (eventually_ge_atTop (max N₀ 9))).exists
  obtain ⟨⟨h11_neg, h22_neg, hdet_gt⟩, hn_ge⟩ :=
    ⟨⟨h11_n, h22_n.1, h22_n.2.1⟩, h22_n.2.2⟩
  have hmax : max U (n : ℝ) = (n : ℝ) :=
    max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 9).trans hn_ge))
  have hb_small : 2 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ)) ≤ 1 := by
    have hn9 : 9 ≤ n := (le_max_right N₀ 9).trans hn_ge
    have hb := hexp_bound n (by omega)
    have h69 : (6 : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast (by omega : 0 < n))]
      exact_mod_cast (by omega : 6 ≤ n)
    exact hb.trans h69
  have hsep (i j : Fin (Nseq n)) (hi : a₁seq n i ≠ 0) (hj : a₂seq n j ≠ 0) :
      R * (i.val + 1) < j.val + 1 := by
    have hex_i : ∃ k : Fin M, ιseq n 0 k = i := by
      by_contra hno; exact hi (Function.extend_apply' _ _ _ hno)
    have hex_j : ∃ k' : Fin M, ιseq n 1 k' = j := by
      by_contra hno; exact hj (Function.extend_apply' _ _ _ hno)
    obtain ⟨k, rfl⟩ := hex_i
    obtain ⟨k', rfl⟩ := hex_j
    have hk_up := (hι_props n 0 k).2.2.1
    have hk'_lo := (hι_props n 1 k').2.2.2
    rw [hmax] at hk_up hk'_lo
    simp only [Δ_vec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, add_zero]
      at hk_up hk'_lo
    have hk_le_M : ((k : ℝ) + 1) ≤ (M : ℝ) + 1 := by
      have := k.isLt
      have hlt : (k : ℝ) < M := by exact_mod_cast this
      linarith
    have hlog_k_le : Real.log ((k : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1) :=
      Real.log_le_log (by positivity) hk_le_M
    have hlog_k'_nn : 0 ≤ Real.log ((k' : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k'])
    have he1 : Real.exp 1 ≤ 3 := by
      have h := Real.exp_one_lt_d9.le; linarith
    have hlog_4 : Real.log 4 > 1 := by
      rw [gt_iff_lt, Real.lt_log_iff_exp_lt (by norm_num)]
      linarith
    have hlog_R_diff :
        Real.log ((R : ℝ) * (((ιseq n 0 k).val : ℝ) + 1)) <
          Real.log (((ιseq n 1 k').val : ℝ) + 1) := by
      have hR_pos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
      rw [Real.log_mul hR_pos.ne' (by positivity)]
      have hT₀_split : T₀ = Real.log 4 + Real.log R + Real.log ((M : ℝ) + 1) := by
        dsimp [T₀]
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) hR_pos.ne']
      linarith only [hk_up, hk'_lo, hΔ_ge, hT₀_split, hlog_k_le, hlog_k'_nn, hb_small, hlog_4]
    have hreal_lt : (R : ℝ) * (((ιseq n 0 k).val : ℝ) + 1) < ((ιseq n 1 k').val : ℝ) + 1 := by
      have hR_pos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog_R_diff
    exact_mod_cast hreal_lt
  have hdisj : Disjoint (activeConductors (a₁seq n)) (activeConductors (a₂seq n)) := by
    rw [disjoint_activeConductors_iff]
    intro ℓ
    by_contra! hboth
    have hlt := hsep ℓ ℓ hboth.1 hboth.2
    nlinarith only [hR, hlt]
  have hN_gt : P₀ < Nseq n := by
    have h1 := (hι_props n 0 i₀).2.1
    have h2 := (ιseq n 0 i₀).isLt
    omega
  exact ⟨Nseq n, a₁seq n, a₂seq n, hN_gt,
    (isSignedPrimeSupported_extend (hι_row_inj n 0)
      (fun i => ⟨(hι_props n 0 i).1, (hι_props n 0 i).2.1⟩) hu_ne hu_sum).1,
    (isSignedPrimeSupported_extend (hι_row_inj n 1)
      (fun i => ⟨(hι_props n 1 i).1, (hι_props n 1 i).2.1⟩) hu_ne hu_sum).1,
    (isSignedPrimeSupported_extend (hι_row_inj n 0)
      (fun i => ⟨(hι_props n 0 i).1, (hι_props n 0 i).2.1⟩) hu_ne hu_sum).2,
    (isSignedPrimeSupported_extend (hι_row_inj n 1)
      (fun i => ⟨(hι_props n 1 i).1, (hι_props n 1 i).2.1⟩) hu_ne hu_sum).2,
    hsep, hdisj, h11_neg, h22_neg, hdet_gt⟩

/-! ### 5. Finite-mode quotient positivity and near-annihilating prime probes -/

/-- Logarithmic mode character `u ↦ u^{conj ρ - 1/2}` associated to a zero `ρ`. -/
abbrev modeChar (ρ : ℂ) : HeckeLattice →* ℂ := zeroChar (conj ρ)

/-- Joint linear evaluation map of the finite mode set `S₀` on horizon-`N` coefficient vectors. -/
def modeEvalMap (S₀ : Finset ℂ) (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (↥S₀ → ℂ) :=
  LinearMap.pi fun ρ : ↥S₀ =>
    charEval (modeChar ρ.1) (fun i : Fin N => natSlope i.val)

/-- Scale-invariant hyperbolic pair product `‖χ_ρ(c)‖ · ‖χ_ρ†(c)‖` at mode `ρ` and horizon `N`. -/
def modePairProduct (ρ : ℂ) (N : ℕ) (c : Fin N → ℂ) : ℝ :=
  ‖charEval (modeChar ρ) (fun i : Fin N => natSlope i.val) c‖ *
    ‖charEval (reflectChar (modeChar ρ)) (fun i : Fin N => natSlope i.val) c‖

private theorem gram_natSlope_eq_atomGram' (N : ℕ) :
    gram zetaKernel (fun i : Fin N => natSlope i.val) = atomGram N := by
  rw [gram_zetaKernel_eq_weilGram]
  simp only [scale_natSlope, Nat.cast_add_one]
  rfl

/-- **Quotient positivity law:** if `rightZeros zetaZeroConfig ⊆ S₀`, then `atomGram N` is strictly
positive definite on `ker (modeEvalMap S₀ N)` at every horizon `N`. -/
theorem isPosDefOn_atomGram_ker_modeEvalMap {S₀ : Finset ℂ}
    (hsub : rightZeros zetaZeroConfig ⊆ (S₀ : Set ℂ)) (N : ℕ) :
    IsPosDefOn (atomGram N) (LinearMap.ker (modeEvalMap S₀ N)) := by
  classical
  have hf : (rightZeros zetaZeroConfig).Finite := S₀.finite_toSet.subset hsub
  let R := hf.toFinset
  let x : Fin N → HeckeLattice := fun i => natSlope i.val
  let ω (ρ : ℂ) := conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ)
  intro c hc hc0
  have hz : zetaKernel = fun u => orbitKernel zetaOnLine cubicSpline u +
      ∑ ρ ∈ R, pairKernel (modeChar ρ) (ω ρ) u :=
    funext (orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig cubicSpline_mem_realTests hf)
  rw [← gram_natSlope_eq_atomGram', hz, hermQuad_gram_add, hermQuad_gram_sum]
  have hterm (ρ : ℂ) (hρ : ρ ∈ R) : hermQuad (gram (pairKernel (modeChar ρ) (ω ρ)) x) c = 0 := by
    have hρS : ρ ∈ S₀ := hsub (hf.mem_toFinset.mp hρ)
    have he : charEval (modeChar ρ) x c = 0 :=
      congrFun (LinearMap.mem_ker.mp hc) ⟨ρ, hρS⟩
    rw [hermQuad_gram_pairKernel, he]
    simp
  rw [Finset.sum_eq_zero hterm, add_zero]
  exact hermQuad_gram_onLine_natSlope_pos Fin.val_injective hc0

/-- **Uniform mode pair-product lower bound under `rightZeros zetaZeroConfig ⊆ S₀`.**
There exists an `N`-independent constant `η > 0` such that every probe `a : Fin N → ℤ` with
`integerProbe N a < 0` has `η · (-integerProbe N a) ≤ modePairProduct ρ N a` for some `ρ ∈ S₀`. -/
theorem exists_uniform_modePair_lower_of_rightZeros_subset {S₀ : Finset ℂ}
    (hsub : rightZeros zetaZeroConfig ⊆ (S₀ : Set ℂ)) :
    ∃ η : ℝ, 0 < η ∧ ∀ (N : ℕ) (a : Fin N → ℤ), integerProbe N a < 0 →
      ∃ ρ ∈ S₀, η * (-integerProbe N a) ≤ modePairProduct ρ N (fun i => (a i : ℂ)) := by
  classical
  have hf : (rightZeros zetaZeroConfig).Finite := S₀.finite_toSet.subset hsub
  let R := hf.toFinset
  have hR_sub : R ⊆ S₀ := fun ρ hρ => hsub (hf.mem_toFinset.mp hρ)
  let ω (ρ : ℂ) := conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ)
  let W_tot : ℝ := 1 + ∑ ρ ∈ S₀, 2 * ‖ω ρ‖
  have hW_pos : 0 < W_tot := by
    dsimp [W_tot]
    have hnn : 0 ≤ ∑ ρ ∈ S₀, 2 * ‖ω ρ‖ := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  refine ⟨1 / W_tot, by positivity, fun N a hneg => ?_⟩
  let x : Fin N → HeckeLattice := fun i => natSlope i.val
  let c : Fin N → ℂ := fun i => (a i : ℂ)
  have hc0 : c ≠ 0 := by
    intro h0
    have ha0 : a = 0 := funext fun i => by exact_mod_cast congrFun h0 i
    subst ha0
    rw [integerProbe_eq_sum] at hneg
    simp at hneg
  have hz : zetaKernel = fun u => orbitKernel zetaOnLine cubicSpline u +
      ∑ ρ ∈ R, pairKernel (modeChar ρ) (ω ρ) u :=
    funext (orbitKernel_eq_onLine_add_pairs temperedConfig_zetaZeroConfig cubicSpline_mem_realTests hf)
  have hquad : integerProbe N a =
      hermQuad (gram (orbitKernel zetaOnLine cubicSpline) x) c +
        ∑ ρ ∈ R, hermQuad (gram (pairKernel (modeChar ρ) (ω ρ)) x) c := by
    unfold integerProbe
    rw [← gram_natSlope_eq_atomGram', hz, hermQuad_gram_add, hermQuad_gram_sum]
  have hon_pos : 0 < hermQuad (gram (orbitKernel zetaOnLine cubicSpline) x) c :=
    hermQuad_gram_onLine_natSlope_pos Fin.val_injective hc0
  have hS₀_ne : S₀.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hR_empty : R = ∅ := Finset.subset_empty.mp (hempty ▸ hR_sub)
    rw [hR_empty, Finset.sum_empty, add_zero] at hquad
    linarith only [hneg, hquad, hon_pos]
  obtain ⟨ρ_max, hρ_max, hmax⟩ := S₀.exists_max_image (fun ρ => modePairProduct ρ N c) hS₀_ne
  have hpair_ge :
      -∑ ρ ∈ R, hermQuad (gram (pairKernel (modeChar ρ) (ω ρ)) x) c ≤
        W_tot * modePairProduct ρ_max N c := by
    have hterm (ρ : ℂ) (hρ : ρ ∈ R) :
        -hermQuad (gram (pairKernel (modeChar ρ) (ω ρ)) x) c ≤
          (2 * ‖ω ρ‖) * modePairProduct ρ_max N c := by
      rw [hermQuad_gram_pairKernel]
      have h1 : -(2 * (ω ρ * charEval (modeChar ρ) x c *
          conj (charEval (reflectChar (modeChar ρ)) x c)).re) ≤
          2 * ‖ω ρ * charEval (modeChar ρ) x c *
            conj (charEval (reflectChar (modeChar ρ)) x c)‖ := by
        have habs := Complex.abs_re_le_norm
          (ω ρ * charEval (modeChar ρ) x c * conj (charEval (reflectChar (modeChar ρ)) x c))
        linarith [(neg_le_abs _).trans habs]
      rw [norm_mul, norm_mul, Complex.norm_conj] at h1
      calc -2 * (ω ρ * charEval (modeChar ρ) x c *
              conj (charEval (reflectChar (modeChar ρ)) x c)).re
          ≤ 2 * (‖ω ρ‖ * modePairProduct ρ N c) := by
            unfold modePairProduct; linarith only [h1]
        _ ≤ (2 * ‖ω ρ‖) * modePairProduct ρ_max N c := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (hmax ρ (hR_sub hρ)) (by positivity)
    rw [← Finset.sum_neg_distrib]
    calc ∑ ρ ∈ R, -hermQuad (gram (pairKernel (modeChar ρ) (ω ρ)) x) c
        ≤ ∑ ρ ∈ R, (2 * ‖ω ρ‖) * modePairProduct ρ_max N c := Finset.sum_le_sum hterm
      _ ≤ ∑ ρ ∈ S₀, (2 * ‖ω ρ‖) * modePairProduct ρ_max N c :=
          Finset.sum_le_sum_of_subset_of_nonneg hR_sub fun ρ _ _ =>
            mul_nonneg (by positivity) (by unfold modePairProduct; positivity)
      _ = (∑ ρ ∈ S₀, 2 * ‖ω ρ‖) * modePairProduct ρ_max N c := (Finset.sum_mul _ _ _).symm
      _ ≤ W_tot * modePairProduct ρ_max N c := by
          dsimp [W_tot]
          have hmp_nn : 0 ≤ modePairProduct ρ_max N c := by unfold modePairProduct; positivity
          nlinarith only [hmp_nn]
  refine ⟨ρ_max, hρ_max, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hW_pos, one_mul, mul_comm]
  linarith only [hquad, hon_pos, hpair_ge]

/-- Real packet `∑_{i < M} v_i B(· - log(i + 1))` with real weights `v : Fin M → ℝ`. -/
def realProbePacket {M : ℕ} (v : Fin M → ℝ) : ℝ → ℝ :=
  ∑ i : Fin M, v i • scaleShift (Real.log ((i : ℝ) + 1)) cubicSpline

theorem realProbePacket_mem_realTests {M : ℕ} (v : Fin M → ℝ) : realProbePacket v ∈ realTests :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (v i) (scaleShift_mem _ cubicSpline_mem_realTests)

private theorem paperFT_realProbePacket_gammaOf_conj {M : ℕ} (v : Fin M → ℝ) (ρ : ℂ) :
    paperFT (cx (realProbePacket v)) (gammaOf (conj ρ)) =
      charEval (modeChar ρ) (fun i : Fin M => natSlope i.val) (fun i => (v i : ℂ)) *
        paperFT (cx cubicSpline) (gammaOf (conj ρ)) := by
  have hcx : cx (realProbePacket v) =
      ∑ i : Fin M, (v i : ℂ) • ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1))
        (cx cubicSpline) := by
    funext u
    simp [cx, realProbePacket, scaleShift, ArithmeticCastelnuovoSeveri.translate,
      Finset.sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
  have hind : ∀ s : Finset (Fin M),
      paperFT (∑ i ∈ s, (v i : ℂ) •
        ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline))
        (gammaOf (conj ρ)) =
      (∑ i ∈ s, (v i : ℂ) * modeChar ρ (natSlope i.val)) *
        paperFT (cx cubicSpline) (gammaOf (conj ρ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [paperFT]
    | insert a s ha ih =>
      have hc (i : Fin M) : ContDiff ℝ 2 ((v i : ℂ) •
          ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline)) :=
        (translate_contDiff (cx_contDiff contDiff_cubicSpline) _).const_smul _
      have hs' (i : Fin M) : HasCompactSupport ((v i : ℂ) •
          ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline)) :=
        (translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) _).smul_left
      rw [Finset.sum_insert ha,
        paperFT_add (hc a).continuous (hs' a)
          (ContDiff.sum fun i _ => hc i).continuous (HasCompactSupport.sum fun i _ => hs' i),
        ih, paperFT_smul, ← cx_scaleShift_eq_translate, paperFT_cx_scaleShift_apply,
        Finset.sum_insert ha]
      have hmode : cexp ((Real.log ((a : ℝ) + 1) : ℂ) * (I * gammaOf (conj ρ))) =
          modeChar ρ (natSlope a.val) := by
        have hI : I * gammaOf (conj ρ) = conj ρ - 1 / 2 := by
          rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]
        rw [hI, modeChar, zeroChar, logChar_apply, scale_natSlope]
        push_cast; ring_nf
      rw [hmode]; ring
  rw [hcx, hind Finset.univ, charEval_apply]

/-- Among `{2, 3, 5}`, at least one prime `q` satisfies both `q^{ρ_* - ρ} ≠ 1` and
`q^{ρ_* - conj ρ} ≠ 1` whenever `ρ_* ∉ {ρ, conj ρ}`, by irrationality of `log p / log q`. -/
private theorem exists_prime_235_separating_pair {ρ ρ_star : ℂ}
    (hne1 : ρ_star ≠ ρ) (hne2 : ρ_star ≠ conj ρ) :
    ∃ q : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ 2 ≤ q ∧
      cexp ((Real.log q : ℂ) * (ρ_star - ρ)) ≠ 1 ∧
      cexp ((Real.log q : ℂ) * (ρ_star - conj ρ)) ≠ 1 := by
  have no_two_primes {z : ℂ} (hz : z ≠ 0) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
      ¬ (cexp ((Real.log p : ℂ) * z) = 1 ∧ cexp ((Real.log q : ℂ) * z) = 1) := by
    rintro ⟨h1, h2⟩
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hre : z.re = 0 := by
      have hr := congrArg Complex.re hm
      simp only [Complex.re_ofReal_mul, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul] at hr
      exact (mul_eq_zero.mp hr).resolve_left hlogp.ne'
    have him_ne : z.im ≠ 0 := fun him0 => hz (Complex.ext hre him0)
    have him_p : Real.log p * z.im = m * (2 * π) := by
      have hi := congrArg Complex.im hm
      simp only [Complex.im_ofReal_mul] at hi
      have h2pi : ((m : ℂ) * (2 * ↑π * I)).im = m * (2 * π) := by simp [ mul_assoc]
      linarith
    have him_q : Real.log q * z.im = n * (2 * π) := by
      have hi := congrArg Complex.im hn
      simp only [Complex.im_ofReal_mul] at hi
      have h2pi : ((n : ℂ) * (2 * ↑π * I)).im = n * (2 * π) := by simp [mul_assoc]
      linarith
    have hm_ne : m ≠ 0 := by
      intro hm0; rw [hm0, Int.cast_zero, zero_mul] at him_p
      exact mul_ne_zero hlogp.ne' him_ne him_p
    have hrat : Real.log q / Real.log p = ((n : ℚ) / (m : ℚ) : ℚ) := by
      have h2pi_ne : (2 * π : ℝ) ≠ 0 := by positivity
      have hz_eq : z.im = m * (2 * π) / Real.log p := (eq_div_iff hlogp.ne').mpr (by linarith)
      rw [hz_eq] at him_q
      have hm_r : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm_ne
      push_cast
      field_simp at him_q ⊢
      linarith
    exact _root_.RHTower.irrational_log_ratio hq hp hpq.symm ⟨(n : ℚ) / (m : ℚ), hrat.symm⟩
  have hz1 : ρ_star - ρ ≠ 0 := sub_ne_zero.mpr hne1
  have hz2 : ρ_star - conj ρ ≠ 0 := sub_ne_zero.mpr hne2
  by_cases h2 : cexp ((Real.log (2 : ℕ) : ℂ) * (ρ_star - ρ)) ≠ 1 ∧
      cexp ((Real.log (2 : ℕ) : ℂ) * (ρ_star - conj ρ)) ≠ 1
  · exact ⟨2, Or.inl rfl, by decide, h2.1, h2.2⟩
  by_cases h3 : cexp ((Real.log (3 : ℕ) : ℂ) * (ρ_star - ρ)) ≠ 1 ∧
      cexp ((Real.log (3 : ℕ) : ℂ) * (ρ_star - conj ρ)) ≠ 1
  · exact ⟨3, Or.inr (Or.inl rfl), by decide, h3.1, h3.2⟩
  by_cases h5 : cexp ((Real.log (5 : ℕ) : ℂ) * (ρ_star - ρ)) ≠ 1 ∧
      cexp ((Real.log (5 : ℕ) : ℂ) * (ρ_star - conj ρ)) ≠ 1
  · exact ⟨5, Or.inr (Or.inr rfl), by decide, h5.1, h5.2⟩
  exfalso
  rw [not_and_or, not_not, not_not] at h2 h3 h5
  rcases h2 with h2a | h2b <;> rcases h3 with h3a | h3b <;> rcases h5 with h5a | h5b
  · exact no_two_primes hz1 Nat.prime_two Nat.prime_three (by decide) ⟨h2a, h3a⟩
  · exact no_two_primes hz1 Nat.prime_two Nat.prime_three (by decide) ⟨h2a, h3a⟩
  · exact no_two_primes hz1 Nat.prime_two Nat.prime_five (by decide) ⟨h2a, h5a⟩
  · exact no_two_primes hz2 Nat.prime_three Nat.prime_five (by decide) ⟨h3b, h5b⟩
  · exact no_two_primes hz1 Nat.prime_three Nat.prime_five (by decide) ⟨h3a, h5a⟩
  · exact no_two_primes hz2 Nat.prime_two Nat.prime_five (by decide) ⟨h2b, h5b⟩
  · exact no_two_primes hz2 Nat.prime_two Nat.prime_three (by decide) ⟨h2b, h3b⟩
  · exact no_two_primes hz2 Nat.prime_two Nat.prime_three (by decide) ⟨h2b, h3b⟩

/-- Dilated zero-extension placing `v i` at integer coordinate `m * (i + 1) - 1 < L`. -/
private def dilateVec {M L : ℕ} (m : ℕ) (hm : 1 ≤ m) (hmL : m * M ≤ L) (v : Fin M → ℝ) :
    Fin L → ℝ :=
  Function.extend (fun i : Fin M => (⟨m * (i.val + 1) - 1, by have := i.isLt; nlinarith⟩ : Fin L)) v 0

private theorem dilateVec_properties {M L : ℕ} (m : ℕ) (hm : 1 ≤ m) (hmL : m * M ≤ L)
    (v : Fin M → ℝ) :
    (∑ ℓ : Fin L, dilateVec m hm hmL v ℓ) = (∑ i : Fin M, v i) ∧
    realProbePacket (dilateVec m hm hmL v) = scaleShift (Real.log m) (realProbePacket v) := by
  let emb : Fin M → Fin L := fun i => ⟨m * (i.val + 1) - 1, by have := i.isLt; nlinarith⟩
  have hemb_val (i : Fin M) : (emb i).val + 1 = m * (i.val + 1) := by
    dsimp [emb]; have := i.isLt; nlinarith
  have hemb_inj : Function.Injective emb := by
    intro i j hij
    have h1 := hemb_val i; have h2 := hemb_val j
    have heq : m * (i.val + 1) = m * (j.val + 1) := by rw [← h1, ← h2, congrArg Fin.val hij]
    have hij_val := Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) heq
    exact Fin.ext (by omega)
  have hoff (ℓ : Fin L) (hℓ : ℓ ∉ Finset.univ.image emb) : dilateVec m hm hmL v ℓ = 0 :=
    Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  constructor
  · rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb)) fun ℓ _ hℓ => hoff ℓ hℓ,
      Finset.sum_image fun i _ j _ h => hemb_inj h]
    exact Finset.sum_congr rfl fun i _ => hemb_inj.extend_apply v 0 i
  · funext u
    unfold realProbePacket
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, scaleShift]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb)) fun ℓ _ hℓ => by
      rw [hoff ℓ hℓ, zero_mul],
      Finset.sum_image fun i _ j _ h => hemb_inj h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hemb_inj.extend_apply v 0 i]
    have hcast : (((emb i).val : ℝ) + 1) = (m : ℝ) * ((i : ℝ) + 1) := by exact_mod_cast hemb_val i
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
    rw [hcast, Real.log_mul hm_pos.ne' (by positivity), sub_sub, add_comm (Real.log m)]

/-- Single-step real 3-point integer-dilation annihilator for a pair `{ρ, conj ρ}` preserving
zero sum and visibility of `ρ_star ∉ {ρ, conj ρ}`. -/
private theorem exists_realProbePacket_annihilating_step {M : ℕ} (hM2 : 2 ≤ M) (v : Fin M → ℝ)
    (hv_sum : (∑ i : Fin M, v i) = 0) {ρ ρ_star : ℂ} (hρ_re : 1 / 2 < ρ.re)
    (hstar_re : 1 / 2 < ρ_star.re) (hne1 : ρ_star ≠ ρ) (hne2 : ρ_star ≠ conj ρ)
    (hsees : Sees (realProbePacket v) ρ_star) :
    ∃ (M' : ℕ) (v' : Fin M' → ℝ),
      2 ≤ M' ∧
      (∑ i : Fin M', v' i) = 0 ∧
      (∀ z : ℂ, paperFT (cx (realProbePacket v)) z = 0 → paperFT (cx (realProbePacket v')) z = 0) ∧
      paperFT (cx (realProbePacket v')) (gammaOf (conj ρ)) = 0 ∧
      Sees (realProbePacket v') ρ_star := by
  obtain ⟨q, _, hq2, hsep1, hsep2⟩ := exists_prime_235_separating_pair hne1 hne2
  let M' := q ^ 2 * M
  have hM'2 : 2 ≤ M' := by dsimp [M']; nlinarith
  have h1M : 1 * M ≤ M' := by dsimp [M']; nlinarith
  have hqM : q * M ≤ M' := by dsimp [M']; nlinarith
  let w : ℂ := cexp (-(Real.log q : ℂ) * (ρ - 1 / 2))
  let v' : Fin M' → ℝ :=
    dilateVec 1 le_rfl h1M v - (2 * w.re) • dilateVec q (by omega) hqM v +
      (‖w‖ ^ 2) • dilateVec (q ^ 2) (by nlinarith) le_rfl v
  have hd1 := dilateVec_properties 1 le_rfl h1M v
  have hdq := dilateVec_properties q (by omega) hqM v
  have hdq2 := dilateVec_properties (q ^ 2) (by nlinarith) le_rfl v
  have hv'_sum : (∑ i : Fin M', v' i) = 0 := by
    dsimp [v']
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      hd1.1, hdq.1, hdq2.1, hv_sum, mul_zero, sub_zero, add_zero]
  have hpkt : realProbePacket v' =
      realProbePacket v - (2 * w.re) • scaleShift (Real.log q) (realProbePacket v) +
        (‖w‖ ^ 2) • scaleShift (2 * Real.log q) (realProbePacket v) := by
    have hlog1 : Real.log (1 : ℕ) = 0 := by simp
    have hlogq2 : Real.log ((q ^ 2 : ℕ) : ℝ) = 2 * Real.log q := by
      push_cast; rw [Real.log_pow]; ring
    funext u
    have hlin : realProbePacket v' u =
        realProbePacket (dilateVec 1 le_rfl h1M v) u -
          2 * w.re * realProbePacket (dilateVec q (by omega) hqM v) u +
          ‖w‖ ^ 2 * realProbePacket (dilateVec (q ^ 2) (by nlinarith) le_rfl v) u := by
      unfold realProbePacket
      simp only [v', Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
    rw [hlin, hd1.2, hdq.2, hdq2.2, hlog1, scaleShift_zero, hlogq2]
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hft (z : ℂ) : paperFT (cx (realProbePacket v')) z =
      (1 - w * cexp ((Real.log q : ℂ) * (I * z))) *
        (1 - conj w * cexp ((Real.log q : ℂ) * (I * z))) *
        paperFT (cx (realProbePacket v)) z := by
    have hf := realProbePacket_mem_realTests v
    have hsh1 := scaleShift_mem (Real.log q) hf
    have hsh2 := scaleShift_mem (2 * Real.log q) hf
    have hcx : cx (realProbePacket v') =
        (cx (realProbePacket v) + ((-2 * w.re : ℝ) : ℂ) • cx (scaleShift (Real.log q) (realProbePacket v))) +
          ((‖w‖ ^ 2 : ℝ) : ℂ) • cx (scaleShift (2 * Real.log q) (realProbePacket v)) := by
      funext u; rw [hpkt]; simp [cx]; ring
    rw [hcx,
      paperFT_add
        ((cx_contDiff hf.1).continuous.add (((cx_contDiff hsh1.1).continuous).const_smul _))
        ((cx_hasCompactSupport hf.2).add ((cx_hasCompactSupport hsh1.2).smul_left))
        (((cx_contDiff hsh2.1).continuous).const_smul _) ((cx_hasCompactSupport hsh2.2).smul_left),
      paperFT_add (cx_contDiff hf.1).continuous (cx_hasCompactSupport hf.2)
        (((cx_contDiff hsh1.1).continuous).const_smul _) ((cx_hasCompactSupport hsh1.2).smul_left),
      paperFT_smul, paperFT_smul, paperFT_cx_scaleShift_apply, paperFT_cx_scaleShift_apply]
    set X : ℂ := cexp ((Real.log q : ℂ) * (I * z))
    have hX2 : cexp (((2 * Real.log q : ℝ) : ℂ) * (I * z)) = X ^ 2 := by
      dsimp [X]; rw [← Complex.exp_nat_mul]; push_cast; ring_nf
    have hw_conj : w + conj w = ((2 * w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [two_mul]
    have hw_norm : w * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hX2, ← hw_conj, ← hw_norm]
    ring
  refine ⟨M', v', hM'2, hv'_sum, ?_, ?_, ?_⟩
  · intro z hz; rw [hft, hz, mul_zero]
  · rw [hft]
    have hI : I * gammaOf (conj ρ) = conj ρ - 1 / 2 := by
      rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]
    have hcw : conj w = cexp (-(Real.log q : ℂ) * (conj ρ - 1 / 2)) := by
      dsimp [w]
      rw [← Complex.exp_conj]
      simp [Complex.conj_ofReal]
    rw [hI, hcw, ← Complex.exp_add]
    have h0 : -(Real.log q : ℂ) * (conj ρ - 1 / 2) + (Real.log q : ℂ) * (conj ρ - 1 / 2) = 0 := by
      ring
    rw [h0, Complex.exp_zero, sub_self, mul_zero, zero_mul]
  · obtain ⟨hs1, hs2⟩ := hsees
    have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    refine ⟨?_, ?_⟩
    · rw [hft]
      have hI : I * gammaOf ρ_star = ρ_star - 1 / 2 := by
        rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]
      have hw1 : w * cexp ((Real.log q : ℂ) * (I * gammaOf ρ_star)) =
          cexp ((Real.log q : ℂ) * (ρ_star - ρ)) := by
        dsimp [w]; rw [hI, ← Complex.exp_add]; congr 1; ring
      have hw2 : conj w * cexp ((Real.log q : ℂ) * (I * gammaOf ρ_star)) =
          cexp ((Real.log q : ℂ) * (ρ_star - conj ρ)) := by
        dsimp [w]; rw [← Complex.exp_conj, hI, ← Complex.exp_add]
        simp only [map_mul, map_neg, Complex.conj_ofReal, map_sub, map_div₀, map_one, map_ofNat]
        congr 1; ring
      rw [hw1, hw2]
      exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hsep1.symm) (sub_ne_zero.mpr hsep2.symm)) hs1
    · rw [hft]
      have hI : I * conj (gammaOf ρ_star) = 1 / 2 - conj ρ_star := by
        rw [← gammaOf_reflect, gammaOf, mul_div_cancel₀ _ I_ne_zero, reflect]
      have hnorm_w : ‖w‖ < 1 := by
        dsimp [w]
        rw [Complex.norm_exp]
        have hre : (-(Real.log q : ℂ) * (ρ - 1 / 2)).re = -Real.log q * (ρ.re - 1 / 2) := by
          simp
        rw [hre]
        exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hlogq) (by linarith))
      have hnorm_X : ‖cexp ((Real.log q : ℂ) * (I * conj (gammaOf ρ_star)))‖ < 1 := by
        rw [hI, Complex.norm_exp, Complex.re_ofReal_mul, Complex.sub_re, Complex.conj_re]
        exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg hlogq (by linarith))
      have hf1 : 1 - w * cexp ((Real.log q : ℂ) * (I * conj (gammaOf ρ_star))) ≠ 0 := by
        refine sub_ne_zero.mpr fun heq => ?_
        have hn := congrArg norm heq.symm
        rw [norm_one, norm_mul] at hn
        have hlt : ‖w‖ * ‖cexp ((Real.log q : ℂ) * (I * conj (gammaOf ρ_star)))‖ < 1 :=
          mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hnorm_w hnorm_X.le
        linarith
      have hf2 : 1 - conj w * cexp ((Real.log q : ℂ) * (I * conj (gammaOf ρ_star))) ≠ 0 := by
        refine sub_ne_zero.mpr fun heq => ?_
        have hn := congrArg norm heq.symm
        rw [norm_one, norm_mul, Complex.norm_conj] at hn
        have hlt : ‖w‖ * ‖cexp ((Real.log q : ℂ) * (I * conj (gammaOf ρ_star)))‖ < 1 :=
          mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hnorm_w hnorm_X.le
        linarith
      exact mul_ne_zero (mul_ne_zero hf1 hf2) hs2

/-- **Existence of near-annihilating signed high-prime probes when `S₀` misses a right-zero pair.**
If `S₀ ⊆ {s : 1/2 < Re s}` and some `ρ_* ∈ rightZeros zetaZeroConfig` satisfies `ρ_* ∉ S₀` and
`conj ρ_* ∉ S₀`, then for every prime cutoff `P₀` and every `δ > 0` there exist `N > P₀` and a
signed prime-supported probe `a : Fin N → ℤ` supported above `P₀` with `integerProbe N a < 0` and
`modePairProduct ρ N a < δ · (-integerProbe N a)` for every `ρ ∈ S₀`. -/
theorem exists_signedPrimeProbe_nearAnnihilating_of_not_mem_pair {S₀ : Finset ℂ}
    (hS₀_re : ∀ ρ ∈ S₀, 1 / 2 < ρ.re)
    {ρ_star : ℂ} (hstar : ρ_star ∈ rightZeros zetaZeroConfig)
    (hnot1 : ρ_star ∉ S₀) (hnot2 : conj ρ_star ∉ S₀)
    (P₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (a : Fin N → ℤ),
      P₀ < N ∧
      isSignedPrimeSupported a ∧
      (∀ ℓ : Fin N, a ℓ ≠ 0 → P₀ < ℓ.val + 1) ∧
      integerProbe N a < 0 ∧
      ∀ ρ ∈ S₀, modePairProduct ρ N (fun i => (a i : ℂ)) < δ * (-integerProbe N a) := by
  classical
  -- Step 1: Build a zero-sum real probe packet annihilating `S₀` while seeing `ρ_star`.
  have hbase_pkt : realProbePacket (![1, -1] : Fin 2 → ℝ) = twoAtomDiffTest := by
    funext u
    unfold realProbePacket twoAtomDiffTest
    simp [Fin.sum_univ_two, scaleShift, sub_eq_add_neg]
  have hbase_sees : Sees (realProbePacket (![1, -1] : Fin 2 → ℝ)) ρ_star := by
    rw [hbase_pkt]
    have hmem : ρ_star ∈ seenRightZeros zetaZeroConfig twoAtomDiffTest := by
      rwa [seenRightZeros_twoAtomDiffTest]
    exact hmem.2.2
  have hind_S₀ : ∀ T : Finset ℂ, T ⊆ S₀ →
      ∃ (M₁ : ℕ) (v₁ : Fin M₁ → ℝ),
        2 ≤ M₁ ∧ (∑ i : Fin M₁, v₁ i) = 0 ∧
        (∀ ρ ∈ T, paperFT (cx (realProbePacket v₁)) (gammaOf (conj ρ)) = 0) ∧
        Sees (realProbePacket v₁) ρ_star := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      exact fun _ => ⟨2, ![1, -1], le_rfl, by simp [Fin.sum_univ_two], fun _ h => False.elim (Finset.notMem_empty _ h), hbase_sees⟩
    | insert ρ T hρT ih =>
      intro hsubT
      obtain ⟨M₁, v₁, hM₁, hv₁_sum, hv₁_van, hv₁_sees⟩ :=
        ih (Finset.Subset.trans (Finset.subset_insert ρ T) hsubT)
      have hρS₀ : ρ ∈ S₀ := hsubT (Finset.mem_insert_self ρ T)
      have hne1 : ρ_star ≠ ρ := fun h => hnot1 (h ▸ hρS₀)
      have hne2 : ρ_star ≠ conj ρ := fun h => hnot2 (by rw [h, conj_conj]; exact hρS₀)
      obtain ⟨M', v', hM', hv'_sum, hv'_pres, hv'_ρ, hv'_sees⟩ :=
        exists_realProbePacket_annihilating_step hM₁ v₁ hv₁_sum (hS₀_re ρ hρS₀) hstar.2
          hne1 hne2 hv₁_sees
      refine ⟨M', v', hM', hv'_sum, ?_, hv'_sees⟩
      intro τ hτ
      rcases Finset.mem_insert.mp hτ with rfl | hτT
      · exact hv'_ρ
      · exact hv'_pres _ (hv₁_van τ hτT)
  obtain ⟨M₁, v₁, hM₁2, hv₁_sum, hv₁_van, hv₁_sees⟩ := hind_S₀ S₀ Finset.Subset.rfl
  -- Step 2: Obtain an integer-window translate combination with strictly negative Weil square.
  have h1_le : ((1 : ℕ) : ℕ∞) ≤ (seenRightZeros zetaZeroConfig (realProbePacket v₁)).encard :=
    Set.one_le_encard_iff_nonempty.mpr ⟨ρ_star, hstar.1, hstar.2, hv₁_sees⟩
  rw [← negIndex_orbitKernel zetaZeroConfig temperedConfig_zetaZeroConfig
    (realProbePacket_mem_realTests v₁), negIndex_eq_iSup_intWindow] at h1_le
  obtain ⟨K, hK_pos⟩ :
      ∃ K : ℕ, 1 ≤ hermNegIndex (gram (orbitKernel zetaZeroConfig (realProbePacket v₁)) (intWindow K)) := by
    by_contra! hall
    have h0 : (⨆ K : ℕ,
        (hermNegIndex (gram (orbitKernel zetaZeroConfig (realProbePacket v₁)) (intWindow K)) : ℕ∞)) = 0 := by
      rw [ENat.iSup_eq_zero]
      intro K; exact_mod_cast Nat.lt_one_iff.mp (hall K)
    rw [h0] at h1_le; exact absurd h1_le (by norm_num)
  have hK1 : 1 ≤ K := by
    by_contra! hK0
    have : K = 0 := by omega
    subst this
    obtain ⟨W, hrank, _⟩ := exists_isPosDefOn_finrank_eq_posIndex
      (-(gram (orbitKernel zetaZeroConfig (realProbePacket v₁)) (intWindow 0)))
    have hle := Submodule.finrank_le W
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
    change 1 ≤ hermPosIndex _ at hK_pos
    rw [← hrank] at hK_pos; omega
  -- Express each `intWindow K k` translate of `realProbePacket v₁` in `Fin (K * M₁)`
  let M := K * M₁
  have hM2 : 2 ≤ M := by dsimp [M]; nlinarith
  let shiftV (k : Fin K) : Fin M → ℝ :=
    dilateVec (k.val + 1) (by omega) (by dsimp [M]; have := k.isLt; nlinarith) v₁
  have hgram_eq :
      gram (orbitKernel zetaZeroConfig (realProbePacket v₁)) (intWindow K) =
        Matrix.of fun k k' =>
          ((∑ i : Fin M, ∑ j : Fin M,
            (atomGram M i j).re * shiftV k i * shiftV k' j : ℝ) : ℂ) := by
    ext k k'
    rw [gram_orbitKernel]
    change zetaZeroConfig.W _ _ = _
    have hdk := dilateVec_properties (k.val + 1) (by omega)
      (by dsimp [M]; have := k.isLt; nlinarith) v₁
    have hdk' := dilateVec_properties (k'.val + 1) (by omega)
      (by dsimp [M]; have := k'.isLt; nlinarith) v₁
    have htr (r : Fin K) (hd : realProbePacket (shiftV r) =
        scaleShift (Real.log ((r.val + 1 : ℕ) : ℝ)) (realProbePacket v₁)) :
        ArithmeticCastelnuovoSeveri.translate (scale heckeLogScale (intWindow K r))
          (cx (realProbePacket v₁)) =
        ∑ i : Fin M, (shiftV r i : ℂ) •
          ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline) := by
      rw [scale_intWindow, ← cx_scaleShift_eq_translate]
      have hcast : ((r : ℝ) + 1) = ((r.val + 1 : ℕ) : ℝ) := by push_cast; rfl
      rw [hcast, ← hd]
      funext u
      simp [cx, realProbePacket, scaleShift, ArithmeticCastelnuovoSeveri.translate,
        Finset.sum_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    have hcB (i : Fin M) : ContDiff ℝ 2
        (ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline)) :=
      translate_contDiff (cx_contDiff contDiff_cubicSpline) _
    have hsB (i : Fin M) : HasCompactSupport
        (ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline)) :=
      translate_hasCompactSupport (cx_hasCompactSupport hasCompactSupport_cubicSpline) _
    have hW_atom (i j : Fin M) :
        zetaZeroConfig.W
          (ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline))
          (ArithmeticCastelnuovoSeveri.translate (Real.log ((j : ℝ) + 1)) (cx cubicSpline)) =
        ((atomGram M i j).re : ℂ) := by
      have hw := weilGram_eq_zeroGram (f := fun c : Fin M =>
        ArithmeticCastelnuovoSeveri.translate (Real.log ((c : ℝ) + 1)) (cx cubicSpline))
        hcB hsB
      exact (congr_fun (congr_fun hw i) j).symm.trans
        (Complex.ext rfl (by simpa using atomGram_im M i j))
    rw [htr k hdk.2, htr k' hdk'.2,
      W_sum_left_zeta Finset.univ _ _
        (fun i _ => (hcB i).const_smul _) (fun i _ => (hsB i).smul_left)
        (ContDiff.sum fun j _ => (hcB j).const_smul _)
        (HasCompactSupport.sum fun j _ => (hsB j).smul_left)]
    simp only [Matrix.of_apply, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [W_sum_right_zeta Finset.univ _ _
      ((hcB i).const_smul _) ((hsB i).smul_left)
      (fun j _ => (hcB j).const_smul _) (fun j _ => (hsB j).smul_left)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [W_smul_left, W_smul_right, hW_atom]
    simp only [Complex.conj_ofReal]
    ring
  -- Extract a single real vector `c_r : Fin K → ℝ` with negative quadratic square
  obtain ⟨W_sub, hrank_W, hW_pos⟩ := exists_isPosDefOn_finrank_eq_posIndex
    (-(gram (orbitKernel zetaZeroConfig (realProbePacket v₁)) (intWindow K)))
  change 1 ≤ hermPosIndex _ at hK_pos
  rw [← hrank_W] at hK_pos
  obtain ⟨y_c, hy_mem, hy_ne⟩ : ∃ y ∈ W_sub, y ≠ 0 := by
    by_contra! hall
    have hbot : W_sub = ⊥ := (Submodule.eq_bot_iff _).mpr hall
    rw [hbot, finrank_bot] at hK_pos; omega
  have hy_quad : hermQuad (gram (orbitKernel zetaZeroConfig (realProbePacket v₁)) (intWindow K)) y_c < 0 := by
    have hp := hW_pos y_c hy_mem hy_ne
    rw [hermQuad_neg] at hp; linarith
  rw [hgram_eq, hermQuad_ofReal_matrix] at hy_quad
  obtain ⟨w_k, hw_k_neg⟩ :
      ∃ w_k : Fin K → ℝ,
        realQuad (fun k k' => ∑ i : Fin M, ∑ j : Fin M, (atomGram M i j).re * shiftV k i * shiftV k' j)
          w_k < 0 := by
    by_contra! hall_nn
    linarith [hall_nn (fun k => (y_c k).re), hall_nn (fun k => (y_c k).im), hy_quad]
  let v : Fin M → ℝ := fun i => ∑ k : Fin K, w_k k * shiftV k i
  have hv_sum : (∑ i : Fin M, v i) = 0 := by
    dsimp [v]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum,
      (dilateVec_properties (k.val + 1) (by omega) (by dsimp [M]; have := k.isLt; nlinarith) v₁).1,
      hv₁_sum, mul_zero]
  have hv_quad : realQuad (fun i j => (atomGram M i j).re) v < 0 := by
    have heq : realQuad (fun i j => (atomGram M i j).re) v =
        realQuad (fun k k' => ∑ i : Fin M, ∑ j : Fin M, (atomGram M i j).re * shiftV k i * shiftV k' j)
          w_k := by
      unfold realQuad
      dsimp [v]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun j _ => by ring
    rwa [heq]
  have hv_mode_zero (ρ : ℂ) (hρ : ρ ∈ S₀) :
      modePairProduct ρ M (fun i => (v i : ℂ)) = 0 := by
    have hpkt_v : realProbePacket v =
        ∑ k : Fin K, w_k k • scaleShift (Real.log ((k.val + 1 : ℕ) : ℝ)) (realProbePacket v₁) := by
      funext u
      have h1 : realProbePacket v u = ∑ k : Fin K, w_k k * realProbePacket (shiftV k) u := by
        unfold realProbePacket
        dsimp [v]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
      rw [h1]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(dilateVec_properties (k.val + 1) (by omega) (by dsimp [M]; have := k.isLt; nlinarith) v₁).2]
    have hft_zero : paperFT (cx (realProbePacket v)) (gammaOf (conj ρ)) = 0 := by
      have hind_K : ∀ s : Finset (Fin K),
          paperFT (cx (∑ k ∈ s, w_k k •
            scaleShift (Real.log ((k.val + 1 : ℕ) : ℝ)) (realProbePacket v₁)))
            (gammaOf (conj ρ)) = 0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [cx, paperFT]
        | insert k s hk ih =>
          have hmem_k : (w_k k • scaleShift (Real.log ((k.val + 1 : ℕ) : ℝ)) (realProbePacket v₁)) ∈
              realTests :=
            Submodule.smul_mem _ _ (scaleShift_mem _ (realProbePacket_mem_realTests v₁))
          have hmem_s : (∑ k' ∈ s, w_k k' •
              scaleShift (Real.log ((k'.val + 1 : ℕ) : ℝ)) (realProbePacket v₁)) ∈ realTests :=
            Submodule.sum_mem _ fun k' _ =>
              Submodule.smul_mem _ _ (scaleShift_mem _ (realProbePacket_mem_realTests v₁))
          rw [Finset.sum_insert hk, cx_add,
            paperFT_add (cx_contDiff hmem_k.1).continuous (cx_hasCompactSupport hmem_k.2)
              (cx_contDiff hmem_s.1).continuous (cx_hasCompactSupport hmem_s.2),
            ih, add_zero, cx_smul, paperFT_smul, paperFT_cx_scaleShift_apply, hv₁_van ρ hρ,
            mul_zero, smul_zero]
      rw [hpkt_v]; exact hind_K Finset.univ
    rw [paperFT_realProbePacket_gammaOf_conj] at hft_zero
    have hB_ne : paperFT (cx cubicSpline) (gammaOf (conj ρ)) ≠ 0 :=
      BiScaleUncertainty.ChebyshevGauge.paperFT_cubicSpline_ne_zero
        (SquareRootThreshold.im_gammaOf_ne_zero (by rw [Complex.conj_re]; linarith [hS₀_re ρ hρ]))
    have hev_zero : charEval (modeChar ρ) (fun i : Fin M => natSlope i.val) (fun i => (v i : ℂ)) = 0 :=
      (mul_eq_zero.mp hft_zero).resolve_right hB_ne
    unfold modePairProduct
    rw [hev_zero, norm_zero, zero_mul]
  -- Step 3: Zero-sum rational approximation of `v` and denominator clearing.
  let i_zero : Fin M := ⟨0, by omega⟩
  let projZero : (Fin M → ℝ) → (Fin M → ℝ) := fun x i =>
    if i = i_zero then -∑ j ∈ Finset.univ.erase i_zero, x j else x i
  have hproj_cont : Continuous projZero := by
    refine continuous_pi fun i => ?_
    dsimp [projZero]
    split_ifs
    · exact (continuous_finset_sum _ fun j _ => continuous_apply j).neg
    · exact continuous_apply i
  have hproj_v : projZero v = v := by
    funext i
    dsimp [projZero]
    split_ifs with hi
    · subst hi
      have hsp := Finset.add_sum_erase Finset.univ v (Finset.mem_univ i_zero)
      linarith only [hsp, hv_sum]
    · rfl
  let Q_real : (Fin M → ℝ) → ℝ := realQuad (fun i j => (atomGram M i j).re)
  let MP_real (ρ : ℂ) : (Fin M → ℝ) → ℝ := fun x =>
    modePairProduct ρ M (fun i => (x i : ℂ))
  have hMP_cont (ρ : ℂ) : Continuous (MP_real ρ) := by
    dsimp [MP_real, modePairProduct, charEval]
    fun_prop
  have hev_w : ∀ᶠ x : Fin M → ℝ in 𝓝 v,
      Q_real (projZero x) < 0 ∧
      ∀ ρ ∈ S₀, MP_real ρ (projZero x) < (δ / 2) * (-Q_real (projZero x)) := by
    have hQv : Q_real (projZero v) < 0 := by rwa [hproj_v]
    refine (((continuous_realQuad _).comp hproj_cont).continuousAt.eventually
      (gt_mem_nhds hQv)).and ?_
    rw [eventually_all_finset]
    intro ρ hρ
    have h0v : MP_real ρ (projZero v) < (δ / 2) * (-Q_real (projZero v)) := by
      rw [hproj_v]
      dsimp [MP_real]
      rw [hv_mode_zero ρ hρ]
      exact mul_pos (half_pos hδ) (neg_pos.mpr hv_quad)
    have hdiff_cont : Continuous
        (fun x : Fin M → ℝ => (δ / 2) * (-Q_real (projZero x)) - MP_real ρ (projZero x)) :=
      (continuous_const.mul (((continuous_realQuad _).comp hproj_cont).neg)).sub
        ((hMP_cont ρ).comp hproj_cont)
    exact (hdiff_cont.continuousAt.eventually (lt_mem_nhds (sub_pos.mpr h0v))).mono fun x hx => by
      linarith only [hx]
  have hdense_Q : DenseRange (fun q₀ : Fin M → ℚ => fun i => ((q₀ i : ℚ) : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨r_rad, hr_pos, hball_v⟩ := Metric.eventually_nhds_iff.mp hev_w
  obtain ⟨q₀, hq₀_dist⟩ := Metric.denseRange_iff.mp hdense_Q v r_rad hr_pos
  rw [dist_comm] at hq₀_dist
  obtain ⟨hQ_neg_q, hMP_lt_q⟩ := hball_v hq₀_dist
  let q : Fin M → ℚ := fun i =>
    if i = i_zero then -∑ j ∈ Finset.univ.erase i_zero, q₀ j else q₀ i
  have hq_cast : (fun i : Fin M => ((q i : ℚ) : ℝ)) = projZero (fun i => ((q₀ i : ℚ) : ℝ)) := by
    funext i
    dsimp [q, projZero]
    split_ifs <;> push_cast <;> rfl
  have hq_sum : (∑ i : Fin M, q i) = 0 := by
    rw [← Finset.add_sum_erase Finset.univ q (Finset.mem_univ i_zero)]
    have hi0 : q i_zero = -∑ j ∈ Finset.univ.erase i_zero, q₀ j := if_pos rfl
    have hrest : ∑ j ∈ Finset.univ.erase i_zero, q j = ∑ j ∈ Finset.univ.erase i_zero, q₀ j :=
      Finset.sum_congr rfl fun j hj => if_neg (Finset.mem_erase.mp hj).1
    rw [hi0, hrest, neg_add_cancel]
  obtain ⟨D, u, hD_pos, hu_eq⟩ := exists_common_denominator q
  have hD_r : (0 : ℝ) < D := Nat.cast_pos.mpr hD_pos
  have hu_sum : (∑ i : Fin M, u i) = 0 := by
    have hreal : (∑ i : Fin M, (u i : ℝ)) = 0 := by
      simp_rw [← hu_eq, ← Finset.sum_mul]
      have hqr : (∑ i : Fin M, ((q i : ℚ) : ℝ)) = 0 := by exact_mod_cast hq_sum
      rw [hqr, zero_mul]
    exact_mod_cast hreal
  have hu_probe : integerProbe M u = (D : ℝ) ^ 2 * Q_real (projZero (fun i => ((q₀ i : ℚ) : ℝ))) := by
    rw [integerProbe_eq_sum, ← hq_cast]
    dsimp [Q_real, realQuad]
    simp_rw [← hu_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu_neg : integerProbe M u < 0 := by
    rw [hu_probe]
    exact mul_neg_of_pos_of_neg (pow_pos hD_r 2) hQ_neg_q
  have hu_ne : u ≠ 0 := by
    rintro rfl
    rw [integerProbe_eq_sum] at hu_neg
    simp at hu_neg
  have hu_mp_lt (ρ : ℂ) (hρ : ρ ∈ S₀) :
      modePairProduct ρ M (fun i => (u i : ℂ)) < (δ / 2) * (-integerProbe M u) := by
    have hmp_scale :
        modePairProduct ρ M (fun i => (u i : ℂ)) =
          (D : ℝ) ^ 2 * MP_real ρ (projZero (fun i => ((q₀ i : ℚ) : ℝ))) := by
      rw [← hq_cast]
      dsimp [MP_real, modePairProduct]
      have hc1 : charEval (modeChar ρ) (fun i : Fin M => natSlope i.val) (fun i => (u i : ℂ)) =
          (D : ℂ) * charEval (modeChar ρ) (fun i : Fin M => natSlope i.val)
            (fun i => (((q i : ℚ) : ℝ) : ℂ)) := by
        simp only [charEval_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi : (u i : ℂ) = (((q i : ℚ) : ℝ) : ℂ) * (D : ℂ) := by exact_mod_cast (hu_eq i).symm
        rw [hi]; ring
      have hc2 : charEval (reflectChar (modeChar ρ)) (fun i : Fin M => natSlope i.val)
          (fun i => (u i : ℂ)) =
          (D : ℂ) * charEval (reflectChar (modeChar ρ)) (fun i : Fin M => natSlope i.val)
            (fun i => (((q i : ℚ) : ℝ) : ℂ)) := by
        simp only [charEval_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi : (u i : ℂ) = (((q i : ℚ) : ℝ) : ℂ) * (D : ℂ) := by exact_mod_cast (hu_eq i).symm
        rw [hi]; ring
      rw [hc1, hc2, norm_mul, norm_mul, Complex.norm_natCast]
      ring
    rw [hmp_scale, hu_probe]
    have hlt := hMP_lt_q ρ hρ
    nlinarith [pow_pos hD_r 2]
  -- Step 4: Transport `u` to a co-scaled prime cluster above `P₀`, preserving `modePairProduct`.
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin M, u i ≠ 0 := by simpa [funext_iff] using hu_ne
  obtain ⟨U, _, hU⟩ := exists_shifted_primeBlocks_log_approx 1 M P₀ ![0]
    (fun r => by fin_cases r; exact le_rfl)
  have hseq (n : ℕ) := hU (max U (n : ℝ)) (le_max_left _ _)
  choose Nseq ιseq hι_inj hι_props using hseq
  have hι0_inj (n : ℕ) : Function.Injective (ιseq n 0) :=
    fun i j hij => Prod.mk.inj_iff.mp (hι_inj n (p₁ := (0, i)) (p₂ := (0, j)) hij) |>.2
  let aseq (n : ℕ) : Fin (Nseq n) → ℤ := Function.extend (ιseq n 0) u 0
  have hzero : Tendsto (fun n : ℕ => (6 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hexp_bound (n : ℕ) (hn1 : 1 ≤ n) :
      2 * Real.exp (-(1 / 3 : ℝ) * (n : ℝ)) ≤ (6 : ℝ) / (n : ℝ) := by
    have hlin : (1 / 3 : ℝ) * (n : ℝ) ≤ Real.exp ((1 / 3 : ℝ) * (n : ℝ)) := by
      linarith [Real.add_one_le_exp ((1 / 3 : ℝ) * (n : ℝ))]
    rw [neg_mul, Real.exp_neg]
    have hinv := inv_anti₀ (by positivity : 0 < (1 / 3 : ℝ) * (n : ℝ)) hlin
    rw [show ((1 / 3 : ℝ) * (n : ℝ))⁻¹ = (3 : ℝ) / (n : ℝ) by field_simp] at hinv
    calc 2 * (Real.exp ((1 / 3 : ℝ) * (n : ℝ)))⁻¹ ≤ 2 * ((3 : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 6 / (n : ℝ) := by ring
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt U
  have herr_zero (i : Fin M) :
      Tendsto (fun n : ℕ =>
        Real.log (((ιseq n 0 i).val : ℝ) + 1) - (max U (n : ℝ) + Real.log ((i : ℝ) + 1)))
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using hzero.neg) tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop (max N₀ 1)] with n hn
      have hmax : max U (n : ℝ) = (n : ℝ) :=
        max_eq_right (hN₀.le.trans (by exact_mod_cast (le_max_left N₀ 1).trans hn))
      have hb := hexp_bound n ((le_max_right N₀ 1).trans hn)
      have hi := (hι_props n 0 i).2.2.2
      simp only [Matrix.cons_val_zero, add_zero] at hi
      rw [hmax] at hi ⊢
      linarith only [hi, hb]
    · filter_upwards [eventually_ge_atTop 0] with n _
      have hi := (hι_props n 0 i).2.2.1
      simp only [Matrix.cons_val_zero, add_zero] at hi
      linarith only [hi]
  have hconv_Q : Tendsto (fun n : ℕ => integerProbe (Nseq n) (aseq n))
      atTop (𝓝 (integerProbe M u)) := by
    rw [← probePairing_self M u]
    unfold probePairing
    refine (tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_finsetSum Finset.univ fun j _ => ?_).congr fun n => by
        rw [← probePairing_self, extend_probePairing_eq (hι0_inj n) (hι0_inj n) u u]
    have harg : Tendsto
        (fun n : ℕ =>
          Real.log (((ιseq n 0 i).val : ℝ) + 1) - Real.log (((ιseq n 0 j).val : ℝ) + 1))
        atTop (𝓝 (Real.log ((i : ℝ) + 1) - Real.log ((j : ℝ) + 1))) := by
      have hd := (herr_zero i).sub (herr_zero j)
      simp only [sub_zero] at hd
      refine (tendsto_const_nhds.add hd).congr' ?_
      filter_upwards with n; ring
    rw [atomGram_eq_splineSeries M i j]
    have hsp := ((Complex.continuous_re.comp continuous_splineSeries).tendsto _).comp harg
    refine ((hsp.mul_const (u i : ℝ)).mul_const (u j : ℝ)).congr fun n => ?_
    dsimp only [Function.comp_apply]
    rw [atomGram_eq_splineSeries (Nseq n) (ιseq n 0 i) (ιseq n 0 j)]
  have hconv_MP (ρ : ℂ) :
      Tendsto (fun n : ℕ => modePairProduct ρ (Nseq n) (fun ℓ => (aseq n ℓ : ℂ)))
        atTop (𝓝 (modePairProduct ρ M (fun i => (u i : ℂ)))) := by
    let s_exp : ℂ := conj ρ - 1 / 2
    have hsum_ext_cx (n : ℕ) (w : Fin (Nseq n) → ℂ) :
        (∑ ℓ : Fin (Nseq n), ((aseq n ℓ : ℤ) : ℂ) * w ℓ) =
          ∑ i : Fin M, (u i : ℂ) * w (ιseq n 0 i) := by
      have hoff : ∀ ℓ : Fin (Nseq n), ℓ ∉ Finset.univ.image (ιseq n 0) →
          ((aseq n ℓ : ℤ) : ℂ) * w ℓ = 0 := by
        intro ℓ hℓ
        have hz : aseq n ℓ = 0 :=
          Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hℓ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
        rw [hz, Int.cast_zero, zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (ιseq n 0)))
        fun ℓ _ hℓ => hoff ℓ hℓ,
        Finset.sum_image fun i _ j _ h => hι0_inj n h]
      exact Finset.sum_congr rfl fun i _ => by simp only [aseq, (hι0_inj n).extend_apply]
    have hprod_eq (n : ℕ) :
        modePairProduct ρ (Nseq n) (fun ℓ => (aseq n ℓ : ℂ)) =
          ‖∑ i : Fin M, (u i : ℂ) *
              cexp (s_exp * ((Real.log ((i : ℝ) + 1) +
                (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                  (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ))‖ *
            ‖∑ i : Fin M, (u i : ℂ) *
              cexp ((-conj s_exp) * ((Real.log ((i : ℝ) + 1) +
                (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                  (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ))‖ := by
      unfold modePairProduct
      rw [charEval_apply, charEval_apply, hsum_ext_cx, hsum_ext_cx]
      let Tn : ℝ := max U (n : ℝ)
      have hc1 :
          (∑ i : Fin M, (u i : ℂ) * modeChar ρ (natSlope (ιseq n 0 i).val)) =
            cexp (s_exp * (Tn : ℂ)) *
              ∑ i : Fin M, (u i : ℂ) *
                cexp (s_exp * ((Real.log ((i : ℝ) + 1) +
                  (Real.log (((ιseq n 0 i).val : ℝ) + 1) - (Tn + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [modeChar, zeroChar, logChar_apply, scale_natSlope]
        have harg_eq :
            s_exp * (Real.log ((((ιseq n 0 i).val + 1 : ℕ) : ℝ)) : ℂ) =
              s_exp * (Tn : ℂ) +
                s_exp * ((Real.log ((i : ℝ) + 1) +
                  (Real.log (((ιseq n 0 i).val : ℝ) + 1) - (Tn + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ) := by
          push_cast; ring
        change (u i : ℂ) * cexp (s_exp * (Real.log ((((ιseq n 0 i).val + 1 : ℕ) : ℝ)) : ℂ)) = _
        rw [harg_eq, Complex.exp_add]
        ring
      have hc2 :
          (∑ i : Fin M, (u i : ℂ) * reflectChar (modeChar ρ) (natSlope (ιseq n 0 i).val)) =
            cexp ((-conj s_exp) * (Tn : ℂ)) *
              ∑ i : Fin M, (u i : ℂ) *
                cexp ((-conj s_exp) * ((Real.log ((i : ℝ) + 1) +
                  (Real.log (((ιseq n 0 i).val : ℝ) + 1) - (Tn + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [modeChar, zeroChar, reflectChar_logChar, logChar_apply, scale_natSlope]
        have harg_eq :
            (-conj s_exp) * (Real.log ((((ιseq n 0 i).val + 1 : ℕ) : ℝ)) : ℂ) =
              (-conj s_exp) * (Tn : ℂ) +
                (-conj s_exp) * ((Real.log ((i : ℝ) + 1) +
                  (Real.log (((ιseq n 0 i).val : ℝ) + 1) - (Tn + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ) := by
          push_cast; ring
        change (u i : ℂ) * cexp ((-conj s_exp) * (Real.log ((((ιseq n 0 i).val + 1 : ℕ) : ℝ)) : ℂ)) = _
        rw [harg_eq, Complex.exp_add]
        ring
      rw [hc1, hc2, norm_mul, norm_mul]
      have hnorm_cancel :
          ‖cexp (s_exp * (Tn : ℂ))‖ * ‖cexp ((-conj s_exp) * (Tn : ℂ))‖ = 1 := by
        rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
        have hre0 : (s_exp * (Tn : ℂ)).re + ((-conj s_exp) * (Tn : ℂ)).re = 0 := by
          simp
        rw [hre0, Real.exp_zero]
      calc (‖cexp (s_exp * (Tn : ℂ))‖ * _) * (‖cexp ((-conj s_exp) * (Tn : ℂ))‖ * _)
          = (‖cexp (s_exp * (Tn : ℂ))‖ * ‖cexp ((-conj s_exp) * (Tn : ℂ))‖) * (_ * _) := by ring
        _ = _ := by rw [hnorm_cancel, one_mul]
    have hlim1 :
        Tendsto (fun n : ℕ =>
          ‖∑ i : Fin M, (u i : ℂ) *
              cexp (s_exp * ((Real.log ((i : ℝ) + 1) +
                (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                  (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ))‖)
          atTop (𝓝 ‖charEval (modeChar ρ) (fun i : Fin M => natSlope i.val) (fun i => (u i : ℂ))‖) := by
      have hexp_lim :
          Tendsto (fun n : ℕ =>
            ∑ i : Fin M, (u i : ℂ) *
              cexp (s_exp * ((Real.log ((i : ℝ) + 1) +
                (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                  (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ)))
            atTop (𝓝 (charEval (modeChar ρ) (fun i : Fin M => natSlope i.val) (fun i => (u i : ℂ)))) := by
        rw [charEval_apply]
        refine tendsto_finsetSum Finset.univ fun i _ => ?_
        have h1 : Tendsto (fun n : ℕ =>
            s_exp * ((Real.log ((i : ℝ) + 1) +
              (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ))
            atTop (𝓝 (s_exp * (Real.log ((i.val + 1 : ℕ) : ℝ) : ℂ))) := by
          have hc : ((i : ℝ) + 1) = ((i.val + 1 : ℕ) : ℝ) := by push_cast; rfl
          rw [← hc]
          have hr := tendsto_const_nhds.add (herr_zero i)
          rw [add_zero] at hr
          exact ((Complex.continuous_ofReal.tendsto _).comp hr).const_mul s_exp
        have h2 := (Complex.continuous_exp.tendsto _).comp h1
        have hgoal : modeChar ρ (natSlope i.val) =
            cexp (s_exp * (Real.log ((i.val + 1 : ℕ) : ℝ) : ℂ)) := by
          rw [modeChar, zeroChar, logChar_apply, scale_natSlope]
        rw [hgoal]
        exact h2.const_mul (u i : ℂ)
      exact (continuous_norm.tendsto _).comp hexp_lim
    have hlim2 :
        Tendsto (fun n : ℕ =>
          ‖∑ i : Fin M, (u i : ℂ) *
              cexp ((-conj s_exp) * ((Real.log ((i : ℝ) + 1) +
                (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                  (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ))‖)
          atTop (𝓝 ‖charEval (reflectChar (modeChar ρ)) (fun i : Fin M => natSlope i.val)
            (fun i => (u i : ℂ))‖) := by
      have hexp_lim :
          Tendsto (fun n : ℕ =>
            ∑ i : Fin M, (u i : ℂ) *
              cexp ((-conj s_exp) * ((Real.log ((i : ℝ) + 1) +
                (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                  (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ)))
            atTop (𝓝 (charEval (reflectChar (modeChar ρ)) (fun i : Fin M => natSlope i.val)
              (fun i => (u i : ℂ)))) := by
        rw [charEval_apply]
        refine tendsto_finsetSum Finset.univ fun i _ => ?_
        have h1 : Tendsto (fun n : ℕ =>
            (-conj s_exp) * ((Real.log ((i : ℝ) + 1) +
              (Real.log (((ιseq n 0 i).val : ℝ) + 1) -
                (max U (n : ℝ) + Real.log ((i : ℝ) + 1))) : ℝ) : ℂ))
            atTop (𝓝 ((-conj s_exp) * (Real.log ((i.val + 1 : ℕ) : ℝ) : ℂ))) := by
          have hc : ((i : ℝ) + 1) = ((i.val + 1 : ℕ) : ℝ) := by push_cast; rfl
          rw [← hc]
          have hr := tendsto_const_nhds.add (herr_zero i)
          rw [add_zero] at hr
          exact ((Complex.continuous_ofReal.tendsto _).comp hr).const_mul (-conj s_exp)
        have h2 := (Complex.continuous_exp.tendsto _).comp h1
        have hgoal : reflectChar (modeChar ρ) (natSlope i.val) =
            cexp ((-conj s_exp) * (Real.log ((i.val + 1 : ℕ) : ℝ) : ℂ)) := by
          rw [modeChar, zeroChar, reflectChar_logChar, logChar_apply, scale_natSlope]
        rw [hgoal]
        exact h2.const_mul (u i : ℂ)
      exact (continuous_norm.tendsto _).comp hexp_lim
    exact (hlim1.mul hlim2).congr fun n => (hprod_eq n).symm
  have hev_final : ∀ᶠ n : ℕ in atTop,
      integerProbe (Nseq n) (aseq n) < 0 ∧
      ∀ ρ ∈ S₀, modePairProduct ρ (Nseq n) (fun ℓ => (aseq n ℓ : ℂ)) <
        δ * (-integerProbe (Nseq n) (aseq n)) := by
    refine (hconv_Q.eventually (gt_mem_nhds hu_neg)).and ?_
    rw [eventually_all_finset]
    intro ρ hρ
    have hlim_sub :
        Tendsto (fun n : ℕ =>
          δ * (-integerProbe (Nseq n) (aseq n)) -
            modePairProduct ρ (Nseq n) (fun ℓ => (aseq n ℓ : ℂ)))
          atTop (𝓝 (δ * (-integerProbe M u) - modePairProduct ρ M (fun i => (u i : ℂ)))) :=
      (hconv_Q.neg.const_mul δ).sub (hconv_MP ρ)
    have hpos_lim : 0 < δ * (-integerProbe M u) - modePairProduct ρ M (fun i => (u i : ℂ)) := by
      have h1 := hu_mp_lt ρ hρ
      have h2 : (δ / 2) * (-integerProbe M u) < δ * (-integerProbe M u) :=
        mul_lt_mul_of_pos_right (half_lt_self hδ) (neg_pos.mpr hu_neg)
      linarith only [h1, h2]
    exact (hlim_sub.eventually (lt_mem_nhds hpos_lim)).mono fun n hn => by linarith only [hn]
  obtain ⟨n, hn_neg, hn_mp⟩ := hev_final.exists
  have hN_gt : P₀ < Nseq n := by
    have h1 := (hι_props n 0 i₀).2.1
    have h2 := (ιseq n 0 i₀).isLt
    omega
  exact ⟨Nseq n, aseq n, hN_gt,
    (isSignedPrimeSupported_extend (hι0_inj n)
      (fun i => ⟨(hι_props n 0 i).1, (hι_props n 0 i).2.1⟩) hu_ne hu_sum).1,
    (isSignedPrimeSupported_extend (hι0_inj n)
      (fun i => ⟨(hι_props n 0 i).1, (hι_props n 0 i).2.1⟩) hu_ne hu_sum).2,
    hn_neg, hn_mp⟩

/-- **Exact finite-mode quotient and near-annihilator dichotomy.**
For any conjugation-closed finite set `S₀ ⊆ {s : 1/2 < Re s}`, `rightZeros zetaZeroConfig ⊆ S₀`
holds if and only if there is no sequence of signed prime-supported negative probes above a cutoff
`P₀` with arbitrarily small normalized `S₀`-mode pair products. -/
theorem rightZeros_subset_iff_no_nearAnnihilating_neg_primeProbe {S₀ : Finset ℂ}
    (hS₀_re : ∀ ρ ∈ S₀, 1 / 2 < ρ.re)
    (hS₀_conj : ∀ ρ ∈ S₀, conj ρ ∈ S₀) (P₀ : ℕ) :
    rightZeros zetaZeroConfig ⊆ (S₀ : Set ℂ) ↔
      ∃ η : ℝ, 0 < η ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
        P₀ < N → isSignedPrimeSupported a →
        (∀ ℓ : Fin N, a ℓ ≠ 0 → P₀ < ℓ.val + 1) →
        integerProbe N a < 0 →
        ∃ ρ ∈ S₀, η * (-integerProbe N a) ≤ modePairProduct ρ N (fun i => (a i : ℂ)) := by
  constructor
  · intro hsub
    obtain ⟨η, hη, hall⟩ := exists_uniform_modePair_lower_of_rightZeros_subset hsub
    exact ⟨η, hη, fun N a _ _ _ hneg => hall N a hneg⟩
  · rintro ⟨η, hη, hall⟩ ρ_star hstar
    by_contra hnot1
    have hnot1' : ρ_star ∉ S₀ := hnot1
    have hnot2' : conj ρ_star ∉ S₀ := fun hc => hnot1' (by simpa using hS₀_conj _ hc)
    obtain ⟨N, a, hN, hsig, hgt, hneg, hmp_lt⟩ :=
      exists_signedPrimeProbe_nearAnnihilating_of_not_mem_pair hS₀_re hstar hnot1' hnot2' P₀ hη
    obtain ⟨ρ, hρ, hge⟩ := hall N a hN hsig hgt hneg
    exact (not_lt_of_ge hge) (hmp_lt ρ hρ)

end GaloisForLFunctions.CountingHolography.Sections

