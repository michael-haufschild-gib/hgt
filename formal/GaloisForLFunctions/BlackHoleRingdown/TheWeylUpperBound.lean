import GaloisForLFunctions.BlackHoleRingdown.TheWeylLowerBound
import GaloisForLFunctions.BlackHoleRingdown.TheMultiplicityOfTheHeckeModes
import GaloisForLFunctions.BlackHoleRingdown.TheVolumeOfTheModularHorizon
import GaloisForLFunctions.RHTower.SarnakXueCuspTail
import GaloisForLFunctions.RHTower.SelbergMaassParseval
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTail
import GaloisForLFunctions.RHTower.DeckPointPairSymmetry

/-!
# The Weyl upper bound for the cusp spectrum

The number of cusp forms of the modular horizon with eigenvalue at most `Λ` is at most `C(Λ + 1)`
(`cuspCount_le`). With the lower bound, `N(Λ) ≍ Λ` (`weyl_law_order`): the undamped tones of the
modular black hole have the density of a compact surface. In particular the heat trace
`Σ_j e^{-tλ_j}` is finite for every `t > 0` (`summable_exp_neg_mul`).

**Pointwise Bessel inequality.** A nonnegative profile `φ ≤ M` of radius `R` and mass `1` acts on each
basis eigenfunction `U_i` by a number `κ_i` (Selberg), and `(L_φ U)(z) = ⟨K_z, U⟩` with the automorphic
kernel `K_z(z') = ½ Σ_B φ(u(z, Bz'))` on `𝒟`. Bessel's inequality for the orthonormal family gives
`Σ_i |κ_i|² |U_i(z)|² ≤ ‖K_z‖²`, and Cauchy–Schwarz over the near translates with the tiling of `ℍ`
gives `‖K_z‖² ≤ m M / 2`, where `m` bounds the number of `B` with `u(z, Bz') ≤ R` (`sum_sq_le`).

**Counting.** For `z, z' ∈ 𝒟` the translations `z' ↦ z' ± b` with `u ≤ R` have `b` in an interval of
length `8√R Im z`, and a matrix with `c ≠ 0` forces `Im z ≤ 6`, where all its entries are at most `1304`
(`card_near_le`).

**The cusp.** Each Fourier mode of a cusp form solves `a'' = (4π²n² − λ/y²) a` and tends to zero, so
`|a|²` is convex and nonincreasing beyond `Y₁ = max(1, √λ/2π)`, and `Y ∫_Y^∞ |a|²/y² ≤ Y₁ ∫_{Y₁}^∞ |a|²/y²`.
By Parseval on the horocycles the cusp above `Y = 5Y₁` carries at most a fifth of the mass (`tail_le`).

**Assembly.** With `R = 1/(512(Λ+1))` the normalized narrow profile has `M ≤ 8/(πR)`, the transforms
satisfy `|κ_i| ≥ ½` for `λ_i ≤ Λ`, and `√R · Y ≤ 1`, so `m` is bounded on `𝒟 ∩ {y ≤ Y}`. Integrating the
Bessel inequality there, each of the `N(Λ)` eigenfunctions contributes at least `4/5`, against a total
of `O(M) = O(Λ + 1)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups InnerProductSpace ENNReal UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry (pairU pairU_nonneg pairU_le_bounds im_smul_int entryBound_eq
  modularEntryBound entries_sq_le_of_pairU_le re_smul_int_of_c_eq_zero det_real)
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos)
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace (Deck)
open GaloisForLFunctions.RHTower.SelbergMaassMean (point)

namespace WeylUpper

open HeckeCusp

/-! ### Counting near translates -/

theorem half_le_im_of_mem_fd {z : ℍ} (hz : z ∈ ModularGroup.fd) : 1 / 2 ≤ z.im := by
  have h := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith [z.im_pos]

/-- A matrix with nonzero lower-left entry moves `𝒟` within `u ≤ R ≤ 1/4` of `z` only if `Im z ≤ 6`. -/
theorem im_le_six {z z' : ℍ} (hz' : z' ∈ ModularGroup.fd) {R : ℝ} (hR : R ≤ 1 / 4)
    {B : SL(2, ℤ)} (hc : B 1 0 ≠ 0) (h : pairU z (B • z') ≤ R) : z.im ≤ 6 := by
  have hR0 : 0 ≤ R := (pairU_nonneg _ _).trans h
  obtain ⟨h1, -, -⟩ := pairU_le_bounds h
  have hy' := half_le_im_of_mem_fd hz'
  have hc1 : (1 : ℝ) ≤ ((B 1 0 : ℤ) : ℝ) ^ 2 := by
    have h' : (1 : ℝ) ≤ |((B 1 0 : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hc
    nlinarith [abs_nonneg ((B 1 0 : ℤ) : ℝ), sq_abs ((B 1 0 : ℤ) : ℝ)]
  have hIm := im_smul_int B z'
  have hDge : z'.im ^ 2 ≤ ((B 1 0 : ℝ) * z'.re + B 1 1) ^ 2 + ((B 1 0 : ℝ) * z'.im) ^ 2 := by
    nlinarith [sq_nonneg ((B 1 0 : ℝ) * z'.re + B 1 1), sq_nonneg z'.im]
  have hw : (B • z').im ≤ 2 := by
    rw [hIm, div_le_iff₀ (lt_of_lt_of_le (by positivity) hDge)]
    nlinarith
  have hK : 0 < 4 * R + 2 := by linarith
  rw [div_le_iff₀ hK] at h1
  nlinarith

/-- **Entries of the non-translations.** If `c ≠ 0` and `B𝒟` comes within `u ≤ R ≤ 1/4` of `z ∈ 𝒟`,
every entry of `B` has absolute value at most `1304`. -/
theorem abs_entry_le {z z' : ℍ} (hz : z ∈ ModularGroup.fd) (hz' : z' ∈ ModularGroup.fd) {R : ℝ}
    (hR : R ≤ 1 / 4) {B : SL(2, ℤ)} (hc : B 1 0 ≠ 0) (h : pairU z (B • z') ≤ R) (i j : Fin 2) :
    |B i j| ≤ 1304 := by
  have hR0 : 0 ≤ R := (pairU_nonneg _ _).trans h
  have hy6 := im_le_six hz' hR hc h
  have hy := half_le_im_of_mem_fd hz
  have hx : z.re ^ 2 ≤ 1 / 4 := by have := abs_le.1 hz.2; nlinarith
  have hE : modularEntryBound z R ≤ 1700000 := by
    rw [entryBound_eq]
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = (4 * R + 2) / z.im := ⟨_, rfl⟩
    obtain ⟨X, hX⟩ : ∃ X, X = 2 * z.re ^ 2 + 8 * R * (4 * R + 2) * z.im ^ 2 := ⟨_, rfl⟩
    rw [← hQ, ← hX]
    have hQ0 : 0 ≤ Q := by rw [hQ]; have := z.im_pos; positivity
    have hQ6 : Q ≤ 6 := by rw [hQ, div_le_iff₀ z.im_pos]; linarith
    have hRK : R * (4 * R + 2) ≤ 3 / 4 := by nlinarith
    have hy2 : z.im ^ 2 ≤ 36 := by nlinarith [z.im_pos]
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    have hX1 : X ≤ 217 := by
      rw [hX]
      have := mul_le_mul hRK hy2 (sq_nonneg _) (by norm_num)
      nlinarith
    have hA : 4 * (4 * R + 2) * z.im + 8 * Q * X ≤ 10488 := by
      have h1 : (4 * R + 2) * z.im ≤ 18 := by nlinarith
      have h2 : Q * X ≤ 6 * 217 := mul_le_mul hQ6 hX1 hX0 (by norm_num)
      nlinarith
    have hA0 : 0 ≤ 4 * (4 * R + 2) * z.im + 8 * Q * X := by have := z.im_pos; positivity
    have hD : 2 * Q ^ 2 + Q + 1 ≤ 79 := by nlinarith
    have hAD := mul_le_mul hA hD (by positivity) (by norm_num)
    nlinarith
  have hb := (entries_sq_le_of_pairU_le hz' h i j).trans hE
  have hlt : ((B i j : ℤ) : ℝ) ^ 2 < 1305 ^ 2 := by linarith
  have habs : |((B i j : ℤ) : ℝ)| < 1305 := abs_lt_of_sq_lt_sq hlt (by norm_num)
  rw [← Int.cast_abs] at habs
  have : |B i j| < 1305 := by exact_mod_cast habs
  omega

/-- For a translation `c = 0` the matrix is `±(1, b; 0, 1)` and moves `z'` to `z' + ab`. -/
theorem translation_data (B : SL(2, ℤ)) (hc : B 1 0 = 0) (z' : ℍ) :
    (B 0 0 = 1 ∨ B 0 0 = -1) ∧ B 1 1 = B 0 0 ∧
      (B • z').re = z'.re + ((B 0 0 * B 0 1 : ℤ) : ℝ) := by
  have hre := re_smul_int_of_c_eq_zero B hc z'
  have hdet := det_real B
  have had : (B 0 0) * (B 1 1) = 1 := by
    have : ((B 0 0 * B 1 1 : ℤ) : ℝ) = 1 := by push_cast; rw [hc] at hdet; simpa using hdet
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨Or.inl h1, by rw [h1, h2], ?_⟩
    rw [hre]; simp [h1, h2]
  · refine ⟨Or.inr h1, by rw [h1, h2], ?_⟩
    rw [hre]; simp only [h1, h2]; push_cast; ring

/-- **The level-one displacement count.** For `z, z' ∈ 𝒟` and `0 ≤ R ≤ 1/4`, at most
`16 √R Im z + 2609⁴ + 2` matrices `B ∈ SL(2,ℤ)` satisfy `u(z, Bz') ≤ R`: the translations by an
integer within `4√R Im z` of `Re z - Re z'` (two signs each), and boundedly many others. -/
theorem card_near_le {z z' : ℍ} (hz : z ∈ ModularGroup.fd) (hz' : z' ∈ ModularGroup.fd) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : R ≤ 1 / 4) (S : Finset SL(2, ℤ)) (hS : ∀ B ∈ S, pairU z (B • z') ≤ R) :
    (S.card : ℝ) ≤ 16 * Real.sqrt R * z.im + (2609 ^ 4 + 2) := by
  classical
  set ρ := Real.sqrt (4 * R * (4 * R + 2)) * z.im with hρ
  have hρ0 : 0 ≤ ρ := mul_nonneg (Real.sqrt_nonneg _) z.im_pos.le
  have hρ2 : ρ ^ 2 = 4 * R * (4 * R + 2) * z.im ^ 2 := by
    rw [hρ, mul_pow, Real.sq_sqrt (by positivity)]
  set t₀ := z.re - z'.re
  set lo : ℤ := ⌈t₀ - ρ⌉
  set hi : ℤ := ⌊t₀ + ρ⌋
  -- the translations
  have h0 : ((S.filter fun B => B 1 0 = 0).card : ℝ) ≤ 2 * (2 * ρ + 1) := by
    set T : Finset (ℤ × ℤ) := ({1, -1} : Finset ℤ) ×ˢ Finset.Icc lo hi
    have hmaps : ∀ B ∈ S.filter (fun B => B 1 0 = 0), (B 0 0, B 0 0 * B 0 1) ∈ T := by
      intro B hB
      rw [Finset.mem_filter] at hB
      obtain ⟨ha, -, hre⟩ := translation_data B hB.2 z'
      obtain ⟨-, -, hx⟩ := pairU_le_bounds (hS B hB.1)
      rw [hre, ← hρ2] at hx
      have hab := abs_le_of_sq_le_sq' hx hρ0
      refine Finset.mem_product.2 ⟨by rcases ha with h | h <;> simp [h], Finset.mem_Icc.2 ⟨?_, ?_⟩⟩
      · exact Int.ceil_le.2 (by simp only [t₀]; linarith [hab.1])
      · exact Int.le_floor.2 (by simp only [t₀]; linarith [hab.2])
    have hinj : Set.InjOn (fun B : SL(2, ℤ) => (B 0 0, B 0 0 * B 0 1))
        (S.filter fun B => B 1 0 = 0 : Finset SL(2, ℤ)) := by
      intro B hB B' hB' he
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hB hB'
      simp only [Prod.mk.injEq] at he
      obtain ⟨ha, hd, -⟩ := translation_data B hB.2 z'
      obtain ⟨-, hd', -⟩ := translation_data B' hB'.2 z'
      have ha0 : B 0 0 ≠ 0 := by rcases ha with h | h <;> rw [h] <;> decide
      have hb : B 0 1 = B' 0 1 := by
        rw [← he.1] at he; exact mul_left_cancel₀ ha0 he.2
      ext i j
      fin_cases i <;> fin_cases j
      · exact he.1
      · exact hb
      · simp [hB.2, hB'.2]
      · simp [hd, hd', he.1]
    have hcard := Finset.card_le_card_of_injOn (fun B : SL(2, ℤ) => (B 0 0, B 0 0 * B 0 1)) hmaps hinj
    have hT : (T.card : ℝ) ≤ 2 * (2 * ρ + 1) := by
      rw [Finset.card_product, Int.card_Icc, Nat.cast_mul]
      have h2 : (({1, -1} : Finset ℤ).card : ℝ) = 2 := by norm_num [Finset.card_insert_of_notMem]
      rw [h2]
      have hle : (((hi + 1 - lo).toNat : ℕ) : ℝ) ≤ 2 * ρ + 1 := by
        have e : (((hi + 1 - lo).toNat : ℕ) : ℝ) = ((max (hi + 1 - lo) 0 : ℤ) : ℝ) := by
          rw [← Int.toNat_eq_max]; norm_cast
        rw [e, Int.cast_max, Int.cast_zero]
        have hfl : (hi : ℝ) ≤ t₀ + ρ := Int.floor_le _
        have hce : t₀ - ρ ≤ (lo : ℝ) := Int.le_ceil _
        refine max_le ?_ (by linarith)
        push_cast
        linarith
      linarith
    exact (Nat.cast_le.2 hcard).trans hT
  -- the remaining matrices have bounded entries
  have h1 : ((S.filter fun B => ¬ B 1 0 = 0).card : ℝ) ≤ 2609 ^ 4 := by
    obtain ⟨T, hTdef⟩ : ∃ T : Finset (Fin 2 → Fin 2 → ℤ), T = Fintype.piFinset fun _ : Fin 2 =>
        Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-1304 : ℤ) 1304 := ⟨_, rfl⟩
    have hmaps : Set.MapsTo (fun B : SL(2, ℤ) => fun i j => B i j)
        ↑(S.filter fun B => ¬ B 1 0 = 0) ↑T := by
      intro B hB
      rw [Finset.mem_coe, Finset.mem_filter] at hB
      rw [Finset.mem_coe, hTdef]
      simp only [Fintype.mem_piFinset, Finset.mem_Icc]
      intro i j
      exact abs_le.1 (abs_entry_le hz hz' hR hB.2 (hS B hB.1) i j)
    have hinj : Set.InjOn (fun B : SL(2, ℤ) => fun i j => B i j)
        ↑(S.filter fun B => ¬ B 1 0 = 0) := by
      intro B _ B' _ he
      ext i j
      exact congrFun (congrFun he i) j
    have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
    have hT : T.card = 2609 ^ 4 := by
      rw [hTdef]
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [show (Finset.Icc (-1304 : ℤ) 1304).card = 2609 by simp]
      ring
    rw [hT] at hcard
    exact_mod_cast hcard
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun B => B 1 0 = 0)
  have hρle : ρ ≤ 4 * Real.sqrt R * z.im := by
    rw [hρ]
    refine mul_le_mul_of_nonneg_right ?_ z.im_pos.le
    rw [show 4 * Real.sqrt R = Real.sqrt (16 * R) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [← hsplit, Nat.cast_add]
  linarith

/-! ### The cusp carries a bounded fraction of the mass -/

/-- On the one-point deck the norm is the norm of the single coordinate. -/
theorem norm_deck_zero (v : MaassFiniteDeckDirichlet.DeckSpace 0) : ‖v‖ = ‖v 1‖ := by
  rw [EuclideanSpace.norm_eq, Fintype.sum_subsingleton _ (1 : Deck 0), Real.sqrt_sq (norm_nonneg _)]

theorem norm_vecOf (g : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ‖vecOf g z‖ = ‖g z‖ := by
  rw [norm_deck_zero, vecOf_apply]

variable {lam : ℝ} {g : UpperHalfPlane → ℂ}

/-- The mass of `g` on the closed horocycle at height `y`. -/
def slice (g : UpperHalfPlane → ℂ) (y : ℝ) : ℝ :=
  ∫ x in (-(1 / 2 : ℝ))..(1 / 2), ‖g (ofComplex (point x y))‖ ^ 2

theorem point_add_one (x y : ℝ) : point (x + 1) y = point x y + 1 := by
  simp only [point]; push_cast; ring

theorem continuousOn_comp (hg : g ∈ cuspSpace lam) :
    ContinuousOn (fun w : ℂ => g (ofComplex w)) {w : ℂ | 0 < w.im} :=
  hg.2.1.1.continuousOn

/-- **Parseval on a horocycle**: `Σ_n |a_n(y)|² = ∫_{-1/2}^{1/2} |g(x+iy)|² dx`. -/
theorem hasSum_slice (hg : g ∈ cuspSpace lam) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ‖fourierCoeff g n y‖ ^ 2) (slice g y) := by
  have h := SelbergMaassParseval.coefficient_mass_hasSum 1 one_pos (F := g ∘ ofComplex)
    (continuousOn_comp hg) hy
  have hper : Function.Periodic (fun x => ‖g (ofComplex (point x y))‖ ^ 2) 1 := fun x => by
    have := periodic_comp hg (point x y) (point_im_pos hy)
    simp only [Function.comp] at this
    simp only [point_add_one, this]
  have hshift := hper.intervalIntegral_add_eq (-(1 / 2)) 0
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at hshift
  simp only [Complex.normSq_eq_norm_sq, inv_one, one_mul, Function.comp] at h
  rw [slice, hshift]
  exact h

theorem slice_nonneg (y : ℝ) : 0 ≤ slice g y :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

theorem slice_le {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) (y : ℝ) : slice g y ≤ C ^ 2 := by
  have hb : ∀ x ∈ Set.uIoc (-(1 / 2 : ℝ)) (1 / 2), ‖‖g (ofComplex (point x y))‖ ^ 2‖ ≤ C ^ 2 := by
    intro x _
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC _) 2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show |(1 / 2 : ℝ) - -(1 / 2)| = 1 by norm_num, mul_one] at this
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans this)

theorem continuousOn_slice (hg : g ∈ cuspSpace lam) {Y₀ : ℝ} (hY₀ : 0 < Y₀) :
    ContinuousOn (slice g) (Ioi Y₀) := by
  set H : ℝ → ℝ → ℝ := fun y x => ‖g (ofComplex (point x (max y Y₀)))‖ ^ 2
  have hH : Continuous (Function.uncurry H) := by
    have hp : Continuous fun p : ℝ × ℝ => point p.2 (max p.1 Y₀) := by
      simp only [point]; fun_prop
    have hmaps : ∀ p : ℝ × ℝ, point p.2 (max p.1 Y₀) ∈ {w : ℂ | 0 < w.im} := fun p => by
      show 0 < (point p.2 (max p.1 Y₀)).im
      simp only [point, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero]
      exact lt_max_of_lt_right hY₀
    exact (((continuousOn_comp hg).comp_continuous hp hmaps).norm.pow 2)
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hH
    (-(1 / 2 : ℝ)) (1 / 2)
  refine hc.continuousOn.congr fun y hy => ?_
  simp only [slice, H, max_eq_left (le_of_lt (mem_Ioi.1 hy))]

theorem integrableOn_slice (hg : g ∈ cuspSpace lam) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => slice g y / y ^ 2) (Ioi Y) := by
  obtain ⟨C, hC⟩ := exists_bound hg
  refine Integrable.mono' ((SarnakXueCuspTail.integrableOn_inv_sq hY).const_mul (C ^ 2)) ?_ ?_
  · exact ((continuousOn_slice hg hY).div (continuousOn_id.pow 2) fun y hy =>
      pow_ne_zero 2 (ne_of_gt (hY.trans hy))).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hY.trans hy
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (slice_nonneg y) (sq_nonneg _)), div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (slice_le hC y) (by positivity)

/-! ### One mode -/

theorem norm_fourierCoeff_le {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) (n : ℤ) (y : ℝ) :
    ‖fourierCoeff g n y‖ ≤ C := by
  unfold HeckeCusp.fourierCoeff
  unfold SelbergMaassFourier.coefficient _root_.RHTower.deningerFourierCoeff
  have hb : ∀ x ∈ Set.uIoc (0 : ℝ) 1, ‖_root_.RHTower.deningerFourierKernel 1 n x *
      (g ∘ ofComplex) (point x y)‖ ≤ C := by
    intro x _
    rw [norm_mul]
    have hk : ‖_root_.RHTower.deningerFourierKernel 1 n x‖ = 1 := by
      unfold _root_.RHTower.deningerFourierKernel
      rw [Complex.norm_exp]
      simp
    rw [hk, one_mul]
    exact hC _
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show |(1 : ℝ) - 0| = 1 by norm_num, mul_one] at this
  rw [norm_mul]
  simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, norm_one, one_mul, Complex.ofReal_one]
  exact this

theorem mode_integrable (hg : g ∈ cuspSpace lam) (n : ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => ‖fourierCoeff g n y‖ ^ 2 / y ^ 2) (Ioi Y) := by
  obtain ⟨C, hC⟩ := exists_bound hg
  have hcont : ContinuousOn (fourierCoeff g n) (Ioi 0) := (modalSol_fourierCoeff hg n).continuousOn.1
  refine Integrable.mono' ((SarnakXueCuspTail.integrableOn_inv_sq hY).const_mul (C ^ 2)) ?_ ?_
  · refine (((hcont.mono (Ioi_subset_Ioi hY.le)).norm.pow 2).div (continuousOn_id.pow 2) fun y hy =>
      pow_ne_zero 2 (ne_of_gt (hY.trans hy))).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hY.trans hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
      (norm_fourierCoeff_le hC n y) 2) (by positivity)

/-- **A mode decays monotonically beyond its turning point.** If `λ ≤ 4π²Y₁²`, every nonconstant mode
`|a_n|²` is nonincreasing on `[Y₁, ∞)`: there `a_n'' = (4π²n² − λ/y²) a_n` has a nonnegative
coefficient, so `|a_n|²` is convex, and it tends to `0`. -/
theorem antitone_mode (hg : g ∈ cuspSpace lam) {n : ℤ} (hn : n ≠ 0) {Y₁ : ℝ} (hY₁ : 0 < Y₁)
    (hlam : lam ≤ 4 * Real.pi ^ 2 * Y₁ ^ 2) :
    AntitoneOn (fun y => ‖fourierCoeff g n y‖ ^ 2) (Ici Y₁) := by
  set k : ℝ := SelbergMaassFourier.signedFrequency ((0 + 1 : ℕ) : ℝ) n
  have ha := modalSol_fourierCoeff hg n
  have hk : lam ≤ k ^ 2 * Y₁ ^ 2 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      nlinarith [sq_abs (n : ℝ)]
    have hk2 : k ^ 2 = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
      simp only [k, SelbergMaassFourier.signedFrequency]; push_cast; ring
    rw [hk2]
    have := mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Y₁ ^ 2)
    nlinarith
  have h := SarnakXueCuspTail.normSq_antitoneOn (a := fourierCoeff g n) (k := k) hY₁ hk
    (fun y hy => (ha y hy).1)
    (fun y hy => (ha y hy).2.differentiableAt.hasDerivAt)
    (fun y hy => by
      rw [(ha y hy).2.deriv]
      have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
      rw [show modalConst n = k ^ 2 from rfl]
      push_cast
      field_simp
      ring)
    (tendsto_fourierCoeff hg n)
  refine fun y hy y' hy' hle => ?_
  have := h hy hy' hle
  simp only [Complex.normSq_eq_norm_sq] at this
  exact this

/-- **One mode carries little mass far in the cusp**: `Y ∫_Y^∞ |a_n|²/y² ≤ Y₁ ∫_{Y₁}^∞ |a_n|²/y²`
for `Y₁ < Y` beyond the turning point. -/
theorem mode_tail_le (hg : g ∈ cuspSpace lam) (n : ℤ) {Y₁ Y : ℝ} (hY₁ : 0 < Y₁) (hY : Y₁ < Y)
    (hlam : lam ≤ 4 * Real.pi ^ 2 * Y₁ ^ 2) :
    Y * ∫ y in Ioi Y, ‖fourierCoeff g n y‖ ^ 2 / y ^ 2 ≤
      Y₁ * ∫ y in Ioi Y₁, ‖fourierCoeff g n y‖ ^ 2 / y ^ 2 := by
  set G : ℝ → ℝ := fun y => ‖fourierCoeff g n y‖ ^ 2
  have hi := mode_integrable hg n hY₁
  have hsplit : ∫ y in Ioi Y₁, G y / y ^ 2 = (∫ y in Ioc Y₁ Y, G y / y ^ 2) + ∫ y in Ioi Y, G y / y ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi hY.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hY.le))]
  have hT : 0 ≤ ∫ y in Ioi Y, G y / y ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun y _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hn : n = 0
  · subst hn
    have hz : ∀ Z : ℝ, 0 < Z → ∫ y in Ioi Z, G y / y ^ 2 = 0 := fun Z hZ =>
      setIntegral_eq_zero_of_forall_eq_zero fun y hy => by
        simp [G, fourierCoeff_zero hg (hZ.trans hy)]
    change Y * ∫ y in Ioi Y, G y / y ^ 2 ≤ Y₁ * ∫ y in Ioi Y₁, G y / y ^ 2
    rw [hz Y (hY₁.trans hY), hz Y₁ hY₁]
    simp
  · have h := SarnakXueCuspTail.tail_le_bulk hY₁ hY (antitone_mode hg hn hY₁ hlam)
      (fun y _ => sq_nonneg _) hi
    change Y * ∫ y in Ioi Y, G y / y ^ 2 ≤ Y₁ * ∫ y in Ioi Y₁, G y / y ^ 2
    rw [hsplit]
    nlinarith

/-! ### All modes -/

/-- **The cusp mass is the sum of the modal masses.** -/
theorem hasSum_tail (hg : g ∈ cuspSpace lam) {Y : ℝ} (hY : 1 ≤ Y) :
    HasSum (fun n : ℤ => ∫ y in Ioi Y, ‖fourierCoeff g n y‖ ^ 2 / y ^ 2)
      (∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y < z.im}, ‖g z‖ ^ 2) := by
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY
  have hiter := MaassFiniteDeckDirichlet.cusp_normSq_tail_eq_iterated (vecOf g) (continuous_vecOf hg)
    (memLp_vecOf hg) hY
  simp only [norm_vecOf] at hiter
  have he : (∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y < z.im}, ‖g z‖ ^ 2) =
      ∫ y in Ioi Y, slice g y / y ^ 2 := by
    rw [hiter]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [slice]
    ring
  rw [he]
  refine hasSum_integral_of_dominated_convergence (fun n y => ‖fourierCoeff g n y‖ ^ 2 / y ^ 2)
    (fun n => (mode_integrable hg n hY0).aestronglyMeasurable) (fun n => ?_) ?_ ?_ ?_
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ((hasSum_slice hg (hY0.trans hy)).div_const _).summable
  · refine (integrableOn_slice hg hY0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (((hasSum_slice hg (hY0.trans hy)).div_const (y ^ 2)).tsum_eq).symm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (hasSum_slice hg (hY0.trans hy)).div_const (y ^ 2)

/-- **The cusp mass of a cusp form decays like `1/Y` beyond the turning point.** If `1 ≤ Y₁ < Y` and
`λ ≤ 4π²Y₁²`, then `Y ∫_{𝒟, y > Y} |g|² ≤ Y₁ ∫_{𝒟, y > Y₁} |g|²`. -/
theorem tail_le (hg : g ∈ cuspSpace lam) {Y₁ Y : ℝ} (hY₁ : 1 ≤ Y₁) (hY : Y₁ < Y)
    (hlam : lam ≤ 4 * Real.pi ^ 2 * Y₁ ^ 2) :
    Y * ∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y < z.im}, ‖g z‖ ^ 2 ≤
      Y₁ * ∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y₁ < z.im}, ‖g z‖ ^ 2 := by
  have h1 := hasSum_tail hg (hY₁.trans hY.le)
  have h2 := hasSum_tail hg hY₁
  rw [← h1.tsum_eq, ← h2.tsum_eq, ← tsum_mul_left, ← tsum_mul_left]
  exact (h1.summable.mul_left Y).tsum_le_tsum
    (fun n => mode_tail_le hg n (lt_of_lt_of_le one_pos hY₁) hY hlam) (h2.summable.mul_left Y₁)

/-! ### The pointwise Bessel inequality -/

section Bessel

variable {φ : ℝ → ℝ} {M R : ℝ}

/-- The automorphic kernel `K_z(z') = ½ Σ_B φ(u(z, Bz'))` of the point-pair operator on `𝒟`. -/
def kerFn (φ : ℝ → ℝ) (R : ℝ) (z z' : UpperHalfPlane) : ℝ :=
  1 / 2 * ∑ B ∈ ppNearSet z R, φ (pairU z (B • z'))

theorem continuous_kerFn (hφc : Continuous φ) (z : UpperHalfPlane) : Continuous (kerFn φ R z) :=
  continuous_const.mul (continuous_finsetSum _ fun B _ =>
    hφc.comp ((continuous_pairU_right z).comp (continuous_smul_int B)))

/-- On the one-point deck the point-pair operator integrates against the automorphic kernel. -/
theorem ppApply_one (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hφR : KernelSupport φ R)
    {F : UpperHalfPlane → DeckSpace 0} (hF : MemLp F 2 MaassCongruenceL2.cellMeasure)
    (z : UpperHalfPlane) :
    ppApply φ F z 1 = ∫ z' in ModularGroup.fd, (kerFn φ R z z' : ℂ) * F z' 1 := by
  set pr : DeckSpace 0 →L[ℂ] ℂ := EuclideanSpace.proj (1 : Deck 0)
  have hpr : ∀ v : DeckSpace 0, pr v = v 1 := fun v => rfl
  have hterm : ∀ B : SL(2, ℤ), pr (ppTerm φ F z B) =
      ∫ z' in ModularGroup.fd, ((φ (pairU z (B • z')) : ℝ) : ℂ) * F z' 1 := by
    intro B
    unfold ppTerm
    rw [← pr.integral_comp_comm (integrable_ppTerm_integrand hφc hφM hF z B)]
    refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
    simp only [hpr, WeylBound.deckRho_zero_apply, PiLp.smul_apply, smul_eq_mul]
  have hint : ∀ B : SL(2, ℤ), Integrable (fun z' => ((φ (pairU z (B • z')) : ℝ) : ℂ) * F z' 1)
      (volume.restrict ModularGroup.fd) := by
    intro B
    refine (pr.integrable_comp (integrable_ppTerm_integrand hφc hφM hF z B)).congr
      (Eventually.of_forall fun z' => ?_)
    simp only [hpr, WeylBound.deckRho_zero_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← hpr, ppApply, tsum_ppTerm_eq_sum hφR, map_smul, map_sum]
  simp_rw [hterm]
  rw [← integral_finsetSum _ fun B _ => hint B, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only [kerFn]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun B _ => by ring

theorem inner_ones_apply (v : DeckSpace 0) : ⟪onesVec 0, v⟫_ℂ = v 1 := by
  rw [PiLp.inner_apply, Fintype.sum_subsingleton _ (1 : Deck 0)]
  simp [onesVec]

theorem norm_onesVec_zero : ‖onesVec 0‖ = 1 := by
  rw [norm_deck_zero]
  simp [onesVec]

/-- The basis vector of index `i` is the class of its smooth representative. -/
theorem basis_eq (i : CuspEigenIndex 0) :
    ((cuspEigenBasis 0 i : CuspidalL2 0) : DeckL2 0) =
      toDeckL2 (CuspGravity.cuspFn i) (CuspGravity.isCuspLaplaceEigen_cuspFn i).memLp :=
  (cuspEigenBasis_spec i).choose_spec.choose_spec

theorem orthonormal_basis :
    Orthonormal ℂ (fun i : CuspEigenIndex 0 => ((cuspEigenBasis 0 i : CuspidalL2 0) : DeckL2 0)) :=
  (cuspEigenBasis 0).orthonormal.comp_linearIsometry (cuspidalL2Closure 0).subtypeₗᵢ

/-- **The pointwise Bessel inequality.** Let `φ ≥ 0` be continuous with `φ ≤ M`, radius `R` and mass `1`,
acting on the basis eigenfunctions of `s` by `κ_i`. If at most `m` matrices `B` satisfy `u(z, Bz') ≤ R`
for each `z' ∈ 𝒟`, then `Σ_{i ∈ s} |κ_i|² |U_i(z)|² ≤ m M / 2`. -/
theorem sum_sq_le (hφc : Continuous φ) (hφ0 : ∀ u, 0 ≤ φ u) (hφM : ∀ u, φ u ≤ M)
    (hφR : KernelSupport φ R) (hmass : ppKernelMass φ = 1) (s : Finset (CuspEigenIndex 0))
    (κ : CuspEigenIndex 0 → ℂ)
    (hκ : ∀ i ∈ s, ∀ w, ppApply φ (CuspGravity.cuspFn i) w = κ i • CuspGravity.cuspFn i w)
    {z : UpperHalfPlane} {m : ℝ} (hm0 : 0 ≤ m)
    (hm : ∀ z' ∈ ModularGroup.fd, ∀ T : Finset SL(2, ℤ), (∀ B ∈ T, pairU z (B • z') ≤ R) →
      (T.card : ℝ) ≤ m) :
    ∑ i ∈ s, ‖κ i‖ ^ 2 * ‖CuspGravity.cuspFn i z‖ ^ 2 ≤ m * M / 2 := by
  have hφA : ∀ u, |φ u| ≤ M := fun u => by rw [abs_of_nonneg (hφ0 u)]; exact hφM u
  have hM0 : 0 ≤ M := (hφ0 0).trans (hφM 0)
  set K := kerFn φ R z
  have hK0 : ∀ z', 0 ≤ K z' := fun z' =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun B _ => hφ0 _)
  -- the kernel as an `L²` vector
  set F : UpperHalfPlane → DeckSpace 0 := fun z' => ((K z' : ℝ) : ℂ) • onesVec 0
  have hFc : Continuous F :=
    (Complex.continuous_ofReal.comp (continuous_kerFn hφc z)).smul continuous_const
  have hKb : ∀ z', K z' ≤ 1 / 2 * ((ppNearSet z R).card * M) := fun z' => by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc ∑ B ∈ ppNearSet z R, φ (pairU z (B • z')) ≤ ∑ B ∈ ppNearSet z R, M :=
          Finset.sum_le_sum fun B _ => hφM _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hF : MemLp F 2 MaassCongruenceL2.cellMeasure := by
    refine MemLp.of_bound hFc.aestronglyMeasurable (1 / 2 * ((ppNearSet z R).card * M))
      (Eventually.of_forall fun z' => ?_)
    rw [norm_smul, norm_onesVec_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hK0 z')]
    exact hKb z'
  set v := toDeckL2 F hF
  -- `⟨K_z, U_i⟩ = κ_i U_i(z)`
  have hinner : ∀ i ∈ s, ⟪v, ((cuspEigenBasis 0 i : CuspidalL2 0) : DeckL2 0)⟫_ℂ =
      κ i * CuspGravity.cuspFn i z 1 := by
    intro i hi
    have hU := CuspGravity.isCuspLaplaceEigen_cuspFn i
    rw [basis_eq, MeasureTheory.L2.inner_def]
    have h1 : ⇑(toDeckL2 F hF) =ᵐ[MaassCongruenceL2.cellMeasure] F := MemLp.coeFn_toLp _
    have h2 : ⇑(toDeckL2 (CuspGravity.cuspFn i) hU.memLp) =ᵐ[MaassCongruenceL2.cellMeasure]
        CuspGravity.cuspFn i := MemLp.coeFn_toLp _
    have e : ∫ z', ⟪(toDeckL2 F hF : UpperHalfPlane → DeckSpace 0) z',
        (toDeckL2 (CuspGravity.cuspFn i) hU.memLp : UpperHalfPlane → DeckSpace 0) z'⟫_ℂ
          ∂MaassCongruenceL2.cellMeasure =
        ∫ z' in ModularGroup.fd, (K z' : ℂ) * CuspGravity.cuspFn i z' 1 := by
      refine integral_congr_ae ?_
      filter_upwards [h1, h2] with z' hz1 hz2
      rw [hz1, hz2]
      simp only [F, inner_smul_left, Complex.conj_ofReal, inner_ones_apply]
    rw [e, ← ppApply_one hφc hφA hφR hU.memLp z, hκ i hi z]
    rfl
  -- `‖K_z‖² = ∫_𝒟 K_z²`
  have hnorm : ‖v‖ ^ 2 = ∫ z' in ModularGroup.fd, K z' ^ 2 := by
    rw [_root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    refine integral_congr_ae ?_
    have h1 : ⇑v =ᵐ[MaassCongruenceL2.cellMeasure] F := MemLp.coeFn_toLp hF
    filter_upwards [h1] with z' hz
    rw [hz]
    simp only [F, norm_smul, norm_onesVec_zero, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- Cauchy–Schwarz over the near translates
  have hpt : ∀ z' ∈ ModularGroup.fd,
      K z' ^ 2 ≤ m * M / 4 * ∑ B ∈ ppNearSet z R, φ (pairU z (B • z')) := by
    intro z' hz'
    classical
    set T := (ppNearSet z R).filter fun B => pairU z (B • z') ≤ R
    have hsum : ∑ B ∈ ppNearSet z R, φ (pairU z (B • z')) = ∑ B ∈ T, φ (pairU z (B • z')) := by
      refine (Finset.sum_filter_of_ne fun B _ hB => ?_).symm
      by_contra h
      exact hB (hφR _ (lt_of_not_ge h))
    have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := fun B => φ (pairU z (B • z')))
    have hcard : (T.card : ℝ) ≤ m := hm z' hz' T fun B hB => (Finset.mem_filter.1 hB).2
    have hsq : ∑ B ∈ T, φ (pairU z (B • z')) ^ 2 ≤ M * ∑ B ∈ ppNearSet z R, φ (pairU z (B • z')) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun B _ => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun B _ _ =>
          mul_nonneg hM0 (hφ0 _))
      nlinarith [hφ0 (pairU z (B • z')), hφM (pairU z (B • z'))]
    have hS0 : 0 ≤ ∑ B ∈ ppNearSet z R, φ (pairU z (B • z')) := Finset.sum_nonneg fun B _ => hφ0 _
    have hK : K z' ^ 2 = 1 / 4 * (∑ B ∈ T, φ (pairU z (B • z'))) ^ 2 := by
      simp only [K, kerFn, hsum]; ring
    rw [hK]
    have := hcs.trans (mul_le_mul hcard hsq (Finset.sum_nonneg fun B _ => sq_nonneg _) hm0)
    nlinarith
  -- integrate over the cell
  have hint : ∀ B : SL(2, ℤ), Integrable (fun z' => φ (pairU z (B • z')))
      (volume.restrict ModularGroup.fd) := fun B =>
    (integrable_ppKernel hφc hφA z B).congr (Eventually.of_forall fun z' => abs_of_nonneg (hφ0 _))
  have htwo : ∑ B ∈ ppNearSet z R, ∫ z' in ModularGroup.fd, φ (pairU z (B • z')) ≤ 2 := by
    have h := ofReal_sum_kernel_le hφc hφA z (ppNearSet z R)
    rw [hmass, mul_one] at h
    simp_rw [abs_of_nonneg (hφ0 _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).1 (h.trans_eq (by norm_num))
  have hKint : ∫ z' in ModularGroup.fd, K z' ^ 2 ≤ m * M / 2 := by
    calc ∫ z' in ModularGroup.fd, K z' ^ 2
        ≤ ∫ z' in ModularGroup.fd, m * M / 4 * ∑ B ∈ ppNearSet z R, φ (pairU z (B • z')) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z' => sq_nonneg _)
            ((integrable_finsetSum _ fun B _ => hint B).const_mul _) ?_
          filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z' hz'
          exact hpt z' hz'
      _ = m * M / 4 * ∑ B ∈ ppNearSet z R, ∫ z' in ModularGroup.fd, φ (pairU z (B • z')) := by
          rw [integral_const_mul, integral_finsetSum _ fun B _ => hint B]
      _ ≤ m * M / 4 * 2 := mul_le_mul_of_nonneg_left htwo (by positivity)
      _ = m * M / 2 := by ring
  -- Bessel
  have hB := orthonormal_basis.sum_inner_products_le v (s := s)
  rw [hnorm] at hB
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_)) (hB.trans hKint)
  rw [norm_inner_symm, hinner i hi, norm_mul, mul_pow, norm_deck_zero (CuspGravity.cuspFn i z)]

end Bessel

/-! ### The count -/

/-- The spectral parameter `s = ½ + i√(λ - ¼)` of a basis eigenvalue: `s(1 - s) = λ`, `|s|² = λ`. -/
theorem exists_param (i : CuspEigenIndex 0) : ∃ s : ℂ, s * (1 - s) = (i.1 : ℂ) ∧ ‖s‖ ^ 2 = i.1 := by
  have hq := one_quarter_le_cuspEigenBasis i
  set t := Real.sqrt (i.1 - 1 / 4)
  have ht : t ^ 2 = i.1 - 1 / 4 := Real.sq_sqrt (by linarith)
  refine ⟨1 / 2 + (t : ℂ) * Complex.I, ?_, ?_⟩
  · have h : (1 / 2 + (t : ℂ) * Complex.I) * (1 - (1 / 2 + (t : ℂ) * Complex.I)) =
        1 / 4 + ((t ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h, ht]
    push_cast
    ring
  · rw [← Complex.normSq_eq_norm_sq]
    have h : Complex.normSq (1 / 2 + (t : ℂ) * Complex.I) = 1 / 4 + t ^ 2 := by
      simp [Complex.normSq_apply]
      ring
    rw [h, ht]
    ring

/-- **The Weyl upper bound.** The number of cusp forms of eigenvalue at most `Λ` is `O(Λ + 1)`. -/
theorem cuspCount_le : ∃ C : ℝ, ∀ Λ : ℝ, 0 ≤ Λ → (cuspCount Λ : ℝ) ≤ C * (Λ + 1) := by
  refine ⟨3414 * (2609 ^ 4 + 18), fun Λ hΛ => ?_⟩
  set C₀ : ℝ := 2609 ^ 4 + 2
  -- the kernel
  set R : ℝ := 1 / (512 * (Λ + 1)) with hRdef
  have hR : 0 < R := by positivity
  have hR4 : R ≤ 1 / 4 := by
    rw [hRdef, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hRΛ : R * (512 * (Λ + 1)) = 1 := by rw [hRdef]; field_simp
  set P₀ := WeylBound.narrowProfile R hR
  have hP₀1 : ∀ u, P₀.toFun u ≤ 1 := fun u => by rw [WeylBound.narrow_toFun]; exact WeylBound.baseBump.le_one
  have hfin : ppKernelMass P₀.toFun ≠ ⊤ :=
    (kernelMass_lt_top P₀.radius_nonneg (fun u => by
      rw [abs_of_nonneg (WeylBound.narrow_nonneg R hR u)]; exact hP₀1 u) P₀.kernelSupport).ne
  set m := (ppKernelMass P₀.toFun).toReal
  have hm : Real.pi * R / 8 ≤ m := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (WeylBound.narrow_mass_ge hR (by linarith))
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  let P : SmoothProfile :=
    ⟨fun u => m⁻¹ * P₀.toFun u, R, hR.le, contDiff_const.mul P₀.contDiff,
      fun u hu => by simp [P₀.support u hu]⟩
  have hP0 : ∀ u, 0 ≤ P.toFun u := fun u => mul_nonneg (inv_nonneg.2 hm0.le) (WeylBound.narrow_nonneg R hR u)
  have hPM : ∀ u, P.toFun u ≤ m⁻¹ := fun u =>
    mul_le_of_le_one_right (inv_nonneg.2 hm0.le) (hP₀1 u)
  have hPm : ppKernelMass P.toFun = 1 := by
    change ppKernelMass (fun u => m⁻¹ * P₀.toFun u) = 1
    rw [ppKernelMass_smul (inv_nonneg.2 hm0.le), ← ENNReal.ofReal_toReal hfin,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hm0.le), inv_mul_cancel₀ hm0.ne', ENNReal.ofReal_one]
  have hMinv : m⁻¹ ≤ 8 * 512 * (Λ + 1) / Real.pi := by
    have h := inv_anti₀ (by positivity) hm
    calc m⁻¹ ≤ (Real.pi * R / 8)⁻¹ := h
      _ = 8 * 512 * (Λ + 1) / Real.pi := by rw [hRdef]; field_simp
  have hRP : P.radius * (512 * (Λ + 1)) ≤ 1 := hRΛ.le
  -- the eigenvalues below `Λ`
  set S := (finite_cuspEigenIndex_le Λ).toFinset
  have hS : ∀ i ∈ S, i.1 ≤ Λ := fun i hi => (Set.Finite.mem_toFinset (finite_cuspEigenIndex_le Λ)).1 hi
  choose sOf hsOf using exists_param
  set κ : CuspEigenIndex 0 → ℂ := fun i => selbergTransform P.toFun (sOf i)
  have hκ : ∀ i ∈ S, ∀ w, ppApply P.toFun (CuspGravity.cuspFn i) w = κ i • CuspGravity.cuspFn i w := by
    intro i _ w
    have hU := CuspGravity.isCuspLaplaceEigen_cuspFn i
    refine ppApply_eigen P.contDiff_two.continuous P.kernelSupport hU.contDiffOn hU.equivariant
      (fun z => ?_) w
    rw [hU.eigen z, (hsOf i).1]
    push_cast
    rfl
  have hκ1 : ∀ i ∈ S, 1 / 2 ≤ ‖κ i‖ := by
    intro i hi
    have h := CuspSpectrum.norm_selbergTransform_sub_one_le P hP0 hPm hΛ hRP
      (le_of_eq_of_le (hsOf i).2 (hS i hi))
    have h2 := norm_sub_norm_le (1 : ℂ) (κ i)
    rw [norm_sub_rev, norm_one] at h2
    linarith
  -- heights
  set Y₁ : ℝ := max 1 (Real.sqrt Λ / (2 * Real.pi))
  set Y : ℝ := 5 * Y₁
  have hY₁ : 1 ≤ Y₁ := le_max_left _ _
  have hY : Y₁ < Y := by simp only [Y]; linarith
  have hΛY : Λ ≤ 4 * Real.pi ^ 2 * Y₁ ^ 2 := by
    have h1 : Real.sqrt Λ ≤ 2 * Real.pi * Y₁ := by
      have := le_max_right 1 (Real.sqrt Λ / (2 * Real.pi))
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [Real.sq_sqrt hΛ] at h2
    nlinarith
  have hRY : Real.sqrt R * Y ≤ 1 := by
    have hY0 : 0 ≤ Y := by positivity
    have hY₁le : Y₁ ≤ 1 + Real.sqrt Λ :=
      max_le (by linarith [Real.sqrt_nonneg Λ]) (by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Real.sqrt_nonneg Λ, Real.pi_gt_three])
    have hsq : (1 + Real.sqrt Λ) ^ 2 ≤ 2 * (Λ + 1) := by
      nlinarith [sq_nonneg (1 - Real.sqrt Λ), Real.sq_sqrt hΛ]
    have hRY2 : R * Y ^ 2 ≤ 1 := by
      have h1 : Y ^ 2 ≤ 25 * (2 * (Λ + 1)) := by
        have := pow_le_pow_left₀ (by linarith) hY₁le 2
        simp only [Y]; nlinarith
      calc R * Y ^ 2 ≤ R * (25 * (2 * (Λ + 1))) := mul_le_mul_of_nonneg_left h1 hR.le
        _ = 50 / 512 := by rw [hRdef]; field_simp; ring
        _ ≤ 1 := by norm_num
    calc Real.sqrt R * Y = Real.sqrt (R * Y ^ 2) := by
          rw [Real.sqrt_mul hR.le, Real.sqrt_sq hY0]
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hRY2
      _ = 1 := Real.sqrt_one
  -- the region below height `Y`
  set A : Set UpperHalfPlane := ModularGroup.fd ∩ {z | z.im ≤ Y}
  have hAm : MeasurableSet A := ModularGroup.isClosed_fd.measurableSet.inter
    (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)
  have hvolA : (volume A).toReal ≤ Real.pi / 3 := by
    have h : volume A ≤ ENNReal.ofReal (Real.pi / 3) :=
      (measure_mono inter_subset_left).trans volume_fd_eq.le
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hAfin : volume A ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((measure_mono inter_subset_left).trans volume_fd_eq.le)
  -- pointwise bound on `A`
  have hpt : ∀ z ∈ A, ∑ i ∈ S, ‖CuspGravity.cuspFn i z‖ ^ 2 ≤ 2 * (16 + C₀) * m⁻¹ := by
    intro z hz
    have hzY : z.im ≤ Y := hz.2
    have hmc : ∀ z' ∈ ModularGroup.fd, ∀ T : Finset SL(2, ℤ), (∀ B ∈ T, pairU z (B • z') ≤ R) →
        (T.card : ℝ) ≤ 16 + C₀ := by
      intro z' hz' T hT
      have h := card_near_le hz.1 hz' hR.le hR4 T hT
      have h2 : Real.sqrt R * z.im ≤ 1 :=
        (mul_le_mul_of_nonneg_left hzY (Real.sqrt_nonneg _)).trans hRY
      nlinarith
    have h := sum_sq_le P.contDiff_two.continuous hP0 hPM P.kernelSupport hPm S κ hκ
      (by positivity) hmc
    have h4 : ∑ i ∈ S, 1 / 4 * ‖CuspGravity.cuspFn i z‖ ^ 2 ≤
        ∑ i ∈ S, ‖κ i‖ ^ 2 * ‖CuspGravity.cuspFn i z‖ ^ 2 := by
      refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have := hκ1 i hi
      nlinarith
    rw [← Finset.mul_sum] at h4
    nlinarith
  -- each eigenfunction keeps four fifths of its mass in `A`
  have hlow : ∀ i ∈ S, 4 / 5 ≤ ∫ z in A, ‖CuspGravity.cuspFn i z‖ ^ 2 := by
    intro i hi
    have hU := CuspGravity.isCuspLaplaceEigen_cuspFn i
    have hg := HeckeCusp.component_mem_cuspSpace i
    have hn : ∀ z, ‖CuspGravity.cuspFn i z‖ = ‖CuspGravity.cuspFn i z 1‖ := fun z => norm_deck_zero _
    have hU2 : IntegrableOn (fun z => ‖CuspGravity.cuspFn i z‖ ^ 2) ModularGroup.fd :=
      (memLp_two_iff_integrable_sq_norm hU.memLp.1).1 hU.memLp
    have hone : ∫ z in ModularGroup.fd, ‖CuspGravity.cuspFn i z‖ ^ 2 = 1 := by
      have h1 : ‖toDeckL2 (CuspGravity.cuspFn i) hU.memLp‖ = 1 := by
        rw [← basis_eq]; exact orthonormal_basis.1 i
      have h2 := _root_.HTGeometry.norm_l2_sq_eq_integral_norm_sq _
        (toDeckL2 (CuspGravity.cuspFn i) hU.memLp)
      rw [h1, one_pow] at h2
      rw [h2]
      have h3 : ⇑(toDeckL2 (CuspGravity.cuspFn i) hU.memLp) =ᵐ[MaassCongruenceL2.cellMeasure]
          CuspGravity.cuspFn i := MemLp.coeFn_toLp hU.memLp
      refine integral_congr_ae ?_
      filter_upwards [h3] with z hz
      rw [hz]
    have htail := tail_le hg hY₁ hY ((hS i hi).trans hΛY)
    simp only [← hn] at htail
    have hT1 : ∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y₁ < z.im}, ‖CuspGravity.cuspFn i z‖ ^ 2 ≤ 1 :=
      (setIntegral_mono_set hU2 (Eventually.of_forall fun z => sq_nonneg _)
        (Eventually.of_forall inter_subset_left)).trans_eq hone
    have hsplit := integral_inter_add_sdiff (t := {z : UpperHalfPlane | z.im ≤ Y})
      (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const) hU2
    have hdiff : ModularGroup.fd \ {z : UpperHalfPlane | z.im ≤ Y} =
        ModularGroup.fd ∩ {z : UpperHalfPlane | Y < z.im} := by
      ext z; simp [not_le]
    rw [hdiff, hone] at hsplit
    have hT0 : 0 ≤ ∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y₁ < z.im}, ‖CuspGravity.cuspFn i z‖ ^ 2 :=
      setIntegral_nonneg (ModularGroup.isClosed_fd.measurableSet.inter
        (measurableSet_lt measurable_const UpperHalfPlane.continuous_im.measurable)) fun z _ => sq_nonneg _
    have hYY : Y₁ * ∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y₁ < z.im}, ‖CuspGravity.cuspFn i z‖ ^ 2
        ≤ Y₁ := by nlinarith
    have : Y * ∫ z in ModularGroup.fd ∩ {z : UpperHalfPlane | Y < z.im}, ‖CuspGravity.cuspFn i z‖ ^ 2
        ≤ Y₁ := htail.trans hYY
    simp only [Y] at this
    have hY₁0 : 0 < Y₁ := by linarith
    nlinarith
  -- integrate the pointwise bound
  have hsum : ∑ i ∈ S, ∫ z in A, ‖CuspGravity.cuspFn i z‖ ^ 2 ≤ 2 * (16 + C₀) * m⁻¹ * (Real.pi / 3) := by
    have hint : ∀ i ∈ S, IntegrableOn (fun z => ‖CuspGravity.cuspFn i z‖ ^ 2) A := fun i _ => by
      have h : IntegrableOn (fun z => ‖CuspGravity.cuspFn i z‖ ^ 2) ModularGroup.fd :=
        (memLp_two_iff_integrable_sq_norm (CuspGravity.isCuspLaplaceEigen_cuspFn i).memLp.1).1
          (CuspGravity.isCuspLaplaceEigen_cuspFn i).memLp
      exact h.mono_set inter_subset_left
    rw [← integral_finsetSum _ hint]
    calc ∫ z in A, ∑ i ∈ S, ‖CuspGravity.cuspFn i z‖ ^ 2
        ≤ ∫ z in A, 2 * (16 + C₀) * m⁻¹ :=
          setIntegral_mono_on (integrable_finsetSum _ hint) (integrableOn_const hAfin) hAm hpt
      _ = (volume A).toReal * (2 * (16 + C₀) * m⁻¹) := by
          rw [setIntegral_const, smul_eq_mul, Measure.real]
      _ ≤ Real.pi / 3 * (2 * (16 + C₀) * m⁻¹) :=
          mul_le_mul_of_nonneg_right hvolA (by positivity)
      _ = 2 * (16 + C₀) * m⁻¹ * (Real.pi / 3) := by ring
  have hcard : 4 / 5 * (S.card : ℝ) ≤ 2 * (16 + C₀) * m⁻¹ * (Real.pi / 3) := by
    have h := Finset.card_nsmul_le_sum S (fun i => ∫ z in A, ‖CuspGravity.cuspFn i z‖ ^ 2) (4 / 5) hlow
    rw [nsmul_eq_mul] at h
    linarith
  have hfinal : 2 * (16 + C₀) * m⁻¹ * (Real.pi / 3) ≤
      2 * (16 + C₀) * (8 * 512 * (Λ + 1) / Real.pi) * (Real.pi / 3) := by
    gcongr
  have hpi : 2 * (16 + C₀) * (8 * 512 * (Λ + 1) / Real.pi) * (Real.pi / 3) =
      8192 / 3 * (16 + C₀) * (Λ + 1) := by
    field_simp; ring
  have hc : (cuspCount Λ : ℝ) = S.card := rfl
  rw [hc]
  simp only [C₀] at hcard hfinal hpi ⊢
  nlinarith

/-- **The Weyl law up to constants.** `cΛ ≤ N(Λ) ≤ CΛ` for all large `Λ`: the cusp spectrum of the
modular horizon has the eigenvalue density of a compact surface. -/
theorem weyl_law_order :
    ∃ c > 0, ∃ C > 0, ∃ Λ₀ : ℝ, ∀ Λ ≥ Λ₀, c * Λ ≤ cuspCount Λ ∧ (cuspCount Λ : ℝ) ≤ C * Λ := by
  obtain ⟨c, hc, Λ₁, hlow⟩ := WeylBound.weyl_lower_bound
  obtain ⟨C, hC⟩ := cuspCount_le
  have hC0 : 0 ≤ C := by
    have h := hC 0 le_rfl
    have : (0 : ℝ) ≤ cuspCount 0 := Nat.cast_nonneg _
    linarith
  refine ⟨c, hc, 2 * C + 1, by positivity, max Λ₁ 1, fun Λ hΛ => ⟨hlow Λ (le_trans (le_max_left _ _) hΛ), ?_⟩⟩
  have h1 : 1 ≤ Λ := le_trans (le_max_right _ _) hΛ
  have := hC Λ (by linarith)
  nlinarith

/-- **The heat trace of the cusp channel is finite.** For every `t > 0`, `Σ_j e^{-tλ_j} < ∞`: the
partition function of the undamped tones of the modular horizon converges at every temperature. -/
theorem summable_exp_neg_mul {t : ℝ} (ht : 0 < t) :
    Summable fun i : CuspEigenIndex 0 => Real.exp (-(t * i.1)) := by
  classical
  obtain ⟨C, hC⟩ := cuspCount_le
  set r := Real.exp (-t)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]; exact Real.exp_lt_exp.2 (by linarith)
  have hg : Summable fun k : ℕ => C * ((k : ℝ) + 2) * r ^ k := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0] : ‖r‖ < 1)
    have h2 := summable_geometric_of_lt_one hr0 hr1
    exact ((h1.add (h2.mul_left 2)).mul_left C).congr fun k => by simp only [pow_one]; ring
  have hC0 : 0 ≤ C := by
    have h := hC 0 le_rfl
    have : (0 : ℝ) ≤ cuspCount 0 := Nat.cast_nonneg _
    linarith
  refine summable_of_sum_le (fun i => (Real.exp_pos _).le) (c := ∑' k : ℕ, C * ((k : ℝ) + 2) * r ^ k)
    fun u => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (t := u.image fun i => ⌊i.1⌋₊) (g := fun i => ⌊i.1⌋₊)
    (fun i hi => Finset.mem_image_of_mem _ hi)]
  refine (Finset.sum_le_sum fun k _ => ?_).trans
    (hg.sum_le_tsum _ fun k _ => by positivity)
  have hle : ∀ i ∈ u.filter (fun i => ⌊i.1⌋₊ = k), Real.exp (-(t * i.1)) ≤ r ^ k := by
    intro i hi
    have hk := (Finset.mem_filter.1 hi).2
    have h0 : 0 ≤ i.1 := (one_quarter_le_cuspEigenBasis i).trans' (by norm_num)
    have hkl : (k : ℝ) ≤ i.1 := hk ▸ Nat.floor_le h0
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hcard : ((u.filter fun i => ⌊i.1⌋₊ = k).card : ℝ) ≤ C * ((k : ℝ) + 2) := by
    have hsub : (u.filter fun i => ⌊i.1⌋₊ = k) ⊆ (finite_cuspEigenIndex_le ((k : ℝ) + 1)).toFinset := by
      intro i hi
      have hk := (Finset.mem_filter.1 hi).2
      have h0 : 0 ≤ i.1 := (one_quarter_le_cuspEigenBasis i).trans' (by norm_num)
      rw [Set.Finite.mem_toFinset]
      have := Nat.lt_floor_add_one i.1
      rw [hk] at this
      exact this.le
    have h1 := Nat.cast_le (α := ℝ) |>.2 (Finset.card_le_card hsub)
    have h2 := hC ((k : ℝ) + 1) (by positivity)
    calc ((u.filter fun i => ⌊i.1⌋₊ = k).card : ℝ) ≤ cuspCount ((k : ℝ) + 1) := h1
      _ ≤ C * ((k : ℝ) + 1 + 1) := h2
      _ = C * ((k : ℝ) + 2) := by ring
  calc ∑ i ∈ u.filter (fun i => ⌊i.1⌋₊ = k), Real.exp (-(t * i.1))
      ≤ ∑ i ∈ u.filter (fun i => ⌊i.1⌋₊ = k), r ^ k := Finset.sum_le_sum hle
    _ = ((u.filter fun i => ⌊i.1⌋₊ = k).card : ℝ) * r ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * ((k : ℝ) + 2) * r ^ k := mul_le_mul_of_nonneg_right hcard (pow_nonneg hr0 _)

end WeylUpper

end GaloisForLFunctions.BlackHoleRingdown
