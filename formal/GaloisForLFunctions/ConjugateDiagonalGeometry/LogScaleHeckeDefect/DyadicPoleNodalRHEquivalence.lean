import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.PrimePolynomialSelfAbsorption
import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaPrefixCuspAndSectoriality
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit

/-!
# Dyadic Pole-Nodal Ordinate Selection and Unconditional Equivalence with `RiemannHypothesis`

While a single fixed logarithmic scale `L = c log T` cannot rule out finitely many low-lying
off-line zeros (`Theorem 2`), coupling a dyadic sequence of logarithmic scales
`L_k = 2^k c₀ log T` (`k ∈ ℕ`) with a single constant `C` across all `[T, T + 1)` (`T ≥ 2`) is
unconditionally equivalent to `RiemannHypothesis`:

1. **Low-ordinate zero exclusion** (`three_lt_abs_im_of_mem_zetaZeroConfig`):
   By `xi_re_ge_lowWindow`, every nontrivial zero `ρ ∈ zetaZeroConfig.carrier` satisfies
   `3 < |ρ.im|`, so any putative off-line zero has a conjugate partner `ρ₀` with `ρ₀.im > 3`
   residing inside `[T₀, T₀ + 1)` at `T₀ = ρ₀.im - 1/2 > 2`.

2. **Zero-avoiding subinterval in `[T₀, T₀ + 1]`** (`exists_zero_avoiding_subinterval_in_unitWindow`):
   Local finiteness of `zetaZeroConfig` on `[T₀ - 1, T₀ + 2]` partitions `[T₀, T₀ + 1]` into
   `card + 1` disjoint open slots, yielding `[a₀, b₀] ⊆ [T₀, T₀ + 1]` (`a₀ < b₀`) and `η₀ > 0`
   uniformly separated by `η₀` from all `ζ`-zero ordinates.

3. **Pole-nodal ordinate selection** (`exists_poleNodal_ordinate_in_Icc`):
   On `[a₀, b₀]` (`0 < a₀ < b₀`), for all sufficiently large `L`, evaluating the pole phase
   `e^{-2 i γ L} (tr (twist γ baseBump) 1 / (1/2 - iγ))²` along the explicit four-phase grid
   `2 γ L ∈ 2π ℤ + {0, π/2, π, 3π/2}` produces opposite signs of `Re((tr (twist γ F_L) 1)²)`,
   yielding `γ_L ∈ [a₀, b₀]` where the exponential `s = 0, 1` pole sum vanishes identically.

4. **Dyadic scale equivalence with `RiemannHypothesis`**
   (`riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial`,
    `riemannHypothesis_iff_forall_scale_heckeDefect_le_primePolynomial`,
    `riemannHypothesis_of_dyadic_heckeDefect_le_neg_re_primePolynomial`):
   For every `c₀ > 0` and `α ≥ 0`, `RiemannHypothesis` holds iff there exists `C` such that for all
   `k : ℕ`, `T ≥ 2`, and `γ ∈ [T, T + 1)`,
   `heckeDefect (baseTwistTest γ) (2^k c₀ log T) ≤ α ‖Π_{F_{2^k c₀ log T}}(-γ / 2π)‖ + C`
   (and across all `c > 0`, with signed converse from `-α Re Π_{F_{2^k c₀ log T}} + C`).
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Real ComplexConjugate ContDiff
open _root_.RHTower _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.ArithmeticOrientationGeometry
open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Unconditional low-ordinate exclusion and zero-avoiding subintervals -/

/-- Every nontrivial zero `ρ ∈ zetaZeroConfig.carrier` satisfies `3 < |ρ.im|`, proved via the
low-window sectorial positivity `xi_re_ge_lowWindow`. -/
theorem three_lt_abs_im_of_mem_zetaZeroConfig {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    3 < |ρ.im| := by
  obtain ⟨hxi, h0, h1⟩ :=
    CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ
  by_contra hle
  have him : |ρ.im| ≤ 61 / 20 := (not_lt.mp hle).trans (by norm_num)
  have hre : |ρ.re - 1 / 2| ≤ 9 / 8 := by
    rw [abs_le]; constructor <;> linarith
  have hpos_xi := xi_re_ge_lowWindow hre him
  rw [hxi, Complex.zero_re] at hpos_xi
  have hexp_pos : 0 < (5026 / 16875 : ℝ) * Real.exp (-Real.pi) := by positivity
  linarith

/-- Opaque finite set capturing all `ζ`-zeros in `(T₀ - 1, T₀ + 2]`. -/
private theorem exists_zeta_window_finset (T₀ : ℝ) :
    ∃ S : Finset ℂ, ∀ ρ : ℂ, ρ ∈ S ↔
      ρ ∈ zetaZeroConfig.carrier ∧ (T₀ - 1 < ρ.im ∧ ρ.im ≤ T₀ + 2) := by
  classical
  exact ⟨(zetaZeroConfig.finite_window (T₀ - 1) (T₀ + 2)).toFinset,
    fun _ => Set.Finite.mem_toFinset _⟩

/-- Pigeonhole construction of a nondegenerate subinterval `[a₀, b₀] ⊆ [T₀, T₀ + 1]` and
separation radius `η₀ > 0` uniformly avoiding every `ζ`-zero ordinate. -/
theorem exists_zero_avoiding_subinterval_in_unitWindow (T₀ : ℝ) :
    ∃ a₀ b₀ η₀ : ℝ,
      T₀ ≤ a₀ ∧ a₀ < b₀ ∧ b₀ ≤ T₀ + 1 ∧ 0 < η₀ ∧
      ∀ ρ ∈ zetaZeroConfig.carrier, ∀ γ ∈ Icc a₀ b₀, η₀ ≤ |ρ.im - γ| := by
  classical
  obtain ⟨S, hS_iff⟩ := exists_zeta_window_finset T₀
  set N_sub : ℕ := S.card + 1
  have hN_pos : 0 < (N_sub : ℝ) := by dsimp [N_sub]; positivity
  set η₀ : ℝ := 1 / (4 * (N_sub : ℝ))
  have hη₀_pos : 0 < η₀ := by dsimp [η₀]; positivity
  let slotMid : ℕ → ℝ := fun j => T₀ + (2 * (j : ℝ) + 1) / (2 * (N_sub : ℝ))
  -- At least one of the `N_sub = S.card + 1` disjoint open slots avoids `{z.im | z ∈ S}`
  have hex_slot : ∃ j₀ : Fin N_sub,
      ∀ z ∈ S, z.im ∉ Ioo (slotMid j₀.1 - 2 * η₀) (slotMid j₀.1 + 2 * η₀) := by
    by_contra hall
    have hall' : ∀ j : Fin N_sub,
        ∃ z ∈ S, z.im ∈ Ioo (slotMid j.1 - 2 * η₀) (slotMid j.1 + 2 * η₀) := by
      intro j
      by_contra hj
      exact hall ⟨j, fun z hz hmem => hj ⟨z, hz, hmem⟩⟩
    let f : Fin N_sub → {z // z ∈ S} := fun j =>
      ⟨(hall' j).choose, (hall' j).choose_spec.1⟩
    have hf_inj : Function.Injective f := by
      intro i j hij
      have him_eq : (f i).1.im = (f j).1.im := congrArg (fun x : {z // z ∈ S} => x.1.im) hij
      have hi_mem := (hall' i).choose_spec.2
      have hj_mem := (hall' j).choose_spec.2
      change (f i).1.im ∈ _ at hi_mem
      change (f j).1.im ∈ _ at hj_mem
      rw [← him_eq] at hj_mem
      by_contra hne
      have hval_ne : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
      have hleft_eq : ∀ k : ℕ, slotMid k - 2 * η₀ = T₀ + (k : ℝ) / (N_sub : ℝ) := fun k => by
        dsimp [slotMid, η₀]; field_simp; ring
      have hright_eq : ∀ k : ℕ, slotMid k + 2 * η₀ = T₀ + ((k : ℝ) + 1) / (N_sub : ℝ) := fun k => by
        dsimp [slotMid, η₀]; field_simp; ring
      rcases lt_or_gt_of_ne hval_ne with hlt | hgt
      · have hle_ij : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hlt)
        have hsep_ij : slotMid i.1 + 2 * η₀ ≤ slotMid j.1 - 2 * η₀ := by
          rw [hright_eq, hleft_eq]
          exact add_le_add le_rfl (div_le_div_of_nonneg_right hle_ij hN_pos.le)
        linarith [hi_mem.2, hj_mem.1]
      · have hle_ji : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hgt)
        have hsep_ji : slotMid j.1 + 2 * η₀ ≤ slotMid i.1 - 2 * η₀ := by
          rw [hright_eq, hleft_eq]
          exact add_le_add le_rfl (div_le_div_of_nonneg_right hle_ji hN_pos.le)
        linarith [hj_mem.2, hi_mem.1]
    have hcard := Fintype.card_le_of_injective f hf_inj
    rw [Fintype.card_fin, Fintype.card_coe] at hcard
    dsimp [N_sub] at hcard
    omega
  obtain ⟨j₀, hj₀⟩ := hex_slot
  set a₀ : ℝ := slotMid j₀.1 - η₀
  set b₀ : ℝ := slotMid j₀.1 + η₀
  have hT₀_le_a₀ : T₀ ≤ a₀ := by
    have : slotMid j₀.1 - 2 * η₀ = T₀ + (j₀.1 : ℝ) / (N_sub : ℝ) := by
      dsimp [slotMid, η₀]; field_simp; ring
    have hj_nn : 0 ≤ (j₀.1 : ℝ) / (N_sub : ℝ) := div_nonneg (Nat.cast_nonneg _) hN_pos.le
    dsimp [a₀]; linarith
  have hb₀_le_T₀1 : b₀ ≤ T₀ + 1 := by
    have : slotMid j₀.1 + 2 * η₀ = T₀ + ((j₀.1 : ℝ) + 1) / (N_sub : ℝ) := by
      dsimp [slotMid, η₀]; field_simp; ring
    have hj_le1 : ((j₀.1 : ℝ) + 1) / (N_sub : ℝ) ≤ 1 := by
      rw [div_le_one hN_pos]
      exact_mod_cast (Nat.succ_le_of_lt j₀.2)
    dsimp [b₀]; linarith
  refine ⟨a₀, b₀, η₀, hT₀_le_a₀, by dsimp [a₀, b₀]; linarith, hb₀_le_T₀1, hη₀_pos, ?_⟩
  intro ρ hρ γ hγ
  by_cases hρS : ρ ∈ S
  · have hnot := hj₀ ρ hρS
    rw [mem_Ioo, not_and_or] at hnot
    rcases hnot with hlo | hhi
    · have hle : ρ.im ≤ slotMid j₀.1 - 2 * η₀ := not_lt.mp hlo
      rw [abs_sub_comm]
      exact (by dsimp [a₀] at hγ; linarith [hγ.1] : η₀ ≤ γ - ρ.im).trans (le_abs_self _)
    · have hge : slotMid j₀.1 + 2 * η₀ ≤ ρ.im := not_lt.mp hhi
      exact (by dsimp [b₀] at hγ; linarith [hγ.2] : η₀ ≤ ρ.im - γ).trans (le_abs_self _)
  · -- `ρ ∉ S`: `ρ.im` lies outside `(T₀ - 1, T₀ + 2]`, while `γ ∈ [T₀, T₀ + 1]` and `η₀ ≤ 1`
    have hη_le1 : η₀ ≤ 1 := by
      dsimp [η₀]
      have : (1 : ℝ) ≤ 4 * (N_sub : ℝ) := by
        linarith [(by exact_mod_cast (Nat.succ_pos S.card) : (1 : ℝ) ≤ N_sub)]
      exact div_le_one_of_le₀ this (by positivity)
    have hwin : ¬ (T₀ - 1 < ρ.im ∧ ρ.im ≤ T₀ + 2) := fun hw =>
      hρS ((hS_iff ρ).mpr ⟨hρ, hw⟩)
    rw [not_and_or] at hwin
    rcases hwin with hle1 | hgt2
    · rw [abs_sub_comm]
      exact (by linarith [not_lt.mp hle1, hγ.1] : η₀ ≤ γ - ρ.im).trans (le_abs_self _)
    · exact (by linarith [not_le.mp hgt2, hγ.2] : η₀ ≤ ρ.im - γ).trans (le_abs_self _)

/-! ## §2. Pole-nodal ordinate selection on `[a₀, b₀]` -/

private theorem cos_and_sin_two_pi_mul_nat :
    ∀ m : ℕ, Real.cos (2 * Real.pi * (m : ℝ)) = 1 ∧ Real.sin (2 * Real.pi * (m : ℝ)) = 0
  | 0 => by simp
  | m + 1 => by
      obtain ⟨hc, hs⟩ := cos_and_sin_two_pi_mul_nat m
      have h : 2 * Real.pi * ((m + 1 : ℕ) : ℝ) = 2 * Real.pi * (m : ℝ) + 2 * Real.pi := by
        push_cast; ring
      rw [h, Real.cos_add_two_pi, Real.sin_add_two_pi]
      exact ⟨hc, hs⟩

/-- **Pole-nodal ordinate selection (`exists_poleNodal_ordinate_in_Icc`).**
On any nondegenerate positive interval `[a₀, b₀]` (`0 < a₀`, `a₀ < b₀`), there exists `L_min ≥ 1`
such that for every `L ≥ L_min`, there is an ordinate `γ_L ∈ [a₀, b₀]` where the `s = 0, 1` pole
contribution `2 * ((tr (twist γ_L (heckeAvgBump L)) 1) ^ 2).re` vanishes identically. -/
theorem exists_poleNodal_ordinate_in_Icc {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hab : a₀ < b₀) :
    ∃ L_min : ℝ, 1 ≤ L_min ∧ ∀ L : ℝ, L_min ≤ L →
      ∃ γ_L ∈ Icc a₀ b₀, ((tr (twist γ_L (heckeAvgBump L)) 1) ^ 2).re = 0 := by
  set γ₁ : ℝ := a₀
  by_cases hb0 : tr (twist γ₁ baseBump) 1 = 0
  · -- Degenerate case: `tr (twist γ₁ baseBump) 1 = 0` annihilates the pole at `γ₁` for all `L > 0`
    refine ⟨1, le_rfl, fun L hL1 => ⟨γ₁, ⟨le_rfl, hab.le⟩, ?_⟩⟩
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    rw [tr_twist_heckeAvgBump_eq hLpos γ₁ 1, hb0]
    simp
  · -- Nondegenerate case: `W(γ₁) = (tr (twist γ₁ baseBump) 1 / (1/2 - i γ₁))² ≠ 0`
    let z : ℝ → ℂ := fun γ => (1 : ℂ) - 1 / 2 - (γ : ℂ) * I
    have hz_ne : ∀ γ : ℝ, 0 < γ → z γ ≠ 0 := by
      intro γ hγ hz0
      have him := congrArg Complex.im hz0
      simp [z] at him
      linarith
    let W : ℝ → ℂ := fun γ => (tr (twist γ baseBump) 1 / z γ) ^ 2
    have hW1_ne : W γ₁ ≠ 0 :=
      pow_ne_zero 2 (div_ne_zero hb0 (hz_ne γ₁ ha₀))
    set r₁ : ℝ := ‖W γ₁‖
    have hr₁_pos : 0 < r₁ := norm_pos_iff.mpr hW1_ne
    -- Continuity of `W` at `γ₁`
    have hcont_b : Continuous (fun γ : ℝ => tr (twist γ baseBump) 1) :=
      continuous_tr_twist (contDiff_baseBump (n := ⊤)).continuous hasCompactSupport_baseBump 1
    have hcont_z : Continuous z :=
      continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)
    have hW_contAt : ContinuousAt W γ₁ :=
      (hcont_b.continuousAt.div hcont_z.continuousAt (hz_ne γ₁ ha₀)).pow 2
    obtain ⟨δ_raw, hδ_raw_pos, hδ_raw⟩ :=
      Metric.continuousAt_iff.mp hW_contAt (r₁ / 8) (by positivity)
    set δ₁ : ℝ := min ((b₀ - a₀) / 2) (δ_raw / 2)
    have hδ₁_pos : 0 < δ₁ := lt_min (by linarith) (by positivity)
    have hsub_Icc : Icc γ₁ (γ₁ + δ₁) ⊆ Icc a₀ b₀ := by
      intro γ hγ
      have hδ_le : δ₁ ≤ (b₀ - a₀) / 2 := min_le_left _ _
      exact ⟨hγ.1, by dsimp [γ₁] at hγ; linarith [hγ.2]⟩
    have hW_diff : ∀ γ ∈ Icc γ₁ (γ₁ + δ₁), ‖W γ - W γ₁‖ ≤ r₁ / 8 := by
      intro γ hγ
      have hlt : dist γ γ₁ < δ_raw := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hγ.1])]
        have : δ₁ ≤ δ_raw / 2 := min_le_right _ _
        linarith [hγ.2]
      exact (dist_eq_norm (W γ) (W γ₁) ▸ (hδ_raw hlt).le)
    have hW_norm : ∀ γ ∈ Icc γ₁ (γ₁ + δ₁), ‖W γ‖ ≤ 2 * r₁ := by
      intro γ hγ
      have hd := hW_diff γ hγ
      have htri := norm_add_le (W γ₁) (W γ - W γ₁)
      rw [add_sub_cancel] at htri
      change ‖W γ‖ ≤ r₁ + ‖W γ - W γ₁‖ at htri
      linarith [hr₁_pos]
    set L_min : ℝ := max 6 (4 * Real.pi / δ₁)
    have hLmin_ge1 : 1 ≤ L_min := le_trans (by norm_num) (le_max_left _ _)
    refine ⟨L_min, hLmin_ge1, fun L hL => ?_⟩
    have hL_ge6 : 6 ≤ L := (le_max_left _ _).trans hL
    have hL_δ : 4 * Real.pi / δ₁ ≤ L := (le_max_right _ _).trans hL
    have hLpos : 0 < L := by linarith
    -- Scaled real pole function `Φ(γ) = e^{-L} * Re((2 L * tr (twist γ F_L) 1)²)`
    let Φ : ℝ → ℝ := fun γ =>
      Real.exp (-L) * (((2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1) ^ 2).re
    -- Perturbation bound `|Φ(γ) - (u₁ cos(2γL) + v₁ sin(2γL))| ≤ r₁ / 4` on `Icc γ₁ (γ₁ + δ₁)`
    set u₁ : ℝ := (W γ₁).re
    set v₁ : ℝ := (W γ₁).im
    have huv_sq : u₁ ^ 2 + v₁ ^ 2 = r₁ ^ 2 := by
      have := Complex.normSq_eq_norm_sq (W γ₁)
      rw [Complex.normSq_apply] at this
      dsimp [u₁, v₁, r₁]; linarith
    have hΦ_approx : ∀ γ ∈ Icc γ₁ (γ₁ + δ₁),
        |Φ γ - (u₁ * Real.cos (2 * γ * L) + v₁ * Real.sin (2 * γ * L))| ≤ r₁ / 4 := by
      intro γ hγ
      have hγ_pos : 0 < γ := lt_of_lt_of_le ha₀ hγ.1
      have hzne := hz_ne γ hγ_pos
      -- Exact evaluation of `2 L * tr (twist γ F_L) 1`
      have htr_eq : (2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1 =
          (Complex.exp (z γ * (L : ℂ)) - Complex.exp (-(z γ * (L : ℂ)))) *
            (tr (twist γ baseBump) 1 / z γ) := by
        rw [tr_twist_heckeAvgBump_eq hLpos γ 1, intervalIntegral.integral_mul_const,
          show (1 : ℂ) - 1 / 2 - (γ : ℂ) * I = z γ from rfl,
          intervalIntegral_cexp_mul_eq_div hzne]
        have hL_ne_c : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
        push_cast
        field_simp
      set E_pos : ℂ := Complex.exp (((-(γ * L) : ℝ) : ℂ) * I)
      set E_neg : ℂ := Complex.exp (((γ * L : ℝ) : ℂ) * I)
      have hE_pos_norm : ‖E_pos‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      have hE_neg_norm : ‖E_neg‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      have hzL_pos : Complex.exp (z γ * (L : ℂ)) = ((Real.exp (L / 2) : ℝ) : ℂ) * E_pos := by
        have : z γ * (L : ℂ) = ((L / 2 : ℝ) : ℂ) + ((-(γ * L) : ℝ) : ℂ) * I := by
          dsimp [z]; push_cast; ring
        rw [this, Complex.exp_add, Complex.ofReal_exp]
      have hzL_neg : Complex.exp (-(z γ * (L : ℂ))) = ((Real.exp (-(L / 2)) : ℝ) : ℂ) * E_neg := by
        have : -(z γ * (L : ℂ)) = ((-(L / 2) : ℝ) : ℂ) + ((γ * L : ℝ) : ℂ) * I := by
          dsimp [z]; push_cast; ring
        rw [this, Complex.exp_add, Complex.ofReal_exp]
      -- Multiply square by `exp(-L)`
      have hsq_scaled : (((Real.exp (-L) : ℝ) : ℂ) *
          (((2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1) ^ 2)) =
          E_pos ^ 2 * W γ₁ +
            (E_pos ^ 2 * (W γ - W γ₁) +
              (-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
                ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2) * W γ) := by
        rw [htr_eq, mul_pow, hzL_pos, hzL_neg]
        have he1 : Real.exp (-L) * (Real.exp (L / 2) * Real.exp (L / 2)) = 1 := by
          rw [← Real.exp_add, ← Real.exp_add, show -L + (L / 2 + L / 2) = 0 by ring, Real.exp_zero]
        have he2 : Real.exp (-L) * (Real.exp (L / 2) * Real.exp (-(L / 2))) = Real.exp (-L) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        have he3 : Real.exp (-L) * (Real.exp (-(L / 2)) * Real.exp (-(L / 2))) = Real.exp (-(2 * L)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        dsimp [W]
        have hstep : (((Real.exp (-L) : ℝ) : ℂ) *
            ((((Real.exp (L / 2) : ℝ) : ℂ) * E_pos - ((Real.exp (-(L / 2)) : ℝ) : ℂ) * E_neg) ^ 2)) =
            E_pos ^ 2 - 2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
              ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2 := by
          have hc1 : ((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (L / 2) : ℝ) : ℂ)) = 1 := by
            exact_mod_cast he1
          have hc2 : ((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ)) =
              ((Real.exp (-L) : ℝ) : ℂ) := by
            exact_mod_cast he2
          have hc3 : ((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (-(L / 2)) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ)) =
              ((Real.exp (-(2 * L)) : ℝ) : ℂ) := by
            exact_mod_cast he3
          calc (((Real.exp (-L) : ℝ) : ℂ) *
                ((((Real.exp (L / 2) : ℝ) : ℂ) * E_pos - ((Real.exp (-(L / 2)) : ℝ) : ℂ) * E_neg) ^ 2))
              = (((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (L / 2) : ℝ) : ℂ))) * E_pos ^ 2 -
                  2 * (((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (L / 2) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ))) *
                    (E_pos * E_neg) +
                  (((Real.exp (-L) : ℝ) : ℂ) * (((Real.exp (-(L / 2)) : ℝ) : ℂ) * ((Real.exp (-(L / 2)) : ℝ) : ℂ))) *
                    E_neg ^ 2 := by ring
            _ = E_pos ^ 2 - 2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
                  ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2 := by
                rw [hc1, hc2, hc3, one_mul]
        rw [← mul_assoc, hstep]
        ring
      -- Lead real part `(E_pos^2 * W γ₁).re = u₁ cos(2γL) + v₁ sin(2γL)`
      have hlead_re : (E_pos ^ 2 * W γ₁).re = u₁ * Real.cos (2 * γ * L) + v₁ * Real.sin (2 * γ * L) := by
        have hE2 : E_pos ^ 2 = Complex.exp (((-(2 * γ * L) : ℝ) : ℂ) * I) := by
          dsimp [E_pos]; rw [sq, ← Complex.exp_add]; congr 1; push_cast; ring
        rw [hE2, Complex.exp_mul_I]
        simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.cos_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
          Complex.I_re, Complex.I_im, Real.cos_neg, Real.sin_neg]
        dsimp [u₁, v₁]
        ring
      -- Remainder norm `≤ r₁ / 4` since `L ≥ 6` (`exp(-L) ≤ 1 / 64 ≤ 1 / 48`)
      set Rem : ℂ := E_pos ^ 2 * (W γ - W γ₁) +
        (-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
          ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2) * W γ
      have hΦ_diff : Φ γ - (u₁ * Real.cos (2 * γ * L) + v₁ * Real.sin (2 * γ * L)) = Rem.re := by
        have hΦ_eq : Φ γ = (((Real.exp (-L) : ℝ) : ℂ) *
            (((2 * (L : ℂ)) * tr (twist γ (heckeAvgBump L)) 1) ^ 2)).re := by
          dsimp [Φ]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rw [hΦ_eq, hsq_scaled, Complex.add_re, hlead_re]
        ring
      rw [hΦ_diff]
      refine (Complex.abs_re_le_norm Rem).trans ?_
      have hexp_le : Real.exp (-L) ≤ 1 / 48 := by
        have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp 1
          linarith
        have h64 : (64 : ℝ) ≤ Real.exp L := by
          calc (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) := by norm_num
            _ ≤ (Real.exp 1) ^ (6 : ℕ) := pow_le_pow_left₀ zero_le_two h2_le_e 6
            _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
            _ ≤ Real.exp L := Real.exp_le_exp.mpr hL_ge6
        rw [Real.exp_neg]
        calc (Real.exp L)⁻¹ ≤ (64 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h64
          _ ≤ 1 / 48 := by norm_num
      have hexp2_le : Real.exp (-(2 * L)) ≤ Real.exp (-L) :=
        Real.exp_le_exp.mpr (by linarith)
      have hrem1 : ‖E_pos ^ 2 * (W γ - W γ₁)‖ ≤ r₁ / 8 := by
        rw [norm_mul, norm_pow, hE_pos_norm, one_pow, one_mul]
        exact hW_diff γ hγ
      have hrem2 : ‖(-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
          ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2) * W γ‖ ≤ r₁ / 8 := by
        rw [norm_mul]
        have h1 : ‖-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
            ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2‖ ≤ 3 * Real.exp (-L) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_neg, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), norm_mul, hE_pos_norm, hE_neg_norm, mul_one, mul_one,
            norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
            norm_pow, hE_neg_norm, one_pow, mul_one]
          linarith
        calc ‖-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
              ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2‖ * ‖W γ‖
            ≤ (3 * Real.exp (-L)) * (2 * r₁) :=
              mul_le_mul h1 (hW_norm γ hγ) (norm_nonneg _) (by positivity)
          _ = 6 * r₁ * Real.exp (-L) := by ring
          _ ≤ 6 * r₁ * (1 / 48) := mul_le_mul_of_nonneg_left hexp_le (by positivity)
          _ = r₁ / 8 := by ring
      calc ‖Rem‖ ≤ ‖E_pos ^ 2 * (W γ - W γ₁)‖ +
            ‖(-2 * ((Real.exp (-L) : ℝ) : ℂ) * (E_pos * E_neg) +
              ((Real.exp (-(2 * L)) : ℝ) : ℂ) * E_neg ^ 2) * W γ‖ := norm_add_le _ _
        _ ≤ r₁ / 8 + r₁ / 8 := add_le_add hrem1 hrem2
        _ = r₁ / 4 := by ring
    -- Four-phase grid `θ_j = 2πm + j π/2` (`j = 0, 1, 2, 3`) inside `[2 γ₁ L, 2 (γ₁ + δ₁) L]`
    set m : ℕ := ⌈γ₁ * L / Real.pi⌉₊
    have hπ_pos : 0 < Real.pi := Real.pi_pos
    have hm_ge : γ₁ * L / Real.pi ≤ (m : ℝ) := Nat.le_ceil _
    have hm_lt : (m : ℝ) < γ₁ * L / Real.pi + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (mul_nonneg ha₀.le hLpos.le) hπ_pos.le)
    have hθ_in_Icc : ∀ α_off : ℝ, 0 ≤ α_off → α_off ≤ 3 * Real.pi / 2 →
        (2 * Real.pi * (m : ℝ) + α_off) / (2 * L) ∈ Icc γ₁ (γ₁ + δ₁) := by
      intro α_off hα0 hα3
      constructor
      · rw [le_div_iff₀ (by positivity)]
        have : 2 * γ₁ * L ≤ 2 * Real.pi * (m : ℝ) := by
          have := (div_le_iff₀ hπ_pos).mp hm_ge
          linarith
        linarith
      · rw [div_le_iff₀ (by positivity)]
        have h2πm : 2 * Real.pi * (m : ℝ) < 2 * γ₁ * L + 2 * Real.pi := by
          have := (lt_div_iff₀' hπ_pos).mp (by linarith : (m : ℝ) - 1 < γ₁ * L / Real.pi)
          linarith
        have h4π_le : 4 * Real.pi ≤ L * δ₁ := (div_le_iff₀ hδ₁_pos).mp hL_δ
        nlinarith [hπ_pos]
    obtain ⟨hcos_m, hsin_m⟩ := cos_and_sin_two_pi_mul_nat m
    let g_lead : ℝ → ℝ := fun θ => u₁ * Real.cos θ + v₁ * Real.sin θ
    have hg0 : g_lead (2 * Real.pi * (m : ℝ) + 0) = u₁ := by
      dsimp [g_lead]; rw [add_zero, hcos_m, hsin_m]; ring
    have hg1 : g_lead (2 * Real.pi * (m : ℝ) + Real.pi / 2) = v₁ := by
      dsimp [g_lead]
      rw [Real.cos_add, Real.sin_add, hcos_m, hsin_m, Real.cos_pi_div_two, Real.sin_pi_div_two]
      ring
    have hg2 : g_lead (2 * Real.pi * (m : ℝ) + Real.pi) = -u₁ := by
      dsimp [g_lead]
      rw [Real.cos_add, Real.sin_add, hcos_m, hsin_m, Real.cos_pi, Real.sin_pi]
      ring
    have hg3 : g_lead (2 * Real.pi * (m : ℝ) + 3 * Real.pi / 2) = -v₁ := by
      set θ₁ : ℝ := 2 * Real.pi * (m : ℝ) + Real.pi / 2
      have h32 : 2 * Real.pi * (m : ℝ) + 3 * Real.pi / 2 = θ₁ + Real.pi := by
        dsimp [θ₁]; ring
      rw [h32]
      dsimp [g_lead] at hg1 ⊢
      rw [Real.cos_add θ₁ Real.pi, Real.sin_add θ₁ Real.pi, Real.cos_pi, Real.sin_pi]
      linarith [hg1]
    -- Either `r₁ / 2 ≤ |u₁|` or `r₁ / 2 ≤ |v₁|`
    have hmax_uv : r₁ / 2 ≤ |u₁| ∨ r₁ / 2 ≤ |v₁| := by
      by_contra hnot
      rw [not_or] at hnot
      have hu2 : u₁ ^ 2 < (r₁ / 2) ^ 2 := by
        rw [← sq_abs u₁]
        exact pow_lt_pow_left₀ (not_le.mp hnot.1) (abs_nonneg _) (by norm_num)
      have hv2 : v₁ ^ 2 < (r₁ / 2) ^ 2 := by
        rw [← sq_abs v₁]
        exact pow_lt_pow_left₀ (not_le.mp hnot.2) (abs_nonneg _) (by norm_num)
      nlinarith [huv_sq, hr₁_pos]
    -- Construct `γ_pos, γ_neg ∈ Icc γ₁ (γ₁ + δ₁)` with `g_lead(2 γ_pos L) ≥ r₁ / 2` and
    -- `g_lead(2 γ_neg L) ≤ -r₁ / 2`
    have hex_pm : ∃ γ_pos γ_neg : ℝ,
        γ_pos ∈ Icc γ₁ (γ₁ + δ₁) ∧ γ_neg ∈ Icc γ₁ (γ₁ + δ₁) ∧
        r₁ / 2 ≤ g_lead (2 * γ_pos * L) ∧ g_lead (2 * γ_neg * L) ≤ -r₁ / 2 := by
      have hmul_div : ∀ θ : ℝ, 2 * (θ / (2 * L)) * L = θ := fun θ => by
        have := hLpos.ne'; field_simp
      rcases hmax_uv with hu | hv
      · rcases le_or_gt 0 u₁ with hu0 | hu_neg
        · rw [abs_of_nonneg hu0] at hu
          refine ⟨(2 * Real.pi * (m : ℝ) + 0) / (2 * L),
            (2 * Real.pi * (m : ℝ) + Real.pi) / (2 * L),
            hθ_in_Icc 0 le_rfl (by positivity),
            hθ_in_Icc Real.pi hπ_pos.le (by linarith), ?_, ?_⟩ <;>
            rw [hmul_div]
          · rw [hg0]; exact hu
          · rw [hg2]; linarith
        · rw [abs_of_neg hu_neg] at hu
          refine ⟨(2 * Real.pi * (m : ℝ) + Real.pi) / (2 * L),
            (2 * Real.pi * (m : ℝ) + 0) / (2 * L),
            hθ_in_Icc Real.pi hπ_pos.le (by linarith),
            hθ_in_Icc 0 le_rfl (by positivity), ?_, ?_⟩ <;>
            rw [hmul_div]
          · rw [hg2]; linarith
          · rw [hg0]; linarith
      · rcases le_or_gt 0 v₁ with hv0 | hv_neg
        · rw [abs_of_nonneg hv0] at hv
          refine ⟨(2 * Real.pi * (m : ℝ) + Real.pi / 2) / (2 * L),
            (2 * Real.pi * (m : ℝ) + 3 * Real.pi / 2) / (2 * L),
            hθ_in_Icc (Real.pi / 2) (by positivity) (by linarith),
            hθ_in_Icc (3 * Real.pi / 2) (by positivity) le_rfl, ?_, ?_⟩ <;>
            rw [hmul_div]
          · rw [hg1]; exact hv
          · rw [hg3]; linarith
        · rw [abs_of_neg hv_neg] at hv
          refine ⟨(2 * Real.pi * (m : ℝ) + 3 * Real.pi / 2) / (2 * L),
            (2 * Real.pi * (m : ℝ) + Real.pi / 2) / (2 * L),
            hθ_in_Icc (3 * Real.pi / 2) (by positivity) le_rfl,
            hθ_in_Icc (Real.pi / 2) (by positivity) (by linarith), ?_, ?_⟩ <;>
            rw [hmul_div]
          · rw [hg3]; linarith
          · rw [hg1]; linarith
    obtain ⟨γ_pos, γ_neg, hγp_mem, hγn_mem, hlead_p, hlead_n⟩ := hex_pm
    have hΦ_pos : 0 ≤ Φ γ_pos := by
      have happ := (abs_le.mp (hΦ_approx γ_pos hγp_mem)).1
      dsimp [g_lead] at hlead_p
      linarith
    have hΦ_neg : Φ γ_neg ≤ 0 := by
      have happ := (abs_le.mp (hΦ_approx γ_neg hγn_mem)).2
      dsimp [g_lead] at hlead_n
      linarith
    -- Continuity of `Φ` and intermediate value theorem between `γ_pos` and `γ_neg`
    have hcont_Φ : Continuous Φ :=
      continuous_const.mul (Complex.continuous_re.comp
        ((continuous_const.mul (continuous_tr_twist (contDiff_heckeAvgBump L).continuous
          (hasCompactSupport_heckeAvgBump hLpos) 1)).pow 2))
    have hex_zero : ∃ γ_L ∈ Icc γ₁ (γ₁ + δ₁), Φ γ_L = 0 := by
      rcases le_total γ_pos γ_neg with hle | hle
      · obtain ⟨γ_L, hγL_in, hΦ0⟩ := intermediate_value_Icc' hle hcont_Φ.continuousOn
          ⟨hΦ_neg, hΦ_pos⟩
        exact ⟨γ_L, ⟨hγp_mem.1.trans hγL_in.1, hγL_in.2.trans hγn_mem.2⟩, hΦ0⟩
      · obtain ⟨γ_L, hγL_in, hΦ0⟩ := intermediate_value_Icc hle hcont_Φ.continuousOn
          ⟨hΦ_neg, hΦ_pos⟩
        exact ⟨γ_L, ⟨hγn_mem.1.trans hγL_in.1, hγL_in.2.trans hγp_mem.2⟩, hΦ0⟩
    obtain ⟨γ_L, hγL_sub, hΦ0⟩ := hex_zero
    refine ⟨γ_L, hsub_Icc hγL_sub, ?_⟩
    -- Since `Φ γ_L = exp(-L) * (4 L^2) * ((tr (twist γ_L F_L) 1)^2).re = 0` and `4 L^2 exp(-L) > 0`
    have hΦ_unfold : Φ γ_L =
        Real.exp (-L) * (4 * L ^ 2 * ((tr (twist γ_L (heckeAvgBump L)) 1) ^ 2).re) := by
      dsimp [Φ]
      congr 1
      have hsq : ((2 * (L : ℂ)) * tr (twist γ_L (heckeAvgBump L)) 1) ^ 2 =
          (((4 * L ^ 2 : ℝ) : ℂ)) * (tr (twist γ_L (heckeAvgBump L)) 1) ^ 2 := by
        push_cast; ring
      rw [hsq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hΦ_unfold] at hΦ0
    have hexp_ne : Real.exp (-L) ≠ 0 := (Real.exp_pos _).ne'
    have h4L_ne : 4 * L ^ 2 ≠ 0 := by positivity
    have h1 := (mul_eq_zero.mp hΦ0).resolve_left hexp_ne
    exact (mul_eq_zero.mp h1).resolve_left h4L_ne

/-! ## §3. Theorem 4 — Dyadic log-scale equivalence with `RiemannHypothesis` -/

/-- Under `RiemannHypothesis`, `heckeDefect (baseTwistTest γ) L = 0` identically for all `γ, L ∈ ℝ`. -/
theorem heckeDefect_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) (γ L : ℝ) :
    heckeDefect (baseTwistTest γ) L = 0 := by
  have hon := CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
  unfold heckeDefect
  refine Eq.trans (tsum_congr fun ρ => ?_) tsum_zero
  have hre : (ρ : ℂ).re = 1 / 2 := hon (ρ : ℂ) ρ.2
  have hd0 : zetaDepth ρ = 0 := by simp [zetaDepth, hre]
  rw [hd0, depthKernel_zero_depth, mul_zero]

/-- **Theorem 4a (`riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial` — Unconditional
Dyadic Log-Scale Equivalence with `RiemannHypothesis`).**
For EVERY `c₀ > 0` and EVERY `α ≥ 0`, `RiemannHypothesis` holds IF AND ONLY IF there exists an
additive constant `C ∈ ℝ` such that across the dyadic scales `L_k = 2^k * c₀ * log T` (`k ∈ ℕ`),
for all `T ≥ 2` and all `γ ∈ [T, T + 1)`,
`heckeDefect (baseTwistTest γ) (2^k * c₀ * log T) ≤ α * ‖primePolynomial (heckeAvgBump (2^k * c₀ * log T)) N*(2^k * c₀ * log T) (-γ / 2π)‖ + C`. -/
theorem riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial {c₀ α : ℝ}
    (hc₀ : 0 < c₀) (hα : 0 ≤ α) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
        heckeDefect (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) ≤
          α * ‖primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
            ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ + C := by
  constructor
  · intro hRH
    refine ⟨0, fun k T _ γ _ => ?_⟩
    rw [heckeDefect_eq_zero_of_riemannHypothesis hRH, add_zero]
    exact mul_nonneg hα (norm_nonneg _)
  · rintro ⟨C, hdyad⟩
    rw [CrossRouteReceiverBridges.riemannHypothesis_iff_zetaZeroConfig_onLine]
    by_contra hnot_on
    have hex_raw : ∃ ρ_raw ∈ zetaZeroConfig.carrier, ρ_raw.re ≠ 1 / 2 := by
      by_contra hall
      exact hnot_on fun ρ hρ => by_contra fun hne => hall ⟨ρ, hρ, hne⟩
    obtain ⟨ρ_raw, hρ_raw, hre_raw⟩ := hex_raw
    -- Conjugate if needed to obtain an off-line zero `ρ₀` with `ρ₀.im > 3`
    have hex_pos : ∃ ρ₀ ∈ zetaZeroConfig.carrier, ρ₀.re ≠ 1 / 2 ∧ 3 < ρ₀.im := by
      have habs := three_lt_abs_im_of_mem_zetaZeroConfig hρ_raw
      rcases le_or_gt 0 ρ_raw.im with him0 | him_neg
      · rw [abs_of_nonneg him0] at habs
        exact ⟨ρ_raw, hρ_raw, hre_raw, habs⟩
      · rw [abs_of_neg him_neg] at habs
        refine ⟨conj ρ_raw, conj_mem_zetaZeroConfig hρ_raw, ?_, ?_⟩
        · simpa only [Complex.conj_re] using hre_raw
        · simp only [Complex.conj_im]; linarith
    obtain ⟨ρ₀, hρ₀_mem, hρ₀_re, hρ₀_im3⟩ := hex_pos
    set δ₀ : ℝ := |ρ₀.re - 1 / 2|
    have hδ₀_pos : 0 < δ₀ := abs_pos.mpr (sub_ne_zero.mpr hρ₀_re)
    set T₀ : ℝ := ρ₀.im - 1 / 2
    have hT₀_ge2 : 2 ≤ T₀ := by dsimp [T₀]; linarith
    have hlogT₀_pos : 0 < Real.log T₀ := Real.log_pos (by linarith)
    -- `ρ₀ ∈ xiUnitWindowZeros T₀`
    obtain ⟨hxi₀, h0₀, h1₀⟩ :=
      CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ₀_mem
    have hρ₀_W : ρ₀ ∈ xiUnitWindowZeros T₀ := by
      rw [mem_xiUnitWindowZeros]
      exact ⟨(Set.Finite.mem_toFinset _).mpr
        ⟨⟨h0₀, h1₀, by linarith, by dsimp [T₀]; linarith⟩, hxi₀⟩, by dsimp [T₀]; linarith⟩
    have hord₀_ge1 : (1 : ℝ) ≤ ((analyticOrderAt xi ρ₀).toNat : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hxi₀)
    -- Select zero-avoiding `[a₀, b₀] ⊆ [T₀, T₀ + 1]` and pole-nodal threshold `L_min`
    obtain ⟨a₀, b₀, η₀, hT₀_a₀, ha₀_b₀, hb₀_T₀1, hη₀_pos, hsep_all⟩ :=
      exists_zero_avoiding_subinterval_in_unitWindow T₀
    obtain ⟨L_min, hLmin1, hpole_nodal⟩ :=
      exists_poleNodal_ordinate_in_Icc (by linarith : 0 < a₀) ha₀_b₀
    obtain ⟨C_mu, hCmu, hmu_bd⟩ := exists_abs_re_archPart_sub_pole_heckeAvgBump_le
    obtain ⟨C_lor, hClor, hlor⟩ := exists_zetaZeroConfig_lorentz_le
    -- Uniform constants on `[a₀, b₀] ⊆ [T₀, T₀ + 1]`
    set C_arch_nodal : ℝ := C_mu + Real.log (3 + T₀)
    set C_lor_T₀ : ℝ := (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) * (C_lor * (1 + Real.log (T₀ + 5)))
    have hCarn_pos : 0 < C_arch_nodal := by
      have : 0 ≤ Real.log (3 + T₀) := Real.log_nonneg (by linarith)
      dsimp [C_arch_nodal]; linarith
    have hClorT_pos : 0 < C_lor_T₀ := by
      have : 0 ≤ Real.log (T₀ + 5) := Real.log_nonneg (by linarith)
      dsimp [C_lor_T₀]; positivity
    -- Choose `k : ℕ` so `L_k = 2^k * c₀ * log T₀` exceeds all three thresholds simultaneously
    have htend_L : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * c₀ * Real.log T₀) atTop atTop := by
      have h1 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * (c₀ * Real.log T₀)) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const
          (mul_pos hc₀ hlogT₀_pos)
      exact h1.congr fun k => (mul_assoc _ _ _).symm
    set M_rhs : ℝ := α * (C_arch_nodal + C_lor_T₀) + |C| + 1
    have hM_nn : 0 ≤ M_rhs := by
      dsimp [M_rhs]
      nlinarith [hCarn_pos, hClorT_pos, abs_nonneg C]
    have hcos_pos := cos_quarter_sq_pos
    set L_target : ℝ := max L_min
      (max (Real.sqrt (α / (2 * η₀ ^ 2)) + 1)
        (Real.sqrt (M_rhs / (2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)) + 1))
    obtain ⟨k, hk⟩ := (htend_L.eventually_ge_atTop L_target).exists
    set L_k : ℝ := (2 : ℝ) ^ k * c₀ * Real.log T₀
    have hLk_ge_target : L_target ≤ L_k := hk
    have hLk_ge_min : L_min ≤ L_k := (le_max_left _ _).trans hLk_ge_target
    have hLk_ge1 : 1 ≤ L_k := hLmin1.trans hLk_ge_min
    have hLk_pos : 0 < L_k := lt_of_lt_of_le one_pos hLk_ge1
    -- Select pole-nodal ordinate `γ_k ∈ [a₀, b₀] ⊆ [T₀, T₀ + 1]` at scale `L_k`
    obtain ⟨γ_k, hγk_ab, hpole0⟩ := hpole_nodal L_k hLk_ge_min
    have hγk_Icc : γ_k ∈ Icc T₀ (T₀ + 1) := ⟨hT₀_a₀.trans hγk_ab.1, hγk_ab.2.trans hb₀_T₀1⟩
    -- 1. Archimedean bound at `γ_k`: pole term vanishes identically!
    have harch_k : |(archPart (heckeAvgBump L_k) (-γ_k / (2 * Real.pi))).re| ≤ C_arch_nodal := by
      have hsub := hmu_bd L_k γ_k hLk_ge1
      rw [hpole0, mul_zero, sub_zero] at hsub
      have habs_γk : |γ_k| = γ_k := abs_of_pos (by linarith [hγk_Icc.1])
      have hlog_le : Real.log (2 + |γ_k|) / (2 * L_k) ≤ Real.log (3 + T₀) := by
        rw [habs_γk]
        have h1 : Real.log (2 + γ_k) ≤ Real.log (3 + T₀) :=
          Real.log_le_log (by linarith [hγk_Icc.1]) (by linarith [hγk_Icc.2])
        calc Real.log (2 + γ_k) / (2 * L_k)
            ≤ Real.log (2 + γ_k) :=
              div_le_self (Real.log_nonneg (by linarith [hγk_Icc.1])) (by linarith)
          _ ≤ Real.log (3 + T₀) := h1
      dsimp [C_arch_nodal]; linarith
    -- 2. Collided-form bound at `γ_k` via `normSq_tr_twist_heckeAvgBump_le_of_sep` on ALL zeros
    have hcoll_k : collidedForm zetaZeroConfig (twist γ_k (heckeAvgBump L_k)) ≤
        C_lor_T₀ + (1 / (4 * η₀ ^ 2 * L_k ^ 2)) * heckeDefect (baseTwistTest γ_k) L_k := by
      have hs_coll := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L_k) γ_k)
        (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLk_pos) γ_k)
      have hlor_sum := (hlor γ_k).1
      have hdef_sum := summable_heckeDefect (baseTwistTest γ_k) L_k
      set c₁ : ℝ := (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L_k ^ 2
      set c₂ : ℝ := 1 / (4 * η₀ ^ 2 * L_k ^ 2)
      have hptw : ∀ ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k (heckeAvgBump L_k)) ρ) ≤
            c₁ * ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2))) +
              c₂ * (zetaWeight (baseTwistTest γ_k) ρ * depthKernel L_k (zetaDepth ρ)) := by
        intro ρ
        have hsep := hsep_all (ρ : ℂ) ρ.2 γ_k hγk_ab
        have hbd := normSq_tr_twist_heckeAvgBump_le_of_sep hLk_pos hη₀_pos γ_k ρ hsep
        have hm0 : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
        have hw_eq : zetaWeight (baseTwistTest γ_k) ρ =
            (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k baseBump) ρ) := rfl
        rw [hw_eq, show c₁ = (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L_k ^ 2 from rfl,
          show c₂ = 1 / (4 * η₀ ^ 2 * L_k ^ 2) from rfl]
        calc (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k (heckeAvgBump L_k)) ρ)
            ≤ (zetaZeroConfig.mult ρ : ℝ) *
                ((1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) / L_k ^ 2 * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2)) +
                  1 / (4 * η₀ ^ 2 * L_k ^ 2) *
                    (Complex.normSq (tr (twist γ_k baseBump) ρ) * depthKernel L_k (zetaDepth ρ))) :=
              mul_le_mul_of_nonneg_left hbd hm0
          _ = _ := by ring
      have htsum := hs_coll.tsum_le_tsum hptw ((hlor_sum.mul_left c₁).add (hdef_sum.mul_left c₂))
      rw [(hlor_sum.mul_left c₁).tsum_add (hdef_sum.mul_left c₂), tsum_mul_left, tsum_mul_left]
        at htsum
      have hlor_le : c₁ * (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2))) ≤ C_lor_T₀ := by
        have h1 : c₁ ≤ (1 + η₀⁻¹ ^ 2) * Real.exp (1 / 4) := by
          dsimp [c₁]
          exact div_le_self (by positivity) (by nlinarith : 1 ≤ L_k ^ 2)
        have habs_γk : |γ_k| = γ_k := abs_of_pos (by linarith [hγk_Icc.1])
        have h2 : (∑' ρ : zetaZeroConfig.carrier,
            (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ_k - (ρ : ℂ).im) ^ 2))) ≤
            C_lor * (1 + Real.log (T₀ + 5)) := by
          refine (hlor γ_k).2.trans (mul_le_mul_of_nonneg_left ?_ hClor.le)
          have : Real.log (|γ_k| + 4) ≤ Real.log (T₀ + 5) := by
            rw [habs_γk]
            exact Real.log_le_log (by linarith [hγk_Icc.1]) (by linarith [hγk_Icc.2])
          linarith
        dsimp [C_lor_T₀]
        exact mul_le_mul h1 h2
          (tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))
          (by positivity)
      have hcoll_def : (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) * Complex.normSq (tr (twist γ_k (heckeAvgBump L_k)) ρ)) =
          collidedForm zetaZeroConfig (twist γ_k (heckeAvgBump L_k)) := rfl
      have hdef_eq : (∑' ρ : zetaZeroConfig.carrier,
          zetaWeight (baseTwistTest γ_k) ρ * depthKernel L_k (zetaDepth ρ)) =
          heckeDefect (baseTwistTest γ_k) L_k := rfl
      rw [hcoll_def, hdef_eq, show c₂ = 1 / (4 * η₀ ^ 2 * L_k ^ 2) from rfl] at htsum
      linarith [htsum, hlor_le]
    -- 3. Combine dyadic hypothesis at `(k, T₀, γ_k)` with `norm_primePolynomial_heckeAvgBump_le`
    have hhyp_k := hdyad k T₀ hT₀_ge2 γ_k hγk_Icc
    have hpp_k := norm_primePolynomial_heckeAvgBump_le hLk_pos γ_k
    have hLk_abs : α / (4 * η₀ ^ 2 * L_k ^ 2) ≤ 1 / 2 := by
      have hge_sq : Real.sqrt (α / (2 * η₀ ^ 2)) < L_k := by
        have := (le_max_left _ _).trans ((le_max_right _ _).trans hLk_ge_target)
        linarith
      have hsq : α / (2 * η₀ ^ 2) ≤ L_k ^ 2 := by
        have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hge_sq.le 2
        rwa [Real.sq_sqrt (by positivity)] at h1
      rw [div_le_div_iff₀ (by positivity) zero_lt_two]
      have := (div_le_iff₀ (by positivity : 0 < 2 * η₀ ^ 2)).mp hsq
      linarith
    set E_k := heckeDefect (baseTwistTest γ_k) L_k
    have hEk_nn : 0 ≤ E_k := heckeDefect_nonneg _ _
    have hEk_upper : (1 / 2) * E_k ≤ α * (C_arch_nodal + C_lor_T₀) + |C| := by
      have h1 : E_k ≤ α * (C_arch_nodal + C_lor_T₀ + (1 / (4 * η₀ ^ 2 * L_k ^ 2)) * E_k) + |C| := by
        have hpp_tot : ‖primePolynomial (heckeAvgBump L_k)
            ⌊Real.exp (2 * (L_k + 1 / 4))⌋₊ (-γ_k / (2 * Real.pi))‖ ≤
            C_arch_nodal + C_lor_T₀ + (1 / (4 * η₀ ^ 2 * L_k ^ 2)) * E_k := by
          linarith [hpp_k, harch_k, hcoll_k]
        calc E_k ≤ α * ‖primePolynomial (heckeAvgBump L_k)
              ⌊Real.exp (2 * (L_k + 1 / 4))⌋₊ (-γ_k / (2 * Real.pi))‖ + C := hhyp_k
          _ ≤ α * (C_arch_nodal + C_lor_T₀ + (1 / (4 * η₀ ^ 2 * L_k ^ 2)) * E_k) + |C| :=
              add_le_add (mul_le_mul_of_nonneg_left hpp_tot hα) (le_abs_self C)
      have h2 : α * ((1 / (4 * η₀ ^ 2 * L_k ^ 2)) * E_k) ≤ (1 / 2) * E_k := by
        rw [← mul_assoc, mul_one_div]
        exact mul_le_mul_of_nonneg_right hLk_abs hEk_nn
      linarith
    -- 4. Lower bound `(1 / 2) * E_k` from `ρ₀ ∈ xiUnitWindowZeros T₀` and contradict `hEk_upper`
    have hEk_lower : 2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2 * L_k ^ 2 ≤ (1 / 2) * E_k := by
      have hunit := unitWindow_depthCharge_le_heckeDefect T₀ L_k hγk_Icc.1 hγk_Icc.2
      have hsingle : ((analyticOrderAt xi ρ₀).toNat : ℝ) * depthKernel L_k (ρ₀.re - 1 / 2) ≤
          ∑ ρ ∈ xiUnitWindowZeros T₀,
            ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2) :=
        Finset.single_le_sum
          (f := fun ρ => ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2))
          (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (depthKernel_nonneg _ _)) hρ₀_W
      have hquad : 4 * L_k ^ 2 * δ₀ ^ 2 ≤ depthKernel L_k (ρ₀.re - 1 / 2) := by
        have h1 := quadratic_le_depthKernel L_k (ρ₀.re - 1 / 2)
        have h2 : δ₀ ^ 2 = (ρ₀.re - 1 / 2) ^ 2 := sq_abs _
        rwa [← h2] at h1
      have hdk_le_ord : depthKernel L_k (ρ₀.re - 1 / 2) ≤
          ((analyticOrderAt xi ρ₀).toNat : ℝ) * depthKernel L_k (ρ₀.re - 1 / 2) :=
        le_mul_of_one_le_left (depthKernel_nonneg _ _) hord₀_ge1
      have hchain : Real.cos (1 / 4 : ℝ) ^ 2 * (4 * L_k ^ 2 * δ₀ ^ 2) ≤ E_k := by
        calc Real.cos (1 / 4 : ℝ) ^ 2 * (4 * L_k ^ 2 * δ₀ ^ 2)
            ≤ Real.cos (1 / 4 : ℝ) ^ 2 *
                ∑ ρ ∈ xiUnitWindowZeros T₀,
                  ((analyticOrderAt xi ρ).toNat : ℝ) * depthKernel L_k (ρ.re - 1 / 2) :=
              mul_le_mul_of_nonneg_left (hquad.trans (hdk_le_ord.trans hsingle)) hcos_pos.le
          _ ≤ E_k := hunit
      linarith
    have hLk_grow : M_rhs < 2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2 * L_k ^ 2 := by
      have hgt_sq : Real.sqrt (M_rhs / (2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)) < L_k := by
        have := (le_max_right _ _).trans ((le_max_right _ _).trans hLk_ge_target)
        linarith
      have hsq : M_rhs / (2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2) < L_k ^ 2 := by
        have h1 := pow_lt_pow_left₀ hgt_sq (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)
        rwa [Real.sq_sqrt (div_nonneg hM_nn (by positivity))] at h1
      have hmul := (div_lt_iff₀ (by positivity : 0 < 2 * Real.cos (1 / 4 : ℝ) ^ 2 * δ₀ ^ 2)).mp hsq
      linarith
    dsimp [M_rhs] at hLk_grow
    linarith

/-- **Theorem 4b (`riemannHypothesis_of_dyadic_heckeDefect_le_neg_re_primePolynomial`).**
Signed dyadic converse: if a single constant `C` bounds
`heckeDefect (baseTwistTest γ) (2^k c₀ log T) ≤ -α Re Π_{F_{2^k c₀ log T}}(-γ / 2π) + C` across
all `k ∈ ℕ`, `T ≥ 2`, `γ ∈ [T, T + 1)`, then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_dyadic_heckeDefect_le_neg_re_primePolynomial {c₀ α : ℝ}
    (hc₀ : 0 < c₀) (hα : 0 ≤ α)
    (hhyp : ∃ C : ℝ, ∀ (k : ℕ) (T : ℝ), 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
      heckeDefect (baseTwistTest γ) ((2 : ℝ) ^ k * c₀ * Real.log T) ≤
        -α * (primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
          ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))).re + C) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial hc₀ hα]
  obtain ⟨C, hC⟩ := hhyp
  refine ⟨C, fun k T hT γ hγ => (hC k T hT γ hγ).trans ?_⟩
  set z := primePolynomial (heckeAvgBump ((2 : ℝ) ^ k * c₀ * Real.log T))
    ⌊Real.exp (2 * ((2 : ℝ) ^ k * c₀ * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))
  have hle : -z.re ≤ ‖z‖ := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
  linarith [mul_le_mul_of_nonneg_left hle hα]

/-- **Theorem 4c (`riemannHypothesis_iff_forall_scale_heckeDefect_le_primePolynomial`).**
Scale-uniform equivalence across `(0, ∞)`: for every `α ≥ 0`, `RiemannHypothesis` holds iff there
exists a constant `C` independent of `c > 0` such that for all `c > 0`, `T ≥ 2`, and
`γ ∈ [T, T + 1)`, `E_γ(c log T) ≤ α ‖Π_{F_{c log T}}(-γ / 2π)‖ + C`. -/
theorem riemannHypothesis_iff_forall_scale_heckeDefect_le_primePolynomial {α : ℝ} (hα : 0 ≤ α) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ (c : ℝ), 0 < c → ∀ (T : ℝ), 2 ≤ T → ∀ γ ∈ Icc T (T + 1),
        heckeDefect (baseTwistTest γ) (c * Real.log T) ≤
          α * ‖primePolynomial (heckeAvgBump (c * Real.log T))
            ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ + C := by
  constructor
  · intro hRH
    refine ⟨0, fun c _ T _ γ _ => ?_⟩
    rw [heckeDefect_eq_zero_of_riemannHypothesis hRH, add_zero]
    exact mul_nonneg hα (norm_nonneg _)
  · rintro ⟨C, hall⟩
    rw [riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial one_pos hα]
    exact ⟨C, fun k T hT γ hγ => by
      simpa only [mul_one] using hall ((2 : ℝ) ^ k) (by positivity) T hT γ hγ⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.three_lt_abs_im_of_mem_zetaZeroConfig
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_zero_avoiding_subinterval_in_unitWindow
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_poleNodal_ordinate_in_Icc
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_iff_dyadic_heckeDefect_le_primePolynomial
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_of_dyadic_heckeDefect_le_neg_re_primePolynomial
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.riemannHypothesis_iff_forall_scale_heckeDefect_le_primePolynomial
