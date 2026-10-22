import GaloisForLFunctions.SquareRootThreshold.FejerLagWindowCubicPotentialLaw
import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity

/-!
# Lag positivity forces close companions for `ζ`

Let `φ(v) = 2 Re S(v) = Σ_z D(z) e^{zv}` be the lag function of `ζ` for a width `w`, so that
`P_v = φ(0) − φ(v)` is the dyadic window functional of the difference test at lag `v`. Suppose
`P_v ≥ 0` for every `v ∈ [0, V]`.

**Records.** At the lag `V` the loudness `A_z = |D(z)| e^{Re z·V}` of the exponents right of the line
attains its maximum at a *Legendre record* `z*` (`exists_right_record`): the coefficients are
summable, so only finitely many exponents are louder than any given one. This holds whether or
not the largest real part of the zeros is attained.

**Counting.** The corpus local zero count (`RHTower.card_le_of_ordinates_in_window`, at most
`40 log(180|t|)` zero copies with ordinate within `1` of `t`) bounds the exponents of `φ` in every
unit height window by `160 log(180(|a| + 5))` (`card_exponent_unitWindow_le`). Grouping the
exponents by unit windows around a point `s`, every finite family at distance `≥ r` from `s` has
cubic potential `Σ |z − s|^{−3} ≤ 480 L_s (r^{−3} + 3)`, `L_s = log(180(|Im s| + 6))`
(`sum_inv_cube_le`).

**The companion law** (`zeta_companion_law`). Evaluate the Fejér window
(`FejerLagWindowCubicPotentialLaw`) at `s = σ + i Im z*`, `σ = Re z* − κ/V`. Every right exponent
is at most as loud as the record, the others are quiet, so the whole potential is
`(4/3)|D(z*)| e^κ Π + (8/3) Σ|D| (1/64 + 1/r³)`, with `Π = 480 log 1080 (1/64 + 3) + 480 L_s (r^{−3} + 3)`
built from the local count alone, provided no other exponent lies within `r` of `s`. When
`V³ ≥ (8/3)κ(κ² + 4π²) Π`, positivity of `P_v` on `[0, V]` forces
`(4/3) Π |D(z*)| (e^κ − 2) ≤ |φ(0)|(1/σ³ + 1/24) + (8/3) Σ|D| (1/64 + 1/r³)`.

So at every lag `V` the off-line zeros of `ζ`, if any, satisfy one of three things: the record is
quiet (`|D(z*)| e^κ` bounded), or the lag family is already negative on `[0, V]`, or another zero lies
within distance `r ≍ κ (log |Im z*|)^{1/3}/V` of the point `(Re z* − κ/V, Im z*)`: a companion just
below the record, closer and closer as `V` grows. Nothing but the local zero count is used; the
attainment premise is replaced by the record and the count.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Counting the exponents of the lag function of `ζ` -/

/-- A nontrivial zero of `ζ` lifts to its first zero copy of `ξ`. -/
def carrierCopy (ρ : zetaZeroConfig.carrier) : XiZeroCopy :=
  ⟨xiDivisorZetaCarrierEquiv.symm ρ, ⟨0, by
    have h := xi_divisor_pos_on_support (xiDivisorZetaCarrierEquiv.symm ρ); omega⟩⟩

theorem carrierCopy_val (ρ : zetaZeroConfig.carrier) : ((carrierCopy ρ).1 : ℂ) = ρ := rfl

/-- At most `40 log(180|t|)` nontrivial zeros of `ζ` have ordinate within `1` of `t`, `|t| ≥ 4`. -/
theorem card_carrier_window_le {t : ℝ} (ht : 4 ≤ |t|) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier ∧ |ρ.im - t| ≤ 1) :
    (S.card : ℝ) ≤ 40 * Real.log (180 * |t|) := by
  classical
  set F : Finset XiZeroCopy := S.attach.image fun ρ => carrierCopy ⟨ρ.1, (hS ρ.1 ρ.2).1⟩ with hF
  have hinj : Function.Injective fun ρ : S => carrierCopy ⟨ρ.1, (hS ρ.1 ρ.2).1⟩ := by
    intro ρ ρ' h
    have := congrArg (fun q : XiZeroCopy => ((q.1 : ℂ))) h
    simp only [carrierCopy_val] at this
    exact Subtype.ext this
  have hcard : F.card = S.card := by
    rw [hF, Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have := card_le_of_ordinates_in_window ht F fun q hq => by
    obtain ⟨ρ, -, rfl⟩ := Finset.mem_image.mp hq
    rw [carrierCopy_val]
    exact (hS ρ.1 ρ.2).2
  rwa [hcard] at this

/-- At most `80 log(180|t|)` exponents of the lag function have height within `1` of `t`, `|t| ≥ 4`. -/
theorem card_exponent_window_le {b : ℝ → ℂ} {t : ℝ} (ht : 4 ≤ |t|) (F : Finset ℂ)
    (hF : ∀ z ∈ F, evenCoeff zetaZeroConfig b z ≠ 0 ∧ |z.im - t| ≤ 1) :
    (F.card : ℝ) ≤ 80 * Real.log (180 * |t|) := by
  classical
  set F₁ := F.filter fun z => (1 / 2 + z) ∈ zetaZeroConfig.carrier with hF₁
  set F₂ := F.filter fun z => ¬ (1 / 2 + z) ∈ zetaZeroConfig.carrier with hF₂
  have hsplit : (F.card : ℝ) = F₁.card + F₂.card := by
    rw [hF₁, hF₂]; exact_mod_cast (Finset.card_filter_add_card_filter_not _).symm
  have h1 : (F₁.card : ℝ) ≤ 40 * Real.log (180 * |t|) := by
    have := card_carrier_window_le ht (F₁.image fun z => 1 / 2 + z) fun ρ hρ => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hρ
      rw [hF₁, Finset.mem_filter] at hz
      exact ⟨hz.2, by simpa using (hF z hz.1).2⟩
    rwa [Finset.card_image_of_injective _ (add_right_injective _)] at this
  have h2 : (F₂.card : ℝ) ≤ 40 * Real.log (180 * |t|) := by
    have ht' : 4 ≤ |-t| := by rwa [abs_neg]
    have := card_carrier_window_le ht' (F₂.image fun z => 1 / 2 + conj z) fun ρ hρ => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hρ
      rw [hF₂, Finset.mem_filter] at hz
      refine ⟨(mem_of_evenCoeff_ne_zero (hF z hz.1).1).resolve_left hz.2, ?_⟩
      have := (hF z hz.1).2
      simp only [Complex.add_im, Complex.conj_im]
      rw [show (1 / 2 : ℂ).im + -z.im - -t = -(z.im - t) by simp; ring, abs_neg]
      exact this
    rw [Finset.card_image_of_injective _ fun z z' h => by
      simpa using congrArg conj (add_left_cancel h), abs_neg] at this
    exact this
  linarith

/-- **Unit windows.** At most `160 log(180(|a| + 5))` exponents of the lag function of `ζ` have
height in `[a, a + 1]`. -/
theorem card_exponent_unitWindow_le {b : ℝ → ℂ} (a : ℝ) (F : Finset ℂ)
    (hF : ∀ z ∈ F, evenCoeff zetaZeroConfig b z ≠ 0 ∧ a ≤ z.im ∧ z.im ≤ a + 1) :
    (F.card : ℝ) ≤ 160 * Real.log (180 * (|a| + 5)) := by
  classical
  have hL : 0 ≤ Real.log (180 * (|a| + 5)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg a])
  by_cases ht : 4 ≤ |a + 1 / 2|
  · have := card_exponent_window_le ht F fun z hz => ⟨(hF z hz).1, by
      rw [abs_le]; constructor <;> linarith [(hF z hz).2.1, (hF z hz).2.2]⟩
    have hmono : Real.log (180 * |a + 1 / 2|) ≤ Real.log (180 * (|a| + 5)) :=
      Real.log_le_log (by positivity) (by
        have := abs_add_le a (1 / 2); rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
        linarith)
    linarith
  · push Not at ht
    -- every exponent in the window has height in `[4, 4.5]` or `[−4.5, −4]`
    set Fp := F.filter fun z => 0 ≤ z.im with hFp
    set Fn := F.filter fun z => ¬ 0 ≤ z.im with hFn
    have hsplit : (F.card : ℝ) = Fp.card + Fn.card := by
      rw [hFp, hFn]; exact_mod_cast (Finset.card_filter_add_card_filter_not _).symm
    have hwin : ∀ z ∈ F, |z.im| ≤ 9 / 2 := fun z hz => by
      have h := abs_lt.mp ht
      rw [abs_le]; constructor <;> linarith [(hF z hz).2.1, (hF z hz).2.2]
    have h4 : ∀ z ∈ F, 4 ≤ |z.im| := fun z hz => four_le_abs_im_of_evenCoeff_zeta (hF z hz).1
    have hp : (Fp.card : ℝ) ≤ 80 * Real.log (180 * |(4 : ℝ)|) :=
      card_exponent_window_le (by norm_num) Fp fun z hz => by
        rw [hFp, Finset.mem_filter] at hz
        have h1 := h4 z hz.1; have h2 := hwin z hz.1
        rw [abs_of_nonneg hz.2] at h1 h2
        exact ⟨(hF z hz.1).1, by rw [abs_le]; constructor <;> linarith⟩
    have hn : (Fn.card : ℝ) ≤ 80 * Real.log (180 * |(-4 : ℝ)|) :=
      card_exponent_window_le (by norm_num) Fn fun z hz => by
        rw [hFn, Finset.mem_filter] at hz
        push Not at hz
        have h1 := h4 z hz.1; have h2 := hwin z hz.1
        rw [abs_of_neg hz.2] at h1 h2
        exact ⟨(hF z hz.1).1, by rw [abs_le]; constructor <;> linarith⟩
    have hmono : Real.log (180 * 4) ≤ Real.log (180 * (|a| + 5)) :=
      Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg a])
    norm_num at hp hn
    rw [hsplit]
    have : Real.log 720 ≤ Real.log (180 * (|a| + 5)) := by
      rw [show (720 : ℝ) = 180 * 4 by norm_num]; exact hmono
    linarith

/-! ### The cubic potential of the exponents -/

/-- The distance from the height window `j` (heights in `[j, j+1)` relative to `s`) to `s`. -/
def windowDist (j : ℤ) : ℝ := if 0 ≤ j then (j : ℝ) else (-j - 1 : ℝ)

theorem windowDist_nonneg (j : ℤ) : 0 ≤ windowDist j := by
  unfold windowDist; split_ifs with h
  · exact_mod_cast h
  · push Not at h; have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
    linarith

/-- `Σ_{n ∈ F} 1/n² ≤ π²/6` for every finite set of naturals. -/
theorem sum_inv_sq_le (F : Finset ℕ) : ∑ n ∈ F, 1 / (n : ℝ) ^ 2 ≤ π ^ 2 / 6 :=
  sum_le_hasSum F (fun n _ => by positivity) hasSum_zeta_two

/-- **Window weights.** For every finite set `J` of window indices,
`Σ_{j ∈ J} (|j| + 1)/max(r, d_j)³ ≤ 3(1/r³ + 3)`. -/
theorem sum_window_weight_le {r : ℝ} (hr : 0 < r) (J : Finset ℤ) :
    ∑ j ∈ J, ((|j| : ℝ) + 1) / max r (windowDist j) ^ 3 ≤ 3 * (1 / r ^ 3 + 3) := by
  classical
  set f : ℤ → ℝ := fun j => ((|j| : ℝ) + 1) / max r (windowDist j) ^ 3 with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j => by
    rw [hf]; exact div_nonneg (by positivity) (by positivity)
  set Jz := J.filter fun j => -1 ≤ j ∧ j ≤ 0 with hJz
  set Jp := J.filter fun j => 1 ≤ j with hJp
  set Jm := J.filter fun j => j ≤ -2 with hJm
  have hcover : ∑ j ∈ J, f j ≤ ∑ j ∈ Jz, f j + ∑ j ∈ Jp, f j + ∑ j ∈ Jm, f j := by
    have h1 : ∑ j ∈ J, f j = ∑ j ∈ Jz, f j + ∑ j ∈ J.filter (fun j => ¬ (-1 ≤ j ∧ j ≤ 0)), f j :=
      (Finset.sum_filter_add_sum_filter_not J _ f).symm
    have h2 : ∑ j ∈ J.filter (fun j => ¬ (-1 ≤ j ∧ j ≤ 0)), f j ≤ ∑ j ∈ Jp, f j + ∑ j ∈ Jm, f j := by
      rw [← Finset.sum_union (by
        rw [Finset.disjoint_left]; intro j h1 h2
        rw [hJp, Finset.mem_filter] at h1; rw [hJm, Finset.mem_filter] at h2; omega)]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hf0 j
      rw [Finset.mem_filter] at hj
      obtain ⟨hjJ, hjc⟩ := hj
      rw [Finset.mem_union, hJp, hJm, Finset.mem_filter, Finset.mem_filter]
      by_cases h1 : 1 ≤ j
      · exact Or.inl ⟨hjJ, h1⟩
      · exact Or.inr ⟨hjJ, by omega⟩
    linarith
  -- the two central windows
  have h0 : ∑ j ∈ Jz, f j ≤ 3 / r ^ 3 := by
    have hsub : Jz ⊆ {-1, 0} := fun j hj => by
      rw [hJz, Finset.mem_filter] at hj
      rw [Finset.mem_insert, Finset.mem_singleton]; omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hf0 j).trans ?_
    rw [Finset.sum_pair (by norm_num)]
    have hd1 : windowDist (-1) = 0 := by simp [windowDist]
    have hd0 : windowDist 0 = 0 := by simp [windowDist]
    have e1 : f (-1) = 2 / r ^ 3 := by
      simp only [hf, hd1, max_eq_left hr.le]; norm_num
    have e0 : f 0 = 1 / r ^ 3 := by
      simp only [hf, hd0, max_eq_left hr.le]; norm_num
    rw [e1, e0]
    exact le_of_eq (by ring)
  -- the windows above
  have hp : ∑ j ∈ Jp, f j ≤ 2 * (π ^ 2 / 6) := by
    have hle : ∀ j ∈ Jp, f j ≤ 2 * (1 / ((j.toNat : ℕ) : ℝ) ^ 2) := fun j hj => by
      rw [hJp, Finset.mem_filter] at hj
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.2
      have hcast : ((j.toNat : ℕ) : ℝ) = j := by exact_mod_cast Int.toNat_of_nonneg (by omega)
      have hd : windowDist j = j := by simp [windowDist, show 0 ≤ j by omega]
      rw [hcast]
      simp only [hf, hd]
      rw [abs_of_nonneg (by linarith)]
      have hmax : (j : ℝ) ≤ max r j := le_max_right _ _
      calc ((j : ℝ) + 1) / max r j ^ 3 ≤ ((j : ℝ) + 1) / (j : ℝ) ^ 3 :=
            div_le_div_of_nonneg_left (by linarith) (by positivity)
              (pow_le_pow_left₀ (by linarith) hmax 3)
        _ ≤ 2 * (1 / (j : ℝ) ^ 2) := by
            rw [div_le_iff₀ (by positivity)]; field_simp; nlinarith
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hinj : Set.InjOn (fun j : ℤ => j.toNat) Jp := fun j hj j' hj' h => by
      rw [Finset.mem_coe, hJp, Finset.mem_filter] at hj hj'
      have : (j.toNat : ℤ) = j.toNat := rfl
      simp only at h
      omega
    rw [← Finset.sum_image (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hinj]
    exact sum_inv_sq_le _
  -- the windows below
  have hn : ∑ j ∈ Jm, f j ≤ 3 * (π ^ 2 / 6) := by
    have hle : ∀ j ∈ Jm, f j ≤ 3 * (1 / (((-j - 1).toNat : ℕ) : ℝ) ^ 2) := fun j hj => by
      rw [hJm, Finset.mem_filter] at hj
      have hcast : (((-j - 1).toNat : ℕ) : ℝ) = -j - 1 := by
        rw [show (-(j : ℝ) - 1) = ((-j - 1 : ℤ) : ℝ) by push_cast; ring]
        exact_mod_cast Int.toNat_of_nonneg (by omega)
      have hk1 : (1 : ℝ) ≤ -j - 1 := by
        have : (j : ℝ) ≤ -2 := by exact_mod_cast hj.2
        linarith
      have hd : windowDist j = -j - 1 := by simp [windowDist, show ¬ 0 ≤ j by omega]
      rw [hcast]
      simp only [hf, hd]
      rw [abs_of_neg (by linarith)]
      have hmax : (-(j : ℝ) - 1) ≤ max r (-j - 1) := le_max_right _ _
      calc (-(j : ℝ) + 1) / max r (-j - 1) ^ 3 ≤ (-(j : ℝ) + 1) / (-(j : ℝ) - 1) ^ 3 :=
            div_le_div_of_nonneg_left (by linarith) (by positivity)
              (pow_le_pow_left₀ (by linarith) hmax 3)
        _ ≤ 3 * (1 / (-(j : ℝ) - 1) ^ 2) := by
            rw [div_le_iff₀ (by positivity)]; field_simp; nlinarith
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hinj : Set.InjOn (fun j : ℤ => (-j - 1).toNat) Jm := fun j hj j' hj' h => by
      rw [Finset.mem_coe, hJm, Finset.mem_filter] at hj hj'
      simp only at h
      omega
    rw [← Finset.sum_image (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hinj]
    exact sum_inv_sq_le _
  have hpi : π ^ 2 / 6 ≤ 9 / 5 := by
    have h1 := Real.pi_lt_d2; have h2 := Real.pi_pos; nlinarith
  calc ∑ j ∈ J, f j ≤ 3 / r ^ 3 + 2 * (π ^ 2 / 6) + 3 * (π ^ 2 / 6) := by linarith
    _ ≤ 3 * (1 / r ^ 3 + 3) := by
        have : 3 / r ^ 3 = 3 * (1 / r ^ 3) := by ring
        nlinarith

/-- **Cubic potential.** Every finite family of exponents of the lag function of `ζ` at distance
`≥ r` from `s` has `Σ |z − s|^{−3} ≤ 480 L (1/r³ + 3)`, `L = log(180(|Im s| + 6))`. -/
theorem sum_inv_cube_le {b : ℝ → ℂ} {s : ℂ} {r : ℝ} (hr : 0 < r) (S : Finset ℂ)
    (hS : ∀ z ∈ S, evenCoeff zetaZeroConfig b z ≠ 0 ∧ r ≤ ‖z - s‖) :
    ∑ z ∈ S, 1 / ‖z - s‖ ^ 3 ≤ 480 * Real.log (180 * (|s.im| + 6)) * (1 / r ^ 3 + 3) := by
  classical
  set L := Real.log (180 * (|s.im| + 6)) with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith [abs_nonneg s.im]
  set j : ℂ → ℤ := fun z => ⌊z.im - s.im⌋ with hj
  set J := S.image j with hJ
  rw [← Finset.sum_fiberwise_of_maps_to (g := j) (t := J) fun z hz => Finset.mem_image_of_mem _ hz]
  have hfib : ∀ k ∈ J, ∑ z ∈ S with j z = k, 1 / ‖z - s‖ ^ 3 ≤
      160 * L * (((|k| : ℝ) + 1) / max r (windowDist k) ^ 3) := by
    intro k _
    set Sk := S.filter fun z => j z = k with hSk
    -- the window `[Im s + k, Im s + k + 1]`
    have hwin : ∀ z ∈ Sk, (k : ℝ) ≤ z.im - s.im ∧ z.im - s.im < k + 1 := fun z hz => by
      rw [hSk, Finset.mem_filter] at hz
      have := Int.floor_le (z.im - s.im); have := Int.lt_floor_add_one (z.im - s.im)
      rw [hj] at hz; simp only at hz; rw [hz.2] at *
      exact ⟨by linarith, by linarith⟩
    have hcard : (Sk.card : ℝ) ≤ 160 * Real.log (180 * (|s.im + k| + 5)) :=
      card_exponent_unitWindow_le (s.im + k) Sk fun z hz => by
        have := hwin z hz
        exact ⟨(hS z (Finset.mem_filter.mp hz).1).1, by linarith, by linarith⟩
    have hlog : Real.log (180 * (|s.im + k| + 5)) ≤ L * ((|k| : ℝ) + 1) := by
      have h1 : 180 * (|s.im + k| + 5) ≤ 180 * (|s.im| + 6) * ((|k| : ℝ) + 1) := by
        have := abs_add_le s.im (k : ℝ)
        have : (|(k : ℝ)|) = ((|k| : ℤ) : ℝ) := by push_cast; rfl
        nlinarith [abs_nonneg s.im, abs_nonneg (k : ℝ)]
      have hk : (0 : ℝ) < (|k| : ℝ) + 1 := by positivity
      calc Real.log (180 * (|s.im + k| + 5)) ≤ Real.log (180 * (|s.im| + 6) * ((|k| : ℝ) + 1)) :=
            Real.log_le_log (by positivity) h1
        _ = L + Real.log ((|k| : ℝ) + 1) := by
            rw [Real.log_mul (by positivity) hk.ne']
        _ ≤ L + (|k| : ℝ) := by
            linarith [Real.log_le_sub_one_of_pos hk]
        _ ≤ L * ((|k| : ℝ) + 1) := by nlinarith [abs_nonneg (k : ℝ)]
    have hterm : ∀ z ∈ Sk, 1 / ‖z - s‖ ^ 3 ≤ 1 / max r (windowDist k) ^ 3 := fun z hz => by
      have hd : windowDist k ≤ ‖z - s‖ := by
        have hw := hwin z hz
        have him : |z.im - s.im| ≤ ‖z - s‖ := by
          have := Complex.abs_im_le_norm (z - s); simpa using this
        refine le_trans ?_ him
        unfold windowDist
        split_ifs with hk
        · have h0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
          rw [abs_of_nonneg (by linarith [hw.1])]; exact hw.1
        · push Not at hk
          have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
          rw [abs_of_neg (by linarith)]; linarith
      have hmax : max r (windowDist k) ≤ ‖z - s‖ :=
        max_le (hS z (Finset.mem_filter.mp hz).1).2 hd
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (le_max_of_le_left hr.le) hmax 3)
    calc ∑ z ∈ Sk, 1 / ‖z - s‖ ^ 3 ≤ ∑ _z ∈ Sk, 1 / max r (windowDist k) ^ 3 :=
          Finset.sum_le_sum hterm
      _ = Sk.card * (1 / max r (windowDist k) ^ 3) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (160 * Real.log (180 * (|s.im + k| + 5))) * (1 / max r (windowDist k) ^ 3) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (160 * (L * ((|k| : ℝ) + 1))) * (1 / max r (windowDist k) ^ 3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  calc ∑ k ∈ J, ∑ z ∈ S with j z = k, 1 / ‖z - s‖ ^ 3
      ≤ ∑ k ∈ J, 160 * L * (((|k| : ℝ) + 1) / max r (windowDist k) ^ 3) := Finset.sum_le_sum hfib
    _ = 160 * L * ∑ k ∈ J, ((|k| : ℝ) + 1) / max r (windowDist k) ^ 3 := by rw [Finset.mul_sum]
    _ ≤ 160 * L * (3 * (1 / r ^ 3 + 3)) :=
        mul_le_mul_of_nonneg_left (sum_window_weight_le hr J) (by positivity)
    _ = 480 * L * (1 / r ^ 3 + 3) := by ring

/-- The cubic potential as a sum over all exponents selected by `p`. -/
theorem tsum_inv_cube_le {b : ℝ → ℂ} {s : ℂ} {r : ℝ} (hr : 0 < r) (p : ℂ → Prop) [DecidablePred p]
    (hp : ∀ z, p z → evenCoeff zetaZeroConfig b z ≠ 0 ∧ r ≤ ‖z - s‖) :
    Summable (fun z : ℂ => if p z then 1 / ‖z - s‖ ^ 3 else 0) ∧
      ∑' z : ℂ, (if p z then 1 / ‖z - s‖ ^ 3 else 0) ≤
        480 * Real.log (180 * (|s.im| + 6)) * (1 / r ^ 3 + 3) := by
  classical
  have hfin : ∀ u : Finset ℂ, ∑ z ∈ u, (if p z then 1 / ‖z - s‖ ^ 3 else 0) ≤
      480 * Real.log (180 * (|s.im| + 6)) * (1 / r ^ 3 + 3) := fun u => by
    rw [← Finset.sum_filter]
    exact sum_inv_cube_le hr _ fun z hz => hp z (Finset.mem_filter.mp hz).2
  have h0 : 0 ≤ fun z : ℂ => if p z then 1 / ‖z - s‖ ^ 3 else 0 := fun z => by
    simp only [Pi.zero_apply]; split_ifs <;> positivity
  have hs := summable_of_sum_le h0 hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

/-! ### Records -/

/-- **Legendre records exist.** If some exponent `z₀` right of the line has `D(z₀) ≠ 0`, then at every
lag `V ≥ 0` the loudness `|D(z)| e^{Re z·V}` of the exponents right of the line attains its maximum. -/
theorem exists_right_record (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) {z₀ : ℂ}
    (hz₀ : evenCoeff Z b z₀ ≠ 0) (hre₀ : 0 < z₀.re) :
    ∃ z₁ : ℂ, evenCoeff Z b z₁ ≠ 0 ∧ 0 < z₁.re ∧ ∀ z : ℂ, evenCoeff Z b z ≠ 0 → 0 < z.re →
      ‖evenCoeff Z b z‖ * Real.exp (z.re * V) ≤ ‖evenCoeff Z b z₁‖ * Real.exp (z₁.re * V) := by
  classical
  set f : ℂ → ℝ := fun z => ‖evenCoeff Z b z‖ * Real.exp (z.re * V) with hf
  have hs : Summable f := summable_norm_evenCoeff_mul Z hZ hb hbs (C := Real.exp (1 / 2 * V))
    (fun _ => (Real.exp_pos _).le) fun z hz => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      ((le_abs_self _).trans (abs_re_le_of_evenCoeff_ne_zero hz)) hV)
  have hε : 0 < f z₀ := mul_pos (norm_pos_iff.mpr hz₀) (Real.exp_pos _)
  have hfin : {z : ℂ | f z₀ ≤ f z}.Finite := by
    have := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)
    rw [Filter.eventually_cofinite] at this
    exact this.subset fun z hz => not_lt.mpr hz
  set T := (hfin.inter_of_left {z : ℂ | evenCoeff Z b z ≠ 0 ∧ 0 < z.re}).toFinset with hT
  have hz₀T : z₀ ∈ T := by
    rw [hT, Set.Finite.mem_toFinset]; exact ⟨show f z₀ ≤ f z₀ from le_rfl, hz₀, hre₀⟩
  obtain ⟨z₁, hz₁T, hmax⟩ := T.exists_max_image f ⟨z₀, hz₀T⟩
  rw [hT, Set.Finite.mem_toFinset] at hz₁T
  refine ⟨z₁, hz₁T.2.1, hz₁T.2.2, fun z hz hre => ?_⟩
  by_cases hzT : z ∈ T
  · exact hmax z hzT
  · rw [hT, Set.Finite.mem_toFinset] at hzT
    have : ¬ f z₀ ≤ f z := fun h => hzT ⟨show f z₀ ≤ f z from h, hz, hre⟩
    exact (le_of_lt (not_le.mp this)).trans (hmax z₀ hz₀T)

/-! ### The companion law -/

/-- **The companion law for `ζ`.** Let `0 < w < ½ log 2`, `V ≥ π`, and suppose the dyadic window
functionals `P_v` of the difference tests are nonnegative for every `v ∈ [0, V]`. Let `z*` be a
Legendre record right of the line at lag `V`, `κ > 0`, `σ = Re z* − κ/V > 0`, `s = σ + i Im z*`, and
suppose no other exponent lies within `r` of `s`, `Vr ≥ 4π`. With
`Π = 480 log 1080 (1/64 + 3) + 480 log(180(|Im z*| + 6)) (1/r³ + 3)` and
`V³ ≥ (8/3)κ(κ² + 4π²)Π`:
`(4/3) Π |D(z*)| (e^κ − 2) ≤ |M|(1/σ³ + 1/24) + (8/3) Σ_z |D(z)| (1/64 + 1/r³)`. -/
theorem zeta_companion_law {w V : ℝ} (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hV : π ≤ V)
    (hP : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hσ : 0 < z₁.re - κ / V) (hr : 0 < r) (hVr : 4 * π ≤ V * r)
    (hsep : ∀ z, z ≠ z₁ → evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖)
    (hV3 : 8 / 3 * (κ * (κ ^ 2 + 4 * π ^ 2)) * (480 * Real.log 1080 * (1 / 64 + 3) +
      480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) ≤ V ^ 3) :
    4 / 3 * (480 * Real.log 1080 * (1 / 64 + 3) +
        480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) *
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * (Real.exp κ - 2) ≤
      |2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| *
          (1 / (z₁.re - κ / V) ^ 3 + 1 / 24) +
        8 / 3 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖) *
          (1 / 64 + 1 / r ^ 3) := by
  classical
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs : ∀ u, b u ≠ 0 → |u| ≤ w := modScaledBump_support hw 0
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set σ : ℝ := z₁.re - κ / V with hσdef
  set θ : ℝ := κ / V with hθdef
  have hV0 : 0 < V := lt_of_lt_of_le Real.pi_pos hV
  have hθ0 : 0 < θ := div_pos hκ hV0
  have hθV : θ * V = κ := by rw [hθdef]; field_simp
  set s : ℂ := (σ : ℂ) + z₁.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = z₁.im := by simp [hs]
  -- the lag family is nonnegative on `[0, V]`
  have hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re :=
    fun v hv => by
      rw [hbdef, zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
        (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
        (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
          (modScaledBump_support hw 0)) v (-1)),
        literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1]
      exact hP v hv
  have hcore := norm_evenCoeff_mul_fejerWin_le zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
    hV0.le hm z₁ σ z₁.im
  rw [← hs] at hcore
  -- the record term
  have hz₁s : z₁ - s = (θ : ℂ) := by apply Complex.ext <;> simp [hs, hσdef, hθdef]
  have hLHS : ‖D z₁ * fejerWin V (z₁ - s)‖ =
      ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) := by
    rw [norm_mul, hz₁s, norm_fejerWin_ofReal_pos hV0 hθ0, hθV]
  -- the loudness of every exponent, relative to the record
  have hloud : ∀ z, D z ≠ 0 → ‖D z‖ * Real.exp ((z.re - σ) * V) ≤ ‖D z₁‖ * Real.exp κ + ‖D z‖ :=
    fun z hz => by
      by_cases hre : 0 < z.re
      · have h := hrec z hz hre
        have e1 : ‖D z‖ * Real.exp ((z.re - σ) * V) =
            ‖D z‖ * Real.exp (z.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
        have e2 : ‖D z₁‖ * Real.exp κ = ‖D z₁‖ * Real.exp (z₁.re * V) * Real.exp (-σ * V) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hσdef]; linarith [hθV]
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_right h (Real.exp_pos (-σ * V)).le
        linarith [norm_nonneg (D z)]
      · push Not at hre
        have : Real.exp ((z.re - σ) * V) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) hV0.le)
        have := mul_le_mul_of_nonneg_left this (norm_nonneg (D z))
        have := mul_nonneg (norm_nonneg (D z₁)) (Real.exp_pos κ).le
        linarith
  set c : ℝ := 8 * π ^ 2 / 3 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  -- potential kernels
  have hkern : ∀ {z u : ℂ} {d : ℝ}, 0 < d → 4 * π ≤ V * d → u.re = σ → D z ≠ 0 →
      d ≤ ‖z - u‖ → ‖D z‖ * ‖fejerWin V (z - u)‖ ≤
        c / V ^ 2 * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3) + 2 * ‖D z‖ / d ^ 3) := by
    intro z u d hd hVd hu hz hgap
    have hzu : 0 < ‖z - u‖ := lt_of_lt_of_le hd hgap
    have h4 : 4 * π ≤ V * ‖z - u‖ := hVd.trans (mul_le_mul_of_nonneg_left hgap hV0.le)
    have hcube := norm_fejerWin_le_cube hV0 h4
    rw [Complex.sub_re, hu, ← hc] at hcube
    have hcube' : 1 / ‖z - u‖ ^ 3 ≤ 1 / d ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hd.le hgap 3)
    have hl := hloud z hz
    calc ‖D z‖ * ‖fejerWin V (z - u)‖
        ≤ ‖D z‖ * (c * (Real.exp ((z.re - σ) * V) + 1) / (V ^ 2 * ‖z - u‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left hcube (norm_nonneg _)
      _ = c / V ^ 2 * ((‖D z‖ * Real.exp ((z.re - σ) * V) + ‖D z‖) * (1 / ‖z - u‖ ^ 3)) := by
          field_simp
      _ ≤ c / V ^ 2 * ((‖D z₁‖ * Real.exp κ + 2 * ‖D z‖) * (1 / ‖z - u‖ ^ 3)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          linarith
      _ ≤ c / V ^ 2 * (‖D z₁‖ * Real.exp κ * (1 / ‖z - u‖ ^ 3) + 2 * ‖D z‖ / d ^ 3) := by
          gcongr
          rw [add_mul]
          have : 2 * ‖D z‖ * (1 / ‖z - u‖ ^ 3) ≤ 2 * ‖D z‖ * (1 / d ^ 3) :=
            mul_le_mul_of_nonneg_left hcube' (by positivity)
          rw [show 2 * ‖D z‖ / d ^ 3 = 2 * ‖D z‖ * (1 / d ^ 3) by ring]
          linarith
  -- the potential sums
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
  obtain ⟨hs0, hP0b⟩ := tsum_inv_cube_le (b := b) (s := (σ : ℂ)) (r := 4) (by norm_num)
    (fun z => D z ≠ 0) fun z hz => ⟨hz, (four_le_abs_im_of_evenCoeff_zeta hz).trans (by
      have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this)⟩
  obtain ⟨hs1, hP1b⟩ := tsum_inv_cube_le (b := b) (s := s) hr (fun z => D z ≠ 0 ∧ z ≠ z₁)
    fun z hz => ⟨hz.1, hsep z hz.2 hz.1⟩
  rw [show (|((σ : ℂ)).im| : ℝ) = 0 by simp, zero_add] at hP0b
  rw [hsim] at hP1b
  set P0 : ℝ := ∑' z : ℂ, (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) with hP0
  set P1 : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ z ≠ z₁ then 1 / ‖z - s‖ ^ 3 else 0) with hP1
  have hP0 : ∑' z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤
      c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) := by
    have hle : ∀ z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤ c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) +
          2 * ‖D z‖ / 4 ^ 3) := fun z => by
      by_cases hz : D z = 0
      · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, if_false, mul_zero,
          zero_add, zero_div]
        positivity
      · rw [if_pos hz]
        exact hkern (by norm_num) (by linarith [Real.pi_pos]) (by simp) hz
          ((four_le_abs_im_of_evenCoeff_zeta hz).trans (by
            have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
    have hR : Summable fun z : ℂ => c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) +
          2 * ‖D z‖ / 4 ^ 3) :=
      ((hs0.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le (fun _ => by positivity) hle) hR).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add (hs0.mul_left _) ((hsD.mul_left 2).div_const _),
      tsum_mul_left, tsum_div_const, tsum_mul_left]
  have hP1 : ∑' z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤
      c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) := by
    have hle : ∀ z : ℂ, (if z = z₁ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤ c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 ∧ z ≠ z₁ then 1 / ‖z - s‖ ^ 3 else 0) +
          2 * ‖D z‖ / r ^ 3) := fun z => by
      by_cases hzz : z = z₁
      · rw [if_pos hzz]; positivity
      · rw [if_neg hzz]
        by_cases hz : D z = 0
        · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, false_and, if_false,
            mul_zero, zero_add, zero_div]
          positivity
        · rw [if_pos ⟨hz, hzz⟩]
          exact hkern hr hVr hsre hz (hsep z hzz hz)
    have hR : Summable fun z : ℂ => c / V ^ 2 *
        (‖D z₁‖ * Real.exp κ * (if D z ≠ 0 ∧ z ≠ z₁ then 1 / ‖z - s‖ ^ 3 else 0) +
          2 * ‖D z‖ / r ^ 3) :=
      ((hs1.mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) hle) hR).trans (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add (hs1.mul_left _) ((hsD.mul_left 2).div_const _),
      tsum_mul_left, tsum_div_const, tsum_mul_left]
  -- the archimedean-pole kernels
  have hE1 : ‖fejerWin V (-(σ : ℂ))‖ ≤ 2 * π ^ 2 / (V ^ 2 * σ ^ 3) := norm_fejerWin_neg_le hV0 hσ
  have hE2 : ‖fejerWin V (-s)‖ ≤ c * 2 / (V ^ 2 * 4 ^ 3) := by
    have h4 : (4 : ℝ) ≤ ‖(0 : ℂ) - s‖ := by
      rw [zero_sub, norm_neg]
      exact (four_le_abs_im_of_evenCoeff_zeta hz₁).trans (by
        rw [← hsim]; exact Complex.abs_im_le_norm s)
    have := norm_fejerWin_sub_le hV0 (by norm_num) (by linarith [Real.pi_pos]) h4
    rw [zero_sub, Complex.zero_re, hsre, ← hc] at this
    refine this.trans ?_
    have : Real.exp ((0 - σ) * V) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    gcongr
    linarith
  -- assemble, in units of `u = 2π²/V²`
  set u : ℝ := 2 * π ^ 2 / V ^ 2 with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  set Pb : ℝ := 480 * Real.log 1080 * (1 / 64 + 3) +
    480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3) with hPb
  have hPle : P0 + P1 ≤ Pb := by
    have h0 : P0 ≤ 480 * Real.log 1080 * (1 / 64 + 3) := by
      refine hP0b.trans (le_of_eq ?_); norm_num
    rw [hPb]; linarith [hP1b]
  have hcu : c / V ^ 2 = u * (4 / 3) := by rw [hc, hu]; field_simp; ring
  have hE1' : 2 * π ^ 2 / (V ^ 2 * σ ^ 3) = u * (1 / σ ^ 3) := by rw [hu]; field_simp
  have hE2' : c * 2 / (V ^ 2 * 4 ^ 3) = u * (1 / 24) := by rw [hc, hu]; field_simp; norm_num
  have hDe : 0 ≤ ‖D z₁‖ * Real.exp κ := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hbig : ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) ≤
      u * (|M| * (1 / σ ^ 3 + 1 / 24) + 4 / 3 * (‖D z₁‖ * Real.exp κ) * Pb +
        8 / 3 * W * (1 / 64 + 1 / r ^ 3)) := by
    rw [← hLHS]
    refine hcore.trans ?_
    have h1 : |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤ u * (|M| * (1 / σ ^ 3 + 1 / 24)) := by
      calc |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤
            |M| * (u * (1 / σ ^ 3) + u * (1 / 24)) :=
            mul_le_mul_of_nonneg_left (add_le_add (hE1.trans_eq hE1') (hE2.trans_eq hE2'))
              (abs_nonneg M)
        _ = _ := by ring
    have h2 : c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) +
        c / V ^ 2 * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) ≤
        u * (4 / 3 * (‖D z₁‖ * Real.exp κ) * Pb + 8 / 3 * W * (1 / 64 + 1 / r ^ 3)) := by
      rw [hcu]
      have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
      have : ‖D z₁‖ * Real.exp κ * (P0 + P1) ≤ ‖D z₁‖ * Real.exp κ * Pb :=
        mul_le_mul_of_nonneg_left hPle hDe
      have e : u * (4 / 3) * (‖D z₁‖ * Real.exp κ * P0 + 2 * W / 4 ^ 3) +
          u * (4 / 3) * (‖D z₁‖ * Real.exp κ * P1 + 2 * W / r ^ 3) =
          u * (4 / 3 * (‖D z₁‖ * Real.exp κ * (P0 + P1)) + 8 / 3 * W * (1 / 64 + 1 / r ^ 3)) := by
        ring
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ hu0.le
      linarith
    linarith
  -- `V³/(κ(κ² + 4π²)) ≥ (8/3)Π`
  have hQ : θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2) = κ * (κ ^ 2 + 4 * π ^ 2) / V := by
    rw [hθdef]; field_simp
  have hQ0 : 0 < κ * (κ ^ 2 + 4 * π ^ 2) := by positivity
  have hexp : 0 ≤ Real.exp κ - 1 := by linarith [Real.one_le_exp hκ.le]
  have hlow : u * (8 / 3 * Pb * (‖D z₁‖ * (Real.exp κ - 1))) ≤
      ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2))) := by
    rw [hQ]
    have hX : 0 ≤ ‖D z₁‖ * (Real.exp κ - 1) := mul_nonneg (norm_nonneg _) hexp
    have hk : u * (8 / 3 * Pb) ≤ 2 * π ^ 2 / (κ * (κ ^ 2 + 4 * π ^ 2) / V) := by
      rw [hu, div_div_eq_mul_div, le_div_iff₀ hQ0]
      have : 8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2)) ≤ V ^ 3 :=
        calc 8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2)) = 8 / 3 * (κ * (κ ^ 2 + 4 * π ^ 2)) * Pb := by
              ring
          _ ≤ V ^ 3 := hV3
      calc 2 * π ^ 2 / V ^ 2 * (8 / 3 * Pb) * (κ * (κ ^ 2 + 4 * π ^ 2))
          = 2 * π ^ 2 / V ^ 2 * (8 / 3 * Pb * (κ * (κ ^ 2 + 4 * π ^ 2))) := by ring
        _ ≤ 2 * π ^ 2 / V ^ 2 * V ^ 3 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 2 * π ^ 2 * V := by field_simp
    calc u * (8 / 3 * Pb * (‖D z₁‖ * (Real.exp κ - 1)))
        = u * (8 / 3 * Pb) * (‖D z₁‖ * (Real.exp κ - 1)) := by ring
      _ ≤ 2 * π ^ 2 / (κ * (κ ^ 2 + 4 * π ^ 2) / V) * (‖D z₁‖ * (Real.exp κ - 1)) :=
          mul_le_mul_of_nonneg_right hk hX
      _ = ‖D z₁‖ * (2 * π ^ 2 * (Real.exp κ - 1) / (κ * (κ ^ 2 + 4 * π ^ 2) / V)) := by ring
  have hfin := le_of_mul_le_mul_left (hlow.trans hbig) hu0
  linarith

/-- **Off-line zeros of `ζ` give a loud exponent.** For a width at which `h_w` vanishes at no zero
ordinate, an off-line zero of `ζ` yields an exponent `z₀` right of the line with `D(z₀) ≠ 0`. -/
theorem exists_right_exponent_of_offLine {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0)
    {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) (hre : ρ.re ≠ 1 / 2) :
    ∃ z₀ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z₀ ≠ 0 ∧ 0 < z₀.re := by
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine zetaZeroConfig hρ hre
  have hgt : paperFT (scaledBump w) (gammaOf t) ≠ 0 := hgood t ht.1 (by linarith [ht.2])
  have hz : (1 / 2 + (t - 1 / 2)) ∈ zetaZeroConfig.carrier := by rw [add_sub_cancel]; exact ht.1
  refine ⟨t - 1 / 2, ?_, by simp; linarith [ht.2]⟩
  rw [evenCoeff_modScaledBump_zero zetaZeroConfig hw hz]
  have hγt : -(I * (t - 1 / 2)) = gammaOf t := by rw [gammaOf, Complex.div_I]; ring
  rw [hγt]
  have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + (t - 1 / 2)) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ hz
  refine mul_ne_zero (fun h1 => ?_) (pow_ne_zero 2 hgt)
  have h2 := congrArg Complex.re h1
  by_cases hc : (1 / 2 + conj (t - 1 / 2)) ∈ zetaZeroConfig.carrier
  · rw [Set.indicator_of_mem hc, Complex.add_re, Complex.natCast_re, Complex.natCast_re,
      Complex.zero_re] at h2
    linarith [(Nat.cast_nonneg (zetaZeroConfig.mult (1 / 2 + conj (t - 1 / 2))) : (0 : ℝ) ≤ _)]
  · rw [Set.indicator_of_notMem hc, Complex.add_re, Complex.natCast_re, Complex.zero_re] at h2
    linarith

/-- **The trichotomy for `ζ`.** For all but countably many widths `w ∈ (0, ½ log 2)`: if RH fails,
then at every lag `V ≥ π` either some window functional `P_v`, `v ∈ [0, V]`, is negative, or there
is a Legendre record `z*` right of the line at lag `V` for which every admissible `κ, r` with no other
exponent within `r` of `(Re z* − κ/V) + i Im z*` obeys the inequality of `zeta_companion_law`. -/
theorem zeta_lag_negative_or_record_bound :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E → ∀ V : ℝ, π ≤ V →
      (∃ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2) →
      (∃ v ∈ Icc (0 : ℝ) V, (lagPrimeWindowRHS v w (EF.weilTest
        (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re < 0) ∨
      ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0 ∧ 0 < z₁.re ∧
        ∀ κ r : ℝ, 0 < κ → 0 < z₁.re - κ / V → 0 < r → 4 * π ≤ V * r →
        (∀ z, z ≠ z₁ → evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
          r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖) →
        8 / 3 * (κ * (κ ^ 2 + 4 * π ^ 2)) * (480 * Real.log 1080 * (1 / 64 + 3) +
          480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) ≤ V ^ 3 →
        4 / 3 * (480 * Real.log 1080 * (1 / 64 + 3) +
            480 * Real.log (180 * (|z₁.im| + 6)) * (1 / r ^ 3 + 3)) *
            ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * (Real.exp κ - 2) ≤
          |2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| *
              (1 / (z₁.re - κ / V) ^ 3 + 1 / 24) +
            8 / 3 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖) *
              (1 / 64 + 1 / r ^ 3) := by
  refine ⟨_, countable_bad_widths zetaZeroConfig, fun w hw hw2 hwE V hV hoff => ?_⟩
  by_cases hneg : ∃ v ∈ Icc (0 : ℝ) V, (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re < 0
  · exact Or.inl hneg
  push Not at hneg
  have hgood : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  obtain ⟨ρ, hρ, hre⟩ := hoff
  obtain ⟨z₀, hz₀, hre₀⟩ := exists_right_exponent_of_offLine hw hgood hρ hre
  have hV0 : 0 ≤ V := (Real.pi_pos.le).trans hV
  obtain ⟨z₁, hz₁, hre₁, hrec⟩ := exists_right_record zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w 0) (modScaledBump_support hw 0) hV0 hz₀ hre₀
  exact Or.inr ⟨z₁, hz₁, hre₁, fun κ r hκ hσ hr hVr hsep hV3 =>
    zeta_companion_law hw hw2 hV hneg hz₁ hrec hκ hσ hr hVr hsep hV3⟩

end GaloisForLFunctions.SquareRootThreshold
