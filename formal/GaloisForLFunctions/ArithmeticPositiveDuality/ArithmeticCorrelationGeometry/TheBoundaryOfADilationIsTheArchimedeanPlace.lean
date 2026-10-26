import GaloisForLFunctions.BiarithmeticGeometry.HorizonBoundaryCalculus
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The boundary of a dilation is the archimedean place

A finite arithmetic presentation is the horizon `{0, …, N}` with the affine maps `j ↦ aj + b`;
the cells pushed past `N` are absorbed. The **escaped pairing** `β_{a,b}(v, w)` is the pairing on
the absorbed cells; it is exactly the defect of the affine map
(`escapedPairing_eq_defect`), and it composes as a cocycle
(`escapedPairing_comp`): the boundary of a composite is the boundary of the first map plus the
transported boundary of the second. The relation `D_a U = U^a D_a` holds with its boundary terms
(`escapedPairing_ring_relation`): both orders absorb the same cells, attributed differently.

**The weight that makes boundaries horizon-uniform.** Give the cell `j ≥ 1` the weight `j^{−σ}`
(`critSource`). Its escaped mass under `j ↦ aj + b` is the sum of `j^{−2σ}` over
`(N − b)/a < j ≤ N` (`escapedPairing_critSource`). As the horizon grows:

* at `σ = ½` it tends to `log a` (`tendsto_escapedMass_half`): the boundary of a dilation is the
  archimedean absolute value of its multiplier, and the cocycle becomes `log(ac) = log a + log c`;
* above `½` it tends to `0` (`tendsto_escapedMass_of_half_lt`);
* below `½` it tends to `+∞` for every genuine dilation `a ≥ 2` (`tendsto_escapedMass_of_lt_half`);
* for the successor `a = 1` it tends to `0` at every positive weight
  (`tendsto_escapedMass_successor`).

Hence (`exists_pos_tendsto_escapedMass_iff`): the escaped mass of a dilation converges to a finite
nonzero limit iff `σ = ½`. The critical line is exactly the normalisation at which multiplicative
structure lives in the boundary at a fixed, nonzero cost, while additive structure leaves no
boundary at all. A finite presentation that discards its escaped cells discards the archimedean
place.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open BiarithmeticGeometry

/-! ### Escaped pairings and their cocycle -/

/-- The escaped pairing of `j ↦ aj + b`: the signed pairing on the cells absorbed by the horizon. -/
def escapedPairing (N : ℕ) (a : ℕ+) (b : ℕ) (v w : HorizonSpace N) : ℝ :=
  ∑ j : Fin (N + 1), if N < (a : ℕ) * j.val + b then v j * w j else 0

/-- The escaped pairing is the exact defect of the affine map. -/
theorem escapedPairing_eq_defect (N : ℕ) (a : ℕ+) (b : ℕ) (v w : HorizonSpace N) :
    escapedPairing N a b v w =
      horizonPairing N v w - horizonPairing N (horizonAffine N a b v) (horizonAffine N a b w) := by
  have h := horizonPairing_affine_add_boundary N a b v w
  rw [escapedPairing]
  linarith

/-- **The boundary cocycle.** The boundary of a composite is the boundary of the inner map plus the
transported boundary of the outer one. -/
theorem escapedPairing_comp (N : ℕ) (a c : ℕ+) (b d : ℕ) (v w : HorizonSpace N) :
    escapedPairing N (a * c) (a * d + b) v w =
      escapedPairing N c d v w +
        escapedPairing N a b (horizonAffine N c d v) (horizonAffine N c d w) := by
  have hcomp : ∀ u : HorizonSpace N, horizonAffine N (a * c) (a * d + b) u =
      horizonAffine N a b (horizonAffine N c d u) := fun u => by
    rw [← horizonAffine_comp]; rfl
  rw [escapedPairing_eq_defect, escapedPairing_eq_defect, escapedPairing_eq_defect, hcomp, hcomp]
  ring

/-- **`D_a U = U^a D_a` with its boundary.** Both orders realise `j ↦ aj + a`; they absorb the same
cells, attributed to different steps. -/
theorem escapedPairing_ring_relation (N : ℕ) (a : ℕ+) (v w : HorizonSpace N) :
    escapedPairing N 1 1 v w +
        escapedPairing N a 0 (horizonAffine N 1 1 v) (horizonAffine N 1 1 w) =
      escapedPairing N a 0 v w +
        escapedPairing N 1 a (horizonAffine N a 0 v) (horizonAffine N a 0 w) := by
  rw [← escapedPairing_comp, ← escapedPairing_comp]
  simp only [mul_one, one_mul, add_zero, mul_zero, zero_add]

/-! ### The weighted source and its escaped mass -/

/-- The source with weight `j^{−σ}` on the cells `j ≥ 1` and nothing at the origin. -/
def critSource (N : ℕ) (σ : ℝ) : HorizonSpace N := fun j =>
  if j.val = 0 then 0 else ((j.val : ℝ) ^ σ)⁻¹

/-- The escaped mass `Σ_{(N − b)/a < j ≤ N} j^{−2σ}`. -/
def escapedMass (N a b : ℕ) (σ : ℝ) : ℝ := ∑ j ∈ Ioc ((N - b) / a) N, ((j : ℝ) ^ (2 * σ))⁻¹

/-- A positive cell escapes exactly when it exceeds `(N − b)/a`. -/
theorem lt_mul_add_iff {N a b j : ℕ} (ha : 0 < a) (hj : 1 ≤ j) :
    N < a * j + b ↔ (N - b) / a < j := by
  rw [Nat.div_lt_iff_lt_mul ha]
  constructor <;> intro h
  · rcases le_or_gt b N with hb | hb
    · rw [Nat.sub_lt_iff_lt_add hb]; linarith [mul_comm a j]
    · rw [Nat.sub_eq_zero_of_le hb.le]; exact Nat.mul_pos hj ha
  · rcases le_or_gt b N with hb | hb
    · rw [Nat.sub_lt_iff_lt_add hb] at h; linarith [mul_comm a j]
    · omega

theorem critSource_mul_self {N : ℕ} {σ : ℝ} (j : Fin (N + 1)) (hj : j.val ≠ 0) :
    critSource N σ j * critSource N σ j = ((j.val : ℝ) ^ (2 * σ))⁻¹ := by
  have hj0 : (0 : ℝ) < j.val := by exact_mod_cast Nat.pos_of_ne_zero hj
  rw [critSource, if_neg hj, ← mul_inv, ← Real.rpow_add hj0]
  ring_nf

/-- **The escaped pairing of the weighted source is its escaped mass.** -/
theorem escapedPairing_critSource (N : ℕ) (a : ℕ+) (b : ℕ) (σ : ℝ) :
    escapedPairing N a b (critSource N σ) (critSource N σ) = escapedMass N a b σ := by
  simp only [escapedPairing, critSource]
  rw [escapedMass,
    Fin.sum_univ_eq_sum_range (fun j => if N < (a : ℕ) * j + b then
      (if j = 0 then (0 : ℝ) else ((j : ℝ) ^ σ)⁻¹) *
        (if j = 0 then (0 : ℝ) else ((j : ℝ) ^ σ)⁻¹) else 0) (N + 1)]
  rw [Finset.range_eq_Ico, ← Finset.sum_filter_add_sum_filter_not (Ico 0 (N + 1)) (· = 0)]
  have h0 : ∑ j ∈ (Ico 0 (N + 1)).filter (· = 0), (if N < (a : ℕ) * j + b then
      (if j = 0 then (0 : ℝ) else ((j : ℝ) ^ σ)⁻¹) *
        (if j = 0 then (0 : ℝ) else ((j : ℝ) ^ σ)⁻¹) else 0) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [(Finset.mem_filter.mp hj).2]; simp
  rw [h0, zero_add, Finset.sum_filter]
  rw [← Finset.sum_filter_add_sum_filter_not (Ico 0 (N + 1)) (fun j => (N - b) / (a : ℕ) < j)]
  have hrest : ∑ j ∈ (Ico 0 (N + 1)).filter (fun j => ¬ (N - b) / (a : ℕ) < j),
      (if ¬ j = 0 then (if N < (a : ℕ) * j + b then
        (if j = 0 then (0 : ℝ) else ((j : ℝ) ^ σ)⁻¹) *
          (if j = 0 then (0 : ℝ) else ((j : ℝ) ^ σ)⁻¹) else 0) else 0) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have hj' := (Finset.mem_filter.mp hj).2
      by_cases hj0 : j = 0
      · simp [hj0]
      · rw [if_pos hj0, if_neg]
        rw [lt_mul_add_iff a.pos (Nat.one_le_iff_ne_zero.mpr hj0)]
        exact hj'
  rw [hrest, add_zero, Finset.sum_filter]
  have hset : (Ico 0 (N + 1)).filter (fun j => (N - b) / (a : ℕ) < j) = Ioc ((N - b) / a) N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_filter, hset]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hj).1)
  have hj0 : j ≠ 0 := by omega
  have hesc : N < (a : ℕ) * j + b :=
    (lt_mul_add_iff a.pos hj1).mpr (Finset.mem_Ioc.mp hj).1
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  rw [if_pos hj0, if_pos hesc, if_neg hj0, ← mul_inv, ← Real.rpow_add hjpos]
  ring_nf

/-! ### Growth of the escaped index range -/

theorem div_le_self_sub {N a b : ℕ} : (N - b) / a ≤ N :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

theorem tendsto_escapeStart {a b : ℕ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N - b) / a) atTop atTop :=
  (Nat.tendsto_div_const_atTop ha.ne').comp (tendsto_sub_atTop_nat b)

/-- The horizon over the escape start tends to the multiplier. -/
theorem tendsto_ratio_escapeStart {a b : ℕ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) / ((N - b) / a : ℕ)) atTop (𝓝 a) := by
  have hM := tendsto_escapeStart (b := b) ha
  have hMr : Tendsto (fun N : ℕ => (((N - b) / a : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hM
  have hup : Tendsto (fun N : ℕ => (a : ℝ) + ((a : ℝ) + b) / (((N - b) / a : ℕ) : ℝ)) atTop
      (𝓝 a) := by
    have := (tendsto_const_nhds (x := ((a : ℝ) + b))).div_atTop hMr
    simpa using (tendsto_const_nhds (x := (a : ℝ))).add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hM.eventually_ge_atTop 1] with N hN
    have hMpos : (0 : ℝ) < ((N - b) / a : ℕ) := by exact_mod_cast hN
    rw [le_div_iff₀ hMpos]
    have h1 : a * ((N - b) / a) ≤ N := (Nat.mul_div_le _ _).trans (Nat.sub_le _ _)
    exact_mod_cast h1
  · filter_upwards [hM.eventually_ge_atTop 1] with N hN
    have hMpos : (0 : ℝ) < ((N - b) / a : ℕ) := by exact_mod_cast hN
    rw [div_le_iff₀ hMpos, add_mul, div_mul_cancel₀ _ hMpos.ne']
    have h2 : N - b < a * ((N - b) / a + 1) := by
      have := Nat.lt_mul_div_succ (N - b) ha
      linarith
    have h2' : a * ((N - b) / a + 1) = a * ((N - b) / a) + a := by ring
    have h3 : N < a * ((N - b) / a) + a + b := by
      generalize a * ((N - b) / a) = K at h2 h2' ⊢
      omega
    have h3' : (N : ℝ) < a * ((N - b) / a : ℕ) + a + b := by exact_mod_cast h3
    linarith

/-! ### The three regimes -/

/-- **At `σ = ½` the boundary of a dilation is `log a`.** -/
theorem tendsto_escapedMass_half {a b : ℕ} (ha : 0 < a) :
    Tendsto (fun N => escapedMass N a b (1 / 2)) atTop (𝓝 (Real.log a)) := by
  have hM := tendsto_escapeStart (b := b) ha
  have hharm : ∀ N, escapedMass N a b (1 / 2) =
      ((harmonic N : ℝ) - Real.log N) - ((harmonic ((N - b) / a) : ℝ) - Real.log ((N - b) / a : ℕ))
        + (Real.log N - Real.log ((N - b) / a : ℕ)) := by
    intro N
    have hsplit : Icc 1 N = Icc 1 ((N - b) / a) ∪ Ioc ((N - b) / a) N := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      have := div_le_self_sub (N := N) (a := a) (b := b)
      generalize (N - b) / a = M at this ⊢
      omega
    have hdisj : Disjoint (Icc 1 ((N - b) / a)) (Ioc ((N - b) / a) N) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
      generalize (N - b) / a = M at h1 h2
      omega
    have hH : (harmonic N : ℝ) = (harmonic ((N - b) / a) : ℝ) +
        ∑ j ∈ Ioc ((N - b) / a) N, ((j : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
      push_cast
      rw [hsplit, Finset.sum_union hdisj]
    rw [escapedMass]
    simp only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    linarith
  simp_rw [hharm]
  have hγN := Real.tendsto_harmonic_sub_log
  have hγM := Real.tendsto_harmonic_sub_log.comp hM
  have hlog : Tendsto (fun N : ℕ => Real.log N - Real.log ((N - b) / a : ℕ)) atTop
      (𝓝 (Real.log a)) := by
    have hpos : (0 : ℝ) < a := by exact_mod_cast ha
    have hlim := ((Real.continuousAt_log hpos.ne').tendsto).comp (tendsto_ratio_escapeStart
      (b := b) ha)
    refine hlim.congr' ?_
    filter_upwards [hM.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hN hN1
    have hMpos : (0 : ℝ) < ((N - b) / a : ℕ) := by exact_mod_cast hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    simp only [Function.comp_apply]
    rw [Real.log_div hNpos.ne' hMpos.ne']
  have := (hγN.sub hγM).add hlog
  simpa using this

/-- **Above `½` the boundary vanishes.** -/
theorem tendsto_escapedMass_of_half_lt {a b : ℕ} (ha : 0 < a) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Tendsto (fun N => escapedMass N a b σ) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun j => ((j : ℝ) ^ (2 * σ))⁻¹ with hf
  have hsum : Summable f := Real.summable_nat_rpow_inv.mpr (by linarith)
  have hf0 : ∀ j, 0 ≤ f j := fun j => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have htail := (tendsto_sum_nat_add f).comp
    ((tendsto_add_atTop_nat 1).comp (tendsto_escapeStart (b := b) ha))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun N => Finset.sum_nonneg fun j _ => hf0 j) fun N => ?_
  simp only [Function.comp_apply]
  rw [escapedMass, ← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
  calc ∑ k ∈ range ((N + 1) - ((N - b) / a + 1)), f ((N - b) / a + 1 + k)
      = ∑ k ∈ range ((N + 1) - ((N - b) / a + 1)), f (k + ((N - b) / a + 1)) :=
        Finset.sum_congr rfl fun k _ => by rw [add_comm]
    _ ≤ ∑' k, f (k + ((N - b) / a + 1)) :=
        ((summable_nat_add_iff _).mpr hsum).sum_le_tsum _ fun k _ => hf0 _

/-- **Below `½` the boundary of a dilation is unbounded.** -/
theorem tendsto_escapedMass_of_lt_half {a b : ℕ} (ha : 2 ≤ a) {σ : ℝ} (hσ : σ < 1 / 2) :
    Tendsto (fun N => escapedMass N a b σ) atTop atTop := by
  have hlow : ∀ N : ℕ, 1 ≤ N → ((N : ℝ) / 2) / ((N : ℝ) ^ (2 * σ) + 1) ≤ escapedMass N a b σ := by
    intro N hN
    have hcard : (N : ℝ) / 2 ≤ ((Ioc ((N - b) / a) N).card : ℝ) := by
      rw [Nat.card_Ioc]
      have h1 : (N - b) / a ≤ N / 2 :=
        (Nat.div_le_div_right (Nat.sub_le _ _)).trans (Nat.div_le_div_left ha (by norm_num))
      have h2 : (N : ℝ) / 2 ≤ N - ((N / 2 : ℕ) : ℝ) := by
        have := Nat.div_mul_le_self N 2
        have h' : ((N / 2 : ℕ) : ℝ) * 2 ≤ N := by exact_mod_cast this
        linarith
      have h3 : ((N - (N - b) / a : ℕ) : ℝ) = N - (((N - b) / a : ℕ) : ℝ) := by
        rw [Nat.cast_sub div_le_self_sub]
      rw [h3]
      have h4 : (((N - b) / a : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hden : 0 < (N : ℝ) ^ (2 * σ) + 1 := by positivity
    have hterm : ∀ j ∈ Ioc ((N - b) / a) N, ((N : ℝ) ^ (2 * σ) + 1)⁻¹ ≤ ((j : ℝ) ^ (2 * σ))⁻¹ := by
      intro j hj
      have hj1 : 1 ≤ j := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hj).1)
      have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
      have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hj).2
      refine inv_anti₀ (Real.rpow_pos_of_pos hjpos _) ?_
      rcases le_or_gt 0 σ with hσ0 | hσ0
      · have := Real.rpow_le_rpow hjpos.le hjN (by linarith : 0 ≤ 2 * σ)
        linarith
      · have := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hj1 : (1 : ℝ) ≤ j)
          (by linarith : 2 * σ ≤ 0)
        have := Real.rpow_nonneg (Nat.cast_nonneg N) (2 * σ)
        linarith
    calc ((N : ℝ) / 2) / ((N : ℝ) ^ (2 * σ) + 1)
        ≤ ((Ioc ((N - b) / a) N).card : ℝ) * ((N : ℝ) ^ (2 * σ) + 1)⁻¹ := by
          rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hden.le)
      _ = ∑ j ∈ Ioc ((N - b) / a) N, ((N : ℝ) ^ (2 * σ) + 1)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ escapedMass N a b σ := Finset.sum_le_sum hterm
  -- the lower bound tends to infinity
  have hgrow : Tendsto (fun N : ℕ => ((N : ℝ) / 2) / ((N : ℝ) ^ (2 * σ) + 1)) atTop atTop := by
    rcases le_or_gt 0 σ with hσ0 | hσ0
    · have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - 2 * σ) / 4) atTop atTop :=
        ((tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop).atTop_div_const
          (by norm_num)
      refine tendsto_atTop_mono' atTop ?_ hpow
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have hNs : (1 : ℝ) ≤ (N : ℝ) ^ (2 * σ) :=
        Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
      have hsplit : (N : ℝ) = (N : ℝ) ^ (1 - 2 * σ) * (N : ℝ) ^ (2 * σ) := by
        rw [← Real.rpow_add hNpos]; norm_num
      rw [le_div_iff₀ (by positivity)]
      have hp0 : 0 ≤ (N : ℝ) ^ (1 - 2 * σ) := Real.rpow_nonneg hNpos.le _
      calc (N : ℝ) ^ (1 - 2 * σ) / 4 * ((N : ℝ) ^ (2 * σ) + 1)
          ≤ (N : ℝ) ^ (1 - 2 * σ) / 4 * (2 * (N : ℝ) ^ (2 * σ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (N : ℝ) ^ (1 - 2 * σ) * (N : ℝ) ^ (2 * σ) / 2 := by ring
        _ = (N : ℝ) / 2 := by rw [← hsplit]
    · have hlin : Tendsto (fun N : ℕ => (N : ℝ) / 4) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
      refine tendsto_atTop_mono' atTop ?_ hlin
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNs : (N : ℝ) ^ (2 * σ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith)
      have hNs0 : 0 ≤ (N : ℝ) ^ (2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      rw [le_div_iff₀ (by positivity)]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
  exact tendsto_atTop_mono' atTop
    (by filter_upwards [eventually_ge_atTop 1] with N hN; exact hlow N hN) hgrow

/-- **Successor boundaries vanish at every positive weight.** -/
theorem tendsto_escapedMass_successor (b : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun N => escapedMass N 1 b σ) atTop (𝓝 0) := by
  have hbound : ∀ N : ℕ, b + 1 ≤ N →
      escapedMass N 1 b σ ≤ b * (((N - b : ℕ) : ℝ) ^ (2 * σ))⁻¹ := by
    intro N hN
    rw [escapedMass, Nat.div_one]
    have hterm : ∀ j ∈ Ioc (N - b) N, ((j : ℝ) ^ (2 * σ))⁻¹ ≤ (((N - b : ℕ) : ℝ) ^ (2 * σ))⁻¹ := by
      intro j hj
      have hj := (Finset.mem_Ioc.mp hj).1
      have hpos : (0 : ℝ) < ((N - b : ℕ) : ℝ) := by
        have : 0 < N - b := by omega
        exact_mod_cast this
      exact inv_anti₀ (Real.rpow_pos_of_pos hpos _)
        (Real.rpow_le_rpow hpos.le (by exact_mod_cast hj.le) (by linarith))
    calc _ ≤ ∑ j ∈ Ioc (N - b) N, (((N - b : ℕ) : ℝ) ^ (2 * σ))⁻¹ := Finset.sum_le_sum hterm
      _ = ((Ioc (N - b) N).card : ℝ) * (((N - b : ℕ) : ℝ) ^ (2 * σ))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ b * (((N - b : ℕ) : ℝ) ^ (2 * σ))⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))
          rw [Nat.card_Ioc]
          have : N - (N - b) = b := by omega
          rw [this]
  have hlim : Tendsto (fun N : ℕ => (b : ℝ) * (((N - b : ℕ) : ℝ) ^ (2 * σ))⁻¹) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_atTop (by linarith : 0 < 2 * σ)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat b))).inv_tendsto_atTop
    simpa using h.const_mul (b : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun N => Finset.sum_nonneg fun j _ =>
      inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · filter_upwards [eventually_ge_atTop (b + 1)] with N hN
    exact hbound N hN

/-- **The critical line is the unique horizon-uniform normalisation.** The escaped mass of a
dilation `a ≥ 2` converges to a finite nonzero limit iff `σ = ½`, and then the limit is `log a`. -/
theorem exists_pos_tendsto_escapedMass_iff {a b : ℕ} (ha : 2 ≤ a) (σ : ℝ) :
    (∃ c, 0 < c ∧ Tendsto (fun N => escapedMass N a b σ) atTop (𝓝 c)) ↔ σ = 1 / 2 := by
  have ha0 : 0 < a := by omega
  constructor
  · rintro ⟨c, hc, hlim⟩
    rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
    · exact absurd hlim (not_tendsto_nhds_of_tendsto_atTop (tendsto_escapedMass_of_lt_half ha hlt) c)
    · exact heq
    · have h0 := tendsto_escapedMass_of_half_lt (b := b) ha0 hgt
      exact absurd (tendsto_nhds_unique hlim h0) hc.ne'
  · rintro rfl
    refine ⟨Real.log a, Real.log_pos (by exact_mod_cast (by omega : 1 < a)), ?_⟩
    exact tendsto_escapedMass_half ha0

end GaloisForLFunctions.ArithmeticCorrelationGeometry
