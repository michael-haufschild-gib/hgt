import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMoebiusSigmaSumsDecay
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MoebiusBandAverageStepAndEnergyProfile
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The cofinal Möbius profile is asymptotically linear

`P(B) = lim_N Q_N((B+1)N)/N` (`cofinalMobiusQuadraticProfile`) is the cofinal quadratic energy of
the literal Möbius sieve on the linear horizon `(B+1)N`. This module determines its large-band law:

* `tendsto_cofinalBandSlope`: the band slopes `γ_t = P(t) − P(t−1)` converge to
  `κ = ρ Σ_{j≥1} S(j) log(1 + 1/j)`, `ρ = 6/π²`, `S(X) = Σ_{a,b≤X, (a,b)=1} μ(a)μ(b)/(σ(a)σ(b))`;
* `tendsto_cofinalMobiusQuadraticProfile_div`: `P(B)/B → κ`;
* `tendsto_sum_bandAverageStep`: the Buchstab band averages obey the sum rule
  `Σ_{b≥1} A(b)/(b(b+1)) = −κ`.

Mechanism. The slope is the mean square of the complementary truncation `Σ_{q|k, q≤t} μ(k/q)`, an
explicit finite sum `Σ_{q,r≤t} D(q,r)/[q,r]` (`cofinalBandSlope`). Writing `q = g b`, `r = g a`
with `(a,b) = 1`, the coprime-squarefree densities become `ρ w(a)w(b)/g`, `w = μ/σ`, so
`γ_t = ρ Σ_{g≤t} S(⌊t/g⌋)/g` (`cofinalBandSlope_eq`). Since `S(X) = O(log^{-4} X)`
(`exists_abs_coprimePairMoebiusSigmaSum_le`), the harmonic average of `S` converges to
`Σ_j S(j) log(1+1/j)`: the fibre `⌊t/g⌋ = j` carries harmonic mass `→ log(1+1/j)`
(`tendsto_harmonicFibre`), dominated by `3/j` below `√t`, and the fibres above `√t` cost
`O(log^{-3} t)` (`tendsto_sum_div_of_log_decay`).

The limits `N → ∞` then `B → ∞` are taken in this order; the band averages themselves change sign
(`A(10) > 0`), so the sum rule is not a sign statement.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### A log-squared series -/

/-- `log(j/(j-1)) ≥ 1/j`. -/
theorem inv_le_log_div {j : ℕ} (hj : 2 ≤ j) :
    (j : ℝ)⁻¹ ≤ Real.log j - Real.log ((j - 1 : ℕ) : ℝ) := by
  have hj1 : (1 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - 1)
  have hjR : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hjpos : (0 : ℝ) < j := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((j - 1 : ℕ) : ℝ) / j by positivity)
  rw [Real.log_div (by positivity) hjpos.ne', hjR] at h
  rw [hjR]
  have : ((j : ℝ) - 1) / j - 1 = -(j : ℝ)⁻¹ := by field_simp; ring
  linarith

/-- `1/(j (1 + log j)²) ≤ φ(j-1) - φ(j)` with `φ(x) = 1/(1 + log x)`. -/
theorem term_le_telescope {j : ℕ} (hj : 2 ≤ j) :
    ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ ≤
      (1 + Real.log ((j - 1 : ℕ) : ℝ))⁻¹ - (1 + Real.log j)⁻¹ := by
  have hj1 : (1 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - 1)
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have ha := Real.log_nonneg hj1
  have hb := Real.log_nonneg hjR
  have hle : Real.log ((j - 1 : ℕ) : ℝ) ≤ Real.log j :=
    Real.log_le_log (by linarith) (by exact_mod_cast (by omega : j - 1 ≤ j))
  have hd := inv_le_log_div hj
  have hpos : (0 : ℝ) < j := by linarith
  rw [inv_sub_inv (by linarith) (by linarith)]
  rw [show (1 + Real.log j - (1 + Real.log ((j - 1 : ℕ) : ℝ))) =
    Real.log j - Real.log ((j - 1 : ℕ) : ℝ) by ring]
  rw [mul_inv, ← div_eq_mul_inv, ← one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 1 ≤ (j : ℝ) * (Real.log j - Real.log ((j - 1 : ℕ) : ℝ)) := by
    rw [inv_le_iff_one_le_mul₀' hpos] at hd; linarith
  nlinarith [mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ 1 + Real.log j)]

/-- `Σ_j 1/(j (1 + log j)²) < ∞`. -/
theorem summable_inv_mul_one_add_log_sq :
    Summable (fun j : ℕ => ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹) := by
  have hnn : ∀ j : ℕ, 0 ≤ ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have := Real.log_nonneg this
      positivity
  refine summable_of_sum_range_le hnn (c := 2) fun N => ?_
  have key : ∀ N : ℕ, ∑ j ∈ range (N + 2), ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ ≤
      2 - (1 + Real.log ((N + 1 : ℕ) : ℝ))⁻¹ := by
    intro N
    induction N with
    | zero => norm_num [Finset.sum_range_succ]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have ht := term_le_telescope (j := N + 2) (by omega)
      rw [show N + 2 - 1 = N + 1 by omega] at ht
      push_cast at ht ih ⊢
      rw [show ((N : ℝ) + 1 + 1) = (N : ℝ) + 2 by ring]
      linarith
  rcases N with _ | _ | N
  · simp
  · norm_num
  · have h := key N
    have hpos : 0 ≤ (1 + Real.log ((N + 1 : ℕ) : ℝ))⁻¹ := by
      have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
      have := Real.log_nonneg this
      positivity
    linarith

/-! ### Harmonic fibres -/

/-- `Σ_{g ∈ (a, b]} 1/g = H(b) - H(a)`. -/
theorem sum_Ioc_inv_eq_harmonic_sub {a b : ℕ} (hab : a ≤ b) :
    ∑ g ∈ Ioc a b, (g : ℝ)⁻¹ = (harmonic b : ℝ) - harmonic a := by
  have hsplit : Icc 1 b = Icc 1 a ∪ Ioc a b := by
    ext g; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 a) (Ioc a b) := by
    rw [disjoint_left]; intro g h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc, hsplit, sum_union hdisj]
  push_cast
  ring

/-- The fibre weight `A_j(t) = Σ_{g ≤ t, ⌊t/g⌋ = j} 1/g`. -/
def harmonicFibre (t j : ℕ) : ℝ := ∑ g ∈ Icc 1 t with t / g = j, (g : ℝ)⁻¹

/-- The fibre `⌊t/g⌋ = j` is the interval `(⌊t/(j+1)⌋, ⌊t/j⌋]`. -/
theorem filter_div_eq_Ioc {t j : ℕ} (hj : 1 ≤ j) :
    (Icc 1 t).filter (fun g => t / g = j) = Ioc (t / (j + 1)) (t / j) := by
  ext g
  simp only [mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hg1, -⟩, h⟩
    have h1 : j * g ≤ t := by rw [← h]; exact Nat.div_mul_le_self t g
    have h2 : t < j * g + g := by rw [← h]; exact Nat.lt_div_mul_add (by omega)
    exact ⟨(Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith),
      (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)⟩
  · rintro ⟨h1, h2⟩
    have ht : t < g * (j + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp h1
    have hg1 : 1 ≤ g := by
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · simp at ht
      · exact hg
    have hjg : g * j ≤ t := (Nat.le_div_iff_mul_le (by omega)).mp h2
    refine ⟨⟨hg1, by nlinarith⟩, le_antisymm ?_ ?_⟩
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hg1).mpr (by nlinarith))
    · exact (Nat.le_div_iff_mul_le hg1).mpr (by nlinarith)

theorem harmonicFibre_eq {t j : ℕ} (hj : 1 ≤ j) :
    harmonicFibre t j = (harmonic (t / j) : ℝ) - harmonic (t / (j + 1)) := by
  rw [harmonicFibre, filter_div_eq_Ioc hj,
    sum_Ioc_inv_eq_harmonic_sub (Nat.div_le_div_left (by omega) (by omega))]

theorem harmonicFibre_nonneg (t j : ℕ) : 0 ≤ harmonicFibre t j :=
  sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

/-- `A_j(t) ≤ 3/j` once `j² ≤ t`. -/
theorem harmonicFibre_le {t j : ℕ} (hj : 1 ≤ j) (hjt : j * j ≤ t) :
    harmonicFibre t j ≤ 3 / j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht0 : 0 < t := by nlinarith
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  rw [harmonicFibre, filter_div_eq_Ioc hj]
  have hpt : ∀ g ∈ Ioc (t / (j + 1)) (t / j), (g : ℝ)⁻¹ ≤ ((j : ℝ) + 1) / t := by
    intro g hg
    have h1 := (Nat.div_lt_iff_lt_mul (by omega)).mp (mem_Ioc.mp hg).1
    have hg0 : (0 : ℝ) < g := by
      have : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
      exact_mod_cast this
    rw [inv_le_comm₀ hg0 (by positivity), inv_div, div_le_iff₀ (by positivity)]
    exact_mod_cast h1.le
  calc ∑ g ∈ Ioc (t / (j + 1)) (t / j), (g : ℝ)⁻¹
      ≤ ∑ _g ∈ Ioc (t / (j + 1)) (t / j), ((j : ℝ) + 1) / t := sum_le_sum hpt
    _ = (#(Ioc (t / (j + 1)) (t / j)) : ℝ) * (((j : ℝ) + 1) / t) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((t : ℝ) / (j * (j + 1)) + 1) * (((j : ℝ) + 1) / t) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Nat.card_Ioc, Nat.cast_sub (Nat.div_le_div_left (by omega) (by omega))]
        have hu : ((t / j : ℕ) : ℝ) ≤ t / j := Nat.cast_div_le
        have hl : (t : ℝ) / (j + 1) - 1 ≤ ((t / (j + 1) : ℕ) : ℝ) := by
          have h := Nat.lt_div_mul_add (a := t) (b := j + 1) (by omega)
          have h' : (t : ℝ) < ((t / (j + 1) : ℕ) : ℝ) * (j + 1) + (j + 1) := by exact_mod_cast h
          rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
          linarith
        have he : (t : ℝ) / j - t / (j + 1) = t / (j * (j + 1)) := by field_simp; ring
        linarith
    _ = 1 / j + ((j : ℝ) + 1) / t := by field_simp
    _ ≤ 1 / j + 2 / j := by
        have h2 : ((j : ℝ) + 1) / t ≤ 2 / j := by
          rw [div_le_div_iff₀ htR (by positivity)]
          have : (j : ℝ) * j ≤ t := by exact_mod_cast hjt
          nlinarith
        linarith
    _ = 3 / j := by ring

/-- `⌊t/j⌋/t → 1/j`. -/
theorem tendsto_natDiv_div_self {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun t : ℕ => ((t / j : ℕ) : ℝ) / t) atTop (𝓝 (1 / j)) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hlim : Tendsto (fun t : ℕ => (1 : ℝ) / j - 1 / t) atTop (𝓝 (1 / j)) := by
    have := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / j)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have h := Nat.lt_div_mul_add (a := t) (b := j) (by omega)
    have h' : (t : ℝ) < ((t / j : ℕ) : ℝ) * j + j := by exact_mod_cast h
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', div_sub_div _ _ hjR.ne' htR.ne',
      div_le_div_iff₀ (by positivity) htR]
    nlinarith
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    rw [div_le_div_iff₀ htR hjR, one_mul]
    have : ((t / j : ℕ) : ℝ) * j ≤ t := by exact_mod_cast Nat.div_mul_le_self t j
    linarith

/-- **Fibre weights.** `A_j(t) → log(1 + 1/j)`. -/
theorem tendsto_harmonicFibre {j : ℕ} (hj : 1 ≤ j) :
    Tendsto (fun t => harmonicFibre t j) atTop (𝓝 (Real.log (1 + 1 / (j : ℝ)))) := by
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hH := Real.tendsto_harmonic_sub_log
  have h1 := hH.comp (Nat.tendsto_div_const_atTop (by omega : j ≠ 0))
  have h2 := hH.comp (Nat.tendsto_div_const_atTop (by omega : j + 1 ≠ 0))
  have hr : Tendsto (fun t : ℕ => (((t / j : ℕ) : ℝ) / t) / (((t / (j + 1) : ℕ) : ℝ) / t)) atTop
      (𝓝 ((1 / j) / (1 / ((j + 1 : ℕ) : ℝ)))) :=
    (tendsto_natDiv_div_self hj).div (tendsto_natDiv_div_self (by omega)) (by positivity)
  have hval : (1 / (j : ℝ)) / (1 / ((j + 1 : ℕ) : ℝ)) = 1 + 1 / j := by
    push_cast; field_simp
  rw [hval] at hr
  have hlog := (Real.continuousAt_log (by positivity : (1 + 1 / (j : ℝ)) ≠ 0)).tendsto.comp hr
  have hsum := (h1.sub h2).add hlog
  rw [sub_self, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (j + 1)] with t ht
  have ha : 0 < t / j := Nat.div_pos (by omega) (by omega)
  have hb : 0 < t / (j + 1) := Nat.div_pos ht (by omega)
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have haR : (0 : ℝ) < ((t / j : ℕ) : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < ((t / (j + 1) : ℕ) : ℝ) := by exact_mod_cast hb
  simp only [Function.comp, harmonicFibre_eq hj]
  rw [div_div_div_cancel_right₀ htR.ne', Real.log_div haR.ne' hbR.ne']
  ring

/-! ### Harmonic averages of log-decaying sequences -/

/-- Fibre decomposition: `Σ_{g ≤ t} f(⌊t/g⌋)/g = Σ_{j ≤ t} f(j) A_j(t)`. -/
theorem sum_div_eq_sum_harmonicFibre (f : ℕ → ℝ) (t : ℕ) :
    ∑ g ∈ Icc 1 t, f (t / g) / g = ∑ j ∈ Icc 1 t, f j * harmonicFibre t j := by
  rw [← sum_fiberwise_of_maps_to (s := Icc 1 t) (t := Icc 1 t) (g := fun g => t / g)
    (fun g hg => by
      obtain ⟨hg1, hgt⟩ := mem_Icc.mp hg
      exact mem_Icc.mpr ⟨(Nat.one_le_div_iff (by omega)).mpr hgt, Nat.div_le_self t g⟩)]
  refine sum_congr rfl fun j _ => ?_
  rw [harmonicFibre, mul_sum]
  refine sum_congr rfl fun g hg => ?_
  rw [(mem_filter.mp hg).2, div_eq_mul_inv]

theorem sum_harmonicFibre (t : ℕ) : ∑ j ∈ Icc 1 t, harmonicFibre t j = (harmonic t : ℝ) := by
  have h := sum_div_eq_sum_harmonicFibre (fun _ => 1) t
  simp only [one_mul, one_div] at h
  rw [← h, harmonic_eq_sum_Icc]
  push_cast
  rfl

/-- **Harmonic averages.** If `|f X| ≤ C (1 + log X)^{-4}` for `X ≥ 1`, then
`Σ_{g ≤ t} f(⌊t/g⌋)/g → Σ_j f(j) log(1 + 1/j)`. -/
theorem tendsto_sum_div_of_log_decay {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ X : ℕ, 1 ≤ X → |f X| ≤ C / (1 + Real.log X) ^ 4) :
    Tendsto (fun t : ℕ => ∑ g ∈ Icc 1 t, f (t / g) / g) atTop
      (𝓝 (∑' j : ℕ, f j * Real.log (1 + 1 / (j : ℝ)))) := by
  have hC0 : 0 ≤ C := by
    have h1 := hf 1 le_rfl
    rw [Nat.cast_one, Real.log_one, add_zero, one_pow, div_one] at h1
    exact (abs_nonneg _).trans h1
  set F : ℕ → ℕ → ℝ := fun t j =>
    if j ∈ Icc 1 (Nat.sqrt t) then f j * harmonicFibre t j else 0 with hF
  set G : ℕ → ℝ := fun j => 3 * C * ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ with hG
  -- the head is a tsum
  have hhead : ∀ t : ℕ, ∑ j ∈ Icc 1 t with j ≤ Nat.sqrt t, f j * harmonicFibre t j =
      ∑' j, F t j := by
    intro t
    have hset : (Icc 1 t).filter (· ≤ Nat.sqrt t) = Icc 1 (Nat.sqrt t) := by
      ext j; simp only [mem_filter, mem_Icc]
      have := Nat.sqrt_le_self t
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans this⟩, h2⟩
    rw [hset, tsum_eq_sum (s := Icc 1 (Nat.sqrt t)) (fun j hj => by simp only [hF]; rw [if_neg hj])]
    exact sum_congr rfl fun j hj => by simp only [hF]; rw [if_pos hj]
  -- dominated convergence for the head
  have hheadlim : Tendsto (fun t => ∑' j, F t j) atTop
      (𝓝 (∑' j : ℕ, f j * Real.log (1 + 1 / (j : ℝ)))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := G)
      ((summable_inv_mul_one_add_log_sq).mul_left (3 * C)) ?_ ?_
    · intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp only [hF, mem_Icc, Nat.cast_zero, div_zero, add_zero, Real.log_one, mul_zero]
        simp
      · refine ((tendsto_harmonicFibre hj).const_mul (f j)).congr' ?_
        filter_upwards [eventually_ge_atTop (j * j)] with t ht
        simp only [hF]
        rw [if_pos (mem_Icc.mpr ⟨hj, Nat.le_sqrt.mpr ht⟩)]
    · refine Eventually.of_forall fun t j => ?_
      simp only [hF, hG]
      split_ifs with hj
      · obtain ⟨hj1, hjs⟩ := mem_Icc.mp hj
        have hjt : j * j ≤ t := Nat.le_sqrt.mp hjs
        have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        have hl := Real.log_nonneg hjR
        have hA := harmonicFibre_le hj1 hjt
        have hA0 := harmonicFibre_nonneg t j
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hA0]
        have hfj := hf j hj1
        have h4 : (1 + Real.log j) ^ 2 ≤ (1 + Real.log j) ^ 4 := by
          have : 1 ≤ (1 + Real.log j) ^ 2 := by nlinarith
          nlinarith
        calc |f j| * harmonicFibre t j ≤ C / (1 + Real.log j) ^ 4 * (3 / j) :=
              mul_le_mul hfj hA hA0 (by positivity)
          _ ≤ C / (1 + Real.log j) ^ 2 * (3 / j) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact div_le_div_of_nonneg_left hC0 (by positivity) h4
          _ = 3 * C * ((j : ℝ) * (1 + Real.log j) ^ 2)⁻¹ := by field_simp
      · simp only [norm_zero]
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simp
        · have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj0
          have := Real.log_nonneg hjR
          positivity
  -- the tail vanishes
  have htail : Tendsto (fun t : ℕ => ∑ j ∈ Icc 1 t with ¬ j ≤ Nat.sqrt t,
      f j * harmonicFibre t j) atTop (𝓝 0) := by
    have hbound : ∀ t : ℕ, 1 ≤ t → |∑ j ∈ Icc 1 t with ¬ j ≤ Nat.sqrt t, f j * harmonicFibre t j| ≤
        16 * C / (1 + Real.log t) ^ 3 := by
      intro t ht
      have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have hlt := Real.log_nonneg htR
      set s := Nat.sqrt t
      have hsR : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos s
      have hls := Real.log_nonneg hsR
      -- (1 + log(s+1)) ≥ (1 + log t)/2
      have hsq : (t : ℝ) < ((s + 1 : ℕ) : ℝ) ^ 2 := by
        have := Nat.lt_succ_sqrt' t
        exact_mod_cast (by nlinarith : t < (s + 1) ^ 2)
      have hlog2 : Real.log t ≤ 2 * Real.log ((s + 1 : ℕ) : ℝ) := by
        rw [← Real.log_rpow (by positivity), Real.rpow_two]
        exact Real.log_le_log (by positivity) hsq.le
      have hhalf : (1 + Real.log t) / 2 ≤ 1 + Real.log ((s + 1 : ℕ) : ℝ) := by linarith
      have hpt : ∀ j ∈ (Icc 1 t).filter (fun j => ¬ j ≤ s), |f j * harmonicFibre t j| ≤
          C / (1 + Real.log ((s + 1 : ℕ) : ℝ)) ^ 4 * harmonicFibre t j := by
        intro j hj
        obtain ⟨hjI, hjs⟩ := mem_filter.mp hj
        have hj1 := (mem_Icc.mp hjI).1
        rw [abs_mul, abs_of_nonneg (harmonicFibre_nonneg t j)]
        apply mul_le_mul_of_nonneg_right _ (harmonicFibre_nonneg t j)
        refine (hf j hj1).trans (div_le_div_of_nonneg_left hC0 (by positivity) ?_)
        have : ((s + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast (by omega : s + 1 ≤ j)
        have := Real.log_le_log (by positivity) this
        exact pow_le_pow_left₀ (by linarith) (by linarith) 4
      calc |∑ j ∈ Icc 1 t with ¬ j ≤ s, f j * harmonicFibre t j|
          ≤ ∑ j ∈ Icc 1 t with ¬ j ≤ s, |f j * harmonicFibre t j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Icc 1 t with ¬ j ≤ s,
              C / (1 + Real.log ((s + 1 : ℕ) : ℝ)) ^ 4 * harmonicFibre t j := sum_le_sum hpt
        _ ≤ ∑ j ∈ Icc 1 t, C / (1 + Real.log ((s + 1 : ℕ) : ℝ)) ^ 4 * harmonicFibre t j :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ =>
              mul_nonneg (by positivity) (harmonicFibre_nonneg t j)
        _ = C / (1 + Real.log ((s + 1 : ℕ) : ℝ)) ^ 4 * harmonic t := by
            rw [← mul_sum, sum_harmonicFibre]
        _ ≤ C / ((1 + Real.log t) / 2) ^ 4 * (1 + Real.log t) := by
            have hH0 : (0 : ℝ) ≤ harmonic t := by
              rw [harmonic_eq_sum_Icc]; push_cast; exact sum_nonneg fun i _ => by positivity
            have hq0 : 0 ≤ C / ((1 + Real.log t) / 2) ^ 4 := div_nonneg hC0 (by positivity)
            apply mul_le_mul _ (harmonic_le_one_add_log t) hH0 hq0
            exact div_le_div_of_nonneg_left hC0 (by positivity)
              (pow_le_pow_left₀ (by positivity) hhalf 4)
        _ = 16 * C / (1 + Real.log t) ^ 3 := by field_simp; ring
    have hlim : Tendsto (fun t : ℕ => 16 * C / (1 + Real.log t) ^ 3) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℕ => 1 + Real.log t) atTop atTop :=
        tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      have h3 := (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp h1
      simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp h3).const_mul (16 * C)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with t ht
    exact hbound t ht
  -- assemble
  have hsum := hheadlim.add htail
  rw [add_zero] at hsum
  refine hsum.congr' (Eventually.of_forall fun t => ?_)
  simp only
  rw [sum_div_eq_sum_harmonicFibre, ← hhead t, sum_filter_add_sum_filter_not]


/-! ### The band slope -/

/-- The band slope `γ_t = Σ_{q,r ≤ t} D(q,r)/[q,r]`: the mean square of the complementary
truncation `Σ_{q ∣ k, q ≤ t} μ(k/q)` over the band `(tN, (t+1)N]`. -/
def cofinalBandSlope (t : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 t, ∑ r ∈ Icc 1 t,
    moebiusDilationPairDensity (r / Nat.gcd q r) (q / Nat.gcd q r) / Nat.lcm q r

/-- `P(t+1) = P(t) + γ_{t+1}`: pairs with `max(q,r) = t+1` enter with weight zero. -/
theorem cofinalMobiusQuadraticProfile_succ (t : ℕ) :
    cofinalMobiusQuadraticProfile (t + 1) =
      cofinalMobiusQuadraticProfile t + cofinalBandSlope (t + 1) := by
  set w : ℕ → ℕ → ℝ := fun q r =>
    moebiusDilationPairDensity (r / Nat.gcd q r) (q / Nat.gcd q r) / Nat.lcm q r with hw
  have hP : ∀ B : ℕ, cofinalMobiusQuadraticProfile B =
      ∑ q ∈ Icc 1 B, ∑ r ∈ Icc 1 B, ((B : ℝ) + 1 - (max q r : ℕ)) * w q r := by
    intro B
    unfold cofinalMobiusQuadraticProfile
    refine sum_congr rfl fun q _ => sum_congr rfl fun r _ => ?_
    simp only [hw]; ring
  have hzero : ∀ q r : ℕ, max q r = t + 1 → ((t : ℝ) + 1 - (max q r : ℕ)) * w q r = 0 := by
    intro q r h; rw [h]; push_cast; ring
  have hdrop : ∑ q ∈ Icc 1 (t + 1), ∑ r ∈ Icc 1 (t + 1), ((t : ℝ) + 1 - (max q r : ℕ)) * w q r =
      ∑ q ∈ Icc 1 t, ∑ r ∈ Icc 1 t, ((t : ℝ) + 1 - (max q r : ℕ)) * w q r := by
    rw [sum_Icc_succ_top (by omega)]
    have hlast : ∑ r ∈ Icc 1 (t + 1), ((t : ℝ) + 1 - (max (t + 1) r : ℕ)) * w (t + 1) r = 0 :=
      sum_eq_zero fun r hr => hzero _ _ (max_eq_left (mem_Icc.mp hr).2)
    rw [hlast, add_zero]
    refine sum_congr rfl fun q hq => ?_
    rw [sum_Icc_succ_top (by omega), hzero q (t + 1) (max_eq_right (by
      have := (mem_Icc.mp hq).2; omega)), add_zero]
  rw [hP, hP, ← hdrop, cofinalBandSlope, ← sum_add_distrib]
  refine sum_congr rfl fun q _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  simp only [hw]
  push_cast
  ring

theorem cofinalMobiusQuadraticProfile_eq_sum (B : ℕ) :
    cofinalMobiusQuadraticProfile B = ∑ t ∈ range B, cofinalBandSlope (t + 1) := by
  induction B with
  | zero => simp [cofinalMobiusQuadraticProfile_zero]
  | succ B ih => rw [cofinalMobiusQuadraticProfile_succ, ih, Finset.sum_range_succ]

/-! ### The slope in Möbius–divisor-sum coordinates -/

/-- For squarefree `a`, `∏_{p ∣ a} p/(p+1) = a/σ(a)`. -/
theorem prod_primeFactors_div_succ_eq {a : ℕ} (ha : Squarefree a) :
    ∏ p ∈ a.primeFactors, (p : ℝ) / ((p : ℝ) + 1) = (a : ℝ) / (ArithmeticFunction.sigma 1 a : ℝ) := by
  have hprod : ∏ p ∈ a.primeFactors, p = a := Nat.prod_primeFactors_of_squarefree ha
  have hσ : ArithmeticFunction.sigma 1 a = ∏ p ∈ a.primeFactors, (p + 1) := by
    conv_lhs => rw [← hprod]
    rw [isMultiplicative_sigma.map_prod_of_prime _ (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    refine prod_congr rfl fun p hp => ?_
    have h1 := sigma_one_apply_prime_pow (i := 1) (Nat.prime_of_mem_primeFactors hp)
    rw [pow_one] at h1
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [prod_div_distrib, hσ]
  push_cast
  rw [← Nat.cast_prod, hprod]

/-- `D(a,b)/(g a b) = ρ w(a) w(b)/g` on coprime `a, b`. -/
theorem moebiusDilationPairDensity_div {a b g : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a)
    (hb : 0 < b) :
    moebiusDilationPairDensity a b / ((g : ℝ) * a * b) =
      RHTower.Sieve.squarefreeDensity * (moebiusSigma a * moebiusSigma b) / g := by
  unfold moebiusDilationPairDensity coprimeSquarefreeDensity moebiusSigma moebiusReal
  by_cases hsa : Squarefree a
  · by_cases hsb : Squarefree b
    · rw [Nat.Coprime.primeFactors_mul hab,
        prod_union (Nat.Coprime.disjoint_primeFactors hab),
        prod_primeFactors_div_succ_eq hsa, prod_primeFactors_div_succ_eq hsb]
      have hσa := sigma_one_pos ha.ne'
      have hσb := sigma_one_pos hb.ne'
      have haR : (0 : ℝ) < a := by exact_mod_cast ha
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · simp
      · have hgR : (0 : ℝ) < g := by exact_mod_cast hg
        field_simp
    · simp [moebius_eq_zero_of_not_squarefree hsb]
  · simp [moebius_eq_zero_of_not_squarefree hsa]

/-- Gcd parametrization of pairs: `(q, r) = (g b, g a)` with `(a, b) = 1`. -/
theorem sum_gcd_reindex (t : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    ∑ q ∈ Icc 1 t, ∑ r ∈ Icc 1 t, F (Nat.gcd q r) (r / Nat.gcd q r) (q / Nat.gcd q r) =
      ∑ g ∈ Icc 1 t, ∑ a ∈ Icc 1 (t / g), ∑ b ∈ Icc 1 (t / g),
        if Nat.Coprime a b then F g a b else 0 := by
  rw [← sum_product' (Icc 1 t) (Icc 1 t)
    (fun q r => F (Nat.gcd q r) (r / Nat.gcd q r) (q / Nat.gcd q r))]
  have hrhs : ∀ g ∈ Icc 1 t, ∑ a ∈ Icc 1 (t / g), ∑ b ∈ Icc 1 (t / g),
      (if Nat.Coprime a b then F g a b else 0) =
      ∑ x ∈ (Icc 1 (t / g) ×ˢ Icc 1 (t / g)).filter (fun x => Nat.Coprime x.1 x.2),
        F g x.1 x.2 := by
    intro g _
    rw [sum_filter, ← sum_product' (Icc 1 (t / g)) (Icc 1 (t / g))
      (fun a b => if Nat.Coprime a b then F g a b else 0)]
  rw [sum_congr rfl hrhs, sum_sigma']
  refine sum_nbij' (fun x => ⟨Nat.gcd x.1 x.2, (x.2 / Nat.gcd x.1 x.2, x.1 / Nat.gcd x.1 x.2)⟩)
    (fun y => (y.1 * y.2.2, y.1 * y.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨q, r⟩ hx
    simp only [mem_product, mem_Icc] at hx
    obtain ⟨⟨hq1, hqt⟩, hr1, hrt⟩ := hx
    have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r (by omega)
    have hgq := Nat.gcd_dvd_left q r
    have hgr := Nat.gcd_dvd_right q r
    simp only [mem_sigma, mem_filter, mem_product, mem_Icc]
    refine ⟨⟨hg, (Nat.le_of_dvd (by omega) hgq).trans hqt⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hgr) hg
    · exact Nat.div_le_div_right hrt
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hgq) hg
    · exact Nat.div_le_div_right hqt
    · rw [Nat.gcd_comm q r]
      exact Nat.coprime_div_gcd_div_gcd (by rw [Nat.gcd_comm]; exact hg)
  · rintro ⟨g, a, b⟩ hy
    simp only [mem_sigma, mem_filter, mem_product, mem_Icc] at hy
    obtain ⟨⟨hg1, hgt⟩, ⟨⟨ha1, hat⟩, hb1, hbt⟩, hab⟩ := hy
    simp only [mem_product, mem_Icc]
    have h1 : g * b ≤ t := (Nat.mul_le_mul_left g hbt).trans (Nat.mul_div_le t g)
    have h2 : g * a ≤ t := (Nat.mul_le_mul_left g hat).trans (Nat.mul_div_le t g)
    exact ⟨⟨Nat.mul_pos hg1 hb1, h1⟩, Nat.mul_pos hg1 ha1, h2⟩
  · rintro ⟨q, r⟩ hx
    simp only [mem_product, mem_Icc] at hx
    show (Nat.gcd q r * (q / Nat.gcd q r), Nat.gcd q r * (r / Nat.gcd q r)) = (q, r)
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left q r), Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)]
  · rintro ⟨g, a, b⟩ hy
    simp only [mem_sigma, mem_filter, mem_product, mem_Icc] at hy
    obtain ⟨⟨hg1, -⟩, -, hab⟩ := hy
    have hgcd : Nat.gcd (g * b) (g * a) = g := by
      rw [Nat.gcd_mul_left, Nat.gcd_comm, hab, mul_one]
    show (⟨Nat.gcd (g * b) (g * a), (g * a / Nat.gcd (g * b) (g * a),
      g * b / Nat.gcd (g * b) (g * a))⟩ : (_ : ℕ) × ℕ × ℕ) = ⟨g, (a, b)⟩
    rw [hgcd, Nat.mul_div_cancel_left _ hg1, Nat.mul_div_cancel_left _ hg1]
  · rintro ⟨q, r⟩ _
    rfl

/-- **The slope in `μ/σ` coordinates.** `γ_t = ρ Σ_{g ≤ t} S(⌊t/g⌋)/g`. -/
theorem cofinalBandSlope_eq (t : ℕ) :
    cofinalBandSlope t = RHTower.Sieve.squarefreeDensity *
      ∑ g ∈ Icc 1 t, coprimePairMoebiusSigmaSum (t / g) / g := by
  have hpt : ∀ q ∈ Icc 1 t, ∀ r ∈ Icc 1 t,
      moebiusDilationPairDensity (r / Nat.gcd q r) (q / Nat.gcd q r) / Nat.lcm q r =
        RHTower.Sieve.squarefreeDensity *
          (moebiusSigma (r / Nat.gcd q r) * moebiusSigma (q / Nat.gcd q r)) / Nat.gcd q r := by
    intro q hq r hr
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    have hr0 : 0 < r := (mem_Icc.mp hr).1
    have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq0
    have hcop : Nat.Coprime (r / Nat.gcd q r) (q / Nat.gcd q r) := by
      rw [Nat.gcd_comm q r]; exact Nat.coprime_div_gcd_div_gcd (by rw [Nat.gcd_comm]; exact hg)
    have hlcm : (Nat.lcm q r : ℝ) =
        (Nat.gcd q r : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ) := by
      have h1 : Nat.gcd q r * Nat.lcm q r = q * r := Nat.gcd_mul_lcm q r
      have h2 : Nat.gcd q r * (r / Nat.gcd q r) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
      have h3 : Nat.gcd q r * (q / Nat.gcd q r) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
      have hgR : (0 : ℝ) < Nat.gcd q r := by exact_mod_cast hg
      have h1R : (Nat.gcd q r : ℝ) * Nat.lcm q r = q * r := by exact_mod_cast h1
      have h2R : (Nat.gcd q r : ℝ) * ((r / Nat.gcd q r : ℕ) : ℝ) = r := by exact_mod_cast h2
      have h3R : (Nat.gcd q r : ℝ) * ((q / Nat.gcd q r : ℕ) : ℝ) = q := by exact_mod_cast h3
      apply mul_left_cancel₀ hgR.ne'
      rw [h1R, ← h2R, ← h3R]
      ring
    rw [hlcm, moebiusDilationPairDensity_div hcop
      (Nat.div_pos (Nat.le_of_dvd hr0 (Nat.gcd_dvd_right q r)) hg)
      (Nat.div_pos (Nat.le_of_dvd hq0 (Nat.gcd_dvd_left q r)) hg)]
  unfold cofinalBandSlope
  rw [sum_congr rfl fun q hq => sum_congr rfl fun r hr => hpt q hq r hr,
    sum_gcd_reindex t (fun g a b => RHTower.Sieve.squarefreeDensity *
      (moebiusSigma a * moebiusSigma b) / g), mul_sum]
  refine sum_congr rfl fun g _ => ?_
  unfold coprimePairMoebiusSigmaSum
  simp only [div_eq_mul_inv, mul_sum, sum_mul]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/-! ### The large-band law -/

/-- The asymptotic slope `κ = ρ Σ_{j ≥ 1} S(j) log(1 + 1/j)`. -/
def cofinalMobiusSlope : ℝ :=
  RHTower.Sieve.squarefreeDensity *
    ∑' j : ℕ, coprimePairMoebiusSigmaSum j * Real.log (1 + 1 / (j : ℝ))

/-- **The band slopes converge**: `P(t+1) − P(t) → κ`. -/
theorem tendsto_cofinalBandSlope :
    Tendsto cofinalBandSlope atTop (𝓝 cofinalMobiusSlope) := by
  obtain ⟨C, hC⟩ := exists_abs_coprimePairMoebiusSigmaSum_le
  have h := (tendsto_sum_div_of_log_decay hC).const_mul RHTower.Sieve.squarefreeDensity
  refine h.congr' (Eventually.of_forall fun t => ?_)
  rw [cofinalBandSlope_eq]

theorem tendsto_cofinalMobiusQuadraticProfile_succ_sub :
    Tendsto (fun B : ℕ => cofinalMobiusQuadraticProfile (B + 1) - cofinalMobiusQuadraticProfile B)
      atTop (𝓝 cofinalMobiusSlope) := by
  refine (tendsto_cofinalBandSlope.comp (tendsto_add_atTop_nat 1)).congr' ?_
  exact Eventually.of_forall fun B => by
    simp only [Function.comp, cofinalMobiusQuadraticProfile_succ]; ring

/-- **The cofinal profile is asymptotically linear**: `P(B)/B → κ`. -/
theorem tendsto_cofinalMobiusQuadraticProfile_div :
    Tendsto (fun B : ℕ => cofinalMobiusQuadraticProfile B / B) atTop (𝓝 cofinalMobiusSlope) := by
  have h := (tendsto_cofinalBandSlope.comp (tendsto_add_atTop_nat 1)).cesaro
  refine h.congr' (Eventually.of_forall fun B => ?_)
  simp only [Function.comp, cofinalMobiusQuadraticProfile_eq_sum]
  rw [div_eq_inv_mul]

/-- **The Buchstab sum rule**: `Σ_{b ≤ B} A(b)/(b(b+1)) → −κ`. -/
theorem tendsto_sum_bandAverageStep :
    Tendsto (fun B : ℕ => ∑ b ∈ Icc 1 B, bandAverageStep b / ((b : ℝ) * (b + 1))) atTop
      (𝓝 (-cofinalMobiusSlope)) := by
  have hratio : Tendsto (fun B : ℕ => (B : ℝ) / (B + 1)) atTop (𝓝 1) := by
    have := tendsto_natCast_div_add_atTop (1 : ℝ)
    simpa using this
  have h := (tendsto_cofinalMobiusQuadraticProfile_div.mul hratio).neg
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  rw [cofinalMobiusQuadraticProfile_eq_band_integral hB]
  field_simp

end

end GaloisForLFunctions.BezoutValuationIncidence
