import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionPeriodizationDefect

/-!
# Two prime prices are attained only past the product length

For prime powers `m₁ = p^e`, `m₂ = q^f` of different primes the joint deletion price
`w(m₁) + w(m₂)` is attained on windows longer than `log(m₁m₂)` by the double pair
(`PrimeTwoThreeDecouplingLength`). Here: never on windows of length `L ≤ log(m₁m₂)`.

**Theorem** (`eulerPrice_mem_eulerWindowDeviations_iff`). For two primes `p ≠ q` and exponents
`e ≥ 1`, the Euler price `w(p^{e(p)}) + w(q^{e(q)})` is a window deviation of length `L` iff
`L > log(p^{e(p)} q^{e(q)})`; the same for `−(w + w)` (`neg_eulerPrice_mem_eulerWindowDeviations_iff`).

**Mechanism.** At the price both nodes are extreme, so every test is a pair `g + g(· − log m₁)`
(`PrimePowerDeletionPeriodizationDefect`) whose alternating `log m₂`-periodization vanishes. The
`log m₂`-periodization `φ` of `g` then satisfies `φ(u) = σ φ(u − log m₁)` and is antiperiodic along
`log m₂`; `|φ|` is invariant under the group `log m₁ ℤ + log m₂ ℤ`, which is dense because
`log m₁/log m₂` is irrational (`dense_addSubgroupClosure_pair_iff`). When `g` is shorter than
`log m₂`, `φ` vanishes at the left end of the support, hence everywhere, and `g = 0`
(`eq_zero_of_periodization_relation`): an extremal needs room for both shifts.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Full periodizations -/

/-- The full `σ`-periodization `Σ_{j∈ℤ} σ^j g(u + jℓ)`. -/
def altPer (ℓ σ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ := ∑' j : ℤ, ((σ ^ j : ℝ) : ℂ) * g (u + j * ℓ)

/-- The indices that can reach the support `(a, b)` from `u`. -/
def perIndex (a b ℓ u : ℝ) : Finset ℤ := Finset.Icc ⌈(a - u) / ℓ⌉ ⌊(b - u) / ℓ⌋

theorem mem_perIndex {a b ℓ u : ℝ} (hℓ : 0 < ℓ) {j : ℤ} (h : u + j * ℓ ∈ Ioo a b) :
    j ∈ perIndex a b ℓ u := by
  rw [perIndex, Finset.mem_Icc]
  constructor
  · rw [Int.ceil_le, div_le_iff₀ hℓ]; linarith [h.1]
  · rw [Int.le_floor, le_div_iff₀ hℓ]; linarith [h.2]

section Periodization

variable {g : ℝ → ℂ} {a b ℓ σ : ℝ} (hℓ : 0 < ℓ) (hsupp : ∀ u, g u ≠ 0 → u ∈ Ioo a b)

include hsupp in
theorem altPer_eq_sum_of_subset (u : ℝ) {J : Finset ℤ}
    (hJ : ∀ j : ℤ, u + j * ℓ ∈ Ioo a b → j ∈ J) :
    altPer ℓ σ g u = ∑ j ∈ J, ((σ ^ j : ℝ) : ℂ) * g (u + j * ℓ) := by
  refine tsum_eq_sum fun j hj => ?_
  by_cases h : g (u + j * ℓ) = 0
  · rw [h, mul_zero]
  · exact absurd (hJ j (hsupp _ h)) hj

include hℓ hsupp in
theorem summable_altPer (u : ℝ) : Summable fun j : ℤ => ((σ ^ j : ℝ) : ℂ) * g (u + j * ℓ) :=
  summable_of_ne_finset_zero (s := perIndex a b ℓ u) fun j hj => by
    by_cases h : g (u + j * ℓ) = 0
    · rw [h, mul_zero]
    · exact absurd (mem_perIndex hℓ (hsupp _ h)) hj

/-- Shifting by `nℓ` multiplies the periodization by `σ^{−n}`. -/
theorem altPer_add_int_mul (hσ : σ ≠ 0) (u : ℝ) (n : ℤ) :
    altPer ℓ σ g (u + n * ℓ) = ((σ ^ (-n) : ℝ) : ℂ) * altPer ℓ σ g u := by
  unfold altPer
  set F : ℤ → ℂ := fun k => ((σ ^ (k - n) : ℝ) : ℂ) * g (u + k * ℓ) with hF
  have e1 : (∑' j : ℤ, ((σ ^ j : ℝ) : ℂ) * g (u + n * ℓ + j * ℓ)) =
      ∑' j : ℤ, F (Equiv.addRight n j) := by
    refine tsum_congr fun j => ?_
    simp only [hF, Equiv.coe_addRight, add_sub_cancel_right]
    push_cast; ring_nf
  rw [e1, (Equiv.addRight n).tsum_eq F, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [hF]
  rw [zpow_sub₀ hσ, zpow_neg]
  push_cast
  ring

include hℓ hsupp in
/-- The periodization is continuous. -/
theorem continuous_altPer (hg : Continuous g) : Continuous (altPer ℓ σ g) := by
  rw [continuous_iff_continuousAt]
  intro x
  set J := Finset.Icc ⌈(a - (x + 1)) / ℓ⌉ ⌊(b - (x - 1)) / ℓ⌋
  have hfin : Continuous fun u => ∑ j ∈ J, ((σ ^ j : ℝ) : ℂ) * g (u + j * ℓ) :=
    continuous_finsetSum _ fun _ _ => continuous_const.mul (hg.comp (continuous_id.add continuous_const))
  refine (hfin.continuousAt).congr ?_
  filter_upwards [Ioo_mem_nhds (show x - 1 < x by linarith) (show x < x + 1 by linarith)] with u hu
  refine (altPer_eq_sum_of_subset hsupp u fun j hj => ?_).symm
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.ceil_le, div_le_iff₀ hℓ]; linarith [hj.1, hu.2]
  · rw [Int.le_floor, le_div_iff₀ hℓ]; linarith [hj.2, hu.1]

end Periodization

theorem altPer_shift (ℓ σ : ℝ) (g : ℝ → ℂ) (s u : ℝ) :
    altPer ℓ σ (fun x => g (x - s)) u = altPer ℓ σ g (u - s) := by
  unfold altPer
  congr 1; funext j
  show _ * g (u + j * ℓ - s) = _
  rw [show u + (j : ℝ) * ℓ - s = u - s + j * ℓ by ring]

theorem altPer_sub {g h : ℝ → ℂ} {a b c d ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hg : ∀ u, g u ≠ 0 → u ∈ Ioo a b) (hh : ∀ u, h u ≠ 0 → u ∈ Ioo c d) (κ : ℂ) (u : ℝ) :
    altPer ℓ σ (fun x => g x - κ * h x) u = altPer ℓ σ g u - κ * altPer ℓ σ h u := by
  unfold altPer
  rw [← tsum_mul_left, ← Summable.tsum_sub (summable_altPer hℓ hg u)
    ((summable_altPer hℓ hh u).mul_left κ)]
  congr 1; funext j; ring

/-- A test shorter than the period: the periodization vanishes at the left end of the support. -/
theorem altPer_left_end {g : ℝ → ℂ} {a L ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hsupp : ∀ u, g u ≠ 0 → u ∈ Ioo a (a + L)) (hL : L ≤ ℓ) : altPer ℓ σ g a = 0 := by
  rw [altPer_eq_sum_of_subset hsupp a (J := ∅) fun j hj => ?_]
  · simp
  · exfalso
    obtain ⟨h1, h2⟩ := hj
    rcases lt_trichotomy j 0 with hj0 | rfl | hj0
    · have : (j : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hj0
      nlinarith
    · simp at h1
    · have : (1 : ℝ) ≤ j := by exact_mod_cast hj0
      nlinarith

/-- Inside a support shorter than the period, the periodization is the function. -/
theorem altPer_eq_self {g : ℝ → ℂ} {a L ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hsupp : ∀ u, g u ≠ 0 → u ∈ Ioo a (a + L)) (hL : L ≤ ℓ) {u : ℝ} (hu : u ∈ Ioo a (a + L)) :
    altPer ℓ σ g u = g u := by
  rw [altPer_eq_sum_of_subset hsupp u (J := {0}) fun j hj => ?_]
  · simp
  · obtain ⟨h1, h2⟩ := hj
    rcases lt_trichotomy j 0 with hj0 | rfl | hj0
    · have : (j : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hj0
      exfalso; nlinarith [hu.2]
    · simp
    · have : (1 : ℝ) ≤ j := by exact_mod_cast hj0
      exfalso; nlinarith [hu.1]

/-! ### 2. Invariance under a dense group -/

/-- **A continuous function whose modulus is invariant under two incommensurable shifts and which
vanishes somewhere vanishes everywhere.** -/
theorem eq_zero_of_norm_invariant {φ : ℝ → ℂ} (hφ : Continuous φ) {ℓ₁ ℓ₂ : ℝ}
    (hirr : Irrational (ℓ₁ / ℓ₂)) (h₁ : ∀ x, ‖φ (x + ℓ₁)‖ = ‖φ x‖) (h₂ : ∀ x, ‖φ (x + ℓ₂)‖ = ‖φ x‖)
    {x₀ : ℝ} (h₀ : φ x₀ = 0) (x : ℝ) : φ x = 0 := by
  set H := AddSubgroup.closure ({ℓ₁, ℓ₂} : Set ℝ)
  have hinv : ∀ h ∈ H, ∀ y, ‖φ (y + h)‖ = ‖φ y‖ := by
    intro h hh
    induction hh using AddSubgroup.closure_induction with
    | mem z hz =>
      intro y
      rcases hz with rfl | hz
      · exact h₁ y
      · rw [Set.mem_singleton_iff] at hz; subst hz; exact h₂ y
    | zero => intro y; rw [add_zero]
    | add z w _ _ hz hw => intro y; rw [← add_assoc, hw, hz]
    | neg z _ hz => intro y; rw [← hz (y + -z), neg_add_cancel_right]
  have hdense : Dense (H : Set ℝ) := dense_addSubgroupClosure_pair_iff.mpr hirr
  have hext : (fun h : ℝ => ‖φ (x₀ + h)‖) = fun _ => (0 : ℝ) :=
    Continuous.ext_on hdense ((hφ.comp (continuous_const.add continuous_id)).norm) continuous_const
      fun h hh => by rw [hinv h hh, h₀, norm_zero]
  have := congrFun hext (x - x₀)
  simp only [add_sub_cancel, norm_eq_zero] at this
  exact this

/-- **Two periodizations force the zero function.** If `g` is continuous and supported in
`(a, a + L')` with `L' ≤ ℓ₂`, `ℓ₁/ℓ₂` is irrational and the `σ₂`-periodization along `ℓ₂` of
`g − σ₁ g(· − ℓ₁)` vanishes identically, then `g = 0`. -/
theorem eq_zero_of_periodization_relation {g : ℝ → ℂ} (hg : Continuous g) {a L' ℓ₁ ℓ₂ : ℝ}
    (hℓ₂ : 0 < ℓ₂) (hsupp : ∀ u, g u ≠ 0 → u ∈ Ioo a (a + L')) (hL' : L' ≤ ℓ₂)
    (hirr : Irrational (ℓ₁ / ℓ₂)) {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ ^ 2 = 1) (hσ₂ : σ₂ ^ 2 = 1)
    (hrel : ∀ u, altPer ℓ₂ σ₂ (fun x => g x - (σ₁ : ℂ) * g (x - ℓ₁)) u = 0) (u : ℝ) : g u = 0 := by
  set φ := altPer ℓ₂ σ₂ g
  have hσ₂0 : σ₂ ≠ 0 := by rintro rfl; norm_num at hσ₂
  have hn₁ : ‖(σ₁ : ℂ)‖ = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := sq_abs σ₁; nlinarith [abs_nonneg σ₁]
  have hsupp' : ∀ u, g (u - ℓ₁) ≠ 0 → u ∈ Ioo (a + ℓ₁) (a + L' + ℓ₁) := fun u hu => by
    have := hsupp _ hu; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hrel' : ∀ x, φ x = (σ₁ : ℂ) * φ (x - ℓ₁) := by
    intro x
    have := hrel x
    rw [altPer_sub hℓ₂ hsupp hsupp' (σ₁ : ℂ) x, altPer_shift] at this
    exact sub_eq_zero.mp this
  have hφc : Continuous φ := continuous_altPer hℓ₂ hsupp hg
  have h₁ : ∀ x, ‖φ (x + ℓ₁)‖ = ‖φ x‖ := fun x => by
    rw [hrel' (x + ℓ₁), add_sub_cancel_right, norm_mul, hn₁, one_mul]
  have h₂ : ∀ x, ‖φ (x + ℓ₂)‖ = ‖φ x‖ := fun x => by
    show ‖altPer ℓ₂ σ₂ g (x + ℓ₂)‖ = ‖altPer ℓ₂ σ₂ g x‖
    have := altPer_add_int_mul (g := g) (ℓ := ℓ₂) (σ := σ₂) hσ₂0 x 1
    simp only [Int.cast_one, one_mul] at this
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_zpow,
      show |σ₂| = 1 by nlinarith [sq_abs σ₂, abs_nonneg σ₂], one_zpow, one_mul]
  have hzero := eq_zero_of_norm_invariant hφc hirr h₁ h₂ (altPer_left_end hℓ₂ hsupp hL')
  by_cases hu : u ∈ Ioo a (a + L')
  · rw [← altPer_eq_self hℓ₂ hsupp hL' hu]; exact hzero u
  · by_contra h; exact hu (hsupp u h)

/-! ### 3. From one period to the whole line -/

/-- On one period the one-sided periodization is the full periodization. -/
theorem stepSum_eq_altPer {f : ℝ → ℂ} {a L ℓ σ : ℝ} {K : ℕ} (hℓ : 0 < ℓ)
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Ioo a (a + L)) (hL : L < (K + 1) * ℓ) {u : ℝ}
    (hu : u ∈ Icc a (a + ℓ)) : stepSum ℓ σ K f u = altPer ℓ σ f u := by
  classical
  rw [altPer_eq_sum_of_subset hsupp u (J := (Finset.range (K + 1)).map ⟨Nat.cast, Nat.cast_injective⟩)
    fun j hj => ?_]
  · rw [stepSum, Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.Embedding.coeFn_mk, zpow_natCast, Int.cast_natCast]
  · obtain ⟨h1, h2⟩ := hj
    obtain ⟨hu1, hu2⟩ := hu
    have hj0 : 0 ≤ j := by
      by_contra h; push Not at h
      have : (j : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
      nlinarith
    have hjK : j < K + 1 := by
      by_contra h; push Not at h
      have : ((K : ℝ) + 1) ≤ j := by exact_mod_cast h
      nlinarith
    rw [Finset.mem_map]
    exact ⟨j.toNat, Finset.mem_range.mpr (by omega), by simp [Int.toNat_of_nonneg hj0]⟩

/-- A periodization vanishing on one period vanishes everywhere. -/
theorem altPer_eq_zero_of_period {f : ℝ → ℂ} {a ℓ σ : ℝ} (hℓ : 0 < ℓ) (hσ : σ ≠ 0)
    (h : ∀ u ∈ Icc a (a + ℓ), altPer ℓ σ f u = 0) (x : ℝ) : altPer ℓ σ f x = 0 := by
  set n := ⌊(x - a) / ℓ⌋ with hn
  have h1 : (n : ℝ) ≤ (x - a) / ℓ := Int.floor_le _
  have h2 : (x - a) / ℓ < n + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hℓ] at h1
  rw [div_lt_iff₀ hℓ] at h2
  have hx : x = (x - n * ℓ) + n * ℓ := by ring
  rw [hx, altPer_add_int_mul hσ, h (x - n * ℓ) ⟨by linarith, by linarith⟩, mul_zero]

/-! ### 4. Two extreme nodes force the zero combination -/

/-- `log m₁ / log m₂` is irrational for powers of two different primes. -/
theorem irrational_log_div_log {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Irrational (Real.log ((p ^ a : ℕ) : ℝ) / Real.log ((q ^ b : ℕ) : ℝ)) := by
  rw [irrational_iff_ne_rational]
  intro r s hs h
  have hl₁ : 0 < Real.log ((p ^ a : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast Nat.one_lt_pow (by omega) hp.one_lt)
  have hl₂ : 0 < Real.log ((q ^ b : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast Nat.one_lt_pow (by omega) hq.one_lt)
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
  have heq : (s : ℝ) * Real.log ((p ^ a : ℕ) : ℝ) = r * Real.log ((q ^ b : ℕ) : ℝ) := by
    rw [div_eq_div_iff hl₂.ne' hs'] at h; linarith
  -- pass to absolute values: `|s| log m₁ = |r| log m₂`
  have habs : ((s.natAbs : ℕ) : ℝ) * Real.log ((p ^ a : ℕ) : ℝ) =
      ((r.natAbs : ℕ) : ℝ) * Real.log ((q ^ b : ℕ) : ℝ) := by
    have h' := congrArg abs heq
    rw [abs_mul, abs_mul, abs_of_pos hl₁, abs_of_pos hl₂] at h'
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact h'
  rw [← Real.log_pow, ← Real.log_pow] at habs
  have hp0 : (0 : ℝ) < ((p ^ a : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos a
  have hq0 : (0 : ℝ) < ((q ^ b : ℕ) : ℝ) := by exact_mod_cast pow_pos hq.pos b
  have hpow := Real.log_injOn_pos (Set.mem_Ioi.mpr (pow_pos hp0 _))
    (Set.mem_Ioi.mpr (pow_pos hq0 _)) habs
  have hnat : (p ^ a) ^ s.natAbs = (q ^ b) ^ r.natAbs := by exact_mod_cast hpow
  rw [← pow_mul, ← pow_mul] at hnat
  have hsn : 1 ≤ s.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hs)
  exact hpq (eq_of_prime_pow_eq hp hq (Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))) hnat).1

/-- **Both nodes extreme on short windows forces the zero combination.** -/
theorem massOf_eq_zero_of_two_extremal {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {m₁ m₂ : ℕ}
    (hm₁ : 2 ≤ m₁) (hm₂ : 2 ≤ m₂)
    (hb₁ : ∀ j : LogIndex, (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m₁ ^ k) → nodeVector c j = 0)
    (hb₂ : ∀ j : LogIndex, (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m₂ ^ k) → nodeVector c j = 0)
    {L : ℝ} (hs : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L))
    (hL : L ≤ Real.log m₁ + Real.log m₂) (hirr : Irrational (Real.log m₁ / Real.log m₂))
    {σ : ℝ} (hσ : σ ^ 2 = 1) (h₁ : massOf c + σ * (Real.sqrt m₁ * nodeVector c ⟨m₁, hm₁⟩) = 0)
    (h₂ : massOf c + σ * (Real.sqrt m₂ * nodeVector c ⟨m₂, hm₂⟩) = 0) : massOf c = 0 := by
  classical
  choose! a ha using hs
  have hℓ₁ : 0 < Real.log m₁ := Real.log_pos (by exact_mod_cast (by omega : 1 < m₁))
  have hℓ₂ : 0 < Real.log m₂ := Real.log_pos (by exact_mod_cast (by omega : 1 < m₂))
  have hσ0 : σ ≠ 0 := by rintro rfl; norm_num at hσ
  obtain ⟨K₁, hK₁, hL₁⟩ := exists_period_count (L := L) hℓ₁
  obtain ⟨K₂, hK₂, hL₂⟩ := exists_period_count (L := L) hℓ₂
  have hz₁ := stepSum_eq_zero_of_extremal hc hm₁ hb₁ ha hK₁ hL₁ hσ h₁
  have hz₂ := stepSum_eq_zero_of_extremal hc hm₂ hb₂ ha hK₂ hL₂ hσ h₂
  -- every test vanishes
  have hzero : ∀ f ∈ c.support, ∀ u, f.1 u = 0 := by
    intro f hf
    obtain ⟨g, hg, hgs, hgf⟩ := pair_structure_of_stepSum_eq_zero f.2.1.continuous hσ hℓ₁ (ha f hf)
      hL₁ (hz₁ f hf)
    have hper : ∀ x, altPer (Real.log m₂) σ f.1 x = 0 :=
      altPer_eq_zero_of_period hℓ₂ hσ0 fun u hu => by
        rw [← stepSum_eq_altPer hℓ₂ (ha f hf) hL₂ hu]; exact hz₂ f hf u hu
    have hrel : ∀ x, altPer (Real.log m₂) σ (fun y => g y - (σ : ℂ) * g (y - Real.log m₁)) x = 0 :=
      fun x => by rw [show (fun y => g y - (σ : ℂ) * g (y - Real.log m₁)) = f.1 from
        funext fun y => (hgf y).symm]; exact hper x
    have hgs' : ∀ u, g u ≠ 0 → u ∈ Ioo (a f) (a f + (L - Real.log m₁)) := fun u hu => by
      have := hgs u hu; rwa [← add_sub_assoc]
    have hgz := eq_zero_of_periodization_relation (L' := L - Real.log m₁) (ℓ₁ := Real.log m₁) hg
      hℓ₂ hgs' (by linarith) hirr hσ hσ hrel
    intro u
    rw [hgf u, hgz u, hgz (u - Real.log m₁), mul_zero, sub_zero]
  rw [show massOf c = c.sum fun f t => t * ∫ x, ‖f.1 x‖ ^ 2 from rfl, Finsupp.sum]
  refine Finset.sum_eq_zero fun f hf => ?_
  simp [hzero f hf]

/-! ### 5. The attainment threshold for two prime powers -/

/-- At `±` the Euler price of two nodes both nodes are extreme. -/
theorem two_nodes_extreme {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) {e : ℕ → ℕ} (hep : 1 ≤ e p) (heq : 1 ≤ e q)
    (hb : BlindOn (primePowerNodes \ ↑(eulerNodes {p, q} e)) c) {s : ℝ} (hs : s ^ 2 = 1)
    (hext : nodeArchEnergy c - weilEnergy c = s * eulerPrice {p, q} e * massOf c) :
    massOf c + (-s) * (Real.sqrt ((p ^ e p : ℕ) : ℝ) *
        nodeVector c ⟨p ^ e p, (hp.isPrimePow.pow (by omega)).two_le⟩) = 0 ∧
      massOf c + (-s) * (Real.sqrt ((q ^ e q : ℕ) : ℝ) *
        nodeVector c ⟨q ^ e q, (hq.isPrimePow.pow (by omega)).two_le⟩) = 0 := by
  classical
  have hP : ∀ r ∈ ({p, q} : Finset ℕ), r.Prime := fun r hr => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr; rcases hr with rfl | rfl <;> assumption
  have heP : ∀ r ∈ ({p, q} : Finset ℕ), 1 ≤ e r := fun r hr => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr; rcases hr with rfl | rfl <;> assumption
  have h₁ : 2 ≤ p ^ e p := (hp.isPrimePow.pow (by omega)).two_le
  have h₂ : 2 ≤ q ^ e q := (hq.isPrimePow.pow (by omega)).two_le
  have hne : p ^ e p ≠ q ^ e q := fun h => hpq (eq_of_prime_pow_eq hp hq hep h).1
  set N₁ := nodeVector c ⟨p ^ e p, h₁⟩
  set N₂ := nodeVector c ⟨q ^ e q, h₂⟩
  set M := massOf c
  have hid : nodeArchEnergy c - weilEnergy c =
      ArithmeticFunction.vonMangoldt (p ^ e p) * N₁ + ArithmeticFunction.vonMangoldt (q ^ e q) * N₂ := by
    rw [nodeArchEnergy_eq_weilEnergy_add_finset _ hb, add_sub_cancel_left, eulerNodes,
      Finset.sum_image (injOn_eulerNodes hP heP), Finset.sum_pair hpq, nodeAt, nodeAt, dif_pos h₁,
      dif_pos h₂]
  have hbound : ∀ r ∈ ({p, q} : Finset ℕ), ∀ (h2 : 2 ≤ r ^ e r),
      |nodeVector c ⟨r ^ e r, h2⟩| ≤ M / Real.sqrt ((r ^ e r : ℕ) : ℝ) := fun r hr h2 =>
    abs_nodeVector_le_massOf_div_sqrt hc h2 fun j ⟨k, hk, hj⟩ =>
      hb j (hj ▸ pow_mem_primePowerNodes_diff_eulerNodes hP heP hr hk)
  have hb₁ := hbound p (by simp) h₁
  have hb₂ := hbound q (by simp) h₂
  have hΛ₁ : 0 < (ArithmeticFunction.vonMangoldt (p ^ e p) : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact Real.log_pos (by exact_mod_cast hp.one_lt)
  have hΛ₂ : 0 < (ArithmeticFunction.vonMangoldt (q ^ e q) : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hq]
    exact Real.log_pos (by exact_mod_cast hq.one_lt)
  have hs₁ : 0 < Real.sqrt ((p ^ e p : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs₂ : 0 < Real.sqrt ((q ^ e q : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hprice : eulerPrice {p, q} e = ArithmeticFunction.vonMangoldt (p ^ e p) /
      Real.sqrt ((p ^ e p : ℕ) : ℝ) + ArithmeticFunction.vonMangoldt (q ^ e q) /
      Real.sqrt ((q ^ e q : ℕ) : ℝ) := by
    rw [eulerPrice, Finset.sum_pair hpq]
  rw [hid, hprice] at hext
  -- `s N_i √m_i ≤ M` for each node, with equality forced by the sum
  have u₁ : s * (Real.sqrt ((p ^ e p : ℕ) : ℝ) * N₁) ≤ M := by
    have : |s| = 1 := by nlinarith [sq_abs s, abs_nonneg s]
    have h := abs_le.mp hb₁
    rw [le_div_iff₀ hs₁] at h
    rw [div_le_iff₀ hs₁] at h
    rcases abs_eq (zero_le_one) |>.mp this with h1 | h1 <;> subst h1 <;> nlinarith [h.1, h.2]
  have u₂ : s * (Real.sqrt ((q ^ e q : ℕ) : ℝ) * N₂) ≤ M := by
    have : |s| = 1 := by nlinarith [sq_abs s, abs_nonneg s]
    have h := abs_le.mp hb₂
    rw [le_div_iff₀ hs₂] at h
    rw [div_le_iff₀ hs₂] at h
    rcases abs_eq (zero_le_one) |>.mp this with h1 | h1 <;> subst h1 <;> nlinarith [h.1, h.2]
  -- the sum identity in the scaled variables
  have hsum : (ArithmeticFunction.vonMangoldt (p ^ e p) / Real.sqrt ((p ^ e p : ℕ) : ℝ)) *
        (M - s * (Real.sqrt ((p ^ e p : ℕ) : ℝ) * N₁)) +
      (ArithmeticFunction.vonMangoldt (q ^ e q) / Real.sqrt ((q ^ e q : ℕ) : ℝ)) *
        (M - s * (Real.sqrt ((q ^ e q : ℕ) : ℝ) * N₂)) = 0 := by
    have hs2 : s * s = 1 := by nlinarith
    field_simp
    linear_combination (-(Real.sqrt ((p ^ e p : ℕ) : ℝ)) * Real.sqrt ((q ^ e q : ℕ) : ℝ) * s) * hext +
      (ArithmeticFunction.vonMangoldt (p ^ e p) * Real.sqrt ((q ^ e q : ℕ) : ℝ) * M +
        ArithmeticFunction.vonMangoldt (q ^ e q) * Real.sqrt ((p ^ e p : ℕ) : ℝ) * M) * hs2
  have hw₁ : 0 < ArithmeticFunction.vonMangoldt (p ^ e p) / Real.sqrt ((p ^ e p : ℕ) : ℝ) :=
    div_pos hΛ₁ hs₁
  have hw₂ : 0 < ArithmeticFunction.vonMangoldt (q ^ e q) / Real.sqrt ((q ^ e q : ℕ) : ℝ) :=
    div_pos hΛ₂ hs₂
  have t₁ : M - s * (Real.sqrt ((p ^ e p : ℕ) : ℝ) * N₁) = 0 := by
    nlinarith [mul_nonneg hw₁.le (sub_nonneg.mpr u₁), mul_nonneg hw₂.le (sub_nonneg.mpr u₂)]
  have t₂ : M - s * (Real.sqrt ((q ^ e q : ℕ) : ℝ) * N₂) = 0 := by
    nlinarith [mul_nonneg hw₁.le (sub_nonneg.mpr u₁), mul_nonneg hw₂.le (sub_nonneg.mpr u₂)]
  constructor <;> linarith

/-- **The Euler price of two prime powers is a window deviation of length `L` iff
`L > log(p^{e(p)} q^{e(q)})`.** -/
theorem signed_eulerPrice_mem_eulerWindowDeviations_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {e : ℕ → ℕ} (hep : 1 ≤ e p) (heq : 1 ≤ e q) {s : ℝ} (hs : s ^ 2 = 1) (L : ℝ) :
    s * eulerPrice {p, q} e ∈ eulerWindowDeviations {p, q} e L ↔
      Real.log ((p ^ e p * q ^ e q : ℕ) : ℝ) < L := by
  classical
  have hP : ∀ r ∈ ({p, q} : Finset ℕ), r.Prime := fun r hr => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr; rcases hr with rfl | rfl <;> assumption
  have heP : ∀ r ∈ ({p, q} : Finset ℕ), 1 ≤ e r := fun r hr => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr; rcases hr with rfl | rfl <;> assumption
  have hsub : subProd e {p, q} = p ^ e p * q ^ e q := by
    rw [subProd, Finset.prod_pair hpq]
  constructor
  · rintro ⟨c, hc, hb, hw, hpos, hx⟩
    by_contra hL
    push Not at hL
    have hext : nodeArchEnergy c - weilEnergy c = s * eulerPrice {p, q} e * massOf c := by
      rw [hx, div_mul_cancel₀ _ hpos.ne']
    obtain ⟨e₁, e₂⟩ := two_nodes_extreme hc hp hq hpq hep heq hb hs hext
    have h₁ : 2 ≤ p ^ e p := (hp.isPrimePow.pow (by omega)).two_le
    have h₂ : 2 ≤ q ^ e q := (hq.isPrimePow.pow (by omega)).two_le
    have hbpow : ∀ (r : ℕ) (hr : r ∈ ({p, q} : Finset ℕ)), ∀ j : LogIndex,
        (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = (r ^ e r) ^ k) → nodeVector c j = 0 :=
      fun r hr j ⟨k, hk, hj⟩ => hb j (hj ▸ pow_mem_primePowerNodes_diff_eulerNodes hP heP hr hk)
    have hlog : L ≤ Real.log ((p ^ e p : ℕ) : ℝ) + Real.log ((q ^ e q : ℕ) : ℝ) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; push_cast at hL ⊢; exact hL
    have hzero := massOf_eq_zero_of_two_extremal hc h₁ h₂ (hbpow p (by simp)) (hbpow q (by simp)) hw
      hlog (irrational_log_div_log hp hq hpq hep heq) (σ := -s) (by nlinarith) e₁ e₂
    exact absurd hzero hpos.ne'
  · intro hL
    exact deviation_mem_eulerWindowDeviations hP heP (by rw [hsub]; exact hL) hs

/-- **The upper price.** -/
theorem eulerPrice_mem_eulerWindowDeviations_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {e : ℕ → ℕ} (hep : 1 ≤ e p) (heq : 1 ≤ e q) (L : ℝ) :
    eulerPrice {p, q} e ∈ eulerWindowDeviations {p, q} e L ↔
      Real.log ((p ^ e p * q ^ e q : ℕ) : ℝ) < L := by
  simpa using signed_eulerPrice_mem_eulerWindowDeviations_iff hp hq hpq hep heq (s := 1)
    (by norm_num) L

/-- **The lower price.** -/
theorem neg_eulerPrice_mem_eulerWindowDeviations_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {e : ℕ → ℕ} (hep : 1 ≤ e p) (heq : 1 ≤ e q) (L : ℝ) :
    -eulerPrice {p, q} e ∈ eulerWindowDeviations {p, q} e L ↔
      Real.log ((p ^ e p * q ^ e q : ℕ) : ℝ) < L := by
  simpa using signed_eulerPrice_mem_eulerWindowDeviations_iff hp hq hpq hep heq (s := -1)
    (by norm_num) L

end

end GaloisForLFunctions.BiScaleUncertainty
