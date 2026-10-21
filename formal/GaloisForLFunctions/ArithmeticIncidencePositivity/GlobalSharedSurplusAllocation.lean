import GaloisForLFunctions.ArithmeticIncidencePositivity.EdgeTentLogarithmicCapacity

/-!
# The global shared-surplus allocation

For an odd test `F` supported in `[−r, r]` the prime side of the zero form is the series
`Σ_n 2Λ(n)/√n ∫ F(x) F(x + log n) dx`. Its atoms vanish for `log n > 2r` (the two supports are
disjoint), so it is the finite sum over `n ≤ e^{2r}` (`tsum_primeShift_eq_sum_primeSide`). Every atom
draws on two resources: the archimedean surplus `T` of the pairs of the support, which all strips
`S_n = [log n − r, r]` share because they are nested, and the mass `∫_{S_n} F²` of its own strip.

**The allocation** (`tsum_primeShift_le_globalAllocation`). For every window `r ≥ 2` and cone width
`0 < δ ≤ e^{−r}/(16r)`:

    Σ_n 2Λ(n)/√n ∫ F F(· + log n) ≤ T(r − 2δ, r) + Σ_{n ≤ e^{2r}, n ∉ cone} 2Λ(n)/√n · m_n(F),

`m_n(F) = ∫_{log n − r}^{r} F²` for `log n ≥ r` and `∫ F²` otherwise (`atomStripMass`). The atoms of the
light cone `2r − 2δ ≤ log n < 2r` are paid together by one copy of the surplus of `[r − 2δ, r]`
(`sum_primeShift_le_lightCone`); every other atom is charged once, to its own strip
(`two_mul_primeShift_le_atomStripMass`). No pair of the surplus is counted twice and no atom is left
out.

**Why the surplus goes to the light cone only.** The odd edge tent lies in every strip at once; one
copy of the surplus of the support pays the odd parts of strips wider than `ε` only up to total weight
`2 log(4/ε) + 84` (`stripBoxEnergy_edgeTent_lt_sum_oddPart`), and for large `r` the odd parts of the
thin band exceed it (`exists_edgeTent_oddPart_sharing_fails`). Beyond the cone the surplus cannot
take the odd parts of all atoms; the strip masses carry them, and paying those masses is the
prime–polar problem of the form.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The prime side at radius `r`: the integers `n ≤ e^{2r}`; every other atom vanishes. -/
def primeSide (r : ℝ) : Finset ℕ := Finset.range (⌊Real.exp (2 * r)⌋₊ + 1)

/-- The strip mass an atom charges when the surplus does not pay it: `∫_{log n − r}^{r} F²` when
`log n ≥ r`, `∫ F²` otherwise. -/
def atomStripMass (F : ℝ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  if r ≤ Real.log n then ∫ x in (Real.log n - r)..r, F x ^ 2 else ∫ x, F x ^ 2

section Global

variable {F : ℝ → ℝ} {K r : ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
  (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hsupp : ∀ x, r < |x| → F x = 0)

include hsupp in
/-- Past `2r` the two supports are disjoint: `∫ F(x) F(x + L) dx = 0` for `L > 2r`. -/
theorem integral_mul_shift_eq_zero_of_lt {L : ℝ} (hL : 2 * r < L) : (∫ x, F x * F (x + L)) = 0 := by
  have h : ∀ x, F x * F (x + L) = 0 := fun x => by
    by_cases h1 : r < |x|
    · rw [hsupp x h1, zero_mul]
    by_cases h2 : r < |x + L|
    · rw [hsupp _ h2, mul_zero]
    rw [not_lt, abs_le] at h1 h2
    linarith [h1.1, h2.2]
  simp_rw [h, integral_zero]

include hF hFc in
/-- A shift correlation is at most the mass: `∫ F(x) F(x + L) dx ≤ ∫ F²`. -/
theorem integral_mul_shift_le_integral_sq (L : ℝ) : (∫ x, F x * F (x + L)) ≤ ∫ x, F x ^ 2 := by
  have hFL' : Continuous fun x => F (x + L) := hF.comp (continuous_add_const L)
  have hcL : HasCompactSupport fun x => F (x + L) := hFc.comp_homeomorph (Homeomorph.addRight L)
  have hI1 : Integrable fun x => F x * F (x + L) :=
    (hF.mul hFL').integrable_of_hasCompactSupport hFc.mul_right
  have hI2 : Integrable fun x => F x ^ 2 := by
    rw [show (fun x => F x ^ 2) = fun x => F x * F x from funext fun x => sq (F x)]
    exact (hF.mul hF).integrable_of_hasCompactSupport hFc.mul_right
  have hI3 : Integrable fun x => F (x + L) ^ 2 := by
    rw [show (fun x => F (x + L) ^ 2) = fun x => F (x + L) * F (x + L) from
      funext fun x => sq (F (x + L))]
    exact (hFL'.mul hFL').integrable_of_hasCompactSupport hcL.mul_right
  have hmono : (∫ x, F x * F (x + L)) ≤ ∫ x, (F x ^ 2 + F (x + L) ^ 2) / 2 :=
    integral_mono hI1 ((hI2.add hI3).div_const 2) fun x => by
      nlinarith [sq_nonneg (F x - F (x + L))]
  rw [integral_div, integral_add hI2 hI3,
    integral_add_right_eq_self (μ := volume) (fun x => F x ^ 2) L] at hmono
  linarith

include hF hFc hodd hsupp in
/-- **An atom charged to its own strip.** For `n ≤ e^{2r}`:
`2Λ(n)/√n ∫ F F(· + log n) ≤ 2Λ(n)/√n · m_n(F)`. On a crossing strip (`log n ≥ r`) the correlation
is at most `∫_{S_n} F²` (the parity identity at `t = −1`); otherwise at most `∫ F²`. -/
theorem two_mul_primeShift_le_atomStripMass {n : ℕ} (hn : Real.log n ≤ 2 * r) :
    2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) ≤
      2 * vonMangoldtAtom n * atomStripMass F r n := by
  have hw := vonMangoldtAtom_nonneg n
  have hcorr : (∫ x, F x * F (x + Real.log n)) ≤ atomStripMass F r n := by
    unfold atomStripMass
    split_ifs with hrL
    · have h := integral_mul_shift_le_interp hF hFc hodd (r := r) (L := Real.log n)
        (by linarith [Real.log_natCast_nonneg n]) (by linarith) hsupp (t := -1) (by norm_num)
      linarith
    · exact integral_mul_shift_le_integral_sq hF hFc _
  have := mul_le_mul_of_nonneg_left hcorr hw
  linarith

include hsupp in
/-- The prime side is finite: `Σ_n 2Λ(n)/√n ∫ F F(· + log n) = Σ_{n ≤ e^{2r}}`. -/
theorem tsum_primeShift_eq_sum_primeSide :
    (∑' n : ℕ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) =
      ∑ n ∈ primeSide r, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n)) := by
  refine tsum_eq_sum fun n hn => ?_
  simp only [primeSide, Finset.mem_range, not_lt] at hn
  have hlt : Real.exp (2 * r) < n := by
    have := Nat.lt_floor_add_one (Real.exp (2 * r))
    exact this.trans_le (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hlt
  have hlog : 2 * r < Real.log n := by
    have := Real.log_lt_log (Real.exp_pos _) hlt
    rwa [Real.log_exp] at this
  rw [integral_mul_shift_eq_zero_of_lt hsupp hlog, mul_zero, mul_zero]

include hF hFc hodd hFL hsupp in
/-- **The global shared-surplus allocation.** For every window `r ≥ 2`, every cone width
`0 < δ ≤ e^{−r}/(16r)` and every odd `F` supported in `[−r, r]`, the complete prime side is paid by
one copy of the surplus of `[r − 2δ, r]` and the strip masses of the atoms outside the light cone:
`Σ_n 2Λ(n)/√n ∫ F F(· + log n) ≤ T(r − 2δ, r) + Σ_{n ≤ e^{2r}, n ∉ cone} 2Λ(n)/√n m_n(F)`. -/
theorem tsum_primeShift_le_globalAllocation {δ : ℝ} (hr : 2 ≤ r) (hδ0 : 0 < δ)
    (hδ : δ ≤ Real.exp (-r) / (16 * r)) :
    (∑' n : ℕ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) ≤
      stripBoxEnergy F (r - 2 * δ) r +
        ∑ n ∈ primeSide r \ lightConeBand r δ, 2 * vonMangoldtAtom n * atomStripMass F r n := by
  -- the light cone lies inside the prime side
  have hsub : lightConeBand r δ ⊆ primeSide r := fun n hn => by
    simp only [lightConeBand, Finset.mem_filter, Finset.mem_range] at hn
    simp only [primeSide, Finset.mem_range]
    have hn0 : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · have : Real.log (n : ℝ) = 0 := by rw [h, Nat.cast_zero, Real.log_zero]
        have hδ' : δ ≤ 1 := by
          have := Real.exp_le_one_iff.mpr (show -r ≤ 0 by linarith)
          calc δ ≤ Real.exp (-r) / (16 * r) := hδ
            _ ≤ 1 / (16 * 2) := div_le_div₀ (by norm_num) this (by norm_num) (by linarith)
            _ ≤ 1 := by norm_num
        linarith [hn.2.1]
      · exact_mod_cast h
    have hlt : (n : ℝ) < Real.exp (2 * r) := by
      rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr hn.2.2
    have : n ≤ ⌊Real.exp (2 * r)⌋₊ := Nat.le_floor hlt.le
    omega
  rw [tsum_primeShift_eq_sum_primeSide hsupp, ← Finset.sum_sdiff hsub]
  -- the light cone from the shared surplus, the rest from the strip masses
  have hcone := sum_primeShift_le_lightCone hF hFc hodd hFL hsupp hr hδ0 hδ
  have hrest : (∑ n ∈ primeSide r \ lightConeBand r δ,
      2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) ≤
      ∑ n ∈ primeSide r \ lightConeBand r δ, 2 * vonMangoldtAtom n * atomStripMass F r n := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' := (Finset.mem_sdiff.mp hn).1
    simp only [primeSide, Finset.mem_range] at hn'
    refine two_mul_primeShift_le_atomStripMass hF hFc hodd hsupp ?_
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]; linarith
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast h
      have hle : (n : ℝ) ≤ Real.exp (2 * r) :=
        (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hn')).trans (Nat.floor_le (Real.exp_pos _).le)
      have := Real.log_le_log hn0 hle
      rwa [Real.log_exp] at this
  linarith

end Global

/-- **The global shared-surplus allocation for `C¹` tests.** For every odd `C¹` test supported in
`[−r, r]`, `r ≥ 2`, `0 < δ ≤ e^{−r}/(16r)`, the complete prime side is at most
`T(r − 2δ, r) + Σ_{n ≤ e^{2r}, n ∉ cone} 2Λ(n)/√n m_n(F)`; the Lipschitz bound comes from the compact
support. -/
theorem tsum_primeShift_le_globalAllocation_of_contDiff {F : ℝ → ℝ} {r δ : ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, r < |x| → F x = 0) (hr : 2 ≤ r) (hδ0 : 0 < δ)
    (hδ : δ ≤ Real.exp (-r) / (16 * r)) :
    (∑' n : ℕ, 2 * (vonMangoldtAtom n * ∫ x, F x * F (x + Real.log n))) ≤
      stripBoxEnergy F (r - 2 * δ) r +
        ∑ n ∈ primeSide r \ lightConeBand r δ, 2 * vonMangoldtAtom n * atomStripMass F r n := by
  obtain ⟨K, -, hK⟩ := exists_lipschitz_bound_of_compactSupport hF hFc
  exact tsum_primeShift_le_globalAllocation hF.continuous hFc hodd (fun a b => hK b a) hsupp hr hδ0 hδ

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
