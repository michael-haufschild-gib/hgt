/-
# The literal single limit `(A−B)/i → Φ(c)` on the pole-excess field model

The interchange `tendsto_shellSum_stripResidue` states `Σ_{n≥1} shellDiffTerm c n i → Φ(c)`, where
`shellDiffTerm c n i` is the `n`-th geometric shell of the discrete field balance. This file recovers
the balance on the **physical pole-excess model** — the field `poleExcess(u) = 1/(e^u − 1)` summed
over the pole distances — via the Tonelli identity `poleExcess(u) = Σ_{n≥1} e^{−nu}` (`poleExcess_hasSum`):

* `poleModelDiff c i = A/i − B/i`, with `A/i = (1/i)Σ'_k poleExcess(ahead_k)` (excess of all poles
  ahead of the gap midpoint) and `B/i = (1/i)Σ_{k<i} poleExcess(behind_k)` (the finitely many behind).
* `poleModelDiff_eq` : `A/i = Σ_n aheadShell`, `B/i = Σ_n behindShell` (Tonelli — `Summable.tsum_comm`
  for the ahead double sum, `Summable.tsum_finsetSum` for the finite behind), so
  `poleModelDiff = Σ_n shellDiffTerm`.
* `tendsto_poleModel` : `poleModelDiff c i → stripResidue c = Φ(c)` as `i → ∞`. This is the literal
  `(A−B)/i → Φ(c)` on the pole-excess field.

The ahead double-sum summability (`aheadTerm_prod_summable`) uses `poleExcess(ahead_k) ≤ C·aheadTerm(k,1)`
(`poleExcess_ahead_le`, from `poleExcess(u) = e^{−u}/(1−e^{−u})` decreasing) reducing to the
`k`-summability `aheadTerm_summable`; the `n`-marginal comes from the product-swap `summable_prod_swap`.
-/
import GaloisForLFunctions.RHTower.LegStripCapstone
open MeasureTheory Real Set Filter Topology
noncomputable section
namespace RHTower

def aheadShell (c : ℝ) (n : ℕ+) (i : ℕ) : ℝ := (1/(i:ℝ)) * ∑' k:ℕ, aheadTerm c n i k
def behindShell (c : ℝ) (n : ℕ+) (i : ℕ) : ℝ :=
  (1/(i:ℝ)) * ∑ k ∈ Finset.range i, behindTerm c n i k

def poleModelDiff (c : ℝ) (i : ℕ) : ℝ :=
  (1/(i:ℝ)) * ∑' k:ℕ, poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))
  - (1/(i:ℝ)) * ∑ k ∈ Finset.range i, poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))

theorem ahead_pos {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 1 ≤ i) (k : ℕ) :
    0 < c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by
  have hi0 : (0:ℝ) < i := by exact_mod_cast hi
  have hc0 : 0 < c := by linarith
  have hs : 0 ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) := by positivity
  have h1 : 0 < c/(2*(i:ℝ)) := by positivity
  nlinarith [mul_nonneg hc0.le hs]

theorem behind_pos {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 1 ≤ i) {k : ℕ} (hk : k < i) :
    0 < c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j) := by
  have hi0 : (0:ℝ) < i := by exact_mod_cast hi
  have hc0 : 0 < c := by linarith
  have hs : 0 ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j) := by
    apply Finset.sum_nonneg; intro j hj; rw [Finset.mem_range] at hj
    have : j + 2 ≤ i := by omega
    have : (j:ℝ)+2 ≤ (i:ℝ) := by exact_mod_cast this
    have : (0:ℝ) < (i:ℝ)-1-j := by linarith
    positivity
  have h1 : 0 < c/(2*(i:ℝ)) := by positivity
  nlinarith [mul_nonneg hc0.le hs]

theorem poleExcess_ahead {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 1 ≤ i) (k : ℕ) :
    poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))
      = ∑' n:ℕ+, aheadTerm c n i k :=
  ((poleExcess_hasSum (ahead_pos hc hi k)).tsum_eq).symm

theorem poleExcess_behind {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 1 ≤ i) {k : ℕ} (hk : k < i) :
    poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j))
      = ∑' n:ℕ+, behindTerm c n i k :=
  ((poleExcess_hasSum (behind_pos hc hi hk)).tsum_eq).symm


theorem poleExcess_pos {u : ℝ} (hu : 0 < u) : 0 < poleExcess u := by
  rw [poleExcess]
  exact div_pos one_pos (by linarith [Real.one_lt_exp_iff.mpr hu])

theorem poleExcess_ahead_le {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 1 ≤ i) (k : ℕ) :
    poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))
      ≤ (1 - Real.exp (-(c/(2*(i:ℝ)))))⁻¹ * aheadTerm c 1 i k := by
  have hi0 : (0:ℝ) < i := by exact_mod_cast hi
  have hc0 : 0 < c := by linarith
  set u := c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) with hu_def
  have hu0 : 0 < c/(2*(i:ℝ)) := by positivity
  have hule : c/(2*(i:ℝ)) ≤ u := by
    rw [hu_def]
    nlinarith [mul_nonneg hc0.le (show (0:ℝ) ≤ ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1) by positivity)]
  have hupos : 0 < u := lt_of_lt_of_le hu0 hule
  have hat1 : aheadTerm c 1 i k = Real.exp (-u) := by
    rw [aheadTerm]; congr 1; rw [hu_def]; push_cast; ring
  have hd0 : 0 < 1 - Real.exp (-(c/(2*(i:ℝ)))) := by
    have : Real.exp (-(c/(2*(i:ℝ)))) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hd : 0 < 1 - Real.exp (-u) := by
    have : Real.exp (-u) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hdd : 1 - Real.exp (-(c/(2*(i:ℝ)))) ≤ 1 - Real.exp (-u) := by
    have : Real.exp (-u) ≤ Real.exp (-(c/(2*(i:ℝ)))) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hfactor : Real.exp u - 1 = Real.exp u * (1 - Real.exp (-u)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hat1, poleExcess, hfactor, one_div, mul_inv, ← Real.exp_neg,
    mul_comm ((1 - Real.exp (-(c/(2*(i:ℝ)))))⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hd0 hdd

theorem aheadTerm_prod_summable {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 2 ≤ i) :
    Summable (Function.uncurry (fun k n => aheadTerm c n i k)) := by
  have hnn : ∀ p : ℕ × ℕ+, 0 ≤ Function.uncurry (fun k n => aheadTerm c n i k) p :=
    fun p => (Real.exp_pos _).le
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun k => (poleExcess_hasSum (ahead_pos hc (by omega) k)).summable, ?_⟩
  have hC : Summable (fun k:ℕ => (1 - Real.exp (-(c/(2*(i:ℝ)))))⁻¹ * aheadTerm c 1 i k) :=
    (aheadTerm_summable hc 1 hi).mul_left _
  have hkey : Summable (fun k:ℕ => poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1))) :=
    Summable.of_nonneg_of_le (fun k => (poleExcess_pos (ahead_pos hc (by omega) k)).le)
      (fun k => poleExcess_ahead_le hc (by omega) k) hC
  exact hkey.congr (fun k => poleExcess_ahead hc (by omega) k)

theorem summable_prod_swap {α β : Type*} (g : α → β → ℝ)
    (hf : Summable (Function.uncurry g)) : Summable (fun p : β × α => g p.2 p.1) := by
  apply (hf.comp_injective (Equiv.prodComm β α).injective).congr
  rintro ⟨n, k⟩; rfl

theorem aheadShell_summable {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 2 ≤ i) :
    Summable (fun n : ℕ+ => aheadShell c n i) := by
  have hnn' : ∀ p : ℕ+ × ℕ, 0 ≤ (fun q : ℕ+ × ℕ => aheadTerm c q.1 i q.2) p :=
    fun p => (Real.exp_pos _).le
  have hswap : Summable (fun p : ℕ+ × ℕ => aheadTerm c p.1 i p.2) :=
    summable_prod_swap (fun k n => aheadTerm c n i k) (aheadTerm_prod_summable hc hi)
  have hmarg : Summable (fun n : ℕ+ => ∑' k, aheadTerm c n i k) :=
    ((summable_prod_of_nonneg hnn').mp hswap).2
  exact (hmarg.mul_left (1/(i:ℝ))).congr (fun n => by rw [aheadShell])

theorem behindShell_summable {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 2 ≤ i) :
    Summable (fun n : ℕ+ => behindShell c n i) := by
  have h : Summable (fun n : ℕ+ => ∑ k ∈ Finset.range i, behindTerm c n i k) := by
    apply summable_sum
    intro k hk; rw [Finset.mem_range] at hk
    exact (poleExcess_hasSum (behind_pos hc (by omega) hk)).summable
  exact (h.mul_left (1/(i:ℝ))).congr (fun n => by rw [behindShell])

theorem tsum_aheadShell {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 2 ≤ i) :
    ∑' n : ℕ+, aheadShell c n i
      = (1/(i:ℝ)) * ∑' k:ℕ, poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)+j+1)) := by
  simp only [aheadShell]
  rw [tsum_mul_left, Summable.tsum_comm (aheadTerm_prod_summable hc hi)]
  congr 1
  exact tsum_congr (fun k => (poleExcess_ahead hc (by omega) k).symm)

theorem tsum_behindShell {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 2 ≤ i) :
    ∑' n : ℕ+, behindShell c n i
      = (1/(i:ℝ)) * ∑ k ∈ Finset.range i, poleExcess (c/(2*(i:ℝ)) + c * ∑ j ∈ Finset.range k, 1/((i:ℝ)-1-j)) := by
  simp only [behindShell]
  rw [tsum_mul_left]
  congr 1
  rw [Summable.tsum_finsetSum (fun k hk => by
    rw [Finset.mem_range] at hk
    exact (poleExcess_hasSum (behind_pos hc (by omega) hk)).summable)]
  apply Finset.sum_congr rfl
  intro k hk; rw [Finset.mem_range] at hk
  exact (poleExcess_behind hc (by omega) hk).symm

theorem poleModelDiff_eq {c : ℝ} (hc : 1 < c) {i : ℕ} (hi : 2 ≤ i) :
    poleModelDiff c i = ∑' n : ℕ+, shellDiffTerm c n i := by
  have hsub : ∀ n : ℕ+, shellDiffTerm c n i = aheadShell c n i - behindShell c n i :=
    fun n => rfl
  rw [tsum_congr hsub, (aheadShell_summable hc hi).tsum_sub (behindShell_summable hc hi),
    tsum_aheadShell hc hi, tsum_behindShell hc hi, poleModelDiff]

theorem tendsto_poleModel {c : ℝ} (hc : 1 < c) :
    Tendsto (fun i : ℕ => poleModelDiff c i) atTop (𝓝 (stripResidue c)) := by
  refine (tendsto_shellSum_stripResidue hc).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with i hi
  exact (poleModelDiff_eq hc hi).symm

end RHTower
end
