import GaloisForLFunctions.RHTower.Sieve.LogWindowDiscreteTransfer
import GaloisForLFunctions.RHTower.Sieve.FibreLogCharacterisation
import GaloisForLFunctions.RHTower.Sieve.GallagherDyadicTail
import GaloisForLFunctions.RHTower.Sieve.MRFibreReduction

/-!
# The fibre sum is a logarithmic window sum

`FibreLogCharacterisation` identifies the fibre above `a` with the closed logarithmic window
`[log(x/a), log(x/a) + fibreWidth x h]`, while `logWindowSum` uses the half-open window
`(u, u + δ]`.  The two differ only at the lower endpoint, where at most one integer can sit, so the
fibre sum and the window sum differ by at most one coefficient.

This is the bridge between the Matomäki--Radziwiłł fibre decomposition and the Plancherel identity:
after it, the averaged fibre mean square is a sum of window sums at the `√x` sample points
`log(x/a)`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The common index set carrying every fibre: the outer factor is at least `√x`, so every fibre
element is at most `√x + h`. -/
noncomputable def fibreIndex (x h : ℝ) : Finset ℕ := Finset.Icc 1 ⌊Real.sqrt x + h⌋₊

theorem mem_fibreIndex {x h : ℝ} {b : ℕ} :
    b ∈ fibreIndex x h ↔ 1 ≤ b ∧ b ≤ ⌊Real.sqrt x + h⌋₊ := by
  rw [fibreIndex, Finset.mem_Icc]

theorem innerFibre_subset_fibreIndex {x h : ℝ} (hx : 4 ≤ x) {a : ℕ}
    (ha : a ∈ outerBlock x h) : innerFibre x h a ⊆ fibreIndex x h := by
  intro b hb
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have halo : Real.sqrt x ≤ (a : ℝ) := by
    rw [outerBlock, Finset.mem_filter] at ha
    exact ha.2.1
  rw [innerFibre, Finset.mem_filter] at hb
  obtain ⟨hbIcc, -, hhi⟩ := hb
  rw [Finset.mem_Icc] at hbIcc
  refine mem_fibreIndex.2 ⟨hbIcc.1, ?_⟩
  have hcast : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; ring
  rw [hcast] at hhi
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hble : (b : ℝ) ≤ Real.sqrt x + h := by
    nlinarith [hhi, halo, hb0, hsx, hsq]
  exact Nat.le_floor hble

/-- At most one integer has a prescribed logarithm. -/
theorem card_filter_log_eq_le_one (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (u : ℝ) :
    (s.filter (fun b : ℕ => Real.log (b : ℝ) = u)).card ≤ 1 := by
  classical
  refine Finset.card_le_one.2 fun b hb c hc => ?_
  rw [Finset.mem_filter] at hb hc
  have hb0 : (0 : ℝ) < (b : ℝ) := by
    have := hs b hb.1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hc0 : (0 : ℝ) < (c : ℝ) := by
    have := hs c hc.1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlog : Real.log (b : ℝ) = Real.log (c : ℝ) := by rw [hb.2, hc.2]
  have : (b : ℝ) = (c : ℝ) := by
    rw [← Real.exp_log hb0, ← Real.exp_log hc0, hlog]
  exact_mod_cast this

/-- The logarithmic window sum, as a sum over a filtered index set. -/
theorem logWindowSum_eq_sum_filter (a : ℕ → ℂ) (s : Finset ℕ) (δ u : ℝ) :
    logWindowSum a s δ u
      = ∑ b ∈ s.filter (fun b : ℕ => u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ), a b := by
  classical
  rw [logWindowSum_eq_sum_indicator, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : u < Real.log b ∧ Real.log b ≤ u + δ
  · rw [if_pos hb, Set.indicator_of_mem]
    rw [logWindow, Set.mem_Ico]
    exact ⟨by linarith [hb.2], hb.1⟩
  · rw [if_neg hb, Set.indicator_of_notMem]
    rw [logWindow, Set.mem_Ico]
    intro hmem
    exact hb ⟨hmem.2, by linarith [hmem.1]⟩

/-- **The fibre sum and the window sum differ by at most one coefficient.** -/
theorem norm_fibreSum_sub_logWindowSum_le {f : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |f n| ≤ M)
    (hM0 : 0 ≤ M) {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) {a : ℕ} (ha : a ∈ outerBlock x h) :
    ‖((∑ b ∈ innerFibre x h a, f b : ℝ) : ℂ)
        - logWindowSum (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x h) (fibreWidth x h)
            (Real.log (x / a))‖ ≤ M := by
  classical
  set u : ℝ := Real.log (x / a) with hu
  set δ : ℝ := fibreWidth x h with hδ
  set s : Finset ℕ := fibreIndex x h with hs
  have hs1 : ∀ n ∈ s, 1 ≤ n := fun n hn => (mem_fibreIndex.1 hn).1
  have hδ0 : 0 ≤ δ := by
    rw [hδ, fibreWidth]
    refine Real.log_nonneg ?_
    have hxs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have : (0 : ℝ) ≤ h / Real.sqrt x := by positivity
    linarith
  -- the fibre as a filtered sum
  have hfib : innerFibre x h a
      = s.filter (fun b : ℕ => u ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ) := by
    ext b
    constructor
    · intro hb
      have hbs : b ∈ s := innerFibre_subset_fibreIndex hx ha hb
      have hb1 : 1 ≤ b := hs1 b hbs
      exact Finset.mem_filter.2 ⟨hbs, (mem_innerFibre_iff_log hx hh ha hb1).1 hb⟩
    · intro hb
      rw [Finset.mem_filter] at hb
      have hb1 : 1 ≤ b := hs1 b hb.1
      exact (mem_innerFibre_iff_log hx hh ha hb1).2 hb.2
  -- the two filters differ inside the endpoint fibre
  have hsubset : s.filter (fun b : ℕ => u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ)
      ⊆ s.filter (fun b : ℕ => u ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ) := by
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, le_of_lt hb.2.1, hb.2.2⟩
  have hdiff : (s.filter (fun b : ℕ => u ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ))
        \ (s.filter (fun b : ℕ => u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ))
      ⊆ s.filter (fun b : ℕ => Real.log (b : ℝ) = u) := by
    intro b hb
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hb
    obtain ⟨⟨hbs, hlo, hhi⟩, hnot⟩ := hb
    refine Finset.mem_filter.2 ⟨hbs, ?_⟩
    by_contra hne
    exact hnot ⟨hbs, lt_of_le_of_ne hlo (Ne.symm hne), hhi⟩
  -- the difference of the sums
  have hsplit : ((∑ b ∈ innerFibre x h a, f b : ℝ) : ℂ)
        - logWindowSum (fun n => ((f n : ℝ) : ℂ)) s δ u
      = ∑ b ∈ (s.filter (fun b : ℕ => u ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ))
          \ (s.filter (fun b : ℕ => u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ)), ((f b : ℝ) : ℂ) := by
    rw [logWindowSum_eq_sum_filter, hfib, Complex.ofReal_sum,
      ← Finset.sum_sdiff_eq_sub hsubset]
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ b ∈ (s.filter (fun b : ℕ => u ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ))
      \ (s.filter (fun b : ℕ => u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ)),
      ‖((f b : ℝ) : ℂ)‖ ≤ M := by
    intro b _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM b
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((s.filter (fun b : ℕ => u ≤ Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ))
      \ (s.filter (fun b : ℕ => u < Real.log (b : ℝ) ∧ Real.log (b : ℝ) ≤ u + δ))).card : ℝ) ≤ 1 := by
    have := le_trans (Finset.card_le_card hdiff) (card_filter_log_eq_le_one s hs1 u)
    exact_mod_cast this
  nlinarith [hcard, hM0]

/-! ## The sample points -/

/-- The logarithmic starting point of the fibre above `a`. -/
noncomputable def fibreLogStart (x : ℝ) (a : ℕ) : ℝ := Real.log (x / a)

/-- **The fibre starting points are `1/(2√x)`-separated.**  The gap between consecutive outer
factors is at least `1/a' ≥ 1/(2√x)` in the logarithmic variable. -/
theorem fibreLogStart_separated {x h : ℝ} (hx : 4 ≤ x) {a a' : ℕ}
    (ha : a ∈ outerBlock x h) (ha' : a' ∈ outerBlock x h) (hlt : a < a') :
    fibreLogStart x a' + 1 / (2 * Real.sqrt x) ≤ fibreLogStart x a := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [outerBlock, Finset.mem_filter] at ha ha'
  obtain ⟨-, halo, -⟩ := ha
  obtain ⟨-, -, hahi'⟩ := ha'
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hsx halo
  have haa' : (a : ℝ) < (a' : ℝ) := by exact_mod_cast hlt
  have ha'0 : (0 : ℝ) < (a' : ℝ) := lt_trans ha0 haa'
  have hratio : (1 : ℝ) < (a' : ℝ) / (a : ℝ) := (one_lt_div ha0).2 haa'
  have hlog : 1 - ((a' : ℝ) / (a : ℝ))⁻¹ ≤ Real.log ((a' : ℝ) / (a : ℝ)) :=
    Real.one_sub_inv_le_log_of_pos (by linarith)
  have hinv : ((a' : ℝ) / (a : ℝ))⁻¹ = (a : ℝ) / (a' : ℝ) := by
    rw [inv_div]
  have hgap : 1 / (2 * Real.sqrt x) ≤ 1 - (a : ℝ) / (a' : ℝ) := by
    have hstep : 1 - (a : ℝ) / (a' : ℝ) = ((a' : ℝ) - (a : ℝ)) / (a' : ℝ) := by
      field_simp
    rw [hstep]
    have hnum : (1 : ℝ) ≤ (a' : ℝ) - (a : ℝ) := by
      have : (a : ℕ) + 1 ≤ a' := hlt
      have hc : ((a : ℕ) : ℝ) + 1 ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [div_le_div_iff₀ (by positivity) ha'0]
    nlinarith [hahi', hsx, hnum]
  have hsplit : Real.log ((a' : ℝ) / (a : ℝ))
      = fibreLogStart x a - fibreLogStart x a' := by
    rw [fibreLogStart, fibreLogStart,
      Real.log_div (ne_of_gt hx0) (ne_of_gt ha0),
      Real.log_div (ne_of_gt hx0) (ne_of_gt ha'0),
      Real.log_div (ne_of_gt ha'0) (ne_of_gt ha0)]
    ring
  rw [hinv] at hlog
  rw [hsplit] at hlog
  linarith

/-! ## The transfer to the Plancherel integral -/

theorem exp_fibreLogStart {x : ℝ} (hx : 4 ≤ x) {h : ℝ} {a : ℕ} (ha : a ∈ outerBlock x h) :
    Real.exp (fibreLogStart x a) = x / (a : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [outerBlock, Finset.mem_filter] at ha
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hsx ha.2.1
  rw [fibreLogStart, Real.exp_log (by positivity)]

theorem exp_fibreLogStart_le {x : ℝ} (hx : 4 ≤ x) {h : ℝ} {a : ℕ} (ha : a ∈ outerBlock x h) :
    Real.exp (fibreLogStart x a) ≤ Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hlo : Real.sqrt x ≤ (a : ℝ) := by
    rw [outerBlock, Finset.mem_filter] at ha
    exact ha.2.1
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hsx hlo
  rw [exp_fibreLogStart hx ha, div_le_iff₀ ha0]
  nlinarith [hlo, hsx, hsq]

theorem exp_fibreWidth {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) :
    Real.exp (fibreWidth x h) = 1 + h / Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [fibreWidth, Real.exp_log (by positivity)]

/-- **The oscillation of the window sum over one separation cell is bounded by five.** -/
theorem norm_logWindowSum_osc_le {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 ≤ x)
    (hh0 : 0 ≤ h) (hhx : h ≤ Real.sqrt x) {a : ℕ} (ha : a ∈ outerBlock x h) {v : ℝ}
    (hv : v ∈ Set.Ico (fibreLogStart x a) (fibreLogStart x a + 1 / (2 * Real.sqrt x))) :
    ‖logWindowSum (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x h) (fibreWidth x h)
        (fibreLogStart x a)
      - logWindowSum (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x h) (fibreWidth x h) v‖ ≤ 5 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsx2 : (2 : ℝ) ≤ Real.sqrt x := by
    have hle : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rwa [show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hle
  set u : ℝ := fibreLogStart x a with hudef
  set lam : ℝ := 1 / (2 * Real.sqrt x) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlamhalf : lam ≤ 1 / 2 := by
    rw [hlamdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hM : ∀ n : ℕ, ‖((f n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  have hs1 : ∀ n ∈ fibreIndex x h, 1 ≤ n := fun n hn => (mem_fibreIndex.1 hn).1
  have hbase := logWindowDiscreteTransferNorm_logWindowSum_sub_le (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x h) hs1 hM
    (δ := fibreWidth x h) (u := u) (u' := v) hv.1
  refine hbase.trans ?_
  -- the exponential increments
  have hexpu : Real.exp u ≤ Real.sqrt x := exp_fibreLogStart_le hx ha
  have hexpδ : Real.exp (fibreWidth x h) ≤ 2 := by
    rw [exp_fibreWidth hx hh0]
    have hle : h / Real.sqrt x ≤ 1 := by
      rw [div_le_one hsx]
      exact hhx
    linarith
  have hlamexp : Real.exp lam ≤ 1 + 2 * lam := by
    have h1 : (1 : ℝ) - lam ≤ Real.exp (-lam) := by
      have := Real.add_one_le_exp (-lam)
      linarith
    have h2 : (0 : ℝ) < 1 - lam := by linarith
    have h3 : Real.exp lam * Real.exp (-lam) = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : Real.exp lam * (1 - lam) ≤ 1 := by
      nlinarith [Real.exp_pos lam, h1, h3]
    nlinarith [h4, hlam0, hlamhalf]
  have hstep : Real.exp v - Real.exp u ≤ 1 := by
    have hvle : v ≤ u + lam := le_of_lt hv.2
    have hmono : Real.exp v ≤ Real.exp (u + lam) := Real.exp_le_exp.2 hvle
    have hprod : Real.exp (u + lam) = Real.exp u * Real.exp lam := Real.exp_add u lam
    have hexpu0 : (0 : ℝ) < Real.exp u := Real.exp_pos u
    have hkey : Real.exp u * Real.exp lam - Real.exp u ≤ Real.sqrt x * (2 * lam) := by
      have h1 : Real.exp u * Real.exp lam - Real.exp u
          = Real.exp u * (Real.exp lam - 1) := by ring
      rw [h1]
      have h2 : Real.exp lam - 1 ≤ 2 * lam := by linarith
      nlinarith [hexpu, hexpu0, hlam0, h2]
    have hval : Real.sqrt x * (2 * lam) = 1 := by
      rw [hlamdef]
      field_simp
    rw [hval] at hkey
    linarith [hmono, hprod]
  have hstep2 : Real.exp (v + fibreWidth x h) - Real.exp (u + fibreWidth x h) ≤ 2 := by
    have hid : Real.exp (v + fibreWidth x h) - Real.exp (u + fibreWidth x h)
        = Real.exp (fibreWidth x h) * (Real.exp v - Real.exp u) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [hid]
    have hd0 : (0 : ℝ) ≤ Real.exp v - Real.exp u := by
      have := Real.exp_le_exp.2 hv.1
      linarith
    nlinarith [hexpδ, hd0, Real.exp_pos (fibreWidth x h)]
  nlinarith [hstep, hstep2]

set_option maxHeartbeats 1000000 in
/-- **The averaged fibre mean square is controlled by the Plancherel integral.**  The fibre sums are
window sums at `1/(2√x)`-separated sample points, so the discrete average is at most `8√x` times the
continuous `L²` norm of the window sum, plus a term of size `√x`. -/
theorem sum_fibreSum_sq_le_integral {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 ≤ x)
    (hh0 : 0 ≤ h) (hhx : h ≤ Real.sqrt x) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      ≤ 8 * Real.sqrt x * (∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
            (fibreIndex x h) (fibreWidth x h) u‖ ^ 2)
        + 102 * (Real.sqrt x + 1) := by
  classical
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  set lam : ℝ := 1 / (2 * Real.sqrt x) with hlamdef
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  set S : ℝ → ℂ := logWindowSum (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x h) (fibreWidth x h)
    with hSdef
  -- pointwise comparison
  have hpoint : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, f b) ^ 2 ≤ 2 * ‖S (fibreLogStart x a)‖ ^ 2 + 2 := by
    intro a ha
    have hcmp := norm_fibreSum_sub_logWindowSum_le (f := f) (M := 1)
      (fun n => hf n) (by norm_num) hx hh0 ha
    have habs : |∑ b ∈ innerFibre x h a, f b| ≤ ‖S (fibreLogStart x a)‖ + 1 := by
      have hnorm : ‖((∑ b ∈ innerFibre x h a, f b : ℝ) : ℂ)‖
          = |∑ b ∈ innerFibre x h a, f b| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have htri := norm_sub_norm_le
        (((∑ b ∈ innerFibre x h a, f b : ℝ) : ℂ)) (S (fibreLogStart x a))
      rw [hnorm] at htri
      have hcmp' : ‖((∑ b ∈ innerFibre x h a, f b : ℝ) : ℂ) - S (fibreLogStart x a)‖ ≤ 1 := by
        rw [hSdef, fibreLogStart]
        exact hcmp
      linarith [htri, hcmp']
    have hsq : (∑ b ∈ innerFibre x h a, f b) ^ 2
        = |∑ b ∈ innerFibre x h a, f b| ^ 2 := (sq_abs _).symm
    rw [hsq]
    have h0 : (0 : ℝ) ≤ |∑ b ∈ innerFibre x h a, f b| := abs_nonneg _
    have hsq2 : |∑ b ∈ innerFibre x h a, f b| ^ 2 ≤ (‖S (fibreLogStart x a)‖ + 1) ^ 2 :=
      pow_le_pow_left₀ h0 habs 2
    nlinarith [hsq2, sq_nonneg (‖S (fibreLogStart x a)‖ - 1)]
  -- the separation
  have hdisj : ((outerBlock x h : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun a => Set.Ico (fibreLogStart x a) (fibreLogStart x a + lam) := by
    intro a ha a' ha' hne
    have hmem : a ∈ outerBlock x h := ha
    have hmem' : a' ∈ outerBlock x h := ha'
    refine Set.disjoint_left.2 fun y hy hy' => ?_
    rw [hlamdef] at hy hy'
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsep := fibreLogStart_separated hx hmem hmem' hlt
      exact absurd hy'.2 (not_lt.2 (le_trans hsep hy.1))
    · have hsep := fibreLogStart_separated hx hmem' hmem hgt
      exact absurd hy.2 (not_lt.2 (le_trans hsep hy'.1))
  -- the oscillation
  have hosc : ∀ a ∈ outerBlock x h,
      ∀ v ∈ Set.Ico (fibreLogStart x a) (fibreLogStart x a + lam),
      ‖S (fibreLogStart x a) - S v‖ ≤ 5 := by
    intro a ha v hv
    rw [hSdef]
    exact norm_logWindowSum_osc_le hf hx hh0 hhx ha (by rw [← hlamdef]; exact hv)
  have htransfer := sum_normSq_logWindowSum_le_integral (fun n => ((f n : ℝ) : ℂ))
    (fibreIndex x h) (fibreWidth x h) hlam0 (by norm_num : (0 : ℝ) ≤ 5)
    (outerBlock x h) (fibreLogStart x) hdisj hosc
  rw [← hSdef] at htransfer
  -- assemble
  have hcard := card_outerBlock_le hx hh0
  have hsum1 : ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2
      ≤ ∑ a ∈ outerBlock x h, (2 * ‖S (fibreLogStart x a)‖ ^ 2 + 2) :=
    Finset.sum_le_sum hpoint
  have hsplit : ∑ a ∈ outerBlock x h, (2 * ‖S (fibreLogStart x a)‖ ^ 2 + 2)
      = 2 * (∑ a ∈ outerBlock x h, ‖S (fibreLogStart x a)‖ ^ 2)
        + 2 * ((outerBlock x h).card : ℝ) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  have hlamval : lam * (2 * Real.sqrt x) = 1 := by
    rw [hlamdef]
    field_simp
  have hkey : ∑ a ∈ outerBlock x h, ‖S (fibreLogStart x a)‖ ^ 2
      ≤ 4 * Real.sqrt x * (∫ u : ℝ, ‖S u‖ ^ 2) + 50 * ((outerBlock x h).card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left htransfer (le_of_lt (by positivity : (0:ℝ) < 2 * Real.sqrt x))
    have hlhs : (2 * Real.sqrt x) * (lam * ∑ a ∈ outerBlock x h, ‖S (fibreLogStart x a)‖ ^ 2)
        = ∑ a ∈ outerBlock x h, ‖S (fibreLogStart x a)‖ ^ 2 := by
      rw [← mul_assoc, mul_comm (2 * Real.sqrt x) lam, hlamval, one_mul]
    rw [hlhs] at hmul
    refine hmul.trans (le_of_eq ?_)
    rw [hlamdef]
    field_simp
    ring
  have hcard0 : (0 : ℝ) ≤ ((outerBlock x h).card : ℝ) := Nat.cast_nonneg _
  have hint0 : (0 : ℝ) ≤ ∫ u : ℝ, ‖S u‖ ^ 2 := by
    refine MeasureTheory.integral_nonneg fun u => ?_
    positivity
  linarith [hsum1, hsplit.le, hsplit.ge, hkey, hcard, hcard0]

/-- **The averaged fibre mean square from a spectral majorant.**  After Plancherel the whole
Matomäki--Radziwiłł input is a statement about the `L²` norm of the logarithmic window sum: if that
norm is `o(h²)`, the fibre mean square the Route E cards consume tends to zero. -/
theorem averagedMeanSquare_of_spectral {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {hh : ℝ → ℝ}
    (hgrow : Filter.Tendsto hh Filter.atTop Filter.atTop)
    (hhx : ∀ᶠ x : ℝ in Filter.atTop, hh x ≤ Real.sqrt x)
    (hspec : Filter.Tendsto (fun x : ℝ => (∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
          (fibreIndex x (hh x)) (fibreWidth x (hh x)) u‖ ^ 2) / hh x ^ 2)
      Filter.atTop (nhds 0)) :
    AveragedMeanSquare f hh := by
  have hsqinv : Filter.Tendsto (fun x : ℝ => 1 / hh x ^ 2) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun x : ℝ => hh x ^ 2) Filter.atTop Filter.atTop := by
      have := hgrow.atTop_mul_atTop₀ hgrow
      refine this.congr fun x => ?_
      ring
    refine (hsq.inv_tendsto_atTop).congr fun x => ?_
    simp [one_div]
  have hmaj : Filter.Tendsto (fun x : ℝ =>
      8 * ((∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
          (fibreIndex x (hh x)) (fibreWidth x (hh x)) u‖ ^ 2) / hh x ^ 2)
        + 204 * (1 / hh x ^ 2)) Filter.atTop (nhds 0) := by
    have h1 := hspec.const_mul (8 : ℝ)
    have h2 := hsqinv.const_mul (204 : ℝ)
    have := h1.add h2
    simpa using this
  rw [AveragedMeanSquare]
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hhx, Filter.eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop (1 : ℝ)]
    with x hhxx hx hhone
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsx1 : (1 : ℝ) ≤ Real.sqrt x := by
    have hle : Real.sqrt 1 ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_one] at hle
  have hh0 : (0 : ℝ) ≤ hh x := by linarith
  have hbridge := sum_fibreSum_sq_le_integral hf hx hh0 hhxx
  set I : ℝ := ∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
      (fibreIndex x (hh x)) (fibreWidth x (hh x)) u‖ ^ 2 with hIdef
  have hI0 : (0 : ℝ) ≤ I := by
    rw [hIdef]
    refine MeasureTheory.integral_nonneg fun u => ?_
    positivity
  have hnum0 : (0 : ℝ) ≤ ∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have hden : (0 : ℝ) < hh x ^ 2 * Real.sqrt x := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ hden]
  have hexpand : (8 * (I / hh x ^ 2) + 204 * (1 / hh x ^ 2)) * (hh x ^ 2 * Real.sqrt x)
      = 8 * Real.sqrt x * I + 204 * Real.sqrt x := by
    field_simp
  rw [hexpand]
  have htail : (102 : ℝ) * (Real.sqrt x + 1) ≤ 204 * Real.sqrt x := by nlinarith [hsx1]
  linarith [hbridge, htail]

theorem fibreWidth_nonneg {x h : ℝ} (hx : 4 ≤ x) (hh : 0 ≤ h) : 0 ≤ fibreWidth x h := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  rw [fibreWidth]
  refine Real.log_nonneg ?_
  have : (0 : ℝ) ≤ h / Real.sqrt x := by positivity
  linarith

/-- **The averaged fibre mean square from the spectral side.**  Plancherel turns the interface into
a statement about the Dirichlet polynomial itself, weighted by the window kernel. -/
theorem averagedMeanSquare_of_spectralPoly {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {hh : ℝ → ℝ}
    (hgrow : Filter.Tendsto hh Filter.atTop Filter.atTop)
    (hhx : ∀ᶠ x : ℝ in Filter.atTop, hh x ≤ Real.sqrt x)
    (hspec : Filter.Tendsto (fun x : ℝ =>
        (∫ w : ℝ, ‖logWindowKernel (fibreWidth x (hh x)) w‖ ^ 2
            * ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x (hh x)) w‖ ^ 2) / hh x ^ 2)
      Filter.atTop (nhds 0)) :
    AveragedMeanSquare f hh := by
  refine averagedMeanSquare_of_spectral hf hgrow hhx ?_
  refine hspec.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop (0 : ℝ)]
    with x hx hh0
  rw [integral_normSq_logWindowSum_eq _ _ (fibreWidth_nonneg hx hh0)]

/-- **The averaged fibre mean square from an affine mean-square majorant.**  Gallagher's dyadic
split pays every frequency by a mean square, so the whole Matomäki--Radziwiłł input reduces to an
affine majorant `∫_{|w| ≤ T}|A|² ≤ αT + β` for the Dirichlet polynomial of the fibre range, together
with the requirement that the resulting budget be `o(h²)`. -/
theorem averagedMeanSquare_of_gallagherBudget {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1)
    {hh W α β : ℝ → ℝ}
    (hgrow : Filter.Tendsto hh Filter.atTop Filter.atTop)
    (hhx : ∀ᶠ x : ℝ in Filter.atTop, hh x ≤ Real.sqrt x)
    (hWpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < W x)
    (hmaj : ∀ᶠ x : ℝ in Filter.atTop, ∀ T : ℝ, W x ≤ T →
      (∫ w in Set.Icc (-T) T,
          ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x (hh x)) w‖ ^ 2)
        ≤ α x * T + β x)
    (hlim : Filter.Tendsto (fun x : ℝ =>
        (2 * fibreWidth x (hh x) ^ 2 * (α x * W x + β x)
          + (4 * α x / (Real.pi ^ 2 * W x) + 4 * β x / (3 * Real.pi ^ 2 * W x ^ 2))) / hh x ^ 2)
      Filter.atTop (nhds 0)) :
    AveragedMeanSquare f hh := by
  refine averagedMeanSquare_of_spectral hf hgrow hhx ?_
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hWpos, hmaj, Filter.eventually_ge_atTop (4 : ℝ),
    hgrow.eventually_ge_atTop (1 : ℝ)] with x hWx hmjx hx hh1
  have hδ : 0 < fibreWidth x (hh x) := fibreWidth_pos (by linarith) (by linarith)
  have hbud := gallagher_split_integral_dyadic (fun n => ((f n : ℝ) : ℂ))
    (fibreIndex x (hh x)) hδ hWx hmjx
  have hint0 : (0 : ℝ) ≤ ∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
      (fibreIndex x (hh x)) (fibreWidth x (hh x)) u‖ ^ 2 := by
    refine MeasureTheory.integral_nonneg fun u => ?_
    positivity
  have hh0 : (0 : ℝ) < hh x := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right hbud (by positivity)

/-- **The Möbius capstone.**  An affine mean-square majorant for the Möbius Dirichlet polynomial of
the fibre range, whose Gallagher budget is `o(h²)`, gives the averaged short-interval cancellation
the Route E cards consume. -/
theorem averagedShortInterval_moebius_of_gallagherBudget {hh W α β : ℝ → ℝ}
    (hgrow : Filter.Tendsto hh Filter.atTop Filter.atTop)
    (hhx : ∀ᶠ x : ℝ in Filter.atTop, hh x ≤ Real.sqrt x)
    (hWpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < W x)
    (hmaj : ∀ᶠ x : ℝ in Filter.atTop, ∀ T : ℝ, W x ≤ T →
      (∫ w in Set.Icc (-T) T,
          ‖logPoly (fun n => (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ)) (fibreIndex x (hh x)) w‖ ^ 2)
        ≤ α x * T + β x)
    (hlim : Filter.Tendsto (fun x : ℝ =>
        (2 * fibreWidth x (hh x) ^ 2 * (α x * W x + β x)
          + (4 * α x / (Real.pi ^ 2 * W x) + 4 * β x / (3 * Real.pi ^ 2 * W x ^ 2))) / hh x ^ 2)
      Filter.atTop (nhds 0)) :
    AveragedShortInterval (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh :=
  averagedShortInterval_of_meanSquare hgrow
    (averagedMeanSquare_of_gallagherBudget abs_moebius_real_le_one hgrow hhx hWpos hmaj hlim)

/-- The two Möbius coefficient normalisations of this folder agree. -/
theorem logPoly_moebius_congr (s : Finset ℕ) (w : ℝ) :
    logPoly (fun n => (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ)) s w
      = logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s w := by
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1

/-- **The Route E gate, in the corpus's Möbius normalisation.**  This is the form the Ramaré chain
(`Sieve/RamarePrimeOffDiagonal`) produces: an affine majorant for the Möbius mean square on
`[-T, T]` whose Gallagher budget is `o(h²)` gives the averaged short-interval cancellation. -/
theorem averagedShortInterval_moebius_of_affineMajorant {hh W α β : ℝ → ℝ}
    (hgrow : Filter.Tendsto hh Filter.atTop Filter.atTop)
    (hhx : ∀ᶠ x : ℝ in Filter.atTop, hh x ≤ Real.sqrt x)
    (hWpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < W x)
    (hmaj : ∀ᶠ x : ℝ in Filter.atTop, ∀ T : ℝ, W x ≤ T →
      (∫ w in Set.Icc (-T) T,
          ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (fibreIndex x (hh x)) w‖ ^ 2)
        ≤ α x * T + β x)
    (hlim : Filter.Tendsto (fun x : ℝ =>
        (2 * fibreWidth x (hh x) ^ 2 * (α x * W x + β x)
          + (4 * α x / (Real.pi ^ 2 * W x) + 4 * β x / (3 * Real.pi ^ 2 * W x ^ 2))) / hh x ^ 2)
      Filter.atTop (nhds 0)) :
    AveragedShortInterval (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  refine averagedShortInterval_moebius_of_gallagherBudget hgrow hhx hWpos ?_ hlim
  filter_upwards [hmaj] with x hx T hT
  have hcongr : (∫ w in Set.Icc (-T) T,
      ‖logPoly (fun n => (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ))
        (fibreIndex x (hh x)) w‖ ^ 2)
      = ∫ w in Set.Icc (-T) T,
          ‖logPoly (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
            (fibreIndex x (hh x)) w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [logPoly_moebius_congr]
  rw [hcongr]
  exact hx T hT

/-! ## The fibres live in a dyadic block -/

/-- The dyadic block carrying every fibre: the outer factor lies in `[√x, 2√x]`, so every fibre
element lies between `√x/2` and `√x + h`. -/
noncomputable def fibreDyadicIndex (x h : ℝ) : Finset ℕ :=
  Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌊Real.sqrt x + h⌋₊

theorem fibreDyadicIndex_subset {x : ℝ} (hx : 4 ≤ x) (h : ℝ) :
    fibreDyadicIndex x h ⊆ fibreIndex x h := by
  intro b hb
  rw [fibreDyadicIndex, Finset.mem_Icc] at hb
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have h1 : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
  exact mem_fibreIndex.2 ⟨le_trans h1 hb.1, hb.2⟩

/-- **Every fibre lies in a block of ratio at most four.**  This is the structural fact the product
decomposition of the Matomäki--Radziwiłł argument needs: the Möbius polynomial of the reduction is
supported on a dyadic block, not on an initial segment. -/
theorem innerFibre_subset_fibreDyadicIndex {x h : ℝ} (hx : 4 ≤ x) {a : ℕ}
    (ha : a ∈ outerBlock x h) : innerFibre x h a ⊆ fibreDyadicIndex x h := by
  intro b hb
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hahi : (a : ℝ) ≤ 2 * Real.sqrt x := by
    rw [outerBlock, Finset.mem_filter] at ha
    exact ha.2.2
  have halo : Real.sqrt x ≤ (a : ℝ) := by
    rw [outerBlock, Finset.mem_filter] at ha
    exact ha.2.1
  have ha0 : (0 : ℝ) < (a : ℝ) := lt_of_lt_of_le hsx halo
  have hbtop := innerFibre_subset_fibreIndex hx ha hb
  rw [innerFibre, Finset.mem_filter] at hb
  obtain ⟨-, hlo, -⟩ := hb
  have hcast : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; ring
  rw [hcast] at hlo
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hblo : Real.sqrt x / 2 ≤ (b : ℝ) := by
    nlinarith [hlo, hahi, hb0, hsx, hsq]
  refine Finset.mem_Icc.2 ⟨Nat.ceil_le.2 hblo, (mem_fibreIndex.1 hbtop).2⟩

end

end RHTower.Sieve
