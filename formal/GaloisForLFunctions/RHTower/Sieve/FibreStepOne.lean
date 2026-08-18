import GaloisForLFunctions.RHTower.Sieve.GoodStartFibreWindow
import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquare

/-!
# Step 1 at the fibre data, with the analytic input discharged
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction

/-- **Every fibre is long.**  The fibre above `a ∈ [√x, 2√x]` has length at least `h/4`. -/
theorem fibreLen_ge {x h : ℝ} (hx : 4 ≤ x) (hh : 4 ≤ h) {a : ℕ} (ha : a ∈ outerBlock x h) :
    h / 4 ≤ (fibreLen x h a : ℝ) := by
  rw [mem_outerBlock] at ha
  obtain ⟨⟨hone, -⟩, hlow, hhigh⟩ := ha
  have hx0 : (0 : ℝ) < x := by linarith
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have ha0 : (0 : ℝ) < (a : ℝ) := by linarith
  set A : ℝ := (x + h * Real.sqrt x) / (a : ℝ) with hA
  set B : ℝ := x / (a : ℝ) with hB
  have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
  have hdiff : h / 2 ≤ A - B := by
    have hval : A - B = h * Real.sqrt x / (a : ℝ) := by
      rw [hA, hB]
      field_simp
      ring
    rw [hval, le_div_iff₀ ha0]
    nlinarith [hhigh, hs2, hh]
  have hfl : A - 1 < (⌊A⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one A
    linarith
  have hce : (⌈B⌉₊ : ℝ) < B + 1 := Nat.ceil_lt_add_one hB0
  have hce1 : 1 ≤ ⌈B⌉₊ := by
    refine Nat.one_le_ceil_iff.2 ?_
    rw [hB]
    positivity
  have hcast : ((⌈B⌉₊ - 1 : ℕ) : ℝ) = (⌈B⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hce1]
    norm_num
  have hgap : h / 4 < (⌊A⌋₊ : ℝ) - ((⌈B⌉₊ - 1 : ℕ) : ℝ) := by
    rw [hcast]
    have : h / 2 - 1 ≤ A - B - 1 := by linarith
    have h4 : h / 4 ≤ h / 2 - 1 := by linarith
    linarith
  have hle : ⌈B⌉₊ - 1 ≤ ⌊A⌋₊ := by
    by_contra hcon
    push Not at hcon
    have : ((⌊A⌋₊ : ℕ) : ℝ) ≤ ((⌈B⌉₊ - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcon.le
    linarith [hgap, hh]
  have hfin : (fibreLen x h a : ℝ) = (⌊A⌋₊ : ℝ) - ((⌈B⌉₊ - 1 : ℕ) : ℝ) := by
    rw [fibreLen, fibreStartIdx, Nat.cast_sub hle]
  rw [hfin]
  linarith

/-- **Step 1 at the fibre data, with the mean-square input supplied.**  The exceptional count is
`1024 ε √x / D²`, from the corpus's unconditional Möbius fibre mean square at window
`exp((log x)^{99/100})`. -/
theorem eventually_fibre_step_one {D : ℝ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ∀ Bad₂ : Finset ℕ,
        (∀ a ∈ outerBlock x (cardLength (99 / 100) x), a ∉ Bad₂ →
          (1 / 2) * D * (fibreLen x (cardLength (99 / 100) x) a : ℝ)
            ≤ ∑ b ∈ innerFibre x (cardLength (99 / 100) x) a,
                ((moebius b : ℤ) : ℝ) ^ 2) →
        ((outerBlock x (cardLength (99 / 100) x)).card : ℝ)
          ≤ (((outerBlock x (cardLength (99 / 100) x)).filter (fun a =>
              (3 / 16) * D * (fibreLen x (cardLength (99 / 100) x) a : ℝ)
                  ≤ (((Finset.Ioc (fibreStartIdx x a)
                      (fibreStartIdx x a + fibreLen x (cardLength (99 / 100) x) a)).filter
                      (fun n => moebius n = 1)).card : ℝ)
                ∧ (3 / 16) * D * (fibreLen x (cardLength (99 / 100) x) a : ℝ)
                  ≤ (((Finset.Ioc (fibreStartIdx x a)
                      (fibreStartIdx x a + fibreLen x (cardLength (99 / 100) x) a)).filter
                      (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
            + 1024 * ε * Real.sqrt x / D ^ 2 + (Bad₂.card : ℝ) := by
  have hms := averagedMeanSquare_moebius
  have hqt : ∀ᶠ x : ℝ in atTop,
      (∑ a ∈ outerBlock x (cardLength (99 / 100) x),
        (∑ b ∈ innerFibre x (cardLength (99 / 100) x) a, ((moebius b : ℤ) : ℝ)) ^ 2)
        / (cardLength (99 / 100) x ^ 2 * Real.sqrt x) < ε :=
    hms.eventually (gt_mem_nhds hε)
  have hlen : ∀ᶠ x : ℝ in atTop, 4 ≤ cardLength (99 / 100) x :=
    (tendsto_cardLength (by norm_num)).eventually_ge_atTop 4
  filter_upwards [hqt, hlen, eventually_ge_atTop (4 : ℝ)] with x hq hh4 hx4
  intro Bad₂ h2
  set h : ℝ := cardLength (99 / 100) x with hhdef
  have hh0 : (0 : ℝ) < h := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ) < h ^ 2 * Real.sqrt x := by positivity
  set V : ℝ := ε * (h ^ 2 * Real.sqrt x) with hVdef
  have hmsx : ∑ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ)) ^ 2 ≤ V := by
    rw [hVdef]
    rw [div_lt_iff₀ hden] at hq
    linarith
  set δ : ℝ := (1 / 32) * D * h with hδdef
  have hδ0 : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hδL : ∀ a ∈ outerBlock x h, δ ≤ (1 / 8) * D * (fibreLen x h a : ℝ) := by
    intro a ha
    have hge := fibreLen_ge hx4 hh4 ha
    rw [hδdef]
    nlinarith [hge, hD, hh0]
  have hbase := card_le_good_add_fibreMeanSquare (x := x) (h := h) hx4 hh0.le
    (Bad₂ := Bad₂) (D := D) (V := V) (δ := δ) hδ0 hδL hmsx h2
  refine le_trans hbase (le_of_le_of_eq (le_refl _) ?_)
  have hval : V / δ ^ 2 = 1024 * ε * Real.sqrt x / D ^ 2 := by
    rw [hVdef, hδdef]
    field_simp
    ring
  rw [hval]

end RHTower.Sieve
