import GaloisForLFunctions.RHTower.Sieve.FibreStepOne
import GaloisForLFunctions.RHTower.Sieve.FibreSquarefreeMass
import GaloisForLFunctions.RHTower.Sieve.FibreWindowTop
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDensityBound
import GaloisForLFunctions.RHTower.Sieve.CoprimeSignDensity

/-!
# Step 1 of the reciprocal-marker Hall law, with no hypotheses
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction

/-- The ceiling square root of the window top is below its floor. -/
theorem fibre_step_one_ceil_le {T : ℝ} (hT : 4 ≤ T) : ⌈Real.sqrt T⌉₊ ≤ ⌊T⌋₊ := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hs0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hs2 : (2 : ℝ) ≤ Real.sqrt T := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hT
  have hTsq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0
  have hhalf : Real.sqrt T ≤ T / 2 := by nlinarith [hs2, hTsq]
  have hceil : ((⌈Real.sqrt T⌉₊ : ℕ) : ℝ) ≤ T / 2 + 1 := by
    have := Nat.ceil_lt_add_one hs0
    linarith
  have hfloor : T - 1 < ((⌊T⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one T
    linarith
  have hcmp : ((⌈Real.sqrt T⌉₊ : ℕ) : ℝ) < ((⌊T⌋₊ : ℕ) : ℝ) + 1 := by
    have h1 : T / 2 + 1 ≤ T - 1 := by linarith
    linarith
  have : ⌈Real.sqrt T⌉₊ < ⌊T⌋₊ + 1 := by exact_mod_cast hcmp
  omega

/-- **Step 1 of the Hall law, unconditionally.**  Most fibres above the outer block carry at least
`(3/16)·ϱ·(fibre length)` integers of each Möbius sign; the exceptional count is the sum of the
Möbius mean-square budget and the squarefree tail budget, both `o(√x)`. -/
theorem eventually_fibre_step_one_closed {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      ((outerBlock x (cardLength (99 / 100) x)).card : ℝ)
        ≤ (((outerBlock x (cardLength (99 / 100) x)).filter (fun a =>
            (3 / 16) * squarefreeDensity * (fibreLen x (cardLength (99 / 100) x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (cardLength (99 / 100) x) a)).filter
                    (fun n => moebius n = 1)).card : ℝ)
              ∧ (3 / 16) * squarefreeDensity * (fibreLen x (cardLength (99 / 100) x) a : ℝ)
                ≤ (((Finset.Ioc (fibreStartIdx x a)
                    (fibreStartIdx x a + fibreLen x (cardLength (99 / 100) x) a)).filter
                    (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
          + 1024 * ε * Real.sqrt x / squarefreeDensity ^ (2 : ℕ)
          + fibreTailBudget x (cardLength (99 / 100) x) 5000
              ⌈Real.sqrt (x + cardLength (99 / 100) x * Real.sqrt x)⌉₊
            / (cardLength (99 / 100) x / 100) := by
  classical
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hDge : (3 : ℝ) / 8 ≤ squarefreeDensity := squarefreeDensity_ge
  have hstep := eventually_fibre_step_one (D := squarefreeDensity) hD hε
  have hbig := (tendsto_cardLength (by norm_num : (0:ℝ) < 99 / 100)).eventually_ge_atTop
    (200000 : ℝ)
  filter_upwards [hstep, hbig, eventually_ge_atTop (4 : ℝ)] with x hx1 hh hx4
  set h : ℝ := cardLength (99 / 100) x with hhdef
  have hh0 : (0 : ℝ) ≤ h := by linarith
  have hh4 : (4 : ℝ) ≤ h := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  set T : ℝ := x + h * Real.sqrt x with hTdef
  have hT4 : (4 : ℝ) ≤ T := by
    rw [hTdef]
    nlinarith [hh0, hs0, hx4]
  set M' : ℕ := ⌈Real.sqrt T⌉₊ with hM'
  set M : ℕ := ⌊T⌋₊ with hM
  set θ : ℝ := h / 100 with hθdef
  have hθ0 : (0 : ℝ) < θ := by rw [hθdef]; linarith
  set Bad : Finset ℕ := (outerBlock x h).filter (fun a =>
      θ ≤ windowTail (fibreStartIdx x a) (fibreLen x h a) 5000 M') with hBad
  -- the squarefree mass outside the exceptional set
  have hgap : ∀ a ∈ outerBlock x h,
      (5000 : ℝ) + (fibreLen x h a : ℝ) / (5000 : ℝ) + θ
        ≤ (1 / 2) * squarefreeDensity * (fibreLen x h a : ℝ) := by
    intro a ha
    have hL := fibreLen_ge hx4 hh4 ha
    have hL0 : (0 : ℝ) ≤ (fibreLen x h a : ℝ) := Nat.cast_nonneg _
    have hprod : (3 / 8 : ℝ) * (fibreLen x h a : ℝ)
        ≤ squarefreeDensity * (fibreLen x h a : ℝ) :=
      mul_le_mul_of_nonneg_right hDge hL0
    rw [hθdef]
    linarith [hL, hprod, hh]
  have h2 : ∀ a ∈ outerBlock x h, a ∉ Bad →
      (1 / 2) * squarefreeDensity * (fibreLen x h a : ℝ)
        ≤ ∑ b ∈ innerFibre x h a, ((moebius b : ℤ) : ℝ) ^ (2 : ℕ) := by
    intro a ha hnot
    have htail : windowTail (fibreStartIdx x a) (fibreLen x h a) 5000 M' ≤ θ := by
      by_contra hcon
      exact hnot (by rw [hBad, Finset.mem_filter]; exact ⟨ha, (not_le.mp hcon).le⟩)
    exact fibre_squarefree_mass hx4 hh0 (by norm_num : 1 ≤ 5000)
      (fun b hb => fibre_top_le_floor hx4 hh0 hb)
      (fibre_step_one_ceil_le hT4)
      (fun b hb => fibre_top_lt_sq hx4 hh0 hb) hgap a ha htail
  -- the exceptional count
  have hcard : ((Bad.card : ℕ) : ℝ) ≤ fibreTailBudget x h 5000 M' / θ := by
    rw [hBad]
    refine card_fibre_bad_le hx4 hh0 (by norm_num : 1 ≤ 5000) ?_ ?_ hθ0
    · refine Nat.one_le_ceil_iff.2 ?_
      positivity
    · have : ⌈Real.sqrt x / 2⌉₊ ≤ ⌈Real.sqrt x⌉₊ := by
        refine Nat.ceil_mono ?_
        linarith [hs0]
      omega
  have hmain := hx1 Bad h2
  have hθval : θ = h / 100 := hθdef
  linarith [hmain, hcard]

end RHTower.Sieve
