import GaloisForLFunctions.RHTower.JointAncestryRouteCapstone
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# Off-line chains have doubly-logarithmic plateau records

Let the off-line zeros form a chain, so `δ(ρ) = |Re ρ − ½|` has no maximum.  Call a zero a *record*
if no zero of smaller or equal height is farther from the critical line.  **Theorem**
(`exists_plateau_record_of_chain`): for every `κ > 0`, `C > 1` and height `H₀ ≥ e^e` there is a
record `ρ` with `|Im ρ| ≥ H₀` such that every zero of height at most `|Im ρ|^C` satisfies

`δ(ρ') ≤ δ(ρ) + κ / log log |Im ρ|`.

So infinitely many records are plateaus at the doubly-logarithmic scale over polynomial height
ranges.

**Proof.**  Otherwise every record `r` is beaten by `κ / log log |Im r|` within height `|Im r|^C`.
The farthest zero of height `≤ |Im r|^C` is then a new record `r'`, and `log log |Im r'| ≤ log C +
log log |Im r|`.  Iterating from one record, the `j`-th record has `δ ≥ δ₀ + Σ_{i<j} κ/(L₀ + i log C)`.
This harmonic sum diverges, while `δ ≤ ½`.

The scale matters.  A slack `κ/(log γ)^θ` with `θ > 0` gives a convergent sum along polynomial height
steps, so no plateau statement follows at that scale.  For window tests on primes up to `N`, a
plateau with slack `s` controls the farther zeros exactly when `s · log N = O(1)`.  The present
records therefore serve windows of polylogarithmic length.
-/

open Real Filter

namespace RHTower

noncomputable section

/-- **Abstract plateau lemma.**  Let `d` be bounded with no maximum on a type in which every
sublevel set of `h` is finite.  Then for all `κ > 0`, `C > 1` there are records of arbitrarily large
height that no point of height `≤ h^C` beats by more than `κ / log log h`. -/
theorem exists_plateau_record {α : Type*} [Nonempty α] (h d : α → ℝ) {B : ℝ}
    (hB : ∀ a, d a ≤ B) (hfin : ∀ H : ℝ, {a | h a ≤ H}.Finite) (hnomax : ∀ a, ∃ b, d a < d b)
    {κ C : ℝ} (hκ : 0 < κ) (hC : 1 < C) {H₀ : ℝ} (hH₀ : Real.exp (Real.exp 1) ≤ H₀) :
    ∃ a, H₀ ≤ h a ∧ (∀ b, h b ≤ h a → d b ≤ d a) ∧
      ∀ b, h b ≤ h a ^ C → d b ≤ d a + κ / Real.log (Real.log (h a)) := by
  classical
  have hH₀1 : 1 < H₀ := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)) hH₀
  -- the farthest point below a height
  have hmax : ∀ H : ℝ, {a | h a ≤ H}.Nonempty →
      ∃ m, h m ≤ H ∧ ∀ b, h b ≤ H → d b ≤ d m := fun H hne => by
    obtain ⟨m, hm, hm'⟩ := Set.exists_max_image _ d (hfin H) hne
    exact ⟨m, hm, fun b hb => hm' b hb⟩
  -- a first record above `H₀`
  obtain ⟨a₀⟩ := ‹Nonempty α›
  obtain ⟨m₁, hm₁, hm₁'⟩ := hmax (max H₀ (h a₀)) ⟨a₀, show h a₀ ≤ max H₀ (h a₀) from le_max_right _ _⟩
  obtain ⟨b₁, hb₁⟩ := hnomax m₁
  obtain ⟨r₀, hr₀, hr₀'⟩ := hmax (h b₁) ⟨b₁, show h b₁ ≤ h b₁ from le_rfl⟩
  have hr₀H : H₀ ≤ h r₀ := by
    by_contra hlt
    push Not at hlt
    have := hm₁' r₀ (hlt.le.trans (le_max_left _ _))
    have := hr₀' b₁ le_rfl
    linarith
  have hr₀rec : ∀ b, h b ≤ h r₀ → d b ≤ d r₀ := fun b hb => hr₀' b (hb.trans hr₀)
  by_contra hne
  push Not at hne
  -- the successor record
  set L : α → ℝ := fun a => Real.log (Real.log (h a)) with hL
  have hL1 : ∀ a, H₀ ≤ h a → 1 ≤ L a := fun a ha => by
    have h1 : Real.exp 1 ≤ Real.log (h a) := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact hH₀.trans ha
    rw [hL]; simp only
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 1])]
    exact h1
  have hstep : ∀ a, H₀ ≤ h a → (∀ b, h b ≤ h a → d b ≤ d a) →
      ∃ a', H₀ ≤ h a' ∧ (∀ b, h b ≤ h a' → d b ≤ d a') ∧ d a + κ / L a < d a' ∧
        L a' ≤ Real.log C + L a := by
    intro a ha hrec
    obtain ⟨b, hb, hbd⟩ := hne a ha hrec
    have ha1 : 1 ≤ h a := by linarith
    obtain ⟨m, hm, hm'⟩ := hmax (h a ^ C) ⟨a, show h a ≤ h a ^ C from Real.self_le_rpow_of_one_le ha1 hC.le⟩
    have hdm : d a + κ / L a < d m := lt_of_lt_of_le hbd (hm' b hb)
    have hLa : 0 < L a := by linarith [hL1 a ha]
    have hma : h a < h m := by
      by_contra hle
      push Not at hle
      have := hrec m hle
      have : 0 < κ / L a := div_pos hκ hLa
      linarith
    refine ⟨m, ha.trans hma.le, fun c hc => hm' c (hc.trans hm), hdm, ?_⟩
    have hm0 : 0 < h m := by linarith
    have hlogm : 0 < Real.log (h m) := Real.log_pos (by linarith)
    have hloga : 0 < Real.log (h a) := Real.log_pos (by linarith)
    have h1 : Real.log (h m) ≤ C * Real.log (h a) := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log hm0 hm
    rw [hL]; simp only
    rw [← Real.log_mul (by linarith) hloga.ne']
    exact Real.log_le_log hlogm h1
  choose! next hnextH hnextrec hnextd hnextL using hstep
  -- iterate
  set c : ℝ := Real.log C with hc
  have hc0 : 0 < c := Real.log_pos hC
  set L₀ := L r₀ with hL₀
  have hL₀1 : 1 ≤ L₀ := hL1 r₀ hr₀H
  have key : ∀ j : ℕ, H₀ ≤ h (next^[j] r₀) ∧
      (∀ b, h b ≤ h (next^[j] r₀) → d b ≤ d (next^[j] r₀)) ∧
      L (next^[j] r₀) ≤ L₀ + j * c ∧
      d r₀ + κ / (L₀ + c) * ∑ i ∈ Finset.range j, 1 / ((i : ℝ) + 1) ≤ d (next^[j] r₀) := by
    intro j
    induction j with
    | zero => exact ⟨hr₀H, hr₀rec, by rw [hL₀]; simp, by simp⟩
    | succ j ih =>
      obtain ⟨ihH, ihrec, ihL, ihd⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨hnextH _ ihH ihrec, hnextrec _ ihH ihrec, ?_, ?_⟩
      · have := hnextL _ ihH ihrec
        push_cast
        linarith
      · have hd := hnextd _ ihH ihrec
        have hLj : 0 < L (next^[j] r₀) := by linarith [hL1 _ ihH]
        have hden : L (next^[j] r₀) ≤ (L₀ + c) * ((j : ℝ) + 1) := by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          nlinarith
        have hfrac : κ / ((L₀ + c) * ((j : ℝ) + 1)) ≤ κ / L (next^[j] r₀) :=
          div_le_div_of_nonneg_left hκ.le hLj hden
        rw [Finset.sum_range_succ, mul_add]
        have : κ / (L₀ + c) * (1 / ((j : ℝ) + 1)) = κ / ((L₀ + c) * ((j : ℝ) + 1)) := by
          field_simp
        linarith
  -- the harmonic sum diverges
  have hpos : 0 < κ / (L₀ + c) := div_pos hκ (by linarith)
  obtain ⟨j, hj⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_gt_atTop
    ((B - d r₀) / (κ / (L₀ + c)))).exists
  have h1 := (key j).2.2.2
  have h2 := hB (next^[j] r₀)
  rw [div_lt_iff₀ hpos] at hj
  nlinarith

/-- **Plateau records of an off-line chain.** -/
theorem exists_plateau_record_of_chain (hch : JasOffLineChain) {κ C : ℝ} (hκ : 0 < κ)
    (hC : 1 < C) {H₀ : ℝ} (hH₀ : Real.exp (Real.exp 1) ≤ H₀) :
    ∃ q : XiZeroCopy, H₀ ≤ |(q.1 : ℂ).im| ∧
      (∀ q' : XiZeroCopy, |(q'.1 : ℂ).im| ≤ |(q.1 : ℂ).im| →
        |(q'.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).re - 1 / 2|) ∧
      ∀ q' : XiZeroCopy, |(q'.1 : ℂ).im| ≤ |(q.1 : ℂ).im| ^ C →
        |(q'.1 : ℂ).re - 1 / 2| ≤ |(q.1 : ℂ).re - 1 / 2| + κ / Real.log (Real.log |(q.1 : ℂ).im|) := by
  obtain ⟨q₁, hq₁⟩ := hch.1
  haveI : Nonempty XiZeroCopy := ⟨q₁⟩
  refine exists_plateau_record (fun q : XiZeroCopy => |(q.1 : ℂ).im|)
    (fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) (B := 1 / 2) (fun q => ?_) (fun H => ?_)
    (fun q => ?_) hκ hC hH₀
  · have h := xi_divisor_support_re_mem_open_unit q.1
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  · rcases le_or_gt 0 H with hH | hH
    · exact (finite_xiZeroCopy_band 0 hH).subset fun q hq => by simpa using hq
    · exact Set.finite_empty.subset fun q hq => by
        simp only [Set.mem_setOf_eq] at hq; linarith [abs_nonneg ((q.1 : ℂ).im)]
  · by_cases hq : (q.1 : ℂ).re = 1 / 2
    · exact ⟨q₁, by simp only [hq, sub_self, abs_zero]; exact abs_pos.mpr (sub_ne_zero.mpr hq₁)⟩
    · exact hch.2 q hq

end

end RHTower
