import GaloisForLFunctions.RHTower.PrimeWeylSamplingIdealizerAnalytic
import GaloisForLFunctions.RHTower.XiRealDivisorSampling
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# Aperiodicity from progression-freeness, not from counting density

Theorem A of `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` uses superlinear counting
growth only to force `shiftFailure S h` to be infinite for every `h ≠ 0`.  That conclusion follows
from a strictly weaker hypothesis: it is enough that `S` be unbounded above and contain **no
infinite arithmetic progression**.

Indeed, if `shiftFailure S h` is finite it is bounded above by some `T₀`; picking any sample above
`T₀` and translating repeatedly by `h` produces a full one-sided progression inside `S`.  Symmetry
transports the statement from `h` to `-h`, so a single sign suffices.

For the real Xi divisor this replaces the card's counting input — the positive-proportion theorem
together with Riemann–von Mangoldt — by:

* **Hardy's theorem**, which this tree already owns (`RHTower.exists_Xi_zero_gt`), and
* **progression-freeness of the critical zeros** (Putnam 1954), a strictly weaker statement than a
  positive proportion of simple critical zeros.
-/

open Set

namespace RHTower

/-! ## Progressions inside an almost translation-invariant sample set -/

/-- If the shift failure at a positive step `h` is finite, the sample set contains a full one-sided
arithmetic progression of step `h`. -/
theorem exists_progression_of_finite_shiftFailure {S : Set ℝ} {h : ℝ} (hh : 0 < h)
    (hfin : (shiftFailure S h).Finite)
    (hunb : ∀ T : ℝ, ∃ γ, γ ∈ S ∧ T < γ) :
    ∃ a : ℝ, ∀ n : ℕ, a + (n : ℝ) * h ∈ S := by
  obtain ⟨T₀, hT₀⟩ := hfin.bddAbove
  obtain ⟨γ₀, hγ₀S, hγ₀⟩ := hunb T₀
  refine ⟨γ₀, ?_⟩
  intro n
  induction n with
  | zero => simpa using hγ₀S
  | succ n ih =>
      have hgt : T₀ < γ₀ + (n : ℝ) * h := by
        have : (0 : ℝ) ≤ (n : ℝ) * h := by positivity
        linarith
      have hnot : γ₀ + (n : ℝ) * h ∉ shiftFailure S h := by
        intro hmem
        exact absurd (hT₀ hmem) (not_le.mpr hgt)
      have hstep : γ₀ + (n : ℝ) * h + h ∈ S := by
        by_contra hcon
        exact hnot ⟨ih, hcon⟩
      have hcast : γ₀ + ((n + 1 : ℕ) : ℝ) * h = γ₀ + (n : ℝ) * h + h := by
        push_cast
        ring
      rw [hcast]
      exact hstep

/-- The shift failure of a symmetric sample set at `h` is the reflection of its failure at `-h`. -/
theorem shiftFailure_neg_eq {S : Set ℝ} (hsym : ∀ x, x ∈ S → -x ∈ S) (h : ℝ) :
    shiftFailure S h = (fun x => -x) '' shiftFailure S (-h) := by
  ext x
  simp only [shiftFailure, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hxS, hxh⟩
    refine ⟨-x, ⟨hsym x hxS, ?_⟩, by ring⟩
    intro hmem
    have hb := hsym (-x + -h) hmem
    rw [show -(-x + -h) = x + h by ring] at hb
    exact hxh hb
  · rintro ⟨y, ⟨hyS, hyh⟩, rfl⟩
    refine ⟨hsym y hyS, ?_⟩
    intro hmem
    have hb := hsym (-y + h) hmem
    rw [show -(-y + h) = y + -h by ring] at hb
    exact hyh hb

/-- **Aperiodicity from progression-freeness.**  A symmetric sample set that is unbounded above and
contains no infinite arithmetic progression has infinite shift failure at every nonzero step. -/
theorem infinite_shiftFailure_of_no_progression {S : Set ℝ}
    (hsym : ∀ x, x ∈ S → -x ∈ S)
    (hunb : ∀ T : ℝ, ∃ γ, γ ∈ S ∧ T < γ)
    (hnoAP : ∀ a h : ℝ, 0 < h → ∃ n : ℕ, a + (n : ℝ) * h ∉ S)
    {h : ℝ} (hh : h ≠ 0) : (shiftFailure S h).Infinite := by
  have hpos : ∀ k : ℝ, 0 < k → (shiftFailure S k).Infinite := by
    intro k hk
    rw [Set.Infinite]
    intro hfin
    obtain ⟨a, ha⟩ := exists_progression_of_finite_shiftFailure hk hfin hunb
    obtain ⟨n, hn⟩ := hnoAP a k hk
    exact hn (ha n)
  rcases lt_or_gt_of_ne hh with hneg | hposh
  · have hkey := hpos (-h) (by linarith)
    rw [shiftFailure_neg_eq hsym h]
    exact hkey.image (fun x _ y _ hxy => by simpa using neg_injective hxy)
  · exact hpos h hposh

/-- **Theorem A with the counting hypothesis replaced by progression-freeness.** -/
theorem samplingIdealizer_collapse_of_no_progression {m : ℕ} {S : Set ℝ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ}
    (hlf : LocallyFiniteSamples S) (hsym : ∀ x, x ∈ S → -x ∈ S)
    (hunb : ∀ T : ℝ, ∃ γ, γ ∈ S ∧ T < γ)
    (hnoAP : ∀ b k : ℝ, 0 < k → ∃ n : ℕ, b + (n : ℝ) * k ∉ S)
    (h0 : (0 : ℝ) ∈ F) (hpres : PreservesSamplingIdeal m S F a) :
    ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → a h j = 0 := by
  have hinf : S.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨T, hT⟩
    obtain ⟨γ, hγS, hγ⟩ := hunb T
    exact absurd (hT hγS) (not_le.mpr hγ)
  intro h hhF j hj hcase
  rcases eq_or_ne h 0 with rfl | hh
  · have hj0 : j ≠ 0 := hcase.resolve_left (by simp)
    exact derivCoeff_eq_zero_of_infinite_samples hlf hpres h0 hinf hj hj0
  · exact shiftCoeff_eq_zero_of_infinite_failure hlf hpres hhF
      (infinite_shiftFailure_of_no_progression hsym hunb hnoAP hh) hj

/-! ## The real Xi divisor is unbounded above -/

/-- Hardy's theorem, read on the real Xi divisor. -/
theorem unbounded_xiRealDivisor (T : ℝ) : ∃ γ, γ ∈ xiRealDivisor ∧ T < γ := by
  obtain ⟨t, hT, ht⟩ := exists_Xi_zero_gt T
  refine ⟨t, ?_, hT⟩
  rw [xiRealDivisor, Set.mem_setOf_eq, XiC_ofReal, ht]
  norm_num

/-- **`(23)` with Hardy's theorem in place of the counting input.**  The only remaining hypothesis
is that the critical zeros contain no infinite arithmetic progression. -/
theorem xiSamplingIdealizer_collapse_of_no_progression {m : ℕ} {F : Finset ℝ}
    {a : ℝ → ℕ → Polynomial ℂ}
    (hnoAP : ∀ b k : ℝ, 0 < k → ∃ n : ℕ, b + (n : ℝ) * k ∉ xiRealDivisor)
    (h0 : (0 : ℝ) ∈ F) (hpres : PreservesSamplingIdeal m xiRealDivisor F a) :
    ∀ h ∈ F, ∀ j ≤ m, (h ≠ 0 ∨ j ≠ 0) → a h j = 0 :=
  samplingIdealizer_collapse_of_no_progression locallyFiniteSamples_xiRealDivisor
    symmetric_xiRealDivisor unbounded_xiRealDivisor hnoAP h0 hpres

end RHTower
