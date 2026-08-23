import GaloisForLFunctions.RHTower.ZetaDivPowRepresentative
import GaloisForLFunctions.RHTower.HeadTailMellinAnalytic
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyCongr
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyMul

/-!
# The analytic representative of `G(s)/(s-ρ)^k`

Dividing a meromorphic function by a power of a linear factor produces junk values at `ρ`; the
honest object is the meromorphic normal form, which agrees with the quotient away from `ρ` and is
analytic there as soon as `G` vanishes to order at least `k`.

Because Hardy membership sees only the open right half-plane, the anonymous quotient produced by
`exists_isHalfPlaneHardy_div_pow` can be replaced by this concrete representative — which, unlike
the anonymous one, can be divided again.

## Main results

* `divPowNF`, `divPowNF_eq`, `analyticAt_divPowNF`
* `meromorphicOrderAt_divPowNF_self`
* `exists_isHalfPlaneHardy_divPowNF`
-/

open Complex Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The naive quotient by a power of a linear factor. -/
def divPow (G : ℂ → ℂ) (ρ : ℂ) (k : ℕ) : ℂ → ℂ := fun s => G s / (s - ρ) ^ k

theorem divPow_eq_div (G : ℂ → ℂ) (ρ : ℂ) (k : ℕ) :
    divPow G ρ k = G / fun z : ℂ => (z - ρ) ^ k := by
  funext z
  rw [divPow, Pi.div_apply]

theorem meromorphicAt_divPow {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ : ℂ) (k : ℕ)
    (s : ℂ) : MeromorphicAt (divPow G ρ k) s := by
  rw [divPow_eq_div]
  exact (hG s).div (analyticAt_sub_const_pow ρ k s).meromorphicAt

theorem analyticAt_divPow_of_ne {G : ℂ → ℂ} {ρ s : ℂ} {k : ℕ} (hG : AnalyticAt ℂ G s)
    (hsρ : s ≠ ρ) : AnalyticAt ℂ (divPow G ρ k) s :=
  hG.div (analyticAt_sub_const_pow ρ k s) (pow_ne_zero _ (sub_ne_zero.2 hsρ))

/-- The analytic representative of `G(s)/(s-ρ)^k`. -/
def divPowNF (G : ℂ → ℂ) (ρ : ℂ) (k : ℕ) : ℂ → ℂ := toMeromorphicNFOn (divPow G ρ k) Set.univ

theorem meromorphicOn_divPow {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ : ℂ) (k : ℕ) :
    MeromorphicOn (divPow G ρ k) Set.univ := fun z _ => meromorphicAt_divPow hG ρ k z

theorem meromorphicOrderAt_divPowNF {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ : ℂ) (k : ℕ)
    (z : ℂ) :
    meromorphicOrderAt (divPowNF G ρ k) z = meromorphicOrderAt (divPow G ρ k) z :=
  meromorphicOrderAt_congr
    ((meromorphicOn_divPow hG ρ k).toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z))

theorem divPowNF_eq_of_analyticAt {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ z : ℂ} {k : ℕ}
    (h : AnalyticAt ℂ (divPow G ρ k) z) : divPowNF G ρ k z = divPow G ρ k z := by
  have hmero := meromorphicOn_divPow hG ρ k
  simp [divPowNF, toMeromorphicNFOn, hmero,
    ← (toMeromorphicNFAt_eq_self.2 h.meromorphicNFAt).symm]

/-- **Off `ρ` the representative is the honest quotient.** -/
theorem divPowNF_eq {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ s : ℂ} {k : ℕ}
    (hana : AnalyticAt ℂ G s) (hsρ : s ≠ ρ) : divPowNF G ρ k s = G s / (s - ρ) ^ k :=
  divPowNF_eq_of_analyticAt hG (analyticAt_divPow_of_ne hana hsρ)

theorem meromorphicOrderAt_divPow_eq {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ : ℂ) (k : ℕ)
    (z : ℂ) :
    meromorphicOrderAt (divPow G ρ k) z
      = meromorphicOrderAt G z - meromorphicOrderAt (fun w : ℂ => (w - ρ) ^ k) z := by
  rw [divPow_eq_div, meromorphicOrderAt_div (hG z) (analyticAt_sub_const_pow ρ k z).meromorphicAt]

/-- **The representative is analytic wherever `G` is, provided `G` vanishes to order `k` at `ρ`.** -/
theorem analyticAt_divPowNF {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ s : ℂ} {k : ℕ}
    (hana : AnalyticAt ℂ G s) (hρana : AnalyticAt ℂ G ρ)
    (hord : (k : ℕ∞) ≤ analyticOrderAt G ρ) :
    AnalyticAt ℂ (divPowNF G ρ k) s := by
  have hNF : MeromorphicNFAt (divPowNF G ρ k) s :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)
  refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
  rw [meromorphicOrderAt_divPowNF hG ρ k s, meromorphicOrderAt_divPow_eq hG ρ k s]
  by_cases hsρ : s = ρ
  · subst hsρ
    rw [meromorphicOrderAt_sub_pow]
    refine withTop_sub_nonneg_of_le ?_
    rw [hρana.meromorphicOrderAt_eq]
    induction hx : analyticOrderAt G s with
    | top => simp
    | coe n =>
        rw [hx] at hord
        have hn : (k : ℕ) ≤ n := by exact_mod_cast hord
        have : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        simpa using this
  · rw [meromorphicOrderAt_sub_pow_of_ne k hsρ, sub_zero]
    exact meromorphicOrderAt_nonneg_of_analyticAt hana

/-- **The order drops by exactly `k` at `ρ`.** -/
theorem meromorphicOrderAt_divPowNF_self {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ : ℂ)
    (k : ℕ) :
    meromorphicOrderAt (divPowNF G ρ k) ρ
      = meromorphicOrderAt G ρ - ((k : ℤ) : WithTop ℤ) := by
  rw [meromorphicOrderAt_divPowNF hG ρ k, meromorphicOrderAt_divPow_eq hG ρ k,
    meromorphicOrderAt_sub_pow]

theorem meromorphicOrderAt_divPowNF_of_ne {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ z : ℂ}
    (k : ℕ) (hzρ : z ≠ ρ) :
    meromorphicOrderAt (divPowNF G ρ k) z = meromorphicOrderAt G z := by
  rw [meromorphicOrderAt_divPowNF hG ρ k, meromorphicOrderAt_divPow_eq hG ρ k,
    meromorphicOrderAt_sub_pow_of_ne k hzρ, sub_zero]

/-- **The concrete representative is Hardy.**  It agrees on the half-plane with the anonymous
quotient produced by the division lemma. -/
theorem exists_isHalfPlaneHardy_divPowNF {G : ℂ → ℂ} {M : ℝ} (hHardy : IsHalfPlaneHardy G M)
    (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ : ℂ} {k : ℕ} (hρana : AnalyticAt ℂ G ρ)
    (hord : (k : ℕ∞) ≤ analyticOrderAt G ρ)
    (hGana : ∀ s : ℂ, 0 < s.re → AnalyticAt ℂ G s) :
    ∃ N : ℝ, IsHalfPlaneHardy (divPowNF G ρ k) N := by
  obtain ⟨H, N, hH, hHeq⟩ := exists_isHalfPlaneHardy_div_pow hHardy hρana hord
  refine ⟨N, hH.congr_right ?_⟩
  have hoff : ∀ w : ℂ, 0 < w.re → w ≠ ρ → H w = divPowNF G ρ k w := by
    intro w hw hwρ
    have hne : ((w : ℂ) - ρ) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hwρ)
    have hval := hHeq w hw hwρ
    rw [divPowNF_eq hG (hGana w hw) hwρ, ← hval]
    field_simp
  intro w hw
  by_cases hwρ : w = ρ
  · subst hwρ
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hcontH : ContinuousAt H w := (hH.holo.analyticAt (hopen.mem_nhds hw)).continuousAt
    have hcontD : ContinuousAt (divPowNF G w k) w :=
      (analyticAt_divPowNF hG (hGana w hw) hρana hord).continuousAt
    refine eq_of_eventuallyEq_punctured hcontH hcontD ?_
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (hopen.eventually_mem hw)] with z hz hz'
    exact hoff z hz' (by simpa using hz)
  · exact hoff w hw hwρ

end

end RHTower
