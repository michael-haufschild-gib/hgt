import GaloisForLFunctions.RHTower.ZetaHardyQuotientPow
import GaloisForLFunctions.RHTower.MellinHardyClasses

/-!
# Burnol's Proposition 4.2

`ζ(s)/(s-ρ)^l` lies in `L̂₁ = s/(s-1)·H²` whenever `ρ` is a zero of `ζ` of order at least `l ≥ 1`.

The corpus owns the Hardy function `zetaHardyCore w = (s-1)ζ(s)/s²` (`s = w + 1/2`).  The
renormalised transform of `ζ(s)/(s-ρ)^l` is `(w+1/2)·zetaHardyCore(w)/(w-w₀)^l` with `w₀ = ρ - 1/2`,
and multiplying a Hardy function by `w + 1/2` is not allowed.  The fix is the splitting
`w + 1/2 = (w - w₀) + (w₀ + 1/2)`, which rewrites the target as

`zetaHardyCore/(w-w₀)^{l-1}  +  (w₀+1/2)·zetaHardyCore/(w-w₀)^l`,

two divisions of one Hardy function by powers of one of its own zeros.  When `ρ` lies strictly right
of the critical line the corpus's `exists_isHalfPlaneHardy_div_pow` applies at the interior point
`w₀`; otherwise `w₀` is on or beyond the boundary, the quotient is holomorphic on the half-plane to
begin with, and `isHalfPlaneHardy_of_div_pow_bounded` needs only the local bound coming from the
analytic factor of `ζ` at `ρ`.

## Main results

* `exists_isHalfPlaneHardy_zetaCore_div` — dividing `zetaHardyCore` by a zeta zero
* `isMellinHeadHardy_zetaQuotient` — **Burnol's Proposition 4.2**
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The analytic factor of `zetaHardyCore` at a zeta zero, in the half-plane variable. -/
def zetaCoreFactor (g : ℂ → ℂ) (w : ℂ) : ℂ := (w - 1 / 2) * g (w + 1 / 2) / (w + 1 / 2) ^ 2

theorem analyticAt_zetaCoreFactor {ρ : ℂ} (hρ0 : ρ ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g ρ) : AnalyticAt ℂ (zetaCoreFactor g) (ρ - 1 / 2) := by
  have hval : ((ρ : ℂ) - 1 / 2) + 1 / 2 = ρ := by ring
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) (ρ - 1 / 2) :=
    analyticAt_id.add analyticAt_const
  have hg' : AnalyticAt ℂ g (((ρ : ℂ) - 1 / 2) + 1 / 2) := by rw [hval]; exact hg
  have hcomp : AnalyticAt ℂ (fun w : ℂ => g (w + 1 / 2)) (ρ - 1 / 2) := by
    have hc := AnalyticAt.comp (g := g) (f := fun w : ℂ => w + 1 / 2)
      (x := (ρ : ℂ) - 1 / 2) hg' hshift
    exact hc
  have hdenne : (((ρ : ℂ) - 1 / 2) + 1 / 2) ^ 2 ≠ 0 := by
    rw [hval]; exact pow_ne_zero _ hρ0
  exact ((analyticAt_id.sub analyticAt_const).mul hcomp).div (hshift.pow 2) hdenne

/-- Near a zero of order at least `k`, `zetaHardyCore` factors through `(w - w₀)^k`. -/
theorem eventually_zetaHardyCore_factor {ρ : ℂ} {k : ℕ} {g : ℂ → ℂ}
    (hgfac : ∀ᶠ z : ℂ in 𝓝 ρ, riemannZeta z = (z - ρ) ^ k • g z) :
    ∀ᶠ w : ℂ in 𝓝 (ρ - 1 / 2), 0 < w.re → w ≠ 1 / 2 →
      zetaHardyCore w = (w - (ρ - 1 / 2)) ^ k * zetaCoreFactor g w := by
  have hval : ((ρ : ℂ) - 1 / 2) + 1 / 2 = ρ := by ring
  have hshift : Filter.Tendsto (fun w : ℂ => w + 1 / 2) (𝓝 (ρ - 1 / 2)) (𝓝 ρ) := by
    have hc : ContinuousAt (fun w : ℂ => w + 1 / 2) (ρ - 1 / 2) :=
      (continuous_id.add continuous_const).continuousAt
    rw [ContinuousAt, hval] at hc
    exact hc
  filter_upwards [hshift.eventually hgfac] with w hw hre hne
  rw [zetaHardyCore_eq hre hne, hw, zetaCoreFactor, smul_eq_mul]
  have hsub : (w + 1 / 2 - ρ) = w - (ρ - 1 / 2) := by ring
  have hs : (w + 1 / 2 - 1) = w - 1 / 2 := by ring
  rw [hsub, hs]
  have hden : (w + 1 / 2) ^ 2 ≠ 0 := by
    refine pow_ne_zero _ ?_
    exact halfShift_ne_zero hre
  field_simp

/-- **Dividing the Hardy core by a zeta zero.** -/
theorem exists_isHalfPlaneHardy_zetaCore_div {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) {k : ℕ}
    (hord : (k : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ (H : ℂ → ℂ) (N : ℝ), IsHalfPlaneHardy H N ∧
      ∀ w : ℂ, 0 < w.re → w ≠ ρ - 1 / 2 →
        H w * (w - (ρ - 1 / 2)) ^ k = zetaHardyCore w := by
  have hζan : AnalyticAt ℂ riemannZeta ρ := by
    have hopen1 : IsOpen ({(1 : ℂ)}ᶜ : Set ℂ) := isOpen_compl_singleton
    have hdiff : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := fun z hz =>
      (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
    exact hdiff.analyticAt (hopen1.mem_nhds (by simpa using hρ1))
  obtain ⟨g, hgan, hgfac⟩ := (natCast_le_analyticOrderAt hζan).1 hord
  obtain ⟨M, hM⟩ := isHalfPlaneHardy_zetaHardyCore
  have hw₀ne : (ρ : ℂ) - 1 / 2 ≠ 1 / 2 := by
    intro h
    exact hρ1 (by linear_combination h)
  have hfac := eventually_zetaHardyCore_factor hgfac (ρ := ρ) (k := k) (g := g)
  have hFan : AnalyticAt ℂ (zetaCoreFactor g) (ρ - 1 / 2) := analyticAt_zetaCoreFactor hρ0 hgan
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hnehalf : ∀ᶠ w : ℂ in 𝓝 ((ρ : ℂ) - 1 / 2), w ≠ 1 / 2 :=
    isOpen_ne.mem_nhds hw₀ne
  by_cases hint : 0 < ((ρ : ℂ) - 1 / 2).re
  · have hcoreAn : AnalyticAt ℂ zetaHardyCore (ρ - 1 / 2) :=
      hM.holo.analyticAt (hopen.mem_nhds hint)
    have hord' : (k : ℕ∞) ≤ analyticOrderAt zetaHardyCore (ρ - 1 / 2) := by
      refine (natCast_le_analyticOrderAt hcoreAn).2 ⟨zetaCoreFactor g, hFan, ?_⟩
      filter_upwards [hfac, hopen.mem_nhds hint, hnehalf] with w hw hre hne
      rw [hw hre hne, smul_eq_mul]
    obtain ⟨H, N, hH, hHeq⟩ := exists_isHalfPlaneHardy_div_pow hM hcoreAn hord'
    exact ⟨H, N, hH, hHeq⟩
  · have hne : ∀ w : ℂ, 0 < w.re → w - ((ρ : ℂ) - 1 / 2) ≠ 0 := by
      intro w hw h
      have hwe : w = (ρ : ℂ) - 1 / 2 := by linear_combination h
      rw [hwe] at hw
      exact hint hw
    set H : ℂ → ℂ := fun w => zetaHardyCore w / (w - ((ρ : ℂ) - 1 / 2)) ^ k with hHdef
    have hHdiff : DifferentiableOn ℂ H {w : ℂ | 0 < w.re} := by
      refine hM.holo.div ?_ (fun w hw => pow_ne_zero _ (hne w hw))
      exact ((differentiable_id.sub_const _).pow k).differentiableOn
    have hcont : ContinuousAt (zetaCoreFactor g) (ρ - 1 / 2) := hFan.continuousAt
    have hbd : ∀ᶠ w : ℂ in 𝓝 ((ρ : ℂ) - 1 / 2),
        ‖zetaCoreFactor g w‖ ≤ ‖zetaCoreFactor g ((ρ : ℂ) - 1 / 2)‖ + 1 := by
      have h := hcont.norm
      exact (h.eventually (gt_mem_nhds (by linarith :
        ‖zetaCoreFactor g ((ρ : ℂ) - 1 / 2)‖ < ‖zetaCoreFactor g ((ρ : ℂ) - 1 / 2)‖ + 1))).mono
        fun w hw => le_of_lt hw
    obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 (hfac.and (hbd.and hnehalf))
    have heq : ∀ w : ℂ, 0 < w.re → w ≠ (ρ : ℂ) - 1 / 2 →
        H w * (w - ((ρ : ℂ) - 1 / 2)) ^ k = zetaHardyCore w := by
      intro w hw _
      rw [hHdef]
      simp only
      exact div_mul_cancel₀ _ (pow_ne_zero _ (hne w hw))
    have hbound : ∀ w : ℂ, 0 < w.re → ‖w - ((ρ : ℂ) - 1 / 2)‖ < δ →
        ‖H w‖ ≤ ‖zetaCoreFactor g ((ρ : ℂ) - 1 / 2)‖ + 1 := by
      intro w hw hball
      obtain ⟨hf, hb, hnh⟩ := hδ (by simpa [dist_eq_norm] using hball)
      rw [hHdef]
      simp only
      rw [hf hw hnh, mul_comm, mul_div_assoc, div_self (pow_ne_zero _ (hne w hw)), mul_one]
      exact hb
    obtain ⟨N, hN⟩ := isHalfPlaneHardy_of_div_pow_bounded hM hHdiff
      (by positivity) hδ0 hbound heq
    exact ⟨H, N, hN, heq⟩

/-- Splitting `w + 1/2 = (w - w₀) + (w₀ + 1/2)` at the level of quotients. -/
theorem div_pow_split (Z c d : ℂ) (hd : d ≠ 0) (m : ℕ) :
    Z / d ^ m + c * (Z / d ^ (m + 1)) = Z * (d + c) / d ^ (m + 1) := by
  have hp : d ^ m ≠ 0 := pow_ne_zero _ hd
  field_simp
  ring

/-- **Burnol's Proposition 4.2.**  If `ρ` is a zero of `ζ` of order at least `l ≥ 1` then
`ζ(s)/(s-ρ)^l` lies in `L̂₁ = s/(s-1)·H²`. -/
theorem isMellinHeadHardy_zetaQuotient {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) {l : ℕ} (hl : 1 ≤ l)
    (hord : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    ∃ G : ℂ → ℂ, IsMellinHeadHardy 1 G ∧
      ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → s ≠ ρ → G s = riemannZeta s / (s - ρ) ^ l := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, l = m + 1 := ⟨l - 1, (Nat.succ_pred_eq_of_pos hl).symm⟩
  obtain ⟨Hb, Nb, hHb, hHbeq⟩ := exists_isHalfPlaneHardy_zetaCore_div hρ1 hρ0 hord
  have hordm : ((m : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ := by
    refine le_trans ?_ hord
    exact_mod_cast Nat.cast_le.2 (Nat.le_succ m)
  obtain ⟨Ha, Na, hHa, hHaeq⟩ := exists_isHalfPlaneHardy_zetaCore_div hρ1 hρ0 hordm
  set K : ℂ → ℂ := fun w => Ha w + ((ρ : ℂ) - 1 / 2 + 1 / 2) * Hb w with hKdef
  have hK : IsHalfPlaneHardy K (2 * Na + 2 * (‖(ρ : ℂ) - 1 / 2 + 1 / 2‖ ^ 2 * Nb)) :=
    isHalfPlaneHardy_add hHa (isHalfPlaneHardy_const_mul hHb _)
  have hKval : ∀ w : ℂ, 0 < w.re → w ≠ (ρ : ℂ) - 1 / 2 → w ≠ 1 / 2 →
      K w = zetaHardyCore w * (w + 1 / 2) / (w - ((ρ : ℂ) - 1 / 2)) ^ (m + 1) := by
    intro w hw hwne _
    have hne : w - ((ρ : ℂ) - 1 / 2) ≠ 0 := sub_ne_zero.2 hwne
    have ha := hHaeq w hw hwne
    have hb := hHbeq w hw hwne
    have hpa : (w - ((ρ : ℂ) - 1 / 2)) ^ m ≠ 0 := pow_ne_zero _ hne
    have hpb : (w - ((ρ : ℂ) - 1 / 2)) ^ (m + 1) ≠ 0 := pow_ne_zero _ hne
    have hAa : Ha w = zetaHardyCore w / (w - ((ρ : ℂ) - 1 / 2)) ^ m :=
      eq_div_of_mul_eq hpa ha
    have hBb : Hb w = zetaHardyCore w / (w - ((ρ : ℂ) - 1 / 2)) ^ (m + 1) :=
      eq_div_of_mul_eq hpb hb
    have hdρ : (w - ((ρ : ℂ) - 1 / 2)) + ρ = w + 1 / 2 := by ring
    rw [hKdef]
    simp only
    rw [hAa, hBb, show ((ρ : ℂ) - 1 / 2 + 1 / 2) = ρ from by ring,
      div_pow_split (zetaHardyCore w) ρ _ hne m, hdρ]
  refine ⟨fun s => s * K (s - 1 / 2) / (s - 1), ⟨K, _, hK, fun w hw hwne => ?_⟩, ?_⟩
  · have hs0 : w + 1 / 2 ≠ 0 := halfShift_ne_zero hw
    have hs1 : w + 1 / 2 - 1 ≠ 0 := by
      intro h
      exact hwne (by linear_combination h)
    have hsub : w + 1 / 2 - 1 / 2 = w := by ring
    have hhalf : (w : ℂ) - 1 / 2 ≠ 0 := by
      intro h
      exact hwne (by linear_combination h)
    have h2a : (w * 2 - 1 : ℂ) ≠ 0 := by
      intro h
      exact hwne (by linear_combination h / 2)
    have h2b : (w * 2 + 1 : ℂ) ≠ 0 := by
      intro h
      exact hs0 (by linear_combination h / 2)
    simp only
    rw [Complex.ofReal_one, Complex.one_cpow, one_mul, hsub,
      show (w + 1 / 2 - 1 : ℂ) = w - 1 / 2 from by ring]
    field_simp
  · intro s hs hs1 hsρ
    have hw : 0 < (s - 1 / 2).re := by
      rw [Complex.sub_re]
      have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
      rw [h2]
      linarith
    have hwne : s - 1 / 2 ≠ (ρ : ℂ) - 1 / 2 := by
      intro h
      exact hsρ (by linear_combination h)
    have hwhalf : s - 1 / 2 ≠ 1 / 2 := by
      intro h
      exact hs1 (by linear_combination h)
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    have hsone : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    have hρne : (s - 1 / 2) - ((ρ : ℂ) - 1 / 2) = s - ρ := by ring
    have hpow : (s - ρ) ^ (m + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hsρ)
    have hcore := zetaHardyCore_eq hw hwhalf
    have hsub : s - 1 / 2 + 1 / 2 = s := by ring
    rw [hsub] at hcore
    simp only
    rw [hKval (s - 1 / 2) hw hwne hwhalf, hρne, hcore, hsub]
    field_simp

end RHTower

end
