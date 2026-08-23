import GaloisForLFunctions.RHTower.ZetaZeroOrderReflection
import GaloisForLFunctions.RHTower.BurnolRectangleResidue
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The analytic representative of `ζ(s)/(s-ρ)^l`

At a zero `ρ` of `ζ` of order at least `l` the quotient `ζ(s)/(s-ρ)^l` has a removable singularity,
but the Lean expression still carries the junk value `0/0` there.  As for `burnolQuotientNF`, the
honest object is the meromorphic normal form; it agrees with the quotient wherever the latter is
already analytic and is analytic at every point of the open critical strip.

## Main results

* `zetaDivPow`, `zetaDivPowNF`
* `zetaDivPowNF_eq`, `analyticAt_zetaDivPowNF`
-/

namespace RHTower

open Complex Filter Topology

noncomputable section

/-- The naive quotient. -/
def zetaDivPow (ρ : ℂ) (l : ℕ) : ℂ → ℂ := fun s => riemannZeta s / (s - ρ) ^ l

theorem analyticAt_sub_pow (ρ : ℂ) (l : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (z - ρ) ^ l) s :=
  (analyticAt_id.sub analyticAt_const).pow l

theorem meromorphicAt_zetaDivPow (ρ : ℂ) (l : ℕ) (s : ℂ) :
    MeromorphicAt (zetaDivPow ρ l) s := by
  have h : zetaDivPow ρ l = riemannZeta / fun z : ℂ => (z - ρ) ^ l := by
    funext z
    rw [zetaDivPow, Pi.div_apply]
  rw [h]
  exact (meromorphicAt_riemannZeta_everywhere s).div (analyticAt_sub_pow ρ l s).meromorphicAt

theorem analyticAt_zetaDivPow_of_ne {ρ : ℂ} {l : ℕ} {s : ℂ} (hs1 : s ≠ 1) (hsρ : s ≠ ρ) :
    AnalyticAt ℂ (zetaDivPow ρ l) s := by
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs1)
  have hne : ((s : ℂ) - ρ) ^ l ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hsρ)
  exact hζ.div (analyticAt_sub_pow ρ l s) hne

theorem meromorphicOrderAt_sub_pow (ρ : ℂ) (l : ℕ) :
    meromorphicOrderAt (fun z : ℂ => (z - ρ) ^ l) ρ = ((l : ℤ) : WithTop ℤ) := by
  have hord : analyticOrderAt (fun z : ℂ => (z - ρ) ^ l) ρ = ((l : ℕ) : ℕ∞) := by
    refine ((analyticAt_sub_pow ρ l ρ).analyticOrderAt_eq_natCast).2
      ⟨fun _ : ℂ => (1 : ℂ), analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards with z
    simp
  rw [(analyticAt_sub_pow ρ l ρ).meromorphicOrderAt_eq, hord]
  simp

theorem meromorphicOrderAt_sub_pow_of_ne {ρ : ℂ} (l : ℕ) {s : ℂ} (hsρ : s ≠ ρ) :
    meromorphicOrderAt (fun z : ℂ => (z - ρ) ^ l) s = (0 : WithTop ℤ) := by
  have hne : ((s : ℂ) - ρ) ^ l ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hsρ)
  rw [(analyticAt_sub_pow ρ l s).meromorphicOrderAt_eq,
    (analyticAt_sub_pow ρ l s).analyticOrderAt_eq_zero.2 hne]
  simp

theorem le_meromorphicOrderAt_of_le_analyticOrderAt {f : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (h : AnalyticAt ℂ f z) (hn : (n : ℕ∞) ≤ analyticOrderAt f z) :
    ((n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z := by
  rw [h.meromorphicOrderAt_eq]
  induction hx : analyticOrderAt f z with
  | top => simp
  | coe m =>
      rw [hx] at hn
      have hm : n ≤ m := by exact_mod_cast hn
      simp only [ENat.map_coe]
      exact_mod_cast hm

theorem zero_le_meromorphicOrderAt_zetaDivPow {ρ : ℂ} {l : ℕ} (hρ1 : ρ ≠ 1)
    (hord : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) {s : ℂ} (hs1 : s ≠ 1) :
    (0 : WithTop ℤ) ≤ meromorphicOrderAt (zetaDivPow ρ l) s := by
  have hfun : zetaDivPow ρ l = riemannZeta / fun z : ℂ => (z - ρ) ^ l := by
    funext z
    rw [zetaDivPow, Pi.div_apply]
  have hζ : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hs1)
  rw [hfun, meromorphicOrderAt_div hζ.meromorphicAt (analyticAt_sub_pow ρ l s).meromorphicAt]
  by_cases hsρ : s = ρ
  · subst hsρ
    rw [meromorphicOrderAt_sub_pow]
    have hle : ((l : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt riemannZeta s :=
      le_meromorphicOrderAt_of_le_analyticOrderAt hζ hord
    exact withTop_sub_nonneg_of_le hle
  · rw [meromorphicOrderAt_sub_pow_of_ne l hsρ, sub_zero]
    exact meromorphicOrderAt_nonneg_of_analyticAt hζ

/-- The analytic representative of `ζ(s)/(s-ρ)^l`. -/
def zetaDivPowNF (ρ : ℂ) (l : ℕ) : ℂ → ℂ := toMeromorphicNFOn (zetaDivPow ρ l) Set.univ

theorem meromorphicOn_zetaDivPow (ρ : ℂ) (l : ℕ) :
    MeromorphicOn (zetaDivPow ρ l) Set.univ := fun z _ => meromorphicAt_zetaDivPow ρ l z

theorem zetaDivPowNF_eventuallyEq (ρ : ℂ) (l : ℕ) (z : ℂ) :
    zetaDivPowNF ρ l =ᶠ[𝓝[≠] z] zetaDivPow ρ l :=
  (meromorphicOn_zetaDivPow ρ l).toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)

theorem meromorphicOrderAt_zetaDivPowNF (ρ : ℂ) (l : ℕ) (z : ℂ) :
    meromorphicOrderAt (zetaDivPowNF ρ l) z = meromorphicOrderAt (zetaDivPow ρ l) z :=
  meromorphicOrderAt_congr (zetaDivPowNF_eventuallyEq ρ l z)

theorem zetaDivPowNF_eq_of_analyticAt {ρ : ℂ} {l : ℕ} {z : ℂ}
    (h : AnalyticAt ℂ (zetaDivPow ρ l) z) : zetaDivPowNF ρ l z = zetaDivPow ρ l z := by
  have hmero := meromorphicOn_zetaDivPow ρ l
  simp [zetaDivPowNF, toMeromorphicNFOn, hmero,
    ← (toMeromorphicNFAt_eq_self.2 h.meromorphicNFAt).symm]

/-- **Off `1` and off `ρ` the representative is the honest quotient.** -/
theorem zetaDivPowNF_eq {ρ : ℂ} {l : ℕ} {s : ℂ} (hs1 : s ≠ 1) (hsρ : s ≠ ρ) :
    zetaDivPowNF ρ l s = riemannZeta s / (s - ρ) ^ l :=
  zetaDivPowNF_eq_of_analyticAt (analyticAt_zetaDivPow_of_ne hs1 hsρ)

/-- **The representative is analytic away from `s = 1`.** -/
theorem analyticAt_zetaDivPowNF {ρ : ℂ} {l : ℕ} (hρ1 : ρ ≠ 1)
    (hord : (l : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (zetaDivPowNF ρ l) s := by
  have hNF : MeromorphicNFAt (zetaDivPowNF ρ l) s :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)
  refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
  rw [meromorphicOrderAt_zetaDivPowNF ρ l s]
  exact zero_le_meromorphicOrderAt_zetaDivPow hρ1 hord hs1

end

end RHTower
