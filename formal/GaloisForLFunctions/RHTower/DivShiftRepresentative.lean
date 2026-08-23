import GaloisForLFunctions.RHTower.BurnolRectangleResidue
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The analytic representative of `G(s)/(s-ρ)`

Dividing an analytic function by a simple zero leaves a removable singularity carrying the Lean
junk value `0/0`.  As for `zetaDivPowNF`, the honest object is the meromorphic normal form of the
quotient; it agrees with the naive quotient wherever the latter is already analytic, and it is
analytic at `ρ` as soon as `G` vanishes there.

## Main results

* `divShift`, `divShiftNF`
* `divShiftNF_eq`, `analyticAt_divShiftNF`
-/

namespace RHTower

open Complex Filter Topology

noncomputable section

/-- The naive quotient by a simple linear factor. -/
def divShift (G : ℂ → ℂ) (ρ : ℂ) : ℂ → ℂ := fun s => G s / (s - ρ)

theorem analyticAt_sub_const (ρ : ℂ) (s : ℂ) : AnalyticAt ℂ (fun z : ℂ => z - ρ) s :=
  analyticAt_id.sub analyticAt_const

theorem meromorphicAt_divShift {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ : ℂ) (s : ℂ) :
    MeromorphicAt (divShift G ρ) s := by
  have h : divShift G ρ = G / fun z : ℂ => z - ρ := by
    funext z
    rw [divShift, Pi.div_apply]
  rw [h]
  exact (hG s).div (analyticAt_sub_const ρ s).meromorphicAt

theorem analyticAt_divShift_of_ne {G : ℂ → ℂ} {ρ s : ℂ} (hG : AnalyticAt ℂ G s) (hsρ : s ≠ ρ) :
    AnalyticAt ℂ (divShift G ρ) s :=
  hG.div (analyticAt_sub_const ρ s) (sub_ne_zero.2 hsρ)

theorem meromorphicOrderAt_sub_const_self (ρ : ℂ) :
    meromorphicOrderAt (fun z : ℂ => z - ρ) ρ = ((1 : ℤ) : WithTop ℤ) := by
  have hord : analyticOrderAt (fun z : ℂ => z - ρ) ρ = ((1 : ℕ) : ℕ∞) := by
    refine ((analyticAt_sub_const ρ ρ).analyticOrderAt_eq_natCast).2
      ⟨fun _ : ℂ => (1 : ℂ), analyticAt_const, one_ne_zero, ?_⟩
    filter_upwards with z
    simp
  rw [(analyticAt_sub_const ρ ρ).meromorphicOrderAt_eq, hord]
  simp

theorem meromorphicOrderAt_sub_const_of_ne {ρ s : ℂ} (hsρ : s ≠ ρ) :
    meromorphicOrderAt (fun z : ℂ => z - ρ) s = (0 : WithTop ℤ) := by
  rw [(analyticAt_sub_const ρ s).meromorphicOrderAt_eq,
    (analyticAt_sub_const ρ s).analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hsρ)]
  simp

/-- The analytic representative of `G(s)/(s-ρ)`. -/
def divShiftNF (G : ℂ → ℂ) (ρ : ℂ) : ℂ → ℂ := toMeromorphicNFOn (divShift G ρ) Set.univ

theorem meromorphicOn_divShift {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ : ℂ) :
    MeromorphicOn (divShift G ρ) Set.univ := fun z _ => meromorphicAt_divShift hG ρ z

theorem meromorphicOrderAt_divShiftNF {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) (ρ z : ℂ) :
    meromorphicOrderAt (divShiftNF G ρ) z = meromorphicOrderAt (divShift G ρ) z :=
  meromorphicOrderAt_congr
    ((meromorphicOn_divShift hG ρ).toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z))

theorem divShiftNF_eq_of_analyticAt {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ z : ℂ}
    (h : AnalyticAt ℂ (divShift G ρ) z) : divShiftNF G ρ z = divShift G ρ z := by
  have hmero := meromorphicOn_divShift hG ρ
  simp [divShiftNF, toMeromorphicNFOn, hmero,
    ← (toMeromorphicNFAt_eq_self.2 h.meromorphicNFAt).symm]

/-- **Off `ρ` the representative is the honest quotient.** -/
theorem divShiftNF_eq {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ s : ℂ}
    (hana : AnalyticAt ℂ G s) (hsρ : s ≠ ρ) : divShiftNF G ρ s = G s / (s - ρ) :=
  divShiftNF_eq_of_analyticAt hG (analyticAt_divShift_of_ne hana hsρ)

/-- **The representative is analytic at every point where `G` is analytic and, at `ρ`, vanishes.** -/
theorem analyticAt_divShiftNF {G : ℂ → ℂ} (hG : ∀ s : ℂ, MeromorphicAt G s) {ρ s : ℂ}
    (hana : AnalyticAt ℂ G s) (hρana : AnalyticAt ℂ G ρ) (hvan : G ρ = 0) :
    AnalyticAt ℂ (divShiftNF G ρ) s := by
  have hNF : MeromorphicNFAt (divShiftNF G ρ) s :=
    meromorphicNFOn_toMeromorphicNFOn _ _ (Set.mem_univ s)
  refine hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
  rw [meromorphicOrderAt_divShiftNF hG ρ s]
  have hfun : divShift G ρ = G / fun z : ℂ => z - ρ := by
    funext z
    rw [divShift, Pi.div_apply]
  rw [hfun, meromorphicOrderAt_div (hG s) (analyticAt_sub_const ρ s).meromorphicAt]
  by_cases hsρ : s = ρ
  · subst hsρ
    rw [meromorphicOrderAt_sub_const_self]
    refine withTop_sub_nonneg_of_le ?_
    exact one_le_meromorphicOrderAt_of_eq_zero hρana hvan
  · rw [meromorphicOrderAt_sub_const_of_ne hsρ, sub_zero]
    exact meromorphicOrderAt_nonneg_of_analyticAt hana

end

end RHTower
