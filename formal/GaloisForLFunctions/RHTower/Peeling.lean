/-
# Kummer obstruction II — global peeling of a single zero

`exists_peel`: an analytic function on an open set factors globally through any one of its
points: if `analyticOrderAt f ρ = m` then `f = (· - ρ) ^ m * h` on `U` with `h` analytic on
all of `U`, `h ρ ≠ 0`, and `h` carrying the same vanishing orders as `f` at every other point
of `U`.  Local input is mathlib's `AnalyticAt.analyticOrderAt_eq_natCast`; globalisation is
explicit division away from `ρ` glued to the local cofactor at `ρ`.
-/
import GaloisForLFunctions.RHTower.KummerObstruction

namespace RHTower

open Complex Filter Set

/-- **Global peeling.**  If `f` is analytic on an open `U` and has finite vanishing order `m`
at `ρ ∈ U`, then `f = (· - ρ) ^ m * h` on `U` for an analytic `h` with `h ρ ≠ 0` whose orders
agree with those of `f` away from `ρ`. -/
theorem exists_peel {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    {ρ : ℂ} (hρ : ρ ∈ U) {m : ℕ} (hm : analyticOrderAt f ρ = m) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ h ρ ≠ 0 ∧ (∀ s ∈ U, f s = (s - ρ) ^ m * h s) ∧
      ∀ σ ∈ U, σ ≠ ρ → analyticOrderAt h σ = analyticOrderAt f σ := by
  classical
  obtain ⟨g, hgan, hg0, hgev⟩ := ((hf ρ hρ).analyticOrderAt_eq_natCast).mp hm
  set h : ℂ → ℂ := fun s => if s = ρ then g ρ else f s / (s - ρ) ^ m with hh
  have hev_g : h =ᶠ[nhds ρ] g := by
    filter_upwards [hgev] with z hzf
    by_cases hzρ : z = ρ
    · simp [hh, hzρ]
    · have hne : (z - ρ) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzρ)
      simp only [hh, if_neg hzρ, hzf, smul_eq_mul]
      exact mul_div_cancel_left₀ _ hne
  have hhρ : h ρ = g ρ := by simp [hh]
  have hhan : AnalyticOnNhd ℂ h U := by
    intro σ hσ
    by_cases hσρ : σ = ρ
    · subst hσρ
      exact hgan.congr hev_g.symm
    · have hne : (σ - ρ) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hσρ)
      have hdiv : AnalyticAt ℂ (f / fun z => (z - ρ) ^ m) σ :=
        (hf σ hσ).div ((analyticAt_id.sub analyticAt_const).pow m) hne
      refine hdiv.congr ?_
      filter_upwards [eventually_ne_nhds hσρ] with z hz
      simp [hh, if_neg hz]
  have hfact : ∀ s ∈ U, f s = (s - ρ) ^ m * h s := by
    intro s hsU
    by_cases hsρ : s = ρ
    · subst hsρ
      rw [hhρ, ← smul_eq_mul]
      exact hgev.self_of_nhds
    · have hne : (s - ρ) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hsρ)
      simp only [hh, if_neg hsρ]
      rw [mul_comm]
      exact (div_mul_cancel₀ _ hne).symm
  refine ⟨h, hhan, by rw [hhρ]; exact hg0, hfact, ?_⟩
  intro σ hσU hσρ
  have hfev : f =ᶠ[nhds σ] ((fun z => (z - ρ) ^ m) * h) := by
    filter_upwards [hU.mem_nhds hσU] with z hz
    exact hfact z hz
  have hpowσ : AnalyticAt ℂ (fun z => (z - ρ) ^ m) σ :=
    (analyticAt_id.sub analyticAt_const).pow m
  have hpow0 : analyticOrderAt (fun z => (z - ρ) ^ m) σ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (pow_ne_zero _ (sub_ne_zero.mpr hσρ)))
  rw [analyticOrderAt_congr hfev, analyticOrderAt_mul hpowσ (hhan σ hσU), hpow0, zero_add]

end RHTower

namespace RHTower

open Complex Filter Set

/-- **Global multi-peeling.**  An analytic function on an open set whose zeros
there all lie in a finite set `t` of finite vanishing orders factors globally
through `t` with a nonvanishing analytic cofactor: `f = ∏_{w ∈ t} (·−w)^{m w} · h`
with `h` analytic and zero-free on `U`.  Iterated single-zero peeling; the order
bookkeeping of `exists_peel` keeps the induction hypotheses alive. -/
theorem exists_multi_peel {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ U)
    (hzeros : ∀ z ∈ U, f z = 0 → z ∈ t)
    (hord : ∀ w ∈ t, analyticOrderAt f w ≠ ⊤) :
    ∃ (m : ℂ → ℕ) (h : ℂ → ℂ), AnalyticOnNhd ℂ h U ∧ (∀ z ∈ U, h z ≠ 0) ∧
      ∀ z ∈ U, f z = (∏ w ∈ t, (z - w) ^ m w) * h z := by
  classical
  revert f htU hzeros hord
  induction t using Finset.induction_on with
  | empty =>
      intro f hf _ hzeros _
      exact ⟨fun _ => 0, f, hf,
        fun z hz h0 => absurd (hzeros z hz h0) (Finset.notMem_empty z),
        fun z _ => by simp⟩
  | insert ρ s hρs ih =>
      intro f hf htU hzeros hord
      have hρU : ρ ∈ U := htU ρ (Finset.mem_insert_self ρ s)
      have hordρ : analyticOrderAt f ρ ≠ ⊤ := hord ρ (Finset.mem_insert_self ρ s)
      set mρ : ℕ := (analyticOrderAt f ρ).toNat with hmρ
      have hmcast : analyticOrderAt f ρ = (mρ : ℕ∞) := (ENat.coe_toNat hordρ).symm
      obtain ⟨h₁, hh₁an, hh₁ρ, hfact₁, hords₁⟩ := exists_peel hU hf hρU hmcast
      have hzeros₁ : ∀ z ∈ U, h₁ z = 0 → z ∈ s := by
        intro z hz h10
        by_cases hzρ : z = ρ
        · exact absurd (hzρ ▸ h10) hh₁ρ
        · have hf0 : f z = 0 := by rw [hfact₁ z hz, h10, mul_zero]
          rcases Finset.mem_insert.mp (hzeros z hz hf0) with h | h
          · exact absurd h hzρ
          · exact h
      have hord₁ : ∀ w ∈ s, analyticOrderAt h₁ w ≠ ⊤ := by
        intro w hw
        have hwρ : w ≠ ρ := fun h => hρs (h ▸ hw)
        rw [hords₁ w (htU w (Finset.mem_insert_of_mem hw)) hwρ]
        exact hord w (Finset.mem_insert_of_mem hw)
      obtain ⟨m', h', hh'an, hh'0, hfact'⟩ :=
        ih hh₁an (fun w hw => htU w (Finset.mem_insert_of_mem hw)) hzeros₁ hord₁
      refine ⟨fun w => if w = ρ then mρ else m' w, h', hh'an, hh'0, fun z hz => ?_⟩
      rw [Finset.prod_insert hρs]
      have hif : (if ρ = ρ then mρ else m' ρ) = mρ := if_pos rfl
      have hprods : (∏ w ∈ s, (z - w) ^ (if w = ρ then mρ else m' w))
          = ∏ w ∈ s, (z - w) ^ m' w :=
        Finset.prod_congr rfl fun w hw => by
          rw [if_neg (ne_of_mem_of_not_mem hw hρs)]
      rw [hif, hprods, hfact₁ z hz, hfact' z hz]
      ring

end RHTower
