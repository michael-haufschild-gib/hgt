import GaloisForLFunctions.RHTower.SoninStripEvaluator
import GaloisForLFunctions.RHTower.BurnolMinimalitySystem
import GaloisForLFunctions.RHTower.HeadTailMellinAnalytic
import GaloisForLFunctions.HTGeometry.ShiftedMonomialJet

/-!
# The biorthogonal functional of the quotient system

Fix a zero `ρ` of `ζ` in the open critical strip, of order `m`, and an index `1 ≤ l ≤ m`.  Writing
`ζ(s) = (s − ρ)^m·g(s)` with `g` analytic and nonvanishing near `ρ`, the multiplier `h = 1/g` turns
the continued Mellin transform of a vector whose transform is `ζ(s)/(s − ρ')^{l'}` into

`(s − ρ)^m / (s − ρ')^{l'}`,

which near `ρ` is the monomial `(s − ρ)^{m − l'}` when `ρ' = ρ`, and carries a flat factor of order
`m` when `ρ' ≠ ρ`.  Reading the `(m − l)`-th Taylor coefficient therefore returns `1` exactly on the
vector indexed by `(ρ, l)` and `0` on every other vector of the system: a biorthogonal partner,
bounded because it is a jet evaluator of a multiplied transform.

## Main results

* `exists_zetaLocalUnit`
* `exists_zetaJetFunctional`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem eventuallyEq_of_eventuallyEq_punctured {F H : ℂ → ℂ} {ρ : ℂ}
    (hF : ContinuousAt F ρ) (hH : ContinuousAt H ρ)
    (h : ∀ᶠ z in 𝓝[≠] ρ, F z = H z) : F =ᶠ[𝓝 ρ] H := by
  have hpt := eq_of_eventuallyEq_punctured hF hH h
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with z hz
  by_cases hzρ : z = ρ
  · rw [hzρ]; exact hpt
  · exact hz (by simpa using hzρ)

/-- **The local unit of `ζ` at a zero of order `m`.**  On a neighbourhood of `ρ` inside the strip
there is an analytic `h` with `ζ·h = (s − ρ)^m`. -/
theorem exists_zetaLocalUnit {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {m : ℕ}
    (hm : analyticOrderAt riemannZeta ρ = (m : ℕ∞)) :
    ∃ (U : Set ℂ) (h : ℂ → ℂ), IsOpen U ∧ ρ ∈ U ∧ U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1} ∧
      AnalyticOnNhd ℂ h U ∧ ∀ s ∈ U, riemannZeta s * h s = (s - ρ) ^ m := by
  have hρne : ρ ≠ 1 := by
    intro hc; rw [hc] at hρ1; simp at hρ1
  have hζ : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρne
  obtain ⟨g, hg, hg0, hgeq⟩ := hζ.analyticOrderAt_eq_natCast.1 hm
  have hev : ∀ᶠ z in 𝓝 ρ,
      ((AnalyticAt ℂ g z ∧ g z ≠ 0) ∧ riemannZeta z = (z - ρ) ^ m • g z) ∧
        z ∈ {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    refine ((hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hg0)).and hgeq).and ?_
    exact isOpen_criticalOpenStrip.eventually_mem ⟨hρ0, hρ1⟩
  obtain ⟨U, hUP, hUopen, hUmem⟩ := eventually_nhds_iff.1 hev
  refine ⟨U, fun s => (g s)⁻¹, hUopen, hUmem, fun s hs => (hUP s hs).2, ?_, ?_⟩
  · intro s hs
    have hinv : AnalyticAt ℂ (fun w : ℂ => (g w)⁻¹) s :=
      AnalyticAt.inv (hUP s hs).1.1.1 (hUP s hs).1.1.2
    exact hinv
  · intro s hs
    have hgs : g s ≠ 0 := (hUP s hs).1.1.2
    rw [(hUP s hs).1.2, smul_eq_mul, mul_assoc, mul_inv_cancel₀ hgs, mul_one]

/-- **The biorthogonal functional.**  For a zero `ρ` of order `m` and an index `1 ≤ l ≤ m` there is
a bounded functional on the even part of `L₁` returning `1` on a vector whose transform is
`ζ(s)/(s − ρ)^l` and `0` on a vector whose transform is `ζ(s)/(s − ρ')^{l'}` for any other pair. -/
theorem exists_zetaJetFunctional {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {m : ℕ}
    (hm : analyticOrderAt riemannZeta ρ = (m : ℕ∞)) {l : ℕ} (hl1 : 1 ≤ l) (hlm : l ≤ m) :
    ∃ Λ : soninEvenExtended 1 →L[ℂ] ℂ,
      ∀ (f : soninEvenExtended 1) (ρ' : ℂ) (l' : ℕ), 0 < ρ'.re → ρ'.re < 1 → 1 ≤ l' →
        ((l' : ℕ∞) ≤ analyticOrderAt riemannZeta ρ') →
        (∀ s : ℂ, 0 < s.re → s.re < 1 → soninEval 1 ((f : SoninL2)) s = zetaDivPowNF ρ' l' s) →
        (Λ f = if ρ' = ρ ∧ l' = l then 1 else 0) := by
  classical
  obtain ⟨U, h, hUopen, hUmem, hUsub, hUana, hUmul⟩ := exists_zetaLocalUnit hρ0 hρ1 hm
  obtain ⟨Λ₀, hΛ₀⟩ :=
    exists_soninEvaluatorJetMul (a := 1) one_pos hUopen hUsub hUana (m - l) hUmem
  have hfac : ((Nat.factorial (m - l) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (m - l)
  refine ⟨(((Nat.factorial (m - l) : ℕ) : ℂ))⁻¹ • Λ₀, ?_⟩
  intro f ρ' l' hρ'0 hρ'1 hl'1 hl'ord hf
  rw [smul_apply, smul_eq_mul, hΛ₀ f]
  -- the transform, multiplied, computed on the punctured neighbourhood
  have hbase : ∀ᶠ s in 𝓝 ρ, s ≠ ρ' →
      soninEval 1 ((f : SoninL2)) s * h s = (s - ρ) ^ m * ((s - ρ') ^ l')⁻¹ := by
    filter_upwards [hUopen.eventually_mem hUmem] with s hs hsρ'
    obtain ⟨hs0, hs1⟩ := hUsub hs
    have hs1' : s ≠ 1 := by
      intro hc; rw [hc] at hs1; simp at hs1
    rw [hf s hs0 hs1, zetaDivPowNF_eq hs1' hsρ', div_mul_eq_mul_div, mul_comm (riemannZeta s) (h s),
      ← mul_comm (riemannZeta s) (h s), hUmul s hs, div_eq_mul_inv]
  by_cases hρρ' : ρ' = ρ
  · -- same zero: the germ is a monomial
    subst hρρ'
    have hl'm : l' ≤ m := by
      have : ((l' : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := by rw [← hm]; exact hl'ord
      exact_mod_cast this
    have hcont : ContinuousAt (fun s : ℂ => soninEval 1 ((f : SoninL2)) s * h s) ρ' := by
      have h1 : AnalyticAt ℂ (soninEval 1 ((f : SoninL2))) ρ' :=
        soninEval_analyticAt one_pos f.property.1 f.property.2 hρ0 hρ1
      exact (h1.mul (hUana ρ' hUmem)).continuousAt
    have hcont2 : ContinuousAt (fun s : ℂ => (s - ρ') ^ (m - l')) ρ' := by
      fun_prop
    have hgerm : (fun s : ℂ => soninEval 1 ((f : SoninL2)) s * h s)
        =ᶠ[𝓝 ρ'] fun s : ℂ => (s - ρ') ^ (m - l') := by
      refine eventuallyEq_of_eventuallyEq_punctured hcont hcont2 ?_
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hbase] with s hs hsne
      have hsρ' : s ≠ ρ' := by simpa using hsne
      have hsub : s - ρ' ≠ 0 := sub_ne_zero.2 hsρ'
      rw [hs hsρ', pow_sub₀ _ hsub hl'm]
    rw [hgerm.iteratedDeriv_eq (m - l), iteratedDeriv_sub_const_pow ρ' (m - l) (m - l')]
    by_cases hll : l' = l
    · subst hll
      simp [hfac]
    · have hne : m - l ≠ m - l' := by omega
      simp [hne, hll]
  · -- a different zero: the germ carries a flat factor of order `m`
    have hW : AnalyticAt ℂ (fun s : ℂ => ((s - ρ') ^ l')⁻¹) ρ := by
      have hbase' : AnalyticAt ℂ (fun s : ℂ => (s - ρ') ^ l') ρ :=
        (analyticAt_id.sub analyticAt_const).pow l'
      have hne : ((ρ - ρ') ^ l' : ℂ) ≠ 0 :=
        pow_ne_zero _ (sub_ne_zero.2 fun hc => hρρ' hc.symm)
      exact AnalyticAt.inv hbase' hne
    have hgerm : (fun s : ℂ => soninEval 1 ((f : SoninL2)) s * h s)
        =ᶠ[𝓝 ρ] fun s : ℂ => (s - ρ) ^ m * ((s - ρ') ^ l')⁻¹ := by
      filter_upwards [hbase, eventually_ne_nhds (fun hc : ρ = ρ' => hρρ' hc.symm)] with s hs hsne
      exact hs hsne
    have hjet := iteratedDeriv_eq_zero_of_eventuallyEq_sub_pow_mul hW hgerm
      (show m - l < m by omega)
    rw [hjet]
    simp [hρρ']

end

end RHTower
