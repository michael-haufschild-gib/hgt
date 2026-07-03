/-
The deck-class cocycle (MWM lane, A3 revived — task #113; q62 deck pattern).

The box invariant w_k of the MWM lane, defined WITHOUT contour integrals (mathlib has no
argument principle): on a two-chart cover U₁, U₂ whose overlap splits into two preconnected
pieces VP, VM (the standard annulus picture), any two local 2^k-th roots of f differ by
constant roots of unity on each overlap piece, and the RATIO of the two constants is a
well-defined element of μ_{2^k} — the deck class. It is independent of the choice of local
roots and of the basepoints, it is trivial exactly when the local roots glue to a global
root on U₁ ∪ U₂ (the ladder link: RH_{2^k} language), and it is coherent in k (the class of
the squared roots is the square of the class — the dyadic tower structure, cf. the q62
`dyadicRoot` pattern).

Everything is derivative-free: the engine is `pow_root_unique` (identity theorem +
geometric-sum factorisation), anchored at a single point where f does not vanish.
-/
import GaloisForLFunctions.RHTower.KummerObstruction

namespace RHTower

open Set

/-- Two analytic `n`-th roots of the same function on a preconnected open set differ by a
constant `n`-th root of unity, read off at any anchor where `f` does not vanish. -/
theorem pow_root_ratio {f g₁ g₂ : ℂ → ℂ} {U : Set ℂ} {n : ℕ} (hn : 0 < n)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (h₁ : AnalyticOnNhd ℂ g₁ U) (h₂ : AnalyticOnNhd ℂ g₂ U)
    (hp₁ : ∀ s ∈ U, g₁ s ^ n = f s) (hp₂ : ∀ s ∈ U, g₂ s ^ n = f s)
    {z₀ : ℂ} (hz : z₀ ∈ U) (hf0 : f z₀ ≠ 0) :
    (g₁ z₀ / g₂ z₀) ^ n = 1 ∧ Set.EqOn g₁ (fun s => (g₁ z₀ / g₂ z₀) * g₂ s) U := by
  have hg₂0 : g₂ z₀ ≠ 0 := fun h0 => hf0 (by rw [← hp₂ z₀ hz, h0, zero_pow hn.ne'])
  have hζ : (g₁ z₀ / g₂ z₀) ^ n = 1 := by
    rw [div_pow, hp₁ z₀ hz, hp₂ z₀ hz, div_self hf0]
  refine ⟨hζ, ?_⟩
  have h₂' : AnalyticOnNhd ℂ (fun s => (g₁ z₀ / g₂ z₀) * g₂ s) U :=
    fun s hs => analyticAt_const.mul (h₂ s hs)
  have hp₂' : ∀ s ∈ U, ((g₁ z₀ / g₂ z₀) * g₂ s) ^ n = f s := fun s hs => by
    rw [mul_pow, hζ, one_mul, hp₂ s hs]
  have hpt : g₁ z₀ = (g₁ z₀ / g₂ z₀) * g₂ z₀ := by
    field_simp
  exact pow_root_unique hn hU hUc h₁ h₂' hp₁ hp₂' hz hf0 hpt

/-- The deck class of a pair of local roots relative to two overlap basepoints. -/
noncomputable def deckClass (g₁ g₂ : ℂ → ℂ) (pP pM : ℂ) : ℂ :=
  (g₁ pP / g₂ pP) / (g₁ pM / g₂ pM)

/-- The deck class is a `n`-th root of unity. -/
theorem deckClass_pow_eq_one {f g₁ g₂ : ℂ → ℂ} {n : ℕ} {pP pM : ℂ}
    (h₁P : g₁ pP ^ n = f pP) (h₂P : g₂ pP ^ n = f pP)
    (h₁M : g₁ pM ^ n = f pM) (h₂M : g₂ pM ^ n = f pM)
    (hfP : f pP ≠ 0) (hfM : f pM ≠ 0) :
    deckClass g₁ g₂ pP pM ^ n = 1 := by
  have hP : (g₁ pP / g₂ pP) ^ n = 1 := by rw [div_pow, h₁P, h₂P, div_self hfP]
  have hM : (g₁ pM / g₂ pM) ^ n = 1 := by rw [div_pow, h₁M, h₂M, div_self hfM]
  rw [deckClass, div_pow, hP, hM, div_self one_ne_zero]

/-- Changing either local root multiplies both overlap ratios by the same constant, so the
deck class is independent of the choice of local roots. Stated on the standard cover data:
`U₁`, `U₂` open and preconnected, basepoints in the overlap, `f` nonvanishing there. -/
theorem deckClass_root_indep {f g₁ g₂ h₁ h₂ : ℂ → ℂ} {U₁ U₂ : Set ℂ} {n : ℕ} (hn : 0 < n)
    (hU₁ : IsOpen U₁) (hU₁c : IsPreconnected U₁)
    (hU₂ : IsOpen U₂) (hU₂c : IsPreconnected U₂)
    (hg₁ : AnalyticOnNhd ℂ g₁ U₁) (hh₁ : AnalyticOnNhd ℂ h₁ U₁)
    (hg₂ : AnalyticOnNhd ℂ g₂ U₂) (hh₂ : AnalyticOnNhd ℂ h₂ U₂)
    (hpg₁ : ∀ s ∈ U₁, g₁ s ^ n = f s) (hph₁ : ∀ s ∈ U₁, h₁ s ^ n = f s)
    (hpg₂ : ∀ s ∈ U₂, g₂ s ^ n = f s) (hph₂ : ∀ s ∈ U₂, h₂ s ^ n = f s)
    {pP pM : ℂ} (hpP₁ : pP ∈ U₁) (hpP₂ : pP ∈ U₂) (hpM₁ : pM ∈ U₁) (hpM₂ : pM ∈ U₂)
    (hfP : f pP ≠ 0) (hfM : f pM ≠ 0) :
    deckClass h₁ h₂ pP pM = deckClass g₁ g₂ pP pM := by
  obtain ⟨-, hE₁⟩ := pow_root_ratio hn hU₁ hU₁c hh₁ hg₁ hph₁ hpg₁ hpP₁ hfP
  obtain ⟨-, hE₂⟩ := pow_root_ratio hn hU₂ hU₂c hh₂ hg₂ hph₂ hpg₂ hpP₂ hfP
  have hg₁P : g₁ pP ≠ 0 := fun h0 => hfP (by rw [← hpg₁ pP hpP₁, h0, zero_pow hn.ne'])
  have hg₂P : g₂ pP ≠ 0 := fun h0 => hfP (by rw [← hpg₂ pP hpP₂, h0, zero_pow hn.ne'])
  have hg₁M : g₁ pM ≠ 0 := fun h0 => hfM (by rw [← hpg₁ pM hpM₁, h0, zero_pow hn.ne'])
  have hg₂M : g₂ pM ≠ 0 := fun h0 => hfM (by rw [← hpg₂ pM hpM₂, h0, zero_pow hn.ne'])
  have hh₁P : h₁ pP ≠ 0 := fun h0 => hfP (by rw [← hph₁ pP hpP₁, h0, zero_pow hn.ne'])
  have hh₂P : h₂ pP ≠ 0 := fun h0 => hfP (by rw [← hph₂ pP hpP₂, h0, zero_pow hn.ne'])
  have e₁M := hE₁ hpM₁
  have e₂M := hE₂ hpM₂
  simp only at e₁M e₂M
  rw [deckClass, deckClass, e₁M, e₂M]
  field_simp

/-- Coherence in the dyadic tower: the deck class of the squared roots is the square of
the deck class — `w_k = w_{k+1}²` in the ladder's notation. -/
theorem deckClass_sq (g₁ g₂ : ℂ → ℂ) (pP pM : ℂ) :
    deckClass (fun s => g₁ s ^ 2) (fun s => g₂ s ^ 2) pP pM =
      deckClass g₁ g₂ pP pM ^ 2 := by
  simp only [deckClass, div_pow]

/-- **Triviality ⟺ gluing.** On the standard two-chart annulus data — overlap exactly
`VP ∪ VM` with each piece open, preconnected, carrying a basepoint where `f` does not
vanish — the deck class is `1` iff the two local roots glue (after the canonical constant
adjustment) to a global analytic `n`-th root of `f` on `U₁ ∪ U₂`. -/
theorem deckClass_eq_one_iff_exists_root {f g₁ g₂ : ℂ → ℂ} {U₁ U₂ VP VM : Set ℂ} {n : ℕ}
    (hn : 0 < n) (hU₁ : IsOpen U₁) (hU₁c : IsPreconnected U₁)
    (hU₂ : IsOpen U₂) (hU₂c : IsPreconnected U₂)
    (hVP : IsOpen VP) (hVPc : IsPreconnected VP)
    (hVM : IsOpen VM) (hVMc : IsPreconnected VM)
    (hcap : U₁ ∩ U₂ = VP ∪ VM)
    (hg₁ : AnalyticOnNhd ℂ g₁ U₁) (hg₂ : AnalyticOnNhd ℂ g₂ U₂)
    (hpg₁ : ∀ s ∈ U₁, g₁ s ^ n = f s) (hpg₂ : ∀ s ∈ U₂, g₂ s ^ n = f s)
    {pP pM : ℂ} (hpP : pP ∈ VP) (hpM : pM ∈ VM)
    (hfP : f pP ≠ 0) (hfM : f pM ≠ 0) :
    deckClass g₁ g₂ pP pM = 1 ↔
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (U₁ ∪ U₂) ∧ ∀ s ∈ U₁ ∪ U₂, g s ^ n = f s := by
  classical
  have hVPsub : VP ⊆ U₁ ∩ U₂ := by rw [hcap]; exact subset_union_left
  have hVMsub : VM ⊆ U₁ ∩ U₂ := by rw [hcap]; exact subset_union_right
  have hpP₁ : pP ∈ U₁ := (hVPsub hpP).1
  have hpP₂ : pP ∈ U₂ := (hVPsub hpP).2
  have hpM₁ : pM ∈ U₁ := (hVMsub hpM).1
  have hpM₂ : pM ∈ U₂ := (hVMsub hpM).2
  constructor
  · intro hw
    set ζ : ℂ := g₁ pP / g₂ pP with hζ_def
    have hζn : ζ ^ n = 1 := by
      rw [hζ_def, div_pow, hpg₁ pP hpP₁, hpg₂ pP hpP₂, div_self hfP]
    obtain ⟨-, hEP⟩ := pow_root_ratio hn hVP hVPc (fun s hs => hg₁ s (hVPsub hs).1)
      (fun s hs => hg₂ s (hVPsub hs).2) (fun s hs => hpg₁ s (hVPsub hs).1)
      (fun s hs => hpg₂ s (hVPsub hs).2) hpP hfP
    obtain ⟨-, hEM⟩ := pow_root_ratio hn hVM hVMc (fun s hs => hg₁ s (hVMsub hs).1)
      (fun s hs => hg₂ s (hVMsub hs).2) (fun s hs => hpg₁ s (hVMsub hs).1)
      (fun s hs => hpg₂ s (hVMsub hs).2) hpM hfM
    have hζM : g₁ pM / g₂ pM = ζ := by
      have hw' := hw
      rw [deckClass] at hw'
      have hg₁M : g₁ pM ≠ 0 := fun h0 => hfM (by rw [← hpg₁ pM hpM₁, h0, zero_pow hn.ne'])
      have hg₂M : g₂ pM ≠ 0 := fun h0 => hfM (by rw [← hpg₂ pM hpM₂, h0, zero_pow hn.ne'])
      have hden : g₁ pM / g₂ pM ≠ 0 := div_ne_zero hg₁M hg₂M
      rw [div_eq_one_iff_eq hden] at hw'
      rw [hζ_def, ← hw']
    have hEq : ∀ s ∈ U₁ ∩ U₂, g₁ s = ζ * g₂ s := by
      intro s hs
      rw [hcap] at hs
      rcases hs with hs | hs
      · exact hEP hs
      · have := hEM hs
        simp only at this
        rw [this, hζM]
    refine ⟨fun z => if z ∈ U₁ then g₁ z else ζ * g₂ z, ?_, ?_⟩
    · intro z hz
      by_cases hz₁ : z ∈ U₁
      · exact (hg₁ z hz₁).congr (Filter.eventually_of_mem (hU₁.mem_nhds hz₁)
          (fun y hy => by simp [hy]))
      · have hz₂ : z ∈ U₂ := hz.resolve_left hz₁
        have hconst : AnalyticAt ℂ (fun _ : ℂ => ζ) z := analyticAt_const
        refine (hconst.mul (hg₂ z hz₂)).congr
          (Filter.eventually_of_mem (hU₂.mem_nhds hz₂) (fun y hy => ?_))
        by_cases hy₁ : y ∈ U₁
        · simp only [hy₁, if_pos]
          exact (hEq y ⟨hy₁, hy⟩).symm
        · simp [hy₁]
    · intro s hs
      by_cases hs₁ : s ∈ U₁
      · simp only [hs₁, if_pos]
        exact hpg₁ s hs₁
      · have hs₂ : s ∈ U₂ := hs.resolve_left hs₁
        simp only [hs₁, if_false]
        rw [mul_pow, hζn, one_mul]
        exact hpg₂ s hs₂
  · rintro ⟨g, hg, hpg⟩
    have hgU₁ : AnalyticOnNhd ℂ g U₁ := fun s hs => hg s (Or.inl hs)
    have hgU₂ : AnalyticOnNhd ℂ g U₂ := fun s hs => hg s (Or.inr hs)
    have hpgU₁ : ∀ s ∈ U₁, g s ^ n = f s := fun s hs => hpg s (Or.inl hs)
    have hpgU₂ : ∀ s ∈ U₂, g s ^ n = f s := fun s hs => hpg s (Or.inr hs)
    obtain ⟨-, hC₁⟩ := pow_root_ratio hn hU₁ hU₁c hg₁ hgU₁ hpg₁ hpgU₁ hpP₁ hfP
    obtain ⟨-, hC₂⟩ := pow_root_ratio hn hU₂ hU₂c hg₂ hgU₂ hpg₂ hpgU₂ hpP₂ hfP
    have e₁M := hC₁ hpM₁
    have e₂M := hC₂ hpM₂
    simp only at e₁M e₂M
    have hgpM : g pM ≠ 0 := fun h0 => hfM (by rw [← hpgU₁ pM hpM₁, h0, zero_pow hn.ne'])
    have hgpP : g pP ≠ 0 := fun h0 => hfP (by rw [← hpgU₁ pP hpP₁, h0, zero_pow hn.ne'])
    have hg₂P : g₂ pP ≠ 0 := fun h0 => hfP (by rw [← hpg₂ pP hpP₂, h0, zero_pow hn.ne'])
    have hg₂M : g₂ pM ≠ 0 := fun h0 => hfM (by rw [← hpg₂ pM hpM₂, h0, zero_pow hn.ne'])
    have hg₁P : g₁ pP ≠ 0 := fun h0 => hfP (by rw [← hpg₁ pP hpP₁, h0, zero_pow hn.ne'])
    rw [deckClass, e₁M, e₂M]
    have key : ((g₁ pP / g pP) * g pM) / ((g₂ pP / g pP) * g pM) = g₁ pP / g₂ pP := by
      field_simp
    rw [key]
    exact div_self (div_ne_zero hg₁P hg₂P)

end RHTower
