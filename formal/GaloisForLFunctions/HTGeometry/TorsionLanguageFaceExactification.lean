import GaloisForLFunctions.HTGeometry.GeometricPatternWeightLimit

/-!
# Exactification of a convergent ADE face by torsion-language recurrence

A finite face of bounded multiplicity patterns has polynomially normalized weights.  If its
phase-weighted sum tends to zero along a torsion-language-universal phase, exact recurrence of
every torsion word and finite Fourier inversion force every limiting face weight to vanish.
-/

namespace GaloisForLFunctions

open Filter Finset Topology

noncomputable section

/-- Finite Fourier exactification for multiplicity patterns valued in `Fin (D+1)`. -/
theorem face_fin_weights_eq_zero
    {M D : ℕ} (F : Finset (Fin M → Fin (D + 1)))
    (ell : (Fin M → Fin (D + 1)) → ℂ)
    (hvanish : ∀ s : Fin M → ℂ, (∀ r, s r ^ (D + 1) = 1) →
      ∑ p ∈ F, ell p * ∏ r, s r ^ (p r : ℕ) = 0) :
    ∀ p ∈ F, ell p = 0 := by
  classical
  let enc : (Fin M → Fin (D + 1)) → (Fin M → ℕ) :=
    fun p r => (p r : ℕ)
  have henc : Function.Injective enc := by
    intro p q hpq
    funext r
    exact Fin.ext (congrFun hpq r)
  let Fnat := F.image enc
  let ellNat : (Fin M → ℕ) → ℂ := fun e =>
    if h : e ∈ Fnat then ell (Classical.choose (Finset.mem_image.mp h)) else 0
  have hellNat : ∀ p ∈ F, ellNat (enc p) = ell p := by
    intro p hp
    have hmem : enc p ∈ Fnat := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    dsimp only [ellNat]
    rw [dif_pos hmem]
    let p' := Classical.choose (Finset.mem_image.mp hmem)
    have hp'eq : enc p' = enc p :=
      (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    have hp' : p' = p := henc hp'eq
    exact congrArg ell hp'
  have hvanishNat : ∀ s : Fin M → ℂ, (∀ r, s r ^ (D + 1) = 1) →
      ∑ e ∈ Fnat, ellNat e * ∏ r, s r ^ e r = 0 := by
    intro s hs
    calc
      ∑ e ∈ Fnat, ellNat e * ∏ r, s r ^ e r =
          ∑ p ∈ F, ellNat (enc p) * ∏ r, s r ^ enc p r := by
        dsimp only [Fnat]
        rw [Finset.sum_image]
        intro p hp q hq hpq
        exact henc hpq
      _ = ∑ p ∈ F, ell p * ∏ r, s r ^ (p r : ℕ) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hellNat p hp]
      _ = 0 := hvanish s hs
  have hzero := face_weights_eq_zero (m := D + 1) (D := D) (by omega) Fnat
    (fun e he r => by
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp he
      rw [← hpe]
      change (p r : ℕ) ≤ D
      omega)
    ellNat hvanishNat
  intro p hp
  have hz := hzero (enc p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  rwa [hellNat p hp] at hz

/-- Torsion-language universality turns asymptotic face cancellation into exact vanishing of every
limiting face weight. -/
theorem face_weights_eq_zero_of_torsionLanguageUniversal
    {M D : ℕ} (u : ℕ → ℂ) (hu : TorsionLanguageUniversal u)
    (F : Finset (Fin M → Fin (D + 1)))
    (w : ℕ → (Fin M → Fin (D + 1)) → ℂ)
    (ell : (Fin M → Fin (D + 1)) → ℂ)
    (hw : ∀ p ∈ F, Tendsto (fun q => w q p) atTop (𝓝 (ell p)))
    (hface : Tendsto (fun q =>
      ∑ p ∈ F, w q p * ∏ r : Fin M, u (q + (r : ℕ)) ^ (p r : ℕ))
      atTop (𝓝 0)) :
    ∀ p ∈ F, ell p = 0 := by
  have hvanish : ∀ s : Fin M → ℂ, (∀ r, s r ^ (D + 1) = 1) →
      ∑ p ∈ F, ell p * ∏ r, s r ^ (p r : ℕ) = 0 := by
    intro s hs
    obtain ⟨q, _hqmono, hqtop, hqword⟩ :=
      hu.exists_strictMono_occurrences (show 0 < D + 1 by omega) s hs
    have hterm : ∀ p ∈ F,
        Tendsto (fun k =>
          w (q k) p * ∏ r : Fin M, u (q k + (r : ℕ)) ^ (p r : ℕ))
          atTop (𝓝 (ell p * ∏ r : Fin M, s r ^ (p r : ℕ))) := by
      intro p hp
      simpa only [hqword] using
        (((hw p hp).comp hqtop).mul tendsto_const_nhds)
    have hsum := tendsto_finsetSum F (fun p hp => hterm p hp)
    have hzero := hface.comp hqtop
    exact tendsto_nhds_unique hsum hzero
  exact face_fin_weights_eq_zero F ell hvanish

end

end GaloisForLFunctions
