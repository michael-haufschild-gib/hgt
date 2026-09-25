import GaloisForLFunctions.RHTower.SelbergPoincareUnfolding

open MeasureTheory UpperHalfPlane ModularGroup Set
open scoped MatrixGroups Pointwise

/-!
# Unfolding `Γ∞(N)\Γ(N)`-series with an arbitrary seed

For `N ≥ 3`, a `⟨T^N⟩`-invariant seed `F` and a `Γ(N)`-invariant `g` with `F g` integrable on the strip
`0 ≤ Re z < N`: `∫_{cellP} (Σ_{q ∈ Γ∞(N)\Γ(N)} F(q z)) g(z) dμ = ∫_{strip} F g dμ` (`seed_unfold`). The Eisenstein
series is the seed `Im(z)^s`; the truncated row sums of the Maass–Selberg relation are the seeds
`[Im z ≤ Y] Im(z)^s`.
-/

namespace GaloisForLFunctions.RHTower.SelbergSeedUnfolding
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SelbergPoincare
  GaloisForLFunctions.RHTower.SelbergPoincareUnfolding
open CongruenceSubgroup

variable (N : ℕ)

/-- **Unfolding a `Γ∞(N)\Γ(N)`-series with an arbitrary seed.** For `N ≥ 3`, a `Γ(N)`-invariant `g` and a
`⟨T^N⟩`-invariant seed `F` with `F g` integrable on the strip `0 ≤ x < N`:
`∫_{cellP} (Σ_{q ∈ Γ∞(N)\Γ(N)} F(q z)) g(z) dμ = ∫_{strip} F g dμ`. -/
theorem seed_unfold [NeZero N] (hN : 3 ≤ N) {F g : ℍ → ℂ}
    (hF : ∀ (h : Hinf N) z, F (((h : Gamma N) : SL(2, ℤ)) • z) = F z)
    (hg : ∀ (γ : Gamma N) z, g ((γ : SL(2, ℤ)) • z) = g z)
    (hint : IntegrableOn (fun z => F z * g z) (stripN N)) :
    ∫ z in GaloisForLFunctions.RHTower.SarnakXuePretrace.cellP N, (∑' q : Cosets N, F (((Quotient.out q : Gamma N) : SL(2, ℤ)) • z)) * g z =
      ∫ z in stripN N, F z * g z := by
  set f : ℍ → ℂ := fun z => F z * g z
  have hfinv : ∀ (h : Hinf N) z, f (h • z) = f z := by
    intro h z
    simp only [f]
    rw [show h • z = ((h : Gamma N) : SL(2, ℤ)) • z from rfl, hF, hg]
  have hGF := isFundamentalDomain_cellP_Gamma N hN
  set Rep : Cosets N → Gamma N := fun q => Quotient.out q
  have hU : IsFundamentalDomain (Hinf N) (⋃ q, Rep q • GaloisForLFunctions.RHTower.SarnakXuePretrace.cellP N) volume := by
    apply isFundamentalDomain_iUnion_smul_of_cosetReps hGF (Hinf N) Rep
    · intro g'
      set c : Cosets N := Quotient.mk _ g'
      have hc : QuotientGroup.rightRel (Hinf N) (Quotient.out c) g' := Quotient.mk_out (s := _) g'
      have hmem : g' * (Quotient.out c)⁻¹ ∈ Hinf N := QuotientGroup.rightRel_apply.mp hc
      exact ⟨⟨_, hmem⟩, c, by simp [Rep]⟩
    · intro h h' c c' heq
      have hcc : c = c' := by
        rw [← Quotient.out_eq c, ← Quotient.out_eq c']
        apply Quotient.sound
        show QuotientGroup.rightRel (Hinf N) _ _
        rw [QuotientGroup.rightRel_apply]
        have : Quotient.out c' * (Quotient.out c)⁻¹ = (h' : Gamma N)⁻¹ * h := by
          calc Quotient.out c' * (Quotient.out c)⁻¹
              = (h' : Gamma N)⁻¹ * ((h' : Gamma N) * Quotient.out c') * (Quotient.out c)⁻¹ := by group
            _ = (h' : Gamma N)⁻¹ * ((h : Gamma N) * Quotient.out c) * (Quotient.out c)⁻¹ := by
                rw [heq]
            _ = _ := by group
        rw [this]
        exact mul_mem (inv_mem h'.2) h.2
      subst hcc
      exact ⟨Subtype.ext (mul_right_cancel heq), rfl⟩
  have hRinj : Function.Injective Rep := by
    intro q q' h
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    simp only [Rep] at h
    rw [h]
  have hintU : IntegrableOn f (⋃ q, Rep q • GaloisForLFunctions.RHTower.SarnakXuePretrace.cellP N) :=
    (hU.integrableOn_iff (isFundamentalDomain_stripN N) hfinv).mpr hint
  rw [(isFundamentalDomain_stripN N).setIntegral_eq hU hfinv,
    integral_iUnion_eq_integral_tsum hGF hRinj hintU]
  congr 1
  funext z
  simp only [f]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro q
  rw [show Rep q • z = ((Rep q : Gamma N) : SL(2, ℤ)) • z from rfl, hg]

end GaloisForLFunctions.RHTower.SelbergSeedUnfolding
