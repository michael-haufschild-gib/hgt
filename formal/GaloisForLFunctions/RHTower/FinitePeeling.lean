import GaloisForLFunctions.HTGeometry.Peeling

/-!
# Peeling an arbitrary finite analytic zero packet

`exists_multi_peel` produces a globally nonvanishing cofactor when the supplied finite set contains
every zero on the open domain.  Contour arguments often need a different statement: peel only the
finitely many zeros in one compact window, retain an analytic global cofactor, and certify that the
cofactor is nonzero at each peeled point.  This module provides that finite-packet factorization.
-/

namespace RHTower

open Complex Filter Set

/-- **Finite-packet analytic peeling.**  Any finite family of points with finite vanishing order can
be peeled from an analytic function.  The resulting cofactor is analytic on the original open set,
is nonzero at every peeled point, and gives an exact product factorization throughout that set.
Zeros outside the packet are intentionally retained in the cofactor. -/
theorem exists_finite_peel {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (t : Finset ℂ)
    (htU : ∀ w ∈ t, w ∈ U)
    (hord : ∀ w ∈ t, analyticOrderAt f w ≠ ⊤) :
    ∃ (m : ℂ → ℕ) (h : ℂ → ℂ), AnalyticOnNhd ℂ h U ∧
      (∀ w ∈ t, m w = (analyticOrderAt f w).toNat) ∧
      (∀ w ∈ t, h w ≠ 0) ∧
      ∀ z ∈ U, f z = (∏ w ∈ t, (z - w) ^ m w) * h z := by
  classical
  revert f htU hord
  induction t using Finset.induction_on with
  | empty =>
      intro f hf _ _
      exact ⟨fun _ => 0, f, hf, by simp, by simp, fun z _ => by simp⟩
  | insert ρ s hρs ih =>
      intro f hf htU hord
      have hρU : ρ ∈ U := htU ρ (Finset.mem_insert_self ρ s)
      have hordρ : analyticOrderAt f ρ ≠ ⊤ :=
        hord ρ (Finset.mem_insert_self ρ s)
      set mρ : ℕ := (analyticOrderAt f ρ).toNat with hmρ
      have hmcast : analyticOrderAt f ρ = (mρ : ℕ∞) :=
        (ENat.coe_toNat hordρ).symm
      obtain ⟨h₁, hh₁an, hh₁ρ, hfact₁, hords₁⟩ :=
        exists_peel hU hf hρU hmcast
      have hord₁ : ∀ w ∈ s, analyticOrderAt h₁ w ≠ ⊤ := by
        intro w hw
        have hwρ : w ≠ ρ := fun h => hρs (h ▸ hw)
        rw [hords₁ w (htU w (Finset.mem_insert_of_mem hw)) hwρ]
        exact hord w (Finset.mem_insert_of_mem hw)
      obtain ⟨m', h', hh'an, hm', hh'0, hfact'⟩ :=
        ih hh₁an (fun w hw => htU w (Finset.mem_insert_of_mem hw)) hord₁
      refine ⟨fun w => if w = ρ then mρ else m' w, h', hh'an, ?_, ?_, fun z hz => ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwρ | hws
        · subst w
          simp [mρ]
        · change (if w = ρ then mρ else m' w) = (analyticOrderAt f w).toNat
          rw [if_neg (ne_of_mem_of_not_mem hws hρs), hm' w hws,
            hords₁ w (htU w (Finset.mem_insert_of_mem hws))
              (ne_of_mem_of_not_mem hws hρs)]
      · intro w hw
        rcases Finset.mem_insert.mp hw with hwρ | hws
        · subst w
          intro hh'ρ
          have hzero : h₁ ρ = 0 := by
            rw [hfact' ρ hρU, hh'ρ, mul_zero]
          exact hh₁ρ hzero
        · exact hh'0 w hws
      · rw [Finset.prod_insert hρs]
        beta_reduce
        have hif : (if ρ = ρ then mρ else m' ρ) = mρ := if_pos rfl
        have hprods : (∏ w ∈ s, (z - w) ^ (if w = ρ then mρ else m' w)) =
            ∏ w ∈ s, (z - w) ^ m' w :=
          Finset.prod_congr rfl fun w hw => by
            rw [if_neg (ne_of_mem_of_not_mem hw hρs)]
        rw [hif, hprods, hfact₁ z hz, hfact' z hz]
        ring

end RHTower
