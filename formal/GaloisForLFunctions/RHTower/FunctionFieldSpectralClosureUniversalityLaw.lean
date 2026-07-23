import GaloisForLFunctions.HTGeometry.MultisetSymmetricDetermination
import GaloisForLFunctions.RHTower.FunctionFieldFE

/-!
# Function-field spectral-closure universality

The function-field functional-equation module derives the weighted elementary-symmetric
coefficient relations from closure of the Frobenius multiset under `ω ↦ q / ω`.  Elementary
symmetric functions determine a finite multiset, so the entire coefficient relation is also a
converse: it recovers the spectral pairing with no separately supplied root matching.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Coefficient completeness for the function-field functional equation.**  A finite complex
multiset is closed under `ω ↦ q / ω` exactly when all of its elementary symmetric functions obey
the `q`-weighted reciprocal relation.  Thus coefficient-level palindromy and spectral pairing are
equivalent data, without a chosen matching of roots. -/
theorem functionField_spectralClosure_iff_esymm_FE (q : ℂ) (S : Multiset ℂ) :
    S.map (fun ω => q / ω) = S ↔
      ∀ k : ℕ, S.esymm k = q ^ k * (S.map (fun ω => ω⁻¹)).esymm k := by
  constructor
  · intro hclosed k
    exact functionField_esymm_FE q S hclosed k
  · intro hcoeff
    let T : Multiset ℂ := S.map (fun ω => q / ω)
    have hcard : S.card = T.card := by
      simp [T]
    have hscaled (k : ℕ) :
        T.esymm k = q ^ k * (S.map (fun ω => ω⁻¹)).esymm k := by
      have h := multiset_esymm_map_mul q (S.map (fun ω => ω⁻¹)) k
      rw [Multiset.map_map] at h
      simpa only [T, Function.comp_apply, div_eq_mul_inv] using h
    have hST : S = T := multiset_eq_of_esymm_eq hcard (fun k _ => by
      rw [hcoeff k, hscaled k])
    exact hST.symm

/-- The bounded coefficient packet through the multiset cardinality is already complete: higher
elementary symmetric functions carry no additional spectral-closure information. -/
theorem functionField_spectralClosure_iff_bounded_esymm_FE (q : ℂ) (S : Multiset ℂ) :
    S.map (fun ω => q / ω) = S ↔
      ∀ k ≤ S.card,
        S.esymm k = q ^ k * (S.map (fun ω => ω⁻¹)).esymm k := by
  constructor
  · intro hclosed k _
    exact functionField_esymm_FE q S hclosed k
  · intro hcoeff
    let T : Multiset ℂ := S.map (fun ω => q / ω)
    have hcard : S.card = T.card := by
      simp [T]
    have hscaled (k : ℕ) :
        T.esymm k = q ^ k * (S.map (fun ω => ω⁻¹)).esymm k := by
      have h := multiset_esymm_map_mul q (S.map (fun ω => ω⁻¹)) k
      rw [Multiset.map_map] at h
      simpa only [T, Function.comp_apply, div_eq_mul_inv] using h
    have hST : S = T := multiset_eq_of_esymm_eq hcard (fun k hk => by
      rw [hcoeff k hk, hscaled k])
    exact hST.symm

end

end GaloisForLFunctions
