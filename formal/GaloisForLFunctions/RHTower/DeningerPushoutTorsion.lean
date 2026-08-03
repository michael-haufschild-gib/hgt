import GaloisForLFunctions.RHTower.DeningerCyclicReduction

/-!
# An amalgamated free product of torsion free groups is torsion free

Every element is conjugate to one lying in a factor or to a cyclically reduced one.  A cyclically
reduced element has powers of growing length, so it has infinite order; an element of a factor has
infinite order because the factors do.

* `deningerPushout_torsionFree` : the amalgam is torsion free.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **An amalgamated free product of torsion free groups is torsion free.** -/
theorem deningerPushout_torsionFree (hφ : ∀ i, Function.Injective (φ i))
    (hG : ∀ i, ∀ (x : G i) (n : ℕ), 0 < n → x ^ n = 1 → x = 1)
    (hH : ∀ (h : H) (n : ℕ), 0 < n → h ^ n = 1 → h = 1)
    (g : PushoutI φ) (n : ℕ) (hn : 0 < n) (hg : g ^ n = 1) : g = 1 := by
  classical
  obtain ⟨d⟩ := NormalWord.transversal_nonempty φ hφ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨c, hc⟩ := deningerExists_cycRed (d := d) g
  set g' := c⁻¹ * g * c with hg'def
  have hg'pow : g' ^ (m + 1) = 1 := by
    have hcp : (c⁻¹ * g * (c⁻¹)⁻¹) ^ (m + 1) = c⁻¹ * g ^ (m + 1) * (c⁻¹)⁻¹ := conj_pow
    rw [inv_inv] at hcp
    rw [hg'def, hcp, hg]
    group
  suffices hs : g' = 1 by
    have hgc : g = c * g' * c⁻¹ := by rw [hg'def]; group
    rw [hgc, hs, mul_one, mul_inv_cancel]
  rcases hc with hshort | ⟨L, hLne, hred, halt, hcyc, hgL⟩
  · -- `g'` lies in a factor
    rcases Nat.lt_or_ge (deningerLen d g') 1 with hlt | hge
    · have h0 : deningerLen d g' = 0 := by omega
      obtain ⟨h, hh⟩ := (deningerLen_eq_zero_iff (d := d) g').1 h0
      rw [← hh] at hg'pow ⊢
      rw [← map_pow] at hg'pow
      rw [hH h (m + 1) (by omega) (PushoutI.base_injective hφ (by rw [hg'pow, map_one])), map_one]
    · have h1 : deningerLen d g' = 1 := by omega
      rcases deningerExists_letterProd (d := d) g' with ⟨h, hh, h0⟩ | ⟨L, _, hredL, _, hlenL, hgL⟩
      · omega
      · obtain ⟨p, rfl⟩ : ∃ p, L = [p] := by
          rw [h1] at hlenL
          match L, hlenL with
          | [p], _ => exact ⟨p, rfl⟩
        have hp : g' = PushoutI.of p.1 p.2 := by
          rw [hgL, deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
        rw [hp] at hg'pow
        rw [← map_pow] at hg'pow
        have hx : p.2 = 1 := hG p.1 p.2 (m + 1) (by omega)
          (PushoutI.of_injective hφ p.1 (by rw [hg'pow, map_one]))
        exact absurd ⟨1, by rw [map_one, ← hx]⟩ (hredL p List.mem_cons_self)
  · -- `g'` is cyclically reduced
    exfalso
    have hlen := deningerLen_pow (d := d) L 1 m hLne hred halt hcyc
    rw [map_one, mul_one, ← hgL, hg'pow, deningerLen_one] at hlen
    have hzero : (m + 1) * L.length = 0 := hlen.symm
    have hL0 : L.length = 0 := by
      rcases Nat.mul_eq_zero.1 hzero with h | h
      · omega
      · exact h
    exact hLne (List.length_eq_zero_iff.1 hL0)

end RHTower
