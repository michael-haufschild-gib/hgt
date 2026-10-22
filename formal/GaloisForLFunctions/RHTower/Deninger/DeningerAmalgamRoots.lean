import GaloisForLFunctions.RHTower.Deninger.DeningerBaseCentralizer
import GaloisForLFunctions.RHTower.Deninger.DeningerConjCycRed

/-!
# Uniqueness of roots in an amalgam

A common power of two elements is, after conjugation, either a cyclically reduced word, an element
of a factor which does not conjugate into the base group there, or an element of the base group.
The three cases are settled separately, and conjugation transports the conclusion back, so an
amalgam whose base group is abelian, torsion free, self-centralizing in each factor and not moved by
conjugation from them has unique roots as soon as its factors do.

* `deningerAmalgam_pow_inj` : uniqueness of roots in an amalgam.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- Conjugation is injective. -/
theorem deningerConj_inj (w x y : PushoutI φ) (h : w⁻¹ * x * w = w⁻¹ * y * w) : x = y := by
  have := congrArg (fun z => w * z * w⁻¹) h
  simpa [mul_assoc] using this

include d in
/-- **Uniqueness of roots in an amalgam.** -/
theorem deningerAmalgam_pow_inj (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hself : ∀ (i : ι) (x : G i) (v : H), v ≠ 1 → x * φ i v * x⁻¹ = φ i v → x ∈ (φ i).range)
    (hcomm : ∀ u v : H, u * v = v * u)
    (htf : ∀ (u : H) (m : ℕ), 0 < m → u ^ m = 1 → u = 1)
    (hH : ∀ (a b : H) (m : ℕ), 0 < m → a ^ m = b ^ m → a = b)
    (hG : ∀ (i : ι) (a b : G i) (m : ℕ), 0 < m → a ^ m = b ^ m → a = b)
    (htor : ∀ (g : PushoutI φ) (m : ℕ), 0 < m → g ^ m = 1 → g = 1)
    (x y : PushoutI φ) (n : ℕ) (heq : x ^ (n + 1) = y ^ (n + 1)) : x = y := by
  classical
  by_cases hlen : deningerLen d (x ^ (n + 1)) = 0
  · obtain ⟨k, hk⟩ := (deningerLen_eq_zero_iff (d := d) (x ^ (n + 1))).1 hlen
    by_cases hk1 : k = 1
    · subst hk1
      rw [map_one] at hk
      rw [htor x (n + 1) (by omega) hk.symm, htor y (n + 1) (by omega) (by rw [← heq, ← hk])]
    · exact deningerPow_eq_of_basePow (d := d) hφ hcent hself hH k hk1 x y n hk.symm
        (by rw [← heq]; exact hk.symm)
  · obtain ⟨w, V, hVne, hVred, hValt, hdisj, hz⟩ :=
      deningerExists_cycRed_conj (d := d) (x ^ (n + 1)) hlen
    rcases hdisj with hshort | hVcyc
    · obtain ⟨p, hp⟩ : ∃ p, V = [p] := by
        refine List.length_eq_one_iff.1 ?_
        have := List.length_pos_iff.2 hVne
        omega
      subst hp
      have hpred : p.2 ∉ (φ p.1).range := hVred p (by simp)
      have hzp : w⁻¹ * x ^ (n + 1) * w = PushoutI.of (φ := φ) p.1 p.2 := by
        rw [hz, deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
      by_cases hesc : ∃ (x' : G p.1) (k : H), x'⁻¹ * p.2 * x' = φ p.1 k
      · obtain ⟨x', k, hx'⟩ := hesc
        set w' : PushoutI φ := w * PushoutI.of (φ := φ) p.1 x' with hw'
        have hz' : w'⁻¹ * x ^ (n + 1) * w' = PushoutI.base φ k := by
          rw [hw', mul_inv_rev, ← PushoutI.of_apply_eq_base φ p.1 k, ← hx', map_mul, map_mul,
            map_inv]
          rw [show (PushoutI.of (φ := φ) p.1 x')⁻¹ * w⁻¹ * x ^ (n + 1) *
              (w * PushoutI.of (φ := φ) p.1 x') =
              (PushoutI.of (φ := φ) p.1 x')⁻¹ * (w⁻¹ * x ^ (n + 1) * w) *
              PushoutI.of (φ := φ) p.1 x' by group, hzp]
        have hz'y : w'⁻¹ * y ^ (n + 1) * w' = PushoutI.base φ k := by rw [← heq]; exact hz'
        by_cases hk1 : k = 1
        · subst hk1
          rw [map_one] at hz' hz'y
          have hx1 : x ^ (n + 1) = 1 := by
            refine deningerConj_inj w' _ _ ?_
            rw [hz']
            group
          have hy1 : y ^ (n + 1) = 1 := by
            refine deningerConj_inj w' _ _ ?_
            rw [hz'y]
            group
          rw [htor x (n + 1) (by omega) hx1, htor y (n + 1) (by omega) hy1]
        · refine deningerConj_inj w' x y ?_
          refine deningerPow_eq_of_basePow (d := d) hφ hcent hself hH k hk1 _ _ n ?_ ?_
          · rw [← deningerConj_zpow]; exact hz'
          · rw [← deningerConj_zpow]; exact hz'y
      · refine deningerConj_inj w x y ?_
        refine deningerPow_eq_of_factorPow (d := d) hφ hG p.1 p.2 hpred hesc _ _ n ?_ ?_
        · rw [← deningerConj_zpow]; exact hzp
        · rw [← deningerConj_zpow, ← heq]; exact hzp
    · exact deningerPow_eq_of_conj_cycRed (d := d) hφ hcent hcomm htf x y w _ n hVne hVred hValt
        hVcyc heq hz

end RHTower
