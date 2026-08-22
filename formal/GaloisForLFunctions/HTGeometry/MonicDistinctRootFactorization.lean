import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

/-!
# A monic polynomial with as many distinct roots as its degree splits into linear factors

The deformation step of the generic-Galois-group construction lifts the `D` distinct roots of a
residue polynomial to `D` distinct roots of the deformed polynomial; the deformed polynomial is
monic of degree `D`, so it is exactly the product of the corresponding linear factors.  That is the
statement below, over any integral domain.

## Main result

* `eq_prod_X_sub_C_of_monic_of_injective_roots`
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **A monic polynomial of degree `d` with `d` distinct roots is the product of the corresponding
linear factors.** -/
theorem eq_prod_X_sub_C_of_monic_of_injective_roots {p : R[X]} (hp : p.Monic) {d : ℕ}
    (hd : p.natDegree = d) {f : Fin d → R} (hf : Function.Injective f)
    (hroot : ∀ i, p.IsRoot (f i)) :
    p = ∏ i, (X - C (f i)) := by
  classical
  set q : R[X] := ∏ i, (X - C (f i)) with hq
  have hqm : q.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (f i)
  have hqdeg : q.natDegree = d := by
    rw [hq, Polynomial.natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (f i)]
    simp
  have hp0 : p ≠ 0 := hp.ne_zero
  set s : Multiset R := Multiset.map f Finset.univ.val with hs
  have hsnodup : s.Nodup := by
    rw [hs]
    exact Finset.univ.nodup.map hf
  have hsle : s ≤ p.roots := by
    refine Multiset.le_iff_count.mpr fun a => ?_
    by_cases hmem : a ∈ s
    · have hcount1 : Multiset.count a s ≤ 1 :=
        Multiset.nodup_iff_count_le_one.mp hsnodup a
      have hroot' : p.IsRoot a := by
        obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hmem
        exact hroot i
      have hge : 1 ≤ Multiset.count a p.roots := by
        rw [Multiset.one_le_count_iff_mem]
        exact (Polynomial.mem_roots' ).mpr ⟨hp0, hroot'⟩
      omega
    · simp [Multiset.count_eq_zero_of_notMem hmem]
  have hdvd : q ∣ p := by
    have h1 : (Multiset.map (fun a => X - C a) s).prod ∣
        (Multiset.map (fun a => X - C a) p.roots).prod :=
      Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hsle)
    have h2 := Polynomial.prod_multiset_X_sub_C_dvd p
    have h3 : (Multiset.map (fun a => X - C a) s).prod = q := by
      rw [hs, hq, Multiset.map_map]
      rfl
    rw [h3] at h1
    exact h1.trans h2
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    intro h
    rw [hc, h, mul_zero] at hp0
    exact hp0 rfl
  have hdegmul : p.natDegree = q.natDegree + c.natDegree := by
    rw [hc, Polynomial.natDegree_mul hqm.ne_zero hc0]
  have hcdeg : c.natDegree = 0 := by
    rw [hd, hqdeg] at hdegmul
    omega
  have hcm : c.Monic := by
    have hpm := hp
    rw [hc] at hpm
    exact hqm.of_mul_monic_left hpm
  have hc1 : c = 1 := by
    have hcc := Polynomial.eq_C_of_natDegree_eq_zero hcdeg
    have hlead : c.leadingCoeff = c.coeff 0 := by
      rw [Polynomial.leadingCoeff, hcdeg]
    have hone : c.coeff 0 = 1 := by
      rw [← hlead]
      exact hcm
    rw [hcc, hone, map_one]
  rw [hc, hc1, mul_one]

end GaloisForLFunctions.HTGeometry
