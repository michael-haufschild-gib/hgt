import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations

/-! Local equations at points of a reduced finite fibre. -/

namespace GlobalTheory.SchemeCohomology

/-- If a common zero fibre is Artinian and reduced, every function vanishing
at a marked point is a combination of its equations after clearing a
denominator whose value at the point is one. -/
theorem exists_clearingDenominator_of_artinian_reduced_quotient
    {A k ι : Type*} [CommRing A] [Field k] [Fintype ι] (r : ι → A)
    [IsArtinianRing (A ⧸ Ideal.span (Set.range r))]
    [IsReduced (A ⧸ Ideal.span (Set.range r))]
    (ev : A →+* k) (b : A) (hb : ev b = 0) :
    ∃ (c : A) (g : ι → A), ev c = 1 ∧ c * b = ∑ j, g j * r j := by
  let I := Ideal.span (Set.range r)
  let Q := A ⧸ I
  let π := Ideal.Quotient.mk I
  let z : Q := π b
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd z (1 : Q)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
  let c : A := 1 - b * a
  have hc : ev c = 1 := by simp only [c, map_sub, map_one, map_mul, hb, zero_mul, sub_zero]
  have hy' : π a * z ^ (n + 1) = z ^ n := by
    simpa only [← ha, smul_eq_mul, mul_one, mul_comm (z ^ (n + 1))] using hy
  have hz : (z * π a) * z ^ n = z ^ n := by
    rw [mul_comm z (π a), mul_assoc, ← pow_succ', hy']
  have hkill : π c * z ^ n = 0 := by
    rw [show π c = 1 - z * π a by simp only [c, z, map_sub, map_mul, map_one],
      sub_mul, one_mul, hz, sub_self]
  have hzero : π (c * b) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨n + 1, ?_⟩
    change (π (c * b)) ^ (n + 1) = 0
    rw [map_mul, mul_pow]
    calc
      π c ^ (n + 1) * z ^ (n + 1) =
          (π c ^ n * z) * (π c * z ^ n) := by
            rw [pow_succ (π c) n, pow_succ' z n]
            ac_rfl
      _ = 0 := by rw [hkill, mul_zero]
  have hmem : c * b ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  exact ⟨c, g, hc, hg.symm⟩

end GlobalTheory.SchemeCohomology
