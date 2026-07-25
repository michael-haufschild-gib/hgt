import GaloisForLFunctions.HTGeometry.GradedDefectInertness
import GaloisForLFunctions.HTGeometry.JetTowerFreeness
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import Mathlib

/-!
# The exact dichotomy over an inert coefficient field

Let `K` be a difference-differential field over `C`, `x` transcendental with `sigma x = x + 1` and
`x' = d` a nonzero constant, and let `F` be a `sigma`-stable intermediate field containing `C(x)`
whose `sigma`-invariants are the constants and which is **inert**: every rational translation defect
of `F` is already a translation defect of `C(x)`.

Then for rational `b` the solutions of `sigma y = y + b` are hypertranscendental over `F` exactly
when `b` is not a translation defect of `C(x)`.  Inertness is the only property of `F` used, so the
criterion depends on `b` alone, no matter how large `F` is.
-/

open Polynomial
open scoped Differential

namespace HTGeometry

variable {K : Type*} [Field K] [Algebra ℂ K] [Differential K]

/-- The jets of a rational element stay rational. -/
theorem jet_mem_coordBase {d : ℂ} {x : K} (hx : Transcendental ℂ x)
    (hdx : (x)′ = algebraMap ℂ K d) (hdc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0)
    {b : K} (hb : b ∈ coordBase x) (n : ℕ) :
    GaloisForLFunctions.differentialJet n b ∈ coordBase x := by
  induction n with
  | zero => simpa using hb
  | succ n ih =>
      rw [GaloisForLFunctions.differentialJet_succ]
      exact coordBase_deriv_mem hx hdx hdc ih

omit [Algebra ℂ K] in
theorem differentialJet_eq_iterate (n : ℕ) (z : K) :
    GaloisForLFunctions.differentialJet n z = (fun w : K => w′)^[n] z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [GaloisForLFunctions.differentialJet_succ, ih, Function.iterate_succ_apply']

/-- When `b` is not a translation defect, no nonzero element of the span of its jets is a
translation defect of `C(x)` either. -/
theorem defect_eq_zero_of_not_defect {d : ℂ} (hd : d ≠ 0) {x : K} (hx : Transcendental ℂ x)
    (sigma : K ≃ₐ[ℂ] K) (hsig : sigma x = x + 1)
    (hdx : (x)′ = algebraMap ℂ K d) (hdc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0)
    {b : K} (hb : b ∈ coordBase x)
    (hnodef : ¬ ∃ R ∈ coordBase x, sigma R - R = b)
    {u v : K} (hu : u ∈ coordBase x)
    (hv : v ∈ defectSpanAll (fun n => GaloisForLFunctions.differentialJet n b))
    (hduv : sigma u - u = v) : v = 0 := by
  classical
  by_contra hv0
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  have hlne : l.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hv0 (by rw [← hl, Finsupp.sum, h, Finset.sum_empty])
  set N : ℕ := l.support.max' hlne with hN
  have hsub : l.support ⊆ Finset.range (N + 1) := fun i hi =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ i hi))
  have hzero : ∀ i ∈ Finset.range (N + 1), i ∉ l.support →
      algebraMap ℂ K (l i) * (fun z : K => z′)^[i] b = 0 := by
    intro i _ hnot
    rw [Finsupp.notMem_support_iff.mp hnot, map_zero, zero_mul]
  have hconv : ∀ i : ℕ, l i • (GaloisForLFunctions.differentialJet i b)
      = algebraMap ℂ K (l i) * (fun z : K => z′)^[i] b := by
    intro i
    rw [Algebra.smul_def, differentialJet_eq_iterate]
  have hexpand : ∑ n ∈ Finset.range (N + 1),
      algebraMap ℂ K (l n) * (fun z : K => z′)^[n] b = sigma u - u := by
    rw [hduv, ← hl, Finsupp.sum]
    simp only [hconv]
    exact (Finset.sum_subset hsub hzero).symm
  exact hnodef (defect_of_operator_defect hd hx sigma hsig hdx hdc hb hu
    (Finsupp.mem_support_iff.mp (l.support.max'_mem hlne)) hexpand)

/-- No jet lies in the span of its predecessors when `b` is not a translation defect. -/
theorem jet_not_mem_defectSpan_of_not_defect {d : ℂ} (hd : d ≠ 0) {x : K}
    (hx : Transcendental ℂ x) (sigma : K ≃ₐ[ℂ] K) (hsig : sigma x = x + 1)
    (hdx : (x)′ = algebraMap ℂ K d) (hdc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0)
    {b : K} (hb : b ∈ coordBase x)
    (hnodef : ¬ ∃ R ∈ coordBase x, sigma R - R = b) (n : ℕ) :
    GaloisForLFunctions.differentialJet n b ∉
      defectSpan (fun k => GaloisForLFunctions.differentialJet k b) n := by
  classical
  intro hmem
  have hQ : ∃ a : ℕ → ℂ, GaloisForLFunctions.differentialJet n b
      = ∑ i ∈ Finset.range n,
          algebraMap ℂ K (a i) * GaloisForLFunctions.differentialJet i b := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
    · rintro z ⟨i, hi, rfl⟩
      simp only [Set.mem_Iio] at hi
      refine ⟨fun k => if k = i then 1 else 0, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hi) hnot
    · exact ⟨fun _ => 0, by simp⟩
    · rintro z w - - ⟨az, hz⟩ ⟨aw, hw⟩
      refine ⟨fun k => az k + aw k, ?_⟩
      rw [hz, hw, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add, add_mul]
    · rintro t z - ⟨az, hz⟩
      refine ⟨fun k => t * az k, ?_⟩
      rw [Algebra.smul_def, hz, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_assoc]
  obtain ⟨a, ha⟩ := hQ
  set A : ℕ → ℂ := fun i => if i = n then -1 else a i with hA
  have hAn : A n = -1 := by simp [hA]
  have hsum : ∑ i ∈ Finset.range (n + 1),
      algebraMap ℂ K (A i) * (fun z : K => z′)^[i] b = sigma 0 - 0 := by
    rw [map_zero, sub_zero, Finset.sum_range_succ, hAn]
    have hlow : ∀ i ∈ Finset.range n,
        algebraMap ℂ K (A i) * (fun z : K => z′)^[i] b
          = algebraMap ℂ K (a i) * GaloisForLFunctions.differentialJet i b := by
      intro i hi
      have hine : i ≠ n := by
        simp only [Finset.mem_range] at hi
        omega
      rw [differentialJet_eq_iterate, hA]
      simp [hine]
    rw [Finset.sum_congr rfl hlow, ← ha, ← differentialJet_eq_iterate]
    simp
  exact hnodef (defect_of_operator_defect hd hx sigma hsig hdx hdc hb (zero_mem _)
    (by rw [hAn]; norm_num) hsum)

/-- **The exact dichotomy over an inert coefficient field.**  For `b` rational, every solution of
`sigma y = y + b` is hypertranscendental over `F` **if and only if** `b` is not itself a translation
defect of `C(x)`.  The size of `F` is irrelevant: only inertness is used. -/
theorem graded_hypertranscendental_iff {d : ℂ} (hd : d ≠ 0) {x : K} (hx : Transcendental ℂ x)
    (sigma : K ≃ₐ[ℂ] K) (hsig : sigma x = x + 1)
    (hdx : (x)′ = algebraMap ℂ K d) (hdc : ∀ a : ℂ, (algebraMap ℂ K a)′ = 0)
    (hsigd : ∀ u : K, sigma (u′) = (sigma u)′)
    (F : IntermediateField ℂ K) (hxF : coordBase x ≤ F)
    (hFstab : ∀ u : K, sigma u ∈ F ↔ u ∈ F)
    (hfixF : ∀ u ∈ F, sigma u = u → ∃ a : ℂ, u = algebraMap ℂ K a)
    (hinert : ∀ u ∈ F, ∀ v ∈ coordBase x, sigma u - u = v →
      ∃ R ∈ coordBase x, sigma R - R = v)
    {b : K} (hb : b ∈ coordBase x) :
    (∀ y : K, sigma y = y + b → GaloisForLFunctions.HypertranscendentalOver (F : Type _) y)
      ↔ ¬ ∃ R ∈ coordBase x, sigma R - R = b := by
  constructor
  · rintro hall ⟨R, hR, hRdef⟩
    exact hall R (by linear_combination hRdef)
      (GaloisForLFunctions.HTGeometry.differentialAlgebraicOver_algebraMap
        (F := (F : Type _)) (E := K) ⟨R, hxF hR⟩)
  · intro hnodef y hy
    have hjet : ∀ n, sigma (GaloisForLFunctions.differentialJet n y)
        = GaloisForLFunctions.differentialJet n y + GaloisForLFunctions.differentialJet n b := by
      intro n
      induction n with
      | zero => simpa using hy
      | succ n ih =>
          rw [GaloisForLFunctions.differentialJet_succ n y, hsigd, ih, Derivation.map_add,
            GaloisForLFunctions.differentialJet_succ n b]
    have hcrat : ∀ v ∈ defectSpanAll (fun n => GaloisForLFunctions.differentialJet n b),
        v ∈ coordBase x :=
      defectSpanAll_le_of_mem fun n => jet_mem_coordBase hx hdx hdc hb n
    have hfree := jetTower_transcendental sigma F
      (fun n => GaloisForLFunctions.differentialJet n y)
      (fun n => GaloisForLFunctions.differentialJet n b)
      hFstab (fun n => hxF (jet_mem_coordBase hx hdx hdc hb n)) hjet hfixF
      (fun u hu v hv hduv => by
        by_cases hv0 : v = 0
        · exact hv0
        · obtain ⟨R, hR, hRdef⟩ := hinert u hu v (hcrat v hv) hduv
          exact defect_eq_zero_of_not_defect hd hx sigma hsig hdx hdc hb hnodef hR hv hRdef)
      (jet_not_mem_defectSpan_of_not_defect hd hx sigma hsig hdx hdc hb hnodef)
    have hind := algebraicIndependent_of_jetTower_transcendental F
      (fun n => GaloisForLFunctions.differentialJet n y) hfree
    rw [GaloisForLFunctions.hypertranscendentalOver_iff_differentialIndependent_singleton]
    have hinj : Function.Injective (fun p : Unit × ℕ => p.2) := by
      rintro ⟨u1, m⟩ ⟨u2, k⟩ h
      simp only at h
      subst h
      rfl
    exact hind.comp (fun p : Unit × ℕ => p.2) hinj

end HTGeometry
