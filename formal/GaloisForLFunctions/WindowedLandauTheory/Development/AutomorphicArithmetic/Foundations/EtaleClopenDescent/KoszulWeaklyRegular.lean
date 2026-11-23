import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulContraction
import Mathlib.RingTheory.Regular.RegularSequence

/-! A weakly regular sequence in the ideal of the weights gives exact
Koszul cochains below the length of that sequence. -/

noncomputable section

open scoped Pointwise

namespace GlobalTheory.WH

variable {R ι M N : Type*} [CommRing R] [LinearOrder ι]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Koszul cochain differential with weights acting by scalar multiplication. -/
def koszulDifferential (r : ι → R) : Module.End R (Finset ι → M) :=
  wd (fun i => Algebra.lsmul R R M (r i))

theorem koszulDifferential_apply (r : ι → R) (a : Finset ι → M) (t : Finset ι) :
    koszulDifferential r a t = ∑ i ∈ t, cubeSign t i • (r i • a (t.erase i)) :=
  wd_apply _ _ _

private theorem koszulDifferential_sq (r : ι → R) (a : Finset ι → M) :
    koszulDifferential r (koszulDifferential r a) = 0 :=
  wd_wd _ (fun i j => (Commute.all (r i) (r j)).map (Algebra.lsmul R R M)) a

private theorem koszulDifferential_map (r : ι → R) (f : M →ₗ[R] N) (a : Finset ι → M)
    (t : Finset ι) : koszulDifferential r (fun s => f (a s)) t = f (koszulDifferential r a t) := by
  simp only [koszulDifferential_apply, map_sum, map_zsmul, map_smul]

private theorem koszulDifferential_support (r : ι → R) {n : ℤ} {a : Finset ι → M}
    (ha : ∀ t : Finset ι, (t.card : ℤ) ≠ n → a t = 0) (t : Finset ι)
    (ht : (t.card : ℤ) ≠ n + 1) : koszulDifferential r a t = 0 := by
  rw [koszulDifferential_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hc := Finset.card_erase_add_one hi
  rw [ha _ (by omega), smul_zero, smul_zero]

/-- Every scalar in the ideal of the weights kills Koszul cohomology
in its given degree. -/
theorem exists_koszul_primitive_smul (r : ι → R) {n : ℤ} {a : Finset ι → M}
    (ha : ∀ t : Finset ι, (t.card : ℤ) ≠ n → a t = 0) (hz : koszulDifferential r a = 0)
    {g : R} (hg : g ∈ Ideal.span (Set.range r)) :
    ∃ b : Finset ι → M, (∀ t, (t.card : ℤ) ≠ n - 1 → b t = 0) ∧
      koszulDifferential r b = g • a := by
  let P : Submodule R R :=
    { carrier := {g | ∃ b : Finset ι → M, (∀ t, (t.card : ℤ) ≠ n - 1 → b t = 0) ∧
          koszulDifferential r b = g • a}
      zero_mem' := ⟨0, fun _ _ => rfl, by rw [map_zero, zero_smul]⟩
      add_mem' := by
        rintro v w ⟨p, hp, hdp⟩ ⟨q, hq, hdq⟩
        exact ⟨p + q, fun t ht => (Pi.add_apply p q t).trans (by rw [hp t ht, hq t ht, add_zero]),
          by rw [map_add, hdp, hdq, add_smul]⟩
      smul_mem' := by
        rintro c v ⟨p, hp, hdp⟩
        exact ⟨c • p, fun t ht => (Pi.smul_apply c p t).trans (by rw [hp t ht, smul_zero]),
          by rw [map_smul, hdp, smul_smul, smul_eq_mul]⟩ }
  have hle : Ideal.span (Set.range r) ≤ P := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    refine ⟨koszulContraction (k := R) i a, koszulContraction_support (k := R) i ha, ?_⟩
    have e := koszulContraction_wd (fun i => Algebra.lsmul R R M (r i)) i a
    change koszulContraction (k := R) i (koszulDifferential r a) +
      koszulDifferential r (koszulContraction (k := R) i a) = (r i) • a at e
    rwa [hz, map_zero, zero_add] at e)
  exact hle hg

/-- Exactness below the length of a weakly regular sequence in the
weight ideal follows by passing to each successive quotient. -/
theorem koszul_exact_of_weaklyRegular (r : ι → R) (l : List R)
    (hl : ∀ g ∈ l, g ∈ Ideal.span (Set.range r)) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M], RingTheory.Sequence.IsWeaklyRegular M l →
      ∀ (n : ℤ), n < l.length → ∀ a : Finset ι → M,
        (∀ t, (t.card : ℤ) ≠ n → a t = 0) → koszulDifferential r a = 0 →
        ∃ b : Finset ι → M, (∀ t, (t.card : ℤ) ≠ n - 1 → b t = 0) ∧ koszulDifferential r b = a := by
  induction l with
  | nil =>
    intro M _ _ _ n hn a ha _
    have hzero : a = 0 := funext fun t => ha t (by
      have hcard : (0 : ℤ) ≤ t.card := Int.natCast_nonneg _
      simp only [List.length_nil, Nat.cast_zero] at hn
      omega)
    exact ⟨0, fun _ _ => rfl, (map_zero _).trans hzero.symm⟩
  | cons g l ih =>
    intro M _ _ hreg n hn a ha hza
    obtain ⟨hg, hreg'⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff M g l).mp hreg
    obtain ⟨y, hy, hdy⟩ := exists_koszul_primitive_smul r ha hza (hl g List.mem_cons_self)
    let Q := QuotSMulTop g M
    let π : M →ₗ[R] Q := Submodule.mkQ _
    have hker (v : M) : π v = 0 ↔ ∃ w : M, g • w = v := by
      change Submodule.Quotient.mk v = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      simp only [Submodule.mem_top, true_and]
    have hyq (t : Finset ι) (ht : (t.card : ℤ) ≠ n - 1) : π (y t) = 0 := by rw [hy t ht, map_zero]
    have hzy : koszulDifferential r (fun t => π (y t)) = 0 := by
      funext t
      rw [koszulDifferential_map, hdy]
      exact (hker _).mpr ⟨a t, rfl⟩
    obtain ⟨z, hz, hdz⟩ := ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) Q hreg'
      (n - 1) (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hn; omega)
      (fun t => π (y t)) hyq hzy
    have hpre (t : Finset ι) : ∃ v : M, π v = z t ∧ (z t = 0 → v = 0) := by
      by_cases ht : z t = 0
      · exact ⟨0, (map_zero _).trans ht.symm, fun _ => rfl⟩
      · obtain ⟨v, hv⟩ := (Submodule.mkQ_surjective (g • (⊤ : Submodule R M))) (z t)
        exact ⟨v, hv, fun e => (ht e).elim⟩
    choose v hv hv0 using hpre
    have hvs (t : Finset ι) (ht : (t.card : ℤ) ≠ n - 1 - 1) : v t = 0 := hv0 t (hz t ht)
    have hdiv (t : Finset ι) : ∃ w : M, g • w = y t - koszulDifferential r v t := by
      apply (hker _).mp
      rw [map_sub, ← koszulDifferential_map, funext hv, hdz, sub_self]
    choose b hb using hdiv
    refine ⟨b, fun t ht => hg ?_, ?_⟩
    · change g • b t = g • (0 : M)
      rw [hb, hy t ht, koszulDifferential_support r hvs t (by omega), sub_zero, smul_zero]
    · funext t
      apply hg
      change g • koszulDifferential r b t = g • a t
      have he : g • b = y - koszulDifferential r v := funext hb
      rw [← Pi.smul_apply, ← map_smul, he, map_sub, koszulDifferential_sq, sub_zero, hdy, Pi.smul_apply]

end GlobalTheory.WH
