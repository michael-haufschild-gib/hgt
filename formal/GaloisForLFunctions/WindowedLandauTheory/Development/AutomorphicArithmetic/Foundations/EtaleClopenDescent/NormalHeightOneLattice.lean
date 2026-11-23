import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! Divisibility and projective lattice membership over a normal
Noetherian domain are detected in codimension one. -/

noncomputable section

namespace GlobalTheory.PD

section Ring

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

private theorem height_eq_one_of_forall_mem_iff_dvd {p : Ideal A} [hp : p.IsPrime] {a b : A} (ha : a ≠ 0)
    (h : ∀ r, r ∈ p ↔ a ∣ r * b) : p.height = 1 := by
  have hap : a ∈ p := (h a).mpr (dvd_mul_right a b)
  let K := FractionRing A
  have ha' : algebraMap A K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  obtain ⟨y, hy, k, hk, hyk⟩ : ∃ y ∈ p, ∃ k, k ∉ p ∧ y * b = a * k := by
    by_contra! hnone
    have hint := isIntegral_of_smul_mem_submodule (A := K)
      (Submodule.map (Algebra.linearMap A K) p) ?_ ?_ (algebraMap A K b / algebraMap A K a) ?_
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
      refine hp.ne_top ((Ideal.eq_top_iff_one p).mpr ((h 1).mpr ⟨y, ?_⟩))
      apply IsFractionRing.injective A K
      rw [one_mul, map_mul, e, mul_div_cancel₀ _ ha']
    · rw [Submodule.ne_bot_iff]
      exact ⟨_, ⟨a, hap, rfl⟩, ha'⟩
    · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨k, hk⟩ := (h m).mp hm
      refine ⟨k, by_contra fun hkp => hnone m hm k hkp hk, ?_⟩
      change algebraMap A K k = algebraMap A K b / algebraMap A K a * algebraMap A K m
      rw [div_mul_eq_mul_div, ← map_mul, mul_comm b, hk, map_mul, mul_div_cancel_left₀ _ ha']
  have hmin : p ∈ (Ideal.span {y}).minimalPrimes := by
    refine ⟨⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr hy⟩, ?_⟩
    rintro q ⟨hq, hyq⟩ hqp m hm
    obtain ⟨k', hk'⟩ := (h m).mp hm
    have e : k * m = y * k' := by
      apply mul_left_cancel₀ ha
      linear_combination y * hk' - m * hyk
    have : k * m ∈ q := e ▸ q.mul_mem_right _ ((Ideal.span_singleton_le_iff_mem q).mp hyq)
    exact (hq.mem_or_mem this).resolve_left fun hkq => hk (hqp hkq)
  refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hmin) ?_
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  rintro rfl
  exact ha hap

private theorem height_eq_one_of_mem_associatedPrimes {a : A} (ha : a ≠ 0) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})) : p.height = 1 := by
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine height_eq_one_of_forall_mem_iff_dvd (b := b) ha fun r => ?_
  rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

/-- A divisor can be tested in the local rings at the height-one primes. -/
theorem dvd_of_forall_height_one {a b : A} (ha : a ≠ 0)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 → ∃ s, s ∉ p ∧ a ∣ s * b) : a ∣ b := by
  by_contra hab
  have hb : Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hb
  letI := hp.1
  obtain ⟨s, hs, hsb⟩ := h p (height_eq_one_of_mem_associatedPrimes ha hp)
  refine hs (hle ?_)
  rwa [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

end Ring

section Lattice

variable {A M V : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Module.Projective A M]
  [AddCommGroup V] [Module A V]

private theorem exists_smul_eq_of_dual_dvd {a : A} {m : M}
    (h : ∀ φ : Module.Dual A M, a ∣ φ m) : ∃ m', a • m' = m := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  choose c hc using fun i : M => h (Finsupp.lapply i ∘ₗ s)
  refine ⟨∑ i ∈ (s m).support, c i • i, ?_⟩
  conv_rhs => rw [← hs m, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Module.IsTorsionFree A V]

/-- A vector with a common denominator belongs to the projective
lattice if it belongs after localization at every height-one prime. -/
theorem mem_range_of_forall_height_one_of_projective (f : M →ₗ[A] V) (hf : Function.Injective f)
    {v : V} {a : A} (ha : a ≠ 0) (hav : a • v ∈ LinearMap.range f)
    (h : ∀ (p : Ideal A) [p.IsPrime], p.height = 1 →
      ∃ s, s ∉ p ∧ s • v ∈ LinearMap.range f) : v ∈ LinearMap.range f := by
  obtain ⟨m, hm⟩ := hav
  obtain ⟨m', hm'⟩ := exists_smul_eq_of_dual_dvd (m := m) (a := a) fun φ =>
    dvd_of_forall_height_one ha fun p _ hp => by
      obtain ⟨s, hs, n, hn⟩ := h p hp
      refine ⟨s, hs, φ n, ?_⟩
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul]
      congr 1
      apply hf
      rw [map_smul, map_smul, hm, hn, smul_comm]
  refine ⟨m', smul_right_injective V ha ?_⟩
  change a • f m' = a • v
  rw [← map_smul, hm', hm]

end Lattice

end GlobalTheory.PD
