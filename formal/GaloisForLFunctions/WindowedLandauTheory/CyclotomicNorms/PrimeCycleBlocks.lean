import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.StatementI

/-! A prime cycle moving more than half the points allows only a one-block
or a singleton partition into invariant blocks of equal size. -/

open Finset

namespace WindowedLandauTheory.CyclotomicNorms

theorem blocks_form_cycle : BlocksCycle := by
  unfold BlocksCycle
  intro G Ω _ _ _ _ B m p g₀ hsize hdisj hcover hinv hp hlt hcyc hsupp
  have hpow : ∀ (i : ℕ) (y : Ω), ((MulAction.toPerm g₀ : Equiv.Perm Ω) ^ i) y = g₀ ^ i • y := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih => intro y; simp [pow_succ, mul_smul, ih]
  have hord : orderOf (MulAction.toPerm g₀ : Equiv.Perm Ω) = p := by
    rw [hcyc.orderOf, hsupp]
  have hfix : ∀ y : Ω, g₀ ^ p • y = y := by
    intro y
    have h1 := pow_orderOf_eq_one (MulAction.toPerm g₀ : Equiv.Perm Ω)
    rw [hord] at h1
    rw [← hpow]
    simp [h1]
  let φ (s : Finset Ω) := s.image (fun x => g₀ • x)
  have hφ : ∀ (i : ℕ) (s : Finset Ω), φ^[i] s = s.image (fun x => g₀ ^ i • x) := by
    intro i
    induction i with
    | zero => intro s; simp
    | succ i ih =>
      intro s
      rw [Function.iterate_succ_apply', ih, show φ _ = Finset.image (fun x => g₀ • x) _ from rfl, Finset.image_image]
      congr 1
      funext y
      simp only [Function.comp_apply, pow_succ', mul_smul]
  have hφB : ∀ (i : ℕ), ∀ s ∈ B, φ^[i] s ∈ B := by
    intro i s hs
    rw [hφ]
    exact hinv (g₀ ^ i) s hs
  have hper : ∀ s : Finset Ω, φ^[p] s = s := by
    intro s
    rw [hφ]
    simp [hfix]
  have hp2 := hp.two_le
  obtain ⟨x, hx⟩ : (MulAction.toPerm g₀ : Equiv.Perm Ω).support.Nonempty := by
    rw [← Finset.card_pos, hsupp]
    omega
  obtain ⟨b, hbB, hxb⟩ := hcover x
  have hcard : Fintype.card Ω = B.card * m := by
    have hU : B.biUnion (fun c => c) = Finset.univ := by
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
      obtain ⟨c, hc, hyc⟩ := hcover y
      exact ⟨c, hc, hyc⟩
    rw [← Finset.card_univ, ← hU, Finset.card_biUnion (fun c hc c' hc' hne => hdisj c hc c' hc' hne)]
    exact Finset.sum_const_nat hsize
  have hmp : Function.minimalPeriod φ b ∣ p :=
    Function.IsPeriodicPt.minimalPeriod_dvd (hper b)
  rcases (Nat.dvd_prime hp).1 hmp with h1 | hpp
  · left
    have hfixb : φ b = b := Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1
    have hsub : (MulAction.toPerm g₀ : Equiv.Perm Ω).support ⊆ b := by
      intro y hy
      obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (Equiv.Perm.mem_support.1 hx) (Equiv.Perm.mem_support.1 hy)
      have hib : φ^[i] b = b := Function.iterate_fixed hfixb i
      rw [← hi, hpow, ← hib, hφ]
      exact Finset.mem_image_of_mem _ hxb
    have hpm : p ≤ m := by
      rw [← hsupp, ← hsize b hbB]
      exact Finset.card_le_card hsub
    have hk1 : 1 ≤ B.card := Finset.card_pos.2 ⟨b, hbB⟩
    by_contra hne
    have hk2 : 2 ≤ B.card := by omega
    have h2 := Nat.mul_le_mul hk2 hpm
    apply (Nat.not_le_of_gt hlt)
    rw [hcard]
    exact h2
  · right
    have hinj : Set.InjOn (fun n => φ^[n] b) (Finset.range p : Set ℕ) := by
      rw [Finset.coe_range, ← hpp]
      exact Function.iterate_injOn_Iio_minimalPeriod
    have hkp : p ≤ B.card := by
      have h1 : ((Finset.range p).image (fun n => φ^[n] b)) ⊆ B := by
        intro c hc
        obtain ⟨n, -, rfl⟩ := Finset.mem_image.1 hc
        exact hφB n b hbB
      have h2 := Finset.card_le_card h1
      rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at h2
    have hm1 : 1 ≤ m := by
      rw [← hsize b hbB]
      exact Finset.card_pos.2 ⟨x, hxb⟩
    have hm : m = 1 := by
      by_contra hne
      have hm2 : 2 ≤ m := by omega
      have h3 := Nat.mul_le_mul hkp hm2
      apply (Nat.not_le_of_gt hlt)
      rw [hcard]
      simpa only [Nat.mul_comm p 2] using h3
    rw [hcard, hm, mul_one]


/-- An element whose cycle type contains a prime larger than half the degree
has a power acting by a single cycle of that prime length. -/
theorem exists_power_prime_cycle {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (σ : Equiv.Perm Ω) {p : ℕ} (hp : p.Prime) (hmem : p ∈ σ.cycleType)
    (hcard : Fintype.card Ω < 2 * p) :
    ∃ k : ℕ, (σ ^ k).IsCycle ∧ (σ ^ k).support.card = p := by
  have hdvd : p ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hmem
  let k := orderOf σ / p
  have hord : orderOf (σ ^ k) = p := orderOf_pow_orderOf_div (orderOf_pos σ).ne' hdvd
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := σ ^ k) (hord ▸ hp)
  rw [hord] at hn
  have hsum : (σ ^ k).support.card = (n + 1) * p := by
    rw [← Equiv.Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul]
  have hle := Finset.card_le_univ (σ ^ k).support
  have hn₀ : n = 0 := by
    by_contra h
    have h' : 2 * p ≤ (n + 1) * p := Nat.mul_le_mul_right p (by omega)
    rw [hsum] at hle
    exact (Nat.not_le_of_gt hcard) (h'.trans hle)
  subst n
  refine ⟨k, ?_, by simpa only [zero_add, one_mul] using hsum⟩
  rw [← Equiv.Perm.card_cycleType_eq_one, hn]
  simp

end WindowedLandauTheory.CyclotomicNorms
