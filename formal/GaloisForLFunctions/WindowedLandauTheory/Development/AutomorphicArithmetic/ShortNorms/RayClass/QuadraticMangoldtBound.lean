import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.IdealCoefficients
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.NormOne

/-! Quadratic-field prime-power weights are bounded by twice the rational von Mangoldt weight. -/

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LamRay

variable {K : Type} [Field K] [NumberField K]

theorem lamIdeal_nonneg (I : Ideal (𝓞 K)) : 0 ≤ lamIdeal I := by
  unfold lamIdeal
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

theorem pow_prime_norm {P : Ideal (𝓞 K)} {k : ℕ} (hP : P.IsPrime) (h0 : P ≠ ⊥)
    (hk : 1 ≤ k) : IsPrimePow (Ideal.absNorm (P ^ k)) ∧
      P ∣ Ideal.span {((Ideal.absNorm (P ^ k)).minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm P := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hP, h0⟩
  letI : P.IsMaximal := hP.isMaximal h0
  obtain ⟨p, i, hi, hm, hp, he⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  have hd : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have h1 : 1 < Ideal.absNorm P := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hik : i * k ≠ 0 := mul_ne_zero hi.ne' (by omega)
  rw [map_pow, he, ← pow_mul, hp.pow_minFac hik]
  exact ⟨(isPrimePow_nat_iff _).2 ⟨p, i * k, hp, Nat.pos_of_ne_zero hik, rfl⟩, hd, he ▸ h1⟩

theorem sum_lamIdeal_le (hK : Module.finrank ℚ K = 2) (n : ℕ) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ I ∈ S, Ideal.absNorm I = n) : ∑ I ∈ S, lamIdeal I ≤ 2 * Λ n := by
  set T := S.filter (fun I => ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) with hT
  have e : ∑ I ∈ S, lamIdeal I = ∑ I ∈ T, Real.log (Ideal.absNorm I.radical) := by
    rw [hT, Finset.sum_filter]
    rfl
  rw [e]
  rcases T.eq_empty_or_nonempty with h | ⟨I₀, hI₀⟩
  · rw [h, Finset.sum_empty]
    exact mul_nonneg zero_le_two vonMangoldt_nonneg
  have key : ∀ I ∈ T, IsPrimePow n ∧ I.radical.IsPrime ∧ I.radical ≠ ⊥ ∧
      I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm I.radical ∧ ∃ k, I = I.radical ^ k := by
    intro I hI
    obtain ⟨hIS, P, k, hP, h0, hk, rfl⟩ := Finset.mem_filter.1 hI
    have h := pow_prime_norm hP h0 hk
    rw [hS _ hIS] at h
    rw [Ideal.radical_pow _ (by omega), hP.radical]
    exact ⟨h.1, hP, h0, h.2.1, h.2.2, k, rfl⟩
  have hn := (key I₀ hI₀).1
  have hp : n.minFac.Prime := Nat.minFac_prime hn.ne_one
  have hdvd : ∏ I ∈ T, I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime (fun I hI J hJ hIJ => ?_) (fun I hI => (key I hI).2.2.2.1)
    obtain ⟨-, a1, a2, -, a3, k, a4⟩ := key I hI
    obtain ⟨-, b1, b2, -, -, l, b4⟩ := key J hJ
    refine Ideal.isCoprime_iff_sup_eq.2 ((a1.isMaximal a2).coprime_of_ne (b1.isMaximal b2) fun h => hIJ ?_)
    have c1 := hS I (Finset.mem_filter.1 hI).1
    have c2 := hS J (Finset.mem_filter.1 hJ).1
    rw [a4, map_pow] at c1
    rw [b4, map_pow, ← h] at c2
    have := Nat.pow_right_injective a3 (c1.trans c2.symm)
    rw [a4, b4, ← h, this]
  have h2 : ∏ I ∈ T, Ideal.absNorm I.radical ∣ n.minFac ^ 2 := by
    have := map_dvd Ideal.absNorm hdvd
    rwa [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at this
  have h3 : ((∏ I ∈ T, Ideal.absNorm I.radical : ℕ) : ℝ) ≤ (n.minFac ^ 2 : ℕ) :=
    Nat.cast_le.2 (Nat.le_of_dvd (pow_pos hp.pos 2) h2)
  have hpos : ∀ I ∈ T, (0 : ℝ) < Ideal.absNorm I.radical := fun I hI =>
    Nat.cast_pos.2 (lt_trans one_pos (key I hI).2.2.2.2.1)
  push_cast at h3
  rw [← Real.log_prod (fun I hI => (hpos I hI).ne'), vonMangoldt_apply, if_pos hn]
  have h4 := Real.log_le_log (Finset.prod_pos hpos) h3
  rw [Real.log_pow] at h4
  exact_mod_cast h4

theorem normOne_span {d M : ℕ} {ω : 𝓞 K} (hgen : ∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω)
    (hnorm : ∀ a b : ℤ,
      Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2)
    {π : 𝓞 K} (hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    GlobalTheory.Mem.An.NormOne d M (Ideal.absNorm (Ideal.span {π})) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨a, b, rfl⟩ := hgen z
  have e : π = ((1 + M * a : ℤ) : 𝓞 K) + ((M * b : ℤ) : 𝓞 K) * ω := by
    push_cast
    linear_combination -hz
  have hn := hnorm (1 + M * a) (M * b)
  rw [← e] at hn
  have h0 : 0 ≤ Algebra.norm ℤ π := by
    have : 0 ≤ (2 * (1 + (M : ℤ) * a) + M * b) ^ 2 + d * ((M : ℤ) * b) ^ 2 := by positivity
    linarith
  refine ⟨2 * (1 + M * a) + M * b, M * b, ?_, Dvd.intro _ rfl, ⟨a, by ring⟩⟩
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg h0]
  linarith

theorem lamRay_props {d M : ℕ} (D : RayData K M) (hK : Module.finrank ℚ K = 2)
    (ω : 𝓞 K) (hgen : ∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω)
    (hnorm : ∀ a b : ℤ,
      Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2) :
    (∀ g n, 0 ≤ lamRay D g n) ∧ (∀ n : ℕ, ∑ g : D.G, lamRay D g n ≤ 2 * Λ n) ∧
    ∀ p : ℕ, p.Prime → lamRay D 1 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  refine ⟨fun g n => ?_, fun n => ?_, fun p _ h => ?_⟩
  · exact finsum_nonneg fun I => finsum_nonneg fun _ => lamIdeal_nonneg I
  · have e : ∀ g, lamRay D g n = ∑ I ∈ (RayCount.idealsIn_finite D g n).toFinset, lamIdeal I := fun g =>
      finsum_mem_eq_finite_toFinset_sum _ _
    simp only [e]
    rw [← Finset.sum_biUnion]
    · refine sum_lamIdeal_le hK n _ fun I hI => ?_
      obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.1 hI
      exact ((Set.Finite.mem_toFinset _).1 hg).2.2.1
    · intro g _ g' _ hgg
      refine Finset.disjoint_left.2 fun I h1 h2 => hgg ?_
      exact ((Set.Finite.mem_toFinset _).1 h1).2.2.2.symm.trans ((Set.Finite.mem_toFinset _).1 h2).2.2.2
  · have hne : (idealsIn D 1 p).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h0
      apply h
      unfold lamRay
      rw [h0, finsum_mem_empty]
    obtain ⟨I, h0, hc, hN, hcl⟩ := hne
    obtain ⟨π, hI, hπ⟩ := (D.cls_eq_one_iff hc h0).mp hcl
    rw [← hN, hI]
    exact normOne_span hgen hnorm hπ

end GlobalTheory.Hk.LamRay
