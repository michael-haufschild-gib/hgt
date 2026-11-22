import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.IdealCoefficients
import GaloisForLFunctions.ArtinMertens.TheIdealVonMangoldtIdentity

/-! The log of an ideal norm is the sum of the von Mangoldt weights of its divisors. -/

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.RayConv

variable {K : Type} [Field K] [NumberField K]

theorem finite_dvd {I : Ideal (𝓞 K)} (hI : I ≠ 0) : {J : Ideal (𝓞 K) | J ∣ I}.Finite := by
  refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (Ideal.absNorm I)).subset fun J hJ => ?_
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)) (map_dvd _ hJ)

/-- Reindex the native prime-power identity by the prime-power ideals dividing `I`. -/
theorem sum_lamIdeal (I : Ideal (𝓞 K)) : I ≠ 0 → ∀ T : Finset (Ideal (𝓞 K)), (∀ J, J ∈ T ↔ J ∣ I) →
    ∑ J ∈ T, lamIdeal J = Real.log (Ideal.absNorm I) := by
  classical
  intro hI T hT
  let good (J : Ideal (𝓞 K)) : Prop :=
    ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ J = P ^ k
  let U := (GaloisForLFunctions.ArtinMertens.primePowersLe K (Ideal.absNorm I)).filter
    (fun pk => pk.1 ^ pk.2 ∣ I)
  have hU {P : Ideal (𝓞 K)} {k : ℕ} : (P, k) ∈ U ↔
      (P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ Ideal.absNorm P ^ k ≤ Ideal.absNorm I) ∧ P ^ k ∣ I := by
    simp only [U, Finset.mem_filter, GaloisForLFunctions.ArtinMertens.mem_primePowersLe]
  have hfilter : ∑ J ∈ T, lamIdeal J = ∑ J ∈ T.filter good, lamIdeal J := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun J _ => ?_
    by_cases hJ : good J
    · rw [if_pos hJ]
    · rw [if_neg hJ, RayCount.lamIdeal_of_not_prime_pow hJ]
  have hsum : (∑ pk ∈ U, Real.log (Ideal.absNorm pk.1)) = ∑ J ∈ T.filter good, lamIdeal J := by
    refine Finset.sum_bij (fun pk _ => pk.1 ^ pk.2) ?_ ?_ ?_ ?_
    · rintro ⟨P, k⟩ hp
      obtain ⟨⟨hP, hP0, hk, -⟩, hdiv⟩ := hU.mp hp
      exact Finset.mem_filter.mpr ⟨(hT _).mpr hdiv, P, k, hP, hP0, hk, rfl⟩
    · rintro ⟨P, k⟩ hp ⟨Q, j⟩ hq he
      obtain ⟨⟨hP, hP0, hk, -⟩, -⟩ := hU.mp hp
      obtain ⟨⟨hQ, hQ0, -, -⟩, -⟩ := hU.mp hq
      have hdiv : P ∣ Q := ((Ideal.prime_iff_isPrime hP0).mpr hP).dvd_of_dvd_pow
        (he ▸ dvd_pow_self P (by omega : k ≠ 0))
      have hPQ := (hQ.isMaximal hQ0).eq_of_le hP.ne_top (Ideal.dvd_iff_le.mp hdiv)
      subst Q
      have h2 := GaloisForLFunctions.ArtinMertens.two_le_absNorm_of_isPrime hP hP0
      have heN : Ideal.absNorm P ^ k = Ideal.absNorm P ^ j := by
        simpa only [map_pow] using congrArg (Ideal.absNorm (S := 𝓞 K)) he
      exact congrArg (Prod.mk P) (pow_right_injective₀
        (a := Ideal.absNorm P) (by omega) (by omega) heN)
    · intro J hJ
      obtain ⟨hJT, P, k, hP, hP0, hk, rfl⟩ := Finset.mem_filter.mp hJ
      have hdiv := (hT _).mp hJT
      have hN : Ideal.absNorm P ^ k ≤ Ideal.absNorm I := by
        rw [← map_pow]
        exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
          (map_dvd _ hdiv)
      exact ⟨(P, k), hU.mpr ⟨⟨hP, hP0, hk, hN⟩, hdiv⟩, rfl⟩
    · rintro ⟨P, k⟩ hp
      obtain ⟨⟨hP, hP0, hk, -⟩, -⟩ := hU.mp hp
      exact (RayCount.lamIdeal_prime_pow P hP hP0 k hk).symm
  refine hfilter.trans (hsum.symm.trans ?_)
  simpa only [U, Finset.sum_filter] using
    GaloisForLFunctions.ArtinMertens.sum_primePowersLe_dvd_eq hI le_rfl

theorem aRay_mul_log : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (g : D.G) (n : ℕ), aRay D g n * Real.log n = ∑ h : D.G, ∑ p ∈ n.divisorsAntidiagonal, lamRay D h p.1 * aRay D (g / h) p.2 := by
  intro K _ _ M _ D g n
  let F : D.G → ℕ → Finset (Ideal (𝓞 K)) := fun g n => (RayCount.idealsIn_finite D g n).toFinset
  have hF : ∀ g n I, I ∈ F g n ↔ I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ Ideal.absNorm I = n ∧ D.cls I = g :=
    fun g n I => by simp [F, idealsIn]
  have ha : ∀ g n, aRay D g n = (F g n).card := fun g n => by
    unfold aRay; rw [Set.ncard_eq_toFinset_card _ (RayCount.idealsIn_finite D g n)]
  have hl : ∀ g n, lamRay D g n = ∑ I ∈ F g n, lamIdeal I := fun g n => by
    unfold lamRay; rw [finsum_mem_eq_finite_toFinset_sum _ (RayCount.idealsIn_finite D g n)]
  let T : Ideal (𝓞 K) → Finset (Ideal (𝓞 K)) := fun I => if h : I = 0 then ∅ else (finite_dvd h).toFinset
  have hT : ∀ I, I ≠ 0 → ∀ J, J ∈ T I ↔ J ∣ I := fun I hI J => by
    simp only [T]; rw [dif_neg hI]; simp
  have L : aRay D g n * Real.log n = ∑ I ∈ F g n, ∑ J ∈ T I, lamIdeal J := by
    rw [ha, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun I hI => ?_
    have := (hF _ _ _).1 hI
    rw [sum_lamIdeal I this.1 _ (hT I this.1), this.2.2.1]
  have R : ∀ h (p : ℕ × ℕ), lamRay D h p.1 * aRay D (g / h) p.2 =
      ∑ q ∈ F h p.1 ×ˢ F (g / h) p.2, lamIdeal q.1 := fun h p => by
    rw [hl, ha, Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp [mul_comm]
  simp only [R]
  rw [L, Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => ⟨x.2.1 * x.2.2, x.2.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨⟨h, p⟩, I, J⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx ⊢
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    refine ⟨⟨mul_ne_zero a1 b1, a2.mul_left b2, by rw [map_mul, a3, b3, hp], ?_⟩,
      (hT _ (mul_ne_zero a1 b1) _).2 (dvd_mul_right _ _)⟩
    rw [D.cls_mul I J a2 b2 a1 b1, a4, b4]
    exact mul_div_cancel h g
  · rintro ⟨⟨h, p, p'⟩, I, J⟩ hx ⟨⟨h', q, q'⟩, I', J'⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal] at hx hy
    obtain ⟨⟨-, hp, -⟩, ⟨a1, a2, a3, a4⟩, b1, b2, b3, b4⟩ := hx
    obtain ⟨⟨-, hq, -⟩, ⟨c1, c2, c3, c4⟩, d1, d2, d3, d4⟩ := hy
    simp only [Sigma.mk.injEq, heq_eq_eq] at hxy
    obtain ⟨e1, rfl⟩ := hxy
    obtain rfl : J = J' := mul_left_cancel₀ a1 e1
    subst a3 b3 a4 c3 d3 c4
    rfl
  · rintro ⟨I, J⟩ hx
    simp only [Finset.mem_sigma, hF] at hx
    obtain ⟨⟨a1, a2, a3, a4⟩, hJ⟩ := hx
    obtain ⟨J', rfl⟩ := (hT _ a1 _).1 hJ
    have j1 : J ≠ ⊥ := left_ne_zero_of_mul a1
    have j2 : J' ≠ ⊥ := right_ne_zero_of_mul a1
    refine ⟨⟨⟨D.cls J, Ideal.absNorm J, Ideal.absNorm J'⟩, J, J'⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_product, hF, Nat.mem_divisorsAntidiagonal, Finset.mem_univ, true_and, and_true]
    refine ⟨⟨by rw [← map_mul, a3], ?_⟩, ⟨j1, a2.of_mul_left_left⟩, j2, a2.of_mul_left_right, ?_⟩
    · rw [← a3]; exact fun h => a1 (Ideal.absNorm_eq_zero_iff.1 h)
    · rw [← a4, D.cls_mul J J' a2.of_mul_left_left a2.of_mul_left_right j1 j2]
      exact (mul_div_cancel_left (D.cls J) (D.cls J')).symm
  · intro x _; rfl

end GlobalTheory.Hk.RayConv
