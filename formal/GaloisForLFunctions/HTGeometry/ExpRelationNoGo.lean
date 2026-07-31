import GaloisForLFunctions.HTGeometry.SymmetricSumOverRoots

/-!
# No integer relation between one and the exponentials of a conjugate set

If `h : ℤ[X]` is monic with nonzero constant term, then for no nonzero integer `b` can
`b + ∑_{r} exp r` vanish, the sum being over the complex roots of `h` with multiplicity.

This is the core of the Lindemann–Weierstrass argument.  The analytic estimate
`LindemannWeierstrass.exp_polynomial_approx` produces, for each large prime `p`, an integer `nₚ` not
divisible by `p` and an integer polynomial `gₚ` approximating `nₚ · exp` at every root.  Summing the
errors over the roots gives an integer congruent to `−b·nₚ` modulo `p`, hence nonzero, hence of
absolute value at least one — while the estimate bounds it by `(deg h) · cᵖ / (p−1)!`, which tends to
zero.  The integrality of the sum of `gₚ` over the roots is `sum_aeval_aroots_isInt`.

* `no_int_exp_relation` — the no-go.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Filter Finset Topology
open scoped Nat

/-- **No nonzero integer is cancelled by an integer combination of conjugate-set exponential sums.**
This is the Lindemann–Weierstrass core: the coefficients are constant on each conjugate set, which is
what the symmetrisation of a single algebraic relation produces. -/
theorem no_int_grouped_exp_relation {k : ℕ} {H : Fin k → ℤ[X]} (hm : ∀ j, (H j).Monic)
    (h0 : (∏ j, H j).eval 0 ≠ 0) (β : Fin k → ℤ) {b : ℤ} (hb : b ≠ 0) :
    (b : ℂ) + ∑ j, (β j : ℂ) * ((((H j).aroots ℂ)).map Complex.exp).sum ≠ 0 := by
  intro hrel
  set F : ℤ[X] := ∏ j, H j with hF
  have hFm : F.Monic := monic_prod_of_monic _ _ fun j _ => hm j
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx F h0
  -- every root of a factor is a root of the product
  have hsub : ∀ j : Fin k, ((H j).aroots ℂ) ≤ F.aroots ℂ := by
    intro j
    have hmapne : (F.map (algebraMap ℤ ℂ)) ≠ 0 := (hFm.map (algebraMap ℤ ℂ)).ne_zero
    have hmapprod : F.map (algebraMap ℤ ℂ) = ∏ i, (H i).map (algebraMap ℤ ℂ) := by
      rw [hF, Polynomial.map_prod]
    have hroots : (F.map (algebraMap ℤ ℂ)).roots
        = ∑ i, ((H i).map (algebraMap ℤ ℂ)).roots := by
      rw [hmapprod]
      exact Polynomial.roots_prod _ _ (by rwa [← hmapprod])
    rw [Polynomial.aroots, Polynomial.aroots, hroots]
    exact Finset.single_le_sum (f := fun i => ((H i).map (algebraMap ℤ ℂ)).roots)
      (fun i _ => Multiset.zero_le _) (Finset.mem_univ j)
  set K : ℝ := ∑ j, |(β j : ℝ)| * (Multiset.card (((H j).aroots ℂ)) : ℝ) with hK
  have hKnn : 0 ≤ K := Finset.sum_nonneg fun j _ => by positivity
  have hlim : Tendsto (fun m : ℕ => K * (|c| * (|c| ^ m / m !))) atTop (𝓝 0) := by
    have h1 := (FloorSemiring.tendsto_pow_div_factorial_atTop (|c|)).const_mul (|c|)
    simpa using h1.const_mul K
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < 1 by norm_num) hlim)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes
    (max (max ((F.eval 0).natAbs + 1) (b.natAbs + 1)) (N + 1))
  have hp1 : (F.eval 0).natAbs < p := by omega
  have hp2 : b.natAbs < p := by omega
  have hp3 : N ≤ p - 1 := by omega
  obtain ⟨np, hnp, gp, -, hgp⟩ := hc p hp1 hp
  have hfacpos : (0 : ℝ) < ((p - 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_pos (p - 1)
  -- the integer sums over each conjugate set
  have hGex : ∀ j : Fin k, ∃ z : ℤ,
      (((H j).aroots ℂ).map (fun r => Polynomial.aeval r gp)).sum = (z : ℂ) :=
    fun j => sum_aeval_aroots_isInt (hm j) gp
  choose G hG using hGex
  obtain ⟨Z, hZ⟩ : ∃ z : ℤ, z = b * np + p * ∑ j, β j * G j := ⟨_, rfl⟩
  -- the integer is the total error
  have hsplit : ((Z : ℤ) : ℂ)
      = -∑ j, (β j : ℂ) * ((((H j).aroots ℂ)).map
          (fun r => (np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp))).sum := by
    have hterm : ∀ j : Fin k,
        ((((H j).aroots ℂ)).map
            (fun r => (np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp))).sum
          = (np : ℂ) * ((((H j).aroots ℂ)).map Complex.exp).sum - (p : ℂ) * ((G j : ℤ) : ℂ) := by
      intro j
      rw [Multiset.sum_map_sub, Multiset.sum_map_mul_left, Multiset.sum_map_mul_left, hG j]
    have hsumE : ∑ j, (β j : ℂ) * ((((H j).aroots ℂ)).map Complex.exp).sum = -(b : ℂ) := by
      linear_combination hrel
    have hterm3 : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        (β j : ℂ) * ((((H j).aroots ℂ)).map
            (fun r => (np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp))).sum
          = (np : ℂ) * ((β j : ℂ) * ((((H j).aroots ℂ)).map Complex.exp).sum)
            - (p : ℂ) * ((β j : ℂ) * ((G j : ℤ) : ℂ)) := by
      intro j _
      rw [hterm j]
      ring
    rw [Finset.sum_congr rfl hterm3, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsumE, hZ]
    push_cast
    ring
  -- the estimate bounds it below one
  have hbound : ‖((Z : ℤ) : ℂ)‖ < 1 := by
    rw [hsplit, norm_neg]
    refine lt_of_le_of_lt (norm_sum_le _ _) ?_
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin k)),
        ‖(β j : ℂ) * ((((H j).aroots ℂ)).map
            (fun r => (np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp))).sum‖
          ≤ |(β j : ℝ)| * (Multiset.card (((H j).aroots ℂ)) : ℝ) * (|c| ^ p / ((p - 1)! : ℝ)) := by
      intro j _
      rw [norm_mul]
      have hnormcast : ‖(β j : ℂ)‖ = |(β j : ℝ)| := by simp
      rw [hnormcast, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine le_trans (norm_multiset_sum_le _) ?_
      have hbd : ∀ x ∈ ((((H j).aroots ℂ)).map
          (fun r => (np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp))).map norm,
          x ≤ |c| ^ p / ((p - 1)! : ℝ) := by
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [Multiset.mem_map] at hy
        obtain ⟨r, hr, rfl⟩ := hy
        have hkey := hgp (Multiset.mem_of_le (hsub j) hr)
        have hnorm : ‖(np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp)‖
            ≤ c ^ p / ((p - 1)! : ℝ) := by
          simpa [zsmul_eq_mul, nsmul_eq_mul] using hkey
        refine hnorm.trans ?_
        rw [div_le_div_iff_of_pos_right hfacpos]
        calc c ^ p ≤ |c ^ p| := le_abs_self _
          _ = |c| ^ p := abs_pow c p
      refine le_trans (Multiset.sum_le_card_nsmul _ _ hbd) ?_
      rw [Multiset.card_map, Multiset.card_map, nsmul_eq_mul]
    refine lt_of_le_of_lt (Finset.sum_le_sum hj) ?_
    rw [← Finset.sum_mul, ← hK]
    have hp1' : p - 1 + 1 = p := by omega
    have hpow : |c| ^ p = |c| * |c| ^ (p - 1) := by rw [← pow_succ', hp1']
    rw [hpow, mul_div_assoc]
    exact hN (p - 1) hp3
  -- conclude
  have hZ0 : Z = 0 := by
    have habs : |(Z : ℝ)| < 1 := by simpa using hbound
    have hZabs : |Z| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp hZabs
  have hdvd : (p : ℤ) ∣ b * np := by
    refine ⟨-∑ j, β j * G j, ?_⟩
    rw [hZ] at hZ0
    linarith [hZ0]
  rcases (Int.Prime.dvd_mul' hp hdvd) with hd | hd
  · have hle : (p : ℤ) ≤ |b| := Int.le_of_dvd (abs_pos.mpr hb) ((dvd_abs _ _).mpr hd)
    rw [Int.abs_eq_natAbs] at hle
    omega
  · exact hnp hd

/-- **No nonzero integer is cancelled by the sum of the exponentials of a conjugate set.** -/
theorem no_int_exp_relation {h : ℤ[X]} (hm : h.Monic) (h0 : h.eval 0 ≠ 0) {b : ℤ} (hb : b ≠ 0) :
    (b : ℂ) + ((h.aroots ℂ).map Complex.exp).sum ≠ 0 := by
  intro hrel
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx h h0
  set M : ℕ := Multiset.card (h.aroots ℂ) with hM
  have hlim : Tendsto (fun m : ℕ => (M : ℝ) * (|c| * (|c| ^ m / m !))) atTop (𝓝 0) := by
    have h1 := (FloorSemiring.tendsto_pow_div_factorial_atTop (|c|)).const_mul (|c|)
    simpa using h1.const_mul (M : ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Filter.Tendsto.eventually_lt_const (show (0 : ℝ) < 1 by norm_num) hlim)
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes
    (max (max ((h.eval 0).natAbs + 1) (b.natAbs + 1)) (N + 1))
  have hp1 : (h.eval 0).natAbs < p := by omega
  have hp2 : b.natAbs < p := by omega
  have hp3 : N ≤ p - 1 := by omega
  obtain ⟨np, hnp, gp, -, hgp⟩ := hc p hp1 hp
  obtain ⟨Gz, hGz⟩ := sum_aeval_aroots_isInt hm gp
  -- the exponential sum, from the assumed relation
  have hexpsum : ((h.aroots ℂ).map Complex.exp).sum = -(b : ℂ) := by
    linear_combination hrel
  -- the integer produced by the estimate
  obtain ⟨Z, hZ⟩ : ∃ z : ℤ, z = -b * np - p * Gz := ⟨_, rfl⟩
  have hsplit : ((h.aroots ℂ).map
      (fun r => (np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp))).sum
      = ((Z : ℤ) : ℂ) := by
    rw [Multiset.sum_map_sub, Multiset.sum_map_mul_left, Multiset.sum_map_mul_left,
      hexpsum, hGz, hZ]
    push_cast
    ring
  -- the estimate bounds it below one
  have hfacpos : (0 : ℝ) < ((p - 1)! : ℝ) := by
    exact_mod_cast Nat.factorial_pos (p - 1)
  have hbound : ‖((Z : ℤ) : ℂ)‖ < 1 := by
    rw [← hsplit]
    refine lt_of_le_of_lt (norm_multiset_sum_le _) ?_
    have hterm : ∀ x ∈ ((h.aroots ℂ).map
        (fun r => (np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp))).map norm,
        x ≤ |c| ^ p / ((p - 1)! : ℝ) := by
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Multiset.mem_map] at hy
      obtain ⟨r, hr, rfl⟩ := hy
      have hkey := hgp hr
      have hnorm : ‖(np : ℂ) * Complex.exp r - (p : ℂ) * (Polynomial.aeval r gp)‖
          ≤ c ^ p / ((p - 1)! : ℝ) := by
        simpa [zsmul_eq_mul, nsmul_eq_mul] using hkey
      refine hnorm.trans ?_
      rw [div_le_div_iff_of_pos_right hfacpos]
      calc c ^ p ≤ |c ^ p| := le_abs_self _
        _ = |c| ^ p := abs_pow c p
    refine lt_of_le_of_lt (Multiset.sum_le_card_nsmul _ _ hterm) ?_
    rw [Multiset.card_map, Multiset.card_map, ← hM, nsmul_eq_mul]
    have hp1' : p - 1 + 1 = p := by omega
    have hpow : |c| ^ p = |c| * |c| ^ (p - 1) := by
      rw [← pow_succ', hp1']
    rw [hpow, mul_div_assoc]
    exact hN (p - 1) hp3
  -- conclude
  have hZ0 : Z = 0 := by
    have habs : |(Z : ℝ)| < 1 := by simpa using hbound
    have hZabs : |Z| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp hZabs
  have hdvd : (p : ℤ) ∣ b * np := by
    refine ⟨-Gz, ?_⟩
    rw [hZ] at hZ0
    linarith [hZ0]
  rcases (Int.Prime.dvd_mul' hp hdvd) with hd | hd
  · have hle : (p : ℤ) ≤ |b| := Int.le_of_dvd (abs_pos.mpr hb) ((dvd_abs _ _).mpr hd)
    rw [Int.abs_eq_natAbs] at hle
    omega
  · exact hnp hd

end GaloisForLFunctions.HTGeometry
