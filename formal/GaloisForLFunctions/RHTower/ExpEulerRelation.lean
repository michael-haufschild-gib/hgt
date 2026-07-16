import GaloisForLFunctions.RHTower.IntegralizedConjugateSet
import GaloisForLFunctions.RHTower.ReducedSubsetSumPoly
import GaloisForLFunctions.RHTower.OrbitSumDegree
import GaloisForLFunctions.RHTower.ScaledHermiteContradiction

/-!
# The non-monic Lindemann–Weierstrass contradiction

The analytic finish of Lindemann–Weierstrass for a Euler-type exponential relation over a *non-monic*
conjugate set.  If `μ ∈ ℤ[X]` is nonzero with leading coefficient `ℓ` and complete factorization
`μ.map = C ℓ · ∏_j (X − θ_j)`, and the subset-sum exponential relation
`∑_S exp(∑_{j∈S} θ_j) = 0` holds (the expansion of `∏_j (1 + e^{θ_j}) = 0`), a contradiction follows.

The mechanism is Hermite's, adapted to non-integer exponents.  The empty subset contributes `σ_∅ = 0`,
so the count `a₀ = #\{S : σ_S = 0\} ≥ 1` is the nondegeneracy — with the all-ones coefficient family
there is no sign cancellation.  Feed the reduced integer polynomial `g` (roots the nonzero `σ_S`) to
`exp_polynomial_approx`; the symmetric orbit sum `Φ = ∑_S aeval(∑_{j∈S} X_j) gp` is cleared to an
integer by `ℓ^{Φ.totalDegree}` (non-monic symmetric integrality), and `Φ.totalDegree ≤ gp.natDegree`
keeps the `ℓ`-power below `|ℓ|^{p·deg g}`.  The resulting integer
`J = a₀·n_p·ℓ^{Φ.totalDegree} + p·(T₀ − a₀·g_p(0)·ℓ^{Φ.totalDegree})` satisfies
`|J| ≤ (\#S)·(|ℓ|^{deg g}·B)^p/(p−1)! → 0`, so `J = 0`; but then `p ∣ a₀·n_p·ℓ^{Φ.totalDegree}`,
contradicting `p ∤ a₀`, `p ∤ n_p`, `p ∤ ℓ` for a large prime `p`.
-/

open Polynomial Finset
open scoped Nat

namespace GaloisForLFunctions.RHTower

theorem exp_euler_relation_ne {d : ℕ} (μ : ℤ[X]) (hμ0 : μ ≠ 0) (θ : Fin d → ℂ)
    (hθ : μ.map (Int.castRingHom ℂ)
        = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (θ j)) Finset.univ.val).prod)
    (hrel : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Complex.exp (∑ j ∈ S, θ j) = 0) :
    False := by
  classical
  set ℓ : ℤ := μ.leadingCoeff with hℓ
  have hℓ0 : ℓ ≠ 0 := by rw [hℓ]; exact Polynomial.leadingCoeff_ne_zero.mpr hμ0
  set PS := (Finset.univ : Finset (Fin d)).powerset with hPS
  set a0 : ℤ := ((PS.filter (fun S => (∑ j ∈ S, θ j) = 0)).card : ℤ) with ha0def
  have hemp : (∅ : Finset (Fin d)) ∈ PS.filter (fun S => (∑ j ∈ S, θ j) = 0) := by
    rw [Finset.mem_filter, hPS, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by simp⟩
  have ha0pos : 0 < a0 := by
    rw [ha0def]; exact_mod_cast Finset.card_pos.mpr ⟨_, hemp⟩
  have ha0ne : a0 ≠ 0 := ne_of_gt ha0pos
  -- split relation into zero and nonzero subset sums
  have hz : ∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) = 0), Complex.exp (∑ j ∈ S, θ j) = (a0 : ℂ) := by
    have hone : ∀ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) = 0), Complex.exp (∑ j ∈ S, θ j) = 1 := by
      intro S hS; rw [Finset.mem_filter] at hS; rw [hS.2, Complex.exp_zero]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one, ha0def]
    push_cast; ring
  have hsplit : (a0 : ℂ) + ∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0),
      Complex.exp (∑ j ∈ S, θ j) = 0 := by
    rw [← hz, Finset.sum_filter_add_sum_filter_not]
    exact hrel
  have hsum_exp : ∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0),
      Complex.exp (∑ j ∈ S, θ j) = -(a0 : ℂ) := eq_neg_of_add_eq_zero_right hsplit
  -- reduced polynomial for exp_polynomial_approx
  obtain ⟨g, hg0e, hroot⟩ := exists_reduced_subsetSum_poly μ hμ0 θ hθ
  obtain ⟨B, hB⟩ := LindemannWeierstrass.exp_polynomial_approx g hg0e
  -- the estimate base and limit
  set N : ℝ := ((PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0)).card : ℝ) with hN
  set B' : ℝ := |(ℓ : ℝ)| ^ g.natDegree * B with hB'
  have hlim : Filter.Tendsto (fun p : ℕ => N * (B' ^ p / (p - 1)!)) Filter.atTop (nhds 0) := by
    have h1 := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (1 : ℝ) B' 1
    have h2 : Filter.Tendsto (fun p : ℕ => B' ^ p / (p - 1)!) Filter.atTop (nhds 0) := by simpa using h1
    simpa using h2.const_mul N
  have hev : ∀ᶠ p : ℕ in Filter.atTop, N * (B' ^ p / (p - 1)!) < 1 :=
    hlim.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨P₀, hP₀⟩ := hev
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes
    (max P₀ (max ((g.eval 0).natAbs + 1) (max (a0.natAbs + 1) (ℓ.natAbs + 1))))
  have hp_ge_P₀ : P₀ ≤ p := le_trans (le_max_left _ _) hp_gt
  have hp_gt_g : (g.eval 0).natAbs < p := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp_gt; omega
  have hp_gt_a0 : a0.natAbs < p := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hp_gt); omega
  have hp_gt_ℓ : ℓ.natAbs < p := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hp_gt); omega
  obtain ⟨n_p, hnp_ndvd, gp, hgp_deg, hgp_bound⟩ := hB p hp_gt_g hp_prime
  -- symmetric orbit sum
  set Φ : MvPolynomial (Fin d) ℤ :=
    ∑ S ∈ PS, Polynomial.aeval (∑ j ∈ S, MvPolynomial.X (R := ℤ) j) gp with hΦ
  have hΦsym : Φ.IsSymmetric := by
    intro σ
    rw [hΦ, map_sum]
    refine Finset.sum_nbij' (fun T => T.image σ) (fun T => T.image σ.symm) ?_ ?_ ?_ ?_ ?_
    · intro T _; simp [hPS]
    · intro T _; simp [hPS]
    · intro T _; simp [Finset.image_image]
    · intro T _; simp [Finset.image_image]
    · intro T _
      have hargeq : (MvPolynomial.rename σ) (∑ j ∈ T, MvPolynomial.X (R := ℤ) j)
          = ∑ j ∈ T.image σ, MvPolynomial.X (R := ℤ) j := by
        rw [map_sum, Finset.sum_image (fun a _ b _ h => σ.injective h)]
        exact Finset.sum_congr rfl (fun j _ => by simp [MvPolynomial.rename_X])
      rw [← Polynomial.aeval_algHom_apply, hargeq]
  obtain ⟨T₀, hT₀⟩ := nonmonic_symmetric_aeval_isInt_of_factorization μ hμ0 θ hθ Φ hΦsym
  -- evaluate Φ at θ
  have hΦeval : MvPolynomial.aeval θ Φ
      = ∑ S ∈ PS, Polynomial.aeval (∑ j ∈ S, θ j) gp := by
    rw [hΦ, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have harg : (MvPolynomial.aeval θ) (∑ j ∈ S, MvPolynomial.X (R := ℤ) j) = ∑ j ∈ S, θ j := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [MvPolynomial.aeval_X]
    rw [← Polynomial.aeval_algHom_apply, harg]
  have hev0 : Polynomial.aeval (0 : ℂ) gp = ((gp.eval 0 : ℤ) : ℂ) := by
    have h0 : (0 : ℂ) = (algebraMap ℤ ℂ) (0 : ℤ) := by simp
    rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]; simp
  have hzero_part : ∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) = 0),
      Polynomial.aeval (∑ j ∈ S, θ j) gp = (a0 : ℂ) * ((gp.eval 0 : ℤ) : ℂ) := by
    have hone : ∀ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) = 0),
        Polynomial.aeval (∑ j ∈ S, θ j) gp = ((gp.eval 0 : ℤ) : ℂ) := by
      intro S hS; rw [Finset.mem_filter] at hS; rw [hS.2, hev0]
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, ha0def]; push_cast; ring
  have hnonzero_part : ∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0),
      Polynomial.aeval (∑ j ∈ S, θ j) gp
      = MvPolynomial.aeval θ Φ - (a0 : ℂ) * ((gp.eval 0 : ℤ) : ℂ) := by
    have hfa := Finset.sum_filter_add_sum_filter_not PS (fun S => (∑ j ∈ S, θ j) = 0)
        (fun S => Polynomial.aeval (∑ j ∈ S, θ j) gp)
    rw [hΦeval, ← hfa, hzero_part]; ring
  set δfun : Finset (Fin d) → ℂ := fun S => (n_p : ℂ) * Complex.exp (∑ j ∈ S, θ j)
      - (p : ℂ) * Polynomial.aeval (∑ j ∈ S, θ j) gp with hδ
  have hbound : ∀ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0), ‖δfun S‖ ≤ B ^ p / (p - 1)! := by
    intro S hS
    rw [Finset.mem_filter] at hS
    have hr : (∑ j ∈ S, θ j) ∈ g.aroots ℂ := hroot S hS.1 hS.2
    have hb := hgp_bound hr
    rw [zsmul_eq_mul, nsmul_eq_mul] at hb
    exact hb
  set Tdeg := Φ.totalDegree with hTdeg
  have hTD : Tdeg ≤ gp.natDegree := by rw [hTdeg, hΦ, hPS]; exact orbitSum_totalDegree_le gp
  set Jℤ : ℤ := a0 * n_p * ℓ ^ Tdeg + (p : ℤ) * (T₀ - a0 * gp.eval 0 * ℓ ^ Tdeg) with hJdef
  have hLcast : ((ℓ : ℤ) : ℂ) ^ Tdeg * MvPolynomial.aeval θ Φ = (T₀ : ℂ) := hT₀
  have hkey : (Jℤ : ℂ) = -(((ℓ : ℤ) : ℂ) ^ Tdeg
      * ∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0), δfun S) := by
    have hexpand : ∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0), δfun S
        = (n_p : ℂ) * (∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0), Complex.exp (∑ j ∈ S, θ j))
          - (p : ℂ) * (∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0),
              Polynomial.aeval (∑ j ∈ S, θ j) gp) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [hexpand, hsum_exp, hnonzero_part, hJdef]
    push_cast
    rw [← hLcast]
    ring
  have hℓabs : (1 : ℝ) ≤ |((ℓ : ℤ) : ℝ)| := by
    have := Int.one_le_abs hℓ0
    calc (1:ℝ) = ((1:ℤ):ℝ) := by norm_num
      _ ≤ ((|ℓ| : ℤ) : ℝ) := by exact_mod_cast this
      _ = |((ℓ:ℤ):ℝ)| := by rw [Int.cast_abs]
  have hnorm : ‖(Jℤ : ℂ)‖ < 1 := by
    rw [hkey, norm_neg, norm_mul, norm_pow, Complex.norm_intCast]
    have hsumle : ‖∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0), δfun S‖
        ≤ N * (B ^ p / (p - 1)!) := by
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum hbound) (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    have hpow : |((ℓ : ℤ) : ℝ)| ^ Tdeg ≤ |((ℓ : ℤ) : ℝ)| ^ (p * g.natDegree) := by
      apply pow_le_pow_right₀ hℓabs
      have := hgp_deg; omega
    calc |((ℓ : ℤ) : ℝ)| ^ Tdeg * ‖∑ S ∈ PS.filter (fun S => (∑ j ∈ S, θ j) ≠ 0), δfun S‖
        ≤ |((ℓ : ℤ) : ℝ)| ^ (p * g.natDegree) * (N * (B ^ p / (p - 1)!)) := by
          apply mul_le_mul hpow hsumle (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
      _ = N * (B' ^ p / (p - 1)!) := by
          rw [hB', mul_pow, pow_mul]; ring
      _ < 1 := hP₀ p hp_ge_P₀
  have hI0 : Jℤ = 0 := by
    have habs : |(Jℤ : ℝ)| < 1 := by rw [← Complex.norm_intCast]; exact hnorm
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  have hdvd : (p : ℤ) ∣ a0 * n_p * ℓ ^ Tdeg := by
    have heq : a0 * n_p * ℓ ^ Tdeg = -((p : ℤ) * (T₀ - a0 * gp.eval 0 * ℓ ^ Tdeg)) := by
      have := hI0; rw [hJdef] at this; linarith
    rw [heq]; exact (Dvd.intro _ rfl).neg_right
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_prime_int.dvd_mul.mp hdvd with h | h
  · rcases hp_prime_int.dvd_mul.mp h with h1 | h1
    · have hdvdnat : p ∣ a0.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr h1; rwa [Int.natAbs_natCast] at this
      exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr ha0ne) hdvdnat) (not_le.mpr hp_gt_a0)
    · exact hnp_ndvd h1
  · have hpℓ : (p : ℤ) ∣ ℓ := hp_prime_int.dvd_of_dvd_pow h
    have hdvdnat : p ∣ ℓ.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hpℓ; rwa [Int.natAbs_natCast] at this
    exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hℓ0) hdvdnat) (not_le.mpr hp_gt_ℓ)

end GaloisForLFunctions.RHTower
