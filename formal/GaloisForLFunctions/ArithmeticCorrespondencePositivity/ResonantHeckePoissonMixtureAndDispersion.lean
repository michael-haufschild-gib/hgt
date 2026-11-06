import GaloisForLFunctions.RHTower.EisensteinHeckeSecondMoment
import GaloisForLFunctions.RHTower.EisensteinHeckeResonanceAllZeros
import GaloisForLFunctions.RHTower.EisensteinHeckeCoefficient
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonBoundedReproduction
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges

/-!
# Multiplicative Hecke algebra Poisson positivity and exact resonant dispersion

At a single prime `p`, the first two moments of `T_p` on the truncated Eisenstein resonant state
`Λ^Y E_u` (`Λ(1 + 2u) = 0`, `Re u < 0`, `Y ≥ p`) are `p^u + p^{ū}` and `2 + p^{2u} + p^{2ū}`
(`EisensteinHeckeResonantMoment`, `EisensteinHeckeSecondMoment`). This module resolves what happens
across the **entire multiplicative Hecke algebra** `{T_n}_{n ≥ 1}` and extracts the exact positive
Hilbert-space invariant behind the obstruction:

* **Multiplicative Hecke eigenvalue law** (`whittakerCoeff_mul_eq_sum_gcd_divisors`,
  `conj_whittakerCoeff_mul_I`): for all `m, n ≥ 1` and `u ∈ ℂ`,
  `W_u(m) W_u(n) = Σ_{d ∣ gcd(m, n)} W_u(mn / d²)`, and on the tempered line `u = it` (`t ∈ ℝ`) the
  eigenvalues `W_{it}(n)` are real.
* **Exact Poisson mixture identity and `C*`-positivity no-go**
  (`resonantHeckeMoment_eq_poisson_integral`, `resonantHeckeStarSquare_eq_poisson_integral`,
  `resonantHeckeStarSquare_re_nonneg`): the all-`n` resonant Hecke moment `μ_n(u)` (`Re u < 0`) is
  the half-plane Poisson integral `∫ P_{-Re u}(t - Im u) W_{it}(n) dt`. Consequently, for *every*
  `u` with `Re u < 0`—both on-line (`Re u = -1/4`) and off-line (`Re u ≠ -1/4`)—and every finite
  Hecke combination `Σ_{m ∈ S} c_m T_m`, the `C*`-square expectation equals
  `∫ P_{-Re u}(t - Im u) ‖Σ_{m ∈ S} c_m W_{it}(m)‖² dt ≥ 0`. No `C*`-positivity inequality in the
  commutative Hecke algebra can ever be violated by an off-line zero.
* **Exact `L²(𝒟)` Hecke eigen-defect dispersion and single-prime RH criteria**
  (`integral_norm_sq_heckeEigenDefect_resonantZero`, `riemannHypothesis_iff_heckeEigenDefect_le`,
  `riemannHypothesis_iff_heckeEigenDefect_ge`, `xiZeroHalfPlaneBound_iff_heckeEigenDefect_le`):
  every strip zero `ρ` of `Λ` (`0 < Re ρ < 1`) is automatically nonreal (`Im ρ ≠ 0`), and for every
  prime `p` and height `Y ≥ p`,
  `∫_𝒟 ‖T_p Λ^Y E_u − (p^u + p^{ū}) Λ^Y E_u‖² = 2 (1 − p^{Re ρ − 1}) ∫_𝒟 ‖Λ^Y E_u‖²`
  (`u = ρ/2 − 1/2`), cancelling the ordinate phase `cos(γ log p)` identically. Because reflection
  `ρ ↔ 1 − ρ` splits any off-line pair strictly across `2 (1 − p^{-1/2})`, a one-sided bound (`≤`
  or `≥`) at *any single prime `p` and single height `Y ≥ p`* is equivalent to `RiemannHypothesis`,
  and `≤ 2 (1 − p^{-1/2 − β})` (`β ≥ 0`) is equivalent to `XiZeroHalfPlaneBound β`.
-/

open Complex Finset MeasureTheory Set ModularGroup
open scoped ComplexConjugate UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open _root_.RHTower
open _root_.RHTower.CrossRouteReceiverBridges (mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip
  mem_zetaZeroConfig_carrier_of_xi_eq_zero xiZeroHalfPlaneBound_iff_zetaZeroConfig_re_le)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-! ### Multiplicative algebra of Eisenstein Hecke eigenvalues -/

@[simp]
theorem whittakerCoeff_one (u : ℂ) : whittakerCoeff u 1 = 1 := by
  simp [whittakerCoeff, divisorPowerSum]

theorem whittakerCoeff_prime (u : ℂ) {p : ℕ} (hp : p.Prime) :
    whittakerCoeff u p = (p : ℂ) ^ u + (p : ℂ) ^ (-u) := by
  have h := whittakerCoeff_hecke u hp one_ne_zero
  rw [mul_one, if_neg hp.not_dvd_one, add_zero, whittakerCoeff_one, mul_one] at h
  exact h

theorem whittakerCoeff_mul_coprime (u : ℂ) {a b : ℕ} (hab : a.Coprime b) :
    whittakerCoeff u (a * b) = whittakerCoeff u a * whittakerCoeff u b := by
  unfold whittakerCoeff
  rw [natCast_mul_cpow', divisorPowerSum_mul_coprime _ hab]
  ring

/-- Symmetric antidiagonal form `W_u(n) = Σ_{a d = n} a^u d^{-u}` for `n ≠ 0`. -/
theorem whittakerCoeff_eq_sum_antidiagonal (u : ℂ) {n : ℕ} (_hn : n ≠ 0) :
    whittakerCoeff u n =
      ∑ ad ∈ n.divisorsAntidiagonal, (ad.1 : ℂ) ^ u * (ad.2 : ℂ) ^ (-u) := by
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a d => (a : ℂ) ^ u * (d : ℂ) ^ (-u))]
  unfold whittakerCoeff divisorPowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hn_eq : n = n / d * d := (Nat.div_mul_cancel hd_dvd).symm
  conv_lhs => rw [hn_eq]
  rw [natCast_mul_cpow', mul_assoc, ← Complex.cpow_add _ _ hd0]
  congr 2
  ring

/-- On the tempered line `u = i t` (`t ∈ ℝ`), `W_{i t}(n)` is real for every `n ≠ 0`. -/
theorem conj_whittakerCoeff_I_mul_real (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    starRingEnd ℂ (whittakerCoeff (Complex.I * (t : ℂ)) n) =
      whittakerCoeff (Complex.I * (t : ℂ)) n := by
  rw [whittakerCoeff_eq_sum_antidiagonal _ hn, map_sum]
  have hterm : ∀ a d : ℕ,
      starRingEnd ℂ
          ((a : ℂ) ^ (Complex.I * (t : ℂ)) * (d : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
        (d : ℂ) ^ (Complex.I * (t : ℂ)) * (a : ℂ) ^ (-(Complex.I * (t : ℂ))) := fun a d => by
    rw [map_mul, conj_natCast_cpow, conj_natCast_cpow]
    have h1 : starRingEnd ℂ (Complex.I * (t : ℂ)) = -(Complex.I * (t : ℂ)) := by simp
    have h2 : starRingEnd ℂ (-(Complex.I * (t : ℂ))) = Complex.I * (t : ℂ) := by simp
    rw [h1, h2, mul_comm]
  have hcongr : ∑ x ∈ n.divisorsAntidiagonal,
      starRingEnd ℂ
        ((x.1 : ℂ) ^ (Complex.I * (t : ℂ)) * (x.2 : ℂ) ^ (-(Complex.I * (t : ℂ)))) =
      ∑ x ∈ n.divisorsAntidiagonal,
        (x.2 : ℂ) ^ (Complex.I * (t : ℂ)) * (x.1 : ℂ) ^ (-(Complex.I * (t : ℂ))) :=
    Finset.sum_congr rfl fun x _ => hterm x.1 x.2
  rw [hcongr]
  refine Finset.sum_nbij Prod.swap (fun x hx => ?_) (fun _ _ _ _ h => Prod.swap_injective h)
      (fun y hy => ⟨y.swap, ?_, Prod.swap_swap y⟩) (fun _ _ => rfl)
  · obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨by simpa [mul_comm] using hprod, hne⟩
  · obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp hy
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨by simpa [mul_comm] using hprod, hne⟩

/-- **Multiplicative Hecke eigenvalue product law.** For all `m, n ≥ 1` and `u ∈ ℂ`,
`W_u(m) W_u(n) = Σ_{d ∣ gcd(m, n)} W_u(mn / d²)`. -/
theorem whittakerCoeff_mul_eq_sum_gcd_divisors (u : ℂ) :
    ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 →
      whittakerCoeff u m * whittakerCoeff u n =
        ∑ d ∈ (Nat.gcd m n).divisors, whittakerCoeff u (m * n / d ^ 2) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n hm hn
    by_cases hm1 : m = 1
    · subst hm1
      simp [Nat.gcd_one_left]
    · have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm, hm1⟩
      set p : ℕ := m.minFac
      have hp : p.Prime := Nat.minFac_prime hm1
      have hp_dvd : p ∣ m := Nat.minFac_dvd m
      set m₁ : ℕ := m / p
      have hm_eq : m = p * m₁ := (Nat.mul_div_cancel' hp_dvd).symm
      have hm₁_pos : 0 < m₁ := by
        by_contra hc
        simp only [not_lt, Nat.le_zero] at hc
        rw [hc, mul_zero] at hm_eq
        exact hm hm_eq
      have hm₁ : m₁ ≠ 0 := hm₁_pos.ne'
      have hm₁_lt : m₁ < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) hp.one_lt
      have hhecke_m : whittakerCoeff u m =
          ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * whittakerCoeff u m₁ -
            (if p ∣ m₁ then whittakerCoeff u (m₁ / p) else 0) := by
        rw [hm_eq]
        exact eq_sub_of_add_eq (whittakerCoeff_hecke u hp hm₁)
      set D₀ := (Nat.gcd m₁ n).divisors
      set D₁ := (Nat.gcd (p * m₁) n).divisors
      set A := D₀.filter fun d => p * d ^ 2 ∣ m₁ * n
      set B := D₀.filter fun d => p * d ∣ m₁
      -- First piece: apply IH at `(m₁, n)` and expand via `whittakerCoeff_hecke`
      have hpiece1 : ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * (whittakerCoeff u m₁ * whittakerCoeff u n) =
          (∑ d ∈ D₀, whittakerCoeff u (p * m₁ * n / d ^ 2)) +
            ∑ d ∈ A, whittakerCoeff u (m₁ * n / (p * d ^ 2)) := by
        rw [ih m₁ hm₁_lt hm₁ hn, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd_gcd : d ∣ Nat.gcd m₁ n := (Nat.mem_divisors.mp hd).1
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
        have hd2_dvd : d ^ 2 ∣ m₁ * n := by
          rw [sq]; exact mul_dvd_mul (hd_gcd.trans (Nat.gcd_dvd_left m₁ n))
            (hd_gcd.trans (Nat.gcd_dvd_right m₁ n))
        have hq_pos : 0 < m₁ * n / d ^ 2 :=
          Nat.div_pos (Nat.le_of_dvd (mul_pos hm₁_pos (Nat.pos_of_ne_zero hn)) hd2_dvd)
            (pow_pos hd_pos 2)
        have hh := (whittakerCoeff_hecke u hp hq_pos.ne').symm
        have hmul_div : p * (m₁ * n / d ^ 2) = p * m₁ * n / d ^ 2 := by
          rw [mul_assoc, Nat.mul_div_assoc p hd2_dvd]
        have hdiv_div : m₁ * n / d ^ 2 / p = m₁ * n / (p * d ^ 2) := by
          rw [Nat.div_div_eq_div_mul, mul_comm (d ^ 2) p]
        have hdvd_iff : p ∣ m₁ * n / d ^ 2 ↔ p * d ^ 2 ∣ m₁ * n := by
          constructor
          · rintro ⟨k, hk⟩
            refine ⟨k, ?_⟩
            calc m₁ * n = d ^ 2 * (m₁ * n / d ^ 2) := (Nat.mul_div_cancel' hd2_dvd).symm
              _ = d ^ 2 * (p * k) := by rw [hk]
              _ = p * d ^ 2 * k := by ring
          · rintro ⟨k, hk⟩
            refine ⟨k, ?_⟩
            have : m₁ * n = d ^ 2 * (p * k) := by rw [hk]; ring
            rw [this, Nat.mul_div_cancel_left _ (pow_pos hd_pos 2)]
        rw [hh, hmul_div, hdiv_div]
        congr 1
        by_cases hpd : p * d ^ 2 ∣ m₁ * n
        · rw [if_pos (hdvd_iff.mpr hpd), if_pos hpd]
        · rw [if_neg (fun h => hpd (hdvd_iff.mp h)), if_neg hpd]
      -- Second piece: rewrite `(if p ∣ m₁ then W(m₁/p) else 0) * W(n)` as the sum over `B`
      have hpiece2 : (if p ∣ m₁ then whittakerCoeff u (m₁ / p) else 0) * whittakerCoeff u n =
          ∑ d ∈ B, whittakerCoeff u (m₁ * n / (p * d ^ 2)) := by
        by_cases hp₁ : p ∣ m₁
        · rw [if_pos hp₁]
          have hm₂_pos : 0 < m₁ / p := Nat.div_pos (Nat.le_of_dvd hm₁_pos hp₁) hp.pos
          have hm₂_lt : m₁ / p < m := (Nat.div_lt_self hm₁_pos hp.one_lt).trans hm₁_lt
          rw [ih (m₁ / p) hm₂_lt hm₂_pos.ne' hn]
          have hset : (Nat.gcd (m₁ / p) n).divisors = B := by
            ext d
            simp only [B, D₀, Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
            constructor
            · rintro ⟨⟨hd1, hd2⟩, _⟩
              have hpdm : p * d ∣ m₁ := by
                rcases hd1 with ⟨k, hk⟩
                refine ⟨k, ?_⟩
                calc m₁ = p * (m₁ / p) := (Nat.mul_div_cancel' hp₁).symm
                  _ = p * (d * k) := by rw [hk]
                  _ = p * d * k := by ring
              exact ⟨⟨⟨(dvd_mul_left d p).trans hpdm, hd2⟩,
                fun h => hn (Nat.gcd_eq_zero_iff.mp h).2⟩, hpdm⟩
            · rintro ⟨⟨⟨_, hd2⟩, _⟩, hpdm⟩
              have hd1 : d ∣ m₁ / p := by
                rcases hpdm with ⟨k, hk⟩
                have : m₁ = p * (d * k) := by rw [hk]; ring
                rw [this, Nat.mul_div_cancel_left _ hp.pos]
                exact dvd_mul_right d k
              exact ⟨⟨hd1, hd2⟩, fun h => hn (Nat.gcd_eq_zero_iff.mp h).2⟩
          rw [hset]
          refine Finset.sum_congr rfl fun d _ => ?_
          congr 1
          rw [Nat.div_mul_right_comm hp₁, Nat.div_div_eq_div_mul]
        · rw [if_neg hp₁, zero_mul, eq_comm]
          refine Finset.sum_eq_zero fun d hd => ?_
          have hpdm : p * d ∣ m₁ := (Finset.mem_filter.mp hd).2
          exact absurd ((dvd_mul_right p d).trans hpdm) hp₁
      -- Subset inclusions `B ⊆ A` and `D₀ ⊆ D₁`
      have hBA : B ⊆ A := fun d hd => by
        obtain ⟨hd0, hpdm⟩ := Finset.mem_filter.mp hd
        refine Finset.mem_filter.mpr ⟨hd0, ?_⟩
        have hdn : d ∣ n := ((Nat.mem_divisors.mp hd0).1).trans (Nat.gcd_dvd_right m₁ n)
        simpa [sq, mul_assoc] using mul_dvd_mul hpdm hdn
      have hD₀₁ : D₀ ⊆ D₁ := fun d hd => by
        obtain ⟨hdg, hne⟩ := Nat.mem_divisors.mp hd
        refine Nat.mem_divisors.mpr ⟨Nat.dvd_gcd ?_ (hdg.trans (Nat.gcd_dvd_right m₁ n)),
          fun h => hn (Nat.gcd_eq_zero_iff.mp h).2⟩
        exact (hdg.trans (Nat.gcd_dvd_left m₁ n)).trans (dvd_mul_left m₁ p)
      -- Bijection `d ↦ p * d` from `A \ B` onto `D₁ \ D₀`
      have hbij : ∑ d ∈ A \ B, whittakerCoeff u (m₁ * n / (p * d ^ 2)) =
          ∑ c ∈ D₁ \ D₀, whittakerCoeff u (p * m₁ * n / c ^ 2) := by
        refine Finset.sum_nbij (fun d => p * d) ?_ ?_ ?_ ?_
        · intro d hd
          obtain ⟨hdA, hdB⟩ := Finset.mem_sdiff.mp hd
          obtain ⟨hd0, hpd2⟩ := Finset.mem_filter.mp hdA
          have hpdm_not : ¬ p * d ∣ m₁ := fun h => hdB (Finset.mem_filter.mpr ⟨hd0, h⟩)
          have hdm : d ∣ m₁ := ((Nat.mem_divisors.mp hd0).1).trans (Nat.gcd_dvd_left m₁ n)
          have hdn : d ∣ n := ((Nat.mem_divisors.mp hd0).1).trans (Nat.gcd_dvd_right m₁ n)
          have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd0
          rcases hdm with ⟨k, hk⟩
          rcases hdn with ⟨l, hl⟩
          have hpkl : p ∣ k * l := by
            apply Nat.dvd_of_mul_dvd_mul_left (pow_pos hd_pos 2)
            rcases hpd2 with ⟨r, hr⟩
            refine ⟨r, ?_⟩
            calc d ^ 2 * (k * l) = (d * k) * (d * l) := by ring
              _ = m₁ * n := by rw [← hk, ← hl]
              _ = p * d ^ 2 * r := hr
              _ = d ^ 2 * p * r := by ring
          have hpk_not : ¬ p ∣ k := by
            rintro ⟨s, rfl⟩
            exact hpdm_not ⟨s, by rw [hk]; ring⟩
          have hpl : p ∣ l := (hp.dvd_mul.mp hpkl).resolve_left hpk_not
          have hpd_n : p * d ∣ n := by
            rcases hpl with ⟨s, rfl⟩
            exact ⟨s, by rw [hl]; ring⟩
          have hpd_pm : p * d ∣ p * m₁ := mul_dvd_mul_left p ⟨k, hk⟩
          refine Finset.mem_sdiff.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hpd_pm hpd_n,
            fun h => hn (Nat.gcd_eq_zero_iff.mp h).2⟩, fun hc0 => ?_⟩
          exact hpdm_not (((Nat.mem_divisors.mp hc0).1).trans (Nat.gcd_dvd_left m₁ n))
        · intro d₁ _ d₂ _ heq
          exact mul_right_injective₀ hp.ne_zero heq
        · intro c hc
          obtain ⟨hc1, hc0⟩ := Finset.mem_sdiff.mp hc
          have hcg : c ∣ Nat.gcd (p * m₁) n := (Nat.mem_divisors.mp hc1).1
          have hc_pm : c ∣ p * m₁ := hcg.trans (Nat.gcd_dvd_left (p * m₁) n)
          have hc_n : c ∣ n := hcg.trans (Nat.gcd_dvd_right (p * m₁) n)
          have hc_not_m : ¬ c ∣ m₁ := fun hcm =>
            hc0 (Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hcm hc_n,
              fun h => hn (Nat.gcd_eq_zero_iff.mp h).2⟩)
          have hpc : p ∣ c := by
            by_contra hnpc
            have hcop : c.Coprime p := (hp.coprime_iff_not_dvd.mpr hnpc).symm
            exact hc_not_m (hcop.dvd_of_dvd_mul_left hc_pm)
          rcases hpc with ⟨d, rfl⟩
          refine ⟨d, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
          · have hdm : d ∣ m₁ := Nat.dvd_of_mul_dvd_mul_left hp.pos hc_pm
            exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hdm ((dvd_mul_left d p).trans hc_n),
              fun h => hn (Nat.gcd_eq_zero_iff.mp h).2⟩
          · have hdm : d ∣ m₁ := Nat.dvd_of_mul_dvd_mul_left hp.pos hc_pm
            simpa [sq, mul_comm, mul_left_comm, mul_assoc] using mul_dvd_mul hdm hc_n
          · intro hdB
            exact hc_not_m (Finset.mem_filter.mp hdB).2
        · intro d _
          congr 1
          have hnum : p * m₁ * n = p * (m₁ * n) := by ring
          have hden : (p * d) ^ 2 = p * (p * d ^ 2) := by ring
          rw [hnum, hden, Nat.mul_div_mul_left _ _ hp.pos]
      -- Assemble all pieces
      calc whittakerCoeff u m * whittakerCoeff u n
          = ((p : ℂ) ^ u + (p : ℂ) ^ (-u)) * (whittakerCoeff u m₁ * whittakerCoeff u n) -
              (if p ∣ m₁ then whittakerCoeff u (m₁ / p) else 0) * whittakerCoeff u n := by
                rw [hhecke_m]; ring
        _ = (∑ d ∈ D₀, whittakerCoeff u (p * m₁ * n / d ^ 2)) +
              (∑ d ∈ A, whittakerCoeff u (m₁ * n / (p * d ^ 2)) -
                ∑ d ∈ B, whittakerCoeff u (m₁ * n / (p * d ^ 2))) := by
                rw [hpiece1, hpiece2]; ring
        _ = (∑ d ∈ D₀, whittakerCoeff u (p * m₁ * n / d ^ 2)) +
              ∑ d ∈ A \ B, whittakerCoeff u (m₁ * n / (p * d ^ 2)) := by
                rw [← Finset.sum_sdiff_eq_sub hBA]
        _ = (∑ d ∈ D₀, whittakerCoeff u (p * m₁ * n / d ^ 2)) +
              ∑ c ∈ D₁ \ D₀, whittakerCoeff u (p * m₁ * n / c ^ 2) := by rw [hbij]
        _ = ∑ c ∈ D₁, whittakerCoeff u (p * m₁ * n / c ^ 2) := by
                rw [add_comm, Finset.sum_sdiff hD₀₁]
        _ = ∑ c ∈ (Nat.gcd m n).divisors, whittakerCoeff u (m * n / c ^ 2) := by
                simp only [D₁, hm_eq]

/-! ### Shifted Poisson–Laplace integral and the resonant Hecke Poisson mixture -/

/-- **Shifted Poisson–Laplace integral.** For `σ > 0` and `t₀, x ∈ ℝ`,
`∫ P_σ(t − t₀) e^{i x t} dt = exp(−σ |x| + i t₀ x)`. -/
theorem integral_halfPlanePoisson_shift_mul_cexp {σ : ℝ} (hσ : 0 < σ) (t₀ x : ℝ) :
    (∫ t : ℝ, (halfPlanePoisson σ (t - t₀) : ℂ) * Complex.exp (I * (x : ℂ) * (t : ℂ))) =
      Complex.exp (((-σ * |x| : ℝ) : ℂ) + I * ((t₀ * x : ℝ) : ℂ)) := by
  -- Step 1: unit-height unshifted evaluation via `integral_halfPlanePoisson_one_mul_eq_apply_I`
  have hunit_nonneg : ∀ {y : ℝ}, 0 ≤ y →
      (∫ w : ℝ, (halfPlanePoisson 1 w : ℂ) * Complex.exp (I * (y : ℂ) * (w : ℂ))) =
        Complex.exp ((-y : ℝ) : ℂ) := by
    intro y hy
    set F : ℂ → ℂ := fun z => Complex.exp (I * (y : ℂ) * z) with hF
    have hdiff : ∀ z : ℂ, 0 ≤ z.im → DifferentiableAt ℂ F z := fun z _ => by
      simp only [hF]; fun_prop
    have hbd : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ 1 := fun z hz => by
      simp only [hF, Complex.norm_exp, Real.exp_le_one_iff, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, zero_mul, one_mul,
        zero_sub, sub_zero, zero_add]
      nlinarith
    have hrep := integral_halfPlanePoisson_one_mul_eq_apply_I hdiff hbd
    have hFI : F I = Complex.exp ((-y : ℝ) : ℂ) := by
      simp only [hF]
      congr 1
      push_cast
      linear_combination (y : ℂ) * Complex.I_sq
    rwa [hFI] at hrep
  have hunit : ∀ y : ℝ,
      (∫ w : ℝ, (halfPlanePoisson 1 w : ℂ) * Complex.exp (I * (y : ℂ) * (w : ℂ))) =
        Complex.exp ((-|y| : ℝ) : ℂ) := by
    intro y
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]; exact hunit_nonneg hy
    · rw [abs_of_nonpos hy, ← hunit_nonneg (neg_nonneg.mpr hy)]
      have hneg := MeasureTheory.integral_neg_eq_self
        (fun w : ℝ => (halfPlanePoisson 1 w : ℂ) * Complex.exp (I * (y : ℂ) * (w : ℂ)))
        (volume : Measure ℝ)
      rw [← hneg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      dsimp only
      have heven : halfPlanePoisson 1 (-w) = halfPlanePoisson 1 w := by
        unfold halfPlanePoisson; ring
      have hexp_w : Complex.exp (I * (y : ℂ) * ((-w : ℝ) : ℂ)) =
          Complex.exp (I * ((-y : ℝ) : ℂ) * (w : ℂ)) := by
        congr 1
        push_cast
        ring
      rw [heven, hexp_w]
  -- Step 2: rescale `s = σ * w` and shift `t = s + t₀`
  have hscale : (∫ s : ℝ, (halfPlanePoisson σ s : ℂ) * Complex.exp (I * (x : ℂ) * (s : ℂ))) =
      Complex.exp (((-σ * |x| : ℝ) : ℂ)) := by
    have hsub := Measure.integral_comp_mul_left
      (fun s : ℝ => (halfPlanePoisson σ s : ℂ) * Complex.exp (I * (x : ℂ) * (s : ℂ))) σ
    have hpt : ∀ w : ℝ,
        (halfPlanePoisson σ (σ * w) : ℂ) * Complex.exp (I * (x : ℂ) * ((σ * w : ℝ) : ℂ)) =
          ((σ⁻¹ : ℝ) : ℂ) *
            ((halfPlanePoisson 1 w : ℂ) * Complex.exp (I * ((σ * x : ℝ) : ℂ) * (w : ℂ))) := by
      intro w
      have hp : halfPlanePoisson σ (σ * w) = σ⁻¹ * halfPlanePoisson 1 w := by
        unfold halfPlanePoisson
        have hσ0 : σ ≠ 0 := hσ.ne'
        have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp
      rw [hp]
      push_cast
      ring
    simp_rw [hpt] at hsub
    rw [integral_const_mul, abs_of_pos (inv_pos.mpr hσ), Complex.real_smul] at hsub
    have hσC : ((σ⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_ne_zero hσ.ne')
    have heq := mul_left_cancel₀ hσC hsub.symm
    rw [heq, hunit (σ * x), abs_mul, abs_of_pos hσ]
    congr 1
    push_cast
    ring
  have hshift := MeasureTheory.integral_sub_right_eq_self
    (μ := volume)
    (fun s : ℝ => (halfPlanePoisson σ s : ℂ) * Complex.exp (I * (x : ℂ) * ((s + t₀ : ℝ) : ℂ))) t₀
  have hcongr : (∫ t : ℝ, (halfPlanePoisson σ (t - t₀) : ℂ) * Complex.exp (I * (x : ℂ) * (t : ℂ))) =
      Complex.exp (I * ((t₀ * x : ℝ) : ℂ)) *
        ∫ s : ℝ, (halfPlanePoisson σ s : ℂ) * Complex.exp (I * (x : ℂ) * (s : ℂ)) := by
    calc (∫ t : ℝ, (halfPlanePoisson σ (t - t₀) : ℂ) * Complex.exp (I * (x : ℂ) * (t : ℂ)))
        = ∫ t : ℝ, (halfPlanePoisson σ (t - t₀) : ℂ) *
            Complex.exp (I * (x : ℂ) * ((t - t₀ + t₀ : ℝ) : ℂ)) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
              dsimp only
              rw [sub_add_cancel]
      _ = ∫ s : ℝ, (halfPlanePoisson σ s : ℂ) *
            Complex.exp (I * (x : ℂ) * ((s + t₀ : ℝ) : ℂ)) := hshift
      _ = ∫ s : ℝ, Complex.exp (I * ((t₀ * x : ℝ) : ℂ)) *
            ((halfPlanePoisson σ s : ℂ) * Complex.exp (I * (x : ℂ) * (s : ℂ))) := by
              refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
              dsimp only
              have hexp_s : Complex.exp (I * (x : ℂ) * ((s + t₀ : ℝ) : ℂ)) =
                  Complex.exp (I * ((t₀ * x : ℝ) : ℂ)) * Complex.exp (I * (x : ℂ) * (s : ℂ)) := by
                rw [← Complex.exp_add]
                congr 1
                push_cast
                ring
              rw [hexp_s]
              ring
      _ = Complex.exp (I * ((t₀ * x : ℝ) : ℂ)) *
            ∫ s : ℝ, (halfPlanePoisson σ s : ℂ) * Complex.exp (I * (x : ℂ) * (s : ℂ)) :=
              integral_const_mul _ _
  rw [hcongr, hscale, ← Complex.exp_add]
  congr 1
  ring

theorem integrable_halfPlanePoisson_shift_mul_cexp {σ : ℝ} (hσ : 0 < σ) (t₀ x : ℝ) :
    Integrable fun t : ℝ =>
      (halfPlanePoisson σ (t - t₀) : ℂ) * Complex.exp (I * (x : ℂ) * (t : ℂ)) := by
  have hP : Integrable (fun t : ℝ => (halfPlanePoisson σ (t - t₀) : ℂ)) :=
    ((integrable_halfPlanePoisson hσ).comp_sub_right t₀).ofReal
  have hbd : ∀ t : ℝ, ‖Complex.exp (I * (x : ℂ) * (t : ℂ))‖ ≤ 1 := fun t => by
    rw [Complex.norm_exp]
    have hre : (I * (x : ℂ) * (t : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero]
  exact hP.mul_bdd (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall hbd)

/-- **All-`n` resonant Hecke moment** on the half-plane `Re u < 0`. -/
def resonantHeckeMoment (u : ℂ) (n : ℕ) : ℂ :=
  ∑ ad ∈ n.divisorsAntidiagonal,
    if ad.2 < ad.1 then ((ad.1 : ℂ) / ad.2) ^ u
    else if ad.1 < ad.2 then ((ad.2 : ℂ) / ad.1) ^ (starRingEnd ℂ u)
    else 1

@[simp]
theorem resonantHeckeMoment_one (u : ℂ) : resonantHeckeMoment u 1 = 1 := by
  simp [resonantHeckeMoment]

theorem resonantHeckeMoment_prime (u : ℂ) {p : ℕ} (hp : p.Prime) :
    resonantHeckeMoment u p = (p : ℂ) ^ u + (p : ℂ) ^ (starRingEnd ℂ u) := by
  unfold resonantHeckeMoment
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a d =>
      if d < a then ((a : ℂ) / d) ^ u
      else if a < d then ((d : ℂ) / a) ^ (starRingEnd ℂ u)
      else 1),
    hp.divisors, Finset.sum_pair hp.one_lt.ne]
  have h1p : 1 < p := hp.one_lt
  rw [Nat.div_one, Nat.div_self hp.pos, if_pos h1p, if_neg (not_lt.mpr h1p.le), if_pos h1p]
  simp

theorem resonantHeckeMoment_prime_sq (u : ℂ) {p : ℕ} (hp : p.Prime) :
    resonantHeckeMoment u (p ^ 2) =
      (p : ℂ) ^ (2 * u) + 1 + (p : ℂ) ^ (2 * starRingEnd ℂ u) := by
  unfold resonantHeckeMoment
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a d =>
      if d < a then ((a : ℂ) / d) ^ u
      else if a < d then ((d : ℂ) / a) ^ (starRingEnd ℂ u)
      else 1),
    Nat.divisors_prime_pow hp 2, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, zero_add, pow_zero, pow_one]
  have hp1 : 1 < p := hp.one_lt
  have hp2 : 1 < p ^ 2 := one_lt_pow₀ hp1 two_ne_zero
  have hpC0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdiv1 : p ^ 2 / p = p := by rw [sq, Nat.mul_div_cancel_left _ hp.pos]
  have hdiv2 : p ^ 2 / p ^ 2 = 1 := Nat.div_self (pow_pos hp.pos 2)
  rw [Nat.div_one, hdiv1, hdiv2, if_pos hp2, if_neg (lt_irrefl p), if_neg (lt_irrefl p),
    if_neg (not_lt.mpr hp2.le), if_pos hp2]
  have hpow1 : ((p ^ 2 : ℕ) : ℂ) ^ u = (p : ℂ) ^ (2 * u) := by
    rw [sq p, natCast_mul_cpow', ← Complex.cpow_add _ _ hpC0, two_mul]
  have hpow2 : ((p ^ 2 : ℕ) : ℂ) ^ (starRingEnd ℂ u) = (p : ℂ) ^ (2 * starRingEnd ℂ u) := by
    rw [sq p, natCast_mul_cpow', ← Complex.cpow_add _ _ hpC0, two_mul]
  simp only [Nat.cast_one, div_one]
  rw [hpow1, hpow2]

/-- **Exact Poisson mixture representation of the resonant Hecke moment.** For every `u` with
`Re u < 0` and every `n ≥ 1`, `μ_n(u) = ∫ P_{-Re u}(t − Im u) W_{i t}(n) dt`. -/
theorem resonantHeckeMoment_eq_poisson_integral {u : ℂ} (hu : u.re < 0) {n : ℕ} (hn : n ≠ 0) :
    resonantHeckeMoment u n =
      ∫ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) * whittakerCoeff (I * (t : ℂ)) n := by
  have hσ : 0 < -u.re := neg_pos.mpr hu
  have hterm_exp : ∀ ad ∈ n.divisorsAntidiagonal, ∀ t : ℝ,
      (ad.1 : ℂ) ^ (I * (t : ℂ)) * (ad.2 : ℂ) ^ (-(I * (t : ℂ))) =
        Complex.exp (I * ((Real.log ((ad.1 : ℝ) / ad.2) : ℝ) : ℂ) * (t : ℂ)) := by
    intro ad had t
    have ha_pos : 0 < ad.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal had)
    have hd_pos : 0 < ad.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal had)
    have haR : (0 : ℝ) < ad.1 := by exact_mod_cast ha_pos
    have hdR : (0 : ℝ) < ad.2 := by exact_mod_cast hd_pos
    have haC : (ad.1 : ℂ) ≠ 0 := by exact_mod_cast ha_pos.ne'
    have hdC : (ad.2 : ℂ) ≠ 0 := by exact_mod_cast hd_pos.ne'
    rw [Complex.cpow_def_of_ne_zero haC, Complex.cpow_def_of_ne_zero hdC,
      show (ad.1 : ℂ) = ((ad.1 : ℝ) : ℂ) by norm_cast,
      show (ad.2 : ℂ) = ((ad.2 : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_log haR.le, ← Complex.ofReal_log hdR.le, ← Complex.exp_add,
      Real.log_div haR.ne' hdR.ne']
    congr 1
    push_cast
    ring
  have hcongr : (fun t : ℝ => (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
      whittakerCoeff (I * (t : ℂ)) n) =
      fun t : ℝ => ∑ ad ∈ n.divisorsAntidiagonal,
        (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          Complex.exp (I * ((Real.log ((ad.1 : ℝ) / ad.2) : ℝ) : ℂ) * (t : ℂ)) := by
    funext t
    rw [whittakerCoeff_eq_sum_antidiagonal _ hn, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ad had => by rw [hterm_exp ad had t]
  rw [hcongr, integral_finsetSum _ fun ad _ =>
    integrable_halfPlanePoisson_shift_mul_cexp hσ u.im (Real.log ((ad.1 : ℝ) / ad.2))]
  unfold resonantHeckeMoment
  refine Finset.sum_congr rfl fun ad had => ?_
  rw [integral_halfPlanePoisson_shift_mul_cexp hσ u.im (Real.log ((ad.1 : ℝ) / ad.2)), neg_neg]
  have ha_pos : 0 < ad.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal had)
  have hd_pos : 0 < ad.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal had)
  have haR : (0 : ℝ) < ad.1 := by exact_mod_cast ha_pos
  have hdR : (0 : ℝ) < ad.2 := by exact_mod_cast hd_pos
  by_cases hlt1 : ad.2 < ad.1
  · rw [if_pos hlt1]
    have hgt1 : 1 < (ad.1 : ℝ) / ad.2 := (one_lt_div hdR).mpr (by exact_mod_cast hlt1)
    have hlog_pos : 0 < Real.log ((ad.1 : ℝ) / ad.2) := Real.log_pos hgt1
    have hq0 : ((ad.1 : ℂ) / ad.2) ≠ 0 := div_ne_zero (by exact_mod_cast ha_pos.ne')
      (by exact_mod_cast hd_pos.ne')
    rw [abs_of_pos hlog_pos, Complex.cpow_def_of_ne_zero hq0,
      show ((ad.1 : ℂ) / ad.2) = (((ad.1 : ℝ) / ad.2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (by positivity)]
    congr 1
    apply Complex.ext <;> simp <;> ring
  · rw [if_neg hlt1]
    by_cases hlt2 : ad.1 < ad.2
    · rw [if_pos hlt2]
      have hgt1 : 1 < (ad.2 : ℝ) / ad.1 := (one_lt_div haR).mpr (by exact_mod_cast hlt2)
      have hlog_pos : 0 < Real.log ((ad.2 : ℝ) / ad.1) := Real.log_pos hgt1
      have hlog_inv : Real.log ((ad.1 : ℝ) / ad.2) = -Real.log ((ad.2 : ℝ) / ad.1) := by
        rw [Real.log_div haR.ne' hdR.ne', Real.log_div hdR.ne' haR.ne']; ring
      have hq0 : ((ad.2 : ℂ) / ad.1) ≠ 0 := div_ne_zero (by exact_mod_cast hd_pos.ne')
        (by exact_mod_cast ha_pos.ne')
      rw [hlog_inv, abs_neg, abs_of_pos hlog_pos, Complex.cpow_def_of_ne_zero hq0,
        show ((ad.2 : ℂ) / ad.1) = (((ad.2 : ℝ) / ad.1 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_log (by positivity)]
      congr 1
      apply Complex.ext <;> simp <;> ring
    · rw [if_neg hlt2]
      have heq : ad.1 = ad.2 := le_antisymm (not_lt.mp hlt1) (not_lt.mp hlt2)
      rw [heq, div_self hdR.ne', Real.log_one, abs_zero, mul_zero, mul_zero]
      simp

theorem continuous_whittakerCoeff_I_mul_real {n : ℕ} (hn : n ≠ 0) :
    Continuous fun t : ℝ => whittakerCoeff (I * (t : ℂ)) n := by
  have heq : (fun t : ℝ => whittakerCoeff (I * (t : ℂ)) n) = fun t : ℝ =>
      ∑ ad ∈ n.divisorsAntidiagonal,
        Complex.exp (Complex.log (ad.1 : ℂ) * (I * (t : ℂ))) *
          Complex.exp (Complex.log (ad.2 : ℂ) * (-(I * (t : ℂ)))) := by
    funext t
    rw [whittakerCoeff_eq_sum_antidiagonal _ hn]
    refine Finset.sum_congr rfl fun ad had => ?_
    have ha : (ad.1 : ℂ) ≠ 0 :=
      by exact_mod_cast (Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal had)).ne'
    have hd : (ad.2 : ℂ) ≠ 0 :=
      by exact_mod_cast (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal had)).ne'
    rw [Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hd]
  rw [heq]
  exact continuous_finsetSum _ fun _ _ => by fun_prop

theorem norm_whittakerCoeff_I_mul_real_le {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ‖whittakerCoeff (I * (t : ℂ)) n‖ ≤ n.divisorsAntidiagonal.card := by
  rw [whittakerCoeff_eq_sum_antidiagonal _ hn]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ ad ∈ n.divisorsAntidiagonal,
        ‖(ad.1 : ℂ) ^ (I * (t : ℂ)) * (ad.2 : ℂ) ^ (-(I * (t : ℂ)))‖
      ≤ ∑ _ad ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
        refine Finset.sum_le_sum fun ad had => ?_
        have ha := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal had)
        have hd := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal had)
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos ha, Complex.norm_natCast_cpow_of_pos hd]
        simp
    _ = n.divisorsAntidiagonal.card := by simp

/-- The multiplicative Hecke `C*`-square expectation `ω_u(A* A)` for `A = Σ_{m ∈ S} c_m T_m`. -/
def resonantHeckeStarSquare (u : ℂ) (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ m ∈ S, ∑ k ∈ S, starRingEnd ℂ (c m) * c k *
    ∑ d ∈ (Nat.gcd m k).divisors, resonantHeckeMoment u (m * k / d ^ 2)

/-- **Multiplicative Hecke `C*`-positivity no-go identity.** For *every* `u` with `Re u < 0`
(including off-line parameters `Re u ≠ -1/4`), the resonant `C*`-square expectation of any finite
Hecke combination equals its weighted `L²` norm against the positive Poisson density. -/
theorem resonantHeckeStarSquare_eq_poisson_integral {u : ℂ} (hu : u.re < 0)
    {S : Finset ℕ} (hS : ∀ m ∈ S, m ≠ 0) (c : ℕ → ℂ) :
    resonantHeckeStarSquare u S c =
      ((∫ t : ℝ, halfPlanePoisson (-u.re) (t - u.im) *
        ‖∑ m ∈ S, c m * whittakerCoeff (I * (t : ℂ)) m‖ ^ 2 : ℝ) : ℂ) := by
  have hσ : 0 < -u.re := neg_pos.mpr hu
  have hP : Integrable (fun t : ℝ => (halfPlanePoisson (-u.re) (t - u.im) : ℂ)) :=
    ((integrable_halfPlanePoisson hσ).comp_sub_right u.im).ofReal
  have hW_int : ∀ m ∈ S, ∀ k ∈ S, Integrable fun t : ℝ =>
      starRingEnd ℂ (c m) * c k *
        ((halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          (whittakerCoeff (I * (t : ℂ)) m * whittakerCoeff (I * (t : ℂ)) k)) := by
    intro m hm k hk
    have hbd : ∀ t : ℝ, ‖whittakerCoeff (I * (t : ℂ)) m * whittakerCoeff (I * (t : ℂ)) k‖ ≤
        (m.divisorsAntidiagonal.card : ℝ) * (k.divisorsAntidiagonal.card : ℝ) := fun t => by
      rw [norm_mul]
      exact mul_le_mul (norm_whittakerCoeff_I_mul_real_le (hS m hm) t)
        (norm_whittakerCoeff_I_mul_real_le (hS k hk) t) (norm_nonneg _) (by positivity)
    exact (hP.mul_bdd
      ((continuous_whittakerCoeff_I_mul_real (hS m hm)).mul
        (continuous_whittakerCoeff_I_mul_real (hS k hk))).aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)).const_mul _
  -- Step 1: replace the inner gcd-divisor sum by the integral of `W_{it}(m) W_{it}(k)`
  have dinner : ∀ m ∈ S, ∀ k ∈ S,
      (∑ d ∈ (Nat.gcd m k).divisors, resonantHeckeMoment u (m * k / d ^ 2)) =
        ∫ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          (whittakerCoeff (I * (t : ℂ)) m * whittakerCoeff (I * (t : ℂ)) k) := by
    intro m hm k hk
    have hmk_pos : 0 < m * k := mul_pos (Nat.pos_of_ne_zero (hS m hm))
      (Nat.pos_of_ne_zero (hS k hk))
    have hd_ne : ∀ d ∈ (Nat.gcd m k).divisors, m * k / d ^ 2 ≠ 0 := fun d hd => by
      have hdg := (Nat.mem_divisors.mp hd).1
      have hd_pos := Nat.pos_of_mem_divisors hd
      have hd2 : d ^ 2 ∣ m * k := by
        rw [sq]
        exact mul_dvd_mul (hdg.trans (Nat.gcd_dvd_left m k)) (hdg.trans (Nat.gcd_dvd_right m k))
      exact (Nat.div_pos (Nat.le_of_dvd hmk_pos hd2) (pow_pos hd_pos 2)).ne'
    have hcongr_sum : (∑ d ∈ (Nat.gcd m k).divisors, resonantHeckeMoment u (m * k / d ^ 2)) =
        ∑ d ∈ (Nat.gcd m k).divisors,
          ∫ t : ℝ, (halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
            whittakerCoeff (I * (t : ℂ)) (m * k / d ^ 2) :=
      Finset.sum_congr rfl fun d hd => resonantHeckeMoment_eq_poisson_integral hu (hd_ne d hd)
    rw [hcongr_sum, ← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      rw [← Finset.mul_sum, ← whittakerCoeff_mul_eq_sum_gcd_divisors _ (hS m hm) (hS k hk)]
    · intro d hd
      exact hP.mul_bdd (continuous_whittakerCoeff_I_mul_real (hd_ne d hd)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => norm_whittakerCoeff_I_mul_real_le (hd_ne d hd) t)
  -- Step 2: sum over `m, k ∈ S` and fold into `‖Σ_{m ∈ S} c_m W_{it}(m)‖²`
  unfold resonantHeckeStarSquare
  have houter : (∑ m ∈ S, ∑ k ∈ S, starRingEnd ℂ (c m) * c k *
      ∑ d ∈ (Nat.gcd m k).divisors, resonantHeckeMoment u (m * k / d ^ 2)) =
      ∑ m ∈ S, ∑ k ∈ S, ∫ t : ℝ, starRingEnd ℂ (c m) * c k *
        ((halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          (whittakerCoeff (I * (t : ℂ)) m * whittakerCoeff (I * (t : ℂ)) k)) :=
    Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun k hk => by
      rw [dinner m hm k hk, ← integral_const_mul]
  rw [houter]
  have hswap1 : ∀ m ∈ S,
      (∑ k ∈ S, ∫ t : ℝ, starRingEnd ℂ (c m) * c k *
        ((halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          (whittakerCoeff (I * (t : ℂ)) m * whittakerCoeff (I * (t : ℂ)) k))) =
      ∫ t : ℝ, ∑ k ∈ S, starRingEnd ℂ (c m) * c k *
        ((halfPlanePoisson (-u.re) (t - u.im) : ℂ) *
          (whittakerCoeff (I * (t : ℂ)) m * whittakerCoeff (I * (t : ℂ)) k)) :=
    fun m hm => (integral_finsetSum S fun k hk => hW_int m hm k hk).symm
  rw [Finset.sum_congr rfl hswap1, ← integral_finsetSum S fun m hm =>
    integrable_finsetSum S fun k hk => hW_int m hm k hk, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  set Z : ℂ := ∑ m ∈ S, c m * whittakerCoeff (I * (t : ℂ)) m with hZ
  have hnormZ : ((‖Z‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ Z * Z := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm]
  have hconjZ : starRingEnd ℂ Z = ∑ m ∈ S, starRingEnd ℂ (c m) * whittakerCoeff (I * (t : ℂ)) m := by
    rw [hZ, map_sum]
    exact Finset.sum_congr rfl fun m hm => by
      rw [map_mul, conj_whittakerCoeff_I_mul_real t (hS m hm)]
  rw [Complex.ofReal_mul, hnormZ, hconjZ, hZ, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Nonnegativity of every Hecke `C*`-square on `Re u < 0`.** Off-line zeros (`Re u ≠ -1/4`)
cannot violate `C*`-positivity on the multiplicative Hecke algebra. -/
theorem resonantHeckeStarSquare_re_nonneg {u : ℂ} (hu : u.re < 0)
    {S : Finset ℕ} (hS : ∀ m ∈ S, m ≠ 0) (c : ℕ → ℂ) :
    0 ≤ (resonantHeckeStarSquare u S c).re := by
  rw [resonantHeckeStarSquare_eq_poisson_integral hu hS c, Complex.ofReal_re]
  refine integral_nonneg fun t => ?_
  exact mul_nonneg (halfPlanePoisson_pos (neg_pos.mpr hu) _).le (sq_nonneg _)

theorem resonantHeckeStarSquare_im_eq_zero {u : ℂ} (hu : u.re < 0)
    {S : Finset ℕ} (hS : ∀ m ∈ S, m ≠ 0) (c : ℕ → ℂ) :
    (resonantHeckeStarSquare u S c).im = 0 := by
  rw [resonantHeckeStarSquare_eq_poisson_integral hu hS c, Complex.ofReal_im]

/-! ### Exact `L²(𝒟)` Hecke eigen-defect dispersion at all strip zeros and single-prime RH criteria -/

/-- Inside `0 < Re ρ < 1`, `reflectedCompletedLambda ρ = 0` iff `riemannZeta ρ = 0`. -/
theorem reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip {ρ : ℂ}
    (h0 : 0 < ρ.re) :
    reflectedCompletedLambda ρ = 0 ↔ riemannZeta ρ = 0 := by
  unfold reflectedCompletedLambda
  exact mul_eq_zero_iff_left (Complex.Gammaℝ_ne_zero_of_re_pos h0)

/-- Every zero of `reflectedCompletedLambda` in the open critical strip `0 < Re ρ < 1` is nonreal. -/
theorem im_ne_zero_of_reflectedCompletedLambda_eq_zero {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.im ≠ 0 := by
  intro him
  have hζ : riemannZeta ρ = 0 :=
    (reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip h0).mp hρ
  have hreal : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hreal] at hζ
  exact riemannZeta_real_strip_ne_zero h0 h1 hζ

/-- **Truncated `L²(𝒟)` norm at every strip zero of `Λ`** (both `Im ρ > 0` and `Im ρ < 0`). -/
theorem integral_norm_sq_resonantState_all {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 =
      ‖reflectedCompletedLambda (ρ - 1)‖ ^ 2 * Y ^ (1 - ρ.re) / (1 - ρ.re) := by
  have him : ρ.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_eq_zero hρ h0 h1
  rcases lt_or_gt_of_ne him with hneg | hpos
  · set σ := starRingEnd ℂ ρ with hσ
    have hσz : reflectedCompletedLambda σ = 0 := by
      rw [hσ, reflectedCompletedLambda_conj, hρ, map_zero]
    have hσ0 : 0 < σ.re := by simpa [hσ] using h0
    have hσ1 : σ.re < 1 := by simpa [hσ] using h1
    have hσi : 0 < σ.im := by simp [hσ]; linarith
    have h := integral_norm_sq_resonantState hσz hσ0 hσ1 hσi hY
    have hlhs : ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 =
        ∫ z in fd, ‖truncatedLineModel (resonantParameter σ) Y z‖ ^ 2 := by
      refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
      have hρσ : ρ = starRingEnd ℂ σ := by rw [hσ, Complex.conj_conj]
      rw [hρσ, resonantParameter_conj, ← truncatedLineModel_conj, Complex.norm_conj]
    have hrhs : ‖reflectedCompletedLambda (σ - 1)‖ = ‖reflectedCompletedLambda (ρ - 1)‖ := by
      have : σ - 1 = starRingEnd ℂ (ρ - 1) := by simp [hσ]
      rw [this, reflectedCompletedLambda_conj, Complex.norm_conj]
    rw [hlhs, h, hrhs]
    simp [hσ]
  · exact integral_norm_sq_resonantState hρ h0 h1 hpos hY

theorem integral_norm_sq_resonantState_pos {ρ : ℂ} (hρ : reflectedCompletedLambda ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {Y : ℝ} (hY : 1 ≤ Y) :
    0 < ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 := by
  rw [integral_norm_sq_resonantState_all hρ h0 h1 hY]
  have him : ρ.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_eq_zero hρ h0 h1
  have hne : reflectedCompletedLambda (ρ - 1) ≠ 0 := reflectedCompletedLambda_sub_one_ne_zero h1 him
  have hn : 0 < ‖reflectedCompletedLambda (ρ - 1)‖ := norm_pos_iff.mpr hne
  have hY0 : 0 < Y := by linarith
  have h1r : 0 < 1 - ρ.re := by linarith
  positivity

/-- **Second Hecke moment at every strip zero of `Λ`** (both `Im ρ > 0` and `Im ρ < 0`). -/
theorem heckeSecondMoment_resonantZero_re {p : ℕ} (hp : p.Prime) {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    ∫ z in fd, ‖heckeTruncated p (resonantParameter ρ) Y z‖ ^ 2 =
      (2 + 2 * ((p : ℂ) ^ (2 * resonantParameter ρ)).re) *
        ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 := by
  have him : ρ.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_eq_zero hρ h0 h1
  rcases lt_or_gt_of_ne him with hneg | hpos
  · set σ := starRingEnd ℂ ρ with hσ
    have hσz : reflectedCompletedLambda σ = 0 := by
      rw [hσ, reflectedCompletedLambda_conj, hρ, map_zero]
    have hσ0 : 0 < σ.re := by simpa [hσ] using h0
    have hσ1 : σ.re < 1 := by simpa [hσ] using h1
    have hσi : 0 < σ.im := by simp [hσ]; linarith
    have h := heckeSecondMoment_resonant_re hp (resonantParameter_mem hσ0 hσi)
      (resonantParameter_re_neg hσ1) (by rw [msA_resonantParameter]; exact hσz) hY
    have hlhs : ∫ z in fd, ‖heckeTruncated p (resonantParameter ρ) Y z‖ ^ 2 =
        ∫ z in fd, ‖heckeTruncated p (resonantParameter σ) Y z‖ ^ 2 := by
      refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
      have hρσ : ρ = starRingEnd ℂ σ := by rw [hσ, Complex.conj_conj]
      rw [hρσ, resonantParameter_conj, ← heckeTruncated_conj hp.pos, Complex.norm_conj]
    have hrhs_int : ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 =
        ∫ z in fd, ‖truncatedLineModel (resonantParameter σ) Y z‖ ^ 2 := by
      refine setIntegral_congr_fun isClosed_fd.measurableSet fun z _ => ?_
      have hρσ : ρ = starRingEnd ℂ σ := by rw [hσ, Complex.conj_conj]
      rw [hρσ, resonantParameter_conj, ← truncatedLineModel_conj, Complex.norm_conj]
    have hrhs_re : ((p : ℂ) ^ (2 * resonantParameter σ)).re =
        ((p : ℂ) ^ (2 * resonantParameter ρ)).re := by
      have : 2 * resonantParameter σ = starRingEnd ℂ (2 * resonantParameter ρ) := by
        rw [hσ, resonantParameter_conj, map_mul, map_ofNat]
      rw [this, Complex.cpow_conj _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
        Complex.conj_natCast, Complex.conj_re]
    rw [hlhs, h, hrhs_re, hrhs_int]
  · exact heckeSecondMoment_resonant_re hp (resonantParameter_mem h0 hpos)
      (resonantParameter_re_neg h1) (by rw [msA_resonantParameter]; exact hρ) hY

/-- The Hecke eigen-defect `T_p Λ^Y E_u − (p^u + p^{ū}) Λ^Y E_u` of a truncated line model. -/
def heckeEigenDefect (p : ℕ) (u : ℂ) (Y : ℝ) (z : ℍ) : ℂ :=
  heckeTruncated p u Y z -
    ((p : ℂ) ^ u + (p : ℂ) ^ (starRingEnd ℂ u)) * truncatedLineModel u Y z

/-- **Exact `L²(𝒟)` Hecke eigen-defect dispersion law.** At every strip zero `ρ` of `Λ`, every
prime `p`, and every height `Y ≥ p`, the normalized `L²(𝒟)` Hecke eigen-defect equals
`2 (1 − p^{Re ρ − 1})`, independent of `Y` and independent of `Im ρ`. -/
theorem integral_norm_sq_heckeEigenDefect_resonantZero {p : ℕ} (hp : p.Prime) {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    ∫ z in fd, ‖heckeEigenDefect p (resonantParameter ρ) Y z‖ ^ 2 =
      2 * (1 - (p : ℝ) ^ (ρ.re - 1)) *
        ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 := by
  have him : ρ.im ≠ 0 := im_ne_zero_of_reflectedCompletedLambda_eq_zero hρ h0 h1
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
    linarith
  have hY0 : 0 < Y := by linarith
  set u := resonantParameter ρ with hu_def
  set μ : ℝ := 2 * ((p : ℂ) ^ u).re with hμ_def
  have hμ_coe : (p : ℂ) ^ u + (p : ℂ) ^ (starRingEnd ℂ u) = (μ : ℂ) := by
    rw [← conj_natCast_cpow, Complex.add_conj, hμ_def]
  -- Pointwise expansion of `‖a − μ b‖²`
  have hpt : ∀ z : ℍ, ‖heckeEigenDefect p u Y z‖ ^ 2 =
      ‖heckeTruncated p u Y z‖ ^ 2 -
        2 * μ * (heckeTruncated p u Y z * starRingEnd ℂ (truncatedLineModel u Y z)).re +
        μ ^ 2 * ‖truncatedLineModel u Y z‖ ^ 2 := by
    intro z
    unfold heckeEigenDefect
    rw [hμ_coe]
    set a := heckeTruncated p u Y z
    set b := truncatedLineModel u Y z
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  -- Integrability of the three real pieces on `fd`
  have hiT : IntegrableOn (fun z : ℍ => ‖heckeTruncated p u Y z‖ ^ 2) fd := by
    obtain ⟨M, _, hM⟩ := exists_bound_heckeRemainder hp.pos u hY0
    set lam : ℂ := (p : ℂ) ^ u + (p : ℂ) ^ (-u)
    have hm : Measurable (fun z : ℍ => ‖heckeTruncated p u Y z‖ ^ 2) := by
      simp_rw [heckeTruncated_eq hp u Y]
      exact ((measurable_const.mul (measurable_truncatedLineModel u Y)).add
        (measurable_heckeRemainder_im p u Y)).norm.pow_const 2
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hm.aestronglyMeasurable
      (M := (‖lam‖ * truncBound' u Y + M) ^ 2) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), heckeTruncated_eq hp u Y z]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖lam * truncatedLineModel u Y z + heckeRemainder p u Y z.im‖
        ≤ ‖lam * truncatedLineModel u Y z‖ + ‖heckeRemainder p u Y z.im‖ := norm_add_le _ _
      _ ≤ ‖lam‖ * truncBound' u Y + M := by
        rw [norm_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (norm_truncatedLineModel_le_truncBound' u hY1 hz) (norm_nonneg _))
          (hM z.im)
  have hiB : IntegrableOn (fun z : ℍ => ‖truncatedLineModel u Y z‖ ^ 2) fd := by
    refine Measure.integrableOn_of_bounded volume_fd_ne_top
      ((measurable_truncatedLineModel u Y).norm.pow_const 2).aestronglyMeasurable
      (M := truncBound' u Y ^ 2) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_truncatedLineModel_le_truncBound' u hY1 hz) 2
  have hi_cx : IntegrableOn
      (fun z : ℍ => heckeTruncated p u Y z * starRingEnd ℂ (truncatedLineModel u Y z)) fd := by
    obtain ⟨M, _, hM⟩ := exists_bound_heckeRemainder hp.pos u hY0
    set lam : ℂ := (p : ℂ) ^ u + (p : ℂ) ^ (-u)
    have hm : Measurable (fun z : ℍ =>
        heckeTruncated p u Y z * starRingEnd ℂ (truncatedLineModel u Y z)) := by
      simp_rw [heckeTruncated_eq hp u Y]
      exact ((measurable_const.mul (measurable_truncatedLineModel u Y)).add
        (measurable_heckeRemainder_im p u Y)).mul
        (Complex.continuous_conj.measurable.comp (measurable_truncatedLineModel u Y))
    refine Measure.integrableOn_of_bounded volume_fd_ne_top hm.aestronglyMeasurable
      (M := (‖lam‖ * truncBound' u Y + M) * truncBound' u Y) ?_
    refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    rw [norm_mul, Complex.norm_conj, heckeTruncated_eq hp u Y z]
    refine mul_le_mul ?_ (norm_truncatedLineModel_le_truncBound' u hY1 hz) (norm_nonneg _) ?_
    · calc ‖lam * truncatedLineModel u Y z + heckeRemainder p u Y z.im‖
          ≤ ‖lam * truncatedLineModel u Y z‖ + ‖heckeRemainder p u Y z.im‖ := norm_add_le _ _
        _ ≤ ‖lam‖ * truncBound' u Y + M := by
          rw [norm_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (norm_truncatedLineModel_le_truncBound' u hY1 hz) (norm_nonneg _))
            (hM z.im)
    · have := (norm_nonneg (truncatedLineModel u Y z)).trans
        (norm_truncatedLineModel_le_truncBound' u hY1 hz)
      positivity
  have hiC : IntegrableOn
      (fun z : ℍ => (heckeTruncated p u Y z * starRingEnd ℂ (truncatedLineModel u Y z)).re) fd :=
    hi_cx.re
  -- Integrate termwise and substitute the first and second resonant moments
  have hint_eq : ∫ z in fd, ‖heckeEigenDefect p u Y z‖ ^ 2 =
      (∫ z in fd, ‖heckeTruncated p u Y z‖ ^ 2) -
        2 * μ * (∫ z in fd, (heckeTruncated p u Y z * starRingEnd ℂ (truncatedLineModel u Y z)).re) +
        μ ^ 2 * ∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 := by
    simp_rw [hpt]
    have h1 := integral_add (hiT.sub (hiC.const_mul (2 * μ))) (hiB.const_mul (μ ^ 2))
    have h2 := integral_sub hiT (hiC.const_mul (2 * μ))
    simp only [Pi.sub_apply] at h1 h2
    rw [h1, h2, integral_const_mul, integral_const_mul]
  have hmom1 : ∫ z in fd,
      (heckeTruncated p u Y z * starRingEnd ℂ (truncatedLineModel u Y z)).re =
      μ * ∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2 := by
    have hre_int : ∫ z in fd,
        (heckeTruncated p u Y z * starRingEnd ℂ (truncatedLineModel u Y z)).re =
        (heckeHermitianMoment p u Y).re :=
      Complex.reCLM.integral_comp_comm hi_cx
    rw [hre_int, hu_def, heckeHermitianMoment_resonantZero_re hp hρ h0 h1 him hY, Complex.ofReal_re,
      ← integral_norm_sq_resonantState_all hρ h0 h1 hY1, ← hu_def, ← hμ_def]
  rw [hint_eq, hmom1, hu_def, heckeSecondMoment_resonantZero_re hp hρ h0 h1 hY, ← hu_def]
  -- Phase cancellation: `2 + 2 Re(q²) − 4 (Re q)² = 2 (1 − ‖q‖²) = 2 (1 − p^{Re ρ − 1})`
  set q : ℂ := (p : ℂ) ^ u with hq
  have hq2 : (p : ℂ) ^ (2 * u) = q ^ 2 := by
    rw [hq, show (2 : ℂ) * u = ((2 : ℕ) : ℂ) * u by push_cast; ring, Complex.cpow_nat_mul]
  have hq_norm : ‖q‖ ^ 2 = (p : ℝ) ^ (ρ.re - 1) := by
    rw [hq, Complex.norm_natCast_cpow_of_pos hp.pos, rpow_re_sq (by exact_mod_cast hp.pos)]
    congr 1
    simp [hu_def, resonantParameter]
    ring
  have hphase : 2 + 2 * (q ^ 2).re - 2 * μ * μ + μ ^ 2 = 2 * (1 - ‖q‖ ^ 2) := by
    rw [hμ_def, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq q, Complex.mul_re]
    ring
  rw [hq2, ← hq_norm]
  linear_combination (∫ z in fd, ‖truncatedLineModel u Y z‖ ^ 2) * hphase

/-- **Strict positivity of the `L²(𝒟)` Hecke eigen-defect at every strip zero.** -/
theorem integral_norm_sq_heckeEigenDefect_resonantZero_pos {p : ℕ} (hp : p.Prime) {ρ : ℂ}
    (hρ : reflectedCompletedLambda ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {Y : ℝ} (hY : (p : ℝ) ≤ Y) :
    0 < ∫ z in fd, ‖heckeEigenDefect p (resonantParameter ρ) Y z‖ ^ 2 := by
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
    linarith
  rw [integral_norm_sq_heckeEigenDefect_resonantZero hp hρ h0 h1 hY]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlt : (p : ℝ) ^ (ρ.re - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  exact mul_pos (by linarith) (integral_norm_sq_resonantState_pos hρ h0 h1 hY1)

/-- **Reflection symmetry of the normalized Hecke eigen-defect characterizes the critical line.** -/
theorem heckeEigenDefect_rate_eq_reflect_iff {p : ℕ} (hp : p.Prime) (ρ : ℂ) :
    2 * (1 - (p : ℝ) ^ (ρ.re - 1)) = 2 * (1 - (p : ℝ) ^ ((1 - ρ).re - 1)) ↔ ρ.re = 1 / 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simp only [Complex.sub_re, Complex.one_re]
  constructor
  · intro h
    have hrpow : (p : ℝ) ^ (ρ.re - 1) = (p : ℝ) ^ (1 - ρ.re - 1) := by linarith
    have hexp := (Real.rpow_right_inj (by positivity) hp1.ne').mp hrpow
    linarith
  · intro h
    rw [h]
    norm_num

/-- **Single-prime, single-height upper Hecke dispersion criterion for RH.** For *any* prime `p`
and *any* height `Y ≥ p`, RH holds iff every strip zero `ρ` of `Λ` has normalized `L²(𝒟)` Hecke
eigen-defect at most `2 (1 − p^{-1/2})`. -/
theorem riemannHypothesis_iff_heckeEigenDefect_le {p : ℕ} (hp : p.Prime) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) :
    RiemannHypothesis ↔ ∀ ρ : ℂ, reflectedCompletedLambda ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      ∫ z in fd, ‖heckeEigenDefect p (resonantParameter ρ) Y z‖ ^ 2 ≤
        2 * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
    linarith
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_re_lt_half]
  constructor
  · intro hRH ρ hρ h0 h1
    rw [integral_norm_sq_heckeEigenDefect_resonantZero hp hρ h0 h1 hY]
    have hζ : riemannZeta ρ = 0 :=
      (reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip h0).mp hρ
    have hge : 1 / 2 ≤ ρ.re := by
      by_contra hlt
      exact hRH ρ h0 (not_le.mp hlt) hζ
    have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ (ρ.re - 1) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith)
      (integral_norm_sq_resonantState_pos hρ h0 h1 hY1).le
  · intro hle ρ h0 hlt hζ
    have h1 : ρ.re < 1 := by linarith
    have hρ : reflectedCompletedLambda ρ = 0 :=
      (reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip h0).mpr hζ
    have hbound := hle ρ hρ h0 h1
    rw [integral_norm_sq_heckeEigenDefect_resonantZero hp hρ h0 h1 hY] at hbound
    have hN := integral_norm_sq_resonantState_pos hρ h0 h1 hY1
    have hrate : 2 * (1 - (p : ℝ) ^ (ρ.re - 1)) ≤ 2 * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) :=
      le_of_mul_le_mul_right hbound hN
    have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ (ρ.re - 1) := by linarith
    have hexp : -(1 / 2 : ℝ) ≤ ρ.re - 1 :=
      (Real.rpow_le_rpow_left_iff hp1).mp hpow
    linarith

/-- **Single-prime, single-height lower Hecke dispersion criterion for RH.** Because an off-line
zero pair `{ρ, 1 − ρ}` splits strictly on both sides of `2 (1 − p^{-1/2})`, the reverse inequality
`≥ 2 (1 − p^{-1/2})` at every strip zero is *also* equivalent to RH. -/
theorem riemannHypothesis_iff_heckeEigenDefect_ge {p : ℕ} (hp : p.Prime) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) :
    RiemannHypothesis ↔ ∀ ρ : ℂ, reflectedCompletedLambda ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      2 * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 ≤
        ∫ z in fd, ‖heckeEigenDefect p (resonantParameter ρ) Y z‖ ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
    linarith
  rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro hRH ρ hρ h0 h1
    rw [integral_norm_sq_heckeEigenDefect_resonantZero hp hρ h0 h1 hY]
    have hζ : riemannZeta ρ = 0 :=
      (reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip h0).mp hρ
    have hle : ρ.re ≤ 1 / 2 := by
      by_contra hgt
      exact hRH ρ (not_le.mp hgt) h1 hζ
    have hpow : (p : ℝ) ^ (ρ.re - 1) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith)
      (integral_norm_sq_resonantState_pos hρ h0 h1 hY1).le
  · intro hge ρ hgt h1 hζ
    have h0 : 0 < ρ.re := by linarith
    have hρ : reflectedCompletedLambda ρ = 0 :=
      (reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip h0).mpr hζ
    have hbound := hge ρ hρ h0 h1
    rw [integral_norm_sq_heckeEigenDefect_resonantZero hp hρ h0 h1 hY] at hbound
    have hN := integral_norm_sq_resonantState_pos hρ h0 h1 hY1
    have hrate : 2 * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ))) ≤ 2 * (1 - (p : ℝ) ^ (ρ.re - 1)) :=
      le_of_mul_le_mul_right hbound hN
    have hpow : (p : ℝ) ^ (ρ.re - 1) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
    have hexp : ρ.re - 1 ≤ -(1 / 2 : ℝ) :=
      (Real.rpow_le_rpow_left_iff hp1).mp hpow
    linarith

/-- **Single-prime Hecke dispersion characterization of `XiZeroHalfPlaneBound β`.** -/
theorem xiZeroHalfPlaneBound_iff_heckeEigenDefect_le {p : ℕ} (hp : p.Prime) {Y : ℝ}
    (hY : (p : ℝ) ≤ Y) (β : ℝ) :
    XiZeroHalfPlaneBound β ↔ ∀ ρ : ℂ, reflectedCompletedLambda ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      ∫ z in fd, ‖heckeEigenDefect p (resonantParameter ρ) Y z‖ ^ 2 ≤
        2 * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ) - β)) *
          ∫ z in fd, ‖truncatedLineModel (resonantParameter ρ) Y z‖ ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.pos
    linarith
  rw [xiZeroHalfPlaneBound_iff_zetaZeroConfig_re_le]
  constructor
  · intro hbound ρ hρ h0 h1
    rw [integral_norm_sq_heckeEigenDefect_resonantZero hp hρ h0 h1 hY]
    have hζ : riemannZeta ρ = 0 :=
      (reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip h0).mp hρ
    have hmem : ρ ∈ Zeta23.zetaZeroConfig.carrier := by
      refine ⟨hζ, h0, h1⟩
    have hrefl : Zeta23.reflect ρ ∈ Zeta23.zetaZeroConfig.carrier :=
      Zeta23.zetaZeroConfig.reflect_mem ρ hmem
    have hle := hbound (Zeta23.reflect ρ) hrefl
    rw [Zeta23.reflect_re] at hle
    have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ) - β) ≤ (p : ℝ) ^ (ρ.re - 1) :=
      Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith)
      (integral_norm_sq_resonantState_pos hρ h0 h1 hY1).le
  · intro hle ρ hmem
    have hrefl : Zeta23.reflect ρ ∈ Zeta23.zetaZeroConfig.carrier :=
      Zeta23.zetaZeroConfig.reflect_mem ρ hmem
    set σ := Zeta23.reflect ρ
    have h0 : 0 < σ.re := hrefl.2.1
    have h1 : σ.re < 1 := hrefl.2.2
    have hσ : reflectedCompletedLambda σ = 0 :=
      (reflectedCompletedLambda_eq_zero_iff_riemannZeta_eq_zero_of_strip h0).mpr hrefl.1
    have hbound := hle σ hσ h0 h1
    rw [integral_norm_sq_heckeEigenDefect_resonantZero hp hσ h0 h1 hY] at hbound
    have hN := integral_norm_sq_resonantState_pos hσ h0 h1 hY1
    have hrate : 2 * (1 - (p : ℝ) ^ (σ.re - 1)) ≤ 2 * (1 - (p : ℝ) ^ (-(1 / 2 : ℝ) - β)) :=
      le_of_mul_le_mul_right hbound hN
    have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ) - β) ≤ (p : ℝ) ^ (σ.re - 1) := by linarith
    have hexp : -(1 / 2 : ℝ) - β ≤ σ.re - 1 :=
      (Real.rpow_le_rpow_left_iff hp1).mp hpow
    have hσre : σ.re = 1 - ρ.re := Zeta23.reflect_re ρ
    linarith

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
