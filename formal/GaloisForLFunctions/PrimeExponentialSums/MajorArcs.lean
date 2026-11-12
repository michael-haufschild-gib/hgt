import GaloisForLFunctions.PrimeExponentialSums.PrimeSumsByParts
import GaloisForLFunctions.RHTower.SelbergClass.DirichletFourier
import GaloisForLFunctions.goldbach.ModularInverseRectangleCompletion

/-!
# Major arcs: Dirichlet characters and Siegel–Walfisz

On residues prime to `q`, the additive phase `x ↦ e(ux/q)` expands in Dirichlet characters:

`e(ux/q) = φ(q)⁻¹ Σ_χ c_χ χ(x)`,  `c_χ = Σ_x χ̄(x) e(ux/q)`.

For a unit `u` the principal coefficient is the Ramanujan sum `c_q(u) = μ(q)`, of modulus at most
one; every coefficient has `|c_χ| ≤ q`. Hence, for weights `w` on integers prime to `q`
(`norm_sum_addPhase_le`),

`|Σ e(un/q) w(n)| ≤ |Σ w(n)|/φ(q) + q · max_{χ ≠ 1} |Σ χ(n) w(n)|`.

A nonprincipal character agrees on integers prime to `q` with its primitive character, so
Siegel–Walfisz in short windows (`siegelWalfisz_window`) and Abel summation
(`norm_sum_primes_le_of_windows`) bound `Σ_{N < p ≤ Q} χ(p) e(pθ)` for every modulus
`q ≤ (log N)^B` (`exists_norm_sum_primes_char_le`).
-/

open Finset ArithmeticFunction Filter
open GaloisForLFunctions.LogarithmicChowla
open GaloisForLFunctions.ShortIntervalPrimesInProgressions (psiChi twistedVM)

namespace GaloisForLFunctions.PrimeExponentialSums

noncomputable section
set_option autoImplicit false

section Expansion

variable {q : ℕ} [NeZero q]

/-- The additive phase `x ↦ e(ux/q)` on `ZMod q`. -/
def addPhase (u : ZMod q) (x : ZMod q) : ℂ := ZMod.stdAddChar (u * x)

/-- `e(an/q)` as an additive phase. -/
theorem addPhase_natCast (a n : ℕ) : addPhase (a : ZMod q) (n : ZMod q) = ex (a * n / q) := by
  have h : ((a : ZMod q) * (n : ZMod q)) = (((a * n : ℕ) : ℤ) : ZMod q) := by push_cast; ring
  rw [addPhase, h, ZMod.stdAddChar_coe, ex]
  congr 1
  push_cast
  ring

/-- The character coefficient `c_χ = Σ_x χ̄(x) e(ux/q)`. -/
def phaseCoeff (u : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  RHTower.dirichletCharacterFourierCoeff (addPhase u) χ

/-- `|c_χ| ≤ q`. -/
theorem norm_phaseCoeff_le (u : ZMod q) (χ : DirichletCharacter ℂ q) : ‖phaseCoeff u χ‖ ≤ q := by
  rw [phaseCoeff, RHTower.dirichletCharacterFourierCoeff]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x : ZMod q, ‖χ⁻¹ x * addPhase u x‖ ≤ ∑ _x : ZMod q, (1 : ℝ) := by
        refine sum_le_sum fun x _ => ?_
        rw [norm_mul, addPhase, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
        exact DirichletCharacter.norm_le_one _ x
    _ = q := by rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/-- The principal coefficient of a unit phase is a Kloosterman sum at frequency zero. -/
theorem phaseCoeff_one_eq (u : (ZMod q)ˣ) :
    phaseCoeff (u : ZMod q) 1 = RHTower.Sieve.kloostermanSum q u 0 := by
  classical
  rw [phaseCoeff, RHTower.dirichletCharacterFourierCoeff, inv_one, RHTower.Sieve.kloostermanSum]
  have h1 : ∀ x : ZMod q, (1 : DirichletCharacter ℂ q) x * addPhase (u : ZMod q) x
      = if IsUnit x then addPhase (u : ZMod q) x else 0 := by
    intro x
    split_ifs with hx
    · rw [MulChar.one_apply hx, one_mul]
    · rw [MulChar.map_nonunit _ hx, zero_mul]
  rw [sum_congr rfl fun x _ => h1 x, ← sum_filter]
  have hmap : (univ : Finset (ZMod q)).filter IsUnit
      = univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q), Units.val_injective⟩ := by
    ext a
    simp [IsUnit]
  rw [hmap, sum_map]
  refine sum_congr rfl fun x _ => ?_
  simp [RHTower.Sieve.kloostermanPhase, addPhase]

/-- **Ramanujan sum.** `|c_1| = |μ(q)| ≤ 1` for a unit phase. -/
theorem norm_phaseCoeff_one_le (u : (ZMod q)ˣ) : ‖phaseCoeff (u : ZMod q) 1‖ ≤ 1 := by
  rw [phaseCoeff_one_eq]
  exact Goldbach.norm_kloostermanSum_unit_zero_le ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ u

/-- Finite Fourier inversion of the phase on a unit residue. -/
theorem addPhase_eq_sum (u : ZMod q) {n : ZMod q} (hn : IsUnit n) :
    addPhase u n = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, phaseCoeff u χ * χ n := by
  have h := RHTower.dirichletCharacterFourier_expansion (addPhase u) n
  rwa [MulChar.one_apply hn, one_mul] at h

/-- **Major-arc expansion.** For weights `w` on a finite set of integers prime to `q` and a unit
`u`: `|Σ e(un/q) w(n)| ≤ |Σ w(n)|/φ(q) + q D` whenever every nonprincipal twist
`|Σ χ(n) w(n)|` is at most `D`. -/
theorem norm_sum_addPhase_le (u : (ZMod q)ˣ) (S : Finset ℕ) (hS : ∀ n ∈ S, IsUnit (n : ZMod q))
    (w : ℕ → ℂ) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖∑ n ∈ S, χ n * w n‖ ≤ D) :
    ‖∑ n ∈ S, addPhase (u : ZMod q) n * w n‖ ≤ ‖∑ n ∈ S, w n‖ / q.totient + q * D := by
  classical
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hterm : ∀ n ∈ S, addPhase (u : ZMod q) n * w n
      = ∑ χ : DirichletCharacter ℂ q,
          (q.totient : ℂ)⁻¹ * (phaseCoeff (u : ZMod q) χ * (χ n * w n)) := by
    intro n hn
    rw [addPhase_eq_sum _ (hS n hn), mul_assoc, sum_mul, mul_sum]
    exact sum_congr rfl fun χ _ => by ring
  have hexp : ∑ n ∈ S, addPhase (u : ZMod q) n * w n
      = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          phaseCoeff (u : ZMod q) χ * ∑ n ∈ S, χ n * w n := by
    rw [sum_congr rfl hterm, sum_comm, mul_sum]
    exact sum_congr rfl fun χ _ => by simp only [mul_sum]
  rw [hexp, ← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ q))]
  have h1 : ∑ n ∈ S, (1 : DirichletCharacter ℂ q) n * w n = ∑ n ∈ S, w n :=
    sum_congr rfl fun n hn => by rw [MulChar.one_apply (hS n hn), one_mul]
  rw [h1, norm_mul, norm_inv, Complex.norm_natCast]
  have hrest : ‖∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
      phaseCoeff (u : ZMod q) χ * ∑ n ∈ S, χ n * w n‖ ≤ q.totient * (q * D) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
          ‖phaseCoeff (u : ZMod q) χ * ∑ n ∈ S, χ n * w n‖
        ≤ ∑ _χ ∈ univ.erase (1 : DirichletCharacter ℂ q), ((q : ℝ) * D) := by
          refine sum_le_sum fun χ hχ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_phaseCoeff_le _ χ) (hD χ (ne_of_mem_erase hχ))
            (norm_nonneg _) (Nat.cast_nonneg q)
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, ((q : ℝ) * D) :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by positivity
      _ = q.totient * (q * D) := by
          rw [sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
            DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  have hc1 := norm_phaseCoeff_one_le u
  calc (q.totient : ℝ)⁻¹ * ‖phaseCoeff (u : ZMod q) 1 * ∑ n ∈ S, w n +
        ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q),
          phaseCoeff (u : ZMod q) χ * ∑ n ∈ S, χ n * w n‖
      ≤ (q.totient : ℝ)⁻¹ * (‖∑ n ∈ S, w n‖ + q.totient * (q * D)) := by
        gcongr
        refine (norm_add_le _ _).trans (add_le_add ?_ hrest)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hc1
    _ = ‖∑ n ∈ S, w n‖ / q.totient + q * D := by
        field_simp

end Expansion

section Twisted

/-- `Σ_{N < n ≤ t} χ(n)Λ(n) = ψ(t, χ) − ψ(N, χ)`. -/
theorem sum_Ioc_twistedVM_eq {M : ℕ} (χ : DirichletCharacter ℂ M) {N t : ℕ} (hNt : N ≤ t) :
    ∑ n ∈ Ioc N t, twistedVM χ n = psiChi χ t - psiChi χ N := by
  have hsplit : Icc 1 t = Icc 1 N ∪ Ioc N t := by
    ext n
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 N) (Ioc N t) := by
    rw [disjoint_left]
    intro n h1 h2
    simp only [mem_Icc, mem_Ioc] at h1 h2
    omega
  rw [psiChi, psiChi, Nat.floor_natCast, Nat.floor_natCast, hsplit, sum_union hdisj]
  ring

/-- `log(2N) ≤ 2 log N` once `log N ≥ 1`. -/
theorem log_two_mul_le {N : ℕ} (hL : 1 ≤ Real.log N) : Real.log (2 * N) ≤ 2 * Real.log N := by
  have hN : (N : ℝ) ≠ 0 := by
    intro h
    rw [h, Real.log_zero] at hL
    linarith
  rw [Real.log_mul two_ne_zero hN]
  have := Real.log_two_lt_d9
  linarith

/-- **Siegel–Walfisz on dyadic windows.** For `A, B ≥ 1` and all large `N`: every primitive
nonprincipal `χ` of modulus at most `(log N)^B` has `|Σ_{N < n ≤ t} χ(n)Λ(n)| ≤ N/(log N)^A` for
`N ≤ t ≤ 2N`. Long windows come from `siegelWalfisz_window`; windows shorter than
`N/(log N)^{A+2}` are trivial. -/
theorem exists_norm_sum_twistedVM_le (A B : ℕ) (hB : 1 ≤ B) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 →
      χ.IsPrimitive → (M : ℝ) ≤ Real.log N ^ B → ∀ t : ℕ, N ≤ t → t ≤ 2 * N →
        ‖∑ n ∈ Ioc N t, twistedVM χ n‖ ≤ N / Real.log N ^ A := by
  obtain ⟨x₀, hx₀⟩ := ShortIntervalPrimesInProgressions.siegelWalfisz_window A B (A + 2) hB
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_natCast_atTop_atTop.eventually_ge_atTop x₀).and (hlog.eventually_ge_atTop 2))
  refine ⟨N₀, fun N hN M _ χ hχ hprim hM t hNt ht2 => ?_⟩
  obtain ⟨hx, hL2⟩ := hN₀ N hN
  set L := Real.log N with hLdef
  have hL0 : 0 < L := by linarith
  have hNt' : (N : ℝ) ≤ t := by exact_mod_cast hNt
  have ht2' : (t : ℝ) ≤ 2 * N := by exact_mod_cast ht2
  by_cases hlong : (N : ℝ) / L ^ (A + 2) ≤ (t : ℝ) - N
  · have hsw := hx₀ N hx M χ hχ hprim hM ((t : ℝ) - N) hlong (by linarith)
    rw [show (N : ℝ) + ((t : ℝ) - N) = t by ring] at hsw
    rw [sum_Ioc_twistedVM_eq χ hNt]
    calc ‖psiChi χ t - psiChi χ N‖ ≤ ((t : ℝ) - N) / L ^ A := hsw
      _ ≤ N / L ^ A := by gcongr; linarith
  · rw [not_le] at hlong
    have hN1 : 1 ≤ N := by
      by_contra h
      have : N = 0 := by omega
      rw [this, Nat.cast_zero, Real.log_zero] at hLdef
      linarith
    have hlog2N := log_two_mul_le (N := N) (by linarith)
    calc ‖∑ n ∈ Ioc N t, twistedVM χ n‖
        ≤ ∑ n ∈ Ioc N t, vonMangoldt n :=
          (norm_sum_le _ _).trans
            (sum_le_sum fun n _ => ShortIntervalPrimesInProgressions.norm_twistedVM_le n)
      _ ≤ ∑ _n ∈ Ioc N t, Real.log (2 * N) := by
          refine sum_le_sum fun n hn => vonMangoldt_le_log.trans ?_
          have hn := mem_Ioc.mp hn
          exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
            (by exact_mod_cast (show n ≤ 2 * N by omega))
      _ = ((t : ℝ) - N) * Real.log (2 * N) := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hNt]
      _ ≤ (N : ℝ) / L ^ (A + 2) * (2 * L) := by
          have h2N : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by
            have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
            linarith)
          exact mul_le_mul hlong.le hlog2N h2N (by positivity)
      _ = N / L ^ A * (2 / L) := by
          rw [pow_add]
          field_simp
      _ ≤ N / L ^ A := by
          refine mul_le_of_le_one_right (by positivity) ?_
          rw [div_le_one hL0]
          linarith

/-- A nonprincipal character agrees with its primitive character at primes `p > q`. -/
theorem primitiveCharacter_apply_prime {q : ℕ} (χ : DirichletCharacter ℂ q) {p : ℕ}
    (hp : p.Prime) (hq : 1 ≤ q) (hqp : q < p) :
    χ.primitiveCharacter p = χ p := by
  have hcop : Nat.Coprime p q :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => absurd (Nat.le_of_dvd hq h) (by omega)
  have h := χ.primitiveCharacter_apply_of_isCoprime (a := (p : ℤ))
    (Nat.isCoprime_iff_coprime.mpr hcop)
  simpa using h

/-- A nonprincipal character has a nonprincipal primitive character. -/
theorem primitiveCharacter_ne_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hχ
  rw [← χ.changeLevel_primitiveCharacter, h, map_one]

/-- **Twisted prime sums on major arcs.** For `A, B ≥ 1` and all large `N`: every nonprincipal
`χ` of modulus `q ≤ (log N)^B`, `q < N`, every `θ` and `N ≤ Q ≤ 2N` satisfy
`|Σ_{N < p ≤ Q} χ(p) e(pθ)| ≤ (N/(log N)^A)(2 + 2π|θ|N)/log N + 3√(2N) log(2N)`. -/
theorem exists_norm_sum_primes_char_le (A B : ℕ) (hB : 1 ≤ B) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      (q : ℝ) ≤ Real.log N ^ B → q < N → ∀ θ : ℝ, ∀ Q : ℕ, N ≤ Q → Q ≤ 2 * N →
        ‖∑ p ∈ (Ioc N Q).filter Nat.Prime, χ p * ex (p * θ)‖
          ≤ N / Real.log N ^ A * ((2 + 2 * Real.pi * |θ| * N) / Real.log N) +
            3 * Real.sqrt (2 * N) * Real.log (2 * N) := by
  obtain ⟨N₀, hN₀⟩ := exists_norm_sum_twistedVM_le A B hB
  refine ⟨max N₀ 2, fun N hN q _ χ hχ hqL hqN θ Q hNQ hQ2 => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  set ψ := χ.primitiveCharacter with hψ
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ1 : ψ ≠ 1 := primitiveCharacter_ne_one hχ
  have hψprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hcond : (χ.conductor : ℝ) ≤ Real.log N ^ B :=
    le_trans (by exact_mod_cast Nat.le_of_dvd hq1 χ.conductor_dvd_level) hqL
  have hswap : ∑ p ∈ (Ioc N Q).filter Nat.Prime, χ p * ex (p * θ)
      = ∑ p ∈ (Ioc N Q).filter Nat.Prime, ψ p * ex (p * θ) := by
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
    rw [hψ, primitiveCharacter_apply_prime χ hpp hq1 (by have := (mem_Ioc.mp hpI).1; omega)]
  have hwin : ∀ t, N ≤ t → t ≤ Q →
      ‖∑ n ∈ Ioc N t, (vonMangoldt n : ℂ) * ψ n‖ ≤ N / Real.log N ^ A := by
    intro t hNt htQ
    have h := hN₀ N hN0 χ.conductor ψ hψ1 hψprim hcond t hNt (htQ.trans hQ2)
    rwa [show ∑ n ∈ Ioc N t, twistedVM ψ n = ∑ n ∈ Ioc N t, (vonMangoldt n : ℂ) * ψ n from
      sum_congr rfl fun n _ => mul_comm _ _] at h
  have hbr := norm_sum_primes_le_of_windows (fun n => ψ n)
    (fun n => DirichletCharacter.norm_le_one ψ _) hN2 hNQ θ hwin
  have hQ1 : 1 ≤ Q := by omega
  have hpow := psi_sub_theta_div_log_two_le hQ1
  have hQN : ((Q : ℝ) - N) ≤ N := by
    have : (Q : ℝ) ≤ 2 * N := by exact_mod_cast hQ2
    linarith
  have hL0 : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsq : 3 * Real.sqrt Q * Real.log Q ≤ 3 * Real.sqrt (2 * N) * Real.log (2 * N) := by
    have hQ' : (Q : ℝ) ≤ 2 * N := by exact_mod_cast hQ2
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    gcongr
  rw [hswap]
  calc ‖∑ p ∈ (Ioc N Q).filter Nat.Prime, ψ p * ex (p * θ)‖
      ≤ N / Real.log N ^ A * ((2 + 2 * Real.pi * |θ| * (Q - N)) / Real.log N) +
          (Chebyshev.psi Q - Chebyshev.theta Q) / Real.log 2 := hbr
    _ ≤ N / Real.log N ^ A * ((2 + 2 * Real.pi * |θ| * N) / Real.log N) +
          3 * Real.sqrt (2 * N) * Real.log (2 * N) := by
        refine add_le_add ?_ (hpow.trans hsq)
        gcongr

end Twisted

end

end GaloisForLFunctions.PrimeExponentialSums
