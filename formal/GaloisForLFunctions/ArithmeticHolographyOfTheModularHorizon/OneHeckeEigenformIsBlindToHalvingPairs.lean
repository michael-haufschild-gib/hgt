import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheShimuraIntegralOfACuspForm
import GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.TheHeckeEigenformsSeeEveryResonanceInPairs
import GaloisForLFunctions.BlackHoleRingdown.TheParityOfTheHeckeModes
import GaloisForLFunctions.RHTower.XiCosineShiftNonrealZeroCount

/-!
# One Hecke eigenform is blind to halving pairs

For a Hecke–Maass form `u` the diagonal pair entry `Λ_u(s) = ∫_𝒟 |u|² E*(s − ½)` is, up to Gamma factors,
`ζ(s) · L(s, sym² u)`: the Rankin–Selberg series of a Hecke eigenform is `ζ(s) Σ τ(m²) m^{−s}`
(`lseries_sq_eq`), and the factor `ζ(2s)` of `E*` completes `Σ τ(m²) m^{−s}` to Shimura's integral
(`Shimura.fold_eq`). Shimura's integral is holomorphic on `Re s > 0` (`Shimura.differentiableAt_fold`), so the
identity

  `4 ρ(1) (s − 1) c(s) Mel_ν(s/2) P_u(s) = Γ_ℝ(2s) (2π)^{−s} G(s) (|ρ(1)|² + |ρ(−1)|²) · s · (s − 1)ζ(s) · Sh_u(s)`

(`diagonal_identity`), proved for `Re s > 3` by Euler products, holds on `Re s > 0` by analytic continuation.

**Consequences.**
* **Halving obstruction** (`pairing_self_eq_zero_of_zeta`, `pairing_half_eq_zero`): at every zero `s₀` of `ζ` with
  `0 < Re s₀`, every Hecke form has `Λ_u(s₀) = 0`. So no single Hecke eigenform sees a resonance `ρ/2` for which
  `ρ/2` is itself a zero of `ζ`; B109 for one Hecke eigenform implies that no right zero `ρ` has `ζ(ρ/2) = 0`
  (`zeta_half_ne_zero_of_hecke_seeing`).
* **Exact criterion** (`pairing_self_ne_zero_iff_of_rho`, for `ρ(1) ≠ 0`): `Λ_u(s₀) ≠ 0` iff `ζ(s₀) ≠ 0` and
  Shimura's integral of `u` does not vanish at `w = s₀/2 + ¼`.

**Ingredients.** The Hecke relations `τ(p^{k+2}) = λ_p τ(p^{k+1}) − τ(p^k)` give the doubling formulas
`τ(p^{2k+2}) = τ(p^{k+1})² − τ(p^k)²` (`double`) and hence `τ(n)² = Σ_{d | n} τ((n/d)²)` (`sq_eq_zeta_mul`);
the eigenvalues are real because `T_p` is self-adjoint (`conj_eigenvalue`), so `|τ|² = τ²`; and `E*` is even in
`x`, so the mirror form has the same diagonal (`pairing_comp_mirror`), which covers forms with `ρ(1) = 0`.
-/

open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped MatrixGroups UpperHalfPlane InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HalvingPairs

open GaloisForLFunctions.BlackHoleRingdown GaloisForLFunctions.BlackHoleRingdown.CuspEuler
open GaloisForLFunctions.RHTower.Gamma0MaassHecke (heckeH)

/-! ### The Hecke relations at a prime power -/

section Algebra

variable {lam : ℕ → ℂ} {τ : ℕ → ℂ}

/-- **Doubling at a prime power**: `U_{2k+2} = U_{k+1}² − U_k²` and `U_{2k+3} = U_{k+1}(U_{k+2} − U_k)` for
`U_m = τ(p^m)`. -/
theorem double (hτ : HeckeRec lam τ) (h1 : τ 1 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    τ (p ^ (2 * k + 2)) = τ (p ^ (k + 1)) ^ 2 - τ (p ^ k) ^ 2 ∧
      τ (p ^ (2 * k + 3)) = τ (p ^ (k + 1)) * (τ (p ^ (k + 2)) - τ (p ^ k)) := by
  have hrec : ∀ m, τ (p ^ (m + 2)) = lam p * τ (p ^ (m + 1)) - τ (p ^ m) := fun m => hτ.pow_succ_succ hp m
  have h0 : τ (p ^ 0) = 1 := by rw [pow_zero]; exact h1
  have h1' : τ (p ^ 1) = lam p := by rw [pow_one]; exact hτ.prime h1 hp
  have hidx : ∀ m n : ℕ, m = n → τ (p ^ m) = τ (p ^ n) := fun m n h => by rw [h]
  induction k with
  | zero =>
    have e2 := hrec 0
    have e3 := hrec 1
    rw [hidx (1 + 2) 3 rfl, hidx (1 + 1) 2 rfl] at e3
    rw [hidx (0 + 2) 2 rfl, hidx (0 + 1) 1 rfl] at e2
    refine ⟨?_, ?_⟩
    · rw [hidx (2 * 0 + 2) 2 rfl, hidx (0 + 1) 1 rfl, e2, h1', h0]; ring
    · rw [hidx (2 * 0 + 3) 3 rfl, hidx (0 + 1) 1 rfl, hidx (0 + 2) 2 rfl, e3, e2, h1', h0]; ring
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : τ (p ^ (2 * k + 4)) = lam p * τ (p ^ (2 * k + 3)) - τ (p ^ (2 * k + 2)) := by
      have h := hrec (2 * k + 2)
      rwa [hidx (2 * k + 2 + 2) (2 * k + 4) (by ring), hidx (2 * k + 2 + 1) (2 * k + 3) (by ring)] at h
    have e2 : τ (p ^ (2 * k + 5)) = lam p * τ (p ^ (2 * k + 4)) - τ (p ^ (2 * k + 3)) := by
      have h := hrec (2 * k + 3)
      rwa [hidx (2 * k + 3 + 2) (2 * k + 5) (by ring), hidx (2 * k + 3 + 1) (2 * k + 4) (by ring)] at h
    have e3 : τ (p ^ (k + 3)) = lam p * τ (p ^ (k + 2)) - τ (p ^ (k + 1)) := by
      have h := hrec (k + 1)
      rwa [hidx (k + 1 + 2) (k + 3) (by ring), hidx (k + 1 + 1) (k + 2) (by ring)] at h
    have e4 : τ (p ^ (k + 2)) = lam p * τ (p ^ (k + 1)) - τ (p ^ k) := hrec k
    have f1 : τ (p ^ (2 * k + 4)) = τ (p ^ (k + 2)) ^ 2 - τ (p ^ (k + 1)) ^ 2 := by
      rw [e1, ih2, ih1]; linear_combination (τ (p ^ k) - τ (p ^ (k + 2))) * e4
    refine ⟨?_, ?_⟩
    · rw [hidx (2 * (k + 1) + 2) (2 * k + 4) (by ring), hidx (k + 1 + 1) (k + 2) (by ring)]
      exact f1
    · rw [hidx (2 * (k + 1) + 3) (2 * k + 5) (by ring), hidx (k + 1 + 1) (k + 2) (by ring),
        hidx (k + 1 + 2) (k + 3) (by ring), e2, f1, ih2, e3]
      linear_combination τ (p ^ (k + 1)) * e4

/-- `Σ_{j ≤ k} τ(p^{2j}) = τ(p^k)²`. -/
theorem sum_double (hτ : HeckeRec lam τ) (h1 : τ 1 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), τ (p ^ (2 * j)) = τ (p ^ k) ^ 2 := by
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 2 by ring, (double hτ h1 hp k).1]
    ring

/-- `τ` as an arithmetic function. -/
def tauAF (τ : ℕ → ℂ) (h0 : τ 0 = 0) : ArithmeticFunction ℂ := ⟨τ, h0⟩

/-- `m ↦ τ(m²)` as an arithmetic function. -/
def tauSqAF (τ : ℕ → ℂ) (h0 : τ 0 = 0) : ArithmeticFunction ℂ := ⟨fun m => τ (m ^ 2), by simpa using h0⟩

theorem isMultiplicative_tauAF (hτ : HeckeRec lam τ) (h1 : τ 1 = 1) (h0 : τ 0 = 0) :
    (tauAF τ h0).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨h1, fun {m n} hm hn hmn => ?_⟩
  exact hτ.mul h1 n m (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn

theorem isMultiplicative_tauSqAF (hτ : HeckeRec lam τ) (h1 : τ 1 = 1) (h0 : τ 0 = 0) :
    (tauSqAF τ h0).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simpa [tauSqAF] using h1, fun {m n} hm hn hmn => ?_⟩
  show τ ((m * n) ^ 2) = τ (m ^ 2) * τ (n ^ 2)
  rw [mul_pow]
  exact hτ.mul h1 (n ^ 2) (m ^ 2) (by positivity) (by positivity) (hmn.pow 2 2)

/-- **`τ(n)² = Σ_{d | n} τ((n/d)²)`**: `τ · τ = ζ * (m ↦ τ(m²))`. -/
theorem sq_eq_zeta_mul (hτ : HeckeRec lam τ) (h1 : τ 1 = 1) (h0 : τ 0 = 0) :
    (tauAF τ h0).pmul (tauAF τ h0) = ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) * tauSqAF τ h0 := by
  have hT := isMultiplicative_tauAF hτ h1 h0
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hT.pmul hT) _
    (isMultiplicative_zeta.natCast.mul (isMultiplicative_tauSqAF hτ h1 h0))).2 fun p i hp => ?_
  rw [pmul_apply, coe_zeta_mul_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, tauSqAF, tauAF]
  show τ (p ^ i) * τ (p ^ i) = ∑ x ∈ Finset.range (i + 1), τ ((p ^ x) ^ 2)
  simp_rw [← pow_mul, mul_comm _ 2]
  rw [sum_double hτ h1 hp i]
  ring


theorem tauAF_apply (h0 : τ 0 = 0) (n : ℕ) : tauAF τ h0 n = τ n := rfl

theorem tauSqAF_apply (h0 : τ 0 = 0) (n : ℕ) : tauSqAF τ h0 n = τ (n ^ 2) := rfl

/-- **The Dirichlet series of `τ²`**: `Σ τ(n)² n^{−s} = ζ(s) Σ τ(m²) m^{−s}` for `Re s > 2` when `|τ(n)| ≤ K√n`. -/
theorem lseries_sq_eq (hτ : HeckeRec lam τ) (h1 : τ 1 = 1) (h0 : τ 0 = 0) {K : ℝ}
    (hK : ∀ n : ℕ, ‖τ n‖ ≤ K * Real.sqrt n) {s : ℂ} (hs : 2 < s.re) :
    LSeries (fun n => τ n * τ n) s = riemannZeta s * LSeries (fun m => τ (m ^ 2)) s := by
  have hsq : LSeriesSummable (fun m => tauSqAF τ h0 m) s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨K, fun m hm => ?_⟩
    have := hK (m ^ 2)
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)] at this
    rw [tauSqAF_apply, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    exact this
  have hz : LSeriesSummable (fun n => ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) s := by
    simp only [natCoe_apply]
    exact LSeriesSummable_zeta_iff.2 (by linarith)
  have e : (fun n => τ n * τ n) = fun n => ((tauAF τ h0).pmul (tauAF τ h0)) n := by
    funext n; rw [pmul_apply, tauAF_apply]
  have hL := LSeries_mul' hz hsq
  rw [← sq_eq_zeta_mul hτ h1 h0] at hL
  rw [e, hL]
  congr 1
  · simp only [natCoe_apply]
    exact LSeries_zeta_eq_riemannZeta (by linarith)

end Algebra

/-! ### Hecke eigenforms: real eigenvalues and the normalized sequence -/

section Form

variable {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) {c : ℕ → ℂ}
  (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g)

include hg in
theorem integral_conj_self_ne_zero (hg0 : g ≠ 0) : ∫ z in ModularGroup.fd, conj (g z) * g z ≠ 0 := by
  have h := inner_toImage (⟨g, hg⟩ : HeckeCusp.cuspSpace lam) ⟨g, hg⟩
  intro h0
  apply hg0
  have hx : toImage lam ⟨g, hg⟩ = 0 := inner_self_eq_zero.1 (h.trans h0)
  have := (toImage lam).injective (hx.trans (map_zero _).symm)
  exact congrArg Subtype.val this

include hg hc in
/-- **Hecke eigenvalues are real**: `T_p` is self-adjoint for the Petersson product. -/
theorem conj_eigenvalue (hg0 : g ≠ 0) (p : ℕ) [Fact p.Prime] : conj (c p) = c p := by
  have hs := integral_conj_heckeH_mul hg hg p
  rw [hc p] at hs
  simp only [Pi.smul_apply, smul_eq_mul, map_mul] at hs
  have e1 : ∫ z in ModularGroup.fd, conj (c p) * conj (g z) * g z =
      conj (c p) * ∫ z in ModularGroup.fd, conj (g z) * g z := by
    rw [← integral_const_mul]; congr 1; ext z; ring
  have e2 : ∫ z in ModularGroup.fd, conj (g z) * (c p * g z) =
      c p * ∫ z in ModularGroup.fd, conj (g z) * g z := by
    rw [← integral_const_mul]; congr 1; ext z; ring
  rw [e1, e2] at hs
  exact mul_right_cancel₀ (integral_conj_self_ne_zero hg hg0) hs

include hg hc in
theorem conj_heckeLam (hg0 : g ≠ 0) {p : ℕ} (hp : p.Prime) : conj (CuspEuler.heckeLam c p) = CuspEuler.heckeLam c p := by
  haveI := Fact.mk hp
  unfold CuspEuler.heckeLam
  rw [map_div₀, conj_eigenvalue hg hc hg0 p, Complex.conj_ofReal]

variable {ρ : ℤ → ℂ} (hρ0 : ρ 0 = 0)
  (hρ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
    HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam))

/-- The normalized Hecke sequence `τ(n) = ρ(n)/ρ(1)`. -/
def tauOf (ρ : ℤ → ℂ) (n : ℕ) : ℂ := (ρ 1)⁻¹ * ρ n

include hg hc hρ in
theorem heckeRec_tauOf : HeckeRec (CuspEuler.heckeLam c) (tauOf ρ) := by
  have hP := heckeRec_rho hg hρ c hc 1 (Or.inl rfl)
  intro p hp n hn
  have h := hP p hp n hn
  simp only [one_mul] at h
  simp only [tauOf]
  rw [h]
  split_ifs <;> ring

theorem tauOf_one (hρ1 : ρ 1 ≠ 0) : tauOf ρ 1 = 1 := by
  simp [tauOf, hρ1]

include hρ0 in
theorem tauOf_zero : tauOf ρ 0 = 0 := by simp [tauOf, hρ0]

include hg hρ0 hρ in
theorem exists_tauOf_bound : ∃ K : ℝ, ∀ n : ℕ, ‖tauOf ρ n‖ ≤ K * Real.sqrt n := by
  obtain ⟨C, hC0, hC⟩ := CuspL.exists_coeff_bound hg hρ0 hρ
  refine ⟨‖ρ 1‖⁻¹ * C, fun n => ?_⟩
  rw [tauOf, norm_mul, norm_inv, mul_assoc]
  have := hC n
  simp only [Int.cast_natCast, Nat.abs_cast] at this
  exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 (norm_nonneg _))

include hg hc hρ in
theorem rho_neg (hρ1 : ρ 1 ≠ 0) {n : ℕ} (hn : 0 < n) : ρ (-(n : ℤ)) = ρ (-1) * tauOf ρ n := by
  have hM := heckeRec_rho hg hρ c hc (-1) (Or.inr rfl)
  have h := hM.proportional (heckeRec_tauOf hg hc hρ) n hn
  rw [tauOf_one hρ1] at h
  simp only [neg_one_mul, Nat.cast_one, mul_one] at h
  rw [h]; ring

theorem rho_pos (hρ1 : ρ 1 ≠ 0) (n : ℕ) : ρ n = ρ 1 * tauOf ρ n := by
  simp [tauOf, hρ1]

include hg hc hρ in
/-- With real eigenvalues the normalized sequence is real. -/
theorem conj_tauOf (hg0 : g ≠ 0) (hρ1 : ρ 1 ≠ 0) {n : ℕ} (hn : 0 < n) : conj (tauOf ρ n) = tauOf ρ n := by
  have hτ := heckeRec_tauOf hg hc hρ
  have hσ : HeckeRec (CuspEuler.heckeLam c) fun n => conj (tauOf ρ n) := by
    intro p hp m hm
    simp only
    rw [hτ p hp m hm, map_sub, map_mul, conj_heckeLam hg hc hg0 hp]
    split_ifs <;> simp
  have h := hσ.proportional hτ n hn
  rw [tauOf_one hρ1, map_one] at h
  simpa using h

/-! ### The two series -/

include hg hc hρ0 hρ in
/-- The Rankin–Selberg series of a Hecke eigenform is `(|ρ(1)|² + |ρ(−1)|²) Σ τ(n)² n^{−s}`. -/
theorem tsum_rankinSelberg_eq (hg0 : g ≠ 0) (hρ1 : ρ 1 ≠ 0) {s : ℂ} (hs : 2 < s.re) :
    ∑' n : ℤ, ρ n * conj (ρ n) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) =
      ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) * LSeries (fun n => tauOf ρ n * tauOf ρ n) s := by
  obtain ⟨C, hC0, hC⟩ := CuspL.exists_coeff_bound hg hρ0 hρ
  set f : ℤ → ℂ := fun n => ρ n * conj (ρ n) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)
  have hf : Summable f := by
    refine Summable.of_norm_bounded ((Real.summable_abs_int_rpow (b := s.re - 1) (by linarith)).mul_left
      (C ^ 2)) fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [f, hρ0]; positivity
    have hn0 : (0 : ℝ) < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
    simp only [f]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
    have h1 := hC n
    have hsq : (C * Real.sqrt |(n : ℝ)|) ^ 2 = C ^ 2 * |(n : ℝ)| := by
      rw [mul_pow, Real.sq_sqrt hn0.le]
    calc ‖ρ n‖ * ‖ρ n‖ * |(n : ℝ)| ^ (-s.re) ≤ (C * Real.sqrt |(n : ℝ)|) ^ 2 * |(n : ℝ)| ^ (-s.re) := by
          gcongr; nlinarith [norm_nonneg (ρ n)]
      _ = C ^ 2 * |(n : ℝ)| ^ (-(s.re - 1)) := by
          rw [hsq, mul_assoc, ← Real.rpow_one_add' hn0.le (by linarith)]
          congr 2; ring
  have h := tsum_nat_add_neg hf
  have hf0 : f 0 = 0 := by simp [f, hρ0]
  rw [hf0, add_zero] at h
  rw [← h, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [f, hρ0]
  rw [if_neg hn.ne']
  simp only [f, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, Complex.ofReal_natCast]
  rw [rho_neg hg hc hρ hρ1 hn, rho_pos hρ1 n, map_mul, map_mul, conj_tauOf hg hc hρ hg0 hρ1 hn,
    Complex.cpow_neg, div_eq_mul_inv]
  have e1 : ρ 1 * conj (ρ 1) = (‖ρ 1‖ : ℂ) ^ 2 := Complex.mul_conj' _
  have e2 : ρ (-1) * conj (ρ (-1)) = (‖ρ (-1)‖ : ℂ) ^ 2 := Complex.mul_conj' _
  push_cast
  linear_combination (tauOf ρ n * tauOf ρ n * ((n : ℂ) ^ s)⁻¹) * (e1 + e2)

end Form

/-! ### The Shimura series as a Dirichlet series -/

/-- The constant `c(w) = (8π)^{3/4−w}/√(2π)` of the Shimura series. -/
def shC (w : ℂ) : ℂ := ((8 * Real.pi : ℝ) : ℂ) ^ (3 / 4 - w) / ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)

theorem sq_cpow {n : ℕ} (hn : 0 < n) (z : ℂ) : (((n : ℝ) ^ 2 : ℝ) : ℂ) ^ z = (n : ℂ) ^ (2 * z) := by
  have h1 : (((n : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (Nat.cast_pos.2 hn) 2).ne'
  have h2 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2,
    ← Complex.ofReal_log (by positivity), Real.log_pow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]
  congr 1; push_cast; ring

theorem norm_zCoef_le {ρ : ℤ → ℂ} {R : ℝ} (hR : ∀ k : ℤ, ‖Shimura.rW ρ k‖ ≤ R) (w : ℂ) (j : ℤ) :
    ‖Shimura.zCoef ρ w j‖ ≤ R * (8 * Real.pi) ^ (3 / 4 - w.re) * |(j : ℝ)| ^ (-(2 * w.re - 3 / 2)) := by
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  by_cases hj : j = 0
  · subst hj; rw [Shimura.zCoef, if_pos rfl, norm_zero]
    exact mul_nonneg (mul_nonneg hR0 (by positivity)) (by positivity)
  have hj0 : (0 : ℝ) < |(j : ℝ)| := abs_pos.2 (by exact_mod_cast hj)
  rw [Shimura.zCoef, if_neg hj, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  have e : (8 * Real.pi * (j : ℝ) ^ 2) ^ (3 / 4 - w).re =
      (8 * Real.pi) ^ (3 / 4 - w.re) * |(j : ℝ)| ^ (-(2 * w.re - 3 / 2)) := by
    rw [show (3 / 4 - w).re = 3 / 4 - w.re by simp, Real.mul_rpow (by positivity) (sq_nonneg _),
      ← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul hj0.le]
    congr 2; push_cast; ring
  rw [e, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hR _) (by positivity)) (by positivity)

section Series

variable {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) {c : ℕ → ℂ}
  (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) {ρ : ℤ → ℂ} (hρ0 : ρ 0 = 0)
  (hρ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
    HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam))

theorem zCoef_nat (hρ1 : ρ 1 ≠ 0) (w : ℂ) {n : ℕ} (hn : 0 < n) :
    Shimura.zCoef ρ w n = ρ 1 * shC w * (tauOf ρ (n ^ 2) * ((n : ℂ) ^ (2 * w - 1 / 2))⁻¹) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : ρ ((n : ℤ) ^ 2) = ρ 1 * tauOf ρ (n ^ 2) := by
    rw [← rho_pos hρ1 (n ^ 2)]; push_cast; rfl
  have habs : |(((n : ℤ) ^ 2 : ℤ) : ℝ)| = (n : ℝ) ^ 2 := by push_cast; exact abs_of_nonneg (sq_nonneg _)
  have hsqrt : Real.sqrt (2 * Real.pi * (n : ℝ) ^ 2) = Real.sqrt (2 * Real.pi) * n := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hnr.le]
  have hpow : ((8 * Real.pi * ((n : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) ^ (3 / 4 - w) =
      ((8 * Real.pi : ℝ) : ℂ) ^ (3 / 4 - w) * ((n : ℂ) * ((n : ℂ) ^ (2 * w - 1 / 2))⁻¹) := by
    rw [Int.cast_natCast, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (sq_nonneg _),
      sq_cpow hn, show 2 * (3 / 4 - w) = 1 + -(2 * w - 1 / 2) by ring, Complex.cpow_add _ _ hn',
      Complex.cpow_one, Complex.cpow_neg]
  have hs0 : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  rw [Shimura.zCoef, if_neg (by exact_mod_cast hn.ne'), Shimura.rW, hsq, habs, hsqrt, hpow, shC]
  push_cast
  field_simp

theorem zCoef_neg (w : ℂ) (j : ℤ) : Shimura.zCoef ρ w (-j) = Shimura.zCoef ρ w j := by
  unfold Shimura.zCoef
  simp

include hg hρ0 hρ in
/-- **The Shimura series of a Hecke eigenform**:
`Σ_j ρ_W(j²)(8πj²)^{3/4−w} = 2 ρ(1) c(w) Σ_m τ(m²) m^{−(2w−½)}` for `Re w > 5/4`. -/
theorem tsum_zCoef_eq (hρ1 : ρ 1 ≠ 0) {w : ℂ} (hw : 5 / 4 < w.re) :
    ∑' j : ℤ, Shimura.zCoef ρ w j = 2 * ρ 1 * shC w * LSeries (fun m => tauOf ρ (m ^ 2)) (2 * w - 1 / 2) := by
  obtain ⟨C, hC0, hC⟩ := CuspL.exists_coeff_bound hg hρ0 hρ
  have hR := Shimura.norm_rW_le hC
  have hz : Summable (Shimura.zCoef ρ w) :=
    Summable.of_norm_bounded ((Real.summable_abs_int_rpow (b := 2 * w.re - 3 / 2) (by linarith)).mul_left
      (C / Real.sqrt (2 * Real.pi) * (8 * Real.pi) ^ (3 / 4 - w.re))) fun j => norm_zCoef_le hR w j
  have h := tsum_nat_add_neg hz
  have h0 : Shimura.zCoef ρ w 0 = 0 := by simp [Shimura.zCoef]
  rw [h0, add_zero] at h
  rw [← h, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def, zCoef_neg]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Shimura.zCoef]
  rw [if_neg hn.ne', zCoef_nat hρ1 w hn, div_eq_mul_inv]
  ring

end Series

/-! ### The completed Eisenstein function is even in `x` -/

theorem completedEisenstein_neg_x (u : ℂ) (x Y : ℝ) :
    EisAuto.completedEisenstein u (-x) Y = EisAuto.completedEisenstein u x Y := by
  have hphase : ∀ (b : Bool) (N : ℕ), _root_.RHTower.d4BMCompletedEisensteinFourierPhase b N (-x) =
      _root_.RHTower.d4BMCompletedEisensteinFourierPhase (!b) N x := by
    intro b N
    cases b <;> simp [_root_.RHTower.d4BMCompletedEisensteinFourierPhase, _root_.RHTower.d4BMFourierSign]
  have ht : ∀ b, _root_.RHTower.weightedTail u b (-x) Y = _root_.RHTower.weightedTail u (!b) x Y := by
    intro b
    simp only [_root_.RHTower.weightedTail, _root_.RHTower.d4BMSignedWhittakerMode, hphase]
  simp only [EisAuto.completedEisenstein, eisensteinNumerator, eisTail, ht, Bool.not_false, Bool.not_true]
  ring

/-- **The mirror form has the same diagonal**: `E*` is even in `x` and `𝒟` is mirror symmetric. -/
theorem pairing_comp_mirror (s : ℂ) (g : ℍ → ℂ) :
    pairing s (g ∘ OddCusp.mirror) (g ∘ OddCusp.mirror) = pairing s g g := by
  have hm : Measurable OddCusp.mirror := OddSector.continuous_mirror.measurable
  have hme : MeasurableEmbedding OddCusp.mirror :=
    (MeasurableEquiv.mk ⟨OddCusp.mirror, OddCusp.mirror, fun z => OddSector.mirror_mirror z,
      fun z => OddSector.mirror_mirror z⟩ hm hm).measurableEmbedding
  have hre : ∀ z : ℍ, (OddCusp.mirror z).re = -z.re := fun z => by
    show (-(starRingEnd ℂ) (z : ℂ)).re = -(z : ℂ).re
    simp
  have e : ∀ z, pairIntegrand s (g ∘ OddCusp.mirror) (g ∘ OddCusp.mirror) z =
      pairIntegrand s g g (OddCusp.mirror z) := by
    intro z
    simp only [pairIntegrand, Function.comp]
    rw [hre, OddCusp.mirror_im, completedEisenstein_neg_x]
  unfold pairing
  simp_rw [e]
  exact OddSector.measurePreserving_mirror_fd.integral_comp hme _

/-! ### Gamma factors on `Re s > 0` -/

theorem re_ne_neg_nat {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -m := fun h => by
  rw [h] at hz; simp at hz; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

theorem differentiableAt_Gamma_of_re {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Complex.Gamma z :=
  Complex.differentiableAt_Gamma z (re_ne_neg_nat hz)

theorem Gamma_ne_zero_of_re {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero (re_ne_neg_nat hz)

theorem dGamma {f : ℂ → ℂ} {s : ℂ} (hf : DifferentiableAt ℂ f s) (h : 0 < (f s).re) :
    DifferentiableAt ℂ (fun s => Complex.Gamma (f s)) s :=
  (differentiableAt_Gamma_of_re h).comp s hf

theorem differentiableAt_melC {ν : ℂ} (hν : ν.re = 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun s => Shimura.melC ν (s / 2)) s := by
  unfold Shimura.melC
  have hid : DifferentiableAt ℂ (fun x : ℂ => x) s := differentiableAt_id
  have d0 := ((hid.div_const 2).sub_const 1).const_cpow (c := (2 : ℂ)) (Or.inl two_ne_zero)
  have d1 := dGamma (hid.div_const 2) (by simp; linarith)
  have d2 := dGamma ((hid.div_const 2).add_const ν) (by simp [hν]; linarith)
  have d3 := dGamma ((hid.div_const 2).sub_const ν) (by simp [hν]; linarith)
  have d4 := dGamma ((hid.div_const 2).const_mul 2) (by simp; linarith)
  exact (((d0.mul d1).mul d2).mul d3).div d4 (Gamma_ne_zero_of_re (by simp; linarith))

theorem melC_ne_zero {ν : ℂ} (hν : ν.re = 0) {s : ℂ} (hs : 0 < s.re) : Shimura.melC ν (s / 2) ≠ 0 := by
  unfold Shimura.melC
  have h1 : 0 < (s / 2).re := by simp; linarith
  refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (Gamma_ne_zero_of_re h1))
    (Gamma_ne_zero_of_re (by simp [hν]; linarith))) (Gamma_ne_zero_of_re (by simp [hν]; linarith)))
    (Gamma_ne_zero_of_re (by simp; linarith))
  exact (Complex.cpow_ne_zero_iff.2 (Or.inl two_ne_zero))

theorem differentiableAt_pairGamma {ν : ℂ} (hν : ν.re = 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun s => pairGamma ν ν s) s := by
  unfold pairGamma
  have hid : DifferentiableAt ℂ (fun x : ℂ => x) s := differentiableAt_id
  refine (((hid.sub_const 3).const_cpow (Or.inl two_ne_zero)).div
    (differentiableAt_Gamma_of_re hs) (Gamma_ne_zero_of_re hs)).mul
    ((((dGamma (((hid.add_const ν).add_const ν).div_const 2) ?_).mul
      (dGamma (((hid.add_const ν).sub_const ν).div_const 2) ?_)).mul
      (dGamma (((hid.sub_const ν).add_const ν).div_const 2) ?_)).mul
      (dGamma (((hid.sub_const ν).sub_const ν).div_const 2) ?_)) <;>
    · simp [hν]; linarith

theorem pairGamma_ne_zero {ν : ℂ} (hν : ν.re = 0) {s : ℂ} (hs : 0 < s.re) : pairGamma ν ν s ≠ 0 := by
  unfold pairGamma
  have h2 : (2 : ℂ) ^ (s - 3) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
  refine mul_ne_zero (div_ne_zero h2 (Gamma_ne_zero_of_re hs))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (Gamma_ne_zero_of_re ?_) (Gamma_ne_zero_of_re ?_))
      (Gamma_ne_zero_of_re ?_)) (Gamma_ne_zero_of_re ?_)) <;>
    · simp [hν]; linarith

/-! ### The diagonal identity -/

/-- Shimura's spectral variable `w = s/2 + ¼`. -/
def wOf (s : ℂ) : ℂ := s / 2 + 1 / 4

/-- The left side `4 ρ(1)(s − 1) c(w) Mel_ν(s/2) P_u(s)`. -/
def lhsD (lam : ℝ) (g : ℍ → ℂ) (ρ : ℤ → ℂ) (s : ℂ) : ℂ :=
  4 * ρ 1 * (s - 1) * shC (wOf s) * Shimura.melC (CuspL.nu lam) (s / 2) *
    polarTransform (fun z => g z * conj (g z)) s

/-- The right side `Γ_ℝ(2s)(2π)^{−s} G(s) N s (s − 1)ζ(s) Sh_u(w)`. -/
def rhsD (lam : ℝ) (g : ℍ → ℂ) (ρ : ℤ → ℂ) (s : ℂ) : ℂ :=
  Complex.Gammaℝ (2 * s) * (2 * Real.pi : ℂ) ^ (-s) * pairGamma (CuspL.nu lam) (CuspL.nu lam) s *
    ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) * s * _root_.RHTower.zetaResidueFactor s *
      GaloisForLFunctions.RHTower.HalfWeight.rsFold 1 (Shimura.kernel g) (wOf s)

theorem shC_ne_zero (w : ℂ) : shC w ≠ 0 := by
  unfold shC
  refine div_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast (by positivity : (0 : ℝ) < 8 * Real.pi).ne'))) ?_
  exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'

section Identity

variable {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) {c : ℕ → ℂ}
  (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) {ρ : ℤ → ℂ} (hρ0 : ρ 0 = 0)
  (hρ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
    HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam))

include hg hc hρ0 hρ in
/-- **The diagonal identity on `Re s > 3`**, from the two Euler factorizations. -/
theorem identity_of_re (hg0 : g ≠ 0) (hρ1 : ρ 1 ≠ 0) {s : ℂ} (hs : 3 < s.re) (him : s.im ≠ 0) :
    lhsD lam g ρ s = rhsD lam g ρ s := by
  have hs1 : 1 < s.re := by linarith
  have hs2 : 2 < s.re := by linarith
  have h0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have h12 : s ≠ 1 / 2 := fun h => by rw [h] at hs; norm_num at hs
  have h1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have h2s1 : 2 * s ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hτ := heckeRec_tauOf hg hc hρ
  obtain ⟨K, hK⟩ := exists_tauOf_bound hg hρ0 hρ
  have hP : polarTransform (fun z => g z * conj (g z)) s = 4 * s * (2 * s - 1) * (s - 1) * pairing s g g :=
    polarTransform_eq_mul h0 h12 h1
  have h2s : 1 < (2 * s).re := by simp; linarith
  have hxi : _root_.RHTower.xi (2 * s) / (2 * s * (2 * s - 1)) =
      Complex.Gammaℝ (2 * s) * riemannZeta (2 * s) / 2 := by
    rw [_root_.RHTower.xi_eq_mul_Gammaℝ_zeta h2s]
    have hs0' : s * (2 * s - 1) ≠ 0 :=
      mul_ne_zero h0 (fun h => h2s1 (by linear_combination h))
    field_simp
  have hw7 : 7 / 4 < (wOf s).re := by simp [wOf]; linarith
  have hw5 : 5 / 4 < (wOf s).re := by linarith
  have e2w : 2 * wOf s - 1 / 2 = s := by unfold wOf; ring
  have ew4 : wOf s - 1 / 4 = s / 2 := by unfold wOf; ring
  have hreg : GaloisForLFunctions.RHTower.HalfWeight.regF (wOf s) =
      (2 * s - 2) * ((2 * s - 1) * riemannZeta (2 * s)) := by
    unfold GaloisForLFunctions.RHTower.HalfWeight.regF wOf
    rw [show 4 * (s / 2 + 1 / 4) - 1 = 2 * s by ring, _root_.RHTower.zetaResidueFactor_of_ne h2s1]
    ring
  have hzs : _root_.RHTower.zetaResidueFactor s = (s - 1) * riemannZeta s :=
    _root_.RHTower.zetaResidueFactor_of_ne h1
  unfold lhsD rhsD
  rw [hP, pairing_eq_rankinSelberg hg hg hρ0 hρ hρ hs1 him, tsum_rankinSelberg_eq hg hc hρ0 hρ hg0 hρ1 hs2,
    lseries_sq_eq hτ (tauOf_one hρ1) (tauOf_zero hρ0) hK hs2, hxi, Shimura.fold_eq hg hρ0 hρ hw7,
    tsum_zCoef_eq hg hρ0 hρ hρ1 hw5, e2w, ew4, hreg, hzs]
  ring

include hg in
theorem differentiableOn_lhsD : DifferentiableOn ℂ (lhsD lam g ρ) {s | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hseed : IsSeed (fun z => g z * conj (g z)) :=
    (isSeed_of_mem_cuspSpace hg).mul (isSeed_of_mem_cuspSpace hg).star
  have hsh : DifferentiableAt ℂ (fun s => shC (wOf s)) s := by
    unfold shC wOf
    exact ((differentiableAt_const _).sub ((differentiableAt_id.div_const 2).add_const _)).const_cpow
      (Or.inl (by exact_mod_cast (by positivity : (0 : ℝ) < 8 * Real.pi).ne')) |>.div_const _
  unfold lhsD
  exact ((((differentiableAt_const _).mul (differentiableAt_id.sub_const 1)).mul hsh).mul
    (differentiableAt_melC (CuspL.nu_re lam) hs')).mul
    ((differentiable_polarTransform hseed) s) |>.differentiableWithinAt

include hg in
theorem differentiableOn_rhsD : DifferentiableOn ℂ (rhsD lam g ρ) {s | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hG : DifferentiableAt ℂ (fun s => Complex.Gammaℝ (2 * s)) s := by
    simp_rw [Complex.Gammaℝ_def]
    have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hid : DifferentiableAt ℂ (fun x : ℂ => x) s := differentiableAt_id
    exact (((hid.const_mul 2).neg.div_const 2).const_cpow (Or.inl hπ)).mul
      (dGamma ((hid.const_mul 2).div_const 2) (by simp; linarith))
  have h2π : DifferentiableAt ℂ (fun s : ℂ => (2 * Real.pi : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'))
  have hw : DifferentiableAt ℂ (fun s => GaloisForLFunctions.RHTower.HalfWeight.rsFold 1 (Shimura.kernel g)
      (wOf s)) s :=
    (Shimura.differentiableAt_fold hg (by simp [wOf]; linarith)).comp s
      ((differentiableAt_id.div_const 2).add_const _)
  unfold rhsD
  exact ((((((hG.mul h2π).mul (differentiableAt_pairGamma (CuspL.nu_re lam) hs')).mul
    (differentiableAt_const _)).mul differentiableAt_id).mul
    (_root_.RHTower.differentiable_zetaResidueFactor s)).mul hw).differentiableWithinAt

include hg hc hρ0 hρ in
/-- **The diagonal identity on `Re s > 0`** (analytic continuation). -/
theorem diagonal_identity (hg0 : g ≠ 0) (hρ1 : ρ 1 ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    lhsD lam g ρ s = rhsD lam g ρ s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have hL := (differentiableOn_lhsD hg (ρ := ρ)).analyticOnNhd hU
  have hR := (differentiableOn_rhsD hg (ρ := ρ)).analyticOnNhd hU
  have hV : IsOpen {s : ℂ | 3 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im)
  have hz₀V : (4 + Complex.I : ℂ) ∈ {s : ℂ | 3 < s.re ∧ 0 < s.im} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]; norm_num
  have heq : lhsD lam g ρ =ᶠ[𝓝 (4 + Complex.I)] rhsD lam g ρ :=
    Filter.eventually_of_mem (hV.mem_nhds hz₀V) fun s hs =>
      identity_of_re hg hc hρ0 hρ hg0 hρ1 hs.1 hs.2.ne'
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hpre (by norm_num) heq hs

end Identity

/-! ### The halving obstruction -/

section Obstruction

variable {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) {c : ℕ → ℂ}
  (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) {ρ : ℤ → ℂ} (hρ0 : ρ 0 = 0)
  (hρ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
    HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam))

/-- The left side is a nonzero multiple of the diagonal entry. -/
theorem lhsD_eq (s : ℂ) (h0 : s ≠ 0) (h12 : s ≠ 1 / 2) (h1 : s ≠ 1) :
    lhsD lam g ρ s = (16 * ρ 1 * (s - 1) ^ 2 * s * (2 * s - 1) * shC (wOf s) *
      Shimura.melC (CuspL.nu lam) (s / 2)) * pairing s g g := by
  unfold lhsD
  rw [polarTransform_eq_mul h0 h12 h1]
  show _ = _ * seedTransform (fun z => g z * conj (g z)) s
  ring

theorem lhsD_coeff_ne_zero (hρ1 : ρ 1 ≠ 0) {s : ℂ} (hs : 0 < s.re) (h12 : s ≠ 1 / 2) (h1 : s ≠ 1) :
    16 * ρ 1 * (s - 1) ^ 2 * s * (2 * s - 1) * shC (wOf s) * Shimura.melC (CuspL.nu lam) (s / 2) ≠ 0 := by
  have h0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have h2 : 2 * s - 1 ≠ 0 := fun h => h12 (by linear_combination h / 2)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hρ1)
    (pow_ne_zero 2 (sub_ne_zero.2 h1))) h0) h2) (shC_ne_zero _)) (melC_ne_zero (CuspL.nu_re lam) hs)

include hg hc hρ0 hρ in
/-- **The diagonal of a Hecke form vanishes at the zeros of `ζ`** (case `ρ(1) ≠ 0`). -/
theorem pairing_self_eq_zero_of_rho (hg0 : g ≠ 0) (hρ1 : ρ 1 ≠ 0) {s₀ : ℂ} (hs : 0 < s₀.re)
    (h12 : s₀ ≠ 1 / 2) (h1 : s₀ ≠ 1) (hz : riemannZeta s₀ = 0) : pairing s₀ g g = 0 := by
  have h0 : s₀ ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hid := diagonal_identity hg hc hρ0 hρ hg0 hρ1 hs
  have hR : rhsD lam g ρ s₀ = 0 := by
    unfold rhsD; rw [_root_.RHTower.zetaResidueFactor_of_ne h1, hz]; ring
  rw [hR, lhsD_eq s₀ h0 h12 h1] at hid
  exact (mul_eq_zero.1 hid).resolve_left (lhsD_coeff_ne_zero (lam := lam) hρ1 hs h12 h1)

include hg hc hρ0 hρ in
/-- **Exact criterion** (case `ρ(1) ≠ 0`): the diagonal sees `s₀` iff `ζ(s₀) ≠ 0` and Shimura's integral of the
form does not vanish at `w = s₀/2 + ¼`. -/
theorem pairing_self_ne_zero_iff_of_rho (hg0 : g ≠ 0) (hρ1 : ρ 1 ≠ 0) {s₀ : ℂ} (hs : 0 < s₀.re)
    (h12 : s₀ ≠ 1 / 2) (h1 : s₀ ≠ 1) :
    pairing s₀ g g ≠ 0 ↔ riemannZeta s₀ ≠ 0 ∧
      GaloisForLFunctions.RHTower.HalfWeight.rsFold 1 (Shimura.kernel g) (wOf s₀) ≠ 0 := by
  have h0 : s₀ ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hid := diagonal_identity hg hc hρ0 hρ hg0 hρ1 hs
  rw [lhsD_eq s₀ h0 h12 h1] at hid
  have hA := lhsD_coeff_ne_zero (lam := lam) hρ1 hs h12 h1
  have hN : ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hB : Complex.Gammaℝ (2 * s₀) * (2 * Real.pi : ℂ) ^ (-s₀) * pairGamma (CuspL.nu lam) (CuspL.nu lam) s₀ *
      ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) * s₀ * (s₀ - 1) ≠ 0 :=
    by
    have hΓ : Complex.Gammaℝ (2 * s₀) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
    have h2π : (2 * Real.pi : ℂ) ^ (-s₀) ≠ 0 :=
      Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'))
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hΓ h2π)
      (pairGamma_ne_zero (CuspL.nu_re lam) hs)) hN) h0) (sub_ne_zero.2 h1)
  have hR : rhsD lam g ρ s₀ = (Complex.Gammaℝ (2 * s₀) * (2 * Real.pi : ℂ) ^ (-s₀) *
      pairGamma (CuspL.nu lam) (CuspL.nu lam) s₀ * ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) * s₀ * (s₀ - 1)) *
      (riemannZeta s₀ * GaloisForLFunctions.RHTower.HalfWeight.rsFold 1 (Shimura.kernel g) (wOf s₀)) := by
    unfold rhsD; rw [_root_.RHTower.zetaResidueFactor_of_ne h1]; ring
  rw [hR] at hid
  constructor
  · intro hp
    have hl : (16 * ρ 1 * (s₀ - 1) ^ 2 * s₀ * (2 * s₀ - 1) * shC (wOf s₀) *
        Shimura.melC (CuspL.nu lam) (s₀ / 2)) * pairing s₀ g g ≠ 0 := mul_ne_zero hA hp
    rw [hid] at hl
    exact mul_ne_zero_iff.1 (right_ne_zero_of_mul hl)
  · rintro ⟨hz, hf⟩ hp
    rw [hp, mul_zero] at hid
    exact mul_ne_zero hB (mul_ne_zero hz hf) hid.symm

end Obstruction

/-- The coefficient form of the mirror. -/
theorem whittaker_comp_mirror {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) {ρ : ℤ → ℂ}
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam)) :
    ∀ n : ℤ, ∀ y, 0 < y → HeckeCusp.fourierCoeff (g ∘ OddCusp.mirror) n y = ρ (-n) * (Real.sqrt y : ℂ) *
      HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (CuspL.nu lam) := fun n y hy => by
  rw [HeckeCusp.fourierCoeff_comp_mirror hg n hy, hρ (-n) y hy]
  simp

theorem fourierCoeff_zero (n : ℤ) (y : ℝ) : HeckeCusp.fourierCoeff (0 : ℍ → ℂ) n y = 0 := by
  simp [HeckeCusp.fourierCoeff, GaloisForLFunctions.RHTower.SelbergMaassFourier.coefficient,
    _root_.RHTower.deningerFourierCoeff]

/-- **The halving obstruction**: at every zero `s₀` of `ζ` with `0 < Re s₀ < 1`, `s₀ ≠ ½`, every Hecke form has
vanishing diagonal entry `∫_𝒟 |u|² E*(s₀ − ½) = 0`. -/
theorem pairing_self_eq_zero_of_zeta {lam : ℝ} {g : ℍ → ℂ} (hg : g ∈ HeckeCusp.cuspSpace lam) {c : ℕ → ℂ}
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) {s₀ : ℂ} (hs : 0 < s₀.re) (h12 : s₀ ≠ 1 / 2)
    (h1 : s₀ ≠ 1) (hz : riemannZeta s₀ = 0) : pairing s₀ g g = 0 := by
  by_cases hg0 : g = 0
  · subst hg0; exact pairing_zero_left _ _
  obtain ⟨ρ, hρ0, hρ⟩ := CuspL.exists_whittaker hg
  by_cases hρ1 : ρ 1 = 0
  · have hρm1 : ρ (-1) ≠ 0 := by
      intro hm
      apply hg0
      refine HeckeCusp.eq_of_heckeData hg (Submodule.zero_mem _) c hc (fun p _ => ?_) (fun y hy => ?_)
        (fun y hy => ?_)
      · rw [smul_zero]; funext z; simp [heckeH]
      · rw [hρ 1 y hy, hρ1, fourierCoeff_zero]; ring
      · rw [hρ (-1) y hy, hm, fourierCoeff_zero]; ring
    have hg' := HeckeCusp.comp_mirror_mem_cuspSpace hg
    have hc' : ∀ (p : ℕ) [Fact p.Prime], heckeH p (g ∘ OddCusp.mirror) = c p • (g ∘ OddCusp.mirror) :=
      fun p _ => by rw [HeckeCusp.heckeH_comp_mirror p hg, hc p]; rfl
    have hg'0 : g ∘ OddCusp.mirror ≠ 0 := fun h => hg0 (by
      funext z
      have := congrFun h (OddCusp.mirror z)
      simpa [OddSector.mirror_mirror] using this)
    rw [← pairing_comp_mirror]
    exact pairing_self_eq_zero_of_rho hg' hc' (ρ := fun n => ρ (-n)) (by simpa using hρ0)
      (whittaker_comp_mirror hg hρ) hg'0 (by simpa using hρm1) hs h12 h1 hz
  · exact pairing_self_eq_zero_of_rho hg hc hρ0 hρ hg0 hρ1 hs h12 h1 hz

/-- The eigenvalues of a Hecke form as a function on `ℕ`. -/
def eigenvalues {lam : ℝ} {u : ℍ → ℂ} (hu : IsHeckeForm lam u) (p : ℕ) : ℂ :=
  if h : p.Prime then (haveI := Fact.mk h; Classical.choose (hu.2 p)) else 0

theorem eigenvalues_spec {lam : ℝ} {u : ℍ → ℂ} (hu : IsHeckeForm lam u) (p : ℕ) [hp : Fact p.Prime] :
    heckeH p u = eigenvalues hu p • u := by
  rw [eigenvalues, dif_pos hp.out]
  exact Classical.choose_spec (hu.2 p)

/-- **One Hecke eigenform is blind to halving pairs**: if `ρ` and `ρ/2` are both zeros of `ζ` (`Re ρ > 0`), no Hecke
form sees the resonance `ρ/2` in its energy. -/
theorem pairing_half_eq_zero {lam : ℝ} {u : ℍ → ℂ} (hu : IsHeckeForm lam u) {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (hpos : 0 < ρ.re) (hhalf : riemannZeta (ρ / 2) = 0) : pairing (ρ / 2) u u = 0 := by
  have hlt : ρ.re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ
  have hlt2 : (ρ / 2).re < 1 := lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hhalf
  refine pairing_self_eq_zero_of_zeta hu.1 (eigenvalues_spec hu) (by simp; linarith) (fun h => ?_)
    (fun h => by rw [h] at hlt2; simp at hlt2) hhalf
  have : ρ = 1 := by linear_combination 2 * h
  rw [this] at hlt; simp at hlt

/-- **B109 for one Hecke eigenform excludes halving pairs**: if a single Hecke form sees every right resonance in
its energy, then `ζ(ρ/2) ≠ 0` at every zero `ρ` with `Re ρ > ½`. -/
theorem zeta_half_ne_zero_of_hecke_seeing {lam : ℝ} {u : ℍ → ℂ} (hu : IsHeckeForm lam u)
    (hsee : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → pairing (ρ / 2) u u ≠ 0) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → riemannZeta (ρ / 2) ≠ 0 :=
  fun ρ hζ hρ hhalf => hsee ρ hζ hρ (pairing_half_eq_zero hu hζ (by linarith) hhalf)

end GaloisForLFunctions.ArithmeticHolographyOfTheModularHorizon.HalvingPairs
