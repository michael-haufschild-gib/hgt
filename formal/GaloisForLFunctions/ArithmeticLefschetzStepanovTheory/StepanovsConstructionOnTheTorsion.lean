import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheFrobeniusOfTheTorsionIsGalois
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Stepanov's construction on the torsion

Stepanov's auxiliary over `𝔽_q` is `h = Σ_i f_i · (g_i ∘ F)`: on the rational points `g_i ∘ F = g_i`,
so `h = Σ f_i g_i` there, and one polynomial identity `Σ f_i g_i = 0` makes `h` vanish at every point;
inseparability gives the higher orders. Over `ℤ` the construction runs verbatim on the torsion of
the prime torus with `F = ψ_q` the Adams operation.

* **(S1) Cheap exact vanishing** (`aeval_stepanov_eq_zero`). If `Σ f_i g_i = 0` then
  `h = Σ f_i ψ_q(g_i)` vanishes at every torsion point of order dividing `q − 1`: one polynomial
  identity kills all `(q−1)^{|σ|}` points.
* **(S2) Inseparability lives at `ℓ`** (`map_adams_eq_pow`, `map_pderiv_adams_eq_zero`). For a prime
  `ℓ`, `ψ_ℓ(g) ≡ g^ℓ (mod ℓ)` and every partial derivative of `ψ_ℓ(g)` is divisible by `ℓ`
  (`exists_pderiv_adams_eq`). Over `ℂ` it is not: `∂(g(u^ℓ)) = ℓ u^{ℓ−1} (∂g)(u^ℓ)`.
* **(S1)+(S2)+(S3): the `ℓ`-adic Stepanov amplifier** (`pderiv_stepanov_eq_zero_of_lt`). If moreover
  `Σ_i (∂_j f_i) g_i = 0`, then at an `(ℓ−1)`-torsion point `∂_j h = ℓ R` for an integer polynomial
  `R` (`aeval_pderiv_stepanov_eq`), and the norm amplifier works with threshold `ℓ^{φ(m)}` instead of
  `1`: if `Π_{μ prim} |∂_j h(μ^b)| < ℓ^{φ(m)}`, then `∂_j h` vanishes on the whole closed point.

The archimedean place enters only through that threshold: the derivative values must be below `ℓ`
in geometric mean over the closed point. Over `𝔽_ℓ` there is no archimedean place and the
condition is void; over `ℤ` the values of `∂_j h`, a polynomial of degree about `ℓ deg g`, are not
small, and the order gained `ℓ`-adically is not an order of vanishing on the prime orbit.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ : Type*}

/-- The Stepanov auxiliary `h = Σ_i f_i ψ_q(g_i)`. -/
def stepanovAux (q : ℕ) {r : ℕ} (f g : Fin r → MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∑ i, f i * adams q (g i)

/-- **(S1) Cheap exact vanishing on the torsion.** One identity `Σ f_i g_i = 0` kills `h` at every
torsion point of order dividing `q − 1`. -/
theorem aeval_stepanov_eq_zero (q : ℕ) {r : ℕ} (f g : Fin r → MvPolynomial σ ℤ)
    (hfg : ∑ i, f i * g i = 0) {μ : ℂ} (hμ : μ ^ q = μ) (b : σ → ℕ) :
    MvPolynomial.aeval (torsionPoint μ b) (stepanovAux q f g) = 0 := by
  have h := congrArg (MvPolynomial.aeval (torsionPoint μ b)) hfg
  rw [map_zero, map_sum] at h
  rw [stepanovAux, map_sum, ← h]
  refine sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, aeval_torsionPoint_adams_of_pow_eq hμ]

theorem adams_eq_expand (a : ℕ) (g : MvPolynomial σ ℤ) : adams a g = MvPolynomial.expand a g := by
  rw [adams, MvPolynomial.aeval_eq_bind₁]
  rfl

/-- **The Frobenius congruence.** `ψ_ℓ(g) ≡ g^ℓ (mod ℓ)`. -/
theorem map_adams_eq_pow (ℓ : ℕ) [Fact ℓ.Prime] (g : MvPolynomial σ ℤ) :
    MvPolynomial.map (Int.castRingHom (ZMod ℓ)) (adams ℓ g) =
      MvPolynomial.map (Int.castRingHom (ZMod ℓ)) g ^ ℓ := by
  rw [adams_eq_expand, MvPolynomial.map_expand, ← MvPolynomial.frobenius_zmod, frobenius_def]

/-- **Inseparability at `ℓ`.** Every partial derivative of `ψ_ℓ(g)` vanishes modulo `ℓ`. -/
theorem map_pderiv_adams_eq_zero (ℓ : ℕ) [Fact ℓ.Prime] (g : MvPolynomial σ ℤ) (j : σ) :
    MvPolynomial.map (Int.castRingHom (ZMod ℓ)) (MvPolynomial.pderiv j (adams ℓ g)) = 0 := by
  rw [← MvPolynomial.pderiv_map, map_adams_eq_pow, Derivation.leibniz_pow]
  have : (ℓ : MvPolynomial σ (ZMod ℓ)) = 0 := by
    rw [← map_natCast (MvPolynomial.C : ZMod ℓ →+* MvPolynomial σ (ZMod ℓ)), ZMod.natCast_self,
      map_zero]
  rw [nsmul_eq_mul, this, zero_mul]

/-- An integer polynomial vanishing modulo `ℓ` is `ℓ` times an integer polynomial. -/
theorem exists_eq_C_mul_of_map_eq_zero (ℓ : ℕ) {G : MvPolynomial σ ℤ}
    (h : MvPolynomial.map (Int.castRingHom (ZMod ℓ)) G = 0) :
    ∃ R : MvPolynomial σ ℤ, G = MvPolynomial.C (ℓ : ℤ) * R := by
  classical
  have hdvd : ∀ s, (ℓ : ℤ) ∣ G.coeff s := by
    intro s
    have := congrArg (MvPolynomial.coeff s) h
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, eq_intCast] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  refine ⟨∑ s ∈ G.support, MvPolynomial.monomial s (G.coeff s / ℓ), ?_⟩
  conv_lhs => rw [MvPolynomial.as_sum G]
  rw [mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.C_mul_monomial, Int.mul_ediv_cancel' (hdvd s)]

/-- Every partial derivative of `ψ_ℓ(g)` is `ℓ` times an integer polynomial. -/
theorem exists_pderiv_adams_eq (ℓ : ℕ) [Fact ℓ.Prime] (g : MvPolynomial σ ℤ) (j : σ) :
    ∃ R : MvPolynomial σ ℤ, MvPolynomial.pderiv j (adams ℓ g) = MvPolynomial.C (ℓ : ℤ) * R :=
  exists_eq_C_mul_of_map_eq_zero ℓ (map_pderiv_adams_eq_zero ℓ g j)

/-- At an `(ℓ−1)`-torsion point, if `Σ_i (∂_j f_i) g_i = 0`, then `∂_j h = ℓ R` for an integer
polynomial `R`. -/
theorem aeval_pderiv_stepanov_eq (ℓ : ℕ) [Fact ℓ.Prime] {r : ℕ} (f g : Fin r → MvPolynomial σ ℤ)
    (j : σ) (hdf : ∑ i, MvPolynomial.pderiv j (f i) * g i = 0) :
    ∃ R : MvPolynomial σ ℤ, ∀ (μ : ℂ), μ ^ ℓ = μ → ∀ b : σ → ℕ,
      MvPolynomial.aeval (torsionPoint μ b) (MvPolynomial.pderiv j (stepanovAux ℓ f g)) =
        ℓ * MvPolynomial.aeval (torsionPoint μ b) R := by
  choose R hR using fun i => exists_pderiv_adams_eq ℓ (g i) j
  refine ⟨∑ i, f i * R i, fun μ hμ b => ?_⟩
  have hd := congrArg (MvPolynomial.aeval (torsionPoint μ b)) hdf
  rw [map_zero, map_sum] at hd
  have hexp : MvPolynomial.pderiv j (stepanovAux ℓ f g) =
      ∑ i, MvPolynomial.pderiv j (f i) * adams ℓ (g i) +
        MvPolynomial.C (ℓ : ℤ) * ∑ i, f i * R i := by
    rw [stepanovAux, map_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, hR i, smul_eq_mul, smul_eq_mul]
    ring
  rw [hexp, map_add, map_sum, map_mul, MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast,
    Int.cast_natCast]
  have hzero : ∑ i, MvPolynomial.aeval (torsionPoint μ b) (MvPolynomial.pderiv j (f i) *
      adams ℓ (g i)) = 0 := by
    rw [← hd]
    refine sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, aeval_torsionPoint_adams_of_pow_eq hμ]
  rw [hzero, zero_add]

/-- **The `ℓ`-adic Stepanov amplifier.** Under `Σ f_i g_i = 0` and `Σ (∂_j f_i) g_i = 0`, on a closed
point of order `m ∣ ℓ − 1`: if `Π_{μ prim} |∂_j h(μ^b)| < ℓ^{φ(m)}`, then `∂_j h` vanishes on the
whole closed point (and `h` itself vanishes there by `aeval_stepanov_eq_zero`). -/
theorem pderiv_stepanov_eq_zero_of_lt (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {r : ℕ}
    (f g : Fin r → MvPolynomial σ ℤ) (j : σ) (hdf : ∑ i, MvPolynomial.pderiv j (f i) * g i = 0)
    {m : ℕ} (hm : 0 < m) (hmℓ : m ∣ ℓ - 1) (b : σ → ℕ)
    (hsmall : ∏ μ ∈ primitiveRoots m ℂ,
      ‖MvPolynomial.aeval (torsionPoint μ b) (MvPolynomial.pderiv j (stepanovAux ℓ f g))‖ <
        (ℓ : ℝ) ^ m.totient) :
    ∀ μ ∈ primitiveRoots m ℂ,
      MvPolynomial.aeval (torsionPoint μ b) (MvPolynomial.pderiv j (stepanovAux ℓ f g)) = 0 := by
  obtain ⟨R, hR⟩ := aeval_pderiv_stepanov_eq ℓ f g j hdf
  have hfix : ∀ μ ∈ primitiveRoots m ℂ, μ ^ ℓ = μ := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots hm).mp hμ
    obtain ⟨k, hk⟩ := hmℓ
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel hℓ.out.one_lt.le).symm
    rw [hℓ1, pow_succ, hk, pow_mul, hμ'.pow_eq_one, one_pow, one_mul]
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
  have hcard : (primitiveRoots m ℂ).card = m.totient :=
    (Complex.isPrimitiveRoot_exp m hm.ne').card_primitiveRoots
  have hR1 : ∏ μ ∈ primitiveRoots m ℂ, ‖MvPolynomial.aeval (torsionPoint μ b) R‖ < 1 := by
    have heq : ∏ μ ∈ primitiveRoots m ℂ,
        ‖MvPolynomial.aeval (torsionPoint μ b) (MvPolynomial.pderiv j (stepanovAux ℓ f g))‖ =
        (ℓ : ℝ) ^ m.totient * ∏ μ ∈ primitiveRoots m ℂ, ‖MvPolynomial.aeval (torsionPoint μ b) R‖ := by
      rw [← hcard, ← prod_const, ← prod_mul_distrib]
      refine prod_congr rfl fun μ hμ => ?_
      rw [hR μ (hfix μ hμ) b, norm_mul, Complex.norm_natCast]
    rw [heq] at hsmall
    have hpow : (0 : ℝ) < (ℓ : ℝ) ^ m.totient := pow_pos hℓpos _
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_left hge hpow.le
    linarith
  intro μ hμ
  rw [hR μ (hfix μ hμ) b, torus_norm_amplifier hm R b hR1 μ hμ, mul_zero]

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
