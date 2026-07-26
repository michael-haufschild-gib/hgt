/-
# The gamma-widened functional-equation cell and its convolution mobility

Widening the integral-multiplicative functional-equation carrier to carry a completion factor turns
a rigid single class into a *cell closed under Dirichlet convolution by the degree-zero member*
`dzo`.  A carrier `f` lies in `GammaFECell` when it is the Dirichlet series of an integer-valued
multiplicative arithmetic function `a` (convergent on `Re s > 1`) and there is a factor `γ`,
nonvanishing on the open critical strip, with the self-dual relation `γ(1−s)·f(1−s) = γ(s)·f(s)`.
Because `γ` never vanishes on the strip, multiplying by it does not move the strip divisor: the zeros
of `γ·f` inside `0 < Re s < 1` are exactly the zeros of `f`.

Two seed members bracket the cell.  The completed Riemann zeta identity
`Gammaℝ(s)·ζ(s) = completedRiemannZeta(s)` together with `completedRiemannZeta(1−s) =
completedRiemannZeta(s)` puts `riemannZeta` in the cell with `γ = Gammaℝ` (nonvanishing for
`Re s > 0`).  The finite degree-zero polynomial `dzo` is in the cell with the analytic factor
`γ(s) = 8^{s − 1/2}`: its exact equation `dzo(s) = 8^{1−2s}·dzo(1−s)` rearranges to
`dzo(1−s) = 8^{2s−1}·dzo(s)`, whence `8^{(1−s)−1/2}·dzo(1−s) = 8^{s−1/2}·dzo(s)`.

The cell is stable under `· ⋆ dzoCoeff`: Dirichlet convolution preserves multiplicativity
(`IsMultiplicative.mul`), integrality (the integer casts form a subring closed under the antidiagonal
sum), and, on `Re s > 1`, `L(a ⋆ dzoCoeff) = L(a)·L(dzo)`; the completion factor of the product is
`γ_f · 8^{s−1/2}`, and its functional equation is the termwise product of the two.  Applying this to
`ζ` yields the concrete member `zetaDzo = ζ · dzo`, which carries a simple zero at `ρ = 1/3` inside
the strip and off the line, yet is nonzero at `s = 2` — a hypertranscendental fiber whose off-line
divisor the widened conjunction cannot see.

Read through the deck-charge trichotomy: `dzo ∈ GammaFECell` has a simple (odd) off-line zero, so the
cell carries off-line charge; by `forcesRHParity_iff_categorical` it cannot force RH-grade parity.
-/
import GaloisForLFunctions.RHTower.DegreeZeroOffline
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The gamma-widened functional-equation cell -/

/-- The **gamma-widened functional-equation cell**: a Dirichlet series with integral multiplicative
coefficients admitting a gamma-completed self-dual functional equation on the open critical strip.
The completion factor `γ` is required nonvanishing on the strip, so the divisor of `γ·f` on the strip
equals that of `f`. -/
def GammaFECell (f : ℂ → ℂ) : Prop :=
  ∃ a : ArithmeticFunction ℂ, a.IsMultiplicative ∧ (∀ n, ∃ k : ℤ, a n = (k : ℂ)) ∧
    (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => a n) s) ∧
    (∀ s : ℂ, 1 < s.re → f s = LSeries (fun n => a n) s) ∧
    (∃ γ : ℂ → ℂ, (∀ s : ℂ, 0 < s.re → s.re < 1 → γ s ≠ 0) ∧
      (∀ s : ℂ, 0 < s.re → s.re < 1 → γ (1 - s) * f (1 - s) = γ s * f s))

/-! ### §2 The degree-zero member `dzo` -/

/-- The analytic completion equation for `dzo` with factor `8^{s − 1/2}`.  Solving the exact equation
`dzo(s) = 8^{1−2s}·dzo(1−s)` for `dzo(1−s) = 8^{2s−1}·dzo(s)` and folding the exponents
`((1−s)−1/2) + (2s−1) = s − 1/2` gives `8^{(1−s)−1/2}·dzo(1−s) = 8^{s−1/2}·dzo(s)`. -/
private theorem dzo_gamma_fe (s : ℂ) :
    (8 : ℂ) ^ ((1 - s) - 1 / 2) * dzo (1 - s) = (8 : ℂ) ^ (s - 1 / 2) * dzo s := by
  have h8 : (8 : ℂ) ≠ 0 := by norm_num
  have hrefl : dzo (1 - s) = (8 : ℂ) ^ (2 * s - 1) * dzo s := by
    rw [dzo_fe s, ← mul_assoc, ← Complex.cpow_add _ _ h8,
      show (2 * s - 1) + (1 - 2 * s) = (0 : ℂ) by ring, Complex.cpow_zero, one_mul]
  rw [hrefl, ← mul_assoc, ← Complex.cpow_add _ _ h8,
    show ((1 - s) - 1 / 2) + (2 * s - 1) = s - 1 / 2 by ring]

/-- The Dirichlet series of `dzoCoeff` converges at every `s`: its support `{1, 8, 64}` is finite, so
the term function vanishes off a finite set. -/
private theorem dzoCoeff_summable (s : ℂ) : LSeriesSummable (fun n => dzoCoeff n) s := by
  apply summable_of_ne_finset_zero (s := ({1, 8, 64} : Finset ℕ))
  intro n hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hpos.ne' _ s]
    have h1 : n ≠ 1 := by rintro rfl; exact hn (by decide)
    have h8 : n ≠ 8 := by rintro rfl; exact hn (by decide)
    have h64 : n ≠ 64 := by rintro rfl; exact hn (by decide)
    have hz : dzoCoeff n = 0 := by
      show (if n = 1 then (1 : ℂ) else if n = 8 then -6 else if n = 64 then 8 else 0) = 0
      rw [if_neg h1, if_neg h8, if_neg h64]
    rw [hz]; simp

/-- **`dzo` lies in the gamma cell.**  Coefficients `dzoCoeff` (finite support, hence summable at
every `s`); completion factor `γ(s) = 8^{s − 1/2}`, nonvanishing as a `cpow` of the nonzero base `8`;
the functional-equation clause is `dzo_gamma_fe`. -/
theorem dzo_mem_gammaFECell : GammaFECell dzo :=
  ⟨dzoCoeff, dzoCoeff_multiplicative, dzoCoeff_integral,
    fun s _ => dzoCoeff_summable s, fun s _ => (LSeries_dzoCoeff s).symm,
    fun s => (8 : ℂ) ^ (s - 1 / 2),
    fun _ _ _ => Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)),
    fun s _ _ => dzo_gamma_fe s⟩

/-! ### §3 The Riemann zeta member -/

/-- The integer-valued arithmetic function that is `1` at every positive integer.  Its Dirichlet
series is `riemannZeta` on `Re s > 1`. -/
def zetaCoeff : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else 1, by simp⟩

private theorem zetaCoeff_apply (n : ℕ) : zetaCoeff n = if n = 0 then 0 else 1 := rfl

/-- **`zetaCoeff` is multiplicative.**  Its value is `1` off `0`, so both sides of a coprime product
are `1` unless one factor is `0`, where both sides vanish. -/
theorem zetaCoeff_multiplicative : zetaCoeff.IsMultiplicative := by
  constructor
  · simp [zetaCoeff_apply]
  · intro m n _
    simp only [zetaCoeff_apply]
    rcases eq_or_ne m 0 with hm | hm
    · subst hm; simp
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp
    · rw [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)]; ring

/-- **`zetaCoeff` is integer-valued.**  Every value is `0` or `1`. -/
theorem zetaCoeff_integral (n : ℕ) : ∃ k : ℤ, zetaCoeff n = (k : ℂ) := by
  rw [zetaCoeff_apply]
  by_cases h : n = 0
  · exact ⟨0, by rw [if_pos h]; norm_num⟩
  · exact ⟨1, by rw [if_neg h]; norm_num⟩

/-- The Dirichlet series of `zetaCoeff` converges on `Re s > 1`: off `0` it agrees with the constant
sequence `1`, whose series converges there. -/
private theorem zetaCoeff_summable (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => zetaCoeff n) s := by
  have h : ∀ {n : ℕ}, n ≠ 0 → (fun n => zetaCoeff n) n = (1 : ℕ → ℂ) n := by
    intro n hn; simp [zetaCoeff_apply, hn]
  exact (LSeriesSummable_congr s h).mpr (LSeriesSummable_one_iff.mpr hs)

/-- On `Re s > 1` the Dirichlet series of `zetaCoeff` equals `riemannZeta`: off `0` it agrees with the
constant sequence `1`, whose series is `riemannZeta` there. -/
private theorem zetaCoeff_lseries (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = LSeries (fun n => zetaCoeff n) s := by
  have h : ∀ {n : ℕ}, n ≠ 0 → (fun n => zetaCoeff n) n = (1 : ℕ → ℂ) n := by
    intro n hn; simp [zetaCoeff_apply, hn]
  rw [LSeries_congr h s, LSeries_one_eq_riemannZeta hs]

/-- The gamma-completed functional equation for `riemannZeta` with factor `Gammaℝ`, on the open
critical strip.  For `z ≠ 0` with `Gammaℝ(z) ≠ 0` one has `Gammaℝ(z)·ζ(z) = completedRiemannZeta(z)`;
applying this at `z = s` and `z = 1−s` (both have positive real part on the strip) and using
`completedRiemannZeta(1−s) = completedRiemannZeta(s)` gives the equation. -/
private theorem zeta_gamma_fe (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) = Complex.Gammaℝ s * riemannZeta s := by
  have hspos : (0 : ℝ) < s.re := hs0
  have hsne : s ≠ 0 := by intro h; rw [h] at hspos; simp at hspos
  have h1re : 0 < (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have h1ne : (1 - s) ≠ 0 := by intro h; rw [h] at h1re; simp at h1re
  have hΓs : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have hΓ1 : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h1re
  have key : ∀ z : ℂ, z ≠ 0 → Complex.Gammaℝ z ≠ 0 →
      Complex.Gammaℝ z * riemannZeta z = completedRiemannZeta z := by
    intro z hz hΓz
    rw [riemannZeta_def_of_ne_zero hz]; field_simp
  rw [key (1 - s) h1ne hΓ1, key s hsne hΓs, completedRiemannZeta_one_sub]

/-- **`riemannZeta` lies in the gamma cell.**  Coefficients `zetaCoeff`; completion factor
`γ = Gammaℝ`, nonvanishing for `Re s > 0` (`Gammaℝ_ne_zero_of_re_pos`); the functional-equation clause
is `zeta_gamma_fe`. -/
theorem zeta_mem_gammaFECell : GammaFECell riemannZeta :=
  ⟨zetaCoeff, zetaCoeff_multiplicative, zetaCoeff_integral,
    fun s hs => zetaCoeff_summable s hs, fun s hs => zetaCoeff_lseries s hs,
    Complex.Gammaℝ, fun _ hs _ => Complex.Gammaℝ_ne_zero_of_re_pos hs,
    fun s hs hs1 => zeta_gamma_fe s hs hs1⟩

/-! ### §4 Convolution mobility -/

/-- **Convolution mobility.**  The gamma cell is closed under Dirichlet convolution by `dzo`: from a
member `f` with coefficients `a` and factor `γ_f`, the product `f·dzo` is a member with coefficients
`a ⋆ dzoCoeff` and factor `γ_f · 8^{s−1/2}`.  Multiplicativity is `IsMultiplicative.mul`, integrality
is `RHTower.intCast_conv_integral`, `L(a ⋆ dzoCoeff) = L(a)·L(dzo)` on `Re s > 1`, nonvanishing is the product
of nonvanishing factors, and the functional equation is the termwise product of the two. -/
theorem gammaFECell_mul_dzo {f : ℂ → ℂ} (hf : GammaFECell f) :
    GammaFECell (fun s => f s * dzo s) := by
  obtain ⟨a, ha_mul, ha_int, ha_summ, ha_ls, γf, hγf_ne, hγf_fe⟩ := hf
  refine ⟨a * dzoCoeff, ha_mul.mul dzoCoeff_multiplicative,
    RHTower.intCast_conv_integral a dzoCoeff ha_int dzoCoeff_integral, ?_, ?_,
    fun s => γf s * (8 : ℂ) ^ (s - 1 / 2), ?_, ?_⟩
  · intro s hs
    exact ArithmeticFunction.LSeriesSummable_mul (ha_summ s hs) (dzoCoeff_summable s)
  · intro s hs
    show f s * dzo s = LSeries (fun n => (a * dzoCoeff) n) s
    rw [ArithmeticFunction.LSeries_mul' (ha_summ s hs) (dzoCoeff_summable s), ← ha_ls s hs,
      LSeries_dzoCoeff s]
  · intro s hs hs1
    exact mul_ne_zero (hγf_ne s hs hs1) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  · intro s hs hs1
    show (γf (1 - s) * (8 : ℂ) ^ ((1 - s) - 1 / 2)) * (f (1 - s) * dzo (1 - s)) =
      (γf s * (8 : ℂ) ^ (s - 1 / 2)) * (f s * dzo s)
    calc (γf (1 - s) * (8 : ℂ) ^ ((1 - s) - 1 / 2)) * (f (1 - s) * dzo (1 - s))
        = (γf (1 - s) * f (1 - s)) * ((8 : ℂ) ^ ((1 - s) - 1 / 2) * dzo (1 - s)) := by ring
      _ = (γf s * f s) * ((8 : ℂ) ^ (s - 1 / 2) * dzo s) := by rw [hγf_fe s hs hs1, dzo_gamma_fe s]
      _ = (γf s * (8 : ℂ) ^ (s - 1 / 2)) * (f s * dzo s) := by ring

/-! ### §5 The concrete hypertranscendental fiber `ζ · dzo` -/

/-- The witness member `zetaDzo = ζ · dzo`. -/
def zetaDzo : ℂ → ℂ := fun s => riemannZeta s * dzo s

/-- **`zetaDzo` lies in the gamma cell**, as the convolution of the two seed members. -/
theorem zetaDzo_mem_gammaFECell : GammaFECell zetaDzo :=
  gammaFECell_mul_dzo zeta_mem_gammaFECell

/-- **`zetaDzo` has a strip zero off the critical line.**  The factor `dzo` vanishes at `ρdzo = 1/3`,
which lies strictly inside the open critical strip and off `Re s = 1/2`. -/
theorem zetaDzo_offline_strip_zero :
    zetaDzo ρdzo = 0 ∧ 0 < ρdzo.re ∧ ρdzo.re < 1 ∧ ρdzo.re ≠ 1 / 2 := by
  refine ⟨?_, ρdzo_re_pos, ρdzo_re_lt_one, ρdzo_re_ne_half⟩
  show riemannZeta ρdzo * dzo ρdzo = 0
  rw [dzo_ρdzo_eq_zero, mul_zero]

/-- **`zetaDzo` is nonzero at `s = 2`.**  `ζ(2) = π²/6 ≠ 0`, and
`dzo(2) = (1 − 2·8^{−2})(1 − 4·8^{−2}) = (31/32)(15/16) ≠ 0`. -/
theorem zetaDzo_ne_zero_at_two : zetaDzo 2 ≠ 0 := by
  show riemannZeta 2 * dzo 2 ≠ 0
  refine mul_ne_zero ?_ ?_
  · rw [riemannZeta_two]
    exact div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)
  · have h64 : (8 : ℂ) ^ (-(2 : ℂ)) = 1 / 64 := by
      rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      norm_num
    show (1 - 2 * (8 : ℂ) ^ (-(2 : ℂ))) * (1 - 4 * (8 : ℂ) ^ (-(2 : ℂ))) ≠ 0
    rw [h64]; norm_num

/-! ### §6 The cell carries off-line charge, hence no RH-grade parity -/

/-- The gamma cell carries nontrivial charge at `ρdzo`: the member `dzo` has a simple (odd) zero
there, so its base-level deck charge is `(−1)¹ = −1 ≠ 1`. -/
private theorem carriesChargeAt_dzo_gamma : CarriesChargeAt GammaFECell ρdzo := by
  refine ⟨dzo, dzo_mem_gammaFECell, ?_⟩
  rw [carrierCharge_one_eq_neg_one_pow, dzo_order_one, ENat.toNat_one]; norm_num

/-- **The gamma cell carries off-line charge.**  The witness `ρdzo` has `Re ρdzo = 1/3 ≠ 1/2`, strictly
inside the open critical strip. -/
theorem gammaFECell_carriesOffLineCharge : CarriesOffLineCharge GammaFECell :=
  ⟨ρdzo, ρdzo_re_ne_half, carriesChargeAt_dzo_gamma⟩

/-- **The gamma-widened cell cannot force RH-grade parity.**  Parity-forcing by charge is exactly the
charge-free (categorical) cell (`forcesRHParity_iff_categorical`); this cell carries off-line charge,
so it is not categorical.  Widening the integral multiplicative functional-equation carrier by a
strip-nonvanishing completion factor, and closing under convolution by `dzo`, stays blind to the
off-line divisor of `dzo`. -/
theorem gammaFECell_not_forcesRHParity : ¬ ForcesRHParity GammaFECell := by
  rw [forcesRHParity_iff_categorical]
  exact fun hcat => hcat gammaFECell_carriesOffLineCharge

end RHTower
